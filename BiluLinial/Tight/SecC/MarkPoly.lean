/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.Compare.Partial

/-!
# Coefficient majorants and line derivatives (helpers for T.MARK)

Generic tools for `SecC/Mark.lean` (node T.MARK of `docs/tight/BP_SECC.md`, AUDIT-C §3 and §9):

* `IsMaj rel`: a relation "`|P| ≪ Q`" closed under `0, 1, -, +, *`; `IsMaj.poly` lifts it
  coefficientwise to `R[X]`. The base case is `absRel` (`|a| ≤ b` on `ℝ`), giving one-variable
  majorants `Maj1` on `ℝ[X]` and two-variable majorants `Maj2` on `ℝ[X][X]`.
* `coeff_C_add_C_mul_X_pow`: `[Xⁿ](u + bX)^M = binom(M, n) u^{M-n} bⁿ` over any commutative ring.
* `iteratedDeriv_eval_zero`: `(d/dt)ⁿ P(t)|_{t=0} = n! [tⁿ] P`.
* `iteratedDeriv_line`: for `g ∈ C^n`, `(d/dt)ⁿ g(x + t e_i) = ∂_iⁿ g(x + t e_i)`.
* `pderiv_iterate_congr_nhds`: iterated partial derivatives at `x` only depend on the germ at `x`.
* Two-variable bookkeeping on `ℝ[X][X]` (inner variable `t = C X`, outer variable `s = X`):
  `mono2 κ m n = κ t^m s^n`, `coeff2 P m n = [t^m s^n] P`, the evaluation `ev2 t s`.
-/

@[expose] public section

namespace BiluLinial.Tight

namespace SecC

open Polynomial Filter Topology
open scoped Nat

section Maj

variable {R : Type*} [CommRing R]

/-- A coefficientwise majorant relation ("`|a| ≪ b`") closed under the ring operations. -/
structure IsMaj (rel : R → R → Prop) : Prop where
  zero : rel 0 0
  one : rel 1 1
  neg : ∀ {a b : R}, rel a b → rel (-a) b
  add : ∀ {a b c d : R}, rel a b → rel c d → rel (a + c) (b + d)
  mul : ∀ {a b c d : R}, rel a b → rel c d → rel (a * c) (b * d)

variable {rel : R → R → Prop}

theorem IsMaj.sub (h : IsMaj rel) {a b c d : R} (h1 : rel a b) (h2 : rel c d) :
    rel (a - c) (b + d) := by
  rw [sub_eq_add_neg]
  exact h.add h1 (h.neg h2)

theorem IsMaj.pow (h : IsMaj rel) {a b : R} (h1 : rel a b) : ∀ n : ℕ, rel (a ^ n) (b ^ n)
  | 0 => by simpa using h.one
  | n + 1 => by
    rw [pow_succ, pow_succ]
    exact h.mul (h.pow h1 n) h1

theorem IsMaj.sum (h : IsMaj rel) {α : Type*} (s : Finset α) {f g : α → R}
    (hfg : ∀ x ∈ s, rel (f x) (g x)) : rel (∑ x ∈ s, f x) (∑ x ∈ s, g x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h.zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact h.add (hfg a (Finset.mem_insert_self a s))
      (ih fun x hx => hfg x (Finset.mem_insert_of_mem hx))

/-- The coefficientwise lift of `rel` to `R[X]`. -/
def polyRel (rel : R → R → Prop) (P Q : R[X]) : Prop :=
  ∀ n, rel (P.coeff n) (Q.coeff n)

theorem IsMaj.poly (h : IsMaj rel) : IsMaj (polyRel rel) where
  zero n := by simpa using h.zero
  one n := by
    rw [coeff_one]
    split_ifs
    · exact h.one
    · exact h.zero
  neg h1 n := by
    rw [coeff_neg]
    exact h.neg (h1 n)
  add h1 h2 n := by
    rw [coeff_add, coeff_add]
    exact h.add (h1 n) (h2 n)
  mul h1 h2 n := by
    rw [coeff_mul, coeff_mul]
    exact h.sum _ fun x _ => h.mul (h1 x.1) (h2 x.2)

theorem IsMaj.polyC (h : IsMaj rel) {a b : R} (h1 : rel a b) : polyRel rel (C a) (C b) :=
  fun n => by
    rw [coeff_C, coeff_C]
    split_ifs
    · exact h1
    · exact h.zero

theorem IsMaj.polyX (h : IsMaj rel) : polyRel rel (X : R[X]) X := fun n => by
  rw [coeff_X]
  split_ifs
  · exact h.one
  · exact h.zero

end Maj

/-- The base majorant relation `|a| ≤ b` on `ℝ`. -/
def absRel (a b : ℝ) : Prop := |a| ≤ b

theorem isMaj_absRel : IsMaj absRel where
  zero := by simp [absRel]
  one := by simp [absRel]
  neg h := by simpa [absRel] using h
  add h1 h2 := (abs_add_le _ _).trans (add_le_add h1 h2)
  mul h1 h2 := by
    unfold absRel at *
    rw [abs_mul]
    exact mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1)

/-- One-variable coefficient majorants: `Maj1 P Q` iff `|[tⁿ]P| ≤ [tⁿ]Q` for all `n`. -/
abbrev Maj1 : ℝ[X] → ℝ[X] → Prop := polyRel absRel

/-- Two-variable coefficient majorants on `ℝ[X][X]`. -/
abbrev Maj2 : ℝ[X][X] → ℝ[X][X] → Prop := polyRel (polyRel absRel)

theorem isMaj1 : IsMaj Maj1 := isMaj_absRel.poly

theorem isMaj2 : IsMaj Maj2 := isMaj1.poly

theorem maj1_C {a b : ℝ} (h : |a| ≤ b) : Maj1 (C a) (C b) := isMaj_absRel.polyC h

theorem maj1_X : Maj1 X X := isMaj_absRel.polyX

theorem abs_coeff_le_of_maj1 {P Q : ℝ[X]} (h : Maj1 P Q) (n : ℕ) : |P.coeff n| ≤ Q.coeff n :=
  h n

/-- `[Xⁿ](u + bX)^M = binom(M, n) u^{M-n} bⁿ`. -/
theorem coeff_C_add_C_mul_X_pow {R : Type*} [CommRing R] (u b : R) (M n : ℕ) :
    ((C u + C b * X) ^ M).coeff n = (M.choose n : R) * u ^ (M - n) * b ^ n := by
  rw [add_comm, add_pow, finsetSum_coeff]
  have key : ∀ m ∈ Finset.range (M + 1),
      ((C b * X) ^ m * C u ^ (M - m) * (M.choose m : R[X])).coeff n =
        if n = m then (M.choose n : R) * u ^ (M - n) * b ^ n else 0 := by
    intro m _
    have e : (C b * X) ^ m * C u ^ (M - m) * (M.choose m : R[X]) =
        C (b ^ m * u ^ (M - m) * M.choose m) * X ^ m := by
      simp only [map_mul, map_pow, map_natCast]
      ring
    rw [e, coeff_C_mul_X_pow]
    split_ifs with h
    · subst h
      ring
    · rfl
  rw [Finset.sum_congr rfl key, Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · rw [Finset.mem_range, not_lt] at h
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp

/-! ### Derivatives of polynomials and along lines -/

theorem iteratedDeriv_eval (P : ℝ[X]) (n : ℕ) :
    iteratedDeriv n (fun t => P.eval t) = fun t => (derivative^[n] P).eval t := by
  induction n generalizing P with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ',
      show deriv (fun t => P.eval t) = fun t => (derivative P).eval t from
        funext fun t => Polynomial.deriv P, ih, Function.iterate_succ_apply]

/-- `(d/dt)ⁿ P(t)|_{t=0} = n! [tⁿ] P`. -/
theorem iteratedDeriv_eval_zero (P : ℝ[X]) (n : ℕ) :
    iteratedDeriv n (fun t => P.eval t) 0 = n ! * P.coeff n := by
  rw [iteratedDeriv_eval]
  dsimp only
  rw [← coeff_zero_eq_eval_zero, coeff_iterate_derivative, zero_add, Nat.descFactorial_self,
    nsmul_eq_mul]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Along a coordinate line, the `n`-th derivative of a `Cⁿ` function is `∂_iⁿ`. -/
theorem iteratedDeriv_line : ∀ (n : ℕ) {g : (ι → ℝ) → ℝ}, ContDiff ℝ n g →
    ∀ (x : ι → ℝ) (i : ι), iteratedDeriv n (fun t : ℝ => g (x + t • Pi.single i (1 : ℝ))) =
      fun t : ℝ => (pderiv i)^[n] g (x + t • Pi.single i (1 : ℝ))
  | 0, g, _, x, i => by simp
  | n + 1, g, hg, x, i => by
    have hd : Differentiable ℝ g := hg.differentiable (by norm_cast)
    have hderiv : deriv (fun t : ℝ => g (x + t • Pi.single i (1 : ℝ))) =
        fun t : ℝ => pderiv i g (x + t • Pi.single i (1 : ℝ)) := by
      funext t
      have hl : HasDerivAt (fun t : ℝ => x + t • (Pi.single i (1 : ℝ) : ι → ℝ))
          (Pi.single i (1 : ℝ) : ι → ℝ) t := by
        simpa using ((hasDerivAt_id t).smul_const (Pi.single i (1 : ℝ) : ι → ℝ)).const_add x
      exact ((hd _).hasFDerivAt.comp_hasDerivAt t hl).deriv
    rw [iteratedDeriv_succ', hderiv, iteratedDeriv_line n (contDiff_pderiv hg i) x i]
    funext t
    rw [Function.iterate_succ_apply]

/-- `∂_i^m` of a `C^{N+m}` function is `C^N`. -/
theorem contDiff_pderiv_iterate {N : ℕ} : ∀ (m : ℕ) {f : (ι → ℝ) → ℝ},
    ContDiff ℝ ((N + m : ℕ) : WithTop ℕ∞) f → ∀ i : ι,
      ContDiff ℝ (N : WithTop ℕ∞) ((pderiv i)^[m] f)
  | 0, f, hf, i => by simpa using hf
  | m + 1, f, hf, i => by
    rw [Function.iterate_succ_apply]
    exact contDiff_pderiv_iterate m (contDiff_pderiv (N := N + m) hf i) i

omit [Fintype ι] in
theorem pderiv_congr_nhds {f g : (ι → ℝ) → ℝ} {x : ι → ℝ} (h : f =ᶠ[𝓝 x] g) (i : ι) :
    pderiv i f =ᶠ[𝓝 x] pderiv i g :=
  h.eventuallyEq_nhds.mono fun y hy => by
    unfold pderiv
    rw [hy.fderiv_eq]

omit [Fintype ι] in
theorem pderiv_iterate_congr_nhds : ∀ (n : ℕ) {f g : (ι → ℝ) → ℝ} {x : ι → ℝ},
    f =ᶠ[𝓝 x] g → ∀ i : ι, (pderiv i)^[n] f =ᶠ[𝓝 x] (pderiv i)^[n] g
  | 0, _, _, _, h, _ => h
  | n + 1, _, _, _, h, i => by
    simp only [Function.iterate_succ_apply]
    exact pderiv_iterate_congr_nhds n (pderiv_congr_nhds h i) i

/-! ### Two-variable polynomials -/

/-- The monomial `κ t^m s^n` of `ℝ[X][X]` (inner variable `t = C X`, outer variable `s = X`). -/
noncomputable def mono2 (κ : ℝ) (m n : ℕ) : ℝ[X][X] := C (C κ) * (C X) ^ m * X ^ n

/-- The coefficient `[t^m s^n] P`. -/
noncomputable def coeff2 (P : ℝ[X][X]) (m n : ℕ) : ℝ := (P.coeff n).coeff m

theorem coeff2_add (P Q : ℝ[X][X]) (m n : ℕ) :
    coeff2 (P + Q) m n = coeff2 P m n + coeff2 Q m n := by
  simp [coeff2]

theorem coeff2_sub (P Q : ℝ[X][X]) (m n : ℕ) :
    coeff2 (P - Q) m n = coeff2 P m n - coeff2 Q m n := by
  simp [coeff2]

theorem coeff2_CC_mul (κ : ℝ) (P : ℝ[X][X]) (m n : ℕ) :
    coeff2 (C (C κ) * P) m n = κ * coeff2 P m n := by
  simp [coeff2, coeff_C_mul]

theorem coeff2_sum {α : Type*} (s : Finset α) (f : α → ℝ[X][X]) (m n : ℕ) :
    coeff2 (∑ a ∈ s, f a) m n = ∑ a ∈ s, coeff2 (f a) m n := by
  simp [coeff2]

theorem abs_coeff2_le_of_maj2 {P Q : ℝ[X][X]} (h : Maj2 P Q) (m n : ℕ) :
    |coeff2 P m n| ≤ coeff2 Q m n :=
  h n m

theorem maj2_mono {κ κ' : ℝ} (h : |κ| ≤ κ') (m n : ℕ) : Maj2 (mono2 κ m n) (mono2 κ' m n) :=
  isMaj2.mul (isMaj2.mul (isMaj1.polyC (maj1_C h)) (isMaj2.pow (isMaj1.polyC maj1_X) m))
    (isMaj2.pow isMaj1.polyX n)

theorem maj2_CC {κ κ' : ℝ} (h : |κ| ≤ κ') : Maj2 (C (C κ)) (C (C κ')) :=
  isMaj1.polyC (maj1_C h)

/-- Evaluation of `P ∈ ℝ[X][X]` at `(t, s)`. -/
noncomputable def ev2 (t s : ℝ) : ℝ[X][X] →+* ℝ :=
  (evalRingHom s).comp (mapRingHom (evalRingHom t))

theorem ev2_apply (t s : ℝ) (P : ℝ[X][X]) : ev2 t s P = (P.map (evalRingHom t)).eval s := by
  simp [ev2]

theorem ev2_CC (t s κ : ℝ) : ev2 t s (C (C κ)) = κ := by
  simp [ev2]

theorem ev2_mono (t s κ : ℝ) (m n : ℕ) : ev2 t s (mono2 κ m n) = κ * t ^ m * s ^ n := by
  simp [ev2, mono2]

/-- `(d/ds)ⁿ P(t, s)|_{s=0} = n! [sⁿ] P (t)`. -/
theorem iteratedDeriv_ev2 (P : ℝ[X][X]) (t : ℝ) (n : ℕ) :
    iteratedDeriv n (fun s => ev2 t s P) 0 = n ! * (P.coeff n).eval t := by
  simp only [ev2_apply]
  rw [iteratedDeriv_eval_zero, coeff_map, coe_evalRingHom]

end SecC

end BiluLinial.Tight
