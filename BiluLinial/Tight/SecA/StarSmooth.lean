/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecA.Defs
public import BiluLinial.Tight.Tools.Alpha2

/-!
# Calculus of clipped observables (sub-lemmas of `SecA/Star.lean`)

Proofs of the nodes `A-CLIP`, `A-CLIP0`, `A-MAJ`, `A-E5`, `A-SMOOTH` of `docs/tight/BP_SECA.md`
(source lines 296–343; AUDIT-A §2.4), stated in `SecA/Star.lean`. Everything lives in the
namespace `BiluLinial.Tight.SecA.StarCalc`.

* `pderiv` calculus: sums, products, constants, local congruence, and the line formula
  `∂_i G(x) = d/ds G(x + s e_i)|_{s=0}` (`pderiv_eq_of_line`).
* Quadratic functions: `quadFn c ℓ Q (x + s e_i) = q(x) + s (ℓ_i + ((Q + Qᵀ)x)_i) + s² Q_ii`
  (`quadFn_line`), hence `∂_i q = ℓ_i + ((Q + Qᵀ)x)_i` and `∂_j ∂_i q = Q_ij + Q_ji`.
* `A-CLIP`: `t ↦ t₊^e` is `C^{e-1}` (`contDiff_posPow'`), with derivative `k t₊^{k-1}` for
  `k ≥ 2`.
* `A-CLIP0` through the class `ClipGood φ ψ n` of finite sums `h φ₊^a ψ₊^b` with `h` smooth and
  `a, b > n`: one partial derivative maps `ClipGood n` into `ClipGood (n-1)` (for `n ≥ 1`), and
  every member of `ClipGood 0` vanishes where `φ ≤ 0` or `ψ ≤ 0`.
* `A-MAJ` through `MajAt x₀ λ M K f` (`|∂^l f(x₀)| ≤ M K^{|l|} λ^l` for all `l`), closed under
  products (`majBound_mul`: Leibniz by induction on `l`), with quadratics `MajAt m 2`.
* `A-E5`: at interior points `1 - q_A` satisfies `QuadMaj` with scale `1` and weights
  `√(A_ii + B_ii)` (`quadMaj_clip`, from `(Ax)_i² ≤ A_ii q_A(x)`, `mulVec_apply_sq_le`); off the
  interior `A-CLIP0` applies.
-/

@[expose] public section

namespace BiluLinial.Tight.SecA.StarCalc

open Matrix Filter Topology Function
open scoped ContDiff

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Smoothness of quadratic functions -/

omit [DecidableEq ι] in
theorem contDiff_qForm (M : Matrix ι ι ℝ) {n : WithTop ℕ∞} : ContDiff ℝ n (qForm M) := by
  unfold qForm
  simp only [dotProduct, mulVec]
  fun_prop

omit [DecidableEq ι] in
theorem contDiff_quadFn (c : ℝ) (ℓ : ι → ℝ) (Q : Matrix ι ι ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (quadFn c ℓ Q) := by
  have h := contDiff_qForm Q (n := n)
  unfold quadFn
  simp only [dotProduct]
  fun_prop

/-! ### `pderiv` calculus -/

theorem contDiff_pderiv_top {f : (ι → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (i : ι) :
    ContDiff ℝ ∞ (pderiv i f) :=
  (contDiff_infty_iff_fderiv.1 hf).2.clm_apply contDiff_const

omit [DecidableEq ι] in
theorem differentiable_of_top {f : (ι → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) : Differentiable ℝ f :=
  hf.differentiable (by simp)

theorem pderiv_add {f g : (ι → ℝ) → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (i : ι) : pderiv i (f + g) = pderiv i f + pderiv i g := by
  funext x
  simp only [pderiv, Pi.add_apply]
  rw [fderiv_add (hf x) (hg x)]
  rfl

theorem pderiv_mul {f g : (ι → ℝ) → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (i : ι) : pderiv i (f * g) = pderiv i f * g + f * pderiv i g := by
  funext x
  simp only [pderiv, Pi.add_apply, Pi.mul_apply]
  rw [fderiv_mul (hf x) (hg x)]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  ring

omit [Fintype ι] in
theorem pderiv_const (c : ℝ) (i : ι) : pderiv i (fun _ : ι → ℝ => c) = 0 := by
  funext x
  simp [pderiv]

omit [Fintype ι] in
theorem pderivList_zero (l : List ι) : pderivList l (0 : (ι → ℝ) → ℝ) = 0 := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    rw [pderivList_cons, show pderiv i (0 : (ι → ℝ) → ℝ) = 0 from pderiv_const 0 i, ih]

theorem pderivList_add (l : List ι) {f g : (ι → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) : pderivList l (f + g) = pderivList l f + pderivList l g := by
  induction l generalizing f g with
  | nil => rfl
  | cons i l ih =>
    rw [pderivList_cons, pderivList_cons, pderivList_cons,
      pderiv_add (differentiable_of_top hf) (differentiable_of_top hg) i]
    exact ih (contDiff_pderiv_top hf i) (contDiff_pderiv_top hg i)

omit [Fintype ι] in
theorem pderivList_congr_nhds {f g : (ι → ℝ) → ℝ} {x : ι → ℝ} (h : f =ᶠ[𝓝 x] g)
    (l : List ι) : pderivList l f =ᶠ[𝓝 x] pderivList l g := by
  induction l generalizing f g with
  | nil => exact h
  | cons i l ih =>
    refine ih ?_
    exact h.eventuallyEq_nhds.mono fun y hy => by
      unfold pderiv
      rw [hy.fderiv_eq]

/-- Along the line `s ↦ x + s e_i`, the derivative of a differentiable function is `∂_i`. -/
theorem hasDerivAt_line {G : (ι → ℝ) → ℝ} (hG : Differentiable ℝ G) (x : ι → ℝ) (i : ι)
    (t : ℝ) : HasDerivAt (fun s : ℝ => G (x + s • Pi.single i 1))
      (pderiv i G (x + t • Pi.single i 1)) t := by
  have hl : HasDerivAt (fun s : ℝ => x + s • (Pi.single i 1 : ι → ℝ)) (Pi.single i 1) t := by
    simpa using ((hasDerivAt_id t).smul_const (Pi.single i (1 : ℝ) : ι → ℝ)).const_add x
  exact (hG _).hasFDerivAt.comp_hasDerivAt t hl

theorem pderiv_eq_of_line {G : (ι → ℝ) → ℝ} (hG : Differentiable ℝ G) {x : ι → ℝ} {i : ι}
    {D : ℝ} (h : HasDerivAt (fun s : ℝ => G (x + s • Pi.single i 1)) D 0) :
    pderiv i G x = D := by
  have h0 := hasDerivAt_line hG x i 0
  simp only [zero_smul, add_zero] at h0
  exact h0.unique h

/-! ### Derivatives of quadratic functions -/

/-- `q(x + s e_i) = q(x) + s (ℓ_i + ((Q + Qᵀ)x)_i) + s² Q_ii` for `q = quadFn c ℓ Q`. -/
theorem quadFn_line (c : ℝ) (ℓ : ι → ℝ) (Q : Matrix ι ι ℝ) (x : ι → ℝ) (i : ι) (s : ℝ) :
    quadFn c ℓ Q (x + s • Pi.single i 1) =
      quadFn c ℓ Q x + s * (ℓ i + ((Q + Qᵀ) *ᵥ x) i) + s ^ 2 * Q i i := by
  have h1 : x ⬝ᵥ (Q *ᵥ Pi.single i 1) = (Qᵀ *ᵥ x) i := by
    rw [dotProduct_mulVec, mulVec_transpose, dotProduct_single_one]
  have h2 : Pi.single i 1 ⬝ᵥ (Q *ᵥ x) = (Q *ᵥ x) i := single_one_dotProduct i _
  have h3 : Pi.single i 1 ⬝ᵥ (Q *ᵥ Pi.single i 1) = Q i i := by
    rw [single_one_dotProduct, mulVec_single_one]; rfl
  have h4 : ℓ ⬝ᵥ Pi.single i 1 = ℓ i := dotProduct_single_one ℓ i
  simp only [quadFn, qForm, mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct,
    dotProduct_smul, smul_dotProduct, smul_eq_mul, h1, h2, h3, h4, add_mulVec, Pi.add_apply]
  ring

theorem pderiv_quadFn (c : ℝ) (ℓ : ι → ℝ) (Q : Matrix ι ι ℝ) (i : ι) :
    pderiv i (quadFn c ℓ Q) = fun x => ℓ i + ((Q + Qᵀ) *ᵥ x) i := by
  funext x
  refine pderiv_eq_of_line (differentiable_of_top (contDiff_quadFn c ℓ Q)) ?_
  have e : (fun s : ℝ => quadFn c ℓ Q (x + s • Pi.single i 1)) = fun s =>
      quadFn c ℓ Q x + s * (ℓ i + ((Q + Qᵀ) *ᵥ x) i) + s ^ 2 * Q i i := by
    funext s
    exact quadFn_line c ℓ Q x i s
  rw [e]
  exact ((((hasDerivAt_id (0 : ℝ)).mul_const (ℓ i + ((Q + Qᵀ) *ᵥ x) i)).const_add
    (quadFn c ℓ Q x)).add ((hasDerivAt_pow 2 (0 : ℝ)).mul_const (Q i i))).congr_deriv
    (by simp)

omit [DecidableEq ι] in
theorem affine_eq_quadFn (a : ℝ) (M : Matrix ι ι ℝ) (i : ι) :
    (fun x : ι → ℝ => a + (M *ᵥ x) i) = quadFn a (M i) 0 := by
  funext x
  simp only [quadFn, qForm, zero_mulVec, dotProduct_zero, add_zero]
  rfl

theorem pderiv_affine (a : ℝ) (M : Matrix ι ι ℝ) (i j : ι) :
    pderiv j (fun x : ι → ℝ => a + (M *ᵥ x) i) = fun _ => M i j := by
  rw [affine_eq_quadFn, pderiv_quadFn]
  funext x
  simp

/-! ### `A-CLIP`: clipped powers -/

/-- `t ↦ t₊^k` has derivative `k t₊^{k-1}` for `k ≥ 2`. -/
theorem hasDerivAt_posPow {k : ℕ} (hk : 2 ≤ k) (t : ℝ) :
    HasDerivAt (fun t : ℝ => max t 0 ^ k) (k * max t 0 ^ (k - 1)) t := by
  rcases lt_trichotomy t 0 with ht | ht | ht
  · have hev : (fun t : ℝ => max t 0 ^ k) =ᶠ[𝓝 t] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds ht] with s hs
      rw [max_eq_right (le_of_lt hs), zero_pow (by omega)]
    rw [max_eq_right ht.le, zero_pow (by omega), mul_zero]
    exact (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq hev
  · subst ht
    rw [max_self, zero_pow (by omega), mul_zero, hasDerivAt_iff_isLittleO]
    simp only [max_self, zero_pow (show k ≠ 0 by omega), sub_zero, smul_zero]
    have h1 : (fun x : ℝ => x ^ k) =o[𝓝 0] fun x => x := Asymptotics.isLittleO_pow_id (by omega)
    refine Asymptotics.IsBigO.trans_isLittleO ?_ h1
    refine Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall fun x => ?_)
    rw [one_mul, norm_pow, norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      exact max_le (le_abs_self x) (abs_nonneg x)) k
  · have hev : (fun t : ℝ => max t 0 ^ k) =ᶠ[𝓝 t] fun s => s ^ k := by
      filter_upwards [Ioi_mem_nhds ht] with s hs
      rw [max_eq_left (le_of_lt hs)]
    rw [max_eq_left ht.le]
    exact (hasDerivAt_pow k t).congr_of_eventuallyEq hev

theorem contDiff_posPow_succ (n : ℕ) :
    ContDiff ℝ (n : WithTop ℕ∞) (fun t : ℝ => max t 0 ^ (n + 1)) := by
  induction n with
  | zero =>
    rw [Nat.cast_zero, contDiff_zero]
    exact (continuous_id.max continuous_const).pow _
  | succ n ih =>
    have hd : deriv (fun t : ℝ => max t 0 ^ (n + 1 + 1)) =
        fun t => ((n + 1 + 1 : ℕ) : ℝ) * max t 0 ^ (n + 1) := by
      funext t
      exact (hasDerivAt_posPow (by omega) t).deriv
    rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by push_cast; rfl,
      contDiff_succ_iff_deriv]
    refine ⟨fun t => (hasDerivAt_posPow (by omega) t).differentiableAt,
      fun h => by simp at h, ?_⟩
    rw [hd]
    exact contDiff_const.mul ih

/-- **A-CLIP**: `t ↦ t₊^e` is `C^{e-1}`. -/
theorem contDiff_posPow' (e : ℕ) :
    ContDiff ℝ ((e - 1 : ℕ) : WithTop ℕ∞) (fun t : ℝ => max t 0 ^ e) := by
  cases e with
  | zero =>
    simp only [pow_zero]
    exact contDiff_const
  | succ n => simpa using contDiff_posPow_succ n

omit [DecidableEq ι] in
theorem contDiff_clipF_pow (A : Matrix ι ι ℝ) (e : ℕ) :
    ContDiff ℝ ((e - 1 : ℕ) : WithTop ℕ∞) (fun x => clipF A x ^ e) :=
  (contDiff_posPow' e).comp (contDiff_const.sub (contDiff_qForm A))

omit [DecidableEq ι] in
/-- **A-CLIP**: a clipped observable with smooth prefactor is `C^{min(e₁,e₂)-1}`. -/
theorem contDiff_clipObs' {g : (ι → ℝ) → ℝ} (hg : ContDiff ℝ ∞ g) (e₁ e₂ : ℕ)
    (A B : Matrix ι ι ℝ) :
    ContDiff ℝ ((min e₁ e₂ - 1 : ℕ) : WithTop ℕ∞) (clipObs g e₁ e₂ A B) := by
  have h1 := (contDiff_clipF_pow A e₁).of_le
    (show ((min e₁ e₂ - 1 : ℕ) : WithTop ℕ∞) ≤ ((e₁ - 1 : ℕ) : WithTop ℕ∞) by
      exact_mod_cast (by omega : min e₁ e₂ - 1 ≤ e₁ - 1))
  have h2 := (contDiff_clipF_pow B e₂).of_le
    (show ((min e₁ e₂ - 1 : ℕ) : WithTop ℕ∞) ≤ ((e₂ - 1 : ℕ) : WithTop ℕ∞) by
      exact_mod_cast (by omega : min e₁ e₂ - 1 ≤ e₂ - 1))
  have h0 := hg.of_le (show ((min e₁ e₂ - 1 : ℕ) : WithTop ℕ∞) ≤ ∞ from
    WithTop.coe_le_coe.2 le_top)
  exact (h0.mul h1).mul h2

/-! ### `A-CLIP0`: the class `ClipGood` -/

section ClipGood

variable (φ ψ : (ι → ℝ) → ℝ)

/-- Finite sums of terms `h φ₊^a ψ₊^b` with `h` smooth and `a, b > n`. -/
inductive ClipGood : ℕ → ((ι → ℝ) → ℝ) → Prop
  | term {n : ℕ} {h : (ι → ℝ) → ℝ} (hh : ContDiff ℝ ∞ h) {a b : ℕ} (ha : n < a) (hb : n < b) :
      ClipGood n (fun x => h x * max (φ x) 0 ^ a * max (ψ x) 0 ^ b)
  | add {n : ℕ} {f g : (ι → ℝ) → ℝ} : ClipGood n f → ClipGood n g → ClipGood n (f + g)

variable {φ ψ}

omit [DecidableEq ι] in
theorem hasFDerivAt_posPow_comp {k : ℕ} (hk : 2 ≤ k) {φ : (ι → ℝ) → ℝ}
    (hφ : Differentiable ℝ φ) (x : ι → ℝ) :
    HasFDerivAt (fun x => max (φ x) 0 ^ k) ((k * max (φ x) 0 ^ (k - 1)) • fderiv ℝ φ x) x :=
  (hasDerivAt_posPow hk (φ x)).comp_hasFDerivAt x (hφ x).hasFDerivAt

omit [DecidableEq ι] in
theorem hasFDerivAt_clipTerm {h : (ι → ℝ) → ℝ} (hh : ContDiff ℝ ∞ h) (hφ : ContDiff ℝ ∞ φ)
    (hψ : ContDiff ℝ ∞ ψ) {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) (x : ι → ℝ) :
    HasFDerivAt (fun x => h x * max (φ x) 0 ^ a * max (ψ x) 0 ^ b)
      ((h x * max (φ x) 0 ^ a) • ((b * max (ψ x) 0 ^ (b - 1)) • fderiv ℝ ψ x) +
        max (ψ x) 0 ^ b • (h x • ((a * max (φ x) 0 ^ (a - 1)) • fderiv ℝ φ x) +
          max (φ x) 0 ^ a • fderiv ℝ h x)) x :=
  (((differentiable_of_top hh) x).hasFDerivAt.mul
    (hasFDerivAt_posPow_comp ha (differentiable_of_top hφ) x)).mul
    (hasFDerivAt_posPow_comp hb (differentiable_of_top hψ) x)

theorem pderiv_clipTerm {h : (ι → ℝ) → ℝ} (hh : ContDiff ℝ ∞ h) (hφ : ContDiff ℝ ∞ φ)
    (hψ : ContDiff ℝ ∞ ψ) {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) (i : ι) :
    pderiv i (fun x => h x * max (φ x) 0 ^ a * max (ψ x) 0 ^ b) =
      (fun x => pderiv i h x * max (φ x) 0 ^ a * max (ψ x) 0 ^ b) +
      (fun x => (h x * a * pderiv i φ x) * max (φ x) 0 ^ (a - 1) * max (ψ x) 0 ^ b) +
      (fun x => (h x * b * pderiv i ψ x) * max (φ x) 0 ^ a * max (ψ x) 0 ^ (b - 1)) := by
  funext x
  have h1 := (hasFDerivAt_clipTerm hh hφ hψ ha hb x).fderiv
  simp only [pderiv, Pi.add_apply]
  rw [h1]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  ring

omit [DecidableEq ι] in
theorem ClipGood.differentiable (hφ : ContDiff ℝ ∞ φ) (hψ : ContDiff ℝ ∞ ψ) {n : ℕ}
    {f : (ι → ℝ) → ℝ} (hf : ClipGood φ ψ n f) (hn : 1 ≤ n) : Differentiable ℝ f := by
  induction hf with
  | term hh ha hb =>
    exact fun x => (hasFDerivAt_clipTerm hh hφ hψ (by omega) (by omega) x).differentiableAt
  | add _ _ ihf ihg => exact ihf.add ihg

theorem ClipGood.pderiv (hφ : ContDiff ℝ ∞ φ) (hψ : ContDiff ℝ ∞ ψ) {n : ℕ}
    {f : (ι → ℝ) → ℝ} (hf : ClipGood φ ψ n f) (hn : 1 ≤ n) (i : ι) :
    ClipGood φ ψ (n - 1) (pderiv i f) := by
  induction hf with
  | term hh ha hb =>
    rw [pderiv_clipTerm hh hφ hψ (by omega) (by omega) i]
    refine ((ClipGood.term (contDiff_pderiv_top hh i) (by omega) (by omega)).add
      (ClipGood.term ?_ (by omega) (by omega))).add (ClipGood.term ?_ (by omega) (by omega))
    · exact (hh.mul contDiff_const).mul (contDiff_pderiv_top hφ i)
    · exact (hh.mul contDiff_const).mul (contDiff_pderiv_top hψ i)
  | add hf hg ihf ihg =>
    rw [pderiv_add (hf.differentiable hφ hψ hn) (hg.differentiable hφ hψ hn)]
    exact ihf.add ihg

theorem ClipGood.pderivList (hφ : ContDiff ℝ ∞ φ) (hψ : ContDiff ℝ ∞ ψ) :
    ∀ (l : List ι) {n : ℕ} {f : (ι → ℝ) → ℝ}, ClipGood φ ψ n f → l.length ≤ n →
      ClipGood φ ψ (n - l.length) (BiluLinial.Tight.pderivList l f)
  | [], n, f, hf, _ => by simpa using hf
  | i :: l, n, f, hf, hl => by
    simp only [List.length_cons] at hl ⊢
    rw [pderivList_cons]
    have := ClipGood.pderivList hφ hψ l (hf.pderiv hφ hψ (by omega) i) (by omega)
    rwa [show n - 1 - l.length = n - (l.length + 1) by omega] at this

omit [DecidableEq ι] in
theorem ClipGood.eq_zero {n : ℕ} {f : (ι → ℝ) → ℝ} (hf : ClipGood φ ψ n f) {x : ι → ℝ}
    (hx : φ x ≤ 0 ∨ ψ x ≤ 0) : f x = 0 := by
  induction hf with
  | @term h hh a b ha hb =>
    rcases hx with hx | hx
    · simp only [max_eq_right hx, zero_pow (show a ≠ 0 by omega), mul_zero, zero_mul]
    · simp only [max_eq_right hx, zero_pow (show b ≠ 0 by omega), mul_zero]
  | add _ _ ihf ihg => simp only [Pi.add_apply, ihf, ihg, add_zero]

end ClipGood

/-- **A-CLIP0**: derivatives of order `< min(e₁,e₂)` of a clipped observable vanish outside
`{q_A < 1, q_B < 1}`. -/
theorem pderivList_clipObs_eq_zero' {g : (ι → ℝ) → ℝ} (hg : ContDiff ℝ ∞ g) {e₁ e₂ : ℕ}
    {A B : Matrix ι ι ℝ} (l : List ι) (hl : l.length < min e₁ e₂) {x : ι → ℝ}
    (hx : 1 ≤ qForm A x ∨ 1 ≤ qForm B x) : pderivList l (clipObs g e₁ e₂ A B) x = 0 := by
  have hφ : ContDiff ℝ ∞ (fun x => 1 - qForm A x) := contDiff_const.sub (contDiff_qForm A)
  have hψ : ContDiff ℝ ∞ (fun x => 1 - qForm B x) := contDiff_const.sub (contDiff_qForm B)
  have h0 : ClipGood (fun x => 1 - qForm A x) (fun x => 1 - qForm B x) (min e₁ e₂ - 1)
      (clipObs g e₁ e₂ A B) :=
    ClipGood.term (h := g) hg (a := e₁) (b := e₂) (by omega) (by omega)
  refine (h0.pderivList hφ hψ l (by omega)).eq_zero ?_
  rcases hx with h | h
  · left; show 1 - qForm A x ≤ 0; linarith
  · right; show 1 - qForm B x ≤ 0; linarith

/-! ### `A-MAJ`: majorant bounds are closed under products -/

/-- `f` is smooth and `|∂^l f(x₀)| ≤ M K^{|l|} λ^l` for every list of coordinates `l`. -/
def MajAt (x₀ lam : ι → ℝ) (M K : ℝ) (f : (ι → ℝ) → ℝ) : Prop :=
  ContDiff ℝ ∞ f ∧ ∀ l : List ι, |pderivList l f x₀| ≤ M * K ^ l.length * (l.map lam).prod

omit [Fintype ι] [DecidableEq ι] in
theorem prod_map_nonneg {lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i) (l : List ι) :
    0 ≤ (l.map lam).prod :=
  List.prod_nonneg fun a ha => by
    obtain ⟨b, -, rfl⟩ := List.mem_map.1 ha
    exact hlam b

/-- Leibniz closure: bounds `M₁ K₁^n λ^ν`, `M₂ K₂^n λ^ν` give `M₁ M₂ (K₁ + K₂)^n λ^ν` for the
product (`Σ_a C(n,a) K₁^a K₂^{n-a} = (K₁ + K₂)^n`, by induction on the list). -/
theorem majBound_mul {x₀ lam : ι → ℝ} {K₁ K₂ : ℝ} :
    ∀ (l : List ι) {f g : (ι → ℝ) → ℝ} {M₁ M₂ : ℝ}, ContDiff ℝ ∞ f → ContDiff ℝ ∞ g →
      (∀ l' : List ι, |pderivList l' f x₀| ≤ M₁ * K₁ ^ l'.length * (l'.map lam).prod) →
      (∀ l' : List ι, |pderivList l' g x₀| ≤ M₂ * K₂ ^ l'.length * (l'.map lam).prod) →
      |pderivList l (f * g) x₀| ≤ M₁ * M₂ * (K₁ + K₂) ^ l.length * (l.map lam).prod
  | [], f, g, M₁, M₂, _, _, hf, hg => by
    have h1 := hf []
    have h2 := hg []
    simp only [pderivList_nil, List.length_nil, pow_zero, mul_one, List.map_nil,
      List.prod_nil] at h1 h2
    simp only [pderivList_nil, Pi.mul_apply, abs_mul, List.length_nil, pow_zero, mul_one,
      List.map_nil, List.prod_nil]
    exact mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1)
  | i :: l, f, g, M₁, M₂, hfc, hgc, hf, hg => by
    have hf' : ∀ l' : List ι, |pderivList l' (pderiv i f) x₀| ≤
        (M₁ * K₁ * lam i) * K₁ ^ l'.length * (l'.map lam).prod := fun l' => by
      have h := hf (i :: l')
      simp only [pderivList_cons, List.length_cons, List.map_cons, List.prod_cons,
        pow_succ] at h
      exact h.trans_eq (by ring)
    have hg' : ∀ l' : List ι, |pderivList l' (pderiv i g) x₀| ≤
        (M₂ * K₂ * lam i) * K₂ ^ l'.length * (l'.map lam).prod := fun l' => by
      have h := hg (i :: l')
      simp only [pderivList_cons, List.length_cons, List.map_cons, List.prod_cons,
        pow_succ] at h
      exact h.trans_eq (by ring)
    have h1 := majBound_mul l (contDiff_pderiv_top hfc i) hgc hf' hg
    have h2 := majBound_mul l hfc (contDiff_pderiv_top hgc i) hf hg'
    rw [pderivList_cons, pderiv_mul (differentiable_of_top hfc) (differentiable_of_top hgc),
      pderivList_add l (f := pderiv i f * g) (g := f * pderiv i g)
        ((contDiff_pderiv_top hfc i).mul hgc) (hfc.mul (contDiff_pderiv_top hgc i)), Pi.add_apply]
    simp only [List.length_cons, List.map_cons, List.prod_cons, pow_succ]
    calc _ ≤ _ := abs_add_le _ _
      _ ≤ _ := add_le_add h1 h2
      _ = _ := by ring

theorem majAt_one (x₀ lam : ι → ℝ) : MajAt x₀ lam 1 0 (1 : (ι → ℝ) → ℝ) := by
  refine ⟨contDiff_const, fun l => ?_⟩
  cases l with
  | nil => simp
  | cons i l =>
    rw [pderivList_cons, show pderiv i (1 : (ι → ℝ) → ℝ) = 0 from pderiv_const 1 i,
      pderivList_zero]
    simp

theorem MajAt.mul {x₀ lam : ι → ℝ} {M₁ M₂ K₁ K₂ : ℝ} {f g : (ι → ℝ) → ℝ}
    (hf : MajAt x₀ lam M₁ K₁ f) (hg : MajAt x₀ lam M₂ K₂ g) :
    MajAt x₀ lam (M₁ * M₂) (K₁ + K₂) (f * g) :=
  ⟨hf.1.mul hg.1, fun l => majBound_mul l hf.1 hg.1 hf.2 hg.2⟩

theorem MajAt.pow {x₀ lam : ι → ℝ} {M K : ℝ} {f : (ι → ℝ) → ℝ} (hf : MajAt x₀ lam M K f)
    (e : ℕ) : MajAt x₀ lam (M ^ e) (e * K) (f ^ e) := by
  induction e with
  | zero => simpa using majAt_one x₀ lam
  | succ e ih =>
    have e' : ((e + 1 : ℕ) : ℝ) * K = e * K + K := by push_cast; ring
    rw [e', pow_succ, pow_succ]
    exact ih.mul hf

/-- A quadratic satisfying the majorant condition `QuadMaj` with scale `m` is `MajAt m 2`:
`|∂^ν q(x₀)| ≤ m 2^n λ^ν` (orders `0, 1, 2` by `QuadMaj`, higher orders vanish). -/
theorem majAt_quadFn {c : ℝ} {ℓ : ι → ℝ} {Q : Matrix ι ι ℝ} {x₀ : ι → ℝ} {m : ℝ}
    {lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i) (h : QuadMaj c ℓ Q x₀ m lam) :
    MajAt x₀ lam m 2 (quadFn c ℓ Q) := by
  have hm : 0 ≤ m := (abs_nonneg _).trans h.h0
  refine ⟨contDiff_quadFn c ℓ Q, fun l => ?_⟩
  rcases l with _ | ⟨i, _ | ⟨j, _ | ⟨k, l⟩⟩⟩
  · simpa using h.h0
  · simp only [pderivList_cons, pderivList_nil, pderiv_quadFn, List.length_cons,
      List.length_nil, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
    have := h.h1 i
    norm_num
    linarith
  · simp only [pderivList_cons, pderivList_nil, pderiv_quadFn, pderiv_affine,
      List.length_cons, List.length_nil, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, Matrix.add_apply, Matrix.transpose_apply]
    have h2 := h.h2 i j
    have hP : 0 ≤ m * lam i * lam j := mul_nonneg (mul_nonneg hm (hlam i)) (hlam j)
    calc |Q i j + Q j i| ≤ 2 * m * lam i * lam j := h2
      _ ≤ m * 2 ^ (0 + 1 + 1) * (lam i * (lam j * 1)) := by
        norm_num
        linarith
  · rw [pderivList_cons, pderivList_cons, pderivList_cons, pderiv_quadFn, pderiv_affine,
      pderiv_const, pderivList_zero]
    simp only [Pi.zero_apply, abs_zero]
    exact mul_nonneg (mul_nonneg hm (by positivity)) (prod_map_nonneg hlam _)

omit [DecidableEq ι] in
theorem quadFn_one_zero_neg (A : Matrix ι ι ℝ) (x : ι → ℝ) :
    quadFn 1 0 (-A) x = 1 - qForm A x := by
  simp only [quadFn, qForm, zero_dotProduct, neg_mulVec, dotProduct_neg]
  ring

/-- **A-MAJ** (majorant lemma at an interior point). -/
theorem pderivList_clipObs_le_of_interior' {A B : Matrix ι ι ℝ} {e₁ e₂ : ℕ} {c : ℝ}
    {ℓ : ι → ℝ} {Q : Matrix ι ι ℝ} {x₀ : ι → ℝ} (hα : qForm A x₀ < 1) (hβ : qForm B x₀ < 1)
    {mg mα mβ : ℝ} {lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i) (hg : QuadMaj c ℓ Q x₀ mg lam)
    (hA : QuadMaj 1 0 (-A) x₀ mα lam) (hB : QuadMaj 1 0 (-B) x₀ mβ lam) (l : List ι) :
    |pderivList l (clipObs (quadFn c ℓ Q) e₁ e₂ A B) x₀| ≤
      mg * mα ^ e₁ * mβ ^ e₂ * (2 * (1 + e₁ + e₂ : ℝ)) ^ l.length * (l.map lam).prod := by
  have hM := ((majAt_quadFn hlam hg).mul ((majAt_quadFn hlam hA).pow e₁)).mul
    ((majAt_quadFn hlam hB).pow e₂)
  have hev : clipObs (quadFn c ℓ Q) e₁ e₂ A B =ᶠ[𝓝 x₀]
      quadFn c ℓ Q * quadFn 1 0 (-A) ^ e₁ * quadFn 1 0 (-B) ^ e₂ := by
    filter_upwards [(isOpen_lt (continuous_qForm A) continuous_const).mem_nhds hα,
      (isOpen_lt (continuous_qForm B) continuous_const).mem_nhds hβ] with x hxA hxB
    simp only [clipObs, Pi.mul_apply, Pi.pow_apply, clipF_eq_of_lt hxA, clipF_eq_of_lt hxB,
      quadFn_one_zero_neg]
  rw [(pderivList_congr_nhds hev l).eq_of_nhds]
  have h := hM.2 l
  have hK : (2 : ℝ) + e₁ * 2 + e₂ * 2 = 2 * (1 + e₁ + e₂) := by ring
  rwa [hK] at h

/-! ### `A-E5`, `A-SMOOTH` -/

omit [Fintype ι] [DecidableEq ι] in
theorem psd_transpose {A : Matrix ι ι ℝ} (hA : A.PosSemidef) : Aᵀ = A := by
  simpa [conjTranspose_eq_transpose_of_trivial] using hA.isHermitian.eq

theorem qForm_line (M : Matrix ι ι ℝ) (x : ι → ℝ) (i : ι) (s : ℝ) :
    qForm M (x + s • Pi.single i 1) = qForm M x + s * ((M + Mᵀ) *ᵥ x) i + s ^ 2 * M i i := by
  have h := quadFn_line 0 0 M x i s
  simpa [quadFn] using h

/-- Cauchy–Schwarz for a PSD form: `(Ax)_i² ≤ A_ii q_A(x)`. -/
theorem mulVec_apply_sq_le {A : Matrix ι ι ℝ} (hA : A.PosSemidef) (x : ι → ℝ) (i : ι) :
    (A *ᵥ x) i ^ 2 ≤ A i i * qForm A x := by
  have hs : (A + Aᵀ) *ᵥ x = (2 : ℝ) • (A *ᵥ x) := by
    rw [psd_transpose hA, ← two_smul ℝ A, Matrix.smul_mulVec]
  have h : ∀ t : ℝ, 0 ≤ A i i * (t * t) + 2 * (A *ᵥ x) i * t + qForm A x := by
    intro t
    have h0 := qForm_nonneg hA (x + t • Pi.single i 1)
    rw [qForm_line, hs] at h0
    simp only [Pi.smul_apply, smul_eq_mul] at h0
    exact h0.trans_eq (by ring)
  have hd := discrim_le_zero h
  rw [discrim] at hd
  nlinarith [hd]

theorem psd_entry_sq_le {A : Matrix ι ι ℝ} (hA : A.PosSemidef) (i j : ι) :
    A i j ^ 2 ≤ A i i * A j j := by
  have h := mulVec_apply_sq_le hA (Pi.single j 1) i
  have e1 : (A *ᵥ Pi.single j 1) i = A i j := by rw [mulVec_single_one]; rfl
  have e2 : qForm A (Pi.single j 1) = A j j := by
    rw [qForm, single_one_dotProduct, mulVec_single_one]; rfl
  rwa [e1, e2] at h

/-- The factor `1 - q_A` satisfies `QuadMaj` with scale `1` and weights `√w_i` (`A_ii ≤ w_i`) at
every point of `{q_A < 1}` (AUDIT-A §2.4: `|(Ax)_i| ≤ √(A_ii q_A)`, `|A_ij| ≤ √(A_ii A_jj)`). -/
theorem quadMaj_clip {A : Matrix ι ι ℝ} (hA : A.PosSemidef) {w : ι → ℝ}
    (hw : ∀ i, A i i ≤ w i) {x : ι → ℝ} (hx : qForm A x < 1) :
    QuadMaj 1 0 (-A) x 1 (fun i => Real.sqrt (w i)) := by
  have hq0 := qForm_nonneg hA x
  have hAt := psd_transpose hA
  have hdiag : ∀ i, 0 ≤ A i i := fun i => hA.diag_nonneg
  refine ⟨?_, fun i => ?_, fun i j => ?_⟩
  · rw [quadFn_one_zero_neg, abs_of_nonneg (by linarith)]
    linarith
  · have e : (0 : ι → ℝ) i + ((-A + (-A)ᵀ) *ᵥ x) i = -(2 * (A *ᵥ x) i) := by
      rw [transpose_neg, hAt, add_mulVec, neg_mulVec]
      simp only [Pi.zero_apply, Pi.add_apply, Pi.neg_apply]
      ring
    rw [e, abs_neg, abs_mul, abs_two]
    have h1 : |(A *ᵥ x) i| ≤ Real.sqrt (w i) := by
      refine Real.abs_le_sqrt ?_
      have h2 := mulVec_apply_sq_le hA x i
      have h3 := mul_le_mul_of_nonneg_left hx.le (hdiag i)
      have h4 := hw i
      nlinarith
    linarith
  · have hji : A j i = A i j := by
      have h := congrFun (congrFun hAt i) j
      simpa using h
    have e : (-A) i j + (-A) j i = -(2 * A i j) := by
      simp only [Matrix.neg_apply, hji]
      ring
    rw [e, abs_neg, abs_mul, abs_two]
    have h2 : |A i j| ≤ Real.sqrt (w i) * Real.sqrt (w j) := by
      rw [← Real.sqrt_mul ((hdiag i).trans (hw i))]
      exact Real.abs_le_sqrt ((psd_entry_sq_le hA i j).trans
        (mul_le_mul (hw i) (hw j) (hdiag j) ((hdiag i).trans (hw i))))
    linarith

/-- **A-E5**: sup bounds of the derivatives of a clipped observable (orders `< min(e₁,e₂)`). -/
theorem pderivList_clipObs_le' {A B : Matrix ι ι ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    {e₁ e₂ : ℕ} {c : ℝ} {ℓ : ι → ℝ} {Q : Matrix ι ι ℝ} {m : ℝ}
    (hg : ∀ x, qForm A x < 1 → qForm B x < 1 →
      QuadMaj c ℓ Q x m fun i => Real.sqrt (A i i + B i i))
    (l : List ι) (hl : l.length < min e₁ e₂) (x : ι → ℝ) :
    |pderivList l (clipObs (quadFn c ℓ Q) e₁ e₂ A B) x| ≤
      m * (2 * (1 + e₁ + e₂ : ℝ)) ^ l.length *
        (l.map fun i => Real.sqrt (A i i + B i i)).prod := by
  have hlam : ∀ i, 0 ≤ Real.sqrt (A i i + B i i) := fun i => Real.sqrt_nonneg _
  have h00 : qForm A 0 < 1 := by simp [qForm]
  have h00' : qForm B 0 < 1 := by simp [qForm]
  have hm : 0 ≤ m := (abs_nonneg _).trans (hg 0 h00 h00').h0
  by_cases hx : qForm A x < 1 ∧ qForm B x < 1
  · have h := pderivList_clipObs_le_of_interior' (e₁ := e₁) (e₂ := e₂) hx.1 hx.2 hlam
      (hg x hx.1 hx.2)
      (quadMaj_clip hA (fun i => le_add_of_nonneg_right (hB.diag_nonneg (i := i))) hx.1)
      (quadMaj_clip hB (fun i => le_add_of_nonneg_left (hA.diag_nonneg (i := i))) hx.2) l
    simpa only [one_pow, mul_one] using h
  · have hx' : 1 ≤ qForm A x ∨ 1 ≤ qForm B x :=
      (not_and_or.1 hx).imp not_lt.1 not_lt.1
    rw [pderivList_clipObs_eq_zero' (contDiff_quadFn c ℓ Q) l hl hx', abs_zero]
    exact mul_nonneg (mul_nonneg hm (by positivity)) (prod_map_nonneg hlam l)

/-- **A-SMOOTH**: clipped observables are `SmoothBdd` up to order `min(e₁,e₂) - 1`. -/
theorem smoothBdd_clipObs' {A B : Matrix ι ι ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    {e₁ e₂ : ℕ} {c : ℝ} {ℓ : ι → ℝ} {Q : Matrix ι ι ℝ} {m : ℝ}
    (hg : ∀ x, qForm A x < 1 → qForm B x < 1 →
      QuadMaj c ℓ Q x m fun i => Real.sqrt (A i i + B i i))
    {n : ℕ} (hn : n < min e₁ e₂) :
    SmoothBdd n (clipObs (quadFn c ℓ Q) e₁ e₂ A B) :=
  ⟨(contDiff_clipObs' (contDiff_quadFn c ℓ Q) e₁ e₂ A B).of_le
      (by exact_mod_cast (by omega : n ≤ min e₁ e₂ - 1)),
    fun l hl => ⟨_, fun x => pderivList_clipObs_le' hA hB hg l (by omega) x⟩⟩

end BiluLinial.Tight.SecA.StarCalc
