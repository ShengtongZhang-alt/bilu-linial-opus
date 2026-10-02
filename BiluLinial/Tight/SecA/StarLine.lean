/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecA.StarSmooth

/-!
# The single-coordinate coefficient majorant (sub-lemmas of `A-EPB4`)

Node `A-EPB4` of `docs/tight/BP_SECA.md` (source lines 509–527; AUDIT-A §2.6, gap A7). At a
point `x₀` with `q_A(x₀), q_B(x₀) < 1` the clipped observable `F = q α₊^{e₁} β₊^{e₂}` agrees near
`x₀` with the polynomial `q (1 - q_A)^{e₁} (1 - q_B)^{e₂}`, whose restriction to the line
`x₀ + s e_i` is the polynomial `P(s) = q(s) α(s)^{e₁} β(s)^{e₂}` with quadratic factors. Then

* `∂_i^k F(x₀) = k! [s^k] P` (`iter_pderiv_line`, `iteratedDeriv_eval_poly_zero`);
* `α(s) = α₀ (1 + (a₁/α₀) s + (a₂/α₀) s²)` and coefficientwise majorization
  (`CoeffMaj`, closed under products) gives
  `|[s^k] P| ≤ α₀^{e₁} β₀^{e₂} [s^k] (m₀ + m₁ s + m₂ s²)(1 + 2r_α s + ω_α s²)^{e₁}(…)^{e₂}`.
-/

@[expose] public section

namespace BiluLinial.Tight.SecA.StarCalc

open Matrix Filter Topology Function Polynomial
open scoped ContDiff

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Iterated partials along a coordinate line -/

/-- `∂_i^k G(x + t e_i) = (d/ds)^k G(x + s e_i)|_{s=t}` for smooth `G`. -/
theorem iter_pderiv_line {G : (ι → ℝ) → ℝ} (hG : ContDiff ℝ ∞ G) (x : ι → ℝ) (i : ι) (k : ℕ)
    (t : ℝ) : (pderiv i)^[k] G (x + t • Pi.single i 1) =
      iteratedDeriv k (fun s => G (x + s • Pi.single i 1)) t := by
  induction k generalizing G t with
  | zero => simp
  | succ k ih =>
    rw [iterate_succ_apply, ih (contDiff_pderiv_top hG i) t, iteratedDeriv_succ']
    have e : (fun s : ℝ => pderiv i G (x + s • Pi.single i 1)) =
        deriv (fun s : ℝ => G (x + s • Pi.single i 1)) := by
      funext s
      exact ((hasDerivAt_line (differentiable_of_top hG) x i s).deriv).symm
    rw [e]

theorem iteratedDeriv_eval_poly (P : ℝ[X]) (k : ℕ) :
    iteratedDeriv k (fun s => P.eval s) = fun s => (derivative^[k] P).eval s := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ, ih, iterate_succ_apply']
    funext s
    exact Polynomial.deriv _

theorem iteratedDeriv_eval_poly_zero (P : ℝ[X]) (k : ℕ) :
    iteratedDeriv k (fun s => P.eval s) 0 = k.factorial * P.coeff k := by
  simp only [iteratedDeriv_eval_poly]
  rw [← coeff_zero_eq_eval_zero, coeff_iterate_derivative, zero_add,
    Nat.descFactorial_self, nsmul_eq_mul]

/-! ### Coefficientwise majorization -/

/-- `R` majorizes `P` coefficientwise: `|[s^n] P| ≤ [s^n] R`. -/
def CoeffMaj (P R : ℝ[X]) : Prop := ∀ n, |P.coeff n| ≤ R.coeff n

theorem CoeffMaj.mul {P₁ P₂ R₁ R₂ : ℝ[X]} (h₁ : CoeffMaj P₁ R₁) (h₂ : CoeffMaj P₂ R₂) :
    CoeffMaj (P₁ * P₂) (R₁ * R₂) := by
  intro n
  rw [coeff_mul, coeff_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  rw [abs_mul]
  exact mul_le_mul (h₁ _) (h₂ _) (abs_nonneg _) ((abs_nonneg _).trans (h₁ _))

theorem coeffMaj_one : CoeffMaj 1 1 := by
  intro n
  rw [coeff_one]
  split_ifs <;> simp

theorem CoeffMaj.pow {P R : ℝ[X]} (h : CoeffMaj P R) (e : ℕ) : CoeffMaj (P ^ e) (R ^ e) := by
  induction e with
  | zero => simpa using coeffMaj_one
  | succ e ih =>
    rw [pow_succ, pow_succ]
    exact ih.mul h

theorem coeffMaj_quad {a b c a' b' c' : ℝ} (ha : |a| ≤ a') (hb : |b| ≤ b') (hc : |c| ≤ c') :
    CoeffMaj (C a + C b * X + C c * X ^ 2) (C a' + C b' * X + C c' * X ^ 2) := by
  intro n
  simp only [coeff_add, coeff_C, coeff_C_mul_X, coeff_C_mul_X_pow]
  rcases n with _ | _ | _ | n <;> simp [ha, hb, hc]

theorem quad_factor {a : ℝ} (ha : a ≠ 0) (b c : ℝ) :
    C a + C b * X + C c * X ^ 2 = C a * (1 + C (b / a) * X + C (c / a) * X ^ 2) := by
  have h1 : a * (b / a) = b := by field_simp
  have h2 : a * (c / a) = c := by field_simp
  rw [mul_add, mul_add, mul_one, ← mul_assoc, ← mul_assoc, ← C_mul, ← C_mul, h1, h2]

/-- The restriction of `quadFn c ℓ Q` to the line `x + s e_i`, as a polynomial in `s`. -/
noncomputable def linePoly (c : ℝ) (ℓ : ι → ℝ) (Q : Matrix ι ι ℝ) (x : ι → ℝ) (i : ι) : ℝ[X] :=
  C (quadFn c ℓ Q x) + C (ℓ i + ((Q + Qᵀ) *ᵥ x) i) * X + C (Q i i) * X ^ 2

theorem eval_linePoly (c : ℝ) (ℓ : ι → ℝ) (Q : Matrix ι ι ℝ) (x : ι → ℝ) (i : ι) (s : ℝ) :
    (linePoly c ℓ Q x i).eval s = quadFn c ℓ Q (x + s • Pi.single i 1) := by
  rw [quadFn_line]
  simp only [linePoly, eval_add, eval_mul, eval_C, eval_X, eval_pow]
  ring

omit [DecidableEq ι] in
/-- The factor `1 - q_A` on the line, normalized by `α₀ = 1 - q_A(x₀) > 0`, is majorized by
`1 + 2r s + w s²` when `|((A + Aᵀ)x₀)_i| ≤ 2 r α₀` and `|A_ii| ≤ w α₀`. -/
theorem linePoly_clip_factor {A : Matrix ι ι ℝ} {x₀ : ι → ℝ} (hα : qForm A x₀ < 1) (i : ι)
    {r w : ℝ} (h1 : |((A + Aᵀ) *ᵥ x₀) i| ≤ 2 * r * clipF A x₀)
    (h2 : |A i i| ≤ w * clipF A x₀) :
    ∃ U : ℝ[X], linePoly 1 0 (-A) x₀ i = C (clipF A x₀) * U ∧
      CoeffMaj U (1 + C (2 * r) * X + C w * X ^ 2) := by
  have hcl : clipF A x₀ = 1 - qForm A x₀ := clipF_eq_of_lt hα
  have hα0 : 0 < clipF A x₀ := by rw [hcl]; linarith
  set b : ℝ := (0 : ι → ℝ) i + ((-A + (-A)ᵀ) *ᵥ x₀) i with hb
  have hbabs : |b| = |((A + Aᵀ) *ᵥ x₀) i| := by
    rw [hb, transpose_neg, ← neg_add, neg_mulVec, Pi.neg_apply, Pi.zero_apply, zero_add,
      abs_neg]
  refine ⟨1 + C (b / clipF A x₀) * X + C ((-A) i i / clipF A x₀) * X ^ 2, ?_, ?_⟩
  · rw [← quad_factor hα0.ne', linePoly, quadFn_one_zero_neg, ← hcl]
  · have := coeffMaj_quad (a := 1) (a' := 1) (b := b / clipF A x₀) (b' := 2 * r)
      (c := (-A) i i / clipF A x₀) (c' := w) (by simp)
      (by rw [abs_div, abs_of_pos hα0, div_le_iff₀ hα0, hbabs]; exact h1)
      (by rw [abs_div, abs_of_pos hα0, div_le_iff₀ hα0, Matrix.neg_apply, abs_neg]; exact h2)
    simpa only [map_one] using this

/-- **A-EPB4**: the refined single-coordinate bound (coefficient majorant in one variable). -/
theorem iter_pderiv_clipObs_le' {A B : Matrix ι ι ℝ} {e₁ e₂ : ℕ} {c : ℝ} {ℓ : ι → ℝ}
    {Q : Matrix ι ι ℝ} {x₀ : ι → ℝ} (hα : qForm A x₀ < 1) (hβ : qForm B x₀ < 1) (i : ι)
    {m₀ m₁ m₂ rα ωα rβ ωβ : ℝ} (h0 : |quadFn c ℓ Q x₀| ≤ m₀)
    (h1 : |ℓ i + ((Q + Qᵀ) *ᵥ x₀) i| ≤ m₁) (h2 : |Q i i| ≤ m₂)
    (hα1 : |((A + Aᵀ) *ᵥ x₀) i| ≤ 2 * rα * clipF A x₀) (hα2 : |A i i| ≤ ωα * clipF A x₀)
    (hβ1 : |((B + Bᵀ) *ᵥ x₀) i| ≤ 2 * rβ * clipF B x₀) (hβ2 : |B i i| ≤ ωβ * clipF B x₀)
    (k : ℕ) :
    |(pderiv i)^[k] (clipObs (quadFn c ℓ Q) e₁ e₂ A B) x₀| ≤
      k.factorial * clipF A x₀ ^ e₁ * clipF B x₀ ^ e₂ *
        ((C m₀ + C m₁ * X + C m₂ * X ^ 2) * (1 + C (2 * rα) * X + C ωα * X ^ 2) ^ e₁ *
          (1 + C (2 * rβ) * X + C ωβ * X ^ 2) ^ e₂).coeff k := by
  set F' : (ι → ℝ) → ℝ := quadFn c ℓ Q * quadFn 1 0 (-A) ^ e₁ * quadFn 1 0 (-B) ^ e₂
    with hF'
  have hF'c : ContDiff ℝ ∞ F' :=
    ((contDiff_quadFn c ℓ Q).mul ((contDiff_quadFn 1 0 (-A)).pow e₁)).mul
      ((contDiff_quadFn 1 0 (-B)).pow e₂)
  have hev : clipObs (quadFn c ℓ Q) e₁ e₂ A B =ᶠ[𝓝 x₀] F' := by
    filter_upwards [(isOpen_lt (continuous_qForm A) continuous_const).mem_nhds hα,
      (isOpen_lt (continuous_qForm B) continuous_const).mem_nhds hβ] with x hxA hxB
    simp only [hF', clipObs, Pi.mul_apply, Pi.pow_apply, clipF_eq_of_lt hxA, clipF_eq_of_lt hxB,
      quadFn_one_zero_neg]
  have hk : (pderiv i)^[k] (clipObs (quadFn c ℓ Q) e₁ e₂ A B) x₀ = (pderiv i)^[k] F' x₀ := by
    rw [← pderivList_replicate, ← pderivList_replicate]
    exact (pderivList_congr_nhds hev _).eq_of_nhds
  set P : ℝ[X] := linePoly c ℓ Q x₀ i * linePoly 1 0 (-A) x₀ i ^ e₁ *
    linePoly 1 0 (-B) x₀ i ^ e₂ with hP
  have hline : (fun s : ℝ => F' (x₀ + s • Pi.single i 1)) = fun s => P.eval s := by
    funext s
    simp only [hF', hP, Pi.mul_apply, Pi.pow_apply, eval_mul, eval_pow, eval_linePoly]
  have hiter : (pderiv i)^[k] F' x₀ = k.factorial * P.coeff k := by
    have h := iter_pderiv_line hF'c x₀ i k 0
    simp only [zero_smul, add_zero] at h
    rw [h, hline, iteratedDeriv_eval_poly_zero]
  obtain ⟨UA, hUA, hmA⟩ := linePoly_clip_factor hα i hα1 hα2
  obtain ⟨UB, hUB, hmB⟩ := linePoly_clip_factor hβ i hβ1 hβ2
  have hPf : P = C (clipF A x₀ ^ e₁ * clipF B x₀ ^ e₂) *
      (linePoly c ℓ Q x₀ i * UA ^ e₁ * UB ^ e₂) := by
    rw [hP, hUA, hUB, mul_pow, mul_pow, C_mul, C_pow, C_pow]
    ring
  have hmaj := ((coeffMaj_quad h0 h1 h2).mul (hmA.pow e₁)).mul (hmB.pow e₂) k
  have hα0 : 0 ≤ clipF A x₀ := clipF_nonneg A x₀
  have hβ0 : 0 ≤ clipF B x₀ := clipF_nonneg B x₀
  rw [hk, hiter, hPf, coeff_C_mul, abs_mul, abs_mul, Nat.abs_cast,
    abs_of_nonneg (by positivity : 0 ≤ clipF A x₀ ^ e₁ * clipF B x₀ ^ e₂)]
  have hfac : (0 : ℝ) ≤ k.factorial := Nat.cast_nonneg _
  calc (k.factorial : ℝ) * (clipF A x₀ ^ e₁ * clipF B x₀ ^ e₂ *
        |(linePoly c ℓ Q x₀ i * UA ^ e₁ * UB ^ e₂).coeff k|)
      ≤ k.factorial * (clipF A x₀ ^ e₁ * clipF B x₀ ^ e₂ *
        ((C m₀ + C m₁ * X + C m₂ * X ^ 2) * (1 + C (2 * rα) * X + C ωα * X ^ 2) ^ e₁ *
          (1 + C (2 * rβ) * X + C ωβ * X ^ 2) ^ e₂).coeff k) := by
        gcongr
        exact hmaj
    _ = _ := by ring

end BiluLinial.Tight.SecA.StarCalc
