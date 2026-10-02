/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.Tools.Alpha2
public import BiluLinial.Tight.Gauss.BLmid
public import BiluLinial.Tight.Gauss.IBP

/-!
# BLmid under the standard Gaussian measure

Node T.BLG of `docs/tight/BP_TOOLS.md`: BLmid (`integral_quad_le_of_midpoint`, AUDIT-C §5.3)
transported to `gaussPi ι` for the clipped weights `φ = α₊^m β₊^{m'}` (`clipProd m m' A B`).

* `gaussPi_eq_withDensity`, `integral_gaussPi_eq`: `gaussPi ι` has Lebesgue density
  `∏ᵢ φ₁(xᵢ) = (2π)^{-n/2} e^{-|x|²/2}`, so `𝖦 f = (2π)^{-n/2} ∫ f(x) e^{-|x|²/2} dx` for every
  `f` (no integrability needed: both sides are Bochner integrals of the same function against
  the same measure).
* `gaussE_qForm_mul_clipProd_le` (variable modulus): for `T ⪰ 0`, `0 ⪯ M ⪯ A`, `0 ⪯ N ⪯ B`:
  `𝖦[q_T φ] ≤ 𝖦[tr(T (I + H)⁻¹) φ]`, `H = clipHess m m' A B M N`. Proof: BLmid with
  `ρ = φ e^{-|x|²/2}` and `K = I + H` (`κ = 1`); the midpoint hypothesis is
  `gaussWt_clipProd_midpoint` (T.ALPHA2).
* `gaussE_qForm_mul_clipProd_le_const` (constant modulus `K = I + cA`, `0 ≤ c ≤ 2m`):
  `𝖦[q_T φ] ≤ tr(T (I + cA)⁻¹) 𝖦 φ`. With `c = 0`: `𝖦[q_T φ] ≤ tr T · 𝖦 φ`.
-/

@[expose] public section

namespace BiluLinial.Tight

open MeasureTheory ProbabilityTheory Matrix Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The Gaussian density -/

omit [DecidableEq ι] in
theorem prod_gaussianPDFReal (x : ι → ℝ) :
    ∏ i, gaussianPDFReal 0 1 (x i) =
      (√(2 * π))⁻¹ ^ Fintype.card ι * Real.exp (-(x ⬝ᵥ x) / 2) := by
  simp only [gaussianPDFReal_zero_one, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, ← Real.exp_sum]
  congr 2
  simp only [dotProduct, neg_div, Finset.sum_neg_distrib, Finset.sum_div, sq]

omit [DecidableEq ι] in
theorem measurable_prod_gaussianPDFReal :
    Measurable fun x : ι → ℝ => ∏ i, gaussianPDFReal 0 1 (x i) :=
  Finset.measurable_prod _ fun i _ => (measurable_gaussianPDFReal 0 1).comp (measurable_pi_apply i)

omit [DecidableEq ι] in
/-- The standard Gaussian measure on `ι → ℝ` has density `∏ᵢ φ₁(xᵢ)`. -/
theorem gaussPi_eq_withDensity :
    gaussPi ι = volume.withDensity fun x => ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (x i)) := by
  unfold gaussPi
  refine Measure.pi_eq fun s hs => ?_
  have hmeas : MeasurableSet (Set.univ.pi s) := MeasurableSet.univ_pi hs
  rw [withDensity_apply _ hmeas, ← lintegral_indicator hmeas]
  have hind : ∀ x, (Set.univ.pi s).indicator
      (fun x => ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (x i))) x =
      ENNReal.ofReal (∏ i, (s i).indicator (gaussianPDFReal 0 1) (x i)) := by
    intro x
    by_cases hx : x ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hx]
      congr 1
      exact Finset.prod_congr rfl fun i _ => (Set.indicator_of_mem (hx i (Set.mem_univ i)) _).symm
    · rw [Set.indicator_of_notMem hx]
      obtain ⟨i, hi⟩ : ∃ i, x i ∉ s i := by simpa [Set.mem_univ_pi] using hx
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _),
        ENNReal.ofReal_zero]
  simp_rw [hind]
  have hnn : ∀ i y, 0 ≤ (s i).indicator (gaussianPDFReal 0 1) y := fun i y =>
    Set.indicator_nonneg (fun z _ => gaussianPDFReal_nonneg 0 1 z) y
  have hint : Integrable (fun x : ι → ℝ => ∏ i, (s i).indicator (gaussianPDFReal 0 1) (x i)) := by
    rw [volume_pi]
    exact Integrable.fintype_prod (f := fun i => (s i).indicator (gaussianPDFReal 0 1))
      fun i => (integrable_gaussianPDFReal 0 1).indicator (hs i)
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (ae_of_all _ fun x => Finset.prod_nonneg fun i _ => hnn i (x i)), volume_pi,
    integral_fintype_prod_eq_prod (f := fun i => (s i).indicator (gaussianPDFReal 0 1)),
    ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (hnn i))]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [gaussianReal_apply_eq_integral 0 one_ne_zero, integral_indicator (hs i)]

omit [DecidableEq ι] in
/-- `𝖦 f = (2π)^{-n/2} ∫ f(x) e^{-|x|²/2} dx` for every `f`. -/
theorem integral_gaussPi_eq (f : (ι → ℝ) → ℝ) :
    ∫ x, f x ∂gaussPi ι =
      (√(2 * π))⁻¹ ^ Fintype.card ι * ∫ x, f x * Real.exp (-(x ⬝ᵥ x) / 2) := by
  rw [gaussPi_eq_withDensity, integral_withDensity_eq_integral_toReal_smul
    measurable_prod_gaussianPDFReal.ennreal_ofReal (ae_of_all _ fun _ => ENNReal.ofReal_lt_top),
    ← integral_const_mul]
  congr 1
  funext x
  rw [ENNReal.toReal_ofReal (Finset.prod_nonneg fun i _ => gaussianPDFReal_nonneg 0 1 _),
    prod_gaussianPDFReal, smul_eq_mul]
  ring

omit [DecidableEq ι] in
theorem gaussE_eq (f : (ι → ℝ) → ℝ) :
    gaussE f = (√(2 * π))⁻¹ ^ Fintype.card ι * ∫ x, f x * Real.exp (-(x ⬝ᵥ x) / 2) :=
  integral_gaussPi_eq f

/-! ### Measurability of the modulus -/

theorem measurable_one_add_clipHess (m m' : ℕ) (A B M N : Matrix ι ι ℝ) :
    Measurable fun x => 1 + clipHess m m' A B M N x := by
  refine Measurable.of_eval_matrix _ fun i j => ?_
  simp only [clipHess, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  exact measurable_const.add
    (((measurable_const.div (continuous_clipF A).measurable).mul_const _).add
      ((measurable_const.div (continuous_clipF B).measurable).mul_const _))

omit [DecidableEq ι] in
theorem measurable_gaussWt_clipProd (m m' : ℕ) (A B : Matrix ι ι ℝ) :
    Measurable (gaussWt (clipProd m m' A B)) := by
  unfold gaussWt
  exact ((continuous_clipProd m m' A B).mul (by fun_prop)).measurable

/-! ### BLmid on the Gaussian -/

/-- **T.BLG** (variable modulus). For `T ⪰ 0`, `0 ⪯ M ⪯ A`, `0 ⪯ N ⪯ B`:
`𝖦[q_T φ] ≤ 𝖦[tr(T (I + H)⁻¹) φ]` with `φ = α₊^m β₊^{m'}`, `H = 2mM/α + 2m'N/β`. -/
theorem gaussE_qForm_mul_clipProd_le {A B M N T : Matrix ι ι ℝ} (hA : A.PosSemidef)
    (hB : B.PosSemidef) (hM : M.PosSemidef) (hN : N.PosSemidef) (hMA : (A - M).PosSemidef)
    (hNB : (B - N).PosSemidef) (hT : T.PosSemidef) (m m' : ℕ) :
    gaussE (fun x => qForm T x * clipProd m m' A B x) ≤
      gaussE (fun x => (T * (1 + clipHess m m' A B M N x)⁻¹).trace * clipProd m m' A B x) := by
  have hKs : ∀ z, (1 + clipHess m m' A B M N z).IsHermitian := fun z =>
    isHermitian_one.add (clipHess_posSemidef hM hN m m' A B z).isHermitian
  have hKκ : ∀ z w : ι → ℝ, 1 * (w ⬝ᵥ w) ≤ w ⬝ᵥ ((1 + clipHess m m' A B M N z) *ᵥ w) := by
    intro z w
    have h := (clipHess_posSemidef hM hN m m' A B z).dotProduct_mulVec_nonneg w
    simp only [star_trivial] at h
    rw [add_mulVec, one_mulVec, dotProduct_add, one_mul]
    linarith
  have h := integral_quad_le_of_midpoint (measurable_gaussWt_clipProd m m' A B)
    (gaussWt_nonneg (clipProd_nonneg m m' A B)) (gaussWt_neg (clipProd_neg m m' A B))
    (measurable_one_add_clipHess m m' A B M N) one_pos hKs hKκ
    (gaussWt_clipProd_midpoint hA hB hMA hNB m m') hT
  rw [gaussE_eq, gaussE_eq]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have e1 : (fun x => qForm T x * clipProd m m' A B x * Real.exp (-(x ⬝ᵥ x) / 2)) =
      fun x => (x ⬝ᵥ (T *ᵥ x)) * gaussWt (clipProd m m' A B) x := by
    funext x; simp only [qForm, gaussWt]; ring
  have e2 : (fun x => (T * (1 + clipHess m m' A B M N x)⁻¹).trace * clipProd m m' A B x *
      Real.exp (-(x ⬝ᵥ x) / 2)) = fun x => (T * (1 + clipHess m m' A B M N x)⁻¹).trace *
        gaussWt (clipProd m m' A B) x := by
    funext x; simp only [gaussWt]; ring
  rw [e1, e2]
  exact h

/-- **T.BLG** (constant modulus `K = I + cA`, `0 ≤ c ≤ 2m`):
`𝖦[q_T φ] ≤ tr(T (I + cA)⁻¹) 𝖦 φ`. -/
theorem gaussE_qForm_mul_clipProd_le_const {A B T : Matrix ι ι ℝ} (hA : A.PosSemidef)
    (hB : B.PosSemidef) (hT : T.PosSemidef) (m m' : ℕ) {c : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ 2 * m) :
    gaussE (fun x => qForm T x * clipProd m m' A B x) ≤
      (T * (1 + c • A)⁻¹).trace * gaussE (clipProd m m' A B) := by
  have hKs : ∀ _z : ι → ℝ, (1 + c • A).IsHermitian := fun _ =>
    isHermitian_one.add (hA.smul hc0).isHermitian
  have hKκ : ∀ (_z : ι → ℝ) (w : ι → ℝ), 1 * (w ⬝ᵥ w) ≤ w ⬝ᵥ ((1 + c • A) *ᵥ w) := by
    intro _ w
    have h := (hA.smul hc0).dotProduct_mulVec_nonneg w
    simp only [star_trivial] at h
    rw [add_mulVec, one_mulVec, dotProduct_add, one_mul]
    linarith
  have h := integral_quad_le_of_midpoint (K := fun _ => 1 + c • A)
    (measurable_gaussWt_clipProd m m' A B)
    (gaussWt_nonneg (clipProd_nonneg m m' A B)) (gaussWt_neg (clipProd_neg m m' A B))
    measurable_const one_pos hKs hKκ (gaussWt_clipProd_midpoint_const hA hB m m' hc) hT
  rw [integral_const_mul] at h
  rw [gaussE_eq, gaussE_eq, mul_left_comm]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have e1 : (fun x => qForm T x * clipProd m m' A B x * Real.exp (-(x ⬝ᵥ x) / 2)) =
      fun x => (x ⬝ᵥ (T *ᵥ x)) * gaussWt (clipProd m m' A B) x := by
    funext x; simp only [qForm, gaussWt]; ring
  rw [e1]
  exact h

end BiluLinial.Tight
