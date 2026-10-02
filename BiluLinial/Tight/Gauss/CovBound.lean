/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.Gauss.PrekopaLeindler

/-!
# Even log-concave perturbations of a Gaussian have covariance at most the Gaussian's

Let `M` be a positive definite matrix, `gM x = exp (-(xᵀ M x) / 2)`, and let `f ≥ 0` be
measurable, even and midpoint log-concave (`f x * f y ≤ f (midpoint ℝ x y) ^ 2`). Then:

* (EVEN) `le_apply_zero_of_even_of_midpoint_logConcave`: `f x ≤ f 0`;
* (COV-a) `integral_mul_exp_dotProduct_mul_gauss_le`: the exponential moment bound
  `∫ f e^{θ·x} gM ≤ e^{θᵀM⁻¹θ/2} ∫ f gM`;
* (COV-b) `integral_mul_sq_dotProduct_mul_gauss_le`: the second moment bound
  `∫ f (θ·x)² gM ≤ (θᵀM⁻¹θ) ∫ f gM`;
* (COV-c) `integral_mul_dotProduct_mul_gauss_eq_zero`: `∫ f (θ·x) gM = 0`.

Proof of (COV-a): completing the square, `f(x) e^{θ·x} gM(x) = e^{θᵀM⁻¹θ/2} f(x) gM(x - M⁻¹θ)`,
and `I(t) = ∫ f(x) gM(x - t) dx` satisfies `I(t) ≤ I(0)`: Prékopa–Leindler applied to
`f · gM(· - t)`, `f · gM(· + t)` and `f · gM` gives `I(t) I(-t) ≤ I(0)²`, and `I(-t) = I(t)` by
evenness. (COV-b) follows from (COV-a) at `±sθ`, `cosh u ≥ 1 + u²/2`, and `s → 0`.
-/

@[expose] public section

namespace BiluLinial.Tight

open MeasureTheory Set Matrix Filter Topology
open scoped ENNReal

variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
/-- (EVEN) A nonnegative, even, midpoint log-concave function is maximal at the origin. -/
theorem le_apply_zero_of_even_of_midpoint_logConcave {f : (ι → ℝ) → ℝ} (hf0 : ∀ x, 0 ≤ f x)
    (hfe : ∀ x, f (-x) = f x) (hfl : ∀ x y, f x * f y ≤ f (midpoint ℝ x y) ^ 2)
    (x : ι → ℝ) : f x ≤ f 0 := by
  have h := hfl x (-x)
  rw [hfe, midpoint_self_neg, ← sq] at h
  exact (pow_le_pow_iff_left₀ (hf0 x) (hf0 0) two_ne_zero).1 h

/-! ### The quadratic form `x ↦ xᵀ M x` -/

lemma quad_neg (M : Matrix ι ι ℝ) (x : ι → ℝ) : (-x) ⬝ᵥ (M *ᵥ (-x)) = x ⬝ᵥ (M *ᵥ x) := by
  rw [mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg]

lemma quad_smul (M : Matrix ι ι ℝ) (r : ℝ) (x : ι → ℝ) :
    (r • x) ⬝ᵥ (M *ᵥ (r • x)) = r ^ 2 * (x ⬝ᵥ (M *ᵥ x)) := by
  simp only [mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]; ring

/-- Midpoint convexity of a positive semidefinite quadratic form. -/
lemma quad_midpoint_le {M : Matrix ι ι ℝ} (hM : M.PosSemidef) (u w : ι → ℝ) :
    midpoint ℝ u w ⬝ᵥ (M *ᵥ midpoint ℝ u w) ≤ (u ⬝ᵥ (M *ᵥ u) + w ⬝ᵥ (M *ᵥ w)) / 2 := by
  obtain ⟨m, hm⟩ : ∃ m, m = midpoint ℝ u w := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : ι → ℝ, d = (2⁻¹ : ℝ) • (u - w) := ⟨_, rfl⟩
  have hu : u = m + d := by
    subst hm hd; ext i
    simp only [midpoint_eq_smul_add, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
      invOf_eq_inv]
    ring
  have hw : w = m - d := by
    subst hm hd; ext i
    simp only [midpoint_eq_smul_add, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
      invOf_eq_inv]
    ring
  have hd0 : 0 ≤ d ⬝ᵥ (M *ᵥ d) := by simpa using hM.dotProduct_mulVec_nonneg d
  have key : (m + d) ⬝ᵥ (M *ᵥ (m + d)) + (m - d) ⬝ᵥ (M *ᵥ (m - d)) =
      2 * (m ⬝ᵥ (M *ᵥ m)) + 2 * (d ⬝ᵥ (M *ᵥ d)) := by
    simp only [mulVec_add, mulVec_sub, dotProduct_add, add_dotProduct, dotProduct_sub,
      sub_dotProduct]
    ring
  rw [← hm, hu, hw]
  linarith

/-- Completing the square. -/
lemma quad_sub_inv_mulVec [DecidableEq ι] {M : Matrix ι ι ℝ} (hM : M.PosDef) (θ x : ι → ℝ) :
    (x - M⁻¹ *ᵥ θ) ⬝ᵥ (M *ᵥ (x - M⁻¹ *ᵥ θ)) =
      x ⬝ᵥ (M *ᵥ x) - 2 * (θ ⬝ᵥ x) + θ ⬝ᵥ (M⁻¹ *ᵥ θ) := by
  have hMinv : M * M⁻¹ = 1 := M.mul_nonsing_inv ((M.isUnit_iff_isUnit_det).1 hM.isUnit)
  have hMm : M *ᵥ (M⁻¹ *ᵥ θ) = θ := by rw [mulVec_mulVec, hMinv, one_mulVec]
  have hMt : Mᵀ = M := by rw [← conjTranspose_eq_transpose_of_trivial]; exact hM.isHermitian
  have h1 : (M⁻¹ *ᵥ θ) ⬝ᵥ (M *ᵥ x) = θ ⬝ᵥ x := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hMt, hMm]
  have h2 : x ⬝ᵥ (M *ᵥ (M⁻¹ *ᵥ θ)) = θ ⬝ᵥ x := by rw [hMm, dotProduct_comm]
  have h3 : (M⁻¹ *ᵥ θ) ⬝ᵥ (M *ᵥ (M⁻¹ *ᵥ θ)) = θ ⬝ᵥ (M⁻¹ *ᵥ θ) := by
    rw [hMm, dotProduct_comm]
  simp only [mulVec_sub, sub_dotProduct, dotProduct_sub]
  rw [h1, h2, h3]
  ring

/-- A positive definite quadratic form dominates a positive multiple of `∑ xᵢ²`. -/
lemma exists_pos_mul_sum_sq_le_quad {M : Matrix ι ι ℝ} (hM : M.PosDef) :
    ∃ c > 0, ∀ x : ι → ℝ, c * ∑ i, x i ^ 2 ≤ x ⬝ᵥ (M *ᵥ x) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨1, one_pos, fun x => by simp [dotProduct]⟩
  have hq : Continuous fun x : ι → ℝ => x ⬝ᵥ (M *ᵥ x) := by fun_prop
  obtain ⟨u, hu, hmin⟩ := (isCompact_sphere (0 : ι → ℝ) 1).exists_isMinOn
    (NormedSpace.sphere_nonempty.2 zero_le_one) hq.continuousOn
  have hu1 : ‖u‖ = 1 := mem_sphere_zero_iff_norm.1 hu
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu1
  have hqu : 0 < u ⬝ᵥ (M *ᵥ u) := by simpa using hM.dotProduct_mulVec_pos hu0
  have hcard : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 Fintype.card_pos
  refine ⟨u ⬝ᵥ (M *ᵥ u) / Fintype.card ι, div_pos hqu hcard, fun x => ?_⟩
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hy : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : ι → ℝ) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hxn.ne']
  have h1 : u ⬝ᵥ (M *ᵥ u) ≤ (‖x‖⁻¹ • x) ⬝ᵥ (M *ᵥ (‖x‖⁻¹ • x)) := hmin hy
  rw [quad_smul] at h1
  have h3 : ∑ i, x i ^ 2 ≤ Fintype.card ι * ‖x‖ ^ 2 := by
    calc ∑ i, x i ^ 2 ≤ ∑ _i : ι, ‖x‖ ^ 2 := Finset.sum_le_sum fun i _ => by
          have := norm_le_pi_norm x i
          rw [Real.norm_eq_abs] at this
          calc x i ^ 2 = |x i| ^ 2 := (sq_abs _).symm
            _ ≤ ‖x‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
      _ = Fintype.card ι * ‖x‖ ^ 2 := by simp
  have hxn2 : ‖x‖ ^ 2 ≠ 0 := pow_ne_zero 2 hxn.ne'
  calc u ⬝ᵥ (M *ᵥ u) / Fintype.card ι * ∑ i, x i ^ 2
      ≤ u ⬝ᵥ (M *ᵥ u) / Fintype.card ι * (Fintype.card ι * ‖x‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h3 (div_pos hqu hcard).le
    _ = u ⬝ᵥ (M *ᵥ u) * ‖x‖ ^ 2 := by
        rw [div_mul_eq_mul_div, mul_comm (Fintype.card ι : ℝ), ← mul_assoc,
          mul_div_assoc, div_self hcard.ne', mul_one]
    _ ≤ ‖x‖⁻¹ ^ 2 * x ⬝ᵥ (M *ᵥ x) * ‖x‖ ^ 2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
    _ = x ⬝ᵥ (M *ᵥ x) := by
        rw [inv_pow, mul_comm, ← mul_assoc, mul_inv_cancel₀ hxn2, one_mul]

/-! ### The Gaussian weight -/

/-- The centred Gaussian weight `exp (-(xᵀ M x) / 2)` with precision matrix `M`. -/
noncomputable def gaussWeight (M : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ :=
  Real.exp (-(x ⬝ᵥ (M *ᵥ x)) / 2)

lemma gaussWeight_pos (M : Matrix ι ι ℝ) (x : ι → ℝ) : 0 < gaussWeight M x := Real.exp_pos _

lemma gaussWeight_neg (M : Matrix ι ι ℝ) (x : ι → ℝ) : gaussWeight M (-x) = gaussWeight M x := by
  rw [gaussWeight, gaussWeight, quad_neg]

lemma continuous_gaussWeight (M : Matrix ι ι ℝ) : Continuous (gaussWeight M) := by
  unfold gaussWeight; fun_prop

/-- The Gaussian weight of a positive semidefinite form is midpoint log-concave. -/
lemma gaussWeight_mul_le {M : Matrix ι ι ℝ} (hM : M.PosSemidef) (u w : ι → ℝ) :
    gaussWeight M u * gaussWeight M w ≤ gaussWeight M (midpoint ℝ u w) ^ 2 := by
  have h := quad_midpoint_le hM u w
  simp only [gaussWeight]
  rw [← Real.exp_add, ← Real.exp_nat_mul]
  apply Real.exp_le_exp.2
  push_cast
  linarith

/-- Completing the square: `e^{θ·x} gM(x) = e^{θᵀM⁻¹θ/2} gM(x - M⁻¹θ)`. -/
lemma exp_mul_gaussWeight_eq [DecidableEq ι] {M : Matrix ι ι ℝ} (hM : M.PosDef)
    (θ x : ι → ℝ) :
    Real.exp (θ ⬝ᵥ x) * gaussWeight M x =
      Real.exp (θ ⬝ᵥ (M⁻¹ *ᵥ θ) / 2) * gaussWeight M (x - M⁻¹ *ᵥ θ) := by
  simp only [gaussWeight]
  rw [← Real.exp_add, ← Real.exp_add, quad_sub_inv_mulVec hM]
  congr 1; ring

/-- The Gaussian weight of a positive definite form is integrable. -/
lemma integrable_gaussWeight {M : Matrix ι ι ℝ} (hM : M.PosDef) :
    Integrable (gaussWeight M) := by
  obtain ⟨c, hc, hle⟩ := exists_pos_mul_sum_sq_le_quad hM
  have hprod : Integrable (fun x : ι → ℝ => ∏ i, Real.exp (-(c / 2) * x i ^ 2)) := by
    rw [volume_pi]
    exact Integrable.fintype_prod (f := fun (_ : ι) (t : ℝ) => Real.exp (-(c / 2) * t ^ 2))
      (fun _ => integrable_exp_neg_mul_sq (by positivity))
  refine hprod.mono' (continuous_gaussWeight M).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (gaussWeight_pos M x), ← Real.exp_sum, gaussWeight]
  apply Real.exp_le_exp.2
  rw [← Finset.mul_sum]
  linarith [hle x]

lemma integrable_mul_gaussWeight_sub {M : Matrix ι ι ℝ} (hM : M.PosDef) {f : (ι → ℝ) → ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) {B : ℝ} (hfB : ∀ x, f x ≤ B) (t : ι → ℝ) :
    Integrable fun x => f x * gaussWeight M (x - t) := by
  refine (((integrable_gaussWeight hM).comp_sub_right t).const_mul B).mono'
    (hf.mul ((continuous_gaussWeight M).measurable.comp
      (measurable_sub_const t))).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hf0 x) (gaussWeight_pos M _).le)]
  exact mul_le_mul_of_nonneg_right (hfB x) (gaussWeight_pos M _).le

lemma integrable_mul_gaussWeight {M : Matrix ι ι ℝ} (hM : M.PosDef) {f : (ι → ℝ) → ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) {B : ℝ} (hfB : ∀ x, f x ≤ B) :
    Integrable fun x => f x * gaussWeight M x := by
  simpa using integrable_mul_gaussWeight_sub hM hf hf0 hfB 0

lemma integrable_mul_exp_mul_gaussWeight {M : Matrix ι ι ℝ} (hM : M.PosDef)
    {f : (ι → ℝ) → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) {B : ℝ} (hfB : ∀ x, f x ≤ B)
    (φ : ι → ℝ) : Integrable fun x => f x * Real.exp (φ ⬝ᵥ x) * gaussWeight M x := by
  classical
  refine ((integrable_mul_gaussWeight_sub hM hf hf0 hfB (M⁻¹ *ᵥ φ)).const_mul
    (Real.exp (φ ⬝ᵥ (M⁻¹ *ᵥ φ) / 2))).congr (Eventually.of_forall fun x => ?_)
  change Real.exp (φ ⬝ᵥ (M⁻¹ *ᵥ φ) / 2) * (f x * gaussWeight M (x - M⁻¹ *ᵥ φ)) =
    f x * Real.exp (φ ⬝ᵥ x) * gaussWeight M x
  rw [mul_assoc (f x), exp_mul_gaussWeight_eq hM]
  ring

/-! ### Shifting the Gaussian does not increase the integral -/

/-- `I(t) ≤ I(0)` for `I(t) = ∫ f(x) gM(x - t) dx` (Prékopa–Leindler and evenness). -/
lemma lintegral_mul_gaussWeight_sub_le {M : Matrix ι ι ℝ} (hM : M.PosSemidef)
    {f : (ι → ℝ) → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hfe : ∀ x, f (-x) = f x)
    (hfl : ∀ x y, f x * f y ≤ f (midpoint ℝ x y) ^ 2) (t : ι → ℝ) :
    ∫⁻ x, ENNReal.ofReal (f x * gaussWeight M (x - t)) ≤
      ∫⁻ x, ENNReal.ofReal (f x * gaussWeight M x) := by
  have hG := (continuous_gaussWeight M).measurable
  have hG0 : ∀ z, 0 ≤ gaussWeight M z := fun z => (gaussWeight_pos M z).le
  have key := prekopaLeindler (f := fun x => ENNReal.ofReal (f x * gaussWeight M (x - t)))
    (g := fun x => ENNReal.ofReal (f x * gaussWeight M (x + t)))
    (h := fun x => ENNReal.ofReal (f x * gaussWeight M x))
    (hf.mul (hG.comp (measurable_sub_const t))).ennreal_ofReal
    (hf.mul (hG.comp (measurable_add_const t))).ennreal_ofReal
    (hf.mul hG).ennreal_ofReal ?_
  · beta_reduce at key
    have hsym : ∫⁻ x, ENNReal.ofReal (f x * gaussWeight M (x + t)) =
        ∫⁻ x, ENNReal.ofReal (f x * gaussWeight M (x - t)) := by
      refine (lintegral_neg_eq_self _).symm.trans (lintegral_congr fun x => ?_)
      change ENNReal.ofReal (f (-x) * gaussWeight M (-x + t)) =
        ENNReal.ofReal (f x * gaussWeight M (x - t))
      rw [hfe, show -x + t = -(x - t) by abel, gaussWeight_neg]
    rw [hsym, ← sq] at key
    exact (ENNReal.pow_le_pow_left_iff two_ne_zero).1 key
  · intro x y
    have hxy : midpoint ℝ (x - t) (y + t) = midpoint ℝ x y := by
      rw [midpoint_eq_smul_add, midpoint_eq_smul_add, sub_add_add_cancel]
    have h1 := hfl x y
    have h2 := gaussWeight_mul_le hM (x - t) (y + t)
    rw [hxy] at h2
    change ENNReal.ofReal (f x * gaussWeight M (x - t)) *
        ENNReal.ofReal (f y * gaussWeight M (y + t)) ≤
      ENNReal.ofReal (f (midpoint ℝ x y) * gaussWeight M (midpoint ℝ x y)) ^ 2
    rw [← ENNReal.ofReal_mul (mul_nonneg (hf0 x) (hG0 _)),
      ← ENNReal.ofReal_pow (mul_nonneg (hf0 _) (hG0 _))]
    apply ENNReal.ofReal_le_ofReal
    calc f x * gaussWeight M (x - t) * (f y * gaussWeight M (y + t))
        = (f x * f y) * (gaussWeight M (x - t) * gaussWeight M (y + t)) := by ring
      _ ≤ f (midpoint ℝ x y) ^ 2 * gaussWeight M (midpoint ℝ x y) ^ 2 :=
          mul_le_mul h1 h2 (mul_nonneg (hG0 _) (hG0 _)) (sq_nonneg _)
      _ = (f (midpoint ℝ x y) * gaussWeight M (midpoint ℝ x y)) ^ 2 := by ring

/-! ### Moment bounds -/

/-- (COV-a) in terms of `gaussWeight`. -/
theorem integral_mul_exp_mul_gaussWeight_le [DecidableEq ι] {M : Matrix ι ι ℝ}
    (hM : M.PosDef) {f : (ι → ℝ) → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hfe : ∀ x, f (-x) = f x) (hfl : ∀ x y, f x * f y ≤ f (midpoint ℝ x y) ^ 2)
    (θ : ι → ℝ) :
    ∫ x, f x * Real.exp (θ ⬝ᵥ x) * gaussWeight M x ≤
      Real.exp (θ ⬝ᵥ (M⁻¹ *ᵥ θ) / 2) * ∫ x, f x * gaussWeight M x := by
  have hfB := le_apply_zero_of_even_of_midpoint_logConcave hf0 hfe hfl
  have hG := (continuous_gaussWeight M).measurable
  have hG0 : ∀ x, 0 ≤ gaussWeight M x := fun x => (gaussWeight_pos M x).le
  have e1 : (fun x => f x * Real.exp (θ ⬝ᵥ x) * gaussWeight M x) =
      fun x => Real.exp (θ ⬝ᵥ (M⁻¹ *ᵥ θ) / 2) * (f x * gaussWeight M (x - M⁻¹ *ᵥ θ)) := by
    funext x
    rw [mul_assoc, exp_mul_gaussWeight_eq hM]
    ring
  rw [e1, integral_const_mul]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  have hA : ∫ x, f x * gaussWeight M (x - M⁻¹ *ᵥ θ) =
      (∫⁻ x, ENNReal.ofReal (f x * gaussWeight M (x - M⁻¹ *ᵥ θ))).toReal :=
    integral_eq_lintegral_of_nonneg_ae
      (Eventually.of_forall fun x => mul_nonneg (hf0 x) (hG0 _))
      (hf.mul (hG.comp (measurable_sub_const _))).aestronglyMeasurable
  have hB : ∫ x, f x * gaussWeight M x =
      (∫⁻ x, ENNReal.ofReal (f x * gaussWeight M x)).toReal :=
    integral_eq_lintegral_of_nonneg_ae
      (Eventually.of_forall fun x => mul_nonneg (hf0 x) (hG0 _))
      (hf.mul hG).aestronglyMeasurable
  rw [hA, hB]
  exact ENNReal.toReal_mono (integrable_mul_gaussWeight hM hf hf0 hfB).lintegral_lt_top.ne
    (lintegral_mul_gaussWeight_sub_le hM.posSemidef hf hf0 hfe hfl _)

/-- `2 + v² ≤ eᵛ + e⁻ᵛ`. -/
lemma two_add_sq_le_exp_add_exp_neg (v : ℝ) : 2 + v ^ 2 ≤ Real.exp v + Real.exp (-v) := by
  have h1 : Real.exp v + Real.exp (-v) = 2 * Real.cosh v := by rw [Real.cosh_eq]; ring
  have h2 : Real.cosh v = 1 + 2 * Real.sinh (v / 2) ^ 2 := by
    have := Real.cosh_two_mul (v / 2)
    rw [show 2 * (v / 2) = v by ring] at this
    rw [this, Real.cosh_sq]; ring
  have h3 : (v / 2) ^ 2 ≤ Real.sinh (v / 2) ^ 2 := by
    rcases le_total 0 (v / 2) with h | h
    · exact pow_le_pow_left₀ h (Real.self_le_sinh_iff.2 h) 2
    · have h' := Real.self_le_sinh_iff.2 (neg_nonneg.2 h)
      rw [Real.sinh_neg] at h'
      have := pow_le_pow_left₀ (neg_nonneg.2 h) h' 2
      rwa [neg_sq, neg_sq] at this
  rw [h1, h2]
  nlinarith [h3]

/-- `eʸ - 1 ≤ y eʸ`. -/
lemma exp_sub_one_le_mul_exp (y : ℝ) : Real.exp y - 1 ≤ y * Real.exp y := by
  have h1 := Real.add_one_le_exp (-y)
  have h2 : Real.exp (-y) * Real.exp y = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have h3 := mul_le_mul_of_nonneg_right h1 (Real.exp_pos y).le
  rw [h2] at h3
  nlinarith [h3]

/-- If `K ≤ c e^{s²c/2} J` for every `s > 0`, then `K ≤ c J`. -/
lemma le_mul_of_forall_pos_le_mul_exp {K c J : ℝ}
    (h : ∀ s : ℝ, 0 < s → K ≤ c * Real.exp (s ^ 2 * c / 2) * J) : K ≤ c * J := by
  have hcont : Continuous fun s : ℝ => c * Real.exp (s ^ 2 * c / 2) * J := by fun_prop
  have h0 := hcont.tendsto 0
  have hval : c * Real.exp ((0 : ℝ) ^ 2 * c / 2) * J = c * J := by simp
  rw [hval] at h0
  exact ge_of_tendsto (h0.mono_left nhdsWithin_le_nhds)
    (eventually_nhdsWithin_of_forall (s := Ioi 0) fun s hs => h s hs)

/-- (COV-b) in terms of `gaussWeight`. -/
theorem integral_mul_sq_mul_gaussWeight_le [DecidableEq ι] {M : Matrix ι ι ℝ}
    (hM : M.PosDef) {f : (ι → ℝ) → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hfe : ∀ x, f (-x) = f x) (hfl : ∀ x y, f x * f y ≤ f (midpoint ℝ x y) ^ 2)
    (θ : ι → ℝ) :
    ∫ x, f x * (θ ⬝ᵥ x) ^ 2 * gaussWeight M x ≤
      (θ ⬝ᵥ (M⁻¹ *ᵥ θ)) * ∫ x, f x * gaussWeight M x := by
  have hfB := le_apply_zero_of_even_of_midpoint_logConcave hf0 hfe hfl
  have hG := (continuous_gaussWeight M).measurable
  have hG0 : ∀ x, 0 ≤ gaussWeight M x := fun x => (gaussWeight_pos M x).le
  have hJint := integrable_mul_gaussWeight hM hf hf0 hfB
  have hexpint := integrable_mul_exp_mul_gaussWeight hM hf hf0 hfB
  have hKint : Integrable fun x => f x * (θ ⬝ᵥ x) ^ 2 * gaussWeight M x := by
    refine ((hexpint θ).add (hexpint (-θ))).mono'
      ((hf.mul (by fun_prop : Measurable fun x : ι → ℝ => (θ ⬝ᵥ x) ^ 2)).mul
        hG).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    have hfG : 0 ≤ f x * gaussWeight M x := mul_nonneg (hf0 x) (hG0 x)
    have h1 := mul_le_mul_of_nonneg_left (two_add_sq_le_exp_add_exp_neg (θ ⬝ᵥ x)) hfG
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (hf0 x) (sq_nonneg _)) (hG0 x))]
    change f x * (θ ⬝ᵥ x) ^ 2 * gaussWeight M x ≤
      f x * Real.exp (θ ⬝ᵥ x) * gaussWeight M x + f x * Real.exp ((-θ) ⬝ᵥ x) * gaussWeight M x
    rw [neg_dotProduct]
    nlinarith [h1, hfG]
  have hJ0 : 0 ≤ ∫ x, f x * gaussWeight M x :=
    integral_nonneg fun x => mul_nonneg (hf0 x) (hG0 x)
  refine le_mul_of_forall_pos_le_mul_exp fun s hs => ?_
  have ha := integral_mul_exp_mul_gaussWeight_le hM hf hf0 hfe hfl (s • θ)
  have hb := integral_mul_exp_mul_gaussWeight_le hM hf hf0 hfe hfl (-(s • θ))
  have hca : (s • θ) ⬝ᵥ (M⁻¹ *ᵥ (s • θ)) = s ^ 2 * (θ ⬝ᵥ (M⁻¹ *ᵥ θ)) := by
    simp only [mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]; ring
  have hcb : (-(s • θ)) ⬝ᵥ (M⁻¹ *ᵥ (-(s • θ))) = s ^ 2 * (θ ⬝ᵥ (M⁻¹ *ᵥ θ)) := by
    simp only [mulVec_neg, dotProduct_neg, neg_dotProduct, mulVec_smul, dotProduct_smul,
      smul_dotProduct, smul_eq_mul]; ring
  rw [hca] at ha
  rw [hcb] at hb
  have hlow : 2 * (∫ x, f x * gaussWeight M x) +
      s ^ 2 * (∫ x, f x * (θ ⬝ᵥ x) ^ 2 * gaussWeight M x) ≤
      (∫ x, f x * Real.exp ((s • θ) ⬝ᵥ x) * gaussWeight M x) +
        ∫ x, f x * Real.exp ((-(s • θ)) ⬝ᵥ x) * gaussWeight M x := by
    rw [← integral_add (hexpint _) (hexpint _), ← integral_const_mul, ← integral_const_mul,
      ← integral_add (hJint.const_mul 2) (hKint.const_mul _)]
    refine integral_mono ((hJint.const_mul 2).add (hKint.const_mul _))
      ((hexpint _).add (hexpint _)) fun x => ?_
    change 2 * (f x * gaussWeight M x) + s ^ 2 * (f x * (θ ⬝ᵥ x) ^ 2 * gaussWeight M x) ≤
      f x * Real.exp ((s • θ) ⬝ᵥ x) * gaussWeight M x +
        f x * Real.exp ((-(s • θ)) ⬝ᵥ x) * gaussWeight M x
    rw [neg_dotProduct, smul_dotProduct, smul_eq_mul]
    have hfG : 0 ≤ f x * gaussWeight M x := mul_nonneg (hf0 x) (hG0 x)
    have h1 := mul_le_mul_of_nonneg_left (two_add_sq_le_exp_add_exp_neg (s * (θ ⬝ᵥ x))) hfG
    nlinarith [h1]
  have hE := mul_le_mul_of_nonneg_right
    (exp_sub_one_le_mul_exp (s ^ 2 * (θ ⬝ᵥ (M⁻¹ *ᵥ θ)) / 2)) hJ0
  have hs2 : 0 < s ^ 2 := by positivity
  have key : s ^ 2 * (∫ x, f x * (θ ⬝ᵥ x) ^ 2 * gaussWeight M x) ≤
      s ^ 2 * ((θ ⬝ᵥ (M⁻¹ *ᵥ θ)) * Real.exp (s ^ 2 * (θ ⬝ᵥ (M⁻¹ *ᵥ θ)) / 2) *
        ∫ x, f x * gaussWeight M x) := by
    linarith
  exact le_of_mul_le_mul_left key hs2

/-! ### Main statements (explicit Gaussian weight) -/

/-- (COV-a) **Exponential moment bound.** Let `M` be positive definite and `f ≥ 0` measurable,
even and midpoint log-concave. Then for every `θ`,
`∫ f(x) e^{θ·x} e^{-xᵀMx/2} dx ≤ e^{θᵀM⁻¹θ/2} ∫ f(x) e^{-xᵀMx/2} dx`. -/
theorem integral_mul_exp_dotProduct_mul_gauss_le [DecidableEq ι] {M : Matrix ι ι ℝ}
    (hM : M.PosDef) {f : (ι → ℝ) → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hfe : ∀ x, f (-x) = f x) (hfl : ∀ x y, f x * f y ≤ f (midpoint ℝ x y) ^ 2)
    (θ : ι → ℝ) :
    ∫ x, f x * Real.exp (θ ⬝ᵥ x) * Real.exp (-(x ⬝ᵥ (M *ᵥ x)) / 2) ≤
      Real.exp ((θ ⬝ᵥ (M⁻¹ *ᵥ θ)) / 2) * ∫ x, f x * Real.exp (-(x ⬝ᵥ (M *ᵥ x)) / 2) :=
  integral_mul_exp_mul_gaussWeight_le hM hf hf0 hfe hfl θ

/-- (COV-b) **Second moment bound.** Let `M` be positive definite and `f ≥ 0` measurable,
even and midpoint log-concave. Then for every `θ`,
`∫ f(x) (θ·x)² e^{-xᵀMx/2} dx ≤ (θᵀM⁻¹θ) ∫ f(x) e^{-xᵀMx/2} dx`, i.e. the covariance of the
probability measure with density proportional to `f e^{-xᵀMx/2}` is at most `M⁻¹`. -/
theorem integral_mul_sq_dotProduct_mul_gauss_le [DecidableEq ι] {M : Matrix ι ι ℝ}
    (hM : M.PosDef) {f : (ι → ℝ) → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hfe : ∀ x, f (-x) = f x) (hfl : ∀ x y, f x * f y ≤ f (midpoint ℝ x y) ^ 2)
    (θ : ι → ℝ) :
    ∫ x, f x * (θ ⬝ᵥ x) ^ 2 * Real.exp (-(x ⬝ᵥ (M *ᵥ x)) / 2) ≤
      (θ ⬝ᵥ (M⁻¹ *ᵥ θ)) * ∫ x, f x * Real.exp (-(x ⬝ᵥ (M *ᵥ x)) / 2) :=
  integral_mul_sq_mul_gaussWeight_le hM hf hf0 hfe hfl θ

/-- (COV-b), normalized: the variance of `θ·x` under the probability measure with density
proportional to `f e^{-xᵀMx/2}` is at most `θᵀM⁻¹θ` (the ratio is `0` if `f e^{-xᵀMx/2}`
integrates to `0`). -/
theorem integral_mul_sq_dotProduct_mul_gauss_div_le [DecidableEq ι] {M : Matrix ι ι ℝ}
    (hM : M.PosDef) {f : (ι → ℝ) → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hfe : ∀ x, f (-x) = f x) (hfl : ∀ x y, f x * f y ≤ f (midpoint ℝ x y) ^ 2)
    (θ : ι → ℝ) :
    (∫ x, f x * (θ ⬝ᵥ x) ^ 2 * Real.exp (-(x ⬝ᵥ (M *ᵥ x)) / 2)) /
        (∫ x, f x * Real.exp (-(x ⬝ᵥ (M *ᵥ x)) / 2)) ≤ θ ⬝ᵥ (M⁻¹ *ᵥ θ) := by
  have hc : 0 ≤ θ ⬝ᵥ (M⁻¹ *ᵥ θ) := by
    simpa using hM.inv.posSemidef.dotProduct_mulVec_nonneg θ
  rcases (integral_nonneg fun x => mul_nonneg (hf0 x) (Real.exp_pos _).le :
      0 ≤ ∫ x, f x * Real.exp (-(x ⬝ᵥ (M *ᵥ x)) / 2)).eq_or_lt with h | h
  · rw [← h, div_zero]; exact hc
  · exact (div_le_iff₀ h).2 (integral_mul_sq_dotProduct_mul_gauss_le hM hf hf0 hfe hfl θ)

/-- (COV-c) **Zero mean.** For even `f`, `∫ f(x) (θ·x) e^{-xᵀMx/2} dx = 0`. -/
theorem integral_mul_dotProduct_mul_gauss_eq_zero (M : Matrix ι ι ℝ) {f : (ι → ℝ) → ℝ}
    (hfe : ∀ x, f (-x) = f x) (θ : ι → ℝ) :
    ∫ x, f x * (θ ⬝ᵥ x) * Real.exp (-(x ⬝ᵥ (M *ᵥ x)) / 2) = 0 := by
  have h := integral_neg_eq_self
    (fun x => f x * (θ ⬝ᵥ x) * Real.exp (-(x ⬝ᵥ (M *ᵥ x)) / 2)) volume
  have h2 : ∀ x : ι → ℝ, f (-x) * (θ ⬝ᵥ (-x)) * Real.exp (-((-x) ⬝ᵥ (M *ᵥ (-x))) / 2) =
      -(f x * (θ ⬝ᵥ x) * Real.exp (-(x ⬝ᵥ (M *ᵥ x)) / 2)) := by
    intro x
    rw [hfe, quad_neg, dotProduct_neg]
    ring
  simp only [h2, integral_neg] at h
  linarith

/-- Integrability of `f e^{-xᵀMx/2}` for bounded measurable `f ≥ 0` and positive definite `M`. -/
theorem integrable_mul_gauss {M : Matrix ι ι ℝ} (hM : M.PosDef) {f : (ι → ℝ) → ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) {B : ℝ} (hfB : ∀ x, f x ≤ B) :
    Integrable fun x => f x * Real.exp (-(x ⬝ᵥ (M *ᵥ x)) / 2) :=
  integrable_mul_gaussWeight hM hf hf0 hfB

end BiluLinial.Tight
