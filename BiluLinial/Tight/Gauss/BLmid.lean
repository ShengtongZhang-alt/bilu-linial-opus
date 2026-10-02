/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.Gauss.CovBound

/-!
# Brascamp–Lieb for linear functions with a variable modulus (BLmid)

Blueprint node `D-BLmid` (AUDIT-C §5.3). It replaces the source's PDE proof of the Brascamp–Lieb
inequality in Lemma "Multiplicative shifted trace comparison" (B1), and covers every "covariance
at most `M⁻¹`" claim of the source.

Let `ρ ≥ 0` be measurable and even, and `K(z) ⪰ κ I` (`κ > 0`) measurable and symmetric with the
midpoint inequality `ρ(z+w) ρ(z−w) ≤ ρ(z)² exp(−⟨w, K(z) w⟩)`. Then
`∫ ⟨θ,x⟩² ρ ≤ ∫ ⟨θ, K(x)⁻¹ θ⟩ ρ`.

**Sketch.** `z = 0` and evenness give `ρ(w) ≤ ρ(0) e^{−⟨w,K(0)w⟩/2}`, so every `ρ e^{⟨φ,x⟩}` is
integrable. For `ε > 0` put `f = ρ e^{ε⟨θ,·⟩}`, `g = ρ e^{−ε⟨θ,·⟩}`,
`h(z) = ρ(z) exp((ε²/2)⟨θ, K(z)⁻¹θ⟩)`. With `x = z+w`, `y = z−w`,
`2ε⟨θ,w⟩ ≤ ⟨w,K w⟩ + ε²⟨θ,K⁻¹θ⟩` gives `f(x) g(y) ≤ h(z)²`; midpoint Prékopa–Leindler
(`prekopaLeindler`) gives `∫f ∫g ≤ (∫h)²`, and `∫f = ∫g` by evenness, so `∫f + ∫g ≤ 2∫h`. With
`c(x) = ⟨θ,K(x)⁻¹θ⟩ ∈ [0, |θ|²/κ]`, `eᵘ + e⁻ᵘ ≥ 2 + u²` and `eʸ − 1 ≤ y eʸ`:
`2∫ρ + ε²∫⟨θ,x⟩²ρ ≤ 2∫ρ + ε² e^{ε²|θ|²/(2κ)} ∫ c ρ`; divide by `ε²` and let `ε → 0`. The trace
form follows from `M = Lᵀ L`, summing over the rows of `L`.

**Checks.** `ι` empty: both sides vanish. Gaussian `ρ = exp(−xᵀKx/2)` with constant `K ≻ 0`: the
midpoint inequality and the conclusion are equalities.
-/

@[expose] public section

namespace BiluLinial.Tight

open MeasureTheory Matrix Filter Topology

/-- If `A ≤ e^{s²C/2} B` for every `s > 0`, then `A ≤ B`. -/
lemma le_of_forall_pos_le_exp_mul {A B C : ℝ}
    (h : ∀ s : ℝ, 0 < s → A ≤ Real.exp (s ^ 2 * C / 2) * B) : A ≤ B := by
  have hcont : Continuous fun s : ℝ => Real.exp (s ^ 2 * C / 2) * B := by fun_prop
  have h0 := hcont.tendsto 0
  have hval : Real.exp ((0 : ℝ) ^ 2 * C / 2) * B = B := by simp
  rw [hval] at h0
  exact ge_of_tendsto (h0.mono_left nhdsWithin_le_nhds)
    (eventually_nhdsWithin_of_forall (s := Set.Ioi 0) fun s hs => h s hs)

section Helpers

variable {ι : Type*} [Fintype ι]

/-- A symmetric matrix with `κ |w|² ≤ wᵀ A w` (`κ > 0`) is positive definite. -/
lemma posDef_of_coercive {A : Matrix ι ι ℝ} (hA : A.IsHermitian) {κ : ℝ} (hκ : 0 < κ)
    (hAκ : ∀ w, κ * (w ⬝ᵥ w) ≤ w ⬝ᵥ (A *ᵥ w)) : A.PosDef := by
  refine PosDef.of_dotProduct_mulVec_pos hA fun w hw => ?_
  have h1 : 0 < w ⬝ᵥ w := by
    rcases (Finset.sum_nonneg fun i _ => mul_self_nonneg (w i) : 0 ≤ w ⬝ᵥ w).eq_or_lt with h | h
    · exact absurd (dotProduct_self_eq_zero.1 h.symm) hw
    · exact h
  simpa using (mul_pos hκ h1).trans_le (hAκ w)

/-- The midpoint inequality at `z = 0` and evenness give a Gaussian upper bound. -/
lemma rho_le_gaussWeight_of_midpoint {ρ : (ι → ℝ) → ℝ} (hρ0 : ∀ x, 0 ≤ ρ x)
    (hρe : ∀ x, ρ (-x) = ρ x) {K : (ι → ℝ) → Matrix ι ι ℝ}
    (hmid : ∀ z w, ρ (z + w) * ρ (z - w) ≤ ρ z ^ 2 * Real.exp (-(w ⬝ᵥ (K z *ᵥ w))))
    (x : ι → ℝ) : ρ x ≤ ρ 0 * gaussWeight (K 0) x := by
  have h := hmid 0 x
  rw [zero_add, zero_sub, hρe, ← sq] at h
  have e : (ρ 0 * gaussWeight (K 0) x) ^ 2 = ρ 0 ^ 2 * Real.exp (-(x ⬝ᵥ (K 0 *ᵥ x))) := by
    rw [mul_pow, gaussWeight, ← Real.exp_nat_mul]; congr 2; push_cast; ring
  rw [← e] at h
  exact (pow_le_pow_iff_left₀ (hρ0 x) (mul_nonneg (hρ0 0) (gaussWeight_pos _ _).le)
    two_ne_zero).1 h

lemma integrable_mul_exp_of_le_gaussWeight {ρ : (ι → ℝ) → ℝ} (hρm : Measurable ρ)
    (hρ0 : ∀ x, 0 ≤ ρ x) {M0 : Matrix ι ι ℝ} (hM0 : M0.PosDef)
    (hρG : ∀ x, ρ x ≤ ρ 0 * gaussWeight M0 x) (θ : ι → ℝ) (a : ℝ) :
    Integrable fun x => ρ x * Real.exp (a * (θ ⬝ᵥ x)) := by
  refine (integrable_mul_exp_mul_gaussWeight hM0 (f := fun _ => ρ 0) measurable_const
    (fun _ => hρ0 0) (fun _ => le_rfl) (a • θ)).mono'
    (hρm.mul (by fun_prop)).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hρ0 x) (Real.exp_pos _).le), smul_dotProduct,
    smul_eq_mul]
  calc ρ x * Real.exp (a * (θ ⬝ᵥ x)) ≤ ρ 0 * gaussWeight M0 x * Real.exp (a * (θ ⬝ᵥ x)) :=
        mul_le_mul_of_nonneg_right (hρG x) (Real.exp_pos _).le
    _ = ρ 0 * Real.exp (a * (θ ⬝ᵥ x)) * gaussWeight M0 x := by ring

lemma integrable_of_le_gaussWeight {ρ : (ι → ℝ) → ℝ} (hρm : Measurable ρ)
    (hρ0 : ∀ x, 0 ≤ ρ x) {M0 : Matrix ι ι ℝ} (hM0 : M0.PosDef)
    (hρG : ∀ x, ρ x ≤ ρ 0 * gaussWeight M0 x) : Integrable ρ := by
  simpa using integrable_mul_exp_of_le_gaussWeight hρm hρ0 hM0 hρG 0 0

lemma integrable_sq_mul_of_le_gaussWeight {ρ : (ι → ℝ) → ℝ} (hρm : Measurable ρ)
    (hρ0 : ∀ x, 0 ≤ ρ x) {M0 : Matrix ι ι ℝ} (hM0 : M0.PosDef)
    (hρG : ∀ x, ρ x ≤ ρ 0 * gaussWeight M0 x) (θ : ι → ℝ) :
    Integrable fun x => (θ ⬝ᵥ x) ^ 2 * ρ x := by
  refine ((integrable_mul_exp_of_le_gaussWeight hρm hρ0 hM0 hρG θ 1).add
    (integrable_mul_exp_of_le_gaussWeight hρm hρ0 hM0 hρG θ (-1))).mono'
    (((by fun_prop : Measurable fun x : ι → ℝ => θ ⬝ᵥ x).pow_const 2).mul
      hρm).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (hρ0 x))]
  change (θ ⬝ᵥ x) ^ 2 * ρ x ≤ ρ x * Real.exp (1 * (θ ⬝ᵥ x)) + ρ x * Real.exp (-1 * (θ ⬝ᵥ x))
  rw [one_mul, neg_one_mul]
  have h1 := mul_le_mul_of_nonneg_left (two_add_sq_le_exp_add_exp_neg (θ ⬝ᵥ x)) (hρ0 x)
  nlinarith [h1, hρ0 x]

lemma integrable_mul_of_bdd {ρ c : (ι → ℝ) → ℝ} (hρint : Integrable ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (hcm : Measurable c) {C₀ : ℝ} (hc0 : ∀ x, 0 ≤ c x) (hcC : ∀ x, c x ≤ C₀) :
    Integrable fun x => c x * ρ x := by
  refine (hρint.const_mul C₀).mono' (hcm.aestronglyMeasurable.mul hρint.aestronglyMeasurable)
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hc0 x) (hρ0 x))]
  exact mul_le_mul_of_nonneg_right (hcC x) (hρ0 x)

/-- The analytic core of BLmid: if `ρ` is even, bounded by a Gaussian, and the functions
`ρ e^{ε⟨θ,·⟩}`, `ρ e^{−ε⟨θ,·⟩}`, `ρ e^{(ε²/2) c}` satisfy the Prékopa–Leindler hypothesis for every
`ε`, where `0 ≤ c ≤ C₀` is measurable, then `∫ ⟨θ,x⟩² ρ ≤ ∫ c ρ`. -/
lemma integral_sq_dotProduct_le_of_prekopaLeindler {ρ : (ι → ℝ) → ℝ} (hρm : Measurable ρ)
    (hρ0 : ∀ x, 0 ≤ ρ x) (hρe : ∀ x, ρ (-x) = ρ x) {M0 : Matrix ι ι ℝ} (hM0 : M0.PosDef)
    (hρG : ∀ x, ρ x ≤ ρ 0 * gaussWeight M0 x) {c : (ι → ℝ) → ℝ} (hcm : Measurable c)
    {C₀ : ℝ} (hc0 : ∀ x, 0 ≤ c x) (hcC : ∀ x, c x ≤ C₀) (θ : ι → ℝ)
    (hPL : ∀ (ε : ℝ) (x y : ι → ℝ),
      ρ x * Real.exp (ε * (θ ⬝ᵥ x)) * (ρ y * Real.exp (-(ε * (θ ⬝ᵥ y)))) ≤
        (ρ (midpoint ℝ x y) * Real.exp (ε ^ 2 / 2 * c (midpoint ℝ x y))) ^ 2) :
    ∫ x, (θ ⬝ᵥ x) ^ 2 * ρ x ≤ ∫ x, c x * ρ x := by
  have hexp := integrable_mul_exp_of_le_gaussWeight hρm hρ0 hM0 hρG θ
  have hρint := integrable_of_le_gaussWeight hρm hρ0 hM0 hρG
  have hsq := integrable_sq_mul_of_le_gaussWeight hρm hρ0 hM0 hρG θ
  have hcint := integrable_mul_of_bdd hρint hρ0 hcm hc0 hcC
  have hhint : ∀ b : ℝ, 0 ≤ b → Integrable fun x => ρ x * Real.exp (b * c x) := by
    intro b hb
    refine (hρint.const_mul (Real.exp (b * C₀))).mono' (hρm.mul (by fun_prop)).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hρ0 x) (Real.exp_pos _).le), mul_comm]
    exact mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (hcC x) hb)) (hρ0 x)
  have hmeasE : ∀ a : ℝ, Measurable fun x => ρ x * Real.exp (a * (θ ⬝ᵥ x)) :=
    fun a => hρm.mul (by fun_prop)
  refine le_of_forall_pos_le_exp_mul (C := C₀) fun ε hε => ?_
  have hmeasH : Measurable fun x => ρ x * Real.exp (ε ^ 2 / 2 * c x) := hρm.mul (by fun_prop)
  -- midpoint Prékopa–Leindler
  have key := prekopaLeindler
    (f := fun x => ENNReal.ofReal (ρ x * Real.exp (ε * (θ ⬝ᵥ x))))
    (g := fun x => ENNReal.ofReal (ρ x * Real.exp (-ε * (θ ⬝ᵥ x))))
    (h := fun x => ENNReal.ofReal (ρ x * Real.exp (ε ^ 2 / 2 * c x)))
    (hmeasE ε).ennreal_ofReal (hmeasE (-ε)).ennreal_ofReal hmeasH.ennreal_ofReal ?_
  swap
  · intro x y
    rw [← ENNReal.ofReal_mul (mul_nonneg (hρ0 x) (Real.exp_pos _).le),
      ← ENNReal.ofReal_pow (mul_nonneg (hρ0 _) (Real.exp_pos _).le), neg_mul]
    exact ENNReal.ofReal_le_ofReal (hPL ε x y)
  beta_reduce at key
  have hsym : ∫⁻ x, ENNReal.ofReal (ρ x * Real.exp (-ε * (θ ⬝ᵥ x))) =
      ∫⁻ x, ENNReal.ofReal (ρ x * Real.exp (ε * (θ ⬝ᵥ x))) := by
    refine (lintegral_neg_eq_self _).symm.trans (lintegral_congr fun x => ?_)
    change ENNReal.ofReal (ρ (-x) * Real.exp (-ε * (θ ⬝ᵥ (-x)))) =
      ENNReal.ofReal (ρ x * Real.exp (ε * (θ ⬝ᵥ x)))
    simp only [hρe, dotProduct_neg, neg_mul, mul_neg, neg_neg]
  rw [hsym, ← sq] at key
  have hle := (ENNReal.pow_le_pow_left_iff two_ne_zero).1 key
  -- back to Bochner integrals
  have hA : ∫ x, ρ x * Real.exp (ε * (θ ⬝ᵥ x)) =
      (∫⁻ x, ENNReal.ofReal (ρ x * Real.exp (ε * (θ ⬝ᵥ x)))).toReal :=
    integral_eq_lintegral_of_nonneg_ae
      (Eventually.of_forall fun x => mul_nonneg (hρ0 x) (Real.exp_pos _).le)
      (hmeasE ε).aestronglyMeasurable
  have hH : ∫ x, ρ x * Real.exp (ε ^ 2 / 2 * c x) =
      (∫⁻ x, ENNReal.ofReal (ρ x * Real.exp (ε ^ 2 / 2 * c x))).toReal :=
    integral_eq_lintegral_of_nonneg_ae
      (Eventually.of_forall fun x => mul_nonneg (hρ0 x) (Real.exp_pos _).le)
      hmeasH.aestronglyMeasurable
  have hAH : ∫ x, ρ x * Real.exp (ε * (θ ⬝ᵥ x)) ≤ ∫ x, ρ x * Real.exp (ε ^ 2 / 2 * c x) := by
    rw [hA, hH]
    exact ENNReal.toReal_mono (hhint (ε ^ 2 / 2) (by positivity)).lintegral_lt_top.ne hle
  have hBA : ∫ x, ρ x * Real.exp (-ε * (θ ⬝ᵥ x)) = ∫ x, ρ x * Real.exp (ε * (θ ⬝ᵥ x)) := by
    refine (integral_neg_eq_self _ volume).symm.trans
      (integral_congr_ae (Eventually.of_forall fun x => ?_))
    change ρ (-x) * Real.exp (-ε * (θ ⬝ᵥ (-x))) = ρ x * Real.exp (ε * (θ ⬝ᵥ x))
    simp only [hρe, dotProduct_neg, neg_mul, mul_neg, neg_neg]
  -- `cosh` lower bound
  have hlow : 2 * (∫ x, ρ x) + ε ^ 2 * (∫ x, (θ ⬝ᵥ x) ^ 2 * ρ x) ≤
      (∫ x, ρ x * Real.exp (ε * (θ ⬝ᵥ x))) + ∫ x, ρ x * Real.exp (-ε * (θ ⬝ᵥ x)) := by
    rw [← integral_add (hexp ε) (hexp (-ε)), ← integral_const_mul, ← integral_const_mul,
      ← integral_add (hρint.const_mul 2) (hsq.const_mul _)]
    refine integral_mono ((hρint.const_mul 2).add (hsq.const_mul _))
      ((hexp ε).add (hexp (-ε))) fun x => ?_
    change 2 * ρ x + ε ^ 2 * ((θ ⬝ᵥ x) ^ 2 * ρ x) ≤
      ρ x * Real.exp (ε * (θ ⬝ᵥ x)) + ρ x * Real.exp (-ε * (θ ⬝ᵥ x))
    rw [neg_mul]
    have h1 := mul_le_mul_of_nonneg_left (two_add_sq_le_exp_add_exp_neg (ε * (θ ⬝ᵥ x))) (hρ0 x)
    nlinarith [h1]
  -- exponential upper bound
  have hup : ∫ x, ρ x * Real.exp (ε ^ 2 / 2 * c x) ≤
      (∫ x, ρ x) + ε ^ 2 / 2 * Real.exp (ε ^ 2 * C₀ / 2) * ∫ x, c x * ρ x := by
    rw [← integral_const_mul, ← integral_add hρint (hcint.const_mul _)]
    refine integral_mono (hhint _ (by positivity)) (hρint.add (hcint.const_mul _)) fun x => ?_
    change ρ x * Real.exp (ε ^ 2 / 2 * c x) ≤
      ρ x + ε ^ 2 / 2 * Real.exp (ε ^ 2 * C₀ / 2) * (c x * ρ x)
    have hy0 : 0 ≤ ε ^ 2 / 2 * c x := mul_nonneg (by positivity) (hc0 x)
    have hyY : ε ^ 2 / 2 * c x ≤ ε ^ 2 * C₀ / 2 := by
      nlinarith [mul_le_mul_of_nonneg_left (hcC x) (sq_nonneg ε)]
    have h1 := exp_sub_one_le_mul_exp (ε ^ 2 / 2 * c x)
    have h2 : Real.exp (ε ^ 2 / 2 * c x) ≤ Real.exp (ε ^ 2 * C₀ / 2) := Real.exp_le_exp.2 hyY
    have h3 : Real.exp (ε ^ 2 / 2 * c x) ≤ 1 + ε ^ 2 / 2 * c x * Real.exp (ε ^ 2 * C₀ / 2) := by
      nlinarith [mul_le_mul_of_nonneg_left h2 hy0]
    nlinarith [mul_le_mul_of_nonneg_left h3 (hρ0 x)]
  have hs2 : 0 < ε ^ 2 := by positivity
  have key2 : ε ^ 2 * (∫ x, (θ ⬝ᵥ x) ^ 2 * ρ x) ≤
      ε ^ 2 * (Real.exp (ε ^ 2 * C₀ / 2) * ∫ x, c x * ρ x) := by
    linarith
  exact le_of_mul_le_mul_left key2 hs2

/-- `xᵀ (Bᵀ B) x = Σ_k ⟨B_k, x⟩²`. -/
lemma quad_transpose_mul_self (B : Matrix ι ι ℝ) (x : ι → ℝ) :
    x ⬝ᵥ ((Bᵀ * B) *ᵥ x) = ∑ k, (B k ⬝ᵥ x) ^ 2 := by
  rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
  simp only [dotProduct, mulVec, sq]

/-- `tr(Bᵀ B A) = Σ_k ⟨B_k, A B_k⟩`. -/
lemma trace_transpose_mul_self_mul (B A : Matrix ι ι ℝ) :
    ((Bᵀ * B) * A).trace = ∑ k, B k ⬝ᵥ (A *ᵥ B k) := by
  rw [Matrix.mul_assoc, trace_mul_comm]
  simp only [trace, diag, mul_apply, transpose_apply, dotProduct, mulVec, Finset.sum_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => by ring

open scoped MatrixOrder in
/-- A positive semidefinite real matrix is of the form `Bᵀ B`. -/
lemma exists_eq_transpose_mul_self {M : Matrix ι ι ℝ} (hM : M.PosSemidef) :
    ∃ B : Matrix ι ι ℝ, M = Bᵀ * B := by
  classical
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hM.nonneg
  exact ⟨B, by rw [hB, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]⟩

section Inverse

variable [DecidableEq ι]

/-- Completing the square: `2ε⟨θ,w⟩ − ⟨w,Aw⟩ ≤ ε²⟨θ,A⁻¹θ⟩` for positive definite `A`. -/
lemma two_mul_dotProduct_sub_quad_le {A : Matrix ι ι ℝ} (hA : A.PosDef) (ε : ℝ)
    (θ w : ι → ℝ) : 2 * ε * (θ ⬝ᵥ w) - w ⬝ᵥ (A *ᵥ w) ≤ ε ^ 2 * (θ ⬝ᵥ (A⁻¹ *ᵥ θ)) := by
  have h0 := hA.posSemidef.dotProduct_mulVec_nonneg (w - A⁻¹ *ᵥ (ε • θ))
  rw [star_trivial, quad_sub_inv_mulVec hA] at h0
  simp only [mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul] at h0
  linarith

lemma dotProduct_inv_mulVec_nonneg {A : Matrix ι ι ℝ} (hA : A.PosDef) (θ : ι → ℝ) :
    0 ≤ θ ⬝ᵥ (A⁻¹ *ᵥ θ) := by
  simpa using hA.inv.posSemidef.dotProduct_mulVec_nonneg θ

/-- `⟨θ, A⁻¹θ⟩ ≤ |θ|²/κ` when `A ⪰ κ I`. -/
lemma dotProduct_inv_mulVec_le {A : Matrix ι ι ℝ} (hA : A.PosDef) {κ : ℝ} (hκ : 0 < κ)
    (hAκ : ∀ w, κ * (w ⬝ᵥ w) ≤ w ⬝ᵥ (A *ᵥ w)) (θ : ι → ℝ) :
    θ ⬝ᵥ (A⁻¹ *ᵥ θ) ≤ (θ ⬝ᵥ θ) / κ := by
  obtain ⟨m, hm⟩ : ∃ m, m = A⁻¹ *ᵥ θ := ⟨_, rfl⟩
  rw [← hm]
  have hAm : A *ᵥ m = θ := by
    rw [hm, mulVec_mulVec, A.mul_nonsing_inv ((A.isUnit_iff_isUnit_det).1 hA.isUnit),
      one_mulVec]
  have h1 : κ * (m ⬝ᵥ m) ≤ θ ⬝ᵥ m := by
    have := hAκ m
    rwa [hAm, dotProduct_comm m θ] at this
  have h2 : 0 ≤ (κ • m - θ) ⬝ᵥ (κ • m - θ) := Finset.sum_nonneg fun i _ => mul_self_nonneg _
  simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul] at h2
  have e : m ⬝ᵥ θ = θ ⬝ᵥ m := dotProduct_comm _ _
  rw [le_div_iff₀ hκ]
  nlinarith [mul_le_mul_of_nonneg_left h1 hκ.le]

lemma measurable_matrix_inv : Measurable fun A : Matrix ι ι ℝ => A⁻¹ := by
  have : (fun A : Matrix ι ι ℝ => A⁻¹) = fun A => (A.det)⁻¹ • A.adjugate := by
    funext A; rw [Matrix.inv_def, Ring.inverse_eq_inv]
  rw [this]
  have h1 : Continuous fun A : Matrix ι ι ℝ => A.det := continuous_id.matrix_det
  have h2 : Continuous fun A : Matrix ι ι ℝ => A.adjugate := continuous_id.matrix_adjugate
  exact h1.measurable.inv.smul h2.measurable

lemma measurable_dotProduct_inv_mulVec {K : (ι → ℝ) → Matrix ι ι ℝ} (hKm : Measurable K)
    (θ : ι → ℝ) : Measurable fun x => θ ⬝ᵥ ((K x)⁻¹ *ᵥ θ) :=
  (by fun_prop : Continuous fun A : Matrix ι ι ℝ => θ ⬝ᵥ (A *ᵥ θ)).measurable.comp
    (measurable_matrix_inv.comp hKm)

end Inverse

end Helpers

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- BLmid: `∫ ⟨θ,x⟩² ρ ≤ ∫ ⟨θ, K(x)⁻¹ θ⟩ ρ` under the midpoint inequality with modulus `K ⪰ κ I`. -/
theorem integral_sq_dotProduct_le_of_midpoint {ρ : (ι → ℝ) → ℝ} (hρm : Measurable ρ)
    (hρ0 : ∀ x, 0 ≤ ρ x) (hρe : ∀ x, ρ (-x) = ρ x)
    {K : (ι → ℝ) → Matrix ι ι ℝ} (hKm : Measurable K) {κ : ℝ} (hκ : 0 < κ)
    (hKs : ∀ z, (K z).IsHermitian) (hKκ : ∀ z w, κ * (w ⬝ᵥ w) ≤ w ⬝ᵥ (K z *ᵥ w))
    (hmid : ∀ z w, ρ (z + w) * ρ (z - w) ≤ ρ z ^ 2 * Real.exp (-(w ⬝ᵥ (K z *ᵥ w))))
    (θ : ι → ℝ) :
    ∫ x, (θ ⬝ᵥ x) ^ 2 * ρ x ≤ ∫ x, (θ ⬝ᵥ ((K x)⁻¹ *ᵥ θ)) * ρ x := by
  have hKpd : ∀ z, (K z).PosDef := fun z => posDef_of_coercive (hKs z) hκ (hKκ z)
  refine integral_sq_dotProduct_le_of_prekopaLeindler hρm hρ0 hρe (hKpd 0)
    (rho_le_gaussWeight_of_midpoint hρ0 hρe hmid) (c := fun x => θ ⬝ᵥ ((K x)⁻¹ *ᵥ θ))
    (measurable_dotProduct_inv_mulVec hKm θ) (fun x => dotProduct_inv_mulVec_nonneg (hKpd x) θ)
    (fun x => dotProduct_inv_mulVec_le (hKpd x) hκ (hKκ x) θ) θ fun ε x y => ?_
  obtain ⟨z, hz⟩ : ∃ z, z = midpoint ℝ x y := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : ι → ℝ, w = (2⁻¹ : ℝ) • (x - y) := ⟨_, rfl⟩
  have hx : z + w = x := by
    subst hz hw; ext i
    simp only [midpoint_eq_smul_add, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
      invOf_eq_inv]
    ring
  have hy : z - w = y := by
    subst hz hw; ext i
    simp only [midpoint_eq_smul_add, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
      invOf_eq_inv]
    ring
  have hθ : θ ⬝ᵥ x - θ ⬝ᵥ y = 2 * (θ ⬝ᵥ w) := by
    rw [hw, dotProduct_smul, dotProduct_sub, smul_eq_mul]; ring
  have h2 := two_mul_dotProduct_sub_quad_le (hKpd z) ε θ w
  rw [← hz]
  calc ρ x * Real.exp (ε * (θ ⬝ᵥ x)) * (ρ y * Real.exp (-(ε * (θ ⬝ᵥ y))))
      = ρ (z + w) * ρ (z - w) * Real.exp (2 * ε * (θ ⬝ᵥ w)) := by
        rw [hx, hy, show 2 * ε * (θ ⬝ᵥ w) = ε * (θ ⬝ᵥ x) + -(ε * (θ ⬝ᵥ y)) by
          linear_combination (-ε) * hθ, Real.exp_add]
        ring
    _ ≤ ρ z ^ 2 * Real.exp (-(w ⬝ᵥ (K z *ᵥ w))) * Real.exp (2 * ε * (θ ⬝ᵥ w)) :=
        mul_le_mul_of_nonneg_right (hmid z w) (Real.exp_pos _).le
    _ = ρ z ^ 2 * Real.exp (2 * ε * (θ ⬝ᵥ w) - w ⬝ᵥ (K z *ᵥ w)) := by
        rw [mul_assoc, ← Real.exp_add, neg_add_eq_sub]
    _ ≤ ρ z ^ 2 * Real.exp (ε ^ 2 * (θ ⬝ᵥ ((K z)⁻¹ *ᵥ θ))) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 h2) (sq_nonneg _)
    _ = (ρ z * Real.exp (ε ^ 2 / 2 * (θ ⬝ᵥ ((K z)⁻¹ *ᵥ θ)))) ^ 2 := by
        rw [mul_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring

/-- BLmid, trace form: for `M ⪰ 0`, `∫ xᵀ M x ρ ≤ ∫ tr(M K(x)⁻¹) ρ`. -/
theorem integral_quad_le_of_midpoint {ρ : (ι → ℝ) → ℝ} (hρm : Measurable ρ)
    (hρ0 : ∀ x, 0 ≤ ρ x) (hρe : ∀ x, ρ (-x) = ρ x)
    {K : (ι → ℝ) → Matrix ι ι ℝ} (hKm : Measurable K) {κ : ℝ} (hκ : 0 < κ)
    (hKs : ∀ z, (K z).IsHermitian) (hKκ : ∀ z w, κ * (w ⬝ᵥ w) ≤ w ⬝ᵥ (K z *ᵥ w))
    (hmid : ∀ z w, ρ (z + w) * ρ (z - w) ≤ ρ z ^ 2 * Real.exp (-(w ⬝ᵥ (K z *ᵥ w))))
    {M : Matrix ι ι ℝ} (hM : M.PosSemidef) :
    ∫ x, (x ⬝ᵥ (M *ᵥ x)) * ρ x ≤ ∫ x, (M * (K x)⁻¹).trace * ρ x := by
  obtain ⟨B, rfl⟩ := exists_eq_transpose_mul_self hM
  have hKpd : ∀ z, (K z).PosDef := fun z => posDef_of_coercive (hKs z) hκ (hKκ z)
  have hρG := rho_le_gaussWeight_of_midpoint hρ0 hρe hmid
  have hρint := integrable_of_le_gaussWeight hρm hρ0 (hKpd 0) hρG
  have e1 : ∫ x, (x ⬝ᵥ ((Bᵀ * B) *ᵥ x)) * ρ x = ∫ x, ∑ k, (B k ⬝ᵥ x) ^ 2 * ρ x :=
    integral_congr_ae (Eventually.of_forall fun x => by
      change (x ⬝ᵥ ((Bᵀ * B) *ᵥ x)) * ρ x = ∑ k, (B k ⬝ᵥ x) ^ 2 * ρ x
      rw [quad_transpose_mul_self, Finset.sum_mul])
  have e2 : ∫ x, ((Bᵀ * B) * (K x)⁻¹).trace * ρ x =
      ∫ x, ∑ k, (B k ⬝ᵥ ((K x)⁻¹ *ᵥ B k)) * ρ x :=
    integral_congr_ae (Eventually.of_forall fun x => by
      change ((Bᵀ * B) * (K x)⁻¹).trace * ρ x = ∑ k, (B k ⬝ᵥ ((K x)⁻¹ *ᵥ B k)) * ρ x
      rw [trace_transpose_mul_self_mul, Finset.sum_mul])
  rw [e1, e2,
    integral_finsetSum _ fun k _ => integrable_sq_mul_of_le_gaussWeight hρm hρ0 (hKpd 0) hρG (B k),
    integral_finsetSum _ fun k _ => integrable_mul_of_bdd hρint hρ0
      (measurable_dotProduct_inv_mulVec hKm (B k))
      (fun x => dotProduct_inv_mulVec_nonneg (hKpd x) _)
      (fun x => dotProduct_inv_mulVec_le (hKpd x) hκ (hKκ x) _)]
  exact Finset.sum_le_sum fun k _ =>
    integral_sq_dotProduct_le_of_midpoint hρm hρ0 hρe hKm hκ hKs hKκ hmid (B k)

end BiluLinial.Tight
