/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.Gauss.IBP

/-!
# The derivative of a Gaussian correlation functional

For independent standard Gaussian vectors `X, Y` on `ι → ℝ` and `s ∈ [-1, 1]`, the vectors `X` and
`Y_s = sX + √(1-s²) Y` are standard Gaussian with cross covariance `s I`. For functions `f, g`
put
`gaussCorr f g s = 𝔼 f(X) g(Y_s)`.
The Gaussian correlation argument of Part D (Lemma "Uniform incident-row gain") uses that this
function of `s` has left derivative `𝔼 ⟨∇f(X), ∇g(X)⟩` at `s = 1`
(`hasDerivWithinAt_gaussCorr_one`), so that monotonicity on `[0, 1]` gives
`𝔼 ⟨∇f, ∇g⟩ ≥ 0` (`integral_inner_grad_nonneg_of_monotoneOn`).

The proof differentiates under the integral for `|s| < 1` (`hasDerivAt_gaussCorr`), evaluates the
derivative by Gaussian integration by parts in `X` and in `Y`
(`integral_corrDeriv_eq`: the second-order terms cancel), and passes to the limit `s → 1⁻`.
-/

@[expose] public section

namespace BiluLinial.Tight

open MeasureTheory ProbabilityTheory Real Filter Topology Set

variable {ι : Type*} [Fintype ι]

/-- The Gaussian correlation functional `s ↦ 𝔼 f(X) g(sX + √(1-s²) Y)`, `X, Y` independent
standard Gaussian vectors. -/
noncomputable def gaussCorr (f g : (ι → ℝ) → ℝ) (s : ℝ) : ℝ :=
  ∫ p, f p.1 * g (s • p.1 + √(1 - s ^ 2) • p.2) ∂(gaussPi ι).prod (gaussPi ι)

/-! ### Elementary bounds -/

theorem sqrt_one_sub_sq_le_one (s : ℝ) : √(1 - s ^ 2) ≤ 1 := by
  calc √(1 - s ^ 2) ≤ √1 := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg s])
    _ = 1 := Real.sqrt_one

theorem abs_sqrt_one_sub_sq_le_one (s : ℝ) : |√(1 - s ^ 2)| ≤ 1 := by
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]; exact sqrt_one_sub_sq_le_one s

theorem norm_smul_add_smul_le {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) (x y : ι → ℝ) :
    ‖a • x + b • y‖ ≤ ‖x‖ + ‖y‖ := by
  calc ‖a • x + b • y‖ ≤ ‖a • x‖ + ‖b • y‖ := norm_add_le _ _
    _ = |a| * ‖x‖ + |b| * ‖y‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ 1 * ‖x‖ + 1 * ‖y‖ := by gcongr
    _ = ‖x‖ + ‖y‖ := by ring

theorem one_add_norm_smul_add_smul_pow_le {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    (x y : ι → ℝ) (m : ℕ) :
    (1 + ‖a • x + b • y‖) ^ m ≤ (1 + ‖x‖) ^ m * (1 + ‖y‖) ^ m := by
  rw [← mul_pow]
  apply pow_le_pow_left₀ (by positivity)
  nlinarith [norm_smul_add_smul_le ha hb x y, norm_nonneg x, norm_nonneg y,
    mul_nonneg (norm_nonneg x) (norm_nonneg y)]

theorem norm_apply_single_le [DecidableEq ι] (L : (ι → ℝ) →L[ℝ] ℝ) (k : ι) :
    ‖L (Pi.single k 1)‖ ≤ ‖L‖ := by
  calc ‖L (Pi.single k 1)‖ ≤ ‖L‖ * ‖(Pi.single k 1 : ι → ℝ)‖ := L.le_opNorm _
    _ = ‖L‖ := by rw [Pi.norm_single, norm_one, mul_one]

theorem norm_apply_single_single_le [DecidableEq ι] (B : (ι → ℝ) →L[ℝ] (ι → ℝ) →L[ℝ] ℝ)
    (k : ι) : ‖B (Pi.single k 1) (Pi.single k 1)‖ ≤ ‖B‖ := by
  calc ‖B (Pi.single k 1) (Pi.single k 1)‖
        ≤ ‖B‖ * ‖(Pi.single k 1 : ι → ℝ)‖ * ‖(Pi.single k 1 : ι → ℝ)‖ := B.le_opNorm₂ _ _
    _ = ‖B‖ := by rw [Pi.norm_single, norm_one, mul_one, mul_one]

/-- A linear functional on `ι → ℝ` in coordinates. -/
theorem clm_apply_eq_sum [DecidableEq ι] (L : (ι → ℝ) →L[ℝ] ℝ) (v : ι → ℝ) :
    L v = ∑ k, v k * L (Pi.single k 1) := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show (Pi.single k (v k) : ι → ℝ) = v k • Pi.single k 1 by
    rw [← Pi.single_smul, smul_eq_mul, mul_one], map_smul, smul_eq_mul]

/-- `u(x) v(ax + by)` is polynomially bounded on pairs when `u`, `v` are and `|a|, |b| ≤ 1`. -/
theorem norm_mul_comp_le {u v : (ι → ℝ) → ℝ} {K : ℝ} {m : ℕ}
    (hu : ∀ x, ‖u x‖ ≤ K * (1 + ‖x‖) ^ m) (hv : ∀ z, ‖v z‖ ≤ K * (1 + ‖z‖) ^ m) {a b : ℝ}
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (p : (ι → ℝ) × (ι → ℝ)) :
    ‖u p.1 * v (a • p.1 + b • p.2)‖ ≤ K * K * ((1 + ‖p.1‖) ^ (m + m) * (1 + ‖p.2‖) ^ m) := by
  have hK : 0 ≤ K := by simpa using (norm_nonneg _).trans (hu 0)
  rw [norm_mul]
  calc ‖u p.1‖ * ‖v (a • p.1 + b • p.2)‖
        ≤ (K * (1 + ‖p.1‖) ^ m) * (K * ((1 + ‖p.1‖) ^ m * (1 + ‖p.2‖) ^ m)) :=
        mul_le_mul (hu _) ((hv _).trans (mul_le_mul_of_nonneg_left
          (one_add_norm_smul_add_smul_pow_le ha hb _ _ m) hK)) (norm_nonneg _) (by positivity)
    _ = K * K * ((1 + ‖p.1‖) ^ (m + m) * (1 + ‖p.2‖) ^ m) := by ring

/-! ### Integration by parts on pairs of independent Gaussian vectors -/

/-- A polynomially bounded function of a pair of independent standard Gaussian vectors is
integrable. -/
theorem integrable_of_polyBound_gaussPair {Φ : (ι → ℝ) × (ι → ℝ) → ℝ}
    (hΦ : AEStronglyMeasurable Φ ((gaussPi ι).prod (gaussPi ι))) {K : ℝ} {a b : ℕ}
    (hb : ∀ p, ‖Φ p‖ ≤ K * ((1 + ‖p.1‖) ^ a * (1 + ‖p.2‖) ^ b)) :
    Integrable Φ ((gaussPi ι).prod (gaussPi ι)) :=
  (((integrable_one_add_norm_pow_gaussPi a).mul_prod
    (integrable_one_add_norm_pow_gaussPi b)).const_mul K).mono' hΦ (ae_of_all _ hb)

theorem norm_fst_mul_le {Φ : (ι → ℝ) × (ι → ℝ) → ℝ} {K : ℝ} {a b : ℕ}
    (hb : ∀ p, ‖Φ p‖ ≤ K * ((1 + ‖p.1‖) ^ a * (1 + ‖p.2‖) ^ b)) (k : ι)
    (p : (ι → ℝ) × (ι → ℝ)) :
    ‖p.1 k * Φ p‖ ≤ K * ((1 + ‖p.1‖) ^ (a + 1) * (1 + ‖p.2‖) ^ b) := by
  have h0 : 0 ≤ K * ((1 + ‖p.1‖) ^ a * (1 + ‖p.2‖) ^ b) := (norm_nonneg _).trans (hb p)
  rw [norm_mul]
  calc ‖p.1 k‖ * ‖Φ p‖ ≤ (1 + ‖p.1‖) * (K * ((1 + ‖p.1‖) ^ a * (1 + ‖p.2‖) ^ b)) :=
        mul_le_mul (by linarith [norm_le_pi_norm p.1 k]) (hb p) (norm_nonneg _) (by positivity)
    _ = K * ((1 + ‖p.1‖) ^ (a + 1) * (1 + ‖p.2‖) ^ b) := by ring

theorem norm_snd_mul_le {Φ : (ι → ℝ) × (ι → ℝ) → ℝ} {K : ℝ} {a b : ℕ}
    (hb : ∀ p, ‖Φ p‖ ≤ K * ((1 + ‖p.1‖) ^ a * (1 + ‖p.2‖) ^ b)) (k : ι)
    (p : (ι → ℝ) × (ι → ℝ)) :
    ‖p.2 k * Φ p‖ ≤ K * ((1 + ‖p.1‖) ^ a * (1 + ‖p.2‖) ^ (b + 1)) := by
  have h0 : 0 ≤ K * ((1 + ‖p.1‖) ^ a * (1 + ‖p.2‖) ^ b) := (norm_nonneg _).trans (hb p)
  rw [norm_mul]
  calc ‖p.2 k‖ * ‖Φ p‖ ≤ (1 + ‖p.2‖) * (K * ((1 + ‖p.1‖) ^ a * (1 + ‖p.2‖) ^ b)) :=
        mul_le_mul (by linarith [norm_le_pi_norm p.2 k]) (hb p) (norm_nonneg _) (by positivity)
    _ = K * ((1 + ‖p.1‖) ^ a * (1 + ‖p.2‖) ^ (b + 1)) := by ring

/-- Stein's identity in the first vector of a pair of independent standard Gaussian vectors. -/
theorem stein_gaussPair_fst [DecidableEq ι] {Φ Ψ : (ι → ℝ) × (ι → ℝ) → ℝ} (k : ι)
    (hΦ : Continuous Φ) (hΨ : Continuous Ψ)
    (hd : ∀ x y t, HasDerivAt (fun r => Φ (Function.update x k r, y))
      (Ψ (Function.update x k t, y)) t)
    {K : ℝ} {a b : ℕ} (hΦb : ∀ p, ‖Φ p‖ ≤ K * ((1 + ‖p.1‖) ^ a * (1 + ‖p.2‖) ^ b))
    (hΨb : ∀ p, ‖Ψ p‖ ≤ K * ((1 + ‖p.1‖) ^ a * (1 + ‖p.2‖) ^ b)) :
    ∫ p, p.1 k * Φ p ∂(gaussPi ι).prod (gaussPi ι) =
      ∫ p, Ψ p ∂(gaussPi ι).prod (gaussPi ι) := by
  have i1 : Integrable (fun p : (ι → ℝ) × (ι → ℝ) => p.1 k * Φ p)
      ((gaussPi ι).prod (gaussPi ι)) :=
    integrable_of_polyBound_gaussPair (by fun_prop : Continuous _).aestronglyMeasurable
      (norm_fst_mul_le hΦb k)
  have i2 := integrable_of_polyBound_gaussPair hΨ.aestronglyMeasurable hΨb
  rw [integral_prod_symm _ i1, integral_prod_symm _ i2]
  congr 1
  ext y
  refine stein_gaussPi_of_hasDerivAt k
    (by fun_prop : Continuous fun x => Φ (x, y)).aestronglyMeasurable
    (by fun_prop : Continuous fun x => Ψ (x, y)).aestronglyMeasurable (fun x t => hd x y t)
    (K := K * (1 + ‖y‖) ^ b) (m := a) (fun x => ?_) (fun x => ?_)
  · exact (hΦb (x, y)).trans_eq (by ring)
  · exact (hΨb (x, y)).trans_eq (by ring)

/-- Stein's identity in the second vector of a pair of independent standard Gaussian vectors. -/
theorem stein_gaussPair_snd [DecidableEq ι] {Φ Ψ : (ι → ℝ) × (ι → ℝ) → ℝ} (k : ι)
    (hΦ : Continuous Φ) (hΨ : Continuous Ψ)
    (hd : ∀ x y t, HasDerivAt (fun r => Φ (x, Function.update y k r))
      (Ψ (x, Function.update y k t)) t)
    {K : ℝ} {a b : ℕ} (hΦb : ∀ p, ‖Φ p‖ ≤ K * ((1 + ‖p.1‖) ^ a * (1 + ‖p.2‖) ^ b))
    (hΨb : ∀ p, ‖Ψ p‖ ≤ K * ((1 + ‖p.1‖) ^ a * (1 + ‖p.2‖) ^ b)) :
    ∫ p, p.2 k * Φ p ∂(gaussPi ι).prod (gaussPi ι) =
      ∫ p, Ψ p ∂(gaussPi ι).prod (gaussPi ι) := by
  have i1 : Integrable (fun p : (ι → ℝ) × (ι → ℝ) => p.2 k * Φ p)
      ((gaussPi ι).prod (gaussPi ι)) :=
    integrable_of_polyBound_gaussPair (by fun_prop : Continuous _).aestronglyMeasurable
      (norm_snd_mul_le hΦb k)
  have i2 := integrable_of_polyBound_gaussPair hΨ.aestronglyMeasurable hΨb
  rw [integral_prod _ i1, integral_prod _ i2]
  congr 1
  ext x
  refine stein_gaussPi_of_hasDerivAt k
    (by fun_prop : Continuous fun y => Φ (x, y)).aestronglyMeasurable
    (by fun_prop : Continuous fun y => Ψ (x, y)).aestronglyMeasurable (fun y t => hd x y t)
    (K := K * (1 + ‖x‖) ^ a) (m := b) (fun y => ?_) (fun y => ?_)
  · exact (hΦb (x, y)).trans_eq (by ring)
  · exact (hΨb (x, y)).trans_eq (by ring)

/-! ### Integration by parts for the correlation derivative -/

section Corr

variable [DecidableEq ι] {f g : (ι → ℝ) → ℝ} {K : ℝ} {m : ℕ}

/-- Gaussian integration by parts in `X` for `𝔼[X_k f(X) ∂_k g(aX + bY)]`. -/
theorem corr_stein_fst (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 2 g)
    (hfb : ∀ x, ‖f x‖ ≤ K * (1 + ‖x‖) ^ m) (hf'b : ∀ x, ‖fderiv ℝ f x‖ ≤ K * (1 + ‖x‖) ^ m)
    (hg'b : ∀ x, ‖fderiv ℝ g x‖ ≤ K * (1 + ‖x‖) ^ m)
    (hg''b : ∀ x, ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ K * (1 + ‖x‖) ^ m) {a b : ℝ} (ha : |a| ≤ 1)
    (hb : |b| ≤ 1) (k : ι) :
    ∫ p, p.1 k * (f p.1 * fderiv ℝ g (a • p.1 + b • p.2) (Pi.single k 1))
        ∂(gaussPi ι).prod (gaussPi ι) =
      ∫ p, (fderiv ℝ f p.1 (Pi.single k 1) * fderiv ℝ g (a • p.1 + b • p.2) (Pi.single k 1) +
        a * (f p.1 * fderiv ℝ (fderiv ℝ g) (a • p.1 + b • p.2) (Pi.single k 1)
          (Pi.single k 1))) ∂(gaussPi ι).prod (gaussPi ι) := by
  have hK : 0 ≤ K := by simpa using (norm_nonneg _).trans (hfb 0)
  have hfd : Differentiable ℝ f := hf.differentiable one_ne_zero
  have hfc : Continuous f := hf.continuous
  have hf'c : Continuous (fderiv ℝ f) := hf.continuous_fderiv one_ne_zero
  have hg1 : ContDiff ℝ 1 (fderiv ℝ g) := hg.fderiv_right (m := 1) (by norm_num)
  have hgd2 : Differentiable ℝ (fderiv ℝ g) := hg1.differentiable one_ne_zero
  have hg'c : Continuous (fderiv ℝ g) := hg1.continuous
  have hg''c : Continuous (fderiv ℝ (fderiv ℝ g)) := hg1.continuous_fderiv one_ne_zero
  have hgk : ∀ z, ‖fderiv ℝ g z (Pi.single k 1)‖ ≤ K * (1 + ‖z‖) ^ m := fun z =>
    (norm_apply_single_le _ k).trans (hg'b z)
  have hgkk : ∀ z, ‖fderiv ℝ (fderiv ℝ g) z (Pi.single k 1) (Pi.single k 1)‖ ≤
      K * (1 + ‖z‖) ^ m := fun z => (norm_apply_single_single_le _ k).trans (hg''b z)
  have hfk : ∀ x, ‖fderiv ℝ f x (Pi.single k 1)‖ ≤ K * (1 + ‖x‖) ^ m := fun x =>
    (norm_apply_single_le _ k).trans (hf'b x)
  refine stein_gaussPair_fst k (by fun_prop) (by fun_prop) (fun x y t => ?_)
    (K := 2 * (K * K)) (a := m + m) (b := m) (fun p => ?_) (fun p => ?_)
  · have h1 : HasDerivAt (fun r => f (Function.update x k r))
        (fderiv ℝ f (Function.update x k t) (Pi.single k 1)) t :=
      (hfd _).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_update x k t)
    have hpath : HasDerivAt (fun r => a • Function.update x k r + b • y)
        (a • (Pi.single k 1 : ι → ℝ)) t :=
      ((hasDerivAt_update x k t).const_smul a).add_const (b • y)
    have h2 := (hasFDerivAt_fderiv_apply_const (hgd2 (a • Function.update x k t + b • y))
      (Pi.single k (1 : ℝ))).comp_hasDerivAt t hpath
    refine (h1.mul h2).congr_deriv ?_
    simp only [Function.comp_apply, ContinuousLinearMap.flip_apply, map_smul, smul_eq_mul]
    ring
  · have := norm_mul_comp_le hfb hgk ha hb p
    have h0 : 0 ≤ K * K * ((1 + ‖p.1‖) ^ (m + m) * (1 + ‖p.2‖) ^ m) := by positivity
    linarith
  · have h1 := norm_mul_comp_le hfk hgk ha hb p
    have h2 := norm_mul_comp_le hfb hgkk ha hb p
    calc _ ≤ ‖fderiv ℝ f p.1 (Pi.single k 1) * fderiv ℝ g (a • p.1 + b • p.2) (Pi.single k 1)‖
          + |a| * ‖f p.1 * fderiv ℝ (fderiv ℝ g) (a • p.1 + b • p.2) (Pi.single k 1)
            (Pi.single k 1)‖ := by
          rw [← Real.norm_eq_abs, ← norm_mul]; exact norm_add_le _ _
      _ ≤ K * K * ((1 + ‖p.1‖) ^ (m + m) * (1 + ‖p.2‖) ^ m)
          + 1 * (K * K * ((1 + ‖p.1‖) ^ (m + m) * (1 + ‖p.2‖) ^ m)) := by gcongr
      _ = _ := by ring

/-- Gaussian integration by parts in `Y` for `𝔼[Y_k f(X) ∂_k g(aX + bY)]`. -/
theorem corr_stein_snd (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 2 g)
    (hfb : ∀ x, ‖f x‖ ≤ K * (1 + ‖x‖) ^ m)
    (hg'b : ∀ x, ‖fderiv ℝ g x‖ ≤ K * (1 + ‖x‖) ^ m)
    (hg''b : ∀ x, ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ K * (1 + ‖x‖) ^ m) {a b : ℝ} (ha : |a| ≤ 1)
    (hb : |b| ≤ 1) (k : ι) :
    ∫ p, p.2 k * (f p.1 * fderiv ℝ g (a • p.1 + b • p.2) (Pi.single k 1))
        ∂(gaussPi ι).prod (gaussPi ι) =
      ∫ p, b * (f p.1 * fderiv ℝ (fderiv ℝ g) (a • p.1 + b • p.2) (Pi.single k 1)
          (Pi.single k 1)) ∂(gaussPi ι).prod (gaussPi ι) := by
  have hK : 0 ≤ K := by simpa using (norm_nonneg _).trans (hfb 0)
  have hfc : Continuous f := hf.continuous
  have hg1 : ContDiff ℝ 1 (fderiv ℝ g) := hg.fderiv_right (m := 1) (by norm_num)
  have hgd2 : Differentiable ℝ (fderiv ℝ g) := hg1.differentiable one_ne_zero
  have hg'c : Continuous (fderiv ℝ g) := hg1.continuous
  have hg''c : Continuous (fderiv ℝ (fderiv ℝ g)) := hg1.continuous_fderiv one_ne_zero
  have hgk : ∀ z, ‖fderiv ℝ g z (Pi.single k 1)‖ ≤ K * (1 + ‖z‖) ^ m := fun z =>
    (norm_apply_single_le _ k).trans (hg'b z)
  have hgkk : ∀ z, ‖fderiv ℝ (fderiv ℝ g) z (Pi.single k 1) (Pi.single k 1)‖ ≤
      K * (1 + ‖z‖) ^ m := fun z => (norm_apply_single_single_le _ k).trans (hg''b z)
  refine stein_gaussPair_snd k (by fun_prop) (by fun_prop) (fun x y t => ?_)
    (K := K * K) (a := m + m) (b := m) (fun p => norm_mul_comp_le hfb hgk ha hb p) (fun p => ?_)
  · have hpath : HasDerivAt (fun r => a • x + b • Function.update y k r)
        (b • (Pi.single k 1 : ι → ℝ)) t :=
      ((hasDerivAt_update y k t).const_smul b).const_add (a • x)
    have h2 := (hasFDerivAt_fderiv_apply_const (hgd2 (a • x + b • Function.update y k t))
      (Pi.single k (1 : ℝ))).comp_hasDerivAt t hpath
    refine (h2.const_mul (f x)).congr_deriv ?_
    simp only [ContinuousLinearMap.flip_apply, map_smul, smul_eq_mul]
    ring
  · rw [norm_mul, Real.norm_eq_abs]
    calc |b| * ‖f p.1 * fderiv ℝ (fderiv ℝ g) (a • p.1 + b • p.2) (Pi.single k 1)
          (Pi.single k 1)‖ ≤ 1 * (K * K * ((1 + ‖p.1‖) ^ (m + m) * (1 + ‖p.2‖) ^ m)) :=
          mul_le_mul hb (norm_mul_comp_le hfb hgkk ha hb p) (norm_nonneg _) zero_le_one
      _ = _ := one_mul _

/-- **The correlation derivative after integration by parts.** For `|s| < 1`,
`𝔼 f(X) Dg(Y_s)(X - s(1-s²)^{-1/2} Y) = 𝔼 ⟨∇f(X), ∇g(Y_s)⟩`. -/
theorem integral_corrDeriv_eq (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 2 g)
    (hfb : ∀ x, ‖f x‖ ≤ K * (1 + ‖x‖) ^ m) (hf'b : ∀ x, ‖fderiv ℝ f x‖ ≤ K * (1 + ‖x‖) ^ m)
    (hg'b : ∀ x, ‖fderiv ℝ g x‖ ≤ K * (1 + ‖x‖) ^ m)
    (hg''b : ∀ x, ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ K * (1 + ‖x‖) ^ m) {s : ℝ} (hs : |s| < 1) :
    ∫ p, f p.1 * fderiv ℝ g (s • p.1 + √(1 - s ^ 2) • p.2) (p.1 + (-s / √(1 - s ^ 2)) • p.2)
        ∂(gaussPi ι).prod (gaussPi ι) =
      ∫ p, ∑ k, fderiv ℝ f p.1 (Pi.single k 1) *
        fderiv ℝ g (s • p.1 + √(1 - s ^ 2) • p.2) (Pi.single k 1)
        ∂(gaussPi ι).prod (gaussPi ι) := by
  have hK : 0 ≤ K := by simpa using (norm_nonneg _).trans (hfb 0)
  have hfc : Continuous f := hf.continuous
  have hf'c : Continuous (fderiv ℝ f) := hf.continuous_fderiv one_ne_zero
  have hg1 : ContDiff ℝ 1 (fderiv ℝ g) := hg.fderiv_right (m := 1) (by norm_num)
  have hg'c : Continuous (fderiv ℝ g) := hg1.continuous
  have hg''c : Continuous (fderiv ℝ (fderiv ℝ g)) := hg1.continuous_fderiv one_ne_zero
  have hs1 : |s| ≤ 1 := hs.le
  have hc0 : 0 < √(1 - s ^ 2) := Real.sqrt_pos.2 (by nlinarith [sq_abs s, abs_nonneg s])
  have hc1 := abs_sqrt_one_sub_sq_le_one s
  generalize √(1 - s ^ 2) = c at hc0 hc1 ⊢
  have hcc : -s / c * c = -s := by field_simp
  have hgk : ∀ k z, ‖fderiv ℝ g z (Pi.single k 1)‖ ≤ K * (1 + ‖z‖) ^ m := fun k z =>
    (norm_apply_single_le _ k).trans (hg'b z)
  have hgkk : ∀ k z, ‖fderiv ℝ (fderiv ℝ g) z (Pi.single k 1) (Pi.single k 1)‖ ≤
      K * (1 + ‖z‖) ^ m := fun k z => (norm_apply_single_single_le _ k).trans (hg''b z)
  have hfk : ∀ k x, ‖fderiv ℝ f x (Pi.single k 1)‖ ≤ K * (1 + ‖x‖) ^ m := fun k x =>
    (norm_apply_single_le _ k).trans (hf'b x)
  -- integrability of the pieces
  have iΦ1 : ∀ k, Integrable (fun p : (ι → ℝ) × (ι → ℝ) =>
      p.1 k * (f p.1 * fderiv ℝ g (s • p.1 + c • p.2) (Pi.single k 1)))
      ((gaussPi ι).prod (gaussPi ι)) := fun k =>
    integrable_of_polyBound_gaussPair (by fun_prop : Continuous _).aestronglyMeasurable
      (norm_fst_mul_le (norm_mul_comp_le hfb (hgk k) hs1 hc1) k)
  have iΦ2 : ∀ k, Integrable (fun p : (ι → ℝ) × (ι → ℝ) =>
      p.2 k * (f p.1 * fderiv ℝ g (s • p.1 + c • p.2) (Pi.single k 1)))
      ((gaussPi ι).prod (gaussPi ι)) := fun k =>
    integrable_of_polyBound_gaussPair (by fun_prop : Continuous _).aestronglyMeasurable
      (norm_snd_mul_le (norm_mul_comp_le hfb (hgk k) hs1 hc1) k)
  have iA : ∀ k, Integrable (fun p : (ι → ℝ) × (ι → ℝ) =>
      fderiv ℝ f p.1 (Pi.single k 1) * fderiv ℝ g (s • p.1 + c • p.2) (Pi.single k 1))
      ((gaussPi ι).prod (gaussPi ι)) := fun k =>
    integrable_of_polyBound_gaussPair (by fun_prop : Continuous _).aestronglyMeasurable
      (norm_mul_comp_le (hfk k) (hgk k) hs1 hc1)
  have iB : ∀ k, Integrable (fun p : (ι → ℝ) × (ι → ℝ) =>
      f p.1 * fderiv ℝ (fderiv ℝ g) (s • p.1 + c • p.2) (Pi.single k 1) (Pi.single k 1))
      ((gaussPi ι).prod (gaussPi ι)) := fun k =>
    integrable_of_polyBound_gaussPair (by fun_prop : Continuous _).aestronglyMeasurable
      (norm_mul_comp_le hfb (hgkk k) hs1 hc1)
  have hexp : ∀ p : (ι → ℝ) × (ι → ℝ),
      f p.1 * fderiv ℝ g (s • p.1 + c • p.2) (p.1 + (-s / c) • p.2) =
        ∑ k, (p.1 k * (f p.1 * fderiv ℝ g (s • p.1 + c • p.2) (Pi.single k 1)) +
          -s / c * (p.2 k * (f p.1 * fderiv ℝ g (s • p.1 + c • p.2) (Pi.single k 1)))) := by
    intro p
    rw [clm_apply_eq_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  calc ∫ p, f p.1 * fderiv ℝ g (s • p.1 + c • p.2) (p.1 + (-s / c) • p.2)
          ∂(gaussPi ι).prod (gaussPi ι)
      = ∫ p, ∑ k, (p.1 k * (f p.1 * fderiv ℝ g (s • p.1 + c • p.2) (Pi.single k 1)) +
          -s / c * (p.2 k * (f p.1 * fderiv ℝ g (s • p.1 + c • p.2) (Pi.single k 1))))
          ∂(gaussPi ι).prod (gaussPi ι) := integral_congr_ae (ae_of_all _ hexp)
    _ = ∑ k, ∫ p, (p.1 k * (f p.1 * fderiv ℝ g (s • p.1 + c • p.2) (Pi.single k 1)) +
          -s / c * (p.2 k * (f p.1 * fderiv ℝ g (s • p.1 + c • p.2) (Pi.single k 1))))
          ∂(gaussPi ι).prod (gaussPi ι) :=
        integral_finsetSum _ fun k _ => (iΦ1 k).add ((iΦ2 k).const_mul _)
    _ = ∑ k, ∫ p, fderiv ℝ f p.1 (Pi.single k 1) *
          fderiv ℝ g (s • p.1 + c • p.2) (Pi.single k 1) ∂(gaussPi ι).prod (gaussPi ι) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [integral_add (iΦ1 k) ((iΦ2 k).const_mul _), integral_const_mul,
          corr_stein_fst hf hg hfb hf'b hg'b hg''b hs1 hc1 k,
          corr_stein_snd hf hg hfb hg'b hg''b hs1 hc1 k, integral_add (iA k) ((iB k).const_mul _),
          integral_const_mul, integral_const_mul]
        linear_combination (∫ p, f p.1 * fderiv ℝ (fderiv ℝ g) (s • p.1 + c • p.2)
          (Pi.single k 1) (Pi.single k 1) ∂(gaussPi ι).prod (gaussPi ι)) * hcc
    _ = _ := (integral_finsetSum _ fun k _ => iA k).symm

/-! ### Differentiation in `s` -/

theorem hasDerivAt_sqrt_one_sub_sq {s : ℝ} (hs : |s| < 1) :
    HasDerivAt (fun r : ℝ => √(1 - r ^ 2)) (-s / √(1 - s ^ 2)) s := by
  have h1 : 0 < 1 - s ^ 2 := by nlinarith [sq_abs s, abs_nonneg s]
  have h2 := ((hasDerivAt_pow 2 s).const_sub 1).sqrt h1.ne'
  refine h2.congr_deriv ?_
  have h3 : √(1 - s ^ 2) ≠ 0 := (Real.sqrt_pos.2 h1).ne'
  field_simp
  norm_num

theorem hasDerivAt_corrPath {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : ℝ}
    (hs : |s| < 1) (x y : E) :
    HasDerivAt (fun r : ℝ => r • x + √(1 - r ^ 2) • y) (x + (-s / √(1 - s ^ 2)) • y) s :=
  (((hasDerivAt_id s).smul_const x).add
    ((hasDerivAt_sqrt_one_sub_sq hs).smul_const y)).congr_deriv (by rw [one_smul])

omit [DecidableEq ι] in
/-- Differentiation of `gaussCorr f g` under the integral sign at `|s₀| < 1`. -/
theorem hasDerivAt_gaussCorr (hf : Continuous f) (hg : ContDiff ℝ 1 g)
    (hfb : ∀ x, ‖f x‖ ≤ K * (1 + ‖x‖) ^ m) (hgb : ∀ x, ‖g x‖ ≤ K * (1 + ‖x‖) ^ m)
    (hg'b : ∀ x, ‖fderiv ℝ g x‖ ≤ K * (1 + ‖x‖) ^ m) {s₀ : ℝ} (hs₀ : |s₀| < 1) :
    HasDerivAt (gaussCorr f g) (∫ p, f p.1 * fderiv ℝ g (s₀ • p.1 + √(1 - s₀ ^ 2) • p.2)
      (p.1 + (-s₀ / √(1 - s₀ ^ 2)) • p.2) ∂(gaussPi ι).prod (gaussPi ι)) s₀ := by
  have hK : 0 ≤ K := by simpa using (norm_nonneg _).trans (hfb 0)
  have hgc : Continuous g := hg.continuous
  have hg'c : Continuous (fderiv ℝ g) := hg.continuous_fderiv one_ne_zero
  have hgd : Differentiable ℝ g := hg.differentiable one_ne_zero
  obtain ⟨r, hr0, hr1⟩ : ∃ r, |s₀| < r ∧ r < 1 := ⟨(1 + |s₀|) / 2, by linarith, by linarith⟩
  have hrpos : 0 < r := (abs_nonneg s₀).trans_lt hr0
  have hδ : 0 < 1 - r ^ 2 := by nlinarith
  have hball : ∀ s ∈ Metric.ball s₀ (r - |s₀|), |s| < r := fun s hs => by
    rw [Metric.mem_ball, Real.dist_eq] at hs
    have := abs_sub_abs_le_abs_sub s s₀
    linarith
  have hsq : 0 < √(1 - r ^ 2) := Real.sqrt_pos.2 hδ
  set M : ℝ := 1 / √(1 - r ^ 2) with hM
  have hM0 : 0 ≤ M := by positivity
  have hc' : ∀ s, |s| < r → |-s / √(1 - s ^ 2)| ≤ M := fun s hs => by
    have h1 : 1 - r ^ 2 ≤ 1 - s ^ 2 := by nlinarith [sq_abs s, abs_nonneg s]
    have h2 : √(1 - r ^ 2) ≤ √(1 - s ^ 2) := Real.sqrt_le_sqrt h1
    have h3 : 0 < √(1 - s ^ 2) := hsq.trans_le h2
    rw [abs_div, abs_neg, abs_of_pos h3, hM, div_le_div_iff₀ h3 hsq]
    exact mul_le_mul (by linarith) h2 hsq.le zero_le_one
  have h_bound : ∀ p : (ι → ℝ) × (ι → ℝ), ∀ s ∈ Metric.ball s₀ (r - |s₀|),
      ‖f p.1 * fderiv ℝ g (s • p.1 + √(1 - s ^ 2) • p.2) (p.1 + (-s / √(1 - s ^ 2)) • p.2)‖ ≤
        K * K * (1 + M) * ((1 + ‖p.1‖) ^ (m + m + 1) * (1 + ‖p.2‖) ^ (m + 1)) := by
    intro p s hs
    have hsr := hball s hs
    have hs1 : |s| ≤ 1 := by linarith
    have hcM := hc' s hsr
    have hv : ‖p.1 + (-s / √(1 - s ^ 2)) • p.2‖ ≤ (1 + M) * ((1 + ‖p.1‖) * (1 + ‖p.2‖)) := by
      calc _ ≤ ‖p.1‖ + |(-s / √(1 - s ^ 2))| * ‖p.2‖ :=
            (norm_add_le _ _).trans_eq (by rw [norm_smul, Real.norm_eq_abs])
        _ ≤ ‖p.1‖ + M * ‖p.2‖ := by gcongr
        _ ≤ (1 + M) * ((1 + ‖p.1‖) * (1 + ‖p.2‖)) := by
            nlinarith [norm_nonneg p.1, norm_nonneg p.2,
              mul_nonneg (norm_nonneg p.1) (norm_nonneg p.2), mul_nonneg hM0 (norm_nonneg p.1),
              mul_nonneg hM0 (mul_nonneg (norm_nonneg p.1) (norm_nonneg p.2))]
    have hDg : ‖fderiv ℝ g (s • p.1 + √(1 - s ^ 2) • p.2)‖ ≤
        K * ((1 + ‖p.1‖) ^ m * (1 + ‖p.2‖) ^ m) :=
      (hg'b _).trans (mul_le_mul_of_nonneg_left (one_add_norm_smul_add_smul_pow_le hs1
        (abs_sqrt_one_sub_sq_le_one s) _ _ m) hK)
    rw [norm_mul]
    calc _ ≤ (K * (1 + ‖p.1‖) ^ m) * ((K * ((1 + ‖p.1‖) ^ m * (1 + ‖p.2‖) ^ m)) *
          ((1 + M) * ((1 + ‖p.1‖) * (1 + ‖p.2‖)))) :=
          mul_le_mul (hfb _) ((ContinuousLinearMap.le_opNorm _ _).trans
            (mul_le_mul hDg hv (norm_nonneg _) (by positivity))) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have h_diff : ∀ p : (ι → ℝ) × (ι → ℝ), ∀ s ∈ Metric.ball s₀ (r - |s₀|),
      HasDerivAt (fun s => f p.1 * g (s • p.1 + √(1 - s ^ 2) • p.2))
        (f p.1 * fderiv ℝ g (s • p.1 + √(1 - s ^ 2) • p.2)
          (p.1 + (-s / √(1 - s ^ 2)) • p.2)) s := by
    intro p s hs
    have hs1 : |s| < 1 := (hball s hs).trans hr1
    exact ((hgd _).hasFDerivAt.comp_hasDerivAt s (hasDerivAt_corrPath hs1 p.1 p.2)).const_mul
      (f p.1)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (gaussPi ι).prod (gaussPi ι))
    (F := fun s p => f p.1 * g (s • p.1 + √(1 - s ^ 2) • p.2))
    (F' := fun s p => f p.1 * fderiv ℝ g (s • p.1 + √(1 - s ^ 2) • p.2)
      (p.1 + (-s / √(1 - s ^ 2)) • p.2))
    (x₀ := s₀)
    (bound := fun p => K * K * (1 + M) * ((1 + ‖p.1‖) ^ (m + m + 1) * (1 + ‖p.2‖) ^ (m + 1)))
    (Metric.ball_mem_nhds s₀ (by linarith : 0 < r - |s₀|))
    (Eventually.of_forall fun s => (by fun_prop : Continuous fun p : (ι → ℝ) × (ι → ℝ) =>
      f p.1 * g (s • p.1 + √(1 - s ^ 2) • p.2)).aestronglyMeasurable)
    (integrable_of_polyBound_gaussPair (by fun_prop : Continuous fun p : (ι → ℝ) × (ι → ℝ) =>
      f p.1 * g (s₀ • p.1 + √(1 - s₀ ^ 2) • p.2)).aestronglyMeasurable
      (norm_mul_comp_le hfb hgb hs₀.le (abs_sqrt_one_sub_sq_le_one s₀)))
    (by fun_prop : Continuous fun p : (ι → ℝ) × (ι → ℝ) =>
      f p.1 * fderiv ℝ g (s₀ • p.1 + √(1 - s₀ ^ 2) • p.2)
        (p.1 + (-s₀ / √(1 - s₀ ^ 2)) • p.2)).aestronglyMeasurable
    (ae_of_all _ h_bound)
    (((integrable_one_add_norm_pow_gaussPi _).mul_prod
      (integrable_one_add_norm_pow_gaussPi _)).const_mul _)
    (ae_of_all _ h_diff)
  exact key.2

/-! ### Continuity at `s = 1` -/

omit [DecidableEq ι] in
theorem continuousWithinAt_gaussCorr_one (hf : Continuous f) (hg : Continuous g)
    (hfb : ∀ x, ‖f x‖ ≤ K * (1 + ‖x‖) ^ m) (hgb : ∀ x, ‖g x‖ ≤ K * (1 + ‖x‖) ^ m) :
    ContinuousWithinAt (gaussCorr f g) (Icc 0 1) 1 := by
  have hmeas : ∀ᶠ s in 𝓝[Icc 0 1] (1 : ℝ), AEStronglyMeasurable
      (fun p : (ι → ℝ) × (ι → ℝ) => f p.1 * g (s • p.1 + √(1 - s ^ 2) • p.2))
      ((gaussPi ι).prod (gaussPi ι)) :=
    Eventually.of_forall fun s => (by fun_prop : Continuous fun p : (ι → ℝ) × (ι → ℝ) =>
      f p.1 * g (s • p.1 + √(1 - s ^ 2) • p.2)).aestronglyMeasurable
  have hbound : ∀ᶠ s in 𝓝[Icc 0 1] (1 : ℝ), ∀ᵐ p ∂(gaussPi ι).prod (gaussPi ι),
      ‖f p.1 * g (s • p.1 + √(1 - s ^ 2) • p.2)‖ ≤
        K * K * ((1 + ‖p.1‖) ^ (m + m) * (1 + ‖p.2‖) ^ m) := by
    refine eventually_nhdsWithin_of_forall fun s hs => ae_of_all _ fun p => ?_
    have hs1 : |s| ≤ 1 := abs_le.2 ⟨by linarith [hs.1], hs.2⟩
    exact norm_mul_comp_le hfb hgb hs1 (abs_sqrt_one_sub_sq_le_one s) p
  have hint : Integrable (fun p : (ι → ℝ) × (ι → ℝ) =>
      K * K * ((1 + ‖p.1‖) ^ (m + m) * (1 + ‖p.2‖) ^ m)) ((gaussPi ι).prod (gaussPi ι)) :=
    ((integrable_one_add_norm_pow_gaussPi (m + m)).mul_prod
      (integrable_one_add_norm_pow_gaussPi m)).const_mul (K * K)
  have hcont : ∀ᵐ p ∂(gaussPi ι).prod (gaussPi ι), ContinuousWithinAt
      (fun s : ℝ => f p.1 * g (s • p.1 + √(1 - s ^ 2) • p.2)) (Icc 0 1) 1 :=
    ae_of_all _ fun p => (by fun_prop : Continuous fun s : ℝ =>
      f p.1 * g (s • p.1 + √(1 - s ^ 2) • p.2)).continuousWithinAt
  exact continuousWithinAt_of_dominated hmeas hbound hint hcont

theorem continuousWithinAt_corrGrad_one (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hf'b : ∀ x, ‖fderiv ℝ f x‖ ≤ K * (1 + ‖x‖) ^ m)
    (hg'b : ∀ x, ‖fderiv ℝ g x‖ ≤ K * (1 + ‖x‖) ^ m) :
    ContinuousWithinAt (fun s => ∫ p, ∑ k, fderiv ℝ f p.1 (Pi.single k 1) *
      fderiv ℝ g (s • p.1 + √(1 - s ^ 2) • p.2) (Pi.single k 1) ∂(gaussPi ι).prod (gaussPi ι))
      (Icc 0 1) 1 := by
  have hf'c : Continuous (fderiv ℝ f) := hf.continuous_fderiv one_ne_zero
  have hg'c : Continuous (fderiv ℝ g) := hg.continuous_fderiv one_ne_zero
  have hgk : ∀ k z, ‖fderiv ℝ g z (Pi.single k 1)‖ ≤ K * (1 + ‖z‖) ^ m := fun k z =>
    (norm_apply_single_le _ k).trans (hg'b z)
  have hfk : ∀ k x, ‖fderiv ℝ f x (Pi.single k 1)‖ ≤ K * (1 + ‖x‖) ^ m := fun k x =>
    (norm_apply_single_le _ k).trans (hf'b x)
  have hmeas : ∀ᶠ s in 𝓝[Icc 0 1] (1 : ℝ), AEStronglyMeasurable
      (fun p : (ι → ℝ) × (ι → ℝ) => ∑ k, fderiv ℝ f p.1 (Pi.single k 1) *
        fderiv ℝ g (s • p.1 + √(1 - s ^ 2) • p.2) (Pi.single k 1))
      ((gaussPi ι).prod (gaussPi ι)) :=
    Eventually.of_forall fun s => (by fun_prop : Continuous fun p : (ι → ℝ) × (ι → ℝ) =>
      ∑ k, fderiv ℝ f p.1 (Pi.single k 1) *
        fderiv ℝ g (s • p.1 + √(1 - s ^ 2) • p.2) (Pi.single k 1)).aestronglyMeasurable
  have hbound : ∀ᶠ s in 𝓝[Icc 0 1] (1 : ℝ), ∀ᵐ p ∂(gaussPi ι).prod (gaussPi ι),
      ‖∑ k, fderiv ℝ f p.1 (Pi.single k 1) *
        fderiv ℝ g (s • p.1 + √(1 - s ^ 2) • p.2) (Pi.single k 1)‖ ≤
        (Fintype.card ι : ℝ) * (K * K * ((1 + ‖p.1‖) ^ (m + m) * (1 + ‖p.2‖) ^ m)) := by
    refine eventually_nhdsWithin_of_forall fun s hs => ae_of_all _ fun p => ?_
    have hs1 : |s| ≤ 1 := abs_le.2 ⟨by linarith [hs.1], hs.2⟩
    refine (norm_sum_le _ _).trans ?_
    calc _ ≤ ∑ _k : ι, K * K * ((1 + ‖p.1‖) ^ (m + m) * (1 + ‖p.2‖) ^ m) :=
          Finset.sum_le_sum fun k _ => norm_mul_comp_le (hfk k) (hgk k) hs1
            (abs_sqrt_one_sub_sq_le_one s) p
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hint : Integrable (fun p : (ι → ℝ) × (ι → ℝ) => (Fintype.card ι : ℝ) *
      (K * K * ((1 + ‖p.1‖) ^ (m + m) * (1 + ‖p.2‖) ^ m))) ((gaussPi ι).prod (gaussPi ι)) :=
    (((integrable_one_add_norm_pow_gaussPi (m + m)).mul_prod
      (integrable_one_add_norm_pow_gaussPi m)).const_mul (K * K)).const_mul _
  have hcont : ∀ᵐ p ∂(gaussPi ι).prod (gaussPi ι), ContinuousWithinAt
      (fun s : ℝ => ∑ k, fderiv ℝ f p.1 (Pi.single k 1) *
        fderiv ℝ g (s • p.1 + √(1 - s ^ 2) • p.2) (Pi.single k 1)) (Icc 0 1) 1 :=
    ae_of_all _ fun p => (by fun_prop : Continuous fun s : ℝ =>
      ∑ k, fderiv ℝ f p.1 (Pi.single k 1) *
        fderiv ℝ g (s • p.1 + √(1 - s ^ 2) • p.2) (Pi.single k 1)).continuousWithinAt
  exact continuousWithinAt_of_dominated hmeas hbound hint hcont

/-! ### The left derivative at `s = 1` -/

/-- **The Gaussian correlation derivative.** For `f ∈ C¹`, `g ∈ C²` with `f, Df, g, Dg, D²g`
polynomially bounded, `s ↦ 𝔼 f(X) g(sX + √(1-s²) Y)` has left derivative
`𝔼 ⟨∇f(X), ∇g(X)⟩` at `s = 1`. -/
theorem hasDerivWithinAt_gaussCorr_one (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 2 g)
    (hfb : ∀ x, ‖f x‖ ≤ K * (1 + ‖x‖) ^ m) (hf'b : ∀ x, ‖fderiv ℝ f x‖ ≤ K * (1 + ‖x‖) ^ m)
    (hgb : ∀ x, ‖g x‖ ≤ K * (1 + ‖x‖) ^ m) (hg'b : ∀ x, ‖fderiv ℝ g x‖ ≤ K * (1 + ‖x‖) ^ m)
    (hg''b : ∀ x, ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ K * (1 + ‖x‖) ^ m) :
    HasDerivWithinAt (gaussCorr f g)
      (∫ x, ∑ k, fderiv ℝ f x (Pi.single k 1) * fderiv ℝ g x (Pi.single k 1) ∂gaussPi ι)
      (Iic 1) 1 := by
  have hg1 : ContDiff ℝ 1 g := hg.of_le (by norm_num)
  set D : ℝ → ℝ := fun s => ∫ p, ∑ k, fderiv ℝ f p.1 (Pi.single k 1) *
      fderiv ℝ g (s • p.1 + √(1 - s ^ 2) • p.2) (Pi.single k 1) ∂(gaussPi ι).prod (gaussPi ι)
    with hD
  have hderiv : ∀ s, |s| < 1 → HasDerivAt (gaussCorr f g) (D s) s := fun s hs => by
    have := hasDerivAt_gaussCorr hf.continuous hg1 hfb hgb hg'b hs
    rwa [integral_corrDeriv_eq hf hg hfb hf'b hg'b hg''b hs] at this
  have hD1 : D 1 =
      ∫ x, ∑ k, fderiv ℝ f x (Pi.single k 1) * fderiv ℝ g x (Pi.single k 1) ∂gaussPi ι := by
    simp only [hD, one_smul, one_pow, sub_self, Real.sqrt_zero, zero_smul, add_zero]
    rw [integral_fun_fst
      (f := fun x => ∑ k, fderiv ℝ f x (Pi.single k 1) * fderiv ℝ g x (Pi.single k 1))]
    simp
  have hmem : ∀ s ∈ Ioo (0 : ℝ) 1, |s| < 1 := fun s hs => abs_lt.2 ⟨by linarith [hs.1], hs.2⟩
  refine hasDerivWithinAt_Iic_of_tendsto_deriv (s := Ioo 0 1)
    (fun s hs => (hderiv s (hmem s hs)).differentiableAt.differentiableWithinAt)
    ((continuousWithinAt_gaussCorr_one hf.continuous hg1.continuous hfb hgb).mono
      Ioo_subset_Icc_self) (Ioo_mem_nhdsLT zero_lt_one) ?_
  rw [← hD1]
  have h1 : Tendsto D (𝓝[<] 1) (𝓝 (D 1)) :=
    ((continuousWithinAt_corrGrad_one hf hg1 hf'b hg'b).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsLT zero_lt_one)).tendsto
  refine h1.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with s hs
  exact (hderiv s (hmem s hs)).deriv.symm

/-- If `s ↦ 𝔼 f(X) g(sX + √(1-s²) Y)` is monotone on `[0, 1]` (e.g. by the Gaussian correlation
inequality), then `𝔼 ⟨∇f, ∇g⟩ ≥ 0`. -/
theorem integral_inner_grad_nonneg_of_monotoneOn (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 2 g)
    (hfb : ∀ x, ‖f x‖ ≤ K * (1 + ‖x‖) ^ m) (hf'b : ∀ x, ‖fderiv ℝ f x‖ ≤ K * (1 + ‖x‖) ^ m)
    (hgb : ∀ x, ‖g x‖ ≤ K * (1 + ‖x‖) ^ m) (hg'b : ∀ x, ‖fderiv ℝ g x‖ ≤ K * (1 + ‖x‖) ^ m)
    (hg''b : ∀ x, ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ K * (1 + ‖x‖) ^ m)
    (hmono : MonotoneOn (gaussCorr f g) (Icc 0 1)) :
    0 ≤ ∫ x, ∑ k, fderiv ℝ f x (Pi.single k 1) * fderiv ℝ g x (Pi.single k 1) ∂gaussPi ι := by
  have hd := (hasDerivWithinAt_gaussCorr_one hf hg hfb hf'b hgb hg'b hg''b).mono
    (Icc_subset_Iic_self : Icc (0 : ℝ) 1 ⊆ Iic 1)
  rw [hasDerivWithinAt_iff_tendsto_slope, Icc_sdiff_right,
    nhdsWithin_Ico_eq_nhdsLT zero_lt_one] at hd
  refine ge_of_tendsto hd ?_
  filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with s hs
  rw [slope_def_field]
  have := hmono ⟨hs.1.le, hs.2.le⟩ ⟨zero_le_one, le_rfl⟩ hs.2.le
  exact div_nonneg_of_nonpos (by linarith) (by linarith [hs.2])

end Corr

end BiluLinial.Tight
