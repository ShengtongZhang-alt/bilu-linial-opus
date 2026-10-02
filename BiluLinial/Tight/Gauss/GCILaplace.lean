/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.Gauss.Basic
public import BiluLinial.Tight.Gauss.GCIMatrix

/-!
# Gaussian Laplace transforms of quadratic forms

Nodes of the GCI subtree (`docs/tight/GCI_PLAN.md`):

* `gaussPi_map_mulVec_orthogonal` (GCI-ROT): `gaussPi` is invariant under orthogonal matrices.
* `integral_exp_neg_quadForm` (GCI-R1): for `G` standard Gaussian, `S` a real matrix and
  `m ≥ 0`, `𝔼 exp(-½ ∑ᵢ mᵢ (S G)ᵢ²) = det(1 + diag(m) S Sᵀ)^{-1/2}`.
* `integral_exp_neg_quadForm_three` (GCI-R4): the same with three independent copies,
  `= det(1 + diag(m) S Sᵀ)^{-3/2}`.
-/

@[expose] public section

namespace BiluLinial.Tight

open MeasureTheory ProbabilityTheory Matrix Real
open scoped RealInnerProductSpace Kronecker

section ROT

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- **GCI-ROT.** The standard Gaussian measure on `κ → ℝ` is invariant under orthogonal
matrices. -/
theorem gaussPi_map_mulVec_orthogonal {U : Matrix κ κ ℝ} (hU : U * Uᵀ = 1) :
    (gaussPi κ).map (fun g => U *ᵥ g) = gaussPi κ := by
  unfold gaussPi
  rw [← charFun_eq_pi_iff]
  intro t
  have hmeasU : Measurable fun g : κ → ℝ => U *ᵥ g := by fun_prop
  rw [Measure.map_map (by fun_prop) hmeasU, charFun_apply,
    integral_map (by fun_prop) (by fun_prop)]
  set t' : EuclideanSpace ℝ κ := WithLp.toLp 2 (Uᵀ *ᵥ WithLp.ofLp t) with ht'
  have key : ∀ g : κ → ℝ,
      ⟪WithLp.toLp 2 (U *ᵥ g), t⟫ = ⟪WithLp.toLp 2 g, t'⟫ := by
    intro g
    simp only [ht', EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
    rw [dotProduct_comm (Uᵀ *ᵥ _) g, dotProduct_mulVec g Uᵀ, vecMul_transpose]
    exact dotProduct_comm _ _
  have h1 : charFun ((Measure.pi fun _ : κ => gaussianReal 0 1).map (WithLp.toLp 2)) t' =
      ∫ g, Complex.exp (↑⟪WithLp.toLp 2 g, t'⟫ * Complex.I)
        ∂Measure.pi fun _ : κ => gaussianReal 0 1 := by
    rw [charFun_apply, integral_map (by fun_prop) (by fun_prop)]
  have hprod : ∀ u : EuclideanSpace ℝ κ, ∏ i, charFun (gaussianReal 0 1) (u i) =
      Complex.exp (-(↑(∑ i, (u i) ^ 2 : ℝ)) / 2) := by
    intro u
    simp only [charFun_gaussianReal, Complex.ofReal_zero, mul_zero, zero_mul, NNReal.coe_one,
      Complex.ofReal_one, one_mul, zero_sub, ← Complex.exp_sum]
    congr 1
    push_cast
    rw [Finset.sum_neg_distrib, neg_div, Finset.sum_div]
  have hsq : ∑ i, (t' i) ^ 2 = ∑ i, (t i) ^ 2 := by
    have : ∑ i, (t' i) ^ 2 = (Uᵀ *ᵥ WithLp.ofLp t) ⬝ᵥ (Uᵀ *ᵥ WithLp.ofLp t) := by
      simp [ht', dotProduct, sq]
    rw [this, dotProduct_mulVec, vecMul_transpose, mulVec_mulVec, hU, one_mulVec]
    simp [dotProduct, sq]
  calc _ = ∫ g, Complex.exp (↑⟪WithLp.toLp 2 g, t'⟫ * Complex.I)
        ∂Measure.pi fun _ : κ => gaussianReal 0 1 := by
          congr 1; ext g; rw [Function.comp_apply, key]
    _ = _ := by rw [← h1, charFun_pi, hprod, hprod, hsq]

end ROT

section R1

/-- One-dimensional Gaussian Laplace transform of a square. -/
theorem integral_exp_neg_mul_sq_gaussianReal {d : ℝ} (hd : 0 ≤ d) :
    ∫ x, Real.exp (-(d * x ^ 2) / 2) ∂gaussianReal 0 1 = (1 + d) ^ (-(1 / 2 : ℝ)) := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num)]
  have hpt : ∀ x : ℝ, gaussianPDFReal 0 1 x • Real.exp (-(d * x ^ 2) / 2) =
      (√(2 * π))⁻¹ * Real.exp (-((1 + d) / 2) * x ^ 2) := by
    intro x
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, smul_eq_mul, mul_assoc,
      ← Real.exp_add]
    congr 2
    ring
  simp_rw [hpt]
  rw [integral_const_mul, integral_gaussian]
  have h1d : 0 < 1 + d := by linarith
  have hπ : 0 < π := Real.pi_pos
  rw [show π / ((1 + d) / 2) = (2 * π) / (1 + d) by field_simp]
  rw [Real.sqrt_div' _ h1d.le, Real.rpow_neg h1d.le, ← Real.sqrt_eq_rpow]
  have h2π : 0 < √(2 * π) := Real.sqrt_pos.mpr (by positivity)
  have h1dsq : 0 < √(1 + d) := Real.sqrt_pos.mpr h1d
  field_simp

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

omit [DecidableEq κ] in
/-- Laplace transform of a diagonal quadratic form under `gaussPi`. -/
theorem integral_exp_neg_diag_quadForm {d : κ → ℝ} (hd : ∀ i, 0 ≤ d i) :
    ∫ g, Real.exp (-(∑ i, d i * g i ^ 2) / 2) ∂gaussPi κ = ∏ i, (1 + d i) ^ (-(1 / 2 : ℝ)) := by
  have : ∀ g : κ → ℝ, Real.exp (-(∑ i, d i * g i ^ 2) / 2) =
      ∏ i, Real.exp (-(d i * g i ^ 2) / 2) := by
    intro g
    rw [← Real.exp_sum, ← Finset.sum_div, Finset.sum_neg_distrib]
  simp_rw [this]
  unfold gaussPi
  rw [integral_fintype_prod_eq_prod (f := fun i x => Real.exp (-(d i * x ^ 2) / 2))]
  exact Finset.prod_congr rfl fun i _ => integral_exp_neg_mul_sq_gaussianReal (hd i)

/-- Laplace transform of a PSD quadratic form under `gaussPi`. -/
theorem integral_exp_neg_posSemidef_quadForm {K : Matrix κ κ ℝ} (hK : K.PosSemidef) :
    ∫ g, Real.exp (-(g ⬝ᵥ (K *ᵥ g)) / 2) ∂gaussPi κ = (1 + K).det ^ (-(1 / 2 : ℝ)) := by
  set V : Matrix κ κ ℝ := (hK.1.eigenvectorUnitary : Matrix κ κ ℝ) with hVdef
  set d : κ → ℝ := hK.1.eigenvalues with hd
  have hd0 : ∀ i, 0 ≤ d i := hK.eigenvalues_nonneg
  have hspec : K = V * diagonal d * Vᵀ := by
    have := hK.1.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    simpa [V, d, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using this
  have hVV : Vᵀ * V = 1 := by
    have := Unitary.coe_star_mul_self hK.1.eigenvectorUnitary
    simpa [V, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using this
  have hVV' : V * Vᵀ = 1 := mul_eq_one_comm.mp hVV
  have hq : ∀ g : κ → ℝ, g ⬝ᵥ (K *ᵥ g) = ∑ i, d i * (Vᵀ *ᵥ g) i ^ 2 := by
    intro g
    rw [hspec, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← transpose_transpose V,
      vecMul_transpose, transpose_transpose]
    simp only [dotProduct, mulVec_diagonal]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp_rw [hq]
  have hmap := gaussPi_map_mulVec_orthogonal (U := Vᵀ) (by rw [transpose_transpose]; exact hVV)
  have hcv : ∫ g, Real.exp (-(∑ i, d i * (Vᵀ *ᵥ g) i ^ 2) / 2) ∂gaussPi κ =
      ∫ y, Real.exp (-(∑ i, d i * y i ^ 2) / 2) ∂gaussPi κ := by
    conv_rhs => rw [← hmap]
    have hc : Continuous fun y : κ → ℝ => Real.exp (-(∑ i, d i * y i ^ 2) / 2) := by fun_prop
    rw [integral_map (by fun_prop) hc.aestronglyMeasurable]
  rw [hcv, integral_exp_neg_diag_quadForm hd0]
  have hdet : (1 + K).det = ∏ i, (1 + d i) := by
    have h1 : 1 + K = V * diagonal (fun i => 1 + d i) * Vᵀ := by
      rw [hspec, show diagonal (fun i => 1 + d i) = 1 + diagonal d by
        ext i j; by_cases h : i = j <;> simp [diagonal, one_apply, h]]
      rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hVV']
    rw [h1, det_mul, det_mul, det_diagonal, mul_comm, ← mul_assoc, ← det_mul, hVV, det_one,
      one_mul]
  rw [hdet, Real.finsetProd_rpow _ _ fun i _ => by linarith [hd0 i]]

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **GCI-R1.** Gaussian Laplace transform of `½ ∑ᵢ mᵢ (S G)ᵢ²`. -/
theorem integral_exp_neg_quadForm (S : Matrix n κ ℝ) {m : n → ℝ} (hm : ∀ i, 0 ≤ m i) :
    ∫ g, Real.exp (-(∑ i, m i * (S *ᵥ g) i ^ 2) / 2) ∂gaussPi κ =
      (1 + diagonal m * (S * Sᵀ)).det ^ (-(1 / 2 : ℝ)) := by
  set K : Matrix κ κ ℝ := Sᵀ * diagonal m * S with hK
  have hKpsd : K.PosSemidef := by
    have hD : (diagonal m).PosSemidef := PosSemidef.diagonal hm
    have := hD.conjTranspose_mul_mul_same S
    simpa [hK, conjTranspose_eq_transpose_of_trivial] using this
  have hq : ∀ g : κ → ℝ, ∑ i, m i * (S *ᵥ g) i ^ 2 = g ⬝ᵥ (K *ᵥ g) := by
    intro g
    rw [hK, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
    simp only [dotProduct, mulVec_diagonal]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp_rw [hq]
  rw [integral_exp_neg_posSemidef_quadForm hKpsd]
  congr 1
  rw [hK, Matrix.mul_assoc, det_one_add_mul_comm, Matrix.mul_assoc]

/-- **GCI-R4.** Three independent copies: `𝔼 exp(-½ ∑ᵢ mᵢ ∑ₗ (S Gₗ)ᵢ²) = det(…)^{-3/2}`. -/
theorem integral_exp_neg_quadForm_three (S : Matrix n κ ℝ) {m : n → ℝ} (hm : ∀ i, 0 ≤ m i) :
    ∫ g, Real.exp (-(∑ i, m i * ∑ l : Fin 3, (S *ᵥ fun j => g (l, j)) i ^ 2) / 2)
        ∂gaussPi (Fin 3 × κ) =
      (1 + diagonal m * (S * Sᵀ)).det ^ (-(3 / 2 : ℝ)) := by
  set S3 : Matrix (Fin 3 × n) (Fin 3 × κ) ℝ := (1 : Matrix (Fin 3) (Fin 3) ℝ) ⊗ₖ S with hS3
  set m3 : Fin 3 × n → ℝ := fun p => m p.2 with hm3
  have hm3nn : ∀ p, 0 ≤ m3 p := fun p => hm p.2
  have hmv : ∀ (g : Fin 3 × κ → ℝ) (l : Fin 3) (i : n),
      (S3 *ᵥ g) (l, i) = (S *ᵥ fun j => g (l, j)) i := by
    intro g l i
    simp only [hS3, mulVec, dotProduct, Fintype.sum_prod_type, kroneckerMap_apply, one_apply]
    rw [Finset.sum_eq_single l]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  have hsum : ∀ g : Fin 3 × κ → ℝ, ∑ p, m3 p * (S3 *ᵥ g) p ^ 2 =
      ∑ i, m i * ∑ l : Fin 3, (S *ᵥ fun j => g (l, j)) i ^ 2 := by
    intro g
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by rw [hmv]
  simp_rw [← hsum]
  rw [integral_exp_neg_quadForm S3 hm3nn]
  have hdiag : diagonal m3 = (1 : Matrix (Fin 3) (Fin 3) ℝ) ⊗ₖ diagonal m := by
    ext ⟨l, i⟩ ⟨l', i'⟩
    by_cases hl : l = l' <;> by_cases hi : i = i' <;>
      simp [hm3, diagonal, one_apply, kroneckerMap_apply, hl, hi]
  have hS3T : S3ᵀ = (1 : Matrix (Fin 3) (Fin 3) ℝ) ⊗ₖ Sᵀ := by
    rw [hS3, ← kroneckerMap_transpose, transpose_one]
  have hblk : 1 + diagonal m3 * (S3 * S3ᵀ) =
      (1 : Matrix (Fin 3) (Fin 3) ℝ) ⊗ₖ (1 + diagonal m * (S * Sᵀ)) := by
    rw [hS3T, hdiag, hS3, ← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul,
      Matrix.one_mul, kronecker_add, one_kronecker_one]
  rw [hblk, det_kronecker, det_one, one_pow, one_mul, Fintype.card_fin]
  have hD : 0 ≤ (1 + diagonal m * (S * Sᵀ)).det := by
    have hC : (S * Sᵀ).PosSemidef := by
      simpa [conjTranspose_eq_transpose_of_trivial] using posSemidef_self_mul_conjTranspose S
    linarith [one_le_det_one_add_diagonal_mul hm hC]
  rw [← Real.rpow_natCast, ← Real.rpow_mul hD]
  norm_num

end R1

end BiluLinial.Tight
