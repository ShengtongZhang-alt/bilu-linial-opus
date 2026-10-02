/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecB.W1FibCfg
public import BiluLinial.Tight.SecA.EndpointDefs

/-!
# The weak loop (W1), edge fibres: positivity along a fibre (tools for TB.W1fib-seg)

* `psd_cauchy`: `(uᵀMw)² ≤ (uᵀMu)(wᵀMw)` for `M ⪰ 0`.
* `sq_le_inv_diag_mul`: `x_i² ≤ (P⁻¹)_ii xᵀPx` for `P ≻ 0`.
* `posDef_add_edge`: `P + c(e_ie_jᵀ + e_je_iᵀ) ≻ 0` when `P ≻ 0` and `4c² (P⁻¹)_ii (P⁻¹)_jj < 1`.
* `posDef_precN_add_edge`: for the normalized precision, `P̃ + s τ a √(y_iy_j) E ≻ 0` when
  `|s| ≤ 3` and `|a| G_ii, |a| G_jj ≤ 1/64` (`G_kk = y_k (P̃⁻¹)_kk`).
-/

@[expose] public section

namespace BiluLinial.Tight.SecB

open Matrix

section Gen

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- Cauchy–Schwarz for a positive semidefinite form. -/
theorem psd_cauchy {M : Matrix n n ℝ} (hM : M.PosSemidef) (u w : n → ℝ) :
    (u ⬝ᵥ (M *ᵥ w)) ^ 2 ≤ (u ⬝ᵥ (M *ᵥ u)) * (w ⬝ᵥ (M *ᵥ w)) := by
  have hsym : ∀ k l, M k l = M l k := fun k l => by
    have := hM.1.apply k l
    simp only [star_trivial] at this
    exact this.symm
  have hswap : w ⬝ᵥ (M *ᵥ u) = u ⬝ᵥ (M *ᵥ w) := dotProduct_mulVec_swap hsym w u
  have hq : ∀ x : ℝ, 0 ≤ (w ⬝ᵥ (M *ᵥ w)) * (x * x) + (2 * (u ⬝ᵥ (M *ᵥ w))) * x +
      (u ⬝ᵥ (M *ᵥ u)) := by
    intro x
    have h := hM.dotProduct_mulVec_nonneg (u + x • w)
    simp only [star_trivial] at h
    have e : (u + x • w) ⬝ᵥ (M *ᵥ (u + x • w)) = (w ⬝ᵥ (M *ᵥ w)) * (x * x) +
        (2 * (u ⬝ᵥ (M *ᵥ w))) * x + (u ⬝ᵥ (M *ᵥ u)) := by
      simp only [mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
        smul_dotProduct, smul_eq_mul]
      rw [hswap]
      ring
    linarith
  have h := discrim_le_zero hq
  rw [discrim] at h
  linarith

/-- `x_i² ≤ (P⁻¹)_ii xᵀPx` for `P ≻ 0`. -/
theorem sq_le_inv_diag_mul {P : Matrix n n ℝ} (hP : P.PosDef) (x : n → ℝ) (i : n) :
    x i ^ 2 ≤ P⁻¹ i i * (x ⬝ᵥ (P *ᵥ x)) := by
  have hdet : IsUnit P.det := hP.det_pos.ne'.isUnit
  have h := psd_cauchy hP.inv.posSemidef (Pi.single i 1) (P *ᵥ x)
  have e1 : P⁻¹ *ᵥ (P *ᵥ x) = x := by
    rw [mulVec_mulVec, nonsing_inv_mul P hdet, one_mulVec]
  have e2 : Pi.single i 1 ⬝ᵥ (P⁻¹ *ᵥ Pi.single i 1) = P⁻¹ i i := by
    simp [dotProduct, mulVec, Pi.single_apply]
  rw [e1, e2] at h
  have e3 : Pi.single i (1 : ℝ) ⬝ᵥ x = x i := by simp [dotProduct, Pi.single_apply]
  rw [e3, dotProduct_comm (P *ᵥ x) x] at h
  exact h

omit [Fintype n] in
theorem edgeE_symm (i j k l : n) : SecA.edgeE i j k l = SecA.edgeE i j l k := by
  simp only [SecA.edgeE, Matrix.add_apply, Matrix.single_apply]
  rw [add_comm]
  congr 1 <;> simp only [and_comm]

theorem dotProduct_edgeE (i j : n) (x : n → ℝ) :
    x ⬝ᵥ (SecA.edgeE i j *ᵥ x) = 2 * (x i * x j) := by
  simp only [SecA.edgeE, add_mulVec, dotProduct_add]
  have h1 : ∀ a b : n, x ⬝ᵥ (Matrix.single a b (1 : ℝ) *ᵥ x) = x a * x b := fun a b => by
    simp [dotProduct, mulVec, Matrix.single_apply, ite_and]
  rw [h1, h1]
  ring

/-- A small symmetric rank-two edge perturbation keeps positive definiteness. -/
theorem posDef_add_edge {P : Matrix n n ℝ} (hP : P.PosDef) {i j : n} {c : ℝ}
    (hc : 4 * c ^ 2 * (P⁻¹ i i * P⁻¹ j j) < 1) : (P + c • SecA.edgeE i j).PosDef := by
  have hsymP : ∀ k l, P k l = P l k := fun k l => by
    have := hP.1.apply k l
    simp only [star_trivial] at this
    exact this.symm
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
  · refine Matrix.IsHermitian.ext fun k l => ?_
    simp only [star_trivial, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    rw [hsymP l k, edgeE_symm i j l k]
  · have hQ := hP.dotProduct_mulVec_pos hx
    simp only [star_trivial] at hQ ⊢
    rw [add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul, dotProduct_edgeE, smul_eq_mul]
    have hi := sq_le_inv_diag_mul hP x i
    have hj := sq_le_inv_diag_mul hP x j
    have hii : 0 ≤ P⁻¹ i i := hP.inv.posSemidef.diag_nonneg
    have hjj : 0 ≤ P⁻¹ j j := hP.inv.posSemidef.diag_nonneg
    have h2 : (c * (2 * (x i * x j))) ^ 2 < (x ⬝ᵥ (P *ᵥ x)) ^ 2 := by
      calc (c * (2 * (x i * x j))) ^ 2 = 4 * c ^ 2 * (x i ^ 2 * x j ^ 2) := by ring
        _ ≤ 4 * c ^ 2 * ((P⁻¹ i i * (x ⬝ᵥ (P *ᵥ x))) * (P⁻¹ j j * (x ⬝ᵥ (P *ᵥ x)))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul hi hj (sq_nonneg _) (mul_nonneg hii hQ.le))
              (by positivity)
        _ = (4 * c ^ 2 * (P⁻¹ i i * P⁻¹ j j)) * (x ⬝ᵥ (P *ᵥ x)) ^ 2 := by ring
        _ < 1 * (x ⬝ᵥ (P *ᵥ x)) ^ 2 := mul_lt_mul_of_pos_right hc (by positivity)
        _ = (x ⬝ᵥ (P *ᵥ x)) ^ 2 := one_mul _
    have h3 := abs_lt_of_sq_lt_sq h2 hQ.le
    have h4 := neg_abs_le (c * (2 * (x i * x j)))
    linarith

end Gen

section Prec

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- `P̃ + s τ a √(y_i y_j) E ≻ 0` for `|s| ≤ 3` when `|a| G_ii, |a| G_jj ≤ 1/64`. -/
theorem posDef_precN_add_edge {a τ : ℝ} (hτ : τ ^ 2 = 1) {y : V → ℝ} (hy : ∀ k, 0 ≤ y k)
    {σ : Config V} {S : Finset V} (hP : (precN G a τ y σ S).PosDef) {i j : V} {s : ℝ}
    (hs : |s| ≤ 3) (hgi : |a| * greenP G a τ y σ S i i ≤ 1 / 64)
    (hgj : |a| * greenP G a τ y σ S j j ≤ 1 / 64) :
    (precN G a τ y σ S +
      (s * (τ * a * (Real.sqrt (y i) * Real.sqrt (y j)))) • SecA.edgeE i j).PosDef := by
  refine posDef_add_edge hP ?_
  have hgi' : greenP G a τ y σ S i i = y i * (precN G a τ y σ S)⁻¹ i i :=
    greenP_diag G σ S (hy i)
  have hgj' : greenP G a τ y σ S j j = y j * (precN G a τ y σ S)⁻¹ j j :=
    greenP_diag G σ S (hy j)
  have hii : 0 ≤ (precN G a τ y σ S)⁻¹ i i := hP.inv.posSemidef.diag_nonneg
  have hjj : 0 ≤ (precN G a τ y σ S)⁻¹ j j := hP.inv.posSemidef.diag_nonneg
  have hsq : (s * (τ * a * (Real.sqrt (y i) * Real.sqrt (y j)))) ^ 2 =
      s ^ 2 * (|a| ^ 2 * (y i * y j)) := by
    have e1 : (Real.sqrt (y i) * Real.sqrt (y j)) ^ 2 = y i * y j := by
      rw [mul_pow, Real.sq_sqrt (hy i), Real.sq_sqrt (hy j)]
    have e2 : τ ^ 2 * a ^ 2 = |a| ^ 2 := by rw [hτ, one_mul, sq_abs]
    calc (s * (τ * a * (Real.sqrt (y i) * Real.sqrt (y j)))) ^ 2 =
        s ^ 2 * ((τ ^ 2 * a ^ 2) * (Real.sqrt (y i) * Real.sqrt (y j)) ^ 2) := by ring
      _ = s ^ 2 * (|a| ^ 2 * (y i * y j)) := by rw [e1, e2]
  rw [hsq]
  have h1 : 0 ≤ |a| * greenP G a τ y σ S i i :=
    mul_nonneg (abs_nonneg a) (by rw [hgi']; exact mul_nonneg (hy i) hii)
  have h2 : 0 ≤ |a| * greenP G a τ y σ S j j :=
    mul_nonneg (abs_nonneg a) (by rw [hgj']; exact mul_nonneg (hy j) hjj)
  have hX : (|a| * greenP G a τ y σ S i i) * (|a| * greenP G a τ y σ S j j) ≤
      1 / 64 * (1 / 64) := mul_le_mul hgi hgj h2 (by norm_num)
  have hs2 : s ^ 2 ≤ 9 := by
    have := sq_abs s
    nlinarith [abs_nonneg s]
  have hm := mul_le_mul hs2 hX (mul_nonneg h1 h2) (by norm_num : (0 : ℝ) ≤ 9)
  rw [hgi', hgj'] at hm
  nlinarith

end Prec

end BiluLinial.Tight.SecB
