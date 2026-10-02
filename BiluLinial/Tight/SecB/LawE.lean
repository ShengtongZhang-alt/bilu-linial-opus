/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecB.Defs
public import BiluLinial.Tight.SecA.Defs
public import BiluLinial.Tight.SourceMax.Law

/-!
# Elementary facts about the paired law and the shifted inverses

Helper lemmas for Section B (`docs/tight/BP_SECB.md`, node TB.law): monotonicity and constants of
`lawE` (linearity, `wt_nonneg`, `Zw_nonneg` are in `Tight/SourceMax/Law.lean`), positivity of the
precisions on the
support of the weight, the physical diagonals `G_ii = y_i h_i`, `X_ii = y_i hzN_i`, and the
Loewner fact `(A + D)⁻¹_ii ≤ A⁻¹_ii` for `A ≻ 0`, `D ⪰ 0` (so `X_ii ≤ G_ii` on the support).
-/

@[expose] public section

namespace BiluLinial.Tight.SecB

open Matrix

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable {p : ℕ} {a : ℝ} {yp ym : V → ℝ} {S : Finset V}

theorem posDef_of_wt_ne_zero {σ : Config V} (h : wt G p a yp ym σ S ≠ 0) :
    (precN G a 1 yp σ S).PosDef ∧ (precN G a (-1) ym σ S).PosDef := by
  unfold wt at h
  split_ifs at h with h'
  · exact h'
  · exact absurd rfl h

theorem lawE_const (hZ : Zw G p a yp ym S ≠ 0) (c : ℝ) :
    lawE G p a yp ym S (fun _ => c) = c := by
  unfold lawE
  rw [← Finset.sum_mul]
  exact mul_div_cancel_left₀ c hZ

theorem lawE_mono {f g : Config V → ℝ} (h : ∀ σ, wt G p a yp ym σ S ≠ 0 → f σ ≤ g σ) :
    lawE G p a yp ym S f ≤ lawE G p a yp ym S g := by
  unfold lawE
  refine div_le_div_of_nonneg_right (Finset.sum_le_sum fun σ _ => ?_) (Zw_nonneg G)
  by_cases hw : wt G p a yp ym σ S = 0
  · rw [hw, zero_mul, zero_mul]
  · exact mul_le_mul_of_nonneg_left (h σ hw) (wt_nonneg G σ)

/-! ### Physical diagonals -/

theorem greenP_diag {a τ : ℝ} {y : V → ℝ} (σ : Config V) (S : Finset V) {i : V} (hy : 0 ≤ y i) :
    greenP G a τ y σ S i i = y i * hN G a τ y σ S i := by
  unfold greenP hN
  rw [mul_comm (Real.sqrt (y i)) _, mul_assoc, Real.mul_self_sqrt hy, mul_comm]

theorem shiftP_diag {a τ z : ℝ} {y : V → ℝ} (σ : Config V) (S : Finset V) {i : V}
    (hy : 0 ≤ y i) : shiftP G a τ z y σ S i i = y i * hzN G a τ z y σ S i := by
  unfold shiftP hzN
  rw [mul_comm (Real.sqrt (y i)) _, mul_assoc, Real.mul_self_sqrt hy, mul_comm]

/-! ### Loewner monotonicity of the inverse diagonal -/

/-- `(A + D)⁻¹_ii ≤ A⁻¹_ii` for `A ≻ 0` and `D ⪰ 0`: indeed
`A⁻¹ - (A + D)⁻¹ = B⁻¹ (D + D A⁻¹ D) B⁻¹` with `B = A + D`. -/
theorem inv_diag_add_le {n : Type*} [Fintype n] [DecidableEq n] {A D : Matrix n n ℝ}
    (hA : A.PosDef) (hD : D.PosSemidef) (i : n) : (A + D)⁻¹ i i ≤ A⁻¹ i i := by
  have hB : (A + D).PosDef := hA.add_posSemidef hD
  have hAu : IsUnit A.det := isUnit_iff_ne_zero.mpr hA.det_pos.ne'
  have hBu : IsUnit (A + D).det := isUnit_iff_ne_zero.mpr hB.det_pos.ne'
  set B := A + D with hBdef
  set M := D + D * A⁻¹ * D with hMdef
  have hDh : Dᴴ = D := hD.1
  have hM : M.PosSemidef := by
    refine hD.add ?_
    have := hA.inv.posSemidef.conjTranspose_mul_mul_same D
    rwa [hDh] at this
  have hBinvh : (B⁻¹)ᴴ = B⁻¹ := hB.inv.1
  have hkey : A⁻¹ - B⁻¹ = B⁻¹ * M * B⁻¹ := by
    have e1 : M = D * A⁻¹ * B := by
      rw [hMdef, hBdef, Matrix.mul_add, Matrix.mul_assoc D A⁻¹ A, Matrix.nonsing_inv_mul A hAu,
        Matrix.mul_one, Matrix.mul_assoc]
    have e2 : A⁻¹ - B⁻¹ = B⁻¹ * D * A⁻¹ := by
      have h1 : A⁻¹ = B⁻¹ * B * A⁻¹ := by rw [Matrix.nonsing_inv_mul B hBu, Matrix.one_mul]
      have h2 : B⁻¹ = B⁻¹ * A * A⁻¹ := by
        rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv A hAu, Matrix.mul_one]
      calc A⁻¹ - B⁻¹ = B⁻¹ * B * A⁻¹ - B⁻¹ * A * A⁻¹ := by rw [← h1, ← h2]
        _ = B⁻¹ * (B - A) * A⁻¹ := by rw [Matrix.mul_sub, Matrix.sub_mul]
        _ = B⁻¹ * D * A⁻¹ := by rw [hBdef, add_sub_cancel_left]
    rw [e2, e1, Matrix.mul_assoc B⁻¹ (D * A⁻¹ * B) B⁻¹, Matrix.mul_assoc (D * A⁻¹) B B⁻¹,
      Matrix.mul_nonsing_inv B hBu, Matrix.mul_one, Matrix.mul_assoc]
  have hP : (B⁻¹ * M * B⁻¹).PosSemidef := by
    have := hM.conjTranspose_mul_mul_same B⁻¹
    rwa [hBinvh] at this
  have h0 : 0 ≤ (B⁻¹ * M * B⁻¹) i i := hP.diag_nonneg
  rw [← hkey] at h0
  simpa [Matrix.sub_apply] using h0

/-- On the support of the weight, the shifted normalized diagonal is at most the unshifted one:
`X_ii / y_i ≤ h_i` (for `z ≥ 0`, `y ≥ 0`). -/
theorem hzN_le_hN {a τ z : ℝ} {y : V → ℝ} {σ : Config V} (hP : (precN G a τ y σ S).PosDef)
    (hz : 0 ≤ z) (hy : ∀ k, 0 ≤ y k) (i : V) : hzN G a τ z y σ S i ≤ hN G a τ y σ S i := by
  have hD : (z • srcDiag y S).PosSemidef := by
    refine Matrix.PosSemidef.smul ?_ hz
    refine Matrix.PosSemidef.diagonal fun k => ?_
    split_ifs
    · exact hy k
    · exact le_rfl
  exact inv_diag_add_le hP hD i

/-- Physical inverse diagonals are nonnegative on the support. -/
theorem diag_nonneg_of_posDef {a τ z : ℝ} {y : V → ℝ} {σ : Config V}
    (hP : (precN G a τ y σ S).PosDef) (hy : ∀ k, 0 ≤ y k) (hz : 0 ≤ z) (k : V) :
    0 ≤ greenP G a τ y σ S k k ∧ 0 ≤ shiftP G a τ z y σ S k k := by
  have hD : (z • srcDiag y S).PosSemidef := by
    refine Matrix.PosSemidef.smul ?_ hz
    refine Matrix.PosSemidef.diagonal fun j => ?_
    split_ifs
    · exact hy j
    · exact le_rfl
  have hQ : (precN G a τ y σ S + z • srcDiag y S).PosDef := hP.add_posSemidef hD
  rw [greenP_diag G σ S (hy k), shiftP_diag G σ S (hy k)]
  exact ⟨mul_nonneg (hy k) hP.inv.posSemidef.diag_nonneg,
    mul_nonneg (hy k) hQ.inv.posSemidef.diag_nonneg⟩

end BiluLinial.Tight.SecB
