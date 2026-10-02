/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecA.Defs
public import BiluLinial.Tight.Tools.MatrixFacts

/-!
# The root Schur identity (node `A-SCHUR`)

Source (F1), lines 137–141, and its uses at lines 400–405 (C3), 547–559 (C5), 604 (the root
equation); `docs/tight/BP_SECA.md` (A-C3, A-C5b–g).

For a symmetric `Q` such that `Q` and its core `Q_c = coreOf Q v` (row and column `v` replaced by
those of the identity) are invertible, put `C = Q_c⁻¹`, `b = colOf Q v` (the column of `Q` at `v`,
with `b_v = 0`), `u = C b` and `s = Q_vv - bᵀu`. Then (`inv_eq_core_sub_add`)
`Q⁻¹ = C - e_v e_vᵀ + s⁻¹ (e_v - u)(e_v - u)ᵀ`; entrywise, `(Q⁻¹)_vv s = 1` (`inv_diag_core`),
`(Q⁻¹)_jv = -(Q⁻¹)_vv u_j` (`inv_apply_root_of_ne`) and `(Q⁻¹)_ij = C_ij + (Q⁻¹)_vv u_i u_j`
(`inv_apply_of_ne`) for `i, j ≠ v`; `C e_v = e_v` and `u_v = 0`. `coreOf`, `colOf`,
`inv_col_core`, `inv_diag_core` are copies of `SecC.coreOf`, `SecC.colOf`, `SecC.inv_col`,
`SecC.inv_diag` (`Tight/SecC/F1.lean`): importing `SecC.F1` would make Section 1.2 depend on
`SecC/Mark.lean`, which is under active development.

Also:
* `coreOf_posDef`: `Q ≻ 0 ⇒ Q_c ≻ 0` (through `vertexSchur`, `Common/Schur.lean`);
* `quad_inv_sub_inv_add_ge`: `z wᵀDw ≤ bᵀM⁻¹b - bᵀ(M + zD)⁻¹b` with `w = (M + zD)⁻¹b`, for
  `M ≻ 0`, `D ⪰ 0`, `z ≥ 0` (expand `b = Mw + zDw`; the defect is `z² (Dw)ᵀM⁻¹(Dw) ≥ 0`);
* graph glue: `precCore = coreOf precN`, `incCol = colOf precN`; the core of the shifted precision
  `P̃ + zY_S` is `P̃_core + zY_{S-v}`, with the same column (`coreOf_shift`, `colOf_shift`), and the
  packaged identities `precN_schur`, `shift_schur`.

Check (rule 2): the identity was tested numerically on 2000 random symmetric matrices of order
`≤ 6` (positive definite and indefinite), maximal error `2·10⁻¹²`, together with `C e_v = e_v`,
`u_v = 0`.
-/

@[expose] public section

namespace BiluLinial.Tight

open Matrix

namespace SecA

section Generic

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `Q` with row and column `v` replaced by those of the identity (`precCore` for `Q = P̃`; the
same matrix as `coreOf`). -/
def coreOf (Q : Matrix V V ℝ) (v : V) : Matrix V V ℝ :=
  Matrix.of fun u w => if u = v ∨ w = v then (if u = w then 1 else 0) else Q u w

/-- The column of `Q` at `v`, with `v` entry `0` (`incCol` for `Q = P̃`). -/
def colOf (Q : Matrix V V ℝ) (v : V) : V → ℝ := fun w => if w = v then 0 else Q w v

theorem sum_ite_zero_eq_sub (g : V → ℝ) (v : V) :
    ∑ l, (if l = v then 0 else g l) = ∑ l, g l - g v := by
  have h : ∀ l, g l = (if l = v then g l else 0) + (if l = v then 0 else g l) := fun l => by
    split_ifs <;> simp
  conv_rhs => rw [Finset.sum_congr rfl fun l _ => h l]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ v g]
  simp

/-- Column `j` of `Q⁻¹` off `v`, through the core: `(Q⁻¹_{lj})_{l ≠ v} = C (e_j' - Q⁻¹_vj b)`. -/
theorem inv_col_core {Q : Matrix V V ℝ} {v : V} (hQ : IsUnit Q.det) (hQc : IsUnit (coreOf Q v).det)
    (j : V) :
    (fun l => if l = v then 0 else Q⁻¹ l j) =
      (coreOf Q v)⁻¹ *ᵥ fun l => (if l = v then 0 else if l = j then 1 else 0) -
        Q⁻¹ v j * colOf Q v l := by
  have hmul : (coreOf Q v *ᵥ fun l => if l = v then 0 else Q⁻¹ l j) =
      fun l => (if l = v then 0 else if l = j then 1 else 0) - Q⁻¹ v j * colOf Q v l := by
    funext k
    have hQQ : ∑ l, Q k l * Q⁻¹ l j = if k = j then 1 else 0 := by
      have := congrFun (congrFun (Matrix.mul_nonsing_inv Q hQ) k) j
      rwa [mul_apply, one_apply] at this
    simp only [mulVec, dotProduct, coreOf, colOf, of_apply]
    by_cases hk : k = v
    · subst hk
      simp only [true_or, ite_true, mul_zero, sub_zero]
      refine Finset.sum_eq_zero fun l _ => ?_
      by_cases hl : l = k
      · simp [hl]
      · simp [hl, Ne.symm hl]
    · have e : ∀ l, (if k = v ∨ l = v then (if k = l then (1 : ℝ) else 0) else Q k l) *
          (if l = v then 0 else Q⁻¹ l j) = if l = v then 0 else Q k l * Q⁻¹ l j := by
        intro l
        by_cases hl : l = v
        · simp [hl]
        · simp [hk, hl]
      rw [Finset.sum_congr rfl fun l _ => e l, sum_ite_zero_eq_sub, hQQ, ite_eq_right hk,
        ite_eq_right hk]
      ring
  rw [← hmul, mulVec_mulVec, nonsing_inv_mul _ hQc, one_mulVec]

/-- The `(v, v)` entry of `Q⁻¹` through the core: `Q⁻¹_vv (Q_vv - bᵀ C b) = 1`. -/
theorem inv_diag_core {Q : Matrix V V ℝ} {v : V} (hsym : ∀ k l, Q k l = Q l k)
    (hQ : IsUnit Q.det) (hQc : IsUnit (coreOf Q v).det) :
    Q⁻¹ v v * (Q v v - colOf Q v ⬝ᵥ ((coreOf Q v)⁻¹ *ᵥ colOf Q v)) = 1 := by
  have hc := inv_col_core hQ hQc v
  have hr : (fun l => (if l = v then (0 : ℝ) else if l = v then 1 else 0) -
      Q⁻¹ v v * colOf Q v l) = (-Q⁻¹ v v) • colOf Q v := by
    funext l
    by_cases hl : l = v <;> simp [hl]
  rw [hr, mulVec_smul] at hc
  have hQQ : ∑ l, Q v l * Q⁻¹ l v = 1 := by
    have := congrFun (congrFun (Matrix.mul_nonsing_inv Q hQ) v) v
    rwa [mul_apply, one_apply, ite_eq_left rfl] at this
  have hsplit : ∑ l, Q v l * Q⁻¹ l v =
      Q v v * Q⁻¹ v v + colOf Q v ⬝ᵥ (fun l => if l = v then 0 else Q⁻¹ l v) := by
    have e : ∀ l, Q v l * Q⁻¹ l v =
        (if l = v then Q v v * Q⁻¹ v v else 0) + colOf Q v l * (if l = v then 0 else Q⁻¹ l v) := by
      intro l
      by_cases hl : l = v
      · subst hl; simp [colOf]
      · simp [hl, colOf, hsym v l]
    rw [Finset.sum_congr rfl fun l _ => e l, Finset.sum_add_distrib, Finset.sum_ite_eq']
    simp [dotProduct]
  rw [hc, dotProduct_smul, smul_eq_mul] at hsplit
  linarith

/-- Row `v` of the core inverse is `e_vᵀ`. -/
theorem coreOf_inv_apply_root_left {Q : Matrix V V ℝ} {v : V}
    (hQc : IsUnit (coreOf Q v).det) (j : V) :
    (coreOf Q v)⁻¹ v j = if v = j then 1 else 0 := by
  have h := congrFun (congrFun (Matrix.mul_nonsing_inv (coreOf Q v) hQc) v) j
  rw [mul_apply, one_apply, Finset.sum_eq_single v] at h
  · simpa [coreOf] using h
  · intro l _ hl
    simp [coreOf, Ne.symm hl]
  · simp

/-- Column `v` of the core inverse is `e_v`. -/
theorem coreOf_inv_apply_root_right {Q : Matrix V V ℝ} {v : V}
    (hQc : IsUnit (coreOf Q v).det) (i : V) :
    (coreOf Q v)⁻¹ i v = if i = v then 1 else 0 := by
  have h := congrFun (congrFun (Matrix.nonsing_inv_mul (coreOf Q v) hQc) i) v
  rw [mul_apply, one_apply, Finset.sum_eq_single v] at h
  · simpa [coreOf] using h
  · intro l _ hl
    simp [coreOf, hl]
  · simp

/-- `u_v = 0` for `u = (coreOf Q v)⁻¹ b`. -/
theorem coreOf_inv_mulVec_colOf_root {Q : Matrix V V ℝ} {v : V}
    (hQc : IsUnit (coreOf Q v).det) :
    ((coreOf Q v)⁻¹ *ᵥ colOf Q v) v = 0 := by
  simp only [mulVec, dotProduct]
  rw [Finset.sum_eq_single v]
  · simp [colOf]
  · intro l _ hl
    rw [coreOf_inv_apply_root_left hQc, ite_eq_right (Ne.symm hl), zero_mul]
  · simp

/-- The inverse of a symmetric matrix is symmetric. -/
theorem inv_apply_symm {Q : Matrix V V ℝ} (hsym : ∀ k l, Q k l = Q l k) (i j : V) :
    Q⁻¹ i j = Q⁻¹ j i := by
  have hQt : Qᵀ = Q := by
    ext k l
    exact hsym l k
  have h : (Q⁻¹)ᵀ = Q⁻¹ := by rw [Matrix.transpose_nonsing_inv, hQt]
  exact congrFun (congrFun h j) i

/-- The column at the root: `(Q⁻¹)_jv = -(Q⁻¹)_vv u_j` for `j ≠ v`. -/
theorem inv_apply_root_of_ne {Q : Matrix V V ℝ} {v : V} (hQ : IsUnit Q.det)
    (hQc : IsUnit (coreOf Q v).det) {j : V} (hj : j ≠ v) :
    Q⁻¹ j v = -(Q⁻¹ v v * ((coreOf Q v)⁻¹ *ᵥ colOf Q v) j) := by
  have h := congrFun (inv_col_core hQ hQc v) j
  simp only [hj, ite_false] at h
  rw [h]
  have hr : (fun l => (if l = v then (0 : ℝ) else if l = v then 1 else 0) -
      Q⁻¹ v v * colOf Q v l) = (-Q⁻¹ v v) • colOf Q v := by
    funext l
    by_cases hl : l = v
    · subst hl
      simp [colOf]
    · simp [hl]
  rw [hr, mulVec_smul, Pi.smul_apply, smul_eq_mul, neg_mul]

/-- The block off the root: `(Q⁻¹)_ij = C_ij + (Q⁻¹)_vv u_i u_j` for `i, j ≠ v`. -/
theorem inv_apply_of_ne {Q : Matrix V V ℝ} {v : V} (hsym : ∀ k l, Q k l = Q l k)
    (hQ : IsUnit Q.det) (hQc : IsUnit (coreOf Q v).det) {i j : V} (hi : i ≠ v)
    (hj : j ≠ v) :
    Q⁻¹ i j = (coreOf Q v)⁻¹ i j + Q⁻¹ v v * ((coreOf Q v)⁻¹ *ᵥ colOf Q v) i *
      ((coreOf Q v)⁻¹ *ᵥ colOf Q v) j := by
  have h := congrFun (inv_col_core hQ hQc j) i
  simp only [hi, ite_false] at h
  rw [h]
  have hr : (fun l => (if l = v then (0 : ℝ) else if l = j then 1 else 0) -
      Q⁻¹ v j * colOf Q v l) =
      (fun l => if l = j then 1 else 0) - (Q⁻¹ v j) • colOf Q v := by
    funext l
    by_cases hl : l = v
    · subst hl
      simp [Ne.symm hj, colOf]
    · simp [hl]
  rw [hr, mulVec_sub, mulVec_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    inv_apply_symm hsym v j, inv_apply_root_of_ne hQ hQc hj]
  have he : ((coreOf Q v)⁻¹ *ᵥ fun l => if l = j then (1 : ℝ) else 0) i =
      (coreOf Q v)⁻¹ i j := by
    simp [mulVec, dotProduct]
  rw [he]
  ring

/-- **A-SCHUR** (the root Schur identity). For symmetric `Q` with `Q` and its core invertible,
with `C = (coreOf Q v)⁻¹`, `b = colOf Q v`, `u = C b`, `s = Q_vv - bᵀu`:
`Q⁻¹ = C - e_v e_vᵀ + s⁻¹ (e_v - u)(e_v - u)ᵀ`. -/
theorem inv_eq_core_sub_add {Q : Matrix V V ℝ} {v : V} (hsym : ∀ k l, Q k l = Q l k)
    (hQ : IsUnit Q.det) (hQc : IsUnit (coreOf Q v).det) :
    Q⁻¹ = (coreOf Q v)⁻¹ - single v v 1 +
      (Q v v - colOf Q v ⬝ᵥ ((coreOf Q v)⁻¹ *ᵥ colOf Q v))⁻¹ •
        vecMulVec (Pi.single v (1 : ℝ) - (coreOf Q v)⁻¹ *ᵥ colOf Q v)
          (Pi.single v (1 : ℝ) - (coreOf Q v)⁻¹ *ᵥ colOf Q v) := by
  have hs := inv_diag_core hsym hQ hQc
  have hg : Q⁻¹ v v =
      (Q v v - colOf Q v ⬝ᵥ ((coreOf Q v)⁻¹ *ᵥ colOf Q v))⁻¹ :=
    eq_inv_of_mul_eq_one_left hs
  have huv := coreOf_inv_mulVec_colOf_root hQc
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply,
    Pi.sub_apply, smul_eq_mul]
  by_cases hi : i = v <;> by_cases hj : j = v
  · rw [hi, hj, coreOf_inv_apply_root_left hQc, ite_eq_left rfl, single_apply_same,
      Pi.single_eq_same, huv, ← hg]
    ring
  · rw [hi, inv_apply_symm hsym v j, inv_apply_root_of_ne hQ hQc hj,
      coreOf_inv_apply_root_left hQc, ← hg]
    simp only [Ne.symm hj, ite_false, single_apply_of_col_ne v v (Ne.symm hj) (1 : ℝ),
      Pi.single_eq_same, Pi.single_eq_of_ne hj, huv]
    ring
  · rw [hj, inv_apply_root_of_ne hQ hQc hi, coreOf_inv_apply_root_right hQc, ← hg]
    simp only [hi, ite_false, single_apply_of_row_ne (Ne.symm hi) v v (1 : ℝ),
      Pi.single_eq_of_ne hi, Pi.single_eq_same, huv]
    ring
  · rw [inv_apply_of_ne hsym hQ hQc hi hj, single_apply_of_row_ne (Ne.symm hi) v j (1 : ℝ),
      Pi.single_eq_of_ne hi, Pi.single_eq_of_ne hj, ← hg]
    ring

/-- The entrywise identities, packaged for a positive definite `Q`. -/
theorem schur_of_posDef {Q : Matrix V V ℝ} {v : V} (hQ : Q.PosDef)
    (hQc : (coreOf Q v).PosDef) :
    Q⁻¹ v v * (Q v v - colOf Q v ⬝ᵥ ((coreOf Q v)⁻¹ *ᵥ colOf Q v)) = 1 ∧
      (∀ j, j ≠ v → Q⁻¹ v j = -(Q⁻¹ v v * ((coreOf Q v)⁻¹ *ᵥ colOf Q v) j)) ∧
      ∀ i j, i ≠ v → j ≠ v → Q⁻¹ i j = (coreOf Q v)⁻¹ i j +
        Q⁻¹ v v * ((coreOf Q v)⁻¹ *ᵥ colOf Q v) i *
          ((coreOf Q v)⁻¹ *ᵥ colOf Q v) j := by
  have hsym : ∀ k l, Q k l = Q l k := fun k l => by simpa using hQ.isHermitian.apply l k
  have hQu : IsUnit Q.det := (isUnit_iff_isUnit_det _).mp hQ.isUnit
  have hQcu : IsUnit (coreOf Q v).det := (isUnit_iff_isUnit_det _).mp hQc.isUnit
  refine ⟨inv_diag_core hsym hQu hQcu, fun j hj => ?_,
    fun i j hi hj => inv_apply_of_ne hsym hQu hQcu hi hj⟩
  rw [inv_apply_symm hsym]
  exact inv_apply_root_of_ne hQu hQcu hj

omit [Fintype V] in
theorem coreOf_isHermitian {Q : Matrix V V ℝ} (hQ : Q.IsHermitian) (v : V) :
    (coreOf Q v).IsHermitian := by
  refine IsHermitian.ext fun i j => ?_
  have h : Q j i = Q i j := by simpa using hQ.apply i j
  simp only [coreOf, of_apply, star_trivial]
  by_cases hij : i = j
  · subst hij
    rfl
  · rw [ite_eq_right (Ne.symm hij), ite_eq_right hij, h]
    split_ifs <;> first | rfl | (exfalso; tauto)

omit [Fintype V] in
theorem delVertex_coreOf (Q : Matrix V V ℝ) (v : V) :
    delVertex (coreOf Q v) v = delVertex Q v := by
  ext ⟨a, ha⟩ ⟨b, hb⟩
  simp [delVertex, coreOf, ha, hb]

theorem vertexSchur_coreOf (Q : Matrix V V ℝ) (v : V) : vertexSchur (coreOf Q v) v = 1 := by
  have h1 : coreOf Q v v v = 1 := by simp [coreOf]
  have h2 : (fun w : {w // w ≠ v} => coreOf Q v w v) = 0 := by
    funext w
    simp [coreOf, w.2]
  rw [vertexSchur, h1, h2]
  simp

/-- `Q ≻ 0 ⇒ coreOf Q v ≻ 0`. -/
theorem coreOf_posDef {Q : Matrix V V ℝ} (hQ : Q.PosDef) (v : V) : (coreOf Q v).PosDef := by
  have hD : (delVertex (coreOf Q v) v).PosDef := by
    rw [delVertex_coreOf]
    exact hQ.submatrix Subtype.val_injective
  rw [vertexSchur_posDef_iff (coreOf_isHermitian hQ.isHermitian v) hD, vertexSchur_coreOf]
  exact one_pos

end Generic

section Quad

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `z wᵀDw ≤ bᵀM⁻¹b - bᵀ(M + zD)⁻¹b` with `w = (M + zD)⁻¹ b` (`M ≻ 0`, `D ⪰ 0`, `z ≥ 0`), i.e.
`M⁻¹ - (M + zD)⁻¹ ⪰ z (M + zD)⁻¹ D (M + zD)⁻¹`. -/
theorem quad_inv_sub_inv_add_ge {M D : Matrix ι ι ℝ} (hM : M.PosDef) (hD : D.PosSemidef) {z : ℝ}
    (hz : 0 ≤ z) (b : ι → ℝ) :
    z * (((M + z • D)⁻¹ *ᵥ b) ⬝ᵥ (D *ᵥ ((M + z • D)⁻¹ *ᵥ b))) ≤
      b ⬝ᵥ (M⁻¹ *ᵥ b) - b ⬝ᵥ ((M + z • D)⁻¹ *ᵥ b) := by
  have hQ : (M + z • D).PosDef := hM.add_posSemidef (hD.smul hz)
  have hMu : IsUnit M.det := (isUnit_iff_isUnit_det _).mp hM.isUnit
  have hQu : IsUnit (M + z • D).det := (isUnit_iff_isUnit_det _).mp hQ.isUnit
  obtain ⟨w, hw⟩ : ∃ w, w = (M + z • D)⁻¹ *ᵥ b := ⟨_, rfl⟩
  rw [← hw]
  have hb : b = M *ᵥ w + z • (D *ᵥ w) := by
    rw [← smul_mulVec, ← add_mulVec, hw, mulVec_mulVec, Matrix.mul_nonsing_inv _ hQu,
      one_mulVec]
  have e1 : b ⬝ᵥ w = w ⬝ᵥ (M *ᵥ w) + z * (w ⬝ᵥ (D *ᵥ w)) := by
    rw [hb, add_dotProduct, smul_dotProduct, smul_eq_mul, dotProduct_comm (M *ᵥ w),
      dotProduct_comm (D *ᵥ w)]
  have h2 : (M *ᵥ w) ⬝ᵥ (M⁻¹ *ᵥ (D *ᵥ w)) = w ⬝ᵥ (D *ᵥ w) := by
    rw [← dotProduct_mulVec_comm_of_symm hM.isHermitian, mulVec_mulVec,
      Matrix.mul_nonsing_inv _ hMu, one_mulVec]
  have hMinv : M⁻¹ *ᵥ (M *ᵥ w) = w := by
    rw [mulVec_mulVec, Matrix.nonsing_inv_mul _ hMu, one_mulVec]
  have e2 : b ⬝ᵥ (M⁻¹ *ᵥ b) = w ⬝ᵥ (M *ᵥ w) + 2 * z * (w ⬝ᵥ (D *ᵥ w)) +
      z ^ 2 * ((D *ᵥ w) ⬝ᵥ (M⁻¹ *ᵥ (D *ᵥ w))) := by
    rw [hb, mulVec_add, mulVec_smul, hMinv]
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [h2, dotProduct_comm (M *ᵥ w), dotProduct_comm (D *ᵥ w) w]
    ring
  have h3 : 0 ≤ (D *ᵥ w) ⬝ᵥ (M⁻¹ *ᵥ (D *ᵥ w)) := by
    have := hM.inv.posSemidef.dotProduct_mulVec_nonneg (D *ᵥ w)
    rwa [star_trivial] at this
  rw [e1, e2]
  nlinarith [mul_nonneg (sq_nonneg z) h3]

end Quad

section Graph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

omit [Fintype V] in
theorem precCore_eq_coreOf (a τ : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) (v : V) :
    precCore G a τ y σ S v = coreOf (precN G a τ y σ S) v := rfl

omit [Fintype V] in
theorem incCol_eq_colOf (a τ : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) (v : V) :
    incCol G a τ y σ S v = colOf (precN G a τ y σ S) v := rfl

theorem precCore_posDef_of_precN {a τ : ℝ} {y : V → ℝ} {σ : Config V} {S : Finset V} {v : V}
    (hP : (precN G a τ y σ S).PosDef) : (precCore G a τ y σ S v).PosDef :=
  coreOf_posDef hP v

omit [Fintype V] in
theorem precN_apply_root (a τ : ℝ) (y : V → ℝ) (σ : Config V) {S : Finset V} {v : V}
    (hv : v ∈ S) : precN G a τ y σ S v v = diagD G a y S v := by
  simp [precN, hv]

omit [Fintype V] in
/-- The core of the shifted precision `P̃ + z Y_S` is `P̃_core + z Y_{S-v}`. -/
theorem coreOf_shift (a τ z : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) (v : V) :
    coreOf (precN G a τ y σ S + z • srcDiag y S) v =
      precCore G a τ y σ S v + z • srcDiag y (S.erase v) := by
  ext k l
  simp only [coreOf, precCore, Matrix.add_apply, Matrix.smul_apply, of_apply, srcDiag,
    diagonal_apply, smul_eq_mul, Finset.mem_erase]
  split_ifs <;> simp_all

omit [Fintype V] in
/-- The shifted precision has the same column at the root. -/
theorem colOf_shift (a τ z : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) (v : V) :
    colOf (precN G a τ y σ S + z • srcDiag y S) v = incCol G a τ y σ S v := by
  funext w
  by_cases hw : w = v
  · simp [colOf, incCol, hw]
  · simp [colOf, incCol, hw, srcDiag]

omit [Fintype V] in
theorem shift_apply_root (a τ z : ℝ) (y : V → ℝ) (σ : Config V) {S : Finset V} {v : V}
    (hv : v ∈ S) :
    (precN G a τ y σ S + z • srcDiag y S) v v = diagD G a y S v + z * y v := by
  simp [precN, srcDiag, hv]

theorem sqrt_mul_le_sqrt_mul_add (x c g u : ℝ) (hg : 0 ≤ g) :
    Real.sqrt x * c * Real.sqrt x ≤ Real.sqrt x * (c + g * u * u) * Real.sqrt x := by
  nlinarith [mul_nonneg (mul_self_nonneg (Real.sqrt x)) (mul_nonneg hg (mul_self_nonneg u))]

theorem srcDiag_posSemidef {y : V → ℝ} (hy : ∀ i, 0 ≤ y i) (S : Finset V) :
    (srcDiag y S).PosSemidef := by
  refine Matrix.PosSemidef.diagonal fun k => ?_
  split_ifs
  · exact hy k
  · exact le_rfl

/-- The root Schur identities of `P̃` (`P̃ ≻ 0`): with `g = (P̃⁻¹)_vv`, `b = incCol`,
`u = P̃_core⁻¹ b`: `g (D_v - bᵀu) = 1`, `(P̃⁻¹)_vj = -g u_j` (`j ≠ v`) and `(P̃⁻¹)_ij = (P̃_core⁻¹)_ij + g u_i u_j` (`i, j ≠ v`). -/
theorem precN_schur {a τ : ℝ} {y : V → ℝ} {σ : Config V} {S : Finset V} {v : V} (hv : v ∈ S)
    (hP : (precN G a τ y σ S).PosDef) :
    (precN G a τ y σ S)⁻¹ v v * (diagD G a y S v - incCol G a τ y σ S v ⬝ᵥ
        ((precCore G a τ y σ S v)⁻¹ *ᵥ incCol G a τ y σ S v)) = 1 ∧
      (∀ j, j ≠ v → (precN G a τ y σ S)⁻¹ v j = -((precN G a τ y σ S)⁻¹ v v *
        ((precCore G a τ y σ S v)⁻¹ *ᵥ incCol G a τ y σ S v) j)) ∧
      ∀ i j, i ≠ v → j ≠ v → (precN G a τ y σ S)⁻¹ i j = (precCore G a τ y σ S v)⁻¹ i j +
        (precN G a τ y σ S)⁻¹ v v * ((precCore G a τ y σ S v)⁻¹ *ᵥ incCol G a τ y σ S v) i *
          ((precCore G a τ y σ S v)⁻¹ *ᵥ incCol G a τ y σ S v) j := by
  have h := schur_of_posDef hP (coreOf_posDef hP v)
  rw [← precCore_eq_coreOf, ← incCol_eq_colOf, precN_apply_root G a τ y σ hv] at h
  exact h

/-- The root Schur identities of the shifted precision `Q = P̃ + z Y_S` (`Q ≻ 0`): with
`g = (Q⁻¹)_vv`, `b = incCol`, `K_z = (P̃_core + z Y_{S-v})⁻¹`, `u = K_z b`:
`g (D_v + z y_v - bᵀu) = 1`, `(Q⁻¹)_vj = -g u_j` (`j ≠ v`) and `(Q⁻¹)_ij = (K_z)_ij + g u_i u_j` (`i, j ≠ v`). -/
theorem shift_schur {a τ z : ℝ} {y : V → ℝ} {σ : Config V} {S : Finset V} {v : V} (hv : v ∈ S)
    (hQ : (precN G a τ y σ S + z • srcDiag y S).PosDef) :
    (precN G a τ y σ S + z • srcDiag y S)⁻¹ v v *
        (diagD G a y S v + z * y v - incCol G a τ y σ S v ⬝ᵥ
          ((precCore G a τ y σ S v + z • srcDiag y (S.erase v))⁻¹ *ᵥ incCol G a τ y σ S v)) = 1 ∧
      (∀ j, j ≠ v → (precN G a τ y σ S + z • srcDiag y S)⁻¹ v j =
        -((precN G a τ y σ S + z • srcDiag y S)⁻¹ v v *
          ((precCore G a τ y σ S v + z • srcDiag y (S.erase v))⁻¹ *ᵥ
            incCol G a τ y σ S v) j)) ∧
      ∀ i j, i ≠ v → j ≠ v → (precN G a τ y σ S + z • srcDiag y S)⁻¹ i j =
        (precCore G a τ y σ S v + z • srcDiag y (S.erase v))⁻¹ i j +
          (precN G a τ y σ S + z • srcDiag y S)⁻¹ v v *
            ((precCore G a τ y σ S v + z • srcDiag y (S.erase v))⁻¹ *ᵥ
              incCol G a τ y σ S v) i *
            ((precCore G a τ y σ S v + z • srcDiag y (S.erase v))⁻¹ *ᵥ
              incCol G a τ y σ S v) j := by
  have h := schur_of_posDef hQ (coreOf_posDef hQ v)
  rw [coreOf_shift, colOf_shift, shift_apply_root G a τ z y σ hv] at h
  exact h

end Graph

end SecA

end BiluLinial.Tight
