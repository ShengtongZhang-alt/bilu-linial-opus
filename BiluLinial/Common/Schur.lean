/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.ChallengeDefs

/-!
# Schur complements of real symmetric block matrices

Blueprint nodes `C-schur` (block form) and `C-vschur` (one vertex of an ambient index type).

For `M = [[A, B], [Bᵀ, D]]` with `D ≻ 0` and Schur complement `A - B D⁻¹ Bᵀ`:
`M ≻ 0 ↔ A - B D⁻¹ Bᵀ ≻ 0`, `M ⪰ 0 ↔ A - B D⁻¹ Bᵀ ⪰ 0`, `det M = det D · det(A - B D⁻¹ Bᵀ)`, and
if `M ≻ 0` the upper-left block of `M⁻¹` is `(A - B D⁻¹ Bᵀ)⁻¹`.
-/

@[expose] public section

namespace BiluLinial

open Matrix

section Block

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

theorem schur_posSemidef_iff (A : Matrix m m ℝ) (B : Matrix m n ℝ)
    {D : Matrix n n ℝ} (hD : D.PosDef) :
    (fromBlocks A B Bᵀ D).PosSemidef ↔ (A - B * D⁻¹ * Bᵀ).PosSemidef := by
  let := hD.isUnit.invertible
  have h := PosDef.fromBlocks₂₂ A B hD
  rw [conjTranspose_eq_transpose_of_trivial] at h
  exact h

theorem schur_det (A : Matrix m m ℝ) (B : Matrix m n ℝ) {D : Matrix n n ℝ} (hD : D.PosDef) :
    (fromBlocks A B Bᵀ D).det = D.det * (A - B * D⁻¹ * Bᵀ).det := by
  let := hD.isUnit.invertible
  rw [det_fromBlocks₂₂, invOf_eq_nonsing_inv]

theorem schur_posDef_iff {A : Matrix m m ℝ} (hA : A.IsHermitian) (B : Matrix m n ℝ)
    {D : Matrix n n ℝ} (hD : D.PosDef) :
    (fromBlocks A B Bᵀ D).PosDef ↔ (A - B * D⁻¹ * Bᵀ).PosDef := by
  constructor
  · intro h
    have hS := (schur_posSemidef_iff A B hD).1 h.posSemidef
    rw [hS.posDef_iff_det_ne_zero]
    intro h0
    have := h.det_pos
    rw [schur_det A B hD, h0, mul_zero] at this
    exact lt_irrefl _ this
  · intro h
    have hM := (schur_posSemidef_iff A B hD).2 h.posSemidef
    rw [hM.posDef_iff_det_ne_zero, schur_det A B hD]
    exact mul_ne_zero hD.det_pos.ne' h.det_pos.ne'

theorem schur_inv_toBlocks₁₁ {A : Matrix m m ℝ} (hA : A.IsHermitian) (B : Matrix m n ℝ)
    {D : Matrix n n ℝ} (hD : D.PosDef) (hM : (fromBlocks A B Bᵀ D).PosDef) :
    (fromBlocks A B Bᵀ D)⁻¹.toBlocks₁₁ = (A - B * D⁻¹ * Bᵀ)⁻¹ := by
  let := hD.isUnit.invertible
  have hS : IsUnit (A - B * ⅟D * Bᵀ) := by
    rw [invOf_eq_nonsing_inv]
    exact ((schur_posDef_iff hA B hD).1 hM).isUnit
  let := hS.invertible
  let := hM.isUnit.invertible
  rw [← invOf_eq_nonsing_inv (fromBlocks A B Bᵀ D), invOf_fromBlocks₂₂_eq A B Bᵀ D,
    toBlocks_fromBlocks₁₁, invOf_eq_nonsing_inv (A - B * ⅟D * Bᵀ), invOf_eq_nonsing_inv D]

end Block

section Vertex

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The principal submatrix of `M` on the vertices other than `v`. -/
def delVertex (M : Matrix V V ℝ) (v : V) : Matrix {w // w ≠ v} {w // w ≠ v} ℝ :=
  M.submatrix Subtype.val Subtype.val

/-- The Schur complement `M_vv - bᵀ D⁻¹ b` of `M` at the vertex `v`, where `D = delVertex M v` and
`b = (M w v)_{w ≠ v}`. -/
noncomputable def vertexSchur (M : Matrix V V ℝ) (v : V) : ℝ :=
  M v v - (fun w : {w // w ≠ v} => M w v) ⬝ᵥ ((delVertex M v)⁻¹ *ᵥ fun w => M w v)

/-- `Unit ⊕ {w // w ≠ v} ≃ V`, sending `inl ()` to `v`. -/
private def vertexEquiv (v : V) : Unit ⊕ {w // w ≠ v} ≃ V where
  toFun := Sum.elim (fun _ => v) Subtype.val
  invFun w := if h : w = v then Sum.inl () else Sum.inr ⟨w, h⟩
  left_inv := by
    rintro (⟨⟩ | ⟨w, hw⟩)
    · simp
    · simp [hw]
  right_inv w := by
    by_cases h : w = v
    · simp [h]
    · simp [h]

/-- The `1 × 1` block `M v v`. -/
private def vA (M : Matrix V V ℝ) (v : V) : Matrix Unit Unit ℝ := of fun _ _ => M v v

/-- The off-diagonal block `(M w v)_{w ≠ v}`, as a row. -/
private def vB (M : Matrix V V ℝ) (v : V) : Matrix Unit {w // w ≠ v} ℝ := of fun _ w => M w v

omit [Fintype V] [DecidableEq V] in
private lemma vA_isHermitian (M : Matrix V V ℝ) (v : V) : (vA M v).IsHermitian :=
  IsHermitian.ext fun _ _ => star_trivial _

omit [Fintype V] in
private lemma submatrix_vertexEquiv {M : Matrix V V ℝ} (hM : M.IsHermitian) (v : V) :
    M.submatrix (vertexEquiv v) (vertexEquiv v) =
      fromBlocks (vA M v) (vB M v) (vB M v)ᵀ (delVertex M v) := by
  have hs : ∀ i j, M i j = M j i := fun i j => by simpa using hM.apply j i
  ext (⟨⟩ | i) (⟨⟩ | j)
  · rfl
  · exact hs v j
  · rfl
  · rfl

private lemma schur_entry (M : Matrix V V ℝ) (v : V) (i j : Unit) :
    (vA M v - vB M v * (delVertex M v)⁻¹ * (vB M v)ᵀ) i j = vertexSchur M v := by
  simp only [vertexSchur, vA, vB, Matrix.sub_apply, mul_apply, transpose_apply, of_apply,
    dotProduct, mulVec, Finset.sum_mul, Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

private lemma unit_eq_diagonal (S : Matrix Unit Unit ℝ) : S = diagonal fun _ => S () () := by
  ext ⟨⟩ ⟨⟩
  simp

private lemma unit_posDef_iff (S : Matrix Unit Unit ℝ) : S.PosDef ↔ 0 < S () () := by
  rw [unit_eq_diagonal S]
  simp

private lemma unit_posSemidef_iff (S : Matrix Unit Unit ℝ) : S.PosSemidef ↔ 0 ≤ S () () := by
  rw [unit_eq_diagonal S]
  simp

private lemma unit_inv_apply (S : Matrix Unit Unit ℝ) : S⁻¹ () () = 1 / S () () := by
  rw [inv_subsingleton]
  simp [Ring.inverse_eq_inv']

private lemma posDef_submatrix_equiv_iff {m n : Type*} (M : Matrix n n ℝ) (e : m ≃ n) :
    (M.submatrix e e).PosDef ↔ M.PosDef :=
  ⟨fun h => by simpa using h.submatrix e.symm.injective, fun h => h.submatrix e.injective⟩

variable {M : Matrix V V ℝ} {v : V}

theorem vertexSchur_posDef_iff (hM : M.IsHermitian) (hD : (delVertex M v).PosDef) :
    M.PosDef ↔ 0 < vertexSchur M v := by
  rw [← posDef_submatrix_equiv_iff M (vertexEquiv v), submatrix_vertexEquiv hM,
    schur_posDef_iff (vA_isHermitian M v) _ hD, unit_posDef_iff, schur_entry]

theorem vertexSchur_posSemidef_iff (hM : M.IsHermitian) (hD : (delVertex M v).PosDef) :
    M.PosSemidef ↔ 0 ≤ vertexSchur M v := by
  rw [← posSemidef_submatrix_equiv (vertexEquiv v), submatrix_vertexEquiv hM,
    schur_posSemidef_iff _ _ hD, unit_posSemidef_iff, schur_entry]

theorem vertexSchur_det (hM : M.IsHermitian) (hD : (delVertex M v).PosDef) :
    M.det = (delVertex M v).det * vertexSchur M v := by
  rw [← det_submatrix_equiv_self (vertexEquiv v) M, submatrix_vertexEquiv hM, schur_det _ _ hD,
    det_unique (vA M v - vB M v * (delVertex M v)⁻¹ * (vB M v)ᵀ), schur_entry]

theorem vertexSchur_inv_apply (hM : M.IsHermitian) (hD : (delVertex M v).PosDef)
    (hMpos : M.PosDef) : M⁻¹ v v = 1 / vertexSchur M v := by
  have hN := hMpos.submatrix (vertexEquiv v).injective
  rw [submatrix_vertexEquiv hM] at hN
  have key := congrFun (congrFun (schur_inv_toBlocks₁₁ (vA_isHermitian M v) _ hD hN) ()) ()
  rw [unit_inv_apply, schur_entry] at key
  have h1 :
      M⁻¹ v v = (M.submatrix (vertexEquiv v) (vertexEquiv v))⁻¹ (Sum.inl ()) (Sum.inl ()) := by
    rw [inv_submatrix_equiv]
    rfl
  rw [h1, submatrix_vertexEquiv hM]
  exact key

end Vertex

end BiluLinial
