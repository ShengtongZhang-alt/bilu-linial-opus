/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Counterexample.Defs
public import BiluLinial.Common.Schur

/-!
# Schur complement onto the core of an attach-type block matrix

Blueprint node `B-attach-schur` (Xu Lemma 3.1 specialized to pendant blocks; source Step 1).

A matrix `N = [[P, B], [Bᵀ, blockDiagonal D]]` on `K ⊕ (W × ι)`, where the coupling `B` has the
entry `s i` (`s i ^ 2 = 1`) between the core vertex `att i` and the vertex `o` of block `i` and
zero elsewhere, and every block `D i` is positive definite. Its Schur complement onto `K` is
`P - diag_c (∑_{i : att i = c} (D i)⁻¹_{oo})`.
-/

@[expose] public section

namespace BiluLinial.Counterexample

open Matrix

variable {K W ι : Type*} [Fintype K] [DecidableEq K] [Fintype W] [DecidableEq W] [Fintype ι]
  [DecidableEq ι]

/-- The Schur complement onto the core: `P - diag_c (∑_{i : att i = c} (D i)⁻¹_{oo})`. -/
noncomputable def attachCompl (P : Matrix K K ℝ) (o : W) (att : ι → K) (D : ι → Matrix W W ℝ) :
    Matrix K K ℝ :=
  P - diagonal fun c => ∑ i ∈ Finset.univ.filter (fun i => att i = c), (D i)⁻¹ o o

omit [DecidableEq W] in
private lemma posDef_blockDiagonal {D : ι → Matrix W W ℝ} (hD : ∀ i, (D i).PosDef) :
    (blockDiagonal D).PosDef := by
  refine PosDef.of_dotProduct_mulVec_pos
    (isHermitian_blockDiagonal_iff.2 fun i => (hD i).isHermitian) fun x hx => ?_
  have key : star x ⬝ᵥ (blockDiagonal D *ᵥ x) =
      ∑ i, star (fun w => x (w, i)) ⬝ᵥ (D i *ᵥ fun w => x (w, i)) := by
    simp only [dotProduct, mulVec, blockDiagonal_apply, Fintype.sum_prod_type, Pi.star_apply,
      ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    exact Finset.sum_comm
  rw [key]
  obtain ⟨⟨w, i⟩, hwi⟩ : ∃ p, x p ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (funext h)
  have hne : (fun w => x (w, i)) ≠ 0 := fun h => hwi (congrFun h w)
  exact Finset.sum_pos' (fun j _ => (hD j).posSemidef.dotProduct_mulVec_nonneg _)
    ⟨i, Finset.mem_univ _, (hD i).dotProduct_mulVec_pos hne⟩

private lemma inv_blockDiagonal {D : ι → Matrix W W ℝ} (hD : ∀ i, (D i).PosDef) :
    (blockDiagonal D)⁻¹ = blockDiagonal fun i => (D i)⁻¹ := by
  refine inv_eq_right_inv ?_
  rw [← blockDiagonal_mul]
  have h : (fun i => D i * (D i)⁻¹) = 1 :=
    funext fun i => mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (hD i).det_pos.ne')
  rw [h, blockDiagonal_one]

omit [Fintype K] in
private lemma couple_mul_blockDiagonal_apply (o : W) (att : ι → K) (s : ι → ℝ)
    (E : ι → Matrix W W ℝ) (c : K) (w' : W) (i' : ι) :
    (couple o att s * blockDiagonal E) c (w', i') =
      if att i' = c then s i' * E i' o w' else 0 := by
  rw [mul_apply, Fintype.sum_eq_single (o, i')]
  · simp [couple, blockDiagonal_apply, ite_mul]
  · rintro ⟨w, i⟩ h
    simp only [couple, of_apply, blockDiagonal_apply]
    by_cases h2 : i = i'
    · subst h2
      have h1 : w ≠ o := fun h1 => h (by rw [h1])
      simp [h1]
    · simp [h2]

omit [Fintype K] in
private lemma couple_mul_blockDiagonal_mul (o : W) (att : ι → K) {s : ι → ℝ}
    (hs : ∀ i, s i ^ 2 = 1) (E : ι → Matrix W W ℝ) :
    couple o att s * blockDiagonal E * (couple o att s)ᵀ =
      diagonal fun c => ∑ i ∈ Finset.univ.filter (fun i => att i = c), E i o o := by
  ext c c'
  rw [mul_apply, Fintype.sum_prod_type]
  simp only [couple_mul_blockDiagonal_apply]
  simp only [transpose_apply, couple, of_apply]
  rw [Finset.sum_eq_single o]
  · by_cases hcc : c = c'
    · subst hcc
      rw [diagonal_apply_eq, Finset.sum_filter]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases h : att i = c
      · simp only [h, and_self, ↓reduceIte]
        linear_combination E i o o * hs i
      · simp [h]
    · rw [diagonal_apply_ne _ hcc]
      refine Finset.sum_eq_zero fun i _ => ?_
      by_cases h : att i = c
      · have h' : att i ≠ c' := fun h' => hcc (h.symm.trans h')
        simp [h']
      · simp [h]
  · intro w _ hw
    refine Finset.sum_eq_zero fun i _ => ?_
    simp [hw]
  · intro h
    exact absurd (Finset.mem_univ o) h

omit [Fintype K] in
private lemma schur_eq_attachCompl (P : Matrix K K ℝ) (o : W) (att : ι → K) {s : ι → ℝ}
    (hs : ∀ i, s i ^ 2 = 1) {D : ι → Matrix W W ℝ} (hD : ∀ i, (D i).PosDef) :
    P - couple o att s * (blockDiagonal D)⁻¹ * (couple o att s)ᵀ = attachCompl P o att D := by
  rw [inv_blockDiagonal hD, couple_mul_blockDiagonal_mul o att hs]
  rfl

theorem attach_posDef_iff {P : Matrix K K ℝ} (hP : P.IsHermitian) (o : W) (att : ι → K)
    {s : ι → ℝ} (hs : ∀ i, s i ^ 2 = 1) {D : ι → Matrix W W ℝ} (hD : ∀ i, (D i).PosDef) :
    (fromBlocks P (couple o att s) (couple o att s)ᵀ (blockDiagonal D)).PosDef ↔
      (attachCompl P o att D).PosDef := by
  rw [schur_posDef_iff hP _ (posDef_blockDiagonal hD), schur_eq_attachCompl P o att hs hD]

theorem attach_posSemidef_iff (P : Matrix K K ℝ) (o : W) (att : ι → K)
    {s : ι → ℝ} (hs : ∀ i, s i ^ 2 = 1) {D : ι → Matrix W W ℝ} (hD : ∀ i, (D i).PosDef) :
    (fromBlocks P (couple o att s) (couple o att s)ᵀ (blockDiagonal D)).PosSemidef ↔
      (attachCompl P o att D).PosSemidef := by
  rw [schur_posSemidef_iff P _ (posDef_blockDiagonal hD), schur_eq_attachCompl P o att hs hD]

theorem attach_inv_toBlocks₁₁ {P : Matrix K K ℝ} (hP : P.IsHermitian) (o : W) (att : ι → K)
    {s : ι → ℝ} (hs : ∀ i, s i ^ 2 = 1) {D : ι → Matrix W W ℝ} (hD : ∀ i, (D i).PosDef)
    (hN : (fromBlocks P (couple o att s) (couple o att s)ᵀ (blockDiagonal D)).PosDef) :
    (fromBlocks P (couple o att s) (couple o att s)ᵀ (blockDiagonal D))⁻¹.toBlocks₁₁ =
      (attachCompl P o att D)⁻¹ := by
  rw [schur_inv_toBlocks₁₁ hP _ (posDef_blockDiagonal hD) hN, schur_eq_attachCompl P o att hs hD]

end BiluLinial.Counterexample
