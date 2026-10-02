/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Counterexample.Defs

/-!
# Signed adjacency matrices of attach graphs

Blueprint node `B-attach-decomp`.

* `IsSignedAdj` is preserved by negation and by restriction along induced embeddings, and every
  `signedAdjMatrix` is a signed adjacency matrix.
* A signed adjacency matrix `A` of `attachGraph C Y att` splits as
  `r I - A = [[r I - A_C, B], [Bᵀ, blockDiagonal (r I - A_i)]]` where `A_C` (core block) is a signed
  adjacency matrix of `C`, each copy block `A_i` one of `Y`, and `B` is the coupling with signs
  `-A (att i, (root, i))`.
* `joinSub Y k i` embeds `join 1 Y` into `join k Y` as an induced subgraph (root and copy `i`).
-/

@[expose] public section

namespace BiluLinial.Counterexample

open Matrix

section General

variable {V V' : Type*} {G : SimpleGraph V} {G' : SimpleGraph V'} {A : Matrix V V ℝ}

theorem IsSignedAdj.neg (hA : IsSignedAdj G A) : IsSignedAdj G (-A) := by
  refine ⟨hA.isHermitian.neg, fun u v h => ?_, fun u v h => ?_⟩
  · rw [Matrix.neg_apply, neg_sq]
    exact hA.sq_eq_one u v h
  · rw [Matrix.neg_apply, hA.eq_zero u v h, neg_zero]

theorem IsSignedAdj.apply_self (hA : IsSignedAdj G A) (v : V) : A v v = 0 :=
  hA.eq_zero v v (G.irrefl)

theorem IsSignedAdj.submatrix (hA : IsSignedAdj G A) {f : V' → V} (hf : Function.Injective f)
    (hadj : ∀ a b, G'.Adj a b ↔ G.Adj (f a) (f b)) : IsSignedAdj G' (A.submatrix f f) :=
  ⟨hA.isHermitian.submatrix f, fun a b h => hA.sq_eq_one _ _ ((hadj a b).1 h),
    fun a b h => hA.eq_zero _ _ fun h' => h ((hadj a b).2 h')⟩

/-- A symmetric matrix over `ℝ`: `A v u = A u v`. -/
theorem IsSignedAdj.apply_comm (hA : IsSignedAdj G A) (u v : V) : A v u = A u v := by
  have h := hA.isHermitian.apply u v
  rwa [star_trivial] at h

theorem isSignedAdj_signedAdjMatrix (G : SimpleGraph V) [DecidableRel G.Adj] (σ : Signing G) :
    IsSignedAdj G (signedAdjMatrix G σ) := by
  refine ⟨Matrix.IsHermitian.ext fun u v => ?_, fun u v h => ?_, fun u v h => ?_⟩
  · rw [star_trivial]
    simp only [signedAdjMatrix, Matrix.of_apply]
    by_cases h : G.Adj u v
    · rw [dite_eq_left h, dite_eq_left (G.adj_symm h)]
      have he : (⟨s(v, u), G.adj_symm h⟩ : G.edgeSet) = ⟨s(u, v), h⟩ :=
        Subtype.ext Sym2.eq_swap
      rw [he]
    · rw [dite_eq_right h, dite_eq_right fun h' => h (G.adj_symm h')]
  · simp only [signedAdjMatrix, Matrix.of_apply, dite_eq_left h]
    rw [← Int.cast_pow, Int.isUnit_sq (σ ⟨s(u, v), h⟩).isUnit, Int.cast_one]
  · simp only [signedAdjMatrix, Matrix.of_apply, dite_eq_right h]

end General

section Attach

variable {K ι : Type} [Fintype K] [DecidableEq K] [Fintype ι] [DecidableEq ι]
  {C : SimpleGraph K} [DecidableRel C.Adj] {Y : RGraph} {att : ι → K}
  {A : Matrix (K ⊕ (Y.V × ι)) (K ⊕ (Y.V × ι)) ℝ}

theorem IsSignedAdj.toBlocks₁₁ (hA : IsSignedAdj (attachGraph C Y att) A) :
    IsSignedAdj C A.toBlocks₁₁ :=
  hA.submatrix (f := Sum.inl) Sum.inl_injective fun a b =>
    (attachGraph_adj_inl_inl C Y att a b).symm

theorem IsSignedAdj.copy (hA : IsSignedAdj (attachGraph C Y att) A) (i : ι) :
    IsSignedAdj Y.G (copyBlock Y A i) :=
  hA.submatrix (f := fun w => Sum.inr (w, i)) (fun a b h => by simpa using h) fun a b => by
    simp

theorem IsSignedAdj.attach_sq (hA : IsSignedAdj (attachGraph C Y att) A) (i : ι) :
    A (.inl (att i)) (.inr (Y.root, i)) ^ 2 = 1 :=
  hA.sq_eq_one _ _ ((attachGraph_adj_inl_inr C Y att _ _).2 ⟨rfl, rfl⟩)

theorem IsSignedAdj.attach_decomp (hA : IsSignedAdj (attachGraph C Y att) A) (r : ℝ) :
    r • (1 : Matrix (K ⊕ (Y.V × ι)) (K ⊕ (Y.V × ι)) ℝ) - A =
      fromBlocks (r • (1 : Matrix K K ℝ) - A.toBlocks₁₁)
        (couple Y.root att fun i => -A (.inl (att i)) (.inr (Y.root, i)))
        (couple Y.root att fun i => -A (.inl (att i)) (.inr (Y.root, i)))ᵀ
        (blockDiagonal fun i => r • (1 : Matrix Y.V Y.V ℝ) - copyBlock Y A i) := by
  ext (a | ⟨w, i⟩) (b | ⟨w', i'⟩)
  · show r • (1 : Matrix _ _ ℝ) (Sum.inl a) (Sum.inl b) - A (Sum.inl a) (Sum.inl b) =
      r • (1 : Matrix K K ℝ) a b - A (Sum.inl a) (Sum.inl b)
    simp [Matrix.one_apply]
  · rw [fromBlocks_apply₁₂, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply_ne Sum.inl_ne_inr, smul_zero, zero_sub]
    simp only [couple, of_apply]
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h
      rfl
    · rw [hA.eq_zero (.inl a) (.inr (w', i')) h, neg_zero]
  · rw [fromBlocks_apply₂₁, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply_ne Sum.inr_ne_inl, smul_zero, zero_sub,
      hA.apply_comm (.inl b) (.inr (w, i))]
    simp only [transpose_apply, couple, of_apply]
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h
      rfl
    · rw [hA.eq_zero (.inl b) (.inr (w, i)) h, neg_zero]
  · rw [fromBlocks_apply₂₂]
    by_cases hi : i = i'
    · subst hi
      rw [blockDiagonal_apply_eq]
      simp [copyBlock, Matrix.one_apply]
    · rw [blockDiagonal_apply_ne _ _ _ hi, Matrix.sub_apply, Matrix.smul_apply,
        hA.eq_zero (.inr (w, i)) (.inr (w', i')) fun h =>
          hi ((attachGraph_adj_inr_inr C Y att (w, i) (w', i')).1 h).1,
        Matrix.one_apply_ne fun h => hi (congrArg Prod.snd (Sum.inr_injective h)), smul_zero,
        sub_zero]

end Attach

section JoinSub

variable (Y : RGraph) (k : ℕ) (i : Fin k)

theorem joinSub_injective : Function.Injective (joinSub Y k i) := by
  rintro (a | ⟨w, j⟩) (b | ⟨w', j'⟩) h
  · cases a; cases b; rfl
  · simp [joinSub] at h
  · simp [joinSub] at h
  · have h' : w = w' := congrArg Prod.fst (Sum.inr_injective h)
    subst h'
    rw [Subsingleton.elim j j']

theorem joinSub_adj_iff (a b : (join 1 Y).V) :
    (join 1 Y).G.Adj a b ↔ (join k Y).G.Adj (joinSub Y k i a) (joinSub Y k i b) := by
  rcases a with a | ⟨w, j⟩ <;> rcases b with b | ⟨w', j'⟩
  · exact Iff.rfl
  · exact Iff.rfl
  · exact Iff.rfl
  · change j = j' ∧ Y.G.Adj w w' ↔ i = i ∧ Y.G.Adj w w'
    simp [Subsingleton.elim j j']

theorem copyBlock_submatrix_joinSub (A : Matrix (join k Y).V (join k Y).V ℝ) :
    copyBlock Y (A.submatrix (joinSub Y k i) (joinSub Y k i)) 0 = copyBlock Y A i := by
  ext w w'
  rfl

end JoinSub

/-- Restricting `r I - A` to a principal submatrix along an injective map. -/
theorem smul_one_sub_submatrix {V V' : Type*} [DecidableEq V] [DecidableEq V'] (r : ℝ)
    (A : Matrix V V ℝ) {f : V' → V} (hf : Function.Injective f) :
    (r • (1 : Matrix V V ℝ) - A).submatrix f f = r • (1 : Matrix V' V' ℝ) - A.submatrix f f := by
  ext a b
  simp [Matrix.one_apply, hf.eq_iff]

end BiluLinial.Counterexample
