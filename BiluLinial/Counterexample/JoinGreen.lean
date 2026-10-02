/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Counterexample.AttachSchur
public import BiluLinial.Counterexample.AttachDecomp

/-!
# The join lemma

Blueprint node `B-join` (source Steps 1 and 4, Xu Lemma 3.3). For a signed adjacency matrix `A`
of `join k Y` whose copy blocks `A_i` satisfy `r I - A_i ≻ 0`, with
`p = r - ∑ᵢ g(A_i)`, `g(A_i) = ((r I - A_i)⁻¹)_{oo}`:
`r I - A ≻ 0 ↔ p > 0`, `r I - A ⪰ 0 ↔ p ≥ 0`, and then `g(A) = 1 / p`. The general form
`join_schur_root` replaces the root diagonal entry `r` by any `α`.
-/

@[expose] public section

namespace BiluLinial.Counterexample

open Matrix

/-- `r I - A` with its root diagonal entry replaced by `α`. -/
noncomputable def rootShift {k : ℕ} {Y : RGraph} (r α : ℝ) (A : Matrix (join k Y).V (join k Y).V ℝ) :
    Matrix (join k Y).V (join k Y).V ℝ :=
  r • (1 : Matrix (join k Y).V (join k Y).V ℝ) - A +
    (α - r) • Matrix.single (join k Y).root (join k Y).root 1

variable {k : ℕ} {Y : RGraph} {A : Matrix (join k Y).V (join k Y).V ℝ} {r : ℝ}

theorem unit_matrix_eq_diagonal (M : Matrix Unit Unit ℝ) : M = diagonal fun _ => M () () := by
  ext ⟨⟩ ⟨⟩
  rw [diagonal_apply_eq]

theorem unit_matrix_posDef_iff (M : Matrix Unit Unit ℝ) : M.PosDef ↔ 0 < M () () := by
  have h := posDef_diagonal_iff (d := fun _ : Unit => M () ())
  rw [← unit_matrix_eq_diagonal M] at h
  exact h.trans ⟨fun h => h (), fun h _ => h⟩

theorem unit_matrix_posSemidef_iff (M : Matrix Unit Unit ℝ) : M.PosSemidef ↔ 0 ≤ M () () := by
  have h := posSemidef_diagonal_iff (d := fun _ : Unit => M () ())
  rw [← unit_matrix_eq_diagonal M] at h
  exact h.trans ⟨fun h => h (), fun h _ => h⟩

theorem unit_matrix_inv_apply (M : Matrix Unit Unit ℝ) : M⁻¹ () () = 1 / M () () := by
  rw [inv_subsingleton, diagonal_apply_eq, Ring.inverse_eq_inv, one_div]

/-- `rootShift_eq_fromBlocks` with the vertex type written as `Unit ⊕ (Y.V × Fin k)`. -/
theorem rootShift_eq_fromBlocks_aux {B : Matrix (Unit ⊕ (Y.V × Fin k)) (Unit ⊕ (Y.V × Fin k)) ℝ}
    (hB : IsSignedAdj (attachGraph (⊥ : SimpleGraph Unit) Y (fun _ : Fin k => ())) B) (α : ℝ) :
    r • (1 : Matrix (Unit ⊕ (Y.V × Fin k)) (Unit ⊕ (Y.V × Fin k)) ℝ) - B +
        (α - r) • single (Sum.inl ()) (Sum.inl ()) 1 =
      fromBlocks (α • (1 : Matrix Unit Unit ℝ))
        (couple Y.root (fun _ : Fin k => ()) fun i => -B (Sum.inl ()) (Sum.inr (Y.root, i)))
        (couple Y.root (fun _ : Fin k => ()) fun i => -B (Sum.inl ()) (Sum.inr (Y.root, i)))ᵀ
        (blockDiagonal fun i => r • (1 : Matrix Y.V Y.V ℝ) - copyBlock Y B i) := by
  have h0 : B (Sum.inl ()) (Sum.inl ()) = 0 := hB.apply_self _
  rw [hB.attach_decomp r]
  ext (a | ⟨w, i⟩) (b | ⟨w', i'⟩)
  · cases a
    cases b
    simp only [Matrix.add_apply, Matrix.smul_apply, fromBlocks_apply₁₁, single_apply_same,
      Matrix.sub_apply, one_apply_eq, toBlocks₁₁, of_apply, h0, smul_eq_mul]
    ring
  · simp
  · simp
  · simp

/-- The block form of `rootShift` on `Unit ⊕ (Y.V × Fin k)`. -/
theorem rootShift_eq_fromBlocks (hA : IsSignedAdj (join k Y).G A) (α : ℝ) :
    rootShift r α A = fromBlocks (α • (1 : Matrix Unit Unit ℝ))
      (couple Y.root (fun _ : Fin k => ()) fun i => -A (Sum.inl ()) (Sum.inr (Y.root, i)))
      (couple Y.root (fun _ : Fin k => ()) fun i => -A (Sum.inl ()) (Sum.inr (Y.root, i)))ᵀ
      (blockDiagonal fun i => r • (1 : Matrix Y.V Y.V ℝ) - copyBlock Y A i) :=
  rootShift_eq_fromBlocks_aux (B := A) hA α

theorem rootShift_self : rootShift r r A = r • (1 : Matrix (join k Y).V (join k Y).V ℝ) - A := by
  rw [rootShift, sub_self, zero_smul, add_zero]

/-- The join lemma with the root diagonal entry of `r I - A` replaced by `α`. -/
theorem join_schur_root (hA : IsSignedAdj (join k Y).G A)
    (hY : ∀ i, (r • (1 : Matrix Y.V Y.V ℝ) - copyBlock Y A i).PosDef) (α : ℝ) :
    ((rootShift r α A).PosDef ↔ 0 < α - ∑ i, green r (copyBlock Y A i) Y.root) ∧
    ((rootShift r α A).PosSemidef ↔ 0 ≤ α - ∑ i, green r (copyBlock Y A i) Y.root) ∧
    ((rootShift r α A).PosDef →
      (rootShift r α A)⁻¹ (join k Y).root (join k Y).root =
        1 / (α - ∑ i, green r (copyBlock Y A i) Y.root)) := by
  have hA' : IsSignedAdj (attachGraph (⊥ : SimpleGraph Unit) Y (fun _ : Fin k => ())) A := hA
  have hs : ∀ i : Fin k, (-A (Sum.inl ()) (Sum.inr (Y.root, i))) ^ 2 = 1 := fun i => by
    rw [neg_sq]
    exact hA'.attach_sq i
  have hP : (α • (1 : Matrix Unit Unit ℝ)).IsHermitian :=
    IsHermitian.ext fun i j => by cases i; cases j; exact star_trivial _
  have hcompl : attachCompl (α • (1 : Matrix Unit Unit ℝ)) Y.root (fun _ : Fin k => ())
      (fun i => r • (1 : Matrix Y.V Y.V ℝ) - copyBlock Y A i) () () =
      α - ∑ i, green r (copyBlock Y A i) Y.root := by
    simp [attachCompl, green]
  rw [rootShift_eq_fromBlocks (r := r) hA α]
  refine ⟨?_, ?_, fun hN => ?_⟩
  · refine (attach_posDef_iff hP Y.root (fun _ : Fin k => ()) hs hY).trans ?_
    rw [unit_matrix_posDef_iff, hcompl]
  · refine (attach_posSemidef_iff _ Y.root (fun _ : Fin k => ()) hs hY).trans ?_
    rw [unit_matrix_posSemidef_iff, hcompl]
  · have h3 := congrFun (congrFun
      (attach_inv_toBlocks₁₁ hP Y.root (fun _ : Fin k => ()) hs hY hN) ()) ()
    rw [unit_matrix_inv_apply, hcompl] at h3
    exact h3

theorem join_posDef_iff (hA : IsSignedAdj (join k Y).G A)
    (hY : ∀ i, (r • (1 : Matrix Y.V Y.V ℝ) - copyBlock Y A i).PosDef) :
    (r • (1 : Matrix (join k Y).V (join k Y).V ℝ) - A).PosDef ↔
      0 < r - ∑ i, green r (copyBlock Y A i) Y.root := by
  rw [← rootShift_self]
  exact (join_schur_root hA hY r).1

theorem join_posSemidef_iff (hA : IsSignedAdj (join k Y).G A)
    (hY : ∀ i, (r • (1 : Matrix Y.V Y.V ℝ) - copyBlock Y A i).PosDef) :
    (r • (1 : Matrix (join k Y).V (join k Y).V ℝ) - A).PosSemidef ↔
      0 ≤ r - ∑ i, green r (copyBlock Y A i) Y.root := by
  rw [← rootShift_self]
  exact (join_schur_root hA hY r).2.1

theorem join_green_eq (hA : IsSignedAdj (join k Y).G A)
    (hY : ∀ i, (r • (1 : Matrix Y.V Y.V ℝ) - copyBlock Y A i).PosDef)
    (hpos : (r • (1 : Matrix (join k Y).V (join k Y).V ℝ) - A).PosDef) :
    green r A (join k Y).root = 1 / (r - ∑ i, green r (copyBlock Y A i) Y.root) := by
  rw [← rootShift_self] at hpos
  have h := (join_schur_root hA hY r).2.2 hpos
  rw [rootShift_self] at h
  exact h

end BiluLinial.Counterexample
