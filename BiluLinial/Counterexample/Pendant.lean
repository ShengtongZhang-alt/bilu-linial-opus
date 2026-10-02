/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Counterexample.JoinGreen

/-!
# Strict positivity from a pendant parent

Blueprint node `B-pendant` (source Step 5, Xu Lemma 3.2). Let `X = join k Y` and consider
`join 1 X` (a parent vertex above the root of `X`). If `r I - A ⪰ 0` on `join 1 X` and the copies
of `Y` inside `X` are positive definite, then `r I - A_X ≻ 0`. Proof: eliminating the parent gives
`r I - A_X - (1/r) E_{oo} ⪰ 0`; the join lemma with root entry `α = r - 1/r` gives
`r - ∑ g - 1/r ≥ 0`, so `r - ∑ g ≥ 1/r > 0`, and the join lemma again gives `r I - A_X ≻ 0`.
-/

@[expose] public section

namespace BiluLinial.Counterexample

open Matrix

/-- Eliminating the parent vertex: if `[[P, C], [Cᵀ, blockDiagonal D]] ⪰ 0` with `P = (r)`,
`r > 0`, and `C` the coupling with sign `s 0` between the parent and the vertex `o` of the single
block, then `D 0 - (1/r) E_{oo} ⪰ 0`. -/
private theorem pendant_elim {W : Type} [Fintype W] [DecidableEq W] (o : W) {r : ℝ} (hr : 0 < r)
    {M : Matrix (Unit ⊕ (W × Fin 1)) (Unit ⊕ (W × Fin 1)) ℝ} (hMpsd : M.PosSemidef)
    {P : Matrix Unit Unit ℝ} {s : Fin 1 → ℝ} {D : Fin 1 → Matrix W W ℝ}
    (hM : M = fromBlocks P (couple o (fun _ => ()) s) (couple o (fun _ => ()) s)ᵀ
      (blockDiagonal D))
    (hP : P () () = r) (hs : s 0 ^ 2 = 1) :
    (D 0 + (r - 1 / r - r) • Matrix.single o o 1).PosSemidef := by
  have hP' : P = r • (1 : Matrix Unit Unit ℝ) := by
    ext ⟨⟩ ⟨⟩
    simp [hP]
  subst hM hP'
  have hPd : (r • (1 : Matrix Unit Unit ℝ)).PosDef := PosDef.one.smul hr
  let := hPd.isUnit.invertible
  rw [← conjTranspose_eq_transpose_of_trivial] at hMpsd
  have h2 := ((PosDef.fromBlocks₁₁ _ _ hPd).1 hMpsd).submatrix (fun w : W => (w, (0 : Fin 1)))
  have hinv : (r • (1 : Matrix Unit Unit ℝ))⁻¹ = r⁻¹ • 1 := by
    apply inv_eq_left_inv
    rw [smul_mul_smul_comm, one_mul, inv_mul_cancel₀ hr.ne', one_smul]
  rw [hinv] at h2
  convert h2 using 1
  ext w w'
  simp [couple, Matrix.mul_apply, Matrix.single, blockDiagonal_apply_eq]
  by_cases hw : w = o <;> by_cases hw' : w' = o
  · subst hw hw'
    simp
    linear_combination r⁻¹ * hs
  · simp [hw, hw', Ne.symm hw']
  · simp [hw, hw', Ne.symm hw]
  · simp [hw', Ne.symm hw]

theorem pendant_posDef (k : ℕ) (Y : RGraph) {r : ℝ} (hr : 0 < r)
    {A : Matrix (join 1 (join k Y)).V (join 1 (join k Y)).V ℝ}
    (hA : IsSignedAdj (join 1 (join k Y)).G A)
    (hpsd : (r • (1 : Matrix (join 1 (join k Y)).V (join 1 (join k Y)).V ℝ) - A).PosSemidef)
    (hY : ∀ i, (r • (1 : Matrix Y.V Y.V ℝ) - copyBlock Y (copyBlock (join k Y) A 0) i).PosDef) :
    (r • (1 : Matrix (join k Y).V (join k Y).V ℝ) - copyBlock (join k Y) A 0).PosDef := by
  have hB : IsSignedAdj (join k Y).G (copyBlock (join k Y) A 0) := hA.copy 0
  have hshift := pendant_elim (join k Y).root hr hpsd (hA.attach_decomp r)
    (by
      have h0 : A.toBlocks₁₁ () () = 0 := hA.apply_self _
      rw [Matrix.sub_apply, h0]
      simp) (by simp only [neg_sq]; exact hA.attach_sq 0)
  have h1 := ((join_schur_root hB hY (r - 1 / r)).2.1).1 hshift
  have h2 : 0 < 1 / r := by positivity
  exact (join_posDef_iff hB hY).2 (by linarith)

end BiluLinial.Counterexample
