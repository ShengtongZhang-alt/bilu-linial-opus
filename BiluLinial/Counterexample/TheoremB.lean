/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Counterexample.Centre
public import BiluLinial.Counterexample.Structure
public import BiluLinial.Counterexample.Completion
public import BiluLinial.Common.Spectral

/-!
# Theorem B

Blueprint node `B-main` (source "Reduction to `J`"). Complete the core `J` to a connected
`d`-regular graph `F` containing `J` as an induced subgraph. If some signing of `F` had
`‖A_σ(F)‖ ≤ r`, then `r I ∓ A_σ(F) ⪰ 0`, so the principal submatrices on `J` are `⪰ 0`, and the
restriction of `A_σ(F)` to `J` is a signed adjacency matrix of `J`, contradicting
`core_not_bounded`.
-/

@[expose] public section

namespace BiluLinial.Counterexample

open Matrix

theorem bilu_linial_counterexample_proof (d : ℕ) (hd : 3 ≤ d) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V)
      (_ : DecidableRel G.Adj),
      G.Connected ∧ G.IsRegularOfDegree d ∧
        ∀ σ : Signing G, 2 * Real.sqrt ((d : ℝ) - 1) < opNorm (signedAdjMatrix G σ) := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 3 := ⟨d - 3, by omega⟩
  obtain ⟨h, L, hJ⟩ := core_not_bounded n
  obtain ⟨V', _, _, F, _, f, hf, hadj, hconn, hreg⟩ :=
    exists_regular_supergraph (coreGraph n h L).G (n + 3) (coreGraph_connected n h L)
      (coreGraph_degree_le n h L)
  refine ⟨V', inferInstance, inferInstance, F, inferInstance, hconn, hreg, fun σ => ?_⟩
  have hr : 2 * Real.sqrt (((n + 3 : ℕ) : ℝ) - 1) = rad n := by
    unfold rad
    congr 2
    push_cast
    ring
  rw [hr]
  by_contra hle
  push Not at hle
  have hA := isSignedAdj_signedAdjMatrix F σ
  have hrad : 0 ≤ rad n := by unfold rad; positivity
  obtain ⟨h1, h2⟩ := (opNorm_le_iff_posSemidef hA.isHermitian hrad).1 hle
  apply hJ ((signedAdjMatrix F σ).submatrix f f) (hA.submatrix hf hadj)
  constructor
  · rw [← smul_one_sub_submatrix _ _ hf]
    exact h1.submatrix f
  · have h2' : (rad n • (1 : Matrix V' V' ℝ) - -signedAdjMatrix F σ).PosSemidef := by
      rwa [sub_neg_eq_add]
    have := h2'.submatrix f
    rwa [smul_one_sub_submatrix _ _ hf, Matrix.submatrix_neg, Pi.neg_apply, Pi.neg_apply,
      sub_neg_eq_add] at this

end BiluLinial.Counterexample
