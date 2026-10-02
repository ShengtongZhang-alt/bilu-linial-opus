/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.SecondOrder.Explicit.Centre
public import BiluLinial.SecondOrder.Explicit.Structure
public import BiluLinial.SecondOrder.Explicit.Param
public import BiluLinial.Counterexample.Completion
public import BiluLinial.Common.Spectral

/-!
# The explicit excess: `γ_d ≥ R_q`

Blueprint node `C2-main` (source Section 6, eq. (6.2)). For `d = n + 3 ≥ 4`, a positive root `z`
of `q z (1 + z + z² + 2z³) = 1 + z + z² + 4z⁴` (`q = d - 1`) and `R < 1/√z + q√z`: `exists_param`
gives `t` with `R < thr n t`; `tri_centre_not_bounded` gives a core `J = triCentre n h L` with no
signed adjacency matrix `A` such that `thr n t · I ∓ A ≻ 0`; `exists_regular_supergraph` embeds
`J` as an induced subgraph of a connected `d`-regular graph `F`. If a signing of `F` had
`‖A_σ‖ < R < thr n t`, then `thr n t · I ∓ A_σ ≻ 0` (`opNorm_lt_iff_posDef`), and the principal
submatrices on `J` (a signed adjacency matrix of `J`) would be positive definite.
-/

@[expose] public section

namespace BiluLinial.SecondOrder.Explicit

open Matrix BiluLinial.Counterexample

theorem explicit_excess_proof (d : ℕ) (hd : 4 ≤ d) (z : ℝ) (hz : 0 < z)
    (hroot : ((d : ℝ) - 1) * z * (1 + z + z ^ 2 + 2 * z ^ 3) = 1 + z + z ^ 2 + 4 * z ^ 4)
    (R : ℝ) (hR : R < 1 / Real.sqrt z + ((d : ℝ) - 1) * Real.sqrt z) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V)
      (_ : DecidableRel G.Adj),
      G.Connected ∧ G.IsRegularOfDegree d ∧
        ∀ σ : Signing G, R ≤ opNorm (signedAdjMatrix G σ) := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 3 := ⟨d - 3, by omega⟩
  have hq : ((n + 3 : ℕ) : ℝ) - 1 = (n : ℝ) + 2 := by
    push_cast
    ring
  rw [hq] at hroot hR
  obtain ⟨t, ht, hqt, hF, hRt⟩ := exists_param n (by omega) hz hroot hR
  obtain ⟨h, L, hJ⟩ := tri_centre_not_bounded n ht hqt hF
  obtain ⟨V', _, _, F, _, f, hf, hadj, hconn, hreg⟩ :=
    exists_regular_supergraph (triCentre n h L).G (n + 3) (triCentre_connected n h L)
      (triCentre_degree_le n h L)
  refine ⟨V', inferInstance, inferInstance, F, inferInstance, hconn, hreg, fun σ => ?_⟩
  by_contra hlt
  push Not at hlt
  have hA := isSignedAdj_signedAdjMatrix F σ
  obtain ⟨h1, h2⟩ := (opNorm_lt_iff_posDef hA.isHermitian (thr_pos n ht)).1 (hlt.trans hRt)
  apply hJ ((signedAdjMatrix F σ).submatrix f f) (hA.submatrix hf hadj)
  constructor
  · rw [← smul_one_sub_submatrix _ _ hf]
    exact h1.submatrix hf
  · have h2' : (thr n t • (1 : Matrix V' V' ℝ) - -signedAdjMatrix F σ).PosDef := by
      rwa [sub_neg_eq_add]
    have := h2'.submatrix hf
    rwa [smul_one_sub_submatrix _ _ hf, Matrix.submatrix_neg, Pi.neg_apply, Pi.neg_apply,
      sub_neg_eq_add] at this

end BiluLinial.SecondOrder.Explicit
