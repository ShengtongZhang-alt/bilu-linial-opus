/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.SecondOrder.Explicit.Centre
public import BiluLinial.SecondOrder.Explicit.Structure
public import BiluLinial.SecondOrder.Explicit.Excess
public import BiluLinial.SecondOrder.Explicit.Root
public import BiluLinial.Counterexample.Completion
public import BiluLinial.Common.Spectral

/-!
# The explicit excess `2√q + q^{-11/2}/25` (the Challenge statement `explicit_excess`)

Blueprint node `C2-thm`. For `d = n + 3 ≥ 4`, `q = n + 2`, take `t = t₀(q)` (`Excess.lean`): then
`q t² < 1`, `F_q(t²) > 0` and `thr n t = q t + 1/t ≥ 2√q + q^{-11/2}/25`. `tri_centre_not_bounded`
gives a core `J = triCentre n h L` with no signed adjacency matrix `A` such that
`thr n t · I ∓ A ≻ 0`, and `exists_regular_supergraph` embeds `J` as an induced subgraph of a
connected `d`-regular graph `F`. A signing of `F` with `‖A_σ‖ < 2√q + q^{-11/2}/25 ≤ thr n t` would
make both `thr n t · I ∓ A_σ` positive definite, hence also their principal submatrices on `J`.
-/

@[expose] public section

namespace BiluLinial.SecondOrder.Explicit

open Matrix BiluLinial.Counterexample

theorem explicit_excess_thm (d : ℕ) (hd : 4 ≤ d) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V) (_ : DecidableRel G.Adj),
      G.Connected ∧ G.IsRegularOfDegree d ∧
        ∀ σ : Signing G,
          2 * Real.sqrt ((d : ℝ) - 1) + 1 / (25 * ((d : ℝ) - 1) ^ 5 * Real.sqrt ((d : ℝ) - 1)) ≤
            opNorm (signedAdjMatrix G σ) := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 3 := ⟨d - 3, by omega⟩
  have hq : ((n + 3 : ℕ) : ℝ) - 1 = (n : ℝ) + 2 := by
    push_cast
    ring
  rw [hq]
  have hq3 : (3 : ℝ) ≤ (n : ℝ) + 2 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    linarith
  have ht := t0_pos hq3
  have hqt := t0_sq_lt hq3
  have hF : 1 + t0 ((n : ℝ) + 2) ^ 2 + (t0 ((n : ℝ) + 2) ^ 2) ^ 2 +
        4 * (t0 ((n : ℝ) + 2) ^ 2) ^ 4 <
      ((n : ℝ) + 2) * t0 ((n : ℝ) + 2) ^ 2 *
        (1 + t0 ((n : ℝ) + 2) ^ 2 + (t0 ((n : ℝ) + 2) ^ 2) ^ 2 +
          2 * (t0 ((n : ℝ) + 2) ^ 2) ^ 3) := by
    have h1 := t0_poly_pos hq3
    have h2 := rootPoly_eq ((n : ℝ) + 2) (t0 ((n : ℝ) + 2) ^ 2)
    linarith
  have hthr : 2 * Real.sqrt ((n : ℝ) + 2) +
      1 / (25 * ((n : ℝ) + 2) ^ 5 * Real.sqrt ((n : ℝ) + 2)) ≤ thr n (t0 ((n : ℝ) + 2)) :=
    t0_thr_ge hq3
  obtain ⟨h, L, hJ⟩ := tri_centre_not_bounded n ht hqt hF
  obtain ⟨V', _, _, F, _, f, hf, hadj, hconn, hreg⟩ :=
    exists_regular_supergraph (triCentre n h L).G (n + 3) (triCentre_connected n h L)
      (triCentre_degree_le n h L)
  refine ⟨V', inferInstance, inferInstance, F, inferInstance, hconn, hreg, fun σ => ?_⟩
  by_contra hlt
  push Not at hlt
  have hA := isSignedAdj_signedAdjMatrix F σ
  obtain ⟨h1, h2⟩ := (opNorm_lt_iff_posDef hA.isHermitian (thr_pos n ht)).1
    (hlt.trans_le hthr)
  apply hJ ((signedAdjMatrix F σ).submatrix f f) (hA.submatrix hf hadj)
  constructor
  · rw [← smul_one_sub_submatrix _ _ hf]
    exact h1.submatrix hf
  · have h2' : (thr n (t0 ((n : ℝ) + 2)) • (1 : Matrix V' V' ℝ) - -signedAdjMatrix F σ).PosDef := by
      rwa [sub_neg_eq_add]
    have := h2'.submatrix hf
    rwa [smul_one_sub_submatrix _ _ hf, Matrix.submatrix_neg, Pi.neg_apply, Pi.neg_apply,
      sub_neg_eq_add] at this

end BiluLinial.SecondOrder.Explicit
