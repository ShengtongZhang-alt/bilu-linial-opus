/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import Mathlib

@[expose] public section

namespace BiluLinial

open Matrix

universe u

/-- Signings and signed adjacency matrix of a graph -/
abbrev Signing {V : Type*} (G : SimpleGraph V) : Type _ :=
  G.edgeSet → ℤˣ

noncomputable def signedAdjMatrix {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    (σ : Signing G) : Matrix V V ℝ :=
  Matrix.of fun u v => if h : G.Adj u v then ((σ ⟨s(u, v), h⟩ : ℤ) : ℝ) else 0

/-- Spectral norm, equal to the largest absolute eigenvalue -/
noncomputable def opNorm {V : Type*} [Fintype V] [DecidableEq V] (M : Matrix V V ℝ) : ℝ :=
  ‖Matrix.toEuclideanCLM (n := V) (𝕜 := ℝ) M‖

theorem opNorm_eq_iSup_abs_eigenvalues₀ {V : Type*} [Fintype V] [DecidableEq V]
    (M : Matrix V V ℝ) (hM : M.IsHermitian) : opNorm M = ⨆ i, |hM.eigenvalues₀ i| := by
  sorry

/-- Main upper bound on Bilu–Linial -/
theorem near_ramanujan_signing :
    ∃ C : ℝ, ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
      ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        (∀ v, G.degree v ≤ d) →
          ∃ σ : Signing G, opNorm (signedAdjMatrix G σ) <
            Real.sqrt (4 * ((d : ℝ) - 1) + C * (d : ℝ) ^ (-(2 : ℝ) / 17)) := by
  sorry

/-- Main lower bound on Bilu–Linial -/
theorem explicit_excess (d : ℕ) (hd : 4 ≤ d) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V) (_ : DecidableRel G.Adj),
      G.Connected ∧ G.IsRegularOfDegree d ∧
        ∀ σ : Signing G,
          2 * Real.sqrt ((d : ℝ) - 1) + 1 / (25 * ((d : ℝ) - 1) ^ 5 * Real.sqrt ((d : ℝ) - 1)) ≤
            opNorm (signedAdjMatrix G σ) := by
  sorry

end BiluLinial
