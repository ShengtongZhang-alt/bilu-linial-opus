/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import Mathlib

/-!
# The definitions of `Challenge.lean`, for the proof modules

A verbatim copy of the three definitions of `Challenge.lean` (same names, types and bodies).
The proof modules import this file instead of `Challenge`, so that `Solution.lean` can restate
the three Challenge theorems under their own names: the comparator loads `Challenge` and
`Solution` as separate environments and checks that every declaration used in the Challenge
statements is identical in both (`scripts/check_statements.sh` performs the same comparison
locally).
-/

@[expose] public section

namespace BiluLinial

open Matrix

universe u

/-- A signing of a simple graph `G`: a sign `σ e ∈ ℤˣ = {1, -1}` for every edge `e` of `G`. -/
abbrev Signing {V : Type*} (G : SimpleGraph V) : Type _ :=
  G.edgeSet → ℤˣ

/-- The signed adjacency matrix `A_σ` of a signing `σ` of `G`: its `(u, v)` entry is `σ(uv)` if
`uv` is an edge of `G` and `0` otherwise. It is a real symmetric matrix with zero diagonal. -/
noncomputable def signedAdjMatrix {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    (σ : Signing G) : Matrix V V ℝ :=
  Matrix.of fun u v => if h : G.Adj u v then ((σ ⟨s(u, v), h⟩ : ℤ) : ℝ) else 0

/-- The Euclidean operator norm `‖M‖ = sup_{‖x‖₂ ≤ 1} ‖M x‖₂` of a real square matrix, computed as
the norm of the continuous linear map `EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V` that `M`
represents in the standard basis. For a symmetric matrix it is the largest absolute value of an
eigenvalue (see `BiluLinial/Sanity.lean`); for an empty matrix it is `0`. -/
noncomputable def opNorm {V : Type*} [Fintype V] [DecidableEq V] (M : Matrix V V ℝ) : ℝ :=
  ‖Matrix.toEuclideanCLM (n := V) (𝕜 := ℝ) M‖

end BiluLinial
