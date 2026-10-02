/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import Mathlib

/-!
# Toolchain smoke test

Checks that the Mathlib API the two formalizations are likely to need (simple graphs, degrees,
regularity, induced subgraphs, matrices, positive definiteness, the `ℓ²` operator norm,
eigenvalues of Hermitian matrices, Schur complements, square roots and logarithms) is available
at the pinned Mathlib revision, and that tactics run.
-/

@[expose] public section

noncomputable section

namespace BiluLinial

open SimpleGraph Matrix

example {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) : Prop :=
  G.IsRegularOfDegree d

example {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) : Prop :=
  ∀ v, G.degree v ≤ d

example {V : Type*} (G : SimpleGraph V) (s : Set V) : SimpleGraph s := G.induce s

example {V : Type*} [Fintype V] (M : Matrix V V ℝ) : Prop := M.PosDef

example {V : Type*} [Fintype V] [DecidableEq V] (M : Matrix V V ℝ) (hM : M.IsHermitian) :
    V → ℝ :=
  hM.eigenvalues

example {V : Type*} [Fintype V] [DecidableEq V] (M : Matrix V V ℝ) : ℝ :=
  ‖Matrix.toEuclideanCLM (𝕜 := ℝ) M‖

open scoped Matrix.Norms.L2Operator in
example {V : Type*} [Fintype V] [DecidableEq V] (M : Matrix V V ℝ) : ℝ := ‖M‖

example : Real.sqrt 4 = 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

example (x : ℝ) (hx : 1 < x) : 0 < Real.log x := Real.log_pos hx

end BiluLinial

end
