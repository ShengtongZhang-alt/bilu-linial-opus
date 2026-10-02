/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Main

/-!
# Solution

The three theorems of `Challenge.lean` (the two main theorems and the equality between the norm and
the largest absolute value of an eigenvalue), under the same names and with the same statements,
proved by the theorems of `BiluLinial/Main.lean`. `comparator.json` configures the comparator
(`Challenge` against `Solution`); `scripts/check_statements.sh` performs its statement check
locally.
-/

@[expose] public section

namespace BiluLinial

universe u

/-- **Theorem 1** of `docs/second_order_bilu_linial_tight.tex`, upper bound. There is an absolute
constant `C` such that for every sufficiently large integer `d` (that is, `d ≥ d₀` for some fixed
`d₀`), every finite simple graph `G` of maximum degree at most `d` has an edge signing `σ` with
`‖A_σ‖ < √(4(d-1) + C d^{-2/17})`. (The paper writes `γ_{q+1} ≤ √(4q + C q^{-2/17})` with
`q = d - 1`; with `∃ C`, the strict and non-strict forms and `d^{-2/17}` versus `(d-1)^{-2/17}` are
equivalent, see `FORMALIZATION.md`.) -/
theorem near_ramanujan_signing :
    ∃ C : ℝ, ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
      ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        (∀ v, G.degree v ≤ d) →
          ∃ σ : Signing G, opNorm (signedAdjMatrix G σ) <
            Real.sqrt (4 * ((d : ℝ) - 1) + C * (d : ℝ) ^ (-(2 : ℝ) / 17)) :=
  near_ramanujan_signing_proof.{u}

/-- Section 6 of `docs/second_order_bilu_linial.tex`, with an explicit excess. For every integer
`d ≥ 4` there is a finite, connected, simple, `d`-regular graph `G` every signing `σ` of which
satisfies `‖A_σ‖ ≥ 2 √(d-1) + (d-1)^{-11/2}/25`. (The paper proves `‖A_σ‖ ≥ R` for every
`R < R_q = 2√q + (1 + O(1/q)) q^{-11/2}`, `q = d - 1`; the constant `1/25` is ours.) -/
theorem explicit_excess (d : ℕ) (hd : 4 ≤ d) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V) (_ : DecidableRel G.Adj),
      G.Connected ∧ G.IsRegularOfDegree d ∧
        ∀ σ : Signing G,
          2 * Real.sqrt ((d : ℝ) - 1) + 1 / (25 * ((d : ℝ) - 1) ^ 5 * Real.sqrt ((d : ℝ) - 1)) ≤
            opNorm (signedAdjMatrix G σ) :=
  explicit_excess_proof d hd

/-- **The norm is the largest absolute value of an eigenvalue.** For a real symmetric matrix `M`,
`opNorm M = max_i |λ_i|`, where `hM.eigenvalues₀ : Fin (Fintype.card V) → ℝ` (Mathlib's
`Matrix.IsHermitian.eigenvalues₀`) lists the eigenvalues of `M` with multiplicity, in decreasing
order. For an empty matrix both sides are `0`. -/
theorem opNorm_eq_iSup_abs_eigenvalues₀ {V : Type*} [Fintype V] [DecidableEq V]
    (M : Matrix V V ℝ) (hM : M.IsHermitian) : opNorm M = ⨆ i, |hM.eigenvalues₀ i| :=
  opNorm_eq_iSup_abs_eigenvalues₀_proof M hM

end BiluLinial
