/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Counterexample.TheoremB
public import BiluLinial.SecondOrder.Explicit.Theorem
public import BiluLinial.Tight.Theorem

/-!
# The main theorems

`near_ramanujan_signing_proof` and `explicit_excess_proof` state, verbatim, the two theorems of
`Challenge.lean` (Part D, the upper bound of `docs/second_order_bilu_linial_tight.tex`, and
Part C2, Section 6 of `docs/second_order_bilu_linial.tex`), over the definitions of
`BiluLinial/ChallengeDefs.lean` (a verbatim copy of those of `Challenge.lean`). The proof modules
do not import `Challenge`, so that `Solution.lean` can restate the Challenge theorems under their
own names; `scripts/check_statements.sh` and the comparator check that the restated theorems and
the definitions they use are identical to those of `Challenge.lean`.
`opNorm_eq_iSup_abs_eigenvalues₀_proof` states, verbatim, the third Challenge theorem: for a real
symmetric matrix, `opNorm` is the largest absolute value of an eigenvalue.

Theorem B (Part B) stays a library theorem, stated in full below: it covers `d = 3`, which
`explicit_excess` does not. The upper bounds of Part A (Theorems 1.1 and 1.2 of
`docs/asymptotic_bilu_linial.tex`) and Part C (Theorem 1.1 of `docs/second_order_bilu_linial.tex`)
were deleted together with their proofs once `near_ramanujan_signing` was proved: it implies the
Part C bound (`secondOrderStatement_of_nearRamanujan` in `BiluLinial/SanityD.lean`), which in turn
implies both Part A theorems.
-/

@[expose] public section

namespace BiluLinial

universe u

/-- **Theorem 1** of `docs/second_order_bilu_linial_tight.tex`, upper bound. There is an absolute
constant `C` such that for every sufficiently large integer `d` (that is, `d ≥ d₀` for some fixed
`d₀`), every finite simple graph `G` of maximum degree at most `d` has an edge signing `σ` with
`‖A_σ‖ < √(4(d-1) + C d^{-2/17})`. -/
theorem near_ramanujan_signing_proof :
    ∃ C : ℝ, ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
      ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        (∀ v, G.degree v ≤ d) →
          ∃ σ : Signing G, opNorm (signedAdjMatrix G σ) <
            Real.sqrt (4 * ((d : ℝ) - 1) + C * (d : ℝ) ^ (-(2 : ℝ) / 17)) :=
  Tight.near_ramanujan_signing_thm.{u}

/-- Section 6 of `docs/second_order_bilu_linial.tex`, with an explicit excess. For every integer
`d ≥ 4` there is a finite, connected, simple, `d`-regular graph `G` every signing `σ` of which
satisfies `‖A_σ‖ ≥ 2 √(d-1) + (d-1)^{-11/2}/25`. -/
theorem explicit_excess_proof (d : ℕ) (hd : 4 ≤ d) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V) (_ : DecidableRel G.Adj),
      G.Connected ∧ G.IsRegularOfDegree d ∧
        ∀ σ : Signing G,
          2 * Real.sqrt ((d : ℝ) - 1) + 1 / (25 * ((d : ℝ) - 1) ^ 5 * Real.sqrt ((d : ℝ) - 1)) ≤
            opNorm (signedAdjMatrix G σ) :=
  SecondOrder.Explicit.explicit_excess_thm d hd

/-- For a real symmetric matrix `M`, `opNorm M` is the largest absolute value of an eigenvalue,
listed with multiplicity by Mathlib's `Matrix.IsHermitian.eigenvalues₀`. -/
theorem opNorm_eq_iSup_abs_eigenvalues₀_proof {V : Type*} [Fintype V] [DecidableEq V]
    (M : Matrix V V ℝ) (hM : M.IsHermitian) : opNorm M = ⨆ i, |hM.eigenvalues₀ i| := by
  rcases isEmpty_or_nonempty V with hV | hV
  · have : IsEmpty (Fin (Fintype.card V)) := by
      rw [Fintype.card_eq_zero]
      infer_instance
    rw [Real.iSup_of_isEmpty, opNorm_of_isEmpty]
  · let e : Fin (Fintype.card V) ≃ V := Fintype.equivOfCardEq (Fintype.card_fin _)
    have he : ∀ j, hM.eigenvalues₀ j = hM.eigenvalues (e j) := fun j => by
      simp [Matrix.IsHermitian.eigenvalues, e]
    have : Nonempty (Fin (Fintype.card V)) := ⟨e.symm (Classical.arbitrary V)⟩
    obtain ⟨i, hi⟩ := exists_abs_eigenvalue_eq_opNorm hM
    refine le_antisymm ?_ (ciSup_le fun j => ?_)
    · have h := le_ciSup (Set.finite_range fun j => |hM.eigenvalues₀ j|).bddAbove (e.symm i)
      rwa [he, e.apply_symm_apply, hi] at h
    · rw [he]
      exact abs_eigenvalue_le_opNorm hM (e j)

/-- **Theorem B** of `docs/COUNTEREXAMPLE_ALL_DEGREES.md` (Xu's Theorem 1.1 for `d = 3`): the
Bilu–Linial conjecture fails in every degree `d ≥ 3`. For every integer `d ≥ 3` there is a finite,
connected, simple, `d`-regular graph `G` such that every signing `σ` of `G` satisfies
`‖A_σ‖ > 2 √(d - 1)`. -/
theorem bilu_linial_counterexample_proof (d : ℕ) (hd : 3 ≤ d) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V)
      (_ : DecidableRel G.Adj),
      G.Connected ∧ G.IsRegularOfDegree d ∧
        ∀ σ : Signing G, 2 * Real.sqrt ((d : ℝ) - 1) < opNorm (signedAdjMatrix G σ) :=
  Counterexample.bilu_linial_counterexample_proof d hd

end BiluLinial
