/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.SecondOrder.Explicit.Defs
public import BiluLinial.Counterexample.Structure

/-!
# Degrees and connectivity of the triangle construction

Blueprint node `C2-structure` (source Section 6: "The distinguished vertex has degree `q`, all
other nonterminal vertices have degree `q+1`"; "a finite connected simple graph `H` of maximum
degree `d`"). With `d = n + 3`:

* the triangle seed satisfies `RootedDegLe d` (`o`: `2 + (q - 2) + 1 = d` counting the parent
  edge; `v₁, v₂`: `2 + (q - 1) = d`; tree vertices as in Part B), hence so does every `Q_j`;
* the core `triCentre n h L` is connected with maximum degree at most `d`.

Reuses Part B's `attach_degree_inl/inr`, `join_rootedDegLe`, `tree_rootedDegLe`,
`attach_connected`, `join_connected`, `tree_connected`.
-/

@[expose] public section

namespace BiluLinial.SecondOrder.Explicit

open BiluLinial.Counterexample

theorem triCore_degree (c : Fin 3) : (⊤ : SimpleGraph (Fin 3)).degree c = 2 := by
  simp

theorem triSeed_rootedDegLe (n h : ℕ) : RootedDegLe (n + 3) (triSeed n h) := by
  rintro (c | ⟨w, i⟩)
  · have hd : ∀ v : (triSeed n h).V, v = Sum.inl c →
        (triSeed n h).G.degree v = (⊤ : SimpleGraph (Fin 3)).degree c + triMult n c := by
      rintro v rfl
      have := attach_degree_inl (⊤ : SimpleGraph (Fin 3)) (tree n h)
        (Sigma.fst : (Σ c : Fin 3, Fin (triMult n c)) → Fin 3) c
      rw [card_filter_sigma_fst (fun c => Fin (triMult n c)), Fintype.card_fin] at this
      exact this
    rw [hd _ rfl, triCore_degree]
    split_ifs with hc
    · obtain rfl : c = 0 := Sum.inl_injective hc
      simp [triMult]
      omega
    · fin_cases c <;> simp [triMult] <;> omega
  · have hd : ∀ v : (triSeed n h).V, v = Sum.inr (w, i) →
        (triSeed n h).G.degree v =
          (tree n h).G.degree w + if w = (tree n h).root then 1 else 0 := by
      rintro v rfl
      exact attach_degree_inr (⊤ : SimpleGraph (Fin 3)) (tree n h) Sigma.fst w i
    have hr : ¬ @Eq (triSeed n h).V (Sum.inr (w, i)) (triSeed n h).root := Sum.inr_ne_inl
    rw [hd _ rfl, ite_eq_right hr, add_zero]
    exact tree_rootedDegLe n h w

theorem triQ_rootedDegLe (n h j : ℕ) : RootedDegLe (n + 3) (triQ n h j) := by
  induction j with
  | zero => exact triSeed_rootedDegLe n h
  | succ j ih => exact join_rootedDegLe (by omega) ih

theorem triCentre_degree_le (n h L : ℕ) (v : (triCentre n h L).V) :
    (triCentre n h L).G.degree v ≤ n + 3 := by
  rcases v with u | ⟨w, i⟩
  · exact (join_degree_inl (n + 3) (triQ n h L) u rfl).le
  · exact (join_degree_inr (n + 3) (triQ n h L) w i rfl).trans_le
      (triQ_rootedDegLe n h L w)

theorem triSeed_connected (n h : ℕ) : (triSeed n h).G.Connected :=
  attach_connected (⊤ : SimpleGraph (Fin 3)) (tree n h) Sigma.fst SimpleGraph.connected_top
    (tree_connected n h)

theorem triQ_connected (n h j : ℕ) : (triQ n h j).G.Connected := by
  induction j with
  | zero => exact triSeed_connected n h
  | succ j ih => exact join_connected ih

theorem triCentre_connected (n h L : ℕ) : (triCentre n h L).G.Connected :=
  join_connected (triQ_connected n h L)

end BiluLinial.SecondOrder.Explicit
