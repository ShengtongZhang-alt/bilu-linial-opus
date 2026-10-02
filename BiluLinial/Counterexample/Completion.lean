/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.ChallengeDefs

/-!
# Regular completion

Blueprint node `B-completion` (source Construction, item 5). Every finite connected graph of
maximum degree at most `d` is an induced subgraph of a finite connected `d`-regular graph.

Doubling construction: take two copies of `G` and join each vertex of degree `< d` to its own
copy. This keeps `G` induced, raises every degree below `d` by one, and keeps connectivity when
some vertex has degree `< d`. Iterate until the graph is `d`-regular.
-/

@[expose] public section

namespace BiluLinial.Counterexample

section Double

variable {V : Type} (G : SimpleGraph V) (S : V → Prop)

/-- Adjacency relation of `dbl G S`. -/
def dblAdj : V ⊕ V → V ⊕ V → Prop
  | .inl a, .inl b => G.Adj a b
  | .inr a, .inr b => G.Adj a b
  | .inl a, .inr b => a = b ∧ S a
  | .inr a, .inl b => a = b ∧ S a

/-- Two copies of `G`, with each vertex `v` satisfying `S v` joined to its own copy. -/
def dbl : SimpleGraph (V ⊕ V) where
  Adj := dblAdj G S
  symm := ⟨by
    rintro (a | a) (b | b) h <;> simp only [dblAdj] at h ⊢
    · exact G.adj_symm h
    · obtain ⟨rfl, h⟩ := h; exact ⟨rfl, h⟩
    · obtain ⟨rfl, h⟩ := h; exact ⟨rfl, h⟩
    · exact G.adj_symm h⟩
  loopless := ⟨by
    rintro (a | a) h <;> simp only [dblAdj] at h
    · exact G.irrefl h
    · exact G.irrefl h⟩

@[simp] theorem dbl_adj_inl_inl (a b : V) : (dbl G S).Adj (.inl a) (.inl b) ↔ G.Adj a b :=
  Iff.rfl

@[simp] theorem dbl_adj_inr_inr (a b : V) : (dbl G S).Adj (.inr a) (.inr b) ↔ G.Adj a b :=
  Iff.rfl

@[simp] theorem dbl_adj_inl_inr (a b : V) : (dbl G S).Adj (.inl a) (.inr b) ↔ a = b ∧ S a :=
  Iff.rfl

@[simp] theorem dbl_adj_inr_inl (a b : V) : (dbl G S).Adj (.inr a) (.inl b) ↔ a = b ∧ S a :=
  Iff.rfl

instance dbl.decidableAdj [DecidableEq V] [DecidableRel G.Adj] [DecidablePred S] :
    DecidableRel (dbl G S).Adj
  | .inl a, .inl b => inferInstanceAs (Decidable (G.Adj a b))
  | .inr a, .inr b => inferInstanceAs (Decidable (G.Adj a b))
  | .inl a, .inr b => inferInstanceAs (Decidable (a = b ∧ S a))
  | .inr a, .inl b => inferInstanceAs (Decidable (a = b ∧ S a))

/-- The first copy. -/
def dblInl : G →g dbl G S := ⟨Sum.inl, fun h => h⟩

/-- The second copy. -/
def dblInr : G →g dbl G S := ⟨Sum.inr, fun h => h⟩

theorem dbl_connected (hG : G.Connected) (v₀ : V) (h₀ : S v₀) : (dbl G S).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨.inl v₀, ?_⟩
  rintro (w | w)
  · exact (hG.preconnected v₀ w).map (dblInl G S)
  · have h1 : (dbl G S).Reachable (.inl v₀) (.inr v₀) := SimpleGraph.Adj.reachable ⟨rfl, h₀⟩
    exact h1.trans ((hG.preconnected v₀ w).map (dblInr G S))

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [DecidablePred S]

theorem dbl_neighborFinset_inl (v : V) :
    (dbl G S).neighborFinset (.inl v) =
      (G.neighborFinset v).disjSum (if S v then {v} else ∅) := by
  ext (w | w)
  · simp [Finset.inl_mem_disjSum]
  · by_cases h : S v
    · simp only [SimpleGraph.mem_neighborFinset, dbl_adj_inl_inr, Finset.inr_mem_disjSum, h,
        ite_true, Finset.mem_singleton, and_true]
      exact eq_comm
    · simp [h]

theorem dbl_neighborFinset_inr (v : V) :
    (dbl G S).neighborFinset (.inr v) =
      Finset.disjSum (if S v then {v} else ∅) (G.neighborFinset v) := by
  ext (w | w)
  · by_cases h : S v
    · simp only [SimpleGraph.mem_neighborFinset, dbl_adj_inr_inl, Finset.inl_mem_disjSum, h,
        ite_true, Finset.mem_singleton, and_true]
      exact eq_comm
    · simp [h]
  · simp [Finset.inr_mem_disjSum]

omit [Fintype V] [DecidableEq V] in
theorem card_ite_singleton (v : V) :
    (if S v then ({v} : Finset V) else ∅).card = if S v then 1 else 0 := by
  split_ifs <;> simp

theorem dbl_degree_inl (v : V) :
    (dbl G S).degree (.inl v) = G.degree v + if S v then 1 else 0 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, dbl_neighborFinset_inl, Finset.card_disjSum,
    card_ite_singleton, SimpleGraph.card_neighborFinset_eq_degree]

theorem dbl_degree_inr (v : V) :
    (dbl G S).degree (.inr v) = G.degree v + if S v then 1 else 0 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, dbl_neighborFinset_inr, Finset.card_disjSum,
    card_ite_singleton, SimpleGraph.card_neighborFinset_eq_degree, Nat.add_comm]

end Double

/-- Induction on the total deficiency bound `k`: if every degree lies in `[d - k, d]`, then `G`
embeds as an induced subgraph in a connected `d`-regular graph. -/
theorem exists_regular_supergraph_aux (d : ℕ) : ∀ k : ℕ, ∀ {V : Type} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected →
    (∀ v, G.degree v ≤ d) → (∀ v, d ≤ G.degree v + k) →
    ∃ (V' : Type) (_ : Fintype V') (_ : DecidableEq V') (F : SimpleGraph V')
      (_ : DecidableRel F.Adj) (f : V → V'),
      Function.Injective f ∧ (∀ a b, G.Adj a b ↔ F.Adj (f a) (f b)) ∧ F.Connected ∧
        F.IsRegularOfDegree d := by
  intro k
  induction k with
  | zero =>
    intro V _ _ G _ hconn hle hge
    exact ⟨V, inferInstance, inferInstance, G, inferInstance, id, Function.injective_id,
      fun a b => Iff.rfl, hconn, fun v => le_antisymm (hle v) (by simpa using hge v)⟩
  | succ k ih =>
    intro V _ _ G _ hconn hle hge
    by_cases hreg : ∀ v, G.degree v = d
    · exact ⟨V, inferInstance, inferInstance, G, inferInstance, id, Function.injective_id,
        fun a b => Iff.rfl, hconn, hreg⟩
    push Not at hreg
    obtain ⟨v₀, hv₀⟩ := hreg
    have hlt : G.degree v₀ < d := lt_of_le_of_ne (hle v₀) hv₀
    obtain ⟨V', i1, i2, F, i3, f, hf, hadj, hFc, hFreg⟩ :=
      ih (dbl G (fun v => G.degree v < d)) (dbl_connected G _ hconn v₀ hlt)
        (by
          rintro (v | v)
          · rw [dbl_degree_inl]; have := hle v; split_ifs <;> omega
          · rw [dbl_degree_inr]; have := hle v; split_ifs <;> omega)
        (by
          rintro (v | v)
          · rw [dbl_degree_inl]; have := hge v; split_ifs <;> omega
          · rw [dbl_degree_inr]; have := hge v; split_ifs <;> omega)
    exact ⟨V', i1, i2, F, i3, f ∘ Sum.inl, hf.comp Sum.inl_injective,
      fun a b => hadj (.inl a) (.inl b), hFc, hFreg⟩

theorem exists_regular_supergraph {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (d : ℕ) (hconn : G.Connected) (hdeg : ∀ v, G.degree v ≤ d) :
    ∃ (V' : Type) (_ : Fintype V') (_ : DecidableEq V') (F : SimpleGraph V')
      (_ : DecidableRel F.Adj) (f : V → V'),
      Function.Injective f ∧ (∀ a b, G.Adj a b ↔ F.Adj (f a) (f b)) ∧ F.Connected ∧
        F.IsRegularOfDegree d :=
  exists_regular_supergraph_aux d d G hconn hdeg (fun _ => Nat.le_add_left d _)

end BiluLinial.Counterexample
