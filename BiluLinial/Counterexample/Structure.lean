/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Counterexample.Defs

/-!
# Degrees and connectivity of the construction

Blueprint node `B-structure` (source Construction, items 1–4). The core `J = coreGraph n h L` is
connected and has maximum degree at most `d = n + 3`.

`RootedDegLe d X` says every vertex of `X` has degree at most `d` and the root at most `d - 1`
(room for one edge to a parent).
-/

@[expose] public section

namespace BiluLinial.Counterexample

section Attach

variable {K ι : Type} [Fintype K] [DecidableEq K] [Fintype ι] [DecidableEq ι]
  (C : SimpleGraph K) [DecidableRel C.Adj] (Y : RGraph) (att : ι → K)

theorem attach_degree_inl (c : K) :
    (attachGraph C Y att).degree (.inl c) =
      C.degree c + (Finset.univ.filter fun i => att i = c).card := by
  have h : (attachGraph C Y att).neighborFinset (.inl c) =
      (C.neighborFinset c).disjSum ({Y.root} ×ˢ Finset.univ.filter fun i => att i = c) := by
    ext (a | ⟨w, i⟩)
    · simp
    · simp only [SimpleGraph.mem_neighborFinset, attachGraph_adj_inl_inr, Finset.inr_mem_disjSum,
        Finset.mem_product, Finset.mem_singleton, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← SimpleGraph.card_neighborFinset_eq_degree, h, Finset.card_disjSum, Finset.card_product,
    Finset.card_singleton, one_mul, SimpleGraph.card_neighborFinset_eq_degree]

theorem attach_degree_inr (w : Y.V) (i : ι) :
    (attachGraph C Y att).degree (.inr (w, i)) = Y.G.degree w + if w = Y.root then 1 else 0 := by
  have h : (attachGraph C Y att).neighborFinset (.inr (w, i)) =
      (Finset.univ.filter fun a => w = Y.root ∧ att i = a).disjSum
        (Y.G.neighborFinset w ×ˢ {i}) := by
    ext (a | ⟨w', i'⟩)
    · simp
    · simp only [SimpleGraph.mem_neighborFinset, attachGraph_adj_inr_inr, Finset.inr_mem_disjSum,
        Finset.mem_product, Finset.mem_singleton]
      exact ⟨fun h => ⟨h.2, h.1.symm⟩, fun h => ⟨h.2.symm, h.1⟩⟩
  have hc : (Finset.univ.filter fun a => w = Y.root ∧ att i = a).card =
      if w = Y.root then 1 else 0 := by
    split_ifs with hw
    · rw [Finset.card_eq_one]
      exact ⟨att i, by ext a; simp [hw, eq_comm]⟩
    · simp [hw]
  rw [← SimpleGraph.card_neighborFinset_eq_degree, h, Finset.card_disjSum, Finset.card_product,
    Finset.card_singleton, mul_one, SimpleGraph.card_neighborFinset_eq_degree, hc]
  omega

/-- The core `C` sits in `attachGraph C Y att` as the `inl` vertices. -/
def attachInl : C →g attachGraph C Y att where
  toFun := Sum.inl
  map_rel' h := h

/-- Copy `i` of `Y` sits in `attachGraph C Y att` as the vertices `inr (·, i)`. -/
def attachInr (i : ι) : Y.G →g attachGraph C Y att where
  toFun w := Sum.inr (w, i)
  map_rel' h := ⟨rfl, h⟩

theorem attach_connected (hC : C.Connected) (hY : Y.G.Connected) :
    (attachGraph C Y att).Connected := by
  obtain ⟨c₀⟩ := hC.nonempty
  have hl : ∀ a, (attachGraph C Y att).Reachable (.inl c₀) (.inl a) := fun a =>
    (hC.preconnected c₀ a).map (attachInl C Y att)
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨.inl c₀, ?_⟩
  rintro (a | ⟨w, i⟩)
  · exact hl a
  · have h1 : (attachGraph C Y att).Reachable (.inl (att i)) (.inr (Y.root, i)) :=
      SimpleGraph.Adj.reachable (by simp)
    exact ((hl (att i)).trans h1).trans ((hY.preconnected Y.root w).map (attachInr C Y att i))

end Attach

/-- Every vertex has degree at most `d`, and the root has degree at most `d - 1`. -/
def RootedDegLe (d : ℕ) (X : RGraph) : Prop :=
  ∀ v, X.G.degree v + (if v = X.root then 1 else 0) ≤ d

theorem join_degree_inl (k : ℕ) (Y : RGraph) {v : (join k Y).V} (u : Unit)
    (hv : v = Sum.inl u) : (join k Y).G.degree v = k := by
  subst hv
  have h := attach_degree_inl (⊥ : SimpleGraph Unit) Y (fun _ : Fin k => ()) u
  simp at h
  exact h

theorem join_degree_inr (k : ℕ) (Y : RGraph) {v : (join k Y).V} (w : Y.V) (i : Fin k)
    (hv : v = Sum.inr (w, i)) :
    (join k Y).G.degree v = Y.G.degree w + if w = Y.root then 1 else 0 := by
  subst hv
  exact attach_degree_inr (⊥ : SimpleGraph Unit) Y (fun _ : Fin k => ()) w i

theorem join_rootedDegLe {d k : ℕ} {Y : RGraph} (hk : k + 1 ≤ d) (hY : RootedDegLe d Y) :
    RootedDegLe d (join k Y) := by
  rintro (u | ⟨w, i⟩)
  · rw [join_degree_inl k Y u rfl]
    split_ifs <;> omega
  · have hr : ¬ @Eq (join k Y).V (Sum.inr (w, i)) (join k Y).root := Sum.inr_ne_inl
    rw [join_degree_inr k Y w i rfl, ite_eq_right hr, add_zero]
    exact hY w

theorem tree_rootedDegLe (n h : ℕ) : RootedDegLe (n + 3) (tree n h) := by
  induction h with
  | zero =>
    intro v
    have : (tree n 0).G.degree v = 0 := SimpleGraph.bot_degree (V := Unit) v
    split_ifs <;> omega
  | succ h ih => exact join_rootedDegLe (by omega) ih

theorem card_filter_sigma_fst {α : Type} [Fintype α] [DecidableEq α] (β : α → Type)
    [∀ a, Fintype (β a)] (a : α) :
    (Finset.univ.filter fun i : Sigma β => i.1 = a).card = Fintype.card (β a) := by
  have : (Finset.univ.filter fun i : Sigma β => i.1 = a) =
      ({a} : Finset α).sigma fun _ => Finset.univ := by
    ext ⟨a', b⟩
    simp
  rw [this, Finset.card_sigma]
  simp

theorem seedCore_degree_zero : seedCore.degree 0 = 1 := by decide

theorem seedCore_degree_one : seedCore.degree 1 = 3 := by decide

theorem seedCore_degree_two : seedCore.degree 2 = 2 := by decide

theorem seedCore_degree_three : seedCore.degree 3 = 2 := by decide

theorem seedCore_degree_le (n : ℕ) (c : Fin 4) : seedCore.degree c + seedMult n c ≤ n + 3 := by
  fin_cases c <;> simp [seedMult, seedCore_degree_zero, seedCore_degree_one, seedCore_degree_two,
    seedCore_degree_three] <;> omega

theorem seedCore_degree_root (n : ℕ) : seedCore.degree 0 + seedMult n 0 + 1 = n + 3 := by
  have hm : seedMult n 0 = n + 1 := rfl
  rw [seedCore_degree_zero, hm]
  omega

theorem seed_rootedDegLe (n h : ℕ) : RootedDegLe (n + 3) (seed n h) := by
  rintro (c | ⟨w, i⟩)
  · have hd : ∀ v : (seed n h).V, v = Sum.inl c →
        (seed n h).G.degree v = seedCore.degree c + seedMult n c := by
      rintro v rfl
      have := attach_degree_inl seedCore (tree n h)
        (Sigma.fst : (Σ c : Fin 4, Fin (seedMult n c)) → Fin 4) c
      rw [card_filter_sigma_fst (fun c => Fin (seedMult n c)), Fintype.card_fin] at this
      exact this
    rw [hd _ rfl]
    split_ifs with hc
    · obtain rfl : c = 0 := Sum.inl_injective hc
      exact (seedCore_degree_root n).le
    · exact seedCore_degree_le n c
  · have hd : ∀ v : (seed n h).V, v = Sum.inr (w, i) →
        (seed n h).G.degree v = (tree n h).G.degree w + if w = (tree n h).root then 1 else 0 := by
      rintro v rfl
      exact attach_degree_inr seedCore (tree n h) Sigma.fst w i
    have hr : ¬ @Eq (seed n h).V (Sum.inr (w, i)) (seed n h).root := Sum.inr_ne_inl
    rw [hd _ rfl, ite_eq_right hr, add_zero]
    exact tree_rootedDegLe n h w

theorem Qgraph_rootedDegLe (n h j : ℕ) : RootedDegLe (n + 3) (Qgraph n h j) := by
  induction j with
  | zero => exact seed_rootedDegLe n h
  | succ j ih => exact join_rootedDegLe (by omega) ih

theorem coreGraph_degree_le (n h L : ℕ) (v : (coreGraph n h L).V) :
    (coreGraph n h L).G.degree v ≤ n + 3 := by
  rcases v with u | ⟨w, i⟩
  · exact (join_degree_inl (n + 3) (Qgraph n h L) u rfl).le
  · exact (join_degree_inr (n + 3) (Qgraph n h L) w i rfl).trans_le
      (Qgraph_rootedDegLe n h L w)

theorem bot_unit_connected : (⊥ : SimpleGraph Unit).Connected :=
  (SimpleGraph.connected_iff_exists_forall_reachable _).2
    ⟨(), fun w => by cases w; exact SimpleGraph.Reachable.refl _⟩

theorem join_connected {k : ℕ} {Y : RGraph} (hY : Y.G.Connected) : (join k Y).G.Connected :=
  attach_connected (⊥ : SimpleGraph Unit) Y (fun _ : Fin k => ()) bot_unit_connected hY

theorem tree_connected (n h : ℕ) : (tree n h).G.Connected := by
  induction h with
  | zero => exact bot_unit_connected
  | succ h ih => exact join_connected ih

theorem seedCore_connected : seedCore.Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  have h01 : seedCore.Adj 0 1 := by decide
  have h12 : seedCore.Adj 1 2 := by decide
  have h13 : seedCore.Adj 1 3 := by decide
  refine ⟨0, fun w => ?_⟩
  fin_cases w
  · exact SimpleGraph.Reachable.refl _
  · exact h01.reachable
  · exact h01.reachable.trans h12.reachable
  · exact h01.reachable.trans h13.reachable

theorem seed_connected (n h : ℕ) : (seed n h).G.Connected :=
  attach_connected seedCore (tree n h) Sigma.fst seedCore_connected (tree_connected n h)

theorem Qgraph_connected (n h j : ℕ) : (Qgraph n h j).G.Connected := by
  induction j with
  | zero => exact seed_connected n h
  | succ j ih => exact join_connected ih

theorem coreGraph_connected (n h L : ℕ) : (coreGraph n h L).G.Connected :=
  join_connected (Qgraph_connected n h L)

end BiluLinial.Counterexample
