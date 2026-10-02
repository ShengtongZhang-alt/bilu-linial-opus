/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.ChallengeDefs

/-!
# Definitions for Theorem B (the counterexample in every degree)

Source: `docs/COUNTEREXAMPLE_ALL_DEGREES.md`. Throughout, `n : ℕ` parametrizes the degree:
`q = n + 2 = d - 1` and `d = n + 3`, so no natural-number subtraction appears.

* `RGraph`: a finite rooted simple graph.
* `attachGraph C Y att`: a core graph `C` on `K` together with, for every `i : ι`, a copy
  `Y × {i}` of the rooted graph `Y`, whose root is joined to the core vertex `att i`.
  Its vertex type is `K ⊕ (Y.V × ι)`.
* `join k Y`: a new root joined to the roots of `k` copies of `Y` (`B(Y, …, Y)` in the source).
* `tree n h`: the complete rooted `q`-ary tree `T_h` of height `h`.
* `seed n h`: the seed `H_h` — core `o, v₀, v₁, v₂` = `0, 1, 2, 3` with edges `o v₀`, `v₀ v₁`,
  `v₀ v₂`, `v₁ v₂`, and `q - 1 = n + 1` copies of `T_h` attached at `o, v₁, v₂`, `q - 2 = n` at `v₀`.
* `Qgraph n h j`: `Q₀ = H_h`, `Q_{j+1} = join q Q_j`.
* `coreGraph n h L`: `J = join d Q_L`.
* `IsSignedAdj G A`: `A` is a signed adjacency matrix of `G` (symmetric, `A u v = ±1` on edges,
  `0` elsewhere).
* `green r A o = ((r I - A)⁻¹)_{oo}` and the normalized response `tval`.
-/

@[expose] public section

namespace BiluLinial.Counterexample

open Matrix

/-- A finite rooted simple graph with decidable equality and adjacency. -/
structure RGraph where
  /-- the vertex type -/
  V : Type
  [fintype : Fintype V]
  [decEq : DecidableEq V]
  /-- the graph -/
  G : SimpleGraph V
  [decAdj : DecidableRel G.Adj]
  /-- the root -/
  root : V

attribute [instance] RGraph.fintype RGraph.decEq RGraph.decAdj

section Attach

variable {K ι : Type} (C : SimpleGraph K) (Y : RGraph) (att : ι → K)

/-- Adjacency relation of `attachGraph`. -/
def attachAdj : K ⊕ (Y.V × ι) → K ⊕ (Y.V × ι) → Prop
  | .inl a, .inl b => C.Adj a b
  | .inl a, .inr p => p.1 = Y.root ∧ att p.2 = a
  | .inr p, .inl a => p.1 = Y.root ∧ att p.2 = a
  | .inr p, .inr p' => p.2 = p'.2 ∧ Y.G.Adj p.1 p'.1

/-- The core graph `C` on `K` with a copy `Y × {i}` of `Y` for each `i : ι`, the root of copy `i`
joined by one edge to the core vertex `att i`. -/
def attachGraph : SimpleGraph (K ⊕ (Y.V × ι)) where
  Adj := attachAdj C Y att
  symm := ⟨by
    rintro (a | ⟨w, i⟩) (b | ⟨w', i'⟩) h <;> simp only [attachAdj] at h ⊢
    · exact C.adj_symm h
    · exact h
    · exact h
    · exact ⟨h.1.symm, Y.G.adj_symm h.2⟩⟩
  loopless := ⟨by
    rintro (a | ⟨w, i⟩) h <;> simp only [attachAdj] at h
    · exact C.irrefl h
    · exact Y.G.irrefl h.2⟩

@[simp] theorem attachGraph_adj_inl_inl (a b : K) :
    (attachGraph C Y att).Adj (.inl a) (.inl b) ↔ C.Adj a b := Iff.rfl

@[simp] theorem attachGraph_adj_inl_inr (a : K) (p : Y.V × ι) :
    (attachGraph C Y att).Adj (.inl a) (.inr p) ↔ p.1 = Y.root ∧ att p.2 = a := Iff.rfl

@[simp] theorem attachGraph_adj_inr_inl (p : Y.V × ι) (a : K) :
    (attachGraph C Y att).Adj (.inr p) (.inl a) ↔ p.1 = Y.root ∧ att p.2 = a := Iff.rfl

@[simp] theorem attachGraph_adj_inr_inr (p p' : Y.V × ι) :
    (attachGraph C Y att).Adj (.inr p) (.inr p') ↔ p.2 = p'.2 ∧ Y.G.Adj p.1 p'.1 := Iff.rfl

instance attachGraph.decidableAdj [DecidableEq K] [DecidableEq ι] [DecidableRel C.Adj] :
    DecidableRel (attachGraph C Y att).Adj
  | .inl a, .inl b => inferInstanceAs (Decidable (C.Adj a b))
  | .inl a, .inr p => inferInstanceAs (Decidable (p.1 = Y.root ∧ att p.2 = a))
  | .inr p, .inl a => inferInstanceAs (Decidable (p.1 = Y.root ∧ att p.2 = a))
  | .inr p, .inr p' => inferInstanceAs (Decidable (p.2 = p'.2 ∧ Y.G.Adj p.1 p'.1))

end Attach

/-- `join k Y = B(Y, …, Y)`: a new root `inl ()` joined to the roots of `k` disjoint copies of
`Y`. -/
def join (k : ℕ) (Y : RGraph) : RGraph where
  V := Unit ⊕ (Y.V × Fin k)
  G := attachGraph ⊥ Y (fun _ => ())
  root := .inl ()

/-- The complete rooted `q`-ary tree `T_h` of height `h`, `q = n + 2`. -/
def tree (n : ℕ) : ℕ → RGraph
  | 0 => { V := Unit, G := ⊥, root := () }
  | h + 1 => join (n + 2) (tree n h)

/-- The core of the seed: `o = 0`, `v₀ = 1`, `v₁ = 2`, `v₂ = 3`, with edges `o v₀`, `v₀ v₁`, `v₀ v₂`,
`v₁ v₂` (a triangle `v₀ v₁ v₂` with the pendant root `o`). -/
def seedCore : SimpleGraph (Fin 4) where
  Adj a b := (a, b) ∈ ({(0, 1), (1, 0), (1, 2), (2, 1), (1, 3), (3, 1), (2, 3), (3, 2)} :
    Finset (Fin 4 × Fin 4))
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

instance : DecidableRel seedCore.Adj := fun a b =>
  inferInstanceAs (Decidable ((a, b) ∈ ({(0, 1), (1, 0), (1, 2), (2, 1), (1, 3), (3, 1), (2, 3),
    (3, 2)} : Finset (Fin 4 × Fin 4))))

/-- Number of trees attached at each core vertex of the seed: `q - 1 = n + 1` at `o, v₁, v₂` and
`q - 2 = n` at `v₀`. -/
def seedMult (n : ℕ) : Fin 4 → ℕ := ![n + 1, n, n + 1, n + 1]

/-- The seed `H_h`. Tree copies are indexed by `Σ c : Fin 4, Fin (seedMult n c)`; copy `⟨c, i⟩` is
attached at `c`. -/
def seed (n h : ℕ) : RGraph where
  V := Fin 4 ⊕ ((tree n h).V × (Σ c : Fin 4, Fin (seedMult n c)))
  G := attachGraph seedCore (tree n h) Sigma.fst
  root := .inl 0

/-- `Q₀ = H_h`, `Q_{j+1} = B(Q_j, …, Q_j)` with `q = n + 2` copies. -/
def Qgraph (n h : ℕ) : ℕ → RGraph
  | 0 => seed n h
  | j + 1 => join (n + 2) (Qgraph n h j)

/-- The core `J = J(h, L)`: a centre joined to the roots of `d = n + 3` copies of `Q_L`. -/
def coreGraph (n h L : ℕ) : RGraph := join (n + 3) (Qgraph n h L)

/-- `A` is a signed adjacency matrix of `G`: symmetric, with `A u v = ±1` (i.e. `A u v ^ 2 = 1`) on
edges and `0` off edges (in particular on the diagonal). -/
structure IsSignedAdj {V : Type*} (G : SimpleGraph V) (A : Matrix V V ℝ) : Prop where
  isHermitian : A.IsHermitian
  sq_eq_one : ∀ u v, G.Adj u v → A u v ^ 2 = 1
  eq_zero : ∀ u v, ¬ G.Adj u v → A u v = 0

/-- The response `g(X, A) = ((r I - A)⁻¹)_{oo}` at the vertex `o`. -/
noncomputable def green {V : Type*} [Fintype V] [DecidableEq V] (r : ℝ) (A : Matrix V V ℝ)
    (o : V) : ℝ :=
  (r • (1 : Matrix V V ℝ) - A)⁻¹ o o

/-- The Ramanujan radius `r = 2 √q`, `q = n + 2`. -/
noncomputable def rad (n : ℕ) : ℝ := 2 * Real.sqrt (n + 2)

/-- The normalized response `t = (√q / 2) (g₁ + g₋₁)` (the infinite `q`-ary tree has `t = 1`). -/
noncomputable def tval (n : ℕ) {V : Type*} [Fintype V] [DecidableEq V] (A : Matrix V V ℝ)
    (o : V) : ℝ :=
  Real.sqrt (n + 2) / 2 * (green (rad n) A o + green (rad n) (-A) o)

/-- The block of a matrix on the attach type belonging to copy `i` of `Y`. -/
def copyBlock {K ι : Type} (Y : RGraph) (A : Matrix (K ⊕ (Y.V × ι)) (K ⊕ (Y.V × ι)) ℝ) (i : ι) :
    Matrix Y.V Y.V ℝ :=
  A.submatrix (fun w => .inr (w, i)) (fun w => .inr (w, i))

/-- The coupling block between the core and the attached copies: entry `s i` between the core
vertex `att i` and the root `o` of copy `i`, zero elsewhere. -/
def couple {K W ι : Type*} [DecidableEq K] [DecidableEq W] (o : W) (att : ι → K) (s : ι → ℝ) :
    Matrix K (W × ι) ℝ :=
  Matrix.of fun c p => if p.1 = o ∧ att p.2 = c then s p.2 else 0

/-- Embedding of `join 1 Y` into `join k Y` onto the root and copy `i`. -/
def joinSub (Y : RGraph) (k : ℕ) (i : Fin k) : (join 1 Y).V → (join k Y).V
  | .inl u => .inl u
  | .inr p => .inr (p.1, i)

/-- The response of `T_h`: `(h + 1) / ((h + 2) √q)` (Step 3). -/
noncomputable def treeGreen (n h : ℕ) : ℝ := (h + 1) / ((h + 2) * Real.sqrt (n + 2))

/-- The seed response `u_τ = 1 / (a - 1 / (b - 2 / (a - τ)))` with `a = r - (q - 1) g`,
`b = r - (q - 2) g`, as a function of the tree response `g` (Step 6). -/
noncomputable def seedResp (n : ℕ) (g τ : ℝ) : ℝ :=
  1 / ((rad n - (n + 1) * g) - 1 / ((rad n - n * g) - 2 / ((rad n - (n + 1) * g) - τ)))

/-- The normalized seed response `t(h) = (√q / 2) (u₁ + u₋₁)`. -/
noncomputable def tseed (n h : ℕ) : ℝ :=
  Real.sqrt (n + 2) / 2 * (seedResp n (treeGreen n h) 1 + seedResp n (treeGreen n h) (-1))

end BiluLinial.Counterexample
