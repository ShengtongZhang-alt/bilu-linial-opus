/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Counterexample.Defs

/-!
# Definitions for the explicit excess (Part C2)

Blueprint node `C2-defs` (source: `docs/second_order_bilu_linial.tex`, Section 6). As in Part B,
`n : ℕ` parametrizes the degree: `q = n + 2 = d - 1`, `d = n + 3`. The construction reuses the
rooted graphs of Part B (`RGraph`, `attachGraph`, `join`, `tree`) and its signed adjacency
matrices and responses (`IsSignedAdj`, `green`, `copyBlock`).

The threshold is parametrized by `t > 0` (the smaller fixed point of `u ↦ 1 / (R - q u)`):
`R = thr n t = q t + 1/t`, so that `t_+ = 1 / (q t)` is the other fixed point.

* `treeResp n R h`: the response of the complete rooted `q`-ary tree `T_h` at threshold `R`,
  defined by its recursion `g₀ = 1/R`, `g_{h+1} = 1 / (R - q g_h)`.
* `mresp R A o = (g(A) + g(-A)) / 2`: the mean two-sided response.
* `triSeed n h`: the triangle seed — core `⊤` on `Fin 3` (`o, v₁, v₂ = 0, 1, 2`) with
  `q - 2 = n` copies of `T_h` attached at `o` and `q - 1 = n + 1` at `v₁` and at `v₂`.
* `triQ n h j`: `Q₀ = triSeed n h`, `Q_{j+1} = join q Q_j`.
* `triCentre n h L = join d Q_L` (a centre joined to `q + 1` copies of `Q_L`).
* `seedResp3 n R g τ = 1 / (b - 2 / (a - τ))`, `a = R - (q - 1) g`, `b = R - (q - 2) g`: the root
  response of the seed with tree response `g` and triangle sign `τ`.
* `seedMean n t h`: the mean of the two seed responses (`τ = ±1`) at `R = thr n t`, `g = g_h`.
-/

@[expose] public section

namespace BiluLinial.SecondOrder.Explicit

open Matrix BiluLinial.Counterexample

/-- The threshold `R = q t + 1/t`, `q = n + 2`. -/
noncomputable def thr (n : ℕ) (t : ℝ) : ℝ := ((n : ℝ) + 2) * t + 1 / t

/-- The response of the complete rooted `q`-ary tree `T_h` at threshold `R`:
`g₀ = 1/R`, `g_{h+1} = 1 / (R - q g_h)`. -/
noncomputable def treeResp (n : ℕ) (R : ℝ) : ℕ → ℝ
  | 0 => 1 / R
  | h + 1 => 1 / (R - ((n : ℝ) + 2) * treeResp n R h)

/-- The mean two-sided response `(g(A) + g(-A)) / 2` at the vertex `o`, threshold `R`. -/
noncomputable def mresp {V : Type*} [Fintype V] [DecidableEq V] (R : ℝ) (A : Matrix V V ℝ)
    (o : V) : ℝ :=
  (green R A o + green R (-A) o) / 2

/-- Number of trees attached at each triangle vertex: `q - 2 = n` at `o = 0`, `q - 1 = n + 1` at
`v₁ = 1` and `v₂ = 2`. -/
def triMult (n : ℕ) : Fin 3 → ℕ := ![n, n + 1, n + 1]

/-- The triangle seed. Tree copies are indexed by `Σ c : Fin 3, Fin (triMult n c)`; copy `⟨c, i⟩`
is attached at `c`. The root is `o = 0`, of degree `q`. -/
def triSeed (n h : ℕ) : RGraph where
  V := Fin 3 ⊕ ((tree n h).V × (Σ c : Fin 3, Fin (triMult n c)))
  G := attachGraph (⊤ : SimpleGraph (Fin 3)) (tree n h) Sigma.fst
  root := .inl 0

/-- `Q₀ = triSeed n h`, `Q_{j+1} = join q Q_j`. -/
def triQ (n h : ℕ) : ℕ → RGraph
  | 0 => triSeed n h
  | j + 1 => join (n + 2) (triQ n h j)

/-- The final core: a centre joined to the roots of `d = n + 3` copies of `Q_L`. -/
def triCentre (n h L : ℕ) : RGraph := join (n + 3) (triQ n h L)

/-- The seed response `1 / (b - 2 / (a - τ))` with `a = R - (q - 1) g`, `b = R - (q - 2) g`. -/
noncomputable def seedResp3 (n : ℕ) (R g τ : ℝ) : ℝ :=
  1 / ((R - n * g) - 2 / ((R - (n + 1) * g) - τ))

/-- The mean seed response at `R = thr n t` and tree height `h`. -/
noncomputable def seedMean (n : ℕ) (t : ℝ) (h : ℕ) : ℝ :=
  (seedResp3 n (thr n t) (treeResp n (thr n t) h) 1 +
    seedResp3 n (thr n t) (treeResp n (thr n t) h) (-1)) / 2

end BiluLinial.SecondOrder.Explicit
