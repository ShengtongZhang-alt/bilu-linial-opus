/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecA.Defs

/-!
# Definitions of the endpoint calculus (E1)

The fibre polynomial, the fibre derivatives `𝒟_j`, `g*` and the rank-two edge perturbation used
by the nodes `A-RANK2` and `A-E1` of `BiluLinial.Tight.SecA.Endpoint`.
-/

@[expose] public section

namespace BiluLinial.Tight.SecA

open Matrix Polynomial

/-- `δ(t) = 1 + 2 t a x - t² a² (g_vv g_ii - x²)` (`x = G_vi`). -/
noncomputable def fibreDelta (a x gvv gii : ℝ) : ℝ[X] :=
  1 + C (2 * a * x) * X - C (a ^ 2 * (gvv * gii - x ^ 2)) * X ^ 2

/-- The fibre polynomial `Π(t) = δ₊(t)^{p-1} δ₋(t)^p (x - t a (g_vv g_ii - x²))`, with
`(x, g_vv, g_ii) = (G⁺_vi, G⁺_vv, G⁺_ii)` and `(y, h_vv, h_ii)` the minus entries. -/
noncomputable def fibrePoly (p : ℕ) (a x gvv gii y hvv hii : ℝ) : ℝ[X] :=
  fibreDelta a x gvv gii ^ (p - 1) * fibreDelta a (-y) hvv hii ^ p *
    (C x - C (a * (gvv * gii - x ^ 2)) * X)

section E1

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- `𝒟_j G⁺_vi = j! [t^j] Π` at a signing. -/
noncomputable def fibreD (p : ℕ) (a : ℝ) (yp ym : V → ℝ) (S : Finset V) (v i : V) (j : ℕ)
    (σ : Config V) : ℝ :=
  j.factorial * (fibrePoly p a (greenP G a 1 yp σ S v i) (greenP G a 1 yp σ S v v)
    (greenP G a 1 yp σ S i i) (greenP G a (-1) ym σ S v i) (greenP G a (-1) ym σ S v v)
    (greenP G a (-1) ym σ S i i)).coeff j

/-- `g* = max_± max(G^±_vv, G^±_ii)`. -/
noncomputable def gStar (a : ℝ) (yp ym : V → ℝ) (S : Finset V) (v i : V) (σ : Config V) : ℝ :=
  max (max (greenP G a 1 yp σ S v v) (greenP G a 1 yp σ S i i))
    (max (greenP G a (-1) ym σ S v v) (greenP G a (-1) ym σ S i i))

end E1

section Rank2

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The symmetric rank-two edge perturbation `e_v e_iᵀ + e_i e_vᵀ`. -/
def edgeE (v i : n) : Matrix n n ℝ := Matrix.single v i 1 + Matrix.single i v 1

end Rank2

end BiluLinial.Tight.SecA
