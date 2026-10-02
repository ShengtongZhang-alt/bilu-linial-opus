/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.ChallengeDefs

/-!
# Definitions for the near-Ramanujan upper bound

Part D of the blueprint (`docs/BLUEPRINT.md`), source `docs/second_order_bilu_linial_tight.tex`,
Section 1 ("Upper bound").

As in Part A, we fix an ambient graph `G` on a finite type `V`; an induced subgraph `H = G[S]` is
represented by its vertex set `S : Finset V`, and a random signing is a `Config V` (a sign for every
unordered pair; only the edges inside `S` matter). Expectations are ratios of plain sums over
`Config V`.

**Normalized precisions.** The source's paired law uses the physical precisions
`P^± = diag Z(y^±) ± a A_σ` with `Z_i(y) = (1 + Σ_{j ∼ i} c_ij)/y_i`. Congruence by
`(diag y)^{1/2}` turns them into the normalized precisions
`P̃^± = diag D(y^±) ± a Y^{1/2} A_σ Y^{1/2}`, `D_i = y_i Z_i = 1 + Σ_{j ∼ i} c_ij`, which make sense
at zero sources (a zero source is an isolated identity row) and multiply every weight by the same
source-dependent factor. We use `P̃^±` throughout (`precN`), padded with the identity outside `S`,
so that determinants, positivity and inverse entries on `S` agree with those of the `S × S` block.
The normalized inverse diagonal is `h_i^± = (P̃^±)⁻¹_ii = G^±_ii / y_i^±` (`hN`).

**Parameters.** `q = d - 1`, `Δ = 4/p`, `R² = 4q + Δ`, `a = 1/R`, `η₀` the positive root of
`q η₀²/(1 - η₀) = Δ`, `τ_* = (1 - η₀)/q`, `s = (1 + q τ_*)/(1 - τ_*)`, `r = 1 + η₀/2`.
-/

@[expose] public section

namespace BiluLinial.Tight

open Matrix

/-- A sign for every unordered pair of vertices; only the edges inside the current vertex set
matter. -/
abbrev Config (V : Type*) := Sym2 V → ℤˣ

/-- The sign `σ(uw)` as a real number. -/
def sgn {V : Type*} (σ : Config V) (u w : V) : ℝ := ((σ s(u, w) : ℤ) : ℝ)

/-- `c(x) = (√(1 + 4x) - 1)/2`, the nonnegative root of `c(1 + c) = x` for `x ≥ 0`. -/
noncomputable def cRoot (x : ℝ) : ℝ := (Real.sqrt (1 + 4 * x) - 1) / 2

/-- The source cube `[0, t]^V`. -/
def InCube {V : Type*} (t : ℝ) (y : V → ℝ) : Prop := ∀ i, 0 ≤ y i ∧ y i ≤ t

section Law

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The neighbours of `v` inside `S`. -/
def nbhd (S : Finset V) (v : V) : Finset V := S.filter (G.Adj v)

/-- `c_ij = c(a² y_i y_j)`, i.e. `c_ij (1 + c_ij) = a² y_i y_j`. -/
noncomputable def cEdge (a : ℝ) (y : V → ℝ) (i j : V) : ℝ := cRoot (a ^ 2 * y i * y j)

/-- `τ_ij = c_ij / (1 + c_ij)`. -/
noncomputable def τEdge (a : ℝ) (y : V → ℝ) (i j : V) : ℝ :=
  cEdge a y i j / (1 + cEdge a y i j)

/-- `D_i(y) = y_i Z_i(y) = 1 + Σ_{j ∈ N_S(i)} c_ij`. -/
noncomputable def diagD (a : ℝ) (y : V → ℝ) (S : Finset V) (i : V) : ℝ :=
  1 + ∑ j ∈ nbhd G S i, cEdge a y i j

/-- The physical precision diagonal `Z_i(y) = D_i(y) / y_i` (junk value `0` at a zero source). -/
noncomputable def precZ (a : ℝ) (y : V → ℝ) (S : Finset V) (i : V) : ℝ :=
  diagD G a y S i / y i

/-- The normalized precision `P̃^τ = diag D(y) + τ a Y^{1/2} A_σ(G[S]) Y^{1/2}` on `S × S`, padded
with the identity outside `S`. `τ = 1` gives `P̃⁺`, `τ = -1` gives `P̃⁻`. -/
noncomputable def precN (a τ : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) : Matrix V V ℝ :=
  Matrix.of fun u w =>
    if u = w then (if u ∈ S then diagD G a y S u else 1)
    else if u ∈ S ∧ w ∈ S ∧ G.Adj u w then
      τ * a * (Real.sqrt (y u) * Real.sqrt (y w)) * sgn σ u w
    else 0

open Classical in
/-- The paired weight `W(σ) = 1{P̃⁺ ≻ 0, P̃⁻ ≻ 0} (det P̃⁺ det P̃⁻)^p`, with sources `y⁺ = yp` and
`y⁻ = ym`. -/
noncomputable def wt (p : ℕ) (a : ℝ) (yp ym : V → ℝ) (σ : Config V) (S : Finset V) : ℝ :=
  if (precN G a 1 yp σ S).PosDef ∧ (precN G a (-1) ym σ S).PosDef then
    ((precN G a 1 yp σ S).det * (precN G a (-1) ym σ S).det) ^ p
  else 0

/-- The partition function `Σ_σ W(σ)` (unnormalized). -/
noncomputable def Zw (p : ℕ) (a : ℝ) (yp ym : V → ℝ) (S : Finset V) : ℝ :=
  ∑ σ : Config V, wt G p a yp ym σ S

/-- The expectation `E f = Σ_σ W(σ) f(σ) / Σ_σ W(σ)` under the paired law. -/
noncomputable def lawE (p : ℕ) (a : ℝ) (yp ym : V → ℝ) (S : Finset V) (f : Config V → ℝ) : ℝ :=
  (∑ σ : Config V, wt G p a yp ym σ S * f σ) / Zw G p a yp ym S

/-- The normalized inverse diagonal `h_i^τ = (P̃^τ)⁻¹_ii`. Only its values on supported signings
matter. -/
noncomputable def hN (a τ : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) (i : V) : ℝ :=
  (precN G a τ y σ S)⁻¹ i i

end Law

/-! ### Parameters, as functions of `d` and `p` -/

/-- `q = d - 1` (real subtraction). -/
noncomputable def qOf (d : ℕ) : ℝ := (d : ℝ) - 1

/-- `Δ = 4/p`. -/
noncomputable def ΔOf (p : ℕ) : ℝ := 4 / (p : ℝ)

/-- `R² = 4q + Δ`. -/
noncomputable def RsqOf (d p : ℕ) : ℝ := 4 * qOf d + ΔOf p

/-- `a = 1/R`. -/
noncomputable def aOf (d p : ℕ) : ℝ := 1 / Real.sqrt (RsqOf d p)

/-- `η₀`, the positive root of `q η₀² + Δ η₀ - Δ = 0`, i.e. of `q η₀²/(1 - η₀) = Δ`. -/
noncomputable def η0Of (d p : ℕ) : ℝ :=
  (Real.sqrt (ΔOf p ^ 2 + 4 * qOf d * ΔOf p) - ΔOf p) / (2 * qOf d)

/-- `τ_* = (1 - η₀)/q`. -/
noncomputable def τsOf (d p : ℕ) : ℝ := (1 - η0Of d p) / qOf d

/-- The source cap `s = (1 + q τ_*)/(1 - τ_*)`. -/
noncomputable def sOf (d p : ℕ) : ℝ := (1 + qOf d * τsOf d p) / (1 - τsOf d p)

/-- The first-mean cap `r = 1 + η₀/2`. -/
noncomputable def rOf (d p : ℕ) : ℝ := 1 + η0Of d p / 2

section Inv

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- `E h_i^+` under the paired law with parameters `(d, p)`. -/
noncomputable def meanPlus (d p : ℕ) (yp ym : V → ℝ) (S : Finset V) (i : V) : ℝ :=
  lawE G p (aOf d p) yp ym S (fun σ => hN G (aOf d p) 1 yp σ S i)

/-- `E h_i^-` under the paired law with parameters `(d, p)`. -/
noncomputable def meanMinus (d p : ℕ) (yp ym : V → ℝ) (S : Finset V) (i : V) : ℝ :=
  lawE G p (aOf d p) yp ym S (fun σ => hN G (aOf d p) (-1) ym σ S i)

/-- The capped-law invariant for `H = G[S]` (source Section 1.1, last paragraph): for all sources
`y^± ∈ [0, s]^V` the paired law exists and every normalized first mean is at most `r`. -/
def TInv (d p : ℕ) (S : Finset V) : Prop :=
  ∀ yp ym : V → ℝ, InCube (sOf d p) yp → InCube (sOf d p) ym →
    0 < Zw G p (aOf d p) yp ym S ∧
      ∀ i ∈ S, meanPlus G d p yp ym S i ≤ rOf d p ∧ meanMinus G d p yp ym S i ≤ rOf d p

end Inv

end BiluLinial.Tight
