/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.Contact.Defs
public import BiluLinial.Tight.Compare.Multi
public import BiluLinial.Tight.Compare.Endpoint

/-!
# Vocabulary of Section 1.2 (endpoint comparison and concentration)

Definitions used by the statements of `docs/tight/BP_SECA.md` (source
`docs/second_order_bilu_linial_tight.tex`, lines 237–625; audit `docs/tight/AUDIT_A.md`).

* `RegA d p`: the regime (R) of AUDIT-A §1.1 (`TRegime d p`, `log d ≥ 400`, `120 log d ≤ p`).
  Every analytic node of the section is stated uniformly for `RegA d p`; `eventually_regA`
  (`SecA/Reg.lean`) puts `p = ⌊c₀ d^{2/17}⌋` in the regime for large `d`.
* `uOf d p = (p/d)^{1/3}`, `b0Of d p = ε + p⁴/d + 1/d` (the paper's `b` without its constant),
  `kStarA d p = ⌈16 p / log d⌉`.

Theorems of the section live in the namespace `BiluLinial.Tight.SecA` (or in the namespaces of
the structures `RegA`, `CapPoint` defined here), to avoid clashes with the other drafters.
* `CapPoint d p`: a capped context `CapCtx` bundled with its graph and a point `(y⁺, y⁻)` of the
  capped cube `[0, λ s]^V` (AUDIT-A (CSL)); every graph-level node quantifies over it.
  `Contact d p` maps to it (`Contact.toCapPoint`).
* `hzN`: the normalized shifted inverse diagonal `((P̃ + z Y)⁻¹)_ii = X_{z,ii}/y_i` (`= 1` at a
  zero source).
* `insF`: the insertion factor `F_H = E_{ν_K} 𝖱 Φ` (`ν_K` = own core law `coreE`).
* Star observables on `ℝ^N`: `f1Obs` (`(tr A - q_A) α^{p-1} β^p`), `wK` (`tr A²/(1 + tr A)`),
  `quadFn` (quadratic functions), `clipObs` (`g α₊^{e₁} β₊^{e₂}`).
* `AgreeOff v σ σ'`: the signings agree off the edges at `v` (core-measurability).
-/

@[expose] public section

namespace BiluLinial.Tight

open Matrix

universe u

/-! ### The regime -/

/-- The regime (R) of Section 1.2 (AUDIT-A §1.1): the structural regime `TRegime d p`
(`p ≥ 10⁶`, `p^17 ≤ d²`, hence `p ≤ d^{1/7}`), `log d ≥ 400` and `120 log d ≤ p`. -/
structure RegA (d p : ℕ) : Prop where
  treg : TRegime d p
  logd : 400 ≤ Real.log d
  plog : 120 * Real.log d ≤ p

/-- `u = (p/d)^{1/3}`. -/
noncomputable def uOf (d p : ℕ) : ℝ := ((p : ℝ) / d) ^ ((1 : ℝ) / 3)

/-- `b₀ = ε + p⁴/d + 1/d`, `ε = r - 1 = η₀/2` (the paper's `b` of line 400 without its `C`). -/
noncomputable def b0Of (d p : ℕ) : ℝ := epsP d p + (p : ℝ) ^ 4 / d + 1 / d

/-- `k_* = ⌈16 p / log d⌉`, the comparison depth of (E4)–(E6) (the same as `kStar` of
`Tight/SecC/Defs.lean`; renamed here to avoid a name clash). -/
noncomputable def kStarA (d p : ℕ) : ℕ := ⌈16 * (p : ℝ) / Real.log d⌉₊

/-! ### Capped points -/

/-- A capped context (`CapCtx`, AUDIT-A (CSL)) bundled with its graph and a point `(y⁺, y⁻)` of
the capped cube `[0, λ s]^V`. -/
structure CapPoint (d p : ℕ) where
  /-- vertex type -/
  V : Type u
  [fin : Fintype V]
  [dec : DecidableEq V]
  /-- ambient graph -/
  G : SimpleGraph V
  [adj : DecidableRel G.Adj]
  /-- current vertex set -/
  S : Finset V
  /-- stage of the expanding cube -/
  lam : ℝ
  /-- plus sources -/
  yp : V → ℝ
  /-- minus sources -/
  ym : V → ℝ
  ctx : CapCtx G d p S lam
  hyp : InCube (lam * sOf d p) yp
  hym : InCube (lam * sOf d p) ym

attribute [instance] CapPoint.fin CapPoint.dec CapPoint.adj

/-- The normalized shifted inverse diagonal `((P̃^τ + z Y)⁻¹)_ii`, i.e. `X^τ_{z,ii}/y_i` with
`X_z = (P^τ + z I)⁻¹` physical (`1` at a zero source). -/
noncomputable def hzN {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (a τ z : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) (i : V) : ℝ :=
  (precN G a τ y σ S + z • srcDiag y S)⁻¹ i i

/-- The insertion factor `F_H = E_{ν_K} 𝖱 Φ` at the root `v` (`ν_K` the own core law). -/
noncomputable def insF {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (p : ℕ) (a : ℝ) (yp ym : V → ℝ) (S : Finset V) (v : V) : ℝ :=
  coreE G p a yp ym S v
    (fun σ => radE (starPhi p (rootMat G a 1 yp σ S v) (rootMat G a (-1) ym σ S v)))

/-- The shifted root matrix `M_z = (a²/Z_v) C_z[N,N]`, `C_z = (P^τ_{-v} + z I)⁻¹` (physical,
inherited core; `a²/Z_v = a² y_v/D_v`). For `z = 0` it is the root matrix `rootMat`. -/
noncomputable def rootMzG {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (a τ z : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) (v : V) :
    Matrix (nbhd G S v) (nbhd G S v) ℝ :=
  Matrix.of fun i j => a ^ 2 * y v / diagD G a y S v * coreShift G a τ z y σ S v i j

/-- `σ` and `σ'` agree on every pair not containing `v` (so they have the same core). -/
def AgreeOff {V : Type*} (v : V) (σ σ' : Config V) : Prop := ∀ e : Sym2 V, v ∉ e → σ e = σ' e

namespace CapPoint

variable {d p : ℕ} (cp : CapPoint.{u} d p)

/-- Expectation under the paired law of `H = G[S]` at `(y⁺, y⁻)`. -/
noncomputable def E (f : Config cp.V → ℝ) : ℝ := lawE cp.G p (aOf d p) cp.yp cp.ym cp.S f

/-- Physical `G⁺`. -/
noncomputable def gp (σ : Config cp.V) (i j : cp.V) : ℝ :=
  greenP cp.G (aOf d p) 1 cp.yp σ cp.S i j

/-- Physical `G⁻`. -/
noncomputable def gm (σ : Config cp.V) (i j : cp.V) : ℝ :=
  greenP cp.G (aOf d p) (-1) cp.ym σ cp.S i j

/-- Normalized `h⁺_i = G⁺_ii / y⁺_i`. -/
noncomputable def hp (σ : Config cp.V) (i : cp.V) : ℝ := hN cp.G (aOf d p) 1 cp.yp σ cp.S i

/-- Normalized `h⁻_i`. -/
noncomputable def hm (σ : Config cp.V) (i : cp.V) : ℝ := hN cp.G (aOf d p) (-1) cp.ym σ cp.S i

/-- `N = N_S(v)`. -/
def N (v : cp.V) : Finset cp.V := nbhd cp.G cp.S v

/-- `A = (a²/Z⁺_v) G_K⁺[N,N]`. -/
noncomputable def A (σ : Config cp.V) (v : cp.V) : Matrix (cp.N v) (cp.N v) ℝ :=
  rootMat cp.G (aOf d p) 1 cp.yp σ cp.S v

/-- `B = (a²/Z⁻_v) G_K⁻[N,N]`. -/
noncomputable def B (σ : Config cp.V) (v : cp.V) : Matrix (cp.N v) (cp.N v) ℝ :=
  rootMat cp.G (aOf d p) (-1) cp.ym σ cp.S v

/-- `Θ = tr(A² + B²)`. -/
noncomputable def Theta (σ : Config cp.V) (v : cp.V) : ℝ :=
  (cp.A σ v * cp.A σ v + cp.B σ v * cp.B σ v).trace

/-- `τ⁺_v = Z⁺_v G⁺_vv = D⁺_v h⁺_v` (the paper's `t`). -/
noncomputable def taup (σ : Config cp.V) (v : cp.V) : ℝ :=
  diagD cp.G (aOf d p) cp.yp cp.S v * cp.hp σ v

/-- `τ⁻_v = D⁻_v h⁻_v`. -/
noncomputable def taum (σ : Config cp.V) (v : cp.V) : ℝ :=
  diagD cp.G (aOf d p) cp.ym cp.S v * cp.hm σ v

/-- Expectation under the own core law `ν_K` at the root `v`. -/
noncomputable def coreE (v : cp.V) (f : Config cp.V → ℝ) : ℝ :=
  BiluLinial.Tight.coreE cp.G p (aOf d p) cp.yp cp.ym cp.S v f

/-- The insertion factor `F_H` at the root `v`. -/
noncomputable def FH (v : cp.V) : ℝ := insF cp.G p (aOf d p) cp.yp cp.ym cp.S v

/-- `ρ` bounds every first-mean deficit: `1 - E h_i^± ≤ ρ` for `i ∈ S`. -/
def DefLe (ρ : ℝ) : Prop :=
  ∀ i ∈ cp.S, 1 - cp.E (fun σ => cp.hp σ i) ≤ ρ ∧ 1 - cp.E (fun σ => cp.hm σ i) ≤ ρ

/-- Normalized shifted diagonals `X⁺_{z,ii}/y⁺_i`. -/
noncomputable def hzp (z : ℝ) (σ : Config cp.V) (i : cp.V) : ℝ :=
  hzN cp.G (aOf d p) 1 z cp.yp σ cp.S i

/-- Normalized shifted diagonals `X⁻_{z,ii}/y⁻_i`. -/
noncomputable def hzm (z : ℝ) (σ : Config cp.V) (i : cp.V) : ℝ :=
  hzN cp.G (aOf d p) (-1) z cp.ym σ cp.S i

/-- `θ` bounds every shifted deficit: `1 - E X^±_{z,ii}/y^±_i ≤ θ` for `i ∈ S`. -/
def DefZLe (z θ : ℝ) : Prop :=
  ∀ i ∈ cp.S, 1 - cp.E (fun σ => cp.hzp z σ i) ≤ θ ∧ 1 - cp.E (fun σ => cp.hzm z σ i) ≤ θ

/-- `θ` is the largest shifted deficit (or `0`). -/
def DefZMax (z θ : ℝ) : Prop :=
  0 ≤ θ ∧ cp.DefZLe z θ ∧
    (θ = 0 ∨ ∃ i ∈ cp.S, 1 - cp.E (fun σ => cp.hzp z σ i) = θ ∨
      1 - cp.E (fun σ => cp.hzm z σ i) = θ)

/-- `M_z = (a²/Z⁺_v) C_{z,+}[N,N]` with `C_{z,+} = (P⁺_{-v} + z I)⁻¹` (physical, inherited core);
`(μ_z - q_z)/Z⁺_v = tr M_z - q_{M_z}(ξ)`. -/
noncomputable def Mz (z : ℝ) (σ : Config cp.V) (v : cp.V) : Matrix (cp.N v) (cp.N v) ℝ :=
  rootMzG cp.G (aOf d p) 1 z cp.yp σ cp.S v

/-- The star vector `ξ` of a signing at the root `v`. -/
def xi (σ : Config cp.V) (v : cp.V) : cp.N v → ℝ := rootSigns cp.G σ cp.S v

/-- The swapped point `(y⁻, y⁺)` (the capped context is swap invariant). -/
def swap : CapPoint.{u} d p where
  V := cp.V
  G := cp.G
  S := cp.S
  lam := cp.lam
  yp := cp.ym
  ym := cp.yp
  ctx := cp.ctx
  hyp := cp.hym
  hym := cp.hyp

end CapPoint

/-- A contact context is a capped point. -/
def Contact.toCapPoint {d p : ℕ} (ct : Contact.{u} d p) : CapPoint.{u} d p where
  V := ct.V
  G := ct.G
  S := ct.S
  lam := ct.lam
  yp := ct.yp
  ym := ct.ym
  ctx := ct.ctx.toCapCtx
  hyp := ct.ctx.hyp
  hym := ct.ctx.hym

/-! ### Star observables -/

section Star

variable {ι : Type*} [Fintype ι]

/-- A quadratic function `x ↦ c + ℓ ⬝ x + xᵀ Q x`. -/
def quadFn (c : ℝ) (ℓ : ι → ℝ) (Q : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ := c + ℓ ⬝ᵥ x + qForm Q x

/-- A clipped observable `g α₊^{e₁} β₊^{e₂}` with `α = (1 - q_A)₊`, `β = (1 - q_B)₊`. -/
def clipObs (g : (ι → ℝ) → ℝ) (e₁ e₂ : ℕ) (A B : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ :=
  g x * clipF A x ^ e₁ * clipF B x ^ e₂

/-- The bias numerator `f₁ = (tr A - q_A) α^{p-1} β^p` of (E5), (C1). -/
def f1Obs (p : ℕ) (A B : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ :=
  (A.trace - qForm A x) * clipF A x ^ (p - 1) * clipF B x ^ p

/-- The core kernel `w = tr A²/(1 + tr A)`. -/
noncomputable def wK (A : Matrix ι ι ℝ) : ℝ := (A * A).trace / (1 + A.trace)

/-- The quadratic majorant condition of AUDIT-A §2.4 (MAJ) for `q = quadFn c ℓ Q` at `x₀`,
scale `m`, weights `λ`: `|q(x₀)| ≤ m`, `|∂_i q(x₀)| ≤ 2 m λ_i`, `|∂_i ∂_j q| ≤ 2 m λ_i λ_j`. -/
structure QuadMaj (c : ℝ) (ℓ : ι → ℝ) (Q : Matrix ι ι ℝ) (x₀ : ι → ℝ) (m : ℝ) (lam : ι → ℝ) :
    Prop where
  h0 : |quadFn c ℓ Q x₀| ≤ m
  h1 : ∀ i, |ℓ i + ((Q + Qᵀ) *ᵥ x₀) i| ≤ 2 * m * lam i
  h2 : ∀ i j, |Q i j + Q j i| ≤ 2 * m * lam i * lam j

end Star

end BiluLinial.Tight
