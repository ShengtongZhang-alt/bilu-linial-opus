/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.Ctx

/-!
# Vocabulary of the contact estimate (Section 1.5)

Definitions used by the statements of `docs/tight/BP_CONTACT.md` (source
`docs/second_order_bilu_linial_tight.tex`, lines 1334–2073; audits AUDIT-C §6, AUDIT-D §3).

* `Contact d p`: a bundled contact context (`ContactCtx`, Lean file `Tight/Ctx.lean`): a graph, the
  vertex set `S`, the stage `λ`, the contact point `(y⁺, y⁻)` and the root `v`. `ContactFree d p`
  says exactly that `Contact d p` is empty (`contactFree_of_isEmpty`, `Tight/Contact.lean`).
* Deterministic parameters of Section 1.5 as functions of `(d, p, h)`: `ε = r - 1`, `L̄ = d a² s²`,
  `L_d = 16 d a²`, `c_p = 1/(4(p-1))`, `ϑ = d^{-10}`, `θ = d^{-2}`, the concentration base
  `δ̄ = ε + p⁴/d + (p/d)^{1/3}` (the source's `δ` is `C δ̄`), `Γ = p⁴ √(p δ̄/d)`,
  `e = √(p δ̄)/(√d h)` (the source's `e = p √δ_row/(√d h)` is `C e`), `B₀`,
  `ε_s = p^{3/2} d^{-1/2}`, the profile error `ξ`, and the error aggregates of D9a, D10, RC3, D12
  and the final ledger.
  Exponentially small terms `e^{-cp}` of the source are replaced by `ϑ = d^{-10}` (equivalent
  under `Eventually`, since `p ≥ c₀ d^{2/17}/2`).
* Random and averaged quantities at a contact (`Contact.*`): the root rows `x_i = G⁺_vi`,
  `z_i = G⁻_vi`, `S`, `T`, `𝓡`, `ℓ_i`, `L`, `C₊`, `D₊`, `J`, `δ_i`, the fourth-order term `Q_*`,
  the root matrices `A`, `B` and their core traces, the Gaussian row numerator `Gterm`
  (`E_{ν_K} 𝖦F/(a² F_H)`), the shifted inverses `X_±` and core shifted inverses `Y_±`, the trace
  budget `Q`, the Hadamard energies `q_±, ζ, z_±, t_±, α, β, ζ₋`, the unshifted centres
  `t_{±,0}`, and the weak-loop scores.
-/

@[expose] public section

namespace BiluLinial.Tight

open Matrix

universe u

/-! ### Deterministic parameters -/

/-- `ε = r - 1 = η₀/2`. -/
noncomputable def epsP (d p : ℕ) : ℝ := rOf d p - 1

/-- `L̄ = d a² s²`. -/
noncomputable def LbarP (d p : ℕ) : ℝ := (d : ℝ) * aOf d p ^ 2 * sOf d p ^ 2

/-- `L_d = 16 d a²`. -/
noncomputable def LdP (d p : ℕ) : ℝ := 16 * (d : ℝ) * aOf d p ^ 2

/-- The scalar loss `c_p = 1/(4(p-1))` of JR2. -/
noncomputable def cpP (p : ℕ) : ℝ := 1 / (4 * ((p : ℝ) - 1))

/-- The polynomial floor `ϑ = d^{-10}`. -/
noncomputable def vth (d : ℕ) : ℝ := 1 / (d : ℝ) ^ 10

/-- The mask floor `θ = d^{-2}`. -/
noncomputable def thP (d : ℕ) : ℝ := 1 / (d : ℝ) ^ 2

/-- The concentration base `δ̄ = ε + p⁴/d + (p/d)^{1/3}` (the source's `δ` of (C2) and (D5) is
`C δ̄` with an absolute `C`). -/
noncomputable def dbar (d p : ℕ) : ℝ :=
  epsP d p + (p : ℝ) ^ 4 / d + ((p : ℝ) / d) ^ ((1 : ℝ) / 3)

/-- `Γ = p⁴ √(p δ̄/d)` (D9a). -/
noncomputable def GamP (d p : ℕ) : ℝ := (p : ℝ) ^ 4 * Real.sqrt ((p : ℝ) * dbar d p / d)

/-- `e = √(p δ̄)/(√d h)` (FS5; the source's `p √δ_row/(√d h)` with `δ_row = C δ̄/p`). -/
noncomputable def eP (d p : ℕ) (h : ℝ) : ℝ :=
  Real.sqrt ((p : ℝ) * dbar d p) / (Real.sqrt d * h)

/-- `B₀ = p/(dh) + 1/(d h^{3/2}) + ϑ` (FS6). -/
noncomputable def B0P (d p : ℕ) (h : ℝ) : ℝ :=
  (p : ℝ) / (d * h) + 1 / (d * h * Real.sqrt h) + vth d

/-- `ε_s = p^{3/2} d^{-1/2}` (D7; the source's `ε_s` is `C ε_s`). -/
noncomputable def epsS (d p : ℕ) : ℝ := (p : ℝ) * Real.sqrt p / Real.sqrt d

/-- The profile error `ξ = √h + χ₊ + √ρ_v + ε + 1/d` with
`χ₊ = √(ε/p + ε² + p/d) + ε_s + η₀ + 1/d` and `ρ_v = ε/p + ε²` (l.1800–1806). -/
noncomputable def xiP (d p : ℕ) (h : ℝ) : ℝ :=
  Real.sqrt h + (Real.sqrt (epsP d p / p + epsP d p ^ 2 + (p : ℝ) / d) + epsS d p +
    η0Of d p + 1 / (d : ℝ)) + Real.sqrt (epsP d p / p + epsP d p ^ 2) + epsP d p + 1 / (d : ℝ)

/-- The row comparison error of (D9a), without its constant: `Γ √(S+1) + p¹³/d² + ϑ`. -/
noncomputable def ErowP (d p : ℕ) (S : ℝ) : ℝ :=
  GamP d p * Real.sqrt (S + 1) + (p : ℝ) ^ 13 / (d : ℝ) ^ 2 + vth d

/-- The multiplicative Brascamp–Lieb loss `η_BL = p⁴/d + p/(dh)` (B1, without its constant). -/
noncomputable def etaBL (d p : ℕ) (h : ℝ) : ℝ := (p : ℝ) ^ 4 / d + (p : ℝ) / (d * h)

/-- The additive Brascamp–Lieb loss `ε_BL = ϑ (p⁵ + p²/h) + ϑ` (B1, without its constant). -/
noncomputable def epsBL (d p : ℕ) (h : ℝ) : ℝ := vth d * ((p : ℝ) ^ 5 + (p : ℝ) ^ 2 / h) + vth d

/-- The error of (D10), without its constant:
`E_row + p⁵/d + p²/(dh) + p/(d h^{3/2}) + ε_BL`. -/
noncomputable def Err10 (d p : ℕ) (h S : ℝ) : ℝ :=
  ErowP d p S + (p : ℝ) ^ 5 / d + (p : ℝ) ^ 2 / (d * h) + (p : ℝ) / (d * h * Real.sqrt h) +
    epsBL d p h

/-- The bracket of (RC3): `e² + B₀ + e (h^{3/4} + (dh)^{-1/2} + √θ) + ξ`. -/
noncomputable def ErrRC3 (d p : ℕ) (h : ℝ) : ℝ :=
  eP d p h ^ 2 + B0P d p h +
    eP d p h * (h ^ ((3 : ℝ) / 4) + Real.sqrt (1 / (d * h)) + Real.sqrt (thP d)) + xiP d p h

/-- The error `𝓔` of (D12), without its constant: `Err10 + p·ErrRC3 + p √h`. -/
noncomputable def Err12 (d p : ℕ) (h S : ℝ) : ℝ :=
  Err10 d p h S + (p : ℝ) * ErrRC3 d p h + (p : ℝ) * Real.sqrt h

/-- The total error of the final drift after absorbing `Γ √(S+1)` (l.1990–2000), without its
constant: `Γ + Γ² + ε_s + η₀ + 1/d + p¹³/d² + ϑ + p⁵/d + p²/(dh) + p/(d h^{3/2}) + ε_BL
+ p·ErrRC3 + p √h + p³ √(p δ̄/d)`. -/
noncomputable def TotErr (d p : ℕ) (h : ℝ) : ℝ :=
  GamP d p + GamP d p ^ 2 + epsS d p + η0Of d p + 1 / (d : ℝ) + (p : ℝ) ^ 13 / (d : ℝ) ^ 2 +
    vth d + (p : ℝ) ^ 5 / d + (p : ℝ) ^ 2 / (d * h) + (p : ℝ) / (d * h * Real.sqrt h) +
    epsBL d p h + (p : ℝ) * ErrRC3 d p h + (p : ℝ) * Real.sqrt h +
    (p : ℝ) ^ 3 * Real.sqrt ((p : ℝ) * dbar d p / d)

/-! ### Polynomials and matrix expressions -/

/-- The fourth-order polynomial `K_i` of l.1372–1383, in `x = x_i`, `z = z_i`,
`P = P_i = G⁺_vv G⁺_ii`, `Q = Q_i = G⁻_vv G⁻_ii`. -/
noncomputable def Kpoly (p : ℕ) (x z P Q : ℝ) : ℝ :=
  let U := ((p : ℝ) - 1) * x - p * z
  let V := ((p : ℝ) - 1) * (P + x ^ 2) + p * (Q + z ^ 2)
  let W := ((p : ℝ) - 1) * (3 * P * x + x ^ 3) - p * (3 * Q * z + z ^ 3)
  x * (8 * U ^ 3 - 12 * U * V + 4 * W) - 3 * (P - x ^ 2) * (4 * U ^ 2 - 2 * V)

/-- The row numerator `F = (p-1) q_{A²} α^{p-2} β^p + p q_{AB} α^{p-1} β^{p-1}` of (E5). -/
noncomputable def rowNum {ι : Type*} [Fintype ι] (p : ℕ) (A B : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ :=
  ((p : ℝ) - 1) * qForm (A * A) x * clipF A x ^ (p - 2) * clipF B x ^ p +
    p * qForm (A * B) x * clipF A x ^ (p - 1) * clipF B x ^ (p - 1)

/-- The Schur column of a mask (W1, BM1, FS1): with `U = X_ε diag(f) X_ν`,
`F_ji = (X_ε)_ii U_ji - (X_ε)_ji U_ii`. -/
def maskF {V : Type*} [Fintype V] [DecidableEq V] (Xe Xn : Matrix V V ℝ) (f : V → ℝ) (j i : V) :
    ℝ :=
  Xe i i * (Xe * diagonal f * Xn) j i - Xe j i * (Xe * diagonal f * Xn) i i

/-- The physical core shifted inverse `(P_K + zI)⁻¹` at the root `v` (`K = S - v`, inherited
precision): `Y^{1/2} (P̃_core + z Y_K)⁻¹ Y^{1/2}`. -/
noncomputable def coreShift {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (a τ z : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) (v i j : V) : ℝ :=
  Real.sqrt (y i) * (precCore G a τ y σ S v + z • srcDiag y (S.erase v))⁻¹ i j * Real.sqrt (y j)

/-! ### Bundled contacts -/

/-- A contact context at degree `d` and parameter `p`, bundled with its graph. -/
structure Contact (d p : ℕ) where
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
  /-- root -/
  v : V
  ctx : ContactCtx G d p S lam yp ym v

attribute [instance] Contact.fin Contact.dec Contact.adj

namespace Contact

variable {d p : ℕ} (ct : Contact.{u} d p)

/-- Expectation under the paired law at the contact point. -/
noncomputable def E (f : Config ct.V → ℝ) : ℝ := lawE ct.G p (aOf d p) ct.yp ct.ym ct.S f

/-- `N = N_S(v)`. -/
def N : Finset ct.V := nbhd ct.G ct.S ct.v

/-- Physical `G⁺`. -/
noncomputable def gp (σ : Config ct.V) (i j : ct.V) : ℝ :=
  greenP ct.G (aOf d p) 1 ct.yp σ ct.S i j

/-- Physical `G⁻`. -/
noncomputable def gm (σ : Config ct.V) (i j : ct.V) : ℝ :=
  greenP ct.G (aOf d p) (-1) ct.ym σ ct.S i j

/-- `x_i = G⁺_vi`. -/
noncomputable def x (σ : Config ct.V) (i : ct.V) : ℝ := ct.gp σ ct.v i

/-- `z_i = G⁻_vi`. -/
noncomputable def z (σ : Config ct.V) (i : ct.V) : ℝ := ct.gm σ ct.v i

/-- `S = Σ_N E x_i²`. -/
noncomputable def Srow : ℝ := ∑ i ∈ ct.N, ct.E fun σ => ct.x σ i ^ 2

/-- `S₋ = Σ_N E z_i²`. -/
noncomputable def Smin : ℝ := ∑ i ∈ ct.N, ct.E fun σ => ct.z σ i ^ 2

/-- `T = Σ_N E x_i z_i`. -/
noncomputable def Tmix : ℝ := ∑ i ∈ ct.N, ct.E fun σ => ct.x σ i * ct.z σ i

/-- `𝓡 = (p-1) S - p T`. -/
noncomputable def Rrow : ℝ := ((p : ℝ) - 1) * ct.Srow - p * ct.Tmix

/-- `Σ_N E P_i`, `P_i = G⁺_vv G⁺_ii`. -/
noncomputable def sumP : ℝ := ∑ i ∈ ct.N, ct.E fun σ => ct.gp σ ct.v ct.v * ct.gp σ i i

/-- `E[ξ_i x_i]` with `ξ_i = σ(vi)`. -/
noncomputable def sx (i : ct.V) : ℝ := ct.E fun σ => sgn σ ct.v i * ct.x σ i

/-- `ℓ_i = a² y⁺_v y⁺_i`. -/
noncomputable def ell (i : ct.V) : ℝ := aOf d p ^ 2 * ct.yp ct.v * ct.yp i

/-- `L = Σ_N ℓ_i`. -/
noncomputable def Lsum : ℝ := ∑ i ∈ ct.N, ct.ell i

/-- `C₊ = Σ_N (c⁺_vi)²`. -/
noncomputable def Cplus : ℝ := ∑ i ∈ ct.N, cEdge (aOf d p) ct.yp ct.v i ^ 2

/-- `D₊ = Z⁺_v y⁺_v = 1 + Σ_N c⁺_vi`. -/
noncomputable def Dplus : ℝ := diagD ct.G (aOf d p) ct.yp ct.S ct.v

/-- `J = Σ_N ℓ_i (𝓑(y⁺)⁻¹)_vi`. -/
noncomputable def Jw : ℝ := ∑ i ∈ ct.N, ct.ell i * walkK ct.G (aOf d p) ct.yp ct.S ct.v i

/-- `E h_i⁺`. -/
noncomputable def mp (i : ct.V) : ℝ := meanPlus ct.G d p ct.yp ct.ym ct.S i

/-- `δ_i = r - E h_i⁺`. -/
noncomputable def delta (i : ct.V) : ℝ := rOf d p - ct.mp i

/-- `Σ_N ℓ_i δ_i`. -/
noncomputable def sumEllDelta : ℝ := ∑ i ∈ ct.N, ct.ell i * ct.delta i

/-- `Q_* = (a⁴/3) Σ_N E K_i`. -/
noncomputable def Qstar : ℝ :=
  aOf d p ^ 4 / 3 * ∑ i ∈ ct.N, ct.E fun σ =>
    Kpoly p (ct.x σ i) (ct.z σ i) (ct.gp σ ct.v ct.v * ct.gp σ i i)
      (ct.gm σ ct.v ct.v * ct.gm σ i i)

/-- The root matrix `A = (a²/Z⁺_v) G_K⁺[N,N]`. -/
noncomputable def Amat (σ : Config ct.V) : Matrix ct.N ct.N ℝ :=
  rootMat ct.G (aOf d p) 1 ct.yp σ ct.S ct.v

/-- The root matrix `B = (a²/Z⁻_v) G_K⁻[N,N]`. -/
noncomputable def Bmat (σ : Config ct.V) : Matrix ct.N ct.N ℝ :=
  rootMat ct.G (aOf d p) (-1) ct.ym σ ct.S ct.v

/-- `E tr A²` (full law). -/
noncomputable def trA2 : ℝ := ct.E fun σ => (ct.Amat σ * ct.Amat σ).trace

/-- `E tr B²` (full law). -/
noncomputable def trB2 : ℝ := ct.E fun σ => (ct.Bmat σ * ct.Bmat σ).trace

/-- `E w`, `w = tr A²/(1 + tr A)` (the core kernel of (C3a)). -/
noncomputable def wker : ℝ :=
  ct.E fun σ => (ct.Amat σ * ct.Amat σ).trace / (1 + (ct.Amat σ).trace)

/-- `E[(G⁺_vv)² ‖G⁺[N,N]‖_F²]` (marked core envelope of CR3). -/
noncomputable def frobP : ℝ :=
  ct.E fun σ => ct.gp σ ct.v ct.v ^ 2 * ∑ i ∈ ct.N, ∑ j ∈ ct.N, ct.gp σ i j ^ 2

/-- `E[(G⁻_vv)² ‖G⁻[N,N]‖_F²]`. -/
noncomputable def frobM : ℝ :=
  ct.E fun σ => ct.gm σ ct.v ct.v ^ 2 * ∑ i ∈ ct.N, ∑ j ∈ ct.N, ct.gm σ i j ^ 2

/-- The Gaussian row numerator `E_{ν_K} 𝖦F / (a² F_H)` of CR1/CR3/B1, with `ν_K` the own core law
(`coreE`) and `F_H = E_{ν_K} 𝖱Φ`. -/
noncomputable def Gterm : ℝ :=
  coreE ct.G p (aOf d p) ct.yp ct.ym ct.S ct.v
      (fun σ => gaussE (rowNum p (ct.Amat σ) (ct.Bmat σ))) /
    (aOf d p ^ 2 *
      coreE ct.G p (aOf d p) ct.yp ct.ym ct.S ct.v
        (fun σ => radE (starPhi p (ct.Amat σ) (ct.Bmat σ))))

/-! #### Shifted inverses and the trace budget -/

/-- `X₊ = (P⁺ + hI)⁻¹` (physical). -/
noncomputable def XP (h : ℝ) (σ : Config ct.V) : Matrix ct.V ct.V ℝ :=
  Matrix.of fun i j => shiftP ct.G (aOf d p) 1 h ct.yp σ ct.S i j

/-- `X₋ = (P⁻ + hI)⁻¹` (physical). -/
noncomputable def XM (h : ℝ) (σ : Config ct.V) : Matrix ct.V ct.V ℝ :=
  Matrix.of fun i j => shiftP ct.G (aOf d p) (-1) h ct.ym σ ct.S i j

/-- `Y₊ = (P⁺_{S-v} + hI)⁻¹` (physical, inherited core). -/
noncomputable def YP (h : ℝ) (σ : Config ct.V) (i j : ct.V) : ℝ :=
  coreShift ct.G (aOf d p) 1 h ct.yp σ ct.S ct.v i j

/-- `Y₋ = (P⁻_{S-v} + hI)⁻¹` (physical, inherited core). -/
noncomputable def YM (h : ℝ) (σ : Config ct.V) (i j : ct.V) : ℝ :=
  coreShift ct.G (aOf d p) (-1) h ct.ym σ ct.S ct.v i j

/-- The trace budget of (B1): `Q = a² E{(p-1)(G⁺_vv)² tr Y₊² + p G⁺_vv G⁻_vv tr(Y₊Y₋)}` with
`Y_± = (P^±_{S-v} + hI)⁻¹[N,N]`. -/
noncomputable def Qbl (h : ℝ) : ℝ :=
  aOf d p ^ 2 * ct.E fun σ =>
    ((p : ℝ) - 1) * ct.gp σ ct.v ct.v ^ 2 * ∑ i ∈ ct.N, ∑ j ∈ ct.N, ct.YP h σ i j ^ 2 +
      p * ct.gp σ ct.v ct.v * ct.gm σ ct.v ct.v *
        ∑ i ∈ ct.N, ∑ j ∈ ct.N, ct.YP h σ i j * ct.YM h σ i j

/-! #### Hadamard energies (l.1560–1594) -/

/-- `Ω₊ = (G⁺_vv/2)²`. -/
noncomputable def OmP (σ : Config ct.V) : ℝ := (ct.gp σ ct.v ct.v / 2) ^ 2

/-- `Ω₋ = G⁺_vv G⁻_vv/4`. -/
noncomputable def OmM (σ : Config ct.V) : ℝ := ct.gp σ ct.v ct.v * ct.gm σ ct.v ct.v / 4

/-- `u = 1_N/√d`. -/
noncomputable def uvec : ct.V → ℝ := fun i => if i ∈ ct.N then 1 / Real.sqrt d else 0

/-- `K₊ = X₊ ∘ X₊/4`. -/
noncomputable def KP (h : ℝ) (σ : Config ct.V) : Matrix ct.V ct.V ℝ :=
  Matrix.of fun i k => ct.XP h σ i k * ct.XP h σ i k / 4

/-- `K₋ = X₊ ∘ X₋/4`. -/
noncomputable def KM (h : ℝ) (σ : Config ct.V) : Matrix ct.V ct.V ℝ :=
  Matrix.of fun i k => ct.XP h σ i k * ct.XM h σ i k / 4

/-- `M₊ = diag(a_i²)`, `a_i = (X₊)_ii/2`. -/
noncomputable def MP (h : ℝ) (σ : Config ct.V) : Matrix ct.V ct.V ℝ :=
  diagonal fun i => (ct.XP h σ i i / 2) ^ 2

/-- `M₋ = diag(a_i b_i)`, `b_i = (X₋)_ii/2`. -/
noncomputable def MM (h : ℝ) (σ : Config ct.V) : Matrix ct.V ct.V ℝ :=
  diagonal fun i => ct.XP h σ i i / 2 * (ct.XM h σ i i / 2)

/-- The unsigned adjacency matrix `A_H` of `H = G[S]`. -/
noncomputable def adjS : Matrix ct.V ct.V ℝ :=
  Matrix.of fun k l => if k ∈ ct.S ∧ l ∈ ct.S ∧ ct.G.Adj k l then 1 else 0

/-- `b₊ = 4 T M₊ u`, `T = a² A_H`. -/
noncomputable def bP (h : ℝ) (σ : Config ct.V) : ct.V → ℝ :=
  (4 * aOf d p ^ 2) • (ct.adjS *ᵥ (ct.MP h σ *ᵥ ct.uvec))

/-- `b₋ = 4 T M₋ u`. -/
noncomputable def bM (h : ℝ) (σ : Config ct.V) : ct.V → ℝ :=
  (4 * aOf d p ^ 2) • (ct.adjS *ᵥ (ct.MM h σ *ᵥ ct.uvec))

/-- `q₊ = E[Ω₊ uᵀK₊u]`. -/
noncomputable def qP (h : ℝ) : ℝ := ct.E fun σ => ct.OmP σ * (ct.uvec ⬝ᵥ (ct.KP h σ *ᵥ ct.uvec))

/-- `ζ = E[Ω₊ uᵀK₊b₊]`. -/
noncomputable def zeta (h : ℝ) : ℝ :=
  ct.E fun σ => ct.OmP σ * (ct.uvec ⬝ᵥ (ct.KP h σ *ᵥ ct.bP h σ))

/-- `z = z₊ = E[Ω₊ b₊ᵀK₊b₊]`. -/
noncomputable def zP (h : ℝ) : ℝ :=
  ct.E fun σ => ct.OmP σ * (ct.bP h σ ⬝ᵥ (ct.KP h σ *ᵥ ct.bP h σ))

/-- `t₊ = E[Ω₊ uᵀM₊u]`. -/
noncomputable def tP (h : ℝ) : ℝ := ct.E fun σ => ct.OmP σ * (ct.uvec ⬝ᵥ (ct.MP h σ *ᵥ ct.uvec))

/-- `α = E[Ω₊ uᵀM₊b₊]`. -/
noncomputable def alphaE (h : ℝ) : ℝ :=
  ct.E fun σ => ct.OmP σ * (ct.uvec ⬝ᵥ (ct.MP h σ *ᵥ ct.bP h σ))

/-- `q₋ = E[Ω₋ uᵀK₋u]`. -/
noncomputable def qM (h : ℝ) : ℝ := ct.E fun σ => ct.OmM σ * (ct.uvec ⬝ᵥ (ct.KM h σ *ᵥ ct.uvec))

/-- `ζ₋ = E[Ω₋ uᵀK₋b₋]`. -/
noncomputable def zetaM (h : ℝ) : ℝ :=
  ct.E fun σ => ct.OmM σ * (ct.uvec ⬝ᵥ (ct.KM h σ *ᵥ ct.bM h σ))

/-- `z₋ = E[Ω₋ b₋ᵀK₋b₋]`. -/
noncomputable def zM (h : ℝ) : ℝ :=
  ct.E fun σ => ct.OmM σ * (ct.bM h σ ⬝ᵥ (ct.KM h σ *ᵥ ct.bM h σ))

/-- `t₋ = E[Ω₋ uᵀM₋u]`. -/
noncomputable def tM (h : ℝ) : ℝ := ct.E fun σ => ct.OmM σ * (ct.uvec ⬝ᵥ (ct.MM h σ *ᵥ ct.uvec))

/-- `β = E[Ω₋ uᵀM₋b₋]`. -/
noncomputable def betaE (h : ℝ) : ℝ :=
  ct.E fun σ => ct.OmM σ * (ct.uvec ⬝ᵥ (ct.MM h σ *ᵥ ct.bM h σ))

/-- `t_{+,0} = (16d)⁻¹ E[(G⁺_vv)² Σ_N (G⁺_ii)²]`. -/
noncomputable def tP0 : ℝ :=
  1 / (16 * (d : ℝ)) * ct.E fun σ => ct.gp σ ct.v ct.v ^ 2 * ∑ i ∈ ct.N, ct.gp σ i i ^ 2

/-- `t_{-,0} = (16d)⁻¹ E[G⁺_vv G⁻_vv Σ_N G⁺_ii G⁻_ii]`. -/
noncomputable def tM0 : ℝ :=
  1 / (16 * (d : ℝ)) * ct.E fun σ =>
    ct.gp σ ct.v ct.v * ct.gm σ ct.v ct.v * ∑ i ∈ ct.N, ct.gp σ i i * ct.gm σ i i

/-! #### Weak-loop scores (W1, FS5) -/

/-- `∂_ij Ω₊ = -a G⁺_vv G⁺_vi G⁺_vj` (edge `ij` perturbed in both branches, (E3)). -/
noncomputable def dOmP (σ : Config ct.V) (i j : ct.V) : ℝ :=
  -(aOf d p) * ct.gp σ ct.v ct.v * ct.gp σ ct.v i * ct.gp σ ct.v j

/-- `∂_ij Ω₋ = (a/2)(G⁺_vv G⁻_vi G⁻_vj - G⁺_vi G⁺_vj G⁻_vv)`. -/
noncomputable def dOmM (σ : Config ct.V) (i j : ct.V) : ℝ :=
  aOf d p / 2 * (ct.gp σ ct.v ct.v * ct.gm σ ct.v i * ct.gm σ ct.v j -
    ct.gp σ ct.v i * ct.gp σ ct.v j * ct.gm σ ct.v ct.v)

/-- The weak-loop score with its physical weight retained and the exact determinant score
`2pa(G⁺_ij - G⁻_ij)` (W1 as in AUDIT-B B-2):
`𝖲 = a Σ_{i∈N} Σ_{j ∼ i} u_i E[|F_ji| (2paH |G⁺_ij - G⁻_ij| + |∂_ij H|)]`. -/
noncomputable def score (H : Config ct.V → ℝ) (dH : Config ct.V → ct.V → ct.V → ℝ)
    (Xe Xn : Config ct.V → Matrix ct.V ct.V ℝ) (f : Config ct.V → ct.V → ℝ) : ℝ :=
  aOf d p * ∑ i ∈ ct.N, ∑ j ∈ nbhd ct.G ct.S i, ct.uvec i * ct.E fun σ =>
    |maskF (Xe σ) (Xn σ) (f σ) j i| *
      (2 * p * aOf d p * H σ * |ct.gp σ i j - ct.gm σ i j| + |dH σ i j|)

/-- `D_* = 1 +` the largest physical inverse diagonal of either branch on `N ∪ N(N) ∪ {v}`. -/
noncomputable def Dstar (σ : Config ct.V) : ℝ :=
  1 + (insert ct.v (ct.N ∪ ct.N.biUnion (nbhd ct.G ct.S))).sup' (Finset.insert_nonempty _ _)
    (fun w => max (ct.gp σ w w) (ct.gm σ w w))

end Contact

/-! ### The regime of the real-number lemmas -/

/-- The parameter regime at `h = κ₀ p^{-4}`: `TRegime d p`, `κ₀ ∈ (0, 1]`. -/
structure Reg (κ₀ : ℝ) (d p : ℕ) (h : ℝ) : Prop where
  treg : TRegime d p
  k0 : 0 < κ₀
  k1 : κ₀ ≤ 1
  hh : h = κ₀ / (p : ℝ) ^ 4

end BiluLinial.Tight
