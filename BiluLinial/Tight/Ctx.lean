/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.Insertion
public import BiluLinial.Tight.Gauss.Basic

/-!
# Shared vocabulary for Sections 1.2–1.5 (the contact exclusion)

Definitions used by the statements of the analytic lemmas of
`docs/second_order_bilu_linial_tight.tex`, Sections 1.2–1.5 (audits `docs/tight/AUDIT_*.md`).

* **Quantifiers.** Every analytic lemma is stated as `∃ C, Eventually fun c₀ κ₀ d p h => …`: the
  constants `C` are absolute (chosen first), then `c₀, κ₀ ∈ (0, 1]`, then a degree threshold
  depending on `c₀, κ₀` only, at `p = ⌊c₀ d^{2/17}⌋` (`pAt`) and `h = κ₀ p^{-4}` (`hAt`). This is
  the order required by the final choice "`κ₀` small, then `c₀` small" (AUDIT-D, gap G3).
* **Contexts.** `CapCtx`: the hypotheses at stage `λ` of the expanding cube (graph-order induction
  hypothesis, the law exists on the whole cube `[0, s]^V`, first means capped by `r` on
  `[0, λ s]^V`). `ContactCtx`: in addition a contact `E h_v^+ = r` at a point of `[0, λ s]^V`.
* **Physical quantities.** `greenP` (`G^± = (P^±)⁻¹`), `shiftP` (`X_z^± = (P^± + z I)⁻¹`),
  `coreGreen` (inherited core inverse `G_K^±`, `K = S - v`), all with zero rows at zero sources,
  and the walk matrix `walkB` (`𝓑`, Lemma "Deletion and source differentiation"), `walkK = 𝓑⁻¹`.
  At a zero source `𝓑` has an identity row, so `walkK` is automatically the inverse for the
  positive-source subgraph (AUDIT-D, gap G1).
* **Star layer.** For the root `v` with `N = N_S(v)`: `rootMat` (`A = (a²/Z_v⁺) G_K⁺[N,N]` and
  `B = (a²/Z_v⁻) G_K⁻[N,N]`), `qForm`, `clipF` (`α = (1 - q_A)₊`), `starPhi` (`Φ = α^p β^p`), the
  Rademacher and Gaussian star averages `radE` (`𝖱`) and `gaussE` (`𝖦`), and `rootSigns` (the
  star vector `ξ` of a signing).
-/

@[expose] public section

namespace BiluLinial.Tight

open Matrix MeasureTheory

/-! ### Quantifier wrapper -/

/-- The shift `h = κ₀ p^{-4}`. -/
noncomputable def hAt (κ₀ : ℝ) (p : ℕ) : ℝ := κ₀ / (p : ℝ) ^ 4

/-- `Eventually P`: for all `c₀, κ₀ ∈ (0, 1]` there is a threshold `D` (depending on `c₀, κ₀`
only) such that `P c₀ κ₀ d p h` holds for every `d ≥ D` at `p = ⌊c₀ d^{2/17}⌋`, `h = κ₀ p^{-4}`. -/
def Eventually (P : ℝ → ℝ → ℕ → ℕ → ℝ → Prop) : Prop :=
  ∀ c₀ κ₀ : ℝ, 0 < c₀ → c₀ ≤ 1 → 0 < κ₀ → κ₀ ≤ 1 →
    ∃ D : ℕ, ∀ d : ℕ, D ≤ d → P c₀ κ₀ d (pAt c₀ d) (hAt κ₀ (pAt c₀ d))

theorem Eventually.mono {P Q : ℝ → ℝ → ℕ → ℕ → ℝ → Prop} (hP : Eventually P)
    (h : ∀ c₀ κ₀ d p h, P c₀ κ₀ d p h → Q c₀ κ₀ d p h) : Eventually Q := by
  intro c₀ κ₀ h0 h1 k0 k1
  obtain ⟨D, hD⟩ := hP c₀ κ₀ h0 h1 k0 k1
  exact ⟨D, fun d hd => h _ _ _ _ _ (hD d hd)⟩

theorem Eventually.and {P Q : ℝ → ℝ → ℕ → ℕ → ℝ → Prop} (hP : Eventually P)
    (hQ : Eventually Q) : Eventually fun c₀ κ₀ d p h => P c₀ κ₀ d p h ∧ Q c₀ κ₀ d p h := by
  intro c₀ κ₀ h0 h1 k0 k1
  obtain ⟨D₁, hD₁⟩ := hP c₀ κ₀ h0 h1 k0 k1
  obtain ⟨D₂, hD₂⟩ := hQ c₀ κ₀ h0 h1 k0 k1
  exact ⟨max D₁ D₂, fun d hd =>
    ⟨hD₁ d (le_of_max_le_left hd), hD₂ d (le_of_max_le_right hd)⟩⟩

/-! ### Contexts -/

section Ctx

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The hypotheses at stage `λ` of the expanding cube for `H = G[S]` (source Section 1.1, last
paragraph; AUDIT-A (CSL), AUDIT-B (CAP), AUDIT-D (H2)–(H3)): maximum degree `≤ d`, the
graph-order induction hypothesis, the law exists on the whole cube `[0, s]^V`, and every first mean
is at most `r` on the cube `[0, λ s]^V`. -/
structure CapCtx (d p : ℕ) (S : Finset V) (lam : ℝ) : Prop where
  deg : ∀ v, G.degree v ≤ d
  ih : ∀ T ⊂ S, TInv G d p T
  pos : ∀ yp ym : V → ℝ, InCube (sOf d p) yp → InCube (sOf d p) ym →
    0 < Zw G p (aOf d p) yp ym S
  lam_nonneg : 0 ≤ lam
  lam_le_one : lam ≤ 1
  cap : ∀ yp ym : V → ℝ, InCube (lam * sOf d p) yp → InCube (lam * sOf d p) ym →
    ∀ i ∈ S, meanPlus G d p yp ym S i ≤ rOf d p ∧ meanMinus G d p yp ym S i ≤ rOf d p

/-- A contact (AUDIT-D (H4)): the context `CapCtx` at stage `λ`, a point `(y⁺, y⁻)` of the cube
`[0, λ s]^V` and a root `v ∈ S` with `E h_v^+ = r`. -/
structure ContactCtx (d p : ℕ) (S : Finset V) (lam : ℝ) (yp ym : V → ℝ) (v : V) : Prop
    extends CapCtx G d p S lam where
  hyp : InCube (lam * sOf d p) yp
  hym : InCube (lam * sOf d p) ym
  mem : v ∈ S
  contact : meanPlus G d p yp ym S v = rOf d p

end Ctx

/-! ### Physical quantities -/

section Physical

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The physical inverse `G^τ = (P^τ)⁻¹ = Y^{1/2} (P̃^τ)⁻¹ Y^{1/2}` (rows of zero sources
vanish). `τ = 1`: `G⁺` with sources `y⁺`; `τ = -1`: `G⁻` with sources `y⁻`. -/
noncomputable def greenP (a τ : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) (i j : V) : ℝ :=
  Real.sqrt (y i) * (precN G a τ y σ S)⁻¹ i j * Real.sqrt (y j)

/-- The diagonal `Y_S` of the sources on `S` (zero off `S`). -/
noncomputable def srcDiag (y : V → ℝ) (S : Finset V) : Matrix V V ℝ :=
  diagonal fun k => if k ∈ S then y k else 0

/-- The physical shifted inverse `X_z^τ = (P^τ + z I)⁻¹ = Y^{1/2} (P̃^τ + z Y)⁻¹ Y^{1/2}` on `S`. -/
noncomputable def shiftP (a τ z : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) (i j : V) : ℝ :=
  Real.sqrt (y i) * (precN G a τ y σ S + z • srcDiag y S)⁻¹ i j * Real.sqrt (y j)

/-- The physical inherited core inverse `G_K^τ` at the root `v` (`K = S - v`, diagonal of `S`). -/
noncomputable def coreGreen (a τ : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) (v i j : V) :
    ℝ :=
  Real.sqrt (y i) * (precCore G a τ y σ S v)⁻¹ i j * Real.sqrt (y j)

/-- The walk matrix `𝓑` of Lemma "Deletion and source differentiation" on `S` (identity off `S`):
`𝓑_ii = 1 + Σ_j τ_ij²/(1 - τ_ij²)`, `𝓑_ij = -τ_ij/(1 - τ_ij²)` on edges. Then
`DZ = -D_y⁻¹ 𝓑 D_y⁻¹` on positive sources. -/
noncomputable def walkB (a : ℝ) (y : V → ℝ) (S : Finset V) : Matrix V V ℝ :=
  Matrix.of fun u w =>
    if u = w then
      (if u ∈ S then
        1 + ∑ j ∈ nbhd G S u, τEdge a y u j ^ 2 / (1 - τEdge a y u j ^ 2) else 1)
    else if u ∈ S ∧ w ∈ S ∧ G.Adj u w then -(τEdge a y u w / (1 - τEdge a y u w ^ 2))
    else 0

/-- `K = 𝓑⁻¹`, the nonbacktracking walk sum (`K ≥ 0`, `K_ii ≥ 1`, `K_ij ≥ τ_ij` on edges). -/
noncomputable def walkK (a : ℝ) (y : V → ℝ) (S : Finset V) : Matrix V V ℝ :=
  (walkB G a y S)⁻¹

end Physical

/-! ### The star layer at a root -/

section Star

/-- `q_M(x) = xᵀ M x`. -/
def qForm {ι : Type*} [Fintype ι] (M : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ := x ⬝ᵥ (M *ᵥ x)

/-- The clipped factor `(1 - q_M(x))₊` (`α` for `M = A`, `β` for `M = B`). -/
def clipF {ι : Type*} [Fintype ι] (M : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ := max (1 - qForm M x) 0

/-- The insertion factor `Φ = α^p β^p` as a function of the star vector `x ∈ ℝ^N`. -/
def starPhi {ι : Type*} [Fintype ι] (p : ℕ) (A B : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ :=
  clipF A x ^ p * clipF B x ^ p

/-- The Rademacher star average `𝖱 f` (uniform signs on `ι`). -/
noncomputable def radE {ι : Type*} [Fintype ι] (f : (ι → ℝ) → ℝ) : ℝ := ∫ x, f x ∂(radPi ι)

/-- The Gaussian star average `𝖦 f` (standard Gaussian on `ι → ℝ`). -/
noncomputable def gaussE {ι : Type*} [Fintype ι] (f : (ι → ℝ) → ℝ) : ℝ := ∫ x, f x ∂(gaussPi ι)

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The root matrix `A = (a²/Z_v⁺) G_K⁺[N,N]` (`τ = 1`, sources `y⁺`) or
`B = (a²/Z_v⁻) G_K⁻[N,N]` (`τ = -1`, sources `y⁻`) on `N = N_S(v)`; `a²/Z_v = a² y_v / D_v`. Its
quadratic form at the star vector of `σ` is the root energy `qRoot` (`q_A`, `q_B`). -/
noncomputable def rootMat (a τ : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) (v : V) :
    Matrix (nbhd G S v) (nbhd G S v) ℝ :=
  Matrix.of fun i j => a ^ 2 * y v / diagD G a y S v * coreGreen G a τ y σ S v i j

/-- The star vector `ξ_i = σ(vi)` of a signing on `N = N_S(v)`. -/
def rootSigns (σ : Config V) (S : Finset V) (v : V) : nbhd G S v → ℝ :=
  fun i => sgn σ v i

end Star

end BiluLinial.Tight
