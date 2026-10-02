/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.Contact.Defs

/-!
# Definitions for Section 1.4 (lines 1077–1333): fresh-star row energies

Source `docs/second_order_bilu_linial_tight.tex`, Section 1.4 ("Comparison of fresh-star row
energies": Lemma "Contact row comparison" (CR1)–(CR3) and Lemma "Multiplicative shifted trace
comparison" (B1)–(B5)); audit `docs/tight/AUDIT_C.md` §1, §4; notes `docs/tight/BP_SECC.md`.

Everything already defined is reused: `rowNum` (`F` of (E5)), `coreShift` (`(P_K + zI)⁻¹`) and
`vth` (`ϑ = d^{-10}`) from `Tight/Contact/Defs.lean`. The graph-level quantities below are the
unbundled forms of the `Contact.*` quantities (`rowMean` is `Contact.Rrow`, `rowGauss` is
`Contact.Gterm`, `shiftQ` is `Contact.Qbl`, `markE` is `Contact.frobP`/`frobM`, `incRowE` is
`Contact.Srow`/`Smin`), stated at any point of the capped family (`CapCtx G d p S λ` with sources
in `[0, λ s]^V`, AUDIT-C §1 "Cap(H, y)") and any root `v ∈ S`, with `N = N_S(v)` (`nbhd G S v`).

* Scalars: `kStar d p = k_* = ⌈16 p / log d⌉`.
* Star level (`x ∈ ℝ^N`): clipped powers `clipPow` (`α^{p-m} β^{p-m'}`), and the star forms of
  the physical row and marks: `starRow` (`x_j = G⁺_vj = -(Ax)_j/(aα)`), `starCore`
  (`e_kj = A_kj/(a²α) = G⁺_vv G⁺_{K,kj}`), `starMark` (`c_kj = G⁺_vv G⁺_kj = e_kj + x_k x_j`),
  `starScale` (the unmarked scale `r_i`). The minus forms are `starRow (-a) B`, `starCore a B`.
* Graph level: `rootT` (`t^± = Z_v G^±_vv = D_v h_v^±`), `incRowE` (`S_±`), `diffRowE`
  (`Σ_N E (x_j - z_j)²`), `markE`, `trSqE`, `rowMean` (`𝓡`), `insFH` (`F_H = E_{ν_K} 𝖱Φ`),
  `rowGauss` (`E_{ν_K} 𝖦F / (a² F_H)`), `shiftY`, `shiftM` (`M = a² Y₊/Z_v⁺`, `𝒩 = a² Y₋/Z_v⁻`),
  `shiftQ` (`Q`), `shiftX1`, `shiftX2` (`X₁ = tr M² α⁻²`, `X₂ = tr(M𝒩) α⁻¹β⁻¹`, physical form).
* `CoreInv v w`: `w` depends only on the signs of pairs not containing `v` (a core functional).

Zero sources: `Z_v = D_v / y_v` is never used; the root factor `a²/Z_v` is written `a² y_v / D_v`
(as in `rootMat`), so every quantity is defined at zero sources (AUDIT-C, end of §4.3).
-/

@[expose] public section

namespace BiluLinial.Tight

open Matrix MeasureTheory

/-- `k_* = ⌈16 p / log d⌉`, the retained grade of (E4) (source line 243). -/
noncomputable def kStar (d p : ℕ) : ℕ := ⌈16 * (p : ℝ) / Real.log d⌉₊

/-! ### Star-level functions -/

section Star

variable {ι : Type*} [Fintype ι]

/-- The clipped power `α^{p-m} β^{p-m'}` (`α = (1 - q_A)₊`, `β = (1 - q_B)₊`). -/
noncomputable def clipPow (p m m' : ℕ) (A B : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ :=
  clipF A x ^ (p - m) * clipF B x ^ (p - m')

/-- The unclipped factor `α = 1 - q_A(x)`. -/
def starAlpha (A : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ := 1 - qForm A x

/-- Star form of the root row `x_j = G⁺_vj = -(A x)_j / (a α)` (F1). The minus row is
`z_j = G⁻_vj = starRow (-a) B x j`. -/
noncomputable def starRow (a : ℝ) (A : Matrix ι ι ℝ) (x : ι → ℝ) (j : ι) : ℝ :=
  -(A *ᵥ x) j / (a * starAlpha A x)

/-- Star form of the core mark `e_kj = A_kj / (a² α) = G⁺_vv G⁺_{K,kj}`; the minus core mark is
`f_kj = starCore a B x k j`. -/
noncomputable def starCore (a : ℝ) (A : Matrix ι ι ℝ) (x : ι → ℝ) (k j : ι) : ℝ :=
  A k j / (a ^ 2 * starAlpha A x)

/-- Star form of the full mark `c_kj = G⁺_vv G⁺_kj = e_kj + x_k x_j` (CR2). The minus mark is
`d_kj = starMark (-a) B x k j`. -/
noncomputable def starMark (a : ℝ) (A : Matrix ι ι ℝ) (x : ι → ℝ) (k j : ι) : ℝ :=
  starCore a A x k j + starRow a A x k * starRow a A x j

/-- The unmarked coordinate scale `r_i = |x_i| + √e_ii + |z_i| + √f_ii`. Along the line
`x + t e_i`, `α/α(x) = 1 + 2a x_i t - a² e_ii t²` and `β/β(x) = 1 - 2a z_i t - a² f_ii t²` are
coefficientwise dominated by `(1 + a r_i t)²`. -/
noncomputable def starScale (a : ℝ) (A B : Matrix ι ι ℝ) (x : ι → ℝ) (i : ι) : ℝ :=
  |starRow a A x i| + Real.sqrt (starCore a A x i i) + |starRow (-a) B x i| +
    Real.sqrt (starCore a B x i i)

end Star

/-! ### Core functionals -/

/-- `w` depends only on the signs of pairs not containing `v` (a functional of the own core law
`ν_K`, constant in the fresh star `ξ`). -/
def CoreInv {V : Type*} (v : V) (w : Config V → ℝ) : Prop :=
  ∀ σ σ' : Config V, (∀ e : Sym2 V, v ∉ e → σ e = σ' e) → w σ = w σ'

/-! ### Graph-level quantities at a root -/

section Graph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- `t^τ = Z_v G^τ_vv = D_v h_v^τ` (normalized; `t₊ = 1/α`, `t₋ = 1/β` on the support). -/
noncomputable def rootT (a τ : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) (v : V) : ℝ :=
  diagD G a y S v * hN G a τ y σ S v

/-- `S_τ = Σ_{j ∈ N} E (G^τ_vj)²` (call with `(1, y⁺)` or `(-1, y⁻)`; `Contact.Srow`, `Smin`). -/
noncomputable def incRowE (d p : ℕ) (yp ym : V → ℝ) (S : Finset V) (v : V) (τ : ℝ) (y : V → ℝ) :
    ℝ :=
  ∑ j ∈ nbhd G S v, lawE G p (aOf d p) yp ym S fun σ => greenP G (aOf d p) τ y σ S v j ^ 2

/-- The difference energy `Σ_{j ∈ N} E (G⁺_vj - G⁻_vj)²` (DR1; hypothesis of CR3′). -/
noncomputable def diffRowE (d p : ℕ) (yp ym : V → ℝ) (S : Finset V) (v : V) : ℝ :=
  ∑ j ∈ nbhd G S v, lawE G p (aOf d p) yp ym S fun σ =>
    (greenP G (aOf d p) 1 yp σ S v j - greenP G (aOf d p) (-1) ym σ S v j) ^ 2

/-- `E[(G^τ_vv)² ‖G^τ[N,N]‖_F²]` (`Contact.frobP`, `frobM`). -/
noncomputable def markE (d p : ℕ) (yp ym : V → ℝ) (S : Finset V) (v : V) (τ : ℝ) (y : V → ℝ) :
    ℝ :=
  lawE G p (aOf d p) yp ym S fun σ => greenP G (aOf d p) τ y σ S v v ^ 2 *
    ∑ i ∈ nbhd G S v, ∑ j ∈ nbhd G S v, greenP G (aOf d p) τ y σ S i j ^ 2

/-- `E tr A²` (`(1, y⁺)`) or `E tr B²` (`(-1, y⁻)`) under the actual law (`Contact.trA2`). -/
noncomputable def trSqE (d p : ℕ) (yp ym : V → ℝ) (S : Finset V) (v : V) (τ : ℝ) (y : V → ℝ) :
    ℝ :=
  lawE G p (aOf d p) yp ym S fun σ =>
    (rootMat G (aOf d p) τ y σ S v * rootMat G (aOf d p) τ y σ S v).trace

/-- `𝓡 = (p-1) S₊ - p T` with `T = Σ_N E G⁺_vj G⁻_vj` (`Contact.Rrow`). -/
noncomputable def rowMean (d p : ℕ) (yp ym : V → ℝ) (S : Finset V) (v : V) : ℝ :=
  ((p : ℝ) - 1) * incRowE G d p yp ym S v 1 yp -
    p * ∑ j ∈ nbhd G S v, lawE G p (aOf d p) yp ym S fun σ =>
      greenP G (aOf d p) 1 yp σ S v j * greenP G (aOf d p) (-1) ym σ S v j

/-- The insertion factor `F_H = E_{ν_K} 𝖱 Φ` (own core law, fresh Rademacher star). -/
noncomputable def insFH (d p : ℕ) (yp ym : V → ℝ) (S : Finset V) (v : V) : ℝ :=
  coreE G p (aOf d p) yp ym S v fun σ =>
    radE (starPhi p (rootMat G (aOf d p) 1 yp σ S v) (rootMat G (aOf d p) (-1) ym σ S v))

/-- The Gaussian side of the row comparison, `E_{ν_K} 𝖦F / (a² F_H)` (`Contact.Gterm`). -/
noncomputable def rowGauss (d p : ℕ) (yp ym : V → ℝ) (S : Finset V) (v : V) : ℝ :=
  coreE G p (aOf d p) yp ym S v
      (fun σ => gaussE (rowNum p (rootMat G (aOf d p) 1 yp σ S v)
        (rootMat G (aOf d p) (-1) ym σ S v))) /
    (aOf d p ^ 2 * insFH G d p yp ym S v)

/-- `Y^τ = (P^τ_K + z I)⁻¹[N,N]` (`Y₊` for `(1, y⁺)`, `Y₋` for `(-1, y⁻)`). -/
noncomputable def shiftY (a τ z : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) (v : V) :
    Matrix (nbhd G S v) (nbhd G S v) ℝ :=
  Matrix.of fun i j => coreShift G a τ z y σ S v i j

/-- `M = (a²/Z_v⁺) Y₊ = (a² y_v⁺ / D_v⁺) Y₊` (`τ = 1`) and `𝒩 = (a² y_v⁻ / D_v⁻) Y₋` (`τ = -1`).
On the core support `0 ⪯ M ⪯ A`, `0 ⪯ 𝒩 ⪯ B`, `M, 𝒩 ⪯ (s a²/z) I` (`shift_mat_facts`). -/
noncomputable def shiftM (a τ z : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) (v : V) :
    Matrix (nbhd G S v) (nbhd G S v) ℝ :=
  (a ^ 2 * y v / diagD G a y S v) • shiftY G a τ z y σ S v

/-- The shifted trace energy of (B1) (`Contact.Qbl`),
`Q = a² E{(p-1) (G⁺_vv)² tr Y₊² + p G⁺_vv G⁻_vv tr(Y₊ Y₋)}`, traces written as entry sums. -/
noncomputable def shiftQ (d p : ℕ) (z : ℝ) (yp ym : V → ℝ) (S : Finset V) (v : V) : ℝ :=
  aOf d p ^ 2 * lawE G p (aOf d p) yp ym S fun σ =>
    ((p : ℝ) - 1) * greenP G (aOf d p) 1 yp σ S v v ^ 2 *
        ∑ i ∈ nbhd G S v, ∑ j ∈ nbhd G S v, coreShift G (aOf d p) 1 z yp σ S v i j ^ 2 +
      p * greenP G (aOf d p) 1 yp σ S v v * greenP G (aOf d p) (-1) ym σ S v v *
        ∑ i ∈ nbhd G S v, ∑ j ∈ nbhd G S v,
          coreShift G (aOf d p) 1 z yp σ S v i j * coreShift G (aOf d p) (-1) z ym σ S v i j

/-- `X₁ = tr M² · t₊²` (`= tr M² / α²` on the support). -/
noncomputable def shiftX1 (d p : ℕ) (z : ℝ) (yp : V → ℝ) (σ : Config V) (S : Finset V) (v : V) :
    ℝ :=
  (shiftM G (aOf d p) 1 z yp σ S v * shiftM G (aOf d p) 1 z yp σ S v).trace *
    rootT G (aOf d p) 1 yp σ S v ^ 2

/-- `X₂ = tr(M𝒩) · t₊ t₋` (`= tr(M𝒩) / (αβ)` on the support). -/
noncomputable def shiftX2 (d p : ℕ) (z : ℝ) (yp ym : V → ℝ) (σ : Config V) (S : Finset V)
    (v : V) : ℝ :=
  (shiftM G (aOf d p) 1 z yp σ S v * shiftM G (aOf d p) (-1) z ym σ S v).trace *
    rootT G (aOf d p) 1 yp σ S v * rootT G (aOf d p) (-1) ym σ S v

end Graph

end BiluLinial.Tight
