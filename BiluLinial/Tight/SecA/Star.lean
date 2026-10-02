/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecA.Defs
public import BiluLinial.Tight.SecA.StarLine
public import BiluLinial.Tight.SecA.StarMat
public import BiluLinial.Tight.SecA.StarCR
public import BiluLinial.Tight.Tools.Cov

/-!
# Star-level analysis on `ℝ^N` (nodes `A-CLIP`, `A-MAJ`, `A-E5`, `A-EPB4`, `A-CR`, `A-PDOM`)

Pure analysis of the clipped observables `g α₊^{e₁} β₊^{e₂}` (`clipObs`), `α = (1 - q_A)₊`,
`β = (1 - q_B)₊`, `A, B ⪰ 0` (source lines 296–343, 393–397, 417–422, 456–491;
AUDIT-A §2.4, §2.6, §2.9, §2.12, §2.13).

* `A-CLIP` (`contDiff_posPow`, `contDiff_clipObs`): `t ↦ t₊^e` is `C^{e-1}`; a clipped observable
  with smooth prefactor is `C^{min(e₁,e₂)-1}`.
* `A-MAJ` (`pderivList_clipObs_le_of_interior`), the majorant lemma of AUDIT-A §2.4: at a point
  `x₀` with `q_A(x₀), q_B(x₀) < 1`, if the three quadratics `g`, `1 - q_A`, `1 - q_B` satisfy the
  majorant condition `QuadMaj` with scales `m_g, m_α, m_β` and common weights `λ`, then every
  iterated partial derivative of order `n` is at most `m_g m_α^{e₁} m_β^{e₂} (2(1+e₁+e₂))^n λ^ν`.
  Proof: near `x₀` the observable is the product of `1 + e₁ + e₂` quadratics; each satisfies
  `|∂^ν q(x₀)| ≤ m 2^n λ^ν`; the bound `M K^n λ^ν` is closed under products (Leibniz and the
  binomial theorem: `Σ_a C(n,a) K₁^a K₂^{n-a} = (K₁+K₂)^n`).
* `A-E5` (`pderivList_clipObs_le`), (E5) as sup bounds: with `λ_i = √b_i`, `b_i = A_ii + B_ii`,
  `m_α = m_β = 1`, every derivative of order `n < min(e₁,e₂)` is bounded by
  `m_g (2(1+e₁+e₂))^n Π √b_i` everywhere (outside `{q_A, q_B < 1}` the derivative vanishes by
  `A-CLIP0`). `A-SMOOTH` (`smoothBdd_clipObs`) follows.
* `A-EPB4` (`iter_pderiv_clipObs_le`), the refined single-coordinate bound (gap A7): along
  `x₀ + t e_i` the observable is `α₀^{e₁} β₀^{e₂}` times a product of one-variable quadratics, and
  `|∂_i^k F(x₀)| ≤ k! α₀^{e₁} β₀^{e₂} [t^k] (m₀ + m₁ t + m₂ t²)(1 + 2r_α t + ω_α t²)^{e₁}
  (1 + 2r_β t + ω_β t²)^{e₂}`.
* (C1b), the whitened Gaussian nonnegativity `N_G ≥ f_G w ≥ 0` (source lines 393–397,
  417–422), is T.COV (`gaussE_NG_ge_whitened`, `gaussE_NG_nonneg`, `Tight/Tools/Cov.lean`), and
  the identity `N_G = 2 𝖦 F` is T.GIBP2 (`two_mul_gaussE_starF`); they are used, not restated.
* `A-CR` (`gaussE_C4`), the Cramér–Rao form (C4). Only the consequence `I - Σ ⪯ E∇²V` of
  Cramér–Rao is used, and it follows from three Gaussian integrations by parts
  (`StarCalc.gaussE_qForm_clip` with `N = M, MA, MB`): `RHS - LHS = 4p² 𝖦[α^{p-2}β^{p-2}
  q_M(βAx + αBx)] ≥ 0`. Needs `p ≥ 3`; `M ⪰ 0` arbitrary.
* `A-PDOM` (`pdom`): for `0 ⪯ M ⪯ A`: `tr(MA), tr(MB) ≤ Θ`, `AMA ⪯ ΘA`, `BMB ⪯ ΘB`.

The proofs are in the namespace `StarCalc`: `SecA/StarSmooth.lean` (CLIP, CLIP0, MAJ, E5,
SMOOTH), `SecA/StarLine.lean` (EPB4), `SecA/StarMat.lean` (PDOM), `SecA/StarCR.lean` (CR).
-/

@[expose] public section

namespace BiluLinial.Tight.SecA

open Matrix MeasureTheory Polynomial
open scoped ContDiff

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `A-CLIP`: `t ↦ t₊^e` is `C^{e-1}`. -/
theorem contDiff_posPow (e : ℕ) :
    ContDiff ℝ ((e - 1 : ℕ) : WithTop ℕ∞) (fun t : ℝ => max t 0 ^ e) :=
  StarCalc.contDiff_posPow' e

/-- `A-CLIP`: a clipped observable with smooth prefactor is `C^{min(e₁,e₂)-1}`. -/
theorem contDiff_clipObs {g : (ι → ℝ) → ℝ} (hg : ContDiff ℝ ∞ g) (e₁ e₂ : ℕ)
    (A B : Matrix ι ι ℝ) :
    ContDiff ℝ ((min e₁ e₂ - 1 : ℕ) : WithTop ℕ∞) (clipObs g e₁ e₂ A B) :=
  StarCalc.contDiff_clipObs' hg e₁ e₂ A B

/-- `A-CLIP0`: outside `{q_A < 1, q_B < 1}` every derivative of order `< min(e₁,e₂)` of a clipped
observable vanishes. -/
theorem pderivList_clipObs_eq_zero {A B : Matrix ι ι ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    {g : (ι → ℝ) → ℝ} (hg : ContDiff ℝ ∞ g) {e₁ e₂ : ℕ} (l : List ι)
    (hl : l.length < min e₁ e₂) {x : ι → ℝ} (hx : 1 ≤ qForm A x ∨ 1 ≤ qForm B x) :
    pderivList l (clipObs g e₁ e₂ A B) x = 0 :=
  StarCalc.pderivList_clipObs_eq_zero' hg l hl hx

/-- `A-MAJ`: the majorant bound at an interior point. -/
theorem pderivList_clipObs_le_of_interior {A B : Matrix ι ι ℝ} {e₁ e₂ : ℕ} {c : ℝ}
    {ℓ : ι → ℝ} {Q : Matrix ι ι ℝ} {x₀ : ι → ℝ} (hα : qForm A x₀ < 1) (hβ : qForm B x₀ < 1)
    {mg mα mβ : ℝ} {lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i) (hg : QuadMaj c ℓ Q x₀ mg lam)
    (hA : QuadMaj 1 0 (-A) x₀ mα lam) (hB : QuadMaj 1 0 (-B) x₀ mβ lam) (l : List ι) :
    |pderivList l (clipObs (quadFn c ℓ Q) e₁ e₂ A B) x₀| ≤
      mg * mα ^ e₁ * mβ ^ e₂ * (2 * (1 + e₁ + e₂ : ℝ)) ^ l.length * (l.map lam).prod :=
  StarCalc.pderivList_clipObs_le_of_interior' hα hβ hlam hg hA hB l

/-- `A-E5`: sup bounds of the derivatives of a clipped observable (orders `< min(e₁,e₂)`). -/
theorem pderivList_clipObs_le {A B : Matrix ι ι ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    {e₁ e₂ : ℕ} {c : ℝ} {ℓ : ι → ℝ} {Q : Matrix ι ι ℝ} {m : ℝ}
    (hg : ∀ x, qForm A x < 1 → qForm B x < 1 →
      QuadMaj c ℓ Q x m fun i => Real.sqrt (A i i + B i i))
    (l : List ι) (hl : l.length < min e₁ e₂) (x : ι → ℝ) :
    |pderivList l (clipObs (quadFn c ℓ Q) e₁ e₂ A B) x| ≤
      m * (2 * (1 + e₁ + e₂ : ℝ)) ^ l.length *
        (l.map fun i => Real.sqrt (A i i + B i i)).prod :=
  StarCalc.pderivList_clipObs_le' hA hB hg l hl x

/-- `A-SMOOTH`: clipped observables are `SmoothBdd` up to order `min(e₁,e₂) - 1`. -/
theorem smoothBdd_clipObs {A B : Matrix ι ι ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    {e₁ e₂ : ℕ} {c : ℝ} {ℓ : ι → ℝ} {Q : Matrix ι ι ℝ} {m : ℝ}
    (hg : ∀ x, qForm A x < 1 → qForm B x < 1 →
      QuadMaj c ℓ Q x m fun i => Real.sqrt (A i i + B i i))
    {n : ℕ} (hn : n < min e₁ e₂) :
    SmoothBdd n (clipObs (quadFn c ℓ Q) e₁ e₂ A B) :=
  StarCalc.smoothBdd_clipObs' hA hB hg hn

/-- `A-EPB4`: the refined single-coordinate bound (coefficient majorant in one variable). -/
theorem iter_pderiv_clipObs_le {A B : Matrix ι ι ℝ} {e₁ e₂ : ℕ} {c : ℝ} {ℓ : ι → ℝ}
    {Q : Matrix ι ι ℝ} {x₀ : ι → ℝ} (hα : qForm A x₀ < 1) (hβ : qForm B x₀ < 1) (i : ι)
    {m₀ m₁ m₂ rα ωα rβ ωβ : ℝ} (h0 : |quadFn c ℓ Q x₀| ≤ m₀)
    (h1 : |ℓ i + ((Q + Qᵀ) *ᵥ x₀) i| ≤ m₁) (h2 : |Q i i| ≤ m₂)
    (hα1 : |((A + Aᵀ) *ᵥ x₀) i| ≤ 2 * rα * clipF A x₀) (hα2 : |A i i| ≤ ωα * clipF A x₀)
    (hβ1 : |((B + Bᵀ) *ᵥ x₀) i| ≤ 2 * rβ * clipF B x₀) (hβ2 : |B i i| ≤ ωβ * clipF B x₀)
    (k : ℕ) :
    |(pderiv i)^[k] (clipObs (quadFn c ℓ Q) e₁ e₂ A B) x₀| ≤
      k.factorial * clipF A x₀ ^ e₁ * clipF B x₀ ^ e₂ *
        ((C m₀ + C m₁ * X + C m₂ * X ^ 2) * (1 + C (2 * rα) * X + C ωα * X ^ 2) ^ e₁ *
          (1 + C (2 * rβ) * X + C ωβ * X ^ 2) ^ e₂).coeff k :=
  StarCalc.iter_pderiv_clipObs_le' hα hβ i h0 h1 h2 hα1 hα2 hβ1 hβ2 k

/-- `A-CR`: the Cramér–Rao form (C4) of the Gaussian bias of `(tr M - q_M) Φ`. -/
theorem gaussE_C4 {A B M : Matrix ι ι ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hM : M.PosSemidef) {p : ℕ} (hp : 3 ≤ p) :
    gaussE (fun x => (M.trace - qForm M x) * starPhi p A B x) ≤
      2 * p * gaussE (fun x => (M * A).trace * clipF A x ^ (p - 1) * clipF B x ^ p +
          (M * B).trace * clipF A x ^ p * clipF B x ^ (p - 1)) +
        4 * p * gaussE (fun x => qForm (A * M * A) x * clipF A x ^ (p - 2) * clipF B x ^ p +
          qForm (B * M * B) x * clipF A x ^ p * clipF B x ^ (p - 2)) :=
  StarCalc.gaussE_C4' hA hB hM hp

/-- `A-PDOM`: prefactor domination for `0 ⪯ M ⪯ A`, `Θ = tr(A² + B²)`. -/
theorem pdom {A B M : Matrix ι ι ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hM : M.PosSemidef) (hMA : (A - M).PosSemidef) :
    (M * A).trace ≤ (A * A + B * B).trace ∧ (M * B).trace ≤ (A * A + B * B).trace ∧
      ((A * A + B * B).trace • A - A * M * A).PosSemidef ∧
      ((A * A + B * B).trace • B - B * M * B).PosSemidef :=
  StarCalc.pdom' hA hB hM hMA

end BiluLinial.Tight.SecA
