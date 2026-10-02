/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecA.EndpointPf

/-!
# The endpoint calculus (E1) (nodes `A-RANK2`, `A-E1`)

Source lines 261–293 (Lemma "Endpoint calculus"); AUDIT-A §2.2 (gap A6).

* `A-RANK2` (`det_add_rank_two`, `inv_add_rank_two_apply`): for an invertible symmetric `P`,
  `G = P⁻¹`, `E = e_v e_iᵀ + e_i e_vᵀ` (`v ≠ i`):
  `det(P + tE) = det P · δ(t)`, `δ(t) = 1 + 2t G_vi - t²(G_vv G_ii - G_vi²)`, and
  `(P + tE)⁻¹_vi = (G_vi - t(G_vv G_ii - G_vi²))/δ(t)` when `δ(t) ≠ 0`.
* The fibre polynomial (`fibrePoly`): along the edge fibre `σ_vi ↦ σ_vi + t` the weighted entry
  `W G⁺_vi` is `W · Π(t)` with `Π(t) = δ₊(t)^{p-1} δ₋(t)^p (G⁺_vi - t a (G⁺_vv G⁺_ii - (G⁺_vi)²))`,
  `δ_±(t) = 1 ± 2 t a G^±_vi - t² a² (G^±_vv G^±_ii - (G^±_vi)²)` (physical entries).
  `𝒟_j G⁺_vi = Π^{(j)}(0) = j! [t^j] Π` (`fibreD`); e.g.
  `𝒟₁ G⁺_vi = -a G⁺_vv G⁺_ii + (2p-1) a (G⁺_vi)² - 2pa G⁺_vi G⁻_vi`.
* `A-E1` (`endpoint_E1`), (E1) with an explicit constant and the law's own normalizer:
  `|E[σ_vi G⁺_vi] - E[𝒟₁ G⁺_vi] + E[𝒟₃ G⁺_vi]/3| ≤ 1.15·10⁹ p⁵ a⁵ E[g*⁶]`,
  `g* = max_± max(G^±_vv, G^±_ii)`.
  Proof: split into edge fibres. If a fibre has a good endpoint with `g* ≤ 1/(64pa)`, then
  `δ_± ≥ 1/2` on `|t| ≤ 2`, the whole segment is good, the fibre sum is `2 L(φ)` for
  `φ(s) = W(s) G⁺(s)_vi`, and `|L(φ)| ≤ (13/60) sup|φ⁽⁵⁾|` (`endpoint_chain`) with
  `|Π⁽⁵⁾(t)| ≤ (4pa)⁵ g*⁶ (1 + a g*|t|)^{4p}` (coefficient majorant `δ_± ≪ (1 + a g* t)²`).
  Otherwise every good endpoint has `64 p a g* > 1` and each term is bounded separately using
  `|𝒟_j G⁺_vi| ≤ (4pa)^j g*^{j+1}`.
-/

@[expose] public section

namespace BiluLinial.Tight.SecA

open Matrix Polynomial

section E1

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- `A-E1` (E1): the endpoint calculus with explicit constant. -/
theorem endpoint_E1 {p : ℕ} (hp : 1 ≤ p) {a : ℝ} (ha : 0 < a) {yp ym : V → ℝ}
    (hyp : ∀ i, 0 ≤ yp i) (hym : ∀ i, 0 ≤ ym i) {S : Finset V} (hZ : 0 < Zw G p a yp ym S)
    {v i : V} (hv : v ∈ S) (hi : i ∈ nbhd G S v) :
    |lawE G p a yp ym S (fun σ => sgn σ v i * greenP G a 1 yp σ S v i) -
        lawE G p a yp ym S (fibreD G p a yp ym S v i 1) +
        lawE G p a yp ym S (fibreD G p a yp ym S v i 3) / 3| ≤
      1.15e9 * (p : ℝ) ^ 5 * a ^ 5 * lawE G p a yp ym S (fun σ => gStar G a yp ym S v i σ ^ 6) := by
  exact endpoint_E1_pf G hp ha hyp hym hZ hv hi

end E1

section Rank2

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `A-RANK2`: the determinant of a rank-two edge perturbation. -/
theorem det_add_rank_two {P : Matrix n n ℝ} (hP : P.IsHermitian) (hdet : IsUnit P.det)
    {v i : n} (hvi : v ≠ i) (t : ℝ) :
    (P + t • edgeE v i).det = P.det * (1 + 2 * t * P⁻¹ v i -
      t ^ 2 * (P⁻¹ v v * P⁻¹ i i - P⁻¹ v i ^ 2)) := by
  exact det_add_rank_two_pf hP hdet hvi t

/-- `A-RANK2`: the inverse entry of a rank-two edge perturbation. -/
theorem inv_add_rank_two_apply {P : Matrix n n ℝ} (hP : P.IsHermitian) (hdet : IsUnit P.det)
    {v i : n} (hvi : v ≠ i) {t : ℝ}
    (hδ : 1 + 2 * t * P⁻¹ v i - t ^ 2 * (P⁻¹ v v * P⁻¹ i i - P⁻¹ v i ^ 2) ≠ 0) :
    (P + t • edgeE v i)⁻¹ v i = (P⁻¹ v i - t * (P⁻¹ v v * P⁻¹ i i - P⁻¹ v i ^ 2)) /
      (1 + 2 * t * P⁻¹ v i - t ^ 2 * (P⁻¹ v v * P⁻¹ i i - P⁻¹ v i ^ 2)) := by
  exact inv_add_rank_two_apply_pf hP hdet hvi hδ

end Rank2

end BiluLinial.Tight.SecA
