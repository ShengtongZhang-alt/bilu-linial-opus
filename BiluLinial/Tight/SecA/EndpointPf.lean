/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecA.EndpointPfFibre

/-!
# Proofs of the endpoint calculus (E1) and the rank-two formulas (`A-E1`, `A-RANK2`)

`endpoint_E1_pf`, `det_add_rank_two_pf` and `inv_add_rank_two_apply_pf` are verbatim copies of
`endpoint_E1`, `det_add_rank_two` and `inv_add_rank_two_apply` of
`BiluLinial.Tight.SecA.Endpoint` (the rank-two ones live in `EndpointPfRank2`).

Proof of (E1) (AUDIT-A §2.2). Flipping the sign of the edge `vi` moves the normalized precisions
by a rank-two perturbation (`epf_precN_flip`). Pair every signing `σ` with its flip `σ'`; then
`2 Σ_σ F(σ) = Σ_σ (F(σ) + F(σ'))` with `F = W (σ_vi G⁺_vi - 𝒟₁ + 𝒟₃/3)`, and it suffices that
`|F(σ) + F(σ')| ≤ K (B(σ) + B(σ'))`, `B = W g*⁶`, `K = 1.15·10⁹ p⁵ a⁵`. If one endpoint is
positive definite with `64 p a g* ≤ 1`, this is `epf_caseA` (the other endpoint is positive
definite by the rank-two criterion); otherwise each endpoint is bounded by `epf_caseB` (bad
endpoints have weight `0`).
-/

@[expose] public section

namespace BiluLinial.Tight.SecA

open Matrix Polynomial

section E1

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] in
theorem epf_sgn_cases (σ : Config V) (u w : V) : sgn σ u w = 1 ∨ sgn σ u w = -1 := by
  unfold sgn
  rcases Int.units_eq_one_or (σ s(u, w)) with h | h <;> simp [h]

omit [Fintype V] [DecidableEq V] in
theorem epf_sgn_swap (σ : Config V) (u w : V) : sgn σ w u = sgn σ u w := by
  unfold sgn; rw [Sym2.eq_swap]

omit [Fintype V] in
/-- Flipping the sign of the edge `vi` is a rank-two perturbation of the normalized precision. -/
theorem epf_precN_flip (a τ : ℝ) (y : V → ℝ) (σ : Config V) {S : Finset V} {v i : V}
    (hv : v ∈ S) (hi : i ∈ S) (hadj : G.Adj v i) :
    precN G a τ y (FloorIns.flipAt s(v, i) σ) S =
      precN G a τ y σ S +
        (τ * a * (Real.sqrt (y v) * Real.sqrt (y i)) * (-2 * sgn σ v i)) • edgeE v i := by
  have hvi : v ≠ i := G.ne_of_adj hadj
  ext u w
  simp only [precN, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    epf_edgeE_apply, FloorIns.sgn_flipAt]
  by_cases h1 : u = v ∧ w = i
  · rw [h1.1, h1.2]
    simp only [hvi, hvi.symm, hv, hi, hadj, eq_self, and_self, ↓reduceIte]
    ring
  · by_cases h2 : u = i ∧ w = v
    · rw [h2.1, h2.2]
      have hsw : s(i, v) = s(v, i) := Sym2.eq_swap
      simp only [hvi, hvi.symm, hv, hi, hadj.symm, hsw, epf_sgn_swap σ v i, eq_self, and_self,
        ↓reduceIte]
      ring
    · have hne : s(u, w) ≠ s(v, i) := by
        rw [Ne, Sym2.eq_iff]; tauto
      have c1 : ¬(v = u ∧ i = w) := fun h => h1 ⟨h.1.symm, h.2.symm⟩
      have c2 : ¬(i = u ∧ v = w) := fun h => h2 ⟨h.1.symm, h.2.symm⟩
      simp only [ite_eq_right hne, ite_eq_right c1, ite_eq_right c2, add_zero, mul_zero]

/-- The summand `W (σ_vi G⁺_vi - 𝒟₁ + 𝒟₃/3)` of (E1). -/
noncomputable def epf_F (p : ℕ) (a : ℝ) (yp ym : V → ℝ) (S : Finset V) (v i : V)
    (σ : Config V) : ℝ :=
  wt G p a yp ym σ S * (sgn σ v i * greenP G a 1 yp σ S v i - fibreD G p a yp ym S v i 1 σ +
    fibreD G p a yp ym S v i 3 σ / 3)

/-- The summand `W g*⁶` of the right-hand side of (E1). -/
noncomputable def epf_B (p : ℕ) (a : ℝ) (yp ym : V → ℝ) (S : Finset V) (v i : V)
    (σ : Config V) : ℝ :=
  wt G p a yp ym σ S * gStar G a yp ym S v i σ ^ 6

theorem epf_wt_nonneg (p : ℕ) (a : ℝ) (yp ym : V → ℝ) (σ : Config V) (S : Finset V) :
    0 ≤ wt G p a yp ym σ S := by
  unfold wt
  split_ifs with h
  · exact pow_nonneg (mul_nonneg h.1.det_pos.le h.2.det_pos.le) p
  · exact le_rfl

theorem epf_B_nonneg (p : ℕ) (a : ℝ) (yp ym : V → ℝ) (S : Finset V) (v i : V) (σ : Config V) :
    0 ≤ epf_B G p a yp ym S v i σ :=
  mul_nonneg (epf_wt_nonneg G p a yp ym σ S) (by positivity)

theorem epf_F_good {p : ℕ} {a : ℝ} {yp ym : V → ℝ} {S : Finset V} {v i : V} {σ : Config V}
    (h : (precN G a 1 yp σ S).PosDef ∧ (precN G a (-1) ym σ S).PosDef) :
    epf_F G p a yp ym S v i σ = epf_U p (precN G a 1 yp σ S) (precN G a (-1) ym σ S) *
      (sgn σ v i * (Real.sqrt (yp v) * (precN G a 1 yp σ S)⁻¹ v i * Real.sqrt (yp i)) -
        epf_D p a (precN G a 1 yp σ S) (precN G a (-1) ym σ S) (Real.sqrt (yp v))
          (Real.sqrt (yp i)) (Real.sqrt (ym v)) (Real.sqrt (ym i)) v i 1 +
        epf_D p a (precN G a 1 yp σ S) (precN G a (-1) ym σ S) (Real.sqrt (yp v))
          (Real.sqrt (yp i)) (Real.sqrt (ym v)) (Real.sqrt (ym i)) v i 3 / 3) := by
  rw [epf_F, wt, ite_eq_left h]
  rfl

theorem epf_B_good {p : ℕ} {a : ℝ} {yp ym : V → ℝ} {S : Finset V} {v i : V} {σ : Config V}
    (h : (precN G a 1 yp σ S).PosDef ∧ (precN G a (-1) ym σ S).PosDef) :
    epf_B G p a yp ym S v i σ = epf_U p (precN G a 1 yp σ S) (precN G a (-1) ym σ S) *
      epf_gs (precN G a 1 yp σ S) (precN G a (-1) ym σ S) (Real.sqrt (yp v))
        (Real.sqrt (yp i)) (Real.sqrt (ym v)) (Real.sqrt (ym i)) v i ^ 6 := by
  rw [epf_B, wt, ite_eq_left h]
  rfl

theorem epf_F_bad {p : ℕ} {a : ℝ} {yp ym : V → ℝ} {S : Finset V} {v i : V} {σ : Config V}
    (h : ¬((precN G a 1 yp σ S).PosDef ∧ (precN G a (-1) ym σ S).PosDef)) :
    epf_F G p a yp ym S v i σ = 0 := by
  rw [epf_F, wt, ite_eq_right h, zero_mul]

theorem epf_B_bad {p : ℕ} {a : ℝ} {yp ym : V → ℝ} {S : Finset V} {v i : V} {σ : Config V}
    (h : ¬((precN G a 1 yp σ S).PosDef ∧ (precN G a (-1) ym σ S).PosDef)) :
    epf_B G p a yp ym S v i σ = 0 := by
  rw [epf_B, wt, ite_eq_right h, zero_mul]

/-- Case A at a signing: a small positive definite endpoint controls the whole fibre. -/
theorem epf_caseA_graph {p : ℕ} (hp : 1 ≤ p) {a : ℝ} (ha : 0 < a) {yp ym : V → ℝ}
    {S : Finset V} {v i : V} (hv : v ∈ S) (hi : i ∈ S) (hadj : G.Adj v i) {σ : Config V}
    (hgood : (precN G a 1 yp σ S).PosDef ∧ (precN G a (-1) ym σ S).PosDef)
    (hsmall : 64 * p * a * gStar G a yp ym S v i σ ≤ 1) :
    |epf_F G p a yp ym S v i σ + epf_F G p a yp ym S v i (FloorIns.flipAt s(v, i) σ)| ≤
      1.15e9 * (p : ℝ) ^ 5 * a ^ 5 * epf_B G p a yp ym S v i σ := by
  have hvi : v ≠ i := G.ne_of_adj hadj
  have hp' := epf_precN_flip G a 1 yp σ hv hi hadj
  have hm' := epf_precN_flip G a (-1) ym σ hv hi hadj
  have hs₀ := epf_sgn_cases σ v i
  have hκ : |(-2 * sgn σ v i)| ≤ 2 := by
    rcases hs₀ with h | h <;> rw [h] <;> norm_num
  obtain ⟨hg, hx, hdx, hy, hdy⟩ := epf_base_bounds hgood.1 hgood.2 hvi (Real.sqrt (yp v))
    (Real.sqrt (yp i)) (Real.sqrt (ym v)) (Real.sqrt (ym i))
  have hNp' : (precN G a 1 yp (FloorIns.flipAt s(v, i) σ) S).PosDef := by
    rw [hp']
    exact epf_caseA_posDef_plus hp ha hgood.1 hvi _ _ _ _ hκ hg hx hdx hsmall
  have hNm' : (precN G a (-1) ym (FloorIns.flipAt s(v, i) σ) S).PosDef := by
    rw [hm']
    exact epf_caseA_posDef_minus hp ha hgood.2 hvi _ _ _ _ hκ hg hy hdy hsmall
  have hs' : sgn (FloorIns.flipAt s(v, i) σ) v i = -sgn σ v i := by
    rw [FloorIns.sgn_flipAt, ite_eq_left rfl]
  have hA := epf_caseA hp ha hgood.1 hgood.2 hNp' hNm' hvi _ _ _ _ hs₀ hp' hm' hsmall
  rw [epf_F_good G hgood, epf_F_good G ⟨hNp', hNm'⟩, hs', epf_B_good G hgood]
  refine hA.trans ?_
  have hY : 0 ≤ epf_U p (precN G a 1 yp σ S) (precN G a (-1) ym σ S) *
      epf_gs (precN G a 1 yp σ S) (precN G a (-1) ym σ S) (Real.sqrt (yp v))
        (Real.sqrt (yp i)) (Real.sqrt (ym v)) (Real.sqrt (ym i)) v i ^ 6 :=
    mul_nonneg (epf_U_nonneg p hgood.1 hgood.2) (by positivity)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (by norm_num) (by positivity)) (pow_nonneg ha.le 5)) hY

/-- Case B at a signing: an endpoint that is not small is bounded on its own. -/
theorem epf_caseB_graph {p : ℕ} (hp : 1 ≤ p) {a : ℝ} (ha : 0 < a) {yp ym : V → ℝ}
    {S : Finset V} {v i : V} (hadj : G.Adj v i) {σ : Config V}
    (hns : ¬(((precN G a 1 yp σ S).PosDef ∧ (precN G a (-1) ym σ S).PosDef) ∧
      64 * p * a * gStar G a yp ym S v i σ ≤ 1)) :
    |epf_F G p a yp ym S v i σ| ≤ 1.15e9 * (p : ℝ) ^ 5 * a ^ 5 * epf_B G p a yp ym S v i σ := by
  by_cases hgood : (precN G a 1 yp σ S).PosDef ∧ (precN G a (-1) ym σ S).PosDef
  · have hbig : 1 < 64 * p * a * gStar G a yp ym S v i σ :=
      not_le.mp fun h => hns ⟨hgood, h⟩
    rw [epf_F_good G hgood, epf_B_good G hgood]
    have hs : |sgn σ v i| ≤ 1 := by
      rcases epf_sgn_cases σ v i with h | h <;> rw [h] <;> norm_num
    exact epf_caseB hp ha hgood.1 hgood.2 (G.ne_of_adj hadj) _ _ _ _ hs hbig
  · rw [epf_F_bad G hgood, epf_B_bad G hgood]
    simp

/-- `A-E1` (E1): the endpoint calculus with explicit constant. -/
theorem endpoint_E1_pf {p : ℕ} (hp : 1 ≤ p) {a : ℝ} (ha : 0 < a) {yp ym : V → ℝ}
    (hyp : ∀ i, 0 ≤ yp i) (hym : ∀ i, 0 ≤ ym i) {S : Finset V} (hZ : 0 < Zw G p a yp ym S)
    {v i : V} (hv : v ∈ S) (hi : i ∈ nbhd G S v) :
    |lawE G p a yp ym S (fun σ => sgn σ v i * greenP G a 1 yp σ S v i) -
        lawE G p a yp ym S (fibreD G p a yp ym S v i 1) +
        lawE G p a yp ym S (fibreD G p a yp ym S v i 3) / 3| ≤
      1.15e9 * (p : ℝ) ^ 5 * a ^ 5 * lawE G p a yp ym S (fun σ => gStar G a yp ym S v i σ ^ 6) := by
  obtain ⟨hiS, hadj⟩ := (FloorIns.mem_nbhd G).1 hi
  have hK0 : (0 : ℝ) ≤ 1.15e9 * (p : ℝ) ^ 5 * a ^ 5 :=
    mul_nonneg (mul_nonneg (by norm_num) (by positivity)) (pow_nonneg ha.le 5)
  have hflip : ∀ f : Config V → ℝ, ∑ σ, f (FloorIns.flipAt s(v, i) σ) = ∑ σ, f σ := fun f => by
    have h := Equiv.sum_comp ((FloorIns.flipAt_involutive s(v, i)).toPerm _) f
    simpa only [Function.Involutive.coe_toPerm] using h
  have hpair : ∀ σ,
      |epf_F G p a yp ym S v i σ + epf_F G p a yp ym S v i (FloorIns.flipAt s(v, i) σ)| ≤
      1.15e9 * (p : ℝ) ^ 5 * a ^ 5 *
        (epf_B G p a yp ym S v i σ + epf_B G p a yp ym S v i (FloorIns.flipAt s(v, i) σ)) := by
    intro σ
    by_cases hs : ((precN G a 1 yp σ S).PosDef ∧ (precN G a (-1) ym σ S).PosDef) ∧
        64 * p * a * gStar G a yp ym S v i σ ≤ 1
    · refine (epf_caseA_graph G hp ha hv hiS hadj hs.1 hs.2).trans ?_
      exact mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_right (epf_B_nonneg G p a yp ym S v i _)) hK0
    · by_cases hs' : ((precN G a 1 yp (FloorIns.flipAt s(v, i) σ) S).PosDef ∧
          (precN G a (-1) ym (FloorIns.flipAt s(v, i) σ) S).PosDef) ∧
          64 * p * a * gStar G a yp ym S v i (FloorIns.flipAt s(v, i) σ) ≤ 1
      · have h := epf_caseA_graph G hp ha hv hiS hadj hs'.1 hs'.2
        rw [FloorIns.flipAt_involutive s(v, i) σ, add_comm] at h
        refine h.trans ?_
        exact mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_left (epf_B_nonneg G p a yp ym S v i _)) hK0
      · have h1 := epf_caseB_graph G hp ha hadj hs
        have h2 := epf_caseB_graph G hp ha hadj hs'
        calc |epf_F G p a yp ym S v i σ + epf_F G p a yp ym S v i (FloorIns.flipAt s(v, i) σ)|
            ≤ |epf_F G p a yp ym S v i σ| +
                |epf_F G p a yp ym S v i (FloorIns.flipAt s(v, i) σ)| := abs_add_le _ _
          _ ≤ 1.15e9 * (p : ℝ) ^ 5 * a ^ 5 * epf_B G p a yp ym S v i σ +
                1.15e9 * (p : ℝ) ^ 5 * a ^ 5 *
                  epf_B G p a yp ym S v i (FloorIns.flipAt s(v, i) σ) := add_le_add h1 h2
          _ = _ := by ring
  have hmain : |∑ σ, epf_F G p a yp ym S v i σ| ≤
      1.15e9 * (p : ℝ) ^ 5 * a ^ 5 * ∑ σ, epf_B G p a yp ym S v i σ := by
    have h2 : 2 * |∑ σ, epf_F G p a yp ym S v i σ| ≤
        2 * (1.15e9 * (p : ℝ) ^ 5 * a ^ 5 * ∑ σ, epf_B G p a yp ym S v i σ) := by
      calc 2 * |∑ σ, epf_F G p a yp ym S v i σ|
          = |∑ σ, (epf_F G p a yp ym S v i σ +
              epf_F G p a yp ym S v i (FloorIns.flipAt s(v, i) σ))| := by
            rw [Finset.sum_add_distrib, hflip (epf_F G p a yp ym S v i), ← two_mul, abs_mul,
              abs_two]
        _ ≤ ∑ σ, |epf_F G p a yp ym S v i σ +
              epf_F G p a yp ym S v i (FloorIns.flipAt s(v, i) σ)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ σ, 1.15e9 * (p : ℝ) ^ 5 * a ^ 5 *
              (epf_B G p a yp ym S v i σ + epf_B G p a yp ym S v i (FloorIns.flipAt s(v, i) σ)) :=
            Finset.sum_le_sum fun σ _ => hpair σ
        _ = 2 * (1.15e9 * (p : ℝ) ^ 5 * a ^ 5 * ∑ σ, epf_B G p a yp ym S v i σ) := by
            rw [← Finset.mul_sum, Finset.sum_add_distrib, hflip (epf_B G p a yp ym S v i)]
            ring
    linarith
  have hsumF : ∑ σ, epf_F G p a yp ym S v i σ =
      (∑ σ, wt G p a yp ym σ S * (sgn σ v i * greenP G a 1 yp σ S v i)) -
        (∑ σ, wt G p a yp ym σ S * fibreD G p a yp ym S v i 1 σ) +
        (∑ σ, wt G p a yp ym σ S * fibreD G p a yp ym S v i 3 σ) / 3 := by
    rw [Finset.sum_div, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [epf_F]
    ring
  have hlhs : lawE G p a yp ym S (fun σ => sgn σ v i * greenP G a 1 yp σ S v i) -
        lawE G p a yp ym S (fibreD G p a yp ym S v i 1) +
        lawE G p a yp ym S (fibreD G p a yp ym S v i 3) / 3 =
      (∑ σ, epf_F G p a yp ym S v i σ) / Zw G p a yp ym S := by
    rw [hsumF]
    simp only [lawE]
    ring
  have hrhs : lawE G p a yp ym S (fun σ => gStar G a yp ym S v i σ ^ 6) =
      (∑ σ, epf_B G p a yp ym S v i σ) / Zw G p a yp ym S := by
    simp only [lawE, epf_B]
  rw [hlhs, hrhs, abs_div, abs_of_pos hZ, mul_div_assoc']
  exact div_le_div_of_nonneg_right hmain hZ.le

end E1

end BiluLinial.Tight.SecA
