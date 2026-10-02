/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecB.WTRemArith

/-!
# The own-core (E4) remainder of the WT observables (node TB.WT5r°)

See the module docstring of `BiluLinial.Tight.SecB.WT` for the development.
-/

@[expose] public section

namespace BiluLinial.Tight.SecB

open Matrix

universe u

/-- **TB.WT5r°** (own-core (E4) remainder at depth `k_* = ⌈16p/log d⌉`). For
the normalized observables `Φ H q_L`, `tr L · Φ H` (`starObsQ`, `starObsT`):
`|E_core[𝖦F - Σ_{|j|_g ≤ k_*} c_j 𝖱 ∂^{2j}F]| ≤ F_H d^{-M-1}` (summed over the two observables).
Sketch (source lines 1043–1071; AUDIT-B §2.5):
* (R1) star form: on `{q_A, q_B < 1}`, by the vertex-Schur formulas at `i` (`SecA.schur_of_posDef`
  for `P̃(x) + zY`, as in `precSub_ins`) every diagonal factor of `H` is
  `c_t + κ_t (ℓ_t·x)²/α_t(x)` (`k ≠ i`) or `κ_t/α_t(x)` (`k = i`), `α_t = 1 - q_{A_t}`, with
  `A_t` the (shifted) root matrix of the branch of `t`, `A_t ⪯ A` resp. `⪯ B`; unshifted factors
  are absorbed in `α₊^p β₊^p`, shifted ones are smooth near `{α ≥ 0, β ≥ 0}`
  (`α_h ≥ (D α + h y_i)/(D + h y_i)`);
* (R2) `SmoothBdd (4k_* + 4)` (local: `≡ 0` near points with `α < 0` or `β < 0`; `4k_* + 4 <
  p - m₀ - 4`), as A-SMOOTH (`SecA.smoothBdd_clipObs`) but with the shifted factors;
* (R3) sup bounds `|∂^{2j}F_σ| ≤ m_σ (Cp)^{2Σj} Π_s b_s^{j_s}`, `b_s = A_ss + B_ss`, by a
  majorant algebra as A-MAJ (`SecA.pderivList_clipObs_le_of_interior`), with weights `√b/μ₀`,
  `μ₀ = min(α(x₀), β(x₀))`, the reciprocal bound `|∂^ν(1/α_h)| ≤ n!(1+√2)^n α_h⁻¹ Π λ` (from
  `α_h · α_h⁻¹ = 1` and Leibniz) and `n! ≤ (4k_*+4)^n ≤ (p/10)^n`; `m_σ` collects
  `poly(d, h⁻¹)`, at most `m₀` unshifted core diagonals and the cancellation
  `Z_i (X₊)_ii² ≤ s/α₊²`;
* (R4) (E4) per signing (`gauss_rad_expansion`) and averaging as A-CREM (`CapPoint.crem`):
  Hölder with moments of order `≤ (m₀ + 1)(2k_* + 3) ≤ p/2` ((M3), `CapPoint.core_moment`), the
  floor `F_H ≥ 40^{-p}` ((M4)) and (E6) with the polynomial slack.
Proof: (R4) is `CapPoint.trans_rem_lo` (A-REM with moments only of order `n ≤ 2k_* + 3`);
(R1)–(R3) are `WR.starObsQ_eq_clip`/`WR.hder_Q`/`WR.smoothBdd_Q` (and the `T` versions), with
`m_σ ≤ C_m X^{|l|+3}` (`WR.mQ_le`) and the moments `WR.mom_m`; the parameters are
`WR.params_of` and the final slack `WR.final_bound`.
Checks: `J = ∅` (`𝖦 = 𝖱` are point masses, `retIdx = {0}`), all cores unsupported (`E_core = 0`). -/
theorem wt5_rem_core (m₀ M : ℕ) : Eventually fun _ _ d p h =>
    ∀ ct : Contact.{u} d p, ∀ i ∈ ct.N, ∀ e dir : Bool, ∀ l : List (ct.V × Bool × Bool),
      l.length ≤ m₀ →
      |coreE ct.G p (aOf d p) ct.yp ct.ym ct.S i
            (coreRem ct i (starObsQ ct h e dir i l) (kStarA d p))| +
          |coreE ct.G p (aOf d p) ct.yp ct.ym ct.S i
            (coreRem ct i (starObsT ct h e dir i l) (kStarA d p))| ≤
        insF ct.G p (aOf d p) ct.yp ct.ym ct.S i / (d : ℝ) ^ (M + 1) := by
  have hev := ((((SecA.eventually_regA.and (eventually_base (100 * ((m₀ : ℝ) + 3)))).and
    eventually_h_facts).and (eventually_log_le_p ((M : ℝ) + m₀ + 7))).and
    (WR.eventually_log_ge (128 * ((m₀ : ℝ) + 3)))).and
    (WR.eventually_d_ge (2 * (1280 * 2 ^ m₀ * 30 ^ (m₀ + 3)) + 2 * m₀ + 4))
  refine hev.mono fun c₀ κ₀ d p h hall => ?_
  obtain ⟨⟨⟨⟨⟨hR, hBase⟩, hHf⟩, hpl⟩, hlog⟩, hdX⟩ := hall
  obtain ⟨-, hB, -, hh_eq, hκ0, hκ1⟩ := hBase
  obtain ⟨-, hh0, hhd, hh1, -⟩ := hHf
  intro ct i hiN e dir l hl
  have hi : i ∈ ct.S := WR.N_subset ct hiN
  have hp0 := hR.p_pos
  have hhp : h ≤ 1 / (p : ℝ) ^ 4 := by
    rw [hh_eq]
    exact div_le_div_of_nonneg_right hκ1 (by positivity)
  obtain ⟨hP, hmomord⟩ := WR.params_of hR hlog hB hh0 hhp l hl
  have hlogd := hR.log_pos
  have hpl' : ((M : ℝ) + m₀ + 7) * Real.log d ≤ p := by
    have : (0 : ℝ) ≤ (M : ℝ) + m₀ + 7 := by positivity
    nlinarith
  have h2C : (0 : ℝ) ≤ 2 * (1280 * 2 ^ m₀ * 30 ^ (m₀ + 3)) := by positivity
  have hm0r : (0 : ℝ) ≤ m₀ := Nat.cast_nonneg _
  have hd2 : 2 * (1280 * 2 ^ m₀ * 30 ^ (m₀ + 3)) ≤ (d : ℝ) := by linarith
  have hdm : 2 * (m₀ : ℝ) + 4 ≤ d := by linarith
  set cp := ct.toCapPoint with hcp
  set Mm := WR.Cm h d p l.length *
    (2 * (2 * ((WR.Rset ct i l).card : ℝ) + 1) * (1 + 2 * epsP d p)) ^ (l.length + 3) with hMm
  have hMm0 : 0 < Mm := by
    have := hR.treg.RsqOf_pos
    have := hR.d_pos
    have := SecA.epsP_nonneg hR.treg
    rw [hMm]
    unfold WR.Cm
    positivity
  have hmomn : ∀ n : ℕ, n ≤ 2 * kStarA d p + 3 → 2 * ((l.length + 3) * n) ≤ p := fun n hn =>
    le_trans (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left _ hn)) hmomord
  -- the derivative hypothesis in the form of `trans_rem_lo`
  have hprodbd : ∀ σ : Config ct.V, wtCore ct.G p (aOf d p) ct.yp ct.ym σ ct.S i ≠ 0 →
      ∀ j : nbhd ct.G ct.S i → ℕ,
        ∏ s, Real.sqrt (WR.bd ct σ i s) ^ (2 * j s) = ∏ s, cp.bdiag σ i s ^ j s := by
    intro σ hw j
    obtain ⟨h1, h2⟩ := SecC.posDef_of_wtCore_ne_zero ct.G hw
    have hA := SecA.rootMat_posSemidef ct.G (fun k => (ct.ctx.hyp k).1) h1
    have hB' := SecA.rootMat_posSemidef ct.G (fun k => (ct.ctx.hym k).1) h2
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [pow_mul, Real.sq_sqrt (show 0 ≤ WR.bd ct σ i s from
      add_nonneg hA.diag_nonneg hB'.diag_nonneg)]
    rfl
  have hlen : ∀ j ∈ (topIdx (kStarA d p) : Finset (cp.N i → ℕ)),
      (dEvenList (cp.lN i) j).length ≤ 4 * kStarA d p + 4 := by
    intro j hj
    obtain ⟨hadm, hgr⟩ := mem_topIdx.1 hj
    have := SecA.sum_le_two_mul_grade' hadm
    rw [show (dEvenList (cp.lN i) j).length = 2 * ∑ s, j s from
      SecA.CA.length_dEvenList_univ' j]
    omega
  have hQ := cp.trans_rem_lo hR (v := i) hi (starObsQ ct h e dir i l) (WR.mQ ct h e i l)
    (WR.mQ_nonneg ct hh0 e i l) hMm0
    (fun n hn1 hn => WR.mom_m cp hR hi (WR.Rset ct i l) (WR.Cm_nonneg hh0 hR.treg _)
      (l.length + 3) (WR.mQ ct h e i l) (WR.mQ_nonneg ct hh0 e i l)
      (fun σ hσ => WR.mQ_le hR.treg ct hh0 hh1 e l hσ) hn1 (by omega) (hmomn n hn))
    (fun σ => WR.smoothBdd_Q hR.treg ct hh0 e dir hi l hP σ)
    (fun σ j hj x => by
      have hb := WR.hder_Q hR.treg ct hh0 e dir hi l hP σ (dEvenList (cp.lN i) j)
        (hlen j hj) x
      have e1 : (dEvenList (ι := nbhd ct.G ct.S i) (cp.lN i) j).length = 2 * ∑ s, j s :=
        SecA.CA.length_dEvenList_univ' j
      have e2 : ((dEvenList (ι := nbhd ct.G ct.S i) (cp.lN i) j).map
          fun s => Real.sqrt (WR.bd ct σ i s)).prod =
          ∏ s, Real.sqrt (WR.bd ct σ i s) ^ (2 * j s) :=
        SecA.CA.prod_map_dEvenList_univ' j _
      rw [e1, e2] at hb
      refine le_trans (b := WR.mQ ct h e i l σ * (8 * (p : ℝ)) ^ (2 * ∑ s, j s) *
        ∏ s, Real.sqrt (WR.bd ct σ i s) ^ (2 * j s)) hb ?_
      by_cases hw : wtCore ct.G p (aOf d p) ct.yp ct.ym σ ct.S i ≠ 0
      · rw [hprodbd σ hw j]
      · simp [WR.mQ, hw])
  have hT := cp.trans_rem_lo hR (v := i) hi (starObsT ct h e dir i l) (WR.mT ct h e dir i l)
    (WR.mT_nonneg ct h e dir i l) hMm0
    (fun n hn1 hn => WR.mom_m cp hR hi (WR.Rset ct i l) (WR.Cm_nonneg hh0 hR.treg _)
      (l.length + 3) (WR.mT ct h e dir i l) (WR.mT_nonneg ct h e dir i l)
      (fun σ hσ => WR.mT_le hR.treg ct hh0 hh1 e dir l hσ) hn1 (by omega) (hmomn n hn))
    (fun σ => WR.smoothBdd_T hR.treg ct hh0 e dir hi l hP σ)
    (fun σ j hj x => by
      have hb := WR.hder_T hR.treg ct hh0 e dir hi l hP σ (dEvenList (cp.lN i) j)
        (hlen j hj) x
      have e1 : (dEvenList (ι := nbhd ct.G ct.S i) (cp.lN i) j).length = 2 * ∑ s, j s :=
        SecA.CA.length_dEvenList_univ' j
      have e2 : ((dEvenList (ι := nbhd ct.G ct.S i) (cp.lN i) j).map
          fun s => Real.sqrt (WR.bd ct σ i s)).prod =
          ∏ s, Real.sqrt (WR.bd ct σ i s) ^ (2 * j s) :=
        SecA.CA.prod_map_dEvenList_univ' j _
      rw [e1, e2] at hb
      refine le_trans (b := WR.mT ct h e dir i l σ * (8 * (p : ℝ)) ^ (2 * ∑ s, j s) *
        ∏ s, Real.sqrt (WR.bd ct σ i s) ^ (2 * j s)) hb ?_
      by_cases hw : wtCore ct.G p (aOf d p) ct.yp ct.ym σ ct.S i ≠ 0
      · rw [hprodbd σ hw j]
      · simp [WR.mT, hw])
  have hFH : 0 ≤ cp.FH i := (cp.FH_pos' hR hi).le
  calc |coreE ct.G p (aOf d p) ct.yp ct.ym ct.S i
          (coreRem ct i (starObsQ ct h e dir i l) (kStarA d p))| +
        |coreE ct.G p (aOf d p) ct.yp ct.ym ct.S i
          (coreRem ct i (starObsT ct h e dir i l) (kStarA d p))|
      ≤ Mm * Real.exp (-(p : ℝ)) / d * cp.FH i + Mm * Real.exp (-(p : ℝ)) / d * cp.FH i :=
        add_le_add hQ hT
    _ = 2 * (Mm * Real.exp (-(p : ℝ)) / d * cp.FH i) := by ring
    _ ≤ cp.FH i / (d : ℝ) ^ (M + 1) :=
        WR.final_bound hR hd2 hdm hpl' hh0 hhd hl (WR.Rset_card_le ct i l) hFH

end BiluLinial.Tight.SecB
