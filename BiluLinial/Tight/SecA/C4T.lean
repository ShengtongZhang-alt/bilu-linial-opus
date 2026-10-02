/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecA.C4TLeft

/-!
# The transfer of (C4) to signs (node `A-C4T`, split)

Source lines 480–540; AUDIT-A §2.13. `transfer_C4T_pf` has the statement of
`SecA.transfer_C4T` (`SecA/Shift.lean`) and is proved here from five sub-nodes about the three
star observables of (C4) at the root `v` (`M` core-measurable, `0 ⪯ M ⪯ A` on the core support):

* `F₀ = (tr M - q_M) Φ` (`c4F0`), `F₁₂ = tr(MA) α^{p-1}β^p + tr(MB) α^pβ^{p-1}` (`c4F12`),
  `F₃₄ = q_{AMA} α^{p-2}β^p + q_{BMB} α^pβ^{p-2}` (`c4F34`); the last two are the integrands of the
  right side of `A-CR` (`gaussE_C4`).
* `A-C4T-RET` (`c4_ret0`, `c4_ret12`, `c4_ret34`): `E_{ν_K} 𝖱F/F_H` is the actual expectation of
  `F(ξ)/Φ(ξ)` (`coreE_radE_div_eq`), i.e. of `tr M - q_M(ξ)`, `tr(MA)τ⁺ + tr(MB)τ⁻`,
  `q_{AMA}(ξ)(τ⁺)² + q_{BMB}(ξ)(τ⁻)²` (F1: `τ⁺ α(ξ) = 1`, `τ⁻ β(ξ) = 1` on the support).
* `A-C4T-CR` (`c4_cr`): `E_{ν_K} 𝖦F₀ ≤ 2p E_{ν_K} 𝖦F₁₂ + 4p E_{ν_K} 𝖦F₃₄` (`A-CR` pointwise on
  the core support, where `A, B, M ⪰ 0`).
* `A-C4T-T0` (`c4_trans0`): `|E_{ν_K}(𝖦F₀ - 𝖱F₀)/F_H| ≤ C{p⁴(ρ+b₀)/d + p²/d + p⁸/d² + e^{-p}/d}`
  (`A-TRANS`; grade one by `A-EPB4`, the row bound and T.IL, gap A7).
* `A-C4T-T12`, `A-C4T-T34` (`c4_trans12`, `c4_trans34`):
  `|E_{ν_K}(𝖦F - 𝖱F)/F_H| ≤ C{p⁴(ρ+b₀)/d + e^{-p}/d}` (relative transfer, endpoint majorant
  `X = Θ τ`-type with `E X ≤ C(ρ+b₀)` by `A-C3b` and T.IL; the sup scale `tr(MA) + tr(MB)` is
  quadratic in the core diagonals, so the own-core moments are needed only up to the order
  `2k_* + 3` that `A-CREM` uses).

Parent (proved below): `E[tr M - q_M] = E_{ν_K}𝖱F₀/F_H = E_{ν_K}𝖦F₀/F_H - D₀ ≤
2p(E_{ν_K}𝖱F₁₂/F_H + D₁₂) + 4p(E_{ν_K}𝖱F₃₄/F_H + D₃₄) - D₀`, and `p e^{-p}/d ≤ p⁹/d²`.
-/

@[expose] public section

universe u

namespace BiluLinial.Tight

open Matrix

namespace CapPoint

variable {d p : ℕ} (cp : CapPoint.{u} d p)

/-- `F₀ = (tr M - q_M) Φ`. -/
noncomputable def c4F0 {v : cp.V} (M : Config cp.V → Matrix (cp.N v) (cp.N v) ℝ)
    (σ : Config cp.V) (x : cp.N v → ℝ) : ℝ :=
  ((M σ).trace - qForm (M σ) x) * starPhi p (cp.A σ v) (cp.B σ v) x

/-- `F₁₂ = tr(MA) α^{p-1} β^p + tr(MB) α^p β^{p-1}`. -/
noncomputable def c4F12 {v : cp.V} (M : Config cp.V → Matrix (cp.N v) (cp.N v) ℝ)
    (σ : Config cp.V) (x : cp.N v → ℝ) : ℝ :=
  (M σ * cp.A σ v).trace * clipF (cp.A σ v) x ^ (p - 1) * clipF (cp.B σ v) x ^ p +
    (M σ * cp.B σ v).trace * clipF (cp.A σ v) x ^ p * clipF (cp.B σ v) x ^ (p - 1)

/-- `F₃₄ = q_{AMA} α^{p-2} β^p + q_{BMB} α^p β^{p-2}`. -/
noncomputable def c4F34 {v : cp.V} (M : Config cp.V → Matrix (cp.N v) (cp.N v) ℝ)
    (σ : Config cp.V) (x : cp.N v → ℝ) : ℝ :=
  qForm (cp.A σ v * M σ * cp.A σ v) x * clipF (cp.A σ v) x ^ (p - 2) * clipF (cp.B σ v) x ^ p +
    qForm (cp.B σ v * M σ * cp.B σ v) x * clipF (cp.A σ v) x ^ p * clipF (cp.B σ v) x ^ (p - 2)

/-- `F₁₂` as a clipped observable: `(T₁(1 - q_B) + T₂(1 - q_A)) α^{p-1} β^{p-1}`. -/
theorem c4F12_eq_clipObs (hp : 2 ≤ p) {v : cp.V} (M : Config cp.V → Matrix (cp.N v) (cp.N v) ℝ)
    (σ : Config cp.V) :
    cp.c4F12 M σ = clipObs (quadFn ((M σ * cp.A σ v).trace + (M σ * cp.B σ v).trace) 0
      (-((M σ * cp.A σ v).trace • cp.B σ v + (M σ * cp.B σ v).trace • cp.A σ v)))
      (p - 1) (p - 1) (cp.A σ v) (cp.B σ v) := by
  funext x
  set T₁ := (M σ * cp.A σ v).trace with hT₁
  set T₂ := (M σ * cp.B σ v).trace with hT₂
  have hq : quadFn (T₁ + T₂) 0 (-(T₁ • cp.B σ v + T₂ • cp.A σ v)) x =
      T₁ * (1 - qForm (cp.B σ v) x) + T₂ * (1 - qForm (cp.A σ v) x) := by
    simp only [quadFn, qForm, zero_dotProduct, add_zero, Matrix.neg_mulVec, Matrix.add_mulVec,
      Matrix.smul_mulVec, dotProduct_neg, dotProduct_add, dotProduct_smul, smul_eq_mul]
    ring
  simp only [c4F12, clipObs, hq]
  have hp1 : p - 1 ≠ 0 := by omega
  have hp0 : p ≠ 0 := by omega
  by_cases hA : qForm (cp.A σ v) x < 1
  · by_cases hB : qForm (cp.B σ v) x < 1
    · have cA : clipF (cp.A σ v) x = 1 - qForm (cp.A σ v) x := max_eq_left (by linarith)
      have cB : clipF (cp.B σ v) x = 1 - qForm (cp.B σ v) x := max_eq_left (by linarith)
      rw [cA, cB]
      set α := 1 - qForm (cp.A σ v) x
      set β := 1 - qForm (cp.B σ v) x
      have eα : α ^ p = α ^ (p - 1) * α := by rw [← pow_succ, Nat.sub_add_cancel (by omega)]
      have eβ : β ^ p = β ^ (p - 1) * β := by rw [← pow_succ, Nat.sub_add_cancel (by omega)]
      rw [eα, eβ]
      ring
    · have cB : clipF (cp.B σ v) x = 0 := max_eq_right (by linarith)
      rw [cB, zero_pow hp1, zero_pow hp0]
      ring
  · have cA : clipF (cp.A σ v) x = 0 := max_eq_right (by linarith)
    rw [cA, zero_pow hp1, zero_pow hp0]
    ring

/-- F1 at the root: `D_v h_v (1 - q_R(ξ)) = 1` on a positive definite precision (`τ² = 1`). -/
theorem _root_.BiluLinial.Tight.SecA.rootT_mul_one_sub_qForm {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] {a τ : ℝ} (hτ : τ ^ 2 = 1)
    {y : V → ℝ} (hy : ∀ i, 0 ≤ y i) {σ : Config V} {S : Finset V} {v : V} (hv : v ∈ S)
    (hP : (precN G a τ y σ S).PosDef) :
    diagD G a y S v * hN G a τ y σ S v *
      (1 - qForm (rootMat G a τ y σ S v) (rootSigns G σ S v)) = 1 := by
  have h := SecA.inv_hzN_root G hτ le_rfl hy hv hP
  have e1 : hzN G a τ 0 y σ S v = hN G a τ y σ S v := by
    simp only [hzN, zero_smul, add_zero]
    rfl
  have e2 : rootMzG G a τ 0 y σ S v = rootMat G a τ y σ S v := by
    ext i j
    simp [rootMzG, rootMat, coreShift, coreGreen]
  rw [e1, e2, zero_mul, add_zero] at h
  have hh : 0 < hN G a τ y σ S v := hP.inv.diag_pos
  rw [one_div, inv_eq_iff_eq_inv] at h
  have hne : diagD G a y S v * (1 - qForm (rootMat G a τ y σ S v) (rootSigns G σ S v)) ≠ 0 := by
    intro h0
    rw [h0, _root_.inv_zero] at h
    linarith
  calc diagD G a y S v * hN G a τ y σ S v *
        (1 - qForm (rootMat G a τ y σ S v) (rootSigns G σ S v)) =
      hN G a τ y σ S v *
        (diagD G a y S v * (1 - qForm (rootMat G a τ y σ S v) (rootSigns G σ S v))) := by ring
    _ = 1 := by rw [h, inv_mul_cancel₀ hne]

/-- F1: `τ⁺ α(ξ) = 1` and `τ⁻ β(ξ) = 1` at a supported signing (and `α(ξ), β(ξ) > 0`). -/
theorem taup_mul_clipF {v : cp.V} (hv : v ∈ cp.S) {σ : Config cp.V}
    (hσ : wt cp.G p (aOf d p) cp.yp cp.ym σ cp.S ≠ 0) :
    cp.taup σ v * clipF (cp.A σ v) (cp.xi σ v) = 1 ∧
      cp.taum σ v * clipF (cp.B σ v) (cp.xi σ v) = 1 ∧
      0 < clipF (cp.A σ v) (cp.xi σ v) ∧ 0 < clipF (cp.B σ v) (cp.xi σ v) := by
  obtain ⟨hPp, hPm⟩ := SecA.precN_posDef_of_wt cp hσ
  have h1 := SecA.rootT_mul_one_sub_qForm cp.G (τ := 1) (by norm_num) cp.yp_nonneg hv hPp
  have h2 := SecA.rootT_mul_one_sub_qForm cp.G (τ := -1) (by norm_num) cp.ym_nonneg hv hPm
  have hD1 : 0 < diagD cp.G (aOf d p) cp.yp cp.S v :=
    lt_of_lt_of_le one_pos (FloorIns.one_le_diagD cp.G _ cp.yp_nonneg cp.S v)
  have hD2 : 0 < diagD cp.G (aOf d p) cp.ym cp.S v :=
    lt_of_lt_of_le one_pos (FloorIns.one_le_diagD cp.G _ cp.ym_nonneg cp.S v)
  have hh1 : 0 < hN cp.G (aOf d p) 1 cp.yp σ cp.S v := hPp.inv.diag_pos
  have hh2 : 0 < hN cp.G (aOf d p) (-1) cp.ym σ cp.S v := hPm.inv.diag_pos
  have q1 : 0 < 1 - qForm (cp.A σ v) (cp.xi σ v) := by
    by_contra hc
    push Not at hc
    have : diagD cp.G (aOf d p) cp.yp cp.S v * hN cp.G (aOf d p) 1 cp.yp σ cp.S v *
        (1 - qForm (rootMat cp.G (aOf d p) 1 cp.yp σ cp.S v) (rootSigns cp.G σ cp.S v)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hc
    linarith
  have q2 : 0 < 1 - qForm (cp.B σ v) (cp.xi σ v) := by
    by_contra hc
    push Not at hc
    have : diagD cp.G (aOf d p) cp.ym cp.S v * hN cp.G (aOf d p) (-1) cp.ym σ cp.S v *
        (1 - qForm (rootMat cp.G (aOf d p) (-1) cp.ym σ cp.S v) (rootSigns cp.G σ cp.S v)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hc
    linarith
  have c1 : clipF (cp.A σ v) (cp.xi σ v) = 1 - qForm (cp.A σ v) (cp.xi σ v) :=
    max_eq_left q1.le
  have c2 : clipF (cp.B σ v) (cp.xi σ v) = 1 - qForm (cp.B σ v) (cp.xi σ v) :=
    max_eq_left q2.le
  refine ⟨?_, ?_, c1 ▸ q1, c2 ▸ q2⟩
  · rw [c1]; exact h1
  · rw [c2]; exact h2

/-- `A-C4T-RET`: `E_{ν_K} 𝖱F₀ / F_H = E[tr M - q_M(ξ)]`. -/
theorem c4_ret0 (hR : RegA d p) {v : cp.V} (hv : v ∈ cp.S)
    (M : Config cp.V → Matrix (cp.N v) (cp.N v) ℝ) (hMc : ∀ σ σ', AgreeOff v σ σ' → M σ = M σ') :
    cp.E (fun σ => (M σ).trace - qForm (M σ) (cp.xi σ v)) =
      cp.coreE v (fun σ => radE (cp.c4F0 M σ)) / cp.FH v := by
  rw [cp.coreE_radE_div_eq hR hv (cp.c4F0 M) (fun σ σ' hσ => by
      funext x
      simp only [c4F0, CapPoint.A, CapPoint.B, SecA.rootMat_congr cp.G hσ, hMc σ σ' hσ])
    (fun σ ξ _ hΦ => by simp only [c4F0, hΦ, mul_zero])]
  refine lawE_congr cp.G fun σ hσ => ?_
  have hΦ := cp.starPhi_xi_pos hR hv hσ
  simp only [c4F0]
  rw [mul_div_assoc, div_self hΦ.ne', mul_one]

/-- `Φ = 0` at a sign vector forces `α = 0` or `β = 0`. -/
theorem clipF_eq_zero_of_starPhi {ι : Type*} [Fintype ι] {p : ℕ} {A B : Matrix ι ι ℝ}
    {x : ι → ℝ} (h : starPhi p A B x = 0) : clipF A x = 0 ∨ clipF B x = 0 := by
  rcases mul_eq_zero.1 h with h | h
  · exact Or.inl (pow_eq_zero_iff'.1 h).1
  · exact Or.inr (pow_eq_zero_iff'.1 h).1

/-- `A-C4T-RET`: `E_{ν_K} 𝖱F₁₂ / F_H = E[tr(MA) τ⁺ + tr(MB) τ⁻]`. -/
theorem c4_ret12 (hR : RegA d p) {v : cp.V} (hv : v ∈ cp.S)
    (M : Config cp.V → Matrix (cp.N v) (cp.N v) ℝ) (hMc : ∀ σ σ', AgreeOff v σ σ' → M σ = M σ') :
    cp.coreE v (fun σ => radE (cp.c4F12 M σ)) / cp.FH v =
      cp.E (fun σ => (M σ * cp.A σ v).trace * cp.taup σ v +
        (M σ * cp.B σ v).trace * cp.taum σ v) := by
  have hp2 : 2 ≤ p := hR.treg.two_le_p
  rw [cp.coreE_radE_div_eq hR hv (cp.c4F12 M) (fun σ σ' hσ => by
      funext x
      simp only [c4F12, CapPoint.A, CapPoint.B, SecA.rootMat_congr cp.G hσ, hMc σ σ' hσ])
    (fun σ ξ _ hΦ => by
      rcases clipF_eq_zero_of_starPhi hΦ with h | h <;>
        simp [c4F12, h, zero_pow (show p - 1 ≠ 0 by omega), zero_pow (show p ≠ 0 by omega)])]
  refine lawE_congr cp.G fun σ hσ => ?_
  obtain ⟨ha, hb, hα, hβ⟩ := cp.taup_mul_clipF hv hσ
  set α := clipF (cp.A σ v) (cp.xi σ v)
  set β := clipF (cp.B σ v) (cp.xi σ v)
  have eα : α ^ p = α ^ (p - 1) * α := by rw [← pow_succ, Nat.sub_add_cancel (by omega)]
  have eβ : β ^ p = β ^ (p - 1) * β := by rw [← pow_succ, Nat.sub_add_cancel (by omega)]
  have hα' : 0 < α ^ (p - 1) := pow_pos hα _
  have hβ' : 0 < β ^ (p - 1) := pow_pos hβ _
  simp only [c4F12, starPhi]
  rw [eα, eβ, div_eq_iff (by positivity)]
  linear_combination (-((M σ * cp.A σ v).trace * α ^ (p - 1) * β ^ (p - 1) * β)) * ha +
    (-((M σ * cp.B σ v).trace * α ^ (p - 1) * α * β ^ (p - 1))) * hb

/-- `A-C4T-RET`: `E_{ν_K} 𝖱F₃₄ / F_H = E[q_{AMA}(ξ)(τ⁺)² + q_{BMB}(ξ)(τ⁻)²]`. -/
theorem c4_ret34 (hR : RegA d p) {v : cp.V} (hv : v ∈ cp.S)
    (M : Config cp.V → Matrix (cp.N v) (cp.N v) ℝ) (hMc : ∀ σ σ', AgreeOff v σ σ' → M σ = M σ') :
    cp.coreE v (fun σ => radE (cp.c4F34 M σ)) / cp.FH v =
      cp.E (fun σ => qForm (cp.A σ v * M σ * cp.A σ v) (cp.xi σ v) * cp.taup σ v ^ 2 +
        qForm (cp.B σ v * M σ * cp.B σ v) (cp.xi σ v) * cp.taum σ v ^ 2) := by
  have hp3 : 3 ≤ p := le_trans (by norm_num) hR.treg.hp
  rw [cp.coreE_radE_div_eq hR hv (cp.c4F34 M) (fun σ σ' hσ => by
      funext x
      simp only [c4F34, CapPoint.A, CapPoint.B, SecA.rootMat_congr cp.G hσ, hMc σ σ' hσ])
    (fun σ ξ _ hΦ => by
      rcases clipF_eq_zero_of_starPhi hΦ with h | h <;>
        simp [c4F34, h, zero_pow (show p - 2 ≠ 0 by omega), zero_pow (show p ≠ 0 by omega)])]
  refine lawE_congr cp.G fun σ hσ => ?_
  obtain ⟨ha, hb, hα, hβ⟩ := cp.taup_mul_clipF hv hσ
  set α := clipF (cp.A σ v) (cp.xi σ v)
  set β := clipF (cp.B σ v) (cp.xi σ v)
  have eα : α ^ p = α ^ (p - 2) * α ^ 2 := by rw [← pow_add, Nat.sub_add_cancel (by omega)]
  have eβ : β ^ p = β ^ (p - 2) * β ^ 2 := by rw [← pow_add, Nat.sub_add_cancel (by omega)]
  have hα' : 0 < α ^ (p - 2) := pow_pos hα _
  have hβ' : 0 < β ^ (p - 2) := pow_pos hβ _
  simp only [c4F34, starPhi]
  rw [eα, eβ, div_eq_iff (by positivity)]
  set q1 := qForm (cp.A σ v * M σ * cp.A σ v) (cp.xi σ v)
  set q2 := qForm (cp.B σ v * M σ * cp.B σ v) (cp.xi σ v)
  set ta := cp.taup σ v
  set tb := cp.taum σ v
  linear_combination (-(q1 * α ^ (p - 2) * β ^ (p - 2) * β ^ 2) * (ta * α + 1)) * ha +
    (-(q2 * α ^ (p - 2) * α ^ 2 * β ^ (p - 2)) * (tb * β + 1)) * hb

/-- `A-C4T-CR`: (C4) averaged over the own core law. -/
theorem c4_cr (hR : RegA d p) {v : cp.V} (M : Config cp.V → Matrix (cp.N v) (cp.N v) ℝ)
    (hMpsd : ∀ σ, 0 < wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v →
      (M σ).PosSemidef ∧ (cp.A σ v - M σ).PosSemidef) :
    cp.coreE v (fun σ => gaussE (cp.c4F0 M σ)) ≤
      2 * p * cp.coreE v (fun σ => gaussE (cp.c4F12 M σ)) +
        4 * p * cp.coreE v (fun σ => gaussE (cp.c4F34 M σ)) := by
  have hp3 : 3 ≤ p := le_trans (by norm_num) hR.treg.hp
  rw [← cp.coreE_fconst_mul, ← cp.coreE_fconst_mul, ← cp.coreE_fadd]
  refine SecA.wavg_mono' (fun σ => SecA.wtCore_nonneg cp.G _ _ _ _ σ _ _) fun σ hσ => ?_
  obtain ⟨hA, hB⟩ := cp.root_psd_core hσ.ne'
  exact SecA.gaussE_C4 hA hB (hMpsd σ hσ).1 hp3

end CapPoint

namespace SecA

/-- `A-C4T-T0`: transfer of the left observable `F₀ = (tr M - q_M) Φ` (`trans_left`: `A-TRANS`
with sup/endpoint scale `1 + tr A`; grade one by `grade_one_sum_le`: `A-EPB4`, the row bound,
T.IL on `(σ, i)`). -/
theorem c4_trans0 : ∃ C : ℝ, 0 < C ∧ ∀ d p : ℕ, RegA d p → ∀ cp : CapPoint.{u} d p,
    ∀ ρ : ℝ, 0 ≤ ρ → cp.DefLe ρ → ∀ v ∈ cp.S,
    ∀ M : Config cp.V → Matrix (cp.N v) (cp.N v) ℝ,
      (∀ σ σ', AgreeOff v σ σ' → M σ = M σ') →
      (∀ σ, 0 < wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v →
        (M σ).PosSemidef ∧ (cp.A σ v - M σ).PosSemidef) →
      |cp.coreE v (fun σ => gaussE (cp.c4F0 M σ) - radE (cp.c4F0 M σ)) / cp.FH v| ≤
        C * ((p : ℝ) ^ 4 * (ρ + b0Of d p) / d + (p : ℝ) ^ 2 / d + (p : ℝ) ^ 8 / (d : ℝ) ^ 2 +
          Real.exp (-(p : ℝ)) / d) := by
  obtain ⟨Cr, hCr, hrowb⟩ := row_bound.{u}
  set K₁ := 2 * Real.exp 2 * 3 * (41 ^ 4 / 4) ^ 2 with hK₁
  have hK₁0 : 0 ≤ K₁ := by positivity
  refine ⟨K₁ + 3 + 1440 + 640320 * (Cr + 1), by positivity,
    fun d p hR cp ρ hρ0 hρ v hv M hMc hMpsd => ?_⟩
  have hd := hR.d_pos
  have hb := hR.b0Of_pos
  have hdb := hR.inv_d_le_b0Of
  -- `F₀` as a clipped observable
  have e : (fun σ => gaussE (cp.c4F0 M σ) - radE (cp.c4F0 M σ)) = fun σ =>
      gaussE (clipObs (quadFn (M σ).trace 0 (-(M σ))) p p (cp.A σ v) (cp.B σ v)) -
        radE (clipObs (quadFn (M σ).trace 0 (-(M σ))) p p (cp.A σ v) (cp.B σ v)) := by
    funext σ
    have e1 : cp.c4F0 M σ = clipObs (quadFn (M σ).trace 0 (-(M σ))) p p (cp.A σ v) (cp.B σ v) := by
      funext x
      simp only [CapPoint.c4F0, clipObs, quadFn, starPhi, zero_dotProduct, add_zero,
        SecA.CA.qForm_neg]
      ring
    rw [e1]
  rw [e]
  have h1 := cp.trans_left hR hv M hMc hMpsd
  -- the row bound
  obtain ⟨r1, r2⟩ := hrowb d p hR cp ρ hρ0 hρ v hv
  set X := ρ + b0Of d p with hX
  have hX0 : 0 ≤ X := by positivity
  have hrow : ∑ i : cp.N v, cp.E (fun σ => cp.c4r σ v i) ≤ 2 * (Cr + 1) * X := by
    have e2 : ∀ i : cp.N v, cp.E (fun σ => cp.c4r σ v i) =
        aOf d p ^ 2 * cp.E (fun σ => cp.gp σ v i ^ 2) +
          aOf d p ^ 2 * cp.E (fun σ => cp.gm σ v i ^ 2) := fun i => by
      unfold CapPoint.E CapPoint.c4r
      rw [← lawE_const_mul, ← lawE_const_mul, ← lawE_add]
      exact congrArg _ (funext fun σ => by ring)
    simp only [e2]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      Finset.sum_coe_sort (cp.N v) (fun i => cp.E (fun σ => cp.gp σ v i ^ 2)),
      Finset.sum_coe_sort (cp.N v) (fun i => cp.E (fun σ => cp.gm σ v i ^ 2))]
    have : Cr * X ≤ (Cr + 1) * X := by nlinarith
    linarith
  have hdm : 1 / (d : ℝ) ≤ 2 * (Cr + 1) * X := by nlinarith
  have h2 := cp.grade_one_sum_le hR hv M hMpsd hrow hdm
  -- the triangle inequality
  have htri : |cp.coreE v (fun σ =>
      gaussE (clipObs (quadFn (M σ).trace 0 (-(M σ))) p p (cp.A σ v) (cp.B σ v)) -
        radE (clipObs (quadFn (M σ).trace 0 (-(M σ))) p p (cp.A σ v) (cp.B σ v))) / cp.FH v| ≤
      (2 * Real.exp 2 * 3 * (41 ^ 4 / 4 * ((p : ℝ) ^ 4 / d)) ^ 2 + 3 * Real.exp (-(p : ℝ)) / d) +
        (1440 * (p : ℝ) ^ 2 / d + 320160 * (p : ℝ) ^ 4 * (2 * (Cr + 1) * X) / d) := by
    refine le_trans ?_ (add_le_add h1 h2)
    refine le_trans (le_of_eq ?_) (abs_add_le _ _)
    congr 1
    ring
  refine htri.trans ?_
  set A1 := (p : ℝ) ^ 4 * X / d with hA1
  set A2 := (p : ℝ) ^ 2 / d with hA2
  set A3 := (p : ℝ) ^ 8 / (d : ℝ) ^ 2 with hA3
  set A4 := Real.exp (-(p : ℝ)) / d with hA4
  have hA10 : 0 ≤ A1 := by positivity
  have hA20 : 0 ≤ A2 := by positivity
  have hA30 : 0 ≤ A3 := by positivity
  have hA40 : 0 ≤ A4 := by positivity
  have f1 : 2 * Real.exp 2 * 3 * (41 ^ 4 / 4 * ((p : ℝ) ^ 4 / d)) ^ 2 = K₁ * A3 := by
    rw [hK₁, hA3]; ring
  have f2 : 3 * Real.exp (-(p : ℝ)) / d = 3 * A4 := by rw [hA4]; ring
  have f3 : 1440 * (p : ℝ) ^ 2 / d = 1440 * A2 := by rw [hA2]; ring
  have f4 : 320160 * (p : ℝ) ^ 4 * (2 * (Cr + 1) * X) / d = 640320 * (Cr + 1) * A1 := by
    rw [hA1]; ring
  rw [f1, f2, f3, f4]
  have hC1 : 0 ≤ Cr + 1 := by linarith
  nlinarith [mul_nonneg hK₁0 hA10, mul_nonneg hK₁0 hA20, mul_nonneg hK₁0 hA40,
    mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 640320) hC1) hA20,
    mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 640320) hC1) hA30,
    mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 640320) hC1) hA40]

/-- `A-C4T-T12`: transfer of `F₁₂ = tr(MA) α^{p-1}β^p + tr(MB) α^pβ^{p-1}` (`trans_pair`,
`A-C3b`). -/
theorem c4_trans12 : ∃ C : ℝ, 0 < C ∧ ∀ d p : ℕ, RegA d p → ∀ cp : CapPoint.{u} d p,
    ∀ ρ : ℝ, 0 ≤ ρ → cp.DefLe ρ → ∀ v ∈ cp.S,
    ∀ M : Config cp.V → Matrix (cp.N v) (cp.N v) ℝ,
      (∀ σ σ', AgreeOff v σ σ' → M σ = M σ') →
      (∀ σ, 0 < wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v →
        (M σ).PosSemidef ∧ (cp.A σ v - M σ).PosSemidef) →
      |cp.coreE v (fun σ => gaussE (cp.c4F12 M σ) - radE (cp.c4F12 M σ)) / cp.FH v| ≤
        C * ((p : ℝ) ^ 4 * (ρ + b0Of d p) / d + Real.exp (-(p : ℝ)) / d) := by
  obtain ⟨CΘ, hCΘ, hΘ⟩ := preclosure_C3b.{u}
  set K₀ := 2 * Real.exp 2 * (108 * (CΘ + 1) * (2 * Real.exp 12000) * 90) * (41 ^ 4 / 4)
    with hK₀
  have hK₀0 : 0 ≤ K₀ := by positivity
  refine ⟨K₀ + 9, by positivity, fun d p hR cp ρ hρ0 hρ v hv M hMc hMpsd => ?_⟩
  have hd := hR.d_pos
  have hb := hR.b0Of_pos
  have hdb := hR.inv_d_le_b0Of
  have hEΘ := hΘ d p hR cp ρ hρ0 hρ v hv
  have hEΘ' : cp.E (fun σ => cp.Theta σ v) ≤ (CΘ + 1) * (ρ + b0Of d p) := by nlinarith
  have hdm : 1 / (d : ℝ) ≤ (CΘ + 1) * (ρ + b0Of d p) := by nlinarith
  have h := cp.trans_pair hR hv M hMc hMpsd hEΘ' hdm
  have e : (fun σ => gaussE (cp.c4F12 M σ) - radE (cp.c4F12 M σ)) = fun σ =>
      gaussE (clipObs (quadFn ((M σ * cp.A σ v).trace + (M σ * cp.B σ v).trace) 0
        (-((M σ * cp.A σ v).trace • cp.B σ v + (M σ * cp.B σ v).trace • cp.A σ v)))
        (p - 1) (p - 1) (cp.A σ v) (cp.B σ v)) -
      radE (clipObs (quadFn ((M σ * cp.A σ v).trace + (M σ * cp.B σ v).trace) 0
        (-((M σ * cp.A σ v).trace • cp.B σ v + (M σ * cp.B σ v).trace • cp.A σ v)))
        (p - 1) (p - 1) (cp.A σ v) (cp.B σ v)) := by
    funext σ
    rw [cp.c4F12_eq_clipObs hR.treg.two_le_p M σ]
  rw [e]
  refine h.trans ?_
  set X := (p : ℝ) ^ 4 * (ρ + b0Of d p) / d with hX
  set Y := Real.exp (-(p : ℝ)) / d with hY
  have hX0 : 0 ≤ X := by positivity
  have hY0 : 0 ≤ Y := by positivity
  have e1 : 2 * Real.exp 2 * (108 * ((CΘ + 1) * (ρ + b0Of d p)) * (2 * Real.exp 12000) * 90) *
      (41 ^ 4 / 4 * ((p : ℝ) ^ 4 / d)) = K₀ * X := by
    rw [hK₀, hX]; ring
  have e2 : 9 * Real.exp (-(p : ℝ)) / d = 9 * Y := by rw [hY]; ring
  rw [e1, e2]
  nlinarith [mul_nonneg hK₀0 hY0]

/-- `A-C4T-T34`: transfer of `F₃₄ = q_{AMA} α^{p-2}β^p + q_{BMB} α^pβ^{p-2}` (`trans_domA`,
`trans_domB`, `A-C3b`; the Gaussian and Rademacher averages split on the core support). -/
theorem c4_trans34 : ∃ C : ℝ, 0 < C ∧ ∀ d p : ℕ, RegA d p → ∀ cp : CapPoint.{u} d p,
    ∀ ρ : ℝ, 0 ≤ ρ → cp.DefLe ρ → ∀ v ∈ cp.S,
    ∀ M : Config cp.V → Matrix (cp.N v) (cp.N v) ℝ,
      (∀ σ σ', AgreeOff v σ σ' → M σ = M σ') →
      (∀ σ, 0 < wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v →
        (M σ).PosSemidef ∧ (cp.A σ v - M σ).PosSemidef) →
      |cp.coreE v (fun σ => gaussE (cp.c4F34 M σ) - radE (cp.c4F34 M σ)) / cp.FH v| ≤
        C * ((p : ℝ) ^ 4 * (ρ + b0Of d p) / d + Real.exp (-(p : ℝ)) / d) := by
  obtain ⟨CΘ, hCΘ, hΘ⟩ := preclosure_C3b.{u}
  set K₀ := 2 * Real.exp 2 * (60 * (CΘ + 1) * (2 * Real.exp 12000) * 90) * (41 ^ 4 / 4)
    with hK₀
  have hK₀0 : 0 ≤ K₀ := by positivity
  refine ⟨2 * K₀ + 10, by positivity, fun d p hR cp ρ hρ0 hρ v hv M hMc hMpsd => ?_⟩
  have hd := hR.d_pos
  have hb := hR.b0Of_pos
  have hdb := hR.inv_d_le_b0Of
  have hEΘ := hΘ d p hR cp ρ hρ0 hρ v hv
  have hEΘ' : cp.E (fun σ => cp.Theta σ v) ≤ (CΘ + 1) * (ρ + b0Of d p) := by nlinarith
  have hdm : 1 / (d : ℝ) ≤ (CΘ + 1) * (ρ + b0Of d p) := by nlinarith
  have h3 := cp.trans_domA hR hv M hMc hMpsd hEΘ' hdm
  have h4 := cp.trans_domB hR hv M hMc hMpsd hEΘ' hdm
  have hFH := cp.FH_pos' hR hv
  -- the split on the core support
  have hsplit : ∀ σ, wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v ≠ 0 →
      gaussE (cp.c4F34 M σ) - radE (cp.c4F34 M σ) =
        (gaussE (clipObs (quadFn 0 0 (cp.A σ v * M σ * cp.A σ v)) (p - 2) p
          (cp.A σ v) (cp.B σ v)) -
          radE (clipObs (quadFn 0 0 (cp.A σ v * M σ * cp.A σ v)) (p - 2) p
          (cp.A σ v) (cp.B σ v))) +
        (gaussE (clipObs (quadFn 0 0 (cp.B σ v * M σ * cp.B σ v)) p (p - 2)
          (cp.A σ v) (cp.B σ v)) -
          radE (clipObs (quadFn 0 0 (cp.B σ v * M σ * cp.B σ v)) p (p - 2)
          (cp.A σ v) (cp.B σ v))) := by
    intro σ hσ
    obtain ⟨hA, hB⟩ := cp.root_psd_core hσ
    have e0 : cp.c4F34 M σ = fun x =>
        clipObs (quadFn 0 0 (cp.A σ v * M σ * cp.A σ v)) (p - 2) p (cp.A σ v) (cp.B σ v) x +
        clipObs (quadFn 0 0 (cp.B σ v * M σ * cp.B σ v)) p (p - 2) (cp.A σ v) (cp.B σ v) x := by
      funext x
      simp only [CapPoint.c4F34, clipObs, quadFn, zero_dotProduct, zero_add]
    have hint : ∀ (L : Matrix (cp.N v) (cp.N v) ℝ) (e₁ e₂ : ℕ),
        MeasureTheory.Integrable (clipObs (quadFn 0 0 L) e₁ e₂ (cp.A σ v) (cp.B σ v))
          (gaussPi (cp.N v)) := by
      intro L e₁ e₂
      have hφc : Continuous (fun x => clipF (cp.A σ v) x ^ e₁ * clipF (cp.B σ v) x ^ e₂) :=
        ((continuous_clipF _).pow _).mul ((continuous_clipF _).pow _)
      have hφ : ∀ x, |clipF (cp.A σ v) x ^ e₁ * clipF (cp.B σ v) x ^ e₂| ≤ 1 := fun x => by
        rw [abs_of_nonneg (mul_nonneg (pow_nonneg (clipF_nonneg _ _) _)
          (pow_nonneg (clipF_nonneg _ _) _))]
        exact clipProd_le_one hA hB e₁ e₂ x
      refine (integrable_qForm_mul_gaussPi L hφc hφ).congr
        (Filter.Eventually.of_forall fun x => ?_)
      simp only [clipObs, quadFn, zero_dotProduct, zero_add]
      ring
    rw [e0]
    have hg : gaussE (fun x =>
        clipObs (quadFn 0 0 (cp.A σ v * M σ * cp.A σ v)) (p - 2) p (cp.A σ v) (cp.B σ v) x +
        clipObs (quadFn 0 0 (cp.B σ v * M σ * cp.B σ v)) p (p - 2) (cp.A σ v) (cp.B σ v) x) =
        gaussE (clipObs (quadFn 0 0 (cp.A σ v * M σ * cp.A σ v)) (p - 2) p
          (cp.A σ v) (cp.B σ v)) +
        gaussE (clipObs (quadFn 0 0 (cp.B σ v * M σ * cp.B σ v)) p (p - 2)
          (cp.A σ v) (cp.B σ v)) :=
      MeasureTheory.integral_add (hint _ _ _) (hint _ _ _)
    have hr : radE (fun x =>
        clipObs (quadFn 0 0 (cp.A σ v * M σ * cp.A σ v)) (p - 2) p (cp.A σ v) (cp.B σ v) x +
        clipObs (quadFn 0 0 (cp.B σ v * M σ * cp.B σ v)) p (p - 2) (cp.A σ v) (cp.B σ v) x) =
        radE (clipObs (quadFn 0 0 (cp.A σ v * M σ * cp.A σ v)) (p - 2) p
          (cp.A σ v) (cp.B σ v)) +
        radE (clipObs (quadFn 0 0 (cp.B σ v * M σ * cp.B σ v)) p (p - 2)
          (cp.A σ v) (cp.B σ v)) := by
      rw [radE_eq_sum, radE_eq_sum, radE_eq_sum, Finset.sum_add_distrib, add_div]
    rw [hg, hr]
    ring
  have e : cp.coreE v (fun σ => gaussE (cp.c4F34 M σ) - radE (cp.c4F34 M σ)) =
      cp.coreE v (fun σ =>
        gaussE (clipObs (quadFn 0 0 (cp.A σ v * M σ * cp.A σ v)) (p - 2) p
          (cp.A σ v) (cp.B σ v)) -
          radE (clipObs (quadFn 0 0 (cp.A σ v * M σ * cp.A σ v)) (p - 2) p
          (cp.A σ v) (cp.B σ v))) +
      cp.coreE v (fun σ =>
        gaussE (clipObs (quadFn 0 0 (cp.B σ v * M σ * cp.B σ v)) p (p - 2)
          (cp.A σ v) (cp.B σ v)) -
          radE (clipObs (quadFn 0 0 (cp.B σ v * M σ * cp.B σ v)) p (p - 2)
          (cp.A σ v) (cp.B σ v))) := by
    rw [← cp.coreE_fadd]
    exact SecA.coreE_congr_of_supp cp.G hsplit
  rw [e, add_div]
  refine (abs_add_le _ _).trans ((add_le_add h3 h4).trans ?_)
  set X := (p : ℝ) ^ 4 * (ρ + b0Of d p) / d with hX
  set Y := Real.exp (-(p : ℝ)) / d with hY
  have hX0 : 0 ≤ X := by positivity
  have hY0 : 0 ≤ Y := by positivity
  have e1 : 2 * Real.exp 2 * (60 * ((CΘ + 1) * (ρ + b0Of d p)) * (2 * Real.exp 12000) * 90) *
      (41 ^ 4 / 4 * ((p : ℝ) ^ 4 / d)) = K₀ * X := by
    rw [hK₀, hX]; ring
  have e2 : 5 * Real.exp (-(p : ℝ)) / d = 5 * Y := by rw [hY]; ring
  rw [e1, e2]
  nlinarith [mul_nonneg hK₀0 hY0]

/-- `A-C4T` (proof copy of `SecA.transfer_C4T`): the transfer of (C4) to signs. -/
theorem transfer_C4T_pf : ∃ C : ℝ, 0 < C ∧ ∀ d p : ℕ, RegA d p → ∀ cp : CapPoint.{u} d p,
    ∀ ρ : ℝ, 0 ≤ ρ → cp.DefLe ρ → ∀ v ∈ cp.S,
    ∀ M : Config cp.V → Matrix (cp.N v) (cp.N v) ℝ,
      (∀ σ σ', AgreeOff v σ σ' → M σ = M σ') →
      (∀ σ, 0 < wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v →
        (M σ).PosSemidef ∧ (cp.A σ v - M σ).PosSemidef) →
      cp.E (fun σ => (M σ).trace - qForm (M σ) (cp.xi σ v)) ≤
        2 * p * cp.E (fun σ => (M σ * cp.A σ v).trace * cp.taup σ v +
            (M σ * cp.B σ v).trace * cp.taum σ v) +
          4 * p * cp.E (fun σ => qForm (cp.A σ v * M σ * cp.A σ v) (cp.xi σ v) * cp.taup σ v ^ 2 +
            qForm (cp.B σ v * M σ * cp.B σ v) (cp.xi σ v) * cp.taum σ v ^ 2) +
          C * ((p : ℝ) ^ 5 * (ρ + b0Of d p) / d + (p : ℝ) ^ 2 / d + (p : ℝ) ^ 9 / (d : ℝ) ^ 2 +
            Real.exp (-(p : ℝ)) / d) := by
  obtain ⟨C0, hC0, h0⟩ := c4_trans0.{u}
  obtain ⟨C1, hC1, h1⟩ := c4_trans12.{u}
  obtain ⟨C2, hC2, h2⟩ := c4_trans34.{u}
  refine ⟨C0 + 2 * C1 + 4 * C2, by positivity,
    fun d p hR cp ρ hρ0 hρ v hv M hMc hMpsd => ?_⟩
  have hFH := cp.FH_pos' hR hv
  have hd := hR.d_pos
  have hp1 := hR.one_le_p
  have hb := hR.b0Of_pos
  have e0 := cp.c4_ret0 hR hv M hMc
  have e12 := cp.c4_ret12 hR hv M hMc
  have e34 := cp.c4_ret34 hR hv M hMc
  have hcr := cp.c4_cr hR M hMpsd
  have t0 := h0 d p hR cp ρ hρ0 hρ v hv M hMc hMpsd
  have t1 := h1 d p hR cp ρ hρ0 hρ v hv M hMc hMpsd
  have t2 := h2 d p hR cp ρ hρ0 hρ v hv M hMc hMpsd
  -- the three differences
  have sub : ∀ F : Config cp.V → (cp.N v → ℝ) → ℝ,
      cp.coreE v (fun σ => gaussE (F σ) - radE (F σ)) / cp.FH v =
        cp.coreE v (fun σ => gaussE (F σ)) / cp.FH v -
          cp.coreE v (fun σ => radE (F σ)) / cp.FH v := fun F => by
    rw [← sub_div]
    congr 1
    exact SecA.wavg_sub _ _ _
  rw [sub] at t0 t1 t2
  have hcr' : cp.coreE v (fun σ => gaussE (cp.c4F0 M σ)) / cp.FH v ≤
      2 * p * (cp.coreE v (fun σ => gaussE (cp.c4F12 M σ)) / cp.FH v) +
        4 * p * (cp.coreE v (fun σ => gaussE (cp.c4F34 M σ)) / cp.FH v) := by
    rw [mul_div_assoc', mul_div_assoc', ← add_div]
    exact div_le_div_of_nonneg_right hcr hFH.le
  rw [e0]
  rw [e12] at t1
  rw [e34] at t2
  -- notation
  set X := ρ + b0Of d p with hX
  have hX0 : 0 ≤ X := by positivity
  set Ep := Real.exp (-(p : ℝ)) with hEp
  have hE0 : 0 ≤ Ep := (Real.exp_pos _).le
  have hEd : Ep ≤ 1 / d := hR.exp_neg_p_le
  have hp0 : (0 : ℝ) ≤ p := by linarith
  -- powers
  have a1 : (p : ℝ) ^ 4 * X / d ≤ (p : ℝ) ^ 5 * X / d := by
    refine div_le_div_of_nonneg_right ?_ hd.le
    have : (p : ℝ) ^ 4 ≤ (p : ℝ) ^ 5 := pow_le_pow_right₀ hp1 (by norm_num)
    exact mul_le_mul_of_nonneg_right this hX0
  have a2 : (p : ℝ) ^ 8 / (d : ℝ) ^ 2 ≤ (p : ℝ) ^ 9 / (d : ℝ) ^ 2 := by
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    exact pow_le_pow_right₀ hp1 (by norm_num)
  have a3 : (p : ℝ) * (Ep / d) ≤ (p : ℝ) ^ 9 / (d : ℝ) ^ 2 := by
    have h1 : (p : ℝ) * (Ep / d) ≤ (p : ℝ) * (1 / d / d) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hEd hd.le) hp0
    have h2 : (p : ℝ) * (1 / d / d) = (p : ℝ) / (d : ℝ) ^ 2 := by ring
    have h3 : (p : ℝ) / (d : ℝ) ^ 2 ≤ (p : ℝ) ^ 9 / (d : ℝ) ^ 2 := by
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      calc (p : ℝ) = (p : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (p : ℝ) ^ 9 := pow_le_pow_right₀ hp1 (by norm_num)
    linarith
  have a4 : (p : ℝ) * ((p : ℝ) ^ 4 * X / d) = (p : ℝ) ^ 5 * X / d := by ring
  have hT : 0 ≤ (p : ℝ) ^ 5 * X / d + (p : ℝ) ^ 2 / d + (p : ℝ) ^ 9 / (d : ℝ) ^ 2 + Ep / d := by
    positivity
  -- combine
  obtain ⟨u0, -⟩ := abs_le.1 t0
  obtain ⟨-, u1⟩ := abs_le.1 t1
  obtain ⟨-, u2⟩ := abs_le.1 t2
  have k1 := mul_le_mul_of_nonneg_left u1 (show (0 : ℝ) ≤ 2 * p by positivity)
  have k2 := mul_le_mul_of_nonneg_left u2 (show (0 : ℝ) ≤ 4 * p by positivity)
  have m1 : 2 * (p : ℝ) * (C1 * ((p : ℝ) ^ 4 * X / d + Ep / d)) ≤
      2 * C1 * ((p : ℝ) ^ 5 * X / d + (p : ℝ) ^ 9 / (d : ℝ) ^ 2) := by
    have : 2 * (p : ℝ) * (C1 * ((p : ℝ) ^ 4 * X / d + Ep / d)) =
        2 * C1 * ((p : ℝ) * ((p : ℝ) ^ 4 * X / d) + (p : ℝ) * (Ep / d)) := by ring
    rw [this, a4]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have m2 : 4 * (p : ℝ) * (C2 * ((p : ℝ) ^ 4 * X / d + Ep / d)) ≤
      4 * C2 * ((p : ℝ) ^ 5 * X / d + (p : ℝ) ^ 9 / (d : ℝ) ^ 2) := by
    have : 4 * (p : ℝ) * (C2 * ((p : ℝ) ^ 4 * X / d + Ep / d)) =
        4 * C2 * ((p : ℝ) * ((p : ℝ) ^ 4 * X / d) + (p : ℝ) * (Ep / d)) := by ring
    rw [this, a4]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have m0 : C0 * ((p : ℝ) ^ 4 * X / d + (p : ℝ) ^ 2 / d + (p : ℝ) ^ 8 / (d : ℝ) ^ 2 + Ep / d) ≤
      C0 * ((p : ℝ) ^ 5 * X / d + (p : ℝ) ^ 2 / d + (p : ℝ) ^ 9 / (d : ℝ) ^ 2 + Ep / d) :=
    mul_le_mul_of_nonneg_left (by linarith) hC0.le
  have m3 : 2 * C1 * ((p : ℝ) ^ 5 * X / d + (p : ℝ) ^ 9 / (d : ℝ) ^ 2) ≤
      2 * C1 * ((p : ℝ) ^ 5 * X / d + (p : ℝ) ^ 2 / d + (p : ℝ) ^ 9 / (d : ℝ) ^ 2 + Ep / d) :=
    mul_le_mul_of_nonneg_left (by have : 0 ≤ (p : ℝ) ^ 2 / d := by positivity
                                  have : 0 ≤ Ep / d := by positivity
                                  linarith) (by positivity)
  have m4 : 4 * C2 * ((p : ℝ) ^ 5 * X / d + (p : ℝ) ^ 9 / (d : ℝ) ^ 2) ≤
      4 * C2 * ((p : ℝ) ^ 5 * X / d + (p : ℝ) ^ 2 / d + (p : ℝ) ^ 9 / (d : ℝ) ^ 2 + Ep / d) :=
    mul_le_mul_of_nonneg_left (by have : 0 ≤ (p : ℝ) ^ 2 / d := by positivity
                                  have : 0 ≤ Ep / d := by positivity
                                  linarith) (by positivity)
  nlinarith [hcr', k1, k2, u0, m0, m1, m2, m3, m4]

end SecA

end BiluLinial.Tight
