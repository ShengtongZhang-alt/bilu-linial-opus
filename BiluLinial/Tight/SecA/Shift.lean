/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecA.C4T

/-!
# Shifted resolvents: (C5), the transfer of (C4) and the bias (C6) (nodes `A-C5*`, `A-C4T`,
`A-TT`, `A-C6`)

Source lines 444–599; AUDIT-A §2.12–§2.14. Physical inverses (zero rows at zero sources):
`G = greenP`, `X_z = shiftP` (`(P + zI)⁻¹`), `C = coreGreen` (`(P_{-v})⁻¹`, inherited core),
`C_z = coreShift` (`(P_{-v} + zI)⁻¹`); `M_z = (a²/Z_v) C_z[N,N]` (`rootMzG`, `cp.Mz`).

Deterministic facts at a supported signing (`P ≻ 0`), `z > 0` (`A-C5`):
* `A-C5a`: `0 < h_z ≤ h` (`hzN ≤ hN`: `P̃ + zY ⪰ P̃`).
* `A-C5b`: `C_{z,ii} ≤ X_{z,ii}` (`i ≠ v`, rank-one Schur correction), `C_ii ≤ G_ii` (`i ≠ v`),
  `C_{z,ii} ≤ C_ii`.
* `A-C5c` (C5(iv)): `Σ_{i ∈ N} (X_{z,ii} - C_{z,ii}) ≤ D_v (h_v - h_{z,v})/z`: the full/core
  correction is `a² X_{z,vv} ξᵀ C_z[N,N]² ξ`, `C - C_z ⪰ z C_z²`, compression, the root Schur
  identities `a² ξᵀ(C - C_z)[N,N] ξ = X_{z,vv}⁻¹ - G_vv⁻¹ - z`, and `1/G_vv = Z_v α ≤ Z_v`.
* `A-C5d`: `1/h_{z,v} = D_v (1 - q_{M_z}(ξ)) + z y_v` (root Schur identity of `P̃ + zY`).
* `A-C5e` (C5(vi)): `tr(C_{z,+}[N,N] C_ν[N,N]) ≤ (2/z) Σ_{ν'} tr((C_{ν'} - C_{z,ν'})[N,N])`
  (`tr(XY) ≤ ½ tr(X² + Y²)`, `‖C_z‖ ≤ 1/z`, `tr C_z[N,N]² ≤ z⁻¹ tr (C - C_z)[N,N]`).
* `A-C5f`: `q_{R M_z R}(ξ) τ² ≤ (a² y_v/(D_v z)) a² Σ_{i ∈ N} G_vi²` for `(R, τ) = (A, τ⁺)` or
  `(B, τ⁻)` (by (F1) `(Rξ)_i τ = ∓ a G_vi`, and `‖M_z‖ ≤ a² y_v/(D_v z)`).

Graph-level nodes (constants `∃ C`, uniform; `θ` any bound on the shifted deficits, `dz ≥ 1`):
* `A-C4T`: for core-measurable `0 ⪯ M ⪯ A` (on the core support), `E_H[tr M - q_M(ξ)] ≤
  2p E_H[tr(MA) τ⁺ + tr(MB) τ⁻] + 4p E_H[q_{AMA}(ξ)(τ⁺)² + q_{BMB}(ξ)(τ⁻)²]
  + C {p⁵(ρ + b₀)/d + p²/d + p⁹/d² + e^{-p}/d}` (`A-CR` pointwise in the core, `A-TRANS` on the five
  observables `F₀ … F₄`, `A-PDOM`, `A-EPB4` for `F₀` (gap A7), `A-INTERP`, `A-C3b`, `A-ROW`).
* `A-TT`: `E_H[tr(M_zA) τ⁺ + tr(M_zB) τ⁻] ≤ C (θ + b₀)/(dz)` and
  `E_H[q_{AM_zA}(ξ)(τ⁺)² + q_{BM_zB}(ξ)(τ⁻)²] ≤ C (θ + b₀)/(dz)`
  (`A-C5`, (M1), `A-INTERP`, `A-ROW`).
* Files: the deterministic facts `A-C5*` and the helpers of `A-TT` are in `SecA/ShiftC5.lean`;
  `A-C4T` is proved in `SecA/C4T.lean` (`transfer_C4T_pf`, split into RET, CR, T0, T12, T34;
  `SecA/C4TTrans.lean`, `C4TRight.lean`, `C4TLeft.lean`).
* `A-C6` (C6):
  `E_H[tr M_z - q_{M_z}(ξ)] ≤ C {p(θ + b₀)/(dz) + p⁵(θ + b₀)/d + p²/d + p⁹/d² + e^{-p}}`
  (`A-C4T` with `M = M_z`, `A-TT`).
-/

@[expose] public section

universe u

namespace BiluLinial.Tight

open Matrix

namespace CapPoint

variable {d p : ℕ} (cp : CapPoint.{u} d p)

/-- `A-C5f`: the quadratic transferred terms, pointwise at a supported signing. -/
theorem qForm_Mz_le (hR : RegA d p) {z : ℝ} (hz : 0 < z) {v : cp.V} (hv : v ∈ cp.S)
    {σ : Config cp.V} (hσ : 0 < wt cp.G p (aOf d p) cp.yp cp.ym σ cp.S) :
    qForm (cp.A σ v * cp.Mz z σ v * cp.A σ v) (cp.xi σ v) * cp.taup σ v ^ 2 ≤
        aOf d p ^ 2 * cp.yp v / (diagD cp.G (aOf d p) cp.yp cp.S v * z) *
          (aOf d p ^ 2 * ∑ i ∈ cp.N v, cp.gp σ v i ^ 2) ∧
      qForm (cp.B σ v * cp.Mz z σ v * cp.B σ v) (cp.xi σ v) * cp.taum σ v ^ 2 ≤
        aOf d p ^ 2 * cp.yp v / (diagD cp.G (aOf d p) cp.yp cp.S v * z) *
          (aOf d p ^ 2 * ∑ i ∈ cp.N v, cp.gm σ v i ^ 2) := by
  have hPp : (precN cp.G (aOf d p) 1 cp.yp σ cp.S).PosDef := by
    by_contra hc
    exact hσ.ne' (by simp [wt, hc])
  have hPm : (precN cp.G (aOf d p) (-1) cp.ym σ cp.S).PosDef := by
    by_contra hc
    exact hσ.ne' (by simp [wt, hc])
  have hcp : (precCore cp.G (aOf d p) 1 cp.yp σ cp.S v).PosDef :=
    SecA.precCore_posDef_of_precN cp.G hPp
  have hD : 0 < diagD cp.G (aOf d p) cp.yp cp.S v :=
    lt_of_lt_of_le one_pos (FloorIns.one_le_diagD cp.G _ cp.yp_nonneg _ _)
  have hc0 : 0 ≤ aOf d p ^ 2 * cp.yp v / diagD cp.G (aOf d p) cp.yp cp.S v :=
    div_nonneg (mul_nonneg (sq_nonneg _) (cp.yp_nonneg v)) hD.le
  have hYle := SecA.shiftY_le cp.G hz cp.yp_nonneg hcp
  have key : ∀ w : nbhd cp.G cp.S v → ℝ, qForm (cp.Mz z σ v) w ≤
      aOf d p ^ 2 * cp.yp v / (diagD cp.G (aOf d p) cp.yp cp.S v * z) * (w ⬝ᵥ w) := by
    intro w
    have h := hYle.dotProduct_mulVec_nonneg w
    rw [star_trivial, sub_mulVec, dotProduct_sub, smul_mulVec, one_mulVec, dotProduct_smul,
      smul_eq_mul, sub_nonneg] at h
    have e : qForm (rootMzG cp.G (aOf d p) 1 z cp.yp σ cp.S v) w =
        aOf d p ^ 2 * cp.yp v / diagD cp.G (aOf d p) cp.yp cp.S v *
          (w ⬝ᵥ (shiftY cp.G (aOf d p) 1 z cp.yp σ cp.S v *ᵥ w)) := by
      rw [SecA.rootMzG_eq_smul, qForm, smul_mulVec, dotProduct_smul, smul_eq_mul]
    calc qForm (cp.Mz z σ v) w = qForm (rootMzG cp.G (aOf d p) 1 z cp.yp σ cp.S v) w := rfl
      _ = aOf d p ^ 2 * cp.yp v / diagD cp.G (aOf d p) cp.yp cp.S v *
          (w ⬝ᵥ (shiftY cp.G (aOf d p) 1 z cp.yp σ cp.S v *ᵥ w)) := e
      _ ≤ aOf d p ^ 2 * cp.yp v / diagD cp.G (aOf d p) cp.yp cp.S v * (z⁻¹ * (w ⬝ᵥ w)) :=
          mul_le_mul_of_nonneg_left h hc0
      _ = _ := by ring
  refine ⟨?_, ?_⟩
  · rw [SecA.qForm_conj_mul_sq (R := cp.A σ v)
      (fun i j => SecC.rootMat_apply_comm cp.G _ 1 cp.yp σ cp.S v i j)]
    refine (key _).trans (le_of_eq ?_)
    congr 1
    rw [Finset.mul_sum, ← Finset.sum_coe_sort (cp.N v)]
    simp only [dotProduct]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h : (cp.A σ v *ᵥ cp.xi σ v) j * cp.taup σ v = -(1 * aOf d p) * cp.gp σ v j :=
      SecA.rootMat_mulVec_mul_rootT cp.G (τ := 1) (by norm_num) cp.yp_nonneg hv hPp j
    exact (SecA.sq_of_mul_eq h).trans (by ring)
  · rw [SecA.qForm_conj_mul_sq (R := cp.B σ v)
      (fun i j => SecC.rootMat_apply_comm cp.G _ (-1) cp.ym σ cp.S v i j)]
    refine (key _).trans (le_of_eq ?_)
    congr 1
    rw [Finset.mul_sum, ← Finset.sum_coe_sort (cp.N v)]
    simp only [dotProduct]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h : (cp.B σ v *ᵥ cp.xi σ v) j * cp.taum σ v = -(-1 * aOf d p) * cp.gm σ v j :=
      SecA.rootMat_mulVec_mul_rootT cp.G (τ := -1) (by norm_num) cp.ym_nonneg hv hPm j
    exact (SecA.sq_of_mul_eq h).trans (by ring)

/-- Shifted deficits dominate the unshifted ones. -/
theorem DefZLe.defLe (hR : RegA d p) {z θ : ℝ} (hz : 0 ≤ z) (h : cp.DefZLe z θ) :
    cp.DefLe θ := by
  intro i hi
  obtain ⟨h1, h2⟩ := h i hi
  have hPD : ∀ σ, wt cp.G p (aOf d p) cp.yp cp.ym σ cp.S ≠ 0 →
      (precN cp.G (aOf d p) 1 cp.yp σ cp.S).PosDef ∧
        (precN cp.G (aOf d p) (-1) cp.ym σ cp.S).PosDef := by
    intro σ hσ
    by_contra hc
    unfold wt at hσ
    exact hσ (by simp [hc])
  have e1 : cp.E (fun σ => cp.hzp z σ i) ≤ cp.E (fun σ => cp.hp σ i) :=
    SecA.lawE_le_of_supp cp.G fun σ hσ =>
      SecA.hzN_le_hN cp.G hz cp.yp_nonneg (hPD σ hσ).1 i
  have e2 : cp.E (fun σ => cp.hzm z σ i) ≤ cp.E (fun σ => cp.hm σ i) :=
    SecA.lawE_le_of_supp cp.G fun σ hσ =>
      SecA.hzN_le_hN cp.G hz cp.ym_nonneg (hPD σ hσ).2 i
  exact ⟨by linarith, by linarith⟩

/-- The trace transferred terms, pointwise on the support:
`tr(M_z A) τ⁺ + tr(M_z B) τ⁻ ≤ (16 a⁴/z) (h⁺_v + h⁻_v)(T⁺ + T⁻)` (C5e). -/
theorem tt_trace_pt (hR : RegA d p) {z : ℝ} (hz : 0 < z) {v : cp.V}
    {σ : Config cp.V} (hσ : wt cp.G p (aOf d p) cp.yp cp.ym σ cp.S ≠ 0) :
    (cp.Mz z σ v * cp.A σ v).trace * cp.taup σ v +
        (cp.Mz z σ v * cp.B σ v).trace * cp.taum σ v ≤
      16 * aOf d p ^ 4 / z * ((cp.hp σ v + cp.hm σ v) *
        (SecA.coreDefect cp.G (aOf d p) 1 z cp.yp σ cp.S v +
          SecA.coreDefect cp.G (aOf d p) (-1) z cp.ym σ cp.S v)) := by
  obtain ⟨hPp, hPm⟩ := SecA.precN_posDef_of_wt cp hσ
  have hMp := SecA.precCore_posDef_of_precN cp.G (v := v) hPp
  have hMm := SecA.precCore_posDef_of_precN cp.G (v := v) hPm
  have hDp1 : 1 ≤ diagD cp.G (aOf d p) cp.yp cp.S v :=
    FloorIns.one_le_diagD cp.G _ cp.yp_nonneg cp.S v
  have hDm1 : 1 ≤ diagD cp.G (aOf d p) cp.ym cp.S v :=
    FloorIns.one_le_diagD cp.G _ cp.ym_nonneg cp.S v
  have hs2 := SecA.sOf_le_two hR.treg
  have hyp2 : cp.yp v ≤ 2 := (cp.inCube_yp hR v).2.trans hs2
  have hym2 : cp.ym v ≤ 2 := (cp.inCube_ym hR v).2.trans hs2
  have hyp0 := cp.yp_nonneg v
  have hym0 := cp.ym_nonneg v
  obtain ⟨S1, hS1⟩ : ∃ S1, S1 = ∑ i ∈ nbhd cp.G cp.S v, ∑ j ∈ nbhd cp.G cp.S v,
      coreShift cp.G (aOf d p) 1 z cp.yp σ cp.S v i j *
        coreGreen cp.G (aOf d p) 1 cp.yp σ cp.S v j i := ⟨_, rfl⟩
  obtain ⟨S2, hS2⟩ : ∃ S2, S2 = ∑ i ∈ nbhd cp.G cp.S v, ∑ j ∈ nbhd cp.G cp.S v,
      coreShift cp.G (aOf d p) 1 z cp.yp σ cp.S v i j *
        coreGreen cp.G (aOf d p) (-1) cp.ym σ cp.S v j i := ⟨_, rfl⟩
  obtain ⟨Tp, hTp⟩ : ∃ T, T = SecA.coreDefect cp.G (aOf d p) 1 z cp.yp σ cp.S v := ⟨_, rfl⟩
  obtain ⟨Tm, hTm⟩ : ∃ T, T = SecA.coreDefect cp.G (aOf d p) (-1) z cp.ym σ cp.S v := ⟨_, rfl⟩
  obtain ⟨cP, hcP⟩ : ∃ c, c = aOf d p ^ 2 * cp.yp v / diagD cp.G (aOf d p) cp.yp cp.S v :=
    ⟨_, rfl⟩
  obtain ⟨cM, hcM⟩ : ∃ c, c = aOf d p ^ 2 * cp.ym v / diagD cp.G (aOf d p) cp.ym cp.S v :=
    ⟨_, rfl⟩
  have htrA : (rootMzG cp.G (aOf d p) 1 z cp.yp σ cp.S v *
      rootMat cp.G (aOf d p) 1 cp.yp σ cp.S v).trace = cP * cP * S1 := by
    rw [hS1, Finset.mul_sum, ← Finset.sum_coe_sort (nbhd cp.G cp.S v)]
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_coe_sort (nbhd cp.G cp.S v)]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [rootMzG, rootMat, of_apply, hcP]
    ring
  have htrB : (rootMzG cp.G (aOf d p) 1 z cp.yp σ cp.S v *
      rootMat cp.G (aOf d p) (-1) cp.ym σ cp.S v).trace = cP * cM * S2 := by
    rw [hS2, Finset.mul_sum, ← Finset.sum_coe_sort (nbhd cp.G cp.S v)]
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_coe_sort (nbhd cp.G cp.S v)]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [rootMzG, rootMat, of_apply, hcP, hcM]
    ring
  replace htrA : (cp.Mz z σ v * cp.A σ v).trace = cP * cP * S1 := htrA
  replace htrB : (cp.Mz z σ v * cp.B σ v).trace = cP * cM * S2 := htrB
  have hhp : 0 < cp.hp σ v := hPp.inv.diag_pos
  have hhm : 0 < cp.hm σ v := hPm.inv.diag_pos
  have hS1le : S1 ≤ 2 / z * (Tp + Tp) := by
    rw [hS1, hTp]
    exact SecA.sum_coreShift_mul_coreGreen_le cp.G hz cp.yp_nonneg cp.yp_nonneg hMp hMp
  have hS2le : S2 ≤ 2 / z * (Tp + Tm) := by
    rw [hS2, hTp, hTm]
    exact SecA.sum_coreShift_mul_coreGreen_le cp.G hz cp.yp_nonneg cp.ym_nonneg hMp hMm
  have hTp0 : 0 ≤ Tp := hTp ▸ SecA.coreDefect_nonneg cp.G hz.le cp.yp_nonneg hMp
  have hTm0 : 0 ≤ Tm := hTm ▸ SecA.coreDefect_nonneg cp.G hz.le cp.ym_nonneg hMm
  -- the coefficients
  have ha2 : 0 ≤ aOf d p ^ 2 := sq_nonneg _
  have hcP0 : 0 ≤ cP := hcP ▸ div_nonneg (mul_nonneg ha2 hyp0) (by linarith)
  have hcP2 : cP ≤ 2 * aOf d p ^ 2 := by
    rw [hcP]
    refine (div_le_self (mul_nonneg ha2 hyp0) hDp1).trans ?_
    nlinarith
  have hAp : aOf d p ^ 2 * cp.yp v ≤ 2 * aOf d p ^ 2 := by nlinarith
  have hAm : aOf d p ^ 2 * cp.ym v ≤ 2 * aOf d p ^ 2 := by nlinarith
  have e : (cp.Mz z σ v * cp.A σ v).trace * cp.taup σ v +
      (cp.Mz z σ v * cp.B σ v).trace * cp.taum σ v =
      (aOf d p ^ 2 * cp.yp v * cP * cp.hp σ v) * S1 +
        (cP * (aOf d p ^ 2 * cp.ym v) * cp.hm σ v) * S2 := by
    rw [htrA, htrB]
    simp only [CapPoint.taup, CapPoint.taum]
    have hD0 : diagD cp.G (aOf d p) cp.ym cp.S v ≠ 0 := by linarith
    have hD0' : diagD cp.G (aOf d p) cp.yp cp.S v ≠ 0 := by linarith
    have hcPD : cP * diagD cp.G (aOf d p) cp.yp cp.S v = aOf d p ^ 2 * cp.yp v := by
      rw [hcP, div_mul_cancel₀ _ hD0']
    have hcMD : cM * diagD cp.G (aOf d p) cp.ym cp.S v = aOf d p ^ 2 * cp.ym v := by
      rw [hcM, div_mul_cancel₀ _ hD0]
    linear_combination (cP * S1 * cp.hp σ v) * hcPD + (cP * S2 * cp.hm σ v) * hcMD
  have hk1 : aOf d p ^ 2 * cp.yp v * cP * cp.hp σ v ≤ 4 * aOf d p ^ 4 * cp.hp σ v := by
    have h1 : aOf d p ^ 2 * cp.yp v * cP ≤ (2 * aOf d p ^ 2) * (2 * aOf d p ^ 2) :=
      mul_le_mul hAp hcP2 hcP0 (by positivity)
    nlinarith
  have hk2 : cP * (aOf d p ^ 2 * cp.ym v) * cp.hm σ v ≤ 4 * aOf d p ^ 4 * cp.hm σ v := by
    have h1 : cP * (aOf d p ^ 2 * cp.ym v) ≤ (2 * aOf d p ^ 2) * (2 * aOf d p ^ 2) :=
      mul_le_mul hcP2 hAm (mul_nonneg ha2 hym0) (by positivity)
    nlinarith
  have hk10 : 0 ≤ aOf d p ^ 2 * cp.yp v * cP * cp.hp σ v := by positivity
  have hk20 : 0 ≤ cP * (aOf d p ^ 2 * cp.ym v) * cp.hm σ v := by positivity
  have hz2 : 0 ≤ 2 / z := by positivity
  rw [e, ← hTp, ← hTm]
  calc (aOf d p ^ 2 * cp.yp v * cP * cp.hp σ v) * S1 +
        (cP * (aOf d p ^ 2 * cp.ym v) * cp.hm σ v) * S2
      ≤ (aOf d p ^ 2 * cp.yp v * cP * cp.hp σ v) * (2 / z * (Tp + Tp)) +
          (cP * (aOf d p ^ 2 * cp.ym v) * cp.hm σ v) * (2 / z * (Tp + Tm)) :=
        add_le_add (mul_le_mul_of_nonneg_left hS1le hk10) (mul_le_mul_of_nonneg_left hS2le hk20)
    _ ≤ (4 * aOf d p ^ 4 * cp.hp σ v) * (2 / z * (Tp + Tp)) +
          (4 * aOf d p ^ 4 * cp.hm σ v) * (2 / z * (Tp + Tm)) :=
        add_le_add (mul_le_mul_of_nonneg_right hk1 (by positivity))
          (mul_le_mul_of_nonneg_right hk2 (by positivity))
    _ ≤ 16 * aOf d p ^ 4 / z * ((cp.hp σ v + cp.hm σ v) * (Tp + Tm)) := by
        have key : 16 * aOf d p ^ 4 / z * ((cp.hp σ v + cp.hm σ v) * (Tp + Tm)) -
            ((4 * aOf d p ^ 4 * cp.hp σ v) * (2 / z * (Tp + Tp)) +
              (4 * aOf d p ^ 4 * cp.hm σ v) * (2 / z * (Tp + Tm))) =
            8 * (aOf d p ^ 4 / z * (2 * cp.hp σ v * Tm + cp.hm σ v * (Tp + Tm))) := by ring
        have : 0 ≤ aOf d p ^ 4 / z * (2 * cp.hp σ v * Tm + cp.hm σ v * (Tp + Tm)) := by
          positivity
        linarith

/-- The quadratic transferred terms, pointwise on the support (C5f). -/
theorem tt_quad_pt (hR : RegA d p) {z : ℝ} (hz : 0 < z) {v : cp.V} (hv : v ∈ cp.S)
    {σ : Config cp.V} (hσ : wt cp.G p (aOf d p) cp.yp cp.ym σ cp.S ≠ 0) :
    qForm (cp.A σ v * cp.Mz z σ v * cp.A σ v) (cp.xi σ v) * cp.taup σ v ^ 2 +
        qForm (cp.B σ v * cp.Mz z σ v * cp.B σ v) (cp.xi σ v) * cp.taum σ v ^ 2 ≤
      1 / (d * z) * (aOf d p ^ 2 * ∑ i ∈ cp.N v, cp.gp σ v i ^ 2 +
        aOf d p ^ 2 * ∑ i ∈ cp.N v, cp.gm σ v i ^ 2) := by
  obtain ⟨q1, q2⟩ := cp.qForm_Mz_le hR hz hv ((wt_nonneg cp.G σ).lt_of_ne' hσ)
  have hd := hR.d_pos
  have hD1 : 1 ≤ diagD cp.G (aOf d p) cp.yp cp.S v :=
    FloorIns.one_le_diagD cp.G _ cp.yp_nonneg cp.S v
  have hyp2 : cp.yp v ≤ 2 := (cp.inCube_yp hR v).2.trans (SecA.sOf_le_two hR.treg)
  have hyp0 := cp.yp_nonneg v
  have ha := SecA.aOf_sq_le_half hR
  have ha2 : 0 ≤ aOf d p ^ 2 := sq_nonneg _
  have hc : aOf d p ^ 2 * cp.yp v / (diagD cp.G (aOf d p) cp.yp cp.S v * z) ≤ 1 / (d * z) := by
    have h1 : aOf d p ^ 2 * cp.yp v / (diagD cp.G (aOf d p) cp.yp cp.S v * z) ≤
        2 * aOf d p ^ 2 / z :=
      div_le_div₀ (by positivity) (by nlinarith) hz (by nlinarith)
    have h2 : 2 * aOf d p ^ 2 / z ≤ 1 / d / z := by
      refine div_le_div_of_nonneg_right ?_ hz.le
      have : 2 * (1 / (2 * (d : ℝ))) = 1 / d := by field_simp
      linarith
    rw [div_div] at h2
    exact h1.trans h2
  have h1 : 0 ≤ aOf d p ^ 2 * ∑ i ∈ cp.N v, cp.gp σ v i ^ 2 :=
    mul_nonneg ha2 (Finset.sum_nonneg fun i _ => sq_nonneg _)
  have h2 : 0 ≤ aOf d p ^ 2 * ∑ i ∈ cp.N v, cp.gm σ v i ^ 2 :=
    mul_nonneg ha2 (Finset.sum_nonneg fun i _ => sq_nonneg _)
  nlinarith [mul_le_mul_of_nonneg_right hc h1, mul_le_mul_of_nonneg_right hc h2]

/-- `E T ≤ 4 d (ε + θ)` for either branch (C5b, C5c, the cap and the shifted deficits). -/
theorem lawE_coreDefect_le (hR : RegA d p) {τ : ℝ} (hτ : τ ^ 2 = 1) {y : cp.V → ℝ}
    (hy : InCube (sOf d p) y)
    (hPD : ∀ σ, wt cp.G p (aOf d p) cp.yp cp.ym σ cp.S ≠ 0 →
      (precN cp.G (aOf d p) τ y σ cp.S).PosDef)
    (hcap : ∀ i ∈ cp.S, cp.E (fun σ => hN cp.G (aOf d p) τ y σ cp.S i) ≤ 1 + epsP d p)
    {z θ : ℝ} (hz : 0 < z) (hdz : 1 ≤ (d : ℝ) * z) (hθ : 0 ≤ θ)
    (hdef : ∀ i ∈ cp.S, 1 - cp.E (fun σ => hzN cp.G (aOf d p) τ z y σ cp.S i) ≤ θ)
    {v : cp.V} (hv : v ∈ cp.S) :
    cp.E (fun σ => SecA.coreDefect cp.G (aOf d p) τ z y σ cp.S v) ≤
      4 * d * (epsP d p + θ) := by
  have hy0 : ∀ i, 0 ≤ y i := fun i => (hy i).1
  have hε := SecA.epsP_nonneg hR.treg
  have hd := hR.d_pos
  have hs2 := SecA.sOf_le_two hR.treg
  have h1 : cp.E (fun σ => SecA.coreDefect cp.G (aOf d p) τ z y σ cp.S v) ≤
      cp.E (fun σ => ∑ i ∈ nbhd cp.G cp.S v, y i * (hN cp.G (aOf d p) τ y σ cp.S i -
          hzN cp.G (aOf d p) τ z y σ cp.S i) +
        diagD cp.G (aOf d p) y cp.S v / z * (hN cp.G (aOf d p) τ y σ cp.S v -
          hzN cp.G (aOf d p) τ z y σ cp.S v)) :=
    SecA.lawE_le_of_supp cp.G fun σ hσ => SecA.coreDefect_le cp.G hτ hz hy0 hv (hPD σ hσ)
  have h2 : cp.E (fun σ => ∑ i ∈ nbhd cp.G cp.S v, y i * (hN cp.G (aOf d p) τ y σ cp.S i -
          hzN cp.G (aOf d p) τ z y σ cp.S i) +
        diagD cp.G (aOf d p) y cp.S v / z * (hN cp.G (aOf d p) τ y σ cp.S v -
          hzN cp.G (aOf d p) τ z y σ cp.S v)) =
      ∑ i ∈ nbhd cp.G cp.S v, y i * (cp.E (fun σ => hN cp.G (aOf d p) τ y σ cp.S i) -
          cp.E (fun σ => hzN cp.G (aOf d p) τ z y σ cp.S i)) +
        diagD cp.G (aOf d p) y cp.S v / z * (cp.E (fun σ => hN cp.G (aOf d p) τ y σ cp.S v) -
          cp.E (fun σ => hzN cp.G (aOf d p) τ z y σ cp.S v)) := by
    unfold CapPoint.E
    simp only [lawE_add, lawE_sum, lawE_const_mul, lawE_sub]
  have hbd : ∀ i ∈ cp.S, cp.E (fun σ => hN cp.G (aOf d p) τ y σ cp.S i) -
      cp.E (fun σ => hzN cp.G (aOf d p) τ z y σ cp.S i) ≤ epsP d p + θ := fun i hi => by
    have := hcap i hi
    have := hdef i hi
    linarith
  have h3 : ∑ i ∈ nbhd cp.G cp.S v, y i * (cp.E (fun σ => hN cp.G (aOf d p) τ y σ cp.S i) -
      cp.E (fun σ => hzN cp.G (aOf d p) τ z y σ cp.S i)) ≤ 2 * d * (epsP d p + θ) := by
    calc _ ≤ ∑ _i ∈ nbhd cp.G cp.S v, 2 * (epsP d p + θ) := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hiS := ((FloorIns.mem_nbhd cp.G).1 hi).1
          have hb := hbd i hiS
          have hyi : y i ≤ 2 := (hy i).2.trans hs2
          calc y i * _ ≤ y i * (epsP d p + θ) := mul_le_mul_of_nonneg_left hb (hy0 i)
            _ ≤ 2 * (epsP d p + θ) := mul_le_mul_of_nonneg_right hyi (by linarith)
      _ = (nbhd cp.G cp.S v).card * (2 * (epsP d p + θ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ d * (2 * (epsP d p + θ)) := by
          refine mul_le_mul_of_nonneg_right ?_ (by linarith)
          exact_mod_cast (FloorIns.card_nbhd_le cp.G cp.S v).trans (cp.ctx.deg v)
      _ = 2 * d * (epsP d p + θ) := by ring
  have h4 : diagD cp.G (aOf d p) y cp.S v / z * (cp.E (fun σ => hN cp.G (aOf d p) τ y σ cp.S v) -
      cp.E (fun σ => hzN cp.G (aOf d p) τ z y σ cp.S v)) ≤ 2 * d * (epsP d p + θ) := by
    have hD2 := SecA.diagD_le_two cp.G hR.treg cp.ctx.deg hy cp.S v
    have hD1 : 1 ≤ diagD cp.G (aOf d p) y cp.S v := FloorIns.one_le_diagD cp.G _ hy0 cp.S v
    have hDz : diagD cp.G (aOf d p) y cp.S v / z ≤ 2 * d := by
      rw [div_le_iff₀ hz]
      nlinarith
    have hDz0 : 0 ≤ diagD cp.G (aOf d p) y cp.S v / z := by positivity
    calc _ ≤ diagD cp.G (aOf d p) y cp.S v / z * (epsP d p + θ) :=
          mul_le_mul_of_nonneg_left (hbd v hv) hDz0
      _ ≤ 2 * d * (epsP d p + θ) := mul_le_mul_of_nonneg_right hDz (by linarith)
  rw [h2] at h1
  linarith

/-- On the support: `T^± ≥ 0` and `T⁺ + T⁻ ≤ 2 Σ_{i ∈ N} (h⁺_i + h⁻_i)`. -/
theorem defect_pt (hR : RegA d p) {z : ℝ} (hz : 0 < z) {v : cp.V} (hv : v ∈ cp.S)
    {σ : Config cp.V} (hσ : wt cp.G p (aOf d p) cp.yp cp.ym σ cp.S ≠ 0) :
    0 ≤ SecA.coreDefect cp.G (aOf d p) 1 z cp.yp σ cp.S v ∧
      0 ≤ SecA.coreDefect cp.G (aOf d p) (-1) z cp.ym σ cp.S v ∧
      SecA.coreDefect cp.G (aOf d p) 1 z cp.yp σ cp.S v +
          SecA.coreDefect cp.G (aOf d p) (-1) z cp.ym σ cp.S v ≤
        2 * ∑ i ∈ nbhd cp.G cp.S v, (cp.hp σ i + cp.hm σ i) := by
  obtain ⟨hPp, hPm⟩ := SecA.precN_posDef_of_wt cp hσ
  have hs2 := SecA.sOf_le_two hR.treg
  refine ⟨SecA.coreDefect_nonneg cp.G hz.le cp.yp_nonneg
      (SecA.precCore_posDef_of_precN cp.G (v := v) hPp),
    SecA.coreDefect_nonneg cp.G hz.le cp.ym_nonneg
      (SecA.precCore_posDef_of_precN cp.G (v := v) hPm), ?_⟩
  have h1 := SecA.coreDefect_le_sum cp.G hz.le cp.yp_nonneg hv hPp
  have h2 := SecA.coreDefect_le_sum cp.G hz.le cp.ym_nonneg hv hPm
  have h3 : ∑ i ∈ nbhd cp.G cp.S v, cp.yp i * hN cp.G (aOf d p) 1 cp.yp σ cp.S i +
      ∑ i ∈ nbhd cp.G cp.S v, cp.ym i * hN cp.G (aOf d p) (-1) cp.ym σ cp.S i ≤
        2 * ∑ i ∈ nbhd cp.G cp.S v, (cp.hp σ i + cp.hm σ i) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have hyp := (cp.inCube_yp hR i).2.trans hs2
    have hym := (cp.inCube_ym hR i).2.trans hs2
    have hhp : 0 < cp.hp σ i := hPp.inv.diag_pos
    have hhm : 0 < cp.hm σ i := hPm.inv.diag_pos
    have e1 : hN cp.G (aOf d p) 1 cp.yp σ cp.S i = cp.hp σ i := rfl
    have e2 : hN cp.G (aOf d p) (-1) cp.ym σ cp.S i = cp.hm σ i := rfl
    rw [e1, e2]
    nlinarith [mul_le_mul_of_nonneg_right hyp hhp.le, mul_le_mul_of_nonneg_right hym hhm.le]
  linarith

/-- `E W ≤ 8(θ + b₀)`, `W = (T⁺ + T⁻)/d`. -/
theorem lawE_W_le (hR : RegA d p) {z : ℝ} (hz : 0 < z) (hdz : 1 ≤ (d : ℝ) * z) {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ : cp.DefZLe z θ) {v : cp.V} (hv : v ∈ cp.S) :
    cp.E (fun σ => (SecA.coreDefect cp.G (aOf d p) 1 z cp.yp σ cp.S v +
      SecA.coreDefect cp.G (aOf d p) (-1) z cp.ym σ cp.S v) / d) ≤ 8 * (θ + b0Of d p) := by
  have hd := hR.d_pos
  have heb := SecA.epsP_le_b0Of hR
  have hT1 := cp.lawE_coreDefect_le hR (τ := 1) (by norm_num) (cp.inCube_yp hR)
    (fun σ hσ => (SecA.precN_posDef_of_wt cp hσ).1)
    (fun i hi => by have := (cp.h_mean_le hi).1; rwa [SecA.rOf_eq] at this) hz hdz hθ0
    (fun i hi => (hθ i hi).1) hv
  have hT2 := cp.lawE_coreDefect_le hR (τ := -1) (by norm_num) (cp.inCube_ym hR)
    (fun σ hσ => (SecA.precN_posDef_of_wt cp hσ).2)
    (fun i hi => by have := (cp.h_mean_le hi).2; rwa [SecA.rOf_eq] at this) hz hdz hθ0
    (fun i hi => (hθ i hi).2) hv
  have hf : (fun σ => (SecA.coreDefect cp.G (aOf d p) 1 z cp.yp σ cp.S v +
      SecA.coreDefect cp.G (aOf d p) (-1) z cp.ym σ cp.S v) / (d : ℝ)) =
      fun σ => 1 / (d : ℝ) * (SecA.coreDefect cp.G (aOf d p) 1 z cp.yp σ cp.S v +
        SecA.coreDefect cp.G (aOf d p) (-1) z cp.ym σ cp.S v) :=
    funext fun σ => by ring
  have e1 : cp.E (fun σ => (SecA.coreDefect cp.G (aOf d p) 1 z cp.yp σ cp.S v +
      SecA.coreDefect cp.G (aOf d p) (-1) z cp.ym σ cp.S v) / d) =
      1 / d * (cp.E (fun σ => SecA.coreDefect cp.G (aOf d p) 1 z cp.yp σ cp.S v) +
        cp.E (fun σ => SecA.coreDefect cp.G (aOf d p) (-1) z cp.ym σ cp.S v)) := by
    unfold CapPoint.E
    rw [hf, lawE_const_mul, lawE_add]
  rw [e1]
  have e2 : 1 / (d : ℝ) * (4 * d * (epsP d p + θ) + 4 * d * (epsP d p + θ)) =
      8 * (epsP d p + θ) := by field_simp; ring
  have h0 : 0 ≤ 1 / (d : ℝ) := by positivity
  have := mul_le_mul_of_nonneg_left (add_le_add hT1 hT2) h0
  linarith

/-- `E W² ≤ (4(1 + 2ε))²`. -/
theorem lawE_W_sq_le (hR : RegA d p) {z : ℝ} (hz : 0 < z) {v : cp.V} (hv : v ∈ cp.S) :
    cp.E (fun σ => ((SecA.coreDefect cp.G (aOf d p) 1 z cp.yp σ cp.S v +
      SecA.coreDefect cp.G (aOf d p) (-1) z cp.ym σ cp.S v) / d) ^ 2) ≤
        (4 * (1 + 2 * epsP d p)) ^ 2 := by
  have hd := hR.d_pos
  have hε0 := SecA.epsP_nonneg hR.treg
  have hp4 : 2 * 2 ≤ p := le_trans (by norm_num) hR.treg.hp
  have hNd : ((nbhd cp.G cp.S v).card : ℝ) ≤ d := by
    exact_mod_cast (FloorIns.card_nbhd_le cp.G cp.S v).trans (cp.ctx.deg v)
  have hcard0 : (0 : ℝ) ≤ (nbhd cp.G cp.S v).card := Nat.cast_nonneg _
  have hpt : ∀ σ, wt cp.G p (aOf d p) cp.yp cp.ym σ cp.S ≠ 0 →
      ((SecA.coreDefect cp.G (aOf d p) 1 z cp.yp σ cp.S v +
        SecA.coreDefect cp.G (aOf d p) (-1) z cp.ym σ cp.S v) / d) ^ 2 ≤
      8 * (nbhd cp.G cp.S v).card / (d : ℝ) ^ 2 *
        ∑ i ∈ nbhd cp.G cp.S v, (cp.hp σ i ^ 2 + cp.hm σ i ^ 2) := fun σ hσ => by
    obtain ⟨a1, a2, hs⟩ := cp.defect_pt hR hz hv hσ
    have hcs : (∑ i ∈ nbhd cp.G cp.S v, (cp.hp σ i + cp.hm σ i)) ^ 2 ≤
        (nbhd cp.G cp.S v).card * ∑ i ∈ nbhd cp.G cp.S v, (cp.hp σ i + cp.hm σ i) ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    have hsq : ∑ i ∈ nbhd cp.G cp.S v, (cp.hp σ i + cp.hm σ i) ^ 2 ≤
        ∑ i ∈ nbhd cp.G cp.S v, 2 * (cp.hp σ i ^ 2 + cp.hm σ i ^ 2) :=
      Finset.sum_le_sum fun i _ => by nlinarith [sq_nonneg (cp.hp σ i - cp.hm σ i)]
    rw [← Finset.mul_sum] at hsq
    have hW : (SecA.coreDefect cp.G (aOf d p) 1 z cp.yp σ cp.S v +
        SecA.coreDefect cp.G (aOf d p) (-1) z cp.ym σ cp.S v) ^ 2 ≤
        (2 * ∑ i ∈ nbhd cp.G cp.S v, (cp.hp σ i + cp.hm σ i)) ^ 2 :=
      pow_le_pow_left₀ (add_nonneg a1 a2) hs 2
    rw [div_pow, div_le_iff₀ (by positivity)]
    have e2 : (8 * ((nbhd cp.G cp.S v).card : ℝ) / (d : ℝ) ^ 2 *
        ∑ i ∈ nbhd cp.G cp.S v, (cp.hp σ i ^ 2 + cp.hm σ i ^ 2)) * (d : ℝ) ^ 2 =
        4 * (((nbhd cp.G cp.S v).card : ℝ) *
          (2 * ∑ i ∈ nbhd cp.G cp.S v, (cp.hp σ i ^ 2 + cp.hm σ i ^ 2))) := by
      rw [div_mul_eq_mul_div, div_mul_cancel₀ _ (by positivity)]
      ring
    rw [e2]
    have := mul_le_mul_of_nonneg_left hsq hcard0
    nlinarith
  have h1 := SecA.lawE_le_of_supp cp.G hpt
  have h2 : lawE cp.G p (aOf d p) cp.yp cp.ym cp.S (fun σ =>
      8 * (nbhd cp.G cp.S v).card / (d : ℝ) ^ 2 *
        ∑ i ∈ nbhd cp.G cp.S v, (cp.hp σ i ^ 2 + cp.hm σ i ^ 2)) =
      8 * (nbhd cp.G cp.S v).card / (d : ℝ) ^ 2 *
        ∑ i ∈ nbhd cp.G cp.S v, (cp.E (fun σ => cp.hp σ i ^ 2) +
          cp.E (fun σ => cp.hm σ i ^ 2)) := by
    unfold CapPoint.E
    simp only [lawE_const_mul, lawE_sum, lawE_add]
  have h3 : ∑ i ∈ nbhd cp.G cp.S v, (cp.E (fun σ => cp.hp σ i ^ 2) +
      cp.E (fun σ => cp.hm σ i ^ 2)) ≤
        (nbhd cp.G cp.S v).card * (2 * (1 + 2 * epsP d p) ^ 2) := by
    calc _ ≤ ∑ _i ∈ nbhd cp.G cp.S v, 2 * (1 + 2 * epsP d p) ^ 2 := by
          refine Finset.sum_le_sum fun i hi => ?_
          obtain ⟨m1, m2⟩ := cp.h_moment hR ((FloorIns.mem_nbhd cp.G).1 hi).1 one_le_two hp4
          linarith
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have h4 : 8 * ((nbhd cp.G cp.S v).card : ℝ) / (d : ℝ) ^ 2 *
      (((nbhd cp.G cp.S v).card : ℝ) * (2 * (1 + 2 * epsP d p) ^ 2)) ≤
        (4 * (1 + 2 * epsP d p)) ^ 2 := by
    have hNd2 : ((nbhd cp.G cp.S v).card : ℝ) ^ 2 ≤ (d : ℝ) ^ 2 :=
      pow_le_pow_left₀ hcard0 hNd 2
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left hNd2
      (show (0 : ℝ) ≤ 16 * (1 + 2 * epsP d p) ^ 2 by positivity)
    nlinarith
  have h0 : 0 ≤ 8 * ((nbhd cp.G cp.S v).card : ℝ) / (d : ℝ) ^ 2 := by positivity
  calc _ ≤ _ := h1
    _ = _ := h2
    _ ≤ _ := mul_le_mul_of_nonneg_left h3 h0
    _ ≤ _ := h4

/-- `E (h⁺_v + h⁻_v)^{2k} ≤ (2(1 + 2ε))^{2k}` for `4k ≤ p`. -/
theorem lawE_hsum_pow_le (hR : RegA d p) {v : cp.V} (hv : v ∈ cp.S) {k : ℕ} (hk1 : 1 ≤ k)
    (hk4 : 2 * (2 * k) ≤ p) :
    cp.E (fun σ => (cp.hp σ v + cp.hm σ v) ^ (2 * k)) ≤ (2 * (1 + 2 * epsP d p)) ^ (2 * k) := by
  have hk2 : 1 ≤ 2 * k := by omega
  have hpt : ∀ σ, wt cp.G p (aOf d p) cp.yp cp.ym σ cp.S ≠ 0 →
      (cp.hp σ v + cp.hm σ v) ^ (2 * k) ≤
        2 ^ (2 * k - 1) * (cp.hp σ v ^ (2 * k) + cp.hm σ v ^ (2 * k)) := fun σ hσ => by
    obtain ⟨hPp, hPm⟩ := SecA.precN_posDef_of_wt cp hσ
    exact add_pow_le (hPp.inv.diag_pos).le (hPm.inv.diag_pos).le _
  have h1 := SecA.lawE_le_of_supp cp.G hpt
  rw [lawE_const_mul, lawE_add] at h1
  obtain ⟨m1, m2⟩ := cp.h_moment hR hv hk2 hk4
  unfold CapPoint.E at m1 m2 ⊢
  have h2 : (2 : ℝ) ^ (2 * k - 1) * ((1 + 2 * epsP d p) ^ (2 * k) +
      (1 + 2 * epsP d p) ^ (2 * k)) = (2 * (1 + 2 * epsP d p)) ^ (2 * k) := by
    rw [mul_pow, ← two_mul, ← mul_assoc, ← pow_succ, Nat.sub_add_cancel hk2]
  have h0 : (0 : ℝ) ≤ 2 ^ (2 * k - 1) := by positivity
  have := mul_le_mul_of_nonneg_left (add_le_add m1 m2) h0
  linarith

/-- `E[(h⁺_v + h⁻_v)(T⁺ + T⁻)] ≤ 180 d (θ + b₀)` (T.IL with `E W ≤ 8(θ + b₀)`, `E W² ≤ 16(1+2ε)²`,
`W = (T⁺ + T⁻)/d`, `k = ⌈log d⌉`). -/
theorem lawE_hW_le (hR : RegA d p) {z : ℝ} (hz : 0 < z) (hdz : 1 ≤ (d : ℝ) * z) {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ : cp.DefZLe z θ) {v : cp.V} (hv : v ∈ cp.S) :
    cp.E (fun σ => (cp.hp σ v + cp.hm σ v) *
      (SecA.coreDefect cp.G (aOf d p) 1 z cp.yp σ cp.S v +
        SecA.coreDefect cp.G (aOf d p) (-1) z cp.ym σ cp.S v)) ≤ 180 * d * (θ + b0Of d p) := by
  have hd := hR.d_pos
  have hε0 := SecA.epsP_nonneg hR.treg
  have hε1 := SecA.epsP_le hR.treg
  have hb := hR.b0Of_pos
  have hdb := hR.inv_d_le_b0Of
  have e : cp.E (fun σ => (cp.hp σ v + cp.hm σ v) *
      (SecA.coreDefect cp.G (aOf d p) 1 z cp.yp σ cp.S v +
        SecA.coreDefect cp.G (aOf d p) (-1) z cp.ym σ cp.S v)) =
      d * cp.E (fun σ => (SecA.coreDefect cp.G (aOf d p) 1 z cp.yp σ cp.S v +
        SecA.coreDefect cp.G (aOf d p) (-1) z cp.ym σ cp.S v) / d *
          (cp.hp σ v + cp.hm σ v)) := by
    unfold CapPoint.E
    rw [← lawE_const_mul]
    congr 1
    funext σ
    rw [div_mul_eq_mul_div, mul_div_assoc', mul_div_cancel_left₀ _ hd.ne']
    ring
  rw [e]
  obtain ⟨k, hkdef⟩ : ∃ k, k = ⌈Real.log d⌉₊ := ⟨_, rfl⟩
  have hlog := hR.logd
  have hk1 : 1 ≤ k := by rw [hkdef]; exact Nat.ceil_pos.2 (by linarith)
  have hkge : Real.log d ≤ k := by rw [hkdef]; exact Nat.le_ceil _
  have hklt : (k : ℝ) < Real.log d + 1 := by
    rw [hkdef]; exact Nat.ceil_lt_add_one (by linarith)
  have hk4 : 2 * (2 * k) ≤ p := by
    have h := hR.interp_order_le
    have : ((2 * (2 * k) : ℕ) : ℝ) ≤ p := by push_cast; linarith
    exact_mod_cast this
  have hint := SecA.lawE_mul_le_interp cp.G (cp.Zw_pos hR)
    (X := fun σ => (SecA.coreDefect cp.G (aOf d p) 1 z cp.yp σ cp.S v +
      SecA.coreDefect cp.G (aOf d p) (-1) z cp.ym σ cp.S v) / d)
    (Y := fun σ => cp.hp σ v + cp.hm σ v)
    (fun σ hσ => div_nonneg (add_nonneg (cp.defect_pt hR hz hv hσ).1
      (cp.defect_pt hR hz hv hσ).2.1) hd.le)
    (fun σ hσ => add_nonneg ((SecA.precN_posDef_of_wt cp hσ).1.inv.diag_pos).le
      ((SecA.precN_posDef_of_wt cp hσ).2.inv.diag_pos).le)
    hk1 (m := 8 * (θ + b0Of d p)) (θ := 1 / d) (BX := 4 * (1 + 2 * epsP d p))
    (BY := 2 * (1 + 2 * epsP d p)) (by positivity) (by linarith) (by positivity)
    (by positivity) (cp.lawE_W_le hR hz hdz hθ0 hθ hv) (cp.lawE_W_sq_le hR hz hv)
    (cp.lawE_hsum_pow_le hR hv hk1 hk4)
  have hfin := SecA.interp_const_le hd hk1 hkge (c := 1 + 2 * epsP d p) (by linarith)
    (by linarith) (x := θ + b0Of d p) (by linarith)
  have hint' : cp.E (fun σ => (SecA.coreDefect cp.G (aOf d p) 1 z cp.yp σ cp.S v +
        SecA.coreDefect cp.G (aOf d p) (-1) z cp.ym σ cp.S v) / d *
          (cp.hp σ v + cp.hm σ v)) ≤ 180 * (θ + b0Of d p) := hint.trans hfin
  calc (d : ℝ) * _ ≤ d * (180 * (θ + b0Of d p)) := mul_le_mul_of_nonneg_left hint' hd.le
    _ = 180 * d * (θ + b0Of d p) := by ring

end CapPoint

namespace SecA

/-- `A-C4T`: the transfer of (C4) to signs. -/
theorem transfer_C4T : ∃ C : ℝ, 0 < C ∧ ∀ d p : ℕ, RegA d p → ∀ cp : CapPoint.{u} d p,
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
            Real.exp (-(p : ℝ)) / d) :=
  transfer_C4T_pf.{u}

/-- `A-TT`: the transferred terms of (C4) at `M = M_z`. -/
theorem transferred_TT : ∃ C : ℝ, 0 < C ∧ ∀ d p : ℕ, RegA d p → ∀ cp : CapPoint.{u} d p,
    ∀ z : ℝ, 0 < z → 1 ≤ (d : ℝ) * z → ∀ θ : ℝ, 0 ≤ θ → cp.DefZLe z θ → ∀ v ∈ cp.S,
      cp.E (fun σ => (cp.Mz z σ v * cp.A σ v).trace * cp.taup σ v +
          (cp.Mz z σ v * cp.B σ v).trace * cp.taum σ v) ≤ C * (θ + b0Of d p) / (d * z) ∧
      cp.E (fun σ => qForm (cp.A σ v * cp.Mz z σ v * cp.A σ v) (cp.xi σ v) * cp.taup σ v ^ 2 +
          qForm (cp.B σ v * cp.Mz z σ v * cp.B σ v) (cp.xi σ v) * cp.taum σ v ^ 2) ≤
        C * (θ + b0Of d p) / (d * z) := by
  obtain ⟨Cr, hCr, hrow⟩ := row_bound.{u}
  refine ⟨720 + 2 * Cr, by positivity, fun d p hR cp z hz hdz θ hθ0 hθ v hv => ?_⟩
  have hρ := CapPoint.DefZLe.defLe cp hR hz.le hθ
  obtain ⟨r1, r2⟩ := hrow d p hR cp θ hθ0 hρ v hv
  have hd := hR.d_pos
  have hb := hR.b0Of_pos
  have hX : 0 ≤ (θ + b0Of d p) / (d * z) := by positivity
  have eC : (720 + 2 * Cr) * (θ + b0Of d p) / (d * z) =
      (720 + 2 * Cr) * ((θ + b0Of d p) / (d * z)) := by ring
  rw [eC]
  constructor
  · have h1 : cp.E (fun σ => (cp.Mz z σ v * cp.A σ v).trace * cp.taup σ v +
          (cp.Mz z σ v * cp.B σ v).trace * cp.taum σ v) ≤
        cp.E (fun σ => 16 * aOf d p ^ 4 / z * ((cp.hp σ v + cp.hm σ v) *
          (SecA.coreDefect cp.G (aOf d p) 1 z cp.yp σ cp.S v +
            SecA.coreDefect cp.G (aOf d p) (-1) z cp.ym σ cp.S v))) :=
      lawE_le_of_supp cp.G fun σ hσ => cp.tt_trace_pt hR hz hσ
    have h2 : cp.E (fun σ => 16 * aOf d p ^ 4 / z * ((cp.hp σ v + cp.hm σ v) *
          (SecA.coreDefect cp.G (aOf d p) 1 z cp.yp σ cp.S v +
            SecA.coreDefect cp.G (aOf d p) (-1) z cp.ym σ cp.S v))) =
        16 * aOf d p ^ 4 / z * cp.E (fun σ => (cp.hp σ v + cp.hm σ v) *
          (SecA.coreDefect cp.G (aOf d p) 1 z cp.yp σ cp.S v +
            SecA.coreDefect cp.G (aOf d p) (-1) z cp.ym σ cp.S v)) :=
      lawE_const_mul cp.G _ _
    have h3 := cp.lawE_hW_le hR hz hdz hθ0 hθ hv
    have ha4 := aOf_four_le hR
    have h4 : 16 * aOf d p ^ 4 / z * (180 * d * (θ + b0Of d p)) ≤
        720 * ((θ + b0Of d p) / (d * z)) := by
      have e : 16 * aOf d p ^ 4 / z * (180 * d * (θ + b0Of d p)) =
          (4 * (d : ℝ) ^ 2 * aOf d p ^ 4) * (720 * ((θ + b0Of d p) / (d * z))) := by
        field_simp
        ring
      have h5 : 4 * (d : ℝ) ^ 2 * aOf d p ^ 4 ≤ 1 := by
        rw [le_div_iff₀ (by positivity)] at ha4
        linarith
      rw [e]
      exact mul_le_of_le_one_left (by positivity) h5
    have h16 : 0 ≤ 16 * aOf d p ^ 4 / z := by positivity
    have := mul_le_mul_of_nonneg_left h3 h16
    have := mul_nonneg hCr.le hX
    linarith
  · have h1 : cp.E (fun σ =>
          qForm (cp.A σ v * cp.Mz z σ v * cp.A σ v) (cp.xi σ v) * cp.taup σ v ^ 2 +
          qForm (cp.B σ v * cp.Mz z σ v * cp.B σ v) (cp.xi σ v) * cp.taum σ v ^ 2) ≤
        cp.E (fun σ => 1 / (d * z) * (aOf d p ^ 2 * ∑ i ∈ cp.N v, cp.gp σ v i ^ 2 +
          aOf d p ^ 2 * ∑ i ∈ cp.N v, cp.gm σ v i ^ 2)) :=
      lawE_le_of_supp cp.G fun σ hσ => cp.tt_quad_pt hR hz hv hσ
    have h2 : cp.E (fun σ => 1 / (d * z) * (aOf d p ^ 2 * ∑ i ∈ cp.N v, cp.gp σ v i ^ 2 +
          aOf d p ^ 2 * ∑ i ∈ cp.N v, cp.gm σ v i ^ 2)) =
        1 / (d * z) * (aOf d p ^ 2 * ∑ i ∈ cp.N v, cp.E (fun σ => cp.gp σ v i ^ 2) +
          aOf d p ^ 2 * ∑ i ∈ cp.N v, cp.E (fun σ => cp.gm σ v i ^ 2)) := by
      unfold CapPoint.E
      simp only [lawE_const_mul, lawE_add, lawE_sum]
    rw [h2] at h1
    have h0 : 0 ≤ 1 / ((d : ℝ) * z) := by positivity
    have h3 := mul_le_mul_of_nonneg_left (add_le_add r1 r2) h0
    have e : 1 / ((d : ℝ) * z) * (Cr * (θ + b0Of d p) + Cr * (θ + b0Of d p)) =
        2 * Cr * ((θ + b0Of d p) / (d * z)) := by ring
    linarith

/-- `A-C6` (C6): the normalized shifted bias. -/
theorem bias_C6 : ∃ C : ℝ, 0 < C ∧ ∀ d p : ℕ, RegA d p → ∀ cp : CapPoint.{u} d p,
    ∀ z : ℝ, 0 < z → 1 ≤ (d : ℝ) * z → ∀ θ : ℝ, 0 ≤ θ → cp.DefZLe z θ → ∀ v ∈ cp.S,
      cp.E (fun σ => (cp.Mz z σ v).trace - qForm (cp.Mz z σ v) (cp.xi σ v)) ≤
        C * ((p : ℝ) * (θ + b0Of d p) / (d * z) + (p : ℝ) ^ 5 * (θ + b0Of d p) / d +
          (p : ℝ) ^ 2 / d + (p : ℝ) ^ 9 / (d : ℝ) ^ 2 + Real.exp (-(p : ℝ))) := by
  obtain ⟨C4, hC4, h4⟩ := transfer_C4T.{u}
  obtain ⟨CT, hCT, hT⟩ := transferred_TT.{u}
  refine ⟨C4 + 6 * CT, by linarith, fun d p hR cp z hz hdz θ hθ0 hθ v hv => ?_⟩
  have hρ : cp.DefLe θ := CapPoint.DefZLe.defLe cp hR hz.le hθ
  have hinv : ∀ σ σ', AgreeOff v σ σ' → cp.Mz z σ v = cp.Mz z σ' v := by
    intro σ σ' h
    simp only [CapPoint.Mz, rootMzG, coreShift_congr cp.G h]
    rfl
  have hpsd : ∀ σ, 0 < wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v →
      (cp.Mz z σ v).PosSemidef ∧ (cp.A σ v - cp.Mz z σ v).PosSemidef := by
    intro σ hσ
    exact rootMz_psd_le cp.G hz.le cp.yp_nonneg
      (posDef_of_wtCore_ne_zero cp.G hσ.ne').1
  have hC := h4 d p hR cp θ hθ0 hρ v hv (fun σ => cp.Mz z σ v) hinv hpsd
  obtain ⟨t1, t2⟩ := hT d p hR cp z hz hdz θ hθ0 hθ v hv
  have hd := hR.d_pos
  have hd1 : (1 : ℝ) ≤ d := by have := hR.treg.ten_pow_six_le_d; linarith
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hb := hR.b0Of_pos
  have hX : 0 ≤ (θ + b0Of d p) / (d * z) := by positivity
  have he : Real.exp (-(p : ℝ)) / d ≤ Real.exp (-(p : ℝ)) :=
    div_le_self (Real.exp_pos _).le hd1
  set Y := (p : ℝ) ^ 5 * (θ + b0Of d p) / d + (p : ℝ) ^ 2 / d + (p : ℝ) ^ 9 / (d : ℝ) ^ 2
    with hY
  have hY0 : 0 ≤ Y := by positivity
  have e1 : (p : ℝ) * (θ + b0Of d p) / (d * z) = p * ((θ + b0Of d p) / (d * z)) := by ring
  have h2 : 2 * (p : ℝ) * cp.E (fun σ => (cp.Mz z σ v * cp.A σ v).trace * cp.taup σ v +
      (cp.Mz z σ v * cp.B σ v).trace * cp.taum σ v) ≤
        2 * p * (CT * ((θ + b0Of d p) / (d * z))) := by
    rw [mul_div_assoc] at t1
    exact mul_le_mul_of_nonneg_left t1 (by positivity)
  have h3 : 4 * (p : ℝ) * cp.E (fun σ => qForm (cp.A σ v * cp.Mz z σ v * cp.A σ v) (cp.xi σ v) *
      cp.taup σ v ^ 2 + qForm (cp.B σ v * cp.Mz z σ v * cp.B σ v) (cp.xi σ v) *
        cp.taum σ v ^ 2) ≤ 4 * p * (CT * ((θ + b0Of d p) / (d * z))) := by
    rw [mul_div_assoc] at t2
    exact mul_le_mul_of_nonneg_left t2 (by positivity)
  rw [e1]
  have hpX : 0 ≤ (p : ℝ) * ((θ + b0Of d p) / (d * z)) := mul_nonneg hp0 hX
  have hE0 : 0 ≤ Real.exp (-(p : ℝ)) := (Real.exp_pos _).le
  nlinarith [mul_nonneg hCT.le hpX, mul_nonneg hC4.le hpX, mul_nonneg hCT.le hY0,
    mul_nonneg hCT.le hE0, mul_nonneg hC4.le hE0]

end SecA

end BiluLinial.Tight
