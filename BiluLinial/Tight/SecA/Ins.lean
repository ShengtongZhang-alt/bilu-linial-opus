/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecA.WAvg
public import BiluLinial.Tight.SecA.Schur
public import BiluLinial.Tight.Star
public import BiluLinial.Tight.FloorLemma
public import BiluLinial.Tight.SourceMax.Law

/-!
# Root insertion for core-measurable observables; (F1); the Schur identity (C3)

Nodes `A-INS`, `A-ROOTPSD`, `A-C3` (source lines 125–141 and 400–405; AUDIT-A §1.3 (INS),
§2.10). The star representation of the paired law (`lawE_eq_star`, `sum_wt_mul_eq_star`,
`qRoot_eq_qForm`, `PhiRoot_eq_starPhi`, `radE_eq_sum`, `setRoot`) is node `D-star`
(`Tight/Star.lean`); it is used here, not restated.

* `A-INS-cong` (`wtCore_congr`, `rootMat_congr`, `coreShift_congr`): the core weight, the root
  matrices and the core shifted inverses only see the signs off the edges at `v` (`AgreeOff`).
* `A-INS` (`lawE_eq_coreE_div`): for `g(σ, ξ)` core-measurable in `σ`,
  `E_H[g(σ, ξ_σ)] = E_{ν_K}[𝖱(Φ g)] / F_H` (`lawE_eq_star` with `f σ = g σ ξ_σ`, since
  `setRoot σ ξ` agrees with `σ` off `v` and has star vector `ξ` at sign vectors), and
  `F_H > 0` when the law exists (`insF_pos`).
* `A-ROOTPSD` (`rootMat_posSemidef`): at a good core (`precCore ≻ 0`) the root matrix is PSD.
* `A-C3` (C3): `E_{ν_K} N_R / F_H = 1 - D_v E h_v + a² Σ_{i ∈ N} E(G_vv G_ii - G_vi²)`, both
  branches, exact (checked by enumeration in AUDIT-A I2). Proof: `A-INS` with
  `g = f₁/Φ = (tr A - q_A)/α` on the support; `(tr A - q_A)/α = 1 + (tr A - 1) τ⁺` with
  `τ⁺ = D_v h_v = 1/α` (F1, Schur at `v`), and `tr A · τ⁺ = a² y_v h_v Σ_{i ∈ N} G_{K,ii}
  = a² Σ_{i ∈ N} (G_vv G_ii - G_vi²)` (F1: `G_ii = G_{K,ii} + G_vi²/G_vv`).

Small cases: `S = {v}` (`N = ∅`, `A = 0`, `Φ = 1`, `F_H = 1`, both sides of (C3) equal
`1 - E h_v = 0`); `y_v = 0` (`A = 0`, `h_v = 1`, `D_v = 1`, `G_v· = 0`: both sides `0`).
-/

@[expose] public section

universe u

namespace BiluLinial.Tight

open Matrix MeasureTheory

namespace SecA

section Ins

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

omit [Fintype V] in
/-- The inherited core precision only sees the signs off the edges at `v`. -/
theorem precCore_congr' {a τ : ℝ} {y : V → ℝ} {S : Finset V} {v : V} {σ σ' : Config V}
    (h : AgreeOff v σ σ') : precCore G a τ y σ S v = precCore G a τ y σ' S v := by
  ext u w
  simp only [precCore, precN, of_apply]
  by_cases huv : u = v ∨ w = v
  · rw [ite_eq_left huv, ite_eq_left huv]
  · rw [ite_eq_right huv, ite_eq_right huv]
    push Not at huv
    have hs : sgn σ u w = sgn σ' u w := by
      unfold sgn
      rw [h s(u, w) (by simp [Sym2.mem_iff, Ne.symm huv.1, Ne.symm huv.2])]
    rw [hs]

/-- `A-INS-cong`: the core weight only sees the signs off the edges at `v`. -/
theorem wtCore_congr {p : ℕ} {a : ℝ} {yp ym : V → ℝ} {S : Finset V} {v : V} {σ σ' : Config V}
    (h : AgreeOff v σ σ') : wtCore G p a yp ym σ S v = wtCore G p a yp ym σ' S v := by
  unfold wtCore
  rw [precCore_congr' G h, precCore_congr' G h]

/-- `A-INS-cong`: the root matrices only see the signs off the edges at `v`. -/
theorem rootMat_congr {a τ : ℝ} {y : V → ℝ} {S : Finset V} {v : V} {σ σ' : Config V}
    (h : AgreeOff v σ σ') : rootMat G a τ y σ S v = rootMat G a τ y σ' S v := by
  ext i j
  simp only [rootMat, coreGreen, of_apply, precCore_congr' G h]

/-- `A-INS-cong`: the physical core shifted inverses only see the signs off the edges at `v`. -/
theorem coreShift_congr {a τ z : ℝ} {y : V → ℝ} {S : Finset V} {v : V} {σ σ' : Config V}
    (h : AgreeOff v σ σ') (i j : V) :
    coreShift G a τ z y σ S v i j = coreShift G a τ z y σ' S v i j := by
  simp only [coreShift, precCore_congr' G h]

omit [Fintype V] in
/-- `setRoot σ ξ` agrees with `σ` off the edges at `v`. -/
theorem agreeOff_setRoot {S : Finset V} {v : V} (σ : Config V) (ξ : nbhd G S v → ℝ) :
    AgreeOff v (setRoot G S v σ ξ) σ := by
  intro e he
  induction e using Sym2.ind with
  | h u w =>
    have hu : u ≠ v := fun h => he (by simp [h])
    have hw : w ≠ v := fun h => he (by simp [h])
    exact setRoot_apply_of_ne G σ ξ hu hw

theorem wtCore_nonneg' {p : ℕ} {a : ℝ} {yp ym : V → ℝ} {S : Finset V} {v : V}
    (σ : Config V) : 0 ≤ wtCore G p a yp ym σ S v := by
  unfold wtCore
  split_ifs with h
  · exact pow_nonneg (mul_pos h.1.det_pos h.2.det_pos).le _
  · exact le_rfl

/-- `(Σ W X / Z)/(Σ W Y / Z) = Σ W X / Σ W Y` with `Z = Σ W`, `W ≥ 0`. -/
theorem coreE_div_coreE {p : ℕ} {a : ℝ} {yp ym : V → ℝ} {S : Finset V} {v : V}
    (X Y : Config V → ℝ) :
    coreE G p a yp ym S v X / coreE G p a yp ym S v Y =
      (∑ σ, wtCore G p a yp ym σ S v * X σ) / ∑ σ, wtCore G p a yp ym σ S v * Y σ := by
  unfold coreE
  by_cases hZ : ZwCore G p a yp ym S v = 0
  · have hall : ∀ σ, wtCore G p a yp ym σ S v = 0 := fun σ =>
      (Finset.sum_eq_zero_iff_of_nonneg fun σ _ => wtCore_nonneg' G σ).1 hZ σ
        (Finset.mem_univ σ)
    simp [hall, hZ]
  · rw [div_div_div_cancel_right₀ hZ]

/-- `A-INS`: the paired law of `H` as a fresh-star average over the own core law. -/
theorem lawE_eq_coreE_div {p : ℕ} (hp : 1 ≤ p) (a : ℝ) {yp ym : V → ℝ} (hyp : ∀ i, 0 ≤ yp i)
    (hym : ∀ i, 0 ≤ ym i) {S : Finset V} {v : V} (hv : v ∈ S)
    (g : Config V → (nbhd G S v → ℝ) → ℝ)
    (hg : ∀ σ σ', AgreeOff v σ σ' → g σ = g σ') :
    lawE G p a yp ym S (fun σ => g σ (rootSigns G σ S v)) =
      coreE G p a yp ym S v (fun σ => radE fun ξ =>
        starPhi p (rootMat G a 1 yp σ S v) (rootMat G a (-1) ym σ S v) ξ * g σ ξ) /
        insF G p a yp ym S v := by
  rw [lawE_eq_star G hp a hyp hym hv, insF, coreE_div_coreE]
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  rw [radE_eq_sum, radE_eq_sum]
  congr 1
  refine Finset.sum_congr rfl fun ε _ => ?_
  have hpm : ∀ i, (if ε i then (1 : ℝ) else -1) = 1 ∨ (if ε i then (1 : ℝ) else -1) = -1 := by
    intro i
    by_cases h : ε i <;> simp [h]
  rw [rootSigns_setRoot G σ hpm, hg _ _ (agreeOff_setRoot G σ _)]

/-- The insertion factor is positive when the law exists. -/
theorem insF_pos {p : ℕ} (hp : 1 ≤ p) (a : ℝ) {yp ym : V → ℝ} (hyp : ∀ i, 0 ≤ yp i)
    (hym : ∀ i, 0 ≤ ym i) {S : Finset V} {v : V} (hv : v ∈ S) (hZ : 0 < Zw G p a yp ym S) :
    0 < insF G p a yp ym S v := by
  have hstar := sum_wt_mul_eq_star G hp a hyp hym hv (fun _ => 1)
  simp only [mul_one] at hstar
  have hX : 0 < ∑ σ : Config V, wtCore G p a yp ym σ S v *
      radE (starPhi p (rootMat G a 1 yp σ S v) (rootMat G a (-1) ym σ S v)) := by
    have hZ' : 0 < (diagD G a yp S v * diagD G a ym S v) ^ p * ∑ σ : Config V,
        wtCore G p a yp ym σ S v *
          radE (starPhi p (rootMat G a 1 yp σ S v) (rootMat G a (-1) ym σ S v)) := by
      rw [← hstar]; exact hZ
    have hc : 0 ≤ (diagD G a yp S v * diagD G a ym S v) ^ p := by
      have h1 : 0 ≤ ∑ j ∈ nbhd G S v, cEdge a yp v j := Finset.sum_nonneg fun j _ =>
        FloorIns.cRoot_nonneg (mul_nonneg (mul_nonneg (sq_nonneg a) (hyp v)) (hyp j))
      have h2 : 0 ≤ ∑ j ∈ nbhd G S v, cEdge a ym v j := Finset.sum_nonneg fun j _ =>
        FloorIns.cRoot_nonneg (mul_nonneg (mul_nonneg (sq_nonneg a) (hym v)) (hym j))
      unfold diagD
      positivity
    exact pos_of_mul_pos_right hZ' hc
  have hZc : 0 < ZwCore G p a yp ym S v := by
    have h0 : 0 ≤ ZwCore G p a yp ym S v :=
      Finset.sum_nonneg fun σ _ => wtCore_nonneg' G σ
    refine lt_of_le_of_ne h0 fun h => ?_
    have hall : ∀ σ, wtCore G p a yp ym σ S v = 0 := fun σ =>
      (Finset.sum_eq_zero_iff_of_nonneg fun σ _ => wtCore_nonneg' G σ).1 h.symm σ
        (Finset.mem_univ σ)
    simp [hall] at hX
  unfold insF coreE
  exact div_pos hX hZc

/-- `A-ROOTPSD`: at a good core the root matrix is positive semidefinite. -/
theorem rootMat_posSemidef {a τ : ℝ} {y : V → ℝ} (hy : ∀ i, 0 ≤ y i) {σ : Config V}
    {S : Finset V} {v : V} (hM : (precCore G a τ y σ S v).PosDef) :
    (rootMat G a τ y σ S v).PosSemidef := by
  have hD : 0 < diagD G a y S v := lt_of_lt_of_le one_pos (FloorIns.one_le_diagD G a hy S v)
  have hc0 : 0 ≤ a ^ 2 * y v / diagD G a y S v :=
    div_nonneg (mul_nonneg (sq_nonneg a) (hy v)) hD.le
  have hKpsd : (diagonal (fun i => Real.sqrt (y i)) * (precCore G a τ y σ S v)⁻¹ *
      (diagonal fun i => Real.sqrt (y i))ᴴ).PosSemidef :=
    hM.inv.posSemidef.mul_mul_conjTranspose_same _
  have e : rootMat G a τ y σ S v = (a ^ 2 * y v / diagD G a y S v) •
      (diagonal (fun i => Real.sqrt (y i)) * (precCore G a τ y σ S v)⁻¹ *
        (diagonal fun i => Real.sqrt (y i))ᴴ).submatrix Subtype.val Subtype.val := by
    ext i j
    simp only [rootMat, coreGreen, of_apply, Matrix.smul_apply, Matrix.submatrix_apply,
      smul_eq_mul, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul, Matrix.mul_diagonal,
      star_trivial]
  rw [e]
  exact (hKpsd.submatrix _).smul hc0

theorem lawE_one {p : ℕ} {a : ℝ} {yp ym : V → ℝ} {S : Finset V}
    (hZ : 0 < Zw G p a yp ym S) : lawE G p a yp ym S (fun _ => 1) = 1 := by
  unfold lawE
  simp only [mul_one]
  exact div_self hZ.ne'

/-- `c^p (t/c) = t c^{p-1}` for `p ≥ 2` (also at `c = 0`). -/
theorem pow_mul_div_self {p : ℕ} (hp : 2 ≤ p) (c t : ℝ) : c ^ p * (t / c) = t * c ^ (p - 1) := by
  rcases eq_or_ne c 0 with h | h
  · simp [h, zero_pow (show p ≠ 0 by omega), zero_pow (show p - 1 ≠ 0 by omega)]
  · obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
    have e : c ^ (k + 1) * (t / c) = t * c ^ k * (c / c) := by ring
    rw [e, div_self h, mul_one, Nat.add_sub_cancel]

/-- (C3) pointwise, one branch (`P̃ ≻ 0`, `τ² = 1`): with `α = (1 - q_A(ξ))₊ = 1/(D_v h_v)`,
`(tr A - q_A(ξ))/α = 1 - D_v h_v + a² Σ_{i ∈ N} (G_vv G_ii - G_vi²)`; by the root Schur identity
`G_vv G_ii - G_vi² = h_v y_v y_i (P̃_core⁻¹)_ii` and `tr A = (a² y_v/D_v) Σ_{i ∈ N} y_i (P̃_core⁻¹)_ii`. -/
theorem f1_ratio_branch {a τ : ℝ} (hτ : τ ^ 2 = 1) {y : V → ℝ} (hy : ∀ i, 0 ≤ y i)
    {S : Finset V} {v : V} (hv : v ∈ S) {σ : Config V} (hP : (precN G a τ y σ S).PosDef) :
    ((rootMat G a τ y σ S v).trace - qForm (rootMat G a τ y σ S v) (rootSigns G σ S v)) /
        clipF (rootMat G a τ y σ S v) (rootSigns G σ S v) =
      1 - diagD G a y S v * hN G a τ y σ S v + a ^ 2 * ∑ i ∈ nbhd G S v,
        (greenP G a τ y σ S v v * greenP G a τ y σ S i i - greenP G a τ y σ S v i ^ 2) := by
  obtain ⟨hd, hrow, hij⟩ := precN_schur G hv hP
  have hD : 0 < diagD G a y S v := lt_of_lt_of_le one_pos (FloorIns.one_le_diagD G a hy S v)
  have hg0 : 0 < (precN G a τ y σ S)⁻¹ v v := hP.inv.diag_pos
  obtain ⟨g, hg⟩ : ∃ g, g = (precN G a τ y σ S)⁻¹ v v := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K, K = (precCore G a τ y σ S v)⁻¹ := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u, u = K *ᵥ incCol G a τ y σ S v := ⟨_, rfl⟩
  rw [← hK, ← hu, ← hg] at hd
  rw [← hg] at hg0
  have hq : qForm (rootMat G a τ y σ S v) (rootSigns G σ S v) =
      incCol G a τ y σ S v ⬝ᵥ u / diagD G a y S v := by
    rw [← qRoot_eq_qForm G hτ hy σ hv, qRoot, ← hK, ← hu]
  have hbu : incCol G a τ y σ S v ⬝ᵥ u = diagD G a y S v - 1 / g := by
    have h1 : diagD G a y S v - incCol G a τ y σ S v ⬝ᵥ u = 1 / g := by
      rw [eq_div_iff hg0.ne']
      linear_combination hd
    linarith
  have hclip : clipF (rootMat G a τ y σ S v) (rootSigns G σ S v) =
      1 / (g * diagD G a y S v) := by
    have e : 1 - qForm (rootMat G a τ y σ S v) (rootSigns G σ S v) =
        1 / (g * diagD G a y S v) := by
      rw [hq, hbu]
      field_simp
      ring
    rw [clipF, e]
    exact max_eq_left (by positivity)
  have hterm : ∀ i ∈ nbhd G S v, greenP G a τ y σ S v v * greenP G a τ y σ S i i -
      greenP G a τ y σ S v i ^ 2 = g * y v * (y i * K i i) := by
    intro i hi
    have hiv : i ≠ v := (G.ne_of_adj (Finset.mem_filter.1 hi).2).symm
    have hyv := Real.mul_self_sqrt (hy v)
    have hyi := Real.mul_self_sqrt (hy i)
    simp only [greenP]
    rw [hij i i hiv hiv, hrow i hiv, ← hg, ← hK, ← hu]
    linear_combination (g * (Real.sqrt (y i) * Real.sqrt (y i)) * K i i) * hyv +
      (g * y v * K i i) * hyi
  have htr : (rootMat G a τ y σ S v).trace =
      a ^ 2 * y v / diagD G a y S v * ∑ i ∈ nbhd G S v, y i * K i i := by
    rw [Matrix.trace, Finset.mul_sum, ← Finset.sum_coe_sort (nbhd G S v)]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [diag_apply, rootMat, coreGreen, of_apply, ← hK]
    linear_combination (a ^ 2 * y v / diagD G a y S v * K i i) * Real.mul_self_sqrt (hy i)
  have hh : hN G a τ y σ S v = g := by rw [hg]; rfl
  rw [Finset.sum_congr rfl hterm, htr, hclip, hq, hbu, hh, ← Finset.mul_sum]
  field_simp
  ring

end Ins

end SecA

namespace CapPoint

variable {d p : ℕ} (cp : CapPoint.{u} d p)

theorem yp_nonneg : ∀ i, 0 ≤ cp.yp i := fun i => (cp.hyp i).1

theorem ym_nonneg : ∀ i, 0 ≤ cp.ym i := fun i => (cp.hym i).1

/-- The capped cube lies in the full cube. -/
theorem inCube_yp (hR : RegA d p) : InCube (sOf d p) cp.yp := fun i =>
  ⟨(cp.hyp i).1, (cp.hyp i).2.trans (by
    have := hR.treg.sOf_pos
    nlinarith [cp.ctx.lam_le_one, cp.ctx.lam_nonneg])⟩

theorem inCube_ym (hR : RegA d p) : InCube (sOf d p) cp.ym := fun i =>
  ⟨(cp.hym i).1, (cp.hym i).2.trans (by
    have := hR.treg.sOf_pos
    nlinarith [cp.ctx.lam_le_one, cp.ctx.lam_nonneg])⟩

/-- (M0) The law exists at the point. -/
theorem Zw_pos (hR : RegA d p) : 0 < Zw cp.G p (aOf d p) cp.yp cp.ym cp.S :=
  cp.ctx.pos cp.yp cp.ym (cp.inCube_yp hR) (cp.inCube_ym hR)

/-- `A-C3` (C3), plus branch. -/
theorem schur_C3 (hR : RegA d p) {v : cp.V} (hv : v ∈ cp.S) :
    cp.coreE v (fun σ => radE (f1Obs p (cp.A σ v) (cp.B σ v))) / cp.FH v =
      1 - diagD cp.G (aOf d p) cp.yp cp.S v * cp.E (fun σ => cp.hp σ v) +
        aOf d p ^ 2 * ∑ i ∈ cp.N v,
          cp.E (fun σ => cp.gp σ v v * cp.gp σ i i - cp.gp σ v i ^ 2) := by
  have hp2 : 2 ≤ p := hR.treg.two_le_p
  have hp1 : 1 ≤ p := le_trans (by norm_num) hp2
  have hins := SecA.lawE_eq_coreE_div cp.G hp1 (aOf d p) cp.yp_nonneg cp.ym_nonneg hv
    (fun σ ξ => ((rootMat cp.G (aOf d p) 1 cp.yp σ cp.S v).trace -
      qForm (rootMat cp.G (aOf d p) 1 cp.yp σ cp.S v) ξ) /
        clipF (rootMat cp.G (aOf d p) 1 cp.yp σ cp.S v) ξ)
    (fun σ σ' h => by simp only [SecA.rootMat_congr cp.G h])
  have hpt : ∀ σ ξ, starPhi p (rootMat cp.G (aOf d p) 1 cp.yp σ cp.S v)
      (rootMat cp.G (aOf d p) (-1) cp.ym σ cp.S v) ξ *
        (((rootMat cp.G (aOf d p) 1 cp.yp σ cp.S v).trace -
          qForm (rootMat cp.G (aOf d p) 1 cp.yp σ cp.S v) ξ) /
            clipF (rootMat cp.G (aOf d p) 1 cp.yp σ cp.S v) ξ) =
      f1Obs p (rootMat cp.G (aOf d p) 1 cp.yp σ cp.S v)
        (rootMat cp.G (aOf d p) (-1) cp.ym σ cp.S v) ξ := by
    intro σ ξ
    simp only [starPhi, f1Obs]
    linear_combination (clipF (rootMat cp.G (aOf d p) (-1) cp.ym σ cp.S v) ξ ^ p) *
      SecA.pow_mul_div_self hp2 (clipF (rootMat cp.G (aOf d p) 1 cp.yp σ cp.S v) ξ)
        ((rootMat cp.G (aOf d p) 1 cp.yp σ cp.S v).trace -
          qForm (rootMat cp.G (aOf d p) 1 cp.yp σ cp.S v) ξ)
  simp only [hpt] at hins
  have e1 : cp.coreE v (fun σ => radE (f1Obs p (cp.A σ v) (cp.B σ v))) / cp.FH v =
      lawE cp.G p (aOf d p) cp.yp cp.ym cp.S (fun σ =>
        ((rootMat cp.G (aOf d p) 1 cp.yp σ cp.S v).trace -
          qForm (rootMat cp.G (aOf d p) 1 cp.yp σ cp.S v) (rootSigns cp.G σ cp.S v)) /
            clipF (rootMat cp.G (aOf d p) 1 cp.yp σ cp.S v) (rootSigns cp.G σ cp.S v)) :=
    hins.symm
  have hsupp : ∀ σ, wt cp.G p (aOf d p) cp.yp cp.ym σ cp.S ≠ 0 →
      ((rootMat cp.G (aOf d p) 1 cp.yp σ cp.S v).trace -
          qForm (rootMat cp.G (aOf d p) 1 cp.yp σ cp.S v) (rootSigns cp.G σ cp.S v)) /
            clipF (rootMat cp.G (aOf d p) 1 cp.yp σ cp.S v) (rootSigns cp.G σ cp.S v) =
        1 - diagD cp.G (aOf d p) cp.yp cp.S v * hN cp.G (aOf d p) 1 cp.yp σ cp.S v +
          aOf d p ^ 2 * ∑ i ∈ nbhd cp.G cp.S v,
            (greenP cp.G (aOf d p) 1 cp.yp σ cp.S v v * greenP cp.G (aOf d p) 1 cp.yp σ cp.S i i -
              greenP cp.G (aOf d p) 1 cp.yp σ cp.S v i ^ 2) := by
    intro σ hσ
    have hP : (precN cp.G (aOf d p) 1 cp.yp σ cp.S).PosDef := by
      by_contra hc
      exact hσ (by simp [wt, hc])
    exact SecA.f1_ratio_branch cp.G (by norm_num) cp.yp_nonneg hv hP
  rw [e1, lawE_congr cp.G hsupp, lawE_add, lawE_sub, lawE_const_mul, lawE_const_mul, lawE_sum,
    SecA.lawE_one cp.G (cp.Zw_pos hR)]
  rfl

/-- `A-C3` (C3), minus branch (`(tr B - q_B) α^p β^{p-1}`). -/
theorem schur_C3_minus (hR : RegA d p) {v : cp.V} (hv : v ∈ cp.S) :
    cp.coreE v (fun σ => radE (f1Obs p (cp.B σ v) (cp.A σ v))) / cp.FH v =
      1 - diagD cp.G (aOf d p) cp.ym cp.S v * cp.E (fun σ => cp.hm σ v) +
        aOf d p ^ 2 * ∑ i ∈ cp.N v,
          cp.E (fun σ => cp.gm σ v v * cp.gm σ i i - cp.gm σ v i ^ 2) := by
  have hp2 : 2 ≤ p := hR.treg.two_le_p
  have hp1 : 1 ≤ p := le_trans (by norm_num) hp2
  have hins := SecA.lawE_eq_coreE_div cp.G hp1 (aOf d p) cp.yp_nonneg cp.ym_nonneg hv
    (fun σ ξ => ((rootMat cp.G (aOf d p) (-1) cp.ym σ cp.S v).trace -
      qForm (rootMat cp.G (aOf d p) (-1) cp.ym σ cp.S v) ξ) /
        clipF (rootMat cp.G (aOf d p) (-1) cp.ym σ cp.S v) ξ)
    (fun σ σ' h => by simp only [SecA.rootMat_congr cp.G h])
  have hpt : ∀ σ ξ, starPhi p (rootMat cp.G (aOf d p) 1 cp.yp σ cp.S v)
      (rootMat cp.G (aOf d p) (-1) cp.ym σ cp.S v) ξ *
        (((rootMat cp.G (aOf d p) (-1) cp.ym σ cp.S v).trace -
          qForm (rootMat cp.G (aOf d p) (-1) cp.ym σ cp.S v) ξ) /
            clipF (rootMat cp.G (aOf d p) (-1) cp.ym σ cp.S v) ξ) =
      f1Obs p (rootMat cp.G (aOf d p) (-1) cp.ym σ cp.S v)
        (rootMat cp.G (aOf d p) 1 cp.yp σ cp.S v) ξ := by
    intro σ ξ
    simp only [starPhi, f1Obs]
    linear_combination (clipF (rootMat cp.G (aOf d p) 1 cp.yp σ cp.S v) ξ ^ p) *
      SecA.pow_mul_div_self hp2 (clipF (rootMat cp.G (aOf d p) (-1) cp.ym σ cp.S v) ξ)
        ((rootMat cp.G (aOf d p) (-1) cp.ym σ cp.S v).trace -
          qForm (rootMat cp.G (aOf d p) (-1) cp.ym σ cp.S v) ξ)
  simp only [hpt] at hins
  have e1 : cp.coreE v (fun σ => radE (f1Obs p (cp.B σ v) (cp.A σ v))) / cp.FH v =
      lawE cp.G p (aOf d p) cp.yp cp.ym cp.S (fun σ =>
        ((rootMat cp.G (aOf d p) (-1) cp.ym σ cp.S v).trace -
          qForm (rootMat cp.G (aOf d p) (-1) cp.ym σ cp.S v) (rootSigns cp.G σ cp.S v)) /
            clipF (rootMat cp.G (aOf d p) (-1) cp.ym σ cp.S v) (rootSigns cp.G σ cp.S v)) :=
    hins.symm
  have hsupp : ∀ σ, wt cp.G p (aOf d p) cp.yp cp.ym σ cp.S ≠ 0 →
      ((rootMat cp.G (aOf d p) (-1) cp.ym σ cp.S v).trace -
          qForm (rootMat cp.G (aOf d p) (-1) cp.ym σ cp.S v) (rootSigns cp.G σ cp.S v)) /
            clipF (rootMat cp.G (aOf d p) (-1) cp.ym σ cp.S v) (rootSigns cp.G σ cp.S v) =
        1 - diagD cp.G (aOf d p) cp.ym cp.S v * hN cp.G (aOf d p) (-1) cp.ym σ cp.S v +
          aOf d p ^ 2 * ∑ i ∈ nbhd cp.G cp.S v,
            (greenP cp.G (aOf d p) (-1) cp.ym σ cp.S v v *
                greenP cp.G (aOf d p) (-1) cp.ym σ cp.S i i -
              greenP cp.G (aOf d p) (-1) cp.ym σ cp.S v i ^ 2) := by
    intro σ hσ
    have hP : (precN cp.G (aOf d p) (-1) cp.ym σ cp.S).PosDef := by
      by_contra hc
      exact hσ (by simp [wt, hc])
    exact SecA.f1_ratio_branch cp.G (by norm_num) cp.ym_nonneg hv hP
  rw [e1, lawE_congr cp.G hsupp, lawE_add, lawE_sub, lawE_const_mul, lawE_const_mul, lawE_sum,
    SecA.lawE_one cp.G (cp.Zw_pos hR)]
  rfl

end CapPoint

end BiluLinial.Tight
