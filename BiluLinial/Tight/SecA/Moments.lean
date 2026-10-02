/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecA.Reg
public import BiluLinial.Tight.SecA.ParP
public import BiluLinial.Tight.SecA.Ins
public import BiluLinial.Tight.FloorLemma
public import BiluLinial.Tight.SourceMax
public import BiluLinial.Tight.SourceMax.Law
public import BiluLinial.Tight.Deletion

/-!
# The moment toolkit of a capped point (node `A-MT`)

AUDIT-A §1.4 (CSL) and §1.5 (MT); source lines 244–248 ("the source maximum bounds the `L^j` norms
of physical diagonals … by an absolute constant for `j ≤ p/2`").

* (M0) `cp.Zw_pos` (`SecA/Ins.lean`): the law exists at the point.
* (M1) `cp.h_moment`: `E (h_x^±)^k ≤ (1 + 2ε)^k` for `1 ≤ k ≤ p/2` — from (F2)
  (`source_moments`) with `B₀ = r`, since `(pr - k)/(p - k) = 1 + pε/(p - k) ≤ 1 + 2ε`.
* (M2) `cp.h_mean_le`: `E h_x^± ≤ r = 1 + ε` (the cap).
* (M3) `cp.core_moment`: own-core moments `E_{ν_K} ((M^±)⁻¹_ii)^k ≤ (1 + 2ε)^k` for
  `1 ≤ k ≤ p/2` — the inherited core law is the law of `J = S - v` at the deletion sources
  `ŷ ≤ y` (`precCore_eq_congr`), `(M⁻¹)_ii = e_i^{-2} h^J_i(ŷ) ≤ h^J_i(ŷ)`, and (F2) for `J`
  at `ŷ` (the context `CapCtx G d p J 1` comes from the induction hypothesis `TInv J`).
* (M4) `cp.floor`: `F_H ≥ 40^{-p}` (`floor_ins` and `A-INS`, since `Σ W_core Φ(ξ_σ)` is
  `Σ W_core 𝖱Φ`).
-/

@[expose] public section

universe u

namespace BiluLinial.Tight

open Matrix

namespace CapPoint

variable {d p : ℕ} (cp : CapPoint.{u} d p)

/-- (M2) The cap. -/
theorem h_mean_le {i : cp.V} (hi : i ∈ cp.S) :
    cp.E (fun σ => cp.hp σ i) ≤ rOf d p ∧ cp.E (fun σ => cp.hm σ i) ≤ rOf d p :=
  cp.ctx.cap cp.yp cp.ym cp.hyp cp.hym i hi

/-- (M1) Moments of the normalized diagonals. -/
theorem h_moment (hR : RegA d p) {i : cp.V} (hi : i ∈ cp.S) {k : ℕ} (hk1 : 1 ≤ k)
    (hk : 2 * k ≤ p) :
    cp.E (fun σ => cp.hp σ i ^ k) ≤ (1 + 2 * epsP d p) ^ k ∧
      cp.E (fun σ => cp.hm σ i ^ k) ≤ (1 + 2 * epsP d p) ^ k := by
  have hp6 : (10 : ℝ) ^ 6 ≤ p := by exact_mod_cast hR.treg.hp
  have hk2 : k + 2 ≤ p := by
    have : (10 ^ 6 : ℕ) ≤ p := hR.treg.hp
    omega
  obtain ⟨h1, h2⟩ := source_moments cp.G hR.treg cp.ctx cp.hyp cp.hym hi hk1 hk2
  have hk' : (2 * k : ℝ) ≤ p := by exact_mod_cast hk
  have hε := SecA.epsP_nonneg hR.treg
  have hpk : (0 : ℝ) < p - k := by linarith
  have hb0 : 0 ≤ ((p : ℝ) * rOf d p - k) / ((p : ℝ) - k) := by
    have : rOf d p = 1 + epsP d p := by rw [epsP]; ring
    rw [this]
    exact div_nonneg (by nlinarith) hpk.le
  have hb : ((p : ℝ) * rOf d p - k) / ((p : ℝ) - k) ≤ 1 + 2 * epsP d p := by
    have : rOf d p = 1 + epsP d p := by rw [epsP]; ring
    rw [this, div_le_iff₀ hpk]
    nlinarith
  exact ⟨h1.trans (pow_le_pow_left₀ hb0 hb k), h2.trans (pow_le_pow_left₀ hb0 hb k)⟩

/-- The core weight is nonnegative. -/
theorem _root_.BiluLinial.Tight.SecA.wtCore_nonneg {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (p : ℕ) (a : ℝ) (yp ym : V → ℝ) (σ : Config V)
    (S : Finset V) (v : V) : 0 ≤ wtCore G p a yp ym σ S v := by
  unfold wtCore
  split_ifs with h
  · exact pow_nonneg (mul_pos h.1.det_pos h.2.det_pos).le _
  · exact le_rfl

/-- A signing of positive core weight has both inherited core precisions positive definite. -/
theorem _root_.BiluLinial.Tight.SecA.posDef_of_wtCore_ne_zero {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] {p : ℕ} {a : ℝ} {yp ym : V → ℝ}
    {σ : Config V} {S : Finset V} {v : V} (h : wtCore G p a yp ym σ S v ≠ 0) :
    (precCore G a 1 yp σ S v).PosDef ∧ (precCore G a (-1) ym σ S v).PosDef := by
  by_contra hc
  unfold wtCore at h
  exact h (by simp [hc])

/-- A supported signing has a good core. -/
theorem wtCore_ne_zero_of_wt (hR : RegA d p) {v : cp.V} (hv : v ∈ cp.S) {σ : Config cp.V}
    (h : wt cp.G p (aOf d p) cp.yp cp.ym σ cp.S ≠ 0) :
    wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v ≠ 0 := by
  intro h0
  apply h
  rw [wt_eq_wtCore_mul cp.G (le_trans (by norm_num) hR.treg.two_le_p) _ cp.yp_nonneg
    cp.ym_nonneg σ hv, h0, zero_mul, zero_mul]

/-- At a supported signing the root matrices are positive semidefinite. -/
theorem root_psd (hR : RegA d p) {v : cp.V} (hv : v ∈ cp.S) {σ : Config cp.V}
    (h : wt cp.G p (aOf d p) cp.yp cp.ym σ cp.S ≠ 0) :
    (cp.A σ v).PosSemidef ∧ (cp.B σ v).PosSemidef := by
  obtain ⟨h1, h2⟩ := SecA.posDef_of_wtCore_ne_zero cp.G (cp.wtCore_ne_zero_of_wt hR hv h)
  exact ⟨SecA.rootMat_posSemidef cp.G cp.yp_nonneg h1,
    SecA.rootMat_posSemidef cp.G cp.ym_nonneg h2⟩

/-- At a signing of positive core weight the root matrices are positive semidefinite. -/
theorem root_psd_core {v : cp.V} {σ : Config cp.V}
    (h : wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v ≠ 0) :
    (cp.A σ v).PosSemidef ∧ (cp.B σ v).PosSemidef := by
  obtain ⟨h1, h2⟩ := SecA.posDef_of_wtCore_ne_zero cp.G h
  exact ⟨SecA.rootMat_posSemidef cp.G cp.yp_nonneg h1,
    SecA.rootMat_posSemidef cp.G cp.ym_nonneg h2⟩

/-- The own core law exists. -/
theorem ZwCore_pos (hR : RegA d p) {v : cp.V} (hv : v ∈ cp.S) :
    0 < ZwCore cp.G p (aOf d p) cp.yp cp.ym cp.S v := by
  have h0 : 0 ≤ ZwCore cp.G p (aOf d p) cp.yp cp.ym cp.S v :=
    Finset.sum_nonneg fun σ _ => SecA.wtCore_nonneg cp.G _ _ _ _ σ _ _
  refine lt_of_le_of_ne h0 fun h => ?_
  have hall : ∀ σ, wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v = 0 := fun σ =>
    (Finset.sum_eq_zero_iff_of_nonneg fun σ _ => SecA.wtCore_nonneg cp.G _ _ _ _ σ _ _).1
      h.symm σ (Finset.mem_univ σ)
  have hZ := cp.Zw_pos hR
  have : Zw cp.G p (aOf d p) cp.yp cp.ym cp.S = 0 := by
    unfold Zw
    refine Finset.sum_eq_zero fun σ _ => ?_
    by_contra hne
    exact cp.wtCore_ne_zero_of_wt hR hv hne (hall σ)
  linarith

/-- (M4) The insertion floor `F_H ≥ 40^{-p}`. -/
theorem floor (hR : RegA d p) {v : cp.V} (hv : v ∈ cp.S) : 1 ≤ (40 : ℝ) ^ p * cp.FH v := by
  have hp1 : 1 ≤ p := le_trans (by norm_num) hR.treg.two_le_p
  have hZc := cp.ZwCore_pos hR hv
  have hyp0 := cp.yp_nonneg
  have hym0 := cp.ym_nonneg
  obtain ⟨yp', ep, hyp'', hep, hcp⟩ := precCore_eq_congr cp.G (aOf d p) hyp0 hv
  obtain ⟨ym', em, hym'', hem, hcm⟩ := precCore_eq_congr cp.G (aOf d p) hym0 hv
  have hc1 : InCube (sOf d p) yp' := fun i =>
    ⟨(hyp'' i).1, (hyp'' i).2.trans (cp.inCube_yp hR i).2⟩
  have hc2 : InCube (sOf d p) ym' := fun i =>
    ⟨(hym'' i).1, (hym'' i).2.trans (cp.inCube_ym hR i).2⟩
  obtain ⟨hZJ, hmJ⟩ := cp.ctx.ih (cp.S.erase v) (Finset.erase_ssubset hv) yp' ym' hc1 hc2
  have hmean : ∀ i ∈ nbhd cp.G cp.S v,
      BiluLinial.Tight.coreE cp.G p (aOf d p) cp.yp cp.ym cp.S v
          (fun σ => (precCore cp.G (aOf d p) 1 cp.yp σ cp.S v)⁻¹ i i) ≤ 101 / 100 ∧
        BiluLinial.Tight.coreE cp.G p (aOf d p) cp.yp cp.ym cp.S v
          (fun σ => (precCore cp.G (aOf d p) (-1) cp.ym σ cp.S v)⁻¹ i i) ≤ 101 / 100 := by
    intro i hi
    have hiJ : i ∈ cp.S.erase v := by
      have hi' := Finset.mem_filter.1 hi
      exact Finset.mem_erase.2 ⟨(cp.G.ne_of_adj hi'.2).symm, hi'.1⟩
    exact coreE_inv_le_of_congr cp.G hep hem hcp hcm hZJ i
      (((hmJ i hiJ).1).trans hR.treg.rOf_le) (((hmJ i hiJ).2).trans hR.treg.rOf_le)
  have hfl := floor_ins cp.G hR.treg cp.ctx.deg (cp.inCube_yp hR) (cp.inCube_ym hR) hv hZc hmean
  -- `Σ W_core Φ(ξ_σ) = Σ W_core 𝖱 Φ`
  have hD : 0 < (diagD cp.G (aOf d p) cp.yp cp.S v * diagD cp.G (aOf d p) cp.ym cp.S v) ^ p :=
    pow_pos (mul_pos (lt_of_lt_of_le one_pos (FloorIns.one_le_diagD cp.G _ cp.yp_nonneg _ _))
      (lt_of_lt_of_le one_pos (FloorIns.one_le_diagD cp.G _ cp.ym_nonneg _ _))) p
  have hstar := sum_wt_mul_eq_star cp.G hp1 (aOf d p) cp.yp_nonneg cp.ym_nonneg hv (fun _ => 1)
  have hins : ∑ σ : Config cp.V, wt cp.G p (aOf d p) cp.yp cp.ym σ cp.S * 1 =
      (diagD cp.G (aOf d p) cp.yp cp.S v * diagD cp.G (aOf d p) cp.ym cp.S v) ^ p *
        ∑ σ : Config cp.V, wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v *
          PhiRoot cp.G p (aOf d p) cp.yp cp.ym σ cp.S v := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [wt_eq_wtCore_mul cp.G hp1 _ cp.yp_nonneg cp.ym_nonneg σ hv]
    ring
  have heq : ∑ σ : Config cp.V, wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v *
        PhiRoot cp.G p (aOf d p) cp.yp cp.ym σ cp.S v =
      ∑ σ : Config cp.V, wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v *
        radE (starPhi p (rootMat cp.G (aOf d p) 1 cp.yp σ cp.S v)
          (rootMat cp.G (aOf d p) (-1) cp.ym σ cp.S v)) := by
    have h2 := hins.symm.trans hstar
    simp only [mul_one] at h2
    exact mul_left_cancel₀ hD.ne' h2
  have hFH : cp.FH v = (∑ σ : Config cp.V, wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v *
      PhiRoot cp.G p (aOf d p) cp.yp cp.ym σ cp.S v) /
      ZwCore cp.G p (aOf d p) cp.yp cp.ym cp.S v := by
    rw [heq]; rfl
  rw [hFH, mul_div_assoc', le_div_iff₀ hZc, one_mul]
  exact hfl

end CapPoint

namespace SecA

section Helpers

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Monotonicity of the paired law on its support. -/
theorem lawE_le_of_supp {p : ℕ} {a : ℝ} {yp ym : V → ℝ} {S : Finset V} {f g : Config V → ℝ}
    (h : ∀ σ, wt G p a yp ym σ S ≠ 0 → f σ ≤ g σ) :
    lawE G p a yp ym S f ≤ lawE G p a yp ym S g := by
  have := lawE_nonneg G (p := p) (a := a) (yp := yp) (ym := ym) (S := S)
    (f := fun σ => g σ - f σ) (fun σ hσ => sub_nonneg.2 (h σ hσ))
  rw [lawE_sub] at this
  linarith

/-- Nonnegativity of the own core law on its support. -/
theorem coreE_nonneg_of_supp {p : ℕ} {a : ℝ} {yp ym : V → ℝ} {S : Finset V} {v : V}
    {f : Config V → ℝ} (h : ∀ σ, wtCore G p a yp ym σ S v ≠ 0 → 0 ≤ f σ) :
    0 ≤ coreE G p a yp ym S v f := by
  unfold coreE ZwCore
  refine div_nonneg (Finset.sum_nonneg fun σ _ => ?_)
    (Finset.sum_nonneg fun σ _ => wtCore_nonneg G _ _ _ _ σ _ _)
  by_cases hσ : wtCore G p a yp ym σ S v = 0
  · rw [hσ, zero_mul]
  · exact mul_nonneg (wtCore_nonneg G _ _ _ _ σ _ _) (h σ hσ)

/-- The own core law only sees its support. -/
theorem coreE_congr_of_supp {p : ℕ} {a : ℝ} {yp ym : V → ℝ} {S : Finset V} {v : V}
    {f g : Config V → ℝ} (h : ∀ σ, wtCore G p a yp ym σ S v ≠ 0 → f σ = g σ) :
    coreE G p a yp ym S v f = coreE G p a yp ym S v g := by
  unfold coreE
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  by_cases hσ : wtCore G p a yp ym σ S v = 0
  · rw [hσ, zero_mul, zero_mul]
  · rw [h σ hσ]

/-- Physical diagonal `G_ii = y_i h_i`. -/
theorem greenP_self {a τ : ℝ} {y : V → ℝ} {σ : Config V} {S : Finset V} {i : V}
    (hy : 0 ≤ y i) : greenP G a τ y σ S i i = y i * hN G a τ y σ S i := by
  rw [greenP, hN, mul_comm (Real.sqrt (y i)), mul_assoc, Real.mul_self_sqrt hy, mul_comm]

theorem coreE_const_mul' {p : ℕ} {a : ℝ} {yp ym : V → ℝ} {S : Finset V} {v : V} (c : ℝ)
    (f : Config V → ℝ) :
    coreE G p a yp ym S v (fun σ => c * f σ) = c * coreE G p a yp ym S v f := by
  rw [coreE_eq_wavg, coreE_eq_wavg, wavg_const_mul]


/-- `A-C5b`: core diagonals are below the full diagonals (Schur order). -/
theorem coreGreen_le_greenP {a τ : ℝ} {y : V → ℝ} (hy : ∀ i, 0 ≤ y i) {σ : Config V}
    {S : Finset V} {v : V} (hv : v ∈ S) (hP : (precN G a τ y σ S).PosDef) {i : V}
    (hi : i ≠ v) : coreGreen G a τ y σ S v i i ≤ greenP G a τ y σ S i i := by
  obtain ⟨-, -, hij⟩ := precN_schur G hv hP
  simp only [coreGreen, greenP]
  rw [hij i i hi hi]
  exact sqrt_mul_le_sqrt_mul_add _ _ _ _ hP.inv.diag_pos.le

end Helpers

section CoreTransfer

/-! The deletion transfer of the own core law (copies of the private lemmas `del_*` of
`Tight/Deletion.lean`, which only exports the first-moment form `coreE_inv_le_of_congr`). -/

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem isUnit_diagonal_of_one_le {e : V → ℝ} (he : ∀ i, 1 ≤ e i) : IsUnit (diagonal e) := by
  rw [isUnit_iff_isUnit_det, det_diagonal]
  exact (Finset.prod_pos fun i _ => lt_of_lt_of_le one_pos (he i)).ne'.isUnit

theorem diagConj_posDef_iff {e : V → ℝ} (he : ∀ i, 1 ≤ e i) (N : Matrix V V ℝ) :
    (diagonal e * N * diagonal e).PosDef ↔ N.PosDef := by
  have h := Matrix.IsUnit.posDef_star_left_conjugate_iff (x := N) (isUnit_diagonal_of_one_le he)
  rwa [star_eq_conjTranspose, diagonal_conjTranspose, star_trivial] at h

theorem det_diagConj (e : V → ℝ) (N : Matrix V V ℝ) :
    (diagonal e * N * diagonal e).det = (∏ i, e i) ^ 2 * N.det := by
  rw [det_mul, det_mul, det_diagonal]
  ring

/-- `0 ≤ (E N E)⁻¹_ii ≤ N⁻¹_ii` for `N ≻ 0`, `E = diag(e) ≥ I`. -/
theorem diagConj_inv_apply_mem {e : V → ℝ} (he : ∀ i, 1 ≤ e i) {N : Matrix V V ℝ}
    (hN : N.PosDef) (i : V) :
    0 ≤ (diagonal e * N * diagonal e)⁻¹ i i ∧ (diagonal e * N * diagonal e)⁻¹ i i ≤ N⁻¹ i i := by
  refine ⟨((diagConj_posDef_iff he N).2 hN).inv.diag_pos.le, ?_⟩
  have he0 : ∀ i, e i ≠ 0 := fun i => (lt_of_lt_of_le one_pos (he i)).ne'
  have hNu : IsUnit N.det := (isUnit_iff_isUnit_det _).mp hN.isUnit
  have h1 : diagonal (fun i => (e i)⁻¹) * diagonal e = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    exact inv_mul_cancel₀ (he0 i)
  have hinv : (diagonal e * N * diagonal e)⁻¹ =
      diagonal (fun i => (e i)⁻¹) * N⁻¹ * diagonal (fun i => (e i)⁻¹) := by
    apply inv_eq_left_inv
    calc _ = diagonal (fun i => (e i)⁻¹) *
          (N⁻¹ * ((diagonal (fun i => (e i)⁻¹) * diagonal e) * N)) * diagonal e := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h1, Matrix.one_mul, nonsing_inv_mul _ hNu, Matrix.mul_one, h1]
  rw [hinv, mul_diagonal, diagonal_mul]
  have hpos : 0 < N⁻¹ i i := hN.inv.diag_pos
  have hei1 : (e i)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (he i)
  have hei : 0 < (e i)⁻¹ := inv_pos.2 (lt_of_lt_of_le one_pos (he i))
  calc (e i)⁻¹ * N⁻¹ i i * (e i)⁻¹ = ((e i)⁻¹ * (e i)⁻¹) * N⁻¹ i i := by ring
    _ ≤ 1 * N⁻¹ i i := mul_le_mul_of_nonneg_right (by nlinarith) hpos.le
    _ = N⁻¹ i i := one_mul _

/-- Through the congruences, `W_core(σ) = K · W_J(σ)` with `K = ((Π e⁺)² (Π e⁻)²)^p`. -/
theorem wtCore_eq_of_diagConj {p : ℕ} {a : ℝ} {yp ym yp' ym' ep em : V → ℝ} {S : Finset V}
    {v : V} (hep : ∀ i, 1 ≤ ep i) (hem : ∀ i, 1 ≤ em i)
    (hcp : ∀ (τ : ℝ) (σ : Config V),
      precCore G a τ yp σ S v = diagonal ep * precN G a τ yp' σ (S.erase v) * diagonal ep)
    (hcm : ∀ (τ : ℝ) (σ : Config V),
      precCore G a τ ym σ S v = diagonal em * precN G a τ ym' σ (S.erase v) * diagonal em)
    (σ : Config V) :
    wtCore G p a yp ym σ S v =
      ((∏ i, ep i) ^ 2 * (∏ i, em i) ^ 2) ^ p * wt G p a yp' ym' σ (S.erase v) := by
  unfold wtCore wt
  rw [hcp 1 σ, hcm (-1) σ]
  by_cases h : (precN G a 1 yp' σ (S.erase v)).PosDef ∧
      (precN G a (-1) ym' σ (S.erase v)).PosDef
  · rw [ite_eq_left ⟨(diagConj_posDef_iff hep _).2 h.1, (diagConj_posDef_iff hem _).2 h.2⟩,
      ite_eq_left h, det_diagConj, det_diagConj, ← mul_pow]
    congr 1
    ring
  · rw [ite_eq_right (fun h' => h ⟨(diagConj_posDef_iff hep _).1 h'.1,
      (diagConj_posDef_iff hem _).1 h'.2⟩), ite_eq_right h, mul_zero]

/-- `D-transfer`: the own core law is the law of `J = S - v` at the deletion sources. -/
theorem coreE_eq_lawE_of_diagConj {p : ℕ} {a : ℝ} {yp ym yp' ym' ep em : V → ℝ}
    {S : Finset V} {v : V} (hep : ∀ i, 1 ≤ ep i) (hem : ∀ i, 1 ≤ em i)
    (hcp : ∀ (τ : ℝ) (σ : Config V),
      precCore G a τ yp σ S v = diagonal ep * precN G a τ yp' σ (S.erase v) * diagonal ep)
    (hcm : ∀ (τ : ℝ) (σ : Config V),
      precCore G a τ ym σ S v = diagonal em * precN G a τ ym' σ (S.erase v) * diagonal em)
    (f : Config V → ℝ) :
    coreE G p a yp ym S v f = lawE G p a yp' ym' (S.erase v) f := by
  have hK : 0 < ((∏ i, ep i) ^ 2 * (∏ i, em i) ^ 2) ^ p :=
    pow_pos (mul_pos (pow_pos (Finset.prod_pos fun i _ => lt_of_lt_of_le one_pos (hep i)) 2)
      (pow_pos (Finset.prod_pos fun i _ => lt_of_lt_of_le one_pos (hem i)) 2)) p
  have hZ : ZwCore G p a yp ym S v =
      ((∏ i, ep i) ^ 2 * (∏ i, em i) ^ 2) ^ p * Zw G p a yp' ym' (S.erase v) := by
    unfold ZwCore Zw
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun σ _ => wtCore_eq_of_diagConj G hep hem hcp hcm σ
  have hs : ∑ σ, wtCore G p a yp ym σ S v * f σ =
      ((∏ i, ep i) ^ 2 * (∏ i, em i) ^ 2) ^ p * ∑ σ, wt G p a yp' ym' σ (S.erase v) * f σ := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun σ _ => by
      rw [wtCore_eq_of_diagConj G hep hem hcp hcm σ, mul_assoc]
  unfold coreE lawE
  rw [hZ, hs, mul_div_mul_left _ _ hK.ne']

/-- Off the core (`i ∉ S - v`) the inherited core inverse has diagonal entry `1`. -/
theorem precCore_inv_apply_of_not_mem {a τ : ℝ} {y : V → ℝ} {σ : Config V} {S : Finset V}
    {v i : V} (hM : (precCore G a τ y σ S v).PosDef) (hi : i ∉ S.erase v) :
    (precCore G a τ y σ S v)⁻¹ i i = 1 := by
  have hcol : precCore G a τ y σ S v *ᵥ Pi.single i 1 = Pi.single i 1 := by
    funext u
    rw [mulVec_single_one, col_apply, Pi.single_apply]
    simp only [precCore, precN, of_apply]
    by_cases hiv : i = v
    · subst hiv
      simp
    · have hiS : i ∉ S := fun h => hi (Finset.mem_erase.2 ⟨hiv, h⟩)
      by_cases hu : u = i
      · subst hu
        simp [hiv, hiS]
      · simp [hu, hiS]
  have hMu : IsUnit (precCore G a τ y σ S v).det := (isUnit_iff_isUnit_det _).mp hM.isUnit
  have h2 : (precCore G a τ y σ S v)⁻¹ *ᵥ Pi.single i 1 = Pi.single i 1 := by
    conv_lhs => rw [← hcol]
    rw [mulVec_mulVec, nonsing_inv_mul _ hMu, one_mulVec]
  have h3 := congrFun h2 i
  rwa [mulVec_single_one, col_apply, Pi.single_eq_same] at h3

end CoreTransfer

end SecA

namespace CapPoint

variable {d p : ℕ} (cp : CapPoint.{u} d p)

/-- (M3) Moments of the normalized inherited core diagonals under the own core law. -/
theorem core_moment (hR : RegA d p) {v : cp.V} (hv : v ∈ cp.S) (i : cp.V) {k : ℕ}
    (hk1 : 1 ≤ k) (hk : 2 * k ≤ p) :
    cp.coreE v (fun σ => (precCore cp.G (aOf d p) 1 cp.yp σ cp.S v)⁻¹ i i ^ k) ≤
        (1 + 2 * epsP d p) ^ k ∧
      cp.coreE v (fun σ => (precCore cp.G (aOf d p) (-1) cp.ym σ cp.S v)⁻¹ i i ^ k) ≤
        (1 + 2 * epsP d p) ^ k := by
  have hε := SecA.epsP_nonneg hR.treg
  have hone : (1 : ℝ) ≤ (1 + 2 * epsP d p) ^ k := one_le_pow₀ (by linarith)
  by_cases hiJ : i ∈ cp.S.erase v
  · obtain ⟨yp', ep, hyp'', hep, hcp⟩ := precCore_eq_congr cp.G (aOf d p) cp.yp_nonneg hv
    obtain ⟨ym', em, hym'', hem, hcm⟩ := precCore_eq_congr cp.G (aOf d p) cp.ym_nonneg hv
    have hc1 : InCube (1 * sOf d p) yp' := fun j =>
      ⟨(hyp'' j).1, by rw [one_mul]; exact (hyp'' j).2.trans (cp.inCube_yp hR j).2⟩
    have hc2 : InCube (1 * sOf d p) ym' := fun j =>
      ⟨(hym'' j).1, by rw [one_mul]; exact (hym'' j).2.trans (cp.inCube_ym hR j).2⟩
    have hJ : TInv cp.G d p (cp.S.erase v) := cp.ctx.ih _ (Finset.erase_ssubset hv)
    have ctxJ : CapCtx cp.G d p (cp.S.erase v) 1 :=
      { deg := cp.ctx.deg
        ih := fun T hT => cp.ctx.ih T (ssubset_of_ssubset_of_subset hT (Finset.erase_subset v cp.S))
        pos := fun yp ym h1 h2 => (hJ yp ym h1 h2).1
        lam_nonneg := zero_le_one
        lam_le_one := le_rfl
        cap := fun yp ym h1 h2 => (hJ yp ym (by simpa using h1) (by simpa using h2)).2 }
    let cpJ : CapPoint.{u} d p :=
      { V := cp.V, G := cp.G, S := cp.S.erase v, lam := 1, yp := yp', ym := ym', ctx := ctxJ,
        hyp := hc1, hym := hc2 }
    obtain ⟨hmp, hmm⟩ := cpJ.h_moment hR hiJ hk1 hk
    have e1 := SecA.coreE_eq_lawE_of_diagConj cp.G (p := p) hep hem hcp hcm
    refine ⟨?_, ?_⟩
    · show BiluLinial.Tight.coreE cp.G p (aOf d p) cp.yp cp.ym cp.S v _ ≤ _
      rw [e1]
      refine le_trans (SecA.lawE_le_of_supp cp.G
        (g := fun σ => hN cp.G (aOf d p) 1 yp' σ (cp.S.erase v) i ^ k) fun σ hσ => ?_) hmp
      have hP : (precN cp.G (aOf d p) 1 yp' σ (cp.S.erase v)).PosDef := by
        by_contra hc
        exact hσ (by simp [wt, hc])
      obtain ⟨h0, h1⟩ := SecA.diagConj_inv_apply_mem hep hP i
      rw [hcp 1 σ]
      exact pow_le_pow_left₀ h0 h1 k
    · show BiluLinial.Tight.coreE cp.G p (aOf d p) cp.yp cp.ym cp.S v _ ≤ _
      rw [e1]
      refine le_trans (SecA.lawE_le_of_supp cp.G
        (g := fun σ => hN cp.G (aOf d p) (-1) ym' σ (cp.S.erase v) i ^ k) fun σ hσ => ?_) hmm
      have hP : (precN cp.G (aOf d p) (-1) ym' σ (cp.S.erase v)).PosDef := by
        by_contra hc
        exact hσ (by simp [wt, hc])
      obtain ⟨h0, h1⟩ := SecA.diagConj_inv_apply_mem hem hP i
      rw [hcm (-1) σ]
      exact pow_le_pow_left₀ h0 h1 k
  · have hZc := cp.ZwCore_pos hR hv
    have mono : ∀ f : Config cp.V → ℝ,
        (∀ σ, wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v ≠ 0 → f σ ≤ (1 + 2 * epsP d p) ^ k) →
          cp.coreE v f ≤ (1 + 2 * epsP d p) ^ k := by
      intro f hf
      show (∑ σ, wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v * f σ) /
          ZwCore cp.G p (aOf d p) cp.yp cp.ym cp.S v ≤ _
      rw [div_le_iff₀ hZc, ZwCore, Finset.mul_sum]
      refine Finset.sum_le_sum fun σ _ => ?_
      by_cases hσ : wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v = 0
      · rw [hσ]
        simp
      · nlinarith [hf σ hσ, SecA.wtCore_nonneg cp.G p (aOf d p) cp.yp cp.ym σ cp.S v]
    refine ⟨mono _ fun σ hσ => ?_, mono _ fun σ hσ => ?_⟩
    · rw [SecA.precCore_inv_apply_of_not_mem cp.G (SecA.posDef_of_wtCore_ne_zero cp.G hσ).1 hiJ,
        one_pow]
      exact hone
    · rw [SecA.precCore_inv_apply_of_not_mem cp.G (SecA.posDef_of_wtCore_ne_zero cp.G hσ).2 hiJ,
        one_pow]
      exact hone

end CapPoint

end BiluLinial.Tight
