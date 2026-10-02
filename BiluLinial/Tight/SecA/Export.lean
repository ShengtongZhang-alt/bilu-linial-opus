/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecA.Closure
public import BiluLinial.Tight.SecA.E1

/-!
# Exports of Section 1.2 to Section 1.5

The inputs `in_E1`, `in_C2`, `in_C1`, `in_whiten`, `in_C3a` of `Tight/Contact/Inputs.lean`
(nodes `I-E1`, `I-C2`, `I-C1`, `I-whiten`, `I-C3a` of `docs/tight/BP_CONTACT.md`), restated
**literally** under the namespace `SecA` and derived from the nodes of `docs/tight/BP_SECA.md`
(parent check). The contact layer (`Tight/Contact/InputsA.lean`) proves its inputs by the
corresponding `SecA.*` theorems.

* `SecA.in_E1` ← `CapPoint.endpoint_E1_cp` (`C = 4·10¹¹`).
* `SecA.in_C2` ← `concentration_C2` (`(p/d)^{1/3} ≤ δ̄`, `tr A² ≤ Θ`).
* `SecA.in_C1` ← T.COV (`gaussE_NG_nonneg`), T.GIBP2 (`two_mul_gaussE_starF`), `A-ROOTPSD`.
* `SecA.in_whiten` ← `whiten`, T.GIBP2 (`E_{ν_K} N_G / F_H = 2 a² Gterm`).
* `SecA.in_C3a` ← `trace_sq_le_two_wK`, `core_tail` (`e^{-p/10} ≤ d^{-10}`).

The regime is supplied by `eventually_regA`.
-/

@[expose] public section

universe u

namespace BiluLinial.Tight

open Matrix

namespace SecA

/-- Export for **I-E1** (`in_E1`). -/
theorem in_E1 : ∃ C : ℝ, 0 < C ∧ Eventually fun _c₀ _κ₀ d p _h =>
    ∀ ct : Contact.{u} d p, ∀ i ∈ ct.N,
      |ct.sx i - aOf d p * (-(ct.E fun σ => ct.gp σ ct.v ct.v * ct.gp σ i i) +
          (2 * (p : ℝ) - 1) * (ct.E fun σ => ct.x σ i ^ 2) -
          2 * (p : ℝ) * (ct.E fun σ => ct.x σ i * ct.z σ i)) +
        aOf d p ^ 3 / 3 * (ct.E fun σ => Kpoly p (ct.x σ i) (ct.z σ i)
          (ct.gp σ ct.v ct.v * ct.gp σ i i) (ct.gm σ ct.v ct.v * ct.gm σ i i))| ≤
        C * (p : ℝ) ^ 5 * aOf d p ^ 5 := by
  refine ⟨4e11, by norm_num, eventually_regA.mono fun _ _ d p _ hR ct i hi => ?_⟩
  exact CapPoint.endpoint_E1_cp ct.toCapPoint hR ct.ctx.mem hi

/-- Export for **I-C2** (`in_C2`). -/
theorem in_C2 : ∃ C : ℝ, 0 < C ∧ Eventually fun _c₀ _κ₀ d p _h =>
    ∀ ct : Contact.{u} d p,
      aOf d p ^ 2 * ct.Srow ≤ C * dbar d p ∧ aOf d p ^ 2 * ct.Smin ≤ C * dbar d p ∧
        ct.trA2 ≤ C * dbar d p ∧ ct.trB2 ≤ C * dbar d p := by
  obtain ⟨C, hC, h⟩ := concentration_C2.{u}
  refine ⟨C, hC, eventually_regA.mono fun _ _ d p _ hR ct => ?_⟩
  have hv : ct.v ∈ ct.S := ct.ctx.mem
  obtain ⟨-, h2⟩ := h d p hR ct.toCapPoint
  obtain ⟨r1, r2, t⟩ := h2 ct.v hv
  have hud : C * uOf d p ≤ C * dbar d p := by
    refine mul_le_mul_of_nonneg_left ?_ hC.le
    have h1 := epsP_nonneg hR.treg
    have h2 : 0 ≤ (p : ℝ) ^ 4 / d := by positivity
    rw [dbar, uOf]
    linarith
  have hA : ct.trA2 ≤ ct.toCapPoint.E (fun σ => ct.toCapPoint.Theta σ ct.v) := by
    refine lawE_le_of_supp ct.G fun σ hσ => ?_
    have hB := (ct.toCapPoint.root_psd hR hv hσ).2
    have := trace_mul_nonneg hB hB
    dsimp only [CapPoint.Theta]
    rw [Matrix.trace_add]
    change (ct.Amat σ * ct.Amat σ).trace ≤ (ct.Amat σ * ct.Amat σ).trace +
      (ct.toCapPoint.B σ ct.v * ct.toCapPoint.B σ ct.v).trace
    linarith
  have hB : ct.trB2 ≤ ct.toCapPoint.E (fun σ => ct.toCapPoint.Theta σ ct.v) := by
    refine lawE_le_of_supp ct.G fun σ hσ => ?_
    have hA := (ct.toCapPoint.root_psd hR hv hσ).1
    have := trace_mul_nonneg hA hA
    dsimp only [CapPoint.Theta]
    rw [Matrix.trace_add]
    change (ct.Bmat σ * ct.Bmat σ).trace ≤
      (ct.toCapPoint.A σ ct.v * ct.toCapPoint.A σ ct.v).trace + (ct.Bmat σ * ct.Bmat σ).trace
    linarith
  exact ⟨r1.trans hud, r2.trans hud, hA.trans (t.trans hud), hB.trans (t.trans hud)⟩

/-- Export for **I-C1** (`in_C1`). -/
theorem in_C1 : Eventually fun _c₀ _κ₀ d p _h => ∀ ct : Contact.{u} d p, 0 ≤ ct.Gterm := by
  refine eventually_regA.mono fun _ _ d p _ hR ct => ?_
  have hp3 : 3 ≤ p := le_trans (by norm_num) hR.treg.hp
  unfold Contact.Gterm
  refine div_nonneg (coreE_nonneg_of_supp ct.G fun σ hσ => ?_)
    (mul_nonneg (sq_nonneg _) (coreE_nonneg_of_supp ct.G fun σ _ => radE_starPhi_nonneg _ _ _))
  obtain ⟨hA, hB⟩ := ct.toCapPoint.root_psd_core hσ
  exact gaussE_rowNum_nonneg hA hB hp3

/-- Export for **I-whiten** (`in_whiten`). -/
theorem in_whiten : ∃ C : ℝ, 0 < C ∧ Eventually fun _c₀ _κ₀ d p _h =>
    ∀ ct : Contact.{u} d p,
      ct.wker ≤ 2 * aOf d p ^ 2 * ct.Gterm + C * ((p : ℝ) ^ 4 / d) * (ct.wker + vth d) := by
  obtain ⟨C, hC, h⟩ := whiten.{u}
  refine ⟨C, hC, eventually_regA.mono fun _ _ d p _ hR ct => ?_⟩
  have hp3 : 3 ≤ p := le_trans (by norm_num) hR.treg.hp
  obtain ⟨h1, -⟩ := h d p hR ct.toCapPoint ct.v ct.ctx.mem
  have hc : ct.toCapPoint.coreE ct.v
      (fun σ => gaussE (f1Obs p (ct.toCapPoint.A σ ct.v) (ct.toCapPoint.B σ ct.v))) =
      2 * coreE ct.G p (aOf d p) ct.yp ct.ym ct.S ct.v
        (fun σ => gaussE (rowNum p (ct.Amat σ) (ct.Bmat σ))) := by
    rw [← coreE_const_mul']
    refine coreE_congr_of_supp ct.G fun σ hσ => ?_
    obtain ⟨hA, hB⟩ := ct.toCapPoint.root_psd_core hσ
    exact gaussE_f1Obs_eq hA hB hp3
  have ha : aOf d p ≠ 0 := hR.treg.aOf_pos.ne'
  have heq : ct.toCapPoint.coreE ct.v
      (fun σ => gaussE (f1Obs p (ct.toCapPoint.A σ ct.v) (ct.toCapPoint.B σ ct.v))) /
        ct.toCapPoint.FH ct.v = 2 * aOf d p ^ 2 * ct.Gterm := by
    rw [hc]
    unfold Contact.Gterm
    change 2 * _ / coreE ct.G p (aOf d p) ct.yp ct.ym ct.S ct.v
      (fun σ => radE (starPhi p (ct.Amat σ) (ct.Bmat σ))) = _
    by_cases hF : coreE ct.G p (aOf d p) ct.yp ct.ym ct.S ct.v
      (fun σ => radE (starPhi p (ct.Amat σ) (ct.Bmat σ))) = 0
    · rw [hF]; simp
    · field_simp
  rw [heq] at h1
  exact h1

/-- Export for **I-C3a** (`in_C3a`). -/
theorem in_C3a : ∃ C : ℝ, 0 < C ∧ Eventually fun _c₀ _κ₀ d p _h =>
    ∀ ct : Contact.{u} d p, ct.trA2 ≤ 2 * ct.wker + C * vth d := by
  refine ⟨1, one_pos, eventually_regA.mono fun _ _ d p _ hR ct => ?_⟩
  have hv : ct.v ∈ ct.S := ct.ctx.mem
  obtain ⟨t1, -⟩ := core_tail hR ct.toCapPoint hv
  have h1 : ct.trA2 ≤ ct.toCapPoint.E (fun σ => 2 * wK (ct.toCapPoint.A σ ct.v) +
      if 1 < (ct.toCapPoint.A σ ct.v).trace then
        (ct.toCapPoint.A σ ct.v * ct.toCapPoint.A σ ct.v).trace else 0) := by
    refine lawE_le_of_supp ct.G fun σ hσ => ?_
    have hA := (ct.toCapPoint.root_psd hR hv hσ).1
    change (ct.toCapPoint.A σ ct.v * ct.toCapPoint.A σ ct.v).trace ≤ _
    have hT := trace_mul_nonneg hA hA
    have hμ := hA.trace_nonneg
    have hw : 0 ≤ wK (ct.toCapPoint.A σ ct.v) := div_nonneg hT (by linarith)
    split_ifs with h
    · linarith
    · have := trace_sq_le_two_wK hA (not_lt.1 h)
      linarith
  have e : ct.toCapPoint.E (fun σ => 2 * wK (ct.toCapPoint.A σ ct.v) +
      if 1 < (ct.toCapPoint.A σ ct.v).trace then
        (ct.toCapPoint.A σ ct.v * ct.toCapPoint.A σ ct.v).trace else 0) =
      2 * ct.wker + ct.toCapPoint.E (fun σ =>
        if 1 < (ct.toCapPoint.A σ ct.v).trace then
          (ct.toCapPoint.A σ ct.v * ct.toCapPoint.A σ ct.v).trace else 0) := by
    unfold CapPoint.E
    rw [lawE_add, lawE_const_mul]
    rfl
  have hx := RegA.exp_neg_p_div_ten_le hR
  rw [e] at h1
  linarith

end SecA

end BiluLinial.Tight
