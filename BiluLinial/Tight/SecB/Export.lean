/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecB.WT
public import BiluLinial.Tight.SecB.RouteDR1
public import BiluLinial.Tight.SecA.Closure
public import BiluLinial.Tight.SecA.E1
public import BiluLinial.Tight.SecA.Reg

/-!
# Exports of Section B (source lines 626–1076) to Section 1.5

The inputs `in_S1`, `in_W5`, `in_W1` of `Tight/Contact/Inputs.lean` (nodes `I-S1`, `I-W5`, `I-W1`
of `docs/tight/BP_CONTACT.md`), restated **literally** under the namespace `SecB`, and the DR1
input of the GCI-free route (`in_DR1`, at every vertex), derived from the nodes of
`docs/tight/BP_SECB.md` (parent check). The contact layer (`Tight/Contact/InputsB.lean`) proves
its inputs by the corresponding `SecB.*` theorems.

* Bridges from Section A: `e1_bridge` (`CapPoint.endpoint_E1_cp` gives `E1Shape 4·10¹¹`),
  `cl1_bridge` (`SecA.scalar_ineq` gives `CL1Shape K 1 1`: the right side
  of `scalar_ineq` lacks the term `1/d ≥ 0` and has `b₀ = ε + p⁴/d + 1/d = bCL 1`) and `c2_bridge`
  (`SecA.concentration_C2` gives `C2RowShape K`, since `(p/d)^{1/3} ≤ δ̄`).
* `SecB.in_S1` ← `mean_shift_of_cl1`, `cl1_bridge` (`C = K_S + 1`).
* `SecB.in_W5 m` ← `ward_mean_of_cl1`, `cl1_bridge`.
* `SecB.in_W1` ← `weak_loop_of`, `cl1_bridge`, `c2_bridge`.
* `SecB.in_DR1` ← `dr1_of_c2`, `e1_bridge`, `c2_bridge` (`C = K_DR + 1`).
-/

@[expose] public section

namespace BiluLinial.Tight.SecB

open Matrix

universe u

/-- Bridge: the endpoint calculus of Section A (`CapPoint.endpoint_E1_cp`) in the form `E1Shape`. -/
theorem e1_bridge : E1Shape.{u} 4e11 := by
  refine SecA.eventually_regA.mono ?_
  intro c₀ κ₀ d p h hR cp v hv i hi
  exact cp.endpoint_E1_cp hR hv hi

/-- Bridge: the closure inequality of Section A (`SecA.scalar_ineq`) in the form `CL1Shape`. -/
theorem cl1_bridge : ∃ K : ℝ, 0 ≤ K ∧ CL1Shape.{u} K 1 1 := by
  obtain ⟨C, hC, hsc⟩ := SecA.scalar_ineq.{u}
  refine ⟨C, hC.le, SecA.eventually_regA.mono ?_⟩
  intro c₀ κ₀ d p h hR cp z θ hz1 hz2 hθ
  have hd0 : (0 : ℝ) < d := hR.d_pos
  have hz0 : 0 < z := lt_of_lt_of_le (by positivity) hz1
  have hdz : 1 ≤ (d : ℝ) * z := by
    rw [div_le_iff₀ hd0] at hz1; linarith
  refine le_trans (hsc d p hR cp z hz0 hdz θ hθ) ?_
  have hb : bCL 1 d p = b0Of d p := by simp [bCL, b0Of]
  rw [cl1Rhs, hb, one_mul]
  apply mul_le_mul_of_nonneg_left _ hC.le
  have : 0 ≤ 1 / (d : ℝ) := by positivity
  linarith

/-- Bridge: the concentration bounds of Section A (`SecA.concentration_C2`) in the form
`C2RowShape`. -/
theorem c2_bridge : ∃ Kδ : ℝ, 0 ≤ Kδ ∧ C2RowShape.{u} Kδ := by
  obtain ⟨C, hC, hc2⟩ := SecA.concentration_C2.{u}
  refine ⟨C, hC.le, SecA.eventually_regA.mono ?_⟩
  intro c₀ κ₀ d p h hR cp w hw
  obtain ⟨h1, h2⟩ := hc2 d p hR cp
  have hu : uOf d p ≤ dbar d p := by
    have h3 := regime_eps_nonneg hR.treg
    have h4 : 0 ≤ (p : ℝ) ^ 4 / d := by positivity
    rw [dbar, uOf]
    linarith
  have hCu : C * uOf d p ≤ C * dbar d p := mul_le_mul_of_nonneg_left hu hC.le
  obtain ⟨-, -, a1, a2⟩ := h1 w hw
  obtain ⟨b1, b2, -⟩ := h2 w hw
  exact ⟨a1.trans hCu, a2.trans hCu, b1.trans hCu, b2.trans hCu⟩

/-- Export for **I-S1** (`in_S1`). -/
theorem in_S1 : ∃ C : ℝ, 0 < C ∧ Eventually fun _c₀ _κ₀ d p h =>
    ∀ ct : Contact.{u} d p, ∀ i ∈ ct.S,
      (0 ≤ ct.E (fun σ => ct.gp σ i i - ct.XP h σ i i) ∧
        ct.E (fun σ => ct.gp σ i i - ct.XP h σ i i) ≤ C * Real.sqrt h * ct.yp i) ∧
      (0 ≤ ct.E (fun σ => ct.gm σ i i - ct.XM h σ i i) ∧
        ct.E (fun σ => ct.gm σ i i - ct.XM h σ i i) ≤ C * Real.sqrt h * ct.ym i) := by
  obtain ⟨K, hK, hCL⟩ := cl1_bridge.{u}
  refine ⟨s1K K + 1, by linarith [one_le_s1K hK],
    (mean_shift_of_cl1 hK zero_le_one one_pos hCL).mono ?_⟩
  intro c₀ κ₀ d p h hS ct i hi
  obtain ⟨-, hS1⟩ := hS ct.toCapPoint
  obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ := hS1 i hi
  have eP : ct.E (fun σ => ct.gp σ i i - ct.XP h σ i i) =
      lawE ct.G p (aOf d p) ct.yp ct.ym ct.S
          (fun σ => greenP ct.G (aOf d p) 1 ct.yp σ ct.S i i) -
        lawE ct.G p (aOf d p) ct.yp ct.ym ct.S
          (fun σ => shiftP ct.G (aOf d p) 1 h ct.yp σ ct.S i i) :=
    lawE_sub ct.G _ _
  have eM : ct.E (fun σ => ct.gm σ i i - ct.XM h σ i i) =
      lawE ct.G p (aOf d p) ct.yp ct.ym ct.S
          (fun σ => greenP ct.G (aOf d p) (-1) ct.ym σ ct.S i i) -
        lawE ct.G p (aOf d p) ct.yp ct.ym ct.S
          (fun σ => shiftP ct.G (aOf d p) (-1) h ct.ym σ ct.S i i) :=
    lawE_sub ct.G _ _
  rw [eP, eM]
  exact ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩

/-- Export for **I-W5** (`in_W5`). -/
theorem in_W5 (m : ℕ) : ∃ C : ℝ, 0 < C ∧ Eventually fun _c₀ _κ₀ d p h =>
    ∀ ct : Contact.{u} d p, ∀ i ∈ ct.S,
      ct.E (fun σ => ct.Dstar σ ^ m * (ct.XP h σ * ct.XP h σ) i i) ≤ C / Real.sqrt h ∧
      ct.E (fun σ => ct.Dstar σ ^ m * (ct.XM h σ * ct.XM h σ) i i) ≤ C / Real.sqrt h := by
  obtain ⟨K, hK, hCL⟩ := cl1_bridge.{u}
  exact ward_mean_of_cl1 m hK zero_le_one one_pos hCL

/-- Export for **I-W1** (`in_W1`). -/
theorem in_W1 : ∃ C : ℝ, 0 < C ∧ Eventually fun _c₀ _κ₀ d p h =>
    ∀ ct : Contact.{u} d p,
      |ct.qP h - ct.zeta h - ct.tP h| ≤
          C * ct.score ct.OmP ct.dOmP (ct.XP h) (ct.XP h) (fun _ => ct.uvec) + C * B0P d p h ∧
      |ct.zeta h - ct.zP h - ct.alphaE h| ≤
          C * ct.score ct.OmP ct.dOmP (ct.XP h) (ct.XP h) (ct.bP h) + C * B0P d p h ∧
      |ct.qM h + ct.zetaM h - ct.tM h| ≤
          C * ct.score ct.OmM ct.dOmM (ct.XM h) (ct.XP h) (fun _ => ct.uvec) + C * B0P d p h ∧
      |ct.zetaM h + ct.zM h - ct.betaE h| ≤
          C * ct.score ct.OmM ct.dOmM (ct.XM h) (ct.XP h) (ct.bM h) + C * B0P d p h := by
  obtain ⟨K, hK, hCL⟩ := cl1_bridge.{u}
  obtain ⟨Kδ, hKδ, hC2⟩ := c2_bridge.{u}
  exact weak_loop_of hK zero_le_one one_pos hKδ hCL hC2

/-- Export for the DR1 input of the GCI-free route (`in_DR1`, DR1_CHECK §2): at every vertex
`w ∈ S` of a contact, `a² Σ_{i ∈ N_S(w)} E(G⁺_wi - G⁻_wi)² ≤ C δ̄ / p`. -/
theorem in_DR1 : ∃ C : ℝ, 0 < C ∧ Eventually fun _c₀ _κ₀ d p _h =>
    ∀ ct : Contact.{u} d p, ∀ w ∈ ct.S,
      aOf d p ^ 2 * ∑ i ∈ nbhd ct.G ct.S w, ct.E (fun σ => (ct.gp σ w i - ct.gm σ w i) ^ 2) ≤
        C * dbar d p / p := by
  obtain ⟨Kδ, hKδ, hC2⟩ := c2_bridge.{u}
  obtain ⟨K, hK, hDR⟩ := dr1_of_c2 (by norm_num) e1_bridge.{u} hKδ hC2
  refine ⟨K + 1, by linarith, (hDR.and (eventually_base 0)).mono ?_⟩
  rintro c₀ κ₀ d p h ⟨hdr, hR, -⟩ ct w hw
  have key := hdr ct.toCapPoint w hw
  have hdb : 0 ≤ dbar d p := le_trans (regime_eps_nonneg hR) (le_dbar hR).1
  have hp := regime_p_pos hR
  refine le_trans key ?_
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hdb) hp.le

end BiluLinial.Tight.SecB
