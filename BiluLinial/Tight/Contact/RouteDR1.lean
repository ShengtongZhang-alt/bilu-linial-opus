/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.Contact.Inputs
public import BiluLinial.Tight.Contact.Real
public import BiluLinial.Tight.Contact.RouteReal
public import BiluLinial.Tight.SourceMax.Law
public import BiluLinial.Tight.SecB.Export
public import BiluLinial.Tight.SecC.RowCompare

/-!
# Route-dependent inputs, GCI-free route (DR1)

Blueprint `docs/tight/BP_CONTACT.md`, "Route-dependent nodes". This file and
`Tight/Contact/RouteDR1D9a.lean` are the active route of the contact chain: the GCI-free route of
AUDIT-B §3.3, confirmed in `docs/tight/DR1_CHECK.md`, with the statements proposed in
`docs/tight/CHECK_CONTACT.md` ("DR1-route replacements"). They export the route-independent
statements `cr1` (here) and `d9a` (`RouteDR1D9a.lean`). The paper's route (GR1, through Royen's
Gaussian correlation inequality) is not formalized (see `FORMALIZATION.md`, Part D, "Proof
route").

Inputs of this file:
* `in_C2_all` — (C2) at **every** vertex of `S` (the source's (C2) is a supremum over vertices); it
  is needed by DR1 at the neighbours of the root (and, inside the proofs of the leaves FS5 and the
  input W1, by the remainder `ρ_row`). Supplied by `SecA.concentration_C2`.
* `in_DR1_of_C2` — DR1 from the all-vertex (C2): `SecB.dr1_of_c2`.
* `in_CR3'` — the row comparison with the difference row mass (CR3′): `SecC.row_comparison_diff`.
-/

@[expose] public section

namespace BiluLinial.Tight

open Matrix

universe u

/-- The all-vertex concentration shape with constant `Kδ` (source (C2), l.378–385, as a supremum
over the vertices `w ∈ S`; the form of `SecB.C2RowShape`): mean deficits `1 - E h^±_w ≤ Kδ δ̄` and
row masses `a² Σ_{j ∼ w} E(G^±_wj)² ≤ Kδ δ̄`. -/
def C2All (Kδ : ℝ) : Prop :=
  Eventually fun _c₀ _κ₀ d p _h => ∀ ct : Contact.{u} d p, ∀ w ∈ ct.S,
    1 - ct.mp w ≤ Kδ * dbar d p ∧
    1 - meanMinus ct.G d p ct.yp ct.ym ct.S w ≤ Kδ * dbar d p ∧
    aOf d p ^ 2 * ∑ j ∈ nbhd ct.G ct.S w, ct.E (fun σ => ct.gp σ w j ^ 2) ≤ Kδ * dbar d p ∧
    aOf d p ^ 2 * ∑ j ∈ nbhd ct.G ct.S w, ct.E (fun σ => ct.gm σ w j ^ 2) ≤ Kδ * dbar d p

/-- **I-C2all** [route DR1] (source (C2), l.378–385, at every vertex; AUDIT-A §2.15, AUDIT-B §2.1;
CHECK_CONTACT (N1)). Supplied by `SecA.concentration_C2` (with `uOf ≤ δ̄`). -/
theorem in_C2_all : ∃ Kδ : ℝ, 0 < Kδ ∧ C2All.{u} Kδ := by
  obtain ⟨C, hC, hc2⟩ := SecA.concentration_C2.{u}
  refine ⟨C, hC, SecA.eventually_regA.mono ?_⟩
  intro c₀ κ₀ d p h hR ct w hw
  obtain ⟨h1, h2⟩ := hc2 d p hR ct.toCapPoint
  have hu : uOf d p ≤ dbar d p := by
    have h3 := SecB.regime_eps_nonneg hR.treg
    have h4 : 0 ≤ (p : ℝ) ^ 4 / d := by positivity
    rw [dbar, uOf]
    linarith
  have hCu : C * uOf d p ≤ C * dbar d p := mul_le_mul_of_nonneg_left hu hC.le
  obtain ⟨-, -, a1, a2⟩ := h1 w hw
  obtain ⟨b1, b2, -⟩ := h2 w hw
  exact ⟨a1.trans hCu, a2.trans hCu, b1.trans hCu, b2.trans hCu⟩

/-- **I-DR1c** [route DR1] (DR1_CHECK §2: the two exact root-row equations, the first-order
endpoint identity, the moment caps and (C2); no sign of `T_v`, hence no GCI). Given the
all-vertex (C2), the branch-difference row energy at every vertex is `O(δ̄/p)`. Supplied by
`SecB.dr1_of_c2`. -/
theorem in_DR1_of_C2 (Kδ : ℝ) (hKδ : 0 ≤ Kδ) (hC2 : C2All.{u} Kδ) :
    ∃ C : ℝ, 0 < C ∧ Eventually fun _c₀ _κ₀ d p _h =>
      ∀ ct : Contact.{u} d p, ∀ w ∈ ct.S,
        aOf d p ^ 2 * ∑ j ∈ nbhd ct.G ct.S w,
          ct.E (fun σ => (ct.gp σ w j - ct.gm σ w j) ^ 2) ≤ C * dbar d p / p := by
  obtain ⟨K₃, hK₃, hRE⟩ := SecB.row_eq_of (by norm_num) SecB.e1_bridge.{u}
  refine ⟨602 / 100 * Kδ + 814 / 100 + 2 * K₃ + 1, by positivity,
    ((hRE.and hC2).and (SecB.eventually_base 0)).mono ?_⟩
  rintro c₀ κ₀ d p h ⟨⟨hre, hc2⟩, hR, -⟩ ct w hw
  obtain ⟨hmP, hmM, hSP, hSM⟩ := hc2 ct w hw
  obtain ⟨hEP, hEM⟩ := hre ct.toCapPoint w hw
  have hdb0 : 0 ≤ dbar d p := le_trans (SecB.regime_eps_nonneg hR) (SecB.le_dbar hR).1
  have hδ : 0 ≤ Kδ * dbar d p := mul_nonneg hKδ hdb0
  have key := SecB.dr1_pt ct.G hR ct.ctx.toCapPt hw hδ hmP hmM hSP hSM hEP hEM
  have hp := SecB.regime_p_pos hR
  have hp1 : (1 : ℝ) ≤ p := by have := hR.two_le_p; exact_mod_cast le_trans (by norm_num) this
  have hd0 : (0 : ℝ) < d := by have := hR.ten_pow_six_le_d; linarith
  obtain ⟨hεd, hpd⟩ := SecB.le_dbar hR
  have h1d : 1 / (d : ℝ) ≤ dbar d p := by
    refine le_trans ?_ hpd
    exact div_le_div_of_nonneg_right (one_le_pow₀ hp1) hd0.le
  have hp3 : (p : ℝ) ^ 3 / d ≤ dbar d p := by
    refine le_trans ?_ hpd
    exact div_le_div_of_nonneg_right (pow_le_pow_right₀ hp1 (by norm_num)) hd0.le
  have hX : 2 * (201 / 100 * (Kδ * dbar d p) + 104 / (100 * d) + 303 / 100 * epsP d p) +
      2 * (K₃ * (p : ℝ) ^ 3 / d) + 2 * (Kδ * dbar d p) ≤
      (602 / 100 * Kδ + 814 / 100 + 2 * K₃) * dbar d p := by
    have e1 : 104 / (100 * (d : ℝ)) = 104 / 100 * (1 / d) := by field_simp
    have e2 : K₃ * (p : ℝ) ^ 3 / d = K₃ * ((p : ℝ) ^ 3 / d) := by ring
    rw [e1, e2]
    nlinarith [mul_le_mul_of_nonneg_left hp3 hK₃]
  have hD0 := SecB.rowDiff_nonneg ct.G (d := d) (p := p) ct.yp ct.ym ct.S w
  have hl : (p : ℝ) * (aOf d p ^ 2 * rowDiff ct.G d p ct.yp ct.ym ct.S w) ≤
      (2 * p - 1) * (aOf d p ^ 2 * rowDiff ct.G d p ct.yp ct.ym ct.S w) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  change aOf d p ^ 2 * rowDiff ct.G d p ct.yp ct.ym ct.S w ≤ _
  rw [le_div_iff₀ hp]
  linarith

/-- **N-DR1** [route DR1] (DR1_CHECK §2). `a² Σ_{j ∼ w} E(G⁺_wj - G⁻_wj)² ≤ C δ̄/p` for every
`w ∈ S`. Proved from `in_C2_all` and `in_DR1_of_C2`. -/
theorem in_DR1 : ∃ C : ℝ, 0 < C ∧ Eventually fun _c₀ _κ₀ d p _h =>
    ∀ ct : Contact.{u} d p, ∀ w ∈ ct.S,
      aOf d p ^ 2 * ∑ j ∈ nbhd ct.G ct.S w,
        ct.E (fun σ => (ct.gp σ w j - ct.gm σ w j) ^ 2) ≤ C * dbar d p / p := by
  obtain ⟨Kδ, hKδ, hC2⟩ := in_C2_all.{u}
  exact in_DR1_of_C2 Kδ hKδ.le hC2

/-- **I-CR3′** [route DR1] (source "Separating incident-row and core marks", (CR3), l.1170–1190,
with the row observable written `𝓡_v = pΣ_j x_j(x_j - z_j) - Σ_j x_j²` (AUDIT-B B-4,
DR1_CHECK §3): the term `Φ⁽⁴⁾𝓡_v` costs `p⁵√(λ_r δ_Δ) + p⁴λ_r`, and `p⁴λ_r ≤ p⁴√(λ_c δ_c)` by the
ordering). For `ϑ ≤ λ_r ≤ λ_c ≤ δ_c ≤ 1`, `ϑ ≤ ρ_Δ`, `S₊/d ≤ λ_r`, `S₋/d ≤ δ_c`,
`d⁻¹ Σ_N E(x_j - z_j)² ≤ ρ_Δ` and the marked core envelopes `λ_c`, `δ_c`:
`|𝓡 - Gterm| ≤ C(p⁵√(λ_r ρ_Δ) + p⁴√(λ_c δ_c) + p¹³/d²) + C ϑ`. Supplied by
`SecC.row_comparison_diff`. -/
theorem in_CR3' : ∃ C : ℝ, 0 < C ∧ Eventually fun _c₀ _κ₀ d p _h =>
    ∀ ct : Contact.{u} d p, ∀ lr rd lc dc : ℝ, vth d ≤ lr → lr ≤ lc → lc ≤ dc → dc ≤ 1 →
      vth d ≤ rd → ct.Srow / d ≤ lr → ct.Smin / d ≤ dc →
      (∑ j ∈ ct.N, ct.E (fun σ => (ct.x σ j - ct.z σ j) ^ 2)) / d ≤ rd →
      ct.frobP / (d : ℝ) ^ 2 ≤ lc → ct.frobM / (d : ℝ) ^ 2 ≤ dc →
      |ct.Rrow - ct.Gterm| ≤ C * ((p : ℝ) ^ 5 * Real.sqrt (lr * rd) +
        (p : ℝ) ^ 4 * Real.sqrt (lc * dc) + (p : ℝ) ^ 13 / (d : ℝ) ^ 2) + C * vth d := by
  obtain ⟨C, hC, h3⟩ := SecC.row_comparison_diff.{u}
  refine ⟨max C 1, lt_of_lt_of_le one_pos (le_max_right _ _),
    (h3.and SecC.eventually_exp_le_vth).mono ?_⟩
  rintro c₀ κ₀ d p h ⟨H, -, he3⟩ ct lr rd lc dc h1 h2 h3' - h5 h6 h7 h8 h9 h10
  have hc := ct.ctx
  have key := H ct.V ct.G ct.S ct.lam ct.yp ct.ym ct.v hc.toCapCtx hc.hyp hc.hym hc.mem lr rd lc
    dc h1 h2 h3' h5 h6 h7 h8 h9 h10
  change |rowMean ct.G d p ct.yp ct.ym ct.S ct.v - rowGauss ct.G d p ct.yp ct.ym ct.S ct.v| ≤ _
  have hX : 0 ≤ (p : ℝ) ^ 5 * Real.sqrt (lr * rd) + (p : ℝ) ^ 4 * Real.sqrt (lc * dc) +
      (p : ℝ) ^ 13 / (d : ℝ) ^ 2 := by positivity
  have hθ0 : 0 ≤ vth d := by unfold vth; positivity
  have e1 := mul_le_mul_of_nonneg_right (le_max_left C 1) hX
  have e2 := mul_le_mul_of_nonneg_right (le_max_right C 1) hθ0
  linarith

namespace Contact

variable {d p : ℕ} (ct : Contact.{u} d p)

/-- `Σ_N E(x_j - z_j)² ≥ 0`. -/
theorem rowDiff_nonneg : 0 ≤ ∑ j ∈ ct.N, ct.E (fun σ => (ct.x σ j - ct.z σ j) ^ 2) :=
  Finset.sum_nonneg fun _ _ => lawE_nonneg ct.G fun _ _ => sq_nonneg _

end Contact

/-- **CR1** (source Lemma "Contact row comparison", (CR1), l.1078–1100; AUDIT-C §4.2, G4: the
floor `λ ≥ ϑ` is explicit and the contact hypothesis is unused). For every envelope `λ` of the plus
row and core masses with `ϑ ≤ λ ≤ M δ̄`: `|𝓡 - Gterm| ≤ C(M)(p⁵√(λ δ̄) + p¹³/d² + ϑ)`.
Route-independent statement; here proved from CR3′, DR1 (at the root), MARKENV and C2. -/
theorem cr1 (M : ℝ) : ∃ C : ℝ, 0 < C ∧ Eventually fun _c₀ _κ₀ d p _h =>
    ∀ ct : Contact.{u} d p, ∀ lam : ℝ, aOf d p ^ 2 * ct.Srow + ct.trA2 ≤ lam → vth d ≤ lam →
      lam ≤ M * dbar d p →
      |ct.Rrow - ct.Gterm| ≤ C * ((p : ℝ) ^ 5 * Real.sqrt (lam * dbar d p) +
        (p : ℝ) ^ 13 / (d : ℝ) ^ 2 + vth d) := by
  obtain ⟨CC, -, hCR3⟩ := in_CR3'.{u}
  obtain ⟨CM, -, hME⟩ := in_markenv.{u}
  obtain ⟨C₂, -, hC2⟩ := in_C2.{u}
  obtain ⟨CD, -, hDR⟩ := in_DR1.{u}
  obtain ⟨C, hC, P₀, hreal⟩ := cr1_real_dr1 CC CM C₂ CD M
  refine ⟨C, hC, ((((hCR3.and hME).and hC2).and hDR).and (eventually_treg_ge P₀)).mono ?_⟩
  rintro c₀ κ₀ d p h ⟨⟨⟨⟨H3, HM⟩, H2⟩, HD⟩, hR, hp⟩ ct lam hl1 hl2 hl3
  exact hreal d p hR hp ct.Srow ct.Smin ct.trA2 ct.trB2 ct.frobP ct.frobM
    (∑ j ∈ ct.N, ct.E (fun σ => (ct.x σ j - ct.z σ j) ^ 2)) ct.Rrow ct.Gterm lam
    (HM ct).1 (HM ct).2 (H2 ct).2.1 (H2 ct).2.2.2 ct.rowDiff_nonneg (HD ct ct.v ct.ctx.mem)
    (H3 ct) hl1 hl2 hl3

end BiluLinial.Tight
