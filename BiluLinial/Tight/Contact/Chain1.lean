/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.Contact.RouteDR1
public import BiluLinial.Tight.Contact.LeavesX
public import BiluLinial.Tight.SourceMax

/-!
# The contact chain, part 1: exact loop and bootstrap (D3)–(D7)

Blueprint `docs/tight/BP_CONTACT.md`, nodes `N-LOOP`, `N-F3sum`, `N-D3`, `N-D4`, `N-D6`, `N-D7`
(source l.1370–1500; AUDIT-C §6, AUDIT-D §3.1). Every node is proved from the statements of its
children (inputs `I-*`, leaves `L-*`, real lemmas `R-*`, and the corollary `cr1`).
-/

@[expose] public section

namespace BiluLinial.Tight

open Matrix

universe u

variable {d p : ℕ}

/-! ### Helpers (proved) -/

namespace Contact

variable (ct : Contact.{u} d p)

theorem yp_nonneg (i : ct.V) : 0 ≤ ct.yp i := (ct.ctx.hyp i).1

/-- `E G⁺_ii = y⁺_i E h⁺_i`. -/
theorem E_gp_diag (i : ct.V) : ct.E (fun σ => ct.gp σ i i) = ct.yp i * ct.mp i := by
  have h : ∀ σ, ct.gp σ i i = ct.yp i * hN ct.G (aOf d p) 1 ct.yp σ ct.S i := by
    intro σ
    unfold gp greenP hN
    have := Real.mul_self_sqrt (ct.yp_nonneg i)
    calc Real.sqrt (ct.yp i) * (precN ct.G (aOf d p) 1 ct.yp σ ct.S)⁻¹ i i *
          Real.sqrt (ct.yp i)
        = (Real.sqrt (ct.yp i) * Real.sqrt (ct.yp i)) *
            (precN ct.G (aOf d p) 1 ct.yp σ ct.S)⁻¹ i i := by ring
      _ = _ := by rw [this]
  unfold E mp meanPlus
  simp only [h]
  exact lawE_const_mul _ _ _

theorem mp_root : ct.mp ct.v = rOf d p := ct.ctx.contact

/-- At the contact, `E G⁺_vv = y⁺_v r`. -/
theorem E_gp_root : ct.E (fun σ => ct.gp σ ct.v ct.v) = ct.yp ct.v * rOf d p := by
  rw [E_gp_diag, mp_root]

theorem mem_S_of_mem_N {i : ct.V} (hi : i ∈ ct.N) : i ∈ ct.S := (Finset.mem_filter.1 hi).1

end Contact

/-! ### The corrected loop and (D3) -/

/-- **N-LOOP** (source l.1394–1400; AUDIT-C §6 LOOP, AUDIT-D §3.1 D3). The root equation and (E1)
at every neighbour give
`D₊ r = 1 + a² Σ_N E P_i - (2p-1) a² S + 2p a² T + Q_* + O(p⁵/d²)`. -/
theorem loop : ∃ C : ℝ, 0 < C ∧ Eventually fun _c₀ _κ₀ d p _h =>
    ∀ ct : Contact.{u} d p,
      |ct.Dplus * rOf d p - (1 + aOf d p ^ 2 * ct.sumP -
          (2 * (p : ℝ) - 1) * aOf d p ^ 2 * ct.Srow + 2 * (p : ℝ) * aOf d p ^ 2 * ct.Tmix +
          ct.Qstar)| ≤ C * (p : ℝ) ^ 5 / (d : ℝ) ^ 2 := by
  obtain ⟨C₁, hC₁, hE1⟩ := in_E1.{u}
  obtain ⟨P₀, hpf⟩ := param_facts
  refine ⟨C₁, hC₁, (hE1.and (eventually_treg_ge P₀)).mono ?_⟩
  rintro c₀ κ₀ d p h ⟨H1, hR, hp⟩ ct
  have hroot := root_equation hR ct
  rw [ct.mp_root] at hroot
  have hcard := (source_facts hR ct).1
  have ha1 := (hpf d p hR hp).1
  have ha0 : 0 < aOf d p := hR.aOf_pos
  have hd0 : (0 : ℝ) < d := lt_of_lt_of_le (by norm_num) hR.ten_pow_six_le_d
  obtain ⟨a, ha⟩ : ∃ a, a = aOf d p := ⟨_, rfl⟩
  rw [← ha] at ha0 ha1 hroot ⊢
  obtain ⟨EP, hEP⟩ : ∃ EP : ct.V → ℝ,
      EP = fun i => ct.E fun σ => ct.gp σ ct.v ct.v * ct.gp σ i i := ⟨_, rfl⟩
  obtain ⟨EX, hEX⟩ : ∃ EX : ct.V → ℝ, EX = fun i => ct.E fun σ => ct.x σ i ^ 2 := ⟨_, rfl⟩
  obtain ⟨EXZ, hEXZ⟩ : ∃ EXZ : ct.V → ℝ,
      EXZ = fun i => ct.E fun σ => ct.x σ i * ct.z σ i := ⟨_, rfl⟩
  obtain ⟨EK, hEK⟩ : ∃ EK : ct.V → ℝ, EK = fun i => ct.E fun σ => Kpoly p (ct.x σ i) (ct.z σ i)
      (ct.gp σ ct.v ct.v * ct.gp σ i i) (ct.gm σ ct.v ct.v * ct.gm σ i i) := ⟨_, rfl⟩
  have hsP : ct.sumP = ∑ i ∈ ct.N, EP i := by rw [hEP]; rfl
  have hsS : ct.Srow = ∑ i ∈ ct.N, EX i := by rw [hEX]; rfl
  have hsT : ct.Tmix = ∑ i ∈ ct.N, EXZ i := by rw [hEXZ]; rfl
  have hQ : ct.Qstar = a ^ 4 / 3 * ∑ i ∈ ct.N, EK i := by rw [hEK, ha]; rfl
  obtain ⟨g, hg⟩ : ∃ g : ct.V → ℝ, g = fun i =>
      a * (-EP i + (2 * (p : ℝ) - 1) * EX i - 2 * (p : ℝ) * EXZ i) + -(a ^ 3 / 3 * EK i) :=
    ⟨_, rfl⟩
  obtain ⟨err, herr⟩ : ∃ err : ct.V → ℝ, err = fun i => ct.sx i - g i := ⟨_, rfl⟩
  have hg' : ∀ i, g i = (-a) * EP i + (a * (2 * (p : ℝ) - 1)) * EX i +
      (-(2 * (p : ℝ) * a)) * EXZ i + (-(a ^ 3 / 3)) * EK i := fun i => by
    simp only [hg]; ring
  have hsumg : ∑ i ∈ ct.N, g i = (-a) * ct.sumP + (a * (2 * (p : ℝ) - 1)) * ct.Srow +
      (-(2 * (p : ℝ) * a)) * ct.Tmix + (-(a ^ 3 / 3)) * ∑ i ∈ ct.N, EK i := by
    rw [Finset.sum_congr rfl (fun i _ => hg' i), hsP, hsS, hsT]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hsx : ∑ i ∈ ct.N, ct.sx i = ∑ i ∈ ct.N, g i + ∑ i ∈ ct.N, err i := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by simp only [herr]; ring
  have herr_le : ∀ i ∈ ct.N, |err i| ≤ C₁ * (p : ℝ) ^ 5 * a ^ 5 := by
    intro i hi
    have h1 := H1 ct i hi
    rw [← ha] at h1
    have e : err i = ct.sx i - a * (-(ct.E fun σ => ct.gp σ ct.v ct.v * ct.gp σ i i) +
          (2 * (p : ℝ) - 1) * (ct.E fun σ => ct.x σ i ^ 2) -
          2 * (p : ℝ) * (ct.E fun σ => ct.x σ i * ct.z σ i)) +
        a ^ 3 / 3 * (ct.E fun σ => Kpoly p (ct.x σ i) (ct.z σ i)
          (ct.gp σ ct.v ct.v * ct.gp σ i i) (ct.gm σ ct.v ct.v * ct.gm σ i i)) := by
      simp only [herr, hg, hEP, hEX, hEXZ, hEK]
      ring
    rw [e]
    exact h1
  have hsum_abs : |∑ i ∈ ct.N, err i| ≤ ct.N.card * (C₁ * (p : ℝ) ^ 5 * a ^ 5) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have := Finset.sum_le_card_nsmul ct.N (fun i => |err i|) _ herr_le
    simpa [nsmul_eq_mul] using this
  have hkey : ct.Dplus * rOf d p - (1 + a ^ 2 * ct.sumP - (2 * (p : ℝ) - 1) * a ^ 2 * ct.Srow +
      2 * (p : ℝ) * a ^ 2 * ct.Tmix + ct.Qstar) = -(a * ∑ i ∈ ct.N, err i) := by
    rw [hQ]
    have : ct.Dplus * rOf d p = 1 - a * ∑ i ∈ ct.N, ct.sx i := by linarith
    rw [this, hsx, hsumg]
    ring
  rw [hkey, abs_neg, abs_mul, abs_of_pos ha0]
  have hC0 : 0 ≤ C₁ * (p : ℝ) ^ 5 := by positivity
  have ha6 : a ^ 6 * (d : ℝ) ≤ 1 / (d : ℝ) ^ 2 := by
    have h3 : (a ^ 2) ^ 3 ≤ (1 / (d : ℝ)) ^ 3 := pow_le_pow_left₀ (sq_nonneg a) ha1 3
    calc a ^ 6 * (d : ℝ) = (a ^ 2) ^ 3 * d := by ring
      _ ≤ (1 / (d : ℝ)) ^ 3 * d := mul_le_mul_of_nonneg_right h3 hd0.le
      _ = 1 / (d : ℝ) ^ 2 := by field_simp
  calc a * |∑ i ∈ ct.N, err i| ≤ a * (ct.N.card * (C₁ * (p : ℝ) ^ 5 * a ^ 5)) :=
        mul_le_mul_of_nonneg_left hsum_abs ha0.le
    _ = C₁ * (p : ℝ) ^ 5 * (a ^ 6 * ct.N.card) := by ring
    _ ≤ C₁ * (p : ℝ) ^ 5 * (a ^ 6 * d) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcard (by positivity)) hC0
    _ ≤ C₁ * (p : ℝ) ^ 5 * (1 / (d : ℝ) ^ 2) := mul_le_mul_of_nonneg_left ha6 hC0
    _ = C₁ * (p : ℝ) ^ 5 / (d : ℝ) ^ 2 := by ring

/-- **N-F3sum** (source l.1401–1406; AUDIT-D §3.1 D3). (F3) at every neighbour, multiplied by
`a²/p` and summed, with `E G⁺_vv = y_v r` and `E G⁺_ii = y_i(r - δ_i)`:
`a² Σ_N E P_i ≤ r(rL - Σℓδ) + (a²/p) S - (r/p) J`. -/
theorem f3_summed (hR : TRegime d p) (ct : Contact.{u} d p) :
    aOf d p ^ 2 * ct.sumP ≤ rOf d p * (rOf d p * ct.Lsum - ct.sumEllDelta) +
      aOf d p ^ 2 / p * ct.Srow - rOf d p / p * ct.Jw := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast lt_of_lt_of_le (by norm_num) hR.hp
  have key : ∀ i ∈ ct.N, aOf d p ^ 2 * (ct.E fun σ => ct.gp σ ct.v ct.v * ct.gp σ i i) ≤
      rOf d p * (ct.ell i * ct.mp i) + aOf d p ^ 2 / p * (ct.E fun σ => ct.x σ i ^ 2) -
        rOf d p / p * (ct.ell i * walkK ct.G (aOf d p) ct.yp ct.S ct.v i) := by
    intro i hi
    have h1 := source_covariance ct.G hR ct.ctx (ct.mem_S_of_mem_N hi)
    change (p : ℝ) * (ct.E (fun σ => ct.gp σ ct.v ct.v * ct.gp σ i i) -
        ct.E (fun σ => ct.gp σ ct.v ct.v) * ct.E (fun σ => ct.gp σ i i)) -
        ct.E (fun σ => ct.x σ i ^ 2) ≤ _ at h1
    rw [ct.E_gp_root, ct.E_gp_diag] at h1
    have h3 : aOf d p ^ 2 * (ct.E fun σ => ct.gp σ ct.v ct.v * ct.gp σ i i) -
        (rOf d p * (ct.ell i * ct.mp i) + aOf d p ^ 2 / p * (ct.E fun σ => ct.x σ i ^ 2) -
          rOf d p / p * (ct.ell i * walkK ct.G (aOf d p) ct.yp ct.S ct.v i)) =
        aOf d p ^ 2 / p * ((p : ℝ) * ((ct.E fun σ => ct.gp σ ct.v ct.v * ct.gp σ i i) -
          ct.yp ct.v * rOf d p * (ct.yp i * ct.mp i)) - (ct.E fun σ => ct.x σ i ^ 2) +
          rOf d p * ct.yp ct.v * ct.yp i * walkK ct.G (aOf d p) ct.yp ct.S ct.v i) := by
      unfold Contact.ell
      field_simp
      ring
    have h4 : aOf d p ^ 2 / p * ((p : ℝ) * ((ct.E fun σ => ct.gp σ ct.v ct.v * ct.gp σ i i) -
          ct.yp ct.v * rOf d p * (ct.yp i * ct.mp i)) - (ct.E fun σ => ct.x σ i ^ 2) +
          rOf d p * ct.yp ct.v * ct.yp i * walkK ct.G (aOf d p) ct.yp ct.S ct.v i) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    linarith
  have hsum := Finset.sum_le_sum key
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  have hell : ∑ i ∈ ct.N, ct.ell i * ct.mp i = rOf d p * ct.Lsum - ct.sumEllDelta := by
    unfold Contact.Lsum Contact.sumEllDelta
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by unfold Contact.delta; ring
  rw [hell] at hsum
  exact hsum

/-- **N-D3** (source (D3), l.1407–1412; AUDIT-C §6 (D3), AUDIT-D §3.1 D3: algebra checked
symbolically). The exact scalar inequality
`(r-1)(1 - rL) + rΣℓδ + (1 - 1/p) a² S + (r/p) J + 2a²𝓡 ≤ Q_* + rC₊ + C p⁵/d²`. -/
theorem d3 : ∃ C : ℝ, 0 < C ∧ Eventually fun _c₀ _κ₀ d p _h =>
    ∀ ct : Contact.{u} d p,
      epsP d p * (1 - rOf d p * ct.Lsum) + rOf d p * ct.sumEllDelta +
          (1 - 1 / (p : ℝ)) * aOf d p ^ 2 * ct.Srow + rOf d p / p * ct.Jw +
          2 * aOf d p ^ 2 * ct.Rrow ≤
        ct.Qstar + rOf d p * ct.Cplus + C * (p : ℝ) ^ 5 / (d : ℝ) ^ 2 := by
  obtain ⟨C, hC, hL⟩ := loop.{u}
  refine ⟨C, hC, (hL.and (eventually_treg_ge 0)).mono ?_⟩
  rintro c₀ κ₀ d p h ⟨HL, hR, -⟩ ct
  have h1 := (abs_le.1 (HL ct)).2
  have h2 := f3_summed hR ct
  have h3 := (source_facts hR ct).2.2.2.2.2.2.1
  have hp0 : (0 : ℝ) < p := by exact_mod_cast lt_of_lt_of_le (by norm_num) hR.hp
  unfold Contact.Rrow epsP
  rw [h3] at h1
  have e1 : (1 - 1 / (p : ℝ)) * aOf d p ^ 2 * ct.Srow =
      aOf d p ^ 2 * ct.Srow - aOf d p ^ 2 / p * ct.Srow := by ring
  rw [e1]
  linarith

/-! ### The bootstrap (D4), (D6), (D7) -/

/-- **N-D4** (source (D4), l.1423–1436). `𝓡 ≤ C(p + p⁵/d)`; if `𝓡 ≥ -b` then
`S + a⁻²Σℓδ ≤ C(1 + p + p⁵/d + b)` and `L̄ - L ≤ C a²(1 + p + p⁵/d + b)/(r-1)`. -/
theorem d4 : ∃ C : ℝ, 0 < C ∧ Eventually fun _c₀ _κ₀ d p _h =>
    ∀ ct : Contact.{u} d p,
      ct.Rrow ≤ C * (p + (p : ℝ) ^ 5 / d) ∧
      ∀ b : ℝ, 0 ≤ b → -b ≤ ct.Rrow →
        ct.Srow + ct.sumEllDelta / aOf d p ^ 2 ≤ C * (1 + p + (p : ℝ) ^ 5 / d + b) ∧
        LbarP d p - ct.Lsum ≤ C * aOf d p ^ 2 * (1 + p + (p : ℝ) ^ 5 / d + b) / epsP d p := by
  obtain ⟨C₃, -, hD3⟩ := d3.{u}
  obtain ⟨CQ, -, hQ⟩ := qstar_bound.{u}
  obtain ⟨C, hC, P₀, hreal⟩ := d4_real C₃ CQ
  refine ⟨C, hC, ((hD3.and hQ).and (eventually_treg_ge P₀)).mono ?_⟩
  rintro c₀ κ₀ d p h ⟨⟨H3, HQ⟩, hR, hp⟩ ct
  obtain ⟨-, -, hL, hC0, hCJ, hCa, -, hsED, hS, -⟩ := source_facts hR ct
  exact hreal d p hR hp ct.Srow ct.Rrow ct.Jw ct.Cplus ct.Qstar ct.Lsum ct.sumEllDelta hS hC0
    hCJ hsED hL hCa (HQ ct) (H3 ct)

/-- **N-D6** (source (D6), l.1438–1487; AUDIT-C §6 (D6)). With `λ = a² S + E tr A² + ϑ`:
`λ ≤ C p/d` (`=: λ₁`). Uses CR1 with the envelope `λ` itself (`ϑ ≤ λ ≤ (2C₂+1) δ̄` by (C2)),
`Gterm ≥ 0` (C1), the whitening transfer, (C3a) and (D4). -/
theorem d6 : ∃ C : ℝ, 0 < C ∧ Eventually fun _c₀ _κ₀ d p _h =>
    ∀ ct : Contact.{u} d p, aOf d p ^ 2 * ct.Srow + ct.trA2 + vth d ≤ C * p / d := by
  obtain ⟨C₂, hC₂, hC2⟩ := in_C2.{u}
  obtain ⟨C₁, -, hCR1⟩ := cr1.{u} (2 * C₂ + 1)
  obtain ⟨Cw, -, hW⟩ := in_whiten.{u}
  obtain ⟨Ca, -, hA⟩ := in_C3a.{u}
  obtain ⟨C₄, -, hD4⟩ := d4.{u}
  obtain ⟨C, hC, P₀, hreal⟩ := d6_real C₁ Cw Ca C₄
  refine ⟨C, hC, ((((((hC2.and hCR1).and in_C1).and hW).and hA).and hD4).and
    (eventually_treg_ge P₀)).mono ?_⟩
  rintro c₀ κ₀ d p h ⟨⟨⟨⟨⟨⟨H2, HR1⟩, H1⟩, HW⟩, HA⟩, HD4⟩, hR, hp⟩ ct
  obtain ⟨-, -, -, -, -, -, -, -, hS, -, hA2, -, hw⟩ := source_facts hR ct
  have hv := vth_le_dbar hR
  have hvth : 0 ≤ vth d := by unfold vth; positivity
  have ha2 : 0 ≤ aOf d p ^ 2 * ct.Srow := mul_nonneg (sq_nonneg _) hS
  have hlam : aOf d p ^ 2 * ct.Srow + ct.trA2 + vth d ≤ (2 * C₂ + 1) * dbar d p := by
    have := H2 ct
    linarith [this.1, this.2.2.1]
  have hcr := HR1 ct (aOf d p ^ 2 * ct.Srow + ct.trA2 + vth d) (by linarith) (by linarith) hlam
  exact hreal d p hR hp ct.Srow ct.trA2 ct.wker ct.Gterm ct.Rrow hS hA2 hw hcr (H1 ct) (HW ct)
    (HA ct) (HD4 ct).1 fun b hb hRb => by
      have := ((HD4 ct).2 b hb hRb).1
      have hq : 0 ≤ ct.sumEllDelta / aOf d p ^ 2 :=
        div_nonneg (source_facts hR ct).2.2.2.2.2.2.2.1 (sq_nonneg _)
      linarith

/-- **N-D7** (source (D7), l.1487–1491; AUDIT-C §6 (D7)). `S ≤ Cp`, `Σℓδ ≤ C p a²`,
`L̄ - L ≤ C ε_s`. -/
theorem d7 : ∃ C : ℝ, 0 < C ∧ Eventually fun _c₀ _κ₀ d p _h =>
    ∀ ct : Contact.{u} d p,
      ct.Srow ≤ C * p ∧ ct.sumEllDelta ≤ C * p * aOf d p ^ 2 ∧
        LbarP d p - ct.Lsum ≤ C * epsS d p := by
  obtain ⟨C₂, hC₂, hC2⟩ := in_C2.{u}
  obtain ⟨C₁, -, hCR1⟩ := cr1.{u} (2 * C₂ + 1)
  obtain ⟨C₄, -, hD4⟩ := d4.{u}
  obtain ⟨C₆, -, hD6⟩ := d6.{u}
  obtain ⟨C, hC, P₀, hreal⟩ := d7_real C₁ C₄ C₆
  refine ⟨C, hC, (((((hC2.and hCR1).and in_C1).and hD4).and hD6).and
    (eventually_treg_ge P₀)).mono ?_⟩
  rintro c₀ κ₀ d p h ⟨⟨⟨⟨⟨H2, HR1⟩, H1⟩, HD4⟩, HD6⟩, hR, hp⟩ ct
  obtain ⟨-, -, -, -, -, -, -, hsED, hS, -, hA2, -, -⟩ := source_facts hR ct
  have hv := vth_le_dbar hR
  have hvth : 0 ≤ vth d := by unfold vth; positivity
  have ha2 : 0 ≤ aOf d p ^ 2 * ct.Srow := mul_nonneg (sq_nonneg _) hS
  have hlam : aOf d p ^ 2 * ct.Srow + ct.trA2 + vth d ≤ (2 * C₂ + 1) * dbar d p := by
    have := H2 ct
    linarith [this.1, this.2.2.1]
  have hcr := HR1 ct (aOf d p ^ 2 * ct.Srow + ct.trA2 + vth d) (by linarith) (by linarith) hlam
  exact hreal d p hR hp ct.Srow ct.trA2 ct.Gterm ct.Rrow ct.Lsum ct.sumEllDelta hS hA2 (HD6 ct)
    hcr (H1 ct) (HD4 ct).2 hsED

end BiluLinial.Tight
