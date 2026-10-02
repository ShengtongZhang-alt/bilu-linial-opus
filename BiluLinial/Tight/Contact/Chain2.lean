/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.Contact.RouteDR1D9a
public import BiluLinial.Tight.Contact.Leaves3

/-!
# The contact chain, part 2: trace budget, energies, centres and the conclusion

Blueprint `docs/tight/BP_CONTACT.md`, nodes `N-D9b`, `N-D10`, `N-Ec`, `N-FS6`, `N-RC3`, `N-D12`,
`N-D15`, `N-final` (source l.1520–2053; AUDIT-C §6, AUDIT-D §3.1–3.8). Every node is proved from
the statements of its children. The last node `contact_final` gives the contradiction once the
critical coefficient `C(√κ₀ + c₀^{17/3} + κ₀⁻²c₀^{34/3})` is at most `1/8`.
-/

@[expose] public section

namespace BiluLinial.Tight

open Matrix

universe u

variable {d p : ℕ}

/-- **N-D9b** (source (D9b), l.1520–1531). `Q ≤ C p`. -/
theorem d9b : ∃ C : ℝ, 0 < C ∧ Eventually fun _c₀ _κ₀ d p h =>
    ∀ ct : Contact.{u} d p, ct.Qbl h ≤ C * p := by
  obtain ⟨CB, -, hB1⟩ := in_B1.{u}
  obtain ⟨C₉, -, hD9a⟩ := d9a.{u}
  obtain ⟨C₄, -, hD4⟩ := d4.{u}
  obtain ⟨C₇, -, hD7⟩ := d7.{u}
  obtain ⟨C, hC, hreal⟩ := d9b_real CB C₉ C₄ C₇
  refine ⟨C, hC, (((((hB1.and hD9a).and hD4).and hD7).and (eventually_treg_ge 0)).and
    (Eventually.of_reg hreal)).mono ?_⟩
  rintro c₀ κ₀ d p h ⟨⟨⟨⟨⟨HB, H9⟩, H4⟩, H7⟩, hR, -⟩, HR⟩ ct
  exact HR ct.Srow ct.Rrow ct.Gterm (ct.Qbl h) (source_facts hR ct).2.2.2.2.2.2.2.2.1 (HB ct)
    (H9 ct) (H4 ct).1 (H7 ct).1

/-- **N-D10** (source (D10), l.1546–1558; AUDIT-D G6: `ε_BL` added).
`𝓡 ≥ L_d[(p-1)q₊ + p q₋] - C{E_row + p⁵/d + p²/(dh) + p/(dh^{3/2}) + ε_BL}`. -/
theorem d10 : ∃ C : ℝ, 0 < C ∧ Eventually fun _c₀ _κ₀ d p h =>
    ∀ ct : Contact.{u} d p,
      LdP d p * (((p : ℝ) - 1) * ct.qP h + p * ct.qM h) - C * Err10 d p h ct.Srow ≤ ct.Rrow := by
  obtain ⟨CB, hCB, hB1⟩ := in_B1.{u}
  obtain ⟨C₉, -, hD9a⟩ := d9a.{u}
  obtain ⟨C₉b, -, hD9b⟩ := d9b.{u}
  obtain ⟨Cc, -, hcorr⟩ := d10_corr.{u}
  obtain ⟨C, hC, hreal⟩ := d10_real CB C₉ C₉b Cc hCB.le
  refine ⟨C, hC, ((((hB1.and hD9a).and hD9b).and hcorr).and eventually_reg).mono ?_⟩
  rintro c₀ κ₀ d p h ⟨⟨⟨⟨HB, H9⟩, H9b⟩, HC⟩, hR, -⟩ ct
  exact hreal d p h hR.treg hR.h_pos ct.Srow ct.Rrow ct.Gterm (ct.Qbl h) _ (HB ct) (H9 ct)
    (H9b ct) (HC ct)

/-- **N-Ec** (source l.1590–1592, (E-c) of AUDIT-D §3.2). `q₊ ≤ C`. -/
theorem qP_le : ∃ C : ℝ, 0 < C ∧ Eventually fun _c₀ _κ₀ d p h =>
    ∀ ct : Contact.{u} d p, ct.qP h ≤ C := by
  obtain ⟨C₉b, -, hD9b⟩ := d9b.{u}
  obtain ⟨Cc, -, hcorr⟩ := d10_corr.{u}
  obtain ⟨C, hC, hreal⟩ := qP_le_real C₉b Cc
  refine ⟨C, hC, (((hD9b.and hcorr).and eventually_reg).and (Eventually.of_reg hreal)).mono ?_⟩
  rintro c₀ κ₀ d p h ⟨⟨⟨H9b, HC⟩, hR, -⟩, HR⟩ ct
  exact HR (ct.Qbl h) (ct.qP h) (ct.qM h) (energy_psd hR.treg hR.h_pos ct).2.2.2.2.2.2.2.1
    (HC ct) (H9b ct)

/-- **N-FS6** (source (FS6), l.1765–1776, the weak loop (W1) applied with the scores bounded by
(FS5)). The four weak residuals are bounded by `C(e√(·) + e h^{3/4} + B₀)`. -/
theorem weak_res : ∃ C : ℝ, 0 < C ∧ Eventually fun _c₀ _κ₀ d p h =>
    ∀ ct : Contact.{u} d p,
      |ct.qP h - ct.zeta h - ct.tP h| ≤ C * (eP d p h * Real.sqrt (ct.zeta h - ct.alphaE h +
          1 / (d * h) * (ct.qP h - ct.tP h) + thP d) + eP d p h * h ^ ((3 : ℝ) / 4) +
          B0P d p h) ∧
      |ct.zeta h - ct.zP h - ct.alphaE h| ≤
          C * (eP d p h * Real.sqrt (ct.zP h + thP d) + B0P d p h) ∧
      |ct.qM h + ct.zetaM h - ct.tM h| ≤ C * (eP d p h * Real.sqrt (ct.zeta h - ct.alphaE h +
          1 / (d * h) * (ct.qP h - ct.tP h) + thP d) + eP d p h * h ^ ((3 : ℝ) / 4) +
          B0P d p h) ∧
      |ct.zetaM h + ct.zM h - ct.betaE h| ≤
          C * (eP d p h * Real.sqrt (ct.zM h + thP d) + B0P d p h) := by
  obtain ⟨CW, hCW, hW1⟩ := in_W1.{u}
  obtain ⟨CF, hCF, hFS5⟩ := fs5_scores.{u}
  refine ⟨CW * (CF + 1), by positivity, ((hW1.and hFS5).and eventually_reg).mono ?_⟩
  rintro c₀ κ₀ d p h ⟨⟨HW, HF⟩, hR, -⟩ ct
  have hh := hR.h_pos
  have he : 0 ≤ eP d p h := by unfold eP; have := hh.le; positivity
  have hB : 0 ≤ B0P d p h := by unfold B0P vth; positivity
  have hq : 0 ≤ h ^ ((3 : ℝ) / 4) := Real.rpow_nonneg hh.le _
  obtain ⟨w1, w2, w3, w4⟩ := HW ct
  obtain ⟨f1, f2, f3, f4⟩ := HF ct
  have comb : ∀ r s x y : ℝ, 0 ≤ x → 0 ≤ y → r ≤ CW * s + CW * B0P d p h →
      s ≤ CF * x + CF * y → r ≤ CW * (CF + 1) * (x + y + B0P d p h) := by
    intro r s x y hx hy h1 h2
    have h3 := mul_le_mul_of_nonneg_left h2 hCW.le
    have h4 := mul_nonneg hCW.le hx
    have h5 := mul_nonneg hCW.le hy
    have h6 := mul_nonneg (mul_nonneg hCW.le hCF.le) hB
    linarith
  have hs1 := mul_nonneg he (Real.sqrt_nonneg (ct.zeta h - ct.alphaE h +
    1 / (d * h) * (ct.qP h - ct.tP h) + thP d))
  have hs2 := mul_nonneg he (Real.sqrt_nonneg (ct.zP h + thP d))
  have hs4 := mul_nonneg he (Real.sqrt_nonneg (ct.zM h + thP d))
  have hs3 := mul_nonneg he hq
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact comb _ _ _ _ hs1 hs3 w1 (by linarith)
  · have := comb _ _ _ 0 hs2 le_rfl w2 (by linarith)
    simpa using this
  · exact comb _ _ _ _ hs1 hs3 w3 (by linarith)
  · have := comb _ _ _ 0 hs4 le_rfl w4 (by linarith)
    simpa using this

/-- **N-RC3** (source (RC3), l.1910–1918, through (FS7), the α-cap, (JR3) and (JR2), l.1776–1908).
`(p-1)(q₊ - t₊) + p(q₋ - t₋) ≥ -c_p - C p {e² + B₀ + e[h^{3/4} + (dh)^{-1/2} + √θ] + ξ}`. -/
theorem rc3 : ∃ C : ℝ, 0 < C ∧ Eventually fun _c₀ _κ₀ d p h =>
    ∀ ct : Contact.{u} d p,
      -cpP p - C * p * ErrRC3 d p h ≤
        ((p : ℝ) - 1) * (ct.qP h - ct.tP h) + p * (ct.qM h - ct.tM h) := by
  obtain ⟨Cw, -, hWR⟩ := weak_res.{u}
  obtain ⟨Cq, -, hQP⟩ := qP_le.{u}
  obtain ⟨C₁, -, hRC1⟩ := rc1_tbounds.{u}
  obtain ⟨C₂, -, hRC2⟩ := rc2_profile.{u}
  obtain ⟨K₁, hK₁, hfs7⟩ := fs7_real Cw Cq
  obtain ⟨K₂, hK₂, hjr⟩ := jr_real C₁ C₂
  obtain ⟨K, hK, hyg⟩ := rc3_young_real (K₂ * max K₁ 1)
  refine ⟨2 * K, by positivity, ((((hWR.and hQP).and hRC1).and hRC2).and eventually_reg).mono ?_⟩
  rintro c₀ κ₀ d p h ⟨⟨⟨⟨HW, HQ⟩, H1⟩, H2⟩, hR, -⟩ ct
  have hh := hR.h_pos
  have hp2 : 2 ≤ p := hR.treg.two_le_p
  obtain ⟨eq0, ez0, ezq, etq, ea0, eaz, et0, eqm0, ezm0, ezqm, eb0, etm0⟩ :=
    energy_psd hR.treg hh ct
  have he : 0 ≤ eP d p h := by unfold eP; have := hh.le; positivity
  have hB : 0 ≤ B0P d p h := by unfold B0P vth; positivity
  have hq : 0 ≤ h ^ ((3 : ℝ) / 4) := Real.rpow_nonneg hh.le _
  have hbh : 0 ≤ 1 / ((d : ℝ) * h) := by positivity
  have hth : 0 ≤ thP d := by unfold thP; positivity
  have hε : 0 ≤ epsP d p := by unfold epsP; linarith [hR.treg.one_lt_rOf]
  have hεξ := epsP_le_xiP hR.treg h
  obtain ⟨w1, w2, w3, w4⟩ := HW ct
  obtain ⟨r1, r2, r3, r4⟩ := hfs7 (eP d p h) (B0P d p h) (h ^ ((3 : ℝ) / 4)) (1 / (d * h))
    (thP d) (ct.qP h) (ct.tP h) (ct.zeta h) (ct.alphaE h) (ct.zP h) (ct.qM h) (ct.zetaM h)
    (ct.tM h) (ct.zM h) (ct.betaE h) he hB hq hbh hth ez0 ezm0 (by linarith)
    (by linarith [HQ ct]) eaz w1 w2 w3 w4
  set Ec := EcF (eP d p h) (B0P d p h) (h ^ ((3 : ℝ) / 4)) (1 / (d * h)) (thP d) (ct.zP h)
    (ct.zM h) with hEc
  set E₀ := eP d p h ^ 2 + B0P d p h +
    eP d p h * (h ^ ((3 : ℝ) / 4) + Real.sqrt (1 / (d * h)) + Real.sqrt (thP d)) with hE₀
  have hE₀0 : 0 ≤ E₀ := by
    have := Real.sqrt_nonneg (1 / ((d : ℝ) * h))
    have := Real.sqrt_nonneg (thP d)
    positivity
  have hEc0 : 0 ≤ K₁ * Ec := by
    have := Real.sqrt_nonneg (ct.zP h)
    have := Real.sqrt_nonneg (ct.zM h)
    have := Real.sqrt_nonneg (1 / ((d : ℝ) * h))
    have := Real.sqrt_nonneg (thP d)
    rw [hEc, EcF]
    positivity
  have hJR := hjr p hp2 (K₁ * Ec) (xiP d p h) (epsP d p) (ct.qP h) (ct.tP h) (ct.zeta h)
    (ct.alphaE h) (ct.zP h) (ct.qM h) (ct.zetaM h) (ct.tM h) (ct.zM h) (ct.betaE h) hEc0 hε hεξ
    eq0 ez0 ezq eqm0 ezm0 ezqm etq ea0 eaz eb0 et0 (H1 ct).1 etm0 (H1 ct).2 (H2 ct) r1 r2 r3 r4
  have hξ0 : 0 ≤ xiP d p h := le_trans hε hεξ
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hmono : K₂ * p * (K₁ * Ec + xiP d p h) ≤ K₂ * max K₁ 1 * p *
      (eP d p h * Real.sqrt (ct.zP h) + eP d p h * Real.sqrt (ct.zM h) + E₀ + xiP d p h) := by
    have h1 : K₁ * Ec + xiP d p h ≤ max K₁ 1 *
        (eP d p h * Real.sqrt (ct.zP h) + eP d p h * Real.sqrt (ct.zM h) + E₀ + xiP d p h) := by
      have hEcE : Ec = eP d p h * Real.sqrt (ct.zP h) + eP d p h * Real.sqrt (ct.zM h) + E₀ := by
        rw [hEc, hE₀, EcF]; ring
      have hm1 : K₁ ≤ max K₁ 1 := le_max_left _ _
      have hm2 : 1 ≤ max K₁ 1 := le_max_right _ _
      have hEc' : 0 ≤ Ec := by
        rw [hEcE]
        have := Real.sqrt_nonneg (ct.zP h)
        have := Real.sqrt_nonneg (ct.zM h)
        positivity
      have k1 : K₁ * Ec ≤ max K₁ 1 * Ec := mul_le_mul_of_nonneg_right hm1 hEc'
      have k2 : 1 * xiP d p h ≤ max K₁ 1 * xiP d p h := mul_le_mul_of_nonneg_right hm2 hξ0
      rw [hEcE] at k1 ⊢
      linarith
    have := mul_le_mul_of_nonneg_left h1 (mul_nonneg hK₂.le hp0)
    linarith
  have hY := hyg p hp2 (eP d p h) (ct.zP h) (ct.zM h) E₀ (xiP d p h)
    (((p : ℝ) - 1) * (ct.qP h - ct.tP h) + p * (ct.qM h - ct.tM h)) he ez0 ezm0 hE₀0 hξ0
    (by linarith)
  have hE : eP d p h ^ 2 + E₀ + xiP d p h ≤ 2 * ErrRC3 d p h := by
    have hErr : ErrRC3 d p h = E₀ + xiP d p h := by rw [hE₀]; rfl
    have he2 : eP d p h ^ 2 ≤ E₀ := by
      have h1 : 0 ≤ eP d p h * (h ^ ((3 : ℝ) / 4) + Real.sqrt (1 / (d * h)) +
          Real.sqrt (thP d)) := by
        have := Real.sqrt_nonneg (1 / ((d : ℝ) * h))
        have := Real.sqrt_nonneg (thP d)
        positivity
      rw [hE₀]
      linarith
    rw [hErr]
    linarith
  have hcp : cpP p = 1 / (4 * ((p : ℝ) - 1)) := rfl
  have hKE := mul_le_mul_of_nonneg_left hE (mul_nonneg hK.le hp0)
  rw [hcp]
  linarith

/-- **N-D12** (source (D12), l.1955–1963).
`𝒟 = 𝓡 - L_d[(p-1)t_{+,0} + p t_{-,0}] ≥ -L_d c_p - C𝓔`. -/
theorem d12 : ∃ C : ℝ, 0 < C ∧ Eventually fun _c₀ _κ₀ d p h =>
    ∀ ct : Contact.{u} d p,
      -(LdP d p * cpP p) - C * Err12 d p h ct.Srow ≤
        ct.Rrow - LdP d p * (((p : ℝ) - 1) * ct.tP0 + p * ct.tM0) := by
  obtain ⟨C₁₀, -, hD10⟩ := d10.{u}
  obtain ⟨C₃, -, hRC3⟩ := rc3.{u}
  obtain ⟨C₄, -, hRC4⟩ := rc4_centres.{u}
  obtain ⟨C, hC, P₀, hreal⟩ := d12_real C₁₀ C₃ C₄
  refine ⟨C, hC, (((hD10.and hRC3).and hRC4).and (eventually_reg.and
    (eventually_treg_ge P₀))).mono ?_⟩
  rintro c₀ κ₀ d p h ⟨⟨⟨H10, H3⟩, H4⟩, ⟨hR, -⟩, -, hp⟩ ct
  exact hreal d p h hR.treg hp hR.h_pos ct.Srow ct.Rrow (ct.qP h) (ct.qM h) (ct.tP h) (ct.tM h)
    ct.tP0 ct.tM0 (H10 ct) (H3 ct) (H4 ct).1.2 (H4 ct).2.2

/-- **N-D15** (source (D15), l.1977–1982). `S ≥ 4 - C(ε_s + η₀ + 1/d)`. -/
theorem d15 : ∃ C : ℝ, 0 < C ∧ Eventually fun _c₀ _κ₀ d p _h =>
    ∀ ct : Contact.{u} d p, 4 - C * (epsS d p + η0Of d p + 1 / (d : ℝ)) ≤ ct.Srow := by
  obtain ⟨C₇, -, hD7⟩ := d7.{u}
  obtain ⟨C, hC, P₀, hreal⟩ := d15_real C₇
  refine ⟨C, hC, (hD7.and (eventually_treg_ge P₀)).mono ?_⟩
  rintro c₀ κ₀ d p h ⟨H7, hR, hp⟩ ct
  obtain ⟨hcard, -, -, hC0, -, hCa, hDp, -, hS, -⟩ := source_facts hR ct
  have hroot := root_equation hR ct
  rw [ct.mp_root] at hroot
  have hcs := d15_cs ct
  have hsq : (rOf d p * ct.Dplus - 1) ^ 2 ≤ aOf d p ^ 2 * ct.N.card * ct.Srow := by
    have e : rOf d p * ct.Dplus - 1 = -(aOf d p * ∑ i ∈ ct.N, ct.sx i) := by linarith
    rw [e, neg_sq, mul_pow, mul_assoc]
    exact mul_le_mul_of_nonneg_left hcs (sq_nonneg _)
  exact hreal d p hR hp ct.Srow ct.N.card ct.Lsum ct.Cplus ct.Dplus hS (Nat.cast_nonneg _) hcard
    hC0 hDp hCa (H7 ct).2.2 hsq

/-- **N-final** (source (D14), absorption, (D16) and the conclusion, l.1965–2053; AUDIT-D §3.8,
§4). There is an absolute `C` such that, for all `c₀, κ₀ ∈ (0,1]` with
`C(√κ₀ + c₀^{17/3} + κ₀⁻² c₀^{34/3}) ≤ 1/8` and all large `d`, no contact exists. -/
theorem contact_final : ∃ Ccrit : ℝ, 0 < Ccrit ∧ Eventually fun c₀ κ₀ d p _h =>
    Ccrit * (Real.sqrt κ₀ + c₀ ^ ((17 : ℝ) / 3) + κ₀⁻¹ ^ 2 * c₀ ^ ((34 : ℝ) / 3)) ≤ 1 / 8 →
      ∀ _ct : Contact.{u} d p, False := by
  obtain ⟨C₃, -, hD3⟩ := d3.{u}
  obtain ⟨C₁₂, -, hD12⟩ := d12.{u}
  obtain ⟨C₁₃, -, hD13⟩ := d13_centering.{u}
  obtain ⟨C₁₅, -, hD15⟩ := d15.{u}
  obtain ⟨K, -, P₁, hasm⟩ := final_assembly_real C₃ C₁₂ C₁₃ C₁₅
  obtain ⟨Ccrit, hCcrit, hled⟩ := ledger_real K
  refine ⟨Ccrit, hCcrit, ?_⟩
  intro c₀ κ₀ hc0 hc1 hk0 hk1
  by_cases hcrit : Ccrit * (Real.sqrt κ₀ + c₀ ^ ((17 : ℝ) / 3) +
      κ₀⁻¹ ^ 2 * c₀ ^ ((34 : ℝ) / 3)) ≤ 1 / 8
  · obtain ⟨P₂, hP₂⟩ := hled c₀ κ₀ hc0 hc1 hk0 hk1 hcrit
    obtain ⟨D, hD⟩ := ((((hD3.and hD12).and hD13).and hD15).and (eventually_reg.and
      (eventually_ge fun _ _ => max P₁ P₂))) c₀ κ₀ hc0 hc1 hk0 hk1
    refine ⟨D, fun d hd _ ct => ?_⟩
    obtain ⟨⟨⟨⟨H3, H12⟩, H13⟩, H15⟩, ⟨hR, -, -, hpc⟩, hp⟩ := hD d hd
    obtain ⟨-, -, hL, hC0, hCJ, hCa, -, hsED, hS, -⟩ := source_facts hR.treg ct
    have h1 := hasm d _ _ hR.treg (le_trans (le_max_left _ _) hp) hR.h_pos ct.Srow ct.Rrow ct.Jw
      ct.Cplus ct.Qstar ct.Lsum ct.sumEllDelta
      (((pAt c₀ d : ℝ) - 1) * ct.tP0 + (pAt c₀ d) * ct.tM0) hS hsED hL hC0 hCJ hCa (H3 ct)
      (H12 ct) (H13 ct) (H15 ct)
    have h2 := hP₂ d _ _ hR hpc (le_trans (le_max_right _ _) hp)
    linarith
  · exact ⟨0, fun d _ hc => absurd hc hcrit⟩

end BiluLinial.Tight
