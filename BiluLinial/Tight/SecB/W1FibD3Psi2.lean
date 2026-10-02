/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecB.W1FibD3Psi

/-!
# TB.W1fib-d3: the jet of `Ψ` (assembly)

`d3_psi_jet`: at a good endpoint `τ₀`, on `|t - t₀| ≤ 3`, `t ↦ obsPsi(P̃⁺(t), P̃⁻(t))` has a 3-jet
with `|Ψ^{(r)}| ≤ 4718592 Q⁸/(√d h) (aD)^r`, `D = D_*(τ₀)`, `Q = 2661121 D³` (all four
configurations). See `SecB/W1FibD3Psi.lean`.
-/

@[expose] public section

namespace BiluLinial.Tight.SecB

open Matrix

universe u

section Gen

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `jb_entry_bounds` for the shifted family `physInv y ((B + κ(t) E) + C)`. -/
theorem jb_entry_bounds' {B C : Matrix n n ℝ} (hB : (B + C).PosDef) (y : n → ℝ) {i j : n}
    (hij : i ≠ j) {U : Set ℝ} {t₀ : ℝ} (hU : ∀ t ∈ U, |t - t₀| ≤ 3) {θ a D : ℝ} (hθ : |θ| ≤ a)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hD : 1 ≤ D) (Bl : Finset n) (hiB : i ∈ Bl) (hjB : j ∈ Bl)
    (hball : ∀ x ∈ Bl, ∀ z ∈ Bl, |physInv y (B + C) x z| ≤ D)
    (hsm : a * (|physInv y (B + C) i i| + |physInv y (B + C) j j| + |physInv y (B + C) i j|) ≤
      1 / 32) (x z : n) :
    (x ∈ Bl → ∃ F, JB U (fun t => physInv y (B + ((t - t₀) * (θ * (Real.sqrt (y i) *
        Real.sqrt (y j)))) • SecA.edgeE i j + C) x z) F
      (|physInv y (B + C) x z| + 1330560 * D ^ 2 * (|physInv y (B + C) i z| +
        |physInv y (B + C) j z|)) (a * D)) ∧
    (z ∈ Bl → ∃ F, JB U (fun t => physInv y (B + ((t - t₀) * (θ * (Real.sqrt (y i) *
        Real.sqrt (y j)))) • SecA.edgeE i j + C) x z) F
      (|physInv y (B + C) x z| + 1330560 * D ^ 2 * (|physInv y (B + C) x i| +
        |physInv y (B + C) x j|)) (a * D)) ∧
    (x ∈ Bl → z ∈ Bl → ∃ F, JB U (fun t => physInv y (B + ((t - t₀) * (θ * (Real.sqrt (y i) *
        Real.sqrt (y j)))) • SecA.edgeE i j + C) x z) F (2661121 * D ^ 3) (a * D)) := by
  obtain ⟨e1, e2, e3⟩ := jb_entry_bounds hB y hij hU hθ ha0 ha1 hD Bl hiB hjB hball hsm x z
  have hc : ∀ t, B + ((t - t₀) * (θ * (Real.sqrt (y i) * Real.sqrt (y j)))) • SecA.edgeE i j + C =
      B + C + ((t - t₀) * (θ * (Real.sqrt (y i) * Real.sqrt (y j)))) • SecA.edgeE i j :=
    fun t => add_right_comm _ _ _
  refine ⟨fun hx => ⟨_, (e1 hx).congr fun t _ => by rw [hc]⟩,
    fun hz => ⟨_, (e2 hz).congr fun t _ => by rw [hc]⟩,
    fun hx hz => ⟨_, (e3 hx hz).congr fun t _ => by rw [hc]⟩⟩

end Gen

section Psi

variable {d p : ℕ} (ct : Contact.{u} d p)

/-- **The jet of `Ψ`** at a good endpoint. -/
theorem d3_psi_jet {h : ℝ} (hh : 0 < h) (hR : TRegime d p) {τ₀ : Config ct.V} {i j : ct.V}
    (hi : i ∈ ct.N) (hj : j ∈ nbhd ct.G ct.S i) (hg : fibGood ct i j τ₀) {U : Set ℝ} {t₀ : ℝ}
    (hU : ∀ t ∈ U, |t - t₀| ≤ 3) (k : Fin 4) :
    ∃ F, JB U (fun t => obsPsi ct h k i j
        (precN ct.G (aOf d p) 1 ct.yp τ₀ ct.S +
          ((t - t₀) * (1 * aOf d p * (Real.sqrt (ct.yp i) * Real.sqrt (ct.yp j)))) •
            SecA.edgeE i j)
        (precN ct.G (aOf d p) (-1) ct.ym τ₀ ct.S +
          ((t - t₀) * (-1 * aOf d p * (Real.sqrt (ct.ym i) * Real.sqrt (ct.ym j)))) •
            SecA.edgeE i j))
      F (4718592 * (2661121 * ct.Dstar τ₀ ^ 3) ^ 8 / (Real.sqrt d * h))
      (aOf d p * ct.Dstar τ₀) := by
  have hw := hg.1
  have hp : 1 ≤ p := le_trans (by norm_num) hR.hp
  have hij : ct.G.Adj i j := (Finset.mem_filter.mp hj).2
  have hne : i ≠ j := ct.G.ne_of_adj hij
  have hiB := w1Ball_N ct hi
  have hjB := w1Ball_NN ct hi hj
  have hvB := w1Ball_v ct
  have hD1 := w1_Dstar_ge_one ct hw
  have hD0 : 0 ≤ ct.Dstar τ₀ := by linarith
  have ha := hR.aOf_pos
  have hd : (0 : ℝ) < d := by have := hR.ten_pow_six_le_d; linarith
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd
  have ha2 := hR.pf_a_sq_le
  have had : aOf d p ^ 2 * d ≤ 1 := by
    have := mul_le_mul_of_nonneg_right ha2 hd.le
    rwa [one_div_mul_cancel hd.ne'] at this
  have ha1 : aOf d p ≤ 1 := by
    have : 1 / (d : ℝ) ≤ 1 := by rw [div_le_one hd]; have := hR.ten_pow_six_le_d; linarith
    nlinarith
  have hl : 0 ≤ aOf d p * ct.Dstar τ₀ := by positivity
  obtain ⟨hpP, hpM⟩ := posDef_of_wt_ne_zero ct.G hw
  have hyp : ∀ k, 0 ≤ ct.yp k := fun k => (ct.ctx.hyp k).1
  have hym : ∀ k, 0 ≤ ct.ym k := fun k => (ct.ctx.hym k).1
  have hsrc : ∀ y : ct.V → ℝ, (∀ k, 0 ≤ y k) → (h • srcDiag y ct.S).PosSemidef := fun y hy => by
    refine Matrix.PosSemidef.smul ?_ hh.le
    refine Matrix.PosSemidef.diagonal fun l => ?_
    split_ifs
    · exact hy l
    · exact le_rfl
  have hpPX := hpP.add_posSemidef (hsrc _ hyp)
  have hpMX := hpM.add_posSemidef (hsrc _ hym)
  obtain ⟨smP, smM, smXP, smXM⟩ := d3_small ct hh hp hg
  have hθp : |1 * aOf d p| ≤ aOf d p := by rw [one_mul, abs_of_pos ha]
  have hθm : |-1 * aOf d p| ≤ aOf d p := by rw [neg_one_mul, abs_neg, abs_of_pos ha]
  -- the constants
  set D := ct.Dstar τ₀ with hDdef
  have hQ1 : 1 ≤ 2661121 * D ^ 3 := by
    have : 1 ≤ D ^ 3 := one_le_pow₀ hD1
    linarith
  have hQ0 : 0 ≤ 2661121 * D ^ 3 := by linarith
  have hDQ : D ≤ 2661121 * D ^ 3 := by
    have : D ≤ D ^ 3 := by
      have h2 : 1 ≤ D ^ 2 := one_le_pow₀ hD1
      calc D = D * 1 := (mul_one D).symm
        _ ≤ D * D ^ 2 := mul_le_mul_of_nonneg_left h2 hD0
        _ = D ^ 3 := by ring
    linarith
  have hc0 : 0 ≤ 1330560 * D ^ 2 := by positivity
  have hcQ : 1 + 1330560 * D ^ 2 ≤ 2 * (2661121 * D ^ 3) := by
    have h2 : D ^ 2 ≤ D ^ 3 := by
      have := mul_le_mul_of_nonneg_left hD1 (sq_nonneg D)
      nlinarith
    have : 1 ≤ D ^ 3 := one_le_pow₀ hD1
    linarith
  have hRQ : D / h ≤ 2661121 * D ^ 3 / h := div_le_div_of_nonneg_right hDQ hh.le
  set Q := 2661121 * D ^ 3 with hQdef
  have hAf : 0 ≤ 8 * Q ^ 2 / Real.sqrt d := by positivity
  -- ball bounds at `τ₀`
  have bGP : ∀ x ∈ w1Ball ct, ∀ z ∈ w1Ball ct,
      |physInv ct.yp (precN ct.G (aOf d p) 1 ct.yp τ₀ ct.S) x z| ≤ D :=
    fun x hx z hz => (w1_g_off_le ct hw hx hz).1
  have bGM : ∀ x ∈ w1Ball ct, ∀ z ∈ w1Ball ct,
      |physInv ct.ym (precN ct.G (aOf d p) (-1) ct.ym τ₀ ct.S) x z| ≤ D :=
    fun x hx z hz => (w1_g_off_le ct hw hx hz).2
  have bXP : ∀ x ∈ w1Ball ct, ∀ z ∈ w1Ball ct,
      |physInv ct.yp (precN ct.G (aOf d p) 1 ct.yp τ₀ ct.S + h • srcDiag ct.yp ct.S) x z| ≤ D :=
    fun x hx z hz => w1_XP_off_le ct hh hw hx hz
  have bXM : ∀ x ∈ w1Ball ct, ∀ z ∈ w1Ball ct,
      |physInv ct.ym (precN ct.G (aOf d p) (-1) ct.ym τ₀ ct.S + h • srcDiag ct.ym ct.S) x z| ≤ D :=
    fun x hx z hz => w1_XM_off_le ct hh hw hx hz
  -- entry jets
  have eGP := fun x z => jb_entry_bounds hpP ct.yp hne hU hθp ha.le ha1 hD1 (w1Ball ct) hiB hjB
    bGP smP x z
  have eGM := fun x z => jb_entry_bounds hpM ct.ym hne hU hθm ha.le ha1 hD1 (w1Ball ct) hiB hjB
    bGM smM x z
  have eXP := fun x z => jb_entry_bounds' hpPX ct.yp hne hU hθp ha.le ha1 hD1 (w1Ball ct) hiB hjB
    bXP smXP x z
  have eXM := fun x z => jb_entry_bounds' hpMX ct.ym hne hU hθm ha.le ha1 hD1 (w1Ball ct) hiB hjB
    bXM smXM x z
  -- row energies at `τ₀`
  have rP : ∀ x ∈ w1Ball ct, ∑ z,
      physInv ct.yp (precN ct.G (aOf d p) 1 ct.yp τ₀ ct.S + h • srcDiag ct.yp ct.S) x z ^ 2 ≤
        D / h := fun x hx => (w1_XP_facts ct hh hw hx).2.2
  have rM : ∀ x ∈ w1Ball ct, ∑ z,
      physInv ct.ym (precN ct.G (aOf d p) (-1) ct.ym τ₀ ct.S + h • srcDiag ct.ym ct.S) x z ^ 2 ≤
        D / h := fun x hx => (w1_XM_facts ct hh hw hx).2.2
  have rPc : ∀ x ∈ w1Ball ct, ∑ z,
      physInv ct.yp (precN ct.G (aOf d p) 1 ct.yp τ₀ ct.S + h • srcDiag ct.yp ct.S) z x ^ 2 ≤
        D / h := fun x hx => by
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun z _ => ?_)) (rP x hx)
    exact congrArg (· ^ 2) (w1_XP_symm ct h τ₀ z x)
  -- H jets
  have hHp : ∃ F, JB U (fun t => (physInv ct.yp (precN ct.G (aOf d p) 1 ct.yp τ₀ ct.S +
      ((t - t₀) * (1 * aOf d p * (Real.sqrt (ct.yp i) * Real.sqrt (ct.yp j)))) •
        SecA.edgeE i j) ct.v ct.v / 2) ^ 2) F (2 * Q ^ 2) (aOf d p * D) := by
    have e := (eGP ct.v ct.v).2.2 hvB hvB
    have m := (e.smul (1 / 2)).mul (e.smul (1 / 2)) (by positivity) (by positivity) hl
    refine ⟨_, (m.congr fun t _ => by ring).mono (le_of_eq ?_) hl⟩
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    ring
  have hHm : ∃ F, JB U (fun t => physInv ct.yp (precN ct.G (aOf d p) 1 ct.yp τ₀ ct.S +
      ((t - t₀) * (1 * aOf d p * (Real.sqrt (ct.yp i) * Real.sqrt (ct.yp j)))) •
        SecA.edgeE i j) ct.v ct.v * physInv ct.ym (precN ct.G (aOf d p) (-1) ct.ym τ₀ ct.S +
      ((t - t₀) * (-1 * aOf d p * (Real.sqrt (ct.ym i) * Real.sqrt (ct.ym j)))) •
        SecA.edgeE i j) ct.v ct.v / 4) F (2 * Q ^ 2) (aOf d p * D) := by
    have m := (((eGP ct.v ct.v).2.2 hvB hvB).mul ((eGM ct.v ct.v).2.2 hvB hvB) hQ0 hQ0 hl).smul
      (1 / 4)
    refine ⟨_, (m.congr fun t _ => by ring).mono (le_of_eq ?_) hl⟩
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
    ring
  -- maskF jets
  have mask : ∀ (Xe Xn : ℝ → Matrix ct.V ct.V ℝ) (Me Mn : Matrix ct.V ct.V ℝ) (f : ℝ → ct.V → ℝ),
      (∀ x z, (x ∈ w1Ball ct → ∃ F, JB U (fun t => Xe t x z) F (|Me x z| + 1330560 * D ^ 2 *
        (|Me i z| + |Me j z|)) (aOf d p * D)) ∧
        (x ∈ w1Ball ct → z ∈ w1Ball ct → ∃ F, JB U (fun t => Xe t x z) F Q (aOf d p * D))) →
      (∀ x z, z ∈ w1Ball ct → ∃ F, JB U (fun t => Xn t x z) F (|Mn x z| + 1330560 * D ^ 2 *
        (|Mn x i| + |Mn x j|)) (aOf d p * D)) →
      (∀ x, ∃ F, JB U (fun t => f t x) F (8 * Q ^ 2 / Real.sqrt d) (aOf d p * D)) →
      (∀ x ∈ w1Ball ct, ∑ z, Me x z ^ 2 ≤ D / h) → (∀ x ∈ w1Ball ct, ∑ z, Mn z x ^ 2 ≤ D / h) →
      ∃ F, JB U (fun t => maskF (Xe t) (Xn t) (f t) j i) F
        (36864 * (8 * Q ^ 2 / Real.sqrt d) * Q ^ 4 / h) (aOf d p * D) := by
    intro Xe Xn Me Mn f he hn hf re rn
    choose FAj hAj using fun x => (he j x).1 hjB
    choose FAi hAi using fun x => (he i x).1 hiB
    choose FB hFB using fun x => hn x i hiB
    choose Ff hFf using hf
    obtain ⟨Fii, hFii⟩ := (he i i).2 hiB hiB
    obtain ⟨Fji, hFji⟩ := (he j i).2 hjB hiB
    exact d3_maskF_jet hl j i hAj hAi hFB hFf hFii hFji (re i hiB) (re j hjB) (rn i hiB)
      (rn j hjB) hc0 hcQ hh hRQ hQ0 hAf
  -- the four configurations
  have hPsi : ∀ (H M : ℝ → ℝ) {FH FM : ℕ → ℝ → ℝ}, JB U H FH (2 * Q ^ 2) (aOf d p * D) →
      JB U M FM (36864 * (8 * Q ^ 2 / Real.sqrt d) * Q ^ 4 / h) (aOf d p * D) →
      ∃ F, JB U (fun t => H t * M t) F (4718592 * Q ^ 8 / (Real.sqrt d * h)) (aOf d p * D) :=
    fun H M FH FM hH hM => ⟨_, (hH.mul hM (by positivity) (by positivity) hl).mono
      (le_of_eq (by field_simp; ring)) hl⟩
  have uMask : ∀ x, ∃ F, JB U (fun _ : ℝ => ct.uvec x) F (8 * Q ^ 2 / Real.sqrt d)
      (aOf d p * D) := fun x => by
    refine ⟨_, (jb_const U (ct.uvec x) hl).mono ?_ hl⟩
    refine (w1_uvec_abs_le ct x).trans ?_
    rw [div_le_div_iff_of_pos_right hsd]
    nlinarith
  have eXPr : ∀ x z, (x ∈ w1Ball ct → ∃ F, JB U (fun t => physInv ct.yp
      (precN ct.G (aOf d p) 1 ct.yp τ₀ ct.S + ((t - t₀) * (1 * aOf d p * (Real.sqrt (ct.yp i) *
        Real.sqrt (ct.yp j)))) • SecA.edgeE i j + h • srcDiag ct.yp ct.S) x z) F
      (|physInv ct.yp (precN ct.G (aOf d p) 1 ct.yp τ₀ ct.S + h • srcDiag ct.yp ct.S) x z| +
        1330560 * D ^ 2 * (|physInv ct.yp (precN ct.G (aOf d p) 1 ct.yp τ₀ ct.S +
          h • srcDiag ct.yp ct.S) i z| + |physInv ct.yp (precN ct.G (aOf d p) 1 ct.yp τ₀ ct.S +
          h • srcDiag ct.yp ct.S) j z|)) (aOf d p * D)) ∧
      (x ∈ w1Ball ct → z ∈ w1Ball ct → ∃ F, JB U (fun t => physInv ct.yp
      (precN ct.G (aOf d p) 1 ct.yp τ₀ ct.S + ((t - t₀) * (1 * aOf d p * (Real.sqrt (ct.yp i) *
        Real.sqrt (ct.yp j)))) • SecA.edgeE i j + h • srcDiag ct.yp ct.S) x z) F Q
        (aOf d p * D)) := fun x z => ⟨(eXP x z).1, (eXP x z).2.2⟩
  have eXMr : ∀ x z, (x ∈ w1Ball ct → ∃ F, JB U (fun t => physInv ct.ym
      (precN ct.G (aOf d p) (-1) ct.ym τ₀ ct.S + ((t - t₀) * (-1 * aOf d p *
        (Real.sqrt (ct.ym i) * Real.sqrt (ct.ym j)))) • SecA.edgeE i j +
          h • srcDiag ct.ym ct.S) x z) F
      (|physInv ct.ym (precN ct.G (aOf d p) (-1) ct.ym τ₀ ct.S + h • srcDiag ct.ym ct.S) x z| +
        1330560 * D ^ 2 * (|physInv ct.ym (precN ct.G (aOf d p) (-1) ct.ym τ₀ ct.S +
          h • srcDiag ct.ym ct.S) i z| + |physInv ct.ym (precN ct.G (aOf d p) (-1) ct.ym τ₀ ct.S +
          h • srcDiag ct.ym ct.S) j z|)) (aOf d p * D)) ∧
      (x ∈ w1Ball ct → z ∈ w1Ball ct → ∃ F, JB U (fun t => physInv ct.ym
      (precN ct.G (aOf d p) (-1) ct.ym τ₀ ct.S + ((t - t₀) * (-1 * aOf d p *
        (Real.sqrt (ct.ym i) * Real.sqrt (ct.ym j)))) • SecA.edgeE i j +
          h • srcDiag ct.ym ct.S) x z) F Q (aOf d p * D)) := fun x z => ⟨(eXM x z).1, (eXM x z).2.2⟩
  have eXPc := fun x z (hz : z ∈ w1Ball ct) => (eXP x z).2.1 hz
  -- the masks `b₊`, `b₋`
  have bPmask : ∀ x, ∃ F, JB U (fun t => obsBP ct (physInv ct.yp
      (precN ct.G (aOf d p) 1 ct.yp τ₀ ct.S + ((t - t₀) * (1 * aOf d p * (Real.sqrt (ct.yp i) *
        Real.sqrt (ct.yp j)))) • SecA.edgeE i j + h • srcDiag ct.yp ct.S)) x) F
      (8 * Q ^ 2 / Real.sqrt d) (aOf d p * D) := fun x => by
    have hq : ∀ m ∈ ct.N, ∃ F, ∃ A, 0 ≤ A ∧ A ≤ 2 * Q ^ 2 ∧ JB U (fun t => (physInv ct.yp
        (precN ct.G (aOf d p) 1 ct.yp τ₀ ct.S + ((t - t₀) * (1 * aOf d p *
          (Real.sqrt (ct.yp i) * Real.sqrt (ct.yp j)))) • SecA.edgeE i j +
            h • srcDiag ct.yp ct.S) m m / 2) ^ 2) F A (aOf d p * D) := fun m hm => by
      obtain ⟨F, hF⟩ := (eXPr m m).2 (w1Ball_N ct hm) (w1Ball_N ct hm)
      have mm := (hF.smul (1 / 2)).mul (hF.smul (1 / 2)) (by positivity) (by positivity) hl
      refine ⟨_, _, by positivity, le_of_eq ?_, mm.congr fun t _ => by ring⟩
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      ring
    choose! Fq Aq hAq0 hAq hFq using hq
    obtain ⟨F, hF⟩ := d3_mask_jet ct hl hd had hFq hAq0 hAq x
    exact ⟨F, hF.congr fun t _ => (obsBP_apply_N ct _ x).symm⟩
  have bMmask : ∀ x, ∃ F, JB U (fun t => obsBM ct (physInv ct.yp
      (precN ct.G (aOf d p) 1 ct.yp τ₀ ct.S + ((t - t₀) * (1 * aOf d p * (Real.sqrt (ct.yp i) *
        Real.sqrt (ct.yp j)))) • SecA.edgeE i j + h • srcDiag ct.yp ct.S)) (physInv ct.ym
      (precN ct.G (aOf d p) (-1) ct.ym τ₀ ct.S + ((t - t₀) * (-1 * aOf d p *
        (Real.sqrt (ct.ym i) * Real.sqrt (ct.ym j)))) • SecA.edgeE i j +
          h • srcDiag ct.ym ct.S)) x) F (8 * Q ^ 2 / Real.sqrt d) (aOf d p * D) := fun x => by
    have hq : ∀ m ∈ ct.N, ∃ F, ∃ A, 0 ≤ A ∧ A ≤ 2 * Q ^ 2 ∧ JB U (fun t => physInv ct.yp
        (precN ct.G (aOf d p) 1 ct.yp τ₀ ct.S + ((t - t₀) * (1 * aOf d p *
          (Real.sqrt (ct.yp i) * Real.sqrt (ct.yp j)))) • SecA.edgeE i j +
            h • srcDiag ct.yp ct.S) m m / 2 * (physInv ct.ym
        (precN ct.G (aOf d p) (-1) ct.ym τ₀ ct.S + ((t - t₀) * (-1 * aOf d p *
          (Real.sqrt (ct.ym i) * Real.sqrt (ct.ym j)))) • SecA.edgeE i j +
            h • srcDiag ct.ym ct.S) m m / 2)) F A (aOf d p * D) := fun m hm => by
      obtain ⟨F, hF⟩ := (eXPr m m).2 (w1Ball_N ct hm) (w1Ball_N ct hm)
      obtain ⟨F', hF'⟩ := (eXMr m m).2 (w1Ball_N ct hm) (w1Ball_N ct hm)
      have mm := (hF.smul (1 / 2)).mul (hF'.smul (1 / 2)) (by positivity) (by positivity) hl
      refine ⟨_, _, by positivity, le_of_eq ?_, mm.congr fun t _ => by ring⟩
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      ring
    choose! Fq Aq hAq0 hAq hFq using hq
    obtain ⟨F, hF⟩ := d3_mask_jet ct hl hd had hFq hAq0 hAq x
    exact ⟨F, hF.congr fun t _ => (obsBM_apply_N ct _ _ x).symm⟩
  match k with
  | 0 =>
    obtain ⟨FH, hH⟩ := hHp
    obtain ⟨FM, hM⟩ := mask _ _ _ _ _ eXPr eXPc uMask rP rPc
    exact hPsi _ _ hH hM
  | 1 =>
    obtain ⟨FH, hH⟩ := hHp
    obtain ⟨FM, hM⟩ := mask _ _ _ _ _ eXPr eXPc bPmask rP rPc
    exact hPsi _ _ hH hM
  | 2 =>
    obtain ⟨FH, hH⟩ := hHm
    obtain ⟨FM, hM⟩ := mask _ _ _ _ _ eXMr eXPc uMask rM rPc
    exact hPsi _ _ hH hM
  | 3 =>
    obtain ⟨FH, hH⟩ := hHm
    obtain ⟨FM, hM⟩ := mask _ _ _ _ _ eXMr eXPc bMmask rM rPc
    exact hPsi _ _ hH hM

end Psi

end BiluLinial.Tight.SecB
