/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecB.W1FibD3Psi2
public import BiluLinial.Tight.SecB.W1FibD3Arith

/-!
# TB.W1fib-d3: the jet of the weight along a regular fibre

At a good endpoint `τ₀` (`64 p a g*(τ₀) ≤ 1`), `det P̃^±(t) = det P̃^±(τ₀) δ_±(t - t₀)`
(`det_add_edge`), so `W(t) = W(τ₀) (δ₊δ₋)^p`. On `|t - t₀| ≤ 3`: `|δ_± - 1| ≤ 1/(16p)`,
`|δ₊'| + |δ₋'| ≤ 2aR + 24a²D²`, `|δ_±^{(r)}| ≤ 4(aD)^r`, hence `g = δ₊δ₋` has `g^{p-r} ≤ 8/7`,
`|g'| ≤ 26κ`, `|g''| ≤ 41(aD)²`, `|g'''| ≤ 96(aD)³` (`κ = aR + a²D²`, `R = |G⁺_ij| + |G⁻_ij|`),
and `jpow_bounds` gives `d3_W_jet`.
-/

@[expose] public section

namespace BiluLinial.Tight.SecB

open Matrix

universe u

/-- One branch: `|δ(s) - 1| ≤ 4ε` and `|δ'(s)| ≤ 2a|k_ij| + 12a²D²`. -/
theorem delta_branch {θ kii kjj kij a D ε s : ℝ} (hθ : |θ| ≤ a) (ha : 0 ≤ a) (hii : 0 ≤ kii)
    (hjj : 0 ≤ kjj) (hij2 : kij ^ 2 ≤ kii * kjj) (hiiD : kii ≤ D) (hjjD : kjj ≤ D)
    (hijD : |kij| ≤ D) (hε : a * (kii + kjj) ≤ ε) (hε1 : ε ≤ 1 / 64) (hs : |s| ≤ 3) :
    |1 + 2 * θ * kij * s + -(θ ^ 2 * (kii * kjj - kij ^ 2)) * s ^ 2 - 1| ≤ 4 * ε ∧
    |2 * θ * kij + 2 * -(θ ^ 2 * (kii * kjj - kij ^ 2)) * s| ≤ 2 * a * |kij| + 12 * a ^ 2 * D ^ 2 := by
  have hθ2 : θ ^ 2 ≤ a ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hθ 2
  have hΔ0 : 0 ≤ kii * kjj - kij ^ 2 := by linarith
  have hΔ : kii * kjj - kij ^ 2 ≤ kii * kjj := by nlinarith [sq_nonneg kij]
  have hkij : |kij| ≤ (kii + kjj) / 2 := abs_le_half_add hii hjj hij2
  have hs2 : s ^ 2 ≤ 9 := by have := sq_abs s; nlinarith [abs_nonneg s]
  have hε0 : 0 ≤ ε := le_trans (by positivity) hε
  refine ⟨?_, ?_⟩
  · have e : 1 + 2 * θ * kij * s + -(θ ^ 2 * (kii * kjj - kij ^ 2)) * s ^ 2 - 1 =
        2 * θ * kij * s + -(θ ^ 2 * (kii * kjj - kij ^ 2)) * s ^ 2 := by ring
    rw [e]
    have a1 : |2 * θ * kij * s| ≤ 3 * ε := by
      rw [abs_mul, abs_mul, abs_mul, abs_two]
      have : |θ| * |kij| ≤ a * ((kii + kjj) / 2) := mul_le_mul hθ hkij (abs_nonneg _) ha
      have h1 : 2 * |θ| * |kij| ≤ ε := by nlinarith
      have := mul_le_mul h1 hs (abs_nonneg _) hε0
      nlinarith
    have a2 : |-(θ ^ 2 * (kii * kjj - kij ^ 2)) * s ^ 2| ≤ 9 / 2 * ε ^ 2 := by
      rw [abs_mul, abs_neg, abs_mul, abs_of_nonneg (sq_nonneg θ), abs_of_nonneg hΔ0,
        abs_of_nonneg (sq_nonneg s)]
      have h1 : kii * kjj ≤ ((kii + kjj) / 2) ^ 2 := by nlinarith [sq_nonneg (kii - kjj)]
      have h2 : θ ^ 2 * (kii * kjj - kij ^ 2) ≤ a ^ 2 * ((kii + kjj) / 2) ^ 2 :=
        mul_le_mul hθ2 (hΔ.trans h1) hΔ0 (sq_nonneg a)
      have h3 : a ^ 2 * ((kii + kjj) / 2) ^ 2 ≤ ε ^ 2 / 4 := by
        have := pow_le_pow_left₀ (by positivity) hε 2
        nlinarith
      have := mul_le_mul (h2.trans h3) hs2 (sq_nonneg s) (by positivity)
      nlinarith
    have := abs_add_le (2 * θ * kij * s) (-(θ ^ 2 * (kii * kjj - kij ^ 2)) * s ^ 2)
    nlinarith
  · have a1 : |2 * θ * kij| ≤ 2 * a * |kij| := by
      rw [abs_mul, abs_mul, abs_two]; nlinarith [abs_nonneg kij]
    have a2 : |2 * -(θ ^ 2 * (kii * kjj - kij ^ 2)) * s| ≤ 12 * a ^ 2 * D ^ 2 := by
      rw [abs_mul, abs_mul, abs_neg, abs_two, abs_mul, abs_of_nonneg (sq_nonneg θ),
        abs_of_nonneg hΔ0]
      have h1 : kii * kjj ≤ D ^ 2 := by nlinarith
      have h2 : θ ^ 2 * (kii * kjj - kij ^ 2) ≤ a ^ 2 * D ^ 2 :=
        mul_le_mul hθ2 (hΔ.trans h1) hΔ0 (sq_nonneg a)
      have := mul_le_mul h2 hs (abs_nonneg s) (by positivity)
      nlinarith
    have := abs_add_le (2 * θ * kij) (2 * -(θ ^ 2 * (kii * kjj - kij ^ 2)) * s)
    linarith

/-- Bounds on the jet of `g = δ₊δ₋`. -/
theorem g_bounds {d0 d1 d2 e0 e1 e2 y κ l : ℝ} (hy : 0 ≤ y) (hy1 : y ≤ 1 / 16)
    (hd0 : |d0 - 1| ≤ y) (he0 : |e0 - 1| ≤ y) (hd1 : |d1| ≤ 4 * l) (he1 : |e1| ≤ 4 * l)
    (hd2 : |d2| ≤ 4 * l ^ 2) (he2 : |e2| ≤ 4 * l ^ 2) (hκ : |d1| + |e1| ≤ 24 * κ) :
    (1 - y) ^ 2 ≤ d0 * e0 ∧ d0 * e0 ≤ (1 + y) ^ 2 ∧ |d1 * e0 + d0 * e1| ≤ 26 * κ ∧
      |d2 * e0 + 2 * (d1 * e1) + d0 * e2| ≤ 41 * l ^ 2 ∧
      |0 * e0 + 3 * (d2 * e1) + 3 * (d1 * e2) + d0 * 0| ≤ 96 * l ^ 3 := by
  obtain ⟨d0l, d0u⟩ := abs_le.mp hd0
  obtain ⟨e0l, e0u⟩ := abs_le.mp he0
  have hd0p : 0 ≤ d0 := by linarith
  have he0p : 0 ≤ e0 := by linarith
  have ad0 : |d0| ≤ 17 / 16 := by rw [abs_of_nonneg hd0p]; linarith
  have ae0 : |e0| ≤ 17 / 16 := by rw [abs_of_nonneg he0p]; linarith
  have hl : 0 ≤ l := by have := (abs_nonneg d1).trans hd1; linarith
  have hκ0 : 0 ≤ κ := by have := add_nonneg (abs_nonneg d1) (abs_nonneg e1); linarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have h1 : 0 ≤ 1 - y := by linarith
    have := mul_le_mul (show 1 - y ≤ d0 by linarith) (show 1 - y ≤ e0 by linarith) h1 hd0p
    linarith [show (1 - y) * (1 - y) = (1 - y) ^ 2 by ring]
  · have := mul_le_mul (show d0 ≤ 1 + y by linarith) (show e0 ≤ 1 + y by linarith) he0p
      (by linarith)
    linarith [show (1 + y) * (1 + y) = (1 + y) ^ 2 by ring]
  · have t1 := w1_abs_mul_le (le_refl |d1|) ae0
    have t2 := w1_abs_mul_le ad0 (le_refl |e1|)
    have := abs_add_le (d1 * e0) (d0 * e1)
    nlinarith
  · have t1 := w1_abs_mul_le hd2 ae0
    have t2 := w1_abs_mul_le hd1 he1
    have t3 := w1_abs_mul_le ad0 he2
    have c2 : |2 * (d1 * e1)| = 2 * |d1 * e1| := by rw [abs_mul, abs_two]
    have := abs_add_le (d2 * e0 + 2 * (d1 * e1)) (d0 * e2)
    have := abs_add_le (d2 * e0) (2 * (d1 * e1))
    nlinarith
  · have t1 := w1_abs_mul_le hd2 he1
    have t2 := w1_abs_mul_le hd1 he2
    have c1 : |3 * (d2 * e1)| = 3 * |d2 * e1| := by rw [abs_mul]; norm_num
    have c2 : |3 * (d1 * e2)| = 3 * |d1 * e2| := by rw [abs_mul]; norm_num
    have e : 0 * e0 + 3 * (d2 * e1) + 3 * (d1 * e2) + d0 * 0 = 3 * (d2 * e1) + 3 * (d1 * e2) := by
      ring
    rw [e]
    have := abs_add_le (3 * (d2 * e1)) (3 * (d1 * e2))
    nlinarith

section W

variable {d p : ℕ} (ct : Contact.{u} d p)

/-- **The jet of the weight** at a good endpoint. -/
theorem d3_W_jet {h : ℝ} (hh : 0 < h) (hR : TRegime d p) {τ₀ : Config ct.V} {i j : ct.V}
    (hi : i ∈ ct.N) (hj : j ∈ nbhd ct.G ct.S i) (hg : fibGood ct i j τ₀) {U : Set ℝ} {t₀ : ℝ}
    (hU : ∀ t ∈ U, |t - t₀| ≤ 3) :
    ∃ F, JetOf U (fun t => ((precN ct.G (aOf d p) 1 ct.yp τ₀ ct.S +
          ((t - t₀) * (1 * aOf d p * (Real.sqrt (ct.yp i) * Real.sqrt (ct.yp j)))) •
            SecA.edgeE i j).det *
        (precN ct.G (aOf d p) (-1) ct.ym τ₀ ct.S +
          ((t - t₀) * (-1 * aOf d p * (Real.sqrt (ct.ym i) * Real.sqrt (ct.ym j)))) •
            SecA.edgeE i j).det) ^ p) F ∧
      ∀ t ∈ U, |F 0 t| ≤ wt ct.G p (aOf d p) ct.yp ct.ym τ₀ ct.S * 3 ∧
        |F 1 t| ≤ wt ct.G p (aOf d p) ct.yp ct.ym τ₀ ct.S * (3 * p * (26 * (aOf d p *
          fibR ct τ₀ i j + aOf d p ^ 2 * ct.Dstar τ₀ ^ 2))) ∧
        |F 2 t| ≤ wt ct.G p (aOf d p) ct.yp ct.ym τ₀ ct.S * (3 * p ^ 2 * (26 * (aOf d p *
          fibR ct τ₀ i j + aOf d p ^ 2 * ct.Dstar τ₀ ^ 2)) ^ 2 +
            3 * p * (41 * (aOf d p * ct.Dstar τ₀) ^ 2)) ∧
        |F 3 t| ≤ wt ct.G p (aOf d p) ct.yp ct.ym τ₀ ct.S * (3 * p ^ 3 * (26 * (aOf d p *
          fibR ct τ₀ i j + aOf d p ^ 2 * ct.Dstar τ₀ ^ 2)) ^ 3 +
            9 * p ^ 2 * ((26 * (aOf d p * fibR ct τ₀ i j + aOf d p ^ 2 * ct.Dstar τ₀ ^ 2)) *
              (41 * (aOf d p * ct.Dstar τ₀) ^ 2)) +
            3 * p * (96 * (aOf d p * ct.Dstar τ₀) ^ 3)) := by
  obtain ⟨hw, hG⟩ := hg
  have hp3 : 3 ≤ p := le_trans (by norm_num) hR.hp
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast le_trans (by norm_num) hp3
  have hij : ct.G.Adj i j := (Finset.mem_filter.mp hj).2
  have hne : i ≠ j := ct.G.ne_of_adj hij
  have hiB := w1Ball_N ct hi
  have hjB := w1Ball_NN ct hi hj
  have hD1 := w1_Dstar_ge_one ct hw
  have ha := hR.aOf_pos
  obtain ⟨hpP, hpM⟩ := posDef_of_wt_ne_zero ct.G hw
  have hyp : ∀ k, 0 ≤ ct.yp k := fun k => (ct.ctx.hyp k).1
  have hym : ∀ k, 0 ≤ ct.ym k := fun k => (ct.ctx.hym k).1
  obtain ⟨smP, smM, -, -⟩ := d3_small ct hh (le_trans (by norm_num) hp3) ⟨hw, hG⟩
  have hθp : |1 * aOf d p| ≤ aOf d p := by rw [one_mul, abs_of_pos ha]
  have hθm : |-1 * aOf d p| ≤ aOf d p := by rw [neg_one_mul, abs_neg, abs_of_pos ha]
  obtain ⟨gi1, gi2⟩ := w1_gp_nonneg ct hw i
  obtain ⟨gj1, gj2⟩ := w1_gp_nonneg ct hw j
  have bP := fun x z (hx : x ∈ w1Ball ct) (hz : z ∈ w1Ball ct) => (w1_g_off_le ct hw hx hz).1
  have bM := fun x z (hx : x ∈ w1Ball ct) (hz : z ∈ w1Ball ct) => (w1_g_off_le ct hw hx hz).2
  -- `p`-scaled smallness
  set ε := 1 / (64 * (p : ℝ)) with hε
  have hε1 : ε ≤ 1 / 64 := by
    rw [hε]; exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have hag : aOf d p * fibG ct τ₀ i j ≤ ε := by
    rw [hε, le_div_iff₀ (by positivity : (0 : ℝ) < 64 * p)]
    calc aOf d p * fibG ct τ₀ i j * (64 * p) = 64 * p * aOf d p * fibG ct τ₀ i j := by ring
      _ ≤ 1 := hG
  have hag' : aOf d p * ct.gp τ₀ i i + aOf d p * ct.gp τ₀ j j + aOf d p * ct.gm τ₀ i i +
      aOf d p * ct.gm τ₀ j j ≤ ε := by
    have e : aOf d p * fibG ct τ₀ i j = aOf d p * ct.gp τ₀ i i + aOf d p * ct.gp τ₀ j j +
        aOf d p * ct.gm τ₀ i i + aOf d p * ct.gm τ₀ j j := by unfold fibG; ring
    linarith
  have n1 := mul_nonneg ha.le gi1
  have n2 := mul_nonneg ha.le gj1
  have n3 := mul_nonneg ha.le gi2
  have n4 := mul_nonneg ha.le gj2
  have hεP : aOf d p * (ct.gp τ₀ i i + ct.gp τ₀ j j) ≤ ε := by rw [mul_add]; linarith
  have hεM : aOf d p * (ct.gm τ₀ i i + ct.gm τ₀ j j) ≤ ε := by rw [mul_add]; linarith
  -- the jets of `δ_±`
  have hjp := jetOf_quad U 1 (2 * (1 * aOf d p) * ct.gp τ₀ i j)
    (-((1 * aOf d p) ^ 2 * (ct.gp τ₀ i i * ct.gp τ₀ j j - ct.gp τ₀ i j ^ 2))) t₀
  have hjm := jetOf_quad U 1 (2 * (-1 * aOf d p) * ct.gm τ₀ i j)
    (-((-1 * aOf d p) ^ 2 * (ct.gm τ₀ i i * ct.gm τ₀ j j - ct.gm τ₀ i j ^ 2))) t₀
  have hJ := ((hjp.mul hjm).pow hp3).smul (wt ct.G p (aOf d p) ct.yp ct.ym τ₀ ct.S)
  refine ⟨_, hJ.congr fun t _ => ?_, fun t ht => ?_⟩
  · have e : ∀ A B C D : ℝ, (A * B * (C * D)) ^ p = (A * C) ^ p * (B * D) ^ p :=
      fun A B C D => by rw [← mul_pow]; ring
    rw [det_add_edge hpP ct.yp hne, det_add_edge hpM ct.ym hne, e, wt, if_pos ⟨hpP, hpM⟩]
    rfl
  · have hs := hU t ht
    obtain ⟨dp0, dp1⟩ := delta_branch (s := t - t₀) (D := ct.Dstar τ₀) (ε := ε)
      (kii := ct.gp τ₀ i i) (kjj := ct.gp τ₀ j j) (kij := ct.gp τ₀ i j) hθp ha.le gi1 gj1
      (greenP_sq_le ct.G hpP hyp i j) (by linarith [(w1_diag_le_Dstar ct hiB τ₀).1])
      (by linarith [(w1_diag_le_Dstar ct hjB τ₀).1]) (bP i j hiB hjB) hεP hε1 hs
    obtain ⟨dm0, dm1⟩ := delta_branch (s := t - t₀) (D := ct.Dstar τ₀) (ε := ε)
      (kii := ct.gm τ₀ i i) (kjj := ct.gm τ₀ j j) (kij := ct.gm τ₀ i j) hθm ha.le gi2 gj2
      (greenP_sq_le ct.G hpM hym i j) (by linarith [(w1_diag_le_Dstar ct hiB τ₀).2])
      (by linarith [(w1_diag_le_Dstar ct hjB τ₀).2]) (bM i j hiB hjB) hεM hε1 hs
    obtain ⟨-, rp⟩ := dJ_bounds hU hθp ha.le hD1 (bP i i hiB hiB) (bP j j hjB hjB)
      (bP i j hiB hjB) smP
    obtain ⟨-, rm⟩ := dJ_bounds hU hθm ha.le hD1 (bM i i hiB hiB) (bM j j hjB hjB)
      (bM i j hiB hjB) smM
    set dP := dJ (1 * aOf d p) (ct.gp τ₀ i i) (ct.gp τ₀ j j) (ct.gp τ₀ i j) t₀ with hdP
    set dM := dJ (-1 * aOf d p) (ct.gm τ₀ i i) (ct.gm τ₀ j j) (ct.gm τ₀ i j) t₀ with hdM
    have rp1 : |dP 1 t| ≤ 4 * (aOf d p * ct.Dstar τ₀) := by
      simpa using rp 1 le_rfl (by norm_num) t ht
    have rp2 := rp 2 (by norm_num) (by norm_num) t ht
    have rm1 : |dM 1 t| ≤ 4 * (aOf d p * ct.Dstar τ₀) := by
      simpa using rm 1 le_rfl (by norm_num) t ht
    have rm2 := rm 2 (by norm_num) (by norm_num) t ht
    have dp0' : |dP 0 t - 1| ≤ 4 * ε := dp0
    have dm0' : |dM 0 t - 1| ≤ 4 * ε := dm0
    have dp1' : |dP 1 t| ≤ 2 * aOf d p * |ct.gp τ₀ i j| + 12 * aOf d p ^ 2 * ct.Dstar τ₀ ^ 2 :=
      dp1
    have dm1' : |dM 1 t| ≤ 2 * aOf d p * |ct.gm τ₀ i j| + 12 * aOf d p ^ 2 * ct.Dstar τ₀ ^ 2 :=
      dm1
    have hy0 : 0 ≤ 4 * ε := by positivity
    have hy1 : 4 * ε ≤ 1 / 16 := by linarith
    have hκ : |dP 1 t| + |dM 1 t| ≤
        24 * (aOf d p * fibR ct τ₀ i j + aOf d p ^ 2 * ct.Dstar τ₀ ^ 2) := by
      unfold fibR
      have h0 : 0 ≤ aOf d p * |ct.gp τ₀ i j| := mul_nonneg ha.le (abs_nonneg _)
      have h0' : 0 ≤ aOf d p * |ct.gm τ₀ i j| := mul_nonneg ha.le (abs_nonneg _)
      have e : aOf d p * (|ct.gp τ₀ i j| + |ct.gm τ₀ i j|) =
          aOf d p * |ct.gp τ₀ i j| + aOf d p * |ct.gm τ₀ i j| := by ring
      linarith
    obtain ⟨g0l, g0u, g1b, g2b, g3b⟩ := g_bounds hy0 hy1 dp0' dm0' rp1 rm1 rp2 rm2 hκ
    have hG0 : jmul dP dM 0 t = dP 0 t * dM 0 t := rfl
    have hg0 : 0 ≤ jmul dP dM 0 t := by rw [hG0]; exact le_trans (sq_nonneg _) g0l
    have hpow : ∀ r ≤ 3, jmul dP dM 0 t ^ (p - r) ≤ 3 := by
      intro r _
      rw [hG0]
      have hb1 : 1 ≤ (1 + 4 * ε) ^ 2 := one_le_pow₀ (by linarith)
      have h1 := pow_le_pow_left₀ (by rw [← hG0]; exact hg0) g0u (p - r)
      have h2 : ((1 + 4 * ε) ^ 2) ^ (p - r) ≤ ((1 + 4 * ε) ^ 2) ^ p :=
        pow_le_pow_right₀ hb1 (by omega)
      have h3 : ((1 + 4 * ε) ^ 2) ^ p = (1 + 4 * ε) ^ (2 * p) := by rw [← pow_mul]
      have hmy : ((2 * p : ℕ) : ℝ) * (4 * ε) = 1 / 8 := by
        rw [hε]; push_cast; field_simp; ring
      have h4 := one_add_pow_le (m := 2 * p) (by omega) hy0 (by rw [hmy]; norm_num)
      rw [hmy] at h4
      norm_num at h4
      linarith
    obtain ⟨j0, j1, j2, j3⟩ := jpow_bounds (jmul dP dM) hp3 t hg0 hpow g1b g2b g3b
    have hW0 : 0 ≤ wt ct.G p (aOf d p) ct.yp ct.ym τ₀ ct.S := wt_nonneg ct.G τ₀
    simp only [jsmul, abs_mul, abs_of_nonneg hW0]
    exact ⟨mul_le_mul_of_nonneg_left j0 hW0, mul_le_mul_of_nonneg_left j1 hW0,
      mul_le_mul_of_nonneg_left j2 hW0, mul_le_mul_of_nonneg_left j3 hW0⟩

end W

end BiluLinial.Tight.SecB
