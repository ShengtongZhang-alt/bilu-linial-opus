/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecB.WTRemMom

/-!
# Parameter arithmetic of TB.WT5r°

* `params_of`: with `a = m₀ + 3`, `log d ≥ 128 a`, `p ≥ 100 a` and `0 < h ≤ p⁻⁴`, the order
  `N = 4k_* + 4` satisfies the conditions `Params` of the derivative bounds, and the moment order
  `2 (|l| + 3)(2k_* + 3) ≤ p` holds (`k_* ≤ p/(8a) + 1`).
* `final_bound`: `2 M_m e^{-p}/d · F ≤ F/d^{M+1}` for the moment constant
  `M_m = C_m (2(2|R|+1)(1+2ε))^{|l|+3} ≤ 1280 · 2^{m₀} 30^{m₀+3} d^{m₀+6}`, once
  `p ≥ (M + m₀ + 7) log d`, `1/d ≤ h`, `d ≥ 2 · 1280 · 2^{m₀} 30^{m₀+3}` and `d ≥ 2m₀ + 1`.
-/

@[expose] public section

namespace BiluLinial.Tight.SecB.WR

theorem eventually_log_ge (L : ℝ) : Eventually fun _ _ d _ _ => L ≤ Real.log d := by
  intro c₀ κ₀ _ _ _ _
  refine ⟨⌈Real.exp L⌉₊ + 1, fun d hd => ?_⟩
  have h1 : Real.exp L ≤ d := by
    have h2 := Nat.le_ceil (Real.exp L)
    have h3 : ((⌈Real.exp L⌉₊ + 1 : ℕ) : ℝ) ≤ d := by exact_mod_cast hd
    push_cast at h3
    linarith
  calc L = Real.log (Real.exp L) := (Real.log_exp L).symm
    _ ≤ Real.log d := Real.log_le_log (Real.exp_pos L) h1

theorem eventually_d_ge (X : ℝ) : Eventually fun _ _ d _ _ => X ≤ (d : ℝ) := by
  intro c₀ κ₀ _ _ _ _
  refine ⟨⌈X⌉₊, fun d hd => ?_⟩
  have h2 := Nat.le_ceil X
  have h3 : ((⌈X⌉₊ : ℕ) : ℝ) ≤ d := by exact_mod_cast hd
  linarith

theorem exp_half_le_two : Real.exp (1 / 2) ≤ 2 := by
  have h1 : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have h2 := Real.exp_one_lt_d9
  have h3 := Real.exp_pos (1 / 2)
  nlinarith

theorem params_of {d p : ℕ} (hR : RegA d p) {m₀ : ℕ}
    (hlog : 128 * ((m₀ : ℝ) + 3) ≤ Real.log d) (hB : 100 * ((m₀ : ℝ) + 3) ≤ p) {h : ℝ}
    (hh : 0 < h) (hhp : h ≤ 1 / (p : ℝ) ^ 4) {T : Type*} (l : List (T × Bool × Bool))
    (hl : l.length ≤ m₀) :
    Params h p (4 * kStarA d p + 4) l ∧ 2 * ((l.length + 3) * (2 * kStarA d p + 3)) ≤ p := by
  have hlogp := hR.log_pos
  have hp1 := hR.one_le_p
  set K := kStarA d p with hKdef
  set a : ℝ := (m₀ : ℝ) + 3 with ha
  have ha3 : 3 ≤ a := by rw [ha]; linarith [(Nat.cast_nonneg m₀ : (0 : ℝ) ≤ m₀)]
  have hK : (K : ℝ) < (p : ℝ) / (8 * a) + 1 := by
    have h1 : (K : ℝ) < 16 * (p : ℝ) / Real.log d + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have h2 : 16 * (p : ℝ) / Real.log d ≤ (p : ℝ) / (8 * a) := by
      rw [div_le_div_iff₀ hlogp (by positivity)]
      nlinarith
    linarith
  have hK8 : 8 * a * (K : ℝ) < p + 8 * a := by
    have h8 : (0 : ℝ) < 8 * a := by positivity
    have e : 8 * a * ((p : ℝ) / (8 * a)) = p := by field_simp
    have := mul_lt_mul_of_pos_left hK h8
    linarith
  have hlr : (l.length : ℝ) ≤ m₀ := by exact_mod_cast hl
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
  have hc1 : cntK (fun t : T × Bool × Bool => t.2) (true, false) l ≤ l.length :=
    List.countP_le_length
  have hc2 : cntK (fun t : T × Bool × Bool => t.2) (false, false) l ≤ l.length :=
    List.countP_le_length
  -- `2 m₀ + 8 + 4K ≤ p`
  have h24 : 24 * (K : ℝ) ≤ 8 * a * K := by nlinarith
  have hC2r : 2 * (m₀ : ℝ) + 8 + 4 * K ≤ p := by linarith
  have hC2 : 2 * m₀ + 8 + 4 * K ≤ p := by exact_mod_cast hC2r
  have hE1 : l.length + 4 + (4 * K + 4) ≤ eOne p l := by unfold eOne; omega
  have hE2 : l.length + 4 + (4 * K + 4) ≤ eTwo p l := by unfold eTwo; omega
  have he1 : (eOne p l : ℝ) ≤ p := by exact_mod_cast Nat.sub_le _ _
  have he2 : (eTwo p l : ℝ) ≤ p := by exact_mod_cast Nat.sub_le _ _
  refine ⟨⟨by omega, hE1, hE2, ?_, ?_⟩, ?_⟩
  · push_cast
    linarith
  · have hn : ((l.length + 4 + (4 * K + 4) : ℕ) : ℝ) ≤ p := by
      exact_mod_cast (by omega : l.length + 4 + (4 * K + 4) ≤ p)
    have hexp := SecA.one_add_pow_le_exp (by linarith : (0 : ℝ) ≤ 2 * h) hn
    have hp300 : (300 : ℝ) ≤ p := by linarith
    have hp4 : (p : ℝ) ^ 4 ≥ 4 * p := by
      have h3 : (300 : ℝ) ^ 3 ≤ (p : ℝ) ^ 3 := pow_le_pow_left₀ (by norm_num) hp300 3
      have e : (p : ℝ) ^ 4 = (p : ℝ) ^ 3 * p := by ring
      rw [e]
      nlinarith
    have h2hp : 2 * h * p ≤ 1 / 2 := by
      have : h * (p : ℝ) ^ 4 ≤ 1 := by
        rw [le_div_iff₀ (by positivity)] at hhp
        linarith
      nlinarith
    exact hexp.trans ((Real.exp_le_exp.2 h2hp).trans exp_half_le_two)
  · have hC1r : 2 * (((l.length : ℝ) + 3) * (2 * K + 3)) ≤ p := by
      have h1 : ((l.length : ℝ) + 3) ≤ a := by rw [ha]; linarith
      have h2 : ((l.length : ℝ) + 3) * (2 * K + 3) ≤ a * (2 * K + 3) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
      have h3 : a * (2 * K + 3) = 2 * (a * K) + 3 * a := by ring
      have h4 : 8 * a * (K : ℝ) = 8 * (a * K) := by ring
      linarith
    exact_mod_cast hC1r

theorem final_bound {d p : ℕ} (hR : RegA d p) {m₀ M : ℕ}
    (hd2 : 2 * (1280 * 2 ^ m₀ * 30 ^ (m₀ + 3)) ≤ (d : ℝ)) (hdm : 2 * (m₀ : ℝ) + 4 ≤ d)
    (hpl : ((M : ℝ) + m₀ + 7) * Real.log d ≤ p) {h : ℝ} (hh : 0 < h) (hhd : 1 / (d : ℝ) ≤ h)
    {n r : ℕ} (hn : n ≤ m₀) (hr : r ≤ 2 * d + n) {F : ℝ} (hF : 0 ≤ F) :
    2 * (Cm h d p n * (2 * (2 * r + 1) * (1 + 2 * epsP d p)) ^ (n + 3) *
      Real.exp (-(p : ℝ)) / d * F) ≤ F / (d : ℝ) ^ (M + 1) := by
  have hd := hR.d_pos
  have hd1 : (1 : ℝ) ≤ d := by linarith
  have hp1 := hR.one_le_p
  have hε0 := SecA.epsP_nonneg hR.treg
  have hε1 : epsP d p ≤ 1 := hR.epsP_le_u.trans hR.uOf_le_one
  have hnr : (n : ℝ) ≤ m₀ := by exact_mod_cast hn
  have hrr : (r : ℝ) ≤ 2 * d + n := by exact_mod_cast hr
  -- `C_m ≤ 1280 · 2^{m₀} d³`
  have hih : 1 / h ≤ d := by
    rw [div_le_iff₀ hh]
    rw [div_le_iff₀ hd] at hhd
    linarith
  have hih0 : 0 ≤ 1 / h := by positivity
  have hRs : RsqOf d p + 1 ≤ 5 * d := by
    unfold RsqOf qOf ΔOf
    have : 4 / (p : ℝ) ≤ 4 := by rw [div_le_iff₀ (by linarith)]; linarith
    linarith
  have hRs0 : 0 ≤ RsqOf d p + 1 := by have := hR.treg.RsqOf_pos; linarith
  have h2n : (2 : ℝ) ^ n ≤ 2 ^ m₀ := pow_le_pow_right₀ (by norm_num) hn
  have hCm : Cm h d p n ≤ 1280 * 2 ^ m₀ * (d : ℝ) ^ 3 := by
    unfold Cm
    have e : 128 * 2 ^ n * (RsqOf d p + 1) * (1 / h + 4) / (h ^ 2 * d) =
        128 * 2 ^ n * (RsqOf d p + 1) * (1 / h + 4) * (1 / h) ^ 2 / d := by
      field_simp
    rw [e, div_le_iff₀ hd]
    have h14 : 1 / h + 4 ≤ 2 * d := by linarith
    have hsq : (1 / h) ^ 2 ≤ (d : ℝ) ^ 2 := pow_le_pow_left₀ hih0 hih 2
    calc 128 * 2 ^ n * (RsqOf d p + 1) * (1 / h + 4) * (1 / h) ^ 2
        ≤ 128 * 2 ^ m₀ * (5 * d) * (2 * d) * (d : ℝ) ^ 2 := by gcongr
      _ = 1280 * 2 ^ m₀ * (d : ℝ) ^ 3 * d := by ring
  -- `M_X ≤ 30 d`
  have hMX : 2 * (2 * (r : ℝ) + 1) * (1 + 2 * epsP d p) ≤ 30 * d := by
    have h1 : 2 * (r : ℝ) + 1 ≤ 5 * d := by linarith
    have h2 : 1 + 2 * epsP d p ≤ 3 := by linarith
    calc 2 * (2 * (r : ℝ) + 1) * (1 + 2 * epsP d p) ≤ 2 * (5 * d) * 3 := by gcongr
      _ = 30 * d := by ring
  have hMX0 : 0 ≤ 2 * (2 * (r : ℝ) + 1) * (1 + 2 * epsP d p) := by positivity
  have hpow : (2 * (2 * (r : ℝ) + 1) * (1 + 2 * epsP d p)) ^ (n + 3) ≤
      (30 * (d : ℝ)) ^ (m₀ + 3) :=
    (pow_le_pow_left₀ hMX0 hMX _).trans (pow_le_pow_right₀ (by linarith) (by omega))
  -- `e^{-p} ≤ d^{-(M + m₀ + 7)}`
  have hexp : Real.exp (-(p : ℝ)) ≤ 1 / (d : ℝ) ^ (M + m₀ + 7) := by
    have e1 : Real.exp (((M + m₀ + 7 : ℕ) : ℝ) * Real.log d) = (d : ℝ) ^ (M + m₀ + 7) := by
      rw [Real.exp_nat_mul, Real.exp_log hd]
    rw [one_div, ← e1, ← Real.exp_neg]
    refine Real.exp_le_exp.2 ?_
    push_cast
    linarith
  have hCm0 := Cm_nonneg hh hR.treg n
  set C₀ : ℝ := 1280 * 2 ^ m₀ * 30 ^ (m₀ + 3) with hC₀
  have hMm : Cm h d p n * (2 * (2 * (r : ℝ) + 1) * (1 + 2 * epsP d p)) ^ (n + 3) ≤
      C₀ * (d : ℝ) ^ (m₀ + 6) := by
    calc Cm h d p n * (2 * (2 * (r : ℝ) + 1) * (1 + 2 * epsP d p)) ^ (n + 3)
        ≤ (1280 * 2 ^ m₀ * (d : ℝ) ^ 3) * (30 * (d : ℝ)) ^ (m₀ + 3) :=
          mul_le_mul hCm hpow (by positivity) (by positivity)
      _ = C₀ * (d : ℝ) ^ (m₀ + 6) := by
          rw [hC₀, mul_pow]
          ring
  have hMm0 : 0 ≤ Cm h d p n * (2 * (2 * (r : ℝ) + 1) * (1 + 2 * epsP d p)) ^ (n + 3) := by
    positivity
  have hdpos : (0 : ℝ) < (d : ℝ) ^ (M + m₀ + 7) := by positivity
  calc 2 * (Cm h d p n * (2 * (2 * r + 1) * (1 + 2 * epsP d p)) ^ (n + 3) *
        Real.exp (-(p : ℝ)) / d * F)
      ≤ 2 * (C₀ * (d : ℝ) ^ (m₀ + 6) * (1 / (d : ℝ) ^ (M + m₀ + 7)) / d * F) := by
        gcongr
    _ = 2 * C₀ * F / (d : ℝ) ^ (M + 2) := by
        field_simp
        ring
    _ ≤ d * F / (d : ℝ) ^ (M + 2) := by
        gcongr
    _ = F / (d : ℝ) ^ (M + 1) := by
        field_simp
        ring

end BiluLinial.Tight.SecB.WR
