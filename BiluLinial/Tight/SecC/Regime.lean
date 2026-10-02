/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecC.Defs

/-!
# Regime facts for Section 1.4 (node PD of `docs/tight/BP_SECC.md`)

AUDIT-C §2 (R1–R9). Pure real inequalities, either under `TRegime d p` or as `Eventually`
statements at `p = ⌊c₀ d^{2/17}⌋`, `h = κ₀ p^{-4}`.

* `TRegime.d_aOf_sq` (R2): `1/4 ≤ d a² ≤ 1/2` (from `a⁻² = 4(d-1) + 4/p`).
* `TRegime.sOf_le_three` (R3): `s ≤ 3` (from `τ_* ≤ 1/q ≤ 1/3`).
* `TRegime.pow_le_d` (R1, R7): `p^k ≤ d` for `k ≤ 8` (from `p^17 ≤ d²`).
* `eventually_log_le` (R1): `K log d ≤ p` for any fixed `K` (`log d = o(d^{2/17})`).
* `eventually_kStar` (R1): `2 (8 k_* + 12) ≤ p`, hence `4 k_* + 4 ≤ p - 3` and moments of order
  `8 k_* + 12 ≤ p/2` (`k_* ≤ 16p/log d + 1`, `log d ≥ 512`).
* `vth_rpow_neg_le` (R8): `ϑ^{-1/k} ≤ e` for `k ≥ 10 log d`.
* `eventually_exp_absorb` (R8): `(8dp + 24 p² d^{10}) e^{-3p} ≤ e^{-2p}` (`p ≥ 13 log d`).
* `eventually_E6` (R9, exponent 4): `p 40^p (C p)^{4k_*+4} d^{-k_*} ≤ e^{-4p}` for every fixed
  `C ≥ 1`. Proof: `(Cp)^8 ≤ d` (from `p^17 ≤ d²`, `p ≥ C^{16}`), so
  `(Cp)^{4k}/d^k ≤ d^{-k/2} ≤ e^{-8p}` (`k ≥ 16p/log d`); `40 ≤ e^{3.9}`; and
  `p (Cp)^4 ≤ e^{p/10}` for `p ≥ 7!·10^6 C^4`. The source's exponent tends to `-4.78 p`
  (AUDIT-C §0.5); exponent `4` leaves room for the `d^{20}` envelopes of T.TRC.
-/

@[expose] public section

namespace BiluLinial.Tight

namespace SecC

open Real

variable {d p : ℕ}

/-- The base regime at `p = ⌊c₀ d^{2/17}⌋` with `p ≥ B`. -/
theorem eventually_regime (B : ℝ) : Eventually fun _ _ d p _ =>
    TRegime d p ∧ B ≤ (p : ℝ) ∧ (p : ℝ) ^ 17 ≤ (d : ℝ) ^ 2 := by
  intro c₀ κ₀ hc0 hc1 _ _
  obtain ⟨D₁, hD₁⟩ := exists_tRegime_pAt hc0 hc1
  obtain ⟨D₂, hD₂⟩ := exists_base_ge hc0 (2 * |B| + 2)
  refine ⟨max D₁ D₂, fun d hd => ?_⟩
  obtain ⟨hR, hb⟩ := hD₁ d (le_of_max_le_left hd)
  have hb2 := hD₂ d (le_of_max_le_right hd)
  have hp := half_base_le_pAt hb
  refine ⟨hR, ?_, ?_⟩
  · have := le_abs_self B
    linarith
  · exact_mod_cast hR.hpd

/-- `p⁸ ≤ d` (from `p^16 ≤ p^17 ≤ d²`). -/
theorem TRegime.p8_le (hR : TRegime d p) : (p : ℝ) ^ 8 ≤ d := by
  have hp1 : (1 : ℝ) ≤ p := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hR.two_le_p
    linarith
  have h17 : (p : ℝ) ^ 17 ≤ (d : ℝ) ^ 2 := by exact_mod_cast hR.hpd
  have h16 : ((p : ℝ) ^ 8) ^ 2 ≤ (d : ℝ) ^ 2 := by
    calc ((p : ℝ) ^ 8) ^ 2 = (p : ℝ) ^ 16 := by ring
      _ ≤ (p : ℝ) ^ 17 := pow_le_pow_right₀ hp1 (by norm_num)
      _ ≤ (d : ℝ) ^ 2 := h17
  exact (pow_le_pow_iff_left₀ (by positivity) (Nat.cast_nonneg d) (by norm_num)).mp h16

/-- R2: `1/4 ≤ d a² ≤ 1/2`. -/
theorem TRegime.d_aOf_sq (hR : TRegime d p) :
    1 / 4 ≤ (d : ℝ) * aOf d p ^ 2 ∧ (d : ℝ) * aOf d p ^ 2 ≤ 1 / 2 := by
  have hRs := hR.RsqOf_pos
  have hd := hR.ten_pow_six_le_d
  have hΔ := hR.ΔOf_pos
  have hΔ2 := hR.ΔOf_le_two
  have e : RsqOf d p = 4 * ((d : ℝ) - 1) + ΔOf p := rfl
  rw [hR.aOf_sq, mul_one_div]
  constructor
  · rw [le_div_iff₀ hRs, e]
    linarith
  · rw [div_le_iff₀ hRs, e]
    linarith

/-- R3: `s ≤ 3`. -/
theorem TRegime.sOf_le_three (hR : TRegime d p) : sOf d p ≤ 3 := by
  have hq : (3 : ℝ) ≤ qOf d := by
    have := hR.ten_pow_six_le_d
    unfold qOf
    linarith
  have hη := hR.η0Of_pos
  have hτ : τsOf d p ≤ 1 / 3 := by
    rw [τsOf, div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  rw [sOf, hR.one_add_qOf_mul_τsOf, div_le_iff₀ (by linarith)]
  linarith

/-- R1/R7: `p^k ≤ d` for `k ≤ 8`. -/
theorem TRegime.pow_le_d (hR : TRegime d p) {k : ℕ} (hk : k ≤ 8) : (p : ℝ) ^ k ≤ d := by
  have hp1 : (1 : ℝ) ≤ p := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hR.two_le_p
    linarith
  exact (pow_le_pow_right₀ hp1 hk).trans (TRegime.p8_le hR)

/-- R1: `K log d ≤ p` for large `d`. -/
theorem eventually_log_le (K : ℝ) : Eventually fun _ _ d p _ => K * Real.log d ≤ p := by
  intro c₀ κ₀ hc0 hc1 _ _
  have hK : 0 < |K| + 1 := by positivity
  have hlo := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 17)).bound
    (show 0 < c₀ / (2 * (|K| + 1)) by positivity)
  have hev : ∀ᶠ n : ℕ in Filter.atTop,
      ‖Real.log n‖ ≤ c₀ / (2 * (|K| + 1)) * ‖(n : ℝ) ^ ((2 : ℝ) / 17)‖ :=
    tendsto_natCast_atTop_atTop.eventually hlo
  obtain ⟨D₁, hD₁⟩ := Filter.eventually_atTop.mp hev
  obtain ⟨D₂, hD₂⟩ := exists_base_ge hc0 1
  refine ⟨max D₁ (max D₂ 1), fun d hd => ?_⟩
  have h1 := hD₁ d (le_of_max_le_left hd)
  have hb := hD₂ d (le_trans (le_max_left _ _) (le_of_max_le_right hd))
  have hd1 : 1 ≤ d := le_trans (le_max_right _ _) (le_of_max_le_right hd)
  have hp := half_base_le_pAt hb
  have hlog0 : 0 ≤ Real.log d := Real.log_nonneg (by exact_mod_cast hd1)
  rw [Real.norm_of_nonneg hlog0,
    Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)] at h1
  calc K * Real.log d ≤ (|K| + 1) * Real.log d := by nlinarith [le_abs_self K]
    _ ≤ (|K| + 1) * (c₀ / (2 * (|K| + 1)) * (d : ℝ) ^ ((2 : ℝ) / 17)) := by gcongr
    _ = c₀ * (d : ℝ) ^ ((2 : ℝ) / 17) / 2 := by field_simp
    _ ≤ pAt c₀ d := hp

/-- `log d ≥ B` for large `d`. -/
theorem eventually_le_log (B : ℝ) : Eventually fun _ _ d _ _ => B ≤ Real.log d := by
  intro c₀ κ₀ _ _ _ _
  refine ⟨⌈Real.exp B⌉₊, fun d hd => ?_⟩
  have h1 : Real.exp B ≤ d := (Nat.le_ceil _).trans (by exact_mod_cast hd)
  have h0 : 0 < (d : ℝ) := lt_of_lt_of_le (Real.exp_pos B) h1
  exact (Real.le_log_iff_exp_le h0).mpr h1

/-- R1: `2 (8 k_* + 12) ≤ p` (so `4 k_* + 4 ≤ p - 3` and `8 k_* + 12 ≤ p/2`). -/
theorem eventually_kStar : Eventually fun _ _ d p _ => 2 * (8 * kStar d p + 12) ≤ p := by
  refine ((eventually_regime 80).and (eventually_le_log 512)).mono ?_
  rintro c₀ κ₀ d p h ⟨⟨hR, hp80, -⟩, hL⟩
  have hL0 : 0 < Real.log d := by linarith
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hk : (kStar d p : ℝ) < 16 * p / Real.log d + 1 :=
    Nat.ceil_lt_add_one (div_nonneg (by positivity) hL0.le)
  have h16 : 16 * (p : ℝ) / Real.log d ≤ p / 32 := by
    rw [div_le_div_iff₀ hL0 (by norm_num)]
    nlinarith
  have : (2 * (8 * kStar d p + 12) : ℝ) ≤ p := by nlinarith
  exact_mod_cast this

/-- R8: `ϑ^{-1/k} ≤ e` for `k ≥ 10 log d` (`ϑ = d^{-10}`). -/
theorem vth_rpow_neg_le (hd : 1 ≤ d) {k : ℝ} (hk : 0 < k) (hkd : 10 * Real.log d ≤ k) :
    vth d ^ (-(1 / k)) ≤ Real.exp 1 := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hv : 0 < vth d := by unfold vth; positivity
  rw [Real.rpow_def_of_pos hv]
  refine Real.exp_le_exp.mpr ?_
  have hlog : Real.log (vth d) = -(10 * Real.log d) := by
    unfold vth
    rw [one_div, Real.log_inv, Real.log_pow]
    push_cast
    ring
  rw [hlog]
  have : -(10 * Real.log d) * -(1 / k) = 10 * Real.log d / k := by ring
  rw [this, div_le_one hk]
  exact hkd

/-- `d^n = exp(n log d)` and `exp(n log d) ≤ exp p` give `d^n ≤ e^p` when `n log d ≤ p`. -/
private theorem pow_le_exp_of_log {d : ℕ} (hd : 1 ≤ d) {n : ℕ} {x : ℝ}
    (h : n * Real.log d ≤ x) : (d : ℝ) ^ n ≤ Real.exp x := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  calc (d : ℝ) ^ n = Real.exp (Real.log ((d : ℝ) ^ n)) := (Real.exp_log (by positivity)).symm
    _ = Real.exp (n * Real.log d) := by rw [Real.log_pow]
    _ ≤ Real.exp x := Real.exp_le_exp.mpr h

/-- R8: `(8dp + 24 p² d^{10}) e^{-3p} ≤ e^{-2p}`. -/
theorem eventually_exp_absorb : Eventually fun _ _ d p _ =>
    (8 * (d : ℝ) * p + 24 * (p : ℝ) ^ 2 * (d : ℝ) ^ 10) * Real.exp (-(3 * (p : ℝ))) ≤
      Real.exp (-(2 * (p : ℝ))) := by
  refine ((eventually_regime 2).and (eventually_log_le 13)).mono ?_
  rintro c₀ κ₀ d p h ⟨⟨hR, hp2, -⟩, hlog⟩
  have hd := hR.ten_pow_six_le_d
  have hd1 : 1 ≤ d := le_trans (by norm_num) hR.ten_pow_six_le_nat
  have hpd : (p : ℝ) ≤ d := by
    have := TRegime.pow_le_d hR (k := 1) (by norm_num)
    simpa using this
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hexp : (d : ℝ) ^ 13 ≤ Real.exp p := pow_le_exp_of_log hd1 (by push_cast; linarith)
  have hbound : 8 * (d : ℝ) * p + 24 * (p : ℝ) ^ 2 * (d : ℝ) ^ 10 ≤ (d : ℝ) ^ 13 := by
    have h1 : 8 * (d : ℝ) * p ≤ 8 * (d : ℝ) ^ 12 := by
      have : (d : ℝ) * p ≤ (d : ℝ) ^ 12 := by
        calc (d : ℝ) * p ≤ (d : ℝ) * d := by gcongr
          _ = (d : ℝ) ^ 2 := by ring
          _ ≤ (d : ℝ) ^ 12 := pow_le_pow_right₀ (by linarith) (by norm_num)
      linarith
    have h2 : 24 * (p : ℝ) ^ 2 * (d : ℝ) ^ 10 ≤ 24 * (d : ℝ) ^ 12 := by
      have : (p : ℝ) ^ 2 ≤ (d : ℝ) ^ 2 := by gcongr
      calc 24 * (p : ℝ) ^ 2 * (d : ℝ) ^ 10 ≤ 24 * (d : ℝ) ^ 2 * (d : ℝ) ^ 10 := by gcongr
        _ = 24 * (d : ℝ) ^ 12 := by ring
    have h3 : 32 * (d : ℝ) ^ 12 ≤ (d : ℝ) ^ 13 := by
      have : (32 : ℝ) ≤ d := by linarith
      calc 32 * (d : ℝ) ^ 12 ≤ (d : ℝ) * (d : ℝ) ^ 12 := by gcongr
        _ = (d : ℝ) ^ 13 := by ring
    linarith
  calc (8 * (d : ℝ) * p + 24 * (p : ℝ) ^ 2 * (d : ℝ) ^ 10) * Real.exp (-(3 * (p : ℝ)))
      ≤ Real.exp p * Real.exp (-(3 * (p : ℝ))) := by gcongr; exact hbound.trans hexp
    _ = Real.exp (-(2 * (p : ℝ))) := by rw [← Real.exp_add]; ring_nf

/-- R8: `e^{-2p}, e^{-3p} ≤ ϑ = d^{-10}` (`p ≥ 10 log d`). -/
theorem eventually_exp_le_vth : Eventually fun _ _ d p _ =>
    Real.exp (-(2 * (p : ℝ))) ≤ vth d ∧ Real.exp (-(3 * (p : ℝ))) ≤ vth d := by
  refine ((eventually_regime 1).and (eventually_log_le 10)).mono ?_
  rintro c₀ κ₀ d p h ⟨⟨hR, -, -⟩, hlog⟩
  have hd1 : 1 ≤ d := le_trans (by norm_num) hR.ten_pow_six_le_nat
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have key : Real.exp (-(p : ℝ)) ≤ vth d := by
    have h10 := pow_le_exp_of_log hd1 (n := 10) (x := p) (by push_cast; linarith)
    unfold vth
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by positivity) h10
  exact ⟨(Real.exp_le_exp.mpr (by linarith)).trans key,
    (Real.exp_le_exp.mpr (by linarith)).trans key⟩

/-- The shift `h = κ₀ p^{-4}` lies in `[ϑ, 1]` for large `d` (`p⁴ ≤ d ≤ κ₀ d^{10}`). -/
theorem eventually_h_mem : Eventually fun _ _ d _ h => vth d ≤ h ∧ h ≤ 1 := by
  intro c₀ κ₀ hc0 hc1 hk0 hk1
  obtain ⟨D, hD⟩ := eventually_regime 1 c₀ κ₀ hc0 hc1 hk0 hk1
  refine ⟨max D ⌈1 / κ₀⌉₊, fun d hd => ?_⟩
  obtain ⟨hR, -, -⟩ := hD d (le_of_max_le_left hd)
  have hdk : 1 / κ₀ ≤ d := (Nat.le_ceil _).trans (by exact_mod_cast le_of_max_le_right hd)
  have hp1 : (1 : ℝ) ≤ pAt c₀ d := by
    have := hR.two_le_p
    exact_mod_cast (by omega : 1 ≤ pAt c₀ d)
  have hp4 : (pAt c₀ d : ℝ) ^ 4 ≤ d := TRegime.pow_le_d hR (by norm_num)
  have hd1 : (1 : ℝ) ≤ d := le_trans (by norm_num) hR.ten_pow_six_le_d
  show vth d ≤ hAt κ₀ (pAt c₀ d) ∧ hAt κ₀ (pAt c₀ d) ≤ 1
  unfold hAt vth
  have hpp : 0 < (pAt c₀ d : ℝ) ^ 4 := by positivity
  have hp41 : 1 ≤ (pAt c₀ d : ℝ) ^ 4 := one_le_pow₀ hp1
  constructor
  · rw [div_le_div_iff₀ (by positivity) hpp]
    have hkd : 1 ≤ κ₀ * d := by rw [div_le_iff₀ hk0] at hdk; linarith
    have h9 : (d : ℝ) ≤ (d : ℝ) ^ 9 := le_self_pow₀ hd1 (by norm_num)
    have e : κ₀ * (d : ℝ) ^ 10 = (κ₀ * d) * (d : ℝ) ^ 9 := by ring
    have h1 : (d : ℝ) ^ 9 ≤ (κ₀ * d) * (d : ℝ) ^ 9 :=
      le_mul_of_one_le_left (by positivity) hkd
    linarith
  · rw [div_le_one hpp]
    linarith

/-- `40 ≤ e^{3.9}` (`e^{3.9} ≥ e³ e^{0.45} e^{0.45} ≥ 2.718³ · 1.45²`). -/
theorem forty_le_exp : (40 : ℝ) ≤ Real.exp (39 / 10) := by
  have he := Real.exp_one_gt_d9
  have h45 : (1.45 : ℝ) ≤ Real.exp (9 / 20) := by
    have := Real.add_one_le_exp (9 / 20 : ℝ)
    norm_num at this ⊢
    linarith
  have e : Real.exp (39 / 10) = Real.exp 1 ^ 3 * (Real.exp (9 / 20) * Real.exp (9 / 20)) := by
    rw [← Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_add]
    norm_num
  rw [e]
  have h3 : (2.7182818283 : ℝ) ^ 3 ≤ Real.exp 1 ^ 3 := by gcongr
  have h2 : (1.45 : ℝ) * 1.45 ≤ Real.exp (9 / 20) * Real.exp (9 / 20) := by gcongr
  calc (40 : ℝ) ≤ 2.7182818283 ^ 3 * (1.45 * 1.45) := by norm_num
    _ ≤ Real.exp 1 ^ 3 * (Real.exp (9 / 20) * Real.exp (9 / 20)) :=
        mul_le_mul h3 h2 (by norm_num) (by positivity)

/-- `p (Cp)^4 ≤ e^{p/10}` once `p ≥ 7! · 10^7 · C^4`. -/
private theorem poly_le_exp {C : ℝ} (hC : 1 ≤ C) {x : ℝ} (hx : 5040 * 10 ^ 7 * C ^ 4 ≤ x) :
    x * (C * x) ^ 4 ≤ Real.exp (x / 10) := by
  have hC4 : 1 ≤ C ^ 4 := one_le_pow₀ hC
  have hx0 : 0 ≤ x := by nlinarith
  have hx1 : 1 ≤ x := by nlinarith
  have h7 := Real.pow_div_factorial_le_exp (x / 10) (by positivity) 7
  have hfac : ((7 : ℕ).factorial : ℝ) = 5040 := by norm_num [Nat.factorial]
  rw [hfac] at h7
  have key : x * (C * x) ^ 4 ≤ (x / 10) ^ 7 / 5040 := by
    rw [le_div_iff₀ (by norm_num), div_pow]
    have e1 : x * (C * x) ^ 4 * 5040 = 5040 * C ^ 4 * x ^ 5 := by ring
    have e2 : x ^ 7 / 10 ^ 7 = x ^ 2 / 10 ^ 7 * x ^ 5 := by ring
    rw [e1, e2]
    have hx5 : 0 ≤ x ^ 5 := by positivity
    refine mul_le_mul_of_nonneg_right ?_ hx5
    rw [le_div_iff₀ (by norm_num)]
    nlinarith
  linarith

/-- R9 (E6, exponent 4): `p 40^p (C p)^{4k_*+4} / d^{k_*} ≤ e^{-4p}` for every fixed `C ≥ 1`. -/
theorem eventually_E6 (C : ℝ) (hC : 1 ≤ C) : Eventually fun _ _ d p _ =>
    (p : ℝ) * 40 ^ p * (C * p) ^ (4 * kStar d p + 4) / (d : ℝ) ^ kStar d p ≤
      Real.exp (-(4 * (p : ℝ))) := by
  refine ((eventually_regime (C ^ 16 + 5040 * 10 ^ 7 * C ^ 4)).and
    (eventually_le_log 1)).mono ?_
  rintro c₀ κ₀ d p h ⟨⟨hR, hpB, h17⟩, hL1⟩
  set k := kStar d p with hkdef
  set L := Real.log d with hL
  have hC0 : 0 < C := by linarith
  have hC16 : 0 ≤ C ^ 16 := by positivity
  have hC4 : 0 ≤ 5040 * 10 ^ 7 * C ^ 4 := by positivity
  have hp0 : 0 < (p : ℝ) := by
    have : 0 < 5040 * 10 ^ 7 * C ^ 4 := by positivity
    linarith
  have hd1 : 1 ≤ d := le_trans (by norm_num) hR.ten_pow_six_le_nat
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
  have hL0 : 0 < L := by linarith
  -- `(Cp)^8 ≤ d`
  have hCp8 : (C * p) ^ 8 ≤ (d : ℝ) := by
    have hpC : C ^ 16 ≤ (p : ℝ) := by linarith
    have : ((C * p) ^ 8) ^ 2 ≤ (d : ℝ) ^ 2 := by
      calc ((C * p) ^ 8) ^ 2 = C ^ 16 * (p : ℝ) ^ 16 := by ring
        _ ≤ (p : ℝ) * (p : ℝ) ^ 16 := by gcongr
        _ = (p : ℝ) ^ 17 := by ring
        _ ≤ (d : ℝ) ^ 2 := h17
    exact (pow_le_pow_iff_left₀ (by positivity) hd0.le (by norm_num)).mp this
  -- `k ≥ 16 p / L`
  have hk : 16 * (p : ℝ) / L ≤ k := Nat.le_ceil _
  -- `(Cp)^{4k} / d^k ≤ e^{-8p}`
  have hsq : (C * p) ^ (4 * k) * Real.exp (8 * p) ≤ (d : ℝ) ^ k := by
    have h1 : ((C * p) ^ (4 * k)) ^ 2 ≤ (d : ℝ) ^ k := by
      calc ((C * p) ^ (4 * k)) ^ 2 = ((C * p) ^ 8) ^ k := by ring
        _ ≤ (d : ℝ) ^ k := by gcongr
    have h2 : Real.exp (8 * p) ^ 2 ≤ (d : ℝ) ^ k := by
      rw [← Real.exp_nat_mul]
      calc Real.exp ((2 : ℕ) * (8 * (p : ℝ))) = Real.exp (16 * p) := by push_cast; ring_nf
        _ ≤ Real.exp (k * L) := by
          refine Real.exp_le_exp.mpr ?_
          rw [div_le_iff₀ hL0] at hk
          linarith
        _ = (d : ℝ) ^ k := by
          rw [hL, ← Real.log_pow, Real.exp_log (by positivity)]
    have hA : 0 ≤ (C * p) ^ (4 * k) := by positivity
    have hB : 0 ≤ Real.exp (8 * p) := (Real.exp_pos _).le
    nlinarith [sq_nonneg ((C * p) ^ (4 * k) - Real.exp (8 * p)),
      mul_nonneg hA hB]
  have h40 : (40 : ℝ) ^ p ≤ Real.exp (39 / 10 * p) := by
    calc (40 : ℝ) ^ p ≤ Real.exp (39 / 10) ^ p := by gcongr; exact forty_le_exp
      _ = Real.exp (39 / 10 * p) := by rw [← Real.exp_nat_mul, mul_comm]
  have hpoly := poly_le_exp hC (x := p) (by linarith)
  have hdk : 0 < (d : ℝ) ^ k := by positivity
  rw [div_le_iff₀ hdk]
  calc (p : ℝ) * 40 ^ p * (C * p) ^ (4 * k + 4)
      = ((p : ℝ) * (C * p) ^ 4) * 40 ^ p * (C * p) ^ (4 * k) := by ring
    _ ≤ Real.exp (p / 10) * Real.exp (39 / 10 * p) * (C * p) ^ (4 * k) := by gcongr
    _ = Real.exp (-(4 * (p : ℝ))) * ((C * p) ^ (4 * k) * Real.exp (8 * p)) := by
        have : Real.exp (↑p / 10) * Real.exp (39 / 10 * ↑p) =
            Real.exp (-(4 * (p : ℝ))) * Real.exp (8 * p) := by
          rw [← Real.exp_add, ← Real.exp_add]
          ring_nf
        rw [this]
        ring
    _ ≤ Real.exp (-(4 * (p : ℝ))) * (d : ℝ) ^ k := by gcongr

end SecC

end BiluLinial.Tight
