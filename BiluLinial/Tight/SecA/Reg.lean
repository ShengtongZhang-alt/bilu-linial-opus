/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecA.Defs

/-!
# The regime (R) of Section 1.2 (node `A-REG`)

AUDIT-A §1.1 (REG). Under `RegA d p` (`TRegime d p`, `log d ≥ 400`, `120 log d ≤ p`):

* `p^7 ≤ d`, `p^25 ≤ d^4` (from `p^17 ≤ d²`), `p ≤ d`;
* the closure inequalities of (C2) (source lines 615–622): with `u = (p/d)^{1/3}`,
  `p⁴/d ≤ u`, `p⁵/d ≤ u`, `ε ≤ u`, `1/d ≤ u²`, `p²/d ≤ u²`, `p⁹/d² ≤ u²`, `e^{-p} ≤ 1/d ≤ u²`,
  `b₀ ≤ 3u`, `d u² ≥ 1`, `u ≤ 1`;
* the comparison depth `k_* = ⌈16p/log d⌉`: `16 p ≤ k_* log d`, `1920 ≤ k_*`,
  `4 k_* + 7 ≤ p` (regularity margin A4: `α₊^{p-2}` is `C^{p-3}`), `2 (8 k_* + 12) ≤ p`
  (moment orders `≤ p/2`), and `2 (16 (log d + 1)) ≤ p` (interpolation orders);
* `eventually_regA`: `p = ⌊c₀ d^{2/17}⌋` is in the regime for large `d`, for every `c₀ ∈ (0, 1]`.

Sketch: every closure inequality `x ≤ u` (resp. `x ≤ u²`) is reduced to `x³ ≤ p/d`
(resp. `x³ ≤ (p/d)²`), a polynomial inequality implied by `p^17 ≤ d²`; `ε ≤ u` uses
`q η₀² = Δ (1 - η₀) ≤ 4/p`, so `ε² ≤ 1/(pq)` and `ε³ ≤ 1/(pq) ≤ p/d`; `e^{-p} ≤ e^{-log d}`.
-/

@[expose] public section

namespace BiluLinial.Tight

open Real

variable {d p : ℕ}

theorem RegA.one_le_p (hR : RegA d p) : (1 : ℝ) ≤ p := by
  have h : (10 : ℝ) ^ 6 ≤ p := by exact_mod_cast hR.treg.hp
  linarith

theorem RegA.p_pos (hR : RegA d p) : (0 : ℝ) < p := lt_of_lt_of_le one_pos hR.one_le_p

theorem RegA.d_pos (hR : RegA d p) : (0 : ℝ) < d := by
  have h := hR.treg.ten_pow_six_le_d
  linarith

theorem RegA.p_pow_seventeen_le (hR : RegA d p) : (p : ℝ) ^ 17 ≤ (d : ℝ) ^ 2 := by
  exact_mod_cast hR.treg.hpd

/-- `p^7 ≤ d`. -/
theorem RegA.p_pow_seven_le (hR : RegA d p) : (p : ℝ) ^ 7 ≤ d := by
  have h1 : ((p : ℝ) ^ 7) ^ 2 ≤ (d : ℝ) ^ 2 := by
    calc ((p : ℝ) ^ 7) ^ 2 = (p : ℝ) ^ 14 := by ring
      _ ≤ (p : ℝ) ^ 17 := pow_le_pow_right₀ hR.one_le_p (by norm_num)
      _ ≤ (d : ℝ) ^ 2 := hR.p_pow_seventeen_le
  exact (pow_le_pow_iff_left₀ (by positivity) (Nat.cast_nonneg d) two_ne_zero).1 h1

/-- `p^25 ≤ d^4`. -/
theorem RegA.p_pow_twentyfive_le (hR : RegA d p) : (p : ℝ) ^ 25 ≤ (d : ℝ) ^ 4 := by
  calc (p : ℝ) ^ 25 ≤ (p : ℝ) ^ 34 := pow_le_pow_right₀ hR.one_le_p (by norm_num)
    _ = ((p : ℝ) ^ 17) ^ 2 := by ring
    _ ≤ ((d : ℝ) ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) hR.p_pow_seventeen_le 2
    _ = (d : ℝ) ^ 4 := by ring

theorem RegA.p_le_d (hR : RegA d p) : (p : ℝ) ≤ d := by
  calc (p : ℝ) ≤ (p : ℝ) ^ 7 := le_self_pow₀ hR.one_le_p (by norm_num)
    _ ≤ d := hR.p_pow_seven_le

/-! ### `u = (p/d)^{1/3}` -/

namespace SecA

theorem uOf_pow_three {d p : ℕ} : uOf d p ^ 3 = (p : ℝ) / d := by
  rw [uOf, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  norm_num

end SecA

open SecA

theorem RegA.uOf_pos (hR : RegA d p) : 0 < uOf d p :=
  Real.rpow_pos_of_pos (div_pos hR.p_pos hR.d_pos) _

/-- `x ≤ u` as soon as `x³ ≤ p/d`. -/
theorem SecA.le_uOf_of_pow_three_le {x : ℝ} (hx : 0 ≤ x) (h : x ^ 3 ≤ (p : ℝ) / d) :
    x ≤ uOf d p := by
  have hu : 0 ≤ uOf d p := Real.rpow_nonneg (by positivity) _
  rw [← uOf_pow_three] at h
  exact (pow_le_pow_iff_left₀ hx hu (by norm_num)).1 h

/-- `x ≤ u²` as soon as `x³ ≤ (p/d)²`. -/
theorem SecA.le_uOf_sq_of_pow_three_le {x : ℝ} (hx : 0 ≤ x) (h : x ^ 3 ≤ ((p : ℝ) / d) ^ 2) :
    x ≤ uOf d p ^ 2 := by
  have hu : 0 ≤ uOf d p ^ 2 := sq_nonneg _
  have e : (uOf d p ^ 2) ^ 3 = ((p : ℝ) / d) ^ 2 := by rw [← uOf_pow_three]; ring
  rw [← e] at h
  exact (pow_le_pow_iff_left₀ hx hu (by norm_num)).1 h

theorem RegA.uOf_le_one (hR : RegA d p) : uOf d p ≤ 1 := by
  have hu : 0 ≤ uOf d p := hR.uOf_pos.le
  have h : uOf d p ^ 3 ≤ 1 ^ 3 := by
    rw [uOf_pow_three, one_pow, div_le_one hR.d_pos]
    exact hR.p_le_d
  exact (pow_le_pow_iff_left₀ hu zero_le_one (by norm_num)).1 h

/-- `p⁴/d ≤ u`. -/
theorem RegA.p4_div_le_u (hR : RegA d p) : (p : ℝ) ^ 4 / d ≤ uOf d p := by
  have hd := hR.d_pos
  have hp := hR.p_pos
  refine le_uOf_of_pow_three_le (by positivity) ?_
  rw [div_pow, div_le_div_iff₀ (by positivity) hd]
  have h11 : (p : ℝ) ^ 11 ≤ (d : ℝ) ^ 2 :=
    (pow_le_pow_right₀ hR.one_le_p (by norm_num)).trans hR.p_pow_seventeen_le
  calc ((p : ℝ) ^ 4) ^ 3 * d = (p : ℝ) * d * (p : ℝ) ^ 11 := by ring
    _ ≤ (p : ℝ) * d * (d : ℝ) ^ 2 := mul_le_mul_of_nonneg_left h11 (by positivity)
    _ = (p : ℝ) * (d : ℝ) ^ 3 := by ring

/-- `p⁵/d ≤ u`. -/
theorem RegA.p5_div_le_u (hR : RegA d p) : (p : ℝ) ^ 5 / d ≤ uOf d p := by
  have hd := hR.d_pos
  have hp := hR.p_pos
  refine le_uOf_of_pow_three_le (by positivity) ?_
  rw [div_pow, div_le_div_iff₀ (by positivity) hd]
  have h14 : (p : ℝ) ^ 14 ≤ (d : ℝ) ^ 2 :=
    (pow_le_pow_right₀ hR.one_le_p (by norm_num)).trans hR.p_pow_seventeen_le
  calc ((p : ℝ) ^ 5) ^ 3 * d = (p : ℝ) * d * (p : ℝ) ^ 14 := by ring
    _ ≤ (p : ℝ) * d * (d : ℝ) ^ 2 := mul_le_mul_of_nonneg_left h14 (by positivity)
    _ = (p : ℝ) * (d : ℝ) ^ 3 := by ring

/-- `1/d ≤ u²`. -/
theorem RegA.inv_d_le_u_sq (hR : RegA d p) : 1 / (d : ℝ) ≤ uOf d p ^ 2 := by
  have hd := hR.d_pos
  have hp := hR.one_le_p
  refine le_uOf_sq_of_pow_three_le (by positivity) ?_
  rw [div_pow, div_pow, one_pow, div_le_div_iff₀ (by positivity) (by positivity)]
  have hd1 : (1 : ℝ) ≤ d := hR.one_le_p.trans hR.p_le_d
  nlinarith [mul_le_mul hp hp zero_le_one (by linarith), pow_le_pow_right₀ hd1
    (show 2 ≤ 3 by norm_num)]

/-- `p²/d ≤ u²`. -/
theorem RegA.p2_div_le_u_sq (hR : RegA d p) : (p : ℝ) ^ 2 / d ≤ uOf d p ^ 2 := by
  have hd := hR.d_pos
  have hp := hR.p_pos
  refine le_uOf_sq_of_pow_three_le (by positivity) ?_
  rw [div_pow, div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
  have h4 : (p : ℝ) ^ 4 ≤ d :=
    (pow_le_pow_right₀ hR.one_le_p (by norm_num)).trans hR.p_pow_seven_le
  calc ((p : ℝ) ^ 2) ^ 3 * (d : ℝ) ^ 2 = (p : ℝ) ^ 2 * (d : ℝ) ^ 2 * (p : ℝ) ^ 4 := by ring
    _ ≤ (p : ℝ) ^ 2 * (d : ℝ) ^ 2 * d := mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = (p : ℝ) ^ 2 * (d : ℝ) ^ 3 := by ring

/-- `p⁹/d² ≤ u²`. -/
theorem RegA.p9_div_le_u_sq (hR : RegA d p) : (p : ℝ) ^ 9 / (d : ℝ) ^ 2 ≤ uOf d p ^ 2 := by
  have hd := hR.d_pos
  have hp := hR.p_pos
  refine le_uOf_sq_of_pow_three_le (by positivity) ?_
  rw [div_pow, div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
  calc ((p : ℝ) ^ 9) ^ 3 * (d : ℝ) ^ 2 = (p : ℝ) ^ 2 * (d : ℝ) ^ 2 * (p : ℝ) ^ 25 := by ring
    _ ≤ (p : ℝ) ^ 2 * (d : ℝ) ^ 2 * (d : ℝ) ^ 4 :=
        mul_le_mul_of_nonneg_left hR.p_pow_twentyfive_le (by positivity)
    _ = (p : ℝ) ^ 2 * ((d : ℝ) ^ 2) ^ 3 := by ring

/-- `e^{-p} ≤ 1/d`, from `p ≥ 120 log d ≥ log d`. -/
theorem RegA.exp_neg_p_le (hR : RegA d p) : Real.exp (-(p : ℝ)) ≤ 1 / (d : ℝ) := by
  have hd := hR.d_pos
  have hL : 0 ≤ Real.log d := by linarith [hR.logd]
  have h : -(p : ℝ) ≤ -Real.log d := by linarith [hR.plog]
  calc Real.exp (-(p : ℝ)) ≤ Real.exp (-Real.log d) := Real.exp_le_exp.2 h
    _ = 1 / (d : ℝ) := by rw [Real.exp_neg, Real.exp_log hd, one_div]

/-- `e^{-p} ≤ u²`. -/
theorem RegA.exp_neg_p_le_u_sq (hR : RegA d p) : Real.exp (-(p : ℝ)) ≤ uOf d p ^ 2 :=
  hR.exp_neg_p_le.trans hR.inv_d_le_u_sq

/-- `ε ≤ u`: `ε² = η₀²/4 ≤ 1/(pq)`, `ε³ ≤ 1/(pq) ≤ p/d`. -/
theorem RegA.epsP_le_u (hR : RegA d p) : epsP d p ≤ uOf d p := by
  have hT := hR.treg
  have hq := hT.qOf_pos
  have hq1 := hT.one_le_qOf
  have he := hT.η0Of_eq
  have h0 := hT.η0Of_pos
  have h1 := hT.η0Of_lt_one
  have hp := hR.p_pos
  have hd := hR.d_pos
  have hε : epsP d p = η0Of d p / 2 := by rw [epsP, rOf]; ring
  have hε0 : 0 ≤ epsP d p := by rw [hε]; linarith
  have hε1 : epsP d p ≤ 1 := by rw [hε]; linarith
  have hΔ : ΔOf p = 4 / p := rfl
  -- `q η₀² ≤ 4/p`
  have hqη : qOf d * η0Of d p ^ 2 ≤ 4 / p := by
    rw [he, hΔ]
    have : 0 ≤ 4 / (p : ℝ) := by positivity
    nlinarith
  have hε2 : epsP d p ^ 2 * (p * qOf d) ≤ 1 := by
    rw [hε]
    have : qOf d * η0Of d p ^ 2 * p ≤ 4 := by
      rw [le_div_iff₀ hp] at hqη
      linarith
    nlinarith
  refine le_uOf_of_pow_three_le hε0 ?_
  have hdq : (d : ℝ) = qOf d + 1 := by rw [qOf]; ring
  rw [le_div_iff₀ hd]
  have hp6 : (10 : ℝ) ^ 6 ≤ p := by exact_mod_cast hT.hp
  have hp2 : (2 : ℝ) ≤ p ^ 2 := by nlinarith
  calc epsP d p ^ 3 * d = epsP d p * (epsP d p ^ 2 * (p * qOf d)) * (d / (p * qOf d)) := by
        field_simp
    _ ≤ 1 * 1 * (d / (p * qOf d)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul hε1 hε2 (by positivity) zero_le_one
    _ ≤ p := by
        rw [one_mul, one_mul, div_le_iff₀ (by positivity), hdq]
        nlinarith

/-- `b₀ ≤ 3u`. -/
theorem RegA.b0Of_le (hR : RegA d p) : b0Of d p ≤ 3 * uOf d p := by
  have h1 := hR.epsP_le_u
  have h2 := hR.p4_div_le_u
  have h3 := hR.inv_d_le_u_sq
  have hu := hR.uOf_pos
  have hu1 := hR.uOf_le_one
  have : uOf d p ^ 2 ≤ uOf d p := by nlinarith
  rw [b0Of]
  linarith

theorem RegA.b0Of_pos (hR : RegA d p) : 0 < b0Of d p := by
  have hd := hR.d_pos
  have hε : 0 ≤ epsP d p := by
    rw [epsP, rOf]; linarith [hR.treg.η0Of_pos]
  rw [b0Of]
  positivity

/-- `1/d ≤ b₀`. -/
theorem RegA.inv_d_le_b0Of (hR : RegA d p) : 1 / (d : ℝ) ≤ b0Of d p := by
  have hd := hR.d_pos
  have hε : 0 ≤ epsP d p := by
    rw [epsP, rOf]; linarith [hR.treg.η0Of_pos]
  rw [b0Of]
  have : 0 ≤ (p : ℝ) ^ 4 / d := by positivity
  linarith

/-- `d u² ≥ 1` (so `z = u²` is an admissible shift). -/
theorem RegA.one_le_d_mul_u_sq (hR : RegA d p) : 1 ≤ (d : ℝ) * uOf d p ^ 2 := by
  have h := hR.inv_d_le_u_sq
  have hd := hR.d_pos
  rw [div_le_iff₀ hd] at h
  linarith

/-! ### The comparison depth `k_*` -/

theorem RegA.log_pos (hR : RegA d p) : 0 < Real.log d := by linarith [hR.logd]

theorem RegA.kStar_ge (_hR : RegA d p) : 16 * (p : ℝ) / Real.log d ≤ kStarA d p :=
  Nat.le_ceil _

theorem RegA.kStar_lt (hR : RegA d p) : (kStarA d p : ℝ) < (p : ℝ) / 25 + 1 := by
  have hL := hR.log_pos
  have h1 : (kStarA d p : ℝ) < 16 * (p : ℝ) / Real.log d + 1 :=
    Nat.ceil_lt_add_one (by positivity [hR.p_pos])
  have h2 : 16 * (p : ℝ) / Real.log d ≤ (p : ℝ) / 25 := by
    rw [div_le_div_iff₀ hL (by norm_num)]
    nlinarith [hR.logd, hR.p_pos]
  linarith

/-- `16 p ≤ k_* log d`. -/
theorem RegA.sixteen_p_le (hR : RegA d p) : 16 * (p : ℝ) ≤ kStarA d p * Real.log d := by
  have h := hR.kStar_ge
  rwa [div_le_iff₀ hR.log_pos] at h

/-- `k_* ≥ 1920`. -/
theorem RegA.kStar_ge_1920 (hR : RegA d p) : 1920 ≤ kStarA d p := by
  have h := hR.kStar_ge
  have hL := hR.log_pos
  have h2 : (1920 : ℝ) ≤ 16 * (p : ℝ) / Real.log d := by
    rw [le_div_iff₀ hL]; nlinarith [hR.plog]
  exact_mod_cast h2.trans h

/-- Regularity margin (A4): `4 k_* + 7 ≤ p`, i.e. `4 k_* + 4 ≤ p - 3`. -/
theorem RegA.four_kStar_add_seven_le (hR : RegA d p) : 4 * kStarA d p + 7 ≤ p := by
  have h := hR.kStar_lt
  have hp : (10 : ℝ) ^ 6 ≤ p := by exact_mod_cast hR.treg.hp
  have : (4 * (kStarA d p : ℝ) + 7) ≤ p := by linarith
  exact_mod_cast this

/-- Moment orders: `2 (8 k_* + 12) ≤ p`. -/
theorem RegA.moment_order_le (hR : RegA d p) : 2 * (8 * kStarA d p + 12) ≤ p := by
  have h := hR.kStar_lt
  have hp : (10 : ℝ) ^ 6 ≤ p := by exact_mod_cast hR.treg.hp
  have : (2 * (8 * (kStarA d p : ℝ) + 12)) ≤ p := by linarith
  exact_mod_cast this

/-- Interpolation orders: `2 (16 (log d + 1)) ≤ p`. -/
theorem RegA.interp_order_le (hR : RegA d p) : 2 * (16 * (Real.log d + 1)) ≤ p := by
  nlinarith [hR.plog, hR.logd]

/-! ### The regime at `p = ⌊c₀ d^{2/17}⌋` -/

/-- For every `c₀ ∈ (0, 1]`, `p = ⌊c₀ d^{2/17}⌋` is in the regime (R) once `d` is large. -/
theorem SecA.eventually_regA : Eventually fun _ _ d p _ => RegA d p := by
  intro c₀ κ₀ hc0 hc1 _ _
  obtain ⟨D₁, hD₁⟩ := exists_tRegime_pAt hc0 hc1
  -- `log x ≤ (c₀/240) x^{2/17}` eventually
  have hlo := (_root_.isLittleO_log_rpow_atTop (show (0 : ℝ) < 2 / 17 by norm_num)).bound
    (show (0 : ℝ) < c₀ / 240 by positivity)
  have hlo' := Filter.Tendsto.eventually (tendsto_natCast_atTop_atTop (R := ℝ)) hlo
  obtain ⟨D₂, hD₂⟩ := Filter.eventually_atTop.1 hlo'
  have hlog := Filter.Tendsto.eventually (tendsto_natCast_atTop_atTop (R := ℝ))
    (Real.tendsto_log_atTop.eventually_ge_atTop 400)
  obtain ⟨D₃, hD₃⟩ := Filter.eventually_atTop.1 hlog
  refine ⟨max D₁ (max D₂ (max D₃ 2)), fun d hd => ?_⟩
  have h1 := hD₁ d (le_of_max_le_left hd)
  have hd' := le_of_max_le_right hd
  have h2 := hD₂ d (le_of_max_le_left hd')
  have hd'' := le_of_max_le_right hd'
  have h3 := hD₃ d (le_of_max_le_left hd'')
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast le_of_max_le_right hd''
  refine ⟨h1.1, h3, ?_⟩
  have hp := half_base_le_pAt h1.2
  have hlogn : 0 ≤ Real.log d := Real.log_nonneg (by linarith)
  have ht0 : 0 ≤ (d : ℝ) ^ ((2 : ℝ) / 17) := Real.rpow_nonneg (by positivity) _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlogn, abs_of_nonneg ht0] at h2
  nlinarith

end BiluLinial.Tight
