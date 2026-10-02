/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import Mathlib

/-!
# An explicit admissible threshold

Blueprint node `C2-num`. For real `q ≥ 3` let `t₀ = u₀/√q` with `u₀ = 1 - w`, `w = 1/(5q³)`. Then
`0 < t₀`, `q t₀² < 1`, `F_q(t₀²) > 0` where `F_q(z) = -1 + (q-1)z + (q-1)z² + qz³ + (2q-4)z⁴`, and the
threshold `q t₀ + 1/t₀` is at least `2√q + q^{-11/2}/25`. So the Section 6 construction applies
at a threshold `≥ 2√q + q^{-11/2}/25` without mentioning the root `z_q`.

Proof sketch. `q t₀ + 1/t₀ = √q (u₀ + 1/u₀)`, so `q t₀ + 1/t₀ - 2√q = √q (1-u₀)²/u₀ ≥ √q w² =
1/(25 q⁵ √q)` (as `0 < u₀ < 1`, `√q · q⁻⁶ = 1/(q⁵√q)`). For `F_q`: `t₀² = u₀²/q`, and
`P(u) = q⁴ F_q(u²/q) = -q⁴ + (q-1)q³u² + (q-1)q²u⁴ + q²u⁶ + (2q-4)u⁸`. Each `u^{2j}` is convex, so
`P(1-w) ≥ P(1) - P'(1) w` with `P(1) = 2q - 4`, `P'(1) = 2q⁴ + 2q³ + 2q² + 16q - 32`, i.e.
`q³ P(u₀) ≥ 1.6q⁴ - 4.4q³ - 0.4q² - 3.2q + 6.4 > 0` for `q ≥ 3` (value `4.0` at `q = 3`, increasing).
(Termwise: `(1-w)^{2j} ≥ 1 - 2j w` by Bernoulli.)
-/

@[expose] public section

namespace BiluLinial.SecondOrder.Explicit

/-- `t₀ = (1 - 1/(5q³))/√q`. -/
noncomputable def t0 (q : ℝ) : ℝ := (1 - 1 / (5 * q ^ 3)) / Real.sqrt q

private lemma w_bounds {q : ℝ} (hq : 3 ≤ q) :
    0 < 1 / (5 * q ^ 3) ∧ 1 / (5 * q ^ 3) ≤ 1 / 135 := by
  have hq0 : 0 < q := by linarith
  have h9 : 9 ≤ q ^ 2 := by nlinarith
  have h27 : 27 ≤ q ^ 3 := by nlinarith
  exact ⟨by positivity, one_div_le_one_div_of_le (by norm_num) (by linarith)⟩

private lemma t0_sq_eq {q : ℝ} (hq : 3 ≤ q) : q * t0 q ^ 2 = (1 - 1 / (5 * q ^ 3)) ^ 2 := by
  have hq0 : 0 < q := by linarith
  unfold t0
  rw [div_pow, Real.sq_sqrt hq0.le, mul_div_cancel₀ _ hq0.ne']

/-- `q⁴ F_q(u²/q) > 0` for `u = 1 - w`, `w = 1/(5q³)`. -/
private lemma P_pos {q w u : ℝ} (hq : 3 ≤ q) (hw0 : 0 < w) (hw1 : w ≤ 1 / 135)
    (hw5 : 5 * q ^ 3 * w = 1) (hu : 1 - w = u) :
    0 < -q ^ 4 + (q - 1) * q ^ 3 * u ^ 2 + (q - 1) * q ^ 2 * (u ^ 2) ^ 2 +
      q ^ 2 * (u ^ 2) ^ 3 + (2 * q - 4) * (u ^ 2) ^ 4 := by
  have hq0 : 0 < q := by linarith
  have h12 : 0 ≤ 1 - 2 * w := by linarith
  have h14 : 0 ≤ 1 - 4 * w := by linarith
  have h2 : 1 - 2 * w ≤ u ^ 2 := by rw [← hu]; nlinarith [sq_nonneg w]
  have hu2 : 0 ≤ u ^ 2 := sq_nonneg u
  have h4 : 1 - 4 * w ≤ (u ^ 2) ^ 2 := by
    nlinarith [mul_le_mul h2 h2 h12 hu2, sq_nonneg w]
  have hu4 : 0 ≤ (u ^ 2) ^ 2 := by positivity
  have h6 : 1 - 6 * w ≤ (u ^ 2) ^ 3 := by
    nlinarith [mul_le_mul h4 h2 h12 hu4, sq_nonneg w]
  have h8 : 1 - 8 * w ≤ (u ^ 2) ^ 4 := by
    nlinarith [mul_le_mul h4 h4 h14 hu4, sq_nonneg w]
  have hc1 : 0 ≤ (q - 1) * q ^ 3 := mul_nonneg (by linarith) (pow_nonneg hq0.le 3)
  have hc2 : 0 ≤ (q - 1) * q ^ 2 := mul_nonneg (by linarith) (pow_nonneg hq0.le 2)
  have hc3 : 0 ≤ q ^ 2 := pow_nonneg hq0.le 2
  have hc4 : 0 ≤ 2 * q - 4 := by linarith
  have hB : 0 < 8 * q ^ 4 - 22 * q ^ 3 - 2 * q ^ 2 - 16 * q + 32 := by
    have hp : 0 ≤ q - 3 := by linarith
    nlinarith [pow_nonneg hp 2, pow_nonneg hp 3, pow_nonneg hp 4]
  have hlow : 0 < 2 * q - 4 - w * (2 * q ^ 4 + 2 * q ^ 3 + 2 * q ^ 2 + 16 * q - 32) := by
    have h5 : 0 < 5 * q ^ 3 := by positivity
    have e : 5 * q ^ 3 * (2 * q - 4 - w * (2 * q ^ 4 + 2 * q ^ 3 + 2 * q ^ 2 + 16 * q - 32)) =
        8 * q ^ 4 - 22 * q ^ 3 - 2 * q ^ 2 - 16 * q + 32 := by
      linear_combination (-(2 * q ^ 4 + 2 * q ^ 3 + 2 * q ^ 2 + 16 * q - 32)) * hw5
    have h' : 0 < 5 * q ^ 3 *
        (2 * q - 4 - w * (2 * q ^ 4 + 2 * q ^ 3 + 2 * q ^ 2 + 16 * q - 32)) := by
      rw [e]; exact hB
    exact pos_of_mul_pos_right h' h5.le
  linarith [mul_le_mul_of_nonneg_left h2 hc1, mul_le_mul_of_nonneg_left h4 hc2,
    mul_le_mul_of_nonneg_left h6 hc3, mul_le_mul_of_nonneg_left h8 hc4]

theorem t0_pos {q : ℝ} (hq : 3 ≤ q) : 0 < t0 q := by
  obtain ⟨-, hw1⟩ := w_bounds hq
  unfold t0
  exact div_pos (by linarith) (Real.sqrt_pos.mpr (by linarith))

theorem t0_sq_lt {q : ℝ} (hq : 3 ≤ q) : q * t0 q ^ 2 < 1 := by
  obtain ⟨hw0, hw1⟩ := w_bounds hq
  rw [t0_sq_eq hq]
  obtain ⟨w, hw⟩ : ∃ w, 1 / (5 * q ^ 3) = w := ⟨_, rfl⟩
  rw [hw] at hw0 hw1 ⊢
  nlinarith [mul_pos hw0 (by linarith : (0 : ℝ) < 2 - w)]

theorem t0_poly_pos {q : ℝ} (hq : 3 ≤ q) :
    0 < -1 + (q - 1) * t0 q ^ 2 + (q - 1) * (t0 q ^ 2) ^ 2 + q * (t0 q ^ 2) ^ 3 +
      (2 * q - 4) * (t0 q ^ 2) ^ 4 := by
  obtain ⟨hw0, hw1⟩ := w_bounds hq
  have hq0 : 0 < q := by linarith
  have hqz := t0_sq_eq hq
  obtain ⟨w, hw⟩ : ∃ w, 1 / (5 * q ^ 3) = w := ⟨_, rfl⟩
  have hw5 : 5 * q ^ 3 * w = 1 := by rw [← hw]; field_simp
  rw [hw] at hw0 hw1 hqz
  obtain ⟨u, hu⟩ : ∃ u, 1 - w = u := ⟨_, rfl⟩
  rw [hu] at hqz
  have hE : q ^ 4 * (-1 + (q - 1) * t0 q ^ 2 + (q - 1) * (t0 q ^ 2) ^ 2 + q * (t0 q ^ 2) ^ 3 +
      (2 * q - 4) * (t0 q ^ 2) ^ 4) =
      -q ^ 4 + (q - 1) * q ^ 3 * (q * t0 q ^ 2) + (q - 1) * q ^ 2 * (q * t0 q ^ 2) ^ 2 +
        q ^ 2 * (q * t0 q ^ 2) ^ 3 + (2 * q - 4) * (q * t0 q ^ 2) ^ 4 := by
    ring
  rw [hqz] at hE
  have h4 : 0 < q ^ 4 * (-1 + (q - 1) * t0 q ^ 2 + (q - 1) * (t0 q ^ 2) ^ 2 +
      q * (t0 q ^ 2) ^ 3 + (2 * q - 4) * (t0 q ^ 2) ^ 4) := by
    rw [hE]; exact P_pos hq hw0 hw1 hw5 hu
  exact pos_of_mul_pos_right h4 (by positivity)

theorem t0_thr_ge {q : ℝ} (hq : 3 ≤ q) :
    2 * Real.sqrt q + 1 / (25 * q ^ 5 * Real.sqrt q) ≤ q * t0 q + 1 / t0 q := by
  obtain ⟨hw0, hw1⟩ := w_bounds hq
  have hq0 : 0 < q := by linarith
  have hs0 : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq0
  have hss : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq0.le
  unfold t0
  obtain ⟨w, hw⟩ : ∃ w, 1 / (5 * q ^ 3) = w := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s, Real.sqrt q = s := ⟨_, rfl⟩
  rw [hw] at hw0 hw1 ⊢
  rw [hs] at hs0 hss ⊢
  have hsne : s ≠ 0 := hs0.ne'
  have hu0 : 0 < 1 - w := by linarith
  have e1 : q * ((1 - w) / s) = s * (1 - w) := by
    rw [mul_div_assoc', div_eq_iff hsne, ← hss]; ring
  have e3 : 1 / (25 * q ^ 5 * s) = s * w ^ 2 := by
    rw [← hw, ← hss, div_pow, one_pow, mul_one_div,
      div_eq_div_iff (by positivity) (by positivity)]
    ring
  rw [e1, one_div_div, e3]
  have h : s * (1 + w + w ^ 2) ≤ s / (1 - w) := by
    rw [le_div_iff₀ hu0]
    nlinarith [mul_nonneg hs0.le (pow_nonneg hw0.le 3)]
  nlinarith [h]

end BiluLinial.SecondOrder.Explicit
