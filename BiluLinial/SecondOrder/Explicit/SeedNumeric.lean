/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.SecondOrder.Explicit.TreeNumeric

/-!
# Numerics of the triangle seed

Blueprint node `C2-seednum` (source Section 6, eq. (6.3) and "for a sufficiently large finite
height `h`, every signing of the seed has mean two-sided root response greater than `t₊`").
Throughout `R = thr n t = q t + 1/t`, `a(g) = R - (q - 1) g`, `b(g) = R - (q - 2) g`.

* `tri_seed_denoms_pos`: for `g ≤ t` and `τ = ±1`: `a(g) > 1` and `b(g) - 2/(a(g) - τ) > 0`.
  (`a(g) ≥ t + 1/t ≥ 2`, `b(g) ≥ 2t + 1/t`, `a(g) - τ ≥ t + 1/t - 1 > 0`, and
  `(2t + 1/t)(t + 1/t - 1) - 2 = (2t⁴ - 2t³ + t² - t + 1)/t² > 0`.)
* `seedMean_limit`: at `g = t` (`a = 1/t + t`, `b = 1/t + 2t`) the mean of the two seed responses
  is `t (1 + t² + t⁴ + 2t⁶) / (1 + t² + t⁴ + 4t⁸)`.
* `tri_seed_gain`: if `q t² < 1` and `F_q(t²) > 0`, some finite height `h` has
  `seedMean n t h > t₊ = 1/(q t)`: the mean is continuous at `g = t`, `g_h → t`
  (`treeResp_tendsto`), and `m(t) - 1/(q t) = F_q(t²) / (q t (1 + t² + t⁴ + 4t⁸)) > 0`.
-/

@[expose] public section

namespace BiluLinial.SecondOrder.Explicit

open Filter Topology

/-- `2t⁴ - 2t³ + t² - t + 1 = (t² - t)² + (t² - 1/2)² + (t - 1/2)² + 1/2 > 0`. -/
private theorem quartic_pos (t : ℝ) : 0 < 2 * t ^ 4 - 2 * t ^ 3 + t ^ 2 - t + 1 := by
  nlinarith [sq_nonneg (t ^ 2 - t), sq_nonneg (t ^ 2 - 1 / 2), sq_nonneg (t - 1 / 2)]

theorem tri_seed_denoms_pos (n : ℕ) {t : ℝ} (ht : 0 < t) {g : ℝ} (hg : g ≤ t) {τ : ℝ}
    (hτ : τ = 1 ∨ τ = -1) :
    1 < thr n t - (n + 1) * g ∧
      0 < (thr n t - n * g) - 2 / ((thr n t - (n + 1) * g) - τ) := by
  have hn : (0 : ℝ) ≤ n := n.cast_nonneg
  have hτ1 : τ ≤ 1 := by rcases hτ with rfl | rfl <;> norm_num
  have hthr : thr n t = ((n : ℝ) + 2) * t + 1 / t := rfl
  have ha : t + 1 / t ≤ thr n t - (n + 1) * g := by
    rw [hthr]
    nlinarith [mul_le_mul_of_nonneg_left hg (by positivity : (0 : ℝ) ≤ n + 1)]
  have hb : 2 * t + 1 / t ≤ thr n t - n * g := by
    rw [hthr]
    nlinarith [mul_le_mul_of_nonneg_left hg hn]
  have h2 : 2 ≤ t + 1 / t := by
    have e : t + 1 / t - 2 = (t - 1) ^ 2 / t := by
      field_simp
      ring
    have : 0 ≤ (t - 1) ^ 2 / t := by positivity
    linarith
  refine ⟨by linarith, ?_⟩
  have hpos : 0 < t + 1 / t - 1 := by linarith
  have hat : t + 1 / t - 1 ≤ (thr n t - (n + 1) * g) - τ := by linarith
  have h3 : 2 / ((thr n t - (n + 1) * g) - τ) ≤ 2 / (t + 1 / t - 1) :=
    div_le_div_of_nonneg_left (by norm_num) hpos hat
  have h4 : 2 / (t + 1 / t - 1) < 2 * t + 1 / t := by
    rw [div_lt_iff₀ hpos]
    have e : (2 * t + 1 / t) * (t + 1 / t - 1) - 2 =
        (2 * t ^ 4 - 2 * t ^ 3 + t ^ 2 - t + 1) / t ^ 2 := by
      field_simp
      ring
    have : 0 < (2 * t ^ 4 - 2 * t ^ 3 + t ^ 2 - t + 1) / t ^ 2 :=
      div_pos (quartic_pos t) (by positivity)
    linarith
  linarith

theorem seedMean_limit (n : ℕ) {t : ℝ} (ht : 0 < t) :
    (seedResp3 n (thr n t) t 1 + seedResp3 n (thr n t) t (-1)) / 2 =
      t * (1 + t ^ 2 + t ^ 4 + 2 * t ^ 6) / (1 + t ^ 2 + t ^ 4 + 4 * t ^ 8) := by
  have ha : thr n t - (n + 1) * t = t + 1 / t := by
    unfold thr
    ring
  have hb : thr n t - n * t = 2 * t + 1 / t := by
    unfold thr
    ring
  unfold seedResp3
  rw [ha, hb]
  have ht0 : t ≠ 0 := ht.ne'
  have p1 : 0 < t ^ 2 - t + 1 := by nlinarith [sq_nonneg (t - 1 / 2)]
  have p2 : 0 < t ^ 2 + t + 1 := by positivity
  have n1 := quartic_pos t
  have n2 : 0 < 2 * t ^ 4 + 2 * t ^ 3 + t ^ 2 + t + 1 := by positivity
  have d1 : t + 1 / t - 1 = (t ^ 2 - t + 1) / t := by
    field_simp
    ring
  have d2 : t + 1 / t - -1 = (t ^ 2 + t + 1) / t := by
    field_simp
    ring
  rw [d1, d2]
  have e1 : 2 * t + 1 / t - 2 / ((t ^ 2 - t + 1) / t) =
      (2 * t ^ 4 - 2 * t ^ 3 + t ^ 2 - t + 1) / (t * (t ^ 2 - t + 1)) := by
    obtain ⟨D, hD⟩ : ∃ D, D = t ^ 2 - t + 1 := ⟨_, rfl⟩
    have hD0 : D ≠ 0 := by rw [hD]; exact p1.ne'
    have e : 2 * t ^ 4 - 2 * t ^ 3 + t ^ 2 - t + 1 = (2 * t ^ 2 + 1) * D - 2 * t ^ 2 := by
      rw [hD]
      ring
    rw [← hD, e]
    field_simp
  have e2 : 2 * t + 1 / t - 2 / ((t ^ 2 + t + 1) / t) =
      (2 * t ^ 4 + 2 * t ^ 3 + t ^ 2 + t + 1) / (t * (t ^ 2 + t + 1)) := by
    field_simp
    ring
  rw [e1, e2, one_div_div, one_div_div]
  have n3 : 0 < 1 + t ^ 2 + t ^ 4 + 4 * t ^ 8 := by positivity
  rw [div_add_div _ _ n1.ne' n2.ne', div_div, div_eq_div_iff (by positivity) n3.ne']
  ring

theorem tri_seed_gain (n : ℕ) {t : ℝ} (ht : 0 < t) (hqt : ((n : ℝ) + 2) * t ^ 2 < 1)
    (hF : 1 + t ^ 2 + (t ^ 2) ^ 2 + 4 * (t ^ 2) ^ 4 <
      ((n : ℝ) + 2) * t ^ 2 * (1 + t ^ 2 + (t ^ 2) ^ 2 + 2 * (t ^ 2) ^ 3)) :
    ∃ h : ℕ, 1 / (((n : ℝ) + 2) * t) < seedMean n t h := by
  have hc : ∀ τ : ℝ, (τ = 1 ∨ τ = -1) →
      ContinuousAt (fun g => seedResp3 n (thr n t) g τ) t := by
    intro τ hτ
    obtain ⟨ha, hb⟩ := tri_seed_denoms_pos n ht le_rfl hτ
    have hτ1 : τ ≤ 1 := by rcases hτ with rfl | rfl <;> norm_num
    unfold seedResp3
    have c1 : ContinuousAt (fun g : ℝ => thr n t - (n + 1) * g - τ) t := by fun_prop
    have c2 : ContinuousAt
        (fun g : ℝ => (thr n t - n * g) - 2 / ((thr n t - (n + 1) * g) - τ)) t :=
      (by fun_prop : ContinuousAt (fun g : ℝ => thr n t - n * g) t).sub
        (continuousAt_const.div₀ c1 (by linarith))
    exact continuousAt_const.div₀ c2 hb.ne'
  have hcont : ContinuousAt
      (fun g => (seedResp3 n (thr n t) g 1 + seedResp3 n (thr n t) g (-1)) / 2) t :=
    ((hc 1 (Or.inl rfl)).add (hc (-1) (Or.inr rfl))).div_const 2
  have hlim : 1 / (((n : ℝ) + 2) * t) <
      (seedResp3 n (thr n t) t 1 + seedResp3 n (thr n t) t (-1)) / 2 := by
    rw [seedMean_limit n ht, div_lt_div_iff₀ (by positivity) (by positivity)]
    have e1 : 1 * (1 + t ^ 2 + t ^ 4 + 4 * t ^ 8) = 1 + t ^ 2 + (t ^ 2) ^ 2 + 4 * (t ^ 2) ^ 4 := by
      ring
    have e2 : t * (1 + t ^ 2 + t ^ 4 + 2 * t ^ 6) * (((n : ℝ) + 2) * t) =
        ((n : ℝ) + 2) * t ^ 2 * (1 + t ^ 2 + (t ^ 2) ^ 2 + 2 * (t ^ 2) ^ 3) := by
      ring
    rw [e1, e2]
    exact hF
  obtain ⟨h, hh⟩ :=
    ((hcont.tendsto.comp (treeResp_tendsto n ht hqt)).eventually (lt_mem_nhds hlim)).exists
  exact ⟨h, hh⟩

end BiluLinial.SecondOrder.Explicit
