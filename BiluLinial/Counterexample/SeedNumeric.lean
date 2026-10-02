/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Counterexample.Defs

/-!
# Numerics of the seed

Blueprint node `B-seed-num` (source Step 6, "Seed gain").

* `treeGreen n h ∈ (0, 1/√q)`.
* For a tree response `g ∈ [0, 1/√q]`, with `a = r - (q - 1) g`, `b = r - (q - 2) g` and
  `τ = ±1`, all the denominators of the seed response are positive and `a > 1`.
* Seed gain: `t(∞) - 1 = 2(q² - 2) / (q⁶ + q⁵ + q⁴ + 4q + 4) > 0`, so some finite `h` has
  `t(h) > 1` (`g_h = treeGreen n h → 1/√q` and `t` is continuous there).
-/

@[expose] public section

namespace BiluLinial.Counterexample

open Filter Topology

theorem treeGreen_pos (n h : ℕ) : 0 < treeGreen n h := by
  unfold treeGreen
  positivity

theorem treeGreen_lt (n h : ℕ) : treeGreen n h < 1 / Real.sqrt (n + 2) := by
  unfold treeGreen
  have hs : 0 < Real.sqrt ((n : ℝ) + 2) := Real.sqrt_pos.2 (by positivity)
  rw [div_lt_div_iff₀ (by positivity) hs]
  nlinarith

theorem seed_denoms_pos (n : ℕ) {g : ℝ} (hg0 : 0 ≤ g) (hg : g ≤ 1 / Real.sqrt (n + 2)) {τ : ℝ}
    (hτ : τ = 1 ∨ τ = -1) :
    1 < rad n - (n + 1) * g ∧
      0 < (rad n - n * g) - 2 / ((rad n - (n + 1) * g) - τ) ∧
      0 < (rad n - (n + 1) * g) - 1 / ((rad n - n * g) - 2 / ((rad n - (n + 1) * g) - τ)) := by
  have hs0 : 0 < Real.sqrt ((n : ℝ) + 2) := Real.sqrt_pos.2 (by positivity)
  have hs2 : Real.sqrt ((n : ℝ) + 2) ^ 2 = n + 2 := Real.sq_sqrt (by positivity)
  have hrad : rad n = 2 * Real.sqrt ((n : ℝ) + 2) := rfl
  set s := Real.sqrt ((n : ℝ) + 2) with hs_def
  have hgs : g * s ≤ 1 := by rwa [le_div_iff₀ hs0] at hg
  have hτ1 : τ ≤ 1 := by rcases hτ with rfl | rfl <;> norm_num
  have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
  set a := rad n - (n + 1) * g with ha_def
  set b := rad n - n * g with hb_def
  have has : s ^ 2 + 1 ≤ a * s := by
    rw [ha_def, hrad]
    nlinarith [mul_le_mul_of_nonneg_left hgs (by positivity : (0 : ℝ) ≤ n + 1)]
  have hbs : s ^ 2 + 2 ≤ b * s := by
    rw [hb_def, hrad]
    nlinarith [mul_le_mul_of_nonneg_left hgs hn0]
  have ha2 : 2 ≤ a := by nlinarith [sq_nonneg (s - 1)]
  have hb : 14 / 5 < b := by nlinarith [sq_nonneg (s - 7 / 5)]
  have hc : 1 ≤ a - τ := by linarith
  have h2c : 2 / (a - τ) ≤ 2 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  have hβ : 4 / 5 ≤ b - 2 / (a - τ) := by linarith
  refine ⟨by linarith, by linarith, ?_⟩
  have h1β : 1 / (b - 2 / (a - τ)) ≤ 5 / 4 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  linarith

/-! ### The seed response at the limit point `g = 1/√q` -/

/-- `s² + 1 - τ s` with `s = √q`, i.e. `s (a - τ)` at `g = 1/s`. -/
private def Pst (s τ : ℝ) : ℝ := s ^ 2 + 1 - τ * s

/-- `s² (b (a - τ) - 2)` at `g = 1/s`. -/
private def Nst (s τ : ℝ) : ℝ := (s ^ 2 + 2) * Pst s τ - 2 * s ^ 2

/-- `s³ (a (b (a - τ) - 2) - (a - τ))` at `g = 1/s`. -/
private def Dst (s τ : ℝ) : ℝ := (s ^ 2 + 1) * Nst s τ - s ^ 2 * Pst s τ

private lemma Pst_pos {s τ : ℝ} (hs : 1 ≤ s) (hτ : τ = 1 ∨ τ = -1) : 0 < Pst s τ := by
  unfold Pst
  rcases hτ with rfl | rfl <;> nlinarith [sq_nonneg (s - 1)]

private lemma Nst_pos {s τ : ℝ} (hs : 1 ≤ s) (hτ : τ = 1 ∨ τ = -1) : 0 < Nst s τ := by
  have hs0 : 0 ≤ s := by linarith
  unfold Nst Pst
  rcases hτ with rfl | rfl
  · nlinarith [mul_nonneg (pow_nonneg hs0 3) (sub_nonneg.2 hs), sq_nonneg (s - 1)]
  · nlinarith [pow_nonneg hs0 3, pow_nonneg hs0 4]

private lemma Dst_pos {s τ : ℝ} (hs : 1 ≤ s) (hτ : τ = 1 ∨ τ = -1) : 0 < Dst s τ := by
  have hs0 : 0 ≤ s := by linarith
  unfold Dst Nst Pst
  rcases hτ with rfl | rfl
  · nlinarith [mul_nonneg (pow_nonneg hs0 5) (sub_nonneg.2 hs),
      mul_nonneg (sq_nonneg s) (sq_nonneg (s - 1)), sq_nonneg (s - 1)]
  · nlinarith [pow_nonneg hs0 3, pow_nonneg hs0 4, pow_nonneg hs0 5, pow_nonneg hs0 6]

/-- Closed form of the seed response at `g = 1/s`, `s² = m + 2`. -/
private lemma resp_star_aux (s m τ : ℝ) (hs : 1 ≤ s) (hm : s ^ 2 = m + 2)
    (hτ : τ = 1 ∨ τ = -1) :
    1 / ((2 * s - (m + 1) * (1 / s)) -
        1 / ((2 * s - m * (1 / s)) - 2 / ((2 * s - (m + 1) * (1 / s)) - τ))) =
      s * Nst s τ / Dst s τ := by
  obtain rfl : m = s ^ 2 - 2 := by linarith
  have hsne : s ≠ 0 := by positivity
  have hP := Pst_pos hs hτ
  have hN := Nst_pos hs hτ
  have ha : 2 * s - (s ^ 2 - 2 + 1) * (1 / s) = (s ^ 2 + 1) / s := by
    field_simp
    ring
  have hb : 2 * s - (s ^ 2 - 2) * (1 / s) = (s ^ 2 + 2) / s := by
    field_simp
    ring
  have e1 : (s ^ 2 + 1) / s - τ = Pst s τ / s := by
    unfold Pst
    field_simp
  have e2 : (s ^ 2 + 2) / s - 2 * s / Pst s τ = Nst s τ / (s * Pst s τ) := by
    rw [div_sub_div _ _ hsne hP.ne']
    unfold Nst
    ring
  have e3 : (s ^ 2 + 1) / s - s * Pst s τ / Nst s τ = Dst s τ / (s * Nst s τ) := by
    rw [div_sub_div _ _ hsne hN.ne']
    unfold Dst
    ring
  rw [ha, hb, e1, div_div_eq_mul_div, e2, one_div_div, e3, one_div_div]

private lemma seedResp_star (n : ℕ) {τ : ℝ} (hτ : τ = 1 ∨ τ = -1) :
    seedResp n (1 / Real.sqrt (n + 2)) τ =
      Real.sqrt (n + 2) * Nst (Real.sqrt (n + 2)) τ / Dst (Real.sqrt (n + 2)) τ := by
  have hs0 : 0 ≤ Real.sqrt ((n : ℝ) + 2) := Real.sqrt_nonneg _
  have hs2 : Real.sqrt ((n : ℝ) + 2) ^ 2 = n + 2 := Real.sq_sqrt (by positivity)
  have hs1 : 1 ≤ Real.sqrt ((n : ℝ) + 2) := by nlinarith
  unfold seedResp rad
  exact resp_star_aux _ _ _ hs1 hs2 hτ

private lemma gain_aux (s N₁ N₂ D₁ D₂ : ℝ) (h1 : 0 < D₁) (h2 : 0 < D₂)
    (key : 0 < s ^ 2 * (N₁ * D₂ + N₂ * D₁) - 2 * (D₁ * D₂)) :
    1 < s / 2 * (s * N₁ / D₁ + s * N₂ / D₂) := by
  have e : s / 2 * (s * N₁ / D₁ + s * N₂ / D₂) - 1 =
      (s ^ 2 * (N₁ * D₂ + N₂ * D₁) - 2 * (D₁ * D₂)) / (2 * (D₁ * D₂)) := by
    field_simp
  have : 0 < (s ^ 2 * (N₁ * D₂ + N₂ * D₁) - 2 * (D₁ * D₂)) / (2 * (D₁ * D₂)) :=
    div_pos key (by positivity)
  linarith

/-- `t(∞) > 1`. -/
private lemma tstar_gt_one (n : ℕ) :
    1 < Real.sqrt (n + 2) / 2 *
      (seedResp n (1 / Real.sqrt (n + 2)) 1 + seedResp n (1 / Real.sqrt (n + 2)) (-1)) := by
  have hs0 : 0 ≤ Real.sqrt ((n : ℝ) + 2) := Real.sqrt_nonneg _
  have hs2 : Real.sqrt ((n : ℝ) + 2) ^ 2 = n + 2 := Real.sq_sqrt (by positivity)
  have hs1 : 1 ≤ Real.sqrt ((n : ℝ) + 2) := by nlinarith
  rw [seedResp_star n (Or.inl rfl), seedResp_star n (Or.inr rfl)]
  set s := Real.sqrt ((n : ℝ) + 2)
  have hs4 : 4 ≤ s ^ 4 := by nlinarith
  apply gain_aux _ _ _ _ _ (Dst_pos hs1 (Or.inl rfl)) (Dst_pos hs1 (Or.inr rfl))
  have key : s ^ 2 * (Nst s 1 * Dst s (-1) + Nst s (-1) * Dst s 1) - 2 * (Dst s 1 * Dst s (-1)) =
      4 * (s ^ 4 - 2) := by
    unfold Dst Nst Pst
    ring
  rw [key]
  linarith

/-! ### Continuity and the limit `h → ∞` -/

private lemma seedResp_continuousAt (n : ℕ) {g₀ τ : ℝ}
    (h1 : rad n - (n + 1) * g₀ - τ ≠ 0)
    (h2 : (rad n - n * g₀) - 2 / ((rad n - (n + 1) * g₀) - τ) ≠ 0)
    (h3 : (rad n - (n + 1) * g₀) -
      1 / ((rad n - n * g₀) - 2 / ((rad n - (n + 1) * g₀) - τ)) ≠ 0) :
    ContinuousAt (fun g => seedResp n g τ) g₀ := by
  unfold seedResp
  have c1 : ContinuousAt (fun g : ℝ => rad n - (n + 1) * g - τ) g₀ := by fun_prop
  have c2 : ContinuousAt
      (fun g : ℝ => (rad n - n * g) - 2 / ((rad n - (n + 1) * g) - τ)) g₀ :=
    (by fun_prop : ContinuousAt (fun g : ℝ => rad n - n * g) g₀).sub
      (continuousAt_const.div₀ c1 h1)
  have c3 : ContinuousAt (fun g : ℝ => (rad n - (n + 1) * g) -
      1 / ((rad n - n * g) - 2 / ((rad n - (n + 1) * g) - τ))) g₀ :=
    (by fun_prop : ContinuousAt (fun g : ℝ => rad n - (n + 1) * g) g₀).sub
      (continuousAt_const.div₀ c2 h2)
  exact continuousAt_const.div₀ c3 h3

private lemma seedResp_continuousAt_star (n : ℕ) {τ : ℝ} (hτ : τ = 1 ∨ τ = -1) :
    ContinuousAt (fun g => seedResp n g τ) (1 / Real.sqrt (n + 2)) := by
  have hg0 : 0 ≤ 1 / Real.sqrt ((n : ℝ) + 2) := by positivity
  obtain ⟨ha, hβ, hγ⟩ := seed_denoms_pos n hg0 le_rfl hτ
  have hτ1 : τ ≤ 1 := by rcases hτ with rfl | rfl <;> norm_num
  exact seedResp_continuousAt n (by linarith) hβ.ne' hγ.ne'

private lemma treeGreen_tendsto (n : ℕ) :
    Tendsto (treeGreen n) atTop (𝓝 (1 / Real.sqrt (n + 2))) := by
  have hs : Real.sqrt ((n : ℝ) + 2) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
  have hinv : Tendsto (fun h : ℕ => ((h : ℝ) + 2)⁻¹) atTop (𝓝 0) :=
    (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop).inv_tendsto_atTop
  have hlim := (tendsto_const_nhds (x := (1 : ℝ)).sub hinv).div_const (Real.sqrt ((n : ℝ) + 2))
  rw [sub_zero] at hlim
  refine hlim.congr fun h => ?_
  have hh : (h : ℝ) + 2 ≠ 0 := by positivity
  unfold treeGreen
  field_simp
  ring

theorem seed_gain (n : ℕ) : ∃ h : ℕ, 1 < tseed n h := by
  have hF : ContinuousAt (fun g => Real.sqrt ((n : ℝ) + 2) / 2 *
      (seedResp n g 1 + seedResp n g (-1))) (1 / Real.sqrt (n + 2)) :=
    continuousAt_const.mul ((seedResp_continuousAt_star n (Or.inl rfl)).add
      (seedResp_continuousAt_star n (Or.inr rfl)))
  obtain ⟨h, hh⟩ :=
    ((hF.tendsto.comp (treeGreen_tendsto n)).eventually (lt_mem_nhds (tstar_gt_one n))).exists
  exact ⟨h, hh⟩

end BiluLinial.Counterexample
