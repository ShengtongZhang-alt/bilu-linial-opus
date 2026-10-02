/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.SecondOrder.Explicit.Defs

/-!
# Numerics of the tree response

Blueprint node `C2-treenum` (source Section 6: "The root response of a complete `q`-ary tree of
height `h` at `R` converges increasingly to `t`"). With `R = thr n t = q t + 1/t`, `t > 0`:

* `0 < g_h < t` and `R - q g_h > 1/t > 0` for every `h` (induction: `g₀ = 1/R < t` since
  `t R = q t² + 1`, and `g_h < t` gives `R - q g_h > R - q t = 1/t`);
* if moreover `q t² < 1`, then `g_h → t`: `t - g_{h+1} = q t g_{h+1} (t - g_h) ≤ q t² (t - g_h)`, so
  `0 ≤ t - g_h ≤ (q t²)^h (t - g₀)`.
-/

@[expose] public section

namespace BiluLinial.SecondOrder.Explicit

open Filter Topology

theorem thr_pos (n : ℕ) {t : ℝ} (ht : 0 < t) : 0 < thr n t := by
  unfold thr
  positivity

theorem thr_sub_mul (n : ℕ) (t : ℝ) : thr n t - ((n : ℝ) + 2) * t = 1 / t := by
  unfold thr
  ring

theorem treeResp_pos_lt (n : ℕ) {t : ℝ} (ht : 0 < t) (h : ℕ) :
    0 < treeResp n (thr n t) h ∧ treeResp n (thr n t) h < t := by
  have hq : (0 : ℝ) < n + 2 := by positivity
  induction h with
  | zero =>
    have hR := thr_pos n ht
    refine ⟨one_div_pos.2 hR, ?_⟩
    change 1 / thr n t < t
    rw [div_lt_iff₀ hR]
    have e : t * thr n t = ((n : ℝ) + 2) * t ^ 2 + 1 := by
      unfold thr
      field_simp
    rw [e]
    have : 0 < ((n : ℝ) + 2) * t ^ 2 := by positivity
    linarith
  | succ h ih =>
    have hd : 1 / t < thr n t - ((n : ℝ) + 2) * treeResp n (thr n t) h := by
      rw [← thr_sub_mul n t]
      have := mul_lt_mul_of_pos_left ih.2 hq
      linarith
    have hd0 : 0 < thr n t - ((n : ℝ) + 2) * treeResp n (thr n t) h :=
      lt_trans (one_div_pos.2 ht) hd
    change 0 < 1 / (thr n t - ((n : ℝ) + 2) * treeResp n (thr n t) h) ∧
      1 / (thr n t - ((n : ℝ) + 2) * treeResp n (thr n t) h) < t
    refine ⟨one_div_pos.2 hd0, ?_⟩
    calc 1 / (thr n t - ((n : ℝ) + 2) * treeResp n (thr n t) h) < 1 / (1 / t) :=
          one_div_lt_one_div_of_lt (one_div_pos.2 ht) hd
      _ = t := one_div_one_div t

theorem treeResp_denom_pos (n : ℕ) {t : ℝ} (ht : 0 < t) (h : ℕ) :
    0 < thr n t - ((n : ℝ) + 2) * treeResp n (thr n t) h := by
  have hq : (0 : ℝ) < n + 2 := by positivity
  have h1 := mul_lt_mul_of_pos_left (treeResp_pos_lt n ht h).2 hq
  have h2 := thr_sub_mul n t
  have h3 : 0 < 1 / t := one_div_pos.2 ht
  linarith

theorem treeResp_succ (n : ℕ) (R : ℝ) (h : ℕ) :
    treeResp n R (h + 1) = 1 / (R - ((n : ℝ) + 2) * treeResp n R h) := rfl

theorem treeResp_tendsto (n : ℕ) {t : ℝ} (ht : 0 < t) (hqt : ((n : ℝ) + 2) * t ^ 2 < 1) :
    Tendsto (treeResp n (thr n t)) atTop (𝓝 t) := by
  set g := treeResp n (thr n t) with hg_def
  set ρ := ((n : ℝ) + 2) * t ^ 2 with hρ_def
  have hq : (0 : ℝ) < n + 2 := by positivity
  have hρ0 : 0 ≤ ρ := by positivity
  have hstep : ∀ h, t - g (h + 1) ≤ ρ * (t - g h) := by
    intro h
    have hlt := (treeResp_pos_lt n ht h).2
    have hlt' := (treeResp_pos_lt n ht (h + 1)).2
    have hpos' := (treeResp_pos_lt n ht (h + 1)).1
    have hD := treeResp_denom_pos n ht h
    have e : g (h + 1) * (thr n t - ((n : ℝ) + 2) * g h) = 1 := by
      rw [hg_def, treeResp_succ]
      field_simp
    have key : t - g (h + 1) = ((n : ℝ) + 2) * t * g (h + 1) * (t - g h) := by
      have e2 : thr n t = ((n : ℝ) + 2) * t + 1 / t := rfl
      rw [e2] at e
      field_simp at e
      field_simp
      linear_combination (-1 : ℝ) * e
    rw [key]
    have h1 : ((n : ℝ) + 2) * t * g (h + 1) ≤ ρ := by
      rw [hρ_def, sq]
      have := mul_le_mul_of_nonneg_left hlt'.le (by positivity : (0 : ℝ) ≤ ((n : ℝ) + 2) * t)
      linarith
    exact mul_le_mul_of_nonneg_right h1 (by linarith)
  have hbound : ∀ h, t - g h ≤ ρ ^ h * (t - g 0) := by
    intro h
    induction h with
    | zero => simp
    | succ h ih =>
      calc t - g (h + 1) ≤ ρ * (t - g h) := hstep h
        _ ≤ ρ * (ρ ^ h * (t - g 0)) := mul_le_mul_of_nonneg_left ih hρ0
        _ = ρ ^ (h + 1) * (t - g 0) := by ring
  have hlim : Tendsto (fun h : ℕ => ρ ^ h * (t - g 0)) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hqt).mul_const (t - g 0)
  have hsq : Tendsto (fun h => t - g h) atTop (𝓝 0) :=
    squeeze_zero (fun h => by linarith [(treeResp_pos_lt n ht h).2]) hbound hlim
  have := (tendsto_const_nhds (x := t)).sub hsq
  simpa using this

end BiluLinial.SecondOrder.Explicit
