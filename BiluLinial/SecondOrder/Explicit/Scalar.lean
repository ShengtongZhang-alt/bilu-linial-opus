/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.SecondOrder.Explicit.TreeNumeric

/-!
# The scalar amplification map

Blueprint node `C2-scalar` (source Section 6: "Starting strictly above `t₊`, iterating this scalar
map eventually exceeds `R/(q+1)` … above `t₊` the map is strictly larger than its argument").
With `R = thr n t = q t + 1/t` and `q t² < 1` (so `t < t₊ = 1/(q t)`), for `u₀ > t₊` there is a
uniform gain `ε > 0`: every `c ≥ u₀` with `R - q c > 0` has `1/(R - q c) ≥ c + ε`.
Proof: `1/(R - q c) - c = (c - t)(q c - 1/t) / (R - q c)`; for `c ≥ u₀` the numerator is at least
`(u₀ - t)(q u₀ - 1/t) > 0` and `0 < R - q c ≤ R`, so `ε = (u₀ - t)(q u₀ - 1/t) / R` works.
This replaces the source's convergence argument ("an increasing bounded iteration would converge
to a fixed point") by a linear lower bound, as in Part B's `amplify`.
-/

@[expose] public section

namespace BiluLinial.SecondOrder.Explicit

theorem step_gain (n : ℕ) {t : ℝ} (ht : 0 < t) (hqt : ((n : ℝ) + 2) * t ^ 2 < 1) {u₀ : ℝ}
    (hu₀ : 1 / (((n : ℝ) + 2) * t) < u₀) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ c : ℝ, u₀ ≤ c → 0 < thr n t - ((n : ℝ) + 2) * c →
      c + ε ≤ 1 / (thr n t - ((n : ℝ) + 2) * c) := by
  set q : ℝ := (n : ℝ) + 2 with hq_def
  have hq : 0 < q := by positivity
  have hR := thr_pos n ht
  have hqt0 : 0 < q * t := by positivity
  -- `q u₀ > 1/t`
  have hu1 : 1 / t < q * u₀ := by
    rw [div_lt_iff₀ hqt0] at hu₀
    rw [div_lt_iff₀ ht]
    linarith
  -- `t < u₀`
  have htu : t < u₀ := by
    have h1 : t < 1 / (q * t) := by
      rw [lt_div_iff₀ hqt0]
      nlinarith
    linarith
  refine ⟨(u₀ - t) * (q * u₀ - 1 / t) / thr n t,
    div_pos (mul_pos (by linarith) (by linarith)) hR, fun c hc hD => ?_⟩
  have key : 1 / (thr n t - q * c) - c = (c - t) * (q * c - 1 / t) / (thr n t - q * c) := by
    rw [eq_div_iff hD.ne', sub_mul, one_div_mul_cancel hD.ne']
    unfold thr
    field_simp
    ring
  have h1 : (u₀ - t) * (q * u₀ - 1 / t) ≤ (c - t) * (q * c - 1 / t) := by
    have e1 : u₀ - t ≤ c - t := by linarith
    have e2 : q * u₀ - 1 / t ≤ q * c - 1 / t := by nlinarith
    exact mul_le_mul e1 e2 (by linarith) (by linarith)
  have hc0 : 0 < c := by linarith
  have h2 : thr n t - q * c ≤ thr n t := by nlinarith
  have h3 : (u₀ - t) * (q * u₀ - 1 / t) / thr n t ≤
      (c - t) * (q * c - 1 / t) / (thr n t - q * c) :=
    div_le_div₀ (le_trans (mul_pos (by linarith) (by linarith)).le h1) h1 hD h2
  linarith

end BiluLinial.SecondOrder.Explicit
