/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecB.LawE
public import BiluLinial.Tight.SecB.Arith

/-!
# Mean shift (S1)

Node TB.S1 of `docs/tight/BP_SECB.md` (source lines 696–719; AUDIT-B §2.3, gap B-7).

**Input** (Section A, AUDIT-B §2.1, node CL1): for `1/d ≤ z ≤ 1` and the largest shifted deficit
`θ = t_z` (`CapPoint.DefZMax z θ`),
`θ² ≤ K {z + p(θ+b)/(dz) + p⁵(θ+b)/d + p²/d + p⁹/d² + 1/d + e^{-cp}}` with
`b = ε + K_b p⁴/d + 1/d` (`CL1Shape K K_b c`, the constants `K, K_b, c` absolute). The largest
deficit exists (`tShift`, `CapPoint.defZMax_tShift`).

**Sketch.** At `z = h = κ₀ p^{-4}` (`1/d ≤ h ≤ 1` for large `d`), write `√κ₀ = s`, `P = p`.
With `P⁸ ≤ d` (from `P^17 ≤ d²`), `ε ≤ P^{-3}`:
* the coefficient of `t` is `K A`, `A = P/(dh) + P⁵/d ≤ 2/(s² P³)`, and `K A ≤ s/P² = √h` once
  `P ≥ 2K/s³`;
* the constant terms `A b ≤ 2(2+K_b)/(s² P⁶)`, `P²/d ≤ P^{-6}`, `P⁹/d² ≤ P^{-8}`, `1/d ≤ P^{-8}`,
  `e^{-cP} ≤ 120/(cP)⁵` are each `≤ h/(5(K+1))` once `P` exceeds an explicit threshold in
  `K, K_b, c, κ₀` (`s1_scalar_real`).
Hence `t² ≤ (K+1) h + √h t`, so `t ≤ K_S √h` with `K_S = (1 + √(1 + 4(K+1)))/2` the positive
root of `x² = x + K + 1` (`s1_scalar`). The constant `K_S` depends only on `K`.

Then `E G_ii ≤ r y_i = (1+ε) y_i` (the cap) and `E X_ii ≥ (1 - t_h) y_i` (definition of `t_h`)
give `E(G_ii - X_ii) ≤ (t_h + ε) y_i ≤ (K_S + 1) √h y_i` (using `ε ≤ √h`), and `X_ii ≤ G_ii`
pointwise on the support (`hzN_le_hN`) gives `0 ≤ E(G_ii - X_ii)` (`mean_shift_pt`).

**Checks.** `S = ∅`: `t_h = 0`, nothing to prove. Zero source `y_i = 0`: physical rows vanish,
both sides `0`. `K = 0`: `K_S = (1+√5)/2`.
-/

@[expose] public section

namespace BiluLinial.Tight.SecB

open Matrix

universe u

/-- `b = ε + K_b p⁴/d + 1/d` of the closure inequality (AUDIT-B §1). -/
noncomputable def bCL (Kb : ℝ) (d p : ℕ) : ℝ :=
  epsP d p + Kb * (p : ℝ) ^ 4 / d + 1 / (d : ℝ)

/-- The right side of the closure inequality (CL1) at shift `z` and deficit `t`. -/
noncomputable def cl1Rhs (K Kb c : ℝ) (d p : ℕ) (z t : ℝ) : ℝ :=
  K * (z + (p : ℝ) * (t + bCL Kb d p) / (d * z) + (p : ℝ) ^ 5 * (t + bCL Kb d p) / d +
    (p : ℝ) ^ 2 / d + (p : ℝ) ^ 9 / (d : ℝ) ^ 2 + 1 / (d : ℝ) + Real.exp (-(c * p)))

/-- `K_S = (1 + √(1 + 4(K+1)))/2`, the positive root of `x² = x + K + 1`. -/
noncomputable def s1K (K : ℝ) : ℝ := (1 + Real.sqrt (1 + 4 * (K + 1))) / 2

theorem s1K_sq {K : ℝ} (hK : 0 ≤ K) : s1K K ^ 2 = s1K K + (K + 1) := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 1 + 4 * (K + 1) by linarith)
  rw [s1K]
  nlinarith

theorem one_le_s1K {K : ℝ} (hK : 0 ≤ K) : 1 ≤ s1K K := by
  have : 1 ≤ Real.sqrt (1 + 4 * (K + 1)) :=
    le_trans (le_of_eq Real.sqrt_one.symm) (Real.sqrt_le_sqrt (by linarith))
  rw [s1K]
  linarith

/-- From `t² ≤ (K+1) w² + w t` and `t ≥ 0`: `t ≤ K_S w`. -/
theorem le_s1K_of_quad {K t w : ℝ} (hK : 0 ≤ K) (hw : 0 ≤ w)
    (hq : t ^ 2 ≤ (K + 1) * w ^ 2 + w * t) : t ≤ s1K K * w := by
  by_contra hlt
  rw [not_le] at hlt
  have h1 := s1K_sq hK
  have h2 := one_le_s1K hK
  have hpos : 0 < (t - s1K K * w) * (t + (s1K K - 1) * w) :=
    mul_pos (by linarith) (by nlinarith)
  nlinarith

/-- **S1, scalar part, real form.** With `h = s²/P⁴`, `P⁸ ≤ d`, `P^17 ≤ d²`, `0 ≤ ε ≤ P^{-3}` and
`P` above the thresholds `u1`–`u4`, the closure inequality forces `t ≤ K_S s/P²`. -/
theorem s1_scalar_real {K Kb c s P Dd ε t : ℝ} (hK : 0 ≤ K) (hKb : 0 ≤ Kb) (hc : 0 < c)
    (hs0 : 0 < s) (hs1 : s ≤ 1) (hP2 : 2 ≤ P) (hd8 : P ^ 8 ≤ Dd) (hd17 : P ^ 17 ≤ Dd ^ 2)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / P ^ 3) (u1 : 2 * K ≤ s ^ 3 * P)
    (u2 : 10 * (K + 1) * (2 + Kb) ≤ s ^ 4 * P ^ 2) (u3 : 5 * (K + 1) ≤ s ^ 2 * P ^ 2)
    (u4 : 600 * (K + 1) ≤ s ^ 2 * c ^ 5 * P) (ht : 0 ≤ t)
    (hCL : t ^ 2 ≤ K * (s ^ 2 / P ^ 4 +
      P * (t + (ε + Kb * P ^ 4 / Dd + 1 / Dd)) / (Dd * (s ^ 2 / P ^ 4)) +
      P ^ 5 * (t + (ε + Kb * P ^ 4 / Dd + 1 / Dd)) / Dd + P ^ 2 / Dd + P ^ 9 / Dd ^ 2 +
      1 / Dd + Real.exp (-(c * P)))) :
    t ≤ s1K K * (s / P ^ 2) := by
  have hP : 0 < P := by linarith
  have hDd : 0 < Dd := lt_of_lt_of_le (by positivity) hd8
  have hK1 : 0 < K + 1 := by linarith
  have hs2 : s ^ 2 ≤ 1 := by nlinarith
  have hP37 : P ^ 3 ≤ Dd := le_trans (pow_le_pow_right₀ (by linarith) (by norm_num)) hd8
  have hP78 : P ^ 7 ≤ P ^ 8 := pow_le_pow_right₀ (by linarith) (by norm_num)
  -- the small parameter `b`
  have hb0 : 0 ≤ ε + Kb * P ^ 4 / Dd + 1 / Dd := by positivity
  have e1 : P ^ 4 / Dd ≤ 1 / P ^ 3 := by
    rw [div_le_div_iff₀ hDd (by positivity)]
    calc P ^ 4 * P ^ 3 = P ^ 7 := by ring
      _ ≤ P ^ 8 := hP78
      _ ≤ Dd := hd8
      _ = 1 * Dd := by ring
  have hb1 : ε + Kb * P ^ 4 / Dd + 1 / Dd ≤ (2 + Kb) / P ^ 3 := by
    have e2 : 1 / Dd ≤ 1 / P ^ 3 := one_div_le_one_div_of_le (by positivity) hP37
    have e3 : Kb * P ^ 4 / Dd ≤ Kb * (1 / P ^ 3) := by
      rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left e1 hKb
    have e4 : (2 + Kb) / P ^ 3 = 1 / P ^ 3 + Kb * (1 / P ^ 3) + 1 / P ^ 3 := by ring
    rw [e4]
    linarith
  -- the coefficient `A`
  have eA : P / (Dd * (s ^ 2 / P ^ 4)) = P ^ 5 / (s ^ 2 * Dd) := by
    rw [mul_div_assoc', div_div_eq_mul_div]
    ring
  have hA1 : P ^ 5 / (s ^ 2 * Dd) ≤ 1 / (s ^ 2 * P ^ 3) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    calc P ^ 5 * (s ^ 2 * P ^ 3) = s ^ 2 * P ^ 8 := by ring
      _ ≤ s ^ 2 * Dd := mul_le_mul_of_nonneg_left hd8 (sq_nonneg s)
      _ = 1 * (s ^ 2 * Dd) := by ring
  have hA2 : P ^ 5 / Dd ≤ 1 / (s ^ 2 * P ^ 3) := by
    rw [div_le_div_iff₀ hDd (by positivity)]
    calc P ^ 5 * (s ^ 2 * P ^ 3) = s ^ 2 * P ^ 8 := by ring
      _ ≤ 1 * P ^ 8 := mul_le_mul_of_nonneg_right hs2 (by positivity)
      _ ≤ Dd := by linarith
      _ = 1 * Dd := by ring
  set A : ℝ := P ^ 5 / (s ^ 2 * Dd) + P ^ 5 / Dd with hA_def
  have hA0 : 0 ≤ A := by positivity
  have hA : A ≤ 2 / (s ^ 2 * P ^ 3) := by
    have : A ≤ 1 / (s ^ 2 * P ^ 3) + 1 / (s ^ 2 * P ^ 3) := add_le_add hA1 hA2
    linarith [show 1 / (s ^ 2 * P ^ 3) + 1 / (s ^ 2 * P ^ 3) = 2 / (s ^ 2 * P ^ 3) by ring]
  have hKA : K * A ≤ s / P ^ 2 := by
    calc K * A ≤ K * (2 / (s ^ 2 * P ^ 3)) := mul_le_mul_of_nonneg_left hA hK
      _ ≤ s / P ^ 2 := by
        rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
        have := mul_le_mul_of_nonneg_right u1 (by positivity : (0 : ℝ) ≤ P ^ 2)
        calc K * 2 * P ^ 2 = 2 * K * P ^ 2 := by ring
          _ ≤ s ^ 3 * P * P ^ 2 := this
          _ = s * (s ^ 2 * P ^ 3) := by ring
  -- the five constant terms, each at most `hq`
  have hq0 : 0 < s ^ 2 / (5 * (K + 1) * P ^ 4) := by positivity
  have hP6 : 1 / P ^ 6 ≤ s ^ 2 / (5 * (K + 1) * P ^ 4) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have := mul_le_mul_of_nonneg_right u3 (by positivity : (0 : ℝ) ≤ P ^ 4)
    calc 1 * (5 * (K + 1) * P ^ 4) = 5 * (K + 1) * P ^ 4 := by ring
      _ ≤ s ^ 2 * P ^ 2 * P ^ 4 := this
      _ = s ^ 2 * P ^ 6 := by ring
  have c1 : A * (ε + Kb * P ^ 4 / Dd + 1 / Dd) ≤ s ^ 2 / (5 * (K + 1) * P ^ 4) := by
    calc A * (ε + Kb * P ^ 4 / Dd + 1 / Dd) ≤ 2 / (s ^ 2 * P ^ 3) * ((2 + Kb) / P ^ 3) :=
          mul_le_mul hA hb1 hb0 (by positivity)
      _ ≤ s ^ 2 / (5 * (K + 1) * P ^ 4) := by
        rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
        have := mul_le_mul_of_nonneg_right u2 (by positivity : (0 : ℝ) ≤ P ^ 4)
        calc 2 * (2 + Kb) * (5 * (K + 1) * P ^ 4) = 10 * (K + 1) * (2 + Kb) * P ^ 4 := by ring
          _ ≤ s ^ 4 * P ^ 2 * P ^ 4 := this
          _ = s ^ 2 * (s ^ 2 * P ^ 3 * P ^ 3) := by ring
  have c2 : P ^ 2 / Dd ≤ s ^ 2 / (5 * (K + 1) * P ^ 4) := by
    refine le_trans ?_ hP6
    rw [div_le_div_iff₀ hDd (by positivity)]
    calc P ^ 2 * P ^ 6 = P ^ 8 := by ring
      _ ≤ Dd := hd8
      _ = 1 * Dd := by ring
  have hP8 : 1 / P ^ 8 ≤ 1 / P ^ 6 :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by linarith) (by norm_num))
  have c3 : P ^ 9 / Dd ^ 2 ≤ s ^ 2 / (5 * (K + 1) * P ^ 4) := by
    refine le_trans (le_trans ?_ hP8) hP6
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    calc P ^ 9 * P ^ 8 = P ^ 17 := by ring
      _ ≤ Dd ^ 2 := hd17
      _ = 1 * Dd ^ 2 := by ring
  have c4 : 1 / Dd ≤ s ^ 2 / (5 * (K + 1) * P ^ 4) :=
    le_trans (le_trans (one_div_le_one_div_of_le (by positivity) hd8) hP8) hP6
  have c5 : Real.exp (-(c * P)) ≤ s ^ 2 / (5 * (K + 1) * P ^ 4) := by
    have he := Real.pow_div_factorial_le_exp (c * P) (by positivity) 5
    have hf : (Nat.factorial 5 : ℝ) = 120 := by norm_num [Nat.factorial]
    rw [hf, div_le_iff₀ (by norm_num : (0 : ℝ) < 120)] at he
    have hexp : 0 < Real.exp (c * P) := Real.exp_pos _
    rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ hexp (by positivity)]
    have h1 : 5 * (K + 1) * P ^ 4 * 120 ≤ s ^ 2 * (c * P) ^ 5 := by
      have := mul_le_mul_of_nonneg_right u4 (by positivity : (0 : ℝ) ≤ P ^ 4)
      calc 5 * (K + 1) * P ^ 4 * 120 = 600 * (K + 1) * P ^ 4 := by ring
        _ ≤ s ^ 2 * c ^ 5 * P * P ^ 4 := this
        _ = s ^ 2 * (c * P) ^ 5 := by ring
    have h2 : s ^ 2 * (c * P) ^ 5 ≤ s ^ 2 * (Real.exp (c * P) * 120) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    linarith
  -- assemble
  have hsplit : K * (s ^ 2 / P ^ 4 +
      P * (t + (ε + Kb * P ^ 4 / Dd + 1 / Dd)) / (Dd * (s ^ 2 / P ^ 4)) +
      P ^ 5 * (t + (ε + Kb * P ^ 4 / Dd + 1 / Dd)) / Dd + P ^ 2 / Dd + P ^ 9 / Dd ^ 2 +
      1 / Dd + Real.exp (-(c * P))) =
      K * (s ^ 2 / P ^ 4) + K * A * t +
        K * (A * (ε + Kb * P ^ 4 / Dd + 1 / Dd) + P ^ 2 / Dd + P ^ 9 / Dd ^ 2 + 1 / Dd +
          Real.exp (-(c * P))) := by
    rw [hA_def, ← eA]
    ring
  have hK5 : K * (A * (ε + Kb * P ^ 4 / Dd + 1 / Dd) + P ^ 2 / Dd + P ^ 9 / Dd ^ 2 + 1 / Dd +
      Real.exp (-(c * P))) ≤ s ^ 2 / P ^ 4 := by
    have hsum5 : A * (ε + Kb * P ^ 4 / Dd + 1 / Dd) + P ^ 2 / Dd + P ^ 9 / Dd ^ 2 + 1 / Dd +
        Real.exp (-(c * P)) ≤ 5 * (s ^ 2 / (5 * (K + 1) * P ^ 4)) := by linarith
    have h5q : K * (5 * (s ^ 2 / (5 * (K + 1) * P ^ 4))) ≤ s ^ 2 / P ^ 4 := by
      rw [show K * (5 * (s ^ 2 / (5 * (K + 1) * P ^ 4))) = K / (K + 1) * (s ^ 2 / P ^ 4) by
        field_simp]
      have : K / (K + 1) ≤ 1 := by rw [div_le_one hK1]; linarith
      exact mul_le_of_le_one_left (by positivity) this
    exact le_trans (mul_le_mul_of_nonneg_left hsum5 hK) h5q
  have hKAt : K * A * t ≤ s / P ^ 2 * t := mul_le_mul_of_nonneg_right hKA ht
  apply le_s1K_of_quad hK (by positivity)
  have e5 : (K + 1) * (s / P ^ 2) ^ 2 = K * (s ^ 2 / P ^ 4) + s ^ 2 / P ^ 4 := by ring
  rw [e5]
  rw [hsplit] at hCL
  linarith

/-- **S1, scalar part.** The closure inequality at `z = h` forces `t ≤ K_S √h`, for large `d`. -/
theorem s1_scalar {K Kb c : ℝ} (hK : 0 ≤ K) (hKb : 0 ≤ Kb) (hc : 0 < c) :
    Eventually fun _ _ d p h => ∀ t : ℝ, 0 ≤ t → t ^ 2 ≤ cl1Rhs K Kb c d p h t →
      t ≤ s1K K * Real.sqrt h := by
  intro c₀ κ₀ hc0 hc1 hk0 hk1
  obtain ⟨s, hs_def⟩ : ∃ s, s = Real.sqrt κ₀ := ⟨_, rfl⟩
  have hs0 : 0 < s := hs_def ▸ Real.sqrt_pos.2 hk0
  have hs1 : s ≤ 1 := hs_def ▸ Real.sqrt_le_one.mpr hk1
  have hκ : κ₀ = s ^ 2 := by rw [hs_def, Real.sq_sqrt hk0.le]
  obtain ⟨D, hD⟩ := eventually_base (1 + 2 * K / s ^ 3 + 10 * (K + 1) * (2 + Kb) / s ^ 4 +
    5 * (K + 1) / s ^ 2 + 600 * (K + 1) / (s ^ 2 * c ^ 5)) c₀ κ₀ hc0 hc1 hk0 hk1
  refine ⟨D, fun d hd => ?_⟩
  obtain ⟨hR, hB, hd17, hh, -, -⟩ := hD d hd
  intro t ht hCL
  have hP2 : (2 : ℝ) ≤ (pAt c₀ d : ℝ) := by exact_mod_cast hR.two_le_p
  have hd8 : (pAt c₀ d : ℝ) ^ 8 ≤ (d : ℝ) := regime_p8_le hR
  have hK1 : 0 ≤ K + 1 := by linarith
  have t1 : 2 * K / s ^ 3 ≤ (pAt c₀ d : ℝ) := by
    have := (show 0 ≤ 10 * (K + 1) * (2 + Kb) / s ^ 4 by positivity)
    have := (show 0 ≤ 5 * (K + 1) / s ^ 2 by positivity)
    have := (show 0 ≤ 600 * (K + 1) / (s ^ 2 * c ^ 5) by positivity); linarith
  have t2 : 10 * (K + 1) * (2 + Kb) / s ^ 4 ≤ (pAt c₀ d : ℝ) := by
    have := (show 0 ≤ 2 * K / s ^ 3 by positivity)
    have := (show 0 ≤ 5 * (K + 1) / s ^ 2 by positivity)
    have := (show 0 ≤ 600 * (K + 1) / (s ^ 2 * c ^ 5) by positivity); linarith
  have t3 : 5 * (K + 1) / s ^ 2 ≤ (pAt c₀ d : ℝ) := by
    have := (show 0 ≤ 2 * K / s ^ 3 by positivity)
    have := (show 0 ≤ 10 * (K + 1) * (2 + Kb) / s ^ 4 by positivity)
    have := (show 0 ≤ 600 * (K + 1) / (s ^ 2 * c ^ 5) by positivity); linarith
  have t4 : 600 * (K + 1) / (s ^ 2 * c ^ 5) ≤ (pAt c₀ d : ℝ) := by
    have := (show 0 ≤ 2 * K / s ^ 3 by positivity)
    have := (show 0 ≤ 10 * (K + 1) * (2 + Kb) / s ^ 4 by positivity)
    have := (show 0 ≤ 5 * (K + 1) / s ^ 2 by positivity); linarith
  have hPP : (pAt c₀ d : ℝ) ≤ (pAt c₀ d : ℝ) ^ 2 := by nlinarith
  have u1 : 2 * K ≤ s ^ 3 * (pAt c₀ d : ℝ) := by
    rw [div_le_iff₀ (by positivity)] at t1; linarith
  have u2 : 10 * (K + 1) * (2 + Kb) ≤ s ^ 4 * (pAt c₀ d : ℝ) ^ 2 := by
    rw [div_le_iff₀ (by positivity)] at t2
    nlinarith [mul_le_mul_of_nonneg_left hPP (by positivity : (0 : ℝ) ≤ s ^ 4)]
  have u3 : 5 * (K + 1) ≤ s ^ 2 * (pAt c₀ d : ℝ) ^ 2 := by
    rw [div_le_iff₀ (by positivity)] at t3
    nlinarith [mul_le_mul_of_nonneg_left hPP (by positivity : (0 : ℝ) ≤ s ^ 2)]
  have u4 : 600 * (K + 1) ≤ s ^ 2 * c ^ 5 * (pAt c₀ d : ℝ) := by
    rw [div_le_iff₀ (by positivity)] at t4; linarith
  have hz : hAt κ₀ (pAt c₀ d) = s ^ 2 / (pAt c₀ d : ℝ) ^ 4 := by rw [hh, hκ]
  have hsqrth : Real.sqrt (hAt κ₀ (pAt c₀ d)) = s / (pAt c₀ d : ℝ) ^ 2 := by
    rw [hz, Real.sqrt_div' _ (by positivity), Real.sqrt_sq hs0.le,
      show (pAt c₀ d : ℝ) ^ 4 = ((pAt c₀ d : ℝ) ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  rw [cl1Rhs, bCL, hz] at hCL
  rw [hsqrth]
  exact s1_scalar_real hK hKb hc hs0 hs1 hP2 hd8 hd17 (regime_eps_nonneg hR) (regime_eps_le hR)
    u1 u2 u3 u4 ht hCL

/-! ### The pointwise mean shift -/

section Pt

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The shifted deficit `t_z = sup_{i ∈ S, ±} (1 - E X^±_ii / y^±_i)₊` (normalized ratios `hzN`,
`1` at zero sources; `0` for `S = ∅`). -/
noncomputable def tShift (d p : ℕ) (z : ℝ) (yp ym : V → ℝ) (S : Finset V) : ℝ :=
  ((S.sup fun i =>
      (1 - lawE G p (aOf d p) yp ym S fun σ => hzN G (aOf d p) 1 z yp σ S i).toNNReal ⊔
      (1 - lawE G p (aOf d p) yp ym S fun σ => hzN G (aOf d p) (-1) z ym σ S i).toNNReal :
    NNReal) : ℝ)

theorem one_sub_le_tShift {d p : ℕ} {z : ℝ} {yp ym : V → ℝ} {S : Finset V} {i : V}
    (hi : i ∈ S) :
    1 - lawE G p (aOf d p) yp ym S (fun σ => hzN G (aOf d p) 1 z yp σ S i) ≤
        tShift G d p z yp ym S ∧
      1 - lawE G p (aOf d p) yp ym S (fun σ => hzN G (aOf d p) (-1) z ym σ S i) ≤
        tShift G d p z yp ym S := by
  have hle := Finset.le_sup (f := fun i =>
      (1 - lawE G p (aOf d p) yp ym S fun σ => hzN G (aOf d p) 1 z yp σ S i).toNNReal ⊔
      (1 - lawE G p (aOf d p) yp ym S fun σ => hzN G (aOf d p) (-1) z ym σ S i).toNNReal) hi
  constructor
  · refine le_trans (Real.le_coe_toNNReal _) ?_
    rw [tShift, NNReal.coe_le_coe]
    exact le_trans le_sup_left hle
  · refine le_trans (Real.le_coe_toNNReal _) ?_
    rw [tShift, NNReal.coe_le_coe]
    exact le_trans le_sup_right hle

theorem tShift_nonneg (d p : ℕ) (z : ℝ) (yp ym : V → ℝ) (S : Finset V) :
    0 ≤ tShift G d p z yp ym S := NNReal.coe_nonneg _

/-- **S1, pointwise.** At a point of the capped family and `z ≥ 0`:
`0 ≤ E G^±_ii - E X^±_ii ≤ (t_z + ε) y^±_i` for `i ∈ S`. -/
theorem mean_shift_pt {d p : ℕ} {S : Finset V} {lam : ℝ} {yp ym : V → ℝ}
    (hC : CapPt G d p S lam yp ym) {z : ℝ} (hz : 0 ≤ z) {i : V} (hi : i ∈ S) :
    (0 ≤ lawE G p (aOf d p) yp ym S (fun σ => greenP G (aOf d p) 1 yp σ S i i) -
        lawE G p (aOf d p) yp ym S (fun σ => shiftP G (aOf d p) 1 z yp σ S i i) ∧
      lawE G p (aOf d p) yp ym S (fun σ => greenP G (aOf d p) 1 yp σ S i i) -
          lawE G p (aOf d p) yp ym S (fun σ => shiftP G (aOf d p) 1 z yp σ S i i) ≤
        (tShift G d p z yp ym S + epsP d p) * yp i) ∧
    (0 ≤ lawE G p (aOf d p) yp ym S (fun σ => greenP G (aOf d p) (-1) ym σ S i i) -
        lawE G p (aOf d p) yp ym S (fun σ => shiftP G (aOf d p) (-1) z ym σ S i i) ∧
      lawE G p (aOf d p) yp ym S (fun σ => greenP G (aOf d p) (-1) ym σ S i i) -
          lawE G p (aOf d p) yp ym S (fun σ => shiftP G (aOf d p) (-1) z ym σ S i i) ≤
        (tShift G d p z yp ym S + epsP d p) * ym i) := by
  have hyp0 : ∀ k, 0 ≤ yp k := fun k => (hC.hyp k).1
  have hym0 : ∀ k, 0 ≤ ym k := fun k => (hC.hym k).1
  obtain ⟨hcapP, hcapM⟩ := hC.cap yp ym hC.hyp hC.hym i hi
  obtain ⟨htP, htM⟩ := one_sub_le_tShift G (d := d) (p := p) (z := z) (yp := yp) (ym := ym) hi
  have hr : rOf d p = 1 + epsP d p := by rw [epsP]; ring
  -- a generic branch argument
  have key : ∀ (τ : ℝ) (y : V → ℝ), (∀ k, 0 ≤ y k) →
      (∀ σ, wt G p (aOf d p) yp ym σ S ≠ 0 → (precN G (aOf d p) τ y σ S).PosDef) →
      lawE G p (aOf d p) yp ym S (fun σ => hN G (aOf d p) τ y σ S i) ≤ rOf d p →
      1 - lawE G p (aOf d p) yp ym S (fun σ => hzN G (aOf d p) τ z y σ S i) ≤
        tShift G d p z yp ym S →
      0 ≤ lawE G p (aOf d p) yp ym S (fun σ => greenP G (aOf d p) τ y σ S i i) -
          lawE G p (aOf d p) yp ym S (fun σ => shiftP G (aOf d p) τ z y σ S i i) ∧
        lawE G p (aOf d p) yp ym S (fun σ => greenP G (aOf d p) τ y σ S i i) -
            lawE G p (aOf d p) yp ym S (fun σ => shiftP G (aOf d p) τ z y σ S i i) ≤
          (tShift G d p z yp ym S + epsP d p) * y i := by
    intro τ y hy hpd hcap ht
    have eG : lawE G p (aOf d p) yp ym S (fun σ => greenP G (aOf d p) τ y σ S i i) =
        y i * lawE G p (aOf d p) yp ym S (fun σ => hN G (aOf d p) τ y σ S i) := by
      rw [← lawE_const_mul]
      exact lawE_congr G fun σ _ => greenP_diag G σ S (hy i)
    have eX : lawE G p (aOf d p) yp ym S (fun σ => shiftP G (aOf d p) τ z y σ S i i) =
        y i * lawE G p (aOf d p) yp ym S (fun σ => hzN G (aOf d p) τ z y σ S i) := by
      rw [← lawE_const_mul]
      exact lawE_congr G fun σ _ => shiftP_diag G σ S (hy i)
    have hxh : lawE G p (aOf d p) yp ym S (fun σ => hzN G (aOf d p) τ z y σ S i) ≤
        lawE G p (aOf d p) yp ym S (fun σ => hN G (aOf d p) τ y σ S i) :=
      lawE_mono G fun σ hσ => hzN_le_hN G (hpd σ hσ) hz hy i
    rw [eG, eX]
    constructor
    · nlinarith [hy i]
    · rw [hr] at hcap
      nlinarith [hy i]
  exact ⟨key 1 yp hyp0 (fun σ hσ => (posDef_of_wt_ne_zero G hσ).1) hcapP htP,
    key (-1) ym hym0 (fun σ hσ => (posDef_of_wt_ne_zero G hσ).2) hcapM htM⟩

end Pt

/-! ### S1 from the closure inequality -/

/-- `t_z` is the largest shifted deficit of a capped point (`DefZMax` of Section A). -/
theorem defZMax_tShift {d p : ℕ} (cp : CapPoint.{u} d p) (z : ℝ) :
    cp.DefZMax z (tShift cp.G d p z cp.yp cp.ym cp.S) := by
  refine ⟨tShift_nonneg cp.G d p z cp.yp cp.ym cp.S, fun i hi => one_sub_le_tShift cp.G hi, ?_⟩
  rcases cp.S.eq_empty_or_nonempty with hS | hS
  · left
    simp [tShift, hS]
  obtain ⟨i, hi, heq⟩ := Finset.exists_mem_eq_sup cp.S hS (fun i =>
      (1 - cp.E fun σ => cp.hzp z σ i).toNNReal ⊔ (1 - cp.E fun σ => cp.hzm z σ i).toNNReal)
  have ht : tShift cp.G d p z cp.yp cp.ym cp.S =
      max (max (1 - cp.E fun σ => cp.hzp z σ i) 0) (max (1 - cp.E fun σ => cp.hzm z σ i) 0) := by
    change ((cp.S.sup fun i => (1 - cp.E fun σ => cp.hzp z σ i).toNNReal ⊔
      (1 - cp.E fun σ => cp.hzm z σ i).toNNReal : NNReal) : ℝ) = _
    rw [heq, NNReal.coe_max, Real.coe_toNNReal', Real.coe_toNNReal']
  rcases eq_or_lt_of_le (tShift_nonneg cp.G d p z cp.yp cp.ym cp.S) with h0 | h0
  · left
    exact h0.symm
  right
  refine ⟨i, hi, ?_⟩
  rcases le_total (1 - cp.E fun σ => cp.hzp z σ i) (1 - cp.E fun σ => cp.hzm z σ i) with hab | hab
  · right
    have e : tShift cp.G d p z cp.yp cp.ym cp.S = max (1 - cp.E fun σ => cp.hzm z σ i) 0 := by
      rw [ht]; exact max_eq_right (max_le_max hab le_rfl)
    rw [e] at h0 ⊢
    exact (max_eq_left ((lt_max_iff.mp h0).resolve_right (lt_irrefl 0)).le).symm
  · left
    have e : tShift cp.G d p z cp.yp cp.ym cp.S = max (1 - cp.E fun σ => cp.hzp z σ i) 0 := by
      rw [ht]; exact max_eq_left (max_le_max hab le_rfl)
    rw [e] at h0 ⊢
    exact (max_eq_left ((lt_max_iff.mp h0).resolve_right (lt_irrefl 0)).le).symm

/-- The closure inequality (CL1) of Section A (AUDIT-B §2.1) with constants `K, K_b, c`: at every
capped point, every shift `z ∈ [1/d, 1]` and the largest shifted deficit `θ`,
`θ² ≤ cl1Rhs K K_b c d p z θ`. -/
def CL1Shape (K Kb c : ℝ) : Prop :=
  Eventually fun _ _ d p _ => ∀ cp : CapPoint.{u} d p, ∀ z θ : ℝ, 1 / (d : ℝ) ≤ z → z ≤ 1 →
    cp.DefZMax z θ → θ ^ 2 ≤ cl1Rhs K Kb c d p z θ

/-- The conclusion of (S1) at a point, with constant `K`: `t_h ≤ K √h` and
`0 ≤ E(G^±_ii - X^±_ii) ≤ (K + 1) √h y^±_i`. -/
def S1At {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (d p : ℕ) (h K : ℝ) (S : Finset V) (yp ym : V → ℝ) : Prop :=
  tShift G d p h yp ym S ≤ K * Real.sqrt h ∧ ∀ i ∈ S,
    (0 ≤ lawE G p (aOf d p) yp ym S (fun σ => greenP G (aOf d p) 1 yp σ S i i) -
        lawE G p (aOf d p) yp ym S (fun σ => shiftP G (aOf d p) 1 h yp σ S i i) ∧
      lawE G p (aOf d p) yp ym S (fun σ => greenP G (aOf d p) 1 yp σ S i i) -
          lawE G p (aOf d p) yp ym S (fun σ => shiftP G (aOf d p) 1 h yp σ S i i) ≤
        (K + 1) * Real.sqrt h * yp i) ∧
    (0 ≤ lawE G p (aOf d p) yp ym S (fun σ => greenP G (aOf d p) (-1) ym σ S i i) -
        lawE G p (aOf d p) yp ym S (fun σ => shiftP G (aOf d p) (-1) h ym σ S i i) ∧
      lawE G p (aOf d p) yp ym S (fun σ => greenP G (aOf d p) (-1) ym σ S i i) -
          lawE G p (aOf d p) yp ym S (fun σ => shiftP G (aOf d p) (-1) h ym σ S i i) ≤
        (K + 1) * Real.sqrt h * ym i)

/-- Eventually `0 < h`, `1/d ≤ h ≤ 1` and `ε ≤ √h`. -/
theorem eventually_h_facts : Eventually fun _ _ d p h =>
    TRegime d p ∧ 0 < h ∧ 1 / (d : ℝ) ≤ h ∧ h ≤ 1 ∧ epsP d p ≤ Real.sqrt h := by
  intro c₀ κ₀ hc0 hc1 hk0 hk1
  obtain ⟨s, hs_def⟩ : ∃ s, s = Real.sqrt κ₀ := ⟨_, rfl⟩
  have hs0 : 0 < s := hs_def ▸ Real.sqrt_pos.2 hk0
  have hs1 : s ≤ 1 := hs_def ▸ Real.sqrt_le_one.mpr hk1
  have hκ : κ₀ = s ^ 2 := by rw [hs_def, Real.sq_sqrt hk0.le]
  obtain ⟨D, hD⟩ := eventually_base (1 + 1 / s ^ 2) c₀ κ₀ hc0 hc1 hk0 hk1
  refine ⟨D, fun d hd => ?_⟩
  obtain ⟨hR, hB, -, hh, -, -⟩ := hD d hd
  have hP2 : (2 : ℝ) ≤ (pAt c₀ d : ℝ) := by exact_mod_cast hR.two_le_p
  have hd8 : (pAt c₀ d : ℝ) ^ 8 ≤ (d : ℝ) := regime_p8_le hR
  have hz : hAt κ₀ (pAt c₀ d) = s ^ 2 / (pAt c₀ d : ℝ) ^ 4 := by rw [hh, hκ]
  have hsP : 1 ≤ s ^ 2 * (pAt c₀ d : ℝ) := by
    have : 1 / s ^ 2 ≤ (pAt c₀ d : ℝ) := by
      have := (show 0 ≤ 1 / s ^ 2 by positivity); linarith
    rw [div_le_iff₀ (by positivity)] at this; linarith
  refine ⟨hR, by rw [hz]; positivity, ?_, ?_, ?_⟩
  · rw [hz, div_le_div_iff₀ (lt_of_lt_of_le (by positivity) hd8) (by positivity)]
    have h1 : (pAt c₀ d : ℝ) ^ 4 ≤ (pAt c₀ d : ℝ) ^ 7 :=
      pow_le_pow_right₀ (by linarith) (by norm_num)
    have h2 : (pAt c₀ d : ℝ) ^ 7 ≤ s ^ 2 * (pAt c₀ d : ℝ) ^ 8 := by
      nlinarith [pow_pos (by linarith : (0 : ℝ) < pAt c₀ d) 7]
    nlinarith [mul_le_mul_of_nonneg_left hd8 (sq_nonneg s)]
  · rw [hz, div_le_one (by positivity)]
    have : (1 : ℝ) ≤ (pAt c₀ d : ℝ) ^ 4 := one_le_pow₀ (by linarith)
    nlinarith
  · have hsq : Real.sqrt (hAt κ₀ (pAt c₀ d)) = s / (pAt c₀ d : ℝ) ^ 2 := by
      rw [hz, Real.sqrt_div' _ (by positivity), Real.sqrt_sq hs0.le,
        show (pAt c₀ d : ℝ) ^ 4 = ((pAt c₀ d : ℝ) ^ 2) ^ 2 by ring,
        Real.sqrt_sq (by positivity)]
    rw [hsq]
    refine le_trans (regime_eps_le hR) ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : 1 ≤ s * (pAt c₀ d : ℝ) := by nlinarith
    nlinarith [pow_pos (by linarith : (0 : ℝ) < pAt c₀ d) 2]

/-- **S1** from the closure inequality: with `K_S = s1K K`, eventually every capped point
satisfies `t_h ≤ K_S √h` and `0 ≤ E(G^±_ii - X^±_ii) ≤ (K_S + 1) √h y^±_i`. -/
theorem mean_shift_of_cl1 {K Kb c : ℝ} (hK : 0 ≤ K) (hKb : 0 ≤ Kb) (hc : 0 < c)
    (hCL : CL1Shape.{u} K Kb c) :
    Eventually fun _ _ d p h => ∀ cp : CapPoint.{u} d p,
      S1At cp.G d p h (s1K K) cp.S cp.yp cp.ym := by
  refine ((hCL.and (s1_scalar hK hKb hc)).and eventually_h_facts).mono ?_
  rintro c₀ κ₀ d p h ⟨⟨hcl, hsc⟩, hR, h0, h1d, h1, hε⟩ cp
  have hC : CapPt cp.G d p cp.S cp.lam cp.yp cp.ym := ⟨cp.ctx, cp.hyp, cp.hym⟩
  have ht0 := tShift_nonneg cp.G d p h cp.yp cp.ym cp.S
  have ht : tShift cp.G d p h cp.yp cp.ym cp.S ≤ s1K K * Real.sqrt h :=
    hsc _ ht0 (hcl cp h _ h1d h1 (defZMax_tShift cp h))
  refine ⟨ht, fun i hi => ?_⟩
  obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ := mean_shift_pt cp.G hC h0.le hi
  have hyp := (hC.hyp i).1
  have hym := (hC.hym i).1
  have hb : tShift cp.G d p h cp.yp cp.ym cp.S + epsP d p ≤ (s1K K + 1) * Real.sqrt h := by
    linarith
  exact ⟨⟨a1, le_trans a2 (mul_le_mul_of_nonneg_right hb hyp)⟩,
    ⟨b1, le_trans b2 (mul_le_mul_of_nonneg_right hb hym)⟩⟩

/-- The part of (C2) (Section A) used by DR1 and W1, with constant `K_δ`: at every capped point
and every `w ∈ S`, `1 - E h^±_w ≤ K_δ δ̄` and `a² S^±_w ≤ K_δ δ̄`. -/
def C2RowShape (Kδ : ℝ) : Prop :=
  Eventually fun _ _ d p _ => ∀ cp : CapPoint.{u} d p, ∀ w ∈ cp.S,
    1 - cp.E (fun σ => cp.hp σ w) ≤ Kδ * dbar d p ∧
      1 - cp.E (fun σ => cp.hm σ w) ≤ Kδ * dbar d p ∧
      aOf d p ^ 2 * rowSP cp.G d p cp.yp cp.ym cp.S w ≤ Kδ * dbar d p ∧
      aOf d p ^ 2 * rowSM cp.G d p cp.yp cp.ym cp.S w ≤ Kδ * dbar d p

end BiluLinial.Tight.SecB
