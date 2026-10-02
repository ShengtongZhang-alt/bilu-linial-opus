/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import Mathlib

/-!
# The coefficients of `e^{t²/2} / cosh t`

Part D (`docs/second_order_bilu_linial_tight.tex`, Section 1.2, before eq. (E4)). The
high-order Rademacher-to-Gaussian comparison uses the coefficients `c_j` of
`e^{t²/2} / cosh t = Σ_j c_j t^{2j}`. Since `cosh t = Σ_m t^{2m}/(2m)!` and
`e^{t²/2} = Σ_k t^{2k}/(2^k k!)`, they are determined by `c_0 = 1` and the Cauchy-product recursion
`Σ_{i ≤ k} c_i / (2(k-i))! = 1/(2^k k!)`.

Main results:
* `ecoef`: the coefficients, `ecoef_rec`: the recursion (for every `k`, including `k = 0`);
* `ecoef_zero`, `ecoef_one`, `ecoef_two`, `ecoef_three`: `c_0 = 1`, `c_1 = 0`, `c_2 = 1/12`,
  `c_3 = -1/45`;
* `abs_ecoef_le_one`: `|c_j| ≤ 1` for all `j`;
* `sum_inv_factorial_two_mul_succ_le`: `Σ_{m < K} 1/(2(m+1))! ≤ 2/3`, used in the remainder bounds.
-/

@[expose] public section

namespace BiluLinial.Tight

open Finset

/-- The coefficients `c_j` of `e^{t²/2}/cosh t = Σ_j c_j t^{2j}` (paper, Section 1.2, before
eq. (E4)): `c_0 = 1` and `c_k = 1/(2^k k!) - Σ_{i < k} c_i/(2(k-i))!` for `k ≥ 1`. -/
noncomputable def ecoef : ℕ → ℝ
  | 0 => 1
  | k + 1 => 1 / (2 ^ (k + 1) * ((k + 1).factorial : ℝ)) -
      ∑ i : Fin (k + 1), ecoef i / ((2 * (k + 1 - i)).factorial : ℝ)
decreasing_by exact i.isLt

@[simp] theorem ecoef_zero : ecoef 0 = 1 := by rw [ecoef]

theorem ecoef_succ (k : ℕ) : ecoef (k + 1) = 1 / (2 ^ (k + 1) * ((k + 1).factorial : ℝ)) -
    ∑ i ∈ range (k + 1), ecoef i / ((2 * (k + 1 - i)).factorial : ℝ) := by
  rw [ecoef, Fin.sum_univ_eq_sum_range (fun i => ecoef i / ((2 * (k + 1 - i)).factorial : ℝ))]

/-- The defining recursion of `c_j`: `Σ_{i ≤ k} c_i / (2(k-i))! = 1/(2^k k!)` for every `k`
(coefficient of `t^{2k}` in `(Σ c_j t^{2j}) · cosh t = e^{t²/2}`). -/
theorem ecoef_rec (k : ℕ) :
    ∑ i ∈ range (k + 1), ecoef i / ((2 * (k - i)).factorial : ℝ) =
      1 / (2 ^ k * (k.factorial : ℝ)) := by
  cases k with
  | zero => simp
  | succ n =>
    rw [sum_range_succ, ecoef_succ n]
    simp

@[simp] theorem ecoef_one : ecoef 1 = 0 := by
  rw [ecoef_succ]; norm_num [Nat.factorial]

theorem ecoef_two : ecoef 2 = 1 / 12 := by
  rw [ecoef_succ]; norm_num [sum_range_succ, Nat.factorial]

theorem ecoef_three : ecoef 3 = -1 / 45 := by
  rw [ecoef_succ]; norm_num [sum_range_succ, Nat.factorial, ecoef_two]

/-- `(2(m+1))! ≥ 2 · 4^m`. -/
theorem two_mul_four_pow_le_factorial (m : ℕ) : 2 * 4 ^ m ≤ (2 * (m + 1)).factorial := by
  have h := Nat.factorial_mul_pow_le_factorial (m := 1) (n := 2 * m + 1)
  have e1 : 1 + (2 * m + 1) = 2 * (m + 1) := by ring
  have e2 : (2 : ℕ) ^ (2 * m + 1) = 2 * 4 ^ m := by
    rw [pow_succ, pow_mul]; norm_num; ring
  rw [e1] at h
  simpa [e2] using h

/-- `Σ_{m < K} 1/(2(m+1))! ≤ 2/3` (a partial sum of `cosh 1 - 1 ≈ 0.543`). -/
theorem sum_inv_factorial_two_mul_succ_le (K : ℕ) :
    ∑ m ∈ range K, (1 : ℝ) / ((2 * (m + 1)).factorial : ℝ) ≤ 2 / 3 := by
  have hterm : ∀ m, (1 : ℝ) / ((2 * (m + 1)).factorial : ℝ) ≤ (1 / 2) * (1 / 4 : ℝ) ^ m := by
    intro m
    have h := two_mul_four_pow_le_factorial m
    have h' : (2 : ℝ) * 4 ^ m ≤ ((2 * (m + 1)).factorial : ℝ) := by exact_mod_cast h
    have hpos : (0 : ℝ) < 2 * 4 ^ m := by positivity
    rw [div_le_iff₀ (by positivity)]
    calc (1 : ℝ) = (1 / 2) * (1 / 4) ^ m * (2 * 4 ^ m) := by
          rw [one_div_pow]; field_simp
      _ ≤ (1 / 2) * (1 / 4) ^ m * ((2 * (m + 1)).factorial : ℝ) := by gcongr
  calc ∑ m ∈ range K, (1 : ℝ) / ((2 * (m + 1)).factorial : ℝ)
      ≤ ∑ m ∈ range K, (1 / 2) * (1 / 4 : ℝ) ^ m := sum_le_sum fun m _ => hterm m
    _ = (1 / 2) * ∑ m ∈ range K, (1 / 4 : ℝ) ^ m := by rw [mul_sum]
    _ ≤ (1 / 2) * ((1 / 4 : ℝ) ^ 0 / (1 - 1 / 4)) := by
        gcongr
        rw [range_eq_Ico]
        exact geom_sum_Ico_le_of_lt_one (by norm_num) (by norm_num)
    _ = 2 / 3 := by norm_num

/-- `|c_j| ≤ 1` for every `j`. Proof: strong induction on the recursion; for `k ≥ 2`,
`|c_k| ≤ 1/(2^k k!) + Σ_{m=1}^{k} 1/(2m)! ≤ 1/8 + 2/3`. -/
theorem abs_ecoef_le_one (j : ℕ) : |ecoef j| ≤ 1 := by
  induction j using Nat.strong_induction_on with
  | _ k ih =>
    match k, ih with
    | 0, _ => simp
    | 1, _ => simp
    | n + 2, ih =>
      rw [ecoef_succ]
      have h1 : (1 : ℝ) / (2 ^ (n + 1 + 1) * ((n + 1 + 1).factorial : ℝ)) ≤ 1 / 8 := by
        have hf : (2 : ℝ) ≤ ((n + 2).factorial : ℝ) := by
          have : 2 ≤ (n + 2).factorial := by
            calc 2 = (2 : ℕ).factorial := rfl
              _ ≤ (n + 2).factorial := Nat.factorial_le (by omega)
          exact_mod_cast this
        have hp : (4 : ℝ) ≤ 2 ^ (n + 2) := by
          calc (4 : ℝ) = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ (n + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
      have h2 : |∑ i ∈ range (n + 1 + 1), ecoef i / ((2 * (n + 1 + 1 - i)).factorial : ℝ)| ≤
          2 / 3 := by
        calc |∑ i ∈ range (n + 1 + 1), ecoef i / ((2 * (n + 1 + 1 - i)).factorial : ℝ)|
            ≤ ∑ i ∈ range (n + 1 + 1), |ecoef i / ((2 * (n + 1 + 1 - i)).factorial : ℝ)| :=
              abs_sum_le_sum_abs _ _
          _ ≤ ∑ i ∈ range (n + 1 + 1), (1 : ℝ) / ((2 * (n + 1 + 1 - i)).factorial : ℝ) := by
              apply sum_le_sum
              intro i hi
              rw [abs_div, Nat.abs_cast]
              gcongr
              exact ih i (by simp at hi; omega)
          _ = ∑ m ∈ range (n + 1 + 1), (1 : ℝ) / ((2 * (m + 1)).factorial : ℝ) := by
              rw [← sum_range_reflect]
              apply sum_congr rfl
              intro m hm
              simp at hm
              congr 3
              omega
          _ ≤ 2 / 3 := sum_inv_factorial_two_mul_succ_le _
      have h0 : (0 : ℝ) ≤ 1 / (2 ^ (n + 1 + 1) * ((n + 1 + 1).factorial : ℝ)) := by positivity
      calc |1 / (2 ^ (n + 1 + 1) * ((n + 1 + 1).factorial : ℝ)) -
            ∑ i ∈ range (n + 1 + 1), ecoef i / ((2 * (n + 1 + 1 - i)).factorial : ℝ)|
          ≤ |1 / (2 ^ (n + 1 + 1) * ((n + 1 + 1).factorial : ℝ))| +
            |∑ i ∈ range (n + 1 + 1), ecoef i / ((2 * (n + 1 + 1 - i)).factorial : ℝ)| :=
            abs_sub _ _
        _ ≤ 1 / 8 + 2 / 3 := by rw [abs_of_nonneg h0]; linarith
        _ ≤ 1 := by norm_num

end BiluLinial.Tight
