/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import Mathlib

/-!
# Taylor's bound for a chain of derivatives

Part D (`docs/second_order_bilu_linial_tight.tex`, Section 1.2). Both comparisons (E1) and (E4)
expand a function at `0` by Taylor's theorem. We state Taylor's bound for a *chain*
`F 0, F 1, …, F n` of functions with `F (m+1)` the derivative of `F m` on an order-connected set
`I ∋ 0` (e.g. `I = ℝ` or `I = [-1, 1]`); this form applies directly to restrictions of
multivariate functions to coordinate lines, whose derivatives are partial derivatives.

* `taylor_chain_bound`: if `|F n| ≤ M` on `I`, then for `x ∈ I`,
  `|F 0 x - Σ_{m<n} F m 0 · x^m/m!| ≤ M |x|^n / n!`.
-/

@[expose] public section

namespace BiluLinial.Tight

open Finset Set

/-- The derivative of `y ↦ Σ_{m ≤ n} a_m y^m/m!` is `y ↦ Σ_{m < n} a_{m+1} y^m/m!`. -/
theorem hasDerivAt_taylorPoly (a : ℕ → ℝ) (n : ℕ) (y : ℝ) :
    HasDerivAt (fun y => ∑ m ∈ range (n + 1), a m * y ^ m / m.factorial)
      (∑ m ∈ range n, a (m + 1) * y ^ m / m.factorial) y := by
  have h : HasDerivAt (fun y => ∑ m ∈ range (n + 1), a m * y ^ m / m.factorial)
      (∑ m ∈ range (n + 1), a m * ((m : ℝ) * y ^ (m - 1)) / m.factorial) y :=
    HasDerivAt.fun_sum (u := range (n + 1)) (A := fun m y => a m * y ^ m / m.factorial)
      (A' := fun m => a m * ((m : ℝ) * y ^ (m - 1)) / m.factorial)
      (fun m _ => ((hasDerivAt_pow m y).const_mul (a m)).div_const _)
  refine h.congr_deriv ?_
  rw [sum_range_succ']
  simp only [Nat.cast_zero, zero_mul, mul_zero, zero_div, add_zero]
  apply sum_congr rfl
  intro m _
  rw [Nat.factorial_succ, Nat.add_sub_cancel]
  push_cast
  field_simp

/-- A one-sided version of Taylor's bound (`x ≥ 0`) for the remainder `g` with derivative `g'`. -/
private theorem remainder_bound_nonneg {g g' : ℝ → ℝ} {x M : ℝ} (n : ℕ) (hx : 0 ≤ x)
    (hg : ∀ y ∈ Icc 0 x, HasDerivAt g (g' y) y) (hg0 : g 0 = 0)
    (hb : ∀ y ∈ Icc 0 x, |g' y| ≤ M * y ^ n / n.factorial) :
    |g x| ≤ M * x ^ (n + 1) / (n + 1).factorial := by
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary (f := g) (f' := g') (a := 0)
    (b := x) (B := fun y => M * y ^ (n + 1) / (n + 1).factorial)
    (B' := fun y => M * y ^ n / n.factorial)
    (fun y hy => (hg y hy).continuousAt.continuousWithinAt)
    (fun y hy => (hg y (Ico_subset_Icc_self hy)).hasDerivWithinAt)
    (by simp [hg0])
    (fun y => by
      have h := ((hasDerivAt_pow (n + 1) y).const_mul M).div_const ((n + 1).factorial : ℝ)
      refine h.congr_deriv ?_
      rw [Nat.factorial_succ, Nat.add_sub_cancel]
      push_cast
      field_simp)
    (fun y hy => hb y (Ico_subset_Icc_self hy))
    (right_mem_Icc.mpr hx)
  simpa using key

/-- **Taylor's bound for a chain of derivatives.** Let `I ∋ 0` be order-connected and let
`F 0, …, F n` satisfy `(F m)' = F (m+1)` on `I` for `m < n`. If `|F n| ≤ M` on `I`, then for every
`x ∈ I`, `|F 0 x - Σ_{m<n} F m 0 · x^m/m!| ≤ M |x|^n / n!`. -/
theorem taylor_chain_bound {I : Set ℝ} (hI : I.OrdConnected) (h0 : (0 : ℝ) ∈ I) :
    ∀ (n : ℕ) (F : ℕ → ℝ → ℝ), (∀ m < n, ∀ t ∈ I, HasDerivAt (F m) (F (m + 1) t) t) →
    ∀ (M : ℝ), (∀ t ∈ I, |F n t| ≤ M) →
    ∀ x ∈ I, |F 0 x - ∑ m ∈ range n, F m 0 * x ^ m / m.factorial| ≤
      M * |x| ^ n / n.factorial := by
  intro n
  induction n with
  | zero => intro F _ M hM x hx; simpa using hM x hx
  | succ n ih =>
    intro F hF M hM x hx
    have ih' := ih (fun m => F (m + 1)) (fun m hm t ht => hF (m + 1) (by omega) t ht) M hM
    set g : ℝ → ℝ := fun y => F 0 y - ∑ m ∈ range (n + 1), F m 0 * y ^ m / m.factorial with hg_def
    set g' : ℝ → ℝ := fun y => F 1 y - ∑ m ∈ range n, F (m + 1) 0 * y ^ m / m.factorial
      with hg'_def
    have hg : ∀ y ∈ I, HasDerivAt g (g' y) y := fun y hy =>
      (hF 0 (by omega) y hy).sub (hasDerivAt_taylorPoly (fun m => F m 0) n y)
    have hg0 : g 0 = 0 := by
      simp only [hg_def]
      rw [sum_range_succ']
      simp
    have hb : ∀ y ∈ I, |g' y| ≤ M * |y| ^ n / n.factorial := fun y hy => ih' y hy
    change |g x| ≤ M * |x| ^ (n + 1) / (n + 1).factorial
    rcases le_total 0 x with hx0 | hx0
    · rw [abs_of_nonneg hx0]
      refine remainder_bound_nonneg n hx0 (fun y hy => hg y (hI.out h0 hx hy)) hg0 ?_
      intro y hy
      have := hb y (hI.out h0 hx hy)
      rwa [abs_of_nonneg hy.1] at this
    · -- reflect: `h y = g (-y)` on `[0, -x]`
      have hneg : 0 ≤ -x := neg_nonneg.mpr hx0
      have hmem : ∀ y ∈ Icc 0 (-x), -y ∈ I := fun y hy =>
        hI.out hx h0 ⟨by linarith [hy.2], by linarith [hy.1]⟩
      have key := remainder_bound_nonneg (g := fun y => g (-y)) (g' := fun y => -g' (-y))
        (M := M) n hneg
        (fun y hy => by
          have h1 := (hg (-y) (hmem y hy)).comp y (hasDerivAt_neg y)
          convert h1 using 1 <;> first | rfl | ring)
        (by simpa using hg0)
        (fun y hy => by
          have := hb (-y) (hmem y hy)
          rw [abs_neg, abs_of_nonneg hy.1] at this
          rwa [abs_neg])
      simp only [neg_neg] at key
      rwa [abs_of_nonpos hx0]

end BiluLinial.Tight
