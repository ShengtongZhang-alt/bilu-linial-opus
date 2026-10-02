/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Counterexample.JoinGreen

/-!
# The amplification inequality

Blueprint node `B-step4` (source Step 4, Xu Lemma 3.3). For `Z = join q Y` with all copies and
`Z` itself positive definite for both signs:
`t(Z) ≥ 1 / (2 - (1/q) ∑ᵢ t(Y_i))`, the denominator being positive. Proof:
`g_±(Z) = 1/p_±` and `1/p₊ + 1/p₋ ≥ 4/(p₊ + p₋)` with `p₊ + p₋ = 2r - ∑ᵢ s(Y_i) > 0`.
-/

@[expose] public section

namespace BiluLinial.Counterexample

open Matrix

/-- The scalar inequality behind Step 4: with `p₊ = 2s - S₊ > 0`, `p₋ = 2s - S₋ > 0` and
`q = s²`, `2 - (s/2)(S₊ + S₋)/q = (p₊ + p₋)/(2s) > 0` and its reciprocal is at most
`(s/2)(1/p₊ + 1/p₋)`. -/
private theorem step4_scalar {s q Sm Sp : ℝ} (hs : 0 < s) (hsq : s ^ 2 = q)
    (pm : 0 < 2 * s - Sm) (pp : 0 < 2 * s - Sp) :
    0 < 2 - s / 2 * (Sm + Sp) / q ∧
      1 / (2 - s / 2 * (Sm + Sp) / q) ≤ s / 2 * (1 / (2 * s - Sm) + 1 / (2 * s - Sp)) := by
  subst hsq
  obtain ⟨a, rfl⟩ : ∃ a, Sm = 2 * s - a := ⟨2 * s - Sm, by ring⟩
  obtain ⟨b, rfl⟩ : ∃ b, Sp = 2 * s - b := ⟨2 * s - Sp, by ring⟩
  simp only [sub_sub_cancel] at pm pp ⊢
  have hs0 : s ≠ 0 := hs.ne'
  have key : 2 - s / 2 * (2 * s - a + (2 * s - b)) / s ^ 2 = (a + b) / (2 * s) := by
    field_simp
    ring
  rw [key]
  refine ⟨by positivity, ?_⟩
  have h4 : 4 / (a + b) ≤ 1 / a + 1 / b := by
    rw [div_add_div _ _ pm.ne' pp.ne', div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg (a - b)]
  calc 1 / ((a + b) / (2 * s)) = s / 2 * (4 / (a + b)) := by
        field_simp
        ring
    _ ≤ s / 2 * (1 / a + 1 / b) := mul_le_mul_of_nonneg_left h4 (by positivity)

theorem join_tval_ge (n : ℕ) (Y : RGraph)
    {A : Matrix (join (n + 2) Y).V (join (n + 2) Y).V ℝ} (hA : IsSignedAdj (join (n + 2) Y).G A)
    (hY : ∀ i, (rad n • (1 : Matrix Y.V Y.V ℝ) - copyBlock Y A i).PosDef ∧
      (rad n • (1 : Matrix Y.V Y.V ℝ) + copyBlock Y A i).PosDef)
    (hZ : (rad n • (1 : Matrix (join (n + 2) Y).V (join (n + 2) Y).V ℝ) - A).PosDef ∧
      (rad n • (1 : Matrix (join (n + 2) Y).V (join (n + 2) Y).V ℝ) + A).PosDef) :
    0 < 2 - (∑ i, tval n (copyBlock Y A i) Y.root) / (n + 2) ∧
      1 / (2 - (∑ i, tval n (copyBlock Y A i) Y.root) / (n + 2)) ≤
        tval n A (join (n + 2) Y).root := by
  have hq : (0 : ℝ) < n + 2 := by positivity
  have hs : 0 < Real.sqrt (n + 2) := Real.sqrt_pos.2 hq
  have hsq : Real.sqrt (n + 2) ^ 2 = n + 2 := Real.sq_sqrt hq.le
  have hYm : ∀ i, (rad n • (1 : Matrix Y.V Y.V ℝ) - copyBlock Y A i).PosDef := fun i => (hY i).1
  have hYp : ∀ i, (rad n • (1 : Matrix Y.V Y.V ℝ) -
      copyBlock Y (-A : Matrix (join (n + 2) Y).V (join (n + 2) Y).V ℝ) i).PosDef := fun i => by
    have h : copyBlock Y (-A : Matrix (join (n + 2) Y).V (join (n + 2) Y).V ℝ) i =
        -copyBlock Y A i := rfl
    rw [h, sub_neg_eq_add]
    exact (hY i).2
  have hZp : (rad n • (1 : Matrix (join (n + 2) Y).V (join (n + 2) Y).V ℝ) - -A).PosDef := by
    rw [sub_neg_eq_add]
    exact hZ.2
  have gm := join_green_eq hA hYm hZ.1
  have gp := join_green_eq hA.neg hYp hZp
  have pm := (join_posDef_iff hA hYm).1 hZ.1
  have pp := (join_posDef_iff hA.neg hYp).1 hZp
  have hsum : ∑ i, tval n (copyBlock Y A i) Y.root = Real.sqrt (n + 2) / 2 *
      (∑ i, green (rad n) (copyBlock Y A i) Y.root +
        ∑ i, green (rad n)
          (copyBlock Y (-A : Matrix (join (n + 2) Y).V (join (n + 2) Y).V ℝ) i) Y.root) := by
    simp only [tval, ← Finset.mul_sum, Finset.sum_add_distrib]
    rfl
  have htv : tval n A (join (n + 2) Y).root = Real.sqrt (n + 2) / 2 *
      (1 / (rad n - ∑ i, green (rad n) (copyBlock Y A i) Y.root) +
        1 / (rad n - ∑ i, green (rad n)
          (copyBlock Y (-A : Matrix (join (n + 2) Y).V (join (n + 2) Y).V ℝ) i) Y.root)) := by
    rw [tval, gm, gp]
  have hr : rad n = 2 * Real.sqrt (n + 2) := rfl
  rw [hsum, htv]
  rw [hr] at pm pp ⊢
  exact step4_scalar hs hsq pm pp

end BiluLinial.Counterexample
