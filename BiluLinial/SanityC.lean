/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Sanity
public import BiluLinial.SecondOrder.Explicit.Root

/-!
# Sanity checks for `explicit_excess` (Part C2)

* `explicit_excess`: the excess `1 / (25 q⁵ √q)` is `q^{-11/2}/25` and is positive, so the
  threshold is strictly above the Ramanujan value `2√q`; the equation of Section 6 has a unique
  positive root `z_q`, it satisfies `z_q < 1/q`, and `R_q = z_q^{-1/2} + q z_q^{1/2} > 2√q`; and the
  hypotheses (finite, connected, `d`-regular) are satisfiable for every `d`
  (`complete_graph_connected_regular` in `Sanity.lean`).
-/

@[expose] public section

namespace BiluLinial

theorem excess_eq_rpow {q : ℝ} (hq : 0 < q) :
    1 / (25 * q ^ 5 * Real.sqrt q) = q ^ (-(11 : ℝ) / 2) / 25 := by
  have h : q ^ (-(11 : ℝ) / 2) = (q ^ (5 : ℝ) * q ^ ((1 : ℝ) / 2))⁻¹ := by
    rw [← Real.rpow_add hq, ← Real.rpow_neg hq.le]
    norm_num
  rw [h, Real.sqrt_eq_rpow, show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  field_simp

theorem explicit_excess_threshold_gt (d : ℕ) (hd : 4 ≤ d) :
    2 * Real.sqrt ((d : ℝ) - 1) <
      2 * Real.sqrt ((d : ℝ) - 1) + 1 / (25 * ((d : ℝ) - 1) ^ 5 * Real.sqrt ((d : ℝ) - 1)) := by
  have hq : (0 : ℝ) < (d : ℝ) - 1 := by
    have : (4 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have := Real.sqrt_pos.2 hq
  have : 0 < 1 / (25 * ((d : ℝ) - 1) ^ 5 * Real.sqrt ((d : ℝ) - 1)) := by positivity
  linarith

/-- The root `z_q` of Section 6 (eq. (6.1)) exists, is the unique positive root, satisfies
`z_q < 1/q`, and `R_q = z_q^{-1/2} + q z_q^{1/2} > 2√q`. -/
theorem explicit_root_facts (d : ℕ) (hd : 4 ≤ d) :
    (∃! z : ℝ, 0 < z ∧
      ((d : ℝ) - 1) * z * (1 + z + z ^ 2 + 2 * z ^ 3) = 1 + z + z ^ 2 + 4 * z ^ 4) ∧
    ∀ z : ℝ, 0 < z →
      ((d : ℝ) - 1) * z * (1 + z + z ^ 2 + 2 * z ^ 3) = 1 + z + z ^ 2 + 4 * z ^ 4 →
        z < 1 / ((d : ℝ) - 1) ∧
          2 * Real.sqrt ((d : ℝ) - 1) < 1 / Real.sqrt z + ((d : ℝ) - 1) * Real.sqrt z :=
  SecondOrder.Explicit.explicit_excess_root_proof d hd

end BiluLinial
