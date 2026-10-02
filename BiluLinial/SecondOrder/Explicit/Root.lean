/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import Mathlib

/-!
# The root of the explicit excess equation

Blueprint node `C2-root` (source Section 6, eq. (6.1)). For real `q ≥ 3` let
`F_q(z) = q z (1 + z + z² + 2z³) - (1 + z + z² + 4z⁴)
       = -1 + (q-1) z + (q-1) z² + q z³ + (2q-4) z⁴`.
Every coefficient of a positive power of `z` is nonnegative and `q - 1 > 0`, so `F_q` is strictly
increasing on `[0, ∞)`; `F_q(0) = -1` and `F_q(1/q) = (2q-4)/q⁴ > 0`. Hence `F_q` has exactly
one positive root `z`, and `z < 1/q`. Since `q z < 1`,
`1/√z + q√z - 2√q = (1 - √q √z)² / √z > 0`.
-/

@[expose] public section

namespace BiluLinial.SecondOrder.Explicit

/-- `F_q(z) = q z (1 + z + z² + 2z³) - (1 + z + z² + 4z⁴)`. -/
theorem rootPoly_eq (q z : ℝ) : q * z * (1 + z + z ^ 2 + 2 * z ^ 3) - (1 + z + z ^ 2 + 4 * z ^ 4) =
    -1 + (q - 1) * z + (q - 1) * z ^ 2 + q * z ^ 3 + (2 * q - 4) * z ^ 4 := by
  ring

theorem rootPoly_strictMonoOn {q : ℝ} (hq : 3 ≤ q) :
    StrictMonoOn (fun z : ℝ => q * z * (1 + z + z ^ 2 + 2 * z ^ 3) - (1 + z + z ^ 2 + 4 * z ^ 4))
      (Set.Ici 0) := by
  intro a ha b _ hab
  rw [Set.mem_Ici] at ha
  dsimp only
  rw [rootPoly_eq, rootPoly_eq]
  have e1 : (q - 1) * a < (q - 1) * b := mul_lt_mul_of_pos_left hab (by linarith)
  have e2 : (q - 1) * a ^ 2 ≤ (q - 1) * b ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha hab.le 2) (by linarith)
  have e3 : q * a ^ 3 ≤ q * b ^ 3 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha hab.le 3) (by linarith)
  have e4 : (2 * q - 4) * a ^ 4 ≤ (2 * q - 4) * b ^ 4 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha hab.le 4) (by linarith)
  linarith

/-- `F_q(1/q) = 2q⁻³ - 4q⁻⁴ > 0`. -/
theorem rootPoly_inv_pos {q : ℝ} (hq : 3 ≤ q) :
    0 < q * (1 / q) * (1 + 1 / q + (1 / q) ^ 2 + 2 * (1 / q) ^ 3) -
      (1 + 1 / q + (1 / q) ^ 2 + 4 * (1 / q) ^ 4) := by
  have hq0 : 0 < q := by linarith
  have hqw : q * (1 / q) = 1 := by field_simp
  have hw0 : 0 < 1 / q := by positivity
  have hw3 : 1 / q ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) hq
  rw [hqw, one_mul]
  have key : (1 + 1 / q + (1 / q) ^ 2 + 2 * (1 / q) ^ 3) -
      (1 + 1 / q + (1 / q) ^ 2 + 4 * (1 / q) ^ 4) = 2 * (1 / q) ^ 3 * (1 - 2 * (1 / q)) := by
    ring
  rw [key]
  exact mul_pos (by positivity) (by linarith)

theorem root_lt_inv {q z : ℝ} (hq : 3 ≤ q) (hz : 0 < z)
    (h : q * z * (1 + z + z ^ 2 + 2 * z ^ 3) = 1 + z + z ^ 2 + 4 * z ^ 4) : z < 1 / q := by
  by_contra hcon
  have hq0 : 0 < q := by linarith
  have hmono := (rootPoly_strictMonoOn hq).monotoneOn
    (Set.mem_Ici.mpr (by positivity : (0 : ℝ) ≤ 1 / q)) (Set.mem_Ici.mpr hz.le) (not_lt.mp hcon)
  have hpos := rootPoly_inv_pos hq
  linarith

theorem root_unique {q y z : ℝ} (hq : 3 ≤ q) (hy : 0 < y) (hz : 0 < z)
    (hFy : q * y * (1 + y + y ^ 2 + 2 * y ^ 3) = 1 + y + y ^ 2 + 4 * y ^ 4)
    (hFz : q * z * (1 + z + z ^ 2 + 2 * z ^ 3) = 1 + z + z ^ 2 + 4 * z ^ 4) : y = z := by
  apply (rootPoly_strictMonoOn hq).injOn (Set.mem_Ici.mpr hy.le) (Set.mem_Ici.mpr hz.le)
  dsimp only
  linarith

theorem exists_root {q : ℝ} (hq : 3 ≤ q) :
    ∃ z : ℝ, 0 < z ∧ z < 1 / q ∧ q * z * (1 + z + z ^ 2 + 2 * z ^ 3) = 1 + z + z ^ 2 + 4 * z ^ 4 := by
  have hq0 : 0 < q := by linarith
  obtain ⟨c, ⟨hc0, _⟩, hc⟩ := intermediate_value_Icc
    (f := fun z : ℝ => q * z * (1 + z + z ^ 2 + 2 * z ^ 3) - (1 + z + z ^ 2 + 4 * z ^ 4))
    (a := 0) (b := 1 / q) (by positivity) (by fun_prop)
    (show (0 : ℝ) ∈ Set.Icc _ _ from ⟨by norm_num, (rootPoly_inv_pos hq).le⟩)
  dsimp only at hc
  have hFc : q * c * (1 + c + c ^ 2 + 2 * c ^ 3) = 1 + c + c ^ 2 + 4 * c ^ 4 := sub_eq_zero.mp hc
  have hcpos : 0 < c := by
    rcases eq_or_lt_of_le hc0 with h | h
    · subst h
      norm_num at hc
    · exact h
  exact ⟨c, hcpos, root_lt_inv hq hcpos hFc, hFc⟩

/-- For `q, z > 0` with `q z < 1`: `2√q < 1/√z + q√z`. -/
theorem excess_pos {q z : ℝ} (hq : 0 < q) (hz : 0 < z) (hqz : q * z < 1) :
    2 * Real.sqrt q < 1 / Real.sqrt z + q * Real.sqrt z := by
  have hs : 0 < Real.sqrt z := Real.sqrt_pos.mpr hz
  have ht : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq
  have hs2 : Real.sqrt z ^ 2 = z := Real.sq_sqrt hz.le
  have ht2 : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq.le
  have hts : Real.sqrt q * Real.sqrt z < 1 := by
    have h2 : (Real.sqrt q * Real.sqrt z) ^ 2 < 1 := by rw [mul_pow, hs2, ht2]; exact hqz
    nlinarith [mul_pos ht hs]
  have hsne : Real.sqrt z ≠ 0 := hs.ne'
  have key : 1 / Real.sqrt z + q * Real.sqrt z - 2 * Real.sqrt q =
      (1 - Real.sqrt q * Real.sqrt z) ^ 2 / Real.sqrt z := by
    have hq' : q * Real.sqrt z = Real.sqrt q ^ 2 * Real.sqrt z := by rw [ht2]
    rw [hq']
    field_simp
    ring
  have : 0 < (1 - Real.sqrt q * Real.sqrt z) ^ 2 / Real.sqrt z :=
    div_pos (pow_pos (by linarith) 2) hs
  linarith

theorem explicit_excess_root_proof (d : ℕ) (hd : 4 ≤ d) :
    (∃! z : ℝ, 0 < z ∧
      ((d : ℝ) - 1) * z * (1 + z + z ^ 2 + 2 * z ^ 3) = 1 + z + z ^ 2 + 4 * z ^ 4) ∧
    ∀ z : ℝ, 0 < z →
      ((d : ℝ) - 1) * z * (1 + z + z ^ 2 + 2 * z ^ 3) = 1 + z + z ^ 2 + 4 * z ^ 4 →
        z < 1 / ((d : ℝ) - 1) ∧
          2 * Real.sqrt ((d : ℝ) - 1) < 1 / Real.sqrt z + ((d : ℝ) - 1) * Real.sqrt z := by
  have hq : (3 : ℝ) ≤ (d : ℝ) - 1 := by
    have : (4 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hq0 : (0 : ℝ) < (d : ℝ) - 1 := by linarith
  refine ⟨?_, ?_⟩
  · obtain ⟨z, hz0, -, hz⟩ := exists_root hq
    exact ⟨z, ⟨hz0, hz⟩, fun y ⟨hy0, hy⟩ => root_unique hq hy0 hz0 hy hz⟩
  · intro z hz0 hz
    have hlt := root_lt_inv hq hz0 hz
    refine ⟨hlt, excess_pos hq0 hz0 ?_⟩
    have := (lt_div_iff₀ hq0).mp hlt
    linarith

end BiluLinial.SecondOrder.Explicit
