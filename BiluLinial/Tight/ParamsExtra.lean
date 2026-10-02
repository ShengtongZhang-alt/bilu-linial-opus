/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.Params

/-!
# Further consequences of the parameter regime

Blueprint nodes `D-params-*` added after the skeleton (`Tight/Params.lean` holds the first batch).
-/

@[expose] public section

namespace BiluLinial.Tight

variable {d p : ℕ}

/-- `q ≥ 10⁶ - 1`. -/
theorem TRegime.qOf_ge (hR : TRegime d p) : (10 : ℝ) ^ 6 - 1 ≤ qOf d := by
  have h := hR.ten_pow_six_le_d
  rw [qOf]
  linarith

/-- `η₀ ≤ 1/50`, from `q η₀² = Δ (1 - η₀) ≤ Δ ≤ 2`. -/
theorem TRegime.η0Of_le (hR : TRegime d p) : η0Of d p ≤ 1 / 50 := by
  have hq := hR.qOf_ge
  have he := hR.η0Of_eq
  have h1 := hR.η0Of_lt_one
  have hΔ := hR.ΔOf_le_two
  have hΔ0 := hR.ΔOf_pos
  by_contra h
  rw [not_le] at h
  have e1 : ((10 : ℝ) ^ 6 - 1) * η0Of d p ^ 2 ≤ qOf d * η0Of d p ^ 2 :=
    mul_le_mul_of_nonneg_right hq (sq_nonneg _)
  have e2 : (1 / 50 : ℝ) ^ 2 < η0Of d p ^ 2 := pow_lt_pow_left₀ h (by norm_num) two_ne_zero
  have e3 : ΔOf p * (1 - η0Of d p) ≤ 2 := by nlinarith [hR.η0Of_pos]
  nlinarith

/-- `r = 1 + η₀/2 ≤ 1.01` (the source's "for sufficiently large `d`" in the floor lemma). -/
theorem TRegime.rOf_le (hR : TRegime d p) : rOf d p ≤ 101 / 100 := by
  have h := hR.η0Of_le
  rw [rOf]
  linarith

/-- `κ = a² s² = τ_*/(1 - τ_*)²`. -/
theorem TRegime.kappa_eq (hR : TRegime d p) :
    aOf d p ^ 2 * sOf d p ^ 2 = τsOf d p / (1 - τsOf d p) ^ 2 := by
  have hx : 0 ≤ aOf d p ^ 2 * sOf d p * sOf d p :=
    mul_nonneg (mul_nonneg (sq_nonneg _) hR.sOf_pos.le) hR.sOf_pos.le
  have key : cRoot (aOf d p ^ 2 * sOf d p * sOf d p) *
      (1 + cRoot (aOf d p ^ 2 * sOf d p * sOf d p)) = aOf d p ^ 2 * sOf d p * sOf d p := by
    have h := Real.sq_sqrt (show 0 ≤ 1 + 4 * (aOf d p ^ 2 * sOf d p * sOf d p) by linarith)
    rw [cRoot]
    linear_combination h / 4
  rw [hR.cRoot_const] at key
  have hτ1 : 0 < 1 - τsOf d p := sub_pos.mpr hR.τsOf_lt_one
  rw [sq (sOf d p), ← mul_assoc, ← key]
  field_simp
  ring

/-- `τ_* ≤ 10⁻⁵`. -/
theorem TRegime.τsOf_le (hR : TRegime d p) : τsOf d p ≤ 1 / 100000 := by
  have hq := hR.qOf_ge
  have hqt := hR.qOf_mul_τsOf
  have ht0 := hR.τsOf_pos
  have h0 := hR.η0Of_pos
  nlinarith [mul_le_mul_of_nonneg_right hq ht0.le]

/-- `d κ ≤ 1.01` for `κ = a² s² = τ_*/(1-τ_*)²` (floor lemma). Since `τ_* ≤ 1/q`,
`d κ ≤ (q+1) q/(q-1)²`, which is `≤ 1.01` once `q ≥ 400`. -/
theorem TRegime.d_mul_kappa_le (hR : TRegime d p) :
    (d : ℝ) * (aOf d p ^ 2 * sOf d p ^ 2) ≤ 101 / 100 := by
  have hd : (d : ℝ) = qOf d + 1 := by rw [qOf]; ring
  have hqt := hR.qOf_mul_τsOf
  have ht0 := hR.τsOf_pos
  have ht := hR.τsOf_le
  have h0 := hR.η0Of_pos
  have hτ1 : 0 < 1 - τsOf d p := sub_pos.mpr hR.τsOf_lt_one
  rw [hR.kappa_eq, hd, mul_div_assoc', div_le_iff₀ (by positivity)]
  nlinarith [sq_nonneg (τsOf d p)]

/-- `κ = a² s² ≤ 1/100`, so every edge weight `c_ij ≤ κ` is at most `.01` (floor lemma). -/
theorem TRegime.kappa_le (hR : TRegime d p) : aOf d p ^ 2 * sOf d p ^ 2 ≤ 1 / 100 := by
  have h1 := hR.d_mul_kappa_le
  have h2 := hR.ten_pow_six_le_d
  have h3 : 0 ≤ aOf d p ^ 2 * sOf d p ^ 2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  nlinarith [mul_le_mul_of_nonneg_right h2 h3]

end BiluLinial.Tight
