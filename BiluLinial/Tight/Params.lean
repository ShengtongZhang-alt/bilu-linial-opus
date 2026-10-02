/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.Defs

/-!
# The parameter regime of the near-Ramanujan upper bound

Blueprint nodes `D-params-*`. The source takes `p = ⌊c₀ d^{2/17}⌋` for an absolute `c₀ ∈ (0, 1]`
and `d` sufficiently large. The constant `c₀` is chosen by the contact exclusion
(`exists_contact_free`, after the absolute constants of the analytic lemmas; AUDIT-D, gap G3), so
it is not fixed here. The structural nodes use only the regime `TRegime d p`: `p ≥ 10⁶` and
`p ≤ d^{2/17}`. For every `c₀ ∈ (0, 1]`, `p = ⌊c₀ d^{2/17}⌋` is in the regime for large `d`
(`exists_tRegime_pAt`).
-/

@[expose] public section

namespace BiluLinial.Tight

/-- `p = ⌊c₀ d^{2/17}⌋`. -/
noncomputable def pAt (c₀ : ℝ) (d : ℕ) : ℕ := ⌊c₀ * (d : ℝ) ^ ((2 : ℝ) / 17)⌋₊

/-- The parameter regime of the structural nodes: `p ≥ 10⁶` and `p^17 ≤ d²`. -/
structure TRegime (d p : ℕ) : Prop where
  hp : 10 ^ 6 ≤ p
  hpd : p ^ 17 ≤ d ^ 2

variable {d p : ℕ}

/-- `d ≥ 10⁶` in the regime (indeed `d ≥ p^{17/2} ≥ 10⁵¹`). -/
theorem TRegime.ten_pow_six_le_nat (hR : TRegime d p) : 10 ^ 6 ≤ d := by
  by_contra h
  have h1 : (10 ^ 6) ^ 17 ≤ p ^ 17 := Nat.pow_le_pow_left hR.hp 17
  have h2 : d ^ 2 < (10 ^ 6) ^ 2 := Nat.pow_lt_pow_left (not_le.mp h) (by norm_num)
  have h3 : (10 ^ 6) ^ 17 < (10 ^ 6) ^ 2 := lt_of_le_of_lt (h1.trans hR.hpd) h2
  norm_num at h3

theorem TRegime.ten_pow_six_le_d (hR : TRegime d p) : (10 : ℝ) ^ 6 ≤ d := by
  exact_mod_cast hR.ten_pow_six_le_nat

theorem TRegime.two_le_p (hR : TRegime d p) : 2 ≤ p :=
  le_trans (by norm_num) hR.hp

/-- `q = d - 1 ≥ 1`. -/
theorem TRegime.one_le_qOf (hR : TRegime d p) : 1 ≤ qOf d := by
  have h := hR.ten_pow_six_le_d
  rw [qOf]
  linarith

theorem TRegime.qOf_pos (hR : TRegime d p) : 0 < qOf d :=
  lt_of_lt_of_le one_pos hR.one_le_qOf

/-- `Δ = 4/p > 0`. -/
theorem TRegime.ΔOf_pos (hR : TRegime d p) : 0 < ΔOf p := by
  have h : (2 : ℝ) ≤ p := by exact_mod_cast hR.two_le_p
  rw [ΔOf]
  exact div_pos (by norm_num) (by linarith)

/-- `Δ = 4/p ≤ 2`. -/
theorem TRegime.ΔOf_le_two (hR : TRegime d p) : ΔOf p ≤ 2 := by
  have h : (2 : ℝ) ≤ p := by exact_mod_cast hR.two_le_p
  rw [ΔOf, div_le_iff₀ (by linarith)]
  linarith

theorem TRegime.RsqOf_pos (hR : TRegime d p) : 0 < RsqOf d p := by
  have hq := hR.qOf_pos
  have hΔ := hR.ΔOf_pos
  rw [RsqOf]
  linarith

theorem TRegime.aOf_pos (hR : TRegime d p) : 0 < aOf d p := by
  rw [aOf]
  exact div_pos one_pos (Real.sqrt_pos.mpr hR.RsqOf_pos)

/-- `a² = 1/R²`. -/
theorem TRegime.aOf_sq (hR : TRegime d p) : aOf d p ^ 2 = 1 / RsqOf d p := by
  rw [aOf, div_pow, one_pow, Real.sq_sqrt hR.RsqOf_pos.le]

/-- `2 q η₀ = √(Δ² + 4qΔ) - Δ`. -/
theorem TRegime.two_mul_qOf_mul_η0Of (hR : TRegime d p) :
    2 * qOf d * η0Of d p = Real.sqrt (ΔOf p ^ 2 + 4 * qOf d * ΔOf p) - ΔOf p := by
  have hq := hR.qOf_pos.ne'
  rw [η0Of]
  field_simp

theorem TRegime.η0Of_pos (hR : TRegime d p) : 0 < η0Of d p := by
  have hq := hR.qOf_pos
  have hΔ := hR.ΔOf_pos
  have h : ΔOf p < Real.sqrt (ΔOf p ^ 2 + 4 * qOf d * ΔOf p) :=
    (Real.lt_sqrt hΔ.le).mpr (by nlinarith [mul_pos hq hΔ])
  rw [η0Of]
  exact div_pos (sub_pos.mpr h) (by linarith)

theorem TRegime.η0Of_lt_one (hR : TRegime d p) : η0Of d p < 1 := by
  have hq := hR.qOf_pos
  have hΔ := hR.ΔOf_pos
  have h : Real.sqrt (ΔOf p ^ 2 + 4 * qOf d * ΔOf p) < 2 * qOf d + ΔOf p :=
    (Real.sqrt_lt' (by linarith)).mpr (by nlinarith [mul_pos hq hq])
  rw [η0Of, div_lt_one (by linarith)]
  linarith

/-- `q η₀² = Δ (1 - η₀)`. -/
theorem TRegime.η0Of_eq (hR : TRegime d p) :
    qOf d * η0Of d p ^ 2 = ΔOf p * (1 - η0Of d p) := by
  have hq := hR.qOf_pos
  have hΔ := hR.ΔOf_pos
  have hS := Real.sq_sqrt (show 0 ≤ ΔOf p ^ 2 + 4 * qOf d * ΔOf p by
    nlinarith [mul_pos hq hΔ])
  have h2 := hR.two_mul_qOf_mul_η0Of
  have hS' : Real.sqrt (ΔOf p ^ 2 + 4 * qOf d * ΔOf p) = 2 * qOf d * η0Of d p + ΔOf p := by
    linarith
  rw [hS'] at hS
  have h4 : (4 * qOf d) * (qOf d * η0Of d p ^ 2) = (4 * qOf d) * (ΔOf p * (1 - η0Of d p)) := by
    linear_combination hS
  exact mul_left_cancel₀ (by linarith : (0 : ℝ) < 4 * qOf d).ne' h4

theorem TRegime.τsOf_pos (hR : TRegime d p) : 0 < τsOf d p := by
  have h := hR.η0Of_lt_one
  rw [τsOf]
  exact div_pos (by linarith) hR.qOf_pos

theorem TRegime.τsOf_lt_one (hR : TRegime d p) : τsOf d p < 1 := by
  have h := hR.η0Of_pos
  have hq := hR.one_le_qOf
  rw [τsOf, div_lt_one hR.qOf_pos]
  linarith

/-- `q τ_* = 1 - η₀`. -/
theorem TRegime.qOf_mul_τsOf (hR : TRegime d p) : qOf d * τsOf d p = 1 - η0Of d p := by
  have hq := hR.qOf_pos.ne'
  rw [τsOf]
  field_simp

/-- `1 + q τ_* = 2 - η₀`. -/
theorem TRegime.one_add_qOf_mul_τsOf (hR : TRegime d p) :
    1 + qOf d * τsOf d p = 2 - η0Of d p := by
  rw [hR.qOf_mul_τsOf]
  ring

theorem TRegime.sOf_pos (hR : TRegime d p) : 0 < sOf d p := by
  have h1 := hR.η0Of_lt_one
  have h2 := hR.τsOf_lt_one
  rw [sOf, hR.one_add_qOf_mul_τsOf]
  exact div_pos (by linarith) (by linarith)

theorem TRegime.one_lt_rOf (hR : TRegime d p) : 1 < rOf d p := by
  have h := hR.η0Of_pos
  rw [rOf]
  linarith

/-- `c(x)` inverts `c ↦ c (1 + c)` on `c ≥ 0`. -/
theorem cRoot_mul_one_add {c : ℝ} (hc : 0 ≤ c) : cRoot (c * (1 + c)) = c := by
  rw [cRoot, show 1 + 4 * (c * (1 + c)) = (1 + 2 * c) ^ 2 by ring,
    Real.sqrt_sq (by linarith)]
  ring

/-- At the constant sources `y = s`, `c(a² s²) = τ_*/(1 - τ_*)`, i.e. `τ = τ_*` on every edge
(this is `R² = (1 + q τ_*)²/τ_*`, equivalently `R² = q (2 - η₀)²/(1 - η₀) = 4q + Δ`). -/
theorem TRegime.cRoot_const (hR : TRegime d p) :
    cRoot (aOf d p ^ 2 * sOf d p * sOf d p) = τsOf d p / (1 - τsOf d p) := by
  have hq := hR.qOf_pos
  have hR2 := hR.RsqOf_pos
  have hτ0 := hR.τsOf_pos
  have hτ1 : 0 < 1 - τsOf d p := sub_pos.mpr hR.τsOf_lt_one
  have key : (2 - η0Of d p) ^ 2 = τsOf d p * RsqOf d p := by
    refine mul_left_cancel₀ hq.ne' ?_
    rw [RsqOf]
    linear_combination hR.η0Of_eq - (4 * qOf d + ΔOf p) * hR.qOf_mul_τsOf
  have hs : sOf d p = (2 - η0Of d p) / (1 - τsOf d p) := by
    rw [sOf, hR.one_add_qOf_mul_τsOf]
  have hx : aOf d p ^ 2 * sOf d p * sOf d p =
      τsOf d p / (1 - τsOf d p) * (1 + τsOf d p / (1 - τsOf d p)) := by
    rw [hR.aOf_sq, hs]
    calc 1 / RsqOf d p * ((2 - η0Of d p) / (1 - τsOf d p)) * ((2 - η0Of d p) / (1 - τsOf d p))
        = (2 - η0Of d p) ^ 2 / (RsqOf d p * (1 - τsOf d p) ^ 2) := by
          field_simp
      _ = τsOf d p / (1 - τsOf d p) * (1 + τsOf d p / (1 - τsOf d p)) := by
          rw [key]
          field_simp
          ring
  rw [hx, cRoot_mul_one_add (div_nonneg hτ0.le hτ1.le)]

/-! ### The regime at `p = ⌊c₀ d^{2/17}⌋` -/

theorem rpow_two_div_seventeen_pow (d : ℕ) :
    ((d : ℝ) ^ ((2 : ℝ) / 17)) ^ 17 = (d : ℝ) ^ 2 := by
  rw [← Real.rpow_natCast ((d : ℝ) ^ ((2 : ℝ) / 17)) 17, ← Real.rpow_mul (Nat.cast_nonneg d)]
  norm_num

theorem exists_base_ge {c₀ : ℝ} (hc0 : 0 < c₀) (B : ℝ) :
    ∃ D : ℕ, ∀ d : ℕ, D ≤ d → B ≤ c₀ * (d : ℝ) ^ ((2 : ℝ) / 17) := by
  have ht : Filter.Tendsto (fun d : ℕ => c₀ * (d : ℝ) ^ ((2 : ℝ) / 17))
      Filter.atTop Filter.atTop :=
    ((tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop).const_mul_atTop hc0
  exact Filter.eventually_atTop.mp (ht.eventually_ge_atTop B)

/-- `⌊x⌋ ≥ x/2` for `x ≥ 1`, at `x = c₀ d^{2/17}`. -/
theorem half_base_le_pAt {c₀ : ℝ} {d : ℕ} (hb : 1 ≤ c₀ * (d : ℝ) ^ ((2 : ℝ) / 17)) :
    c₀ * (d : ℝ) ^ ((2 : ℝ) / 17) / 2 ≤ pAt c₀ d := by
  rw [pAt]
  have h1 := Nat.sub_one_lt_floor (c₀ * (d : ℝ) ^ ((2 : ℝ) / 17))
  have h2 : (1 : ℝ) ≤ ⌊c₀ * (d : ℝ) ^ ((2 : ℝ) / 17)⌋₊ := by
    exact_mod_cast (Nat.one_le_floor_iff _).mpr hb
  linarith

theorem pAt_le {c₀ : ℝ} (hc0 : 0 ≤ c₀) (hc1 : c₀ ≤ 1) (d : ℕ) :
    (pAt c₀ d : ℝ) ≤ (d : ℝ) ^ ((2 : ℝ) / 17) := by
  have ht0 : 0 ≤ (d : ℝ) ^ ((2 : ℝ) / 17) := Real.rpow_nonneg (Nat.cast_nonneg d) _
  calc (pAt c₀ d : ℝ) ≤ c₀ * (d : ℝ) ^ ((2 : ℝ) / 17) := Nat.floor_le (mul_nonneg hc0 ht0)
    _ ≤ (d : ℝ) ^ ((2 : ℝ) / 17) := by nlinarith

/-- For `c₀ ∈ (0, 1]`, `p = ⌊c₀ d^{2/17}⌋` is in the regime once `d` is large. -/
theorem exists_tRegime_pAt {c₀ : ℝ} (hc0 : 0 < c₀) (hc1 : c₀ ≤ 1) :
    ∃ D : ℕ, ∀ d : ℕ, D ≤ d → TRegime d (pAt c₀ d) ∧ 1 ≤ c₀ * (d : ℝ) ^ ((2 : ℝ) / 17) := by
  obtain ⟨D, hD⟩ := exists_base_ge hc0 (2 * 10 ^ 6)
  refine ⟨D, fun d hd => ?_⟩
  have hb := hD d hd
  have hp := half_base_le_pAt (show 1 ≤ c₀ * (d : ℝ) ^ ((2 : ℝ) / 17) by linarith)
  refine ⟨⟨?_, ?_⟩, by linarith⟩
  · have h : ((10 ^ 6 : ℕ) : ℝ) ≤ pAt c₀ d := by push_cast; linarith
    exact_mod_cast h
  · have h1 := pAt_le hc0.le hc1 d
    have h2 : ((pAt c₀ d : ℝ)) ^ 17 ≤ (d : ℝ) ^ 2 := by
      rw [← rpow_two_div_seventeen_pow]
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) h1 17
    exact_mod_cast h2

/-- `R² = 4(d - 1) + 4/p ≤ 4(d - 1) + (8/c₀) d^{-2/17}` at `p = ⌊c₀ d^{2/17}⌋`, once
`c₀ d^{2/17} ≥ 1` (using `⌊x⌋ ≥ x/2` for `x ≥ 1`). -/
theorem RsqOf_pAt_le {c₀ : ℝ} (hc0 : 0 < c₀) {d : ℕ}
    (hb : 1 ≤ c₀ * (d : ℝ) ^ ((2 : ℝ) / 17)) :
    RsqOf d (pAt c₀ d) ≤ 4 * ((d : ℝ) - 1) + 8 / c₀ * (d : ℝ) ^ (-(2 : ℝ) / 17) := by
  have hp := half_base_le_pAt hb
  have ht : (d : ℝ) ^ (-(2 : ℝ) / 17) = ((d : ℝ) ^ ((2 : ℝ) / 17))⁻¹ := by
    rw [neg_div, Real.rpow_neg (Nat.cast_nonneg d)]
  have ht0 : 0 < (d : ℝ) ^ ((2 : ℝ) / 17) :=
    lt_of_mul_lt_mul_left (by linarith : c₀ * 0 < c₀ * (d : ℝ) ^ ((2 : ℝ) / 17)) hc0.le
  have hc0' := hc0.ne'
  have ht0' := ht0.ne'
  have hΔ : ΔOf (pAt c₀ d) ≤ 8 / c₀ * ((d : ℝ) ^ ((2 : ℝ) / 17))⁻¹ := by
    calc ΔOf (pAt c₀ d) = 4 / (pAt c₀ d : ℝ) := rfl
      _ ≤ 4 / (c₀ * (d : ℝ) ^ ((2 : ℝ) / 17) / 2) :=
          div_le_div_of_nonneg_left (by norm_num) (by positivity) hp
      _ = 8 / c₀ * ((d : ℝ) ^ ((2 : ℝ) / 17))⁻¹ := by
          field_simp
          ring
  rw [RsqOf, qOf, ht]
  linarith

end BiluLinial.Tight
