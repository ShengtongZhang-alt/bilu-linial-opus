/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.Contact.Defs
public import BiluLinial.Tight.ParamsExtra

/-!
# Deterministic parameter facts of Section 1.5 (proof of `param_facts`)

`param_facts_pf` is verbatim the statement of `param_facts` (`Tight/Contact/Real.lean`, node
R-param; source (D1)–(D2), l.1336–1349; AUDIT-C R2–R5). Sketch and checks:
`docs/tight/CHECK_CONTACT.md` §R1 (witness `P₀ = 0`). The proofs of the other real leaves
(`Contact/RealPfA.lean`, `Contact/RealPfB.lean`) import this file; `Real.lean` will import all
three and close its leaves by these proofs.

Write `u = η₀` and `Q = q = d - 1`. Then `p Q u² = 4(1 - u)`, `L̄ (Q - 1 + u)² = (Q + 1) Q (1 - u)`
and `s (Q - 1 + u) = (2 - u) Q`, so every fact is a polynomial inequality in `Q, u` under
`0 < u ≤ 1/50`, `Q ≥ 10⁶ - 1`, `Q u ≥ 10` and `Q u² ≤ 4·10⁻⁶`.
-/

@[expose] public section

namespace BiluLinial.Tight

variable {d p : ℕ}

/-! ### Polynomial inequalities in `Q, u` -/

/-- The reserve polynomial `(Q - 1 + u)² - r (Q + 1) Q (1 - u)` is nonnegative once `Q u ≥ 10`. -/
theorem pf_M_nonneg {Q u : ℝ} (hQ : 0 ≤ Q) (hqu : 10 ≤ Q * u) :
    (1 + u / 2) * ((Q + 1) * Q * (1 - u)) ≤ (Q - 1 + u) ^ 2 := by
  nlinarith [mul_nonneg hQ (sub_nonneg.mpr hqu),
    mul_nonneg (mul_nonneg hQ hQ) (sq_nonneg u), sq_nonneg (1 - u), mul_nonneg hQ (sq_nonneg u)]

/-- The drift polynomial (`G = 2(Q+1)(1-u)M + 8(1-u)D² - QuD²`) is nonnegative. -/
theorem pf_G_nonneg {Q u : ℝ} (hQ : 10 ^ 6 - 1 ≤ Q) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 50)
    (hqu2 : Q * u ^ 2 ≤ 4 / 10 ^ 6) :
    0 ≤ -Q ^ 3 * u ^ 3 + Q ^ 2 * (2 + 6 * u - 6 * u ^ 2 - 2 * u ^ 3) +
      Q * (-20 + 36 * u - 12 * u ^ 2 - 4 * u ^ 3) + 10 * (1 - u) ^ 3 := by
  have hQ0 : 0 ≤ Q := by linarith
  have h50 : 0 ≤ 1 / 50 - u := by linarith
  have hQ2u : 0 ≤ Q ^ 2 * u := mul_nonneg (sq_nonneg Q) hu0
  nlinarith [mul_nonneg hQ2u (sub_nonneg.mpr hqu2), mul_nonneg hQ2u h50,
    mul_nonneg (mul_nonneg (sq_nonneg Q) (sq_nonneg u)) h50,
    mul_nonneg hQ0 (sub_nonneg.mpr hQ), mul_nonneg (mul_nonneg hQ0 (sq_nonneg u)) h50,
    mul_nonneg hQ0 hu0, pow_nonneg (by linarith : (0 : ℝ) ≤ 1 - u) 3]

/-- The polynomial behind `r L̄ s² ≤ 4` is nonnegative once `Q u ≥ 10`. -/
theorem pf_H_nonneg {Q u : ℝ} (hQ : 10 ≤ Q) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 50)
    (hqu : 10 ≤ Q * u) :
    (1 + u / 2) * ((Q + 1) * Q * (1 - u) * ((2 - u) * Q) ^ 2) ≤ 4 * ((Q - 1 + u) ^ 2) ^ 2 := by
  have hQ0 : 0 ≤ Q := by linarith
  have h50 : 0 ≤ 1 / 50 - u := by linarith
  have hQ3 : 0 ≤ Q ^ 3 := pow_nonneg hQ0 3
  have hQ4 : 0 ≤ Q ^ 4 := pow_nonneg hQ0 4
  nlinarith [mul_nonneg hQ3 (sub_nonneg.mpr hqu), mul_nonneg (mul_nonneg hQ4 hu0) h50,
    mul_nonneg (mul_nonneg hQ4 (sq_nonneg u)) h50, mul_nonneg (mul_nonneg hQ3 hu0) h50,
    mul_nonneg (mul_nonneg hQ3 (sq_nonneg u)) h50,
    mul_nonneg (mul_nonneg hQ0 (sq_nonneg (1 - u))) (by linarith : (0 : ℝ) ≤ 3 * Q - 2 + 2 * u),
    mul_nonneg hQ4 (pow_nonneg hu0 4), mul_nonneg hQ3 (pow_nonneg hu0 4),
    pow_nonneg (by linarith : (0 : ℝ) ≤ 1 - u) 4, mul_nonneg hQ3 hu0, mul_nonneg hQ4 hu0]

/-- `r L̄ ≤ 1` from the closed form of `L̄`. -/
theorem pf_rL_real {Q u L : ℝ} (hQ : 10 ≤ Q) (hu0 : 0 ≤ u) (hqu : 10 ≤ Q * u)
    (hL : L * (Q - 1 + u) ^ 2 = (Q + 1) * Q * (1 - u)) : (1 + u / 2) * L ≤ 1 := by
  have hD : 0 < Q - 1 + u := by linarith
  refine le_of_mul_le_mul_right ?_ (pow_pos hD 2)
  rw [mul_assoc, hL, one_mul]
  exact pf_M_nonneg (by linarith) hqu

/-- The drift reserve `1/p - 2u ≤ d ε (1 - r L̄)` in closed form (`ip = 1/p`). -/
theorem pf_drift_real {Q u L ip : ℝ} (hQ : 10 ^ 6 - 1 ≤ Q) (hu0 : 0 < u) (hu1 : u ≤ 1 / 50)
    (hqu2 : Q * u ^ 2 ≤ 4 / 10 ^ 6) (hL : L * (Q - 1 + u) ^ 2 = (Q + 1) * Q * (1 - u))
    (hip : ip * (4 * (1 - u)) = Q * u ^ 2) :
    ip - 2 * u ≤ (Q + 1) * (u / 2) * (1 - (1 + u / 2) * L) := by
  have hD : 0 < Q - 1 + u := by linarith
  have h1u : 0 < 1 - u := by linarith
  have hK : 0 < 4 * (1 - u) * (Q - 1 + u) ^ 2 := by positivity
  refine le_of_mul_le_mul_right ?_ hK
  have e1 : (ip - 2 * u) * (4 * (1 - u) * (Q - 1 + u) ^ 2) =
      Q * u ^ 2 * (Q - 1 + u) ^ 2 - 8 * u * (1 - u) * (Q - 1 + u) ^ 2 := by
    linear_combination (Q - 1 + u) ^ 2 * hip
  have e2 : (Q + 1) * (u / 2) * (1 - (1 + u / 2) * L) * (4 * (1 - u) * (Q - 1 + u) ^ 2) =
      2 * (Q + 1) * u * (1 - u) * ((Q - 1 + u) ^ 2 - (1 + u / 2) * ((Q + 1) * Q * (1 - u))) := by
    linear_combination (-(2 * (Q + 1) * u * (1 - u) * (1 + u / 2))) * hL
  rw [e1, e2]
  have hG := pf_G_nonneg hQ hu0.le hu1 hqu2
  nlinarith [mul_nonneg hu0.le hG]

/-- `r L̄ s² ≤ 4` in closed form. -/
theorem pf_rLs_real {Q u L s : ℝ} (hQ : 10 ≤ Q) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 50)
    (hqu : 10 ≤ Q * u) (hL : L * (Q - 1 + u) ^ 2 = (Q + 1) * Q * (1 - u))
    (hs : s * (Q - 1 + u) = (2 - u) * Q) : (1 + u / 2) * L * s ^ 2 ≤ 4 := by
  have hD : 0 < Q - 1 + u := by linarith
  refine le_of_mul_le_mul_right ?_ (pow_pos (pow_pos hD 2) 2)
  have e : (1 + u / 2) * L * s ^ 2 * ((Q - 1 + u) ^ 2) ^ 2 =
      (1 + u / 2) * ((Q + 1) * Q * (1 - u) * ((2 - u) * Q) ^ 2) := by
    rw [← hL, ← hs]; ring
  rw [e]
  exact pf_H_nonneg hQ hu0 hu1 hqu

/-- `L̄ ≥ 1 - u` in closed form. -/
theorem pf_L_ge {Q u L : ℝ} (hQ : 2 ≤ Q) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 50)
    (hL : L * (Q - 1 + u) ^ 2 = (Q + 1) * Q * (1 - u)) : 1 - u ≤ L := by
  have hD : 0 < Q - 1 + u := by linarith
  refine le_of_mul_le_mul_right ?_ (pow_pos hD 2)
  rw [hL]
  have hD2 : (Q - 1 + u) ^ 2 ≤ (Q + 1) * Q := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - u) (by linarith : (0 : ℝ) ≤ 2 * Q - 1 + u)]
  nlinarith [mul_le_mul_of_nonneg_left hD2 (by linarith : (0 : ℝ) ≤ 1 - u)]

/-- `s ≥ 2 - u` in closed form. -/
theorem pf_s_ge {Q u s : ℝ} (hQ : 2 ≤ Q) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 50)
    (hs : s * (Q - 1 + u) = (2 - u) * Q) : 2 - u ≤ s := by
  have hD : 0 < Q - 1 + u := by linarith
  refine le_of_mul_le_mul_right ?_ hD
  rw [hs]
  nlinarith [mul_le_mul_of_nonneg_left (by linarith : Q - 1 + u ≤ Q)
    (by linarith : (0 : ℝ) ≤ 2 - u)]

/-- `s² ≤ 5` in closed form. -/
theorem pf_s_sq_le {Q u s : ℝ} (hQ : 10 ≤ Q) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 50)
    (hs : s * (Q - 1 + u) = (2 - u) * Q) : s ^ 2 ≤ 5 := by
  have hD : 0 < Q - 1 + u := by linarith
  have hs0 : 0 ≤ s := by
    by_contra h
    rw [not_le] at h
    have : s * (Q - 1 + u) < 0 := mul_neg_of_neg_of_pos h hD
    nlinarith
  have h1 : s * (9 / 10 * Q) ≤ 2 * Q := by
    nlinarith [mul_le_mul_of_nonneg_left (by linarith : 9 / 10 * Q ≤ Q - 1 + u) hs0]
  have h2 : s ≤ 20 / 9 := by nlinarith
  nlinarith

/-! ### The regime in terms of `Q, u` -/

/-- `d = q + 1`. -/
theorem pf_d_eq (d : ℕ) : (d : ℝ) = qOf d + 1 := by
  rw [qOf]; ring

/-- `ε = η₀/2`. -/
theorem pf_epsP_eq (d p : ℕ) : epsP d p = η0Of d p / 2 := by
  unfold epsP rOf; ring

/-- `p q η₀² = 4(1 - η₀)`. -/
theorem TRegime.pf_p_mul (hR : TRegime d p) :
    (p : ℝ) * (qOf d * η0Of d p ^ 2) = 4 * (1 - η0Of d p) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast lt_of_lt_of_le (by norm_num) hR.hp
  rw [hR.η0Of_eq, ΔOf, ← mul_assoc, mul_div_cancel₀ _ hp.ne']

/-- `p² ≤ d`, from `p⁴ ≤ p¹⁷ ≤ d²`. -/
theorem TRegime.pf_sq_le_d (hR : TRegime d p) : (p : ℝ) ^ 2 ≤ d := by
  have hp1 : 1 ≤ p := le_trans (by norm_num) hR.hp
  have h1 : (p ^ 2) ^ 2 ≤ d ^ 2 := by
    rw [← pow_mul]
    exact le_trans (Nat.pow_le_pow_right hp1 (by norm_num)) hR.hpd
  exact_mod_cast (Nat.pow_le_pow_iff_left (by norm_num)).mp h1

/-- `q η₀² ≤ 4·10⁻⁶`. -/
theorem TRegime.pf_qu2_le (hR : TRegime d p) : qOf d * η0Of d p ^ 2 ≤ 4 / 10 ^ 6 := by
  have h := hR.pf_p_mul
  have hp : (10 : ℝ) ^ 6 ≤ p := by exact_mod_cast hR.hp
  have hu := hR.η0Of_pos
  have hx : 0 ≤ qOf d * η0Of d p ^ 2 := mul_nonneg hR.qOf_pos.le (sq_nonneg _)
  rw [le_div_iff₀ (by norm_num)]
  nlinarith [mul_le_mul_of_nonneg_left hp hx]

/-- `q η₀ ≥ 10`, from `p (q η₀)² = 4 (1 - η₀) q` and `q ≥ p² - 1`. -/
theorem TRegime.pf_qu_ge (hR : TRegime d p) : 10 ≤ qOf d * η0Of d p := by
  have h := hR.pf_p_mul
  have hp : (10 : ℝ) ^ 6 ≤ p := by exact_mod_cast hR.hp
  have hd := hR.pf_sq_le_d
  have hu := hR.η0Of_le
  have hu0 := hR.η0Of_pos
  have hq0 := hR.qOf_pos
  have hq : (p : ℝ) ^ 2 - 1 ≤ qOf d := by rw [qOf]; linarith
  have hx : 0 ≤ qOf d * η0Of d p := (mul_pos hq0 hu0).le
  have h2 : (qOf d * η0Of d p) ^ 2 * p = 4 * (1 - η0Of d p) * qOf d := by
    linear_combination qOf d * h
  have h3 : 100 ≤ (qOf d * η0Of d p) ^ 2 := by
    by_contra hc
    rw [not_le] at hc
    have h4 : (qOf d * η0Of d p) ^ 2 * p ≤ 100 * p :=
      mul_le_mul_of_nonneg_right hc.le (by positivity)
    nlinarith [mul_nonneg (sub_nonneg.mpr hu) hq0.le,
      mul_nonneg (sub_nonneg.mpr hp) (sub_nonneg.mpr hp)]
  nlinarith

/-- `q - 1 + η₀ > 0`. -/
theorem TRegime.pf_D_pos (hR : TRegime d p) : 0 < qOf d - 1 + η0Of d p := by
  have := hR.qOf_ge
  have := hR.η0Of_pos
  linarith

/-- `1 - τ_* = (q - 1 + η₀)/q`. -/
theorem TRegime.pf_one_sub_τ (hR : TRegime d p) :
    1 - τsOf d p = (qOf d - 1 + η0Of d p) / qOf d := by
  have hq := hR.qOf_pos.ne'
  rw [τsOf, eq_div_iff hq, sub_mul, div_mul_cancel₀ _ hq]
  ring

/-- `L̄ (q - 1 + η₀)² = (q + 1) q (1 - η₀)`. -/
theorem TRegime.pf_Lbar_mul (hR : TRegime d p) :
    LbarP d p * (qOf d - 1 + η0Of d p) ^ 2 = (qOf d + 1) * qOf d * (1 - η0Of d p) := by
  have hq := hR.qOf_pos.ne'
  have hD := hR.pf_D_pos.ne'
  rw [LbarP, mul_assoc (d : ℝ), hR.kappa_eq, hR.pf_one_sub_τ, τsOf, pf_d_eq d]
  field_simp

/-- `s (q - 1 + η₀) = (2 - η₀) q`. -/
theorem TRegime.pf_s_mul (hR : TRegime d p) :
    sOf d p * (qOf d - 1 + η0Of d p) = (2 - η0Of d p) * qOf d := by
  have hq := hR.qOf_pos.ne'
  have hD := hR.pf_D_pos.ne'
  rw [sOf, hR.one_add_qOf_mul_τsOf, hR.pf_one_sub_τ]
  field_simp

/-- `a² ≤ 1/d`. -/
theorem TRegime.pf_a_sq_le (hR : TRegime d p) : aOf d p ^ 2 ≤ 1 / (d : ℝ) := by
  have hd := hR.ten_pow_six_le_d
  have hΔ := hR.ΔOf_pos
  rw [hR.aOf_sq]
  apply one_div_le_one_div_of_le (by linarith)
  rw [RsqOf, qOf]
  linarith

/-- `1/(4d) ≤ a²`. -/
theorem TRegime.pf_a_sq_ge (hR : TRegime d p) : 1 / (4 * (d : ℝ)) ≤ aOf d p ^ 2 := by
  have hΔ := hR.ΔOf_le_two
  rw [hR.aOf_sq]
  apply one_div_le_one_div_of_le hR.RsqOf_pos
  rw [RsqOf, qOf]
  linarith

/-- `d a² ≤ 1/4 + 1/d`. -/
theorem TRegime.pf_d_a_sq_le (hR : TRegime d p) :
    (d : ℝ) * aOf d p ^ 2 ≤ 1 / 4 + 1 / (d : ℝ) := by
  have hd := hR.ten_pow_six_le_d
  have hΔ := hR.ΔOf_pos
  have hR2 := hR.RsqOf_pos
  have hd0 : (0 : ℝ) < d := by linarith
  rw [hR.aOf_sq, div_add_div _ _ (by norm_num) hd0.ne', mul_one_div,
    div_le_div_iff₀ hR2 (by positivity)]
  rw [RsqOf, qOf]
  nlinarith [mul_pos hd0 hΔ]

/-- `1 ≤ η₀ √(pd) ≤ 2`, from `(η₀ √(pd))² q = 4 (1 - η₀)(q + 1)`. -/
theorem TRegime.pf_u_sqrt (hR : TRegime d p) :
    1 ≤ η0Of d p * Real.sqrt ((p : ℝ) * d) ∧ η0Of d p * Real.sqrt ((p : ℝ) * d) ≤ 2 := by
  have hpq := hR.pf_p_mul
  have hu0 := hR.η0Of_pos
  have hu1 := hR.η0Of_le
  have hqu := hR.pf_qu_ge
  have hq0 := hR.qOf_pos
  have hd := pf_d_eq d
  have hw := Real.sq_sqrt (show (0 : ℝ) ≤ p * d by positivity)
  have hw0 := Real.sqrt_nonneg ((p : ℝ) * d)
  set w := Real.sqrt ((p : ℝ) * d)
  set u := η0Of d p
  set Q := qOf d
  have h2 : (u * w) ^ 2 * Q = 4 * (1 - u) * (Q + 1) := by
    linear_combination u ^ 2 * Q * hw + (d : ℝ) * hpq + 4 * (1 - u) * hd
  have hx : 0 ≤ u * w := mul_nonneg hu0.le hw0
  have hlo : 1 ≤ (u * w) ^ 2 := by
    refine le_of_mul_le_mul_right ?_ hq0
    rw [h2]
    nlinarith [mul_nonneg (sub_nonneg.mpr hu1) hq0.le]
  have hhi : (u * w) ^ 2 ≤ 4 := by
    refine le_of_mul_le_mul_right ?_ hq0
    rw [h2]
    nlinarith
  constructor <;> nlinarith

/-! ### The parameter facts -/

theorem param_facts_pf : ∃ P₀ : ℕ, ∀ d p : ℕ, TRegime d p → P₀ ≤ p →
    aOf d p ^ 2 ≤ 1 / (d : ℝ) ∧ 1 / (4 * (d : ℝ)) ≤ aOf d p ^ 2 ∧
    (d : ℝ) * aOf d p ^ 2 ≤ 1 / 4 + 1 / (d : ℝ) ∧
    1 / (2 * Real.sqrt ((p : ℝ) * d)) ≤ epsP d p ∧ epsP d p ≤ 1 / Real.sqrt ((p : ℝ) * d) ∧
    η0Of d p ≤ 2 / Real.sqrt ((p : ℝ) * d) ∧
    0 ≤ 1 - rOf d p * LbarP d p ∧
    1 / (p : ℝ) - 2 * η0Of d p ≤ (d : ℝ) * epsP d p * (1 - rOf d p * LbarP d p) ∧
    rOf d p * LbarP d p * sOf d p ^ 2 ≤ 4 ∧ 4 - 8 * η0Of d p ≤ LbarP d p * sOf d p ^ 2 ∧
    1 / 2 ≤ LbarP d p ∧ LbarP d p ≤ 2 ∧ sOf d p ^ 2 ≤ 5 := by
  refine ⟨0, fun d p hR _ => ?_⟩
  have hq := hR.qOf_ge
  have hu0 := hR.η0Of_pos
  have hu1 := hR.η0Of_le
  have hqu := hR.pf_qu_ge
  have hqu2 := hR.pf_qu2_le
  have hL := hR.pf_Lbar_mul
  have hs := hR.pf_s_mul
  have hQ10 : (10 : ℝ) ≤ qOf d := by linarith
  have hr : rOf d p = 1 + η0Of d p / 2 := rfl
  have hp0 : (0 : ℝ) < p := by exact_mod_cast lt_of_lt_of_le (by norm_num) hR.hp
  have hd0 : (0 : ℝ) < d := lt_of_lt_of_le (by norm_num) hR.ten_pow_six_le_d
  have hw0 : 0 < Real.sqrt ((p : ℝ) * d) := Real.sqrt_pos.mpr (mul_pos hp0 hd0)
  obtain ⟨hw1, hw2⟩ := hR.pf_u_sqrt
  have hε := pf_epsP_eq d p
  have hLge := pf_L_ge (by linarith) hu0.le hu1 hL
  have hsge := pf_s_ge (by linarith) hu0.le hu1 hs
  refine ⟨hR.pf_a_sq_le, hR.pf_a_sq_ge, hR.pf_d_a_sq_le, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hε, div_le_div_iff₀ (mul_pos two_pos hw0) two_pos]
    linarith
  · rw [hε, div_le_div_iff₀ two_pos hw0]
    linarith
  · rw [le_div_iff₀ hw0]
    linarith
  · have := pf_rL_real hQ10 hu0.le hqu hL
    rw [hr]
    linarith
  · have hip : 1 / (p : ℝ) * (4 * (1 - η0Of d p)) = qOf d * η0Of d p ^ 2 := by
      rw [← hR.pf_p_mul, one_div, inv_mul_cancel_left₀ hp0.ne']
    rw [pf_d_eq d, hε, hr]
    exact pf_drift_real hq hu0 hu1 hqu2 hL hip
  · rw [hr]
    exact pf_rLs_real hQ10 hu0.le hu1 hqu hL hs
  · have h1 : (2 - η0Of d p) ^ 2 ≤ sOf d p ^ 2 := pow_le_pow_left₀ (by linarith) hsge 2
    have h2 : (1 - η0Of d p) * (2 - η0Of d p) ^ 2 ≤ LbarP d p * sOf d p ^ 2 :=
      mul_le_mul hLge h1 (sq_nonneg _) (by linarith)
    nlinarith [mul_nonneg (sq_nonneg (η0Of d p)) (by linarith : (0 : ℝ) ≤ 5 - η0Of d p)]
  · linarith
  · have := hR.d_mul_kappa_le
    rw [LbarP, mul_assoc]
    linarith
  · exact pf_s_sq_le hQ10 hu0.le hu1 hs

end BiluLinial.Tight
