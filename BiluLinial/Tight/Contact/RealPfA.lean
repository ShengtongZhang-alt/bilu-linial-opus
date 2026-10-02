/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.Contact.RealParams

/-!
# Real leaves of Section 1.5, batch A (proofs)

Verbatim copies, with suffix `_pf`, of the theorems `d4_real`, `d6_real`, `d7_real`, `d9b_real`,
`d10_real`, `qP_le_real` and `d15_real` of `Tight/Contact/Real.lean`, with proofs. The one change:
`d10_real_pf` has the extra hypothesis `0 ≤ CB` (`d10_real` is false for `CB < 0`,
`docs/tight/CHECK_CONTACT.md` §R6). Sketches and witnesses: `CHECK_CONTACT.md` §R2–R7, §R12.

The regime helpers (prefix `pfA_`) are the facts (T1)–(T4) of `CHECK_CONTACT.md`:
`p⁷·10⁹ ≤ d`, `δ̄ ≤ 3 (p/d)^{1/3}`, `p² δ̄ ≤ 1`, `p¹¹ δ̄ ≤ 3d`, `Γ² p² ≤ 3`, `ε_s p ≤ 1`.
-/

@[expose] public section

namespace BiluLinial.Tight

variable {d p : ℕ}

/-! ### Regime helpers -/

theorem TRegime.pfA_p_ge (hR : TRegime d p) : (10 : ℝ) ^ 6 ≤ p := by exact_mod_cast hR.hp

theorem TRegime.pfA_p_pos (hR : TRegime d p) : (0 : ℝ) < p :=
  lt_of_lt_of_le (by norm_num) hR.pfA_p_ge

theorem TRegime.pfA_one_le_p (hR : TRegime d p) : (1 : ℝ) ≤ p :=
  le_trans (by norm_num) hR.pfA_p_ge

theorem TRegime.pfA_d_pos (hR : TRegime d p) : (0 : ℝ) < d :=
  lt_of_lt_of_le (by norm_num) hR.ten_pow_six_le_d

theorem TRegime.pfA_p17 (hR : TRegime d p) : (p : ℝ) ^ 17 ≤ (d : ℝ) ^ 2 := by
  exact_mod_cast hR.hpd

/-- `p⁷ · 10⁹ ≤ d`, from `p¹⁴ · 10¹⁸ ≤ p¹⁷ ≤ d²`. -/
theorem TRegime.pfA_p7 (hR : TRegime d p) : (p : ℝ) ^ 7 * 10 ^ 9 ≤ d := by
  have h3 : (10 ^ 6) ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left hR.hp 3
  have h : (p ^ 7 * 10 ^ 9) ^ 2 ≤ d ^ 2 :=
    calc (p ^ 7 * 10 ^ 9) ^ 2 = p ^ 14 * (10 ^ 6) ^ 3 := by ring
      _ ≤ p ^ 14 * p ^ 3 := Nat.mul_le_mul_left _ h3
      _ = p ^ 17 := by ring
      _ ≤ d ^ 2 := hR.hpd
  exact_mod_cast (Nat.pow_le_pow_iff_left (by norm_num)).mp h

/-- `p⁵/d ≤ 1`. -/
theorem TRegime.pfA_p5_div_le (hR : TRegime d p) : (p : ℝ) ^ 5 / d ≤ 1 := by
  have h2 : (p : ℝ) ^ 5 ≤ p ^ 7 := pow_le_pow_right₀ hR.pfA_one_le_p (by norm_num)
  have h3 := hR.pfA_p7
  have h4 : (0 : ℝ) ≤ p ^ 7 := by positivity
  rw [div_le_one hR.pfA_d_pos]
  linarith

/-- `p¹³/d² ≤ 1`. -/
theorem TRegime.pfA_p13_div_le (hR : TRegime d p) : (p : ℝ) ^ 13 / (d : ℝ) ^ 2 ≤ 1 := by
  have h2 : (p : ℝ) ^ 13 ≤ p ^ 17 := pow_le_pow_right₀ hR.pfA_one_le_p (by norm_num)
  rw [div_le_one (pow_pos hR.pfA_d_pos 2)]
  linarith [hR.pfA_p17]

theorem pfA_vth_nonneg (d : ℕ) : 0 ≤ vth d := by
  unfold vth
  positivity

/-- `ϑ d ≤ 1`. -/
theorem TRegime.pfA_vth_mul_d (hR : TRegime d p) : vth d * d ≤ 1 := by
  have hd1 : (1 : ℝ) ≤ d := le_trans (by norm_num) hR.ten_pow_six_le_d
  unfold vth
  rw [div_mul_eq_mul_div, one_mul, div_le_one (pow_pos hR.pfA_d_pos 10)]
  exact le_self_pow₀ hd1 (by norm_num)

theorem TRegime.pfA_vth_le_one (hR : TRegime d p) : vth d ≤ 1 := by
  have h := hR.pfA_vth_mul_d
  have hd1 : (1 : ℝ) ≤ d := le_trans (by norm_num) hR.ten_pow_six_le_d
  have h0 := pfA_vth_nonneg d
  nlinarith

/-- `a² d ≤ 1`. -/
theorem TRegime.pfA_a_sq_mul_d (hR : TRegime d p) : aOf d p ^ 2 * d ≤ 1 := by
  have h := hR.pf_a_sq_le
  rwa [le_div_iff₀ hR.pfA_d_pos] at h

theorem pfA_epsS_nonneg (d p : ℕ) : 0 ≤ epsS d p := by
  unfold epsS
  positivity

/-- `ε_s² = p³/d`. -/
theorem TRegime.pfA_epsS_sq (hR : TRegime d p) : epsS d p ^ 2 = (p : ℝ) ^ 3 / d := by
  unfold epsS
  rw [div_pow, mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ p),
    Real.sq_sqrt hR.pfA_d_pos.le]
  ring

/-- `ε_s p ≤ 1`. -/
theorem TRegime.pfA_epsS_mul_p (hR : TRegime d p) : epsS d p * p ≤ 1 := by
  refine le_of_pow_le_pow_left₀ two_ne_zero zero_le_one ?_
  rw [mul_pow, hR.pfA_epsS_sq, one_pow]
  calc (p : ℝ) ^ 3 / d * p ^ 2 = p ^ 5 / d := by ring
    _ ≤ 1 := hR.pfA_p5_div_le

/-- Arithmetic–geometric mean: `X² ≤ αβ` gives `X ≤ (α + β)/2`. -/
theorem pfA_amgm {X α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (h : X ^ 2 ≤ α * β) :
    X ≤ (α + β) / 2 := by
  by_contra hc
  rw [not_le] at hc
  have h1 : ((α + β) / 2) ^ 2 < X ^ 2 := pow_lt_pow_left₀ hc (by linarith) two_ne_zero
  nlinarith [sq_nonneg (α - β)]

/-- `((p/d)^{1/3})³ = p/d`. -/
theorem pfA_cbrt_cube (d p : ℕ) : (((p : ℝ) / d) ^ ((1 : ℝ) / 3)) ^ 3 = (p : ℝ) / d := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  norm_num

theorem pfA_cbrt_nonneg (d p : ℕ) : 0 ≤ ((p : ℝ) / d) ^ ((1 : ℝ) / 3) :=
  Real.rpow_nonneg (by positivity) _

theorem TRegime.pfA_epsP_nonneg (hR : TRegime d p) : 0 ≤ epsP d p := by
  rw [pf_epsP_eq]
  linarith [hR.η0Of_pos]

/-- `ε² p d ≤ 1`. -/
theorem TRegime.pfA_epsP_sq (hR : TRegime d p) : epsP d p ^ 2 * ((p : ℝ) * d) ≤ 1 := by
  obtain ⟨-, hw2⟩ := hR.pf_u_sqrt
  have hw := Real.sq_sqrt (show (0 : ℝ) ≤ p * d by positivity)
  have hx : 0 ≤ η0Of d p * Real.sqrt ((p : ℝ) * d) :=
    mul_nonneg hR.η0Of_pos.le (Real.sqrt_nonneg _)
  have h4 : (η0Of d p * Real.sqrt ((p : ℝ) * d)) ^ 2 ≤ 4 := by nlinarith
  rw [pf_epsP_eq]
  calc (η0Of d p / 2) ^ 2 * ((p : ℝ) * d) = (η0Of d p * Real.sqrt ((p : ℝ) * d)) ^ 2 / 4 := by
        rw [mul_pow, hw]; ring
    _ ≤ 1 := by linarith

/-- `ε ≤ (p/d)^{1/3}`. -/
theorem TRegime.pfA_epsP_le_cbrt (hR : TRegime d p) :
    epsP d p ≤ ((p : ℝ) / d) ^ ((1 : ℝ) / 3) := by
  have h2 := hR.pfA_epsP_sq
  have hE0 := hR.pfA_epsP_nonneg
  have hE1 : epsP d p ≤ 1 := by rw [pf_epsP_eq]; linarith [hR.η0Of_le]
  have hp1 := hR.pfA_one_le_p
  refine le_of_pow_le_pow_left₀ (n := 3) (by norm_num) (pfA_cbrt_nonneg d p) ?_
  rw [pfA_cbrt_cube, le_div_iff₀ hR.pfA_d_pos]
  have hq : 0 ≤ epsP d p ^ 2 * d := by positivity
  nlinarith [mul_nonneg (sub_nonneg.mpr hE1) hq, mul_nonneg (sub_nonneg.mpr hp1) hq]

/-- `p⁴/d ≤ (p/d)^{1/3}`. -/
theorem TRegime.pfA_p4_le_cbrt (hR : TRegime d p) :
    (p : ℝ) ^ 4 / d ≤ ((p : ℝ) / d) ^ ((1 : ℝ) / 3) := by
  have hd0 := hR.pfA_d_pos
  refine le_of_pow_le_pow_left₀ (n := 3) (by norm_num) (pfA_cbrt_nonneg d p) ?_
  rw [pfA_cbrt_cube, div_pow, div_le_div_iff₀ (pow_pos hd0 3) hd0]
  have h11 : (p : ℝ) ^ 11 ≤ (d : ℝ) ^ 2 :=
    (pow_le_pow_right₀ hR.pfA_one_le_p (by norm_num)).trans hR.pfA_p17
  calc ((p : ℝ) ^ 4) ^ 3 * d = ((p : ℝ) * d) * (p : ℝ) ^ 11 := by ring
    _ ≤ ((p : ℝ) * d) * (d : ℝ) ^ 2 := mul_le_mul_of_nonneg_left h11 (by positivity)
    _ = (p : ℝ) * (d : ℝ) ^ 3 := by ring

/-- (T2) `δ̄ ≤ 3 (p/d)^{1/3}`. -/
theorem TRegime.pfA_dbar_le (hR : TRegime d p) :
    dbar d p ≤ 3 * ((p : ℝ) / d) ^ ((1 : ℝ) / 3) := by
  have h1 := hR.pfA_epsP_le_cbrt
  have h2 := hR.pfA_p4_le_cbrt
  unfold dbar
  linarith

theorem TRegime.pfA_dbar_nonneg (hR : TRegime d p) : 0 ≤ dbar d p := by
  have h1 := hR.pfA_epsP_nonneg
  have h2 : (0 : ℝ) ≤ (p : ℝ) ^ 4 / d := by positivity
  have h3 := pfA_cbrt_nonneg d p
  unfold dbar
  linarith

/-- `p² δ̄ ≤ 1` (from `27 p⁷ ≤ d`). -/
theorem TRegime.pfA_p2_dbar (hR : TRegime d p) : (p : ℝ) ^ 2 * dbar d p ≤ 1 := by
  have hd0 := hR.pfA_d_pos
  have hp0 := hR.pfA_p_pos
  have h7 := hR.pfA_p7
  have hdb := hR.pfA_dbar_le
  have h : 3 * (p : ℝ) ^ 2 * ((p : ℝ) / d) ^ ((1 : ℝ) / 3) ≤ 1 := by
    refine le_of_pow_le_pow_left₀ (n := 3) (by norm_num) zero_le_one ?_
    rw [mul_pow, pfA_cbrt_cube, one_pow, ← mul_div_assoc, div_le_one hd0]
    nlinarith [pow_nonneg hp0.le 7]
  nlinarith [mul_le_mul_of_nonneg_left hdb (sq_nonneg (p : ℝ))]

/-- `p¹¹ δ̄ ≤ 3d` (from `p³⁴ ≤ d⁴`). -/
theorem TRegime.pfA_p11_dbar (hR : TRegime d p) : (p : ℝ) ^ 11 * dbar d p ≤ 3 * d := by
  have hd0 := hR.pfA_d_pos
  have hp0 := hR.pfA_p_pos
  have hdb := hR.pfA_dbar_le
  have h34 : (p : ℝ) ^ 34 ≤ (d : ℝ) ^ 4 := by
    have := pow_le_pow_left₀ (by positivity) hR.pfA_p17 2
    calc (p : ℝ) ^ 34 = ((p : ℝ) ^ 17) ^ 2 := by ring
      _ ≤ ((d : ℝ) ^ 2) ^ 2 := this
      _ = (d : ℝ) ^ 4 := by ring
  have h : (p : ℝ) ^ 11 * ((p : ℝ) / d) ^ ((1 : ℝ) / 3) ≤ d := by
    refine le_of_pow_le_pow_left₀ (n := 3) (by norm_num) hd0.le ?_
    rw [mul_pow, pfA_cbrt_cube, ← mul_div_assoc, div_le_iff₀ hd0]
    calc ((p : ℝ) ^ 11) ^ 3 * p = (p : ℝ) ^ 34 := by ring
      _ ≤ (d : ℝ) ^ 4 := h34
      _ = (d : ℝ) ^ 3 * d := by ring
  nlinarith [mul_le_mul_of_nonneg_left hdb (pow_nonneg hp0.le 11)]

theorem pfA_gam_nonneg (d p : ℕ) : 0 ≤ GamP d p := by
  unfold GamP
  positivity

/-- (T3) `Γ² p² ≤ 3`. -/
theorem TRegime.pfA_gam_sq (hR : TRegime d p) : GamP d p ^ 2 * (p : ℝ) ^ 2 ≤ 3 := by
  have hd0 := hR.pfA_d_pos
  have hp0 := hR.pfA_p_pos
  have h11 := hR.pfA_p11_dbar
  have hdb0 := hR.pfA_dbar_nonneg
  unfold GamP
  rw [mul_pow, Real.sq_sqrt (div_nonneg (mul_nonneg hp0.le hdb0) hd0.le)]
  rw [show ((p : ℝ) ^ 4) ^ 2 * ((p : ℝ) * dbar d p / d) * (p : ℝ) ^ 2 =
    (p : ℝ) ^ 11 * dbar d p / d by ring]
  rw [div_le_iff₀ hd0]
  linarith

theorem pfA_erow_nonneg (d p : ℕ) (S : ℝ) : 0 ≤ ErowP d p S := by
  unfold ErowP
  exact add_nonneg (add_nonneg (mul_nonneg (pfA_gam_nonneg d p) (Real.sqrt_nonneg _))
    (by positivity)) (pfA_vth_nonneg d)

/-- `a² p ≤ 2 ε_s ε` (T1 and `ε ≥ 1/(2√(pd))`). -/
theorem TRegime.pfA_a2p_le (hR : TRegime d p) :
    aOf d p ^ 2 * p ≤ 2 * epsS d p * epsP d p := by
  have hd0 := hR.pfA_d_pos
  have hp0 := hR.pfA_p_pos
  have had := hR.pfA_a_sq_mul_d
  have ha0 : 0 ≤ aOf d p ^ 2 := sq_nonneg _
  obtain ⟨hw1, -⟩ := hR.pf_u_sqrt
  have hw := Real.sq_sqrt (show (0 : ℝ) ≤ p * d by positivity)
  have hu2 : 1 ≤ η0Of d p ^ 2 * ((p : ℝ) * d) := by
    have e : (η0Of d p * Real.sqrt ((p : ℝ) * d)) ^ 2 = η0Of d p ^ 2 * ((p : ℝ) * d) := by
      rw [mul_pow, hw]
    nlinarith
  have h1 : (aOf d p ^ 2) ^ 2 * (d : ℝ) ^ 2 ≤ 1 := by
    have h0 : 0 ≤ aOf d p ^ 2 * d := mul_nonneg ha0 hd0.le
    nlinarith
  have key : (aOf d p ^ 2 * p) ^ 2 ≤ (epsS d p * η0Of d p) ^ 2 := by
    rw [mul_pow, mul_pow, hR.pfA_epsS_sq, div_mul_eq_mul_div, le_div_iff₀ hd0]
    have h2 : (aOf d p ^ 2) ^ 2 * (p : ℝ) ^ 2 * d * d ≤ (p : ℝ) ^ 3 * η0Of d p ^ 2 * d := by
      have e1 := mul_le_mul_of_nonneg_left h1 (sq_nonneg (p : ℝ))
      have e2 := mul_le_mul_of_nonneg_left hu2 (sq_nonneg (p : ℝ))
      linarith
    exact le_of_mul_le_mul_right h2 hd0
  have h3 := le_of_pow_le_pow_left₀ two_ne_zero
    (mul_nonneg (pfA_epsS_nonneg d p) hR.η0Of_pos.le) key
  rw [pf_epsP_eq]
  linarith

/-! ### D4 -/

/-- **R-D4**, verbatim copy of `d4_real` (sketch: `CHECK_CONTACT.md` §R2). -/
theorem d4_real_pf (C₃ CQ : ℝ) : ∃ C : ℝ, 0 < C ∧ ∃ P₀ : ℕ, ∀ d p : ℕ, TRegime d p → P₀ ≤ p →
    ∀ S R J Cp Q L sED : ℝ, 0 ≤ S → 0 ≤ Cp → Cp ≤ J → 0 ≤ sED → L ≤ LbarP d p →
      Cp ≤ aOf d p ^ 2 * LbarP d p * sOf d p ^ 2 →
      |Q| ≤ CQ * aOf d p ^ 2 * (p + (p : ℝ) ^ 3 * dbar d p) →
      epsP d p * (1 - rOf d p * L) + rOf d p * sED + (1 - 1 / (p : ℝ)) * aOf d p ^ 2 * S +
          rOf d p / p * J + 2 * aOf d p ^ 2 * R ≤
        Q + rOf d p * Cp + C₃ * (p : ℝ) ^ 5 / (d : ℝ) ^ 2 →
      R ≤ C * (p + (p : ℝ) ^ 5 / d) ∧
      ∀ b : ℝ, 0 ≤ b → -b ≤ R →
        S + sED / aOf d p ^ 2 ≤ C * (1 + p + (p : ℝ) ^ 5 / d + b) ∧
        LbarP d p - L ≤ C * aOf d p ^ 2 * (1 + p + (p : ℝ) ^ 5 / d + b) / epsP d p := by
  obtain ⟨P₁, hPF⟩ := param_facts_pf
  refine ⟨4 * |CQ| + 8 * |C₃| + 12, by positivity, P₁, fun d p hR hp => ?_⟩
  intro S R J Cp Q L sED hS hCp hCpJ hsED hL hCpb hQ hmain
  obtain ⟨-, hpa2, -, -, -, -, hrL, -, hrLs, -, -, -, -⟩ := hPF d p hR hp
  have hp0 := hR.pfA_p_pos
  have hp1 := hR.pfA_one_le_p
  have hd0 := hR.pfA_d_pos
  have hr1 := hR.one_lt_rOf
  have hE : 0 < epsP d p := by unfold epsP; linarith
  have ha0 : 0 < aOf d p ^ 2 := pow_pos hR.aOf_pos 2
  have hy0 : 0 ≤ (p : ℝ) ^ 5 / d := by positivity
  have hdb := hR.pfA_p2_dbar
  have hdb0 := hR.pfA_dbar_nonneg
  have hcq := abs_nonneg CQ
  have hc3 := abs_nonneg C₃
  -- `Q ≤ 2 |C_Q| a² p`
  have hQ' : Q ≤ |CQ| * aOf d p ^ 2 * (2 * p) := by
    have h1 : (p : ℝ) + p ^ 3 * dbar d p ≤ 2 * p := by
      nlinarith [mul_le_mul_of_nonneg_left hdb hp0.le]
    have h3 : (0 : ℝ) ≤ p ^ 3 * dbar d p := mul_nonneg (by positivity) hdb0
    have h2 : 0 ≤ aOf d p ^ 2 * (p + (p : ℝ) ^ 3 * dbar d p) := mul_nonneg ha0.le (by linarith)
    calc Q ≤ |Q| := le_abs_self Q
      _ ≤ CQ * aOf d p ^ 2 * (p + (p : ℝ) ^ 3 * dbar d p) := hQ
      _ = CQ * (aOf d p ^ 2 * (p + (p : ℝ) ^ 3 * dbar d p)) := by ring
      _ ≤ |CQ| * (aOf d p ^ 2 * (p + (p : ℝ) ^ 3 * dbar d p)) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) h2
      _ ≤ |CQ| * (aOf d p ^ 2 * (2 * p)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 ha0.le) hcq
      _ = |CQ| * aOf d p ^ 2 * (2 * p) := by ring
  -- `r C₊ ≤ 4 a²`
  have hrCp : rOf d p * Cp ≤ 4 * aOf d p ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left hCpb (by linarith : (0 : ℝ) ≤ rOf d p)
    have h2 := mul_le_mul_of_nonneg_left hrLs ha0.le
    linarith
  -- `C₃ p⁵/d² ≤ 4 |C₃| a² p⁵/d`
  have hC3 : C₃ * (p : ℝ) ^ 5 / (d : ℝ) ^ 2 ≤ 4 * |C₃| * aOf d p ^ 2 * ((p : ℝ) ^ 5 / d) := by
    have h1 : 1 / (d : ℝ) ≤ 4 * aOf d p ^ 2 := by
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < 4 * d)] at hpa2
      rw [div_le_iff₀ hd0]
      linarith
    have h2 : C₃ * (p : ℝ) ^ 5 / (d : ℝ) ^ 2 = C₃ * ((p : ℝ) ^ 5 / d) * (1 / d) := by ring
    rw [h2]
    calc C₃ * ((p : ℝ) ^ 5 / d) * (1 / d) ≤ |C₃| * ((p : ℝ) ^ 5 / d) * (1 / d) := by
          gcongr; exact le_abs_self _
      _ ≤ |C₃| * ((p : ℝ) ^ 5 / d) * (4 * aOf d p ^ 2) := by gcongr
      _ = 4 * |C₃| * aOf d p ^ 2 * ((p : ℝ) ^ 5 / d) := by ring
  have hJ : 0 ≤ rOf d p / p * J := mul_nonneg (div_nonneg (by linarith) hp0.le) (by linarith)
  have hrs : sED ≤ rOf d p * sED := le_mul_of_one_le_left hsED hr1.le
  have hS2 : 1 / 2 * aOf d p ^ 2 * S ≤ (1 - 1 / (p : ℝ)) * aOf d p ^ 2 * S := by
    have h1 : (1 : ℝ) / 2 ≤ 1 - 1 / p := by
      have : 1 / (p : ℝ) ≤ 1 / 2 :=
        one_div_le_one_div_of_le two_pos (le_trans (by norm_num) hR.pfA_p_ge)
      linarith
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 ha0.le) hS
  have hE1 : 0 ≤ epsP d p * (1 - rOf d p * LbarP d p) := mul_nonneg hE.le hrL
  have hELn : 0 ≤ rOf d p * epsP d p * (LbarP d p - L) :=
    mul_nonneg (mul_nonneg (by linarith) hE.le) (by linarith)
  have hSn : 0 ≤ 1 / 2 * aOf d p ^ 2 * S := mul_nonneg (by positivity) hS
  have hstar : rOf d p * epsP d p * (LbarP d p - L) + sED + 1 / 2 * aOf d p ^ 2 * S +
      2 * aOf d p ^ 2 * R ≤
      aOf d p ^ 2 * (2 * |CQ| * p + 4 + 4 * |C₃| * ((p : ℝ) ^ 5 / d)) := by
    linarith
  have hX0 : 0 ≤ 2 * |CQ| * p + 4 + 4 * |C₃| * ((p : ℝ) ^ 5 / d) := by positivity
  refine ⟨?_, fun b hb hRb => ?_⟩
  · have h2R : aOf d p ^ 2 * (2 * R) ≤
        aOf d p ^ 2 * (2 * |CQ| * p + 4 + 4 * |C₃| * ((p : ℝ) ^ 5 / d)) := by
      linarith
    have h := le_of_mul_le_mul_left h2R ha0
    linarith [mul_nonneg hcq hp0.le, mul_nonneg hc3 hy0, mul_nonneg hcq hy0,
      mul_nonneg hc3 hp0.le]
  · have hab : aOf d p ^ 2 * (-b) ≤ aOf d p ^ 2 * R := mul_le_mul_of_nonneg_left hRb ha0.le
    have hstar2 : rOf d p * epsP d p * (LbarP d p - L) + sED + 1 / 2 * aOf d p ^ 2 * S ≤
        aOf d p ^ 2 * (2 * |CQ| * p + 4 + 4 * |C₃| * ((p : ℝ) ^ 5 / d) + 2 * b) := by
      linarith
    have hXb : 2 * (2 * |CQ| * p + 4 + 4 * |C₃| * ((p : ℝ) ^ 5 / d) + 2 * b) ≤
        (4 * |CQ| + 8 * |C₃| + 12) * (1 + p + (p : ℝ) ^ 5 / d + b) := by
      linarith [mul_nonneg hcq hy0, mul_nonneg hcq hb, mul_nonneg hc3 hp0.le,
        mul_nonneg hc3 hb]
    constructor
    · have e : aOf d p ^ 2 * (S + sED / aOf d p ^ 2) = aOf d p ^ 2 * S + sED := by
        rw [mul_add, mul_div_cancel₀ _ ha0.ne']
      have h1 : aOf d p ^ 2 * (S + sED / aOf d p ^ 2) ≤
          aOf d p ^ 2 * (2 * (2 * |CQ| * p + 4 + 4 * |C₃| * ((p : ℝ) ^ 5 / d) + 2 * b)) := by
        rw [e]
        linarith
      exact (le_of_mul_le_mul_left h1 ha0).trans hXb
    · rw [le_div_iff₀ hE]
      have h1 : epsP d p * (LbarP d p - L) ≤ rOf d p * (epsP d p * (LbarP d p - L)) :=
        le_mul_of_one_le_left (mul_nonneg hE.le (by linarith)) hr1.le
      have h2 := mul_le_mul_of_nonneg_left hXb ha0.le
      have h3 := mul_nonneg ha0.le
        (by linarith : (0 : ℝ) ≤ 2 * |CQ| * p + 4 + 4 * |C₃| * ((p : ℝ) ^ 5 / d) + 2 * b)
      linarith

/-! ### D6 -/

/-- **R-D6**, verbatim copy of `d6_real` (sketch: `CHECK_CONTACT.md` §R3). -/
theorem d6_real_pf (C₁ Cw Ca C₄ : ℝ) : ∃ C : ℝ, 0 < C ∧ ∃ P₀ : ℕ, ∀ d p : ℕ, TRegime d p →
    P₀ ≤ p → ∀ S A2 W Gt R : ℝ, 0 ≤ S → 0 ≤ A2 → 0 ≤ W →
      |R - Gt| ≤ C₁ * ((p : ℝ) ^ 5 * Real.sqrt ((aOf d p ^ 2 * S + A2 + vth d) * dbar d p) +
        (p : ℝ) ^ 13 / (d : ℝ) ^ 2 + vth d) →
      0 ≤ Gt →
      W ≤ 2 * aOf d p ^ 2 * Gt + Cw * ((p : ℝ) ^ 4 / d) * (W + vth d) →
      A2 ≤ 2 * W + Ca * vth d →
      R ≤ C₄ * (p + (p : ℝ) ^ 5 / d) →
      (∀ b : ℝ, 0 ≤ b → -b ≤ R → S ≤ C₄ * (1 + p + (p : ℝ) ^ 5 / d + b)) →
      aOf d p ^ 2 * S + A2 + vth d ≤ C * p / d := by
  refine ⟨38 * |C₄| + 3 * ((|C₄| + 8) * |C₁|) ^ 2 + 4 * ((|C₄| + 8) * |C₁|) + 2 * |Ca| + 6,
    by positivity, ⌈2 * |Cw|⌉₊, fun d p hR hp => ?_⟩
  intro S A2 W Gt R hS hA2 hW0 habs hGt hW hA2b hR4 hboot
  have hp0 := hR.pfA_p_pos
  have hp1 := hR.pfA_one_le_p
  have hd0 := hR.pfA_d_pos
  have ha0 : 0 ≤ aOf d p ^ 2 := sq_nonneg _
  have had := hR.pfA_a_sq_mul_d
  have hϑ0 := pfA_vth_nonneg d
  have hϑd := hR.pfA_vth_mul_d
  have hϑ1 := hR.pfA_vth_le_one
  have hy0 : 0 ≤ (p : ℝ) ^ 5 / d := by positivity
  have hy1 := hR.pfA_p5_div_le
  have hu0 : 0 ≤ (p : ℝ) ^ 13 / (d : ℝ) ^ 2 := by positivity
  have hu1 := hR.pfA_p13_div_le
  have hdb0 := hR.pfA_dbar_nonneg
  have h11 := hR.pfA_p11_dbar
  have hc1 := abs_nonneg C₁
  have hc4 := abs_nonneg C₄
  have hca := abs_nonneg Ca
  have hK0 : 0 ≤ (|C₄| + 8) * |C₁| := by positivity
  have hCw : 2 * |Cw| ≤ p := (Nat.le_ceil _).trans (by exact_mod_cast hp)
  have hlam0 : 0 ≤ aOf d p ^ 2 * S + A2 + vth d :=
    add_nonneg (add_nonneg (mul_nonneg ha0 hS) hA2) hϑ0
  generalize hlam : aOf d p ^ 2 * S + A2 + vth d = lam at habs hlam0 ⊢
  have hs0 : 0 ≤ Real.sqrt (lam * dbar d p) := Real.sqrt_nonneg _
  have hs2 : Real.sqrt (lam * dbar d p) ^ 2 = lam * dbar d p :=
    Real.sq_sqrt (mul_nonneg hlam0 hdb0)
  generalize hs : Real.sqrt (lam * dbar d p) = s at habs hs0 hs2
  have hF0 : 0 ≤ (p : ℝ) ^ 5 * s + (p : ℝ) ^ 13 / (d : ℝ) ^ 2 + vth d :=
    add_nonneg (add_nonneg (mul_nonneg (by positivity) hs0) hu0) hϑ0
  generalize hF : (p : ℝ) ^ 5 * s + (p : ℝ) ^ 13 / (d : ℝ) ^ 2 + vth d = F at habs hF0
  have hAF : 0 ≤ |C₁| * F := mul_nonneg hc1 hF0
  have hE : C₁ * F ≤ |C₁| * F := mul_le_mul_of_nonneg_right (le_abs_self _) hF0
  obtain ⟨hRG1, -⟩ := abs_le.mp (habs.trans hE)
  have hS1 := hboot (|C₁| * F) hAF (by linarith)
  have hS2 : S ≤ |C₄| * (1 + p + (p : ℝ) ^ 5 / d + |C₁| * F) :=
    hS1.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith))
  have hGt' : Gt ≤ |C₄| * (p + (p : ℝ) ^ 5 / d) + |C₁| * F := by
    have := mul_le_mul_of_nonneg_right (le_abs_self C₄)
      (by linarith : (0 : ℝ) ≤ p + (p : ℝ) ^ 5 / d)
    linarith only [hRG1, hR4, this]
  -- the whitening coefficient is at most `1/2`
  have hCwb : Cw * ((p : ℝ) ^ 4 / d) * (W + vth d) ≤ 1 / 2 * (W + vth d) := by
    have h1 : (p : ℝ) ^ 4 / d * p ≤ 1 := by
      have h5 := hy1
      rw [div_le_one hd0] at h5
      rw [div_mul_eq_mul_div, div_le_one hd0]
      linarith
    have h3 : Cw * ((p : ℝ) ^ 4 / d) ≤ |Cw| * ((p : ℝ) ^ 4 / d) :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    have h4 := mul_le_mul_of_nonneg_left hCw (by positivity : (0 : ℝ) ≤ (p : ℝ) ^ 4 / d)
    have h2 : Cw * ((p : ℝ) ^ 4 / d) ≤ 1 / 2 := by linarith only [h1, h3, h4]
    exact mul_le_mul_of_nonneg_right h2 (by linarith)
  have hW' : W ≤ 4 * aOf d p ^ 2 * Gt + vth d := by linarith only [hW, hCwb]
  have hA2' : A2 ≤ 8 * aOf d p ^ 2 * Gt + (2 + |Ca|) * vth d := by
    have := mul_le_mul_of_nonneg_right (le_abs_self Ca) hϑ0
    linarith only [hA2b, hW', this]
  have hlam1 : lam ≤ aOf d p ^ 2 * (|C₄| * (1 + p + (p : ℝ) ^ 5 / d + |C₁| * F) +
      8 * (|C₄| * (p + (p : ℝ) ^ 5 / d) + |C₁| * F)) + (3 + |Ca|) * vth d := by
    have h1 := mul_le_mul_of_nonneg_left hS2 ha0
    have h2 := mul_le_mul_of_nonneg_left hGt' ha0
    linarith only [hlam, h1, h2, hA2']
  have hBr0 : 0 ≤ |C₄| * (1 + p + (p : ℝ) ^ 5 / d + |C₁| * F) +
      8 * (|C₄| * (p + (p : ℝ) ^ 5 / d) + |C₁| * F) := by
    have h1 := mul_nonneg hc4 (by linarith : (0 : ℝ) ≤ 1 + p + (p : ℝ) ^ 5 / d + |C₁| * F)
    have h2 := mul_nonneg hc4 (by linarith : (0 : ℝ) ≤ p + (p : ℝ) ^ 5 / d)
    linarith only [h1, h2, hAF]
  have hlamd : lam * d ≤ |C₄| * (1 + p + (p : ℝ) ^ 5 / d + |C₁| * F) +
      8 * (|C₄| * (p + (p : ℝ) ^ 5 / d) + |C₁| * F) + (3 + |Ca|) := by
    have h1 := mul_le_mul_of_nonneg_right hlam1 hd0.le
    have h2 := mul_le_mul_of_nonneg_right had hBr0
    have h3 := mul_le_mul_of_nonneg_left hϑd (by positivity : (0 : ℝ) ≤ 3 + |Ca|)
    linarith only [h1, h2, h3]
  -- Young on the row term
  have h10 : (p : ℝ) ^ 10 * dbar d p ≤ 3 * p * d := by
    have e1 := mul_le_mul_of_nonneg_left hp1 (mul_nonneg (pow_nonneg hp0.le 10) hdb0)
    have e2 := mul_le_mul_of_nonneg_right hp1 hd0.le
    linarith only [e1, e2, h11]
  have hX2 : ((|C₄| + 8) * |C₁| * (p : ℝ) ^ 5 * s) ^ 2 ≤
      (lam * d) * (3 * ((|C₄| + 8) * |C₁|) ^ 2 * p) := by
    have e : ((|C₄| + 8) * |C₁| * (p : ℝ) ^ 5 * s) ^ 2 =
        ((|C₄| + 8) * |C₁|) ^ 2 * lam * ((p : ℝ) ^ 10 * dbar d p) := by
      rw [mul_pow, hs2]; ring
    rw [e]
    have := mul_le_mul_of_nonneg_left h10 (mul_nonneg (sq_nonneg ((|C₄| + 8) * |C₁|)) hlam0)
    linarith only [this]
  have hX : (|C₄| + 8) * |C₁| * (p : ℝ) ^ 5 * s ≤
      (lam * d + 3 * ((|C₄| + 8) * |C₁|) ^ 2 * p) / 2 :=
    pfA_amgm (mul_nonneg hlam0 hd0.le) (by positivity) hX2
  have hKF : (|C₄| + 8) * |C₁| * F = (|C₄| + 8) * |C₁| * (p : ℝ) ^ 5 * s +
      (|C₄| + 8) * |C₁| * ((p : ℝ) ^ 13 / (d : ℝ) ^ 2) + (|C₄| + 8) * |C₁| * vth d := by
    rw [← hF]; ring
  have hKu : (|C₄| + 8) * |C₁| * ((p : ℝ) ^ 13 / (d : ℝ) ^ 2) ≤ (|C₄| + 8) * |C₁| * p :=
    mul_le_mul_of_nonneg_left (by linarith) hK0
  have hKϑ : (|C₄| + 8) * |C₁| * vth d ≤ (|C₄| + 8) * |C₁| * p :=
    mul_le_mul_of_nonneg_left (by linarith) hK0
  have g1 := mul_nonneg hc4 (sub_nonneg.mpr hp1)
  have g2 := mul_nonneg hc4 (by linarith : (0 : ℝ) ≤ p - (p : ℝ) ^ 5 / d)
  have g3 := mul_nonneg hca (sub_nonneg.mpr hp1)
  rw [le_div_iff₀ hd0]
  linarith only [hlamd, hKF, hX, hKu, hKϑ, g1, g2, g3, hp1]

/-! ### D7 -/

/-- **R-D7**, verbatim copy of `d7_real` (sketch: `CHECK_CONTACT.md` §R4). -/
theorem d7_real_pf (C₁ C₄ C₆ : ℝ) : ∃ C : ℝ, 0 < C ∧ ∃ P₀ : ℕ, ∀ d p : ℕ, TRegime d p →
    P₀ ≤ p → ∀ S A2 Gt R L sED : ℝ, 0 ≤ S → 0 ≤ A2 →
      aOf d p ^ 2 * S + A2 + vth d ≤ C₆ * p / d →
      |R - Gt| ≤ C₁ * ((p : ℝ) ^ 5 * Real.sqrt ((aOf d p ^ 2 * S + A2 + vth d) * dbar d p) +
        (p : ℝ) ^ 13 / (d : ℝ) ^ 2 + vth d) →
      0 ≤ Gt →
      (∀ b : ℝ, 0 ≤ b → -b ≤ R →
        S + sED / aOf d p ^ 2 ≤ C₄ * (1 + p + (p : ℝ) ^ 5 / d + b) ∧
        LbarP d p - L ≤ C₄ * aOf d p ^ 2 * (1 + p + (p : ℝ) ^ 5 / d + b) / epsP d p) →
      0 ≤ sED →
      S ≤ C * p ∧ sED ≤ C * p * aOf d p ^ 2 ∧ LbarP d p - L ≤ C * epsS d p := by
  refine ⟨2 * (|C₄| * (3 + |C₁| * (Real.sqrt (3 * |C₆|) + 2))) + 1, by positivity, 0,
    fun d p hR _ => ?_⟩
  intro S A2 Gt R L sED hS hA2 hlamC habs hGt hboot hsED
  have hp0 := hR.pfA_p_pos
  have hp1 := hR.pfA_one_le_p
  have hd0 := hR.pfA_d_pos
  have ha0 : 0 < aOf d p ^ 2 := pow_pos hR.aOf_pos 2
  have hE : 0 < epsP d p := by unfold epsP; linarith [hR.one_lt_rOf]
  have hϑ0 := pfA_vth_nonneg d
  have hϑ1 := hR.pfA_vth_le_one
  have hy0 : 0 ≤ (p : ℝ) ^ 5 / d := by positivity
  have hy1 := hR.pfA_p5_div_le
  have hu0 : 0 ≤ (p : ℝ) ^ 13 / (d : ℝ) ^ 2 := by positivity
  have hu1 := hR.pfA_p13_div_le
  have hdb0 := hR.pfA_dbar_nonneg
  have h11 := hR.pfA_p11_dbar
  have hes0 := pfA_epsS_nonneg d p
  have hc1 := abs_nonneg C₁
  have hc4 := abs_nonneg C₄
  have hB0 : 0 ≤ |C₁| * (Real.sqrt (3 * |C₆|) + 2) := by positivity
  have hM0 : 0 ≤ |C₄| * (3 + |C₁| * (Real.sqrt (3 * |C₆|) + 2)) := by positivity
  have hlam0 : 0 ≤ aOf d p ^ 2 * S + A2 + vth d :=
    add_nonneg (add_nonneg (mul_nonneg ha0.le hS) hA2) hϑ0
  generalize hlam : aOf d p ^ 2 * S + A2 + vth d = lam at hlamC habs hlam0
  -- `p⁵ √(λ δ̄) ≤ √(3|C₆|)`
  have hlamd : lam * d ≤ |C₆| * p := by
    rw [le_div_iff₀ hd0] at hlamC
    linarith [mul_le_mul_of_nonneg_right (le_abs_self C₆) hp0.le]
  have hx : ((p : ℝ) ^ 5) ^ 2 * (lam * dbar d p) ≤ 3 * |C₆| := by
    have h1 := mul_le_mul_of_nonneg_left hlamd (mul_nonneg (pow_nonneg hp0.le 10) hdb0)
    have h2 := mul_le_mul_of_nonneg_left h11 (abs_nonneg C₆)
    have h3 : ((p : ℝ) ^ 5) ^ 2 * (lam * dbar d p) * d ≤ 3 * |C₆| * d := by
      linarith only [h1, h2]
    exact le_of_mul_le_mul_right h3 hd0
  have hsq : (p : ℝ) ^ 5 * Real.sqrt (lam * dbar d p) ≤ Real.sqrt (3 * |C₆|) := by
    have e : (p : ℝ) ^ 5 * Real.sqrt (lam * dbar d p) =
        Real.sqrt (((p : ℝ) ^ 5) ^ 2 * (lam * dbar d p)) := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (pow_nonneg hp0.le 5)]
    rw [e]
    exact Real.sqrt_le_sqrt hx
  have hF0 : 0 ≤ (p : ℝ) ^ 5 * Real.sqrt (lam * dbar d p) + (p : ℝ) ^ 13 / (d : ℝ) ^ 2 +
      vth d := add_nonneg (add_nonneg (mul_nonneg (by positivity) (Real.sqrt_nonneg _)) hu0) hϑ0
  have hF1 : (p : ℝ) ^ 5 * Real.sqrt (lam * dbar d p) + (p : ℝ) ^ 13 / (d : ℝ) ^ 2 + vth d ≤
      Real.sqrt (3 * |C₆|) + 2 := by linarith only [hsq, hu1, hϑ1]
  generalize hF : (p : ℝ) ^ 5 * Real.sqrt (lam * dbar d p) + (p : ℝ) ^ 13 / (d : ℝ) ^ 2 +
    vth d = F at habs hF0 hF1
  have hb0 : 0 ≤ C₁ * F := (abs_nonneg _).trans habs
  have hbB : C₁ * F ≤ |C₁| * (Real.sqrt (3 * |C₆|) + 2) :=
    (mul_le_mul_of_nonneg_right (le_abs_self _) hF0).trans (mul_le_mul_of_nonneg_left hF1 hc1)
  obtain ⟨hRG1, -⟩ := abs_le.mp habs
  obtain ⟨hb1, hb2⟩ := hboot (C₁ * F) hb0 (by linarith)
  -- `C₄ (1 + p + p⁵/d + b) ≤ M p` with `M = |C₄| (3 + B₁)`
  have hY0 : 0 ≤ 1 + p + (p : ℝ) ^ 5 / d + C₁ * F := by linarith
  have hY1 : 1 + p + (p : ℝ) ^ 5 / d + C₁ * F ≤
      (3 + |C₁| * (Real.sqrt (3 * |C₆|) + 2)) * p := by
    linarith only [mul_nonneg hB0 (sub_nonneg.mpr hp1), hbB, hy1, hp1]
  have hY : C₄ * (1 + p + (p : ℝ) ^ 5 / d + C₁ * F) ≤
      |C₄| * (3 + |C₁| * (Real.sqrt (3 * |C₆|) + 2)) * p := by
    have := (mul_le_mul_of_nonneg_right (le_abs_self C₄) hY0).trans
      (mul_le_mul_of_nonneg_left hY1 hc4)
    linarith only [this]
  have hsa : 0 ≤ sED / aOf d p ^ 2 := div_nonneg hsED ha0.le
  have hMp := mul_nonneg hM0 hp0.le
  refine ⟨by linarith only [hb1, hY, hsa, hMp], ?_, ?_⟩
  · have h1 : sED / aOf d p ^ 2 ≤ |C₄| * (3 + |C₁| * (Real.sqrt (3 * |C₆|) + 2)) * p := by
      linarith only [hb1, hY, hS]
    rw [div_le_iff₀ ha0] at h1
    have h2 := mul_nonneg hMp ha0.le
    have h3 := mul_nonneg hp0.le ha0.le
    linarith only [h1, h2, h3]
  · have h1 : C₄ * aOf d p ^ 2 * (1 + p + (p : ℝ) ^ 5 / d + C₁ * F) / epsP d p ≤
        2 * (|C₄| * (3 + |C₁| * (Real.sqrt (3 * |C₆|) + 2))) * epsS d p := by
      rw [div_le_iff₀ hE]
      have e1 := mul_le_mul_of_nonneg_left hY ha0.le
      have e2 := mul_le_mul_of_nonneg_left hR.pfA_a2p_le hM0
      linarith only [e1, e2]
    have h2 := mul_nonneg hM0 hes0
    linarith only [hb2, h1, h2, hes0]

/-! ### D9b -/

/-- **R-D9b**, verbatim copy of `d9b_real` (sketch: `CHECK_CONTACT.md` §R5). -/
theorem d9b_real_pf (CB C₉ C₄ C₇ : ℝ) : ∃ C : ℝ, 0 < C ∧ ∀ κ₀ : ℝ, 0 < κ₀ → κ₀ ≤ 1 →
    ∃ P₀ : ℕ, ∀ (d p : ℕ) (h : ℝ), Reg κ₀ d p h → P₀ ≤ p →
    ∀ S R Gt Qb : ℝ, 0 ≤ S →
      (1 - CB * etaBL d p h) * Qb - CB * epsBL d p h ≤ Gt →
      |R - Gt| ≤ C₉ * ErowP d p S →
      R ≤ C₄ * (p + (p : ℝ) ^ 5 / d) →
      S ≤ C₇ * p →
      Qb ≤ C * p := by
  refine ⟨4 * |C₄| + 2 * |C₉| * (|C₇| + 4) + 2 * |CB| + 1, by positivity, fun κ₀ hk0 _ =>
    ⟨⌈4 * |CB| + 1 / κ₀⌉₊, fun d p h hR hp => ?_⟩⟩
  intro S R Gt Qb hS hB1 habs hR4 hS7
  have hT := hR.treg
  have hp0 := hT.pfA_p_pos
  have hp1 := hT.pfA_one_le_p
  have hd0 := hT.pfA_d_pos
  have hϑ0 := pfA_vth_nonneg d
  have hϑd := hT.pfA_vth_mul_d
  have hϑ1 := hT.pfA_vth_le_one
  have hy0 : 0 ≤ (p : ℝ) ^ 5 / d := by positivity
  have hy1 := hT.pfA_p5_div_le
  have hu1 := hT.pfA_p13_div_le
  have hcb := abs_nonneg CB
  have hc9 := abs_nonneg C₉
  have hc4 := abs_nonneg C₄
  have hc7 := abs_nonneg C₇
  have hh0 : 0 < h := by rw [hR.hh]; exact div_pos hk0 (pow_pos hp0 4)
  have hpc : 4 * |CB| + 1 / κ₀ ≤ p := (Nat.le_ceil _).trans (by exact_mod_cast hp)
  have hk1 : 0 ≤ 1 / κ₀ := by positivity
  have hκp : 1 ≤ p * κ₀ := by
    have : 1 / κ₀ ≤ p := by linarith
    rwa [div_le_iff₀ hk0] at this
  have hCBp : 4 * |CB| ≤ p := by linarith
  have h7 : 3 * (p : ℝ) ^ 7 ≤ d := by
    have := hT.pfA_p7
    have : (0 : ℝ) ≤ p ^ 7 := by positivity
    linarith
  -- `p/h ≤ p⁶` and `p²/h ≤ p⁷`
  have hph : (p : ℝ) / h ≤ p ^ 6 := by
    rw [hR.hh, div_div_eq_mul_div, div_le_iff₀ hk0]
    linarith [mul_le_mul_of_nonneg_left hκp (pow_nonneg hp0.le 5)]
  have hp2h : (p : ℝ) ^ 2 / h ≤ p ^ 7 := by
    rw [hR.hh, div_div_eq_mul_div, div_le_iff₀ hk0]
    linarith [mul_le_mul_of_nonneg_left hκp (pow_nonneg hp0.le 6)]
  -- `|C_B| η_BL ≤ 1/2`
  have hη0 : 0 ≤ etaBL d p h :=
    add_nonneg (by positivity) (div_nonneg hp0.le (mul_nonneg hd0.le hh0.le))
  have hη : |CB| * etaBL d p h ≤ 1 / 2 := by
    have e : etaBL d p h = ((p : ℝ) ^ 4 + p / h) / d := by
      unfold etaBL
      ring
    have h4 : (p : ℝ) ^ 4 ≤ p ^ 6 := pow_le_pow_right₀ hp1 (by norm_num)
    rw [e, ← mul_div_assoc, div_le_iff₀ hd0]
    have e1 := mul_le_mul_of_nonneg_left (by linarith : (p : ℝ) ^ 4 + p / h ≤ 2 * p ^ 6) hcb
    have e2 := mul_le_mul_of_nonneg_right hCBp (by positivity : (0 : ℝ) ≤ 2 * (p : ℝ) ^ 6)
    linarith only [e1, e2, h7, pow_nonneg hp0.le 7]
  -- `0 ≤ ε_BL ≤ 1`
  have hp2h0 : 0 ≤ (p : ℝ) ^ 2 / h := div_nonneg (by positivity) hh0.le
  have hεBL0 : 0 ≤ epsBL d p h :=
    add_nonneg (mul_nonneg hϑ0 (add_nonneg (by positivity) hp2h0)) hϑ0
  have hεBL : epsBL d p h ≤ 1 := by
    unfold epsBL
    have h5 : (p : ℝ) ^ 5 ≤ p ^ 7 := pow_le_pow_right₀ hp1 (by norm_num)
    have h0 : (1 : ℝ) ≤ p ^ 7 := one_le_pow₀ hp1
    have e1 := mul_le_mul_of_nonneg_left
      (by linarith : (p : ℝ) ^ 5 + p ^ 2 / h + 1 ≤ 3 * p ^ 7) hϑ0
    have e2 := mul_le_mul_of_nonneg_left h7 hϑ0
    linarith only [e1, e2, hϑd]
  -- `E_row ≤ |C₇| + 4`
  have hgam : GamP d p * Real.sqrt (S + 1) ≤ |C₇| + 2 := by
    refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ?_
    rw [mul_pow, Real.sq_sqrt (by linarith : (0 : ℝ) ≤ S + 1)]
    have hg := hT.pfA_gam_sq
    have hS' : S ≤ |C₇| * p := hS7.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hp0.le)
    have hg2 : 0 ≤ GamP d p ^ 2 := sq_nonneg _
    have hg1 : GamP d p ^ 2 * p ≤ 3 := by
      have := mul_le_mul_of_nonneg_left (by nlinarith : (p : ℝ) ≤ p ^ 2) hg2
      linarith only [this, hg]
    have hg0 : GamP d p ^ 2 ≤ 3 := by
      have := mul_le_mul_of_nonneg_left hp1 hg2
      linarith only [this, hg1]
    linarith only [mul_le_mul_of_nonneg_left hS' hg2, mul_le_mul_of_nonneg_left hg1 hc7,
      sq_nonneg |C₇|, hg0, hc7]
  have hErow : ErowP d p S ≤ |C₇| + 4 := by
    unfold ErowP
    linarith only [hgam, hu1, hϑ1]
  have hE0 := pfA_erow_nonneg d p S
  have hGtR : Gt ≤ R + |C₉| * (|C₇| + 4) := by
    obtain ⟨h1, -⟩ := abs_le.mp habs
    have h2 := mul_le_mul_of_nonneg_right (le_abs_self C₉) hE0
    have h3 := mul_le_mul_of_nonneg_left hErow hc9
    linarith only [h1, h2, h3]
  have hR' : R ≤ 2 * |C₄| * p := by
    have h1 := mul_le_mul_of_nonneg_right (le_abs_self C₄)
      (by linarith : (0 : ℝ) ≤ p + (p : ℝ) ^ 5 / d)
    have h2 := mul_le_mul_of_nonneg_left (by linarith : p + (p : ℝ) ^ 5 / d ≤ 2 * p) hc4
    linarith only [hR4, h1, h2]
  have hCp0 : 0 ≤ (4 * |C₄| + 2 * |C₉| * (|C₇| + 4) + 2 * |CB| + 1) * p := by positivity
  rcases le_or_gt Qb 0 with hq | hq
  · linarith
  · have h1 : CB * etaBL d p h ≤ |CB| * etaBL d p h :=
      mul_le_mul_of_nonneg_right (le_abs_self _) hη0
    have h2 : 1 / 2 * Qb ≤ (1 - CB * etaBL d p h) * Qb :=
      mul_le_mul_of_nonneg_right (by linarith) hq.le
    have h3 : CB * epsBL d p h ≤ |CB| := by
      have := mul_le_mul_of_nonneg_right (le_abs_self CB) hεBL0
      have := mul_le_mul_of_nonneg_left hεBL hcb
      linarith
    have g1 := mul_nonneg (mul_nonneg hc9 (by linarith : (0 : ℝ) ≤ |C₇| + 4))
      (sub_nonneg.mpr hp1)
    have g2 := mul_nonneg hcb (sub_nonneg.mpr hp1)
    linarith only [h2, hB1, h3, hGtR, hR', g1, g2, hp0]

/-! ### D10 -/

/-- **R-D10**, copy of `d10_real` with the extra hypothesis `0 ≤ CB` (`d10_real` is false for
`CB < 0`: `CHECK_CONTACT.md` §R6, `scripts/tight/check_contact_d10.py`). -/
theorem d10_real_pf (CB C₉ C₉b Cc : ℝ) (hCB : 0 ≤ CB) : ∃ C : ℝ, 0 < C ∧
    ∀ (d p : ℕ) (h : ℝ), TRegime d p →
    0 < h → ∀ S R Gt Qb Qf : ℝ,
      (1 - CB * etaBL d p h) * Qb - CB * epsBL d p h ≤ Gt →
      |R - Gt| ≤ C₉ * ErowP d p S →
      Qb ≤ C₉b * p →
      Qf ≤ Qb + Cc * p / (d * h * Real.sqrt h) →
      Qf - C * Err10 d p h S ≤ R := by
  have hcc := abs_nonneg Cc
  have hc9 := abs_nonneg C₉
  have hcbb := mul_nonneg hCB (abs_nonneg C₉b)
  refine ⟨|Cc| + CB * |C₉b| + CB + |C₉| + 1, by linarith, fun d p h hR hh S R Gt Qb Qf hB1
    habs hQb hQf => ?_⟩
  have hp0 := hR.pfA_p_pos
  have hd0 := hR.pfA_d_pos
  have hsh : 0 < Real.sqrt h := Real.sqrt_pos.mpr hh
  have hϑ0 := pfA_vth_nonneg d
  have e1 := pfA_erow_nonneg d p S
  have e2 : 0 ≤ (p : ℝ) ^ 5 / d := by positivity
  have e3 : 0 ≤ (p : ℝ) ^ 2 / (d * h) := div_nonneg (by positivity) (mul_nonneg hd0.le hh.le)
  have e4 : 0 ≤ (p : ℝ) / (d * h * Real.sqrt h) :=
    div_nonneg hp0.le (mul_nonneg (mul_nonneg hd0.le hh.le) hsh.le)
  have e5 : 0 ≤ epsBL d p h :=
    add_nonneg (mul_nonneg hϑ0 (add_nonneg (by positivity) (div_nonneg (by positivity) hh.le)))
      hϑ0
  have hηp : etaBL d p h * p = (p : ℝ) ^ 5 / d + (p : ℝ) ^ 2 / (d * h) := by
    unfold etaBL
    ring
  have hη0 : 0 ≤ etaBL d p h :=
    add_nonneg (by positivity) (div_nonneg hp0.le (mul_nonneg hd0.le hh.le))
  have hQb' : Qb ≤ |C₉b| * p := hQb.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hp0.le)
  have f3 : CB * etaBL d p h * Qb ≤ CB * |C₉b| * ((p : ℝ) ^ 5 / d + (p : ℝ) ^ 2 / (d * h)) := by
    have := mul_le_mul_of_nonneg_left hQb' (mul_nonneg hCB hη0)
    rw [← hηp]
    linarith
  have f2 : C₉ * ErowP d p S ≤ |C₉| * ErowP d p S :=
    mul_le_mul_of_nonneg_right (le_abs_self _) e1
  have f4 : Cc * p / (d * h * Real.sqrt h) ≤ |Cc| * ((p : ℝ) / (d * h * Real.sqrt h)) := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_right (le_abs_self _) e4
  obtain ⟨hRG1, -⟩ := abs_le.mp habs
  unfold Err10
  have g1 := mul_le_mul_of_nonneg_left (show ErowP d p S ≤ ErowP d p S + (p : ℝ) ^ 5 / d +
    (p : ℝ) ^ 2 / (d * h) + (p : ℝ) / (d * h * Real.sqrt h) + epsBL d p h by linarith) hc9
  have g2 := mul_le_mul_of_nonneg_left (show (p : ℝ) ^ 5 / d + (p : ℝ) ^ 2 / (d * h) ≤
    ErowP d p S + (p : ℝ) ^ 5 / d + (p : ℝ) ^ 2 / (d * h) + (p : ℝ) / (d * h * Real.sqrt h) +
      epsBL d p h by linarith) hcbb
  have g3 := mul_le_mul_of_nonneg_left (show (p : ℝ) / (d * h * Real.sqrt h) ≤
    ErowP d p S + (p : ℝ) ^ 5 / d + (p : ℝ) ^ 2 / (d * h) + (p : ℝ) / (d * h * Real.sqrt h) +
      epsBL d p h by linarith) hcc
  have g4 := mul_le_mul_of_nonneg_left (show epsBL d p h ≤
    ErowP d p S + (p : ℝ) ^ 5 / d + (p : ℝ) ^ 2 / (d * h) + (p : ℝ) / (d * h * Real.sqrt h) +
      epsBL d p h by linarith) hCB
  linarith

/-! ### E-c -/

/-- **R-Ec**, verbatim copy of `qP_le_real` (sketch: `CHECK_CONTACT.md` §R7). -/
theorem qP_le_real_pf (C₉b Cc : ℝ) : ∃ C : ℝ, 0 < C ∧ ∀ κ₀ : ℝ, 0 < κ₀ → κ₀ ≤ 1 →
    ∃ P₀ : ℕ, ∀ (d p : ℕ) (h : ℝ), Reg κ₀ d p h → P₀ ≤ p →
    ∀ Qb qp qm : ℝ, 0 ≤ qm →
      LdP d p * (((p : ℝ) - 1) * qp + p * qm) ≤ Qb + Cc * p / (d * h * Real.sqrt h) →
      Qb ≤ C₉b * p →
      qp ≤ C := by
  refine ⟨|C₉b| + 1, by positivity, fun κ₀ hk0 _ =>
    ⟨⌈(|Cc| + 1) / κ₀⌉₊, fun d p h hR hp => ?_⟩⟩
  intro Qb qp qm hqm hL hQb
  have hT := hR.treg
  have hp0 := hT.pfA_p_pos
  have hp2 : (2 : ℝ) ≤ p := le_trans (by norm_num) hT.pfA_p_ge
  have hd0 := hT.pfA_d_pos
  have hh0 : 0 < h := by rw [hR.hh]; exact div_pos hk0 (pow_pos hp0 4)
  have hhp : h * (p : ℝ) ^ 4 = κ₀ := by
    rw [hR.hh]
    exact div_mul_cancel₀ _ (pow_ne_zero 4 hp0.ne')
  have hpc : (|Cc| + 1) / κ₀ ≤ p := (Nat.le_ceil _).trans (by exact_mod_cast hp)
  have hκp : |Cc| + 1 ≤ p * κ₀ := by rwa [div_le_iff₀ hk0] at hpc
  have hsh : 0 < Real.sqrt h := Real.sqrt_pos.mpr hh0
  have hD : 0 < d * h * Real.sqrt h := mul_pos (mul_pos hd0 hh0) hsh
  have hcc := abs_nonneg Cc
  -- `|Cc| p ≤ d h √h`
  have hc3 : |Cc| ^ 2 ≤ (p * κ₀) ^ 3 := by
    have h1 : (|Cc| + 1) ^ 3 ≤ (p * κ₀) ^ 3 := pow_le_pow_left₀ (by positivity) hκp 3
    nlinarith [pow_nonneg hcc 3, sq_nonneg |Cc|]
  have hkey : (|Cc| * p) ^ 2 * (p : ℝ) ^ 12 ≤ (d * h * Real.sqrt h) ^ 2 * (p : ℝ) ^ 12 := by
    have e1 : (d * h * Real.sqrt h) ^ 2 * (p : ℝ) ^ 12 = (d : ℝ) ^ 2 * (h * (p : ℝ) ^ 4) ^ 3 := by
      rw [mul_pow, Real.sq_sqrt hh0.le]
      ring
    rw [e1, hhp]
    calc (|Cc| * p) ^ 2 * (p : ℝ) ^ 12 = |Cc| ^ 2 * (p : ℝ) ^ 14 := by ring
      _ ≤ (p * κ₀) ^ 3 * (p : ℝ) ^ 14 := mul_le_mul_of_nonneg_right hc3 (by positivity)
      _ = (p : ℝ) ^ 17 * κ₀ ^ 3 := by ring
      _ ≤ (d : ℝ) ^ 2 * κ₀ ^ 3 := mul_le_mul_of_nonneg_right hT.pfA_p17 (pow_nonneg hk0.le 3)
  have hc : |Cc| * p ≤ d * h * Real.sqrt h :=
    le_of_pow_le_pow_left₀ two_ne_zero hD.le (le_of_mul_le_mul_right hkey (pow_pos hp0 12))
  have hw : Cc * p / (d * h * Real.sqrt h) ≤ 1 := by
    rw [div_le_one hD]
    exact (mul_le_mul_of_nonneg_right (le_abs_self Cc) hp0.le).trans hc
  have hLd : 4 ≤ LdP d p := by
    have := hT.pf_a_sq_ge
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < 4 * d)] at this
    unfold LdP
    linarith
  have hQb' : Qb ≤ |C₉b| * p := hQb.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hp0.le)
  have hc9 := abs_nonneg C₉b
  by_contra hq
  rw [not_le] at hq
  have hX : 0 ≤ ((p : ℝ) - 1) * qp + p * qm := by
    have h1 := mul_nonneg (by linarith : (0 : ℝ) ≤ p - 1) (by linarith : (0 : ℝ) ≤ qp)
    have h2 := mul_nonneg hp0.le hqm
    linarith
  have h4 := mul_le_mul_of_nonneg_right hLd hX
  linarith [mul_pos (by linarith : (0 : ℝ) < p - 1) (by linarith : 0 < qp - (|C₉b| + 1)),
    mul_nonneg hc9 (by linarith : (0 : ℝ) ≤ p - 2), mul_nonneg hp0.le hqm]

/-! ### D15 -/

/-- **R-D15**, verbatim copy of `d15_real` (sketch: `CHECK_CONTACT.md` §R12). -/
theorem d15_real_pf (C₇ : ℝ) : ∃ C : ℝ, 0 < C ∧ ∃ P₀ : ℕ, ∀ d p : ℕ, TRegime d p → P₀ ≤ p →
    ∀ S n L Cp Dp : ℝ, 0 ≤ S → 0 ≤ n → n ≤ d → 0 ≤ Cp → Dp = 1 + L - Cp →
      Cp ≤ aOf d p ^ 2 * LbarP d p * sOf d p ^ 2 → LbarP d p - L ≤ C₇ * epsS d p →
      (rOf d p * Dp - 1) ^ 2 ≤ aOf d p ^ 2 * n * S →
      4 - C * (epsS d p + η0Of d p + 1 / (d : ℝ)) ≤ S := by
  obtain ⟨P₁, hPF⟩ := param_facts_pf
  refine ⟨11 * |C₇| + 48, by positivity, max P₁ ⌈8 * |C₇|⌉₊, fun d p hR hp => ?_⟩
  intro S n L Cp Dp hS _ hnd hCp hDp hCpb hLL hsq
  obtain ⟨hpa1, -, -, -, -, -, -, -, hrLs, hLs, hLb1, -, hs5⟩ :=
    hPF d p hR (le_of_max_le_left hp)
  have hC7 : 8 * |C₇| ≤ p := (Nat.le_ceil _).trans (by exact_mod_cast le_of_max_le_right hp)
  have hd0 := hR.pfA_d_pos
  have hr1 := hR.one_lt_rOf
  have hr2 := hR.rOf_le
  have ha0 : 0 < aOf d p ^ 2 := pow_pos hR.aOf_pos 2
  have hes0 := pfA_epsS_nonneg d p
  have hesp := hR.pfA_epsS_mul_p
  have hc7 := abs_nonneg C₇
  have hη0 := hR.η0Of_pos
  have hd1 : (0 : ℝ) ≤ 1 / d := by positivity
  have h4d : (4 : ℝ) / d = 4 * (1 / d) := by ring
  -- `r C₊ ≤ 4/d`
  have hrCp : rOf d p * Cp ≤ 4 / (d : ℝ) := by
    have h1 := mul_le_mul_of_nonneg_left hCpb (by linarith : (0 : ℝ) ≤ rOf d p)
    have h2 := mul_le_mul_of_nonneg_left hrLs ha0.le
    linarith
  have hL' : LbarP d p - |C₇| * epsS d p ≤ L := by
    have := mul_le_mul_of_nonneg_right (le_abs_self C₇) hes0
    linarith
  -- `X = L̄ - 1.01 |C₇| ε_s - 4/d ≤ r D₊ - 1`
  have hXle : LbarP d p - 101 / 100 * |C₇| * epsS d p - 4 / (d : ℝ) ≤ rOf d p * Dp - 1 := by
    rw [hDp]
    have h1 : rOf d p * (LbarP d p - |C₇| * epsS d p) ≤ rOf d p * L :=
      mul_le_mul_of_nonneg_left hL' (by linarith)
    have h2 : LbarP d p ≤ rOf d p * LbarP d p := le_mul_of_one_le_left (by linarith) hr1.le
    have h3 : rOf d p * (|C₇| * epsS d p) ≤ 101 / 100 * (|C₇| * epsS d p) :=
      mul_le_mul_of_nonneg_right hr2 (mul_nonneg hc7 hes0)
    linarith
  have hX0 : 1 / 4 ≤ LbarP d p - 101 / 100 * |C₇| * epsS d p - 4 / (d : ℝ) := by
    have h1 : 8 * (|C₇| * epsS d p) ≤ 1 := by
      have := mul_le_mul_of_nonneg_right hC7 hes0
      linarith
    have h2 : 4 / (d : ℝ) ≤ 4 / 10 ^ 6 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hR.ten_pow_six_le_d
    linarith
  have hX2 : (LbarP d p - (101 / 100 * |C₇| * epsS d p + 4 / (d : ℝ))) ^ 2 ≤
      S * (aOf d p ^ 2 * d) := by
    have h1 : (LbarP d p - (101 / 100 * |C₇| * epsS d p + 4 / (d : ℝ))) ^ 2 ≤
        (rOf d p * Dp - 1) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have h2 : aOf d p ^ 2 * n * S ≤ aOf d p ^ 2 * d * S :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnd ha0.le) hS
    linarith
  have hk : 0 < aOf d p ^ 2 * d := mul_pos ha0 hd0
  have hLk : LbarP d p = aOf d p ^ 2 * d * sOf d p ^ 2 := by unfold LbarP; ring
  have hδ0 : 0 ≤ 101 / 100 * |C₇| * epsS d p + 4 / (d : ℝ) := by positivity
  have hmain : LbarP d p * sOf d p ^ 2 -
      2 * sOf d p ^ 2 * (101 / 100 * |C₇| * epsS d p + 4 / (d : ℝ)) ≤ S := by
    refine le_of_mul_le_mul_left ?_ hk
    have e : aOf d p ^ 2 * d * (LbarP d p * sOf d p ^ 2 -
        2 * sOf d p ^ 2 * (101 / 100 * |C₇| * epsS d p + 4 / (d : ℝ))) =
        LbarP d p ^ 2 - 2 * LbarP d p * (101 / 100 * |C₇| * epsS d p + 4 / (d : ℝ)) := by
      rw [hLk]
      ring
    rw [e]
    linarith [sq_nonneg (101 / 100 * |C₇| * epsS d p + 4 / (d : ℝ))]
  have h1 := mul_le_mul_of_nonneg_right hs5 hδ0
  linarith [mul_nonneg hc7 hes0, mul_nonneg hc7 hη0.le, mul_nonneg hc7 hd1]

end BiluLinial.Tight
