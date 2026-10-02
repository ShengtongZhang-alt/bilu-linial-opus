/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecB.W1FibDefs

/-!
# The weak loop (W1), edge fibres: pointwise bounds for TB.W1fib-nonreg

At a signing `τ` with `W(τ) ≠ 0`, for `i ∈ N`, `j ∼ i` and a configuration `(ε, H, X_ε, X₊, f, ∂f)`
with `0 ≤ H ≤ D_*²/4`, `|∂_ij H| ≤ a D_*³`, `|f| ≤ m` and `|∂_ij f| ≤ 4m`:
`|Ψ| + |DΨ| ≤ 9 m D_*⁵/h` (`w1_nonreg_pt`; `Ψ = H F_ji`, `DΨ = fibD`). The inputs are the
pointwise bounds of `SecB/W1Mom.lean`: `|X_kl| ≤ D_*` and row energies `≤ D_*/h` on the ball,
`|F_ji(g)| ≤ 2mD_*²/h` (`maskF_abs_le`), `|U_kl| ≤ mD_*/h` (`w1_maskU_le`), `|G_kl| ≤ D_*`
(`w1_g_off_le`). With `m = D_*²/√d` this holds in all four configurations (`w1_uvec_le_m`,
`w1_bP_le_m`, `w1_bM_le_m`, `w1_dbP_le4`, `w1_dbM_le4`, `w1_dOmP_le`, `w1_dOmM_le`).
`nonreg_absorb` turns `9 D_*⁷/(√d h)` into `9·256⁴ Yb` (`M = 11`) when `1 < 256 p a D_*` and
`p³a ≤ 1`.
-/

@[expose] public section

namespace BiluLinial.Tight.SecB

open Matrix

universe u

theorem w1_abs_mul_le {x y X Y : ℝ} (hx : |x| ≤ X) (hy : |y| ≤ Y) : |x * y| ≤ X * Y := by
  rw [abs_mul]
  exact mul_le_mul hx hy (abs_nonneg _) ((abs_nonneg _).trans hx)

/-- Scalar bookkeeping of `|Ψ| + |DΨ|`. -/
theorem fibD_real_le {a P D m h ε dH g H xe xn xnii xeii F U1 U2 Fd : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hP0 : 0 ≤ P) (hPa : P * a ≤ 1) (hD : 1 ≤ D) (hm : 0 ≤ m)
    (hh : 0 < h) (hε : |ε| ≤ 1) (hdH : |dH| ≤ a * D ^ 3) (hg : |g| ≤ 2 * D) (hH0 : 0 ≤ H)
    (hH : H ≤ D ^ 2 / 4) (hxe : |xe| ≤ D) (hxn : |xn| ≤ D) (hxnii : |xnii| ≤ D)
    (hxeii : |xeii| ≤ D) (hF : |F| ≤ 2 * m * D ^ 2 / h) (hU1 : |U1| ≤ m * D / h)
    (hU2 : |U2| ≤ m * D / h) (hFd : |Fd| ≤ 8 * m * D ^ 2 / h) :
    |H * F| + |(dH * F + 2 * P * a * g * (H * F)) +
        H * (-a * (2 * ε * xe * F + xn * F - xnii * xe * U1)) + H * Fd -
        a * (H * (xeii * xnii) * U2)| ≤ 9 * (m * D ^ 5 / h) := by
  have hD0 : 0 ≤ D := by linarith
  have hQ : 0 ≤ m * D ^ 5 / h := div_nonneg (mul_nonneg hm (pow_nonneg hD0 5)) hh.le
  have hH' : |H| ≤ D ^ 2 / 4 := by rw [abs_of_nonneg hH0]; exact hH
  have h45 : 2 * m * D ^ 4 / h ≤ 2 * (m * D ^ 5 / h) := by
    have h1 : D ^ 4 ≤ D ^ 5 := pow_le_pow_right₀ hD (by norm_num)
    have h2 : 2 * m * D ^ 4 / h ≤ 2 * m * D ^ 5 / h := by gcongr
    linarith [show 2 * m * D ^ 5 / h = 2 * (m * D ^ 5 / h) by ring]
  have b0 : |H * F| ≤ 1 / 2 * (m * D ^ 5 / h) := by
    have h1 := w1_abs_mul_le hH' hF
    have e : D ^ 2 / 4 * (2 * m * D ^ 2 / h) = (2 * m * D ^ 4 / h) / 4 := by ring
    linarith
  have b1 : |dH * F| ≤ 2 * (m * D ^ 5 / h) := by
    have h1 := w1_abs_mul_le hdH hF
    have e : a * D ^ 3 * (2 * m * D ^ 2 / h) = a * (2 * (m * D ^ 5 / h)) := by ring
    have h2 : a * (2 * (m * D ^ 5 / h)) ≤ 2 * (m * D ^ 5 / h) :=
      mul_le_of_le_one_left (by linarith) ha1
    linarith
  have b2 : |2 * P * a * g * (H * F)| ≤ 2 * (m * D ^ 5 / h) := by
    have hpa : |2 * P * a| ≤ 2 := by
      rw [abs_of_nonneg (mul_nonneg (mul_nonneg (by norm_num) hP0) ha)]
      linarith
    have h1 := w1_abs_mul_le (w1_abs_mul_le hpa hg) (w1_abs_mul_le hH' hF)
    have e : 2 * (2 * D) * (D ^ 2 / 4 * (2 * m * D ^ 2 / h)) = 2 * (m * D ^ 5 / h) := by ring
    linarith
  have b3 : |H * (-a * (2 * ε * xe * F + xn * F - xnii * xe * U1))| ≤
      7 / 4 * (m * D ^ 5 / h) := by
    have hna : |-a| ≤ 1 := by rw [abs_neg, abs_of_nonneg ha]; exact ha1
    have h2 : |(2 : ℝ)| ≤ 2 := by norm_num
    have t1 := w1_abs_mul_le (w1_abs_mul_le (w1_abs_mul_le h2 hε) hxe) hF
    have t2 := w1_abs_mul_le hxn hF
    have t3 := w1_abs_mul_le (w1_abs_mul_le hxnii hxe) hU1
    have hA : |2 * ε * xe * F + xn * F - xnii * xe * U1| ≤
        2 * 1 * D * (2 * m * D ^ 2 / h) + D * (2 * m * D ^ 2 / h) + D * D * (m * D / h) := by
      have s1 := abs_sub (2 * ε * xe * F + xn * F) (xnii * xe * U1)
      have s2 := abs_add_le (2 * ε * xe * F) (xn * F)
      linarith
    have h1 := w1_abs_mul_le hH' (w1_abs_mul_le hna hA)
    have e : D ^ 2 / 4 * (1 * (2 * 1 * D * (2 * m * D ^ 2 / h) + D * (2 * m * D ^ 2 / h) +
        D * D * (m * D / h))) = 7 / 4 * (m * D ^ 5 / h) := by ring
    linarith
  have b4 : |H * Fd| ≤ 2 * (m * D ^ 5 / h) := by
    have h1 := w1_abs_mul_le hH' hFd
    have e : D ^ 2 / 4 * (8 * m * D ^ 2 / h) = 2 * m * D ^ 4 / h := by ring
    linarith
  have b5 : |a * (H * (xeii * xnii) * U2)| ≤ 1 / 4 * (m * D ^ 5 / h) := by
    have ha' : |a| ≤ 1 := by rw [abs_of_nonneg ha]; exact ha1
    have h1 := w1_abs_mul_le ha'
      (w1_abs_mul_le (w1_abs_mul_le hH' (w1_abs_mul_le hxeii hxnii)) hU2)
    have e : 1 * (D ^ 2 / 4 * (D * D) * (m * D / h)) = 1 / 4 * (m * D ^ 5 / h) := by ring
    linarith
  have s1 := abs_sub ((dH * F + 2 * P * a * g * (H * F)) +
      H * (-a * (2 * ε * xe * F + xn * F - xnii * xe * U1)) + H * Fd)
    (a * (H * (xeii * xnii) * U2))
  have s2 := abs_add_le ((dH * F + 2 * P * a * g * (H * F)) +
      H * (-a * (2 * ε * xe * F + xn * F - xnii * xe * U1))) (H * Fd)
  have s3 := abs_add_le (dH * F + 2 * P * a * g * (H * F))
    (H * (-a * (2 * ε * xe * F + xn * F - xnii * xe * U1)))
  have s4 := abs_add_le (dH * F) (2 * P * a * g * (H * F))
  linarith

/-- `|U_ji| ≤ mD/h` for `U = Xe D_g Xn`, `|g| ≤ m`, row energies `≤ D/h`. -/
theorem w1_maskU_le {V : Type*} [Fintype V] [DecidableEq V] {h : ℝ}
    {Xe Xn : Matrix V V ℝ} (hXn : ∀ k l, Xn k l = Xn l k) {g : V → ℝ} {m D : ℝ} (hm : 0 ≤ m)
    (hg : ∀ k, |g k| ≤ m) {j i : V} (hrj : ∑ k, Xe j k ^ 2 ≤ D / h)
    (hri : ∑ k, Xn i k ^ 2 ≤ D / h) :
    |(Xe * diagonal g * Xn) j i| ≤ m * D / h := by
  have u := two_abs_maskU_le (Xe := Xe) hXn hm hg j i
  have h1 : m * (∑ k, Xe j k ^ 2 + ∑ k, Xn i k ^ 2) ≤ m * (D / h + D / h) :=
    mul_le_mul_of_nonneg_left (add_le_add hrj hri) hm
  have e : m * (D / h + D / h) = 2 * (m * D / h) := by ring
  linarith

/-- `9 D⁷/(s h) ≤ 9·256⁴ (a³/(s h)) D¹¹ (P³R² + P)` when `1 < 256 P a D` and `P³ a ≤ 1`. -/
theorem nonreg_absorb {a P D s h R : ℝ} (ha : 0 ≤ a) (hP : 0 ≤ P) (hD : 1 ≤ D) (hs : 0 < s)
    (hh : 0 < h) (hPa : P ^ 3 * a ≤ 1) (hx : 1 < 256 * P * a * D) :
    9 * (D ^ 2 / s * D ^ 5 / h) ≤
      9 * 256 ^ 4 * (a ^ 3 / (s * h) * (D ^ 11 * (P ^ 3 * R ^ 2 + P))) := by
  have hD0 : 0 ≤ D := by linarith
  have hD7 : D ^ 7 ≤ 256 ^ 4 * (a ^ 3 * (D ^ 11 * (P ^ 3 * R ^ 2 + P))) := by
    have hy4 : 1 ≤ (256 * P * a * D) ^ 4 := one_le_pow₀ hx.le
    have h0 : 0 ≤ D ^ 7 := pow_nonneg hD0 7
    have h1 : D ^ 7 ≤ (256 * P * a * D) ^ 4 * D ^ 7 := le_mul_of_one_le_left h0 hy4
    have e : (256 * P * a * D) ^ 4 * D ^ 7 = 256 ^ 4 * (a ^ 3 * P * D ^ 11) * (P ^ 3 * a) := by
      ring
    have hA : 0 ≤ 256 ^ 4 * (a ^ 3 * P * D ^ 11) :=
      mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg (pow_nonneg ha 3) hP) (pow_nonneg hD0 11))
    have h2 : 256 ^ 4 * (a ^ 3 * P * D ^ 11) * (P ^ 3 * a) ≤ 256 ^ 4 * (a ^ 3 * P * D ^ 11) :=
      mul_le_of_le_one_right hA hPa
    have hPR : P ≤ P ^ 3 * R ^ 2 + P := by
      have := mul_nonneg (pow_nonneg hP 3) (sq_nonneg R)
      linarith
    have h3 : a ^ 3 * P * D ^ 11 ≤ a ^ 3 * (D ^ 11 * (P ^ 3 * R ^ 2 + P)) := by
      have e2 : a ^ 3 * P * D ^ 11 = a ^ 3 * (D ^ 11 * P) := by ring
      rw [e2]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hPR (pow_nonneg hD0 11))
        (pow_nonneg ha 3)
    have h4 := mul_le_mul_of_nonneg_left h3 (by norm_num : (0 : ℝ) ≤ 256 ^ 4)
    linarith
  have e1 : 9 * (D ^ 2 / s * D ^ 5 / h) = 9 / (s * h) * D ^ 7 := by
    field_simp
  have e2 : 9 * 256 ^ 4 * (a ^ 3 / (s * h) * (D ^ 11 * (P ^ 3 * R ^ 2 + P))) =
      9 / (s * h) * (256 ^ 4 * (a ^ 3 * (D ^ 11 * (P ^ 3 * R ^ 2 + P)))) := by
    field_simp
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_left hD7 (div_nonneg (by norm_num) (mul_pos hs hh).le)

section Pt

variable {d p : ℕ} (ct : Contact.{u} d p)

theorem w1_g_off_le {σ : Config ct.V} (hσ : wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0)
    {j k : ct.V} (hj : j ∈ w1Ball ct) (hk : k ∈ w1Ball ct) :
    |ct.gp σ j k| ≤ ct.Dstar σ ∧ |ct.gm σ j k| ≤ ct.Dstar σ := by
  obtain ⟨hpP, hpM⟩ := posDef_of_wt_ne_zero ct.G hσ
  have h1 := greenP_sq_le ct.G hpP (fun k => (ct.ctx.hyp k).1) j k
  have h2 := greenP_sq_le ct.G hpM (fun k => (ct.ctx.hym k).1) j k
  obtain ⟨a1, a2⟩ := w1_diag_le_Dstar ct hj σ
  obtain ⟨b1, b2⟩ := w1_diag_le_Dstar ct hk σ
  obtain ⟨c1, c2⟩ := w1_gp_nonneg ct hσ j
  obtain ⟨e1, e2⟩ := w1_gp_nonneg ct hσ k
  exact ⟨abs_le_of_sq_le_mul c1 (by linarith) e1 (by linarith) h1,
    abs_le_of_sq_le_mul c2 (by linarith) e2 (by linarith) h2⟩

/-- `|∂_ij Ω₊| ≤ a D_*³`. -/
theorem w1_dOmP_le {σ : Config ct.V} (hσ : wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0)
    {i j : ct.V} (hi : i ∈ w1Ball ct) (hj : j ∈ w1Ball ct) :
    |ct.dOmP σ i j| ≤ aOf d p * ct.Dstar σ ^ 3 := by
  have ha : 0 ≤ aOf d p := by unfold aOf; positivity
  have h1 := (w1_g_off_le ct hσ (w1Ball_v ct) (w1Ball_v ct)).1
  have h2 := (w1_g_off_le ct hσ (w1Ball_v ct) hi).1
  have h3 := (w1_g_off_le ct hσ (w1Ball_v ct) hj).1
  have ha' : |-(aOf d p)| ≤ aOf d p := by rw [abs_neg, abs_of_nonneg ha]
  have := w1_abs_mul_le (w1_abs_mul_le (w1_abs_mul_le ha' h1) h2) h3
  unfold Contact.dOmP
  calc _ ≤ _ := this
    _ = _ := by ring

/-- `|∂_ij Ω₋| ≤ a D_*³`. -/
theorem w1_dOmM_le {σ : Config ct.V} (hσ : wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0)
    {i j : ct.V} (hi : i ∈ w1Ball ct) (hj : j ∈ w1Ball ct) :
    |ct.dOmM σ i j| ≤ aOf d p * ct.Dstar σ ^ 3 := by
  have ha : 0 ≤ aOf d p := by unfold aOf; positivity
  obtain ⟨p1, m1⟩ := w1_g_off_le ct hσ (w1Ball_v ct) (w1Ball_v ct)
  obtain ⟨p2, m2⟩ := w1_g_off_le ct hσ (w1Ball_v ct) hi
  obtain ⟨p3, m3⟩ := w1_g_off_le ct hσ (w1Ball_v ct) hj
  have ha2 : |aOf d p / 2| ≤ aOf d p / 2 := le_of_eq (abs_of_nonneg (by positivity))
  have t1 := w1_abs_mul_le (w1_abs_mul_le p1 m2) m3
  have t2 := w1_abs_mul_le (w1_abs_mul_le p2 p3) m1
  have hs := (abs_sub _ _).trans (add_le_add t1 t2)
  have := w1_abs_mul_le ha2 hs
  unfold Contact.dOmM
  calc _ ≤ _ := this
    _ = _ := by ring

theorem w1_uvec_le_m {σ : Config ct.V} (hσ : wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0)
    (k : ct.V) : |ct.uvec k| ≤ ct.Dstar σ ^ 2 / Real.sqrt d := by
  have hD := w1_Dstar_ge_one ct hσ
  refine (w1_uvec_abs_le ct k).trans ?_
  exact div_le_div_of_nonneg_right (by nlinarith) (Real.sqrt_nonneg _)

theorem w1_bP_le_m {h : ℝ} (hh : 0 < h) {σ : Config ct.V}
    (hσ : wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0) (hR : TRegime d p)
    (had : aOf d p ^ 2 * d ≤ 1) (k : ct.V) : |ct.bP h σ k| ≤ ct.Dstar σ ^ 2 / Real.sqrt d := by
  refine (w1_bP_abs_le ct hh hσ hR k).trans ?_
  exact div_le_div_of_nonneg_right (mul_le_of_le_one_left (sq_nonneg _) had) (Real.sqrt_nonneg _)

theorem w1_bM_le_m {h : ℝ} (hh : 0 < h) {σ : Config ct.V}
    (hσ : wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0) (hR : TRegime d p)
    (had : aOf d p ^ 2 * d ≤ 1) (k : ct.V) : |ct.bM h σ k| ≤ ct.Dstar σ ^ 2 / Real.sqrt d := by
  refine (w1_bM_abs_le ct hh hσ hR k).trans ?_
  exact div_le_div_of_nonneg_right (mul_le_of_le_one_left (sq_nonneg _) had) (Real.sqrt_nonneg _)

theorem w1_a3_div_le {h : ℝ} (hh : 0 < h) (ha1 : aOf d p ≤ 1) (hah : aOf d p ^ 2 ≤ h) :
    aOf d p ^ 3 / h ≤ 1 := by
  have ha : 0 ≤ aOf d p := by unfold aOf; positivity
  rw [div_le_one hh]
  calc aOf d p ^ 3 = aOf d p * aOf d p ^ 2 := by ring
    _ ≤ 1 * aOf d p ^ 2 := mul_le_mul_of_nonneg_right ha1 (sq_nonneg _)
    _ ≤ h := by linarith

/-- `|∂_ij b₊| ≤ 4 D_*²/√d` (from `|∂_ij b₊| ≤ 2a³D_*(r_i + r_j)/√d`, `r ≤ D_*/h`, `a³ ≤ h`). -/
theorem w1_dbP_le4 {h : ℝ} (hh : 0 < h) {σ : Config ct.V}
    (hσ : wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0) (ha1 : aOf d p ≤ 1)
    (hah : aOf d p ^ 2 ≤ h) {i j : ct.V} (hi : i ∈ w1Ball ct) (hj : j ∈ w1Ball ct) (k : ct.V) :
    |dbP ct h σ i j k| ≤ 4 * (ct.Dstar σ ^ 2 / Real.sqrt d) := by
  have h1 := w1_dbP_abs_le ct hh hσ i j k
  rw [mul_self_diag_eq (w1_XP_symm ct h σ), mul_self_diag_eq (w1_XP_symm ct h σ)] at h1
  obtain ⟨-, -, ri⟩ := w1_XP_facts ct hh hσ hi
  obtain ⟨-, -, rj⟩ := w1_XP_facts ct hh hσ hj
  have hD := w1_Dstar_ge_one ct hσ
  have ha : 0 ≤ aOf d p := by unfold aOf; positivity
  have ha3 := w1_a3_div_le hh ha1 hah
  calc |dbP ct h σ i j k|
      ≤ 2 * aOf d p ^ 3 * ct.Dstar σ * (∑ l, ct.XP h σ i l ^ 2 + ∑ l, ct.XP h σ j l ^ 2) /
          Real.sqrt d := h1
    _ ≤ 2 * aOf d p ^ 3 * ct.Dstar σ * (2 * (ct.Dstar σ / h)) / Real.sqrt d := by
        gcongr
        linarith
    _ = 4 * ct.Dstar σ ^ 2 * (aOf d p ^ 3 / h) / Real.sqrt d := by ring
    _ ≤ 4 * ct.Dstar σ ^ 2 * 1 / Real.sqrt d := by gcongr
    _ = 4 * (ct.Dstar σ ^ 2 / Real.sqrt d) := by ring

/-- `|∂_ij b₋| ≤ 4 D_*²/√d`. -/
theorem w1_dbM_le4 {h : ℝ} (hh : 0 < h) {σ : Config ct.V}
    (hσ : wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0) (ha1 : aOf d p ≤ 1)
    (hah : aOf d p ^ 2 ≤ h) {i j : ct.V} (hi : i ∈ w1Ball ct) (hj : j ∈ w1Ball ct) (k : ct.V) :
    |dbM ct h σ i j k| ≤ 4 * (ct.Dstar σ ^ 2 / Real.sqrt d) := by
  have h1 := w1_dbM_abs_le ct hh hσ i j k
  rw [mul_self_diag_eq (w1_XP_symm ct h σ), mul_self_diag_eq (w1_XP_symm ct h σ),
    mul_self_diag_eq (w1_XM_symm ct h σ), mul_self_diag_eq (w1_XM_symm ct h σ)] at h1
  obtain ⟨-, -, ri⟩ := w1_XP_facts ct hh hσ hi
  obtain ⟨-, -, rj⟩ := w1_XP_facts ct hh hσ hj
  obtain ⟨-, -, si⟩ := w1_XM_facts ct hh hσ hi
  obtain ⟨-, -, sj⟩ := w1_XM_facts ct hh hσ hj
  have hD := w1_Dstar_ge_one ct hσ
  have ha : 0 ≤ aOf d p := by unfold aOf; positivity
  have ha3 := w1_a3_div_le hh ha1 hah
  calc |dbM ct h σ i j k|
      ≤ aOf d p ^ 3 * ct.Dstar σ * (∑ l, ct.XM h σ i l ^ 2 + ∑ l, ct.XM h σ j l ^ 2 +
          ∑ l, ct.XP h σ i l ^ 2 + ∑ l, ct.XP h σ j l ^ 2) / Real.sqrt d := h1
    _ ≤ aOf d p ^ 3 * ct.Dstar σ * (4 * (ct.Dstar σ / h)) / Real.sqrt d := by
        gcongr
        linarith
    _ = 4 * ct.Dstar σ ^ 2 * (aOf d p ^ 3 / h) / Real.sqrt d := by ring
    _ ≤ 4 * ct.Dstar σ ^ 2 * 1 / Real.sqrt d := by gcongr
    _ = 4 * (ct.Dstar σ ^ 2 / Real.sqrt d) := by ring

/-- **Pointwise bound** at a signing in the support, for a configuration `(ε, H, X_ε, X₊, f, ∂f)`:
`|Ψ| + |DΨ| ≤ 9 m D_*⁵/h`. -/
theorem w1_nonreg_pt {h : ℝ} (hh : 0 < h) (ha1 : aOf d p ≤ 1) (hPa : (p : ℝ) * aOf d p ≤ 1)
    {τ : Config ct.V} (hτ : wt ct.G p (aOf d p) ct.yp ct.ym τ ct.S ≠ 0) {i j : ct.V}
    (hi : i ∈ ct.N) (hj : j ∈ nbhd ct.G ct.S i) (ε : ℝ) (hε : |ε| ≤ 1) (H : Config ct.V → ℝ)
    (hH0 : 0 ≤ H τ) (hHD : H τ ≤ ct.Dstar τ ^ 2 / 4) (dH : Config ct.V → ct.V → ct.V → ℝ)
    (hdH : |dH τ i j| ≤ aOf d p * ct.Dstar τ ^ 3) (Xe : Config ct.V → Matrix ct.V ct.V ℝ)
    (hfE : ∀ k ∈ w1Ball ct, 0 ≤ Xe τ k k ∧ Xe τ k k ≤ ct.Dstar τ ∧
      ∑ l, Xe τ k l ^ 2 ≤ ct.Dstar τ / h)
    (hoff : ∀ j ∈ w1Ball ct, ∀ k ∈ w1Ball ct, |Xe τ j k| ≤ ct.Dstar τ)
    (f : Config ct.V → ct.V → ℝ) {m : ℝ} (hm : 0 ≤ m) (hf : ∀ k, |f τ k| ≤ m)
    (df : Config ct.V → ct.V → ct.V → ct.V → ℝ) (hdf : ∀ k, |df τ i j k| ≤ 4 * m) :
    |H τ * maskF (Xe τ) (ct.XP h τ) (f τ) j i| +
      |fibD ct ε H dH Xe (ct.XP h) f df i j τ| ≤ 9 * (m * ct.Dstar τ ^ 5 / h) := by
  have hD := w1_Dstar_ge_one ct hτ
  have ha : 0 ≤ aOf d p := by unfold aOf; positivity
  have hiB := w1Ball_N ct hi
  have hjB := w1Ball_NN ct hi hj
  obtain ⟨e1, e2, e3⟩ := hfE i hiB
  obtain ⟨-, -, f3⟩ := hfE j hjB
  obtain ⟨n1, n2, n3⟩ := w1_XP_facts ct hh hτ hiB
  obtain ⟨-, -, n3j⟩ := w1_XP_facts ct hh hτ hjB
  have hXn := w1_XP_symm ct h τ
  have hF := maskF_abs_le hXn hm hf hh e1 e2 (hoff j hjB i hiB) f3 e3 n3
  have hFd := maskF_abs_le hXn (by linarith : (0 : ℝ) ≤ 4 * m) hdf hh e1 e2 (hoff j hjB i hiB)
    f3 e3 n3
  have hU1 := w1_maskU_le hXn hm hf e3 n3j
  have hU2 := w1_maskU_le hXn hm hf f3 n3j
  have hg : |ct.gp τ i j - ct.gm τ i j| ≤ 2 * ct.Dstar τ := by
    obtain ⟨g1, g2⟩ := w1_g_off_le ct hτ hiB hjB
    have := abs_sub (ct.gp τ i j) (ct.gm τ i j)
    linarith
  have hxe := hoff i hiB j hjB
  have hxn := w1_XP_off_le ct hh hτ hiB hjB
  have hxnii : |ct.XP h τ i i| ≤ ct.Dstar τ := by rw [abs_of_nonneg n1]; exact n2
  have hxeii : |Xe τ i i| ≤ ct.Dstar τ := by rw [abs_of_nonneg e1]; exact e2
  unfold fibD
  exact fibD_real_le ha ha1 (Nat.cast_nonneg p) hPa hD hm hh hε hdH hg hH0 hHD hxe hxn hxnii
    hxeii hF hU1 hU2 (le_of_le_of_eq hFd (by ring))

end Pt

end BiluLinial.Tight.SecB
