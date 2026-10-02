/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecB.W1FibNonreg

/-!
# The weak loop (W1), edge fibres: the four configurations

Definitions shared by TB.W1fib-reg, TB.W1fib-nonreg and TB.W1fib-edge (`docs/tight/BP_SECB.md`):
the flipped signing `σ^e` (`fibFlip`), `g* = G⁺_ii + G⁺_jj + G⁻_ii + G⁻_jj` (`fibG`), good endpoints
(`fibGood`: `W > 0` and `64 p a g* ≤ 1`), `Yb = (a³/(√d h)) D_*^M (p³R_ij² + p)` (`fibYb`), and
`Ψ = H F_ji`, `DΨ` in the four configurations (`cfgPsi`, `cfgD`; `0`: `(+, Ω₊, u)`,
`1`: `(+, Ω₊, b₊)`, `2`: `(-, Ω₋, u)`, `3`: `(-, Ω₋, b₋)`). `w1_nonreg_cfg`:
`|Ψ| + |DΨ| ≤ 9 (D_*²/√d) D_*⁵/h` at every signing in the support (from
`SecB/W1FibNonreg.lean`).
-/

@[expose] public section

namespace BiluLinial.Tight.SecB

open Matrix

universe u

section FibEdge

variable {d p : ℕ} (ct : Contact.{u} d p)

/-- The signing flipped to `-1` on the edge `ij`. -/
def fibFlip (σ : Config ct.V) (i j : ct.V) : Config ct.V := Function.update σ s(i, j) (-1)

/-- The endpoint diagonal sum `g* = G⁺_ii + G⁺_jj + G⁻_ii + G⁻_jj`. -/
noncomputable def fibG (σ : Config ct.V) (i j : ct.V) : ℝ :=
  ct.gp σ i i + ct.gp σ j j + ct.gm σ i i + ct.gm σ j j

/-- A good small endpoint: `W(σ) ≠ 0` and `64 p a g*(σ) ≤ 1`. -/
def fibGood (i j : ct.V) (σ : Config ct.V) : Prop :=
  wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 ∧ 64 * p * aOf d p * fibG ct σ i j ≤ 1

/-- `Yb = (a³/(√d h)) D_*^M (p³ R_ij² + p)`. -/
noncomputable def fibYb (M : ℕ) (h : ℝ) (i j : ct.V) (σ : Config ct.V) : ℝ :=
  aOf d p ^ 3 / (Real.sqrt d * h) * (ct.Dstar σ ^ M * ((p : ℝ) ^ 3 * fibR ct σ i j ^ 2 + p))

/-- `Ψ = H F_ji` in configuration `k` (`0`: `(+, Ω₊, u)`, `1`: `(+, Ω₊, b₊)`, `2`: `(-, Ω₋, u)`,
`3`: `(-, Ω₋, b₋)`). -/
noncomputable def cfgPsi (h : ℝ) (k : Fin 4) (i j : ct.V) (σ : Config ct.V) : ℝ :=
  match k with
  | 0 => ct.OmP σ * maskF (ct.XP h σ) (ct.XP h σ) ct.uvec j i
  | 1 => ct.OmP σ * maskF (ct.XP h σ) (ct.XP h σ) (ct.bP h σ) j i
  | 2 => ct.OmM σ * maskF (ct.XM h σ) (ct.XP h σ) ct.uvec j i
  | 3 => ct.OmM σ * maskF (ct.XM h σ) (ct.XP h σ) (ct.bM h σ) j i

/-- `DΨ` in configuration `k`. -/
noncomputable def cfgD (h : ℝ) (k : Fin 4) (i j : ct.V) : Config ct.V → ℝ :=
  match k with
  | 0 => fibD ct 1 ct.OmP ct.dOmP (ct.XP h) (ct.XP h) (fun _ => ct.uvec) (fun _ _ _ _ => 0) i j
  | 1 => fibD ct 1 ct.OmP ct.dOmP (ct.XP h) (ct.XP h) (ct.bP h) (dbP ct h) i j
  | 2 => fibD ct (-1) ct.OmM ct.dOmM (ct.XM h) (ct.XP h) (fun _ => ct.uvec)
      (fun _ _ _ _ => 0) i j
  | 3 => fibD ct (-1) ct.OmM ct.dOmM (ct.XM h) (ct.XP h) (ct.bM h) (dbM ct h) i j

theorem fibYb_mono {M M' : ℕ} (hM : M ≤ M') {h : ℝ} (hh : 0 < h) (i j : ct.V)
    (σ : Config ct.V) :
    wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S * fibYb ct M h i j σ ≤
      wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S * fibYb ct M' h i j σ := by
  by_cases hσ : wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S = 0
  · rw [hσ, zero_mul, zero_mul]
  · have hD := w1_Dstar_ge_one ct hσ
    have ha : 0 ≤ aOf d p := by unfold aOf; positivity
    refine mul_le_mul_of_nonneg_left ?_ (wt_nonneg ct.G σ)
    unfold fibYb
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hD hM) (by positivity)

theorem wt_fibYb_nonneg (M : ℕ) {h : ℝ} (hh : 0 < h) (i j : ct.V) (σ : Config ct.V) :
    0 ≤ wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S * fibYb ct M h i j σ := by
  by_cases hσ : wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S = 0
  · rw [hσ, zero_mul]
  · have hD := w1_Dstar_ge_one ct hσ
    have ha : 0 ≤ aOf d p := by unfold aOf; positivity
    refine mul_nonneg (wt_nonneg ct.G σ) ?_
    unfold fibYb
    positivity

/-- `|Ψ| + |DΨ| ≤ 9 (D_*²/√d) D_*⁵/h` in each configuration, at a signing in the support
(`w1_nonreg_pt` with `m = D_*²/√d`). -/
theorem w1_nonreg_cfg {h : ℝ} (hh : 0 < h) (hR : TRegime d p) (ha1 : aOf d p ≤ 1)
    (hPa : (p : ℝ) * aOf d p ≤ 1) (hah : aOf d p ^ 2 ≤ h) (had : aOf d p ^ 2 * d ≤ 1)
    {τ : Config ct.V} (hτ : wt ct.G p (aOf d p) ct.yp ct.ym τ ct.S ≠ 0) {i j : ct.V}
    (hi : i ∈ ct.N) (hj : j ∈ nbhd ct.G ct.S i) (k : Fin 4) :
    |cfgPsi ct h k i j τ| + |cfgD ct h k i j τ| ≤
      9 * (ct.Dstar τ ^ 2 / Real.sqrt d * ct.Dstar τ ^ 5 / h) := by
  have hD := w1_Dstar_ge_one ct hτ
  have hiB := w1Ball_N ct hi
  have hjB := w1Ball_NN ct hi hj
  have hm : (0 : ℝ) ≤ ct.Dstar τ ^ 2 / Real.sqrt d := by positivity
  match k with
  | 0 =>
    exact w1_nonreg_pt ct hh ha1 hPa hτ hi hj 1 (by norm_num) ct.OmP (w1_OmP_nonneg ct τ)
        (w1_OmP_le ct hτ) ct.dOmP (w1_dOmP_le ct hτ hiB hjB) (ct.XP h)
        (fun k hk => w1_XP_facts ct hh hτ hk) (fun j hj k hk => w1_XP_off_le ct hh hτ hj hk)
        (fun _ => ct.uvec) hm (w1_uvec_le_m ct hτ) (fun _ _ _ _ => 0)
        (fun _ => by simp only [abs_zero]; positivity)
  | 1 =>
    exact w1_nonreg_pt ct hh ha1 hPa hτ hi hj 1 (by norm_num) ct.OmP (w1_OmP_nonneg ct τ)
        (w1_OmP_le ct hτ) ct.dOmP (w1_dOmP_le ct hτ hiB hjB) (ct.XP h)
        (fun k hk => w1_XP_facts ct hh hτ hk) (fun j hj k hk => w1_XP_off_le ct hh hτ hj hk)
        (ct.bP h) hm (w1_bP_le_m ct hh hτ hR had) (dbP ct h)
        (w1_dbP_le4 ct hh hτ ha1 hah hiB hjB)
  | 2 =>
    exact w1_nonreg_pt ct hh ha1 hPa hτ hi hj (-1) (by norm_num) ct.OmM
        (w1_OmM_nonneg ct hτ) (w1_OmM_le ct hτ) ct.dOmM (w1_dOmM_le ct hτ hiB hjB) (ct.XM h)
        (fun k hk => w1_XM_facts ct hh hτ hk) (fun j hj k hk => w1_XM_off_le ct hh hτ hj hk)
        (fun _ => ct.uvec) hm (w1_uvec_le_m ct hτ) (fun _ _ _ _ => 0)
        (fun _ => by simp only [abs_zero]; positivity)
  | 3 =>
    exact w1_nonreg_pt ct hh ha1 hPa hτ hi hj (-1) (by norm_num) ct.OmM
        (w1_OmM_nonneg ct hτ) (w1_OmM_le ct hτ) ct.dOmM (w1_dOmM_le ct hτ hiB hjB) (ct.XM h)
        (fun k hk => w1_XM_facts ct hh hτ hk) (fun j hj k hk => w1_XM_off_le ct hh hτ hj hk)
        (ct.bM h) hm (w1_bM_le_m ct hh hτ hR had) (dbM ct h)
        (w1_dbM_le4 ct hh hτ ha1 hah hiB hjB)

end FibEdge

end BiluLinial.Tight.SecB
