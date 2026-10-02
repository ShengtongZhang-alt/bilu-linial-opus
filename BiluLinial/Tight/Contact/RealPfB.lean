/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.Contact.RealParams

/-!
# Proofs of the algebraic and ledger leaves of the contact estimate

Verbatim copies (suffix `_pf`) of `fs7_real`, `jr_real`, `rc3_young_real`, `d12_real`,
`final_assembly_real`, `ledger_real` and `ledger_choice` of `Tight/Contact/Real.lean`, with
proofs. Sketches and witnesses: `docs/tight/CHECK_CONTACT.md` §R8–R11 and §R13–R15. `EcF_pf` is a
copy of the definition `EcF` of `Real.lean`.
-/

@[expose] public section

namespace BiluLinial.Tight

open Real

/-! ### Generic real helpers -/

/-- `√(x + y) ≤ √x + √y`. -/
theorem sqrt_add_le_pf {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  rw [Real.sqrt_le_left (by positivity)]
  linarith [Real.sq_sqrt hx, Real.sq_sqrt hy,
    mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)]

/-- `1/(1+x)` is decreasing and `1`-Lipschitz on `[0, ∞)`. -/
theorem inv_one_add_lip_pf {x y δ : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hδ : 0 ≤ δ)
    (hyx : y ≤ x + δ) : 1 / (1 + x) - δ ≤ 1 / (1 + y) := by
  have h1 : 0 < 1 + x := by linarith
  have h2 : 0 < 1 + y := by linarith
  have key : 1 / (1 + x) - 1 / (1 + y) = (y - x) / ((1 + x) * (1 + y)) := by
    rw [div_sub_div _ _ h1.ne' h2.ne']
    ring
  have : (y - x) / ((1 + x) * (1 + y)) ≤ δ := by
    rw [div_le_iff₀ (by positivity)]
    linarith [mul_nonneg hδ hx, mul_nonneg hδ hy, mul_nonneg (mul_nonneg hδ hx) hy]
  linarith

/-! ### R-choice -/

theorem ledger_choice_pf (Ccrit : ℝ) (hC : 0 < Ccrit) : ∃ c₀ κ₀ : ℝ, 0 < c₀ ∧ c₀ ≤ 1 ∧ 0 < κ₀ ∧
    κ₀ ≤ 1 ∧
    Ccrit * (Real.sqrt κ₀ + c₀ ^ ((17 : ℝ) / 3) + κ₀⁻¹ ^ 2 * c₀ ^ ((34 : ℝ) / 3)) ≤ 1 / 8 := by
  set M : ℝ := 24 * Ccrit + 24 with hM
  have hM1 : 1 ≤ M := by linarith
  have hM0 : 0 < M := by linarith
  have hc0 : (0 : ℝ) < 1 / M ^ 5 := by positivity
  have hc1 : 1 / M ^ 5 ≤ 1 := by rw [div_le_one (by positivity)]; exact one_le_pow₀ hM1
  refine ⟨1 / M ^ 5, 1 / M ^ 2, hc0, hc1, by positivity, ?_, ?_⟩
  · rw [div_le_one (by positivity)]; exact one_le_pow₀ hM1
  have h1 : Real.sqrt (1 / M ^ 2) = 1 / M := by
    rw [show (1 : ℝ) / M ^ 2 = (1 / M) ^ 2 by rw [div_pow, one_pow]]
    exact Real.sqrt_sq (by positivity)
  have h2 : (1 / M ^ 5) ^ ((17 : ℝ) / 3) ≤ 1 / M ^ 5 := by
    calc (1 / M ^ 5) ^ ((17 : ℝ) / 3) ≤ (1 / M ^ 5) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge hc0 hc1 (by norm_num)
      _ = 1 / M ^ 5 := Real.rpow_one _
  have h3 : (1 / M ^ 5) ^ ((34 : ℝ) / 3) ≤ 1 / M ^ 5 := by
    calc (1 / M ^ 5) ^ ((34 : ℝ) / 3) ≤ (1 / M ^ 5) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge hc0 hc1 (by norm_num)
      _ = 1 / M ^ 5 := Real.rpow_one _
  have h4 : (1 / M ^ 2)⁻¹ ^ 2 = M ^ 4 := by
    rw [one_div, inv_inv]; ring
  have h5 : M ^ 4 * (1 / M ^ 5) ^ ((34 : ℝ) / 3) ≤ 1 / M := by
    calc M ^ 4 * (1 / M ^ 5) ^ ((34 : ℝ) / 3) ≤ M ^ 4 * (1 / M ^ 5) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = 1 / M := by field_simp
  have h6 : 1 / M ^ 5 ≤ 1 / M := one_div_le_one_div_of_le hM0 (le_self_pow₀ hM1 (by norm_num))
  have h7 : Ccrit * (1 / M) ≤ 1 / 24 := by
    rw [mul_one_div, div_le_div_iff₀ hM0 (by norm_num)]
    linarith
  rw [h1, h4]
  calc Ccrit * (1 / M + (1 / M ^ 5) ^ ((17 : ℝ) / 3) + M ^ 4 * (1 / M ^ 5) ^ ((34 : ℝ) / 3))
      ≤ Ccrit * (1 / M + 1 / M + 1 / M) :=
        mul_le_mul_of_nonneg_left (by linarith) hC.le
    _ = 3 * (Ccrit * (1 / M)) := by ring
    _ ≤ 1 / 8 := by linarith

/-! ### R-RC3 -/

theorem rc3_young_real_pf (K₁ : ℝ) : ∃ K : ℝ, 0 < K ∧ ∀ p : ℕ, 2 ≤ p →
    ∀ e z zm E₀ ξ P : ℝ, 0 ≤ e → 0 ≤ z → 0 ≤ zm → 0 ≤ E₀ → 0 ≤ ξ →
      ((p : ℝ) - 1) / 2 * z + p / 2 * zm - 1 / (4 * ((p : ℝ) - 1)) -
          K₁ * p * (e * Real.sqrt z + e * Real.sqrt zm + E₀ + ξ) ≤ P →
      -(1 / (4 * ((p : ℝ) - 1))) - K * p * (e ^ 2 + E₀ + ξ) ≤ P := by
  refine ⟨3 / 2 * |K₁| ^ 2 + |K₁| + 1, by positivity, ?_⟩
  intro p hp e z zm E₀ ξ P he hz hzm hE hξ hP
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hc0 : 0 ≤ |K₁| := abs_nonneg _
  have hw := Real.sqrt_nonneg z
  have hw' := Real.sqrt_nonneg zm
  have hwz := Real.sq_sqrt hz
  have hwz' := Real.sq_sqrt hzm
  have hK := le_abs_self K₁
  set w := Real.sqrt z
  set w' := Real.sqrt zm
  set c := |K₁|
  set Pr : ℝ := (p : ℝ)
  have hX : 0 ≤ e * w + e * w' + E₀ + ξ := by positivity
  have hK1X : K₁ * Pr * (e * w + e * w' + E₀ + ξ) ≤ c * Pr * (e * w + e * w' + E₀ + ξ) := by
    have := mul_le_mul_of_nonneg_right hK (mul_nonneg (by linarith : (0 : ℝ) ≤ Pr) hX)
    linarith
  have hy1 : c * Pr * (e * w) ≤ (Pr - 1) / 2 * z + c ^ 2 * Pr * e ^ 2 := by
    have key : 2 * (Pr - 1) * ((Pr - 1) / 2 * w ^ 2 + c ^ 2 * Pr * e ^ 2 - c * Pr * (e * w)) =
        ((Pr - 1) * w - c * Pr * e) ^ 2 + c ^ 2 * e ^ 2 * Pr * (Pr - 2) := by ring
    have h0 : 0 ≤ 2 * (Pr - 1) *
        ((Pr - 1) / 2 * w ^ 2 + c ^ 2 * Pr * e ^ 2 - c * Pr * (e * w)) := by
      rw [key]
      exact add_nonneg (sq_nonneg _) (mul_nonneg (by positivity) (by linarith))
    have := (mul_nonneg_iff_of_pos_left (by linarith : (0 : ℝ) < 2 * (Pr - 1))).mp h0
    rw [← hwz]
    linarith
  have hy2 : c * Pr * (e * w') ≤ Pr / 2 * zm + c ^ 2 * Pr * e ^ 2 / 2 := by
    rw [← hwz']
    linarith [mul_nonneg (by linarith : (0 : ℝ) ≤ Pr) (sq_nonneg (w' - c * e))]
  have h1 : 0 ≤ c * Pr * e ^ 2 := by positivity
  have h2 : 0 ≤ Pr * e ^ 2 := by positivity
  have h3 : 0 ≤ c ^ 2 * Pr * (E₀ + ξ) := by positivity
  have h4 : 0 ≤ Pr * (E₀ + ξ) := by positivity
  linarith

/-! ### R-FS7 -/

/-- Copy of `EcF` (`Real.lean`): the uniform weak error of (FS7). -/
noncomputable def EcF_pf (e B₀ hq bh θ z zm : ℝ) : ℝ :=
  e * Real.sqrt z + e * Real.sqrt zm + e ^ 2 + B₀ + e * (hq + Real.sqrt bh + Real.sqrt θ)

/-- The square root of the (FS6) budget, split using `ζ - α ≤ z + r₁` and `q - t ≤ |Cq|`. -/
theorem fs7_sqrt_pf {z r1 bh θ Cq ζ α q t : ℝ} (hz : 0 ≤ z) (hr1n : 0 ≤ r1) (hbh : 0 ≤ bh)
    (hθ : 0 ≤ θ) (hζα : ζ - α ≤ z + r1) (hqtC : q - t ≤ Cq) :
    √(ζ - α + bh * (q - t) + θ) ≤ √z + √r1 + √bh * √|Cq| + √θ := by
  have hbq : bh * (q - t) ≤ bh * |Cq| :=
    mul_le_mul_of_nonneg_left (hqtC.trans (le_abs_self Cq)) hbh
  have hbq0 : 0 ≤ bh * |Cq| := mul_nonneg hbh (abs_nonneg _)
  have a1 := sqrt_add_le_pf (by positivity : 0 ≤ z + r1 + bh * |Cq|) hθ
  have a2 := sqrt_add_le_pf (by positivity : 0 ≤ z + r1) hbq0
  have a3 := sqrt_add_le_pf hz hr1n
  have a4 : √(bh * |Cq|) = √bh * √|Cq| := Real.sqrt_mul hbh _
  have a5 : √(ζ - α + bh * (q - t) + θ) ≤ √(z + r1 + bh * |Cq| + θ) :=
    Real.sqrt_le_sqrt (by linarith)
  linarith

theorem fs7_real_pf (Cw Cq : ℝ) : ∃ K : ℝ, 0 < K ∧
    ∀ e B₀ hq bh θ q t ζ α z qm ζm tm zm β : ℝ, 0 ≤ e → 0 ≤ B₀ → 0 ≤ hq → 0 ≤ bh → 0 ≤ θ →
      0 ≤ z → 0 ≤ zm → 0 ≤ q - t → q - t ≤ Cq → α ≤ ζ →
      |q - ζ - t| ≤ Cw * (e * Real.sqrt (ζ - α + bh * (q - t) + θ) + e * hq + B₀) →
      |ζ - z - α| ≤ Cw * (e * Real.sqrt (z + θ) + B₀) →
      |qm + ζm - tm| ≤ Cw * (e * Real.sqrt (ζ - α + bh * (q - t) + θ) + e * hq + B₀) →
      |ζm + zm - β| ≤ Cw * (e * Real.sqrt (zm + θ) + B₀) →
      |q - ζ - t| ≤ K * EcF_pf e B₀ hq bh θ z zm ∧ |ζ - z - α| ≤ K * EcF_pf e B₀ hq bh θ z zm ∧
        |qm + ζm - tm| ≤ K * EcF_pf e B₀ hq bh θ z zm ∧
        |ζm + zm - β| ≤ K * EcF_pf e B₀ hq bh θ z zm := by
  have hc : 0 ≤ |Cw| := abs_nonneg _
  have hs : 0 ≤ Real.sqrt |Cq| := Real.sqrt_nonneg _
  refine ⟨(1 + |Cw|) * (2 + |Cw| + Real.sqrt |Cq|), by positivity, ?_⟩
  intro e B₀ hq bh θ q t ζ α z qm ζm tm zm β he hB hhq hbh hθ hz hzm hqt hqtC hαζ h0 h1 h2 h3
  have hsz := Real.sqrt_nonneg z
  have hszm := Real.sqrt_nonneg zm
  have hsbh := Real.sqrt_nonneg bh
  have hsθ := Real.sqrt_nonneg θ
  have hF_def : EcF_pf e B₀ hq bh θ z zm =
      e * √z + e * √zm + e ^ 2 + B₀ + e * (hq + √bh + √θ) := rfl
  have hez := mul_nonneg he hsz
  have hezm := mul_nonneg he hszm
  have hebh := mul_nonneg he hsbh
  have heθ := mul_nonneg he hsθ
  have hehq := mul_nonneg he hhq
  have he2 := sq_nonneg e
  have hFn : 0 ≤ EcF_pf e B₀ hq bh θ z zm := by rw [hF_def]; positivity
  have habs : ∀ r X : ℝ, 0 ≤ X → |r| ≤ Cw * X → |r| ≤ |Cw| * X := fun r X hX h =>
    h.trans (mul_le_mul_of_nonneg_right (le_abs_self Cw) hX)
  have hY1F : e * √z + e * √θ + B₀ ≤ EcF_pf e B₀ hq bh θ z zm := by rw [hF_def]; linarith
  have hY3F : e * √zm + e * √θ + B₀ ≤ EcF_pf e B₀ hq bh θ z zm := by rw [hF_def]; linarith
  have hbhF : e * √bh ≤ EcF_pf e B₀ hq bh θ z zm := by rw [hF_def]; linarith
  have e5 : e * √z + e ^ 2 / 2 + e * √θ + e * hq + B₀ ≤ EcF_pf e B₀ hq bh θ z zm := by
    rw [hF_def]; linarith
  set F := EcF_pf e B₀ hq bh θ z zm
  set c := |Cw|
  set s := Real.sqrt |Cq|
  -- the two simple residuals
  have hY1 : e * √(z + θ) + B₀ ≤ e * √z + e * √θ + B₀ := by
    have := mul_le_mul_of_nonneg_left (sqrt_add_le_pf hz hθ) he
    linarith
  have hY3 : e * √(zm + θ) + B₀ ≤ e * √zm + e * √θ + B₀ := by
    have := mul_le_mul_of_nonneg_left (sqrt_add_le_pf hzm hθ) he
    linarith
  have hr1 : |ζ - z - α| ≤ c * (e * √z + e * √θ + B₀) :=
    (habs _ _ (by positivity) h1).trans (mul_le_mul_of_nonneg_left hY1 hc)
  have hr3 : |ζm + zm - β| ≤ c * (e * √zm + e * √θ + B₀) :=
    (habs _ _ (by positivity) h3).trans (mul_le_mul_of_nonneg_left hY3 hc)
  -- the big square root
  have hr1n : 0 ≤ |ζ - z - α| := abs_nonneg _
  have hζα : ζ - α ≤ z + |ζ - z - α| := by have := le_abs_self (ζ - z - α); linarith
  have hA := fs7_sqrt_pf hz hr1n hbh hθ hζα hqtC
  set r1 := |ζ - z - α| with hr1def
  have hAM : e * √r1 ≤ (e ^ 2 + r1) / 2 := by
    linarith [sq_nonneg (e - √r1), Real.sq_sqrt hr1n]
  have hX0n : 0 ≤ e * √(ζ - α + bh * (q - t) + θ) + e * hq + B₀ := by positivity
  have hX0 : e * √(ζ - α + bh * (q - t) + θ) + e * hq + B₀ ≤ (1 + c + s) * F := by
    have e1 := mul_le_mul_of_nonneg_left hA he
    have e3 : c * (e * √z + e * √θ + B₀) ≤ c * F := mul_le_mul_of_nonneg_left hY1F hc
    have e4 : s * (e * √bh) ≤ s * F := mul_le_mul_of_nonneg_left hbhF hs
    have e6 : 0 ≤ c * F := mul_nonneg hc hFn
    linarith
  have hKc : c * (1 + c + s) ≤ (1 + c) * (2 + c + s) := by linarith
  have hcK : c ≤ (1 + c) * (2 + c + s) := by linarith [sq_nonneg c, mul_nonneg hc hs]
  have hmain : ∀ r : ℝ, |r| ≤ Cw * (e * √(ζ - α + bh * (q - t) + θ) + e * hq + B₀) →
      |r| ≤ (1 + c) * (2 + c + s) * F := by
    intro r hr
    calc |r| ≤ c * (e * √(ζ - α + bh * (q - t) + θ) + e * hq + B₀) := habs _ _ hX0n hr
      _ ≤ c * ((1 + c + s) * F) := mul_le_mul_of_nonneg_left hX0 hc
      _ = (c * (1 + c + s)) * F := by ring
      _ ≤ (1 + c) * (2 + c + s) * F := mul_le_mul_of_nonneg_right hKc hFn
  refine ⟨hmain _ h0, ?_, hmain _ h2, ?_⟩
  · calc r1 ≤ c * (e * √z + e * √θ + B₀) := hr1
      _ ≤ c * F := mul_le_mul_of_nonneg_left hY1F hc
      _ ≤ (1 + c) * (2 + c + s) * F := mul_le_mul_of_nonneg_right hcK hFn
  · calc |ζm + zm - β| ≤ c * (e * √zm + e * √θ + B₀) := hr3
      _ ≤ c * F := mul_le_mul_of_nonneg_left hY3F hc
      _ ≤ (1 + c) * (2 + c + s) * F := mul_le_mul_of_nonneg_right hcK hFn

/-! ### R-JR -/

/-- The one-variable core of JR2: at `α = ζ/(1+ζ)`, the reserve is at least `-1/(4(p-1))`. -/
theorem jr_one_var_pf {P ζ : ℝ} (hP : 2 ≤ P) (hζ : 0 ≤ ζ) :
    -(1 / (4 * (P - 1))) ≤
      (P - 1) * ζ / 2 - ζ / (1 + ζ) / 2 - P / 2 + P * (1 / (1 + ζ / (1 + ζ))) / 2 := by
  have h1 : 0 < 1 + ζ := by linarith
  have h2 : 0 < 1 + 2 * ζ := by linarith
  have hm : 0 < P - 1 := by linarith
  have h1' := h1.ne'
  have h2' := h2.ne'
  have hm' := hm.ne'
  have hg0 : 1 + ζ / (1 + ζ) = (1 + 2 * ζ) / (1 + ζ) := by
    rw [eq_div_iff h1', add_mul, div_mul_cancel₀ _ h1']
    ring
  have hg : 1 / (1 + ζ / (1 + ζ)) = (1 + ζ) / (1 + 2 * ζ) := by rw [hg0, one_div_div]
  rw [hg]
  have d1 : ζ / (1 + ζ) * (1 + ζ) = ζ := div_mul_cancel₀ _ h1'
  have d2 : (1 + ζ) / (1 + 2 * ζ) * (1 + 2 * ζ) = 1 + ζ := div_mul_cancel₀ _ h2'
  have d3 : 1 / (4 * (P - 1)) * (4 * (P - 1)) = 1 := one_div_mul_cancel (by positivity)
  have key : ((P - 1) * ζ / 2 - ζ / (1 + ζ) / 2 - P / 2 + P * ((1 + ζ) / (1 + 2 * ζ)) / 2 +
      1 / (4 * (P - 1))) * (4 * (P - 1) * (1 + ζ) * (1 + 2 * ζ)) =
      4 * (P - 1) ^ 2 * ζ ^ 3 + (4 * (P - 1) ^ 2 - 6 * (P - 1) + 2) * ζ ^ 2 +
        (3 - 4 * (P - 1)) * ζ + 1 := by
    linear_combination (-2 * (P - 1) * (1 + 2 * ζ)) * d1 + (2 * P * (P - 1) * (1 + ζ)) * d2 +
      ((1 + ζ) * (1 + 2 * ζ)) * d3
  have hpoly : 0 ≤ 4 * (P - 1) ^ 2 * ζ ^ 3 + (4 * (P - 1) ^ 2 - 6 * (P - 1) + 2) * ζ ^ 2 +
      (3 - 4 * (P - 1)) * ζ + 1 := by
    linarith [sq_nonneg (2 * (P - 1) * ζ - 1),
      mul_nonneg hζ (sq_nonneg (2 * (P - 1) * ζ - 3 / 2)), mul_nonneg hζ hζ]
  rw [← key] at hpoly
  have := (mul_nonneg_iff_of_pos_right (by positivity : 0 < 4 * (P - 1) * (1 + ζ) * (1 + 2 * ζ))).mp
    hpoly
  linarith

/-- JR3: the Gram fact of the mixed kernel gives `z₋ ≥ β²/(1+β) - (e₀ + 4E)`. -/
theorem jr_zm_pf {E e₀ qm ζm tm zm β : ℝ} (hE : 0 ≤ E) (he₀ : 0 ≤ e₀) (hβ : 0 ≤ β)
    (hzm : 0 ≤ zm) (hGm : ζm ^ 2 ≤ qm * zm) (htm1 : tm ≤ 1 + e₀) (h2u : qm + ζm - tm ≤ E)
    (h3l : -E ≤ ζm + zm - β) (h3u : ζm + zm - β ≤ E) :
    β - 1 + 1 / (1 + β) - (e₀ + 4 * E) ≤ zm := by
  have a1 : (ζm + zm) ^ 2 ≤ (qm + 2 * ζm + zm) * zm := by linarith
  have a2 : (qm + 2 * ζm + zm) * zm ≤ (1 + β + (e₀ + 2 * E)) * zm :=
    mul_le_mul_of_nonneg_right (by linarith) hzm
  have a3 : β ^ 2 - 2 * β * E ≤ (ζm + zm) ^ 2 := by
    linarith [mul_nonneg hβ (by linarith : 0 ≤ ζm + zm - β + E), sq_nonneg (ζm + zm - β)]
  have hzm1 : β ^ 2 - 2 * β * E ≤ zm * (1 + β + (e₀ + 2 * E)) := by linarith
  have he₁ : 0 ≤ e₀ + 2 * E := by positivity
  have hpos : 0 < 1 + β + (e₀ + 2 * E) := by linarith
  have hu : 0 < 1 + β := by linarith
  have key : 0 ≤ (1 + β + (e₀ + 2 * E)) * (zm * (1 + β) - β ^ 2 + (e₀ + 4 * E) * (1 + β)) := by
    have b1 := mul_le_mul_of_nonneg_left hzm1 hu.le
    linarith [mul_nonneg (mul_nonneg he₁ (by positivity : (0 : ℝ) ≤ e₀ + 4 * E)) hu.le,
      mul_nonneg he₁ (by linarith : (0 : ℝ) ≤ 1 + 2 * β), mul_nonneg hE hu.le]
  have h4 := (mul_nonneg_iff_of_pos_left hpos).mp key
  have hinv : 1 / (1 + β) * (1 + β) = 1 := one_div_mul_cancel hu.ne'
  refine le_of_mul_le_mul_right ?_ hu
  linarith

/-- The α-cap: `ζ² ≤ q z`, `q ≈ ζ + t`, `z ≈ ζ - α` give `α ≤ ζ/(1+ζ) + (e₀ + 3E)`. -/
theorem jr_cap_pf {E e₀ q t ζ α z : ℝ} (hE : 0 ≤ E) (he₀ : 0 ≤ e₀) (hz : 0 ≤ z)
    (hG : ζ ^ 2 ≤ q * z) (hα : 0 ≤ α) (hαζ : α ≤ ζ) (ht1 : t ≤ 1 + e₀)
    (h0u : q - ζ - t ≤ E) (h1l : -E ≤ ζ - z - α) :
    α ≤ ζ / (1 + ζ) + (e₀ + 3 * E) := by
  have hζ0 : 0 ≤ ζ := hα.trans hαζ
  have he'0 : 0 ≤ e₀ + E := by positivity
  have hq' : q ≤ ζ + 1 + (e₀ + E) := by linarith
  have hz' : z ≤ ζ - α + E := by linarith
  have hqz : ζ ^ 2 ≤ (ζ + 1 + (e₀ + E)) * (ζ - α + E) := by
    calc ζ ^ 2 ≤ q * z := hG
      _ ≤ (ζ + 1 + (e₀ + E)) * z := mul_le_mul_of_nonneg_right hq' hz
      _ ≤ (ζ + 1 + (e₀ + E)) * (ζ - α + E) := mul_le_mul_of_nonneg_left hz' (by linarith)
  have hstar : α * (ζ + 1 + (e₀ + E)) ≤ ζ * (1 + E + (e₀ + E)) + E * (1 + (e₀ + E)) := by
    linarith
  have hpos : 0 < 1 + ζ + (e₀ + E) := by linarith
  have h1ζ : 0 < 1 + ζ := by linarith
  have key : 0 ≤ (1 + ζ + (e₀ + E)) * (ζ + (1 + ζ) * (e₀ + 3 * E) - α * (1 + ζ)) := by
    have b1 := mul_le_mul_of_nonneg_left hstar h1ζ.le
    have b2 : 0 ≤ (1 + ζ) * ((e₀ + E) + E + E * ζ + (e₀ + E) ^ 2 + E * (e₀ + E)) := by
      positivity
    linarith [mul_nonneg hζ0 he'0]
  have hcap := (mul_nonneg_iff_of_pos_left hpos).mp key
  have hdiv : ζ / (1 + ζ) * (1 + ζ) = ζ := div_mul_cancel₀ ζ h1ζ.ne'
  refine le_of_mul_le_mul_right ?_ h1ζ
  linarith

theorem jr_real_pf (C₁ C₂ : ℝ) : ∃ K : ℝ, 0 < K ∧ ∀ p : ℕ, 2 ≤ p →
    ∀ E ξ ε q t ζ α z qm ζm tm zm β : ℝ, 0 ≤ E → 0 ≤ ε → ε ≤ ξ →
      0 ≤ q → 0 ≤ z → ζ ^ 2 ≤ q * z → 0 ≤ qm → 0 ≤ zm → ζm ^ 2 ≤ qm * zm →
      t ≤ q → 0 ≤ α → α ≤ ζ → 0 ≤ β → 0 ≤ t → t ≤ 1 + C₁ * ε → 0 ≤ tm →
      tm ≤ 1 + C₁ * ε → β ≤ α + C₂ * ξ →
      |q - ζ - t| ≤ E → |ζ - z - α| ≤ E → |qm + ζm - tm| ≤ E → |ζm + zm - β| ≤ E →
      ((p : ℝ) - 1) / 2 * z + p / 2 * zm - 1 / (4 * ((p : ℝ) - 1)) - K * p * (E + ξ) ≤
        ((p : ℝ) - 1) * (q - t) + p * (qm - tm) := by
  refine ⟨2 * |C₁| + |C₂| + 9, by positivity, ?_⟩
  intro p hp E ξ ε q t ζ α z qm ζm tm zm β hE hε hεξ hq hz hG _ hzm hGm _ hα hαζ hβ _ ht1
    _ htm1 hβα h0 h1 h2 h3
  have hP2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hc₁ : 0 ≤ |C₁| := abs_nonneg _
  have hc₂ : 0 ≤ |C₂| := abs_nonneg _
  have hξ : 0 ≤ ξ := hε.trans hεξ
  have hC1 : C₁ * ε ≤ |C₁| * ξ :=
    (mul_le_mul_of_nonneg_right (le_abs_self C₁) hε).trans (mul_le_mul_of_nonneg_left hεξ hc₁)
  have hC2 : C₂ * ξ ≤ |C₂| * ξ := mul_le_mul_of_nonneg_right (le_abs_self C₂) hξ
  set P : ℝ := (p : ℝ)
  set c₁ := |C₁|
  set c₂ := |C₂|
  obtain ⟨h0l, h0u⟩ := abs_le.mp h0
  obtain ⟨h1l, h1u⟩ := abs_le.mp h1
  obtain ⟨h2l, h2u⟩ := abs_le.mp h2
  obtain ⟨h3l, h3u⟩ := abs_le.mp h3
  have hζ0 : 0 ≤ ζ := hα.trans hαζ
  have he₀ : 0 ≤ c₁ * ξ := mul_nonneg hc₁ hξ
  have hzm3 := jr_zm_pf hE he₀ hβ hzm hGm (by linarith) h2u h3l h3u
  have hαa := jr_cap_pf hE he₀ hz hG hα hαζ (by linarith) h0u h1l
  have h1ζ : 0 < 1 + ζ := by linarith
  have ha'0 : 0 ≤ ζ / (1 + ζ) := div_nonneg hζ0 h1ζ.le
  have hgβ : 1 / (1 + α) - c₂ * ξ ≤ 1 / (1 + β) :=
    inv_one_add_lip_pf hα hβ (by positivity) (by linarith)
  have hgα : 1 / (1 + ζ / (1 + ζ)) - (c₁ * ξ + 3 * E) ≤ 1 / (1 + α) :=
    inv_one_add_lip_pf ha'0 hα (by positivity) hαa
  have h6 := jr_one_var_pf hP2 hζ0
  have hP0 : (0 : ℝ) ≤ P := by linarith
  have hPm : (0 : ℝ) ≤ P - 1 := by linarith
  have f1 := mul_le_mul_of_nonneg_left h0l hPm
  have f2 := mul_le_mul_of_nonneg_left h1l hPm
  have f3 := mul_le_mul_of_nonneg_left h2l hP0
  have f4 := mul_le_mul_of_nonneg_left h3u hP0
  have f5 := mul_le_mul_of_nonneg_left hzm3 hP0
  have f6 := mul_le_mul_of_nonneg_left hgβ hP0
  have f7 : P * β ≤ P * (α + c₂ * ξ) := mul_le_mul_of_nonneg_left (by linarith) hP0
  have f8 := mul_le_mul_of_nonneg_left hgα hP0
  have f11 : 0 ≤ (P - 1) * (c₁ * ξ + 3 * E) := mul_nonneg hPm (by positivity)
  have f12 : 0 ≤ c₁ * P * E := by positivity
  have f13 : 0 ≤ c₂ * P * E := by positivity
  have f14 : 0 ≤ P * E := by positivity
  have f15 : 0 ≤ c₁ * P * ξ := by positivity
  have f16 : 0 ≤ P * ξ := by positivity
  linarith

/-! ### Nonnegativity of the error terms -/

section Nonneg

variable {d p : ℕ}

theorem epsP_pos_pf (hR : TRegime d p) : 0 < epsP d p := by
  unfold epsP; linarith [hR.one_lt_rOf]

theorem dbar_nonneg_pf (hR : TRegime d p) : 0 ≤ dbar d p := by
  have h1 := epsP_pos_pf hR
  have h2 : 0 ≤ (p : ℝ) ^ 4 / d := by positivity
  have h3 : 0 ≤ ((p : ℝ) / d) ^ ((1 : ℝ) / 3) := by positivity
  unfold dbar; linarith

theorem GamP_nonneg_pf : 0 ≤ GamP d p := by unfold GamP; positivity

theorem epsS_nonneg_pf : 0 ≤ epsS d p := by unfold epsS; positivity

theorem eP_nonneg_pf {h : ℝ} (hh : 0 < h) : 0 ≤ eP d p h := by
  unfold eP; exact div_nonneg (Real.sqrt_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hh.le)

theorem B0P_nonneg_pf {h : ℝ} (hh : 0 < h) : 0 ≤ B0P d p h := by
  unfold B0P vth; positivity

theorem xiP_nonneg_pf (hR : TRegime d p) (h : ℝ) : 0 ≤ xiP d p h := by
  have h1 := epsP_pos_pf hR
  have h2 := hR.η0Of_pos
  have h3 := epsS_nonneg_pf (d := d) (p := p)
  have := Real.sqrt_nonneg h
  have := Real.sqrt_nonneg (epsP d p / p + epsP d p ^ 2 + (p : ℝ) / d)
  have := Real.sqrt_nonneg (epsP d p / p + epsP d p ^ 2)
  have : (0 : ℝ) ≤ 1 / (d : ℝ) := by positivity
  unfold xiP; linarith

theorem ErrRC3_nonneg_pf (hR : TRegime d p) {h : ℝ} (hh : 0 < h) : 0 ≤ ErrRC3 d p h := by
  have h1 := eP_nonneg_pf (d := d) (p := p) hh
  have h2 := B0P_nonneg_pf (d := d) (p := p) hh
  have h3 := xiP_nonneg_pf hR h
  have h4 : 0 ≤ h ^ ((3 : ℝ) / 4) + Real.sqrt (1 / (d * h)) + Real.sqrt (thP d) := by positivity
  have h5 := mul_nonneg h1 h4
  have h6 := sq_nonneg (eP d p h)
  unfold ErrRC3; linarith

theorem ErowP_nonneg_pf (S : ℝ) : 0 ≤ ErowP d p S := by
  unfold ErowP GamP vth; positivity

theorem epsBL_nonneg_pf {h : ℝ} (hh : 0 < h) : 0 ≤ epsBL d p h := by
  unfold epsBL vth; positivity

theorem Err10_nonneg_pf {h : ℝ} (hh : 0 < h) (S : ℝ) : 0 ≤ Err10 d p h S := by
  have h1 := ErowP_nonneg_pf (d := d) (p := p) S
  have h2 := epsBL_nonneg_pf (d := d) (p := p) hh
  have h3 : 0 ≤ (p : ℝ) ^ 5 / d + (p : ℝ) ^ 2 / (d * h) + (p : ℝ) / (d * h * Real.sqrt h) := by
    positivity
  unfold Err10; linarith

theorem LdP_nonneg_pf : 0 ≤ LdP d p := by unfold LdP; positivity

theorem LdP_le_five_pf (hR : TRegime d p) : LdP d p ≤ 5 := by
  have hd := hR.ten_pow_six_le_d
  have hΔ := hR.ΔOf_pos
  have hRs := hR.RsqOf_pos
  have hRs' : RsqOf d p = 4 * ((d : ℝ) - 1) + ΔOf p := rfl
  unfold LdP
  rw [hR.aOf_sq, mul_one_div, div_le_iff₀ hRs, hRs']
  linarith

end Nonneg

/-- `c₁ x + c₂ y + c₃ z ≤ (c₁ + c₂ + c₃ + 1)(x + y + z)` for nonnegative data. -/
theorem lin3_pf {a b c x y z : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hx : 0 ≤ x)
    (hy : 0 ≤ y) (hz : 0 ≤ z) : a * x + b * y + c * z ≤ (a + b + c + 1) * (x + y + z) := by
  linarith [mul_nonneg ha hy, mul_nonneg ha hz, mul_nonneg hb hx, mul_nonneg hb hz,
    mul_nonneg hc hx, mul_nonneg hc hy]

/-! ### R-D12 -/

theorem d12_real_pf (C₁₀ C₃ C₄ : ℝ) : ∃ C : ℝ, 0 < C ∧ ∃ P₀ : ℕ, ∀ (d p : ℕ) (h : ℝ),
    TRegime d p → P₀ ≤ p → 0 < h →
    ∀ S R qp qm tp tm tp0 tm0 : ℝ,
      LdP d p * (((p : ℝ) - 1) * qp + p * qm) - C₁₀ * Err10 d p h S ≤ R →
      -cpP p - C₃ * p * ErrRC3 d p h ≤ ((p : ℝ) - 1) * (qp - tp) + p * (qm - tm) →
      tp0 - tp ≤ C₄ * Real.sqrt h → tm0 - tm ≤ C₄ * Real.sqrt h →
      -(LdP d p * cpP p) - C * Err12 d p h S ≤
        R - LdP d p * (((p : ℝ) - 1) * tp0 + p * tm0) := by
  refine ⟨|C₁₀| + 5 * |C₃| + 10 * |C₄| + 1, by positivity, 0, ?_⟩
  intro d p h hR _ hh S R qp qm tp tm tp0 tm0 hD10 hRC3 htp htm
  have hP2 : (2 : ℝ) ≤ p := by exact_mod_cast hR.two_le_p
  have hL0 : 0 ≤ LdP d p := LdP_nonneg_pf
  have hL5 : LdP d p ≤ 5 := LdP_le_five_pf hR
  have hE10 : 0 ≤ Err10 d p h S := Err10_nonneg_pf hh S
  have hRC : 0 ≤ ErrRC3 d p h := ErrRC3_nonneg_pf hR hh
  have hsh : 0 ≤ Real.sqrt h := Real.sqrt_nonneg h
  have hE12 : Err12 d p h S = Err10 d p h S + p * ErrRC3 d p h + p * Real.sqrt h := rfl
  rw [hE12]
  have hc10 : 0 ≤ |C₁₀| := abs_nonneg _
  have hc3 : 0 ≤ |C₃| := abs_nonneg _
  have hc4 : 0 ≤ |C₄| := abs_nonneg _
  have g1 : -(|C₄| * Real.sqrt h) ≤ tp - tp0 := by
    have := mul_le_mul_of_nonneg_right (le_abs_self C₄) hsh; linarith
  have g2 : -(|C₄| * Real.sqrt h) ≤ tm - tm0 := by
    have := mul_le_mul_of_nonneg_right (le_abs_self C₄) hsh; linarith
  have h10 : C₁₀ * Err10 d p h S ≤ |C₁₀| * Err10 d p h S :=
    mul_le_mul_of_nonneg_right (le_abs_self _) hE10
  have h3 : C₃ * p * ErrRC3 d p h ≤ |C₃| * p * ErrRC3 d p h :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)) hRC
  have hlin := lin3_pf hc10 (by positivity : (0 : ℝ) ≤ 5 * |C₃|)
    (by positivity : (0 : ℝ) ≤ 10 * |C₄|) hE10 (by positivity : (0 : ℝ) ≤ p * ErrRC3 d p h)
    (by positivity : (0 : ℝ) ≤ p * Real.sqrt h)
  set L := LdP d p
  set E10 := Err10 d p h S
  set RC := ErrRC3 d p h
  set sh := Real.sqrt h
  set cp := cpP p
  set P : ℝ := (p : ℝ)
  have hB : -(2 * P) * (|C₄| * sh) ≤ (P - 1) * (tp - tp0) + P * (tm - tm0) := by
    have g3 := mul_le_mul_of_nonneg_left g1 (by linarith : (0 : ℝ) ≤ P - 1)
    have g4 := mul_le_mul_of_nonneg_left g2 (by linarith : (0 : ℝ) ≤ P)
    linarith [mul_nonneg hc4 hsh]
  have f1 : L * (-cp - C₃ * P * RC) ≤ L * ((P - 1) * (qp - tp) + P * (qm - tm)) :=
    mul_le_mul_of_nonneg_left hRC3 hL0
  have f2 : L * (C₃ * P * RC) ≤ 5 * (|C₃| * P * RC) :=
    calc L * (C₃ * P * RC) ≤ L * (|C₃| * P * RC) := mul_le_mul_of_nonneg_left h3 hL0
      _ ≤ 5 * (|C₃| * P * RC) := mul_le_mul_of_nonneg_right hL5 (by positivity)
  have f3 : L * (-(2 * P) * (|C₄| * sh)) ≤ L * ((P - 1) * (tp - tp0) + P * (tm - tm0)) :=
    mul_le_mul_of_nonneg_left hB hL0
  have f4 : L * (2 * P * (|C₄| * sh)) ≤ 5 * (2 * P * (|C₄| * sh)) :=
    mul_le_mul_of_nonneg_right hL5 (by positivity)
  linarith

/-! ### R-final -/

/-- The remainder of `Err12` after its row term `Γ √(S+1)`. -/
noncomputable def E12r_pf (d p : ℕ) (h : ℝ) : ℝ :=
  (p : ℝ) ^ 13 / (d : ℝ) ^ 2 + vth d + (p : ℝ) ^ 5 / d + (p : ℝ) ^ 2 / (d * h) +
    (p : ℝ) / (d * h * Real.sqrt h) + epsBL d p h + (p : ℝ) * ErrRC3 d p h +
    (p : ℝ) * Real.sqrt h

theorem Err12_split_pf (d p : ℕ) (h S : ℝ) :
    Err12 d p h S = GamP d p * Real.sqrt (S + 1) + E12r_pf d p h := by
  unfold Err12 Err10 ErowP E12r_pf; ring

theorem TotErr_split_pf (d p : ℕ) (h : ℝ) :
    TotErr d p h = GamP d p + GamP d p ^ 2 + (epsS d p + η0Of d p + 1 / (d : ℝ)) +
      E12r_pf d p h + (p : ℝ) ^ 3 * Real.sqrt ((p : ℝ) * dbar d p / d) := by
  unfold TotErr E12r_pf; ring

theorem E12r_nonneg_pf {d p : ℕ} (hR : TRegime d p) {h : ℝ} (hh : 0 < h) :
    0 ≤ E12r_pf d p h ∧ (p : ℝ) ^ 5 / d ≤ E12r_pf d p h := by
  have h1 : 0 ≤ (p : ℝ) ^ 13 / (d : ℝ) ^ 2 + vth d + (p : ℝ) ^ 2 / (d * h) +
      (p : ℝ) / (d * h * Real.sqrt h) := by unfold vth; positivity
  have h2 := epsBL_nonneg_pf (d := d) (p := p) hh
  have h3 : 0 ≤ (p : ℝ) * ErrRC3 d p h := mul_nonneg (by positivity) (ErrRC3_nonneg_pf hR hh)
  have h4 : 0 ≤ (p : ℝ) * Real.sqrt h := by positivity
  have h5 : 0 ≤ (p : ℝ) ^ 5 / d := by positivity
  unfold E12r_pf
  constructor <;> linarith

theorem TotErr_nonneg_pf {d p : ℕ} (hR : TRegime d p) {h : ℝ} (hh : 0 < h) :
    0 ≤ TotErr d p h := by
  rw [TotErr_split_pf]
  have := (E12r_nonneg_pf hR hh).1
  have := GamP_nonneg_pf (d := d) (p := p)
  have := epsS_nonneg_pf (d := d) (p := p)
  have := hR.η0Of_pos
  have : 0 ≤ 1 / (d : ℝ) := by positivity
  have : 0 ≤ (p : ℝ) ^ 3 * Real.sqrt ((p : ℝ) * dbar d p / d) := by positivity
  nlinarith [sq_nonneg (GamP d p)]

/-- Young absorption of the row term: `2G√(S+1) - (1 - 1/P)(S - 4) ≤ γ + 5G + 2G²` when
`S ≥ 4 - γ`. -/
theorem absorb_pf {S γ G P : ℝ} (hγ : 0 ≤ γ) (hG : 0 ≤ G) (hP : 2 ≤ P) (hS : 4 - γ ≤ S) :
    2 * G * Real.sqrt (S + 1) - (1 - 1 / P) * (S - 4) ≤ γ + 5 * G + 2 * G ^ 2 := by
  have hS' : 0 ≤ S - 4 + γ := by linarith
  have hw : 0 ≤ Real.sqrt (S - 4 + γ) := Real.sqrt_nonneg _
  have hw2 : Real.sqrt (S - 4 + γ) ^ 2 = S - 4 + γ := Real.sq_sqrt hS'
  have h5 : Real.sqrt 5 ≤ 9 / 4 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hsq : Real.sqrt (S + 1) ≤ Real.sqrt (S - 4 + γ) + 9 / 4 := by
    calc Real.sqrt (S + 1) ≤ Real.sqrt ((S - 4 + γ) + 5) := Real.sqrt_le_sqrt (by linarith)
      _ ≤ Real.sqrt (S - 4 + γ) + Real.sqrt 5 := sqrt_add_le_pf hS' (by norm_num)
      _ ≤ Real.sqrt (S - 4 + γ) + 9 / 4 := by linarith
  set w := Real.sqrt (S - 4 + γ)
  have hP0 : 0 < P := by linarith
  have hP1 : 1 / P ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hP
  have hP2 : 0 ≤ 1 / P := by positivity
  have a1 : 2 * G * Real.sqrt (S + 1) ≤ 2 * G * (w + 9 / 4) :=
    mul_le_mul_of_nonneg_left hsq (by positivity)
  have a2 : 1 / 2 * w ^ 2 ≤ (1 - 1 / P) * w ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg w)
  have a3 : 1 / P * w ^ 2 = 1 / P * (S - 4 + γ) := by rw [hw2]
  linarith [mul_nonneg hP2 hγ, sq_nonneg (w - 2 * G)]

/-- (F1): drop the nonnegative terms of (D3) and use `r C₊ ≤ 4a²`. -/
theorem fa_F1_pf {ε r Lb L sED A S J R Cp Q P T3 T3' : ℝ} (hε : 0 < ε) (hr : 1 < r)
    (hL : L ≤ Lb) (hsED : 0 ≤ sED) (hP : 2 ≤ P) (hCpJ : Cp ≤ J) (hrC : r * Cp ≤ 4 * A)
    (hT : T3 ≤ T3')
    (hD3 : ε * (1 - r * L) + r * sED + (1 - 1 / P) * A * S + r / P * J + 2 * A * R ≤
      Q + r * Cp + T3) :
    ε * (1 - r * Lb) + (1 - 1 / P) * A * S + 2 * A * R ≤ Q + 4 * (1 - 1 / P) * A + T3' := by
  have g1 : 0 ≤ r * ε * (Lb - L) := mul_nonneg (mul_nonneg (by linarith) hε.le) (by linarith)
  have g2 : 0 ≤ r * sED := mul_nonneg (by linarith) hsED
  have g3 : r / P * Cp ≤ r / P * J :=
    mul_le_mul_of_nonneg_left hCpJ (div_nonneg (by linarith) (by linarith))
  have g3' : r / P * Cp = 1 / P * (r * Cp) := by ring
  have hP1 : 0 ≤ 1 - 1 / P := by rw [sub_nonneg, div_le_one (by linarith)]; linarith
  have g4' := mul_le_mul_of_nonneg_left hrC hP1
  linarith

/-- (F2): combine (F1) with (D12) and (D13), keeping the absorbed row term. -/
theorem fa_F2_pf {E0 P A S R Q T3' Ld cp C₁₂ G sq E12 Tc C₁₃ p3 sx γ : ℝ}
    (hF1 : E0 + (1 - 1 / P) * A * S + 2 * A * R ≤ Q + 4 * (1 - 1 / P) * A + T3')
    (hD12 : -(Ld * cp) - C₁₂ * (G * sq + E12) ≤ R - Ld * Tc)
    (hD13 : Q ≤ A * (2 * Ld * Tc + C₁₃ * p3 * sx))
    (hA0 : 0 ≤ A) (hp3 : 0 ≤ p3) (hsx : 0 ≤ sx) (hGE : 0 ≤ G * sq + E12)
    (g9 : 2 * (|C₁₂| * G) * sq - (1 - 1 / P) * (S - 4) ≤
      γ + 5 * (|C₁₂| * G) + 2 * (|C₁₂| * G) ^ 2) :
    E0 ≤ 2 * A * Ld * cp + A * (2 * |C₁₂| * E12 + |C₁₃| * p3 * sx +
      (γ + 5 * (|C₁₂| * G) + 2 * (|C₁₂| * G) ^ 2)) + T3' := by
  have g6 := mul_le_mul_of_nonneg_left hD12 (by positivity : (0 : ℝ) ≤ 2 * A)
  have g7 : A * (C₁₃ * p3 * sx) ≤ A * (|C₁₃| * p3 * sx) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self _) hp3) hsx) hA0
  have g8 : 2 * A * (C₁₂ * (G * sq + E12)) ≤ 2 * A * (|C₁₂| * (G * sq + E12)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_abs_self _) hGE) (by positivity)
  have g9A := mul_le_mul_of_nonneg_left g9 hA0
  linarith

/-- (F4): multiply by `d`, using `d a² ≤ 1/4 + 1/d` and the drift reserve. -/
theorem fa_d_pf {D A ε F cp Y' c p5 ip η : ℝ} (hD : 16 ≤ D) (hA0 : 0 ≤ A)
    (hdA : D * A ≤ 1 / 4 + 1 / D) (hcp : 0 ≤ cp) (hY' : 0 ≤ Y')
    (hF2 : ε * F ≤ 2 * A * (16 * D * A) * cp + A * Y' + c * p5 / D ^ 2)
    (hdrift : ip - 2 * η ≤ D * ε * F) :
    ip - 2 * η ≤ 2 * (1 + 9 / D) * cp + 1 / 2 * Y' + c * (p5 / D) := by
  have hD0 : 0 < D := by linarith
  have hDA0 : 0 ≤ D * A := by positivity
  have hiD : 1 / D ≤ 1 / 16 := one_div_le_one_div_of_le (by norm_num) hD
  have hiD0 : 0 ≤ 1 / D := by positivity
  have g10 := mul_le_mul_of_nonneg_left hF2 hD0.le
  have hsq2 : (D * A) ^ 2 ≤ (1 / 4 + 1 / D) ^ 2 := pow_le_pow_left₀ hDA0 hdA 2
  have e : (1 / 4 + 1 / D) ^ 2 = 1 / 16 + 1 / 2 * (1 / D) + 1 / D * (1 / D) := by ring
  have h9 : 9 / D = 9 * (1 / D) := by ring
  have hb : 32 * (D * A) ^ 2 ≤ 2 * (1 + 9 / D) := by
    have := mul_le_mul_of_nonneg_left hiD hiD0
    linarith
  have g11 : D * (2 * A * (16 * D * A) * cp) ≤ 2 * (1 + 9 / D) * cp := by
    calc D * (2 * A * (16 * D * A) * cp) = (32 * (D * A) ^ 2) * cp := by ring
      _ ≤ 2 * (1 + 9 / D) * cp := mul_le_mul_of_nonneg_right hb hcp
  have g12 : D * (A * Y') ≤ 1 / 2 * Y' := by
    calc D * (A * Y') = (D * A) * Y' := by ring
      _ ≤ 1 / 2 * Y' := mul_le_mul_of_nonneg_right (by linarith) hY'
  have g13 : D * (c * p5 / D ^ 2) = c * (p5 / D) := by
    field_simp
  have e2 : D * ε * F = D * (ε * F) := by ring
  have e3 : D * (2 * A * (16 * D * A) * cp + A * Y' + c * p5 / D ^ 2) =
      D * (2 * A * (16 * D * A) * cp) + D * (A * Y') + D * (c * p5 / D ^ 2) := by ring
  linarith

/-- (F5): every term is a multiple of a summand of `TotErr`. -/
theorem fa_K_pf {C₃ C₁₂ C₁₃ C₁₅ G E12 Yv p3 sx p5D lhs cpt : ℝ} (hG : 0 ≤ G) (hE : 0 ≤ E12)
    (hYv : 0 ≤ Yv) (hp3 : 0 ≤ p3) (hsx : 0 ≤ sx) (hp5 : p5D ≤ E12)
    (h : lhs ≤ cpt + 1 / 2 * (2 * |C₁₂| * E12 + |C₁₃| * p3 * sx +
      (|C₁₅| * Yv + 5 * (|C₁₂| * G) + 2 * (|C₁₂| * G) ^ 2)) + |C₃| * p5D) :
    lhs ≤ cpt + (|C₃| + |C₁₃| + 7 * |C₁₂| + 2 * |C₁₂| ^ 2 + |C₁₅| + 1) *
      (G + G ^ 2 + Yv + E12 + p3 * sx) := by
  have hc3 := abs_nonneg C₃
  have hc12 := abs_nonneg C₁₂
  have hc13 := abs_nonneg C₁₃
  have hc15 := abs_nonneg C₁₅
  have hc12s := sq_nonneg |C₁₂|
  set K := |C₃| + |C₁₃| + 7 * |C₁₂| + 2 * |C₁₂| ^ 2 + |C₁₅| + 1 with hK
  have k1 : 5 / 2 * |C₁₂| * G ≤ K * G := mul_le_mul_of_nonneg_right (by linarith) hG
  have k2 : |C₁₂| ^ 2 * G ^ 2 ≤ K * G ^ 2 := mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
  have k3 : |C₁₅| / 2 * Yv ≤ K * Yv := mul_le_mul_of_nonneg_right (by linarith) hYv
  have k4 : (|C₁₂| + |C₃|) * E12 ≤ K * E12 := mul_le_mul_of_nonneg_right (by linarith) hE
  have k5 : |C₁₃| / 2 * (p3 * sx) ≤ K * (p3 * sx) :=
    mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hp3 hsx)
  have k6 : |C₃| * p5D ≤ |C₃| * E12 := mul_le_mul_of_nonneg_left hp5 hc3
  linarith

theorem final_assembly_real_pf (C₃ C₁₂ C₁₃ C₁₅ : ℝ) : ∃ K : ℝ, 0 < K ∧ ∃ P₀ : ℕ,
    ∀ (d p : ℕ) (h : ℝ), TRegime d p → P₀ ≤ p → 0 < h →
    ∀ S R J Cp Q L sED Tc : ℝ, 0 ≤ S → 0 ≤ sED → L ≤ LbarP d p → 0 ≤ Cp → Cp ≤ J →
      Cp ≤ aOf d p ^ 2 * LbarP d p * sOf d p ^ 2 →
      epsP d p * (1 - rOf d p * L) + rOf d p * sED + (1 - 1 / (p : ℝ)) * aOf d p ^ 2 * S +
          rOf d p / p * J + 2 * aOf d p ^ 2 * R ≤
        Q + rOf d p * Cp + C₃ * (p : ℝ) ^ 5 / (d : ℝ) ^ 2 →
      -(LdP d p * cpP p) - C₁₂ * Err12 d p h S ≤ R - LdP d p * Tc →
      Q ≤ aOf d p ^ 2 * (2 * LdP d p * Tc +
        C₁₃ * (p : ℝ) ^ 3 * Real.sqrt ((p : ℝ) * dbar d p / d)) →
      4 - C₁₅ * (epsS d p + η0Of d p + 1 / (d : ℝ)) ≤ S →
      1 / (p : ℝ) - 2 * η0Of d p ≤ 2 * (1 + 9 / (d : ℝ)) * cpP p + K * TotErr d p h := by
  obtain ⟨P₀, hPF⟩ := param_facts_pf
  refine ⟨|C₃| + |C₁₃| + 7 * |C₁₂| + 2 * |C₁₂| ^ 2 + |C₁₅| + 1, by positivity, P₀, ?_⟩
  intro d p h hR hp hh S R J Cp Q L sED Tc _ hsED hL _ hCpJ hCpA hD3 hD12 hD13 hD15
  obtain ⟨-, -, hdA, -, -, -, -, hdrift, hrLs, -, -, -, -⟩ := hPF d p hR hp
  have hP2 : (2 : ℝ) ≤ p := by exact_mod_cast hR.two_le_p
  have hd6 := hR.ten_pow_six_le_d
  have hA0 : 0 ≤ aOf d p ^ 2 := sq_nonneg _
  have hG0 : 0 ≤ GamP d p := GamP_nonneg_pf
  obtain ⟨hE12r, hp5⟩ := E12r_nonneg_pf hR hh
  have hεs : 0 ≤ epsS d p := epsS_nonneg_pf
  have hη0 := hR.η0Of_pos
  have hsx : 0 ≤ Real.sqrt ((p : ℝ) * dbar d p / d) := Real.sqrt_nonneg _
  have hcp : 0 ≤ cpP p := by
    unfold cpP
    exact div_nonneg zero_le_one (by linarith)
  have hLdA : LdP d p = 16 * (d : ℝ) * aOf d p ^ 2 := rfl
  rw [Err12_split_pf] at hD12
  rw [TotErr_split_pf]
  have g4 : rOf d p * Cp ≤ 4 * aOf d p ^ 2 := by
    calc rOf d p * Cp ≤ rOf d p * (aOf d p ^ 2 * LbarP d p * sOf d p ^ 2) :=
          mul_le_mul_of_nonneg_left hCpA (by linarith [hR.one_lt_rOf])
      _ = aOf d p ^ 2 * (rOf d p * LbarP d p * sOf d p ^ 2) := by ring
      _ ≤ aOf d p ^ 2 * 4 := mul_le_mul_of_nonneg_left hrLs hA0
      _ = 4 * aOf d p ^ 2 := by ring
  have g5 : C₃ * (p : ℝ) ^ 5 / (d : ℝ) ^ 2 ≤ |C₃| * (p : ℝ) ^ 5 / (d : ℝ) ^ 2 :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
      (by positivity)
  have hF1 := fa_F1_pf (epsP_pos_pf hR) hR.one_lt_rOf hL hsED hP2 hCpJ g4 g5 hD3
  have hY : 0 ≤ epsS d p + η0Of d p + 1 / (d : ℝ) := by positivity
  have hS15 : 4 - |C₁₅| * (epsS d p + η0Of d p + 1 / (d : ℝ)) ≤ S := by
    have := mul_le_mul_of_nonneg_right (le_abs_self C₁₅) hY
    linarith
  have g9 := absorb_pf (mul_nonneg (abs_nonneg C₁₅) hY) (mul_nonneg (abs_nonneg C₁₂) hG0) hP2
    hS15
  have hF2 := fa_F2_pf hF1 hD12 hD13 hA0 (by positivity) hsx (by positivity) g9
  rw [hLdA] at hF2
  have hF4 := fa_d_pf (by linarith) hA0 hdA hcp (by positivity) hF2 hdrift
  exact fa_K_pf hG0 hE12r hY (by positivity) hsx hp5 hF4

/-! ### R-ledger -/

/-- `t^a / X ≤ 1/t^b` when `t^N ≤ X`, `a + b ≤ N` and `t ≥ 1`. -/
theorem pow_div_le_pf {t X : ℝ} {N : ℕ} (ht : 1 ≤ t) (hX : t ^ N ≤ X) (a b : ℕ)
    (hab : a + b ≤ N) : t ^ a / X ≤ 1 / t ^ b := by
  have ht0 : 0 < t := by linarith
  have hX0 : 0 < X := lt_of_lt_of_le (pow_pos ht0 N) hX
  rw [div_le_div_iff₀ hX0 (pow_pos ht0 b), one_mul, ← pow_add]
  exact (pow_le_pow_right₀ ht hab).trans hX

theorem inv_pow_anti_pf {t : ℝ} (ht : 1 ≤ t) {a b : ℕ} (hab : b ≤ a) :
    1 / t ^ a ≤ 1 / t ^ b :=
  one_div_le_one_div_of_le (pow_pos (by linarith) b) (pow_le_pow_right₀ ht hab)

/-- `t = √p`: `t ≥ 1000`, `p = t²`, `t¹⁷ ≤ d`. -/
theorem ledger_t_pf {d p : ℕ} (hR : TRegime d p) :
    1000 ≤ Real.sqrt p ∧ (p : ℝ) = Real.sqrt p ^ 2 ∧ Real.sqrt p ^ 17 ≤ (d : ℝ) := by
  have hp : (10 : ℝ) ^ 6 ≤ p := by exact_mod_cast hR.hp
  have hp0 : (0 : ℝ) ≤ p := by positivity
  refine ⟨?_, (Real.sq_sqrt hp0).symm, ?_⟩
  · rw [Real.le_sqrt (by norm_num) hp0]; linarith
  · have h17 : (p : ℝ) ^ 17 ≤ (d : ℝ) ^ 2 := by exact_mod_cast hR.hpd
    have : (Real.sqrt p ^ 17) ^ 2 ≤ (d : ℝ) ^ 2 := by
      rw [← pow_mul, show 17 * 2 = 2 * 17 by norm_num, pow_mul, Real.sq_sqrt hp0]
      exact h17
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp this

/-- `η₀² p d ≤ 8`. -/
theorem eta_sq_le_pf {d p : ℕ} (hR : TRegime d p) : η0Of d p ^ 2 * ((p : ℝ) * d) ≤ 8 := by
  have h := hR.pf_p_mul
  have hη0 := hR.η0Of_pos
  have hd := hR.ten_pow_six_le_d
  have hq : qOf d = (d : ℝ) - 1 := rfl
  rw [hq] at h
  have h1 : 0 ≤ ((d : ℝ) - 2) * ((p : ℝ) * η0Of d p ^ 2) :=
    mul_nonneg (by linarith) (by positivity)
  linarith

theorem eta_le_pf {d p : ℕ} (hR : TRegime d p) {t : ℝ} (ht : 1000 ≤ t)
    (hPt : (p : ℝ) = t ^ 2) (hDt : t ^ 17 ≤ (d : ℝ)) : η0Of d p ≤ 1 / t ^ 9 := by
  have h8 := eta_sq_le_pf hR
  have hη0 := hR.η0Of_pos
  have ht0 : 0 < t := by linarith
  have h1 : η0Of d p ^ 2 * t ^ 19 ≤ 8 := by
    have : η0Of d p ^ 2 * t ^ 19 ≤ η0Of d p ^ 2 * ((p : ℝ) * d) := by
      rw [hPt, show t ^ 19 = t ^ 2 * t ^ 17 by ring]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hDt (by positivity))
        (sq_nonneg _)
    linarith
  have hx : 0 ≤ η0Of d p * t ^ 9 := by positivity
  have h3 : (η0Of d p * t ^ 9) ^ 2 ≤ 1 := by
    have e : (η0Of d p * t ^ 9) ^ 2 * t = η0Of d p ^ 2 * t ^ 19 := by ring
    have := mul_le_mul_of_nonneg_left ht (sq_nonneg (η0Of d p * t ^ 9))
    linarith
  have h4 : η0Of d p * t ^ 9 ≤ 1 := by nlinarith
  rw [le_div_iff₀ (by positivity)]; exact h4

theorem epsS_le_pf {d p : ℕ} {t : ℝ} (ht : 1000 ≤ t) (hPt : (p : ℝ) = t ^ 2)
    (hDt : t ^ 17 ≤ (d : ℝ)) : epsS d p ≤ 1 / t ^ 5 := by
  have ht0 : 0 < t := by linarith
  have hD0 : (0 : ℝ) < d := lt_of_lt_of_le (by positivity) hDt
  have hsp : Real.sqrt p = t := by rw [hPt, Real.sqrt_sq ht0.le]
  have hsd : t ^ 8 ≤ Real.sqrt d := by
    rw [Real.le_sqrt (by positivity) hD0.le, ← pow_mul]
    exact (pow_le_pow_right₀ (by linarith) (by norm_num)).trans hDt
  unfold epsS
  rw [hsp, hPt, div_le_div_iff₀ (Real.sqrt_pos.mpr hD0) (by positivity)]
  calc t ^ 2 * t * t ^ 5 = t ^ 8 := by ring
    _ ≤ Real.sqrt d := hsd
    _ = 1 * Real.sqrt d := (one_mul _).symm

theorem xiP_le_pf {d p : ℕ} (hR : TRegime d p) {t : ℝ} (ht : 1000 ≤ t) (hPt : (p : ℝ) = t ^ 2)
    (hDt : t ^ 17 ≤ (d : ℝ)) (h : ℝ) : xiP d p h ≤ Real.sqrt h + 9 / t ^ 5 := by
  have ht0 : 0 < t := by linarith
  have ht1 : 1 ≤ t := by linarith
  have hη := eta_le_pf hR ht hPt hDt
  have hη0 := hR.η0Of_pos
  have hε0 := epsP_pos_pf hR
  have hεle : epsP d p ≤ 1 / t ^ 9 := by rw [pf_epsP_eq]; linarith
  have hεs := epsS_le_pf ht hPt hDt
  have hd1 : 1 / (d : ℝ) ≤ 1 / t ^ 17 := one_div_le_one_div_of_le (by positivity) hDt
  have i9 : 1 / t ^ 9 ≤ 1 / t ^ 5 := inv_pow_anti_pf ht1 (by norm_num)
  have i17 : 1 / t ^ 17 ≤ 1 / t ^ 5 := inv_pow_anti_pf ht1 (by norm_num)
  have hX : epsP d p / p + epsP d p ^ 2 + (p : ℝ) / d ≤ 4 / t ^ 10 := by
    have a1 : epsP d p / p ≤ 1 / t ^ 11 := by
      rw [hPt]
      calc epsP d p / t ^ 2 ≤ 1 / t ^ 9 / t ^ 2 :=
            div_le_div_of_nonneg_right hεle (by positivity)
        _ = 1 / t ^ 11 := by ring
    have a2 : epsP d p ^ 2 ≤ 1 / t ^ 18 := by
      calc epsP d p ^ 2 ≤ (1 / t ^ 9) ^ 2 := pow_le_pow_left₀ hε0.le hεle 2
        _ = 1 / t ^ 18 := by ring
    have a3 : (p : ℝ) / d ≤ 1 / t ^ 15 := by
      rw [hPt]; exact pow_div_le_pf ht1 hDt 2 15 (by norm_num)
    have b1 : 1 / t ^ 11 ≤ 1 / t ^ 10 := inv_pow_anti_pf ht1 (by norm_num)
    have b2 : 1 / t ^ 18 ≤ 1 / t ^ 10 := inv_pow_anti_pf ht1 (by norm_num)
    have b3 : 1 / t ^ 15 ≤ 1 / t ^ 10 := inv_pow_anti_pf ht1 (by norm_num)
    have e : (4 : ℝ) / t ^ 10 = 4 * (1 / t ^ 10) := by ring
    have : (0 : ℝ) ≤ 1 / t ^ 10 := by positivity
    linarith
  have hsX : Real.sqrt (epsP d p / p + epsP d p ^ 2 + (p : ℝ) / d) ≤ 2 / t ^ 5 := by
    rw [Real.sqrt_le_left (by positivity)]
    calc _ ≤ 4 / t ^ 10 := hX
      _ = (2 / t ^ 5) ^ 2 := by ring
  have hsX' : Real.sqrt (epsP d p / p + epsP d p ^ 2) ≤ 2 / t ^ 5 := by
    have : (0 : ℝ) ≤ (p : ℝ) / d := by positivity
    exact (Real.sqrt_le_sqrt (by linarith)).trans hsX
  have e1 : (9 : ℝ) / t ^ 5 = 9 * (1 / t ^ 5) := by ring
  have e2 : (2 : ℝ) / t ^ 5 = 2 * (1 / t ^ 5) := by ring
  unfold xiP
  linarith

theorem rpow_third_cube_pf {x : ℝ} (hx : 0 ≤ x) : (x ^ ((1 : ℝ) / 3)) ^ 3 = x := by
  rw [← Real.rpow_mul_natCast hx]; norm_num

theorem c0_cube_pf {c : ℝ} (hc : 0 ≤ c) : (c ^ ((17 : ℝ) / 3)) ^ 3 = c ^ 17 := by
  rw [← Real.rpow_mul_natCast hc]; norm_num

theorem c0_sq_pf {c : ℝ} (hc : 0 ≤ c) : c ^ ((34 : ℝ) / 3) = (c ^ ((17 : ℝ) / 3)) ^ 2 := by
  rw [← Real.rpow_mul_natCast hc]; norm_num

/-- (T2): `δ̄ ≤ 3 (p/d)^{1/3}`. -/
theorem dbar_le_pf {d p : ℕ} (hR : TRegime d p) :
    dbar d p ≤ 3 * ((p : ℝ) / d) ^ ((1 : ℝ) / 3) := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast le_trans (by norm_num) hR.hp
  have hd1 : (1 : ℝ) ≤ d := le_trans (by norm_num) hR.ten_pow_six_le_d
  have hp0 : (0 : ℝ) < p := by linarith
  have hd0 : (0 : ℝ) < d := by linarith
  have hu0 : 0 ≤ ((p : ℝ) / d) ^ ((1 : ℝ) / 3) := by positivity
  have hu3 : (((p : ℝ) / d) ^ ((1 : ℝ) / 3)) ^ 3 = (p : ℝ) / d :=
    rpow_third_cube_pf (by positivity)
  have hε0 := epsP_pos_pf hR
  have hε2 : epsP d p ^ 2 * ((p : ℝ) * d) ≤ 2 := by
    have h8 := eta_sq_le_pf hR
    have e : epsP d p ^ 2 * ((p : ℝ) * d) * 4 = η0Of d p ^ 2 * ((p : ℝ) * d) := by
      rw [pf_epsP_eq]; ring
    linarith
  have hεu : epsP d p ≤ ((p : ℝ) / d) ^ ((1 : ℝ) / 3) := by
    have hx : 0 ≤ epsP d p ^ 3 * d := by positivity
    have hcube : (epsP d p ^ 2 * ((p : ℝ) * d)) ^ 3 ≤ 2 ^ 3 :=
      pow_le_pow_left₀ (by positivity) hε2 3
    have hp5 : (8 : ℝ) ≤ (p : ℝ) ^ 5 * d := by
      have := mul_le_mul_of_nonneg_right (one_le_pow₀ hp1 : (1 : ℝ) ≤ (p : ℝ) ^ 5) hd0.le
      linarith [hR.ten_pow_six_le_d]
    have h1 : (epsP d p ^ 3 * d) ^ 2 * ((p : ℝ) ^ 3 * d) ≤ (p : ℝ) ^ 2 * ((p : ℝ) ^ 3 * d) := by
      have e1 : (epsP d p ^ 3 * d) ^ 2 * ((p : ℝ) ^ 3 * d) =
          (epsP d p ^ 2 * ((p : ℝ) * d)) ^ 3 := by ring
      have e2 : (p : ℝ) ^ 2 * ((p : ℝ) ^ 3 * d) = (p : ℝ) ^ 5 * d := by ring
      rw [e1, e2]; linarith
    have h2 : (epsP d p ^ 3 * d) ^ 2 ≤ (p : ℝ) ^ 2 := le_of_mul_le_mul_right h1 (by positivity)
    have h3 : epsP d p ^ 3 * d ≤ p := (pow_le_pow_iff_left₀ hx hp0.le two_ne_zero).mp h2
    have h4 : epsP d p ^ 3 ≤ (((p : ℝ) / d) ^ ((1 : ℝ) / 3)) ^ 3 := by
      rw [hu3, le_div_iff₀ hd0]; exact h3
    exact (pow_le_pow_iff_left₀ hε0.le hu0 (by norm_num)).mp h4
  have hp4u : (p : ℝ) ^ 4 / d ≤ ((p : ℝ) / d) ^ ((1 : ℝ) / 3) := by
    have hx : 0 ≤ (p : ℝ) ^ 4 / d := by positivity
    have h11 : (p : ℝ) ^ 11 ≤ (d : ℝ) ^ 2 := by
      have h17 : (p : ℝ) ^ 17 ≤ (d : ℝ) ^ 2 := by exact_mod_cast hR.hpd
      exact (pow_le_pow_right₀ hp1 (by norm_num)).trans h17
    have h4 : ((p : ℝ) ^ 4 / d) ^ 3 ≤ (((p : ℝ) / d) ^ ((1 : ℝ) / 3)) ^ 3 := by
      rw [hu3, div_pow, div_le_div_iff₀ (by positivity) hd0]
      calc ((p : ℝ) ^ 4) ^ 3 * d = ((p : ℝ) * d) * (p : ℝ) ^ 11 := by ring
        _ ≤ ((p : ℝ) * d) * (d : ℝ) ^ 2 := mul_le_mul_of_nonneg_left h11 (by positivity)
        _ = (p : ℝ) * (d : ℝ) ^ 3 := by ring
    exact (pow_le_pow_iff_left₀ hx hu0 (by norm_num)).mp h4
  unfold dbar
  linarith

theorem GamP_sq_pf {d p : ℕ} (hR : TRegime d p) :
    GamP d p ^ 2 = (p : ℝ) ^ 9 * dbar d p / d := by
  have hdb := dbar_nonneg_pf hR
  unfold GamP
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  ring

/-- `Γ ≤ √3 c₀^{17/3}/p` when `p¹⁷ ≤ c₀¹⁷ d²` (proof of (T3)). -/
theorem GamP_le_pf {d p : ℕ} (hR : TRegime d p) {c₀ : ℝ} (hc0 : 0 < c₀)
    (hpc : (p : ℝ) ^ 17 ≤ c₀ ^ 17 * (d : ℝ) ^ 2) :
    GamP d p ≤ Real.sqrt 3 * c₀ ^ ((17 : ℝ) / 3) / p := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast le_trans (by norm_num) hR.hp
  have hd0 : (0 : ℝ) < d := by linarith [hR.ten_pow_six_le_d]
  have hp0 : (0 : ℝ) < p := by linarith
  have hw0 : 0 ≤ c₀ ^ ((17 : ℝ) / 3) := by positivity
  have hw3 := c0_cube_pf hc0.le
  have hu0 : 0 ≤ ((p : ℝ) / d) ^ ((1 : ℝ) / 3) := by positivity
  have hu3 : (((p : ℝ) / d) ^ ((1 : ℝ) / 3)) ^ 3 = (p : ℝ) / d :=
    rpow_third_cube_pf (by positivity)
  have hdb := dbar_le_pf hR
  set w := c₀ ^ ((17 : ℝ) / 3)
  set u := ((p : ℝ) / d) ^ ((1 : ℝ) / 3)
  have hkey : (p : ℝ) ^ 11 * u ≤ w ^ 2 * d := by
    have hx : 0 ≤ (p : ℝ) ^ 11 * u := by positivity
    have hy : 0 ≤ w ^ 2 * d := by positivity
    have h34 : (p : ℝ) ^ 34 ≤ c₀ ^ 34 * (d : ℝ) ^ 4 := by
      have := pow_le_pow_left₀ (by positivity) hpc 2
      calc (p : ℝ) ^ 34 = ((p : ℝ) ^ 17) ^ 2 := by ring
        _ ≤ (c₀ ^ 17 * (d : ℝ) ^ 2) ^ 2 := this
        _ = c₀ ^ 34 * (d : ℝ) ^ 4 := by ring
    have h3 : ((p : ℝ) ^ 11 * u) ^ 3 ≤ (w ^ 2 * d) ^ 3 := by
      have e1 : ((p : ℝ) ^ 11 * u) ^ 3 = (p : ℝ) ^ 34 / d := by rw [mul_pow, hu3]; ring
      have e2 : (w ^ 2 * d) ^ 3 = (w ^ 3) ^ 2 * (d : ℝ) ^ 3 := by ring
      rw [e1, e2, hw3, div_le_iff₀ hd0]
      calc (p : ℝ) ^ 34 ≤ c₀ ^ 34 * (d : ℝ) ^ 4 := h34
        _ = (c₀ ^ 17) ^ 2 * (d : ℝ) ^ 3 * d := by ring
    exact (pow_le_pow_iff_left₀ hx hy (by norm_num)).mp h3
  have hG0 := GamP_nonneg_pf (d := d) (p := p)
  have hG2 : GamP d p ^ 2 ≤ (Real.sqrt 3 * w / p) ^ 2 := by
    rw [GamP_sq_pf hR, div_pow, mul_pow, Real.sq_sqrt (by norm_num),
      div_le_div_iff₀ hd0 (by positivity)]
    calc (p : ℝ) ^ 9 * dbar d p * (p : ℝ) ^ 2 ≤ (p : ℝ) ^ 9 * (3 * u) * (p : ℝ) ^ 2 := by
          gcongr
      _ = 3 * ((p : ℝ) ^ 11 * u) := by ring
      _ ≤ 3 * (w ^ 2 * d) := by linarith
      _ = 3 * w ^ 2 * d := by ring
  exact (pow_le_pow_iff_left₀ hG0 (by positivity) two_ne_zero).mp hG2

/-- `e = Γ/κ₀` at `h = κ₀ p⁻⁴`. -/
theorem eP_eq_pf {d p : ℕ} (hR : TRegime d p) {κ₀ h : ℝ} (hk0 : 0 < κ₀)
    (hh : h = κ₀ / (p : ℝ) ^ 4) : eP d p h = GamP d p / κ₀ := by
  have hdb := dbar_nonneg_pf hR
  have hd0 : (0 : ℝ) < d := by linarith [hR.ten_pow_six_le_d]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast lt_of_lt_of_le (by norm_num) hR.hp
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd0
  unfold eP GamP
  rw [hh, Real.sqrt_div (by positivity : (0 : ℝ) ≤ p * dbar d p) (d : ℝ)]
  field_simp

/-- `2(1 + 9/d) c_p ≤ 0.6/p`. -/
theorem cp_le_pf {d p : ℕ} (hR : TRegime d p) :
    2 * (1 + 9 / (d : ℝ)) * cpP p ≤ 6 / 10 * (1 / (p : ℝ)) := by
  have hd := hR.ten_pow_six_le_d
  have hp : (10 : ℝ) ^ 6 ≤ p := by exact_mod_cast hR.hp
  have h9 : 9 / (d : ℝ) ≤ 1 / 100 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have hcp : cpP p = 1 / (4 * ((p : ℝ) - 1)) := rfl
  have hcp0 : 0 ≤ cpP p := by rw [hcp]; exact div_nonneg zero_le_one (by linarith)
  calc 2 * (1 + 9 / (d : ℝ)) * cpP p ≤ 2 * (1 + 1 / 100) * cpP p :=
        mul_le_mul_of_nonneg_right (by linarith) hcp0
    _ ≤ 6 / 10 * (1 / (p : ℝ)) := by
        rw [hcp, mul_one_div, mul_one_div, div_le_div_iff₀ (by linarith) (by linarith)]
        linarith

/-- The ledger context: `t = √p ≥ 1000`, `t¹⁷ ≤ d`, `h = κ₀ p⁻⁴`, `κ₀ ∈ (0, 1]`. -/
structure LCtx_pf (d p : ℕ) (κ₀ h t : ℝ) : Prop where
  treg : TRegime d p
  ht : 1000 ≤ t
  hPt : (p : ℝ) = t ^ 2
  hDt : t ^ 17 ≤ (d : ℝ)
  k0 : 0 < κ₀
  k1 : κ₀ ≤ 1
  hh : h = κ₀ / (p : ℝ) ^ 4

namespace LCtx_pf

variable {d p : ℕ} {κ₀ h t : ℝ}

theorem t0 (C : LCtx_pf d p κ₀ h t) : 0 < t := by linarith [C.ht]

theorem t1 (C : LCtx_pf d p κ₀ h t) : 1 ≤ t := by linarith [C.ht]

theorem D0 (C : LCtx_pf d p κ₀ h t) : (0 : ℝ) < d := lt_of_lt_of_le (pow_pos C.t0 17) C.hDt

theorem p0 (C : LCtx_pf d p κ₀ h t) : (0 : ℝ) < p := by rw [C.hPt]; exact pow_pos C.t0 2

theorem h_eq (C : LCtx_pf d p κ₀ h t) : h = κ₀ / t ^ 8 := by rw [C.hh, C.hPt]; ring

theorem h0 (C : LCtx_pf d p κ₀ h t) : 0 < h := by
  rw [C.h_eq]; exact div_pos C.k0 (pow_pos C.t0 8)

theorem h1 (C : LCtx_pf d p κ₀ h t) : h ≤ 1 := by
  rw [C.h_eq, div_le_one (pow_pos C.t0 8)]; exact C.k1.trans (one_le_pow₀ C.t1)

theorem sqrt_h (C : LCtx_pf d p κ₀ h t) : Real.sqrt h = Real.sqrt κ₀ / t ^ 4 := by
  rw [C.h_eq, Real.sqrt_div' _ (pow_pos C.t0 8).le, show t ^ 8 = (t ^ 4) ^ 2 by ring,
    Real.sqrt_sq (pow_pos C.t0 4).le]

theorem inv_h (C : LCtx_pf d p κ₀ h t) : 1 / h = t ^ 8 / κ₀ := by rw [C.h_eq, one_div_div]

theorem inv_sqrt_h (C : LCtx_pf d p κ₀ h t) : 1 / Real.sqrt h = t ^ 4 / Real.sqrt κ₀ := by
  rw [C.sqrt_h, one_div_div]

theorem sk1 (C : LCtx_pf d p κ₀ h t) : Real.sqrt κ₀ ≤ 1 := Real.sqrt_le_one.mpr C.k1

theorem k_le_sk (C : LCtx_pf d p κ₀ h t) : κ₀ ≤ Real.sqrt κ₀ := by
  rw [Real.le_sqrt C.k0.le C.k0.le]; nlinarith [C.k0, C.k1]

theorem kk_le (C : LCtx_pf d p κ₀ h t) : 1 / (κ₀ * Real.sqrt κ₀) ≤ 1 / κ₀ ^ 2 := by
  have := C.k0
  apply one_div_le_one_div_of_le (by positivity)
  rw [sq]; exact mul_le_mul_of_nonneg_left C.k_le_sk C.k0.le

theorem inv_le_W (C : LCtx_pf d p κ₀ h t) {m n : ℕ} (hmn : m ≤ n) :
    1 / t ^ n ≤ 1 / (κ₀ ^ 2 * t ^ m) := by
  have := C.k0; have := C.t0
  apply one_div_le_one_div_of_le (by positivity)
  have hk2 : κ₀ ^ 2 ≤ 1 := by nlinarith [C.k1]
  calc κ₀ ^ 2 * t ^ m ≤ 1 * t ^ n :=
        mul_le_mul hk2 (pow_le_pow_right₀ C.t1 hmn) (by positivity) zero_le_one
    _ = t ^ n := one_mul _

theorem kinv_le_W (C : LCtx_pf d p κ₀ h t) {m n : ℕ} (hmn : m ≤ n) :
    1 / (κ₀ * t ^ n) ≤ 1 / (κ₀ ^ 2 * t ^ m) := by
  have := C.k0; have := C.t0
  apply one_div_le_one_div_of_le (by positivity)
  have hk2 : κ₀ ^ 2 ≤ κ₀ := by nlinarith [C.k1]
  exact mul_le_mul hk2 (pow_le_pow_right₀ C.t1 hmn) (by positivity) C.k0.le

theorem k2inv_le_W (C : LCtx_pf d p κ₀ h t) {m n : ℕ} (hmn : m ≤ n) :
    1 / (κ₀ ^ 2 * t ^ n) ≤ 1 / (κ₀ ^ 2 * t ^ m) := by
  have := C.k0; have := C.t0
  apply one_div_le_one_div_of_le (by positivity)
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ C.t1 hmn) (by positivity)

theorem inv_le_kinv (C : LCtx_pf d p κ₀ h t) (n : ℕ) : 1 / t ^ n ≤ 1 / (κ₀ * t ^ n) := by
  have := C.k0; have := C.t0
  apply one_div_le_one_div_of_le (by positivity)
  exact mul_le_of_le_one_left (by positivity) C.k1

theorem PU (C : LCtx_pf d p κ₀ h t) :
    (p : ℝ) * (1 / (κ₀ ^ 2 * t ^ 5)) = 1 / (κ₀ ^ 2 * t ^ 3) := by
  have := C.k0; have := C.t0
  rw [C.hPt, mul_one_div, div_eq_div_iff (by positivity) (by positivity)]; ring

theorem eta_le (C : LCtx_pf d p κ₀ h t) : η0Of d p ≤ 1 / t ^ 9 :=
  eta_le_pf C.treg C.ht C.hPt C.hDt

theorem invD_le (C : LCtx_pf d p κ₀ h t) : 1 / (d : ℝ) ≤ 1 / t ^ 17 :=
  one_div_le_one_div_of_le (pow_pos C.t0 17) C.hDt

theorem vth_le (C : LCtx_pf d p κ₀ h t) : vth d ≤ 1 / t ^ 17 := by
  have hd1 : (1 : ℝ) ≤ d := le_trans (by norm_num) C.treg.ten_pow_six_le_d
  unfold vth
  exact le_trans (one_div_le_one_div_of_le C.D0 (le_self_pow₀ hd1 (by norm_num))) C.invD_le

theorem d34 (C : LCtx_pf d p κ₀ h t) : t ^ 34 ≤ (d : ℝ) ^ 2 := by
  rw [show t ^ 34 = (t ^ 17) ^ 2 by ring]
  exact pow_le_pow_left₀ (pow_pos C.t0 17).le C.hDt 2

theorem pk_div_le (C : LCtx_pf d p κ₀ h t) (k b : ℕ) (hkb : 2 * k + b ≤ 17) :
    (p : ℝ) ^ k / d ≤ 1 / t ^ b := by
  rw [C.hPt, ← pow_mul]; exact pow_div_le_pf C.t1 C.hDt _ _ hkb

theorem p13_le (C : LCtx_pf d p κ₀ h t) : (p : ℝ) ^ 13 / (d : ℝ) ^ 2 ≤ 1 / t ^ 8 := by
  rw [C.hPt, ← pow_mul]; exact pow_div_le_pf C.t1 C.d34 _ _ (by norm_num)

theorem p2Dh_le (C : LCtx_pf d p κ₀ h t) :
    (p : ℝ) ^ 2 / (d * h) ≤ 1 / (κ₀ ^ 2 * t ^ 3) := by
  have := C.k0; have := C.t0
  have e : (p : ℝ) ^ 2 / (d * h) = (p : ℝ) ^ 6 / d * (1 / κ₀) := by
    calc (p : ℝ) ^ 2 / (d * h) = (p : ℝ) ^ 2 * (1 / (d : ℝ)) * (1 / h) := by ring
      _ = (p : ℝ) ^ 6 / d * (1 / κ₀) := by rw [C.inv_h, C.hPt]; ring
  rw [e]
  calc (p : ℝ) ^ 6 / d * (1 / κ₀) ≤ 1 / t ^ 5 * (1 / κ₀) :=
        mul_le_mul_of_nonneg_right (C.pk_div_le 6 5 (by norm_num)) (by positivity)
    _ = 1 / (κ₀ * t ^ 5) := by ring
    _ ≤ 1 / (κ₀ ^ 2 * t ^ 3) := C.kinv_le_W (by norm_num)

theorem pDhh_le (C : LCtx_pf d p κ₀ h t) :
    (p : ℝ) / (d * h * Real.sqrt h) ≤ 1 / (κ₀ ^ 2 * t ^ 3) := by
  have := C.k0; have := C.t0
  have e : (p : ℝ) / (d * h * Real.sqrt h) = t ^ 14 / d * (1 / (κ₀ * Real.sqrt κ₀)) := by
    calc (p : ℝ) / (d * h * Real.sqrt h) =
          (p : ℝ) * (1 / (d : ℝ)) * (1 / h) * (1 / Real.sqrt h) := by ring
      _ = t ^ 14 / d * (1 / (κ₀ * Real.sqrt κ₀)) := by
          rw [C.inv_h, C.inv_sqrt_h, C.hPt]; ring
  rw [e]
  calc t ^ 14 / d * (1 / (κ₀ * Real.sqrt κ₀)) ≤ 1 / t ^ 3 * (1 / κ₀ ^ 2) :=
        mul_le_mul (pow_div_le_pf C.t1 C.hDt _ _ (by norm_num)) C.kk_le (by positivity)
          (by positivity)
    _ = 1 / (κ₀ ^ 2 * t ^ 3) := by ring

theorem epsBL_le (C : LCtx_pf d p κ₀ h t) : epsBL d p h ≤ 3 * (1 / (κ₀ ^ 2 * t ^ 3)) := by
  have := C.k0; have := C.t0
  have hd1 : (1 : ℝ) ≤ d := le_trans (by norm_num) C.treg.ten_pow_six_le_d
  have hv : vth d ≤ 1 / (d : ℝ) ^ 2 := by
    unfold vth
    exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ hd1 (by norm_num))
  have hv0 : 0 ≤ vth d := by unfold vth; positivity
  have e : (p : ℝ) ^ 5 + (p : ℝ) ^ 2 / h = t ^ 10 + t ^ 12 * (1 / κ₀) := by
    calc (p : ℝ) ^ 5 + (p : ℝ) ^ 2 / h = (p : ℝ) ^ 5 + (p : ℝ) ^ 2 * (1 / h) := by ring
      _ = t ^ 10 + t ^ 12 * (1 / κ₀) := by rw [C.inv_h, C.hPt]; ring
  have hk : 1 ≤ 1 / κ₀ := by rw [le_div_iff₀ C.k0]; linarith [C.k1]
  have ht12 : 1 ≤ t ^ 12 := one_le_pow₀ C.t1
  have ht10 : t ^ 10 ≤ t ^ 12 := pow_le_pow_right₀ C.t1 (by norm_num)
  have hb : t ^ 10 + t ^ 12 * (1 / κ₀) + 1 ≤ 3 * t ^ 12 * (1 / κ₀) := by
    have := mul_le_mul_of_nonneg_left hk (by positivity : (0 : ℝ) ≤ t ^ 12)
    linarith
  have e2 : epsBL d p h = vth d * (t ^ 10 + t ^ 12 * (1 / κ₀) + 1) := by
    unfold epsBL; rw [e]; ring
  rw [e2]
  calc vth d * (t ^ 10 + t ^ 12 * (1 / κ₀) + 1) ≤ 1 / (d : ℝ) ^ 2 * (3 * t ^ 12 * (1 / κ₀)) :=
        mul_le_mul hv hb (by positivity) (by positivity)
    _ = t ^ 12 / (d : ℝ) ^ 2 * (3 / κ₀) := by ring
    _ ≤ 1 / t ^ 22 * (3 / κ₀) :=
        mul_le_mul_of_nonneg_right (pow_div_le_pf C.t1 C.d34 _ _ (by norm_num)) (by positivity)
    _ = 3 * (1 / (κ₀ * t ^ 22)) := by ring
    _ ≤ 3 * (1 / (κ₀ ^ 2 * t ^ 3)) :=
        mul_le_mul_of_nonneg_left (C.kinv_le_W (by norm_num)) (by norm_num)

theorem Gam_le2 (C : LCtx_pf d p κ₀ h t) : GamP d p ≤ 2 / t ^ 2 := by
  have h17 : (p : ℝ) ^ 17 ≤ (1 : ℝ) ^ 17 * (d : ℝ) ^ 2 := by
    rw [one_pow, one_mul]; exact_mod_cast C.treg.hpd
  have hG := GamP_le_pf C.treg one_pos h17
  rw [Real.one_rpow, mul_one, C.hPt] at hG
  have h3 : Real.sqrt 3 ≤ 2 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  exact hG.trans (div_le_div_of_nonneg_right h3 (by have := C.t0; positivity))

theorem Gam_sq_le (C : LCtx_pf d p κ₀ h t) : GamP d p ^ 2 ≤ 4 * (1 / (κ₀ ^ 2 * t ^ 3)) := by
  have := C.t0
  have h2 : GamP d p ^ 2 ≤ (2 / t ^ 2) ^ 2 := pow_le_pow_left₀ GamP_nonneg_pf C.Gam_le2 2
  have e : (2 / t ^ 2) ^ 2 = 4 * (1 / t ^ 4) := by ring
  have := C.inv_le_W (m := 3) (n := 4) (by norm_num)
  linarith

theorem X_le (C : LCtx_pf d p κ₀ h t) :
    (p : ℝ) ^ 3 * Real.sqrt ((p : ℝ) * dbar d p / d) ≤ 2 * (1 / (κ₀ ^ 2 * t ^ 3)) := by
  have := C.t0
  have hX : (p : ℝ) * ((p : ℝ) ^ 3 * Real.sqrt ((p : ℝ) * dbar d p / d)) = GamP d p := by
    unfold GamP; ring
  have hΓt : GamP d p * t ^ 2 ≤ 2 := (le_div_iff₀ (by positivity)).mp C.Gam_le2
  have h4 : (p : ℝ) ^ 3 * Real.sqrt ((p : ℝ) * dbar d p / d) ≤ 2 * (1 / t ^ 4) := by
    rw [mul_one_div, le_div_iff₀ (by positivity)]
    calc (p : ℝ) ^ 3 * Real.sqrt ((p : ℝ) * dbar d p / d) * t ^ 4 =
          ((p : ℝ) * ((p : ℝ) ^ 3 * Real.sqrt ((p : ℝ) * dbar d p / d))) * t ^ 2 := by
            rw [C.hPt]; ring
      _ = GamP d p * t ^ 2 := by rw [hX]
      _ ≤ 2 := hΓt
  have := C.inv_le_W (m := 3) (n := 4) (by norm_num)
  linarith

theorem xi_le (C : LCtx_pf d p κ₀ h t) :
    xiP d p h ≤ Real.sqrt h + 9 * (1 / (κ₀ ^ 2 * t ^ 5)) := by
  have h1 := xiP_le_pf C.treg C.ht C.hPt C.hDt h
  have h2 := C.inv_le_W (m := 5) (n := 5) le_rfl
  have e : (9 : ℝ) / t ^ 5 = 9 * (1 / t ^ 5) := by ring
  linarith

theorem B0_le (C : LCtx_pf d p κ₀ h t) : B0P d p h ≤ 3 * (1 / (κ₀ ^ 2 * t ^ 5)) := by
  have := C.k0; have := C.t0
  have e1 : (p : ℝ) / (d * h) = t ^ 10 / d * (1 / κ₀) := by
    calc (p : ℝ) / (d * h) = (p : ℝ) * (1 / (d : ℝ)) * (1 / h) := by ring
      _ = t ^ 10 / d * (1 / κ₀) := by rw [C.inv_h, C.hPt]; ring
  have e2 : 1 / ((d : ℝ) * h * Real.sqrt h) = t ^ 12 / d * (1 / (κ₀ * Real.sqrt κ₀)) := by
    calc 1 / ((d : ℝ) * h * Real.sqrt h) = 1 / (d : ℝ) * (1 / h) * (1 / Real.sqrt h) := by ring
      _ = t ^ 12 / d * (1 / (κ₀ * Real.sqrt κ₀)) := by rw [C.inv_h, C.inv_sqrt_h]; ring
  have b1 : (p : ℝ) / (d * h) ≤ 1 / (κ₀ ^ 2 * t ^ 5) := by
    rw [e1]
    calc t ^ 10 / d * (1 / κ₀) ≤ 1 / t ^ 7 * (1 / κ₀) :=
          mul_le_mul_of_nonneg_right (pow_div_le_pf C.t1 C.hDt _ _ (by norm_num))
            (by positivity)
      _ = 1 / (κ₀ * t ^ 7) := by ring
      _ ≤ 1 / (κ₀ ^ 2 * t ^ 5) := C.kinv_le_W (by norm_num)
  have b2 : 1 / ((d : ℝ) * h * Real.sqrt h) ≤ 1 / (κ₀ ^ 2 * t ^ 5) := by
    rw [e2]
    calc t ^ 12 / d * (1 / (κ₀ * Real.sqrt κ₀)) ≤ 1 / t ^ 5 * (1 / κ₀ ^ 2) :=
          mul_le_mul (pow_div_le_pf C.t1 C.hDt _ _ (by norm_num)) C.kk_le (by positivity)
            (by positivity)
      _ = 1 / (κ₀ ^ 2 * t ^ 5) := by ring
  have b3 : vth d ≤ 1 / (κ₀ ^ 2 * t ^ 5) := C.vth_le.trans (C.inv_le_W (by norm_num))
  unfold B0P
  linarith

theorem e_mul_le (C : LCtx_pf d p κ₀ h t) :
    eP d p h * (h ^ ((3 : ℝ) / 4) + Real.sqrt (1 / (d * h)) + Real.sqrt (thP d)) ≤
      6 * (1 / (κ₀ ^ 2 * t ^ 5)) := by
  have := C.k0; have := C.t0; have := C.h0
  have he : eP d p h = GamP d p / κ₀ := eP_eq_pf C.treg C.k0 C.hh
  have he2 : eP d p h ≤ 2 * (1 / (κ₀ * t ^ 2)) := by
    rw [he]
    calc GamP d p / κ₀ ≤ 2 / t ^ 2 / κ₀ := div_le_div_of_nonneg_right C.Gam_le2 C.k0.le
      _ = 2 * (1 / (κ₀ * t ^ 2)) := by ring
  have s1 : h ^ ((3 : ℝ) / 4) ≤ 1 / (κ₀ * t ^ 4) := by
    calc h ^ ((3 : ℝ) / 4) ≤ Real.sqrt h := by
          rw [Real.sqrt_eq_rpow]
          exact Real.rpow_le_rpow_of_exponent_ge C.h0 C.h1 (by norm_num)
      _ = Real.sqrt κ₀ / t ^ 4 := C.sqrt_h
      _ ≤ 1 / t ^ 4 := div_le_div_of_nonneg_right C.sk1 (by positivity)
      _ ≤ 1 / (κ₀ * t ^ 4) := C.inv_le_kinv 4
  have s2 : Real.sqrt (1 / (d * h)) ≤ 1 / (κ₀ * t ^ 4) := by
    rw [Real.sqrt_le_left (by positivity)]
    have e : 1 / ((d : ℝ) * h) = t ^ 8 / d * (1 / κ₀) := by
      calc 1 / ((d : ℝ) * h) = 1 / (d : ℝ) * (1 / h) := by ring
        _ = t ^ 8 / d * (1 / κ₀) := by rw [C.inv_h]; ring
    rw [e]
    calc t ^ 8 / d * (1 / κ₀) ≤ 1 / t ^ 9 * (1 / κ₀) :=
          mul_le_mul_of_nonneg_right (pow_div_le_pf C.t1 C.hDt _ _ (by norm_num))
            (by positivity)
      _ = 1 / (κ₀ * t ^ 9) := by ring
      _ ≤ 1 / (κ₀ ^ 2 * t ^ 8) := C.kinv_le_W (by norm_num)
      _ = (1 / (κ₀ * t ^ 4)) ^ 2 := by ring
  have s3 : Real.sqrt (thP d) ≤ 1 / (κ₀ * t ^ 4) := by
    have e : Real.sqrt (thP d) = 1 / (d : ℝ) := by
      unfold thP
      rw [Real.sqrt_div' _ (by positivity), Real.sqrt_one, Real.sqrt_sq C.D0.le]
    rw [e]
    exact C.invD_le.trans ((inv_pow_anti_pf C.t1 (by norm_num : 4 ≤ 17)).trans
      (C.inv_le_kinv 4))
  have hS0 : 0 ≤ h ^ ((3 : ℝ) / 4) + Real.sqrt (1 / (d * h)) + Real.sqrt (thP d) := by
    positivity
  calc eP d p h * (h ^ ((3 : ℝ) / 4) + Real.sqrt (1 / (d * h)) + Real.sqrt (thP d)) ≤
        2 * (1 / (κ₀ * t ^ 2)) * (3 * (1 / (κ₀ * t ^ 4))) :=
        mul_le_mul he2 (by linarith) hS0 (by positivity)
    _ = 6 * (1 / (κ₀ ^ 2 * t ^ 6)) := by ring
    _ ≤ 6 * (1 / (κ₀ ^ 2 * t ^ 5)) :=
        mul_le_mul_of_nonneg_left (C.k2inv_le_W (by norm_num)) (by norm_num)

theorem ErrRC3_le (C : LCtx_pf d p κ₀ h t) :
    ErrRC3 d p h ≤ GamP d p ^ 2 / κ₀ ^ 2 + Real.sqrt h + 18 * (1 / (κ₀ ^ 2 * t ^ 5)) := by
  have he : eP d p h ^ 2 = GamP d p ^ 2 / κ₀ ^ 2 := by
    rw [eP_eq_pf C.treg C.k0 C.hh, div_pow]
  have h1 := C.B0_le
  have h2 := C.e_mul_le
  have h3 := C.xi_le
  unfold ErrRC3
  linarith

theorem TotErr_le (C : LCtx_pf d p κ₀ h t) :
    TotErr d p h ≤ GamP d p + (p : ℝ) * (GamP d p ^ 2 / κ₀ ^ 2) +
      2 * ((p : ℝ) * Real.sqrt h) + 35 * (1 / (κ₀ ^ 2 * t ^ 3)) := by
  have hp0 := C.p0
  have a11 : (p : ℝ) * ErrRC3 d p h ≤ (p : ℝ) * (GamP d p ^ 2 / κ₀ ^ 2) +
      (p : ℝ) * Real.sqrt h + 18 * (1 / (κ₀ ^ 2 * t ^ 3)) := by
    have h1 := mul_le_mul_of_nonneg_left C.ErrRC3_le hp0.le
    have h2 := C.PU
    linarith
  have a1 := C.Gam_sq_le
  have a2 : epsS d p ≤ 1 / (κ₀ ^ 2 * t ^ 3) :=
    (epsS_le_pf C.ht C.hPt C.hDt).trans (C.inv_le_W (by norm_num))
  have a3 : η0Of d p ≤ 1 / (κ₀ ^ 2 * t ^ 3) := C.eta_le.trans (C.inv_le_W (by norm_num))
  have a4 : 1 / (d : ℝ) ≤ 1 / (κ₀ ^ 2 * t ^ 3) := C.invD_le.trans (C.inv_le_W (by norm_num))
  have a5 : (p : ℝ) ^ 13 / (d : ℝ) ^ 2 ≤ 1 / (κ₀ ^ 2 * t ^ 3) :=
    C.p13_le.trans (C.inv_le_W (by norm_num))
  have a6 : vth d ≤ 1 / (κ₀ ^ 2 * t ^ 3) := C.vth_le.trans (C.inv_le_W (by norm_num))
  have a7 : (p : ℝ) ^ 5 / d ≤ 1 / (κ₀ ^ 2 * t ^ 3) :=
    (C.pk_div_le 5 7 (by norm_num)).trans (C.inv_le_W (by norm_num))
  have a8 := C.p2Dh_le
  have a9 := C.pDhh_le
  have a10 := C.epsBL_le
  have a12 := C.X_le
  unfold TotErr
  linarith

/-- The critical terms: `Γ + p e² + 2 p √h ≤ 3 (√κ₀ + c₀^{17/3} + κ₀⁻² c₀^{34/3}) / p`. -/
theorem crit_le (C : LCtx_pf d p κ₀ h t) {c₀ : ℝ} (hc0 : 0 < c₀)
    (hpc : (p : ℝ) ^ 17 ≤ c₀ ^ 17 * (d : ℝ) ^ 2) :
    GamP d p + (p : ℝ) * (GamP d p ^ 2 / κ₀ ^ 2) + 2 * ((p : ℝ) * Real.sqrt h) ≤
      3 * (Real.sqrt κ₀ + c₀ ^ ((17 : ℝ) / 3) + κ₀⁻¹ ^ 2 * c₀ ^ ((34 : ℝ) / 3)) *
        (1 / (p : ℝ)) := by
  have hp0 := C.p0
  have := C.k0; have := C.t0
  have hΓ := GamP_le_pf C.treg hc0 hpc
  have hw0 : 0 ≤ c₀ ^ ((17 : ℝ) / 3) := by positivity
  rw [c0_sq_pf hc0.le]
  set w := c₀ ^ ((17 : ℝ) / 3)
  have h3 : Real.sqrt 3 ≤ 3 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hiP : 0 ≤ 1 / (p : ℝ) := by positivity
  have c1 : GamP d p ≤ 3 * w * (1 / (p : ℝ)) := by
    calc GamP d p ≤ Real.sqrt 3 * w / p := hΓ
      _ = Real.sqrt 3 * w * (1 / (p : ℝ)) := by ring
      _ ≤ 3 * w * (1 / (p : ℝ)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h3 hw0) hiP
  have c2 : (p : ℝ) * GamP d p ^ 2 ≤ 3 * w ^ 2 * (1 / (p : ℝ)) := by
    have a : GamP d p * p ≤ Real.sqrt 3 * w := (le_div_iff₀ hp0).mp hΓ
    have b : (GamP d p * p) ^ 2 ≤ (Real.sqrt 3 * w) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg GamP_nonneg_pf hp0.le) a 2
    have c : (Real.sqrt 3 * w) ^ 2 = 3 * w ^ 2 := by rw [mul_pow, Real.sq_sqrt (by norm_num)]
    rw [mul_one_div, le_div_iff₀ hp0]
    linarith
  have c2' : (p : ℝ) * (GamP d p ^ 2 / κ₀ ^ 2) ≤ 3 * (κ₀⁻¹ ^ 2 * w ^ 2) * (1 / (p : ℝ)) := by
    have e1 : (p : ℝ) * (GamP d p ^ 2 / κ₀ ^ 2) = ((p : ℝ) * GamP d p ^ 2) * κ₀⁻¹ ^ 2 := by
      rw [inv_pow]; ring
    have e2 : 3 * (κ₀⁻¹ ^ 2 * w ^ 2) * (1 / (p : ℝ)) =
        (3 * w ^ 2 * (1 / (p : ℝ))) * κ₀⁻¹ ^ 2 := by ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_right c2 (by positivity)
  have c3 : (p : ℝ) * Real.sqrt h = Real.sqrt κ₀ * (1 / (p : ℝ)) := by
    rw [C.sqrt_h, C.hPt, mul_div_assoc', mul_one_div,
      div_eq_div_iff (by positivity) (by positivity)]
    ring
  have c4 : 0 ≤ Real.sqrt κ₀ * (1 / (p : ℝ)) := mul_nonneg (Real.sqrt_nonneg _) hiP
  linarith

end LCtx_pf

theorem ledger_real_pf (K : ℝ) : ∃ Ccrit : ℝ, 0 < Ccrit ∧ ∀ c₀ κ₀ : ℝ, 0 < c₀ → c₀ ≤ 1 →
    0 < κ₀ → κ₀ ≤ 1 →
    Ccrit * (Real.sqrt κ₀ + c₀ ^ ((17 : ℝ) / 3) + κ₀⁻¹ ^ 2 * c₀ ^ ((34 : ℝ) / 3)) ≤ 1 / 8 →
    ∃ P₀ : ℕ, ∀ (d p : ℕ) (h : ℝ), Reg κ₀ d p h → (p : ℝ) ≤ c₀ * (d : ℝ) ^ ((2 : ℝ) / 17) →
      P₀ ≤ p →
      2 * (1 + 9 / (d : ℝ)) * cpP p + K * TotErr d p h + 2 * η0Of d p < 1 / (p : ℝ) := by
  refine ⟨24 * (|K| + 1), by positivity, ?_⟩
  intro c₀ κ₀ hc0 _ hk0 hk1 hcrit
  refine ⟨⌈(400 * (|K| + 1) / κ₀ ^ 2) ^ 2⌉₊, ?_⟩
  intro d p h hReg hpc hp
  have hR := hReg.treg
  obtain ⟨ht, hPt, hDt⟩ := ledger_t_pf hR
  have C : LCtx_pf d p κ₀ h (Real.sqrt p) := ⟨hR, ht, hPt, hDt, hk0, hk1, hReg.hh⟩
  have hT0 : 0 ≤ 400 * (|K| + 1) / κ₀ ^ 2 := by positivity
  have htT : 400 * (|K| + 1) / κ₀ ^ 2 ≤ Real.sqrt p := by
    rw [Real.le_sqrt hT0 (by positivity)]
    exact (Nat.le_ceil _).trans (by exact_mod_cast hp)
  have hpc17 : (p : ℝ) ^ 17 ≤ c₀ ^ 17 * (d : ℝ) ^ 2 := by
    calc (p : ℝ) ^ 17 ≤ (c₀ * (d : ℝ) ^ ((2 : ℝ) / 17)) ^ 17 :=
          pow_le_pow_left₀ (by positivity) hpc 17
      _ = c₀ ^ 17 * (d : ℝ) ^ 2 := by rw [mul_pow, rpow_two_div_seventeen_pow]
  have hTot := C.TotErr_le
  have hcr := C.crit_le hc0 hpc17
  have hTot0 := TotErr_nonneg_pf hR C.h0
  have hη := C.eta_le
  have hcp := cp_le_pf hR
  have ht0 := C.t0
  have ht1 := C.t1
  set t := Real.sqrt (p : ℝ) with htdef
  set Z := Real.sqrt κ₀ + c₀ ^ ((17 : ℝ) / 3) + κ₀⁻¹ ^ 2 * c₀ ^ ((34 : ℝ) / 3) with hZ
  have hZ0 : 0 ≤ Z := by positivity
  have hKZ : |K| * Z ≤ 1 / 192 := by
    have := abs_nonneg K
    linarith
  have hpt : (1 : ℝ) / p = 1 / t ^ 2 := by rw [hPt]
  rw [hpt] at hcr hcp ⊢
  have hiP : 0 < 1 / t ^ 2 := by positivity
  have hKT : K * TotErr d p h ≤ |K| * TotErr d p h :=
    mul_le_mul_of_nonneg_right (le_abs_self K) hTot0
  have hKT2 : |K| * TotErr d p h ≤ |K| * (3 * Z * (1 / t ^ 2) + 35 * (1 / (κ₀ ^ 2 * t ^ 3))) :=
    mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg K)
  have hKZp : |K| * (3 * Z * (1 / t ^ 2)) ≤ 3 / 192 * (1 / t ^ 2) := by
    have := mul_le_mul_of_nonneg_right hKZ hiP.le
    linarith
  have hkT : 400 * (|K| + 1) ≤ κ₀ ^ 2 * t := by
    have hk0' := hk0.ne'
    have e : κ₀ ^ 2 * (400 * (|K| + 1) / κ₀ ^ 2) = 400 * (|K| + 1) := by field_simp
    calc 400 * (|K| + 1) = κ₀ ^ 2 * (400 * (|K| + 1) / κ₀ ^ 2) := e.symm
      _ ≤ κ₀ ^ 2 * t := mul_le_mul_of_nonneg_left htT (by positivity)
  have hrest : |K| * (35 * (1 / (κ₀ ^ 2 * t ^ 3))) ≤ 1 / 10 * (1 / t ^ 2) := by
    rw [show |K| * (35 * (1 / (κ₀ ^ 2 * t ^ 3))) = 35 * |K| / (κ₀ ^ 2 * t ^ 3) by ring,
      show (1 : ℝ) / 10 * (1 / t ^ 2) = 1 / (10 * t ^ 2) by ring,
      div_le_div_iff₀ (by positivity) (by positivity)]
    have := mul_le_mul_of_nonneg_right hkT (sq_nonneg t)
    have := mul_nonneg (abs_nonneg K) (sq_nonneg t)
    have := sq_nonneg t
    linarith
  have hη2 : 2 * η0Of d p ≤ 1 / 10 * (1 / t ^ 2) := by
    have h7 : 1000 ≤ t ^ 7 := le_trans ht (le_self_pow₀ ht1 (by norm_num))
    have : 2 * (1 / t ^ 9) ≤ 1 / 10 * (1 / t ^ 2) := by
      rw [mul_one_div, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      have := mul_le_mul_of_nonneg_right h7 (sq_nonneg t)
      have := sq_nonneg t
      linarith
    linarith
  linarith

end BiluLinial.Tight
