/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecB.Defs

/-!
# Parameter arithmetic for Section B

Node TB.exp of `docs/tight/BP_SECB.md` (AUDIT-B §1, "standing numerical facts"). At
`p = ⌊c₀ d^{2/17}⌋` and `h = κ₀ p^{-4}`:

* `eventually_base B`: eventually `TRegime d p`, `p ≥ B`, `p^17 ≤ d²` and `h = κ₀/p⁴`;
* `p⁸ ≤ d` (from `p^16 ≤ p^17 ≤ d²`), `p⁵ ≤ q`;
* `ε = r - 1 = η₀/2` satisfies `0 ≤ ε`, `ε² ≤ 1/(p q)` (from `q η₀² = Δ (1 - η₀) ≤ 4/p`), hence
  `ε ≤ 1/p³` once `p⁵ ≤ q`.
-/

@[expose] public section

namespace BiluLinial.Tight.SecB

variable {d p : ℕ}

/-- The base regime at `p = ⌊c₀ d^{2/17}⌋`, `h = κ₀ p^{-4}`, with `p ≥ B`. -/
theorem eventually_base (B : ℝ) : Eventually fun _ κ₀ d p h =>
    TRegime d p ∧ B ≤ (p : ℝ) ∧ (p : ℝ) ^ 17 ≤ (d : ℝ) ^ 2 ∧ h = κ₀ / (p : ℝ) ^ 4 ∧
      0 < κ₀ ∧ κ₀ ≤ 1 := by
  intro c₀ κ₀ hc0 hc1 hk0 hk1
  obtain ⟨D₁, hD₁⟩ := exists_tRegime_pAt hc0 hc1
  obtain ⟨D₂, hD₂⟩ := exists_base_ge hc0 (2 * |B| + 2)
  refine ⟨max D₁ D₂, fun d hd => ?_⟩
  obtain ⟨hR, hb⟩ := hD₁ d (le_of_max_le_left hd)
  have hb2 := hD₂ d (le_of_max_le_right hd)
  have hp := half_base_le_pAt hb
  refine ⟨hR, ?_, ?_, rfl, hk0, hk1⟩
  · have := le_abs_self B
    linarith
  · exact_mod_cast hR.hpd

theorem regime_p_pos (hR : TRegime d p) : (0 : ℝ) < p := by
  have : (2 : ℝ) ≤ p := by exact_mod_cast hR.two_le_p
  linarith

/-- `p⁸ ≤ d`. -/
theorem regime_p8_le (hR : TRegime d p) : (p : ℝ) ^ 8 ≤ d := by
  have hp1 : (1 : ℝ) ≤ p := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hR.two_le_p
    linarith
  have h17 : (p : ℝ) ^ 17 ≤ (d : ℝ) ^ 2 := by exact_mod_cast hR.hpd
  have h16 : ((p : ℝ) ^ 8) ^ 2 ≤ (d : ℝ) ^ 2 := by
    calc ((p : ℝ) ^ 8) ^ 2 = (p : ℝ) ^ 16 := by ring
      _ ≤ (p : ℝ) ^ 17 := pow_le_pow_right₀ hp1 (by norm_num)
      _ ≤ (d : ℝ) ^ 2 := h17
  exact (pow_le_pow_iff_left₀ (by positivity) (Nat.cast_nonneg d) (by norm_num)).mp h16

/-- `p⁵ ≤ q = d - 1`. -/
theorem regime_p5_le_q (hR : TRegime d p) : (p : ℝ) ^ 5 ≤ qOf d := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hR.two_le_p
  have h8 := regime_p8_le hR
  have : (p : ℝ) ^ 5 + 1 ≤ (p : ℝ) ^ 8 := by
    have h3 : (p : ℝ) ^ 8 = (p : ℝ) ^ 5 * (p : ℝ) ^ 3 := by ring
    have h4 : (8 : ℝ) ≤ (p : ℝ) ^ 3 := by
      have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hp2 3
      norm_num at this ⊢
      linarith
    have h5 : (1 : ℝ) ≤ (p : ℝ) ^ 5 := one_le_pow₀ (by linarith)
    nlinarith
  rw [qOf]
  linarith

theorem regime_eps_nonneg (hR : TRegime d p) : 0 ≤ epsP d p := by
  have := hR.η0Of_pos
  rw [epsP, rOf]
  linarith

/-- `ε² ≤ 1/(p q)`: from `q η₀² = Δ (1 - η₀) ≤ Δ = 4/p`. -/
theorem regime_eps_sq_le (hR : TRegime d p) : epsP d p ^ 2 * ((p : ℝ) * qOf d) ≤ 1 := by
  have hq := hR.qOf_pos
  have hp := regime_p_pos hR
  have he := hR.η0Of_eq
  have h0 := hR.η0Of_pos
  have hε : epsP d p = η0Of d p / 2 := by rw [epsP, rOf]; ring
  rw [hε]
  have hΔ : ΔOf p * (p : ℝ) = 4 := by rw [ΔOf]; field_simp
  have : qOf d * η0Of d p ^ 2 * p ≤ 4 := by
    rw [he]
    nlinarith [hR.ΔOf_pos]
  nlinarith

/-- `ε ≤ 1/p³` (using `p⁵ ≤ q`). -/
theorem regime_eps_le (hR : TRegime d p) : epsP d p ≤ 1 / (p : ℝ) ^ 3 := by
  have hp := regime_p_pos hR
  have h5 := regime_p5_le_q hR
  have hsq := regime_eps_sq_le hR
  have he0 := regime_eps_nonneg hR
  have h6 : epsP d p ^ 2 * (p : ℝ) ^ 6 ≤ 1 := by
    have : (p : ℝ) ^ 6 ≤ (p : ℝ) * qOf d := by
      calc (p : ℝ) ^ 6 = (p : ℝ) * (p : ℝ) ^ 5 := by ring
        _ ≤ (p : ℝ) * qOf d := mul_le_mul_of_nonneg_left h5 hp.le
    nlinarith [sq_nonneg (epsP d p)]
  have h3 : epsP d p * (p : ℝ) ^ 3 ≤ 1 := by
    have : (epsP d p * (p : ℝ) ^ 3) ^ 2 ≤ 1 := by nlinarith
    nlinarith [sq_nonneg (epsP d p * (p : ℝ) ^ 3 - 1), mul_nonneg he0 (pow_pos hp 3).le]
  rw [le_div_iff₀ (by positivity)]
  exact h3

end BiluLinial.Tight.SecB
