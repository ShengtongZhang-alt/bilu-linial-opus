/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.Contact.RealParams
public import BiluLinial.Tight.Contact.Real

/-!
# Real-number parts of CR1 and D9a on the GCI-free route

Pure real inequalities used by `cr1` (`Contact/RouteDR1.lean`) and `d9a`
(`Contact/RouteDR1D9a.lean`). Witnesses and checks: `docs/tight/CHECK_CONTACT_LEAVES.md` §6.
-/

@[expose] public section

namespace BiluLinial.Tight

/-! ### Helpers -/

/-- `√x ≤ √k √y` from `x ≤ k y`. -/
theorem rr_sqrt_le {x k y : ℝ} (hk : 0 ≤ k) (h : x ≤ k * y) :
    Real.sqrt x ≤ Real.sqrt k * Real.sqrt y :=
  (Real.sqrt_le_sqrt h).trans_eq (Real.sqrt_mul hk y)

/-- The callback bound `E ≤ C_C X + C_C ϑ` with `X ≤ B T + u` gives
`E ≤ (|C_C| (B + 1) + 1)(T + u + ϑ)`. -/
theorem rr_absorb {E CC X B T u v : ℝ} (hB : 0 ≤ B) (hT : 0 ≤ T) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hX0 : 0 ≤ X) (hX : X ≤ B * T + u) (hE : E ≤ CC * X + CC * v) :
    E ≤ (|CC| * (B + 1) + 1) * (T + u + v) := by
  have hc := abs_nonneg CC
  have h1 : CC * X ≤ |CC| * X := mul_le_mul_of_nonneg_right (le_abs_self _) hX0
  have h2 : |CC| * X ≤ |CC| * (B * T + u) := mul_le_mul_of_nonneg_left hX hc
  have h3 : CC * v ≤ |CC| * v := mul_le_mul_of_nonneg_right (le_abs_self _) hv
  have h4 : B * T + u + v ≤ (B + 1) * (T + u + v) := by
    linarith [mul_nonneg hB hu, mul_nonneg hB hv]
  have h5 := mul_le_mul_of_nonneg_left h4 hc
  have h6 : 0 ≤ T + u + v := by linarith
  calc E ≤ |CC| * (B * T + u + v) := by linarith
    _ ≤ |CC| * ((B + 1) * (T + u + v)) := h5
    _ ≤ (|CC| * (B + 1) + 1) * (T + u + v) := by linarith

/-- `1/d ≤ 4 a²`. -/
theorem TRegime.rr_inv_d {d p : ℕ} (hR : TRegime d p) : 1 / (d : ℝ) ≤ 4 * aOf d p ^ 2 := by
  have hd0 := hR.pfA_d_pos
  have h := hR.pf_a_sq_ge
  rw [div_le_iff₀ (by linarith : (0 : ℝ) < 4 * d)] at h
  rw [div_le_iff₀ hd0]
  linarith

/-- `p δ̄ ≤ 1`. -/
theorem TRegime.rr_p_dbar {d p : ℕ} (hR : TRegime d p) : (p : ℝ) * dbar d p ≤ 1 := by
  have h1 : (p : ℝ) ≤ (p : ℝ) ^ 2 := le_self_pow₀ hR.pfA_one_le_p two_ne_zero
  have h2 := mul_le_mul_of_nonneg_right h1 hR.pfA_dbar_nonneg
  linarith [hR.pfA_p2_dbar]

/-- `D/d ≤ 4 a² D` for `D ≥ 0`. -/
theorem TRegime.rr_div_d_le {d p : ℕ} (hR : TRegime d p) {D : ℝ} (hD : 0 ≤ D) :
    D / d ≤ 4 * (aOf d p ^ 2 * D) :=
  calc D / d = D * (1 / d) := by ring
    _ ≤ D * (4 * aOf d p ^ 2) := mul_le_mul_of_nonneg_left hR.rr_inv_d hD
    _ = 4 * (aOf d p ^ 2 * D) := by ring

/-- `p⁴/d ≤ δ̄`. -/
theorem TRegime.rr_p4_le_dbar {d p : ℕ} (hR : TRegime d p) : (p : ℝ) ^ 4 / d ≤ dbar d p := by
  have h1 := hR.pfA_epsP_nonneg
  have h2 := pfA_cbrt_nonneg d p
  unfold dbar
  linarith

/-- The row term of D9a: `p⁵ √(4(S+1)/d · 4cδ/p) = √(16c) · p⁴ √(pδ/d) √(S+1)`. -/
theorem rr_row_eq {p d δ S c : ℝ} (hp : 0 < p) (hd : 0 < d) (hc : 0 ≤ c) (hδ : 0 ≤ δ) :
    p ^ 5 * Real.sqrt (4 * (S + 1) / d * (4 * c * δ / p)) =
      Real.sqrt (16 * c) * (p ^ 4 * Real.sqrt (p * δ / d) * Real.sqrt (S + 1)) := by
  have hp' := hp.ne'
  have hd' := hd.ne'
  have e1 : p ^ 2 * (4 * (S + 1) / d * (4 * c * δ / p)) = 16 * c * (p * δ / d * (S + 1)) := by
    field_simp
    ring
  have e2 : p * Real.sqrt (4 * (S + 1) / d * (4 * c * δ / p)) =
      Real.sqrt (p ^ 2 * (4 * (S + 1) / d * (4 * c * δ / p))) := by
    rw [Real.sqrt_mul (sq_nonneg p), Real.sqrt_sq hp.le]
  have h16 : (0 : ℝ) ≤ 16 * c := by linarith
  have hy : 0 ≤ p * δ / d := div_nonneg (mul_nonneg hp.le hδ) hd.le
  calc p ^ 5 * Real.sqrt (4 * (S + 1) / d * (4 * c * δ / p)) =
        p ^ 4 * (p * Real.sqrt (4 * (S + 1) / d * (4 * c * δ / p))) := by ring
    _ = p ^ 4 * Real.sqrt (16 * c * (p * δ / d * (S + 1))) := by rw [e2, e1]
    _ = p ^ 4 * (Real.sqrt (16 * c) * (Real.sqrt (p * δ / d) * Real.sqrt (S + 1))) := by
        rw [Real.sqrt_mul h16, Real.sqrt_mul hy]
    _ = Real.sqrt (16 * c) * (p ^ 4 * Real.sqrt (p * δ / d) * Real.sqrt (S + 1)) := by ring

/-- The core term of D9a: `p⁴ √(K₁ p/d · K₂ δ) = √(K₁ K₂) · p⁴ √(pδ/d)`. -/
theorem rr_core_eq {p d δ K₁ K₂ : ℝ} (hK : 0 ≤ K₁ * K₂) :
    p ^ 4 * Real.sqrt (K₁ * p / d * (K₂ * δ)) =
      Real.sqrt (K₁ * K₂) * (p ^ 4 * Real.sqrt (p * δ / d)) := by
  rw [show K₁ * p / d * (K₂ * δ) = K₁ * K₂ * (p * δ / d) by ring, Real.sqrt_mul hK]
  ring

/-- **R-CR1′** [route DR1] (real part of CR1 from CR3′). With `λ' = max(M, 2C₂ + 1) δ̄`, take
`λ_r = λ_c = max(4, C_M) λ`, `δ_c = max(4, C_M) λ'` (MARKENV with `λ` and with `λ'`, C2 for the
minus masses), and `ρ_Δ = max(4 C_D δ̄/p, ϑ)` (DR1 at the root and `1/d ≤ 4a²`). Then
`p⁵√(λ_r ρ_Δ) + p⁴√(λ_c δ_c) ≤ C p⁵ √(λ δ̄)`. -/
theorem cr1_real_dr1 (CC CM C₂ CD M : ℝ) : ∃ C : ℝ, 0 < C ∧ ∃ P₀ : ℕ, ∀ d p : ℕ,
    TRegime d p → P₀ ≤ p → ∀ S Sm A2 B2 fP fM Dv R Gt lam : ℝ,
      (∀ l : ℝ, aOf d p ^ 2 * S + A2 ≤ l → vth d ≤ l →
        S / d ≤ 4 * l ∧ fP / (d : ℝ) ^ 2 ≤ CM * l) →
      (∀ l : ℝ, aOf d p ^ 2 * Sm + B2 ≤ l → vth d ≤ l →
        Sm / d ≤ 4 * l ∧ fM / (d : ℝ) ^ 2 ≤ CM * l) →
      aOf d p ^ 2 * Sm ≤ C₂ * dbar d p → B2 ≤ C₂ * dbar d p →
      0 ≤ Dv → aOf d p ^ 2 * Dv ≤ CD * dbar d p / p →
      (∀ lr rd lc dc : ℝ, vth d ≤ lr → lr ≤ lc → lc ≤ dc → dc ≤ 1 → vth d ≤ rd →
        S / d ≤ lr → Sm / d ≤ dc → Dv / d ≤ rd →
        fP / (d : ℝ) ^ 2 ≤ lc → fM / (d : ℝ) ^ 2 ≤ dc →
        |R - Gt| ≤ CC * ((p : ℝ) ^ 5 * Real.sqrt (lr * rd) + (p : ℝ) ^ 4 * Real.sqrt (lc * dc) +
          (p : ℝ) ^ 13 / (d : ℝ) ^ 2) + CC * vth d) →
      aOf d p ^ 2 * S + A2 ≤ lam → vth d ≤ lam → lam ≤ M * dbar d p →
      |R - Gt| ≤ C * ((p : ℝ) ^ 5 * Real.sqrt (lam * dbar d p) +
        (p : ℝ) ^ 13 / (d : ℝ) ^ 2 + vth d) := by
  obtain ⟨K, hK4, hKM⟩ : ∃ K : ℝ, 4 ≤ K ∧ CM ≤ K :=
    ⟨max 4 CM, le_max_left _ _, le_max_right _ _⟩
  obtain ⟨M', hM'1, hM'2⟩ : ∃ M' : ℝ, M ≤ M' ∧ 2 * C₂ + 1 ≤ M' :=
    ⟨max M (2 * C₂ + 1), le_max_left _ _, le_max_right _ _⟩
  have hK0 : 0 ≤ K := by linarith
  have hB0 : 0 ≤ Real.sqrt (K * (4 * |CD| + 1)) + Real.sqrt (K * (K * |M'|)) :=
    add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  refine ⟨|CC| * (Real.sqrt (K * (4 * |CD| + 1)) + Real.sqrt (K * (K * |M'|)) + 1) + 1,
    by positivity, ⌈K * |M'|⌉₊, fun d p hR hp => ?_⟩
  intro S Sm A2 B2 fP fM Dv R Gt lam hMP hMM hSm hB2 hDv0 hDv hcb hl1 hl2 hl3
  have hp0 := hR.pfA_p_pos
  have hp1 := hR.pfA_one_le_p
  have hϑ0 := pfA_vth_nonneg d
  have hdb0 := hR.pfA_dbar_nonneg
  have hϑδ := vth_le_dbar hR
  have hpdb := hR.rr_p_dbar
  have hlam0 : 0 ≤ lam := hϑ0.trans hl2
  have hKp : K * |M'| ≤ p := (Nat.le_ceil _).trans (by exact_mod_cast hp)
  -- the minus stage `λ' = M' δ̄`
  have hMd : lam ≤ M' * dbar d p := hl3.trans (mul_le_mul_of_nonneg_right hM'1 hdb0)
  have hlp1 : aOf d p ^ 2 * Sm + B2 ≤ M' * dbar d p := by
    have := mul_le_mul_of_nonneg_right hM'2 hdb0
    linarith
  have hlp2 : vth d ≤ M' * dbar d p := hl2.trans hMd
  have hlp0 : 0 ≤ M' * dbar d p := hϑ0.trans hlp2
  obtain ⟨hSd, hfP⟩ := hMP lam hl1 hl2
  obtain ⟨hSmd, hfM⟩ := hMM (M' * dbar d p) hlp1 hlp2
  -- the hypotheses of the callback
  have hc1 : vth d ≤ K * lam := hl2.trans (le_mul_of_one_le_left hlam0 (by linarith))
  have hc3 : K * lam ≤ K * (M' * dbar d p) := mul_le_mul_of_nonneg_left hMd hK0
  have hm : K * (M' * dbar d p) ≤ K * (|M'| * dbar d p) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_abs_self _) hdb0) hK0
  have hc4 : K * (M' * dbar d p) ≤ 1 := by
    have := mul_le_mul_of_nonneg_right hKp hdb0
    linarith
  have hc5 : vth d ≤ max (4 * |CD| * dbar d p / p) (vth d) := le_max_right _ _
  have hc6 : S / d ≤ K * lam := hSd.trans (mul_le_mul_of_nonneg_right hK4 hlam0)
  have hc7 : Sm / d ≤ K * (M' * dbar d p) := hSmd.trans (mul_le_mul_of_nonneg_right hK4 hlp0)
  have hc8 : Dv / d ≤ max (4 * |CD| * dbar d p / p) (vth d) := by
    refine le_trans ?_ (le_max_left _ _)
    have h1 : CD * dbar d p / p ≤ |CD| * dbar d p / p :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hdb0) hp0.le
    calc Dv / d ≤ 4 * (aOf d p ^ 2 * Dv) := hR.rr_div_d_le hDv0
      _ ≤ 4 * (|CD| * dbar d p / p) := by linarith
      _ = 4 * |CD| * dbar d p / p := by ring
  have hc9 : fP / (d : ℝ) ^ 2 ≤ K * lam := hfP.trans (mul_le_mul_of_nonneg_right hKM hlam0)
  have hc10 : fM / (d : ℝ) ^ 2 ≤ K * (M' * dbar d p) :=
    hfM.trans (mul_le_mul_of_nonneg_right hKM hlp0)
  have hmain := hcb (K * lam) (max (4 * |CD| * dbar d p / p) (vth d)) (K * lam)
    (K * (M' * dbar d p)) hc1 le_rfl hc3 hc4 hc5 hc6 hc7 hc8 hc9 hc10
  -- the square roots
  have hrd : max (4 * |CD| * dbar d p / p) (vth d) ≤ (4 * |CD| + 1) * dbar d p := by
    have hx0 : 0 ≤ 4 * |CD| * dbar d p := mul_nonneg (by positivity) hdb0
    refine max_le ?_ ?_
    · have h1 : 4 * |CD| * dbar d p / p ≤ 4 * |CD| * dbar d p := div_le_self hx0 hp1
      linarith
    · have := mul_nonneg (abs_nonneg CD) hdb0
      linarith
  have hx1 : K * lam * max (4 * |CD| * dbar d p / p) (vth d) ≤
      K * (4 * |CD| + 1) * (lam * dbar d p) :=
    (mul_le_mul_of_nonneg_left hrd (mul_nonneg hK0 hlam0)).trans_eq (by ring)
  have hx2 : K * lam * (K * (M' * dbar d p)) ≤ K * (K * |M'|) * (lam * dbar d p) :=
    (mul_le_mul_of_nonneg_left hm (mul_nonneg hK0 hlam0)).trans_eq (by ring)
  have hs1 := rr_sqrt_le (mul_nonneg hK0 (by positivity : (0 : ℝ) ≤ 4 * |CD| + 1)) hx1
  have hs2 := rr_sqrt_le (mul_nonneg hK0 (mul_nonneg hK0 (abs_nonneg M'))) hx2
  have hp45 : (p : ℝ) ^ 4 ≤ (p : ℝ) ^ 5 := pow_le_pow_right₀ hp1 (by norm_num)
  have hsy := Real.sqrt_nonneg (lam * dbar d p)
  have hk2 := Real.sqrt_nonneg (K * (K * |M'|))
  have hX : (p : ℝ) ^ 5 * Real.sqrt (K * lam * max (4 * |CD| * dbar d p / p) (vth d)) +
      (p : ℝ) ^ 4 * Real.sqrt (K * lam * (K * (M' * dbar d p))) + (p : ℝ) ^ 13 / (d : ℝ) ^ 2 ≤
      (Real.sqrt (K * (4 * |CD| + 1)) + Real.sqrt (K * (K * |M'|))) *
        ((p : ℝ) ^ 5 * Real.sqrt (lam * dbar d p)) + (p : ℝ) ^ 13 / (d : ℝ) ^ 2 := by
    have e1 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ (p : ℝ) ^ 5)
    have e2 := mul_le_mul_of_nonneg_left hs2 (by positivity : (0 : ℝ) ≤ (p : ℝ) ^ 4)
    have e3 := mul_le_mul_of_nonneg_right hp45 (mul_nonneg hk2 hsy)
    linarith
  have hX0 : 0 ≤ (p : ℝ) ^ 5 * Real.sqrt (K * lam * max (4 * |CD| * dbar d p / p) (vth d)) +
      (p : ℝ) ^ 4 * Real.sqrt (K * lam * (K * (M' * dbar d p))) + (p : ℝ) ^ 13 / (d : ℝ) ^ 2 := by
    positivity
  exact rr_absorb hB0 (by positivity) (by positivity) hϑ0 hX0 hX hmain

/-- **R-D9a′** [route DR1] (source l.1505–1517 with CR3′; AUDIT-B §3.3, DR1_CHECK §3,
CHECK_CONTACT). CR3′ with `λ_r = 4(S+1)/d`, `ρ_Δ = 4(|C_D|+1)δ̄/p` (DR1 at the root,
`D_v/d ≤ 4a² D_v`), `λ_c = (|C_M|+4)(|C₆|+|C₇|+2)p/d` (MARKENV with the envelope of (D6) and
`S ≤ C₇p`), `δ_c = 4(|C_M|+4)(2|C₂|+1)δ̄` (MARKENV minus with (C2)); the orderings hold for large
`p` (`p/d ≪ (p/d)^{1/3}`, `δ̄ ≤ 3p^{-5/2}`). Then `p⁵√(λ_r ρ_Δ) = 4√(|C_D|+1) Γ√(S+1)` and
`p⁴√(λ_c δ_c) = O(Γ)`. -/
theorem d9a_real_dr1 (CC CM C₂ CD C₆ C₇ : ℝ) : ∃ C : ℝ, 0 < C ∧ ∃ P₀ : ℕ, ∀ d p : ℕ,
    TRegime d p → P₀ ≤ p → ∀ S Sm A2 B2 fP fM Dv R Gt : ℝ, 0 ≤ S → 0 ≤ A2 →
      (∀ l : ℝ, aOf d p ^ 2 * S + A2 ≤ l → vth d ≤ l →
        S / d ≤ 4 * l ∧ fP / (d : ℝ) ^ 2 ≤ CM * l) →
      (∀ l : ℝ, aOf d p ^ 2 * Sm + B2 ≤ l → vth d ≤ l →
        Sm / d ≤ 4 * l ∧ fM / (d : ℝ) ^ 2 ≤ CM * l) →
      aOf d p ^ 2 * Sm ≤ C₂ * dbar d p → B2 ≤ C₂ * dbar d p →
      0 ≤ Dv → aOf d p ^ 2 * Dv ≤ CD * dbar d p / p →
      aOf d p ^ 2 * S + A2 + vth d ≤ C₆ * p / d → S ≤ C₇ * p →
      (∀ lr rd lc dc : ℝ, vth d ≤ lr → lr ≤ lc → lc ≤ dc → dc ≤ 1 → vth d ≤ rd →
        S / d ≤ lr → Sm / d ≤ dc → Dv / d ≤ rd →
        fP / (d : ℝ) ^ 2 ≤ lc → fM / (d : ℝ) ^ 2 ≤ dc →
        |R - Gt| ≤ CC * ((p : ℝ) ^ 5 * Real.sqrt (lr * rd) + (p : ℝ) ^ 4 * Real.sqrt (lc * dc) +
          (p : ℝ) ^ 13 / (d : ℝ) ^ 2) + CC * vth d) →
      |R - Gt| ≤ C * ErowP d p S := by
  obtain ⟨K₁, hK₁a, hK₁b⟩ : ∃ K₁ : ℝ, 4 * (|C₇| + 1) ≤ K₁ ∧ |CM| * |C₆| ≤ K₁ :=
    ⟨4 * (|C₇| + 1) + |CM| * |C₆|, le_add_of_nonneg_right (by positivity),
      le_add_of_nonneg_left (by positivity)⟩
  obtain ⟨K₂, hK₂a, hK₂b⟩ : ∃ K₂ : ℝ, 4 * (2 * |C₂| + 1) ≤ K₂ ∧ |CM| * (2 * |C₂| + 1) ≤ K₂ :=
    ⟨4 * (2 * |C₂| + 1) + |CM| * (2 * |C₂| + 1), le_add_of_nonneg_right (by positivity),
      le_add_of_nonneg_left (by positivity)⟩
  have hK₁0 : 0 ≤ K₁ := by linarith [abs_nonneg C₇]
  have hK₂1 : 1 ≤ K₂ := by linarith [abs_nonneg C₂]
  have hK₂0 : 0 ≤ K₂ := by linarith
  have hB0 : 0 ≤ Real.sqrt (16 * (|CD| + 1)) + Real.sqrt (K₁ * K₂) :=
    add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  refine ⟨|CC| * (Real.sqrt (16 * (|CD| + 1)) + Real.sqrt (K₁ * K₂) + 1) + 1, by positivity,
    max ⌈K₁⌉₊ ⌈K₂⌉₊, fun d p hR hp => ?_⟩
  intro S Sm A2 B2 fP fM Dv R Gt hS hA2 hMP hMM hSm hB2 hDv0 hDv h6 h7 hcb
  have hp0 := hR.pfA_p_pos
  have hp1 := hR.pfA_one_le_p
  have hd0 := hR.pfA_d_pos
  have hϑ0 := pfA_vth_nonneg d
  have hϑd := hR.pfA_vth_mul_d
  have hdb0 := hR.pfA_dbar_nonneg
  have hϑδ := vth_le_dbar hR
  have hpdb := hR.rr_p_dbar
  have hp4db := hR.rr_p4_le_dbar
  have ha0 : 0 ≤ aOf d p ^ 2 := sq_nonneg _
  have hK₁p : K₁ ≤ p := (Nat.le_ceil _).trans (by exact_mod_cast le_of_max_le_left hp)
  have hK₂p : K₂ ≤ p := (Nat.le_ceil _).trans (by exact_mod_cast le_of_max_le_right hp)
  -- MARKENV plus at `l = C₆ p/d`
  have hl1 : aOf d p ^ 2 * S + A2 ≤ C₆ * p / d := by linarith
  have hl2 : vth d ≤ C₆ * p / d := by
    have := mul_nonneg ha0 hS
    linarith
  have hl0 : 0 ≤ C₆ * p / d := hϑ0.trans hl2
  obtain ⟨-, hfP⟩ := hMP (C₆ * p / d) hl1 hl2
  -- MARKENV minus at `l = (2|C₂| + 1) δ̄`
  have hm1 : aOf d p ^ 2 * Sm + B2 ≤ (2 * |C₂| + 1) * dbar d p := by
    have := mul_le_mul_of_nonneg_right (le_abs_self C₂) hdb0
    linarith
  have hm2 : vth d ≤ (2 * |C₂| + 1) * dbar d p := by
    have := mul_nonneg (abs_nonneg C₂) hdb0
    linarith
  have hm0 : 0 ≤ (2 * |C₂| + 1) * dbar d p := hϑ0.trans hm2
  obtain ⟨hSmd, hfM⟩ := hMM ((2 * |C₂| + 1) * dbar d p) hm1 hm2
  -- the hypotheses of the callback
  have hc1 : vth d ≤ 4 * (S + 1) / d := by
    rw [le_div_iff₀ hd0]
    linarith
  have hc2 : 4 * (S + 1) / d ≤ K₁ * p / d := by
    refine div_le_div_of_nonneg_right ?_ hd0.le
    have hS' : S ≤ |C₇| * p := h7.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hp0.le)
    have := mul_le_mul_of_nonneg_right hK₁a hp0.le
    linarith
  have hc3 : K₁ * p / d ≤ K₂ * dbar d p := by
    have h1 : K₁ * p ≤ K₂ * (p : ℝ) ^ 4 :=
      calc K₁ * p ≤ (p : ℝ) * p := mul_le_mul_of_nonneg_right hK₁p hp0.le
        _ = (p : ℝ) ^ 2 := by ring
        _ ≤ (p : ℝ) ^ 4 := pow_le_pow_right₀ hp1 (by norm_num)
        _ = 1 * (p : ℝ) ^ 4 := by ring
        _ ≤ K₂ * (p : ℝ) ^ 4 := mul_le_mul_of_nonneg_right hK₂1 (by positivity)
    calc K₁ * p / d ≤ K₂ * (p : ℝ) ^ 4 / d := div_le_div_of_nonneg_right h1 hd0.le
      _ = K₂ * ((p : ℝ) ^ 4 / d) := by ring
      _ ≤ K₂ * dbar d p := mul_le_mul_of_nonneg_left hp4db hK₂0
  have hc4 : K₂ * dbar d p ≤ 1 := by
    have := mul_le_mul_of_nonneg_right hK₂p hdb0
    linarith
  have hc5 : vth d ≤ 4 * (|CD| + 1) * dbar d p / p := by
    rw [le_div_iff₀ hp0]
    have e1 : vth d * p ≤ (p : ℝ) ^ 4 / d := by
      rw [le_div_iff₀ hd0]
      have := mul_le_mul_of_nonneg_right hϑd hp0.le
      have e : (p : ℝ) ≤ (p : ℝ) ^ 4 := le_self_pow₀ hp1 (by norm_num)
      linarith
    have e2 := mul_nonneg (abs_nonneg CD) hdb0
    linarith
  have hc6 : S / d ≤ 4 * (S + 1) / d := div_le_div_of_nonneg_right (by linarith) hd0.le
  have hc7 : Sm / d ≤ K₂ * dbar d p := by
    have := mul_le_mul_of_nonneg_right hK₂a hdb0
    linarith
  have hc8 : Dv / d ≤ 4 * (|CD| + 1) * dbar d p / p := by
    have h1 : CD * dbar d p / p ≤ (|CD| + 1) * dbar d p / p :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith [le_abs_self CD]) hdb0) hp0.le
    calc Dv / d ≤ 4 * (aOf d p ^ 2 * Dv) := hR.rr_div_d_le hDv0
      _ ≤ 4 * ((|CD| + 1) * dbar d p / p) := by linarith
      _ = 4 * (|CD| + 1) * dbar d p / p := by ring
  have hc9 : fP / (d : ℝ) ^ 2 ≤ K₁ * p / d := by
    have e1 : CM * (C₆ * p / d) ≤ |CM| * (C₆ * p / d) :=
      mul_le_mul_of_nonneg_right (le_abs_self _) hl0
    have e2 : C₆ * p / d ≤ |C₆| * p / d :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hp0.le) hd0.le
    have e3 := mul_le_mul_of_nonneg_left e2 (abs_nonneg CM)
    have e4 : |CM| * (|C₆| * p / d) = |CM| * |C₆| * p / d := by ring
    have e5 : |CM| * |C₆| * p / d ≤ K₁ * p / d :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hK₁b hp0.le) hd0.le
    linarith
  have hc10 : fM / (d : ℝ) ^ 2 ≤ K₂ * dbar d p := by
    have e1 : CM * ((2 * |C₂| + 1) * dbar d p) ≤ |CM| * ((2 * |C₂| + 1) * dbar d p) :=
      mul_le_mul_of_nonneg_right (le_abs_self _) hm0
    have e2 := mul_le_mul_of_nonneg_right hK₂b hdb0
    linarith
  have hmain := hcb (4 * (S + 1) / d) (4 * (|CD| + 1) * dbar d p / p) (K₁ * p / d)
    (K₂ * dbar d p) hc1 hc2 hc3 hc4 hc5 hc6 hc7 hc8 hc9 hc10
  -- the square roots
  have hG : GamP d p = (p : ℝ) ^ 4 * Real.sqrt ((p : ℝ) * dbar d p / d) := rfl
  have hrow := rr_row_eq (S := S) (c := |CD| + 1) hp0 hd0 (by positivity) hdb0
  have hcore := rr_core_eq (p := (p : ℝ)) (d := (d : ℝ)) (δ := dbar d p) (mul_nonneg hK₁0 hK₂0)
  rw [← hG] at hrow hcore
  have hG0 := pfA_gam_nonneg d p
  have hsS : 1 ≤ Real.sqrt (S + 1) := by
    have := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ S + 1 by linarith)
    rwa [Real.sqrt_one] at this
  have hX : (p : ℝ) ^ 5 * Real.sqrt (4 * (S + 1) / d * (4 * (|CD| + 1) * dbar d p / p)) +
      (p : ℝ) ^ 4 * Real.sqrt (K₁ * p / d * (K₂ * dbar d p)) + (p : ℝ) ^ 13 / (d : ℝ) ^ 2 ≤
      (Real.sqrt (16 * (|CD| + 1)) + Real.sqrt (K₁ * K₂)) *
        (GamP d p * Real.sqrt (S + 1)) + (p : ℝ) ^ 13 / (d : ℝ) ^ 2 := by
    rw [hrow, hcore]
    have e1 : GamP d p ≤ GamP d p * Real.sqrt (S + 1) := le_mul_of_one_le_right hG0 hsS
    have e2 := mul_le_mul_of_nonneg_left e1 (Real.sqrt_nonneg (K₁ * K₂))
    linarith
  have hX0 : 0 ≤ (p : ℝ) ^ 5 * Real.sqrt (4 * (S + 1) / d * (4 * (|CD| + 1) * dbar d p / p)) +
      (p : ℝ) ^ 4 * Real.sqrt (K₁ * p / d * (K₂ * dbar d p)) + (p : ℝ) ^ 13 / (d : ℝ) ^ 2 := by
    positivity
  unfold ErowP
  exact rr_absorb hB0 (mul_nonneg hG0 (Real.sqrt_nonneg _)) (by positivity) hϑ0 hX0 hX hmain

end BiluLinial.Tight
