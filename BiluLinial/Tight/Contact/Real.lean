/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.Contact.RealPfA
public import BiluLinial.Tight.Contact.RealPfB

/-!
# Real-number layer of the contact estimate

Blueprint `docs/tight/BP_CONTACT.md`, nodes `R-*`. Pure real-number statements: the regime
helpers (`eventually_reg`, `eventually_ge`, `Eventually.of_real`, proved), the deterministic
parameter facts of (D1)–(D2) (`param_facts`), and one real lemma per non-leaf node of the chain
(the algebra of D4, D6, D7, D9b, D10, E-c, FS7, JR, RC3, D12, D15, the final assembly, the ledger
(D16) and the choice of `κ₀, c₀`).

Every real lemma has the shape "absolute constant first, then (if needed) `κ₀` or `c₀, κ₀`, then a
threshold `P₀` on `p`": `∃ C > 0, ∀ κ₀ ∈ (0,1], ∃ P₀, ∀ d p h, Reg κ₀ d p h → P₀ ≤ p → …`. This is
the quantifier order of AUDIT-D §4.1.
-/

@[expose] public section

namespace BiluLinial.Tight

open Real

/-! ### Regime helpers (proved) -/

/-- At `p = ⌊c₀ d^{2/17}⌋` and `h = κ₀ p^{-4}`, the regime holds for large `d`. -/
theorem eventually_reg :
    Eventually fun c₀ κ₀ d p h =>
      Reg κ₀ d p h ∧ 0 < c₀ ∧ c₀ ≤ 1 ∧ (p : ℝ) ≤ c₀ * (d : ℝ) ^ ((2 : ℝ) / 17) := by
  intro c₀ κ₀ hc0 hc1 hk0 hk1
  obtain ⟨D, hD⟩ := exists_tRegime_pAt hc0 hc1
  refine ⟨D, fun d hd => ⟨⟨(hD d hd).1, hk0, hk1, rfl⟩, hc0, hc1, ?_⟩⟩
  exact Nat.floor_le (mul_nonneg hc0.le (Real.rpow_nonneg (Nat.cast_nonneg d) _))

/-- `p` exceeds any threshold depending on `c₀, κ₀`, for large `d`. -/
theorem eventually_ge (f : ℝ → ℝ → ℕ) : Eventually fun c₀ κ₀ _d p _h => f c₀ κ₀ ≤ p := by
  intro c₀ κ₀ hc0 _ _ _
  obtain ⟨D, hD⟩ := exists_base_ge hc0 (2 * (f c₀ κ₀ : ℝ) + 2)
  refine ⟨D, fun d hd => ?_⟩
  have hb := hD d hd
  have hf : (0 : ℝ) ≤ f c₀ κ₀ := Nat.cast_nonneg _
  have hp := half_base_le_pAt (c₀ := c₀) (d := d) (by linarith)
  have : (f c₀ κ₀ : ℝ) ≤ pAt c₀ d := by linarith
  exact_mod_cast this

/-- A real lemma with a threshold `P₀(c₀, κ₀)` on `p` gives an `Eventually` statement. -/
theorem Eventually.of_real {P : ℝ → ℝ → ℕ → ℕ → ℝ → Prop}
    (hP : ∀ c₀ κ₀ : ℝ, 0 < c₀ → c₀ ≤ 1 → 0 < κ₀ → κ₀ ≤ 1 → ∃ P₀ : ℕ, ∀ (d p : ℕ) (h : ℝ),
      Reg κ₀ d p h → (p : ℝ) ≤ c₀ * (d : ℝ) ^ ((2 : ℝ) / 17) → P₀ ≤ p → P c₀ κ₀ d p h) :
    Eventually P := by
  intro c₀ κ₀ hc0 hc1 hk0 hk1
  obtain ⟨P₀, hP₀⟩ := hP c₀ κ₀ hc0 hc1 hk0 hk1
  obtain ⟨D₁, hD₁⟩ := eventually_reg c₀ κ₀ hc0 hc1 hk0 hk1
  obtain ⟨D₂, hD₂⟩ := eventually_ge (fun _ _ => P₀) c₀ κ₀ hc0 hc1 hk0 hk1
  refine ⟨max D₁ D₂, fun d hd => ?_⟩
  obtain ⟨hreg, -, -, hpc⟩ := hD₁ d (le_of_max_le_left hd)
  exact hP₀ d _ _ hreg hpc (hD₂ d (le_of_max_le_right hd))

/-- A real lemma depending only on the regime and a threshold on `p`. -/
theorem Eventually.of_reg {P : ℕ → ℕ → ℝ → Prop}
    (hP : ∀ κ₀ : ℝ, 0 < κ₀ → κ₀ ≤ 1 → ∃ P₀ : ℕ, ∀ (d p : ℕ) (h : ℝ),
      Reg κ₀ d p h → P₀ ≤ p → P d p h) :
    Eventually fun _c₀ _κ₀ d p h => P d p h :=
  Eventually.of_real fun _ κ₀ _ _ hk0 hk1 => by
    obtain ⟨P₀, hP₀⟩ := hP κ₀ hk0 hk1
    exact ⟨P₀, fun d p h hreg _ hp => hP₀ d p h hreg hp⟩

/-- `TRegime d p` and a fixed threshold on `p`, for large `d`. -/
theorem eventually_treg_ge (P₀ : ℕ) : Eventually fun _c₀ _κ₀ d p _h => TRegime d p ∧ P₀ ≤ p :=
  Eventually.of_reg fun _ _ _ => ⟨P₀, fun _ _ _ hR hp => ⟨hR.treg, hp⟩⟩

/-- The regime and a `κ₀`-dependent threshold on `p`, for large `d`. -/
theorem eventually_reg_ge (P₀ : ℝ → ℕ) :
    Eventually fun _c₀ κ₀ d p h => Reg κ₀ d p h ∧ P₀ κ₀ ≤ p :=
  Eventually.of_real fun _ κ₀ _ _ _ _ => ⟨P₀ κ₀, fun _ _ _ hR _ hp => ⟨hR, hp⟩⟩

/-- A real lemma of the shape "threshold on `p` in the regime" gives an `Eventually` statement. -/
theorem Eventually.of_treg {Q : ℕ → ℕ → Prop}
    (hQ : ∃ P₀ : ℕ, ∀ d p : ℕ, TRegime d p → P₀ ≤ p → Q d p) :
    Eventually fun _c₀ _κ₀ d p _h => Q d p := by
  obtain ⟨P₀, hP₀⟩ := hQ
  exact (eventually_treg_ge P₀).mono fun _ _ d p _ H => hP₀ d p H.1 H.2

/-- The same, with a positive shift `h`. -/
theorem Eventually.of_treg_h {Q : ℕ → ℕ → ℝ → Prop}
    (hQ : ∃ P₀ : ℕ, ∀ (d p : ℕ) (h : ℝ), TRegime d p → P₀ ≤ p → 0 < h → Q d p h) :
    Eventually fun _c₀ _κ₀ d p h => Q d p h := by
  obtain ⟨P₀, hP₀⟩ := hQ
  refine Eventually.of_reg fun _ _ _ => ⟨P₀, fun d p h hR hp => ?_⟩
  have hh : 0 < h := by
    rw [hR.hh]
    have : (0 : ℝ) < p := by exact_mod_cast lt_of_lt_of_le (by norm_num) hR.treg.hp
    exact div_pos hR.k0 (by positivity)
  exact hP₀ d p h hR.treg hp hh

/-- `ϑ ≤ δ̄` (since `δ̄ ≥ p⁴/d ≥ d^{-10}`). -/
theorem vth_le_dbar {d p : ℕ} (hR : TRegime d p) : vth d ≤ dbar d p := by
  have hd : (1 : ℝ) ≤ d := le_trans (by norm_num) hR.ten_pow_six_le_d
  have hp : (1 : ℝ) ≤ p := by exact_mod_cast le_trans (by norm_num) hR.hp
  have he : 0 ≤ epsP d p := by unfold epsP; linarith [hR.one_lt_rOf]
  have hr : 0 ≤ ((p : ℝ) / d) ^ ((1 : ℝ) / 3) := Real.rpow_nonneg (by positivity) _
  have h1 : vth d ≤ 1 / (d : ℝ) := by
    unfold vth
    exact one_div_le_one_div_of_le (by positivity) (le_self_pow₀ hd (by norm_num))
  have h2 : 1 / (d : ℝ) ≤ (p : ℝ) ^ 4 / d :=
    div_le_div_of_nonneg_right (one_le_pow₀ hp) (by positivity)
  unfold dbar
  linarith

/-- `h = κ₀ p^{-4} > 0` in the regime. -/
theorem Reg.h_pos {κ₀ : ℝ} {d p : ℕ} {h : ℝ} (hR : Reg κ₀ d p h) : 0 < h := by
  rw [hR.hh]
  have : (0 : ℝ) < p := by exact_mod_cast lt_of_lt_of_le (by norm_num) hR.treg.hp
  exact div_pos hR.k0 (by positivity)

/-- `ε ≤ ξ`. -/
theorem epsP_le_xiP {d p : ℕ} (hR : TRegime d p) (h : ℝ) : epsP d p ≤ xiP d p h := by
  have h1 := hR.η0Of_pos
  have h2 : 0 ≤ epsS d p := by unfold epsS; positivity
  unfold xiP
  have := Real.sqrt_nonneg h
  have := Real.sqrt_nonneg (epsP d p / p + epsP d p ^ 2 + (p : ℝ) / d)
  have := Real.sqrt_nonneg (epsP d p / p + epsP d p ^ 2)
  have : (0 : ℝ) ≤ 1 / (d : ℝ) := by positivity
  linarith

/-! ### Deterministic parameter facts (D1)–(D2) (leaf) -/

/-- **R-param** (source (D1)–(D2), l.1336–1349, l.63–68; AUDIT-D §1.1, §3.1 D2; AUDIT-C R2–R5).
Deterministic facts at large `p` in the regime: `1/(4d) ≤ a² ≤ 1/d`, `d a² ≤ 1/4 + 1/d`,
`1/(2√(pd)) ≤ ε ≤ 1/√(pd)`, `η₀ ≤ 2/√(pd)`, `1 - r L̄ ≥ 0`, the drift reserve
`d(r-1)(1 - r L̄) ≥ 1/p - 2η₀`, `r L̄ s² ≤ 4`, `L̄ s² ≥ 4 - 8η₀`, `1/2 ≤ L̄ ≤ 2`, `s² ≤ 5`. -/
theorem param_facts : ∃ P₀ : ℕ, ∀ d p : ℕ, TRegime d p → P₀ ≤ p →
    aOf d p ^ 2 ≤ 1 / (d : ℝ) ∧ 1 / (4 * (d : ℝ)) ≤ aOf d p ^ 2 ∧
    (d : ℝ) * aOf d p ^ 2 ≤ 1 / 4 + 1 / (d : ℝ) ∧
    1 / (2 * Real.sqrt ((p : ℝ) * d)) ≤ epsP d p ∧ epsP d p ≤ 1 / Real.sqrt ((p : ℝ) * d) ∧
    η0Of d p ≤ 2 / Real.sqrt ((p : ℝ) * d) ∧
    0 ≤ 1 - rOf d p * LbarP d p ∧
    1 / (p : ℝ) - 2 * η0Of d p ≤ (d : ℝ) * epsP d p * (1 - rOf d p * LbarP d p) ∧
    rOf d p * LbarP d p * sOf d p ^ 2 ≤ 4 ∧ 4 - 8 * η0Of d p ≤ LbarP d p * sOf d p ^ 2 ∧
    1 / 2 ≤ LbarP d p ∧ LbarP d p ≤ 2 ∧ sOf d p ^ 2 ≤ 5 := by
  exact param_facts_pf

/-! ### Real lemmas of the chain (leaves) -/

/-- The uniform weak error `E_c = e√z₊ + e√z₋ + e² + B₀ + e(h^{3/4} + √β_h + √θ)` of (FS7), with
`hq = h^{3/4}` and `bh = β_h`. -/
noncomputable def EcF (e B₀ hq bh θ z zm : ℝ) : ℝ :=
  e * Real.sqrt z + e * Real.sqrt zm + e ^ 2 + B₀ + e * (hq + Real.sqrt bh + Real.sqrt θ)

/-- **R-D4** (source (D4), l.1423–1436; AUDIT-D §3.1 D4, AUDIT-C §6 (D4)). From (D3), the bound
`|Q_*| ≤ C a²(p + p³δ̄)` and the sign facts, `𝓡 ≤ C(p + p⁵/d)`; and if `𝓡 ≥ -b` then
`S + a⁻² Σℓδ ≤ C(1 + p + p⁵/d + b)` and `L̄ - L ≤ C a² (1 + p + p⁵/d + b)/(r-1)`. -/
theorem d4_real (C₃ CQ : ℝ) : ∃ C : ℝ, 0 < C ∧ ∃ P₀ : ℕ, ∀ d p : ℕ, TRegime d p → P₀ ≤ p →
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
  exact d4_real_pf C₃ CQ

/-- **R-D6** (source (D6), l.1438–1487; AUDIT-C §6 (D6), AUDIT-D §3.1 D6). The `λ`-bootstrap:
with `λ = a² S + E tr A² + ϑ`, CR1 (`|𝓡 - Gterm| ≤ C₁(p⁵√(λδ̄) + p¹³/d² + ϑ)`), `Gterm ≥ 0`
(C1), the whitening transfer, (C3a) and (D4) give `λ ≤ C p/d` (Young absorbs `p⁵√(λδ̄)/d`). -/
theorem d6_real (C₁ Cw Ca C₄ : ℝ) : ∃ C : ℝ, 0 < C ∧ ∃ P₀ : ℕ, ∀ d p : ℕ, TRegime d p →
    P₀ ≤ p → ∀ S A2 W Gt R : ℝ, 0 ≤ S → 0 ≤ A2 → 0 ≤ W →
      |R - Gt| ≤ C₁ * ((p : ℝ) ^ 5 * Real.sqrt ((aOf d p ^ 2 * S + A2 + vth d) * dbar d p) +
        (p : ℝ) ^ 13 / (d : ℝ) ^ 2 + vth d) →
      0 ≤ Gt →
      W ≤ 2 * aOf d p ^ 2 * Gt + Cw * ((p : ℝ) ^ 4 / d) * (W + vth d) →
      A2 ≤ 2 * W + Ca * vth d →
      R ≤ C₄ * (p + (p : ℝ) ^ 5 / d) →
      (∀ b : ℝ, 0 ≤ b → -b ≤ R → S ≤ C₄ * (1 + p + (p : ℝ) ^ 5 / d + b)) →
      aOf d p ^ 2 * S + A2 + vth d ≤ C * p / d := by
  exact d6_real_pf C₁ Cw Ca C₄

/-- **R-D7** (source (D7), l.1487–1491; AUDIT-C §6 (D7)/(D8)). With `λ ≤ C₆ p/d`, the CR1 error is
`O(1)`, so `𝓡 ≥ -C` and (D4) gives `S ≤ Cp`, `Σℓδ ≤ C p a²`, `L̄ - L ≤ C ε_s`. -/
theorem d7_real (C₁ C₄ C₆ : ℝ) : ∃ C : ℝ, 0 < C ∧ ∃ P₀ : ℕ, ∀ d p : ℕ, TRegime d p →
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
  exact d7_real_pf C₁ C₄ C₆

/-- **R-D9b** (source (D9b), l.1520–1531; AUDIT-C §6 (D9b)). From (B1), (D9a), `𝓡 ≤ C(p + p⁵/d)`
and `S ≤ Cp`: `Q ≤ C p` (using `C_B η_BL ≤ 1/2` at `h = κ₀ p^{-4}`). -/
theorem d9b_real (CB C₉ C₄ C₇ : ℝ) : ∃ C : ℝ, 0 < C ∧ ∀ κ₀ : ℝ, 0 < κ₀ → κ₀ ≤ 1 →
    ∃ P₀ : ℕ, ∀ (d p : ℕ) (h : ℝ), Reg κ₀ d p h → P₀ ≤ p →
    ∀ S R Gt Qb : ℝ, 0 ≤ S →
      (1 - CB * etaBL d p h) * Qb - CB * epsBL d p h ≤ Gt →
      |R - Gt| ≤ C₉ * ErowP d p S →
      R ≤ C₄ * (p + (p : ℝ) ^ 5 / d) →
      S ≤ C₇ * p →
      Qb ≤ C * p := by
  exact d9b_real_pf CB C₉ C₄ C₇

/-- **R-D10** (source (D10), l.1546–1558; AUDIT-C §6 (D10)). From (B1), (D9a), (D9b) and the
full/core correction `Q_full ≤ Q + C p/(d h^{3/2})`: `𝓡 ≥ Q_full - C·Err10`. -/
theorem d10_real (CB C₉ C₉b Cc : ℝ) (hCB : 0 ≤ CB) :
    ∃ C : ℝ, 0 < C ∧ ∀ (d p : ℕ) (h : ℝ), TRegime d p →
    0 < h → ∀ S R Gt Qb Qf : ℝ,
      (1 - CB * etaBL d p h) * Qb - CB * epsBL d p h ≤ Gt →
      |R - Gt| ≤ C₉ * ErowP d p S →
      Qb ≤ C₉b * p →
      Qf ≤ Qb + Cc * p / (d * h * Real.sqrt h) →
      Qf - C * Err10 d p h S ≤ R := by
  exact d10_real_pf CB C₉ C₉b Cc hCB

/-- **R-Ec** (source (E-c), l.1590–1592; AUDIT-D §3.2). `L_d (p-1) q₊ ≤ Q_full ≤ Q + small ≤ Cp`
and `q₋ ≥ 0` give `q₊ ≤ C`. -/
theorem qP_le_real (C₉b Cc : ℝ) : ∃ C : ℝ, 0 < C ∧ ∀ κ₀ : ℝ, 0 < κ₀ → κ₀ ≤ 1 →
    ∃ P₀ : ℕ, ∀ (d p : ℕ) (h : ℝ), Reg κ₀ d p h → P₀ ≤ p →
    ∀ Qb qp qm : ℝ, 0 ≤ qm →
      LdP d p * (((p : ℝ) - 1) * qp + p * qm) ≤ Qb + Cc * p / (d * h * Real.sqrt h) →
      Qb ≤ C₉b * p →
      qp ≤ C := by
  exact qP_le_real_pf C₉b Cc

/-- **R-FS7** (source (FS6)–(FS7), l.1765–1798; AUDIT-D §3.4). The raw weak residual bounds (W1 with
the FS5 scores) give the uniform error `E_c = e√z₊ + e√z₋ + e² + B₀ + e(h^{3/4} + √β_h + √θ)`
for all four residuals (AM–GM on `e√|r₁|`). Here `hq = h^{3/4}`, `bh = β_h = (dh)⁻¹`. -/
theorem fs7_real (Cw Cq : ℝ) : ∃ K : ℝ, 0 < K ∧
    ∀ e B₀ hq bh θ q t ζ α z qm ζm tm zm β : ℝ, 0 ≤ e → 0 ≤ B₀ → 0 ≤ hq → 0 ≤ bh → 0 ≤ θ →
      0 ≤ z → 0 ≤ zm → 0 ≤ q - t → q - t ≤ Cq → α ≤ ζ →
      |q - ζ - t| ≤ Cw * (e * Real.sqrt (ζ - α + bh * (q - t) + θ) + e * hq + B₀) →
      |ζ - z - α| ≤ Cw * (e * Real.sqrt (z + θ) + B₀) →
      |qm + ζm - tm| ≤ Cw * (e * Real.sqrt (ζ - α + bh * (q - t) + θ) + e * hq + B₀) →
      |ζm + zm - β| ≤ Cw * (e * Real.sqrt (zm + θ) + B₀) →
      |q - ζ - t| ≤ K * EcF e B₀ hq bh θ z zm ∧ |ζ - z - α| ≤ K * EcF e B₀ hq bh θ z zm ∧
        |qm + ζm - tm| ≤ K * EcF e B₀ hq bh θ z zm ∧
        |ζm + zm - β| ≤ K * EcF e B₀ hq bh θ z zm := by
  exact fs7_real_pf Cw Cq

/-- **R-JR** (source α-cap, (JR3), (JR2), l.1844–1908; AUDIT-D §3.6). From the Gram facts of both
Hadamard kernels, the four weak identities with error `E`, (RC1) and (RC2):
`(p-1)(q₊-t₊) + p(q₋-t₋) ≥ ((p-1)/2) z₊ + (p/2) z₋ - 1/(4(p-1)) - K p (E + ξ)`. -/
theorem jr_real (C₁ C₂ : ℝ) : ∃ K : ℝ, 0 < K ∧ ∀ p : ℕ, 2 ≤ p →
    ∀ E ξ ε q t ζ α z qm ζm tm zm β : ℝ, 0 ≤ E → 0 ≤ ε → ε ≤ ξ →
      0 ≤ q → 0 ≤ z → ζ ^ 2 ≤ q * z → 0 ≤ qm → 0 ≤ zm → ζm ^ 2 ≤ qm * zm →
      t ≤ q → 0 ≤ α → α ≤ ζ → 0 ≤ β → 0 ≤ t → t ≤ 1 + C₁ * ε → 0 ≤ tm →
      tm ≤ 1 + C₁ * ε → β ≤ α + C₂ * ξ →
      |q - ζ - t| ≤ E → |ζ - z - α| ≤ E → |qm + ζm - tm| ≤ E → |ζm + zm - β| ≤ E →
      ((p : ℝ) - 1) / 2 * z + p / 2 * zm - 1 / (4 * ((p : ℝ) - 1)) - K * p * (E + ξ) ≤
        ((p : ℝ) - 1) * (q - t) + p * (qm - tm) := by
  exact jr_real_pf C₁ C₂

/-- **R-RC3** (source (RC3), l.1910–1918; AUDIT-D §3.6). Young absorbs `p e √z_±` into the reserves
`((p-1)/2) z₊ + (p/2) z₋`. -/
theorem rc3_young_real (K₁ : ℝ) : ∃ K : ℝ, 0 < K ∧ ∀ p : ℕ, 2 ≤ p →
    ∀ e z zm E₀ ξ P : ℝ, 0 ≤ e → 0 ≤ z → 0 ≤ zm → 0 ≤ E₀ → 0 ≤ ξ →
      ((p : ℝ) - 1) / 2 * z + p / 2 * zm - 1 / (4 * ((p : ℝ) - 1)) -
          K₁ * p * (e * Real.sqrt z + e * Real.sqrt zm + E₀ + ξ) ≤ P →
      -(1 / (4 * ((p : ℝ) - 1))) - K * p * (e ^ 2 + E₀ + ξ) ≤ P := by
  exact rc3_young_real_pf K₁

/-- **R-D12** (source (D12), l.1955–1963; AUDIT-D §3.7). (D10), (RC3) and (RC4) give
`𝒟 = 𝓡 - L_d[(p-1)t_{+,0} + p t_{-,0}] ≥ -L_d c_p - C·Err12`. -/
theorem d12_real (C₁₀ C₃ C₄ : ℝ) : ∃ C : ℝ, 0 < C ∧ ∃ P₀ : ℕ, ∀ (d p : ℕ) (h : ℝ),
    TRegime d p → P₀ ≤ p → 0 < h →
    ∀ S R qp qm tp tm tp0 tm0 : ℝ,
      LdP d p * (((p : ℝ) - 1) * qp + p * qm) - C₁₀ * Err10 d p h S ≤ R →
      -cpP p - C₃ * p * ErrRC3 d p h ≤ ((p : ℝ) - 1) * (qp - tp) + p * (qm - tm) →
      tp0 - tp ≤ C₄ * Real.sqrt h → tm0 - tm ≤ C₄ * Real.sqrt h →
      -(LdP d p * cpP p) - C * Err12 d p h S ≤
        R - LdP d p * (((p : ℝ) - 1) * tp0 + p * tm0) := by
  exact d12_real_pf C₁₀ C₃ C₄

/-- **R-D15** (source (D15), l.1977–1982; AUDIT-D §3.8). From `a²|N| S ≥ (r D₊ - 1)²`,
`D₊ = 1 + L - C₊`, `L̄ - L ≤ C₇ ε_s`, `C₊ ≤ a² L̄ s²` and `|N| ≤ d`: `S ≥ 4 - C(ε_s + η₀ + 1/d)`. -/
theorem d15_real (C₇ : ℝ) : ∃ C : ℝ, 0 < C ∧ ∃ P₀ : ℕ, ∀ d p : ℕ, TRegime d p → P₀ ≤ p →
    ∀ S n L Cp Dp : ℝ, 0 ≤ S → 0 ≤ n → n ≤ d → 0 ≤ Cp → Dp = 1 + L - Cp →
      Cp ≤ aOf d p ^ 2 * LbarP d p * sOf d p ^ 2 → LbarP d p - L ≤ C₇ * epsS d p →
      (rOf d p * Dp - 1) ^ 2 ≤ aOf d p ^ 2 * n * S →
      4 - C * (epsS d p + η0Of d p + 1 / (d : ℝ)) ≤ S := by
  exact d15_real_pf C₇

/-- **R-final** (source (D14), absorption and conclusion, l.1965–2053; AUDIT-D §3.8). (D3), (D12),
(D13), `J ≥ C₊`, `r C₊ ≤ 4a²`, (D15) and the drift reserve (D2) give
`1/p - 2η₀ ≤ 2(1 + 9/d) c_p + K·TotErr`. The row term `Γ√(S+1)` of `Err12` is absorbed by
`(1/4)(S - 4)` (Young, using (D15)). -/
theorem final_assembly_real (C₃ C₁₂ C₁₃ C₁₅ : ℝ) : ∃ K : ℝ, 0 < K ∧ ∃ P₀ : ℕ,
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
  exact final_assembly_real_pf C₃ C₁₂ C₁₃ C₁₅

/-- **R-ledger** (source (D16), l.2001–2036; AUDIT-D §4.2–4.3). The critical terms satisfy
`p√h = √κ₀/p`, `Γ ≤ √3 c₀^{17/3}/p`, `p e² ≤ 3 κ₀^{-2} c₀^{34/3}/p`, and every other term of
`TotErr` is `O(κ₀^{-3/2} p^{-3/2})`; hence once the critical coefficient is at most `1/8`, the final
inequality fails for large `p` (margin about `3/(8p)`). -/
theorem ledger_real (K : ℝ) : ∃ Ccrit : ℝ, 0 < Ccrit ∧ ∀ c₀ κ₀ : ℝ, 0 < c₀ → c₀ ≤ 1 →
    0 < κ₀ → κ₀ ≤ 1 →
    Ccrit * (Real.sqrt κ₀ + c₀ ^ ((17 : ℝ) / 3) + κ₀⁻¹ ^ 2 * c₀ ^ ((34 : ℝ) / 3)) ≤ 1 / 8 →
    ∃ P₀ : ℕ, ∀ (d p : ℕ) (h : ℝ), Reg κ₀ d p h → (p : ℝ) ≤ c₀ * (d : ℝ) ^ ((2 : ℝ) / 17) →
      P₀ ≤ p →
      2 * (1 + 9 / (d : ℝ)) * cpP p + K * TotErr d p h + 2 * η0Of d p < 1 / (p : ℝ) := by
  exact ledger_real_pf K

/-- **R-choice** (source l.2034–2036; AUDIT-D §0 "Explicit constants"). `κ₀ = min(1, (24C)⁻²)` and
`c₀ = min(1, (24C)^{-3/17}, (κ₀²/(24C))^{3/34})` make the critical coefficient at most `1/8`. -/
theorem ledger_choice (Ccrit : ℝ) (hC : 0 < Ccrit) : ∃ c₀ κ₀ : ℝ, 0 < c₀ ∧ c₀ ≤ 1 ∧ 0 < κ₀ ∧
    κ₀ ≤ 1 ∧
    Ccrit * (Real.sqrt κ₀ + c₀ ^ ((17 : ℝ) / 3) + κ₀⁻¹ ^ 2 * c₀ ^ ((34 : ℝ) / 3)) ≤ 1 / 8 := by
  exact ledger_choice_pf Ccrit hC

end BiluLinial.Tight
