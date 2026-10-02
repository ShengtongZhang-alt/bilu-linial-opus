/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecB.WTRemCore
public import BiluLinial.Tight.SecB.WTRetLaw

/-!
# Weighted fresh-star quadratic domination (WT1)–(WT5)

Nodes TB.sub, TB.WT3, TB.WT5, TB.abs, TB.WT2 of `docs/tight/BP_SECB.md` (source paragraph
"Weighted fresh-star quadratic domination", lines 913–1075; AUDIT-B §2.5).

Fix a contact, a vertex `i ∈ N = N_S(v)` (deleted vertex), `J = N_S(i)`, `ξ` the star vector at
`i`, a branch `e` and a cavity map `T ∈ {T_dir, T_cav}` of (WT1) (`Contact.tMap`, built from the
core shifted inverses `C_e = (P^e_{S-i} + hI)⁻¹`, hence independent of `ξ`), `L = TᵀT ⪰ 0`, and
the weight `H = H₀ (X_e)_ii² (X₊)_ii²` with `H₀` a product of at most `m₀` physical inverse
diagonals (`Contact.wtH`).

* **TB.sub** (definitions): `precSub` is `P̃^τ` with the incident signs at `i` replaced by a real
  vector `x ∈ ℝ^J`; `wSub` is the paired weight at `x` (`= W(σ)` at `x = ξ_σ`); `diagSub` the
  physical (shifted) inverse diagonals at `x`; `wtHSub` the weight `H` at `x`. The Rademacher
  numerator of `E[H q_L]` is `Σ_σ 𝖱[W H q_L]/Z` (star resummation) and the Gaussian numerators are
  `x_G = Σ_σ 𝖦[W H q_L]/Z`, `y_G = Σ_σ tr L · 𝖦[W H]/Z` (`gNumQ`, `gNumT`).
* **TB.WT3** (`wt3_gauss`): for every signing, if `m₀ + 4 ≤ p`,
  `𝖦[W H q_L] ≤ tr L · 𝖦[W H]` (core fixed). TB.WT3d (`wt3Rho_midpoint`) by the elementary route
  of `Tight/Tools/LogConcaveDet.lean`: on the (midpoint convex) support
  `W H = D^{p-|L|} Π_{t ∈ L} (D g_t)` with `D = det P̃⁺ det P̃⁻` and `g_t` the diagonal factors;
  `D` and each `D g_t = y_k det P̃^{-b} · det P̃^b ((P̃^b + zY)⁻¹)_kk` are midpoint log-concave
  along the affine family `x ↦ P̃(x)` (`det A₁ det A₂ ≤ det(A)²`; Cramer; `det P/det(P + zY) =
  det(I - B(P + zY)⁻¹Bᵀ)` and midpoint operator convexity of the inverse). The gauge flip at `i`
  (`x ↦ -x`) fixes every principal minor, so `W H` is even. Then BLmid (`Tight/Gauss/BLmid.lean`)
  with `K = I` (Gaussian covariance `⪯ I`).
* **TB.WT5** (`wt5_transfer`): `|x_G - x| + |y_G - y| ≤ K (p⁴/d)(x + y + d^{-M}) + e^{-p}`
  with `x = E[H q_L(ξ)]`, `y = E[H tr L]`, `K = K(m₀, M)`. With the observables
  `F^Q_σ = W H q_L`, `F^T_σ = tr L · W H` (`obsQ`, `obsT`): TB.WT5a (`massQ_eq_radE`,
  `massT_eq_radE`, exact) `x = Σ_σ 𝖱F^Q_σ/Z` by star resummation (`sum_sum_setRoot`); TB.WT5s
  (`abs_sum_gauss_sub_rad_le`, exact) splits `Σ_σ (𝖦 - 𝖱)F_σ/Z` into the (E4) remainder `remSum`
  at depth `k_* = kStarA d p` and the retained grades `≥ 1` (`retSum`); TB.WT5i (`wSub_eq_star`,
  `obsQ_eq`, exact): insertion at a real star vector, `W(x) = W_core (D⁺_i D⁻_i)^p Φ(x)`, so
  `F_σ = W_core (D⁺_i D⁻_i)^p F°_σ` with the normalized observables `Φ H q_L`, `tr L Φ H`
  (`starObsQ`, `starObsT`); TB.WT5c (`remSum_eq_core`, `retSum_eq_core`, exact): both sums are
  own-core averages divided by `F_H`; TB.WT5r° (`wt5_rem_core`, open): own-core remainder
  `≤ F_H d^{-M-1}`; TB.WT5g° (`wt5_ret_core`): own-core retained grades
  `≤ K(p⁴/d)(x + y + ϑ) F_H`, from A-RET (`coreRet_div_insF_eq`, core-measurability
  `starObsQ_congr`), TB.WT5v (`starObs_vanish`, open: vanishing at clipped sign vectors) and
  TB.WT5l (`wt5_ret_law`, open: the TRC-G form, (WT4) endpoint bounds and grade sums).
* **TB.abs** (`wt2_absorb`, real algebra): `x ≤ x_G + η(x+y+ϑ) + e`, `x_G ≤ y_G`,
  `y_G ≤ y + η(x+y+ϑ) + e`, `0 ≤ η ≤ 1/4`, `x ≥ 0` imply `x ≤ 3y + ϑ + 4e`.
* **TB.WT2** (`wt2`): `E[H q_L] ≤ 4 E[H tr L] + 4 d^{-M} + 4 e^{-p}`, from TB.WT3 (summed:
  `x_G ≤ y_G`), TB.WT5 (with `K p⁴/d ≤ 1/4` for large `d`) and TB.abs.

**Checks.** `J = ∅` (isolated `i`): `L` is `0 × 0`, `q_L = tr L = 0`, all four numerators vanish.
`T_cav` with `|N| ≤ 2`: the sum over `k ∈ N \ {i, l}` may be empty, `L = 0`. Zero sources: the
corresponding physical diagonals vanish, so `H = 0` and both sides vanish.
-/

@[expose] public section

namespace BiluLinial.Tight.SecB

open Matrix

universe u

section WT5

variable {d p : ℕ} (ct : Contact.{u} d p)

/-- **TB.WT5g°** (own-core retained grades `1 ≤ |j|_g ≤ k_*`). Proof: A-RET for the retained
grades (`coreRet_div_insF_eq`, from `SecA.lawE_eq_coreE_div`) with the core-measurability
`starObsQ_congr` and TB.WT5v, `F_H > 0` (`insF_pos_ct`), then TB.WT5l. -/
theorem wt5_ret_core (m₀ M : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ Eventually fun _ _ d p h =>
    ∀ ct : Contact.{u} d p, ∀ i ∈ ct.N, ∀ e dir : Bool, ∀ l : List (ct.V × Bool × Bool),
      l.length ≤ m₀ →
      |coreE ct.G p (aOf d p) ct.yp ct.ym ct.S i
            (coreRet ct i (starObsQ ct h e dir i l) (kStarA d p))| +
          |coreE ct.G p (aOf d p) ct.yp ct.ym ct.S i
            (coreRet ct i (starObsT ct h e dir i l) (kStarA d p))| ≤
        K * ((p : ℝ) ^ 4 / d) *
            (massQ ct h e dir i l + massT ct h e dir i l + 1 / (d : ℝ) ^ M) *
          insF ct.G p (aOf d p) ct.yp ct.ym ct.S i := by
  obtain ⟨K, hK, hlaw⟩ := wt5_ret_law.{u} m₀ M
  refine ⟨K, hK, ((hlaw.and (starObs_vanish.{u} m₀)).and (eventually_base 1)).mono ?_⟩
  rintro c₀ κ₀ d p h ⟨⟨hL, hV⟩, hR, -⟩ ct i hi e dir l hl
  have hp : 1 ≤ p := le_trans (by norm_num) hR.two_le_p
  have hiS : i ∈ ct.S := (Finset.mem_filter.1 hi).1
  have hF := insF_pos_ct ct hR hiS
  have hQ := coreRet_div_insF_eq ct hp hiS (starObsQ ct h e dir i l)
    (fun σ σ' hσ => starObsQ_congr ct h e dir l hσ) (kStarA d p)
    (fun σ j hj ξ hξ hΦ => (hV ct i hi e dir l hl σ j hj ξ hξ hΦ).1)
  have hT := coreRet_div_insF_eq ct hp hiS (starObsT ct h e dir i l)
    (fun σ σ' hσ => starObsT_congr ct h e dir l hσ) (kStarA d p)
    (fun σ j hj ξ hξ hΦ => (hV ct i hi e dir l hl σ j hj ξ hξ hΦ).2)
  rw [div_eq_iff hF.ne'] at hQ hT
  rw [hQ, hT, abs_mul, abs_mul, abs_of_pos hF, ← add_mul]
  exact mul_le_mul_of_nonneg_right (hL ct i hi e dir l hl) hF.le

/-- **TB.WT5r** (the (E4) remainder, summed over signings): `≤ d^{-M-1}`. Proof: TB.WT5c
(`remSum_eq_core` with TB.WT5i, `obsQ_eq`, `obsT_eq`) and TB.WT5r°. -/
theorem wt5_rem (m₀ M : ℕ) : Eventually fun _ _ d p h =>
    ∀ ct : Contact.{u} d p, ∀ i ∈ ct.N, ∀ e dir : Bool, ∀ l : List (ct.V × Bool × Bool),
      l.length ≤ m₀ →
      remSum ct i (obsQ ct h e dir i l) (kStarA d p) +
          remSum ct i (obsT ct h e dir i l) (kStarA d p) ≤ 1 / (d : ℝ) ^ (M + 1) := by
  refine ((wt5_rem_core.{u} m₀ M).and (eventually_base 1)).mono ?_
  rintro c₀ κ₀ d p h ⟨hc, hR, -⟩ ct i hi e dir l hl
  have hp : 1 ≤ p := le_trans (by norm_num) hR.two_le_p
  have hiS : i ∈ ct.S := (Finset.mem_filter.1 hi).1
  rw [remSum_eq_core ct hp hiS _ _ (obsQ_eq ct hp h e dir hiS l),
    remSum_eq_core ct hp hiS _ _ (obsT_eq ct hp h e dir hiS l), ← add_div]
  have h1 := hc ct i hi e dir l hl
  rcases (insF_nonneg' ct i).eq_or_lt with h0 | h0
  · rw [← h0, div_zero]
    positivity
  · rw [div_le_iff₀ h0]
    calc _ ≤ _ := h1
      _ = 1 / (d : ℝ) ^ (M + 1) * insF ct.G p (aOf d p) ct.yp ct.ym ct.S i := by ring

/-- **TB.WT5g** (the retained grades `≥ 1`, summed over signings). Proof: TB.WT5c
(`retSum_eq_core`) and TB.WT5g°. -/
theorem wt5_ret (m₀ M : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ Eventually fun _ _ d p h =>
    ∀ ct : Contact.{u} d p, ∀ i ∈ ct.N, ∀ e dir : Bool, ∀ l : List (ct.V × Bool × Bool),
      l.length ≤ m₀ →
      |retSum ct i (obsQ ct h e dir i l) (kStarA d p)| +
          |retSum ct i (obsT ct h e dir i l) (kStarA d p)| ≤
        K * ((p : ℝ) ^ 4 / d) *
          (massQ ct h e dir i l + massT ct h e dir i l + 1 / (d : ℝ) ^ M) := by
  obtain ⟨K, hK, hc⟩ := wt5_ret_core.{u} m₀ M
  refine ⟨K, hK, (hc.and (eventually_base 1)).mono ?_⟩
  rintro c₀ κ₀ d p h ⟨hc, hR, -, -, hh, hk0, -⟩ ct i hi e dir l hl
  have hp : 1 ≤ p := le_trans (by norm_num) hR.two_le_p
  have hiS : i ∈ ct.S := (Finset.mem_filter.1 hi).1
  have hh0 : 0 ≤ h := by rw [hh]; exact div_nonneg hk0.le (by positivity)
  have hx : 0 ≤ massQ ct h e dir i l := lawE_nonneg ct.G fun σ hσ =>
    mul_nonneg (wtH_nonneg ct hh0 e i l hσ) (qForm_nonneg (kerL_posSemidef ct h e dir i σ) _)
  have hy : 0 ≤ massT ct h e dir i l := lawE_nonneg ct.G fun σ hσ =>
    mul_nonneg (wtH_nonneg ct hh0 e i l hσ) (kerL_posSemidef ct h e dir i σ).trace_nonneg
  rw [retSum_eq_core ct hp hiS _ _ (obsQ_eq ct hp h e dir hiS l),
    retSum_eq_core ct hp hiS _ _ (obsT_eq ct hp h e dir hiS l), abs_div, abs_div,
    abs_of_nonneg (insF_nonneg' ct i), ← add_div]
  have h1 := hc ct i hi e dir l hl
  rcases (insF_nonneg' ct i).eq_or_lt with h0 | h0
  · rw [← h0, div_zero]
    exact mul_nonneg (mul_nonneg hK (by positivity)) (add_nonneg (add_nonneg hx hy) (by positivity))
  · rw [div_le_iff₀ h0]
    exact h1

/-- **TB.WT5** (retained comparison terms preserve the unknown mass; analytic). For fixed `m₀` and
`M` there is `K` such that eventually, at every contact, `i ∈ N`, branch `e`, map `T` and weight
with at most `m₀` extra diagonals:
`|x_G - x| + |y_G - y| ≤ K (p⁴/d)(x + y + d^{-M}) + e^{-p}`. Proof: `x_G = Σ_σ 𝖦F^Q_σ/Z`
(`gNumQ_eq`), `x = Σ_σ 𝖱F^Q_σ/Z` (TB.WT5a, `massQ_eq_radE`), likewise for `y`; split
`𝖦 - 𝖱` into the (E4) remainder and the retained grades `≥ 1` (TB.WT5s), bounded by TB.WT5r
(`≤ d^{-M-1} ≤ (p⁴/d) d^{-M}`) and TB.WT5g. -/
theorem wt5_transfer (m₀ M : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ Eventually fun _ _ d p h =>
    ∀ ct : Contact.{u} d p, ∀ i ∈ ct.N, ∀ e dir : Bool, ∀ l : List (ct.V × Bool × Bool),
      l.length ≤ m₀ →
      |gNumQ ct h e dir i l - massQ ct h e dir i l| +
          |gNumT ct h e dir i l - massT ct h e dir i l| ≤
        K * ((p : ℝ) ^ 4 / d) *
            (massQ ct h e dir i l + massT ct h e dir i l + 1 / (d : ℝ) ^ M) +
          Real.exp (-(p : ℝ)) := by
  obtain ⟨K, hK, hret⟩ := wt5_ret.{u} m₀ M
  refine ⟨K + 1, by linarith, (((wt5_rem.{u} m₀ M).and hret).and (eventually_base 1)).mono ?_⟩
  rintro c₀ κ₀ d p h ⟨⟨hrem, hR⟩, hreg, -, -, hh, hk0, -⟩ ct i hi e dir l hl
  have hiS : i ∈ ct.S := (Finset.mem_filter.1 hi).1
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast le_trans (by norm_num) hreg.two_le_p
  have hd1 : (1 : ℝ) ≤ d := le_trans (by norm_num) hreg.ten_pow_six_le_d
  have hh0 : 0 ≤ h := by rw [hh]; exact div_nonneg hk0.le (by positivity)
  have hQ := abs_sum_gauss_sub_rad_le ct i (obsQ ct h e dir i l) (kStarA d p)
  have hT := abs_sum_gauss_sub_rad_le ct i (obsT ct h e dir i l) (kStarA d p)
  rw [← gNumQ_eq, ← massQ_eq_radE ct h e dir hiS] at hQ
  rw [← gNumT_eq, ← massT_eq_radE ct h e dir hiS] at hT
  have h1 := hrem ct i hi e dir l hl
  have h2 := hR ct i hi e dir l hl
  have hx : 0 ≤ massQ ct h e dir i l := lawE_nonneg ct.G fun σ hσ =>
    mul_nonneg (wtH_nonneg ct hh0 e i l hσ) (qForm_nonneg (kerL_posSemidef ct h e dir i σ) _)
  have hy : 0 ≤ massT ct h e dir i l := lawE_nonneg ct.G fun σ hσ =>
    mul_nonneg (wtH_nonneg ct hh0 e i l hσ) (kerL_posSemidef ct h e dir i σ).trace_nonneg
  set S := massQ ct h e dir i l + massT ct h e dir i l + 1 / (d : ℝ) ^ M with hS
  have hdM : (0 : ℝ) < (d : ℝ) ^ M := by positivity
  have h3 : 1 / (d : ℝ) ^ (M + 1) ≤ (p : ℝ) ^ 4 / d * S := by
    have hp4 : (1 : ℝ) ≤ (p : ℝ) ^ 4 := one_le_pow₀ hp1
    have e1 : 1 / (d : ℝ) ^ (M + 1) = 1 / d * (1 / (d : ℝ) ^ M) := by
      rw [pow_succ]
      field_simp
    have h4 : 1 / (d : ℝ) * (1 / (d : ℝ) ^ M) ≤ (p : ℝ) ^ 4 / d * (1 / (d : ℝ) ^ M) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact div_le_div_of_nonneg_right hp4 (by positivity)
    have h5 : (p : ℝ) ^ 4 / d * (1 / (d : ℝ) ^ M) ≤ (p : ℝ) ^ 4 / d * S := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [hS]
      linarith
    linarith
  have e2 : (K + 1) * ((p : ℝ) ^ 4 / d) * S = K * ((p : ℝ) ^ 4 / d) * S + (p : ℝ) ^ 4 / d * S := by
    ring
  have hexp : 0 ≤ Real.exp (-(p : ℝ)) := (Real.exp_pos _).le
  linarith

end WT5

/-- **TB.abs.** The absorption step of (WT2). -/
theorem wt2_absorb {x y xG yG η ϑ e : ℝ} (hx : 0 ≤ x) (hη : η ≤ 1 / 4)
    (hϑ : 0 ≤ ϑ) (h1 : x ≤ xG + η * (x + y + ϑ) + e) (h2 : xG ≤ yG)
    (h3 : yG ≤ y + η * (x + y + ϑ) + e) (hy : 0 ≤ y) : x ≤ 3 * y + ϑ + 4 * e := by
  have h4 : x ≤ y + 2 * η * (x + y + ϑ) + 2 * e := by linarith
  have h5 : 2 * η * x ≤ x / 2 := by nlinarith
  have h6 : 2 * η * y ≤ y / 2 := by nlinarith
  have h7 : 2 * η * ϑ ≤ ϑ / 2 := by nlinarith
  nlinarith

/-- `x_G ≤ y_G`: TB.WT3 summed over signings. -/
theorem gNumQ_le_gNumT {d p : ℕ} (ct : Contact.{u} d p) {h : ℝ} (hh : 0 ≤ h) (e dir : Bool)
    {i : ct.V} (hi : i ∈ ct.N) (l : List (ct.V × Bool × Bool)) (hl : l.length + 4 ≤ p) :
    gNumQ ct h e dir i l ≤ gNumT ct h e dir i l := by
  unfold gNumQ gNumT
  refine div_le_div_of_nonneg_right (Finset.sum_le_sum fun σ _ => ?_) (Zw_nonneg ct.G)
  exact wt3_gauss ct hh e dir hi l hl σ

/-- **TB.WT2.** For fixed `m₀`, `M`: eventually, at every contact, `i ∈ N`, branch `e`, cavity map
`T ∈ {T_dir, T_cav}` and weight `H = H₀ (X_e)_ii² (X₊)_ii²` with `|H₀| ≤ m₀`:
`E[H q_L(ξ)] ≤ 4 E[H tr L] + 4 d^{-M} + 4 e^{-p}`. -/
theorem wt2 (m₀ M : ℕ) : ∃ K : ℝ, 0 < K ∧ Eventually fun _ _ d p h =>
    ∀ ct : Contact.{u} d p, ∀ i ∈ ct.N, ∀ e dir : Bool, ∀ l : List (ct.V × Bool × Bool),
      l.length ≤ m₀ →
      ct.E (fun σ => ct.wtH h e i l σ * qForm (kerL ct h e dir i σ) (rootSigns ct.G σ ct.S i)) ≤
        K * ct.E (fun σ => ct.wtH h e i l σ * (kerL ct h e dir i σ).trace) +
          K / (d : ℝ) ^ M + K * Real.exp (-(p : ℝ)) := by
  obtain ⟨K, hK, hT⟩ := wt5_transfer.{u} m₀ M
  refine ⟨4, by norm_num, ((hT.and (eventually_base (m₀ + 4 + 4 * K))).and
    eventually_h_facts).mono ?_⟩
  rintro c₀ κ₀ d p h ⟨⟨hT5, hR, hB, -⟩, -, h0, -⟩ ct i hi e dir l hl
  have hp : (m₀ : ℝ) + 4 ≤ p := by have := hK; nlinarith
  have hlp : l.length + 4 ≤ p := by
    have : (l.length : ℝ) + 4 ≤ p := le_trans (by exact_mod_cast Nat.add_le_add_right hl 4) hp
    exact_mod_cast this
  have hd0 : (0 : ℝ) < d := by have := hR.ten_pow_six_le_d; linarith
  have hP := regime_p_pos hR
  have hd8 := regime_p8_le hR
  -- `η = K p⁴/d ≤ 1/4`
  have hη0 : 0 ≤ K * ((p : ℝ) ^ 4 / d) := by positivity
  have hη : K * ((p : ℝ) ^ 4 / d) ≤ 1 / 4 := by
    have h4K : 4 * K ≤ (p : ℝ) := by
      have := (show (0 : ℝ) ≤ m₀ by positivity); linarith
    rw [← mul_div_assoc, div_le_div_iff₀ hd0 (by norm_num)]
    have hp4 : (p : ℝ) ^ 4 * p ≤ d := by
      have : (p : ℝ) ^ 5 ≤ (p : ℝ) ^ 8 := pow_le_pow_right₀ (by linarith) (by norm_num)
      nlinarith
    nlinarith [pow_nonneg hP.le 4]
  set x := massQ ct h e dir i l
  set y := massT ct h e dir i l
  have hx : 0 ≤ x := lawE_nonneg ct.G fun σ hσ =>
    mul_nonneg (wtH_nonneg ct h0.le e i l hσ) (qForm_nonneg (kerL_posSemidef ct h e dir i σ) _)
  have hy : 0 ≤ y := lawE_nonneg ct.G fun σ hσ =>
    mul_nonneg (wtH_nonneg ct h0.le e i l hσ) (kerL_posSemidef ct h e dir i σ).trace_nonneg
  have h5 := hT5 ct i hi e dir l hl
  have hxy := gNumQ_le_gNumT ct h0.le e dir hi l hlp
  have hϑ : (0 : ℝ) ≤ 1 / (d : ℝ) ^ M := by positivity
  have a1 := abs_le.mp (le_trans (le_add_of_nonneg_right (abs_nonneg _)) h5)
  have a2 := abs_le.mp (le_trans (le_add_of_nonneg_left (abs_nonneg _)) h5)
  have key := wt2_absorb hx hη hϑ (xG := gNumQ ct h e dir i l) (yG := gNumT ct h e dir i l)
    (e := Real.exp (-(p : ℝ))) (by linarith [a1.1]) hxy (by linarith [a2.2]) hy
  have hex : 0 ≤ Real.exp (-(p : ℝ)) := (Real.exp_pos _).le
  have : x ≤ 4 * y + 4 / (d : ℝ) ^ M + 4 * Real.exp (-(p : ℝ)) := by
    have : 1 / (d : ℝ) ^ M ≤ 4 / (d : ℝ) ^ M :=
      div_le_div_of_nonneg_right (by norm_num) (by positivity)
    linarith
  exact this

end BiluLinial.Tight.SecB
