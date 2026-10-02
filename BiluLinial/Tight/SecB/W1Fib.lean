/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecB.W1FibEdge

/-!
# The weak loop (W1): first-order endpoint integration by parts on the edge fibres

Node TB.W1fib of `docs/tight/BP_SECB.md` (source l.776–779, 840–903; AUDIT-B §2.4, fixes B-2,
B-3; `docs/tight/DR1_CHECK.md` §3). For an edge `ij` (`i ∈ N`, `j ∼ i`) and a configuration
`(ε, H, ∂H, X_ε, X_ν = X₊, f, ∂f)`, let `Ψ = H F_ji` and let `DΨ` (`fibD`) be its first-order
fibre derivative `∂Ψ + Ψ ∂ log W`:
`DΨ = ∂_ij H·F_ji + 2pa(G⁺_ij - G⁻_ij) H F_ji + H·sec_ij + H F_ji(∂_ij f) - a H (X_ε)_ii (X_ν)_ii U_jj`
(W3 with `ν = +`; checked by finite differences, residual `5·10⁻¹³`). The per-edge remainder of the
first-order endpoint identity is `Rem_ij = E[σ_ij Ψ] - E[DΨ]` (`fibRem`).

* **TB.W1fib-alg** (`weak_fibre_alg`, exact): the left side of `weak_fibre_of` equals
  `a Σ_{i∈N} Σ_{j∼i} u_i Rem_ij`.
* **TB.W1fib-edge** (`weak_fibre_edge`, analytic, open): there are `C, M` with
  `|Rem_ij| ≤ C (a³/(√d h)) E[D_*^M (p³ R_ij² + p)]`, `R_ij = |G⁺_ij| + |G⁻_ij|` (`fibR`). Sketch
  (source l.840–903): by the sign-fibre identity (`sum_sgn_fibre`) `E[σ_ij Ψ]` is a sum over the
  fibres `{σ, σ^{ij}}` of `φ(1) - φ(-1)`, `φ(t) = W Ψ` at the edge value `t`; on a regular fibre
  (endpoint diagonal sum `≤ (64pa)⁻¹`: the segment is positive definite, `G(t) ⪯ 2G(σ)`, weight
  ratios `≤ e^{1/16}`) the trapezoid rule (`trapezoid_chain`) gives
  `|(φ(1)-φ(-1))/2 - (φ'(1)+φ'(-1))/2| ≤ (2/3) sup|φ'''|` with `φ'(±1) = W·DΨ` at the endpoints, and
  `W⁻¹|φ'''| ≤ C a³ D_*^C (p³R³ + p²R² + p²R + p + 1)/(√d h) ≤ C a³ D_*^C (p³R² + p)/(√d h)`
  (`R ≤ 2D_*`, `p²R ≤ (p³R² + p)/2`); on a non-regular fibre `1 ≤ (64pa·4D_*)⁸` (Markov) and the
  terms are bounded directly, `(pa)⁸ ≤ a³ p` for `p⁷a⁵ ≤ 1`. Checked numerically (6-vertex graph,
  full paired law, `a → 0`): `|Rem_ij|/a³` constant, ratio to the bound `≤ 7.4·10⁻⁵` (`M = 6`).
* **TB.W1fib-avg** (`weak_fibre_avg`, open): for every `M`,
  `Σ_{i∈N} Σ_{j∼i} E[D_*^M R_ij²] ≤ C d² (δ̄ + 1/d)` and `E[D_*^M] ≤ C`. Sketch: `Σ_{j∼i} R_ij² ≤
  2Σ_j((G⁺_ij)² + (G⁻_ij)²)` has mean `≤ 2(S⁺_i + S⁻_i) ≤ 4K_δ δ̄/a² ≤ 20 K_δ δ̄ d` by (C2) at `w = i`,
  pointwise envelope `≤ 4dD_*²`; UMI (`wavg_mul_le_umi`) with weight `D_*^M`, floor `1` and
  `k ≈ log d` moments (TB.Dstar) gives `E[D_*^M Σ_j R²] ≤ C(dδ̄ + 1)`; `E[D_*^M] ≤ C` by Lyapunov from
  TB.Dstar at order `k ≈ log d`.
* **TB.W1fib** (`weak_fibre_of`, proved from the three): `a Σ u_i |Rem_ij| ≤
  C a⁴ d (p³(δ̄ + 1/d) + p)/h ≤ 5C p/(dh) ≤ 5C B₀` (`a⁴d ≤ 1/d`, `δ̄ + 1/d ≤ 4/p²`).
* Files: the definitions and generic tools (`trapezoid_chain`, `sum_sgn_fibre`, `sum_fibre_pair`,
  `FibChain`, `fibre_ibp_bound`, `fibD`, `fibRem`, `weak_fibre_alg`) are in `SecB/W1FibDefs.lean`;
  the pointwise bounds in `SecB/W1FibNonreg.lean`; the configurations in `SecB/W1FibCfg.lean`;
  TB.W1fib-reg and its sub-nodes in `SecB/W1FibReg.lean` (tools `SecB/W1FibSeg.lean`,
  `SecB/W1FibSmooth.lean`); TB.W1fib-nonreg and TB.W1fib-edge in `SecB/W1FibEdge.lean`.
-/

@[expose] public section

namespace BiluLinial.Tight.SecB

open Matrix

universe u

theorem abs_add_abs_sq_le (x y : ℝ) : (|x| + |y|) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) := by
  have h := sq_nonneg (|x| - |y|)
  rw [← sq_abs x, ← sq_abs y]
  nlinarith

/-- **TB.W1fib-avg** (moment averaging of the incident rows; open). Given (C2): for every `M` there
is `C > 0` such that eventually, at every contact,
`Σ_{i∈N} Σ_{j∼i} E[D_*^M R_ij²] ≤ C d² (δ̄ + 1/d)` and `E[D_*^M] ≤ C`. Sketch: module docstring. -/
theorem weak_fibre_avg {Kδ : ℝ} (hKδ : 0 ≤ Kδ) (hC2 : C2RowShape.{u} Kδ) (M : ℕ) :
    ∃ C : ℝ, 0 < C ∧ Eventually fun _c₀ _κ₀ d p _h => ∀ ct : Contact.{u} d p,
      ∑ i ∈ ct.N, ∑ j ∈ nbhd ct.G ct.S i, ct.E (fun σ => ct.Dstar σ ^ M * fibR ct σ i j ^ 2) ≤
          C * (d : ℝ) ^ 2 * (dbar d p + 1 / d) ∧
        ct.E (fun σ => ct.Dstar σ ^ M) ≤ C := by
  set B : ℝ := 21 * 12 ^ M with hBdef
  have hB1 : 1 ≤ B := by
    have := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 12) (n := M)
    rw [hBdef]; linarith
  refine ⟨16 * B * (8 * Kδ + 1) + 2 * B, by positivity,
    (((hC2.and dstar_moment).and (eventually_log_le_p (2 * ((M : ℝ) + 2)))).and
      (eventually_base 0)).mono ?_⟩
  rintro c₀ κ₀ d p h ⟨⟨⟨hc2, hDs⟩, hlp⟩, hR, -⟩ ct
  have hd6 : (10 : ℝ) ^ 6 ≤ d := hR.ten_pow_six_le_d
  have hd1 : (1 : ℝ) ≤ d := by linarith
  have hd0 : (0 : ℝ) < d := by linarith
  have hlogd : 0 ≤ Real.log d := Real.log_nonneg hd1
  obtain ⟨c', hc'⟩ : ∃ c' : ℕ, c' = ⌈Real.log d⌉₊ := ⟨_, rfl⟩
  have hcl : Real.log d ≤ c' := hc' ▸ Nat.le_ceil _
  have hcu : (c' : ℝ) < Real.log d + 1 := hc' ▸ Nat.ceil_lt_add_one hlogd
  have hk2 : 2 ≤ c' + 2 := by omega
  have hkp : 2 * ((M + 2) * (c' + 2)) ≤ p := by
    have h1 : 2 * ((M : ℝ) + 2) * ((c' : ℝ) + 2) ≤ p := by
      have : (c' : ℝ) + 2 ≤ Real.log d + 3 := by linarith
      calc 2 * ((M : ℝ) + 2) * ((c' : ℝ) + 2) ≤ 2 * ((M : ℝ) + 2) * (Real.log d + 3) :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ ≤ p := hlp
    have : ((2 * ((M + 2) * (c' + 2)) : ℕ) : ℝ) ≤ p := by push_cast; linarith
    exact_mod_cast this
  -- `3 (1 + d + d²) ≤ 21^k`
  have hpow21 : 3 * (1 + d + (d : ℝ) ^ 2) ≤ 21 ^ (c' + 2) := by
    have hdexp : (d : ℝ) ≤ Real.exp 1 ^ c' := by
      rw [← Real.exp_nat_mul, mul_one]
      calc (d : ℝ) = Real.exp (Real.log d) := (Real.exp_log hd0).symm
        _ ≤ Real.exp c' := Real.exp_le_exp.mpr hcl
    have he : Real.exp 1 ^ 2 ≤ 8 := by
      have := Real.exp_one_lt_d9; have := Real.exp_pos 1; nlinarith
    have hd2 : (d : ℝ) ^ 2 ≤ 8 ^ c' :=
      calc (d : ℝ) ^ 2 ≤ (Real.exp 1 ^ c') ^ 2 := pow_le_pow_left₀ hd0.le hdexp 2
        _ = (Real.exp 1 ^ 2) ^ c' := by rw [← pow_mul, ← pow_mul, mul_comm]
        _ ≤ 8 ^ c' := pow_le_pow_left₀ (by positivity) he c'
    have h8 : (8 : ℝ) ^ c' ≤ 21 ^ c' := pow_le_pow_left₀ (by norm_num) (by norm_num) c'
    have : 3 * (1 + d + (d : ℝ) ^ 2) ≤ 9 * (d : ℝ) ^ 2 := by nlinarith
    rw [pow_add]
    nlinarith
  have hs := hR.sOf_pos
  have hsub : ∀ y : ct.V → ℝ, InCube (ct.lam * sOf d p) y → InCube (sOf d p) y := fun y hy k =>
    ⟨(hy k).1, le_trans (hy k).2 (by nlinarith [ct.ctx.lam_le_one, ct.ctx.lam_nonneg])⟩
  have hZw : 0 < Zw ct.G p (aOf d p) ct.yp ct.ym ct.S :=
    ct.ctx.pos ct.yp ct.ym (hsub _ ct.ctx.hyp) (hsub _ ct.ctx.hym)
  -- the weight `Z = |D_*|^M`
  set Z : Config ct.V → ℝ := fun σ => |ct.Dstar σ| ^ M with hZdef
  have hZ0 : ∀ σ, 0 ≤ Z σ := fun σ => pow_nonneg (abs_nonneg _) M
  have hZeq : ∀ σ, wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 → Z σ = ct.Dstar σ ^ M :=
    fun σ hσ => by simp only [hZdef, abs_of_nonneg (dstar_nonneg ct hσ)]
  have hZk : ct.E (fun σ => Z σ ^ (c' + 2)) ≤ B ^ (c' + 2) := by
    rcases Nat.eq_zero_or_pos M with hm | hm
    · have : ct.E (fun σ => Z σ ^ (c' + 2)) = 1 := by
        rw [← lawE_const ct.G hZw.ne' 1]
        exact lawE_congr ct.G fun σ _ => by simp [hZdef, hm]
      rw [this]
      exact one_le_pow₀ hB1
    · have hn1 : 1 ≤ M * (c' + 2) := Nat.one_le_iff_ne_zero.mpr (by positivity)
      have hmk2 : 2 * (M * (c' + 2)) ≤ p := le_trans (by nlinarith) hkp
      calc ct.E (fun σ => Z σ ^ (c' + 2)) = ct.E (fun σ => ct.Dstar σ ^ (M * (c' + 2))) :=
            lawE_congr ct.G fun σ hσ => by rw [hZeq σ hσ, ← pow_mul]
        _ ≤ 3 * (1 + d + (d : ℝ) ^ 2) * 12 ^ (M * (c' + 2)) := hDs ct _ hn1 hmk2
        _ ≤ 21 ^ (c' + 2) * 12 ^ (M * (c' + 2)) :=
            mul_le_mul_of_nonneg_right hpow21 (by positivity)
        _ = B ^ (c' + 2) := by rw [hBdef, mul_pow, ← pow_mul, mul_comm M]
  have hD2k : ct.E (fun σ => ct.Dstar σ ^ (2 * (c' + 2))) ≤ (21 * 144) ^ (c' + 2) := by
    have h2 : 2 * (2 * (c' + 2)) ≤ p := le_trans (by nlinarith) hkp
    calc ct.E (fun σ => ct.Dstar σ ^ (2 * (c' + 2)))
        ≤ 3 * (1 + d + (d : ℝ) ^ 2) * 12 ^ (2 * (c' + 2)) := hDs ct _ (by omega) h2
      _ ≤ 21 ^ (c' + 2) * 144 ^ (c' + 2) := by
          rw [pow_mul]
          exact mul_le_mul hpow21 (by norm_num) (by positivity) (by positivity)
      _ = (21 * 144) ^ (c' + 2) := by rw [mul_pow]
  -- the interpolation loss
  have hkpos : (0 : ℝ) < ((c' + 2 : ℕ) : ℝ) - 1 := by push_cast; linarith
  have hL : (6048 * (d : ℝ) / 1) ^ (1 / (((c' + 2 : ℕ) : ℝ) - 1)) ≤ 8 := by
    rw [div_one]
    calc (6048 * (d : ℝ)) ^ (1 / (((c' + 2 : ℕ) : ℝ) - 1))
        ≤ ((d : ℝ) ^ 2) ^ (1 / (((c' + 2 : ℕ) : ℝ) - 1)) :=
          Real.rpow_le_rpow (by positivity) (by nlinarith) (by positivity)
      _ = Real.exp (Real.log ((d : ℝ) ^ 2) * (1 / (((c' + 2 : ℕ) : ℝ) - 1))) :=
          Real.rpow_def_of_pos (by positivity) _
      _ ≤ Real.exp 2 := by
          apply Real.exp_le_exp.mpr
          rw [Real.log_pow, mul_one_div, div_le_iff₀ hkpos]
          push_cast
          linarith
      _ ≤ 8 := by
          have e : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
          rw [e]
          have := Real.exp_one_lt_d9; have := Real.exp_pos 1; nlinarith
  -- one row
  have hrow : ∀ i ∈ ct.N, ct.E (fun σ => ∑ j ∈ nbhd ct.G ct.S i,
      ct.Dstar σ ^ M * fibR ct σ i j ^ 2) ≤ 2 * (B * 8 * (8 * Kδ * dbar d p * d + 1)) := by
    intro i hi
    have hiS := w1_N_sub_S ct hi
    set Y : Config ct.V → ℝ := fun σ => ∑ j ∈ nbhd ct.G ct.S i,
      (ct.gp σ i j ^ 2 + ct.gm σ i j ^ 2) with hYdef
    have hY0 : ∀ σ, 0 ≤ Y σ := fun σ => Finset.sum_nonneg fun j _ => by positivity
    have hYenv : ∀ σ, wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 →
        Y σ ≤ 2 * d * ct.Dstar σ ^ 2 := by
      intro σ hσ
      obtain ⟨hpP, hpM⟩ := posDef_of_wt_ne_zero ct.G hσ
      have hb : ∀ j ∈ nbhd ct.G ct.S i,
          ct.gp σ i j ^ 2 + ct.gm σ i j ^ 2 ≤ 2 * ct.Dstar σ ^ 2 := by
        intro j hj
        have hsqP : ct.gp σ i j ^ 2 ≤ ct.gp σ i i * ct.gp σ j j :=
          greenP_sq_le ct.G hpP (fun k => (ct.ctx.hyp k).1) i j
        have hsqM : ct.gm σ i j ^ 2 ≤ ct.gm σ i i * ct.gm σ j j :=
          greenP_sq_le ct.G hpM (fun k => (ct.ctx.hym k).1) i j
        obtain ⟨di1, di2⟩ := w1_diag_le_Dstar ct (w1Ball_N ct hi) σ
        obtain ⟨dj1, dj2⟩ := w1_diag_le_Dstar ct (w1Ball_NN ct hi hj) σ
        obtain ⟨gi1, gi2⟩ := w1_gp_nonneg ct hσ i
        obtain ⟨gj1, gj2⟩ := w1_gp_nonneg ct hσ j
        have t1 : ct.gp σ i i * ct.gp σ j j ≤ ct.Dstar σ ^ 2 := by
          have := mul_le_mul (by linarith : ct.gp σ i i ≤ ct.Dstar σ)
            (by linarith : ct.gp σ j j ≤ ct.Dstar σ) gj1 (by linarith)
          nlinarith
        have t2 : ct.gm σ i i * ct.gm σ j j ≤ ct.Dstar σ ^ 2 := by
          have := mul_le_mul (by linarith : ct.gm σ i i ≤ ct.Dstar σ)
            (by linarith : ct.gm σ j j ≤ ct.Dstar σ) gj2 (by linarith)
          nlinarith
        linarith
      have hD0 := dstar_nonneg ct hσ
      calc Y σ ≤ ∑ _j ∈ nbhd ct.G ct.S i, 2 * ct.Dstar σ ^ 2 := Finset.sum_le_sum hb
        _ = ((nbhd ct.G ct.S i).card : ℝ) * (2 * ct.Dstar σ ^ 2) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (d : ℝ) * (2 * ct.Dstar σ ^ 2) :=
            mul_le_mul_of_nonneg_right (w1_card_nbhd ct i) (by positivity)
        _ = 2 * d * ct.Dstar σ ^ 2 := by ring
    have hYk : ct.E (fun σ => Y σ ^ (c' + 2)) ≤ (6048 * (d : ℝ)) ^ (c' + 2) := by
      calc ct.E (fun σ => Y σ ^ (c' + 2))
          ≤ ct.E (fun σ => (2 * (d : ℝ)) ^ (c' + 2) * ct.Dstar σ ^ (2 * (c' + 2))) :=
            lawE_mono ct.G fun σ hσ => by
              rw [pow_mul, ← mul_pow]
              exact pow_le_pow_left₀ (hY0 σ) (hYenv σ hσ) _
        _ = (2 * (d : ℝ)) ^ (c' + 2) * ct.E (fun σ => ct.Dstar σ ^ (2 * (c' + 2))) :=
            w1_E_const_mul ct _ _
        _ ≤ (2 * (d : ℝ)) ^ (c' + 2) * (21 * 144) ^ (c' + 2) :=
            mul_le_mul_of_nonneg_left hD2k (by positivity)
        _ = (6048 * (d : ℝ)) ^ (c' + 2) := by rw [← mul_pow]; congr 1; ring
    have humi := wavg_mul_le_umi (fun σ => wt_nonneg ct.G σ) hZw hY0 hZ0 hk2
      (by positivity : (0 : ℝ) ≤ 6048 * d) (by positivity : (0 : ℝ) ≤ B) one_pos hYk hZk
    have hEY : ct.E Y ≤ 8 * Kδ * dbar d p * d := by
      obtain ⟨-, -, hSP, hSM⟩ := hc2 ct.toCapPoint i hiS
      have hSP' : aOf d p ^ 2 * rowSP ct.G d p ct.yp ct.ym ct.S i ≤ Kδ * dbar d p := hSP
      have hSM' : aOf d p ^ 2 * rowSM ct.G d p ct.yp ct.ym ct.S i ≤ Kδ * dbar d p := hSM
      have e : ct.E Y = rowSP ct.G d p ct.yp ct.ym ct.S i + rowSM ct.G d p ct.yp ct.ym ct.S i := by
        unfold Contact.E rowSP rowSM
        rw [hYdef, lawE_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ => lawE_add ct.G _ _
      have hX0 : 0 ≤ rowSP ct.G d p ct.yp ct.ym ct.S i + rowSM ct.G d p ct.yp ct.ym ct.S i :=
        add_nonneg (Finset.sum_nonneg fun j _ => lawE_nonneg ct.G fun σ _ => sq_nonneg _)
          (Finset.sum_nonneg fun j _ => lawE_nonneg ct.G fun σ _ => sq_nonneg _)
      have ha2 := hR.pf_a_sq_ge
      have h4 : 1 ≤ 4 * (d : ℝ) * aOf d p ^ 2 := by
        rw [div_le_iff₀ (by positivity)] at ha2; linarith
      rw [e]
      have hS : aOf d p ^ 2 * (rowSP ct.G d p ct.yp ct.ym ct.S i +
          rowSM ct.G d p ct.yp ct.ym ct.S i) ≤ 2 * (Kδ * dbar d p) := by linarith
      have t1 : rowSP ct.G d p ct.yp ct.ym ct.S i + rowSM ct.G d p ct.yp ct.ym ct.S i ≤
          4 * (d : ℝ) * aOf d p ^ 2 *
            (rowSP ct.G d p ct.yp ct.ym ct.S i + rowSM ct.G d p ct.yp ct.ym ct.S i) :=
        le_mul_of_one_le_left hX0 h4
      have t2 : 4 * (d : ℝ) * (aOf d p ^ 2 *
          (rowSP ct.G d p ct.yp ct.ym ct.S i + rowSM ct.G d p ct.yp ct.ym ct.S i)) ≤
          4 * (d : ℝ) * (2 * (Kδ * dbar d p)) := mul_le_mul_of_nonneg_left hS (by positivity)
      have e2 : 4 * (d : ℝ) * aOf d p ^ 2 *
          (rowSP ct.G d p ct.yp ct.ym ct.S i + rowSM ct.G d p ct.yp ct.ym ct.S i) =
          4 * (d : ℝ) * (aOf d p ^ 2 *
            (rowSP ct.G d p ct.yp ct.ym ct.S i + rowSM ct.G d p ct.yp ct.ym ct.S i)) := by ring
      have e3 : 4 * (d : ℝ) * (2 * (Kδ * dbar d p)) = 8 * Kδ * dbar d p * d := by ring
      linarith
    have hYZ : ct.E (fun σ => Y σ * Z σ) ≤ B * 8 * (8 * Kδ * dbar d p * d + 1) := by
      refine le_trans humi ?_
      have hEY0 : 0 ≤ ct.E Y := lawE_nonneg ct.G fun σ _ => hY0 σ
      have hL0 : 0 ≤ (6048 * (d : ℝ) / 1) ^ (1 / (((c' + 2 : ℕ) : ℝ) - 1)) :=
        Real.rpow_nonneg (by positivity) _
      exact mul_le_mul (mul_le_mul_of_nonneg_left hL (by positivity))
        (by change ct.E Y + 1 ≤ 8 * Kδ * dbar d p * d + 1; linarith) (by positivity)
        (by positivity)
    calc ct.E (fun σ => ∑ j ∈ nbhd ct.G ct.S i, ct.Dstar σ ^ M * fibR ct σ i j ^ 2)
        ≤ ct.E (fun σ => 2 * (Y σ * Z σ)) := lawE_mono ct.G fun σ hσ => by
          rw [hZeq σ hσ, ← Finset.mul_sum]
          have hR2 : ∑ j ∈ nbhd ct.G ct.S i, fibR ct σ i j ^ 2 ≤ 2 * Y σ := by
            have hpt : ∀ j, fibR ct σ i j ^ 2 ≤ 2 * (ct.gp σ i j ^ 2 + ct.gm σ i j ^ 2) :=
              fun j => abs_add_abs_sq_le _ _
            calc ∑ j ∈ nbhd ct.G ct.S i, fibR ct σ i j ^ 2
                ≤ ∑ j ∈ nbhd ct.G ct.S i, 2 * (ct.gp σ i j ^ 2 + ct.gm σ i j ^ 2) :=
                  Finset.sum_le_sum fun j _ => hpt j
              _ = 2 * Y σ := by
                  change _ = 2 * ∑ j ∈ nbhd ct.G ct.S i, (ct.gp σ i j ^ 2 + ct.gm σ i j ^ 2)
                  rw [Finset.mul_sum]
          have hDM : 0 ≤ ct.Dstar σ ^ M := pow_nonneg (dstar_nonneg ct hσ) M
          calc ct.Dstar σ ^ M * ∑ j ∈ nbhd ct.G ct.S i, fibR ct σ i j ^ 2
              ≤ ct.Dstar σ ^ M * (2 * Y σ) := mul_le_mul_of_nonneg_left hR2 hDM
            _ = 2 * (Y σ * ct.Dstar σ ^ M) := by ring
      _ = 2 * ct.E (fun σ => Y σ * Z σ) := w1_E_const_mul ct _ _
      _ ≤ 2 * (B * 8 * (8 * Kδ * dbar d p * d + 1)) := by linarith
  refine ⟨?_, ?_⟩
  · have hsum : ∑ i ∈ ct.N, ∑ j ∈ nbhd ct.G ct.S i,
        ct.E (fun σ => ct.Dstar σ ^ M * fibR ct σ i j ^ 2) =
        ∑ i ∈ ct.N, ct.E (fun σ => ∑ j ∈ nbhd ct.G ct.S i,
          ct.Dstar σ ^ M * fibR ct σ i j ^ 2) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      unfold Contact.E
      rw [lawE_sum]
    rw [hsum]
    have hdb : 0 ≤ dbar d p := le_trans (regime_eps_nonneg hR) (le_dbar hR).1
    calc ∑ i ∈ ct.N, ct.E (fun σ => ∑ j ∈ nbhd ct.G ct.S i, ct.Dstar σ ^ M * fibR ct σ i j ^ 2)
        ≤ ∑ _i ∈ ct.N, 2 * (B * 8 * (8 * Kδ * dbar d p * d + 1)) := Finset.sum_le_sum hrow
      _ = (ct.N.card : ℝ) * (2 * (B * 8 * (8 * Kδ * dbar d p * d + 1))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (d : ℝ) * (2 * (B * 8 * (8 * Kδ * dbar d p * d + 1))) :=
          mul_le_mul_of_nonneg_right (w1_card_N ct) (by positivity)
      _ ≤ (16 * B * (8 * Kδ + 1) + 2 * B) * (d : ℝ) ^ 2 * (dbar d p + 1 / d) := by
          have e : (d : ℝ) ^ 2 * (dbar d p + 1 / d) = d ^ 2 * dbar d p + d := by
            field_simp
          have : (16 * B * (8 * Kδ + 1) + 2 * B) * (d : ℝ) ^ 2 * (dbar d p + 1 / d) =
              (16 * B * (8 * Kδ + 1) + 2 * B) * ((d : ℝ) ^ 2 * dbar d p + d) := by
            rw [mul_assoc, e]
          rw [this]
          have h1 : 0 ≤ (d : ℝ) ^ 2 * dbar d p := by positivity
          have p1 : 0 ≤ B * Kδ * d := by positivity
          have p2 : 0 ≤ B * ((d : ℝ) ^ 2 * dbar d p) := by positivity
          have p3 : 0 ≤ B * d := by positivity
          have e5 : (d : ℝ) * (2 * (B * 8 * (8 * Kδ * dbar d p * d + 1))) =
              128 * (B * Kδ) * ((d : ℝ) ^ 2 * dbar d p) + 16 * (B * d) := by ring
          have e6 : (16 * B * (8 * Kδ + 1) + 2 * B) * ((d : ℝ) ^ 2 * dbar d p + d) =
              128 * (B * Kδ) * ((d : ℝ) ^ 2 * dbar d p) + 128 * (B * Kδ * d) +
                18 * (B * ((d : ℝ) ^ 2 * dbar d p)) + 18 * (B * d) := by ring
          rw [e5, e6]
          linarith
  · have humi1 := wavg_mul_le_umi (fun σ => wt_nonneg ct.G σ) hZw (Y := fun _ => (1 : ℝ))
      (fun _ => zero_le_one) hZ0 hk2 zero_le_one (by positivity : (0 : ℝ) ≤ B) one_pos
      (by rw [wavg_const hZw]) hZk
    rw [wavg_const hZw, div_one, Real.one_rpow] at humi1
    calc ct.E (fun σ => ct.Dstar σ ^ M) = ct.E (fun σ => 1 * Z σ) :=
          lawE_congr ct.G fun σ hσ => by rw [hZeq σ hσ, one_mul]
      _ ≤ B * 1 * (1 + 1) := humi1
      _ ≤ 16 * B * (8 * Kδ + 1) + 2 * B := by nlinarith

/-! ### Assembly -/

/-- `δ̄ + 1/d ≤ 4/p²` in the regime (`ε ≤ p⁻³`, `p⁸ ≤ d`). -/
theorem dbar_add_le {d p : ℕ} (hR : TRegime d p) : dbar d p + 1 / d ≤ 4 / (p : ℝ) ^ 2 := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast le_trans (by norm_num) hR.hp
  have hp0 : (0 : ℝ) < p := by linarith
  have h8 := regime_p8_le hR
  have hd0 : (0 : ℝ) < d := lt_of_lt_of_le (by positivity) h8
  have hε := regime_eps_le hR
  have hp32 : 1 / (p : ℝ) ^ 3 ≤ 1 / (p : ℝ) ^ 2 :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ hp1 (by norm_num))
  have hp4d : (p : ℝ) ^ 4 / d ≤ 1 / (p : ℝ) ^ 2 := by
    rw [div_le_div_iff₀ hd0 (by positivity)]
    calc (p : ℝ) ^ 4 * (p : ℝ) ^ 2 = (p : ℝ) ^ 6 := by ring
      _ ≤ (p : ℝ) ^ 8 := pow_le_pow_right₀ hp1 (by norm_num)
      _ ≤ d := h8
      _ = 1 * d := by ring
  have hd1 : 1 / (d : ℝ) ≤ 1 / (p : ℝ) ^ 2 :=
    one_div_le_one_div_of_le (by positivity)
      (le_trans (pow_le_pow_right₀ hp1 (by norm_num)) h8)
  have hu : ((p : ℝ) / d) ^ ((1 : ℝ) / 3) ≤ 1 / (p : ℝ) ^ 2 := by
    have hu0 : 0 ≤ ((p : ℝ) / d) ^ ((1 : ℝ) / 3) := by positivity
    have hu3 : (((p : ℝ) / d) ^ ((1 : ℝ) / 3)) ^ 3 = (p : ℝ) / d := by
      rw [← Real.rpow_mul_natCast (by positivity)]; norm_num
    have hpd : (p : ℝ) / d ≤ (1 / (p : ℝ) ^ 2) ^ 3 := by
      rw [div_le_iff₀ hd0]
      have : (1 / (p : ℝ) ^ 2) ^ 3 * d ≥ (1 / (p : ℝ) ^ 2) ^ 3 * (p : ℝ) ^ 8 :=
        mul_le_mul_of_nonneg_left h8 (by positivity)
      have hpne : (p : ℝ) ≠ 0 := hp0.ne'
      have e : (1 / (p : ℝ) ^ 2) ^ 3 * (p : ℝ) ^ 8 = (p : ℝ) ^ 2 := by field_simp
      nlinarith
    rw [← hu3] at hpd
    exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) hpd
  unfold dbar
  have e4 : (4 : ℝ) / (p : ℝ) ^ 2 = 1 / (p : ℝ) ^ 2 + 1 / (p : ℝ) ^ 2 + 1 / (p : ℝ) ^ 2 +
      1 / (p : ℝ) ^ 2 := by ring
  rw [e4]
  linarith

/-- Real-number assembly of TB.W1fib. -/
theorem w1_fib_par {a s P h C₁ C₂ ρ N Y Z X : ℝ} (hs : 0 < s) (hP : 1 ≤ P) (hh : 0 < h)
    (ha : 0 ≤ a) (ha2 : a ^ 2 ≤ 1 / s ^ 2) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hρ0 : 0 ≤ ρ)
    (hρ : ρ ≤ 4 / P ^ 2) (hN : N ≤ s ^ 2) (hY : Y ≤ C₂ * (s ^ 2) ^ 2 * ρ)
    (hZ : Z ≤ N * s ^ 2 * C₂)
    (hX : X ≤ 1 / s * (C₁ * (a ^ 3 / (s * h)) * (P ^ 3 * Y + P * Z))) :
    a * X ≤ 5 * C₁ * C₂ * (P / (s ^ 2 * h)) := by
  have hs0 : s ≠ 0 := hs.ne'
  have hP0 : P ≠ 0 := by linarith
  have hZ' : Z ≤ (s ^ 2) ^ 2 * C₂ := by
    refine le_trans hZ ?_
    have := mul_le_mul_of_nonneg_right hN (by positivity : (0 : ℝ) ≤ s ^ 2 * C₂)
    nlinarith
  have hA : 0 ≤ C₁ * (a ^ 3 / (s * h)) := by positivity
  have hinner : P ^ 3 * Y + P * Z ≤ (s ^ 2) ^ 2 * C₂ * (P ^ 3 * ρ + P) := by
    have t1 := mul_le_mul_of_nonneg_left hY (by positivity : (0 : ℝ) ≤ P ^ 3)
    have t2 := mul_le_mul_of_nonneg_left hZ' (by positivity : (0 : ℝ) ≤ P)
    nlinarith
  have hPρ : P ^ 3 * ρ ≤ 4 * P := by
    have := mul_le_mul_of_nonneg_left hρ (by positivity : (0 : ℝ) ≤ P ^ 3)
    have e : P ^ 3 * (4 / P ^ 2) = 4 * P := by field_simp
    linarith
  have ha4 : a ^ 4 ≤ (1 / s ^ 2) ^ 2 := by
    rw [show a ^ 4 = (a ^ 2) ^ 2 by ring]; exact pow_le_pow_left₀ (sq_nonneg a) ha2 2
  have h1 : a ^ 4 * (s ^ 2) ^ 2 ≤ 1 := by
    have := mul_le_mul_of_nonneg_right ha4 (by positivity : (0 : ℝ) ≤ (s ^ 2) ^ 2)
    have e : (1 / s ^ 2) ^ 2 * (s ^ 2) ^ 2 = 1 := by field_simp
    linarith
  have h2 : (P ^ 3 * ρ + P) / (s ^ 2 * h) ≤ (4 * P + P) / (s ^ 2 * h) :=
    div_le_div_of_nonneg_right (by linarith) (by positivity)
  have h3 : 0 ≤ (P ^ 3 * ρ + P) / (s ^ 2 * h) :=
    div_nonneg (add_nonneg (mul_nonneg (by positivity) hρ0) (by linarith)) (by positivity)
  have h4 := mul_le_mul h1 h2 h3 (by norm_num)
  have hCC := mul_nonneg hC₁ hC₂
  calc a * X ≤ a * (1 / s * (C₁ * (a ^ 3 / (s * h)) * ((s ^ 2) ^ 2 * C₂ * (P ^ 3 * ρ + P)))) := by
        refine mul_le_mul_of_nonneg_left (le_trans hX ?_) ha
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hinner hA) (by positivity)
    _ = C₁ * C₂ * (a ^ 4 * (s ^ 2) ^ 2 * ((P ^ 3 * ρ + P) / (s ^ 2 * h))) := by
        field_simp
    _ ≤ C₁ * C₂ * (1 * ((4 * P + P) / (s ^ 2 * h))) := mul_le_mul_of_nonneg_left h4 hCC
    _ = 5 * C₁ * C₂ * (P / (s ^ 2 * h)) := by ring

/-- **TB.W1fib** (first-order endpoint integration by parts on the edge fibres). Given (CL1) and
(C2): for each configuration, the edge sum, the main term and the first-order terms (`wScore`,
`wSec`, `wMask` with `∂_ij b_± = dbP, dbM`; no mask term for `f = u`) satisfy
`|a·wEdge + a²·wMain - a(wScore + wSec + wMask)| ≤ C B₀`. Proof: TB.W1fib-alg, TB.W1fib-edge,
TB.W1fib-avg and `w1_fib_par`. -/
theorem weak_fibre_of {K Kb c Kδ : ℝ} (hK : 0 ≤ K) (hKb : 0 ≤ Kb) (hc : 0 < c) (hKδ : 0 ≤ Kδ)
    (hCL : CL1Shape.{u} K Kb c) (hC2 : C2RowShape.{u} Kδ) :
    ∃ C : ℝ, 0 < C ∧ Eventually fun _c₀ _κ₀ d p h => ∀ ct : Contact.{u} d p,
      |aOf d p * wEdge ct ct.OmP (ct.XP h) (ct.XP h) (fun _ => ct.uvec) +
          aOf d p ^ 2 * wMain ct ct.OmP (ct.XP h) (ct.XP h) (fun _ => ct.uvec) -
          aOf d p * (wScore ct ct.OmP ct.dOmP (ct.XP h) (ct.XP h) (fun _ => ct.uvec) +
            wSec ct 1 ct.OmP (ct.XP h) (ct.XP h) (fun _ => ct.uvec) + 0)| ≤ C * B0P d p h ∧
      |aOf d p * wEdge ct ct.OmP (ct.XP h) (ct.XP h) (ct.bP h) +
          aOf d p ^ 2 * wMain ct ct.OmP (ct.XP h) (ct.XP h) (ct.bP h) -
          aOf d p * (wScore ct ct.OmP ct.dOmP (ct.XP h) (ct.XP h) (ct.bP h) +
            wSec ct 1 ct.OmP (ct.XP h) (ct.XP h) (ct.bP h) +
            wMask ct ct.OmP (ct.XP h) (ct.XP h) (dbP ct h))| ≤ C * B0P d p h ∧
      |aOf d p * wEdge ct ct.OmM (ct.XM h) (ct.XP h) (fun _ => ct.uvec) +
          aOf d p ^ 2 * wMain ct ct.OmM (ct.XM h) (ct.XP h) (fun _ => ct.uvec) -
          aOf d p * (wScore ct ct.OmM ct.dOmM (ct.XM h) (ct.XP h) (fun _ => ct.uvec) +
            wSec ct (-1) ct.OmM (ct.XM h) (ct.XP h) (fun _ => ct.uvec) + 0)| ≤ C * B0P d p h ∧
      |aOf d p * wEdge ct ct.OmM (ct.XM h) (ct.XP h) (ct.bM h) +
          aOf d p ^ 2 * wMain ct ct.OmM (ct.XM h) (ct.XP h) (ct.bM h) -
          aOf d p * (wScore ct ct.OmM ct.dOmM (ct.XM h) (ct.XP h) (ct.bM h) +
            wSec ct (-1) ct.OmM (ct.XM h) (ct.XP h) (ct.bM h) +
            wMask ct ct.OmM (ct.XM h) (ct.XP h) (dbM ct h))| ≤ C * B0P d p h := by
  obtain ⟨C₁, hC₁, M, hE⟩ := weak_fibre_edge.{u}
  obtain ⟨C₂, hC₂, hA⟩ := weak_fibre_avg hKδ hC2 M
  refine ⟨5 * C₁ * C₂ + 1, by positivity, ((hE.and hA).and eventually_h_facts).mono ?_⟩
  rintro c₀ κ₀ d p h ⟨⟨hE', hA'⟩, hR, h0, -⟩ ct
  have hd0 : (0 : ℝ) < d := by have := hR.ten_pow_six_le_d; linarith
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.2 hd0
  have hds : (d : ℝ) = Real.sqrt d ^ 2 := (Real.sq_sqrt hd0.le).symm
  have ha0 : 0 < aOf d p := hR.aOf_pos
  have ha2 : aOf d p ^ 2 ≤ 1 / Real.sqrt d ^ 2 := by rw [← hds]; exact hR.pf_a_sq_le
  have hP1 : (1 : ℝ) ≤ p := by exact_mod_cast le_trans (by norm_num) hR.hp
  have hρ := dbar_add_le hR
  have hρ0 : 0 ≤ dbar d p + 1 / d := by
    have := le_trans (regime_eps_nonneg hR) (le_dbar hR).1
    positivity
  obtain ⟨hY, hZ⟩ := hA' ct
  have hN : (ct.N.card : ℝ) ≤ Real.sqrt d ^ 2 := hds ▸ w1_card_N ct
  have hB : (p : ℝ) / (Real.sqrt d ^ 2 * h) ≤ B0P d p h := by
    rw [← hds]
    unfold B0P vth
    have h1 : (0 : ℝ) ≤ 1 / (d * h * Real.sqrt h) := by positivity
    have h2 : (0 : ℝ) ≤ 1 / (d : ℝ) ^ 10 := by positivity
    linarith
  have key : ∀ rem : ct.V → ct.V → ℝ,
      (∀ i ∈ ct.N, ∀ j ∈ nbhd ct.G ct.S i, |rem i j| ≤ fibB ct C₁ M h i j) →
      |aOf d p * ∑ i ∈ ct.N, ∑ j ∈ nbhd ct.G ct.S i, ct.uvec i * rem i j| ≤
        (5 * C₁ * C₂ + 1) * B0P d p h := by
    intro rem hrem
    set E1 : ct.V → ct.V → ℝ := fun i j =>
      ct.E (fun σ => ct.Dstar σ ^ M * fibR ct σ i j ^ 2) with hE1
    set E0 : ℝ := ct.E (fun σ => ct.Dstar σ ^ M) with hE0
    have hfib : ∀ i j, fibB ct C₁ M h i j =
        C₁ * (aOf d p ^ 3 / (Real.sqrt d * h)) * ((p : ℝ) ^ 3 * E1 i j + p * E0) := by
      intro i j
      unfold fibB
      congr 1
      simp only [hE1, hE0]
      unfold Contact.E
      rw [← lawE_const_mul ct.G, ← lawE_const_mul ct.G, ← lawE_add ct.G]
      exact lawE_congr ct.G fun σ _ => by ring
    have hX : |∑ i ∈ ct.N, ∑ j ∈ nbhd ct.G ct.S i, ct.uvec i * rem i j| ≤
        1 / Real.sqrt d * (C₁ * (aOf d p ^ 3 / (Real.sqrt d * h)) *
          ((p : ℝ) ^ 3 * (∑ i ∈ ct.N, ∑ j ∈ nbhd ct.G ct.S i, E1 i j) +
            p * ∑ i ∈ ct.N, ∑ j ∈ nbhd ct.G ct.S i, E0)) := by
      have hc : 0 ≤ C₁ * (aOf d p ^ 3 / (Real.sqrt d * h)) := by positivity
      calc |∑ i ∈ ct.N, ∑ j ∈ nbhd ct.G ct.S i, ct.uvec i * rem i j|
          ≤ ∑ i ∈ ct.N, ∑ j ∈ nbhd ct.G ct.S i, 1 / Real.sqrt d * fibB ct C₁ M h i j := by
            refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun i hi => ?_)
            refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun j hj => ?_)
            rw [abs_mul, w1_uvec_N ct hi, abs_of_nonneg (by positivity)]
            exact mul_le_mul_of_nonneg_left (hrem i hi j hj) (by positivity)
        _ = ∑ i ∈ ct.N, ∑ j ∈ nbhd ct.G ct.S i,
              (1 / Real.sqrt d * (C₁ * (aOf d p ^ 3 / (Real.sqrt d * h))) * (p : ℝ) ^ 3 * E1 i j +
                1 / Real.sqrt d * (C₁ * (aOf d p ^ 3 / (Real.sqrt d * h))) * p * E0) := by
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
            rw [hfib]
            ring
        _ = 1 / Real.sqrt d * (C₁ * (aOf d p ^ 3 / (Real.sqrt d * h))) * (p : ℝ) ^ 3 *
              (∑ i ∈ ct.N, ∑ j ∈ nbhd ct.G ct.S i, E1 i j) +
            1 / Real.sqrt d * (C₁ * (aOf d p ^ 3 / (Real.sqrt d * h))) * p *
              (∑ i ∈ ct.N, ∑ j ∈ nbhd ct.G ct.S i, E0) := by
            simp only [Finset.sum_add_distrib, Finset.mul_sum]
        _ = _ := by ring
    have hZ' : ∑ i ∈ ct.N, ∑ j ∈ nbhd ct.G ct.S i, E0 ≤
        (ct.N.card : ℝ) * Real.sqrt d ^ 2 * C₂ := by
      have hE00 : 0 ≤ E0 := lawE_nonneg ct.G fun σ hσ => pow_nonneg (dstar_nonneg ct hσ) M
      calc ∑ i ∈ ct.N, ∑ j ∈ nbhd ct.G ct.S i, E0
          = ∑ i ∈ ct.N, ((nbhd ct.G ct.S i).card : ℝ) * E0 := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ _i ∈ ct.N, (d : ℝ) * C₂ :=
            Finset.sum_le_sum fun i _ => mul_le_mul (w1_card_nbhd ct i) hZ hE00 (by positivity)
        _ = (ct.N.card : ℝ) * Real.sqrt d ^ 2 * C₂ := by
            rw [Finset.sum_const, nsmul_eq_mul, ← hds]; ring
    have hY' : ∑ i ∈ ct.N, ∑ j ∈ nbhd ct.G ct.S i, E1 i j ≤
        C₂ * (Real.sqrt d ^ 2) ^ 2 * (dbar d p + 1 / d) := by
      rw [← hds]; exact hY
    have hfin := w1_fib_par hs hP1 h0 ha0.le ha2 hC₁.le hC₂.le hρ0 hρ hN hY' hZ' hX
    rw [abs_mul, abs_of_pos ha0]
    have hB0 : 0 ≤ B0P d p h := le_trans (by positivity) hB
    calc aOf d p * |∑ i ∈ ct.N, ∑ j ∈ nbhd ct.G ct.S i, ct.uvec i * rem i j|
        ≤ 5 * C₁ * C₂ * ((p : ℝ) / (Real.sqrt d ^ 2 * h)) := hfin
      _ ≤ 5 * C₁ * C₂ * B0P d p h := mul_le_mul_of_nonneg_left hB (by positivity)
      _ ≤ (5 * C₁ * C₂ + 1) * B0P d p h := by nlinarith
  have e1 := weak_fibre_alg ct 1 ct.OmP ct.dOmP (ct.XP h) (ct.XP h) (fun _ => ct.uvec)
    (fun _ _ _ _ => 0)
  have e2 := weak_fibre_alg ct 1 ct.OmP ct.dOmP (ct.XP h) (ct.XP h) (ct.bP h) (dbP ct h)
  have e3 := weak_fibre_alg ct (-1) ct.OmM ct.dOmM (ct.XM h) (ct.XP h) (fun _ => ct.uvec)
    (fun _ _ _ _ => 0)
  have e4 := weak_fibre_alg ct (-1) ct.OmM ct.dOmM (ct.XM h) (ct.XP h) (ct.bM h) (dbM ct h)
  rw [wMask_zero] at e1 e3
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e1]; exact key _ fun i hi j hj => (hE' ct i hi j hj).1
  · rw [e2]; exact key _ fun i hi j hj => (hE' ct i hi j hj).2.1
  · rw [e3]; exact key _ fun i hi j hj => (hE' ct i hi j hj).2.2.1
  · rw [e4]; exact key _ fun i hi j hj => (hE' ct i hi j hj).2.2.2

end BiluLinial.Tight.SecB
