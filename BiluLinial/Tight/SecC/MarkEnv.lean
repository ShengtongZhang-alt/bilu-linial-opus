/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecC.F1
public import BiluLinial.Tight.SecC.ShiftMat
public import BiluLinial.Tight.SecC.RootMoments
public import BiluLinial.Tight.Tools.MatrixFacts

/-!
# Marked envelopes (node MARKENV of `docs/tight/BP_SECC.md`)

AUDIT-C §4.2 (MARKENV), source lines 1129–1148 (proof of CR1).

**Statement.** At a capped point, if `a² S_τ + E tr A_τ² ≤ λ` and `ϑ ≤ λ`, then
`S_τ/d ≤ C λ` and `d^{-2} E[(G^τ_vv)² ‖G^τ[N,N]‖_F²] ≤ C λ`, for both branches
(`A₊ = A`, `A₋ = B`), with `C` absolute. The contact hypothesis of the source's CR1 is not used
(gap G4); the floor `λ ≥ ϑ` is needed by the interpolation.

**Sketch.** `S_τ/d = a² S_τ/(a² d) ≤ 4 λ` (`d a² ≥ 1/4`). The Frobenius bound (`frob_branch`)
gives `d^{-2} E[(G_vv)² ‖G[N,N]‖_F²] ≤ (a⁴d²)⁻¹ (2 E[t² tr A²] + 2 E[R²])`, `R = a² Σ_N G_vj²`,
`a⁴ d² ≥ 1/16`. On the support (F1, `root_diag_le`): `A_ii = a²α(G_vvG_ii - G_vi²) ≤ a² s G_ii`
and `G_vi² ≤ G_vvG_ii`, so with `κ = a²s²` and `U = Σ_N h_j`: `tr A² ≤ (tr A)² ≤ (κU)²` and
`R ≤ κ h_v U` (`root_bounds_cap`), where `κ|N| ≤ 1.01`. T.IL with the floor
(`lawE_mul_le_vth`, `k = ⌈30 log d⌉`, `m = λ`): for `X = tr A²`, `Y = t²`:
`E X² ≤ 17 ≤ d²`, `E Y^{2k} = E t^{4k} ≤ 25^{2k}` (F2, `rootT_moment_le`); for `X = Y = R`:
`E R² ≤ 33 ≤ d²`, `E R^{2k} ≤ 2(4.04)^{2k} ≤ 9^{2k}` (`hN_mul_sum_moment_le`). Moments of order
`≤ 4k ≤ p/2` (`eventually_kIL`). Hence `a⁴ E[G_vv² ‖G[N,N]‖_F²] ≤ (2·25 + 2·9) e² λ` and
`C = 16 · 68 e² ≤ 1100 e²`.

**Checks.** `N = ∅`: all quantities vanish. Zero source at `v`: `G_vv = 0`, `x = 0`, `A = 0`.
-/

@[expose] public section

namespace BiluLinial.Tight

namespace SecC

universe u

/-- **MARKENV, row half** (exact): `a² S_τ + E tr A_τ² ≤ λ` gives `S_τ/d ≤ 4λ`
(`tr A² ≥ 0`, `S_τ ≥ 0`, `4 d a² ≥ 1`). -/
theorem mark_envelope_row {d p : ℕ} (hR : TRegime d p) {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (yp ym : V → ℝ) (v : V) (l : ℝ) :
    (aOf d p ^ 2 * incRowE G d p yp ym S v 1 yp + trSqE G d p yp ym S v 1 yp ≤ l →
      incRowE G d p yp ym S v 1 yp / d ≤ 4 * l) ∧
    (aOf d p ^ 2 * incRowE G d p yp ym S v (-1) ym + trSqE G d p yp ym S v (-1) ym ≤ l →
      incRowE G d p yp ym S v (-1) ym / d ≤ 4 * l) := by
  have hd0 : (0 : ℝ) < d := lt_of_lt_of_le (by norm_num) hR.ten_pow_six_le_d
  obtain ⟨ha1, -⟩ := TRegime.d_aOf_sq hR
  have key : ∀ (τ : ℝ) (y : V → ℝ),
      aOf d p ^ 2 * incRowE G d p yp ym S v τ y + trSqE G d p yp ym S v τ y ≤ l →
        incRowE G d p yp ym S v τ y / d ≤ 4 * l := by
    intro τ y h
    have htr : 0 ≤ trSqE G d p yp ym S v τ y :=
      lawE_nonneg G fun σ _ => trace_rootMat_sq_nonneg G _ τ y σ S v
    have hS : 0 ≤ incRowE G d p yp ym S v τ y :=
      Finset.sum_nonneg fun j _ => lawE_nonneg G fun σ _ => sq_nonneg _
    rw [div_le_iff₀ hd0]
    have := mul_le_mul_of_nonneg_left ha1 hS
    nlinarith
  exact ⟨key 1 yp, key (-1) ym⟩

section Frob

open Matrix

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Root facts on the support of one branch (F1): `A_ii = a²α(G_vvG_ii - G_vi²)`, hence
`A_ii ≤ a² s G_ii` (`α G_vv = y_v/D_v ≤ s`) and `G_vi² ≤ G_vv G_ii` (`A_ii ≥ 0`). -/
theorem root_diag_le {a τ s : ℝ} (ha : 0 < a) (hτ : τ = 1 ∨ τ = -1) {y : V → ℝ}
    (hy : InCube s y) {S : Finset V} {v : V} (hv : v ∈ S) {σ : Config V}
    (hP : (precN G a τ y σ S).PosDef) (hPc : (precCore G a τ y σ S v).PosDef)
    (i : nbhd G S v) :
    rootMat G a τ y σ S v i i ≤ a ^ 2 * s * greenP G a τ y σ S i i ∧
      greenP G a τ y σ S v i ^ 2 ≤ greenP G a τ y σ S v v * greenP G a τ y σ S i i := by
  have hy0 : ∀ j, 0 ≤ y j := fun j => (hy j).1
  obtain ⟨hα, ht, hrow, hmark⟩ := root_branch G ha.ne' hτ hy0 hv hP hPc
  have hτ2 : τ ^ 2 = 1 := by rcases hτ with h | h <;> simp [h]
  have hA := (shift_branch G hy0 (hy v).2 one_pos hPc).1
  have hAii : 0 ≤ rootMat G a τ y σ S v i i := hA.diag_nonneg
  have hm := hmark i i
  rw [starMark, starCore, ← hrow i, mul_pow, hτ2, one_mul] at hm
  set α := starAlpha (rootMat G a τ y σ S v) (rootSigns G σ S v) with hαdef
  have ha2 : 0 < a ^ 2 := pow_pos ha 2
  have hc : 0 < a ^ 2 * α := mul_pos ha2 hα
  have h1 : greenP G a τ y σ S v v * greenP G a τ y σ S i i -
      greenP G a τ y σ S v i * greenP G a τ y σ S v i =
        rootMat G a τ y σ S v i i / (a ^ 2 * α) := by
    linarith
  refine ⟨?_, ?_⟩
  · have h2 := h1
    rw [eq_div_iff hc.ne'] at h2
    have hD1 := one_le_diagD G a hy0 S v
    have hh : 0 < hN G a τ y σ S v := hP.inv.diag_pos
    have hhi : 0 < hN G a τ y σ S i := hP.inv.diag_pos
    have hGvv := greenP_self G (a := a) (τ := τ) hy0 σ S v
    have hGii := greenP_self G (a := a) (τ := τ) hy0 σ S i
    have hGii0 : 0 ≤ greenP G a τ y σ S i i := by rw [hGii]; exact mul_nonneg (hy0 i) hhi.le
    have ht' := ht
    rw [rootT, eq_div_iff hα.ne'] at ht'
    have hhα : hN G a τ y σ S v * α ≤ 1 := by
      nlinarith [mul_nonneg (sub_nonneg.2 hD1) (mul_pos hh hα).le]
    have hαg : α * greenP G a τ y σ S v v ≤ s := by
      rw [hGvv]
      nlinarith [mul_nonneg (sub_nonneg.2 hhα) (hy0 v), (hy v).2]
    nlinarith [mul_nonneg hc.le (mul_self_nonneg (greenP G a τ y σ S v i)),
      mul_le_mul_of_nonneg_right hαg (mul_nonneg ha2.le hGii0)]
  · have h3 := div_nonneg hAii hc.le
    rw [sq]
    linarith

variable {d p : ℕ}

/-- Pointwise envelopes on the support at a capped point (`κ = a²s²`, `U = Σ_N h_j`):
`tr A² ≤ (κU)²` and `a² Σ_N G_vj² ≤ κ h_v U`. -/
theorem root_bounds_cap (hR : TRegime d p) {S : Finset V} {lam : ℝ} (hC : CapCtx G d p S lam)
    {yp ym : V → ℝ} (hyp : InCube (lam * sOf d p) yp) (hym : InCube (lam * sOf d p) ym)
    {τ : ℝ} {y : V → ℝ} (hb : IsBranch yp ym τ y) {v : V} (hv : v ∈ S) {σ : Config V}
    (hσ : wt G p (aOf d p) yp ym σ S ≠ 0) :
    (rootMat G (aOf d p) τ y σ S v * rootMat G (aOf d p) τ y σ S v).trace ≤
        (aOf d p ^ 2 * sOf d p ^ 2 * ∑ j ∈ nbhd G S v, hN G (aOf d p) τ y σ S j) ^ 2 ∧
      aOf d p ^ 2 * ∑ j ∈ nbhd G S v, greenP G (aOf d p) τ y σ S v j ^ 2 ≤
        aOf d p ^ 2 * sOf d p ^ 2 *
          (hN G (aOf d p) τ y σ S v * ∑ j ∈ nbhd G S v, hN G (aOf d p) τ y σ S j) := by
  have hp1 : 1 ≤ p := le_trans (by norm_num) hR.two_le_p
  have hy := inCube_of_cap G hR hC (hb.inCube hyp hym)
  have hy0 : ∀ j, 0 ≤ y j := fun j => (hy j).1
  obtain ⟨hP, hPc⟩ := posDef_branch G hp1 (fun i => (hyp i).1) (fun i => (hym i).1) hv hb hσ
  have ha := hR.aOf_pos
  have hs := hR.sOf_pos
  have hA := (shift_branch G hy0 (hy v).2 one_pos hPc).1
  have hpt := root_diag_le G ha hb.tau hy hv hP hPc
  have hh : ∀ j, 0 < hN G (aOf d p) τ y σ S j := fun j => hP.inv.diag_pos
  have hGjj : ∀ j, greenP G (aOf d p) τ y σ S j j ≤ sOf d p * hN G (aOf d p) τ y σ S j :=
    fun j => by
      rw [greenP_self G hy0 σ S j]
      exact mul_le_mul_of_nonneg_right (hy j).2 (hh j).le
  have hGjj0 : ∀ j, 0 ≤ greenP G (aOf d p) τ y σ S j j := fun j => by
    rw [greenP_self G hy0 σ S j]
    exact mul_nonneg (hy0 j) (hh j).le
  have htr : (rootMat G (aOf d p) τ y σ S v).trace ≤
      aOf d p ^ 2 * sOf d p ^ 2 * ∑ j ∈ nbhd G S v, hN G (aOf d p) τ y σ S j := by
    calc (rootMat G (aOf d p) τ y σ S v).trace
        = ∑ i : nbhd G S v, rootMat G (aOf d p) τ y σ S v i i := rfl
      _ ≤ ∑ i : nbhd G S v, aOf d p ^ 2 * sOf d p ^ 2 * hN G (aOf d p) τ y σ S i :=
          Finset.sum_le_sum fun i _ => by
            have h1 := (hpt i).1
            have h2 := mul_le_mul_of_nonneg_left (hGjj i)
              (mul_nonneg (sq_nonneg (aOf d p)) hs.le)
            linarith
      _ = aOf d p ^ 2 * sOf d p ^ 2 * ∑ j ∈ nbhd G S v, hN G (aOf d p) τ y σ S j := by
          rw [Finset.mul_sum]
          exact Finset.sum_coe_sort (nbhd G S v)
            (fun j => aOf d p ^ 2 * sOf d p ^ 2 * hN G (aOf d p) τ y σ S j)
  refine ⟨?_, ?_⟩
  · calc (rootMat G (aOf d p) τ y σ S v * rootMat G (aOf d p) τ y σ S v).trace
        ≤ (rootMat G (aOf d p) τ y σ S v).trace * (rootMat G (aOf d p) τ y σ S v).trace :=
          trace_mul_le_trace_mul_trace hA hA
      _ ≤ (aOf d p ^ 2 * sOf d p ^ 2 * ∑ j ∈ nbhd G S v, hN G (aOf d p) τ y σ S j) *
            (aOf d p ^ 2 * sOf d p ^ 2 * ∑ j ∈ nbhd G S v, hN G (aOf d p) τ y σ S j) :=
          mul_self_le_mul_self hA.trace_nonneg htr
      _ = _ := (sq _).symm
  · have hrow : ∑ j ∈ nbhd G S v, greenP G (aOf d p) τ y σ S v j ^ 2 ≤
        sOf d p ^ 2 * (hN G (aOf d p) τ y σ S v * ∑ j ∈ nbhd G S v, hN G (aOf d p) τ y σ S j) := by
      calc ∑ j ∈ nbhd G S v, greenP G (aOf d p) τ y σ S v j ^ 2
          = ∑ j : nbhd G S v, greenP G (aOf d p) τ y σ S v j ^ 2 :=
            (Finset.sum_coe_sort (nbhd G S v) (fun j => greenP G (aOf d p) τ y σ S v j ^ 2)).symm
        _ ≤ ∑ j : nbhd G S v,
              sOf d p ^ 2 * (hN G (aOf d p) τ y σ S v * hN G (aOf d p) τ y σ S j) :=
            Finset.sum_le_sum fun j _ => by
              have h1 := (hpt j).2
              have h2 := mul_le_mul (hGjj v) (hGjj j) (hGjj0 j) (mul_nonneg hs.le (hh v).le)
              linarith
        _ = ∑ j ∈ nbhd G S v,
              sOf d p ^ 2 * (hN G (aOf d p) τ y σ S v * hN G (aOf d p) τ y σ S j) :=
            Finset.sum_coe_sort (nbhd G S v)
              (fun j => sOf d p ^ 2 * (hN G (aOf d p) τ y σ S v * hN G (aOf d p) τ y σ S j))
        _ = _ := by rw [Finset.mul_sum, Finset.mul_sum]
    calc aOf d p ^ 2 * ∑ j ∈ nbhd G S v, greenP G (aOf d p) τ y σ S v j ^ 2
        ≤ aOf d p ^ 2 * (sOf d p ^ 2 *
            (hN G (aOf d p) τ y σ S v * ∑ j ∈ nbhd G S v, hN G (aOf d p) τ y σ S j)) :=
          mul_le_mul_of_nonneg_left hrow (sq_nonneg _)
      _ = _ := by ring

/-- **MARKENV, Frobenius half, one branch**: `a² S_τ + E tr A_τ² ≤ λ` and `ϑ ≤ λ` give
`d^{-2} E[(G^τ_vv)² ‖G^τ[N,N]‖_F²] ≤ 1100 e² λ` (see the module docstring). -/
theorem markE_branch_le (hR : TRegime d p) (hk : 8 * kIL d ≤ p) {S : Finset V} {lam : ℝ}
    (hC : CapCtx G d p S lam) {yp ym : V → ℝ} (hyp : InCube (lam * sOf d p) yp)
    (hym : InCube (lam * sOf d p) ym) {τ : ℝ} {y : V → ℝ} (hb : IsBranch yp ym τ y) {v : V}
    (hv : v ∈ S) {l : ℝ} (hl : vth d ≤ l)
    (hS : aOf d p ^ 2 * incRowE G d p yp ym S v τ y + trSqE G d p yp ym S v τ y ≤ l) :
    markE G d p yp ym S v τ y / (d : ℝ) ^ 2 ≤ 1100 * Real.exp 2 * l := by
  have hd3 : 3 ≤ d := le_trans (by norm_num) hR.ten_pow_six_le_nat
  have hp6 := hR.hp
  have hk1 := one_le_kIL hd3
  have hp1 : 1 ≤ p := le_trans (by norm_num) hR.two_le_p
  have hdR := hR.ten_pow_six_le_d
  have hd0 : (0 : ℝ) < d := lt_of_lt_of_le (by norm_num) hdR
  have hZ := Zw_pos_cap G hR hC hyp hym
  have ha := hR.aOf_pos
  have hs := hR.sOf_pos
  obtain ⟨hda1, -⟩ := TRegime.d_aOf_sq hR
  have hκd := hR.d_mul_kappa_le
  have hθ : 0 < vth d := by unfold vth; positivity
  have hl0 : 0 ≤ l := hθ.le.trans hl
  have hNS : nbhd G S v ⊆ S := Finset.filter_subset _ _
  have hcard : ((nbhd G S v).card : ℝ) ≤ d := by
    have h := card_nbhd_le G hC.deg S v
    rw [Fintype.card_coe] at h
    exact_mod_cast h
  have hκ0 : 0 ≤ aOf d p ^ 2 * sOf d p ^ 2 := by positivity
  have hκc0 : 0 ≤ aOf d p ^ 2 * sOf d p ^ 2 * (nbhd G S v).card := by positivity
  have hκc : aOf d p ^ 2 * sOf d p ^ 2 * (nbhd G S v).card ≤ 101 / 100 := by
    have := mul_le_mul_of_nonneg_left hcard hκ0
    linarith
  have hy := inCube_of_cap G hR hC (hb.inCube hyp hym)
  have hy0 : ∀ j, 0 ≤ y j := fun j => (hy j).1
  have hdd : (d : ℝ) ≤ (d : ℝ) ^ 30 := le_self_pow₀ (by linarith) (by norm_num)
  -- the two energies
  have hSnn : 0 ≤ aOf d p ^ 2 * incRowE G d p yp ym S v τ y :=
    mul_nonneg (sq_nonneg _)
      (Finset.sum_nonneg fun j _ => lawE_nonneg G fun σ _ => sq_nonneg _)
  have hTnn : 0 ≤ trSqE G d p yp ym S v τ y :=
    lawE_nonneg G fun σ _ => trace_rootMat_sq_nonneg G _ τ y σ S v
  have hRE : lawE G p (aOf d p) yp ym S
      (fun σ => aOf d p ^ 2 * ∑ j ∈ nbhd G S v, greenP G (aOf d p) τ y σ S v j ^ 2) =
      aOf d p ^ 2 * incRowE G d p yp ym S v τ y := by
    rw [lawE_const_mul, lawE_sum]
    rfl
  -- (i) `E[tr A² t²] ≤ 25 e² λ`
  have hX1sq : lawE G p (aOf d p) yp ym S (fun σ =>
      (rootMat G (aOf d p) τ y σ S v * rootMat G (aOf d p) τ y σ S v).trace ^ 2) ≤ (d : ℝ) ^ 2 := by
    calc _ ≤ lawE G p (aOf d p) yp ym S (fun σ => (aOf d p ^ 2 * sOf d p ^ 2) ^ 4 *
            (∑ j ∈ nbhd G S v, hN G (aOf d p) τ y σ S j) ^ 4) :=
          lawE_mono G fun σ hσ => by
            have h := (root_bounds_cap G hR hC hyp hym hb hv hσ).1
            have h0 := trace_rootMat_sq_nonneg G (aOf d p) τ y σ S v
            calc (rootMat G (aOf d p) τ y σ S v * rootMat G (aOf d p) τ y σ S v).trace ^ 2
                ≤ ((aOf d p ^ 2 * sOf d p ^ 2 *
                    ∑ j ∈ nbhd G S v, hN G (aOf d p) τ y σ S j) ^ 2) ^ 2 :=
                  pow_le_pow_left₀ h0 h 2
              _ = _ := by ring
      _ = (aOf d p ^ 2 * sOf d p ^ 2) ^ 4 * lawE G p (aOf d p) yp ym S
            (fun σ => (∑ j ∈ nbhd G S v, hN G (aOf d p) τ y σ S j) ^ 4) := lawE_const_mul G _ _
      _ ≤ (aOf d p ^ 2 * sOf d p ^ 2) ^ 4 * (((nbhd G S v).card : ℝ) ^ 4 * 2 ^ 4) :=
          mul_le_mul_of_nonneg_left
            (hN_sum_moment_le G hR hC hyp hym hb hNS (n := 4) (by omega)) (by positivity)
      _ = (aOf d p ^ 2 * sOf d p ^ 2 * (nbhd G S v).card) ^ 4 * 16 := by ring
      _ ≤ (101 / 100) ^ 4 * 16 := by gcongr
      _ ≤ (d : ℝ) ^ 2 := by nlinarith
  have hY1 : lawE G p (aOf d p) yp ym S (fun σ =>
      (rootT G (aOf d p) τ y σ S v ^ 2) ^ (2 * kIL d)) ≤ 25 ^ (2 * kIL d) := by
    simp only [← pow_mul]
    calc _ ≤ (5 : ℝ) ^ (2 * (2 * kIL d)) :=
          rootT_moment_le G hR hC hyp hym hb hv (by omega)
      _ = 25 ^ (2 * kIL d) := by rw [pow_mul]; norm_num
  have hI1 : lawE G p (aOf d p) yp ym S (fun σ =>
      (rootMat G (aOf d p) τ y σ S v * rootMat G (aOf d p) τ y σ S v).trace *
        rootT G (aOf d p) τ y σ S v ^ 2) ≤ Real.exp 2 * 25 * l := lawE_mul_le_vth G hd3 hZ
    (X := fun σ => (rootMat G (aOf d p) τ y σ S v * rootMat G (aOf d p) τ y σ S v).trace)
    (Y := fun σ => rootT G (aOf d p) τ y σ S v ^ 2)
    (fun σ _ => trace_rootMat_sq_nonneg G _ τ y σ S v) (fun σ _ => sq_nonneg _)
    hl hd0.le hdd (by norm_num) (show trSqE G d p yp ym S v τ y ≤ l by linarith) hX1sq hY1
  -- (ii) `E[R²] ≤ 9 e² λ`
  have hR2 : lawE G p (aOf d p) yp ym S (fun σ =>
      (aOf d p ^ 2 * ∑ j ∈ nbhd G S v, greenP G (aOf d p) τ y σ S v j ^ 2) ^ 2) ≤ (d : ℝ) ^ 2 := by
    calc _ ≤ lawE G p (aOf d p) yp ym S (fun σ => (aOf d p ^ 2 * sOf d p ^ 2) ^ 2 *
            (hN G (aOf d p) τ y σ S v * ∑ j ∈ nbhd G S v, hN G (aOf d p) τ y σ S j) ^ 2) :=
          lawE_mono G fun σ hσ => by
            have h := (root_bounds_cap G hR hC hyp hym hb hv hσ).2
            have h0 : 0 ≤ aOf d p ^ 2 * ∑ j ∈ nbhd G S v, greenP G (aOf d p) τ y σ S v j ^ 2 :=
              mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun j _ => sq_nonneg _)
            calc (aOf d p ^ 2 * ∑ j ∈ nbhd G S v, greenP G (aOf d p) τ y σ S v j ^ 2) ^ 2
                ≤ (aOf d p ^ 2 * sOf d p ^ 2 * (hN G (aOf d p) τ y σ S v *
                    ∑ j ∈ nbhd G S v, hN G (aOf d p) τ y σ S j)) ^ 2 :=
                  pow_le_pow_left₀ h0 h 2
              _ = _ := by ring
      _ = (aOf d p ^ 2 * sOf d p ^ 2) ^ 2 * lawE G p (aOf d p) yp ym S (fun σ =>
            (hN G (aOf d p) τ y σ S v * ∑ j ∈ nbhd G S v, hN G (aOf d p) τ y σ S j) ^ 2) :=
          lawE_const_mul G _ _
      _ ≤ (aOf d p ^ 2 * sOf d p ^ 2) ^ 2 * (2 * ((nbhd G S v).card : ℝ) ^ 2 * 4 ^ 2) :=
          mul_le_mul_of_nonneg_left
            (hN_mul_sum_moment_le G hR hC hyp hym hb hv hNS (n := 2) (by omega)) (by positivity)
      _ = (aOf d p ^ 2 * sOf d p ^ 2 * (nbhd G S v).card) ^ 2 * 32 := by ring
      _ ≤ (101 / 100) ^ 2 * 32 := by gcongr
      _ ≤ (d : ℝ) ^ 2 := by nlinarith
  have hY2 : lawE G p (aOf d p) yp ym S (fun σ =>
      (aOf d p ^ 2 * ∑ j ∈ nbhd G S v, greenP G (aOf d p) τ y σ S v j ^ 2) ^ (2 * kIL d)) ≤
      9 ^ (2 * kIL d) := by
    set n := 2 * kIL d with hn
    have hn1 : n ≠ 0 := by omega
    calc _ ≤ lawE G p (aOf d p) yp ym S (fun σ => (aOf d p ^ 2 * sOf d p ^ 2) ^ n *
            (hN G (aOf d p) τ y σ S v * ∑ j ∈ nbhd G S v, hN G (aOf d p) τ y σ S j) ^ n) :=
          lawE_mono G fun σ hσ => by
            have h := (root_bounds_cap G hR hC hyp hym hb hv hσ).2
            have h0 : 0 ≤ aOf d p ^ 2 * ∑ j ∈ nbhd G S v, greenP G (aOf d p) τ y σ S v j ^ 2 :=
              mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun j _ => sq_nonneg _)
            exact (pow_le_pow_left₀ h0 h n).trans_eq (mul_pow _ _ _)
      _ = (aOf d p ^ 2 * sOf d p ^ 2) ^ n * lawE G p (aOf d p) yp ym S (fun σ =>
            (hN G (aOf d p) τ y σ S v * ∑ j ∈ nbhd G S v, hN G (aOf d p) τ y σ S j) ^ n) :=
          lawE_const_mul G _ _
      _ ≤ (aOf d p ^ 2 * sOf d p ^ 2) ^ n * (2 * ((nbhd G S v).card : ℝ) ^ n * 4 ^ n) :=
          mul_le_mul_of_nonneg_left
            (hN_mul_sum_moment_le G hR hC hyp hym hb hv hNS (by omega)) (by positivity)
      _ = 2 * (4 * (aOf d p ^ 2 * sOf d p ^ 2 * (nbhd G S v).card)) ^ n := by ring
      _ ≤ 2 ^ n * (4 * (aOf d p ^ 2 * sOf d p ^ 2 * (nbhd G S v).card)) ^ n :=
          mul_le_mul_of_nonneg_right (le_self_pow₀ (by norm_num) hn1) (by positivity)
      _ = (8 * (aOf d p ^ 2 * sOf d p ^ 2 * (nbhd G S v).card)) ^ n := by
          rw [← mul_pow]
          congr 1
          ring
      _ ≤ 9 ^ n := pow_le_pow_left₀ (by positivity) (by linarith) n
  have hI2 : lawE G p (aOf d p) yp ym S (fun σ =>
      (aOf d p ^ 2 * ∑ j ∈ nbhd G S v, greenP G (aOf d p) τ y σ S v j ^ 2) *
        (aOf d p ^ 2 * ∑ j ∈ nbhd G S v, greenP G (aOf d p) τ y σ S v j ^ 2)) ≤
      Real.exp 2 * 9 * l := lawE_mul_le_vth G hd3 hZ
    (X := fun σ => aOf d p ^ 2 * ∑ j ∈ nbhd G S v, greenP G (aOf d p) τ y σ S v j ^ 2)
    (Y := fun σ => aOf d p ^ 2 * ∑ j ∈ nbhd G S v, greenP G (aOf d p) τ y σ S v j ^ 2)
    (fun σ _ => mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun j _ => sq_nonneg _))
    (fun σ _ => mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun j _ => sq_nonneg _))
    hl hd0.le hdd (by norm_num) (by rw [hRE]; linarith) hR2 hY2
  -- (iii) the Frobenius bound under the law
  have hfrob : aOf d p ^ 4 * markE G d p yp ym S v τ y ≤
      2 * lawE G p (aOf d p) yp ym S (fun σ =>
          (rootMat G (aOf d p) τ y σ S v * rootMat G (aOf d p) τ y σ S v).trace *
            rootT G (aOf d p) τ y σ S v ^ 2) +
        2 * lawE G p (aOf d p) yp ym S (fun σ =>
          (aOf d p ^ 2 * ∑ j ∈ nbhd G S v, greenP G (aOf d p) τ y σ S v j ^ 2) *
            (aOf d p ^ 2 * ∑ j ∈ nbhd G S v, greenP G (aOf d p) τ y σ S v j ^ 2)) := by
    have e : aOf d p ^ 4 * markE G d p yp ym S v τ y = lawE G p (aOf d p) yp ym S (fun σ =>
        aOf d p ^ 4 * (greenP G (aOf d p) τ y σ S v v ^ 2 *
          ∑ i ∈ nbhd G S v, ∑ j ∈ nbhd G S v, greenP G (aOf d p) τ y σ S i j ^ 2)) :=
      (lawE_const_mul G _ _).symm
    rw [e]
    calc _ ≤ lawE G p (aOf d p) yp ym S (fun σ =>
            2 * ((rootMat G (aOf d p) τ y σ S v * rootMat G (aOf d p) τ y σ S v).trace *
              rootT G (aOf d p) τ y σ S v ^ 2) +
            2 * ((aOf d p ^ 2 * ∑ j ∈ nbhd G S v, greenP G (aOf d p) τ y σ S v j ^ 2) *
              (aOf d p ^ 2 * ∑ j ∈ nbhd G S v, greenP G (aOf d p) τ y σ S v j ^ 2))) :=
          lawE_mono G fun σ hσ => by
            obtain ⟨hP, hPc⟩ :=
              posDef_branch G hp1 (fun i => (hyp i).1) (fun i => (hym i).1) hv hb hσ
            have h := frob_branch G ha.ne' hb.tau hy0 hv hP hPc
            nlinarith [h]
      _ = _ := by rw [lawE_add, lawE_const_mul, lawE_const_mul]
  have hM0 : 0 ≤ markE G d p yp ym S v τ y :=
    lawE_nonneg G fun σ _ => mul_nonneg (sq_nonneg _)
      (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)
  have he : 0 < Real.exp 2 := Real.exp_pos 2
  have hda4 : 1 ≤ 16 * (aOf d p ^ 4 * (d : ℝ) ^ 2) := by
    have := mul_le_mul hda1 hda1 (by norm_num) (by linarith)
    nlinarith
  have hE : aOf d p ^ 4 * markE G d p yp ym S v τ y ≤ 68 * Real.exp 2 * l := by linarith
  rw [div_le_iff₀ (pow_pos hd0 2)]
  calc markE G d p yp ym S v τ y
      ≤ markE G d p yp ym S v τ y * (16 * (aOf d p ^ 4 * (d : ℝ) ^ 2)) :=
        le_mul_of_one_le_right hM0 hda4
    _ = 16 * (d : ℝ) ^ 2 * (aOf d p ^ 4 * markE G d p yp ym S v τ y) := by ring
    _ ≤ 16 * (d : ℝ) ^ 2 * (68 * Real.exp 2 * l) :=
        mul_le_mul_of_nonneg_left hE (by positivity)
    _ ≤ 1100 * Real.exp 2 * l * (d : ℝ) ^ 2 := by
        nlinarith [mul_nonneg (mul_nonneg he.le hl0) (sq_nonneg (d : ℝ))]

end Frob

/-- **MARKENV, Frobenius half** (source lines 1135–1148), `C = 1100 e²` (`markE_branch_le`). -/
theorem mark_envelope_frob : ∃ C : ℝ, 1 ≤ C ∧ Eventually fun _ _ d p _ =>
    ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
      (S : Finset V) (lam : ℝ) (yp ym : V → ℝ) (v : V), CapCtx G d p S lam →
      InCube (lam * sOf d p) yp → InCube (lam * sOf d p) ym → v ∈ S →
      ∀ l : ℝ, vth d ≤ l →
        (aOf d p ^ 2 * incRowE G d p yp ym S v 1 yp + trSqE G d p yp ym S v 1 yp ≤ l →
          markE G d p yp ym S v 1 yp / (d : ℝ) ^ 2 ≤ C * l) ∧
        (aOf d p ^ 2 * incRowE G d p yp ym S v (-1) ym + trSqE G d p yp ym S v (-1) ym ≤ l →
          markE G d p yp ym S v (-1) ym / (d : ℝ) ^ 2 ≤ C * l) := by
  refine ⟨1100 * Real.exp 2, ?_, ((eventually_regime 1).and eventually_kIL).mono ?_⟩
  · have := Real.one_le_exp (show (0 : ℝ) ≤ 2 by norm_num)
    linarith
  rintro c₀ κ₀ d p h ⟨⟨hR, -, -⟩, hk⟩ V _ _ G _ S lam yp ym v hC hyp hym hv l hl
  exact ⟨markE_branch_le G hR hk hC hyp hym (isBranch_plus yp ym) hv hl,
    markE_branch_le G hR hk hC hyp hym (isBranch_minus yp ym) hv hl⟩

/-- **MARKENV** (from the row and Frobenius halves, `C = max(4, C_F)`). -/
theorem mark_envelope : ∃ C : ℝ, 1 ≤ C ∧ Eventually fun _ _ d p _ =>
    ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
      (S : Finset V) (lam : ℝ) (yp ym : V → ℝ) (v : V), CapCtx G d p S lam →
      InCube (lam * sOf d p) yp → InCube (lam * sOf d p) ym → v ∈ S →
      ∀ l : ℝ, vth d ≤ l →
        (aOf d p ^ 2 * incRowE G d p yp ym S v 1 yp + trSqE G d p yp ym S v 1 yp ≤ l →
          incRowE G d p yp ym S v 1 yp / d ≤ C * l ∧
            markE G d p yp ym S v 1 yp / (d : ℝ) ^ 2 ≤ C * l) ∧
        (aOf d p ^ 2 * incRowE G d p yp ym S v (-1) ym + trSqE G d p yp ym S v (-1) ym ≤ l →
          incRowE G d p yp ym S v (-1) ym / d ≤ C * l ∧
            markE G d p yp ym S v (-1) ym / (d : ℝ) ^ 2 ≤ C * l) := by
  obtain ⟨CF, hCF, hF⟩ := mark_envelope_frob.{u}
  refine ⟨max 4 CF, le_trans (by norm_num) (le_max_left _ _),
    (hF.and (eventually_regime 1)).mono ?_⟩
  rintro c₀ κ₀ d p h ⟨H, hR, -, -⟩ V _ _ G _ S lam yp ym v hC hyp hym hv l hl
  have hl0 : 0 ≤ l := le_trans (by unfold vth; positivity) hl
  have h4 : 4 * l ≤ max 4 CF * l := mul_le_mul_of_nonneg_right (le_max_left _ _) hl0
  have hCF : CF * l ≤ max 4 CF * l := mul_le_mul_of_nonneg_right (le_max_right _ _) hl0
  obtain ⟨hr1, hr2⟩ := mark_envelope_row hR G S yp ym v l
  obtain ⟨hf1, hf2⟩ := H V G S lam yp ym v hC hyp hym hv l hl
  exact ⟨fun h => ⟨(hr1 h).trans h4, (hf1 h).trans hCF⟩,
    fun h => ⟨(hr2 h).trans h4, (hf2 h).trans hCF⟩⟩

end SecC

end BiluLinial.Tight
