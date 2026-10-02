/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecC.RowG12Aux

/-!
# Helpers for CR-G1, CR-G2: the weighted row energies under the law

Nodes CR-G1, CR-G2 of `docs/tight/BP_SECC.md`. Notation at a signing `σ`: `r_i` (`g12r`), the
row energies `X^τ_i = a⁴ Σ_j ((G^τ_vj)² + e^τ_ij²)` in star form (`g12Xb`), the unmarked weight
`W = rowWt = a² Σ_i (1 + r_i)⁴`, `R_τ = a² Σ_N (G^τ_vj)²`.

* Pointwise at a supported signing (F1): `X^τ_i ≤ W²` (`g12Xb_le_W`), `R_τ ≤ W` (`g12_R_le_W`),
  and `Σ_i X^τ_i ≤ R_τ/2 + 2 a⁴ G_vv² ‖G[N,N]‖_F² + 2 R_τ W` (`g12_sumXb_pt`; `e = c - x xᵀ`
  with the full marks `c_ij = G_vv G_ij`, `|N| a² ≤ 1/2`).
* `E[R_τ W] ≤ e² B λ` (`g12_rowWt_mul_R_le`, T.IL as in `rowWt_mul_R_le`, both branches), hence
  `E Σ_i X^τ_i ≤ (1 + 2e²B) λ` when `S_τ/d ≤ λ`, `markE_τ/d² ≤ λ`, `ϑ ≤ λ` (`g12_sumXb_le`).
* Per-row interpolation (`g12_sum_interp`): for weights `Y_i ≥ 0` with `‖Y_i‖_{2k} ≤ B_Y`,
  `E Σ_i Y_i X_i ≤ e² B_Y (E Σ_i X_i + ϑ)` (T.IL for each `i` applied to `d X_i` with the
  floor `ϑ`, second moments from `X_i ≤ W²`, `E W⁴ ≤ B⁴`).
* Weight moments: `(1 + r_i)⁴`, `(1 + r_i)⁶`, `W (1 + r_i)⁴` (`g12_Y4_moment`, `g12_Y6_moment`,
  `g12_YT_moment`), from `r_i ≤ ρ_i` (`starScale_le_rho`) and F2.
* `g12_EU_le`: `E[U⁺ + √U⁺ √U⁻] ≤ 2 e² B_Y K √(λ_c δ_c)` for `U^± = Σ_i Y_i X^±_i`.
-/

@[expose] public section

namespace BiluLinial.Tight

namespace SecC

open Matrix

section Law

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable {d p : ℕ}

/-- The unmarked scale `r_i` at a signing. -/
noncomputable def g12r (d p : ℕ) (yp ym : V → ℝ) (σ : Config V) (S : Finset V) (v : V)
    (i : nbhd G S v) : ℝ :=
  starScale (aOf d p) (rootMat G (aOf d p) 1 yp σ S v) (rootMat G (aOf d p) (-1) ym σ S v)
    (rootSigns G σ S v) i

/-- The row energy `X^τ_i = a⁴ Σ_j ((G^τ_vj)² + e^τ_ij²)` at a signing, in star form. -/
noncomputable def g12Xb (d p : ℕ) (τ : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) (v : V)
    (i : nbhd G S v) : ℝ :=
  aOf d p ^ 4 * ∑ j : nbhd G S v,
    (starRow (τ * aOf d p) (rootMat G (aOf d p) τ y σ S v) (rootSigns G σ S v) j ^ 2 +
      starCore (τ * aOf d p) (rootMat G (aOf d p) τ y σ S v) (rootSigns G σ S v) i j ^ 2)

theorem g12Xb_nonneg (d p : ℕ) (τ : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) (v : V)
    (i : nbhd G S v) : 0 ≤ g12Xb G d p τ y σ S v i := by
  unfold g12Xb
  positivity

theorem g12r_nonneg (d p : ℕ) (yp ym : V → ℝ) (σ : Config V) (S : Finset V) (v : V)
    (i : nbhd G S v) : 0 ≤ g12r G d p yp ym σ S v i :=
  starScale_nonneg i

theorem g12P_eq (d p : ℕ) (yp : V → ℝ) (σ : Config V) (S : Finset V) (v : V)
    (i : nbhd G S v) :
    g12P (aOf d p) (rootMat G (aOf d p) 1 yp σ S v) (rootSigns G σ S v) i =
      g12Xb G d p 1 yp σ S v i := by
  unfold g12P g12Xb
  simp only [one_mul]

theorem g12M_eq (d p : ℕ) (ym : V → ℝ) (σ : Config V) (S : Finset V) (v : V)
    (i : nbhd G S v) :
    g12M (aOf d p) (rootMat G (aOf d p) (-1) ym σ S v) (rootSigns G σ S v) i =
      g12Xb G d p (-1) ym σ S v i := by
  unfold g12M g12Xb
  simp only [neg_one_mul, starCore_neg]

theorem rowWt_eq_g12r (d p : ℕ) (yp ym : V → ℝ) (σ : Config V) (S : Finset V) (v : V) :
    rowWt G d p yp ym σ S v = aOf d p ^ 2 * ∑ i, (1 + g12r G d p yp ym σ S v i) ^ 4 := rfl

theorem rowWt_nonneg' (d p : ℕ) (yp ym : V → ℝ) (σ : Config V) (S : Finset V) (v : V) :
    0 ≤ rowWt G d p yp ym σ S v := by
  rw [rowWt_eq_g12r]
  have := fun i => g12r_nonneg G d p yp ym σ S v i
  positivity

/-- `|E f| ≤ E |f|`. -/
theorem g12_abs_lawE_le {p : ℕ} {a : ℝ} {yp ym : V → ℝ} {S : Finset V} (f : Config V → ℝ) :
    |lawE G p a yp ym S f| ≤ lawE G p a yp ym S (fun σ => |f σ|) := by
  rw [abs_le]
  constructor
  · have h := lawE_mono G (p := p) (a := a) (yp := yp) (ym := ym) (S := S)
      (f := fun σ => (-1) * |f σ|) (g := f) fun σ _ => by have := neg_abs_le (f σ); linarith
    rw [lawE_const_mul] at h
    linarith
  · exact lawE_mono G fun σ _ => le_abs_self (f σ)

/-- Cauchy–Schwarz in the law: `E[√U √W] ≤ √(E U) √(E W)` for `U, W ≥ 0`. -/
theorem g12_lawE_sqrt_mul_le {p : ℕ} {a : ℝ} {yp ym : V → ℝ} {S : Finset V}
    (U W : Config V → ℝ) (hU : ∀ σ, 0 ≤ U σ) (hW : ∀ σ, 0 ≤ W σ) :
    lawE G p a yp ym S (fun σ => Real.sqrt (U σ) * Real.sqrt (W σ)) ≤
      Real.sqrt (lawE G p a yp ym S U) * Real.sqrt (lawE G p a yp ym S W) := by
  have h : lawE G p a yp ym S (fun σ => Real.sqrt (U σ) * Real.sqrt (W σ)) ^ 2 ≤
      lawE G p a yp ym S (fun σ => Real.sqrt (U σ) ^ 2) *
        lawE G p a yp ym S (fun σ => Real.sqrt (W σ) ^ 2) :=
    wavg_mul_sq_le (fun σ => wt_nonneg G σ) _ _
  have e1 : (fun σ => Real.sqrt (U σ) ^ 2) = U := funext fun σ => Real.sq_sqrt (hU σ)
  have e2 : (fun σ => Real.sqrt (W σ) ^ 2) = W := funext fun σ => Real.sq_sqrt (hW σ)
  rw [e1, e2] at h
  rw [← Real.sqrt_mul (lawE_nonneg G fun σ _ => hU σ)]
  exact (le_abs_self _).trans (Real.abs_le_sqrt h)

/-- Facts at a supported signing: `A, B ⪰ 0`, `α, β > 0`. -/
theorem g12_supp (hR : TRegime d p) {S : Finset V} {yp ym : V → ℝ} (hyp : ∀ i, 0 ≤ yp i)
    (hym : ∀ i, 0 ≤ ym i) {v : V} (hv : v ∈ S) {σ : Config V}
    (hσ : wt G p (aOf d p) yp ym σ S ≠ 0) :
    (rootMat G (aOf d p) 1 yp σ S v).PosSemidef ∧
      (rootMat G (aOf d p) (-1) ym σ S v).PosSemidef ∧
      0 < starAlpha (rootMat G (aOf d p) 1 yp σ S v) (rootSigns G σ S v) ∧
      0 < starAlpha (rootMat G (aOf d p) (-1) ym σ S v) (rootSigns G σ S v) := by
  have hp1 : 1 ≤ p := le_trans (by norm_num) hR.two_le_p
  obtain ⟨-, -, hc1, hc2⟩ := posDef_of_wt_ne_zero' G hp1 hyp hym hv hσ
  obtain ⟨hα, hβ, -⟩ := root_F1 G hR hyp hym hv hσ
  exact ⟨(shift_branch G hyp le_rfl one_pos hc1).1, (shift_branch G hym le_rfl one_pos hc2).1,
    hα, hβ⟩

/-- `X^τ_i ≤ W²` at a supported signing. -/
theorem g12Xb_le_W (hR : TRegime d p) {S : Finset V} {yp ym : V → ℝ} (hyp : ∀ i, 0 ≤ yp i)
    (hym : ∀ i, 0 ≤ ym i) {v : V} (hv : v ∈ S) {τ : ℝ} {y : V → ℝ} (hb : IsBranch yp ym τ y)
    {σ : Config V} (hσ : wt G p (aOf d p) yp ym σ S ≠ 0) (i : nbhd G S v) :
    g12Xb G d p τ y σ S v i ≤ rowWt G d p yp ym σ S v ^ 2 := by
  obtain ⟨hA, hB, hα, hβ⟩ := g12_supp G hR hyp hym hv hσ
  rcases hb with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2, ← g12P_eq]
    exact g12P_le_W (B := rootMat G (aOf d p) (-1) ym σ S v) hA hα i
  · rw [h1, h2, ← g12M_eq]
    exact g12M_le_W (A := rootMat G (aOf d p) 1 yp σ S v) hB hβ i

/-- `R_τ ≤ W` at a supported signing (`|G^τ_vj| ≤ r_j`). -/
theorem g12_R_le_W (hR : TRegime d p) {S : Finset V} {yp ym : V → ℝ} (hyp : ∀ i, 0 ≤ yp i)
    (hym : ∀ i, 0 ≤ ym i) {v : V} (hv : v ∈ S) {τ : ℝ} {y : V → ℝ} (hb : IsBranch yp ym τ y)
    {σ : Config V} (hσ : wt G p (aOf d p) yp ym σ S ≠ 0) :
    aOf d p ^ 2 * ∑ j ∈ nbhd G S v, greenP G (aOf d p) τ y σ S v j ^ 2 ≤
      rowWt G d p yp ym σ S v := by
  obtain ⟨-, -, -, -, hrp, hrm, -, -⟩ := root_F1 G hR hyp hym hv hσ
  rw [rowWt_eq_g12r]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
  rw [← Finset.sum_coe_sort (nbhd G S v)]
  refine Finset.sum_le_sum fun j _ => ?_
  have hr := g12r_nonneg G d p yp ym σ S v j
  have hx : greenP G (aOf d p) τ y σ S v j ^ 2 ≤ g12r G d p yp ym σ S v j ^ 2 := by
    unfold g12r
    rcases hb with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2, hrp j]
      exact g12_sq_le_of_abs_le (abs_starRow_le j)
    · rw [h1, h2, hrm j]
      exact g12_sq_le_of_abs_le (abs_starRow_neg_le j)
  exact hx.trans (g12_sq_le_pow4 hr)

/-- Pointwise: `Σ_i X^τ_i ≤ R_τ/2 + 2 a⁴ G_vv² ‖G[N,N]‖_F² + 2 R_τ W`. -/
theorem g12_sumXb_pt (hR : TRegime d p) {S : Finset V} {lam : ℝ} (hC : CapCtx G d p S lam)
    {yp ym : V → ℝ} (hyp : ∀ i, 0 ≤ yp i) (hym : ∀ i, 0 ≤ ym i) {τ : ℝ} {y : V → ℝ}
    (hb : IsBranch yp ym τ y) {v : V} (hv : v ∈ S) {σ : Config V}
    (hσ : wt G p (aOf d p) yp ym σ S ≠ 0) :
    ∑ i, g12Xb G d p τ y σ S v i ≤
      1 / 2 * (aOf d p ^ 2 * ∑ j ∈ nbhd G S v, greenP G (aOf d p) τ y σ S v j ^ 2) +
        2 * (aOf d p ^ 4 * (greenP G (aOf d p) τ y σ S v v ^ 2 *
          ∑ i ∈ nbhd G S v, ∑ j ∈ nbhd G S v, greenP G (aOf d p) τ y σ S i j ^ 2)) +
        2 * ((aOf d p ^ 2 * ∑ j ∈ nbhd G S v, greenP G (aOf d p) τ y σ S v j ^ 2) *
          rowWt G d p yp ym σ S v) := by
  have hp1 : 1 ≤ p := le_trans (by norm_num) hR.two_le_p
  have hy0 : ∀ i, 0 ≤ y i := by
    rcases hb with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] <;> assumption
  obtain ⟨hP, hPc⟩ := posDef_branch G hp1 hyp hym hv hb hσ
  obtain ⟨-, -, hrow, hmark⟩ := root_branch G hR.aOf_pos.ne' hb.tau hy0 hv hP hPc
  obtain ⟨-, hda⟩ := TRegime.d_aOf_sq hR
  obtain ⟨x, hx⟩ : ∃ x : nbhd G S v → ℝ, ∀ j,
      x j = starRow (τ * aOf d p) (rootMat G (aOf d p) τ y σ S v) (rootSigns G σ S v) j :=
    ⟨_, fun j => rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : nbhd G S v → nbhd G S v → ℝ, ∀ i j,
      c i j = starMark (τ * aOf d p) (rootMat G (aOf d p) τ y σ S v) (rootSigns G σ S v) i j :=
    ⟨_, fun i j => rfl⟩
  have hRx : aOf d p ^ 2 * ∑ j ∈ nbhd G S v, greenP G (aOf d p) τ y σ S v j ^ 2 =
      aOf d p ^ 2 * ∑ j, x j ^ 2 := by
    rw [← Finset.sum_coe_sort (nbhd G S v)]
    exact congrArg _ (Finset.sum_congr rfl fun j _ => by rw [hrow j, hx j])
  have hCc : greenP G (aOf d p) τ y σ S v v ^ 2 *
      ∑ i ∈ nbhd G S v, ∑ j ∈ nbhd G S v, greenP G (aOf d p) τ y σ S i j ^ 2 =
        ∑ i, ∑ j, c i j ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_coe_sort (nbhd G S v)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_coe_sort (nbhd G S v)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hc i j, ← hmark i j]
    ring
  have he : ∀ i j, starCore (τ * aOf d p) (rootMat G (aOf d p) τ y σ S v) (rootSigns G σ S v) i j =
      c i j - x i * x j := fun i j => by
    rw [hc i j, hx i, hx j, starMark]
    ring
  have hcard : (Fintype.card (nbhd G S v) : ℝ) * aOf d p ^ 2 ≤ 1 / 2 := by
    have h := card_nbhd_le G hC.deg S v
    have h' : (Fintype.card (nbhd G S v) : ℝ) ≤ d := by exact_mod_cast h
    nlinarith [sq_nonneg (aOf d p)]
  set R := aOf d p ^ 2 * ∑ j ∈ nbhd G S v, greenP G (aOf d p) τ y σ S v j ^ 2 with hR_def
  have hR0 : 0 ≤ R := by rw [hR_def]; positivity
  have hRW : R * R ≤ R * rowWt G d p yp ym σ S v :=
    mul_le_mul_of_nonneg_left (g12_R_le_W G hR hyp hym hv hb hσ) hR0
  have s1 : ∑ _i : nbhd G S v, ∑ j : nbhd G S v, x j ^ 2 =
      (Fintype.card (nbhd G S v) : ℝ) * ∑ j, x j ^ 2 := by
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  have s2 : ∑ i : nbhd G S v, ∑ j : nbhd G S v, x i ^ 2 * x j ^ 2 = (∑ j, x j ^ 2) ^ 2 := by
    rw [sq, Finset.sum_mul_sum]
  have s3 : ∑ i : nbhd G S v, ∑ j : nbhd G S v,
      (x j ^ 2 + 2 * c i j ^ 2 + 2 * (x i ^ 2 * x j ^ 2)) =
      ∑ _i : nbhd G S v, ∑ j : nbhd G S v, x j ^ 2 + 2 * ∑ i, ∑ j, c i j ^ 2 +
        2 * ∑ i : nbhd G S v, ∑ j : nbhd G S v, x i ^ 2 * x j ^ 2 := by
    simp only [Finset.sum_add_distrib, Finset.mul_sum]
  calc ∑ i, g12Xb G d p τ y σ S v i
      = aOf d p ^ 4 * ∑ i, ∑ j, (x j ^ 2 + (c i j - x i * x j) ^ 2) := by
        unfold g12Xb
        rw [← Finset.mul_sum]
        exact congrArg _ (Finset.sum_congr rfl fun i _ =>
          Finset.sum_congr rfl fun j _ => by rw [he i j, ← hx j])
    _ ≤ aOf d p ^ 4 * ∑ i, ∑ j, (x j ^ 2 + 2 * c i j ^ 2 + 2 * (x i ^ 2 * x j ^ 2)) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ =>
          Finset.sum_le_sum fun j _ => ?_) (by positivity)
        nlinarith [sq_nonneg (c i j + x i * x j)]
    _ = (Fintype.card (nbhd G S v) * aOf d p ^ 2) * (aOf d p ^ 2 * ∑ j, x j ^ 2) +
          2 * (aOf d p ^ 4 * ∑ i, ∑ j, c i j ^ 2) +
          2 * ((aOf d p ^ 2 * ∑ j, x j ^ 2) * (aOf d p ^ 2 * ∑ j, x j ^ 2)) := by
        rw [s3, s1, s2]
        ring
    _ ≤ 1 / 2 * R + 2 * (aOf d p ^ 4 * ∑ i, ∑ j, c i j ^ 2) +
          2 * (R * rowWt G d p yp ym σ S v) := by
        rw [← hRx]
        have := mul_le_mul_of_nonneg_right hcard hR0
        linarith
    _ = _ := by rw [hCc]

/-- `E[R_τ W] ≤ e² B λ` (T.IL, both branches; as `rowWt_mul_R_le` with `m = 1`). -/
theorem g12_rowWt_mul_R_le (hR : TRegime d p) (hk : 32 * kIL d ≤ p) {S : Finset V} {lam : ℝ}
    (hC : CapCtx G d p S lam) {yp ym : V → ℝ} (hyp : InCube (lam * sOf d p) yp)
    (hym : InCube (lam * sOf d p) ym) {τ : ℝ} {y : V → ℝ} (hb : IsBranch yp ym τ y) {v : V}
    (hv : v ∈ S) {l : ℝ} (hvl : vth d ≤ l) (hS : incRowE G d p yp ym S v τ y / d ≤ l) :
    lawE G p (aOf d p) yp ym S (fun σ => (aOf d p ^ 2 *
        ∑ j ∈ nbhd G S v, greenP G (aOf d p) τ y σ S v j ^ 2) * rowWt G d p yp ym σ S v) ≤
      Real.exp 2 * (3 * 96 ^ 4) * l := by
  have hdR := hR.ten_pow_six_le_d
  have hd0 : (0 : ℝ) < d := lt_of_lt_of_le (by norm_num) hdR
  have hd3 : 3 ≤ d := le_trans (by norm_num) hR.ten_pow_six_le_nat
  have hp8 : 8 ≤ p := le_trans (by norm_num) hR.hp
  obtain ⟨-, hda⟩ := TRegime.d_aOf_sq hR
  have hZ := Zw_pos_cap G hR hC hyp hym
  have hθ : 0 < vth d := by unfold vth; positivity
  have hEX : lawE G p (aOf d p) yp ym S (fun σ => aOf d p ^ 2 *
      ∑ j ∈ nbhd G S v, greenP G (aOf d p) τ y σ S v j ^ 2) ≤ l := by
    rw [lawE_const_mul, lawE_sum]
    have h1 : incRowE G d p yp ym S v τ y ≤ d * l := by
      rwa [div_le_iff₀ hd0, mul_comm] at hS
    have h2 : aOf d p ^ 2 * incRowE G d p yp ym S v τ y ≤ aOf d p ^ 2 * (d * l) :=
      mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
    have hl : 0 ≤ l := hθ.le.trans hvl
    have h3 : aOf d p ^ 2 * (d * l) ≤ l := by nlinarith
    exact h2.trans h3
  have hk1 : 1 ≤ kIL d := one_le_kIL hd3
  have hmom : lawE G p (aOf d p) yp ym S (fun σ => rowWt G d p yp ym σ S v ^ (2 * kIL d)) ≤
      (3 * 96 ^ 4) ^ (2 * kIL d) :=
    rowWt_moment_le G hR hC hyp hym hv (by omega) (by omega)
  exact lawE_mul_le_vth G hd3 hZ (fun σ _ => by positivity)
    (fun σ _ => rowWt_nonneg' G d p yp ym σ S v) hvl (by norm_num) (by
      have h8 : (8 : ℝ) ≤ d := by linarith
      exact h8.trans (le_self_pow₀ (by linarith) (by norm_num))) (by positivity) hEX
    (rowR_sq_le G hR hC hyp hym hb hv hp8) hmom

/-- `E Σ_i X^τ_i ≤ (1 + 2 e² B) λ`. -/
theorem g12_sumXb_le (hR : TRegime d p) (hk : 32 * kIL d ≤ p) {S : Finset V} {lam : ℝ}
    (hC : CapCtx G d p S lam) {yp ym : V → ℝ} (hyp : InCube (lam * sOf d p) yp)
    (hym : InCube (lam * sOf d p) ym) {τ : ℝ} {y : V → ℝ} (hb : IsBranch yp ym τ y) {v : V}
    (hv : v ∈ S) {l : ℝ} (hvl : vth d ≤ l) (hS : incRowE G d p yp ym S v τ y / d ≤ l)
    (hM : markE G d p yp ym S v τ y / (d : ℝ) ^ 2 ≤ l) :
    lawE G p (aOf d p) yp ym S (fun σ => ∑ i, g12Xb G d p τ y σ S v i) ≤
      (1 + 2 * (Real.exp 2 * (3 * 96 ^ 4))) * l := by
  have hdR := hR.ten_pow_six_le_d
  have hd0 : (0 : ℝ) < d := lt_of_lt_of_le (by norm_num) hdR
  obtain ⟨-, hda⟩ := TRegime.d_aOf_sq hR
  have hθ : 0 < vth d := by unfold vth; positivity
  have hl : 0 ≤ l := hθ.le.trans hvl
  have hyp0 : ∀ i, 0 ≤ yp i := fun i => (hyp i).1
  have hym0 : ∀ i, 0 ≤ ym i := fun i => (hym i).1
  have hRW := g12_rowWt_mul_R_le G hR hk hC hyp hym hb hv hvl hS
  have h1 : incRowE G d p yp ym S v τ y ≤ d * l := by
    rwa [div_le_iff₀ hd0, mul_comm] at hS
  have h2 : markE G d p yp ym S v τ y ≤ (d : ℝ) ^ 2 * l := by
    rwa [div_le_iff₀ (by positivity), mul_comm] at hM
  have hE1 : aOf d p ^ 2 * incRowE G d p yp ym S v τ y ≤ l / 2 := by
    have := mul_le_mul_of_nonneg_left h1 (sq_nonneg (aOf d p))
    nlinarith
  have hE2 : aOf d p ^ 4 * markE G d p yp ym S v τ y ≤ l / 4 := by
    have := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ aOf d p ^ 4)
    have hda2 : ((d : ℝ) * aOf d p ^ 2) ^ 2 ≤ 1 / 4 := by
      have h0 : 0 ≤ (d : ℝ) * aOf d p ^ 2 := by positivity
      nlinarith
    nlinarith
  calc lawE G p (aOf d p) yp ym S (fun σ => ∑ i, g12Xb G d p τ y σ S v i)
      ≤ lawE G p (aOf d p) yp ym S (fun σ =>
          1 / 2 * (aOf d p ^ 2 * ∑ j ∈ nbhd G S v, greenP G (aOf d p) τ y σ S v j ^ 2) +
          2 * (aOf d p ^ 4 * (greenP G (aOf d p) τ y σ S v v ^ 2 *
            ∑ i ∈ nbhd G S v, ∑ j ∈ nbhd G S v, greenP G (aOf d p) τ y σ S i j ^ 2)) +
          2 * ((aOf d p ^ 2 * ∑ j ∈ nbhd G S v, greenP G (aOf d p) τ y σ S v j ^ 2) *
            rowWt G d p yp ym σ S v)) :=
        lawE_mono G fun σ hσ => g12_sumXb_pt G hR hC hyp0 hym0 hb hv hσ
    _ = 1 / 2 * (aOf d p ^ 2 * incRowE G d p yp ym S v τ y) +
          2 * (aOf d p ^ 4 * markE G d p yp ym S v τ y) +
          2 * lawE G p (aOf d p) yp ym S (fun σ => (aOf d p ^ 2 *
            ∑ j ∈ nbhd G S v, greenP G (aOf d p) τ y σ S v j ^ 2) * rowWt G d p yp ym σ S v) := by
        rw [lawE_add, lawE_add, lawE_const_mul, lawE_const_mul, lawE_const_mul, lawE_const_mul,
          lawE_const_mul, lawE_sum]
        rfl
    _ ≤ 1 / 2 * (l / 2) + 2 * (l / 4) + 2 * (Real.exp 2 * (3 * 96 ^ 4) * l) := by
        gcongr
    _ ≤ (1 + 2 * (Real.exp 2 * (3 * 96 ^ 4))) * l := by nlinarith

/-- **Per-row interpolation**: `E Σ_i Y_i X_i ≤ e² B_Y (E Σ_i X_i + ϑ)` for `0 ≤ X_i ≤ W²` and
`‖Y_i‖_{2k} ≤ B_Y`. -/
theorem g12_sum_interp (hR : TRegime d p) (hk : 32 * kIL d ≤ p) {S : Finset V} {lam : ℝ}
    (hC : CapCtx G d p S lam) {yp ym : V → ℝ} (hyp : InCube (lam * sOf d p) yp)
    (hym : InCube (lam * sOf d p) ym) {v : V} (hv : v ∈ S)
    {X Y : nbhd G S v → Config V → ℝ} (hX0 : ∀ i σ, 0 ≤ X i σ) (hY0 : ∀ i σ, 0 ≤ Y i σ)
    (hXW : ∀ i σ, wt G p (aOf d p) yp ym σ S ≠ 0 → X i σ ≤ rowWt G d p yp ym σ S v ^ 2)
    {BY : ℝ} (hBY : 0 ≤ BY)
    (hY : ∀ i, lawE G p (aOf d p) yp ym S (fun σ => Y i σ ^ (2 * kIL d)) ≤ BY ^ (2 * kIL d)) :
    lawE G p (aOf d p) yp ym S (fun σ => ∑ i, Y i σ * X i σ) ≤
      Real.exp 2 * BY * (lawE G p (aOf d p) yp ym S (fun σ => ∑ i, X i σ) + vth d) := by
  have hdR := hR.ten_pow_six_le_d
  have hd0 : (0 : ℝ) < d := lt_of_lt_of_le (by norm_num) hdR
  have hd3 : 3 ≤ d := le_trans (by norm_num) hR.ten_pow_six_le_nat
  have hZ := Zw_pos_cap G hR hC hyp hym
  have hk1 : 1 ≤ kIL d := one_le_kIL hd3
  have hθ : 0 < vth d := by unfold vth; positivity
  have hW4 : lawE G p (aOf d p) yp ym S (fun σ => rowWt G d p yp ym σ S v ^ 4) ≤
      (3 * 96 ^ 4) ^ 4 :=
    rowWt_moment_le G hR hC hyp hym hv (by norm_num) (by omega)
  have hBd : (d : ℝ) * (3 * 96 ^ 4) ^ 2 ≤ (d : ℝ) ^ 30 := by
    have h1 : ((3 : ℝ) * 96 ^ 4) ^ 2 ≤ (d : ℝ) ^ 29 := by
      calc ((3 : ℝ) * 96 ^ 4) ^ 2 ≤ ((10 : ℝ) ^ 6) ^ 3 := by norm_num
        _ ≤ (d : ℝ) ^ 3 := pow_le_pow_left₀ (by norm_num) hdR 3
        _ ≤ (d : ℝ) ^ 29 := pow_le_pow_right₀ (by linarith) (by norm_num)
    calc (d : ℝ) * (3 * 96 ^ 4) ^ 2 ≤ d * d ^ 29 := mul_le_mul_of_nonneg_left h1 hd0.le
      _ = d ^ 30 := by ring
  have hone : ∀ i, lawE G p (aOf d p) yp ym S (fun σ => Y i σ * X i σ) ≤
      Real.exp 2 * BY * (lawE G p (aOf d p) yp ym S (X i) + vth d / d) := by
    intro i
    have hEX0 : 0 ≤ lawE G p (aOf d p) yp ym S (X i) := lawE_nonneg G fun σ _ => hX0 i σ
    have hX2 : lawE G p (aOf d p) yp ym S (fun σ => ((d : ℝ) * X i σ) ^ 2) ≤
        ((d : ℝ) * (3 * 96 ^ 4) ^ 2) ^ 2 := by
      calc lawE G p (aOf d p) yp ym S (fun σ => ((d : ℝ) * X i σ) ^ 2)
          = (d : ℝ) ^ 2 * lawE G p (aOf d p) yp ym S (fun σ => X i σ ^ 2) := by
            rw [← lawE_const_mul]
            congr 1
            funext σ
            ring
        _ ≤ (d : ℝ) ^ 2 * lawE G p (aOf d p) yp ym S
              (fun σ => rowWt G d p yp ym σ S v ^ 4) := by
            refine mul_le_mul_of_nonneg_left (lawE_mono G fun σ hσ => ?_) (by positivity)
            calc X i σ ^ 2 ≤ (rowWt G d p yp ym σ S v ^ 2) ^ 2 :=
                  pow_le_pow_left₀ (hX0 i σ) (hXW i σ hσ) 2
              _ = rowWt G d p yp ym σ S v ^ 4 := by ring
        _ ≤ (d : ℝ) ^ 2 * (3 * 96 ^ 4) ^ 4 := mul_le_mul_of_nonneg_left hW4 (by positivity)
        _ = _ := by ring
    have h := lawE_mul_le_vth G hd3 hZ (X := fun σ => (d : ℝ) * X i σ) (Y := Y i)
      (fun σ _ => mul_nonneg hd0.le (hX0 i σ)) (fun σ _ => hY0 i σ)
      (m := d * lawE G p (aOf d p) yp ym S (X i) + vth d)
      (by nlinarith) (by positivity) hBd hBY
      (by rw [lawE_const_mul]; linarith) hX2 (hY i)
    have e : lawE G p (aOf d p) yp ym S (fun σ => (d : ℝ) * X i σ * Y i σ) =
        d * lawE G p (aOf d p) yp ym S (fun σ => Y i σ * X i σ) := by
      rw [← lawE_const_mul]
      congr 1
      funext σ
      ring
    have e2 : Real.exp 2 * BY * (d * lawE G p (aOf d p) yp ym S (X i) + vth d) =
        d * (Real.exp 2 * BY * (lawE G p (aOf d p) yp ym S (X i) + vth d / d)) := by
      have : (d : ℝ) * (vth d / d) = vth d := by field_simp
      calc Real.exp 2 * BY * (d * lawE G p (aOf d p) yp ym S (X i) + vth d)
          = Real.exp 2 * BY * (d * lawE G p (aOf d p) yp ym S (X i) + d * (vth d / d)) := by
            rw [this]
        _ = _ := by ring
    rw [e, e2] at h
    exact le_of_mul_le_mul_left h hd0
  have hcard : (Fintype.card (nbhd G S v) : ℝ) ≤ d := by
    exact_mod_cast card_nbhd_le G hC.deg S v
  have hEXs : 0 ≤ Real.exp 2 * BY := by positivity
  rw [lawE_sum, lawE_sum]
  calc ∑ i, lawE G p (aOf d p) yp ym S (fun σ => Y i σ * X i σ)
      ≤ ∑ i, Real.exp 2 * BY * (lawE G p (aOf d p) yp ym S (X i) + vth d / d) :=
        Finset.sum_le_sum fun i _ => hone i
    _ = Real.exp 2 * BY * (∑ i, lawE G p (aOf d p) yp ym S (X i) +
          (Fintype.card (nbhd G S v) : ℝ) * (vth d / d)) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul]
    _ ≤ Real.exp 2 * BY * (∑ i, lawE G p (aOf d p) yp ym S (X i) + vth d) := by
        refine mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) hEXs
        calc (Fintype.card (nbhd G S v) : ℝ) * (vth d / d) ≤ d * (vth d / d) :=
              mul_le_mul_of_nonneg_right hcard (by positivity)
          _ = vth d := by field_simp

/-- `E (1 + r_i)^{4n} ≤ 5 · 96^{4n}` for `8n ≤ p` (`r_i ≤ ρ_i`, F2). -/
theorem g12_scale_moment (hR : TRegime d p) {S : Finset V} {lam : ℝ} (hC : CapCtx G d p S lam)
    {yp ym : V → ℝ} (hyp : InCube (lam * sOf d p) yp) (hym : InCube (lam * sOf d p) ym)
    {v : V} (hv : v ∈ S) (i : nbhd G S v) {n : ℕ} (hn : 8 * n ≤ p) :
    lawE G p (aOf d p) yp ym S (fun σ => (1 + g12r G d p yp ym σ S v i) ^ (4 * n)) ≤
      5 * 96 ^ (4 * n) := by
  have hi : (i : V) ∈ S := (Finset.mem_filter.1 i.2).1
  refine le_trans (lawE_mono G fun σ hσ => ?_) (one_add_rho_moment_le G hR hC hyp hym hv hi hn)
  have h0 := g12r_nonneg G d p yp ym σ S v i
  have h1 := starScale_le_rho G hR hC hyp hym hv hσ i
  exact pow_le_pow_left₀ (by linarith) (by unfold g12r; linarith) _

theorem g12_five_le_three_pow {k : ℕ} (hk : 1 ≤ k) : (5 : ℝ) ≤ 3 ^ (2 * k) :=
  calc (5 : ℝ) ≤ 3 ^ 2 := by norm_num
    _ ≤ 3 ^ (2 * k) := pow_le_pow_right₀ (by norm_num) (by omega)

/-- `‖(1 + r_i)⁴‖_{2k} ≤ 3 · 96⁴`. -/
theorem g12_Y4_moment (hR : TRegime d p) (hk : 32 * kIL d ≤ p) {S : Finset V} {lam : ℝ}
    (hC : CapCtx G d p S lam) {yp ym : V → ℝ} (hyp : InCube (lam * sOf d p) yp)
    (hym : InCube (lam * sOf d p) ym) {v : V} (hv : v ∈ S) (i : nbhd G S v) :
    lawE G p (aOf d p) yp ym S (fun σ => ((1 + g12r G d p yp ym σ S v i) ^ 4) ^ (2 * kIL d)) ≤
      (3 * 96 ^ 4) ^ (2 * kIL d) := by
  have hd3 : 3 ≤ d := le_trans (by norm_num) hR.ten_pow_six_le_nat
  have hk1 := one_le_kIL hd3
  have h := g12_scale_moment G hR hC hyp hym hv i (n := 2 * kIL d) (by omega)
  have e : (fun σ => ((1 + g12r G d p yp ym σ S v i) ^ 4) ^ (2 * kIL d)) =
      fun σ => (1 + g12r G d p yp ym σ S v i) ^ (4 * (2 * kIL d)) := by
    funext σ
    rw [← pow_mul]
  rw [e]
  refine h.trans ?_
  rw [mul_pow, ← pow_mul]
  exact mul_le_mul_of_nonneg_right (g12_five_le_three_pow hk1) (by positivity)

/-- `‖(1 + r_i)⁶‖_{2k} ≤ 3 · 96⁶`. -/
theorem g12_Y6_moment (hR : TRegime d p) (hk : 32 * kIL d ≤ p) {S : Finset V} {lam : ℝ}
    (hC : CapCtx G d p S lam) {yp ym : V → ℝ} (hyp : InCube (lam * sOf d p) yp)
    (hym : InCube (lam * sOf d p) ym) {v : V} (hv : v ∈ S) (i : nbhd G S v) :
    lawE G p (aOf d p) yp ym S (fun σ => ((1 + g12r G d p yp ym σ S v i) ^ 6) ^ (2 * kIL d)) ≤
      (3 * 96 ^ 6) ^ (2 * kIL d) := by
  have hd3 : 3 ≤ d := le_trans (by norm_num) hR.ten_pow_six_le_nat
  have hk1 := one_le_kIL hd3
  have h := g12_scale_moment G hR hC hyp hym hv i (n := 3 * kIL d) (by omega)
  have e : (fun σ => ((1 + g12r G d p yp ym σ S v i) ^ 6) ^ (2 * kIL d)) =
      fun σ => (1 + g12r G d p yp ym σ S v i) ^ (4 * (3 * kIL d)) := by
    funext σ
    rw [← pow_mul, show 6 * (2 * kIL d) = 4 * (3 * kIL d) by ring]
  rw [e]
  refine h.trans ?_
  rw [mul_pow, ← pow_mul, show 6 * (2 * kIL d) = 4 * (3 * kIL d) by ring]
  exact mul_le_mul_of_nonneg_right (g12_five_le_three_pow hk1) (by positivity)

/-- `‖W (1 + r_i)⁴‖_{2k} ≤ 9 · 96⁸` (`ab ≤ (a² + b²)/2`). -/
theorem g12_YT_moment (hR : TRegime d p) (hk : 32 * kIL d ≤ p) {S : Finset V} {lam : ℝ}
    (hC : CapCtx G d p S lam) {yp ym : V → ℝ} (hyp : InCube (lam * sOf d p) yp)
    (hym : InCube (lam * sOf d p) ym) {v : V} (hv : v ∈ S) (i : nbhd G S v) :
    lawE G p (aOf d p) yp ym S (fun σ =>
        (rowWt G d p yp ym σ S v * (1 + g12r G d p yp ym σ S v i) ^ 4) ^ (2 * kIL d)) ≤
      (9 * 96 ^ 8) ^ (2 * kIL d) := by
  have hd3 : 3 ≤ d := le_trans (by norm_num) hR.ten_pow_six_le_nat
  have hk1 := one_le_kIL hd3
  set k := kIL d with hk_def
  have hW := rowWt_moment_le G hR hC hyp hym hv (n := 4 * k) (by omega) (by omega)
  have hr := g12_scale_moment G hR hC hyp hym hv i (n := 4 * k) (by omega)
  have hpt : ∀ σ, (rowWt G d p yp ym σ S v * (1 + g12r G d p yp ym σ S v i) ^ 4) ^ (2 * k) ≤
      1 / 2 * (rowWt G d p yp ym σ S v ^ (4 * k) +
        (1 + g12r G d p yp ym σ S v i) ^ (4 * (4 * k))) := by
    intro σ
    have e : (rowWt G d p yp ym σ S v * (1 + g12r G d p yp ym σ S v i) ^ 4) ^ (2 * k) =
        rowWt G d p yp ym σ S v ^ (2 * k) * (1 + g12r G d p yp ym σ S v i) ^ (4 * (2 * k)) := by
      rw [mul_pow, ← pow_mul]
    have e1 : rowWt G d p yp ym σ S v ^ (4 * k) = (rowWt G d p yp ym σ S v ^ (2 * k)) ^ 2 := by
      ring
    have e2 : (1 + g12r G d p yp ym σ S v i) ^ (4 * (4 * k)) =
        ((1 + g12r G d p yp ym σ S v i) ^ (4 * (2 * k))) ^ 2 := by
      ring
    rw [e, e1, e2]
    nlinarith [sq_nonneg (rowWt G d p yp ym σ S v ^ (2 * k) -
      (1 + g12r G d p yp ym σ S v i) ^ (4 * (2 * k)))]
  have hB : ((3 : ℝ) * 96 ^ 4) ^ (4 * k) = (9 * 96 ^ 8) ^ (2 * k) := by
    rw [show (9 : ℝ) * 96 ^ 8 = (3 * 96 ^ 4) ^ 2 by norm_num, ← pow_mul,
      show 2 * (2 * k) = 4 * k by ring]
  have h5 : (5 : ℝ) * 96 ^ (4 * (4 * k)) ≤ (3 * 96 ^ 4) ^ (4 * k) := by
    rw [mul_pow, ← pow_mul]
    have : (5 : ℝ) ≤ 3 ^ (4 * k) := by
      have := g12_five_le_three_pow (k := 2 * k) (by omega)
      rwa [show 2 * (2 * k) = 4 * k by ring] at this
    exact mul_le_mul_of_nonneg_right this (by positivity)
  calc lawE G p (aOf d p) yp ym S (fun σ =>
        (rowWt G d p yp ym σ S v * (1 + g12r G d p yp ym σ S v i) ^ 4) ^ (2 * k))
      ≤ lawE G p (aOf d p) yp ym S (fun σ => 1 / 2 * (rowWt G d p yp ym σ S v ^ (4 * k) +
          (1 + g12r G d p yp ym σ S v i) ^ (4 * (4 * k)))) := lawE_mono G fun σ _ => hpt σ
    _ = 1 / 2 * (lawE G p (aOf d p) yp ym S (fun σ => rowWt G d p yp ym σ S v ^ (4 * k)) +
          lawE G p (aOf d p) yp ym S
            (fun σ => (1 + g12r G d p yp ym σ S v i) ^ (4 * (4 * k)))) := by
        rw [lawE_const_mul, lawE_add]
    _ ≤ 1 / 2 * ((3 * 96 ^ 4) ^ (4 * k) + 5 * 96 ^ (4 * (4 * k))) := by gcongr
    _ ≤ 1 / 2 * ((3 * 96 ^ 4) ^ (4 * k) + (3 * 96 ^ 4) ^ (4 * k)) := by gcongr
    _ = (9 * 96 ^ 8) ^ (2 * k) := by rw [← hB]; ring

/-- The constant `K = 2 + 2 e² B` of the row energies. -/
noncomputable def g12K : ℝ := 2 + 2 * (Real.exp 2 * (3 * 96 ^ 4))

theorem g12K_pos : 0 < g12K := by
  unfold g12K
  positivity

/-- `E[U⁺ + √U⁺ √U⁻] ≤ 2 e² B_Y K √(λ_c δ_c)` for `U^± = Σ_i Y_i X^±_i`. -/
theorem g12_EU_le (hR : TRegime d p) (hk : 32 * kIL d ≤ p) {S : Finset V} {lam : ℝ}
    (hC : CapCtx G d p S lam) {yp ym : V → ℝ} (hyp : InCube (lam * sOf d p) yp)
    (hym : InCube (lam * sOf d p) ym) {v : V} (hv : v ∈ S) {lr lc dc : ℝ} (hvl : vth d ≤ lr)
    (hlrc : lr ≤ lc) (hlcd : lc ≤ dc)
    (hS1 : incRowE G d p yp ym S v 1 yp / d ≤ lr)
    (hS2 : incRowE G d p yp ym S v (-1) ym / d ≤ dc)
    (hM1 : markE G d p yp ym S v 1 yp / (d : ℝ) ^ 2 ≤ lc)
    (hM2 : markE G d p yp ym S v (-1) ym / (d : ℝ) ^ 2 ≤ dc)
    {Y : nbhd G S v → Config V → ℝ} (hY0 : ∀ i σ, 0 ≤ Y i σ) {BY : ℝ} (hBY : 0 ≤ BY)
    (hY : ∀ i, lawE G p (aOf d p) yp ym S (fun σ => Y i σ ^ (2 * kIL d)) ≤ BY ^ (2 * kIL d)) :
    lawE G p (aOf d p) yp ym S (fun σ => ∑ i, Y i σ * g12Xb G d p 1 yp σ S v i +
        Real.sqrt (∑ i, Y i σ * g12Xb G d p 1 yp σ S v i) *
          Real.sqrt (∑ i, Y i σ * g12Xb G d p (-1) ym σ S v i)) ≤
      2 * (Real.exp 2 * BY * g12K) * Real.sqrt (lc * dc) := by
  have hd0 : (0 : ℝ) < d := lt_of_lt_of_le (by norm_num) hR.ten_pow_six_le_d
  have hθ : 0 < vth d := by unfold vth; positivity
  have hlr0 : 0 ≤ lr := hθ.le.trans hvl
  have hlc0 : 0 ≤ lc := hlr0.trans hlrc
  have hdc0 : 0 ≤ dc := hlc0.trans hlcd
  have hvc : vth d ≤ lc := hvl.trans hlrc
  have hvd : vth d ≤ dc := hvc.trans hlcd
  have hyp0 : ∀ i, 0 ≤ yp i := fun i => (hyp i).1
  have hym0 : ∀ i, 0 ≤ ym i := fun i => (hym i).1
  have hK := g12K_pos
  set c := Real.exp 2 * BY * g12K with hc_def
  have hc0 : 0 ≤ c := by positivity
  have hXp := g12_sumXb_le G hR hk hC hyp hym (isBranch_plus yp ym) hv hvc (hS1.trans hlrc) hM1
  have hXm := g12_sumXb_le G hR hk hC hyp hym (isBranch_minus yp ym) hv hvd hS2 hM2
  have hint : ∀ {τ : ℝ} {y : V → ℝ}, IsBranch yp ym τ y → ∀ {l : ℝ}, 0 ≤ l → vth d ≤ l →
      lawE G p (aOf d p) yp ym S (fun σ => ∑ i, g12Xb G d p τ y σ S v i) ≤
        (1 + 2 * (Real.exp 2 * (3 * 96 ^ 4))) * l →
      lawE G p (aOf d p) yp ym S (fun σ => ∑ i, Y i σ * g12Xb G d p τ y σ S v i) ≤ c * l := by
    intro τ y hb l hl hvl' hX
    refine (g12_sum_interp G hR hk hC hyp hym hv (X := fun i σ => g12Xb G d p τ y σ S v i)
      (fun i σ => g12Xb_nonneg G d p τ y σ S v i) hY0
      (fun i σ hσ => g12Xb_le_W G hR hyp0 hym0 hv hb hσ i) hBY hY).trans ?_
    have h2 : lawE G p (aOf d p) yp ym S (fun σ => ∑ i, g12Xb G d p τ y σ S v i) + vth d ≤
        g12K * l := by
      unfold g12K
      linarith
    calc Real.exp 2 * BY * (lawE G p (aOf d p) yp ym S (fun σ => ∑ i, g12Xb G d p τ y σ S v i) +
          vth d) ≤ Real.exp 2 * BY * (g12K * l) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = c * l := by rw [hc_def]; ring
  have hUp := hint (isBranch_plus yp ym) hlc0 hvc hXp
  have hUm := hint (isBranch_minus yp ym) hdc0 hvd hXm
  have hU0 : ∀ (τ : ℝ) (y : V → ℝ) σ, 0 ≤ ∑ i, Y i σ * g12Xb G d p τ y σ S v i := fun τ y σ =>
    Finset.sum_nonneg fun i _ => mul_nonneg (hY0 i σ) (g12Xb_nonneg G d p τ y σ S v i)
  have hCS := g12_lawE_sqrt_mul_le G (p := p) (a := aOf d p) (yp := yp) (ym := ym) (S := S)
    (fun σ => ∑ i, Y i σ * g12Xb G d p 1 yp σ S v i)
    (fun σ => ∑ i, Y i σ * g12Xb G d p (-1) ym σ S v i) (hU0 1 yp) (hU0 (-1) ym)
  have hsq : Real.sqrt (c * lc) * Real.sqrt (c * dc) = c * Real.sqrt (lc * dc) := by
    rw [← g12_sqrt_scale hc0, Real.sqrt_mul hlc0]
  have hls : lc ≤ Real.sqrt (lc * dc) := by
    calc lc = Real.sqrt (lc * lc) := (Real.sqrt_mul_self hlc0).symm
      _ ≤ Real.sqrt (lc * dc) := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hlcd hlc0)
  rw [lawE_add]
  calc lawE G p (aOf d p) yp ym S (fun σ => ∑ i, Y i σ * g12Xb G d p 1 yp σ S v i) +
        lawE G p (aOf d p) yp ym S (fun σ => Real.sqrt (∑ i, Y i σ * g12Xb G d p 1 yp σ S v i) *
          Real.sqrt (∑ i, Y i σ * g12Xb G d p (-1) ym σ S v i))
      ≤ c * lc + Real.sqrt (c * lc) * Real.sqrt (c * dc) :=
        add_le_add hUp (hCS.trans (mul_le_mul (Real.sqrt_le_sqrt hUp) (Real.sqrt_le_sqrt hUm)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))
    _ = c * lc + c * Real.sqrt (lc * dc) := by rw [hsq]
    _ ≤ c * Real.sqrt (lc * dc) + c * Real.sqrt (lc * dc) := by
        gcongr
    _ = 2 * c * Real.sqrt (lc * dc) := by ring

end Law

end SecC

end BiluLinial.Tight
