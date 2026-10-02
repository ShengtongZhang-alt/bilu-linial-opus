/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecC.RowCompareParts
public import BiluLinial.Tight.SecC.RootMoments

/-!
# The grade-one row term `X₅` (nodes CR-X5 of `docs/tight/BP_SECC.md`)

Source lines 1170–1190 (CR3) and `docs/tight/DR1_CHECK.md` §3 (CR3′).
`X₅ = E[W a² |Σ_N G⁺_vj (G⁺_vj - G⁻_vj)|]` with the unmarked weight `W = rowWt = a² Σ_N (1 + r_i)⁴`.

* Pointwise (`starScale_le_rho`, F1): at a supported signing `r_i ≤ s (h⁺_v + h⁺_i + h⁻_v + h⁻_i)`
  (`|G_vi|, √e_ii ≤ √(G_vv G_ii) ≤ (G_vv + G_ii)/2`, `e_ii = G_vv G_ii - G_vi² ≥ 0`,
  `G_uu = y_u h_u ≤ s h_u`), and `(G⁺_vj)² ≤ s² h⁺_v h⁺_j`.
* Moments (`rowWt_moment_le`): `E W^n ≤ (3·96⁴)^n` for `8n ≤ p` (power mean over `|N| ≤ d`,
  `a²d ≤ 1/2`, F2 `E h^{4n} ≤ 2^{4n}`); `E R₊² ≤ 64` for `R₊ = a² Σ_N (G⁺_vj)²`.
* Interpolation (`lawE_mul_le_vth`, `k = kIL d`, `32 kIL d ≤ p`): `E[W^m R₊] ≤ e² B^m λ_r` for
  `m = 1, 2` (`E R₊ = a² S₊ ≤ λ_r/2`, `ϑ ≤ λ_r`).
* **CR-X5, split** (`row_x5_split`): `|Σx(x-z)| ≤ Σx² + √(Σx²)√(Σz²)`, Cauchy–Schwarz in the law:
  `X₅ ≤ E[W R₊] + √(E[W² R₊]) √(E R₋) ≤ (e² + e) B √(λ_r ρ_r)` (`λ_r ≤ ρ_r`).
* **CR-X5, difference** (`row_x5_diff`): `|Σx(x-z)| ≤ √(Σx²)√(Σ(x-z)²)`:
  `X₅ ≤ √(E[W² R₊]) √(a² diffRowE) ≤ e B √(λ_r ρ_Δ)`.

**Checks.** `N = ∅`: `X₅ = 0`. Zero source at `v`: `G_vj = 0`, `X₅ = 0`. The constants are
explicit (`B = 3·96⁴`).
-/

@[expose] public section

namespace BiluLinial.Tight

namespace SecC

universe u

open Matrix

section Pointwise

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable {d p : ℕ}

omit [DecidableEq V] in
theorem starCore_neg (a : ℝ) {ι : Type*} [Fintype ι] (B : Matrix ι ι ℝ) (x : ι → ℝ) (k j : ι) :
    starCore (-a) B x k j = starCore a B x k j := by
  unfold starCore
  rw [neg_sq]

private theorem sqrt_mul_le_half {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x * y) ≤ (x + y) / 2 :=
  Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith [sq_nonneg (x - y)]⟩

/-- At a supported signing, for one branch: `|G_vi| ≤ (G_vv + G_ii)/2`,
`√(e_ii) ≤ (G_vv + G_ii)/2` and `(G_vj)² ≤ G_vv G_jj`, from F1 (`e_ii = G_vvG_ii - G_vi² ≥ 0`). -/
theorem branch_scale_le {a τ : ℝ} (ha : a ≠ 0) (hτ : τ = 1 ∨ τ = -1) {y : V → ℝ}
    (hy : ∀ i, 0 ≤ y i) {S : Finset V} {v : V} (hv : v ∈ S) {σ : Config V}
    (hP : (precN G a τ y σ S).PosDef) (hPc : (precCore G a τ y σ S v).PosDef)
    (i : nbhd G S v) :
    |greenP G a τ y σ S v i| ≤ (greenP G a τ y σ S v v + greenP G a τ y σ S i i) / 2 ∧
    Real.sqrt (starCore (τ * a) (rootMat G a τ y σ S v) (rootSigns G σ S v) i i) ≤
      (greenP G a τ y σ S v v + greenP G a τ y σ S i i) / 2 ∧
    greenP G a τ y σ S v i ^ 2 ≤ greenP G a τ y σ S v v * greenP G a τ y σ S i i := by
  obtain ⟨hα, -, hrow, hmark⟩ := root_branch G ha hτ hy hv hP hPc
  have hA := (shift_branch G hy le_rfl one_pos hPc).1
  have he0 : 0 ≤ starCore (τ * a) (rootMat G a τ y σ S v) (rootSigns G σ S v) i i :=
    starCore_diag_nonneg hA hα i
  have hm := hmark i i
  rw [starMark, ← hrow i] at hm
  have hvv : 0 ≤ greenP G a τ y σ S v v := by
    rw [greenP_self G hy σ S v]; exact mul_nonneg (hy v) hP.inv.diag_pos.le
  have hii : 0 ≤ greenP G a τ y σ S i i := by
    rw [greenP_self G hy σ S (i : V)]; exact mul_nonneg (hy i) hP.inv.diag_pos.le
  have hsq : greenP G a τ y σ S v i ^ 2 ≤ greenP G a τ y σ S v v * greenP G a τ y σ S i i := by
    nlinarith
  have hg := sqrt_mul_le_half hvv hii
  refine ⟨(Real.abs_le_sqrt hsq).trans hg, ?_, hsq⟩
  refine (Real.sqrt_le_sqrt ?_).trans hg
  nlinarith [sq_nonneg (greenP G a τ y σ S v i)]

/-- **Unmarked scale at a supported signing**: `r_i ≤ s (h⁺_v + h⁺_i + h⁻_v + h⁻_i)` and
`(G^τ_vj)² ≤ s² h^τ_v h^τ_j`. -/
theorem starScale_le_rho (hR : TRegime d p) {S : Finset V} {lam : ℝ} (hC : CapCtx G d p S lam)
    {yp ym : V → ℝ} (hyp : InCube (lam * sOf d p) yp) (hym : InCube (lam * sOf d p) ym)
    {v : V} (hv : v ∈ S) {σ : Config V} (hσ : wt G p (aOf d p) yp ym σ S ≠ 0)
    (i : nbhd G S v) :
    starScale (aOf d p) (rootMat G (aOf d p) 1 yp σ S v) (rootMat G (aOf d p) (-1) ym σ S v)
        (rootSigns G σ S v) i ≤
      sOf d p * (hN G (aOf d p) 1 yp σ S v + hN G (aOf d p) 1 yp σ S i +
        hN G (aOf d p) (-1) ym σ S v + hN G (aOf d p) (-1) ym σ S i) := by
  have hp1 : 1 ≤ p := le_trans (by norm_num) hR.two_le_p
  have hyp' := inCube_of_cap G hR hC hyp
  have hym' := inCube_of_cap G hR hC hym
  have hyp0 : ∀ i, 0 ≤ yp i := fun i => (hyp i).1
  have hym0 : ∀ i, 0 ≤ ym i := fun i => (hym i).1
  have ha := hR.aOf_pos.ne'
  obtain ⟨hPp, hPm, hc1, hc2⟩ := posDef_of_wt_ne_zero' G hp1 hyp0 hym0 hv hσ
  obtain ⟨h1, h2, -⟩ := branch_scale_le G ha (Or.inl rfl) hyp0 hv hPp hc1 i
  obtain ⟨h3, h4, -⟩ := branch_scale_le G ha (Or.inr rfl) hym0 hv hPm hc2 i
  obtain ⟨-, -, -, -, hrp, hrm, -, -⟩ := root_F1 G hR hyp0 hym0 hv hσ
  simp only [one_mul, neg_one_mul, starCore_neg] at h2 h4
  have hGp : ∀ u, greenP G (aOf d p) 1 yp σ S u u ≤ sOf d p * hN G (aOf d p) 1 yp σ S u :=
    fun u => by
      rw [greenP_self G hyp0 σ S u]
      exact mul_le_mul_of_nonneg_right (hyp' u).2 (hN_pos G hσ u).le
  have hGm : ∀ u, greenP G (aOf d p) (-1) ym σ S u u ≤ sOf d p * hN G (aOf d p) (-1) ym σ S u :=
    fun u => by
      rw [greenP_self G hym0 σ S u]
      exact mul_le_mul_of_nonneg_right (hym' u).2 (hN_pos_minus G hσ u).le
  unfold starScale
  rw [← hrp i, ← hrm i]
  have := hGp v
  have := hGp i
  have := hGm v
  have := hGm i
  linarith

theorem greenP_row_sq_le (hR : TRegime d p) {S : Finset V} {lam : ℝ} (hC : CapCtx G d p S lam)
    {yp ym : V → ℝ} (hyp : InCube (lam * sOf d p) yp) (hym : InCube (lam * sOf d p) ym)
    {τ : ℝ} {y : V → ℝ} (hb : IsBranch yp ym τ y) {v : V} (hv : v ∈ S) {σ : Config V}
    (hσ : wt G p (aOf d p) yp ym σ S ≠ 0) (j : nbhd G S v) :
    greenP G (aOf d p) τ y σ S v j ^ 2 ≤
      sOf d p ^ 2 * (hN G (aOf d p) τ y σ S v * hN G (aOf d p) τ y σ S j) := by
  have hp1 : 1 ≤ p := le_trans (by norm_num) hR.two_le_p
  have hy' := inCube_of_cap G hR hC (hb.inCube hyp hym)
  have hy0 : ∀ i, 0 ≤ y i := fun i => (hy' i).1
  obtain ⟨hP, hPc⟩ := posDef_branch G hp1 (fun i => (hyp i).1) (fun i => (hym i).1) hv hb hσ
  obtain ⟨-, -, h⟩ := branch_scale_le G hR.aOf_pos.ne' hb.tau hy0 hv hP hPc j
  have hhv := (hN_pos_branch G hb hσ v).le
  have hhj := (hN_pos_branch G hb hσ (j : V)).le
  rw [greenP_self G hy0 σ S v, greenP_self G hy0 σ S (j : V)] at h
  have h1 : y v * hN G (aOf d p) τ y σ S v ≤ sOf d p * hN G (aOf d p) τ y σ S v :=
    mul_le_mul_of_nonneg_right (hy' v).2 hhv
  have h2 : y j * hN G (aOf d p) τ y σ S j ≤ sOf d p * hN G (aOf d p) τ y σ S j :=
    mul_le_mul_of_nonneg_right (hy' j).2 hhj
  calc greenP G (aOf d p) τ y σ S v j ^ 2
      ≤ y v * hN G (aOf d p) τ y σ S v * (y j * hN G (aOf d p) τ y σ S j) := h
    _ ≤ sOf d p * hN G (aOf d p) τ y σ S v * (sOf d p * hN G (aOf d p) τ y σ S j) :=
        mul_le_mul h1 h2 (mul_nonneg (hy0 j) hhj) (mul_nonneg hR.sOf_pos.le hhv)
    _ = _ := by ring

end Pointwise

/-! ### Moments -/

section Moments

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable {d p : ℕ}

private theorem add4_pow_le' {a b c e : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (he : 0 ≤ e)
    (N : ℕ) : (a + b + c + e) ^ N ≤ 8 ^ N * (a ^ N + b ^ N + c ^ N + e ^ N) := by
  have h1 := add_pow_le_two_pow_mul (add_nonneg (add_nonneg ha hb) hc) he N
  have h2 := add_pow_le_two_pow_mul (add_nonneg ha hb) hc N
  have h3 := add_pow_le_two_pow_mul ha hb N
  have h8 : (8 : ℝ) ^ N = 2 ^ N * 2 ^ N * 2 ^ N := by rw [← mul_pow, ← mul_pow]; norm_num
  have h2N : (1 : ℝ) ≤ 2 ^ N := one_le_pow₀ (by norm_num)
  have hcN := pow_nonneg hc N
  have heN := pow_nonneg he N
  have habN := add_nonneg (pow_nonneg ha N) (pow_nonneg hb N)
  rw [h8]
  calc (a + b + c + e) ^ N ≤ 2 ^ N * ((a + b + c) ^ N + e ^ N) := h1
    _ ≤ 2 ^ N * (2 ^ N * ((a + b) ^ N + c ^ N) + e ^ N) := by gcongr
    _ ≤ 2 ^ N * (2 ^ N * (2 ^ N * (a ^ N + b ^ N) + c ^ N) + e ^ N) := by gcongr
    _ ≤ 2 ^ N * 2 ^ N * 2 ^ N * (a ^ N + b ^ N + c ^ N + e ^ N) := by
        have k1 : c ^ N ≤ 2 ^ N * c ^ N := le_mul_of_one_le_left hcN h2N
        have k2 : e ^ N ≤ 2 ^ N * 2 ^ N * e ^ N :=
          le_mul_of_one_le_left heN (one_le_mul_of_one_le_of_one_le h2N h2N)
        nlinarith [mul_le_mul_of_nonneg_left k1 (pow_nonneg (zero_le_two : (0 : ℝ) ≤ 2) N)]

/-- `E (1 + s ρ_i)^{4n} ≤ 5 · 96^{4n}` for `8n ≤ p` (`s ≤ 3`, F2). -/
theorem one_add_rho_moment_le (hR : TRegime d p) {S : Finset V} {lam : ℝ}
    (hC : CapCtx G d p S lam) {yp ym : V → ℝ} (hyp : InCube (lam * sOf d p) yp)
    (hym : InCube (lam * sOf d p) ym) {v : V} (hv : v ∈ S) {i : V} (hi : i ∈ S) {n : ℕ}
    (hn : 8 * n ≤ p) :
    lawE G p (aOf d p) yp ym S (fun σ => (1 + sOf d p * (hN G (aOf d p) 1 yp σ S v +
      hN G (aOf d p) 1 yp σ S i + hN G (aOf d p) (-1) ym σ S v +
        hN G (aOf d p) (-1) ym σ S i)) ^ (4 * n)) ≤ 5 * 96 ^ (4 * n) := by
  have hs0 := hR.sOf_pos.le
  have hs3 := TRegime.sOf_le_three hR
  have hZ := Zw_pos_cap G hR hC hyp hym
  have hn2 : 2 * (4 * n) ≤ p := by omega
  set N := 4 * n with hNdef
  have hpt : ∀ σ, wt G p (aOf d p) yp ym σ S ≠ 0 →
      (1 + sOf d p * (hN G (aOf d p) 1 yp σ S v + hN G (aOf d p) 1 yp σ S i +
        hN G (aOf d p) (-1) ym σ S v + hN G (aOf d p) (-1) ym σ S i)) ^ N ≤
      2 ^ N * (1 + sOf d p ^ N * 8 ^ N * (hN G (aOf d p) 1 yp σ S v ^ N +
        hN G (aOf d p) 1 yp σ S i ^ N + hN G (aOf d p) (-1) ym σ S v ^ N +
          hN G (aOf d p) (-1) ym σ S i ^ N)) := by
    intro σ hσ
    have h1 := (hN_pos G hσ v).le
    have h2 := (hN_pos G hσ i).le
    have h3 := (hN_pos_minus G hσ v).le
    have h4 := (hN_pos_minus G hσ i).le
    have hρ := add4_pow_le' h1 h2 h3 h4 N
    have hρ0 : 0 ≤ hN G (aOf d p) 1 yp σ S v + hN G (aOf d p) 1 yp σ S i +
        hN G (aOf d p) (-1) ym σ S v + hN G (aOf d p) (-1) ym σ S i := by positivity
    calc _ ≤ 2 ^ N * (1 ^ N + (sOf d p * (hN G (aOf d p) 1 yp σ S v +
            hN G (aOf d p) 1 yp σ S i + hN G (aOf d p) (-1) ym σ S v +
              hN G (aOf d p) (-1) ym σ S i)) ^ N) :=
          add_pow_le_two_pow_mul zero_le_one (mul_nonneg hs0 hρ0) N
      _ ≤ _ := by
          rw [one_pow, mul_pow]
          refine mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) (by positivity)
          calc sOf d p ^ N * (hN G (aOf d p) 1 yp σ S v + hN G (aOf d p) 1 yp σ S i +
              hN G (aOf d p) (-1) ym σ S v + hN G (aOf d p) (-1) ym σ S i) ^ N
              ≤ sOf d p ^ N * (8 ^ N * (hN G (aOf d p) 1 yp σ S v ^ N +
                hN G (aOf d p) 1 yp σ S i ^ N + hN G (aOf d p) (-1) ym σ S v ^ N +
                  hN G (aOf d p) (-1) ym σ S i ^ N)) :=
                mul_le_mul_of_nonneg_left hρ (pow_nonneg hs0 N)
            _ = _ := by ring
  have hm1 := hN_moment_le G hR hC hyp hym (isBranch_plus yp ym) hv hn2
  have hm2 := hN_moment_le G hR hC hyp hym (isBranch_plus yp ym) hi hn2
  have hm3 := hN_moment_le G hR hC hyp hym (isBranch_minus yp ym) hv hn2
  have hm4 := hN_moment_le G hR hC hyp hym (isBranch_minus yp ym) hi hn2
  have hsN : sOf d p ^ N ≤ 3 ^ N := pow_le_pow_left₀ hs0 hs3 N
  calc _ ≤ lawE G p (aOf d p) yp ym S (fun σ => 2 ^ N * (1 + sOf d p ^ N * 8 ^ N *
        (hN G (aOf d p) 1 yp σ S v ^ N + hN G (aOf d p) 1 yp σ S i ^ N +
          hN G (aOf d p) (-1) ym σ S v ^ N + hN G (aOf d p) (-1) ym σ S i ^ N))) :=
        lawE_mono G hpt
    _ = 2 ^ N * (1 + sOf d p ^ N * 8 ^ N *
          (lawE G p (aOf d p) yp ym S (fun σ => hN G (aOf d p) 1 yp σ S v ^ N) +
            lawE G p (aOf d p) yp ym S (fun σ => hN G (aOf d p) 1 yp σ S i ^ N) +
            lawE G p (aOf d p) yp ym S (fun σ => hN G (aOf d p) (-1) ym σ S v ^ N) +
            lawE G p (aOf d p) yp ym S (fun σ => hN G (aOf d p) (-1) ym σ S i ^ N))) := by
        rw [lawE_const_mul, lawE_add, lawE_const_one G hZ, lawE_const_mul, lawE_add, lawE_add,
          lawE_add]
    _ ≤ 2 ^ N * (1 + 3 ^ N * 8 ^ N * (2 ^ N + 2 ^ N + 2 ^ N + 2 ^ N)) := by
        have k1 : 0 ≤ lawE G p (aOf d p) yp ym S (fun σ => hN G (aOf d p) 1 yp σ S v ^ N) :=
          lawE_nonneg G fun σ hσ => pow_nonneg (hN_pos G hσ v).le N
        have k2 : 0 ≤ lawE G p (aOf d p) yp ym S (fun σ => hN G (aOf d p) 1 yp σ S i ^ N) :=
          lawE_nonneg G fun σ hσ => pow_nonneg (hN_pos G hσ i).le N
        have k3 : 0 ≤ lawE G p (aOf d p) yp ym S (fun σ => hN G (aOf d p) (-1) ym σ S v ^ N) :=
          lawE_nonneg G fun σ hσ => pow_nonneg (hN_pos_minus G hσ v).le N
        have k4 : 0 ≤ lawE G p (aOf d p) yp ym S (fun σ => hN G (aOf d p) (-1) ym σ S i ^ N) :=
          lawE_nonneg G fun σ hσ => pow_nonneg (hN_pos_minus G hσ i).le N
        have hsum := add_le_add (add_le_add (add_le_add hm1 hm2) hm3) hm4
        have h38 : sOf d p ^ N * 8 ^ N ≤ 3 ^ N * 8 ^ N :=
          mul_le_mul_of_nonneg_right hsN (by positivity)
        have hk := mul_le_mul h38 hsum (by linarith) (by positivity)
        exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hk) (by positivity)
    _ ≤ 5 * 96 ^ N := by
        have e : (96 : ℝ) ^ N = 2 ^ N * (3 ^ N * 8 ^ N * 2 ^ N) := by
          rw [← mul_pow, ← mul_pow, ← mul_pow]; norm_num
        have h1 : (1 : ℝ) ≤ 3 ^ N * 8 ^ N * 2 ^ N := by
          rw [← mul_pow, ← mul_pow]; exact one_le_pow₀ (by norm_num)
        have h2 : (0 : ℝ) ≤ 2 ^ N := by positivity
        rw [e]
        nlinarith

/-- **Moments of the unmarked weight**: `E W^n ≤ (3·96⁴)^n` for `1 ≤ n`, `8n ≤ p`. -/
theorem rowWt_moment_le (hR : TRegime d p) {S : Finset V} {lam : ℝ} (hC : CapCtx G d p S lam)
    {yp ym : V → ℝ} (hyp : InCube (lam * sOf d p) yp) (hym : InCube (lam * sOf d p) ym)
    {v : V} (hv : v ∈ S) {n : ℕ} (hn1 : 1 ≤ n) (hn : 8 * n ≤ p) :
    lawE G p (aOf d p) yp ym S (fun σ => rowWt G d p yp ym σ S v ^ n) ≤ (3 * 96 ^ 4) ^ n := by
  have ha := hR.aOf_pos
  obtain ⟨-, hda⟩ := TRegime.d_aOf_sq hR
  have hdR := hR.ten_pow_six_le_d
  have hNS : ∀ u : nbhd G S v, (u : V) ∈ S := fun u => (Finset.mem_filter.1 u.2).1
  have hcard : ((Finset.univ : Finset (nbhd G S v)).card : ℝ) ≤ d := by
    rw [Finset.card_univ]
    exact_mod_cast card_nbhd_le G hC.deg S v
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  set ρ : Config V → nbhd G S v → ℝ := fun σ u => 1 + sOf d p * (hN G (aOf d p) 1 yp σ S v +
    hN G (aOf d p) 1 yp σ S u + hN G (aOf d p) (-1) ym σ S v + hN G (aOf d p) (-1) ym σ S u)
    with hρ
  have hpt : ∀ σ, wt G p (aOf d p) yp ym σ S ≠ 0 → rowWt G d p yp ym σ S v ^ (m + 1) ≤
      aOf d p ^ (2 * (m + 1)) * ((Finset.univ : Finset (nbhd G S v)).card : ℝ) ^ m *
        ∑ u : nbhd G S v, ρ σ u ^ (4 * (m + 1)) := by
    intro σ hσ
    have hr : ∀ u : nbhd G S v, (1 + starScale (aOf d p) (rootMat G (aOf d p) 1 yp σ S v)
        (rootMat G (aOf d p) (-1) ym σ S v) (rootSigns G σ S v) u) ^ 4 ≤ ρ σ u ^ 4 := by
      intro u
      have h0 := starScale_nonneg (a := aOf d p) (A := rootMat G (aOf d p) 1 yp σ S v)
        (B := rootMat G (aOf d p) (-1) ym σ S v) (x := rootSigns G σ S v) u
      exact pow_le_pow_left₀ (by linarith) (by
        have := starScale_le_rho G hR hC hyp hym hv hσ u
        simp only [hρ]
        linarith) 4
    have hW : rowWt G d p yp ym σ S v ≤ aOf d p ^ 2 * ∑ u : nbhd G S v, ρ σ u ^ 4 := by
      unfold rowWt
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun u _ => hr u) (sq_nonneg _)
    have hW0 : 0 ≤ rowWt G d p yp ym σ S v := by unfold rowWt; positivity
    have hρ0 : ∀ u, 0 ≤ ρ σ u ^ 4 := fun u => by positivity
    calc rowWt G d p yp ym σ S v ^ (m + 1)
        ≤ (aOf d p ^ 2 * ∑ u : nbhd G S v, ρ σ u ^ 4) ^ (m + 1) := pow_le_pow_left₀ hW0 hW _
      _ = aOf d p ^ (2 * (m + 1)) * (∑ u : nbhd G S v, ρ σ u ^ 4) ^ (m + 1) := by
          rw [mul_pow, ← pow_mul]
      _ ≤ aOf d p ^ (2 * (m + 1)) * (((Finset.univ : Finset (nbhd G S v)).card : ℝ) ^ m *
            ∑ u : nbhd G S v, (ρ σ u ^ 4) ^ (m + 1)) :=
          mul_le_mul_of_nonneg_left (pow_sum_le_card_mul_sum_pow (fun u _ => hρ0 u) m)
            (by positivity)
      _ = _ := by
          simp only [← pow_mul]
          ring
  have hmom : ∀ u : nbhd G S v, lawE G p (aOf d p) yp ym S (fun σ => ρ σ u ^ (4 * (m + 1))) ≤
      5 * 96 ^ (4 * (m + 1)) := fun u =>
    one_add_rho_moment_le G hR hC hyp hym hv (hNS u) hn
  have hk : ((Finset.univ : Finset (nbhd G S v)).card : ℝ) * aOf d p ^ 2 ≤ 1 / 2 := by
    calc ((Finset.univ : Finset (nbhd G S v)).card : ℝ) * aOf d p ^ 2 ≤ d * aOf d p ^ 2 :=
          mul_le_mul_of_nonneg_right hcard (sq_nonneg _)
      _ ≤ 1 / 2 := hda
  have hc0 : (0 : ℝ) ≤ ((Finset.univ : Finset (nbhd G S v)).card : ℝ) * aOf d p ^ 2 :=
    by positivity
  calc lawE G p (aOf d p) yp ym S (fun σ => rowWt G d p yp ym σ S v ^ (m + 1))
      ≤ lawE G p (aOf d p) yp ym S (fun σ => aOf d p ^ (2 * (m + 1)) *
          ((Finset.univ : Finset (nbhd G S v)).card : ℝ) ^ m *
            ∑ u : nbhd G S v, ρ σ u ^ (4 * (m + 1))) := lawE_mono G hpt
    _ = aOf d p ^ (2 * (m + 1)) * ((Finset.univ : Finset (nbhd G S v)).card : ℝ) ^ m *
          ∑ u : nbhd G S v, lawE G p (aOf d p) yp ym S (fun σ => ρ σ u ^ (4 * (m + 1))) := by
        rw [lawE_const_mul, lawE_sum]
    _ ≤ aOf d p ^ (2 * (m + 1)) * ((Finset.univ : Finset (nbhd G S v)).card : ℝ) ^ m *
          ∑ _u : nbhd G S v, 5 * (96 : ℝ) ^ (4 * (m + 1)) := by
        gcongr with u
        exact hmom u
    _ = 5 * (((Finset.univ : Finset (nbhd G S v)).card : ℝ) * aOf d p ^ 2) ^ (m + 1) *
          ((96 : ℝ) ^ 4) ^ (m + 1) := by
        rw [Finset.sum_const, nsmul_eq_mul, pow_mul, pow_mul, mul_pow]
        ring
    _ ≤ 5 * (1 / 2) ^ (m + 1) * ((96 : ℝ) ^ 4) ^ (m + 1) := by
        gcongr
    _ ≤ (3 * 96 ^ 4) ^ (m + 1) := by
        rw [mul_pow (3 : ℝ)]
        have h6 : (5 : ℝ) * (1 / 2) ^ (m + 1) ≤ 3 ^ (m + 1) := by
          have h1 : (5 : ℝ) ≤ 6 ^ (m + 1) := by
            calc (5 : ℝ) ≤ 6 ^ 1 := by norm_num
              _ ≤ 6 ^ (m + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
          have e : (6 : ℝ) ^ (m + 1) * (1 / 2) ^ (m + 1) = 3 ^ (m + 1) := by
            rw [← mul_pow]; norm_num
          rw [← e]
          exact mul_le_mul_of_nonneg_right h1 (by positivity)
        exact mul_le_mul_of_nonneg_right h6 (by positivity)

/-- `E R₊² ≤ 64`, `R₊ = a² Σ_N (G⁺_vj)²` (and the same for `R₋`). -/
theorem rowR_sq_le (hR : TRegime d p) {S : Finset V} {lam : ℝ} (hC : CapCtx G d p S lam)
    {yp ym : V → ℝ} (hyp : InCube (lam * sOf d p) yp) (hym : InCube (lam * sOf d p) ym)
    {τ : ℝ} {y : V → ℝ} (hb : IsBranch yp ym τ y) {v : V} (hv : v ∈ S) (hp8 : 8 ≤ p) :
    lawE G p (aOf d p) yp ym S (fun σ => (aOf d p ^ 2 *
      ∑ j ∈ nbhd G S v, greenP G (aOf d p) τ y σ S v j ^ 2) ^ 2) ≤ 8 ^ 2 := by
  have hκ := hR.d_mul_kappa_le
  have hcard : ((nbhd G S v).card : ℝ) ≤ d := by
    have := card_nbhd_le G hC.deg S v
    rw [Fintype.card_coe] at this
    exact_mod_cast this
  have hNS : nbhd G S v ⊆ S := Finset.filter_subset _ _
  have hpt : ∀ σ, wt G p (aOf d p) yp ym σ S ≠ 0 →
      (aOf d p ^ 2 * ∑ j ∈ nbhd G S v, greenP G (aOf d p) τ y σ S v j ^ 2) ^ 2 ≤
        (aOf d p ^ 2 * sOf d p ^ 2) ^ 2 *
          (hN G (aOf d p) τ y σ S v * ∑ j ∈ nbhd G S v, hN G (aOf d p) τ y σ S j) ^ 2 := by
    intro σ hσ
    have hsum : ∑ j ∈ nbhd G S v, greenP G (aOf d p) τ y σ S v j ^ 2 ≤
        sOf d p ^ 2 * (hN G (aOf d p) τ y σ S v * ∑ j ∈ nbhd G S v, hN G (aOf d p) τ y σ S j) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      rw [← Finset.sum_coe_sort (nbhd G S v), ← Finset.sum_coe_sort (nbhd G S v)]
      exact Finset.sum_le_sum fun j _ => greenP_row_sq_le G hR hC hyp hym hb hv hσ j
    have h0 : 0 ≤ aOf d p ^ 2 * ∑ j ∈ nbhd G S v, greenP G (aOf d p) τ y σ S v j ^ 2 := by
      positivity
    calc _ ≤ (aOf d p ^ 2 * (sOf d p ^ 2 * (hN G (aOf d p) τ y σ S v *
          ∑ j ∈ nbhd G S v, hN G (aOf d p) τ y σ S j))) ^ 2 :=
          pow_le_pow_left₀ h0 (mul_le_mul_of_nonneg_left hsum (sq_nonneg _)) 2
      _ = _ := by ring
  calc _ ≤ lawE G p (aOf d p) yp ym S (fun σ => (aOf d p ^ 2 * sOf d p ^ 2) ^ 2 *
        (hN G (aOf d p) τ y σ S v * ∑ j ∈ nbhd G S v, hN G (aOf d p) τ y σ S j) ^ 2) :=
        lawE_mono G hpt
    _ = (aOf d p ^ 2 * sOf d p ^ 2) ^ 2 * lawE G p (aOf d p) yp ym S (fun σ =>
          (hN G (aOf d p) τ y σ S v * ∑ j ∈ nbhd G S v, hN G (aOf d p) τ y σ S j) ^ 2) :=
        lawE_const_mul G _ _
    _ ≤ (aOf d p ^ 2 * sOf d p ^ 2) ^ 2 * (2 * ((nbhd G S v).card : ℝ) ^ 2 * 4 ^ 2) :=
        mul_le_mul_of_nonneg_left
          (hN_mul_sum_moment_le G hR hC hyp hym hb hv hNS (by omega)) (by positivity)
    _ = 32 * (((nbhd G S v).card : ℝ) * (aOf d p ^ 2 * sOf d p ^ 2)) ^ 2 := by ring
    _ ≤ 32 * ((d : ℝ) * (aOf d p ^ 2 * sOf d p ^ 2)) ^ 2 := by gcongr
    _ ≤ 32 * (101 / 100) ^ 2 := by gcongr
    _ ≤ 8 ^ 2 := by norm_num

end Moments

/-! ### Interpolation and the two forms of CR-X5 -/

section Final

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem lawE_mul_le_sqrt {p : ℕ} {a : ℝ} {yp ym : V → ℝ} {S : Finset V}
    (U W : Config V → ℝ) :
    lawE G p a yp ym S (fun σ => U σ * W σ) ≤
      Real.sqrt (lawE G p a yp ym S (fun σ => U σ ^ 2)) *
        Real.sqrt (lawE G p a yp ym S (fun σ => W σ ^ 2)) := by
  have h : lawE G p a yp ym S (fun σ => U σ * W σ) ^ 2 ≤
      lawE G p a yp ym S (fun σ => U σ ^ 2) * lawE G p a yp ym S (fun σ => W σ ^ 2) :=
    wavg_mul_sq_le (fun σ => wt_nonneg G σ) U W
  rw [← Real.sqrt_mul (lawE_nonneg G fun σ _ => sq_nonneg (U σ))]
  exact (le_abs_self _).trans (Real.abs_le_sqrt h)

private theorem abs_sum_mul_le_sqrt {ι : Type*} (s : Finset ι) (f g : ι → ℝ) :
    |∑ i ∈ s, f i * g i| ≤ Real.sqrt (∑ i ∈ s, f i ^ 2) * Real.sqrt (∑ i ∈ s, g i ^ 2) := by
  refine abs_le.mpr ⟨?_, Real.sum_mul_le_sqrt_mul_sqrt s f g⟩
  have h := Real.sum_mul_le_sqrt_mul_sqrt s (fun i => -f i) g
  simp only [neg_mul, Finset.sum_neg_distrib, neg_sq] at h
  linarith

/-- `32 kIL d ≤ p` for large `d`. -/
theorem eventually_kIL32 : Eventually fun _ _ d p _ => 32 * kIL d ≤ p := by
  refine ((eventually_log_le 1000).and (eventually_le_log 8)).mono ?_
  rintro c₀ κ₀ d p h ⟨h1, h2⟩
  have hk : (kIL d : ℝ) < 30 * Real.log d + 1 := Nat.ceil_lt_add_one (by linarith)
  have : ((32 * kIL d : ℕ) : ℝ) ≤ p := by
    push_cast
    linarith
  exact_mod_cast this

/-- The interpolated weighted row energies: `E[W^m R₊] ≤ e² (3·96⁴)^m λ_r` for `m = 1, 2`. -/
theorem rowWt_mul_R_le {d p : ℕ} (hR : TRegime d p) (hk : 32 * kIL d ≤ p) {S : Finset V}
    {lam : ℝ} (hC : CapCtx G d p S lam) {yp ym : V → ℝ} (hyp : InCube (lam * sOf d p) yp)
    (hym : InCube (lam * sOf d p) ym) {v : V} (hv : v ∈ S) {lr : ℝ} (hvl : vth d ≤ lr)
    (hS1 : incRowE G d p yp ym S v 1 yp / d ≤ lr) {m : ℕ} (hm1 : 1 ≤ m) (hm2 : m ≤ 2) :
    lawE G p (aOf d p) yp ym S (fun σ => (aOf d p ^ 2 *
        ∑ j ∈ nbhd G S v, greenP G (aOf d p) 1 yp σ S v j ^ 2) *
          rowWt G d p yp ym σ S v ^ m) ≤
      Real.exp 2 * (3 * 96 ^ 4) ^ m * lr := by
  have hdR := hR.ten_pow_six_le_d
  have hd0 : (0 : ℝ) < d := lt_of_lt_of_le (by norm_num) hdR
  have hd3 : 3 ≤ d := le_trans (by norm_num) hR.ten_pow_six_le_nat
  have hp8 : 8 ≤ p := le_trans (by norm_num) hR.hp
  obtain ⟨-, hda⟩ := TRegime.d_aOf_sq hR
  have hZ := Zw_pos_cap G hR hC hyp hym
  have hθ : 0 < vth d := by unfold vth; positivity
  have hS0 : 0 ≤ incRowE G d p yp ym S v 1 yp :=
    Finset.sum_nonneg fun j _ => lawE_nonneg G fun σ _ => sq_nonneg _
  have hEX : lawE G p (aOf d p) yp ym S (fun σ => aOf d p ^ 2 *
      ∑ j ∈ nbhd G S v, greenP G (aOf d p) 1 yp σ S v j ^ 2) ≤ lr := by
    rw [lawE_const_mul, lawE_sum]
    have h1 : incRowE G d p yp ym S v 1 yp ≤ d * lr := by
      rwa [div_le_iff₀ hd0, mul_comm] at hS1
    have h2 : aOf d p ^ 2 * incRowE G d p yp ym S v 1 yp ≤ aOf d p ^ 2 * (d * lr) :=
      mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
    have hlr : 0 ≤ lr := hθ.le.trans hvl
    have h3 : aOf d p ^ 2 * (d * lr) ≤ lr := by nlinarith
    exact h2.trans h3
  have hk1 : 1 ≤ kIL d := one_le_kIL hd3
  have hmom : lawE G p (aOf d p) yp ym S (fun σ => (rowWt G d p yp ym σ S v ^ m) ^ (2 * kIL d)) ≤
      ((3 * 96 ^ 4) ^ m) ^ (2 * kIL d) := by
    simp only [← pow_mul]
    exact rowWt_moment_le G hR hC hyp hym hv (by nlinarith) (by nlinarith)
  exact lawE_mul_le_vth G hd3 hZ (fun σ _ => by positivity)
    (fun σ _ => by unfold rowWt; positivity) hvl (by norm_num) (by
      have h8 : (8 : ℝ) ≤ d := by linarith
      exact h8.trans (le_self_pow₀ (by linarith) (by norm_num))) (by positivity) hEX
      (rowR_sq_le G hR hC hyp hym (isBranch_plus yp ym) hv hp8)
      hmom

end Final

private theorem sq_cs_aux {ι : Type*} (s : Finset ι) {a : ℝ} (ha : 0 ≤ a) (f g : ι → ℝ) :
    a ^ 2 * |∑ i ∈ s, f i * g i| ≤
      Real.sqrt (a ^ 2 * ∑ i ∈ s, f i ^ 2) * Real.sqrt (a ^ 2 * ∑ i ∈ s, g i ^ 2) := by
  rw [Real.sqrt_mul (sq_nonneg a), Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha]
  have h := abs_sum_mul_le_sqrt s f g
  calc a ^ 2 * |∑ i ∈ s, f i * g i| ≤
        a ^ 2 * (Real.sqrt (∑ i ∈ s, f i ^ 2) * Real.sqrt (∑ i ∈ s, g i ^ 2)) :=
        mul_le_mul_of_nonneg_left h (sq_nonneg a)
    _ = _ := by ring

private theorem exp_one_le_three : Real.exp 1 ≤ 3 := by
  have := Real.exp_one_lt_d9
  linarith

/-- **CR-X5, split form** (CR3, source lines 1170–1190). See the module docstring. -/
theorem row_x5_split : ∃ C : ℝ, 0 < C ∧ Eventually fun _ _ d p _ =>
    ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
      (S : Finset V) (lam : ℝ) (yp ym : V → ℝ) (v : V), CapCtx G d p S lam →
      InCube (lam * sOf d p) yp → InCube (lam * sOf d p) ym → v ∈ S →
      ∀ lr rr : ℝ, vth d ≤ lr → lr ≤ rr →
        incRowE G d p yp ym S v 1 yp / d ≤ lr → incRowE G d p yp ym S v (-1) ym / d ≤ rr →
        rowX5 G d p yp ym S v ≤ C * Real.sqrt (lr * rr) := by
  refine ⟨12 * (3 * 96 ^ 4), by positivity, ((eventually_regime 1).and eventually_kIL32).mono ?_⟩
  rintro c₀ κ₀ d p h ⟨⟨hR, -, -⟩, hk⟩ V _ _ G _ S lam yp ym v hC hyp hym hv lr rr hvl hlrr hS1
    hS2
  have ha := hR.aOf_pos
  have hdR := hR.ten_pow_six_le_d
  have hd0 : (0 : ℝ) < d := lt_of_lt_of_le (by norm_num) hdR
  obtain ⟨-, hda⟩ := TRegime.d_aOf_sq hR
  have hθ : 0 < vth d := by unfold vth; positivity
  have hlr : 0 ≤ lr := hθ.le.trans hvl
  have hrr : 0 ≤ rr := hlr.trans hlrr
  set B : ℝ := 3 * 96 ^ 4 with hB
  have hB0 : 0 < B := by positivity
  set Rp : Config V → ℝ := fun σ =>
    aOf d p ^ 2 * ∑ j ∈ nbhd G S v, greenP G (aOf d p) 1 yp σ S v j ^ 2 with hRp
  set Rm : Config V → ℝ := fun σ =>
    aOf d p ^ 2 * ∑ j ∈ nbhd G S v, greenP G (aOf d p) (-1) ym σ S v j ^ 2 with hRm
  have hRp0 : ∀ σ, 0 ≤ Rp σ := fun σ => by simp only [hRp]; positivity
  have hRm0 : ∀ σ, 0 ≤ Rm σ := fun σ => by simp only [hRm]; positivity
  have hW0 : ∀ σ, 0 ≤ rowWt G d p yp ym σ S v := fun σ => by unfold rowWt; positivity
  -- pointwise
  have hpt : ∀ σ, wt G p (aOf d p) yp ym σ S ≠ 0 →
      rowWt G d p yp ym σ S v * (aOf d p ^ 2 *
        |∑ j ∈ nbhd G S v, greenP G (aOf d p) 1 yp σ S v j *
          (greenP G (aOf d p) 1 yp σ S v j - greenP G (aOf d p) (-1) ym σ S v j)|) ≤
        Rp σ * rowWt G d p yp ym σ S v ^ 1 +
          (rowWt G d p yp ym σ S v * Real.sqrt (Rp σ)) * Real.sqrt (Rm σ) := by
    intro σ _
    have hcs := sq_cs_aux (nbhd G S v) ha.le (fun j => greenP G (aOf d p) 1 yp σ S v j)
      (fun j => greenP G (aOf d p) (-1) ym σ S v j)
    have hsplit : ∑ j ∈ nbhd G S v, greenP G (aOf d p) 1 yp σ S v j *
          (greenP G (aOf d p) 1 yp σ S v j - greenP G (aOf d p) (-1) ym σ S v j) =
        ∑ j ∈ nbhd G S v, greenP G (aOf d p) 1 yp σ S v j ^ 2 -
          ∑ j ∈ nbhd G S v, greenP G (aOf d p) 1 yp σ S v j *
            greenP G (aOf d p) (-1) ym σ S v j := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hx : 0 ≤ ∑ j ∈ nbhd G S v, greenP G (aOf d p) 1 yp σ S v j ^ 2 := by positivity
    have habs : aOf d p ^ 2 * |∑ j ∈ nbhd G S v, greenP G (aOf d p) 1 yp σ S v j *
          (greenP G (aOf d p) 1 yp σ S v j - greenP G (aOf d p) (-1) ym σ S v j)| ≤
        Rp σ + Real.sqrt (Rp σ) * Real.sqrt (Rm σ) := by
      rw [hsplit]
      have h1 := abs_sub_le_add (∑ j ∈ nbhd G S v, greenP G (aOf d p) 1 yp σ S v j ^ 2)
        (∑ j ∈ nbhd G S v, greenP G (aOf d p) 1 yp σ S v j * greenP G (aOf d p) (-1) ym σ S v j)
      rw [abs_of_nonneg hx] at h1
      have h2 := mul_le_mul_of_nonneg_left h1 (sq_nonneg (aOf d p))
      simp only [hRp, hRm]
      nlinarith [hcs]
    calc _ ≤ rowWt G d p yp ym σ S v * (Rp σ + Real.sqrt (Rp σ) * Real.sqrt (Rm σ)) :=
          mul_le_mul_of_nonneg_left habs (hW0 σ)
      _ = _ := by ring
  -- the two expectations
  have hE1 := rowWt_mul_R_le G hR hk hC hyp hym hv hvl hS1 (m := 1) le_rfl (by norm_num)
  have hE2 := rowWt_mul_R_le G hR hk hC hyp hym hv hvl hS1 (m := 2) (by norm_num) le_rfl
  have hERm : lawE G p (aOf d p) yp ym S (fun σ => Real.sqrt (Rm σ) ^ 2) ≤ rr := by
    have e : lawE G p (aOf d p) yp ym S (fun σ => Real.sqrt (Rm σ) ^ 2) =
        aOf d p ^ 2 * incRowE G d p yp ym S v (-1) ym := by
      rw [lawE_congr G fun σ _ => Real.sq_sqrt (hRm0 σ)]
      simp only [hRm]
      rw [lawE_const_mul, lawE_sum]
      rfl
    rw [e]
    have h1 : incRowE G d p yp ym S v (-1) ym ≤ d * rr := by
      rwa [div_le_iff₀ hd0, mul_comm] at hS2
    have h2 := mul_le_mul_of_nonneg_left h1 (sq_nonneg (aOf d p))
    nlinarith
  have hU2 : lawE G p (aOf d p) yp ym S (fun σ =>
      (rowWt G d p yp ym σ S v * Real.sqrt (Rp σ)) ^ 2) ≤ Real.exp 2 * B ^ 2 * lr := by
    have e : lawE G p (aOf d p) yp ym S (fun σ =>
        (rowWt G d p yp ym σ S v * Real.sqrt (Rp σ)) ^ 2) =
        lawE G p (aOf d p) yp ym S (fun σ => Rp σ * rowWt G d p yp ym σ S v ^ 2) :=
      lawE_congr G fun σ _ => by rw [mul_pow, Real.sq_sqrt (hRp0 σ)]; ring
    rw [e]
    exact hE2
  have hCS := lawE_mul_le_sqrt G (p := p) (a := aOf d p) (yp := yp) (ym := ym) (S := S)
    (fun σ => rowWt G d p yp ym σ S v * Real.sqrt (Rp σ)) (fun σ => Real.sqrt (Rm σ))
  have hmain : rowX5 G d p yp ym S v ≤ Real.exp 2 * B ^ 1 * lr +
      Real.sqrt (Real.exp 2 * B ^ 2 * lr) * Real.sqrt rr := by
    unfold rowX5
    refine (lawE_mono G hpt).trans ?_
    rw [lawE_add]
    refine add_le_add hE1 (hCS.trans ?_)
    exact mul_le_mul (Real.sqrt_le_sqrt hU2) (Real.sqrt_le_sqrt hERm) (Real.sqrt_nonneg _)
      (Real.sqrt_nonneg _)
  -- constants
  have he := exp_one_le_three
  have he0 := Real.exp_pos 1
  have he2 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
  have hsq : Real.sqrt (Real.exp 2 * B ^ 2 * lr) = Real.exp 1 * B * Real.sqrt lr := by
    rw [he2, show Real.exp 1 ^ 2 * B ^ 2 * lr = (Real.exp 1 * B) ^ 2 * lr by ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  have hlrs : lr ≤ Real.sqrt (lr * rr) := by
    calc lr = Real.sqrt (lr * lr) := (Real.sqrt_mul_self hlr).symm
      _ ≤ Real.sqrt (lr * rr) := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hlrr hlr)
  have hmul : Real.sqrt lr * Real.sqrt rr = Real.sqrt (lr * rr) := (Real.sqrt_mul hlr rr).symm
  rw [hsq, pow_one, mul_assoc (Real.exp 1 * B), hmul] at hmain
  have hs0 := Real.sqrt_nonneg (lr * rr)
  have hE2' : Real.exp 2 ≤ 9 := by rw [he2]; nlinarith
  calc rowX5 G d p yp ym S v ≤ Real.exp 2 * B * lr + Real.exp 1 * B * Real.sqrt (lr * rr) := hmain
    _ ≤ 9 * B * Real.sqrt (lr * rr) + 3 * B * Real.sqrt (lr * rr) := by
        gcongr
    _ = 12 * B * Real.sqrt (lr * rr) := by ring

/-- **CR-X5, difference form** (CR3′, `docs/tight/DR1_CHECK.md` §3). See the module docstring. -/
theorem row_x5_diff : ∃ C : ℝ, 0 < C ∧ Eventually fun _ _ d p _ =>
    ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
      (S : Finset V) (lam : ℝ) (yp ym : V → ℝ) (v : V), CapCtx G d p S lam →
      InCube (lam * sOf d p) yp → InCube (lam * sOf d p) ym → v ∈ S →
      ∀ lr rd : ℝ, vth d ≤ lr → vth d ≤ rd →
        incRowE G d p yp ym S v 1 yp / d ≤ lr → diffRowE G d p yp ym S v / d ≤ rd →
        rowX5 G d p yp ym S v ≤ C * Real.sqrt (lr * rd) := by
  refine ⟨3 * (3 * 96 ^ 4), by positivity, ((eventually_regime 1).and eventually_kIL32).mono ?_⟩
  rintro c₀ κ₀ d p h ⟨⟨hR, -, -⟩, hk⟩ V _ _ G _ S lam yp ym v hC hyp hym hv lr rd hvl hvr hS1
    hD
  have ha := hR.aOf_pos
  have hdR := hR.ten_pow_six_le_d
  have hd0 : (0 : ℝ) < d := lt_of_lt_of_le (by norm_num) hdR
  obtain ⟨-, hda⟩ := TRegime.d_aOf_sq hR
  have hθ : 0 < vth d := by unfold vth; positivity
  have hlr : 0 ≤ lr := hθ.le.trans hvl
  have hrd : 0 ≤ rd := hθ.le.trans hvr
  set B : ℝ := 3 * 96 ^ 4 with hB
  have hB0 : 0 < B := by positivity
  set Rp : Config V → ℝ := fun σ =>
    aOf d p ^ 2 * ∑ j ∈ nbhd G S v, greenP G (aOf d p) 1 yp σ S v j ^ 2 with hRp
  set Dl : Config V → ℝ := fun σ => aOf d p ^ 2 * ∑ j ∈ nbhd G S v,
    (greenP G (aOf d p) 1 yp σ S v j - greenP G (aOf d p) (-1) ym σ S v j) ^ 2 with hDl
  have hRp0 : ∀ σ, 0 ≤ Rp σ := fun σ => by simp only [hRp]; positivity
  have hDl0 : ∀ σ, 0 ≤ Dl σ := fun σ => by simp only [hDl]; positivity
  have hW0 : ∀ σ, 0 ≤ rowWt G d p yp ym σ S v := fun σ => by unfold rowWt; positivity
  have hpt : ∀ σ, wt G p (aOf d p) yp ym σ S ≠ 0 →
      rowWt G d p yp ym σ S v * (aOf d p ^ 2 *
        |∑ j ∈ nbhd G S v, greenP G (aOf d p) 1 yp σ S v j *
          (greenP G (aOf d p) 1 yp σ S v j - greenP G (aOf d p) (-1) ym σ S v j)|) ≤
        (rowWt G d p yp ym σ S v * Real.sqrt (Rp σ)) * Real.sqrt (Dl σ) := by
    intro σ _
    have hcs := sq_cs_aux (nbhd G S v) ha.le (fun j => greenP G (aOf d p) 1 yp σ S v j)
      (fun j => greenP G (aOf d p) 1 yp σ S v j - greenP G (aOf d p) (-1) ym σ S v j)
    calc _ ≤ rowWt G d p yp ym σ S v * (Real.sqrt (Rp σ) * Real.sqrt (Dl σ)) :=
          mul_le_mul_of_nonneg_left hcs (hW0 σ)
      _ = _ := by ring
  have hE2 := rowWt_mul_R_le G hR hk hC hyp hym hv hvl hS1 (m := 2) (by norm_num) le_rfl
  have hEDl : lawE G p (aOf d p) yp ym S (fun σ => Real.sqrt (Dl σ) ^ 2) ≤ rd := by
    have e : lawE G p (aOf d p) yp ym S (fun σ => Real.sqrt (Dl σ) ^ 2) =
        aOf d p ^ 2 * diffRowE G d p yp ym S v := by
      rw [lawE_congr G fun σ _ => Real.sq_sqrt (hDl0 σ)]
      simp only [hDl]
      rw [lawE_const_mul, lawE_sum]
      rfl
    rw [e]
    have h1 : diffRowE G d p yp ym S v ≤ d * rd := by
      rwa [div_le_iff₀ hd0, mul_comm] at hD
    have h2 := mul_le_mul_of_nonneg_left h1 (sq_nonneg (aOf d p))
    nlinarith
  have hU2 : lawE G p (aOf d p) yp ym S (fun σ =>
      (rowWt G d p yp ym σ S v * Real.sqrt (Rp σ)) ^ 2) ≤ Real.exp 2 * B ^ 2 * lr := by
    have e : lawE G p (aOf d p) yp ym S (fun σ =>
        (rowWt G d p yp ym σ S v * Real.sqrt (Rp σ)) ^ 2) =
        lawE G p (aOf d p) yp ym S (fun σ => Rp σ * rowWt G d p yp ym σ S v ^ 2) :=
      lawE_congr G fun σ _ => by rw [mul_pow, Real.sq_sqrt (hRp0 σ)]; ring
    rw [e]
    exact hE2
  have hCS := lawE_mul_le_sqrt G (p := p) (a := aOf d p) (yp := yp) (ym := ym) (S := S)
    (fun σ => rowWt G d p yp ym σ S v * Real.sqrt (Rp σ)) (fun σ => Real.sqrt (Dl σ))
  have hmain : rowX5 G d p yp ym S v ≤
      Real.sqrt (Real.exp 2 * B ^ 2 * lr) * Real.sqrt rd := by
    unfold rowX5
    refine (lawE_mono G hpt).trans (hCS.trans ?_)
    exact mul_le_mul (Real.sqrt_le_sqrt hU2) (Real.sqrt_le_sqrt hEDl) (Real.sqrt_nonneg _)
      (Real.sqrt_nonneg _)
  have he := exp_one_le_three
  have he2 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
  have hsq : Real.sqrt (Real.exp 2 * B ^ 2 * lr) = Real.exp 1 * B * Real.sqrt lr := by
    rw [he2, show Real.exp 1 ^ 2 * B ^ 2 * lr = (Real.exp 1 * B) ^ 2 * lr by ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  have hmul : Real.sqrt lr * Real.sqrt rd = Real.sqrt (lr * rd) := (Real.sqrt_mul hlr rd).symm
  rw [hsq, mul_assoc, hmul] at hmain
  have hs0 := Real.sqrt_nonneg (lr * rd)
  calc rowX5 G d p yp ym S v ≤ Real.exp 1 * B * Real.sqrt (lr * rd) := hmain
    _ ≤ 3 * B * Real.sqrt (lr * rd) := by gcongr

end SecC

end BiluLinial.Tight
