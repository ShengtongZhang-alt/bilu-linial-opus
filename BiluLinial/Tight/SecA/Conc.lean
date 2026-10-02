/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecA.Transfer
public import BiluLinial.Tight.SecA.Star
public import BiluLinial.Tight.SecA.ConcAux

/-!
# Bias, row bound, second moments and the core kernel (nodes `A-C1a`, `A-ROW`, `A-SM2`,
`A-WHITEN`, `A-WLE`, `A-CK`, `A-C3a`, `A-C3b`)

Source lines 369–442 (Lemma "Bias and reference concentration", first half); AUDIT-A §2.9–§2.11.
Constants are absolute (`∃ C` before `d, p`); `ρ` is any bound on the first-mean deficits
(`DefLe`), `b₀ = ε + p⁴/d + 1/d`. `N_R = 𝖱 f₁`, `N_G = 𝖦 f₁`, `f₁ = (tr A - q_A) α^{p-1} β^p`.

* `A-C1a` (C1, first part): `|E_{ν_K}(N_R - N_G)| ≤ C (p⁴/d) F_H`, both branches, `C = 10⁸`.
  Proof (`CapPoint.bias_gen`, `SecA/ConcAux.lean`): `A-TRANSR` on `f₁` with sup majorant
  `1 + tr A` (`A-E5`, `λ = √b`) and endpoint majorant `(1 + tr A)·2h_v ≥ (1 + tr A) τ⁺`, weights
  `5pλ_i`, `λ_i = a(2√(G⁺_vvG⁺_ii) + 2√(G⁻_vvG⁻_ii))` (`A-MAJ` and (F1)); all retained grades
  `≤ 10e²·41⁴/4 · p⁴/d`, the remainder `≤ 3e^{-p}/d` (REG).
* (C1, second part) `N_G ≥ f_G w ≥ 0` is T.COV (`gaussE_NG_ge_whitened`, `Tight/Tools/Cov.lean`).
* `A-ROW`: `a² Σ_{i ∼ v} E (G^±_vi)² ≤ C (ρ + b₀)`. Proof: (C3), `A-C1a`, `N_G ≥ 0`,
  `E G_vv G_ii ≤ y_v y_i (1 + 2ε)²` (Cauchy–Schwarz, (M1)), `-D_v E h_v ≤ -D_v (1 - ρ)`,
  `1 - D_v + L_v = C_v ≤ 1/d`, `D_v ≤ 2`, `L_v ≤ 1`.
* `A-SM2` (explicit): `E (h^±_i - 1)² ≤ 5ε + 2ρ` ((M1) with `k = 2`).
* `A-WHITEN` (source l. 413–424, the core-constant numerator `wΦ` and the whitened covariance
  bound; AUDIT-A §2.11 first step, AUDIT-C T.TRC):
  `E_H w ≤ E_{ν_K}[N_G]/F_H + C (p⁴/d)(E_H w + d^{-10})`.
  Proof (`CapPoint.whiten_gen`, `SecA/ConcAux.lean`): `E_H w = E_{ν_K}[w 𝖱Φ]/F_H` (`A-RET` with
  `R = wΦ`), `A-TRANSR` on `wΦ` (T.IL on every retained grade with `m = E_H w + ϑ`,
  `ϑ = d^{-10}`, `K = ⌊log d/300⌋`; the remainder `≤ 2e^{-p}/d ≤ (p⁴/d) ϑ`), and `N_G ≥ f_G w`
  (T.COV). `C = 3·10⁶ e^{12002}`. (`A-TRANS` itself does not suffice: its grade-`≥ 2` bound is
  absolute, `2e² M_E (dL⁴)²` with `M_E ≥ ‖w‖_n` for all `n ≤ p/2`, not relative to `E_H w`.)
* `A-WLE`: `E_H w ≤ 1` (`w ≤ tr A ≤ (a² y_v/D_v) Σ_{i ∈ N} G_ii`, cap and `L_v/D_v ≤ 0.51`).
* `A-CK`: `E_H w ≤ C (ρ + b₀)`, both branches (`A-WHITEN`, `A-C1a`, (C3) dropping the row term,
  `A-WLE` for the term `C (p⁴/d) E_H w`).
* `A-C3a`: `T_A 1{μ ≤ 1} ≤ 2w` (pointwise, `A ⪰ 0`), and `E_H[T_A 1{μ > 1}] ≤ e^{-p/10}`:
  `T_A ≤ μ² ≤ U²`, `U = (a² y_v/D_v) Σ_{i ∈ N} G_ii ≥ μ` (Schur order), `‖U‖_k ≤ U₀ (1 + 2ε) ≤ 0.52`
  for `k = ⌊p/4⌋` (Jensen, (M1), `A-PARP`), so `E[U² 1{U > 1}] ≤ E U^k ≤ 0.52^k ≤ e^{-p/10}`.
* `A-C3b`: `E_H Θ ≤ C (ρ + b₀)`, `Θ = tr(A² + B²)` (`A-CK`, `A-C3a`, `e^{-p/10} ≤ 1/d ≤ b₀`).

Small cases: `y_v = 0` gives `A = B = 0`, `f₁ = 0`, `w = Θ = 0` and `G_v· = 0`, so every bound is
trivial; the statements are monotone in `ρ`.
-/

@[expose] public section

universe u

namespace BiluLinial.Tight

open Matrix

namespace SecA


section Star

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- `rowNum = starF` (the coefficient `(p : ℝ) - 1 = ((p - 1 : ℕ) : ℝ)` for `p ≥ 1`). -/
theorem rowNum_eq_starF {p : ℕ} (hp : 1 ≤ p) (A B : Matrix ι ι ℝ) :
    rowNum p A B = starF p A B := by
  funext x
  rw [rowNum, starF, Nat.cast_sub hp, Nat.cast_one]

omit [DecidableEq ι] in
/-- `f₁ = (tr A - q_A) starG`. -/
theorem f1Obs_eq (p : ℕ) (A B : Matrix ι ι ℝ) :
    f1Obs p A B = fun x => (A.trace - qForm A x) * starG p A B x := by
  funext x
  simp only [f1Obs, starG, clipProd]
  ring

/-- `N_G = 2 𝖦 F` (T.GIBP2). -/
theorem gaussE_f1Obs_eq {A B : Matrix ι ι ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef) {p : ℕ}
    (hp : 3 ≤ p) : gaussE (f1Obs p A B) = 2 * gaussE (rowNum p A B) := by
  rw [rowNum_eq_starF (by omega), two_mul_gaussE_starF hA hB hp, f1Obs_eq]

/-- `𝖦 F ≥ 0` (T.COV and T.GIBP2). -/
theorem gaussE_rowNum_nonneg {A B : Matrix ι ι ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    {p : ℕ} (hp : 3 ≤ p) : 0 ≤ gaussE (rowNum p A B) := by
  have h := gaussE_NG_nonneg hA hB p
  rw [← f1Obs_eq, gaussE_f1Obs_eq hA hB hp] at h
  linarith

omit [DecidableEq ι] in
theorem radE_starPhi_nonneg (p : ℕ) (A B : Matrix ι ι ℝ) : 0 ≤ radE (starPhi p A B) :=
  MeasureTheory.integral_nonneg fun x =>
    mul_nonneg (pow_nonneg (clipF_nonneg A x) p) (pow_nonneg (clipF_nonneg B x) p)

end Star

/-- `e^{-p/10} ≤ d^{-10}` in the regime. -/
theorem RegA.exp_neg_p_div_ten_le {d p : ℕ} (hR : RegA d p) :
    Real.exp (-(p : ℝ) / 10) ≤ vth d := by
  have hd := hR.d_pos
  have hL : 0 ≤ Real.log d := by linarith [hR.logd]
  have h : -(p : ℝ) / 10 ≤ -(10 * Real.log d) := by linarith [hR.plog]
  calc Real.exp (-(p : ℝ) / 10) ≤ Real.exp (-(10 * Real.log d)) := Real.exp_le_exp.2 h
    _ = vth d := by
        rw [vth, Real.exp_neg, show (10 : ℝ) * Real.log d = ((10 : ℕ) : ℝ) * Real.log d by
          norm_num, Real.exp_nat_mul, Real.exp_log hd, one_div]

variable {d p : ℕ}

/-- `A-C1a`: the Rademacher–Gaussian bias of `f₁`, both branches. -/
theorem bias_C1a : ∃ C : ℝ, 0 < C ∧ ∀ d p : ℕ, RegA d p → ∀ cp : CapPoint.{u} d p,
    ∀ v ∈ cp.S,
      |cp.coreE v (fun σ => radE (f1Obs p (cp.A σ v) (cp.B σ v)) -
          gaussE (f1Obs p (cp.A σ v) (cp.B σ v)))| ≤ C * (p : ℝ) ^ 4 / d * cp.FH v ∧
      |cp.coreE v (fun σ => radE (f1Obs p (cp.B σ v) (cp.A σ v)) -
          gaussE (f1Obs p (cp.B σ v) (cp.A σ v)))| ≤ C * (p : ℝ) ^ 4 / d * cp.FH v := by
  refine ⟨10 ^ 8, by norm_num, fun d p hR cp v hv => ?_⟩
  have hp4 : 2 * 4 ≤ p := le_trans (by norm_num) hR.treg.hp
  exact ⟨cp.bias_gen hR hv (fun σ => cp.A σ v) (fun σ => cp.B σ v) (Or.inl fun σ => ⟨rfl, rfl⟩)
      (fun n hn1 hn => (cp.coreE_trace_pow_le hR hv hn1 hn).1)
      (cp.E_trace_pow_le hR hv (by norm_num) hp4).1 (fun σ => cp.hp σ v)
      (fun σ hσ => (cp.alpha_two_h hR hv hσ).1) (cp.h_moment hR hv (by norm_num) hp4).1,
    cp.bias_gen hR hv (fun σ => cp.B σ v) (fun σ => cp.A σ v) (Or.inr fun σ => ⟨rfl, rfl⟩)
      (fun n hn1 hn => (cp.coreE_trace_pow_le hR hv hn1 hn).2)
      (cp.E_trace_pow_le hR hv (by norm_num) hp4).2 (fun σ => cp.hm σ v)
      (fun σ hσ => (cp.alpha_two_h hR hv hσ).2) (cp.h_moment hR hv (by norm_num) hp4).2⟩

/-- `A-SM2`: second moments of the normalized diagonals (explicit constants). -/
theorem second_moment (hR : RegA d p) (cp : CapPoint.{u} d p) {ρ : ℝ} (hρ : cp.DefLe ρ)
    {i : cp.V} (hi : i ∈ cp.S) :
    cp.E (fun σ => (cp.hp σ i - 1) ^ 2) ≤ 5 * epsP d p + 2 * ρ ∧
      cp.E (fun σ => (cp.hm σ i - 1) ^ 2) ≤ 5 * epsP d p + 2 * ρ := by
  have hZ := cp.Zw_pos hR
  have hp4 : 2 * 2 ≤ p := le_trans (by norm_num) hR.treg.hp
  obtain ⟨m1, m2⟩ := cp.h_moment hR hi one_le_two hp4
  obtain ⟨d1, d2⟩ := hρ i hi
  have hε0 := epsP_nonneg hR.treg
  have hε1 := epsP_le hR.treg
  have key : ∀ f : Config cp.V → ℝ,
      cp.E (fun σ => (f σ - 1) ^ 2) =
        cp.E (fun σ => f σ ^ 2) - 2 * cp.E f + 1 := by
    intro f
    have e : (fun σ => (f σ - 1) ^ 2) = fun σ => (f σ ^ 2 - 2 * f σ) + 1 := by
      funext σ; ring
    unfold CapPoint.E
    rw [e, lawE_add, lawE_sub, lawE_const_mul, lawE_one cp.G hZ]
  rw [key, key]
  constructor <;> nlinarith

/-- The algebra of `A-BIASB` for one branch: from (C3), the moment bound `E h_i² ≤ (1 + 2ε)²`
(`i ∈ S`), the deficit bound at `v` and `A-PARP`. -/
theorem bias_branch {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hR : RegA d p) (hdeg : ∀ v, G.degree v ≤ d) {τ : ℝ} {yp ym y : V → ℝ}
    (hy : InCube (sOf d p) y) {S : Finset V} {v : V} (hv : v ∈ S) {ρ X : ℝ} (hρ0 : 0 ≤ ρ)
    (hC3 : X = 1 - diagD G (aOf d p) y S v *
        lawE G p (aOf d p) yp ym S (fun σ => hN G (aOf d p) τ y σ S v) +
      aOf d p ^ 2 * ∑ i ∈ nbhd G S v, lawE G p (aOf d p) yp ym S (fun σ =>
        greenP G (aOf d p) τ y σ S v v * greenP G (aOf d p) τ y σ S i i -
          greenP G (aOf d p) τ y σ S v i ^ 2))
    (hmom : ∀ i ∈ S, lawE G p (aOf d p) yp ym S (fun σ => hN G (aOf d p) τ y σ S i ^ 2) ≤
      (1 + 2 * epsP d p) ^ 2)
    (hdef : 1 - lawE G p (aOf d p) yp ym S (fun σ => hN G (aOf d p) τ y σ S v) ≤ ρ) :
    X + aOf d p ^ 2 * ∑ i ∈ nbhd G S v,
        lawE G p (aOf d p) yp ym S (fun σ => greenP G (aOf d p) τ y σ S v i ^ 2) ≤
      2 * ρ + 5 * epsP d p + 1 / d := by
  have hε0 := epsP_nonneg hR.treg
  have hε1 := epsP_le hR.treg
  set c := 1 + 2 * epsP d p with hc
  have hc0 : 0 ≤ c := by rw [hc]; linarith
  have hy0 : ∀ i, 0 ≤ y i := fun i => (hy i).1
  have hterm : ∀ i ∈ nbhd G S v, lawE G p (aOf d p) yp ym S (fun σ =>
      greenP G (aOf d p) τ y σ S v v * greenP G (aOf d p) τ y σ S i i) ≤ y v * y i * c ^ 2 := by
    intro i hi
    have hiS : i ∈ S := (Finset.mem_filter.1 hi).1
    have e : lawE G p (aOf d p) yp ym S (fun σ =>
        greenP G (aOf d p) τ y σ S v v * greenP G (aOf d p) τ y σ S i i) =
        y v * y i * lawE G p (aOf d p) yp ym S (fun σ =>
          hN G (aOf d p) τ y σ S v * hN G (aOf d p) τ y σ S i) := by
      rw [← lawE_const_mul]
      refine congrArg _ (funext fun σ => ?_)
      rw [greenP_self G (hy0 v), greenP_self G (hy0 i)]
      ring
    rw [e]
    have hcs := wavg_mul_sq_le (w := fun σ => wt G p (aOf d p) yp ym σ S)
      (fun σ => wt_nonneg G σ) (fun σ => hN G (aOf d p) τ y σ S v)
      (fun σ => hN G (aOf d p) τ y σ S i)
    rw [← lawE_eq_wavg, ← lawE_eq_wavg, ← lawE_eq_wavg] at hcs
    have ha := hmom v hv
    have hb := hmom i hiS
    have hb0 : 0 ≤ lawE G p (aOf d p) yp ym S (fun σ => hN G (aOf d p) τ y σ S i ^ 2) :=
      lawE_nonneg G fun σ _ => sq_nonneg _
    have hab := mul_le_mul ha hb hb0 (sq_nonneg c)
    have hx : lawE G p (aOf d p) yp ym S (fun σ =>
        hN G (aOf d p) τ y σ S v * hN G (aOf d p) τ y σ S i) ≤ c ^ 2 := by
      by_contra hcon
      push Not at hcon
      nlinarith [sq_nonneg c]
    exact mul_le_mul_of_nonneg_left hx (mul_nonneg (hy0 v) (hy0 i))
  have hsum : ∑ i ∈ nbhd G S v, lawE G p (aOf d p) yp ym S (fun σ =>
        greenP G (aOf d p) τ y σ S v v * greenP G (aOf d p) τ y σ S i i -
          greenP G (aOf d p) τ y σ S v i ^ 2) +
      ∑ i ∈ nbhd G S v,
        lawE G p (aOf d p) yp ym S (fun σ => greenP G (aOf d p) τ y σ S v i ^ 2) =
      ∑ i ∈ nbhd G S v, lawE G p (aOf d p) yp ym S (fun σ =>
        greenP G (aOf d p) τ y σ S v v * greenP G (aOf d p) τ y σ S i i) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [lawE_sub]; ring
  have hsum2 : ∑ i ∈ nbhd G S v, lawE G p (aOf d p) yp ym S (fun σ =>
      greenP G (aOf d p) τ y σ S v v * greenP G (aOf d p) τ y σ S i i) ≤
      y v * (∑ i ∈ nbhd G S v, y i) * c ^ 2 := by
    calc _ ≤ ∑ i ∈ nbhd G S v, y v * y i * c ^ 2 := Finset.sum_le_sum hterm
      _ = y v * (∑ i ∈ nbhd G S v, y i) * c ^ 2 := by
        rw [Finset.mul_sum, Finset.sum_mul]
  have hD := diagD_eq_one_add_L_sub_C G (aOf d p) hy0 S v
  have hL := Lsum_le_one G hR.treg hdeg hy S v
  have hL0 : 0 ≤ aOf d p ^ 2 * y v * ∑ i ∈ nbhd G S v, y i :=
    mul_nonneg (mul_nonneg (sq_nonneg _) (hy0 v)) (Finset.sum_nonneg fun i _ => hy0 i)
  have hCv := Csum_le G hR.treg hdeg hy S v
  have hD2 := diagD_le_two G hR.treg hdeg hy S v
  have hD1 := FloorIns.one_le_diagD G (aOf d p) hy0 S v
  have hm : -(diagD G (aOf d p) y S v *
      lawE G p (aOf d p) yp ym S (fun σ => hN G (aOf d p) τ y σ S v)) ≤
      -(diagD G (aOf d p) y S v * (1 - ρ)) := by
    have := mul_le_mul_of_nonneg_left (show 1 - ρ ≤ lawE G p (aOf d p) yp ym S
      (fun σ => hN G (aOf d p) τ y σ S v) by linarith) (by linarith : (0 : ℝ) ≤ diagD G
        (aOf d p) y S v)
    linarith
  rw [hC3, add_assoc, ← mul_add, hsum]
  have hsq : aOf d p ^ 2 * (y v * (∑ i ∈ nbhd G S v, y i) * c ^ 2) =
      (aOf d p ^ 2 * y v * ∑ i ∈ nbhd G S v, y i) * c ^ 2 := by ring
  have h5 := mul_le_mul_of_nonneg_left hsum2 (sq_nonneg (aOf d p))
  rw [hsq] at h5
  have hc2 : c ^ 2 ≤ 1 + 5 * epsP d p := by rw [hc]; nlinarith
  have h6 : (aOf d p ^ 2 * y v * ∑ i ∈ nbhd G S v, y i) * c ^ 2 ≤
      aOf d p ^ 2 * y v * ∑ i ∈ nbhd G S v, y i + 5 * epsP d p := by
    nlinarith
  nlinarith

/-- `A-BIASB`: (C3) with the moment bounds, both branches:
`E_{ν_K} N_R / F_H + a² Σ_{i ∼ v} E (G_vi)² ≤ 2ρ + 5ε + 1/d`. -/
theorem bias_bound (hR : RegA d p) (cp : CapPoint.{u} d p) {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ : cp.DefLe ρ) {v : cp.V} (hv : v ∈ cp.S) :
    cp.coreE v (fun σ => radE (f1Obs p (cp.A σ v) (cp.B σ v))) / cp.FH v +
        aOf d p ^ 2 * ∑ i ∈ cp.N v, cp.E (fun σ => cp.gp σ v i ^ 2) ≤
      2 * ρ + 5 * epsP d p + 1 / d ∧
    cp.coreE v (fun σ => radE (f1Obs p (cp.B σ v) (cp.A σ v))) / cp.FH v +
        aOf d p ^ 2 * ∑ i ∈ cp.N v, cp.E (fun σ => cp.gm σ v i ^ 2) ≤
      2 * ρ + 5 * epsP d p + 1 / d := by
  have hp4 : 2 * 2 ≤ p := le_trans (by norm_num) hR.treg.hp
  exact ⟨bias_branch cp.G hR cp.ctx.deg (cp.inCube_yp hR) hv hρ0
      (cp.schur_C3 hR hv) (fun i hi => (cp.h_moment hR hi one_le_two hp4).1) (hρ v hv).1,
    bias_branch cp.G hR cp.ctx.deg (cp.inCube_ym hR) hv hρ0
      (cp.schur_C3_minus hR hv) (fun i hi => (cp.h_moment hR hi one_le_two hp4).2) (hρ v hv).2⟩

/-- `N_G ≥ 0` averaged over the own core law. -/
theorem coreE_NG_nonneg (cp : CapPoint.{u} d p) (v : cp.V) :
    0 ≤ cp.coreE v (fun σ => gaussE (f1Obs p (cp.A σ v) (cp.B σ v))) ∧
      0 ≤ cp.coreE v (fun σ => gaussE (f1Obs p (cp.B σ v) (cp.A σ v))) := by
  constructor
  · refine coreE_nonneg_of_supp cp.G fun σ hσ => ?_
    obtain ⟨hA, hB⟩ := cp.root_psd_core hσ
    rw [f1Obs_eq]; exact gaussE_NG_nonneg hA hB p
  · refine coreE_nonneg_of_supp cp.G fun σ hσ => ?_
    obtain ⟨hA, hB⟩ := cp.root_psd_core hσ
    rw [f1Obs_eq]; exact gaussE_NG_nonneg hB hA p

theorem FH_pos (hR : RegA d p) (cp : CapPoint.{u} d p) {v : cp.V} (hv : v ∈ cp.S) :
    0 < cp.FH v := by
  have := cp.floor hR hv
  by_contra hc
  push Not at hc
  nlinarith [pow_pos (show (0 : ℝ) < 40 by norm_num) p]

/-- The Gaussian average over the floor is below the Rademacher one up to the bias bound. -/
theorem gauss_le_rad_of_bias {C : ℝ} (hR : RegA d p) (cp : CapPoint.{u} d p) {v : cp.V}
    (hv : v ∈ cp.S) (F : Config cp.V → (cp.N v → ℝ) → ℝ)
    (h : |cp.coreE v (fun σ => radE (F σ) - gaussE (F σ))| ≤ C * (p : ℝ) ^ 4 / d * cp.FH v) :
    cp.coreE v (fun σ => gaussE (F σ)) / cp.FH v ≤
      cp.coreE v (fun σ => radE (F σ)) / cp.FH v + C * ((p : ℝ) ^ 4 / d) := by
  have hF := FH_pos hR cp hv
  unfold CapPoint.coreE at h ⊢
  rw [coreE_eq_wavg, wavg_sub, ← coreE_eq_wavg, ← coreE_eq_wavg] at h
  rw [div_le_iff₀ hF, add_mul, div_mul_cancel₀ _ hF.ne']
  have := (abs_le.1 h).1
  have e : C * (p : ℝ) ^ 4 / d * cp.FH v = C * ((p : ℝ) ^ 4 / d) * cp.FH v := by ring
  linarith

/-- `A-ROW`: the incident-row bound, both branches. -/
theorem row_bound : ∃ C : ℝ, 0 < C ∧ ∀ d p : ℕ, RegA d p → ∀ cp : CapPoint.{u} d p,
    ∀ ρ : ℝ, 0 ≤ ρ → cp.DefLe ρ → ∀ v ∈ cp.S,
      aOf d p ^ 2 * ∑ i ∈ cp.N v, cp.E (fun σ => cp.gp σ v i ^ 2) ≤ C * (ρ + b0Of d p) ∧
      aOf d p ^ 2 * ∑ i ∈ cp.N v, cp.E (fun σ => cp.gm σ v i ^ 2) ≤ C * (ρ + b0Of d p) := by
  obtain ⟨C₁, hC₁, h₁⟩ := bias_C1a.{u}
  refine ⟨5 + C₁, by linarith, fun d p hR cp ρ hρ0 hρ v hv => ?_⟩
  obtain ⟨b1, b2⟩ := bias_bound hR cp hρ0 hρ hv
  obtain ⟨c1, c2⟩ := h₁ d p hR cp v hv
  obtain ⟨n1, n2⟩ := coreE_NG_nonneg cp v
  have hF := FH_pos hR cp hv
  have g1 := gauss_le_rad_of_bias hR cp hv _ c1
  have g2 := gauss_le_rad_of_bias hR cp hv _ c2
  have q1 := div_nonneg n1 hF.le
  have q2 := div_nonneg n2 hF.le
  have hε0 := epsP_nonneg hR.treg
  have hd := hR.d_pos
  have hp4 : 0 ≤ (p : ℝ) ^ 4 / d := by positivity
  have hd1 : 0 ≤ 1 / (d : ℝ) := by positivity
  have hb : b0Of d p = epsP d p + (p : ℝ) ^ 4 / d + 1 / d := rfl
  constructor <;> nlinarith

/-- `A-WHITEN`: the core kernel against the Gaussian bias, both branches. -/
theorem whiten : ∃ C : ℝ, 0 < C ∧ ∀ d p : ℕ, RegA d p → ∀ cp : CapPoint.{u} d p,
    ∀ v ∈ cp.S,
      cp.E (fun σ => wK (cp.A σ v)) ≤
          cp.coreE v (fun σ => gaussE (f1Obs p (cp.A σ v) (cp.B σ v))) / cp.FH v +
            C * ((p : ℝ) ^ 4 / d) * (cp.E (fun σ => wK (cp.A σ v)) + 1 / (d : ℝ) ^ 10) ∧
      cp.E (fun σ => wK (cp.B σ v)) ≤
          cp.coreE v (fun σ => gaussE (f1Obs p (cp.B σ v) (cp.A σ v))) / cp.FH v +
            C * ((p : ℝ) ^ 4 / d) * (cp.E (fun σ => wK (cp.B σ v)) + 1 / (d : ℝ) ^ 10) := by
  refine ⟨3 * 10 ^ 6 * Real.exp 12002, by positivity, fun d p hR cp v hv => ?_⟩
  have hp4 : 2 * 2 ≤ p := le_trans (by norm_num) hR.treg.hp
  have hp2 : 2 ≤ p := hR.treg.two_le_p
  have hFH := FH_pos hR cp hv
  have hw : ∀ σ, 0 ≤ wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v :=
    fun σ => wtCore_nonneg cp.G _ _ _ _ σ _ _
  -- T.COV: `w(P) 𝖦Φ ≤ 𝖦 f₁(P, Q)` on the core support
  have hcov : ∀ (P Q : Config cp.V → Matrix (cp.N v) (cp.N v) ℝ),
      (∀ σ, wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v ≠ 0 →
        (P σ).PosSemidef ∧ (Q σ).PosSemidef) →
      cp.coreE v (fun σ => (if wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v ≠ 0 then
          wK (P σ) else 0) * gaussE (starPhi p (P σ) (Q σ))) ≤
        cp.coreE v (fun σ => gaussE (f1Obs p (P σ) (Q σ))) := by
    intro P Q hPQ
    refine wavg_mono' hw fun σ hσ => ?_
    obtain ⟨hP, hQ⟩ := hPQ σ hσ.ne'
    rw [ite_eq_left hσ.ne', f1Obs_eq, mul_comm]
    exact gaussE_NG_ge_whitened hP hQ hp2
  constructor
  · have h := cp.whiten_gen hR hv (fun σ => cp.A σ v) (fun σ => cp.B σ v)
      (Or.inl fun σ => ⟨rfl, rfl⟩) (fun n hn1 hn => (cp.coreE_trace_pow_le hR hv hn1 hn).1)
      (cp.E_trace_pow_le hR hv (by norm_num) hp4).1
    have hc := hcov (fun σ => cp.A σ v) (fun σ => cp.B σ v) fun σ hσ => cp.root_psd_core hσ
    have hd := div_le_div_of_nonneg_right hc hFH.le
    exact h.trans (by unfold vth at *; linarith)
  · have h := cp.whiten_gen hR hv (fun σ => cp.B σ v) (fun σ => cp.A σ v)
      (Or.inr fun σ => ⟨rfl, rfl⟩) (fun n hn1 hn => (cp.coreE_trace_pow_le hR hv hn1 hn).2)
      (cp.E_trace_pow_le hR hv (by norm_num) hp4).2
    have hc := hcov (fun σ => cp.B σ v) (fun σ => cp.A σ v) fun σ hσ =>
      (cp.root_psd_core hσ).symm
    have hd := div_le_div_of_nonneg_right hc hFH.le
    exact h.trans (by unfold vth at *; linarith)

/-- The root trace is dominated by the full diagonals: `tr R ≤ (a² y_v/D_v) Σ_{i ∈ N} y_i h_i`
(Schur order `G_{K,ii} ≤ G_ii`). -/
theorem trace_rootMat_le {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {a τ : ℝ} {y : V → ℝ} (hy : ∀ i, 0 ≤ y i) {σ : Config V}
    {S : Finset V} {v : V} (hv : v ∈ S) (hP : (precN G a τ y σ S).PosDef) :
    (rootMat G a τ y σ S v).trace ≤
      a ^ 2 * y v / diagD G a y S v * ∑ i ∈ nbhd G S v, y i * hN G a τ y σ S i := by
  have hD : 0 < diagD G a y S v := lt_of_lt_of_le one_pos (FloorIns.one_le_diagD G a hy S v)
  have hc0 : 0 ≤ a ^ 2 * y v / diagD G a y S v :=
    div_nonneg (mul_nonneg (sq_nonneg a) (hy v)) hD.le
  have e : (rootMat G a τ y σ S v).trace =
      a ^ 2 * y v / diagD G a y S v * ∑ i ∈ nbhd G S v, coreGreen G a τ y σ S v i i := by
    rw [← Finset.sum_coe_sort (nbhd G S v), Finset.mul_sum]
    rfl
  rw [e]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i hi => ?_) hc0
  have hiv : i ≠ v := fun h => by
    have := (Finset.mem_filter.1 hi).2
    rw [h] at this
    exact G.irrefl this
  rw [← greenP_self G (hy i)]
  exact coreGreen_le_greenP G hy hv hP hiv

/-- `A-WLE` and the tail of `A-C3a` for one branch. -/
theorem tail_branch {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hR : RegA d p) (hdeg : ∀ v, G.degree v ≤ d) {τ : ℝ}
    {yp ym y : V → ℝ} (hy : InCube (sOf d p) y) {S : Finset V} {v : V} (hv : v ∈ S)
    (hZ : 0 < Zw G p (aOf d p) yp ym S)
    (hPD : ∀ σ, wt G p (aOf d p) yp ym σ S ≠ 0 →
      (precN G (aOf d p) τ y σ S).PosDef ∧ (rootMat G (aOf d p) τ y σ S v).PosSemidef)
    (hmom : ∀ i ∈ S, ∀ k : ℕ, 1 ≤ k → 2 * k ≤ p →
      lawE G p (aOf d p) yp ym S (fun σ => hN G (aOf d p) τ y σ S i ^ k) ≤
        (1 + 2 * epsP d p) ^ k)
    (hcap : ∀ i ∈ S, lawE G p (aOf d p) yp ym S (fun σ => hN G (aOf d p) τ y σ S i) ≤
      rOf d p) :
    lawE G p (aOf d p) yp ym S (fun σ => wK (rootMat G (aOf d p) τ y σ S v)) ≤ 1 ∧
      lawE G p (aOf d p) yp ym S (fun σ =>
        if 1 < (rootMat G (aOf d p) τ y σ S v).trace then
          (rootMat G (aOf d p) τ y σ S v * rootMat G (aOf d p) τ y σ S v).trace else 0) ≤
        Real.exp (-(p : ℝ) / 10) := by
  have hy0 : ∀ i, 0 ≤ y i := fun i => (hy i).1
  have hD : 0 < diagD G (aOf d p) y S v :=
    lt_of_lt_of_le one_pos (FloorIns.one_le_diagD G _ hy0 S v)
  have hc0 : 0 ≤ aOf d p ^ 2 * y v / diagD G (aOf d p) y S v :=
    div_nonneg (mul_nonneg (sq_nonneg _) (hy0 v)) hD.le
  have hU0 : aOf d p ^ 2 * y v / diagD G (aOf d p) y S v * ∑ i ∈ nbhd G S v, y i ≤ 51 / 100 := by
    have := Lsum_div_diagD_le G hR.treg hdeg hy S v
    rw [div_mul_eq_mul_div]
    exact this
  have hU00 : 0 ≤ aOf d p ^ 2 * y v / diagD G (aOf d p) y S v * ∑ i ∈ nbhd G S v, y i :=
    mul_nonneg hc0 (Finset.sum_nonneg fun i _ => hy0 i)
  have hε0 := epsP_nonneg hR.treg
  have hε1 := epsP_le hR.treg
  have hr : rOf d p = 1 + epsP d p := by rw [epsP]; ring
  have hhpos : ∀ σ, wt G p (aOf d p) yp ym σ S ≠ 0 → ∀ i, 0 ≤ hN G (aOf d p) τ y σ S i :=
    fun σ hσ i => ((hPD σ hσ).1.inv.diag_pos).le
  have hNS : ∀ i ∈ nbhd G S v, i ∈ S := fun i hi => (Finset.mem_filter.1 hi).1
  -- pointwise: `tr R ≤ U`
  have hptU : ∀ σ, wt G p (aOf d p) yp ym σ S ≠ 0 →
      (rootMat G (aOf d p) τ y σ S v).trace ≤ aOf d p ^ 2 * y v / diagD G (aOf d p) y S v *
        ∑ i ∈ nbhd G S v, y i * hN G (aOf d p) τ y σ S i :=
    fun σ hσ => trace_rootMat_le G hy0 hv (hPD σ hσ).1
  -- `E U ≤ U₀ r`
  have hEU : lawE G p (aOf d p) yp ym S (fun σ => aOf d p ^ 2 * y v / diagD G (aOf d p) y S v *
      ∑ i ∈ nbhd G S v, y i * hN G (aOf d p) τ y σ S i) ≤
      aOf d p ^ 2 * y v / diagD G (aOf d p) y S v * ∑ i ∈ nbhd G S v, y i * rOf d p := by
    rw [lawE_const_mul, lawE_sum]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i hi => ?_) hc0
    rw [lawE_const_mul]
    exact mul_le_mul_of_nonneg_left (hcap i (hNS i hi)) (hy0 i)
  constructor
  · -- `w ≤ tr R ≤ U`
    have h1 : lawE G p (aOf d p) yp ym S (fun σ => wK (rootMat G (aOf d p) τ y σ S v)) ≤
        lawE G p (aOf d p) yp ym S (fun σ => aOf d p ^ 2 * y v / diagD G (aOf d p) y S v *
          ∑ i ∈ nbhd G S v, y i * hN G (aOf d p) τ y σ S i) := by
      refine lawE_le_of_supp G fun σ hσ => ?_
      have hA := (hPD σ hσ).2
      have hμ := hA.trace_nonneg
      have hT := trace_mul_le_trace_mul_trace hA hA
      have hw : wK (rootMat G (aOf d p) τ y σ S v) ≤ (rootMat G (aOf d p) τ y σ S v).trace := by
        rw [wK, div_le_iff₀ (by linarith)]
        nlinarith
      exact hw.trans (hptU σ hσ)
    have h2 : aOf d p ^ 2 * y v / diagD G (aOf d p) y S v * ∑ i ∈ nbhd G S v, y i * rOf d p =
        (aOf d p ^ 2 * y v / diagD G (aOf d p) y S v * ∑ i ∈ nbhd G S v, y i) * rOf d p := by
      rw [← Finset.sum_mul]; ring
    rw [h2] at hEU
    have : (aOf d p ^ 2 * y v / diagD G (aOf d p) y S v * ∑ i ∈ nbhd G S v, y i) * rOf d p ≤ 1 := by
      rw [hr]; nlinarith
    linarith
  · -- the tail with `k = 2m`, `m = p/8`
    set m := p / 8 with hm
    have hm1 : 1 ≤ m := by
      have : 8 ≤ p := le_trans (by norm_num) hR.treg.hp
      omega
    have hk : 2 * (2 * m) ≤ p := by omega
    have hpt : ∀ σ, wt G p (aOf d p) yp ym σ S ≠ 0 →
        (if 1 < (rootMat G (aOf d p) τ y σ S v).trace then
          (rootMat G (aOf d p) τ y σ S v * rootMat G (aOf d p) τ y σ S v).trace else 0) ≤
        (aOf d p ^ 2 * y v / diagD G (aOf d p) y S v *
          ∑ i ∈ nbhd G S v, y i * hN G (aOf d p) τ y σ S i) ^ (2 * m) := by
      intro σ hσ
      have hA := (hPD σ hσ).2
      have hU := hptU σ hσ
      have hUnn : 0 ≤ aOf d p ^ 2 * y v / diagD G (aOf d p) y S v *
          ∑ i ∈ nbhd G S v, y i * hN G (aOf d p) τ y σ S i :=
        mul_nonneg hc0 (Finset.sum_nonneg fun i _ => mul_nonneg (hy0 i) (hhpos σ hσ i))
      split_ifs with h
      · have hT := trace_mul_le_trace_mul_trace hA hA
        set U := aOf d p ^ 2 * y v / diagD G (aOf d p) y S v *
          ∑ i ∈ nbhd G S v, y i * hN G (aOf d p) τ y σ S i
        have hU1 : 1 ≤ U := by linarith
        have h2 : U ^ 2 ≤ U ^ (2 * m) := pow_le_pow_right₀ hU1 (by omega)
        have h3 : (rootMat G (aOf d p) τ y σ S v).trace ^ 2 ≤ U ^ 2 :=
          pow_le_pow_left₀ (by linarith) hU 2
        nlinarith
      · exact pow_nonneg hUnn _
    have h1 := lawE_le_of_supp G hpt
    refine h1.trans ?_
    -- Jensen: `E U^k ≤ (U₀ (1+2ε))^k`
    set U₀ := aOf d p ^ 2 * y v / diagD G (aOf d p) y S v * ∑ i ∈ nbhd G S v, y i with hU₀
    have hJ : lawE G p (aOf d p) yp ym S (fun σ => (aOf d p ^ 2 * y v /
        diagD G (aOf d p) y S v * ∑ i ∈ nbhd G S v, y i * hN G (aOf d p) τ y σ S i) ^ (2 * m)) ≤
        (U₀ * (1 + 2 * epsP d p)) ^ (2 * m) := by
      rcases hU00.eq_or_lt with h0 | hpos
      · -- `U₀ = 0`: every weight vanishes
        have hw0 : ∀ i ∈ nbhd G S v, aOf d p ^ 2 * y v / diagD G (aOf d p) y S v * y i = 0 := by
          intro i hi
          have hle : aOf d p ^ 2 * y v / diagD G (aOf d p) y S v * y i ≤ U₀ := by
            rw [hU₀]
            exact mul_le_mul_of_nonneg_left
              (Finset.single_le_sum (fun j _ => hy0 j) hi) hc0
          have := mul_nonneg hc0 (hy0 i)
          linarith
        have hz : ∀ σ, aOf d p ^ 2 * y v / diagD G (aOf d p) y S v *
            ∑ i ∈ nbhd G S v, y i * hN G (aOf d p) τ y σ S i = 0 := by
          intro σ
          rw [Finset.mul_sum]
          refine Finset.sum_eq_zero fun i hi => ?_
          rw [← mul_assoc, hw0 i hi, zero_mul]
        simp only [hz, zero_pow (by omega : 2 * m ≠ 0), lawE_zero, ← h0, zero_mul, le_refl]
      · -- normalized weights
        have hpt2 : ∀ σ, wt G p (aOf d p) yp ym σ S ≠ 0 →
            (aOf d p ^ 2 * y v / diagD G (aOf d p) y S v *
              ∑ i ∈ nbhd G S v, y i * hN G (aOf d p) τ y σ S i) ^ (2 * m) ≤
            U₀ ^ (2 * m) * ∑ i ∈ nbhd G S v, (aOf d p ^ 2 * y v / diagD G (aOf d p) y S v *
              y i / U₀) * hN G (aOf d p) τ y σ S i ^ (2 * m) := by
          intro σ hσ
          have hwt : ∀ i ∈ nbhd G S v,
              0 ≤ aOf d p ^ 2 * y v / diagD G (aOf d p) y S v * y i / U₀ :=
            fun i _ => div_nonneg (mul_nonneg hc0 (hy0 i)) hpos.le
          have hsum : ∑ i ∈ nbhd G S v, aOf d p ^ 2 * y v / diagD G (aOf d p) y S v * y i / U₀
              = 1 := by
            rw [← Finset.sum_div, ← Finset.mul_sum, ← hU₀, div_self hpos.ne']
          have hJen := Real.pow_arith_mean_le_arith_mean_pow (nbhd G S v)
            (fun i => aOf d p ^ 2 * y v / diagD G (aOf d p) y S v * y i / U₀)
            (fun i => hN G (aOf d p) τ y σ S i) hwt hsum (fun i _ => hhpos σ hσ i) (2 * m)
          have e : aOf d p ^ 2 * y v / diagD G (aOf d p) y S v *
              ∑ i ∈ nbhd G S v, y i * hN G (aOf d p) τ y σ S i =
              U₀ * ∑ i ∈ nbhd G S v, aOf d p ^ 2 * y v / diagD G (aOf d p) y S v * y i / U₀ *
                hN G (aOf d p) τ y σ S i := by
            rw [Finset.mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            field_simp
          rw [e, mul_pow]
          exact mul_le_mul_of_nonneg_left hJen (pow_nonneg hpos.le _)
        refine (lawE_le_of_supp G hpt2).trans ?_
        rw [lawE_const_mul, lawE_sum, mul_pow U₀ (1 + 2 * epsP d p)]
        refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hpos.le _)
        calc ∑ i ∈ nbhd G S v, lawE G p (aOf d p) yp ym S (fun σ =>
              aOf d p ^ 2 * y v / diagD G (aOf d p) y S v * y i / U₀ *
                hN G (aOf d p) τ y σ S i ^ (2 * m))
            ≤ ∑ i ∈ nbhd G S v, aOf d p ^ 2 * y v / diagD G (aOf d p) y S v * y i / U₀ *
                (1 + 2 * epsP d p) ^ (2 * m) := by
              refine Finset.sum_le_sum fun i hi => ?_
              rw [lawE_const_mul]
              exact mul_le_mul_of_nonneg_left (hmom i (hNS i hi) (2 * m) (by omega) hk)
                (div_nonneg (mul_nonneg hc0 (hy0 i)) hpos.le)
          _ = (1 + 2 * epsP d p) ^ (2 * m) := by
              rw [← Finset.sum_mul, ← Finset.sum_div, ← Finset.mul_sum, ← hU₀,
                div_self hpos.ne', one_mul]
    refine hJ.trans ?_
    -- `(U₀(1+2ε))² ≤ 0.2704 ≤ e^{-1}` and `m ≥ p/8 - 1`
    have hb2 : (U₀ * (1 + 2 * epsP d p)) ^ 2 ≤ Real.exp (-1) := by
      have h1 : U₀ * (1 + 2 * epsP d p) ≤ 51 / 100 * (101 / 100) :=
        mul_le_mul hU0 (by linarith) (by linarith) (by norm_num)
      have h2 : (U₀ * (1 + 2 * epsP d p)) ^ 2 ≤ (51 / 100 * (101 / 100)) ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg hU00 (by linarith)) h1 2
      have h3 : (51 / 100 * (101 / 100) : ℝ) ^ 2 ≤ Real.exp (-1) := by
        rw [Real.exp_neg]
        have := Real.exp_one_lt_d9
        rw [le_inv_comm₀ (by norm_num) (Real.exp_pos 1)]
        norm_num at this ⊢
        linarith
      linarith
    have hpow : (U₀ * (1 + 2 * epsP d p)) ^ (2 * m) ≤ Real.exp (-1) ^ m := by
      rw [pow_mul]
      exact pow_le_pow_left₀ (sq_nonneg _) hb2 m
    refine hpow.trans ?_
    rw [← Real.exp_nat_mul, Real.exp_le_exp]
    have hm8 : (p : ℝ) / 8 - 1 ≤ m := by
      have h := Nat.div_add_mod p 8
      have hlt := Nat.mod_lt p (by norm_num : 8 > 0)
      have : (p : ℝ) = 8 * m + (p % 8 : ℕ) := by rw [hm]; exact_mod_cast h.symm
      have : ((p % 8 : ℕ) : ℝ) ≤ 7 := by exact_mod_cast Nat.lt_succ_iff.mp hlt
      linarith
    have hp6 : (10 : ℝ) ^ 6 ≤ p := by exact_mod_cast hR.treg.hp
    nlinarith

/-- Positive definiteness of both precisions at a supported signing. -/
theorem precN_posDef_of_wt (cp : CapPoint.{u} d p) {σ : Config cp.V}
    (h : wt cp.G p (aOf d p) cp.yp cp.ym σ cp.S ≠ 0) :
    (precN cp.G (aOf d p) 1 cp.yp σ cp.S).PosDef ∧
      (precN cp.G (aOf d p) (-1) cp.ym σ cp.S).PosDef := by
  by_contra hc
  unfold wt at h
  exact h (by simp [hc])

/-- `A-WLE`: the core kernel has mean at most one. -/
theorem wK_mean_le_one (hR : RegA d p) (cp : CapPoint.{u} d p) {v : cp.V} (hv : v ∈ cp.S) :
    cp.E (fun σ => wK (cp.A σ v)) ≤ 1 ∧ cp.E (fun σ => wK (cp.B σ v)) ≤ 1 := by
  exact ⟨(tail_branch cp.G hR cp.ctx.deg (cp.inCube_yp hR) hv (cp.Zw_pos hR)
      (fun σ hσ => ⟨(precN_posDef_of_wt cp hσ).1, (cp.root_psd hR hv hσ).1⟩)
      (fun i hi k hk1 hk => (cp.h_moment hR hi hk1 hk).1) (fun i hi => (cp.h_mean_le hi).1)).1,
    (tail_branch cp.G hR cp.ctx.deg (cp.inCube_ym hR) hv (cp.Zw_pos hR)
      (fun σ hσ => ⟨(precN_posDef_of_wt cp hσ).2, (cp.root_psd hR hv hσ).2⟩)
      (fun i hi k hk1 hk => (cp.h_moment hR hi hk1 hk).2) (fun i hi => (cp.h_mean_le hi).2)).1⟩

/-- `A-CK`: the core kernel bound, both branches. -/
theorem core_kernel : ∃ C : ℝ, 0 < C ∧ ∀ d p : ℕ, RegA d p → ∀ cp : CapPoint.{u} d p,
    ∀ ρ : ℝ, 0 ≤ ρ → cp.DefLe ρ → ∀ v ∈ cp.S,
      cp.E (fun σ => wK (cp.A σ v)) ≤ C * (ρ + b0Of d p) ∧
      cp.E (fun σ => wK (cp.B σ v)) ≤ C * (ρ + b0Of d p) := by
  obtain ⟨C₁, hC₁, h₁⟩ := bias_C1a.{u}
  obtain ⟨Cw, hCw, hw⟩ := whiten.{u}
  refine ⟨5 + C₁ + 2 * Cw, by linarith, fun d p hR cp ρ hρ0 hρ v hv => ?_⟩
  obtain ⟨b1, b2⟩ := bias_bound hR cp hρ0 hρ hv
  obtain ⟨c1, c2⟩ := h₁ d p hR cp v hv
  obtain ⟨w1, w2⟩ := hw d p hR cp v hv
  obtain ⟨l1, l2⟩ := wK_mean_le_one hR cp hv
  have g1 := gauss_le_rad_of_bias hR cp hv _ c1
  have g2 := gauss_le_rad_of_bias hR cp hv _ c2
  have hε0 := epsP_nonneg hR.treg
  have hd := hR.d_pos
  have hd1 : (1 : ℝ) ≤ d := by have := hR.treg.ten_pow_six_le_d; linarith
  have hp4 : 0 ≤ (p : ℝ) ^ 4 / d := by positivity
  have hv10 : 1 / (d : ℝ) ^ 10 ≤ 1 := by
    rw [div_le_one (by positivity)]; exact one_le_pow₀ hd1
  have hb : b0Of d p = epsP d p + (p : ℝ) ^ 4 / d + 1 / d := rfl
  have r1 : 0 ≤ aOf d p ^ 2 * ∑ i ∈ cp.N v, cp.E (fun σ => cp.gp σ v i ^ 2) :=
    mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ => lawE_nonneg cp.G fun σ _ =>
      sq_nonneg _)
  have r2 : 0 ≤ aOf d p ^ 2 * ∑ i ∈ cp.N v, cp.E (fun σ => cp.gm σ v i ^ 2) :=
    mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ => lawE_nonneg cp.G fun σ _ =>
      sq_nonneg _)
  have e1 : Cw * ((p : ℝ) ^ 4 / d) * (cp.E (fun σ => wK (cp.A σ v)) + 1 / (d : ℝ) ^ 10) ≤
      2 * Cw * ((p : ℝ) ^ 4 / d) := by
    have := mul_le_mul_of_nonneg_left (add_le_add l1 hv10)
      (mul_nonneg hCw.le hp4)
    linarith
  have e2 : Cw * ((p : ℝ) ^ 4 / d) * (cp.E (fun σ => wK (cp.B σ v)) + 1 / (d : ℝ) ^ 10) ≤
      2 * Cw * ((p : ℝ) ^ 4 / d) := by
    have := mul_le_mul_of_nonneg_left (add_le_add l2 hv10)
      (mul_nonneg hCw.le hp4)
    linarith
  have hfin : ∀ X : ℝ, X ≤ 2 * ρ + 5 * epsP d p + 1 / d + (C₁ + 2 * Cw) * ((p : ℝ) ^ 4 / d) →
      X ≤ (5 + C₁ + 2 * Cw) * (ρ + b0Of d p) := by
    intro X hX
    rw [hb]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 3 + C₁ + 2 * Cw) hρ0,
      mul_nonneg (by linarith : (0 : ℝ) ≤ C₁ + 2 * Cw) hε0,
      mul_nonneg (by linarith : (0 : ℝ) ≤ 4 + C₁ + 2 * Cw) (by positivity : (0 : ℝ) ≤ 1 / d)]
  exact ⟨hfin _ (by linarith), hfin _ (by linarith)⟩

/-- `A-C3a`, pointwise part: `tr A² 1{tr A ≤ 1} ≤ 2 w` for `A ⪰ 0`. -/
theorem trace_sq_le_two_wK {ι : Type*} [Fintype ι] {A : Matrix ι ι ℝ} (hA : A.PosSemidef)
    (h1 : A.trace ≤ 1) : (A * A).trace ≤ 2 * wK A := by
  have h0 : 0 ≤ A.trace := hA.trace_nonneg
  have hT : 0 ≤ (A * A).trace := trace_mul_nonneg hA hA
  rw [wK, mul_div_assoc', le_div_iff₀ (by linarith)]
  nlinarith

/-- `A-C3a`, tail part: `E_H[tr A² 1{tr A > 1}] ≤ e^{-p/10}`, both branches. -/
theorem core_tail (hR : RegA d p) (cp : CapPoint.{u} d p) {v : cp.V} (hv : v ∈ cp.S) :
    cp.E (fun σ => if 1 < (cp.A σ v).trace then (cp.A σ v * cp.A σ v).trace else 0) ≤
        Real.exp (-(p : ℝ) / 10) ∧
      cp.E (fun σ => if 1 < (cp.B σ v).trace then (cp.B σ v * cp.B σ v).trace else 0) ≤
        Real.exp (-(p : ℝ) / 10) := by
  exact ⟨(tail_branch cp.G hR cp.ctx.deg (cp.inCube_yp hR) hv (cp.Zw_pos hR)
      (fun σ hσ => ⟨(precN_posDef_of_wt cp hσ).1, (cp.root_psd hR hv hσ).1⟩)
      (fun i hi k hk1 hk => (cp.h_moment hR hi hk1 hk).1) (fun i hi => (cp.h_mean_le hi).1)).2,
    (tail_branch cp.G hR cp.ctx.deg (cp.inCube_ym hR) hv (cp.Zw_pos hR)
      (fun σ hσ => ⟨(precN_posDef_of_wt cp hσ).2, (cp.root_psd hR hv hσ).2⟩)
      (fun i hi k hk1 hk => (cp.h_moment hR hi hk1 hk).2) (fun i hi => (cp.h_mean_le hi).2)).2⟩

/-- `A-C3a`, pointwise split: `tr A² ≤ 2w + tr A² 1{tr A > 1}` for `A ⪰ 0`. -/
theorem trace_sq_le_split {ι : Type*} [Fintype ι] {A : Matrix ι ι ℝ} (hA : A.PosSemidef) :
    (A * A).trace ≤ 2 * wK A + if 1 < A.trace then (A * A).trace else 0 := by
  have hT := trace_mul_nonneg hA hA
  have hμ := hA.trace_nonneg
  have hw : 0 ≤ wK A := div_nonneg hT (by linarith)
  split_ifs with h
  · linarith
  · have := trace_sq_le_two_wK hA (not_lt.1 h)
    linarith

/-- `A-C3b`: the preclosure core bound. -/
theorem preclosure_C3b : ∃ C : ℝ, 0 < C ∧ ∀ d p : ℕ, RegA d p → ∀ cp : CapPoint.{u} d p,
    ∀ ρ : ℝ, 0 ≤ ρ → cp.DefLe ρ → ∀ v ∈ cp.S,
      cp.E (fun σ => cp.Theta σ v) ≤ C * (ρ + b0Of d p) := by
  obtain ⟨CK, hCK, hK⟩ := core_kernel.{u}
  refine ⟨4 * CK + 2, by linarith, fun d p hR cp ρ hρ0 hρ v hv => ?_⟩
  obtain ⟨k1, k2⟩ := hK d p hR cp ρ hρ0 hρ v hv
  obtain ⟨t1, t2⟩ := core_tail hR cp hv
  have h1 : cp.E (fun σ => cp.Theta σ v) ≤ cp.E (fun σ =>
      (2 * wK (cp.A σ v) + if 1 < (cp.A σ v).trace then (cp.A σ v * cp.A σ v).trace else 0) +
      (2 * wK (cp.B σ v) + if 1 < (cp.B σ v).trace then (cp.B σ v * cp.B σ v).trace else 0)) := by
    refine lawE_le_of_supp cp.G fun σ hσ => ?_
    obtain ⟨hA, hB⟩ := cp.root_psd hR hv hσ
    dsimp only [CapPoint.Theta]
    rw [Matrix.trace_add]
    exact add_le_add (trace_sq_le_split hA) (trace_sq_le_split hB)
  have e : cp.E (fun σ =>
      (2 * wK (cp.A σ v) + if 1 < (cp.A σ v).trace then (cp.A σ v * cp.A σ v).trace else 0) +
      (2 * wK (cp.B σ v) + if 1 < (cp.B σ v).trace then (cp.B σ v * cp.B σ v).trace else 0)) =
      2 * cp.E (fun σ => wK (cp.A σ v)) +
        cp.E (fun σ => if 1 < (cp.A σ v).trace then (cp.A σ v * cp.A σ v).trace else 0) +
      (2 * cp.E (fun σ => wK (cp.B σ v)) +
        cp.E (fun σ => if 1 < (cp.B σ v).trace then (cp.B σ v * cp.B σ v).trace else 0)) := by
    unfold CapPoint.E
    rw [lawE_add, lawE_add, lawE_add, lawE_const_mul, lawE_const_mul]
  have hx := RegA.exp_neg_p_div_ten_le hR
  have hd := hR.d_pos
  have hd1 : (1 : ℝ) ≤ d := by have := hR.treg.ten_pow_six_le_d; linarith
  have hvth : vth d ≤ 1 / (d : ℝ) := by
    rw [vth]
    exact one_div_le_one_div_of_le hd (le_self_pow₀ hd1 (by norm_num))
  have hb := hR.inv_d_le_b0Of
  rw [e] at h1
  nlinarith

end SecA

end BiluLinial.Tight
