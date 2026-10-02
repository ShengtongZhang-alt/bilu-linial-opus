/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecC.Transfer
public import BiluLinial.Tight.SecC.ShiftMat
public import BiluLinial.Tight.SecC.RootMoments
public import BiluLinial.Tight.Tools.Cov
public import BiluLinial.Common.Spectral

/-!
# Lemma "Multiplicative shifted trace comparison" (B1)–(B5)

Source lines 1192–1331; AUDIT-C §4.3 (restatement with `η_BL`, `ε_BL`), §5 (Brascamp–Lieb through
BLmid, gap C/G1), gap D-G6 (`ε_BL` in D10). Nodes of `docs/tight/BP_SECC.md`:

* `shift_mat_facts` (SHIFTMAT; T.MAT (v) instance): on the core support, `0 ⪯ M ⪯ A`,
  `0 ⪯ 𝒩 ⪯ B`, `M, 𝒩 ⪯ (s a²/z) I`.
* `gauss_rowNum_ge` (B25 = B2 + B5, star level): for PSD `A, B, M, 𝒩` with `M ⪯ A`, `𝒩 ⪯ B`,
  `M, 𝒩 ⪯ m₀ I`, `p ≥ 4`:
  `𝖦F ≥ (p-1) tr M² 𝖦[α^{p-2}β^p] + p tr(M𝒩) 𝖦[α^{p-1}β^{p-1}]
          - 4p² m₀ (tr M² 𝖦[α^{p-3}β^p] + tr(M𝒩) 𝖦[α^{p-1}β^{p-2}])`.
* `shift_interp` (B3; T.IL instance): `E[X₁ t₊ + X₂ t₋] ≤ C (E[X₁ + X₂] + ϑ)`.
* `rowGauss_ge_shiftQ` (B4 assembly, proved from the above, T.TRC and the regime):
  `E_{ν_K}𝖦F/(a²F_H) ≥ (1 - C(p⁴/d + p/(dz))) Q - C(p⁵ + p²/z) ϑ - e^{-2p}`.
* `shifted_trace_comparison` (**B1**, proved): with any `E_row` such that
  `𝓡 ≥ E_{ν_K}𝖦F/(a²F_H) - E_row`, `𝓡 ≥ (1 - η_BL) Q - E_row - ε_BL` with
  `η_BL = C(p⁴/d + p/(dz))`, `ε_BL = C(p⁵ + p²/z)ϑ + e^{-2p}`, for every shift `z ∈ [ϑ, 1]`
  (the source's `h = κ₀ p^{-4}` is one such `z`). The audit's explicit form is
  `C = max(8 C_TR, 12 K₁)`, `K₁ = (1 + C_TR) C_B3 + 2 C_TR` (see the proof).
-/

@[expose] public section

namespace BiluLinial.Tight

namespace SecC

universe u

open Matrix MeasureTheory

/-! ### The shifted matrices -/

/-- **SHIFTMAT** (T.MAT (v) instance; source lines 1216–1221). On the core support (`W_core ≠ 0`),
with sources `0 ≤ y ≤ s` at `v` and `z > 0`: `A, B, M, 𝒩 ⪰ 0`, `M ⪯ A`, `𝒩 ⪯ B` (antitonicity
of the inverse: `(P̃_K + z Y_K)⁻¹ ⪯ P̃_K⁻¹`, compressed by `√y` to `N`), and `M, 𝒩 ⪯ (s a²/z) I`
(`(P̃_K + z Y_K)⁻¹ ⪯ (z Y_K)⁺` on the range of `Y_K`, i.e. `Y ⪯ z⁻¹ I`, then
`a² y_v/D_v ≤ a² s`). -/
theorem shift_mat_facts {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {d p : ℕ} (hR : TRegime d p) {S : Finset V} {yp ym : V → ℝ}
    (hyp : InCube (sOf d p) yp) (hym : InCube (sOf d p) ym) {v : V} {z : ℝ} (hz : 0 < z)
    {σ : Config V} (hσ : wtCore G p (aOf d p) yp ym σ S v ≠ 0) :
    let A := rootMat G (aOf d p) 1 yp σ S v
    let B := rootMat G (aOf d p) (-1) ym σ S v
    let M := shiftM G (aOf d p) 1 z yp σ S v
    let N := shiftM G (aOf d p) (-1) z ym σ S v
    let m₀ := sOf d p * aOf d p ^ 2 / z
    A.PosSemidef ∧ B.PosSemidef ∧ M.PosSemidef ∧ N.PosSemidef ∧ (A - M).PosSemidef ∧
      (B - N).PosSemidef ∧ (m₀ • (1 : Matrix (nbhd G S v) (nbhd G S v) ℝ) - M).PosSemidef ∧
      (m₀ • (1 : Matrix (nbhd G S v) (nbhd G S v) ℝ) - N).PosSemidef := by
  obtain ⟨hP1, hP2⟩ := posDef_of_wtCore_ne_zero G hσ
  obtain ⟨hA, hM, hAM, hM0⟩ := shift_branch G (fun i => (hyp i).1) (hyp v).2 hz hP1
  obtain ⟨hB, hN, hBN, hN0⟩ := shift_branch G (fun i => (hym i).1) (hym v).2 hz hP2
  exact ⟨hA, hB, hM, hN, hAM, hBN, hM0, hN0⟩

/-- Trace consequences of SHIFTMAT (T.MAT (i)–(ii)): `0 ≤ tr M² ≤ |N| m₀²` and
`0 ≤ tr(M𝒩) ≤ |N| m₀²`. -/
theorem shift_trace_bounds {ι : Type*} [Fintype ι] [DecidableEq ι] {M N : Matrix ι ι ℝ}
    (hM : M.PosSemidef) (hN : N.PosSemidef) {m₀ : ℝ} (hm₀ : 0 ≤ m₀)
    (hM0 : (m₀ • (1 : Matrix ι ι ℝ) - M).PosSemidef)
    (hN0 : (m₀ • (1 : Matrix ι ι ℝ) - N).PosSemidef) :
    0 ≤ (M * M).trace ∧ (M * M).trace ≤ Fintype.card ι * m₀ ^ 2 ∧
      0 ≤ (M * N).trace ∧ (M * N).trace ≤ Fintype.card ι * m₀ ^ 2 := by
  have htrM : M.trace ≤ Fintype.card ι * m₀ := by
    have := hM0.trace_nonneg
    rw [trace_sub, trace_smul, trace_one, smul_eq_mul] at this
    linarith
  have h1 : (M * M).trace ≤ m₀ * M.trace := by
    have := trace_mul_le_trace_mul hM hM0
    rwa [Matrix.mul_smul, Matrix.mul_one, trace_smul, smul_eq_mul] at this
  have h2 : (M * N).trace ≤ m₀ * M.trace := by
    have := trace_mul_le_trace_mul hM hN0
    rwa [Matrix.mul_smul, Matrix.mul_one, trace_smul, smul_eq_mul] at this
  have h3 := mul_le_mul_of_nonneg_left htrM hm₀
  refine ⟨trace_mul_nonneg hM hM, by nlinarith, trace_mul_nonneg hM hN, by nlinarith⟩

/-! ### B2 + B5 at the star level -/

/-- **B25** (B2 + B5; source lines 1215–1257 and 1312–1317; AUDIT-C §4.3, §5). Sketch:
`2𝖦F = 𝖦[(tr A - q_A) g]`, `g = α^{p-1}β^p` (T.GIBP2, `two_mul_gaussE_starF`)
`= 𝖦g · tr(A(I - Σ_ν)) ≥ 𝖦g · tr(M(I - Σ_ν))` (T.MAT (viii), `Σ_ν ⪯ I`)
`≥ 𝖦[g tr(M(H - H²))]`, `H = 2(p-1)M/α + 2p𝒩/β`, by BLmid (`integral_quad_le_of_midpoint`
with `ρ = g e^{-|x|²/2}`, `K = I + H`, whose midpoint hypothesis is T.ALPHA2,
`gaussWt_clipProd_midpoint`) and T.MAT (iv). Then `g tr(MH)/2` is the first two terms and
`g tr(MH²)/2 ≤ 4p² m₀ (tr M² α^{p-3}β^p + tr(M𝒩) α^{p-1}β^{p-2})` (B5,
`trace_mul_hess_sq_div_le'`). Off the support every term vanishes or has the favourable sign. -/
theorem gauss_rowNum_ge {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ℕ} (hp : 4 ≤ p)
    {A B M N : Matrix ι ι ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef) (hM : M.PosSemidef)
    (hN : N.PosSemidef) (hMA : (A - M).PosSemidef) (hNB : (B - N).PosSemidef) {m₀ : ℝ}
    (hm₀ : 0 ≤ m₀) (hM0 : (m₀ • (1 : Matrix ι ι ℝ) - M).PosSemidef)
    (hN0 : (m₀ • (1 : Matrix ι ι ℝ) - N).PosSemidef) :
    ((p : ℝ) - 1) * ((M * M).trace * gaussE (clipPow p 2 0 A B)) +
        p * ((M * N).trace * gaussE (clipPow p 1 1 A B)) -
      4 * (p : ℝ) ^ 2 * m₀ * ((M * M).trace * gaussE (clipPow p 3 0 A B) +
        (M * N).trace * gaussE (clipPow p 1 2 A B)) ≤
    gaussE (rowNum p A B) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 4 := ⟨p - 4, by omega⟩
  set T₁ := (M * M).trace with hT₁def
  set T₂ := (M * N).trace with hT₂def
  have hT₁ : 0 ≤ T₁ := trace_mul_nonneg hM hM
  have hT₂ : 0 ≤ T₂ := trace_mul_nonneg hM hN
  have hML : opNorm M ≤ m₀ :=
    (opNorm_le_iff_posSemidef hM.1 hm₀).2 ⟨hM0, (PosSemidef.one.smul hm₀).add hM⟩
  have hNL : opNorm N ≤ m₀ :=
    (opNorm_le_iff_posSemidef hN.1 hm₀).2 ⟨hN0, (PosSemidef.one.smul hm₀).add hN⟩
  set H := clipHess (q + 4 - 1) (q + 4) A B M N with hHdef
  have e1 : q + 4 - 1 = q + 3 := by omega
  have hc1 : ((q + 4 - 1 : ℕ) : ℝ) = (q : ℝ) + 3 := by rw [e1]; push_cast; ring
  have hc4 : ((q + 4 : ℕ) : ℝ) = (q : ℝ) + 4 := by push_cast; ring
  -- the expanded B2 integrand `g` and the lower integrand `f`
  set g : (ι → ℝ) → ℝ := fun x => starPhi (q + 4) A B x *
    (((q + 4 - 1 : ℕ) : ℝ) * T₁ / clipF A x ^ 2 + ((q + 4 : ℕ) : ℝ) * T₂ / (clipF A x * clipF B x) -
      (M * (H x * H x)).trace / (2 * clipF A x)) with hgdef
  set f : (ι → ℝ) → ℝ := fun x =>
    (((q + 4 : ℕ) : ℝ) - 1) * T₁ * clipPow (q + 4) 2 0 A B x +
      ((q + 4 : ℕ) : ℝ) * T₂ * clipPow (q + 4) 1 1 A B x -
      4 * ((q + 4 : ℕ) : ℝ) ^ 2 * m₀ *
        (T₁ * clipPow (q + 4) 3 0 A B x + T₂ * clipPow (q + 4) 1 2 A B x) with hfdef
  set K := ((q : ℝ) + 4) * (T₁ + T₂) + 4 * ((q : ℝ) + 4) ^ 2 * m₀ * (T₁ + T₂) with hK
  -- pointwise: `f ≤ g` and `|g| ≤ K`
  have hpt : ∀ x, f x ≤ g x ∧ |g x| ≤ K := by
    intro x
    have hK0 : 0 ≤ K := by positivity
    set u := clipF A x with hu
    set w := clipF B x with hw
    have hu0 : 0 ≤ u := clipF_nonneg A x
    have hw0 : 0 ≤ w := clipF_nonneg B x
    have hu1 : u ≤ 1 := clipF_le_one hA x
    have hw1 : w ≤ 1 := clipF_le_one hB x
    simp only [hfdef, hgdef, clipPow, starPhi, ← hu, ← hw, e1,
      show q + 4 - 2 = q + 2 by omega, show q + 4 - 3 = q + 1 by omega, Nat.sub_zero]
    rcases hu0.eq_or_lt with hu' | hu'
    · rw [← hu']
      simp
      exact hK0
    rcases hw0.eq_or_lt with hw' | hw'
    · rw [← hw']
      simp
      exact hK0
    have hX0 : 0 ≤ (M * (H x * H x)).trace :=
      trace_mul_nonneg hM (posSemidef_mul_self (clipHess_posSemidef hM hN _ _ A B x).1)
    have hB5 := trace_mul_hess_sq_div_le' hM hN hu' hw' (q + 4) hML hNL
    have hHx : H x = (2 * ((q + 4 - 1 : ℕ) : ℝ) / u) • M + (2 * ((q + 4 : ℕ) : ℝ) / w) • N :=
      rfl
    rw [← hHx] at hB5
    set X := (M * (H x * H x)).trace with hXdef
    push_cast at hB5 ⊢
    have hPos : 0 ≤ u ^ (q + 4) * w ^ (q + 4) := by positivity
    have key := mul_le_mul_of_nonneg_left hB5 hPos
    have I1 : u ^ (q + 4) * w ^ (q + 4) * (((q : ℝ) + 3) * T₁ / u ^ 2 +
        ((q : ℝ) + 4) * T₂ / (u * w) - X / (2 * u)) =
        ((q : ℝ) + 3) * T₁ * (u ^ (q + 2) * w ^ (q + 4)) +
          ((q : ℝ) + 4) * T₂ * (u ^ (q + 3) * w ^ (q + 3)) -
          1 / 2 * (u ^ (q + 4) * w ^ (q + 4) * (X / u)) := by
      field_simp
      ring
    have I2 : u ^ (q + 4) * w ^ (q + 4) * (8 * ((q : ℝ) + 4) ^ 2 * m₀ *
        (T₁ / u ^ 2 * (1 / u) + T₂ / (u * w) * (1 / w))) =
        8 * ((q : ℝ) + 4) ^ 2 * m₀ *
          (T₁ * (u ^ (q + 1) * w ^ (q + 4)) + T₂ * (u ^ (q + 3) * w ^ (q + 2))) := by
      field_simp
      ring
    have hY0 : 0 ≤ u ^ (q + 4) * w ^ (q + 4) * (X / u) := by positivity
    have hle : ∀ m n : ℕ, u ^ m * w ^ n ≤ 1 := fun m n =>
      (mul_le_mul (pow_le_one₀ hu0 hu1) (pow_le_one₀ hw0 hw1) (by positivity)
        zero_le_one).trans_eq (one_mul 1)
    have hp1 := hle (q + 2) (q + 4)
    have hp2 := hle (q + 3) (q + 3)
    have hp3 := hle (q + 1) (q + 4)
    have hp4 := hle (q + 3) (q + 2)
    have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    have hm4 : 0 ≤ 4 * ((q : ℝ) + 4) ^ 2 * m₀ := by positivity
    rw [I1]
    rw [I2] at key
    have b1 := mul_le_mul_of_nonneg_left hp1 (show 0 ≤ ((q : ℝ) + 3) * T₁ by positivity)
    have b2 := mul_le_mul_of_nonneg_left hp2 (show 0 ≤ ((q : ℝ) + 4) * T₂ by positivity)
    have b3 := mul_le_mul_of_nonneg_left hp3 hT₁
    have b4 := mul_le_mul_of_nonneg_left hp4 hT₂
    have b5 := mul_le_mul_of_nonneg_left (add_le_add b3 b4) hm4
    have c1 : 0 ≤ ((q : ℝ) + 3) * T₁ * (u ^ (q + 2) * w ^ (q + 4)) := by positivity
    have c2 : 0 ≤ ((q : ℝ) + 4) * T₂ * (u ^ (q + 3) * w ^ (q + 3)) := by positivity
    have d1 := mul_nonneg hm4 (add_nonneg hT₁ hT₂)
    have d2 := mul_nonneg (show (0 : ℝ) ≤ (q : ℝ) + 4 by positivity) (add_nonneg hT₁ hT₂)
    constructor
    · linarith
    · rw [abs_le]
      constructor <;> linarith
  -- integrate
  have hI : ∀ m m' : ℕ, Integrable (clipPow (q + 4) m m' A B) (gaussPi ι) :=
    fun m m' => integrable_clipProd_gaussPi hA hB _ _
  have hJ₁ := (hI 2 0).const_mul ((((q + 4 : ℕ) : ℝ) - 1) * T₁)
  have hJ₂ := (hI 1 1).const_mul (((q + 4 : ℕ) : ℝ) * T₂)
  have hJ₃ := ((hI 3 0).const_mul T₁).add ((hI 1 2).const_mul T₂)
  have hJ₃' : Integrable (fun x => 4 * ((q + 4 : ℕ) : ℝ) ^ 2 * m₀ *
      (T₁ * clipPow (q + 4) 3 0 A B x + T₂ * clipPow (q + 4) 1 2 A B x)) (gaussPi ι) :=
    hJ₃.const_mul _
  have hfI : Integrable f (gaussPi ι) := (hJ₁.add hJ₂).sub hJ₃'
  have hlin : gaussE f = (((q + 4 : ℕ) : ℝ) - 1) * (T₁ * gaussE (clipPow (q + 4) 2 0 A B)) +
      ((q + 4 : ℕ) : ℝ) * (T₂ * gaussE (clipPow (q + 4) 1 1 A B)) -
      4 * ((q + 4 : ℕ) : ℝ) ^ 2 * m₀ * (T₁ * gaussE (clipPow (q + 4) 3 0 A B) +
        T₂ * gaussE (clipPow (q + 4) 1 2 A B)) := by
    have h12 : Integrable (fun x => (((q + 4 : ℕ) : ℝ) - 1) * T₁ * clipPow (q + 4) 2 0 A B x +
        ((q + 4 : ℕ) : ℝ) * T₂ * clipPow (q + 4) 1 1 A B x) (gaussPi ι) := hJ₁.add hJ₂
    have e := integral_sub h12 hJ₃'
    have e2 := integral_add hJ₁ hJ₂
    have e3 := integral_add ((hI 3 0).const_mul T₁) ((hI 1 2).const_mul T₂)
    unfold gaussE
    rw [hfdef]
    beta_reduce
    rw [e, e2]
    simp only [integral_const_mul]
    rw [e3]
    simp only [integral_const_mul]
    ring
  have hgI : Integrable g (gaussPi ι) := by
    refine integrable_gaussPi_of_abs_le ?_ fun x => (hpt x).2
    have hcA := (continuous_clipF A).measurable
    have hcB := (continuous_clipF B).measurable
    have hHm : Measurable H := by
      refine Measurable.of_eval_matrix _ fun i j => ?_
      simp only [hHdef, clipHess, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      exact ((measurable_const.div hcA).mul_const _).add ((measurable_const.div hcB).mul_const _)
    have hXm : Measurable fun x => (M * (H x * H x)).trace :=
      ((continuous_const.matrix_mul (continuous_id.matrix_mul continuous_id)).matrix_trace
        |>.measurable).comp hHm
    refine Measurable.aestronglyMeasurable ?_
    exact ((hcA.pow_const _).mul (hcB.pow_const _)).mul
      (((measurable_const.div (hcA.pow_const 2)).add (measurable_const.div (hcA.mul hcB))).sub
        (hXm.div (measurable_const.mul hcA)))
  have hstarF : starF (q + 4) A B = rowNum (q + 4) A B := by
    funext x
    simp only [starF, rowNum, hc1, hc4]
    ring
  have hB2 := gaussE_starPhi_B2_le hA hB hM hN hMA hNB (p := q + 4) (by omega)
  rw [← hstarF, ← hlin]
  refine le_trans (integral_mono hfI hgI fun x => (hpt x).1) ?_
  exact hB2

/-! ### B3 -/

/-- On the core support, for a shift `z ≥ ϑ`: `0 ≤ tr M², tr(M𝒩) ≤ |N| (s a²/z)² ≤ d^{20}`
(`m₀ = s a²/z ≤ (3/2) d⁹`, `|N| ≤ d`). -/
theorem shift_traces_le {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {d p : ℕ} (hR : TRegime d p) {S : Finset V} {lam : ℝ}
    (hC : CapCtx G d p S lam) {yp ym : V → ℝ} (hyp : InCube (lam * sOf d p) yp)
    (hym : InCube (lam * sOf d p) ym) {v : V} {z : ℝ} (hz1 : vth d ≤ z) {σ : Config V}
    (hσ : wtCore G p (aOf d p) yp ym σ S v ≠ 0) :
    (0 ≤ (shiftM G (aOf d p) 1 z yp σ S v * shiftM G (aOf d p) 1 z yp σ S v).trace ∧
      (shiftM G (aOf d p) 1 z yp σ S v * shiftM G (aOf d p) 1 z yp σ S v).trace ≤
        (d : ℝ) ^ 20) ∧
    (0 ≤ (shiftM G (aOf d p) 1 z yp σ S v * shiftM G (aOf d p) (-1) z ym σ S v).trace ∧
      (shiftM G (aOf d p) 1 z yp σ S v * shiftM G (aOf d p) (-1) z ym σ S v).trace ≤
        (d : ℝ) ^ 20) := by
  have hd0 : (0 : ℝ) < d := lt_of_lt_of_le (by norm_num) hR.ten_pow_six_le_d
  have hd3 : (3 : ℝ) ≤ d := le_trans (by norm_num) hR.ten_pow_six_le_d
  have hθ : 0 < vth d := by unfold vth; positivity
  have hz : 0 < z := hθ.trans_le hz1
  obtain ⟨ha1, ha2⟩ := TRegime.d_aOf_sq hR
  have hs0 := hR.sOf_pos
  have hs3 := TRegime.sOf_le_three hR
  have hm₀ : 0 ≤ sOf d p * aOf d p ^ 2 / z := by positivity
  have hbnd : ((Fintype.card (nbhd G S v) : ℕ) : ℝ) * (sOf d p * aOf d p ^ 2 / z) ^ 2 ≤
      (d : ℝ) ^ 20 := by
    have hz' : 1 / z ≤ (d : ℝ) ^ 10 := by
      rw [div_le_iff₀ hz]
      have : 1 / (d : ℝ) ^ 10 ≤ z := hz1
      rw [div_le_iff₀ (by positivity)] at this
      linarith
    have ha' : aOf d p ^ 2 ≤ 1 / (2 * d) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    have hm : sOf d p * aOf d p ^ 2 / z ≤ 3 / 2 * (d : ℝ) ^ 9 := by
      calc sOf d p * aOf d p ^ 2 / z = sOf d p * aOf d p ^ 2 * (1 / z) := by ring
        _ ≤ 3 * (1 / (2 * d)) * (d : ℝ) ^ 10 := by gcongr
        _ = 3 / 2 * (d : ℝ) ^ 9 := by field_simp
    have hc : ((Fintype.card (nbhd G S v) : ℕ) : ℝ) ≤ d := by
      exact_mod_cast card_nbhd_le G hC.deg S v
    calc ((Fintype.card (nbhd G S v) : ℕ) : ℝ) * (sOf d p * aOf d p ^ 2 / z) ^ 2
        ≤ d * (3 / 2 * (d : ℝ) ^ 9) ^ 2 := by gcongr
      _ = 9 / 4 * (d : ℝ) ^ 19 := by ring
      _ ≤ (d : ℝ) * (d : ℝ) ^ 19 := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = (d : ℝ) ^ 20 := by ring
  obtain ⟨-, -, hMp, hNp, -, -, hM0, hN0⟩ :=
    shift_mat_facts G hR (inCube_of_cap G hR hC hyp) (inCube_of_cap G hR hC hym) hz hσ
  obtain ⟨h1, h2, h3, h4⟩ := shift_trace_bounds hMp hNp hm₀ hM0 hN0
  exact ⟨⟨h1, h2.trans hbnd⟩, ⟨h3, h4.trans hbnd⟩⟩

/-- **B3** (source lines 1259–1279; T.IL instance, gap G5). At a capped point, for
`z ∈ [ϑ, 1]`: `E[X₁ t₊ + X₂ t₋] ≤ C (E[X₁ + X₂] + ϑ)`, `C = 20 e²`. Proof: on the support
`X₁t₊ + X₂t₋ ≤ X Y` with `X = X₁ + X₂`, `Y = t₊ + t₋`, and `X ≤ d^{20} Y²` (`shift_traces_le`);
`E Y^n ≤ 2 · 10^n` for `2n ≤ p` (F2, `rootT_moment_le`), so `E X² ≤ (400 d^{20})²` and
`E Y^{2k} ≤ 20^{2k}`; T.IL with the floor (`lawE_mul_le_vth`, `k = ⌈30 log d⌉`,
`m = E X + ϑ`). -/
theorem shift_interp : ∃ C : ℝ, 0 < C ∧ Eventually fun _ _ d p _ =>
    ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
      (S : Finset V) (lam : ℝ) (yp ym : V → ℝ) (v : V), CapCtx G d p S lam →
      InCube (lam * sOf d p) yp → InCube (lam * sOf d p) ym → v ∈ S →
      ∀ z : ℝ, vth d ≤ z → z ≤ 1 →
        lawE G p (aOf d p) yp ym S (fun σ =>
            shiftX1 G d p z yp σ S v * rootT G (aOf d p) 1 yp σ S v +
              shiftX2 G d p z yp ym σ S v * rootT G (aOf d p) (-1) ym σ S v) ≤
          C * (lawE G p (aOf d p) yp ym S (fun σ =>
            shiftX1 G d p z yp σ S v + shiftX2 G d p z yp ym σ S v) + vth d) := by
  refine ⟨20 * Real.exp 2, by positivity, ((eventually_regime 4).and eventually_kIL).mono ?_⟩
  rintro c₀ κ₀ d p h ⟨⟨hR, -, -⟩, hk⟩ V _ _ G _ S lam yp ym v hC hyp hym hv z hz1 hz2
  have hd3 : 3 ≤ d := le_trans (by norm_num) hR.ten_pow_six_le_nat
  have hk1 := one_le_kIL hd3
  have hp6 := hR.hp
  have hp1n : 1 ≤ p := le_trans (by norm_num) hR.hp
  have hdR := hR.ten_pow_six_le_d
  have hyp0 : ∀ i, 0 ≤ yp i := fun i => (hyp i).1
  have hym0 : ∀ i, 0 ≤ ym i := fun i => (hym i).1
  have hZ := Zw_pos_cap G hR hC hyp hym
  have hθ : 0 < vth d := by unfold vth; positivity
  -- pointwise facts on the support
  have hpt : ∀ σ, wt G p (aOf d p) yp ym σ S ≠ 0 →
      0 ≤ shiftX1 G d p z yp σ S v ∧ 0 ≤ shiftX2 G d p z yp ym σ S v ∧
        0 ≤ rootT G (aOf d p) 1 yp σ S v ∧ 0 ≤ rootT G (aOf d p) (-1) ym σ S v ∧
        shiftX1 G d p z yp σ S v + shiftX2 G d p z yp ym σ S v ≤
          (d : ℝ) ^ 20 * (rootT G (aOf d p) 1 yp σ S v + rootT G (aOf d p) (-1) ym σ S v) ^ 2 := by
    intro σ hσ
    have hc := wtCore_ne_zero_of_wt G hp1n hyp0 hym0 hv hσ
    obtain ⟨ht1, ht2⟩ := rootT_nonneg G hyp0 hym0 hσ v
    obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := shift_traces_le G hR hC hyp hym hz1 hc
    refine ⟨mul_nonneg h1 (sq_nonneg _), mul_nonneg (mul_nonneg h3 ht1) ht2, ht1, ht2, ?_⟩
    simp only [shiftX1, shiftX2]
    have e1 := mul_le_mul_of_nonneg_right h2 (sq_nonneg (rootT G (aOf d p) 1 yp σ S v))
    have e2 := mul_le_mul_of_nonneg_right h4 (mul_nonneg ht1 ht2)
    have hD0 : (0 : ℝ) ≤ (d : ℝ) ^ 20 := by positivity
    nlinarith [mul_nonneg hD0 (sq_nonneg (rootT G (aOf d p) (-1) ym σ S v)),
      mul_nonneg hD0 (mul_nonneg ht1 ht2)]
  -- moments of `Y = t₊ + t₋`
  have hYmom : ∀ n : ℕ, 2 * n ≤ p → lawE G p (aOf d p) yp ym S (fun σ =>
      (rootT G (aOf d p) 1 yp σ S v + rootT G (aOf d p) (-1) ym σ S v) ^ n) ≤ 2 * 10 ^ n := by
    intro n hn
    calc _ ≤ lawE G p (aOf d p) yp ym S (fun σ => 2 ^ n *
            (rootT G (aOf d p) 1 yp σ S v ^ n + rootT G (aOf d p) (-1) ym σ S v ^ n)) :=
          lawE_mono G fun σ hσ =>
            add_pow_le_two_pow_mul (hpt σ hσ).2.2.1 (hpt σ hσ).2.2.2.1 n
      _ = 2 ^ n * (lawE G p (aOf d p) yp ym S (fun σ => rootT G (aOf d p) 1 yp σ S v ^ n) +
            lawE G p (aOf d p) yp ym S (fun σ => rootT G (aOf d p) (-1) ym σ S v ^ n)) := by
          rw [lawE_const_mul, lawE_add]
      _ ≤ 2 ^ n * (5 ^ n + 5 ^ n) := by
          gcongr
          · exact rootT_moment_le G hR hC hyp hym (isBranch_plus yp ym) hv hn
          · exact rootT_moment_le G hR hC hyp hym (isBranch_minus yp ym) hv hn
      _ = 2 * 10 ^ n := by
          rw [show (10 : ℝ) ^ n = 2 ^ n * 5 ^ n by rw [← mul_pow]; norm_num]
          ring
  -- `E X² ≤ (400 d^{20})²`
  have hX2 : lawE G p (aOf d p) yp ym S (fun σ =>
      (shiftX1 G d p z yp σ S v + shiftX2 G d p z yp ym σ S v) ^ 2) ≤ (400 * (d : ℝ) ^ 20) ^ 2 := by
    calc _ ≤ lawE G p (aOf d p) yp ym S (fun σ => (d : ℝ) ^ 40 *
            (rootT G (aOf d p) 1 yp σ S v + rootT G (aOf d p) (-1) ym σ S v) ^ 4) :=
          lawE_mono G fun σ hσ => by
            obtain ⟨h1, h2, -, -, h5⟩ := hpt σ hσ
            calc (shiftX1 G d p z yp σ S v + shiftX2 G d p z yp ym σ S v) ^ 2
                ≤ ((d : ℝ) ^ 20 * (rootT G (aOf d p) 1 yp σ S v +
                    rootT G (aOf d p) (-1) ym σ S v) ^ 2) ^ 2 :=
                  pow_le_pow_left₀ (add_nonneg h1 h2) h5 2
              _ = _ := by ring
      _ = (d : ℝ) ^ 40 * lawE G p (aOf d p) yp ym S (fun σ =>
            (rootT G (aOf d p) 1 yp σ S v + rootT G (aOf d p) (-1) ym σ S v) ^ 4) :=
          lawE_const_mul G _ _
      _ ≤ (d : ℝ) ^ 40 * (2 * 10 ^ 4) :=
          mul_le_mul_of_nonneg_left (hYmom 4 (by omega)) (by positivity)
      _ ≤ (400 * (d : ℝ) ^ 20) ^ 2 := by nlinarith [pow_nonneg (Nat.cast_nonneg d : (0 : ℝ) ≤ d) 40]
  -- `E Y^{2k} ≤ 20^{2k}`
  have hY2k : lawE G p (aOf d p) yp ym S (fun σ =>
      (rootT G (aOf d p) 1 yp σ S v + rootT G (aOf d p) (-1) ym σ S v) ^ (2 * kIL d)) ≤
      20 ^ (2 * kIL d) := by
    refine (hYmom _ (by omega)).trans ?_
    rw [show (20 : ℝ) ^ (2 * kIL d) = 2 ^ (2 * kIL d) * 10 ^ (2 * kIL d) by
      rw [← mul_pow]; norm_num]
    exact mul_le_mul_of_nonneg_right (le_self_pow₀ (by norm_num) (by omega)) (by positivity)
  have hB : 400 * (d : ℝ) ^ 20 ≤ (d : ℝ) ^ 30 := by
    have h10 : (400 : ℝ) ≤ (d : ℝ) ^ 10 :=
      le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hdR 10)
    calc 400 * (d : ℝ) ^ 20 ≤ (d : ℝ) ^ 10 * (d : ℝ) ^ 20 :=
          mul_le_mul_of_nonneg_right h10 (by positivity)
      _ = (d : ℝ) ^ 30 := by ring
  have hX0 : 0 ≤ lawE G p (aOf d p) yp ym S (fun σ =>
      shiftX1 G d p z yp σ S v + shiftX2 G d p z yp ym σ S v) :=
    lawE_nonneg G fun σ hσ => add_nonneg (hpt σ hσ).1 (hpt σ hσ).2.1
  have hI : lawE G p (aOf d p) yp ym S (fun σ =>
      (shiftX1 G d p z yp σ S v + shiftX2 G d p z yp ym σ S v) *
        (rootT G (aOf d p) 1 yp σ S v + rootT G (aOf d p) (-1) ym σ S v)) ≤
      Real.exp 2 * 20 * (lawE G p (aOf d p) yp ym S (fun σ =>
        shiftX1 G d p z yp σ S v + shiftX2 G d p z yp ym σ S v) + vth d) :=
    lawE_mul_le_vth G hd3 hZ
      (X := fun σ => shiftX1 G d p z yp σ S v + shiftX2 G d p z yp ym σ S v)
      (Y := fun σ => rootT G (aOf d p) 1 yp σ S v + rootT G (aOf d p) (-1) ym σ S v)
      (fun σ hσ => add_nonneg (hpt σ hσ).1 (hpt σ hσ).2.1)
      (fun σ hσ => add_nonneg (hpt σ hσ).2.2.1 (hpt σ hσ).2.2.2.1)
      (by linarith) (by positivity) hB (by norm_num) (by linarith) hX2 hY2k
  calc _ ≤ lawE G p (aOf d p) yp ym S (fun σ =>
          (shiftX1 G d p z yp σ S v + shiftX2 G d p z yp ym σ S v) *
            (rootT G (aOf d p) 1 yp σ S v + rootT G (aOf d p) (-1) ym σ S v)) :=
        lawE_mono G fun σ hσ => by
          obtain ⟨h1, h2, h3, h4, -⟩ := hpt σ hσ
          nlinarith [mul_nonneg h1 h4, mul_nonneg h2 h3]
    _ ≤ _ := hI
    _ = _ := by ring

/-! ### Assembly -/

/-- The real-number core of the B4 assembly (source lines 1319–1328; AUDIT-C §4.3 "Assembly"):
with `Γ = E_{ν_K}𝖦F/F_H`, the four transferred numerators `T₁, …, T₄`, the energies
`x₁ = E X₁`, `x₂ = E X₂`, `y₁ = E[X₁ t₊]`, `y₂ = E[X₂ t₋]` and `(p-1) x₁ + p x₂ = a² Q`. -/
theorem b_assembly_real {a d p s z θ E e2 CT C3 Q Γ T₁ T₂ T₃ T₄ x₁ x₂ y₁ y₂ : ℝ}
    (hp : 2 ≤ p) (hd : 0 < d) (hp4 : p ^ 4 ≤ d) (ha1 : 1 / 4 ≤ d * a ^ 2)
    (ha2 : d * a ^ 2 ≤ 1 / 2) (hs0 : 0 < s) (hs3 : s ≤ 3) (hθ : 0 < θ) (hθz : θ ≤ z)
    (hθd : θ = 1 / d ^ 10) (hE : 0 ≤ E) (hexp : (8 * d * p + 24 * p ^ 2 * d ^ 10) * E ≤ e2)
    (hCT : 0 < CT) (hC3 : 0 < C3)
    (hx₁ : 0 ≤ x₁) (hx₂ : 0 ≤ x₂) (hy₁ : 0 ≤ y₁) (hy₂ : 0 ≤ y₂)
    (hQ : (p - 1) * x₁ + p * x₂ = a ^ 2 * Q)
    (hΓ : (p - 1) * T₁ + p * T₂ - 4 * p ^ 2 * (s * a ^ 2 / z) * (T₃ + T₄) ≤ Γ)
    (h1 : |T₁ - x₁| ≤ CT * (p ^ 4 / d) * (x₁ + θ) + E)
    (h2 : |T₂ - x₂| ≤ CT * (p ^ 4 / d) * (x₂ + θ) + E)
    (h3 : |T₃ - y₁| ≤ CT * (p ^ 4 / d) * (y₁ + θ) + E)
    (h4 : |T₄ - y₂| ≤ CT * (p ^ 4 / d) * (y₂ + θ) + E)
    (hy : y₁ + y₂ ≤ C3 * (x₁ + x₂ + θ)) :
    (1 - max (8 * CT) (12 * ((1 + CT) * C3 + 2 * CT)) * (p ^ 4 / d + p / (d * z))) * Q -
        max (8 * CT) (12 * ((1 + CT) * C3 + 2 * CT)) * (p ^ 5 + p ^ 2 / z) * θ - e2 ≤
      Γ / a ^ 2 := by
  set K₁ := (1 + CT) * C3 + 2 * CT with hK₁
  set C := max (8 * CT) (12 * K₁) with hC
  have hK₁0 : 0 < K₁ := by positivity
  have hC8 : 8 * CT ≤ C := le_max_left _ _
  have hC12 : 12 * K₁ ≤ C := le_max_right _ _
  have hp0 : 0 < p := by linarith
  have hz : 0 < z := lt_of_lt_of_le hθ hθz
  have ha2pos : 0 < a ^ 2 := by
    rcases (sq_nonneg a).lt_or_eq with h | h
    · exact h
    · rw [← h] at ha1; linarith
  set u := p ^ 4 / d with hu
  have hu0 : 0 ≤ u := by positivity
  have hu1 : u ≤ 1 := by rw [hu, div_le_one hd]; exact hp4
  have hwd : 1 / z ≤ d ^ 10 := by
    rw [div_le_iff₀ hz]
    have : 1 / d ^ 10 ≤ z := hθd ▸ hθz
    rw [div_le_iff₀ (by positivity)] at this
    linarith
  set x := x₁ + x₂ with hx
  have hx0 : 0 ≤ x := by positivity
  have h1' := (abs_le.mp h1).1
  have h2' := (abs_le.mp h2).1
  have h3' := (abs_le.mp h3).2
  have h4' := (abs_le.mp h4).2
  -- the two retained numerators
  have e1 : (p - 1) * (x₁ - CT * u * (x₁ + θ) - E) ≤ (p - 1) * T₁ :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have e2' : p * (x₂ - CT * u * (x₂ + θ) - E) ≤ p * T₂ :=
    mul_le_mul_of_nonneg_left (by linarith) hp0.le
  have e3 : CT * u * ((p - 1) * (x₁ + θ)) ≤ CT * u * (p * (x₁ + θ)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hA : a ^ 2 * Q - CT * u * p * (x + 2 * θ) - 2 * p * E ≤ (p - 1) * T₁ + p * T₂ := by
    linear_combination e1 + e2' + e3 + hE - hQ
  -- the two cubic numerators
  have f1 : CT * u * (y₁ + y₂) ≤ CT * (y₁ + y₂) := by
    have := mul_le_mul_of_nonneg_left hu1 (show 0 ≤ CT * (y₁ + y₂) by positivity)
    linarith
  have f2 : CT * u * θ ≤ CT * θ := by
    have := mul_le_mul_of_nonneg_left hu1 (show 0 ≤ CT * θ by positivity)
    linarith
  have f3 : (1 + CT) * (y₁ + y₂) ≤ (1 + CT) * (C3 * (x + θ)) :=
    mul_le_mul_of_nonneg_left hy (by linarith)
  have f4 : 2 * CT * θ ≤ 2 * CT * (x + θ) := by
    have := mul_le_mul_of_nonneg_left (show θ ≤ x + θ by linarith)
      (show 0 ≤ 2 * CT by positivity)
    linarith
  have hB : T₃ + T₄ ≤ K₁ * (x + θ) + 2 * E := by
    rw [hK₁]
    linarith
  have g1 : 4 * p ^ 2 * (s * a ^ 2 / z) * (T₃ + T₄) ≤
      4 * p ^ 2 * (s * a ^ 2 / z) * (K₁ * (x + θ) + 2 * E) :=
    mul_le_mul_of_nonneg_left hB (by positivity)
  have hΓ' : a ^ 2 * Q - CT * u * p * (x + 2 * θ) - 2 * p * E -
      4 * p ^ 2 * (s * a ^ 2 / z) * (K₁ * (x + θ) + 2 * E) ≤ Γ := by linarith
  -- `p x ≤ 2 a² Q` and `Q ≥ 0`
  have hpx : p * x ≤ 2 * (a ^ 2 * Q) := by
    have := mul_nonneg (show 0 ≤ p - 2 by linarith) hx₁
    have := mul_nonneg hp0.le hx₂
    linarith
  have hQ0 : 0 ≤ Q := by
    have h : 0 ≤ a ^ 2 * Q := by
      have := mul_nonneg (show 0 ≤ p - 1 by linarith) hx₁
      have := mul_nonneg hp0.le hx₂
      linarith
    by_contra hc
    have := mul_neg_of_pos_of_neg ha2pos (lt_of_not_ge hc)
    linarith
  have hι0 : 0 < d * a ^ 2 := by linarith
  have hda : 1 / d ≤ 4 * a ^ 2 := by
    rw [div_le_iff₀ hd]
    linarith
  have hsda : s * (d * a ^ 2) ≤ 3 / 2 := by
    calc s * (d * a ^ 2) ≤ 3 * (1 / 2) := mul_le_mul hs3 ha2 hι0.le (by norm_num)
      _ = 3 / 2 := by norm_num
  -- (i) the multiplicative losses
  have i1 : CT * u * (p * x) ≤ C * u * Q * a ^ 2 := by
    have := mul_le_mul_of_nonneg_left hpx (show 0 ≤ CT * u by positivity)
    have h2CT : 2 * CT ≤ C := by linarith
    have := mul_le_mul_of_nonneg_right h2CT (mul_nonneg hu0 (mul_nonneg hQ0 ha2pos.le))
    linarith
  have i2 : 4 * p ^ 2 * (s * a ^ 2 / z) * K₁ * x ≤ C * (p / (d * z)) * Q * a ^ 2 := by
    have step1 : 4 * p ^ 2 * (s * a ^ 2 / z) * K₁ * x ≤
        4 * p * (s * a ^ 2 / z) * K₁ * (2 * (a ^ 2 * Q)) := by
      have := mul_le_mul_of_nonneg_left hpx (show 0 ≤ 4 * p * (s * a ^ 2 / z) * K₁ by
        positivity)
      linarith
    have step2 : 4 * p * (s * a ^ 2 / z) * K₁ * (2 * (a ^ 2 * Q)) =
        8 * (s * (d * a ^ 2)) * K₁ * (p / (d * z) * Q * a ^ 2) := by
      field_simp
      ring
    have step3 : 8 * (s * (d * a ^ 2)) * K₁ ≤ C := by
      have := mul_le_mul_of_nonneg_right hsda hK₁0.le
      linarith
    have hP0 : 0 ≤ p / (d * z) * Q * a ^ 2 :=
      mul_nonneg (mul_nonneg (div_nonneg hp0.le (mul_pos hd hz).le) hQ0) ha2pos.le
    have := mul_le_mul_of_nonneg_right step3 hP0
    linarith
  -- (ii) the additive `ϑ` losses
  have ii1 : CT * u * p * (2 * θ) ≤ C * p ^ 5 * θ * a ^ 2 := by
    have e : CT * u * p * (2 * θ) = 2 * CT * p ^ 5 * θ * (1 / d) := by
      rw [hu]; field_simp
    rw [e]
    have := mul_le_mul_of_nonneg_left hda (show 0 ≤ 2 * CT * p ^ 5 * θ by positivity)
    have h8 := mul_le_mul_of_nonneg_right hC8 (show 0 ≤ p ^ 5 * θ * a ^ 2 by positivity)
    linarith
  have ii2 : 4 * p ^ 2 * (s * a ^ 2 / z) * K₁ * θ ≤ C * (p ^ 2 / z) * θ * a ^ 2 := by
    have e : 4 * p ^ 2 * (s * a ^ 2 / z) * K₁ * θ =
        (4 * s * K₁) * (p ^ 2 / z * θ * a ^ 2) := by
      field_simp
    rw [e]
    have h4 : 4 * s * K₁ ≤ C := by
      have := mul_le_mul_of_nonneg_right hs3 hK₁0.le
      linarith
    have := mul_le_mul_of_nonneg_right h4 (show 0 ≤ p ^ 2 / z * θ * a ^ 2 by positivity)
    linarith
  -- (iii) the exponential losses
  have iii : 2 * p * E + 4 * p ^ 2 * (s * a ^ 2 / z) * (2 * E) ≤ e2 * a ^ 2 := by
    have j1 : 2 * p * E ≤ 8 * d * p * E * a ^ 2 := by
      have := mul_le_mul_of_nonneg_left (show 2 ≤ 8 * (d * a ^ 2) by linarith)
        (show 0 ≤ p * E by positivity)
      linarith
    have j2 : 4 * p ^ 2 * (s * a ^ 2 / z) * (2 * E) ≤ 24 * p ^ 2 * d ^ 10 * E * a ^ 2 := by
      have e : 4 * p ^ 2 * (s * a ^ 2 / z) * (2 * E) =
          8 * p ^ 2 * a ^ 2 * E * (s * (1 / z)) := by
        field_simp
        ring
      rw [e]
      have hsw : s * (1 / z) ≤ 3 * d ^ 10 := mul_le_mul hs3 hwd (by positivity) (by norm_num)
      have := mul_le_mul_of_nonneg_left hsw (show 0 ≤ 8 * p ^ 2 * a ^ 2 * E by positivity)
      linarith
    have j3 := mul_le_mul_of_nonneg_right hexp ha2pos.le
    linarith
  rw [le_div_iff₀ ha2pos]
  linarith

/-- `b_assembly_real` before division by `F_H`: `c_k = E_{ν_K}[w_k 𝖦_k]`, `Γ₀ = E_{ν_K} 𝖦F`. -/
theorem b_assembly_real' {a d p s z θ E e2 CT C3 Q F Γ₀ c₁ c₂ c₃ c₄ x₁ x₂ y₁ y₂ : ℝ}
    (hp : 2 ≤ p) (hd : 0 < d) (hp4 : p ^ 4 ≤ d) (ha1 : 1 / 4 ≤ d * a ^ 2)
    (ha2 : d * a ^ 2 ≤ 1 / 2) (hs0 : 0 < s) (hs3 : s ≤ 3) (hθ : 0 < θ) (hθz : θ ≤ z)
    (hθd : θ = 1 / d ^ 10) (hE : 0 ≤ E) (hexp : (8 * d * p + 24 * p ^ 2 * d ^ 10) * E ≤ e2)
    (hCT : 0 < CT) (hC3 : 0 < C3)
    (hx₁ : 0 ≤ x₁) (hx₂ : 0 ≤ x₂) (hy₁ : 0 ≤ y₁) (hy₂ : 0 ≤ y₂)
    (hQ : (p - 1) * x₁ + p * x₂ = a ^ 2 * Q) (hF : 0 < F)
    (hΓ : (p - 1) * c₁ + p * c₂ - 4 * p ^ 2 * (s * a ^ 2 / z) * (c₃ + c₄) ≤ Γ₀)
    (h1 : |c₁ / F - x₁| ≤ CT * (p ^ 4 / d) * (x₁ + θ) + E)
    (h2 : |c₂ / F - x₂| ≤ CT * (p ^ 4 / d) * (x₂ + θ) + E)
    (h3 : |c₃ / F - y₁| ≤ CT * (p ^ 4 / d) * (y₁ + θ) + E)
    (h4 : |c₄ / F - y₂| ≤ CT * (p ^ 4 / d) * (y₂ + θ) + E)
    (hy : y₁ + y₂ ≤ C3 * (x₁ + x₂ + θ)) :
    (1 - max (8 * CT) (12 * ((1 + CT) * C3 + 2 * CT)) * (p ^ 4 / d + p / (d * z))) * Q -
        max (8 * CT) (12 * ((1 + CT) * C3 + 2 * CT)) * (p ^ 5 + p ^ 2 / z) * θ - e2 ≤
      Γ₀ / (a ^ 2 * F) := by
  have hΓ' : (p - 1) * (c₁ / F) + p * (c₂ / F) - 4 * p ^ 2 * (s * a ^ 2 / z) * (c₃ / F + c₄ / F)
      ≤ Γ₀ / F := by
    have e : (p - 1) * (c₁ / F) + p * (c₂ / F) - 4 * p ^ 2 * (s * a ^ 2 / z) * (c₃ / F + c₄ / F) =
        ((p - 1) * c₁ + p * c₂ - 4 * p ^ 2 * (s * a ^ 2 / z) * (c₃ + c₄)) / F := by
      field_simp
    rw [e]
    exact div_le_div_of_nonneg_right hΓ hF.le
  have := b_assembly_real hp hd hp4 ha1 ha2 hs0 hs3 hθ hθz hθd hE hexp hCT hC3 hx₁ hx₂ hy₁ hy₂ hQ
    hΓ' h1 h2 h3 h4 hy
  rwa [div_div, mul_comm F] at this

/-- **B4 assembly** (proved from SHIFTMAT, B25, T.TRC, B3, `shiftQ_eq` and the regime). -/
theorem rowGauss_ge_shiftQ : ∃ C : ℝ, 0 < C ∧ Eventually fun _ _ d p _ =>
    ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
      (S : Finset V) (lam : ℝ) (yp ym : V → ℝ) (v : V), CapCtx G d p S lam →
      InCube (lam * sOf d p) yp → InCube (lam * sOf d p) ym → v ∈ S →
      ∀ z : ℝ, vth d ≤ z → z ≤ 1 →
        (1 - C * ((p : ℝ) ^ 4 / d + p / (d * z))) * shiftQ G d p z yp ym S v -
            C * ((p : ℝ) ^ 5 + (p : ℝ) ^ 2 / z) * vth d - Real.exp (-(2 * (p : ℝ))) ≤
          rowGauss G d p yp ym S v := by
  obtain ⟨CT, hCT, hTRC⟩ := core_transfer.{u}
  obtain ⟨C3, hC3, hB3⟩ := shift_interp.{u}
  refine ⟨max (8 * CT) (12 * ((1 + CT) * C3 + 2 * CT)),
    lt_of_lt_of_le (by positivity) (le_max_left _ _),
    (((hTRC.and hB3).and (eventually_regime 4)).and eventually_exp_absorb).mono ?_⟩
  rintro c₀ κ₀ d p h ⟨⟨⟨hT, hB⟩, hR, -, -⟩, hexp⟩ V _ _ G _ S lam yp ym v hC hyp hym hv z hz1
    hz2
  have hd0 : (0 : ℝ) < d := lt_of_lt_of_le (by norm_num) hR.ten_pow_six_le_d
  have hd3 : (3 : ℝ) ≤ d := le_trans (by norm_num) hR.ten_pow_six_le_d
  have hθ : 0 < vth d := by unfold vth; positivity
  have hz : 0 < z := hθ.trans_le hz1
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hR.two_le_p
  have hp4 : (p : ℝ) ^ 4 ≤ d := TRegime.pow_le_d hR (by norm_num)
  have hp4n : 4 ≤ p := le_trans (by norm_num) hR.hp
  have hp1n : 1 ≤ p := le_trans (by norm_num) hR.hp
  obtain ⟨ha1, ha2⟩ := TRegime.d_aOf_sq hR
  have hs0 := hR.sOf_pos
  have hs3 := TRegime.sOf_le_three hR
  have hyp' := inCube_of_cap G hR hC hyp
  have hym' := inCube_of_cap G hR hC hym
  have hyp0 : ∀ i, 0 ≤ yp i := fun i => (hyp i).1
  have hym0 : ∀ i, 0 ≤ ym i := fun i => (hym i).1
  have hFH := insFH_pos G hR hC hyp hym hv
  have hm₀ : 0 ≤ sOf d p * aOf d p ^ 2 / z := by positivity
  -- `m₀ ≤ (3/2) d⁹`, so `|N| m₀² ≤ d^20`
  have hbnd : ((Fintype.card (nbhd G S v) : ℕ) : ℝ) * (sOf d p * aOf d p ^ 2 / z) ^ 2 ≤
      (d : ℝ) ^ 20 := by
    have hz' : 1 / z ≤ (d : ℝ) ^ 10 := by
      rw [div_le_iff₀ hz]
      have : 1 / (d : ℝ) ^ 10 ≤ z := hz1
      rw [div_le_iff₀ (by positivity)] at this
      linarith
    have ha' : aOf d p ^ 2 ≤ 1 / (2 * d) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    have hm : sOf d p * aOf d p ^ 2 / z ≤ 3 / 2 * (d : ℝ) ^ 9 := by
      calc sOf d p * aOf d p ^ 2 / z = sOf d p * aOf d p ^ 2 * (1 / z) := by ring
        _ ≤ 3 * (1 / (2 * d)) * (d : ℝ) ^ 10 := by gcongr
        _ = 3 / 2 * (d : ℝ) ^ 9 := by field_simp
    have hc : ((Fintype.card (nbhd G S v) : ℕ) : ℝ) ≤ d := by
      exact_mod_cast card_nbhd_le G hC.deg S v
    calc ((Fintype.card (nbhd G S v) : ℕ) : ℝ) * (sOf d p * aOf d p ^ 2 / z) ^ 2
        ≤ d * (3 / 2 * (d : ℝ) ^ 9) ^ 2 := by gcongr
      _ = 9 / 4 * (d : ℝ) ^ 19 := by ring
      _ ≤ (d : ℝ) * (d : ℝ) ^ 19 := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = (d : ℝ) ^ 20 := by ring
  -- B25 on the core support, averaged over the own core law
  have hL : ∀ σ, wtCore G p (aOf d p) yp ym σ S v ≠ 0 →
      ((p : ℝ) - 1) * ((shiftM G (aOf d p) 1 z yp σ S v * shiftM G (aOf d p) 1 z yp σ S v).trace *
          gaussE (clipPow p 2 0 (rootMat G (aOf d p) 1 yp σ S v)
            (rootMat G (aOf d p) (-1) ym σ S v))) +
        p * ((shiftM G (aOf d p) 1 z yp σ S v * shiftM G (aOf d p) (-1) z ym σ S v).trace *
          gaussE (clipPow p 1 1 (rootMat G (aOf d p) 1 yp σ S v)
            (rootMat G (aOf d p) (-1) ym σ S v))) -
        4 * (p : ℝ) ^ 2 * (sOf d p * aOf d p ^ 2 / z) *
          ((shiftM G (aOf d p) 1 z yp σ S v * shiftM G (aOf d p) 1 z yp σ S v).trace *
              gaussE (clipPow p 3 0 (rootMat G (aOf d p) 1 yp σ S v)
                (rootMat G (aOf d p) (-1) ym σ S v)) +
            (shiftM G (aOf d p) 1 z yp σ S v * shiftM G (aOf d p) (-1) z ym σ S v).trace *
              gaussE (clipPow p 1 2 (rootMat G (aOf d p) 1 yp σ S v)
                (rootMat G (aOf d p) (-1) ym σ S v))) ≤
        gaussE (rowNum p (rootMat G (aOf d p) 1 yp σ S v) (rootMat G (aOf d p) (-1) ym σ S v)) := by
    intro σ hσ
    obtain ⟨hA, hB, hMp, hNp, hAM, hBN, hM0, hN0⟩ := shift_mat_facts G hR hyp' hym' hz hσ
    exact gauss_rowNum_ge hp4n hA hB hMp hNp hAM hBN hm₀ hM0 hN0
  have hmono := coreE_mono G hL
  simp only [coreE_sub, coreE_add, coreE_const_mul] at hmono
  -- the trace numerators
  have hwb : ∀ σ, wtCore G p (aOf d p) yp ym σ S v ≠ 0 →
      (0 ≤ (shiftM G (aOf d p) 1 z yp σ S v * shiftM G (aOf d p) 1 z yp σ S v).trace ∧
        (shiftM G (aOf d p) 1 z yp σ S v * shiftM G (aOf d p) 1 z yp σ S v).trace ≤
          (d : ℝ) ^ 20) ∧
      (0 ≤ (shiftM G (aOf d p) 1 z yp σ S v * shiftM G (aOf d p) (-1) z ym σ S v).trace ∧
        (shiftM G (aOf d p) 1 z yp σ S v * shiftM G (aOf d p) (-1) z ym σ S v).trace ≤
          (d : ℝ) ^ 20) := by
    intro σ hσ
    obtain ⟨-, -, hMp, hNp, -, -, hM0, hN0⟩ := shift_mat_facts G hR hyp' hym' hz hσ
    obtain ⟨h1, h2, h3, h4⟩ := shift_trace_bounds hMp hNp hm₀ hM0 hN0
    exact ⟨⟨h1, h2.trans hbnd⟩, ⟨h3, h4.trans hbnd⟩⟩
  have hinv1 := coreInv_of_mats G (aOf d p) z yp ym S v fun _ _ M _ => (M * M).trace
  have hinv2 := coreInv_of_mats G (aOf d p) z yp ym S v fun _ _ M N => (M * N).trace
  have hT1 := hT V G S lam yp ym v hC hyp hym hv _ 2 0 (by norm_num) (by norm_num) hinv1
    fun σ hσ => (hwb σ hσ).1
  have hT2 := hT V G S lam yp ym v hC hyp hym hv _ 1 1 (by norm_num) (by norm_num) hinv2
    fun σ hσ => (hwb σ hσ).2
  have hT3 := hT V G S lam yp ym v hC hyp hym hv _ 3 0 (by norm_num) (by norm_num) hinv1
    fun σ hσ => (hwb σ hσ).1
  have hT4 := hT V G S lam yp ym v hC hyp hym hv _ 1 2 (by norm_num) (by norm_num) hinv2
    fun σ hσ => (hwb σ hσ).2
  beta_reduce at hT1 hT2 hT3 hT4
  have hB3' := hB V G S lam yp ym v hC hyp hym hv z hz1 hz2
  rw [lawE_add G, lawE_add G] at hB3'
  -- identify the transferred energies with `E X₁`, `E X₂`, `E[X₁ t₊]`, `E[X₂ t₋]`
  have ex1 : lawE G p (aOf d p) yp ym S (fun σ =>
      (shiftM G (aOf d p) 1 z yp σ S v * shiftM G (aOf d p) 1 z yp σ S v).trace *
        rootT G (aOf d p) 1 yp σ S v ^ 2 * rootT G (aOf d p) (-1) ym σ S v ^ 0) =
      lawE G p (aOf d p) yp ym S (fun σ => shiftX1 G d p z yp σ S v) := by
    congr 1; funext σ; simp [shiftX1]
  have ex2 : lawE G p (aOf d p) yp ym S (fun σ =>
      (shiftM G (aOf d p) 1 z yp σ S v * shiftM G (aOf d p) (-1) z ym σ S v).trace *
        rootT G (aOf d p) 1 yp σ S v ^ 1 * rootT G (aOf d p) (-1) ym σ S v ^ 1) =
      lawE G p (aOf d p) yp ym S (fun σ => shiftX2 G d p z yp ym σ S v) := by
    congr 1; funext σ; simp [shiftX2]
  have ex3 : lawE G p (aOf d p) yp ym S (fun σ =>
      (shiftM G (aOf d p) 1 z yp σ S v * shiftM G (aOf d p) 1 z yp σ S v).trace *
        rootT G (aOf d p) 1 yp σ S v ^ 3 * rootT G (aOf d p) (-1) ym σ S v ^ 0) =
      lawE G p (aOf d p) yp ym S (fun σ => shiftX1 G d p z yp σ S v *
        rootT G (aOf d p) 1 yp σ S v) := by
    congr 1; funext σ; simp only [shiftX1, pow_zero, mul_one]; ring
  have ex4 : lawE G p (aOf d p) yp ym S (fun σ =>
      (shiftM G (aOf d p) 1 z yp σ S v * shiftM G (aOf d p) (-1) z ym σ S v).trace *
        rootT G (aOf d p) 1 yp σ S v ^ 1 * rootT G (aOf d p) (-1) ym σ S v ^ 2) =
      lawE G p (aOf d p) yp ym S (fun σ => shiftX2 G d p z yp ym σ S v *
        rootT G (aOf d p) (-1) ym σ S v) := by
    congr 1; funext σ; simp only [shiftX2, pow_one]; ring
  rw [ex1] at hT1
  rw [ex2] at hT2
  rw [ex3] at hT3
  rw [ex4] at hT4
  -- nonnegativity on the support
  have hsupp : ∀ σ, wt G p (aOf d p) yp ym σ S ≠ 0 →
      0 ≤ shiftX1 G d p z yp σ S v ∧ 0 ≤ shiftX2 G d p z yp ym σ S v ∧
        0 ≤ rootT G (aOf d p) 1 yp σ S v ∧ 0 ≤ rootT G (aOf d p) (-1) ym σ S v := by
    intro σ hσ
    have hc := wtCore_ne_zero_of_wt G hp1n hyp0 hym0 hv hσ
    obtain ⟨ht1, ht2⟩ := rootT_nonneg G hyp0 hym0 hσ v
    obtain ⟨⟨hw1, -⟩, ⟨hw2, -⟩⟩ := hwb σ hc
    exact ⟨mul_nonneg hw1 (sq_nonneg _), mul_nonneg (mul_nonneg hw2 ht1) ht2, ht1, ht2⟩
  have hx1 := lawE_nonneg G fun σ hσ => (hsupp σ hσ).1
  have hx2 := lawE_nonneg G fun σ hσ => (hsupp σ hσ).2.1
  have hy1 := lawE_nonneg G fun σ hσ => mul_nonneg (hsupp σ hσ).1 (hsupp σ hσ).2.2.1
  have hy2 := lawE_nonneg G fun σ hσ => mul_nonneg (hsupp σ hσ).2.1 (hsupp σ hσ).2.2.2
  have hQ := shiftQ_eq G (d := d) (p := p) (S := S) hyp0 hym0 v z
  unfold rowGauss
  exact b_assembly_real' hp2 hd0 hp4 ha1 ha2 hs0 hs3 hθ hz1 rfl (Real.exp_pos _).le hexp hCT hC3
    hx1 hx2 hy1 hy2 hQ hFH hmono hT1 hT2 hT3 hT4 hB3'

/-- `Q ≥ 0` at a capped point (`a² Q = (p-1) E X₁ + p E X₂`, `X₁, X₂ ≥ 0` on the support). -/
theorem shiftQ_nonneg {d p : ℕ} (hR : TRegime d p) {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {S : Finset V} {lam : ℝ} {yp ym : V → ℝ} {v : V}
    (hC : CapCtx G d p S lam) (hyp : InCube (lam * sOf d p) yp)
    (hym : InCube (lam * sOf d p) ym) (hv : v ∈ S) {z : ℝ} (hz : 0 < z) :
    0 ≤ shiftQ G d p z yp ym S v := by
  have hyp' := inCube_of_cap G hR hC hyp
  have hym' := inCube_of_cap G hR hC hym
  have hyp0 : ∀ i, 0 ≤ yp i := fun i => (hyp i).1
  have hym0 : ∀ i, 0 ≤ ym i := fun i => (hym i).1
  have hp1n : 1 ≤ p := le_trans (by norm_num) hR.hp
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp1n
  have hm₀ : 0 ≤ sOf d p * aOf d p ^ 2 / z := by have := hR.sOf_pos; positivity
  have hsupp : ∀ σ, wt G p (aOf d p) yp ym σ S ≠ 0 →
      0 ≤ shiftX1 G d p z yp σ S v ∧ 0 ≤ shiftX2 G d p z yp ym σ S v := by
    intro σ hσ
    have hc := wtCore_ne_zero_of_wt G hp1n hyp0 hym0 hv hσ
    obtain ⟨ht1, ht2⟩ := rootT_nonneg G hyp0 hym0 hσ v
    obtain ⟨-, -, hMp, hNp, -, -, hM0, hN0⟩ := shift_mat_facts G hR hyp' hym' hz hc
    obtain ⟨h1, -, h3, -⟩ := shift_trace_bounds hMp hNp hm₀ hM0 hN0
    exact ⟨mul_nonneg h1 (sq_nonneg _), mul_nonneg (mul_nonneg h3 ht1) ht2⟩
  have hx1 := lawE_nonneg G fun σ hσ => (hsupp σ hσ).1
  have hx2 := lawE_nonneg G fun σ hσ => (hsupp σ hσ).2
  have hQ := shiftQ_eq G (d := d) (p := p) (S := S) hyp0 hym0 v z
  have ha : 0 < aOf d p ^ 2 := pow_pos hR.aOf_pos 2
  have h0 : 0 ≤ aOf d p ^ 2 * shiftQ G d p z yp ym S v := by
    rw [← hQ]
    have := mul_nonneg (show (0 : ℝ) ≤ (p : ℝ) - 1 by linarith) hx1
    have := mul_nonneg (show (0 : ℝ) ≤ p by linarith) hx2
    linarith
  by_contra hc
  have := mul_neg_of_pos_of_neg ha (lt_of_not_ge hc)
  linarith

/-- **B1** (source display (B1), line 1205), with explicit-form losses
`η_BL = C(p⁴/d + p/(dz))` and `ε_BL = C(p⁵ + p²/z)ϑ + e^{-2p}`, for every `E_row` with
`𝓡 ≥ E_{ν_K}𝖦F/(a²F_H) - E_row` and every shift `z ∈ [ϑ, 1]`. -/
theorem shifted_trace_comparison : ∃ C : ℝ, 0 < C ∧ Eventually fun _ _ d p _ =>
    ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
      (S : Finset V) (lam : ℝ) (yp ym : V → ℝ) (v : V), CapCtx G d p S lam →
      InCube (lam * sOf d p) yp → InCube (lam * sOf d p) ym → v ∈ S →
      ∀ z : ℝ, vth d ≤ z → z ≤ 1 → ∀ Erow : ℝ,
        rowGauss G d p yp ym S v - Erow ≤ rowMean G d p yp ym S v →
        (1 - C * ((p : ℝ) ^ 4 / d + p / (d * z))) * shiftQ G d p z yp ym S v - Erow -
            C * ((p : ℝ) ^ 5 + (p : ℝ) ^ 2 / z) * vth d - Real.exp (-(2 * (p : ℝ))) ≤
          rowMean G d p yp ym S v := by
  obtain ⟨C, hC, hB⟩ := rowGauss_ge_shiftQ
  refine ⟨C, hC, hB.mono fun c₀ κ₀ d p h hP V _ _ G _ S lam yp ym v hC hyp hym hv z hz1 hz2
    Erow hE => ?_⟩
  have := hP V G S lam yp ym v hC hyp hym hv z hz1 hz2
  linarith

end SecC

end BiluLinial.Tight
