/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.Tools.GaussDensity
public import BiluLinial.Tight.Tools.GIBP2
public import BiluLinial.Tight.Tools.MatrixFacts

/-!
# T.COV: covariance consequences of BLmid for the star weight

Node T.COV (i)–(iii) of `docs/tight/BP_TOOLS.md` (AUDIT-C §5.3 corollaries, §7; AUDIT-A §2.9
(C1b)). For PSD `A, B`, `g = α^{p-1} β^p` (`starG p A B`), `Φ = α^p β^p` (`starPhi`) and
`N_G = 𝖦[(tr A - q_A) g]`:

* (i) `gaussE_NG_nonneg`: `N_G ≥ 0` (every `p`).
* (ii) `gaussE_NG_ge_of_le`: if `0 ≤ λ` and `A ⪯ λ I`, then
  `N_G ≥ 𝖦 g · 2(p-1) tr A² / (1 + 2(p-1)λ)`; `gaussE_NG_ge_opNorm` is the case `λ = ‖A‖`;
  `gaussE_NG_ge_whitened` (`p ≥ 2`): `N_G ≥ f_G w` with `f_G = 𝖦 Φ`, `w = tr A²/(1 + tr A)`.
  Proof: `N_G = tr A 𝖦 g - 𝖦[q_A g]`, BLmid with constant modulus `K = I + 2(p-1)A`
  (`gaussE_qForm_mul_clipProd_le_const`), and the matrix bound
  `tr A - tr(A (I + cA)⁻¹) ≥ c tr A²/(1 + cλ)` (`trace_sub_trace_mul_inv_ge`).
* (iii) **B2** `gaussE_starG_trace_le`: for `p ≥ 3`, `0 ⪯ M ⪯ A`, `0 ⪯ N ⪯ B` and
  `H = 2(p-1)M/α + 2pN/β` (`clipHess (p-1) p A B M N`): `𝖦[g tr(M(H - H²))] ≤ 2 𝖦 F`.
  Proof: `2𝖦F = N_G` (T.GIBP2); `N_G = 𝖦[(tr(A-M) - q_{A-M}) g] + 𝖦[(tr M - q_M) g]`; the first
  term is `≥ 0` (BLmid, `K = I`), the second is `≥ 𝖦[tr(M(I - (I+H)⁻¹)) g]` (BLmid, `K = I + H`),
  and `tr(M(I - (I+H)⁻¹)) ≥ tr(M(H - H²))` pointwise (T.MAT (iv)). If `x ↦ g tr(M(H-H²))` is not
  integrable its integral is `0` and the bound follows from `𝖦[tr(M(I-(I+H)⁻¹)) g] ≥ 0`.
* `gaussE_starPhi_B2_le` (B2, expanded): `𝖦 F ≥ 𝖦[Φ{(p-1) tr M²/α² + p tr(MN)/(αβ)
  - tr(MH²)/(2α)}]`, since `g tr(M(H - H²))/2` equals that integrand pointwise.

**Checks.** `A = 0`: `N_G = 0` and all lower bounds are `0` (`M = 0`). `ι` empty: all terms `0`.
`p = 1` in (ii): `c = 0`, bound `0`.
-/

@[expose] public section

namespace BiluLinial.Tight

open MeasureTheory Matrix BiluLinial

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The matrix input of (ii): `c tr A²/(1 + cλ) ≤ tr A - tr(A (I + cA)⁻¹)` for `A ⪰ 0`,
`A ⪯ λ I`, `λ ≥ 0`, `c ≥ 0`. -/
theorem trace_sub_trace_mul_inv_ge {A : Matrix ι ι ℝ} (hA : A.PosSemidef) {l c : ℝ}
    (hl : 0 ≤ l) (hAl : (l • (1 : Matrix ι ι ℝ) - A).PosSemidef) (hc : 0 ≤ c) :
    c * (A * A).trace / (1 + c * l) ≤ A.trace - (A * (1 + c • A)⁻¹).trace := by
  have hKpd : (1 + c • A).PosDef := posDef_one_add (hA.smul hc)
  set R := (1 + c • A)⁻¹ with hRdef
  have hRK : R * (1 + c • A) = 1 :=
    Matrix.nonsing_inv_mul (A := 1 + c • A) (hKpd.isUnit.map Matrix.detMonoidHom)
  have hR : R.PosSemidef := hKpd.inv.posSemidef
  have h1R : 1 - R = c • (R * A) := by
    have h : R * (1 + c • A) = R + c • (R * A) := by rw [mul_add, mul_one, mul_smul_comm]
    rw [hRK] at h
    rw [h]; abel
  have htr1 : A.trace - (A * R).trace = c * (R * (A * A)).trace := by
    have h : A.trace - (A * R).trace = (A * (1 - R)).trace := by
      rw [mul_sub, mul_one, trace_sub]
    rw [h, h1R, mul_smul_comm, trace_smul, smul_eq_mul, trace_mul_comm A (R * A),
      Matrix.mul_assoc]
  have hAA : (A * A).trace = (R * (A * A)).trace + c * (R * (A * (A * A))).trace := by
    have h : A * A = R * (1 + c • A) * (A * A) := by rw [hRK, Matrix.one_mul]
    conv_lhs => rw [h]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, mul_smul_comm, smul_mul_assoc,
      trace_add, trace_smul, smul_eq_mul, Matrix.mul_assoc]
  have hP : (l • (A * A) - A * (A * A)).PosSemidef := by
    have h := hAl.conjTranspose_mul_mul_same A
    rw [hA.isHermitian.eq] at h
    have e : A * (l • (1 : Matrix ι ι ℝ) - A) * A = l • (A * A) - A * (A * A) := by
      simp only [Matrix.mul_sub, Matrix.sub_mul, mul_smul_comm, smul_mul_assoc, Matrix.mul_one,
        Matrix.mul_assoc]
    rwa [e] at h
  have hkey : (R * (A * (A * A))).trace ≤ l * (R * (A * A)).trace := by
    have h := trace_mul_nonneg hR hP
    rw [Matrix.mul_sub, trace_sub, mul_smul_comm, trace_smul, smul_eq_mul] at h
    linarith
  have hden : 0 < 1 + c * l := by positivity
  rw [htr1, div_le_iff₀ hden]
  nlinarith [mul_le_mul_of_nonneg_left hkey (mul_nonneg hc hc)]

omit [DecidableEq ι] in
theorem integrable_gaussPi_of_abs_le {f : (ι → ℝ) → ℝ} (hf : AEStronglyMeasurable f (gaussPi ι))
    {C : ℝ} (hb : ∀ x, |f x| ≤ C) : Integrable f (gaussPi ι) :=
  (integrable_const C).mono' hf (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hb x)

omit [DecidableEq ι] in
theorem integrable_clipProd_gaussPi {A B : Matrix ι ι ℝ} (hA : A.PosSemidef)
    (hB : B.PosSemidef) (m m' : ℕ) : Integrable (clipProd m m' A B) (gaussPi ι) :=
  integrable_gaussPi_of_abs_le (continuous_clipProd m m' A B).aestronglyMeasurable fun x => by
    rw [abs_of_nonneg (clipProd_nonneg m m' A B x)]; exact clipProd_le_one hA hB m m' x

omit [DecidableEq ι] in
theorem abs_clipProd_le_one {A B : Matrix ι ι ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (m m' : ℕ) (x : ι → ℝ) : |clipProd m m' A B x| ≤ 1 := by
  rw [abs_of_nonneg (clipProd_nonneg m m' A B x)]; exact clipProd_le_one hA hB m m' x

omit [DecidableEq ι] in
/-- `N_G = tr A · 𝖦 g - 𝖦[q_A g]` (and the same for any `T` in place of `A`). -/
theorem gaussE_trace_sub_qForm_mul {A B T : Matrix ι ι ℝ} (hA : A.PosSemidef)
    (hB : B.PosSemidef) (m m' : ℕ) :
    gaussE (fun x => (T.trace - qForm T x) * clipProd m m' A B x) =
      T.trace * gaussE (clipProd m m' A B) - gaussE (fun x => qForm T x * clipProd m m' A B x) := by
  unfold gaussE
  rw [← integral_const_mul, ← integral_sub ((integrable_clipProd_gaussPi hA hB m m').const_mul _)
    (integrable_qForm_mul_gaussPi T (continuous_clipProd m m' A B)
      (abs_clipProd_le_one hA hB m m'))]
  congr 1; funext x; ring

/-- **T.COV (ii).** `N_G ≥ 𝖦 g · 2(p-1) tr A²/(1 + 2(p-1)λ)` for `0 ≤ λ`, `A ⪯ λ I`. -/
theorem gaussE_NG_ge_of_le {A B : Matrix ι ι ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (p : ℕ) {l : ℝ} (hl : 0 ≤ l) (hAl : (l • (1 : Matrix ι ι ℝ) - A).PosSemidef) :
    gaussE (starG p A B) *
        (2 * ((p - 1 : ℕ) : ℝ) * (A * A).trace / (1 + 2 * ((p - 1 : ℕ) : ℝ) * l)) ≤
      gaussE (fun x => (A.trace - qForm A x) * starG p A B x) := by
  have hc : (0 : ℝ) ≤ 2 * ((p - 1 : ℕ) : ℝ) := by positivity
  have hBL := gaussE_qForm_mul_clipProd_le_const hA hB hA (p - 1) p hc le_rfl
  have hmat := trace_sub_trace_mul_inv_ge hA hl hAl hc
  have hG0 : 0 ≤ gaussE (starG p A B) := integral_nonneg (clipProd_nonneg _ _ A B)
  rw [gaussE_trace_sub_qForm_mul hA hB]
  calc gaussE (starG p A B) *
        (2 * ((p - 1 : ℕ) : ℝ) * (A * A).trace / (1 + 2 * ((p - 1 : ℕ) : ℝ) * l))
      ≤ gaussE (starG p A B) *
          (A.trace - (A * (1 + (2 * ((p - 1 : ℕ) : ℝ)) • A)⁻¹).trace) :=
        mul_le_mul_of_nonneg_left hmat hG0
    _ ≤ A.trace * gaussE (starG p A B) -
          gaussE (fun x => qForm A x * starG p A B x) := by
        have : gaussE (fun x => qForm A x * starG p A B x) ≤
            (A * (1 + (2 * ((p - 1 : ℕ) : ℝ)) • A)⁻¹).trace * gaussE (starG p A B) := hBL
        nlinarith

/-- **T.COV (ii)** with `λ = ‖A‖`: `N_G ≥ 𝖦 g · 2(p-1) tr A²/(1 + 2(p-1)‖A‖)`. -/
theorem gaussE_NG_ge_opNorm {A B : Matrix ι ι ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (p : ℕ) :
    gaussE (starG p A B) *
        (2 * ((p - 1 : ℕ) : ℝ) * (A * A).trace / (1 + 2 * ((p - 1 : ℕ) : ℝ) * opNorm A)) ≤
      gaussE (fun x => (A.trace - qForm A x) * starG p A B x) :=
  gaussE_NG_ge_of_le hA hB p (opNorm_nonneg A) (posSemidef_opNorm_smul_sub hA.isHermitian)

/-- **T.COV (ii)**, whitened form (AUDIT-A (C1b)): for `p ≥ 2`, `N_G ≥ f_G w` with
`f_G = 𝖦[α^p β^p]` and `w = tr A²/(1 + tr A)`. -/
theorem gaussE_NG_ge_whitened {A B : Matrix ι ι ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    {p : ℕ} (hp : 2 ≤ p) :
    gaussE (starPhi p A B) * ((A * A).trace / (1 + A.trace)) ≤
      gaussE (fun x => (A.trace - qForm A x) * starG p A B x) := by
  refine le_trans ?_ (gaussE_NG_ge_of_le hA hB p hA.trace_nonneg (posSemidef_trace_smul_sub hA))
  set c : ℝ := 2 * ((p - 1 : ℕ) : ℝ) with hcdef
  have hc1 : 1 ≤ c := by
    have : (1 : ℝ) ≤ ((p - 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ p - 1 by omega)
    linarith
  have hT := trace_mul_nonneg hA hA
  have htr := hA.trace_nonneg
  have hPhi_le : ∀ x, starPhi p A B x ≤ starG p A B x := fun x => by
    have ha0 := clipF_nonneg A x
    have ha1 := clipF_le_one hA x
    have h : clipF A x ^ p ≤ clipF A x ^ (p - 1) :=
      pow_le_pow_of_le_one ha0 ha1 (Nat.sub_le p 1)
    exact mul_le_mul_of_nonneg_right h (pow_nonneg (clipF_nonneg B x) p)
  have hPhiI : Integrable (starPhi p A B) (gaussPi ι) := integrable_clipProd_gaussPi hA hB p p
  have hG : gaussE (starPhi p A B) ≤ gaussE (starG p A B) :=
    integral_mono hPhiI (integrable_clipProd_gaussPi hA hB _ _) hPhi_le
  have hPhi0 : 0 ≤ gaussE (starPhi p A B) := integral_nonneg (clipProd_nonneg p p A B)
  have hfrac : (A * A).trace / (1 + A.trace) ≤ c * (A * A).trace / (1 + c * A.trace) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hc1 hT, mul_nonneg hT htr]
  exact mul_le_mul hG hfrac (by positivity) (hPhi0.trans hG)

/-- **T.COV (i).** `N_G = 𝖦[(tr A - q_A) α^{p-1} β^p] ≥ 0`. -/
theorem gaussE_NG_nonneg {A B : Matrix ι ι ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (p : ℕ) : 0 ≤ gaussE (fun x => (A.trace - qForm A x) * starG p A B x) := by
  refine le_trans ?_ (gaussE_NG_ge_opNorm hA hB p)
  have hG0 : 0 ≤ gaussE (starG p A B) := integral_nonneg (clipProd_nonneg _ _ A B)
  have hT := trace_mul_nonneg hA hA
  have hn := opNorm_nonneg A
  positivity

/-- **T.COV (iii) = B2.** For `p ≥ 3`, `0 ⪯ M ⪯ A`, `0 ⪯ N ⪯ B` and
`H = 2(p-1)M/α + 2pN/β`: `𝖦[g · tr(M(H - H²))] ≤ 2 𝖦 F`. -/
theorem gaussE_starG_trace_le {A B M N : Matrix ι ι ℝ} (hA : A.PosSemidef)
    (hB : B.PosSemidef) (hM : M.PosSemidef) (hN : N.PosSemidef) (hMA : (A - M).PosSemidef)
    (hNB : (B - N).PosSemidef) {p : ℕ} (hp : 3 ≤ p) :
    gaussE (fun x => starG p A B x * (M * (clipHess (p - 1) p A B M N x -
        clipHess (p - 1) p A B M N x * clipHess (p - 1) p A B M N x)).trace) ≤
      2 * gaussE (starF p A B) := by
  set H := clipHess (p - 1) p A B M N with hHdef
  have hHpsd : ∀ x, (H x).PosSemidef := clipHess_posSemidef hM hN (p - 1) p A B
  rw [two_mul_gaussE_starF hA hB hp]
  -- the `A - M` part: BLmid with `K = I`
  have hAM := gaussE_qForm_mul_clipProd_le_const hA hB hMA (p - 1) p le_rfl
    (by positivity : (0 : ℝ) ≤ 2 * ((p - 1 : ℕ) : ℝ))
  simp only [zero_smul, add_zero, inv_one, Matrix.mul_one] at hAM
  -- the `M` part: BLmid with `K = I + H`
  have hMv : gaussE (fun x => qForm M x * starG p A B x) ≤
      gaussE (fun x => (M * (1 + H x)⁻¹).trace * starG p A B x) :=
    gaussE_qForm_mul_clipProd_le hA hB hM hN hMA hNB hM (p - 1) p
  rw [trace_sub] at hAM
  change gaussE (fun x => qForm (A - M) x * starG p A B x) ≤
    (A.trace - M.trace) * gaussE (starG p A B) at hAM
  -- integrability
  have hg := continuous_clipProd (p - 1) p A B
  have hgb := abs_clipProd_le_one hA hB (p - 1) p
  have hqA := integrable_qForm_mul_gaussPi A hg hgb
  have hqM := integrable_qForm_mul_gaussPi M hg hgb
  have hqAM := integrable_qForm_mul_gaussPi (A - M) hg hgb
  have hRmem : ∀ x, 0 ≤ (M * (1 + H x)⁻¹).trace ∧ (M * (1 + H x)⁻¹).trace ≤ M.trace :=
    fun x => trace_mul_inv_one_add_mem hM (hHpsd x)
  have hRmeas : Measurable fun x => (M * (1 + H x)⁻¹).trace :=
    ((continuous_const.matrix_mul continuous_id).matrix_trace.measurable).comp
      (measurable_matrix_inv.comp (measurable_one_add_clipHess (p - 1) p A B M N))
  have hRI : Integrable (fun x => (M * (1 + H x)⁻¹).trace * starG p A B x) (gaussPi ι) := by
    refine integrable_gaussPi_of_abs_le (C := M.trace)
      (hRmeas.aestronglyMeasurable.mul hg.aestronglyMeasurable) fun x => ?_
    rw [abs_mul, abs_of_nonneg (hRmem x).1, abs_of_nonneg (clipProd_nonneg _ _ A B x)]
    exact (mul_le_of_le_one_right (hRmem x).1 (clipProd_le_one hA hB _ _ x)).trans (hRmem x).2
  have hgI := integrable_clipProd_gaussPi hA hB (p - 1) p
  -- lower bound for `N_G`
  have hNG : gaussE (fun x => (M.trace - (M * (1 + H x)⁻¹).trace) * starG p A B x) ≤
      gaussE (fun x => (A.trace - qForm A x) * starG p A B x) := by
    have e1 : gaussE (fun x => (M.trace - (M * (1 + H x)⁻¹).trace) * starG p A B x) =
        M.trace * gaussE (starG p A B) -
          gaussE (fun x => (M * (1 + H x)⁻¹).trace * starG p A B x) := by
      unfold gaussE
      rw [← integral_const_mul, ← integral_sub (hgI.const_mul _) hRI]
      congr 1; funext x; ring
    have e2 : gaussE (fun x => qForm A x * starG p A B x) =
        gaussE (fun x => qForm (A - M) x * starG p A B x) +
          gaussE (fun x => qForm M x * starG p A B x) := by
      unfold gaussE
      rw [← integral_add hqAM hqM]
      congr 1; funext x; rw [qForm_sub]; ring
    rw [e1, gaussE_trace_sub_qForm_mul hA hB, e2]
    linarith
  refine le_trans ?_ hNG
  by_cases hI : Integrable (fun x => starG p A B x *
      (M * (H x - H x * H x)).trace) (gaussPi ι)
  · have hJ : Integrable (fun x => (M.trace - (M * (1 + H x)⁻¹).trace) * starG p A B x)
        (gaussPi ι) := by
      refine ((hgI.const_mul M.trace).sub hRI).congr (ae_of_all _ fun x => ?_)
      change M.trace * starG p A B x - (M * (1 + H x)⁻¹).trace * starG p A B x =
        (M.trace - (M * (1 + H x)⁻¹).trace) * starG p A B x
      ring
    refine integral_mono hI hJ fun x => ?_
    · have h := trace_mul_sub_sq_le hM (hHpsd x)
      have hg0 := clipProd_nonneg (p - 1) p A B x
      change starG p A B x * (M * (H x - H x * H x)).trace ≤
        (M.trace - (M * (1 + H x)⁻¹).trace) * starG p A B x
      nlinarith [mul_le_mul_of_nonneg_left h hg0]
  · rw [show gaussE (fun x => starG p A B x * (M * (H x - H x * H x)).trace) = 0 from
      integral_undef hI]
    exact integral_nonneg fun x =>
      mul_nonneg (sub_nonneg.2 (hRmem x).2) (clipProd_nonneg _ _ A B x)

/-- **B2**, expanded (source display (B2)):
`𝖦 F ≥ 𝖦[Φ {(p-1) tr M²/α² + p tr(MN)/(αβ) - tr(M H²)/(2α)}]`. -/
theorem gaussE_starPhi_B2_le {A B M N : Matrix ι ι ℝ} (hA : A.PosSemidef)
    (hB : B.PosSemidef) (hM : M.PosSemidef) (hN : N.PosSemidef) (hMA : (A - M).PosSemidef)
    (hNB : (B - N).PosSemidef) {p : ℕ} (hp : 3 ≤ p) :
    gaussE (fun x => starPhi p A B x *
        (((p - 1 : ℕ) : ℝ) * (M * M).trace / clipF A x ^ 2 +
          (p : ℝ) * (M * N).trace / (clipF A x * clipF B x) -
          (M * (clipHess (p - 1) p A B M N x * clipHess (p - 1) p A B M N x)).trace /
            (2 * clipF A x))) ≤
      gaussE (starF p A B) := by
  have hpt : ∀ x, starPhi p A B x *
        (((p - 1 : ℕ) : ℝ) * (M * M).trace / clipF A x ^ 2 +
          (p : ℝ) * (M * N).trace / (clipF A x * clipF B x) -
          (M * (clipHess (p - 1) p A B M N x * clipHess (p - 1) p A B M N x)).trace /
            (2 * clipF A x)) =
      1 / 2 * (starG p A B x * (M * (clipHess (p - 1) p A B M N x -
        clipHess (p - 1) p A B M N x * clipHess (p - 1) p A B M N x)).trace) := by
    intro x
    have htrH1 : (M * clipHess (p - 1) p A B M N x).trace =
        2 * ((p - 1 : ℕ) : ℝ) / clipF A x * (M * M).trace +
          2 * (p : ℝ) / clipF B x * (M * N).trace := by
      simp only [clipHess, Matrix.mul_add, mul_smul_comm, trace_add, trace_smul, smul_eq_mul]
    rw [Matrix.mul_sub, trace_sub, htrH1]
    set T2 := (M * (clipHess (p - 1) p A B M N x * clipHess (p - 1) p A B M N x)).trace
    clear_value T2
    simp only [starPhi, starG, clipProd]
    have ha0 := clipF_nonneg A x
    have hb0 := clipF_nonneg B x
    rcases ha0.eq_or_lt with ha | ha
    · rw [← ha]; simp [zero_pow (show p ≠ 0 by omega), zero_pow (show p - 1 ≠ 0 by omega)]
    rcases hb0.eq_or_lt with hb | hb
    · rw [← hb]; simp [zero_pow (show p ≠ 0 by omega)]
    have e : clipF A x ^ p = clipF A x ^ (p - 1) * clipF A x := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega)]
    rw [e]
    set u := clipF A x ^ (p - 1)
    set v := clipF B x ^ p
    clear_value u v
    field_simp
  simp only [hpt]
  unfold gaussE
  rw [integral_const_mul]
  have h := gaussE_starG_trace_le hA hB hM hN hMA hNB hp
  unfold gaussE at h
  linarith

end BiluLinial.Tight
