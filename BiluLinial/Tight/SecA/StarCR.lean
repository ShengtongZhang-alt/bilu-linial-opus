/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecA.StarSmooth
public import BiluLinial.Tight.Tools.GIBP2

/-!
# The Cramér–Rao form (C4) (`A-CR`)

Node `A-CR` of `docs/tight/BP_SECA.md` (source lines 456–478; AUDIT-A §2.12). For PSD `A, B, M`
and `p ≥ 3`, with `α = (1 - q_A)₊`, `β = (1 - q_B)₊`, `Φ = α^p β^p`:

  `𝖦[(tr M - q_M) Φ] ≤ 2p 𝖦[tr(MA) α^{p-1}β^p + tr(MB) α^p β^{p-1}]
      + 4p 𝖦[q_{AMA} α^{p-2}β^p + q_{BMB} α^p β^{p-2}]`.

**Route (no matrix inverse is needed).** The paper derives (C4) from the Cramér–Rao bound
`Σ ⪰ (I + 𝔼∇²V)⁻¹`; only its consequence `I - Σ ⪯ 𝔼∇²V` is used, and that follows from three
Gaussian integrations by parts. The generic Stein identity (`gaussE_qForm_clip`, from
`𝖦[x_i f_i] = 𝖦[∂_i f_i]` with `f_i = (Nx)_i α^a β^b`, `a, b ≥ 2`) reads

  `𝖦[q_N α^a β^b] = tr N 𝖦[α^a β^b] - 2a 𝖦[q_{AN} α^{a-1}β^b] - 2b 𝖦[q_{BN} α^a β^{b-1}]`.

Applied with `N = M` (`a = b = p`), then `N = MA` (`a = p-1, b = p`) and `N = MB`
(`a = p, b = p-1`), and using `q_{AM} = q_{MA}`, it gives

  `RHS - LHS = 4p² 𝖦[α^{p-2}β^{p-2} q_M(β A x + α B x)] ≥ 0`

(the Fisher-information term `𝖦[∇Φᵀ M ∇Φ / Φ]`).
-/

@[expose] public section

namespace BiluLinial.Tight.SecA.StarCalc

open Matrix MeasureTheory Filter Topology Function
open scoped ContDiff

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem abs_entry_le_sum (N : Matrix ι ι ℝ) (i j : ι) : |N i j| ≤ ∑ k, ∑ l, |N k l| :=
  calc |N i j| ≤ ∑ l, |N i l| :=
        Finset.single_le_sum (f := fun l => |N i l|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ k, ∑ l, |N k l| := Finset.single_le_sum (f := fun k => ∑ l, |N k l|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)

theorem pderiv_mulVec_apply (M : Matrix ι ι ℝ) (i j : ι) :
    pderiv j (fun x : ι → ℝ => (M *ᵥ x) i) = fun _ => M i j := by
  simpa using pderiv_affine 0 M i j

theorem pderiv_one_sub_qForm {A : Matrix ι ι ℝ} (hA : Aᵀ = A) (i : ι) :
    pderiv i (fun x : ι → ℝ => 1 - qForm A x) = fun x => -(2 * (A *ᵥ x) i) := by
  have e : (fun x : ι → ℝ => 1 - qForm A x) = quadFn 1 0 (-A) :=
    funext fun x => (quadFn_one_zero_neg A x).symm
  rw [e, pderiv_quadFn]
  funext x
  rw [transpose_neg, hA, add_mulVec, neg_mulVec]
  simp only [Pi.zero_apply, Pi.add_apply, Pi.neg_apply]
  ring

omit [DecidableEq ι] in
theorem contDiff_mulVec_apply (N : Matrix ι ι ℝ) (i : ι) :
    ContDiff ℝ ∞ (fun x : ι → ℝ => (N *ᵥ x) i) := by
  simp only [mulVec, dotProduct]
  fun_prop

/-- `∂_i ((Nx)_i α^a β^b) = N_ii α^a β^b - 2a (Nx)_i (Ax)_i α^{a-1}β^b
- 2b (Nx)_i (Bx)_i α^a β^{b-1}` for symmetric `A, B` and `a, b ≥ 2`. -/
theorem pderiv_steinTerm {A B : Matrix ι ι ℝ} (hA : Aᵀ = A) (hB : Bᵀ = B) (N : Matrix ι ι ℝ)
    {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) (i : ι) :
    pderiv i (fun x => (N *ᵥ x) i * clipF A x ^ a * clipF B x ^ b) = fun x =>
      N i i * clipF A x ^ a * clipF B x ^ b -
        2 * a * ((N *ᵥ x) i * (A *ᵥ x) i) * clipF A x ^ (a - 1) * clipF B x ^ b -
        2 * b * ((N *ᵥ x) i * (B *ᵥ x) i) * clipF A x ^ a * clipF B x ^ (b - 1) := by
  have hφ : ContDiff ℝ ∞ (fun x : ι → ℝ => 1 - qForm A x) :=
    contDiff_const.sub (contDiff_qForm A)
  have hψ : ContDiff ℝ ∞ (fun x : ι → ℝ => 1 - qForm B x) :=
    contDiff_const.sub (contDiff_qForm B)
  have h := pderiv_clipTerm (contDiff_mulVec_apply N i) hφ hψ ha hb i
  change pderiv i (fun x => (N *ᵥ x) i * max (1 - qForm A x) 0 ^ a *
    max (1 - qForm B x) 0 ^ b) = _
  rw [h, pderiv_mulVec_apply, pderiv_one_sub_qForm hA, pderiv_one_sub_qForm hB]
  funext x
  simp only [Pi.add_apply, clipF]
  ring

theorem stein_bound_aux {cN cA cB a b s : ℝ} (hN : 0 ≤ cN) (hA : 0 ≤ cA) (hB : 0 ≤ cB)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hs : 0 ≤ s) :
    cN + 2 * a * (cN * s * (cA * s)) + 2 * b * (cN * s * (cB * s)) ≤
      cN * (1 + 2 * (a + b) * (cA + cB)) * (1 + s) ^ 2 := by
  have hS1 : 1 ≤ (1 + s) ^ 2 := by nlinarith
  have hS2 : s * s ≤ (1 + s) ^ 2 := by nlinarith
  have h1 : a * cA + b * cB ≤ (a + b) * (cA + cB) := by
    nlinarith [mul_nonneg ha hB, mul_nonneg hb hA]
  have h3 : (a * cA + b * cB) * (s * s) ≤ ((a + b) * (cA + cB)) * (1 + s) ^ 2 :=
    mul_le_mul h1 hS2 (by positivity) (by positivity)
  have e : cN + 2 * a * (cN * s * (cA * s)) + 2 * b * (cN * s * (cB * s)) =
      cN * 1 + 2 * cN * ((a * cA + b * cB) * (s * s)) := by ring
  have e2 : cN * (1 + 2 * (a + b) * (cA + cB)) * (1 + s) ^ 2 =
      cN * (1 + s) ^ 2 + 2 * cN * (((a + b) * (cA + cB)) * (1 + s) ^ 2) := by ring
  rw [e, e2]
  have h4 := mul_le_mul_of_nonneg_left hS1 hN
  have h5 := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 2 * cN)
  linarith

theorem abs_add_neg_neg_le {x y z X Y Z : ℝ} (hx : |x| ≤ X) (hy : |y| ≤ Y) (hz : |z| ≤ Z) :
    |x + -y + -z| ≤ X + Y + Z := by
  have h1 := abs_add_le (x + -y) (-z)
  have h2 := abs_add_le x (-y)
  rw [abs_neg] at h1 h2
  linarith

/-- The generic Gaussian integration by parts for clipped weights (`a, b ≥ 2`, `A, B ⪰ 0`):
`𝖦[q_N α^a β^b] = tr N 𝖦[α^a β^b] - 2a 𝖦[q_{AN} α^{a-1}β^b] - 2b 𝖦[q_{BN} α^a β^{b-1}]`. -/
theorem gaussE_qForm_clip {A B : Matrix ι ι ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (N : Matrix ι ι ℝ) {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    gaussE (fun x => qForm N x * (clipF A x ^ a * clipF B x ^ b)) =
      N.trace * gaussE (fun x => clipF A x ^ a * clipF B x ^ b) -
        2 * a * gaussE (fun x => qForm (A * N) x * (clipF A x ^ (a - 1) * clipF B x ^ b)) -
        2 * b * gaussE (fun x => qForm (B * N) x * (clipF A x ^ a * clipF B x ^ (b - 1))) := by
  have hAt := psd_transpose hA
  have hBt := psd_transpose hB
  have hcA := continuous_clipF A
  have hcB := continuous_clipF B
  have hP : ∀ m n : ℕ, Continuous (fun x => clipF A x ^ m * clipF B x ^ n) :=
    fun m n => (hcA.pow m).mul (hcB.pow n)
  have hPa : ∀ (m n : ℕ) x, |clipF A x ^ m * clipF B x ^ n| ≤ 1 := fun m n x => by
    rw [abs_of_nonneg (mul_nonneg (pow_nonneg (clipF_nonneg A x) m)
      (pow_nonneg (clipF_nonneg B x) n))]
    exact clipProd_le_one hA hB m n x
  have hIc : ∀ m n : ℕ, Integrable (fun x => clipF A x ^ m * clipF B x ^ n) (gaussPi ι) :=
    fun m n => (integrable_const (1 : ℝ)).mono' (hP m n).aestronglyMeasurable
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hPa m n x)
  have hIq : ∀ (T : Matrix ι ι ℝ) (m n : ℕ),
      Integrable (fun x => qForm T x * (clipF A x ^ m * clipF B x ^ n)) (gaussPi ι) :=
    fun T m n => integrable_qForm_mul_gaussPi T (hP m n) (hPa m n)
  have hcv : ∀ (T : Matrix ι ι ℝ) (i : ι), Continuous fun x : ι → ℝ => (T *ᵥ x) i :=
    fun T i => (contDiff_mulVec_apply T i).continuous
  set cN := ∑ j, ∑ k, |N j k| with hcN
  set cA := ∑ j, ∑ k, |A j k| with hcA'
  set cB := ∑ j, ∑ k, |B j k| with hcB'
  have hcN0 : 0 ≤ cN := by positivity
  have hcA0 : 0 ≤ cA := by positivity
  have hcB0 : 0 ≤ cB := by positivity
  set K : ℝ := cN * (1 + 2 * (a + b) * (cA + cB)) with hK
  have hKN : cN ≤ K := le_mul_of_one_le_right hcN0 (by
    have : 0 ≤ 2 * ((a : ℝ) + b) * (cA + cB) := by positivity
    linarith)
  set f : ι → (ι → ℝ) → ℝ := fun i x => (N *ᵥ x) i * clipF A x ^ a * clipF B x ^ b with hf
  set g : ι → (ι → ℝ) → ℝ := fun i x => N i i * clipF A x ^ a * clipF B x ^ b -
      2 * a * ((N *ᵥ x) i * (A *ᵥ x) i) * clipF A x ^ (a - 1) * clipF B x ^ b -
      2 * b * ((N *ᵥ x) i * (B *ᵥ x) i) * clipF A x ^ a * clipF B x ^ (b - 1) with hg
  have hfd : ∀ i, Differentiable ℝ (f i) := fun i x =>
    (hasFDerivAt_clipTerm (contDiff_mulVec_apply N i) (contDiff_const.sub (contDiff_qForm A))
      (contDiff_const.sub (contDiff_qForm B)) ha hb x).differentiableAt
  have hfg : ∀ i, pderiv i (f i) = g i := fun i => pderiv_steinTerm hAt hBt N ha hb i
  have hfc : ∀ i, Continuous (f i) := fun i => ((hcv N i).mul (hcA.pow a)).mul (hcB.pow b)
  have hgc : ∀ i, Continuous (g i) := fun i => by
    have h1 := hcv N i
    have h2 := hcv A i
    have h3 := hcv B i
    simp only [hg]
    fun_prop
  have hxn : ∀ x : ι → ℝ, ‖x‖ ≤ (1 + ‖x‖) ^ 2 := fun x => by nlinarith [norm_nonneg x]
  have hfb : ∀ i x, ‖f i x‖ ≤ K * (1 + ‖x‖) ^ 2 := by
    intro i x
    have h1 := abs_mulVec_apply_le N x i
    have e : f i x = (N *ᵥ x) i * (clipF A x ^ a * clipF B x ^ b) := by
      simp only [hf]; ring
    rw [e, Real.norm_eq_abs, abs_mul]
    calc |(N *ᵥ x) i| * |clipF A x ^ a * clipF B x ^ b| ≤ cN * ‖x‖ * 1 :=
          mul_le_mul h1 (hPa a b x) (abs_nonneg _) (by positivity)
      _ ≤ K * (1 + ‖x‖) ^ 2 := by
          rw [mul_one]
          exact mul_le_mul hKN (hxn x) (norm_nonneg x) (hcN0.trans hKN)
  have hgb : ∀ i x, ‖g i x‖ ≤ K * (1 + ‖x‖) ^ 2 := by
    intro i x
    have h0 := abs_entry_le_sum N i i
    have h1 := abs_mulVec_apply_le N x i
    have h2 := abs_mulVec_apply_le A x i
    have h3 := abs_mulVec_apply_le B x i
    have hx := norm_nonneg x
    have e : g i x = N i i * (clipF A x ^ a * clipF B x ^ b) +
        -(2 * a * ((N *ᵥ x) i * (A *ᵥ x) i) * (clipF A x ^ (a - 1) * clipF B x ^ b)) +
        -(2 * b * ((N *ᵥ x) i * (B *ᵥ x) i) * (clipF A x ^ a * clipF B x ^ (b - 1))) := by
      simp only [hg]; ring
    have t1 : |N i i * (clipF A x ^ a * clipF B x ^ b)| ≤ cN := by
      rw [abs_mul]
      exact (mul_le_of_le_one_right (abs_nonneg _) (hPa a b x)).trans h0
    have t2 : |2 * a * ((N *ᵥ x) i * (A *ᵥ x) i) * (clipF A x ^ (a - 1) * clipF B x ^ b)| ≤
        2 * a * (cN * ‖x‖ * (cA * ‖x‖)) := by
      have hX : |(N *ᵥ x) i * (A *ᵥ x) i| ≤ cN * ‖x‖ * (cA * ‖x‖) := by
        rw [abs_mul]
        exact mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
      rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * a)]
      calc 2 * (a : ℝ) * |(N *ᵥ x) i * (A *ᵥ x) i| * |clipF A x ^ (a - 1) * clipF B x ^ b|
          ≤ 2 * a * (cN * ‖x‖ * (cA * ‖x‖)) * 1 :=
            mul_le_mul (mul_le_mul_of_nonneg_left hX (by positivity)) (hPa _ _ x)
              (abs_nonneg _) (by positivity)
        _ = _ := mul_one _
    have t3 : |2 * b * ((N *ᵥ x) i * (B *ᵥ x) i) * (clipF A x ^ a * clipF B x ^ (b - 1))| ≤
        2 * b * (cN * ‖x‖ * (cB * ‖x‖)) := by
      have hX : |(N *ᵥ x) i * (B *ᵥ x) i| ≤ cN * ‖x‖ * (cB * ‖x‖) := by
        rw [abs_mul]
        exact mul_le_mul h1 h3 (abs_nonneg _) (by positivity)
      rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * b)]
      calc 2 * (b : ℝ) * |(N *ᵥ x) i * (B *ᵥ x) i| * |clipF A x ^ a * clipF B x ^ (b - 1)|
          ≤ 2 * b * (cN * ‖x‖ * (cB * ‖x‖)) * 1 :=
            mul_le_mul (mul_le_mul_of_nonneg_left hX (by positivity)) (hPa _ _ x)
              (abs_nonneg _) (by positivity)
        _ = _ := mul_one _
    rw [e, Real.norm_eq_abs]
    exact (abs_add_neg_neg_le t1 t2 t3).trans
      (stein_bound_aux hcN0 hcA0 hcB0 (Nat.cast_nonneg a) (Nat.cast_nonneg b) hx)
  have hstein : ∀ i, ∫ x, x i * f i x ∂gaussPi ι = ∫ x, g i x ∂gaussPi ι := fun i =>
    stein_gaussPi_of_hasDerivAt i (hfc i).aestronglyMeasurable (hgc i).aestronglyMeasurable
      (fun x t => by rw [← hfg i]; exact hasDerivAt_slice (hfd i) x i t) (hfb i) (hgb i)
  have hint1 : ∀ i, Integrable (fun x => x i * f i x) (gaussPi ι) := fun i =>
    integrable_of_polyBound_gaussPi ((continuous_apply i).mul (hfc i)).aestronglyMeasurable
      (norm_coord_mul_le (hfb i) i)
  have hint2 : ∀ i, Integrable (g i) (gaussPi ι) := fun i =>
    integrable_of_polyBound_gaussPi (hgc i).aestronglyMeasurable (hgb i)
  have e1 : (fun x => qForm N x * (clipF A x ^ a * clipF B x ^ b)) =
      fun x => ∑ i, x i * f i x := by
    funext x
    simp only [hf, qForm, dotProduct, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hTN : ∀ (T : Matrix ι ι ℝ), T.IsHermitian → ∀ x,
      ∑ i, (N *ᵥ x) i * (T *ᵥ x) i = qForm (T * N) x := fun T hT x => by
    rw [qForm, ← mulVec_mulVec, dotProduct_mulVec_comm_of_symm hT, dotProduct]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have e2 : ∀ x, ∑ i, g i x = N.trace * (clipF A x ^ a * clipF B x ^ b) -
      2 * a * (qForm (A * N) x * (clipF A x ^ (a - 1) * clipF B x ^ b)) -
      2 * b * (qForm (B * N) x * (clipF A x ^ a * clipF B x ^ (b - 1))) := by
    intro x
    rw [← hTN A hA.isHermitian x, ← hTN B hB.isHermitian x]
    have hgi : ∀ i, g i x = (clipF A x ^ a * clipF B x ^ b) * N i i -
        (2 * a * (clipF A x ^ (a - 1) * clipF B x ^ b)) * ((N *ᵥ x) i * (A *ᵥ x) i) -
        (2 * b * (clipF A x ^ a * clipF B x ^ (b - 1))) * ((N *ᵥ x) i * (B *ᵥ x) i) :=
      fun i => by simp only [hg]; ring
    simp only [hgi, Finset.sum_sub_distrib, ← Finset.mul_sum, trace, diag]
    ring
  have iA : Integrable (fun x => N.trace * (clipF A x ^ a * clipF B x ^ b)) (gaussPi ι) :=
    (hIc a b).const_mul _
  have iB : Integrable (fun x => 2 * (a : ℝ) *
      (qForm (A * N) x * (clipF A x ^ (a - 1) * clipF B x ^ b))) (gaussPi ι) :=
    (hIq _ _ _).const_mul _
  have iC : Integrable (fun x => 2 * (b : ℝ) *
      (qForm (B * N) x * (clipF A x ^ a * clipF B x ^ (b - 1)))) (gaussPi ι) :=
    (hIq _ _ _).const_mul _
  unfold gaussE
  rw [e1, integral_finsetSum _ fun i _ => hint1 i, Finset.sum_congr rfl fun i _ => hstein i,
    ← integral_finsetSum _ fun i _ => hint2 i]
  simp only [e2]
  rw [integral_sub, integral_sub, integral_const_mul, integral_const_mul, integral_const_mul]
  all_goals first | exact iA | exact iB | exact iC | exact iA.sub iB

omit [DecidableEq ι] in
theorem gaussE_add {f g : (ι → ℝ) → ℝ} (hf : Integrable f (gaussPi ι))
    (hg : Integrable g (gaussPi ι)) : gaussE (fun x => f x + g x) = gaussE f + gaussE g :=
  integral_add hf hg

/-- **A-CR**: the Cramér–Rao form (C4) of the Gaussian bias of `(tr M - q_M) Φ`. -/
theorem gaussE_C4' {A B M : Matrix ι ι ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hM : M.PosSemidef) {p : ℕ} (hp : 3 ≤ p) :
    gaussE (fun x => (M.trace - qForm M x) * starPhi p A B x) ≤
      2 * p * gaussE (fun x => (M * A).trace * clipF A x ^ (p - 1) * clipF B x ^ p +
          (M * B).trace * clipF A x ^ p * clipF B x ^ (p - 1)) +
        4 * p * gaussE (fun x => qForm (A * M * A) x * clipF A x ^ (p - 2) * clipF B x ^ p +
          qForm (B * M * B) x * clipF A x ^ p * clipF B x ^ (p - 2)) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 2 := ⟨p - 2, by omega⟩
  have hq1 : q + 2 - 1 = q + 1 := rfl
  have hq2 : q + 2 - 2 = q := rfl
  have hq3 : q + 1 - 1 = q := rfl
  rw [hq1, hq2]
  have hcA := continuous_clipF A
  have hcB := continuous_clipF B
  have hP : ∀ m n : ℕ, Continuous (fun x => clipF A x ^ m * clipF B x ^ n) :=
    fun m n => (hcA.pow m).mul (hcB.pow n)
  have hPa : ∀ (m n : ℕ) x, |clipF A x ^ m * clipF B x ^ n| ≤ 1 := fun m n x => by
    rw [abs_of_nonneg (mul_nonneg (pow_nonneg (clipF_nonneg A x) m)
      (pow_nonneg (clipF_nonneg B x) n))]
    exact clipProd_le_one hA hB m n x
  have hIc : ∀ m n : ℕ, Integrable (fun x => clipF A x ^ m * clipF B x ^ n) (gaussPi ι) :=
    fun m n => (integrable_const (1 : ℝ)).mono' (hP m n).aestronglyMeasurable
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hPa m n x)
  have hIq : ∀ (T : Matrix ι ι ℝ) (m n : ℕ),
      Integrable (fun x => qForm T x * (clipF A x ^ m * clipF B x ^ n)) (gaussPi ι) :=
    fun T m n => integrable_qForm_mul_gaussPi T (hP m n) (hPa m n)
  -- the three Stein identities
  have G1 := gaussE_qForm_clip hA hB M (a := q + 2) (b := q + 2) (by omega) (by omega)
  have G2 := gaussE_qForm_clip hA hB (M * A) (a := q + 1) (b := q + 2) (by omega) (by omega)
  have G3 := gaussE_qForm_clip hA hB (M * B) (a := q + 2) (b := q + 1) (by omega) (by omega)
  rw [hq1] at G1
  rw [hq3, hq1] at G2
  rw [hq1, hq3] at G3
  have eTM : ∀ (T : Matrix ι ι ℝ), T.IsHermitian → ∀ x, qForm (T * M) x = qForm (M * T) x :=
    fun T hT x => by
      rw [qForm, qForm, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec_comm_of_symm hT,
        dotProduct_mulVec_comm_of_symm hM.isHermitian, dotProduct_comm]
  simp only [eTM A hA.isHermitian, eTM B hB.isHermitian] at G1
  -- linearity of the outer integrals
  have hL : gaussE (fun x => (M.trace - qForm M x) * starPhi (q + 2) A B x) =
      M.trace * gaussE (fun x => clipF A x ^ (q + 2) * clipF B x ^ (q + 2)) -
        gaussE (fun x => qForm M x * (clipF A x ^ (q + 2) * clipF B x ^ (q + 2))) := by
    unfold gaussE starPhi
    rw [← integral_const_mul, ← integral_sub ((hIc _ _).const_mul _) (hIq M _ _)]
    congr 1
    funext x
    ring
  have hR1 : gaussE (fun x => (M * A).trace * clipF A x ^ (q + 1) * clipF B x ^ (q + 2) +
      (M * B).trace * clipF A x ^ (q + 2) * clipF B x ^ (q + 1)) =
      (M * A).trace * gaussE (fun x => clipF A x ^ (q + 1) * clipF B x ^ (q + 2)) +
        (M * B).trace * gaussE (fun x => clipF A x ^ (q + 2) * clipF B x ^ (q + 1)) := by
    unfold gaussE
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add ((hIc _ _).const_mul _) ((hIc _ _).const_mul _)]
    congr 1
    funext x
    ring
  have hR2 : gaussE (fun x => qForm (A * M * A) x * clipF A x ^ q * clipF B x ^ (q + 2) +
      qForm (B * M * B) x * clipF A x ^ (q + 2) * clipF B x ^ q) =
      gaussE (fun x => qForm (A * (M * A)) x * (clipF A x ^ q * clipF B x ^ (q + 2))) +
        gaussE (fun x => qForm (B * (M * B)) x * (clipF A x ^ (q + 2) * clipF B x ^ q)) := by
    unfold gaussE
    rw [← integral_add (hIq _ _ _) (hIq _ _ _)]
    congr 1
    funext x
    rw [Matrix.mul_assoc A M A, Matrix.mul_assoc B M B]
    ring
  -- the Fisher-information term is nonnegative
  have hpt : ∀ x, 0 ≤ qForm (A * (M * A)) x * (clipF A x ^ q * clipF B x ^ (q + 2)) +
      qForm (B * (M * B)) x * (clipF A x ^ (q + 2) * clipF B x ^ q) +
      qForm (B * (M * A)) x * (clipF A x ^ (q + 1) * clipF B x ^ (q + 1)) +
      qForm (A * (M * B)) x * (clipF A x ^ (q + 1) * clipF B x ^ (q + 1)) := by
    intro x
    have hAh := hA.isHermitian
    have hBh := hB.isHermitian
    have e1 : qForm (A * (M * A)) x = (A *ᵥ x) ⬝ᵥ (M *ᵥ (A *ᵥ x)) := by
      rw [qForm, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec_comm_of_symm hAh]
    have e2 : qForm (B * (M * B)) x = (B *ᵥ x) ⬝ᵥ (M *ᵥ (B *ᵥ x)) := by
      rw [qForm, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec_comm_of_symm hBh]
    have e3 : qForm (B * (M * A)) x = (B *ᵥ x) ⬝ᵥ (M *ᵥ (A *ᵥ x)) := by
      rw [qForm, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec_comm_of_symm hBh]
    have e4 : qForm (A * (M * B)) x = (A *ᵥ x) ⬝ᵥ (M *ᵥ (B *ᵥ x)) := by
      rw [qForm, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec_comm_of_symm hAh]
    have ew : qForm M (clipF B x • (A *ᵥ x) + clipF A x • (B *ᵥ x)) =
        clipF B x ^ 2 * ((A *ᵥ x) ⬝ᵥ (M *ᵥ (A *ᵥ x))) +
          clipF A x * clipF B x * ((A *ᵥ x) ⬝ᵥ (M *ᵥ (B *ᵥ x)) +
            (B *ᵥ x) ⬝ᵥ (M *ᵥ (A *ᵥ x))) +
          clipF A x ^ 2 * ((B *ᵥ x) ⬝ᵥ (M *ᵥ (B *ᵥ x))) := by
      simp only [qForm, mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct,
        dotProduct_smul, smul_dotProduct, smul_eq_mul]
      ring
    have key : qForm (A * (M * A)) x * (clipF A x ^ q * clipF B x ^ (q + 2)) +
        qForm (B * (M * B)) x * (clipF A x ^ (q + 2) * clipF B x ^ q) +
        qForm (B * (M * A)) x * (clipF A x ^ (q + 1) * clipF B x ^ (q + 1)) +
        qForm (A * (M * B)) x * (clipF A x ^ (q + 1) * clipF B x ^ (q + 1)) =
        clipF A x ^ q * clipF B x ^ q *
          qForm M (clipF B x • (A *ᵥ x) + clipF A x • (B *ᵥ x)) := by
      rw [e1, e2, e3, e4, ew]
      ring
    rw [key]
    exact mul_nonneg (mul_nonneg (pow_nonneg (clipF_nonneg A x) q)
      (pow_nonneg (clipF_nonneg B x) q)) (qForm_nonneg hM _)
  have hNN : 0 ≤
      gaussE (fun x => qForm (A * (M * A)) x * (clipF A x ^ q * clipF B x ^ (q + 2))) +
      gaussE (fun x => qForm (B * (M * B)) x * (clipF A x ^ (q + 2) * clipF B x ^ q)) +
      gaussE (fun x => qForm (B * (M * A)) x * (clipF A x ^ (q + 1) * clipF B x ^ (q + 1))) +
      gaussE (fun x => qForm (A * (M * B)) x * (clipF A x ^ (q + 1) * clipF B x ^ (q + 1))) := by
    have h : 0 ≤ gaussE (fun x =>
        qForm (A * (M * A)) x * (clipF A x ^ q * clipF B x ^ (q + 2)) +
        qForm (B * (M * B)) x * (clipF A x ^ (q + 2) * clipF B x ^ q) +
        qForm (B * (M * A)) x * (clipF A x ^ (q + 1) * clipF B x ^ (q + 1)) +
        qForm (A * (M * B)) x * (clipF A x ^ (q + 1) * clipF B x ^ (q + 1))) :=
      integral_nonneg fun x => hpt x
    rw [gaussE_add, gaussE_add, gaussE_add] at h
    · exact h
    all_goals first
      | exact hIq _ _ _
      | exact (hIq _ _ _).add (hIq _ _ _)
      | exact ((hIq _ _ _).add (hIq _ _ _)).add (hIq _ _ _)
  rw [hL, hR1, hR2]
  push_cast at G1 G2 G3 ⊢
  have hq0 : (0 : ℝ) ≤ 4 * ((q : ℝ) + 2) ^ 2 := by positivity
  have hF := mul_nonneg hq0 hNN
  linear_combination hF - G1 + 2 * ((q : ℝ) + 2) * G2 + 2 * ((q : ℝ) + 2) * G3

end BiluLinial.Tight.SecA.StarCalc
