/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.Gauss.Basic

/-!
# Gaussian integration by parts (Stein's lemma)

Part D (`docs/second_order_bilu_linial_tight.tex`) uses Gaussian integration by parts on
`ι → ℝ` (`ι` finite) under the standard Gaussian `gaussPi ι`. This file proves:

* moments: polynomially bounded functions are integrable under `gaussianReal 0 1` and
  `gaussPi ι`; the even moments are `(2k-1)‼` and the odd moments vanish;
* `measurePreserving_update`: resampling one coordinate of a product measure preserves it,
  which gives the Fubini splitting `integral_gaussPi_eq_integral_update`;
* `stein_gaussianReal`: `𝔼[X f(X)] = 𝔼[f'(X)]` for a standard normal `X`;
* `stein_gaussPi`: `𝔼[X_i f(X)] = 𝔼[∂_i f(X)]` on `ι → ℝ`;
* `stein_two_gaussPi`: `𝔼[(X_i X_j - δ_ij) f(X)] = 𝔼[∂_i ∂_j f(X)]`.

Polynomial bounds are written `‖f x‖ ≤ K * (1 + ‖x‖) ^ m`, with the sup norm on `ι → ℝ`.
-/

@[expose] public section

namespace BiluLinial.Tight

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal Nat

variable {ι : Type*} [Fintype ι]

/-! ### Moments and integrability -/

/-- All absolute moments of the standard Gaussian are finite. -/
theorem integrable_abs_pow_gaussianReal (m : ℕ) :
    Integrable (fun x : ℝ => |x| ^ m) (gaussianReal 0 1) := by
  simpa [Real.norm_eq_abs] using
    (memLp_id_gaussianReal' (μ := 0) (v := 1) (m : ℝ≥0∞)
      (ENNReal.natCast_ne_top m)).integrable_norm_pow'

/-- `(1 + |x|) ^ m` is integrable under the standard Gaussian. -/
theorem integrable_one_add_abs_pow_gaussianReal (m : ℕ) :
    Integrable (fun x : ℝ => (1 + |x|) ^ m) (gaussianReal 0 1) := by
  refine (((integrable_const (1 : ℝ)).add (integrable_abs_pow_gaussianReal m)).const_mul
    (2 ^ (m - 1))).mono' (by fun_prop) (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  simpa using add_pow_le zero_le_one (abs_nonneg x) m

/-- A polynomially bounded function is integrable under the standard Gaussian on `ℝ`. -/
theorem integrable_of_polyBound_gaussianReal {E : Type*} [NormedAddCommGroup E] {g : ℝ → E}
    (hg : AEStronglyMeasurable g (gaussianReal 0 1)) {K : ℝ} {m : ℕ}
    (hb : ∀ x, ‖g x‖ ≤ K * (1 + |x|) ^ m) : Integrable g (gaussianReal 0 1) :=
  ((integrable_one_add_abs_pow_gaussianReal m).const_mul K).mono' hg (ae_of_all _ hb)

/-- A coordinate of a standard Gaussian vector is in every `Lᵖ`, `p < ∞`. -/
theorem memLp_eval_gaussPi (i : ι) (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (fun x : ι → ℝ => x i) p (gaussPi ι) :=
  (memLp_id_gaussianReal' (μ := 0) (v := 1) p hp).comp_measurePreserving
    (measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i)

/-- The sup norm on `ι → ℝ` is at most the `ℓ¹` norm. -/
theorem norm_le_sum_abs (x : ι → ℝ) : ‖x‖ ≤ ∑ i, |x i| := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (f := fun i => |x i|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)

/-- `(1 + ‖x‖) ^ m` is integrable under the standard Gaussian on `ι → ℝ`. -/
theorem one_add_norm_pow_le_sum (x : ι → ℝ) (m : ℕ) :
    (1 + ‖x‖) ^ m ≤ 1 + ∑ i, (1 + |x i|) ^ m := by
  have hs : 0 ≤ ∑ i, (1 + |x i|) ^ m := by positivity
  rcases isEmpty_or_nonempty ι with hι | hι
  · have h0 : ‖x‖ ≤ 0 := (pi_norm_le_iff_of_nonneg le_rfl).2 fun i => isEmptyElim i
    have h0' : ‖x‖ = 0 := le_antisymm h0 (norm_nonneg x)
    rw [h0', add_zero, one_pow]
    linarith
  · obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image Finset.univ (fun i => |x i|)
      Finset.univ_nonempty
    have hx : ‖x‖ ≤ |x i₀| := (pi_norm_le_iff_of_nonneg (abs_nonneg _)).2 fun j => by
      rw [Real.norm_eq_abs]; exact hi₀ j (Finset.mem_univ j)
    calc (1 + ‖x‖) ^ m ≤ (1 + |x i₀|) ^ m := pow_le_pow_left₀ (by positivity) (by linarith) m
      _ ≤ ∑ i, (1 + |x i|) ^ m :=
          Finset.single_le_sum (f := fun i => (1 + |x i|) ^ m) (fun j _ => by positivity)
            (Finset.mem_univ i₀)
      _ ≤ 1 + ∑ i, (1 + |x i|) ^ m := by linarith

/-- `(1 + ‖x‖) ^ m` is integrable under the standard Gaussian on `ι → ℝ`. -/
theorem integrable_one_add_norm_pow_gaussPi (m : ℕ) :
    Integrable (fun x : ι → ℝ => (1 + ‖x‖) ^ m) (gaussPi ι) := by
  have h : Integrable (fun x : ι → ℝ => 1 + ∑ i, (1 + |x i|) ^ m) (gaussPi ι) :=
    (integrable_const 1).add (integrable_finsetSum Finset.univ fun i _ =>
      integrable_comp_eval (μ := fun _ : ι => gaussianReal 0 1) (i := i)
        (f := fun t : ℝ => (1 + |t|) ^ m) (integrable_one_add_abs_pow_gaussianReal m))
  refine h.mono' (by fun_prop) (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact one_add_norm_pow_le_sum x m

/-- A polynomially bounded function is integrable under the standard Gaussian on `ι → ℝ`. -/
theorem integrable_of_polyBound_gaussPi {E : Type*} [NormedAddCommGroup E]
    {g : (ι → ℝ) → E} (hg : AEStronglyMeasurable g (gaussPi ι)) {K : ℝ} {m : ℕ}
    (hb : ∀ x, ‖g x‖ ≤ K * (1 + ‖x‖) ^ m) : Integrable g (gaussPi ι) :=
  ((integrable_one_add_norm_pow_gaussPi m).const_mul K).mono' hg (ae_of_all _ hb)

/-! ### Resampling one coordinate -/

/-- Replacing coordinate `i` of a sample of `Measure.pi μ` by an independent sample of `μ i`
gives again a sample of `Measure.pi μ`. -/
theorem measurePreserving_update {α : Type*} [MeasurableSpace α] [DecidableEq ι]
    (μ : ι → Measure α) [∀ i, IsProbabilityMeasure (μ i)] (i : ι) :
    MeasurePreserving (fun p : (ι → α) × α => Function.update p.1 i p.2)
      ((Measure.pi μ).prod (μ i)) (Measure.pi μ) := by
  refine ⟨measurable_update', (Measure.pi_eq fun s hs => ?_).symm⟩
  have hpre : (fun p : (ι → α) × α => Function.update p.1 i p.2) ⁻¹' Set.univ.pi s =
      (Set.univ.pi (Function.update s i Set.univ)) ×ˢ s i := by
    ext ⟨x, t⟩
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_prod]
    constructor
    · intro h
      refine ⟨fun j => ?_, by simpa using h i⟩
      by_cases hj : j = i
      · subst hj; simp
      · simpa [Function.update_of_ne hj] using h j
    · rintro ⟨h1, h2⟩ j
      by_cases hj : j = i
      · subst hj; simpa using h2
      · simpa [Function.update_of_ne hj] using h1 j
  rw [Measure.map_apply measurable_update' (MeasurableSet.univ_pi hs), hpre, Measure.prod_prod,
    Measure.pi_pi, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i),
    ← Finset.prod_erase_mul _ (fun j => μ j (s j)) (Finset.mem_univ i)]
  simp only [Function.update_self, measure_univ, mul_one]
  congr 1
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

/-- `measurePreserving_update` for the standard Gaussian. -/
theorem measurePreserving_update_gaussPi [DecidableEq ι] (i : ι) :
    MeasurePreserving (fun p : (ι → ℝ) × ℝ => Function.update p.1 i p.2)
      ((gaussPi ι).prod (gaussianReal 0 1)) (gaussPi ι) :=
  measurePreserving_update (fun _ : ι => gaussianReal 0 1) i

/-- Fubini splitting off coordinate `i` of a standard Gaussian vector. -/
theorem integral_gaussPi_eq_integral_update [DecidableEq ι] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {g : (ι → ℝ) → E} (hg : Integrable g (gaussPi ι)) (i : ι) :
    ∫ x, g x ∂gaussPi ι = ∫ x, ∫ t, g (Function.update x i t) ∂gaussianReal 0 1 ∂gaussPi ι := by
  have hΦ := measurePreserving_update_gaussPi (ι := ι) i
  have hint : Integrable (g ∘ fun p : (ι → ℝ) × ℝ => Function.update p.1 i p.2)
      ((gaussPi ι).prod (gaussianReal 0 1)) :=
    (hΦ.integrable_comp hg.aestronglyMeasurable).2 hg
  have h := integral_map (μ := (gaussPi ι).prod (gaussianReal 0 1)) hΦ.measurable.aemeasurable
    (f := g) (by rw [hΦ.map_eq]; exact hg.aestronglyMeasurable)
  rw [hΦ.map_eq] at h
  exact h.trans (integral_prod _ hint)

/-! ### The Gaussian density -/

theorem gaussianPDFReal_zero_one (x : ℝ) :
    gaussianPDFReal 0 1 x = (√(2 * π))⁻¹ * rexp (-x ^ 2 / 2) := by
  simp [gaussianPDFReal]

/-- The standard Gaussian density `φ` satisfies `φ' = -x φ`. -/
theorem hasDerivAt_gaussianPDFReal_zero_one (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x * gaussianPDFReal 0 1 x) x := by
  have hfun : gaussianPDFReal 0 1 = fun x => (√(2 * π))⁻¹ * rexp (-x ^ 2 / 2) :=
    funext gaussianPDFReal_zero_one
  rw [hfun]
  have h1 : HasDerivAt (fun x : ℝ => -x ^ 2 / 2) (-x) x := by
    have := ((hasDerivAt_pow 2 x).neg).div_const 2
    convert this using 1
    norm_num
    ring
  convert (h1.exp).const_mul (√(2 * π))⁻¹ using 1
  ring

/-- Integrability under the standard Gaussian is Lebesgue integrability against its density. -/
theorem integrable_gaussianReal_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : ℝ → E} :
    Integrable g (gaussianReal 0 1) ↔ Integrable (fun x => gaussianPDFReal 0 1 x • g x) := by
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero,
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
      (ae_of_all _ fun _ => gaussianPDF_lt_top)]
  simp only [toReal_gaussianPDF]

/-! ### One-dimensional Stein identity -/

/-- **Stein's identity on `ℝ`**: if `f` has derivative `f'` everywhere and `f`, `f'` are
polynomially bounded, then `𝔼[X f(X)] = 𝔼[f'(X)]` for a standard normal `X`. -/
theorem stein_gaussianReal_of_hasDerivAt {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    {K : ℝ} {m : ℕ} (hfb : ∀ x, |f x| ≤ K * (1 + |x|) ^ m)
    (hf'b : ∀ x, |f' x| ≤ K * (1 + |x|) ^ m) :
    ∫ x, x * f x ∂gaussianReal 0 1 = ∫ x, f' x ∂gaussianReal 0 1 := by
  set ρ := gaussianPDFReal 0 1 with hρ
  have hf'eq : f' = deriv f := funext fun x => (hf x).deriv.symm
  have hfc : Continuous f := continuous_iff_continuousAt.2 fun x => (hf x).continuousAt
  have hf'm : Measurable f' := hf'eq ▸ measurable_deriv f
  have i1 : Integrable f (gaussianReal 0 1) :=
    integrable_of_polyBound_gaussianReal hfc.aestronglyMeasurable (K := K) (m := m)
      (by simpa [Real.norm_eq_abs] using hfb)
  have i2 : Integrable f' (gaussianReal 0 1) :=
    integrable_of_polyBound_gaussianReal hf'm.aestronglyMeasurable (K := K) (m := m)
      (by simpa [Real.norm_eq_abs] using hf'b)
  have i3 : Integrable (fun x => x * f x) (gaussianReal 0 1) := by
    refine integrable_of_polyBound_gaussianReal (by fun_prop) (K := K) (m := m + 1) fun x => ?_
    rw [Real.norm_eq_abs, abs_mul, pow_succ]
    have h0 : 0 ≤ K * (1 + |x|) ^ m := (abs_nonneg _).trans (hfb x)
    calc |x| * |f x| ≤ (1 + |x|) * (K * (1 + |x|) ^ m) :=
          mul_le_mul (by linarith [abs_nonneg x]) (hfb x) (abs_nonneg _) (by positivity)
      _ = K * ((1 + |x|) ^ m * (1 + |x|)) := by ring
  rw [integrable_gaussianReal_iff] at i1 i2 i3
  simp only [smul_eq_mul] at i1 i2 i3
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero,
    integral_gaussianReal_eq_integral_smul one_ne_zero]
  simp only [smul_eq_mul]
  have key := integral_mul_deriv_eq_deriv_mul_of_integrable (u := f) (v := ρ) (u' := f')
    (v' := fun x => -x * ρ x) (fun x _ => hf x) (fun x _ => hasDerivAt_gaussianPDFReal_zero_one x)
    (i3.neg.congr (ae_of_all _ fun x => by simp only [Pi.mul_apply, Pi.neg_apply, hρ]; ring))
    (i2.congr (ae_of_all _ fun x => by simp only [Pi.mul_apply, hρ]; ring))
    (i1.congr (ae_of_all _ fun x => by simp only [Pi.mul_apply, hρ]; ring))
  calc ∫ x, ρ x * (x * f x) = -∫ x, f x * (-x * ρ x) := by
        rw [← integral_neg]; congr 1; ext x; ring
    _ = ∫ x, f' x * ρ x := by rw [key, neg_neg]
    _ = ∫ x, ρ x * f' x := by congr 1; ext x; ring

/-- **Stein's identity on `ℝ`**: `𝔼[X f(X)] = 𝔼[f'(X)]` for differentiable `f` with `f`, `f'`
polynomially bounded. -/
theorem stein_gaussianReal {f : ℝ → ℝ} (hf : Differentiable ℝ f) {K : ℝ} {m : ℕ}
    (hfb : ∀ x, |f x| ≤ K * (1 + |x|) ^ m) (hf'b : ∀ x, |deriv f x| ≤ K * (1 + |x|) ^ m) :
    ∫ x, x * f x ∂gaussianReal 0 1 = ∫ x, deriv f x ∂gaussianReal 0 1 :=
  stein_gaussianReal_of_hasDerivAt (fun x => (hf x).hasDerivAt) hfb hf'b

/-! ### Moments of the standard Gaussian -/

/-- The moment recursion `𝔼[X^(n+2)] = (n+1) 𝔼[X^n]`. -/
theorem integral_pow_add_two_gaussianReal (n : ℕ) :
    ∫ x, x ^ (n + 2) ∂gaussianReal 0 1 = (n + 1) * ∫ x, x ^ n ∂gaussianReal 0 1 := by
  have h := stein_gaussianReal_of_hasDerivAt (f := fun x : ℝ => x ^ (n + 1))
    (f' := fun x => ((n + 1 : ℕ) : ℝ) * x ^ n) (fun x => by simpa using hasDerivAt_pow (n + 1) x)
    (K := n + 1) (m := n + 1) (fun x => ?_) (fun x => ?_)
  · rw [← integral_const_mul]
    convert h using 1
    · congr 1; ext x; ring
    · congr 1; ext x; push_cast; ring
  · rw [abs_pow]
    calc |x| ^ (n + 1) ≤ 1 * (1 + |x|) ^ (n + 1) := by
          rw [one_mul]; exact pow_le_pow_left₀ (abs_nonneg x) (by linarith) _
      _ ≤ (n + 1) * (1 + |x|) ^ (n + 1) := by gcongr; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  · rw [abs_mul, abs_pow, Nat.abs_cast]
    push_cast
    gcongr
    calc |x| ^ n ≤ (1 + |x|) ^ n := pow_le_pow_left₀ (abs_nonneg x) (by linarith) _
      _ ≤ (1 + |x|) ^ (n + 1) := pow_le_pow_right₀ (by linarith [abs_nonneg x]) (by omega)

/-- The even moments of the standard Gaussian: `𝔼[X^(2k)] = (2k-1)‼`. -/
theorem integral_pow_two_mul_gaussianReal (k : ℕ) :
    ∫ x, x ^ (2 * k) ∂gaussianReal 0 1 = ((2 * k - 1)‼ : ℕ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 by ring, integral_pow_add_two_gaussianReal, ih,
      show 2 * k + 2 - 1 = 2 * k + 1 by omega, Nat.doubleFactorial_add_one]
    push_cast
    ring

/-- The odd moments of the standard Gaussian vanish. -/
theorem integral_pow_two_mul_add_one_gaussianReal (k : ℕ) :
    ∫ x, x ^ (2 * k + 1) ∂gaussianReal 0 1 = 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 2 by ring, integral_pow_add_two_gaussianReal, ih,
      mul_zero]

/-! ### Stein identity on `ι → ℝ` -/

theorem norm_update_le [DecidableEq ι] (x : ι → ℝ) (i : ι) (t : ℝ) :
    ‖Function.update x i t‖ ≤ ‖x‖ + |t| := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
  by_cases hj : j = i
  · subst hj; rw [Function.update_self, Real.norm_eq_abs]; linarith [norm_nonneg x]
  · rw [Function.update_of_ne hj]; linarith [norm_le_pi_norm x j, abs_nonneg t]

theorem one_add_norm_update_pow_le [DecidableEq ι] (x : ι → ℝ) (i : ι) (t : ℝ) (m : ℕ) :
    (1 + ‖Function.update x i t‖) ^ m ≤ (1 + ‖x‖) ^ m * (1 + |t|) ^ m := by
  rw [← mul_pow]
  apply pow_le_pow_left₀ (by positivity)
  nlinarith [norm_update_le x i t, norm_nonneg x, abs_nonneg t,
    mul_nonneg (norm_nonneg x) (abs_nonneg t)]

/-- Multiplying a polynomially bounded function by a coordinate raises the degree by one. -/
theorem norm_coord_mul_le {g : (ι → ℝ) → ℝ} {K : ℝ} {m : ℕ}
    (hb : ∀ x, ‖g x‖ ≤ K * (1 + ‖x‖) ^ m) (i : ι) (x : ι → ℝ) :
    ‖x i * g x‖ ≤ K * (1 + ‖x‖) ^ (m + 1) := by
  rw [norm_mul, pow_succ]
  have h0 : 0 ≤ K * (1 + ‖x‖) ^ m := (norm_nonneg _).trans (hb x)
  calc ‖x i‖ * ‖g x‖ ≤ (1 + ‖x‖) * (K * (1 + ‖x‖) ^ m) :=
        mul_le_mul (by linarith [norm_le_pi_norm x i]) (hb x) (norm_nonneg _) (by positivity)
    _ = K * ((1 + ‖x‖) ^ m * (1 + ‖x‖)) := by ring

/-- **Stein's identity on `ι → ℝ`, partial-derivative form.** If `g` is the partial derivative
of `f` in direction `i` along every coordinate line and both are polynomially bounded, then
`𝔼[X_i f(X)] = 𝔼[g(X)]`. -/
theorem stein_gaussPi_of_hasDerivAt [DecidableEq ι] {f g : (ι → ℝ) → ℝ} (i : ι)
    (hfm : AEStronglyMeasurable f (gaussPi ι)) (hgm : AEStronglyMeasurable g (gaussPi ι))
    (hfg : ∀ x t, HasDerivAt (fun s => f (Function.update x i s)) (g (Function.update x i t)) t)
    {K : ℝ} {m : ℕ} (hfb : ∀ x, ‖f x‖ ≤ K * (1 + ‖x‖) ^ m)
    (hgb : ∀ x, ‖g x‖ ≤ K * (1 + ‖x‖) ^ m) :
    ∫ x, x i * f x ∂gaussPi ι = ∫ x, g x ∂gaussPi ι := by
  have hK : 0 ≤ K := by simpa using (norm_nonneg _).trans (hfb 0)
  have i1 : Integrable (fun x => x i * f x) (gaussPi ι) :=
    integrable_of_polyBound_gaussPi ((measurable_pi_apply i).aestronglyMeasurable.mul hfm)
      (norm_coord_mul_le hfb i)
  have i2 : Integrable g (gaussPi ι) := integrable_of_polyBound_gaussPi hgm hgb
  rw [integral_gaussPi_eq_integral_update i1 i, integral_gaussPi_eq_integral_update i2 i]
  congr 1
  ext x
  simp only [Function.update_self]
  refine stein_gaussianReal_of_hasDerivAt (hfg x) (K := K * (1 + ‖x‖) ^ m) (m := m)
    (fun t => ?_) (fun t => ?_)
  · have h1 := hfb (Function.update x i t)
    rw [Real.norm_eq_abs] at h1
    calc _ ≤ _ := h1
      _ ≤ K * ((1 + ‖x‖) ^ m * (1 + |t|) ^ m) :=
          mul_le_mul_of_nonneg_left (one_add_norm_update_pow_le x i t m) hK
      _ = _ := by ring
  · have h1 := hgb (Function.update x i t)
    rw [Real.norm_eq_abs] at h1
    calc _ ≤ _ := h1
      _ ≤ K * ((1 + ‖x‖) ^ m * (1 + |t|) ^ m) :=
          mul_le_mul_of_nonneg_left (one_add_norm_update_pow_le x i t m) hK
      _ = _ := by ring

/-- **Stein's identity on `ι → ℝ`**: for differentiable `f` with `f` and `Df` polynomially
bounded, `𝔼[X_i f(X)] = 𝔼[∂_i f(X)]` under the standard Gaussian. -/
theorem stein_gaussPi [DecidableEq ι] {f : (ι → ℝ) → ℝ} (hf : Differentiable ℝ f) {K : ℝ}
    {m : ℕ} (hfb : ∀ x, ‖f x‖ ≤ K * (1 + ‖x‖) ^ m)
    (hf'b : ∀ x, ‖fderiv ℝ f x‖ ≤ K * (1 + ‖x‖) ^ m) (i : ι) :
    ∫ x, x i * f x ∂gaussPi ι = ∫ x, fderiv ℝ f x (Pi.single i 1) ∂gaussPi ι := by
  refine stein_gaussPi_of_hasDerivAt i hf.continuous.aestronglyMeasurable
    (measurable_fderiv_apply_const ℝ f _).aestronglyMeasurable (fun x t => ?_) hfb (fun x => ?_)
  · exact (hf _).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_update x i t)
  · calc ‖fderiv ℝ f x (Pi.single i 1)‖
          ≤ ‖fderiv ℝ f x‖ * ‖(Pi.single i 1 : ι → ℝ)‖ := (fderiv ℝ f x).le_opNorm _
      _ = ‖fderiv ℝ f x‖ := by rw [Pi.norm_single, norm_one, mul_one]
      _ ≤ _ := hf'b x

/-- `stein_gaussPi` for `C¹` functions. -/
theorem stein_gaussPi_of_contDiff [DecidableEq ι] {f : (ι → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    {K : ℝ} {m : ℕ} (hfb : ∀ x, ‖f x‖ ≤ K * (1 + ‖x‖) ^ m)
    (hf'b : ∀ x, ‖fderiv ℝ f x‖ ≤ K * (1 + ‖x‖) ^ m) (i : ι) :
    ∫ x, x i * f x ∂gaussPi ι = ∫ x, fderiv ℝ f x (Pi.single i 1) ∂gaussPi ι :=
  stein_gaussPi (hf.differentiable one_ne_zero) hfb hf'b i

/-- The derivative of a partial derivative `y ↦ Df(y) v` is `(D²f(x)).flip v`. -/
theorem hasFDerivAt_fderiv_apply_const {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {x : E} (h : DifferentiableAt ℝ (fderiv ℝ f) x) (v : E) :
    HasFDerivAt (fun y => fderiv ℝ f y v) ((fderiv ℝ (fderiv ℝ f) x).flip v) x := by
  simpa using h.hasFDerivAt.clm_apply (hasFDerivAt_const v x)

/-- **Second-order Gaussian integration by parts**: for `C²` functions `f` with `f`, `Df`, `D²f`
polynomially bounded, `𝔼[(X_i X_j - δ_ij) f(X)] = 𝔼[∂_i ∂_j f(X)]`. -/
theorem stein_two_gaussPi [DecidableEq ι] {f : (ι → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) {K : ℝ}
    {m : ℕ} (hfb : ∀ x, ‖f x‖ ≤ K * (1 + ‖x‖) ^ m)
    (hf'b : ∀ x, ‖fderiv ℝ f x‖ ≤ K * (1 + ‖x‖) ^ m)
    (hf''b : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ K * (1 + ‖x‖) ^ m) (i j : ι) :
    ∫ x, (x i * x j - if i = j then 1 else 0) * f x ∂gaussPi ι =
      ∫ x, fderiv ℝ (fun y => fderiv ℝ f y (Pi.single j 1)) x (Pi.single i 1) ∂gaussPi ι := by
  have hd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hd2 : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  have hK : 0 ≤ K := by simpa using (norm_nonneg _).trans (hfb 0)
  set e : ℝ := if i = j then 1 else 0 with he
  set fj : (ι → ℝ) → ℝ := fun y => fderiv ℝ f y (Pi.single j 1) with hfj
  have hdj : Differentiable ℝ fj := fun y =>
    (hasFDerivAt_fderiv_apply_const (hd2 y) _).differentiableAt
  have hfc : Continuous f := hd.continuous
  have hfjc : Continuous fj := hdj.continuous
  have hfjb : ∀ x, ‖fj x‖ ≤ K * (1 + ‖x‖) ^ m := fun x => by
    calc ‖fderiv ℝ f x (Pi.single j 1)‖
          ≤ ‖fderiv ℝ f x‖ * ‖(Pi.single j 1 : ι → ℝ)‖ := (fderiv ℝ f x).le_opNorm _
      _ = ‖fderiv ℝ f x‖ := by rw [Pi.norm_single, norm_one, mul_one]
      _ ≤ _ := hf'b x
  have hfj'b : ∀ x, ‖fderiv ℝ fj x‖ ≤ K * (1 + ‖x‖) ^ m := fun x => by
    rw [(hasFDerivAt_fderiv_apply_const (hd2 x) _).fderiv]
    calc ‖(fderiv ℝ (fderiv ℝ f) x).flip (Pi.single j 1)‖
          ≤ ‖(fderiv ℝ (fderiv ℝ f) x).flip‖ * ‖(Pi.single j 1 : ι → ℝ)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ = ‖fderiv ℝ (fderiv ℝ f) x‖ := by
          rw [ContinuousLinearMap.opNorm_flip, Pi.norm_single, norm_one, mul_one]
      _ ≤ _ := hf''b x
  have hB := stein_gaussPi hdj hfjb hfj'b i
  have hpow : ∀ x : ι → ℝ, (1 + ‖x‖) ^ m ≤ (1 + ‖x‖) ^ (m + 1) := fun x =>
    pow_le_pow_right₀ (by linarith [norm_nonneg x]) (Nat.le_succ m)
  have he1 : ‖e‖ ≤ 1 := by rw [he]; split_ifs <;> simp
  have hderiv : ∀ x t, HasDerivAt (fun s => Function.update x j s i * f (Function.update x j s))
      (Function.update x j t i * fj (Function.update x j t) + e * f (Function.update x j t)) t := by
    intro x t
    have h1 : HasDerivAt (fun s => Function.update x j s i) ((Pi.single j 1 : ι → ℝ) i) t :=
      hasDerivAt_pi.1 (hasDerivAt_update x j t) i
    have h2 : HasDerivAt (fun s => f (Function.update x j s)) (fj (Function.update x j t)) t :=
      (hd _).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_update x j t)
    convert h1.mul h2 using 1
    rw [he, Pi.single_apply]
    ring
  have hbF : ∀ x : ι → ℝ, ‖x i * f x‖ ≤ 2 * K * (1 + ‖x‖) ^ (m + 1) := fun x => by
    calc ‖x i * f x‖ ≤ K * (1 + ‖x‖) ^ (m + 1) := norm_coord_mul_le hfb i x
      _ ≤ 2 * K * (1 + ‖x‖) ^ (m + 1) := by
          have : 0 ≤ K * (1 + ‖x‖) ^ (m + 1) := by positivity
          linarith
  have hbG : ∀ x : ι → ℝ, ‖x i * fj x + e * f x‖ ≤ 2 * K * (1 + ‖x‖) ^ (m + 1) := fun x => by
    calc ‖x i * fj x + e * f x‖ ≤ ‖x i * fj x‖ + ‖e‖ * ‖f x‖ := by
          rw [← norm_mul]; exact norm_add_le _ _
      _ ≤ K * (1 + ‖x‖) ^ (m + 1) + 1 * (K * (1 + ‖x‖) ^ (m + 1)) := by
          gcongr
          · exact norm_coord_mul_le hfjb i x
          · exact (hfb x).trans (mul_le_mul_of_nonneg_left (hpow x) hK)
      _ = 2 * K * (1 + ‖x‖) ^ (m + 1) := by ring
  have hA := stein_gaussPi_of_hasDerivAt (f := fun x => x i * f x)
    (g := fun x => x i * fj x + e * f x) j (by fun_prop : Continuous _).aestronglyMeasurable
    (by fun_prop : Continuous _).aestronglyMeasurable hderiv hbF hbG
  have iA : Integrable (fun x => x j * (x i * f x)) (gaussPi ι) :=
    integrable_of_polyBound_gaussPi (by fun_prop : Continuous _).aestronglyMeasurable
      (norm_coord_mul_le (norm_coord_mul_le hfb i) j)
  have iE : Integrable (fun x => e * f x) (gaussPi ι) :=
    (integrable_of_polyBound_gaussPi hfc.aestronglyMeasurable hfb).const_mul e
  have iB : Integrable (fun x => x i * fj x) (gaussPi ι) :=
    integrable_of_polyBound_gaussPi (by fun_prop : Continuous _).aestronglyMeasurable
      (norm_coord_mul_le hfjb i)
  calc ∫ x, (x i * x j - e) * f x ∂gaussPi ι
        = ∫ x, (x j * (x i * f x) - e * f x) ∂gaussPi ι := by congr 1; ext x; ring
    _ = ∫ x, x j * (x i * f x) ∂gaussPi ι - ∫ x, e * f x ∂gaussPi ι := integral_sub iA iE
    _ = ∫ x, (x i * fj x + e * f x) ∂gaussPi ι - ∫ x, e * f x ∂gaussPi ι := by rw [hA]
    _ = ∫ x, x i * fj x ∂gaussPi ι := by rw [integral_add iB iE]; ring
    _ = _ := hB

/-! ### Convenience corollaries -/

/-- `stein_gaussianReal` for bounded `f` with bounded derivative. -/
theorem stein_gaussianReal_of_bounded {f : ℝ → ℝ} (hf : Differentiable ℝ f) {C : ℝ}
    (hfb : ∀ x, |f x| ≤ C) (hf'b : ∀ x, |deriv f x| ≤ C) :
    ∫ x, x * f x ∂gaussianReal 0 1 = ∫ x, deriv f x ∂gaussianReal 0 1 :=
  stein_gaussianReal hf (K := C) (m := 0) (by simpa using hfb) (by simpa using hf'b)

/-- `stein_gaussianReal` for compactly supported `C¹` functions. -/
theorem stein_gaussianReal_of_hasCompactSupport {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hcs : HasCompactSupport f) :
    ∫ x, x * f x ∂gaussianReal 0 1 = ∫ x, deriv f x ∂gaussianReal 0 1 := by
  obtain ⟨C₁, hC₁⟩ := hf.continuous.bounded_above_of_compact_support hcs
  obtain ⟨C₂, hC₂⟩ := (hf.continuous_deriv le_rfl).bounded_above_of_compact_support hcs.deriv
  exact stein_gaussianReal_of_bounded (hf.differentiable one_ne_zero) (C := max C₁ C₂)
    (fun x => (hC₁ x).trans (le_max_left _ _)) (fun x => (hC₂ x).trans (le_max_right _ _))

/-- `stein_gaussPi` for bounded `f` with bounded derivative. -/
theorem stein_gaussPi_of_bounded [DecidableEq ι] {f : (ι → ℝ) → ℝ} (hf : Differentiable ℝ f)
    {C : ℝ} (hfb : ∀ x, ‖f x‖ ≤ C) (hf'b : ∀ x, ‖fderiv ℝ f x‖ ≤ C) (i : ι) :
    ∫ x, x i * f x ∂gaussPi ι = ∫ x, fderiv ℝ f x (Pi.single i 1) ∂gaussPi ι :=
  stein_gaussPi hf (K := C) (m := 0) (by simpa using hfb) (by simpa using hf'b) i

/-- `stein_gaussPi` for compactly supported `C¹` functions. -/
theorem stein_gaussPi_of_hasCompactSupport [DecidableEq ι] {f : (ι → ℝ) → ℝ}
    (hf : ContDiff ℝ 1 f) (hcs : HasCompactSupport f) (i : ι) :
    ∫ x, x i * f x ∂gaussPi ι = ∫ x, fderiv ℝ f x (Pi.single i 1) ∂gaussPi ι := by
  obtain ⟨C₁, hC₁⟩ := hf.continuous.bounded_above_of_compact_support hcs
  obtain ⟨C₂, hC₂⟩ :=
    (hf.continuous_fderiv one_ne_zero).bounded_above_of_compact_support (hcs.fderiv (𝕜 := ℝ))
  exact stein_gaussPi_of_bounded (hf.differentiable one_ne_zero) (C := max C₁ C₂)
    (fun x => (hC₁ x).trans (le_max_left _ _)) (fun x => (hC₂ x).trans (le_max_right _ _)) i

end BiluLinial.Tight
