/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.Tools.Alpha2
public import BiluLinial.Tight.Tools.MatrixFacts
public import BiluLinial.Tight.Gauss.IBP

/-!
# T.GIBP2: the Gaussian integration-by-parts identity `2𝖦F = N_G`

Node T.GIBP2 of `docs/tight/BP_TOOLS.md` (AUDIT-C §5, source line 1248). For PSD `A, B` and
`p ≥ 3`, with `α = (1 - q_A)₊`, `β = (1 - q_B)₊`, `g = α^{p-1} β^p` (`starG`) and

  `F = (p-1) q_{A²} α^{p-2} β^p + p q_{AB} α^{p-1} β^{p-1}` (`starF`),

`2 𝖦 F = 𝖦[(tr A - q_A) g]`.

**Sketch.** Stein's identity `𝖦[xᵢ fᵢ] = 𝖦[∂ᵢ fᵢ]` (`stein_gaussPi_of_hasDerivAt`) for
`fᵢ = (Ax)ᵢ g`, which is `C¹` with polynomially bounded derivative because `p - 1 ≥ 2`
(`t ↦ (t₊)^k` is `C¹` for `k ≥ 2`, with derivative `k (t₊)^{k-1}`). Summing over `i`:
`Σ xᵢ (Ax)ᵢ = q_A` and `Σ ∂ᵢ fᵢ = tr A · g + (Ax)·∇g`, where
`∇g = -2(p-1) α^{p-2} β^p Ax - 2p α^{p-1} β^{p-1} Bx`, so `(Ax)·∇g = -2F` (using `Aᵀ = A`:
`|Ax|² = q_{A²}`, `(Ax)·(Bx) = q_{AB}`). Hence `𝖦[q_A g] = tr A 𝖦 g - 2 𝖦 F`.

**Checks.** `A = 0`: `F = 0` and `tr A - q_A = 0`. `ι` empty: both sides `0`. `p = 3`, `B = 0`,
one coordinate, `A = a`: `F = 2a²x²(1-ax²)₊`, and the identity is the Stein identity for
`x ↦ ax (1 - ax²)₊²`.
-/

@[expose] public section

namespace BiluLinial.Tight

open MeasureTheory ProbabilityTheory Matrix Filter Topology

variable {ι : Type*} [Fintype ι]

/-- `g = α^{p-1} β^p`, the Gaussian weight of `ν` in Lemma B1. -/
abbrev starG (p : ℕ) (A B : Matrix ι ι ℝ) : (ι → ℝ) → ℝ := clipProd (p - 1) p A B

/-- The row observable `F = (p-1) q_{A²} α^{p-2} β^p + p q_{AB} α^{p-1} β^{p-1}` (source line 332;
the coefficient `p - 1` is the natural-number difference, equal to `(p : ℝ) - 1` for `p ≥ 1`). -/
noncomputable def starF (p : ℕ) (A B : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ :=
  ((p - 1 : ℕ) : ℝ) * qForm (A * A) x * clipF A x ^ (p - 2) * clipF B x ^ p +
    (p : ℝ) * qForm (A * B) x * clipF A x ^ (p - 1) * clipF B x ^ (p - 1)

/-! ### Line derivatives -/

section Deriv

variable [DecidableEq ι]

private theorem hasDerivAt_posPart_pow {k : ℕ} (hk : 2 ≤ k) (t : ℝ) :
    HasDerivAt (fun t : ℝ => max t 0 ^ k) (k * max t 0 ^ (k - 1)) t := by
  rcases lt_trichotomy t 0 with ht | ht | ht
  · have hev : (fun t : ℝ => max t 0 ^ k) =ᶠ[𝓝 t] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds ht] with s hs
      rw [max_eq_right (le_of_lt hs), zero_pow (by omega)]
    rw [max_eq_right ht.le, zero_pow (by omega), mul_zero]
    exact (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq hev
  · subst ht
    rw [max_self, zero_pow (by omega), mul_zero, hasDerivAt_iff_isLittleO]
    simp only [max_self, zero_pow (show k ≠ 0 by omega), sub_zero, smul_zero]
    have h1 : (fun x : ℝ => x ^ k) =o[𝓝 0] fun x => x := Asymptotics.isLittleO_pow_id (by omega)
    refine Asymptotics.IsBigO.trans_isLittleO ?_ h1
    refine Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall fun x => ?_)
    rw [one_mul, norm_pow, norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      exact max_le (le_abs_self x) (abs_nonneg x)) k
  · have hev : (fun t : ℝ => max t 0 ^ k) =ᶠ[𝓝 t] fun s => s ^ k := by
      filter_upwards [Ioi_mem_nhds ht] with s hs
      rw [max_eq_left (le_of_lt hs)]
    rw [max_eq_left ht.le]
    exact (hasDerivAt_pow k t).congr_of_eventuallyEq hev

omit [Fintype ι] in
private theorem update_eq_add_smul_single (x : ι → ℝ) (i : ι) (s : ℝ) :
    Function.update x i s = x + (s - x i) • Pi.single i 1 := by
  ext j
  by_cases h : j = i
  · subst h; simp
  · simp [Function.update_of_ne h, Pi.single_eq_of_ne h]

private theorem mulVec_update_apply (A : Matrix ι ι ℝ) (x : ι → ℝ) (i k : ι) (s : ℝ) :
    (A *ᵥ Function.update x i s) k = (A *ᵥ x) k + (s - x i) * A k i := by
  rw [update_eq_add_smul_single, mulVec_add, mulVec_smul, mulVec_single_one]
  simp [Matrix.col]

private theorem qForm_add_smul_single {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (x : ι → ℝ)
    (i : ι) (r : ℝ) :
    qForm A (x + r • Pi.single i 1) = qForm A x + 2 * r * (A *ᵥ x) i + r ^ 2 * A i i := by
  have h1 : x ⬝ᵥ (A *ᵥ Pi.single i 1) = (A *ᵥ x) i := by
    rw [dotProduct_mulVec_comm_of_symm hA, dotProduct_single_one]
  have h2 : Pi.single i 1 ⬝ᵥ (A *ᵥ x) = (A *ᵥ x) i := single_one_dotProduct i _
  have h3 : Pi.single i 1 ⬝ᵥ (A *ᵥ Pi.single i 1) = A i i := by
    rw [single_one_dotProduct, mulVec_single_one]; rfl
  simp only [qForm, mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
    smul_dotProduct, smul_eq_mul, h1, h2, h3]
  ring

private theorem hasDerivAt_qForm_update {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (x : ι → ℝ)
    (i : ι) (t : ℝ) :
    HasDerivAt (fun s => qForm A (Function.update x i s)) (2 * (A *ᵥ Function.update x i t) i)
      t := by
  have e : (fun s => qForm A (Function.update x i s)) =
      fun s => qForm A x + 2 * (s - x i) * (A *ᵥ x) i + (s - x i) ^ 2 * A i i := by
    funext s; rw [update_eq_add_smul_single, qForm_add_smul_single hA]
  rw [e, mulVec_update_apply]
  have h1 : HasDerivAt (fun s : ℝ => s - x i) 1 t := (hasDerivAt_id t).sub_const _
  refine ((((h1.const_mul 2).mul_const ((A *ᵥ x) i)).const_add (qForm A x)).add
    ((h1.pow 2).mul_const (A i i))).congr_deriv ?_
  simp
  ring

private theorem hasDerivAt_mulVec_update (A : Matrix ι ι ℝ) (x : ι → ℝ) (i k : ι) (t : ℝ) :
    HasDerivAt (fun s => (A *ᵥ Function.update x i s) k) (A k i) t := by
  simp only [mulVec_update_apply]
  refine (((hasDerivAt_id t).sub_const (x i)).mul_const (A k i)).const_add _ |>.congr_deriv ?_
  simp

private theorem hasDerivAt_clipF_pow_update {A : Matrix ι ι ℝ} (hA : A.IsHermitian) {k : ℕ}
    (hk : 2 ≤ k) (x : ι → ℝ) (i : ι) (t : ℝ) :
    HasDerivAt (fun s => clipF A (Function.update x i s) ^ k)
      (k * clipF A (Function.update x i t) ^ (k - 1) *
        (-(2 * (A *ᵥ Function.update x i t) i))) t :=
  (hasDerivAt_posPart_pow hk _).comp t ((hasDerivAt_qForm_update hA x i t).const_sub 1)

/-- `∂ᵢ g` for `g = α^{p-1} β^p`. -/
private noncomputable def dStarG (p : ℕ) (A B : Matrix ι ι ℝ) (i : ι) (y : ι → ℝ) : ℝ :=
  ((p - 1 : ℕ) : ℝ) * clipF A y ^ (p - 2) * (-(2 * (A *ᵥ y) i)) * clipF B y ^ p +
    clipF A y ^ (p - 1) * ((p : ℝ) * clipF B y ^ (p - 1) * (-(2 * (B *ᵥ y) i)))

private theorem hasDerivAt_starG_update {A B : Matrix ι ι ℝ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) {p : ℕ} (hp : 3 ≤ p) (x : ι → ℝ) (i : ι) (t : ℝ) :
    HasDerivAt (fun s => starG p A B (Function.update x i s))
      (dStarG p A B i (Function.update x i t)) t := by
  have h := (hasDerivAt_clipF_pow_update hA (show 2 ≤ p - 1 by omega) x i t).mul
    (hasDerivAt_clipF_pow_update hB (show 2 ≤ p by omega) x i t)
  rw [show p - 1 - 1 = p - 2 by omega] at h
  exact h

/-- `∂ᵢ ((Ax)ᵢ g)`. -/
private noncomputable def dSteinF (p : ℕ) (A B : Matrix ι ι ℝ) (i : ι) (y : ι → ℝ) : ℝ :=
  A i i * starG p A B y + (A *ᵥ y) i * dStarG p A B i y

private theorem hasDerivAt_steinF_update {A B : Matrix ι ι ℝ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) {p : ℕ} (hp : 3 ≤ p) (x : ι → ℝ) (i : ι) (t : ℝ) :
    HasDerivAt (fun s => (A *ᵥ Function.update x i s) i * starG p A B (Function.update x i s))
      (dSteinF p A B i (Function.update x i t)) t :=
  ((hasDerivAt_mulVec_update A x i i t).mul (hasDerivAt_starG_update hA hB hp x i t))

omit [DecidableEq ι] in
/-- `Σᵢ ∂ᵢ((Ax)ᵢ g) = tr A · g - 2F`. -/
private theorem sum_dSteinF {A B : Matrix ι ι ℝ} (hA : A.IsHermitian) (p : ℕ) (y : ι → ℝ) :
    ∑ i, dSteinF p A B i y = A.trace * starG p A B y - 2 * starF p A B y := by
  have hAA : qForm (A * A) y = ∑ i, (A *ᵥ y) i * (A *ᵥ y) i := by
    rw [qForm, ← mulVec_mulVec, dotProduct_mulVec_comm_of_symm hA]; rfl
  have hAB : qForm (A * B) y = ∑ i, (A *ᵥ y) i * (B *ᵥ y) i := by
    rw [qForm, ← mulVec_mulVec, dotProduct_mulVec_comm_of_symm hA]; rfl
  have e : ∀ i, dSteinF p A B i y = A i i * starG p A B y +
      (-2 * (((p - 1 : ℕ) : ℝ) * clipF A y ^ (p - 2) * clipF B y ^ p)) *
        ((A *ᵥ y) i * (A *ᵥ y) i) +
      (-2 * ((p : ℝ) * clipF A y ^ (p - 1) * clipF B y ^ (p - 1))) *
        ((A *ᵥ y) i * (B *ᵥ y) i) := fun i => by
    simp only [dSteinF, dStarG]; ring
  rw [Finset.sum_congr rfl fun i _ => e i, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum, ← Finset.mul_sum, ← hAA, ← hAB, starF]
  simp only [trace, diag]
  ring

/-! ### Bounds -/

omit [DecidableEq ι] in
theorem abs_mulVec_apply_le (A : Matrix ι ι ℝ) (x : ι → ℝ) (i : ι) :
    |(A *ᵥ x) i| ≤ (∑ j, ∑ k, |A j k|) * ‖x‖ := by
  rw [mulVec, dotProduct]
  calc |∑ k, A i k * x k| ≤ ∑ k, |A i k| * ‖x‖ := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left ((Real.norm_eq_abs (x k)) ▸ norm_le_pi_norm x k)
          (abs_nonneg _)
    _ = (∑ k, |A i k|) * ‖x‖ := by rw [Finset.sum_mul]
    _ ≤ (∑ j, ∑ k, |A j k|) * ‖x‖ :=
        mul_le_mul_of_nonneg_right (Finset.single_le_sum (f := fun j => ∑ k, |A j k|)
          (fun j _ => Finset.sum_nonneg fun k _ => abs_nonneg _) (Finset.mem_univ i))
          (norm_nonneg x)

omit [DecidableEq ι] in
private theorem abs_apply_le_sum (A : Matrix ι ι ℝ) (i : ι) : |A i i| ≤ ∑ j, ∑ k, |A j k| :=
  calc |A i i| ≤ ∑ k, |A i k| :=
        Finset.single_le_sum (f := fun k => |A i k|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    _ ≤ ∑ j, ∑ k, |A j k| := Finset.single_le_sum (f := fun j => ∑ k, |A j k|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)

omit [DecidableEq ι] in
private theorem abs_dStarG_le {A B : Matrix ι ι ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (p : ℕ) (i : ι) (y : ι → ℝ) :
    |dStarG p A B i y| ≤ 2 * p * (|(A *ᵥ y) i| + |(B *ᵥ y) i|) := by
  have ha0 := clipF_nonneg A y
  have ha1 := clipF_le_one hA y
  have hb0 := clipF_nonneg B y
  have hb1 := clipF_le_one hB y
  have hq0 : (0 : ℝ) ≤ ((p - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hq : ((p - 1 : ℕ) : ℝ) ≤ p := by exact_mod_cast Nat.sub_le p 1
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg _
  have c1 : 0 ≤ clipF A y ^ (p - 2) * clipF B y ^ p := by positivity
  have c1' : clipF A y ^ (p - 2) * clipF B y ^ p ≤ 1 := by
    simpa using mul_le_mul (pow_le_one₀ ha0 ha1) (pow_le_one₀ hb0 hb1 (n := p))
      (by positivity) zero_le_one
  have c2 : 0 ≤ clipF A y ^ (p - 1) * clipF B y ^ (p - 1) := by positivity
  have c2' : clipF A y ^ (p - 1) * clipF B y ^ (p - 1) ≤ 1 := by
    simpa using mul_le_mul (pow_le_one₀ ha0 ha1) (pow_le_one₀ hb0 hb1 (n := p - 1))
      (by positivity) zero_le_one
  have e : dStarG p A B i y =
      (((p - 1 : ℕ) : ℝ) * (clipF A y ^ (p - 2) * clipF B y ^ p)) * (-(2 * (A *ᵥ y) i)) +
        ((p : ℝ) * (clipF A y ^ (p - 1) * clipF B y ^ (p - 1))) * (-(2 * (B *ᵥ y) i)) := by
    simp only [dStarG]; ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  set c := ((p - 1 : ℕ) : ℝ) * (clipF A y ^ (p - 2) * clipF B y ^ p) with hc
  set d := (p : ℝ) * (clipF A y ^ (p - 1) * clipF B y ^ (p - 1)) with hd
  have h1 : c ≤ p := (mul_le_of_le_one_right hq0 c1').trans hq
  have h2 : d ≤ p := mul_le_of_le_one_right hp0 c2'
  have hc0 : 0 ≤ c := mul_nonneg hq0 c1
  have hd0 : 0 ≤ d := mul_nonneg hp0 c2
  clear_value c d
  rw [abs_mul, abs_mul, abs_neg, abs_neg, abs_mul, abs_mul, abs_two, abs_of_nonneg hc0,
    abs_of_nonneg hd0]
  have hu := abs_nonneg ((A *ᵥ y) i)
  have hv := abs_nonneg ((B *ᵥ y) i)
  nlinarith [mul_le_mul_of_nonneg_right h1 hu, mul_le_mul_of_nonneg_right h2 hv]

end Deriv

/-- `x ↦ q_T(x) φ(x)` is `𝖦`-integrable for continuous `φ` with `|φ| ≤ 1`. -/
theorem integrable_qForm_mul_gaussPi (T : Matrix ι ι ℝ) {φ : (ι → ℝ) → ℝ} (hφc : Continuous φ)
    (hφ : ∀ x, |φ x| ≤ 1) : Integrable (fun x => qForm T x * φ x) (gaussPi ι) := by
  set cT := ∑ j, ∑ k, |T j k|
  have hcT : 0 ≤ cT := by positivity
  refine integrable_of_polyBound_gaussPi (K := Fintype.card ι * cT) (m := 2)
    (((continuous_qForm T).mul hφc).aestronglyMeasurable) fun x => ?_
  have hx := norm_nonneg x
  rw [Real.norm_eq_abs, abs_mul]
  have hq : |qForm T x| ≤ Fintype.card ι * cT * ‖x‖ ^ 2 := by
    rw [qForm, dotProduct]
    calc |∑ i, x i * (T *ᵥ x) i| ≤ ∑ i, |x i * (T *ᵥ x) i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : ι, ‖x‖ * (cT * ‖x‖) := Finset.sum_le_sum fun i _ => by
          rw [abs_mul]
          exact mul_le_mul ((Real.norm_eq_abs (x i)) ▸ norm_le_pi_norm x i)
            (abs_mulVec_apply_le T x i) (abs_nonneg _) hx
      _ = Fintype.card ι * cT * ‖x‖ ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  calc |qForm T x| * |φ x| ≤ Fintype.card ι * cT * ‖x‖ ^ 2 * 1 :=
        mul_le_mul hq (hφ x) (abs_nonneg _) (by positivity)
    _ ≤ Fintype.card ι * cT * (1 + ‖x‖) ^ 2 := by
        rw [mul_one]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx (by linarith) 2) (by positivity)

/-- **T.GIBP2.** `2 𝖦 F = 𝖦[(tr A - q_A) α^{p-1} β^p]` for PSD `A, B` and `p ≥ 3`. -/
theorem two_mul_gaussE_starF [DecidableEq ι] {A B : Matrix ι ι ℝ} (hA : A.PosSemidef)
    (hB : B.PosSemidef) {p : ℕ} (hp : 3 ≤ p) :
    2 * gaussE (starF p A B) = gaussE (fun x => (A.trace - qForm A x) * starG p A B x) := by
  set cA := ∑ j, ∑ k, |A j k| with hcA
  set cB := ∑ j, ∑ k, |B j k| with hcB
  have hcA0 : 0 ≤ cA := by positivity
  have hcB0 : 0 ≤ cB := by positivity
  set K : ℝ := 1 + cA + 2 * p * (cA + cB) * cA with hK
  have hg0 : ∀ x, 0 ≤ starG p A B x := clipProd_nonneg _ _ A B
  have hg1 : ∀ x, starG p A B x ≤ 1 := clipProd_le_one hA hB _ _
  have hcont_g : Continuous (starG p A B) := continuous_clipProd _ _ A B
  have hcont_Ax : ∀ (M : Matrix ι ι ℝ) (i : ι), Continuous fun x : ι → ℝ => (M *ᵥ x) i :=
    fun M i => (continuous_apply i).comp (continuous_const.matrix_mulVec continuous_id)
  have hcont_d : ∀ i, Continuous (dSteinF p A B i) := by
    intro i
    unfold dSteinF dStarG
    have h1 := continuous_clipF A
    have h2 := continuous_clipF B
    have h3 := hcont_Ax A i
    have h4 := hcont_Ax B i
    fun_prop
  have hfb : ∀ i x, ‖(A *ᵥ x) i * starG p A B x‖ ≤ K * (1 + ‖x‖) ^ 2 := by
    intro i x
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hg0 x)]
    have h1 := abs_mulVec_apply_le A x i
    have hx := norm_nonneg x
    have hK1 : cA ≤ K := by
      have : 0 ≤ 2 * (p : ℝ) * (cA + cB) * cA := by positivity
      linarith
    calc |(A *ᵥ x) i| * starG p A B x ≤ cA * ‖x‖ * 1 :=
          mul_le_mul h1 (hg1 x) (hg0 x) (by positivity)
      _ ≤ cA * (1 + ‖x‖) ^ 2 := by
          rw [mul_one]; exact mul_le_mul_of_nonneg_left (by nlinarith) hcA0
      _ ≤ K * (1 + ‖x‖) ^ 2 := mul_le_mul_of_nonneg_right hK1 (sq_nonneg _)
  have hdb : ∀ i x, ‖dSteinF p A B i x‖ ≤ K * (1 + ‖x‖) ^ 2 := by
    intro i x
    rw [Real.norm_eq_abs]
    have hx := norm_nonneg x
    have hAi := abs_apply_le_sum A i
    have hu := abs_mulVec_apply_le A x i
    have hv := abs_mulVec_apply_le B x i
    have hd := abs_dStarG_le hA hB p i x
    have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg _
    have hd' : |dStarG p A B i x| ≤ 2 * p * (cA + cB) * ‖x‖ := by
      calc _ ≤ 2 * p * (|(A *ᵥ x) i| + |(B *ᵥ x) i|) := hd
        _ ≤ 2 * p * (cA * ‖x‖ + cB * ‖x‖) := by gcongr
        _ = 2 * p * (cA + cB) * ‖x‖ := by ring
    calc |dSteinF p A B i x| ≤ |A i i| * starG p A B x + |(A *ᵥ x) i| * |dStarG p A B i x| := by
          unfold dSteinF
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul, abs_of_nonneg (hg0 x)]
      _ ≤ cA * 1 + (cA * ‖x‖) * (2 * p * (cA + cB) * ‖x‖) := by
          gcongr
          all_goals first | exact hg0 x | exact hg1 x
      _ ≤ K * (1 + ‖x‖) ^ 2 := by
          have h5 : 0 ≤ 2 * (p : ℝ) * (cA + cB) * cA := by positivity
          nlinarith [mul_nonneg h5 hx, mul_nonneg hcA0 hx]
  have hstein : ∀ i, ∫ x, x i * ((A *ᵥ x) i * starG p A B x) ∂gaussPi ι =
      ∫ x, dSteinF p A B i x ∂gaussPi ι := fun i =>
    stein_gaussPi_of_hasDerivAt i ((hcont_Ax A i).mul hcont_g).aestronglyMeasurable
      (hcont_d i).aestronglyMeasurable
      (fun x t => hasDerivAt_steinF_update hA.isHermitian hB.isHermitian hp x i t)
      (hfb i) (hdb i)
  have hint1 : ∀ i, Integrable (fun x => x i * ((A *ᵥ x) i * starG p A B x)) (gaussPi ι) :=
    fun i => integrable_of_polyBound_gaussPi
      ((continuous_apply i).mul ((hcont_Ax A i).mul hcont_g)).aestronglyMeasurable
      (norm_coord_mul_le (hfb i) i)
  have hint2 : ∀ i, Integrable (dSteinF p A B i) (gaussPi ι) := fun i =>
    integrable_of_polyBound_gaussPi (hcont_d i).aestronglyMeasurable (hdb i)
  have e1 : (fun x => qForm A x * starG p A B x) =
      fun x => ∑ i, x i * ((A *ᵥ x) i * starG p A B x) := by
    funext x
    simp only [qForm, dotProduct, Finset.sum_mul, mul_assoc]
  have e2 : (fun x => A.trace * starG p A B x - 2 * starF p A B x) =
      fun x => ∑ i, dSteinF p A B i x := by
    funext x; exact (sum_dSteinF hA.isHermitian p x).symm
  have hQI : Integrable (fun x => qForm A x * starG p A B x) (gaussPi ι) := by
    rw [e1]; exact integrable_finsetSum _ fun i _ => hint1 i
  have hRI : Integrable (fun x => A.trace * starG p A B x - 2 * starF p A B x) (gaussPi ι) := by
    rw [e2]; exact integrable_finsetSum _ fun i _ => hint2 i
  have hgI : Integrable (fun x => A.trace * starG p A B x) (gaussPi ι) := by
    refine (integrable_const |A.trace|).mono' (continuous_const.mul hcont_g).aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hg0 x)]
    exact mul_le_of_le_one_right (abs_nonneg _) (hg1 x)
  have hQ : ∫ x, qForm A x * starG p A B x ∂gaussPi ι =
      ∫ x, (A.trace * starG p A B x - 2 * starF p A B x) ∂gaussPi ι := by
    rw [e1, e2, integral_finsetSum _ fun i _ => hint1 i, integral_finsetSum _ fun i _ => hint2 i]
    exact Finset.sum_congr rfl fun i _ => hstein i
  unfold gaussE
  calc 2 * ∫ x, starF p A B x ∂gaussPi ι
      = ∫ x, A.trace * starG p A B x ∂gaussPi ι -
          ∫ x, (A.trace * starG p A B x - 2 * starF p A B x) ∂gaussPi ι := by
        rw [← integral_sub hgI hRI, ← integral_const_mul]
        congr 1; funext x; ring
    _ = ∫ x, A.trace * starG p A B x ∂gaussPi ι - ∫ x, qForm A x * starG p A B x ∂gaussPi ι := by
        rw [hQ]
    _ = ∫ x, (A.trace - qForm A x) * starG p A B x ∂gaussPi ι := by
        rw [← integral_sub hgI hQI]
        congr 1; funext x; ring

end BiluLinial.Tight
