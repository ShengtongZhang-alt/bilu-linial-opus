/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.Gauss.GCIEllipsoid
public import BiluLinial.Tight.Gauss.IBP

/-!
# The derivative at `s = 1`: the GCI input of Lemma GR1

`docs/second_order_bilu_linial_tight.tex`, proof of Lemma "Uniform incident-row gain" (GR1),
line 640: for PSD `A, B` and `p > 2`, `𝖦[q_AB α^{p-1} β^{p-1}] ≥ 0`, where
`α = (1 - xᵀAx)₊`, `β = (1 - xᵀBx)₊` and `q_AB(x) = ⟨Ax, Bx⟩`.

* `pitt_of_monotoneOn` (GCI-E3): if `f, g` have continuous, polynomially bounded gradients
  `f', g'` and `s ↦ 𝔼 f(X) g(Yₛ)` is monotone on `[0, 1]`, then `𝔼 f'·g' ≥ 0` (Pitt's
  inequality). Proof by the rotation `(X, Z) ↦ (Y_θ, Y'_θ)` and Stein's identity, using only
  first derivatives.
* `hasFDerivAt_gciClipPow` (GCI-E4): `∇((1 - xᵀAx)₊^p) = -2p (1 - xᵀAx)₊^{p-1} A x` for `p ≥ 2`.
* `gci_clipped` (GCI-T): the target.
-/

@[expose] public section

namespace BiluLinial.Tight

open MeasureTheory ProbabilityTheory Matrix Real Filter Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The continuous linear functional `v ↦ w ⬝ᵥ v`. -/
noncomputable def dotCLM (w : ι → ℝ) : (ι → ℝ) →L[ℝ] ℝ :=
  ∑ i, w i • ContinuousLinearMap.proj i

omit [DecidableEq ι] in
@[simp]
theorem dotCLM_apply (w v : ι → ℝ) : dotCLM w v = w ⬝ᵥ v := by
  simp [dotCLM, dotProduct]

/-! ### GCI-E3: Pitt's inequality from monotonicity -/

section pitt

omit [DecidableEq ι] in
theorem abs_dotProduct_le (u v : ι → ℝ) : |u ⬝ᵥ v| ≤ Fintype.card ι * (‖u‖ * ‖v‖) := by
  unfold dotProduct
  calc |∑ i, u i * v i| ≤ ∑ i, |u i * v i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : ι, ‖u‖ * ‖v‖ := Finset.sum_le_sum fun i _ => by
        rw [abs_mul]
        exact mul_le_mul (by simpa using norm_le_pi_norm u i) (by simpa using norm_le_pi_norm v i)
          (abs_nonneg _) (norm_nonneg _)
    _ = _ := by simp

/-- Rotation by `θ` in each plane `(inl i, inr i)`. -/
noncomputable def rotMat (θ : ℝ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ :=
  fromBlocks (Real.cos θ • 1) (Real.sin θ • 1) (-Real.sin θ • 1) (Real.cos θ • 1)

theorem rotMat_mul_transpose (θ : ℝ) :
    rotMat (ι := ι) θ * (rotMat θ)ᵀ = 1 := by
  rw [rotMat, fromBlocks_transpose, fromBlocks_multiply, ← fromBlocks_one]
  simp only [transpose_smul, transpose_one, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    smul_smul, ← add_smul]
  congr 1
  · rw [← sq, ← sq, Real.cos_sq_add_sin_sq, one_smul]
  · convert zero_smul ℝ (1 : Matrix ι ι ℝ) using 2; ring
  · convert zero_smul ℝ (1 : Matrix ι ι ℝ) using 2; ring
  · rw [show -Real.sin θ * -Real.sin θ + Real.cos θ * Real.cos θ = 1 by
      nlinarith [Real.sin_sq_add_cos_sq θ], one_smul]

omit [DecidableEq ι] in
theorem rotMat_mulVec_inl [DecidableEq ι] (θ : ℝ) (G : ι ⊕ ι → ℝ) (i : ι) :
    (rotMat θ *ᵥ G) (Sum.inl i) = Real.cos θ * G (Sum.inl i) + Real.sin θ * G (Sum.inr i) := by
  simp [rotMat, mulVec, dotProduct, Fintype.sum_sum_type, Matrix.smul_apply, one_apply]

omit [DecidableEq ι] in
theorem rotMat_mulVec_inr [DecidableEq ι] (θ : ℝ) (G : ι ⊕ ι → ℝ) (i : ι) :
    (rotMat θ *ᵥ G) (Sum.inr i) = -Real.sin θ * G (Sum.inl i) + Real.cos θ * G (Sum.inr i) := by
  simp [rotMat, mulVec, dotProduct, Fintype.sum_sum_type, Matrix.smul_apply, one_apply]

/-- `Y_θ = cos θ X + sin θ Z`. -/
noncomputable def gYθ (θ : ℝ) (G : ι ⊕ ι → ℝ) : ι → ℝ :=
  fun i => Real.cos θ * G (Sum.inl i) + Real.sin θ * G (Sum.inr i)

/-- `Y'_θ = -sin θ X + cos θ Z = ∂_θ Y_θ`. -/
noncomputable def gY'θ (θ : ℝ) (G : ι ⊕ ι → ℝ) : ι → ℝ :=
  fun i => -Real.sin θ * G (Sum.inl i) + Real.cos θ * G (Sum.inr i)

/-- `X = cos θ Y_θ - sin θ Y'_θ`, written in the rotated coordinates. -/
noncomputable def gXθ (θ : ℝ) (W : ι ⊕ ι → ℝ) : ι → ℝ :=
  fun i => Real.cos θ * W (Sum.inl i) - Real.sin θ * W (Sum.inr i)

/-- Second component `Z = G ∘ inr`. -/
def gZ (G : ι ⊕ ι → ℝ) : ι → ℝ := fun i => G (Sum.inr i)

theorem gXθ_rot (θ : ℝ) (G : ι ⊕ ι → ℝ) : gXθ θ (rotMat θ *ᵥ G) = gX G := by
  ext i
  simp only [gXθ, gX, rotMat_mulVec_inl, rotMat_mulVec_inr]
  linear_combination (G (Sum.inl i)) * Real.cos_sq_add_sin_sq θ

theorem gX_rot (θ : ℝ) (G : ι ⊕ ι → ℝ) : gX (rotMat θ *ᵥ G) = gYθ θ G := by
  ext i; simp only [gX, gYθ, rotMat_mulVec_inl]

theorem gZ_rot (θ : ℝ) (G : ι ⊕ ι → ℝ) : gZ (rotMat θ *ᵥ G) = gY'θ θ G := by
  ext i; simp only [gZ, gY'θ, rotMat_mulVec_inr]

omit [DecidableEq ι] in
theorem norm_gX_le (G : ι ⊕ ι → ℝ) : ‖gX G‖ ≤ ‖G‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i => norm_le_pi_norm G (Sum.inl i)

omit [DecidableEq ι] in
theorem norm_gZ_le (G : ι ⊕ ι → ℝ) : ‖gZ G‖ ≤ ‖G‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i => norm_le_pi_norm G (Sum.inr i)

omit [DecidableEq ι] in
theorem norm_cos_sin_comb_le (a b : ℝ) (ha : |a| ≤ 1) (hb : |b| ≤ 1) (G : ι ⊕ ι → ℝ) :
    ‖fun i => a * G (Sum.inl i) + b * G (Sum.inr i)‖ ≤ 2 * ‖G‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
  rw [Real.norm_eq_abs]
  have h1 : |G (Sum.inl i)| ≤ ‖G‖ := by simpa using norm_le_pi_norm G (Sum.inl i)
  have h2 : |G (Sum.inr i)| ≤ ‖G‖ := by simpa using norm_le_pi_norm G (Sum.inr i)
  calc |a * G (Sum.inl i) + b * G (Sum.inr i)| ≤ |a| * |G (Sum.inl i)| + |b| * |G (Sum.inr i)| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ 1 * ‖G‖ + 1 * ‖G‖ := by gcongr
    _ = 2 * ‖G‖ := by ring

omit [DecidableEq ι] in
theorem norm_gYθ_le (θ : ℝ) (G : ι ⊕ ι → ℝ) : ‖gYθ θ G‖ ≤ 2 * ‖G‖ :=
  norm_cos_sin_comb_le _ _ (Real.abs_cos_le_one θ) (Real.abs_sin_le_one θ) G

omit [DecidableEq ι] in
theorem norm_gY'θ_le (θ : ℝ) (G : ι ⊕ ι → ℝ) : ‖gY'θ θ G‖ ≤ 2 * ‖G‖ :=
  norm_cos_sin_comb_le _ _ (by rw [abs_neg]; exact Real.abs_sin_le_one θ)
    (Real.abs_cos_le_one θ) G

omit [DecidableEq ι] in
theorem norm_gXθ_le (θ : ℝ) (G : ι ⊕ ι → ℝ) : ‖gXθ θ G‖ ≤ 2 * ‖G‖ := by
  have := norm_cos_sin_comb_le (Real.cos θ) (-Real.sin θ) (Real.abs_cos_le_one θ)
    (by rw [abs_neg]; exact Real.abs_sin_le_one θ) G
  convert this using 2
  ext i
  simp only [gXθ]
  ring

omit [DecidableEq ι] in
theorem one_add_pow_le_of_norm_le {y : ι → ℝ} {G : ι ⊕ ι → ℝ} (h : ‖y‖ ≤ 2 * ‖G‖) (m : ℕ) :
    (1 + ‖y‖) ^ m ≤ 2 ^ m * (1 + ‖G‖) ^ m := by
  rw [← mul_pow]
  exact pow_le_pow_left₀ (by positivity) (by linarith [norm_nonneg G]) m

omit [DecidableEq ι] in
theorem one_add_pow_le_of_norm_le' {y : ι → ℝ} {G : ι ⊕ ι → ℝ} (h : ‖y‖ ≤ ‖G‖) (m : ℕ) :
    (1 + ‖y‖) ^ m ≤ 2 ^ m * (1 + ‖G‖) ^ m :=
  one_add_pow_le_of_norm_le (h.trans (by linarith [norm_nonneg G])) m

omit [DecidableEq ι] in
theorem integral_gX_eq (F : (ι → ℝ) → ℝ) :
    ∫ W, F (gX W) ∂gaussPi (ι ⊕ ι) = ∫ x, F x ∂gaussPi ι := by
  have hmp := measurePreserving_sumPiEquivProdPi_symm
    (X := fun _ : ι ⊕ ι => ℝ) (fun _ => gaussianReal 0 1)
  rw [gaussPi, ← hmp.integral_comp (MeasurableEquiv.measurableEmbedding _)]
  have : ∀ p : (ι → ℝ) × (ι → ℝ), gX ((MeasurableEquiv.sumPiEquivProdPi
      (fun _ : ι ⊕ ι => ℝ)).symm p) = p.1 := fun p => rfl
  simp_rw [this]
  rw [integral_fun_fst]
  simp [gaussPi]

/-- **GCI-E3** (Pitt's inequality from monotonicity). -/
theorem pitt_of_monotoneOn {f g : (ι → ℝ) → ℝ} {f' g' : (ι → ℝ) → ι → ℝ}
    (hf : ∀ x, HasFDerivAt f (dotCLM (f' x)) x) (hg : ∀ x, HasFDerivAt g (dotCLM (g' x)) x)
    (hf'c : Continuous f') (hg'c : Continuous g') {K : ℝ} {m : ℕ}
    (hfb : ∀ x, ‖f x‖ ≤ K * (1 + ‖x‖) ^ m) (hgb : ∀ x, ‖g x‖ ≤ K * (1 + ‖x‖) ^ m)
    (hf'b : ∀ x, ‖f' x‖ ≤ K * (1 + ‖x‖) ^ m) (hg'b : ∀ x, ‖g' x‖ ≤ K * (1 + ‖x‖) ^ m)
    (hmono : MonotoneOn (fun s => ∫ G, f (gX G) * g (gY s G) ∂gaussPi (ι ⊕ ι)) (Set.Icc 0 1)) :
    0 ≤ ∫ x, f' x ⬝ᵥ g' x ∂gaussPi ι := by
  have hK : 0 ≤ K := by
    have := (norm_nonneg _).trans (hfb 0)
    simpa using this
  have hfc : Continuous f := continuous_iff_continuousAt.2 fun x => (hf x).continuousAt
  have hgc : Continuous g := continuous_iff_continuousAt.2 fun x => (hg x).continuousAt
  set n : ℝ := (Fintype.card ι : ℝ)
  have hn : 0 ≤ n := by positivity
  set C : ℝ := 2 * n * K ^ 2 * 2 ^ (2 * m + 2)
  have hC : 0 ≤ C := by positivity
  set Kt : ℝ → ℝ := fun θ => ∫ W, f' (gXθ θ W) ⬝ᵥ g' (gX W) ∂gaussPi (ι ⊕ ι)
  set Hθ : ℝ → ℝ := fun θ => ∫ G, f (gX G) * g (gYθ θ G) ∂gaussPi (ι ⊕ ι)
  have hcontθ : ∀ G : ι ⊕ ι → ℝ, Continuous fun θ => gYθ θ G := fun G => by
    unfold gYθ; fun_prop
  have hcontG : ∀ θ, Continuous (gYθ (ι := ι) θ) := fun θ => by unfold gYθ; fun_prop
  have hcontG' : ∀ θ, Continuous (gY'θ (ι := ι) θ) := fun θ => by unfold gY'θ; fun_prop
  have hcontX : ∀ θ, Continuous (gXθ (ι := ι) θ) := fun θ => by unfold gXθ; fun_prop
  have hcontgX : Continuous (gX (ι := ι)) := by unfold gX; fun_prop
  have hcontgZ : Continuous (gZ (ι := ι)) := by unfold gZ; fun_prop
  -- Step A: differentiation under the integral sign
  have hderivA : ∀ θ, HasDerivAt Hθ
      (∫ G, f (gX G) * (g' (gYθ θ G) ⬝ᵥ gY'θ θ G) ∂gaussPi (ι ⊕ ι)) θ := by
    intro θ
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := gaussPi (ι ⊕ ι))
      (F := fun θ G => f (gX G) * g (gYθ θ G))
      (F' := fun θ G => f (gX G) * (g' (gYθ θ G) ⬝ᵥ gY'θ θ G)) (x₀ := θ)
      (s := Set.univ) Filter.univ_mem
      (bound := fun G : ι ⊕ ι → ℝ => C * (1 + ‖G‖) ^ (2 * m + 1)) ?_ ?_ ?_ ?_ ?_ ?_).2
    · exact Eventually.of_forall fun θ' =>
        ((hfc.comp hcontgX).mul (hgc.comp (hcontG θ'))).aestronglyMeasurable
    · refine integrable_of_polyBound_gaussPi
        ((hfc.comp hcontgX).mul (hgc.comp (hcontG θ))).aestronglyMeasurable
        (K := K ^ 2 * 2 ^ (2 * m)) (m := 2 * m) fun G => ?_
      rw [norm_mul]
      calc ‖f (gX G)‖ * ‖g (gYθ θ G)‖ ≤ (K * (2 ^ m * (1 + ‖G‖) ^ m)) *
            (K * (2 ^ m * (1 + ‖G‖) ^ m)) := by
            gcongr
            · exact (hfb _).trans (by gcongr; exact one_add_pow_le_of_norm_le' (norm_gX_le G) m)
            · exact (hgb _).trans (by gcongr; exact one_add_pow_le_of_norm_le (norm_gYθ_le θ G) m)
        _ = K ^ 2 * 2 ^ (2 * m) * (1 + ‖G‖) ^ (2 * m) := by
            rw [two_mul, pow_add, pow_add]; ring
    · exact ((hfc.comp hcontgX).mul (Continuous.dotProduct (hg'c.comp (hcontG θ))
        (hcontG' θ))).aestronglyMeasurable
    · refine Eventually.of_forall fun G θ' _ => ?_
      rw [norm_mul, Real.norm_eq_abs (_ ⬝ᵥ _)]
      have h1 : ‖f (gX G)‖ ≤ K * (2 ^ m * (1 + ‖G‖) ^ m) :=
        (hfb _).trans (by gcongr; exact one_add_pow_le_of_norm_le' (norm_gX_le G) m)
      have h2 : ‖g' (gYθ θ' G)‖ ≤ K * (2 ^ m * (1 + ‖G‖) ^ m) :=
        (hg'b _).trans (by gcongr; exact one_add_pow_le_of_norm_le (norm_gYθ_le θ' G) m)
      have h3 : ‖gY'θ θ' G‖ ≤ 2 * (1 + ‖G‖) := by
        linarith [norm_gY'θ_le θ' G, norm_nonneg G]
      have h4 := abs_dotProduct_le (g' (gYθ θ' G)) (gY'θ θ' G)
      calc ‖f (gX G)‖ * |g' (gYθ θ' G) ⬝ᵥ gY'θ θ' G|
          ≤ (K * (2 ^ m * (1 + ‖G‖) ^ m)) * (n * ((K * (2 ^ m * (1 + ‖G‖) ^ m)) *
              (2 * (1 + ‖G‖)))) := by
            gcongr
            exact h4.trans (by gcongr)
        _ = C / 4 * (1 + ‖G‖) ^ (2 * m + 1) := by
            simp only [C]
            ring
        _ ≤ C * (1 + ‖G‖) ^ (2 * m + 1) := by
            have : 0 ≤ C * (1 + ‖G‖) ^ (2 * m + 1) := by positivity
            linarith
    · exact (integrable_one_add_norm_pow_gaussPi (2 * m + 1)).const_mul C
    · refine Eventually.of_forall fun G θ' _ => ?_
      have hY : HasDerivAt (fun θ => gYθ θ G) (gY'θ θ' G) θ' := by
        rw [hasDerivAt_pi]
        intro i
        simp only [gYθ, gY'θ]
        have := ((Real.hasDerivAt_cos θ').mul_const (G (Sum.inl i))).add
          ((Real.hasDerivAt_sin θ').mul_const (G (Sum.inr i)))
        convert this using 1 <;> ring
      have := ((hg (gYθ θ' G)).comp_hasDerivAt θ' hY).const_mul (f (gX G))
      simpa [dotCLM_apply, Function.comp_def] using this
  -- Steps B and C: rotation and Stein's identity
  have hBC : ∀ θ, ∫ G, f (gX G) * (g' (gYθ θ G) ⬝ᵥ gY'θ θ G) ∂gaussPi (ι ⊕ ι) = -Real.sin θ * Kt θ := by
    intro θ
    -- rotation
    have hrot : ∫ G, f (gX G) * (g' (gYθ θ G) ⬝ᵥ gY'θ θ G) ∂gaussPi (ι ⊕ ι) =
        ∫ W, f (gXθ θ W) * (g' (gX W) ⬝ᵥ gZ W) ∂gaussPi (ι ⊕ ι) := by
      have hmap := gaussPi_map_mulVec_orthogonal (rotMat_mul_transpose (ι := ι) θ)
      have hΦ : Continuous fun W : ι ⊕ ι → ℝ => f (gXθ θ W) * (g' (gX W) ⬝ᵥ gZ W) :=
        (hfc.comp (hcontX θ)).mul (Continuous.dotProduct (hg'c.comp hcontgX) hcontgZ)
      calc ∫ G, f (gX G) * (g' (gYθ θ G) ⬝ᵥ gY'θ θ G) ∂gaussPi (ι ⊕ ι)
          = ∫ G, (fun W => f (gXθ θ W) * (g' (gX W) ⬝ᵥ gZ W)) (rotMat θ *ᵥ G)
              ∂gaussPi (ι ⊕ ι) := by
            congr 1; ext G; simp only [gXθ_rot, gX_rot, gZ_rot]
        _ = ∫ W, f (gXθ θ W) * (g' (gX W) ⬝ᵥ gZ W)
              ∂((gaussPi (ι ⊕ ι)).map fun G => rotMat θ *ᵥ G) :=
            (integral_map (by fun_prop) hΦ.aestronglyMeasurable).symm
        _ = ∫ W, f (gXθ θ W) * (g' (gX W) ⬝ᵥ gZ W) ∂gaussPi (ι ⊕ ι) := by rw [hmap]
    rw [hrot]
    -- Stein in each coordinate `inr i`
    have hstein : ∀ i : ι, ∫ W, W (Sum.inr i) * (f (gXθ θ W) * g' (gX W) i) ∂gaussPi (ι ⊕ ι) =
        ∫ W, -Real.sin θ * f' (gXθ θ W) i * g' (gX W) i ∂gaussPi (ι ⊕ ι) := by
      intro i
      have hgXu : ∀ (W : ι ⊕ ι → ℝ) (s : ℝ), gX (Function.update W (Sum.inr i) s) = gX W := by
        intro W s; ext j; simp [gX]
      refine stein_gaussPi_of_hasDerivAt (Sum.inr i)
        ((hfc.comp (hcontX θ)).mul ((continuous_apply i).comp
          (hg'c.comp hcontgX))).aestronglyMeasurable
        ((continuous_const.mul ((continuous_apply i).comp (hf'c.comp (hcontX θ)))).mul
          ((continuous_apply i).comp (hg'c.comp hcontgX))).aestronglyMeasurable
        (fun W t => ?_) (K := K ^ 2 * 2 ^ (2 * m)) (m := 2 * m) (fun W => ?_) (fun W => ?_)
      · have hXu : HasDerivAt (fun s => gXθ θ (Function.update W (Sum.inr i) s))
            (-Real.sin θ • Pi.single i (1 : ℝ)) t := by
          rw [hasDerivAt_pi]
          intro j
          have e1 : ∀ s, Function.update W (Sum.inr i) s (Sum.inl j) = W (Sum.inl j) :=
            fun s => by simp
          have e2 : ∀ s, Function.update W (Sum.inr i) s (Sum.inr j) =
              if j = i then s else W (Sum.inr j) := fun s => by
            by_cases hj : j = i
            · rw [hj]; simp
            · simp [hj]
          simp only [gXθ, e1, e2, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
          by_cases hj : j = i
          · simp only [hj, ite_true, mul_one]
            simpa using ((hasDerivAt_id t).const_mul (Real.sin θ)).const_sub
              (Real.cos θ * W (Sum.inl i))
          · simp only [hj, ite_false, mul_zero]
            exact hasDerivAt_const _ _
        have hcomp := (hf (gXθ θ (Function.update W (Sum.inr i) t))).comp_hasDerivAt t hXu
        simp only [hgXu]
        refine (hcomp.mul_const (g' (gX W) i)).congr_deriv ?_
        simp only [dotCLM_apply, dotProduct_smul, dotProduct_single, smul_eq_mul, mul_one]
        try ring
      · rw [norm_mul]
        calc ‖f (gXθ θ W)‖ * ‖g' (gX W) i‖ ≤ (K * (2 ^ m * (1 + ‖W‖) ^ m)) *
              (K * (2 ^ m * (1 + ‖W‖) ^ m)) := by
              gcongr
              · exact (hfb _).trans (by gcongr; exact one_add_pow_le_of_norm_le (norm_gXθ_le θ W) m)
              · exact (norm_le_pi_norm _ i).trans ((hg'b _).trans
                  (by gcongr; exact one_add_pow_le_of_norm_le' (norm_gX_le W) m))
          _ = K ^ 2 * 2 ^ (2 * m) * (1 + ‖W‖) ^ (2 * m) := by
              rw [two_mul, pow_add, pow_add]; ring
      · rw [norm_mul, norm_mul, Real.norm_eq_abs (-Real.sin θ), abs_neg]
        calc |Real.sin θ| * ‖f' (gXθ θ W) i‖ * ‖g' (gX W) i‖ ≤ 1 * (K * (2 ^ m * (1 + ‖W‖) ^ m)) *
              (K * (2 ^ m * (1 + ‖W‖) ^ m)) := by
              gcongr
              · exact Real.abs_sin_le_one θ
              · exact (norm_le_pi_norm _ i).trans ((hf'b _).trans
                  (by gcongr; exact one_add_pow_le_of_norm_le (norm_gXθ_le θ W) m))
              · exact (norm_le_pi_norm _ i).trans ((hg'b _).trans
                  (by gcongr; exact one_add_pow_le_of_norm_le' (norm_gX_le W) m))
          _ = K ^ 2 * 2 ^ (2 * m) * (1 + ‖W‖) ^ (2 * m) := by
              rw [two_mul, pow_add, pow_add]; ring
    -- integrability of the summands
    have hpb : ∀ W : ι ⊕ ι → ℝ, ∀ i, ‖f (gXθ θ W)‖ * ‖g' (gX W) i‖ ≤
        K ^ 2 * 2 ^ (2 * m) * (1 + ‖W‖) ^ (2 * m) := by
      intro W i
      calc ‖f (gXθ θ W)‖ * ‖g' (gX W) i‖ ≤ (K * (2 ^ m * (1 + ‖W‖) ^ m)) *
            (K * (2 ^ m * (1 + ‖W‖) ^ m)) := by
            gcongr
            · exact (hfb _).trans (by gcongr; exact one_add_pow_le_of_norm_le (norm_gXθ_le θ W) m)
            · exact (norm_le_pi_norm _ i).trans ((hg'b _).trans
                (by gcongr; exact one_add_pow_le_of_norm_le' (norm_gX_le W) m))
        _ = K ^ 2 * 2 ^ (2 * m) * (1 + ‖W‖) ^ (2 * m) := by
            rw [two_mul, pow_add, pow_add]; ring
    have hint1 : ∀ i : ι, Integrable (fun W => W (Sum.inr i) * (f (gXθ θ W) * g' (gX W) i)) (gaussPi (ι ⊕ ι)) := by
      intro i
      refine integrable_of_polyBound_gaussPi
        ((continuous_apply (Sum.inr i)).mul ((hfc.comp (hcontX θ)).mul ((continuous_apply i).comp
          (hg'c.comp hcontgX)))).aestronglyMeasurable
        (K := K ^ 2 * 2 ^ (2 * m)) (m := 2 * m + 1) fun W => ?_
      rw [norm_mul, norm_mul, pow_succ]
      have hW : ‖W (Sum.inr i)‖ ≤ 1 + ‖W‖ := by
        linarith [norm_le_pi_norm W (Sum.inr i)]
      calc ‖W (Sum.inr i)‖ * (‖f (gXθ θ W)‖ * ‖g' (gX W) i‖)
          ≤ (1 + ‖W‖) * (K ^ 2 * 2 ^ (2 * m) * (1 + ‖W‖) ^ (2 * m)) :=
            mul_le_mul hW (hpb W i) (by positivity) (by positivity)
        _ = _ := by ring
    have hint2 : ∀ i : ι, Integrable (fun W => -Real.sin θ * f' (gXθ θ W) i * g' (gX W) i) (gaussPi (ι ⊕ ι)) := by
      intro i
      refine integrable_of_polyBound_gaussPi
        ((continuous_const.mul ((continuous_apply i).comp (hf'c.comp (hcontX θ)))).mul
          ((continuous_apply i).comp (hg'c.comp hcontgX))).aestronglyMeasurable
        (K := K ^ 2 * 2 ^ (2 * m)) (m := 2 * m) fun W => ?_
      rw [norm_mul, norm_mul, Real.norm_eq_abs (-Real.sin θ), abs_neg]
      calc |Real.sin θ| * ‖f' (gXθ θ W) i‖ * ‖g' (gX W) i‖ ≤ 1 * (K * (2 ^ m * (1 + ‖W‖) ^ m)) *
            (K * (2 ^ m * (1 + ‖W‖) ^ m)) := by
            gcongr
            · exact Real.abs_sin_le_one θ
            · exact (norm_le_pi_norm _ i).trans ((hf'b _).trans
                (by gcongr; exact one_add_pow_le_of_norm_le (norm_gXθ_le θ W) m))
            · exact (norm_le_pi_norm _ i).trans ((hg'b _).trans
                (by gcongr; exact one_add_pow_le_of_norm_le' (norm_gX_le W) m))
        _ = K ^ 2 * 2 ^ (2 * m) * (1 + ‖W‖) ^ (2 * m) := by
            rw [two_mul, pow_add, pow_add]; ring
    calc ∫ W, f (gXθ θ W) * (g' (gX W) ⬝ᵥ gZ W) ∂gaussPi (ι ⊕ ι)
        = ∫ W, ∑ i, W (Sum.inr i) * (f (gXθ θ W) * g' (gX W) i) ∂gaussPi (ι ⊕ ι) := by
          congr 1; ext W
          simp only [dotProduct, gZ, Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = ∑ i, ∫ W, W (Sum.inr i) * (f (gXθ θ W) * g' (gX W) i) ∂gaussPi (ι ⊕ ι) :=
          integral_finsetSum _ fun i _ => hint1 i
      _ = ∑ i, ∫ W, -Real.sin θ * f' (gXθ θ W) i * g' (gX W) i ∂gaussPi (ι ⊕ ι) :=
          Finset.sum_congr rfl fun i _ => hstein i
      _ = ∫ W, ∑ i, -Real.sin θ * f' (gXθ θ W) i * g' (gX W) i ∂gaussPi (ι ⊕ ι) :=
          (integral_finsetSum _ fun i _ => hint2 i).symm
      _ = -Real.sin θ * Kt θ := by
          rw [← integral_const_mul]
          congr 1; ext W
          simp only [dotProduct, Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
  have hderiv : ∀ θ, HasDerivAt Hθ (-Real.sin θ * Kt θ) θ := fun θ => hBC θ ▸ hderivA θ
  -- Step D: monotonicity gives `Kt θ ≥ 0` on `(0, π/2)`
  have hHθ : ∀ θ ∈ Set.Icc (0 : ℝ) (π / 2),
      Hθ θ = ∫ G, f (gX G) * g (gY (Real.cos θ) G) ∂gaussPi (ι ⊕ ι) := by
    intro θ hθ
    have hsin : Real.sin θ = √(1 - Real.cos θ ^ 2) :=
      Real.sin_eq_sqrt_one_sub_cos_sq hθ.1 (by linarith [hθ.2, Real.pi_pos])
    simp only [Hθ]
    congr 1; ext G
    congr 2
    ext i
    simp only [gYθ, gY, hsin]
  have hanti : AntitoneOn Hθ (Set.Icc 0 (π / 2)) := by
    intro θ hθ θ' hθ' hle
    rw [hHθ θ hθ, hHθ θ' hθ']
    have hc : ∀ x ∈ Set.Icc (0 : ℝ) (π / 2), Real.cos x ∈ Set.Icc (0 : ℝ) 1 := fun x hx =>
      ⟨Real.cos_nonneg_of_mem_Icc ⟨by linarith [hx.1, Real.pi_pos], hx.2⟩, Real.cos_le_one x⟩
    exact hmono (hc θ' hθ') (hc θ hθ)
      (Real.cos_le_cos_of_nonneg_of_le_pi hθ.1 (by linarith [hθ'.2, Real.pi_pos]) hle)
  have hKt_nonneg : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), 0 ≤ Kt θ := by
    intro θ hθ
    have h1 := deriv_nonpos_of_antitoneOn hanti hθ
    rw [(hderiv θ).deriv] at h1
    have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
    nlinarith
  -- Step E: let `θ → 0⁺`
  have hKt_cont : ContinuousAt Kt 0 := by
    refine continuousAt_of_dominated (bound := fun W => n * (K ^ 2 * 2 ^ (2 * m)) *
      (1 + ‖W‖) ^ (2 * m)) ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun θ =>
        (Continuous.dotProduct (hf'c.comp (hcontX θ)) (hg'c.comp hcontgX)).aestronglyMeasurable
    · refine Eventually.of_forall fun θ => Eventually.of_forall fun W => ?_
      rw [Real.norm_eq_abs]
      refine (abs_dotProduct_le _ _).trans ?_
      calc n * (‖f' (gXθ θ W)‖ * ‖g' (gX W)‖) ≤ n * ((K * (2 ^ m * (1 + ‖W‖) ^ m)) *
            (K * (2 ^ m * (1 + ‖W‖) ^ m))) := by
            gcongr
            · exact (hf'b _).trans (by gcongr; exact one_add_pow_le_of_norm_le (norm_gXθ_le θ W) m)
            · exact (hg'b _).trans (by gcongr; exact one_add_pow_le_of_norm_le' (norm_gX_le W) m)
        _ = n * (K ^ 2 * 2 ^ (2 * m)) * (1 + ‖W‖) ^ (2 * m) := by
            rw [two_mul, pow_add, pow_add]; ring
    · exact (integrable_one_add_norm_pow_gaussPi (2 * m)).const_mul _
    · refine Eventually.of_forall fun W => ?_
      have : Continuous fun θ => gXθ θ W := by unfold gXθ; fun_prop
      exact ((hf'c.comp this).dotProduct continuous_const).continuousAt
  have hKt0 : 0 ≤ Kt 0 := by
    have hlim : Tendsto Kt (𝓝[>] 0) (𝓝 (Kt 0)) := hKt_cont.tendsto.mono_left nhdsWithin_le_nhds
    refine ge_of_tendsto hlim ?_
    have hmem : Set.Ioo (0 : ℝ) (π / 2) ∈ 𝓝[>] (0 : ℝ) :=
      Ioo_mem_nhdsGT (by linarith [Real.pi_pos])
    filter_upwards [hmem] with θ hθ using hKt_nonneg θ hθ
  have hKt0' : Kt 0 = ∫ x, f' x ⬝ᵥ g' x ∂gaussPi ι := by
    have : ∀ W : ι ⊕ ι → ℝ, gXθ 0 W = gX W := by
      intro W; ext i; simp [gXθ, gX]
    simp only [Kt, this]
    exact integral_gX_eq (fun x => f' x ⬝ᵥ g' x)
  rw [← hKt0']
  exact hKt0

end pitt

/-! ### GCI-E4: the clipped power -/

/-- `t ↦ (t₊)^p` has derivative `p (t₊)^{p-1}` for `p ≥ 2`. -/
theorem hasDerivAt_max_zero_pow {p : ℕ} (hp : 2 ≤ p) (t : ℝ) :
    HasDerivAt (fun t : ℝ => max t 0 ^ p) (p * max t 0 ^ (p - 1)) t := by
  rcases lt_trichotomy t 0 with ht | ht | ht
  · have hev : (fun t : ℝ => max t 0 ^ p) =ᶠ[𝓝 t] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds ht] with s hs
      rw [max_eq_right (le_of_lt hs), zero_pow (by omega)]
    rw [max_eq_right ht.le, zero_pow (by omega), mul_zero]
    exact (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq hev
  · subst ht
    rw [max_self, zero_pow (by omega), mul_zero, hasDerivAt_iff_isLittleO]
    simp only [max_self, zero_pow (show p ≠ 0 by omega), sub_zero, smul_zero]
    have h1 : (fun x : ℝ => x ^ p) =o[𝓝 0] fun x => x :=
      Asymptotics.isLittleO_pow_id (by omega)
    refine Asymptotics.IsBigO.trans_isLittleO ?_ h1
    refine Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall fun x => ?_)
    rw [one_mul, norm_pow, norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      exact max_le (le_abs_self x) (abs_nonneg x)) p
  · have hev : (fun t : ℝ => max t 0 ^ p) =ᶠ[𝓝 t] fun s => s ^ p := by
      filter_upwards [Ioi_mem_nhds ht] with s hs
      rw [max_eq_left (le_of_lt hs)]
    rw [max_eq_left ht.le]
    exact (hasDerivAt_pow p t).congr_of_eventuallyEq hev

omit [DecidableEq ι] in
/-- The derivative of `xᵀAx` for symmetric `A`. -/
theorem hasFDerivAt_quadForm (A : Matrix ι ι ℝ) (hA : A.IsSymm) (x : ι → ℝ) :
    HasFDerivAt (fun x => x ⬝ᵥ (A *ᵥ x)) (dotCLM ((2 : ℝ) • (A *ᵥ x))) x := by
  set L : (ι → ℝ) →L[ℝ] (ι → ℝ) := LinearMap.toContinuousLinearMap (Matrix.mulVecLin A)
  have hL : ∀ y, L y = A *ᵥ y := fun y => rfl
  have hterm : ∀ i, HasFDerivAt (fun y : ι → ℝ => y i * (A *ᵥ y) i)
      (x i • ((ContinuousLinearMap.proj i).comp L) + (A *ᵥ x) i • ContinuousLinearMap.proj i) x := by
    intro i
    have h1 : HasFDerivAt (fun y : ι → ℝ => y i) (ContinuousLinearMap.proj i) x :=
      hasFDerivAt_apply (𝕜 := ℝ) i x
    have h2 : HasFDerivAt (fun y : ι → ℝ => (A *ᵥ y) i) ((ContinuousLinearMap.proj i).comp L) x :=
      ((ContinuousLinearMap.proj i).comp L).hasFDerivAt
    exact h1.mul h2
  have hsum := HasFDerivAt.fun_sum (u := Finset.univ) fun i _ => hterm i
  have hD : dotCLM ((2 : ℝ) • (A *ᵥ x)) = ∑ i ∈ Finset.univ,
      (x i • ((ContinuousLinearMap.proj i).comp L) + (A *ᵥ x) i • ContinuousLinearMap.proj i) := by
    refine ContinuousLinearMap.ext fun v => ?_
    rw [ContinuousLinearMap.sum_apply]
    simp only [dotCLM_apply, _root_.add_apply, _root_.smul_apply, ContinuousLinearMap.coe_comp,
      Function.comp_apply, ContinuousLinearMap.proj_apply, hL, smul_eq_mul, Finset.sum_add_distrib]
    have hsymm : ∑ i, x i * (A *ᵥ v) i = ∑ i, (A *ᵥ x) i * v i := by
      have h : x ⬝ᵥ (A *ᵥ v) = (A *ᵥ x) ⬝ᵥ v := by
        rw [dotProduct_mulVec, ← mulVec_transpose, hA.eq]
      simpa [dotProduct] using h
    rw [hsymm]
    simp [dotProduct, two_mul, Finset.sum_add_distrib, add_mul]
  rw [hD]
  exact hsum

omit [DecidableEq ι] in
/-- **GCI-E4.** The gradient of `((1 - xᵀAx)₊)^p` for symmetric `A` and `p ≥ 2`. -/
theorem hasFDerivAt_gciClipPow (A : Matrix ι ι ℝ) (hA : A.IsSymm) {p : ℕ} (hp : 2 ≤ p)
    (x : ι → ℝ) :
    HasFDerivAt (gciClipPow A p)
      (dotCLM ((-(2 * (p : ℝ)) * max (1 - x ⬝ᵥ (A *ᵥ x)) 0 ^ (p - 1)) • (A *ᵥ x))) x := by
  have hq : HasFDerivAt (fun x => 1 - x ⬝ᵥ (A *ᵥ x)) (-dotCLM ((2 : ℝ) • (A *ᵥ x))) x := by
    simpa using (hasFDerivAt_quadForm A hA x).const_sub 1
  have hh := (hasDerivAt_max_zero_pow hp (1 - x ⬝ᵥ (A *ᵥ x))).hasFDerivAt
  have hcomp := hh.comp x hq
  have hD : (ContinuousLinearMap.toSpanSingleton ℝ ((p : ℝ) * max (1 - x ⬝ᵥ (A *ᵥ x)) 0 ^ (p - 1))).comp
      (-dotCLM ((2 : ℝ) • (A *ᵥ x))) =
      dotCLM ((-(2 * (p : ℝ)) * max (1 - x ⬝ᵥ (A *ᵥ x)) 0 ^ (p - 1)) • (A *ᵥ x)) := by
    refine ContinuousLinearMap.ext (fun v : ι → ℝ => ?_)
    simp only [dotCLM_apply, ContinuousLinearMap.coe_comp', Function.comp_apply,
      ContinuousLinearMap.neg_apply, ContinuousLinearMap.toSpanSingleton_apply, smul_dotProduct,
      smul_eq_mul]
    ring
  exact hcomp.congr_fderiv hD

omit [DecidableEq ι] in
theorem norm_mulVec_le (A : Matrix ι ι ℝ) (x : ι → ℝ) :
    ‖A *ᵥ x‖ ≤ (∑ i, ∑ j, |A i j|) * ‖x‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
  rw [Real.norm_eq_abs, mulVec, dotProduct]
  calc |∑ j, A i j * x j| ≤ ∑ j, |A i j| * ‖x‖ := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left ((Real.norm_eq_abs (x j)) ▸ norm_le_pi_norm x j)
          (abs_nonneg _)
    _ = (∑ j, |A i j|) * ‖x‖ := by rw [Finset.sum_mul]
    _ ≤ (∑ i, ∑ j, |A i j|) * ‖x‖ :=
        mul_le_mul_of_nonneg_right (Finset.single_le_sum (f := fun i => ∑ j, |A i j|)
          (fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _) (Finset.mem_univ i))
          (norm_nonneg x)

/-- **GCI-T.** The Gaussian correlation input of Lemma GR1:
`𝖦[⟨Ax, Bx⟩ α^{p-1} β^{p-1}] ≥ 0` for PSD `A, B` and `p ≥ 2`. -/
theorem gci_clipped (A B : Matrix ι ι ℝ) (hA : A.PosSemidef) (hB : B.PosSemidef) (p : ℕ)
    (hp : 2 ≤ p) :
    0 ≤ ∫ x, (A *ᵥ x) ⬝ᵥ (B *ᵥ x) * max (1 - x ⬝ᵥ (A *ᵥ x)) 0 ^ (p - 1) *
      max (1 - x ⬝ᵥ (B *ᵥ x)) 0 ^ (p - 1) ∂gaussPi ι := by
  have hAs : A.IsSymm := by
    have := hA.1
    rw [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
    exact this
  have hBs : B.IsSymm := by
    have := hB.1
    rw [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
    exact this
  set gradA : (ι → ℝ) → ι → ℝ := fun x =>
    (-(2 * (p : ℝ)) * max (1 - x ⬝ᵥ (A *ᵥ x)) 0 ^ (p - 1)) • (A *ᵥ x) with hgradA
  set gradB : (ι → ℝ) → ι → ℝ := fun x =>
    (-(2 * (p : ℝ)) * max (1 - x ⬝ᵥ (B *ᵥ x)) 0 ^ (p - 1)) • (B *ᵥ x) with hgradB
  set cA := ∑ i, ∑ j, |A i j|
  set cB := ∑ i, ∑ j, |B i j|
  set K : ℝ := 1 + 2 * p * (cA + cB)
  have hcA : 0 ≤ cA := by positivity
  have hcB : 0 ≤ cB := by positivity
  have hK1 : 1 ≤ K := by
    have : (0 : ℝ) ≤ 2 * p * (cA + cB) := by positivity
    simp only [K]; linarith
  have hmax_le : ∀ (M : Matrix ι ι ℝ), M.PosSemidef → ∀ (x : ι → ℝ) (k : ℕ),
      0 ≤ max (1 - x ⬝ᵥ (M *ᵥ x)) 0 ^ k ∧ max (1 - x ⬝ᵥ (M *ᵥ x)) 0 ^ k ≤ 1 := by
    intro M hM x k
    have hq := quadForm_nonneg M hM x
    have h0 : 0 ≤ max (1 - x ⬝ᵥ (M *ᵥ x)) 0 := le_max_right _ _
    exact ⟨pow_nonneg h0 k, pow_le_one₀ h0 (max_le (by linarith) zero_le_one)⟩
  have hgrad_bound : ∀ (M : Matrix ι ι ℝ), M.PosSemidef → ∀ x : ι → ℝ,
      ‖(-(2 * (p : ℝ)) * max (1 - x ⬝ᵥ (M *ᵥ x)) 0 ^ (p - 1)) • (M *ᵥ x)‖ ≤
        2 * p * (∑ i, ∑ j, |M i j|) * (1 + ‖x‖) := by
    intro M hM x
    obtain ⟨h0, h1⟩ := hmax_le M hM x (p - 1)
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * p),
      abs_of_nonneg h0]
    calc 2 * p * max (1 - x ⬝ᵥ (M *ᵥ x)) 0 ^ (p - 1) * ‖M *ᵥ x‖
        ≤ 2 * p * 1 * ((∑ i, ∑ j, |M i j|) * ‖x‖) := by
          gcongr
          exact norm_mulVec_le M x
      _ ≤ 2 * p * (∑ i, ∑ j, |M i j|) * (1 + ‖x‖) := by
          have : 0 ≤ ∑ i, ∑ j, |M i j| := by positivity
          nlinarith [norm_nonneg x]
  have hpitt := pitt_of_monotoneOn (f := gciClipPow A p) (g := gciClipPow B p) (f' := gradA)
    (g' := gradB) (hasFDerivAt_gciClipPow A hAs hp) (hasFDerivAt_gciClipPow B hBs hp)
    (by simp only [hgradA]; fun_prop) (by simp only [hgradB]; fun_prop) (K := K) (m := 1)
    (fun x => ?_) (fun x => ?_) (fun x => ?_) (fun x => ?_)
    (clipped_pair_monotoneOn A B hA hB p (by omega))
  · have heq : ∀ x, gradA x ⬝ᵥ gradB x = (4 * (p : ℝ) ^ 2) * ((A *ᵥ x) ⬝ᵥ (B *ᵥ x) *
        max (1 - x ⬝ᵥ (A *ᵥ x)) 0 ^ (p - 1) * max (1 - x ⬝ᵥ (B *ᵥ x)) 0 ^ (p - 1)) := by
      intro x
      simp only [hgradA, hgradB, smul_dotProduct, dotProduct_smul, smul_eq_mul]
      ring
    simp_rw [heq] at hpitt
    rw [integral_const_mul] at hpitt
    have h4 : (0 : ℝ) < 4 * (p : ℝ) ^ 2 := by
      have : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
      positivity
    exact (mul_nonneg_iff_of_pos_left h4).mp hpitt
  · obtain ⟨h0, h1⟩ := gciClipPow_mem_Icc A hA p x
    rw [Real.norm_eq_abs, abs_of_nonneg h0, pow_one]
    calc gciClipPow A p x ≤ 1 := h1
      _ ≤ K := hK1
      _ ≤ K * (1 + ‖x‖) := le_mul_of_one_le_right (by linarith) (by linarith [norm_nonneg x])
  · obtain ⟨h0, h1⟩ := gciClipPow_mem_Icc B hB p x
    rw [Real.norm_eq_abs, abs_of_nonneg h0, pow_one]
    calc gciClipPow B p x ≤ 1 := h1
      _ ≤ K := hK1
      _ ≤ K * (1 + ‖x‖) := le_mul_of_one_le_right (by linarith) (by linarith [norm_nonneg x])
  · rw [pow_one]
    refine (hgrad_bound A hA x).trans ?_
    have : 2 * (p : ℝ) * cA ≤ K := by
      have : (0 : ℝ) ≤ 2 * p * cB := by positivity
      simp only [K]; nlinarith
    nlinarith [norm_nonneg x]
  · rw [pow_one]
    refine (hgrad_bound B hB x).trans ?_
    have : 2 * (p : ℝ) * cB ≤ K := by
      have : (0 : ℝ) ≤ 2 * p * cA := by positivity
      simp only [K]; nlinarith
    nlinarith [norm_nonneg x]

end BiluLinial.Tight
