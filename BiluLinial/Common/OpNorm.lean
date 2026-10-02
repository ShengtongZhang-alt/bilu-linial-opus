/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.ChallengeDefs

/-!
# Basic properties of the Euclidean operator norm `opNorm`

Blueprint node `C-opnorm`. Standard facts about `BiluLinial.opNorm`, the `ℓ² → ℓ²` operator
norm of a real square matrix. `opNorm M` is definitionally Mathlib's scoped `ℓ²` operator norm
`‖M‖` (`Matrix.Norms.L2Operator`), which is a normed-ring norm.

Vectors are plain functions `n → ℝ`; their Euclidean length is `√(x ⬝ᵥ x)`.
-/

@[expose] public section

namespace BiluLinial

open Matrix

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

open scoped Matrix.Norms.L2Operator in
/-- `opNorm` is Mathlib's scoped `ℓ²` operator norm. -/
theorem opNorm_eq_l2_opNorm (M : Matrix n n ℝ) : opNorm M = ‖M‖ := rfl

theorem opNorm_nonneg (M : Matrix n n ℝ) : 0 ≤ opNorm M := by
  unfold opNorm
  exact norm_nonneg _

theorem opNorm_zero : opNorm (0 : Matrix n n ℝ) = 0 := by
  simp only [opNorm, map_zero, norm_zero]

theorem opNorm_one_le : opNorm (1 : Matrix n n ℝ) ≤ 1 := by
  unfold opNorm
  rw [map_one]
  exact ContinuousLinearMap.norm_id_le

theorem opNorm_neg (M : Matrix n n ℝ) : opNorm (-M) = opNorm M := by
  simp only [opNorm, map_neg, norm_neg]

theorem opNorm_smul (c : ℝ) (M : Matrix n n ℝ) : opNorm (c • M) = |c| * opNorm M := by
  simp only [opNorm, map_smul, norm_smul, Real.norm_eq_abs]

theorem opNorm_add_le (M N : Matrix n n ℝ) : opNorm (M + N) ≤ opNorm M + opNorm N := by
  simp only [opNorm, map_add]
  exact norm_add_le _ _

theorem opNorm_sub_le (M N : Matrix n n ℝ) : opNorm (M - N) ≤ opNorm M + opNorm N := by
  simp only [opNorm, map_sub]
  exact norm_sub_le _ _

theorem opNorm_sum_le {ι : Type*} (s : Finset ι) (M : ι → Matrix n n ℝ) :
    opNorm (∑ i ∈ s, M i) ≤ ∑ i ∈ s, opNorm (M i) := by
  simp only [opNorm, map_sum]
  exact norm_sum_le _ _

theorem opNorm_mul_le (M N : Matrix n n ℝ) : opNorm (M * N) ≤ opNorm M * opNorm N := by
  simp only [opNorm, map_mul]
  exact norm_mul_le _ _

theorem opNorm_pow_le (M : Matrix n n ℝ) (k : ℕ) : opNorm (M ^ k) ≤ opNorm M ^ k := by
  induction k with
  | zero =>
    simp only [pow_zero]
    exact opNorm_one_le
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact (opNorm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ih (opNorm_nonneg M))

open scoped Matrix.Norms.L2Operator in
theorem opNorm_transpose (M : Matrix n n ℝ) : opNorm Mᵀ = opNorm M := by
  rw [opNorm_eq_l2_opNorm, opNorm_eq_l2_opNorm, ← conjTranspose_eq_transpose_of_trivial,
    l2_opNorm_conjTranspose]

lemma norm_toEuclideanCLM_apply_le (M : Matrix n n ℝ) (x : EuclideanSpace ℝ n) :
    ‖toEuclideanCLM (n := n) (𝕜 := ℝ) M x‖ ≤ opNorm M * ‖x‖ :=
  (toEuclideanCLM (n := n) (𝕜 := ℝ) M).le_opNorm x

omit [DecidableEq n] in
lemma norm_sq_eq_dotProduct (x : EuclideanSpace ℝ n) :
    ‖x‖ ^ 2 = WithLp.ofLp x ⬝ᵥ WithLp.ofLp x := by
  rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct, star_trivial]

omit [DecidableEq n] in
lemma dotProduct_self_eq_norm_sq (x : n → ℝ) :
    x ⬝ᵥ x = ‖(WithLp.toLp 2 x : EuclideanSpace ℝ n)‖ ^ 2 :=
  (norm_sq_eq_dotProduct _).symm

omit [DecidableEq n] in
lemma dotProduct_self_nonneg' (x : n → ℝ) : 0 ≤ x ⬝ᵥ x := by
  rw [dotProduct_self_eq_norm_sq]
  positivity

omit [DecidableEq n] in
lemma sqrt_dotProduct_self (x : n → ℝ) :
    Real.sqrt (x ⬝ᵥ x) = ‖(WithLp.toLp 2 x : EuclideanSpace ℝ n)‖ := by
  rw [dotProduct_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]

/-- `‖M x‖² ≤ ‖M‖² ‖x‖²`. -/
theorem mulVec_dotProduct_self_le (M : Matrix n n ℝ) (x : n → ℝ) :
    (M *ᵥ x) ⬝ᵥ (M *ᵥ x) ≤ opNorm M ^ 2 * (x ⬝ᵥ x) := by
  have h := norm_toEuclideanCLM_apply_le M (WithLp.toLp 2 x)
  rw [dotProduct_self_eq_norm_sq (M *ᵥ x), dotProduct_self_eq_norm_sq x, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

/-- `|xᵀ M y| ≤ ‖M‖ ‖x‖ ‖y‖`. -/
theorem abs_dotProduct_mulVec_le (M : Matrix n n ℝ) (x y : n → ℝ) :
    |x ⬝ᵥ (M *ᵥ y)| ≤ opNorm M * Real.sqrt (x ⬝ᵥ x) * Real.sqrt (y ⬝ᵥ y) := by
  have hxy : x ⬝ᵥ (M *ᵥ y) = inner ℝ (WithLp.toLp 2 x : EuclideanSpace ℝ n)
      (toEuclideanCLM (n := n) (𝕜 := ℝ) M (WithLp.toLp 2 y)) :=
    (inner_toEuclideanCLM M _ _).symm
  rw [hxy, sqrt_dotProduct_self, sqrt_dotProduct_self]
  calc _ ≤ ‖(WithLp.toLp 2 x : EuclideanSpace ℝ n)‖ *
        ‖toEuclideanCLM (n := n) (𝕜 := ℝ) M (WithLp.toLp 2 y)‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖(WithLp.toLp 2 x : EuclideanSpace ℝ n)‖ *
        (opNorm M * ‖(WithLp.toLp 2 y : EuclideanSpace ℝ n)‖) :=
        mul_le_mul_of_nonneg_left (norm_toEuclideanCLM_apply_le M _) (norm_nonneg _)
    _ = _ := by ring

/-- `|xᵀ M x| ≤ ‖M‖ ‖x‖²`. -/
theorem abs_dotProduct_mulVec_self_le (M : Matrix n n ℝ) (x : n → ℝ) :
    |x ⬝ᵥ (M *ᵥ x)| ≤ opNorm M * (x ⬝ᵥ x) := by
  have h := abs_dotProduct_mulVec_le M x x
  rwa [mul_assoc, Real.mul_self_sqrt (dotProduct_self_nonneg' x)] at h

/-- Every entry is bounded by the operator norm. -/
theorem abs_apply_le_opNorm (M : Matrix n n ℝ) (i j : n) : |M i j| ≤ opNorm M := by
  have h := abs_dotProduct_mulVec_le M (Pi.single i 1) (Pi.single j 1)
  simpa [mulVec_single_one, col_apply] using h

/-- The squared Euclidean length of a column is at most `‖M‖²`. -/
theorem sum_sq_col_le (M : Matrix n n ℝ) (j : n) : ∑ i, M i j ^ 2 ≤ opNorm M ^ 2 := by
  have h := mulVec_dotProduct_self_le M (Pi.single j 1)
  have h1 : (M *ᵥ Pi.single j 1) ⬝ᵥ (M *ᵥ Pi.single j 1) = ∑ i, M i j ^ 2 := by
    simp only [mulVec_single_one, dotProduct, col_apply, sq]
  rwa [h1, dotProduct_single_one, Pi.single_eq_same, mul_one] at h

/-- The squared Euclidean length of a row is at most `‖M‖²`. -/
theorem sum_sq_row_le (M : Matrix n n ℝ) (i : n) : ∑ j, M i j ^ 2 ≤ opNorm M ^ 2 := by
  have h := sum_sq_col_le Mᵀ i
  simpa only [opNorm_transpose, transpose_apply] using h

omit [DecidableEq n] [DecidableEq m] in
/-- Extension by zero along an injective map. -/
lemma exists_extend {f : m → n} (hf : Function.Injective f) (x : m → ℝ) :
    ∃ y : n → ℝ, (∀ a, y (f a) = x a) ∧
      ∀ g : n → ℝ, ∑ i, g i * y i = ∑ a, g (f a) * x a := by
  refine ⟨Function.extend f x 0, fun a => hf.extend_apply x 0 a, fun g => ?_⟩
  calc ∑ i, g i * Function.extend f x 0 i
      = ∑ i ∈ Finset.univ.map ⟨f, hf⟩, g i * Function.extend f x 0 i := by
        refine (Finset.sum_subset (Finset.subset_univ _) fun i _ hi => ?_).symm
        have hi' : ¬ ∃ a, f a = i := by
          rintro ⟨a, rfl⟩
          exact hi (Finset.mem_map_of_mem _ (Finset.mem_univ a))
        rw [Function.extend_apply' _ _ _ hi', Pi.zero_apply, mul_zero]
    _ = ∑ a, g (f a) * Function.extend f x 0 (f a) := Finset.sum_map _ _ _
    _ = ∑ a, g (f a) * x a := by simp only [hf.extend_apply]

omit [DecidableEq n] [DecidableEq m] in
lemma sum_comp_le_sum {f : m → n} (hf : Function.Injective f) (g : n → ℝ)
    (hg : ∀ i, 0 ≤ g i) : ∑ a, g (f a) ≤ ∑ i, g i :=
  calc ∑ a, g (f a) = ∑ i ∈ Finset.univ.map ⟨f, hf⟩, g i :=
        (Finset.sum_map Finset.univ ⟨f, hf⟩ g).symm
    _ ≤ ∑ i, g i :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun i _ _ => hg i

lemma opNorm_submatrix_le_aux (M : Matrix n n ℝ) {f : m → n} (hf : Function.Injective f) :
    opNorm (M.submatrix f f) ≤ opNorm M := by
  refine (toEuclideanCLM (n := m) (𝕜 := ℝ) (M.submatrix f f)).opNorm_le_bound (opNorm_nonneg M)
    fun x => (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (opNorm_nonneg M) (norm_nonneg _))).mp ?_
  obtain ⟨y, hyf, hsum⟩ := exists_extend hf (WithLp.ofLp x)
  have hz : ∀ a, (M.submatrix f f *ᵥ WithLp.ofLp x) a = (M *ᵥ y) (f a) := fun a =>
    (hsum (M (f a))).symm
  have hy : y ⬝ᵥ y = WithLp.ofLp x ⬝ᵥ WithLp.ofLp x := by
    change ∑ i, y i * y i = ∑ a, WithLp.ofLp x a * WithLp.ofLp x a
    rw [hsum y]
    simp only [hyf]
  rw [norm_sq_eq_dotProduct, ofLp_toEuclideanCLM, mul_pow, norm_sq_eq_dotProduct, ← hy]
  calc (M.submatrix f f *ᵥ WithLp.ofLp x) ⬝ᵥ (M.submatrix f f *ᵥ WithLp.ofLp x)
      = ∑ a, (M *ᵥ y) (f a) * (M *ᵥ y) (f a) := by simp only [dotProduct, hz]
    _ ≤ (M *ᵥ y) ⬝ᵥ (M *ᵥ y) :=
      sum_comp_le_sum hf (fun i => (M *ᵥ y) i * (M *ᵥ y) i) fun i => mul_self_nonneg _
    _ ≤ opNorm M ^ 2 * (y ⬝ᵥ y) := mulVec_dotProduct_self_le M y

/-- Reindexing along an equivalence does not change the norm. -/
theorem opNorm_submatrix_equiv (M : Matrix n n ℝ) (e : m ≃ n) :
    opNorm (M.submatrix e e) = opNorm M := by
  refine le_antisymm (opNorm_submatrix_le_aux M e.injective) ?_
  have h := opNorm_submatrix_le_aux (M.submatrix e e) e.symm.injective
  rwa [submatrix_submatrix, Equiv.self_comp_symm, submatrix_id_id] at h

/-- The norm of a principal submatrix is at most the norm. -/
theorem opNorm_submatrix_le (M : Matrix n n ℝ) {f : m → n} (hf : Function.Injective f) :
    opNorm (M.submatrix f f) ≤ opNorm M :=
  opNorm_submatrix_le_aux M hf

end BiluLinial
