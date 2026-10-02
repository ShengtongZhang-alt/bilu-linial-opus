/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.Gauss.GCILaplace

/-!
# Royen's Gaussian correlation monotonicity for boxes

Nodes of the GCI subtree (`docs/tight/GCI_PLAN.md`, §3 "Royen-exp"):

* `royen_expSum_monotoneOn` (GCI-R6): for a Gaussian vector `V(s) = S(s) G` whose covariance
  `C(s)` has its off-diagonal blocks multiplied by `s`, and one-dimensional exponential sums
  `φᵢ` with `φᵢ ≥ 0`, `-φᵢ' ≥ 0` on `[0, ∞)`, the map `s ↦ 𝔼 ∏ᵢ φᵢ(Vᵢ(s)²/2)` is monotone on
  `[0, 1]`. This is Royen's computation (Latała–Matlak, arXiv:1512.08776) tested only against
  exponential sums, so no densities and no Laplace inversion are needed.
* `approxStep` and its lemmas (GCI-R5): exponential sums `0 ≤ φₖ ≤ 1` with `-φₖ' ≥ 0` and
  `φₖ(z) → 1{z ≤ t}` for every `z ≥ 0`.
* `royen_box_monotoneOn` (GCI-R7): `s ↦ P(∀ k, |(P₁ X)ₖ| ≤ cₖ ∧ ∀ k, |(P₂ Yₛ)ₖ| ≤ dₖ)` is
  monotone on `[0, 1]`, where `X` and `Yₛ = s X + √(1 - s²) Z` are standard Gaussian vectors
  with cross covariance `s I`.
-/

@[expose] public section

namespace BiluLinial.Tight

open MeasureTheory ProbabilityTheory Matrix Real Filter Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The Gaussian pair `(X, Yₛ)` -/

/-- First component `X = G ∘ inl` of `G ∈ ℝ^{ι ⊕ ι}`. -/
def gX (G : ι ⊕ ι → ℝ) : ι → ℝ := fun i => G (Sum.inl i)

/-- `Yₛ = s X + √(1 - s²) Z` with `X = G ∘ inl`, `Z = G ∘ inr`. Under `gaussPi (ι ⊕ ι)` and for
`s ∈ [-1, 1]`, `X` and `Yₛ` are standard Gaussian vectors with cross covariance `s I`. -/
noncomputable def gY (s : ℝ) (G : ι ⊕ ι → ℝ) : ι → ℝ :=
  fun i => s * G (Sum.inl i) + √(1 - s ^ 2) * G (Sum.inr i)

variable {κ₁ κ₂ : Type*} [Fintype κ₁] [Fintype κ₂] [DecidableEq κ₁] [DecidableEq κ₂]

/-- The matrix with `royenMat P₁ P₂ s *ᵥ G = (P₁ X, P₂ Yₛ)`. -/
noncomputable def royenMat (P₁ : Matrix κ₁ ι ℝ) (P₂ : Matrix κ₂ ι ℝ) (s : ℝ) :
    Matrix (κ₁ ⊕ κ₂) (ι ⊕ ι) ℝ :=
  fromBlocks P₁ 0 (s • P₂) (√(1 - s ^ 2) • P₂)

/-- Royen's covariance family: off-diagonal blocks of the covariance multiplied by `s`. -/
def royenCov (P₁ : Matrix κ₁ ι ℝ) (P₂ : Matrix κ₂ ι ℝ) (s : ℝ) :
    Matrix (κ₁ ⊕ κ₂) (κ₁ ⊕ κ₂) ℝ :=
  fromBlocks (P₁ * P₁ᵀ) (s • (P₁ * P₂ᵀ)) (s • (P₂ * P₁ᵀ)) (P₂ * P₂ᵀ)

omit [DecidableEq ι] [Fintype κ₁] [Fintype κ₂] [DecidableEq κ₁] [DecidableEq κ₂] in
theorem royenMat_mulVec_inl (P₁ : Matrix κ₁ ι ℝ) (P₂ : Matrix κ₂ ι ℝ) (s : ℝ)
    (G : ι ⊕ ι → ℝ) (k : κ₁) : (royenMat P₁ P₂ s *ᵥ G) (Sum.inl k) = (P₁ *ᵥ gX G) k := by
  simp [royenMat, gX, mulVec, dotProduct]

omit [DecidableEq ι] [Fintype κ₁] [Fintype κ₂] [DecidableEq κ₁] [DecidableEq κ₂] in
theorem royenMat_mulVec_inr (P₁ : Matrix κ₁ ι ℝ) (P₂ : Matrix κ₂ ι ℝ) (s : ℝ)
    (G : ι ⊕ ι → ℝ) (k : κ₂) : (royenMat P₁ P₂ s *ᵥ G) (Sum.inr k) = (P₂ *ᵥ gY s G) k := by
  simp only [royenMat, gY, mulVec, dotProduct, Fintype.sum_sum_type, fromBlocks_apply₂₁,
    fromBlocks_apply₂₂, Matrix.smul_apply, smul_eq_mul, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

omit [DecidableEq ι] [Fintype κ₁] [Fintype κ₂] [DecidableEq κ₁] [DecidableEq κ₂] in
theorem royenMat_mul_transpose (P₁ : Matrix κ₁ ι ℝ) (P₂ : Matrix κ₂ ι ℝ) {s : ℝ}
    (hs : s ∈ Set.Icc (-1 : ℝ) 1) :
    royenMat P₁ P₂ s * (royenMat P₁ P₂ s)ᵀ = royenCov P₁ P₂ s := by
  have h1 : √(1 - s ^ 2) * √(1 - s ^ 2) = 1 - s ^ 2 :=
    Real.mul_self_sqrt (by nlinarith [hs.1, hs.2])
  rw [royenMat, fromBlocks_transpose, fromBlocks_multiply, royenCov]
  congr 1
  · simp
  · simp [Matrix.smul_mul]
  · simp [Matrix.mul_smul, transpose_smul]
  · simp only [transpose_zero, Matrix.mul_zero, zero_add, transpose_smul, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, ← add_smul]
    rw [h1, show s * s + (1 - s ^ 2) = 1 by ring, one_smul]

omit [DecidableEq ι] in
theorem royenCov_posSemidef (P₁ : Matrix κ₁ ι ℝ) (P₂ : Matrix κ₂ ι ℝ) {s : ℝ}
    (hs : s ∈ Set.Icc (-1 : ℝ) 1) : (royenCov P₁ P₂ s).PosSemidef := by
  rw [← royenMat_mul_transpose P₁ P₂ hs]
  simpa [conjTranspose_eq_transpose_of_trivial] using
    posSemidef_self_mul_conjTranspose (royenMat P₁ P₂ s)

omit [Fintype ι] [DecidableEq ι] [Fintype κ₁] [Fintype κ₂] [DecidableEq κ₁] [DecidableEq κ₂] in
theorem royenCov_eq_sideScale (P₁ : Matrix κ₁ ι ℝ) (P₂ : Matrix κ₂ ι ℝ) (s : ℝ)
    [Fintype ι] :
    royenCov P₁ P₂ s = sideScale (royenCov P₁ P₂ 1) (fun a => a.isLeft = true) s := by
  ext (i | i) (j | j) <;> simp [royenCov, sideScale]

/-! ### One-dimensional exponential sums -/

/-- A finite exponential sum `z ↦ ∑ⱼ aⱼ e^{-λⱼ z}` with nonnegative frequencies. -/
structure ExpSum where
  /-- number of terms -/
  N : ℕ
  /-- coefficients -/
  a : Fin N → ℝ
  /-- frequencies -/
  lam : Fin N → ℝ
  lam_nonneg : ∀ j, 0 ≤ lam j

/-- `z ↦ ∑ⱼ aⱼ e^{-λⱼ z}`. -/
noncomputable def ExpSum.eval (e : ExpSum) (z : ℝ) : ℝ := ∑ j, e.a j * Real.exp (-(e.lam j * z))

/-- `z ↦ ∑ⱼ aⱼ λⱼ e^{-λⱼ z}`, i.e. minus the derivative of `e.eval`. -/
noncomputable def ExpSum.evalD (e : ExpSum) (z : ℝ) : ℝ :=
  ∑ j, e.a j * e.lam j * Real.exp (-(e.lam j * z))

/-! ### GCI-R6: Royen's monotonicity against exponential sums -/

section expSumAlgebra

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Distributivity for a product of exponential sums. -/
theorem prod_sum_mul_exp (e : κ → ExpSum) (b : (i : κ) → Fin (e i).N → ℝ) (z : κ → ℝ) :
    ∏ i, ∑ j, b i j * Real.exp (-((e i).lam j * z i)) =
      ∑ ω : (i : κ) → Fin (e i).N, (∏ i, b i (ω i)) *
        Real.exp (-(∑ i, (e i).lam (ω i) * z i)) := by
  rw [Fintype.prod_sum (fun i j => b i j * Real.exp (-((e i).lam j * z i)))]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [Finset.prod_mul_distrib, ← Real.exp_sum, ← Finset.sum_neg_distrib]

/-- `∏ᵢ φᵢ(zᵢ)` as an exponential sum in `z`. -/
theorem prod_eval_eq_sum (e : κ → ExpSum) (z : κ → ℝ) :
    ∏ i, (e i).eval (z i) = ∑ ω : (i : κ) → Fin (e i).N, (∏ i, (e i).a (ω i)) *
      Real.exp (-(∑ i, (e i).lam (ω i) * z i)) :=
  prod_sum_mul_exp e (fun i j => (e i).a j) z

/-- `∏_{i ∈ J} (-φᵢ')(zᵢ) ∏_{i ∉ J} φᵢ(zᵢ)` as an exponential sum in `z`. -/
theorem prod_evalJ_eq_sum (e : κ → ExpSum) (J : Finset κ) (z : κ → ℝ) :
    ∏ i, (if i ∈ J then (e i).evalD (z i) else (e i).eval (z i)) =
      ∑ ω : (i : κ) → Fin (e i).N, (∏ i, (e i).a (ω i)) * (∏ i ∈ J, (e i).lam (ω i)) *
        Real.exp (-(∑ i, (e i).lam (ω i) * z i)) := by
  have h : ∀ i, (if i ∈ J then (e i).evalD (z i) else (e i).eval (z i)) =
      ∑ j, ((e i).a j * if i ∈ J then (e i).lam j else 1) * Real.exp (-((e i).lam j * z i)) := by
    intro i
    by_cases hi : i ∈ J <;> simp [hi, ExpSum.eval, ExpSum.evalD]
  simp_rw [h]
  rw [prod_sum_mul_exp]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [Finset.prod_mul_distrib, Finset.prod_ite_mem, Finset.univ_inter]

end expSumAlgebra

omit [DecidableEq ι] [Fintype κ₁] [Fintype κ₂] [DecidableEq κ₁] [DecidableEq κ₂] in
theorem differentiable_royenCov_apply (P₁ : Matrix κ₁ ι ℝ) (P₂ : Matrix κ₂ ι ℝ)
    (a b : κ₁ ⊕ κ₂) : Differentiable ℝ fun s => royenCov P₁ P₂ s a b := by
  rcases a with a | a <;> rcases b with b | b <;> simp [royenCov]

/-- The determinant `D(s) = det(1 + diag(λ) C(s))`. -/
noncomputable def royenDet (P₁ : Matrix κ₁ ι ℝ) (P₂ : Matrix κ₂ ι ℝ) (m : κ₁ ⊕ κ₂ → ℝ)
    (s : ℝ) : ℝ :=
  (1 + diagonal m * royenCov P₁ P₂ s).det

omit [DecidableEq ι] in
theorem one_le_royenDet (P₁ : Matrix κ₁ ι ℝ) (P₂ : Matrix κ₂ ι ℝ) {m : κ₁ ⊕ κ₂ → ℝ}
    (hm : ∀ i, 0 ≤ m i) {s : ℝ} (hs : s ∈ Set.Icc (-1 : ℝ) 1) : 1 ≤ royenDet P₁ P₂ m s :=
  one_le_det_one_add_diagonal_mul hm (royenCov_posSemidef P₁ P₂ hs)

/-- The principal minor `s ↦ det C(s)[J, J]`. -/
noncomputable def royenMinor (P₁ : Matrix κ₁ ι ℝ) (P₂ : Matrix κ₂ ι ℝ) (J : Finset (κ₁ ⊕ κ₂))
    (s : ℝ) : ℝ :=
  ((royenCov P₁ P₂ s).submatrix (Subtype.val : J → κ₁ ⊕ κ₂) Subtype.val).det

omit [DecidableEq ι] in
theorem differentiable_royenMinor (P₁ : Matrix κ₁ ι ℝ) (P₂ : Matrix κ₂ ι ℝ)
    (J : Finset (κ₁ ⊕ κ₂)) : Differentiable ℝ (royenMinor P₁ P₂ J) :=
  differentiable_det fun a b => differentiable_royenCov_apply P₁ P₂ a b

omit [DecidableEq ι] in
/-- Royen's sign condition: `a_J(s) = -∂ₛ det C(s)[J, J] ≥ 0` on `(0, 1)`. -/
theorem deriv_royenMinor_nonpos (P₁ : Matrix κ₁ ι ℝ) (P₂ : Matrix κ₂ ι ℝ)
    (J : Finset (κ₁ ⊕ κ₂)) {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1) :
    deriv (royenMinor P₁ P₂ J) s ≤ 0 := by
  refine deriv_nonpos_of_antitoneOn ?_ hs
  have heq : royenMinor P₁ P₂ J = fun s => (sideScale ((royenCov P₁ P₂ 1).submatrix
      (Subtype.val : J → κ₁ ⊕ κ₂) Subtype.val) (fun a => (a : κ₁ ⊕ κ₂).isLeft = true) s).det := by
    funext s
    rw [royenMinor, royenCov_eq_sideScale P₁ P₂ s, sideScale_submatrix]
  rw [heq]
  exact det_sideScale_antitoneOn
    ((royenCov_posSemidef P₁ P₂ (s := 1) (by norm_num)).submatrix _) _

omit [DecidableEq ι] in
theorem royenDet_eq_sum (P₁ : Matrix κ₁ ι ℝ) (P₂ : Matrix κ₂ ι ℝ) (m : κ₁ ⊕ κ₂ → ℝ) :
    royenDet P₁ P₂ m = fun s => ∑ J : Finset (κ₁ ⊕ κ₂), (∏ i ∈ J, m i) *
      royenMinor P₁ P₂ J s := by
  funext s
  exact det_one_add_diagonal_mul m _

omit [DecidableEq ι] in
theorem hasDerivAt_royenDet (P₁ : Matrix κ₁ ι ℝ) (P₂ : Matrix κ₂ ι ℝ) (m : κ₁ ⊕ κ₂ → ℝ)
    (s : ℝ) : HasDerivAt (royenDet P₁ P₂ m)
      (∑ J : Finset (κ₁ ⊕ κ₂), (∏ i ∈ J, m i) * deriv (royenMinor P₁ P₂ J) s) s := by
  rw [royenDet_eq_sum]
  exact HasDerivAt.fun_sum fun J _ =>
    ((differentiable_royenMinor P₁ P₂ J s).hasDerivAt).const_mul _

/-- The Laplace transform of `V(s)²/2` (GCI-R1 in Royen's coordinates). -/
theorem integral_exp_royen (P₁ : Matrix κ₁ ι ℝ) (P₂ : Matrix κ₂ ι ℝ) {m : κ₁ ⊕ κ₂ → ℝ}
    (hm : ∀ i, 0 ≤ m i) {s : ℝ} (hs : s ∈ Set.Icc (-1 : ℝ) 1) :
    ∫ G, Real.exp (-(∑ i, m i * ((royenMat P₁ P₂ s *ᵥ G) i ^ 2 / 2))) ∂gaussPi (ι ⊕ ι) =
      royenDet P₁ P₂ m s ^ (-(1 / 2 : ℝ)) := by
  have h := integral_exp_neg_quadForm (royenMat P₁ P₂ s) hm
  rw [royenMat_mul_transpose P₁ P₂ hs] at h
  rw [royenDet, ← h]
  congr 1
  ext G
  congr 1
  rw [neg_div, Finset.sum_div]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The three-copy Laplace transform in Royen's coordinates (GCI-R4). -/
theorem integral_exp_royen_three (P₁ : Matrix κ₁ ι ℝ) (P₂ : Matrix κ₂ ι ℝ) {m : κ₁ ⊕ κ₂ → ℝ}
    (hm : ∀ i, 0 ≤ m i) {s : ℝ} (hs : s ∈ Set.Icc (-1 : ℝ) 1) :
    ∫ g, Real.exp (-(∑ i, m i * ((∑ l : Fin 3,
        (royenMat P₁ P₂ s *ᵥ fun j => g (l, j)) i ^ 2) / 2))) ∂gaussPi (Fin 3 × (ι ⊕ ι)) =
      royenDet P₁ P₂ m s ^ (-(3 / 2 : ℝ)) := by
  have h := integral_exp_neg_quadForm_three (royenMat P₁ P₂ s) hm
  rw [royenMat_mul_transpose P₁ P₂ hs] at h
  rw [royenDet, ← h]
  congr 1
  ext G
  congr 1
  rw [neg_div, Finset.sum_div]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The explicit form of `s ↦ 𝔼 ∏ᵢ φᵢ(Vᵢ(s)²/2)`. -/
noncomputable def royenF (P₁ : Matrix κ₁ ι ℝ) (P₂ : Matrix κ₂ ι ℝ) (e : κ₁ ⊕ κ₂ → ExpSum)
    (s : ℝ) : ℝ :=
  ∑ ω : (i : κ₁ ⊕ κ₂) → Fin (e i).N, (∏ i, (e i).a (ω i)) *
    royenDet P₁ P₂ (fun i => (e i).lam (ω i)) s ^ (-(1 / 2 : ℝ))

theorem integral_prod_eval_eq_royenF (P₁ : Matrix κ₁ ι ℝ) (P₂ : Matrix κ₂ ι ℝ)
    (e : κ₁ ⊕ κ₂ → ExpSum) {s : ℝ} (hs : s ∈ Set.Icc (-1 : ℝ) 1) :
    ∫ G, ∏ i, (e i).eval ((royenMat P₁ P₂ s *ᵥ G) i ^ 2 / 2) ∂gaussPi (ι ⊕ ι) =
      royenF P₁ P₂ e s := by
  simp_rw [prod_eval_eq_sum]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun ω _ => ?_
    rw [integral_const_mul, integral_exp_royen P₁ P₂ (fun i => (e i).lam_nonneg (ω i)) hs]
  · intro ω _
    refine Integrable.const_mul ?_ _
    refine (integrable_const (1 : ℝ)).mono' (by fun_prop) (Eventually.of_forall fun G => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff, neg_nonpos]
    exact Finset.sum_nonneg fun i _ => mul_nonneg ((e i).lam_nonneg _) (by positivity)

/-- Royen's positivity: `∑_ω c_ω λ_ω^J D_ω(s)^{-3/2} = 𝔼 ∏_{i∈J} ψᵢ(Z̃ᵢ) ∏_{i∉J} φᵢ(Z̃ᵢ) ≥ 0`. -/
theorem royen_sum_nonneg (P₁ : Matrix κ₁ ι ℝ) (P₂ : Matrix κ₂ ι ℝ) (e : κ₁ ⊕ κ₂ → ExpSum)
    (h0 : ∀ i z, 0 ≤ z → 0 ≤ (e i).eval z) (h1 : ∀ i z, 0 ≤ z → 0 ≤ (e i).evalD z)
    (J : Finset (κ₁ ⊕ κ₂)) {s : ℝ} (hs : s ∈ Set.Icc (-1 : ℝ) 1) :
    0 ≤ ∑ ω : (i : κ₁ ⊕ κ₂) → Fin (e i).N, (∏ i, (e i).a (ω i)) *
      (∏ i ∈ J, (e i).lam (ω i)) *
        royenDet P₁ P₂ (fun i => (e i).lam (ω i)) s ^ (-(3 / 2 : ℝ)) := by
  set W : (Fin 3 × (ι ⊕ ι) → ℝ) → κ₁ ⊕ κ₂ → ℝ := fun g i =>
    (∑ l : Fin 3, (royenMat P₁ P₂ s *ᵥ fun j => g (l, j)) i ^ 2) / 2 with hW
  have hW0 : ∀ g i, 0 ≤ W g i := fun g i => by positivity
  have hint : ∀ ω : (i : κ₁ ⊕ κ₂) → Fin (e i).N, Integrable (fun g =>
      Real.exp (-(∑ i, (e i).lam (ω i) * W g i))) (gaussPi (Fin 3 × (ι ⊕ ι))) := by
    intro ω
    refine (integrable_const (1 : ℝ)).mono' (by fun_prop) (Eventually.of_forall fun g => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff, neg_nonpos]
    exact Finset.sum_nonneg fun i _ => mul_nonneg ((e i).lam_nonneg _) (hW0 g i)
  have heq : ∑ ω : (i : κ₁ ⊕ κ₂) → Fin (e i).N, (∏ i, (e i).a (ω i)) *
      (∏ i ∈ J, (e i).lam (ω i)) *
        royenDet P₁ P₂ (fun i => (e i).lam (ω i)) s ^ (-(3 / 2 : ℝ)) =
      ∫ g, ∏ i, (if i ∈ J then (e i).evalD (W g i) else (e i).eval (W g i))
        ∂gaussPi (Fin 3 × (ι ⊕ ι)) := by
    simp_rw [prod_evalJ_eq_sum]
    rw [integral_finsetSum _ fun ω _ => (hint ω).const_mul _]
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [integral_const_mul,
      ← integral_exp_royen_three P₁ P₂ (fun i => (e i).lam_nonneg (ω i)) hs]
  rw [heq]
  refine integral_nonneg fun g => Finset.prod_nonneg fun i _ => ?_
  split_ifs
  · exact h1 i _ (hW0 g i)
  · exact h0 i _ (hW0 g i)

/-- **GCI-R6.** Royen's monotonicity for products of exponential sums of the squared
coordinates of `V(s) = royenMat P₁ P₂ s *ᵥ G`. -/
theorem royen_expSum_monotoneOn (P₁ : Matrix κ₁ ι ℝ) (P₂ : Matrix κ₂ ι ℝ)
    (e : κ₁ ⊕ κ₂ → ExpSum) (h0 : ∀ i z, 0 ≤ z → 0 ≤ (e i).eval z)
    (h1 : ∀ i z, 0 ≤ z → 0 ≤ (e i).evalD z) :
    MonotoneOn (fun s => ∫ G, ∏ i, (e i).eval ((royenMat P₁ P₂ s *ᵥ G) i ^ 2 / 2)
      ∂gaussPi (ι ⊕ ι)) (Set.Icc 0 1) := by
  have hIcc : ∀ s ∈ Set.Icc (0 : ℝ) 1, s ∈ Set.Icc (-1 : ℝ) 1 :=
    fun s hs => ⟨by linarith [hs.1], hs.2⟩
  have hF : MonotoneOn (royenF P₁ P₂ e) (Set.Icc 0 1) := by
    have hpos : ∀ ω : (i : κ₁ ⊕ κ₂) → Fin (e i).N, ∀ s ∈ Set.Icc (0 : ℝ) 1,
        0 < royenDet P₁ P₂ (fun i => (e i).lam (ω i)) s := fun ω s hs =>
      lt_of_lt_of_le one_pos (one_le_royenDet P₁ P₂ (fun i => (e i).lam_nonneg (ω i)) (hIcc s hs))
    have hderiv : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (royenF P₁ P₂ e)
        (∑ ω : (i : κ₁ ⊕ κ₂) → Fin (e i).N, (∏ i, (e i).a (ω i)) *
          ((∑ J : Finset (κ₁ ⊕ κ₂), (∏ i ∈ J, (e i).lam (ω i)) *
              deriv (royenMinor P₁ P₂ J) s) * (-(1 / 2 : ℝ)) *
            royenDet P₁ P₂ (fun i => (e i).lam (ω i)) s ^ (-(1 / 2 : ℝ) - 1))) s := by
      intro s hs
      unfold royenF
      refine HasDerivAt.fun_sum fun ω _ => HasDerivAt.const_mul _ ?_
      exact (hasDerivAt_royenDet P₁ P₂ _ s).rpow_const (Or.inl (hpos ω s hs).ne')
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 1) ?_ ?_ ?_
    · exact fun s hs => (hderiv s hs).continuousAt.continuousWithinAt
    · rw [interior_Icc]
      exact fun s hs => (hderiv s (Set.Ioo_subset_Icc_self hs)).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro s hs
      rw [(hderiv s (Set.Ioo_subset_Icc_self hs)).deriv]
      have hreorg : ∑ ω : (i : κ₁ ⊕ κ₂) → Fin (e i).N, (∏ i, (e i).a (ω i)) *
          ((∑ J : Finset (κ₁ ⊕ κ₂), (∏ i ∈ J, (e i).lam (ω i)) *
              deriv (royenMinor P₁ P₂ J) s) * (-(1 / 2 : ℝ)) *
            royenDet P₁ P₂ (fun i => (e i).lam (ω i)) s ^ (-(1 / 2 : ℝ) - 1)) =
          ∑ J : Finset (κ₁ ⊕ κ₂), (-deriv (royenMinor P₁ P₂ J) s / 2) *
            ∑ ω : (i : κ₁ ⊕ κ₂) → Fin (e i).N, (∏ i, (e i).a (ω i)) *
              (∏ i ∈ J, (e i).lam (ω i)) *
                royenDet P₁ P₂ (fun i => (e i).lam (ω i)) s ^ (-(3 / 2 : ℝ)) := by
        have he : (-(1 / 2 : ℝ) - 1) = -(3 / 2 : ℝ) := by norm_num
        simp_rw [he, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun J _ => Finset.sum_congr rfl fun ω _ => ?_
        ring
      rw [hreorg]
      refine Finset.sum_nonneg fun J _ => mul_nonneg ?_ ?_
      · linarith [deriv_royenMinor_nonpos P₁ P₂ J hs]
      · exact royen_sum_nonneg P₁ P₂ e h0 h1 J (hIcc s (Set.Ioo_subset_Icc_self hs))
  intro s hs t ht hst
  simp only
  rw [integral_prod_eval_eq_royenF P₁ P₂ e (hIcc s hs),
    integral_prod_eval_eq_royenF P₁ P₂ e (hIcc t ht)]
  exact hF hs ht hst

/-! ### GCI-R5: exponential-sum approximations of a step -/

/-- The number of terms parameter `b = ⌈e^{k² t + k}⌉` of `approxStep t k`. -/
noncomputable def approxStepB (t : ℝ) (k : ℕ) : ℕ := ⌈Real.exp ((k : ℝ) ^ 2 * t + k)⌉₊

/-- `φ_{t,k}(z) = 1 - (1 - e^{-k² z})^b` written as an exponential sum
`∑_{j ≤ b} aⱼ e^{-j k² z}` with `a₀ = 0`, `aⱼ = -(b choose j) (-1)^j`. -/
noncomputable def approxStep (t : ℝ) (k : ℕ) : ExpSum where
  N := approxStepB t k + 1
  a := fun j => if (j : ℕ) = 0 then 0 else -((approxStepB t k).choose j * (-1 : ℝ) ^ (j : ℕ))
  lam := fun j => (j : ℝ) * (k : ℝ) ^ 2
  lam_nonneg := fun j => by positivity

theorem approxStep_eval (t : ℝ) (k : ℕ) (z : ℝ) :
    (approxStep t k).eval z = 1 - (1 - Real.exp (-((k : ℝ) ^ 2 * z))) ^ approxStepB t k := by
  set b := approxStepB t k
  set y := Real.exp (-((k : ℝ) ^ 2 * z)) with hy
  have hexp : ∀ j : ℕ, Real.exp (-((j : ℝ) * (k : ℝ) ^ 2 * z)) = y ^ j := by
    intro j
    rw [hy, ← Real.exp_nat_mul]
    ring_nf
  unfold ExpSum.eval
  show ∑ j : Fin (b + 1), (if (j : ℕ) = 0 then (0 : ℝ) else -((b.choose j : ℝ) * (-1 : ℝ) ^ (j : ℕ))) *
      Real.exp (-(((j : ℕ) : ℝ) * (k : ℝ) ^ 2 * z)) = _
  rw [Fin.sum_univ_eq_sum_range
    (fun j => (if j = 0 then 0 else -((b.choose j : ℝ) * (-1 : ℝ) ^ j)) *
      Real.exp (-((j : ℝ) * (k : ℝ) ^ 2 * z))) (b + 1)]
  simp_rw [hexp]
  have hbin : (1 - y) ^ b = ∑ j ∈ Finset.range (b + 1), (b.choose j : ℝ) * (-1 : ℝ) ^ j * y ^ j := by
    rw [sub_eq_neg_add, add_pow]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [one_pow, mul_one, neg_pow]
    ring
  rw [hbin, Finset.sum_range_succ', Finset.sum_range_succ']
  simp

theorem hasDerivAt_exp_neg_mul (c z : ℝ) :
    HasDerivAt (fun z => Real.exp (-(c * z))) (-(c * Real.exp (-(c * z)))) z := by
  have h : HasDerivAt (fun z => -(c * z)) (-c) z := by
    simpa using (hasDerivAt_id z).const_mul (-c)
  convert h.exp using 1
  ring

theorem approxStep_evalD (t : ℝ) (k : ℕ) (z : ℝ) :
    (approxStep t k).evalD z = approxStepB t k * (k : ℝ) ^ 2 * Real.exp (-((k : ℝ) ^ 2 * z)) *
      (1 - Real.exp (-((k : ℝ) ^ 2 * z))) ^ (approxStepB t k - 1) := by
  set b := approxStepB t k
  have h1 : HasDerivAt (fun z => (approxStep t k).eval z) (-(approxStep t k).evalD z) z := by
    have : ∀ j, HasDerivAt (fun z => (approxStep t k).a j * Real.exp (-((approxStep t k).lam j * z)))
        (-((approxStep t k).a j * (approxStep t k).lam j *
          Real.exp (-((approxStep t k).lam j * z)))) z := by
      intro j
      convert (hasDerivAt_exp_neg_mul ((approxStep t k).lam j) z).const_mul
        ((approxStep t k).a j) using 1
      ring
    simp only [ExpSum.eval, ExpSum.evalD, ← Finset.sum_neg_distrib]
    exact HasDerivAt.fun_sum fun j _ => this j
  have h2 : HasDerivAt (fun z => 1 - (1 - Real.exp (-((k : ℝ) ^ 2 * z))) ^ b)
      (-(b * (1 - Real.exp (-((k : ℝ) ^ 2 * z))) ^ (b - 1) *
        ((k : ℝ) ^ 2 * Real.exp (-((k : ℝ) ^ 2 * z))))) z := by
    have hin : HasDerivAt (fun z => 1 - Real.exp (-((k : ℝ) ^ 2 * z)))
        ((k : ℝ) ^ 2 * Real.exp (-((k : ℝ) ^ 2 * z))) z := by
      convert (hasDerivAt_exp_neg_mul ((k : ℝ) ^ 2) z).const_sub 1 using 1
      ring
    have := (hin.pow b).const_sub 1
    convert this using 1
  have heq : (fun z => (approxStep t k).eval z) =
      fun z => 1 - (1 - Real.exp (-((k : ℝ) ^ 2 * z))) ^ b := funext (approxStep_eval t k)
  rw [heq] at h1
  have := h1.unique h2
  linarith

theorem approxStep_eval_mem_Icc (t : ℝ) (k : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    (approxStep t k).eval z ∈ Set.Icc (0 : ℝ) 1 := by
  rw [approxStep_eval]
  have hy1 : Real.exp (-((k : ℝ) ^ 2 * z)) ≤ 1 := Real.exp_le_one_iff.mpr (by
    have : 0 ≤ (k : ℝ) ^ 2 * z := by positivity
    linarith)
  have hy0 : 0 < Real.exp (-((k : ℝ) ^ 2 * z)) := Real.exp_pos _
  have hu0 : 0 ≤ 1 - Real.exp (-((k : ℝ) ^ 2 * z)) := by linarith
  have hu1 : 1 - Real.exp (-((k : ℝ) ^ 2 * z)) ≤ 1 := by linarith
  constructor
  · linarith [pow_le_one₀ hu0 hu1 (n := approxStepB t k)]
  · linarith [pow_nonneg hu0 (approxStepB t k)]

theorem approxStep_evalD_nonneg (t : ℝ) (k : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    0 ≤ (approxStep t k).evalD z := by
  rw [approxStep_evalD]
  have hy1 : Real.exp (-((k : ℝ) ^ 2 * z)) ≤ 1 := Real.exp_le_one_iff.mpr (by
    have : 0 ≤ (k : ℝ) ^ 2 * z := by positivity
    linarith)
  have hu0 : 0 ≤ 1 - Real.exp (-((k : ℝ) ^ 2 * z)) := by linarith
  positivity

/-- `φ_{t,k}(z) → 1{z ≤ t}` for every `z ≥ 0`. -/
theorem tendsto_approxStep_eval {t : ℝ} (ht : 0 ≤ t) {z : ℝ} (hz : 0 ≤ z) :
    Tendsto (fun k : ℕ => (approxStep t k).eval z) atTop
      (𝓝 (Set.indicator (Set.Iic t) (fun _ => (1 : ℝ)) z)) := by
  have hb : ∀ k : ℕ, Real.exp ((k : ℝ) ^ 2 * t + k) ≤ approxStepB t k :=
    fun k => Nat.le_ceil _
  have hb' : ∀ k : ℕ, (approxStepB t k : ℝ) ≤ Real.exp ((k : ℝ) ^ 2 * t + k) + 1 :=
    fun k => (Nat.ceil_lt_add_one (Real.exp_pos _).le).le
  by_cases hzt : z ≤ t
  · rw [Set.indicator_of_mem (Set.mem_Iic.mpr hzt)]
    -- `(1 - y)^b ≤ exp(-b y) ≤ exp(-e^k)`
    have hbound : ∀ k : ℕ, (1 - Real.exp (-((k : ℝ) ^ 2 * z))) ^ approxStepB t k ≤
        Real.exp (-Real.exp k) := by
      intro k
      set y := Real.exp (-((k : ℝ) ^ 2 * z)) with hy
      have hy0 : 0 ≤ y := (Real.exp_pos _).le
      have hy1 : y ≤ 1 := Real.exp_le_one_iff.mpr (by
        have : 0 ≤ (k : ℝ) ^ 2 * z := by positivity
        linarith)
      have h1 : (1 - y) ^ approxStepB t k ≤ Real.exp (-y) ^ approxStepB t k :=
        pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (-y)]) _
      rw [← Real.exp_nat_mul] at h1
      refine h1.trans (Real.exp_le_exp.mpr ?_)
      have h2 : Real.exp k ≤ approxStepB t k * y := by
        calc Real.exp k = Real.exp ((k : ℝ) ^ 2 * t + k) * y * Real.exp ((k : ℝ) ^ 2 * (z - t)) := by
              rw [hy, mul_assoc, ← Real.exp_add, ← Real.exp_add]; ring_nf
          _ ≤ Real.exp ((k : ℝ) ^ 2 * t + k) * y * 1 := by
              gcongr
              exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos (by positivity)
                (by linarith))
          _ ≤ approxStepB t k * y := by rw [mul_one]; gcongr; exact hb k
      linarith
    have hlim0 : Tendsto (fun k : ℕ => Real.exp (-Real.exp k)) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (Real.tendsto_exp_atTop.comp tendsto_natCast_atTop_atTop)
    have hsq : Tendsto (fun k : ℕ => (1 - Real.exp (-((k : ℝ) ^ 2 * z))) ^ approxStepB t k)
        atTop (𝓝 0) := by
      refine squeeze_zero (fun k => ?_) hbound hlim0
      have : Real.exp (-((k : ℝ) ^ 2 * z)) ≤ 1 := Real.exp_le_one_iff.mpr (by
        have : 0 ≤ (k : ℝ) ^ 2 * z := by positivity
        linarith)
      exact pow_nonneg (by linarith) _
    simp_rw [approxStep_eval]
    simpa using hsq.const_sub 1
  · rw [Set.indicator_of_notMem (by simpa using hzt)]
    push Not at hzt
    -- `0 ≤ 1 - (1 - y)^b ≤ b y ≤ e^{-(k²(z - t) - k)} + e^{-k² z}`
    have hbound : ∀ k : ℕ, (approxStep t k).eval z ≤
        Real.exp (-((k : ℝ) ^ 2 * (z - t) - k)) + Real.exp (-((k : ℝ) ^ 2 * z)) := by
      intro k
      rw [approxStep_eval]
      set y := Real.exp (-((k : ℝ) ^ 2 * z)) with hy
      have hy0 : 0 ≤ y := (Real.exp_pos _).le
      have hy1 : y ≤ 1 := Real.exp_le_one_iff.mpr (by
        have : 0 ≤ (k : ℝ) ^ 2 * z := by positivity
        linarith)
      have hbern : 1 - approxStepB t k * y ≤ (1 - y) ^ approxStepB t k := by
        have := one_add_mul_le_pow (a := -y) (by linarith) (approxStepB t k)
        simpa [sub_eq_add_neg, mul_neg] using this
      have h2 : approxStepB t k * y ≤
          Real.exp (-((k : ℝ) ^ 2 * (z - t) - k)) + y := by
        calc approxStepB t k * y ≤ (Real.exp ((k : ℝ) ^ 2 * t + k) + 1) * y := by
              gcongr; exact hb' k
          _ = Real.exp (-((k : ℝ) ^ 2 * (z - t) - k)) + y := by
              rw [add_mul, one_mul, hy, ← Real.exp_add]; ring_nf
      linarith
    have hlim1 : Tendsto (fun k : ℕ => Real.exp (-((k : ℝ) ^ 2 * (z - t) - k))) atTop (𝓝 0) := by
      refine Real.tendsto_exp_neg_atTop_nhds_zero.comp ?_
      have hzt' : 0 < z - t := by linarith
      refine tendsto_atTop_mono' atTop ?_ tendsto_natCast_atTop_atTop
      filter_upwards [eventually_ge_atTop ⌈2 / (z - t)⌉₊] with k hk
      have hk' : 2 / (z - t) ≤ (k : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hk)
      have : 2 ≤ (k : ℝ) * (z - t) := by
        rwa [div_le_iff₀ hzt'] at hk'
      nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    have hlim2 : Tendsto (fun k : ℕ => Real.exp (-((k : ℝ) ^ 2 * z))) atTop (𝓝 0) := by
      refine Real.tendsto_exp_neg_atTop_nhds_zero.comp ?_
      have hz' : 0 < z := by linarith
      refine tendsto_atTop_mono' atTop ?_ tendsto_natCast_atTop_atTop
      filter_upwards [eventually_ge_atTop ⌈1 / z⌉₊] with k hk
      have hk' : 1 / z ≤ (k : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hk)
      have : 1 ≤ (k : ℝ) * z := by rwa [div_le_iff₀ hz'] at hk'
      nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    refine squeeze_zero (fun k => (approxStep_eval_mem_Icc t k hz).1) hbound ?_
    simpa using hlim1.add hlim2

/-! ### GCI-R7: Royen's monotonicity for boxes -/

/-- **GCI-R7** (Royen). For standard Gaussian vectors `X`, `Yₛ` with cross covariance `s I`, the
probability of a pair of slab intersections `P(∀ k, |(P₁ X)ₖ| ≤ cₖ ∧ ∀ k, |(P₂ Yₛ)ₖ| ≤ dₖ)` is
monotone in `s ∈ [0, 1]`. -/
theorem royen_box_monotoneOn (P₁ : Matrix κ₁ ι ℝ) (P₂ : Matrix κ₂ ι ℝ) (c : κ₁ → ℝ)
    (d : κ₂ → ℝ) :
    MonotoneOn (fun s => (gaussPi (ι ⊕ ι)).real
      {G | (∀ k, |(P₁ *ᵥ gX G) k| ≤ c k) ∧ ∀ k, |(P₂ *ᵥ gY s G) k| ≤ d k}) (Set.Icc 0 1) := by
  by_cases hneg : (∃ k, c k < 0) ∨ (∃ k, d k < 0)
  · have hempty : ∀ s : ℝ,
        {G : ι ⊕ ι → ℝ | (∀ k, |(P₁ *ᵥ gX G) k| ≤ c k) ∧ ∀ k, |(P₂ *ᵥ gY s G) k| ≤ d k} = ∅ := by
      intro s
      ext G
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
      rcases hneg with ⟨k, hk⟩ | ⟨k, hk⟩
      · intro h1 _
        linarith [h1 k, abs_nonneg ((P₁ *ᵥ gX G) k)]
      · intro _ h2
        linarith [h2 k, abs_nonneg ((P₂ *ᵥ gY s G) k)]
    intro s _ t _ _
    simp only [hempty, measureReal_empty, le_refl]
  push Not at hneg
  obtain ⟨hc, hd⟩ := hneg
  set thr : κ₁ ⊕ κ₂ → ℝ := Sum.elim (fun k => c k ^ 2 / 2) (fun k => d k ^ 2 / 2) with hthrdef
  have hthr : ∀ i, 0 ≤ thr i := by
    rintro (k | k) <;> simp only [thr, Sum.elim_inl, Sum.elim_inr] <;> positivity
  have key : ∀ v w : ℝ, 0 ≤ w → (|v| ≤ w ↔ v ^ 2 / 2 ≤ w ^ 2 / 2) := by
    intro v w hw
    rw [div_le_div_iff_of_pos_right two_pos, ← sq_abs v]
    exact (sq_le_sq₀ (abs_nonneg v) hw).symm
  have hset : ∀ s : ℝ,
      {G : ι ⊕ ι → ℝ | (∀ k, |(P₁ *ᵥ gX G) k| ≤ c k) ∧ ∀ k, |(P₂ *ᵥ gY s G) k| ≤ d k} =
        {G | ∀ i, (royenMat P₁ P₂ s *ᵥ G) i ^ 2 / 2 ≤ thr i} := by
    intro s
    ext G
    simp only [Set.mem_setOf_eq, Sum.forall, royenMat_mulVec_inl, royenMat_mulVec_inr, thr,
      Sum.elim_inl, Sum.elim_inr, key _ _ (hc _), key _ _ (hd _)]
  have hmeas : ∀ s : ℝ, MeasurableSet {G : ι ⊕ ι → ℝ | ∀ i, (royenMat P₁ P₂ s *ᵥ G) i ^ 2 / 2 ≤ thr i} := by
    intro s
    rw [Set.setOf_forall]
    exact MeasurableSet.iInter fun i => measurableSet_le (by fun_prop) measurable_const
  have hcont : ∀ (t' : ℝ) (k : ℕ), Continuous fun z => (approxStep t' k).eval z := by
    intro t' k
    unfold ExpSum.eval
    fun_prop
  set F : ℕ → ℝ → ℝ := fun k s => ∫ G, ∏ i, (approxStep (thr i) k).eval
    ((royenMat P₁ P₂ s *ᵥ G) i ^ 2 / 2) ∂gaussPi (ι ⊕ ι) with hFdef
  have hFmono : ∀ k, MonotoneOn (F k) (Set.Icc 0 1) := fun k =>
    royen_expSum_monotoneOn P₁ P₂ (fun i => approxStep (thr i) k)
      (fun i z hz => (approxStep_eval_mem_Icc _ k hz).1) (fun i z hz => approxStep_evalD_nonneg _ k hz)
  have hFlim : ∀ s : ℝ, Tendsto (fun k => F k s) atTop
      (𝓝 ((gaussPi (ι ⊕ ι)).real {G | ∀ i, (royenMat P₁ P₂ s *ᵥ G) i ^ 2 / 2 ≤ thr i})) := by
    intro s
    have hind : ∀ G : ι ⊕ ι → ℝ, Tendsto (fun k => ∏ i, (approxStep (thr i) k).eval
        ((royenMat P₁ P₂ s *ᵥ G) i ^ 2 / 2)) atTop
        (𝓝 (Set.indicator {G | ∀ i, (royenMat P₁ P₂ s *ᵥ G) i ^ 2 / 2 ≤ thr i} 1 G)) := by
      intro G
      have hlim := tendsto_finset_prod Finset.univ fun i _ =>
        tendsto_approxStep_eval (hthr i) (by positivity : 0 ≤ (royenMat P₁ P₂ s *ᵥ G) i ^ 2 / 2)
      convert hlim using 2
      by_cases hG : ∀ i, (royenMat P₁ P₂ s *ᵥ G) i ^ 2 / 2 ≤ thr i
      · rw [Set.indicator_of_mem (by exact hG)]
        symm
        exact Finset.prod_eq_one fun i _ => Set.indicator_of_mem (Set.mem_Iic.mpr (hG i)) _
      · rw [Set.indicator_of_notMem (by exact hG)]
        push Not at hG
        obtain ⟨i, hi⟩ := hG
        symm
        exact Finset.prod_eq_zero (Finset.mem_univ i)
          (Set.indicator_of_notMem (by simpa using hi) _)
    rw [← integral_indicator_one (hmeas s)]
    refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) (fun k => ?_)
      (integrable_const 1) (fun k => Eventually.of_forall fun G => ?_)
      (Eventually.of_forall hind)
    · exact (Continuous.aestronglyMeasurable (by
        refine continuous_finset_prod _ fun i _ => (hcont _ k).comp ?_
        fun_prop))
    · rw [Real.norm_eq_abs, abs_of_nonneg (Finset.prod_nonneg fun i _ =>
        (approxStep_eval_mem_Icc _ k (by positivity)).1)]
      exact Finset.prod_le_one₀ (fun i _ => (approxStep_eval_mem_Icc _ k (by positivity)).1)
        (fun i _ => (approxStep_eval_mem_Icc _ k (by positivity)).2)
  intro s hs t ht hst
  simp only [hset s, hset t]
  exact le_of_tendsto_of_tendsto (hFlim s) (hFlim t)
    (Eventually.of_forall fun k => hFmono k hs ht hst)

end BiluLinial.Tight
