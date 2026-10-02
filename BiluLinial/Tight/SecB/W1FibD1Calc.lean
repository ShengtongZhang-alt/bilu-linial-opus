/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecB.W1FibReg
public import BiluLinial.Tight.SecA.EndpointPfRank2

/-!
# The endpoint derivatives of an edge fibre: generic calculus (tools for TB.W1fib-d1)

Along the affine pencil `N(t) = N₀ + (t - t₀) c E`, `E = e_i e_jᵀ + e_j e_iᵀ`:

* `wd1_hasDerivAt_inv`: `∂(N⁻¹) = -N₀⁻¹ (cE) N₀⁻¹` at `t₀` (differentiate `N(t) N(t)⁻¹ = 1`,
  which holds near `t₀`; the entries of `N(t)⁻¹` are differentiable by `entCD_inv`);
* `wd1_hasDerivAt_physInv`: for `c = τ a √(y_i y_j)`, the physical inverse
  `X_kl = √y_k (N⁻¹)_kl √y_l` has `∂X_kl = -τa (X_ki X_jl + X_kj X_il)`;
* `wd1_hasDerivAt_det`: `∂ det N = det N₀ · 2c (N₀⁻¹)_ij` (from `SecA.det_add_rank_two_pf`);
* `wd1_hasDerivAt_W`: `∂ (det N⁺ det N⁻)^p = W · 2pa (G⁺_ij - G⁻_ij)`;
* `wd1_hasDerivAt_maskF`: the product rule for `F_ji = (X_ε)_ii U_ji - (X_ε)_ji U_ii`,
  `U = X_ε diag(f) X_ν`;
* `wd1_config_deriv`: with `∂X_ε = -εa X_ε E X_ε`, `∂X_ν = -a X_ν E X_ν`, the derivative of
  `W · H · F_ji` is `W · wd1_fibD` (`wd1_fibD` is the body of `fibD` with the signing-dependent
  quantities replaced by values).
-/

@[expose] public section

namespace BiluLinial.Tight.SecB

open Matrix

section Calc

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem wd1_edgeE_mul_apply (A B : Matrix n n ℝ) (i j k l : n) :
    (A * SecA.edgeE i j * B) k l = A k i * B j l + A k j * B i l := by
  have hEB : ∀ m, (SecA.edgeE i j * B) m l =
      (Pi.single i (B j l) + Pi.single j (B i l) : n → ℝ) m := by
    intro m
    rw [← SecA.epf_edgeE_mulVec i j (fun r => B r l)]
    rfl
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  simp only [hEB, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  simp [Pi.single_apply, mul_ite, Finset.sum_ite_eq']

/-- `∂(N⁻¹) = -N₀⁻¹ (cM) N₀⁻¹` along `N(t) = N₀ + (t - t₀) c M`. -/
theorem wd1_hasDerivAt_inv {N₀ M : Matrix n n ℝ} (hdet : N₀.det ≠ 0) (c t₀ : ℝ) (k l : n) :
    HasDerivAt (fun t => (N₀ + ((t - t₀) * c) • M)⁻¹ k l) (-(N₀⁻¹ * (c • M) * N₀⁻¹) k l) t₀ := by
  let N : ℝ → Matrix n n ℝ := fun t => N₀ + ((t - t₀) * c) • M
  have hN : EntCD N t₀ := entCD_add (entCD_const _ _)
    (entCD_smul ((contDiffAt_id.sub contDiffAt_const).mul contDiffAt_const) M)
  have hN0 : N t₀ = N₀ := by simp [N]
  have hdet' : (N t₀).det ≠ 0 := by rw [hN0]; exact hdet
  have hinv := entCD_inv hN hdet'
  let D : Matrix n n ℝ := Matrix.of fun a b => deriv (fun t => (N t)⁻¹ a b) t₀
  have hD : ∀ a b, HasDerivAt (fun t => (N t)⁻¹ a b) (D a b) t₀ := fun a b =>
    ((hinv a b).differentiableAt (by norm_num)).hasDerivAt
  have hNe : ∀ a b, HasDerivAt (fun t => N t a b) ((c • M) a b) t₀ := by
    intro a b
    have h1 :=
      ((((hasDerivAt_id t₀).sub_const t₀).mul_const c).mul_const (M a b)).const_add (N₀ a b)
    have e : (fun t => N t a b) = fun t => N₀ a b + (id t - t₀) * c * M a b := by
      funext t; simp [N, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    rw [e]
    refine h1.congr_deriv ?_
    simp [Matrix.smul_apply]
  have hev : ∀ᶠ t in nhds t₀, (N t).det ≠ 0 := (cd_det hN).continuousAt.eventually_ne hdet'
  have hzero : c • M * N₀⁻¹ + N₀ * D = 0 := by
    ext a b
    have h1 : HasDerivAt (fun t => (N t * (N t)⁻¹) a b) ((c • M * N₀⁻¹ + N₀ * D) a b) t₀ := by
      simp only [Matrix.mul_apply, Matrix.add_apply]
      rw [← Finset.sum_add_distrib]
      refine HasDerivAt.fun_sum fun m _ => ?_
      have := (hNe a m).fun_mul (hD m b)
      rw [hN0] at this
      exact this
    have h2 : HasDerivAt (fun t => (N t * (N t)⁻¹) a b) 0 t₀ := by
      refine (hasDerivAt_const t₀ ((1 : Matrix n n ℝ) a b)).congr_of_eventuallyEq ?_
      filter_upwards [hev] with t ht
      rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 ht)]
    rw [h1.unique h2, Matrix.zero_apply]
  have hu : IsUnit N₀.det := isUnit_iff_ne_zero.2 hdet
  have h3 : N₀ * D = -(c • M * N₀⁻¹) := by
    rw [← sub_eq_zero, sub_neg_eq_add, add_comm]; exact hzero
  have hDeq : D = -(N₀⁻¹ * (c • M) * N₀⁻¹) := by
    calc D = N₀⁻¹ * (N₀ * D) := by
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
      _ = -(N₀⁻¹ * (c • M) * N₀⁻¹) := by rw [h3, Matrix.mul_neg, Matrix.mul_assoc]
  have := hD k l
  rw [hDeq] at this
  exact this

/-- The physical inverse `X_kl = √y_k (N⁻¹)_kl √y_l` along `N(t) = N₀ + (t - t₀) τa√(y_iy_j) E`:
`∂X_kl = -τa (X_ki X_jl + X_kj X_il)`. -/
theorem wd1_hasDerivAt_physInv (y : n → ℝ) {N₀ : Matrix n n ℝ} (hdet : N₀.det ≠ 0)
    (τ a t₀ : ℝ) (i j k l : n) :
    HasDerivAt (fun t => physInv y (N₀ + ((t - t₀) * (τ * a * (Real.sqrt (y i) *
        Real.sqrt (y j)))) • SecA.edgeE i j) k l)
      (-(τ * a) * (physInv y N₀ k i * physInv y N₀ j l + physInv y N₀ k j * physInv y N₀ i l))
      t₀ := by
  have h := ((wd1_hasDerivAt_inv (M := SecA.edgeE i j) hdet
    (τ * a * (Real.sqrt (y i) * Real.sqrt (y j))) t₀ k l).const_mul (Real.sqrt (y k))).mul_const
    (Real.sqrt (y l))
  simp only [physInv, Matrix.of_apply]
  refine h.congr_deriv ?_
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply,
    wd1_edgeE_mul_apply, smul_eq_mul]
  ring

/-- The same with a constant shift `S₀` (`X = √y (N + S₀)⁻¹ √y`). -/
theorem wd1_hasDerivAt_physInv_add (y : n → ℝ) {N₀ S₀ : Matrix n n ℝ}
    (hdet : (N₀ + S₀).det ≠ 0) (τ a t₀ : ℝ) (i j k l : n) :
    HasDerivAt (fun t => physInv y (N₀ + ((t - t₀) * (τ * a * (Real.sqrt (y i) *
        Real.sqrt (y j)))) • SecA.edgeE i j + S₀) k l)
      (-(τ * a) * (physInv y (N₀ + S₀) k i * physInv y (N₀ + S₀) j l +
        physInv y (N₀ + S₀) k j * physInv y (N₀ + S₀) i l)) t₀ := by
  have h := wd1_hasDerivAt_physInv y hdet τ a t₀ i j k l
  have e : (fun t => physInv y (N₀ + ((t - t₀) * (τ * a * (Real.sqrt (y i) *
      Real.sqrt (y j)))) • SecA.edgeE i j + S₀) k l) =
      fun t => physInv y (N₀ + S₀ + ((t - t₀) * (τ * a * (Real.sqrt (y i) *
        Real.sqrt (y j)))) • SecA.edgeE i j) k l := by
    funext t; rw [add_right_comm]
  rw [e]; exact h

theorem wd1_physInv_symm (y : n → ℝ) {N : Matrix n n ℝ} (hN : N.IsHermitian) (k l : n) :
    physInv y N k l = physInv y N l k := by
  simp only [physInv, Matrix.of_apply]
  rw [SecA.epf_inv_symm hN k l]; ring

/-- `∂ det N = det N₀ · 2c (N₀⁻¹)_ij` along `N(t) = N₀ + (t - t₀) c E` (`i ≠ j`). -/
theorem wd1_hasDerivAt_det {N₀ : Matrix n n ℝ} (hN : N₀.IsHermitian) (hdet : N₀.det ≠ 0)
    {i j : n} (hij : i ≠ j) (c t₀ : ℝ) :
    HasDerivAt (fun t => (N₀ + ((t - t₀) * c) • SecA.edgeE i j).det)
      (N₀.det * (2 * c * N₀⁻¹ i j)) t₀ := by
  have e : (fun t => (N₀ + ((t - t₀) * c) • SecA.edgeE i j).det) = fun t => N₀.det *
      (1 + 2 * ((t - t₀) * c) * N₀⁻¹ i j -
        ((t - t₀) * c) ^ 2 * (N₀⁻¹ i i * N₀⁻¹ j j - N₀⁻¹ i j ^ 2)) := by
    funext t; exact SecA.det_add_rank_two_pf hN (isUnit_iff_ne_zero.2 hdet) hij _
  rw [e]
  have hs : HasDerivAt (fun t => (t - t₀) * c) c t₀ := by
    simpa using ((hasDerivAt_id t₀).sub_const t₀).mul_const c
  have h := ((((hs.const_mul 2).mul_const (N₀⁻¹ i j)).const_add 1).sub
    ((hs.pow 2).mul_const (N₀⁻¹ i i * N₀⁻¹ j j - N₀⁻¹ i j ^ 2))).const_mul N₀.det
  refine h.congr_deriv ?_
  simp

/-- `∂ (det N⁺ det N⁻)^p = W · 2pa (G⁺_ij - G⁻_ij)` with `G^± = physInv y^± N^±₀`. -/
theorem wd1_hasDerivAt_W {A B : Matrix n n ℝ} (hA : A.PosDef) (hB : B.PosDef) {i j : n}
    (hij : i ≠ j) (p : ℕ) (a t₀ : ℝ) (yp ym : n → ℝ) :
    HasDerivAt (fun t => ((A + ((t - t₀) * (1 * a * (Real.sqrt (yp i) * Real.sqrt (yp j)))) •
        SecA.edgeE i j).det * (B + ((t - t₀) * (-1 * a * (Real.sqrt (ym i) *
          Real.sqrt (ym j)))) • SecA.edgeE i j).det) ^ p)
      ((A.det * B.det) ^ p * (2 * p * a * (physInv yp A i j - physInv ym B i j))) t₀ := by
  have hdA := wd1_hasDerivAt_det hA.isHermitian hA.det_pos.ne' hij
    (1 * a * (Real.sqrt (yp i) * Real.sqrt (yp j))) t₀
  have hdB := wd1_hasDerivAt_det hB.isHermitian hB.det_pos.ne' hij
    (-1 * a * (Real.sqrt (ym i) * Real.sqrt (ym j))) t₀
  refine ((hdA.fun_mul hdB).fun_pow p).congr_deriv ?_
  simp only [sub_self, zero_mul, zero_smul, add_zero, physInv, Matrix.of_apply]
  rcases p with _ | q
  · simp
  · rw [Nat.add_sub_cancel, pow_succ]
    push_cast
    ring

theorem wd1_U_apply (X Y : Matrix n n ℝ) (g : n → ℝ) (a b : n) :
    (X * diagonal g * Y) a b = ∑ m, X a m * g m * Y m b := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal]

theorem wd1_hasDerivAt_U {Xe Xn : ℝ → Matrix n n ℝ} {f : ℝ → n → ℝ} {t₀ : ℝ}
    {DXe DXn : Matrix n n ℝ} {Df : n → ℝ}
    (hXe : ∀ k l, HasDerivAt (fun t => Xe t k l) (DXe k l) t₀)
    (hXn : ∀ k l, HasDerivAt (fun t => Xn t k l) (DXn k l) t₀)
    (hf : ∀ k, HasDerivAt (fun t => f t k) (Df k) t₀) (a b : n) :
    HasDerivAt (fun t => (Xe t * diagonal (f t) * Xn t) a b)
      ((DXe * diagonal (f t₀) * Xn t₀ + Xe t₀ * diagonal Df * Xn t₀ +
        Xe t₀ * diagonal (f t₀) * DXn) a b) t₀ := by
  simp only [wd1_U_apply, Matrix.add_apply]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine HasDerivAt.fun_sum fun m _ => ?_
  exact (((hXe a m).fun_mul (hf m)).fun_mul (hXn m b)).congr_deriv (by ring)

/-- The product rule for the mask column `F_ji = (X_ε)_ii U_ji - (X_ε)_ji U_ii`. -/
theorem wd1_hasDerivAt_maskF {Xe Xn : ℝ → Matrix n n ℝ} {f : ℝ → n → ℝ} {t₀ : ℝ}
    {DXe DXn : Matrix n n ℝ} {Df : n → ℝ}
    (hXe : ∀ k l, HasDerivAt (fun t => Xe t k l) (DXe k l) t₀)
    (hXn : ∀ k l, HasDerivAt (fun t => Xn t k l) (DXn k l) t₀)
    (hf : ∀ k, HasDerivAt (fun t => f t k) (Df k) t₀) (j i : n) :
    HasDerivAt (fun t => maskF (Xe t) (Xn t) (f t) j i)
      (DXe i i * (Xe t₀ * diagonal (f t₀) * Xn t₀) j i +
          Xe t₀ i i * (DXe * diagonal (f t₀) * Xn t₀ + Xe t₀ * diagonal Df * Xn t₀ +
            Xe t₀ * diagonal (f t₀) * DXn) j i -
        (DXe j i * (Xe t₀ * diagonal (f t₀) * Xn t₀) i i +
          Xe t₀ j i * (DXe * diagonal (f t₀) * Xn t₀ + Xe t₀ * diagonal Df * Xn t₀ +
            Xe t₀ * diagonal (f t₀) * DXn) i i)) t₀ := by
  unfold maskF
  exact ((hXe i i).fun_mul (wd1_hasDerivAt_U hXe hXn hf j i)).fun_sub
    ((hXe j i).fun_mul (wd1_hasDerivAt_U hXe hXn hf i i))

/-- The body of `fibD` with the signing-dependent quantities replaced by values: `ℓ = ∂ log W`,
`Hv = H`, `dHv = ∂H`, `Xe = X_ε`, `Xn = X_ν`, `f`, `Df = ∂f`. -/
noncomputable def wd1_fibD (ℓ ε a Hv dHv : ℝ) (Xe Xn : Matrix n n ℝ) (f Df : n → ℝ) (i j : n) :
    ℝ :=
  (dHv * maskF Xe Xn f j i + ℓ * (Hv * maskF Xe Xn f j i)) +
    Hv * (-a * (2 * ε * Xe i j * maskF Xe Xn f j i + Xn i j * maskF Xe Xn f j i -
      Xn i i * Xe i j * (Xe * diagonal f * Xn) i j)) +
    Hv * maskF Xe Xn Df j i -
    a * (Hv * (Xe i i * Xn i i) * (Xe * diagonal f * Xn) j j)

/-- The derivative of `W · H · F_ji` along the fibre, given the derivatives of the pieces. -/
theorem wd1_config_deriv {Wf Hf : ℝ → ℝ} {Xe Xn : ℝ → Matrix n n ℝ} {f : ℝ → n → ℝ} {t₀ : ℝ}
    {Wv ℓ Hv dHv ε a : ℝ} {Xe0 Xn0 : Matrix n n ℝ} {f0 Df : n → ℝ} {i j : n}
    (hW : HasDerivAt Wf (Wv * ℓ) t₀) (hW0 : Wf t₀ = Wv)
    (hH : HasDerivAt Hf dHv t₀) (hH0 : Hf t₀ = Hv)
    (hXe : ∀ k l, HasDerivAt (fun t => Xe t k l)
      (-(ε * a) * (Xe0 k i * Xe0 j l + Xe0 k j * Xe0 i l)) t₀)
    (hXn : ∀ k l, HasDerivAt (fun t => Xn t k l)
      (-(1 * a) * (Xn0 k i * Xn0 j l + Xn0 k j * Xn0 i l)) t₀)
    (hf : ∀ k, HasDerivAt (fun t => f t k) (Df k) t₀)
    (hXe0 : Xe t₀ = Xe0) (hXn0 : Xn t₀ = Xn0) (hf0 : f t₀ = f0)
    (hse : Xe0 j i = Xe0 i j) (hsn : Xn0 j i = Xn0 i j) :
    HasDerivAt (fun t => Wf t * (Hf t * maskF (Xe t) (Xn t) (f t) j i))
      (Wv * wd1_fibD ℓ ε a Hv dHv Xe0 Xn0 f0 Df i j) t₀ := by
  subst hXe0 hXn0 hf0 hW0 hH0
  have hXe' : ∀ k l, HasDerivAt (fun t => Xe t k l)
      (((-(ε * a)) • (Xe t₀ * SecA.edgeE i j * Xe t₀)) k l) t₀ := by
    intro k l; rw [Matrix.smul_apply, wd1_edgeE_mul_apply, smul_eq_mul]; exact hXe k l
  have hXn' : ∀ k l, HasDerivAt (fun t => Xn t k l)
      (((-(1 * a)) • (Xn t₀ * SecA.edgeE i j * Xn t₀)) k l) t₀ := by
    intro k l; rw [Matrix.smul_apply, wd1_edgeE_mul_apply, smul_eq_mul]; exact hXn k l
  have hF := wd1_hasDerivAt_maskF hXe' hXn' hf j i
  refine (hW.fun_mul (hH.fun_mul hF)).congr_deriv ?_
  have hDU : (-(ε * a)) • (Xe t₀ * SecA.edgeE i j * Xe t₀) * diagonal (f t₀) * Xn t₀ +
      Xe t₀ * diagonal Df * Xn t₀ +
      Xe t₀ * diagonal (f t₀) * ((-(1 * a)) • (Xn t₀ * SecA.edgeE i j * Xn t₀)) =
      (-(ε * a)) • (Xe t₀ * SecA.edgeE i j * (Xe t₀ * diagonal (f t₀) * Xn t₀)) +
        Xe t₀ * diagonal Df * Xn t₀ +
        (-(1 * a)) • ((Xe t₀ * diagonal (f t₀) * Xn t₀) * SecA.edgeE i j * Xn t₀) := by
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
  rw [hDU]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, wd1_edgeE_mul_apply, wd1_fibD,
    maskF]
  simp only [hse, hsn]
  ring

end Calc

end BiluLinial.Tight.SecB
