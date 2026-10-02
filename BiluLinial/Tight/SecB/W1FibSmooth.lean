/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecB.W1FibSeg

/-!
# The weak loop (W1), edge fibres: entrywise smoothness (tools for TB.W1fib-smooth)

`EntCD M t₀` (every entry of the matrix family `M` is `C³` at `t₀`) and `VecCD v t₀` are closed
under sums, products, scalar multiples, `diagonal`, `mulVec`, and inversion at a point where the
determinant does not vanish (`A⁻¹ = (det A)⁻¹ • adj A`, `adj A_ab = det (A.updateRow b e_a)`);
`det` and `maskF` of such families are `C³` (`cd_det`, `cd_maskF`).
-/

@[expose] public section

namespace BiluLinial.Tight.SecB

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Every entry of `M` is `C³` at `t₀`. -/
def EntCD (M : ℝ → Matrix n n ℝ) (t₀ : ℝ) : Prop :=
  ∀ a b, ContDiffAt ℝ 3 (fun t => M t a b) t₀

/-- Every entry of `v` is `C³` at `t₀`. -/
def VecCD (v : ℝ → n → ℝ) (t₀ : ℝ) : Prop :=
  ∀ a, ContDiffAt ℝ 3 (fun t => v t a) t₀

omit [Fintype n] [DecidableEq n] in
theorem entCD_const (M : Matrix n n ℝ) (t₀ : ℝ) : EntCD (fun _ => M) t₀ :=
  fun _ _ => contDiffAt_const

omit [Fintype n] [DecidableEq n] in
theorem entCD_add {M N : ℝ → Matrix n n ℝ} {t₀ : ℝ} (hM : EntCD M t₀) (hN : EntCD N t₀) :
    EntCD (fun t => M t + N t) t₀ :=
  fun a b => (hM a b).add (hN a b)

omit [Fintype n] [DecidableEq n] in
theorem entCD_smul {c : ℝ → ℝ} {t₀ : ℝ} (hc : ContDiffAt ℝ 3 c t₀) (E : Matrix n n ℝ) :
    EntCD (fun t => c t • E) t₀ :=
  fun a b => by
    simp only [Matrix.smul_apply, smul_eq_mul]
    exact hc.mul contDiffAt_const

omit [DecidableEq n] in
theorem entCD_mul {M N : ℝ → Matrix n n ℝ} {t₀ : ℝ} (hM : EntCD M t₀) (hN : EntCD N t₀) :
    EntCD (fun t => M t * N t) t₀ :=
  fun a b => by
    simp only [Matrix.mul_apply]
    exact ContDiffAt.sum fun c _ => (hM a c).mul (hN c b)

omit [Fintype n] in
theorem entCD_diagonal {v : ℝ → n → ℝ} {t₀ : ℝ} (hv : VecCD v t₀) :
    EntCD (fun t => diagonal (v t)) t₀ :=
  fun a b => by
    by_cases hab : a = b
    · subst hab
      simp only [diagonal_apply_eq]
      exact hv a
    · simp only [diagonal_apply_ne _ hab]
      exact contDiffAt_const

omit [Fintype n] in
theorem entCD_updateRow {M : ℝ → Matrix n n ℝ} {t₀ : ℝ} (hM : EntCD M t₀) (j : n) (c : n → ℝ) :
    EntCD (fun t => (M t).updateRow j c) t₀ :=
  fun a b => by
    by_cases h : a = j
    · subst h
      simp only [updateRow_self]
      exact contDiffAt_const
    · simp only [updateRow_ne h]
      exact hM a b

theorem cd_det {M : ℝ → Matrix n n ℝ} {t₀ : ℝ} (hM : EntCD M t₀) :
    ContDiffAt ℝ 3 (fun t => (M t).det) t₀ := by
  simp_rw [det_apply']
  exact ContDiffAt.sum fun σ _ => contDiffAt_const.mul (contDiffAt_prod fun i _ => hM (σ i) i)

theorem entCD_inv {M : ℝ → Matrix n n ℝ} {t₀ : ℝ} (hM : EntCD M t₀) (hdet : (M t₀).det ≠ 0) :
    EntCD (fun t => (M t)⁻¹) t₀ :=
  fun a b => by
    simp only [inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv', adjugate_apply]
    exact ((cd_det hM).inv hdet).mul (cd_det (entCD_updateRow hM b (Pi.single a 1)))

omit [Fintype n] [DecidableEq n] in
theorem vecCD_const (v : n → ℝ) (t₀ : ℝ) : VecCD (fun _ => v) t₀ := fun _ => contDiffAt_const

omit [DecidableEq n] in
theorem vecCD_mulVec {M : ℝ → Matrix n n ℝ} {v : ℝ → n → ℝ} {t₀ : ℝ} (hM : EntCD M t₀)
    (hv : VecCD v t₀) : VecCD (fun t => M t *ᵥ v t) t₀ :=
  fun a => by
    simp only [mulVec, dotProduct]
    exact ContDiffAt.sum fun c _ => (hM a c).mul (hv c)

omit [Fintype n] [DecidableEq n] in
theorem vecCD_smul (c : ℝ) {v : ℝ → n → ℝ} {t₀ : ℝ} (hv : VecCD v t₀) :
    VecCD (fun t => c • v t) t₀ :=
  fun a => by
    simp only [Pi.smul_apply, smul_eq_mul]
    exact contDiffAt_const.mul (hv a)

theorem cd_maskF {Xe Xn : ℝ → Matrix n n ℝ} {g : ℝ → n → ℝ} {t₀ : ℝ} (he : EntCD Xe t₀)
    (hn : EntCD Xn t₀) (hg : VecCD g t₀) (j i : n) :
    ContDiffAt ℝ 3 (fun t => maskF (Xe t) (Xn t) (g t) j i) t₀ := by
  have hU := entCD_mul (entCD_mul he (entCD_diagonal hg)) hn
  unfold maskF
  exact ((he i i).mul (hU j i)).sub ((he j i).mul (hU i i))

end BiluLinial.Tight.SecB
