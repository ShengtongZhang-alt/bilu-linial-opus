/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Common.OpNorm

/-!
# Operator norm, eigenvalues and the Loewner order

Blueprint nodes `C-eigen` and `C-loewner`.

* For a real symmetric matrix, `opNorm` is the largest absolute value of an eigenvalue.
* For a real symmetric matrix `A` and `r ≥ 0`: `‖A‖ ≤ r ↔ rI - A ⪰ 0 ∧ rI + A ⪰ 0`, and for
  `r > 0`: `‖A‖ < r ↔ rI - A ≻ 0 ∧ rI + A ≻ 0`.
-/

@[expose] public section

namespace BiluLinial

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The spectral theorem for a real symmetric matrix: `A = U D Uᵀ` with `U` orthogonal and `D`
the diagonal matrix of eigenvalues. -/
theorem spectral_theorem_real {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    A = (hA.eigenvectorUnitary : Matrix n n ℝ) * diagonal hA.eigenvalues *
      star (hA.eigenvectorUnitary : Matrix n n ℝ) := by
  have h := hA.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply, RCLike.ofReal_real_eq_id, Function.id_comp] at h
  exact h

/-- `rI + sA = U diag(r + s λᵢ) Uᵀ`. -/
theorem smul_one_add_smul_eq_conj {A : Matrix n n ℝ} (hA : A.IsHermitian) (r s : ℝ) :
    r • (1 : Matrix n n ℝ) + s • A =
      (hA.eigenvectorUnitary : Matrix n n ℝ) * diagonal (fun i => r + s * hA.eigenvalues i) *
        star (hA.eigenvectorUnitary : Matrix n n ℝ) := by
  have hU : (hA.eigenvectorUnitary : Matrix n n ℝ) *
      star (hA.eigenvectorUnitary : Matrix n n ℝ) = 1 :=
    Unitary.coe_mul_star_self _
  have hdiag : diagonal (fun i => r + s * hA.eigenvalues i) =
      r • (1 : Matrix n n ℝ) + s • diagonal hA.eigenvalues := by
    ext i j
    rcases eq_or_ne i j with rfl | hij
    · simp
    · simp [hij]
  conv_lhs => rw [spectral_theorem_real hA]
  rw [hdiag]
  simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_one, hU]

theorem smul_one_add_eq_conj {A : Matrix n n ℝ} (hA : A.IsHermitian) (r : ℝ) :
    r • (1 : Matrix n n ℝ) + A =
      (hA.eigenvectorUnitary : Matrix n n ℝ) * diagonal (fun i => r + hA.eigenvalues i) *
        star (hA.eigenvectorUnitary : Matrix n n ℝ) := by
  simpa using smul_one_add_smul_eq_conj hA r 1

theorem smul_one_sub_eq_conj {A : Matrix n n ℝ} (hA : A.IsHermitian) (r : ℝ) :
    r • (1 : Matrix n n ℝ) - A =
      (hA.eigenvectorUnitary : Matrix n n ℝ) * diagonal (fun i => r - hA.eigenvalues i) *
        star (hA.eigenvectorUnitary : Matrix n n ℝ) := by
  simpa [sub_eq_add_neg] using smul_one_add_smul_eq_conj hA r (-1)

open scoped Matrix.Norms.L2Operator in
/-- The norm of a symmetric matrix is the sup norm of its vector of eigenvalues. -/
theorem opNorm_eq_norm_eigenvalues {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    opNorm A = ‖hA.eigenvalues‖ := by
  rw [opNorm_eq_l2_opNorm]
  conv_lhs => rw [spectral_theorem_real hA]
  rw [CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem hA.eigenvectorUnitary.2),
    CStarRing.norm_mem_unitary_mul _ hA.eigenvectorUnitary.2, l2_opNorm_diagonal]

/-- Every eigenvalue of a symmetric matrix is bounded in absolute value by the norm. -/
theorem abs_eigenvalue_le_opNorm {A : Matrix n n ℝ} (hA : A.IsHermitian) (i : n) :
    |hA.eigenvalues i| ≤ opNorm A := by
  rw [opNorm_eq_norm_eigenvalues hA, ← Real.norm_eq_abs]
  exact norm_le_pi_norm hA.eigenvalues i

/-- For a symmetric matrix on a nonempty index type, the norm is attained by an eigenvalue. -/
theorem exists_abs_eigenvalue_eq_opNorm [Nonempty n] {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    ∃ i, |hA.eigenvalues i| = opNorm A := by
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun j => |hA.eigenvalues j|)
    Finset.univ_nonempty
  refine ⟨i, le_antisymm (abs_eigenvalue_le_opNorm hA i) ?_⟩
  rw [opNorm_eq_norm_eigenvalues hA]
  refine (pi_norm_le_iff_of_nonneg (abs_nonneg _)).2 fun j => ?_
  rw [Real.norm_eq_abs]
  exact hi j (Finset.mem_univ j)

/-- The norm of a symmetric matrix is the largest absolute value of an eigenvalue. -/
theorem opNorm_eq_sup_abs_eigenvalues [Nonempty n] {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    opNorm A = Finset.univ.sup' Finset.univ_nonempty (fun i => |hA.eigenvalues i|) := by
  obtain ⟨i, hi⟩ := exists_abs_eigenvalue_eq_opNorm hA
  refine le_antisymm ?_ (Finset.sup'_le _ _ fun j _ => abs_eigenvalue_le_opNorm hA j)
  rw [← hi]
  exact Finset.le_sup' (fun j => |hA.eigenvalues j|) (Finset.mem_univ i)

/-- The norm of an empty matrix is `0`. -/
theorem opNorm_of_isEmpty [IsEmpty n] (A : Matrix n n ℝ) : opNorm A = 0 := by
  have hA0 : A = 0 := by
    ext i
    exact isEmptyElim i
  rw [hA0, opNorm, map_zero, norm_zero]

/-- `‖A‖ ≤ r` iff `-rI ⪯ A ⪯ rI`, for symmetric `A` and `r ≥ 0`. -/
theorem opNorm_le_iff_posSemidef {A : Matrix n n ℝ} (hA : A.IsHermitian) {r : ℝ} (hr : 0 ≤ r) :
    opNorm A ≤ r ↔ (r • (1 : Matrix n n ℝ) - A).PosSemidef ∧ (r • (1 : Matrix n n ℝ) + A).PosSemidef := by
  have hU : IsUnit (hA.eigenvectorUnitary : Matrix n n ℝ) := Unitary.isUnit_coe
  rw [smul_one_sub_eq_conj hA, smul_one_add_eq_conj hA,
    Matrix.IsUnit.posSemidef_star_right_conjugate_iff hU,
    Matrix.IsUnit.posSemidef_star_right_conjugate_iff hU,
    posSemidef_diagonal_iff, posSemidef_diagonal_iff, opNorm_eq_norm_eigenvalues hA,
    pi_norm_le_iff_of_nonneg hr, ← forall_and]
  refine forall_congr' fun i => ?_
  simp only [Real.norm_eq_abs, abs_le]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- `‖A‖ < r` iff `-rI ≺ A ≺ rI`, for symmetric `A` and `r > 0`. -/
theorem opNorm_lt_iff_posDef {A : Matrix n n ℝ} (hA : A.IsHermitian) {r : ℝ} (hr : 0 < r) :
    opNorm A < r ↔ (r • (1 : Matrix n n ℝ) - A).PosDef ∧ (r • (1 : Matrix n n ℝ) + A).PosDef := by
  have hU : IsUnit (hA.eigenvectorUnitary : Matrix n n ℝ) := Unitary.isUnit_coe
  rw [smul_one_sub_eq_conj hA, smul_one_add_eq_conj hA,
    Matrix.IsUnit.posDef_star_right_conjugate_iff hU,
    Matrix.IsUnit.posDef_star_right_conjugate_iff hU,
    posDef_diagonal_iff, posDef_diagonal_iff, opNorm_eq_norm_eigenvalues hA,
    pi_norm_lt_iff hr, ← forall_and]
  refine forall_congr' fun i => ?_
  simp only [Real.norm_eq_abs, abs_lt]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

end BiluLinial
