/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecA.Conc
public import BiluLinial.Tight.SecC.ShiftMat

/-!
# Shifted resolvents at a supported signing: the deterministic facts (C5)

The graph-generic part of `SecA/Shift.lean` (nodes `A-C5a` … `A-C5g` and their helpers, the
helpers of `A-TT`), split off so that the transfer of (C4) can be developed without importing the
graph-level nodes. See `SecA/Shift.lean` for the node list.
-/

@[expose] public section

namespace BiluLinial.Tight

open Matrix

namespace SecA

section C5

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- `(A + D)⁻¹_ii ≤ A⁻¹_ii` for `A ≻ 0`, `D ⪰ 0` (`A⁻¹ - (A+D)⁻¹ = B⁻¹(D + DA⁻¹D)B⁻¹`). -/
theorem inv_diag_add_le' {n : Type*} [Fintype n] [DecidableEq n] {A D : Matrix n n ℝ}
    (hA : A.PosDef) (hD : D.PosSemidef) (i : n) : (A + D)⁻¹ i i ≤ A⁻¹ i i := by
  have hB : (A + D).PosDef := hA.add_posSemidef hD
  have hAu : IsUnit A.det := isUnit_iff_ne_zero.mpr hA.det_pos.ne'
  have hBu : IsUnit (A + D).det := isUnit_iff_ne_zero.mpr hB.det_pos.ne'
  set B := A + D with hBdef
  set M := D + D * A⁻¹ * D with hMdef
  have hDh : Dᴴ = D := hD.1
  have hM : M.PosSemidef := by
    refine hD.add ?_
    have := hA.inv.posSemidef.conjTranspose_mul_mul_same D
    rwa [hDh] at this
  have hBinvh : (B⁻¹)ᴴ = B⁻¹ := hB.inv.1
  have hkey : A⁻¹ - B⁻¹ = B⁻¹ * M * B⁻¹ := by
    have e1 : M = D * A⁻¹ * B := by
      rw [hMdef, hBdef, Matrix.mul_add, Matrix.mul_assoc D A⁻¹ A, Matrix.nonsing_inv_mul A hAu,
        Matrix.mul_one, Matrix.mul_assoc]
    have e2 : A⁻¹ - B⁻¹ = B⁻¹ * D * A⁻¹ := by
      have h1 : A⁻¹ = B⁻¹ * B * A⁻¹ := by rw [Matrix.nonsing_inv_mul B hBu, Matrix.one_mul]
      have h2 : B⁻¹ = B⁻¹ * A * A⁻¹ := by
        rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv A hAu, Matrix.mul_one]
      calc A⁻¹ - B⁻¹ = B⁻¹ * B * A⁻¹ - B⁻¹ * A * A⁻¹ := by rw [← h1, ← h2]
        _ = B⁻¹ * (B - A) * A⁻¹ := by rw [Matrix.mul_sub, Matrix.sub_mul]
        _ = B⁻¹ * D * A⁻¹ := by rw [hBdef, add_sub_cancel_left]
    rw [e2, e1, Matrix.mul_assoc B⁻¹ (D * A⁻¹ * B) B⁻¹, Matrix.mul_assoc (D * A⁻¹) B B⁻¹,
      Matrix.mul_nonsing_inv B hBu, Matrix.mul_one, Matrix.mul_assoc]
  have hP : (B⁻¹ * M * B⁻¹).PosSemidef := by
    have := hM.conjTranspose_mul_mul_same B⁻¹
    rwa [hBinvh] at this
  have h0 : 0 ≤ (B⁻¹ * M * B⁻¹) i i := hP.diag_nonneg
  rw [← hkey] at h0
  simpa [Matrix.sub_apply] using h0

omit [Fintype V] in
theorem srcDiag_smul_posSemidef {z : ℝ} (hz : 0 ≤ z) {y : V → ℝ} (hy : ∀ i, 0 ≤ y i)
    (S : Finset V) : (z • srcDiag y S).PosSemidef := by
  refine Matrix.PosSemidef.smul ?_ hz
  refine Matrix.PosSemidef.diagonal fun k => ?_
  split_ifs
  · exact hy k
  · exact le_rfl

/-- `A-C5a`: the shifted normalized diagonal is positive. -/
theorem hzN_pos {a τ z : ℝ} (hz : 0 ≤ z) {y : V → ℝ} (hy : ∀ i, 0 ≤ y i) {σ : Config V}
    {S : Finset V} (hP : (precN G a τ y σ S).PosDef) (i : V) : 0 < hzN G a τ z y σ S i := by
  have hQ := hP.add_posSemidef (srcDiag_smul_posSemidef hz hy S)
  exact hQ.inv.diag_pos

/-- `A-C5a`: the shift decreases the normalized diagonal. -/
theorem hzN_le_hN {a τ z : ℝ} (hz : 0 ≤ z) {y : V → ℝ} (hy : ∀ i, 0 ≤ y i) {σ : Config V}
    {S : Finset V} (hP : (precN G a τ y σ S).PosDef) (i : V) :
    hzN G a τ z y σ S i ≤ hN G a τ y σ S i :=
  inv_diag_add_le' hP (srcDiag_smul_posSemidef hz hy S) i

/-! #### Helpers: the shifted core on `N` -/

/-- `C_z[N,N] = Rᴴ (P̃_core + z Y_{S-v})⁻¹ R` (`R = SecC.compR`). -/
theorem shiftY_eq_conj (a τ z : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) (v : V) :
    shiftY G a τ z y σ S v = (SecC.compR G y S v)ᴴ *
      (precCore G a τ y σ S v + z • srcDiag y (S.erase v))⁻¹ * SecC.compR G y S v := by
  ext i j
  rw [SecC.compR_conj_apply]
  rfl

/-- `C[N,N] = Rᴴ P̃_core⁻¹ R`, entrywise. -/
theorem conj_core_apply (a τ : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) (v : V)
    (i j : nbhd G S v) :
    ((SecC.compR G y S v)ᴴ * (precCore G a τ y σ S v)⁻¹ * SecC.compR G y S v) i j =
      coreGreen G a τ y σ S v i j := by
  rw [SecC.compR_conj_apply]
  rfl

theorem rootMzG_eq_smul (a τ z : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) (v : V) :
    rootMzG G a τ z y σ S v =
      (a ^ 2 * y v / diagD G a y S v) • shiftY G a τ z y σ S v := by
  ext i j
  simp only [rootMzG, shiftY, Matrix.smul_apply, of_apply, smul_eq_mul]

/-- `‖C_z[N,N]‖ ≤ 1/z`, i.e. `C_z[N,N] ⪯ z⁻¹ I` (`z > 0`, good core). -/
theorem shiftY_le {a τ z : ℝ} (hz : 0 < z) {y : V → ℝ} (hy : ∀ i, 0 ≤ y i) {σ : Config V}
    {S : Finset V} {v : V} (hM : (precCore G a τ y σ S v).PosDef) :
    (z⁻¹ • (1 : Matrix (nbhd G S v) (nbhd G S v) ℝ) -
      shiftY G a τ z y σ S v).PosSemidef := by
  have hdv0 : ∀ k, 0 ≤ (if k ∈ S.erase v then y k else 0) := fun k => by
    split_ifs
    · exact hy k
    · exact le_rfl
  have hsrc : srcDiag y (S.erase v) = diagonal fun k => if k ∈ S.erase v then y k else 0 := rfl
  have hQ : (precCore G a τ y σ S v + z • diagonal fun k => if k ∈ S.erase v then y k else 0).PosDef :=
    hM.add_posSemidef ((PosSemidef.diagonal hdv0).smul hz.le)
  have hherm : (z⁻¹ • (1 : Matrix (nbhd G S v) (nbhd G S v) ℝ) -
      shiftY G a τ z y σ S v).IsHermitian := by
    refine (isHermitian_one.smul (IsSelfAdjoint.all _)).sub ?_
    rw [shiftY_eq_conj, hsrc]
    exact isHermitian_conjTranspose_mul_mul _ hQ.inv.isHermitian
  refine PosSemidef.of_dotProduct_mulVec_nonneg hherm fun x => ?_
  rw [star_trivial, sub_mulVec, dotProduct_sub, smul_mulVec, one_mulVec, dotProduct_smul,
    smul_eq_mul, shiftY_eq_conj, SecC.quad_conj, hsrc]
  have hg : ∀ k t, 2 * (SecC.compR G y S v *ᵥ x) k * t -
      z * (if k ∈ S.erase v then y k else 0) * t ^ 2 ≤
        (if h : k ∈ nbhd G S v then x ⟨k, h⟩ ^ 2 / z else 0) := by
    intro k t
    by_cases hk : k ∈ nbhd G S v
    · have hkS : k ∈ S.erase v := by
        have h' := Finset.mem_filter.1 hk
        exact Finset.mem_erase.2 ⟨(G.ne_of_adj h'.2).symm, h'.1⟩
      have hw : (SecC.compR G y S v *ᵥ x) k = Real.sqrt (y k) * x ⟨k, hk⟩ :=
        SecC.compR_mulVec_coe G y S v x ⟨k, hk⟩
      rw [hw, dite_eq_left hk, ite_eq_left hkS, le_div_iff₀ hz]
      have h1 : 0 ≤ x ⟨k, hk⟩ ^ 2 - 2 * z * Real.sqrt (y k) * x ⟨k, hk⟩ * t +
          z ^ 2 * y k * t ^ 2 := by
        have h2 := sq_nonneg (x ⟨k, hk⟩ - z * Real.sqrt (y k) * t)
        have e : (x ⟨k, hk⟩ - z * Real.sqrt (y k) * t) ^ 2 = x ⟨k, hk⟩ ^ 2 -
            2 * z * Real.sqrt (y k) * x ⟨k, hk⟩ * t + z ^ 2 * Real.sqrt (y k) ^ 2 * t ^ 2 := by
          ring
        rwa [e, Real.sq_sqrt (hy k)] at h2
      nlinarith [h1]
    · rw [SecC.compR_mulVec_of_not G y S v x hk, dite_eq_right hk]
      nlinarith [mul_nonneg (mul_nonneg hz.le (hdv0 k)) (sq_nonneg t)]
  have hb := SecC.inv_quad_le_of_diag hM.posSemidef hQ _ _ hg
  have h0 : ∀ k ∈ (Finset.univ : Finset V), k ∉ nbhd G S v →
      (if h : k ∈ nbhd G S v then x ⟨k, h⟩ ^ 2 / z else 0) = 0 := fun k _ hk => dite_eq_right hk
  have hsum : ∑ k, (if h : k ∈ nbhd G S v then x ⟨k, h⟩ ^ 2 / z else 0) = z⁻¹ * (x ⬝ᵥ x) := by
    rw [← Finset.sum_subset (Finset.subset_univ _) h0, ← Finset.sum_coe_sort (nbhd G S v),
      dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [dite_eq_left i.2]
    simp only [Subtype.coe_eta]
    ring
  linarith

/-- `C[N,N] - C_z[N,N] ⪰ 0` (`z ≥ 0`, good core). -/
theorem core_sub_shiftY_posSemidef {a τ z : ℝ} (hz : 0 ≤ z) {y : V → ℝ} (hy : ∀ i, 0 ≤ y i)
    {σ : Config V} {S : Finset V} {v : V} (hM : (precCore G a τ y σ S v).PosDef) :
    ((SecC.compR G y S v)ᴴ * (precCore G a τ y σ S v)⁻¹ * SecC.compR G y S v -
      shiftY G a τ z y σ S v).PosSemidef := by
  have hD := srcDiag_smul_posSemidef hz hy (S.erase v)
  have hQ : (precCore G a τ y σ S v + z • srcDiag y (S.erase v)).PosDef := hM.add_posSemidef hD
  have hdiff : ((precCore G a τ y σ S v)⁻¹ -
      (precCore G a τ y σ S v + z • srcDiag y (S.erase v))⁻¹).PosSemidef := by
    refine PosSemidef.of_dotProduct_mulVec_nonneg (hM.inv.isHermitian.sub hQ.inv.isHermitian)
      fun x => ?_
    have hQP : (precCore G a τ y σ S v + z • srcDiag y (S.erase v) -
        precCore G a τ y σ S v).PosSemidef := by
      rwa [add_sub_cancel_left]
    have := SecC.inv_quad_antitone hM hQ hQP x
    rw [star_trivial, sub_mulVec, dotProduct_sub]
    linarith
  rw [shiftY_eq_conj, ← Matrix.sub_mul, ← Matrix.mul_sub]
  exact hdiff.conjTranspose_mul_mul_same _

/-- `z Σ_{k ∈ N} (C_z)_ik² ≤ C_ii - (C_z)_ii` (from `C - C_z ⪰ z C_z Y C_z`, `z ≥ 0`). -/
theorem sum_coreShift_sq_le {a τ z : ℝ} (hz : 0 ≤ z) {y : V → ℝ} (hy : ∀ i, 0 ≤ y i)
    {σ : Config V} {S : Finset V} {v : V} (hM : (precCore G a τ y σ S v).PosDef) (i : V) :
    z * ∑ k ∈ nbhd G S v, coreShift G a τ z y σ S v i k ^ 2 ≤
      coreGreen G a τ y σ S v i i - coreShift G a τ z y σ S v i i := by
  have hQ : (precCore G a τ y σ S v + z • srcDiag y (S.erase v)).PosDef :=
    hM.add_posSemidef (srcDiag_smul_posSemidef hz hy _)
  have hkey := quad_inv_sub_inv_add_ge hM (srcDiag_posSemidef hy (S.erase v)) hz
    (Pi.single i 1)
  obtain ⟨Kq, hKq⟩ : ∃ Kq, Kq = (precCore G a τ y σ S v + z • srcDiag y (S.erase v))⁻¹ :=
    ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K, K = (precCore G a τ y σ S v)⁻¹ := ⟨_, rfl⟩
  rw [← hKq, ← hK] at hkey
  have hKqs : ∀ k l, Kq k l = Kq l k := fun k l => by
    rw [hKq]
    simpa using hQ.inv.isHermitian.apply l k
  simp only [mulVec_single_one, col_apply', single_one_dotProduct] at hkey
  have hdot : (fun j => Kq j i) ⬝ᵥ (srcDiag y (S.erase v) *ᵥ fun j => Kq j i) =
      ∑ k, (if k ∈ S.erase v then y k else 0) * Kq k i ^ 2 := by
    simp only [srcDiag, mulVec_diagonal, dotProduct]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hdot] at hkey
  have hsub : ∑ k ∈ nbhd G S v, y k * Kq k i ^ 2 ≤
      ∑ k, (if k ∈ S.erase v then y k else 0) * Kq k i ^ 2 := by
    calc ∑ k ∈ nbhd G S v, y k * Kq k i ^ 2 =
          ∑ k ∈ nbhd G S v, (if k ∈ S.erase v then y k else 0) * Kq k i ^ 2 := by
          refine Finset.sum_congr rfl fun k hk => ?_
          have hkS : k ∈ S.erase v := by
            have h' := Finset.mem_filter.1 hk
            exact Finset.mem_erase.2 ⟨(G.ne_of_adj h'.2).symm, h'.1⟩
          rw [ite_eq_left hkS]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun k _ _ =>
          mul_nonneg (by split_ifs; exacts [hy k, le_rfl]) (sq_nonneg _)
  have hfin : z * ∑ k ∈ nbhd G S v, y k * Kq k i ^ 2 ≤ K i i - Kq i i :=
    (mul_le_mul_of_nonneg_left hsub hz).trans hkey
  have hcs : ∀ k, coreShift G a τ z y σ S v i k ^ 2 = y i * (y k * Kq k i ^ 2) := by
    intro k
    simp only [coreShift]
    rw [← hKq, hKqs i k, mul_pow, mul_pow, Real.sq_sqrt (hy i), Real.sq_sqrt (hy k)]
    ring
  have hcg : coreGreen G a τ y σ S v i i - coreShift G a τ z y σ S v i i =
      y i * (K i i - Kq i i) := by
    simp only [coreGreen, coreShift]
    rw [← hK, ← hKq]
    linear_combination (K i i - Kq i i) * Real.mul_self_sqrt (hy i)
  rw [Finset.sum_congr rfl fun k _ => hcs k, ← Finset.mul_sum, hcg]
  calc z * (y i * ∑ k ∈ nbhd G S v, y k * Kq k i ^ 2) =
        y i * (z * ∑ k ∈ nbhd G S v, y k * Kq k i ^ 2) := by ring
    _ ≤ y i * (K i i - Kq i i) := mul_le_mul_of_nonneg_left hfin (hy i)

/-- `bᵀ X b = a² y_v Σ_{i,j ∈ N} ξ_i (√y_i X_ij √y_j) ξ_j` for the incident column `b`. -/
theorem incCol_quad {a τ : ℝ} (hτ : τ ^ 2 = 1) {y : V → ℝ} (hy : ∀ i, 0 ≤ y i)
    (σ : Config V) {S : Finset V} {v : V} (hv : v ∈ S) (X : Matrix V V ℝ) :
    incCol G a τ y σ S v ⬝ᵥ (X *ᵥ incCol G a τ y σ S v) =
      a ^ 2 * y v * ∑ i : nbhd G S v, ∑ j : nbhd G S v, rootSigns G σ S v i *
        (Real.sqrt (y i) * X i j * Real.sqrt (y j)) * rootSigns G σ S v j := by
  have hc : (τ * a * Real.sqrt (y v)) ^ 2 = a ^ 2 * y v := by
    rw [mul_pow, mul_pow, hτ, Real.sq_sqrt (hy v), one_mul]
  have hnum : incCol G a τ y σ S v ⬝ᵥ (X *ᵥ incCol G a τ y σ S v) =
      ∑ i : nbhd G S v, ∑ j : nbhd G S v,
        τ * a * Real.sqrt (y v) * (Real.sqrt (y i) * sgn σ v i) *
          (X i j * (τ * a * Real.sqrt (y v) * (Real.sqrt (y j) * sgn σ v j))) := by
    simp only [dotProduct, mulVec, incCol_eq_ite G a τ y σ hv, mul_ite, mul_zero, ite_mul,
      zero_mul, Finset.sum_ite_mem, Finset.univ_inter]
    simp only [Finset.mul_sum]
    rw [← Finset.sum_coe_sort (nbhd G S v)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_coe_sort (nbhd G S v)]
  rw [hnum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [rootSigns]
  linear_combination (Real.sqrt (y i) * sgn σ v i * X i j * (Real.sqrt (y j) * sgn σ v j)) * hc

/-- `D_v q_{M_z}(ξ) = a² y_v Σ_{i,j ∈ N} ξ_i (C_z)_ij ξ_j`. -/
theorem diagD_mul_qForm_rootMzG {a τ z : ℝ} {y : V → ℝ} (hy : ∀ i, 0 ≤ y i) (σ : Config V)
    (S : Finset V) (v : V) :
    diagD G a y S v * qForm (rootMzG G a τ z y σ S v) (rootSigns G σ S v) =
      a ^ 2 * y v * ∑ i : nbhd G S v, ∑ j : nbhd G S v, rootSigns G σ S v i *
        (Real.sqrt (y i) * (precCore G a τ y σ S v + z • srcDiag y (S.erase v))⁻¹ i j *
          Real.sqrt (y j)) * rootSigns G σ S v j := by
  have hD : diagD G a y S v ≠ 0 :=
    (lt_of_lt_of_le one_pos (FloorIns.one_le_diagD G a hy S v)).ne'
  have hc : diagD G a y S v * (a ^ 2 * y v / diagD G a y S v) = a ^ 2 * y v := by
    field_simp
  rw [rootMzG_eq_smul, qForm, smul_mulVec, dotProduct_smul, smul_eq_mul, ← mul_assoc, hc]
  congr 1
  simp only [dotProduct, mulVec, shiftY, coreShift, of_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- The root row through the star vector: `(Aξ)_j D_v h_v = -τ a G_vj` (`P̃ ≻ 0`, `τ² = 1`). -/
theorem rootMat_mulVec_mul_rootT {a τ : ℝ} (hτ : τ ^ 2 = 1) {y : V → ℝ} (hy : ∀ i, 0 ≤ y i)
    {σ : Config V} {S : Finset V} {v : V} (hv : v ∈ S) (hP : (precN G a τ y σ S).PosDef)
    (j : nbhd G S v) :
    (rootMat G a τ y σ S v *ᵥ rootSigns G σ S v) j * (diagD G a y S v * hN G a τ y σ S v) =
      -(τ * a) * greenP G a τ y σ S v j := by
  obtain ⟨-, hrow, -⟩ := precN_schur G hv hP
  have hjv : (j : V) ≠ v := (G.ne_of_adj (Finset.mem_filter.1 j.2).2).symm
  have hD : diagD G a y S v ≠ 0 :=
    (lt_of_lt_of_le one_pos (FloorIns.one_le_diagD G a hy S v)).ne'
  obtain ⟨m, hm⟩ : ∃ m, m = ∑ i : nbhd G S v,
      (precCore G a τ y σ S v)⁻¹ j i * (Real.sqrt (y i) * sgn σ v i) := ⟨_, rfl⟩
  have hu : ((precCore G a τ y σ S v)⁻¹ *ᵥ incCol G a τ y σ S v) j =
      τ * a * Real.sqrt (y v) * m := by
    rw [hm]
    simp only [mulVec, dotProduct, incCol_eq_ite G a τ y σ hv, mul_ite, mul_zero,
      Finset.sum_ite_mem, Finset.univ_inter]
    rw [← Finset.sum_coe_sort (nbhd G S v), Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hA : (rootMat G a τ y σ S v *ᵥ rootSigns G σ S v) j =
      a ^ 2 * y v / diagD G a y S v * Real.sqrt (y j) * m := by
    rw [hm]
    simp only [mulVec, dotProduct, rootMat, coreGreen, of_apply, rootSigns, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  obtain ⟨g, hg⟩ : ∃ g, g = (precN G a τ y σ S)⁻¹ v v := ⟨_, rfl⟩
  have hG : greenP G a τ y σ S v j =
      -(Real.sqrt (y v) * (g * (τ * a * Real.sqrt (y v) * m)) * Real.sqrt (y j)) := by
    simp only [greenP]
    rw [hrow j hjv, hu, ← hg]
    ring
  have hh : hN G a τ y σ S v = g := by rw [hg]; rfl
  have hyv := Real.mul_self_sqrt (hy v)
  rw [hA, hG, hh]
  calc a ^ 2 * y v / diagD G a y S v * Real.sqrt (y j) * m * (diagD G a y S v * g) =
        (a ^ 2 * y v / diagD G a y S v * diagD G a y S v) * (Real.sqrt (y j) * m * g) := by
        ring
    _ = a ^ 2 * y v * (Real.sqrt (y j) * m * g) := by rw [div_mul_cancel₀ _ hD]
    _ = _ := by
        linear_combination (-(a ^ 2 * g * m * Real.sqrt (y j))) * hyv +
          (-(a ^ 2 * g * m * Real.sqrt (y j) * (Real.sqrt (y v) * Real.sqrt (y v)))) * hτ

/-- `q_{RMR}(x) t² = q_M(t Rx)` for symmetric `R`. -/
theorem qForm_conj_mul_sq {ι : Type*} [Fintype ι] {R : Matrix ι ι ℝ}
    (hR : ∀ i j, R i j = R j i) (M : Matrix ι ι ℝ) (x : ι → ℝ) (t : ℝ) :
    qForm (R * M * R) x * t ^ 2 = qForm M (t • (R *ᵥ x)) := by
  have hRt : Rᵀ = R := by
    ext i j
    exact hR j i
  simp only [qForm]
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose, hRt, mulVec_smul,
    smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  ring

theorem sq_of_mul_eq {x t c g : ℝ} (h : x * t = -c * g) : t * x * (t * x) = c ^ 2 * g ^ 2 := by
  rw [show t * x * (t * x) = (x * t) ^ 2 by ring, h]
  ring

/-! #### The nodes -/

/-- `A-C5b`: core shifted diagonals are below the full shifted diagonals. -/
theorem coreShift_le_shiftP {a τ z : ℝ} (hz : 0 ≤ z) {y : V → ℝ} (hy : ∀ i, 0 ≤ y i)
    {σ : Config V} {S : Finset V} {v : V} (hv : v ∈ S) (hP : (precN G a τ y σ S).PosDef)
    {i : V} (hi : i ≠ v) : coreShift G a τ z y σ S v i i ≤ shiftP G a τ z y σ S i i := by
  have hQ := hP.add_posSemidef (srcDiag_smul_posSemidef hz hy S)
  obtain ⟨-, -, hij⟩ := shift_schur G hv hQ
  simp only [coreShift, shiftP]
  rw [hij i i hi hi]
  exact sqrt_mul_le_sqrt_mul_add _ _ _ _ hQ.inv.diag_pos.le

/-- `A-C5b`: the shift decreases the core diagonals. -/
theorem coreShift_le_coreGreen {a τ z : ℝ} (hz : 0 ≤ z) {y : V → ℝ} (hy : ∀ i, 0 ≤ y i)
    {σ : Config V} {S : Finset V} {v : V} (hM : (precCore G a τ y σ S v).PosDef) (i : V) :
    coreShift G a τ z y σ S v i i ≤ coreGreen G a τ y σ S v i i := by
  simp only [coreShift, coreGreen]
  have h := inv_diag_add_le' hM (srcDiag_smul_posSemidef hz hy (S.erase v)) i
  nlinarith [mul_nonneg (mul_self_nonneg (Real.sqrt (y i))) (sub_nonneg.2 h)]

/-- `A-C5c` (C5(iv)): the full/core shifted trace correction on `N`. -/
theorem sum_shift_sub_core_le {a τ z : ℝ} (hτ : τ ^ 2 = 1) (hz : 0 < z) {y : V → ℝ}
    (hy : ∀ i, 0 ≤ y i) {σ : Config V} {S : Finset V} {v : V} (hv : v ∈ S)
    (hP : (precN G a τ y σ S).PosDef) :
    ∑ i ∈ nbhd G S v, (shiftP G a τ z y σ S i i - coreShift G a τ z y σ S v i i) ≤
      diagD G a y S v * (hN G a τ y σ S v - hzN G a τ z y σ S v) / z := by
  have hQ := hP.add_posSemidef (srcDiag_smul_posSemidef hz.le hy S)
  have hPc : (precCore G a τ y σ S v).PosDef := precCore_posDef_of_precN G hP
  obtain ⟨hdz, -, hijz⟩ := shift_schur G hv hQ
  obtain ⟨hd0, -, -⟩ := precN_schur G hv hP
  have hkey := quad_inv_sub_inv_add_ge hPc (srcDiag_posSemidef hy (S.erase v)) hz.le
    (incCol G a τ y σ S v)
  have hbK : 0 ≤ incCol G a τ y σ S v ⬝ᵥ ((precCore G a τ y σ S v)⁻¹ *ᵥ incCol G a τ y σ S v) := by
    have := hPc.inv.posSemidef.dotProduct_mulVec_nonneg (incCol G a τ y σ S v)
    rwa [star_trivial] at this
  have hg : 0 < (precN G a τ y σ S)⁻¹ v v := hP.inv.diag_pos
  have hgz : 0 < (precN G a τ y σ S + z • srcDiag y S)⁻¹ v v := hQ.inv.diag_pos
  obtain ⟨g, hgdef⟩ : ∃ g, g = (precN G a τ y σ S)⁻¹ v v := ⟨_, rfl⟩
  obtain ⟨gz, hgzdef⟩ : ∃ gz, gz = (precN G a τ y σ S + z • srcDiag y S)⁻¹ v v := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u, u = (precCore G a τ y σ S v + z • srcDiag y (S.erase v))⁻¹ *ᵥ
      incCol G a τ y σ S v := ⟨_, rfl⟩
  obtain ⟨bK, hbKdef⟩ : ∃ bK, bK = incCol G a τ y σ S v ⬝ᵥ
      ((precCore G a τ y σ S v)⁻¹ *ᵥ incCol G a τ y σ S v) := ⟨_, rfl⟩
  rw [← hgdef] at hd0 hg
  rw [← hbKdef] at hd0 hbK
  rw [← hgzdef, ← hu] at hdz hijz
  rw [← hgzdef] at hgz
  rw [← hu, ← hbKdef] at hkey
  have hL : ∑ i ∈ nbhd G S v, (shiftP G a τ z y σ S i i - coreShift G a τ z y σ S v i i) =
      gz * ∑ i ∈ nbhd G S v, y i * u i ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hiv : i ≠ v := (G.ne_of_adj (Finset.mem_filter.1 hi).2).symm
    simp only [shiftP, coreShift]
    rw [hijz i i hiv hiv]
    linear_combination (gz * u i ^ 2) * Real.mul_self_sqrt (hy i)
  have hYu : ∑ i ∈ nbhd G S v, y i * u i ^ 2 ≤ u ⬝ᵥ (srcDiag y (S.erase v) *ᵥ u) := by
    have e : u ⬝ᵥ (srcDiag y (S.erase v) *ᵥ u) =
        ∑ k, (if k ∈ S.erase v then y k else 0) * u k ^ 2 := by
      simp only [srcDiag, mulVec_diagonal, dotProduct]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [e]
    calc ∑ i ∈ nbhd G S v, y i * u i ^ 2 =
          ∑ i ∈ nbhd G S v, (if i ∈ S.erase v then y i else 0) * u i ^ 2 := by
          refine Finset.sum_congr rfl fun i hi => ?_
          have hiS : i ∈ S.erase v := by
            have h' := Finset.mem_filter.1 hi
            exact Finset.mem_erase.2 ⟨(G.ne_of_adj h'.2).symm, h'.1⟩
          rw [ite_eq_left hiS]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun k _ _ =>
          mul_nonneg (by split_ifs; exacts [hy k, le_rfl]) (sq_nonneg _)
  have hX0 : 0 ≤ ∑ i ∈ nbhd G S v, y i * u i ^ 2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hy i) (sq_nonneg _)
  have hΔ : z * ∑ i ∈ nbhd G S v, y i * u i ^ 2 ≤ bK - incCol G a τ y σ S v ⬝ᵥ u :=
    (mul_le_mul_of_nonneg_left hYu hz.le).trans hkey
  have hDg : 1 ≤ diagD G a y S v * g := by
    have : diagD G a y S v * g = 1 + g * bK := by linear_combination hd0
    nlinarith [mul_nonneg hg.le hbK]
  have e : g - gz = g * gz * (z * y v + (bK - incCol G a τ y σ S v ⬝ᵥ u)) := by
    linear_combination gz * hd0 - g * hdz
  have hT : 0 ≤ z * y v + (bK - incCol G a τ y σ S v ⬝ᵥ u) := by
    nlinarith [mul_nonneg hz.le (hy v), mul_nonneg hz.le hX0]
  have hhN : hN G a τ y σ S v = g := by rw [hgdef]; rfl
  have hhz : hzN G a τ z y σ S v = gz := by rw [hgzdef]; rfl
  rw [hL, hhN, hhz, le_div_iff₀ hz]
  calc gz * (∑ i ∈ nbhd G S v, y i * u i ^ 2) * z =
        gz * (z * ∑ i ∈ nbhd G S v, y i * u i ^ 2) := by ring
    _ ≤ gz * (z * y v + (bK - incCol G a τ y σ S v ⬝ᵥ u)) :=
        mul_le_mul_of_nonneg_left (by nlinarith [mul_nonneg hz.le (hy v)]) hgz.le
    _ ≤ (diagD G a y S v * g) * (gz * (z * y v + (bK - incCol G a τ y σ S v ⬝ᵥ u))) :=
        le_mul_of_one_le_left (mul_nonneg hgz.le hT) hDg
    _ = diagD G a y S v * (g - gz) := by rw [e]; ring

/-- `A-C5d`: the root Schur identity of the shifted precision. -/
theorem inv_hzN_root {a τ z : ℝ} (hτ : τ ^ 2 = 1) (hz : 0 ≤ z) {y : V → ℝ}
    (hy : ∀ i, 0 ≤ y i) {σ : Config V} {S : Finset V} {v : V} (hv : v ∈ S)
    (hP : (precN G a τ y σ S).PosDef) :
    1 / hzN G a τ z y σ S v =
      diagD G a y S v * (1 - qForm (rootMzG G a τ z y σ S v) (rootSigns G σ S v)) + z * y v := by
  have hQ := hP.add_posSemidef (srcDiag_smul_posSemidef hz hy S)
  obtain ⟨hd, -, -⟩ := shift_schur G hv hQ
  have hb : incCol G a τ y σ S v ⬝ᵥ ((precCore G a τ y σ S v + z • srcDiag y (S.erase v))⁻¹ *ᵥ
      incCol G a τ y σ S v) =
      diagD G a y S v * qForm (rootMzG G a τ z y σ S v) (rootSigns G σ S v) := by
    rw [incCol_quad G hτ hy σ hv, diagD_mul_qForm_rootMzG G hy]
  rw [hb] at hd
  have hX : (precN G a τ y σ S + z • srcDiag y S)⁻¹ v v ≠ 0 := hQ.inv.diag_pos.ne'
  change 1 / (precN G a τ y σ S + z • srcDiag y S)⁻¹ v v = _
  rw [div_eq_iff hX]
  linear_combination -hd

/-- `A-C5e` (C5(vi)): mixed core traces against the shifted core. -/
theorem sum_coreShift_mul_coreGreen_le {a τ z : ℝ} (hz : 0 < z) {yp y : V → ℝ}
    (hyp : ∀ i, 0 ≤ yp i) (hy : ∀ i, 0 ≤ y i) {σ : Config V} {S : Finset V} {v : V}
    (hMp : (precCore G a 1 yp σ S v).PosDef) (hM : (precCore G a τ y σ S v).PosDef) :
    ∑ i ∈ nbhd G S v, ∑ j ∈ nbhd G S v,
        coreShift G a 1 z yp σ S v i j * coreGreen G a τ y σ S v j i ≤
      2 / z * (∑ i ∈ nbhd G S v, (coreGreen G a 1 yp σ S v i i - coreShift G a 1 z yp σ S v i i) +
        ∑ i ∈ nbhd G S v, (coreGreen G a τ y σ S v i i - coreShift G a τ z y σ S v i i)) := by
  obtain ⟨X, hX⟩ : ∃ X, X = shiftY G a 1 z yp σ S v := ⟨_, rfl⟩
  obtain ⟨Xc, hXc⟩ : ∃ Xc, Xc = (SecC.compR G yp S v)ᴴ * (precCore G a 1 yp σ S v)⁻¹ *
      SecC.compR G yp S v := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y, Y = (SecC.compR G y S v)ᴴ * (precCore G a τ y σ S v)⁻¹ *
      SecC.compR G y S v := ⟨_, rfl⟩
  obtain ⟨Yz, hYz⟩ : ∃ Yz, Yz = shiftY G a τ z y σ S v := ⟨_, rfl⟩
  have hXe : ∀ i j : nbhd G S v, X i j = coreShift G a 1 z yp σ S v i j := fun i j => by
    rw [hX]; rfl
  have hYze : ∀ i j : nbhd G S v, Yz i j = coreShift G a τ z y σ S v i j := fun i j => by
    rw [hYz]; rfl
  have hXce : ∀ i j : nbhd G S v, Xc i j = coreGreen G a 1 yp σ S v i j := fun i j => by
    rw [hXc]; exact conj_core_apply G a 1 yp σ S v i j
  have hYe : ∀ i j : nbhd G S v, Y i j = coreGreen G a τ y σ S v i j := fun i j => by
    rw [hY]; exact conj_core_apply G a τ y σ S v i j
  have hXle : (z⁻¹ • (1 : Matrix (nbhd G S v) (nbhd G S v) ℝ) - X).PosSemidef := by
    rw [hX]; exact shiftY_le G hz hyp hMp
  have hYd : (Y - Yz).PosSemidef := by rw [hY, hYz]; exact core_sub_shiftY_posSemidef G hz.le hy hM
  have hXd : (Xc - X).PosSemidef := by
    rw [hXc, hX]; exact core_sub_shiftY_posSemidef G hz.le hyp hMp
  have hQp : (precCore G a 1 yp σ S v + z • srcDiag yp (S.erase v)).PosDef :=
    hMp.add_posSemidef (srcDiag_smul_posSemidef hz.le hyp _)
  have hQ : (precCore G a τ y σ S v + z • srcDiag y (S.erase v)).PosDef :=
    hM.add_posSemidef (srcDiag_smul_posSemidef hz.le hy _)
  have hXs : X.IsHermitian := by
    rw [hX, shiftY_eq_conj]; exact isHermitian_conjTranspose_mul_mul _ hQp.inv.isHermitian
  have hYzs : Yz.IsHermitian := by
    rw [hYz, shiftY_eq_conj]; exact isHermitian_conjTranspose_mul_mul _ hQ.inv.isHermitian
  have hcsym : ∀ (yy : V → ℝ) (τ' : ℝ) (i k : V),
      (precCore G a τ' yy σ S v + z • srcDiag yy (S.erase v)).PosDef →
      coreShift G a τ' z yy σ S v k i = coreShift G a τ' z yy σ S v i k := by
    intro yy τ' i k hQ'
    have h : (precCore G a τ' yy σ S v + z • srcDiag yy (S.erase v))⁻¹ k i =
        (precCore G a τ' yy σ S v + z • srcDiag yy (S.erase v))⁻¹ i k := by
      simpa using hQ'.inv.isHermitian.apply i k
    simp only [coreShift]
    rw [h]
    ring
  -- traces
  have htrsq : ∀ (W : Matrix (nbhd G S v) (nbhd G S v) ℝ) (yy : V → ℝ) (τ' : ℝ),
      (precCore G a τ' yy σ S v + z • srcDiag yy (S.erase v)).PosDef →
      (∀ i j : nbhd G S v, W i j = coreShift G a τ' z yy σ S v i j) →
      z * (W * W).trace =
        ∑ i : nbhd G S v, z * ∑ k ∈ nbhd G S v, coreShift G a τ' z yy σ S v i k ^ 2 := by
    intro W yy τ' hQ' hW
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_coe_sort (nbhd G S v)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hW, hW, hcsym yy τ' i k hQ']
    ring
  have htrdiff : ∀ (W Wc : Matrix (nbhd G S v) (nbhd G S v) ℝ) (yy : V → ℝ) (τ' : ℝ),
      (∀ i j : nbhd G S v, W i j = coreShift G a τ' z yy σ S v i j) →
      (∀ i j : nbhd G S v, Wc i j = coreGreen G a τ' yy σ S v i j) →
      (Wc - W).trace =
        ∑ i ∈ nbhd G S v, (coreGreen G a τ' yy σ S v i i - coreShift G a τ' z yy σ S v i i) := by
    intro W Wc yy τ' hW hWc
    rw [← Finset.sum_coe_sort (nbhd G S v)]
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.sub_apply, hW, hWc]
  have hXX : z * (X * X).trace ≤ (Xc - X).trace := by
    rw [htrsq X yp 1 hQp hXe, htrdiff X Xc yp 1 hXe hXce, ← Finset.sum_coe_sort (nbhd G S v)]
    exact Finset.sum_le_sum fun i _ => sum_coreShift_sq_le G hz.le hyp hMp i
  have hYY : z * (Yz * Yz).trace ≤ (Y - Yz).trace := by
    rw [htrsq Yz y τ hQ hYze, htrdiff Yz Y y τ hYze hYe, ← Finset.sum_coe_sort (nbhd G S v)]
    exact Finset.sum_le_sum fun i _ => sum_coreShift_sq_le G hz.le hy hM i
  have hXYz : 2 * (X * Yz).trace ≤ (X * X).trace + (Yz * Yz).trace := by
    have h := (posSemidef_conjTranspose_mul_self (X - Yz)).trace_nonneg
    rw [conjTranspose_sub, hXs.eq, hYzs.eq, sub_mul, mul_sub, mul_sub, trace_sub, trace_sub,
      trace_sub, trace_mul_comm Yz X] at h
    linarith
  have hXD : z * (X * (Y - Yz)).trace ≤ (Y - Yz).trace := by
    have h := trace_mul_nonneg hXle hYd
    rw [Matrix.sub_mul, smul_mul_assoc, one_mul, trace_sub, trace_smul, smul_eq_mul] at h
    have h2 := mul_le_mul_of_nonneg_left (sub_nonneg.1 h) hz.le
    rwa [← mul_assoc, mul_inv_cancel₀ hz.ne', one_mul] at h2
  have h1 : 0 ≤ (Y - Yz).trace := hYd.trace_nonneg
  have h2 : 0 ≤ (Xc - X).trace := hXd.trace_nonneg
  have hLHS : ∑ i ∈ nbhd G S v, ∑ j ∈ nbhd G S v,
      coreShift G a 1 z yp σ S v i j * coreGreen G a τ y σ S v j i = (X * Y).trace := by
    rw [← Finset.sum_coe_sort (nbhd G S v)]
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_coe_sort (nbhd G S v)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hXe, hYe]
  rw [hLHS, ← htrdiff X Xc yp 1 hXe hXce, ← htrdiff Yz Y y τ hYze hYe]
  have hsplit : (X * Y).trace = (X * Yz).trace + (X * (Y - Yz)).trace := by
    rw [mul_sub, trace_sub]
    ring
  rw [hsplit, div_mul_eq_mul_div, le_div_iff₀ hz]
  nlinarith [mul_le_mul_of_nonneg_left hXYz hz.le]

/-- `A-C5g`: at a good core, `0 ⪯ M_z ⪯ A` (`C_z ⪯ C`, both PSD; `a² y_v/D_v ≥ 0`). -/
theorem rootMz_psd_le {a z : ℝ} (hz : 0 ≤ z) {y : V → ℝ} (hy : ∀ i, 0 ≤ y i) {σ : Config V}
    {S : Finset V} {v : V} (hM : (precCore G a 1 y σ S v).PosDef) :
    (rootMzG G a 1 z y σ S v).PosSemidef ∧
      (rootMat G a 1 y σ S v - rootMzG G a 1 z y σ S v).PosSemidef := by
  rcases hz.eq_or_lt with rfl | hz
  · have e : rootMzG G a 1 0 y σ S v = rootMat G a 1 y σ S v := by
      ext i j
      simp [rootMzG, rootMat, coreShift, coreGreen]
    rw [e, sub_self]
    exact ⟨rootMat_posSemidef G hy hM, PosSemidef.zero⟩
  · obtain ⟨-, h2, h3, -⟩ := SecC.shift_branch G hy (le_refl (y v)) hz hM
    have e : rootMzG G a 1 z y σ S v = shiftM G a 1 z y σ S v := by
      rw [rootMzG_eq_smul]
      rfl
    rw [e]
    exact ⟨h2, h3⟩

/-- `T = Σ_{i ∈ N} (C_ii - C_{z,ii})`, the core trace defect of the shift. -/
noncomputable def coreDefect (a τ z : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) (v : V) : ℝ :=
  ∑ i ∈ nbhd G S v, (coreGreen G a τ y σ S v i i - coreShift G a τ z y σ S v i i)

theorem shiftP_diag_eq {a τ z : ℝ} {y : V → ℝ} {σ : Config V} {S : Finset V} {i : V}
    (hy : 0 ≤ y i) : shiftP G a τ z y σ S i i = y i * hzN G a τ z y σ S i := by
  rw [shiftP, hzN, mul_comm (Real.sqrt (y i)), mul_assoc, Real.mul_self_sqrt hy, mul_comm]

theorem coreShift_diag_nonneg {a τ z : ℝ} (hz : 0 ≤ z) {y : V → ℝ} (hy : ∀ i, 0 ≤ y i)
    {σ : Config V} {S : Finset V} {v : V} (hM : (precCore G a τ y σ S v).PosDef) (i : V) :
    0 ≤ coreShift G a τ z y σ S v i i := by
  have hQ := hM.add_posSemidef (srcDiag_smul_posSemidef hz hy (S.erase v))
  have h := hQ.inv.diag_pos (i := i)
  simp only [coreShift]
  rw [mul_comm (Real.sqrt (y i)), mul_assoc]
  exact mul_nonneg h.le (mul_self_nonneg _)

theorem coreDefect_nonneg {a τ z : ℝ} (hz : 0 ≤ z) {y : V → ℝ} (hy : ∀ i, 0 ≤ y i)
    {σ : Config V} {S : Finset V} {v : V} (hM : (precCore G a τ y σ S v).PosDef) :
    0 ≤ coreDefect G a τ z y σ S v :=
  Finset.sum_nonneg fun i _ => sub_nonneg.2 (coreShift_le_coreGreen G hz hy hM i)

/-- `T ≤ Σ_{i ∈ N} y_i (h_i - h_{z,i}) + (D_v/z)(h_v - h_{z,v})` (C5b, C5c). -/
theorem coreDefect_le {a τ z : ℝ} (hτ : τ ^ 2 = 1) (hz : 0 < z) {y : V → ℝ}
    (hy : ∀ i, 0 ≤ y i) {σ : Config V} {S : Finset V} {v : V} (hv : v ∈ S)
    (hP : (precN G a τ y σ S).PosDef) :
    coreDefect G a τ z y σ S v ≤
      ∑ i ∈ nbhd G S v, y i * (hN G a τ y σ S i - hzN G a τ z y σ S i) +
        diagD G a y S v / z * (hN G a τ y σ S v - hzN G a τ z y σ S v) := by
  have h1 := sum_shift_sub_core_le G hτ hz hy hv hP
  have h2 : coreDefect G a τ z y σ S v ≤
      ∑ i ∈ nbhd G S v, (y i * (hN G a τ y σ S i - hzN G a τ z y σ S i) +
        (shiftP G a τ z y σ S i i - coreShift G a τ z y σ S v i i)) := by
    refine Finset.sum_le_sum fun i hi => ?_
    have hiv : i ≠ v := FloorIns.ne_of_mem_nbhd G hi
    have hc := coreGreen_le_greenP G hy hv hP hiv
    rw [greenP_self G (hy i)] at hc
    rw [shiftP_diag_eq G (hy i)]
    have e : y i * (hN G a τ y σ S i - hzN G a τ z y σ S i) +
        (y i * hzN G a τ z y σ S i - coreShift G a τ z y σ S v i i) =
        y i * hN G a τ y σ S i - coreShift G a τ z y σ S v i i := by ring
    linarith
  rw [Finset.sum_add_distrib] at h2
  have e : diagD G a y S v * (hN G a τ y σ S v - hzN G a τ z y σ S v) / z =
      diagD G a y S v / z * (hN G a τ y σ S v - hzN G a τ z y σ S v) := by ring
  linarith

/-- `T ≤ Σ_{i ∈ N} y_i h_i` (C5b and `C_{z,ii} ≥ 0`). -/
theorem coreDefect_le_sum {a τ z : ℝ} (hz : 0 ≤ z) {y : V → ℝ} (hy : ∀ i, 0 ≤ y i)
    {σ : Config V} {S : Finset V} {v : V} (hv : v ∈ S) (hP : (precN G a τ y σ S).PosDef) :
    coreDefect G a τ z y σ S v ≤ ∑ i ∈ nbhd G S v, y i * hN G a τ y σ S i := by
  have hM := precCore_posDef_of_precN G (v := v) hP
  refine Finset.sum_le_sum fun i hi => ?_
  have hc := coreGreen_le_greenP G hy hv hP (FloorIns.ne_of_mem_nbhd G hi)
  rw [greenP_self G (hy i)] at hc
  have := coreShift_diag_nonneg G hz hy hM i
  linarith

/-- T.IL on the support of the paired law. -/
theorem lawE_mul_le_interp {p : ℕ} {a : ℝ} {yp ym : V → ℝ} {S : Finset V}
    (hZ : 0 < Zw G p a yp ym S) {X Y : Config V → ℝ}
    (hX : ∀ σ, wt G p a yp ym σ S ≠ 0 → 0 ≤ X σ) (hY : ∀ σ, wt G p a yp ym σ S ≠ 0 → 0 ≤ Y σ)
    {k : ℕ} (hk : 1 ≤ k) {m θ BX BY : ℝ} (hθ : 0 < θ) (hθm : θ ≤ m) (hBX : 0 ≤ BX)
    (hBY : 0 ≤ BY) (hXm : lawE G p a yp ym S X ≤ m)
    (hX2 : lawE G p a yp ym S (fun σ => X σ ^ 2) ≤ BX ^ 2)
    (hY2k : lawE G p a yp ym S (fun σ => Y σ ^ (2 * k)) ≤ BY ^ (2 * k)) :
    lawE G p a yp ym S (fun σ => X σ * Y σ) ≤
      m * θ ^ (-(1 / (k : ℝ))) * BX ^ (1 / (k : ℝ)) * BY := by
  have hcX : ∀ σ, wt G p a yp ym σ S ≠ 0 → max (X σ) 0 = X σ := fun σ hσ =>
    max_eq_left (hX σ hσ)
  have hcY : ∀ σ, wt G p a yp ym σ S ≠ 0 → max (Y σ) 0 = Y σ := fun σ hσ =>
    max_eq_left (hY σ hσ)
  have e0 : lawE G p a yp ym S (fun σ => X σ * Y σ) =
      lawE G p a yp ym S (fun σ => max (X σ) 0 * max (Y σ) 0) :=
    lawE_congr G fun σ hσ => by rw [hcX σ hσ, hcY σ hσ]
  have e1 : lawE G p a yp ym S X = lawE G p a yp ym S (fun σ => max (X σ) 0) :=
    lawE_congr G fun σ hσ => (hcX σ hσ).symm
  have e2 : lawE G p a yp ym S (fun σ => X σ ^ 2) =
      lawE G p a yp ym S (fun σ => max (X σ) 0 ^ 2) :=
    lawE_congr G fun σ hσ => by rw [hcX σ hσ]
  have e3 : lawE G p a yp ym S (fun σ => Y σ ^ (2 * k)) =
      lawE G p a yp ym S (fun σ => max (Y σ) 0 ^ (2 * k)) :=
    lawE_congr G fun σ hσ => by rw [hcY σ hσ]
  rw [e0]
  rw [e1] at hXm
  rw [e2] at hX2
  rw [e3] at hY2k
  simp only [lawE_eq_wavg] at hXm hX2 hY2k ⊢
  exact wavg_mul_le_interp (fun σ => wt_nonneg G σ) hZ (fun σ => le_max_right _ _)
    (fun σ => le_max_right _ _) hk hθ hθm hBX hBY hXm hX2 hY2k

end C5

/-- The interpolation constant: `8 x d^{1/k} (4c)^{1/k} (2c) ≤ 180 x` for `log d ≤ k`,
`1 ≤ c ≤ 1.01`. -/
theorem interp_const_le {d : ℝ} (hd : 0 < d) {k : ℕ} (hk1 : 1 ≤ k) (hkge : Real.log d ≤ k)
    {c : ℝ} (hc1 : 1 ≤ c) (hc2 : c ≤ 101 / 100) {x : ℝ} (hx : 0 ≤ x) :
    8 * x * (1 / d) ^ (-(1 / (k : ℝ))) * (4 * c) ^ (1 / (k : ℝ)) * (2 * c) ≤ 180 * x := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
  have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hE : (1 / d) ^ (-(1 / (k : ℝ))) ≤ 2.7182818286 := by
    rw [Real.rpow_def_of_pos (by positivity)]
    have hl : Real.log (1 / d) = -Real.log d := by rw [one_div, Real.log_inv]
    rw [hl]
    have : -Real.log d * -(1 / (k : ℝ)) ≤ 1 := by
      rw [neg_mul_neg, mul_one_div, div_le_one hkpos]
      exact hkge
    exact (Real.exp_le_exp.2 this).trans Real.exp_one_lt_d9.le
  have hB : (4 * c) ^ (1 / (k : ℝ)) ≤ 4 * c := by
    calc (4 * c) ^ (1 / (k : ℝ)) ≤ (4 * c) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith)
            (by rw [div_le_one hkpos]; exact hk1')
      _ = 4 * c := Real.rpow_one _
  have h1 : 0 ≤ (4 * c) ^ (1 / (k : ℝ)) := by positivity
  have hB' : (4 * c) ^ (1 / (k : ℝ)) ≤ 4 * (101 / 100) := by linarith
  have hc' : 2 * c ≤ 2 * (101 / 100) := by linarith
  calc 8 * x * (1 / d) ^ (-(1 / (k : ℝ))) * (4 * c) ^ (1 / (k : ℝ)) * (2 * c) ≤
        8 * x * 2.7182818286 * (4 * (101 / 100)) * (2 * (101 / 100)) := by
        refine mul_le_mul ?_ hc' (by positivity) (by positivity)
        refine mul_le_mul ?_ hB' h1 (by positivity)
        exact mul_le_mul_of_nonneg_left hE (by positivity)
    _ ≤ 180 * x := by linarith

section Params

variable {d p : ℕ}

theorem rOf_eq (d p : ℕ) : rOf d p = 1 + epsP d p := by
  rw [epsP]; ring

theorem epsP_le_b0Of (hR : RegA d p) : epsP d p ≤ b0Of d p := by
  have hd := hR.d_pos
  rw [b0Of]
  have : 0 ≤ (p : ℝ) ^ 4 / d := by positivity
  have : 0 ≤ 1 / (d : ℝ) := by positivity
  linarith

theorem aOf_sq_le_half (hR : RegA d p) : aOf d p ^ 2 ≤ 1 / (2 * d) := by
  have h := aOf_sq_le hR.treg
  have hd := hR.d_pos
  have hd2 : (2 : ℝ) ≤ d := by have := hR.treg.ten_pow_six_le_d; linarith
  refine h.trans ?_
  rw [qOf]
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

theorem aOf_four_le (hR : RegA d p) : aOf d p ^ 4 ≤ 1 / (4 * (d : ℝ) ^ 2) := by
  have h := aOf_sq_le_half hR
  have hd := hR.d_pos
  have h0 : 0 ≤ aOf d p ^ 2 := sq_nonneg _
  calc aOf d p ^ 4 = (aOf d p ^ 2) ^ 2 := by ring
    _ ≤ (1 / (2 * (d : ℝ))) ^ 2 := pow_le_pow_left₀ h0 h 2
    _ = 1 / (4 * (d : ℝ) ^ 2) := by field_simp; ring

end Params

end SecA

end BiluLinial.Tight
