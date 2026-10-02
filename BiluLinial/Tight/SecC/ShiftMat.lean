/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecC.Root
public import BiluLinial.Tight.Gauss.CovBound

/-!
# The shifted core matrices (node SHIFTMAT of `docs/tight/BP_SECC.md`)

Source lines 1216–1221 (`0 ⪯ M ⪯ A`, `0 ⪯ 𝒩 ⪯ B`, `‖M‖, ‖𝒩‖ ≤ C a²/h`); AUDIT-C §3 T.MAT (v).

* `two_dot_sub_quad_le`: `2 uᵀx - xᵀPx ≤ uᵀP⁻¹u` for `P ≻ 0` (completing the square).
* `inv_quad_antitone`: `P ⪯ Q`, both `≻ 0` ⇒ `uᵀQ⁻¹u ≤ uᵀP⁻¹u`.
* `inv_quad_le_of_diag`: for `Q = P + z diag(d) ≻ 0`, `P ⪰ 0`, and `2 w_k t - z d_k t² ≤ g_k` for
  all `t`: `wᵀQ⁻¹w ≤ Σ g_k` (at `x = Q⁻¹w`: `wᵀQ⁻¹w = 2wᵀx - xᵀQx ≤ 2wᵀx - z Σ d_k x_k²`).
* `compR`: the compression `ℝ^N → ℝ^V`, `(Ru)_k = √y_k u_k` on `N`, so that
  `A = (a² y_v/D_v) Rᴴ P̃_K⁻¹ R` (`rootMat_eq_conj`) and `M = (a² y_v/D_v) Rᴴ (P̃_K + z Y_K)⁻¹ R`
  (`shiftM_eq_conj`).
-/

@[expose] public section

namespace BiluLinial.Tight

namespace SecC

open Matrix

section Generic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem quad_nonneg_of_posSemidef {P : Matrix ι ι ℝ} (hP : P.PosSemidef) (x : ι → ℝ) :
    0 ≤ x ⬝ᵥ (P *ᵥ x) := by
  have := hP.dotProduct_mulVec_nonneg x
  rwa [star_trivial] at this

/-- Completing the square: `2 uᵀx - xᵀPx ≤ uᵀP⁻¹u` for `P ≻ 0`. -/
theorem two_dot_sub_quad_le {P : Matrix ι ι ℝ} (hP : P.PosDef) (u x : ι → ℝ) :
    2 * (u ⬝ᵥ x) - x ⬝ᵥ (P *ᵥ x) ≤ u ⬝ᵥ (P⁻¹ *ᵥ u) := by
  have h := quad_sub_inv_mulVec hP u x
  have h0 := quad_nonneg_of_posSemidef hP.posSemidef (x - P⁻¹ *ᵥ u)
  linarith

theorem mulVec_inv_mulVec {Q : Matrix ι ι ℝ} (hQ : Q.PosDef) (u : ι → ℝ) :
    Q *ᵥ (Q⁻¹ *ᵥ u) = u := by
  rw [mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Q.isUnit_iff_isUnit_det).1 hQ.isUnit),
    one_mulVec]

/-- Antitonicity of the inverse on quadratic forms. -/
theorem inv_quad_antitone {P Q : Matrix ι ι ℝ} (hP : P.PosDef) (hQ : Q.PosDef)
    (hPQ : (Q - P).PosSemidef) (u : ι → ℝ) :
    u ⬝ᵥ (Q⁻¹ *ᵥ u) ≤ u ⬝ᵥ (P⁻¹ *ᵥ u) := by
  have hQx := mulVec_inv_mulVec hQ u
  have hxQx : (Q⁻¹ *ᵥ u) ⬝ᵥ (Q *ᵥ (Q⁻¹ *ᵥ u)) = u ⬝ᵥ (Q⁻¹ *ᵥ u) := by
    rw [hQx, dotProduct_comm]
  have hd := quad_nonneg_of_posSemidef hPQ (Q⁻¹ *ᵥ u)
  rw [sub_mulVec, dotProduct_sub] at hd
  have hv := two_dot_sub_quad_le hP u (Q⁻¹ *ᵥ u)
  linarith

/-- The variational bound for a diagonal shift. -/
theorem inv_quad_le_of_diag {P : Matrix ι ι ℝ} (hP : P.PosSemidef) {z : ℝ} {d : ι → ℝ}
    (hQ : (P + z • diagonal d).PosDef) (w g : ι → ℝ)
    (hg : ∀ k t, 2 * w k * t - z * d k * t ^ 2 ≤ g k) :
    w ⬝ᵥ ((P + z • diagonal d)⁻¹ *ᵥ w) ≤ ∑ k, g k := by
  have hQx := mulVec_inv_mulVec hQ w
  set x := (P + z • diagonal d)⁻¹ *ᵥ w with hx
  have hxQx : x ⬝ᵥ ((P + z • diagonal d) *ᵥ x) = w ⬝ᵥ x := by rw [hQx, dotProduct_comm]
  have hP0 := quad_nonneg_of_posSemidef hP x
  have hsplit : x ⬝ᵥ ((P + z • diagonal d) *ᵥ x) =
      x ⬝ᵥ (P *ᵥ x) + ∑ k, z * d k * x k ^ 2 := by
    rw [add_mulVec, dotProduct_add, smul_mulVec, dotProduct_smul, smul_eq_mul]
    congr 1
    simp only [dotProduct, mulVec_diagonal, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hsum : 2 * (w ⬝ᵥ x) - ∑ k, z * d k * x k ^ 2 ≤ ∑ k, g k := by
    rw [dotProduct, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum fun k _ => by have := hg k (x k); linarith
  linarith

end Generic

section Graph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The compression `R : ℝ^N → ℝ^V`, `R_{k,i} = √y_i [k = i]`. -/
noncomputable def compR (y : V → ℝ) (S : Finset V) (v : V) : Matrix V (nbhd G S v) ℝ :=
  Matrix.of fun k i => if k = (i : V) then Real.sqrt (y i) else 0

theorem compR_conj_apply (y : V → ℝ) (S : Finset V) (v : V) (X : Matrix V V ℝ)
    (i j : nbhd G S v) :
    ((compR G y S v)ᴴ * X * compR G y S v) i j =
      Real.sqrt (y i) * X i j * Real.sqrt (y j) := by
  simp only [compR, mul_apply, conjTranspose_apply, of_apply, star_trivial, ite_mul, zero_mul,
    mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem compR_mulVec_coe (y : V → ℝ) (S : Finset V) (v : V) (u : nbhd G S v → ℝ)
    (i : nbhd G S v) : (compR G y S v *ᵥ u) i = Real.sqrt (y i) * u i := by
  simp only [compR, mulVec, dotProduct, of_apply, ite_mul, zero_mul]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [ite_eq_right fun h => hj (Subtype.ext h.symm)]
  · simp

theorem compR_mulVec_of_not (y : V → ℝ) (S : Finset V) (v : V) (u : nbhd G S v → ℝ) {k : V}
    (hk : k ∉ nbhd G S v) : (compR G y S v *ᵥ u) k = 0 := by
  simp only [compR, mulVec, dotProduct, of_apply, ite_mul, zero_mul]
  refine Finset.sum_eq_zero fun j _ => ite_eq_right fun h => hk ?_
  rw [h]
  exact j.2

theorem quad_conj (y : V → ℝ) (S : Finset V) (v : V) (X : Matrix V V ℝ)
    (u : nbhd G S v → ℝ) :
    u ⬝ᵥ (((compR G y S v)ᴴ * X * compR G y S v) *ᵥ u) =
      (compR G y S v *ᵥ u) ⬝ᵥ (X *ᵥ (compR G y S v *ᵥ u)) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec,
    conjTranspose_eq_transpose_of_trivial, vecMul_transpose]

theorem rootMat_eq_conj (a τ : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) (v : V) :
    rootMat G a τ y σ S v = (a ^ 2 * y v / diagD G a y S v) •
      ((compR G y S v)ᴴ * (precCore G a τ y σ S v)⁻¹ * compR G y S v) := by
  ext i j
  rw [Matrix.smul_apply, compR_conj_apply, smul_eq_mul]
  rfl

theorem shiftM_eq_conj (a τ z : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) (v : V) :
    shiftM G a τ z y σ S v = (a ^ 2 * y v / diagD G a y S v) •
      ((compR G y S v)ᴴ * (precCore G a τ y σ S v + z • srcDiag y (S.erase v))⁻¹ *
        compR G y S v) := by
  ext i j
  rw [shiftM, Matrix.smul_apply, Matrix.smul_apply, compR_conj_apply]
  rfl

omit [Fintype V] [DecidableEq V] in
theorem one_le_diagD (a : ℝ) {y : V → ℝ} (hy : ∀ i, 0 ≤ y i) (S : Finset V) (v : V) :
    1 ≤ diagD G a y S v := by
  have h : ∀ j ∈ nbhd G S v, 0 ≤ cEdge a y v j := by
    intro j _
    unfold cEdge cRoot
    have h0 : 0 ≤ a ^ 2 * y v * y j := by
      have := hy v
      have := hy j
      positivity
    have : 1 ≤ Real.sqrt (1 + 4 * (a ^ 2 * y v * y j)) := Real.one_le_sqrt.2 (by linarith)
    linarith
  unfold diagD
  linarith [Finset.sum_nonneg h]

/-- **SHIFTMAT, one branch.** If the inherited core precision is positive definite, `y ≥ 0`,
`y_v ≤ s` and `z > 0`: `A ⪰ 0`, `M ⪰ 0`, `M ⪯ A` and `M ⪯ (s a²/z) I`. -/
theorem shift_branch {a τ z s : ℝ} {y : V → ℝ} (hy : ∀ i, 0 ≤ y i) {S : Finset V} {v : V}
    (hys : y v ≤ s) (hz : 0 < z) {σ : Config V} (hP : (precCore G a τ y σ S v).PosDef) :
    (rootMat G a τ y σ S v).PosSemidef ∧ (shiftM G a τ z y σ S v).PosSemidef ∧
      (rootMat G a τ y σ S v - shiftM G a τ z y σ S v).PosSemidef ∧
      ((s * a ^ 2 / z) • (1 : Matrix (nbhd G S v) (nbhd G S v) ℝ) -
        shiftM G a τ z y σ S v).PosSemidef := by
  set R := compR G y S v
  set c := a ^ 2 * y v / diagD G a y S v with hcdef
  have hD1 := one_le_diagD G a hy S v
  have hc : 0 ≤ c := div_nonneg (mul_nonneg (sq_nonneg a) (hy v)) (by linarith)
  have hcs : c ≤ s * a ^ 2 := by
    calc c ≤ a ^ 2 * y v := div_le_self (mul_nonneg (sq_nonneg a) (hy v)) hD1
      _ ≤ a ^ 2 * s := mul_le_mul_of_nonneg_left hys (sq_nonneg a)
      _ = s * a ^ 2 := by ring
  set dv : V → ℝ := fun k => if k ∈ S.erase v then y k else 0 with hdv
  have hdv0 : ∀ k, 0 ≤ dv k := fun k => by
    simp only [hdv]
    split_ifs
    · exact hy k
    · exact le_rfl
  have hsrc : srcDiag y (S.erase v) = diagonal dv := rfl
  have hDpsd : (z • diagonal dv).PosSemidef := (PosSemidef.diagonal hdv0).smul hz.le
  have hQ : (precCore G a τ y σ S v + z • diagonal dv).PosDef := hP.add_posSemidef hDpsd
  have hA : rootMat G a τ y σ S v = c • (Rᴴ * (precCore G a τ y σ S v)⁻¹ * R) :=
    rootMat_eq_conj G a τ y σ S v
  have hM : shiftM G a τ z y σ S v = c • (Rᴴ * (precCore G a τ y σ S v + z • diagonal dv)⁻¹ * R) :=
    shiftM_eq_conj G a τ z y σ S v
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hA]; exact (hP.inv.posSemidef.conjTranspose_mul_mul_same R).smul hc
  · rw [hM]; exact (hQ.inv.posSemidef.conjTranspose_mul_mul_same R).smul hc
  · -- `M ⪯ A`: antitonicity of the inverse
    have hdiff : ((precCore G a τ y σ S v)⁻¹ -
        (precCore G a τ y σ S v + z • diagonal dv)⁻¹).PosSemidef := by
      refine PosSemidef.of_dotProduct_mulVec_nonneg (hP.inv.isHermitian.sub hQ.inv.isHermitian)
        fun x => ?_
      have hQP : (precCore G a τ y σ S v + z • diagonal dv - precCore G a τ y σ S v).PosSemidef :=
        by rwa [add_sub_cancel_left]
      have := inv_quad_antitone hP hQ hQP x
      rw [star_trivial, sub_mulVec, dotProduct_sub]
      linarith
    rw [hA, hM, ← smul_sub, ← Matrix.sub_mul, ← Matrix.mul_sub]
    exact (hdiff.conjTranspose_mul_mul_same R).smul hc
  · -- `M ⪯ (s a²/z) I`
    have hherm : ((s * a ^ 2 / z) • (1 : Matrix (nbhd G S v) (nbhd G S v) ℝ) -
        shiftM G a τ z y σ S v).IsHermitian := by
      refine (isHermitian_one.smul (IsSelfAdjoint.all _)).sub ?_
      rw [hM]
      exact ((hQ.inv.posSemidef.conjTranspose_mul_mul_same R).smul hc).isHermitian
    refine PosSemidef.of_dotProduct_mulVec_nonneg hherm fun x => ?_
    rw [star_trivial, sub_mulVec, dotProduct_sub, smul_mulVec, dotProduct_smul, one_mulVec,
      smul_eq_mul, hM, smul_mulVec, dotProduct_smul, smul_eq_mul, quad_conj]
    -- the variational bound
    set w := R *ᵥ x with hw
    set g : V → ℝ := fun k => w k ^ 2 / (z * dv k) with hg
    have hwz : ∀ k, dv k = 0 → w k = 0 := by
      intro k hk
      by_cases hkN : k ∈ nbhd G S v
      · have hkS : k ∈ S.erase v := by
          have h' := Finset.mem_filter.1 hkN
          exact Finset.mem_erase.2 ⟨(G.ne_of_adj h'.2).symm, h'.1⟩
        have hdk : dv k = y k := by simp only [hdv]; exact ite_eq_left hkS
        have hy0 : y k = 0 := hdk ▸ hk
        rw [hw, show k = ((⟨k, hkN⟩ : nbhd G S v) : V) from rfl, compR_mulVec_coe, hy0,
          Real.sqrt_zero, zero_mul]
      · exact compR_mulVec_of_not G y S v x hkN
    have hgk : ∀ k t, 2 * w k * t - z * dv k * t ^ 2 ≤ g k := by
      intro k t
      rcases (hdv0 k).eq_or_lt with h0 | h0
      · simp only [hg]
        rw [← h0, hwz k h0.symm]
        simp
      · simp only [hg]
        rw [le_div_iff₀ (mul_pos hz h0)]
        nlinarith [sq_nonneg (w k - z * dv k * t)]
    have hbound := inv_quad_le_of_diag hP.posSemidef hQ w g hgk
    have hgsum : ∑ k, g k ≤ (x ⬝ᵥ x) / z := by
      have h1 : ∑ k ∈ nbhd G S v, g k = ∑ k, g k :=
        Finset.sum_subset (Finset.subset_univ _) fun k _ hk => by
          have hwk : w k = 0 := compR_mulVec_of_not G y S v x hk
          simp only [hg, hwk]
          simp
      rw [← h1, ← Finset.sum_coe_sort (nbhd G S v), dotProduct, Finset.sum_div]
      refine Finset.sum_le_sum fun i _ => ?_
      have hiS : (i : V) ∈ S.erase v := by
        have h' := Finset.mem_filter.1 i.2
        exact Finset.mem_erase.2 ⟨(G.ne_of_adj h'.2).symm, h'.1⟩
      have hdi : dv i = y i := by simp only [hdv]; exact ite_eq_left hiS
      have hwi : w i = Real.sqrt (y i) * x i := compR_mulVec_coe G y S v x i
      show w i ^ 2 / (z * dv i) ≤ x i * x i / z
      rw [hwi, hdi, mul_pow, Real.sq_sqrt (hy i)]
      rcases (hy i).eq_or_lt with h0 | h0
      · rw [← h0]
        simp only [zero_mul, mul_zero, div_zero]
        exact div_nonneg (mul_self_nonneg _) hz.le
      · exact le_of_eq (by field_simp)
    have hxx : 0 ≤ x ⬝ᵥ x := by
      rw [dotProduct]; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    have hc' : c * (x ⬝ᵥ x / z) ≤ s * a ^ 2 / z * (x ⬝ᵥ x) := by
      rw [show s * a ^ 2 / z * (x ⬝ᵥ x) = (s * a ^ 2) * (x ⬝ᵥ x / z) by ring]
      exact mul_le_mul_of_nonneg_right hcs (div_nonneg hxx hz.le)
    have := mul_le_mul_of_nonneg_left (hbound.trans hgsum) hc
    rw [hsrc] at *
    linarith

end Graph

end SecC

end BiluLinial.Tight
