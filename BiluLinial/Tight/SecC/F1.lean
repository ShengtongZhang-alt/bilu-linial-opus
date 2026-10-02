/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecC.Root
public import BiluLinial.Tight.SecC.Mark

/-!
# The root Schur identities (F1), the row numerator and the Frobenius bound

Nodes F1, ROWF, FROB of `docs/tight/BP_SECC.md` (source (F1), lines 137–141, and lines
1135–1140; AUDIT-C §3 T.ROOT).

**Block inverse through the core** (generic, `P` invertible with invertible `P_c`, the matrix `P`
with row and column `v` replaced by those of the identity, and `b` the column of `P` at `v`
with `b_v = 0`): from `P P⁻¹ = I`,
* `inv_col`: off `v`, column `j` of `P⁻¹` is `P_c⁻¹ (e_j' - (P⁻¹)_vj b)` (`e_j'` = `e_j` with the
  `v` entry removed);
* `inv_diag`: `(P⁻¹)_vv (P_vv - bᵀ P_c⁻¹ b) = 1` (for symmetric `P`).

**F1** (`root_branch`, both branches at once with `τ = ±1`): with `g = h_v = (P̃⁻¹)_vv`,
`u = P_c⁻¹ b`, `q = bᵀu/D_v = q_A(ξ)`: `g D_v (1 - q) = 1`, `(P̃⁻¹)_jv = -g u_j`,
`(P̃⁻¹)_ij = (P_c⁻¹)_ij + g u_i u_j`; in physical form `t = D_v g = 1/α`, `G_vj = x_j`,
`G_vv G_ij = A_ij/(a²α) + x_i x_j`.
-/

@[expose] public section

namespace BiluLinial.Tight

namespace SecC

open Matrix

section Schur

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `P` with row and column `v` replaced by those of the identity (`precCore` for `P = P̃`). -/
def coreOf (P : Matrix V V ℝ) (v : V) : Matrix V V ℝ :=
  Matrix.of fun u w => if u = v ∨ w = v then (if u = w then 1 else 0) else P u w

/-- The column of `P` at `v`, with `v` entry `0` (`incCol` for `P = P̃`). -/
def colOf (P : Matrix V V ℝ) (v : V) : V → ℝ := fun w => if w = v then 0 else P w v

theorem sum_ite_eq_sub (g : V → ℝ) (v : V) :
    ∑ l, (if l = v then 0 else g l) = ∑ l, g l - g v := by
  have h : ∀ l, g l = (if l = v then g l else 0) + (if l = v then 0 else g l) := fun l => by
    split_ifs <;> simp
  conv_rhs => rw [Finset.sum_congr rfl fun l _ => h l]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ v g]
  simp

/-- Column `j` of `P⁻¹` off `v`, through the core. -/
theorem inv_col {P : Matrix V V ℝ} {v : V} (hP : IsUnit P.det) (hPc : IsUnit (coreOf P v).det)
    (j : V) :
    (fun l => if l = v then 0 else P⁻¹ l j) =
      (coreOf P v)⁻¹ *ᵥ fun l => (if l = v then 0 else if l = j then 1 else 0) -
        P⁻¹ v j * colOf P v l := by
  have hmul : (coreOf P v *ᵥ fun l => if l = v then 0 else P⁻¹ l j) =
      fun l => (if l = v then 0 else if l = j then 1 else 0) - P⁻¹ v j * colOf P v l := by
    funext k
    have hPP : ∑ l, P k l * P⁻¹ l j = if k = j then 1 else 0 := by
      have := congrFun (congrFun (Matrix.mul_nonsing_inv P hP) k) j
      rwa [mul_apply, one_apply] at this
    simp only [mulVec, dotProduct, coreOf, colOf, of_apply]
    by_cases hk : k = v
    · subst hk
      simp only [true_or, ite_true, mul_zero, sub_zero]
      refine Finset.sum_eq_zero fun l _ => ?_
      by_cases hl : l = k
      · simp [hl]
      · simp [hl, Ne.symm hl]
    · have e : ∀ l, (if k = v ∨ l = v then (if k = l then (1 : ℝ) else 0) else P k l) *
          (if l = v then 0 else P⁻¹ l j) = if l = v then 0 else P k l * P⁻¹ l j := by
        intro l
        by_cases hl : l = v
        · simp [hl]
        · simp [hk, hl]
      rw [Finset.sum_congr rfl fun l _ => e l, sum_ite_eq_sub, hPP, ite_eq_right hk,
        ite_eq_right hk]
      ring
  rw [← hmul, mulVec_mulVec, nonsing_inv_mul _ hPc, one_mulVec]

/-- The `(v, v)` entry of `P⁻¹` through the core. -/
theorem inv_diag {P : Matrix V V ℝ} {v : V} (hsym : ∀ k l, P k l = P l k) (hP : IsUnit P.det)
    (hPc : IsUnit (coreOf P v).det) :
    P⁻¹ v v * (P v v - colOf P v ⬝ᵥ ((coreOf P v)⁻¹ *ᵥ colOf P v)) = 1 := by
  have hc := inv_col hP hPc v
  have hr : (fun l => (if l = v then (0 : ℝ) else if l = v then 1 else 0) -
      P⁻¹ v v * colOf P v l) = (-P⁻¹ v v) • colOf P v := by
    funext l
    by_cases hl : l = v <;> simp [hl]
  rw [hr, mulVec_smul] at hc
  have hPP : ∑ l, P v l * P⁻¹ l v = 1 := by
    have := congrFun (congrFun (Matrix.mul_nonsing_inv P hP) v) v
    rwa [mul_apply, one_apply, if_pos rfl] at this
  have hsplit : ∑ l, P v l * P⁻¹ l v =
      P v v * P⁻¹ v v + colOf P v ⬝ᵥ (fun l => if l = v then 0 else P⁻¹ l v) := by
    have e : ∀ l, P v l * P⁻¹ l v =
        (if l = v then P v v * P⁻¹ v v else 0) + colOf P v l * (if l = v then 0 else P⁻¹ l v) := by
      intro l
      by_cases hl : l = v
      · subst hl; simp [colOf]
      · simp [hl, colOf, hsym v l]
    rw [Finset.sum_congr rfl fun l _ => e l, Finset.sum_add_distrib, Finset.sum_ite_eq']
    simp [dotProduct]
  rw [hc, dotProduct_smul, smul_eq_mul] at hsplit
  linarith

end Schur

section Root

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **F1, one branch** (`τ = ±1`, sources `y ≥ 0`, `P̃ ≻ 0`, `P̃_core ≻ 0`). -/
theorem root_branch {a τ : ℝ} (ha : a ≠ 0) (hτ : τ = 1 ∨ τ = -1) {y : V → ℝ}
    (hy : ∀ i, 0 ≤ y i) {S : Finset V} {v : V} (hv : v ∈ S) {σ : Config V}
    (hP : (precN G a τ y σ S).PosDef) (hPc : (precCore G a τ y σ S v).PosDef) :
    0 < starAlpha (rootMat G a τ y σ S v) (rootSigns G σ S v) ∧
      rootT G a τ y σ S v = 1 / starAlpha (rootMat G a τ y σ S v) (rootSigns G σ S v) ∧
      (∀ j : nbhd G S v, greenP G a τ y σ S v j =
        starRow (τ * a) (rootMat G a τ y σ S v) (rootSigns G σ S v) j) ∧
      (∀ i j : nbhd G S v, greenP G a τ y σ S v v * greenP G a τ y σ S i j =
        starMark (τ * a) (rootMat G a τ y σ S v) (rootSigns G σ S v) i j) := by
  have hτ2 : τ ^ 2 = 1 := by rcases hτ with h | h <;> simp [h]
  have hττ : τ * τ = 1 := by rw [← sq]; exact hτ2
  have hτa : τ * a ≠ 0 := mul_ne_zero (by rcases hτ with h | h <;> simp [h]) ha
  have hD : 0 < diagD G a y S v := diagD_pos G a hy S v
  have hyv : Real.sqrt (y v) * Real.sqrt (y v) = y v := Real.mul_self_sqrt (hy v)
  have hPu : IsUnit (precN G a τ y σ S).det := (isUnit_iff_isUnit_det _).mp hP.isUnit
  have hPcu : IsUnit (coreOf (precN G a τ y σ S) v).det :=
    (isUnit_iff_isUnit_det _).mp hPc.isUnit
  have hsym : ∀ k l, precN G a τ y σ S k l = precN G a τ y σ S l k := fun k l => by
    simpa using (precN_isHermitian' G a τ y σ S).apply l k
  have hinvsym : ∀ k l, (precN G a τ y σ S)⁻¹ k l = (precN G a τ y σ S)⁻¹ l k := fun k l => by
    simpa using (precN_isHermitian' G a τ y σ S).inv.apply l k
  have hPvv : precN G a τ y σ S v v = diagD G a y S v := by simp [precN, hv]
  have hcol : ∀ j, (fun l => if l = v then 0 else (precN G a τ y σ S)⁻¹ l j) =
      (precCore G a τ y σ S v)⁻¹ *ᵥ fun l => (if l = v then 0 else if l = j then 1 else 0) -
        (precN G a τ y σ S)⁻¹ v j * incCol G a τ y σ S v l := fun j => inv_col hPu hPcu j
  have hdiag : (precN G a τ y σ S)⁻¹ v v * (diagD G a y S v - incCol G a τ y σ S v ⬝ᵥ
      ((precCore G a τ y σ S v)⁻¹ *ᵥ incCol G a τ y σ S v)) = 1 := by
    have h := inv_diag hsym hPu hPcu
    rw [hPvv] at h
    exact h
  have hg0 : 0 < (precN G a τ y σ S)⁻¹ v v := hP.inv.diag_pos
  obtain ⟨g, hg⟩ : ∃ g, g = (precN G a τ y σ S)⁻¹ v v := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : V → ℝ,
      u = (precCore G a τ y σ S v)⁻¹ *ᵥ incCol G a τ y σ S v := ⟨_, rfl⟩
  rw [← hg] at hdiag hg0
  rw [← hu] at hdiag
  -- the root energy
  have hα : starAlpha (rootMat G a τ y σ S v) (rootSigns G σ S v) =
      1 - incCol G a τ y σ S v ⬝ᵥ u / diagD G a y S v := by
    rw [starAlpha, ← qRoot_eq_qForm G hτ2 hy σ hv, qRoot, ← hu]
  have hgα : g * starAlpha (rootMat G a τ y σ S v) (rootSigns G σ S v) = 1 / diagD G a y S v := by
    rw [hα, eq_div_iff hD.ne']
    field_simp
    linarith
  have hαpos : 0 < starAlpha (rootMat G a τ y σ S v) (rootSigns G σ S v) := by
    by_contra h
    push Not at h
    have : g * starAlpha (rootMat G a τ y σ S v) (rootSigns G σ S v) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hg0.le h
    have : 0 < 1 / diagD G a y S v := by positivity
    linarith
  -- the column at `v` and the core block
  have hcolv : ∀ j, j ≠ v → (precN G a τ y σ S)⁻¹ j v = -g * u j := by
    intro j hj
    have h := congrFun (hcol v) j
    simp only [hj, if_false] at h
    rw [h]
    have hr : (fun l => (if l = v then (0 : ℝ) else if l = v then 1 else 0) -
        (precN G a τ y σ S)⁻¹ v v * incCol G a τ y σ S v l) = (-g) • incCol G a τ y σ S v := by
      funext l
      by_cases hl : l = v
      · subst hl; simp [incCol]
      · simp [hl, hg]
    rw [hr, mulVec_smul, Pi.smul_apply, smul_eq_mul, hu]
  have hblock : ∀ i j, i ≠ v → j ≠ v →
      (precN G a τ y σ S)⁻¹ i j = (precCore G a τ y σ S v)⁻¹ i j + g * u i * u j := by
    intro i j hi hj
    have h := congrFun (hcol j) i
    simp only [hi, if_false] at h
    rw [h]
    have hr : (fun l => (if l = v then (0 : ℝ) else if l = j then 1 else 0) -
        (precN G a τ y σ S)⁻¹ v j * incCol G a τ y σ S v l) =
        (fun l => if l = j then 1 else 0) - ((precN G a τ y σ S)⁻¹ v j) • incCol G a τ y σ S v := by
      funext l
      by_cases hl : l = v
      · subst hl; simp [Ne.symm hj, incCol]
      · simp [hl]
    rw [hr, mulVec_sub, mulVec_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hinvsym v j,
      hcolv j hj, ← hu]
    have he : ((precCore G a τ y σ S v)⁻¹ *ᵥ fun l => if l = j then (1 : ℝ) else 0) i =
        (precCore G a τ y σ S v)⁻¹ i j := by
      simp [mulVec, dotProduct]
    rw [he]
    ring
  -- physical forms
  have hNv : ∀ j : nbhd G S v, (j : V) ≠ v := fun j =>
    (G.ne_of_adj (Finset.mem_filter.1 j.2).2).symm
  have hGvv : greenP G a τ y σ S v v = y v * g := by rw [greenP_self G hy σ S v, hg]; rfl
  have hGvj : ∀ j : nbhd G S v,
      greenP G a τ y σ S v j = -(Real.sqrt (y v) * g * u j * Real.sqrt (y j)) := by
    intro j
    simp only [greenP]
    rw [hinvsym v j, hcolv j (hNv j)]
    ring
  -- `u` through the star vector
  have hAx : ∀ j : nbhd G S v, (rootMat G a τ y σ S v *ᵥ rootSigns G σ S v) j * (τ * a) =
      a ^ 2 / diagD G a y S v * Real.sqrt (y v) * Real.sqrt (y j) * u j := by
    intro j
    have hu' : u j = τ * a * Real.sqrt (y v) * ∑ i : nbhd G S v,
        (precCore G a τ y σ S v)⁻¹ j i * (Real.sqrt (y i) * sgn σ v i) := by
      rw [hu]
      simp only [mulVec, dotProduct, incCol_eq_ite G a τ y σ hv, mul_ite, mul_zero,
        Finset.sum_ite_mem, Finset.univ_inter]
      rw [← Finset.sum_coe_sort (nbhd G S v), Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hAx' : (rootMat G a τ y σ S v *ᵥ rootSigns G σ S v) j =
        a ^ 2 * y v / diagD G a y S v * Real.sqrt (y j) * ∑ i : nbhd G S v,
          (precCore G a τ y σ S v)⁻¹ j i * (Real.sqrt (y i) * sgn σ v i) := by
      simp only [mulVec, dotProduct, rootMat, coreGreen, of_apply, rootSigns, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hAx', hu']
    rw [show a ^ 2 / diagD G a y S v * Real.sqrt (y v) * Real.sqrt (y j) *
        (τ * a * Real.sqrt (y v) * ∑ i : nbhd G S v,
          (precCore G a τ y σ S v)⁻¹ j i * (Real.sqrt (y i) * sgn σ v i)) =
        a ^ 2 / diagD G a y S v * (Real.sqrt (y v) * Real.sqrt (y v)) * Real.sqrt (y j) *
          (τ * a) * ∑ i : nbhd G S v,
            (precCore G a τ y σ S v)⁻¹ j i * (Real.sqrt (y i) * sgn σ v i) by ring, hyv]
    ring
  have hrow : ∀ j : nbhd G S v, greenP G a τ y σ S v j =
      starRow (τ * a) (rootMat G a τ y σ S v) (rootSigns G σ S v) j := by
    intro j
    rw [hGvj, starRow, eq_div_iff (mul_ne_zero hτa hαpos.ne'), neg_mul, neg_inj]
    apply mul_right_cancel₀ hτa
    rw [hAx j]
    calc Real.sqrt (y v) * g * u j * Real.sqrt (y j) *
          (τ * a * starAlpha (rootMat G a τ y σ S v) (rootSigns G σ S v)) * (τ * a)
        = Real.sqrt (y v) * Real.sqrt (y j) * u j * a ^ 2 * (τ * τ) *
            (g * starAlpha (rootMat G a τ y σ S v) (rootSigns G σ S v)) := by ring
      _ = a ^ 2 / diagD G a y S v * Real.sqrt (y v) * Real.sqrt (y j) * u j := by
          rw [hττ, hgα]; ring
  refine ⟨hαpos, ?_, hrow, ?_⟩
  · -- `t = D g = 1/α`
    rw [rootT, eq_div_iff hαpos.ne']
    have h1 : hN G a τ y σ S v = g := by rw [hg]; rfl
    rw [h1]
    have := hgα
    field_simp at this ⊢
    linarith
  · intro i j
    rw [starMark, starCore, ← hrow i, ← hrow j, hGvv, hGvj i, hGvj j]
    have hij : greenP G a τ y σ S i j = Real.sqrt (y i) *
        ((precCore G a τ y σ S v)⁻¹ i j + g * u i * u j) * Real.sqrt (y j) := by
      simp only [greenP]
      rw [hblock i j (hNv i) (hNv j)]
    rw [hij]
    have hA : rootMat G a τ y σ S v i j = a ^ 2 * y v / diagD G a y S v *
        (Real.sqrt (y i) * (precCore G a τ y σ S v)⁻¹ i j * Real.sqrt (y j)) := rfl
    rw [hA, mul_pow, hτ2, one_mul]
    have hαinv : starAlpha (rootMat G a τ y σ S v) (rootSigns G σ S v) =
        1 / (g * diagD G a y S v) := by
      rw [eq_div_iff (mul_pos hg0 hD).ne']
      have := hgα
      field_simp at this
      linarith
    rw [hαinv]
    have hga : g ≠ 0 := hg0.ne'
    field_simp
    rw [Real.sq_sqrt (hy v)]
    ring

/-- The Frobenius estimate from the mark identities `a² c_ij = t A_ij + a² x_i x_j`. -/
theorem frob_of_marks {ι : Type*} [Fintype ι] (a t : ℝ) (A : Matrix ι ι ℝ)
    (hA : ∀ i j, A i j = A j i) (x : ι → ℝ) (c : ι → ι → ℝ)
    (hc : ∀ i j, a ^ 2 * c i j = t * A i j + a ^ 2 * (x i * x j)) :
    ∑ i, ∑ j, (a ^ 2 * c i j) ^ 2 ≤ 2 * t ^ 2 * (A * A).trace + 2 * (a ^ 2 * ∑ j, x j ^ 2) ^ 2 := by
  have htr : (A * A).trace = ∑ i, ∑ j, A i j ^ 2 := by
    simp only [trace, diag, mul_apply]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hA j i]; ring
  have hsq : (a ^ 2 * ∑ j, x j ^ 2) ^ 2 = ∑ i, ∑ j, (a ^ 2) ^ 2 * (x i ^ 2 * x j ^ 2) := by
    rw [mul_pow, sq (∑ j, x j ^ 2), Finset.sum_mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
  rw [htr, hsq]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  rw [hc]
  nlinarith [sq_nonneg (t * A i j - a ^ 2 * (x i * x j))]

/-- The Frobenius bound in one branch. -/
theorem frob_branch {a τ : ℝ} (ha : a ≠ 0) (hτ : τ = 1 ∨ τ = -1) {y : V → ℝ}
    (hy : ∀ i, 0 ≤ y i) {S : Finset V} {v : V} (hv : v ∈ S) {σ : Config V}
    (hP : (precN G a τ y σ S).PosDef) (hPc : (precCore G a τ y σ S v).PosDef) :
    a ^ 4 * (greenP G a τ y σ S v v ^ 2 *
        ∑ i ∈ nbhd G S v, ∑ j ∈ nbhd G S v, greenP G a τ y σ S i j ^ 2) ≤
      2 * rootT G a τ y σ S v ^ 2 * (rootMat G a τ y σ S v * rootMat G a τ y σ S v).trace +
        2 * (a ^ 2 * ∑ j ∈ nbhd G S v, greenP G a τ y σ S v j ^ 2) ^ 2 := by
  obtain ⟨hα, ht, hrow, hmark⟩ := root_branch G ha hτ hy hv hP hPc
  have hτ2 : τ ^ 2 = 1 := by rcases hτ with h | h <;> simp [h]
  have key := frob_of_marks a (rootT G a τ y σ S v) (rootMat G a τ y σ S v)
    (fun i j => rootMat_apply_comm G a τ y σ S v i j)
    (fun j => starRow (τ * a) (rootMat G a τ y σ S v) (rootSigns G σ S v) j)
    (fun i j => starMark (τ * a) (rootMat G a τ y σ S v) (rootSigns G σ S v) i j)
    (fun i j => by
      rw [starMark, starCore, ht, mul_pow, hτ2, one_mul]
      field_simp)
  have hL : a ^ 4 * (greenP G a τ y σ S v v ^ 2 *
      ∑ i ∈ nbhd G S v, ∑ j ∈ nbhd G S v, greenP G a τ y σ S i j ^ 2) =
      ∑ i : nbhd G S v, ∑ j : nbhd G S v,
        (a ^ 2 * starMark (τ * a) (rootMat G a τ y σ S v) (rootSigns G σ S v) i j) ^ 2 := by
    rw [← Finset.sum_coe_sort (nbhd G S v), Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_coe_sort (nbhd G S v), Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hmark i j]
    ring
  have hR : ∑ j ∈ nbhd G S v, greenP G a τ y σ S v j ^ 2 =
      ∑ j : nbhd G S v, starRow (τ * a) (rootMat G a τ y σ S v) (rootSigns G σ S v) j ^ 2 := by
    rw [← Finset.sum_coe_sort (nbhd G S v)]
    exact Finset.sum_congr rfl fun j _ => by rw [hrow j]
  rw [hL, hR]
  exact key

end Root

section Corollaries

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable {d p : ℕ}

/-- The four positive-definiteness facts of a supported signing. -/
theorem posDef_of_wt_ne_zero' (hp : 1 ≤ p) {a : ℝ} {yp ym : V → ℝ} (hyp : ∀ i, 0 ≤ yp i)
    (hym : ∀ i, 0 ≤ ym i) {S : Finset V} {v : V} (hv : v ∈ S) {σ : Config V}
    (hσ : wt G p a yp ym σ S ≠ 0) :
    (precN G a 1 yp σ S).PosDef ∧ (precN G a (-1) ym σ S).PosDef ∧
      (precCore G a 1 yp σ S v).PosDef ∧ (precCore G a (-1) ym σ S v).PosDef := by
  have hPp : (precN G a 1 yp σ S).PosDef := by
    by_contra hc
    exact hσ (by simp [wt, hc])
  have hPm : (precN G a (-1) ym σ S).PosDef := by
    by_contra hc
    exact hσ (by simp [wt, hc])
  obtain ⟨hc1, hc2⟩ := posDef_of_wtCore_ne_zero G (wtCore_ne_zero_of_wt G hp hyp hym hv hσ)
  exact ⟨hPp, hPm, hc1, hc2⟩

/-- **(F1)** at a supported signing (`W(σ) ≠ 0`), with `ξ = ξ(σ)`, `α = 1 - q_A(ξ) > 0`,
`β = 1 - q_B(ξ) > 0`: `t₊ = 1/α`, `t₋ = 1/β`, `G⁺_vj = -(Aξ)_j/(aα)`, `G⁻_vj = (Bξ)_j/(aβ)`
for `j ∈ N`, and `G⁺_vv G⁺_ij = A_ij/(a²α) + G⁺_vi G⁺_vj` for `i, j ∈ N` (`root_branch`). -/
theorem root_F1 (hR : TRegime d p) {S : Finset V} {yp ym : V → ℝ} (hyp : ∀ i, 0 ≤ yp i)
    (hym : ∀ i, 0 ≤ ym i) {v : V} (hv : v ∈ S) {σ : Config V}
    (hσ : wt G p (aOf d p) yp ym σ S ≠ 0) :
    let A := rootMat G (aOf d p) 1 yp σ S v
    let B := rootMat G (aOf d p) (-1) ym σ S v
    let ξ := rootSigns G σ S v
    0 < starAlpha A ξ ∧ 0 < starAlpha B ξ ∧
      rootT G (aOf d p) 1 yp σ S v = 1 / starAlpha A ξ ∧
      rootT G (aOf d p) (-1) ym σ S v = 1 / starAlpha B ξ ∧
      (∀ j : nbhd G S v, greenP G (aOf d p) 1 yp σ S v j = starRow (aOf d p) A ξ j) ∧
      (∀ j : nbhd G S v, greenP G (aOf d p) (-1) ym σ S v j = starRow (-aOf d p) B ξ j) ∧
      (∀ i j : nbhd G S v, greenP G (aOf d p) 1 yp σ S v v * greenP G (aOf d p) 1 yp σ S i j =
        starMark (aOf d p) A ξ i j) ∧
      (∀ i j : nbhd G S v,
        greenP G (aOf d p) (-1) ym σ S v v * greenP G (aOf d p) (-1) ym σ S i j =
          starMark (-aOf d p) B ξ i j) := by
  have hp1 : 1 ≤ p := le_trans (by norm_num) hR.two_le_p
  obtain ⟨hPp, hPm, hc1, hc2⟩ := posDef_of_wt_ne_zero' G hp1 hyp hym hv hσ
  have ha := hR.aOf_pos.ne'
  obtain ⟨h1, h2, h3, h4⟩ := root_branch G ha (Or.inl rfl) hyp hv hPp hc1
  obtain ⟨h5, h6, h7, h8⟩ := root_branch G ha (Or.inr rfl) hym hv hPm hc2
  simp only [one_mul, neg_one_mul] at h3 h4 h7 h8
  exact ⟨h1, h5, h2, h6, h3, h7, h4, h8⟩

/-- At a supported signing, `F(ξ) = a² Φ(ξ) 𝓡_v(σ)` (source line 141): `rowNum_line` at `t = 0`
and (F1). -/
theorem rowNum_eq (hR : TRegime d p) {S : Finset V} {yp ym : V → ℝ} (hyp : ∀ i, 0 ≤ yp i)
    (hym : ∀ i, 0 ≤ ym i) {v : V} (hv : v ∈ S) {σ : Config V}
    (hσ : wt G p (aOf d p) yp ym σ S ≠ 0) :
    rowNum p (rootMat G (aOf d p) 1 yp σ S v) (rootMat G (aOf d p) (-1) ym σ S v)
        (rootSigns G σ S v) =
      aOf d p ^ 2 * starPhi p (rootMat G (aOf d p) 1 yp σ S v)
          (rootMat G (aOf d p) (-1) ym σ S v) (rootSigns G σ S v) *
        (((p : ℝ) - 1) * ∑ j ∈ nbhd G S v, greenP G (aOf d p) 1 yp σ S v j ^ 2 -
          p * ∑ j ∈ nbhd G S v,
            greenP G (aOf d p) 1 yp σ S v j * greenP G (aOf d p) (-1) ym σ S v j) := by
  obtain ⟨hα, hβ, -, -, hrp, hrm, -, -⟩ := root_F1 G hR hyp hym hv hσ
  have hp2 : 2 ≤ p := hR.two_le_p
  have ha := hR.aOf_pos.ne'
  have hAs : (rootMat G (aOf d p) 1 yp σ S v).IsSymm := by
    ext i j; exact rootMat_apply_comm G _ 1 yp σ S v j i
  have hBs : (rootMat G (aOf d p) (-1) ym σ S v).IsSymm := by
    ext i j; exact rootMat_apply_comm G _ (-1) ym σ S v j i
  have hΦ : starPhi p (rootMat G (aOf d p) 1 yp σ S v) (rootMat G (aOf d p) (-1) ym σ S v)
      (rootSigns G σ S v) = starAlpha (rootMat G (aOf d p) 1 yp σ S v) (rootSigns G σ S v) ^ p *
        starAlpha (rootMat G (aOf d p) (-1) ym σ S v) (rootSigns G σ S v) ^ p := by
    simp only [starPhi, clipF]
    change max (starAlpha _ _) 0 ^ p * max (starAlpha _ _) 0 ^ p = _
    rw [max_eq_left hα.le, max_eq_left hβ.le]
  rcases isEmpty_or_nonempty (nbhd G S v) with hN | hne
  · have h0 : nbhd G S v = ∅ := Finset.isEmpty_coe_sort.mp hN
    simp [rowNum, qForm, dotProduct, h0]
  · obtain ⟨i⟩ := hne
    have hline := rowNum_line (p := p) hp2 ha hAs hBs hα hβ i (t := 0) (by simp) (by simp)
    simp only [zero_smul, add_zero, mul_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, one_pow, mul_one] at hline
    have hS1 : ∑ j ∈ nbhd G S v, greenP G (aOf d p) 1 yp σ S v j ^ 2 =
        ∑ j : nbhd G S v,
          starRow (aOf d p) (rootMat G (aOf d p) 1 yp σ S v) (rootSigns G σ S v) j ^ 2 := by
      rw [← Finset.sum_coe_sort (nbhd G S v)]
      exact Finset.sum_congr rfl fun j _ => by rw [hrp j]
    have hS2 : ∑ j ∈ nbhd G S v,
        greenP G (aOf d p) 1 yp σ S v j * greenP G (aOf d p) (-1) ym σ S v j =
        ∑ j : nbhd G S v,
          starRow (aOf d p) (rootMat G (aOf d p) 1 yp σ S v) (rootSigns G σ S v) j *
            starRow (-aOf d p) (rootMat G (aOf d p) (-1) ym σ S v) (rootSigns G σ S v) j := by
      rw [← Finset.sum_coe_sort (nbhd G S v)]
      exact Finset.sum_congr rfl fun j _ => by rw [hrp j, hrm j]
    rw [hline, hΦ, hS1, hS2]
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring

/-- **Frobenius bound** (source lines 1135–1140, exact constants `2, 2`): at a supported
signing, `a⁴ G_vv² ‖G[N,N]‖_F² ≤ 2 t₊² tr A² + 2 (a² Σ_N G_vj²)²`, both branches
(`frob_branch`). -/
theorem frob_root_le (hR : TRegime d p) {S : Finset V} {yp ym : V → ℝ} (hyp : ∀ i, 0 ≤ yp i)
    (hym : ∀ i, 0 ≤ ym i) {v : V} (hv : v ∈ S) {σ : Config V}
    (hσ : wt G p (aOf d p) yp ym σ S ≠ 0) :
    aOf d p ^ 4 * (greenP G (aOf d p) 1 yp σ S v v ^ 2 *
        ∑ i ∈ nbhd G S v, ∑ j ∈ nbhd G S v, greenP G (aOf d p) 1 yp σ S i j ^ 2) ≤
      2 * rootT G (aOf d p) 1 yp σ S v ^ 2 *
          (rootMat G (aOf d p) 1 yp σ S v * rootMat G (aOf d p) 1 yp σ S v).trace +
        2 * (aOf d p ^ 2 * ∑ j ∈ nbhd G S v, greenP G (aOf d p) 1 yp σ S v j ^ 2) ^ 2 ∧
    aOf d p ^ 4 * (greenP G (aOf d p) (-1) ym σ S v v ^ 2 *
        ∑ i ∈ nbhd G S v, ∑ j ∈ nbhd G S v, greenP G (aOf d p) (-1) ym σ S i j ^ 2) ≤
      2 * rootT G (aOf d p) (-1) ym σ S v ^ 2 *
          (rootMat G (aOf d p) (-1) ym σ S v * rootMat G (aOf d p) (-1) ym σ S v).trace +
        2 * (aOf d p ^ 2 * ∑ j ∈ nbhd G S v, greenP G (aOf d p) (-1) ym σ S v j ^ 2) ^ 2 := by
  have hp1 : 1 ≤ p := le_trans (by norm_num) hR.two_le_p
  obtain ⟨hPp, hPm, hc1, hc2⟩ := posDef_of_wt_ne_zero' G hp1 hyp hym hv hσ
  have ha := hR.aOf_pos.ne'
  exact ⟨frob_branch G ha (Or.inl rfl) hyp hv hPp hc1, frob_branch G ha (Or.inr rfl) hym hv hPm hc2⟩

end Corollaries

end SecC

end BiluLinial.Tight
