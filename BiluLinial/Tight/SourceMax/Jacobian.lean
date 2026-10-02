/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.Ctx

/-!
# The source Jacobian `DZ = -D_y⁻¹ 𝓑 D_y⁻¹`

Blueprint node `D-SM-jac` (source Section 1.1, Lemma "Deletion and source differentiation", first
display).

**Sketch.** `Z_u(y) = (1 + Σ_{m ∈ N_S(u)} c(a² y_u y_m))/y_u` with `c(x) = (√(1+4x) - 1)/2`,
`c'(x) = 1/√(1+4x) = 1/(1 + 2c)`. Along `y_j ↦ y_j - t` at `t = 0` (`u, j ∈ S`, `y_u, y_j > 0`):
* `u = j`: derivative `(1 + Σ_m [c - c(1+c)/(1+2c)])/y_j² = (1 + Σ_m c²/(1+2c))/y_j²`;
* `u ∼ j`: derivative `-a²/(1+2c_uj) = -c(1+c)/((1+2c) y_u y_j)`;
* otherwise `0`.
With `τ = c/(1+c)`: `τ²/(1-τ²) = c²/(1+2c)`, `τ/(1-τ²) = c(1+c)/(1+2c)`, so the derivative is
`𝓑_uj/(y_u y_j)` (`𝓑 = walkB`). Uses `c(1+c) = a² y_u y_m`, valid since `a² y_u y_m ≥ 0`.
-/

@[expose] public section

namespace BiluLinial.Tight

open Matrix

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem cRoot_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ cRoot x := by
  unfold cRoot
  have h := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 1 + 4 * x by linarith)
  rw [Real.sqrt_one] at h
  linarith

theorem cRoot_mul_one_add_self {x : ℝ} (hx : 0 ≤ x) : cRoot x * (1 + cRoot x) = x := by
  unfold cRoot
  have h := Real.sq_sqrt (show 0 ≤ 1 + 4 * x by linarith)
  linear_combination h / 4

/-- `c'(x) = 1/(1 + 2c(x))`. -/
theorem hasDerivAt_cRoot {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt cRoot (1 / (1 + 2 * cRoot x)) x := by
  have h1 : 0 < 1 + 4 * x := by linarith
  have hs : HasDerivAt (fun x => 1 + 4 * x) 4 x := by
    simpa using ((hasDerivAt_id x).const_mul 4).const_add 1
  have h2 := (((Real.hasDerivAt_sqrt h1.ne').comp x hs).sub_const 1).div_const 2
  have hpos : 0 < Real.sqrt (1 + 4 * x) := Real.sqrt_pos.2 h1
  have e : 1 / (1 + 2 * cRoot x) = 1 / (2 * Real.sqrt (1 + 4 * x)) * 4 / 2 := by
    rw [show 1 + 2 * cRoot x = Real.sqrt (1 + 4 * x) by unfold cRoot; ring]
    field_simp
    ring
  rw [e]
  exact h2

/-- `τ²/(1-τ²) = c²/(1+2c)` and `τ/(1-τ²) = c(1+c)/(1+2c)` for `τ = c/(1+c)`, `c ≥ 0`. -/
theorem tau_identities {c : ℝ} (hc : 0 ≤ c) :
    (c / (1 + c)) ^ 2 / (1 - (c / (1 + c)) ^ 2) = c ^ 2 / (1 + 2 * c) ∧
      (c / (1 + c)) / (1 - (c / (1 + c)) ^ 2) = c * (1 + c) / (1 + 2 * c) := by
  have h1 : 1 + c ≠ 0 := by linarith
  have h2 : 1 + 2 * c ≠ 0 := by linarith
  have h3 : 1 - (c / (1 + c)) ^ 2 = (1 + 2 * c) / (1 + c) ^ 2 := by
    field_simp
    ring
  rw [h3]
  constructor
  · field_simp
  · field_simp

omit [Fintype V] in
/-- `D-SM-jac`: `∂_t Z_u(y - t e_j)|_{t=0} = 𝓑_uj/(y_u y_j)` for positive sources `u, j ∈ S`. -/
theorem hasDerivAt_precZ_update {a : ℝ} {y : V → ℝ} (hy : ∀ u, 0 ≤ y u) {S : Finset V} {u j : V}
    (hu : u ∈ S) (hyu : 0 < y u) (hj : j ∈ S) (hyj : 0 < y j) :
    HasDerivAt (fun t => precZ G a (Function.update y j (y j - t)) S u)
      (walkB G a y S u j / (y u * y j)) 0 := by
  classical
  let yt : ℝ → V → ℝ := fun t => Function.update y j (y j - t)
  have hy0 : yt 0 = y := by simp [yt]
  let e : V → ℝ := fun v => if v = j then 1 else 0
  have hyv : ∀ v, HasDerivAt (fun t => yt t v) (-e v) 0 := by
    intro v
    by_cases hv : v = j
    · subst hv
      simp only [yt, e, Function.update_self, ite_true]
      exact (hasDerivAt_id (0 : ℝ)).const_sub (y v)
    · simp only [yt, e, Function.update_of_ne hv, hv, ite_false, neg_zero]
      exact hasDerivAt_const _ _
  have hg : ∀ m, HasDerivAt (fun t => a ^ 2 * yt t u * yt t m)
      (a ^ 2 * (-e u) * y m + a ^ 2 * y u * (-e m)) 0 := by
    intro m
    have h := ((hyv u).const_mul (a ^ 2)).mul (hyv m)
    simp only [hy0] at h
    exact h
  have hc : ∀ m, HasDerivAt (fun t => cRoot (a ^ 2 * yt t u * yt t m))
      (1 / (1 + 2 * cEdge a y u m) * (a ^ 2 * (-e u) * y m + a ^ 2 * y u * (-e m))) 0 := by
    intro m
    have h0 : 0 ≤ a ^ 2 * y u * y m := mul_nonneg (mul_nonneg (sq_nonneg a) (hy u)) (hy m)
    have hcR : HasDerivAt cRoot (1 / (1 + 2 * cEdge a y u m)) (a ^ 2 * yt 0 u * yt 0 m) := by
      rw [hy0]
      exact hasDerivAt_cRoot h0
    exact hcR.comp (0 : ℝ) (hg m)
  have hD : HasDerivAt (fun t => diagD G a (yt t) S u)
      (∑ m ∈ nbhd G S u, 1 / (1 + 2 * cEdge a y u m) *
        (a ^ 2 * (-e u) * y m + a ^ 2 * y u * (-e m))) 0 :=
    (HasDerivAt.fun_sum fun m (_ : m ∈ nbhd G S u) => hc m).const_add 1
  have hyu0 : yt 0 u ≠ 0 := by
    rw [hy0]
    exact hyu.ne'
  have hZ := hD.div (hyv u) hyu0
  simp only [hy0] at hZ
  refine hZ.congr_deriv ?_
  have hcm : ∀ m, cEdge a y u m * (1 + cEdge a y u m) = a ^ 2 * y u * y m := fun m =>
    cRoot_mul_one_add_self (mul_nonneg (mul_nonneg (sq_nonneg a) (hy u)) (hy m))
  have hc0 : ∀ m, 0 ≤ cEdge a y u m := fun m =>
    cRoot_nonneg (mul_nonneg (mul_nonneg (sq_nonneg a) (hy u)) (hy m))
  by_cases huj : u = j
  · subst huj
    have heu : e u = 1 := by simp [e]
    have hem : ∀ m ∈ nbhd G S u, e m = 0 := fun m hm => by
      have : G.Adj u m := (Finset.mem_filter.1 hm).2
      simp [e, this.ne']
    have hterm : ∀ m ∈ nbhd G S u,
        1 / (1 + 2 * cEdge a y u m) * (a ^ 2 * (-e u) * y m + a ^ 2 * y u * (-e m)) * y u +
          cEdge a y u m = τEdge a y u m ^ 2 / (1 - τEdge a y u m ^ 2) := by
      intro m hm
      have h12 : 1 + 2 * cEdge a y u m ≠ 0 := by linarith [hc0 m]
      rw [heu, hem m hm, τEdge, (tau_identities (hc0 m)).1]
      have e1 : 1 / (1 + 2 * cEdge a y u m) * (a ^ 2 * (-1) * y m + a ^ 2 * y u * (-0)) * y u =
          -(a ^ 2 * y u * y m) / (1 + 2 * cEdge a y u m) := by
        field_simp
        ring
      rw [e1, ← hcm m, eq_div_iff h12, add_mul, div_mul_cancel₀ _ h12]
      ring
    have hnum : (∑ m ∈ nbhd G S u, 1 / (1 + 2 * cEdge a y u m) *
          (a ^ 2 * (-e u) * y m + a ^ 2 * y u * (-e m))) * y u - diagD G a y S u * (-e u) =
        1 + ∑ m ∈ nbhd G S u, τEdge a y u m ^ 2 / (1 - τEdge a y u m ^ 2) := by
      rw [← Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.sum_mul, heu, diagD]
      ring
    rw [hnum]
    simp only [walkB, of_apply, ite_true, hu]
    ring
  · have heu : e u = 0 := by simp [e, huj]
    by_cases hadj : G.Adj u j
    · have hjN : j ∈ nbhd G S u := Finset.mem_filter.2 ⟨hj, hadj⟩
      have hsum : (∑ m ∈ nbhd G S u, 1 / (1 + 2 * cEdge a y u m) *
          (a ^ 2 * (-e u) * y m + a ^ 2 * y u * (-e m))) =
          1 / (1 + 2 * cEdge a y u j) * (a ^ 2 * (-e u) * y j + a ^ 2 * y u * (-e j)) := by
        refine Finset.sum_eq_single_of_mem j hjN fun m _ hmj => ?_
        simp [e, hmj, heu]
      have hej : e j = 1 := by simp [e]
      have h12 : 1 + 2 * cEdge a y u j ≠ 0 := by linarith [hc0 j]
      have hτ : τEdge a y u j / (1 - τEdge a y u j ^ 2) =
          a ^ 2 * y u * y j / (1 + 2 * cEdge a y u j) := by
        rw [τEdge, (tau_identities (hc0 j)).2, hcm j]
      rw [hsum, heu, hej]
      simp only [walkB, of_apply, huj, ite_false, hu, hj, hadj, and_self, ite_true, hτ]
      field_simp
      ring
    · have hsum : (∑ m ∈ nbhd G S u, 1 / (1 + 2 * cEdge a y u m) *
          (a ^ 2 * (-e u) * y m + a ^ 2 * y u * (-e m))) = 0 := by
        refine Finset.sum_eq_zero fun m hm => ?_
        have hmj : m ≠ j := by
          rintro rfl
          exact hadj (Finset.mem_filter.1 hm).2
        simp [e, hmj, heu]
      rw [hsum, heu]
      simp only [walkB, of_apply, huj, ite_false, hadj, and_false]
      ring

end BiluLinial.Tight
