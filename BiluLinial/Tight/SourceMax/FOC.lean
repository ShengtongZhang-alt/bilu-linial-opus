/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SourceMax.Deriv

/-!
# First-order condition at a source maximum

Blueprint node `D-SM-foc` (source Section 1.1, proof of Lemma "Source maximum and moments":
"decreasing each positive source is feasible, so `(DZ)ᵀ C ≥ k m_k y_v^{k-1} e_v`").

**Sketch.** If `y⁺` maximizes `m(y) = E_y (h_i^+)^k` (second source fixed) over the cube
`[0, c]^V`, then for `j ∈ S⁺` and `0 < t ≤ y_j` the point `y - t e_j` lies in the cube, so the
right slopes of `t ↦ m(y - t e_j)` at `0` are `≤ 0` and the derivative of `hasDerivAt_moment` is
`≤ 0`. Multiplying it by `y_i^k y_j > 0` and using `1_{i=j} y_j = 1_{i=j} y_i` gives
`Σ_{l ∈ S⁺} 𝓑_lj C_l / y_l + 1_{i=j} k m y_i^k ≤ 0`.
-/

@[expose] public section

namespace BiluLinial.Tight

open Matrix

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- `D-SM-foc`: the first-order condition at a maximizer of a moment over a source cube. -/
theorem foc_of_max {p k : ℕ} (hk : k + 2 ≤ p) {a c : ℝ} {yp ym : V → ℝ} (hcube : InCube c yp)
    {S : Finset V} (hZ : 0 < Zw G p a yp ym S) {i j : V} (hi : i ∈ posSrc S yp)
    (hj : j ∈ posSrc S yp)
    (hmax : ∀ y, InCube c y → lawE G p a y ym S (fun σ => hN G a 1 y σ S i ^ k) ≤
      lawE G p a yp ym S (fun σ => hN G a 1 yp σ S i ^ k)) :
    ∑ l ∈ posSrc S yp, walkB G a yp S l j * (momC G p a yp ym S k i l / yp l) +
        (if i = j then
          (k : ℝ) * lawE G p a yp ym S (fun σ => hN G a 1 yp σ S i ^ k) * yp i ^ k else 0) ≤
      0 := by
  have hy : ∀ u, 0 ≤ yp u := fun u => (hcube u).1
  have hyi : 0 < yp i := (Finset.mem_filter.1 hi).2
  have hyj : 0 < yp j := (Finset.mem_filter.1 hj).2
  have hd := hasDerivAt_moment G hk hy hZ hi hj
  set m := lawE G p a yp ym S (fun σ => hN G a 1 yp σ S i ^ k) with hm
  set f : ℝ → ℝ := fun t => lawE G p a (Function.update yp j (yp j - t)) ym S
    (fun σ => hN G a 1 (Function.update yp j (yp j - t)) σ S i ^ k) with hf
  set D := (∑ l ∈ posSrc S yp, walkB G a yp S l j / (yp l * yp j) * momC G p a yp ym S k i l) /
      yp i ^ k + (if i = j then (k : ℝ) * m / yp i else 0) with hD
  have hf0 : f 0 = m := by simp [hf, hm]
  have hslope : Filter.Tendsto (slope f 0) (nhdsWithin 0 (Set.Ioi 0)) (nhds D) :=
    (hasDerivWithinAt_iff_tendsto_slope' (by simp)).1 hd.hasDerivWithinAt
  have hDle : D ≤ 0 := by
    refine le_of_tendsto hslope ?_
    filter_upwards [Ioo_mem_nhdsGT hyj] with t ht
    have hcube' : InCube c (Function.update yp j (yp j - t)) := by
      intro u
      by_cases hu : u = j
      · subst hu
        simp only [Function.update_self]
        exact ⟨by linarith [ht.2], by linarith [ht.1, (hcube u).2]⟩
      · simp only [Function.update_of_ne hu]
        exact hcube u
    have hle : f t ≤ f 0 := by
      rw [hf0]
      exact hmax _ hcube'
    rw [slope_def_field]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith [ht.1])
  have key : ∑ l ∈ posSrc S yp, walkB G a yp S l j * (momC G p a yp ym S k i l / yp l) +
      (if i = j then (k : ℝ) * m * yp i ^ k else 0) = (yp i ^ k * yp j) * D := by
    have hyik : yp i ^ k ≠ 0 := pow_ne_zero _ hyi.ne'
    have h1 : (yp i ^ k * yp j) * ((∑ l ∈ posSrc S yp, walkB G a yp S l j / (yp l * yp j) *
        momC G p a yp ym S k i l) / yp i ^ k) =
        ∑ l ∈ posSrc S yp, walkB G a yp S l j * (momC G p a yp ym S k i l / yp l) := by
      calc (yp i ^ k * yp j) * ((∑ l ∈ posSrc S yp, walkB G a yp S l j / (yp l * yp j) *
            momC G p a yp ym S k i l) / yp i ^ k)
          = yp j * (∑ l ∈ posSrc S yp, walkB G a yp S l j / (yp l * yp j) *
            momC G p a yp ym S k i l) * (yp i ^ k / yp i ^ k) := by ring
        _ = _ := by
          rw [div_self hyik, mul_one, Finset.mul_sum]
          refine Finset.sum_congr rfl fun l hl => ?_
          have hyl : 0 < yp l := (Finset.mem_filter.1 hl).2
          field_simp
    have h2 : (yp i ^ k * yp j) * (if i = j then (k : ℝ) * m / yp i else 0) =
        if i = j then (k : ℝ) * m * yp i ^ k else 0 := by
      by_cases hij : i = j
      · subst hij
        simp only [ite_true]
        field_simp
      · simp only [hij, ite_false, mul_zero]
    rw [hD, mul_add, h1, h2]
  rw [key]
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hDle

end BiluLinial.Tight
