/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.Walk
public import BiluLinial.Tight.SourceMax.Phys

/-!
# Inverting the first-order condition with the walk matrix

Blueprint node `D-SM-la` (source Section 1.1, proof of Lemma "Source maximum and moments":
"multiply by `-D_y K D_y`"; AUDIT-D gap G1).

**Sketch.** `𝓑 = walkB` is symmetric, and at a zero source (or off `S`) its row and column are
those of the identity, since every `τ` there vanishes. Put `x_l = C_l / y_l` on `S⁺` and `0`
elsewhere. The first-order conditions say `(𝓑 x)_j ≤ -c 1_{j=i}` for `j ∈ S⁺`; for `j ∉ S⁺`,
`(𝓑 x)_j = 0 = -c 1_{j=i}` as `i ∈ S⁺`. With `K = 𝓑⁻¹ ≥ 0` (`walk_facts`),
`x = K 𝓑 x ≤ -c K e_i`, i.e. `C_l ≤ -c y_l K_li` on `S⁺`.
-/

@[expose] public section

namespace BiluLinial.Tight

open Matrix

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

omit [Fintype V] in
theorem walkB_symm (a : ℝ) (y : V → ℝ) (S : Finset V) (u w : V) :
    walkB G a y S u w = walkB G a y S w u := by
  have hc : cEdge a y u w = cEdge a y w u := by
    unfold cEdge
    rw [mul_right_comm]
  have hτ : τEdge a y u w = τEdge a y w u := by
    unfold τEdge
    rw [hc]
  by_cases h : u = w
  · subst h
    rfl
  · simp only [walkB, Matrix.of_apply]
    rw [ite_eq_right h, ite_eq_right (Ne.symm h)]
    by_cases hS : u ∈ S ∧ w ∈ S ∧ G.Adj u w
    · rw [ite_eq_left hS, ite_eq_left ⟨hS.2.1, hS.1, hS.2.2.symm⟩, hτ]
    · rw [ite_eq_right hS, ite_eq_right fun h' => hS ⟨h'.2.1, h'.1, h'.2.2.symm⟩]

theorem walkK_symm (a : ℝ) (y : V → ℝ) (S : Finset V) (u w : V) :
    walkK G a y S u w = walkK G a y S w u := by
  have hB : (walkB G a y S)ᵀ = walkB G a y S := by
    ext u w
    exact walkB_symm G a y S w u
  unfold walkK
  rw [← Matrix.transpose_apply (walkB G a y S)⁻¹ w u, Matrix.transpose_nonsing_inv, hB]

omit [Fintype V] in
/-- At a zero source, or off `S`, the rows and columns of `𝓑` are those of the identity. -/
theorem walkB_eq_zero_of_not_mem {a : ℝ} {y : V → ℝ} (hy : ∀ u, 0 ≤ y u) {S : Finset V} {u w : V}
    (huw : u ≠ w) (h : u ∉ posSrc S y ∨ w ∉ posSrc S y) : walkB G a y S u w = 0 := by
  simp only [walkB, Matrix.of_apply]
  rw [ite_eq_right huw]
  by_cases hS : u ∈ S ∧ w ∈ S ∧ G.Adj u w
  · rw [ite_eq_left hS]
    have h0 : a ^ 2 * y u * y w = 0 := by
      rcases h with h | h
      · have : y u = 0 := le_antisymm
          (not_lt.1 fun hp => h (Finset.mem_filter.2 ⟨hS.1, hp⟩)) (hy u)
        rw [this]
        ring
      · have : y w = 0 := le_antisymm
          (not_lt.1 fun hp => h (Finset.mem_filter.2 ⟨hS.2.1, hp⟩)) (hy w)
        rw [this]
        ring
    simp [τEdge, cEdge, h0, cRoot]
  · rw [ite_eq_right hS]

/-- If `K B = 1` with `K ≥ 0` entrywise, then `B x ≤ b` implies `x ≤ K b`. -/
theorem le_mulVec_of_mulVec_le {n : Type*} [Fintype n] [DecidableEq n] {B K : Matrix n n ℝ}
    (hKB : K * B = 1) (hK : ∀ u w, 0 ≤ K u w) {x b : n → ℝ} (h : ∀ u, (B *ᵥ x) u ≤ b u) (u : n) :
    x u ≤ (K *ᵥ b) u := by
  have hx : x = K *ᵥ (B *ᵥ x) := by rw [mulVec_mulVec, hKB, one_mulVec]
  rw [hx]
  simp only [mulVec, dotProduct]
  exact Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_left (h w) (hK u w)

/-- `D-SM-la`: the first-order conditions on `S⁺` give `C_l ≤ -c y_l K_li` on `S⁺`. -/
theorem walk_dual {d p : ℕ} (hR : TRegime d p) (hdeg : ∀ v, G.degree v ≤ d) {yp : V → ℝ}
    (hy : InCube (sOf d p) yp) {S : Finset V} {i : V} (hi : i ∈ posSrc S yp) {C : V → ℝ}
    {c : ℝ}
    (hfoc : ∀ j ∈ posSrc S yp, ∑ l ∈ posSrc S yp, walkB G (aOf d p) yp S l j * (C l / yp l) +
      (if i = j then c else 0) ≤ 0) :
    ∀ l ∈ posSrc S yp, C l ≤ -(c * yp l * walkK G (aOf d p) yp S l i) := by
  classical
  obtain ⟨hPD, hK0, -, -⟩ := walk_facts G hR hdeg hy S
  have hy0 : ∀ u, 0 ≤ yp u := fun u => (hy u).1
  let x : V → ℝ := fun l => if l ∈ posSrc S yp then C l / yp l else 0
  let b : V → ℝ := fun u => if u = i then -c else 0
  have hKB : walkK G (aOf d p) yp S * walkB G (aOf d p) yp S = 1 :=
    nonsing_inv_mul _ hPD.det_pos.ne'.isUnit
  have hsum : ∀ u, (walkB G (aOf d p) yp S *ᵥ x) u =
      ∑ l ∈ posSrc S yp, walkB G (aOf d p) yp S u l * (C l / yp l) := by
    intro u
    simp only [mulVec, dotProduct, x, mul_ite, mul_zero]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  have hBx : ∀ u, (walkB G (aOf d p) yp S *ᵥ x) u ≤ b u := by
    intro u
    rw [hsum]
    by_cases hu : u ∈ posSrc S yp
    · have h1 := hfoc u hu
      simp only [walkB_symm G _ _ _ u] at *
      by_cases hiu : u = i
      · subst hiu
        simp only [b, ite_true] at h1 ⊢
        linarith
      · simp only [b, hiu, Ne.symm hiu, ite_false] at h1 ⊢
        linarith
    · have hz : ∑ l ∈ posSrc S yp, walkB G (aOf d p) yp S u l * (C l / yp l) = 0 :=
        Finset.sum_eq_zero fun l hl => by
          have hul : u ≠ l := by
            rintro rfl
            exact hu hl
          rw [walkB_eq_zero_of_not_mem G hy0 hul (Or.inl hu), zero_mul]
      have hiu : u ≠ i := by
        rintro rfl
        exact hu hi
      simp only [hz, b, hiu, ite_false, le_refl]
  intro l hl
  have h1 := le_mulVec_of_mulVec_le hKB hK0 hBx l
  have hKb : (walkK G (aOf d p) yp S *ᵥ b) l = -(c * walkK G (aOf d p) yp S l i) := by
    simp only [mulVec, dotProduct, b, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true]
    ring
  simp only [x, hl, ite_true, hKb] at h1
  have hyl : 0 < yp l := (Finset.mem_filter.1 hl).2
  rw [div_le_iff₀ hyl] at h1
  linarith

end BiluLinial.Tight
