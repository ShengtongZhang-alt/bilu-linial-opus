/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.Ctx
public import BiluLinial.Tight.SourceMax.Glue

/-!
# Physical form of the paired law

Blueprint node `D-SM-phys` (source Section 1.1, first paragraph: "congruence by
`√(diag y)` multiplies all weights by the same source-dependent factor").

On the positive plus-sources `S⁺ = {u ∈ S : y_u > 0}` the normalized precision is
`P̃ = M P M` with `M = diag m`, `m_u = √y_u` on `S⁺` and `1` elsewhere, where the physical
precision `P` (`precPhys`) has diagonal `Z_u = D_u/y_u` and off-diagonal `τ a σ_uw` on `S⁺`, and
is the identity elsewhere (zero sources are isolated identity rows of `P̃`, since `D_u = 1` and
`√y_u = 0` there). Hence `det P̃ = (Π_{S⁺} y_u) det P`, `P̃ ≻ 0 ⟺ P ≻ 0`,
`P̃⁻¹ = M⁻¹ P⁻¹ M⁻¹`, so `greenP = P⁻¹` on `S⁺ × S⁺` and `h_i = P⁻¹_ii / y_i` for `i ∈ S⁺`. The
weight is `W = (Π_{S⁺} y_u)^p · W⁻ · 1{P ≻ 0} det(P)^p`, with `W⁻ = 1{P̃⁻ ≻ 0} det(P̃⁻)^p`, and the
factor cancels in `lawE`. Moving one positive source `y_j ↦ y_j - t` (`t < y_j`) keeps `S⁺` and
the off-diagonal part of `P`, so `P` moves along a diagonal curve.
Requires `y ≥ 0` (at a negative coordinate `√y = 0` but `D ≠ 1`).
-/

@[expose] public section

namespace BiluLinial.Tight

open Matrix

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The positive sources `S⁺ = {u ∈ S : y_u > 0}`. -/
noncomputable def posSrc (S : Finset V) (y : V → ℝ) : Finset V := S.filter fun u => 0 < y u

/-- The congruence factor `Π_{u ∈ S⁺} y_u`. -/
noncomputable def physFactor (S : Finset V) (y : V → ℝ) : ℝ := ∏ u ∈ posSrc S y, y u

/-- The scaling `m_u = √y_u` on `S⁺`, `1` elsewhere. -/
noncomputable def physScale (S : Finset V) (y : V → ℝ) (u : V) : ℝ :=
  if u ∈ posSrc S y then Real.sqrt (y u) else 1

/-- The physical precision on `S⁺` (diagonal `Z_u`, off-diagonal `τ a σ_uw`), identity
elsewhere. -/
noncomputable def precPhys (a τ : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) :
    Matrix V V ℝ :=
  Matrix.of fun u w =>
    if u = w then (if u ∈ posSrc S y then precZ G a y S u else 1)
    else if u ∈ posSrc S y ∧ w ∈ posSrc S y ∧ G.Adj u w then τ * a * sgn σ u w else 0

/-- The minus-branch factor `W⁻ = 1{P̃⁻ ≻ 0} det(P̃⁻)^p` of the weight. -/
noncomputable def wtMinus (p : ℕ) (a : ℝ) (ym : V → ℝ) (σ : Config V) (S : Finset V) : ℝ :=
  posPow p (precN G a (-1) ym σ S)

variable {G}

omit [Fintype V] [DecidableEq V] in
theorem physFactor_pos (S : Finset V) (y : V → ℝ) : 0 < physFactor S y :=
  Finset.prod_pos fun _ hu => (Finset.mem_filter.1 hu).2

omit [Fintype V] in
theorem precPhys_isHermitian (a τ : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) :
    (precPhys G a τ y σ S).IsHermitian := by
  refine Matrix.IsHermitian.ext fun u w => ?_
  simp only [precPhys, Matrix.of_apply, star_trivial]
  by_cases h : u = w
  · subst h
    rfl
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]
    have hs : sgn σ w u = sgn σ u w := by
      unfold sgn
      rw [Sym2.eq_swap]
    by_cases hc : u ∈ posSrc S y ∧ w ∈ posSrc S y ∧ G.Adj u w
    · rw [ite_eq_left ⟨hc.2.1, hc.1, hc.2.2.symm⟩, ite_eq_left hc, hs]
    · rw [ite_eq_right (fun h' => hc ⟨h'.2.1, h'.1, h'.2.2.symm⟩), ite_eq_right hc]

variable {a τ : ℝ} {y : V → ℝ} {σ : Config V} {S : Finset V}

omit [Fintype V] in
theorem physScale_pos (u : V) : 0 < physScale S y u := by
  unfold physScale
  split_ifs with h
  · exact Real.sqrt_pos.2 (Finset.mem_filter.1 h).2
  · exact one_pos

theorem precN_eq_scale (hy : ∀ u, 0 ≤ y u) :
    precN G a τ y σ S =
      diagonal (physScale S y) * precPhys G a τ y σ S * diagonal (physScale S y) := by
  have hz : ∀ v, v ∈ S → ¬ 0 < y v → y v = 0 := fun v _ hv => le_antisymm (not_lt.1 hv) (hy v)
  ext u w
  rw [mul_diagonal, diagonal_mul]
  simp only [precN, precPhys, physScale, of_apply, posSrc, Finset.mem_filter]
  by_cases huw : u = w
  · subst huw
    simp only [ite_true]
    by_cases hu : u ∈ S
    · by_cases hpos : 0 < y u
      · simp only [hu, hpos, and_self, ite_true, precZ]
        have h1 := Real.mul_self_sqrt (hy u)
        rw [mul_comm, ← mul_assoc, h1]
        field_simp
      · have h0 := hz u hu hpos
        simp [hu, diagD, cEdge, h0, cRoot]
    · simp [hu]
  · simp only [huw, ite_false]
    by_cases hc : u ∈ S ∧ w ∈ S ∧ G.Adj u w
    · obtain ⟨hu, hw, hadj⟩ := hc
      by_cases hpu : 0 < y u
      · by_cases hpw : 0 < y w
        · simp only [hu, hw, hadj, hpu, hpw, and_self, ite_true]
          ring
        · simp [hu, hw, hadj, hz w hw hpw]
      · simp [hu, hw, hadj, hz u hu hpu]
    · have hc' : ¬((u ∈ S ∧ 0 < y u) ∧ (w ∈ S ∧ 0 < y w) ∧ G.Adj u w) :=
        fun h => hc ⟨h.1.1, h.2.1.1, h.2.2⟩
      simp only [hc, hc', ite_false, mul_zero, zero_mul]

theorem det_precN (hy : ∀ u, 0 ≤ y u) :
    (precN G a τ y σ S).det = physFactor S y * (precPhys G a τ y σ S).det := by
  have hsq : ∀ u, physScale S y u * physScale S y u = if u ∈ posSrc S y then y u else 1 := by
    intro u
    unfold physScale
    split_ifs
    · exact Real.mul_self_sqrt (hy u)
    · ring
  have hprod : (∏ u, physScale S y u) * (∏ u, physScale S y u) = physFactor S y := by
    rw [← Finset.prod_mul_distrib]
    simp only [hsq]
    rw [Finset.prod_ite_mem, Finset.univ_inter]
    rfl
  rw [precN_eq_scale hy, det_mul, det_mul, det_diagonal, ← hprod]
  ring

theorem posDef_precN_iff (hy : ∀ u, 0 ≤ y u) :
    (precN G a τ y σ S).PosDef ↔ (precPhys G a τ y σ S).PosDef := by
  have hU : IsUnit (diagonal (physScale S y)) :=
    isUnit_diagonal.2 (Pi.isUnit_iff.2 fun u => (physScale_pos u).ne'.isUnit)
  have hstar : star (diagonal (physScale S y)) = diagonal (physScale S y) := by
    rw [star_eq_conjTranspose, diagonal_conjTranspose, star_trivial]
  have := hU.posDef_star_right_conjugate_iff (x := precPhys G a τ y σ S)
  rw [hstar] at this
  rw [precN_eq_scale hy]
  exact this

theorem inv_precN_apply (hy : ∀ u, 0 ≤ y u) (u w : V) :
    (precN G a τ y σ S)⁻¹ u w =
      (physScale S y u)⁻¹ * (precPhys G a τ y σ S)⁻¹ u w * (physScale S y w)⁻¹ := by
  have hD : (diagonal (physScale S y))⁻¹ = diagonal fun u => (physScale S y u)⁻¹ := by
    refine inv_eq_right_inv ?_
    rw [diagonal_mul_diagonal]
    convert diagonal_one with u
    exact mul_inv_cancel₀ (physScale_pos u).ne'
  rw [precN_eq_scale hy, Matrix.mul_inv_rev, Matrix.mul_inv_rev, hD, diagonal_mul,
    mul_diagonal]
  ring

theorem greenP_eq_phys (hy : ∀ u, 0 ≤ y u) {u w : V} (hu : u ∈ posSrc S y)
    (hw : w ∈ posSrc S y) : greenP G a τ y σ S u w = (precPhys G a τ y σ S)⁻¹ u w := by
  rw [greenP, inv_precN_apply hy]
  have hsu : physScale S y u = Real.sqrt (y u) := by simp [physScale, hu]
  have hsw : physScale S y w = Real.sqrt (y w) := by simp [physScale, hw]
  have h1 : Real.sqrt (y u) ≠ 0 := (Real.sqrt_pos.2 (Finset.mem_filter.1 hu).2).ne'
  have h2 : Real.sqrt (y w) ≠ 0 := (Real.sqrt_pos.2 (Finset.mem_filter.1 hw).2).ne'
  rw [hsu, hsw]
  field_simp

theorem hN_eq_phys (hy : ∀ u, 0 ≤ y u) {i : V} (hi : i ∈ posSrc S y) :
    hN G a τ y σ S i = (precPhys G a τ y σ S)⁻¹ i i / y i := by
  rw [hN, inv_precN_apply hy]
  have hsi : physScale S y i = Real.sqrt (y i) := by simp [physScale, hi]
  have hpos : 0 < y i := (Finset.mem_filter.1 hi).2
  have hs : Real.sqrt (y i) * Real.sqrt (y i) = y i := Real.mul_self_sqrt hpos.le
  rw [hsi, eq_div_iff hpos.ne']
  calc (Real.sqrt (y i))⁻¹ * (precPhys G a τ y σ S)⁻¹ i i * (Real.sqrt (y i))⁻¹ * y i
      = (precPhys G a τ y σ S)⁻¹ i i * (y i / (Real.sqrt (y i) * Real.sqrt (y i))) := by ring
    _ = (precPhys G a τ y σ S)⁻¹ i i := by rw [hs, div_self hpos.ne', mul_one]

theorem wt_eq_phys (hy : ∀ u, 0 ≤ y u) (p : ℕ) (ym : V → ℝ) :
    wt G p a y ym σ S =
      physFactor S y ^ p * wtMinus G p a ym σ S * posPow p (precPhys G a 1 y σ S) := by
  unfold wt wtMinus posPow
  rw [det_precN hy]
  by_cases h1 : (precPhys G a 1 y σ S).PosDef
  · have h1' : (precN G a 1 y σ S).PosDef := (posDef_precN_iff hy).2 h1
    by_cases h2 : (precN G a (-1) ym σ S).PosDef
    · rw [ite_eq_left ⟨h1', h2⟩, ite_eq_left h2, ite_eq_left h1]
      ring
    · rw [ite_eq_right (fun h => h2 h.2), ite_eq_right h2]
      ring
  · have h1' : ¬ (precN G a 1 y σ S).PosDef := fun h => h1 ((posDef_precN_iff hy).1 h)
    rw [ite_eq_right (fun h => h1' h.1), ite_eq_right h1]
    ring

theorem wt_mul_hN_pow_eq_phys (hy : ∀ u, 0 ≤ y u) (p : ℕ) (ym : V → ℝ) {i : V}
    (hi : i ∈ posSrc S y) (k : ℕ) :
    wt G p a y ym σ S * hN G a 1 y σ S i ^ k =
      physFactor S y ^ p * wtMinus G p a ym σ S * glue p k i (precPhys G a 1 y σ S) /
        y i ^ k := by
  rw [wt_eq_phys hy, hN_eq_phys hy hi, glue, div_pow]
  ring

/-- The law in physical form: the congruence factor cancels. -/
theorem lawE_eq_phys (hy : ∀ u, 0 ≤ y u) (p : ℕ) (ym : V → ℝ) (f : Config V → ℝ) :
    lawE G p a y ym S f =
      (∑ σ, wtMinus G p a ym σ S * posPow p (precPhys G a 1 y σ S) * f σ) /
        ∑ σ, wtMinus G p a ym σ S * posPow p (precPhys G a 1 y σ S) := by
  unfold lawE Zw
  simp only [wt_eq_phys hy]
  have h1 : ∑ σ, physFactor S y ^ p * wtMinus G p a ym σ S * posPow p (precPhys G a 1 y σ S) *
      f σ = physFactor S y ^ p *
        ∑ σ, wtMinus G p a ym σ S * posPow p (precPhys G a 1 y σ S) * f σ := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun σ _ => by ring
  have h2 : ∑ σ, physFactor S y ^ p * wtMinus G p a ym σ S * posPow p (precPhys G a 1 y σ S) =
      physFactor S y ^ p * ∑ σ, wtMinus G p a ym σ S * posPow p (precPhys G a 1 y σ S) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun σ _ => by ring
  rw [h1, h2, mul_div_mul_left _ _ (pow_ne_zero _ (physFactor_pos S y).ne')]

omit [Fintype V] in
theorem posSrc_update {j : V} (hj : j ∈ posSrc S y) {t : ℝ} (ht : t < y j) :
    posSrc S (Function.update y j (y j - t)) = posSrc S y := by
  ext u
  simp only [posSrc, Finset.mem_filter, Function.update_apply]
  by_cases h : u = j
  · subst h
    have := (Finset.mem_filter.1 hj)
    simp only [ite_true]
    constructor
    · exact fun h' => this
    · exact fun h' => ⟨h'.1, by linarith⟩
  · simp only [h, ite_false]

omit [Fintype V] in
/-- Moving the positive source `j` moves `P` along a diagonal curve. -/
theorem precPhys_update {j : V} (hj : j ∈ posSrc S y) {t : ℝ} (ht : t < y j) :
    precPhys G a τ (Function.update y j (y j - t)) σ S =
      precPhys G a τ y σ S + diagonal (fun u => if u ∈ posSrc S y then
        precZ G a (Function.update y j (y j - t)) S u - precZ G a y S u else 0) := by
  ext u w
  simp only [precPhys, of_apply, Matrix.add_apply, diagonal_apply, posSrc_update hj ht]
  by_cases huw : u = w
  · subst huw
    by_cases hu : u ∈ posSrc S y
    · simp only [ite_true, hu]
      ring
    · simp only [ite_true, hu, ite_false, add_zero]
  · simp only [huw, ite_false, add_zero]

end BiluLinial.Tight
