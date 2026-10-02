/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.Gauss.Basic

/-!
# Replacing one coordinate of a product measure

Part D (`docs/second_order_bilu_linial_tight.tex`, Section 1.2, proof of eq. (E4)): the
coordinates are processed one at a time, so we integrate out a single coordinate of a product
measure on `ι → ℝ`.

* `pi_update_eq_map`: `Measure.pi (update μs i ν)` is the image of `Measure.pi μs ⊗ ν` under
  `(x, t) ↦ update x i t`;
* `integral_pi_update`: `∫ g d(Measure.pi (update μs i ν)) = ∫ (∫ g (update x i t) dν(t)) dμ(x)`
  for bounded continuous `g`, and `integrable_integral_update`;
* `hybPi l`: Gaussian coordinates on the list `l`, Rademacher coordinates elsewhere
  (`hybPi [] = radPi ι`, `hybPi l = gaussPi ι` if `l` contains every coordinate), with
  `integral_hybPi_cons` and `integral_hybPi_rad` describing one step of the hybrid argument.
-/

@[expose] public section

namespace BiluLinial.Tight

open MeasureTheory ProbabilityTheory Function

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
theorem isProbabilityMeasure_update (μs : ι → Measure ℝ) [∀ j, IsProbabilityMeasure (μs j)]
    (i : ι) (ν : Measure ℝ) [IsProbabilityMeasure ν] (j : ι) :
    IsProbabilityMeasure (update μs i ν j) := by
  by_cases h : j = i
  · subst h; simp only [update_self]; infer_instance
  · simp only [update_of_ne h]; infer_instance

/-- Replacing coordinate `i` of a product of probability measures by `ν`: the result is the image
of `Measure.pi μs ⊗ ν` under `(x, t) ↦ update x i t`. -/
theorem pi_update_eq_map (μs : ι → Measure ℝ) [∀ j, IsProbabilityMeasure (μs j)] (i : ι)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    Measure.pi (update μs i ν) =
      ((Measure.pi μs).prod ν).map (fun p : (ι → ℝ) × ℝ => update p.1 i p.2) := by
  have := isProbabilityMeasure_update μs i ν
  refine Measure.pi_eq (fun s hs => ?_)
  rw [Measure.map_apply (measurable_update' (a := i)) (MeasurableSet.univ_pi hs)]
  have hpre : (fun p : (ι → ℝ) × ℝ => update p.1 i p.2) ⁻¹' (Set.univ.pi s) =
      (Set.univ.pi (update s i Set.univ)) ×ˢ s i := by
    ext ⟨x, t⟩
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_prod]
    constructor
    · intro h
      refine ⟨fun j => ?_, by simpa using h i⟩
      by_cases hj : j = i
      · subst hj; simp
      · simpa [update_of_ne hj] using h j
    · rintro ⟨h1, h2⟩ j
      by_cases hj : j = i
      · subst hj; simpa using h2
      · simpa [update_of_ne hj] using h1 j
  rw [hpre, Measure.prod_prod, Measure.pi_pi, Fintype.prod_eq_mul_prod_compl i,
    Fintype.prod_eq_mul_prod_compl i (fun j => update μs i ν j (s j))]
  simp only [update_self, measure_univ, one_mul]
  rw [mul_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  have : j ≠ i := by simpa using hj
  simp [update_of_ne this]

theorem integrable_comp_update (μs : ι → Measure ℝ) [∀ j, IsProbabilityMeasure (μs j)] (i : ι)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {g : (ι → ℝ) → ℝ} (hg : Continuous g)
    (hb : ∃ C, ∀ x, |g x| ≤ C) :
    Integrable (fun p : (ι → ℝ) × ℝ => g (update p.1 i p.2)) ((Measure.pi μs).prod ν) := by
  obtain ⟨C, hC⟩ := hb
  exact Integrable.of_bound (hg.measurable.comp (measurable_update' (a := i))).aestronglyMeasurable
    C (ae_of_all _ fun p => by simpa [Real.norm_eq_abs] using hC _)

/-- Integrating out coordinate `i` of a product measure, for bounded continuous `g`. -/
theorem integral_pi_update (μs : ι → Measure ℝ) [∀ j, IsProbabilityMeasure (μs j)] (i : ι)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {g : (ι → ℝ) → ℝ} (hg : Continuous g)
    (hb : ∃ C, ∀ x, |g x| ≤ C) :
    ∫ x, g x ∂(Measure.pi (update μs i ν)) =
      ∫ x, (∫ t, g (update x i t) ∂ν) ∂(Measure.pi μs) := by
  rw [pi_update_eq_map, integral_map (measurable_update' (a := i)).aemeasurable
    hg.aestronglyMeasurable]
  exact integral_prod _ (integrable_comp_update μs i ν hg hb)

theorem integrable_integral_update (μs : ι → Measure ℝ) [∀ j, IsProbabilityMeasure (μs j)]
    (i : ι) (ν : Measure ℝ) [IsProbabilityMeasure ν] {g : (ι → ℝ) → ℝ} (hg : Continuous g)
    (hb : ∃ C, ∀ x, |g x| ≤ C) :
    Integrable (fun x => ∫ t, g (update x i t) ∂ν) (Measure.pi μs) :=
  (integrable_comp_update μs i ν hg hb).integral_prod_left

/-- The coordinate laws of `hybPi l`: Gaussian on `l`, Rademacher elsewhere. -/
noncomputable def hybLaw (l : List ι) (i : ι) : Measure ℝ :=
  if i ∈ l then gaussianReal 0 1 else radReal

instance isProbabilityMeasure_hybLaw (l : List ι) (i : ι) : IsProbabilityMeasure (hybLaw l i) := by
  unfold hybLaw; split_ifs <;> infer_instance

/-- The hybrid product measure: standard Gaussian coordinates on the list `l`, Rademacher
coordinates off `l`. -/
noncomputable def hybPi (l : List ι) : Measure (ι → ℝ) := Measure.pi (hybLaw l)

instance isProbabilityMeasure_hybPi (l : List ι) : IsProbabilityMeasure (hybPi l) := by
  unfold hybPi; infer_instance

theorem hybPi_nil : hybPi ([] : List ι) = radPi ι := by
  unfold hybPi radPi
  congr 1

theorem hybPi_of_forall_mem {l : List ι} (h : ∀ i, i ∈ l) : hybPi l = gaussPi ι := by
  unfold hybPi gaussPi
  congr 1
  funext x
  simp [hybLaw, h]

omit [Fintype ι] in
theorem hybLaw_cons (i : ι) (l : List ι) :
    hybLaw (i :: l) = update (hybLaw l) i (gaussianReal 0 1) := by
  funext x
  by_cases h : x = i
  · subst h; simp [hybLaw]
  · simp [hybLaw, h]

omit [Fintype ι] in
theorem hybLaw_eq_update_rad {i : ι} {l : List ι} (hi : i ∉ l) :
    hybLaw l = update (hybLaw l) i radReal := by
  conv_lhs => rw [← update_eq_self i (hybLaw l)]
  simp [hybLaw, hi]

/-- One hybrid step, Gaussian side: `∫ g d(hybPi (i :: l)) = ∫ (𝖦_i g) d(hybPi l)`. -/
theorem integral_hybPi_cons {i : ι} {l : List ι} {g : (ι → ℝ) → ℝ} (hg : Continuous g)
    (hb : ∃ C, ∀ x, |g x| ≤ C) :
    ∫ x, g x ∂hybPi (i :: l) = ∫ x, (∫ t, g (update x i t) ∂gaussianReal 0 1) ∂hybPi l := by
  rw [hybPi, hybLaw_cons]
  exact integral_pi_update _ i _ hg hb

/-- One hybrid step, Rademacher side: for `i ∉ l`, `∫ (𝖱_i g) d(hybPi l) = ∫ g d(hybPi l)`. -/
theorem integral_hybPi_rad {i : ι} {l : List ι} (hi : i ∉ l) {g : (ι → ℝ) → ℝ}
    (hg : Continuous g) (hb : ∃ C, ∀ x, |g x| ≤ C) :
    ∫ x, (∫ t, g (update x i t) ∂radReal) ∂hybPi l = ∫ x, g x ∂hybPi l := by
  rw [hybPi]
  conv_rhs => rw [hybLaw_eq_update_rad hi]
  exact (integral_pi_update _ i _ hg hb).symm

theorem integrable_hybPi_slice (i : ι) (l : List ι) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {g : (ι → ℝ) → ℝ} (hg : Continuous g) (hb : ∃ C, ∀ x, |g x| ≤ C) :
    Integrable (fun x => ∫ t, g (update x i t) ∂ν) (hybPi l) :=
  integrable_integral_update _ i ν hg hb

end BiluLinial.Tight
