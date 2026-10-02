/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import Mathlib

/-!
# Gaussian and Rademacher product measures

Part D (`docs/second_order_bilu_linial_tight.tex`, Section 1). The paper compares expectations of
functions of an incident sign vector `ξ ∈ {±1}^N` (written `𝖱[·]`) with expectations under a
standard Gaussian vector (written `𝖦[·]`). Both are product measures on `ι → ℝ`:

* `gaussPi ι`: independent standard normal coordinates;
* `radPi ι`: independent Rademacher coordinates (`±1` with probability `1/2` each);
* `mixPi S ι`: Rademacher coordinates on `S`, standard normal coordinates off `S` (the mixed
  operators that appear when the coordinates are processed one at a time in eq. (E4)).
-/

@[expose] public section

namespace BiluLinial.Tight

open MeasureTheory ProbabilityTheory

/-- The Rademacher law on `ℝ`: the atoms `1` and `-1`, each with mass `1/2`. -/
noncomputable def radReal : Measure ℝ :=
  (2 : ENNReal)⁻¹ • (Measure.dirac 1 + Measure.dirac (-1))

instance isProbabilityMeasure_radReal : IsProbabilityMeasure radReal := by
  constructor
  simp only [radReal, Measure.smul_apply, Measure.add_apply, Measure.dirac_apply_of_mem,
    Set.mem_univ, smul_eq_mul]
  rw [← two_mul, mul_one, ENNReal.inv_mul_cancel (by norm_num) (by norm_num)]

/-- The standard Gaussian measure on `ι → ℝ`: independent standard normal coordinates. -/
noncomputable def gaussPi (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi fun _ : ι => gaussianReal 0 1

instance isProbabilityMeasure_gaussPi (ι : Type*) [Fintype ι] :
    IsProbabilityMeasure (gaussPi ι) := by
  unfold gaussPi
  infer_instance

/-- The uniform measure on sign vectors `{±1}^ι ⊆ ι → ℝ`: independent Rademacher coordinates. -/
noncomputable def radPi (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi fun _ : ι => radReal

instance isProbabilityMeasure_radPi (ι : Type*) [Fintype ι] :
    IsProbabilityMeasure (radPi ι) := by
  unfold radPi
  infer_instance

/-- Rademacher coordinates on `S`, standard normal coordinates off `S`. -/
noncomputable def mixPi {ι : Type*} [Fintype ι] (S : Set ι) [DecidablePred (· ∈ S)] :
    Measure (ι → ℝ) :=
  Measure.pi fun i : ι => if i ∈ S then radReal else gaussianReal 0 1

instance isProbabilityMeasure_mixPi {ι : Type*} [Fintype ι] (S : Set ι)
    [DecidablePred (· ∈ S)] : IsProbabilityMeasure (mixPi S) := by
  unfold mixPi
  have : ∀ i : ι, IsProbabilityMeasure (if i ∈ S then radReal else gaussianReal 0 1) := by
    intro i
    split_ifs <;> infer_instance
  infer_instance

end BiluLinial.Tight
