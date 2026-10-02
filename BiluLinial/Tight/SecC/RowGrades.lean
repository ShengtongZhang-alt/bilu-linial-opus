/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecC.RowG1
public import BiluLinial.Tight.SecC.RowG2
public import BiluLinial.Tight.SecC.RowG3

/-!
# The retained grades of the row comparison (node CR-GR of `docs/tight/BP_SECC.md`)

Source lines 1153–1190 (steps 2–3 of AUDIT-C §4.2). `row_grades_le` (CR-GR) is proved from three
sub-nodes, one per range of grades of the retained multi-indices `j ∈ retIdx k_*` (`j ≠ 0` iff
`|j|_g ≥ 1`, `sum_erase_zero_split`):

* **CR-G1** (`row_grade1_le`), `|j|_g = 1`, i.e. `j = 2e_i`, `c_j = 1/12`, `∂^{2j} = ∂_i⁴`:
  `|Σ c_j rowRet j| ≤ a² C (p⁵ X₅ + p⁴ √(λ_c δ_c))`.
* **CR-G2** (`row_grade2_le`), `|j|_g = 2`, i.e. `j = 3e_i` (`c_j = -1/45`, `∂_i⁶`) or
  `j = 2e_i + 2e_k` (`c_j = 1/144`, `∂_i⁴∂_k⁴`): `≤ a² C p⁴ √(λ_c δ_c)`.
* **CR-G3** (`row_grade3_le`), `3 ≤ |j|_g ≤ k_*` (unmarked): `≤ a² C p¹³/d²`.

**Checks.** `N = ∅`: `retIdx k = {0}`, all three sums are empty. One coordinate: the three ranges
are `{2e}`, `{3e}` and `{ae : 4 ≤ a ≤ k_*+1}`. Orders of magnitude (with `D`-type unmarked weights
of bounded moments, `R₊ = a²Σ_N (G⁺_vj)²`, `E R₊ ≤ λ_r/2`): grade one, row mark
`Σ_i a⁴(1 + r_i)⁴ Σ_j x_j² = rowWt · R₊`, so `a² p⁴ E[rowWt R₊] ≲ a² p⁴ λ_r`; grade two, diagonal
`Σ_i a⁶(1 + r_i)⁶ Σ_j x_j² = a² W₆ R₊` and mixed
`Σ_{i≠k} a⁸(1+r_i)⁴(1+r_k)⁴ Σ_j x_j² ≤ a² rowWt² R₊`,
so `a² p⁹ a² E[⋯] ≲ a² (p⁹/d) λ_r ≤ a² p⁴ λ_r` (`p⁵ ≤ d`); grade `g ≥ 3`, `p (C p⁴/d)^g` in
`F/Φ` units, `Σ_{g≥3} ≲ p¹³/d³ ≲ a² p¹³/d²`.
-/

@[expose] public section

namespace BiluLinial.Tight

namespace SecC

universe u

open Matrix

/-- `Σ_{j ∈ retIdx k, j ≠ 0} f = Σ_{|j|_g = 1} f + Σ_{|j|_g = 2} f + Σ_{|j|_g ≥ 3} f`. -/
theorem sum_erase_zero_split {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ)
    (f : (ι → ℕ) → ℝ) :
    ∑ j ∈ (retIdx k : Finset (ι → ℕ)).erase 0, f j =
      ∑ j ∈ (retIdx k : Finset (ι → ℕ)).filter (fun j => grade j = 1), f j +
        ∑ j ∈ (retIdx k : Finset (ι → ℕ)).filter (fun j => grade j = 2), f j +
        ∑ j ∈ (retIdx k : Finset (ι → ℕ)).filter (fun j => 3 ≤ grade j), f j := by
  rw [← Finset.filter_ne', Finset.sum_filter, Finset.sum_filter, Finset.sum_filter,
    Finset.sum_filter, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j hj => ?_
  obtain ⟨hadm, -⟩ := mem_retIdx.1 hj
  by_cases h0 : j = 0
  · subst h0
    have hg : grade (0 : ι → ℕ) = 0 := by simp [grade]
    simp [hg]
  · have hg : grade j ≠ 0 := fun h => h0 (eq_zero_of_grade_eq_zero hadm h)
    simp only [ne_eq, h0, not_false_eq_true, ↓reduceIte]
    rcases Nat.lt_or_ge (grade j) 3 with h3 | h3
    · interval_cases hgj : grade j
      · exact absurd rfl hg
      · simp
      · simp
    · have h1 : grade j ≠ 1 := by omega
      have h2 : grade j ≠ 2 := by omega
      simp [h1, h2, h3]

/-- **CR-GR** (the retained grades `1 ≤ |j|_g ≤ k_*`), from CR-G1, CR-G2 and CR-G3. -/
theorem row_grades_le : ∃ C : ℝ, 0 < C ∧ Eventually fun _ _ d p _ =>
    ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
      (S : Finset V) (lam : ℝ) (yp ym : V → ℝ) (v : V), CapCtx G d p S lam →
      InCube (lam * sOf d p) yp → InCube (lam * sOf d p) ym → v ∈ S →
      ∀ lr lc dc : ℝ, vth d ≤ lr → lr ≤ lc → lc ≤ dc →
        incRowE G d p yp ym S v 1 yp / d ≤ lr → incRowE G d p yp ym S v (-1) ym / d ≤ dc →
        markE G d p yp ym S v 1 yp / (d : ℝ) ^ 2 ≤ lc →
        markE G d p yp ym S v (-1) ym / (d : ℝ) ^ 2 ≤ dc →
        |∑ j ∈ (retIdx (kStar d p) : Finset (nbhd G S v → ℕ)).erase 0,
            ecoefM j * rowRet G d p yp ym S v j| ≤
          aOf d p ^ 2 * (C * ((p : ℝ) ^ 5 * rowX5 G d p yp ym S v +
            (p : ℝ) ^ 4 * Real.sqrt (lc * dc) + (p : ℝ) ^ 13 / (d : ℝ) ^ 2)) := by
  obtain ⟨C₁, hC₁, h1⟩ := row_grade1_le.{u}
  obtain ⟨C₂, hC₂, h2⟩ := row_grade2_le.{u}
  obtain ⟨C₃, hC₃, h3⟩ := row_grade3_le.{u}
  refine ⟨C₁ + C₂ + C₃, by positivity, ((h1.and h2).and h3).mono ?_⟩
  rintro c₀ κ₀ d p h ⟨⟨H1, H2⟩, H3⟩ V _ _ G _ S lam yp ym v hC hyp hym hv lr lc dc hvl hllc hlcd
    hS1 hS2 hM1 hM2
  have e1 := H1 V G S lam yp ym v hC hyp hym hv lr lc dc hvl hllc hlcd hS1 hS2 hM1 hM2
  have e2 := H2 V G S lam yp ym v hC hyp hym hv lr lc dc hvl hllc hlcd hS1 hS2 hM1 hM2
  have e3 := H3 V G S lam yp ym v hC hyp hym hv
  rw [sum_erase_zero_split]
  have hX0 : 0 ≤ rowX5 G d p yp ym S v := by
    unfold rowX5
    refine lawE_nonneg G fun σ _ => mul_nonneg ?_ (mul_nonneg (sq_nonneg _) (abs_nonneg _))
    unfold rowWt
    positivity
  have hs0 : 0 ≤ Real.sqrt (lc * dc) := Real.sqrt_nonneg _
  have hT0 : 0 ≤ (p : ℝ) ^ 13 / (d : ℝ) ^ 2 := by positivity
  have ha2 : 0 ≤ aOf d p ^ 2 := sq_nonneg _
  have hA := abs_add_le (∑ j ∈ (retIdx (kStar d p) : Finset (nbhd G S v → ℕ)).filter
      (fun j => grade j = 1), ecoefM j * rowRet G d p yp ym S v j +
    ∑ j ∈ (retIdx (kStar d p) : Finset (nbhd G S v → ℕ)).filter
      (fun j => grade j = 2), ecoefM j * rowRet G d p yp ym S v j)
    (∑ j ∈ (retIdx (kStar d p) : Finset (nbhd G S v → ℕ)).filter
      (fun j => 3 ≤ grade j), ecoefM j * rowRet G d p yp ym S v j)
  have hB := abs_add_le (∑ j ∈ (retIdx (kStar d p) : Finset (nbhd G S v → ℕ)).filter
      (fun j => grade j = 1), ecoefM j * rowRet G d p yp ym S v j)
    (∑ j ∈ (retIdx (kStar d p) : Finset (nbhd G S v → ℕ)).filter
      (fun j => grade j = 2), ecoefM j * rowRet G d p yp ym S v j)
  have k1 : 0 ≤ aOf d p ^ 2 * (C₂ * ((p : ℝ) ^ 5 * rowX5 G d p yp ym S v + (p : ℝ) ^ 13 /
      (d : ℝ) ^ 2)) := by positivity
  have k2 : 0 ≤ aOf d p ^ 2 * (C₃ * ((p : ℝ) ^ 5 * rowX5 G d p yp ym S v +
      (p : ℝ) ^ 4 * Real.sqrt (lc * dc))) := by positivity
  have k3 : 0 ≤ aOf d p ^ 2 * (C₁ * ((p : ℝ) ^ 13 / (d : ℝ) ^ 2)) := by positivity
  have e : aOf d p ^ 2 * ((C₁ + C₂ + C₃) * ((p : ℝ) ^ 5 * rowX5 G d p yp ym S v +
      (p : ℝ) ^ 4 * Real.sqrt (lc * dc) + (p : ℝ) ^ 13 / (d : ℝ) ^ 2)) =
      aOf d p ^ 2 * (C₁ * ((p : ℝ) ^ 5 * rowX5 G d p yp ym S v +
        (p : ℝ) ^ 4 * Real.sqrt (lc * dc))) +
      aOf d p ^ 2 * (C₂ * ((p : ℝ) ^ 4 * Real.sqrt (lc * dc))) +
      aOf d p ^ 2 * (C₃ * ((p : ℝ) ^ 13 / (d : ℝ) ^ 2)) +
      aOf d p ^ 2 * (C₂ * ((p : ℝ) ^ 5 * rowX5 G d p yp ym S v + (p : ℝ) ^ 13 /
        (d : ℝ) ^ 2)) +
      aOf d p ^ 2 * (C₃ * ((p : ℝ) ^ 5 * rowX5 G d p yp ym S v +
        (p : ℝ) ^ 4 * Real.sqrt (lc * dc))) +
      aOf d p ^ 2 * (C₁ * ((p : ℝ) ^ 13 / (d : ℝ) ^ 2)) := by ring
  linarith

end SecC

end BiluLinial.Tight
