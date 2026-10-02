/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecC.RowG12Mom

/-!
# Row comparison, grade one (node CR-G1 of `docs/tight/BP_SECC.md`)

The retained multi-indices of grade one, `j = 2e_i`. See `BiluLinial.Tight.SecC.RowGrades`
for the parent CR-GR and the orders-of-magnitude checks.

**Proof.** The grade-one retained indices are among the `2e_i` (`g12_sum_grade1_le`), with
`c_{2e_i} = 1/12` and `∂^{2j} = ∂_i⁴` (`SecA.dEven_single_two`). At a supported signing,
`mark_grade_one` divided by `Φ` (`g12_grade1_star`) and summed over `i` gives
`(1000/12) a² (p⁵ W a²|Σ_N x(x - z)| + 4p⁴ (U⁺ + √U⁺ √U⁻))` (`g12_grade1_pt`), where
`U^± = Σ_i (1 + r_i)⁴ X^±_i` and the seven marks are absorbed by Cauchy–Schwarz over `j` and
over `i`. Under the law the first term is `p⁵ X₅` and `E[U⁺ + √U⁺ √U⁻] ≤ 2e²BK √(λ_c δ_c)`
(`g12_EU_le` with `‖(1 + r_i)⁴‖_{2k} ≤ B = 3·96⁴`).
-/

@[expose] public section

namespace BiluLinial.Tight

namespace SecC

universe u

open Matrix

section Main

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable {d p : ℕ}

/-- Pointwise grade-one bound at a supported signing. -/
theorem g12_grade1_pt (hR : TRegime d p) {S : Finset V} {yp ym : V → ℝ} (hyp : ∀ i, 0 ≤ yp i)
    (hym : ∀ i, 0 ≤ ym i) {v : V} (hv : v ∈ S) {σ : Config V}
    (hσ : wt G p (aOf d p) yp ym σ S ≠ 0) :
    ∑ i : nbhd G S v, 1 / 12 * |dEven (Finset.univ : Finset (nbhd G S v)).toList
        (Function.update 0 i 2)
        (rowNum p (rootMat G (aOf d p) 1 yp σ S v) (rootMat G (aOf d p) (-1) ym σ S v))
        (rootSigns G σ S v) /
      starPhi p (rootMat G (aOf d p) 1 yp σ S v) (rootMat G (aOf d p) (-1) ym σ S v)
        (rootSigns G σ S v)| ≤
      1000 / 12 * aOf d p ^ 2 * ((p : ℝ) ^ 5 * (rowWt G d p yp ym σ S v * (aOf d p ^ 2 *
          |∑ j ∈ nbhd G S v, greenP G (aOf d p) 1 yp σ S v j *
            (greenP G (aOf d p) 1 yp σ S v j - greenP G (aOf d p) (-1) ym σ S v j)|)) +
        4 * (p : ℝ) ^ 4 * (∑ i, (1 + g12r G d p yp ym σ S v i) ^ 4 * g12Xb G d p 1 yp σ S v i +
          Real.sqrt (∑ i, (1 + g12r G d p yp ym σ S v i) ^ 4 * g12Xb G d p 1 yp σ S v i) *
            Real.sqrt (∑ i, (1 + g12r G d p yp ym σ S v i) ^ 4 *
              g12Xb G d p (-1) ym σ S v i))) := by
  have ha := hR.aOf_pos
  have hp8 : 8 ≤ p := le_trans (by norm_num) hR.hp
  obtain ⟨hA, hB, hα, hβ⟩ := g12_supp G hR hyp hym hv hσ
  obtain ⟨-, -, -, -, hrp, hrm, -, -⟩ := root_F1 G hR hyp hym hv hσ
  set Sx := |∑ j ∈ nbhd G S v, greenP G (aOf d p) 1 yp σ S v j *
    (greenP G (aOf d p) 1 yp σ S v j - greenP G (aOf d p) (-1) ym σ S v j)| with hSx
  have hS1 : |∑ j, starRow (aOf d p) (rootMat G (aOf d p) 1 yp σ S v) (rootSigns G σ S v) j *
      (starRow (aOf d p) (rootMat G (aOf d p) 1 yp σ S v) (rootSigns G σ S v) j -
        starRow (-aOf d p) (rootMat G (aOf d p) (-1) ym σ S v) (rootSigns G σ S v) j)| = Sx := by
    rw [hSx, ← Finset.sum_coe_sort (nbhd G S v)]
    exact congrArg _ (Finset.sum_congr rfl fun j _ => by rw [hrp j, hrm j])
  have hpt : ∀ i : nbhd G S v, |dEven (Finset.univ : Finset (nbhd G S v)).toList
        (Function.update 0 i 2)
        (rowNum p (rootMat G (aOf d p) 1 yp σ S v) (rootMat G (aOf d p) (-1) ym σ S v))
        (rootSigns G σ S v) /
      starPhi p (rootMat G (aOf d p) 1 yp σ S v) (rootMat G (aOf d p) (-1) ym σ S v)
        (rootSigns G σ S v)| ≤
      1000 * aOf d p ^ 2 * (1 + g12r G d p yp ym σ S v i) ^ 4 *
        ((p : ℝ) ^ 5 * (aOf d p ^ 4 * Sx) + 4 * (p : ℝ) ^ 4 *
          (g12Xb G d p 1 yp σ S v i + Real.sqrt (g12Xb G d p 1 yp σ S v i) *
            Real.sqrt (g12Xb G d p (-1) ym σ S v i))) := by
    intro i
    rw [SecA.dEven_single_two (Finset.nodup_toList _) (Finset.mem_toList.2 (Finset.mem_univ i))]
    have h := g12_grade1_star hp8 ha hA hB hα hβ i
    rw [g12P_eq, g12M_eq, hS1] at h
    exact h
  have hterm : ∀ i : nbhd G S v, 1 / 12 * (1000 * aOf d p ^ 2 *
      (1 + g12r G d p yp ym σ S v i) ^ 4 *
        ((p : ℝ) ^ 5 * (aOf d p ^ 4 * Sx) + 4 * (p : ℝ) ^ 4 *
          (g12Xb G d p 1 yp σ S v i + Real.sqrt (g12Xb G d p 1 yp σ S v i) *
            Real.sqrt (g12Xb G d p (-1) ym σ S v i)))) =
      (1000 / 12 * aOf d p ^ 2 * (p : ℝ) ^ 5 * (aOf d p ^ 4 * Sx)) *
          (1 + g12r G d p yp ym σ S v i) ^ 4 +
        (4000 / 12 * aOf d p ^ 2 * (p : ℝ) ^ 4) *
          ((1 + g12r G d p yp ym σ S v i) ^ 4 * g12Xb G d p 1 yp σ S v i) +
        (4000 / 12 * aOf d p ^ 2 * (p : ℝ) ^ 4) *
          ((1 + g12r G d p yp ym σ S v i) ^ 4 * (Real.sqrt (g12Xb G d p 1 yp σ S v i) *
            Real.sqrt (g12Xb G d p (-1) ym σ S v i))) := fun i => by ring
  have hCS := g12_sum_wsqrt_le Finset.univ (fun i => (1 + g12r G d p yp ym σ S v i) ^ 4)
    (fun i => g12Xb G d p 1 yp σ S v i) (fun i => g12Xb G d p (-1) ym σ S v i)
    (fun i => by positivity) (fun i => g12Xb_nonneg G d p 1 yp σ S v i)
    (fun i => g12Xb_nonneg G d p (-1) ym σ S v i)
  have hβ0 : (0 : ℝ) ≤ 4000 / 12 * aOf d p ^ 2 * (p : ℝ) ^ 4 := by positivity
  calc _ ≤ ∑ i : nbhd G S v, 1 / 12 * (1000 * aOf d p ^ 2 * (1 + g12r G d p yp ym σ S v i) ^ 4 *
        ((p : ℝ) ^ 5 * (aOf d p ^ 4 * Sx) + 4 * (p : ℝ) ^ 4 *
          (g12Xb G d p 1 yp σ S v i + Real.sqrt (g12Xb G d p 1 yp σ S v i) *
            Real.sqrt (g12Xb G d p (-1) ym σ S v i)))) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hpt i) (by norm_num)
    _ = (1000 / 12 * aOf d p ^ 2 * (p : ℝ) ^ 5 * (aOf d p ^ 4 * Sx)) *
          ∑ i, (1 + g12r G d p yp ym σ S v i) ^ 4 +
        (4000 / 12 * aOf d p ^ 2 * (p : ℝ) ^ 4) *
          ∑ i, (1 + g12r G d p yp ym σ S v i) ^ 4 * g12Xb G d p 1 yp σ S v i +
        (4000 / 12 * aOf d p ^ 2 * (p : ℝ) ^ 4) *
          ∑ i, (1 + g12r G d p yp ym σ S v i) ^ 4 * (Real.sqrt (g12Xb G d p 1 yp σ S v i) *
            Real.sqrt (g12Xb G d p (-1) ym σ S v i)) := by
        rw [Finset.sum_congr rfl fun i _ => hterm i]
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ (1000 / 12 * aOf d p ^ 2 * (p : ℝ) ^ 5 * (aOf d p ^ 4 * Sx)) *
          ∑ i, (1 + g12r G d p yp ym σ S v i) ^ 4 +
        (4000 / 12 * aOf d p ^ 2 * (p : ℝ) ^ 4) *
          ∑ i, (1 + g12r G d p yp ym σ S v i) ^ 4 * g12Xb G d p 1 yp σ S v i +
        (4000 / 12 * aOf d p ^ 2 * (p : ℝ) ^ 4) *
          (Real.sqrt (∑ i, (1 + g12r G d p yp ym σ S v i) ^ 4 * g12Xb G d p 1 yp σ S v i) *
            Real.sqrt (∑ i, (1 + g12r G d p yp ym σ S v i) ^ 4 *
              g12Xb G d p (-1) ym σ S v i)) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hCS hβ0)
    _ = _ := by
        rw [rowWt_eq_g12r]
        ring

/-- CR-G1 at a fixed point of the regime, with explicit constant. -/
theorem g12_grade1_main (hR : TRegime d p) (hk : 32 * kIL d ≤ p) {S : Finset V} {lam : ℝ}
    (hC : CapCtx G d p S lam) {yp ym : V → ℝ} (hyp : InCube (lam * sOf d p) yp)
    (hym : InCube (lam * sOf d p) ym) {v : V} (hv : v ∈ S) {lr lc dc : ℝ} (hvl : vth d ≤ lr)
    (hlrc : lr ≤ lc) (hlcd : lc ≤ dc)
    (hS1 : incRowE G d p yp ym S v 1 yp / d ≤ lr)
    (hS2 : incRowE G d p yp ym S v (-1) ym / d ≤ dc)
    (hM1 : markE G d p yp ym S v 1 yp / (d : ℝ) ^ 2 ≤ lc)
    (hM2 : markE G d p yp ym S v (-1) ym / (d : ℝ) ^ 2 ≤ dc) :
    |∑ j ∈ (retIdx (kStar d p) : Finset (nbhd G S v → ℕ)).filter (fun j => grade j = 1),
        ecoefM j * rowRet G d p yp ym S v j| ≤
      aOf d p ^ 2 * (1000 * (1 + 8 * (Real.exp 2 * (3 * 96 ^ 4) * g12K)) *
        ((p : ℝ) ^ 5 * rowX5 G d p yp ym S v + (p : ℝ) ^ 4 * Real.sqrt (lc * dc))) := by
  have hyp0 : ∀ i, 0 ≤ yp i := fun i => (hyp i).1
  have hym0 : ∀ i, 0 ≤ ym i := fun i => (hym i).1
  have hK := g12K_pos
  set D : (nbhd G S v → ℕ) → Config V → ℝ := fun j σ =>
    dEven (Finset.univ : Finset (nbhd G S v)).toList j
        (rowNum p (rootMat G (aOf d p) 1 yp σ S v) (rootMat G (aOf d p) (-1) ym σ S v))
        (rootSigns G σ S v) /
      starPhi p (rootMat G (aOf d p) 1 yp σ S v) (rootMat G (aOf d p) (-1) ym σ S v)
        (rootSigns G σ S v) with hD
  have hret : ∀ j, rowRet G d p yp ym S v j = lawE G p (aOf d p) yp ym S (D j) := fun j => rfl
  set T := (retIdx (kStar d p) : Finset (nbhd G S v → ℕ)).filter (fun j => grade j = 1) with hT
  have hTm : ∀ j ∈ T, (∀ x, j x ≠ 1) ∧ grade j = 1 := fun j hj =>
    ⟨(mem_retIdx.1 (Finset.mem_filter.1 hj).1).1, (Finset.mem_filter.1 hj).2⟩
  have step1 : |∑ j ∈ T, ecoefM j * rowRet G d p yp ym S v j| ≤
      lawE G p (aOf d p) yp ym S
        (fun σ => ∑ i : nbhd G S v, 1 / 12 * |D (Function.update 0 i 2) σ|) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j ∈ T, |ecoefM j * rowRet G d p yp ym S v j|
        ≤ ∑ j ∈ T, |ecoefM j| * lawE G p (aOf d p) yp ym S (fun σ => |D j σ|) :=
          Finset.sum_le_sum fun j _ => by
            rw [abs_mul, hret]
            exact mul_le_mul_of_nonneg_left (g12_abs_lawE_le G _) (abs_nonneg _)
      _ ≤ ∑ i : nbhd G S v, |ecoefM (Function.update (0 : nbhd G S v → ℕ) i 2)| *
            lawE G p (aOf d p) yp ym S (fun σ => |D (Function.update 0 i 2) σ|) :=
          g12_sum_grade1_le T hTm
            (fun j => |ecoefM j| * lawE G p (aOf d p) yp ym S (fun σ => |D j σ|))
            (fun j => mul_nonneg (abs_nonneg _) (lawE_nonneg G fun σ _ => abs_nonneg _))
      _ = _ := by
          rw [lawE_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [SecA.ecoefM_single_two, lawE_const_mul,
            abs_of_pos (by norm_num : (0 : ℝ) < 1 / 12)]
  have hU : lawE G p (aOf d p) yp ym S (fun σ =>
      ∑ i, (1 + g12r G d p yp ym σ S v i) ^ 4 * g12Xb G d p 1 yp σ S v i +
        Real.sqrt (∑ i, (1 + g12r G d p yp ym σ S v i) ^ 4 * g12Xb G d p 1 yp σ S v i) *
          Real.sqrt (∑ i, (1 + g12r G d p yp ym σ S v i) ^ 4 * g12Xb G d p (-1) ym σ S v i)) ≤
      2 * (Real.exp 2 * (3 * 96 ^ 4) * g12K) * Real.sqrt (lc * dc) :=
    g12_EU_le G hR hk hC hyp hym hv hvl hlrc hlcd hS1 hS2 hM1 hM2
      (Y := fun i σ => (1 + g12r G d p yp ym σ S v i) ^ 4) (fun i σ => by positivity)
      (by norm_num) (fun i => g12_Y4_moment G hR hk hC hyp hym hv i)
  have hX5 : 0 ≤ rowX5 G d p yp ym S v :=
    lawE_nonneg G fun σ _ => mul_nonneg (rowWt_nonneg' G d p yp ym σ S v) (by positivity)
  have hs := Real.sqrt_nonneg (lc * dc)
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  set cK := Real.exp 2 * (3 * 96 ^ 4) * g12K with hcK
  have hcK0 : 0 ≤ cK := by positivity
  calc |∑ j ∈ T, ecoefM j * rowRet G d p yp ym S v j|
      ≤ lawE G p (aOf d p) yp ym S
          (fun σ => ∑ i : nbhd G S v, 1 / 12 * |D (Function.update 0 i 2) σ|) := step1
    _ ≤ lawE G p (aOf d p) yp ym S (fun σ =>
          1000 / 12 * aOf d p ^ 2 * ((p : ℝ) ^ 5 * (rowWt G d p yp ym σ S v * (aOf d p ^ 2 *
            |∑ j ∈ nbhd G S v, greenP G (aOf d p) 1 yp σ S v j *
              (greenP G (aOf d p) 1 yp σ S v j - greenP G (aOf d p) (-1) ym σ S v j)|)) +
          4 * (p : ℝ) ^ 4 *
            (∑ i, (1 + g12r G d p yp ym σ S v i) ^ 4 * g12Xb G d p 1 yp σ S v i +
              Real.sqrt (∑ i, (1 + g12r G d p yp ym σ S v i) ^ 4 * g12Xb G d p 1 yp σ S v i) *
                Real.sqrt (∑ i, (1 + g12r G d p yp ym σ S v i) ^ 4 *
                  g12Xb G d p (-1) ym σ S v i)))) :=
        lawE_mono G fun σ hσ => g12_grade1_pt G hR hyp0 hym0 hv hσ
    _ = 1000 / 12 * aOf d p ^ 2 * ((p : ℝ) ^ 5 * rowX5 G d p yp ym S v +
          4 * (p : ℝ) ^ 4 * lawE G p (aOf d p) yp ym S (fun σ =>
            ∑ i, (1 + g12r G d p yp ym σ S v i) ^ 4 * g12Xb G d p 1 yp σ S v i +
              Real.sqrt (∑ i, (1 + g12r G d p yp ym σ S v i) ^ 4 * g12Xb G d p 1 yp σ S v i) *
                Real.sqrt (∑ i, (1 + g12r G d p yp ym σ S v i) ^ 4 *
                  g12Xb G d p (-1) ym σ S v i))) := by
        rw [lawE_const_mul, lawE_add, lawE_const_mul, lawE_const_mul]
        rfl
    _ ≤ 1000 / 12 * aOf d p ^ 2 * ((p : ℝ) ^ 5 * rowX5 G d p yp ym S v +
          4 * (p : ℝ) ^ 4 * (2 * cK * Real.sqrt (lc * dc))) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl
          (mul_le_mul_of_nonneg_left hU (by positivity))) (by positivity)
    _ = aOf d p ^ 2 * (1000 / 12 * ((p : ℝ) ^ 5 * rowX5 G d p yp ym S v) +
          (8000 / 12 * cK) * ((p : ℝ) ^ 4 * Real.sqrt (lc * dc))) := by ring
    _ ≤ aOf d p ^ 2 * (1000 * (1 + 8 * cK) * ((p : ℝ) ^ 5 * rowX5 G d p yp ym S v) +
          1000 * (1 + 8 * cK) * ((p : ℝ) ^ 4 * Real.sqrt (lc * dc))) := by
        refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (sq_nonneg _)
        · exact mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
        · exact mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
    _ = _ := by ring

end Main

/-- **CR-G1** (grade one: `j = 2e_i`, `c_j = 1/12`, `∂^{2j} = ∂_i⁴`).

**Sketch.** At a supported signing (F1, `root_F1`) the star forms are physical: `x_j = G⁺_vj`,
`z_j = G⁻_vj`, `e_ij = G⁺_vvG⁺_ij - x_ix_j`, `f_ij` likewise; `Φ > 0`. `mark_grade_one` divided by
`Φ`: `|∂_i⁴F/Φ| ≤ 1000 a² a⁴(1 + r_i)⁴ (p⁵|Σ x(x - z)| + p⁴ Σ_j m_ij)`. Summed over `i`
(`Σ_i a⁴(1 + r_i)⁴ = a² rowWt`), the `p⁵` part is exactly `1000 a² p⁵ X₅`. The `p⁴` marks:
`a⁴Σ_i(1 + r_i)⁴ Σ_j x_j² = rowWt · R₊`; `Σ_{ij} a⁴ e_ij² ≤ 2a⁴G⁺_vv²‖G⁺[N,N]‖_F² + 2R₊²` (FROB)
and the same for `f`; the cross marks by Cauchy–Schwarz over `(i, j)`, e.g.
`Σ_{ij} a⁴(1 + r_i)⁴|x_j e_ij| ≤ D₄ √(a⁴|N|Σx²) √(a⁴Σe²)`. Expectations: Cauchy–Schwarz in the law
and `lawE_mul_le_vth` with the moments of the unmarked weights (`rowWt_moment_le`), with
`E R₊ ≤ λ_r/2`, `E R₋ ≤ δ_c/2`, `a⁴ E[G_vv²‖G[N,N]‖_F²] ≤ a⁴d² λ_c ≤ λ_c/4` (resp. `δ_c`); every
product is `≤ C √(λ_c δ_c)` by `λ_r ≤ λ_c ≤ δ_c`. -/
theorem row_grade1_le : ∃ C : ℝ, 0 < C ∧ Eventually fun _ _ d p _ =>
    ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
      (S : Finset V) (lam : ℝ) (yp ym : V → ℝ) (v : V), CapCtx G d p S lam →
      InCube (lam * sOf d p) yp → InCube (lam * sOf d p) ym → v ∈ S →
      ∀ lr lc dc : ℝ, vth d ≤ lr → lr ≤ lc → lc ≤ dc →
        incRowE G d p yp ym S v 1 yp / d ≤ lr → incRowE G d p yp ym S v (-1) ym / d ≤ dc →
        markE G d p yp ym S v 1 yp / (d : ℝ) ^ 2 ≤ lc →
        markE G d p yp ym S v (-1) ym / (d : ℝ) ^ 2 ≤ dc →
        |∑ j ∈ (retIdx (kStar d p) : Finset (nbhd G S v → ℕ)).filter (fun j => grade j = 1),
            ecoefM j * rowRet G d p yp ym S v j| ≤
          aOf d p ^ 2 * (C * ((p : ℝ) ^ 5 * rowX5 G d p yp ym S v +
            (p : ℝ) ^ 4 * Real.sqrt (lc * dc))) := by
  refine ⟨1000 * (1 + 8 * (Real.exp 2 * (3 * 96 ^ 4) * g12K)),
    by have := g12K_pos; positivity, ((eventually_regime 1).and eventually_kIL32).mono ?_⟩
  rintro c₀ κ₀ d p h ⟨⟨hR, -, -⟩, hk⟩ V _ _ G _ S lam yp ym v hC hyp hym hv lr lc dc hvl hlrc
    hlcd hS1 hS2 hM1 hM2
  exact g12_grade1_main G hR hk hC hyp hym hv hvl hlrc hlcd hS1 hS2 hM1 hM2

end SecC

end BiluLinial.Tight
