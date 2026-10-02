/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecC.F1
public import BiluLinial.Tight.SecC.ShiftMat
public import BiluLinial.Tight.SecA.Transfer
public import BiluLinial.Tight.SecA.Star
public import BiluLinial.Tight.Compare.Symm

/-!
# Sub-nodes of the contact row comparison (CR3, CR3′)

Source lines 1153–1190 (proof of CR1/CR3); AUDIT-C §4.2; `docs/tight/DR1_CHECK.md` §3; nodes
CR-* of `docs/tight/BP_SECC.md`. The proof follows the pattern of T.TRC (`core_transfer`):
(E4) at depth `k_*` pointwise in the core for the core-measurable family `F_σ = rowNum p A_σ B_σ`,
averaged over the own core law and divided by `a² F_H`.

* `rowRet j = E[∂^{2j}F(ξ)/Φ(ξ)]`, the retained term of (E4) under the actual law.
* `rowWt σ = a² Σ_{i∈N} (1 + r_i)⁴`, `r_i` the star scale at the own signs (`starScale`): the
  unmarked weight of T.MARK, grade one, summed over `i` (`Σ_i a⁴(1 + r_i)⁴ = a² rowWt`).
* `rowX5 = E[rowWt · a² |Σ_N G⁺_vj (G⁺_vj - G⁻_vj)|]`, the row term carrying the coefficient `p⁵`.

Nodes:
* **CR-REM** (`row_rem`, in `SecC/RowRem.lean`): A-REM (`CapPoint.trans_rem`) for `F`:
  `|E_{ν_K}(𝖦F - Σ_{j ∈ ret} c_j 𝖱∂^{2j}F)| ≤ C p e^{-p}/d · F_H`.
* **CR-RET** (`row_ret`): A-RET (`coreE_rad_div_eq`) for `F`:
  `E_{ν_K} 𝖱∂^{2j}F / F_H = rowRet j` (`∂^{2j}F = 0` at the sign vectors with `Φ = 0`, A-CLIP0).
* **CR-G0** (`row_grade0`): `rowRet 0 = a² 𝓡` (ROWF, `rowNum_eq`).
* **CR-GR** (`row_grades_le`, in `SecC/RowGrades.lean`): the retained grades `1 ≤ |j|_g ≤ k_*`:
  `|Σ_{j ≠ 0} c_j rowRet j| ≤ a² C (p⁵ X₅ + p⁴ √(λ_c δ_c) + p¹³/d²)`.
* **CR-X5** (`row_x5_split`, `row_x5_diff`, in `SecC/RowX5.lean`): `X₅ ≤ C √(λ_r ρ_r)` (CR3)
  and `X₅ ≤ C √(λ_r ρ_Δ)` (CR3′).

CR3 and CR3′ (`RowCompare.lean`) follow: `𝓡 - 𝖦F/(a²F_H) = -Rem/(a²F_H) - a⁻² Σ_{j≠0} c_j rowRet j`,
`a⁻² ≤ 4d` and `p e^{-p} ≤ p¹³/d²`.

**Checks.** `N = ∅`: `retIdx k = {0}`, so `Σ_{j≠0} = 0`, `X₅ = 0`, `rowRet 0 = 0 = a²𝓡`, and
`𝖦F = 𝖱F = 0`: every node is trivially true. One coordinate, `B = 0`, `A = (α₀)`: the grade-one
term is `(1/12) E[∂⁴F/Φ]` with `∂⁴F(0) = -24(p-1)(p-2)α₀³` (T.MARK check), of order
`p² a⁶ ≤ a² p⁴ √(λ_cδ_c)` once `λ_c, δ_c ≳ a⁴`, consistent with CR-GR. Zero source at `v`:
`A = B = 0`, `F ≡ 0`, all retained terms vanish.
-/

@[expose] public section

namespace BiluLinial.Tight

namespace SecC

universe u

open Matrix
open scoped ContDiff

/-! ### Definitions -/

section Defs

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The retained term `E[∂^{2j}F(ξ)/Φ(ξ)]` of (E4) for `F = rowNum` under the actual law. -/
noncomputable def rowRet (d p : ℕ) (yp ym : V → ℝ) (S : Finset V) (v : V)
    (j : nbhd G S v → ℕ) : ℝ :=
  lawE G p (aOf d p) yp ym S fun σ =>
    dEven (Finset.univ : Finset (nbhd G S v)).toList j (rowNum p (rootMat G (aOf d p) 1 yp σ S v)
        (rootMat G (aOf d p) (-1) ym σ S v)) (rootSigns G σ S v) /
      starPhi p (rootMat G (aOf d p) 1 yp σ S v) (rootMat G (aOf d p) (-1) ym σ S v)
        (rootSigns G σ S v)

/-- The unmarked weight `a² Σ_{i∈N} (1 + r_i)⁴` at the own signs. -/
noncomputable def rowWt (d p : ℕ) (yp ym : V → ℝ) (σ : Config V) (S : Finset V) (v : V) : ℝ :=
  aOf d p ^ 2 * ∑ i : nbhd G S v, (1 + starScale (aOf d p) (rootMat G (aOf d p) 1 yp σ S v)
    (rootMat G (aOf d p) (-1) ym σ S v) (rootSigns G σ S v) i) ^ 4

/-- The grade-one row term `X₅ = E[rowWt · a² |Σ_N G⁺_vj (G⁺_vj - G⁻_vj)|]`. -/
noncomputable def rowX5 (d p : ℕ) (yp ym : V → ℝ) (S : Finset V) (v : V) : ℝ :=
  lawE G p (aOf d p) yp ym S fun σ => rowWt G d p yp ym σ S v * (aOf d p ^ 2 *
    |∑ j ∈ nbhd G S v, greenP G (aOf d p) 1 yp σ S v j *
      (greenP G (aOf d p) 1 yp σ S v j - greenP G (aOf d p) (-1) ym σ S v j)|)

end Defs

/-! ### Star-level helpers -/

section Star

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Iterated partial derivatives are additive on `C^{|l|}` functions. -/
theorem pderivList_add : ∀ (l : List ι) {f g : (ι → ℝ) → ℝ},
    ContDiff ℝ (l.length : WithTop ℕ∞) f → ContDiff ℝ (l.length : WithTop ℕ∞) g →
      pderivList l (f + g) = pderivList l f + pderivList l g
  | [], _, _, _, _ => rfl
  | i :: l, f, g, hf, hg => by
    have hf1 : ContDiff ℝ ((l.length + 1 : ℕ) : WithTop ℕ∞) f := by simpa using hf
    have hg1 : ContDiff ℝ ((l.length + 1 : ℕ) : WithTop ℕ∞) g := by simpa using hg
    have hpd : pderiv i (f + g) = pderiv i f + pderiv i g := by
      funext x
      have hfd : DifferentiableAt ℝ f x := (hf1.differentiable (by norm_cast)) x
      have hgd : DifferentiableAt ℝ g x := (hg1.differentiable (by norm_cast)) x
      simp only [pderiv, Pi.add_apply]
      rw [fderiv_add hfd hgd]
      rfl
    rw [pderivList_cons, pderivList_cons, pderivList_cons, hpd]
    exact pderivList_add l (contDiff_pderiv hf1 i) (contDiff_pderiv hg1 i)

omit [Fintype ι] in
theorem pderivList_zero_fun (l : List ι) :
    pderivList l (fun _ : ι → ℝ => (0 : ℝ)) = fun _ => 0 := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    rw [pderivList_cons]
    have h : pderiv i (fun _ : ι → ℝ => (0 : ℝ)) = fun _ => 0 := by
      funext x
      simp [pderiv]
    rw [h, ih]

omit [DecidableEq ι] in
theorem sum_le_two_mul_grade_aux {j : ι → ℕ} (hadm : ∀ i, j i ≠ 1) :
    ∑ i, j i ≤ 2 * grade j := by
  rw [grade, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have := hadm i
  omega

omit [DecidableEq ι] in
theorem length_dEvenList_univ_aux (j : ι → ℕ) :
    (dEvenList (Finset.univ : Finset ι).toList j).length = 2 * ∑ i, j i := by
  rw [length_dEvenList, Finset.sum_map_toList, Finset.mul_sum]

omit [DecidableEq ι] in
theorem quadFn_zero_zero (Q : Matrix ι ι ℝ) : quadFn 0 0 Q = qForm Q := by
  funext x
  simp [quadFn]

omit [DecidableEq ι] in
/-- `F = rowNum` as a sum of two clipped observables of Section A. -/
theorem rowNum_eq_clipObs (p : ℕ) (A B : Matrix ι ι ℝ) :
    rowNum p A B = clipObs (quadFn 0 0 (((p : ℝ) - 1) • (A * A))) (p - 2) p A B +
      clipObs (quadFn 0 0 ((p : ℝ) • (A * B))) (p - 1) (p - 1) A B := by
  funext x
  simp only [rowNum, clipObs, quadFn_zero_zero, Pi.add_apply, qForm, smul_mulVec,
    dotProduct_smul, smul_eq_mul]

/-- A-CLIP0 for `F = rowNum`: derivatives of order `< p - 2` vanish where `q_A ≥ 1` or
`q_B ≥ 1`. -/
theorem pderivList_rowNum_eq_zero {p : ℕ} {A B : Matrix ι ι ℝ} (hA : A.PosSemidef)
    (hB : B.PosSemidef) (l : List ι) (hl : l.length + 3 ≤ p) {x : ι → ℝ}
    (hx : 1 ≤ qForm A x ∨ 1 ≤ qForm B x) : pderivList l (rowNum p A B) x = 0 := by
  have hg1 : ContDiff ℝ ∞ (quadFn 0 0 (((p : ℝ) - 1) • (A * A))) := by
    rw [quadFn_zero_zero]; exact contDiff_qForm' _
  have hg2 : ContDiff ℝ ∞ (quadFn 0 0 ((p : ℝ) • (A * B))) := by
    rw [quadFn_zero_zero]; exact contDiff_qForm' _
  have hc1 := SecA.contDiff_clipObs hg1 (p - 2) p A B
  have hc2 := SecA.contDiff_clipObs hg2 (p - 1) (p - 1) A B
  have hm1 : l.length ≤ min (p - 2) p - 1 := by omega
  have hm2 : l.length ≤ min (p - 1) (p - 1) - 1 := by omega
  rw [rowNum_eq_clipObs, pderivList_add l (hc1.of_le (by exact_mod_cast hm1))
    (hc2.of_le (by exact_mod_cast hm2)), Pi.add_apply,
    SecA.pderivList_clipObs_eq_zero hA hB hg1 l (by omega) hx,
    SecA.pderivList_clipObs_eq_zero hA hB hg2 l (by omega) hx, add_zero]

end Star

/-! ### CR-G0 and CR-RET -/

section Law

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable {d p : ℕ}

/-- **CR-G0**: the grade-zero retained term is `a² 𝓡` (ROWF). -/
theorem row_grade0 (hR : TRegime d p) {S : Finset V} {yp ym : V → ℝ} (hyp : ∀ i, 0 ≤ yp i)
    (hym : ∀ i, 0 ≤ ym i) {v : V} (hv : v ∈ S) :
    rowRet G d p yp ym S v 0 = aOf d p ^ 2 * rowMean G d p yp ym S v := by
  have hpt : ∀ σ, wt G p (aOf d p) yp ym σ S ≠ 0 →
      dEven (Finset.univ : Finset (nbhd G S v)).toList 0 (rowNum p (rootMat G (aOf d p) 1 yp σ S v)
          (rootMat G (aOf d p) (-1) ym σ S v)) (rootSigns G σ S v) /
        starPhi p (rootMat G (aOf d p) 1 yp σ S v) (rootMat G (aOf d p) (-1) ym σ S v)
          (rootSigns G σ S v) =
      aOf d p ^ 2 * (((p : ℝ) - 1) * ∑ j ∈ nbhd G S v, greenP G (aOf d p) 1 yp σ S v j ^ 2 -
        p * ∑ j ∈ nbhd G S v,
          greenP G (aOf d p) 1 yp σ S v j * greenP G (aOf d p) (-1) ym σ S v j) := by
    intro σ hσ
    obtain ⟨hα, hβ, -⟩ := root_F1 G hR hyp hym hv hσ
    have hΦ : 0 < starPhi p (rootMat G (aOf d p) 1 yp σ S v) (rootMat G (aOf d p) (-1) ym σ S v)
        (rootSigns G σ S v) := by
      rw [starPhi_eq hα hβ]
      exact mul_pos (pow_pos hα p) (pow_pos hβ p)
    rw [dEven_zero, rowNum_eq G hR hyp hym hv hσ]
    field_simp
  unfold rowRet rowMean incRowE
  rw [lawE_congr G hpt, lawE_const_mul, lawE_sub, lawE_const_mul, lawE_const_mul, lawE_sum,
    lawE_sum]

/-- **CR-RET**: retained terms of `F = rowNum` pass to the actual law (A-RET, A-CLIP0). -/
theorem row_ret : Eventually fun _ _ d p _ =>
    ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
      (S : Finset V) (lam : ℝ) (yp ym : V → ℝ) (v : V), CapCtx G d p S lam →
      InCube (lam * sOf d p) yp → InCube (lam * sOf d p) ym → v ∈ S →
      ∀ j ∈ (retIdx (kStar d p) : Finset (nbhd G S v → ℕ)),
        coreE G p (aOf d p) yp ym S v (fun σ => radE (dEven
            (Finset.univ : Finset (nbhd G S v)).toList j
            (rowNum p (rootMat G (aOf d p) 1 yp σ S v) (rootMat G (aOf d p) (-1) ym σ S v)))) /
          insFH G d p yp ym S v = rowRet G d p yp ym S v j := by
  refine SecA.eventually_regA.mono ?_
  rintro c₀ κ₀ d p h hRA V _ _ G _ S lam yp ym v hC hyp hym hv j hj
  classical
  have hR : TRegime d p := hRA.treg
  have hk := hRA.moment_order_le
  have hk' : kStarA d p = kStar d p := rfl
  have hp1 : 1 ≤ p := le_trans (by norm_num) hR.two_le_p
  have hyp0 : ∀ i, 0 ≤ yp i := fun i => (hyp i).1
  have hym0 : ∀ i, 0 ≤ ym i := fun i => (hym i).1
  let cp : CapPoint.{u} d p :=
    { V := V, G := G, S := S, lam := lam, yp := yp, ym := ym, ctx := hC, hyp := hyp, hym := hym }
  have hvS : v ∈ cp.S := hv
  have hPSD : ∀ σ, wtCore G p (aOf d p) yp ym σ S v ≠ 0 →
      (rootMat G (aOf d p) 1 yp σ S v).PosSemidef ∧
        (rootMat G (aOf d p) (-1) ym σ S v).PosSemidef := by
    intro σ hσ
    obtain ⟨h1, h2⟩ := posDef_of_wtCore_ne_zero G hσ
    exact ⟨(shift_branch G hyp0 le_rfl one_pos h1).1, (shift_branch G hym0 le_rfl one_pos h2).1⟩
  set F : Config V → (nbhd G S v → ℝ) → ℝ := fun σ =>
    if wtCore G p (aOf d p) yp ym σ S v ≠ 0 then
      rowNum p (rootMat G (aOf d p) 1 yp σ S v) (rootMat G (aOf d p) (-1) ym σ S v)
    else fun _ => 0 with hF
  have hFs : ∀ σ, wtCore G p (aOf d p) yp ym σ S v ≠ 0 → F σ =
      rowNum p (rootMat G (aOf d p) 1 yp σ S v) (rootMat G (aOf d p) (-1) ym σ S v) :=
    fun σ hσ => by rw [hF]; simp [hσ]
  have hFn : ∀ σ, ¬ wtCore G p (aOf d p) yp ym σ S v ≠ 0 → F σ = fun _ => 0 :=
    fun σ hσ => by rw [hF]; simp only [ne_eq, not_not] at hσ; simp [hσ]
  have hFc : ∀ σ σ' : Config V, (∀ e : Sym2 V, v ∉ e → σ e = σ' e) → F σ = F σ' := by
    intro σ σ' hσ
    have h1 := wtCore_coreInv G p (aOf d p) yp ym S v σ σ' hσ
    simp only [hF, rootMat_eq_of_offRoot G _ 1 yp S v hσ, rootMat_eq_of_offRoot G _ (-1) ym S v hσ]
    simp only at h1
    rw [h1]
  have hlen : (dEvenList (Finset.univ : Finset (nbhd G S v)).toList j).length + 3 ≤ p := by
    rw [length_dEvenList_univ_aux]
    have := sum_le_two_mul_grade_aux (mem_retIdx.1 hj).1
    have := (mem_retIdx.1 hj).2
    omega
  have hret := cp.coreE_radE_div_eq hRA hvS
    (fun σ => dEven (Finset.univ : Finset (nbhd G S v)).toList j (F σ))
    (fun σ σ' hσ => by simp only [hFc σ σ' hσ])
    (fun σ ξ _ hΦ => by
      by_cases hσ : wtCore G p (aOf d p) yp ym σ S v ≠ 0
      · change dEven (Finset.univ : Finset (nbhd G S v)).toList j (F σ) ξ = 0
        rw [hFs σ hσ, dEven_eq_pderivList]
        obtain ⟨hA, hB⟩ := hPSD σ hσ
        refine pderivList_rowNum_eq_zero hA hB _ hlen ?_
        have h0 : clipF (rootMat G (aOf d p) 1 yp σ S v) ξ ^ p *
            clipF (rootMat G (aOf d p) (-1) ym σ S v) ξ ^ p = 0 := hΦ
        rcases mul_eq_zero.1 h0 with h | h
        · left
          have := pow_eq_zero_iff (n := p) (by omega) |>.1 h
          simp only [clipF] at this
          have := le_max_left (1 - qForm (rootMat G (aOf d p) 1 yp σ S v) ξ) 0
          linarith
        · right
          have := pow_eq_zero_iff (n := p) (by omega) |>.1 h
          simp only [clipF] at this
          have := le_max_left (1 - qForm (rootMat G (aOf d p) (-1) ym σ S v) ξ) 0
          linarith
      · change dEven (Finset.univ : Finset (nbhd G S v)).toList j (F σ) ξ = 0
        rw [hFn σ hσ, dEven_eq_pderivList, pderivList_zero_fun])
  have hL : coreE G p (aOf d p) yp ym S v (fun σ => radE (dEven
        (Finset.univ : Finset (nbhd G S v)).toList j
        (rowNum p (rootMat G (aOf d p) 1 yp σ S v) (rootMat G (aOf d p) (-1) ym σ S v)))) =
      coreE G p (aOf d p) yp ym S v (fun σ => radE (dEven
        (Finset.univ : Finset (nbhd G S v)).toList j (F σ))) :=
    SecA.coreE_congr_of_supp G fun σ hσ => by rw [hFs σ hσ]
  rw [hL]
  refine hret.trans ?_
  unfold rowRet
  refine lawE_congr G fun σ hσ => ?_
  change dEven (Finset.univ : Finset (nbhd G S v)).toList j (F σ) (rootSigns G σ S v) /
      starPhi p (rootMat G (aOf d p) 1 yp σ S v) (rootMat G (aOf d p) (-1) ym σ S v)
        (rootSigns G σ S v) = _
  rw [hFs σ (wtCore_ne_zero_of_wt G hp1 hyp0 hym0 hv hσ)]

end Law

end SecC

end BiluLinial.Tight
