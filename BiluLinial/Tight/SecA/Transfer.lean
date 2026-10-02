/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecA.Moments

/-!
# Averaged remainders, retained terms and the generic transfer (nodes `A-CNT`, `A-E6`,
`A-CREM`, `A-REM`, `A-RET`, `A-HGR`, `A-TRANS`)

Source lines 337–367 (averaged remainders, retained terms, (E6)); AUDIT-A §2.5–§2.8.

* `A-CNT` (`sum_topIdx_prod_pow_le`): for `x, T > 0`, `xT < 1`,
  `Σ_{|j|_g = k+1} Π_i x^{j_i} ≤ T^{-(k+1)} (1 + x²T/(1 - xT))^{|ι|}`.
  Proof: `T^{k+1} = Π T^{j_i - 1}`
  over active coordinates, so the sum is at most `Π_i (1 + Σ_{a ≥ 2} x^a T^{a-1})`. Used with
  `T = 1/(2x)` (CREM: `(2x)^{k+1}(1+x)^{|ι|}`) and `T = 1/(d x²)` (HGR: `(d x²)^{k+1} e²`).
* `A-E6` (`RegA.E6`), (E6) with `(C₁, C₂) = (8, 8)`:
  `p 40^p (8p)^{4k_*+4} 8^{k_*+1} d^{-k_*} ≤ e^{-p}`. Proof: the coefficient of `k_*` in the
  logarithm, `4 log(8p) + log 8 - log d ≤ 5 log 8 - (9/17) log d`, is negative, so `k_* ≥ 16p/log d`
  may be used; the coefficient of `p` is then `≤ log 40 + 0.42 + 128/17 - 16 < -4`.
* `A-CREM` (`CapPoint.crem`): `E_{ν_K}[m Σ_{|j|_g = k+1} Π_i b_i^{j_i}] ≤ M (5/d)^{k+1} e³` when
  the own-core moments of `m` are `≤ Mⁿ` (`2n ≤ p`) and `2(2k+3) ≤ p`.
  Proof: `b_i ≤ (1/d)(h⁺_{K,i} +
  h⁻_{K,i})` (`a² s² ≤ 1/d`), so `‖b_i‖_n ≤ 2.01/d` by (M3); `A-HOLD` with `n = 1 + Σ j_i ≤ 2k+3`;
  `A-CNT` with `x = 2.01/d`, `|N| ≤ d`.
* `A-REM` (`CapPoint.trans_rem`): the averaged (E4) remainder at depth `k_*`, divided by the floor,
  is `≤ M e^{-p}/d` (E4 with constant 2, `A-CREM`, (M4), `A-E6`).
* `A-RET` (`CapPoint.coreE_radE_div_eq`): retained terms pass to the actual law exactly:
  `E_{ν_K} 𝖱 R / F_H = E_H[R(ξ)/Φ(ξ)]` if `R` vanishes at the sign vectors where `Φ = 0` (`A-INS`).
* `A-HGR` (`CapPoint.hgr`): if `|R_j| ≤ m Π_i λ_i^{2 j_i}` under the actual law, with moments
  `≤ Mⁿ`, `≤ Lⁿ` (`2n ≤ p`), `d L² ≥ 2` and `d L⁴ ≤ 1/2`, then the retained grades `2 … k` sum to
  at most `2 e² M (d L⁴)²` (`A-HOLD`, `A-CNT` with `T = 1/(dL⁴)`).
* `A-TRANS` (`CapPoint.trans`): the generic transfer of AUDIT-A §2.8: for a core-measurable
  observable family `F` with sup majorant (`A-E5`) and endpoint majorant (`A-MAJ` at the own signs),
  `|E_{ν_K}(𝖦F - 𝖱F)/F_H - (1/12) Σ_i E_H[∂_i⁴F/Φ]| ≤ 2 e² M_E (d L⁴)² + M e^{-p}/d`.
  Proof: grade `0` of (E4) is `𝖱F`; the other retained terms pass to the actual law (`A-RET`); the
  grade-one indices are exactly the `2 e_i` (`retIdx_filter_grade_one`, `c_2 = 1/12`,
  `∂^{2·2e_i} = ∂_i⁴`); grades `≥ 2` by `A-HGR` (`|c_j| ≤ 1`), the remainder by `A-REM`.

Helpers: `SecA.abs_wavg_le_of_supp`, `SecA.wavg_mul_prod_pow_le` (`A-HOLD` with one distinguished
factor), `SecA.sum_topIdx_le_exp` (`A-CNT` with `xT ≤ 1/2`, `|ι| ≤ D`), `SecA.rootMat_diag_mem`
(`0 ≤ R_ii ≤ (M⁻¹)_ii/d`), `CapPoint.bdiag_moment` (`E_{ν_K}(b_i⁺)ⁿ ≤ (2(1+2ε)/d)ⁿ`),
`CapPoint.starPhi_xi_pos`, `CapPoint.card_N_le`.
-/

@[expose] public section

universe u

namespace BiluLinial.Tight

open Matrix Finset

/-- `A-CNT`: the generating-function bound for remainder multi-indices. -/
theorem SecA.sum_topIdx_prod_pow_le {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ) {x T : ℝ}
    (hx : 0 < x) (hT : 0 < T) (hxT : x * T < 1) :
    ∑ j ∈ (topIdx k : Finset (ι → ℕ)), ∏ i, x ^ j i ≤
      (1 / T) ^ (k + 1) * (1 + x ^ 2 * T / (1 - x * T)) ^ Fintype.card ι := by
  let w : ℕ → ℝ := fun a => if a = 1 then 0 else x ^ a * T ^ (a - 1)
  have hw0 : ∀ a, 0 ≤ w a := fun a => by
    simp only [w]; split_ifs
    · exact le_rfl
    · positivity
  have key : ∀ j ∈ (topIdx k : Finset (ι → ℕ)),
      ∏ i, x ^ j i = (1 / T) ^ (k + 1) * ∏ i, w (j i) := by
    intro j hj
    obtain ⟨h1, hg⟩ := mem_topIdx.1 hj
    have e : ∏ i, w (j i) = (∏ i, x ^ j i) * T ^ (k + 1) := by
      rw [← hg, grade, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      simp only [w, ite_eq_right (h1 i)]
    rw [e, mul_comm (∏ i, x ^ j i), ← mul_assoc, ← mul_pow, one_div_mul_cancel hT.ne',
      one_pow, one_mul]
  have hxT0 : 0 < 1 - x * T := by linarith
  have hgeom : ∑ a ∈ Finset.range (k + 3), w a ≤ 1 + x ^ 2 * T / (1 - x * T) := by
    rw [Finset.sum_range_succ', Finset.sum_range_succ']
    have h0 : w (0 + 1) = 0 := by simp [w]
    have h00 : w 0 = 1 := by simp [w]
    have hs : ∑ a ∈ Finset.range (k + 1), w (a + 1 + 1) =
        x ^ 2 * T * ∑ a ∈ Finset.range (k + 1), (x * T) ^ a := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [w, show a + 1 + 1 ≠ 1 by omega, ite_false, show a + 1 + 1 - 1 = a + 1 by omega]
      ring
    have hg : ∑ a ∈ Finset.range (k + 1), (x * T) ^ a ≤ 1 / (1 - x * T) := by
      rw [geom_sum_eq (by linarith) (k + 1), ← neg_sub 1 ((x * T) ^ (k + 1)), ← neg_sub 1 (x * T),
        neg_div_neg_eq]
      exact div_le_div_of_nonneg_right (by linarith [pow_nonneg (mul_pos hx hT).le (k + 1)])
        hxT0.le
    rw [h0, h00, hs]
    have := mul_le_mul_of_nonneg_left hg (by positivity : (0 : ℝ) ≤ x ^ 2 * T)
    rw [mul_one_div] at this
    linarith
  calc ∑ j ∈ (topIdx k : Finset (ι → ℕ)), ∏ i, x ^ j i
      = ∑ j ∈ (topIdx k : Finset (ι → ℕ)), (1 / T) ^ (k + 1) * ∏ i, w (j i) :=
        Finset.sum_congr rfl key
    _ = (1 / T) ^ (k + 1) * ∑ j ∈ (topIdx k : Finset (ι → ℕ)), ∏ i, w (j i) := by
        rw [Finset.mul_sum]
    _ ≤ (1 / T) ^ (k + 1) * ∑ j ∈ Fintype.piFinset (fun _ : ι => Finset.range (k + 3)),
          ∏ i, w (j i) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.filter_subset _ _) fun j _ _ => Finset.prod_nonneg fun i _ => hw0 _)
          (by positivity)
    _ = (1 / T) ^ (k + 1) * ∏ _i : ι, ∑ a ∈ Finset.range (k + 3), w a := by
        rw [Finset.prod_univ_sum]
    _ = (1 / T) ^ (k + 1) * (∑ a ∈ Finset.range (k + 3), w a) ^ Fintype.card ι := by
        rw [Finset.prod_const, Finset.card_univ]
    _ ≤ (1 / T) ^ (k + 1) * (1 + x ^ 2 * T / (1 - x * T)) ^ Fintype.card ι :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Finset.sum_nonneg fun a _ => hw0 a)
          hgeom _) (by positivity)

namespace SecA

/-! ### Helpers -/

/-- `|E f| ≤ E g` when `|f| ≤ g` on the support of the weights. -/
theorem abs_wavg_le_of_supp {Ω : Type*} [Fintype Ω] {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω)
    {f g : Ω → ℝ} (h : ∀ ω, 0 < w ω → |f ω| ≤ g ω) : |wavg w f| ≤ wavg w g := by
  refine abs_le.2 ⟨?_, wavg_mono' hw fun ω hω => (le_abs_self _).trans (h ω hω)⟩
  have h1 := wavg_mono' hw (f := fun ω => -g ω) (g := f) fun ω hω => by
    have := h ω hω
    have := neg_abs_le (f ω)
    linarith
  have e : wavg w (fun ω => -g ω) = -wavg w g := by
    rw [show (fun ω => -g ω) = fun ω => (-1) * g ω by funext ω; ring, wavg_const_mul]
    ring
  linarith

/-- Hölder with one distinguished factor: `E[Y Π X_i^{e_i}] ≤ M Π c_i^{e_i}` when
`n = 1 + Σ e_i`, `E Y^n ≤ M^n` and `E X_i^n ≤ c_i^n` (`A-HOLD` on `Option ι`). -/
theorem wavg_mul_prod_pow_le {Ω ι : Type*} [Fintype Ω] [Fintype ι] {w : Ω → ℝ}
    (hw : ∀ ω, 0 ≤ w ω) (Y : Ω → ℝ) (hY : ∀ ω, 0 ≤ Y ω) (X : ι → Ω → ℝ)
    (hX : ∀ i ω, 0 ≤ X i ω) (e : ι → ℕ) {n : ℕ} (hn : 1 + ∑ i, e i = n) {M : ℝ} (hM : 0 < M)
    (c : ι → ℝ) (hc : ∀ i, 0 < c i) (hYm : wavg w (fun ω => Y ω ^ n) ≤ M ^ n)
    (hXm : ∀ i, 0 < e i → wavg w (fun ω => X i ω ^ n) ≤ c i ^ n) :
    wavg w (fun ω => Y ω * ∏ i, X i ω ^ e i) ≤ M * ∏ i, c i ^ e i := by
  have h := wavg_prod_pow_le hw (fun o : Option ι => fun ω => o.elim (Y ω) (fun i => X i ω))
    (fun o ω => by cases o <;> simp [hY, hX]) (fun o => o.elim 1 e) n
    (by rw [Fintype.sum_option]; simpa using hn) (by omega) (fun o => o.elim M c)
    (fun o => by cases o <;> simp [hM, hc]) (fun o ho => by
      cases o with
      | none => simpa using hYm
      | some i => simpa using hXm i ho)
  simpa [Fintype.prod_option] using h

/-- `(1 + x)^n ≤ e^{x D}` for `x ≥ 0`, `n ≤ D`. -/
theorem one_add_pow_le_exp {x : ℝ} (hx : 0 ≤ x) {n : ℕ} {D : ℝ} (hn : (n : ℝ) ≤ D) :
    (1 + x) ^ n ≤ Real.exp (x * D) := by
  calc (1 + x) ^ n ≤ Real.exp x ^ n :=
        pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp x]) n
    _ = Real.exp (n * x) := (Real.exp_nat_mul x n).symm
    _ ≤ Real.exp (x * D) := Real.exp_le_exp.2 (by nlinarith)

/-- `A-CNT` with `x T ≤ 1/2` and `|ι| ≤ D`:
`Σ_{|j|_g = g+1} Π x^{j_i} ≤ T^{-(g+1)} e^{2 x² T D}`. -/
theorem sum_topIdx_le_exp {ι : Type*} [Fintype ι] [DecidableEq ι] (g : ℕ) {x T D : ℝ}
    (hx : 0 < x) (hT : 0 < T) (hxT : x * T ≤ 1 / 2) (hD : (Fintype.card ι : ℝ) ≤ D) :
    ∑ j ∈ (topIdx g : Finset (ι → ℕ)), ∏ i, x ^ j i ≤
      (1 / T) ^ (g + 1) * Real.exp (2 * x ^ 2 * T * D) := by
  have h := sum_topIdx_prod_pow_le (ι := ι) g hx hT (by linarith)
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  have h1 : x ^ 2 * T / (1 - x * T) ≤ 2 * x ^ 2 * T := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [mul_pos (pow_pos hx 2) hT]
  have h0 : 0 ≤ x ^ 2 * T / (1 - x * T) := div_nonneg (by positivity) (by linarith)
  calc (1 + x ^ 2 * T / (1 - x * T)) ^ Fintype.card ι ≤ (1 + 2 * x ^ 2 * T) ^ Fintype.card ι :=
        pow_le_pow_left₀ (by linarith) (by linarith) _
    _ ≤ Real.exp (2 * x ^ 2 * T * D) := one_add_pow_le_exp (by positivity) hD

theorem abs_ecoefM_le_one {ι : Type*} [Fintype ι] (j : ι → ℕ) : |ecoefM j| ≤ 1 := by
  unfold ecoefM
  rw [Finset.abs_prod]
  exact Finset.prod_le_one₀ (fun i _ => abs_nonneg _) (fun i _ => abs_ecoef_le_one _)

/-- Admissible multi-indices have `Σ j_i ≤ 2 |j|_g`. -/
theorem sum_le_two_mul_grade' {ι : Type*} [Fintype ι] {j : ι → ℕ} (hadm : ∀ i, j i ≠ 1) :
    ∑ i, j i ≤ 2 * grade j := by
  unfold grade
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => by have := hadm i; omega

section Single

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
/-- `∂^{2 e_i·2} = ∂_i⁴` (the grade-one multi-index `2 e_i`). -/
theorem dEven_single_two {l : List ι} (hl : l.Nodup) {i : ι} (hi : i ∈ l)
    (f : (ι → ℝ) → ℝ) : dEven l (Function.update 0 i 2) f = (pderiv i)^[4] f := by
  induction l with
  | nil => simp at hi
  | cons x l ih =>
    rw [dEven_cons]
    have hxl : x ∉ l := (List.nodup_cons.1 hl).1
    by_cases hx : x = i
    · subst hx
      rw [Function.update_self, dEven_congr (j' := 0) (fun y hy => by
        rw [Function.update_of_ne (by rintro rfl; exact hxl hy)]), dEven_zero]
    · rw [Function.update_of_ne hx]
      have hi' : i ∈ l := by
        rcases List.mem_cons.1 hi with h | h
        · exact absurd h.symm hx
        · exact h
      simpa using ih (List.nodup_cons.1 hl).2 hi'

theorem grade_single_two (i : ι) : grade (Function.update (0 : ι → ℕ) i 2) = 1 := by
  rw [grade_update (j := 0) (i := i) rfl 2]
  simp

theorem ecoefM_single_two (i : ι) : ecoefM (Function.update (0 : ι → ℕ) i 2) = 1 / 12 := by
  rw [ecoefM_update (j := 0) (i := i) rfl 2, ecoefM_zero, ecoef_two, mul_one]

theorem eq_single_two_of_grade_one {j : ι → ℕ} (hadm : ∀ x, j x ≠ 1) (hg : grade j = 1) :
    ∃ i, j = Function.update (0 : ι → ℕ) i 2 := by
  have hne : ∃ i, j i - 1 ≠ 0 := by
    by_contra h
    push Not at h
    have : grade j = 0 := Finset.sum_eq_zero fun i _ => h i
    omega
  obtain ⟨i, hi⟩ := hne
  have hle : ∀ x, j x - 1 ≤ grade j := fun x =>
    Finset.single_le_sum (f := fun x => j x - 1) (fun _ _ => Nat.zero_le _) (Finset.mem_univ x)
  have hji : j i = 2 := by
    have := hle i
    have := hadm i
    omega
  refine ⟨i, funext fun x => ?_⟩
  by_cases hx : x = i
  · subst hx
    simp [hji]
  · rw [Function.update_of_ne hx]
    have hp := Finset.sum_pair (f := fun y => j y - 1) (Ne.symm hx)
    have h2 : (j i - 1) + (j x - 1) ≤ grade j := by
      rw [← hp]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        fun _ _ _ => Nat.zero_le _
    have := hadm x
    simp only [Pi.zero_apply]
    omega

omit [Fintype ι] in
theorem single_two_injective :
    Function.Injective (fun i : ι => Function.update (0 : ι → ℕ) i 2) := by
  intro i i' h
  by_contra hne
  have := congrFun h i
  simp [Function.update_of_ne hne] at this

/-- The grade-one retained multi-indices are exactly the `2 e_i`. -/
theorem retIdx_filter_grade_one {k : ℕ} (hk : 1 ≤ k) :
    (retIdx k : Finset (ι → ℕ)).filter (fun j => grade j = 1) =
      Finset.univ.image (fun i => Function.update (0 : ι → ℕ) i 2) := by
  ext j
  simp only [Finset.mem_filter, mem_retIdx, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨hadm, -⟩, hg⟩
    obtain ⟨i, rfl⟩ := eq_single_two_of_grade_one hadm hg
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    refine ⟨⟨fun x => ?_, ?_⟩, grade_single_two i⟩
    · by_cases hx : x = i
      · subst hx
        simp
      · rw [Function.update_of_ne hx]
        simp
    · rw [grade_single_two]
      exact hk

end Single

/-- Root diagonal entries on a good core: `0 ≤ R_ii ≤ (M⁻¹)_ii / d` (`a² s² ≤ 1/d`). -/
theorem rootMat_diag_mem {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {d p : ℕ} (hR : TRegime d p) {τ : ℝ} {y : V → ℝ}
    (hy : InCube (sOf d p) y) {σ : Config V} {S : Finset V} {v : V}
    (hP : (precCore G (aOf d p) τ y σ S v).PosDef) (i : nbhd G S v) :
    0 ≤ rootMat G (aOf d p) τ y σ S v i i ∧
      rootMat G (aOf d p) τ y σ S v i i ≤ (1 / d) * (precCore G (aOf d p) τ y σ S v)⁻¹ i i := by
  have hy0 : ∀ j, 0 ≤ y j := fun j => (hy j).1
  have hc0 : 0 ≤ (precCore G (aOf d p) τ y σ S v)⁻¹ i i := (hP.inv.diag_pos).le
  have hD : 1 ≤ diagD G (aOf d p) y S v := FloorIns.one_le_diagD G _ hy0 S v
  have hd : (0 : ℝ) < d := lt_of_lt_of_le (by norm_num) hR.ten_pow_six_le_d
  have e : rootMat G (aOf d p) τ y σ S v i i =
      aOf d p ^ 2 * y v * y i / diagD G (aOf d p) y S v *
        (precCore G (aOf d p) τ y σ S v)⁻¹ i i := by
    simp only [rootMat, coreGreen, Matrix.of_apply]
    rw [mul_right_comm (Real.sqrt (y i)), Real.mul_self_sqrt (hy0 i)]
    ring
  have hs := sOf_le_two hR
  have hκ := d_mul_kappa_le_one hR
  have hc1 : aOf d p ^ 2 * y v * y i / diagD G (aOf d p) y S v ≤ 1 / d := by
    have h1 : aOf d p ^ 2 * y v * y i / diagD G (aOf d p) y S v ≤ aOf d p ^ 2 * y v * y i :=
      div_le_self (by have := hy0 v; have := hy0 i; positivity) hD
    have h2 : aOf d p ^ 2 * y v * y i ≤ aOf d p ^ 2 * sOf d p * sOf d p := by
      have := mul_le_mul (hy v).2 (hy i).2 (hy0 i) (le_trans (hy0 v) (hy v).2)
      have ha := sq_nonneg (aOf d p)
      nlinarith
    have h3 : aOf d p ^ 2 * sOf d p * sOf d p ≤ 1 / d := by
      rw [le_div_iff₀ hd]
      nlinarith
    linarith
  have hc10 : 0 ≤ aOf d p ^ 2 * y v * y i / diagD G (aOf d p) y S v := by
    have := hy0 v; have := hy0 i; positivity
  rw [e]
  exact ⟨mul_nonneg hc10 hc0, mul_le_mul_of_nonneg_right hc1 hc0⟩

end SecA

/-- `A-E6`: the floor loss of the final remainder is exponentially small. -/
theorem RegA.E6 {d p : ℕ} (hR : RegA d p) :
    (p : ℝ) * 40 ^ p * (8 * (p : ℝ)) ^ (4 * kStarA d p + 4) * 8 ^ (kStarA d p + 1) /
        (d : ℝ) ^ kStarA d p ≤ Real.exp (-(p : ℝ)) := by
  have hd := hR.d_pos
  have hp := hR.p_pos
  have hp6 : (10 : ℝ) ^ 6 ≤ p := by exact_mod_cast hR.treg.hp
  have hL400 : 400 ≤ Real.log d := hR.logd
  have hLp : 120 * Real.log d ≤ p := hR.plog
  have hkge : 16 * (p : ℝ) / Real.log d ≤ kStarA d p := hR.kStar_ge
  have hLpos : 0 < Real.log d := by linarith
  have hlogp : 17 * Real.log p ≤ 2 * Real.log d := by
    have h := Real.log_le_log (by positivity) hR.p_pow_seventeen_le
    rw [Real.log_pow, Real.log_pow] at h
    push_cast at h
    linarith
  have hl2 : Real.log 2 < 6931471808 / 10 ^ 10 := by
    have := Real.log_two_lt_d9; norm_num at this ⊢; linarith
  have hl8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  have hl40 : Real.log 40 ≤ 6 * Real.log 2 := by
    have : Real.log 40 ≤ Real.log (2 ^ 6) := Real.log_le_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at this; norm_num at this; linarith
  have hl2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set k : ℕ := kStarA d p with hk
  set P : ℝ := (p : ℝ) with hP
  set L : ℝ := Real.log d with hL
  set c : ℝ := 5 * Real.log 8 + 4 * Real.log P - L with hc
  have hc_le : c ≤ 104 / 10 - 9 / 17 * L := by rw [hc]; linarith
  have hc_neg : c ≤ 0 := by linarith
  have hkc : (k : ℝ) * c ≤ 16 * P / L * c := mul_le_mul_of_nonpos_right hkge hc_neg
  have hkc2 : 16 * P / L * c ≤ 16 * P / L * (104 / 10 - 9 / 17 * L) :=
    mul_le_mul_of_nonneg_left hc_le (by positivity)
  have hexp : 16 * P / L * (104 / 10 - 9 / 17 * L) = 1664 / 10 * (P / L) - 144 / 17 * P := by
    field_simp
    ring
  have hPL : P / L ≤ P / 400 := div_le_div_of_nonneg_left (by positivity) (by norm_num) hL400
  have h8p : (0 : ℝ) < 8 * P := by positivity
  have hpos : 0 < P * 40 ^ p * (8 * P) ^ (4 * k + 4) * 8 ^ (k + 1) / (d : ℝ) ^ k := by
    positivity
  have hlog : Real.log (P * 40 ^ p * (8 * P) ^ (4 * k + 4) * 8 ^ (k + 1) / (d : ℝ) ^ k) =
      Real.log P + P * Real.log 40 + (4 * k + 4) * (Real.log 8 + Real.log P) +
        (k + 1) * Real.log 8 - k * L := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow, Real.log_mul (by norm_num) hp.ne']
    push_cast
    ring
  rw [← Real.exp_log hpos, Real.exp_le_exp, hlog]
  have e : Real.log P + P * Real.log 40 + (4 * k + 4) * (Real.log 8 + Real.log P) +
      (k + 1) * Real.log 8 - k * L =
      5 * Real.log P + 5 * Real.log 8 + P * Real.log 40 + k * c := by
    rw [hc]; ring
  rw [e]
  have h40 : P * Real.log 40 ≤ P * (6 * Real.log 2) := mul_le_mul_of_nonneg_left hl40 hp.le
  have h40' : P * (6 * Real.log 2) ≤ P * (6 * (6931471808 / 10 ^ 10)) :=
    mul_le_mul_of_nonneg_left (by linarith) hp.le
  linarith

namespace CapPoint

variable {d p : ℕ} (cp : CapPoint.{u} d p)

/-- The coordinates of `N_S(v)` as a list (each exactly once). -/
noncomputable def lN (v : cp.V) : List (cp.N v) := (Finset.univ : Finset (cp.N v)).toList

/-- `b_i = A_ii + B_ii`. -/
noncomputable def bdiag (σ : Config cp.V) (v : cp.V) (i : cp.N v) : ℝ :=
  cp.A σ v i i + cp.B σ v i i

theorem lN_nodup (v : cp.V) : (cp.lN v).Nodup := Finset.nodup_toList _

theorem mem_lN {v : cp.V} (i : cp.N v) : i ∈ cp.lN v := Finset.mem_toList.2 (Finset.mem_univ i)

/-- `|N_S(v)| ≤ d`. -/
theorem card_N_le (v : cp.V) : (Fintype.card (cp.N v) : ℝ) ≤ d := by
  have h1 : (cp.N v).card ≤ cp.G.degree v := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    refine Finset.card_le_card fun x hx => ?_
    rw [SimpleGraph.mem_neighborFinset]
    simp only [CapPoint.N, nbhd, Finset.mem_filter] at hx
    exact hx.2
  rw [Fintype.card_coe]
  exact_mod_cast h1.trans (cp.ctx.deg v)

theorem coreE_fadd (v : cp.V) (f g : Config cp.V → ℝ) :
    cp.coreE v (fun σ => f σ + g σ) = cp.coreE v f + cp.coreE v g := SecA.wavg_add _ _ _

theorem coreE_fsum (v : cp.V) {κ : Type*} (s : Finset κ) (f : κ → Config cp.V → ℝ) :
    cp.coreE v (fun σ => ∑ u ∈ s, f u σ) = ∑ u ∈ s, cp.coreE v (f u) := wavg_sum _ _

theorem coreE_fconst_mul (v : cp.V) (c : ℝ) (f : Config cp.V → ℝ) :
    cp.coreE v (fun σ => c * f σ) = c * cp.coreE v f := SecA.wavg_const_mul _ _ _

/-- `|E_{ν_K} f| ≤ E_{ν_K} g` when `|f| ≤ g` on the core support. -/
theorem abs_coreE_le (v : cp.V) {f g : Config cp.V → ℝ}
    (h : ∀ σ, 0 < wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v → |f σ| ≤ g σ) :
    |cp.coreE v f| ≤ cp.coreE v g :=
  SecA.abs_wavg_le_of_supp (fun σ => SecA.wtCore_nonneg cp.G _ _ _ _ σ _ _) h

/-- `F_H > 0` (from the floor). -/
theorem FH_pos' (hR : RegA d p) {v : cp.V} (hv : v ∈ cp.S) : 0 < cp.FH v :=
  pos_of_mul_pos_right (lt_of_lt_of_le one_pos (cp.floor hR hv)) (by positivity)

/-- `Φ(ξ_σ) > 0` at a supported signing. -/
theorem starPhi_xi_pos (hR : RegA d p) {v : cp.V} (hv : v ∈ cp.S) {σ : Config cp.V}
    (hσ : wt cp.G p (aOf d p) cp.yp cp.ym σ cp.S ≠ 0) :
    0 < starPhi p (cp.A σ v) (cp.B σ v) (cp.xi σ v) := by
  have hp1 : 1 ≤ p := le_trans (by norm_num) hR.treg.two_le_p
  have e := wt_eq_wtCore_mul cp.G hp1 (aOf d p) cp.yp_nonneg cp.ym_nonneg σ hv
  rw [PhiRoot_eq_starPhi cp.G p (aOf d p) cp.yp_nonneg cp.ym_nonneg σ hv] at e
  have h0 : 0 ≤ starPhi p (cp.A σ v) (cp.B σ v) (cp.xi σ v) :=
    mul_nonneg (pow_nonneg (le_max_right _ _) _) (pow_nonneg (le_max_right _ _) _)
  refine lt_of_le_of_ne h0 fun h => hσ ?_
  have h' : starPhi p (rootMat cp.G (aOf d p) 1 cp.yp σ cp.S v)
      (rootMat cp.G (aOf d p) (-1) cp.ym σ cp.S v) (rootSigns cp.G σ cp.S v) = 0 := h.symm
  rw [e, h', mul_zero]

/-- Bounds on `b_i` on the core support: `0 ≤ b_i ≤ (h⁺_{K,i} + h⁻_{K,i})/d`. -/
theorem bdiag_mem (hR : RegA d p) {v : cp.V} {σ : Config cp.V}
    (hσ : wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v ≠ 0) (i : cp.N v) :
    0 ≤ cp.bdiag σ v i ∧
      cp.bdiag σ v i ≤ (1 / d) * ((precCore cp.G (aOf d p) 1 cp.yp σ cp.S v)⁻¹ i i +
        (precCore cp.G (aOf d p) (-1) cp.ym σ cp.S v)⁻¹ i i) ∧
      0 ≤ (precCore cp.G (aOf d p) 1 cp.yp σ cp.S v)⁻¹ i i ∧
      0 ≤ (precCore cp.G (aOf d p) (-1) cp.ym σ cp.S v)⁻¹ i i := by
  obtain ⟨h1, h2⟩ := SecA.posDef_of_wtCore_ne_zero cp.G hσ
  obtain ⟨a1, a2⟩ := SecA.rootMat_diag_mem cp.G hR.treg (cp.inCube_yp hR) h1 i
  obtain ⟨b1, b2⟩ := SecA.rootMat_diag_mem cp.G hR.treg (cp.inCube_ym hR) h2 i
  refine ⟨add_nonneg a1 b1, ?_, (h1.inv.diag_pos).le, (h2.inv.diag_pos).le⟩
  change cp.A σ v i i + cp.B σ v i i ≤ _
  rw [mul_add]
  exact add_le_add a2 b2

/-- Moments of `b_i⁺` under the own core law: `E_{ν_K} (b_i⁺)^n ≤ (2(1+2ε)/d)^n`. -/
theorem bdiag_moment (hR : RegA d p) {v : cp.V} (hv : v ∈ cp.S) (i : cp.N v) {n : ℕ}
    (hn1 : 1 ≤ n) (hn : 2 * n ≤ p) :
    cp.coreE v (fun σ => max (cp.bdiag σ v i) 0 ^ n) ≤
      (2 * (1 + 2 * epsP d p) / d) ^ n := by
  have hd := hR.d_pos
  have hw : ∀ σ, 0 ≤ wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v :=
    fun σ => SecA.wtCore_nonneg cp.G _ _ _ _ σ _ _
  obtain ⟨m1, m2⟩ := cp.core_moment hR hv (i : cp.V) hn1 hn
  set hp' := fun σ => (precCore cp.G (aOf d p) 1 cp.yp σ cp.S v)⁻¹ i i with hhp
  set hm' := fun σ => (precCore cp.G (aOf d p) (-1) cp.ym σ cp.S v)⁻¹ i i with hhm
  have hpt : ∀ σ, 0 < wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v →
      max (cp.bdiag σ v i) 0 ^ n ≤ (1 / (d : ℝ)) ^ n * 2 ^ (n - 1) * (hp' σ ^ n + hm' σ ^ n) := by
    intro σ hσ
    obtain ⟨b0, b1, c1, c2⟩ := cp.bdiag_mem hR hσ.ne' i
    rw [max_eq_left b0]
    calc cp.bdiag σ v i ^ n ≤ ((1 / d) * (hp' σ + hm' σ)) ^ n := pow_le_pow_left₀ b0 b1 n
      _ = (1 / (d : ℝ)) ^ n * (hp' σ + hm' σ) ^ n := mul_pow _ _ _
      _ ≤ (1 / (d : ℝ)) ^ n * (2 ^ (n - 1) * (hp' σ ^ n + hm' σ ^ n)) :=
          mul_le_mul_of_nonneg_left (add_pow_le c1 c2 n) (by positivity)
      _ = _ := by ring
  have h1 := SecA.wavg_mono' hw hpt
  have e : wavg (fun σ => wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v)
      (fun σ => (1 / (d : ℝ)) ^ n * 2 ^ (n - 1) * (hp' σ ^ n + hm' σ ^ n)) =
      (1 / (d : ℝ)) ^ n * 2 ^ (n - 1) * (cp.coreE v (fun σ => hp' σ ^ n) +
        cp.coreE v (fun σ => hm' σ ^ n)) := by
    rw [SecA.wavg_const_mul, SecA.wavg_add]
    rfl
  rw [e] at h1
  refine h1.trans ?_
  have e2 : (2 : ℝ) ^ (n - 1) * 2 = 2 ^ n := by rw [← pow_succ, Nat.sub_add_cancel hn1]
  calc (1 / (d : ℝ)) ^ n * 2 ^ (n - 1) * (cp.coreE v (fun σ => hp' σ ^ n) +
        cp.coreE v (fun σ => hm' σ ^ n))
      ≤ (1 / (d : ℝ)) ^ n * 2 ^ (n - 1) * ((1 + 2 * epsP d p) ^ n + (1 + 2 * epsP d p) ^ n) :=
        mul_le_mul_of_nonneg_left (add_le_add m1 m2) (by positivity)
    _ = (1 / (d : ℝ)) ^ n * (2 ^ (n - 1) * 2) * (1 + 2 * epsP d p) ^ n := by ring
    _ = (2 * (1 + 2 * epsP d p) / d) ^ n := by
        rw [e2, div_eq_mul_one_div (2 * (1 + 2 * epsP d p)), mul_pow, mul_pow]
        ring

/-- `A-CREM`: core averages of remainder products. -/
theorem crem (hR : RegA d p) {v : cp.V} (hv : v ∈ cp.S) (m : Config cp.V → ℝ)
    (hm0 : ∀ σ, 0 ≤ m σ) {M : ℝ} (hM : 0 < M)
    (hmom : ∀ n : ℕ, 1 ≤ n → 2 * n ≤ p → cp.coreE v (fun σ => m σ ^ n) ≤ M ^ n) (k : ℕ)
    (hk : 2 * (2 * k + 3) ≤ p) :
    cp.coreE v (fun σ => m σ * ∑ j ∈ (topIdx k : Finset (cp.N v → ℕ)),
        ∏ i, cp.bdiag σ v i ^ j i) ≤ M * (5 / (d : ℝ)) ^ (k + 1) * Real.exp 3 := by
  have hd := hR.d_pos
  have hε0 := SecA.epsP_nonneg hR.treg
  have hε1 := SecA.epsP_le hR.treg
  have hw : ∀ σ, 0 ≤ wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v :=
    fun σ => SecA.wtCore_nonneg cp.G _ _ _ _ σ _ _
  set x : ℝ := 2 * (1 + 2 * epsP d p) / d with hx
  have hx0 : 0 < x := by positivity
  -- one multi-index at a time (Hölder)
  have hj : ∀ j ∈ (topIdx k : Finset (cp.N v → ℕ)),
      cp.coreE v (fun σ => m σ * ∏ i, cp.bdiag σ v i ^ j i) ≤ M * ∏ i, x ^ j i := by
    intro j hj
    obtain ⟨hadm, hg⟩ := mem_topIdx.1 hj
    have hsum : ∑ i, j i ≤ 2 * (k + 1) := hg ▸ SecA.sum_le_two_mul_grade' hadm
    have hn1 : 1 ≤ 1 + ∑ i, j i := by omega
    have hn2 : 2 * (1 + ∑ i, j i) ≤ p := by omega
    have e : cp.coreE v (fun σ => m σ * ∏ i, cp.bdiag σ v i ^ j i) =
        cp.coreE v (fun σ => m σ * ∏ i, max (cp.bdiag σ v i) 0 ^ j i) :=
      SecA.coreE_congr_of_supp cp.G fun σ hσ => by
        congr 1
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [max_eq_left (cp.bdiag_mem hR hσ i).1]
    rw [e]
    exact SecA.wavg_mul_prod_pow_le hw m hm0 (fun i σ => max (cp.bdiag σ v i) 0)
      (fun i σ => le_max_right _ _) j rfl hM (fun _ => x) (fun _ => hx0)
      (hmom _ hn1 hn2) (fun i _ => cp.bdiag_moment hR hv i hn1 hn2)
  -- the sum over the remainder indices
  have e1 : cp.coreE v (fun σ => m σ * ∑ j ∈ (topIdx k : Finset (cp.N v → ℕ)),
        ∏ i, cp.bdiag σ v i ^ j i) =
      ∑ j ∈ (topIdx k : Finset (cp.N v → ℕ)),
        cp.coreE v (fun σ => m σ * ∏ i, cp.bdiag σ v i ^ j i) := by
    simp only [Finset.mul_sum]
    exact wavg_sum _ _
  rw [e1]
  have hxT : x * (1 / (2 * x)) ≤ 1 / 2 := by
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hcnt := SecA.sum_topIdx_le_exp (ι := cp.N v) k hx0 (by positivity : (0 : ℝ) < 1 / (2 * x))
    hxT (cp.card_N_le v)
  have hT : 1 / (1 / (2 * x)) = 2 * x := one_div_one_div _
  have hexp : 2 * x ^ 2 * (1 / (2 * x)) * d = 2 * (1 + 2 * epsP d p) := by
    rw [hx]
    field_simp
  rw [hT, hexp] at hcnt
  calc ∑ j ∈ (topIdx k : Finset (cp.N v → ℕ)),
        cp.coreE v (fun σ => m σ * ∏ i, cp.bdiag σ v i ^ j i)
      ≤ ∑ j ∈ (topIdx k : Finset (cp.N v → ℕ)), M * ∏ i, x ^ j i := Finset.sum_le_sum hj
    _ = M * ∑ j ∈ (topIdx k : Finset (cp.N v → ℕ)), ∏ i, x ^ j i := by rw [Finset.mul_sum]
    _ ≤ M * ((2 * x) ^ (k + 1) * Real.exp (2 * (1 + 2 * epsP d p))) :=
        mul_le_mul_of_nonneg_left hcnt hM.le
    _ ≤ M * ((5 / (d : ℝ)) ^ (k + 1) * Real.exp 3) := by
        gcongr
        · rw [hx, ← mul_div_assoc]
          exact div_le_div_of_nonneg_right (by linarith) hd.le
        · linarith
    _ = M * (5 / (d : ℝ)) ^ (k + 1) * Real.exp 3 := by ring

/-- `A-REM`: the averaged remainder of (E4) at depth `k_*` is exponentially small after
division by the floor. -/
theorem trans_rem (hR : RegA d p) {v : cp.V} (hv : v ∈ cp.S)
    (F : Config cp.V → (cp.N v → ℝ) → ℝ) (m : Config cp.V → ℝ) (hm0 : ∀ σ, 0 ≤ m σ) {M : ℝ}
    (hM : 0 < M)
    (hmom : ∀ n : ℕ, 1 ≤ n → 2 * n ≤ p → cp.coreE v (fun σ => m σ ^ n) ≤ M ^ n)
    (hsm : ∀ σ, SmoothBdd (4 * kStarA d p + 4) (F σ))
    (hder : ∀ σ, ∀ j ∈ (topIdx (kStarA d p) : Finset (cp.N v → ℕ)), ∀ x,
      |dEven (cp.lN v) j (F σ) x| ≤
        m σ * (5 * (p : ℝ)) ^ (2 * ∑ i, j i) * ∏ i, cp.bdiag σ v i ^ j i) :
    |cp.coreE v (fun σ => gaussE (F σ) -
        ∑ j ∈ (retIdx (kStarA d p) : Finset (cp.N v → ℕ)),
          ecoefM j * radE (dEven (cp.lN v) j (F σ)))| ≤
      M * Real.exp (-(p : ℝ)) / d * cp.FH v := by
  have hd := hR.d_pos
  have hp := hR.p_pos
  have hk7 := hR.four_kStar_add_seven_le
  set k := kStarA d p with hk
  have h5p : (1 : ℝ) ≤ 5 * p := by linarith [hR.one_le_p]
  -- pointwise: (E4) and the order count `Σ j_i ≤ 2(k+1)`
  have hpt : ∀ σ, 0 < wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v →
      |gaussE (F σ) - ∑ j ∈ (retIdx k : Finset (cp.N v → ℕ)),
          ecoefM j * radE (dEven (cp.lN v) j (F σ))| ≤
        2 * (5 * (p : ℝ)) ^ (4 * k + 4) *
          (m σ * ∑ j ∈ (topIdx k : Finset (cp.N v → ℕ)), ∏ i, cp.bdiag σ v i ^ j i) := by
    intro σ hσ
    have h : |gaussE (F σ) - ∑ j ∈ (retIdx k : Finset (cp.N v → ℕ)),
          ecoefM j * radE (dEven (cp.lN v) j (F σ))| ≤
        2 * ∑ j ∈ (topIdx k : Finset (cp.N v → ℕ)),
          m σ * (5 * (p : ℝ)) ^ (2 * ∑ i, j i) * ∏ i, cp.bdiag σ v i ^ j i :=
      gauss_rad_expansion k (cp.lN_nodup v) cp.mem_lN (hsm σ) _ (hder σ)
    refine h.trans ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => ?_
    obtain ⟨hadm, hg⟩ := mem_topIdx.1 hj
    have hsum : ∑ i, j i ≤ 2 * (k + 1) := hg ▸ SecA.sum_le_two_mul_grade' hadm
    have hb : 0 ≤ m σ * ∏ i, cp.bdiag σ v i ^ j i :=
      mul_nonneg (hm0 σ) (Finset.prod_nonneg fun i _ =>
        pow_nonneg (cp.bdiag_mem hR hσ.ne' i).1 _)
    have hpow : (5 * (p : ℝ)) ^ (2 * ∑ i, j i) ≤ (5 * (p : ℝ)) ^ (4 * k + 4) :=
      pow_le_pow_right₀ h5p (by omega)
    calc m σ * (5 * (p : ℝ)) ^ (2 * ∑ i, j i) * ∏ i, cp.bdiag σ v i ^ j i
        = (5 * (p : ℝ)) ^ (2 * ∑ i, j i) * (m σ * ∏ i, cp.bdiag σ v i ^ j i) := by ring
      _ ≤ (5 * (p : ℝ)) ^ (4 * k + 4) * (m σ * ∏ i, cp.bdiag σ v i ^ j i) :=
          mul_le_mul_of_nonneg_right hpow hb
  have h1 := cp.abs_coreE_le v hpt
  have h2 : cp.coreE v (fun σ => 2 * (5 * (p : ℝ)) ^ (4 * k + 4) *
        (m σ * ∑ j ∈ (topIdx k : Finset (cp.N v → ℕ)), ∏ i, cp.bdiag σ v i ^ j i)) =
      2 * (5 * (p : ℝ)) ^ (4 * k + 4) * cp.coreE v (fun σ =>
        m σ * ∑ j ∈ (topIdx k : Finset (cp.N v → ℕ)), ∏ i, cp.bdiag σ v i ^ j i) :=
    SecA.wavg_const_mul _ _ _
  have h3 := cp.crem hR hv m hm0 hM hmom k (by omega)
  have hFH := cp.FH_pos' hR hv
  have hfl := cp.floor hR hv
  have hE6 := hR.E6
  -- `2 e³ ≤ p`
  have he3 : 2 * Real.exp 3 ≤ p := by
    have h1 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
    have h2 := Real.exp_one_lt_d9
    have h3 : Real.exp 1 ^ 3 ≤ 3 ^ 3 := pow_le_pow_left₀ (Real.exp_pos 1).le (by linarith) 3
    have hp6 : (10 : ℝ) ^ 6 ≤ p := by exact_mod_cast hR.treg.hp
    linarith
  have key : 2 * Real.exp 3 * (5 * (p : ℝ)) ^ (4 * k + 4) * (5 / (d : ℝ)) ^ (k + 1) *
      40 ^ p ≤ Real.exp (-(p : ℝ)) / d := by
    calc 2 * Real.exp 3 * (5 * (p : ℝ)) ^ (4 * k + 4) * (5 / (d : ℝ)) ^ (k + 1) * 40 ^ p
        ≤ (p : ℝ) * (8 * (p : ℝ)) ^ (4 * k + 4) * (8 / (d : ℝ)) ^ (k + 1) * 40 ^ p := by
          gcongr
          · linarith
          · norm_num
      _ = (p : ℝ) * 40 ^ p * (8 * (p : ℝ)) ^ (4 * k + 4) * 8 ^ (k + 1) / (d : ℝ) ^ k / d := by
          have hd0 : (d : ℝ) ≠ 0 := hd.ne'
          rw [div_pow, pow_succ (d : ℝ) k]
          field_simp
          try ring
      _ ≤ Real.exp (-(p : ℝ)) / d := div_le_div_of_nonneg_right hE6 hd.le
  calc _ ≤ _ := h1
    _ = _ := h2
    _ ≤ 2 * (5 * (p : ℝ)) ^ (4 * k + 4) * (M * (5 / (d : ℝ)) ^ (k + 1) * Real.exp 3) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = M * (2 * Real.exp 3 * (5 * (p : ℝ)) ^ (4 * k + 4) * (5 / (d : ℝ)) ^ (k + 1)) * 1 := by
        ring
    _ ≤ M * (2 * Real.exp 3 * (5 * (p : ℝ)) ^ (4 * k + 4) * (5 / (d : ℝ)) ^ (k + 1)) *
          (40 ^ p * cp.FH v) := mul_le_mul_of_nonneg_left hfl (by positivity)
    _ = M * (2 * Real.exp 3 * (5 * (p : ℝ)) ^ (4 * k + 4) * (5 / (d : ℝ)) ^ (k + 1) *
          40 ^ p) * cp.FH v := by ring
    _ ≤ M * (Real.exp (-(p : ℝ)) / d) * cp.FH v :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left key hM.le) hFH.le
    _ = M * Real.exp (-(p : ℝ)) / d * cp.FH v := by ring

/-- `A-RET`: retained terms pass to the actual law (exact). -/
theorem coreE_radE_div_eq (hR : RegA d p) {v : cp.V} (hv : v ∈ cp.S)
    (R : Config cp.V → (cp.N v → ℝ) → ℝ) (hRc : ∀ σ σ', AgreeOff v σ σ' → R σ = R σ')
    (hvan : ∀ σ (ξ : cp.N v → ℝ), (∀ i, ξ i = 1 ∨ ξ i = -1) →
      starPhi p (cp.A σ v) (cp.B σ v) ξ = 0 → R σ ξ = 0) :
    cp.coreE v (fun σ => radE (R σ)) / cp.FH v =
      cp.E (fun σ => R σ (cp.xi σ v) / starPhi p (cp.A σ v) (cp.B σ v) (cp.xi σ v)) := by
  have hp1 : 1 ≤ p := le_trans (by norm_num) hR.treg.two_le_p
  have h := SecA.lawE_eq_coreE_div cp.G hp1 (aOf d p) cp.yp_nonneg cp.ym_nonneg hv
    (fun σ ξ => R σ ξ / starPhi p (cp.A σ v) (cp.B σ v) ξ) (fun σ σ' hσ => by
      funext ξ
      simp only [CapPoint.A, CapPoint.B, SecA.rootMat_congr cp.G hσ, hRc σ σ' hσ])
  refine Eq.trans ?_ h.symm
  congr 1
  refine congrArg _ (funext fun σ => ?_)
  rw [radE_eq_sum, radE_eq_sum]
  congr 1
  refine Finset.sum_congr rfl fun ε _ => ?_
  have hpm : ∀ i, (if ε i then (1 : ℝ) else -1) = 1 ∨ (if ε i then (1 : ℝ) else -1) = -1 := by
    intro i
    by_cases h : ε i <;> simp [h]
  show R σ (fun i => if ε i then 1 else -1) =
    starPhi p (cp.A σ v) (cp.B σ v) (fun i => if ε i then 1 else -1) *
      (R σ (fun i => if ε i then 1 else -1) /
        starPhi p (cp.A σ v) (cp.B σ v) (fun i => if ε i then 1 else -1))
  by_cases hΦ : starPhi p (cp.A σ v) (cp.B σ v) (fun i => if ε i then 1 else -1) = 0
  · rw [hΦ, zero_mul]
    exact hvan σ _ hpm hΦ
  · rw [mul_div_assoc', mul_comm, mul_div_assoc, div_self hΦ, mul_one]

/-- `A-HGR`: the retained grades `≥ 2` under the actual law. -/
theorem hgr (hR : RegA d p) {v : cp.V} (hv : v ∈ cp.S) (k : ℕ) (hk : 2 * (4 * k + 1) ≤ p)
    (R : (cp.N v → ℕ) → Config cp.V → ℝ) (m : Config cp.V → ℝ)
    (lam : cp.N v → Config cp.V → ℝ) (hm0 : ∀ σ, 0 ≤ m σ) (hl0 : ∀ i σ, 0 ≤ lam i σ)
    {M L : ℝ} (hM : 0 < M) (hL : 0 < L)
    (hmomm : ∀ n : ℕ, 1 ≤ n → 2 * n ≤ p → cp.E (fun σ => m σ ^ n) ≤ M ^ n)
    (hmoml : ∀ i, ∀ n : ℕ, 1 ≤ n → 2 * n ≤ p → cp.E (fun σ => lam i σ ^ n) ≤ L ^ n)
    (hRb : ∀ j ∈ (retIdx k : Finset (cp.N v → ℕ)), ∀ σ,
      0 < wt cp.G p (aOf d p) cp.yp cp.ym σ cp.S → |R j σ| ≤ m σ * ∏ i, lam i σ ^ (2 * j i))
    (hdL : 2 ≤ (d : ℝ) * L ^ 2) (hdL4 : (d : ℝ) * L ^ 4 ≤ 1 / 2) :
    ∑ j ∈ (retIdx k : Finset (cp.N v → ℕ)).filter (fun j => 2 ≤ grade j), |cp.E (R j)| ≤
      2 * Real.exp 2 * M * ((d : ℝ) * L ^ 4) ^ 2 := by
  have hd := hR.d_pos
  have hw : ∀ σ, 0 ≤ wt cp.G p (aOf d p) cp.yp cp.ym σ cp.S := fun σ => wt_nonneg cp.G σ
  -- one multi-index at a time (Hölder)
  have hj : ∀ j ∈ (retIdx k : Finset (cp.N v → ℕ)), |cp.E (R j)| ≤ M * ∏ i, (L ^ 2) ^ j i := by
    intro j hj
    obtain ⟨hadm, hg⟩ := mem_retIdx.1 hj
    have hsum : ∑ i, j i ≤ 2 * k := (SecA.sum_le_two_mul_grade' hadm).trans (by omega)
    have h1 : |cp.E (R j)| ≤ cp.E (fun σ => m σ * ∏ i, lam i σ ^ (2 * j i)) :=
      SecA.abs_wavg_le_of_supp hw fun σ hσ => hRb j hj σ hσ
    have hn : 1 + ∑ i, 2 * j i = 1 + 2 * ∑ i, j i := by rw [Finset.mul_sum]
    have h2 := SecA.wavg_mul_prod_pow_le hw m hm0 lam hl0 (fun i => 2 * j i) hn hM
      (fun _ => L) (fun _ => hL) (hmomm _ (by omega) (by omega))
      (fun i _ => hmoml i _ (by omega) (by omega))
    refine h1.trans (h2.trans (le_of_eq ?_))
    congr 1
    exact Finset.prod_congr rfl fun i _ => by rw [pow_mul]
  -- grade by grade (A-CNT with `x = L²`, `T = 1/(d L⁴)`)
  have hmaps : ∀ j ∈ (retIdx k : Finset (cp.N v → ℕ)).filter (fun j => 2 ≤ grade j),
      grade j ∈ Finset.Ico 2 (k + 1) := by
    intro j hj
    obtain ⟨hj1, hj2⟩ := Finset.mem_filter.1 hj
    have := (mem_retIdx.1 hj1).2
    rw [Finset.mem_Ico]
    omega
  have hT0 : (0 : ℝ) < 1 / ((d : ℝ) * L ^ 4) := by positivity
  have hxT : L ^ 2 * (1 / ((d : ℝ) * L ^ 4)) ≤ 1 / 2 := by
    have e : L ^ 2 * (1 / ((d : ℝ) * L ^ 4)) = 1 / ((d : ℝ) * L ^ 2) := by
      field_simp
    rw [e, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hexp2 : 2 * (L ^ 2) ^ 2 * (1 / ((d : ℝ) * L ^ 4)) * d = 2 := by
    field_simp
  have hgrade : ∀ g ∈ Finset.Ico 2 (k + 1),
      ∑ j ∈ (retIdx k : Finset (cp.N v → ℕ)).filter (fun j => 2 ≤ grade j) with grade j = g,
        M * ∏ i, (L ^ 2) ^ j i ≤ M * (((d : ℝ) * L ^ 4) ^ g * Real.exp 2) := by
    intro g hg
    have hg1 : 1 ≤ g := by rw [Finset.mem_Ico] at hg; omega
    have hsub : ((retIdx k : Finset (cp.N v → ℕ)).filter (fun j => 2 ≤ grade j)).filter
        (fun j => grade j = g) ⊆ topIdx (g - 1) := by
      intro j hj
      obtain ⟨hj1, hj2⟩ := Finset.mem_filter.1 hj
      obtain ⟨hj3, -⟩ := Finset.mem_filter.1 hj1
      exact mem_topIdx.2 ⟨(mem_retIdx.1 hj3).1, by omega⟩
    have hcnt := SecA.sum_topIdx_le_exp (ι := cp.N v) (g - 1) (pow_pos hL 2) hT0 hxT
      (cp.card_N_le v)
    rw [one_div_one_div, Nat.sub_add_cancel hg1, hexp2] at hcnt
    calc _ ≤ ∑ j ∈ (topIdx (g - 1) : Finset (cp.N v → ℕ)), M * ∏ i, (L ^ 2) ^ j i :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun j _ _ =>
            mul_nonneg hM.le (Finset.prod_nonneg fun i _ => by positivity)
      _ = M * ∑ j ∈ (topIdx (g - 1) : Finset (cp.N v → ℕ)), ∏ i, (L ^ 2) ^ j i := by
          rw [Finset.mul_sum]
      _ ≤ M * (((d : ℝ) * L ^ 4) ^ g * Real.exp 2) := mul_le_mul_of_nonneg_left hcnt hM.le
  have hr0 : (0 : ℝ) ≤ (d : ℝ) * L ^ 4 := by positivity
  have hgeom := geom_sum_Ico_le_of_lt_one (m := 2) (n := k + 1) hr0 (by linarith)
  have h2r : ((d : ℝ) * L ^ 4) ^ 2 / (1 - (d : ℝ) * L ^ 4) ≤ 2 * ((d : ℝ) * L ^ 4) ^ 2 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [sq_nonneg ((d : ℝ) * L ^ 4)]
  calc ∑ j ∈ (retIdx k : Finset (cp.N v → ℕ)).filter (fun j => 2 ≤ grade j), |cp.E (R j)|
      ≤ ∑ j ∈ (retIdx k : Finset (cp.N v → ℕ)).filter (fun j => 2 ≤ grade j),
          M * ∏ i, (L ^ 2) ^ j i :=
        Finset.sum_le_sum fun j hjf => hj j (Finset.mem_filter.1 hjf).1
    _ = ∑ g ∈ Finset.Ico 2 (k + 1),
          ∑ j ∈ (retIdx k : Finset (cp.N v → ℕ)).filter (fun j => 2 ≤ grade j) with grade j = g,
            M * ∏ i, (L ^ 2) ^ j i := (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ ≤ ∑ g ∈ Finset.Ico 2 (k + 1), M * (((d : ℝ) * L ^ 4) ^ g * Real.exp 2) :=
        Finset.sum_le_sum hgrade
    _ = M * Real.exp 2 * ∑ g ∈ Finset.Ico 2 (k + 1), ((d : ℝ) * L ^ 4) ^ g := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun g _ => by ring
    _ ≤ M * Real.exp 2 * (2 * ((d : ℝ) * L ^ 4) ^ 2) :=
        mul_le_mul_of_nonneg_left (hgeom.trans h2r) (by positivity)
    _ = 2 * Real.exp 2 * M * ((d : ℝ) * L ^ 4) ^ 2 := by ring

/-- `A-TRANS`: the generic transfer. `F` is a core-measurable family of star observables with a
sup majorant (`m`, own-core moments `≤ Mⁿ`), vanishing derivatives at the sign vectors outside the
support of `Φ`, and an endpoint majorant (`m_E`, `λ_i`, actual-law moments `≤ M_Eⁿ`, `≤ Lⁿ`) for the
retained grades `≥ 2`. -/
theorem trans (hR : RegA d p) {v : cp.V} (hv : v ∈ cp.S)
    (F : Config cp.V → (cp.N v → ℝ) → ℝ) (hFc : ∀ σ σ', AgreeOff v σ σ' → F σ = F σ')
    (m : Config cp.V → ℝ) (hm0 : ∀ σ, 0 ≤ m σ) {M : ℝ} (hM : 0 < M)
    (hmom : ∀ n : ℕ, 1 ≤ n → 2 * n ≤ p → cp.coreE v (fun σ => m σ ^ n) ≤ M ^ n)
    (hsm : ∀ σ, SmoothBdd (4 * kStarA d p + 4) (F σ))
    (hder : ∀ σ, ∀ j ∈ (topIdx (kStarA d p) : Finset (cp.N v → ℕ)), ∀ x,
      |dEven (cp.lN v) j (F σ) x| ≤
        m σ * (5 * (p : ℝ)) ^ (2 * ∑ i, j i) * ∏ i, cp.bdiag σ v i ^ j i)
    (hvan : ∀ σ, ∀ j ∈ (retIdx (kStarA d p) : Finset (cp.N v → ℕ)), ∀ ξ : cp.N v → ℝ,
      (∀ i, ξ i = 1 ∨ ξ i = -1) → starPhi p (cp.A σ v) (cp.B σ v) ξ = 0 →
        dEven (cp.lN v) j (F σ) ξ = 0)
    (mE : Config cp.V → ℝ) (lam : cp.N v → Config cp.V → ℝ) (hmE0 : ∀ σ, 0 ≤ mE σ)
    (hl0 : ∀ i σ, 0 ≤ lam i σ) {ME L : ℝ} (hME : 0 < ME) (hL : 0 < L)
    (hmomE : ∀ n : ℕ, 1 ≤ n → 2 * n ≤ p → cp.E (fun σ => mE σ ^ n) ≤ ME ^ n)
    (hmoml : ∀ i, ∀ n : ℕ, 1 ≤ n → 2 * n ≤ p → cp.E (fun σ => lam i σ ^ n) ≤ L ^ n)
    (hend : ∀ j ∈ (retIdx (kStarA d p) : Finset (cp.N v → ℕ)), 2 ≤ grade j → ∀ σ,
      0 < wt cp.G p (aOf d p) cp.yp cp.ym σ cp.S →
        |dEven (cp.lN v) j (F σ) (cp.xi σ v)| ≤
          mE σ * starPhi p (cp.A σ v) (cp.B σ v) (cp.xi σ v) * ∏ i, lam i σ ^ (2 * j i))
    (hdL : 2 ≤ (d : ℝ) * L ^ 2) (hdL4 : (d : ℝ) * L ^ 4 ≤ 1 / 2) :
    |cp.coreE v (fun σ => gaussE (F σ) - radE (F σ)) / cp.FH v -
        ∑ i : cp.N v, (1 / 12 : ℝ) * cp.E (fun σ => (pderiv i)^[4] (F σ) (cp.xi σ v) /
          starPhi p (cp.A σ v) (cp.B σ v) (cp.xi σ v))| ≤
      2 * Real.exp 2 * ME * ((d : ℝ) * L ^ 4) ^ 2 + M * Real.exp (-(p : ℝ)) / d := by
  have hk1 : 1 ≤ kStarA d p := le_trans (by norm_num) hR.kStar_ge_1920
  have hmo := hR.moment_order_le
  have hFH := cp.FH_pos' hR hv
  have hrem := cp.trans_rem hR hv F m hm0 hM hmom hsm hder
  set k := kStarA d p with hk
  -- the retained terms pass to the actual law (A-RET)
  set Lj : (cp.N v → ℕ) → ℝ := fun j => cp.E (fun σ => dEven (cp.lN v) j (F σ) (cp.xi σ v) /
      starPhi p (cp.A σ v) (cp.B σ v) (cp.xi σ v)) with hLj
  have hret : ∀ j ∈ (retIdx k : Finset (cp.N v → ℕ)),
      cp.coreE v (fun σ => radE (dEven (cp.lN v) j (F σ))) = cp.FH v * Lj j := by
    intro j hj
    have h := cp.coreE_radE_div_eq hR hv (fun σ => dEven (cp.lN v) j (F σ))
      (fun σ σ' hσ => congrArg (fun f => dEven (cp.lN v) j f) (hFc σ σ' hσ))
      (fun σ ξ hξ hΦ => hvan σ j hj ξ hξ hΦ)
    rw [div_eq_iff hFH.ne'] at h
    rw [h, mul_comm]
  -- grade `0` is `𝖱 F`; the rest are retained terms
  have h0mem : (0 : cp.N v → ℕ) ∈ (retIdx k : Finset (cp.N v → ℕ)) :=
    mem_retIdx.2 ⟨fun i => by simp, by simp⟩
  have hpt : (fun σ => gaussE (F σ) - radE (F σ)) = fun σ =>
      (gaussE (F σ) - ∑ j ∈ (retIdx k : Finset (cp.N v → ℕ)),
        ecoefM j * radE (dEven (cp.lN v) j (F σ))) +
      ∑ j ∈ (retIdx k : Finset (cp.N v → ℕ)).erase 0,
        ecoefM j * radE (dEven (cp.lN v) j (F σ)) := by
    funext σ
    rw [← Finset.add_sum_erase _ _ h0mem, ecoefM_zero, dEven_zero, one_mul]
    ring
  have e2 : cp.coreE v (fun σ => ∑ j ∈ (retIdx k : Finset (cp.N v → ℕ)).erase 0,
        ecoefM j * radE (dEven (cp.lN v) j (F σ))) =
      cp.FH v * ∑ j ∈ (retIdx k : Finset (cp.N v → ℕ)).erase 0, ecoefM j * Lj j := by
    rw [cp.coreE_fsum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [cp.coreE_fconst_mul, hret j (Finset.mem_of_mem_erase hj)]
    ring
  have hdec : cp.coreE v (fun σ => gaussE (F σ) - radE (F σ)) =
      cp.coreE v (fun σ => gaussE (F σ) - ∑ j ∈ (retIdx k : Finset (cp.N v → ℕ)),
        ecoefM j * radE (dEven (cp.lN v) j (F σ))) +
      cp.FH v * ∑ j ∈ (retIdx k : Finset (cp.N v → ℕ)).erase 0, ecoefM j * Lj j := by
    rw [hpt, cp.coreE_fadd, e2]
  -- split by grade: `1` and `≥ 2`
  have hsplit : ∑ j ∈ (retIdx k : Finset (cp.N v → ℕ)).erase 0, ecoefM j * Lj j =
      ∑ j ∈ (retIdx k : Finset (cp.N v → ℕ)).filter (fun j => grade j = 1), ecoefM j * Lj j +
      ∑ j ∈ (retIdx k : Finset (cp.N v → ℕ)).filter (fun j => 2 ≤ grade j), ecoefM j * Lj j := by
    rw [← Finset.sum_filter_add_sum_filter_not ((retIdx k : Finset (cp.N v → ℕ)).erase 0)
      (fun j => grade j = 1)]
    have s1 : ((retIdx k : Finset (cp.N v → ℕ)).erase 0).filter (fun j => grade j = 1) =
        (retIdx k : Finset (cp.N v → ℕ)).filter (fun j => grade j = 1) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨⟨-, hj⟩, hg⟩
        exact ⟨hj, hg⟩
      · rintro ⟨hj, hg⟩
        refine ⟨⟨?_, hj⟩, hg⟩
        rintro rfl
        simp at hg
    have s2 : ((retIdx k : Finset (cp.N v → ℕ)).erase 0).filter (fun j => ¬ grade j = 1) =
        (retIdx k : Finset (cp.N v → ℕ)).filter (fun j => 2 ≤ grade j) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨⟨hne, hj⟩, hg⟩
        refine ⟨hj, ?_⟩
        have : grade j ≠ 0 := fun h0 => hne (eq_zero_of_grade_eq_zero (mem_retIdx.1 hj).1 h0)
        omega
      · rintro ⟨hj, hg⟩
        refine ⟨⟨?_, hj⟩, by omega⟩
        rintro rfl
        simp at hg
    rw [s1, s2]
  -- grade one: the `2 e_i`
  have hg1 : ∑ j ∈ (retIdx k : Finset (cp.N v → ℕ)).filter (fun j => grade j = 1),
        ecoefM j * Lj j =
      ∑ i : cp.N v, (1 / 12 : ℝ) * cp.E (fun σ => (pderiv i)^[4] (F σ) (cp.xi σ v) /
        starPhi p (cp.A σ v) (cp.B σ v) (cp.xi σ v)) := by
    rw [SecA.retIdx_filter_grade_one hk1,
      Finset.sum_image (Set.injOn_of_injective SecA.single_two_injective)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [SecA.ecoefM_single_two]
    simp only [hLj, SecA.dEven_single_two (cp.lN_nodup v) (cp.mem_lN i)]
  -- grades `≥ 2` (A-HGR)
  have hRb : ∀ j ∈ (retIdx k : Finset (cp.N v → ℕ)), ∀ σ,
      0 < wt cp.G p (aOf d p) cp.yp cp.ym σ cp.S →
        |(if 2 ≤ grade j then dEven (cp.lN v) j (F σ) (cp.xi σ v) /
            starPhi p (cp.A σ v) (cp.B σ v) (cp.xi σ v) else 0)| ≤
          mE σ * ∏ i, lam i σ ^ (2 * j i) := by
    intro j hj σ hσ
    by_cases hg : 2 ≤ grade j
    · rw [ite_eq_left hg]
      have hΦ := cp.starPhi_xi_pos hR hv hσ.ne'
      rw [abs_div, abs_of_pos hΦ, div_le_iff₀ hΦ]
      have := hend j hj hg σ hσ
      calc _ ≤ _ := this
        _ = _ := by ring
    · rw [ite_eq_right hg, abs_zero]
      exact mul_nonneg (hmE0 σ) (Finset.prod_nonneg fun i _ => pow_nonneg (hl0 i σ) _)
  have hG2 := cp.hgr hR hv k (by omega) (fun j σ => if 2 ≤ grade j then
      dEven (cp.lN v) j (F σ) (cp.xi σ v) / starPhi p (cp.A σ v) (cp.B σ v) (cp.xi σ v) else 0)
    mE lam hmE0 hl0 hME hL hmomE hmoml hRb hdL hdL4
  have hG2' : |∑ j ∈ (retIdx k : Finset (cp.N v → ℕ)).filter (fun j => 2 ≤ grade j),
      ecoefM j * Lj j| ≤ 2 * Real.exp 2 * ME * ((d : ℝ) * L ^ 4) ^ 2 := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_trans ?_ hG2)
    refine Finset.sum_le_sum fun j hj => ?_
    have hg := (Finset.mem_filter.1 hj).2
    have e : cp.E (fun σ => if 2 ≤ grade j then dEven (cp.lN v) j (F σ) (cp.xi σ v) /
        starPhi p (cp.A σ v) (cp.B σ v) (cp.xi σ v) else 0) = Lj j := by
      simp only [ite_eq_left hg, hLj]
    rw [abs_mul, e]
    exact mul_le_of_le_one_left (abs_nonneg _) (SecA.abs_ecoefM_le_one j)
  -- assemble
  have hrem' : |cp.coreE v (fun σ => gaussE (F σ) - ∑ j ∈ (retIdx k : Finset (cp.N v → ℕ)),
      ecoefM j * radE (dEven (cp.lN v) j (F σ))) / cp.FH v| ≤ M * Real.exp (-(p : ℝ)) / d := by
    rw [abs_div, abs_of_pos hFH, div_le_iff₀ hFH]
    exact hrem
  rw [hdec, hsplit, hg1, add_div, mul_div_cancel_left₀ _ hFH.ne']
  calc _ = |cp.coreE v (fun σ => gaussE (F σ) - ∑ j ∈ (retIdx k : Finset (cp.N v → ℕ)),
          ecoefM j * radE (dEven (cp.lN v) j (F σ))) / cp.FH v +
        ∑ j ∈ (retIdx k : Finset (cp.N v → ℕ)).filter (fun j => 2 ≤ grade j),
          ecoefM j * Lj j| := by ring_nf
    _ ≤ _ := abs_add_le _ _
    _ ≤ M * Real.exp (-(p : ℝ)) / d + 2 * Real.exp 2 * ME * ((d : ℝ) * L ^ 4) ^ 2 :=
        add_le_add hrem' hG2'
    _ = _ := by ring

end CapPoint

end BiluLinial.Tight
