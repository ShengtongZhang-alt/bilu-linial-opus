/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecC.RootMoments
public import BiluLinial.Tight.SecC.F1
public import BiluLinial.Tight.SecC.MarkEnv
public import BiluLinial.Tight.SecA.Star
public import BiluLinial.Tight.SecA.Transfer
public import BiluLinial.Tight.Compare.Symm

/-!
# T.TRC: the retained grades (node TRC-G of `docs/tight/BP_SECC.md`)

AUDIT-C §3 (T.TRC), source lines 1281–1310 and 1290–1293 (gap G5).

* `trcObs p m₊ m₋ c A B = c α₊^{p-m₊} β₊^{p-m₋}` (`= c · clipPow p m₊ m₋ A B`), the core-constant
  numerator of T.TRC as a clipped observable of SecA (`clipObs (quadFn c 0 0)`), so that the
  star-level nodes of Section A (A-SMOOTH, A-E5, A-CLIP0, A-MAJ) apply to it.
* `nbL G S v`: the coordinates of `N_S(v)` as a list (each once; `CapPoint.lN`).
* Multi-index helpers: `sum_le_two_mul_grade` (`Σ j_i ≤ 2|j|_g` for admissible `j`),
  `length_dEvenList_univ`, `prod_map_dEvenList_univ`.
* **TRC-G** (`retained_grades_le`): at a capped point, for `0 ≤ w ≤ d^{20}` on the core support and
  `m_± ≤ 3`, the retained grades `1 ≤ |j|_g ≤ k_*` of (E4), transferred to the actual law
  (`E[w ∂^{2j}(α^{p-m₊}β^{p-m₋})(ξ)/Φ(ξ)]`), sum to at most `C (p⁴/d)(x_w + ϑ)`,
  `x_w = E[w t₊^{m₊} t₋^{m₋}]`.

**Sketch of TRC-G.** (G1) At a supported signing the star vector `ξ` is interior
(`α, β > 0`, F1) and A-MAJ applies with `m_g = w`, `m_α = α`, `m_β = β` and the common weights
`λ_i = a r_i`, `r_i = |x_i| + √(G⁺_vvG⁺_ii) + |z_i| + √(G⁻_vvG⁻_ii)`: indeed `(Aξ)_i = -aα x_i`
(F1), `A_ii ≤ a²α G_vvG_ii` (`root_diag_le`) and `|A_ik| ≤ √(A_iiA_kk)`. Hence
`|∂^{2j}F(ξ)|/Φ(ξ) ≤ X (4p+2)^{2Σj} Π λ_i^{2j_i} ≤ X Π μ_i^{j_i}`, `X = w t₊^{m₊} t₋^{m₋}`,
`μ_i = 25 p² a² r_i²`. (G2) By A-CNT (`SecA.sum_topIdx_prod_pow_le`, proved) with
`x' = max(max_i μ_i, 2/d)` and `T = 1/(d x'²)`: `Σ_{|j|_g = g} Π μ_i^{j_i} ≤ e² (d x'²)^g` and
`d x'² ≤ 157 (p⁴/d)(1 + R⁴)`, `R = max_i r_i ≤ s(h⁺_v + h⁻_v + max_i(h⁺_i + h⁻_i))` (since
`|x_i| ≤ √(G_vvG_ii) ≤ (G_vv + G_ii)/2`). (G3) T.IL per grade (`lawE_mul_le_interp`) with
`k_g = ⌊p/(16g)⌋ ≥ 1` (`16 k_* ≤ p`), `m = x_w + ϑ`, `‖X‖₂ ≤ d^{30}` (`w ≤ d^{20}`, F2):
`ϑ^{-1/k_g}, B_X^{1/k_g} ≤ 2^g` once `p ≥ 1400 log d`, and `‖(1+R)^{4g}‖_{2k_g} ≤ 2^g C^{4g}` by
T.DSTAR (`wavg_sup_pow_le`, `|N| ≤ d`) and F2 (moment order `8 g k_g ≤ p/2`). So grade `g` costs
`≤ e² (C' p⁴/d)^g (x_w + ϑ)`, and the geometric sum over `g ≥ 1` (ratio `≤ 1/2`) gives
`C (p⁴/d)(x_w + ϑ)`.

**Checks.** `N = ∅`: `retIdx k = {0}`, the sum is empty. `w = 0`: every term vanishes. One
coordinate, `B = 0`, `A = (α₀)`, `m₊ = m₋ = 0`: the grade-one term is
`(1/12) E[∂⁴(α^p)(ξ)/α^p] = (1/12)(12 p(p-1)α₀²/α² + O(p³α₀³))`, of order `p²a⁴ ≤ p⁴/d`, within
the bound.
-/

@[expose] public section

namespace BiluLinial.Tight

namespace SecC

universe u

open Matrix

section Star

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The core-constant numerator `c α₊^{p-m₊} β₊^{p-m₋}` of T.TRC. -/
def trcObs (p mp mm : ℕ) (c : ℝ) (A B : Matrix ι ι ℝ) : (ι → ℝ) → ℝ :=
  clipObs (quadFn c 0 0) (p - mp) (p - mm) A B

omit [DecidableEq ι] in
theorem trcObs_apply (p mp mm : ℕ) (c : ℝ) (A B : Matrix ι ι ℝ) (x : ι → ℝ) :
    trcObs p mp mm c A B x = c * clipPow p mp mm A B x := by
  simp [trcObs, clipObs, quadFn, qForm, clipPow, mul_assoc]

omit [DecidableEq ι] in
/-- The constant prefactor `c` satisfies the majorant condition with scale `m ≥ |c|`. -/
theorem quadMaj_const {c m : ℝ} (hc : |c| ≤ m) {lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i)
    (x : ι → ℝ) : QuadMaj c 0 0 x m lam := by
  have hm : 0 ≤ m := (abs_nonneg c).trans hc
  refine ⟨?_, fun i => ?_, fun i j => ?_⟩
  · simpa [quadFn, qForm] using hc
  · simp only [Pi.zero_apply, add_zero, transpose_zero, zero_mulVec, abs_zero]
    exact mul_nonneg (mul_nonneg zero_le_two hm) (hlam i)
  · simp only [Matrix.zero_apply, add_zero, abs_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg zero_le_two hm) (hlam i)) (hlam j)

omit [Fintype ι] in
theorem pderivList_const_zero (l : List ι) :
    pderivList l (fun _ : ι → ℝ => (0 : ℝ)) = fun _ => 0 := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    rw [pderivList_cons]
    have h : pderiv i (fun _ : ι → ℝ => (0 : ℝ)) = fun _ => 0 := by
      funext x
      simp [pderiv]
    rw [h, ih]

theorem smoothBdd_const_zero (N : ℕ) : SmoothBdd N (fun _ : ι → ℝ => (0 : ℝ)) :=
  ⟨contDiff_const, fun l _ => ⟨0, fun x => by rw [pderivList_const_zero]; simp⟩⟩

omit [DecidableEq ι] in
/-- For an admissible multi-index (no entry `1`), `Σ_i j_i ≤ 2 |j|_g`. -/
theorem sum_le_two_mul_grade {j : ι → ℕ} (hadm : ∀ i, j i ≠ 1) : ∑ i, j i ≤ 2 * grade j := by
  rw [grade, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have := hadm i
  omega

omit [DecidableEq ι] in
theorem length_dEvenList_univ (j : ι → ℕ) :
    (dEvenList (Finset.univ : Finset ι).toList j).length = 2 * ∑ i, j i := by
  rw [length_dEvenList, Finset.sum_map_toList, Finset.mul_sum]

omit [Fintype ι] [DecidableEq ι] in
theorem prod_map_dEvenList (l : List ι) (j : ι → ℕ) (f : ι → ℝ) :
    ((dEvenList l j).map f).prod = (l.map fun x => f x ^ (2 * j x)).prod := by
  induction l with
  | nil => simp [dEvenList]
  | cons y l ih =>
    simp only [dEvenList, List.flatMap_cons, List.map_append, List.prod_append,
      List.map_replicate, List.prod_replicate, List.map_cons, List.prod_cons] at ih ⊢
    rw [ih]

omit [DecidableEq ι] in
theorem prod_map_dEvenList_univ (j : ι → ℕ) (f : ι → ℝ) :
    ((dEvenList (Finset.univ : Finset ι).toList j).map f).prod = ∏ i, f i ^ (2 * j i) := by
  rw [prod_map_dEvenList]
  exact Finset.prod_map_toList _ (fun i => f i ^ (2 * j i))

omit [DecidableEq ι] in
/-- Off-diagonal entries of a PSD matrix: `A_ik² ≤ A_ii A_kk` (2×2 principal minor). -/
theorem psd_apply_sq_le {A : Matrix ι ι ℝ} (hA : A.PosSemidef) (i k : ι) :
    A i k ^ 2 ≤ A i i * A k k := by
  have h2 := (hA.submatrix ![i, k]).det_nonneg
  rw [Matrix.det_fin_two] at h2
  simp only [Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at h2
  have hsym : A k i = A i k := by simpa using hA.isHermitian.apply i k
  rw [hsym] at h2
  nlinarith

omit [DecidableEq ι] in
/-- The majorant condition for `1 - q_A` at `ξ` with scale `α = 1 - q_A(ξ)` and weights `λ`. -/
theorem quadMaj_neg {A : Matrix ι ι ℝ} (hAs : ∀ i k, A i k = A k i) {ξ : ι → ℝ} {lam : ι → ℝ}
    (hα : 0 < 1 - qForm A ξ) (h1 : ∀ i, |(A *ᵥ ξ) i| ≤ (1 - qForm A ξ) * lam i)
    (h2 : ∀ i k, |A i k| ≤ (1 - qForm A ξ) * lam i * lam k) :
    QuadMaj 1 0 (-A) ξ (1 - qForm A ξ) lam := by
  have hT : (-A + (-A)ᵀ) *ᵥ ξ = (-2 : ℝ) • (A *ᵥ ξ) := by
    have e : -A + (-A)ᵀ = (-2 : ℝ) • A := by
      ext i k
      simp only [Matrix.add_apply, Matrix.neg_apply, Matrix.transpose_apply, Matrix.smul_apply,
        smul_eq_mul, hAs k i]
      ring
    rw [e, Matrix.smul_mulVec]
  refine ⟨?_, fun i => ?_, fun i k => ?_⟩
  · have e : quadFn 1 0 (-A) ξ = 1 - qForm A ξ := by
      simp only [quadFn, qForm, zero_dotProduct, Matrix.neg_mulVec, dotProduct_neg]
      ring
    rw [e, abs_of_pos hα]
  · rw [hT]
    simp only [Pi.zero_apply, zero_add, Pi.smul_apply, smul_eq_mul, abs_mul]
    norm_num
    linarith [h1 i]
  · simp only [Matrix.neg_apply, hAs k i]
    rw [show -A i k + -A i k = -(2 * A i k) by ring, abs_neg, abs_mul, abs_two]
    linarith [h2 i k]

/-- **G1, star level** (A-MAJ at an interior point): with `α = 1 - q_A(ξ) > 0`, `β > 0` and
weights `λ` satisfying the majorant conditions,
`|∂^{2j}(c α^{p-m₊}β^{p-m₋})(ξ)| ≤ c α^{p-m₊} β^{p-m₋} Π_i (25 p² λ_i²)^{j_i}`. -/
theorem endpoint_majorant {p mp mm : ℕ} (hp : 2 ≤ p) {c : ℝ} (hc : 0 ≤ c)
    {A B : Matrix ι ι ℝ} (hAs : ∀ i k, A i k = A k i) (hBs : ∀ i k, B i k = B k i)
    {ξ : ι → ℝ} (hα : 0 < 1 - qForm A ξ) (hβ : 0 < 1 - qForm B ξ) {lam : ι → ℝ}
    (hlam : ∀ i, 0 ≤ lam i)
    (hA1 : ∀ i, |(A *ᵥ ξ) i| ≤ (1 - qForm A ξ) * lam i)
    (hA2 : ∀ i k, |A i k| ≤ (1 - qForm A ξ) * lam i * lam k)
    (hB1 : ∀ i, |(B *ᵥ ξ) i| ≤ (1 - qForm B ξ) * lam i)
    (hB2 : ∀ i k, |B i k| ≤ (1 - qForm B ξ) * lam i * lam k) (j : ι → ℕ) :
    |dEven (Finset.univ : Finset ι).toList j (trcObs p mp mm c A B) ξ| ≤
      c * (1 - qForm A ξ) ^ (p - mp) * (1 - qForm B ξ) ^ (p - mm) *
        ∏ i, (25 * (p : ℝ) ^ 2 * lam i ^ 2) ^ j i := by
  have h := SecA.pderivList_clipObs_le_of_interior (e₁ := p - mp) (e₂ := p - mm)
    (by linarith : qForm A ξ < 1) (by linarith : qForm B ξ < 1) hlam
    (quadMaj_const (abs_of_nonneg hc).le hlam ξ) (quadMaj_neg hAs hα hA1 hA2)
    (quadMaj_neg hBs hβ hB1 hB2) (dEvenList (Finset.univ : Finset ι).toList j)
  rw [length_dEvenList_univ, prod_map_dEvenList_univ] at h
  rw [dEven_eq_pderivList]
  refine h.trans ?_
  have hbase : 2 * (1 + ((p - mp : ℕ) : ℝ) + ((p - mm : ℕ) : ℝ)) ≤ 5 * p := by
    have h1 : ((p - mp : ℕ) : ℝ) ≤ p := by exact_mod_cast Nat.sub_le p mp
    have h2 : ((p - mm : ℕ) : ℝ) ≤ p := by exact_mod_cast Nat.sub_le p mm
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have hprod : (5 * (p : ℝ)) ^ (2 * ∑ i, j i) * ∏ i, lam i ^ (2 * j i) =
      ∏ i, (25 * (p : ℝ) ^ 2 * lam i ^ 2) ^ j i := by
    rw [Finset.mul_sum, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [pow_mul, pow_mul, ← mul_pow]
    ring
  have hK : 0 ≤ c * (1 - qForm A ξ) ^ (p - mp) * (1 - qForm B ξ) ^ (p - mm) :=
    mul_nonneg (mul_nonneg hc (pow_nonneg hα.le _)) (pow_nonneg hβ.le _)
  have hL : 0 ≤ ∏ i, lam i ^ (2 * j i) := Finset.prod_nonneg fun i _ => pow_nonneg (hlam i) _
  calc c * (1 - qForm A ξ) ^ (p - mp) * (1 - qForm B ξ) ^ (p - mm) *
        (2 * (1 + ((p - mp : ℕ) : ℝ) + ((p - mm : ℕ) : ℝ))) ^ (2 * ∑ i, j i) *
          ∏ i, lam i ^ (2 * j i)
      = c * (1 - qForm A ξ) ^ (p - mp) * (1 - qForm B ξ) ^ (p - mm) *
          ((2 * (1 + ((p - mp : ℕ) : ℝ) + ((p - mm : ℕ) : ℝ))) ^ (2 * ∑ i, j i) *
            ∏ i, lam i ^ (2 * j i)) := by ring
    _ ≤ c * (1 - qForm A ξ) ^ (p - mp) * (1 - qForm B ξ) ^ (p - mm) *
          ((5 * (p : ℝ)) ^ (2 * ∑ i, j i) * ∏ i, lam i ^ (2 * j i)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hbase _) hL) hK
    _ = _ := by rw [hprod]

/-- **G2** (grade sums, A-CNT with `T = 1/(d x²)`): for `d x ≥ 2` and `|ι| ≤ d`,
`Σ_{j ∈ retIdx k, j ≠ 0} Π_i x^{j_i} ≤ e² Σ_{g < k} (d x²)^{g+1}`. -/
theorem sum_ret_prod_le (k : ℕ) {d : ℝ} (hd : 1 ≤ d) (hcard : (Fintype.card ι : ℝ) ≤ d)
    {x : ℝ} (hdx : 2 ≤ d * x) :
    ∑ j ∈ (retIdx k : Finset (ι → ℕ)).erase 0, ∏ i, x ^ j i ≤
      Real.exp 2 * ∑ g ∈ Finset.range k, (d * x ^ 2) ^ (g + 1) := by
  have hd0 : 0 < d := by linarith
  have hx : 0 < x := by
    by_contra h
    push_neg at h
    nlinarith
  have hT : 0 < 1 / (d * x ^ 2) := by positivity
  have hxT : x * (1 / (d * x ^ 2)) = 1 / (d * x) := by field_simp
  have hxT2 : x * (1 / (d * x ^ 2)) ≤ 1 / 2 := by
    rw [hxT, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hgrade : ∀ g : ℕ, ∑ j ∈ (topIdx g : Finset (ι → ℕ)), ∏ i, x ^ j i ≤
      Real.exp 2 * (d * x ^ 2) ^ (g + 1) := by
    intro g
    refine (SecA.sum_topIdx_prod_pow_le g hx hT (by linarith)).trans ?_
    have h1 : 1 / (1 / (d * x ^ 2)) = d * x ^ 2 := one_div_one_div _
    have e : x ^ 2 * (1 / (d * x ^ 2)) = 1 / d := by field_simp
    have hq : 1 / 2 ≤ 1 - x * (1 / (d * x ^ 2)) := by linarith
    have h2 : 1 + x ^ 2 * (1 / (d * x ^ 2)) / (1 - x * (1 / (d * x ^ 2))) ≤ 1 + 2 / d := by
      rw [e]
      have : 1 / d / (1 - x * (1 / (d * x ^ 2))) ≤ 1 / d / (1 / 2) :=
        div_le_div_of_nonneg_left (by positivity) (by norm_num) hq
      have e2 : 1 / d / (1 / 2) = 2 / d := by field_simp
      linarith
    have h20 : 0 ≤ 1 + x ^ 2 * (1 / (d * x ^ 2)) / (1 - x * (1 / (d * x ^ 2))) := by
      have : 0 ≤ x ^ 2 * (1 / (d * x ^ 2)) / (1 - x * (1 / (d * x ^ 2))) :=
        div_nonneg (by positivity) (by linarith)
      linarith
    have h3 : (1 + 2 / d) ^ Fintype.card ι ≤ Real.exp 2 := by
      calc (1 + 2 / d) ^ Fintype.card ι ≤ Real.exp (2 / d) ^ Fintype.card ι := by
            gcongr
            linarith [Real.add_one_le_exp (2 / d)]
        _ = Real.exp (Fintype.card ι * (2 / d)) := by rw [← Real.exp_nat_mul]
        _ ≤ Real.exp 2 := Real.exp_le_exp.mpr (by
            rw [mul_div_assoc', div_le_iff₀ hd0]
            linarith)
    rw [h1]
    calc (d * x ^ 2) ^ (g + 1) *
          (1 + x ^ 2 * (1 / (d * x ^ 2)) / (1 - x * (1 / (d * x ^ 2)))) ^ Fintype.card ι
        ≤ (d * x ^ 2) ^ (g + 1) * (1 + 2 / d) ^ Fintype.card ι :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h20 h2 _) (by positivity)
      _ ≤ (d * x ^ 2) ^ (g + 1) * Real.exp 2 :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = Real.exp 2 * (d * x ^ 2) ^ (g + 1) := by ring
  have hsub : (retIdx k : Finset (ι → ℕ)).erase 0 ⊆
      (Finset.range k).biUnion (fun g => (topIdx g : Finset (ι → ℕ))) := by
    intro j hj
    obtain ⟨hj0, hjr⟩ := Finset.mem_erase.1 hj
    obtain ⟨hadm, hgr⟩ := mem_retIdx.1 hjr
    have hg1 : 1 ≤ grade j := by
      by_contra h
      push_neg at h
      exact hj0 (eq_zero_of_grade_eq_zero hadm (by omega))
    exact Finset.mem_biUnion.2
      ⟨grade j - 1, Finset.mem_range.2 (by omega), mem_topIdx.2 ⟨hadm, by omega⟩⟩
  have hdisj : ((Finset.range k : Finset ℕ) : Set ℕ).PairwiseDisjoint
      (fun g => (topIdx g : Finset (ι → ℕ))) := by
    intro g _ g' _ hgg'
    show Disjoint (topIdx g : Finset (ι → ℕ)) (topIdx g')
    refine Finset.disjoint_left.2 fun j hj hj' => hgg' ?_
    have h1 := (mem_topIdx.1 hj).2
    have h2 := (mem_topIdx.1 hj').2
    omega
  have hnn : ∀ j : ι → ℕ, 0 ≤ ∏ i, x ^ j i := fun j =>
    Finset.prod_nonneg fun i _ => pow_nonneg hx.le _
  calc ∑ j ∈ (retIdx k : Finset (ι → ℕ)).erase 0, ∏ i, x ^ j i
      ≤ ∑ j ∈ (Finset.range k).biUnion (fun g => (topIdx g : Finset (ι → ℕ))), ∏ i, x ^ j i :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => hnn j
    _ = ∑ g ∈ Finset.range k, ∑ j ∈ (topIdx g : Finset (ι → ℕ)), ∏ i, x ^ j i :=
        Finset.sum_biUnion hdisj
    _ ≤ ∑ g ∈ Finset.range k, Real.exp 2 * (d * x ^ 2) ^ (g + 1) :=
        Finset.sum_le_sum fun g _ => hgrade g
    _ = Real.exp 2 * ∑ g ∈ Finset.range k, (d * x ^ 2) ^ (g + 1) := by rw [Finset.mul_sum]

end Star

/-- The coordinates of `N_S(v)` as a list, each exactly once (`CapPoint.lN`). -/
noncomputable def nbL {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) (v : V) : List (nbhd G S v) :=
  (Finset.univ : Finset (nbhd G S v)).toList

section Law

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The common majorant weights `λ_i = a (2√(G⁺_vvG⁺_ii) + 2√(G⁻_vvG⁻_ii))`. -/
noncomputable def lamR (a : ℝ) (yp ym : V → ℝ) (σ : Config V) (S : Finset V) (v : V)
    (i : nbhd G S v) : ℝ :=
  a * (2 * Real.sqrt (greenP G a 1 yp σ S v v * greenP G a 1 yp σ S i i) +
    2 * Real.sqrt (greenP G a (-1) ym σ S v v * greenP G a (-1) ym σ S i i))

/-- The diagonal scale `ρ_i = h⁺_v + h⁺_i + h⁻_v + h⁻_i`. -/
noncomputable def rhoR (a : ℝ) (yp ym : V → ℝ) (σ : Config V) (S : Finset V) (v : V)
    (i : nbhd G S v) : ℝ :=
  hN G a 1 yp σ S v + hN G a 1 yp σ S i + hN G a (-1) ym σ S v + hN G a (-1) ym σ S i

/-- The random scale `Z = 1 + (max_{i ∈ N} ρ_i)²` (for `N ≠ ∅`). -/
noncomputable def ZR (a : ℝ) (yp ym : V → ℝ) (σ : Config V) (S : Finset V) (v : V)
    [Nonempty (nbhd G S v)] : ℝ :=
  1 + (Finset.univ.sup' Finset.univ_nonempty (rhoR G a yp ym σ S v)) ^ 2

/-- Root star bounds for one branch at a supported signing (F1): with `α = 1 - q_A(ξ) > 0`,
`|(Aξ)_i| = aα|G_vi| ≤ α a √(G_vvG_ii)` and `A_ii = a²α(G_vvG_ii - G_vi²) ≤ α a² G_vvG_ii`. -/
theorem root_star_bounds {a τ s : ℝ} (ha : 0 < a) (hτ : τ = 1 ∨ τ = -1) {y : V → ℝ}
    (hy : InCube s y) {S : Finset V} {v : V} (hv : v ∈ S) {σ : Config V}
    (hP : (precN G a τ y σ S).PosDef) (hPc : (precCore G a τ y σ S v).PosDef)
    (i : nbhd G S v) :
    0 < 1 - qForm (rootMat G a τ y σ S v) (rootSigns G σ S v) ∧
    |(rootMat G a τ y σ S v *ᵥ rootSigns G σ S v) i| ≤
      (1 - qForm (rootMat G a τ y σ S v) (rootSigns G σ S v)) *
        (a * Real.sqrt (greenP G a τ y σ S v v * greenP G a τ y σ S i i)) ∧
    rootMat G a τ y σ S v i i ≤ (1 - qForm (rootMat G a τ y σ S v) (rootSigns G σ S v)) *
        (a ^ 2 * (greenP G a τ y σ S v v * greenP G a τ y σ S i i)) ∧
    0 ≤ greenP G a τ y σ S v v * greenP G a τ y σ S i i := by
  have hy0 : ∀ j, 0 ≤ y j := fun j => (hy j).1
  obtain ⟨hα, -, hrow, hmark⟩ := root_branch G ha.ne' hτ hy0 hv hP hPc
  have hτ2 : τ ^ 2 = 1 := by rcases hτ with h | h <;> simp [h]
  have hτa : |τ| = 1 := by rcases hτ with h | h <;> simp [h]
  have hτ0 : τ ≠ 0 := by rcases hτ with h | h <;> simp [h]
  have hA := (shift_branch G hy0 (hy v).2 one_pos hPc).1
  have hAii : 0 ≤ rootMat G a τ y σ S v i i := hA.diag_nonneg
  have hsq := (root_diag_le G ha hτ hy hv hP hPc i).2
  have hm := hmark i i
  rw [starMark, starCore, ← hrow i, mul_pow, hτ2, one_mul] at hm
  have hr := hrow i
  rw [starRow] at hr
  have hαq : 1 - qForm (rootMat G a τ y σ S v) (rootSigns G σ S v) =
      starAlpha (rootMat G a τ y σ S v) (rootSigns G σ S v) := rfl
  rw [hαq]
  set α := starAlpha (rootMat G a τ y σ S v) (rootSigns G σ S v) with hαdef
  have ha2 : 0 < a ^ 2 := pow_pos ha 2
  have hc : 0 < a ^ 2 * α := mul_pos ha2 hα
  have h1 : greenP G a τ y σ S v v * greenP G a τ y σ S i i -
      greenP G a τ y σ S v i * greenP G a τ y σ S v i =
        rootMat G a τ y σ S v i i / (a ^ 2 * α) := by linarith
  have h2 := h1
  rw [eq_div_iff hc.ne'] at h2
  have hG0 : 0 ≤ greenP G a τ y σ S v v * greenP G a τ y σ S i i := by
    have := div_nonneg hAii hc.le
    nlinarith [mul_self_nonneg (greenP G a τ y σ S v i)]
  refine ⟨hα, ?_, ?_, hG0⟩
  · rw [eq_div_iff (mul_ne_zero (mul_ne_zero hτ0 ha.ne') hα.ne')] at hr
    have e : (rootMat G a τ y σ S v *ᵥ rootSigns G σ S v) i =
        -(greenP G a τ y σ S v i * (τ * a * α)) := by linarith
    rw [e, abs_neg, abs_mul, abs_mul, abs_mul, hτa, abs_of_pos ha, abs_of_pos hα, one_mul]
    have hgi : |greenP G a τ y σ S v i| ≤
        Real.sqrt (greenP G a τ y σ S v v * greenP G a τ y σ S i i) := Real.abs_le_sqrt hsq
    nlinarith [mul_le_mul_of_nonneg_right hgi (mul_pos ha hα).le]
  · nlinarith [mul_nonneg hc.le (mul_self_nonneg (greenP G a τ y σ S v i))]

variable {d p : ℕ}

/-- The majorant conditions of A-MAJ for one branch at a supported signing, with the common
weights `λ = lamR`. -/
theorem branch_majorant (hR : TRegime d p) {S : Finset V} {lam : ℝ} (hC : CapCtx G d p S lam)
    {yp ym : V → ℝ} (hyp : InCube (lam * sOf d p) yp) (hym : InCube (lam * sOf d p) ym)
    {τ : ℝ} {y : V → ℝ} (hb : IsBranch yp ym τ y) {v : V} (hv : v ∈ S) {σ : Config V}
    (hσ : wt G p (aOf d p) yp ym σ S ≠ 0) :
    0 < 1 - qForm (rootMat G (aOf d p) τ y σ S v) (rootSigns G σ S v) ∧
    (∀ i, |(rootMat G (aOf d p) τ y σ S v *ᵥ rootSigns G σ S v) i| ≤
      (1 - qForm (rootMat G (aOf d p) τ y σ S v) (rootSigns G σ S v)) *
        lamR G (aOf d p) yp ym σ S v i) ∧
    (∀ i k, |rootMat G (aOf d p) τ y σ S v i k| ≤
      (1 - qForm (rootMat G (aOf d p) τ y σ S v) (rootSigns G σ S v)) *
        lamR G (aOf d p) yp ym σ S v i * lamR G (aOf d p) yp ym σ S v k) := by
  have hp1 : 1 ≤ p := le_trans (by norm_num) hR.two_le_p
  have hy := inCube_of_cap G hR hC (hb.inCube hyp hym)
  have hy0 : ∀ j, 0 ≤ y j := fun j => (hy j).1
  obtain ⟨hP, hPc⟩ := posDef_branch G hp1 (fun i => (hyp i).1) (fun i => (hym i).1) hv hb hσ
  have ha := hR.aOf_pos
  have hA := (shift_branch G hy0 (hy v).2 one_pos hPc).1
  have hrs := root_star_bounds G ha hb.tau hy hv hP hPc
  -- `a √(G^τ_vv G^τ_ii) ≤ λ_i`
  have hlam : ∀ i : nbhd G S v, aOf d p * Real.sqrt (greenP G (aOf d p) τ y σ S v v *
      greenP G (aOf d p) τ y σ S i i) ≤ lamR G (aOf d p) yp ym σ S v i := by
    intro i
    have s1 := Real.sqrt_nonneg (greenP G (aOf d p) 1 yp σ S v v * greenP G (aOf d p) 1 yp σ S i i)
    have s2 := Real.sqrt_nonneg
      (greenP G (aOf d p) (-1) ym σ S v v * greenP G (aOf d p) (-1) ym σ S i i)
    unfold lamR
    rcases hb with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 h2
    · nlinarith
    · nlinarith
  have hlam0 : ∀ i : nbhd G S v, 0 ≤ lamR G (aOf d p) yp ym σ S v i := fun i =>
    mul_nonneg ha.le (add_nonneg (mul_nonneg zero_le_two (Real.sqrt_nonneg _))
      (mul_nonneg zero_le_two (Real.sqrt_nonneg _)))
  obtain ⟨hα0, -, -, -⟩ := root_branch G ha.ne' hb.tau hy0 hv hP hPc
  have hα0' : 0 < 1 - qForm (rootMat G (aOf d p) τ y σ S v) (rootSigns G σ S v) := hα0
  refine ⟨hα0', fun i => ?_, fun i k => ?_⟩
  · obtain ⟨-, h1, -, -⟩ := hrs i
    exact h1.trans (mul_le_mul_of_nonneg_left (hlam i) hα0'.le)
  · obtain ⟨-, -, hi, hGi⟩ := hrs i
    obtain ⟨-, -, hk, hGk⟩ := hrs k
    have hsq := psd_apply_sq_le hA i k
    have hAk : 0 ≤ rootMat G (aOf d p) τ y σ S v k k := hA.diag_nonneg
    set α := 1 - qForm (rootMat G (aOf d p) τ y σ S v) (rootSigns G σ S v) with hαdef
    set gi := Real.sqrt (greenP G (aOf d p) τ y σ S v v * greenP G (aOf d p) τ y σ S i i)
      with hgidef
    set gk := Real.sqrt (greenP G (aOf d p) τ y σ S v v * greenP G (aOf d p) τ y σ S k k)
      with hgkdef
    have hgi2 : gi ^ 2 = greenP G (aOf d p) τ y σ S v v * greenP G (aOf d p) τ y σ S i i :=
      Real.sq_sqrt hGi
    have hgk2 : gk ^ 2 = greenP G (aOf d p) τ y σ S v v * greenP G (aOf d p) τ y σ S k k :=
      Real.sq_sqrt hGk
    have hgi0 : 0 ≤ gi := Real.sqrt_nonneg _
    have hgk0 : 0 ≤ gk := Real.sqrt_nonneg _
    have hprod : rootMat G (aOf d p) τ y σ S v i i * rootMat G (aOf d p) τ y σ S v k k ≤
        (α * (aOf d p * gi) * (aOf d p * gk)) ^ 2 := by
      calc rootMat G (aOf d p) τ y σ S v i i * rootMat G (aOf d p) τ y σ S v k k
          ≤ (α * (aOf d p ^ 2 * (greenP G (aOf d p) τ y σ S v v *
                greenP G (aOf d p) τ y σ S i i))) *
              (α * (aOf d p ^ 2 * (greenP G (aOf d p) τ y σ S v v *
                greenP G (aOf d p) τ y σ S k k))) :=
            mul_le_mul hi hk hAk (mul_nonneg hα0'.le (mul_nonneg (sq_nonneg _) hGi))
        _ = (α * (aOf d p * gi) * (aOf d p * gk)) ^ 2 := by rw [← hgi2, ← hgk2]; ring
    have h0 : 0 ≤ α * (aOf d p * gi) * (aOf d p * gk) :=
      mul_nonneg (mul_nonneg hα0'.le (mul_nonneg ha.le hgi0)) (mul_nonneg ha.le hgk0)
    calc |rootMat G (aOf d p) τ y σ S v i k|
        ≤ Real.sqrt ((α * (aOf d p * gi) * (aOf d p * gk)) ^ 2) :=
          Real.abs_le_sqrt (hsq.trans hprod)
      _ = α * (aOf d p * gi) * (aOf d p * gk) := Real.sqrt_sq h0
      _ ≤ α * lamR G (aOf d p) yp ym σ S v i * lamR G (aOf d p) yp ym σ S v k :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hlam i) hα0'.le) (hlam k)
            (mul_nonneg ha.le hgk0) (mul_nonneg hα0'.le (hlam0 i))

/-- `2√(xy) ≤ x + y` for `x, y ≥ 0`. -/
theorem two_sqrt_mul_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : 2 * Real.sqrt (x * y) ≤ x + y := by
  have h : Real.sqrt (x * y) ≤ (x + y) / 2 := by
    rw [Real.sqrt_le_iff]
    exact ⟨by linarith, by nlinarith [sq_nonneg (x - y)]⟩
  linarith

/-- **G1 at a supported signing**: `|∂^{2j}F(ξ)/Φ(ξ)| ≤ X Π_i (25 p² λ_i²)^{j_i}`,
`F = c α^{p-m₊}β^{p-m₋}`, `X = c t₊^{m₊} t₋^{m₋}`. -/
theorem retained_pointwise (hR : TRegime d p) {S : Finset V} {lam : ℝ}
    (hC : CapCtx G d p S lam) {yp ym : V → ℝ} (hyp : InCube (lam * sOf d p) yp)
    (hym : InCube (lam * sOf d p) ym) {v : V} (hv : v ∈ S) {σ : Config V}
    (hσ : wt G p (aOf d p) yp ym σ S ≠ 0) {c : ℝ} (hc : 0 ≤ c) {mp mm : ℕ} (hmp : mp ≤ p)
    (hmm : mm ≤ p) (j : nbhd G S v → ℕ) :
    |dEven (nbL G S v) j (trcObs p mp mm c (rootMat G (aOf d p) 1 yp σ S v)
        (rootMat G (aOf d p) (-1) ym σ S v)) (rootSigns G σ S v) /
      starPhi p (rootMat G (aOf d p) 1 yp σ S v) (rootMat G (aOf d p) (-1) ym σ S v)
        (rootSigns G σ S v)| ≤
      c * rootT G (aOf d p) 1 yp σ S v ^ mp * rootT G (aOf d p) (-1) ym σ S v ^ mm *
        ∏ i, (25 * (p : ℝ) ^ 2 * lamR G (aOf d p) yp ym σ S v i ^ 2) ^ j i := by
  obtain ⟨hα, hA1, hA2⟩ := branch_majorant G hR hC hyp hym (isBranch_plus yp ym) hv hσ
  obtain ⟨hβ, hB1, hB2⟩ := branch_majorant G hR hC hyp hym (isBranch_minus yp ym) hv hσ
  have ha := hR.aOf_pos
  have hlam0 : ∀ i : nbhd G S v, 0 ≤ lamR G (aOf d p) yp ym σ S v i := fun i =>
    mul_nonneg ha.le (add_nonneg (mul_nonneg zero_le_two (Real.sqrt_nonneg _))
      (mul_nonneg zero_le_two (Real.sqrt_nonneg _)))
  have hEM := endpoint_majorant (p := p) (mp := mp) (mm := mm) hR.two_le_p hc
    (rootMat_apply_comm G _ 1 yp σ S v) (rootMat_apply_comm G _ (-1) ym σ S v) hα hβ hlam0
    hA1 hA2 hB1 hB2 j
  obtain ⟨-, -, ht1, ht2, -, -, -, -⟩ :=
    root_F1 G hR (fun i => (hyp i).1) (fun i => (hym i).1) hv hσ
  have ht1' : rootT G (aOf d p) 1 yp σ S v =
      1 / (1 - qForm (rootMat G (aOf d p) 1 yp σ S v) (rootSigns G σ S v)) := ht1
  have ht2' : rootT G (aOf d p) (-1) ym σ S v =
      1 / (1 - qForm (rootMat G (aOf d p) (-1) ym σ S v) (rootSigns G σ S v)) := ht2
  set α := 1 - qForm (rootMat G (aOf d p) 1 yp σ S v) (rootSigns G σ S v) with hαdef
  set β := 1 - qForm (rootMat G (aOf d p) (-1) ym σ S v) (rootSigns G σ S v) with hβdef
  have hΦ : starPhi p (rootMat G (aOf d p) 1 yp σ S v) (rootMat G (aOf d p) (-1) ym σ S v)
      (rootSigns G σ S v) = α ^ p * β ^ p := by
    simp only [starPhi, clipF]
    rw [← hαdef, ← hβdef, max_eq_left hα.le, max_eq_left hβ.le]
  have hΦ0 : 0 < α ^ p * β ^ p := mul_pos (pow_pos hα p) (pow_pos hβ p)
  rw [abs_div, hΦ, abs_of_pos hΦ0, div_le_iff₀ hΦ0, ht1', ht2']
  set P := ∏ i, (25 * (p : ℝ) ^ 2 * lamR G (aOf d p) yp ym σ S v i ^ 2) ^ j i with hP
  have e1 : α ^ p = α ^ (p - mp) * α ^ mp := by rw [← pow_add, Nat.sub_add_cancel hmp]
  have e2 : β ^ p = β ^ (p - mm) * β ^ mm := by rw [← pow_add, Nat.sub_add_cancel hmm]
  have hα1 := (pow_pos hα mp).ne'
  have hβ1 := (pow_pos hβ mm).ne'
  calc |dEven (nbL G S v) j (trcObs p mp mm c (rootMat G (aOf d p) 1 yp σ S v)
          (rootMat G (aOf d p) (-1) ym σ S v)) (rootSigns G σ S v)|
      ≤ c * α ^ (p - mp) * β ^ (p - mm) * P := hEM
    _ = c * (1 / α) ^ mp * (1 / β) ^ mm * P * (α ^ p * β ^ p) := by
        rw [e1, e2, _root_.one_div_pow, _root_.one_div_pow]
        field_simp

/-- `25 p² λ_i² ≤ (26 p²/d) Z` on the support (`2√(xy) ≤ x + y`, `G_ii = y_i h_i ≤ s h_i`,
`a²s² ≤ 1.01/d`, `ρ_i ≤ max ρ`). -/
theorem lam_sq_le (hR : TRegime d p) {S : Finset V} {lam : ℝ} (hC : CapCtx G d p S lam)
    {yp ym : V → ℝ} (hyp : InCube (lam * sOf d p) yp) (hym : InCube (lam * sOf d p) ym)
    {v : V} [Nonempty (nbhd G S v)] {σ : Config V} (hσ : wt G p (aOf d p) yp ym σ S ≠ 0)
    (i : nbhd G S v) :
    25 * (p : ℝ) ^ 2 * lamR G (aOf d p) yp ym σ S v i ^ 2 ≤
      26 * (p : ℝ) ^ 2 / d * ZR G (aOf d p) yp ym σ S v := by
  have hyp' := inCube_of_cap G hR hC hyp
  have hym' := inCube_of_cap G hR hC hym
  have ha := hR.aOf_pos
  have hs := hR.sOf_pos
  have hdR := hR.ten_pow_six_le_d
  have hd0 : (0 : ℝ) < d := lt_of_lt_of_le (by norm_num) hdR
  have hκ := hR.d_mul_kappa_le
  have hhp : ∀ u, 0 < hN G (aOf d p) 1 yp σ S u := fun u => hN_pos G hσ u
  have hhm : ∀ u, 0 < hN G (aOf d p) (-1) ym σ S u := fun u => hN_pos_minus G hσ u
  have hGp : ∀ u, 0 ≤ greenP G (aOf d p) 1 yp σ S u u ∧
      greenP G (aOf d p) 1 yp σ S u u ≤ sOf d p * hN G (aOf d p) 1 yp σ S u := fun u => by
    rw [greenP_self G (fun j => (hyp j).1) σ S u]
    exact ⟨mul_nonneg (hyp u).1 (hhp u).le, mul_le_mul_of_nonneg_right (hyp' u).2 (hhp u).le⟩
  have hGm : ∀ u, 0 ≤ greenP G (aOf d p) (-1) ym σ S u u ∧
      greenP G (aOf d p) (-1) ym σ S u u ≤ sOf d p * hN G (aOf d p) (-1) ym σ S u := fun u => by
    rw [greenP_self G (fun j => (hym j).1) σ S u]
    exact ⟨mul_nonneg (hym u).1 (hhm u).le, mul_le_mul_of_nonneg_right (hym' u).2 (hhm u).le⟩
  have hρ0 : ∀ u : nbhd G S v, 0 ≤ rhoR G (aOf d p) yp ym σ S v u := fun u => by
    unfold rhoR
    linarith [hhp v, hhp u, hhm v, hhm u]
  have hlamρ : lamR G (aOf d p) yp ym σ S v i ≤
      aOf d p * (sOf d p * rhoR G (aOf d p) yp ym σ S v i) := by
    unfold lamR rhoR
    have h1 := two_sqrt_mul_le (hGp v).1 (hGp i).1
    have h2 := two_sqrt_mul_le (hGm v).1 (hGm i).1
    have h3 := (hGp v).2
    have h4 := (hGp i).2
    have h5 := (hGm v).2
    have h6 := (hGm i).2
    refine mul_le_mul_of_nonneg_left ?_ ha.le
    nlinarith
  have hlam0 : 0 ≤ lamR G (aOf d p) yp ym σ S v i :=
    mul_nonneg ha.le (add_nonneg (mul_nonneg zero_le_two (Real.sqrt_nonneg _))
      (mul_nonneg zero_le_two (Real.sqrt_nonneg _)))
  have hρR : rhoR G (aOf d p) yp ym σ S v i ≤
      Finset.univ.sup' Finset.univ_nonempty (rhoR G (aOf d p) yp ym σ S v) :=
    Finset.le_sup' (rhoR G (aOf d p) yp ym σ S v) (Finset.mem_univ i)
  have hZ : rhoR G (aOf d p) yp ym σ S v i ^ 2 ≤ ZR G (aOf d p) yp ym σ S v := by
    unfold ZR
    nlinarith [hρ0 i]
  have hl2 : lamR G (aOf d p) yp ym σ S v i ^ 2 ≤
      aOf d p ^ 2 * sOf d p ^ 2 * rhoR G (aOf d p) yp ym σ S v i ^ 2 := by
    calc lamR G (aOf d p) yp ym σ S v i ^ 2
        ≤ (aOf d p * (sOf d p * rhoR G (aOf d p) yp ym σ S v i)) ^ 2 :=
          pow_le_pow_left₀ hlam0 hlamρ 2
      _ = _ := by ring
  have hκd : aOf d p ^ 2 * sOf d p ^ 2 ≤ 101 / 100 / d := by
    rw [le_div_iff₀ hd0]; linarith
  have hZ0 : 0 ≤ ZR G (aOf d p) yp ym σ S v := le_trans (sq_nonneg _) hZ
  have hp0 : (0 : ℝ) ≤ (p : ℝ) ^ 2 := by positivity
  calc 25 * (p : ℝ) ^ 2 * lamR G (aOf d p) yp ym σ S v i ^ 2
      ≤ 25 * (p : ℝ) ^ 2 * (101 / 100 / d * ZR G (aOf d p) yp ym σ S v) := by
        refine mul_le_mul_of_nonneg_left (hl2.trans ?_) (by positivity)
        exact mul_le_mul hκd hZ (sq_nonneg _) (by positivity)
    _ ≤ 26 * (p : ℝ) ^ 2 / d * ZR G (aOf d p) yp ym σ S v := by
        rw [show 25 * (p : ℝ) ^ 2 * (101 / 100 / d * ZR G (aOf d p) yp ym σ S v) =
          (2525 / 100) * (p : ℝ) ^ 2 / d * ZR G (aOf d p) yp ym σ S v by ring]
        gcongr
        norm_num

/-- `(a + b + c + e)^N ≤ 8^N (a^N + b^N + c^N + e^N)` for nonnegative reals. -/
theorem add4_pow_le {a b c e : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (he : 0 ≤ e)
    (N : ℕ) : (a + b + c + e) ^ N ≤ 8 ^ N * (a ^ N + b ^ N + c ^ N + e ^ N) := by
  have h1 := add_pow_le_two_pow_mul (add_nonneg (add_nonneg ha hb) hc) he N
  have h2 := add_pow_le_two_pow_mul (add_nonneg ha hb) hc N
  have h3 := add_pow_le_two_pow_mul ha hb N
  have h8 : (8 : ℝ) ^ N = 2 ^ N * 2 ^ N * 2 ^ N := by rw [← mul_pow, ← mul_pow]; norm_num
  have h2N : (1 : ℝ) ≤ 2 ^ N := one_le_pow₀ (by norm_num)
  have hcN := pow_nonneg hc N
  have heN := pow_nonneg he N
  have habN := add_nonneg (pow_nonneg ha N) (pow_nonneg hb N)
  rw [h8]
  calc (a + b + c + e) ^ N ≤ 2 ^ N * ((a + b + c) ^ N + e ^ N) := h1
    _ ≤ 2 ^ N * (2 ^ N * ((a + b) ^ N + c ^ N) + e ^ N) := by gcongr
    _ ≤ 2 ^ N * (2 ^ N * (2 ^ N * (a ^ N + b ^ N) + c ^ N) + e ^ N) := by gcongr
    _ ≤ 2 ^ N * 2 ^ N * 2 ^ N * (a ^ N + b ^ N + c ^ N + e ^ N) := by
        have k1 : c ^ N ≤ 2 ^ N * c ^ N := le_mul_of_one_le_left hcN h2N
        have k2 : e ^ N ≤ 2 ^ N * 2 ^ N * e ^ N :=
          le_mul_of_one_le_left heN (one_le_mul_of_one_le_of_one_le h2N h2N)
        nlinarith [mul_le_mul_of_nonneg_left k1 (pow_nonneg (zero_le_two : (0 : ℝ) ≤ 2) N)]

/-- Moments of the scale: `E Z^n ≤ 5 d 512^n` for `4n ≤ p` (T.DSTAR over `N`, F2). -/
theorem Z_moment_le (hR : TRegime d p) {S : Finset V} {lam : ℝ} (hC : CapCtx G d p S lam)
    {yp ym : V → ℝ} (hyp : InCube (lam * sOf d p) yp) (hym : InCube (lam * sOf d p) ym)
    {v : V} (hv : v ∈ S) [Nonempty (nbhd G S v)] {n : ℕ} (hn : 4 * n ≤ p) :
    lawE G p (aOf d p) yp ym S (fun σ => ZR G (aOf d p) yp ym σ S v ^ n) ≤
      5 * d * 512 ^ n := by
  have hdR := hR.ten_pow_six_le_d
  have hNS : ∀ u : nbhd G S v, (u : V) ∈ S := fun u => (Finset.mem_filter.1 u.2).1
  have hcard : ((Finset.univ : Finset (nbhd G S v)).card : ℝ) ≤ d := by
    rw [Finset.card_univ]
    exact_mod_cast card_nbhd_le G hC.deg S v
  have hn2 : 2 * (2 * n) ≤ p := by omega
  have hmom : ∀ (τ : ℝ) (y : V → ℝ), IsBranch yp ym τ y → ∀ u ∈ S,
      lawE G p (aOf d p) yp ym S (fun σ => hN G (aOf d p) τ y σ S u ^ (2 * n)) ≤ 4 ^ n :=
    fun τ y hb u hu => (hN_moment_le G hR hC hyp hym hb hu hn2).trans_eq (by rw [pow_mul]; norm_num)
  -- pointwise domination on the support
  have hpt : ∀ σ, wt G p (aOf d p) yp ym σ S ≠ 0 →
      ZR G (aOf d p) yp ym σ S v ^ n ≤ 2 ^ n * (1 + ∑ u : nbhd G S v, 8 ^ (2 * n) *
        (hN G (aOf d p) 1 yp σ S v ^ (2 * n) + hN G (aOf d p) 1 yp σ S u ^ (2 * n) +
          hN G (aOf d p) (-1) ym σ S v ^ (2 * n) + hN G (aOf d p) (-1) ym σ S u ^ (2 * n))) := by
    intro σ hσ
    have hhp : ∀ u, 0 < hN G (aOf d p) 1 yp σ S u := fun u => hN_pos G hσ u
    have hhm : ∀ u, 0 < hN G (aOf d p) (-1) ym σ S u := fun u => hN_pos_minus G hσ u
    have hρ0 : ∀ u : nbhd G S v, 0 ≤ rhoR G (aOf d p) yp ym σ S v u := fun u => by
      unfold rhoR
      linarith [hhp v, hhp u, hhm v, hhm u]
    obtain ⟨u₀, -, hu₀⟩ := (Finset.univ : Finset (nbhd G S v)).exists_mem_eq_sup'
      Finset.univ_nonempty (rhoR G (aOf d p) yp ym σ S v)
    have hR2 : (Finset.univ.sup' Finset.univ_nonempty (rhoR G (aOf d p) yp ym σ S v) ^ 2) ^ n ≤
        ∑ u : nbhd G S v, rhoR G (aOf d p) yp ym σ S v u ^ (2 * n) := by
      rw [hu₀, ← pow_mul]
      exact Finset.single_le_sum (f := fun u => rhoR G (aOf d p) yp ym σ S v u ^ (2 * n))
        (fun u _ => pow_nonneg (hρ0 u) _) (Finset.mem_univ u₀)
    have hρ : ∀ u : nbhd G S v, rhoR G (aOf d p) yp ym σ S v u ^ (2 * n) ≤ 8 ^ (2 * n) *
        (hN G (aOf d p) 1 yp σ S v ^ (2 * n) + hN G (aOf d p) 1 yp σ S u ^ (2 * n) +
          hN G (aOf d p) (-1) ym σ S v ^ (2 * n) + hN G (aOf d p) (-1) ym σ S u ^ (2 * n)) :=
      fun u => add4_pow_le (hhp v).le (hhp u).le (hhm v).le (hhm u).le _
    calc ZR G (aOf d p) yp ym σ S v ^ n
        ≤ 2 ^ n * (1 ^ n + (Finset.univ.sup' Finset.univ_nonempty
            (rhoR G (aOf d p) yp ym σ S v) ^ 2) ^ n) :=
          add_pow_le_two_pow_mul zero_le_one (sq_nonneg _) n
      _ ≤ _ := by
          rw [one_pow]
          gcongr
          exact hR2.trans (Finset.sum_le_sum fun u _ => hρ u)
  have hZw := Zw_pos_cap G hR hC hyp hym
  calc lawE G p (aOf d p) yp ym S (fun σ => ZR G (aOf d p) yp ym σ S v ^ n)
      ≤ lawE G p (aOf d p) yp ym S (fun σ => 2 ^ n * (1 + ∑ u : nbhd G S v, 8 ^ (2 * n) *
        (hN G (aOf d p) 1 yp σ S v ^ (2 * n) + hN G (aOf d p) 1 yp σ S u ^ (2 * n) +
          hN G (aOf d p) (-1) ym σ S v ^ (2 * n) + hN G (aOf d p) (-1) ym σ S u ^ (2 * n)))) :=
        lawE_mono G hpt
    _ = 2 ^ n * (1 + ∑ u : nbhd G S v, 8 ^ (2 * n) *
          (lawE G p (aOf d p) yp ym S (fun σ => hN G (aOf d p) 1 yp σ S v ^ (2 * n)) +
            lawE G p (aOf d p) yp ym S (fun σ => hN G (aOf d p) 1 yp σ S u ^ (2 * n)) +
            lawE G p (aOf d p) yp ym S (fun σ => hN G (aOf d p) (-1) ym σ S v ^ (2 * n)) +
            lawE G p (aOf d p) yp ym S (fun σ => hN G (aOf d p) (-1) ym σ S u ^ (2 * n)))) := by
        rw [lawE_const_mul, lawE_add, lawE_const_one G hZw, lawE_sum]
        congr 2
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [lawE_const_mul, lawE_add, lawE_add, lawE_add]
    _ ≤ 2 ^ n * (1 + ∑ _u : nbhd G S v, 8 ^ (2 * n) * (4 ^ n + 4 ^ n + 4 ^ n + 4 ^ n)) := by
        gcongr with u
        · exact hmom 1 yp (isBranch_plus yp ym) v hv
        · exact hmom 1 yp (isBranch_plus yp ym) u (hNS u)
        · exact hmom (-1) ym (isBranch_minus yp ym) v hv
        · exact hmom (-1) ym (isBranch_minus yp ym) u (hNS u)
    _ = 2 ^ n * (1 + ((Finset.univ : Finset (nbhd G S v)).card : ℝ) * (4 * 256 ^ n)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        congr 2
        rw [pow_mul, show (8 : ℝ) ^ 2 = 64 by norm_num, show (256 : ℝ) ^ n = 64 ^ n * 4 ^ n by
          rw [← mul_pow]; norm_num]
        ring
    _ ≤ 2 ^ n * (5 * d * 256 ^ n) := by
        have h1 : (1 : ℝ) ≤ 256 ^ n := one_le_pow₀ (by norm_num)
        gcongr
        nlinarith
    _ = 5 * d * 512 ^ n := by
        rw [show (512 : ℝ) ^ n = 2 ^ n * 256 ^ n by rw [← mul_pow]; norm_num]
        ring

/-- `E X² ≤ (d^{30})²` for `X = w t₊^{m₊} t₋^{m₋}`, `0 ≤ w ≤ d^{20}`, `m_± ≤ 3`
(`t^m ≤ 1 + t³`, F2 for `t^{12}`). -/
theorem X_sq_le (hR : TRegime d p) {S : Finset V} {lam : ℝ} (hC : CapCtx G d p S lam)
    {yp ym : V → ℝ} (hyp : InCube (lam * sOf d p) yp) (hym : InCube (lam * sOf d p) ym)
    {v : V} (hv : v ∈ S) {w : Config V → ℝ}
    (hwb : ∀ σ, wtCore G p (aOf d p) yp ym σ S v ≠ 0 → 0 ≤ w σ ∧ w σ ≤ (d : ℝ) ^ 20)
    {mp mm : ℕ} (hmp : mp ≤ 3) (hmm : mm ≤ 3) :
    lawE G p (aOf d p) yp ym S (fun σ => (w σ * rootT G (aOf d p) 1 yp σ S v ^ mp *
      rootT G (aOf d p) (-1) ym σ S v ^ mm) ^ 2) ≤ ((d : ℝ) ^ 30) ^ 2 := by
  have hp6 := hR.hp
  have hdR := hR.ten_pow_six_le_d
  have hp1n : 1 ≤ p := le_trans (by norm_num) hp6
  have hyp0 : ∀ i, 0 ≤ yp i := fun i => (hyp i).1
  have hym0 : ∀ i, 0 ≤ ym i := fun i => (hym i).1
  have hZw := Zw_pos_cap G hR hC hyp hym
  have hpow3 : ∀ {t : ℝ} {m : ℕ}, 0 ≤ t → m ≤ 3 → t ^ m ≤ 1 + t ^ 3 := by
    intro t m ht hm
    rcases le_total t 1 with h | h
    · linarith [pow_le_one₀ ht h (n := m), pow_nonneg ht 3]
    · linarith [pow_le_pow_right₀ h hm]
  have hpt : ∀ σ, wt G p (aOf d p) yp ym σ S ≠ 0 →
      (w σ * rootT G (aOf d p) 1 yp σ S v ^ mp * rootT G (aOf d p) (-1) ym σ S v ^ mm) ^ 2 ≤
        (d : ℝ) ^ 40 * (16 * (1 + rootT G (aOf d p) 1 yp σ S v ^ 12) +
          16 * (1 + rootT G (aOf d p) (-1) ym σ S v ^ 12)) := by
    intro σ hσ
    have hc := wtCore_ne_zero_of_wt G hp1n hyp0 hym0 hv hσ
    obtain ⟨hw0, hw1⟩ := hwb σ hc
    obtain ⟨ht1, ht2⟩ := rootT_nonneg G hyp0 hym0 hσ v
    set t₁ := rootT G (aOf d p) 1 yp σ S v
    set t₂ := rootT G (aOf d p) (-1) ym σ S v
    have hA := hpow3 ht1 hmp
    have hB := hpow3 ht2 hmm
    have hA0 := pow_nonneg ht1 mp
    have hB0 := pow_nonneg ht2 mm
    have hX : w σ * t₁ ^ mp * t₂ ^ mm ≤ (d : ℝ) ^ 20 * ((1 + t₁ ^ 3) * (1 + t₂ ^ 3)) :=
      mul_le_mul (mul_le_mul hw1 hA hA0 (by positivity)) hB hB0 (by positivity) |>.trans_eq
        (by ring)
    have hX0 : 0 ≤ w σ * t₁ ^ mp * t₂ ^ mm := by positivity
    have hP1 : (1 + t₁ ^ 3) ^ 4 ≤ 16 * (1 + t₁ ^ 12) := by
      have h := add_pow_le_two_pow_mul zero_le_one (pow_nonneg ht1 3) 4
      have e : (1 : ℝ) ^ 4 + (t₁ ^ 3) ^ 4 = 1 + t₁ ^ 12 := by ring
      rw [e] at h
      norm_num at h
      exact h
    have hP2 : (1 + t₂ ^ 3) ^ 4 ≤ 16 * (1 + t₂ ^ 12) := by
      have h := add_pow_le_two_pow_mul zero_le_one (pow_nonneg ht2 3) 4
      have e : (1 : ℝ) ^ 4 + (t₂ ^ 3) ^ 4 = 1 + t₂ ^ 12 := by ring
      rw [e] at h
      norm_num at h
      exact h
    have hAB : ((1 + t₁ ^ 3) * (1 + t₂ ^ 3)) ^ 2 ≤ (1 + t₁ ^ 3) ^ 4 + (1 + t₂ ^ 3) ^ 4 := by
      nlinarith [sq_nonneg ((1 + t₁ ^ 3) ^ 2 - (1 + t₂ ^ 3) ^ 2), pow_nonneg ht1 3,
        pow_nonneg ht2 3]
    calc (w σ * t₁ ^ mp * t₂ ^ mm) ^ 2
        ≤ ((d : ℝ) ^ 20 * ((1 + t₁ ^ 3) * (1 + t₂ ^ 3))) ^ 2 := pow_le_pow_left₀ hX0 hX 2
      _ = (d : ℝ) ^ 40 * ((1 + t₁ ^ 3) * (1 + t₂ ^ 3)) ^ 2 := by ring
      _ ≤ (d : ℝ) ^ 40 * (16 * (1 + t₁ ^ 12) + 16 * (1 + t₂ ^ 12)) := by
          gcongr
          linarith
  have hm1 := rootT_moment_le G hR hC hyp hym (isBranch_plus yp ym) hv (n := 12) (by omega)
  have hm2 := rootT_moment_le G hR hC hyp hym (isBranch_minus yp ym) hv (n := 12) (by omega)
  calc _ ≤ lawE G p (aOf d p) yp ym S (fun σ => (d : ℝ) ^ 40 *
          (16 * (1 + rootT G (aOf d p) 1 yp σ S v ^ 12) +
            16 * (1 + rootT G (aOf d p) (-1) ym σ S v ^ 12))) := lawE_mono G hpt
    _ = (d : ℝ) ^ 40 * (16 * (1 + lawE G p (aOf d p) yp ym S
            (fun σ => rootT G (aOf d p) 1 yp σ S v ^ 12)) +
          16 * (1 + lawE G p (aOf d p) yp ym S
            (fun σ => rootT G (aOf d p) (-1) ym σ S v ^ 12))) := by
        rw [lawE_const_mul, lawE_add, lawE_const_mul, lawE_const_mul, lawE_add, lawE_add,
          lawE_const_one G hZw]
    _ ≤ (d : ℝ) ^ 40 * (16 * (1 + 5 ^ 12) + 16 * (1 + 5 ^ 12)) := by gcongr
    _ ≤ ((d : ℝ) ^ 30) ^ 2 := by
        have h20 : (32 * (1 + 5 ^ 12) : ℝ) ≤ (d : ℝ) ^ 20 :=
          le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hdR 20)
        calc (d : ℝ) ^ 40 * (16 * (1 + 5 ^ 12) + 16 * (1 + 5 ^ 12))
            = (32 * (1 + 5 ^ 12)) * (d : ℝ) ^ 40 := by ring
          _ ≤ (d : ℝ) ^ 20 * (d : ℝ) ^ 40 := mul_le_mul_of_nonneg_right h20 (by positivity)
          _ = ((d : ℝ) ^ 30) ^ 2 := by ring

/-- `|E f| ≤ E g` when `|f| ≤ g` on the support. -/
theorem abs_lawE_le {p : ℕ} {a : ℝ} {yp ym : V → ℝ} {S : Finset V} {f g : Config V → ℝ}
    (h : ∀ σ, wt G p a yp ym σ S ≠ 0 → |f σ| ≤ g σ) :
    |lawE G p a yp ym S f| ≤ lawE G p a yp ym S g := by
  rw [abs_le]
  constructor
  · have h1 : lawE G p a yp ym S (fun σ => (-1) * g σ) ≤ lawE G p a yp ym S f :=
      lawE_mono G fun σ hσ => by linarith [neg_abs_le (f σ), h σ hσ]
    rw [lawE_const_mul] at h1
    linarith
  · exact lawE_mono G fun σ hσ => (le_abs_self _).trans (h σ hσ)

/-- **Truncation** (replaces T.IL with grade-dependent exponents): if
`E X² · E Z^{2(2n+m)} ≤ (Λ^m Λ^{2n} θ)²`, then `E[X Z^{2n}] ≤ Λ^{2n}(E X + θ)` (split at
`Z = Λ`; Cauchy–Schwarz on `{Z > Λ}` with the extra factor `(Z/Λ)^m`). -/
theorem trunc_moment {p : ℕ} {a : ℝ} {yp ym : V → ℝ} {S : Finset V} {X Z : Config V → ℝ}
    (hX : ∀ σ, wt G p a yp ym σ S ≠ 0 → 0 ≤ X σ) (hZ : ∀ σ, wt G p a yp ym σ S ≠ 0 → 0 ≤ Z σ)
    {n m : ℕ} {Λ θ : ℝ} (hΛ : 0 < Λ) (hθ : 0 ≤ θ)
    (hCS : lawE G p a yp ym S (fun σ => X σ ^ 2) *
        lawE G p a yp ym S (fun σ => Z σ ^ (2 * (2 * n + m))) ≤ (Λ ^ m * Λ ^ (2 * n) * θ) ^ 2) :
    lawE G p a yp ym S (fun σ => X σ * Z σ ^ (2 * n)) ≤
      Λ ^ (2 * n) * (lawE G p a yp ym S X + θ) := by
  have hΛm : 0 < Λ ^ m := pow_pos hΛ m
  have hK0 : 0 ≤ Λ ^ m * Λ ^ (2 * n) * θ := by positivity
  -- pointwise splitting
  have hpt : ∀ σ, wt G p a yp ym σ S ≠ 0 → Λ ^ m * (X σ * Z σ ^ (2 * n)) ≤
      Λ ^ m * Λ ^ (2 * n) * X σ + X σ * Z σ ^ (2 * n + m) := by
    intro σ hσ
    have hX0 := hX σ hσ
    have hZ0 := hZ σ hσ
    have hXZ : 0 ≤ X σ * Z σ ^ (2 * n + m) := mul_nonneg hX0 (pow_nonneg hZ0 _)
    rcases le_total (Z σ) Λ with h | h
    · have := pow_le_pow_left₀ hZ0 h (2 * n)
      nlinarith [mul_le_mul_of_nonneg_left this (mul_nonneg hΛm.le hX0)]
    · have hm := pow_le_pow_left₀ hΛ.le h m
      have e : X σ * Z σ ^ (2 * n + m) = Z σ ^ m * (X σ * Z σ ^ (2 * n)) := by ring
      rw [e]
      nlinarith [mul_le_mul_of_nonneg_right hm (mul_nonneg hX0 (pow_nonneg hZ0 (2 * n))),
        mul_nonneg (mul_nonneg hΛm.le (pow_nonneg hΛ.le (2 * n))) hX0]
  -- Cauchy–Schwarz on the tail
  have hCS2 : lawE G p a yp ym S (fun σ => X σ * Z σ ^ (2 * n + m)) ≤
      Λ ^ m * Λ ^ (2 * n) * θ := by
    have h := wavg_mul_sq_le (w := fun σ => wt G p a yp ym σ S) (fun σ => wt_nonneg G σ) X
      (fun σ => Z σ ^ (2 * n + m))
    simp only [← pow_mul, mul_comm (2 * n + m) 2] at h
    rw [← lawE_eq_wavg, ← lawE_eq_wavg, ← lawE_eq_wavg] at h
    exact abs_le_of_sq_le_sq' (h.trans hCS) hK0 |>.2
  have h1 := lawE_mono G hpt
  rw [lawE_const_mul, lawE_add, lawE_const_mul] at h1
  have h2 : Λ ^ m * lawE G p a yp ym S (fun σ => X σ * Z σ ^ (2 * n)) ≤
      Λ ^ m * (Λ ^ (2 * n) * (lawE G p a yp ym S X + θ)) := by nlinarith
  exact le_of_mul_le_mul_left h2 hΛm

/-- `5 d^{81} ≤ 2^{4 kIL d}` (`4 kIL d ≥ 120 log d`, `log 2 > 0.69`). -/
theorem two_pow_kIL (hd : 5 ≤ d) : (5 : ℝ) * (d : ℝ) ^ 81 ≤ 2 ^ (4 * kIL d) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hd5 : (5 : ℝ) ≤ d := by exact_mod_cast hd
  have hlog : 0 ≤ Real.log d := Real.log_nonneg (by linarith)
  have hk := kIL_ge d
  have hl2 := Real.log_two_gt_d9
  calc (5 : ℝ) * (d : ℝ) ^ 81 ≤ (d : ℝ) * (d : ℝ) ^ 81 :=
        mul_le_mul_of_nonneg_right hd5 (by positivity)
    _ = Real.exp (((82 : ℕ) : ℝ) * Real.log d) := by
        rw [← Real.log_pow, Real.exp_log (pow_pos hd0 82)]
        ring
    _ ≤ Real.exp ((4 * kIL d : ℕ) * Real.log 2) := by
        refine Real.exp_le_exp.mpr ?_
        push_cast
        nlinarith [mul_le_mul_of_nonneg_right hk (by linarith : (0 : ℝ) ≤ Real.log 2),
          mul_le_mul_of_nonneg_left hl2.le hlog]
    _ = 2 ^ (4 * kIL d) := by
        rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]

end Law

/-- `32 k_* + 32 kIL d ≤ p` for large `d`. -/
theorem eventually_trc : Eventually fun _ _ d p _ => 32 * kStar d p + 32 * kIL d ≤ p := by
  refine ((eventually_log_le 2000).and (eventually_le_log 1024)).mono ?_
  rintro c₀ κ₀ d p h ⟨h1, h2⟩
  have hL0 : 0 < Real.log d := by linarith
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hk : (kStar d p : ℝ) < 16 * p / Real.log d + 1 :=
    Nat.ceil_lt_add_one (div_nonneg (by positivity) hL0.le)
  have h16 : 16 * (p : ℝ) / Real.log d ≤ p / 64 := by
    rw [div_le_div_iff₀ hL0 (by norm_num)]
    nlinarith
  have hkI : (kIL d : ℝ) < 30 * Real.log d + 1 := Nat.ceil_lt_add_one (by linarith)
  have : ((32 * kStar d p + 32 * kIL d : ℕ) : ℝ) ≤ p := by
    push_cast
    nlinarith
  exact_mod_cast this

/-- **TRC-G** (retained grades `1 ≤ |j|_g ≤ k_*` of T.TRC under the actual law). See the module
docstring for the proof sketch and checks. -/
theorem retained_grades_le : ∃ C : ℝ, 0 < C ∧ Eventually fun _ _ d p _ =>
    ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
      (S : Finset V) (lam : ℝ) (yp ym : V → ℝ) (v : V), CapCtx G d p S lam →
      InCube (lam * sOf d p) yp → InCube (lam * sOf d p) ym → v ∈ S →
      ∀ (w : Config V → ℝ) (mp mm : ℕ), mp ≤ 3 → mm ≤ 3 →
        (∀ σ, wtCore G p (aOf d p) yp ym σ S v ≠ 0 → 0 ≤ w σ ∧ w σ ≤ (d : ℝ) ^ 20) →
        |∑ j ∈ (retIdx (kStar d p) : Finset (nbhd G S v → ℕ)).erase 0, ecoefM j *
            lawE G p (aOf d p) yp ym S (fun σ =>
              dEven (nbL G S v) j (trcObs p mp mm (w σ) (rootMat G (aOf d p) 1 yp σ S v)
                  (rootMat G (aOf d p) (-1) ym σ S v)) (rootSigns G σ S v) /
                starPhi p (rootMat G (aOf d p) 1 yp σ S v) (rootMat G (aOf d p) (-1) ym σ S v)
                  (rootSigns G σ S v))| ≤
          C * ((p : ℝ) ^ 4 / d) *
            (lawE G p (aOf d p) yp ym S (fun σ => w σ * rootT G (aOf d p) 1 yp σ S v ^ mp *
              rootT G (aOf d p) (-1) ym σ S v ^ mm) + vth d) := by
  refine ⟨2 * (676 * 1024 ^ 2) * Real.exp 2, by positivity,
    ((eventually_regime 1).and eventually_trc).mono ?_⟩
  rintro c₀ κ₀ d p h ⟨⟨hR, -, -⟩, hreg⟩ V _ _ G _ S lam yp ym v hC hyp hym hv w mp mm hmp hmm
    hwb
  classical
  have hp6 := hR.hp
  have hdR := hR.ten_pow_six_le_d
  have hd0 : (0 : ℝ) < d := lt_of_lt_of_le (by norm_num) hdR
  have hd1 : (1 : ℝ) ≤ d := le_trans (by norm_num) hdR
  have hd5 : 5 ≤ d := le_trans (by norm_num) hR.ten_pow_six_le_nat
  have hp1n : 1 ≤ p := le_trans (by norm_num) hp6
  have hyp0 : ∀ i, 0 ≤ yp i := fun i => (hyp i).1
  have hym0 : ∀ i, 0 ≤ ym i := fun i => (hym i).1
  have hθ : 0 < vth d := by unfold vth; positivity
  set X : Config V → ℝ := fun σ => w σ * rootT G (aOf d p) 1 yp σ S v ^ mp *
    rootT G (aOf d p) (-1) ym σ S v ^ mm with hXdef
  have hX0 : ∀ σ, wt G p (aOf d p) yp ym σ S ≠ 0 → 0 ≤ X σ := fun σ hσ => by
    have hc := wtCore_ne_zero_of_wt G hp1n hyp0 hym0 hv hσ
    obtain ⟨ht1, ht2⟩ := rootT_nonneg G hyp0 hym0 hσ v
    exact mul_nonneg (mul_nonneg (hwb σ hc).1 (pow_nonneg ht1 _)) (pow_nonneg ht2 _)
  have hxw0 : 0 ≤ lawE G p (aOf d p) yp ym S X := lawE_nonneg G hX0
  have hxθ : 0 ≤ lawE G p (aOf d p) yp ym S X + vth d := by linarith
  have hRHS0 : 0 ≤ 2 * (676 * 1024 ^ 2) * Real.exp 2 * ((p : ℝ) ^ 4 / d) *
      (lawE G p (aOf d p) yp ym S X + vth d) := mul_nonneg (by positivity) hxθ
  rcases isEmpty_or_nonempty (nbhd G S v) with hN | hN
  · have hE : (retIdx (kStar d p) : Finset (nbhd G S v → ℕ)).erase 0 = ∅ := by
      ext j
      simp only [Finset.mem_erase, Finset.notMem_empty, iff_false, not_and]
      intro hj
      exact absurd (funext fun i => (IsEmpty.false i).elim) hj
    rw [hE, Finset.sum_empty, abs_zero]
    exact hRHS0
  set k := kStar d p with hk
  set Z : Config V → ℝ := fun σ => ZR G (aOf d p) yp ym σ S v with hZdef
  set xp : Config V → ℝ := fun σ => 26 * (p : ℝ) ^ 2 / d * Z σ with hxp
  have hZ1 : ∀ σ, 1 ≤ Z σ := fun σ => by
    simp only [hZdef, ZR]
    nlinarith [sq_nonneg (Finset.univ.sup' Finset.univ_nonempty (rhoR G (aOf d p) yp ym σ S v))]
  have hp2 : (1 : ℝ) ≤ (p : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast hp1n)
  have hdx : ∀ σ, 2 ≤ (d : ℝ) * xp σ := fun σ => by
    simp only [hxp]
    rw [show (d : ℝ) * (26 * (p : ℝ) ^ 2 / d * Z σ) = 26 * (p : ℝ) ^ 2 * Z σ by field_simp]
    nlinarith [mul_le_mul hp2 (hZ1 σ) zero_le_one (by positivity)]
  have hcard : (Fintype.card (nbhd G S v) : ℝ) ≤ d := by exact_mod_cast card_nbhd_le G hC.deg S v
  -- the retained terms, one multi-index at a time
  have hLj : ∀ j ∈ (retIdx k : Finset (nbhd G S v → ℕ)).erase 0,
      |ecoefM j * lawE G p (aOf d p) yp ym S (fun σ =>
          dEven (nbL G S v) j (trcObs p mp mm (w σ) (rootMat G (aOf d p) 1 yp σ S v)
              (rootMat G (aOf d p) (-1) ym σ S v)) (rootSigns G σ S v) /
            starPhi p (rootMat G (aOf d p) 1 yp σ S v) (rootMat G (aOf d p) (-1) ym σ S v)
              (rootSigns G σ S v))| ≤
        lawE G p (aOf d p) yp ym S (fun σ => X σ * ∏ i, xp σ ^ j i) := by
    intro j _
    have hc : |ecoefM j| ≤ 1 := by
      rw [ecoefM, Finset.abs_prod]
      exact Finset.prod_le_one₀ (fun i _ => abs_nonneg _) fun i _ => abs_ecoef_le_one _
    rw [abs_mul]
    refine (mul_le_of_le_one_left (abs_nonneg _) hc).trans (abs_lawE_le G fun σ hσ => ?_)
    have hwc := wtCore_ne_zero_of_wt G hp1n hyp0 hym0 hv hσ
    refine (retained_pointwise G hR hC hyp hym hv hσ (hwb σ hwc).1 (by omega) (by omega) j).trans ?_
    refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀
      (fun i _ => pow_nonneg (by positivity) _) fun i _ => pow_le_pow_left₀ (by positivity)
        (lam_sq_le G hR hC hyp hym hσ i) _) (hX0 σ hσ)
  -- the grade expansion of the sum
  have hgr : ∀ σ, wt G p (aOf d p) yp ym σ S ≠ 0 →
      X σ * ∑ j ∈ (retIdx k : Finset (nbhd G S v → ℕ)).erase 0, ∏ i, xp σ ^ j i ≤
        ∑ g ∈ Finset.range k, Real.exp 2 * (676 * (p : ℝ) ^ 4 / d) ^ (g + 1) *
          (X σ * Z σ ^ (2 * (g + 1))) := fun σ hσ => by
    refine (mul_le_mul_of_nonneg_left (sum_ret_prod_le k hd1 hcard (hdx σ)) (hX0 σ hσ)).trans_eq ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    have e : (d : ℝ) * xp σ ^ 2 = 676 * (p : ℝ) ^ 4 / d * Z σ ^ 2 := by
      simp only [hxp]
      field_simp
      ring
    rw [e, mul_pow, ← pow_mul]
    ring
  -- per-grade truncation
  have htr : ∀ g ∈ Finset.range k, lawE G p (aOf d p) yp ym S (fun σ => X σ * Z σ ^ (2 * (g + 1))) ≤
      1024 ^ (2 * (g + 1)) * (lawE G p (aOf d p) yp ym S X + vth d) := by
    intro g hg
    have hgk : g + 1 ≤ k := Finset.mem_range.1 hg
    refine trunc_moment G hX0 (fun σ _ => (zero_le_one).trans (hZ1 σ)) (n := g + 1)
      (m := 2 * kIL d) (by norm_num) hθ.le ?_
    have hXs := X_sq_le G hR hC hyp hym hv hwb hmp hmm
    have hZm := Z_moment_le G hR hC hyp hym hv (n := 2 * (2 * (g + 1) + 2 * kIL d)) (by omega)
    have hXs0 : 0 ≤ lawE G p (aOf d p) yp ym S (fun σ => X σ ^ 2) :=
      lawE_nonneg G fun σ _ => sq_nonneg _
    have h2 := two_pow_kIL hd5
    calc lawE G p (aOf d p) yp ym S (fun σ => X σ ^ 2) *
          lawE G p (aOf d p) yp ym S (fun σ => Z σ ^ (2 * (2 * (g + 1) + 2 * kIL d)))
        ≤ ((d : ℝ) ^ 30) ^ 2 * (5 * d * 512 ^ (2 * (2 * (g + 1) + 2 * kIL d))) :=
          mul_le_mul hXs hZm (lawE_nonneg G fun σ hσ => pow_nonneg ((zero_le_one).trans (hZ1 σ)) _)
            (by positivity)
      _ ≤ (1024 ^ (2 * kIL d) * 1024 ^ (2 * (g + 1)) * vth d) ^ 2 := by
          set A := 2 * (g + 1) + 2 * kIL d with hA
          have hLA : (1024 : ℝ) ^ (2 * kIL d) * 1024 ^ (2 * (g + 1)) = 1024 ^ A := by
            rw [← pow_add, add_comm]
          have h2A : (2 : ℝ) ^ (4 * kIL d) ≤ 2 ^ (2 * A) :=
            pow_le_pow_right₀ (by norm_num) (by omega)
          have h5 := h2.trans h2A
          have h1024 : (512 : ℝ) ^ (2 * A) * 2 ^ (2 * A) = 1024 ^ (2 * A) := by
            rw [← mul_pow]; norm_num
          have hP : 0 ≤ (512 : ℝ) ^ (2 * A) := by positivity
          have hRHS : (1024 ^ (2 * kIL d) * 1024 ^ (2 * (g + 1)) * vth d) ^ 2 =
              512 ^ (2 * A) * 2 ^ (2 * A) / (d : ℝ) ^ 20 := by
            rw [hLA, h1024]
            unfold vth
            field_simp
            ring
          rw [hRHS, le_div_iff₀ (pow_pos hd0 20)]
          calc ((d : ℝ) ^ 30) ^ 2 * (5 * d * 512 ^ (2 * A)) * (d : ℝ) ^ 20
              = 512 ^ (2 * A) * (5 * (d : ℝ) ^ 81) := by ring
            _ ≤ 512 ^ (2 * A) * 2 ^ (2 * A) := mul_le_mul_of_nonneg_left h5 hP
  -- the geometric sum
  have hq : 676 * 1024 ^ 2 * (p : ℝ) ^ 4 / d ≤ 1 / 2 := by
    have h8 := TRegime.p8_le hR
    have hp4 : (10 : ℝ) ^ 24 ≤ (p : ℝ) ^ 4 := by
      have : (10 : ℝ) ^ 6 ≤ p := by exact_mod_cast hp6
      calc (10 : ℝ) ^ 24 = ((10 : ℝ) ^ 6) ^ 4 := by norm_num
        _ ≤ (p : ℝ) ^ 4 := pow_le_pow_left₀ (by norm_num) this 4
    rw [div_le_iff₀ hd0]
    nlinarith [mul_le_mul_of_nonneg_right hp4 (by positivity : (0 : ℝ) ≤ (p : ℝ) ^ 4)]
  have hq0 : 0 ≤ 676 * 1024 ^ 2 * (p : ℝ) ^ 4 / d := by positivity
  have hgeom : ∑ g ∈ Finset.range k, (676 * 1024 ^ 2 * (p : ℝ) ^ 4 / d) ^ (g + 1) ≤
      2 * (676 * 1024 ^ 2 * (p : ℝ) ^ 4 / d) := by
    calc ∑ g ∈ Finset.range k, (676 * 1024 ^ 2 * (p : ℝ) ^ 4 / d) ^ (g + 1)
        = (676 * 1024 ^ 2 * (p : ℝ) ^ 4 / d) *
            ∑ g ∈ Finset.range k, (676 * 1024 ^ 2 * (p : ℝ) ^ 4 / d) ^ g := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun g _ => by ring
      _ ≤ (676 * 1024 ^ 2 * (p : ℝ) ^ 4 / d) * ∑ g ∈ Finset.range k, (1 / 2 : ℝ) ^ g := by
          gcongr
      _ ≤ (676 * 1024 ^ 2 * (p : ℝ) ^ 4 / d) * 2 :=
          mul_le_mul_of_nonneg_left (sum_geometric_two_le k) hq0
      _ = _ := by ring
  -- assemble
  calc _ ≤ ∑ j ∈ (retIdx k : Finset (nbhd G S v → ℕ)).erase 0,
        |ecoefM j * lawE G p (aOf d p) yp ym S (fun σ =>
          dEven (nbL G S v) j (trcObs p mp mm (w σ) (rootMat G (aOf d p) 1 yp σ S v)
              (rootMat G (aOf d p) (-1) ym σ S v)) (rootSigns G σ S v) /
            starPhi p (rootMat G (aOf d p) 1 yp σ S v) (rootMat G (aOf d p) (-1) ym σ S v)
              (rootSigns G σ S v))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ (retIdx k : Finset (nbhd G S v → ℕ)).erase 0,
          lawE G p (aOf d p) yp ym S (fun σ => X σ * ∏ i, xp σ ^ j i) := Finset.sum_le_sum hLj
    _ = lawE G p (aOf d p) yp ym S (fun σ =>
          X σ * ∑ j ∈ (retIdx k : Finset (nbhd G S v → ℕ)).erase 0, ∏ i, xp σ ^ j i) := by
        rw [← lawE_sum]
        exact congrArg _ (funext fun σ => (Finset.mul_sum _ _ _).symm)
    _ ≤ lawE G p (aOf d p) yp ym S (fun σ => ∑ g ∈ Finset.range k, Real.exp 2 *
          (676 * (p : ℝ) ^ 4 / d) ^ (g + 1) * (X σ * Z σ ^ (2 * (g + 1)))) := lawE_mono G hgr
    _ = ∑ g ∈ Finset.range k, Real.exp 2 * (676 * (p : ℝ) ^ 4 / d) ^ (g + 1) *
          lawE G p (aOf d p) yp ym S (fun σ => X σ * Z σ ^ (2 * (g + 1))) := by
        rw [lawE_sum]
        exact Finset.sum_congr rfl fun g _ => lawE_const_mul G _ _
    _ ≤ ∑ g ∈ Finset.range k, Real.exp 2 * (676 * (p : ℝ) ^ 4 / d) ^ (g + 1) *
          (1024 ^ (2 * (g + 1)) * (lawE G p (aOf d p) yp ym S X + vth d)) := by
        refine Finset.sum_le_sum fun g hg => mul_le_mul_of_nonneg_left (htr g hg) ?_
        positivity
    _ = Real.exp 2 * (lawE G p (aOf d p) yp ym S X + vth d) *
          ∑ g ∈ Finset.range k, (676 * 1024 ^ 2 * (p : ℝ) ^ 4 / d) ^ (g + 1) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [show (676 * 1024 ^ 2 * (p : ℝ) ^ 4 / d) ^ (g + 1) =
          (676 * (p : ℝ) ^ 4 / d) ^ (g + 1) * 1024 ^ (2 * (g + 1)) by
            rw [pow_mul, ← mul_pow]; ring_nf]
        ring
    _ ≤ Real.exp 2 * (lawE G p (aOf d p) yp ym S X + vth d) *
          (2 * (676 * 1024 ^ 2 * (p : ℝ) ^ 4 / d)) :=
        mul_le_mul_of_nonneg_left hgeom (mul_nonneg (Real.exp_pos 2).le hxθ)
    _ = _ := by ring

end SecC

end BiluLinial.Tight
