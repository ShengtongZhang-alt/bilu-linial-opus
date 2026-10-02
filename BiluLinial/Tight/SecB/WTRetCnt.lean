/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecB.WTRetCalc
public import BiluLinial.Tight.SecA.Transfer
public import BiluLinial.Tight.Compare.Symm

/-!
# Grade sums for the retained WT terms (helpers for TB.WT5l)

* `sum_map_dEvenList_univ`, `qd2_le_double`: the first- and second-derivative sums of
  `quad_leibniz` along `dEvenList j` in terms of the multi-index `j`.
* `sum_topIdx_weight_le` (weighted A-CNT): for `x T ≤ 1/8` and exponents `e_i ≤ 2`,
  `Σ_{|j|_g = g+1} Π_i j_i^{e_i} x^{j_i} ≤ T^{-(g+1)} Π_i B_i` with `B_i = 1 + 2x²T` (`e_i = 0`)
  and `B_i = 2^{e_i+1} x²T` (`e_i > 0`): a coordinate carrying a weight `j_s` is forced to have
  `j_s ≥ 2`, which costs `x²T` instead of `1`.
* `sum_ret_weight_le`: with `L = TᵀT`, `x = κ²`, `d κ² ≥ 8`, `|ι| ≤ d`,
  `Σ_{1 ≤ |j|_g ≤ k} κ^{2Σj} (q_L + qd1_j/κ + qd2_j/κ² + tr L) ≤ 26 e² Σ_{g<k} (dκ⁴)^{g+1}
  (q_L + tr L)`.
-/

@[expose] public section

namespace BiluLinial.Tight.SecB

open Matrix Finset

section Count

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem sum_map_dEvenList (l : List ι) (j : ι → ℕ) (f : ι → ℝ) :
    ((dEvenList l j).map f).sum = (l.map fun s => (2 * j s : ℝ) * f s).sum := by
  induction l with
  | nil => simp [dEvenList]
  | cons y l ih =>
    simp only [dEvenList, List.flatMap_cons, List.map_append, List.sum_append,
      List.map_replicate, List.sum_replicate, List.map_cons, List.sum_cons, nsmul_eq_mul] at ih ⊢
    rw [ih]
    push_cast
    ring

omit [DecidableEq ι] in
theorem sum_map_dEvenList_univ (j : ι → ℕ) (f : ι → ℝ) :
    ((dEvenList (Finset.univ : Finset ι).toList j).map f).sum = ∑ s, (2 * j s : ℝ) * f s := by
  rw [sum_map_dEvenList]
  exact Finset.sum_map_toList _ (fun s => (2 * j s : ℝ) * f s)

omit [Fintype ι] [DecidableEq ι] in
/-- `qd2` is at most the full double sum over pairs of positions. -/
theorem qd2_le_double (Q : Matrix ι ι ℝ) : ∀ l : List ι,
    qd2 Q l ≤ (l.map fun s => (l.map fun t => |(Q + Qᵀ) t s|).sum).sum
  | [] => by simp [qd2]
  | i :: l => by
    have ih := qd2_le_double Q l
    rw [qd2]
    simp only [List.map_cons, List.sum_cons]
    have h1 : 0 ≤ |(Q + Qᵀ) i i| := abs_nonneg _
    have h2 : (l.map fun s => (l.map fun t => |(Q + Qᵀ) t s|).sum).sum ≤
        (l.map fun s => |(Q + Qᵀ) i s| + (l.map fun t => |(Q + Qᵀ) t s|).sum).sum :=
      List.sum_le_sum fun s _ => le_add_of_nonneg_left (abs_nonneg _)
    linarith

omit [DecidableEq ι] in
theorem qd2_dEvenList_le (Q : Matrix ι ι ℝ) (j : ι → ℕ) :
    qd2 Q (dEvenList (Finset.univ : Finset ι).toList j) ≤
      ∑ s, ∑ t, (2 * j s : ℝ) * (2 * j t) * |(Q + Qᵀ) t s| := by
  refine (qd2_le_double Q _).trans_eq ?_
  rw [sum_map_dEvenList_univ]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [sum_map_dEvenList_univ, Finset.mul_sum]
  exact Finset.sum_congr rfl fun t _ => by ring

omit [DecidableEq ι] in
theorem qd1_dEvenList (ℓ : ι → ℝ) (Q : Matrix ι ι ℝ) (x₀ : ι → ℝ) (j : ι → ℕ) :
    qd1 ℓ Q x₀ (dEvenList (Finset.univ : Finset ι).toList j) =
      ∑ s, (2 * j s : ℝ) * |ℓ s + ((Q + Qᵀ) *ᵥ x₀) s| := by
  unfold qd1
  rw [sum_map_dEvenList_univ]

/-- **Weighted A-CNT.** -/
theorem sum_topIdx_weight_le (g : ℕ) {x T : ℝ} (hx : 0 < x) (hT : 0 < T)
    (hxT : x * T ≤ 1 / 8) (e : ι → ℕ) (he : ∀ i, e i ≤ 2) :
    ∑ j ∈ (topIdx g : Finset (ι → ℕ)), ∏ i, ((j i : ℝ) ^ e i * x ^ j i) ≤
      (1 / T) ^ (g + 1) * ∏ i, (if e i = 0 then 1 + 2 * (x ^ 2 * T) else
        2 ^ (e i + 1) * (x ^ 2 * T)) := by
  let w : ι → ℕ → ℝ := fun i a => if a = 1 then 0 else (a : ℝ) ^ e i * x ^ a * T ^ (a - 1)
  have hw0 : ∀ i a, 0 ≤ w i a := fun i a => by
    simp only [w]; split_ifs
    · exact le_rfl
    · positivity
  have key : ∀ j ∈ (topIdx g : Finset (ι → ℕ)),
      ∏ i, ((j i : ℝ) ^ e i * x ^ j i) = (1 / T) ^ (g + 1) * ∏ i, w i (j i) := by
    intro j hj
    obtain ⟨h1, hg⟩ := mem_topIdx.1 hj
    have e' : ∏ i, w i (j i) = (∏ i, ((j i : ℝ) ^ e i * x ^ j i)) * T ^ (g + 1) := by
      rw [← hg, grade, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      simp only [w, if_neg (h1 i)]
    rw [e', mul_comm (∏ i, ((j i : ℝ) ^ e i * x ^ j i)), ← mul_assoc, ← mul_pow,
      one_div_mul_cancel hT.ne', one_pow, one_mul]
  have hcoord : ∀ i, ∑ a ∈ Finset.range (g + 3), w i a ≤
      (if e i = 0 then 1 + 2 * (x ^ 2 * T) else 2 ^ (e i + 1) * (x ^ 2 * T)) := by
    intro i
    rw [Finset.sum_range_succ', Finset.sum_range_succ']
    have h0 : w i (0 + 1) = 0 := by simp [w]
    have h00 : w i 0 = if e i = 0 then 1 else 0 := by
      by_cases hei : e i = 0
      · simp [w, hei]
      · simp [w, hei, zero_pow hei]
    have hr : (2 : ℝ) ^ e i * (x * T) ≤ 1 / 2 := by
      have h4 : (2 : ℝ) ^ e i ≤ 4 := by
        calc (2 : ℝ) ^ e i ≤ 2 ^ 2 := pow_le_pow_right₀ (by norm_num) (he i)
          _ = 4 := by norm_num
      have hxT0 : 0 ≤ x * T := by positivity
      nlinarith
    have hs : ∑ a ∈ Finset.range (g + 1), w i (a + 1 + 1) ≤ 2 ^ (e i + 1) * (x ^ 2 * T) := by
      have hterm : ∀ a, w i (a + 1 + 1) ≤ 2 ^ e i * (x ^ 2 * T) * ((1 : ℝ) / 2) ^ a := by
        intro a
        simp only [w, show a + 1 + 1 ≠ 1 by omega, if_false,
          show a + 1 + 1 - 1 = a + 1 by omega]
        have hA : ((a + 1 + 1 : ℕ) : ℝ) ≤ 2 ^ (a + 1) := by
          have h' : a + 1 + 1 ≤ 2 ^ (a + 1) := (a + 1).lt_two_pow_self
          exact_mod_cast h'
        have hA' : ((a + 1 + 1 : ℕ) : ℝ) ^ e i ≤ 2 ^ e i * ((2 : ℝ) ^ e i) ^ a := by
          calc ((a + 1 + 1 : ℕ) : ℝ) ^ e i ≤ ((2 : ℝ) ^ (a + 1)) ^ e i :=
                pow_le_pow_left₀ (by positivity) hA _
            _ = 2 ^ e i * ((2 : ℝ) ^ e i) ^ a := by
                rw [← pow_mul, ← pow_mul, ← pow_add]
                congr 1
                ring
        have hr' : ((2 : ℝ) ^ e i * (x * T)) ^ a ≤ (1 / 2) ^ a :=
          pow_le_pow_left₀ (by positivity) hr a
        have hxa : 0 ≤ x ^ (a + 1 + 1) * T ^ (a + 1) := by positivity
        calc ((a + 1 + 1 : ℕ) : ℝ) ^ e i * x ^ (a + 1 + 1) * T ^ (a + 1)
            = ((a + 1 + 1 : ℕ) : ℝ) ^ e i * (x ^ (a + 1 + 1) * T ^ (a + 1)) := by ring
          _ ≤ (2 ^ e i * ((2 : ℝ) ^ e i) ^ a) * (x ^ (a + 1 + 1) * T ^ (a + 1)) :=
              mul_le_mul_of_nonneg_right hA' hxa
          _ = 2 ^ e i * (x ^ 2 * T) * ((2 : ℝ) ^ e i * (x * T)) ^ a := by ring
          _ ≤ 2 ^ e i * (x ^ 2 * T) * ((1 : ℝ) / 2) ^ a :=
              mul_le_mul_of_nonneg_left hr' (by positivity)
      calc ∑ a ∈ Finset.range (g + 1), w i (a + 1 + 1)
          ≤ ∑ a ∈ Finset.range (g + 1), 2 ^ e i * (x ^ 2 * T) * ((1 : ℝ) / 2) ^ a :=
            Finset.sum_le_sum fun a _ => hterm a
        _ = 2 ^ e i * (x ^ 2 * T) * ∑ a ∈ Finset.range (g + 1), ((1 : ℝ) / 2) ^ a := by
            rw [Finset.mul_sum]
        _ ≤ 2 ^ e i * (x ^ 2 * T) * 2 :=
            mul_le_mul_of_nonneg_left (sum_geometric_two_le _) (by positivity)
        _ = 2 ^ (e i + 1) * (x ^ 2 * T) := by ring
    rw [h0, h00]
    split_ifs with hei
    · rw [hei] at hs
      norm_num at hs ⊢
      linarith
    · linarith
  calc ∑ j ∈ (topIdx g : Finset (ι → ℕ)), ∏ i, ((j i : ℝ) ^ e i * x ^ j i)
      = ∑ j ∈ (topIdx g : Finset (ι → ℕ)), (1 / T) ^ (g + 1) * ∏ i, w i (j i) :=
        Finset.sum_congr rfl key
    _ = (1 / T) ^ (g + 1) * ∑ j ∈ (topIdx g : Finset (ι → ℕ)), ∏ i, w i (j i) := by
        rw [Finset.mul_sum]
    _ ≤ (1 / T) ^ (g + 1) * ∑ j ∈ Fintype.piFinset (fun _ : ι => Finset.range (g + 3)),
          ∏ i, w i (j i) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.filter_subset _ _) fun j _ _ => Finset.prod_nonneg fun i _ => hw0 _ _)
          (by positivity)
    _ = (1 / T) ^ (g + 1) * ∏ i, ∑ a ∈ Finset.range (g + 3), w i a := by
        rw [Finset.prod_univ_sum]
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀
          (fun i _ => Finset.sum_nonneg fun a _ => hw0 i a) fun i _ => hcoord i) (by positivity)

omit [DecidableEq ι] in
/-- The coordinate factors: `Π_i B_i ≤ e² Π_{e_i > 0} 2^{e_i+1} y` when `y |ι| ≤ 1`. -/
theorem prod_weight_le_exp {y d : ℝ} (hy : 0 ≤ y) (hd : (Fintype.card ι : ℝ) ≤ d)
    (hyd : y * d ≤ 1) (e : ι → ℕ) :
    ∏ i, (if e i = 0 then 1 + 2 * y else 2 ^ (e i + 1) * y) ≤
      Real.exp 2 * ∏ i, (if e i = 0 then 1 else 2 ^ (e i + 1) * y) := by
  have h1 : ∀ i, (if e i = 0 then 1 + 2 * y else 2 ^ (e i + 1) * y) ≤
      (if e i = 0 then 1 else 2 ^ (e i + 1) * y) * (1 + 2 * y) := by
    intro i
    split_ifs
    · linarith
    · have : 0 ≤ 2 ^ (e i + 1) * y := by positivity
      nlinarith
  have hnn : ∀ i, 0 ≤ (if e i = 0 then (1 : ℝ) else 2 ^ (e i + 1) * y) := fun i => by
    split_ifs <;> positivity
  calc _ ≤ ∏ i, ((if e i = 0 then 1 else 2 ^ (e i + 1) * y) * (1 + 2 * y)) :=
        Finset.prod_le_prod₀ (fun i _ => by split_ifs <;> positivity) fun i _ => h1 i
    _ = (∏ i, (if e i = 0 then 1 else 2 ^ (e i + 1) * y)) * (1 + 2 * y) ^ Fintype.card ι := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
    _ ≤ (∏ i, (if e i = 0 then 1 else 2 ^ (e i + 1) * y)) * Real.exp 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (Finset.prod_nonneg fun i _ => hnn i)
        refine (SecA.one_add_pow_le_exp (by positivity) hd).trans ?_
        exact Real.exp_le_exp.2 (by nlinarith)
    _ = _ := by ring

omit [DecidableEq ι] in
theorem prod_ite_zero (y : ℝ) :
    ∏ i, (if (0 : ι → ℕ) i = 0 then (1 : ℝ) else 2 ^ ((0 : ι → ℕ) i + 1) * y) = 1 := by
  simp

theorem prod_ite_single (s : ι) {n : ℕ} (hn : n ≠ 0) (y : ℝ) :
    ∏ i, (if (Pi.single s n : ι → ℕ) i = 0 then (1 : ℝ) else
      2 ^ ((Pi.single s n : ι → ℕ) i + 1) * y) = 2 ^ (n + 1) * y := by
  rw [Finset.prod_eq_single s]
  · simp [hn]
  · intro i _ hi
    simp [Pi.single_apply, hi]
  · simp

theorem prod_ite_pair {s t : ι} (hst : s ≠ t) (y : ℝ) :
    ∏ i, (if (Pi.single s 1 + Pi.single t 1 : ι → ℕ) i = 0 then (1 : ℝ) else
      2 ^ ((Pi.single s 1 + Pi.single t 1 : ι → ℕ) i + 1) * y) = (4 * y) * (4 * y) := by
  have e : ∀ i, (if (Pi.single s 1 + Pi.single t 1 : ι → ℕ) i = 0 then (1 : ℝ) else
      2 ^ ((Pi.single s 1 + Pi.single t 1 : ι → ℕ) i + 1) * y) =
      (if i = s then 4 * y else 1) * (if i = t then 4 * y else 1) := by
    intro i
    by_cases his : i = s
    · subst his
      simp [Pi.single_apply, hst]
      norm_num
    · by_cases hit : i = t
      · subst hit
        simp [Pi.single_apply, his]
        norm_num
      · simp [Pi.single_apply, his, hit]
  rw [Finset.prod_congr rfl fun i _ => e i, Finset.prod_mul_distrib, Finset.prod_ite_eq',
    Finset.prod_ite_eq']
  simp

theorem prod_pow_single (j : ι → ℕ) (s : ι) (n : ℕ) :
    ∏ i, (j i : ℝ) ^ (Pi.single s n : ι → ℕ) i = (j s : ℝ) ^ n := by
  rw [Finset.prod_eq_single s]
  · simp
  · intro i _ hi
    simp [Pi.single_apply, hi]
  · simp

theorem prod_pow_pair (j : ι → ℕ) {s t : ι} (hst : s ≠ t) :
    ∏ i, (j i : ℝ) ^ (Pi.single s 1 + Pi.single t 1 : ι → ℕ) i = (j s : ℝ) * j t := by
  have e : ∀ i, (j i : ℝ) ^ (Pi.single s 1 + Pi.single t 1 : ι → ℕ) i =
      (if i = s then (j s : ℝ) else 1) * (if i = t then (j t : ℝ) else 1) := by
    intro i
    by_cases his : i = s
    · subst his
      simp [Pi.single_apply, hst]
    · by_cases hit : i = t
      · subst hit
        simp [Pi.single_apply, his]
      · simp [Pi.single_apply, his, hit]
  rw [Finset.prod_congr rfl fun i _ => e i, Finset.prod_mul_distrib, Finset.prod_ite_eq',
    Finset.prod_ite_eq']
  simp

/-- Weighted A-CNT with the coordinate factors summed up. -/
theorem sum_topIdx_weight_exp (g : ℕ) {x T d : ℝ} (hx : 0 < x) (hT : 0 < T)
    (hxT : x * T ≤ 1 / 8) (hd : (Fintype.card ι : ℝ) ≤ d) (hyd : x ^ 2 * T * d ≤ 1)
    (e : ι → ℕ) (he : ∀ i, e i ≤ 2) :
    ∑ j ∈ (topIdx g : Finset (ι → ℕ)), (∏ i, (j i : ℝ) ^ e i) * ∏ i, x ^ j i ≤
      (1 / T) ^ (g + 1) * (Real.exp 2 *
        ∏ i, (if e i = 0 then 1 else 2 ^ (e i + 1) * (x ^ 2 * T))) := by
  have h := sum_topIdx_weight_le g hx hT hxT e he
  simp only [Finset.prod_mul_distrib] at h
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  exact prod_weight_le_exp (by positivity) hd hyd e

/-! ### The kernel `L = TᵀT` -/

omit [DecidableEq ι] in
theorem kerT_apply (Tm : Matrix ι ι ℝ) (s t : ι) : (Tmᵀ * Tm) s t = ∑ a, Tm a s * Tm a t := by
  simp [Matrix.mul_apply, Matrix.transpose_apply]

omit [DecidableEq ι] in
theorem kerT_transpose (Tm : Matrix ι ι ℝ) : (Tmᵀ * Tm)ᵀ = Tmᵀ * Tm := by
  rw [Matrix.transpose_mul, Matrix.transpose_transpose]

omit [DecidableEq ι] in
theorem kerT_mulVec (Tm : Matrix ι ι ℝ) (ξ : ι → ℝ) (s : ι) :
    ((Tmᵀ * Tm) *ᵥ ξ) s = ∑ a, Tm a s * (Tm *ᵥ ξ) a := by
  rw [← Matrix.mulVec_mulVec]
  simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply]

omit [DecidableEq ι] in
theorem kerT_qForm (Tm : Matrix ι ι ℝ) (ξ : ι → ℝ) :
    qForm (Tmᵀ * Tm) ξ = ∑ a, (Tm *ᵥ ξ) a ^ 2 := by
  unfold qForm
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  simp [dotProduct, sq]

omit [DecidableEq ι] in
theorem kerT_trace (Tm : Matrix ι ι ℝ) : (Tmᵀ * Tm).trace = ∑ s, ∑ a, Tm a s ^ 2 := by
  simp only [Matrix.trace, Matrix.diag, kerT_apply, sq]

omit [DecidableEq ι] in
/-- `Σ_s |((L + Lᵀ)ξ)_s| ≤ tr L/κ + κ |ι| q_L`. -/
theorem sum_abs_kerT_mulVec_le (Tm : Matrix ι ι ℝ) (ξ : ι → ℝ) {κ : ℝ} (hκ : 0 < κ) :
    ∑ s, |((Tmᵀ * Tm + (Tmᵀ * Tm)ᵀ) *ᵥ ξ) s| ≤
      (Tmᵀ * Tm).trace / κ + κ * Fintype.card ι * qForm (Tmᵀ * Tm) ξ := by
  have hpt : ∀ s, |((Tmᵀ * Tm + (Tmᵀ * Tm)ᵀ) *ᵥ ξ) s| ≤
      ∑ a, (Tm a s ^ 2 / κ + κ * (Tm *ᵥ ξ) a ^ 2) := by
    intro s
    have e2 : (∑ a, Tm a s * (Tm *ᵥ ξ) a) + ∑ a, Tm a s * (Tm *ᵥ ξ) a =
        ∑ a, 2 * (Tm a s * (Tm *ᵥ ξ) a) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun a _ => by ring
    rw [kerT_transpose, Matrix.add_mulVec, Pi.add_apply, kerT_mulVec, e2]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    rw [abs_mul, abs_mul, abs_two]
    have h1 : 0 ≤ (|Tm a s| - κ * |(Tm *ᵥ ξ) a|) ^ 2 := sq_nonneg _
    have e1 : Tm a s ^ 2 / κ + κ * (Tm *ᵥ ξ) a ^ 2 - 2 * (|Tm a s| * |(Tm *ᵥ ξ) a|) =
        (|Tm a s| - κ * |(Tm *ᵥ ξ) a|) ^ 2 / κ := by
      rw [← sq_abs (Tm a s), ← sq_abs ((Tm *ᵥ ξ) a)]
      field_simp
      ring
    have h2 : 0 ≤ (|Tm a s| - κ * |(Tm *ᵥ ξ) a|) ^ 2 / κ := div_nonneg h1 hκ.le
    linarith
  calc ∑ s, |((Tmᵀ * Tm + (Tmᵀ * Tm)ᵀ) *ᵥ ξ) s|
      ≤ ∑ s, ∑ a, (Tm a s ^ 2 / κ + κ * (Tm *ᵥ ξ) a ^ 2) := Finset.sum_le_sum fun s _ => hpt s
    _ = _ := by
        rw [kerT_trace, kerT_qForm]
        simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          ← Finset.mul_sum, ← Finset.sum_div]
        ring

omit [DecidableEq ι] in
/-- `Σ_{s,t} |L_st| ≤ |ι| tr L`. -/
theorem sum_abs_kerT_le (Tm : Matrix ι ι ℝ) :
    ∑ s, ∑ t, |(Tmᵀ * Tm) s t| ≤ Fintype.card ι * (Tmᵀ * Tm).trace := by
  have hpt : ∀ s t, |(Tmᵀ * Tm) s t| ≤ ∑ a, (Tm a s ^ 2 + Tm a t ^ 2) / 2 := by
    intro s t
    rw [kerT_apply]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    rw [abs_mul]
    nlinarith [sq_nonneg (|Tm a s| - |Tm a t|), sq_abs (Tm a s), sq_abs (Tm a t)]
  calc ∑ s, ∑ t, |(Tmᵀ * Tm) s t| ≤ ∑ s, ∑ t, ∑ a, (Tm a s ^ 2 + Tm a t ^ 2) / 2 :=
        Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun t _ => hpt s t
    _ = _ := by
        have e1 : ∀ s t, ∑ a, (Tm a s ^ 2 + Tm a t ^ 2) / 2 =
            (∑ a, Tm a s ^ 2) / 2 + (∑ a, Tm a t ^ 2) / 2 := by
          intro s t
          rw [← add_div, ← Finset.sum_add_distrib, Finset.sum_div]
        simp only [e1, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        rw [kerT_trace]
        simp only [← Finset.mul_sum, ← Finset.sum_div]
        ring

omit [DecidableEq ι] in
theorem kerT_symm (Tm : Matrix ι ι ℝ) (s t : ι) : (Tmᵀ * Tm) t s = (Tmᵀ * Tm) s t := by
  rw [kerT_apply, kerT_apply]
  exact Finset.sum_congr rfl fun a _ => by ring

omit [DecidableEq ι] in
theorem kerT_diag_nonneg (Tm : Matrix ι ι ℝ) (s : ι) : 0 ≤ (Tmᵀ * Tm) s s := by
  rw [kerT_apply]
  exact Finset.sum_nonneg fun a _ => mul_self_nonneg _

/-- **Grade sums at one signing.** With `L = TᵀT`, `κ > 0`, `d κ² ≥ 8`, `|ι| ≤ d`:
`Σ_{1 ≤ |j|_g ≤ k} κ^{2Σj} (q_L + qd1_j/κ + qd2_j/κ² + tr L) ≤
26 e² Σ_{g<k} (dκ⁴)^{g+1} (q_L + tr L)`. -/
theorem sum_ret_weight_le (k : ℕ) {d κ : ℝ} (hd : 1 ≤ d) (hcard : (Fintype.card ι : ℝ) ≤ d)
    (hκ : 0 < κ) (hdκ : 8 ≤ d * κ ^ 2) (Tm : Matrix ι ι ℝ) (ξ : ι → ℝ) :
    ∑ j ∈ (retIdx k : Finset (ι → ℕ)).erase 0, κ ^ (2 * ∑ i, j i) *
        (qForm (Tmᵀ * Tm) ξ +
          qd1 0 (Tmᵀ * Tm) ξ (dEvenList (Finset.univ : Finset ι).toList j) / κ +
          qd2 (Tmᵀ * Tm) (dEvenList (Finset.univ : Finset ι).toList j) / κ ^ 2 +
          (Tmᵀ * Tm).trace) ≤
      26 * Real.exp 2 * ∑ g ∈ Finset.range k, (d * κ ^ 4) ^ (g + 1) *
        (qForm (Tmᵀ * Tm) ξ + (Tmᵀ * Tm).trace) := by
  set L := Tmᵀ * Tm with hL
  set q := qForm L ξ with hq
  set tr := L.trace with htr
  set x := κ ^ 2 with hx
  have hx0 : 0 < x := by positivity
  have hd0 : 0 < d := by linarith
  set T := 1 / (d * x ^ 2) with hT
  have hT0 : 0 < T := by positivity
  have hxT : x * T ≤ 1 / 8 := by
    rw [hT, show x * (1 / (d * x ^ 2)) = 1 / (d * x) by field_simp]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  set y := x ^ 2 * T with hy
  have hy' : y = 1 / d := by rw [hy, hT]; field_simp
  have hyd : y * d ≤ 1 := le_of_eq (by rw [hy']; field_simp)
  have hy0 : 0 ≤ y := by rw [hy']; positivity
  have hyc : y * Fintype.card ι ≤ 1 := by
    calc y * Fintype.card ι ≤ y * d := mul_le_mul_of_nonneg_left hcard hy0
      _ ≤ 1 := hyd
  set r := y / κ ^ 2 with hr
  have hr0 : 0 ≤ r := by positivity
  have hr8 : 8 * r ≤ 1 := by
    rw [hr, hy', show 8 * (1 / d / κ ^ 2) = 8 / (d * κ ^ 2) by field_simp,
      div_le_one (by positivity)]
    exact hdκ
  have hq0 : 0 ≤ q := by rw [hq, hL, kerT_qForm]; positivity
  have htr0 : 0 ≤ tr := by rw [htr, hL, kerT_trace]; positivity
  have hTd : 1 / T = d * κ ^ 4 := by rw [hT, hx, one_div_one_div]; ring
  set a : ι → ℝ := fun s => |((L + Lᵀ) *ᵥ ξ) s| with ha
  set b : ι → ι → ℝ := fun t s => |(L + Lᵀ) t s| with hb
  have ha0 : ∀ s, 0 ≤ a s := fun s => abs_nonneg _
  have hb0 : ∀ t s, 0 ≤ b t s := fun t s => abs_nonneg _
  set P : (ι → ℕ) → ℝ := fun j => ∏ i, x ^ j i with hP
  have hP0 : ∀ j, 0 ≤ P j := fun j => Finset.prod_nonneg fun i _ => pow_nonneg hx0.le _
  -- step A: one multi-index
  have hA : ∀ j : ι → ℕ, κ ^ (2 * ∑ i, j i) * (q +
      qd1 0 L ξ (dEvenList (Finset.univ : Finset ι).toList j) / κ +
      qd2 L (dEvenList (Finset.univ : Finset ι).toList j) / κ ^ 2 + tr) ≤
      P j * (q + tr) + ∑ s, (2 * a s / κ) * ((j s : ℝ) * P j) +
        ∑ s, ∑ t, (4 * b t s / κ ^ 2) * ((j s : ℝ) * j t * P j) := by
    intro j
    have hk : κ ^ (2 * ∑ i, j i) = P j := by
      rw [pow_mul, ← hx]
      show x ^ (∑ i, j i) = ∏ i, x ^ j i
      rw [Finset.prod_pow_eq_pow_sum]
    have h1 : qd1 0 L ξ (dEvenList (Finset.univ : Finset ι).toList j) =
        ∑ s, (2 * j s : ℝ) * a s := by
      rw [qd1_dEvenList]
      exact Finset.sum_congr rfl fun s _ => by simp [ha]
    have h2 := qd2_dEvenList_le L j
    have h2' : qd2 L (dEvenList (Finset.univ : Finset ι).toList j) / κ ^ 2 ≤
        (∑ s, ∑ t, (2 * j s : ℝ) * (2 * j t) * b t s) / κ ^ 2 :=
      div_le_div_of_nonneg_right h2 (by positivity)
    rw [hk, h1]
    have e1 : P j * ((∑ s, (2 * j s : ℝ) * a s) / κ) =
        ∑ s, (2 * a s / κ) * ((j s : ℝ) * P j) := by
      rw [Finset.sum_div, Finset.mul_sum]
      exact Finset.sum_congr rfl fun s _ => by ring
    have e2 : P j * ((∑ s, ∑ t, (2 * j s : ℝ) * (2 * j t) * b t s) / κ ^ 2) =
        ∑ s, ∑ t, (4 * b t s / κ ^ 2) * ((j s : ℝ) * j t * P j) := by
      rw [Finset.sum_div, Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Finset.sum_div, Finset.mul_sum]
      exact Finset.sum_congr rfl fun t _ => by ring
    have h3 := mul_le_mul_of_nonneg_left h2' (hP0 j)
    rw [e2] at h3
    calc P j * (q + (∑ s, (2 * j s : ℝ) * a s) / κ +
          qd2 L (dEvenList (Finset.univ : Finset ι).toList j) / κ ^ 2 + tr)
        = P j * (q + tr) + P j * ((∑ s, (2 * j s : ℝ) * a s) / κ) +
          P j * (qd2 L (dEvenList (Finset.univ : Finset ι).toList j) / κ ^ 2) := by ring
      _ ≤ _ := by rw [e1]; linarith
  -- the counts
  have hC : ∀ g (e : ι → ℕ), (∀ i, e i ≤ 2) →
      ∑ j ∈ (topIdx g : Finset (ι → ℕ)), (∏ i, (j i : ℝ) ^ e i) * P j ≤
        (1 / T) ^ (g + 1) * (Real.exp 2 * ∏ i, (if e i = 0 then 1 else 2 ^ (e i + 1) * y)) :=
    fun g e he => sum_topIdx_weight_exp g hx0 hT0 hxT hcard (by rw [← hy]; exact hyd) e he
  have hsingle : ∀ (s : ι) (n : ℕ), n ≤ 2 → ∀ i, (Pi.single s n : ι → ℕ) i ≤ 2 := by
    intro s n hn i
    rw [Pi.single_apply]
    split_ifs <;> omega
  have hpair : ∀ s t : ι, ∀ i, (Pi.single s 1 + Pi.single t 1 : ι → ℕ) i ≤ 2 := by
    intro s t i
    simp only [Pi.add_apply, Pi.single_apply]
    split_ifs <;> omega
  have hC0 : ∀ g, ∑ j ∈ (topIdx g : Finset (ι → ℕ)), P j ≤ (1 / T) ^ (g + 1) * Real.exp 2 := by
    intro g
    have h := hC g 0 (fun i => by simp)
    simp only [Pi.zero_apply, pow_zero, Finset.prod_const_one, one_mul] at h
    simpa using h
  have hC1 : ∀ g s, ∑ j ∈ (topIdx g : Finset (ι → ℕ)), (j s : ℝ) * P j ≤
      (1 / T) ^ (g + 1) * Real.exp 2 * (4 * y) := by
    intro g s
    have h := hC g (Pi.single s 1) (hsingle s 1 (by norm_num))
    rw [prod_ite_single s one_ne_zero] at h
    simp only [prod_pow_single, pow_one] at h
    refine h.trans_eq ?_
    norm_num
    ring
  have hC2 : ∀ g s, ∑ j ∈ (topIdx g : Finset (ι → ℕ)), (j s : ℝ) * j s * P j ≤
      (1 / T) ^ (g + 1) * Real.exp 2 * (8 * y) := by
    intro g s
    have h := hC g (Pi.single s 2) (hsingle s 2 le_rfl)
    rw [prod_ite_single s two_ne_zero] at h
    simp only [prod_pow_single] at h
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun j _ => by ring)) (h.trans_eq ?_)
    norm_num
    ring
  have hC3 : ∀ g s t, s ≠ t → ∑ j ∈ (topIdx g : Finset (ι → ℕ)), (j s : ℝ) * j t * P j ≤
      (1 / T) ^ (g + 1) * Real.exp 2 * (16 * y ^ 2) := by
    intro g s t hst
    have h := hC g (Pi.single s 1 + Pi.single t 1) (hpair s t)
    rw [prod_ite_pair hst] at h
    simp only [prod_pow_pair _ hst] at h
    refine h.trans_eq ?_
    ring
  have hκ0 : κ ≠ 0 := hκ.ne'
  have hLs : ∀ s t, L t s = L s t := fun s t => kerT_symm Tm s t
  have hLd : ∀ s, 0 ≤ L s s := fun s => kerT_diag_nonneg Tm s
  have hLsum : ∑ s, ∑ t, |L s t| ≤ Fintype.card ι * tr := sum_abs_kerT_le Tm
  have hbs : ∀ s t, b t s ≤ 2 * |L s t| := by
    intro s t
    show |(L + Lᵀ) t s| ≤ 2 * |L s t|
    rw [Matrix.add_apply, Matrix.transpose_apply, hLs s t, ← two_mul, abs_mul, abs_two]
  have hbd : ∑ s, b s s ≤ 2 * tr := by
    calc ∑ s, b s s ≤ ∑ s, 2 * |L s s| := Finset.sum_le_sum fun s _ => hbs s s
      _ = 2 * tr := by
          rw [← Finset.mul_sum, htr, Matrix.trace]
          congr 1
          exact Finset.sum_congr rfl fun s _ => abs_of_nonneg (hLd s)
  have hbo : ∑ s, ∑ t ∈ Finset.univ.erase s, b t s ≤ 2 * (Fintype.card ι * tr) := by
    calc ∑ s, ∑ t ∈ Finset.univ.erase s, b t s ≤ ∑ s, ∑ t, b t s :=
          Finset.sum_le_sum fun s _ => Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.erase_subset _ _) fun t _ _ => hb0 t s
      _ ≤ ∑ s, ∑ t, 2 * |L s t| :=
          Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun t _ => hbs s t
      _ = 2 * ∑ s, ∑ t, |L s t| := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun s _ => (Finset.mul_sum _ _ _).symm
      _ ≤ 2 * (Fintype.card ι * tr) := mul_le_mul_of_nonneg_left hLsum (by norm_num)
  have hsa := sum_abs_kerT_mulVec_le Tm ξ hκ
  -- one grade
  have hgrade : ∀ g, ∑ j ∈ (topIdx g : Finset (ι → ℕ)), κ ^ (2 * ∑ i, j i) * (q +
      qd1 0 L ξ (dEvenList (Finset.univ : Finset ι).toList j) / κ +
      qd2 L (dEvenList (Finset.univ : Finset ι).toList j) / κ ^ 2 + tr) ≤
      26 * Real.exp 2 * ((d * κ ^ 4) ^ (g + 1) * (q + tr)) := by
    intro g
    obtain ⟨B, hB⟩ : ∃ B, B = (1 / T) ^ (g + 1) * Real.exp 2 := ⟨_, rfl⟩
    have hB0 : 0 ≤ B := by rw [hB]; positivity
    have e2 : ∑ j ∈ (topIdx g : Finset (ι → ℕ)), ∑ s, (2 * a s / κ) * ((j s : ℝ) * P j) =
        ∑ s, (2 * a s / κ) * ∑ j ∈ (topIdx g : Finset (ι → ℕ)), (j s : ℝ) * P j := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun s _ => (Finset.mul_sum _ _ _).symm
    have e3 : ∑ j ∈ (topIdx g : Finset (ι → ℕ)), ∑ s, ∑ t, (4 * b t s / κ ^ 2) *
        ((j s : ℝ) * j t * P j) = ∑ s, ∑ t, (4 * b t s / κ ^ 2) *
          ∑ j ∈ (topIdx g : Finset (ι → ℕ)), (j s : ℝ) * j t * P j := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun t _ => (Finset.mul_sum _ _ _).symm
    have h0 : ∑ j ∈ (topIdx g : Finset (ι → ℕ)), P j ≤ B := (hC0 g).trans_eq hB.symm
    have h1 : ∑ s, (2 * a s / κ) * ∑ j ∈ (topIdx g : Finset (ι → ℕ)), (j s : ℝ) * P j ≤
        B * (tr + 8 * q) := by
      have hc : 0 ≤ 8 * B * y / κ := div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hB0) hy0)
        hκ.le
      calc ∑ s, (2 * a s / κ) * ∑ j ∈ (topIdx g : Finset (ι → ℕ)), (j s : ℝ) * P j
          ≤ ∑ s, (2 * a s / κ) * (B * (4 * y)) := Finset.sum_le_sum fun s _ =>
            mul_le_mul_of_nonneg_left ((hC1 g s).trans_eq (by rw [hB]))
              (div_nonneg (mul_nonneg (by norm_num) (ha0 s)) hκ.le)
        _ = 8 * B * y / κ * ∑ s, a s := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun s _ => by ring
        _ ≤ 8 * B * y / κ * (tr / κ + κ * Fintype.card ι * q) :=
            mul_le_mul_of_nonneg_left hsa hc
        _ = B * tr * (8 * r) + 8 * B * q * (y * Fintype.card ι) := by
            rw [hr]
            field_simp
        _ ≤ B * tr * 1 + 8 * B * q * 1 :=
            add_le_add (mul_le_mul_of_nonneg_left hr8 (mul_nonneg hB0 htr0))
              (mul_le_mul_of_nonneg_left hyc (mul_nonneg (mul_nonneg (by norm_num) hB0) hq0))
        _ = B * (tr + 8 * q) := by ring
    have h2 : ∑ s, ∑ t, (4 * b t s / κ ^ 2) *
        ∑ j ∈ (topIdx g : Finset (ι → ℕ)), (j s : ℝ) * j t * P j ≤ B * (24 * tr) := by
      have hpt : ∀ s, ∑ t, (4 * b t s / κ ^ 2) *
          ∑ j ∈ (topIdx g : Finset (ι → ℕ)), (j s : ℝ) * j t * P j ≤
          (4 * b s s / κ ^ 2) * (B * (8 * y)) +
            ∑ t ∈ Finset.univ.erase s, (4 * b t s / κ ^ 2) * (B * (16 * y ^ 2)) := by
        intro s
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ s)]
        refine add_le_add (mul_le_mul_of_nonneg_left ((hC2 g s).trans_eq (by rw [hB]))
          (div_nonneg (mul_nonneg (by norm_num) (hb0 s s)) (by positivity)))
          (Finset.sum_le_sum fun t ht => mul_le_mul_of_nonneg_left
            ((hC3 g s t (Finset.ne_of_mem_erase ht).symm).trans_eq (by rw [hB]))
            (div_nonneg (mul_nonneg (by norm_num) (hb0 t s)) (by positivity)))
      have hc1 : 0 ≤ 32 * B * y / κ ^ 2 :=
        div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hB0) hy0) (by positivity)
      have hc2 : 0 ≤ 64 * B * y ^ 2 / κ ^ 2 :=
        div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hB0) (by positivity)) (by positivity)
      calc _ ≤ ∑ s, ((4 * b s s / κ ^ 2) * (B * (8 * y)) +
            ∑ t ∈ Finset.univ.erase s, (4 * b t s / κ ^ 2) * (B * (16 * y ^ 2))) :=
            Finset.sum_le_sum fun s _ => hpt s
        _ = 32 * B * y / κ ^ 2 * ∑ s, b s s +
            64 * B * y ^ 2 / κ ^ 2 * ∑ s, ∑ t ∈ Finset.univ.erase s, b t s := by
            rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
            congr 1
            · exact Finset.sum_congr rfl fun s _ => by ring
            · refine Finset.sum_congr rfl fun s _ => ?_
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun t _ => by ring
        _ ≤ 32 * B * y / κ ^ 2 * (2 * tr) + 64 * B * y ^ 2 / κ ^ 2 * (2 * (Fintype.card ι * tr)) :=
            add_le_add (mul_le_mul_of_nonneg_left hbd hc1) (mul_le_mul_of_nonneg_left hbo hc2)
        _ = B * tr * (8 * r) * 8 + B * tr * (8 * r) * (y * Fintype.card ι) * 16 := by
            rw [hr]
            field_simp
            ring
        _ ≤ B * tr * 1 * 8 + B * tr * 1 * 1 * 16 := by
            have h8 := mul_le_mul_of_nonneg_left hr8 (mul_nonneg hB0 htr0)
            have hBr : 0 ≤ B * tr * (8 * r) := mul_nonneg (mul_nonneg hB0 htr0) (by positivity)
            have h9 := mul_le_mul h8 hyc (by positivity) (by linarith)
            nlinarith
        _ = B * (24 * tr) := by ring
    calc ∑ j ∈ (topIdx g : Finset (ι → ℕ)), κ ^ (2 * ∑ i, j i) * (q +
          qd1 0 L ξ (dEvenList (Finset.univ : Finset ι).toList j) / κ +
          qd2 L (dEvenList (Finset.univ : Finset ι).toList j) / κ ^ 2 + tr)
        ≤ ∑ j ∈ (topIdx g : Finset (ι → ℕ)), (P j * (q + tr) +
            ∑ s, (2 * a s / κ) * ((j s : ℝ) * P j) +
            ∑ s, ∑ t, (4 * b t s / κ ^ 2) * ((j s : ℝ) * j t * P j)) :=
          Finset.sum_le_sum fun j _ => hA j
      _ = (∑ j ∈ (topIdx g : Finset (ι → ℕ)), P j) * (q + tr) +
            ∑ s, (2 * a s / κ) * ∑ j ∈ (topIdx g : Finset (ι → ℕ)), (j s : ℝ) * P j +
            ∑ s, ∑ t, (4 * b t s / κ ^ 2) *
              ∑ j ∈ (topIdx g : Finset (ι → ℕ)), (j s : ℝ) * j t * P j := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_mul, e2, e3]
      _ ≤ B * (q + tr) + B * (tr + 8 * q) + B * (24 * tr) :=
          add_le_add (add_le_add (mul_le_mul_of_nonneg_right h0 (by linarith)) h1) h2
      _ ≤ 26 * B * (q + tr) := by nlinarith
      _ = 26 * Real.exp 2 * ((d * κ ^ 4) ^ (g + 1) * (q + tr)) := by rw [hB, hTd]; ring
  -- the grade decomposition
  have hF0 : ∀ j : ι → ℕ, 0 ≤ κ ^ (2 * ∑ i, j i) * (q +
      qd1 0 L ξ (dEvenList (Finset.univ : Finset ι).toList j) / κ +
      qd2 L (dEvenList (Finset.univ : Finset ι).toList j) / κ ^ 2 + tr) := fun j => by
    have := qd1_nonneg 0 L ξ (dEvenList (Finset.univ : Finset ι).toList j)
    have := qd2_nonneg L (dEvenList (Finset.univ : Finset ι).toList j)
    positivity
  have hsub : (retIdx k : Finset (ι → ℕ)).erase 0 ⊆
      (Finset.range k).biUnion (fun g => (topIdx g : Finset (ι → ℕ))) := by
    intro j hj
    obtain ⟨hj0, hjr⟩ := Finset.mem_erase.1 hj
    obtain ⟨hadm, hgr⟩ := mem_retIdx.1 hjr
    have hg1 : 1 ≤ grade j := by
      by_contra h
      push Not at h
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
  calc _ ≤ ∑ j ∈ (Finset.range k).biUnion (fun g => (topIdx g : Finset (ι → ℕ))),
        κ ^ (2 * ∑ i, j i) * (q +
          qd1 0 L ξ (dEvenList (Finset.univ : Finset ι).toList j) / κ +
          qd2 L (dEvenList (Finset.univ : Finset ι).toList j) / κ ^ 2 + tr) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => hF0 j
    _ = ∑ g ∈ Finset.range k, ∑ j ∈ (topIdx g : Finset (ι → ℕ)), κ ^ (2 * ∑ i, j i) * (q +
          qd1 0 L ξ (dEvenList (Finset.univ : Finset ι).toList j) / κ +
          qd2 L (dEvenList (Finset.univ : Finset ι).toList j) / κ ^ 2 + tr) :=
        Finset.sum_biUnion hdisj
    _ ≤ ∑ g ∈ Finset.range k, 26 * Real.exp 2 * ((d * κ ^ 4) ^ (g + 1) * (q + tr)) :=
        Finset.sum_le_sum fun g _ => hgrade g
    _ = _ := by rw [Finset.mul_sum]

end Count

end BiluLinial.Tight.SecB
