/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.Compare.Coeff
public import BiluLinial.Tight.Compare.Partial

/-!
# Multi-indices for the comparison (E4)

Part D (`docs/second_order_bilu_linial_tight.tex`, Section 1.2, eq. (E4)): "For a multi-index `j`
with entries zero or at least two, put `|j|_g = Σ_{j_i>0} (j_i - 1)` and `c_j = Π c_{j_i}`."

* `grade j = Σ_i (j_i - 1)` (truncated subtraction, so zero entries contribute `0`);
* `ecoefM j = Π_i c_{j_i}`;
* `suppBox K l`: multi-indices with entries `< K` supported on the list `l`; `retSet K l k` and
  `topSet K l k`: its admissible members (no entry `1`) of grade `≤ k`, resp. `= k + 1`;
* `dEven l j f = ∂^{2j} f`, the derivatives taken coordinate by coordinate in the order of `l`;
* `sum_retSet_cons`, `sum_topSet_cons`: the decomposition of these sums by the value of the
  first coordinate of `l`, used in the hybrid induction.
-/

@[expose] public section

namespace BiluLinial.Tight

open Finset Function

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The grade `|j|_g = Σ_{j_i > 0} (j_i - 1)` of a multi-index (truncated subtraction). -/
def grade (j : ι → ℕ) : ℕ := ∑ i, (j i - 1)

/-- `c_j = Π_i c_{j_i}`. -/
noncomputable def ecoefM (j : ι → ℕ) : ℝ := ∏ i, ecoef (j i)

/-- Multi-indices with entries `< K` supported on the list `l`. -/
def suppBox (K : ℕ) (l : List ι) : Finset (ι → ℕ) :=
  (Fintype.piFinset fun _ => range K).filter fun j => ∀ x, x ∉ l → j x = 0

/-- Admissible multi-indices (no entry equal to `1`) supported on `l`, entries `< K`, grade
`≤ k`: the retained terms of (E4). -/
def retSet (K : ℕ) (l : List ι) (k : ℕ) : Finset (ι → ℕ) :=
  (suppBox K l).filter fun j => (∀ x, j x ≠ 1) ∧ grade j ≤ k

/-- Admissible multi-indices supported on `l`, entries `< K`, grade exactly `k + 1`: the
remainder terms of (E4). -/
def topSet (K : ℕ) (l : List ι) (k : ℕ) : Finset (ι → ℕ) :=
  (suppBox K l).filter fun j => (∀ x, j x ≠ 1) ∧ grade j = k + 1

/-- `∂^{2j} f = Π_{x ∈ l} ∂_x^{2 j_x} f`, the coordinates of `l` being differentiated in order. -/
noncomputable def dEven (l : List ι) (j : ι → ℕ) (f : (ι → ℝ) → ℝ) : (ι → ℝ) → ℝ :=
  pderivList (l.flatMap fun x => List.replicate (2 * j x) x) f

theorem mem_suppBox {K : ℕ} {l : List ι} {j : ι → ℕ} :
    j ∈ suppBox K l ↔ (∀ x, j x < K) ∧ ∀ x, x ∉ l → j x = 0 := by
  simp [suppBox, Fintype.mem_piFinset]

theorem mem_retSet {K : ℕ} {l : List ι} {k : ℕ} {j : ι → ℕ} :
    j ∈ retSet K l k ↔ j ∈ suppBox K l ∧ (∀ x, j x ≠ 1) ∧ grade j ≤ k := by
  simp [retSet]

theorem mem_topSet {K : ℕ} {l : List ι} {k : ℕ} {j : ι → ℕ} :
    j ∈ topSet K l k ↔ j ∈ suppBox K l ∧ (∀ x, j x ≠ 1) ∧ grade j = k + 1 := by
  simp [topSet]

omit [DecidableEq ι] in
@[simp] theorem grade_zero : grade (0 : ι → ℕ) = 0 := by simp [grade]

omit [DecidableEq ι] in
@[simp] theorem ecoefM_zero : ecoefM (0 : ι → ℕ) = 1 := by simp [ecoefM]

omit [Fintype ι] in
theorem dEven_nil (j : ι → ℕ) (f : (ι → ℝ) → ℝ) : dEven [] j f = f := rfl

omit [Fintype ι] in
theorem dEven_cons (i : ι) (l : List ι) (j : ι → ℕ) (f : (ι → ℝ) → ℝ) :
    dEven (i :: l) j f = dEven l j ((pderiv i)^[2 * j i] f) := by
  simp only [dEven, List.flatMap_cons, pderivList_append, pderivList_replicate]

omit [Fintype ι] in
theorem dEven_congr {l : List ι} {j j' : ι → ℕ} (h : ∀ x ∈ l, j x = j' x)
    (f : (ι → ℝ) → ℝ) : dEven l j f = dEven l j' f := by
  unfold dEven
  rw [List.flatMap_congr (fun x hx => by rw [h x hx])]

omit [Fintype ι] in
theorem dEven_zero (l : List ι) (f : (ι → ℝ) → ℝ) : dEven l 0 f = f := by
  induction l generalizing f with
  | nil => rfl
  | cons i l ih => rw [dEven_cons]; simpa using ih f

theorem grade_update {j : ι → ℕ} {i : ι} (hj : j i = 0) (a : ℕ) :
    grade (update j i a) = grade j + (a - 1) := by
  unfold grade
  rw [Fintype.sum_eq_add_sum_compl i, Fintype.sum_eq_add_sum_compl i (fun x => j x - 1)]
  simp only [update_self, hj]
  have : ∑ x ∈ {i}ᶜ, (update j i a x - 1) = ∑ x ∈ {i}ᶜ, (j x - 1) := by
    apply sum_congr rfl
    intro x hx
    rw [update_of_ne (by simpa using hx)]
  rw [this]
  omega

theorem ecoefM_update {j : ι → ℕ} {i : ι} (hj : j i = 0) (a : ℕ) :
    ecoefM (update j i a) = ecoef a * ecoefM j := by
  unfold ecoefM
  rw [Fintype.prod_eq_mul_prod_compl i, Fintype.prod_eq_mul_prod_compl i (fun x => ecoef (j x))]
  simp only [update_self, hj, ecoef_zero, one_mul]
  congr 1
  apply prod_congr rfl
  intro x hx
  rw [update_of_ne (by simpa using hx)]

omit [Fintype ι] in
theorem adm_update {j : ι → ℕ} {i : ι} (hj : j i = 0) (a : ℕ) :
    (∀ x, update j i a x ≠ 1) ↔ a ≠ 1 ∧ ∀ x, j x ≠ 1 := by
  constructor
  · intro h
    refine ⟨by simpa using h i, fun x => ?_⟩
    by_cases hx : x = i
    · subst hx; rw [hj]; omega
    · simpa [update_of_ne hx] using h x
  · rintro ⟨ha, h⟩ x
    by_cases hx : x = i
    · subst hx; simpa using ha
    · rw [update_of_ne hx]; exact h x

omit [DecidableEq ι] in
theorem eq_zero_of_grade_eq_zero {j : ι → ℕ} (hadm : ∀ x, j x ≠ 1) (hg : grade j = 0) :
    j = 0 := by
  funext x
  have h1 := (Finset.sum_eq_zero_iff.mp hg) x (mem_univ x)
  have h2 := hadm x
  simp only [Pi.zero_apply]
  omega

/-- Decomposing a sum over multi-indices supported on `i :: l` by the value of the `i`-th entry. -/
theorem sum_suppBox_cons {K : ℕ} {i : ι} {l : List ι} (hi : i ∉ l) (φ : (ι → ℕ) → ℝ) :
    ∑ j ∈ suppBox K (i :: l), φ j = ∑ a ∈ range K, ∑ j ∈ suppBox K l, φ (update j i a) := by
  rw [← sum_product' (range K) (suppBox K l) (fun a j => φ (update j i a))]
  refine sum_nbij' (fun j => (j i, update j i 0)) (fun p => update p.2 i p.1) ?_ ?_ ?_ ?_ ?_
  · intro j hj
    rw [mem_suppBox] at hj
    simp only [mem_product, mem_range, mem_suppBox]
    refine ⟨hj.1 i, fun x => ?_, fun x hx => ?_⟩
    · by_cases h : x = i
      · subst h; simpa using lt_of_le_of_lt (Nat.zero_le _) (hj.1 x)
      · simp [update_of_ne h, hj.1 x]
    · by_cases h : x = i
      · subst h; simp
      · rw [update_of_ne h]; exact hj.2 x (by simp [h, hx])
  · rintro ⟨a, j⟩ hp
    simp only [mem_product, mem_range, mem_suppBox] at hp
    rw [mem_suppBox]
    refine ⟨fun x => ?_, fun x hx => ?_⟩
    · by_cases h : x = i
      · subst h; simpa using hp.1
      · simp [update_of_ne h, hp.2.1 x]
    · have h : x ≠ i := fun h => hx (by simp [h])
      rw [update_of_ne h]
      exact hp.2.2 x (fun hl => hx (by simp [hl]))
  · intro j _
    simp
  · rintro ⟨a, j⟩ hp
    simp only [mem_product, mem_suppBox] at hp
    have hj0 : j i = 0 := hp.2.2 i hi
    refine Prod.ext (by simp) ?_
    funext x
    by_cases h : x = i
    · subst h; simp [hj0]
    · simp [update_of_ne h]
  · intro j _
    simp

/-- Decomposition of the retained sum of (E4) by the value `a` of the first coordinate. -/
theorem sum_retSet_cons {K k : ℕ} (hK : k + 2 ≤ K) {i : ι} {l : List ι} (hi : i ∉ l)
    (φ : (ι → ℕ) → ℝ) (ψ : ℕ → (ι → ℕ) → ℝ)
    (hφ : ∀ j ∈ suppBox K l, ∀ a, φ (update j i a) = ecoef a * ψ a j) :
    ∑ j ∈ retSet K (i :: l) k, φ j =
      ∑ a ∈ range (k + 2), ecoef a * ∑ j ∈ retSet K l (k - (a - 1)), ψ a j := by
  rw [retSet, sum_filter, sum_suppBox_cons hi, ← sum_range_add_sum_Ico _ hK]
  have hIco : ∑ a ∈ Ico (k + 2) K, ∑ j ∈ suppBox K l,
      (if (∀ x, update j i a x ≠ 1) ∧ grade (update j i a) ≤ k then φ (update j i a) else 0) =
        0 := by
    apply sum_eq_zero
    intro a ha
    apply sum_eq_zero
    intro j hj
    have hj0 : j i = 0 := (mem_suppBox.mp hj).2 i hi
    rw [ite_eq_right]
    rw [grade_update hj0]
    simp only [mem_Ico] at ha
    omega
  rw [hIco, add_zero]
  apply sum_congr rfl
  intro a ha
  simp only [mem_range] at ha
  rw [retSet, sum_filter, mul_sum]
  apply sum_congr rfl
  intro j hj
  have hj0 : j i = 0 := (mem_suppBox.mp hj).2 i hi
  simp only [adm_update hj0, grade_update hj0, hφ j hj a]
  by_cases ha1 : a = 1
  · subst ha1; simp
  · have e : grade j + (a - 1) ≤ k ↔ grade j ≤ k - (a - 1) := by omega
    simp only [ne_eq, ha1, not_false_eq_true, true_and, e]
    split_ifs <;> ring

/-- Decomposition of the remainder sum of (E4) by the value `a` of the first coordinate: the
values `a ≤ k + 1` leave a remainder of grade `k + 1 - (a - 1)` in the other coordinates, and
`a = k + 2` is the remainder of the first coordinate itself. -/
theorem sum_topSet_cons {K k : ℕ} (hK : k + 3 ≤ K) {i : ι} {l : List ι} (hi : i ∉ l)
    (M : (ι → ℕ) → ℝ) :
    ∑ j ∈ topSet K (i :: l) k, M j =
      ∑ a ∈ range (k + 2), (if a = 1 then 0 else
        ∑ j ∈ topSet K l (k - (a - 1)), M (update j i a)) + M (update 0 i (k + 2)) := by
  rw [topSet, sum_filter, sum_suppBox_cons hi, ← sum_range_add_sum_Ico _ hK]
  have hIco : ∑ a ∈ Ico (k + 3) K, ∑ j ∈ suppBox K l,
      (if (∀ x, update j i a x ≠ 1) ∧ grade (update j i a) = k + 1 then M (update j i a)
        else 0) = 0 := by
    apply sum_eq_zero
    intro a ha
    apply sum_eq_zero
    intro j hj
    have hj0 : j i = 0 := (mem_suppBox.mp hj).2 i hi
    rw [ite_eq_right]
    rw [grade_update hj0]
    simp only [mem_Ico] at ha
    omega
  rw [hIco, add_zero, sum_range_succ]
  congr 1
  · apply sum_congr rfl
    intro a ha
    simp only [mem_range] at ha
    split_ifs with ha1
    · subst ha1
      apply sum_eq_zero
      intro j hj
      have hj0 : j i = 0 := (mem_suppBox.mp hj).2 i hi
      rw [ite_eq_right]
      rw [adm_update hj0]
      simp
    · rw [topSet, sum_filter]
      apply sum_congr rfl
      intro j hj
      have hj0 : j i = 0 := (mem_suppBox.mp hj).2 i hi
      simp only [adm_update hj0, grade_update hj0]
      have e : grade j + (a - 1) = k + 1 ↔ grade j = k - (a - 1) + 1 := by omega
      simp only [ne_eq, ha1, not_false_eq_true, true_and, e]
  · have h0 : (0 : ι → ℕ) ∈ suppBox K l := by
      rw [mem_suppBox]; exact ⟨fun x => by simp; omega, fun x _ => rfl⟩
    rw [sum_eq_single (0 : ι → ℕ)]
    · rw [ite_eq_left]
      rw [adm_update (by rfl), grade_update (by rfl)]
      refine ⟨⟨by omega, fun x => by simp⟩, by simp⟩
    · intro j hj hne
      have hj0 : j i = 0 := (mem_suppBox.mp hj).2 i hi
      rw [ite_eq_right]
      rw [adm_update hj0, grade_update hj0]
      rintro ⟨⟨_, hadm⟩, hg⟩
      exact hne (eq_zero_of_grade_eq_zero hadm (by omega))
    · intro h; exact absurd h0 h

end BiluLinial.Tight
