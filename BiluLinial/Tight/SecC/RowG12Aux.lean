/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecC.RowX5

/-!
# Helpers for the grade-one and grade-two row terms (CR-G1, CR-G2): star level

Nodes CR-G1, CR-G2 of `docs/tight/BP_SECC.md` (source lines 1153–1190, AUDIT-C §4.2).

* Real inequalities: the seven-term mark sum `Σ_j (x² + |xz| + |x|E + |x|F + E|z| + E² + EF)` is
  at most `4 (P + √P √Q)` with `P = Σ (x² + E²)`, `Q = Σ (z² + F²)` (`g12_marks_le`), and the
  weighted Cauchy–Schwarz `Σ w √A √B ≤ √(Σ w A) √(Σ w B)` (`g12_sum_wsqrt_le`).
* Multi-indices: an admissible index of grade two is `3e_i` or `2e_i + 2e_k`, `i ≠ k`
  (`g12_grade_two_cases`); sums over the retained grades one and two are bounded by sums over
  `i` and over ordered pairs (`g12_sum_grade1_le`, `g12_sum_grade2_le`); `∂^{2j}` for these
  indices (`g12_dEven_single`, `g12_dEven_pair`).
* Star level: the row energies `X⁺_i = a⁴ Σ_j (x_j² + e_ij²)` (`g12P`) and
  `X⁻_i = a⁴ Σ_j (z_j² + f_ij²)` (`g12M`), the T.MARK bounds divided by `Φ` in terms of them
  (`g12_grade1_star`, `g12_grade2d_star`, `g12_grade2m_star`), and `X^±_i ≤ W²` with
  `W = a² Σ_j (1 + r_j)⁴` (`g12P_le_W`, `g12M_le_W`).
-/

@[expose] public section

namespace BiluLinial.Tight

namespace SecC

open Matrix

/-! ### Real inequalities -/

theorem g12_sum_abs_mul_le {ι : Type*} (s : Finset ι) (f g : ι → ℝ) :
    ∑ j ∈ s, |f j| * |g j| ≤ Real.sqrt (∑ j ∈ s, f j ^ 2) * Real.sqrt (∑ j ∈ s, g j ^ 2) := by
  simpa only [sq_abs] using Real.sum_mul_le_sqrt_mul_sqrt s (fun j => |f j|) (fun j => |g j|)

theorem g12_sqrt_scale {c : ℝ} (hc : 0 ≤ c) (P Q : ℝ) :
    c * (Real.sqrt P * Real.sqrt Q) = Real.sqrt (c * P) * Real.sqrt (c * Q) := by
  rw [Real.sqrt_mul hc, Real.sqrt_mul hc]
  have h := Real.mul_self_sqrt hc
  calc c * (Real.sqrt P * Real.sqrt Q) =
        (Real.sqrt c * Real.sqrt c) * (Real.sqrt P * Real.sqrt Q) := by rw [h]
    _ = _ := by ring

/-- Weighted Cauchy–Schwarz: `Σ w √A √B ≤ √(Σ w A) √(Σ w B)`. -/
theorem g12_sum_wsqrt_le {ι : Type*} (s : Finset ι) (w A B : ι → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hA : ∀ j, 0 ≤ A j) (hB : ∀ j, 0 ≤ B j) :
    ∑ j ∈ s, w j * (Real.sqrt (A j) * Real.sqrt (B j)) ≤
      Real.sqrt (∑ j ∈ s, w j * A j) * Real.sqrt (∑ j ∈ s, w j * B j) := by
  have e : ∀ j, w j * (Real.sqrt (A j) * Real.sqrt (B j)) =
      Real.sqrt (w j * A j) * Real.sqrt (w j * B j) := fun j => g12_sqrt_scale (hw j) _ _
  simp only [e]
  have h := Real.sum_mul_le_sqrt_mul_sqrt s (fun j => Real.sqrt (w j * A j))
    (fun j => Real.sqrt (w j * B j))
  have e1 : ∑ j ∈ s, Real.sqrt (w j * A j) ^ 2 = ∑ j ∈ s, w j * A j :=
    Finset.sum_congr rfl fun j _ => Real.sq_sqrt (mul_nonneg (hw j) (hA j))
  have e2 : ∑ j ∈ s, Real.sqrt (w j * B j) ^ 2 = ∑ j ∈ s, w j * B j :=
    Finset.sum_congr rfl fun j _ => Real.sq_sqrt (mul_nonneg (hw j) (hB j))
  rw [e1, e2] at h
  exact h

theorem g12_mono_ps {P P' Q Q' : ℝ} (hPP : P ≤ P') (hQQ : Q ≤ Q') :
    P + Real.sqrt P * Real.sqrt Q ≤ P' + Real.sqrt P' * Real.sqrt Q' :=
  add_le_add hPP (mul_le_mul (Real.sqrt_le_sqrt hPP) (Real.sqrt_le_sqrt hQQ) (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _))

/-- The seven-term mark sum: `≤ 4 (P + √P √Q)`, `P = Σ (X² + E²)`, `Q = Σ (Z² + F²)`. -/
theorem g12_marks_le {ι : Type*} (s : Finset ι) (X Z E F : ι → ℝ) (hE : ∀ j, 0 ≤ E j)
    (hF : ∀ j, 0 ≤ F j) :
    ∑ j ∈ s, (X j ^ 2 + |X j * Z j| + |X j| * E j + |X j| * F j + E j * |Z j| + E j ^ 2 +
        E j * F j) ≤
      4 * (∑ j ∈ s, (X j ^ 2 + E j ^ 2) +
        Real.sqrt (∑ j ∈ s, (X j ^ 2 + E j ^ 2)) * Real.sqrt (∑ j ∈ s, (Z j ^ 2 + F j ^ 2))) := by
  set P := ∑ j ∈ s, (X j ^ 2 + E j ^ 2) with hPdef
  set Q := ∑ j ∈ s, (Z j ^ 2 + F j ^ 2) with hQdef
  have hP0 : 0 ≤ P := Finset.sum_nonneg fun j _ => by positivity
  have hsP0 : 0 ≤ Real.sqrt P := Real.sqrt_nonneg _
  have hsX : Real.sqrt (∑ j ∈ s, X j ^ 2) ≤ Real.sqrt P :=
    Real.sqrt_le_sqrt (Finset.sum_le_sum fun j _ => by nlinarith [sq_nonneg (E j)])
  have hsE : Real.sqrt (∑ j ∈ s, E j ^ 2) ≤ Real.sqrt P :=
    Real.sqrt_le_sqrt (Finset.sum_le_sum fun j _ => by nlinarith [sq_nonneg (X j)])
  have hsZ : Real.sqrt (∑ j ∈ s, Z j ^ 2) ≤ Real.sqrt Q :=
    Real.sqrt_le_sqrt (Finset.sum_le_sum fun j _ => by nlinarith [sq_nonneg (F j)])
  have hsF : Real.sqrt (∑ j ∈ s, F j ^ 2) ≤ Real.sqrt Q :=
    Real.sqrt_le_sqrt (Finset.sum_le_sum fun j _ => by nlinarith [sq_nonneg (Z j)])
  have hk : ∀ {u w : ℝ}, u ≤ Real.sqrt P → w ≤ Real.sqrt Q → 0 ≤ w →
      u * w ≤ Real.sqrt P * Real.sqrt Q := fun hu hw hw0 =>
    mul_le_mul hu hw hw0 hsP0
  have h1 := (g12_sum_abs_mul_le s X Z).trans (hk hsX hsZ (Real.sqrt_nonneg _))
  have h2 := (g12_sum_abs_mul_le s X F).trans (hk hsX hsF (Real.sqrt_nonneg _))
  have h3 := (g12_sum_abs_mul_le s E Z).trans (hk hsE hsZ (Real.sqrt_nonneg _))
  have h4 := (g12_sum_abs_mul_le s E F).trans (hk hsE hsF (Real.sqrt_nonneg _))
  have hterm : ∀ j, X j ^ 2 + |X j * Z j| + |X j| * E j + |X j| * F j + E j * |Z j| + E j ^ 2 +
      E j * F j ≤ 3 / 2 * (X j ^ 2 + E j ^ 2) + |X j| * |Z j| + |X j| * |F j| +
        |E j| * |Z j| + |E j| * |F j| := by
    intro j
    rw [abs_mul, abs_of_nonneg (hE j), abs_of_nonneg (hF j)]
    nlinarith [sq_nonneg (|X j| - E j), sq_abs (X j)]
  have hsum : ∑ j ∈ s, (3 / 2 * (X j ^ 2 + E j ^ 2) + |X j| * |Z j| + |X j| * |F j| +
        |E j| * |Z j| + |E j| * |F j|) =
      3 / 2 * P + ∑ j ∈ s, |X j| * |Z j| + ∑ j ∈ s, |X j| * |F j| +
        ∑ j ∈ s, |E j| * |Z j| + ∑ j ∈ s, |E j| * |F j| := by
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hPdef]
  have hsQ0 := Real.sqrt_nonneg Q
  calc _ ≤ ∑ j ∈ s, (3 / 2 * (X j ^ 2 + E j ^ 2) + |X j| * |Z j| + |X j| * |F j| +
        |E j| * |Z j| + |E j| * |F j|) := Finset.sum_le_sum fun j _ => hterm j
    _ = _ := hsum
    _ ≤ 3 / 2 * P + 4 * (Real.sqrt P * Real.sqrt Q) := by linarith
    _ ≤ _ := by nlinarith [mul_nonneg hsP0 hsQ0]

/-! ### Multi-indices of grades one and two -/

section Index

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- An admissible multi-index of grade two is `3 e_i` or `2 e_i + 2 e_k` with `i ≠ k`. -/
theorem g12_grade_two_cases {j : ι → ℕ} (hadm : ∀ x, j x ≠ 1) (hg : grade j = 2) :
    (∃ i, j = Function.update (0 : ι → ℕ) i 3) ∨
      ∃ i k, i ≠ k ∧ j = Function.update (Function.update (0 : ι → ℕ) i 2) k 2 := by
  have hne : ∃ i, j i - 1 ≠ 0 := by
    by_contra h
    push Not at h
    have : grade j = 0 := Finset.sum_eq_zero fun i _ => h i
    omega
  obtain ⟨i, hi⟩ := hne
  have hle : ∀ x, j x - 1 ≤ grade j := fun x =>
    Finset.single_le_sum (f := fun x => j x - 1) (fun _ _ => Nat.zero_le _) (Finset.mem_univ x)
  have hpair : ∀ x, x ≠ i → (j i - 1) + (j x - 1) ≤ grade j := fun x hx => by
    have hp := Finset.sum_pair (f := fun y => j y - 1) (Ne.symm hx)
    rw [← hp]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun _ _ _ => Nat.zero_le _
  have hji := hadm i
  have hi2 := hle i
  rcases (by omega : j i = 3 ∨ j i = 2) with h3 | h2
  · left
    refine ⟨i, funext fun x => ?_⟩
    by_cases hx : x = i
    · subst hx
      simp [h3]
    · rw [Function.update_of_ne hx]
      have := hpair x hx
      have := hadm x
      simp only [Pi.zero_apply]
      omega
  · right
    have hne2 : ∃ k, k ≠ i ∧ j k - 1 ≠ 0 := by
      by_contra h
      push Not at h
      have hs : grade j = (j i - 1) + ∑ x ∈ Finset.univ.erase i, (j x - 1) := by
        exact (Finset.add_sum_erase _ (fun x => j x - 1) (Finset.mem_univ i)).symm
      have h0 : ∑ x ∈ Finset.univ.erase i, (j x - 1) = 0 :=
        Finset.sum_eq_zero fun x hx => h x (Finset.ne_of_mem_erase hx)
      omega
    obtain ⟨k, hki, hk⟩ := hne2
    have hk2 : j k = 2 := by
      have := hpair k hki
      have := hadm k
      omega
    refine ⟨i, k, Ne.symm hki, funext fun x => ?_⟩
    by_cases hxk : x = k
    · subst hxk
      simp [hk2]
    · rw [Function.update_of_ne hxk]
      by_cases hxi : x = i
      · subst hxi
        simp [h2]
      · rw [Function.update_of_ne hxi]
        have h3 : (j i - 1) + (j k - 1) + (j x - 1) ≤ grade j := by
          have hnot : i ∉ ({k, x} : Finset ι) := by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨Ne.symm hki, Ne.symm hxi⟩
          have e : ∑ y ∈ ({i, k, x} : Finset ι), (j y - 1) =
              (j i - 1) + (j k - 1) + (j x - 1) := by
            rw [Finset.sum_insert hnot, Finset.sum_pair (Ne.symm hxk)]
            omega
          rw [← e]
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            fun _ _ _ => Nat.zero_le _
        have := hadm x
        simp only [Pi.zero_apply]
        omega

/-- Sums over the retained grade-one indices are bounded by sums over the `2 e_i`. -/
theorem g12_sum_grade1_le (T : Finset (ι → ℕ)) (hT : ∀ j ∈ T, (∀ x, j x ≠ 1) ∧ grade j = 1)
    (g : (ι → ℕ) → ℝ) (hg : ∀ j, 0 ≤ g j) :
    ∑ j ∈ T, g j ≤ ∑ i, g (Function.update 0 i 2) := by
  have hsub : T ⊆ Finset.univ.image (fun i => Function.update (0 : ι → ℕ) i 2) := by
    intro j hj
    obtain ⟨i, rfl⟩ := SecA.eq_single_two_of_grade_one (hT j hj).1 (hT j hj).2
    exact Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩
  calc ∑ j ∈ T, g j
      ≤ ∑ j ∈ Finset.univ.image (fun i => Function.update (0 : ι → ℕ) i 2), g j :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => hg j
    _ ≤ ∑ i, g (Function.update 0 i 2) := Finset.sum_image_le_of_nonneg fun j _ => hg j

/-- Sums over the retained grade-two indices are bounded by sums over the `3 e_i` and over the
ordered pairs `(i, k)`, `i ≠ k`, of `2 e_i + 2 e_k`. -/
theorem g12_sum_grade2_le (T : Finset (ι → ℕ)) (hT : ∀ j ∈ T, (∀ x, j x ≠ 1) ∧ grade j = 2)
    (g : (ι → ℕ) → ℝ) (hg : ∀ j, 0 ≤ g j) :
    ∑ j ∈ T, g j ≤ ∑ i, g (Function.update 0 i 3) +
      ∑ ik ∈ (Finset.univ : Finset ι).offDiag,
        g (Function.update (Function.update 0 ik.1 2) ik.2 2) := by
  set U₁ := Finset.univ.image (fun i => Function.update (0 : ι → ℕ) i 3) with hU₁
  set U₂ := (Finset.univ : Finset ι).offDiag.image
    (fun ik => Function.update (Function.update (0 : ι → ℕ) ik.1 2) ik.2 2) with hU₂
  have hsub : T ⊆ U₁ ∪ U₂ := by
    intro j hj
    rcases g12_grade_two_cases (hT j hj).1 (hT j hj).2 with ⟨i, rfl⟩ | ⟨i, k, hik, rfl⟩
    · exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.2
        ⟨(i, k), Finset.mem_offDiag.2 ⟨Finset.mem_univ _, Finset.mem_univ _, hik⟩, rfl⟩)
  have h1 : ∑ j ∈ T, g j ≤ ∑ j ∈ U₁ ∪ U₂, g j :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => hg j
  have h2 : ∑ j ∈ U₁ ∪ U₂, g j ≤ ∑ j ∈ U₁, g j + ∑ j ∈ U₂, g j := by
    have := Finset.sum_union_inter (s₁ := U₁) (s₂ := U₂) (f := g)
    have h0 : 0 ≤ ∑ j ∈ U₁ ∩ U₂, g j := Finset.sum_nonneg fun j _ => hg j
    linarith
  have h3 : ∑ j ∈ U₁, g j ≤ ∑ i, g (Function.update 0 i 3) :=
    Finset.sum_image_le_of_nonneg fun j _ => hg j
  have h4 : ∑ j ∈ U₂, g j ≤ ∑ ik ∈ (Finset.univ : Finset ι).offDiag,
      g (Function.update (Function.update 0 ik.1 2) ik.2 2) :=
    Finset.sum_image_le_of_nonneg fun j _ => hg j
  linarith

omit [Fintype ι] in
/-- `∂^{2 n e_i} = ∂_i^{2n}`. -/
theorem g12_dEven_single {l : List ι} (hl : l.Nodup) {i : ι} (hi : i ∈ l) (n : ℕ)
    (f : (ι → ℝ) → ℝ) : dEven l (Function.update 0 i n) f = (pderiv i)^[2 * n] f := by
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

omit [Fintype ι] in
/-- `∂^{2(2e_i + 2e_k)}` is `∂_k⁴ ∂_i⁴` or `∂_i⁴ ∂_k⁴`, depending on the order in `l`. -/
theorem g12_dEven_pair {l : List ι} (hl : l.Nodup) {i k : ι} (hi : i ∈ l) (hk : k ∈ l)
    (hik : i ≠ k) (f : (ι → ℝ) → ℝ) :
    dEven l (Function.update (Function.update 0 i 2) k 2) f =
        (pderiv k)^[4] ((pderiv i)^[4] f) ∨
      dEven l (Function.update (Function.update 0 i 2) k 2) f =
        (pderiv i)^[4] ((pderiv k)^[4] f) := by
  induction l with
  | nil => simp at hi
  | cons x l ih =>
    rw [dEven_cons]
    have hxl : x ∉ l := (List.nodup_cons.1 hl).1
    have hl' := (List.nodup_cons.1 hl).2
    by_cases hxi : x = i
    · subst hxi
      left
      have hkl : k ∈ l := by
        rcases List.mem_cons.1 hk with h | h
        · exact absurd h.symm hik
        · exact h
      rw [Function.update_of_ne hik, Function.update_self,
        dEven_congr (j' := Function.update 0 k 2) (fun y hy => by
          have hyx : y ≠ x := by rintro rfl; exact hxl hy
          by_cases hyk : y = k
          · subst hyk
            simp
          · rw [Function.update_of_ne hyk, Function.update_of_ne hyk,
              Function.update_of_ne hyx]),
        g12_dEven_single hl' hkl]
    · by_cases hxk : x = k
      · subst hxk
        right
        have hil : i ∈ l := by
          rcases List.mem_cons.1 hi with h | h
          · exact absurd h.symm hxi
          · exact h
        rw [Function.update_self,
          dEven_congr (j' := Function.update 0 i 2) (fun y hy => by
            have hyx : y ≠ x := by rintro rfl; exact hxl hy
            rw [Function.update_of_ne hyx]),
          g12_dEven_single hl' hil]
      · rw [Function.update_of_ne hxk, Function.update_of_ne hxi]
        have hi' : i ∈ l := by
          rcases List.mem_cons.1 hi with h | h
          · exact absurd h.symm hxi
          · exact h
        have hk' : k ∈ l := by
          rcases List.mem_cons.1 hk with h | h
          · exact absurd h.symm hxk
          · exact h
        simpa using ih hl' hi' hk'

end Index

/-! ### Star level -/

section Star

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The plus row-`i` energy `X⁺_i = a⁴ Σ_j (x_j² + e_ij²)`. -/
noncomputable def g12P (a : ℝ) (A : Matrix ι ι ℝ) (x : ι → ℝ) (i : ι) : ℝ :=
  a ^ 4 * ∑ j, (starRow a A x j ^ 2 + starCore a A x i j ^ 2)

/-- The minus row-`i` energy `X⁻_i = a⁴ Σ_j (z_j² + f_ij²)`. -/
noncomputable def g12M (a : ℝ) (B : Matrix ι ι ℝ) (x : ι → ℝ) (i : ι) : ℝ :=
  a ^ 4 * ∑ j, (starRow (-a) B x j ^ 2 + starCore a B x i j ^ 2)

omit [DecidableEq ι] in
theorem g12P_nonneg (a : ℝ) (A : Matrix ι ι ℝ) (x : ι → ℝ) (i : ι) : 0 ≤ g12P a A x i := by
  unfold g12P
  positivity

omit [DecidableEq ι] in
theorem g12M_nonneg (a : ℝ) (B : Matrix ι ι ℝ) (x : ι → ℝ) (i : ι) : 0 ≤ g12M a B x i := by
  unfold g12M
  positivity

omit [Fintype ι] [DecidableEq ι] in
/-- `a⁴ · (seven-term mark sum) ≤ 4 (a⁴P + √(a⁴P) √(a⁴Q))`. -/
theorem g12_marks_scaled [Fintype ι] (a : ℝ) (X Z E F : ι → ℝ) (hE : ∀ j, 0 ≤ E j)
    (hF : ∀ j, 0 ≤ F j) :
    a ^ 4 * ∑ j, (X j ^ 2 + |X j * Z j| + |X j| * E j + |X j| * F j + E j * |Z j| + E j ^ 2 +
        E j * F j) ≤
      4 * (a ^ 4 * ∑ j, (X j ^ 2 + E j ^ 2) +
        Real.sqrt (a ^ 4 * ∑ j, (X j ^ 2 + E j ^ 2)) *
          Real.sqrt (a ^ 4 * ∑ j, (Z j ^ 2 + F j ^ 2))) := by
  have h := g12_marks_le Finset.univ X Z E F hE hF
  have ha : (0 : ℝ) ≤ a ^ 4 := by positivity
  rw [← g12_sqrt_scale ha]
  calc _ ≤ a ^ 4 * (4 * (∑ j, (X j ^ 2 + E j ^ 2) +
        Real.sqrt (∑ j, (X j ^ 2 + E j ^ 2)) * Real.sqrt (∑ j, (Z j ^ 2 + F j ^ 2)))) :=
        mul_le_mul_of_nonneg_left h ha
    _ = _ := by ring

omit [DecidableEq ι] in
/-- The grade-one marks of `mark_grade_one`, scaled by `a⁴`. -/
theorem g12_grade1_marks (a : ℝ) (A B : Matrix ι ι ℝ) (x : ι → ℝ) (i : ι) :
    a ^ 4 * ∑ j, (starRow a A x j ^ 2 + |starRow a A x j * starCore a A x i j| +
        |starRow a A x j * starCore a B x i j| +
        |starCore a A x i j * starRow (-a) B x j| + starCore a A x i j ^ 2 +
        |starCore a A x i j * starCore a B x i j|) ≤
      4 * (g12P a A x i + Real.sqrt (g12P a A x i) * Real.sqrt (g12M a B x i)) := by
  have h := g12_marks_scaled a (starRow a A x) (starRow (-a) B x)
    (fun j => |starCore a A x i j|) (fun j => |starCore a B x i j|)
    (fun j => abs_nonneg _) (fun j => abs_nonneg _)
  simp only [sq_abs] at h
  unfold g12P g12M
  refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => ?_) (by positivity)) h
  simp only [abs_mul]
  have := mul_nonneg (abs_nonneg (starRow a A x j)) (abs_nonneg (starRow (-a) B x j))
  linarith

omit [DecidableEq ι] in
/-- The diagonal grade-two marks of `mark_grade_two_diag`, scaled by `a⁴`. -/
theorem g12_grade2d_marks (a : ℝ) (A B : Matrix ι ι ℝ) (x : ι → ℝ) (i : ι) :
    a ^ 4 * ∑ j, (starRow a A x j ^ 2 + |starRow a A x j * starRow (-a) B x j| +
        |starRow a A x j * starCore a A x i j| + |starRow a A x j * starCore a B x i j| +
        |starCore a A x i j * starRow (-a) B x j| + starCore a A x i j ^ 2 +
        |starCore a A x i j * starCore a B x i j|) ≤
      4 * (g12P a A x i + Real.sqrt (g12P a A x i) * Real.sqrt (g12M a B x i)) := by
  have h := g12_marks_scaled a (starRow a A x) (starRow (-a) B x)
    (fun j => |starCore a A x i j|) (fun j => |starCore a B x i j|)
    (fun j => abs_nonneg _) (fun j => abs_nonneg _)
  simp only [sq_abs] at h
  unfold g12P g12M
  refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => ?_) (by positivity)) h
  simp only [abs_mul]
  exact le_rfl

omit [DecidableEq ι] in
/-- The mixed grade-two marks of `mark_grade_two_mixed`, scaled by `a⁴`. -/
theorem g12_grade2m_marks (a : ℝ) (A B : Matrix ι ι ℝ) (x : ι → ℝ) (i k : ι) :
    a ^ 4 * ∑ j, (starRow a A x j ^ 2 + |starRow a A x j * starRow (-a) B x j| +
        |starRow a A x j| * (|starCore a A x i j| + |starCore a A x k j|) +
        |starRow a A x j| * (|starCore a B x i j| + |starCore a B x k j|) +
        (|starCore a A x i j| + |starCore a A x k j|) * |starRow (-a) B x j| +
        (|starCore a A x i j| + |starCore a A x k j|) ^ 2 +
        (|starCore a A x i j| + |starCore a A x k j|) *
          (|starCore a B x i j| + |starCore a B x k j|)) ≤
      4 * (2 * (g12P a A x i + g12P a A x k) +
        Real.sqrt (2 * (g12P a A x i + g12P a A x k)) *
          Real.sqrt (2 * (g12M a B x i + g12M a B x k))) := by
  have h := g12_marks_scaled a (starRow a A x) (starRow (-a) B x)
    (fun j => |starCore a A x i j| + |starCore a A x k j|)
    (fun j => |starCore a B x i j| + |starCore a B x k j|)
    (fun j => by positivity) (fun j => by positivity)
  refine h.trans (mul_le_mul_of_nonneg_left (g12_mono_ps ?_ ?_) (by norm_num))
  · have e : 2 * (g12P a A x i + g12P a A x k) = a ^ 4 * ∑ j,
        (2 * (starRow a A x j ^ 2 + starCore a A x i j ^ 2) +
          2 * (starRow a A x j ^ 2 + starCore a A x k j ^ 2)) := by
      unfold g12P
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => ?_) (by positivity)
    nlinarith [sq_nonneg (|starCore a A x i j| - |starCore a A x k j|),
      sq_abs (starCore a A x i j), sq_abs (starCore a A x k j), sq_nonneg (starRow a A x j)]
  · have e : 2 * (g12M a B x i + g12M a B x k) = a ^ 4 * ∑ j,
        (2 * (starRow (-a) B x j ^ 2 + starCore a B x i j ^ 2) +
          2 * (starRow (-a) B x j ^ 2 + starCore a B x k j ^ 2)) := by
      unfold g12M
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => ?_) (by positivity)
    nlinarith [sq_nonneg (|starCore a B x i j| - |starCore a B x k j|),
      sq_abs (starCore a B x i j), sq_abs (starCore a B x k j),
      sq_nonneg (starRow (-a) B x j)]

theorem g12_alg1 {a Φ R S1 M P Q p : ℝ} (hΦ : 0 ≤ Φ) (hR : 0 ≤ R) (hp : 0 ≤ p)
    (hM : a ^ 4 * M ≤ 4 * (P + Real.sqrt P * Real.sqrt Q)) :
    a ^ 2 * Φ * a ^ 4 * R * 1000 * (p ^ 5 * S1 + p ^ 4 * M) ≤
      1000 * a ^ 2 * R * (p ^ 5 * (a ^ 4 * S1) + 4 * p ^ 4 * (P + Real.sqrt P * Real.sqrt Q)) *
        Φ := by
  have hc : 0 ≤ 1000 * a ^ 2 * R * Φ := by positivity
  have key : p ^ 4 * (a ^ 4 * M) ≤ 4 * p ^ 4 * (P + Real.sqrt P * Real.sqrt Q) :=
    calc p ^ 4 * (a ^ 4 * M) ≤ p ^ 4 * (4 * (P + Real.sqrt P * Real.sqrt Q)) :=
          mul_le_mul_of_nonneg_left hM (pow_nonneg hp 4)
      _ = _ := by ring
  calc a ^ 2 * Φ * a ^ 4 * R * 1000 * (p ^ 5 * S1 + p ^ 4 * M)
      = 1000 * a ^ 2 * R * Φ * (p ^ 5 * (a ^ 4 * S1) + p ^ 4 * (a ^ 4 * M)) := by ring
    _ ≤ 1000 * a ^ 2 * R * Φ *
          (p ^ 5 * (a ^ 4 * S1) + 4 * p ^ 4 * (P + Real.sqrt P * Real.sqrt Q)) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl key) hc
    _ = _ := by ring

theorem g12_alg2 {a Φ R M Z p : ℝ} (hΦ : 0 ≤ Φ) (hR : 0 ≤ R) (hp : 0 ≤ p)
    (hM : a ^ 4 * M ≤ 4 * Z) :
    a ^ 2 * Φ * a ^ 6 * R * 10 ^ 6 * p ^ 9 * M ≤ 10 ^ 6 * p ^ 9 * a ^ 2 * (a ^ 2 * R * (4 * Z)) *
      Φ := by
  have hc : 0 ≤ 10 ^ 6 * p ^ 9 * a ^ 2 * (a ^ 2 * R) * Φ := by positivity
  calc a ^ 2 * Φ * a ^ 6 * R * 10 ^ 6 * p ^ 9 * M
      = 10 ^ 6 * p ^ 9 * a ^ 2 * (a ^ 2 * R) * Φ * (a ^ 4 * M) := by ring
    _ ≤ 10 ^ 6 * p ^ 9 * a ^ 2 * (a ^ 2 * R) * Φ * (4 * Z) := mul_le_mul_of_nonneg_left hM hc
    _ = _ := by ring

theorem g12_alg3 {a Φ R₁ R₂ M Z p : ℝ} (hΦ : 0 ≤ Φ) (hR₁ : 0 ≤ R₁) (hR₂ : 0 ≤ R₂) (hp : 0 ≤ p)
    (hM : a ^ 4 * M ≤ 4 * Z) :
    a ^ 2 * Φ * a ^ 8 * R₁ * R₂ * 10 ^ 6 * p ^ 9 * M ≤
      10 ^ 6 * p ^ 9 * a ^ 2 * (a ^ 4 * R₁ * R₂ * (4 * Z)) * Φ := by
  have hc : 0 ≤ 10 ^ 6 * p ^ 9 * a ^ 2 * (a ^ 4 * R₁ * R₂) * Φ := by positivity
  calc a ^ 2 * Φ * a ^ 8 * R₁ * R₂ * 10 ^ 6 * p ^ 9 * M
      = 10 ^ 6 * p ^ 9 * a ^ 2 * (a ^ 4 * R₁ * R₂) * Φ * (a ^ 4 * M) := by ring
    _ ≤ 10 ^ 6 * p ^ 9 * a ^ 2 * (a ^ 4 * R₁ * R₂) * Φ * (4 * Z) :=
        mul_le_mul_of_nonneg_left hM hc
    _ = _ := by ring

/-- **Grade one, one coordinate**, divided by `Φ`. -/
theorem g12_grade1_star {p : ℕ} (hp : 8 ≤ p) {a : ℝ} (ha : 0 < a) {A B : Matrix ι ι ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) {x : ι → ℝ} (hα : 0 < starAlpha A x)
    (hβ : 0 < starAlpha B x) (i : ι) :
    |(pderiv i)^[4] (rowNum p A B) x / starPhi p A B x| ≤
      1000 * a ^ 2 * (1 + starScale a A B x i) ^ 4 *
        ((p : ℝ) ^ 5 * (a ^ 4 * |∑ j, starRow a A x j * (starRow a A x j - starRow (-a) B x j)|) +
          4 * (p : ℝ) ^ 4 *
            (g12P a A x i + Real.sqrt (g12P a A x i) * Real.sqrt (g12M a B x i))) := by
  have hΦ : 0 < starPhi p A B x := by rw [starPhi_eq hα hβ]; positivity
  have hr := starScale_nonneg (a := a) (A := A) (B := B) (x := x) i
  rw [abs_div, abs_of_pos hΦ, div_le_iff₀ hΦ]
  exact (mark_grade_one hp ha hA hB hα hβ i).trans
    (g12_alg1 hΦ.le (by positivity) (Nat.cast_nonneg p) (g12_grade1_marks a A B x i))

/-- **Grade two, one coordinate** (`∂_i⁶`), divided by `Φ`. -/
theorem g12_grade2d_star {p : ℕ} (hp : 8 ≤ p) {a : ℝ} (ha : 0 < a) {A B : Matrix ι ι ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) {x : ι → ℝ} (hα : 0 < starAlpha A x)
    (hβ : 0 < starAlpha B x) (i : ι) :
    |(pderiv i)^[6] (rowNum p A B) x / starPhi p A B x| ≤
      10 ^ 6 * (p : ℝ) ^ 9 * a ^ 2 * (a ^ 2 * (1 + starScale a A B x i) ^ 6 *
        (4 * (g12P a A x i + Real.sqrt (g12P a A x i) * Real.sqrt (g12M a B x i)))) := by
  have hΦ : 0 < starPhi p A B x := by rw [starPhi_eq hα hβ]; positivity
  have hr := starScale_nonneg (a := a) (A := A) (B := B) (x := x) i
  rw [abs_div, abs_of_pos hΦ, div_le_iff₀ hΦ]
  exact (mark_grade_two_diag hp ha hA hB hα hβ i).trans
    (g12_alg2 hΦ.le (by positivity) (Nat.cast_nonneg p) (g12_grade2d_marks a A B x i))

/-- The symmetric pair bound `a⁴ (1 + r_i)⁴ (1 + r_k)⁴ · 4 (Y⁺ + √Y⁺ √Y⁻)`,
`Y^± = 2 (X^±_i + X^±_k)`. -/
noncomputable def g12Bm (a : ℝ) (A B : Matrix ι ι ℝ) (x : ι → ℝ) (i k : ι) : ℝ :=
  a ^ 4 * (1 + starScale a A B x i) ^ 4 * (1 + starScale a A B x k) ^ 4 *
    (4 * (2 * (g12P a A x i + g12P a A x k) +
      Real.sqrt (2 * (g12P a A x i + g12P a A x k)) *
        Real.sqrt (2 * (g12M a B x i + g12M a B x k))))

omit [DecidableEq ι] in
theorem g12Bm_comm (a : ℝ) (A B : Matrix ι ι ℝ) (x : ι → ℝ) (i k : ι) :
    g12Bm a A B x k i = g12Bm a A B x i k := by
  unfold g12Bm
  rw [add_comm (g12P a A x k), add_comm (g12M a B x k)]
  ring

/-- **Grade two, two coordinates** (`∂_i⁴ ∂_k⁴`, `i ≠ k`), divided by `Φ`. -/
theorem g12_grade2m_star {p : ℕ} (hp : 8 ≤ p) {a : ℝ} (ha : 0 < a) {A B : Matrix ι ι ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) {x : ι → ℝ} (hα : 0 < starAlpha A x)
    (hβ : 0 < starAlpha B x) {i k : ι} (hik : i ≠ k) :
    |(pderiv i)^[4] ((pderiv k)^[4] (rowNum p A B)) x / starPhi p A B x| ≤
      10 ^ 6 * (p : ℝ) ^ 9 * a ^ 2 * g12Bm a A B x i k := by
  have hΦ : 0 < starPhi p A B x := by rw [starPhi_eq hα hβ]; positivity
  have hri := starScale_nonneg (a := a) (A := A) (B := B) (x := x) i
  have hrk := starScale_nonneg (a := a) (A := A) (B := B) (x := x) k
  rw [abs_div, abs_of_pos hΦ, div_le_iff₀ hΦ]
  exact (mark_grade_two_mixed hp ha hA hB hα hβ hik).trans
    (g12_alg3 hΦ.le (by positivity) (by positivity) (Nat.cast_nonneg p)
      (g12_grade2m_marks a A B x i k))

theorem g12_one_add_sq_le {r : ℝ} (hr : 0 ≤ r) : 1 + r ^ 2 ≤ (1 + r) ^ 4 := by
  nlinarith [pow_nonneg hr 3, pow_nonneg hr 4, sq_nonneg r]

theorem g12_sq_le_pow4 {r : ℝ} (hr : 0 ≤ r) : r ^ 2 ≤ (1 + r) ^ 4 := by
  nlinarith [pow_nonneg hr 3, pow_nonneg hr 4, sq_nonneg r]

omit [DecidableEq ι] in
theorem g12_single_le_W (a : ℝ) (A B : Matrix ι ι ℝ) (x : ι → ℝ) (i : ι) :
    a ^ 2 * (1 + starScale a A B x i) ^ 4 ≤ a ^ 2 * ∑ j, (1 + starScale a A B x j) ^ 4 :=
  mul_le_mul_of_nonneg_left
    (Finset.single_le_sum (f := fun j => (1 + starScale a A B x j) ^ 4)
      (fun j _ => by have := starScale_nonneg (a := a) (A := A) (B := B) (x := x) j; positivity)
      (Finset.mem_univ i)) (sq_nonneg a)

omit [DecidableEq ι] in
theorem g12_rowsum_le (a : ℝ) {A B : Matrix ι ι ℝ} {x : ι → ℝ} (u c : ι → ℝ) (i : ι)
    (hu : ∀ j, u j ^ 2 ≤ starScale a A B x j ^ 2)
    (hc : ∀ j, c j ^ 2 ≤ (starScale a A B x i * starScale a A B x j) ^ 2) :
    a ^ 4 * ∑ j, (u j ^ 2 + c j ^ 2) ≤ (a ^ 2 * ∑ j, (1 + starScale a A B x j) ^ 4) ^ 2 := by
  have hr : ∀ j, 0 ≤ starScale a A B x j := fun j => starScale_nonneg j
  have hterm : ∀ j, u j ^ 2 + c j ^ 2 ≤
      (1 + starScale a A B x i) ^ 4 * (1 + starScale a A B x j) ^ 4 := by
    intro j
    calc u j ^ 2 + c j ^ 2
        ≤ starScale a A B x j ^ 2 + (starScale a A B x i * starScale a A B x j) ^ 2 :=
          add_le_add (hu j) (hc j)
      _ = (1 + starScale a A B x i ^ 2) * starScale a A B x j ^ 2 := by ring
      _ ≤ (1 + starScale a A B x i) ^ 4 * (1 + starScale a A B x j) ^ 4 :=
          mul_le_mul (g12_one_add_sq_le (hr i)) (g12_sq_le_pow4 (hr j)) (sq_nonneg _)
            (by positivity)
  have hW0 : 0 ≤ a ^ 2 * ∑ j, (1 + starScale a A B x j) ^ 4 :=
    mul_nonneg (sq_nonneg a) (Finset.sum_nonneg fun j _ => by have := hr j; positivity)
  calc a ^ 4 * ∑ j, (u j ^ 2 + c j ^ 2)
      ≤ a ^ 4 * ∑ j, (1 + starScale a A B x i) ^ 4 * (1 + starScale a A B x j) ^ 4 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => hterm j) (by positivity)
    _ = (a ^ 2 * (1 + starScale a A B x i) ^ 4) * (a ^ 2 * ∑ j, (1 + starScale a A B x j) ^ 4) := by
        rw [← Finset.mul_sum]
        ring
    _ ≤ (a ^ 2 * ∑ j, (1 + starScale a A B x j) ^ 4) *
          (a ^ 2 * ∑ j, (1 + starScale a A B x j) ^ 4) :=
        mul_le_mul_of_nonneg_right (g12_single_le_W a A B x i) hW0
    _ = _ := (sq _).symm

theorem g12_sq_le_of_abs_le {u r : ℝ} (h : |u| ≤ r) : u ^ 2 ≤ r ^ 2 := by
  rw [← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) h 2

omit [DecidableEq ι] in
/-- `X⁺_i ≤ W²`, `W = a² Σ_j (1 + r_j)⁴`. -/
theorem g12P_le_W {a : ℝ} {A B : Matrix ι ι ℝ} {x : ι → ℝ} (hA : A.PosSemidef)
    (hα : 0 < starAlpha A x) (i : ι) :
    g12P a A x i ≤ (a ^ 2 * ∑ j, (1 + starScale a A B x j) ^ 4) ^ 2 :=
  g12_rowsum_le a (starRow a A x) (starCore a A x i) i
    (fun j => g12_sq_le_of_abs_le (abs_starRow_le (B := B) j))
    (fun j => g12_sq_le_of_abs_le (abs_starCore_le (B := B) hA hα i j))

omit [DecidableEq ι] in
/-- `X⁻_i ≤ W²`. -/
theorem g12M_le_W {a : ℝ} {A B : Matrix ι ι ℝ} {x : ι → ℝ} (hB : B.PosSemidef)
    (hβ : 0 < starAlpha B x) (i : ι) :
    g12M a B x i ≤ (a ^ 2 * ∑ j, (1 + starScale a A B x j) ^ 4) ^ 2 :=
  g12_rowsum_le a (starRow (-a) B x) (starCore a B x i) i
    (fun j => g12_sq_le_of_abs_le (abs_starRow_neg_le (A := A) j))
    (fun j => g12_sq_le_of_abs_le (abs_starCore_le' (A := A) hB hβ i j))

end Star

end SecC

end BiluLinial.Tight
