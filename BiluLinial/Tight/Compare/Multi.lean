/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.Compare.OneDim
public import BiluLinial.Tight.Compare.Fubini
public import BiluLinial.Tight.Compare.MultiIndex

/-!
# The high-order Rademacher-to-Gaussian comparison (E4)

Part D (`docs/second_order_bilu_linial_tight.tex`, Section 1.2, eq. (E4)):
`𝖦 f = Σ_{|j|_g ≤ k} c_j 𝖱 ∂^{2j} f + 𝓔_k(f)`, `|𝓔_k(f)| ≤ C^{k+1} Σ_{|j|_g = k+1} ‖∂^{2j} f‖_∞`,
the sums running over multi-indices `j` with entries `0` or `≥ 2`. We prove it with `C^{k+1}`
replaced by the absolute constant `2` (`gauss_rad_expansion`).

Proof (hybrid argument, `hybrid_expansion`): process the coordinates of a list `l` one at a time.
For the first coordinate `i`, integrate it out (`integral_hybPi_cons`) and apply the
one-dimensional comparison with budget `k` on every coordinate line (`slice_compare`): this
spends grade `a - 1` on the selected derivative `∂_i^{2a}` (`a ∈ {0, 2, …, k+1}`; `c_1 = 0`) and
leaves the first remainder `∂_i^{2k+4} f`, of grade exactly `k + 1`, with constant `2`. The
retained terms `∂_i^{2a} f` are then expanded in the remaining coordinates with budget
`k - (a - 1)` (induction hypothesis). Every remainder multi-index of grade `k + 1` arises exactly
once (`sum_topSet_cons`), with coefficient `Π |c_{a}| ≤ 1` times `2`.
-/

@[expose] public section

namespace BiluLinial.Tight

open MeasureTheory ProbabilityTheory Finset Function

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The one-dimensional comparison along every coordinate line, with budget `k`. -/
theorem slice_compare {k : ℕ} {f : (ι → ℝ) → ℝ} (hf : SmoothBdd (4 * k + 4) f) (i : ι) (B : ℝ)
    (hB : ∀ x, |(pderiv i)^[2 * k + 4] f x| ≤ B) (x : ι → ℝ) :
    |∫ t, f (update x i t) ∂gaussianReal 0 1 -
        ∑ a ∈ range (k + 2), ecoef a * ∫ t, (pderiv i)^[2 * a] f (update x i t) ∂radReal| ≤
      2 * B := by
  have h := gauss_rad_compare_chain (k + 1) (fun m t => (pderiv i)^[m] f (update x i t))
    (fun m hm t => by
      have hd : Differentiable ℝ ((pderiv i)^[m] f) :=
        (hf.iterate' (m := m) (by omega) i).differentiable (by omega)
      have := hasDerivAt_slice hd x i t
      rwa [← iterate_succ_apply' (pderiv i) m f] at this) B
    (fun t => by
      rw [show 2 * (k + 1) + 2 = 2 * k + 4 by ring]
      exact hB _)
  exact h

private theorem single_mem_topSet {K k : ℕ} (hK : k + 3 ≤ K) (i : ι) (l : List ι) :
    update (0 : ι → ℕ) i (k + 2) ∈ topSet K (i :: l) k := by
  rw [mem_topSet, mem_suppBox]
  refine ⟨⟨fun x => ?_, fun x hx => ?_⟩, ?_, ?_⟩
  · by_cases h : x = i
    · subst h; simp; omega
    · simp [update_of_ne h]; omega
  · have h : x ≠ i := fun h => hx (by simp [h])
    simp [update_of_ne h]
  · rw [adm_update (by rfl)]; exact ⟨by omega, fun x => by simp⟩
  · rw [grade_update (by rfl)]; simp

private theorem update_mem_topSet {K k k' a : ℕ} {i : ι} {l : List ι} (hi : i ∉ l)
    {j : ι → ℕ} (hj : j ∈ topSet K l k') (haK : a < K) (ha1 : a ≠ 1) (hk : a - 1 ≤ k)
    (hk' : k' = k - (a - 1)) : update j i a ∈ topSet K (i :: l) k := by
  obtain ⟨hs, hadm, hg⟩ := mem_topSet.mp hj
  have hj0 : j i = 0 := (mem_suppBox.mp hs).2 i hi
  rw [mem_topSet, mem_suppBox]
  refine ⟨⟨fun x => ?_, fun x hx => ?_⟩, ?_, ?_⟩
  · by_cases h : x = i
    · subst h; simpa using haK
    · rw [update_of_ne h]; exact (mem_suppBox.mp hs).1 x
  · have h : x ≠ i := fun h => hx (by simp [h])
    rw [update_of_ne h]
    exact (mem_suppBox.mp hs).2 x (fun hl => hx (by simp [hl]))
  · rw [adm_update hj0]; exact ⟨ha1, hadm⟩
  · rw [grade_update hj0, hg, hk']; omega

omit [Fintype ι] in
/-- `dEven (i :: l) (update j i a) f = dEven l j (∂_i^{2a} f)` when `i ∉ l`. -/
private theorem dEven_cons_update {i : ι} {l : List ι} (hi : i ∉ l) (j : ι → ℕ) (a : ℕ)
    (f : (ι → ℝ) → ℝ) : dEven (i :: l) (update j i a) f = dEven l j ((pderiv i)^[2 * a] f) := by
  rw [dEven_cons, update_self]
  apply dEven_congr
  intro y hy
  have : y ≠ i := fun h => hi (h ▸ hy)
  rw [update_of_ne this]

/-- **Hybrid expansion.** Gaussian coordinates on the list `l` (Rademacher elsewhere): for
`f ∈ C^{4k+4}` with bounded partial derivatives,
`|∫ f d(hybPi l) - Σ_{j ∈ retSet K l k} c_j 𝖱 ∂^{2j} f| ≤ 2 Σ_{j ∈ topSet K l k} M_j` whenever
`|∂^{2j} f| ≤ M_j` for the remainder multi-indices `j` (grade `k + 1`, supported on `l`). -/
theorem hybrid_expansion (K : ℕ) : ∀ (l : List ι), l.Nodup → ∀ (k : ℕ), k + 3 ≤ K →
    ∀ (f : (ι → ℝ) → ℝ), SmoothBdd (4 * k + 4) f → ∀ (M : (ι → ℕ) → ℝ),
    (∀ j ∈ topSet K l k, ∀ x, |dEven l j f x| ≤ M j) →
    |∫ x, f x ∂hybPi l - ∑ j ∈ retSet K l k, ecoefM j * ∫ x, dEven l j f x ∂radPi ι| ≤
      2 * ∑ j ∈ topSet K l k, M j := by
  intro l
  induction l with
  | nil =>
    intro _ k hK f _ M _
    have hret : ∑ j ∈ retSet K ([] : List ι) k, ecoefM j * ∫ x, dEven [] j f x ∂radPi ι =
        ∫ x, f x ∂radPi ι := by
      rw [sum_eq_single (0 : ι → ℕ)]
      · simp [dEven_nil]
      · intro j hj hne
        exfalso; apply hne
        funext x
        exact (mem_suppBox.mp (mem_retSet.mp hj).1).2 x List.not_mem_nil
      · intro h; exfalso; apply h
        rw [mem_retSet, mem_suppBox]
        exact ⟨⟨fun x => by simp; omega, fun x _ => rfl⟩, fun x => by simp, by simp⟩
    have htop : ∑ j ∈ topSet K ([] : List ι) k, M j = 0 := by
      apply sum_eq_zero
      intro j hj
      exfalso
      obtain ⟨hs, _, hg⟩ := mem_topSet.mp hj
      have : j = 0 := funext fun x => (mem_suppBox.mp hs).2 x List.not_mem_nil
      subst this; simp at hg
    rw [hret, htop, hybPi_nil]; simp
  | cons i l ih =>
    intro hl k hK f hf M hM
    have hi : i ∉ l := (List.nodup_cons.mp hl).1
    have hl' : l.Nodup := (List.nodup_cons.mp hl).2
    have hfa : ∀ a, a < k + 2 → SmoothBdd (4 * k + 4 - 2 * a) ((pderiv i)^[2 * a] f) :=
      fun a ha => hf.iterate' (by omega) i
    -- The first remainder: `|∂_i^{2k+4} f| ≤ M (update 0 i (k+2))`.
    have hMtop : ∀ x, |(pderiv i)^[2 * k + 4] f x| ≤ M (update (0 : ι → ℕ) i (k + 2)) := by
      intro x
      have := hM _ (single_mem_topSet hK i l) x
      rwa [dEven_cons_update hi, dEven_zero, show 2 * (k + 2) = 2 * k + 4 by ring] at this
    -- Step 1: integrate out coordinate `i` and compare on every coordinate line.
    have step1 : |∫ x, f x ∂hybPi (i :: l) -
        ∑ a ∈ range (k + 2), ecoef a * ∫ x, (pderiv i)^[2 * a] f x ∂hybPi l| ≤
          2 * M (update (0 : ι → ℕ) i (k + 2)) := by
      rw [integral_hybPi_cons hf.continuous hf.bdd]
      have hRa : ∀ a ∈ range (k + 2), ∫ x, (pderiv i)^[2 * a] f x ∂hybPi l =
          ∫ x, (∫ t, (pderiv i)^[2 * a] f (update x i t) ∂radReal) ∂hybPi l := by
        intro a ha
        have h := hfa a (by simpa using ha)
        exact (integral_hybPi_rad hi h.continuous h.bdd).symm
      rw [sum_congr rfl (fun a ha => by rw [hRa a ha])]
      have hGint := integrable_hybPi_slice i l (gaussianReal 0 1) hf.continuous hf.bdd
      have hRint : ∀ a ∈ range (k + 2), Integrable (fun x => ecoef a *
          ∫ t, (pderiv i)^[2 * a] f (update x i t) ∂radReal) (hybPi l) := by
        intro a ha
        have h := hfa a (by simpa using ha)
        exact (integrable_hybPi_slice i l radReal h.continuous h.bdd).const_mul _
      have e : ∫ x, (∫ t, f (update x i t) ∂gaussianReal 0 1) ∂hybPi l -
          ∑ a ∈ range (k + 2), ecoef a *
            ∫ x, (∫ t, (pderiv i)^[2 * a] f (update x i t) ∂radReal) ∂hybPi l =
          ∫ x, ((∫ t, f (update x i t) ∂gaussianReal 0 1) -
            ∑ a ∈ range (k + 2), ecoef a *
              ∫ t, (pderiv i)^[2 * a] f (update x i t) ∂radReal) ∂hybPi l := by
        rw [integral_sub hGint (integrable_finsetSum _ hRint), integral_finsetSum _ hRint]
        simp_rw [integral_const_mul]
      rw [e]
      have h := norm_integral_le_of_norm_le_const (μ := hybPi l)
        (ae_of_all _ fun x => (Real.norm_eq_abs _).symm ▸ slice_compare hf i _ hMtop x)
      simpa using h
    -- Step 2: expand every retained term in the remaining coordinates.
    set err : ℕ → ℝ := fun a => ∫ x, (pderiv i)^[2 * a] f x ∂hybPi l -
      ∑ j ∈ retSet K l (k - (a - 1)), ecoefM j * ∫ x, dEven l j ((pderiv i)^[2 * a] f) x ∂radPi ι
      with herr
    set T : ℕ → ℝ := fun a => if a = 1 then 0 else
      ∑ j ∈ topSet K l (k - (a - 1)), M (update j i a) with hT
    have step2 : ∀ a ∈ range (k + 2), |ecoef a * err a| ≤ 2 * T a := by
      intro a ha
      simp only [mem_range] at ha
      by_cases ha1 : a = 1
      · subst ha1; simp [hT]
      · have hIH := ih hl' (k - (a - 1)) (by omega) ((pderiv i)^[2 * a] f)
          ((hfa a ha).mono (by omega)) (fun j => M (update j i a))
          (fun j hj x => by
            have := hM _ (update_mem_topSet hi hj (by omega) ha1 (by omega) rfl) x
            rwa [dEven_cons_update hi] at this)
        rw [abs_mul]
        calc |ecoef a| * |err a| ≤ 1 * |err a| :=
              mul_le_mul_of_nonneg_right (abs_ecoef_le_one a) (abs_nonneg _)
          _ ≤ 2 * T a := by rw [one_mul]; simpa [hT, ha1] using hIH
    -- Step 3: reassemble the multi-index sums.
    have hC1 : ∑ j ∈ retSet K (i :: l) k, ecoefM j * ∫ x, dEven (i :: l) j f x ∂radPi ι =
        ∑ a ∈ range (k + 2), ecoef a * ∑ j ∈ retSet K l (k - (a - 1)),
          ecoefM j * ∫ x, dEven l j ((pderiv i)^[2 * a] f) x ∂radPi ι := by
      apply sum_retSet_cons (by omega) hi
      intro j hj a
      have hj0 : j i = 0 := (mem_suppBox.mp hj).2 i hi
      rw [ecoefM_update hj0, dEven_cons_update hi]
      ring
    have hC2 := sum_topSet_cons hK hi M
    rw [hC1, hC2]
    have e : ∫ x, f x ∂hybPi (i :: l) - ∑ a ∈ range (k + 2), ecoef a *
        ∑ j ∈ retSet K l (k - (a - 1)),
          ecoefM j * ∫ x, dEven l j ((pderiv i)^[2 * a] f) x ∂radPi ι =
        (∫ x, f x ∂hybPi (i :: l) -
          ∑ a ∈ range (k + 2), ecoef a * ∫ x, (pderiv i)^[2 * a] f x ∂hybPi l) +
        ∑ a ∈ range (k + 2), ecoef a * err a := by
      simp only [herr, mul_sub, sum_sub_distrib]
      ring
    rw [e]
    calc _ ≤ |∫ x, f x ∂hybPi (i :: l) -
          ∑ a ∈ range (k + 2), ecoef a * ∫ x, (pderiv i)^[2 * a] f x ∂hybPi l| +
          |∑ a ∈ range (k + 2), ecoef a * err a| := abs_add_le _ _
      _ ≤ 2 * M (update (0 : ι → ℕ) i (k + 2)) + ∑ a ∈ range (k + 2), 2 * T a := by
          refine add_le_add step1 ((abs_sum_le_sum_abs _ _).trans (sum_le_sum step2))
      _ = 2 * (∑ a ∈ range (k + 2), T a + M (update (0 : ι → ℕ) i (k + 2))) := by
          rw [← mul_sum]; ring

/-- The remainder-free index set of (E4): admissible multi-indices (entries `0` or `≥ 2`) of
grade `≤ k`. (Entries are automatically `≤ k + 1`; see `mem_retIdx`.) -/
def retIdx (k : ℕ) : Finset (ι → ℕ) :=
  (Fintype.piFinset fun _ => range (k + 3)).filter fun j => (∀ i, j i ≠ 1) ∧ grade j ≤ k

/-- The remainder index set of (E4): admissible multi-indices of grade exactly `k + 1`.
(Entries are automatically `≤ k + 2`; see `mem_topIdx`.) -/
def topIdx (k : ℕ) : Finset (ι → ℕ) :=
  (Fintype.piFinset fun _ => range (k + 3)).filter fun j => (∀ i, j i ≠ 1) ∧ grade j = k + 1

omit [DecidableEq ι] in
theorem le_grade_add_one (j : ι → ℕ) (i : ι) : j i ≤ grade j + 1 := by
  have : j i - 1 ≤ grade j := by
    unfold grade
    exact single_le_sum (f := fun x => j x - 1) (fun _ _ => Nat.zero_le _) (mem_univ i)
  omega

/-- `j ∈ retIdx k` iff `j` has no entry `1` and grade `≤ k`. -/
theorem mem_retIdx {k : ℕ} {j : ι → ℕ} : j ∈ retIdx k ↔ (∀ i, j i ≠ 1) ∧ grade j ≤ k := by
  simp only [retIdx, mem_filter, Fintype.mem_piFinset, mem_range, and_iff_right_iff_imp]
  intro h i
  have := le_grade_add_one j i
  omega

/-- `j ∈ topIdx k` iff `j` has no entry `1` and grade `k + 1`. -/
theorem mem_topIdx {k : ℕ} {j : ι → ℕ} : j ∈ topIdx k ↔ (∀ i, j i ≠ 1) ∧ grade j = k + 1 := by
  simp only [topIdx, mem_filter, Fintype.mem_piFinset, mem_range, and_iff_right_iff_imp]
  intro h i
  have := le_grade_add_one j i
  omega

theorem retSet_eq_retIdx {l : List ι} (hcov : ∀ i, i ∈ l) (k : ℕ) :
    retSet (k + 3) l k = retIdx k := by
  ext j
  simp [retSet, retIdx, suppBox, hcov]

theorem topSet_eq_topIdx {l : List ι} (hcov : ∀ i, i ∈ l) (k : ℕ) :
    topSet (k + 3) l k = topIdx k := by
  ext j
  simp [topSet, topIdx, suppBox, hcov]

/-- **The comparison (E4)** with explicit constant. Let `l` enumerate the coordinates (without
repetition) and `f ∈ C^{4k+4}` with bounded partial derivatives of order `≤ 4k+4`. If
`|∂^{2j} f| ≤ M_j` everywhere for every admissible `j` of grade `k + 1`, then
`|𝖦 f - Σ_{|j|_g ≤ k} c_j 𝖱 ∂^{2j} f| ≤ 2 Σ_{|j|_g = k+1} M_j`. Here `𝖦 = ∫ · d(gaussPi ι)`,
`𝖱 = ∫ · d(radPi ι)`, `∂^{2j} = dEven l j` and `c_j = ecoefM j`. -/
theorem gauss_rad_expansion (k : ℕ) {l : List ι} (hl : l.Nodup) (hcov : ∀ i, i ∈ l)
    {f : (ι → ℝ) → ℝ} (hf : SmoothBdd (4 * k + 4) f) (M : (ι → ℕ) → ℝ)
    (hM : ∀ j ∈ topIdx k, ∀ x, |dEven l j f x| ≤ M j) :
    |∫ x, f x ∂gaussPi ι - ∑ j ∈ retIdx k, ecoefM j * ∫ x, dEven l j f x ∂radPi ι| ≤
      2 * ∑ j ∈ topIdx k, M j := by
  have h := hybrid_expansion (k + 3) l hl k le_rfl f hf M
    (fun j hj x => hM j (topSet_eq_topIdx hcov k ▸ hj) x)
  rwa [hybPi_of_forall_mem hcov, retSet_eq_retIdx hcov, topSet_eq_topIdx hcov] at h

/-- **(E4), equation form**: `𝖦 f = Σ_{|j|_g ≤ k} c_j 𝖱 ∂^{2j} f + 𝓔` with
`|𝓔| ≤ 2 Σ_{|j|_g = k+1} M_j`. -/
theorem gauss_rad_expansion_eq (k : ℕ) {l : List ι} (hl : l.Nodup) (hcov : ∀ i, i ∈ l)
    {f : (ι → ℝ) → ℝ} (hf : SmoothBdd (4 * k + 4) f) (M : (ι → ℕ) → ℝ)
    (hM : ∀ j ∈ topIdx k, ∀ x, |dEven l j f x| ≤ M j) :
    ∃ E : ℝ, ∫ x, f x ∂gaussPi ι =
        ∑ j ∈ retIdx k, ecoefM j * ∫ x, dEven l j f x ∂radPi ι + E ∧
      |E| ≤ 2 * ∑ j ∈ topIdx k, M j :=
  ⟨_, by ring, gauss_rad_expansion k hl hcov hf M hM⟩

end BiluLinial.Tight
