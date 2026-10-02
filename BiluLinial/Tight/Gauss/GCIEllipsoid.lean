/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.Gauss.GCIRoyen

/-!
# Gaussian correlation monotonicity for two centred ellipsoids

Nodes of the GCI subtree (`docs/tight/GCI_PLAN.md`):

* `setOf_quadForm_le_eq_iInter` (GCI-SLAB): for `A ⪰ 0` and `t ≥ 0`, the (possibly degenerate)
  ellipsoid `{x | xᵀAx ≤ t}` is the intersection of the slabs
  `{x | |(A y)·x| ≤ √(t yᵀAy)}` over rational `y`.
* `ellipsoid_pair_monotoneOn` (GCI-E1): `s ↦ P(Xᵀ A X ≤ t ∧ Yₛᵀ B Yₛ ≤ u)` is monotone on
  `[0, 1]` (Royen's theorem for boxes, `royen_box_monotoneOn`, and continuity from above).
* `clipped_pair_monotoneOn` (GCI-E2): `s ↦ 𝔼 α(X)^p β(Yₛ)^p` is monotone on `[0, 1]`, where
  `α(x) = (1 - xᵀAx)₊`, `β(x) = (1 - xᵀBx)₊` (layer-cake formula).
-/

@[expose] public section

namespace BiluLinial.Tight

open MeasureTheory ProbabilityTheory Matrix Real Filter Topology
open scoped MatrixOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[fun_prop]
theorem continuous_gX : Continuous (gX : (ι ⊕ ι → ℝ) → ι → ℝ) := by
  unfold gX; fun_prop

@[fun_prop]
theorem continuous_gY (s : ℝ) : Continuous (gY s : (ι ⊕ ι → ℝ) → ι → ℝ) := by
  unfold gY; fun_prop

/-- The slab supporting the ellipsoid `{x | xᵀAx ≤ t}` in the direction `A y`. -/
noncomputable def quadSlab (A : Matrix ι ι ℝ) (t : ℝ) (y : ι → ℝ) : Set (ι → ℝ) :=
  {x | |(A *ᵥ y) ⬝ᵥ x| ≤ √(t * (y ⬝ᵥ (A *ᵥ y)))}

/-- Cauchy–Schwarz for a PSD form: `((A y)·x)² ≤ (yᵀAy)(xᵀAx)`. -/
theorem sq_mulVec_dotProduct_le (A : Matrix ι ι ℝ) (hA : A.PosSemidef) (x y : ι → ℝ) :
    ((A *ᵥ y) ⬝ᵥ x) ^ 2 ≤ (y ⬝ᵥ (A *ᵥ y)) * (x ⬝ᵥ (A *ᵥ x)) := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at hB
  have hform : ∀ u v : ι → ℝ, (A *ᵥ u) ⬝ᵥ v = (B *ᵥ u) ⬝ᵥ (B *ᵥ v) := by
    intro u v
    rw [hB, ← mulVec_mulVec, dotProduct_comm, dotProduct_mulVec, vecMul_transpose,
      dotProduct_comm]
  have hform' : ∀ u : ι → ℝ, u ⬝ᵥ (A *ᵥ u) = (B *ᵥ u) ⬝ᵥ (B *ᵥ u) := by
    intro u
    rw [dotProduct_comm, hform]
  rw [hform, hform', hform']
  simpa [dotProduct, sq] using
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => (B *ᵥ y) i) (fun i => (B *ᵥ x) i)

omit [DecidableEq ι] in
theorem quadForm_nonneg (A : Matrix ι ι ℝ) (hA : A.PosSemidef) (x : ι → ℝ) :
    0 ≤ x ⬝ᵥ (A *ᵥ x) := by
  simpa using hA.dotProduct_mulVec_nonneg x

/-- **GCI-SLAB.** A centred (possibly degenerate) ellipsoid is the intersection of its
supporting slabs in the rational directions `A y`. -/
theorem setOf_quadForm_le_eq_iInter (A : Matrix ι ι ℝ) (hA : A.PosSemidef) {t : ℝ}
    (ht : 0 ≤ t) :
    {x | x ⬝ᵥ (A *ᵥ x) ≤ t} = ⋂ y : ι → ℚ, quadSlab A t (fun i => (y i : ℝ)) := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_iInter, quadSlab]
  constructor
  · intro hx y
    apply Real.abs_le_sqrt
    calc ((A *ᵥ fun i => (y i : ℝ)) ⬝ᵥ x) ^ 2
        ≤ ((fun i => (y i : ℝ)) ⬝ᵥ (A *ᵥ fun i => (y i : ℝ))) * (x ⬝ᵥ (A *ᵥ x)) :=
          sq_mulVec_dotProduct_le A hA x _
      _ ≤ ((fun i => (y i : ℝ)) ⬝ᵥ (A *ᵥ fun i => (y i : ℝ))) * t :=
          mul_le_mul_of_nonneg_left hx (quadForm_nonneg A hA _)
      _ = t * ((fun i => (y i : ℝ)) ⬝ᵥ (A *ᵥ fun i => (y i : ℝ))) := mul_comm _ _
  · intro hx
    by_contra hlt
    push Not at hlt
    set q := x ⬝ᵥ (A *ᵥ x) with hq
    have hq0 : 0 < q := lt_of_le_of_lt ht hlt
    let h : (ι → ℝ) → ℝ := fun y => |(A *ᵥ y) ⬝ᵥ x| - √(t * (y ⬝ᵥ (A *ᵥ y)))
    have hcont : Continuous h := by fun_prop
    have hx0 : 0 < h x := by
      have hsym : (A *ᵥ x) ⬝ᵥ x = q := by rw [hq, dotProduct_comm]
      simp only [h, hsym, abs_of_pos hq0]
      have : √(t * q) < q := by
        rw [Real.sqrt_lt' hq0]
        nlinarith
      linarith
    have hdense : DenseRange (fun (y : ι → ℚ) (i : ι) => (y i : ℝ)) :=
      DenseRange.piMap fun _ => Rat.denseRange_cast
    obtain ⟨y, hy⟩ := hdense.exists_mem_open (isOpen_lt continuous_const hcont) ⟨x, hx0⟩
    have := hx y
    simp only [Set.mem_ofPred_eq, h] at hy
    linarith

/-- **GCI-E1.** Royen's monotonicity for a pair of centred ellipsoids. -/
theorem ellipsoid_pair_monotoneOn (A B : Matrix ι ι ℝ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (t u : ℝ) :
    MonotoneOn (fun s => (gaussPi (ι ⊕ ι)).real
      {G | gX G ⬝ᵥ (A *ᵥ gX G) ≤ t ∧ gY s G ⬝ᵥ (B *ᵥ gY s G) ≤ u}) (Set.Icc 0 1) := by
  by_cases htu : t < 0 ∨ u < 0
  · have hempty : ∀ s : ℝ,
        {G : ι ⊕ ι → ℝ | gX G ⬝ᵥ (A *ᵥ gX G) ≤ t ∧ gY s G ⬝ᵥ (B *ᵥ gY s G) ≤ u} = ∅ := by
      intro s
      ext G
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      rcases htu with h | h
      · intro h1 _; linarith [quadForm_nonneg A hA (gX G)]
      · intro _ h2; linarith [quadForm_nonneg B hB (gY s G)]
    intro s _ s' _ _
    simp only [hempty, measureReal_empty, le_refl]
  push Not at htu
  obtain ⟨ht, hu⟩ := htu
  obtain ⟨e, he⟩ := exists_surjective_nat (ι → ℚ)
  let yv : ℕ → ι → ℝ := fun k i => (e k i : ℝ)
  let P₁ : (N : ℕ) → Matrix (Fin N) ι ℝ := fun N => Matrix.of fun k i => (A *ᵥ yv k) i
  let P₂ : (N : ℕ) → Matrix (Fin N) ι ℝ := fun N => Matrix.of fun k i => (B *ᵥ yv k) i
  let c : (N : ℕ) → Fin N → ℝ := fun N k => √(t * (yv k ⬝ᵥ (A *ᵥ yv k)))
  let d : (N : ℕ) → Fin N → ℝ := fun N k => √(u * (yv k ⬝ᵥ (B *ᵥ yv k)))
  let S : ℕ → ℝ → Set (ι ⊕ ι → ℝ) := fun N s =>
    {G | (∀ k, |(P₁ N *ᵥ gX G) k| ≤ c N k) ∧ ∀ k, |(P₂ N *ᵥ gY s G) k| ≤ d N k}
  have hP₁ : ∀ N (k : Fin N) (v : ι → ℝ), (P₁ N *ᵥ v) k = (A *ᵥ yv k) ⬝ᵥ v := fun _ _ _ => rfl
  have hP₂ : ∀ N (k : Fin N) (v : ι → ℝ), (P₂ N *ᵥ v) k = (B *ᵥ yv k) ⬝ᵥ v := fun _ _ _ => rfl
  have hSmono : ∀ N, MonotoneOn (fun s => (gaussPi (ι ⊕ ι)).real (S N s)) (Set.Icc 0 1) :=
    fun N => royen_box_monotoneOn (P₁ N) (P₂ N) (c N) (d N)
  have hSanti : ∀ s, Antitone fun N => S N s := by
    intro s N N' hNN' G hG
    refine ⟨fun k => ?_, fun k => ?_⟩
    · have := hG.1 ⟨k, lt_of_lt_of_le k.2 hNN'⟩
      simpa [hP₁, c] using this
    · have := hG.2 ⟨k, lt_of_lt_of_le k.2 hNN'⟩
      simpa [hP₂, d] using this
  have hSinter : ∀ s, (⋂ N, S N s) =
      {G | gX G ⬝ᵥ (A *ᵥ gX G) ≤ t ∧ gY s G ⬝ᵥ (B *ᵥ gY s G) ≤ u} := by
    intro s
    have hA' := setOf_quadForm_le_eq_iInter A hA ht
    have hB' := setOf_quadForm_le_eq_iInter B hB hu
    ext G
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    have eA : gX G ⬝ᵥ (A *ᵥ gX G) ≤ t ↔ ∀ k, gX G ∈ quadSlab A t (yv k) := by
      have := congrArg (gX G ∈ ·) hA'
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, eq_iff_iff] at this
      rw [this]
      exact ⟨fun h k => h (e k), fun h y => by obtain ⟨k, rfl⟩ := he y; exact h k⟩
    have eB : gY s G ⬝ᵥ (B *ᵥ gY s G) ≤ u ↔ ∀ k, gY s G ∈ quadSlab B u (yv k) := by
      have := congrArg (gY s G ∈ ·) hB'
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, eq_iff_iff] at this
      rw [this]
      exact ⟨fun h k => h (e k), fun h y => by obtain ⟨k, rfl⟩ := he y; exact h k⟩
    rw [eA, eB]
    simp only [S, Set.mem_ofPred_eq, hP₁, hP₂, quadSlab]
    constructor
    · intro h
      exact ⟨fun k => (h (k + 1)).1 ⟨k, Nat.lt_succ_self k⟩,
        fun k => (h (k + 1)).2 ⟨k, Nat.lt_succ_self k⟩⟩
    · intro h N
      exact ⟨fun k => h.1 k, fun k => h.2 k⟩
  have hmeasS : ∀ N s, MeasurableSet (S N s) := by
    intro N s
    simp only [S, Set.setOf_and, Set.setOf_forall]
    refine MeasurableSet.inter (MeasurableSet.iInter fun k => measurableSet_le ?_ ?_)
      (MeasurableSet.iInter fun k => measurableSet_le ?_ ?_)
    all_goals first
      | exact measurable_const
      | fun_prop
  have hlim : ∀ s, Tendsto (fun N => (gaussPi (ι ⊕ ι)).real (S N s)) atTop
      (𝓝 ((gaussPi (ι ⊕ ι)).real
        {G | gX G ⬝ᵥ (A *ᵥ gX G) ≤ t ∧ gY s G ⬝ᵥ (B *ᵥ gY s G) ≤ u})) := by
    intro s
    rw [← hSinter s]
    have h := tendsto_measure_iInter_atTop (μ := gaussPi (ι ⊕ ι))
      (fun N => (hmeasS N s).nullMeasurableSet) (hSanti s) ⟨0, measure_ne_top _ _⟩
    exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h
  intro s hs s' hs' hss'
  exact le_of_tendsto_of_tendsto (hlim s) (hlim s')
    (Eventually.of_forall fun N => hSmono N hs hs' hss')

/-- The clipped power `x ↦ ((1 - xᵀAx)₊)^p`. -/
noncomputable def gciClipPow (A : Matrix ι ι ℝ) (p : ℕ) (x : ι → ℝ) : ℝ :=
  max (1 - x ⬝ᵥ (A *ᵥ x)) 0 ^ p

omit [DecidableEq ι] in
theorem gciClipPow_mem_Icc (A : Matrix ι ι ℝ) (hA : A.PosSemidef) (p : ℕ) (x : ι → ℝ) :
    gciClipPow A p x ∈ Set.Icc (0 : ℝ) 1 := by
  have hq := quadForm_nonneg A hA x
  have h0 : 0 ≤ max (1 - x ⬝ᵥ (A *ᵥ x)) 0 := le_max_right _ _
  have h1 : max (1 - x ⬝ᵥ (A *ᵥ x)) 0 ≤ 1 := max_le (by linarith) zero_le_one
  exact ⟨pow_nonneg h0 p, pow_le_one₀ h0 h1⟩

omit [DecidableEq ι] in
@[fun_prop]
theorem continuous_gciClipPow (A : Matrix ι ι ℝ) (p : ℕ) : Continuous (gciClipPow A p) := by
  unfold gciClipPow; fun_prop

omit [DecidableEq ι] in
/-- Superlevel sets of the clipped power are ellipsoids. -/
theorem le_gciClipPow_iff (A : Matrix ι ι ℝ) {p : ℕ} (hp : 1 ≤ p) {a : ℝ} (ha : 0 < a)
    (x : ι → ℝ) : a ≤ gciClipPow A p x ↔ x ⬝ᵥ (A *ᵥ x) ≤ 1 - a ^ (1 / (p : ℝ)) := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  set m := max (1 - x ⬝ᵥ (A *ᵥ x)) 0 with hm
  have hm0 : 0 ≤ m := le_max_right _ _
  have hroot : a ≤ m ^ p ↔ a ^ (1 / (p : ℝ)) ≤ m := by
    rw [← Real.rpow_natCast m p]
    constructor
    · intro h
      calc a ^ (1 / (p : ℝ)) ≤ (m ^ (p : ℝ)) ^ (1 / (p : ℝ)) :=
            Real.rpow_le_rpow ha.le h (by positivity)
        _ = m := by rw [← Real.rpow_mul hm0, mul_one_div_cancel hp'.ne', Real.rpow_one]
    · intro h
      calc a = (a ^ (1 / (p : ℝ))) ^ (p : ℝ) := by
            rw [← Real.rpow_mul ha.le, one_div_mul_cancel hp'.ne', Real.rpow_one]
        _ ≤ m ^ (p : ℝ) := Real.rpow_le_rpow (by positivity) h hp'.le
  have hpos : 0 < a ^ (1 / (p : ℝ)) := Real.rpow_pos_of_pos ha _
  rw [gciClipPow, ← hm, hroot, hm]
  constructor
  · intro h
    rcases le_total (1 - x ⬝ᵥ (A *ᵥ x)) 0 with h' | h'
    · rw [max_eq_right h'] at h; linarith
    · rw [max_eq_left h'] at h; linarith
  · intro h
    exact le_max_of_le_left (by linarith)

/-- The step approximation `⌊n v⌋ / n` written as a sum of indicators. -/
noncomputable def stepSum (n : ℕ) (v : ℝ) : ℝ :=
  (∑ j ∈ Finset.Icc 1 n, if (j : ℝ) / n ≤ v then (1 : ℝ) else 0) / n

theorem stepSum_eq_floor {n : ℕ} (hn : 1 ≤ n) {v : ℝ} (hv : v ∈ Set.Icc (0 : ℝ) 1) :
    stepSum n v = (⌊n * v⌋₊ : ℝ) / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  unfold stepSum
  congr 1
  rw [Finset.sum_boole]
  have hfl : ⌊(n : ℝ) * v⌋₊ ≤ n := by
    apply Nat.floor_le_of_le
    calc (n : ℝ) * v ≤ n * 1 := by gcongr; exact hv.2
      _ = n := mul_one _
  have : Finset.filter (fun j : ℕ => (j : ℝ) / n ≤ v) (Finset.Icc 1 n) =
      Finset.Icc 1 ⌊(n : ℝ) * v⌋₊ := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_Icc]
    rw [div_le_iff₀ hn', mul_comm, Nat.le_floor_iff (mul_nonneg hn'.le hv.1)]
    constructor
    · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, by
        have : (j : ℝ) ≤ n := le_trans h2 (by
          calc (n : ℝ) * v ≤ n * 1 := by gcongr; exact hv.2
            _ = n := mul_one _)
        exact_mod_cast this⟩, h2⟩
  rw [this, Nat.card_Icc]
  simp

theorem abs_stepSum_sub_le {n : ℕ} (hn : 1 ≤ n) {v : ℝ} (hv : v ∈ Set.Icc (0 : ℝ) 1) :
    |stepSum n v - v| ≤ 1 / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [stepSum_eq_floor hn hv]
  have h1 : (⌊(n : ℝ) * v⌋₊ : ℝ) ≤ n * v := Nat.floor_le (by positivity [hv.1])
  have h2 : (n : ℝ) * v < ⌊(n : ℝ) * v⌋₊ + 1 := Nat.lt_floor_add_one _
  have key1 : (⌊(n : ℝ) * v⌋₊ : ℝ) / n ≤ v := by rw [div_le_iff₀ hn']; linarith
  have key2 : v < (⌊(n : ℝ) * v⌋₊ : ℝ) / n + 1 / n := by
    rw [← add_div, lt_div_iff₀ hn']; linarith
  have key3 : 0 ≤ 1 / (n : ℝ) := by positivity
  rw [abs_le]
  constructor <;> linarith

theorem stepSum_mem_Icc {n : ℕ} (hn : 1 ≤ n) {v : ℝ} (hv : v ∈ Set.Icc (0 : ℝ) 1) :
    stepSum n v ∈ Set.Icc (0 : ℝ) 1 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [stepSum_eq_floor hn hv]
  constructor
  · positivity
  · rw [div_le_one hn']
    calc (⌊(n : ℝ) * v⌋₊ : ℝ) ≤ n * v := Nat.floor_le (by positivity [hv.1])
      _ ≤ n * 1 := by gcongr; exact hv.2
      _ = n := mul_one _

/-- **GCI-E2.** `s ↦ 𝔼 α(X)^p β(Yₛ)^p` is monotone on `[0, 1]`. -/
theorem clipped_pair_monotoneOn (A B : Matrix ι ι ℝ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (p : ℕ) (hp : 1 ≤ p) :
    MonotoneOn (fun s => ∫ G, gciClipPow A p (gX G) * gciClipPow B p (gY s G) ∂gaussPi (ι ⊕ ι))
      (Set.Icc 0 1) := by
  set γ := gaussPi (ι ⊕ ι)
  set f := gciClipPow A p
  set g := gciClipPow B p
  -- the step approximations
  set H : ℕ → ℝ → ℝ := fun n s => ∫ G, stepSum n (f (gX G)) * stepSum n (g (gY s G)) ∂γ
  have hmeasf : ∀ (n j : ℕ), MeasurableSet {G : ι ⊕ ι → ℝ | (j : ℝ) / n ≤ f (gX G)} :=
    fun n j => measurableSet_le measurable_const (by fun_prop)
  have hmeasg : ∀ (n l : ℕ) (s : ℝ), MeasurableSet {G : ι ⊕ ι → ℝ | (l : ℝ) / n ≤ g (gY s G)} :=
    fun n l s => measurableSet_le measurable_const (by fun_prop)
  have hHeq : ∀ n s, H n s = (∑ j ∈ Finset.Icc 1 n, ∑ l ∈ Finset.Icc 1 n,
      γ.real ({G | (j : ℝ) / n ≤ f (gX G)} ∩ {G | (l : ℝ) / n ≤ g (gY s G)})) / (n * n) := by
    intro n s
    have hpt : ∀ G, stepSum n (f (gX G)) * stepSum n (g (gY s G)) =
        (∑ j ∈ Finset.Icc 1 n, ∑ l ∈ Finset.Icc 1 n,
          ({G | (j : ℝ) / n ≤ f (gX G)} ∩ {G | (l : ℝ) / n ≤ g (gY s G)}).indicator 1 G) /
            (n * n) := by
      intro G
      simp only [stepSum, div_mul_div_comm, Finset.sum_mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
      by_cases hj : (j : ℝ) / n ≤ f (gX G) <;> by_cases hl : (l : ℝ) / n ≤ g (gY s G) <;>
        simp [Set.indicator, hj, hl]
    simp only [H, hpt]
    rw [integral_div, integral_finsetSum]
    · congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_finsetSum]
      · exact Finset.sum_congr rfl fun l _ =>
          integral_indicator_one ((hmeasf n j).inter (hmeasg n l s))
      · exact fun l _ => (integrable_const (1 : ℝ)).indicator ((hmeasf n j).inter (hmeasg n l s))
    · intro j _
      exact integrable_finsetSum _ fun l _ =>
        (integrable_const (1 : ℝ)).indicator ((hmeasf n j).inter (hmeasg n l s))
  have hHmono : ∀ n, MonotoneOn (H n) (Set.Icc 0 1) := by
    intro n s hs s' hs' hss'
    rw [hHeq, hHeq]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    refine Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun l hl => ?_
    have hj0 : (0 : ℝ) < (j : ℝ) / n := by
      have := (Finset.mem_Icc.mp hj).1
      have : 1 ≤ n := le_trans this (Finset.mem_Icc.mp hj).2
      positivity
    have hl0 : (0 : ℝ) < (l : ℝ) / n := by
      have := (Finset.mem_Icc.mp hl).1
      have : 1 ≤ n := le_trans this (Finset.mem_Icc.mp hl).2
      positivity
    have hset : ∀ σ : ℝ, {G : ι ⊕ ι → ℝ | (j : ℝ) / n ≤ f (gX G)} ∩
        {G | (l : ℝ) / n ≤ g (gY σ G)} = {G | gX G ⬝ᵥ (A *ᵥ gX G) ≤ 1 - ((j : ℝ) / n) ^ (1 / (p : ℝ))
          ∧ gY σ G ⬝ᵥ (B *ᵥ gY σ G) ≤ 1 - ((l : ℝ) / n) ^ (1 / (p : ℝ))} := by
      intro σ
      ext G
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, f, g, le_gciClipPow_iff A hp hj0,
        le_gciClipPow_iff B hp hl0]
    rw [hset, hset]
    exact ellipsoid_pair_monotoneOn A B hA hB _ _ hs hs' hss'
  have hconv : ∀ s, Tendsto (fun n => H n s) atTop
      (𝓝 (∫ G, f (gX G) * g (gY s G) ∂γ)) := by
    intro s
    have hbound : ∀ n : ℕ, 1 ≤ n → |H n s - ∫ G, f (gX G) * g (gY s G) ∂γ| ≤ 2 / n := by
      intro n hn
      have hint1 : Integrable (fun G => stepSum n (f (gX G)) * stepSum n (g (gY s G))) γ := by
        refine (integrable_const (1 : ℝ)).mono' ?_ (Eventually.of_forall fun G => ?_)
        · have hstep : Measurable (stepSum n) := by
            unfold stepSum
            refine Measurable.div_const (Finset.measurable_sum _ fun j _ => ?_) _
            exact Measurable.ite measurableSet_Ici measurable_const measurable_const
          exact ((hstep.comp (by fun_prop : Measurable fun G => f (gX G))).mul
            (hstep.comp (by fun_prop : Measurable fun G => g (gY s G)))).aestronglyMeasurable
        · have h1 := stepSum_mem_Icc hn (gciClipPow_mem_Icc A hA p (gX G))
          have h2 := stepSum_mem_Icc hn (gciClipPow_mem_Icc B hB p (gY s G))
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h1.1 h2.1)]
          nlinarith [h1.1, h1.2, h2.1, h2.2]
      have hint2 : Integrable (fun G => f (gX G) * g (gY s G)) γ := by
        refine (integrable_const (1 : ℝ)).mono' (by fun_prop) (Eventually.of_forall fun G => ?_)
        have h1 := gciClipPow_mem_Icc A hA p (gX G)
        have h2 := gciClipPow_mem_Icc B hB p (gY s G)
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h1.1 h2.1)]
        nlinarith [h1.1, h1.2, h2.1, h2.2]
      simp only [H]
      rw [← integral_sub hint1 hint2]
      calc |∫ G, (stepSum n (f (gX G)) * stepSum n (g (gY s G)) - f (gX G) * g (gY s G)) ∂γ|
          ≤ ∫ G, |stepSum n (f (gX G)) * stepSum n (g (gY s G)) - f (gX G) * g (gY s G)| ∂γ :=
            abs_integral_le_integral_abs
        _ ≤ ∫ _G, (2 / n : ℝ) ∂γ := by
            refine integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
              (integrable_const _) (Eventually.of_forall fun G => ?_)
            dsimp only
            have hf1 := gciClipPow_mem_Icc A hA p (gX G)
            have hg1 := gciClipPow_mem_Icc B hB p (gY s G)
            have hs1 := stepSum_mem_Icc hn hf1
            have hs2 := stepSum_mem_Icc hn hg1
            have e1 := abs_stepSum_sub_le hn hf1
            have e2 := abs_stepSum_sub_le hn hg1
            have : stepSum n (f (gX G)) * stepSum n (g (gY s G)) - f (gX G) * g (gY s G) =
                (stepSum n (f (gX G)) - f (gX G)) * stepSum n (g (gY s G)) +
                  f (gX G) * (stepSum n (g (gY s G)) - g (gY s G)) := by ring
            rw [this]
            calc _ ≤ |(stepSum n (f (gX G)) - f (gX G)) * stepSum n (g (gY s G))| +
                  |f (gX G) * (stepSum n (g (gY s G)) - g (gY s G))| := abs_add_le _ _
              _ ≤ 1 / n * 1 + 1 * (1 / n) := by
                  rw [abs_mul, abs_mul]
                  gcongr
                  · rw [abs_of_nonneg hs2.1]; exact hs2.2
                  · rw [abs_of_nonneg hf1.1]; exact hf1.2
              _ = 2 / n := by ring
        _ = 2 / n := by simp
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero' (g := fun n : ℕ => 2 / (n : ℝ)) (Eventually.of_forall fun n => dist_nonneg)
      ?_ (tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ))
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [Real.dist_eq]
    exact hbound n hn
  intro s hs s' hs' hss'
  exact le_of_tendsto_of_tendsto (hconv s) (hconv s')
    (Eventually.of_forall fun n => hHmono n hs hs' hss')

end BiluLinial.Tight
