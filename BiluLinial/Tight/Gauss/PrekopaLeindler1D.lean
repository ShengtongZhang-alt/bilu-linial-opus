/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import Mathlib

/-!
# The one-dimensional Prékopa–Leindler inequality (midpoint form)

For measurable `f g h : ℝ → ℝ≥0∞` with `f x * g y ≤ h ((x + y) / 2) ^ 2` for all `x y`,
`(∫⁻ f) * (∫⁻ g) ≤ (∫⁻ h) ^ 2`.

The proof goes through the one-dimensional Brunn–Minkowski inequality: for nonempty measurable
`A B ⊆ ℝ` and a set `C` containing all midpoints `(x + y) / 2` with `x ∈ A`, `y ∈ B`,
`volume A + volume B ≤ 2 * volume C` (`volume_add_volume_le_two_mul`). For compact `A`, `B` the
set `C` contains two half-size copies of `A` and `B` that meet in at most one point; the general
case follows by inner regularity. For `f`, `g` normalized to `⨆ f = ⨆ g = 1`, the superlevel sets
at a level `s ∈ (0, 1)` satisfy this midpoint condition, and the layer-cake formula turns the
inequality of volumes into `∫⁻ f + ∫⁻ g ≤ 2 ∫⁻ h`; AM-GM and a rescaling finish the bounded case,
and truncation with monotone convergence removes the boundedness assumption.
-/

@[expose] public section

namespace BiluLinial.Tight

open MeasureTheory Set
open scoped ENNReal NNReal

/-- The midpoint of two reals. -/
lemma real_midpoint_eq (a b : ℝ) : midpoint ℝ a b = (a + b) / 2 := by
  rw [midpoint_eq_smul_add]; simp; ring

/-- `2 * volume ((z ↦ 2 z - c)⁻¹' K) = volume K`. -/
lemma two_mul_volume_preimage_two_mul_sub (c : ℝ) (K : Set ℝ) :
    2 * volume ((fun z : ℝ => 2 * z - c) ⁻¹' K) = volume K := by
  have h1 : (fun z : ℝ => 2 * z - c) ⁻¹' K =
      (fun z : ℝ => 2 * z) ⁻¹' ((fun w => w + (-c)) ⁻¹' K) := by
    ext z; simp only [mem_preimage, sub_eq_add_neg]
  have h2 : (2 : ℝ≥0∞) * ENNReal.ofReal |(2 : ℝ)⁻¹| = 1 := by
    rw [abs_of_pos (by norm_num), ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat,
      ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
  rw [h1, Real.volume_preimage_mul_left two_ne_zero, measure_preimage_add_right, ← mul_assoc, h2,
    one_mul]

/-- One-dimensional Brunn–Minkowski inequality (midpoint form) for nonempty compact sets. -/
lemma volume_add_volume_le_two_mul_of_isCompact {K L C : Set ℝ} (hK : IsCompact K)
    (hL : IsCompact L) (hK0 : K.Nonempty) (hL0 : L.Nonempty)
    (hC : ∀ x ∈ K, ∀ y ∈ L, (x + y) / 2 ∈ C) :
    volume K + volume L ≤ 2 * volume C := by
  have hk : sSup K ∈ K := hK.sSup_mem hK0
  have hl : sInf L ∈ L := hL.sInf_mem hL0
  have hkK : ∀ x ∈ K, x ≤ sSup K := fun x hx => le_csSup hK.bddAbove hx
  have hlL : ∀ y ∈ L, sInf L ≤ y := fun y hy => csInf_le hL.bddBelow hy
  have hPC : (fun z : ℝ => 2 * z - sInf L) ⁻¹' K ⊆ C := by
    intro z hz
    have := hC _ hz _ hl
    rwa [show (2 * z - sInf L + sInf L) / 2 = z by ring] at this
  have hQC : (fun z : ℝ => 2 * z - sSup K) ⁻¹' L ⊆ C := by
    intro z hz
    have := hC _ hk _ hz
    rwa [show (sSup K + (2 * z - sSup K)) / 2 = z by ring] at this
  have hPQ : (fun z : ℝ => 2 * z - sInf L) ⁻¹' K ∩ (fun z : ℝ => 2 * z - sSup K) ⁻¹' L ⊆
      {(sSup K + sInf L) / 2} := by
    rintro z ⟨hzP, hzQ⟩
    have h1 := hkK _ hzP
    have h2 := hlL _ hzQ
    simp only [mem_singleton_iff]
    linarith
  have hQm : MeasurableSet ((fun z : ℝ => 2 * z - sSup K) ⁻¹' L) :=
    (hL.isClosed.preimage (by fun_prop)).measurableSet
  have hsum : volume ((fun z : ℝ => 2 * z - sInf L) ⁻¹' K) +
      volume ((fun z : ℝ => 2 * z - sSup K) ⁻¹' L) ≤ volume C := by
    rw [← measure_union_add_inter _ hQm, measure_mono_null hPQ (measure_singleton _), add_zero]
    exact measure_mono (union_subset hPC hQC)
  calc volume K + volume L
      = 2 * volume ((fun z : ℝ => 2 * z - sInf L) ⁻¹' K) +
          2 * volume ((fun z : ℝ => 2 * z - sSup K) ⁻¹' L) := by
        rw [two_mul_volume_preimage_two_mul_sub, two_mul_volume_preimage_two_mul_sub]
    _ = 2 * (volume ((fun z : ℝ => 2 * z - sInf L) ⁻¹' K) +
          volume ((fun z : ℝ => 2 * z - sSup K) ⁻¹' L)) := (mul_add _ _ _).symm
    _ ≤ 2 * volume C := mul_le_mul' le_rfl hsum

/-- Inner regularity in the form used below: to bound `volume A + x`, it suffices to bound
`volume K + x` for compact `K ⊆ A`. -/
lemma volume_add_le_of_forall_isCompact {A : Set ℝ} (hA : MeasurableSet A) {x c : ℝ≥0∞}
    (h : ∀ K ⊆ A, IsCompact K → volume K + x ≤ c) : volume A + x ≤ c := by
  have hx : x ≤ c := by simpa using h ∅ (empty_subset _) isCompact_empty
  rw [hA.measure_eq_iSup_isCompact, ENNReal.iSup_add]
  refine iSup_le fun K => ?_
  by_cases hKA : K ⊆ A
  · by_cases hK : IsCompact K
    · rw [iSup_pos hKA, iSup_pos hK]
      exact h K hKA hK
    · rw [iSup_pos hKA, iSup_neg hK, ENNReal.bot_eq_zero, zero_add]
      exact hx
  · rw [iSup_neg hKA, ENNReal.bot_eq_zero, zero_add]
    exact hx

/-- One-dimensional Brunn–Minkowski inequality (midpoint form): for nonempty measurable
`A B ⊆ ℝ` and any set `C` containing every midpoint `(x + y) / 2` with `x ∈ A`, `y ∈ B`,
`volume A + volume B ≤ 2 * volume C`. -/
theorem volume_add_volume_le_two_mul {A B C : Set ℝ} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hA0 : A.Nonempty) (hB0 : B.Nonempty)
    (hC : ∀ x ∈ A, ∀ y ∈ B, (x + y) / 2 ∈ C) :
    volume A + volume B ≤ 2 * volume C := by
  obtain ⟨a, ha⟩ := hA0
  obtain ⟨b, hb⟩ := hB0
  refine volume_add_le_of_forall_isCompact hA fun K hKA hK => ?_
  rw [add_comm]
  refine volume_add_le_of_forall_isCompact hB fun L hLB hL => ?_
  rw [add_comm]
  calc volume K + volume L ≤ volume (insert a K) + volume (insert b L) :=
        add_le_add (measure_mono (subset_insert _ _)) (measure_mono (subset_insert _ _))
    _ ≤ 2 * volume C :=
        volume_add_volume_le_two_mul_of_isCompact (hK.insert a) (hL.insert b)
          (insert_nonempty _ _) (insert_nonempty _ _)
          (fun x hx y hy => hC x (insert_subset ha hKA hx) y (insert_subset hb hLB hy))

/-- Layer-cake formula for a measurable function with values in `[0, 1]`. -/
lemma lintegral_eq_setLIntegral_Ioo_meas_lt {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {φ : α → ℝ≥0∞} (hφ : Measurable φ) (h1 : ∀ x, φ x ≤ 1) :
    ∫⁻ x, φ x ∂μ = ∫⁻ s in Ioo (0 : ℝ) 1, μ {x | ENNReal.ofReal s < φ x} := by
  have hfin : ∀ x, φ x ≠ ∞ := fun x => ne_top_of_le_ne_top ENNReal.one_ne_top (h1 x)
  have e1 : ∫⁻ x, φ x ∂μ = ∫⁻ x, ENNReal.ofReal (φ x).toReal ∂μ := by
    congr 1; funext x; rw [ENNReal.ofReal_toReal (hfin x)]
  rw [e1, lintegral_eq_lintegral_meas_lt μ
      (Filter.Eventually.of_forall fun x => ENNReal.toReal_nonneg)
      hφ.ennreal_toReal.aemeasurable,
    ← Ioo_union_Ici_eq_Ioi zero_lt_one,
    lintegral_union measurableSet_Ici
      (Set.disjoint_left.2 fun t ht ht' => (not_le.2 ht.2) ht')]
  have h2 : ∫⁻ t in Ici (1 : ℝ), μ {a | t < (φ a).toReal} = 0 := by
    rw [setLIntegral_congr_fun measurableSet_Ici (g := fun _ => 0), lintegral_zero]
    intro t ht
    have : {a | t < (φ a).toReal} = ∅ := by
      ext a
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
      calc (φ a).toReal ≤ (1 : ℝ≥0∞).toReal := ENNReal.toReal_mono ENNReal.one_ne_top (h1 a)
        _ = 1 := ENNReal.toReal_one
        _ ≤ t := ht
    simp [this]
  rw [h2, add_zero]
  refine setLIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
  congr 1
  ext x
  exact (ENNReal.ofReal_lt_iff_lt_toReal ht.1.le (hfin x)).symm

/-- The superlevel-set measure `s ↦ μ {φ > s}` is measurable. -/
lemma measurable_meas_lt {α : Type*} [MeasurableSpace α] (μ : Measure α) (φ : α → ℝ≥0∞) :
    Measurable fun s : ℝ => μ {x | ENNReal.ofReal s < φ x} := by
  apply Antitone.measurable
  intro s t hst
  apply measure_mono
  intro x hx
  exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hst) hx

/-- Normalized one-dimensional Prékopa–Leindler: if `f, g ≤ 1` both have supremum `1`, then
`∫⁻ f + ∫⁻ g ≤ 2 ∫⁻ h`. -/
lemma lintegral_add_lintegral_le_of_normalized {f g h : ℝ → ℝ≥0∞} (hf : Measurable f)
    (hg : Measurable g) (hh : Measurable h) (hf1 : ∀ x, f x ≤ 1) (hg1 : ∀ x, g x ≤ 1)
    (hfs : ∀ t < 1, ∃ x, t < f x) (hgs : ∀ t < 1, ∃ x, t < g x)
    (hfgh : ∀ x y, f x * g y ≤ h ((x + y) / 2) ^ 2) :
    (∫⁻ x, f x) + (∫⁻ x, g x) ≤ 2 * ∫⁻ x, h x := by
  have hh' : Measurable fun z => min (h z) 1 := hh.min measurable_const
  have level : ∀ s ∈ Ioo (0 : ℝ) 1,
      volume {x | ENNReal.ofReal s < f x} + volume {x | ENNReal.ofReal s < g x} ≤
        2 * volume {x | ENNReal.ofReal s < min (h x) 1} := by
    intro s hs
    have hs1 : ENNReal.ofReal s < 1 := by
      rw [← ENNReal.ofReal_one]; exact (ENNReal.ofReal_lt_ofReal_iff one_pos).2 hs.2
    refine volume_add_volume_le_two_mul (measurableSet_lt measurable_const hf)
      (measurableSet_lt measurable_const hg) (hfs _ hs1) (hgs _ hs1) ?_
    intro x hx y hy
    simp only [mem_ofPred_eq] at hx hy ⊢
    refine lt_min ?_ hs1
    by_contra hcon
    have h1 : ENNReal.ofReal s * ENNReal.ofReal s < f x * g y := ENNReal.mul_lt_mul hx hy
    have h2 : h ((x + y) / 2) ^ 2 ≤ ENNReal.ofReal s ^ 2 :=
      pow_le_pow_left₀ zero_le (not_lt.1 hcon) 2
    have h3 := h1.trans_le ((hfgh x y).trans h2)
    rw [sq] at h3
    exact lt_irrefl _ h3
  rw [lintegral_eq_setLIntegral_Ioo_meas_lt volume hf hf1,
    lintegral_eq_setLIntegral_Ioo_meas_lt volume hg hg1]
  calc (∫⁻ s in Ioo (0 : ℝ) 1, volume {x | ENNReal.ofReal s < f x}) +
        (∫⁻ s in Ioo (0 : ℝ) 1, volume {x | ENNReal.ofReal s < g x})
      = ∫⁻ s in Ioo (0 : ℝ) 1, (volume {x | ENNReal.ofReal s < f x} +
          volume {x | ENNReal.ofReal s < g x}) :=
        (lintegral_add_left (measurable_meas_lt volume f) _).symm
    _ ≤ ∫⁻ s in Ioo (0 : ℝ) 1, 2 * volume {x | ENNReal.ofReal s < min (h x) 1} :=
        setLIntegral_mono ((measurable_meas_lt volume _).const_mul 2) level
    _ = 2 * ∫⁻ s in Ioo (0 : ℝ) 1, volume {x | ENNReal.ofReal s < min (h x) 1} :=
        lintegral_const_mul 2 (measurable_meas_lt volume _)
    _ = 2 * ∫⁻ x, min (h x) 1 := by
        rw [lintegral_eq_setLIntegral_Ioo_meas_lt volume hh' (fun x => min_le_right _ _)]
    _ ≤ 2 * ∫⁻ x, h x := by
        gcongr with x
        exact min_le_left _ _

/-- AM-GM in `ℝ≥0∞`: `x + y ≤ 2 z` implies `x y ≤ z ^ 2`. -/
lemma mul_le_sq_of_add_le_two_mul {x y z : ℝ≥0∞} (h : x + y ≤ 2 * z) : x * y ≤ z ^ 2 := by
  rcases eq_or_ne z ∞ with rfl | hz
  · simp
  have hxy : x + y ≠ ∞ := ne_top_of_le_ne_top (ENNReal.mul_ne_top (by norm_num) hz) h
  have hx : x ≠ ∞ := fun hx => hxy (by simp [hx])
  have hy : y ≠ ∞ := fun hy => hxy (by simp [hy])
  lift x to ℝ≥0 using hx
  lift y to ℝ≥0 using hy
  lift z to ℝ≥0 using hz
  norm_cast at h ⊢
  rw [← NNReal.coe_le_coe] at h ⊢
  push_cast at h ⊢
  nlinarith [sq_nonneg ((x : ℝ) - y), mul_nonneg (sub_nonneg.2 h)
    (add_nonneg (add_nonneg x.2 y.2) (mul_nonneg zero_le_two z.2))]

/-- One-dimensional Prékopa–Leindler for `f`, `g` with finite suprema. -/
lemma prekopaLeindler_one_of_iSup_ne_top {f g h : ℝ → ℝ≥0∞} (hf : Measurable f)
    (hg : Measurable g) (hh : Measurable h) (hfb : (⨆ x, f x) ≠ ∞) (hgb : (⨆ x, g x) ≠ ∞)
    (hfgh : ∀ x y, f x * g y ≤ h ((x + y) / 2) ^ 2) :
    (∫⁻ x, f x) * (∫⁻ x, g x) ≤ (∫⁻ x, h x) ^ 2 := by
  obtain ⟨a, ha⟩ : ∃ a, a = ⨆ x, f x := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = ⨆ x, g x := ⟨_, rfl⟩
  rw [← ha] at hfb
  rw [← hb] at hgb
  have hfa : ∀ x, f x ≤ a := fun x => ha ▸ le_iSup f x
  have hgb' : ∀ x, g x ≤ b := fun x => hb ▸ le_iSup g x
  rcases eq_or_ne a 0 with ha0 | ha0
  · have : ∀ x, f x = 0 := fun x => le_antisymm ((hfa x).trans ha0.le) zero_le
    simp [this]
  rcases eq_or_ne b 0 with hb0 | hb0
  · have : ∀ x, g x = 0 := fun x => le_antisymm ((hgb' x).trans hb0.le) zero_le
    simp [this]
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0∞, c = ((a.toNNReal * b.toNNReal).sqrt : ℝ≥0) := ⟨_, rfl⟩
  have hc2 : c ^ 2 = a * b := by
    rw [hc, ← ENNReal.coe_pow, NNReal.sq_sqrt, ENNReal.coe_mul, ENNReal.coe_toNNReal hfb,
      ENNReal.coe_toNNReal hgb]
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, zero_pow two_ne_zero] at hc2
    exact mul_ne_zero ha0 hb0 hc2.symm
  have hctop : c ≠ ∞ := by rw [hc]; exact ENNReal.coe_ne_top
  -- the normalized functions `f / a`, `g / b`, `h / c`
  have hsup : ∀ (φ : ℝ → ℝ≥0∞) (m : ℝ≥0∞), m = (⨆ x, φ x) → m ≠ 0 → m ≠ ∞ →
      ∀ t < 1, ∃ x, t < φ x * m⁻¹ := by
    intro φ m hm hm0 hmtop t ht
    have htm : t * m < m := by
      simpa [mul_comm] using ENNReal.mul_lt_mul_right hm0 hmtop ht
    obtain ⟨x, hx⟩ := lt_iSup_iff.1 (htm.trans_eq hm)
    refine ⟨x, ?_⟩
    rw [← div_eq_mul_inv, ENNReal.lt_div_iff_mul_lt (Or.inl hm0) (Or.inl hmtop)]
    exact hx
  have key := lintegral_add_lintegral_le_of_normalized (f := fun x => f x * a⁻¹)
    (g := fun x => g x * b⁻¹) (h := fun x => h x * c⁻¹) (hf.mul_const _) (hg.mul_const _)
    (hh.mul_const _)
    (fun x => (mul_le_mul' (hfa x) le_rfl).trans (ENNReal.mul_inv_cancel ha0 hfb).le)
    (fun x => (mul_le_mul' (hgb' x) le_rfl).trans (ENNReal.mul_inv_cancel hb0 hgb).le)
    (hsup f a ha ha0 hfb) (hsup g b hb hb0 hgb) ?_
  · beta_reduce at key
    rw [lintegral_mul_const _ hf, lintegral_mul_const _ hg, lintegral_mul_const _ hh] at key
    have hamgm := mul_le_sq_of_add_le_two_mul key
    calc (∫⁻ x, f x) * (∫⁻ x, g x)
        = (∫⁻ x, f x) * a⁻¹ * ((∫⁻ x, g x) * b⁻¹) * (a * b) := by
          rw [show (∫⁻ x, f x) * a⁻¹ * ((∫⁻ x, g x) * b⁻¹) * (a * b) =
              (∫⁻ x, f x) * (∫⁻ x, g x) * (a⁻¹ * a) * (b⁻¹ * b) by ring,
            ENNReal.inv_mul_cancel ha0 hfb, ENNReal.inv_mul_cancel hb0 hgb, mul_one, mul_one]
      _ ≤ ((∫⁻ x, h x) * c⁻¹) ^ 2 * (a * b) := mul_le_mul' hamgm le_rfl
      _ = (∫⁻ x, h x) ^ 2 := by
          rw [← hc2, ← mul_pow, mul_assoc, ENNReal.inv_mul_cancel hc0 hctop, mul_one]
  · intro x y
    have hinv : a⁻¹ * b⁻¹ = c⁻¹ ^ 2 := by
      rw [← ENNReal.inv_pow, hc2, ENNReal.mul_inv (Or.inl ha0) (Or.inl hfb)]
    calc f x * a⁻¹ * (g y * b⁻¹) = f x * g y * (a⁻¹ * b⁻¹) := by ring
      _ ≤ h ((x + y) / 2) ^ 2 * (a⁻¹ * b⁻¹) := mul_le_mul' (hfgh x y) le_rfl
      _ = (h ((x + y) / 2) * c⁻¹) ^ 2 := by rw [hinv, mul_pow]

/-- **One-dimensional Prékopa–Leindler inequality** (midpoint form): for measurable
`f g h : ℝ → ℝ≥0∞` with `f x * g y ≤ h ((x + y) / 2) ^ 2` for all `x y`,
`(∫⁻ f) * (∫⁻ g) ≤ (∫⁻ h) ^ 2`. -/
theorem prekopaLeindler_one {f g h : ℝ → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    (hh : Measurable h) (hfgh : ∀ x y, f x * g y ≤ h ((x + y) / 2) ^ 2) :
    (∫⁻ x, f x) * (∫⁻ x, g x) ≤ (∫⁻ x, h x) ^ 2 := by
  have trunc : ∀ φ : ℝ → ℝ≥0∞, Measurable φ →
      ∫⁻ x, φ x = ⨆ n : ℕ, ∫⁻ x, min (φ x) (n : ℝ≥0∞) := by
    intro φ hφ
    rw [← lintegral_iSup (f := fun n x => min (φ x) (n : ℝ≥0∞))
      (fun n => hφ.min measurable_const)
      (fun m n hmn x => min_le_min_left _ (Nat.cast_le.2 hmn))]
    congr 1
    funext x
    rw [← inf_iSup_eq, ENNReal.iSup_natCast, inf_top_eq]
  rw [trunc f hf, trunc g hg, ENNReal.iSup_mul]
  refine iSup_le fun m => ?_
  rw [ENNReal.mul_iSup]
  refine iSup_le fun n => ?_
  refine prekopaLeindler_one_of_iSup_ne_top (hf.min measurable_const) (hg.min measurable_const) hh
    (ne_top_of_le_ne_top (ENNReal.natCast_ne_top m) (iSup_le fun x => min_le_right _ _))
    (ne_top_of_le_ne_top (ENNReal.natCast_ne_top n) (iSup_le fun x => min_le_right _ _)) ?_
  intro x y
  exact (mul_le_mul' (min_le_left _ _) (min_le_left _ _)).trans (hfgh x y)

/-- **One-dimensional Prékopa–Leindler inequality**, stated with `midpoint`. -/
theorem prekopaLeindler_one_midpoint {f g h : ℝ → ℝ≥0∞} (hf : Measurable f)
    (hg : Measurable g) (hh : Measurable h)
    (hfgh : ∀ x y, f x * g y ≤ h (midpoint ℝ x y) ^ 2) :
    (∫⁻ x, f x) * (∫⁻ x, g x) ≤ (∫⁻ x, h x) ^ 2 :=
  prekopaLeindler_one hf hg hh fun x y => by simpa [real_midpoint_eq] using hfgh x y

end BiluLinial.Tight
