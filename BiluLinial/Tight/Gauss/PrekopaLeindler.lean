/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.Gauss.PrekopaLeindler1D

/-!
# The Prékopa–Leindler inequality on `ι → ℝ` (midpoint form) and Prékopa's theorem

* `prekopaLeindler`: for a finite type `ι` and measurable `f g h : (ι → ℝ) → ℝ≥0∞` with
  `f x * g y ≤ h (midpoint ℝ x y) ^ 2` for all `x y`, `(∫⁻ f) * (∫⁻ g) ≤ (∫⁻ h) ^ 2`.
* `prekopa_midpoint`: the marginal `t ↦ ∫⁻ x, F x t` of a midpoint log-concave function `F` is
  midpoint log-concave.

The proof is by induction on the dimension for `Fin n → ℝ`: split off the first coordinate with
`MeasurableEquiv.piFinSuccAbove`, apply the `n`-dimensional inequality to the slices and the
one-dimensional inequality (`prekopaLeindler_one`) to the partial integrals. A general finite `ι`
is reduced to `Fin (Fintype.card ι)` by the volume-preserving reindexing
`MeasurableEquiv.arrowCongr'`.
-/

@[expose] public section

namespace BiluLinial.Tight

open MeasureTheory Set
open scoped ENNReal

/-- `Fin.insertNth` commutes with midpoints. -/
lemma midpoint_insertNth {n : ℕ} (i : Fin (n + 1)) (a b : ℝ) (x y : Fin n → ℝ) :
    midpoint ℝ (Fin.insertNth i a x : Fin (n + 1) → ℝ) (Fin.insertNth i b y) =
      Fin.insertNth i (midpoint ℝ a b) (midpoint ℝ x y) := by
  funext j
  rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩
  · simp only [pi_midpoint_apply, Fin.insertNth_apply_same]
  · simp only [pi_midpoint_apply, Fin.insertNth_apply_succAbove]

/-- Prékopa–Leindler inequality (midpoint form) on `Fin n → ℝ`. -/
theorem prekopaLeindler_fin : ∀ (n : ℕ) {f g h : (Fin n → ℝ) → ℝ≥0∞}, Measurable f →
    Measurable g → Measurable h → (∀ x y, f x * g y ≤ h (midpoint ℝ x y) ^ 2) →
    (∫⁻ x, f x) * (∫⁻ x, g x) ≤ (∫⁻ x, h x) ^ 2
  | 0, f, g, h, _, _, _, hfgh => by
    have hvol : (volume : Measure (Fin 0 → ℝ)) = Measure.dirac (fun i => Fin.elim0 i) := by
      rw [volume_pi]; exact Measure.pi_of_empty _ _
    simp only [hvol, lintegral_dirac]
    have := hfgh (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
    rwa [midpoint_self] at this
  | n + 1, f, g, h, hf, hg, hh, hfgh => by
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
    have he : MeasurePreserving e.symm volume volume :=
      (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm
    have hint : ∀ φ : (Fin (n + 1) → ℝ) → ℝ≥0∞, Measurable φ →
        ∫⁻ x, φ x = ∫⁻ a : ℝ, ∫⁻ z : Fin n → ℝ, φ (e.symm (a, z)) := by
      intro φ hφ
      rw [← he.lintegral_comp_emb e.symm.measurableEmbedding, Measure.volume_eq_prod,
        lintegral_prod (fun p => φ (e.symm p)) (hφ.comp e.symm.measurable).aemeasurable]
    have hslice : ∀ φ : (Fin (n + 1) → ℝ) → ℝ≥0∞, Measurable φ → ∀ a : ℝ,
        Measurable fun z : Fin n → ℝ => φ (e.symm (a, z)) :=
      fun φ hφ a => hφ.comp (e.symm.measurable.comp measurable_prodMk_left)
    have hmarg : ∀ φ : (Fin (n + 1) → ℝ) → ℝ≥0∞, Measurable φ →
        Measurable fun a : ℝ => ∫⁻ z : Fin n → ℝ, φ (e.symm (a, z)) :=
      fun φ hφ => (hφ.comp e.symm.measurable).lintegral_prod_right'
    have hmid : ∀ (a b : ℝ) (z w : Fin n → ℝ),
        midpoint ℝ (e.symm (a, z)) (e.symm (b, w)) = e.symm ((a + b) / 2, midpoint ℝ z w) := by
      intro a b z w
      change midpoint ℝ (Fin.insertNth 0 a z : Fin (n + 1) → ℝ) (Fin.insertNth 0 b w) =
        Fin.insertNth 0 ((a + b) / 2) (midpoint ℝ z w)
      rw [midpoint_insertNth, real_midpoint_eq]
    rw [hint f hf, hint g hg, hint h hh]
    refine prekopaLeindler_one (hmarg f hf) (hmarg g hg) (hmarg h hh) fun a b => ?_
    refine prekopaLeindler_fin n (hslice f hf a) (hslice g hg b) (hslice h hh _) fun z w => ?_
    rw [← hmid]
    exact hfgh _ _

/-- **Prékopa–Leindler inequality** (midpoint form) on `ι → ℝ` for a finite type `ι`: for
measurable `f g h : (ι → ℝ) → ℝ≥0∞` with `f x * g y ≤ h (midpoint ℝ x y) ^ 2` for all `x y`,
`(∫⁻ f) * (∫⁻ g) ≤ (∫⁻ h) ^ 2` (Lebesgue measure). -/
theorem prekopaLeindler {ι : Type*} [Fintype ι] {f g h : (ι → ℝ) → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (hfgh : ∀ x y, f x * g y ≤ h (midpoint ℝ x y) ^ 2) :
    (∫⁻ x, f x) * (∫⁻ x, g x) ≤ (∫⁻ x, h x) ^ 2 := by
  let e := MeasurableEquiv.arrowCongr' (Fintype.equivFin ι).symm (MeasurableEquiv.refl ℝ)
  have he : MeasurePreserving e volume volume :=
    volume_preserving_arrowCongr' _ _ (MeasurePreserving.id volume)
  have hint : ∀ φ : (ι → ℝ) → ℝ≥0∞, ∫⁻ x, φ x = ∫⁻ y, φ (e y) :=
    fun φ => (he.lintegral_comp_emb e.measurableEmbedding φ).symm
  rw [hint f, hint g, hint h]
  refine prekopaLeindler_fin _ (hf.comp e.measurable) (hg.comp e.measurable)
    (hh.comp e.measurable) fun y y' => ?_
  have hmid : e (midpoint ℝ y y') = midpoint ℝ (e y) (e y') := by
    funext j; rfl
  simp only [hmid]
  exact hfgh _ _

/-- **Prékopa's theorem** (midpoint form): if `F : (ι → ℝ) → (κ → ℝ) → ℝ≥0∞` is jointly
measurable and midpoint log-concave, then its marginal `t ↦ ∫⁻ x, F x t` is midpoint
log-concave. -/
theorem prekopa_midpoint {ι κ : Type*} [Fintype ι] {F : (ι → ℝ) → (κ → ℝ) → ℝ≥0∞}
    (hF : Measurable (Function.uncurry F))
    (hlc : ∀ x y s t, F x s * F y t ≤ F (midpoint ℝ x y) (midpoint ℝ s t) ^ 2)
    (s t : κ → ℝ) :
    (∫⁻ x, F x s) * (∫⁻ x, F x t) ≤ (∫⁻ x, F x (midpoint ℝ s t)) ^ 2 :=
  prekopaLeindler (hF.comp measurable_prodMk_right) (hF.comp measurable_prodMk_right)
    (hF.comp measurable_prodMk_right) fun x y => hlc x y s t

/-- The marginal of a jointly measurable function is measurable. -/
theorem measurable_marginal {ι κ : Type*} [Fintype ι] {F : (ι → ℝ) → (κ → ℝ) → ℝ≥0∞}
    (hF : Measurable (Function.uncurry F)) :
    Measurable fun t => ∫⁻ x, F x t :=
  hF.lintegral_prod_left'

end BiluLinial.Tight
