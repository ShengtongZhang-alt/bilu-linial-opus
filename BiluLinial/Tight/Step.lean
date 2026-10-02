/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.Floor
public import BiluLinial.Tight.Contact
public import BiluLinial.Tight.Continuity
public import BiluLinial.Tight.Symmetry
public import BiluLinial.Tight.FirstContact

/-!
# The induction step

Blueprint node `D-step` (source Section 1.1, last paragraph). Given the invariant for all proper
induced subgraphs: the law of `G[S]` exists on the whole cube (`floor_pos`); the first means are
continuous there (`continuousOn_meanPlus`, with the minus branch by `meanMinus_eq_meanPlus_swap`)
and equal `1 < r` at zero sources (`meanPlus_of_source_zero`); a first contact on an expanding cube
is excluded (`ContactFree`). The first-contact argument (`first_contact_cube`) concludes.
-/

@[expose] public section

namespace BiluLinial.Tight

universe u

variable {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable {d p : ℕ}

theorem tinv_step (hR : TRegime d p) (hCF : ContactFree.{u} d p) (hdeg : ∀ v, G.degree v ≤ d)
    (S : Finset V) (ih : ∀ T ⊂ S, TInv G d p T) : TInv G d p S := by
  have hpos := floor_pos G hR hdeg S ih
  have hs := hR.sOf_pos
  let f : (↥S × Bool) → (V → ℝ) × (V → ℝ) → ℝ := fun j y =>
    cond j.2 (meanPlus G d p y.1 y.2 S j.1) (meanMinus G d p y.1 y.2 S j.1)
  have hcont : ∀ j, ContinuousOn (f j) {y | InCube (sOf d p) y.1 ∧ InCube (sOf d p) y.2} := by
    rintro ⟨i, b⟩
    cases b
    · have hmaps : Set.MapsTo Prod.swap
          {y : (V → ℝ) × (V → ℝ) | InCube (sOf d p) y.1 ∧ InCube (sOf d p) y.2}
          {y | 0 < Zw G p (aOf d p) y.1 y.2 S} := fun y hy => hpos y.2 y.1 hy.2 hy.1
      refine ((continuousOn_meanPlus G (d := d) hR.two_le_p S i).comp
        continuous_swap.continuousOn hmaps).congr fun y _ => ?_
      exact meanMinus_eq_meanPlus_swap G d p y.1 y.2 S i
    · exact (continuousOn_meanPlus G hR.two_le_p S i).mono fun y hy => hpos y.1 y.2 hy.1 hy.2
  have hcube0 : InCube (sOf d p) (0 : V → ℝ) := fun _ => ⟨le_rfl, hs.le⟩
  have h0 : ∀ j, f j (0, 0) ≤ rOf d p := by
    have h1 : ∀ i, meanPlus G d p 0 0 S i = 1 := fun i =>
      meanPlus_of_source_zero G rfl (hpos 0 0 hcube0 hcube0)
    rintro ⟨i, b⟩
    cases b
    · change meanMinus G d p 0 0 S i ≤ rOf d p
      rw [meanMinus_eq_meanPlus_swap, h1]
      exact hR.one_lt_rOf.le
    · change meanPlus G d p 0 0 S i ≤ rOf d p
      rw [h1]
      exact hR.one_lt_rOf.le
  have hstep : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      (∀ y : (V → ℝ) × (V → ℝ), InCube (t * sOf d p) y.1 → InCube (t * sOf d p) y.2 →
        ∀ j, f j y ≤ rOf d p) →
      ∀ y : (V → ℝ) × (V → ℝ), InCube (t * sOf d p) y.1 → InCube (t * sOf d p) y.2 →
        ∀ j, f j y < rOf d p := by
    intro t ht0 ht1 hle y hy1 hy2 j
    have hcap : ∀ yp ym : V → ℝ, InCube (t * sOf d p) yp → InCube (t * sOf d p) ym →
        ∀ i ∈ S, meanPlus G d p yp ym S i ≤ rOf d p ∧ meanMinus G d p yp ym S i ≤ rOf d p :=
      fun yp ym h1 h2 i hi => ⟨hle (yp, ym) h1 h2 (⟨i, hi⟩, true),
        hle (yp, ym) h1 h2 (⟨i, hi⟩, false)⟩
    refine lt_of_le_of_ne (hle y hy1 hy2 j) fun heq => ?_
    obtain ⟨⟨i, hi⟩, b⟩ := j
    cases b
    · have heq' : meanPlus G d p y.2 y.1 S i = rOf d p := by
        rw [← meanMinus_eq_meanPlus_swap]
        exact heq
      have hcap' : ∀ yp ym : V → ℝ, InCube (t * sOf d p) yp → InCube (t * sOf d p) ym →
          ∀ i ∈ S, meanPlus G d p yp ym S i ≤ rOf d p ∧ meanMinus G d p yp ym S i ≤ rOf d p :=
        hcap
      exact hCF V G S t y.2 y.1 i ⟨⟨hdeg, ih, hpos, ht0, ht1, hcap'⟩, hy2, hy1, hi, heq'⟩
    · exact hCF V G S t y.1 y.2 i ⟨⟨hdeg, ih, hpos, ht0, ht1, hcap⟩, hy1, hy2, hi, heq⟩
  have key := first_contact_cube hs f hcont h0 hstep
  intro yp ym hyp hym
  exact ⟨hpos yp ym hyp hym, fun i hi =>
    ⟨key (yp, ym) hyp hym (⟨i, hi⟩, true), key (yp, ym) hyp hym (⟨i, hi⟩, false)⟩⟩

end BiluLinial.Tight
