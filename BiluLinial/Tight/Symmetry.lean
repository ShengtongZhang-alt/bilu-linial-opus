/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.Defs

/-!
# Branch symmetry and zero sources

Blueprint nodes `D-swap` and `D-zero`.

* Reversing all signs swaps the two branches: `P̃⁻(y, σ) = P̃⁺(y, -σ)`, so the law with sources
  `(y⁺, y⁻)` is the image under `σ ↦ -σ` of the law with sources `(y⁻, y⁺)`, and
  `E h_i^-(y⁺, y⁻) = E h_i^+(y⁻, y⁺)`.
* A zero source is an isolated identity row of `P̃` (source Section 1.1): `D_i = 1` and the
  off-diagonal entries of row and column `i` vanish, so `h_i = 1` on every supported signing.
-/

@[expose] public section

namespace BiluLinial.Tight

open Matrix

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] in
/-- Reversing all signs negates every sign: `sgn (-σ) = -sgn σ`. -/
theorem sgn_neg (σ : Config V) (u w : V) : sgn (-σ) u w = -sgn σ u w := by
  simp [sgn]

omit [Fintype V] in
/-- `P̃^τ(y, -σ) = P̃^{-τ}(y, σ)`. -/
theorem precN_neg (a τ : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) :
    precN G a τ y (-σ) S = precN G a (-τ) y σ S := by
  ext u w
  simp only [precN, of_apply, sgn_neg]
  split_ifs <;> ring

/-- Reversing all signs swaps the two branches of the weight. -/
theorem wt_neg (p : ℕ) (a : ℝ) (yp ym : V → ℝ) (σ : Config V) (S : Finset V) :
    wt G p a ym yp (-σ) S = wt G p a yp ym σ S := by
  unfold wt
  rw [precN_neg, precN_neg, neg_neg]
  by_cases h : (precN G a 1 yp σ S).PosDef ∧ (precN G a (-1) ym σ S).PosDef
  · rw [ite_eq_left h, ite_eq_left ⟨h.2, h.1⟩, mul_comm]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h ⟨h'.2, h'.1⟩)]

theorem Zw_swap (p : ℕ) (a : ℝ) (yp ym : V → ℝ) (S : Finset V) :
    Zw G p a yp ym S = Zw G p a ym yp S := by
  unfold Zw
  calc ∑ σ, wt G p a yp ym σ S = ∑ σ, wt G p a ym yp (-σ) S := by simp only [wt_neg]
    _ = ∑ σ, wt G p a ym yp σ S :=
        Equiv.sum_comp (Equiv.neg (Config V)) (fun σ => wt G p a ym yp σ S)

/-- The law with sources `(y⁺, y⁻)` is the image under `σ ↦ -σ` of the law with sources
`(y⁻, y⁺)`, for every observable. -/
theorem lawE_swap (p : ℕ) (a : ℝ) (yp ym : V → ℝ) (S : Finset V) (f : Config V → ℝ) :
    lawE G p a yp ym S f = lawE G p a ym yp S (fun σ => f (-σ)) := by
  unfold lawE
  rw [Zw_swap G p a yp ym S]
  congr 1
  calc ∑ σ, wt G p a yp ym σ S * f σ = ∑ σ, wt G p a ym yp (-σ) S * f (- -σ) := by
        simp only [wt_neg, neg_neg]
    _ = ∑ σ, wt G p a ym yp σ S * f (-σ) :=
        Equiv.sum_comp (Equiv.neg (Config V)) (fun σ => wt G p a ym yp σ S * f (-σ))

theorem meanMinus_eq_meanPlus_swap (d p : ℕ) (yp ym : V → ℝ) (S : Finset V) (i : V) :
    meanMinus G d p yp ym S i = meanPlus G d p ym yp S i := by
  unfold meanMinus meanPlus lawE
  rw [Zw_swap G p (aOf d p) yp ym S]
  congr 1
  calc ∑ σ, wt G p (aOf d p) yp ym σ S * hN G (aOf d p) (-1) ym σ S i
      = ∑ σ, wt G p (aOf d p) ym yp (-σ) S * hN G (aOf d p) 1 ym (-σ) S i := by
        simp only [wt_neg, hN, precN_neg]
    _ = ∑ σ, wt G p (aOf d p) ym yp σ S * hN G (aOf d p) 1 ym σ S i :=
        Equiv.sum_comp (Equiv.neg (Config V))
          (fun σ => wt G p (aOf d p) ym yp σ S * hN G (aOf d p) 1 ym σ S i)

/-- At a zero source the normalized inverse diagonal is `1` (for an invertible precision). -/
theorem hN_of_source_zero {a τ : ℝ} {y : V → ℝ} {σ : Config V} {S : Finset V} {i : V}
    (hyi : y i = 0) (hdet : IsUnit (precN G a τ y σ S).det) : hN G a τ y σ S i = 1 := by
  have hcol : precN G a τ y σ S *ᵥ Pi.single i 1 = Pi.single i 1 := by
    rw [mulVec_single_one]
    ext u
    rw [col_apply]
    by_cases hu : u = i
    · subst hu
      simp [precN, diagD, cEdge, hyi, cRoot]
    · simp [precN, hu, hyi]
  have h := congrArg (fun v => (precN G a τ y σ S)⁻¹ *ᵥ v) hcol
  simp only [mulVec_mulVec, nonsing_inv_mul _ hdet, one_mulVec] at h
  have h' := congrFun h i
  rw [mulVec_single_one, col_apply, Pi.single_eq_same] at h'
  exact h'.symm

theorem meanPlus_of_source_zero {d p : ℕ} {yp ym : V → ℝ} {S : Finset V} {i : V}
    (hyi : yp i = 0) (hZ : 0 < Zw G p (aOf d p) yp ym S) : meanPlus G d p yp ym S i = 1 := by
  unfold meanPlus lawE
  have h : ∀ σ, wt G p (aOf d p) yp ym σ S * hN G (aOf d p) 1 yp σ S i =
      wt G p (aOf d p) yp ym σ S := by
    intro σ
    by_cases hσ : (precN G (aOf d p) 1 yp σ S).PosDef ∧ (precN G (aOf d p) (-1) ym σ S).PosDef
    · rw [hN_of_source_zero G hyi hσ.1.det_pos.ne'.isUnit, mul_one]
    · rw [wt, ite_eq_right hσ, zero_mul]
  simp only [h]
  exact div_self hZ.ne'

end BiluLinial.Tight
