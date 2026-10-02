/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import Mathlib

/-!
# Partial derivatives of functions on `ι → ℝ`

Part D (`docs/second_order_bilu_linial_tight.tex`, Section 1.2, eq. (E4)). The multi-coordinate
comparison involves the iterated partial derivatives `∂^{2j} f = Π_i ∂_i^{2j_i} f`.

* `pderiv i f`: the partial derivative `∂_i f x = Df(x) e_i`;
* `pderivList l f`: iterated partial derivatives along a list of coordinates, head first;
* `SmoothBdd N f`: `f` is `C^N` and every iterated partial derivative of order `≤ N` is bounded
  (`smoothBdd_of_hasCompactSupport`: every compactly supported `C^N` function qualifies);
* `hasDerivAt_slice`: along a coordinate line, `t ↦ g (update x i t)` has derivative
  `∂_i g (update x i t)`.
-/

@[expose] public section

namespace BiluLinial.Tight

open Function

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The partial derivative `∂_i f x = Df(x) e_i` of `f : (ι → ℝ) → ℝ` in coordinate `i`. -/
noncomputable def pderiv (i : ι) (f : (ι → ℝ) → ℝ) : (ι → ℝ) → ℝ :=
  fun x => fderiv ℝ f x (Pi.single i 1)

/-- Iterated partial derivatives along a list of coordinates; the head is applied first:
`pderivList [i₁, …, iₙ] f = ∂_{iₙ} ⋯ ∂_{i₁} f`. -/
noncomputable def pderivList : List ι → ((ι → ℝ) → ℝ) → (ι → ℝ) → ℝ
  | [], f => f
  | i :: l, f => pderivList l (pderiv i f)

omit [Fintype ι] in
@[simp] theorem pderivList_nil (f : (ι → ℝ) → ℝ) : pderivList ([] : List ι) f = f := rfl

omit [Fintype ι] in
@[simp] theorem pderivList_cons (i : ι) (l : List ι) (f : (ι → ℝ) → ℝ) :
    pderivList (i :: l) f = pderivList l (pderiv i f) := rfl

omit [Fintype ι] in
theorem pderivList_append (l₁ l₂ : List ι) (f : (ι → ℝ) → ℝ) :
    pderivList (l₁ ++ l₂) f = pderivList l₂ (pderivList l₁ f) := by
  induction l₁ generalizing f with
  | nil => rfl
  | cons i l ih => simp [ih]

omit [Fintype ι] in
theorem pderivList_replicate (m : ℕ) (i : ι) (f : (ι → ℝ) → ℝ) :
    pderivList (List.replicate m i) f = (pderiv i)^[m] f := by
  induction m generalizing f with
  | zero => rfl
  | succ m ih => rw [List.replicate_succ, pderivList_cons, ih, iterate_succ_apply]

/-- `f` is `C^N` and all its iterated partial derivatives of order at most `N` are bounded. -/
def SmoothBdd (N : ℕ) (f : (ι → ℝ) → ℝ) : Prop :=
  ContDiff ℝ (N : WithTop ℕ∞) f ∧ ∀ l : List ι, l.length ≤ N → ∃ C, ∀ x, |pderivList l f x| ≤ C

theorem contDiff_pderiv {N : ℕ} {f : (ι → ℝ) → ℝ} (hf : ContDiff ℝ ((N + 1 : ℕ) : WithTop ℕ∞) f)
    (i : ι) : ContDiff ℝ (N : WithTop ℕ∞) (pderiv i f) := by
  have h := hf.fderiv_right (m := (N : WithTop ℕ∞)) (by push_cast; exact le_rfl)
  exact h.clm_apply contDiff_const

theorem SmoothBdd.pd {N : ℕ} {f : (ι → ℝ) → ℝ} (hf : SmoothBdd (N + 1) f) (i : ι) :
    SmoothBdd N (pderiv i f) :=
  ⟨contDiff_pderiv hf.1 i, fun l hl => hf.2 (i :: l) (by simp; omega)⟩

theorem SmoothBdd.mono {N N' : ℕ} {f : (ι → ℝ) → ℝ} (hf : SmoothBdd N f) (h : N' ≤ N) :
    SmoothBdd N' f :=
  ⟨hf.1.of_le (by exact_mod_cast h), fun l hl => hf.2 l (hl.trans h)⟩

theorem SmoothBdd.iterate {N m : ℕ} {f : (ι → ℝ) → ℝ} (hf : SmoothBdd (N + m) f) (i : ι) :
    SmoothBdd N ((pderiv i)^[m] f) := by
  induction m generalizing f with
  | zero => simpa using hf
  | succ m ih =>
    rw [iterate_succ_apply]
    exact ih (hf.pd i)

/-- If `m ≤ N`, then `∂_i^m f` is `SmoothBdd (N - m)`. -/
theorem SmoothBdd.iterate' {N m : ℕ} {f : (ι → ℝ) → ℝ} (hf : SmoothBdd N f) (hm : m ≤ N)
    (i : ι) : SmoothBdd (N - m) ((pderiv i)^[m] f) := by
  have h : N = (N - m) + m := by omega
  rw [h] at hf
  exact hf.iterate i

theorem SmoothBdd.continuous {N : ℕ} {f : (ι → ℝ) → ℝ} (hf : SmoothBdd N f) : Continuous f :=
  hf.1.continuous

theorem SmoothBdd.bdd {N : ℕ} {f : (ι → ℝ) → ℝ} (hf : SmoothBdd N f) : ∃ C, ∀ x, |f x| ≤ C :=
  hf.2 [] (Nat.zero_le _)

theorem SmoothBdd.differentiable {N : ℕ} {f : (ι → ℝ) → ℝ} (hf : SmoothBdd N f) (hN : 1 ≤ N) :
    Differentiable ℝ f :=
  hf.1.differentiable (by norm_cast; omega)

/-- Along the coordinate line through `x` in direction `e_i`, the derivative of a differentiable
function is its partial derivative. -/
theorem hasDerivAt_slice {g : (ι → ℝ) → ℝ} (hg : Differentiable ℝ g) (x : ι → ℝ) (i : ι)
    (t : ℝ) : HasDerivAt (fun s => g (update x i s)) (pderiv i g (update x i t)) t :=
  (hg (update x i t)).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_update x i t)

omit [Fintype ι] in
theorem hasCompactSupport_pderiv {f : (ι → ℝ) → ℝ} (hc : HasCompactSupport f) (i : ι) :
    HasCompactSupport (pderiv i f) :=
  (hc.fderiv (𝕜 := ℝ)).comp_left (g := fun L : (ι → ℝ) →L[ℝ] ℝ => L (Pi.single i 1)) (by simp)

private theorem bdd_pderivList_of_hasCompactSupport :
    ∀ (l : List ι) (N : ℕ) (f : (ι → ℝ) → ℝ), ContDiff ℝ (N : WithTop ℕ∞) f →
      HasCompactSupport f → l.length ≤ N → ∃ C, ∀ x, |pderivList l f x| ≤ C
  | [], N, f, hf, hc, _ => by
    obtain ⟨C, hC⟩ := hf.continuous.bounded_above_of_compact_support hc
    exact ⟨C, fun x => by simpa [Real.norm_eq_abs] using hC x⟩
  | i :: l, N, f, hf, hc, hl => by
    obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by simp at hl; omega⟩
    exact bdd_pderivList_of_hasCompactSupport l N' (pderiv i f) (contDiff_pderiv hf i)
      (hasCompactSupport_pderiv hc i) (by simp at hl; omega)

/-- A compactly supported `C^N` function has bounded partial derivatives up to order `N`. -/
theorem smoothBdd_of_hasCompactSupport {N : ℕ} {f : (ι → ℝ) → ℝ}
    (hf : ContDiff ℝ (N : WithTop ℕ∞) f) (hc : HasCompactSupport f) : SmoothBdd N f :=
  ⟨hf, fun l hl => bdd_pderivList_of_hasCompactSupport l N f hf hc hl⟩

end BiluLinial.Tight
