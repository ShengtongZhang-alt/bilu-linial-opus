/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.Compare.Multi

/-!
# Order-independence of `∂^{2j}`

Part D (`docs/second_order_bilu_linial_tight.tex`, Section 1.2, eq. (E4)). The comparison
`gauss_rad_expansion` takes the derivatives `∂^{2j} f = dEven l j f` coordinate by coordinate in
the order of an enumeration `l`. For `C^n` functions partial derivatives commute, so the order is
irrelevant:

* `pderiv_comm`: `∂_i ∂_j f = ∂_j ∂_i f` for `f ∈ C²`;
* `pderivList_perm`: `pderivList l f = pderivList l' f` for `l ~ l'` and `f ∈ C^{|l|}`;
* `dEven_perm`: `dEven l j f = dEven l' j f` for `l ~ l'`;
* `count_dEvenList`, `length_dEvenList`: `dEven l j f = pderivList (dEvenList l j) f` differentiates
  `2 j_x` times in each coordinate `x ∈ l`, in total `Σ_{x ∈ l} 2 j_x` times.
-/

@[expose] public section

namespace BiluLinial.Tight

open Function

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Partial derivatives of a `C²` function commute. -/
theorem pderiv_comm {f : (ι → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) (i j : ι) :
    pderiv i (pderiv j f) = pderiv j (pderiv i f) := by
  funext x
  have hsymm := (hf.contDiffAt (x := x)).isSymmSndFDerivAt (by simp)
  have hd : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have key : ∀ v w : ι → ℝ,
      fderiv ℝ (fun y => fderiv ℝ f y w) x v = fderiv ℝ (fderiv ℝ f) x v w := by
    intro v w
    rw [fderiv_clm_apply (hd x) (differentiableAt_const w)]
    simp
  change fderiv ℝ (fun y => fderiv ℝ f y (Pi.single j 1)) x (Pi.single i 1) =
    fderiv ℝ (fun y => fderiv ℝ f y (Pi.single i 1)) x (Pi.single j 1)
  rw [key, key, hsymm]

/-- Iterated partial derivatives of a `C^{|l|}` function do not depend on the order. -/
theorem pderivList_perm {l l' : List ι} (h : l.Perm l') :
    ∀ f : (ι → ℝ) → ℝ, ContDiff ℝ (l.length : WithTop ℕ∞) f → pderivList l f = pderivList l' f := by
  induction h with
  | nil => intro f _; rfl
  | cons x _ ih =>
    intro f hf
    exact ih (pderiv x f) (contDiff_pderiv (by simpa using hf) x)
  | swap x y l =>
    intro f hf
    simp only [pderivList_cons]
    rw [pderiv_comm (hf.of_le (by norm_cast; simp))]
  | trans h₁ _ ih₁ ih₂ =>
    intro f hf
    rw [ih₁ f hf, ih₂ f (by rwa [← h₁.length_eq])]

/-- The list of coordinates differentiated by `dEven l j`: each `x ∈ l` repeated `2 j_x` times. -/
def dEvenList (l : List ι) (j : ι → ℕ) : List ι :=
  l.flatMap fun x => List.replicate (2 * j x) x

omit [Fintype ι] in
theorem dEven_eq_pderivList (l : List ι) (j : ι → ℕ) (f : (ι → ℝ) → ℝ) :
    dEven l j f = pderivList (dEvenList l j) f := rfl

omit [Fintype ι] [DecidableEq ι] in
theorem length_dEvenList (l : List ι) (j : ι → ℕ) :
    (dEvenList l j).length = (l.map fun x => 2 * j x).sum := by
  simp [dEvenList, List.length_flatMap]

omit [Fintype ι] in
theorem count_dEvenList {l : List ι} (hl : l.Nodup) (j : ι → ℕ) (x : ι) :
    (dEvenList l j).count x = if x ∈ l then 2 * j x else 0 := by
  induction l with
  | nil => simp [dEvenList]
  | cons y l ih =>
    have hy : y ∉ l := (List.nodup_cons.mp hl).1
    have ih' := ih (List.nodup_cons.mp hl).2
    simp only [dEvenList, List.flatMap_cons, List.count_append, List.count_replicate] at ih' ⊢
    rw [ih']
    by_cases hxy : x = y
    · subst hxy; simp [hy]
    · have : (y == x) = false := by simpa using Ne.symm hxy
      simp [this, hxy]

/-- `∂^{2j} f` does not depend on the order in which the coordinates are processed. -/
theorem dEven_perm {l l' : List ι} (h : l.Perm l') (j : ι → ℕ) {f : (ι → ℝ) → ℝ}
    (hf : ContDiff ℝ ((dEvenList l j).length : WithTop ℕ∞) f) : dEven l j f = dEven l' j f :=
  pderivList_perm (h.flatMap_right _) f hf

end BiluLinial.Tight
