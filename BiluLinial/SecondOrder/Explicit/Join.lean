/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.SecondOrder.Explicit.Defs
public import BiluLinial.Counterexample.JoinGreen

/-!
# The join step for mean responses

Blueprint node `C2-join` (source Section 6: "If the child branches have mean two-sided root
response at least `u`, Schur complementation and the harmonic-mean inequality give mean response
at the new root at least `1/(R - q u)`"; and the central Schur inequalities).

* `copy_posDef`: `r I ∓ A ≻ 0` on an attach graph gives `r I ∓ A_i ≻ 0` on every copy (principal
  submatrices of positive definite matrices).
* `join_mresp_ge`: for a signed adjacency matrix `A` of `join k Y` with `R I ∓ A ≻ 0`:
  `R - ∑ᵢ m(A_i) > 0` and `m(A) ≥ 1 / (R - ∑ᵢ m(A_i))`, where `m = mresp R`. Proof: with
  `p_± = R - ∑ᵢ g(±A_i) > 0` (`join_posDef_iff`), `g(±A) = 1/p_±` (`join_green_eq`),
  `R - ∑ᵢ m(A_i) = (p₊ + p₋)/2` and `(1/p₊ + 1/p₋)/2 ≥ 2/(p₊ + p₋)`.
-/

@[expose] public section

namespace BiluLinial.SecondOrder.Explicit

open Matrix BiluLinial.Counterexample

theorem copy_posDef {K ι : Type} [DecidableEq K] [DecidableEq ι] (Y : RGraph) {r : ℝ}
    {A : Matrix (K ⊕ (Y.V × ι)) (K ⊕ (Y.V × ι)) ℝ}
    (hm : (r • (1 : Matrix (K ⊕ (Y.V × ι)) (K ⊕ (Y.V × ι)) ℝ) - A).PosDef)
    (hp : (r • (1 : Matrix (K ⊕ (Y.V × ι)) (K ⊕ (Y.V × ι)) ℝ) + A).PosDef) (i : ι) :
    (r • (1 : Matrix Y.V Y.V ℝ) - copyBlock Y A i).PosDef ∧
      (r • (1 : Matrix Y.V Y.V ℝ) + copyBlock Y A i).PosDef := by
  have hinj : Function.Injective (fun w : Y.V => (Sum.inr (w, i) : K ⊕ (Y.V × ι))) :=
    fun a b hab => by simpa using hab
  refine ⟨?_, ?_⟩
  · have := hm.submatrix hinj
    rwa [smul_one_sub_submatrix r A hinj] at this
  · have hp' : (r • (1 : Matrix (K ⊕ (Y.V × ι)) (K ⊕ (Y.V × ι)) ℝ) - -A).PosDef := by
      rwa [sub_neg_eq_add]
    have := hp'.submatrix hinj
    rw [smul_one_sub_submatrix r (-A) hinj, submatrix_neg, Pi.neg_apply, Pi.neg_apply,
      sub_neg_eq_add] at this
    exact this

/-- `(1/p₊ + 1/p₋)/2 ≥ 1/((p₊ + p₋)/2)` with `p_± = R - S_±`. -/
private theorem mean_scalar {Sm Sp R : ℝ} (pm : 0 < R - Sm) (pp : 0 < R - Sp) :
    0 < R - (Sm + Sp) / 2 ∧ 1 / (R - (Sm + Sp) / 2) ≤ (1 / (R - Sm) + 1 / (R - Sp)) / 2 := by
  obtain ⟨a, rfl⟩ : ∃ a, Sm = R - a := ⟨R - Sm, by ring⟩
  obtain ⟨b, rfl⟩ : ∃ b, Sp = R - b := ⟨R - Sp, by ring⟩
  simp only [sub_sub_cancel] at pm pp ⊢
  have e : R - (R - a + (R - b)) / 2 = (a + b) / 2 := by ring
  rw [e]
  refine ⟨by positivity, ?_⟩
  have key : (1 / a + 1 / b) / 2 - 1 / ((a + b) / 2) = (a - b) ^ 2 / (2 * a * b * (a + b)) := by
    field_simp
    ring
  have : 0 ≤ (a - b) ^ 2 / (2 * a * b * (a + b)) := by positivity
  linarith

theorem join_mresp_ge {k : ℕ} {Y : RGraph} {R : ℝ} {A : Matrix (join k Y).V (join k Y).V ℝ}
    (hA : IsSignedAdj (join k Y).G A)
    (hm : (R • (1 : Matrix (join k Y).V (join k Y).V ℝ) - A).PosDef)
    (hp : (R • (1 : Matrix (join k Y).V (join k Y).V ℝ) + A).PosDef) :
    0 < R - ∑ i, mresp R (copyBlock Y A i) Y.root ∧
      1 / (R - ∑ i, mresp R (copyBlock Y A i) Y.root) ≤ mresp R A (join k Y).root := by
  have hc := fun i => copy_posDef (K := Unit) (ι := Fin k) Y hm hp i
  have hYm : ∀ i, (R • (1 : Matrix Y.V Y.V ℝ) - copyBlock Y A i).PosDef := fun i => (hc i).1
  have hYp : ∀ i, (R • (1 : Matrix Y.V Y.V ℝ) -
      copyBlock Y (-A : Matrix (join k Y).V (join k Y).V ℝ) i).PosDef := fun i => by
    have h : copyBlock Y (-A : Matrix (join k Y).V (join k Y).V ℝ) i = -copyBlock Y A i := rfl
    rw [h, sub_neg_eq_add]
    exact (hc i).2
  have hZp : (R • (1 : Matrix (join k Y).V (join k Y).V ℝ) - -A).PosDef := by
    rwa [sub_neg_eq_add]
  have gm := join_green_eq hA hYm hm
  have gp := join_green_eq hA.neg hYp hZp
  have pm := (join_posDef_iff hA hYm).1 hm
  have pp := (join_posDef_iff hA.neg hYp).1 hZp
  have hsum : ∑ i, mresp R (copyBlock Y A i) Y.root =
      (∑ i, green R (copyBlock Y A i) Y.root +
        ∑ i, green R (copyBlock Y (-A : Matrix (join k Y).V (join k Y).V ℝ) i) Y.root) / 2 := by
    simp only [mresp, ← Finset.sum_div, Finset.sum_add_distrib]
    rfl
  have hval : mresp R A (join k Y).root =
      (1 / (R - ∑ i, green R (copyBlock Y A i) Y.root) +
        1 / (R - ∑ i, green R
          (copyBlock Y (-A : Matrix (join k Y).V (join k Y).V ℝ) i) Y.root)) / 2 := by
    rw [mresp, gm, gp]
  rw [hsum, hval]
  exact mean_scalar pm pp

end BiluLinial.SecondOrder.Explicit
