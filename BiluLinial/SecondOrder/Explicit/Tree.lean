/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.SecondOrder.Explicit.TreeNumeric
public import BiluLinial.Counterexample.JoinGreen

/-!
# The response of the complete `q`-ary tree at a general threshold

Blueprint node `C2-tree` (source Section 6; generalizes Part B's `tree_green`, which holds only
at `r = 2√q`). For `t > 0`, `R = thr n t` and every signed adjacency matrix `A` of `T_h`:
`R I - A ≻ 0` and `g(T_h, A) = treeResp n R h`. Induction on `h` with the join lemma
(`join_posDef_iff`, `join_green_eq`); the denominators are positive by `treeResp_denom_pos`.
-/

@[expose] public section

namespace BiluLinial.SecondOrder.Explicit

open Matrix BiluLinial.Counterexample

/-- One step of the recursion: if every signed adjacency matrix `B` of `Y` has `R I - B ≻ 0` and
response `g`, and `R - q g > 0`, then every signed adjacency matrix of `join q Y` has
`R I - A ≻ 0` and response `1 / (R - q g)`. -/
private theorem join_step (n : ℕ) {R : ℝ} {Y : RGraph} (g : ℝ)
    (hY : ∀ B : Matrix Y.V Y.V ℝ, IsSignedAdj Y.G B →
      (R • (1 : Matrix Y.V Y.V ℝ) - B).PosDef ∧ green R B Y.root = g)
    (hp : 0 < R - ((n : ℝ) + 2) * g)
    {A : Matrix (join (n + 2) Y).V (join (n + 2) Y).V ℝ} (hA : IsSignedAdj (join (n + 2) Y).G A) :
    (R • (1 : Matrix (join (n + 2) Y).V (join (n + 2) Y).V ℝ) - A).PosDef ∧
      green R A (join (n + 2) Y).root = 1 / (R - ((n : ℝ) + 2) * g) := by
  have hA' : IsSignedAdj (attachGraph (⊥ : SimpleGraph Unit) Y (fun _ : Fin (n + 2) => ())) A :=
    hA
  have hc : ∀ i : Fin (n + 2), IsSignedAdj Y.G (copyBlock Y A i) := fun i => hA'.copy i
  have hYpd : ∀ i : Fin (n + 2), (R • (1 : Matrix Y.V Y.V ℝ) - copyBlock Y A i).PosDef :=
    fun i => (hY _ (hc i)).1
  have hsum : ∑ i : Fin (n + 2), green R (copyBlock Y A i) Y.root = ((n : ℝ) + 2) * g := by
    rw [Finset.sum_congr rfl fun i _ => (hY _ (hc i)).2, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    norm_num
  have hpd := (join_posDef_iff hA hYpd).2 (by rw [hsum]; exact hp)
  exact ⟨hpd, by rw [join_green_eq hA hYpd hpd, hsum]⟩

theorem tree_resp (n : ℕ) {t : ℝ} (ht : 0 < t) (h : ℕ) {A : Matrix (tree n h).V (tree n h).V ℝ}
    (hA : IsSignedAdj (tree n h).G A) :
    (thr n t • (1 : Matrix (tree n h).V (tree n h).V ℝ) - A).PosDef ∧
      green (thr n t) A (tree n h).root = treeResp n (thr n t) h := by
  induction h with
  | zero =>
    have h0 : A (tree n 0).root (tree n 0).root = 0 := hA.apply_self _
    have hM0 : (thr n t • (1 : Matrix (tree n 0).V (tree n 0).V ℝ) - A) (tree n 0).root
        (tree n 0).root = thr n t := by
      simp [h0]
    have hM : (thr n t • (1 : Matrix (tree n 0).V (tree n 0).V ℝ) - A) () () = thr n t := hM0
    have hpd := (unit_matrix_posDef_iff
      (thr n t • (1 : Matrix (tree n 0).V (tree n 0).V ℝ) - A)).2 (by rw [hM]; exact thr_pos n ht)
    have hinv := unit_matrix_inv_apply (thr n t • (1 : Matrix (tree n 0).V (tree n 0).V ℝ) - A)
    rw [hM] at hinv
    exact ⟨hpd, hinv⟩
  | succ h ih =>
    exact join_step n (Y := tree n h) (treeResp n (thr n t) h) (fun B hB => ih hB)
      (treeResp_denom_pos n ht h) (A := A) hA

end BiluLinial.SecondOrder.Explicit
