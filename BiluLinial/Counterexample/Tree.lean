/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Counterexample.JoinGreen

/-!
# The response of the complete `q`-ary tree

Blueprint node `B-tree` (source Step 3, Xu Lemma 6.1(ii)). For every signed adjacency matrix `A`
of `T_h`: `r I - A ≻ 0` and `g(T_h, A) = (h + 1) / ((h + 2) √q)`, with `r = 2 √q`, `q = n + 2`.
-/

@[expose] public section

namespace BiluLinial.Counterexample

open Matrix

/-- One step of the recursion: if every signed adjacency matrix `B` of `Y` has `r I - B ≻ 0` and
response `g`, and `r - q g > 0`, then every signed adjacency matrix of `join q Y` has
`r I - A ≻ 0` and response `1 / (r - q g)`. -/
private theorem join_step (n : ℕ) {Y : RGraph} (g : ℝ)
    (hY : ∀ B : Matrix Y.V Y.V ℝ, IsSignedAdj Y.G B →
      (rad n • (1 : Matrix Y.V Y.V ℝ) - B).PosDef ∧ green (rad n) B Y.root = g)
    (hp : 0 < rad n - (n + 2) * g)
    {A : Matrix (join (n + 2) Y).V (join (n + 2) Y).V ℝ} (hA : IsSignedAdj (join (n + 2) Y).G A) :
    (rad n • (1 : Matrix (join (n + 2) Y).V (join (n + 2) Y).V ℝ) - A).PosDef ∧
      green (rad n) A (join (n + 2) Y).root = 1 / (rad n - (n + 2) * g) := by
  have hA' : IsSignedAdj (attachGraph (⊥ : SimpleGraph Unit) Y (fun _ : Fin (n + 2) => ())) A :=
    hA
  have hc : ∀ i : Fin (n + 2), IsSignedAdj Y.G (copyBlock Y A i) := fun i => hA'.copy i
  have hYpd : ∀ i : Fin (n + 2), (rad n • (1 : Matrix Y.V Y.V ℝ) - copyBlock Y A i).PosDef :=
    fun i => (hY _ (hc i)).1
  have hsum : ∑ i : Fin (n + 2), green (rad n) (copyBlock Y A i) Y.root = (n + 2) * g := by
    rw [Finset.sum_congr rfl fun i _ => (hY _ (hc i)).2, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    norm_num
  have hpd := (join_posDef_iff hA hYpd).2 (by rw [hsum]; exact hp)
  exact ⟨hpd, by rw [join_green_eq hA hYpd hpd, hsum]⟩

/-- `r - q g(T_h) > 0` and `1 / (r - q g(T_h)) = g(T_{h+1})`. -/
private theorem rad_sub_treeGreen (n h : ℕ) :
    0 < rad n - (n + 2) * treeGreen n h ∧
      1 / (rad n - (n + 2) * treeGreen n h) = treeGreen n (h + 1) := by
  have hs0 : 0 < Real.sqrt ((n : ℝ) + 2) := Real.sqrt_pos.2 (by positivity)
  have hss : Real.sqrt ((n : ℝ) + 2) * Real.sqrt ((n : ℝ) + 2) = n + 2 :=
    Real.mul_self_sqrt (by positivity)
  have hp : rad n - (n + 2) * treeGreen n h = Real.sqrt ((n : ℝ) + 2) * ((h + 3) / (h + 2)) := by
    unfold rad treeGreen
    generalize Real.sqrt ((n : ℝ) + 2) = s at hs0 hss ⊢
    rw [← hss]
    field_simp
    ring
  rw [hp]
  refine ⟨by positivity, ?_⟩
  unfold treeGreen
  push_cast
  field_simp
  ring

theorem tree_green (n h : ℕ) {A : Matrix (tree n h).V (tree n h).V ℝ}
    (hA : IsSignedAdj (tree n h).G A) :
    (rad n • (1 : Matrix (tree n h).V (tree n h).V ℝ) - A).PosDef ∧
      green (rad n) A (tree n h).root = treeGreen n h := by
  induction h with
  | zero =>
    have h0 : A (tree n 0).root (tree n 0).root = 0 := hA.apply_self _
    have hM0 : (rad n • (1 : Matrix (tree n 0).V (tree n 0).V ℝ) - A) (tree n 0).root
        (tree n 0).root = rad n := by
      simp [h0]
    have hM : (rad n • (1 : Matrix (tree n 0).V (tree n 0).V ℝ) - A) () () = rad n := hM0
    have hr : 0 < rad n := by unfold rad; positivity
    have hpd := (unit_matrix_posDef_iff
      (rad n • (1 : Matrix (tree n 0).V (tree n 0).V ℝ) - A)).2 (by rw [hM]; exact hr)
    have hinv := unit_matrix_inv_apply (rad n • (1 : Matrix (tree n 0).V (tree n 0).V ℝ) - A)
    rw [hM] at hinv
    refine ⟨hpd, hinv.trans ?_⟩
    unfold rad treeGreen
    simp
  | succ h ih =>
    obtain ⟨hp, hval⟩ := rad_sub_treeGreen n h
    obtain ⟨hpd, hg⟩ := join_step n (Y := tree n h) (treeGreen n h) (fun B hB => ih hB) hp
      (A := A) hA
    exact ⟨hpd, hg.trans hval⟩

end BiluLinial.Counterexample
