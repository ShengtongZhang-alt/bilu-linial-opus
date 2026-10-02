/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Counterexample.Amplify
public import BiluLinial.Counterexample.SeedNumeric

/-!
# The centre: no signing of `J` has norm at most `r`

Blueprint node `B-centre` (source Step 8). There are `h, L` such that for every signed adjacency
matrix `A` of `J = coreGraph n h L`, `r I - A ⪰ 0 ∧ r I + A ⪰ 0` fails (`r = 2 √q`).

Proof: `seed_gain` gives `h` with `t(h) > 1`; pick `N ≥ 2` with `t(h) > 1 + 1/N` and `L = N - 1`.
If both were `⪰ 0`, each of the `d` branches `{z} ∪ Q_L` is a `join 1 Q_L` with `r I ∓ · ⪰ 0`, so by
`amplify` the branches are positive definite with `t > c_L = 2`. The join lemma at `z` (PSD
direction) for both signs gives `∑ᵢ s(X_i) ≤ 2r`, i.e. `∑ᵢ t(X_i) ≤ 2q`, contradicting
`∑ᵢ t(X_i) > 2d > 2q`.
-/

@[expose] public section

namespace BiluLinial.Counterexample

open Matrix

private theorem core_contra (n h N L : ℕ) (hN : 2 ≤ N) (hL : L + 1 = N)
    (hseed : 1 + 1 / (N : ℝ) < tseed n h)
    (A : Matrix (join (n + 3) (Qgraph n h L)).V (join (n + 3) (Qgraph n h L)).V ℝ)
    (hA : IsSignedAdj (join (n + 3) (Qgraph n h L)).G A)
    (hm : (rad n • (1 : Matrix (join (n + 3) (Qgraph n h L)).V (join (n + 3) (Qgraph n h L)).V ℝ) -
      A).PosSemidef)
    (hp : (rad n • (1 : Matrix (join (n + 3) (Qgraph n h L)).V (join (n + 3) (Qgraph n h L)).V ℝ) +
      A).PosSemidef) :
    False := by
  have hNL : (N : ℝ) - L = 1 := by
    have : (N : ℝ) = L + 1 := by exact_mod_cast hL.symm
    linarith
  have hbr : ∀ i : Fin (n + 3),
      (rad n • (1 : Matrix (Qgraph n h L).V (Qgraph n h L).V ℝ) -
          copyBlock (Qgraph n h L) A i).PosDef ∧
        (rad n • (1 : Matrix (Qgraph n h L).V (Qgraph n h L).V ℝ) +
          copyBlock (Qgraph n h L) A i).PosDef ∧
        2 < tval n (copyBlock (Qgraph n h L) A i) (Qgraph n h L).root := by
    intro i
    obtain ⟨h1, h2, h3⟩ := AmplifyAux.joinSub_branch (Qgraph n h L) (n + 3) i hA hm hp
    obtain ⟨p1, p2, p3⟩ := amplify n h N hN hseed L (by omega) _ h1 h2 h3
    rw [AmplifyAux.copyBlock_joinSub] at p1 p2 p3
    refine ⟨p1, p2, ?_⟩
    calc (2 : ℝ) = 1 + 1 / ((N : ℝ) - L) := by rw [hNL]; norm_num
      _ < _ := p3
  have hYm : ∀ i : Fin (n + 3), (rad n • (1 : Matrix (Qgraph n h L).V (Qgraph n h L).V ℝ) -
      copyBlock (Qgraph n h L) A i).PosDef := fun i => (hbr i).1
  have hYp : ∀ i : Fin (n + 3), (rad n • (1 : Matrix (Qgraph n h L).V (Qgraph n h L).V ℝ) -
      copyBlock (Qgraph n h L)
        (-A : Matrix (join (n + 3) (Qgraph n h L)).V (join (n + 3) (Qgraph n h L)).V ℝ) i).PosDef :=
    fun i => by
      rw [AmplifyAux.copyBlock_neg, sub_neg_eq_add]
      exact (hbr i).2.1
  have s1 := (join_posSemidef_iff hA hYm).1 hm
  have s2 := (join_posSemidef_iff hA.neg hYp).1 (by rwa [sub_neg_eq_add])
  simp only [AmplifyAux.copyBlock_neg] at s2
  have hsum : ∑ i, tval n (copyBlock (Qgraph n h L) A i) (Qgraph n h L).root =
      Real.sqrt (n + 2) / 2 *
        ((∑ i, green (rad n) (copyBlock (Qgraph n h L) A i) (Qgraph n h L).root) +
          ∑ i, green (rad n) (-copyBlock (Qgraph n h L) A i) (Qgraph n h L).root) := by
    unfold tval
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
  have hlow : 2 * ((n : ℝ) + 3) <
      ∑ i, tval n (copyBlock (Qgraph n h L) A i) (Qgraph n h L).root := by
    have := Finset.sum_lt_sum_of_nonempty (s := (Finset.univ : Finset (Fin (n + 3))))
      (f := fun _ => (2 : ℝ))
      (g := fun i => tval n (copyBlock (Qgraph n h L) A i) (Qgraph n h L).root)
      ⟨0, Finset.mem_univ _⟩ (fun i _ => (hbr i).2.2)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    push_cast at this
    linarith
  rw [hsum] at hlow
  generalize (∑ i, green (rad n) (copyBlock (Qgraph n h L) A i) (Qgraph n h L).root) = G
    at s1 hlow
  generalize (∑ i, green (rad n) (-copyBlock (Qgraph n h L) A i) (Qgraph n h L).root) = G'
    at s2 hlow
  have hrad : rad n = 2 * Real.sqrt (n + 2) := rfl
  rw [hrad] at s1 s2
  have hs2 : Real.sqrt (n + 2) * Real.sqrt (n + 2) = (n : ℝ) + 2 :=
    Real.mul_self_sqrt (by positivity)
  have key : Real.sqrt (n + 2) / 2 * (G + G') ≤ 2 * ((n : ℝ) + 2) := by
    calc Real.sqrt (n + 2) / 2 * (G + G') ≤ Real.sqrt (n + 2) / 2 * (4 * Real.sqrt (n + 2)) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 2 * (Real.sqrt (n + 2) * Real.sqrt (n + 2)) := by ring
      _ = 2 * ((n : ℝ) + 2) := by rw [hs2]
  linarith

theorem core_not_bounded (n : ℕ) :
    ∃ h L : ℕ, ∀ A : Matrix (coreGraph n h L).V (coreGraph n h L).V ℝ,
      IsSignedAdj (coreGraph n h L).G A →
      ¬ ((rad n • (1 : Matrix (coreGraph n h L).V (coreGraph n h L).V ℝ) - A).PosSemidef ∧
        (rad n • (1 : Matrix (coreGraph n h L).V (coreGraph n h L).V ℝ) + A).PosSemidef) := by
  obtain ⟨h, hh⟩ := seed_gain n
  have ht1 : 0 < tseed n h - 1 := by linarith
  obtain ⟨M, hM⟩ := exists_nat_gt (1 / (tseed n h - 1))
  obtain ⟨N, hN, hMN⟩ : ∃ N : ℕ, 2 ≤ N ∧ M ≤ N := ⟨max M 2, le_max_right _ _, le_max_left _ _⟩
  have hNpos : (0 : ℝ) < N := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hseed : 1 + 1 / (N : ℝ) < tseed n h := by
    have h1 : 1 / (tseed n h - 1) < N := lt_of_lt_of_le hM (by exact_mod_cast hMN)
    have h2 : 1 / (N : ℝ) < tseed n h - 1 := by
      rw [div_lt_iff₀ hNpos]
      rw [div_lt_iff₀ ht1] at h1
      linarith [mul_comm (N : ℝ) (tseed n h - 1)]
    linarith
  refine ⟨h, N - 1, fun A hA hAB => ?_⟩
  exact core_contra n h N (N - 1) hN (by omega) hseed A hA hAB.1 hAB.2

end BiluLinial.Counterexample
