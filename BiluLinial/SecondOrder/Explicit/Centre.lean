/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.SecondOrder.Explicit.Amplify
public import BiluLinial.SecondOrder.Explicit.Scalar

/-!
# The centre: no signing of the core has norm below `R`

Blueprint node `C2-centre` (source Section 6: "Joining `q+1` copies of a sufficiently amplified
branch at a final central vertex is therefore impossible under the assumed norm bound: the two
central Schur inequalities would require the sum of the child mean responses to be at most `R`").

Let `t > 0`, `q t² < 1`, `F_q(t²) > 0`, `R = thr n t`. There are `h, L` such that no signed
adjacency matrix `A` of `triCentre n h L = join (q+1) Q_L` has `R I - A ≻ 0` and `R I + A ≻ 0`.

Proof: `tri_seed_gain` gives `h` with `u₀ := seedMean n t h > 1/(q t)`; `step_gain` gives `ε > 0`;
choose `L ≥ (R/(q+1) - u₀)/ε`. If both were `≻ 0`, `join_mresp_ge` gives `∑ᵢ m(A_i) < R`, while
each copy `A_i` (signed, `R I ∓ A_i ≻ 0`) has `m(A_i) ≥ u₀ + L ε ≥ R/(q+1)` by `tri_amplify`, so
`∑ᵢ m(A_i) ≥ R`.
-/

@[expose] public section

namespace BiluLinial.SecondOrder.Explicit

open Matrix BiluLinial.Counterexample

theorem tri_centre_not_bounded (n : ℕ) {t : ℝ} (ht : 0 < t) (hqt : ((n : ℝ) + 2) * t ^ 2 < 1)
    (hF : 1 + t ^ 2 + (t ^ 2) ^ 2 + 4 * (t ^ 2) ^ 4 <
      ((n : ℝ) + 2) * t ^ 2 * (1 + t ^ 2 + (t ^ 2) ^ 2 + 2 * (t ^ 2) ^ 3)) :
    ∃ h L : ℕ, ∀ A : Matrix (triCentre n h L).V (triCentre n h L).V ℝ,
      IsSignedAdj (triCentre n h L).G A →
      ¬ ((thr n t • (1 : Matrix (triCentre n h L).V (triCentre n h L).V ℝ) - A).PosDef ∧
        (thr n t • (1 : Matrix (triCentre n h L).V (triCentre n h L).V ℝ) + A).PosDef) := by
  obtain ⟨h, hh⟩ := tri_seed_gain n ht hqt hF
  obtain ⟨ε, hε, hstep⟩ := step_gain n ht hqt hh
  obtain ⟨L, hL⟩ := exists_nat_ge ((thr n t / ((n : ℝ) + 3) - seedMean n t h) / ε)
  refine ⟨h, L, fun A hA hAB => ?_⟩
  obtain ⟨hm, hp⟩ := hAB
  have hJ : IsSignedAdj (join (n + 3) (triQ n h L)).G A := hA
  have hA' : IsSignedAdj (attachGraph (⊥ : SimpleGraph Unit) (triQ n h L)
      (fun _ : Fin (n + 3) => ())) A := hA
  obtain ⟨hpos, -⟩ := join_mresp_ge hJ hm hp
  have hci : ∀ i, seedMean n t h + L * ε ≤
      mresp (thr n t) (copyBlock (triQ n h L) A i) (triQ n h L).root :=
    fun i => tri_amplify n h ht hε.le le_rfl hstep L _ (hA'.copy i)
      (copy_posDef (K := Unit) _ hm hp i).1 (copy_posDef (K := Unit) _ hm hp i).2
  have hsum : ((n : ℝ) + 3) * (seedMean n t h + L * ε) ≤
      ∑ i, mresp (thr n t) (copyBlock (triQ n h L) A i) (triQ n h L).root := by
    have := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin (n + 3)))) fun i _ => hci i
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    push_cast at this
    exact this
  have hq3 : (0 : ℝ) < n + 3 := by positivity
  have hLε : thr n t ≤ ((n : ℝ) + 3) * (seedMean n t h + L * ε) := by
    have h1 : thr n t / ((n : ℝ) + 3) - seedMean n t h ≤ L * ε := by
      rwa [div_le_iff₀ hε] at hL
    have h2 : thr n t / ((n : ℝ) + 3) ≤ seedMean n t h + L * ε := by linarith
    rwa [div_le_iff₀ hq3, mul_comm] at h2
  linarith

end BiluLinial.SecondOrder.Explicit
