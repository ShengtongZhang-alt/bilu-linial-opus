/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.SecondOrder.Explicit.Seed
public import BiluLinial.SecondOrder.Explicit.Join

/-!
# Amplification along the joins

Blueprint node `C2-amplify` (source Section 6: "repeatedly form a new rooted graph by joining a new
root to the roots of `q` disjoint copies of the previous graph"). Let `R = thr n t`, `u₀ ≤` the seed
mean, and `ε ≥ 0` a uniform gain of the map `c ↦ 1/(R - q c)` above `u₀` (`step_gain`). Then for
every `j` and every signed adjacency matrix `A` of `Q_j` with `R I ∓ A ≻ 0`, the mean response is
at least `u₀ + j ε`.

Proof: induction on `j`. `j = 0`: `seed_resp`. Step: `Q_{j+1} = join q Q_j`; each copy `A_i` is a
signed adjacency matrix of `Q_j` with `R I ∓ A_i ≻ 0` (`IsSignedAdj.copy`, `copy_posDef`), so
`m(A_i) ≥ c := u₀ + j ε`; `join_mresp_ge` gives `0 < R - ∑ m(A_i) ≤ R - q c` and
`m(A) ≥ 1/(R - ∑ m(A_i)) ≥ 1/(R - q c) ≥ c + ε`.
-/

@[expose] public section

namespace BiluLinial.SecondOrder.Explicit

open Matrix BiluLinial.Counterexample

theorem tri_amplify (n h : ℕ) {t : ℝ} (ht : 0 < t) {u₀ ε : ℝ} (hε : 0 ≤ ε)
    (hu₀ : u₀ ≤ seedMean n t h)
    (hstep : ∀ c : ℝ, u₀ ≤ c → 0 < thr n t - ((n : ℝ) + 2) * c →
      c + ε ≤ 1 / (thr n t - ((n : ℝ) + 2) * c)) :
    ∀ (j : ℕ) (A : Matrix (triQ n h j).V (triQ n h j).V ℝ), IsSignedAdj (triQ n h j).G A →
      (thr n t • (1 : Matrix (triQ n h j).V (triQ n h j).V ℝ) - A).PosDef →
      (thr n t • (1 : Matrix (triQ n h j).V (triQ n h j).V ℝ) + A).PosDef →
      u₀ + j * ε ≤ mresp (thr n t) A (triQ n h j).root := by
  intro j
  induction j with
  | zero =>
    intro A hA _ _
    have hs : mresp (thr n t) A (triQ n h 0).root = seedMean n t h := (seed_resp n h ht hA).2
    rw [Nat.cast_zero, zero_mul, add_zero, hs]
    exact hu₀
  | succ j ih =>
    intro A hA hm hp
    have hJ : IsSignedAdj (join (n + 2) (triQ n h j)).G A := hA
    have hA' : IsSignedAdj (attachGraph (⊥ : SimpleGraph Unit) (triQ n h j)
        (fun _ : Fin (n + 2) => ())) A := hA
    obtain ⟨hpos, hge⟩ := join_mresp_ge hJ hm hp
    set c : ℝ := u₀ + j * ε with hc_def
    have hci : ∀ i, c ≤ mresp (thr n t) (copyBlock (triQ n h j) A i) (triQ n h j).root :=
      fun i => ih _ (hA'.copy i) (copy_posDef (K := Unit) _ hm hp i).1
        (copy_posDef (K := Unit) _ hm hp i).2
    have hsum : ((n : ℝ) + 2) * c ≤
        ∑ i, mresp (thr n t) (copyBlock (triQ n h j) A i) (triQ n h j).root := by
      have := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin (n + 2)))) fun i _ => hci i
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
      push_cast at this
      exact this
    have hD : 0 < thr n t - ((n : ℝ) + 2) * c := by linarith
    have hcu : u₀ ≤ c := by
      have : 0 ≤ (j : ℝ) * ε := by positivity
      linarith
    have h1 := hstep c hcu hD
    have h2 : 1 / (thr n t - ((n : ℝ) + 2) * c) ≤
        1 / (thr n t - ∑ i, mresp (thr n t) (copyBlock (triQ n h j) A i) (triQ n h j).root) :=
      one_div_le_one_div_of_le hpos (by linarith)
    have e : u₀ + ((j + 1 : ℕ) : ℝ) * ε = c + ε := by
      rw [hc_def]
      push_cast
      ring
    rw [e]
    exact h1.trans (h2.trans hge)

end BiluLinial.SecondOrder.Explicit
