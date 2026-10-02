/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.Core

/-!
# The upper bound of Theorem 1 of `docs/second_order_bilu_linial_tight.tex`

Blueprint node `D-main`. `exists_contact_free` gives `c₀ ∈ (0, 1]` and a threshold `D`; take
`C = 8/c₀` and `d₀ = max D D₁`, where `D₁` makes `p = ⌊c₀ d^{2/17}⌋` lie in the regime
(`exists_tRegime_pAt`). `tight_signing` gives a signing with `‖A_σ‖ < R = √(4(d - 1) + 4/p)`, and
`4/p ≤ (8/c₀) d^{-2/17}` (`RsqOf_pAt_le`).
-/

@[expose] public section

namespace BiluLinial.Tight

universe u

theorem near_ramanujan_signing_thm :
    ∃ C : ℝ, ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
      ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        (∀ v, G.degree v ≤ d) →
          ∃ σ : Signing G, opNorm (signedAdjMatrix G σ) <
            Real.sqrt (4 * ((d : ℝ) - 1) + C * (d : ℝ) ^ (-(2 : ℝ) / 17)) := by
  obtain ⟨c₀, hc0, hc1, D, hD⟩ := exists_contact_free.{u}
  obtain ⟨D₁, hD₁⟩ := exists_tRegime_pAt hc0 hc1
  refine ⟨8 / c₀, max D D₁, fun d hd V _ _ G _ hdeg => ?_⟩
  obtain ⟨hR, hb⟩ := hD₁ d (le_of_max_le_right hd)
  obtain ⟨σ, hσ⟩ := tight_signing G hR (hD d (le_of_max_le_left hd)) hdeg
  exact ⟨σ, hσ.trans_le (Real.sqrt_le_sqrt (RsqOf_pAt_le hc0 hb))⟩

end BiluLinial.Tight
