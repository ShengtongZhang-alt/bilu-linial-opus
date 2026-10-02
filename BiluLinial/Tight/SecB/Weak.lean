/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecB.W1

/-!
# Random-profile weak loop (W1)

Node TB.W1 of `docs/tight/BP_SECB.md` (source Lemma "Random-profile weak loop", lines 721–911;
AUDIT-B §2.4 with fixes B-2, B-3; `docs/tight/DR1_CHECK.md` §3, W1′). The base nodes TB.row,
TB.W2, TB.ward, TB.S1w, TB.Dstar, TB.W5 are in `SecB/WeakBase.lean`; the sub-nodes of TB.W1
(TB.W1alg, TB.W1fib, TB.W1sec, TB.W1mask, TB.W1ibp) are in `SecB/W1.lean`.

* **TB.W1** (`weak_loop_of`): the four weak identities of Section 1.5 with the exact determinant
  score `2pa|G⁺_ij - G⁻_ij|` and remainder `B₀` (literal form of `in_W1`). Proof: TB.W1alg gives
  `4 T_k = ∓(a·wEdge + a²·wMain)` for each target `T_k` (`weak_targets`), and TB.W1ibp bounds
  `|a·wEdge + a²·wMain| ≤ C 𝖲_f + C B₀` (`weak_ibp_of`).

**Checks.** `N = ∅` (isolated root): `u = 0`, `b = 0`, both sides of each weak identity vanish,
score `0`. Zero source `y_i = 0`: rows of `X` vanish, TB.W2 reads `0 = 0`. Numerically: (W2)
residual `6·10⁻¹⁷`, (W3) residual `4·10⁻¹¹` (AUDIT-B §6, `auditB_weak_identities.py`).
-/

@[expose] public section

namespace BiluLinial.Tight.SecB

open Matrix

universe u

/-- **TB.W1** (random-profile weak loop, GCI-free form W1′), the literal form of `in_W1`, given
(CL1) and (C2). The constant is absolute; the score keeps the exact determinant score
`2pa|G⁺_ij - G⁻_ij|` and the root-weight derivative. -/
theorem weak_loop_of {K Kb c Kδ : ℝ} (hK : 0 ≤ K) (hKb : 0 ≤ Kb) (hc : 0 < c) (hKδ : 0 ≤ Kδ)
    (hCL : CL1Shape.{u} K Kb c) (hC2 : C2RowShape.{u} Kδ) :
    ∃ C : ℝ, 0 < C ∧ Eventually fun _c₀ _κ₀ d p h =>
      ∀ ct : Contact.{u} d p,
        |ct.qP h - ct.zeta h - ct.tP h| ≤
            C * ct.score ct.OmP ct.dOmP (ct.XP h) (ct.XP h) (fun _ => ct.uvec) +
              C * B0P d p h ∧
        |ct.zeta h - ct.zP h - ct.alphaE h| ≤
            C * ct.score ct.OmP ct.dOmP (ct.XP h) (ct.XP h) (ct.bP h) + C * B0P d p h ∧
        |ct.qM h + ct.zetaM h - ct.tM h| ≤
            C * ct.score ct.OmM ct.dOmM (ct.XM h) (ct.XP h) (fun _ => ct.uvec) +
              C * B0P d p h ∧
        |ct.zetaM h + ct.zM h - ct.betaE h| ≤
            C * ct.score ct.OmM ct.dOmM (ct.XM h) (ct.XP h) (ct.bM h) + C * B0P d p h := by
  obtain ⟨C, hC, hI⟩ := weak_ibp_of hK hKb hc hKδ hCL hC2
  refine ⟨C, hC, (hI.and eventually_h_facts).mono ?_⟩
  rintro c₀ κ₀ d p h ⟨hI', -, h0, -⟩ ct
  obtain ⟨i1, i2, i3, i4⟩ := hI' ct
  obtain ⟨e1, e2, e3, e4⟩ := weak_targets ct h0.le
  have key : ∀ T L R : ℝ, |4 * T| = |L| → |L| ≤ R → |T| ≤ R := by
    intro T L R hTL hLR
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)] at hTL
    have := abs_nonneg T
    linarith
  exact ⟨key _ _ _ (by rw [e1, abs_neg]) i1, key _ _ _ (by rw [e2, abs_neg]) i2,
    key _ _ _ (by rw [e3]) i3, key _ _ _ (by rw [e4]) i4⟩

end BiluLinial.Tight.SecB
