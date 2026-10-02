/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.Contact.Chain2

/-!
# Contact exclusion

Blueprint node `D-contact` (source Sections 1.2–1.5). There is an absolute `c₀ ∈ (0, 1]` such that,
for all large `d` and `p = ⌊c₀ d^{2/17}⌋`, no contact context exists: if every proper induced
subgraph satisfies the capped-law invariant, the law of `G[S]` exists on the cube `[0, s]^V`, and
all normalized first means of `G[S]` are at most `r` on the smaller cube `[0, λ s]^V`, then no
point of that cube is a contact point `E h_v^+ = r`. (The minus branch follows by
`meanMinus_eq_meanPlus_swap`.)

The constant `c₀` is existential because the final ledger of Section 1.5 chooses it after the
absolute constants of the analytic lemmas and after `κ₀` (AUDIT-D, gap G3).

**Proof.** `contact_final` (`Tight/Contact/Chain2.lean`) gives an absolute `C` such that no
contact exists for large `d` once `C(√κ₀ + c₀^{17/3} + κ₀⁻² c₀^{34/3}) ≤ 1/8`; `ledger_choice`
picks `κ₀ = min(1, (24C)⁻²)` and then `c₀`. The chain is recorded in `docs/tight/BP_CONTACT.md`.

This is the parent of the whole analytic part of the source: the endpoint calculus and
Rademacher–Gaussian comparison (Section 1.2), concentration and the row gain, shifted means and the
weak loop (Section 1.3), the fresh-star row comparison (Section 1.4) and the contact estimate with
its final ledger (Section 1.5). Its decomposition is recorded in `docs/BLUEPRINT.md`.
-/

@[expose] public section

namespace BiluLinial.Tight

universe u

/-- No contact context exists at degree `d` and parameter `p`, for any graph on a vertex type in
universe `u`. -/
def ContactFree (d p : ℕ) : Prop :=
  ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (lam : ℝ) (yp ym : V → ℝ) (v : V), ¬ ContactCtx G d p S lam yp ym v

theorem exists_contact_free :
    ∃ c₀ : ℝ, 0 < c₀ ∧ c₀ ≤ 1 ∧ ∃ D : ℕ, ∀ d : ℕ, D ≤ d → ContactFree.{u} d (pAt c₀ d) := by
  obtain ⟨Ccrit, hC, hfin⟩ := contact_final.{u}
  obtain ⟨c₀, κ₀, hc0, hc1, hk0, hk1, hcrit⟩ := ledger_choice Ccrit hC
  obtain ⟨D, hD⟩ := hfin c₀ κ₀ hc0 hc1 hk0 hk1
  refine ⟨c₀, hc0, hc1, D, fun d hd => ?_⟩
  intro V _ _ G _ S lam yp ym v hctx
  exact hD d hd hcrit ⟨V, G, S, lam, yp, ym, v, hctx⟩

end BiluLinial.Tight
