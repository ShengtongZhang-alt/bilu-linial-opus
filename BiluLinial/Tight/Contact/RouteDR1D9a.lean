/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.Contact.Chain1

/-!
# The post-contact row error (D9a) — GCI-free route

Blueprint `docs/tight/BP_CONTACT.md`, node `N-D9a`. The statement of `d9a` is route-independent;
here it is proved from CR3′ and DR1 (`Tight/Contact/RouteDR1.lean`), with the witnesses of
`docs/tight/CHECK_CONTACT.md` ("DR1-route replacements"). The paper's GR1-based proof is not
formalized (see `FORMALIZATION.md`, Part D, "Proof route").
-/

@[expose] public section

namespace BiluLinial.Tight

open Matrix

universe u

/-- **N-D9a** (source (D9a), l.1504–1518; AUDIT-C §6 (D9a), AUDIT-D §3.1 D9a; DR1_CHECK §3). With
`Γ = p⁴√(pδ̄/d)`: `|𝓡 - Gterm| ≤ C(Γ√(S+1) + p¹³/d² + ϑ)`. -/
theorem d9a : ∃ C : ℝ, 0 < C ∧ Eventually fun _c₀ _κ₀ d p _h =>
    ∀ ct : Contact.{u} d p, |ct.Rrow - ct.Gterm| ≤ C * ErowP d p ct.Srow := by
  obtain ⟨CC, -, hCR3⟩ := in_CR3'.{u}
  obtain ⟨CM, -, hME⟩ := in_markenv.{u}
  obtain ⟨C₂, -, hC2⟩ := in_C2.{u}
  obtain ⟨CD, -, hDR⟩ := in_DR1.{u}
  obtain ⟨C₆, -, hD6⟩ := d6.{u}
  obtain ⟨C₇, -, hD7⟩ := d7.{u}
  obtain ⟨C, hC, P₀, hreal⟩ := d9a_real_dr1 CC CM C₂ CD C₆ C₇
  refine ⟨C, hC, ((((((hCR3.and hME).and hC2).and hDR).and hD6).and hD7).and
    (eventually_treg_ge P₀)).mono ?_⟩
  rintro c₀ κ₀ d p h ⟨⟨⟨⟨⟨⟨H3, HM⟩, H2⟩, HD⟩, H6⟩, H7⟩, hR, hp⟩ ct
  obtain ⟨-, -, -, -, -, -, -, -, hS, -, hA2, -, -⟩ := source_facts hR ct
  exact hreal d p hR hp ct.Srow ct.Smin ct.trA2 ct.trB2 ct.frobP ct.frobM
    (∑ j ∈ ct.N, ct.E (fun σ => (ct.x σ j - ct.z σ j) ^ 2)) ct.Rrow ct.Gterm hS hA2
    (HM ct).1 (HM ct).2 (H2 ct).2.1 (H2 ct).2.2.2 ct.rowDiff_nonneg (HD ct ct.v ct.ctx.mem)
    (H6 ct) (H7 ct).1 (H3 ct)

end BiluLinial.Tight
