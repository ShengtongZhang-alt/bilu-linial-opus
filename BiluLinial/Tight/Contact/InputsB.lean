/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.Contact.Defs
public import BiluLinial.Tight.SecB.Export

/-!
# Section 1.3 inputs at a contact

Inputs (S1), (W5) and (W1), supplied by the Section 1.3 exports (`Tight/SecB/Export.lean`).
See `Tight/Contact/Inputs.lean` for the conventions.
-/

@[expose] public section

namespace BiluLinial.Tight

open Matrix

universe u


/-- **I-S1** (source mean shift (S1), l.696–719; AUDIT-B §2.3, B-7: `K_S` absolute, valid for
`d ≥ d_S(c₀, κ₀)`). Physical form: `0 ≤ E(G^±_ii - X^±_ii) ≤ C √h y^±_i` for every `i ∈ S`. -/
theorem in_S1 : ∃ C : ℝ, 0 < C ∧ Eventually fun _c₀ _κ₀ d p h =>
    ∀ ct : Contact.{u} d p, ∀ i ∈ ct.S,
      (0 ≤ ct.E (fun σ => ct.gp σ i i - ct.XP h σ i i) ∧
        ct.E (fun σ => ct.gp σ i i - ct.XP h σ i i) ≤ C * Real.sqrt h * ct.yp i) ∧
      (0 ≤ ct.E (fun σ => ct.gm σ i i - ct.XM h σ i i) ∧
        ct.E (fun σ => ct.gm σ i i - ct.XM h σ i i) ≤ C * Real.sqrt h * ct.ym i) := by
  exact SecB.in_S1.{u}

/-- **I-W5** (source mean Ward bound (W5), l.790–797; AUDIT-B §2.4). For every fixed power `m`,
`E[D_*^m (X_±²)_ii] ≤ C(m) h^{-1/2}` for `i ∈ S`. -/
theorem in_W5 (m : ℕ) : ∃ C : ℝ, 0 < C ∧ Eventually fun _c₀ _κ₀ d p h =>
    ∀ ct : Contact.{u} d p, ∀ i ∈ ct.S,
      ct.E (fun σ => ct.Dstar σ ^ m * (ct.XP h σ * ct.XP h σ) i i) ≤ C / Real.sqrt h ∧
      ct.E (fun σ => ct.Dstar σ ^ m * (ct.XM h σ * ct.XM h σ) i i) ≤ C / Real.sqrt h := by
  exact SecB.in_W5.{u} m

/-- **I-W1** (source Lemma "Random-profile weak loop", (W1)–(W4), l.721–911, with the exact
determinant score `2pa(G⁺_ij - G⁻_ij)` produced by its proof (AUDIT-B B-2) and the remainder
`B₀` of l.904–906 (which needs only `ρ_row ≤ Cp^{-2}`, AUDIT-B B-3)). Applied at
`(ε, ν) = (+,+)` with `H = Ω₊` and at `(ε, ν) = (-,+)` with `H = Ω₋`, each with the masks `f = u`
and `f = b_σ` (`w = u - εν b_σ`), and expanded by bilinearity and the symmetry of `K_σ`:
`|q₊ - ζ - t₊|`, `|ζ - z₊ - α|`, `|q₋ + ζ₋ - t₋|`, `|ζ₋ + z₋ - β|` are each at most
`C 𝖲_f + C B₀`. -/
theorem in_W1 : ∃ C : ℝ, 0 < C ∧ Eventually fun _c₀ _κ₀ d p h =>
    ∀ ct : Contact.{u} d p,
      |ct.qP h - ct.zeta h - ct.tP h| ≤
          C * ct.score ct.OmP ct.dOmP (ct.XP h) (ct.XP h) (fun _ => ct.uvec) + C * B0P d p h ∧
      |ct.zeta h - ct.zP h - ct.alphaE h| ≤
          C * ct.score ct.OmP ct.dOmP (ct.XP h) (ct.XP h) (ct.bP h) + C * B0P d p h ∧
      |ct.qM h + ct.zetaM h - ct.tM h| ≤
          C * ct.score ct.OmM ct.dOmM (ct.XM h) (ct.XP h) (fun _ => ct.uvec) + C * B0P d p h ∧
      |ct.zetaM h + ct.zM h - ct.betaE h| ≤
          C * ct.score ct.OmM ct.dOmM (ct.XM h) (ct.XP h) (ct.bM h) + C * B0P d p h := by
  exact SecB.in_W1.{u}

end BiluLinial.Tight
