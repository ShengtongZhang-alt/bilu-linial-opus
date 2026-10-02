/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.Contact.Defs
public import BiluLinial.Tight.SecA.Export

/-!
# Section 1.2 inputs at a contact

Inputs (E1), (C2), (C1), whitening and (C3a), supplied by the Section 1.2 exports
(`Tight/SecA/Export.lean`). See `Tight/Contact/Inputs.lean` for the conventions.
-/

@[expose] public section

namespace BiluLinial.Tight

open Matrix

universe u


/-- **I-E1** (source Lemma "Endpoint calculus", (E1), l.261–293, with the explicit derivatives
`𝒟₁x_i = -aP_i + (2p-1)a x_i² - 2pa x_i z_i` and `𝒟₃x_i = a³K_i` of l.1370–1391; AUDIT-A §2.2
(A6: constant `1.15·10⁹`, times capped sixth moments), AUDIT-D §3.1 D3, AUDIT-C §6 LOOP). For every
neighbour `i` of the root:
`|E[ξ_i x_i] - a(-E P_i + (2p-1) E x_i² - 2p E x_i z_i) + (a³/3) E K_i| ≤ C p⁵ a⁵`. -/
theorem in_E1 : ∃ C : ℝ, 0 < C ∧ Eventually fun _c₀ _κ₀ d p _h =>
    ∀ ct : Contact.{u} d p, ∀ i ∈ ct.N,
      |ct.sx i - aOf d p * (-(ct.E fun σ => ct.gp σ ct.v ct.v * ct.gp σ i i) +
          (2 * (p : ℝ) - 1) * (ct.E fun σ => ct.x σ i ^ 2) -
          2 * (p : ℝ) * (ct.E fun σ => ct.x σ i * ct.z σ i)) +
        aOf d p ^ 3 / 3 * (ct.E fun σ => Kpoly p (ct.x σ i) (ct.z σ i)
          (ct.gp σ ct.v ct.v * ct.gp σ i i) (ct.gm σ ct.v ct.v * ct.gm σ i i))| ≤
        C * (p : ℝ) ^ 5 * aOf d p ^ 5 := by
  exact SecA.in_E1.{u}

/-- **I-C2** (source Lemma "Bias and reference concentration", (C2), l.378–385, row and core parts,
at the root `v`; AUDIT-A §2.15, AUDIT-B §2.1). With `δ = C δ̄`:
`a² S₊ ≤ C δ̄`, `a² S₋ ≤ C δ̄`, `E tr A² ≤ C δ̄`, `E tr B² ≤ C δ̄`. -/
theorem in_C2 : ∃ C : ℝ, 0 < C ∧ Eventually fun _c₀ _κ₀ d p _h =>
    ∀ ct : Contact.{u} d p,
      aOf d p ^ 2 * ct.Srow ≤ C * dbar d p ∧ aOf d p ^ 2 * ct.Smin ≤ C * dbar d p ∧
        ct.trA2 ≤ C * dbar d p ∧ ct.trB2 ≤ C * dbar d p := by
  exact SecA.in_C2.{u}

/-- **I-C1** (source (C1), second part `N_G ≥ 0`, l.373–376 and l.393–397; with the Gaussian
integration by parts `N_G = 2𝖦F` of l.1249–1250; AUDIT-A §2.9, AUDIT-C §5.3 corollary (a)). The
Gaussian row numerator is nonnegative: `E_{ν_K} 𝖦F/(a² F_H) ≥ 0`. -/
theorem in_C1 : Eventually fun _c₀ _κ₀ d p _h => ∀ ct : Contact.{u} d p, 0 ≤ ct.Gterm := by
  exact SecA.in_C1.{u}

/-- **I-whiten** (source core-kernel argument of (C2), l.413–424 — whitening by `I + 2(p-1)A`, so
`N_G ≥ f_G w` — together with the endpoint transfer of the core-constant numerator `wΦ`
(l.1463–1472, AUDIT-C T.TRC with `m_± = 0`); AUDIT-A §2.11, AUDIT-C §6 (D6) step 4). With
`w = tr A²/(1 + tr A)`: `E w ≤ 2a² Gterm + C (p⁴/d)(E w + ϑ)`. -/
theorem in_whiten : ∃ C : ℝ, 0 < C ∧ Eventually fun _c₀ _κ₀ d p _h =>
    ∀ ct : Contact.{u} d p,
      ct.wker ≤ 2 * aOf d p ^ 2 * ct.Gterm + C * ((p : ℝ) ^ 4 / d) * (ct.wker + vth d) := by
  exact SecA.in_whiten.{u}

/-- **I-C3a** (source (C3a), l.428–435; AUDIT-A §2.11: `E[T_A 1{μ>1}] ≤ 0.52^{⌊p/4⌋}`). Since
`T_A 1{μ ≤ 1} ≤ 2w`: `E tr A² ≤ 2 E w + C ϑ`. -/
theorem in_C3a : ∃ C : ℝ, 0 < C ∧ Eventually fun _c₀ _κ₀ d p _h =>
    ∀ ct : Contact.{u} d p, ct.trA2 ≤ 2 * ct.wker + C * vth d := by
  exact SecA.in_C3a.{u}

end BiluLinial.Tight
