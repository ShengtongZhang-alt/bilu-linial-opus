/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.Contact.Defs
public import BiluLinial.Tight.SecC.MarkEnv
public import BiluLinial.Tight.SecC.Shifted

/-!
# Section 1.4 inputs at a contact

Inputs MARKENV and (B1), supplied by the Section 1.4 exports (`Tight/SecC/Export.lean`).
See `Tight/Contact/Inputs.lean` for the conventions.
-/

@[expose] public section

namespace BiluLinial.Tight

open Matrix

universe u

/-- **I-MARKENV** (source proof of Lemma "Contact row comparison", l.1129–1149: the Schur
Frobenius bound `a⁴(G⁺_vv)²‖G⁺[N,N]‖_F² ≤ 2(Z_vG_vv)² tr A² + 2(a² Σ_N x_i²)²` and high-moment
interpolation; AUDIT-C §4.2 MARKENV). For any envelope `λ ≥ ϑ` of the row and core masses, the
marked envelopes of CR3 are `O(λ)`; the same for the minus branch. -/
theorem in_markenv : ∃ C : ℝ, 0 < C ∧ Eventually fun _c₀ _κ₀ d p _h =>
    ∀ ct : Contact.{u} d p,
      (∀ lam : ℝ, aOf d p ^ 2 * ct.Srow + ct.trA2 ≤ lam → vth d ≤ lam →
        ct.Srow / d ≤ 4 * lam ∧ ct.frobP / (d : ℝ) ^ 2 ≤ C * lam) ∧
      (∀ lam : ℝ, aOf d p ^ 2 * ct.Smin + ct.trB2 ≤ lam → vth d ≤ lam →
        ct.Smin / d ≤ 4 * lam ∧ ct.frobM / (d : ℝ) ^ 2 ≤ C * lam) := by
  obtain ⟨CF, hCF, hF⟩ := SecC.mark_envelope_frob.{u}
  refine ⟨CF, by linarith, (hF.and (SecC.eventually_regime 1)).mono ?_⟩
  rintro c₀ κ₀ d p h ⟨H, hR, -, -⟩ ct
  have hc := ct.ctx
  exact ⟨fun lam h1 h2 => ⟨(SecC.mark_envelope_row hR ct.G ct.S ct.yp ct.ym ct.v lam).1 h1,
      (H ct.V ct.G ct.S ct.lam ct.yp ct.ym ct.v hc.toCapCtx hc.hyp hc.hym hc.mem lam h2).1 h1⟩,
    fun lam h1 h2 => ⟨(SecC.mark_envelope_row hR ct.G ct.S ct.yp ct.ym ct.v lam).2 h1,
      (H ct.V ct.G ct.S ct.lam ct.yp ct.ym ct.v hc.toCapCtx hc.hyp hc.hym hc.mem lam h2).2 h1⟩⟩

/-- **I-B1** (source Lemma "Multiplicative shifted trace comparison", (B1), l.1192–1331, with the
Brascamp–Lieb step replaced by BLmid; AUDIT-C §4.3, §5.3). The Gaussian row numerator dominates the
trace budget: `Gterm ≥ (1 - C η_BL) Q - C ε_BL`, `η_BL = p⁴/d + p/(dh)`,
`ε_BL = ϑ(p⁵ + p²/h) + ϑ`. (Equivalently, with any raw comparison `𝓡 ≥ Gterm - E_row`,
`𝓡 ≥ (1 - η_BL) Q - E_row - ε_BL`.) -/
theorem in_B1 : ∃ C : ℝ, 0 < C ∧ Eventually fun _c₀ _κ₀ d p h =>
    ∀ ct : Contact.{u} d p,
      (1 - C * etaBL d p h) * ct.Qbl h - C * epsBL d p h ≤ ct.Gterm := by
  obtain ⟨C, hC, hB⟩ := SecC.rowGauss_ge_shiftQ.{u}
  refine ⟨C + 1, by linarith,
    (((hB.and (SecC.eventually_regime 1)).and SecC.eventually_h_mem).and
      SecC.eventually_exp_le_vth).mono ?_⟩
  rintro c₀ κ₀ d p h ⟨⟨⟨H, hR, -, -⟩, hh1, hh2⟩, he2, -⟩ ct
  have hc := ct.ctx
  have hθ : 0 < vth d := by
    have := hR.ten_pow_six_le_d
    unfold vth
    positivity
  have hh : 0 < h := hθ.trans_le hh1
  have key := H ct.V ct.G ct.S ct.lam ct.yp ct.ym ct.v hc.toCapCtx hc.hyp hc.hym hc.mem h hh1 hh2
  have hQ := SecC.shiftQ_nonneg hR ct.G hc.toCapCtx hc.hyp hc.hym hc.mem hh
  change (1 - (C + 1) * etaBL d p h) * shiftQ ct.G d p h ct.yp ct.ym ct.S ct.v -
    (C + 1) * epsBL d p h ≤ rowGauss ct.G d p ct.yp ct.ym ct.S ct.v
  unfold etaBL epsBL
  have heta : 0 ≤ (p : ℝ) ^ 4 / d + p / (d * h) := by positivity
  have hX : 0 ≤ vth d * ((p : ℝ) ^ 5 + (p : ℝ) ^ 2 / h) := by positivity
  have h1 := mul_nonneg heta hQ
  have h2 := mul_nonneg hC.le hθ.le
  nlinarith

end BiluLinial.Tight
