/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecC.RowCompare
public import BiluLinial.Tight.SecC.Shifted

/-!
# Exports of Section 1.4 to the contact layer

The statements below are literal copies of the inputs of the contact estimate (Section 1.5):
`in_markenv`, `in_B1` (`Tight/Contact/Inputs.lean`) and `in_CR3` (the paper's CR3, an input of
the GCI route, which is not formalized; the active route uses CR3′), proved here as a parent
check. The contact layer (`Tight/Contact/InputsC.lean`) proves `in_markenv` and `in_B1` directly
from the SecC nodes. The inputs are stated for a bundled contact `ct : Contact d p`; a contact is a capped point
(`ContactCtx` extends `CapCtx`, with the sources in `[0, λ s]^V`), and the `Contact.*` quantities
are definitionally the unbundled ones of `Tight/SecC/Defs.lean` (`Rrow = rowMean`,
`Gterm = rowGauss`, `Qbl h = shiftQ h`, `Srow`/`Smin = incRowE`, `trA2`/`trB2 = trSqE`,
`frobP`/`frobM = markE`).

* `in_markenv_pf`: the row half from `mark_envelope_row` (exact, constant `4`), the Frobenius half
  from `mark_envelope_frob`.
* `in_B1_pf`: `rowGauss_ge_shiftQ` at `z = h ∈ [ϑ, 1]` (`eventually_h_mem`), with
  `e^{-2p} ≤ ϑ` (`eventually_exp_le_vth`), `Q ≥ 0` (`shiftQ_nonneg`) and `C ↦ C + 1`.
* `in_CR3_pf`: `row_comparison_split` with `e^{-3p} ≤ ϑ` and `C ↦ max C 1` (the hypothesis
  `δ_c ≤ 1` of the input is not needed).
-/

@[expose] public section

namespace BiluLinial.Tight

namespace SecC

universe u

/-- `in_markenv` (`Tight/Contact/Inputs.lean`). -/
theorem in_markenv_pf : ∃ C : ℝ, 0 < C ∧ Eventually fun _c₀ _κ₀ d p _h =>
    ∀ ct : Contact.{u} d p,
      (∀ lam : ℝ, aOf d p ^ 2 * ct.Srow + ct.trA2 ≤ lam → vth d ≤ lam →
        ct.Srow / d ≤ 4 * lam ∧ ct.frobP / (d : ℝ) ^ 2 ≤ C * lam) ∧
      (∀ lam : ℝ, aOf d p ^ 2 * ct.Smin + ct.trB2 ≤ lam → vth d ≤ lam →
        ct.Smin / d ≤ 4 * lam ∧ ct.frobM / (d : ℝ) ^ 2 ≤ C * lam) := by
  obtain ⟨CF, hCF, hF⟩ := mark_envelope_frob.{u}
  refine ⟨CF, by linarith, (hF.and (eventually_regime 1)).mono ?_⟩
  rintro c₀ κ₀ d p h ⟨H, hR, -, -⟩ ct
  have hc := ct.ctx
  exact ⟨fun lam h1 h2 => ⟨(mark_envelope_row hR ct.G ct.S ct.yp ct.ym ct.v lam).1 h1,
      (H ct.V ct.G ct.S ct.lam ct.yp ct.ym ct.v hc.toCapCtx hc.hyp hc.hym hc.mem lam h2).1 h1⟩,
    fun lam h1 h2 => ⟨(mark_envelope_row hR ct.G ct.S ct.yp ct.ym ct.v lam).2 h1,
      (H ct.V ct.G ct.S ct.lam ct.yp ct.ym ct.v hc.toCapCtx hc.hyp hc.hym hc.mem lam h2).2 h1⟩⟩

/-- `in_B1` (`Tight/Contact/Inputs.lean`). -/
theorem in_B1_pf : ∃ C : ℝ, 0 < C ∧ Eventually fun _c₀ _κ₀ d p h =>
    ∀ ct : Contact.{u} d p,
      (1 - C * etaBL d p h) * ct.Qbl h - C * epsBL d p h ≤ ct.Gterm := by
  obtain ⟨C, hC, hB⟩ := rowGauss_ge_shiftQ.{u}
  refine ⟨C + 1, by linarith,
    (((hB.and (eventually_regime 1)).and eventually_h_mem).and eventually_exp_le_vth).mono ?_⟩
  rintro c₀ κ₀ d p h ⟨⟨⟨H, hR, -, -⟩, hh1, hh2⟩, he2, -⟩ ct
  have hc := ct.ctx
  have hθ : 0 < vth d := by
    have := hR.ten_pow_six_le_d
    unfold vth
    positivity
  have hh : 0 < h := hθ.trans_le hh1
  have key := H ct.V ct.G ct.S ct.lam ct.yp ct.ym ct.v hc.toCapCtx hc.hyp hc.hym hc.mem h hh1 hh2
  have hQ := shiftQ_nonneg hR ct.G hc.toCapCtx hc.hyp hc.hym hc.mem hh
  change (1 - (C + 1) * etaBL d p h) * shiftQ ct.G d p h ct.yp ct.ym ct.S ct.v -
    (C + 1) * epsBL d p h ≤ rowGauss ct.G d p ct.yp ct.ym ct.S ct.v
  unfold etaBL epsBL
  have heta : 0 ≤ (p : ℝ) ^ 4 / d + p / (d * h) := by positivity
  have hX : 0 ≤ vth d * ((p : ℝ) ^ 5 + (p : ℝ) ^ 2 / h) := by positivity
  have h1 := mul_nonneg heta hQ
  have h2 := mul_nonneg hC.le hθ.le
  nlinarith

/-- `in_CR3`, the paper's CR3 (input of the unformalized GCI route). -/
theorem in_CR3_pf : ∃ C : ℝ, 0 < C ∧ Eventually fun _c₀ _κ₀ d p _h =>
    ∀ ct : Contact.{u} d p, ∀ lr rr lc dc : ℝ, vth d ≤ lr → lr ≤ rr → rr ≤ dc → dc ≤ 1 →
      lr ≤ lc → lc ≤ dc → ct.Srow / d ≤ lr → ct.Smin / d ≤ rr →
      ct.frobP / (d : ℝ) ^ 2 ≤ lc → ct.frobM / (d : ℝ) ^ 2 ≤ dc →
      |ct.Rrow - ct.Gterm| ≤
        C * ((p : ℝ) ^ 5 * Real.sqrt (lr * rr) + (p : ℝ) ^ 4 * Real.sqrt (lc * dc) +
          (p : ℝ) ^ 13 / (d : ℝ) ^ 2) + C * vth d := by
  obtain ⟨C, hC, h3⟩ := row_comparison_split.{u}
  refine ⟨max C 1, lt_of_lt_of_le one_pos (le_max_right _ _),
    (h3.and eventually_exp_le_vth).mono ?_⟩
  rintro c₀ κ₀ d p h ⟨H, -, he3⟩ ct lr rr lc dc h1 h2 h3' - h5 h6 h7 h8 h9 h10
  have hc := ct.ctx
  have key := H ct.V ct.G ct.S ct.lam ct.yp ct.ym ct.v hc.toCapCtx hc.hyp hc.hym hc.mem lr rr lc
    dc h1 h2 h5 h6 h3' h7 h8 h9 h10
  change |rowMean ct.G d p ct.yp ct.ym ct.S ct.v - rowGauss ct.G d p ct.yp ct.ym ct.S ct.v| ≤ _
  have hX : 0 ≤ (p : ℝ) ^ 5 * Real.sqrt (lr * rr) + (p : ℝ) ^ 4 * Real.sqrt (lc * dc) +
      (p : ℝ) ^ 13 / (d : ℝ) ^ 2 := by positivity
  have hθ0 : 0 ≤ vth d := by unfold vth; positivity
  have e1 := mul_le_mul_of_nonneg_right (le_max_left C 1) hX
  have e2 := mul_le_mul_of_nonneg_right (le_max_right C 1) hθ0
  linarith

end SecC

end BiluLinial.Tight
