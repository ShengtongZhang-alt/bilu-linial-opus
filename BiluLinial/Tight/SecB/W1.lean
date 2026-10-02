/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecB.W1Mom
public import BiluLinial.Tight.SecB.W1Fib

/-!
# The weak loop (W1): assembly

Node TB.W1ibp of `docs/tight/BP_SECB.md`: `|a·wEdge + a²·wMain| ≤ C 𝖲_f + C B₀` in the four
configurations of `in_W1`, from TB.W1fib (`weak_fibre_of`, `SecB/W1Fib.lean`), TB.W1sec
(`weak_sec_of`) and TB.W1mask (`weak_mask_of`, both in `SecB/W1Mom.lean`) and `a|wScore| ≤ 𝖲_f`
(`w1_score_le`, `SecB/W1Defs.lean`).
-/

@[expose] public section

namespace BiluLinial.Tight.SecB

open Matrix

universe u

/-- The real-number assembly of TB.W1ibp. -/
theorem w1_assemble {a L sc sS sM S0 B C₁ C₂ C₃ : ℝ} (ha : 0 ≤ a)
    (hF : |L - a * (sc + sS + sM)| ≤ C₁ * B) (hsc : a * |sc| ≤ S0) (hS : a * |sS| ≤ C₂ * B)
    (hM : a * |sM| ≤ C₃ * B) (hS0 : 0 ≤ S0) (hB : 0 ≤ B) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hC₃ : 0 ≤ C₃) :
    |L| ≤ (1 + C₁ + C₂ + C₃) * S0 + (1 + C₁ + C₂ + C₃) * B := by
  have h1 : |L| ≤ |L - a * (sc + sS + sM)| + |a * (sc + sS + sM)| := by
    have := abs_add_le (L - a * (sc + sS + sM)) (a * (sc + sS + sM))
    rwa [sub_add_cancel] at this
  have h2 : |a * (sc + sS + sM)| ≤ a * |sc| + a * |sS| + a * |sM| := by
    rw [abs_mul, abs_of_nonneg ha]
    have t1 := abs_add_le (sc + sS) sM
    have t2 := abs_add_le sc sS
    have : |sc + sS + sM| ≤ |sc| + |sS| + |sM| := by linarith
    have := mul_le_mul_of_nonneg_left this ha
    linarith
  have h3 : 0 ≤ (C₁ + C₂ + C₃) * S0 := mul_nonneg (by linarith) hS0
  linarith

/-- **TB.W1ibp** (assembly). Given (CL1) and (C2): `|a·wEdge + a²·wMain| ≤ C 𝖲_f + C B₀` in the
four configurations (from TB.W1fib, TB.W1sec, TB.W1mask and `a|wScore| ≤ 𝖲_f`). -/
theorem weak_ibp_of {K Kb c Kδ : ℝ} (hK : 0 ≤ K) (hKb : 0 ≤ Kb) (hc : 0 < c) (hKδ : 0 ≤ Kδ)
    (hCL : CL1Shape.{u} K Kb c) (hC2 : C2RowShape.{u} Kδ) :
    ∃ C : ℝ, 0 < C ∧ Eventually fun _c₀ _κ₀ d p h => ∀ ct : Contact.{u} d p,
      |aOf d p * wEdge ct ct.OmP (ct.XP h) (ct.XP h) (fun _ => ct.uvec) +
          aOf d p ^ 2 * wMain ct ct.OmP (ct.XP h) (ct.XP h) (fun _ => ct.uvec)| ≤
        C * ct.score ct.OmP ct.dOmP (ct.XP h) (ct.XP h) (fun _ => ct.uvec) + C * B0P d p h ∧
      |aOf d p * wEdge ct ct.OmP (ct.XP h) (ct.XP h) (ct.bP h) +
          aOf d p ^ 2 * wMain ct ct.OmP (ct.XP h) (ct.XP h) (ct.bP h)| ≤
        C * ct.score ct.OmP ct.dOmP (ct.XP h) (ct.XP h) (ct.bP h) + C * B0P d p h ∧
      |aOf d p * wEdge ct ct.OmM (ct.XM h) (ct.XP h) (fun _ => ct.uvec) +
          aOf d p ^ 2 * wMain ct ct.OmM (ct.XM h) (ct.XP h) (fun _ => ct.uvec)| ≤
        C * ct.score ct.OmM ct.dOmM (ct.XM h) (ct.XP h) (fun _ => ct.uvec) + C * B0P d p h ∧
      |aOf d p * wEdge ct ct.OmM (ct.XM h) (ct.XP h) (ct.bM h) +
          aOf d p ^ 2 * wMain ct ct.OmM (ct.XM h) (ct.XP h) (ct.bM h)| ≤
        C * ct.score ct.OmM ct.dOmM (ct.XM h) (ct.XP h) (ct.bM h) + C * B0P d p h := by
  obtain ⟨C₁, hC₁, hF⟩ := weak_fibre_of hK hKb hc hKδ hCL hC2
  obtain ⟨C₂, hC₂, hS⟩ := weak_sec_of hK hKb hc hCL
  obtain ⟨C₃, hC₃, hM⟩ := weak_mask_of hK hKb hc hCL
  refine ⟨1 + C₁ + C₂ + C₃, by linarith, (((hF.and hS).and hM).and eventually_h_facts).mono ?_⟩
  rintro c₀ κ₀ d p h ⟨⟨⟨hF', hS'⟩, hM'⟩, hR, h0, -⟩ ct
  have ha : 0 ≤ aOf d p := hR.aOf_pos.le
  have hB : 0 ≤ B0P d p h := B0P_nonneg h0.le
  obtain ⟨f1, f2, f3, f4⟩ := hF' ct
  obtain ⟨s1, s2, s3, s4⟩ := hS' ct
  obtain ⟨m2, m4⟩ := hM' ct
  have hP : ∀ σ, wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 → 0 ≤ ct.OmP σ :=
    fun σ _ => w1_OmP_nonneg ct σ
  have hMn : ∀ σ, wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 → 0 ≤ ct.OmM σ :=
    fun σ hσ => w1_OmM_nonneg ct hσ
  have z0 : aOf d p * |(0 : ℝ)| ≤ C₃ * B0P d p h := by
    rw [abs_zero, mul_zero]
    exact mul_nonneg hC₃.le hB
  exact ⟨w1_assemble ha f1 (w1_score_le ct _ _ _ _ hP ha) s1 z0
      (w1_score_nonneg ct _ _ _ _ hP ha) hB hC₁.le hC₂.le hC₃.le,
    w1_assemble ha f2 (w1_score_le ct _ _ _ _ hP ha) s2 m2
      (w1_score_nonneg ct _ _ _ _ hP ha) hB hC₁.le hC₂.le hC₃.le,
    w1_assemble ha f3 (w1_score_le ct _ _ _ _ hMn ha) s3 z0
      (w1_score_nonneg ct _ _ _ _ hMn ha) hB hC₁.le hC₂.le hC₃.le,
    w1_assemble ha f4 (w1_score_le ct _ _ _ _ hMn ha) s4 m4
      (w1_score_nonneg ct _ _ _ _ hMn ha) hB hC₁.le hC₂.le hC₃.le⟩

end BiluLinial.Tight.SecB
