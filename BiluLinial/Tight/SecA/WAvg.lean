/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecA.Defs
public import BiluLinial.Tight.Tools.Interp

/-!
# Finite weighted averages: generalized Hölder (node `A-HOLD`)

Both laws of the section are finite weighted averages (`wavg`, `Tight/Tools/Interp.lean`): the
paired law `lawE = wavg wt` (`lawE_eq_wavg`) and the own core law `coreE = wavg wtCore`
(`coreE_eq_wavg`). The Hölder core and the interpolation lemma of AUDIT-A §2.8 (INTERP) are
T.IL (`wavg_mul_le_holder`, `wavg_mul_le_interp`, `Tight/Tools/Interp.lean`); they are not
restated here.

* `A-HOLD` (`wavg_prod_pow_le`), the generalized Hölder inequality used by CREM, HGR and the
  moment toolkit (AUDIT-A §2.5, §2.6): if `n = Σ_i e_i ≥ 1` and `E X_i^n ≤ c_i^n` for every `i`
  with `e_i > 0`, then `E Π_i X_i^{e_i} ≤ Π_i c_i^{e_i}`. Proof: weighted AM–GM
  `Π (X_i/c_i)^{e_i} ≤ Σ (e_i/n)(X_i/c_i)^n` pointwise (`Real.geom_mean_le_arith_mean_weighted`),
  then average.
* Linearity helpers (`wavg_add`, `wavg_sub`, `wavg_const_mul`, `wavg_mono'`).
-/

@[expose] public section

namespace BiluLinial.Tight

open Finset

theorem coreE_eq_wavg {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (p : ℕ) (a : ℝ) (yp ym : V → ℝ) (S : Finset V) (v : V)
    (f : Config V → ℝ) :
    coreE G p a yp ym S v f = wavg (fun σ => wtCore G p a yp ym σ S v) f := rfl

namespace SecA

variable {Ω : Type*} [Fintype Ω]

/-- Monotonicity on the support of the weights. -/
theorem wavg_mono' {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) {f g : Ω → ℝ}
    (h : ∀ ω, 0 < w ω → f ω ≤ g ω) : wavg w f ≤ wavg w g := by
  refine div_le_div_of_nonneg_right (sum_le_sum fun ω _ => ?_) (sum_nonneg fun ω _ => hw ω)
  rcases (hw ω).eq_or_lt with h0 | h0
  · rw [← h0, zero_mul, zero_mul]
  · exact mul_le_mul_of_nonneg_left (h ω h0) (hw ω)

theorem wavg_add (w : Ω → ℝ) (f g : Ω → ℝ) :
    wavg w (fun ω => f ω + g ω) = wavg w f + wavg w g := by
  simp only [wavg, mul_add, sum_add_distrib, add_div]

theorem wavg_sub (w : Ω → ℝ) (f g : Ω → ℝ) :
    wavg w (fun ω => f ω - g ω) = wavg w f - wavg w g := by
  simp only [wavg, mul_sub, sum_sub_distrib, sub_div]

theorem wavg_const_mul (w : Ω → ℝ) (c : ℝ) (f : Ω → ℝ) :
    wavg w (fun ω => c * f ω) = c * wavg w f := by
  simp only [wavg, mul_left_comm _ c, ← mul_sum, mul_div_assoc]

/-- `A-HOLD`: generalized Hölder through weighted AM–GM. -/
theorem wavg_prod_pow_le {ι : Type*} [Fintype ι] {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω)
    (X : ι → Ω → ℝ) (hX : ∀ i ω, 0 ≤ X i ω) (e : ι → ℕ) (n : ℕ) (hn : ∑ i, e i = n)
    (hn1 : 1 ≤ n) (c : ι → ℝ) (hc : ∀ i, 0 < c i)
    (hm : ∀ i, 0 < e i → wavg w (fun ω => X i ω ^ n) ≤ c i ^ n) :
    wavg w (fun ω => ∏ i, X i ω ^ e i) ≤ ∏ i, c i ^ e i := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hC : 0 < ∏ i, c i ^ e i := Finset.prod_pos fun i _ => pow_pos (hc i) _
  rcases (Finset.sum_nonneg fun ω _ => hw ω : 0 ≤ ∑ ω, w ω).eq_or_lt with hW | hW
  · rw [wavg, ← hW, div_zero]; exact hC.le
  -- pointwise weighted AM–GM
  have hpt : ∀ ω, ∏ i, X i ω ^ e i ≤
      (∏ i, c i ^ e i) * ∑ i, ((e i : ℝ) / n) * (X i ω / c i) ^ n := by
    intro ω
    have hz : ∀ i ∈ Finset.univ, 0 ≤ (X i ω / c i) ^ n :=
      fun i _ => pow_nonneg (div_nonneg (hX i ω) (hc i).le) n
    have hwt : ∀ i ∈ Finset.univ, 0 ≤ (e i : ℝ) / n := fun i _ => by positivity
    have hsum : ∑ i ∈ Finset.univ, (e i : ℝ) / n = 1 := by
      rw [← Finset.sum_div, div_eq_one_iff_eq hn0.ne']
      exact_mod_cast hn
    have hg := Real.geom_mean_le_arith_mean_weighted Finset.univ (fun i => (e i : ℝ) / n)
      (fun i => (X i ω / c i) ^ n) hwt hsum hz
    have hpow : ∀ i, ((X i ω / c i) ^ n) ^ ((e i : ℝ) / n) = (X i ω / c i) ^ e i := by
      intro i
      rw [← Real.rpow_natCast (X i ω / c i) n, ← Real.rpow_mul (div_nonneg (hX i ω) (hc i).le),
        mul_div_cancel₀ _ hn0.ne', Real.rpow_natCast]
    simp only [hpow] at hg
    have hprod : ∏ i, X i ω ^ e i = (∏ i, c i ^ e i) * ∏ i, (X i ω / c i) ^ e i := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [div_pow, mul_div_cancel₀ _ (pow_ne_zero _ (hc i).ne')]
    rw [hprod]
    exact mul_le_mul_of_nonneg_left hg hC.le
  have h1 := wavg_mono' hw (fun ω _ => hpt ω)
  rw [wavg_const_mul, wavg_sum] at h1
  refine h1.trans ?_
  have h2 : ∑ i, wavg w (fun ω => (e i : ℝ) / n * (X i ω / c i) ^ n) ≤ ∑ i, (e i : ℝ) / n := by
    refine Finset.sum_le_sum fun i _ => ?_
    rw [wavg_const_mul]
    rcases Nat.eq_zero_or_pos (e i) with h0 | hpos
    · rw [h0]; simp
    · have hm := hm i hpos
      have e1 : wavg w (fun ω => (X i ω / c i) ^ n) = wavg w (fun ω => X i ω ^ n) / c i ^ n := by
        simp only [div_pow]
        rw [show (fun ω => X i ω ^ n / c i ^ n) = fun ω => (c i ^ n)⁻¹ * X i ω ^ n by
          funext ω; rw [div_eq_inv_mul], wavg_const_mul, inv_mul_eq_div]
      rw [e1]
      have : wavg w (fun ω => X i ω ^ n) / c i ^ n ≤ 1 :=
        (div_le_one (pow_pos (hc i) n)).2 hm
      have h3 : (0 : ℝ) ≤ (e i : ℝ) / n := by positivity
      nlinarith
  have hsum : ∑ i, (e i : ℝ) / n = 1 := by
    rw [← Finset.sum_div, div_eq_one_iff_eq hn0.ne']
    exact_mod_cast hn
  rw [hsum] at h2
  nlinarith

end SecA

end BiluLinial.Tight
