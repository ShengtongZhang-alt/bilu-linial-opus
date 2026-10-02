/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecB.W1FibD3W

/-!
# The weak loop (W1), edge fibres: the third-derivative bound (TB.W1fib-d3)

Node TB.W1fib-d3 of `docs/tight/BP_SECB.md`: `|φ'''| ≤ K (W(σ)Yb(σ) + W(σ')Yb(σ'))` on a regular fibre.
Definitions, sketches and the other sub-nodes: `BiluLinial.Tight.SecB.W1FibReg`.

Proof (`d3_at`): let `τ₀` be the good endpoint and `t₀ = ±1` its edge value, so that
`P̃^±(t) = P̃^±(τ₀) + (t - t₀)(±a)√(y_iy_j) E` (`fibPp_rec1`, `fibPp_rec2`, …). On `U = (-2, 2)`
(`|t - t₀| ≤ 3`) `φ = W·Ψ` with the jets of `SecB/W1FibD3W.lean` (`W = W(τ₀)(δ₊δ₋)^p`, p-structured
bounds) and `SecB/W1FibD3Psi2.lean` (`|Ψ^{(r)}| ≤ 4718592 Q⁸/(√d h)(aD)^r`, `Q = 2661121 D³`,
Woodbury along the edge); `φ''' = W'''Ψ + 3W''Ψ' + 3W'Ψ'' + WΨ'''` (`jmul`) and `d3_combine` give
`|φ'''| ≤ 10⁶·4718592·2661121⁸ · W(τ₀) a³D³⁰(p³R² + p)/(√d h) = K W(τ₀) Yb(τ₀)` with `M = 30`.
-/

@[expose] public section

namespace BiluLinial.Tight.SecB

open Matrix

universe u

section D3

variable {d p : ℕ} (ct : Contact.{u} d p)

theorem fibPp_rec1 {σ : Config ct.V} {i j : ct.V} (he : σ s(i, j) = 1) (t : ℝ) :
    fibPp ct σ i j t = precN ct.G (aOf d p) 1 ct.yp σ ct.S +
      ((t - 1) * (1 * aOf d p * (Real.sqrt (ct.yp i) * Real.sqrt (ct.yp j)))) • SecA.edgeE i j := by
  rw [fibPp, precT_recenter _ _ _ _ _ _ _ _ t 1]
  congr 1
  exact fibPp_one ct he

theorem fibPm_rec1 {σ : Config ct.V} {i j : ct.V} (he : σ s(i, j) = 1) (t : ℝ) :
    fibPm ct σ i j t = precN ct.G (aOf d p) (-1) ct.ym σ ct.S +
      ((t - 1) * (-1 * aOf d p * (Real.sqrt (ct.ym i) * Real.sqrt (ct.ym j)))) •
        SecA.edgeE i j := by
  rw [fibPm, precT_recenter _ _ _ _ _ _ _ _ t 1]
  congr 1
  exact fibPm_one ct he

theorem fibPp_rec2 {σ : Config ct.V} {i j : ct.V} (hi : i ∈ ct.S) (hj : j ∈ ct.S)
    (hij : ct.G.Adj i j) (t : ℝ) :
    fibPp ct σ i j t = precN ct.G (aOf d p) 1 ct.yp (fibFlip ct σ i j) ct.S +
      ((t - -1) * (1 * aOf d p * (Real.sqrt (ct.yp i) * Real.sqrt (ct.yp j)))) •
        SecA.edgeE i j := by
  rw [fibPp, precT_recenter _ _ _ _ _ _ _ _ t (-1)]
  congr 1
  exact fibPp_neg_one ct hi hj hij

theorem fibPm_rec2 {σ : Config ct.V} {i j : ct.V} (hi : i ∈ ct.S) (hj : j ∈ ct.S)
    (hij : ct.G.Adj i j) (t : ℝ) :
    fibPm ct σ i j t = precN ct.G (aOf d p) (-1) ct.ym (fibFlip ct σ i j) ct.S +
      ((t - -1) * (-1 * aOf d p * (Real.sqrt (ct.ym i) * Real.sqrt (ct.ym j)))) •
        SecA.edgeE i j := by
  rw [fibPm, precT_recenter _ _ _ _ _ _ _ _ t (-1)]
  congr 1
  exact fibPm_neg_one ct hi hj hij

/-- The bound at a good endpoint `τ₀` with edge value `t₀`. -/
theorem d3_at {h : ℝ} (hh : 0 < h) (hR : TRegime d p) {i j : ct.V} (hi : i ∈ ct.N)
    (hj : j ∈ nbhd ct.G ct.S i) (k : Fin 4) {σ τ₀ : Config ct.V} (hg : fibGood ct i j τ₀)
    {t₀ : ℝ} (ht₀ : |t₀| ≤ 1)
    (hrp : ∀ t, fibPp ct σ i j t = precN ct.G (aOf d p) 1 ct.yp τ₀ ct.S +
      ((t - t₀) * (1 * aOf d p * (Real.sqrt (ct.yp i) * Real.sqrt (ct.yp j)))) • SecA.edgeE i j)
    (hrm : ∀ t, fibPm ct σ i j t = precN ct.G (aOf d p) (-1) ct.ym τ₀ ct.S +
      ((t - t₀) * (-1 * aOf d p * (Real.sqrt (ct.ym i) * Real.sqrt (ct.ym j)))) •
        SecA.edgeE i j)
    {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    |iteratedDeriv 3 (fibPhi ct h k i j σ) t| ≤
      1000000 * 4718592 * 2661121 ^ 8 *
        (wt ct.G p (aOf d p) ct.yp ct.ym τ₀ ct.S * fibYb ct 30 h i j τ₀) := by
  set U : Set ℝ := Set.Ioo (-2) 2 with hUdef
  have hU : ∀ s ∈ U, |s - t₀| ≤ 3 := fun s hs => by
    obtain ⟨h1, h2⟩ := abs_le.mp ht₀
    rw [abs_le]; constructor <;> linarith [hs.1, hs.2]
  have htU : t ∈ U := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  obtain ⟨FW, hFWj, hFWb⟩ := d3_W_jet ct hh hR hi hj hg hU
  obtain ⟨FP, hFP⟩ := d3_psi_jet ct hh hR hi hj hg hU k
  have hJ : JetOf U (fibPhi ct h k i j σ) (jmul FW FP) :=
    (hFWj.mul hFP.1).congr fun s _ => by simp only [fibPhi, hrp, hrm]
  rw [hJ.iteratedDeriv_eq isOpen_Ioo 3 le_rfl t htU]
  change |FW 3 t * FP 0 t + 3 * (FW 2 t * FP 1 t) + 3 * (FW 1 t * FP 2 t) + FW 0 t * FP 3 t| ≤ _
  -- parameters
  have hw := hg.1
  have hiB := w1Ball_N ct hi
  have hjB := w1Ball_NN ct hi hj
  have hD1 := w1_Dstar_ge_one ct hw
  have ha := hR.aOf_pos
  have hd : (0 : ℝ) < d := by have := hR.ten_pow_six_le_d; linarith
  have ha2 := hR.pf_a_sq_le
  have ha1 : aOf d p ≤ 1 := by
    have : 1 / (d : ℝ) ≤ 1 := by rw [div_le_one hd]; have := hR.ten_pow_six_le_d; linarith
    nlinarith
  have hp1 : (1 : ℝ) ≤ p := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hR.two_le_p
    linarith
  have hPa : (p : ℝ) * aOf d p ≤ 1 := by
    have h8 := regime_p8_le hR
    have h2 : (p : ℝ) ^ 2 ≤ d := (pow_le_pow_right₀ hp1 (by norm_num : 2 ≤ 8)).trans h8
    have hsq : ((p : ℝ) * aOf d p) ^ 2 ≤ 1 := by
      have e : ((p : ℝ) * aOf d p) ^ 2 = (p : ℝ) ^ 2 * aOf d p ^ 2 := by ring
      rw [e]
      calc (p : ℝ) ^ 2 * aOf d p ^ 2 ≤ d * (1 / d) :=
            mul_le_mul h2 ha2 (sq_nonneg _) (Nat.cast_nonneg d)
        _ = 1 := by field_simp
    have h0 : 0 ≤ (p : ℝ) * aOf d p := by positivity
    nlinarith
  have hR0 : 0 ≤ fibR ct τ₀ i j := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hR2 : fibR ct τ₀ i j ≤ 2 * ct.Dstar τ₀ := by
    have := (w1_g_off_le ct hw hiB hjB).1
    have := (w1_g_off_le ct hw hiB hjB).2
    unfold fibR
    linarith
  have hW0 : 0 ≤ wt ct.G p (aOf d p) ct.yp ct.ym τ₀ ct.S := wt_nonneg ct.G τ₀
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd
  have hA0 : 0 ≤ 4718592 * (2661121 * ct.Dstar τ₀ ^ 3) ^ 8 / (Real.sqrt d * h) := by positivity
  obtain ⟨w0, w1, w2, w3⟩ := hFWb t htU
  have key := d3_combine hW0 hA0 ha.le ha1 hD1 hR0 hR2 hp1 hPa w0 w1 w2 w3
    (hFP.2 0 (by norm_num) t htU) (hFP.2 1 (by norm_num) t htU) (hFP.2 2 (by norm_num) t htU)
    (hFP.2 3 le_rfl t htU)
  refine key.trans (le_of_eq ?_)
  unfold fibYb
  field_simp

end D3

/-- **TB.W1fib-d3** (third-derivative bound). There are `K > 0` and `M` such that eventually, on
every regular fibre, `|φ'''(t)| ≤ K (W(σ)Yb(σ) + W(σ')Yb(σ'))` for `t ∈ [-1, 1]`. Proof: `d3_at` at
the good endpoint (`K = 10⁶·4718592·2661121⁸`, `M = 30`). -/
theorem fibPhi_d3 :
    ∃ K : ℝ, 0 < K ∧ ∃ M : ℕ, Eventually fun _c₀ _κ₀ d p h => ∀ ct : Contact.{u} d p,
      ∀ i ∈ ct.N, ∀ j ∈ nbhd ct.G ct.S i, ∀ k : Fin 4, ∀ σ : Config ct.V, σ s(i, j) = 1 →
      (fibGood ct i j σ ∨ fibGood ct i j (fibFlip ct σ i j)) →
      ∀ t ∈ Set.Icc (-1 : ℝ) 1, |iteratedDeriv 3 (fibPhi ct h k i j σ) t| ≤
        K * (wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S * fibYb ct M h i j σ +
          wt ct.G p (aOf d p) ct.yp ct.ym (fibFlip ct σ i j) ct.S *
            fibYb ct M h i j (fibFlip ct σ i j)) := by
  refine ⟨1000000 * 4718592 * 2661121 ^ 8, by positivity, 30, eventually_h_facts.mono ?_⟩
  rintro c₀ κ₀ d p h ⟨hR, h0, -, -, -⟩ ct i hi j hj k σ he hreg t ht
  have hiS := w1_N_sub_S ct hi
  have hjS : j ∈ ct.S := (Finset.mem_filter.mp hj).1
  have hij : ct.G.Adj i j := (Finset.mem_filter.mp hj).2
  have n1 := wt_fibYb_nonneg ct 30 h0 i j σ
  have n2 := wt_fibYb_nonneg ct 30 h0 i j (fibFlip ct σ i j)
  have hK : (0 : ℝ) ≤ 1000000 * 4718592 * 2661121 ^ 8 := by positivity
  rcases hreg with hg | hg
  · have := d3_at ct h0 hR hi hj k hg (t₀ := 1) (by norm_num) (fibPp_rec1 ct he)
      (fibPm_rec1 ct he) ht
    refine this.trans (mul_le_mul_of_nonneg_left ?_ hK)
    linarith
  · have := d3_at ct h0 hR hi hj k hg (t₀ := -1) (by norm_num) (fibPp_rec2 ct hiS hjS hij)
      (fibPm_rec2 ct hiS hjS hij) ht
    refine this.trans (mul_le_mul_of_nonneg_left ?_ hK)
    linarith

end BiluLinial.Tight.SecB
