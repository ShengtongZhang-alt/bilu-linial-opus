/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecB.W1FibD1
public import BiluLinial.Tight.SecB.W1FibD3

/-!
# The weak loop (W1), edge fibres: the regular-fibre node (TB.W1fib-reg)

Node TB.W1fib-reg of `docs/tight/BP_SECB.md`, proved from TB.W1fib-seg, TB.W1fib-smooth, the endpoint values, TB.W1fib-d1 and TB.W1fib-d3. Definitions, sketches and the other sub-nodes: `BiluLinial.Tight.SecB.W1FibReg`.
-/

@[expose] public section

namespace BiluLinial.Tight.SecB

open Matrix

universe u

/-! ### Assembly -/

/-- **TB.W1fib-reg** (regular fibres). There are `K > 0` and `M` such that eventually, at every
contact, edge `ij` (`i ∈ N`, `j ∼ i`), configuration `k` and signing `σ` with `σ_ij = 1` whose
fibre has a good endpoint, the edge-interpolated `φ = WΨ` is a `FibChain` for `(WΨ, W DΨ)` with
`|φ'''| ≤ K (W(σ)Yb(σ) + W(σ')Yb(σ'))`. Proof: `fibChain_of_contDiffOn` on `U = (-2, 2)` with
TB.W1fib-seg, TB.W1fib-smooth, the endpoint values, TB.W1fib-d1 and TB.W1fib-d3. -/
theorem weak_fibre_reg :
    ∃ K : ℝ, 0 < K ∧ ∃ M : ℕ, Eventually fun _c₀ _κ₀ d p h => ∀ ct : Contact.{u} d p,
      ∀ i ∈ ct.N, ∀ j ∈ nbhd ct.G ct.S i, ∀ k : Fin 4, ∀ σ : Config ct.V, σ s(i, j) = 1 →
      (fibGood ct i j σ ∨ fibGood ct i j (fibFlip ct σ i j)) →
      FibChain (fun τ => wt ct.G p (aOf d p) ct.yp ct.ym τ ct.S * cfgPsi ct h k i j τ)
        (fun τ => wt ct.G p (aOf d p) ct.yp ct.ym τ ct.S * cfgD ct h k i j τ) σ (fibFlip ct σ i j)
        (K * (wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S * fibYb ct M h i j σ +
          wt ct.G p (aOf d p) ct.yp ct.ym (fibFlip ct σ i j) ct.S *
            fibYb ct M h i j (fibFlip ct σ i j))) := by
  obtain ⟨K, hK, M, hd3⟩ := fibPhi_d3.{u}
  refine ⟨K, hK, M, (hd3.and eventually_h_facts).mono ?_⟩
  rintro c₀ κ₀ d p h ⟨hB, hR, h0, -⟩ ct i hi j hj k σ he hreg
  have hp : 1 ≤ p := le_trans (by norm_num) hR.hp
  have hiS := w1_N_sub_S ct hi
  have hjS : j ∈ ct.S := (Finset.mem_filter.mp hj).1
  have hij : ct.G.Adj i j := (Finset.mem_filter.mp hj).2
  have hseg : ∀ t ∈ Set.Icc (-2 : ℝ) 2, (fibPp ct σ i j t).PosDef ∧ (fibPm ct σ i j t).PosDef :=
    fun t ht => fib_seg_pd ct hp hi hj he hreg ht
  have hPD1 : (precN ct.G (aOf d p) 1 ct.yp σ ct.S).PosDef ∧
      (precN ct.G (aOf d p) (-1) ct.ym σ ct.S).PosDef := by
    have := hseg 1 ⟨by norm_num, by norm_num⟩
    rwa [fibPp_one ct he, fibPm_one ct he] at this
  have hPD2 : (precN ct.G (aOf d p) 1 ct.yp (fibFlip ct σ i j) ct.S).PosDef ∧
      (precN ct.G (aOf d p) (-1) ct.ym (fibFlip ct σ i j) ct.S).PosDef := by
    have := hseg (-1) ⟨by norm_num, by norm_num⟩
    rwa [fibPp_neg_one ct hiS hjS hij, fibPm_neg_one ct hiS hjS hij] at this
  exact fibChain_of_contDiffOn isOpen_Ioo
    (fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    (fibPhi_contDiffOn ct h0.le k i j σ fun t ht => hseg t ⟨ht.1.le, ht.2.le⟩)
    (fibPhi_one ct h k he hPD1) (fibPhi_neg_one ct h k hiS hjS hij hPD2)
    (fibPhi_deriv_one ct h0.le k hi hj he hPD1) (fibPhi_deriv_neg_one ct h0.le k hi hj he hPD2)
    (hB ct i hi j hj k σ he hreg)

end BiluLinial.Tight.SecB
