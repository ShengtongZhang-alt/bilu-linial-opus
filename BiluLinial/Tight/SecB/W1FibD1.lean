/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecB.W1FibReg
public import BiluLinial.Tight.SecB.W1FibD1Pair

/-!
# The weak loop (W1), edge fibres: the endpoint derivatives (TB.W1fib-d1)

Node TB.W1fib-d1 of `docs/tight/BP_SECB.md`: `φ'(±1) = W DΨ` at the two endpoints of a fibre.
Definitions, sketches and the other sub-nodes: `BiluLinial.Tight.SecB.W1FibReg`.

Proof: near the endpoint `t₀ = ±1` the fibre is the pencil
`P̃^±(t) = P̃^±(τ₀) ± (t - t₀) a√(y_iy_j) E` (`precT_recenter`), and `wd1_deriv_pair`
(`SecB/W1FibD1Pair.lean`) computes the derivative of `(det P̃⁺ det P̃⁻)^p Ψ` there as
`(det P̃⁺ det P̃⁻)^p · DΨ` (`wd1_obsD_precN`); at a positive definite endpoint the weight is
`W = (det P̃⁺ det P̃⁻)^p`.
-/

@[expose] public section

namespace BiluLinial.Tight.SecB

open Matrix

universe u

/-- **TB.W1fib-d1** at `t = 1`: `φ'(1) = W(σ) DΨ(σ)`. Sketch: module docstring. -/
theorem fibPhi_deriv_one {d p : ℕ} (ct : Contact.{u} d p) {h : ℝ} (hh : 0 ≤ h) (k : Fin 4)
    {i j : ct.V} (hi : i ∈ ct.N) (hj : j ∈ nbhd ct.G ct.S i) {σ : Config ct.V}
    (he : σ s(i, j) = 1)
    (hPD : (precN ct.G (aOf d p) 1 ct.yp σ ct.S).PosDef ∧
      (precN ct.G (aOf d p) (-1) ct.ym σ ct.S).PosDef) :
    deriv (fibPhi ct h k i j σ) 1 =
      wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S * cfgD ct h k i j σ := by
  have hij : ct.G.Adj i j := (Finset.mem_filter.mp hj).2
  have hp' : ∀ t, fibPp ct σ i j t = precN ct.G (aOf d p) 1 ct.yp σ ct.S +
      ((t - 1) * (1 * aOf d p * (Real.sqrt (ct.yp i) * Real.sqrt (ct.yp j)))) •
        SecA.edgeE i j := by
    intro t
    rw [fibPp, precT_recenter _ _ _ _ _ _ _ _ t 1]
    congr 1
    exact fibPp_one ct he
  have hm' : ∀ t, fibPm ct σ i j t = precN ct.G (aOf d p) (-1) ct.ym σ ct.S +
      ((t - 1) * (-1 * aOf d p * (Real.sqrt (ct.ym i) * Real.sqrt (ct.ym j)))) •
        SecA.edgeE i j := by
    intro t
    rw [fibPm, precT_recenter _ _ _ _ _ _ _ _ t 1]
    congr 1
    exact fibPm_one ct he
  have H := (wd1_deriv_pair ct hh k (ct.G.ne_of_adj hij) hPD.1 hPD.2 1).congr_of_eventuallyEq
    (f₁ := fibPhi ct h k i j σ)
    (Filter.Eventually.of_forall fun t => by rw [fibPhi, hp' t, hm' t])
  rw [H.deriv, wd1_obsD_precN, wt, ite_eq_left hPD]

/-- **TB.W1fib-d1** at `t = -1`: `φ'(-1) = W(σ') DΨ(σ')`. Sketch: module docstring. -/
theorem fibPhi_deriv_neg_one {d p : ℕ} (ct : Contact.{u} d p) {h : ℝ} (hh : 0 ≤ h) (k : Fin 4)
    {i j : ct.V} (hi : i ∈ ct.N) (hj : j ∈ nbhd ct.G ct.S i) {σ : Config ct.V}
    (he : σ s(i, j) = 1)
    (hPD : (precN ct.G (aOf d p) 1 ct.yp (fibFlip ct σ i j) ct.S).PosDef ∧
      (precN ct.G (aOf d p) (-1) ct.ym (fibFlip ct σ i j) ct.S).PosDef) :
    deriv (fibPhi ct h k i j σ) (-1) =
      wt ct.G p (aOf d p) ct.yp ct.ym (fibFlip ct σ i j) ct.S *
        cfgD ct h k i j (fibFlip ct σ i j) := by
  have hiS : i ∈ ct.S := w1_N_sub_S ct hi
  have hjS : j ∈ ct.S := (Finset.mem_filter.mp hj).1
  have hij : ct.G.Adj i j := (Finset.mem_filter.mp hj).2
  have hp' : ∀ t, fibPp ct σ i j t =
      precN ct.G (aOf d p) 1 ct.yp (fibFlip ct σ i j) ct.S +
        ((t - -1) * (1 * aOf d p * (Real.sqrt (ct.yp i) * Real.sqrt (ct.yp j)))) •
          SecA.edgeE i j := by
    intro t
    rw [fibPp, precT_recenter _ _ _ _ _ _ _ _ t (-1)]
    congr 1
    exact fibPp_neg_one ct hiS hjS hij
  have hm' : ∀ t, fibPm ct σ i j t =
      precN ct.G (aOf d p) (-1) ct.ym (fibFlip ct σ i j) ct.S +
        ((t - -1) * (-1 * aOf d p * (Real.sqrt (ct.ym i) * Real.sqrt (ct.ym j)))) •
          SecA.edgeE i j := by
    intro t
    rw [fibPm, precT_recenter _ _ _ _ _ _ _ _ t (-1)]
    congr 1
    exact fibPm_neg_one ct hiS hjS hij
  have H := (wd1_deriv_pair ct hh k (ct.G.ne_of_adj hij) hPD.1 hPD.2 (-1)).congr_of_eventuallyEq
    (f₁ := fibPhi ct h k i j σ)
    (Filter.Eventually.of_forall fun t => by rw [fibPhi, hp' t, hm' t])
  rw [H.deriv, wd1_obsD_precN, wt, ite_eq_left hPD]

end BiluLinial.Tight.SecB
