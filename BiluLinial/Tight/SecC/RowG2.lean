/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecC.RowG12Mom

/-!
# Row comparison, grade two (node CR-G2 of `docs/tight/BP_SECC.md`)

The retained multi-indices of grade two, `j = 3e_i` and `j = 2e_i + 2e_k`. See
`BiluLinial.Tight.SecC.RowGrades` for the parent CR-GR and the orders-of-magnitude checks.

**Proof.** The grade-two retained indices are among the `3e_i` and the `2e_i + 2e_k`, `i ≠ k`
(`g12_sum_grade2_le`), with `|c_j| ≤ 1`; `∂^{2j}` is `∂_i⁶` or `∂_i⁴∂_k⁴` in either order
(`g12_dEven_single`, `g12_dEven_pair`; the T.MARK bound is symmetric, `g12Bm_comm`). At a
supported signing (`g12_grade2_pt`): the diagonal terms give
`10⁶p⁹a² · 4a² (U₆⁺ + √U₆⁺ √U₆⁻)`, `U₆^± = Σ_i (1 + r_i)⁶ X^±_i`, and the pairs give
`10⁶p⁹a² · 16a² (T⁺ + √T⁺ √T⁻)`, `T^± = Σ_i W (1 + r_i)⁴ X^±_i` (`g12_sum_pair_le`:
`Y^±_{ik} ≤ 2(X^±_i + X^±_k)`, Cauchy–Schwarz over pairs, `Σ_{k} a²(1 + r_k)⁴ = W`). Under the law
`g12_EU_le` bounds both by `2e²B_Y K √(λ_c δ_c)`, and `p⁹a⁴ ≤ p⁴a²` (`p⁵ ≤ d`, `d a² ≤ 1/2`).
-/

@[expose] public section

namespace BiluLinial.Tight

namespace SecC

universe u

open Matrix

/-- The pair sum: `Σ_{i ≠ k} a⁴ w_i w_k · 4 (Y⁺ + √Y⁺ √Y⁻) ≤ 16 a² (T⁺ + √T⁺ √T⁻)`, where
`Y^± = 2 (X^±_i + X^±_k)` and `T^± = Σ_i (a² Σ_k w_k) w_i X^±_i`. -/
theorem g12_sum_pair_le {ι : Type*} [Fintype ι] (a : ℝ) (w P M : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hP : ∀ i, 0 ≤ P i) (hM : ∀ i, 0 ≤ M i) :
    ∑ ik ∈ (Finset.univ : Finset ι).offDiag, a ^ 4 * w ik.1 * w ik.2 *
        (4 * (2 * (P ik.1 + P ik.2) +
          Real.sqrt (2 * (P ik.1 + P ik.2)) * Real.sqrt (2 * (M ik.1 + M ik.2)))) ≤
      16 * a ^ 2 * (∑ i, (a ^ 2 * ∑ k, w k) * w i * P i +
        Real.sqrt (∑ i, (a ^ 2 * ∑ k, w k) * w i * P i) *
          Real.sqrt (∑ i, (a ^ 2 * ∑ k, w k) * w i * M i)) := by
  have hsub : (Finset.univ : Finset ι).offDiag ⊆ Finset.univ ×ˢ Finset.univ := fun ik _ =>
    Finset.mem_product.2 ⟨Finset.mem_univ _, Finset.mem_univ _⟩
  have hext : ∀ F : ι × ι → ℝ, (∀ ik, 0 ≤ F ik) →
      ∑ ik ∈ (Finset.univ : Finset ι).offDiag, F ik ≤ ∑ i, ∑ k, F (i, k) := fun F hF =>
    (Finset.sum_le_sum_of_subset_of_nonneg hsub fun ik _ _ => hF ik).trans_eq
      (Finset.sum_product _ _ _)
  have key : ∀ Pf : ι → ℝ, ∑ i, ∑ k, a ^ 4 * w i * w k * (2 * (Pf i + Pf k)) =
      4 * a ^ 2 * ∑ i, (a ^ 2 * ∑ k, w k) * w i * Pf i := by
    intro Pf
    have h1 : ∑ i, ∑ k, a ^ 4 * w i * w k * (2 * (Pf i + Pf k)) =
        2 * ∑ i, ∑ k, a ^ 4 * w i * w k * Pf i + 2 * ∑ i, ∑ k, a ^ 4 * w i * w k * Pf k := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    have h2 : ∑ i, ∑ k, a ^ 4 * w i * w k * Pf k = ∑ i, ∑ k, a ^ 4 * w i * w k * Pf i := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
    have h3 : ∑ i, ∑ k, a ^ 4 * w i * w k * Pf i =
        a ^ 2 * ∑ i, (a ^ 2 * ∑ k, w k) * w i * Pf i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [h1, h2, h3]
    ring
  have hc0 : ∀ ik : ι × ι, 0 ≤ a ^ 4 * w ik.1 * w ik.2 := fun ik => by
    have := hw ik.1
    have := hw ik.2
    positivity
  have hYp : ∀ ik : ι × ι, 0 ≤ 2 * (P ik.1 + P ik.2) := fun ik => by
    have := hP ik.1
    have := hP ik.2
    positivity
  have hYm : ∀ ik : ι × ι, 0 ≤ 2 * (M ik.1 + M ik.2) := fun ik => by
    have := hM ik.1
    have := hM ik.2
    positivity
  set Tp := ∑ i, (a ^ 2 * ∑ k, w k) * w i * P i with hTp
  set Tm := ∑ i, (a ^ 2 * ∑ k, w k) * w i * M i with hTm
  have hVp : ∑ ik ∈ (Finset.univ : Finset ι).offDiag,
      a ^ 4 * w ik.1 * w ik.2 * (2 * (P ik.1 + P ik.2)) ≤ 4 * a ^ 2 * Tp :=
    (hext _ fun ik => mul_nonneg (hc0 ik) (hYp ik)).trans_eq (key P)
  have hVm : ∑ ik ∈ (Finset.univ : Finset ι).offDiag,
      a ^ 4 * w ik.1 * w ik.2 * (2 * (M ik.1 + M ik.2)) ≤ 4 * a ^ 2 * Tm :=
    (hext _ fun ik => mul_nonneg (hc0 ik) (hYm ik)).trans_eq (key M)
  have hCS := g12_sum_wsqrt_le (Finset.univ : Finset ι).offDiag
    (fun ik => a ^ 4 * w ik.1 * w ik.2) (fun ik => 2 * (P ik.1 + P ik.2))
    (fun ik => 2 * (M ik.1 + M ik.2)) hc0 hYp hYm
  have hsplit : ∑ ik ∈ (Finset.univ : Finset ι).offDiag, a ^ 4 * w ik.1 * w ik.2 *
        (4 * (2 * (P ik.1 + P ik.2) +
          Real.sqrt (2 * (P ik.1 + P ik.2)) * Real.sqrt (2 * (M ik.1 + M ik.2)))) =
      4 * ∑ ik ∈ (Finset.univ : Finset ι).offDiag,
          a ^ 4 * w ik.1 * w ik.2 * (2 * (P ik.1 + P ik.2)) +
        4 * ∑ ik ∈ (Finset.univ : Finset ι).offDiag, a ^ 4 * w ik.1 * w ik.2 *
          (Real.sqrt (2 * (P ik.1 + P ik.2)) * Real.sqrt (2 * (M ik.1 + M ik.2))) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun ik _ => by ring
  have h4 : (0 : ℝ) ≤ 4 * a ^ 2 := by positivity
  rw [hsplit]
  calc _ ≤ 4 * (4 * a ^ 2 * Tp) +
        4 * (Real.sqrt (4 * a ^ 2 * Tp) * Real.sqrt (4 * a ^ 2 * Tm)) :=
        add_le_add (mul_le_mul_of_nonneg_left hVp (by norm_num))
          (mul_le_mul_of_nonneg_left (hCS.trans (mul_le_mul (Real.sqrt_le_sqrt hVp)
            (Real.sqrt_le_sqrt hVm) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))) (by norm_num))
    _ = 16 * a ^ 2 * (Tp + Real.sqrt Tp * Real.sqrt Tm) := by
        rw [← g12_sqrt_scale h4]
        ring

section Main

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable {d p : ℕ}

/-- `∂^{2j}F(ξ)/Φ(ξ)` at a signing (the integrand of `rowRet j`). -/
noncomputable def g12D (d p : ℕ) (yp ym : V → ℝ) (σ : Config V) (S : Finset V) (v : V)
    (j : nbhd G S v → ℕ) : ℝ :=
  dEven (Finset.univ : Finset (nbhd G S v)).toList j
      (rowNum p (rootMat G (aOf d p) 1 yp σ S v) (rootMat G (aOf d p) (-1) ym σ S v))
      (rootSigns G σ S v) /
    starPhi p (rootMat G (aOf d p) 1 yp σ S v) (rootMat G (aOf d p) (-1) ym σ S v)
      (rootSigns G σ S v)

/-- Pointwise grade-two bound at a supported signing. -/
theorem g12_grade2_pt (hR : TRegime d p) {S : Finset V} {yp ym : V → ℝ} (hyp : ∀ i, 0 ≤ yp i)
    (hym : ∀ i, 0 ≤ ym i) {v : V} (hv : v ∈ S) {σ : Config V}
    (hσ : wt G p (aOf d p) yp ym σ S ≠ 0) :
    ∑ i : nbhd G S v, |g12D G d p yp ym σ S v (Function.update 0 i 3)| +
        ∑ ik ∈ (Finset.univ : Finset (nbhd G S v)).offDiag,
          |g12D G d p yp ym σ S v (Function.update (Function.update 0 ik.1 2) ik.2 2)| ≤
      10 ^ 6 * (p : ℝ) ^ 9 * aOf d p ^ 2 *
        (4 * aOf d p ^ 2 *
            (∑ i, (1 + g12r G d p yp ym σ S v i) ^ 6 * g12Xb G d p 1 yp σ S v i +
              Real.sqrt (∑ i, (1 + g12r G d p yp ym σ S v i) ^ 6 * g12Xb G d p 1 yp σ S v i) *
                Real.sqrt (∑ i, (1 + g12r G d p yp ym σ S v i) ^ 6 *
                  g12Xb G d p (-1) ym σ S v i)) +
          16 * aOf d p ^ 2 *
            (∑ i, (rowWt G d p yp ym σ S v * (1 + g12r G d p yp ym σ S v i) ^ 4) *
                g12Xb G d p 1 yp σ S v i +
              Real.sqrt (∑ i, (rowWt G d p yp ym σ S v * (1 + g12r G d p yp ym σ S v i) ^ 4) *
                g12Xb G d p 1 yp σ S v i) *
              Real.sqrt (∑ i, (rowWt G d p yp ym σ S v * (1 + g12r G d p yp ym σ S v i) ^ 4) *
                g12Xb G d p (-1) ym σ S v i))) := by
  have ha := hR.aOf_pos
  have hp8 : 8 ≤ p := le_trans (by norm_num) hR.hp
  obtain ⟨hA, hB, hα, hβ⟩ := g12_supp G hR hyp hym hv hσ
  have hK : (0 : ℝ) ≤ 10 ^ 6 * (p : ℝ) ^ 9 * aOf d p ^ 2 := by positivity
  have hdiag : ∀ i : nbhd G S v, |g12D G d p yp ym σ S v (Function.update 0 i 3)| ≤
      10 ^ 6 * (p : ℝ) ^ 9 * aOf d p ^ 2 * (aOf d p ^ 2 * (1 + g12r G d p yp ym σ S v i) ^ 6 *
        (4 * (g12Xb G d p 1 yp σ S v i + Real.sqrt (g12Xb G d p 1 yp σ S v i) *
          Real.sqrt (g12Xb G d p (-1) ym σ S v i)))) := by
    intro i
    have h := g12_grade2d_star hp8 ha hA hB hα hβ i
    rw [g12P_eq, g12M_eq] at h
    unfold g12D
    rw [g12_dEven_single (Finset.nodup_toList _) (Finset.mem_toList.2 (Finset.mem_univ i)) 3]
    exact h
  have hmix : ∀ ik ∈ (Finset.univ : Finset (nbhd G S v)).offDiag,
      |g12D G d p yp ym σ S v (Function.update (Function.update 0 ik.1 2) ik.2 2)| ≤
        10 ^ 6 * (p : ℝ) ^ 9 * aOf d p ^ 2 *
          (aOf d p ^ 4 * (1 + g12r G d p yp ym σ S v ik.1) ^ 4 *
            (1 + g12r G d p yp ym σ S v ik.2) ^ 4 *
            (4 * (2 * (g12Xb G d p 1 yp σ S v ik.1 + g12Xb G d p 1 yp σ S v ik.2) +
              Real.sqrt (2 * (g12Xb G d p 1 yp σ S v ik.1 + g12Xb G d p 1 yp σ S v ik.2)) *
                Real.sqrt (2 * (g12Xb G d p (-1) ym σ S v ik.1 +
                  g12Xb G d p (-1) ym σ S v ik.2))))) := by
    intro ik hik
    have hne := (Finset.mem_offDiag.1 hik).2.2
    have hB1 := g12_grade2m_star hp8 ha hA hB hα hβ hne
    have hB2 := g12_grade2m_star hp8 ha hA hB hα hβ (Ne.symm hne)
    rw [g12Bm_comm] at hB2
    unfold g12Bm at hB1 hB2
    simp only [g12P_eq, g12M_eq] at hB1 hB2
    unfold g12D
    rcases g12_dEven_pair (Finset.nodup_toList _) (Finset.mem_toList.2 (Finset.mem_univ ik.1))
      (Finset.mem_toList.2 (Finset.mem_univ ik.2)) hne
      (rowNum p (rootMat G (aOf d p) 1 yp σ S v) (rootMat G (aOf d p) (-1) ym σ S v)) with h | h
    · rw [h]
      exact hB2
    · rw [h]
      exact hB1
  have hd : ∑ i : nbhd G S v, |g12D G d p yp ym σ S v (Function.update 0 i 3)| ≤
      10 ^ 6 * (p : ℝ) ^ 9 * aOf d p ^ 2 * (4 * aOf d p ^ 2 *
        (∑ i, (1 + g12r G d p yp ym σ S v i) ^ 6 * g12Xb G d p 1 yp σ S v i +
          Real.sqrt (∑ i, (1 + g12r G d p yp ym σ S v i) ^ 6 * g12Xb G d p 1 yp σ S v i) *
            Real.sqrt (∑ i, (1 + g12r G d p yp ym σ S v i) ^ 6 *
              g12Xb G d p (-1) ym σ S v i))) := by
    have hCS := g12_sum_wsqrt_le Finset.univ (fun i => (1 + g12r G d p yp ym σ S v i) ^ 6)
      (fun i => g12Xb G d p 1 yp σ S v i) (fun i => g12Xb G d p (-1) ym σ S v i)
      (fun i => by positivity) (fun i => g12Xb_nonneg G d p 1 yp σ S v i)
      (fun i => g12Xb_nonneg G d p (-1) ym σ S v i)
    calc _ ≤ ∑ i : nbhd G S v, 10 ^ 6 * (p : ℝ) ^ 9 * aOf d p ^ 2 *
          (aOf d p ^ 2 * (1 + g12r G d p yp ym σ S v i) ^ 6 *
            (4 * (g12Xb G d p 1 yp σ S v i + Real.sqrt (g12Xb G d p 1 yp σ S v i) *
              Real.sqrt (g12Xb G d p (-1) ym σ S v i)))) :=
          Finset.sum_le_sum fun i _ => hdiag i
      _ = 10 ^ 6 * (p : ℝ) ^ 9 * aOf d p ^ 2 * (4 * aOf d p ^ 2) *
            (∑ i, (1 + g12r G d p yp ym σ S v i) ^ 6 * g12Xb G d p 1 yp σ S v i +
              ∑ i, (1 + g12r G d p yp ym σ S v i) ^ 6 *
                (Real.sqrt (g12Xb G d p 1 yp σ S v i) *
                  Real.sqrt (g12Xb G d p (-1) ym σ S v i))) := by
          rw [← Finset.sum_add_distrib, Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ ≤ 10 ^ 6 * (p : ℝ) ^ 9 * aOf d p ^ 2 * (4 * aOf d p ^ 2) *
            (∑ i, (1 + g12r G d p yp ym σ S v i) ^ 6 * g12Xb G d p 1 yp σ S v i +
              Real.sqrt (∑ i, (1 + g12r G d p yp ym σ S v i) ^ 6 * g12Xb G d p 1 yp σ S v i) *
                Real.sqrt (∑ i, (1 + g12r G d p yp ym σ S v i) ^ 6 *
                  g12Xb G d p (-1) ym σ S v i)) :=
          mul_le_mul_of_nonneg_left (add_le_add le_rfl hCS) (by positivity)
      _ = _ := by ring
  have hm : ∑ ik ∈ (Finset.univ : Finset (nbhd G S v)).offDiag,
      |g12D G d p yp ym σ S v (Function.update (Function.update 0 ik.1 2) ik.2 2)| ≤
      10 ^ 6 * (p : ℝ) ^ 9 * aOf d p ^ 2 * (16 * aOf d p ^ 2 *
        (∑ i, (rowWt G d p yp ym σ S v * (1 + g12r G d p yp ym σ S v i) ^ 4) *
            g12Xb G d p 1 yp σ S v i +
          Real.sqrt (∑ i, (rowWt G d p yp ym σ S v * (1 + g12r G d p yp ym σ S v i) ^ 4) *
            g12Xb G d p 1 yp σ S v i) *
          Real.sqrt (∑ i, (rowWt G d p yp ym σ S v * (1 + g12r G d p yp ym σ S v i) ^ 4) *
            g12Xb G d p (-1) ym σ S v i))) := by
    have hpair := g12_sum_pair_le (aOf d p) (fun i => (1 + g12r G d p yp ym σ S v i) ^ 4)
      (fun i => g12Xb G d p 1 yp σ S v i) (fun i => g12Xb G d p (-1) ym σ S v i)
      (fun i => by positivity) (fun i => g12Xb_nonneg G d p 1 yp σ S v i)
      (fun i => g12Xb_nonneg G d p (-1) ym σ S v i)
    calc _ ≤ ∑ ik ∈ (Finset.univ : Finset (nbhd G S v)).offDiag,
          10 ^ 6 * (p : ℝ) ^ 9 * aOf d p ^ 2 *
            (aOf d p ^ 4 * (1 + g12r G d p yp ym σ S v ik.1) ^ 4 *
              (1 + g12r G d p yp ym σ S v ik.2) ^ 4 *
              (4 * (2 * (g12Xb G d p 1 yp σ S v ik.1 + g12Xb G d p 1 yp σ S v ik.2) +
                Real.sqrt (2 * (g12Xb G d p 1 yp σ S v ik.1 + g12Xb G d p 1 yp σ S v ik.2)) *
                  Real.sqrt (2 * (g12Xb G d p (-1) ym σ S v ik.1 +
                    g12Xb G d p (-1) ym σ S v ik.2))))) := Finset.sum_le_sum hmix
      _ = 10 ^ 6 * (p : ℝ) ^ 9 * aOf d p ^ 2 *
            ∑ ik ∈ (Finset.univ : Finset (nbhd G S v)).offDiag,
              aOf d p ^ 4 * (1 + g12r G d p yp ym σ S v ik.1) ^ 4 *
                (1 + g12r G d p yp ym σ S v ik.2) ^ 4 *
                (4 * (2 * (g12Xb G d p 1 yp σ S v ik.1 + g12Xb G d p 1 yp σ S v ik.2) +
                  Real.sqrt (2 * (g12Xb G d p 1 yp σ S v ik.1 + g12Xb G d p 1 yp σ S v ik.2)) *
                    Real.sqrt (2 * (g12Xb G d p (-1) ym σ S v ik.1 +
                      g12Xb G d p (-1) ym σ S v ik.2)))) := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hpair hK
      _ = _ := rfl
  calc _ ≤ _ := add_le_add hd hm
    _ = _ := by ring

/-- CR-G2 at a fixed point of the regime, with explicit constant. -/
theorem g12_grade2_main (hR : TRegime d p) (hk : 32 * kIL d ≤ p) {S : Finset V} {lam : ℝ}
    (hC : CapCtx G d p S lam) {yp ym : V → ℝ} (hyp : InCube (lam * sOf d p) yp)
    (hym : InCube (lam * sOf d p) ym) {v : V} (hv : v ∈ S) {lr lc dc : ℝ} (hvl : vth d ≤ lr)
    (hlrc : lr ≤ lc) (hlcd : lc ≤ dc)
    (hS1 : incRowE G d p yp ym S v 1 yp / d ≤ lr)
    (hS2 : incRowE G d p yp ym S v (-1) ym / d ≤ dc)
    (hM1 : markE G d p yp ym S v 1 yp / (d : ℝ) ^ 2 ≤ lc)
    (hM2 : markE G d p yp ym S v (-1) ym / (d : ℝ) ^ 2 ≤ dc) :
    |∑ j ∈ (retIdx (kStar d p) : Finset (nbhd G S v → ℕ)).filter (fun j => grade j = 2),
        ecoefM j * rowRet G d p yp ym S v j| ≤
      aOf d p ^ 2 * (10 ^ 6 * (8 * (Real.exp 2 * (3 * 96 ^ 6) * g12K) +
          32 * (Real.exp 2 * (9 * 96 ^ 8) * g12K)) *
        ((p : ℝ) ^ 4 * Real.sqrt (lc * dc))) := by
  have hyp0 : ∀ i, 0 ≤ yp i := fun i => (hyp i).1
  have hym0 : ∀ i, 0 ≤ ym i := fun i => (hym i).1
  have hK := g12K_pos
  have hret : ∀ j, rowRet G d p yp ym S v j =
      lawE G p (aOf d p) yp ym S (fun σ => g12D G d p yp ym σ S v j) := fun j => rfl
  set T := (retIdx (kStar d p) : Finset (nbhd G S v → ℕ)).filter (fun j => grade j = 2) with hT
  have hTm : ∀ j ∈ T, (∀ x, j x ≠ 1) ∧ grade j = 2 := fun j hj =>
    ⟨(mem_retIdx.1 (Finset.mem_filter.1 hj).1).1, (Finset.mem_filter.1 hj).2⟩
  have step1 : |∑ j ∈ T, ecoefM j * rowRet G d p yp ym S v j| ≤
      lawE G p (aOf d p) yp ym S (fun σ =>
        ∑ i : nbhd G S v, |g12D G d p yp ym σ S v (Function.update 0 i 3)| +
          ∑ ik ∈ (Finset.univ : Finset (nbhd G S v)).offDiag,
            |g12D G d p yp ym σ S v (Function.update (Function.update 0 ik.1 2) ik.2 2)|) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j ∈ T, |ecoefM j * rowRet G d p yp ym S v j|
        ≤ ∑ j ∈ T, lawE G p (aOf d p) yp ym S (fun σ => |g12D G d p yp ym σ S v j|) :=
          Finset.sum_le_sum fun j _ => by
            rw [abs_mul, hret]
            calc |ecoefM j| * |lawE G p (aOf d p) yp ym S (fun σ => g12D G d p yp ym σ S v j)|
                ≤ 1 * lawE G p (aOf d p) yp ym S (fun σ => |g12D G d p yp ym σ S v j|) :=
                  mul_le_mul (SecA.abs_ecoefM_le_one j) (g12_abs_lawE_le G _) (abs_nonneg _)
                    zero_le_one
              _ = _ := one_mul _
      _ ≤ ∑ i : nbhd G S v, lawE G p (aOf d p) yp ym S
              (fun σ => |g12D G d p yp ym σ S v (Function.update 0 i 3)|) +
            ∑ ik ∈ (Finset.univ : Finset (nbhd G S v)).offDiag, lawE G p (aOf d p) yp ym S
              (fun σ => |g12D G d p yp ym σ S v
                (Function.update (Function.update 0 ik.1 2) ik.2 2)|) :=
          g12_sum_grade2_le T hTm
            (fun j => lawE G p (aOf d p) yp ym S (fun σ => |g12D G d p yp ym σ S v j|))
            (fun j => lawE_nonneg G fun σ _ => abs_nonneg _)
      _ = _ := by rw [lawE_add, lawE_sum, lawE_sum]
  have hU6 : lawE G p (aOf d p) yp ym S (fun σ =>
      ∑ i, (1 + g12r G d p yp ym σ S v i) ^ 6 * g12Xb G d p 1 yp σ S v i +
        Real.sqrt (∑ i, (1 + g12r G d p yp ym σ S v i) ^ 6 * g12Xb G d p 1 yp σ S v i) *
          Real.sqrt (∑ i, (1 + g12r G d p yp ym σ S v i) ^ 6 * g12Xb G d p (-1) ym σ S v i)) ≤
      2 * (Real.exp 2 * (3 * 96 ^ 6) * g12K) * Real.sqrt (lc * dc) :=
    g12_EU_le G hR hk hC hyp hym hv hvl hlrc hlcd hS1 hS2 hM1 hM2
      (Y := fun i σ => (1 + g12r G d p yp ym σ S v i) ^ 6) (fun i σ => by positivity)
      (by norm_num) (fun i => g12_Y6_moment G hR hk hC hyp hym hv i)
  have hUT : lawE G p (aOf d p) yp ym S (fun σ =>
      ∑ i, (rowWt G d p yp ym σ S v * (1 + g12r G d p yp ym σ S v i) ^ 4) *
          g12Xb G d p 1 yp σ S v i +
        Real.sqrt (∑ i, (rowWt G d p yp ym σ S v * (1 + g12r G d p yp ym σ S v i) ^ 4) *
          g12Xb G d p 1 yp σ S v i) *
        Real.sqrt (∑ i, (rowWt G d p yp ym σ S v * (1 + g12r G d p yp ym σ S v i) ^ 4) *
          g12Xb G d p (-1) ym σ S v i)) ≤
      2 * (Real.exp 2 * (9 * 96 ^ 8) * g12K) * Real.sqrt (lc * dc) :=
    g12_EU_le G hR hk hC hyp hym hv hvl hlrc hlcd hS1 hS2 hM1 hM2
      (Y := fun i σ => rowWt G d p yp ym σ S v * (1 + g12r G d p yp ym σ S v i) ^ 4)
      (fun i σ => mul_nonneg (rowWt_nonneg' G d p yp ym σ S v) (by positivity))
      (by norm_num) (fun i => g12_YT_moment G hR hk hC hyp hym hv i)
  have hpa : (p : ℝ) ^ 5 * aOf d p ^ 2 ≤ 1 := by
    have h1 := TRegime.pow_le_d hR (k := 5) (by norm_num)
    obtain ⟨-, h2⟩ := TRegime.d_aOf_sq hR
    nlinarith [sq_nonneg (aOf d p)]
  set c6 := Real.exp 2 * (3 * 96 ^ 6) * g12K with hc6_def
  set cT := Real.exp 2 * (9 * 96 ^ 8) * g12K with hcT_def
  have hc6 : 0 ≤ c6 := by positivity
  have hcT : 0 ≤ cT := by positivity
  have hs := Real.sqrt_nonneg (lc * dc)
  have hK0 : (0 : ℝ) ≤ 10 ^ 6 * (p : ℝ) ^ 9 * aOf d p ^ 2 := by positivity
  calc |∑ j ∈ T, ecoefM j * rowRet G d p yp ym S v j|
      ≤ _ := step1
    _ ≤ lawE G p (aOf d p) yp ym S (fun σ => 10 ^ 6 * (p : ℝ) ^ 9 * aOf d p ^ 2 *
          (4 * aOf d p ^ 2 *
              (∑ i, (1 + g12r G d p yp ym σ S v i) ^ 6 * g12Xb G d p 1 yp σ S v i +
                Real.sqrt (∑ i, (1 + g12r G d p yp ym σ S v i) ^ 6 * g12Xb G d p 1 yp σ S v i) *
                  Real.sqrt (∑ i, (1 + g12r G d p yp ym σ S v i) ^ 6 *
                    g12Xb G d p (-1) ym σ S v i)) +
            16 * aOf d p ^ 2 *
              (∑ i, (rowWt G d p yp ym σ S v * (1 + g12r G d p yp ym σ S v i) ^ 4) *
                  g12Xb G d p 1 yp σ S v i +
                Real.sqrt (∑ i, (rowWt G d p yp ym σ S v * (1 + g12r G d p yp ym σ S v i) ^ 4) *
                  g12Xb G d p 1 yp σ S v i) *
                Real.sqrt (∑ i, (rowWt G d p yp ym σ S v * (1 + g12r G d p yp ym σ S v i) ^ 4) *
                  g12Xb G d p (-1) ym σ S v i)))) :=
        lawE_mono G fun σ hσ => g12_grade2_pt G hR hyp0 hym0 hv hσ
    _ = 10 ^ 6 * (p : ℝ) ^ 9 * aOf d p ^ 2 *
          (4 * aOf d p ^ 2 * lawE G p (aOf d p) yp ym S (fun σ =>
              ∑ i, (1 + g12r G d p yp ym σ S v i) ^ 6 * g12Xb G d p 1 yp σ S v i +
                Real.sqrt (∑ i, (1 + g12r G d p yp ym σ S v i) ^ 6 * g12Xb G d p 1 yp σ S v i) *
                  Real.sqrt (∑ i, (1 + g12r G d p yp ym σ S v i) ^ 6 *
                    g12Xb G d p (-1) ym σ S v i)) +
            16 * aOf d p ^ 2 * lawE G p (aOf d p) yp ym S (fun σ =>
              ∑ i, (rowWt G d p yp ym σ S v * (1 + g12r G d p yp ym σ S v i) ^ 4) *
                  g12Xb G d p 1 yp σ S v i +
                Real.sqrt (∑ i, (rowWt G d p yp ym σ S v * (1 + g12r G d p yp ym σ S v i) ^ 4) *
                  g12Xb G d p 1 yp σ S v i) *
                Real.sqrt (∑ i, (rowWt G d p yp ym σ S v * (1 + g12r G d p yp ym σ S v i) ^ 4) *
                  g12Xb G d p (-1) ym σ S v i))) := by
        rw [lawE_const_mul, lawE_add, lawE_const_mul, lawE_const_mul]
    _ ≤ 10 ^ 6 * (p : ℝ) ^ 9 * aOf d p ^ 2 *
          (4 * aOf d p ^ 2 * (2 * c6 * Real.sqrt (lc * dc)) +
            16 * aOf d p ^ 2 * (2 * cT * Real.sqrt (lc * dc))) :=
        mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hU6 (by positivity))
          (mul_le_mul_of_nonneg_left hUT (by positivity))) hK0
    _ = ((p : ℝ) ^ 5 * aOf d p ^ 2) *
          (aOf d p ^ 2 * (10 ^ 6 * (8 * c6 + 32 * cT) * ((p : ℝ) ^ 4 * Real.sqrt (lc * dc)))) := by
        ring
    _ ≤ 1 * (aOf d p ^ 2 * (10 ^ 6 * (8 * c6 + 32 * cT) * ((p : ℝ) ^ 4 * Real.sqrt (lc * dc)))) :=
        mul_le_mul_of_nonneg_right hpa (by positivity)
    _ = _ := one_mul _

end Main

/-- **CR-G2** (grade two: `j = 3e_i`, `c_j = -1/45`, `∂_i⁶`; `j = 2e_i + 2e_k`, `c_j = 1/144`,
`∂_i⁴∂_k⁴`).

**Sketch.** As CR-G1 with `mark_grade_two_diag` and `mark_grade_two_mixed` (either order of the
two coordinates, the bound is symmetric in `i, k`): every term carries two marks and the extra
factor `a²` (`a⁶ = a² · a⁴`, `a⁸ = a⁴ · a⁴`), so the sums over `i` and over `i ≠ k` give
`≤ 10⁶ a² p⁹ a² C √(λ_c δ_c) ≤ a² C' (p⁹/d) √(λ_c δ_c) ≤ a² C' p⁴ √(λ_c δ_c)` (`a²d ≤ 1/2`,
`p⁵ ≤ d`). -/
theorem row_grade2_le : ∃ C : ℝ, 0 < C ∧ Eventually fun _ _ d p _ =>
    ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
      (S : Finset V) (lam : ℝ) (yp ym : V → ℝ) (v : V), CapCtx G d p S lam →
      InCube (lam * sOf d p) yp → InCube (lam * sOf d p) ym → v ∈ S →
      ∀ lr lc dc : ℝ, vth d ≤ lr → lr ≤ lc → lc ≤ dc →
        incRowE G d p yp ym S v 1 yp / d ≤ lr → incRowE G d p yp ym S v (-1) ym / d ≤ dc →
        markE G d p yp ym S v 1 yp / (d : ℝ) ^ 2 ≤ lc →
        markE G d p yp ym S v (-1) ym / (d : ℝ) ^ 2 ≤ dc →
        |∑ j ∈ (retIdx (kStar d p) : Finset (nbhd G S v → ℕ)).filter (fun j => grade j = 2),
            ecoefM j * rowRet G d p yp ym S v j| ≤
          aOf d p ^ 2 * (C * ((p : ℝ) ^ 4 * Real.sqrt (lc * dc))) := by
  refine ⟨10 ^ 6 * (8 * (Real.exp 2 * (3 * 96 ^ 6) * g12K) +
      32 * (Real.exp 2 * (9 * 96 ^ 8) * g12K)),
    by have := g12K_pos; positivity, ((eventually_regime 1).and eventually_kIL32).mono ?_⟩
  rintro c₀ κ₀ d p h ⟨⟨hR, -, -⟩, hk⟩ V _ _ G _ S lam yp ym v hC hyp hym hv lr lc dc hvl hlrc
    hlcd hS1 hS2 hM1 hM2
  exact g12_grade2_main G hR hk hC hyp hym hv hvl hlrc hlcd hS1 hS2 hM1 hM2

end SecC

end BiluLinial.Tight
