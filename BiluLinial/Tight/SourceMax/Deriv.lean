/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SourceMax.Law
public import BiluLinial.Tight.SourceMax.Phys
public import BiluLinial.Tight.SourceMax.Jacobian

/-!
# The derivative of a moment along one positive source

Blueprint node `D-SM-deriv` (source Section 1.1, proof of Lemma "Source maximum and moments";
AUDIT-D DF1, without the deletion lift of §2.5).

`momC k i l = p Cov(G_ii^k, G_ll) - k E(G_ii^{k-1} G_il²)` is the derivative of `E G_ii^k` in the
physical diagonal entry `Z_l` (`G = greenP`, plus branch).

**Sketch.** Let `y(t) = y - t e_j` with `i, j ∈ S⁺`, `k + 2 ≤ p`. For `t < y_j`,
`S⁺(y(t)) = S⁺`, `P_σ(y(t)) = P_σ(y) + diag δ(t)` with `δ_u(t) = Z_u(y(t)) - Z_u(y)` on `S⁺`
(`precPhys_update`), and `δ'_u(0) = 𝓑_uj/(y_u y_j)` (`hasDerivAt_precZ_update`). By the physical
form (`wt_eq_phys`, `wt_mul_hN_pow_eq_phys`), `m(t) = E_{y(t)} (h_i^+)^k = Ñ(t)/(y_i(t)^k D̃(t))`
with `Ñ = Σ_σ W⁻ glue_k(P_σ)`, `D̃ = Σ_σ W⁻ glue_0(P_σ)`, and `D̃(0) > 0` from `Zw > 0`. By
`hasDerivAt_glue`, `Ñ'/D̃ = Σ_l δ'_l (p E[G_ii^k G_ll] - k E[G_ii^{k-1} G_il²])`,
`D̃'/D̃ = p Σ_l δ'_l E[G_ll]`, `Ñ/D̃ = E G_ii^k = y_i^k m` (`P⁻¹ = greenP` on `S⁺`). The quotient
rule with `(y_i(t)^k)' = -k y_i^{k-1} 1_{i=j}` gives the formula.
Small case `S = {i} = {j}`: `m ≡ 1`; the formula gives `-k/y_i + k/y_i = 0`.
-/

@[expose] public section

namespace BiluLinial.Tight

open Matrix

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- `C_l = p Cov(G_ii^k, G_ll) - k E(G_ii^{k-1} G_il²)` (physical plus-branch `G = greenP`). -/
noncomputable def momC (p : ℕ) (a : ℝ) (yp ym : V → ℝ) (S : Finset V) (k : ℕ) (i l : V) : ℝ :=
  (p : ℝ) * (lawE G p a yp ym S
        (fun σ => greenP G a 1 yp σ S i i ^ k * greenP G a 1 yp σ S l l) -
      lawE G p a yp ym S (fun σ => greenP G a 1 yp σ S i i ^ k) *
        lawE G p a yp ym S (fun σ => greenP G a 1 yp σ S l l)) -
    (k : ℝ) * lawE G p a yp ym S
      (fun σ => greenP G a 1 yp σ S i i ^ (k - 1) * greenP G a 1 yp σ S i l ^ 2)

/-- `D-SM-deriv`: the derivative of `t ↦ E_{y - t e_j} (h_i^+)^k` at `0`. -/
theorem hasDerivAt_moment {p k : ℕ} (hk : k + 2 ≤ p) {a : ℝ} {yp ym : V → ℝ}
    (hy : ∀ u, 0 ≤ yp u) {S : Finset V} (hZ : 0 < Zw G p a yp ym S) {i j : V}
    (hi : i ∈ posSrc S yp) (hj : j ∈ posSrc S yp) :
    HasDerivAt (fun t => lawE G p a (Function.update yp j (yp j - t)) ym S
        (fun σ => hN G a 1 (Function.update yp j (yp j - t)) σ S i ^ k))
      ((∑ l ∈ posSrc S yp, walkB G a yp S l j / (yp l * yp j) * momC G p a yp ym S k i l) /
          yp i ^ k +
        (if i = j then
          (k : ℝ) * lawE G p a yp ym S (fun σ => hN G a 1 yp σ S i ^ k) / yp i else 0)) 0 := by
  classical
  have hyi : 0 < yp i := (Finset.mem_filter.1 hi).2
  have hyj : 0 < yp j := (Finset.mem_filter.1 hj).2
  let yt : ℝ → V → ℝ := fun t => Function.update yp j (yp j - t)
  let δ : ℝ → V → ℝ := fun t u =>
    if u ∈ posSrc S yp then precZ G a (yt t) S u - precZ G a yp S u else 0
  let δ' : V → ℝ := fun u =>
    if u ∈ posSrc S yp then walkB G a yp S u j / (yp u * yp j) else 0
  have h0 : δ 0 = 0 := by
    funext u
    simp [δ, yt]
  have hδ : ∀ u, HasDerivAt (fun t => δ t u) (δ' u) 0 := by
    intro u
    by_cases hu : u ∈ posSrc S yp
    · simp only [δ, δ', hu, ite_true]
      exact (hasDerivAt_precZ_update G hy (Finset.mem_filter.1 hu).1 (Finset.mem_filter.1 hu).2
        (Finset.mem_filter.1 hj).1 hyj).sub_const _
    · simp only [δ, δ', hu, ite_false]
      exact hasDerivAt_const _ _
  let Nt : ℝ → ℝ := fun t =>
    ∑ σ, wtMinus G p a ym σ S * glue p k i (precPhys G a 1 yp σ S + diagonal (δ t))
  let Dt : ℝ → ℝ := fun t =>
    ∑ σ, wtMinus G p a ym σ S * glue p 0 i (precPhys G a 1 yp σ S + diagonal (δ t))
  have hderN : HasDerivAt Nt
      (∑ σ, wtMinus G p a ym σ S * glueDeriv p k i (precPhys G a 1 yp σ S) δ') 0 :=
    HasDerivAt.fun_sum fun σ _ =>
      (hasDerivAt_glue (precPhys_isHermitian (G := G) a 1 yp σ S) h0 hδ hk i).const_mul _
  have hderD : HasDerivAt Dt
      (∑ σ, wtMinus G p a ym σ S * glueDeriv p 0 i (precPhys G a 1 yp σ S) δ') 0 :=
    HasDerivAt.fun_sum fun σ _ =>
      (hasDerivAt_glue (precPhys_isHermitian (G := G) a 1 yp σ S) h0 hδ (by omega) i).const_mul _
  have hyt0 : yt 0 i = yp i := by simp [yt]
  have hyti : HasDerivAt (fun t => yt t i ^ k)
      ((k : ℝ) * yp i ^ (k - 1) * -(if i = j then 1 else 0)) 0 := by
    have h1 : HasDerivAt (fun t => yt t i) (-(if i = j then (1 : ℝ) else 0)) 0 := by
      by_cases hij : i = j
      · subst hij
        simp only [yt, Function.update_self, ite_true]
        exact (hasDerivAt_id (0 : ℝ)).const_sub _
      · simp only [yt, Function.update_of_ne hij, hij, ite_false, neg_zero]
        exact hasDerivAt_const _ _
    convert h1.fun_pow k using 1
    rw [hyt0]
  -- the law along the curve in physical form
  have hev : (fun t => lawE G p a (Function.update yp j (yp j - t)) ym S
        (fun σ => hN G a 1 (Function.update yp j (yp j - t)) σ S i ^ k)) =ᶠ[nhds 0]
      fun t => Nt t / (yt t i ^ k * Dt t) := by
    filter_upwards [Iio_mem_nhds hyj] with t ht
    have ht' : t < yp j := ht
    have hyt : ∀ u, 0 ≤ Function.update yp j (yp j - t) u := by
      intro u
      by_cases hu : u = j
      · subst hu
        rw [Function.update_self]
        linarith
      · rw [Function.update_of_ne hu]
        exact hy u
    have hit : i ∈ posSrc S (Function.update yp j (yp j - t)) := by
      rw [posSrc_update hj ht']
      exact hi
    have hP : ∀ σ, precPhys G a 1 (Function.update yp j (yp j - t)) σ S =
        precPhys G a 1 yp σ S + diagonal (δ t) := fun σ => precPhys_update hj ht'
    have e1 : ∑ σ, wt G p a (Function.update yp j (yp j - t)) ym σ S *
        hN G a 1 (Function.update yp j (yp j - t)) σ S i ^ k =
        physFactor S (Function.update yp j (yp j - t)) ^ p /
          Function.update yp j (yp j - t) i ^ k * Nt t := by
      simp only [Nt]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [wt_mul_hN_pow_eq_phys hyt p ym hit k, hP σ]
      ring
    have e2 : Zw G p a (Function.update yp j (yp j - t)) ym S =
        physFactor S (Function.update yp j (yp j - t)) ^ p * Dt t := by
      simp only [Dt]
      unfold Zw
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [wt_eq_phys hyt p ym, hP σ, glue_zero]
      ring
    have hπ : physFactor S (Function.update yp j (yp j - t)) ^ p ≠ 0 :=
      pow_ne_zero _ (physFactor_pos S _).ne'
    have hyk : Function.update yp j (yp j - t) i ^ k ≠ 0 :=
      pow_ne_zero _ (Finset.mem_filter.1 hit).2.ne'
    show lawE G p a (Function.update yp j (yp j - t)) ym S _ = Nt t / (yt t i ^ k * Dt t)
    unfold lawE
    rw [e1, e2]
    by_cases hD0 : Dt t = 0
    · simp [hD0]
    · simp only [yt]
      field_simp
  -- values at `t = 0`
  have hdiag0 : ∀ σ, precPhys G a 1 yp σ S + diagonal (δ 0) = precPhys G a 1 yp σ S :=
    fun σ => by rw [h0]; simp
  have hDt0 : Dt 0 = ∑ σ, wtMinus G p a ym σ S * posPow p (precPhys G a 1 yp σ S) := by
    simp only [Dt, hdiag0, glue_zero]
  have hZD : Zw G p a yp ym S = physFactor S yp ^ p * Dt 0 := by
    rw [hDt0]
    unfold Zw
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun σ _ => by rw [wt_eq_phys hy p ym]; ring
  have hD0 : 0 < Dt 0 := by
    have h := hZ
    rw [hZD] at h
    exact pos_of_mul_pos_right h (pow_pos (physFactor_pos S yp) p).le
  have hmulE : ∀ f : Config V → ℝ,
      ∑ σ, wtMinus G p a ym σ S * posPow p (precPhys G a 1 yp σ S) * f σ =
        Dt 0 * lawE G p a yp ym S f := by
    intro f
    rw [lawE_eq_phys hy p ym f, ← hDt0]
    field_simp
  have hNt0 : Nt 0 = Dt 0 * lawE G p a yp ym S
      (fun σ => (precPhys G a 1 yp σ S)⁻¹ i i ^ k) := by
    rw [← hmulE]
    simp only [Nt, hdiag0, glue, mul_assoc]
  have hgd : ∀ kk : ℕ,
      ∑ σ, wtMinus G p a ym σ S * glueDeriv p kk i (precPhys G a 1 yp σ S) δ' =
        Dt 0 * lawE G p a yp ym S (fun σ => (p : ℝ) * (precPhys G a 1 yp σ S)⁻¹ i i ^ kk *
          ∑ l, (precPhys G a 1 yp σ S)⁻¹ l l * δ' l - (kk : ℝ) *
          (precPhys G a 1 yp σ S)⁻¹ i i ^ (kk - 1) *
            ∑ l, (precPhys G a 1 yp σ S)⁻¹ i l ^ 2 * δ' l) := by
    intro kk
    rw [← hmulE]
    exact Finset.sum_congr rfl fun σ _ => by simp only [glueDeriv]; ring
  have hm : lawE G p a yp ym S (fun σ => hN G a 1 yp σ S i ^ k) =
      lawE G p a yp ym S (fun σ => (precPhys G a 1 yp σ S)⁻¹ i i ^ k) / yp i ^ k := by
    have e : (fun σ => hN G a 1 yp σ S i ^ k) =
        fun σ => 1 / yp i ^ k * (precPhys G a 1 yp σ S)⁻¹ i i ^ k := by
      funext σ
      rw [hN_eq_phys hy hi, div_pow]
      ring
    rw [e, lawE_const_mul]
    ring
  have hsumT : ∀ f : V → ℝ, ∑ l, f l * δ' l =
      ∑ l ∈ posSrc S yp, f l * (walkB G a yp S l j / (yp l * yp j)) := by
    intro f
    simp only [δ', mul_ite, mul_zero]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  have hNd : lawE G p a yp ym S (fun σ => (p : ℝ) * (precPhys G a 1 yp σ S)⁻¹ i i ^ k *
          ∑ l, (precPhys G a 1 yp σ S)⁻¹ l l * δ' l - (k : ℝ) *
          (precPhys G a 1 yp σ S)⁻¹ i i ^ (k - 1) *
            ∑ l, (precPhys G a 1 yp σ S)⁻¹ i l ^ 2 * δ' l) =
      ∑ l ∈ posSrc S yp, walkB G a yp S l j / (yp l * yp j) *
        ((p : ℝ) * lawE G p a yp ym S (fun σ => (precPhys G a 1 yp σ S)⁻¹ i i ^ k *
            (precPhys G a 1 yp σ S)⁻¹ l l) -
          (k : ℝ) * lawE G p a yp ym S (fun σ => (precPhys G a 1 yp σ S)⁻¹ i i ^ (k - 1) *
            (precPhys G a 1 yp σ S)⁻¹ i l ^ 2)) := by
    have e : (fun σ => (p : ℝ) * (precPhys G a 1 yp σ S)⁻¹ i i ^ k *
          ∑ l, (precPhys G a 1 yp σ S)⁻¹ l l * δ' l - (k : ℝ) *
          (precPhys G a 1 yp σ S)⁻¹ i i ^ (k - 1) *
            ∑ l, (precPhys G a 1 yp σ S)⁻¹ i l ^ 2 * δ' l) =
        fun σ => ∑ l ∈ posSrc S yp, walkB G a yp S l j / (yp l * yp j) *
          ((p : ℝ) * ((precPhys G a 1 yp σ S)⁻¹ i i ^ k * (precPhys G a 1 yp σ S)⁻¹ l l) -
            (k : ℝ) * ((precPhys G a 1 yp σ S)⁻¹ i i ^ (k - 1) *
              (precPhys G a 1 yp σ S)⁻¹ i l ^ 2)) := by
      funext σ
      rw [hsumT, hsumT, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun l _ => by ring
    rw [e, lawE_sum]
    exact Finset.sum_congr rfl fun l _ => by
      rw [lawE_const_mul, lawE_sub, lawE_const_mul, lawE_const_mul]
  have hDd : lawE G p a yp ym S (fun σ => (p : ℝ) * (precPhys G a 1 yp σ S)⁻¹ i i ^ 0 *
          ∑ l, (precPhys G a 1 yp σ S)⁻¹ l l * δ' l - ((0 : ℕ) : ℝ) *
          (precPhys G a 1 yp σ S)⁻¹ i i ^ (0 - 1) *
            ∑ l, (precPhys G a 1 yp σ S)⁻¹ i l ^ 2 * δ' l) =
      ∑ l ∈ posSrc S yp, walkB G a yp S l j / (yp l * yp j) *
        ((p : ℝ) * lawE G p a yp ym S (fun σ => (precPhys G a 1 yp σ S)⁻¹ l l)) := by
    have e : (fun σ => (p : ℝ) * (precPhys G a 1 yp σ S)⁻¹ i i ^ 0 *
          ∑ l, (precPhys G a 1 yp σ S)⁻¹ l l * δ' l - ((0 : ℕ) : ℝ) *
          (precPhys G a 1 yp σ S)⁻¹ i i ^ (0 - 1) *
            ∑ l, (precPhys G a 1 yp σ S)⁻¹ i l ^ 2 * δ' l) =
        fun σ => ∑ l ∈ posSrc S yp, walkB G a yp S l j / (yp l * yp j) *
          ((p : ℝ) * (precPhys G a 1 yp σ S)⁻¹ l l) := by
      funext σ
      rw [hsumT, Nat.cast_zero, zero_mul, zero_mul, sub_zero, pow_zero, mul_one, Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by ring
    rw [e, lawE_sum]
    exact Finset.sum_congr rfl fun l _ => by rw [lawE_const_mul, lawE_const_mul]
  have hmom : ∑ l ∈ posSrc S yp, walkB G a yp S l j / (yp l * yp j) *
        momC G p a yp ym S k i l =
      ∑ l ∈ posSrc S yp, walkB G a yp S l j / (yp l * yp j) *
        ((p : ℝ) * lawE G p a yp ym S (fun σ => (precPhys G a 1 yp σ S)⁻¹ i i ^ k *
            (precPhys G a 1 yp σ S)⁻¹ l l) -
          (k : ℝ) * lawE G p a yp ym S (fun σ => (precPhys G a 1 yp σ S)⁻¹ i i ^ (k - 1) *
            (precPhys G a 1 yp σ S)⁻¹ i l ^ 2)) -
        lawE G p a yp ym S (fun σ => (precPhys G a 1 yp σ S)⁻¹ i i ^ k) *
          ∑ l ∈ posSrc S yp, walkB G a yp S l j / (yp l * yp j) *
            ((p : ℝ) * lawE G p a yp ym S (fun σ => (precPhys G a 1 yp σ S)⁻¹ l l)) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun l hl => ?_
    simp only [momC, greenP_eq_phys hy hi hl, greenP_eq_phys hy hl hl, greenP_eq_phys hy hi hi]
    ring
  have hden : HasDerivAt (fun t => yt t i ^ k * Dt t)
      ((k : ℝ) * yp i ^ (k - 1) * -(if i = j then 1 else 0) * Dt 0 + yp i ^ k *
        ∑ σ, wtMinus G p a ym σ S * glueDeriv p 0 i (precPhys G a 1 yp σ S) δ') 0 := by
    convert hyti.mul hderD using 1
    rw [hyt0]
  have hne : yt 0 i ^ k * Dt 0 ≠ 0 := by
    rw [hyt0]
    exact mul_ne_zero (pow_ne_zero _ hyi.ne') hD0.ne'
  have hq := hderN.div hden hne
  refine (hq.congr_of_eventuallyEq hev).congr_deriv ?_
  rw [hyt0, hNt0, hgd k, hgd 0, hm, hmom, hNd, hDd]
  have hD0' := hD0.ne'
  have hyi' := hyi.ne'
  generalize (∑ l ∈ posSrc S yp, walkB G a yp S l j / (yp l * yp j) *
        ((p : ℝ) * lawE G p a yp ym S (fun σ => (precPhys G a 1 yp σ S)⁻¹ i i ^ k *
            (precPhys G a 1 yp σ S)⁻¹ l l) -
          (k : ℝ) * lawE G p a yp ym S (fun σ => (precPhys G a 1 yp σ S)⁻¹ i i ^ (k - 1) *
            (precPhys G a 1 yp σ S)⁻¹ i l ^ 2))) = SN
  generalize (∑ l ∈ posSrc S yp, walkB G a yp S l j / (yp l * yp j) *
        ((p : ℝ) * lawE G p a yp ym S (fun σ => (precPhys G a 1 yp σ S)⁻¹ l l))) = SD
  generalize lawE G p a yp ym S (fun σ => (precPhys G a 1 yp σ S)⁻¹ i i ^ k) = A
  generalize Dt 0 = D0 at hD0' ⊢
  by_cases hij : i = j
  · simp only [ite_eq_left hij]
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · subst hk0
      field_simp
      ring
    · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      rw [Nat.add_sub_cancel]
      field_simp
      ring
  · simp only [ite_eq_right hij]
    field_simp
    ring

end BiluLinial.Tight
