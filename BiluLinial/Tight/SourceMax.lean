/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SourceMax.FOC
public import BiluLinial.Tight.SourceMax.LinAlg

/-!
# Source maximum: moments (F2) and the covariance inequality at a contact (F3)

Blueprint nodes `D-F2`, `D-F3` (source Section 1.1, Lemma "Source maximum and moments"; AUDIT-D
§2.5 and gap G1). Sub-nodes: `docs/tight/BP_SOURCEMAX.md`.

**Sketch (F2).** Fix `i` and `k` with `1 ≤ k ≤ p - 2` and the minus source `y⁻`; let `y*` maximize
`m_k(y) = E_{(y, y⁻)} (h_i⁺)^k` over the compact cube `[0, λ s]^V` (`continuousOn_moment`; the law
exists on the whole `s`-cube). If `y*_i = 0` then `h_i = 1` and the bound holds. Otherwise, in
physical coordinates `C_l = p Cov(G_ii^k, G_ll) - k E(G_ii^{k-1} G_il²)` (`momC`) and decreasing
each positive plus-source `y_j` is feasible inside the cube, so (`foc_of_max`)
`Σ_{l ∈ S⁺} 𝓑_lj C_l / y_l + 1_{i=j} k m_k y_i^k ≤ 0` for `j ∈ S⁺`. Inverting with
`K = 𝓑⁻¹ ≥ 0` (`walk_dual`, using `walk_facts`) gives `C_l ≤ -k m_k y_i^k y_l K_li` on `S⁺`. At
`l = i`, `C_i = y_i^{k+1}((p - k) E h_i^{k+1} - p m_k E h_i)`, the cap `E h_i ≤ r` and `K_ii ≥ 1`
give `(p - k) E h_i^{k+1} ≤ m_k (p r - k)`, and Lyapunov `m_k^{k+1} ≤ (E h_i^{k+1})^k` gives
`m_k ≤ ((p r - k)/(p - k))^k`. The minus branch follows by the swap symmetry.

**Sketch (F3).** At a contact `E h_v⁺ = r` the point maximizes the first mean over the cube (the
caps hold there), `y_v⁺ > 0` (a zero source has mean `1 < r`), and the case `k = 1` gives
`C_l ≤ -r y_v y_l K_lv` on `S⁺`, which is the claim since `K` is symmetric. Vertices with
`y_i⁺ = 0` have physical row zero and both sides vanish.
-/

@[expose] public section

namespace BiluLinial.Tight

open Matrix

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable {d p : ℕ}

omit [Fintype V] [DecidableEq V] in
theorem InCube.of_mul_le_one {lam t : ℝ} (hl : lam ≤ 1) (ht : 0 ≤ t) {y : V → ℝ}
    (hy : InCube (lam * t) y) : InCube t y :=
  fun u => ⟨(hy u).1, (hy u).2.trans (mul_le_of_le_one_left ht hl)⟩

/-- `D-F2`, plus branch. -/
theorem source_moments_plus (hR : TRegime d p) {S : Finset V} {lam : ℝ}
    (hC : CapCtx G d p S lam) {yp ym : V → ℝ} (hyp : InCube (lam * sOf d p) yp)
    (hym : InCube (lam * sOf d p) ym) {i : V} (hi : i ∈ S) {k : ℕ} (hk1 : 1 ≤ k)
    (hk2 : k + 2 ≤ p) :
    lawE G p (aOf d p) yp ym S (fun σ => hN G (aOf d p) 1 yp σ S i ^ k) ≤
      (((p : ℝ) * rOf d p - k) / ((p : ℝ) - k)) ^ k := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hs := hR.sOf_pos
  have hr := hR.one_lt_rOf
  have hsub : ∀ y : V → ℝ, InCube (lam * sOf d p) y → InCube (sOf d p) y :=
    fun y hy => hy.of_mul_le_one hC.lam_le_one hs.le
  have hZ : ∀ y : V → ℝ, InCube (lam * sOf d p) y → 0 < Zw G p (aOf d p) y ym S :=
    fun y hy => hC.pos y ym (hsub y hy) (hsub ym hym)
  obtain ⟨y, hyc, hmax⟩ := (isCompact_cube (lam * sOf d p)).exists_isMaxOn
    (⟨yp, hyp⟩ : Set.Nonempty {y : V → ℝ | InCube (lam * sOf d p) y})
    ((continuousOn_moment G (a := aOf d p) (k := k' + 1) (by omega) ym S i).mono
      fun y hy => hZ y hy)
  have hyc' : InCube (lam * sOf d p) y := hyc
  have hmax' := isMaxOn_iff.1 hmax
  refine le_trans (hmax' yp hyp) ?_
  have hkp : ((k' + 1 : ℕ) : ℝ) + 2 ≤ p := by exact_mod_cast hk2
  have hpk : (0 : ℝ) < p - (k' + 1 : ℕ) := by linarith
  have hB1 : 1 ≤ ((p : ℝ) * rOf d p - (k' + 1 : ℕ)) / ((p : ℝ) - (k' + 1 : ℕ)) := by
    rw [le_div_iff₀ hpk]
    nlinarith
  by_cases hyi : y i = 0
  · rw [lawE_hN_pow_of_source_zero G hyi (hZ y hyc') (k' + 1)]
    exact one_le_pow₀ hB1
  have hyi' : 0 < y i := lt_of_le_of_ne (hyc' i).1 (Ne.symm hyi)
  have hiS : i ∈ posSrc S y := Finset.mem_filter.2 ⟨hi, hyi'⟩
  have hfoc := fun j (hj : j ∈ posSrc S y) =>
    foc_of_max G hk2 hyc' (hZ y hyc') hiS hj fun y' hy' => hmax' y' hy'
  have hla := walk_dual G hR hC.deg (hsub y hyc') hiS hfoc i hiS
  have hK := (walk_facts G hR hC.deg (hsub y hyc') S).2.2.1 i
  have hm0 : 0 ≤ lawE G p (aOf d p) y ym S (fun σ => hN G (aOf d p) 1 y σ S i ^ (k' + 1)) :=
    lawE_nonneg G fun σ hσ => pow_nonneg (hN_pos G hσ i).le _
  have hM0 :
      0 ≤ lawE G p (aOf d p) y ym S (fun σ => hN G (aOf d p) 1 y σ S i ^ (k' + 1 + 1)) :=
    lawE_nonneg G fun σ hσ => pow_nonneg (hN_pos G hσ i).le _
  have hcap : lawE G p (aOf d p) y ym S (fun σ => hN G (aOf d p) 1 y σ S i) ≤ rOf d p :=
    (hC.cap y ym hyc' hym i hi).1
  have hly : lawE G p (aOf d p) y ym S (fun σ => hN G (aOf d p) 1 y σ S i ^ (k' + 1)) ^
        (k' + 1 + 1) ≤
      lawE G p (aOf d p) y ym S (fun σ => hN G (aOf d p) 1 y σ S i ^ (k' + 1 + 1)) ^
        (k' + 1) :=
    lawE_pow_succ_le G (hZ y hyc') (fun σ hσ => (hN_pos G hσ i).le) (k' + 1)
  have hG : ∀ σ, greenP G (aOf d p) 1 y σ S i i = y i * hN G (aOf d p) 1 y σ S i := fun σ => by
    rw [greenP, hN]
    have := Real.mul_self_sqrt (hyc' i).1
    linear_combination (precN G (aOf d p) 1 y σ S)⁻¹ i i * this
  have hmom : momC G p (aOf d p) y ym S (k' + 1) i i = y i ^ (k' + 1 + 1) *
      (((p : ℝ) - (k' + 1 : ℕ)) *
          lawE G p (aOf d p) y ym S (fun σ => hN G (aOf d p) 1 y σ S i ^ (k' + 1 + 1)) -
        p * lawE G p (aOf d p) y ym S (fun σ => hN G (aOf d p) 1 y σ S i ^ (k' + 1)) *
          lawE G p (aOf d p) y ym S (fun σ => hN G (aOf d p) 1 y σ S i)) := by
    have e1 : (fun σ => greenP G (aOf d p) 1 y σ S i i ^ (k' + 1) *
        greenP G (aOf d p) 1 y σ S i i) =
        fun σ => y i ^ (k' + 1 + 1) * hN G (aOf d p) 1 y σ S i ^ (k' + 1 + 1) := by
      funext σ; rw [hG]; ring
    have e2 : (fun σ => greenP G (aOf d p) 1 y σ S i i ^ (k' + 1)) =
        fun σ => y i ^ (k' + 1) * hN G (aOf d p) 1 y σ S i ^ (k' + 1) := by
      funext σ; rw [hG]; ring
    have e3 : (fun σ => greenP G (aOf d p) 1 y σ S i i) =
        fun σ => y i * hN G (aOf d p) 1 y σ S i := by
      funext σ; rw [hG]
    have e4 : (fun σ => greenP G (aOf d p) 1 y σ S i i ^ (k' + 1 - 1) *
        greenP G (aOf d p) 1 y σ S i i ^ 2) =
        fun σ => y i ^ (k' + 1 + 1) * hN G (aOf d p) 1 y σ S i ^ (k' + 1 + 1) := by
      funext σ; rw [hG, Nat.add_sub_cancel]; ring
    rw [momC, e1, e2, e3, e4]
    simp only [lawE_const_mul]
    ring
  rw [hmom] at hla
  generalize lawE G p (aOf d p) y ym S (fun σ => hN G (aOf d p) 1 y σ S i ^ (k' + 1)) = m
    at hla hm0 hly ⊢
  generalize lawE G p (aOf d p) y ym S (fun σ => hN G (aOf d p) 1 y σ S i ^ (k' + 1 + 1)) = M
    at hla hM0 hly
  generalize lawE G p (aOf d p) y ym S (fun σ => hN G (aOf d p) 1 y σ S i) = μ at hla hcap
  generalize walkK G (aOf d p) y S i i = κ at hla hK
  have hkk : (0 : ℝ) ≤ ((k' + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  generalize ((k' + 1 : ℕ) : ℝ) = kk at hla hkp hpk hB1 hkk ⊢
  generalize ((p : ℕ) : ℝ) = P at hla hkp hpk hB1 ⊢
  generalize hB : (P * rOf d p - kk) / (P - kk) = B at hB1 ⊢
  have hyk : 0 < y i ^ (k' + 1 + 1) := pow_pos hyi' _
  have hyk' : y i ^ (k' + 1) * y i = y i ^ (k' + 1 + 1) := (pow_succ _ _).symm
  have h1 : (P - kk) * M - P * m * μ ≤ -(kk * m) := by
    have h3 : kk * m * y i ^ (k' + 1 + 1) ≤ kk * m * y i ^ (k' + 1) * y i * κ := by
      rw [mul_assoc (kk * m), hyk']
      exact le_mul_of_one_le_right (by positivity) hK
    have h2 : y i ^ (k' + 1 + 1) * ((P - kk) * M - P * m * μ) ≤
        y i ^ (k' + 1 + 1) * (-(kk * m)) := by linarith
    exact le_of_mul_le_mul_left h2 hyk
  have h5 : (P - kk) * M ≤ m * (P * rOf d p - kk) := by
    have : P * m * μ ≤ P * m * rOf d p :=
      mul_le_mul_of_nonneg_left hcap (mul_nonneg (by linarith) hm0)
    linarith
  have h6 : M ≤ m * B := by
    rw [← hB, ← mul_div_assoc, le_div_iff₀ hpk]
    linarith
  have h7 : M ^ (k' + 1) ≤ m ^ (k' + 1) * B ^ (k' + 1) := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hM0 h6 _
  rcases hm0.lt_or_eq with hmpos | hmz
  · have h8 : m ^ (k' + 1) * m ≤ m ^ (k' + 1) * B ^ (k' + 1) := by
      rw [← pow_succ]
      exact hly.trans h7
    exact le_of_mul_le_mul_left h8 (pow_pos hmpos _)
  · rw [← hmz]
    exact pow_nonneg (by linarith) _

/-- `D-F2`: moment bounds on the capped cube, `E (h_i^±)^k ≤ ((p r - k)/(p - k))^k` for
`1 ≤ k ≤ p - 2`. -/
theorem source_moments (hR : TRegime d p) {S : Finset V} {lam : ℝ} (hC : CapCtx G d p S lam)
    {yp ym : V → ℝ} (hyp : InCube (lam * sOf d p) yp) (hym : InCube (lam * sOf d p) ym)
    {i : V} (hi : i ∈ S) {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k + 2 ≤ p) :
    lawE G p (aOf d p) yp ym S (fun σ => hN G (aOf d p) 1 yp σ S i ^ k) ≤
        (((p : ℝ) * rOf d p - k) / ((p : ℝ) - k)) ^ k ∧
      lawE G p (aOf d p) yp ym S (fun σ => hN G (aOf d p) (-1) ym σ S i ^ k) ≤
        (((p : ℝ) * rOf d p - k) / ((p : ℝ) - k)) ^ k := by
  refine ⟨source_moments_plus G hR hC hyp hym hi hk1 hk2, ?_⟩
  rw [lawE_hN_neg_pow_swap]
  exact source_moments_plus G hR hC hym hyp hi hk1 hk2

/-- `D-F3`: at a contact `E h_v⁺ = r`,
`p Cov(G⁺_vv, G⁺_ii) - E (G⁺_vi)² ≤ -r y_v⁺ y_i⁺ K_vi` (physical `G⁺`, `K = 𝓑(y⁺)⁻¹`). -/
theorem source_covariance (hR : TRegime d p) {S : Finset V} {lam : ℝ} {yp ym : V → ℝ} {v : V}
    (hC : ContactCtx G d p S lam yp ym v) {i : V} (hi : i ∈ S) :
    (p : ℝ) * (lawE G p (aOf d p) yp ym S
          (fun σ => greenP G (aOf d p) 1 yp σ S v v * greenP G (aOf d p) 1 yp σ S i i) -
        lawE G p (aOf d p) yp ym S (fun σ => greenP G (aOf d p) 1 yp σ S v v) *
          lawE G p (aOf d p) yp ym S (fun σ => greenP G (aOf d p) 1 yp σ S i i)) -
      lawE G p (aOf d p) yp ym S (fun σ => greenP G (aOf d p) 1 yp σ S v i ^ 2) ≤
      -(rOf d p * yp v * yp i * walkK G (aOf d p) yp S v i) := by
  have hs := hR.sOf_pos
  have hr := hR.one_lt_rOf
  have hsub : ∀ y : V → ℝ, InCube (lam * sOf d p) y → InCube (sOf d p) y :=
    fun y hy => hy.of_mul_le_one hC.lam_le_one hs.le
  have hZ : 0 < Zw G p (aOf d p) yp ym S := hC.pos yp ym (hsub _ hC.hyp) (hsub _ hC.hym)
  have hyv : 0 < yp v := by
    rcases (hC.hyp v).1.lt_or_eq with h | h
    · exact h
    · have h1 := meanPlus_of_source_zero G h.symm hZ
      rw [hC.contact] at h1
      linarith
  have hvS : v ∈ posSrc S yp := Finset.mem_filter.2 ⟨hC.mem, hyv⟩
  have hp3 : 1 + 2 ≤ p := le_trans (by norm_num) hR.hp
  have hmax : ∀ y, InCube (lam * sOf d p) y →
      lawE G p (aOf d p) y ym S (fun σ => hN G (aOf d p) 1 y σ S v ^ 1) ≤
        lawE G p (aOf d p) yp ym S (fun σ => hN G (aOf d p) 1 yp σ S v ^ 1) := by
    intro y hy
    simp only [pow_one]
    have h1 := (hC.cap y ym hy hC.hym v hC.mem).1
    have h2 := hC.contact
    rw [meanPlus] at h1 h2
    linarith
  have hfoc := fun j (hj : j ∈ posSrc S yp) => foc_of_max G hp3 hC.hyp hZ hvS hj hmax
  have hla := walk_dual G hR hC.deg (hsub _ hC.hyp) hvS hfoc
  have hm : lawE G p (aOf d p) yp ym S (fun σ => hN G (aOf d p) 1 yp σ S v ^ 1) = rOf d p := by
    simp only [pow_one]
    exact hC.contact
  by_cases hyi : 0 < yp i
  · have h := hla i (Finset.mem_filter.2 ⟨hi, hyi⟩)
    rw [hm, walkK_symm] at h
    simp only [momC, pow_one, Nat.cast_one, one_mul, Nat.sub_self, pow_zero] at h
    linarith
  · have hyi0 : yp i = 0 := le_antisymm (not_lt.1 hyi) (hC.hyp i).1
    have hG1 : ∀ σ, greenP G (aOf d p) 1 yp σ S v i = 0 := fun σ => by simp [greenP, hyi0]
    have hG2 : ∀ σ, greenP G (aOf d p) 1 yp σ S i i = 0 := fun σ => by simp [greenP, hyi0]
    simp only [hG1, hG2, mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      lawE_zero, sub_self, hyi0]
    simp

end BiluLinial.Tight
