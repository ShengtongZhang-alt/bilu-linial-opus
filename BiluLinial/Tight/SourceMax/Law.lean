/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.Symmetry
public import BiluLinial.Tight.Continuity
public import BiluLinial.Tight.SourceMax.Glue

/-!
# Elementary facts about the paired law

Blueprint node `D-SM-law` (source Section 1.1, Lemma "Source maximum and moments"). `lawE` is a
ratio of finite sums with nonnegative weights, so it is linear in `f`, monotone, and satisfies
Lyapunov's inequality `(E f^k)^{k+1} ≤ (E f^{k+1})^k` for `f ≥ 0` (Jensen for `x^{(k+1)/k}`).
At a zero plus-source `h_i^+ = 1` on supported signings, so every moment is `1`. Reversing the
signs swaps the branches (`Symmetry.lean`), also for powers. For `k < p`, `W (h_i^+)^k` is
continuous in `y⁺` (it is `1{…} det^{p-k} adj_ii^k det⁻^p`), so the moments are continuous where
the law exists, and the source cube is compact.
-/

@[expose] public section

namespace BiluLinial.Tight

open Matrix

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable {p : ℕ} {a : ℝ} {yp ym : V → ℝ} {S : Finset V}

theorem wt_nonneg (σ : Config V) : 0 ≤ wt G p a yp ym σ S := by
  unfold wt
  split_ifs with h
  · exact pow_nonneg (mul_pos h.1.det_pos h.2.det_pos).le _
  · exact le_rfl

theorem Zw_nonneg : 0 ≤ Zw G p a yp ym S := Finset.sum_nonneg fun σ _ => wt_nonneg G σ

theorem lawE_add (f g : Config V → ℝ) :
    lawE G p a yp ym S (fun σ => f σ + g σ) = lawE G p a yp ym S f + lawE G p a yp ym S g := by
  unfold lawE
  rw [← add_div, ← Finset.sum_add_distrib]
  exact congrArg (· / _) (Finset.sum_congr rfl fun σ _ => by ring)

theorem lawE_sub (f g : Config V → ℝ) :
    lawE G p a yp ym S (fun σ => f σ - g σ) = lawE G p a yp ym S f - lawE G p a yp ym S g := by
  unfold lawE
  rw [← sub_div, ← Finset.sum_sub_distrib]
  exact congrArg (· / _) (Finset.sum_congr rfl fun σ _ => by ring)

theorem lawE_const_mul (c : ℝ) (f : Config V → ℝ) :
    lawE G p a yp ym S (fun σ => c * f σ) = c * lawE G p a yp ym S f := by
  unfold lawE
  rw [mul_div_assoc', Finset.mul_sum]
  exact congrArg (· / _) (Finset.sum_congr rfl fun σ _ => by ring)

theorem lawE_sum {ι : Type*} (s : Finset ι) (f : ι → Config V → ℝ) :
    lawE G p a yp ym S (fun σ => ∑ l ∈ s, f l σ) = ∑ l ∈ s, lawE G p a yp ym S (f l) := by
  unfold lawE
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm, Finset.sum_div]

theorem lawE_zero : lawE G p a yp ym S (fun _ => 0) = 0 := by
  simp [lawE]

theorem lawE_congr {f g : Config V → ℝ} (h : ∀ σ, wt G p a yp ym σ S ≠ 0 → f σ = g σ) :
    lawE G p a yp ym S f = lawE G p a yp ym S g := by
  unfold lawE
  refine congrArg (· / _) (Finset.sum_congr rfl fun σ _ => ?_)
  by_cases hσ : wt G p a yp ym σ S = 0
  · rw [hσ, zero_mul, zero_mul]
  · rw [h σ hσ]

theorem lawE_nonneg {f : Config V → ℝ} (h : ∀ σ, wt G p a yp ym σ S ≠ 0 → 0 ≤ f σ) :
    0 ≤ lawE G p a yp ym S f := by
  unfold lawE
  refine div_nonneg (Finset.sum_nonneg fun σ _ => ?_) (Zw_nonneg G)
  by_cases hσ : wt G p a yp ym σ S = 0
  · rw [hσ, zero_mul]
  · exact mul_nonneg (wt_nonneg G σ) (h σ hσ)

/-- Lyapunov's inequality for the paired law. -/
theorem lawE_pow_succ_le (hZ : 0 < Zw G p a yp ym S) {f : Config V → ℝ}
    (hf : ∀ σ, wt G p a yp ym σ S ≠ 0 → 0 ≤ f σ) (k : ℕ) :
    lawE G p a yp ym S (fun σ => f σ ^ k) ^ (k + 1) ≤
      lawE G p a yp ym S (fun σ => f σ ^ (k + 1)) ^ k := by
  classical
  let g : Config V → ℝ := fun σ => if wt G p a yp ym σ S = 0 then 0 else f σ
  have hg : ∀ σ, 0 ≤ g σ := fun σ => by
    by_cases h : wt G p a yp ym σ S = 0
    · simp [g, h]
    · simp only [g, h, ite_false]
      exact hf σ h
  have hfg : ∀ m : ℕ, lawE G p a yp ym S (fun σ => f σ ^ m) =
      lawE G p a yp ym S (fun σ => g σ ^ m) :=
    fun m => lawE_congr G fun σ h => by simp [g, h]
  rw [hfg, hfg]
  have hlaw : ∀ m : ℕ, lawE G p a yp ym S (fun σ => g σ ^ m) =
      ∑ σ, wt G p a yp ym σ S / Zw G p a yp ym S * g σ ^ m := by
    intro m
    unfold lawE
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun σ _ => by ring
  have hμ : 0 ≤ lawE G p a yp ym S (fun σ => g σ ^ k) :=
    lawE_nonneg G fun σ _ => pow_nonneg (hg σ) k
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have h1 : lawE G p a yp ym S (fun σ => g σ ^ 0) = 1 := by
      simp only [pow_zero]
      unfold lawE
      simp only [mul_one]
      exact div_self hZ.ne'
    rw [h1]
    simp
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hq : 1 ≤ ((k : ℝ) + 1) / k := by
    rw [le_div_iff₀ hk']
    linarith
  have hw : ∀ σ ∈ (Finset.univ : Finset (Config V)),
      0 ≤ wt G p a yp ym σ S / Zw G p a yp ym S :=
    fun σ _ => div_nonneg (wt_nonneg G σ) hZ.le
  have hw1 : ∑ σ, wt G p a yp ym σ S / Zw G p a yp ym S = 1 := by
    rw [← Finset.sum_div]
    exact div_self hZ.ne'
  have hJ := Real.rpow_arith_mean_le_arith_mean_rpow Finset.univ
    (fun σ => wt G p a yp ym σ S / Zw G p a yp ym S) (fun σ => g σ ^ k) hw hw1
    (fun σ _ => pow_nonneg (hg σ) k) hq
  have hexp : (k : ℝ) * (((k : ℝ) + 1) / k) = ((k + 1 : ℕ) : ℝ) := by
    push_cast
    field_simp
  have hpow : ∀ σ, (g σ ^ k) ^ (((k : ℝ) + 1) / k) = g σ ^ (k + 1) := by
    intro σ
    rw [← Real.rpow_natCast (g σ) k, ← Real.rpow_mul (hg σ), hexp, Real.rpow_natCast]
  simp only [hpow] at hJ
  rw [← hlaw, ← hlaw] at hJ
  calc lawE G p a yp ym S (fun σ => g σ ^ k) ^ (k + 1)
      = (lawE G p a yp ym S (fun σ => g σ ^ k) ^ (((k : ℝ) + 1) / k)) ^ k := by
        rw [← Real.rpow_natCast _ k, ← Real.rpow_mul hμ, mul_comm, hexp, Real.rpow_natCast]
    _ ≤ lawE G p a yp ym S (fun σ => g σ ^ (k + 1)) ^ k :=
        pow_le_pow_left₀ (Real.rpow_nonneg hμ _) hJ k

/-- On a supported signing the normalized inverse diagonal is positive. -/
theorem hN_pos {σ : Config V} (h : wt G p a yp ym σ S ≠ 0) (i : V) :
    0 < hN G a 1 yp σ S i := by
  have hPD : (precN G a 1 yp σ S).PosDef := by
    by_contra hc
    exact h (by simp [wt, hc])
  exact hPD.inv.diag_pos

/-- At a zero plus-source every moment of `h_i^+` is `1`. -/
theorem lawE_hN_pow_of_source_zero {i : V} (hyi : yp i = 0) (hZ : 0 < Zw G p a yp ym S)
    (k : ℕ) : lawE G p a yp ym S (fun σ => hN G a 1 yp σ S i ^ k) = 1 := by
  unfold lawE
  have h : ∀ σ, wt G p a yp ym σ S * hN G a 1 yp σ S i ^ k = wt G p a yp ym σ S := by
    intro σ
    by_cases hσ : (precN G a 1 yp σ S).PosDef ∧ (precN G a (-1) ym σ S).PosDef
    · rw [hN_of_source_zero G hyi hσ.1.det_pos.ne'.isUnit, one_pow, mul_one]
    · rw [wt, ite_eq_right hσ, zero_mul]
  simp only [h]
  exact div_self hZ.ne'

/-- Branch swap for moments: `E (h_i^-)^k (y⁺, y⁻) = E (h_i^+)^k (y⁻, y⁺)`. -/
theorem lawE_hN_neg_pow_swap (i : V) (k : ℕ) :
    lawE G p a yp ym S (fun σ => hN G a (-1) ym σ S i ^ k) =
      lawE G p a ym yp S (fun σ => hN G a 1 ym σ S i ^ k) := by
  unfold lawE
  rw [Zw_swap G p a yp ym S]
  congr 1
  calc ∑ σ, wt G p a yp ym σ S * hN G a (-1) ym σ S i ^ k
      = ∑ σ, wt G p a ym yp (-σ) S * hN G a 1 ym (-σ) S i ^ k := by
        simp only [wt_neg, hN, precN_neg]
    _ = ∑ σ, wt G p a ym yp σ S * hN G a 1 ym σ S i ^ k :=
        Equiv.sum_comp (Equiv.neg (Config V))
          (fun σ => wt G p a ym yp σ S * hN G a 1 ym σ S i ^ k)

omit [Fintype V] in
theorem precN_isHermitian' (a τ : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) :
    (precN G a τ y σ S).IsHermitian := by
  refine Matrix.IsHermitian.ext fun u w => ?_
  simp only [precN, Matrix.of_apply, star_trivial]
  by_cases h : u = w
  · subst h
    rfl
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]
    have hs : sgn σ w u = sgn σ u w := by
      unfold sgn
      rw [Sym2.eq_swap]
    by_cases hc : u ∈ S ∧ w ∈ S ∧ G.Adj u w
    · rw [ite_eq_left ⟨hc.2.1, hc.1, hc.2.2.symm⟩, ite_eq_left hc, hs,
        mul_comm (Real.sqrt (y w))]
    · rw [ite_eq_right (fun h' => hc ⟨h'.2.1, h'.1, h'.2.2.symm⟩), ite_eq_right hc]

/-- For `k < p`, the `k`-th moment of `h_i^+` is continuous in `y⁺` where the law exists. -/
theorem continuousOn_moment {k : ℕ} (hk : k + 1 ≤ p) (ym : V → ℝ) (S : Finset V) (i : V) :
    ContinuousOn (fun y => lawE G p a y ym S (fun σ => hN G a 1 y σ S i ^ k))
      {y | 0 < Zw G p a y ym S} := by
  classical
  have hZc : Continuous fun y : V → ℝ => Zw G p a y ym S := by
    have h1 := continuous_Zw G (p := p) (by omega) a S
    have h2 : Continuous fun y : V → ℝ => (y, ym) := continuous_id.prodMk continuous_const
    have h3 := h1.comp h2
    simp only [Function.comp_def] at h3
    exact h3
  have hterm : ∀ σ, Continuous fun y : V → ℝ => wt G p a y ym σ S * hN G a 1 y σ S i ^ k := by
    intro σ
    have hP : Continuous fun y : V → ℝ => precN G a 1 y σ S := continuous_precN G a 1 σ S
    have heq : (fun y => wt G p a y ym σ S * hN G a 1 y σ S i ^ k) = fun y =>
        if (precN G a 1 y σ S).PosDef ∧ (precN G a (-1) ym σ S).PosDef then
          (precN G a 1 y σ S).det ^ (p - k) * (precN G a 1 y σ S).adjugate i i ^ k *
            (precN G a (-1) ym σ S).det ^ p else 0 := by
      funext y
      unfold wt hN
      split_ifs with h
      · have hd : (precN G a 1 y σ S).det ≠ 0 := h.1.det_pos.ne'
        rw [inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv, mul_pow, mul_pow,
          inv_pow, show (precN G a 1 y σ S).det ^ p =
            (precN G a 1 y σ S).det ^ (p - k) * (precN G a 1 y σ S).det ^ k by
              rw [← pow_add, Nat.sub_add_cancel (by omega)]]
        field_simp
      · rw [zero_mul]
    rw [heq]
    have hF : Continuous fun y : V → ℝ => (precN G a 1 y σ S).det ^ (p - k) *
        (precN G a 1 y σ S).adjugate i i ^ k * (precN G a (-1) ym σ S).det ^ p :=
      ((hP.matrix_det.pow _).mul ((hP.matrix_adjugate.matrix_elem i i).pow _)).mul
        continuous_const
    refine continuous_ite_posDef_family hP continuous_const
      (fun _ => precN_isHermitian' G _ _ _ _ _) (fun _ => precN_isHermitian' G _ _ _ _ _) hF ?_
    have hpk : p - k ≠ 0 := by omega
    have hp0 : p ≠ 0 := by omega
    rintro y (h | h)
    · rw [h, zero_pow hpk, zero_mul, zero_mul]
    · rw [h, zero_pow hp0, mul_zero]
  unfold lawE
  refine ContinuousOn.div₀ ?_ hZc.continuousOn fun y (hy : 0 < _) => hy.ne'
  exact (continuous_finsetSum _ fun σ _ => hterm σ).continuousOn

omit [Fintype V] [DecidableEq V] in
theorem isCompact_cube (c : ℝ) : IsCompact {y : V → ℝ | InCube c y} := by
  have : {y : V → ℝ | InCube c y} = Set.univ.pi fun _ => Set.Icc 0 c := by
    ext y
    simp only [Set.mem_ofPred_eq, InCube, Set.mem_univ_pi, Set.mem_Icc]
  rw [this]
  exact isCompact_univ_pi fun _ => isCompact_Icc

end BiluLinial.Tight
