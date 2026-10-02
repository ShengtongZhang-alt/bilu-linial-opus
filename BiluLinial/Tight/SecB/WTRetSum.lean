/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecB.WTRetMom
public import BiluLinial.Tight.Contact.Real

/-!
# The retained WT grades at one signing and the truncation parameters (helpers for TB.WT5l)

* `retained_sigma_le`: at a supported signing, with `Z = ZR` at the deleted vertex `i` and
  `|H₀| + 4 + 4k ≤ p`,
  `Σ_{1 ≤ |j|_g ≤ k} (|∂^{2j}F_Q(ξ)| + |∂^{2j}F_T(ξ)|)/Φ(ξ) ≤
  26 e² Σ_{g<k} (676 p⁴/d)^{g+1} X Z^{2(g+1)}`, `X = H (q_L + tr L)`
  (`starObs_pointwise` with `κ² = 26 p² Z/d ≥ (5p λ_s)²`, `SecC.lam_sq_le`, and
  `sum_ret_weight_le`).
* `mT M d = ⌈(22 + 2M) log d⌉`, `two_pow_mT`: `5 d^{21+2M} ≤ 2^{2 mT}`;
  `eventually_trunc`: `16 k_* + 8 mT ≤ p` for large `d`.
-/

@[expose] public section

namespace BiluLinial.Tight.SecB

open Matrix

universe u

/-- The extra truncation exponent `⌈(22 + 2M) log d⌉`. -/
noncomputable def mT (M d : ℕ) : ℕ := ⌈(22 + 2 * (M : ℝ)) * Real.log d⌉₊

theorem two_pow_mT (M : ℕ) {d : ℕ} (hd : 5 ≤ d) :
    (5 : ℝ) * (d : ℝ) ^ (21 + 2 * M) ≤ 2 ^ (2 * mT M d) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hd5 : (5 : ℝ) ≤ d := by exact_mod_cast hd
  have hlog : 0 ≤ Real.log d := Real.log_nonneg (by linarith)
  have hm : (22 + 2 * (M : ℝ)) * Real.log d ≤ (mT M d : ℝ) := Nat.le_ceil _
  have hl2 := Real.log_two_gt_d9
  calc (5 : ℝ) * (d : ℝ) ^ (21 + 2 * M) ≤ (d : ℝ) * (d : ℝ) ^ (21 + 2 * M) :=
        mul_le_mul_of_nonneg_right hd5 (by positivity)
    _ = Real.exp (((22 + 2 * M : ℕ) : ℝ) * Real.log d) := by
        rw [← Real.log_pow, Real.exp_log (pow_pos hd0 _)]
        ring
    _ ≤ Real.exp ((2 * mT M d : ℕ) * Real.log 2) := by
        refine Real.exp_le_exp.mpr ?_
        push_cast
        nlinarith
    _ = 2 ^ (2 * mT M d) := by
        rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]

/-- `16 k_* + 8 mT ≤ p` for large `d`. -/
theorem eventually_trunc (M : ℕ) :
    Eventually fun _ _ d p _ => 16 * kStarA d p + 8 * mT M d ≤ p := by
  refine ((SecC.eventually_log_le (32 * (22 + 2 * (M : ℝ)) + 64)).and
    ((SecC.eventually_le_log 1024).and (eventually_base 64))).mono ?_
  rintro c₀ κ₀ d p h ⟨h1, h2, ⟨-, hB, -⟩⟩
  have hL0 : 0 < Real.log d := by linarith
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hk : (kStarA d p : ℝ) < 16 * p / Real.log d + 1 :=
    Nat.ceil_lt_add_one (div_nonneg (by positivity) hL0.le)
  have h16 : 16 * (p : ℝ) / Real.log d ≤ p / 64 := by
    rw [div_le_div_iff₀ hL0 (by norm_num)]
    nlinarith
  have hm : (mT M d : ℝ) < (22 + 2 * (M : ℝ)) * Real.log d + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have : ((16 * kStarA d p + 8 * mT M d : ℕ) : ℝ) ≤ p := by
    push_cast
    nlinarith
  exact_mod_cast this

section Contact

variable {d p : ℕ} (ct : Contact.{u} d p)

/-- **The retained grades at one supported signing.** -/
theorem retained_sigma_le (hR : TRegime d p) {h : ℝ} (hh : 0 < h) (e dir : Bool) {i : ct.V}
    (hi : i ∈ ct.S) [Nonempty (nbhd ct.G ct.S i)] (l : List (ct.V × Bool × Bool)) {k : ℕ}
    (hk : l.length + 4 + 4 * k ≤ p) {σ : Config ct.V}
    (hσ : wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0) :
    ∑ j ∈ (retIdx k : Finset (nbhd ct.G ct.S i → ℕ)).erase 0,
        (|dEven (lJ ct i) j (starObsQ ct h e dir i l σ) (rootSigns ct.G σ ct.S i) /
            starPhi p (rootA ct σ i) (rootB ct σ i) (rootSigns ct.G σ ct.S i)| +
          |dEven (lJ ct i) j (starObsT ct h e dir i l σ) (rootSigns ct.G σ ct.S i) /
            starPhi p (rootA ct σ i) (rootB ct σ i) (rootSigns ct.G σ ct.S i)|) ≤
      26 * Real.exp 2 * ∑ g ∈ Finset.range k, (676 * (p : ℝ) ^ 4 / d) ^ (g + 1) *
        ((ct.wtH h e i l σ * (qForm (kerL ct h e dir i σ) (rootSigns ct.G σ ct.S i) +
          (kerL ct h e dir i σ).trace)) *
            SecC.ZR ct.G (aOf d p) ct.yp ct.ym σ ct.S i ^ (2 * (g + 1))) := by
  have hdR := hR.ten_pow_six_le_d
  have hd0 : (0 : ℝ) < d := lt_of_lt_of_le (by norm_num) hdR
  have hd1 : (1 : ℝ) ≤ d := le_trans (by norm_num) hdR
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast le_trans (by norm_num) hR.two_le_p
  set Z := SecC.ZR ct.G (aOf d p) ct.yp ct.ym σ ct.S i with hZ
  have hZ1 : 1 ≤ Z := by
    simp only [hZ, SecC.ZR]
    nlinarith [sq_nonneg (Finset.univ.sup' Finset.univ_nonempty
      (SecC.rhoR ct.G (aOf d p) ct.yp ct.ym σ ct.S i))]
  set x := 26 * (p : ℝ) ^ 2 / d * Z with hx
  have hx0 : 0 < x := by positivity
  set κ := Real.sqrt x with hκ
  have hκ0 : 0 < κ := Real.sqrt_pos.2 hx0
  have hκ2 : κ ^ 2 = x := Real.sq_sqrt hx0.le
  have hdκ : 8 ≤ (d : ℝ) * κ ^ 2 := by
    rw [hκ2, hx, show (d : ℝ) * (26 * (p : ℝ) ^ 2 / d * Z) = 26 * (p : ℝ) ^ 2 * Z by field_simp]
    nlinarith [mul_le_mul (one_le_pow₀ hp1 : (1 : ℝ) ≤ (p : ℝ) ^ 2) hZ1 zero_le_one
      (by positivity)]
  have hK5 : ((4 * p + (l.length + 4) + 4 * k : ℕ) : ℝ) ≤ 5 * p := by
    have : 4 * p + (l.length + 4) + 4 * k ≤ 5 * p := by omega
    exact_mod_cast this
  have hKl : ∀ s, ((4 * p + (l.length + 4) + 4 * k : ℕ) : ℝ) *
      SecC.lamR ct.G (aOf d p) ct.yp ct.ym σ ct.S i s ≤ κ := by
    intro s
    have h25 := SecC.lam_sq_le ct.G hR ct.ctx.toCapCtx ct.ctx.hyp ct.ctx.hym hσ s
    have hl0 : 0 ≤ SecC.lamR ct.G (aOf d p) ct.yp ct.ym σ ct.S i s :=
      mul_nonneg hR.aOf_pos.le (add_nonneg (mul_nonneg zero_le_two (Real.sqrt_nonneg _))
        (mul_nonneg zero_le_two (Real.sqrt_nonneg _)))
    refine Real.le_sqrt_of_sq_le ?_
    calc (((4 * p + (l.length + 4) + 4 * k : ℕ) : ℝ) *
          SecC.lamR ct.G (aOf d p) ct.yp ct.ym σ ct.S i s) ^ 2
        ≤ (5 * (p : ℝ) * SecC.lamR ct.G (aOf d p) ct.yp ct.ym σ ct.S i s) ^ 2 :=
          pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) hl0)
            (mul_le_mul_of_nonneg_right hK5 hl0) 2
      _ = 25 * (p : ℝ) ^ 2 * SecC.lamR ct.G (aOf d p) ct.yp ct.ym σ ct.S i s ^ 2 := by ring
      _ ≤ x := h25
  have hH0 := wtH_nonneg ct hh.le e i l hσ
  have hcard := card_nbhd_le_d' ct i
  -- one multi-index at a time
  have hpt : ∀ j ∈ (retIdx k : Finset (nbhd ct.G ct.S i → ℕ)).erase 0,
      |dEven (lJ ct i) j (starObsQ ct h e dir i l σ) (rootSigns ct.G σ ct.S i) /
          starPhi p (rootA ct σ i) (rootB ct σ i) (rootSigns ct.G σ ct.S i)| +
        |dEven (lJ ct i) j (starObsT ct h e dir i l σ) (rootSigns ct.G σ ct.S i) /
          starPhi p (rootA ct σ i) (rootB ct σ i) (rootSigns ct.G σ ct.S i)| ≤
      ct.wtH h e i l σ * (κ ^ (2 * ∑ s, j s) *
        (qForm ((ct.tMap h e dir i σ)ᵀ * ct.tMap h e dir i σ) (rootSigns ct.G σ ct.S i) +
          qd1 0 ((ct.tMap h e dir i σ)ᵀ * ct.tMap h e dir i σ) (rootSigns ct.G σ ct.S i)
            (dEvenList (Finset.univ : Finset (nbhd ct.G ct.S i)).toList j) / κ +
          qd2 ((ct.tMap h e dir i σ)ᵀ * ct.tMap h e dir i σ)
            (dEvenList (Finset.univ : Finset (nbhd ct.G ct.S i)).toList j) / κ ^ 2 +
          ((ct.tMap h e dir i σ)ᵀ * ct.tMap h e dir i σ).trace)) := by
    intro j hj
    obtain ⟨hadm, hgr⟩ := mem_retIdx.1 (Finset.mem_of_mem_erase hj)
    have h2 := SecC.sum_le_two_mul_grade hadm
    exact starObs_pointwise ct hR hh e dir hi l hσ (N := 4 * k) hκ0 hKl j (by omega)
  have hsum := sum_ret_weight_le k hd1 hcard hκ0 hdκ (ct.tMap h e dir i σ)
    (rootSigns ct.G σ ct.S i)
  calc _ ≤ ∑ j ∈ (retIdx k : Finset (nbhd ct.G ct.S i → ℕ)).erase 0,
        ct.wtH h e i l σ * (κ ^ (2 * ∑ s, j s) *
          (qForm ((ct.tMap h e dir i σ)ᵀ * ct.tMap h e dir i σ) (rootSigns ct.G σ ct.S i) +
            qd1 0 ((ct.tMap h e dir i σ)ᵀ * ct.tMap h e dir i σ) (rootSigns ct.G σ ct.S i)
              (dEvenList (Finset.univ : Finset (nbhd ct.G ct.S i)).toList j) / κ +
            qd2 ((ct.tMap h e dir i σ)ᵀ * ct.tMap h e dir i σ)
              (dEvenList (Finset.univ : Finset (nbhd ct.G ct.S i)).toList j) / κ ^ 2 +
            ((ct.tMap h e dir i σ)ᵀ * ct.tMap h e dir i σ).trace)) :=
        Finset.sum_le_sum hpt
    _ = ct.wtH h e i l σ * ∑ j ∈ (retIdx k : Finset (nbhd ct.G ct.S i → ℕ)).erase 0,
        κ ^ (2 * ∑ s, j s) *
          (qForm ((ct.tMap h e dir i σ)ᵀ * ct.tMap h e dir i σ) (rootSigns ct.G σ ct.S i) +
            qd1 0 ((ct.tMap h e dir i σ)ᵀ * ct.tMap h e dir i σ) (rootSigns ct.G σ ct.S i)
              (dEvenList (Finset.univ : Finset (nbhd ct.G ct.S i)).toList j) / κ +
            qd2 ((ct.tMap h e dir i σ)ᵀ * ct.tMap h e dir i σ)
              (dEvenList (Finset.univ : Finset (nbhd ct.G ct.S i)).toList j) / κ ^ 2 +
            ((ct.tMap h e dir i σ)ᵀ * ct.tMap h e dir i σ).trace) := by
        rw [Finset.mul_sum]
    _ ≤ ct.wtH h e i l σ * (26 * Real.exp 2 * ∑ g ∈ Finset.range k, ((d : ℝ) * κ ^ 4) ^ (g + 1) *
          (qForm ((ct.tMap h e dir i σ)ᵀ * ct.tMap h e dir i σ) (rootSigns ct.G σ ct.S i) +
            ((ct.tMap h e dir i σ)ᵀ * ct.tMap h e dir i σ).trace)) :=
        mul_le_mul_of_nonneg_left hsum hH0
    _ = _ := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun g _ => ?_
        have hk4 : (d : ℝ) * κ ^ 4 = 676 * (p : ℝ) ^ 4 / d * Z ^ 2 := by
          rw [show κ ^ 4 = (κ ^ 2) ^ 2 by ring, hκ2, hx]
          field_simp
          ring
        rw [hk4, mul_pow, ← pow_mul]
        unfold kerL
        ring

end Contact

end BiluLinial.Tight.SecB
