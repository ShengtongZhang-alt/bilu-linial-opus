/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecA.Conc

/-!
# Transfer with low-order own-core moments (helpers of `A-C4T`)

`CapPoint.crem`, `trans_rem` (`SecA/Transfer.lean`) and `trans_rel` (`SecA/TransRel.lean`) ask
for own-core moments `E_{ν_K} mⁿ ≤ Mⁿ` of the sup majorant for every `n ≤ p/2`, but the proof of
`A-CREM` uses them only for `n ≤ 2k + 3` (generalized Hölder with `n = 1 + Σ_i j_i`,
`Σ_i j_i ≤ 2(k + 1)`). The right-hand observables of (C4) have sup majorants `tr(MA) + tr(MB)`,
`Θ`, which are quadratic in the core diagonals, so only moments of order `≤ p/4` are available.
`crem_w`, `trans_rem_w`, `trans_rel_w` are the same statements with the weaker moment hypothesis
(proofs copied, the only change is the order bound). If the originals are weakened in place,
these copies can be deleted.
-/

@[expose] public section

universe u

namespace BiluLinial.Tight

open Matrix Finset

namespace CapPoint

variable {d p : ℕ} (cp : CapPoint.{u} d p)

/-- `A-CREM` with own-core moments of `m` only up to the order `2k + 3` that it uses. -/
theorem crem_w (hR : RegA d p) {v : cp.V} (hv : v ∈ cp.S) (m : Config cp.V → ℝ)
    (hm0 : ∀ σ, 0 ≤ m σ) {M : ℝ} (hM : 0 < M) (k : ℕ)
    (hmom : ∀ n : ℕ, 1 ≤ n → n ≤ 2 * k + 3 → cp.coreE v (fun σ => m σ ^ n) ≤ M ^ n)
    (hk : 2 * (2 * k + 3) ≤ p) :
    cp.coreE v (fun σ => m σ * ∑ j ∈ (topIdx k : Finset (cp.N v → ℕ)),
        ∏ i, cp.bdiag σ v i ^ j i) ≤ M * (5 / (d : ℝ)) ^ (k + 1) * Real.exp 3 := by
  have hd := hR.d_pos
  have hε0 := SecA.epsP_nonneg hR.treg
  have hε1 := SecA.epsP_le hR.treg
  have hw : ∀ σ, 0 ≤ wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v :=
    fun σ => SecA.wtCore_nonneg cp.G _ _ _ _ σ _ _
  set x : ℝ := 2 * (1 + 2 * epsP d p) / d with hx
  have hx0 : 0 < x := by positivity
  -- one multi-index at a time (Hölder)
  have hj : ∀ j ∈ (topIdx k : Finset (cp.N v → ℕ)),
      cp.coreE v (fun σ => m σ * ∏ i, cp.bdiag σ v i ^ j i) ≤ M * ∏ i, x ^ j i := by
    intro j hj
    obtain ⟨hadm, hg⟩ := mem_topIdx.1 hj
    have hsum : ∑ i, j i ≤ 2 * (k + 1) := hg ▸ SecA.sum_le_two_mul_grade' hadm
    have hn1 : 1 ≤ 1 + ∑ i, j i := by omega
    have hn2 : 2 * (1 + ∑ i, j i) ≤ p := by omega
    have e : cp.coreE v (fun σ => m σ * ∏ i, cp.bdiag σ v i ^ j i) =
        cp.coreE v (fun σ => m σ * ∏ i, max (cp.bdiag σ v i) 0 ^ j i) :=
      SecA.coreE_congr_of_supp cp.G fun σ hσ => by
        congr 1
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [max_eq_left (cp.bdiag_mem hR hσ i).1]
    rw [e]
    exact SecA.wavg_mul_prod_pow_le hw m hm0 (fun i σ => max (cp.bdiag σ v i) 0)
      (fun i σ => le_max_right _ _) j rfl hM (fun _ => x) (fun _ => hx0)
      (hmom _ hn1 (by omega)) (fun i _ => cp.bdiag_moment hR hv i hn1 hn2)
  -- the sum over the remainder indices
  have e1 : cp.coreE v (fun σ => m σ * ∑ j ∈ (topIdx k : Finset (cp.N v → ℕ)),
        ∏ i, cp.bdiag σ v i ^ j i) =
      ∑ j ∈ (topIdx k : Finset (cp.N v → ℕ)),
        cp.coreE v (fun σ => m σ * ∏ i, cp.bdiag σ v i ^ j i) := by
    simp only [Finset.mul_sum]
    exact wavg_sum _ _
  rw [e1]
  have hxT : x * (1 / (2 * x)) ≤ 1 / 2 := by
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hcnt := SecA.sum_topIdx_le_exp (ι := cp.N v) k hx0 (by positivity : (0 : ℝ) < 1 / (2 * x))
    hxT (cp.card_N_le v)
  have hT : 1 / (1 / (2 * x)) = 2 * x := one_div_one_div _
  have hexp : 2 * x ^ 2 * (1 / (2 * x)) * d = 2 * (1 + 2 * epsP d p) := by
    rw [hx]
    field_simp
  rw [hT, hexp] at hcnt
  calc ∑ j ∈ (topIdx k : Finset (cp.N v → ℕ)),
        cp.coreE v (fun σ => m σ * ∏ i, cp.bdiag σ v i ^ j i)
      ≤ ∑ j ∈ (topIdx k : Finset (cp.N v → ℕ)), M * ∏ i, x ^ j i := Finset.sum_le_sum hj
    _ = M * ∑ j ∈ (topIdx k : Finset (cp.N v → ℕ)), ∏ i, x ^ j i := by rw [Finset.mul_sum]
    _ ≤ M * ((2 * x) ^ (k + 1) * Real.exp (2 * (1 + 2 * epsP d p))) :=
        mul_le_mul_of_nonneg_left hcnt hM.le
    _ ≤ M * ((5 / (d : ℝ)) ^ (k + 1) * Real.exp 3) := by
        gcongr
        · rw [hx, ← mul_div_assoc]
          exact div_le_div_of_nonneg_right (by linarith) hd.le
        · linarith
    _ = M * (5 / (d : ℝ)) ^ (k + 1) * Real.exp 3 := by ring

/-- `A-REM` with own-core moments of `m` only up to order `2k_* + 3`. -/
theorem trans_rem_w (hR : RegA d p) {v : cp.V} (hv : v ∈ cp.S)
    (F : Config cp.V → (cp.N v → ℝ) → ℝ) (m : Config cp.V → ℝ) (hm0 : ∀ σ, 0 ≤ m σ) {M : ℝ}
    (hM : 0 < M)
    (hmom : ∀ n : ℕ, 1 ≤ n → n ≤ 2 * kStarA d p + 3 →
      cp.coreE v (fun σ => m σ ^ n) ≤ M ^ n)
    (hsm : ∀ σ, SmoothBdd (4 * kStarA d p + 4) (F σ))
    (hder : ∀ σ, ∀ j ∈ (topIdx (kStarA d p) : Finset (cp.N v → ℕ)), ∀ x,
      |dEven (cp.lN v) j (F σ) x| ≤
        m σ * (5 * (p : ℝ)) ^ (2 * ∑ i, j i) * ∏ i, cp.bdiag σ v i ^ j i) :
    |cp.coreE v (fun σ => gaussE (F σ) -
        ∑ j ∈ (retIdx (kStarA d p) : Finset (cp.N v → ℕ)),
          ecoefM j * radE (dEven (cp.lN v) j (F σ)))| ≤
      M * Real.exp (-(p : ℝ)) / d * cp.FH v := by
  have hd := hR.d_pos
  have hp := hR.p_pos
  have hk7 := hR.four_kStar_add_seven_le
  set k := kStarA d p with hk
  have h5p : (1 : ℝ) ≤ 5 * p := by linarith [hR.one_le_p]
  -- pointwise: (E4) and the order count `Σ j_i ≤ 2(k+1)`
  have hpt : ∀ σ, 0 < wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v →
      |gaussE (F σ) - ∑ j ∈ (retIdx k : Finset (cp.N v → ℕ)),
          ecoefM j * radE (dEven (cp.lN v) j (F σ))| ≤
        2 * (5 * (p : ℝ)) ^ (4 * k + 4) *
          (m σ * ∑ j ∈ (topIdx k : Finset (cp.N v → ℕ)), ∏ i, cp.bdiag σ v i ^ j i) := by
    intro σ hσ
    have h : |gaussE (F σ) - ∑ j ∈ (retIdx k : Finset (cp.N v → ℕ)),
          ecoefM j * radE (dEven (cp.lN v) j (F σ))| ≤
        2 * ∑ j ∈ (topIdx k : Finset (cp.N v → ℕ)),
          m σ * (5 * (p : ℝ)) ^ (2 * ∑ i, j i) * ∏ i, cp.bdiag σ v i ^ j i :=
      gauss_rad_expansion k (cp.lN_nodup v) cp.mem_lN (hsm σ) _ (hder σ)
    refine h.trans ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => ?_
    obtain ⟨hadm, hg⟩ := mem_topIdx.1 hj
    have hsum : ∑ i, j i ≤ 2 * (k + 1) := hg ▸ SecA.sum_le_two_mul_grade' hadm
    have hb : 0 ≤ m σ * ∏ i, cp.bdiag σ v i ^ j i :=
      mul_nonneg (hm0 σ) (Finset.prod_nonneg fun i _ =>
        pow_nonneg (cp.bdiag_mem hR hσ.ne' i).1 _)
    have hpow : (5 * (p : ℝ)) ^ (2 * ∑ i, j i) ≤ (5 * (p : ℝ)) ^ (4 * k + 4) :=
      pow_le_pow_right₀ h5p (by omega)
    calc m σ * (5 * (p : ℝ)) ^ (2 * ∑ i, j i) * ∏ i, cp.bdiag σ v i ^ j i
        = (5 * (p : ℝ)) ^ (2 * ∑ i, j i) * (m σ * ∏ i, cp.bdiag σ v i ^ j i) := by ring
      _ ≤ (5 * (p : ℝ)) ^ (4 * k + 4) * (m σ * ∏ i, cp.bdiag σ v i ^ j i) :=
          mul_le_mul_of_nonneg_right hpow hb
  have h1 := cp.abs_coreE_le v hpt
  have h2 : cp.coreE v (fun σ => 2 * (5 * (p : ℝ)) ^ (4 * k + 4) *
        (m σ * ∑ j ∈ (topIdx k : Finset (cp.N v → ℕ)), ∏ i, cp.bdiag σ v i ^ j i)) =
      2 * (5 * (p : ℝ)) ^ (4 * k + 4) * cp.coreE v (fun σ =>
        m σ * ∑ j ∈ (topIdx k : Finset (cp.N v → ℕ)), ∏ i, cp.bdiag σ v i ^ j i) :=
    SecA.wavg_const_mul _ _ _
  have h3 := cp.crem_w hR hv m hm0 hM k hmom (by omega)
  have hFH := cp.FH_pos' hR hv
  have hfl := cp.floor hR hv
  have hE6 := hR.E6
  -- `2 e³ ≤ p`
  have he3 : 2 * Real.exp 3 ≤ p := by
    have h1 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
    have h2 := Real.exp_one_lt_d9
    have h3 : Real.exp 1 ^ 3 ≤ 3 ^ 3 := pow_le_pow_left₀ (Real.exp_pos 1).le (by linarith) 3
    have hp6 : (10 : ℝ) ^ 6 ≤ p := by exact_mod_cast hR.treg.hp
    linarith
  have key : 2 * Real.exp 3 * (5 * (p : ℝ)) ^ (4 * k + 4) * (5 / (d : ℝ)) ^ (k + 1) *
      40 ^ p ≤ Real.exp (-(p : ℝ)) / d := by
    calc 2 * Real.exp 3 * (5 * (p : ℝ)) ^ (4 * k + 4) * (5 / (d : ℝ)) ^ (k + 1) * 40 ^ p
        ≤ (p : ℝ) * (8 * (p : ℝ)) ^ (4 * k + 4) * (8 / (d : ℝ)) ^ (k + 1) * 40 ^ p := by
          gcongr
          · linarith
          · norm_num
      _ = (p : ℝ) * 40 ^ p * (8 * (p : ℝ)) ^ (4 * k + 4) * 8 ^ (k + 1) / (d : ℝ) ^ k / d := by
          have hd0 : (d : ℝ) ≠ 0 := hd.ne'
          rw [div_pow, pow_succ (d : ℝ) k]
          field_simp
          try ring
      _ ≤ Real.exp (-(p : ℝ)) / d := div_le_div_of_nonneg_right hE6 hd.le
  calc _ ≤ _ := h1
    _ = _ := h2
    _ ≤ 2 * (5 * (p : ℝ)) ^ (4 * k + 4) * (M * (5 / (d : ℝ)) ^ (k + 1) * Real.exp 3) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = M * (2 * Real.exp 3 * (5 * (p : ℝ)) ^ (4 * k + 4) * (5 / (d : ℝ)) ^ (k + 1)) * 1 := by
        ring
    _ ≤ M * (2 * Real.exp 3 * (5 * (p : ℝ)) ^ (4 * k + 4) * (5 / (d : ℝ)) ^ (k + 1)) *
          (40 ^ p * cp.FH v) := mul_le_mul_of_nonneg_left hfl (by positivity)
    _ = M * (2 * Real.exp 3 * (5 * (p : ℝ)) ^ (4 * k + 4) * (5 / (d : ℝ)) ^ (k + 1) *
          40 ^ p) * cp.FH v := by ring
    _ ≤ M * (Real.exp (-(p : ℝ)) / d) * cp.FH v :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left key hM.le) hFH.le
    _ = M * Real.exp (-(p : ℝ)) / d * cp.FH v := by ring

/-- `A-TRANSR` with own-core moments of the sup majorant only up to order `2k_* + 3` (all that
`A-CREM` uses); needed when the sup majorant is quadratic in the core diagonals. -/
theorem trans_rel_w (hR : RegA d p) {v : cp.V} (hv : v ∈ cp.S)
    (F : Config cp.V → (cp.N v → ℝ) → ℝ) (hFc : ∀ σ σ', AgreeOff v σ σ' → F σ = F σ')
    (m : Config cp.V → ℝ) (hm0 : ∀ σ, 0 ≤ m σ) {M : ℝ} (hM : 0 < M)
    (hmom : ∀ n : ℕ, 1 ≤ n → n ≤ 2 * kStarA d p + 3 →
      cp.coreE v (fun σ => m σ ^ n) ≤ M ^ n)
    (hsm : ∀ σ, SmoothBdd (4 * kStarA d p + 4) (F σ))
    (hder : ∀ σ, ∀ j ∈ (topIdx (kStarA d p) : Finset (cp.N v → ℕ)), ∀ x,
      |dEven (cp.lN v) j (F σ) x| ≤
        m σ * (5 * (p : ℝ)) ^ (2 * ∑ i, j i) * ∏ i, cp.bdiag σ v i ^ j i)
    (hvan : ∀ σ, ∀ j ∈ (retIdx (kStarA d p) : Finset (cp.N v → ℕ)), ∀ ξ : cp.N v → ℝ,
      (∀ i, ξ i = 1 ∨ ξ i = -1) → starPhi p (cp.A σ v) (cp.B σ v) ξ = 0 →
        dEven (cp.lN v) j (F σ) ξ = 0)
    (X : Config cp.V → ℝ) (lam : cp.N v → Config cp.V → ℝ) (hX0 : ∀ σ, 0 ≤ X σ)
    (hl0 : ∀ i σ, 0 ≤ lam i σ) (K : ℕ) (hK : 1 ≤ K) (hKk : 16 * K * kStarA d p ≤ p)
    {m₀ θ B L : ℝ} (hθ : 0 < θ) (hθm : θ ≤ m₀) (hB : 0 ≤ B) (hL : 0 < L)
    (hXm : cp.E X ≤ m₀) (hX2 : cp.E (fun σ => X σ ^ 2) ≤ B ^ 2)
    (hmoml : ∀ i, ∀ n : ℕ, 1 ≤ n → 2 * n ≤ p → cp.E (fun σ => lam i σ ^ n) ≤ L ^ n)
    (hend : ∀ j ∈ (retIdx (kStarA d p) : Finset (cp.N v → ℕ)), 1 ≤ grade j → ∀ σ,
      0 < wt cp.G p (aOf d p) cp.yp cp.ym σ cp.S →
        |dEven (cp.lN v) j (F σ) (cp.xi σ v)| ≤
          X σ * starPhi p (cp.A σ v) (cp.B σ v) (cp.xi σ v) * ∏ i, lam i σ ^ (2 * j i))
    (hdL : 2 ≤ (d : ℝ) * L ^ 2) (hdL4 : (d : ℝ) * L ^ 4 ≤ 1 / 2) :
    |cp.coreE v (fun σ => gaussE (F σ) - radE (F σ)) / cp.FH v| ≤
      2 * Real.exp 2 * (m₀ * θ ^ (-(1 / (K : ℝ))) * B ^ (1 / (K : ℝ))) * ((d : ℝ) * L ^ 4) +
        M * Real.exp (-(p : ℝ)) / d := by
  have hFH := cp.FH_pos' hR hv
  have hrem := cp.trans_rem_w hR hv F m hm0 hM hmom hsm hder
  set k := kStarA d p with hk
  set Lj : (cp.N v → ℕ) → ℝ := fun j => cp.E (fun σ => dEven (cp.lN v) j (F σ) (cp.xi σ v) /
      starPhi p (cp.A σ v) (cp.B σ v) (cp.xi σ v)) with hLj
  have hret : ∀ j ∈ (retIdx k : Finset (cp.N v → ℕ)),
      cp.coreE v (fun σ => radE (dEven (cp.lN v) j (F σ))) = cp.FH v * Lj j := by
    intro j hj
    have h := cp.coreE_radE_div_eq hR hv (fun σ => dEven (cp.lN v) j (F σ))
      (fun σ σ' hσ => congrArg (fun f => dEven (cp.lN v) j f) (hFc σ σ' hσ))
      (fun σ ξ hξ hΦ => hvan σ j hj ξ hξ hΦ)
    rw [div_eq_iff hFH.ne'] at h
    rw [h, mul_comm]
  have h0mem : (0 : cp.N v → ℕ) ∈ (retIdx k : Finset (cp.N v → ℕ)) :=
    mem_retIdx.2 ⟨fun i => by simp, by simp⟩
  have hpt : (fun σ => gaussE (F σ) - radE (F σ)) = fun σ =>
      (gaussE (F σ) - ∑ j ∈ (retIdx k : Finset (cp.N v → ℕ)),
        ecoefM j * radE (dEven (cp.lN v) j (F σ))) +
      ∑ j ∈ (retIdx k : Finset (cp.N v → ℕ)).erase 0,
        ecoefM j * radE (dEven (cp.lN v) j (F σ)) := by
    funext σ
    rw [← Finset.add_sum_erase _ _ h0mem, ecoefM_zero, dEven_zero, one_mul]
    ring
  have e2 : cp.coreE v (fun σ => ∑ j ∈ (retIdx k : Finset (cp.N v → ℕ)).erase 0,
        ecoefM j * radE (dEven (cp.lN v) j (F σ))) =
      cp.FH v * ∑ j ∈ (retIdx k : Finset (cp.N v → ℕ)).erase 0, ecoefM j * Lj j := by
    rw [cp.coreE_fsum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [cp.coreE_fconst_mul, hret j (Finset.mem_of_mem_erase hj)]
    ring
  have hset : (retIdx k : Finset (cp.N v → ℕ)).erase 0 =
      (retIdx k : Finset (cp.N v → ℕ)).filter (fun j => 1 ≤ grade j) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hne, hj⟩
      refine ⟨hj, ?_⟩
      have : grade j ≠ 0 := fun h0 => hne (eq_zero_of_grade_eq_zero (mem_retIdx.1 hj).1 h0)
      omega
    · rintro ⟨hj, hg⟩
      refine ⟨?_, hj⟩
      rintro rfl
      simp at hg
  have hdec : cp.coreE v (fun σ => gaussE (F σ) - radE (F σ)) / cp.FH v =
      cp.coreE v (fun σ => gaussE (F σ) - ∑ j ∈ (retIdx k : Finset (cp.N v → ℕ)),
        ecoefM j * radE (dEven (cp.lN v) j (F σ))) / cp.FH v +
      ∑ j ∈ (retIdx k : Finset (cp.N v → ℕ)).filter (fun j => 1 ≤ grade j), ecoefM j * Lj j := by
    rw [hpt, cp.coreE_fadd, e2, add_div, mul_div_cancel_left₀ _ hFH.ne', hset]
  have hRb : ∀ j ∈ (retIdx k : Finset (cp.N v → ℕ)), 1 ≤ grade j → ∀ σ,
      0 < wt cp.G p (aOf d p) cp.yp cp.ym σ cp.S →
        |dEven (cp.lN v) j (F σ) (cp.xi σ v) / starPhi p (cp.A σ v) (cp.B σ v) (cp.xi σ v)| ≤
          X σ * ∏ i, lam i σ ^ (2 * j i) := by
    intro j hj hg σ hσ
    have hΦ := cp.starPhi_xi_pos hR hv hσ.ne'
    rw [abs_div, abs_of_pos hΦ, div_le_iff₀ hΦ]
    calc _ ≤ _ := hend j hj hg σ hσ
      _ = _ := by ring
  have hG := cp.hgr_rel hR k K hK hKk (fun j σ => dEven (cp.lN v) j (F σ) (cp.xi σ v) /
      starPhi p (cp.A σ v) (cp.B σ v) (cp.xi σ v)) X lam hX0 hl0 hθ hθm hB hL hXm hX2 hmoml
    hRb hdL hdL4
  have hG' : |∑ j ∈ (retIdx k : Finset (cp.N v → ℕ)).filter (fun j => 1 ≤ grade j),
      ecoefM j * Lj j| ≤
      2 * Real.exp 2 * (m₀ * θ ^ (-(1 / (K : ℝ))) * B ^ (1 / (K : ℝ))) * ((d : ℝ) * L ^ 4) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_trans ?_ hG)
    refine Finset.sum_le_sum fun j _ => ?_
    rw [abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) (SecA.abs_ecoefM_le_one j)
  have hrem' : |cp.coreE v (fun σ => gaussE (F σ) - ∑ j ∈ (retIdx k : Finset (cp.N v → ℕ)),
      ecoefM j * radE (dEven (cp.lN v) j (F σ))) / cp.FH v| ≤ M * Real.exp (-(p : ℝ)) / d := by
    rw [abs_div, abs_of_pos hFH, div_le_iff₀ hFH]
    exact hrem
  rw [hdec]
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ M * Real.exp (-(p : ℝ)) / d +
          2 * Real.exp 2 * (m₀ * θ ^ (-(1 / (K : ℝ))) * B ^ (1 / (K : ℝ))) *
            ((d : ℝ) * L ^ 4) := add_le_add hrem' hG'
    _ = _ := by ring

/-- Generic relative transfer of a clipped root observable `F = g α^{e₁} β^{e₂}`
(`g = quadFn c ℓ Q` core-measurable, `p - 2 ≤ e_i ≤ p`): a sup majorant `m` (weights
`√(A_ii + B_ii)`, own-core moments up to order `2k_* + 3`), an endpoint majorant `X₀` at the own
signs (weights `endLam`), and the relative factor `X = X₀ (τ⁺)^{p-e₁} (τ⁻)^{p-e₂}` with `E X ≤ m₀`,
`E X² ≤ B²` give `|E_{ν_K}(𝖦F - 𝖱F)/F_H| ≤ 2e² (m₀ 2e^{12000} B)(41⁴/4)(p⁴/d) + M e^{-p}/d`.
Proof: `trans_rel_w` with `K = ⌊log d/300⌋`, `θ = ϑ = d^{-10}`, `A-SMOOTH`/`A-E5`/`A-CLIP0`
(`clip_package`), `A-MAJ` (`endpoint_package`) and F1 (`τ⁺ α(ξ) = 1`). -/
theorem clip_trans_rel (hR : RegA d p) {v : cp.V} (hv : v ∈ cp.S)
    (c : Config cp.V → ℝ) (ℓ : Config cp.V → cp.N v → ℝ)
    (Q : Config cp.V → Matrix (cp.N v) (cp.N v) ℝ)
    (hcong : ∀ σ σ', AgreeOff v σ σ' → c σ = c σ' ∧ ℓ σ = ℓ σ' ∧ Q σ = Q σ')
    {e₁ e₂ : ℕ} (he₁ : p - 2 ≤ e₁) (he₂ : p - 2 ≤ e₂) (he₁p : e₁ ≤ p) (he₂p : e₂ ≤ p)
    (m : Config cp.V → ℝ) {M : ℝ} (hM : 0 < M)
    (hsup : ∀ σ, wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v ≠ 0 → ∀ x,
      qForm (cp.A σ v) x < 1 → qForm (cp.B σ v) x < 1 →
        QuadMaj (c σ) (ℓ σ) (Q σ) x (m σ) fun i => Real.sqrt (cp.A σ v i i + cp.B σ v i i))
    (hmom : ∀ n : ℕ, 1 ≤ n → n ≤ 2 * kStarA d p + 3 → cp.coreE v (fun σ =>
      (if wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v ≠ 0 then m σ else 0) ^ n) ≤ M ^ n)
    (X₀ : Config cp.V → ℝ)
    (hend : ∀ σ, wt cp.G p (aOf d p) cp.yp cp.ym σ cp.S ≠ 0 →
      QuadMaj (c σ) (ℓ σ) (Q σ) (cp.xi σ v) (X₀ σ) (cp.endLam σ v))
    {m₀ B : ℝ} (hθm : vth d ≤ m₀) (hB : 1 ≤ B)
    (hXm : cp.E (fun σ => X₀ σ * cp.taup σ v ^ (p - e₁) * cp.taum σ v ^ (p - e₂)) ≤ m₀)
    (hX2 : cp.E (fun σ => (X₀ σ * cp.taup σ v ^ (p - e₁) * cp.taum σ v ^ (p - e₂)) ^ 2) ≤
      B ^ 2) :
    |cp.coreE v (fun σ =>
        gaussE (clipObs (quadFn (c σ) (ℓ σ) (Q σ)) e₁ e₂ (cp.A σ v) (cp.B σ v)) -
        radE (clipObs (quadFn (c σ) (ℓ σ) (Q σ)) e₁ e₂ (cp.A σ v) (cp.B σ v))) / cp.FH v| ≤
      2 * Real.exp 2 * (m₀ * (2 * Real.exp 12000) * B) * (41 ^ 4 / 4 * ((p : ℝ) ^ 4 / d)) +
        M * Real.exp (-(p : ℝ)) / d := by
  have hd := hR.d_pos
  have hp1 : 1 ≤ p := le_trans (by norm_num) hR.treg.two_le_p
  have hp2 : 2 ≤ p := hR.treg.two_le_p
  have hk7 := hR.four_kStar_add_seven_le
  have hw : ∀ σ, 0 ≤ wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v :=
    fun σ => SecA.wtCore_nonneg cp.G _ _ _ _ σ _ _
  set k := kStarA d p with hk
  have hN1 : 4 * k + 4 < e₁ := by omega
  have hN2 : 4 * k + 4 < e₂ := by omega
  -- the cut-off family and its sup majorant
  set F : Config cp.V → (cp.N v → ℝ) → ℝ := fun σ =>
    if wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v ≠ 0 then
      clipObs (quadFn (c σ) (ℓ σ) (Q σ)) e₁ e₂ (cp.A σ v) (cp.B σ v)
    else fun _ => 0 with hF
  set m' : Config cp.V → ℝ := fun σ =>
    if wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v ≠ 0 then m σ else 0 with hm'
  have hFs : ∀ σ, wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v ≠ 0 →
      F σ = clipObs (quadFn (c σ) (ℓ σ) (Q σ)) e₁ e₂ (cp.A σ v) (cp.B σ v) := fun σ hσ => by
    rw [hF]; dsimp only; rw [ite_eq_left hσ]
  have hFn : ∀ σ, ¬ wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v ≠ 0 → F σ = fun _ => 0 :=
    fun σ hσ => by rw [hF]; dsimp only; rw [ite_eq_right hσ]
  have hms : ∀ σ, wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v ≠ 0 → m' σ = m σ :=
    fun σ hσ => by rw [hm']; dsimp only; rw [ite_eq_left hσ]
  have hmn : ∀ σ, ¬ wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v ≠ 0 → m' σ = 0 :=
    fun σ hσ => by rw [hm']; dsimp only; rw [ite_eq_right hσ]
  have hm0 : ∀ σ, 0 ≤ m' σ := by
    intro σ
    by_cases hσ : wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v ≠ 0
    · rw [hms σ hσ]
      have h := (hsup σ hσ 0 (by simp [qForm]) (by simp [qForm])).h0
      exact (abs_nonneg _).trans h
    · rw [hmn σ hσ]
  have hFc : ∀ σ σ', AgreeOff v σ σ' → F σ = F σ' := by
    intro σ σ' h
    have h1 := SecA.wtCore_congr cp.G (p := p) (a := aOf d p) (yp := cp.yp) (ym := cp.ym)
      (S := cp.S) h
    obtain ⟨h2, h3, h4⟩ := hcong σ σ' h
    simp only [hF, h1, h2, h3, h4, CapPoint.A, CapPoint.B, SecA.rootMat_congr cp.G h]
  have hpkg : ∀ σ, wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v ≠ 0 → _ := fun σ hσ =>
    SecA.CA.clip_package (cp.root_psd_core hσ).1 (cp.root_psd_core hσ).2 (N := 4 * k + 4)
      hN1 hN2 he₁p he₂p hp2 (hsup σ hσ)
  have hsm : ∀ σ, SmoothBdd (4 * kStarA d p + 4) (F σ) := by
    intro σ
    by_cases hσ : wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v ≠ 0
    · rw [hFs σ hσ]; exact (hpkg σ hσ).1
    · rw [hFn σ hσ]; exact SecA.CA.smoothBdd_zero_fn _
  have hder : ∀ σ, ∀ j ∈ (topIdx (kStarA d p) : Finset (cp.N v → ℕ)), ∀ x,
      |dEven (cp.lN v) j (F σ) x| ≤
        m' σ * (5 * (p : ℝ)) ^ (2 * ∑ i, j i) * ∏ i, cp.bdiag σ v i ^ j i := by
    intro σ j hj x
    obtain ⟨hadm, hg⟩ := mem_topIdx.1 hj
    have hsum := SecA.sum_le_two_mul_grade' hadm
    by_cases hσ : wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v ≠ 0
    · rw [hFs σ hσ, hms σ hσ]
      exact (hpkg σ hσ).2.1 j (by omega) x
    · rw [hFn σ hσ, hmn σ hσ, dEven_eq_pderivList, SecA.CA.pderivList_zero_fn]
      simp
  have hvan : ∀ σ, ∀ j ∈ (retIdx (kStarA d p) : Finset (cp.N v → ℕ)), ∀ ξ : cp.N v → ℝ,
      (∀ i, ξ i = 1 ∨ ξ i = -1) → starPhi p (cp.A σ v) (cp.B σ v) ξ = 0 →
        dEven (cp.lN v) j (F σ) ξ = 0 := by
    intro σ j hj ξ _ hΦ
    obtain ⟨hadm, hg⟩ := mem_retIdx.1 hj
    have hsum := SecA.sum_le_two_mul_grade' hadm
    by_cases hσ : wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v ≠ 0
    · rw [hFs σ hσ]
      exact (hpkg σ hσ).2.2 j (by omega) ξ (SecA.CA.one_le_of_starPhi_eq_zero hp1 hΦ)
    · rw [hFn σ hσ, dEven_eq_pderivList, SecA.CA.pderivList_zero_fn]
  have hmom' : ∀ n : ℕ, 1 ≤ n → n ≤ 2 * kStarA d p + 3 →
      cp.coreE v (fun σ => m' σ ^ n) ≤ M ^ n := hmom
  -- the endpoint majorant
  set X : Config cp.V → ℝ := fun σ =>
    if wt cp.G p (aOf d p) cp.yp cp.ym σ cp.S ≠ 0 then
      X₀ σ * cp.taup σ v ^ (p - e₁) * cp.taum σ v ^ (p - e₂) else 0 with hX
  have hXs : ∀ σ, wt cp.G p (aOf d p) cp.yp cp.ym σ cp.S ≠ 0 →
      X σ = X₀ σ * cp.taup σ v ^ (p - e₁) * cp.taum σ v ^ (p - e₂) := fun σ hσ => by
    rw [hX]; dsimp only; rw [ite_eq_left hσ]
  have htau : ∀ σ, wt cp.G p (aOf d p) cp.yp cp.ym σ cp.S ≠ 0 →
      (1 - qForm (cp.A σ v) (cp.xi σ v)) * cp.taup σ v = 1 ∧
        (1 - qForm (cp.B σ v) (cp.xi σ v)) * cp.taum σ v = 1 ∧
        0 < cp.taup σ v ∧ 0 < cp.taum σ v := by
    intro σ hσ
    obtain ⟨hPp, hPm⟩ := cp.precN_pd_of_wt hσ
    have hD1 : 1 ≤ diagD cp.G (aOf d p) cp.yp cp.S v :=
      FloorIns.one_le_diagD cp.G _ cp.yp_nonneg cp.S v
    have hD2 : 1 ≤ diagD cp.G (aOf d p) cp.ym cp.S v :=
      FloorIns.one_le_diagD cp.G _ cp.ym_nonneg cp.S v
    have hh1 : 0 < cp.hp σ v := hPp.inv.diag_pos
    have hh2 : 0 < cp.hm σ v := hPm.inv.diag_pos
    exact ⟨(SecA.CA.root_F1' cp.G (τ := 1) (by norm_num) cp.yp_nonneg hv hPp).1,
      (SecA.CA.root_F1' cp.G (τ := -1) (by norm_num) cp.ym_nonneg hv hPm).1,
      mul_pos (by linarith) hh1, mul_pos (by linarith) hh2⟩
  have hX0 : ∀ σ, 0 ≤ X σ := by
    intro σ
    by_cases hσ : wt cp.G p (aOf d p) cp.yp cp.ym σ cp.S ≠ 0
    · rw [hXs σ hσ]
      obtain ⟨-, -, ht1, ht2⟩ := htau σ hσ
      have h0 : 0 ≤ X₀ σ := (abs_nonneg _).trans (hend σ hσ).h0
      positivity
    · rw [hX]; dsimp only; rw [ite_eq_right hσ]
  have hXm' : cp.E X ≤ m₀ := by
    refine le_trans (le_of_eq ?_) hXm
    exact lawE_congr cp.G fun σ hσ => hXs σ hσ
  have hX2' : cp.E (fun σ => X σ ^ 2) ≤ B ^ 2 := by
    refine le_trans (le_of_eq ?_) hX2
    exact lawE_congr cp.G fun σ hσ => by rw [hXs σ hσ]
  -- weights
  set lam : cp.N v → Config cp.V → ℝ := fun i σ => 5 * (p : ℝ) * cp.endLam σ v i with hlam
  have hl0 : ∀ i σ, 0 ≤ lam i σ := fun i σ =>
    mul_nonneg (by positivity) (cp.endLam_nonneg hR σ v i)
  have hmoml : ∀ i, ∀ n : ℕ, 1 ≤ n → 2 * n ≤ p →
      cp.E (fun σ => lam i σ ^ n) ≤ (41 * (p : ℝ) * aOf d p) ^ n :=
    fun i n hn1 hn => cp.endLam_moment hR hv i hn1 hn
  have hendF : ∀ j ∈ (retIdx (kStarA d p) : Finset (cp.N v → ℕ)), 1 ≤ grade j → ∀ σ,
      0 < wt cp.G p (aOf d p) cp.yp cp.ym σ cp.S →
        |dEven (cp.lN v) j (F σ) (cp.xi σ v)| ≤
          X σ * starPhi p (cp.A σ v) (cp.B σ v) (cp.xi σ v) * ∏ i, lam i σ ^ (2 * j i) := by
    intro j _ _ σ hσ
    have hσc := cp.wtCore_ne_zero_of_wt hR hv hσ.ne'
    obtain ⟨hA, hB'⟩ := cp.root_psd_core hσc
    obtain ⟨⟨hα, hA1, hA2⟩, ⟨hβ, hB1, hB2⟩⟩ := cp.endLam_maj hR hv hσ.ne'
    obtain ⟨ht1, ht2, htp, htm⟩ := htau σ hσ.ne'
    rw [hFs σ hσc, hXs σ hσ.ne', SecA.CA.starPhi_eq_of_pos hα hβ]
    have h := SecA.CA.endpoint_package (SecA.CA.psd_symm hA) (SecA.CA.psd_symm hB')
      he₁p he₂p hp2 hα hβ (cp.endLam_nonneg hR σ v) hA1 hA2 hB1 hB2 (hend σ hσ.ne') j
    refine h.trans (le_of_eq ?_)
    set α := 1 - qForm (cp.A σ v) (cp.xi σ v) with hαdef
    set β := 1 - qForm (cp.B σ v) (cp.xi σ v) with hβdef
    have ea : α ^ p * cp.taup σ v ^ (p - e₁) = α ^ e₁ := by
      have : α ^ p = α ^ e₁ * α ^ (p - e₁) := by rw [← pow_add, Nat.add_sub_cancel' he₁p]
      rw [this, mul_assoc, ← mul_pow, ht1, one_pow, mul_one]
    have eb : β ^ p * cp.taum σ v ^ (p - e₂) = β ^ e₂ := by
      have : β ^ p = β ^ e₂ * β ^ (p - e₂) := by rw [← pow_add, Nat.add_sub_cancel' he₂p]
      rw [this, mul_assoc, ← mul_pow, ht2, one_pow, mul_one]
    rw [← ea, ← eb]
    ring
  -- the relative transfer
  obtain ⟨hdL, hdL4', hdL4⟩ := hR.endL_facts
  obtain ⟨hK1, hKk, hKθ⟩ := hR.whitenK_facts
  have hθ0 : 0 < vth d := by unfold vth; positivity
  have hT := cp.trans_rel_w hR hv F hFc m' hm0 hM hmom' hsm hder hvan X lam hX0 hl0
    ⌊Real.log d / 300⌋₊ hK1 hKk (m₀ := m₀) (θ := vth d) (B := B) hθ0 hθm (by linarith)
    (by have := hR.treg.aOf_pos; positivity) hXm' hX2' hmoml hendF hdL hdL4
  -- back to the uncut observable
  have e : cp.coreE v (fun σ =>
      gaussE (clipObs (quadFn (c σ) (ℓ σ) (Q σ)) e₁ e₂ (cp.A σ v) (cp.B σ v)) -
        radE (clipObs (quadFn (c σ) (ℓ σ) (Q σ)) e₁ e₂ (cp.A σ v) (cp.B σ v))) =
      cp.coreE v (fun σ => gaussE (F σ) - radE (F σ)) :=
    SecA.coreE_congr_of_supp cp.G fun σ hσ => by rw [hFs σ hσ]
  rw [e]
  refine hT.trans ?_
  -- constants
  set K := ⌊Real.log d / 300⌋₊ with hKdef
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK1
  have h2K : (1 : ℝ) ≤ (2 : ℝ) ^ (1 / (K : ℝ)) := Real.one_le_rpow (by norm_num) (by positivity)
  have hθK : vth d ^ (-(1 / (K : ℝ))) ≤ 2 * Real.exp 12000 := by
    have h0 : 0 ≤ vth d ^ (-(1 / (K : ℝ))) := by positivity
    nlinarith
  have hBK : B ^ (1 / (K : ℝ)) ≤ B := by
    calc B ^ (1 / (K : ℝ)) ≤ B ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hB (by rw [div_le_one hKpos]; exact_mod_cast hK1)
      _ = B := Real.rpow_one B
  have hm00 : 0 ≤ m₀ := hθ0.le.trans hθm
  have h1 : m₀ * vth d ^ (-(1 / (K : ℝ))) * B ^ (1 / (K : ℝ)) ≤
      m₀ * (2 * Real.exp 12000) * B := by
    have : 0 ≤ B ^ (1 / (K : ℝ)) := by positivity
    calc m₀ * vth d ^ (-(1 / (K : ℝ))) * B ^ (1 / (K : ℝ)) ≤
          m₀ * (2 * Real.exp 12000) * B ^ (1 / (K : ℝ)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hθK hm00) this
      _ ≤ m₀ * (2 * Real.exp 12000) * B :=
          mul_le_mul_of_nonneg_left hBK (by positivity)
  have h2 : 0 ≤ (d : ℝ) * (41 * (p : ℝ) * aOf d p) ^ 4 := by positivity
  have h3 : 0 ≤ m₀ * vth d ^ (-(1 / (K : ℝ))) * B ^ (1 / (K : ℝ)) := by positivity
  have h4 := mul_le_mul h1 hdL4' h2 (by positivity)
  have he2 : 0 ≤ 2 * Real.exp 2 := by positivity
  have h5 := mul_le_mul_of_nonneg_left h4 he2
  linarith

/-- Generic absolute transfer of a clipped root observable `F = g α^p β^p` with the grade-one
term kept: with a sup majorant `m` (own-core moments `≤ Mⁿ`, `2n ≤ p`) and an endpoint majorant
`X₀` (actual moments `≤ M_Eⁿ`, `2n ≤ p`),
`|E_{ν_K}(𝖦F - 𝖱F)/F_H - (1/12) Σ_i E[∂_i⁴F(ξ)/Φ(ξ)]| ≤ 2e² M_E ((41⁴/4) p⁴/d)² + M e^{-p}/d`.
Proof: `A-TRANS` (`CapPoint.trans`) with the cut-off family, `clip_package`, `endpoint_package`. -/
theorem clip_trans_abs (hR : RegA d p) {v : cp.V} (hv : v ∈ cp.S)
    (c : Config cp.V → ℝ) (ℓ : Config cp.V → cp.N v → ℝ)
    (Q : Config cp.V → Matrix (cp.N v) (cp.N v) ℝ)
    (hcong : ∀ σ σ', AgreeOff v σ σ' → c σ = c σ' ∧ ℓ σ = ℓ σ' ∧ Q σ = Q σ')
    (m : Config cp.V → ℝ) {M : ℝ} (hM : 0 < M)
    (hsup : ∀ σ, wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v ≠ 0 → ∀ x,
      qForm (cp.A σ v) x < 1 → qForm (cp.B σ v) x < 1 →
        QuadMaj (c σ) (ℓ σ) (Q σ) x (m σ) fun i => Real.sqrt (cp.A σ v i i + cp.B σ v i i))
    (hmom : ∀ n : ℕ, 1 ≤ n → 2 * n ≤ p → cp.coreE v (fun σ =>
      (if wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v ≠ 0 then m σ else 0) ^ n) ≤ M ^ n)
    (X₀ : Config cp.V → ℝ)
    (hend : ∀ σ, wt cp.G p (aOf d p) cp.yp cp.ym σ cp.S ≠ 0 →
      QuadMaj (c σ) (ℓ σ) (Q σ) (cp.xi σ v) (X₀ σ) (cp.endLam σ v))
    {ME : ℝ} (hME : 0 < ME)
    (hmomE : ∀ n : ℕ, 1 ≤ n → 2 * n ≤ p → cp.E (fun σ => X₀ σ ^ n) ≤ ME ^ n) :
    |cp.coreE v (fun σ =>
        gaussE (clipObs (quadFn (c σ) (ℓ σ) (Q σ)) p p (cp.A σ v) (cp.B σ v)) -
        radE (clipObs (quadFn (c σ) (ℓ σ) (Q σ)) p p (cp.A σ v) (cp.B σ v))) / cp.FH v -
      ∑ i : cp.N v, (1 / 12 : ℝ) * cp.E (fun σ =>
        (pderiv i)^[4] (clipObs (quadFn (c σ) (ℓ σ) (Q σ)) p p (cp.A σ v) (cp.B σ v))
          (cp.xi σ v) / starPhi p (cp.A σ v) (cp.B σ v) (cp.xi σ v))| ≤
      2 * Real.exp 2 * ME * (41 ^ 4 / 4 * ((p : ℝ) ^ 4 / d)) ^ 2 +
        M * Real.exp (-(p : ℝ)) / d := by
  have hd := hR.d_pos
  have hp1 : 1 ≤ p := le_trans (by norm_num) hR.treg.two_le_p
  have hp2 : 2 ≤ p := hR.treg.two_le_p
  have hk7 := hR.four_kStar_add_seven_le
  have hw : ∀ σ, 0 ≤ wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v :=
    fun σ => SecA.wtCore_nonneg cp.G _ _ _ _ σ _ _
  set k := kStarA d p with hk
  have hN1 : 4 * k + 4 < p := by omega
  set F : Config cp.V → (cp.N v → ℝ) → ℝ := fun σ =>
    if wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v ≠ 0 then
      clipObs (quadFn (c σ) (ℓ σ) (Q σ)) p p (cp.A σ v) (cp.B σ v)
    else fun _ => 0 with hF
  set m' : Config cp.V → ℝ := fun σ =>
    if wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v ≠ 0 then m σ else 0 with hm'
  have hFs : ∀ σ, wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v ≠ 0 →
      F σ = clipObs (quadFn (c σ) (ℓ σ) (Q σ)) p p (cp.A σ v) (cp.B σ v) := fun σ hσ => by
    rw [hF]; dsimp only; rw [ite_eq_left hσ]
  have hFn : ∀ σ, ¬ wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v ≠ 0 → F σ = fun _ => 0 :=
    fun σ hσ => by rw [hF]; dsimp only; rw [ite_eq_right hσ]
  have hms : ∀ σ, wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v ≠ 0 → m' σ = m σ :=
    fun σ hσ => by rw [hm']; dsimp only; rw [ite_eq_left hσ]
  have hmn : ∀ σ, ¬ wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v ≠ 0 → m' σ = 0 :=
    fun σ hσ => by rw [hm']; dsimp only; rw [ite_eq_right hσ]
  have hm0 : ∀ σ, 0 ≤ m' σ := by
    intro σ
    by_cases hσ : wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v ≠ 0
    · rw [hms σ hσ]
      have h := (hsup σ hσ 0 (by simp [qForm]) (by simp [qForm])).h0
      exact (abs_nonneg _).trans h
    · rw [hmn σ hσ]
  have hFc : ∀ σ σ', AgreeOff v σ σ' → F σ = F σ' := by
    intro σ σ' h
    have h1 := SecA.wtCore_congr cp.G (p := p) (a := aOf d p) (yp := cp.yp) (ym := cp.ym)
      (S := cp.S) h
    obtain ⟨h2, h3, h4⟩ := hcong σ σ' h
    simp only [hF, h1, h2, h3, h4, CapPoint.A, CapPoint.B, SecA.rootMat_congr cp.G h]
  have hpkg : ∀ σ, wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v ≠ 0 → _ := fun σ hσ =>
    SecA.CA.clip_package (cp.root_psd_core hσ).1 (cp.root_psd_core hσ).2 (N := 4 * k + 4)
      hN1 hN1 le_rfl le_rfl hp2 (hsup σ hσ)
  have hsm : ∀ σ, SmoothBdd (4 * kStarA d p + 4) (F σ) := by
    intro σ
    by_cases hσ : wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v ≠ 0
    · rw [hFs σ hσ]; exact (hpkg σ hσ).1
    · rw [hFn σ hσ]; exact SecA.CA.smoothBdd_zero_fn _
  have hder : ∀ σ, ∀ j ∈ (topIdx (kStarA d p) : Finset (cp.N v → ℕ)), ∀ x,
      |dEven (cp.lN v) j (F σ) x| ≤
        m' σ * (5 * (p : ℝ)) ^ (2 * ∑ i, j i) * ∏ i, cp.bdiag σ v i ^ j i := by
    intro σ j hj x
    obtain ⟨hadm, hg⟩ := mem_topIdx.1 hj
    have hsum := SecA.sum_le_two_mul_grade' hadm
    by_cases hσ : wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v ≠ 0
    · rw [hFs σ hσ, hms σ hσ]
      exact (hpkg σ hσ).2.1 j (by omega) x
    · rw [hFn σ hσ, hmn σ hσ, dEven_eq_pderivList, SecA.CA.pderivList_zero_fn]
      simp
  have hvan : ∀ σ, ∀ j ∈ (retIdx (kStarA d p) : Finset (cp.N v → ℕ)), ∀ ξ : cp.N v → ℝ,
      (∀ i, ξ i = 1 ∨ ξ i = -1) → starPhi p (cp.A σ v) (cp.B σ v) ξ = 0 →
        dEven (cp.lN v) j (F σ) ξ = 0 := by
    intro σ j hj ξ _ hΦ
    obtain ⟨hadm, hg⟩ := mem_retIdx.1 hj
    have hsum := SecA.sum_le_two_mul_grade' hadm
    by_cases hσ : wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v ≠ 0
    · rw [hFs σ hσ]
      exact (hpkg σ hσ).2.2 j (by omega) ξ (SecA.CA.one_le_of_starPhi_eq_zero hp1 hΦ)
    · rw [hFn σ hσ, dEven_eq_pderivList, SecA.CA.pderivList_zero_fn]
  have hmom' : ∀ n : ℕ, 1 ≤ n → 2 * n ≤ p → cp.coreE v (fun σ => m' σ ^ n) ≤ M ^ n := hmom
  -- the endpoint majorant
  set mE : Config cp.V → ℝ := fun σ =>
    if wt cp.G p (aOf d p) cp.yp cp.ym σ cp.S ≠ 0 then X₀ σ else 0 with hmE
  have hmEs : ∀ σ, wt cp.G p (aOf d p) cp.yp cp.ym σ cp.S ≠ 0 → mE σ = X₀ σ := fun σ hσ => by
    rw [hmE]; dsimp only; rw [ite_eq_left hσ]
  have hmE0 : ∀ σ, 0 ≤ mE σ := by
    intro σ
    by_cases hσ : wt cp.G p (aOf d p) cp.yp cp.ym σ cp.S ≠ 0
    · rw [hmEs σ hσ]; exact (abs_nonneg _).trans (hend σ hσ).h0
    · rw [hmE]; dsimp only; rw [ite_eq_right hσ]
  have hmomE' : ∀ n : ℕ, 1 ≤ n → 2 * n ≤ p → cp.E (fun σ => mE σ ^ n) ≤ ME ^ n := by
    intro n hn1 hn
    refine le_trans (le_of_eq ?_) (hmomE n hn1 hn)
    exact lawE_congr cp.G fun σ hσ => by rw [hmEs σ hσ]
  set lam : cp.N v → Config cp.V → ℝ := fun i σ => 5 * (p : ℝ) * cp.endLam σ v i with hlam
  have hl0 : ∀ i σ, 0 ≤ lam i σ := fun i σ =>
    mul_nonneg (by positivity) (cp.endLam_nonneg hR σ v i)
  have hmoml : ∀ i, ∀ n : ℕ, 1 ≤ n → 2 * n ≤ p →
      cp.E (fun σ => lam i σ ^ n) ≤ (41 * (p : ℝ) * aOf d p) ^ n :=
    fun i n hn1 hn => cp.endLam_moment hR hv i hn1 hn
  have hendF : ∀ j ∈ (retIdx (kStarA d p) : Finset (cp.N v → ℕ)), 2 ≤ grade j → ∀ σ,
      0 < wt cp.G p (aOf d p) cp.yp cp.ym σ cp.S →
        |dEven (cp.lN v) j (F σ) (cp.xi σ v)| ≤
          mE σ * starPhi p (cp.A σ v) (cp.B σ v) (cp.xi σ v) * ∏ i, lam i σ ^ (2 * j i) := by
    intro j _ _ σ hσ
    have hσc := cp.wtCore_ne_zero_of_wt hR hv hσ.ne'
    obtain ⟨hA, hB'⟩ := cp.root_psd_core hσc
    obtain ⟨⟨hα, hA1, hA2⟩, ⟨hβ, hB1, hB2⟩⟩ := cp.endLam_maj hR hv hσ.ne'
    rw [hFs σ hσc, hmEs σ hσ.ne', SecA.CA.starPhi_eq_of_pos hα hβ]
    have h := SecA.CA.endpoint_package (SecA.CA.psd_symm hA) (SecA.CA.psd_symm hB')
      le_rfl le_rfl hp2 hα hβ (cp.endLam_nonneg hR σ v) hA1 hA2 hB1 hB2 (hend σ hσ.ne') j
    refine h.trans (le_of_eq ?_)
    ring
  obtain ⟨hdL, hdL4', hdL4⟩ := hR.endL_facts
  have hT := cp.trans hR hv F hFc m' hm0 hM hmom' hsm hder hvan mE lam hmE0 hl0 hME
    (by have := hR.treg.aOf_pos; positivity) hmomE' hmoml hendF hdL hdL4
  -- back to the uncut observable
  have e1 : cp.coreE v (fun σ =>
      gaussE (clipObs (quadFn (c σ) (ℓ σ) (Q σ)) p p (cp.A σ v) (cp.B σ v)) -
        radE (clipObs (quadFn (c σ) (ℓ σ) (Q σ)) p p (cp.A σ v) (cp.B σ v))) =
      cp.coreE v (fun σ => gaussE (F σ) - radE (F σ)) :=
    SecA.coreE_congr_of_supp cp.G fun σ hσ => by rw [hFs σ hσ]
  have e2 : ∀ i : cp.N v, cp.E (fun σ =>
      (pderiv i)^[4] (clipObs (quadFn (c σ) (ℓ σ) (Q σ)) p p (cp.A σ v) (cp.B σ v))
        (cp.xi σ v) / starPhi p (cp.A σ v) (cp.B σ v) (cp.xi σ v)) =
      cp.E (fun σ => (pderiv i)^[4] (F σ) (cp.xi σ v) /
        starPhi p (cp.A σ v) (cp.B σ v) (cp.xi σ v)) := fun i =>
    lawE_congr cp.G fun σ hσ => by rw [hFs σ (cp.wtCore_ne_zero_of_wt hR hv hσ)]
  rw [e1]
  simp only [e2]
  refine hT.trans ?_
  have h0 : 0 ≤ (d : ℝ) * (41 * (p : ℝ) * aOf d p) ^ 4 := by positivity
  have h1 : ((d : ℝ) * (41 * (p : ℝ) * aOf d p) ^ 4) ^ 2 ≤ (41 ^ 4 / 4 * ((p : ℝ) ^ 4 / d)) ^ 2 :=
    pow_le_pow_left₀ h0 hdL4' 2
  have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * Real.exp 2 * ME)
  linarith

end CapPoint

end BiluLinial.Tight
