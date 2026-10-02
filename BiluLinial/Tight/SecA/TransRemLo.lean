/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecA.Transfer

/-!
# `A-REM` with a restricted moment range (node `A-REMlo`)

`CapPoint.trans_rem` (A-REM) asks for own-core moments `E mⁿ ≤ Mⁿ` for all `2n ≤ p`, but its
proof (A-CREM, Hölder with `n = 1 + Σ j_i ≤ 2k_* + 3`) only uses `n ≤ 2k_* + 3`. Sup majorants
that are products of several core diagonals (TB.WT5r°: up to `m₀ + 2` of them) have moments
only up to order `p/(2(m₀ + 2))`, so the restricted form is needed there.

* `CapPoint.crem_lo`: `A-CREM` with `hmom` for `n ≤ 2k + 3`.
* `CapPoint.trans_rem_lo`: `A-REM` with `hmom` for `n ≤ 2k_* + 3` and the derivative constant
  `8p` (instead of `5p`; (E6) has `(8p)^{4k_*+4}`, so the conclusion `≤ M e^{-p}/d · F_H` is
  unchanged).

Proofs: verbatim those of `crem`, `trans_rem`.
-/

@[expose] public section

universe u

namespace BiluLinial.Tight

open Matrix Finset

namespace CapPoint

variable {d p : ℕ} (cp : CapPoint.{u} d p)

/-- `A-CREM` with the own-core moment hypothesis only for `n ≤ 2k + 3` (all that the proof
uses). -/
theorem crem_lo (hR : RegA d p) {v : cp.V} (hv : v ∈ cp.S) (m : Config cp.V → ℝ)
    (hm0 : ∀ σ, 0 ≤ m σ) {M : ℝ} (hM : 0 < M)
    (k : ℕ)
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

/-- `A-REM` with the own-core moment hypothesis only for `n ≤ 2k_* + 3` and the derivative
constant `8p` (in place of `5p`). -/
theorem trans_rem_lo (hR : RegA d p) {v : cp.V} (hv : v ∈ cp.S)
    (F : Config cp.V → (cp.N v → ℝ) → ℝ) (m : Config cp.V → ℝ) (hm0 : ∀ σ, 0 ≤ m σ) {M : ℝ}
    (hM : 0 < M)
    (hmom : ∀ n : ℕ, 1 ≤ n → n ≤ 2 * kStarA d p + 3 →
      cp.coreE v (fun σ => m σ ^ n) ≤ M ^ n)
    (hsm : ∀ σ, SmoothBdd (4 * kStarA d p + 4) (F σ))
    (hder : ∀ σ, ∀ j ∈ (topIdx (kStarA d p) : Finset (cp.N v → ℕ)), ∀ x,
      |dEven (cp.lN v) j (F σ) x| ≤
        m σ * (8 * (p : ℝ)) ^ (2 * ∑ i, j i) * ∏ i, cp.bdiag σ v i ^ j i) :
    |cp.coreE v (fun σ => gaussE (F σ) -
        ∑ j ∈ (retIdx (kStarA d p) : Finset (cp.N v → ℕ)),
          ecoefM j * radE (dEven (cp.lN v) j (F σ)))| ≤
      M * Real.exp (-(p : ℝ)) / d * cp.FH v := by
  have hd := hR.d_pos
  have hp := hR.p_pos
  have hk7 := hR.four_kStar_add_seven_le
  set k := kStarA d p with hk
  have h5p : (1 : ℝ) ≤ 8 * p := by linarith [hR.one_le_p]
  -- pointwise: (E4) and the order count `Σ j_i ≤ 2(k+1)`
  have hpt : ∀ σ, 0 < wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v →
      |gaussE (F σ) - ∑ j ∈ (retIdx k : Finset (cp.N v → ℕ)),
          ecoefM j * radE (dEven (cp.lN v) j (F σ))| ≤
        2 * (8 * (p : ℝ)) ^ (4 * k + 4) *
          (m σ * ∑ j ∈ (topIdx k : Finset (cp.N v → ℕ)), ∏ i, cp.bdiag σ v i ^ j i) := by
    intro σ hσ
    have h : |gaussE (F σ) - ∑ j ∈ (retIdx k : Finset (cp.N v → ℕ)),
          ecoefM j * radE (dEven (cp.lN v) j (F σ))| ≤
        2 * ∑ j ∈ (topIdx k : Finset (cp.N v → ℕ)),
          m σ * (8 * (p : ℝ)) ^ (2 * ∑ i, j i) * ∏ i, cp.bdiag σ v i ^ j i :=
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
    have hpow : (8 * (p : ℝ)) ^ (2 * ∑ i, j i) ≤ (8 * (p : ℝ)) ^ (4 * k + 4) :=
      pow_le_pow_right₀ h5p (by omega)
    calc m σ * (8 * (p : ℝ)) ^ (2 * ∑ i, j i) * ∏ i, cp.bdiag σ v i ^ j i
        = (8 * (p : ℝ)) ^ (2 * ∑ i, j i) * (m σ * ∏ i, cp.bdiag σ v i ^ j i) := by ring
      _ ≤ (8 * (p : ℝ)) ^ (4 * k + 4) * (m σ * ∏ i, cp.bdiag σ v i ^ j i) :=
          mul_le_mul_of_nonneg_right hpow hb
  have h1 := cp.abs_coreE_le v hpt
  have h2 : cp.coreE v (fun σ => 2 * (8 * (p : ℝ)) ^ (4 * k + 4) *
        (m σ * ∑ j ∈ (topIdx k : Finset (cp.N v → ℕ)), ∏ i, cp.bdiag σ v i ^ j i)) =
      2 * (8 * (p : ℝ)) ^ (4 * k + 4) * cp.coreE v (fun σ =>
        m σ * ∑ j ∈ (topIdx k : Finset (cp.N v → ℕ)), ∏ i, cp.bdiag σ v i ^ j i) :=
    SecA.wavg_const_mul _ _ _
  have h3 := cp.crem_lo hR hv m hm0 hM k hmom (by omega)
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
  have key : 2 * Real.exp 3 * (8 * (p : ℝ)) ^ (4 * k + 4) * (5 / (d : ℝ)) ^ (k + 1) *
      40 ^ p ≤ Real.exp (-(p : ℝ)) / d := by
    calc 2 * Real.exp 3 * (8 * (p : ℝ)) ^ (4 * k + 4) * (5 / (d : ℝ)) ^ (k + 1) * 40 ^ p
        ≤ (p : ℝ) * (8 * (p : ℝ)) ^ (4 * k + 4) * (8 / (d : ℝ)) ^ (k + 1) * 40 ^ p := by
          gcongr
          all_goals first | linarith | norm_num
      _ = (p : ℝ) * 40 ^ p * (8 * (p : ℝ)) ^ (4 * k + 4) * 8 ^ (k + 1) / (d : ℝ) ^ k / d := by
          have hd0 : (d : ℝ) ≠ 0 := hd.ne'
          rw [div_pow, pow_succ (d : ℝ) k]
          field_simp
          try ring
      _ ≤ Real.exp (-(p : ℝ)) / d := div_le_div_of_nonneg_right hE6 hd.le
  calc _ ≤ _ := h1
    _ = _ := h2
    _ ≤ 2 * (8 * (p : ℝ)) ^ (4 * k + 4) * (M * (5 / (d : ℝ)) ^ (k + 1) * Real.exp 3) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = M * (2 * Real.exp 3 * (8 * (p : ℝ)) ^ (4 * k + 4) * (5 / (d : ℝ)) ^ (k + 1)) * 1 := by
        ring
    _ ≤ M * (2 * Real.exp 3 * (8 * (p : ℝ)) ^ (4 * k + 4) * (5 / (d : ℝ)) ^ (k + 1)) *
          (40 ^ p * cp.FH v) := mul_le_mul_of_nonneg_left hfl (by positivity)
    _ = M * (2 * Real.exp 3 * (8 * (p : ℝ)) ^ (4 * k + 4) * (5 / (d : ℝ)) ^ (k + 1) *
          40 ^ p) * cp.FH v := by ring
    _ ≤ M * (Real.exp (-(p : ℝ)) / d) * cp.FH v :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left key hM.le) hFH.le
    _ = M * Real.exp (-(p : ℝ)) / d * cp.FH v := by ring

end CapPoint

end BiluLinial.Tight
