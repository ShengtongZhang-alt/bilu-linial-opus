/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecC.RowRem
public import BiluLinial.Tight.SecC.TransferRet

/-!
# Helpers for CR-G3: the unmarked endpoint majorant of `F = rowNum`

Node CR-G3 of `docs/tight/BP_SECC.md` (`SecC/RowG3.lean`), source lines 1153–1190.

* `quadMaj_prod_interior`: at a point `ξ` where `|(Xξ)_i| ≤ m_X λ_i`, `|X_ik| ≤ m_X λ_i λ_k` (and
  the same for `Y`, both symmetric), the prefactor `c q_{XY}` satisfies `QuadMaj` with scale
  `c m_X m_Y Λ`, `Λ = Σ_k λ_k²` (`(XYξ)_i = Σ_k X_ik (Yξ)_k`).
* `rowNum_endpoint_le` (A-MAJ, `SecA.pderivList_clipObs_le_of_interior`, on the two clipped terms
  of `rowNum`, `rowNum_eq_clipObs`, with `m_α = α`, `m_β = β`):
  `|∂^{2j}F(ξ)| ≤ 2p Λ α^p β^p Π_i (25 p² λ_i²)^{j_i}`.
* `rowNum_retained_pointwise` (at a supported signing, weights `λ = lamR`, `branch_majorant`;
  `25p²λ_i² ≤ (26p²/d) Z`, `lam_sq_le`, hence `Λ ≤ 2Z`):
  `|∂^{2j}F(ξ)/Φ(ξ)| ≤ 4p Z Π_i ((26p²/d) Z)^{j_i}`.
* `sum_ret3_prod_le` (A-CNT per grade, as in `sum_ret_prod_le`):
  `Σ_{3 ≤ |j|_g ≤ k} Π_i x^{j_i} ≤ e² Σ_{2 ≤ g < k} (d x²)^{g+1}`.
* `ZR_pow_trunc` (`trunc_moment` with `X = 1`, `Z_moment_le`, `two_pow_kIL`):
  `E Z^{2n} ≤ 1024^{2n} (1 + ϑ)` for `4(4n + 4 kIL d) ≤ p`.
-/

@[expose] public section

namespace BiluLinial.Tight

namespace SecC

universe u

open Matrix

open scoped ContDiff

/-! ### Star level -/

section Star

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- `QuadMaj` for `c q_{XY}` at an interior point from entrywise majorants. -/
theorem quadMaj_prod_interior {X Y : Matrix ι ι ℝ} (hXs : ∀ i k, X i k = X k i)
    (hYs : ∀ i k, Y i k = Y k i) {ξ lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i) {mX mY c : ℝ}
    (hc : 0 ≤ c) (hmX : 0 ≤ mX) (hmY : 0 ≤ mY)
    (hX1 : ∀ i, |(X *ᵥ ξ) i| ≤ mX * lam i) (hX2 : ∀ i k, |X i k| ≤ mX * lam i * lam k)
    (hY1 : ∀ i, |(Y *ᵥ ξ) i| ≤ mY * lam i) (hY2 : ∀ i k, |Y i k| ≤ mY * lam i * lam k) :
    QuadMaj 0 0 (c • (X * Y)) ξ (c * mX * mY * ∑ k, lam k ^ 2) lam := by
  have hΛ : 0 ≤ ∑ k, lam k ^ 2 := by positivity
  -- `|((X Y) ξ)_i| ≤ m_X m_Y λ_i Λ`
  have hXY : ∀ (X Y : Matrix ι ι ℝ) (mX mY : ℝ), 0 ≤ mX → 0 ≤ mY →
      (∀ i k, |X i k| ≤ mX * lam i * lam k) → (∀ i, |(Y *ᵥ ξ) i| ≤ mY * lam i) →
      ∀ i, |((X * Y) *ᵥ ξ) i| ≤ mX * mY * lam i * ∑ k, lam k ^ 2 := by
    intro X Y mX mY hmX hmY hX2 hY1 i
    rw [← mulVec_mulVec]
    simp only [mulVec, dotProduct]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [abs_mul]
    have h1 := hX2 i k
    have h2 := hY1 k
    have := hlam i
    have := hlam k
    calc |X i k| * |∑ x, Y k x * ξ x| ≤ (mX * lam i * lam k) * (mY * lam k) :=
          mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
      _ = mX * mY * lam i * lam k ^ 2 := by ring
  -- `|(X Y)_ik| ≤ m_X m_Y λ_i λ_k Λ`
  have hXYe : ∀ (X Y : Matrix ι ι ℝ) (mX mY : ℝ), 0 ≤ mX → 0 ≤ mY →
      (∀ i k, |X i k| ≤ mX * lam i * lam k) → (∀ i k, |Y i k| ≤ mY * lam i * lam k) →
      ∀ i k, |(X * Y) i k| ≤ mX * mY * lam i * lam k * ∑ l, lam l ^ 2 := by
    intro X Y mX mY hmX hmY hX2 hY2 i k
    rw [mul_apply]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun l _ => ?_
    rw [abs_mul]
    have h1 := hX2 i l
    have h2 := hY2 l k
    have := hlam i
    have := hlam k
    have := hlam l
    calc |X i l| * |Y l k| ≤ (mX * lam i * lam l) * (mY * lam l * lam k) :=
          mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
      _ = mX * mY * lam i * lam k * lam l ^ 2 := by ring
  have hT : (X * Y)ᵀ = Y * X := by
    rw [transpose_mul]
    congr 1 <;> ext i k
    · exact hYs k i
    · exact hXs k i
  refine ⟨?_, fun i => ?_, fun i k => ?_⟩
  · have e : quadFn 0 0 (c • (X * Y)) ξ = c * ∑ k, (X *ᵥ ξ) k * (Y *ᵥ ξ) k := by
      have hXt : ξ ᵥ* X = X *ᵥ ξ := by
        rw [← mulVec_transpose]
        congr 1
        ext i k
        exact hXs k i
      rw [quadFn_zero_zero, qForm, smul_mulVec, dotProduct_smul, ← mulVec_mulVec,
        dotProduct_mulVec, hXt, smul_eq_mul]
      rfl
    rw [e, abs_mul, abs_of_nonneg hc]
    have hs : |∑ k, (X *ᵥ ξ) k * (Y *ᵥ ξ) k| ≤ mX * mY * ∑ k, lam k ^ 2 := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun k _ => ?_
      rw [abs_mul]
      have := hlam k
      calc |(X *ᵥ ξ) k| * |(Y *ᵥ ξ) k| ≤ (mX * lam k) * (mY * lam k) :=
            mul_le_mul (hX1 k) (hY1 k) (abs_nonneg _) (by positivity)
        _ = mX * mY * lam k ^ 2 := by ring
    calc c * |∑ k, (X *ᵥ ξ) k * (Y *ᵥ ξ) k| ≤ c * (mX * mY * ∑ k, lam k ^ 2) :=
          mul_le_mul_of_nonneg_left hs hc
      _ = c * mX * mY * ∑ k, lam k ^ 2 := by ring
  · rw [transpose_smul, hT]
    simp only [Pi.zero_apply, zero_add, add_mulVec, smul_mulVec, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
    rw [← mul_add, abs_mul, abs_of_nonneg hc]
    have h1 := hXY X Y mX mY hmX hmY hX2 hY1 i
    have h2 := hXY Y X mY mX hmY hmX hY2 hX1 i
    have h3 := abs_add_le (((X * Y) *ᵥ ξ) i) (((Y * X) *ᵥ ξ) i)
    have h4 : 0 ≤ mX * mY * lam i * ∑ k, lam k ^ 2 := by have := hlam i; positivity
    have h5 : |((X * Y) *ᵥ ξ) i + ((Y * X) *ᵥ ξ) i| ≤ 2 * (mX * mY * lam i * ∑ k, lam k ^ 2) := by
      linarith
    calc c * |((X * Y) *ᵥ ξ) i + ((Y * X) *ᵥ ξ) i| ≤ c * (2 * (mX * mY * lam i * ∑ k, lam k ^ 2)) :=
          mul_le_mul_of_nonneg_left h5 hc
      _ = 2 * (c * mX * mY * ∑ k, lam k ^ 2) * lam i := by ring
  · simp only [Matrix.smul_apply, smul_eq_mul]
    rw [← mul_add, abs_mul, abs_of_nonneg hc]
    have h1 := hXYe X Y mX mY hmX hmY hX2 hY2 i k
    have h2 := hXYe X Y mX mY hmX hmY hX2 hY2 k i
    have h3 := abs_add_le ((X * Y) i k) ((X * Y) k i)
    have h5 : |(X * Y) i k + (X * Y) k i| ≤ 2 * (mX * mY * lam i * lam k * ∑ l, lam l ^ 2) := by
      linarith
    calc c * |(X * Y) i k + (X * Y) k i| ≤ c * (2 * (mX * mY * lam i * lam k * ∑ l, lam l ^ 2)) :=
          mul_le_mul_of_nonneg_left h5 hc
      _ = 2 * (c * mX * mY * ∑ k, lam k ^ 2) * lam i * lam k := by ring

/-- **The unmarked endpoint majorant of `F = rowNum`** (A-MAJ at an interior point). -/
theorem rowNum_endpoint_le {p : ℕ} {A B : Matrix ι ι ℝ} (hAs : ∀ i k, A i k = A k i)
    (hBs : ∀ i k, B i k = B k i) {ξ : ι → ℝ} (hα : 0 < 1 - qForm A ξ) (hβ : 0 < 1 - qForm B ξ)
    {lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i)
    (hA1 : ∀ i, |(A *ᵥ ξ) i| ≤ (1 - qForm A ξ) * lam i)
    (hA2 : ∀ i k, |A i k| ≤ (1 - qForm A ξ) * lam i * lam k)
    (hB1 : ∀ i, |(B *ᵥ ξ) i| ≤ (1 - qForm B ξ) * lam i)
    (hB2 : ∀ i k, |B i k| ≤ (1 - qForm B ξ) * lam i * lam k) (j : ι → ℕ)
    (hj : 2 * ∑ i, j i + 3 ≤ p) :
    |dEven (Finset.univ : Finset ι).toList j (rowNum p A B) ξ| ≤
      2 * p * (∑ k, lam k ^ 2) * ((1 - qForm A ξ) ^ p * (1 - qForm B ξ) ^ p) *
        ∏ i, (25 * (p : ℝ) ^ 2 * lam i ^ 2) ^ j i := by
  set α := 1 - qForm A ξ with hαdef
  set β := 1 - qForm B ξ with hβdef
  set Λ := ∑ k, lam k ^ 2 with hΛdef
  have hΛ : 0 ≤ Λ := by positivity
  set l := dEvenList (Finset.univ : Finset ι).toList j with hl
  have hlen : l.length = 2 * ∑ i, j i := length_dEvenList_univ_aux j
  have hp1 : (2 : ℝ) ≤ p := by exact_mod_cast (by omega : 2 ≤ p)
  have hg1 : ContDiff ℝ ∞ (quadFn 0 0 (((p : ℝ) - 1) • (A * A))) := by
    rw [quadFn_zero_zero]; exact contDiff_qForm' _
  have hg2 : ContDiff ℝ ∞ (quadFn 0 0 ((p : ℝ) • (A * B))) := by
    rw [quadFn_zero_zero]; exact contDiff_qForm' _
  have hc1 := SecA.contDiff_clipObs hg1 (p - 2) p A B
  have hc2 := SecA.contDiff_clipObs hg2 (p - 1) (p - 1) A B
  have hm1 : l.length ≤ min (p - 2) p - 1 := by omega
  have hm2 : l.length ≤ min (p - 1) (p - 1) - 1 := by omega
  have hQA := quadMaj_neg hAs hα hA1 hA2
  have hQB := quadMaj_neg hBs hβ hB1 hB2
  have hq1 := quadMaj_prod_interior hAs hAs hlam (c := (p : ℝ) - 1) (by linarith) hα.le hα.le
    hA1 hA2 hA1 hA2
  have hq2 := quadMaj_prod_interior hAs hBs hlam (c := (p : ℝ)) (by linarith) hα.le hβ.le
    hA1 hA2 hB1 hB2
  have e1 := SecA.pderivList_clipObs_le_of_interior (e₁ := p - 2) (e₂ := p)
    (by linarith : qForm A ξ < 1) (by linarith : qForm B ξ < 1) hlam hq1 hQA hQB l
  have e2 := SecA.pderivList_clipObs_le_of_interior (e₁ := p - 1) (e₂ := p - 1)
    (by linarith : qForm A ξ < 1) (by linarith : qForm B ξ < 1) hlam hq2 hQA hQB l
  rw [dEven_eq_pderivList, ← hl, rowNum_eq_clipObs, pderivList_add l
    (hc1.of_le (by exact_mod_cast hm1)) (hc2.of_le (by exact_mod_cast hm2)), Pi.add_apply]
  have hP : 0 ≤ (l.map lam).prod :=
    List.prod_nonneg fun y hy => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hy
      exact hlam i
  have hb1 : 2 * (1 + ((p - 2 : ℕ) : ℝ) + (p : ℝ)) ≤ 5 * p := by
    have : ((p - 2 : ℕ) : ℝ) ≤ p := by exact_mod_cast Nat.sub_le p 2
    linarith
  have hb2 : 2 * (1 + ((p - 1 : ℕ) : ℝ) + ((p - 1 : ℕ) : ℝ)) ≤ 5 * p := by
    have : ((p - 1 : ℕ) : ℝ) = p - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    rw [this]
    linarith
  have hk1 := pow_le_pow_left₀ (by positivity) hb1 l.length
  have hk2 := pow_le_pow_left₀ (by positivity) hb2 l.length
  have ea : α ^ (p - 2) * α * α = α ^ p := by
    rw [mul_assoc, ← sq, ← pow_add, Nat.sub_add_cancel (by omega)]
  have ea1 : α ^ (p - 1) * α = α ^ p := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega)]
  have eb1 : β ^ (p - 1) * β = β ^ p := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega)]
  have hΦ0 : 0 ≤ α ^ p * β ^ p := by positivity
  have h5 : 0 ≤ (5 * (p : ℝ)) ^ l.length := by positivity
  -- the two terms
  have t1 : ((p : ℝ) - 1) * α * α * Λ * α ^ (p - 2) * β ^ p *
      (2 * (1 + ((p - 2 : ℕ) : ℝ) + (p : ℝ))) ^ l.length * (l.map lam).prod ≤
      ((p : ℝ) - 1) * Λ * (α ^ p * β ^ p) * (5 * (p : ℝ)) ^ l.length * (l.map lam).prod := by
    rw [show ((p : ℝ) - 1) * α * α * Λ * α ^ (p - 2) * β ^ p =
      ((p : ℝ) - 1) * Λ * (α ^ (p - 2) * α * α * β ^ p) by ring, ea]
    have h0 : 0 ≤ ((p : ℝ) - 1) * Λ * (α ^ p * β ^ p) :=
      mul_nonneg (mul_nonneg (by linarith) hΛ) hΦ0
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk1 (by
      simpa [mul_assoc] using h0)) hP
  have t2 : (p : ℝ) * α * β * Λ * α ^ (p - 1) * β ^ (p - 1) *
      (2 * (1 + ((p - 1 : ℕ) : ℝ) + ((p - 1 : ℕ) : ℝ))) ^ l.length * (l.map lam).prod ≤
      (p : ℝ) * Λ * (α ^ p * β ^ p) * (5 * (p : ℝ)) ^ l.length * (l.map lam).prod := by
    rw [show (p : ℝ) * α * β * Λ * α ^ (p - 1) * β ^ (p - 1) =
      (p : ℝ) * Λ * ((α ^ (p - 1) * α) * (β ^ (p - 1) * β)) by ring, ea1, eb1]
    have h0 : 0 ≤ (p : ℝ) * Λ * (α ^ p * β ^ p) := by positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk2 h0) hP
  have hprod : (5 * (p : ℝ)) ^ (2 * ∑ i, j i) * ∏ i, lam i ^ (2 * j i) =
      ∏ i, (25 * (p : ℝ) ^ 2 * lam i ^ 2) ^ j i := by
    rw [Finset.mul_sum, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [pow_mul, pow_mul, ← mul_pow]
    ring
  have hlprod : (l.map lam).prod = ∏ i, lam i ^ (2 * j i) := prod_map_dEvenList_univ_aux j lam
  calc _ ≤ |pderivList l (clipObs (quadFn 0 0 (((p : ℝ) - 1) • (A * A))) (p - 2) p A B) ξ| +
        |pderivList l (clipObs (quadFn 0 0 ((p : ℝ) • (A * B))) (p - 1) (p - 1) A B) ξ| :=
        abs_add_le _ _
    _ ≤ ((p : ℝ) - 1) * Λ * (α ^ p * β ^ p) * (5 * (p : ℝ)) ^ l.length * (l.map lam).prod +
        (p : ℝ) * Λ * (α ^ p * β ^ p) * (5 * (p : ℝ)) ^ l.length * (l.map lam).prod :=
        add_le_add (e1.trans t1) (e2.trans t2)
    _ ≤ 2 * p * Λ * (α ^ p * β ^ p) * ((5 * (p : ℝ)) ^ l.length * (l.map lam).prod) := by
        have := mul_nonneg (mul_nonneg hΛ hΦ0) (mul_nonneg h5 hP)
        nlinarith
    _ = _ := by rw [hlen, hlprod, hprod]

/-- One grade of A-CNT with `T = 1/(d x²)`: for `d x ≥ 2` and `|ι| ≤ d`,
`Σ_{j ∈ topIdx g} Π_i x^{j_i} ≤ e² (d x²)^{g+1}`. -/
theorem sum_topIdx_prod_le_exp (g : ℕ) {d : ℝ} (hd : 1 ≤ d) (hcard : (Fintype.card ι : ℝ) ≤ d)
    {x : ℝ} (hdx : 2 ≤ d * x) :
    ∑ j ∈ (topIdx g : Finset (ι → ℕ)), ∏ i, x ^ j i ≤ Real.exp 2 * (d * x ^ 2) ^ (g + 1) := by
  have hd0 : 0 < d := by linarith
  have hx : 0 < x := by
    by_contra h
    push_neg at h
    nlinarith
  have hT : 0 < 1 / (d * x ^ 2) := by positivity
  have hxT : x * (1 / (d * x ^ 2)) = 1 / (d * x) := by field_simp
  have hxT2 : x * (1 / (d * x ^ 2)) ≤ 1 / 2 := by
    rw [hxT, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  refine (SecA.sum_topIdx_prod_pow_le g hx hT (by linarith)).trans ?_
  have h1 : 1 / (1 / (d * x ^ 2)) = d * x ^ 2 := one_div_one_div _
  have e : x ^ 2 * (1 / (d * x ^ 2)) = 1 / d := by field_simp
  have hq : 1 / 2 ≤ 1 - x * (1 / (d * x ^ 2)) := by linarith
  have h2 : 1 + x ^ 2 * (1 / (d * x ^ 2)) / (1 - x * (1 / (d * x ^ 2))) ≤ 1 + 2 / d := by
    rw [e]
    have : 1 / d / (1 - x * (1 / (d * x ^ 2))) ≤ 1 / d / (1 / 2) :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) hq
    have e2 : 1 / d / (1 / 2) = 2 / d := by field_simp
    linarith
  have h20 : 0 ≤ 1 + x ^ 2 * (1 / (d * x ^ 2)) / (1 - x * (1 / (d * x ^ 2))) := by
    have : 0 ≤ x ^ 2 * (1 / (d * x ^ 2)) / (1 - x * (1 / (d * x ^ 2))) :=
      div_nonneg (by positivity) (by linarith)
    linarith
  have h3 : (1 + 2 / d) ^ Fintype.card ι ≤ Real.exp 2 := by
    calc (1 + 2 / d) ^ Fintype.card ι ≤ Real.exp (2 / d) ^ Fintype.card ι := by
          gcongr
          linarith [Real.add_one_le_exp (2 / d)]
      _ = Real.exp (Fintype.card ι * (2 / d)) := by rw [← Real.exp_nat_mul]
      _ ≤ Real.exp 2 := Real.exp_le_exp.mpr (by
          rw [mul_div_assoc', div_le_iff₀ hd0]
          linarith)
  rw [h1]
  calc (d * x ^ 2) ^ (g + 1) *
        (1 + x ^ 2 * (1 / (d * x ^ 2)) / (1 - x * (1 / (d * x ^ 2)))) ^ Fintype.card ι
      ≤ (d * x ^ 2) ^ (g + 1) * (1 + 2 / d) ^ Fintype.card ι :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h20 h2 _) (by positivity)
    _ ≤ (d * x ^ 2) ^ (g + 1) * Real.exp 2 :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = Real.exp 2 * (d * x ^ 2) ^ (g + 1) := by ring

/-- **Grades `3 ≤ |j|_g ≤ k`** (A-CNT per grade): for `d x ≥ 2` and `|ι| ≤ d`,
`Σ_{j ∈ retIdx k, |j|_g ≥ 3} Π_i x^{j_i} ≤ e² Σ_{g < k - 2} (d x²)^{g+3}`. -/
theorem sum_ret3_prod_le (k : ℕ) {d : ℝ} (hd : 1 ≤ d) (hcard : (Fintype.card ι : ℝ) ≤ d)
    {x : ℝ} (hdx : 2 ≤ d * x) :
    ∑ j ∈ (retIdx k : Finset (ι → ℕ)).filter (fun j => 3 ≤ grade j), ∏ i, x ^ j i ≤
      Real.exp 2 * ∑ g ∈ Finset.range (k - 2), (d * x ^ 2) ^ (g + 3) := by
  have hx : 0 < x := by
    by_contra h
    push_neg at h
    nlinarith
  have hsub : (retIdx k : Finset (ι → ℕ)).filter (fun j => 3 ≤ grade j) ⊆
      (Finset.range (k - 2)).biUnion (fun g => (topIdx (g + 2) : Finset (ι → ℕ))) := by
    intro j hj
    obtain ⟨hjr, hg3⟩ := Finset.mem_filter.1 hj
    obtain ⟨hadm, hgr⟩ := mem_retIdx.1 hjr
    exact Finset.mem_biUnion.2
      ⟨grade j - 3, Finset.mem_range.2 (by omega), mem_topIdx.2 ⟨hadm, by omega⟩⟩
  have hdisj : ((Finset.range (k - 2) : Finset ℕ) : Set ℕ).PairwiseDisjoint
      (fun g => (topIdx (g + 2) : Finset (ι → ℕ))) := by
    intro g _ g' _ hgg'
    change Disjoint (topIdx (g + 2) : Finset (ι → ℕ)) (topIdx (g' + 2))
    refine Finset.disjoint_left.2 fun j hj hj' => hgg' ?_
    have h1 := (mem_topIdx.1 hj).2
    have h2 := (mem_topIdx.1 hj').2
    omega
  have hnn : ∀ j : ι → ℕ, 0 ≤ ∏ i, x ^ j i := fun j =>
    Finset.prod_nonneg fun i _ => pow_nonneg hx.le _
  calc ∑ j ∈ (retIdx k : Finset (ι → ℕ)).filter (fun j => 3 ≤ grade j), ∏ i, x ^ j i
      ≤ ∑ j ∈ (Finset.range (k - 2)).biUnion (fun g => (topIdx (g + 2) : Finset (ι → ℕ))),
          ∏ i, x ^ j i :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => hnn j
    _ = ∑ g ∈ Finset.range (k - 2), ∑ j ∈ (topIdx (g + 2) : Finset (ι → ℕ)), ∏ i, x ^ j i :=
        Finset.sum_biUnion hdisj
    _ ≤ ∑ g ∈ Finset.range (k - 2), Real.exp 2 * (d * x ^ 2) ^ (g + 3) :=
        Finset.sum_le_sum fun g _ => sum_topIdx_prod_le_exp (g + 2) hd hcard hdx
    _ = Real.exp 2 * ∑ g ∈ Finset.range (k - 2), (d * x ^ 2) ^ (g + 3) := by rw [Finset.mul_sum]

end Star

/-! ### Graph level -/

section Graph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable {d p : ℕ}

/-- **Pointwise unmarked bound** at a supported signing: `|∂^{2j}F(ξ)/Φ(ξ)| ≤ 4p Z Π_i x^{j_i}`,
`x = (26p²/d) Z`. -/
theorem rowNum_retained_pointwise (hR : TRegime d p) {S : Finset V} {lam : ℝ}
    (hC : CapCtx G d p S lam) {yp ym : V → ℝ} (hyp : InCube (lam * sOf d p) yp)
    (hym : InCube (lam * sOf d p) ym) {v : V} (hv : v ∈ S) [Nonempty (nbhd G S v)]
    {σ : Config V} (hσ : wt G p (aOf d p) yp ym σ S ≠ 0) (j : nbhd G S v → ℕ)
    (hj : 2 * ∑ i, j i + 3 ≤ p) :
    |dEven (Finset.univ : Finset (nbhd G S v)).toList j
        (rowNum p (rootMat G (aOf d p) 1 yp σ S v) (rootMat G (aOf d p) (-1) ym σ S v))
          (rootSigns G σ S v) /
      starPhi p (rootMat G (aOf d p) 1 yp σ S v) (rootMat G (aOf d p) (-1) ym σ S v)
        (rootSigns G σ S v)| ≤
      4 * p * ZR G (aOf d p) yp ym σ S v *
        ∏ i, (26 * (p : ℝ) ^ 2 / d * ZR G (aOf d p) yp ym σ S v) ^ j i := by
  obtain ⟨hα, hA1, hA2⟩ := branch_majorant G hR hC hyp hym (isBranch_plus yp ym) hv hσ
  obtain ⟨hβ, hB1, hB2⟩ := branch_majorant G hR hC hyp hym (isBranch_minus yp ym) hv hσ
  have ha := hR.aOf_pos
  have hdR := hR.ten_pow_six_le_d
  have hd0 : (0 : ℝ) < d := lt_of_lt_of_le (by norm_num) hdR
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hlam0 : ∀ i : nbhd G S v, 0 ≤ lamR G (aOf d p) yp ym σ S v i := fun i =>
    mul_nonneg ha.le (add_nonneg (mul_nonneg zero_le_two (Real.sqrt_nonneg _))
      (mul_nonneg zero_le_two (Real.sqrt_nonneg _)))
  have hEM := rowNum_endpoint_le (p := p) (rootMat_apply_comm G _ 1 yp σ S v)
    (rootMat_apply_comm G _ (-1) ym σ S v) hα hβ hlam0 hA1 hA2 hB1 hB2 j hj
  set α := 1 - qForm (rootMat G (aOf d p) 1 yp σ S v) (rootSigns G σ S v) with hαdef
  set β := 1 - qForm (rootMat G (aOf d p) (-1) ym σ S v) (rootSigns G σ S v) with hβdef
  set Z := ZR G (aOf d p) yp ym σ S v with hZdef
  have hΦ : starPhi p (rootMat G (aOf d p) 1 yp σ S v) (rootMat G (aOf d p) (-1) ym σ S v)
      (rootSigns G σ S v) = α ^ p * β ^ p := by
    simp only [starPhi, clipF]
    rw [← hαdef, ← hβdef, max_eq_left hα.le, max_eq_left hβ.le]
  have hΦ0 : 0 < α ^ p * β ^ p := mul_pos (pow_pos hα p) (pow_pos hβ p)
  have hlsq : ∀ i,
      25 * (p : ℝ) ^ 2 * lamR G (aOf d p) yp ym σ S v i ^ 2 ≤ 26 * (p : ℝ) ^ 2 / d * Z :=
    fun i => lam_sq_le G hR hC hyp hym hσ i
  have hZ0 : 0 ≤ Z := by
    simp only [hZdef, ZR]
    positivity
  have hcard : ((Finset.univ : Finset (nbhd G S v)).card : ℝ) ≤ d := by
    rw [Finset.card_univ]
    exact_mod_cast card_nbhd_le G hC.deg S v
  have hΛ : ∑ k, lamR G (aOf d p) yp ym σ S v k ^ 2 ≤ 2 * Z := by
    have hk : ∀ k, lamR G (aOf d p) yp ym σ S v k ^ 2 ≤ 26 / 25 / d * Z := fun k => by
      have h := hlsq k
      rw [show 26 * (p : ℝ) ^ 2 / d * Z = 25 * (p : ℝ) ^ 2 * (26 / 25 / d * Z) by
        field_simp] at h
      exact le_of_mul_le_mul_left h (by positivity)
    calc ∑ k, lamR G (aOf d p) yp ym σ S v k ^ 2 ≤ ∑ _k : nbhd G S v, 26 / 25 / d * Z :=
          Finset.sum_le_sum fun k _ => hk k
      _ = ((Finset.univ : Finset (nbhd G S v)).card : ℝ) * (26 / 25 / d * Z) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ d * (26 / 25 / d * Z) := mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = 26 / 25 * Z := by field_simp
      _ ≤ 2 * Z := by linarith
  have hprod : ∏ i, (25 * (p : ℝ) ^ 2 * lamR G (aOf d p) yp ym σ S v i ^ 2) ^ j i ≤
      ∏ i, (26 * (p : ℝ) ^ 2 / d * Z) ^ j i :=
    Finset.prod_le_prod₀ (fun i _ => pow_nonneg (by positivity) _)
      fun i _ => pow_le_pow_left₀ (by positivity) (hlsq i) _
  have hP0 : 0 ≤ ∏ i, (25 * (p : ℝ) ^ 2 * lamR G (aOf d p) yp ym σ S v i ^ 2) ^ j i :=
    Finset.prod_nonneg fun i _ => pow_nonneg (by positivity) _
  rw [abs_div, hΦ, abs_of_pos hΦ0, div_le_iff₀ hΦ0]
  calc _ ≤ 2 * p * (∑ k, lamR G (aOf d p) yp ym σ S v k ^ 2) * (α ^ p * β ^ p) *
        ∏ i, (25 * (p : ℝ) ^ 2 * lamR G (aOf d p) yp ym σ S v i ^ 2) ^ j i := hEM
    _ ≤ 2 * p * (2 * Z) * (α ^ p * β ^ p) * ∏ i, (26 * (p : ℝ) ^ 2 / d * Z) ^ j i := by
        gcongr
    _ = 4 * p * Z * (∏ i, (26 * (p : ℝ) ^ 2 / d * Z) ^ j i) * (α ^ p * β ^ p) := by ring

end Graph

end SecC

end BiluLinial.Tight
