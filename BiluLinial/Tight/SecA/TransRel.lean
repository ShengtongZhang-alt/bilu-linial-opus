/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecA.Transfer

/-!
# Relative transfer (nodes `A-HGRR`, `A-TRANSR`)

`A-TRANS` (`CapPoint.trans`) bounds the retained grades `≥ 2` by `2e² M_E (dL⁴)²`, with `M_E` a
moment bound of the endpoint majorant: an absolute error. The whitening step (`A-WHITEN`, source
l.413–424, AUDIT-A §2.11) needs an error relative to `E_H w`, `C (p⁴/d)(E_H w + ϑ)`, which no
choice of `M_E` gives (`M_E ≥ ‖w‖_n` for all `n ≤ p/2`). The fix is AUDIT-C's T.TRC device: T.IL
(`wavg_mul_le_interp`) on every retained term.

* `A-HGRR` (`CapPoint.hgr_rel`): if `|R_j| ≤ X Π_i λ_i^{2j_i}` on the actual support for every
  retained `j` of grade `≥ 1`, with `X ≥ 0`, `E X ≤ m`, `ϑ ≤ m`, `E X² ≤ B²`, `E λ_iⁿ ≤ Lⁿ`
  (`2n ≤ p`), `16 K k ≤ p`, `dL² ≥ 2`, `dL⁴ ≤ 1/2`, then
  `Σ_{1 ≤ |j|_g ≤ k} |E R_j| ≤ 2e² (m ϑ^{-1/K} B^{1/K}) (dL⁴)`.
  Proof: T.IL with exponent `K` on each `j` (`E Y^{2K} ≤ Π L^{4K j_i}` by `A-HOLD`, moment order
  `4K Σ j_i ≤ 8Kk ≤ p/2`), then `A-CNT` grade by grade (`T = 1/(dL⁴)`) and the geometric sum.
* `A-TRANSR` (`CapPoint.trans_rel`): the hypotheses of `A-TRANS`, with the endpoint majorant
  required for all grades `≥ 1` and only `E X ≤ m`, `E X² ≤ B²` on it:
  `|E_{ν_K}(𝖦F - 𝖱F)/F_H| ≤ 2e² m ϑ^{-1/K} B^{1/K} (dL⁴) + M e^{-p}/d`.
  Proof: as `A-TRANS` (grade `0` is `𝖱F`, `A-RET`, `A-REM`), with `A-HGRR` for all grades `≥ 1`.

Checks: `N = ∅` (`retIdx k = {0}`): both sums are empty and `A-TRANSR` reduces to `A-REM`.
With `m = ϑ = B` and `K = 1` the factor `m ϑ^{-1/K} B^{1/K}` is `B` (absolute form, used by
`A-C1a`); with `m = E w + ϑ`, `ϑ = d^{-10}`, `K ≍ log d` it is `≤ C (E w + ϑ)` (`A-WHITEN`).
-/

@[expose] public section

universe u

namespace BiluLinial.Tight

open Matrix Finset

namespace CapPoint

variable {d p : ℕ} (cp : CapPoint.{u} d p)

/-- `A-HGRR`: relative form of `A-HGR` for all retained grades `≥ 1`: T.IL with one exponent
`K` (`16 K k ≤ p`) on every multi-index, then A-CNT grade by grade. -/
theorem hgr_rel (hR : RegA d p) {v : cp.V} (k K : ℕ) (hK : 1 ≤ K) (hKk : 16 * K * k ≤ p)
    (R : (cp.N v → ℕ) → Config cp.V → ℝ) (X : Config cp.V → ℝ)
    (lam : cp.N v → Config cp.V → ℝ) (hX0 : ∀ σ, 0 ≤ X σ) (hl0 : ∀ i σ, 0 ≤ lam i σ)
    {m θ B L : ℝ} (hθ : 0 < θ) (hθm : θ ≤ m) (hB : 0 ≤ B) (hL : 0 < L)
    (hXm : cp.E X ≤ m) (hX2 : cp.E (fun σ => X σ ^ 2) ≤ B ^ 2)
    (hmoml : ∀ i, ∀ n : ℕ, 1 ≤ n → 2 * n ≤ p → cp.E (fun σ => lam i σ ^ n) ≤ L ^ n)
    (hRb : ∀ j ∈ (retIdx k : Finset (cp.N v → ℕ)), 1 ≤ grade j → ∀ σ,
      0 < wt cp.G p (aOf d p) cp.yp cp.ym σ cp.S → |R j σ| ≤ X σ * ∏ i, lam i σ ^ (2 * j i))
    (hdL : 2 ≤ (d : ℝ) * L ^ 2) (hdL4 : (d : ℝ) * L ^ 4 ≤ 1 / 2) :
    ∑ j ∈ (retIdx k : Finset (cp.N v → ℕ)).filter (fun j => 1 ≤ grade j), |cp.E (R j)| ≤
      2 * Real.exp 2 * (m * θ ^ (-(1 / (K : ℝ))) * B ^ (1 / (K : ℝ))) * ((d : ℝ) * L ^ 4) := by
  have hd := hR.d_pos
  have hw : ∀ σ, 0 ≤ wt cp.G p (aOf d p) cp.yp cp.ym σ cp.S := fun σ => wt_nonneg cp.G σ
  have hZ := cp.Zw_pos hR
  set C₁ := m * θ ^ (-(1 / (K : ℝ))) * B ^ (1 / (K : ℝ)) with hC₁
  have hC₁0 : 0 ≤ C₁ := by
    have hm0 : 0 ≤ m := hθ.le.trans hθm
    positivity
  -- one multi-index (T.IL)
  have hj : ∀ j ∈ (retIdx k : Finset (cp.N v → ℕ)), 1 ≤ grade j →
      |cp.E (R j)| ≤ C₁ * ∏ i, (L ^ 2) ^ j i := by
    intro j hj hg1
    obtain ⟨hadm, hg⟩ := mem_retIdx.1 hj
    have hsum : ∑ i, j i ≤ 2 * k := (SecA.sum_le_two_mul_grade' hadm).trans (by omega)
    have hpos : 1 ≤ ∑ i, j i := by
      have : grade j ≤ ∑ i, j i := Finset.sum_le_sum fun i _ => Nat.sub_le _ _
      omega
    have h1 : |cp.E (R j)| ≤ cp.E (fun σ => X σ * ∏ i, lam i σ ^ (2 * j i)) :=
      SecA.abs_wavg_le_of_supp hw fun σ hσ => hRb j hj hg1 σ hσ
    have hY2k : cp.E (fun σ => (∏ i, lam i σ ^ (2 * j i)) ^ (2 * K)) ≤
        (∏ i, L ^ (2 * j i)) ^ (2 * K) := by
      have e1 : (fun σ => (∏ i, lam i σ ^ (2 * j i)) ^ (2 * K)) =
          fun σ => ∏ i, lam i σ ^ (4 * K * j i) := by
        funext σ
        rw [← Finset.prod_pow]
        exact Finset.prod_congr rfl fun i _ => by rw [← pow_mul]; ring_nf
      have e2 : (∏ i, L ^ (2 * j i)) ^ (2 * K) = ∏ i, L ^ (4 * K * j i) := by
        rw [← Finset.prod_pow]
        exact Finset.prod_congr rfl fun i _ => by rw [← pow_mul]; ring_nf
      rw [e1, e2]
      have hn : ∑ i, 4 * K * j i = 4 * K * ∑ i, j i := by rw [Finset.mul_sum]
      have hn1 : 1 ≤ 4 * K * ∑ i, j i := by
        have := Nat.mul_le_mul (Nat.mul_le_mul_left 4 hK) hpos
        simp only [mul_one] at this
        omega
      have hn2 : 2 * (4 * K * ∑ i, j i) ≤ p := by
        have := Nat.mul_le_mul_left (8 * K) hsum
        nlinarith
      exact SecA.wavg_prod_pow_le hw lam hl0 (fun i => 4 * K * j i) _ hn hn1 (fun _ => L)
        (fun _ => hL) (fun i _ => hmoml i _ hn1 hn2)
    have h2 := wavg_mul_le_interp hw hZ hX0 (fun σ => Finset.prod_nonneg fun i _ =>
      pow_nonneg (hl0 i σ) _) hK hθ hθm hB (Finset.prod_nonneg fun i _ => (pow_pos hL _).le)
      hXm hX2 hY2k
    refine h1.trans (h2.trans (le_of_eq ?_))
    rw [hC₁]
    congr 1
    exact Finset.prod_congr rfl fun i _ => by rw [pow_mul]
  -- grade by grade
  have hmaps : ∀ j ∈ (retIdx k : Finset (cp.N v → ℕ)).filter (fun j => 1 ≤ grade j),
      grade j ∈ Finset.Ico 1 (k + 1) := by
    intro j hj
    obtain ⟨hj1, hj2⟩ := Finset.mem_filter.1 hj
    have := (mem_retIdx.1 hj1).2
    rw [Finset.mem_Ico]
    omega
  have hT0 : (0 : ℝ) < 1 / ((d : ℝ) * L ^ 4) := by positivity
  have hxT : L ^ 2 * (1 / ((d : ℝ) * L ^ 4)) ≤ 1 / 2 := by
    have e : L ^ 2 * (1 / ((d : ℝ) * L ^ 4)) = 1 / ((d : ℝ) * L ^ 2) := by
      field_simp
    rw [e, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hexp2 : 2 * (L ^ 2) ^ 2 * (1 / ((d : ℝ) * L ^ 4)) * d = 2 := by
    field_simp
  have hgrade : ∀ g ∈ Finset.Ico 1 (k + 1),
      ∑ j ∈ (retIdx k : Finset (cp.N v → ℕ)).filter (fun j => 1 ≤ grade j) with grade j = g,
        C₁ * ∏ i, (L ^ 2) ^ j i ≤ C₁ * (((d : ℝ) * L ^ 4) ^ g * Real.exp 2) := by
    intro g hg
    have hg1 : 1 ≤ g := by rw [Finset.mem_Ico] at hg; omega
    have hsub : ((retIdx k : Finset (cp.N v → ℕ)).filter (fun j => 1 ≤ grade j)).filter
        (fun j => grade j = g) ⊆ topIdx (g - 1) := by
      intro j hj
      obtain ⟨hj1, hj2⟩ := Finset.mem_filter.1 hj
      obtain ⟨hj3, -⟩ := Finset.mem_filter.1 hj1
      exact mem_topIdx.2 ⟨(mem_retIdx.1 hj3).1, by omega⟩
    have hcnt := SecA.sum_topIdx_le_exp (ι := cp.N v) (g - 1) (pow_pos hL 2) hT0 hxT
      (cp.card_N_le v)
    rw [one_div_one_div, Nat.sub_add_cancel hg1, hexp2] at hcnt
    calc _ ≤ ∑ j ∈ (topIdx (g - 1) : Finset (cp.N v → ℕ)), C₁ * ∏ i, (L ^ 2) ^ j i :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun j _ _ =>
            mul_nonneg hC₁0 (Finset.prod_nonneg fun i _ => by positivity)
      _ = C₁ * ∑ j ∈ (topIdx (g - 1) : Finset (cp.N v → ℕ)), ∏ i, (L ^ 2) ^ j i := by
          rw [Finset.mul_sum]
      _ ≤ C₁ * (((d : ℝ) * L ^ 4) ^ g * Real.exp 2) := mul_le_mul_of_nonneg_left hcnt hC₁0
  have hr0 : (0 : ℝ) ≤ (d : ℝ) * L ^ 4 := by positivity
  have hgeom := geom_sum_Ico_le_of_lt_one (m := 1) (n := k + 1) hr0 (by linarith)
  have h2r : ((d : ℝ) * L ^ 4) ^ 1 / (1 - (d : ℝ) * L ^ 4) ≤ 2 * ((d : ℝ) * L ^ 4) := by
    rw [pow_one, div_le_iff₀ (by linarith)]
    nlinarith
  calc ∑ j ∈ (retIdx k : Finset (cp.N v → ℕ)).filter (fun j => 1 ≤ grade j), |cp.E (R j)|
      ≤ ∑ j ∈ (retIdx k : Finset (cp.N v → ℕ)).filter (fun j => 1 ≤ grade j),
          C₁ * ∏ i, (L ^ 2) ^ j i :=
        Finset.sum_le_sum fun j hjf =>
          hj j (Finset.mem_filter.1 hjf).1 (Finset.mem_filter.1 hjf).2
    _ = ∑ g ∈ Finset.Ico 1 (k + 1),
          ∑ j ∈ (retIdx k : Finset (cp.N v → ℕ)).filter (fun j => 1 ≤ grade j) with grade j = g,
            C₁ * ∏ i, (L ^ 2) ^ j i := (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ ≤ ∑ g ∈ Finset.Ico 1 (k + 1), C₁ * (((d : ℝ) * L ^ 4) ^ g * Real.exp 2) :=
        Finset.sum_le_sum hgrade
    _ = C₁ * Real.exp 2 * ∑ g ∈ Finset.Ico 1 (k + 1), ((d : ℝ) * L ^ 4) ^ g := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun g _ => by ring
    _ ≤ C₁ * Real.exp 2 * (2 * ((d : ℝ) * L ^ 4)) :=
        mul_le_mul_of_nonneg_left (hgeom.trans h2r) (by positivity)
    _ = 2 * Real.exp 2 * C₁ * ((d : ℝ) * L ^ 4) := by ring

/-- `A-TRANSR`: relative form of `A-TRANS`. Same family `F` and sup majorant as `A-TRANS`; the
endpoint majorant `X Φ(ξ) Π λ_i^{2j_i}` holds for all retained grades `≥ 1`, and only `E X ≤ m`,
`E X² ≤ B²` are used (T.IL with exponent `K`, `θ ≤ m`):
`|E_{ν_K}(𝖦F - 𝖱F)/F_H| ≤ 2e² m θ^{-1/K} B^{1/K} (d L⁴) + M e^{-p}/d`. -/
theorem trans_rel (hR : RegA d p) {v : cp.V} (hv : v ∈ cp.S)
    (F : Config cp.V → (cp.N v → ℝ) → ℝ) (hFc : ∀ σ σ', AgreeOff v σ σ' → F σ = F σ')
    (m : Config cp.V → ℝ) (hm0 : ∀ σ, 0 ≤ m σ) {M : ℝ} (hM : 0 < M)
    (hmom : ∀ n : ℕ, 1 ≤ n → 2 * n ≤ p → cp.coreE v (fun σ => m σ ^ n) ≤ M ^ n)
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
  have hrem := cp.trans_rem hR hv F m hm0 hM hmom hsm hder
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

end CapPoint

end BiluLinial.Tight
