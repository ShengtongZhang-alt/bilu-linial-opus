/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecC.RowG3Pt

/-!
# Row comparison, grades at least three (node CR-G3 of `docs/tight/BP_SECC.md`)

The retained multi-indices of grade `3 ≤ |j|_g ≤ k_*`. See `BiluLinial.Tight.SecC.RowGrades` for
the parent CR-GR and the orders-of-magnitude checks. Helpers: `BiluLinial.Tight.SecC.RowG3Pt`.
-/

@[expose] public section

namespace BiluLinial.Tight

namespace SecC

universe u

open Matrix

/-- **CR-G3** (grades `3 ≤ |j|_g ≤ k_*`, unmarked).

**Proof.** At a supported signing apply A-MAJ (`SecA.pderivList_clipObs_le_of_interior`) to the
two clipped terms of `rowNum` (`rowNum_eq_clipObs`) at the interior point `ξ`, with `m_α = α`,
`m_β = β`, the weights `λ_i = lamR` (`branch_majorant`) and prefactor scales `c α² Λ`,
`Λ = Σ_N λ_k²` (`quadMaj_prod_interior`): `|∂^{2j}F/Φ| ≤ 2pΛ Π_i (25 p² λ_i²)^{j_i}`
(`rowNum_endpoint_le`). With `25p²λ_i² ≤ (26p²/d) Z` (`lam_sq_le`) and `Λ ≤ 2Z` this is
`≤ 4pZ Π_i ((26p²/d) Z)^{j_i}` (`rowNum_retained_pointwise`). A-CNT per grade
(`sum_ret3_prod_le`) gives `4p e² Σ_{g ≥ 2} (676p⁴/d)^{g+1} Z^{2(g+2)}` (`Z ≥ 1`), and the
truncation `trunc_moment` with `X = 1` (`Z_moment_le`, `two_pow_kIL`) gives
`E Z^{2(g+2)} ≤ 2 · 1024^{2(g+2)}`. With `q = 676·1024² p⁴/d ≤ 1/2`, `Σ_{g ≥ 2} q^{g+1} ≤ 2q³`,
so the sum is `≤ 16 · 1024² (676·1024²)³ e² p¹³/d³ ≤ a² C p¹³/d²` (`d a² ≥ 1/4`). -/
theorem row_grade3_le : ∃ C : ℝ, 0 < C ∧ Eventually fun _ _ d p _ =>
    ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
      (S : Finset V) (lam : ℝ) (yp ym : V → ℝ) (v : V), CapCtx G d p S lam →
      InCube (lam * sOf d p) yp → InCube (lam * sOf d p) ym → v ∈ S →
        |∑ j ∈ (retIdx (kStar d p) : Finset (nbhd G S v → ℕ)).filter (fun j => 3 ≤ grade j),
            ecoefM j * rowRet G d p yp ym S v j| ≤
          aOf d p ^ 2 * (C * ((p : ℝ) ^ 13 / (d : ℝ) ^ 2)) := by
  refine ⟨64 * (1024 ^ 2 * (676 * 1024 ^ 2) ^ 3 * Real.exp 2), by positivity,
    ((eventually_regime 1).and eventually_trc).mono ?_⟩
  rintro c₀ κ₀ d p h ⟨⟨hR, -, -⟩, hreg⟩ V _ _ G _ S lam yp ym v hC hyp hym hv
  classical
  have hdR := hR.ten_pow_six_le_d
  have hd0 : (0 : ℝ) < d := lt_of_lt_of_le (by norm_num) hdR
  have hdne : (d : ℝ) ≠ 0 := hd0.ne'
  have hd1 : (1 : ℝ) ≤ d := le_trans (by norm_num) hdR
  have hd5 : 5 ≤ d := le_trans (by norm_num) hR.ten_pow_six_le_nat
  have hp6 := hR.hp
  have hp1n : 1 ≤ p := le_trans (by norm_num) hp6
  have hkIL := one_le_kIL (by omega : 3 ≤ d)
  have hθ : 0 < vth d := by unfold vth; positivity
  have hv1 : vth d ≤ 1 := by
    unfold vth
    rw [div_le_one (by positivity)]
    exact one_le_pow₀ hd1
  have ha2 := (TRegime.d_aOf_sq hR).1
  have hRHS0 : 0 ≤ aOf d p ^ 2 * (64 * (1024 ^ 2 * (676 * 1024 ^ 2) ^ 3 * Real.exp 2) *
      ((p : ℝ) ^ 13 / (d : ℝ) ^ 2)) := by positivity
  rcases isEmpty_or_nonempty (nbhd G S v) with hN | hN
  · have hE : (retIdx (kStar d p) : Finset (nbhd G S v → ℕ)).filter (fun j => 3 ≤ grade j) =
        ∅ := by
      ext j
      simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
      intro _ h3
      have : grade j = 0 := by rw [grade, Finset.univ_eq_empty, Finset.sum_empty]
      omega
    rw [hE, Finset.sum_empty, abs_zero]
    exact hRHS0
  set k := kStar d p with hk
  set Z : Config V → ℝ := fun σ => ZR G (aOf d p) yp ym σ S v with hZdef
  set xp : Config V → ℝ := fun σ => 26 * (p : ℝ) ^ 2 / d * Z σ with hxp
  have hZ1 : ∀ σ, 1 ≤ Z σ := fun σ => by
    simp only [hZdef, ZR]
    nlinarith [sq_nonneg (Finset.univ.sup' Finset.univ_nonempty (rhoR G (aOf d p) yp ym σ S v))]
  have hp2 : (1 : ℝ) ≤ (p : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast hp1n)
  have hdx : ∀ σ, 2 ≤ (d : ℝ) * xp σ := fun σ => by
    simp only [hxp]
    rw [show (d : ℝ) * (26 * (p : ℝ) ^ 2 / d * Z σ) = 26 * (p : ℝ) ^ 2 * Z σ by field_simp]
    nlinarith [mul_le_mul hp2 (hZ1 σ) zero_le_one (by positivity)]
  have hcard : (Fintype.card (nbhd G S v) : ℝ) ≤ d := by exact_mod_cast card_nbhd_le G hC.deg S v
  -- one multi-index at a time (pointwise A-MAJ bound)
  have hLj : ∀ j ∈ (retIdx k : Finset (nbhd G S v → ℕ)).filter (fun j => 3 ≤ grade j),
      |ecoefM j * rowRet G d p yp ym S v j| ≤
        lawE G p (aOf d p) yp ym S (fun σ => 4 * p * Z σ * ∏ i, xp σ ^ j i) := by
    intro j hj
    obtain ⟨hjr, -⟩ := Finset.mem_filter.1 hj
    obtain ⟨hadm, hgr⟩ := mem_retIdx.1 hjr
    have hsum : ∑ i, j i ≤ 2 * k := (sum_le_two_mul_grade hadm).trans (by omega)
    have hjp : 2 * ∑ i, j i + 3 ≤ p := by omega
    have hc : |ecoefM j| ≤ 1 := by
      rw [ecoefM, Finset.abs_prod]
      exact Finset.prod_le_one₀ (fun i _ => abs_nonneg _) fun i _ => abs_ecoef_le_one _
    rw [abs_mul, rowRet]
    refine (mul_le_of_le_one_left (abs_nonneg _) hc).trans (abs_lawE_le G fun σ hσ => ?_)
    exact rowNum_retained_pointwise G hR hC hyp hym hv hσ j hjp
  -- the grade expansion (`Z ≥ 1` absorbs the prefactor `Z`)
  have hgr : ∀ σ, wt G p (aOf d p) yp ym σ S ≠ 0 →
      4 * p * Z σ * ∑ j ∈ (retIdx k : Finset (nbhd G S v → ℕ)).filter (fun j => 3 ≤ grade j),
          ∏ i, xp σ ^ j i ≤
        ∑ g ∈ Finset.range (k - 2), 4 * p * Real.exp 2 * (676 * (p : ℝ) ^ 4 / d) ^ (g + 3) *
          Z σ ^ (2 * (g + 4)) := fun σ _ => by
    have h1 := sum_ret3_prod_le k hd1 hcard (hdx σ)
    have hZ0 : 0 ≤ Z σ := zero_le_one.trans (hZ1 σ)
    have hpz : 0 ≤ 4 * (p : ℝ) * Z σ := by positivity
    refine (mul_le_mul_of_nonneg_left h1 hpz).trans ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun g _ => ?_
    have e : (d : ℝ) * xp σ ^ 2 = 676 * (p : ℝ) ^ 4 / d * Z σ ^ 2 := by
      simp only [hxp]
      field_simp
      ring
    rw [e, mul_pow, ← pow_mul]
    have hZp : Z σ * Z σ ^ (2 * (g + 3)) ≤ Z σ ^ (2 * (g + 4)) := by
      rw [← pow_succ']
      exact pow_le_pow_right₀ (hZ1 σ) (by omega)
    have hc0 : 0 ≤ 4 * (p : ℝ) * Real.exp 2 * (676 * (p : ℝ) ^ 4 / d) ^ (g + 3) := by positivity
    calc _ = 4 * (p : ℝ) * Real.exp 2 * (676 * (p : ℝ) ^ 4 / d) ^ (g + 3) *
          (Z σ * Z σ ^ (2 * (g + 3))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hZp hc0
  -- `E 1 ≤ 1`
  have hE1 : lawE G p (aOf d p) yp ym S (fun _ => (1 : ℝ)) ≤ 1 := by
    rcases (Zw_nonneg G (p := p) (a := aOf d p) (yp := yp) (ym := ym) (S := S)).lt_or_eq with
      h0 | h0
    · rw [lawE_const_one G h0]
    · unfold lawE
      rw [← h0, div_zero]
      norm_num
  -- per-grade truncation of the moments of `Z`
  have htr : ∀ g ∈ Finset.range (k - 2),
      lawE G p (aOf d p) yp ym S (fun σ => Z σ ^ (2 * (g + 4))) ≤ 1024 ^ (2 * (g + 4)) * 2 := by
    intro g hg
    have hgk : g + 3 ≤ k := by have := Finset.mem_range.1 hg; omega
    have h := trunc_moment G (p := p) (a := aOf d p) (yp := yp) (ym := ym) (S := S)
      (X := fun _ => (1 : ℝ)) (fun _ _ => zero_le_one)
      (fun σ _ => (zero_le_one).trans (hZ1 σ)) (n := g + 4) (m := 2 * kIL d)
      (by norm_num : (0 : ℝ) < 1024) hθ.le ?_
    · simp only [one_mul] at h
      refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
      linarith
    have hZm := Z_moment_le G hR hC hyp hym hv (n := 2 * (2 * (g + 4) + 2 * kIL d)) (by omega)
    have hX2 : lawE G p (aOf d p) yp ym S (fun _ => (1 : ℝ) ^ 2) ≤ ((d : ℝ) ^ 30) ^ 2 := by
      simp only [one_pow]
      refine hE1.trans ?_
      have : (1 : ℝ) ≤ (d : ℝ) ^ 30 := one_le_pow₀ hd1
      nlinarith
    have h2 := two_pow_kIL hd5
    calc _ ≤ ((d : ℝ) ^ 30) ^ 2 * (5 * d * 512 ^ (2 * (2 * (g + 4) + 2 * kIL d))) :=
          mul_le_mul hX2 hZm
            (lawE_nonneg G fun σ hσ => pow_nonneg ((zero_le_one).trans (hZ1 σ)) _)
            (by positivity)
      _ ≤ (1024 ^ (2 * kIL d) * 1024 ^ (2 * (g + 4)) * vth d) ^ 2 := by
          set A := 2 * (g + 4) + 2 * kIL d with hA
          have hLA : (1024 : ℝ) ^ (2 * kIL d) * 1024 ^ (2 * (g + 4)) = 1024 ^ A := by
            rw [← pow_add, add_comm]
          have h2A : (2 : ℝ) ^ (4 * kIL d) ≤ 2 ^ (2 * A) :=
            pow_le_pow_right₀ (by norm_num) (by omega)
          have h5 := h2.trans h2A
          have h1024 : (512 : ℝ) ^ (2 * A) * 2 ^ (2 * A) = 1024 ^ (2 * A) := by
            rw [← mul_pow]; norm_num
          have hP : 0 ≤ (512 : ℝ) ^ (2 * A) := by positivity
          have hRHS : (1024 ^ (2 * kIL d) * 1024 ^ (2 * (g + 4)) * vth d) ^ 2 =
              512 ^ (2 * A) * 2 ^ (2 * A) / (d : ℝ) ^ 20 := by
            rw [hLA, h1024]
            unfold vth
            field_simp
            ring
          rw [hRHS, le_div_iff₀ (pow_pos hd0 20)]
          calc ((d : ℝ) ^ 30) ^ 2 * (5 * d * 512 ^ (2 * A)) * (d : ℝ) ^ 20
              = 512 ^ (2 * A) * (5 * (d : ℝ) ^ 81) := by ring
            _ ≤ 512 ^ (2 * A) * 2 ^ (2 * A) := mul_le_mul_of_nonneg_left h5 hP
  -- the geometric sum over `g ≥ 2`
  have hq : 676 * 1024 ^ 2 * (p : ℝ) ^ 4 / d ≤ 1 / 2 := by
    have h8 := TRegime.p8_le hR
    have hp4 : (10 : ℝ) ^ 24 ≤ (p : ℝ) ^ 4 := by
      have : (10 : ℝ) ^ 6 ≤ p := by exact_mod_cast hp6
      calc (10 : ℝ) ^ 24 = ((10 : ℝ) ^ 6) ^ 4 := by norm_num
        _ ≤ (p : ℝ) ^ 4 := pow_le_pow_left₀ (by norm_num) this 4
    rw [div_le_iff₀ hd0]
    nlinarith [mul_le_mul_of_nonneg_right hp4 (by positivity : (0 : ℝ) ≤ (p : ℝ) ^ 4)]
  obtain ⟨q, hqdef⟩ : ∃ q : ℝ, q = 676 * 1024 ^ 2 * (p : ℝ) ^ 4 / d := ⟨_, rfl⟩
  rw [← hqdef] at hq
  have hq0 : 0 ≤ q := by rw [hqdef]; positivity
  have hgeom : ∑ g ∈ Finset.range (k - 2), q ^ (g + 3) ≤ 2 * q ^ 3 := by
    calc ∑ g ∈ Finset.range (k - 2), q ^ (g + 3) = q ^ 3 * ∑ g ∈ Finset.range (k - 2), q ^ g := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun g _ => by ring
      _ ≤ q ^ 3 * ∑ g ∈ Finset.range (k - 2), (1 / 2 : ℝ) ^ g := by gcongr
      _ ≤ q ^ 3 * 2 := mul_le_mul_of_nonneg_left (sum_geometric_two_le _) (by positivity)
      _ = 2 * q ^ 3 := by ring
  have hpow : ∀ g : ℕ, (676 * (p : ℝ) ^ 4 / d) ^ (g + 3) * 1024 ^ (2 * (g + 4)) =
      1024 ^ 2 * q ^ (g + 3) := by
    intro g
    rw [hqdef, show 2 * (g + 4) = 2 + 2 * (g + 3) by ring, pow_add (1024 : ℝ) 2, pow_mul,
      show (676 * 1024 ^ 2 * (p : ℝ) ^ 4 / d) = (676 * (p : ℝ) ^ 4 / d) * 1024 ^ 2 by ring, mul_pow]
    ring
  -- assemble
  calc _ ≤ ∑ j ∈ (retIdx k : Finset (nbhd G S v → ℕ)).filter (fun j => 3 ≤ grade j),
        |ecoefM j * rowRet G d p yp ym S v j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ (retIdx k : Finset (nbhd G S v → ℕ)).filter (fun j => 3 ≤ grade j),
          lawE G p (aOf d p) yp ym S (fun σ => 4 * p * Z σ * ∏ i, xp σ ^ j i) :=
        Finset.sum_le_sum hLj
    _ = lawE G p (aOf d p) yp ym S (fun σ => 4 * p * Z σ *
          ∑ j ∈ (retIdx k : Finset (nbhd G S v → ℕ)).filter (fun j => 3 ≤ grade j),
            ∏ i, xp σ ^ j i) := by
        rw [← lawE_sum]
        exact congrArg _ (funext fun σ => (Finset.mul_sum _ _ _).symm)
    _ ≤ lawE G p (aOf d p) yp ym S (fun σ => ∑ g ∈ Finset.range (k - 2),
          4 * p * Real.exp 2 * (676 * (p : ℝ) ^ 4 / d) ^ (g + 3) * Z σ ^ (2 * (g + 4))) :=
        lawE_mono G hgr
    _ = ∑ g ∈ Finset.range (k - 2), 4 * p * Real.exp 2 * (676 * (p : ℝ) ^ 4 / d) ^ (g + 3) *
          lawE G p (aOf d p) yp ym S (fun σ => Z σ ^ (2 * (g + 4))) := by
        rw [lawE_sum]
        exact Finset.sum_congr rfl fun g _ => lawE_const_mul G _ _
    _ ≤ ∑ g ∈ Finset.range (k - 2), 4 * p * Real.exp 2 * (676 * (p : ℝ) ^ 4 / d) ^ (g + 3) *
          (1024 ^ (2 * (g + 4)) * 2) := by
        refine Finset.sum_le_sum fun g hg => mul_le_mul_of_nonneg_left (htr g hg) ?_
        positivity
    _ = 8 * p * Real.exp 2 * 1024 ^ 2 * ∑ g ∈ Finset.range (k - 2), q ^ (g + 3) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun g _ => ?_
        linear_combination (8 * (p : ℝ) * Real.exp 2) * hpow g
    _ ≤ 8 * p * Real.exp 2 * 1024 ^ 2 * (2 * q ^ 3) :=
        mul_le_mul_of_nonneg_left hgeom (by positivity)
    _ ≤ aOf d p ^ 2 * (64 * (1024 ^ 2 * (676 * 1024 ^ 2) ^ 3 * Real.exp 2) *
          ((p : ℝ) ^ 13 / (d : ℝ) ^ 2)) := by
        rw [hqdef]
        have hM : 0 ≤ 1024 ^ 2 * (676 * 1024 ^ 2) ^ 3 * Real.exp 2 * (p : ℝ) ^ 13 /
            (d : ℝ) ^ 3 := by
          positivity
        have e1 : 8 * (p : ℝ) * Real.exp 2 * 1024 ^ 2 *
            (2 * (676 * 1024 ^ 2 * (p : ℝ) ^ 4 / d) ^ 3) =
            16 * (1024 ^ 2 * (676 * 1024 ^ 2) ^ 3 * Real.exp 2 * (p : ℝ) ^ 13 / (d : ℝ) ^ 3) := by
          field_simp
          ring
        have e2 : aOf d p ^ 2 * (64 * (1024 ^ 2 * (676 * 1024 ^ 2) ^ 3 * Real.exp 2) *
            ((p : ℝ) ^ 13 / (d : ℝ) ^ 2)) = 64 * ((d : ℝ) * aOf d p ^ 2) *
              (1024 ^ 2 * (676 * 1024 ^ 2) ^ 3 * Real.exp 2 * (p : ℝ) ^ 13 / (d : ℝ) ^ 3) := by
          field_simp
        rw [e1, e2]
        nlinarith [mul_le_mul_of_nonneg_right ha2 hM]

end SecC

end BiluLinial.Tight
