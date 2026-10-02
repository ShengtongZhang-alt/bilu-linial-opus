/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecC.MarkEnv
public import BiluLinial.Tight.SecC.RowX5
public import BiluLinial.Tight.SecC.RowRem
public import BiluLinial.Tight.SecC.RowGrades

/-!
# Lemma "Contact row comparison" (CR1), (CR3) and the GCI-free (CR3′)

Source lines 1078–1190; AUDIT-C §4.2 (restatement, gap G4); `docs/tight/DR1_CHECK.md` §3 (CR3′).
Nodes of `docs/tight/BP_SECC.md`:

* `row_comparison_split` (**CR3**): envelopes `ϑ ≤ λ_r ≤ ρ_r ≤ δ_c`, `λ_r ≤ λ_c ≤ δ_c` with
  `S₊/d ≤ λ_r`, `S₋/d ≤ ρ_r`, `d^{-2} E[(G^±_vv)²‖G^±[N,N]‖_F²] ≤ λ_c, δ_c` give
  `|𝓡 - E_{ν_K}𝖦F/(a²F_H)| ≤ C{p⁵√(λ_rρ_r) + p⁴√(λ_cδ_c) + p¹³/d²} + e^{-3p}`.
* `row_comparison_diff` (**CR3′**, GCI-free): the minus row envelope is replaced by the
  difference envelope `d^{-1} Σ_N E(G⁺_vj - G⁻_vj)² ≤ ρ_Δ`, the plain minus row by `δ_c`:
  `|𝓡 - E_{ν_K}𝖦F/(a²F_H)| ≤ C{p⁵√(λ_rρ_Δ) + p⁴√(λ_cδ_c) + p¹³/d²} + e^{-3p}`.
* `row_comparison` (**CR1**, proved from CR3 and MARKENV): `a²S₊ + E tr A² ≤ λ`,
  `a²S₋ + E tr B² ≤ δ` (the latter from (C2)), `ϑ ≤ λ ≤ δ` give
  `|𝓡 - E_{ν_K}𝖦F/(a²F_H)| ≤ C{p⁵√(λδ) + p¹³/d²} + e^{-3p}`.

The source's `e^{-cp}` is `e^{-3p}` (AUDIT-C §0.5); the source's upper bounds `δ_c ≤ 1` and the
contact hypothesis are not needed (gap G4).

**Sketch of CR3/CR3′.** Pointwise in the core, (E4) with `k = k_*` for `F = rowNum p A B`
(`C^{4k_*+4}`, `eventually_kStar`). Divided by `a² F_H` and averaged over `ν_K`:
* grade 0 is exactly `𝓡` (law identity `lawE_eq_coreE_rad`, `F = a²Φ𝓡_v` by `rowNum_eq`);
* grade 1 (`∂_i⁴`, `c₂ = 1/12`): `mark_grade_one` at sign endpoints, physical forms by
  `root_F1`, summed over `i, j ∈ N` with Cauchy–Schwarz (`a⁴|N| ≤ a²/2`, `Σ_{ij} a⁴ e_ij² ≤ Kc`),
  then Cauchy–Schwarz in the law and T.IL (`m = λ_r, λ_c ≥ ϑ`; unmarked `(1 + r_i)⁴ ≤ C D⁴`,
  `‖D⁴‖_{2k} ≤ C` by T.DSTAR and F2): `C(p⁵√(λ_r ρ) + p⁴√(λ_c δ_c))`, `ρ = ρ_r` (CR3, via
  `|Σ x(x-z)| ≤ Σ x² + |Σ xz|`) or `ρ_Δ` (CR3′, via `|Σ x(x-z)| ≤ √(Σx²)√(Σ(x-z)²)`);
* grade 2 (`∂_i⁶`, `∂_i⁴∂_k⁴`): `mark_grade_two_diag`, `mark_grade_two_mixed`, the same
  summation: `C (p⁹/d) √(λ_c δ_c) ≤ C p⁴ √(λ_c δ_c)` (`p⁵ ≤ d`);
* grades `3 ≤ g ≤ k_*`: unmarked bounds (E5 at endpoints, `T.HGR`) `p (Cp)^{4g} d^{1-g}`, a
  geometric sum `≤ C p¹³/d²` (`C p⁴/d ≤ 1/2`);
* remainder: `≤ e^{-3p}` (E5 sup bound, `T.CREM`, `insFH_ge`, `eventually_E6`, `a⁻² ≤ 4d`).

**Proofs from the sub-nodes** (`SecC/RowCompareParts.lean`). `row_comparison_core`: CR-REM,
CR-RET, CR-G0 and CR-GR give `𝓡 - 𝖦F/(a²F_H) = -Rem/(a²F_H) - a⁻² Σ_{j≠0} c_j rowRet j`, hence
`|𝓡 - 𝖦F/(a²F_H)| ≤ (C_G + 4C_R)(p⁵ X₅ + p⁴√(λ_cδ_c) + p¹³/d²)` (`a⁻² ≤ 4d`,
`p e^{-p} ≤ p/d² ≤ p¹³/d²` from `p ≥ 2 log d`). CR3 then uses CR-X5 (split form) with
`S₋/d ≤ ρ_r ≤ δ_c`; CR3′ uses CR-X5 (difference form).
-/

@[expose] public section

namespace BiluLinial.Tight

namespace SecC

universe u

section Helpers

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem coreE_sum_aux {p : ℕ} {a : ℝ} {yp ym : V → ℝ} {S : Finset V} {v : V}
    {ι : Type*} (s : Finset ι) (f : ι → Config V → ℝ) :
    coreE G p a yp ym S v (fun σ => ∑ l ∈ s, f l σ) = ∑ l ∈ s, coreE G p a yp ym S v (f l) := by
  unfold coreE
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm, Finset.sum_div]

end Helpers

/-- The common core of CR3 and CR3′: `|𝓡 - 𝖦F/(a²F_H)| ≤ C (p⁵ X₅ + p⁴ √(λ_c δ_c) + p¹³/d²)`
(CR-REM, CR-RET, CR-G0, CR-GR). -/
theorem row_comparison_core : ∃ C : ℝ, 0 < C ∧ Eventually fun _ _ d p _ =>
    ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
      (S : Finset V) (lam : ℝ) (yp ym : V → ℝ) (v : V), CapCtx G d p S lam →
      InCube (lam * sOf d p) yp → InCube (lam * sOf d p) ym → v ∈ S →
      ∀ lr lc dc : ℝ, vth d ≤ lr → lr ≤ lc → lc ≤ dc →
        incRowE G d p yp ym S v 1 yp / d ≤ lr → incRowE G d p yp ym S v (-1) ym / d ≤ dc →
        markE G d p yp ym S v 1 yp / (d : ℝ) ^ 2 ≤ lc →
        markE G d p yp ym S v (-1) ym / (d : ℝ) ^ 2 ≤ dc →
        |rowMean G d p yp ym S v - rowGauss G d p yp ym S v| ≤
          C * ((p : ℝ) ^ 5 * rowX5 G d p yp ym S v + (p : ℝ) ^ 4 * Real.sqrt (lc * dc) +
            (p : ℝ) ^ 13 / (d : ℝ) ^ 2) := by
  obtain ⟨CR, hCR, hRem⟩ := row_rem.{u}
  obtain ⟨CG, hCG, hGr⟩ := row_grades_le.{u}
  refine ⟨CG + 4 * CR, by positivity, (((hRem.and hGr).and row_ret.{u}).and
    ((eventually_regime 1).and (eventually_log_le 2))).mono ?_⟩
  rintro c₀ κ₀ d p h ⟨⟨⟨HR, HG⟩, HRet⟩, ⟨hR, -, -⟩, hlog⟩ V _ _ G _ S lam yp ym v hC hyp hym hv
    lr lc dc hvl hllc hlcd hS1 hS2 hM1 hM2
  classical
  have hyp0 : ∀ i, 0 ≤ yp i := fun i => (hyp i).1
  have hym0 : ∀ i, 0 ≤ ym i := fun i => (hym i).1
  have hFH := insFH_pos G hR hC hyp hym hv
  have ha := hR.aOf_pos
  have ha2 : 0 < aOf d p ^ 2 := pow_pos ha 2
  have hdR := hR.ten_pow_six_le_d
  have hd0 : (0 : ℝ) < d := lt_of_lt_of_le (by norm_num) hdR
  have hd1 : (1 : ℝ) ≤ d := le_trans (by norm_num) hdR
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (le_trans (by norm_num) hR.two_le_p : 1 ≤ p)
  obtain ⟨hda, -⟩ := TRegime.d_aOf_sq hR
  have hRemb := HR V G S lam yp ym v hC hyp hym hv
  have hGb := HG V G S lam yp ym v hC hyp hym hv lr lc dc hvl hllc hlcd hS1 hS2 hM1 hM2
  have hRet := HRet V G S lam yp ym v hC hyp hym hv
  set k := kStar d p with hk
  set FH := insFH G d p yp ym S v with hFHdef
  set Sg := ∑ j ∈ (retIdx k : Finset (nbhd G S v → ℕ)).erase 0,
    ecoefM j * rowRet G d p yp ym S v j with hSg
  set Rem := coreE G p (aOf d p) yp ym S v (fun σ =>
      gaussE (rowNum p (rootMat G (aOf d p) 1 yp σ S v) (rootMat G (aOf d p) (-1) ym σ S v)) -
      ∑ j ∈ (retIdx k : Finset (nbhd G S v → ℕ)), ecoefM j *
        radE (dEven (Finset.univ : Finset (nbhd G S v)).toList j
          (rowNum p (rootMat G (aOf d p) 1 yp σ S v) (rootMat G (aOf d p) (-1) ym σ S v))))
    with hRemdef
  set Γ := coreE G p (aOf d p) yp ym S v (fun σ =>
      gaussE (rowNum p (rootMat G (aOf d p) 1 yp σ S v) (rootMat G (aOf d p) (-1) ym σ S v)))
    with hΓ
  have h0mem : (0 : nbhd G S v → ℕ) ∈ (retIdx k : Finset (nbhd G S v → ℕ)) :=
    mem_retIdx.2 ⟨fun i => by simp, by simp [grade]⟩
  have hlin : Rem = Γ - FH * (aOf d p ^ 2 * rowMean G d p yp ym S v + Sg) := by
    rw [hRemdef, coreE_sub, coreE_sum_aux]
    congr 1
    have hterm : ∀ j ∈ (retIdx k : Finset (nbhd G S v → ℕ)),
        coreE G p (aOf d p) yp ym S v (fun σ => ecoefM j *
          radE (dEven (Finset.univ : Finset (nbhd G S v)).toList j
            (rowNum p (rootMat G (aOf d p) 1 yp σ S v) (rootMat G (aOf d p) (-1) ym σ S v)))) =
          FH * (ecoefM j * rowRet G d p yp ym S v j) := by
      intro j hj
      rw [coreE_const_mul]
      have := hRet j hj
      rw [div_eq_iff hFH.ne'] at this
      rw [this]
      ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← Finset.add_sum_erase _ _ h0mem,
      ecoefM_zero, one_mul, row_grade0 G hR hyp0 hym0 hv]
  have hkey : rowMean G d p yp ym S v - rowGauss G d p yp ym S v =
      -(Rem / (aOf d p ^ 2 * FH)) - Sg / aOf d p ^ 2 := by
    have hG : rowGauss G d p yp ym S v = Γ / (aOf d p ^ 2 * FH) := rfl
    have hΓ' : Γ = Rem + FH * (aOf d p ^ 2 * rowMean G d p yp ym S v + Sg) := by
      rw [hlin]; ring
    rw [hG, hΓ']
    field_simp
    ring
  -- the two error terms
  have hX0 : 0 ≤ rowX5 G d p yp ym S v := by
    unfold rowX5
    refine lawE_nonneg G fun σ _ => mul_nonneg ?_ (mul_nonneg (sq_nonneg _) (abs_nonneg _))
    unfold rowWt
    positivity
  have hsq0 : 0 ≤ Real.sqrt (lc * dc) := Real.sqrt_nonneg _
  have hT0 : 0 ≤ (p : ℝ) ^ 13 / (d : ℝ) ^ 2 := by positivity
  have hB0 : 0 ≤ (p : ℝ) ^ 5 * rowX5 G d p yp ym S v + (p : ℝ) ^ 4 * Real.sqrt (lc * dc) :=
    by positivity
  have hE1 : |Rem / (aOf d p ^ 2 * FH)| ≤ 4 * CR * ((p : ℝ) ^ 13 / (d : ℝ) ^ 2) := by
    rw [abs_div, abs_of_pos (mul_pos ha2 hFH), div_le_iff₀ (mul_pos ha2 hFH)]
    have hep : Real.exp (-(p : ℝ)) ≤ 1 / (d : ℝ) ^ 2 := by
      rw [Real.exp_neg, inv_eq_one_div]
      refine one_div_le_one_div_of_le (by positivity) ?_
      calc (d : ℝ) ^ 2 = Real.exp (2 * Real.log d) := by
            rw [show (2 : ℝ) * Real.log d = Real.log ((d : ℝ) ^ 2) by
              rw [Real.log_pow]; norm_num, Real.exp_log (by positivity)]
        _ ≤ Real.exp p := Real.exp_le_exp.mpr hlog
    have hp13 : (p : ℝ) ≤ (p : ℝ) ^ 13 := le_self_pow₀ hp1 (by norm_num)
    have h4 : 1 ≤ 4 * ((d : ℝ) * aOf d p ^ 2) := by linarith
    calc |Rem| ≤ CR * p * Real.exp (-(p : ℝ)) / d * FH := hRemb
      _ ≤ CR * p * (1 / (d : ℝ) ^ 2) / d * FH := by gcongr
      _ = CR * p / (d : ℝ) ^ 2 * (1 / d) * FH := by ring
      _ ≤ CR * (p : ℝ) ^ 13 / (d : ℝ) ^ 2 * (4 * aOf d p ^ 2) * FH := by
          gcongr
          rw [div_le_iff₀ hd0]
          linarith
      _ = 4 * CR * ((p : ℝ) ^ 13 / (d : ℝ) ^ 2) * (aOf d p ^ 2 * FH) := by ring
  have hE2 : |Sg / aOf d p ^ 2| ≤ CG * ((p : ℝ) ^ 5 * rowX5 G d p yp ym S v +
      (p : ℝ) ^ 4 * Real.sqrt (lc * dc) + (p : ℝ) ^ 13 / (d : ℝ) ^ 2) := by
    rw [abs_div, abs_of_pos ha2, div_le_iff₀ ha2]
    calc |Sg| ≤ _ := hGb
      _ = _ := by ring
  rw [hkey]
  calc |-(Rem / (aOf d p ^ 2 * FH)) - Sg / aOf d p ^ 2|
      ≤ |Rem / (aOf d p ^ 2 * FH)| + |Sg / aOf d p ^ 2| := by
        rw [sub_eq_add_neg, ← neg_add]
        rw [abs_neg]
        exact abs_add_le _ _
    _ ≤ 4 * CR * ((p : ℝ) ^ 13 / (d : ℝ) ^ 2) + CG * ((p : ℝ) ^ 5 * rowX5 G d p yp ym S v +
          (p : ℝ) ^ 4 * Real.sqrt (lc * dc) + (p : ℝ) ^ 13 / (d : ℝ) ^ 2) := add_le_add hE1 hE2
    _ ≤ (CG + 4 * CR) * ((p : ℝ) ^ 5 * rowX5 G d p yp ym S v +
          (p : ℝ) ^ 4 * Real.sqrt (lc * dc) + (p : ℝ) ^ 13 / (d : ℝ) ^ 2) := by
        nlinarith [mul_nonneg hCR.le hB0]

/-- **CR3** (source display (CR3), lines 1170–1190). -/
theorem row_comparison_split : ∃ C : ℝ, 0 < C ∧ Eventually fun _ _ d p _ =>
    ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
      (S : Finset V) (lam : ℝ) (yp ym : V → ℝ) (v : V), CapCtx G d p S lam →
      InCube (lam * sOf d p) yp → InCube (lam * sOf d p) ym → v ∈ S →
      ∀ lr rr lc dc : ℝ, vth d ≤ lr → lr ≤ rr → lr ≤ lc → lc ≤ dc → rr ≤ dc →
        incRowE G d p yp ym S v 1 yp / d ≤ lr → incRowE G d p yp ym S v (-1) ym / d ≤ rr →
        markE G d p yp ym S v 1 yp / (d : ℝ) ^ 2 ≤ lc →
        markE G d p yp ym S v (-1) ym / (d : ℝ) ^ 2 ≤ dc →
        |rowMean G d p yp ym S v - rowGauss G d p yp ym S v| ≤
          C * ((p : ℝ) ^ 5 * Real.sqrt (lr * rr) + (p : ℝ) ^ 4 * Real.sqrt (lc * dc) +
              (p : ℝ) ^ 13 / (d : ℝ) ^ 2) + Real.exp (-(3 * (p : ℝ))) := by
  obtain ⟨C₁, hC₁, hcore⟩ := row_comparison_core.{u}
  obtain ⟨C₅, hC₅, hX⟩ := row_x5_split.{u}
  refine ⟨C₁ * (C₅ + 1), by positivity, (hcore.and hX).mono ?_⟩
  rintro c₀ κ₀ d p h ⟨H1, H5⟩ V _ _ G _ S lam yp ym v hC hyp hym hv lr rr lc dc hvl hlrr hllc
    hlcd hrrd hS1 hS2 hM1 hM2
  have h1 := H1 V G S lam yp ym v hC hyp hym hv lr lc dc hvl hllc hlcd hS1 (hS2.trans hrrd) hM1
    hM2
  have h5 := H5 V G S lam yp ym v hC hyp hym hv lr rr hvl hlrr hS1 hS2
  have hs1 : 0 ≤ Real.sqrt (lr * rr) := Real.sqrt_nonneg _
  have hs2 : 0 ≤ Real.sqrt (lc * dc) := Real.sqrt_nonneg _
  have hT : 0 ≤ (p : ℝ) ^ 13 / (d : ℝ) ^ 2 := by positivity
  have hW : 0 ≤ C₁ * ((p : ℝ) ^ 5 * Real.sqrt (lr * rr) +
      C₅ * ((p : ℝ) ^ 4 * Real.sqrt (lc * dc) + (p : ℝ) ^ 13 / (d : ℝ) ^ 2)) := by positivity
  have e : C₁ * ((p : ℝ) ^ 5 * (C₅ * Real.sqrt (lr * rr)) + (p : ℝ) ^ 4 * Real.sqrt (lc * dc) +
        (p : ℝ) ^ 13 / (d : ℝ) ^ 2) + C₁ * ((p : ℝ) ^ 5 * Real.sqrt (lr * rr) +
        C₅ * ((p : ℝ) ^ 4 * Real.sqrt (lc * dc) + (p : ℝ) ^ 13 / (d : ℝ) ^ 2)) =
      C₁ * (C₅ + 1) * ((p : ℝ) ^ 5 * Real.sqrt (lr * rr) + (p : ℝ) ^ 4 * Real.sqrt (lc * dc) +
        (p : ℝ) ^ 13 / (d : ℝ) ^ 2) := by ring
  have h2 : C₁ * ((p : ℝ) ^ 5 * rowX5 G d p yp ym S v + (p : ℝ) ^ 4 * Real.sqrt (lc * dc) +
        (p : ℝ) ^ 13 / (d : ℝ) ^ 2) ≤
      C₁ * ((p : ℝ) ^ 5 * (C₅ * Real.sqrt (lr * rr)) + (p : ℝ) ^ 4 * Real.sqrt (lc * dc) +
        (p : ℝ) ^ 13 / (d : ℝ) ^ 2) := by gcongr
  have h3 := (Real.exp_pos (-(3 * (p : ℝ)))).le
  linarith

/-- **CR3′** (GCI-free row comparison, `docs/tight/DR1_CHECK.md` §3). -/
theorem row_comparison_diff : ∃ C : ℝ, 0 < C ∧ Eventually fun _ _ d p _ =>
    ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
      (S : Finset V) (lam : ℝ) (yp ym : V → ℝ) (v : V), CapCtx G d p S lam →
      InCube (lam * sOf d p) yp → InCube (lam * sOf d p) ym → v ∈ S →
      ∀ lr rd lc dc : ℝ, vth d ≤ lr → lr ≤ lc → lc ≤ dc → vth d ≤ rd →
        incRowE G d p yp ym S v 1 yp / d ≤ lr → incRowE G d p yp ym S v (-1) ym / d ≤ dc →
        diffRowE G d p yp ym S v / d ≤ rd →
        markE G d p yp ym S v 1 yp / (d : ℝ) ^ 2 ≤ lc →
        markE G d p yp ym S v (-1) ym / (d : ℝ) ^ 2 ≤ dc →
        |rowMean G d p yp ym S v - rowGauss G d p yp ym S v| ≤
          C * ((p : ℝ) ^ 5 * Real.sqrt (lr * rd) + (p : ℝ) ^ 4 * Real.sqrt (lc * dc) +
              (p : ℝ) ^ 13 / (d : ℝ) ^ 2) + Real.exp (-(3 * (p : ℝ))) := by
  obtain ⟨C₁, hC₁, hcore⟩ := row_comparison_core.{u}
  obtain ⟨C₅, hC₅, hX⟩ := row_x5_diff.{u}
  refine ⟨C₁ * (C₅ + 1), by positivity, (hcore.and hX).mono ?_⟩
  rintro c₀ κ₀ d p h ⟨H1, H5⟩ V _ _ G _ S lam yp ym v hC hyp hym hv lr rd lc dc hvl hllc hlcd
    hvr hS1 hS2 hD hM1 hM2
  have h1 := H1 V G S lam yp ym v hC hyp hym hv lr lc dc hvl hllc hlcd hS1 hS2 hM1 hM2
  have h5 := H5 V G S lam yp ym v hC hyp hym hv lr rd hvl hvr hS1 hD
  have hs1 : 0 ≤ Real.sqrt (lr * rd) := Real.sqrt_nonneg _
  have hs2 : 0 ≤ Real.sqrt (lc * dc) := Real.sqrt_nonneg _
  have hT : 0 ≤ (p : ℝ) ^ 13 / (d : ℝ) ^ 2 := by positivity
  have hW : 0 ≤ C₁ * ((p : ℝ) ^ 5 * Real.sqrt (lr * rd) +
      C₅ * ((p : ℝ) ^ 4 * Real.sqrt (lc * dc) + (p : ℝ) ^ 13 / (d : ℝ) ^ 2)) := by positivity
  have e : C₁ * ((p : ℝ) ^ 5 * (C₅ * Real.sqrt (lr * rd)) + (p : ℝ) ^ 4 * Real.sqrt (lc * dc) +
        (p : ℝ) ^ 13 / (d : ℝ) ^ 2) + C₁ * ((p : ℝ) ^ 5 * Real.sqrt (lr * rd) +
        C₅ * ((p : ℝ) ^ 4 * Real.sqrt (lc * dc) + (p : ℝ) ^ 13 / (d : ℝ) ^ 2)) =
      C₁ * (C₅ + 1) * ((p : ℝ) ^ 5 * Real.sqrt (lr * rd) + (p : ℝ) ^ 4 * Real.sqrt (lc * dc) +
        (p : ℝ) ^ 13 / (d : ℝ) ^ 2) := by ring
  have h2 : C₁ * ((p : ℝ) ^ 5 * rowX5 G d p yp ym S v + (p : ℝ) ^ 4 * Real.sqrt (lc * dc) +
        (p : ℝ) ^ 13 / (d : ℝ) ^ 2) ≤
      C₁ * ((p : ℝ) ^ 5 * (C₅ * Real.sqrt (lr * rd)) + (p : ℝ) ^ 4 * Real.sqrt (lc * dc) +
        (p : ℝ) ^ 13 / (d : ℝ) ^ 2) := by gcongr
  have h3 := (Real.exp_pos (-(3 * (p : ℝ)))).le
  linarith

/-- **CR1** (source display (CR1), line 1097), from CR3 with `λ_r = λ_c = C_ME λ`,
`ρ_r = δ_c = C_ME δ` (MARKENV). -/
theorem row_comparison : ∃ C : ℝ, 0 < C ∧ Eventually fun _ _ d p _ =>
    ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
      (S : Finset V) (lam : ℝ) (yp ym : V → ℝ) (v : V), CapCtx G d p S lam →
      InCube (lam * sOf d p) yp → InCube (lam * sOf d p) ym → v ∈ S →
      ∀ l δ : ℝ, vth d ≤ l → l ≤ δ →
        aOf d p ^ 2 * incRowE G d p yp ym S v 1 yp + trSqE G d p yp ym S v 1 yp ≤ l →
        aOf d p ^ 2 * incRowE G d p yp ym S v (-1) ym + trSqE G d p yp ym S v (-1) ym ≤ δ →
        |rowMean G d p yp ym S v - rowGauss G d p yp ym S v| ≤
          C * ((p : ℝ) ^ 5 * Real.sqrt (l * δ) + (p : ℝ) ^ 13 / (d : ℝ) ^ 2) +
            Real.exp (-(3 * (p : ℝ))) := by
  obtain ⟨C₁, hC₁, h3⟩ := row_comparison_split
  obtain ⟨C₂, hC₂, hME⟩ := mark_envelope
  refine ⟨2 * C₁ * C₂, by positivity, (h3.and hME).mono ?_⟩
  rintro c₀ κ₀ d p h ⟨H3, HME⟩ V _ _ G _ S lam yp ym v hC hyp hym hv l δ hl hlδ hP hM
  have hv0 : 0 ≤ vth d := by unfold vth; positivity
  have hl0 : 0 ≤ l := hv0.trans hl
  have hδ0 : 0 ≤ δ := hl0.trans hlδ
  obtain ⟨hP1, hP2⟩ := (HME V G S lam yp ym v hC hyp hym hv l hl).1 hP
  obtain ⟨hM1, hM2⟩ := (HME V G S lam yp ym v hC hyp hym hv δ (hl.trans hlδ)).2 hM
  have hCl : vth d ≤ C₂ * l := hl.trans (le_mul_of_one_le_left hl0 hC₂)
  have hCδ : C₂ * l ≤ C₂ * δ := mul_le_mul_of_nonneg_left hlδ (by linarith)
  have key := H3 V G S lam yp ym v hC hyp hym hv (C₂ * l) (C₂ * δ) (C₂ * l) (C₂ * δ) hCl hCδ
    le_rfl hCδ le_rfl hP1 hM1 hP2 hM2
  have hsq : Real.sqrt (C₂ * l * (C₂ * δ)) = C₂ * Real.sqrt (l * δ) := by
    rw [show C₂ * l * (C₂ * δ) = C₂ ^ 2 * (l * δ) by ring, Real.sqrt_mul (sq_nonneg _),
      Real.sqrt_sq (by linarith)]
  rw [hsq] at key
  have hs0 : 0 ≤ Real.sqrt (l * δ) := Real.sqrt_nonneg _
  have hp45 : (p : ℝ) ^ 4 ≤ (p : ℝ) ^ 5 := by
    rcases Nat.eq_zero_or_pos p with hp | hp
    · simp [hp]
    · exact pow_le_pow_right₀ (by exact_mod_cast hp) (by norm_num)
  have ht0 : 0 ≤ (p : ℝ) ^ 13 / (d : ℝ) ^ 2 := by positivity
  have h1 : (p : ℝ) ^ 4 * (C₂ * Real.sqrt (l * δ)) ≤ (p : ℝ) ^ 5 * (C₂ * Real.sqrt (l * δ)) :=
    mul_le_mul_of_nonneg_right hp45 (by positivity)
  have h2 : C₁ * ((p : ℝ) ^ 5 * (C₂ * Real.sqrt (l * δ)) +
      (p : ℝ) ^ 4 * (C₂ * Real.sqrt (l * δ)) + (p : ℝ) ^ 13 / (d : ℝ) ^ 2) ≤
      2 * C₁ * C₂ * ((p : ℝ) ^ 5 * Real.sqrt (l * δ) + (p : ℝ) ^ 13 / (d : ℝ) ^ 2) := by
    have h3' : (p : ℝ) ^ 13 / (d : ℝ) ^ 2 ≤ 2 * C₂ * ((p : ℝ) ^ 13 / (d : ℝ) ^ 2) := by
      nlinarith
    nlinarith
  linarith

end SecC

end BiluLinial.Tight
