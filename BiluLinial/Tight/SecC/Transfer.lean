/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecC.Root
public import BiluLinial.Tight.SecC.ShiftMat
public import BiluLinial.Tight.SecC.TransferRet

/-!
# Transfer of core-constant numerators (node T.TRC of `docs/tight/BP_SECC.md`)

AUDIT-C §3 (T.TRC), source lines 1281–1310 ((B4)) and 1290–1293 (grade bound, gap G5).

**Statement.** At a capped point, for a core functional `w` with `0 ≤ w ≤ d^{20}` on the core
support and `m₊, m₋ ≤ 3`, with `X = w t₊^{m₊} t₋^{m₋}` and `x_w = E X`,
`|E_{ν_K} 𝖦[w α^{p-m₊} β^{p-m₋}] / F_H - x_w| ≤ C (p⁴/d)(x_w + ϑ) + e^{-3p}`, `C` absolute.

**Proof (from the children).** Put `F_σ = w_σ α^{p-m₊}β^{p-m₋}` on the core support (`trcObs`) and
`F_σ = 0` off it; `F` is a core-measurable family (`hFc`).
* Remainder: A-REM (`CapPoint.trans_rem`, Section A; bridge `cp`) with the sup majorant
  `m_σ = w_σ ≤ d^{20}` (own-core moments `≤ d^{20n}`), smoothness A-SMOOTH and the sup bounds A-E5
  (`|∂^{2j}F_σ| ≤ w_σ (4p+2)^{2Σj} Π b_i^{j_i}`, orders `≤ 4k_*+4 < p - 3`):
  `|E_{ν_K}(𝖦F - Σ_{|j|_g ≤ k_*} c_j 𝖱∂^{2j}F)| ≤ d^{20} e^{-p}/d · F_H`, and
  `d^{19} e^{-p} ≤ (p⁴/d) ϑ` (`p ≥ 40 log d`).
* Retained terms pass to the actual law exactly (`coreE_rad_div_eq`, A-RET from the law identity
  `lawE_eq_coreE_rad`; `∂^{2j}F_σ` vanishes at sign vectors with `Φ = 0` by A-CLIP0).
* Grade 0: `F_σ(ξ)/Φ(ξ) = w_σ α^{-m₊}β^{-m₋} = X` on the support (F1), so the `j = 0` term is `x_w`.
* Grades `1 … k_*`: TRC-G (`retained_grades_le`).
So `C = C_G + 1`.

**Instances.** The four (B4) numerators `tr M² α^{p-2}β^p`, `tr(M𝒩) α^{p-1}β^{p-1}`,
`tr M² α^{p-3}β^p`, `tr(M𝒩) α^{p-1}β^{p-2}` (`X = X₁, X₂, X₁t₊, X₂t₋`), with
`tr M², tr(M𝒩) ≤ |N| (s a²/z)² ≤ d^{20}` for `z ≥ ϑ`.

**Checks.** `N = ∅`: `𝖦 f = 𝖱 f = w`, `t_± = 1` on the support, both sides agree exactly.
`w = 0`: both sides vanish. `m₊ = m₋ = 0`, `w = 1`: `E_{ν_K} 𝖦Φ / F_H - 1`, the bias of the
floor factor, is `O(p⁴/d)` (consistent with C1).
-/

@[expose] public section

namespace BiluLinial.Tight

namespace SecC

universe u

open Matrix

section Helpers

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable {p : ℕ} {a : ℝ} {yp ym : V → ℝ} {S : Finset V} {v : V}

theorem coreE_sum' {ι : Type*} (s : Finset ι) (f : ι → Config V → ℝ) :
    coreE G p a yp ym S v (fun σ => ∑ l ∈ s, f l σ) = ∑ l ∈ s, coreE G p a yp ym S v (f l) := by
  unfold coreE
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm, Finset.sum_div]

theorem coreE_congr' {f g : Config V → ℝ}
    (h : ∀ σ, wtCore G p a yp ym σ S v ≠ 0 → f σ = g σ) :
    coreE G p a yp ym S v f = coreE G p a yp ym S v g := by
  unfold coreE
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  by_cases hσ : wtCore G p a yp ym σ S v = 0
  · rw [hσ, zero_mul, zero_mul]
  · rw [h σ hσ]

theorem coreE_const' (hZ : 0 < ZwCore G p a yp ym S v) (c : ℝ) :
    coreE G p a yp ym S v (fun _ => c) = c := by
  show (∑ σ, wtCore G p a yp ym σ S v * c) / ZwCore G p a yp ym S v = c
  rw [← Finset.sum_mul]
  exact mul_div_cancel_left₀ c hZ.ne'

end Helpers

section Law

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable {d p : ℕ}

theorem ZwCore_pos_of_insFH {S : Finset V} {yp ym : V → ℝ} {v : V}
    (h : 0 < insFH G d p yp ym S v) : 0 < ZwCore G p (aOf d p) yp ym S v := by
  rcases (ZwCore_nonneg G (p := p) (a := aOf d p) (yp := yp) (ym := ym) (S := S) (v := v)).lt_or_eq
    with h' | h'
  · exact h'
  · exfalso
    unfold insFH coreE at h
    rw [← h', div_zero] at h
    exact lt_irrefl 0 h

/-- **A-RET** (retained terms pass to the actual law exactly): for a core-measurable family `R`
of star functions vanishing at the sign vectors where `Φ = 0`,
`E_{ν_K} 𝖱 R / F_H = E[R(ξ)/Φ(ξ)]` (`lawE_eq_coreE_rad`). -/
theorem coreE_rad_div_eq (hR : TRegime d p) {S : Finset V} {yp ym : V → ℝ}
    (hyp : ∀ i, 0 ≤ yp i) (hym : ∀ i, 0 ≤ ym i) {v : V} (hv : v ∈ S)
    (R : Config V → (nbhd G S v → ℝ) → ℝ)
    (hRc : ∀ σ σ' : Config V, (∀ e : Sym2 V, v ∉ e → σ e = σ' e) → R σ = R σ')
    (hvan : ∀ σ (ξ : nbhd G S v → ℝ), (∀ i, ξ i = 1 ∨ ξ i = -1) →
      starPhi p (rootMat G (aOf d p) 1 yp σ S v) (rootMat G (aOf d p) (-1) ym σ S v) ξ = 0 →
        R σ ξ = 0) :
    coreE G p (aOf d p) yp ym S v (fun σ => radE (R σ)) / insFH G d p yp ym S v =
      lawE G p (aOf d p) yp ym S (fun σ => R σ (rootSigns G σ S v) /
        starPhi p (rootMat G (aOf d p) 1 yp σ S v) (rootMat G (aOf d p) (-1) ym σ S v)
          (rootSigns G σ S v)) := by
  have h := lawE_eq_coreE_rad G hR hyp hym hv
    (fun σ ξ => R σ ξ /
      starPhi p (rootMat G (aOf d p) 1 yp σ S v) (rootMat G (aOf d p) (-1) ym σ S v) ξ)
    (fun σ σ' hσ => by
      funext ξ
      simp only [rootMat_eq_of_offRoot G _ 1 yp S v hσ, rootMat_eq_of_offRoot G _ (-1) ym S v hσ,
        hRc σ σ' hσ])
  refine Eq.trans ?_ h.symm
  congr 1
  refine congrArg _ (funext fun σ => ?_)
  rw [radE_eq_sum, radE_eq_sum]
  congr 1
  refine Finset.sum_congr rfl fun ε _ => ?_
  have hpm : ∀ i, (if ε i then (1 : ℝ) else -1) = 1 ∨ (if ε i then (1 : ℝ) else -1) = -1 := by
    intro i
    by_cases h : ε i <;> simp [h]
  by_cases hΦ : starPhi p (rootMat G (aOf d p) 1 yp σ S v) (rootMat G (aOf d p) (-1) ym σ S v)
      (fun i => if ε i then 1 else -1) = 0
  · rw [hΦ, mul_zero]
    exact hvan σ _ hpm hΦ
  · rw [div_mul_cancel₀ _ hΦ]

/-- Grade 0 at a supported signing (F1): `c α^{p-m₊}β^{p-m₋}(ξ)/Φ(ξ) = c t₊^{m₊} t₋^{m₋}`. -/
theorem trcObs_div_starPhi (hR : TRegime d p) {S : Finset V} {yp ym : V → ℝ}
    (hyp : ∀ i, 0 ≤ yp i) (hym : ∀ i, 0 ≤ ym i) {v : V} (hv : v ∈ S) {σ : Config V}
    (hσ : wt G p (aOf d p) yp ym σ S ≠ 0) (c : ℝ) {mp mm : ℕ} (hmp : mp ≤ p) (hmm : mm ≤ p) :
    trcObs p mp mm c (rootMat G (aOf d p) 1 yp σ S v) (rootMat G (aOf d p) (-1) ym σ S v)
        (rootSigns G σ S v) /
      starPhi p (rootMat G (aOf d p) 1 yp σ S v) (rootMat G (aOf d p) (-1) ym σ S v)
        (rootSigns G σ S v) =
      c * rootT G (aOf d p) 1 yp σ S v ^ mp * rootT G (aOf d p) (-1) ym σ S v ^ mm := by
  obtain ⟨hα, hβ, ht1, ht2, -, -, -, -⟩ := root_F1 G hR hyp hym hv hσ
  set α := starAlpha (rootMat G (aOf d p) 1 yp σ S v) (rootSigns G σ S v) with hαdef
  set β := starAlpha (rootMat G (aOf d p) (-1) ym σ S v) (rootSigns G σ S v) with hβdef
  have hcA : clipF (rootMat G (aOf d p) 1 yp σ S v) (rootSigns G σ S v) = α :=
    max_eq_left hα.le
  have hcB : clipF (rootMat G (aOf d p) (-1) ym σ S v) (rootSigns G σ S v) = β :=
    max_eq_left hβ.le
  rw [trcObs_apply, clipPow, starPhi, hcA, hcB, ht1, ht2]
  have e1 : α ^ p = α ^ (p - mp) * α ^ mp := by rw [← pow_add, Nat.sub_add_cancel hmp]
  have e2 : β ^ p = β ^ (p - mm) * β ^ mm := by rw [← pow_add, Nat.sub_add_cancel hmm]
  rw [e1, e2, _root_.one_div_pow, _root_.one_div_pow]
  have hα0 := (pow_pos hα (p - mp)).ne'
  have hβ0 := (pow_pos hβ (p - mm)).ne'
  have hα1 := (pow_pos hα mp).ne'
  have hβ1 := (pow_pos hβ mm).ne'
  field_simp

/-- `𝖦(c α^{p-m₊}β^{p-m₋}) = c 𝖦(α^{p-m₊}β^{p-m₋})`. -/
theorem gaussE_trcObs {ι : Type*} [Fintype ι] (p mp mm : ℕ) (c : ℝ) (A B : Matrix ι ι ℝ) :
    gaussE (trcObs p mp mm c A B) = c * gaussE (clipPow p mp mm A B) := by
  unfold gaussE
  rw [← MeasureTheory.integral_const_mul]
  exact congrArg _ (funext fun x => trcObs_apply p mp mm c A B x)

end Law

/-- **T.TRC.** -/
theorem core_transfer : ∃ C : ℝ, 0 < C ∧ Eventually fun _ _ d p _ =>
    ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
      (S : Finset V) (lam : ℝ) (yp ym : V → ℝ) (v : V), CapCtx G d p S lam →
      InCube (lam * sOf d p) yp → InCube (lam * sOf d p) ym → v ∈ S →
      ∀ (w : Config V → ℝ) (mp mm : ℕ), mp ≤ 3 → mm ≤ 3 → CoreInv v w →
        (∀ σ, wtCore G p (aOf d p) yp ym σ S v ≠ 0 → 0 ≤ w σ ∧ w σ ≤ (d : ℝ) ^ 20) →
        |coreE G p (aOf d p) yp ym S v (fun σ => w σ *
              gaussE (clipPow p mp mm (rootMat G (aOf d p) 1 yp σ S v)
                (rootMat G (aOf d p) (-1) ym σ S v))) / insFH G d p yp ym S v -
            lawE G p (aOf d p) yp ym S (fun σ => w σ * rootT G (aOf d p) 1 yp σ S v ^ mp *
              rootT G (aOf d p) (-1) ym σ S v ^ mm)| ≤
          C * ((p : ℝ) ^ 4 / d) *
              (lawE G p (aOf d p) yp ym S (fun σ => w σ * rootT G (aOf d p) 1 yp σ S v ^ mp *
                rootT G (aOf d p) (-1) ym σ S v ^ mm) + vth d) +
            Real.exp (-(3 * (p : ℝ))) := by
  obtain ⟨CG, hCG, hGr⟩ := retained_grades_le.{u}
  refine ⟨CG + 1, by linarith, ((hGr.and SecA.eventually_regA).and (eventually_log_le 40)).mono ?_⟩
  rintro c₀ κ₀ d p h ⟨⟨hG, hRA⟩, hlog⟩ V _ _ G _ S lam yp ym v hC hyp hym hv w mp mm hmp hmm hwc
    hwb
  classical
  have hR : TRegime d p := hRA.treg
  have hp6 := hR.hp
  have hk8 : 4 * kStar d p + 8 ≤ p := by
    have := hRA.moment_order_le
    have e : kStarA d p = kStar d p := rfl
    omega
  have hdR := hR.ten_pow_six_le_d
  have hd0 : (0 : ℝ) < d := lt_of_lt_of_le (by norm_num) hdR
  have hd1 : (1 : ℝ) ≤ d := le_trans (by norm_num) hdR
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (le_trans (by norm_num) hp6 : 1 ≤ p)
  have hyp0 : ∀ i, 0 ≤ yp i := fun i => (hyp i).1
  have hym0 : ∀ i, 0 ≤ ym i := fun i => (hym i).1
  have hyp' := inCube_of_cap G hR hC hyp
  have hym' := inCube_of_cap G hR hC hym
  have hFH := insFH_pos G hR hC hyp hym hv
  have hZc := ZwCore_pos_of_insFH G hFH
  have hp1n : 1 ≤ p := le_trans (by norm_num) hp6
  -- the bridge to a capped point of Section A
  let cp : CapPoint.{u} d p :=
    { V := V, G := G, S := S, lam := lam, yp := yp, ym := ym, ctx := hC, hyp := hyp, hym := hym }
  have hvS : v ∈ cp.S := hv
  -- the family `F` and its sup majorant `m`
  have hPSD : ∀ σ, wtCore G p (aOf d p) yp ym σ S v ≠ 0 →
      (rootMat G (aOf d p) 1 yp σ S v).PosSemidef ∧
        (rootMat G (aOf d p) (-1) ym σ S v).PosSemidef := by
    intro σ hσ
    obtain ⟨h1, h2⟩ := posDef_of_wtCore_ne_zero G hσ
    exact ⟨(shift_branch G hyp0 (hyp' v).2 one_pos h1).1,
      (shift_branch G hym0 (hym' v).2 one_pos h2).1⟩
  set F : Config V → (nbhd G S v → ℝ) → ℝ := fun σ =>
    if wtCore G p (aOf d p) yp ym σ S v ≠ 0 then
      trcObs p mp mm (w σ) (rootMat G (aOf d p) 1 yp σ S v) (rootMat G (aOf d p) (-1) ym σ S v)
    else fun _ => 0 with hF
  set m : Config V → ℝ := fun σ =>
    if wtCore G p (aOf d p) yp ym σ S v ≠ 0 then w σ else 0 with hm
  have hFs : ∀ σ, wtCore G p (aOf d p) yp ym σ S v ≠ 0 → F σ =
      trcObs p mp mm (w σ) (rootMat G (aOf d p) 1 yp σ S v)
        (rootMat G (aOf d p) (-1) ym σ S v) := fun σ hσ => by
    rw [hF]; exact ite_eq_left hσ
  have hFn : ∀ σ, ¬ wtCore G p (aOf d p) yp ym σ S v ≠ 0 → F σ = fun _ => 0 := fun σ hσ => by
    rw [hF]; exact ite_eq_right hσ
  have hmin : ∀ n, n ≤ 4 * kStar d p + 4 → n < min (p - mp) (p - mm) := fun n hn => by omega
  have hFc : ∀ σ σ' : Config V, (∀ e : Sym2 V, v ∉ e → σ e = σ' e) → F σ = F σ' := by
    intro σ σ' hσ
    have h1 := wtCore_coreInv G p (aOf d p) yp ym S v σ σ' hσ
    simp only [hF, rootMat_eq_of_offRoot G _ 1 yp S v hσ, rootMat_eq_of_offRoot G _ (-1) ym S v hσ,
      hwc σ σ' hσ]
    simp only at h1
    rw [h1]
  have hm0 : ∀ σ, 0 ≤ m σ := fun σ => by
    rw [hm]
    dsimp only
    split_ifs with hσ
    · exact (hwb σ hσ).1
    · exact le_rfl
  have hsm : ∀ σ, SmoothBdd (4 * kStarA d p + 4) (F σ) := by
    intro σ
    by_cases hσ : wtCore G p (aOf d p) yp ym σ S v ≠ 0
    · rw [hFs σ hσ]
      obtain ⟨hA, hB⟩ := hPSD σ hσ
      exact SecA.smoothBdd_clipObs hA hB
        (fun x _ _ => quadMaj_const (le_of_eq (abs_of_nonneg (hwb σ hσ).1))
          (fun i => Real.sqrt_nonneg _) x) (hmin _ le_rfl)
    · rw [hFn σ hσ]
      exact smoothBdd_const_zero _
  have hder : ∀ σ, ∀ j ∈ (topIdx (kStarA d p) : Finset (nbhd G S v → ℕ)), ∀ x,
      |dEven (nbL G S v) j (F σ) x| ≤
        m σ * (5 * (p : ℝ)) ^ (2 * ∑ i, j i) * ∏ i, (rootMat G (aOf d p) 1 yp σ S v i i +
          rootMat G (aOf d p) (-1) ym σ S v i i) ^ j i := by
    intro σ j hj x
    obtain ⟨hadm, hgr⟩ := mem_topIdx.1 hj
    have hsum := sum_le_two_mul_grade hadm
    by_cases hσ : wtCore G p (aOf d p) yp ym σ S v ≠ 0
    · rw [hFs σ hσ]
      have hmσ : m σ = w σ := by rw [hm]; exact ite_eq_left hσ
      rw [hmσ]
      obtain ⟨hA, hB⟩ := hPSD σ hσ
      have hlen : (dEvenList (Finset.univ : Finset (nbhd G S v)).toList j).length =
          2 * ∑ i, j i := length_dEvenList_univ j
      have h5 := SecA.pderivList_clipObs_le (e₁ := p - mp) (e₂ := p - mm) hA hB
        (fun x _ _ => quadMaj_const (le_of_eq (abs_of_nonneg (hwb σ hσ).1))
          (fun i => Real.sqrt_nonneg _) x) (dEvenList (Finset.univ : Finset (nbhd G S v)).toList j)
        (by rw [hlen]; exact hmin _ (by
          have e : kStarA d p = kStar d p := rfl
          rw [e] at hgr
          omega)) x
      rw [hlen, prod_map_dEvenList_univ] at h5
      have hprod : ∏ i, Real.sqrt (rootMat G (aOf d p) 1 yp σ S v i i +
            rootMat G (aOf d p) (-1) ym σ S v i i) ^ (2 * j i) =
          ∏ i, (rootMat G (aOf d p) 1 yp σ S v i i + rootMat G (aOf d p) (-1) ym σ S v i i) ^ j i :=
        Finset.prod_congr rfl fun i _ => by
          rw [pow_mul, Real.sq_sqrt (add_nonneg hA.diag_nonneg hB.diag_nonneg)]
      rw [hprod] at h5
      refine h5.trans ?_
      have hb0 : 0 ≤ ∏ i, (rootMat G (aOf d p) 1 yp σ S v i i +
          rootMat G (aOf d p) (-1) ym σ S v i i) ^ j i :=
        Finset.prod_nonneg fun i _ => pow_nonneg (add_nonneg hA.diag_nonneg hB.diag_nonneg) _
      have hbase : 2 * (1 + ((p - mp : ℕ) : ℝ) + ((p - mm : ℕ) : ℝ)) ≤ 5 * p := by
        have h1 : ((p - mp : ℕ) : ℝ) ≤ p := by exact_mod_cast Nat.sub_le p mp
        have h2 : ((p - mm : ℕ) : ℝ) ≤ p := by exact_mod_cast Nat.sub_le p mm
        have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hR.two_le_p
        linarith
      have hpow := pow_le_pow_left₀ (by positivity) hbase (2 * ∑ i, j i)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow (hwb σ hσ).1) hb0
    · rw [hFn σ hσ]
      have hmσ : m σ = 0 := by rw [hm]; exact ite_eq_right hσ
      rw [hmσ, dEven_eq_pderivList, pderivList_const_zero]
      simp
  have hmom : ∀ n : ℕ, 1 ≤ n → 2 * n ≤ p →
      coreE G p (aOf d p) yp ym S v (fun σ => m σ ^ n) ≤ ((d : ℝ) ^ 20) ^ n := by
    intro n _ _
    calc coreE G p (aOf d p) yp ym S v (fun σ => m σ ^ n)
        ≤ coreE G p (aOf d p) yp ym S v (fun _ => ((d : ℝ) ^ 20) ^ n) :=
          coreE_mono G fun σ hσ => by
            have hmσ : m σ = w σ := by rw [hm]; exact ite_eq_left hσ
            rw [hmσ]
            exact pow_le_pow_left₀ (hwb σ hσ).1 (hwb σ hσ).2 n
      _ = ((d : ℝ) ^ 20) ^ n := coreE_const' G hZc _
  have hrem : |coreE G p (aOf d p) yp ym S v (fun σ => gaussE (F σ) -
        ∑ j ∈ (retIdx (kStar d p) : Finset (nbhd G S v → ℕ)),
          ecoefM j * radE (dEven (nbL G S v) j (F σ)))| ≤
      (d : ℝ) ^ 20 * Real.exp (-(p : ℝ)) / d * insFH G d p yp ym S v :=
    cp.trans_rem hRA hvS F m hm0 (M := (d : ℝ) ^ 20) (by positivity) hmom hsm hder
  -- notation for the pieces
  set k := kStar d p with hk
  set FH := insFH G d p yp ym S v with hFHdef
  set xw := lawE G p (aOf d p) yp ym S (fun σ => w σ * rootT G (aOf d p) 1 yp σ S v ^ mp *
      rootT G (aOf d p) (-1) ym σ S v ^ mm) with hxw
  set Γ := coreE G p (aOf d p) yp ym S v (fun σ => w σ *
      gaussE (clipPow p mp mm (rootMat G (aOf d p) 1 yp σ S v)
        (rootMat G (aOf d p) (-1) ym σ S v))) with hΓ
  set L : (nbhd G S v → ℕ) → ℝ := fun j => lawE G p (aOf d p) yp ym S (fun σ =>
      dEven (nbL G S v) j (F σ) (rootSigns G σ S v) /
        starPhi p (rootMat G (aOf d p) 1 yp σ S v) (rootMat G (aOf d p) (-1) ym σ S v)
          (rootSigns G σ S v)) with hL
  -- linearity of the core average
  have hlin : coreE G p (aOf d p) yp ym S v (fun σ => gaussE (F σ) -
        ∑ j ∈ (retIdx k : Finset (nbhd G S v → ℕ)),
          ecoefM j * radE (dEven (nbL G S v) j (F σ))) =
      Γ - ∑ j ∈ (retIdx k : Finset (nbhd G S v → ℕ)), ecoefM j * (FH * L j) := by
    rw [coreE_sub, coreE_sum']
    congr 1
    · refine coreE_congr' G fun σ hσ => ?_
      rw [hFs σ hσ, gaussE_trcObs]
    · refine Finset.sum_congr rfl fun j hj => ?_
      rw [coreE_const_mul]
      congr 1
      obtain ⟨-, hgr⟩ := mem_retIdx.1 hj
      have hret := coreE_rad_div_eq G hR hyp0 hym0 hv (fun σ => dEven (nbL G S v) j (F σ))
        (fun σ σ' hσ => by simp only [hFc σ σ' hσ])
        (fun σ ξ hξ hΦ => by
          by_cases hσ : wtCore G p (aOf d p) yp ym σ S v ≠ 0
          · rw [hFs σ hσ, dEven_eq_pderivList]
            obtain ⟨hA, hB⟩ := hPSD σ hσ
            refine SecA.pderivList_clipObs_eq_zero hA hB (by
                have : quadFn (w σ) (0 : nbhd G S v → ℝ) 0 = fun _ => w σ := by
                  funext x; simp [quadFn, qForm]
                rw [this]; exact contDiff_const) _ ?_ ?_
            · rw [nbL, length_dEvenList_univ]
              have := sum_le_two_mul_grade (mem_retIdx.1 hj).1
              exact hmin _ (by omega)
            · have h0 : clipF (rootMat G (aOf d p) 1 yp σ S v) ξ ^ p *
                  clipF (rootMat G (aOf d p) (-1) ym σ S v) ξ ^ p = 0 := hΦ
              rcases mul_eq_zero.1 h0 with h | h
              · left
                have := pow_eq_zero_iff (n := p) (by omega) |>.1 h
                simp only [clipF] at this
                have := le_max_left (1 - qForm (rootMat G (aOf d p) 1 yp σ S v) ξ) 0
                linarith
              · right
                have := pow_eq_zero_iff (n := p) (by omega) |>.1 h
                simp only [clipF] at this
                have := le_max_left (1 - qForm (rootMat G (aOf d p) (-1) ym σ S v) ξ) 0
                linarith
          · rw [hFn σ hσ, dEven_eq_pderivList, pderivList_const_zero])
      rw [div_eq_iff hFH.ne'] at hret
      rw [hret, hL, mul_comm]
  rw [hlin] at hrem
  -- grade 0 and the retained grades
  have h0mem : (0 : nbhd G S v → ℕ) ∈ (retIdx k : Finset (nbhd G S v → ℕ)) :=
    mem_retIdx.2 ⟨fun i => by simp, by simp⟩
  have hL0 : L 0 = xw := by
    rw [hL]
    simp only [dEven_zero]
    refine lawE_congr G fun σ hσ => ?_
    have hc := wtCore_ne_zero_of_wt G hp1n hyp0 hym0 hv hσ
    rw [hFs σ hc]
    exact trcObs_div_starPhi G hR hyp0 hym0 hv hσ (w σ) (by omega) (by omega)
  have hsplit : ∑ j ∈ (retIdx k : Finset (nbhd G S v → ℕ)), ecoefM j * (FH * L j) =
      FH * (xw + ∑ j ∈ (retIdx k : Finset (nbhd G S v → ℕ)).erase 0, ecoefM j * L j) := by
    rw [← Finset.add_sum_erase _ _ h0mem, ecoefM_zero, hL0, mul_add, Finset.mul_sum]
    congr 1
    · ring
    · exact Finset.sum_congr rfl fun j _ => by ring
  have hLret : ∑ j ∈ (retIdx k : Finset (nbhd G S v → ℕ)).erase 0, ecoefM j * L j =
      ∑ j ∈ (retIdx k : Finset (nbhd G S v → ℕ)).erase 0, ecoefM j *
        lawE G p (aOf d p) yp ym S (fun σ =>
          dEven (nbL G S v) j (trcObs p mp mm (w σ) (rootMat G (aOf d p) 1 yp σ S v)
              (rootMat G (aOf d p) (-1) ym σ S v)) (rootSigns G σ S v) /
            starPhi p (rootMat G (aOf d p) 1 yp σ S v) (rootMat G (aOf d p) (-1) ym σ S v)
              (rootSigns G σ S v)) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    rw [hL]
    refine lawE_congr G fun σ hσ => ?_
    rw [hFs σ (wtCore_ne_zero_of_wt G hp1n hyp0 hym0 hv hσ)]
  have hGb := hG V G S lam yp ym v hC hyp hym hv w mp mm hmp hmm hwb
  rw [← hLret] at hGb
  set Rt := ∑ j ∈ (retIdx k : Finset (nbhd G S v → ℕ)).erase 0, ecoefM j * L j with hRt
  rw [hsplit] at hrem
  -- the remainder is below `(p⁴/d) ϑ`
  have hxw0 : 0 ≤ xw := lawE_nonneg G fun σ hσ => by
    have hc := wtCore_ne_zero_of_wt G hp1n hyp0 hym0 hv hσ
    obtain ⟨ht1, ht2⟩ := rootT_nonneg G hyp0 hym0 hσ v
    exact mul_nonneg (mul_nonneg (hwb σ hc).1 (pow_nonneg ht1 _)) (pow_nonneg ht2 _)
  have hθ : 0 < vth d := by unfold vth; positivity
  have hed : (d : ℝ) ^ 40 ≤ Real.exp p := by
    rw [← Real.exp_log (pow_pos hd0 40), Real.log_pow]
    exact Real.exp_le_exp.mpr (by push_cast; linarith)
  have hremb : (d : ℝ) ^ 20 * Real.exp (-(p : ℝ)) / d ≤ (p : ℝ) ^ 4 / d * vth d := by
    have hd0' : (d : ℝ) ≠ 0 := hd0.ne'
    have hep : Real.exp (-(p : ℝ)) ≤ 1 / (d : ℝ) ^ 40 := by
      rw [Real.exp_neg, inv_eq_one_div]
      exact one_div_le_one_div_of_le (pow_pos hd0 40) hed
    have hp4 : (1 : ℝ) ≤ (p : ℝ) ^ 4 := one_le_pow₀ hp1
    calc (d : ℝ) ^ 20 * Real.exp (-(p : ℝ)) / d ≤ (d : ℝ) ^ 20 * (1 / (d : ℝ) ^ 40) / d := by
          gcongr
      _ = 1 / (d : ℝ) ^ 21 := by field_simp
      _ ≤ 1 / (d : ℝ) ^ 11 :=
          one_div_le_one_div_of_le (pow_pos hd0 11) (pow_le_pow_right₀ hd1 (by norm_num))
      _ ≤ (p : ℝ) ^ 4 / (d : ℝ) ^ 11 := div_le_div_of_nonneg_right hp4 (pow_pos hd0 11).le
      _ = (p : ℝ) ^ 4 / d * vth d := by unfold vth; field_simp
  -- assemble
  have hdiv : |Γ / FH - (xw + Rt)| ≤ (d : ℝ) ^ 20 * Real.exp (-(p : ℝ)) / d := by
    rw [show Γ / FH - (xw + Rt) = (Γ - FH * (xw + Rt)) / FH by field_simp, abs_div,
      abs_of_pos hFH, div_le_iff₀ hFH]
    exact hrem
  have hpd : 0 ≤ (p : ℝ) ^ 4 / d := by positivity
  have h3 : 0 ≤ Real.exp (-(3 * (p : ℝ))) := (Real.exp_pos _).le
  calc |Γ / FH - xw| = |(Γ / FH - (xw + Rt)) + Rt| := by ring_nf
    _ ≤ |Γ / FH - (xw + Rt)| + |Rt| := abs_add_le _ _
    _ ≤ (p : ℝ) ^ 4 / d * vth d + CG * ((p : ℝ) ^ 4 / d) * (xw + vth d) :=
        add_le_add (hdiv.trans hremb) hGb
    _ ≤ (CG + 1) * ((p : ℝ) ^ 4 / d) * (xw + vth d) + Real.exp (-(3 * (p : ℝ))) := by
        nlinarith [mul_nonneg hpd hxw0]

end SecC

end BiluLinial.Tight
