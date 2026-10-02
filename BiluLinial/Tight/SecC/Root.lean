/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecC.Regime
public import BiluLinial.Tight.Star
public import BiluLinial.Tight.SourceMax.Law
public import BiluLinial.Tight.Deletion
public import BiluLinial.Tight.FloorLemma

/-!
# Root identities and the own core law (node T.ROOT of `docs/tight/BP_SECC.md`)

AUDIT-C §3 (T.ROOT), source (F1) (lines 125–141) and lines 1135–1151, 1323–1325.

* **Own core law** (proved): `wtCore ≥ 0`, linearity and monotonicity of `coreE` on the core
  support (`coreE_add`, `coreE_sub`, `coreE_const_mul`, `coreE_mono`); the inherited core
  precision does not see the signs at `v` (`precCore_congr`), hence `rootMat`, `shiftY`, `shiftM`
  and the core weight are core functionals (`CoreInv`).
* **Law identity** (proved): the actual law is the own core law tilted by the fresh-star factor,
  `E ψ = E_{ν_K} 𝖱[ψ Φ] / F_H` (`lawE_eq_coreE_rad`, from `lawE_eq_star` of `Tight/Star.lean`).
  The floor `F_H ≥ 40^{-p}` (`insFH_ge`) follows with `floor_ins` and the deletion transfer.
* **Physical form of `Q`** (proved): `(p-1) E X₁ + p E X₂ = a² Q` (`shiftQ_eq`), since
  `X₁ = a⁴ G_vv² tr Y₊²` and `X₂ = a⁴ G⁺_vv G⁻_vv tr(Y₊Y₋)` identically (`G_vv = y_v h_v`).
* (F1), the row numerator and the Frobenius bound are in `Tight/SecC/F1.lean`.
-/

@[expose] public section

namespace BiluLinial.Tight

namespace SecC

open Matrix

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ### The paired law -/

section Law0

variable {p : ℕ} {a : ℝ} {yp ym : V → ℝ} {S : Finset V}

/-- Monotonicity of the paired law on its support (the other `lawE` facts are in
`Tight/SourceMax/Law.lean`). -/
theorem lawE_mono {f g : Config V → ℝ} (h : ∀ σ, wt G p a yp ym σ S ≠ 0 → f σ ≤ g σ) :
    lawE G p a yp ym S f ≤ lawE G p a yp ym S g := by
  unfold lawE
  refine div_le_div_of_nonneg_right (Finset.sum_le_sum fun σ _ => ?_) (Zw_nonneg G)
  by_cases hw : wt G p a yp ym σ S = 0
  · rw [hw, zero_mul, zero_mul]
  · exact mul_le_mul_of_nonneg_left (h σ hw) (wt_nonneg G σ)

end Law0

/-! ### The own core law -/

section CoreLaw

variable {p : ℕ} {a : ℝ} {yp ym : V → ℝ} {S : Finset V} {v : V}

theorem wtCore_nonneg (σ : Config V) : 0 ≤ wtCore G p a yp ym σ S v := by
  unfold wtCore
  split_ifs with h
  · exact pow_nonneg (mul_nonneg h.1.det_pos.le h.2.det_pos.le) p
  · exact le_rfl

theorem ZwCore_nonneg : 0 ≤ ZwCore G p a yp ym S v :=
  Finset.sum_nonneg fun σ _ => wtCore_nonneg G σ

theorem coreE_add (f g : Config V → ℝ) :
    coreE G p a yp ym S v (fun σ => f σ + g σ) =
      coreE G p a yp ym S v f + coreE G p a yp ym S v g := by
  unfold coreE
  rw [← add_div, ← Finset.sum_add_distrib]
  simp only [mul_add]

theorem coreE_sub (f g : Config V → ℝ) :
    coreE G p a yp ym S v (fun σ => f σ - g σ) =
      coreE G p a yp ym S v f - coreE G p a yp ym S v g := by
  unfold coreE
  rw [← sub_div, ← Finset.sum_sub_distrib]
  simp only [mul_sub]

theorem coreE_const_mul (c : ℝ) (f : Config V → ℝ) :
    coreE G p a yp ym S v (fun σ => c * f σ) = c * coreE G p a yp ym S v f := by
  unfold coreE
  rw [mul_div_assoc', Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun σ _ => by ring

theorem coreE_mono {f g : Config V → ℝ}
    (h : ∀ σ, wtCore G p a yp ym σ S v ≠ 0 → f σ ≤ g σ) :
    coreE G p a yp ym S v f ≤ coreE G p a yp ym S v g := by
  unfold coreE
  refine div_le_div_of_nonneg_right (Finset.sum_le_sum fun σ _ => ?_) (ZwCore_nonneg G)
  by_cases hw : wtCore G p a yp ym σ S v = 0
  · rw [hw, zero_mul, zero_mul]
  · exact mul_le_mul_of_nonneg_left (h σ hw) (wtCore_nonneg G σ)

theorem posDef_of_wtCore_ne_zero {σ : Config V} (h : wtCore G p a yp ym σ S v ≠ 0) :
    (precCore G a 1 yp σ S v).PosDef ∧ (precCore G a (-1) ym σ S v).PosDef := by
  unfold wtCore at h
  by_contra hc
  exact h (by rw [ite_eq_right hc])

end CoreLaw

/-! ### Core functionals -/

section CoreInv

omit [Fintype V] in
/-- The inherited core precision does not see the signs of the pairs at `v`. -/
theorem precCore_congr (a τ : ℝ) (y : V → ℝ) {σ σ' : Config V} (S : Finset V) (v : V)
    (h : ∀ e : Sym2 V, v ∉ e → σ e = σ' e) :
    precCore G a τ y σ S v = precCore G a τ y σ' S v := by
  ext u w
  simp only [precCore, precN, of_apply]
  by_cases huv : u = v ∨ w = v
  · rw [ite_eq_left huv, ite_eq_left huv]
  · rw [ite_eq_right huv, ite_eq_right huv]
    push Not at huv
    have hs : sgn σ u w = sgn σ' u w := by
      unfold sgn
      rw [h s(u, w) (by simp [Sym2.mem_iff, Ne.symm huv.1, Ne.symm huv.2])]
    rw [hs]

theorem wtCore_coreInv (p : ℕ) (a : ℝ) (yp ym : V → ℝ) (S : Finset V) (v : V) :
    CoreInv v fun σ => wtCore G p a yp ym σ S v := by
  intro σ σ' h
  have h1 := precCore_congr G a 1 yp S v h
  have h2 := precCore_congr G a (-1) ym S v h
  show wtCore G p a yp ym σ S v = wtCore G p a yp ym σ' S v
  unfold wtCore
  rw [h1, h2]

theorem rootMat_eq_of_offRoot (a τ : ℝ) (y : V → ℝ) {σ σ' : Config V} (S : Finset V) (v : V)
    (h : ∀ e : Sym2 V, v ∉ e → σ e = σ' e) :
    rootMat G a τ y σ S v = rootMat G a τ y σ' S v := by
  ext i j
  simp only [rootMat, coreGreen, of_apply, precCore_congr G a τ y S v h]

theorem shiftM_congr (a τ z : ℝ) (y : V → ℝ) {σ σ' : Config V} (S : Finset V) (v : V)
    (h : ∀ e : Sym2 V, v ∉ e → σ e = σ' e) :
    shiftM G a τ z y σ S v = shiftM G a τ z y σ' S v := by
  ext i j
  simp only [shiftM, shiftY, coreShift, Matrix.smul_apply, of_apply,
    precCore_congr G a τ y S v h]

omit [Fintype V] in
/-- The inherited core precision is symmetric. -/
theorem precCore_isHermitian (a τ : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) (v : V) :
    (precCore G a τ y σ S v).IsHermitian := by
  have hP := precN_isHermitian' G a τ y σ S
  refine IsHermitian.ext fun i j => ?_
  have h : precN G a τ y σ S j i = precN G a τ y σ S i j := by simpa using hP.apply i j
  simp only [precCore, of_apply, star_trivial]
  by_cases hij : j = v ∨ i = v
  · rw [ite_eq_left hij, ite_eq_left hij.symm]
    by_cases h3 : j = i
    · rw [ite_eq_left h3, ite_eq_left h3.symm]
    · rw [ite_eq_right h3, ite_eq_right (Ne.symm h3)]
  · rw [ite_eq_right hij, ite_eq_right (fun h' => hij h'.symm), h]

/-- The root matrices are symmetric. -/
theorem rootMat_apply_comm (a τ : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) (v : V)
    (i j : nbhd G S v) : rootMat G a τ y σ S v i j = rootMat G a τ y σ S v j i := by
  have h := (precCore_isHermitian G a τ y σ S v).inv
  have hij : (precCore G a τ y σ S v)⁻¹ j i = (precCore G a τ y σ S v)⁻¹ i j := by
    simpa using h.apply i j
  simp only [rootMat, coreGreen, of_apply, hij]
  ring

/-- `tr A² ≥ 0` (any signing; `A` is symmetric). -/
theorem trace_rootMat_sq_nonneg (a τ : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) (v : V) :
    0 ≤ (rootMat G a τ y σ S v * rootMat G a τ y σ S v).trace := by
  simp only [trace, diag, mul_apply]
  refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
  rw [rootMat_apply_comm G a τ y σ S v j i]
  exact mul_self_nonneg _

/-- Any function of the root matrices `A, B` and the shifted matrices `M, 𝒩` is a core
functional. -/
theorem coreInv_of_mats (a z : ℝ) (yp ym : V → ℝ) (S : Finset V) (v : V)
    (F : Matrix (nbhd G S v) (nbhd G S v) ℝ → Matrix (nbhd G S v) (nbhd G S v) ℝ →
      Matrix (nbhd G S v) (nbhd G S v) ℝ → Matrix (nbhd G S v) (nbhd G S v) ℝ → ℝ) :
    CoreInv v fun σ => F (rootMat G a 1 yp σ S v) (rootMat G a (-1) ym σ S v)
      (shiftM G a 1 z yp σ S v) (shiftM G a (-1) z ym σ S v) := by
  intro σ σ' h
  simp only [rootMat_eq_of_offRoot G a 1 yp S v h, rootMat_eq_of_offRoot G a (-1) ym S v h,
    shiftM_congr G a 1 z yp S v h, shiftM_congr G a (-1) z ym S v h]

end CoreInv

/-! ### The law identity and the floor -/

section Law

variable {d p : ℕ}

omit [Fintype V] [DecidableEq V] in
theorem diagD_pos (a : ℝ) {y : V → ℝ} (hy : ∀ i, 0 ≤ y i) (S : Finset V) (v : V) :
    0 < diagD G a y S v := by
  have h : ∀ j ∈ nbhd G S v, 0 ≤ cEdge a y v j := by
    intro j _
    unfold cEdge cRoot
    have h0 : 0 ≤ a ^ 2 * y v * y j := by
      have := hy v
      have := hy j
      positivity
    have : 1 ≤ Real.sqrt (1 + 4 * (a ^ 2 * y v * y j)) := Real.one_le_sqrt.2 (by linarith)
    linarith
  unfold diagD
  linarith [Finset.sum_nonneg h]

/-- **Law identity** (`E ψ = E_{ν_K} 𝖱[ψ Φ] / F_H`, AUDIT-A INS(i)). For a family `Ψ σ` of
functions of the star vector that depends only on the core signs (`Ψ σ = Ψ σ'` when `σ, σ'`
agree off `v`), the actual law of `Ψ σ ξ(σ)` is the own core law of the Rademacher average of
`Ψ σ · Φ`, divided by `F_H`. This is `lawE_eq_star` (`Tight/Star.lean`) with
`Ψ (setRoot σ ξ) = Ψ σ` and `ξ(setRoot σ ξ) = ξ` on sign vectors (`radE_eq_sum`). -/
theorem lawE_eq_coreE_rad (hR : TRegime d p) {S : Finset V} {yp ym : V → ℝ}
    (hyp : ∀ i, 0 ≤ yp i) (hym : ∀ i, 0 ≤ ym i) {v : V} (hv : v ∈ S)
    (Ψ : Config V → (nbhd G S v → ℝ) → ℝ)
    (hΨ : ∀ σ σ' : Config V, (∀ e : Sym2 V, v ∉ e → σ e = σ' e) → Ψ σ = Ψ σ') :
    lawE G p (aOf d p) yp ym S (fun σ => Ψ σ (rootSigns G σ S v)) =
      coreE G p (aOf d p) yp ym S v (fun σ => radE fun x => Ψ σ x *
          starPhi p (rootMat G (aOf d p) 1 yp σ S v) (rootMat G (aOf d p) (-1) ym σ S v) x) /
        insFH G d p yp ym S v := by
  have hp1 : 1 ≤ p := le_trans (by norm_num) hR.two_le_p
  rw [lawE_eq_star G hp1 (aOf d p) hyp hym hv]
  have hrad : ∀ σ : Config V,
      radE (fun ξ => starPhi p (rootMat G (aOf d p) 1 yp σ S v)
          (rootMat G (aOf d p) (-1) ym σ S v) ξ *
        Ψ (setRoot G S v σ ξ) (rootSigns G (setRoot G S v σ ξ) S v)) =
      radE (fun x => Ψ σ x *
        starPhi p (rootMat G (aOf d p) 1 yp σ S v) (rootMat G (aOf d p) (-1) ym σ S v) x) := by
    intro σ
    rw [radE_eq_sum, radE_eq_sum]
    congr 1
    refine Finset.sum_congr rfl fun ε _ => ?_
    have hpm : ∀ i, (if ε i then (1 : ℝ) else -1) = 1 ∨ (if ε i then (1 : ℝ) else -1) = -1 := by
      intro i
      by_cases h : ε i <;> simp [h]
    have hoff : ∀ e : Sym2 V, v ∉ e →
        setRoot G S v σ (fun i => if ε i then 1 else -1) e = σ e := by
      intro e he
      refine setRoot_apply_of_not G σ _ ?_
      rintro ⟨i, rfl⟩
      exact he (Sym2.mem_mk_left v i)
    rw [rootSigns_setRoot G σ hpm, hΨ _ σ hoff]
    ring
  simp only [hrad]
  unfold insFH coreE
  by_cases hZ : ZwCore G p (aOf d p) yp ym S v = 0
  · have hw : ∀ σ, wtCore G p (aOf d p) yp ym σ S v = 0 := fun σ =>
      (Finset.sum_eq_zero_iff_of_nonneg fun σ _ => wtCore_nonneg G σ).1 hZ σ (Finset.mem_univ _)
    simp [hw]
  · rw [div_div_div_cancel_right₀ hZ]

/-- The insertion floor `F_H ≥ 40^{-p}` at a capped point (`floor_ins`, with the core means
`≤ r ≤ 1.01` from the induction hypothesis through the deletion transfer, and
`F_H = E_{ν_K} Φ(ξ)` by the law identity). -/
theorem insFH_ge (hR : TRegime d p) {S : Finset V} {lam : ℝ} {yp ym : V → ℝ}
    (hC : CapCtx G d p S lam) (hyp : InCube (lam * sOf d p) yp)
    (hym : InCube (lam * sOf d p) ym) {v : V} (hv : v ∈ S) :
    1 / (40 : ℝ) ^ p ≤ insFH G d p yp ym S v := by
  have hs := hR.sOf_pos
  have hls : lam * sOf d p ≤ sOf d p := mul_le_of_le_one_left hs.le hC.lam_le_one
  have hyp' : InCube (sOf d p) yp := fun i => ⟨(hyp i).1, (hyp i).2.trans hls⟩
  have hym' : InCube (sOf d p) ym := fun i => ⟨(hym i).1, (hym i).2.trans hls⟩
  have hp1 : 1 ≤ p := le_trans (by norm_num) hR.two_le_p
  have hyp0 : ∀ i, 0 ≤ yp i := fun i => (hyp i).1
  have hym0 : ∀ i, 0 ≤ ym i := fun i => (hym i).1
  obtain ⟨yp', ep, hyp'', hep, hcp⟩ := precCore_eq_congr G (aOf d p) hyp0 hv
  obtain ⟨ym', em, hym'', hem, hcm⟩ := precCore_eq_congr G (aOf d p) hym0 hv
  have hc1 : InCube (sOf d p) yp' := fun i => ⟨(hyp'' i).1, (hyp'' i).2.trans (hyp' i).2⟩
  have hc2 : InCube (sOf d p) ym' := fun i => ⟨(hym'' i).1, (hym'' i).2.trans (hym' i).2⟩
  obtain ⟨hZJ, hmJ⟩ := hC.ih (S.erase v) (Finset.erase_ssubset hv) yp' ym' hc1 hc2
  have hZc := ZwCore_pos_of_congr G hep hem hcp hcm hZJ
  have hmean : ∀ i ∈ nbhd G S v,
      coreE G p (aOf d p) yp ym S v (fun σ => (precCore G (aOf d p) 1 yp σ S v)⁻¹ i i) ≤
          101 / 100 ∧
        coreE G p (aOf d p) yp ym S v (fun σ => (precCore G (aOf d p) (-1) ym σ S v)⁻¹ i i) ≤
          101 / 100 := by
    intro i hi
    have hiJ : i ∈ S.erase v := by
      have hi' := Finset.mem_filter.1 hi
      exact Finset.mem_erase.2 ⟨(G.ne_of_adj hi'.2).symm, hi'.1⟩
    exact coreE_inv_le_of_congr G hep hem hcp hcm hZJ i
      (((hmJ i hiJ).1).trans hR.rOf_le) (((hmJ i hiJ).2).trans hR.rOf_le)
  have hfl := floor_ins G hR hC.deg hyp' hym' hv hZc hmean
  -- `Σ W_core Φ(ξ(σ)) = Σ W_core 𝖱 Φ`
  have hstar := sum_wt_mul_eq_star G hp1 (aOf d p) hyp0 hym0 hv (fun _ => 1)
  simp only [mul_one] at hstar
  have hsum : ∑ σ : Config V, wt G p (aOf d p) yp ym σ S =
      (diagD G (aOf d p) yp S v * diagD G (aOf d p) ym S v) ^ p *
        ∑ σ : Config V, wtCore G p (aOf d p) yp ym σ S v * PhiRoot G p (aOf d p) yp ym σ S v := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [wt_eq_wtCore_mul G hp1 (aOf d p) hyp0 hym0 σ hv]
    ring
  have hDp : 0 < (diagD G (aOf d p) yp S v * diagD G (aOf d p) ym S v) ^ p :=
    pow_pos (mul_pos (diagD_pos G _ hyp0 S v) (diagD_pos G _ hym0 S v)) p
  have heq : ∑ σ : Config V, wtCore G p (aOf d p) yp ym σ S v *
        radE (starPhi p (rootMat G (aOf d p) 1 yp σ S v) (rootMat G (aOf d p) (-1) ym σ S v)) =
      ∑ σ : Config V, wtCore G p (aOf d p) yp ym σ S v * PhiRoot G p (aOf d p) yp ym σ S v :=
    mul_left_cancel₀ hDp.ne' (hstar.symm.trans hsum)
  unfold insFH coreE
  rw [heq, le_div_iff₀ hZc, div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
  linarith

/-- Sources of the capped cube `[0, λ s]^V` lie in `[0, s]^V`. -/
theorem inCube_of_cap (hR : TRegime d p) {S : Finset V} {lam : ℝ} (hC : CapCtx G d p S lam)
    {y : V → ℝ} (hy : InCube (lam * sOf d p) y) : InCube (sOf d p) y :=
  fun i => ⟨(hy i).1, (hy i).2.trans (mul_le_of_le_one_left hR.sOf_pos.le hC.lam_le_one)⟩

omit [DecidableEq V] in
/-- `|N_S(v)| ≤ deg v ≤ d`. -/
theorem card_nbhd_le (hdeg : ∀ v, G.degree v ≤ d) (S : Finset V) (v : V) :
    Fintype.card (nbhd G S v) ≤ d := by
  rw [Fintype.card_coe]
  refine le_trans (Finset.card_le_card fun x hx => ?_) (hdeg v)
  rw [SimpleGraph.mem_neighborFinset]
  exact (Finset.mem_filter.1 hx).2

/-- The minus normalized inverse diagonal is positive on the support. -/
theorem hN_pos_minus {a : ℝ} {yp ym : V → ℝ} {S : Finset V} {σ : Config V}
    (h : wt G p a yp ym σ S ≠ 0) (i : V) : 0 < hN G a (-1) ym σ S i := by
  have hPD : (precN G a (-1) ym σ S).PosDef := by
    by_contra hc
    exact h (by simp [wt, hc])
  exact hPD.inv.diag_pos

/-- The support of the law lies in the core support. -/
theorem wtCore_ne_zero_of_wt (hp : 1 ≤ p) {a : ℝ} {yp ym : V → ℝ} (hyp : ∀ i, 0 ≤ yp i)
    (hym : ∀ i, 0 ≤ ym i) {S : Finset V} {v : V} (hv : v ∈ S) {σ : Config V}
    (h : wt G p a yp ym σ S ≠ 0) : wtCore G p a yp ym σ S v ≠ 0 := by
  intro h0
  apply h
  rw [wt_eq_wtCore_mul G hp a hyp hym σ hv, h0, zero_mul, zero_mul]

/-- `t^± = D_v h_v^± ≥ 0` on the support. -/
theorem rootT_nonneg {a : ℝ} {yp ym : V → ℝ} (hyp : ∀ i, 0 ≤ yp i) (hym : ∀ i, 0 ≤ ym i)
    {S : Finset V} {σ : Config V} (h : wt G p a yp ym σ S ≠ 0) (v : V) :
    0 ≤ rootT G a 1 yp σ S v ∧ 0 ≤ rootT G a (-1) ym σ S v :=
  ⟨mul_nonneg (diagD_pos G a hyp S v).le (hN_pos G h v).le,
    mul_nonneg (diagD_pos G a hym S v).le (hN_pos_minus G h v).le⟩

theorem insFH_pos (hR : TRegime d p) {S : Finset V} {lam : ℝ} {yp ym : V → ℝ}
    (hC : CapCtx G d p S lam) (hyp : InCube (lam * sOf d p) yp)
    (hym : InCube (lam * sOf d p) ym) {v : V} (hv : v ∈ S) : 0 < insFH G d p yp ym S v :=
  lt_of_lt_of_le (by positivity) (insFH_ge G hR hC hyp hym hv)

end Law

/-! ### (F1), the row numerator and the Frobenius bound -/

section F1

variable {d p : ℕ}

omit [Fintype V] in
/-- `P̃_K + z Y_K` is symmetric. -/
theorem shiftCore_isHermitian (a τ z : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) (v : V) :
    (precCore G a τ y σ S v + z • srcDiag y (S.erase v)).IsHermitian := by
  have hP := precCore_isHermitian G a τ y σ S v
  refine IsHermitian.ext fun i j => ?_
  have h1 : precCore G a τ y σ S v j i = precCore G a τ y σ S v i j := by
    simpa using hP.apply i j
  simp only [star_trivial, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, srcDiag,
    diagonal_apply, h1]
  by_cases hij : j = i
  · subst hij; rfl
  · rw [ite_eq_right hij, ite_eq_right (Ne.symm hij)]

/-- The shifted core inverse is symmetric. -/
theorem coreShift_comm (a τ z : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) (v i j : V) :
    coreShift G a τ z y σ S v j i = coreShift G a τ z y σ S v i j := by
  have h := (shiftCore_isHermitian G a τ z y σ S v).inv
  have hij : (precCore G a τ y σ S v + z • srcDiag y (S.erase v))⁻¹ j i =
      (precCore G a τ y σ S v + z • srcDiag y (S.erase v))⁻¹ i j := by
    simpa using h.apply i j
  simp only [coreShift, hij]
  ring

theorem trace_shiftY_mul (a τ τ' z : ℝ) (y y' : V → ℝ) (σ : Config V) (S : Finset V) (v : V) :
    (shiftY G a τ z y σ S v * shiftY G a τ' z y' σ S v).trace =
      ∑ i ∈ nbhd G S v, ∑ j ∈ nbhd G S v,
        coreShift G a τ z y σ S v i j * coreShift G a τ' z y' σ S v j i := by
  simp only [trace, diag, mul_apply, shiftY, of_apply]
  rw [← Finset.sum_coe_sort (nbhd G S v)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_coe_sort (nbhd G S v)]

omit [Fintype V] [DecidableEq V] in
theorem greenP_self {a τ : ℝ} {y : V → ℝ} (hy : ∀ i, 0 ≤ y i) (σ : Config V) (S : Finset V)
    (v : V) [Fintype V] [DecidableEq V] :
    greenP G a τ y σ S v v = y v * hN G a τ y σ S v := by
  unfold greenP hN
  rw [show Real.sqrt (y v) * (precN G a τ y σ S)⁻¹ v v * Real.sqrt (y v) =
    (Real.sqrt (y v) * Real.sqrt (y v)) * (precN G a τ y σ S)⁻¹ v v by ring,
    Real.mul_self_sqrt (hy v)]

/-- **Physical form of `Q`** (source lines 1323–1325): `(p-1) E X₁ + p E X₂ = a² Q`. Pointwise,
`X₁ = (a² y_v/D_v)² tr Y₊² (D_v h_v)² = a⁴ G_vv² Σ_{ij} (Y₊)_ij²` (`G_vv = y_v h_v`, `Y₊`
symmetric), and `X₂ = a⁴ G⁺_vv G⁻_vv Σ_{ij} (Y₊)_ij (Y₋)_ij`. -/
theorem shiftQ_eq {S : Finset V} {yp ym : V → ℝ} (hyp : ∀ i, 0 ≤ yp i) (hym : ∀ i, 0 ≤ ym i)
    (v : V) (z : ℝ) :
    ((p : ℝ) - 1) * lawE G p (aOf d p) yp ym S (fun σ => shiftX1 G d p z yp σ S v) +
        p * lawE G p (aOf d p) yp ym S (fun σ => shiftX2 G d p z yp ym σ S v) =
      aOf d p ^ 2 * shiftQ G d p z yp ym S v := by
  have hD1 := diagD_pos G (aOf d p) hyp S v
  have hD2 := diagD_pos G (aOf d p) hym S v
  have hpt : ∀ σ : Config V, ((p : ℝ) - 1) * shiftX1 G d p z yp σ S v +
      p * shiftX2 G d p z yp ym σ S v =
      aOf d p ^ 2 * (aOf d p ^ 2 * (((p : ℝ) - 1) * greenP G (aOf d p) 1 yp σ S v v ^ 2 *
          ∑ i ∈ nbhd G S v, ∑ j ∈ nbhd G S v, coreShift G (aOf d p) 1 z yp σ S v i j ^ 2 +
        p * greenP G (aOf d p) 1 yp σ S v v * greenP G (aOf d p) (-1) ym σ S v v *
          ∑ i ∈ nbhd G S v, ∑ j ∈ nbhd G S v,
            coreShift G (aOf d p) 1 z yp σ S v i j *
              coreShift G (aOf d p) (-1) z ym σ S v i j)) := by
    intro σ
    have e1 : (shiftM G (aOf d p) 1 z yp σ S v * shiftM G (aOf d p) 1 z yp σ S v).trace =
        (aOf d p ^ 2 * yp v / diagD G (aOf d p) yp S v) ^ 2 *
          ∑ i ∈ nbhd G S v, ∑ j ∈ nbhd G S v, coreShift G (aOf d p) 1 z yp σ S v i j ^ 2 := by
      rw [shiftM, Matrix.smul_mul, Matrix.mul_smul, trace_smul, trace_smul, smul_eq_mul,
        smul_eq_mul, trace_shiftY_mul]
      have : ∑ i ∈ nbhd G S v, ∑ j ∈ nbhd G S v,
          coreShift G (aOf d p) 1 z yp σ S v i j * coreShift G (aOf d p) 1 z yp σ S v j i =
          ∑ i ∈ nbhd G S v, ∑ j ∈ nbhd G S v, coreShift G (aOf d p) 1 z yp σ S v i j ^ 2 :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
          rw [coreShift_comm G _ 1 z yp σ S v i j]; ring
      rw [this]; ring
    have e2 : (shiftM G (aOf d p) 1 z yp σ S v * shiftM G (aOf d p) (-1) z ym σ S v).trace =
        (aOf d p ^ 2 * yp v / diagD G (aOf d p) yp S v) *
          (aOf d p ^ 2 * ym v / diagD G (aOf d p) ym S v) *
          ∑ i ∈ nbhd G S v, ∑ j ∈ nbhd G S v,
            coreShift G (aOf d p) 1 z yp σ S v i j * coreShift G (aOf d p) (-1) z ym σ S v i j := by
      rw [shiftM, shiftM, Matrix.smul_mul, Matrix.mul_smul, trace_smul, trace_smul, smul_eq_mul,
        smul_eq_mul, trace_shiftY_mul]
      have : ∑ i ∈ nbhd G S v, ∑ j ∈ nbhd G S v,
          coreShift G (aOf d p) 1 z yp σ S v i j * coreShift G (aOf d p) (-1) z ym σ S v j i =
          ∑ i ∈ nbhd G S v, ∑ j ∈ nbhd G S v,
            coreShift G (aOf d p) 1 z yp σ S v i j * coreShift G (aOf d p) (-1) z ym σ S v i j :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
          rw [coreShift_comm G _ (-1) z ym σ S v i j]
      rw [this]; ring
    simp only [shiftX1, shiftX2, rootT, e1, e2, greenP_self G hyp, greenP_self G hym]
    field_simp
  rw [← lawE_const_mul G, ← lawE_const_mul G, ← lawE_add G]
  unfold shiftQ
  rw [← lawE_const_mul G, ← lawE_const_mul G]
  exact congrArg _ (funext hpt)

end F1

end SecC

end BiluLinial.Tight
