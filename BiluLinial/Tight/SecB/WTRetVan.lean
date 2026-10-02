/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecB.WTBase
public import BiluLinial.Tight.SecB.WTRetCalc
public import BiluLinial.Tight.SecC.TransferRet
public import BiluLinial.Tight.SecA.Reg

/-!
# Vanishing of the retained derivatives at clipped sign vectors (helpers for TB.WT5v)

* `psiW δ`: a smooth function with `psiW δ t = t` for `t ≥ δ/2` and `psiW δ t ≥ δ/4`
  (`Real.smoothTransition`); `adj(M)_kk / psiW δ (det M)` is a global smooth version of
  `(M⁻¹)_kk` on `{det M ≥ δ/2}`.
* `contDiff_det_of_entries`, `contDiff_adjugate_apply_of_entries`, `contDiff_precSub_apply`:
  determinants and adjugate entries of the affine family `x ↦ P̃(x) + zY` are smooth.
* `shiftSub_posDef`: if the core is positive definite and `q_A(x) ≤ 1`, the shifted
  substituted precision `P̃(x) + hY` (`h > 0`) is positive definite at `x` (root Schur
  complement `≥ D_i(1 - q_A(x)) + h y_i > 0`; `y_i = 0` forces `A = 0`).
-/

@[expose] public section

namespace BiluLinial.Tight.SecB

open Matrix
open scoped ContDiff Topology

universe u

section Graph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem contDiff_precSub_apply (a τ : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) (i : V)
    (u w : V) : ContDiff ℝ ∞ fun x : nbhd G S i → ℝ => precSub G a τ y σ S i x u w := by
  simp only [precSub, Matrix.of_apply]
  by_cases h1 : u = i ∧ w ∈ nbhd G S i
  · simp only [dif_pos h1]
    exact contDiff_const.mul (contDiff_apply ℝ ℝ _)
  · simp only [dif_neg h1]
    by_cases h2 : w = i ∧ u ∈ nbhd G S i
    · simp only [dif_pos h2]
      exact contDiff_const.mul (contDiff_apply ℝ ℝ _)
    · simp only [dif_neg h2]
      exact contDiff_const

theorem contDiff_shiftSub_apply (a τ z : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) (i : V)
    (Y : Matrix V V ℝ) (u w : V) :
    ContDiff ℝ ∞ fun x : nbhd G S i → ℝ => (precSub G a τ y σ S i x + z • Y) u w := by
  simp only [Matrix.add_apply]
  exact (contDiff_precSub_apply G a τ y σ S i u w).add contDiff_const

theorem continuous_det_shiftSub (a τ z : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) (i : V)
    (Y : Matrix V V ℝ) :
    Continuous fun x : nbhd G S i → ℝ => (precSub G a τ y σ S i x + z • Y).det :=
  (contDiff_det_of_entries (contDiff_shiftSub_apply G a τ z y σ S i Y)).continuous

/-- The core of `P̃(x) + z Y_S` at `i` is `P̃_core + z Y_{S-i}`. -/
theorem coreOf_shiftSub (a τ z : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) (i : V)
    (x : nbhd G S i → ℝ) :
    SecA.coreOf (precSub G a τ y σ S i x + z • srcDiag y S) i =
      precCore G a τ y σ S i + z • srcDiag y (S.erase i) := by
  ext u w
  by_cases h : u = i ∨ w = i
  · have hY : srcDiag y (S.erase i) u w = 0 := by
      by_cases huw : u = w
      · subst huw
        have hu : u = i := by tauto
        simp [srcDiag, hu]
      · simp [srcDiag, diagonal_apply_ne _ huw]
    simp only [SecA.coreOf, precCore, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, if_pos h, hY, mul_zero, add_zero]
  · obtain ⟨hu, hw⟩ := not_or.1 h
    simp only [SecA.coreOf, precCore, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, if_neg h]
    have hp : precSub G a τ y σ S i x u w = precN G a τ y σ S u w := by
      simp only [precSub, Matrix.of_apply]
      rw [dif_neg (fun h' => hu h'.1), dif_neg (fun h' => hw h'.1)]
    have hY : srcDiag y S u w = srcDiag y (S.erase i) u w := by
      by_cases huw : u = w
      · subst huw
        simp [srcDiag, hu]
      · simp [srcDiag, diagonal_apply_ne _ huw]
    rw [hp, hY]

theorem colOf_shiftSub (a τ z : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) (i : V)
    (x : nbhd G S i → ℝ) :
    SecA.colOf (precSub G a τ y σ S i x + z • srcDiag y S) i =
      SecA.colOf (precSub G a τ y σ S i x) i := by
  funext w
  by_cases hw : w = i
  · simp [SecA.colOf, hw]
  · simp [SecA.colOf, hw, srcDiag]

/-- **Positive definiteness of the shifted substituted precision.** If the core is positive
definite, `y ≥ 0`, `i ∈ S`, `h > 0` and `q_A(x) ≤ 1`, then `P̃(x) + hY_S ≻ 0`. -/
theorem shiftSub_posDef {a τ : ℝ} (hτ : τ ^ 2 = 1) {y : V → ℝ} (hy : ∀ k, 0 ≤ y k)
    (σ : Config V) {S : Finset V} {i : V} (hi : i ∈ S) (x : nbhd G S i → ℝ)
    (hM : (precCore G a τ y σ S i).PosDef) {h : ℝ} (hh : 0 < h)
    (hq : qForm (rootMat G a τ y σ S i) x ≤ 1) :
    (precSub G a τ y σ S i x + h • srcDiag y S).PosDef := by
  have hD : 0 < diagD G a y S i := by
    have h1 : 0 ≤ ∑ j ∈ nbhd G S i, cEdge a y i j := Finset.sum_nonneg fun j _ =>
      FloorIns.cRoot_nonneg (mul_nonneg (mul_nonneg (sq_nonneg a) (hy i)) (hy j))
    unfold diagD
    linarith
  have hY' : (srcDiag y (S.erase i)).PosSemidef := SecA.srcDiag_posSemidef hy _
  have hC : (SecA.coreOf (precSub G a τ y σ S i x + h • srcDiag y S) i).PosDef := by
    rw [coreOf_shiftSub]
    exact hM.add_posSemidef (hY'.smul hh.le)
  have hherm : (precSub G a τ y σ S i x + h • srcDiag y S).IsHermitian :=
    (precSub_isHermitian G a τ y σ S i x).add
      ((SecA.srcDiag_posSemidef hy S).smul hh.le).isHermitian
  obtain ⟨h1, -⟩ := ins_generic hherm hC
  rw [h1, coreOf_shiftSub, colOf_shiftSub]
  have hvv : (precSub G a τ y σ S i x + h • srcDiag y S) i i = diagD G a y S i + h * y i := by
    simp [precSub_apply_root G hi, srcDiag, hi]
  rw [hvv]
  have hquad := colOf_precSub_quad G (a := a) hτ hy σ x
  have hineq := SecA.quad_inv_sub_inv_add_ge hM hY' hh.le
    (SecA.colOf (precSub G a τ y σ S i x) i)
  have hw0 : 0 ≤ h * (((precCore G a τ y σ S i + h • srcDiag y (S.erase i))⁻¹ *ᵥ
      SecA.colOf (precSub G a τ y σ S i x) i) ⬝ᵥ (srcDiag y (S.erase i) *ᵥ
        ((precCore G a τ y σ S i + h • srcDiag y (S.erase i))⁻¹ *ᵥ
          SecA.colOf (precSub G a τ y σ S i x) i))) :=
    mul_nonneg hh.le (by
      have := hY'.dotProduct_mulVec_nonneg
        ((precCore G a τ y σ S i + h • srcDiag y (S.erase i))⁻¹ *ᵥ
          SecA.colOf (precSub G a τ y σ S i x) i)
      simpa only [star_trivial] using this)
  rw [hquad] at hineq
  by_cases hyi : y i = 0
  · have hA : rootMat G a τ y σ S i = 0 := by
      ext s t
      simp [rootMat, hyi]
    rw [hA] at hineq
    simp only [qForm, Matrix.zero_mulVec, dotProduct_zero, mul_zero, zero_sub] at hineq
    nlinarith
  · have hyi' : 0 < y i := lt_of_le_of_ne (hy i) (Ne.symm hyi)
    nlinarith [mul_pos hh hyi', mul_nonneg hD.le (sub_nonneg.2 hq)]

end Graph

/-! ### The clipped form of the normalized observables near a boundary point -/

section Contact

variable {d p : ℕ} (ct : Contact.{u} d p)

/-- The branch precision `P̃^b(x)`. -/
noncomputable abbrev brP (σ : Config ct.V) (i : ct.V) (b : Bool) (x : nbhd ct.G ct.S i → ℝ) :
    Matrix ct.V ct.V ℝ :=
  precSub ct.G (aOf d p) (if b then 1 else -1) (ct.ySrc b) σ ct.S i x

/-- The shifted branch precision `P̃^b(x) + hY^b`. -/
noncomputable abbrev brQ (h : ℝ) (σ : Config ct.V) (i : ct.V) (b : Bool)
    (x : nbhd ct.G ct.S i → ℝ) : Matrix ct.V ct.V ℝ :=
  brP ct σ i b x + h • srcDiag (ct.ySrc b) ct.S

/-- A global smooth version of `D g_t` near a point where `det(P̃^b + hY^b) > δ/2`. -/
noncomputable def gamT (h δ : ℝ) (σ : Config ct.V) (i : ct.V) (t : ct.V × Bool × Bool)
    (x : nbhd ct.G ct.S i → ℝ) : ℝ :=
  if t.2.2 then wtDet ct σ i x * (ct.ySrc t.2.1 t.1 * (brQ ct h σ i t.2.1 x).adjugate t.1 t.1 /
    psiW δ (brQ ct h σ i t.2.1 x).det)
  else (brP ct σ i (!t.2.1) x).det * (ct.ySrc t.2.1 t.1 * (brP ct σ i t.2.1 x).adjugate t.1 t.1)

theorem contDiff_wtDet (σ : Config ct.V) (i : ct.V) : ContDiff ℝ ∞ (wtDet ct σ i) := by
  unfold wtDet
  exact (contDiff_det_of_entries (contDiff_precSub_apply ct.G _ _ _ σ ct.S i)).mul
    (contDiff_det_of_entries (contDiff_precSub_apply ct.G _ _ _ σ ct.S i))

theorem contDiff_gamT (h : ℝ) {δ : ℝ} (hδ : 0 < δ) (σ : Config ct.V) (i : ct.V)
    (t : ct.V × Bool × Bool) : ContDiff ℝ ∞ (gamT ct h δ σ i t) := by
  unfold gamT
  have hQ : ∀ b, ∀ u w, ContDiff ℝ ∞ fun x => brQ ct h σ i b x u w := fun b u w =>
    contDiff_shiftSub_apply ct.G _ _ h _ σ ct.S i _ u w
  have hP : ∀ b, ∀ u w, ContDiff ℝ ∞ fun x => brP ct σ i b x u w := fun b u w =>
    contDiff_precSub_apply ct.G _ _ _ σ ct.S i u w
  split_ifs
  · refine (contDiff_wtDet ct σ i).mul ?_
    refine ContDiff.div (contDiff_const.mul (contDiff_adjugate_apply_of_entries (hQ _) _ _))
      ((contDiff_psiW δ).comp (contDiff_det_of_entries (hQ _))) fun x => (psiW_pos hδ _).ne'
  · exact (contDiff_det_of_entries (hP _)).mul
      (contDiff_const.mul (contDiff_adjugate_apply_of_entries (hP _) _ _))

/-- On the support, where `det(P̃^b + hY^b) ≥ δ/2` for the shifted factors, `gamT = D g_t`. -/
theorem gamT_eq {h δ : ℝ} (hδ : 0 < δ) {σ : Config ct.V} {i : ct.V} (t : ct.V × Bool × Bool)
    {x : nbhd ct.G ct.S i → ℝ} (hx : x ∈ wtSupp ct σ i)
    (hQ : t.2.2 = true → δ / 2 ≤ (brQ ct h σ i t.2.1 x).det) :
    gamT ct h δ σ i t x = wtDet ct σ i x * wtDiag ct h i σ t x := by
  obtain ⟨k, b, sh⟩ := t
  have hx' : (precSub ct.G (aOf d p) 1 ct.yp σ ct.S i x).PosDef ∧
      (precSub ct.G (aOf d p) (-1) ct.ym σ ct.S i x).PosDef := hx
  have hPb : (brP ct σ i b x).PosDef := by
    cases b
    · simpa [brP, Contact.ySrc] using hx'.2
    · simpa [brP, Contact.ySrc] using hx'.1
  have hD : wtDet ct σ i x = (brP ct σ i b x).det * (brP ct σ i (!b) x).det := by
    cases b <;> simp [wtDet, brP, Contact.ySrc, mul_comm]
  cases sh
  · simp only [gamT, wtDiag, diagSub, Bool.false_eq_true, ↓reduceIte, zero_smul, add_zero]
    rw [hD]
    have e : precSub ct.G (aOf d p) (if b = true then 1 else -1) (ct.ySrc b) σ ct.S i x =
        brP ct σ i b x := rfl
    rw [e, inv_apply_eq_adjugate_div hPb.det_pos.ne']
    field_simp [hPb.det_pos.ne']
  · have hdet := hQ rfl
    have hpos : 0 < (brQ ct h σ i b x).det := lt_of_lt_of_le (by linarith) hdet
    simp only [gamT, wtDiag, diagSub, ↓reduceIte]
    have e : precSub ct.G (aOf d p) (if b = true then 1 else -1) (ct.ySrc b) σ ct.S i x +
        h • srcDiag (ct.ySrc b) ct.S = brQ ct h σ i b x := rfl
    rw [e, psiW_eq hδ hdet, inv_apply_eq_adjugate_div hpos.ne']
    ring

theorem contDiff_list_prod_map {ι α : Type*} [Fintype ι] (L : List α)
    (f : α → (ι → ℝ) → ℝ) (hf : ∀ t ∈ L, ContDiff ℝ ∞ (f t)) :
    ContDiff ℝ ∞ fun x => (L.map fun t => f t x).prod := by
  induction L with
  | nil => simpa using contDiff_const
  | cons t L ih =>
    simp only [List.map_cons, List.prod_cons]
    exact (hf t List.mem_cons_self).mul (ih fun t' ht' => hf t' (List.mem_cons_of_mem _ ht'))

/-- **TB.WT5v at one signing.** If `Φ(ξ) = 0` and the derivative order is `< p - |L|`, the
derivative of both normalized observables vanishes at `ξ` (`ξ` need not be a sign vector). -/
theorem starObs_dEven_eq_zero {h : ℝ} (hh : 0 < h) (e dir : Bool) {i : ct.V} (hi : i ∈ ct.S)
    (l : List (ct.V × Bool × Bool)) (hl : l.length + 4 ≤ p) (σ : Config ct.V)
    (j : nbhd ct.G ct.S i → ℕ)
    (hlen : (dEvenList (lJ ct i) j).length < p - (l.length + 4))
    (ξ : nbhd ct.G ct.S i → ℝ) (hΦ : starPhi p (rootA ct σ i) (rootB ct σ i) ξ = 0) :
    dEven (lJ ct i) j (starObsQ ct h e dir i l σ) ξ = 0 ∧
      dEven (lJ ct i) j (starObsT ct h e dir i l σ) ξ = 0 := by
  have hyp : ∀ k, 0 ≤ ct.yp k := fun k => (ct.ctx.hyp k).1
  have hym : ∀ k, 0 ≤ ct.ym k := fun k => (ct.ctx.hym k).1
  have hp1 : 1 ≤ p := le_trans (by omega) hl
  rw [dEven_eq_pderivList, dEven_eq_pderivList]
  set lst := dEvenList (lJ ct i) j with hlst
  set E := p - (l.length + 4) with hE
  have hE1 : 1 ≤ E := by omega
  by_cases hc : wtCore ct.G p (aOf d p) ct.yp ct.ym σ ct.S i = 0
  · have h0 : starObsQ ct h e dir i l σ = fun _ => 0 := by
      unfold starObsQ
      rw [if_neg (not_not.2 hc)]
    have h0' : starObsT ct h e dir i l σ = fun _ => 0 := by
      unfold starObsT
      rw [if_neg (not_not.2 hc)]
    rw [h0, h0', SecC.pderivList_const_zero]
    exact ⟨rfl, rfl⟩
  have hM : (precCore ct.G (aOf d p) 1 ct.yp σ ct.S i).PosDef ∧
      (precCore ct.G (aOf d p) (-1) ct.ym σ ct.S i).PosDef := by
    by_contra hn
    exact hc (by unfold wtCore; rw [if_neg hn])
  have hA := (SecC.shift_branch ct.G hyp le_rfl one_pos hM.1).1
  have hB := (SecC.shift_branch ct.G hym le_rfl one_pos hM.2).1
  -- the root quadratic forms at `ξ`
  have hq1 : 1 ≤ qForm (rootA ct σ i) ξ ∨ 1 ≤ qForm (rootB ct σ i) ξ := by
    unfold starPhi at hΦ
    rcases mul_eq_zero.1 hΦ with h1 | h1
    · left
      have := pow_eq_zero_iff (n := p) (by omega) |>.1 h1
      unfold clipF at this
      by_contra hn
      push_neg at hn
      have : 0 < 1 - qForm (rootA ct σ i) ξ := by linarith
      linarith [le_max_left (1 - qForm (rootA ct σ i) ξ) 0]
    · right
      have := pow_eq_zero_iff (n := p) (by omega) |>.1 h1
      unfold clipF at this
      by_contra hn
      push_neg at hn
      have : 0 < 1 - qForm (rootB ct σ i) ξ := by linarith
      linarith [le_max_left (1 - qForm (rootB ct σ i) ξ) 0]
  -- off the boundary the observables vanish near `ξ`
  have hstar0 : ∀ x, (1 ≤ qForm (rootA ct σ i) x ∨ 1 ≤ qForm (rootB ct σ i) x) →
      starPhi p (rootA ct σ i) (rootB ct σ i) x = 0 := by
    intro x hx
    unfold starPhi clipF
    rcases hx with hx | hx
    · rw [show max (1 - qForm (rootA ct σ i) x) 0 = 0 from max_eq_right (by linarith),
        zero_pow (by omega), zero_mul]
    · rw [show max (1 - qForm (rootB ct σ i) x) 0 = 0 from max_eq_right (by linarith),
        zero_pow (by omega), mul_zero]
  have hobs0 : ∀ x, starPhi p (rootA ct σ i) (rootB ct σ i) x = 0 →
      starObsQ ct h e dir i l σ x = 0 ∧ starObsT ct h e dir i l σ x = 0 := by
    intro x hx
    unfold starObsQ starObsT
    simp only [if_pos hc, hx, zero_mul, mul_zero, and_self]
  by_cases hgt : 1 < qForm (rootA ct σ i) ξ ∨ 1 < qForm (rootB ct σ i) ξ
  · have hO : ∀ᶠ x in 𝓝 ξ, 1 < qForm (rootA ct σ i) x ∨ 1 < qForm (rootB ct σ i) x := by
      rcases hgt with hg | hg
      · have h1 : ∀ᶠ x in 𝓝 ξ, 1 < qForm (rootA ct σ i) x :=
          (isOpen_lt continuous_const (continuous_qForm _)).mem_nhds hg
        exact h1.mono fun x hx => Or.inl hx
      · have h1 : ∀ᶠ x in 𝓝 ξ, 1 < qForm (rootB ct σ i) x :=
          (isOpen_lt continuous_const (continuous_qForm _)).mem_nhds hg
        exact h1.mono fun x hx => Or.inr hx
    have hevQ : starObsQ ct h e dir i l σ =ᶠ[𝓝 ξ] fun _ => 0 := hO.mono fun x hx =>
      (hobs0 x (hstar0 x (hx.imp le_of_lt le_of_lt))).1
    have hevT : starObsT ct h e dir i l σ =ᶠ[𝓝 ξ] fun _ => 0 := hO.mono fun x hx =>
      (hobs0 x (hstar0 x (hx.imp le_of_lt le_of_lt))).2
    rw [(SecA.StarCalc.pderivList_congr_nhds hevQ lst).eq_of_nhds,
      (SecA.StarCalc.pderivList_congr_nhds hevT lst).eq_of_nhds, SecC.pderivList_const_zero]
    exact ⟨rfl, rfl⟩
  push_neg at hgt
  -- the boundary case: the shifted precisions are positive definite at `ξ`
  have hQp : (brQ ct h σ i true ξ).PosDef := by
    simpa [brQ, brP, Contact.ySrc] using shiftSub_posDef ct.G (a := aOf d p) (τ := 1)
      (by norm_num) hyp σ hi ξ hM.1 hh hgt.1
  have hQm : (brQ ct h σ i false ξ).PosDef := by
    simpa [brQ, brP, Contact.ySrc] using shiftSub_posDef ct.G (a := aOf d p) (τ := -1)
      (by norm_num) hym σ hi ξ hM.2 hh hgt.2
  set δ := min (brQ ct h σ i true ξ).det (brQ ct h σ i false ξ).det with hδdef
  have hδ : 0 < δ := lt_min hQp.det_pos hQm.det_pos
  have hU : ∀ᶠ x in 𝓝 ξ, δ / 2 < (brQ ct h σ i true x).det ∧
      δ / 2 < (brQ ct h σ i false x).det := by
    have h1 : δ / 2 < (brQ ct h σ i true ξ).det := by
      have := min_le_left (brQ ct h σ i true ξ).det (brQ ct h σ i false ξ).det
      linarith
    have h2 : δ / 2 < (brQ ct h σ i false ξ).det := by
      have := min_le_right (brQ ct h σ i true ξ).det (brQ ct h σ i false ξ).det
      linarith
    have e1 : ∀ᶠ x in 𝓝 ξ, δ / 2 < (brQ ct h σ i true x).det :=
      (isOpen_lt continuous_const (continuous_det_shiftSub ct.G _ _ h _ σ ct.S i _)).mem_nhds h1
    have e2 : ∀ᶠ x in 𝓝 ξ, δ / 2 < (brQ ct h σ i false x).det :=
      (isOpen_lt continuous_const (continuous_det_shiftSub ct.G _ _ h _ σ ct.S i _)).mem_nhds h2
    exact e1.and e2
  -- the clipped form
  obtain ⟨-, hdA⟩ := precSub_ins ct.G (a := aOf d p) (τ := 1) (by norm_num) hyp σ hi ξ hM.1
  set cW := ((precCore ct.G (aOf d p) 1 ct.yp σ ct.S i).det * diagD ct.G (aOf d p) ct.yp ct.S i) *
    ((precCore ct.G (aOf d p) (-1) ct.ym σ ct.S i).det * diagD ct.G (aOf d p) ct.ym ct.S i)
    with hcW
  have hDet : ∀ x, wtDet ct σ i x = cW * (1 - qForm (rootA ct σ i) x) *
      (1 - qForm (rootB ct σ i) x) := by
    intro x
    obtain ⟨-, h1⟩ := precSub_ins ct.G (a := aOf d p) (τ := 1) (by norm_num) hyp σ hi x hM.1
    obtain ⟨-, h2⟩ := precSub_ins ct.G (a := aOf d p) (τ := -1) (by norm_num) hym σ hi x hM.2
    unfold wtDet
    rw [h1, h2]
    ring
  set L' := l ++ [(i, e, true), (i, e, true), (i, true, true), (i, true, true)] with hL'
  set C₀ := cW ^ E / (wtCore ct.G p (aOf d p) ct.yp ct.ym σ ct.S i * dPow ct i) with hC₀
  set Γ : (nbhd ct.G ct.S i → ℝ) → ℝ := fun x => (L'.map fun t => gamT ct h δ σ i t x).prod
    with hΓ
  have hΓc : ContDiff ℝ ∞ Γ :=
    contDiff_list_prod_map L' _ fun t _ => contDiff_gamT ct h hδ σ i t
  have hcd : wtCore ct.G p (aOf d p) ct.yp ct.ym σ ct.S i * dPow ct i ≠ 0 :=
    mul_ne_zero hc (dPow_pos ct i).ne'
  -- the identity on the support near `ξ`
  have hrep : ∀ x, δ / 2 < (brQ ct h σ i true x).det → δ / 2 < (brQ ct h σ i false x).det →
      starPhi p (rootA ct σ i) (rootB ct σ i) x * wtHSub ct h e i l σ x =
        C₀ * Γ x * clipF (rootA ct σ i) x ^ E * clipF (rootB ct σ i) x ^ E := by
    intro x hx1 hx2
    by_cases hx : x ∈ wtSupp ct σ i
    · have hx' : (precSub ct.G (aOf d p) 1 ct.yp σ ct.S i x).PosDef ∧
          (precSub ct.G (aOf d p) (-1) ct.ym σ ct.S i x).PosDef := hx
      have hqA : qForm (rootA ct σ i) x < 1 :=
        ((precSub_ins ct.G (a := aOf d p) (τ := 1) (by norm_num) hyp σ hi x hM.1).1).1 hx'.1
      have hqB : qForm (rootB ct σ i) x < 1 :=
        ((precSub_ins ct.G (a := aOf d p) (τ := -1) (by norm_num) hym σ hi x hM.2).1).1 hx'.2
      have hw := wSub_eq_star ct.G hp1 (aOf d p) hyp hym σ hi x
      have h3 := wt3Rho_eq_of_mem ct (h := h) e i l hl hx
      unfold wt3Rho at h3
      rw [hw] at h3
      have hprod : (L'.map fun t => wtDet ct σ i x * wtDiag ct h i σ t x).prod = Γ x := by
        simp only [hΓ]
        congr 1
        refine List.map_congr_left fun t _ => (gamT_eq ct hδ t hx fun _ => ?_).symm
        rcases t with ⟨k, b, sh⟩
        cases b
        · exact hx2.le
        · exact hx1.le
      rw [hprod, hDet x, ← hE] at h3
      have key : starPhi p (rootA ct σ i) (rootB ct σ i) x * wtHSub ct h e i l σ x =
          (cW * (1 - qForm (rootA ct σ i) x) * (1 - qForm (rootB ct σ i) x)) ^ E * Γ x /
            (wtCore ct.G p (aOf d p) ct.yp ct.ym σ ct.S i * dPow ct i) := by
        rw [eq_div_iff hcd, ← h3]
        ring
      rw [key, clipF_eq_of_lt hqA, clipF_eq_of_lt hqB, hC₀, mul_pow, mul_pow]
      field_simp
    · have hq : 1 ≤ qForm (rootA ct σ i) x ∨ 1 ≤ qForm (rootB ct σ i) x := by
        by_contra hn
        push_neg at hn
        exact hx ⟨((precSub_ins ct.G (a := aOf d p) (τ := 1) (by norm_num) hyp σ hi x
          hM.1).1).2 hn.1, ((precSub_ins ct.G (a := aOf d p) (τ := -1) (by norm_num) hym σ hi
          x hM.2).1).2 hn.2⟩
      rw [hstar0 x hq, zero_mul]
      rcases hq with hq | hq
      · rw [show clipF (rootA ct σ i) x = 0 from max_eq_right (by linarith), zero_pow (by omega)]
        ring
      · rw [show clipF (rootB ct σ i) x = 0 from max_eq_right (by linarith), zero_pow (by omega)]
        ring
  have hlen' : lst.length < min E E := by rw [min_self]; exact hlen
  constructor
  · have hev : starObsQ ct h e dir i l σ =ᶠ[𝓝 ξ]
        clipObs (fun x => C₀ * Γ x * qForm (kerL ct h e dir i σ) x) E E (rootA ct σ i)
          (rootB ct σ i) := hU.mono fun x hx => by
      unfold starObsQ clipObs
      simp only [if_pos hc]
      rw [← mul_assoc, hrep x hx.1 hx.2]
      ring
    rw [(SecA.StarCalc.pderivList_congr_nhds hev lst).eq_of_nhds]
    exact SecA.pderivList_clipObs_eq_zero hA hB
      ((contDiff_const.mul hΓc).mul (SecA.StarCalc.contDiff_qForm _)) lst hlen' hq1
  · have hev : starObsT ct h e dir i l σ =ᶠ[𝓝 ξ]
        clipObs (fun x => (kerL ct h e dir i σ).trace * (C₀ * Γ x)) E E (rootA ct σ i)
          (rootB ct σ i) := hU.mono fun x hx => by
      unfold starObsT clipObs
      simp only [if_pos hc]
      rw [hrep x hx.1 hx.2]
      ring
    rw [(SecA.StarCalc.pderivList_congr_nhds hev lst).eq_of_nhds]
    exact SecA.pderivList_clipObs_eq_zero hA hB (contDiff_const.mul (contDiff_const.mul hΓc))
      lst hlen' hq1

end Contact

end BiluLinial.Tight.SecB
