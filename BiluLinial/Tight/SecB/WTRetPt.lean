/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecB.WTRetVan
public import BiluLinial.Tight.SecB.LawE

/-!
# The retained WT derivatives at a supported signing (helpers for TB.WT5l)

At a supported signing `σ` the star vector `ξ` is interior, and near `ξ`
`F_Q = Φ̃ H̃ q_L`, `F_T = tr L · Φ̃ H̃` with `Φ̃ = (1 - q_A)^p (1 - q_B)^p` and
`H̃ = Π_{t ∈ L'} y_k (M_t⁻¹)_kk` (`M_t = P̃^b(x) + z Y^b`). Then

* `Φ̃` is `MajAt` with scale `α^p β^p`, constant `4p` and weights `λ = lamR` (A-MAJ via
  `SecC.branch_majorant`);
* each inverse entry has rising-factorial derivative bounds (`invSm_deriv_le`) with weights
  `2a √(y_i X_ii) √(y_s X_ss) ≤ λ_s` (shifting decreases the inverse diagonal);
* `quad_leibniz` handles the quadratic factor `q_L`.

`starObs_pointwise`: if `(4p + |L'| + N) λ_s ≤ κ` for all `s` and `2Σj ≤ N`,
`|∂^{2j}F_Q(ξ)|/Φ(ξ) + |∂^{2j}F_T(ξ)|/Φ(ξ) ≤ H κ^{2Σj} (q_L + qd1_j/κ + qd2_j/κ² + tr L)`.
-/

@[expose] public section

namespace BiluLinial.Tight.SecB

open Matrix SecA.StarCalc
open scoped ContDiff Topology

universe u

section Coord

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem pderiv_coord_affine (c k : ℝ) (t s : ι) :
    pderiv s (fun x : ι → ℝ => c * x t + k) = fun _ => c * (if t = s then 1 else 0) := by
  funext x
  have h : HasFDerivAt (fun x : ι → ℝ => c * x t + k) (c • ContinuousLinearMap.proj t) x :=
    ((hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : ι => ℝ) t x).const_mul c).add_const k
  simp only [pderiv, h.fderiv, ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply,
    smul_eq_mul, Pi.single_apply]

omit [Fintype ι] in
theorem pderiv_const' (k : ℝ) (s : ι) : pderiv s (fun _ : ι → ℝ => k) = fun _ => 0 := by
  funext x
  simp [pderiv]

/-- `K^{|l|} Π_{s ∈ l} λ_s ≤ κ^{|l|}` when `K λ_s ≤ κ`. -/
theorem pow_mul_prod_le {K κ : ℝ} {lam : ι → ℝ} (hK : 0 ≤ K) (hlam : ∀ s, 0 ≤ lam s)
    (h : ∀ s, K * lam s ≤ κ) : ∀ l : List ι, K ^ l.length * (l.map lam).prod ≤ κ ^ l.length
  | [] => by simp
  | s :: l => by
    have ih := pow_mul_prod_le hK hlam h l
    simp only [List.length_cons, List.map_cons, List.prod_cons, pow_succ]
    have h0 : 0 ≤ K ^ l.length * (l.map lam).prod :=
      mul_nonneg (pow_nonneg hK _) (prod_map_nonneg' hlam l)
    have h1 : 0 ≤ K * lam s := mul_nonneg hK (hlam s)
    calc K ^ l.length * K * (lam s * (l.map lam).prod)
        = (K * lam s) * (K ^ l.length * (l.map lam).prod) := by ring
      _ ≤ κ * κ ^ l.length := mul_le_mul (h s) ih h0 (h1.trans (h s))
      _ = κ ^ l.length * κ := by ring

theorem list_prod_map_le {f g : ι → ℝ} (h0 : ∀ s, 0 ≤ f s) (h : ∀ s, f s ≤ g s) :
    ∀ l : List ι, (l.map f).prod ≤ (l.map g).prod
  | [] => le_rfl
  | s :: l => by
    simp only [List.map_cons, List.prod_cons]
    exact mul_le_mul (h s) (list_prod_map_le h0 h l) (prod_map_nonneg' h0 l) ((h0 s).trans (h s))

end Coord

section Graph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The derivative of an entry of `P̃(x) + z Y` in the star coordinate `x_s`. -/
theorem pderiv_shiftSub_apply (a τ z : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) (i : V)
    (Y : Matrix V V ℝ) (s : nbhd G S i) (u w : V) :
    pderiv s (fun x => (precSub G a τ y σ S i x + z • Y) u w) = fun _ =>
      τ * a * (Real.sqrt (y i) * Real.sqrt (y s)) *
        ((if u = i ∧ w = (s : V) then 1 else 0) + (if u = (s : V) ∧ w = i then 1 else 0)) := by
  have hsi : (s : V) ≠ i := nbhd_ne_self G s.2
  by_cases h1 : u = i ∧ w ∈ nbhd G S i
  · have hf : (fun x => (precSub G a τ y σ S i x + z • Y) u w) = fun x =>
        τ * a * (Real.sqrt (y u) * Real.sqrt (y w)) * x ⟨w, h1.2⟩ + (z • Y) u w := by
      funext x
      simp only [Matrix.add_apply, precSub, Matrix.of_apply, dif_pos h1]
    rw [hf, pderiv_coord_affine]
    funext _
    obtain ⟨rfl, hw⟩ := h1
    have hwi : w ≠ u := nbhd_ne_self G hw
    by_cases hws : w = (s : V)
    · have e : (⟨w, hw⟩ : nbhd G S u) = s := Subtype.ext hws
      subst hws
      simp [e, hsi]
    · have e : (⟨w, hw⟩ : nbhd G S u) ≠ s := fun h => hws (congrArg Subtype.val h)
      simp [e, hws, hwi]
  · by_cases h2 : w = i ∧ u ∈ nbhd G S i
    · have hf : (fun x => (precSub G a τ y σ S i x + z • Y) u w) = fun x =>
          τ * a * (Real.sqrt (y u) * Real.sqrt (y w)) * x ⟨u, h2.2⟩ + (z • Y) u w := by
        funext x
        simp only [Matrix.add_apply, precSub, Matrix.of_apply, dif_neg h1, dif_pos h2]
      rw [hf, pderiv_coord_affine]
      funext _
      obtain ⟨rfl, hu⟩ := h2
      have hui : u ≠ w := nbhd_ne_self G hu
      by_cases hus : u = (s : V)
      · have e : (⟨u, hu⟩ : nbhd G S w) = s := Subtype.ext hus
        subst hus
        simp only [e, ↓reduceIte, hsi, false_and, and_true]
        ring
      · have e : (⟨u, hu⟩ : nbhd G S w) ≠ s := fun h => hus (congrArg Subtype.val h)
        simp [e, hus, hui]
    · have hf : (fun x => (precSub G a τ y σ S i x + z • Y) u w) = fun _ =>
          precN G a τ y σ S u w + (z • Y) u w := by
        funext x
        simp only [Matrix.add_apply, precSub, Matrix.of_apply, dif_neg h1, dif_neg h2]
      rw [hf, pderiv_const']
      funext _
      have hA : ¬(u = i ∧ w = (s : V)) := fun h => h1 ⟨h.1, h.2 ▸ s.2⟩
      have hB : ¬(u = (s : V) ∧ w = i) := fun h => h2 ⟨h.2, h.1 ▸ s.2⟩
      simp [hA, hB]

end Graph

section Contact

variable {d p : ℕ} (ct : Contact.{u} d p)

/-- `H = Π_{t ∈ L'} g_t` with `L' = H₀ ++ [(i,e,+sh), (i,e,+sh), (i,+,+sh), (i,+,+sh)]`. -/
theorem wtHSub_eq_prod (h : ℝ) (e : Bool) (i : ct.V) (l : List (ct.V × Bool × Bool))
    (σ : Config ct.V) (x : nbhd ct.G ct.S i → ℝ) :
    wtHSub ct h e i l σ x =
      ((l ++ [(i, e, true), (i, e, true), (i, true, true), (i, true, true)]).map fun t =>
        wtDiag ct h i σ t x).prod := by
  have hH : wtHSub ct h e i l σ x = (l.map fun t => wtDiag ct h i σ t x).prod *
      wtDiag ct h i σ (i, e, true) x ^ 2 * wtDiag ct h i σ (i, true, true) x ^ 2 := by
    simp only [wtHSub, diagWSub, wtDiag, Contact.ySrc, ↓reduceIte]
  rw [hH]
  simp only [List.map_append, List.prod_append, List.map_cons, List.prod_cons, List.map_nil,
    List.prod_nil]
  ring

/-- The matrix `P̃^b(x) + z Y^b` of a diagonal factor (`z = h` if shifted, else `0`). -/
noncomputable abbrev facM (h : ℝ) (σ : Config ct.V) (i : ct.V) (b sh : Bool)
    (x : nbhd ct.G ct.S i → ℝ) : Matrix ct.V ct.V ℝ :=
  precSub ct.G (aOf d p) (if b then 1 else -1) (ct.ySrc b) σ ct.S i x +
    (if sh then h else 0) • srcDiag (ct.ySrc b) ct.S

theorem wtDiag_eq_facM (h : ℝ) (i : ct.V) (σ : Config ct.V) (t : ct.V × Bool × Bool)
    (x : nbhd ct.G ct.S i → ℝ) :
    wtDiag ct h i σ t x = ct.ySrc t.2.1 t.1 * (facM ct h σ i t.2.1 t.2.2 x)⁻¹ t.1 t.1 := rfl

theorem rootSigns_pm (σ : Config ct.V) (i : ct.V) (s : nbhd ct.G ct.S i) :
    rootSigns ct.G σ ct.S i s = 1 ∨ rootSigns ct.G σ ct.S i s = -1 :=
  mul_self_eq_one_iff.1 (FloorIns.sgn_mul_self σ i s)

theorem ySrc_nonneg' (b : Bool) (k : ct.V) : 0 ≤ ct.ySrc b k := ySrc_nonneg ct b k

/-- At the star vector of a supported signing, `facM = P^b + zY^b` is positive definite and its
inverse diagonal is at most `h^b_k`. -/
theorem facM_root {h : ℝ} (hh : 0 ≤ h) {i : ct.V} (hi : i ∈ ct.S) {σ : Config ct.V}
    (hσ : wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0) (b sh : Bool) :
    (facM ct h σ i b sh (rootSigns ct.G σ ct.S i)).PosDef ∧
      ∀ k, (facM ct h σ i b sh (rootSigns ct.G σ ct.S i))⁻¹ k k ≤
        hN ct.G (aOf d p) (if b then 1 else -1) (ct.ySrc b) σ ct.S k := by
  have hP : (precN ct.G (aOf d p) (if b then 1 else -1) (ct.ySrc b) σ ct.S).PosDef := by
    obtain ⟨h1, h2⟩ := posDef_of_wt_ne_zero ct.G hσ
    cases b
    · simpa [Contact.ySrc] using h2
    · simpa [Contact.ySrc] using h1
  have he : facM ct h σ i b sh (rootSigns ct.G σ ct.S i) =
      precN ct.G (aOf d p) (if b then 1 else -1) (ct.ySrc b) σ ct.S +
        (if sh then h else 0) • srcDiag (ct.ySrc b) ct.S := by
    simp only [facM]
    rw [precSub_setRoot ct.G _ _ _ σ hi (rootSigns_pm ct σ i), setRoot_rootSigns]
  have hz : 0 ≤ (if sh then h else 0) := by split_ifs <;> simp [hh]
  have hD := posSemidef_smul_srcDiag (fun k => ySrc_nonneg ct b k) ct.S hz
  rw [he]
  exact ⟨hP.add_posSemidef hD, fun k => inv_diag_add_le hP hD k⟩

/-- The derivative weights of the inverse entries of `facM` are at most `λ_s = lamR_s`:
`2 a √(y_i y_s) √(X_ii X_ss) ≤ 2a √(G_ii G_ss) ≤ λ_s`. -/
theorem facM_weight_le (hR : TRegime d p) {h : ℝ} (hh : 0 ≤ h) {i : ct.V} (hi : i ∈ ct.S)
    {σ : Config ct.V} (hσ : wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0) (b sh : Bool)
    (s : nbhd ct.G ct.S i) :
    2 * |(if b then 1 else -1) * aOf d p * (Real.sqrt (ct.ySrc b i) * Real.sqrt (ct.ySrc b s))| *
        (Real.sqrt ((facM ct h σ i b sh (rootSigns ct.G σ ct.S i))⁻¹ i i) *
          Real.sqrt ((facM ct h σ i b sh (rootSigns ct.G σ ct.S i))⁻¹ s s)) ≤
      SecC.lamR ct.G (aOf d p) ct.yp ct.ym σ ct.S i s := by
  have ha := hR.aOf_pos
  obtain ⟨hPD, hX⟩ := facM_root ct hh hi hσ b sh
  set X := (facM ct h σ i b sh (rootSigns ct.G σ ct.S i))⁻¹ with hXdef
  have hy : ∀ k, 0 ≤ ct.ySrc b k := fun k => ySrc_nonneg ct b k
  have hc : |(if b then 1 else -1) * aOf d p * (Real.sqrt (ct.ySrc b i) *
      Real.sqrt (ct.ySrc b s))| = aOf d p * (Real.sqrt (ct.ySrc b i) * Real.sqrt (ct.ySrc b s)) := by
    rw [abs_mul, abs_mul, abs_of_pos ha, abs_of_nonneg (by positivity : (0 : ℝ) ≤
      Real.sqrt (ct.ySrc b i) * Real.sqrt (ct.ySrc b s))]
    split_ifs <;> simp
  have key : ∀ k, Real.sqrt (ct.ySrc b k) * Real.sqrt (X k k) ≤
      Real.sqrt (greenP ct.G (aOf d p) (if b then 1 else -1) (ct.ySrc b) σ ct.S k k) := by
    intro k
    rw [← Real.sqrt_mul (hy k), SecC.greenP_self ct.G hy σ ct.S k]
    exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (hX k) (hy k))
  have hG0 : ∀ k, 0 ≤ greenP ct.G (aOf d p) (if b then 1 else -1) (ct.ySrc b) σ ct.S k k := by
    intro k
    rw [SecC.greenP_self ct.G hy σ ct.S k]
    exact mul_nonneg (hy k) (le_trans hPD.inv.diag_pos.le (hX k))
  have h2 : Real.sqrt (ct.ySrc b i) * Real.sqrt (X (i : ct.V) i) *
      (Real.sqrt (ct.ySrc b s) * Real.sqrt (X s s)) ≤
      Real.sqrt (greenP ct.G (aOf d p) (if b then 1 else -1) (ct.ySrc b) σ ct.S i i *
        greenP ct.G (aOf d p) (if b then 1 else -1) (ct.ySrc b) σ ct.S s s) := by
    rw [Real.sqrt_mul (hG0 i)]
    exact mul_le_mul (key i) (key s) (by positivity) (Real.sqrt_nonneg _)
  rw [hc]
  have e : 2 * (aOf d p * (Real.sqrt (ct.ySrc b i) * Real.sqrt (ct.ySrc b s))) *
      (Real.sqrt (X i i) * Real.sqrt (X s s)) = aOf d p * (2 * (Real.sqrt (ct.ySrc b i) *
        Real.sqrt (X (i : ct.V) i) * (Real.sqrt (ct.ySrc b s) * Real.sqrt (X s s)))) := by ring
  rw [e]
  unfold SecC.lamR
  refine mul_le_mul_of_nonneg_left ?_ ha.le
  have s1 := Real.sqrt_nonneg (greenP ct.G (aOf d p) 1 ct.yp σ ct.S i i *
    greenP ct.G (aOf d p) 1 ct.yp σ ct.S s s)
  have s2 := Real.sqrt_nonneg (greenP ct.G (aOf d p) (-1) ct.ym σ ct.S i i *
    greenP ct.G (aOf d p) (-1) ct.ym σ ct.S s s)
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, Contact.ySrc] at h2 ⊢
    linarith
  · simp only [↓reduceIte, Contact.ySrc] at h2 ⊢
    linarith

/-- **Pointwise bound at a supported signing.** -/
theorem starObs_pointwise (hR : TRegime d p) {h : ℝ} (hh : 0 < h) (e dir : Bool) {i : ct.V}
    (hi : i ∈ ct.S) (l : List (ct.V × Bool × Bool)) {σ : Config ct.V}
    (hσ : wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0) {N : ℕ} {κ : ℝ} (hκ : 0 < κ)
    (hKl : ∀ s, ((4 * p + (l.length + 4) + N : ℕ) : ℝ) *
      SecC.lamR ct.G (aOf d p) ct.yp ct.ym σ ct.S i s ≤ κ)
    (j : nbhd ct.G ct.S i → ℕ) (hj : 2 * ∑ s, j s ≤ N) :
    |dEven (lJ ct i) j (starObsQ ct h e dir i l σ) (rootSigns ct.G σ ct.S i) /
        starPhi p (rootA ct σ i) (rootB ct σ i) (rootSigns ct.G σ ct.S i)| +
      |dEven (lJ ct i) j (starObsT ct h e dir i l σ) (rootSigns ct.G σ ct.S i) /
        starPhi p (rootA ct σ i) (rootB ct σ i) (rootSigns ct.G σ ct.S i)| ≤
      ct.wtH h e i l σ * (κ ^ (2 * ∑ s, j s) * (qForm (kerL ct h e dir i σ) (rootSigns ct.G σ ct.S i) +
        qd1 0 (kerL ct h e dir i σ) (rootSigns ct.G σ ct.S i) (dEvenList (lJ ct i) j) / κ +
        qd2 (kerL ct h e dir i σ) (dEvenList (lJ ct i) j) / κ ^ 2 +
        (kerL ct h e dir i σ).trace)) := by
  classical
  have hp1 : 1 ≤ p := le_trans (by norm_num) hR.two_le_p
  have hyp0 : ∀ k, 0 ≤ ct.yp k := fun k => (ct.ctx.hyp k).1
  have hym0 : ∀ k, 0 ≤ ct.ym k := fun k => (ct.ctx.hym k).1
  have ha := hR.aOf_pos
  have hc : wtCore ct.G p (aOf d p) ct.yp ct.ym σ ct.S i ≠ 0 :=
    SecC.wtCore_ne_zero_of_wt ct.G hp1 hyp0 hym0 hi hσ
  obtain ⟨ξ, hξ⟩ : ∃ ξ, ξ = rootSigns ct.G σ ct.S i := ⟨_, rfl⟩
  rw [← hξ]
  obtain ⟨L', hL'⟩ : ∃ L' : List (ct.V × Bool × Bool),
      L' = l ++ [(i, e, true), (i, e, true), (i, true, true), (i, true, true)] := ⟨_, rfl⟩
  have hL'len : L'.length = l.length + 4 := by rw [hL']; simp
  have hlam0 : ∀ s, 0 ≤ SecC.lamR ct.G (aOf d p) ct.yp ct.ym σ ct.S i s := fun s =>
    mul_nonneg ha.le (add_nonneg (mul_nonneg zero_le_two (Real.sqrt_nonneg _))
      (mul_nonneg zero_le_two (Real.sqrt_nonneg _)))
  -- the endpoint factor `Φ̃`
  obtain ⟨hα, hA1, hA2⟩ := SecC.branch_majorant ct.G hR ct.ctx.toCapCtx ct.ctx.hyp ct.ctx.hym
    (SecC.isBranch_plus ct.yp ct.ym) hi hσ
  obtain ⟨hβ, hB1, hB2⟩ := SecC.branch_majorant ct.G hR ct.ctx.toCapCtx ct.ctx.hyp ct.ctx.hym
    (SecC.isBranch_minus ct.yp ct.ym) hi hσ
  rw [← hξ] at hα hA1 hA2 hβ hB1 hB2
  have hα' : 0 < 1 - qForm (rootA ct σ i) ξ := hα
  have hβ' : 0 < 1 - qForm (rootB ct σ i) ξ := hβ
  have hA1' : ∀ s, |(rootA ct σ i *ᵥ ξ) s| ≤ (1 - qForm (rootA ct σ i) ξ) *
      SecC.lamR ct.G (aOf d p) ct.yp ct.ym σ ct.S i s := hA1
  have hA2' : ∀ s t, |rootA ct σ i s t| ≤ (1 - qForm (rootA ct σ i) ξ) *
      SecC.lamR ct.G (aOf d p) ct.yp ct.ym σ ct.S i s *
        SecC.lamR ct.G (aOf d p) ct.yp ct.ym σ ct.S i t := hA2
  have hB1' : ∀ s, |(rootB ct σ i *ᵥ ξ) s| ≤ (1 - qForm (rootB ct σ i) ξ) *
      SecC.lamR ct.G (aOf d p) ct.yp ct.ym σ ct.S i s := hB1
  have hB2' : ∀ s t, |rootB ct σ i s t| ≤ (1 - qForm (rootB ct σ i) ξ) *
      SecC.lamR ct.G (aOf d p) ct.yp ct.ym σ ct.S i s *
        SecC.lamR ct.G (aOf d p) ct.yp ct.ym σ ct.S i t := hB2
  have hAs : ∀ s t, rootA ct σ i s t = rootA ct σ i t s :=
    SecC.rootMat_apply_comm ct.G _ _ _ σ ct.S i
  have hBs : ∀ s t, rootB ct σ i s t = rootB ct σ i t s :=
    SecC.rootMat_apply_comm ct.G _ _ _ σ ct.S i
  have hΦM := ((majAt_quadFn hlam0 (SecC.quadMaj_neg hAs hα' hA1' hA2')).pow p).mul
    ((majAt_quadFn hlam0 (SecC.quadMaj_neg hBs hβ' hB1' hB2')).pow p)
  obtain ⟨Φt, hΦt⟩ : ∃ f : (nbhd ct.G ct.S i → ℝ) → ℝ,
      f = quadFn 1 0 (-rootA ct σ i) ^ p * quadFn 1 0 (-rootB ct σ i) ^ p := ⟨_, rfl⟩
  rw [← hΦt] at hΦM
  obtain ⟨M₀, hM₀⟩ : ∃ M₀ : ℝ,
      M₀ = (1 - qForm (rootA ct σ i) ξ) ^ p * (1 - qForm (rootB ct σ i) ξ) ^ p := ⟨_, rfl⟩
  rw [← hM₀] at hΦM
  have hM₀pos : 0 < M₀ := by rw [hM₀]; exact mul_pos (pow_pos hα' p) (pow_pos hβ' p)
  have hΦeq : ∀ x, qForm (rootA ct σ i) x < 1 → qForm (rootB ct σ i) x < 1 →
      starPhi p (rootA ct σ i) (rootB ct σ i) x = Φt x := by
    intro x h1 h2
    rw [hΦt]
    simp only [starPhi, clipF_eq_of_lt h1, clipF_eq_of_lt h2, Pi.mul_apply, Pi.pow_apply,
      quadFn_one_zero_neg]
  -- the shift `δ`
  have hF : ∀ b sh, (facM ct h σ i b sh ξ).PosDef ∧ ∀ k, (facM ct h σ i b sh ξ)⁻¹ k k ≤
      hN ct.G (aOf d p) (if b then 1 else -1) (ct.ySrc b) σ ct.S k := fun b sh => by
    rw [hξ]; exact facM_root ct hh.le hi hσ b sh
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = min (min (facM ct h σ i true true ξ).det
      (facM ct h σ i true false ξ).det) (min (facM ct h σ i false true ξ).det
        (facM ct h σ i false false ξ).det) := ⟨_, rfl⟩
  have hδle : ∀ b sh, δ ≤ (facM ct h σ i b sh ξ).det := by
    intro b sh
    rw [hδdef]
    cases b <;> cases sh
    · exact (min_le_right _ _).trans (min_le_right _ _)
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_left _ _).trans (min_le_right _ _)
    · exact (min_le_left _ _).trans (min_le_left _ _)
  have hδ : 0 < δ := by
    rw [hδdef]
    exact lt_min (lt_min (hF true true).1.det_pos (hF true false).1.det_pos)
      (lt_min (hF false true).1.det_pos (hF false false).1.det_pos)
  have hδ2 : ∀ b sh, δ / 2 < (facM ct h σ i b sh ξ).det := fun b sh => by
    linarith [hδle b sh]
  -- the diagonal factors
  have hMc : ∀ b sh, ∀ u w, ContDiff ℝ ∞ fun x => facM ct h σ i b sh x u w :=
    fun b sh u w => contDiff_shiftSub_apply ct.G _ _ _ _ σ ct.S i _ u w
  have hE : ∀ b sh, ∀ (s : nbhd ct.G ct.S i) (u w : ct.V),
      pderiv s (fun x => facM ct h σ i b sh x u w) = fun _ =>
        ((if b then 1 else -1) * aOf d p * (Real.sqrt (ct.ySrc b i) * Real.sqrt (ct.ySrc b s))) *
          ((if u = i ∧ w = (s : ct.V) then 1 else 0) + (if u = (s : ct.V) ∧ w = i then 1 else 0)) :=
    fun b sh s u w => pderiv_shiftSub_apply ct.G _ _ _ _ σ ct.S i _ s u w
  obtain ⟨Γ, hΓdef⟩ : ∃ Γ : ct.V × Bool × Bool → (nbhd ct.G ct.S i → ℝ) → ℝ,
      Γ = fun t x => ct.ySrc t.2.1 t.1 * invSm (facM ct h σ i t.2.1 t.2.2) δ t.1 t.1 x :=
    ⟨_, rfl⟩
  have hΓc : ∀ t, ContDiff ℝ ∞ (Γ t) := fun t => by
    rw [hΓdef]
    exact contDiff_const.mul (contDiff_invSm (hMc _ _) hδ _ _)
  have hΓ : ∀ t (l' : List (nbhd ct.G ct.S i)), |pderivList l' (Γ t) ξ| ≤
      wtDiag ct h i σ t ξ * rfac 1 l'.length *
        (l'.map (SecC.lamR ct.G (aOf d p) ct.yp ct.ym σ ct.S i)).prod := by
    rintro ⟨k, b, sh⟩ l'
    have hinv := invSm_deriv_le (hMc b sh) (hE b sh) hδ (hδ2 b sh) (hF b sh).1 l'.length l'
      le_rfl k k
    have hw : ∀ s : nbhd ct.G ct.S i, 2 * |(if b then 1 else -1) * aOf d p *
        (Real.sqrt (ct.ySrc b i) * Real.sqrt (ct.ySrc b s))| *
          (Real.sqrt ((facM ct h σ i b sh ξ)⁻¹ i i) *
            Real.sqrt ((facM ct h σ i b sh ξ)⁻¹ s s)) ≤
        SecC.lamR ct.G (aOf d p) ct.yp ct.ym σ ct.S i s := fun s => by
      rw [hξ]; exact facM_weight_le ct hR hh.le hi hσ b sh s
    have hprod := list_prod_map_le (fun s => by positivity) hw l'
    have hX0 : 0 ≤ (facM ct h σ i b sh ξ)⁻¹ k k := (hF b sh).1.inv.diag_pos.le
    rw [Real.mul_self_sqrt hX0] at hinv
    have e : pderivList l' (Γ (k, b, sh)) ξ =
        ct.ySrc b k * pderivList l' (invSm (facM ct h σ i b sh) δ k k) ξ := by
      rw [hΓdef]
      exact congrFun (pderivList_cmul l' _ _) ξ
    have hy := ySrc_nonneg ct b k
    rw [e, abs_mul, abs_of_nonneg hy, wtDiag_eq_facM]
    calc ct.ySrc b k * |pderivList l' (invSm (facM ct h σ i b sh) δ k k) ξ|
        ≤ ct.ySrc b k * ((facM ct h σ i b sh ξ)⁻¹ k k * rfac 1 l'.length *
            (l'.map fun s : nbhd ct.G ct.S i => 2 * |(if b then 1 else -1) * aOf d p *
              (Real.sqrt (ct.ySrc b i) * Real.sqrt (ct.ySrc b s))| *
                (Real.sqrt ((facM ct h σ i b sh ξ)⁻¹ i i) *
                  Real.sqrt ((facM ct h σ i b sh ξ)⁻¹ s s))).prod) :=
          mul_le_mul_of_nonneg_left hinv hy
      _ ≤ ct.ySrc b k * ((facM ct h σ i b sh ξ)⁻¹ k k * rfac 1 l'.length *
            (l'.map (SecC.lamR ct.G (aOf d p) ct.yp ct.ym σ ct.S i)).prod) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hprod
            (mul_nonneg hX0 (rfac_nonneg zero_le_one _))) hy
      _ = _ := by ring
  -- the product `H̃`
  obtain ⟨Ht, hHt⟩ : ∃ f : (nbhd ct.G ct.S i → ℝ) → ℝ,
      f = fun x => (L'.map fun t => Γ t x).prod := ⟨_, rfl⟩
  have hHc : ContDiff ℝ ∞ Ht := by
    rw [hHt]; exact contDiff_list_prod_map L' Γ fun t _ => hΓc t
  have hHr := rfBound_listProd (N := N) hlam0 Γ (fun t => wtDiag ct h i σ t ξ) L'
    (fun t _ => hΓc t) (fun t _ l' _ => hΓ t l')
  rw [← hHt] at hHr
  have hHval : (L'.map fun t => wtDiag ct h i σ t ξ).prod = ct.wtH h e i l σ := by
    rw [hL', ← wtHSub_eq_prod, hξ, wtHSub_setRoot ct e hi l σ (rootSigns_pm ct σ i),
      setRoot_rootSigns]
  have hH0 : 0 ≤ ct.wtH h e i l σ := wtH_nonneg ct hh.le e i l hσ
  have hHK : ∀ l' : List (nbhd ct.G ct.S i), l'.length ≤ N → |pderivList l' Ht ξ| ≤
      ct.wtH h e i l σ * ((L'.length : ℝ) + N) ^ l'.length *
        (l'.map (SecC.lamR ct.G (aOf d p) ct.yp ct.ym σ ct.S i)).prod := by
    intro l' hl'
    refine (hHr l' hl').trans ?_
    rw [hHval]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (rfac_le_pow (Nat.cast_nonneg _) hl') hH0) (prod_map_nonneg' hlam0 l')
  -- the product `Φ̃ H̃`
  have hK : (p : ℝ) * 2 + p * 2 + ((L'.length : ℝ) + N) =
      ((4 * p + (l.length + 4) + N : ℕ) : ℝ) := by
    rw [hL'len]; push_cast; ring
  have hfκ : ∀ l' : List (nbhd ct.G ct.S i), l'.length ≤ N →
      |pderivList l' (Φt * Ht) ξ| ≤ (M₀ * ct.wtH h e i l σ) * κ ^ l'.length := by
    intro l' hl'
    have h1 := majBound_mul_len (K₁ := (p : ℝ) * 2 + p * 2) (K₂ := (L'.length : ℝ) + N) l'
      hΦM.1 hHc (fun l'' _ => hΦM.2 l'') (fun l'' hl'' => hHK l'' (le_trans hl'' hl'))
    refine h1.trans ?_
    rw [hK, mul_assoc (M₀ * ct.wtH h e i l σ)]
    exact mul_le_mul_of_nonneg_left (pow_mul_prod_le (Nat.cast_nonneg _) hlam0 hKl l')
      (mul_nonneg hM₀pos.le hH0)
  -- the local representation near `ξ`
  have hqA : qForm (rootA ct σ i) ξ < 1 := by linarith
  have hqB : qForm (rootB ct σ i) ξ < 1 := by linarith
  have hU : ∀ᶠ x in 𝓝 ξ, qForm (rootA ct σ i) x < 1 ∧ qForm (rootB ct σ i) x < 1 ∧
      ∀ b sh, δ / 2 < (facM ct h σ i b sh x).det := by
    have e1 : ∀ᶠ x in 𝓝 ξ, qForm (rootA ct σ i) x < 1 :=
      (isOpen_lt (continuous_qForm _) continuous_const).mem_nhds hqA
    have e2 : ∀ᶠ x in 𝓝 ξ, qForm (rootB ct σ i) x < 1 :=
      (isOpen_lt (continuous_qForm _) continuous_const).mem_nhds hqB
    refine e1.and (e2.and ?_)
    rw [Filter.eventually_all]
    intro b
    rw [Filter.eventually_all]
    intro sh
    exact (isOpen_lt continuous_const
      (continuous_det_shiftSub ct.G _ _ _ _ σ ct.S i _)).mem_nhds (hδ2 b sh)
  have hHeq : ∀ x, (∀ b sh, δ / 2 < (facM ct h σ i b sh x).det) →
      wtHSub ct h e i l σ x = Ht x := by
    intro x hx
    rw [wtHSub_eq_prod, ← hL', hHt]
    congr 1
    refine List.map_congr_left fun t _ => ?_
    obtain ⟨k, b, sh⟩ := t
    rw [wtDiag_eq_facM, hΓdef]
    show ct.ySrc b k * (facM ct h σ i b sh x)⁻¹ k k =
      ct.ySrc b k * invSm (facM ct h σ i b sh) δ k k x
    rw [invSm_eq hδ (hx b sh).le]
  have hevQ : starObsQ ct h e dir i l σ =ᶠ[𝓝 ξ]
      Φt * Ht * quadFn 0 0 (kerL ct h e dir i σ) := hU.mono fun x hx => by
    simp only [starObsQ, if_pos hc]
    rw [hΦeq x hx.1 hx.2.1, hHeq x hx.2.2]
    simp only [Pi.mul_apply, quadFn, zero_add, zero_dotProduct]
    ring
  have hevT : starObsT ct h e dir i l σ =ᶠ[𝓝 ξ]
      fun x => (kerL ct h e dir i σ).trace * (Φt * Ht) x := hU.mono fun x hx => by
    simp only [starObsT, if_pos hc]
    rw [hΦeq x hx.1 hx.2.1, hHeq x hx.2.2]
    rfl
  -- the derivative bounds
  set lst := dEvenList (lJ ct i) j with hlst
  have hlen : lst.length = 2 * ∑ s, j s := SecC.length_dEvenList_univ j
  have hlstN : lst.length ≤ N := hlen ▸ hj
  have hq0 : 0 ≤ qForm (kerL ct h e dir i σ) ξ := by
    have := (kerL_posSemidef ct h e dir i σ).dotProduct_mulVec_nonneg ξ
    simp only [star_trivial] at this
    exact this
  have htr0 : 0 ≤ (kerL ct h e dir i σ).trace := (kerL_posSemidef ct h e dir i σ).trace_nonneg
  have hql := quad_leibniz hκ.le lst (hΦM.1.mul hHc)
    (fun l' hl' => hfκ l' (le_trans hl' hlstN)) (c := 0) (ℓ := 0) (Q := kerL ct h e dir i σ)
  have hqv : quadFn 0 0 (kerL ct h e dir i σ) ξ = qForm (kerL ct h e dir i σ) ξ := by
    simp [quadFn]
  rw [hqv, abs_of_nonneg hq0] at hql
  have hQ : |pderivList lst (starObsQ ct h e dir i l σ) ξ| ≤
      (M₀ * ct.wtH h e i l σ) * (κ ^ lst.length * (qForm (kerL ct h e dir i σ) ξ +
        qd1 0 (kerL ct h e dir i σ) ξ lst / κ + qd2 (kerL ct h e dir i σ) lst / κ ^ 2)) := by
    rw [(pderivList_congr_nhds hevQ lst).eq_of_nhds]
    have hκ2 : 0 < κ ^ 2 := by positivity
    refine le_of_mul_le_mul_left (hql.trans_eq ?_) hκ2
    field_simp
    ring
  have hT : |pderivList lst (starObsT ct h e dir i l σ) ξ| ≤
      (kerL ct h e dir i σ).trace * ((M₀ * ct.wtH h e i l σ) * κ ^ lst.length) := by
    rw [(pderivList_congr_nhds hevT lst).eq_of_nhds, pderivList_cmul]
    show |(kerL ct h e dir i σ).trace * pderivList lst (Φt * Ht) ξ| ≤ _
    rw [abs_mul, abs_of_nonneg htr0]
    exact mul_le_mul_of_nonneg_left (hfκ lst hlstN) htr0
  have hΦξ : starPhi p (rootA ct σ i) (rootB ct σ i) ξ = M₀ := by
    rw [hM₀]
    simp only [starPhi, clipF_eq_of_lt hqA, clipF_eq_of_lt hqB]
  rw [dEven_eq_pderivList, dEven_eq_pderivList, ← hlst, hΦξ, abs_div, abs_div,
    abs_of_pos hM₀pos, ← add_div, div_le_iff₀ hM₀pos, ← hlen]
  calc |pderivList lst (starObsQ ct h e dir i l σ) ξ| +
        |pderivList lst (starObsT ct h e dir i l σ) ξ|
      ≤ (M₀ * ct.wtH h e i l σ) * (κ ^ lst.length * (qForm (kerL ct h e dir i σ) ξ +
          qd1 0 (kerL ct h e dir i σ) ξ lst / κ + qd2 (kerL ct h e dir i σ) lst / κ ^ 2)) +
        (kerL ct h e dir i σ).trace * ((M₀ * ct.wtH h e i l σ) * κ ^ lst.length) :=
        add_le_add hQ hT
    _ = _ := by ring

end Contact

end BiluLinial.Tight.SecB
