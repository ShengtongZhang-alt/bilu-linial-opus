/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import Mathlib

/-!
# Glued determinant powers along diagonal curves

Blueprint node `D-SM-glue` (source Section 1.1, proof of Lemma "Source maximum and moments":
"`p - k ≥ 2` makes inverse-weighted determinant powers continuously differentiable across a
support boundary"; AUDIT-D DF1).

For a symmetric `Q₀` and a curve `Q(t) = Q₀ + diag δ(t)` with `δ(0) = 0` and `δ'(0) = δ'`, the
function `g(t) = 1{Q(t) ≻ 0} det(Q(t))^p ((Q(t))⁻¹_ii)^k` has, for `k + 2 ≤ p`, the derivative
`1{Q₀ ≻ 0} det(Q₀)^p (p G_ii^k Σ_l G_ll δ'_l - k G_ii^{k-1} Σ_l G_il² δ'_l)` at `0`
(`G = Q₀⁻¹`).

**Sketch.** (Jacobi) `t ↦ det(Q₀ + diag δ(t))` has derivative `Σ_l adj(Q₀)_ll δ'_l`: expand the
determinant as a multilinear map of the rows, `f(x + h) = f x + f.linearDeriv x h + Σ_{|s| ≥ 2} …`;
the rows of `h = diag δ(t)` are `δ_l(t) e_l`, so each higher term is `Π_{l ∈ s} δ_l(t)` times a
constant, whose derivative at `0` vanishes since at least two factors vanish there.
(Inverse) Entries of `Q(t)⁻¹ = det⁻¹ adj` are differentiable (adjugate entries are determinants
of entrywise differentiable curves), and differentiating `Q(t) Q(t)⁻¹ = 1` gives
`(Q⁻¹)' = -G diag(δ') G`. (Glue) If `Q₀ ≻ 0`, `Q(t) ≻ 0` near `0` (openness) and the formula is
the product rule. If `Q₀` is not PSD, `Q(t)` is not PSD near `0` and `g = 0` there. If `Q₀ ⪰ 0`
is singular, `det Q₀ = 0`, `|g(t)| ≤ |det Q(t)|^{p-k} |adj(Q(t))_ii|^k = O(t^{p-k}) = o(t)`.
Small cases: `1 × 1`, `Q₀ = q`: `g = 1{q + δ > 0}(q + δ)^{p-k}`; at `q = 0` and `p - k = 1` the
derivative does not exist, so `k + 2 ≤ p` is needed.
-/

@[expose] public section

namespace BiluLinial.Tight

open Matrix Filter Topology Asymptotics

variable {n : Type*} [Fintype n] [DecidableEq n]

open Classical in
/-- `1{Q ≻ 0} det(Q)^p`. -/
noncomputable def posPow (p : ℕ) (Q : Matrix n n ℝ) : ℝ := if Q.PosDef then Q.det ^ p else 0

/-- `1{Q ≻ 0} det(Q)^p ((Q⁻¹)_ii)^k`. -/
noncomputable def glue (p k : ℕ) (i : n) (Q : Matrix n n ℝ) : ℝ := posPow p Q * (Q⁻¹ i i) ^ k

/-- The derivative of `glue` along `Q + t diag e` at `t = 0`:
`1{Q ≻ 0} det(Q)^p (p G_ii^k Σ_l G_ll e_l - k G_ii^{k-1} Σ_l G_il² e_l)`, `G = Q⁻¹`. -/
noncomputable def glueDeriv (p k : ℕ) (i : n) (Q : Matrix n n ℝ) (e : n → ℝ) : ℝ :=
  posPow p Q * ((p : ℝ) * (Q⁻¹ i i) ^ k * ∑ l, Q⁻¹ l l * e l -
    (k : ℝ) * (Q⁻¹ i i) ^ (k - 1) * ∑ l, Q⁻¹ i l ^ 2 * e l)

theorem glue_zero (p : ℕ) (i : n) (Q : Matrix n n ℝ) : glue p 0 i Q = posPow p Q := by
  simp [glue]

/-! ### Positivity along continuous families -/

section Family

variable {X : Type*} [TopologicalSpace X]

omit [DecidableEq n] in
private lemma continuous_quadForm_family {P : X → Matrix n n ℝ} (hP : Continuous P) :
    Continuous fun q : X × (n → ℝ) => q.2 ⬝ᵥ (P q.1 *ᵥ q.2) :=
  continuous_snd.dotProduct ((hP.comp continuous_fst).matrix_mulVec continuous_snd)

omit [DecidableEq n] in
/-- Along a continuous family of symmetric matrices, positive definiteness is an open
condition. -/
theorem isOpen_posDef_family {P : X → Matrix n n ℝ} (hP : Continuous P)
    (hPh : ∀ x, (P x).IsHermitian) : IsOpen {x | (P x).PosDef} := by
  rw [isOpen_iff_mem_nhds]
  intro x₀ hx₀
  have hev : ∀ᶠ x in 𝓝 x₀, ∀ v ∈ Metric.sphere (0 : n → ℝ) 1, 0 < v ⬝ᵥ (P x *ᵥ v) := by
    refine (isCompact_sphere (0 : n → ℝ) 1).eventually_forall_of_forall_eventually
      (P := fun x v => 0 < v ⬝ᵥ (P x *ᵥ v)) fun v hv => ?_
    have hv0 : v ≠ 0 := by
      rintro rfl
      simp at hv
    have hpos : 0 < v ⬝ᵥ (P x₀ *ᵥ v) := by
      simpa only [star_trivial] using PosDef.dotProduct_mulVec_pos hx₀ hv0
    exact (continuous_quadForm_family hP).continuousAt.eventually (eventually_gt_nhds hpos)
  filter_upwards [hev] with x hx
  refine PosDef.of_dotProduct_mulVec_pos (hPh x) fun v hv => ?_
  rw [star_trivial]
  have hn : 0 < ‖v‖ := norm_pos_iff.2 hv
  have hw : ‖v‖⁻¹ • v ∈ Metric.sphere (0 : n → ℝ) 1 := by
    simp [norm_smul, hn.ne']
  have h := hx _ hw
  simp only [mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul] at h
  exact pos_of_mul_pos_right (pos_of_mul_pos_right h (inv_nonneg.2 hn.le)) (inv_nonneg.2 hn.le)

omit [DecidableEq n] in
/-- Along a continuous family of symmetric matrices, positive semidefiniteness is a closed
condition. -/
theorem isClosed_posSemidef_family {P : X → Matrix n n ℝ} (hP : Continuous P)
    (hPh : ∀ x, (P x).IsHermitian) : IsClosed {x | (P x).PosSemidef} := by
  have : {x | (P x).PosSemidef} = ⋂ v : n → ℝ, {x | 0 ≤ v ⬝ᵥ (P x *ᵥ v)} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, posSemidef_iff_dotProduct_mulVec, hPh x,
      true_and, star_trivial]
  rw [this]
  exact isClosed_iInter fun v => isClosed_le continuous_const
    ((continuous_quadForm_family hP).comp (continuous_id.prodMk continuous_const))

/-- A function equal to a continuous `F` where two continuous families of symmetric matrices are
both positive definite, and to `0` elsewhere, is continuous if `F` vanishes whenever one of the
determinants does. -/
theorem continuous_ite_posDef_family {P Q : X → Matrix n n ℝ} (hP : Continuous P)
    (hQ : Continuous Q) (hPh : ∀ x, (P x).IsHermitian) (hQh : ∀ x, (Q x).IsHermitian)
    {F : X → ℝ} (hF : Continuous F) (h0 : ∀ x, (P x).det = 0 ∨ (Q x).det = 0 → F x = 0)
    {_ : ∀ x, Decidable ((P x).PosDef ∧ (Q x).PosDef)} :
    Continuous fun x => if (P x).PosDef ∧ (Q x).PosDef then F x else 0 := by
  have hU : IsOpen {x | (P x).PosDef ∧ (Q x).PosDef} :=
    (isOpen_posDef_family hP hPh).inter (isOpen_posDef_family hQ hQh)
  have hcl : closure {x | (P x).PosDef ∧ (Q x).PosDef} ⊆
      {x | (P x).PosSemidef} ∩ {x | (Q x).PosSemidef} :=
    closure_minimal (fun x hx => ⟨hx.1.posSemidef, hx.2.posSemidef⟩)
      ((isClosed_posSemidef_family hP hPh).inter (isClosed_posSemidef_family hQ hQh))
  refine Continuous.if (fun x hx => ?_) hF continuous_const
  rw [hU.frontier_eq] at hx
  obtain ⟨hxc, hxU⟩ := hx
  obtain ⟨hPs, hQs⟩ := hcl hxc
  apply h0
  by_contra hne
  obtain ⟨hP0, hQ0⟩ := not_or.1 hne
  exact hxU ⟨(PosSemidef.posDef_iff_det_ne_zero hPs).2 hP0,
    (PosSemidef.posDef_iff_det_ne_zero hQs).2 hQ0⟩

end Family

/-! ### Derivatives along diagonal curves -/

/-- A determinant of entrywise differentiable functions is differentiable. -/
theorem differentiableAt_det_of_entries {M : ℝ → Matrix n n ℝ} {t₀ : ℝ}
    (hM : ∀ i j, DifferentiableAt ℝ (fun s => M s i j) t₀) :
    DifferentiableAt ℝ (fun s => (M s).det) t₀ := by
  simp_rw [det_apply']
  exact DifferentiableAt.fun_sum fun σ _ =>
    (differentiableAt_const _).mul (DifferentiableAt.fun_finsetProd fun i _ => hM _ _)

/-- Jacobi's formula along a diagonal curve. -/
theorem hasDerivAt_det_add_diagonal (Q₀ : Matrix n n ℝ) {δ : ℝ → n → ℝ} {δ' : n → ℝ}
    (h0 : δ 0 = 0) (hδ : ∀ l, HasDerivAt (fun t => δ t l) (δ' l) 0) :
    HasDerivAt (fun t => (Q₀ + diagonal (δ t)).det) (∑ l, Q₀.adjugate l l * δ' l) 0 := by
  let f := (detRowAlternating : (n → ℝ) [⋀^n]→ₗ[ℝ] ℝ).toMultilinearMap
  let E : n → n → ℝ := fun l => Pi.single l 1
  let A : n → n → ℝ := Matrix.of.symm Q₀
  let D : ℝ → n → n → ℝ := fun t => Matrix.of.symm (diagonal (δ t))
  have hrow : ∀ t l, D t l = δ t l • E l := by
    intro t l
    ext w
    simp only [D, E, of_symm_apply, diagonal_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    by_cases h : l = w
    · subst h; simp
    · simp [h, Ne.symm h]
  have hexp : ∀ t, (Q₀ + diagonal (δ t)).det = Q₀.det + ∑ l, δ t l * Q₀.adjugate l l +
      ∑ s ∈ Finset.univ.filter (fun s : Finset n => 2 ≤ s.card),
        (∏ l ∈ s, δ t l) * f (s.piecewise E A) := by
    intro t
    have h := f.map_add_eq_map_add_linearDeriv_add A (D t)
    rw [MultilinearMap.linearDeriv_apply] at h
    have hlin : ∀ l, f (Function.update A l (D t l)) = δ t l * Q₀.adjugate l l := by
      intro l
      rw [hrow, f.map_update_smul, smul_eq_mul]
      congr 1
      exact (adjugate_apply Q₀ l l).symm
    have hpw : ∀ s : Finset n,
        f (s.piecewise (D t) A) = (∏ l ∈ s, δ t l) * f (s.piecewise E A) := by
      intro s
      have hs : s.piecewise (D t) A =
          s.piecewise (fun i => δ t i • (s.piecewise E A) i) (s.piecewise E A) := by
        funext i
        by_cases hi : i ∈ s
        · rw [Finset.piecewise_eq_of_mem _ _ _ hi, Finset.piecewise_eq_of_mem _ _ _ hi,
            Finset.piecewise_eq_of_mem _ _ _ hi, hrow]
        · rw [Finset.piecewise_eq_of_notMem _ _ _ hi, Finset.piecewise_eq_of_notMem _ _ _ hi,
            Finset.piecewise_eq_of_notMem _ _ _ hi]
      rw [hs, f.map_piecewise_smul, smul_eq_mul]
    simp only [hlin, hpw] at h
    exact h
  have hd1 : HasDerivAt (fun t => ∑ l, δ t l * Q₀.adjugate l l)
      (∑ l, δ' l * Q₀.adjugate l l) 0 :=
    HasDerivAt.fun_sum fun l _ => (hδ l).mul_const _
  have hd2 : HasDerivAt (fun t => ∑ s ∈ Finset.univ.filter (fun s : Finset n => 2 ≤ s.card),
      (∏ l ∈ s, δ t l) * f (s.piecewise E Q₀)) 0 0 := by
    have hs : ∀ s ∈ Finset.univ.filter (fun s : Finset n => 2 ≤ s.card),
        HasDerivAt (fun t => (∏ l ∈ s, δ t l) * f (s.piecewise E Q₀)) 0 0 := by
      intro s hs
      have hs2 : 2 ≤ s.card := (Finset.mem_filter.1 hs).2
      have hp := HasDerivAt.fun_finsetProd (u := s) (f := fun l t => δ t l) fun l _ => hδ l
      have hz : (∑ i ∈ s, (∏ j ∈ s.erase i, δ 0 j) • δ' i) = 0 := by
        refine Finset.sum_eq_zero fun i hi => ?_
        obtain ⟨j, hj⟩ : (s.erase i).Nonempty := by
          rw [← Finset.card_pos, Finset.card_erase_of_mem hi]
          omega
        rw [Finset.prod_eq_zero hj (by rw [h0]; rfl), zero_smul]
      rw [hz] at hp
      simpa using hp.mul_const (f (s.piecewise E Q₀))
    simpa using HasDerivAt.fun_sum hs
  have := ((hasDerivAt_const (0 : ℝ) Q₀.det).add hd1).add hd2
  convert this using 1
  · funext t
    exact hexp t
  · simp [mul_comm]

/-- The derivative of the inverse along a diagonal curve: `(Q⁻¹)' = -G diag(δ') G`. -/
theorem hasDerivAt_inv_add_diagonal {Q₀ : Matrix n n ℝ} (hQ₀ : IsUnit Q₀.det) {δ : ℝ → n → ℝ}
    {δ' : n → ℝ} (h0 : δ 0 = 0) (hδ : ∀ l, HasDerivAt (fun t => δ t l) (δ' l) 0) (a b : n) :
    HasDerivAt (fun t => (Q₀ + diagonal (δ t))⁻¹ a b) (-∑ l, Q₀⁻¹ a l * δ' l * Q₀⁻¹ l b) 0 := by
  have hQ0 : Q₀ + diagonal (δ 0) = Q₀ := by rw [h0]; simp
  have hentry : ∀ u w, HasDerivAt (fun t => (Q₀ + diagonal (δ t)) u w) (diagonal δ' u w) 0 := by
    intro u w
    simp only [Matrix.add_apply, diagonal_apply]
    by_cases huw : u = w
    · subst huw
      simpa using (hδ u).const_add (Q₀ u u)
    · simpa [huw] using hasDerivAt_const (0 : ℝ) (Q₀ u w)
  have hdet := hasDerivAt_det_add_diagonal Q₀ h0 hδ
  have hdet0 : (Q₀ + diagonal (δ 0)).det ≠ 0 := by
    rw [hQ0]
    exact hQ₀.ne_zero
  have hdiff : ∀ u w, DifferentiableAt ℝ (fun t => (Q₀ + diagonal (δ t))⁻¹ u w) 0 := by
    intro u w
    have hadj : DifferentiableAt ℝ (fun t => (Q₀ + diagonal (δ t)).adjugate u w) 0 := by
      simp_rw [adjugate_apply]
      refine differentiableAt_det_of_entries fun i j => ?_
      simp only [updateRow_apply]
      split_ifs
      · exact differentiableAt_const _
      · exact (hentry i j).differentiableAt
    have : (fun t => (Q₀ + diagonal (δ t))⁻¹ u w) =
        fun t => ((Q₀ + diagonal (δ t)).det)⁻¹ * (Q₀ + diagonal (δ t)).adjugate u w := by
      funext t
      rw [inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv]
    rw [this]
    exact (hdet.differentiableAt.inv hdet0).mul hadj
  let X' : Matrix n n ℝ := Matrix.of fun u w => deriv (fun t => (Q₀ + diagonal (δ t))⁻¹ u w) 0
  have hX : ∀ u w, HasDerivAt (fun t => (Q₀ + diagonal (δ t))⁻¹ u w) (X' u w) 0 :=
    fun u w => (hdiff u w).hasDerivAt
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), IsUnit (Q₀ + diagonal (δ t)).det := by
    filter_upwards [hdet.continuousAt.eventually_ne hdet0] with t ht
    exact isUnit_iff_ne_zero.2 ht
  have hid : ∀ u w, ∑ c, (diagonal δ' u c * Q₀⁻¹ c w + Q₀ u c * X' c w) = 0 := by
    intro u w
    have h1 : HasDerivAt (fun t => ∑ c, (Q₀ + diagonal (δ t)) u c * (Q₀ + diagonal (δ t))⁻¹ c w)
        (∑ c, (diagonal δ' u c * (Q₀ + diagonal (δ 0))⁻¹ c w +
          (Q₀ + diagonal (δ 0)) u c * X' c w)) 0 :=
      HasDerivAt.fun_sum fun c _ => (hentry u c).mul (hX c w)
    have h2 : HasDerivAt (fun t => ∑ c, (Q₀ + diagonal (δ t)) u c * (Q₀ + diagonal (δ t))⁻¹ c w)
        0 0 := by
      refine (hasDerivAt_const (0 : ℝ) ((1 : Matrix n n ℝ) u w)).congr_of_eventuallyEq ?_
      filter_upwards [hev] with t ht
      rw [← mul_apply, mul_nonsing_inv _ ht]
    rw [hQ0] at h1
    exact h1.unique h2
  have hmat : diagonal δ' * Q₀⁻¹ + Q₀ * X' = 0 := by
    ext u w
    simpa [mul_apply, Finset.sum_add_distrib] using hid u w
  have hX' : X' = -(Q₀⁻¹ * diagonal δ' * Q₀⁻¹) := by
    have h2 := congrArg (fun M => Q₀⁻¹ * M) hmat
    simp only [Matrix.mul_add, Matrix.mul_zero, ← Matrix.mul_assoc, nonsing_inv_mul _ hQ₀,
      Matrix.one_mul] at h2
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact h2
  have := hX a b
  rw [hX', Matrix.neg_apply, mul_apply] at this
  simpa only [mul_diagonal] using this

/-- `D-SM-glue`: the glued determinant power is differentiable along a diagonal curve, for
`k + 2 ≤ p`. -/
theorem hasDerivAt_glue {Q₀ : Matrix n n ℝ} (hQ₀ : Q₀.IsHermitian) {δ : ℝ → n → ℝ} {δ' : n → ℝ}
    (h0 : δ 0 = 0) (hδ : ∀ l, HasDerivAt (fun t => δ t l) (δ' l) 0) {p k : ℕ} (hk : k + 2 ≤ p)
    (i : n) :
    HasDerivAt (fun t => glue p k i (Q₀ + diagonal (δ t))) (glueDeriv p k i Q₀ δ') 0 := by
  classical
  have hδc : ContinuousAt δ 0 := continuousAt_pi.2 fun l => (hδ l).continuousAt
  have hF : Continuous fun v : n → ℝ => Q₀ + diagonal v :=
    continuous_const.add continuous_id.matrix_diagonal
  have hFh : ∀ v : n → ℝ, (Q₀ + diagonal v).IsHermitian :=
    fun v => hQ₀.add (isHermitian_diagonal v)
  have hQ0 : Q₀ + diagonal (δ 0) = Q₀ := by rw [h0]; simp
  have hdet := hasDerivAt_det_add_diagonal Q₀ h0 hδ
  by_cases hPD : Q₀.PosDef
  · have hev : ∀ᶠ t in 𝓝 (0 : ℝ), (Q₀ + diagonal (δ t)).PosDef := by
      have hmem : δ 0 ∈ {v : n → ℝ | (Q₀ + diagonal v).PosDef} := by
        show (Q₀ + diagonal (δ 0)).PosDef
        rw [hQ0]
        exact hPD
      exact hδc.preimage_mem_nhds ((isOpen_posDef_family hF hFh).mem_nhds hmem)
    have hdet0 : Q₀.det ≠ 0 := hPD.det_pos.ne'
    have hinv := hasDerivAt_inv_add_diagonal (isUnit_iff_ne_zero.2 hdet0) h0 hδ i i
    have hprod := (hdet.fun_pow p).mul (hinv.fun_pow k)
    have heq : (fun t => glue p k i (Q₀ + diagonal (δ t))) =ᶠ[𝓝 0]
        fun t => (Q₀ + diagonal (δ t)).det ^ p * ((Q₀ + diagonal (δ t))⁻¹ i i) ^ k := by
      filter_upwards [hev] with t ht
      simp [glue, posPow, ht]
    refine (hprod.congr_of_eventuallyEq heq).congr_deriv ?_
    have hadj : ∀ l, Q₀.adjugate l l = Q₀.det * Q₀⁻¹ l l := by
      intro l
      rw [inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv, ← mul_assoc,
        mul_inv_cancel₀ hdet0, one_mul]
    have hsymm : ∀ l, Q₀⁻¹ l i = Q₀⁻¹ i l := fun l => by
      simpa using hQ₀.inv.apply i l
    have hs1 : ∑ l, Q₀.adjugate l l * δ' l = Q₀.det * ∑ l, Q₀⁻¹ l l * δ' l := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by rw [hadj, mul_assoc]
    have hs2 : ∑ l, Q₀⁻¹ i l * δ' l * Q₀⁻¹ l i = ∑ l, Q₀⁻¹ i l ^ 2 * δ' l :=
      Finset.sum_congr rfl fun l _ => by rw [hsymm]; ring
    simp only [hQ0, glueDeriv, posPow, hPD, ite_true, hs1, hs2]
    obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    push_cast
    ring
  · have hval : glueDeriv p k i Q₀ δ' = 0 := by simp [glueDeriv, posPow, hPD]
    rw [hval]
    have hg0 : glue p k i (Q₀ + diagonal (δ 0)) = 0 := by simp [hQ0, glue, posPow, hPD]
    by_cases hPSD : Q₀.PosSemidef
    · have hd0 : Q₀.det = 0 := by
        by_contra h
        exact hPD ((PosSemidef.posDef_iff_det_ne_zero hPSD).2 h)
      have hdetO : (fun t => (Q₀ + diagonal (δ t)).det) =O[𝓝 0] fun t => t := by
        simpa [hQ0, hd0] using hdet.isBigO_sub
      have hadjc : ContinuousAt (fun t => (Q₀ + diagonal (δ t)).adjugate i i) 0 :=
        ((hF.matrix_adjugate.matrix_elem i i).continuousAt).comp hδc
      set φ : ℝ → ℝ := fun t => |(Q₀ + diagonal (δ t)).det| ^ (p - k - 2) *
        |(Q₀ + diagonal (δ t)).adjugate i i| ^ k with hφ
      have hφc : ContinuousAt φ 0 :=
        (hdet.continuousAt.abs.pow _).mul (hadjc.abs.pow _)
      have hbd : ∀ t, |glue p k i (Q₀ + diagonal (δ t))| ≤
          |(Q₀ + diagonal (δ t)).det| ^ 2 * φ t := by
        intro t
        have hsplit : |(Q₀ + diagonal (δ t)).det| ^ 2 * φ t =
            |(Q₀ + diagonal (δ t)).det| ^ (p - k) * |(Q₀ + diagonal (δ t)).adjugate i i| ^ k := by
          rw [hφ, show |(Q₀ + diagonal (δ t)).det| ^ (p - k) =
              |(Q₀ + diagonal (δ t)).det| ^ 2 * |(Q₀ + diagonal (δ t)).det| ^ (p - k - 2) by
            rw [← pow_add]; congr 1; omega]
          ring
        rw [hsplit]
        by_cases ht : (Q₀ + diagonal (δ t)).PosDef
        · have hd : (Q₀ + diagonal (δ t)).det ≠ 0 := ht.det_pos.ne'
          have : glue p k i (Q₀ + diagonal (δ t)) =
              (Q₀ + diagonal (δ t)).det ^ (p - k) * (Q₀ + diagonal (δ t)).adjugate i i ^ k := by
            simp only [glue, posPow, ht, ite_true]
            rw [inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv, mul_pow, inv_pow]
            have hpk : p = (p - k) + k := by omega
            conv_lhs => rw [hpk, pow_add]
            field_simp
          rw [this, abs_mul, abs_pow, abs_pow]
        · simp only [glue, posPow, ht, ite_false, zero_mul, abs_zero]
          positivity
      have hO : (fun t => glue p k i (Q₀ + diagonal (δ t))) =O[𝓝 0]
          fun t => (Q₀ + diagonal (δ t)).det ^ 2 := by
        refine IsBigO.of_bound (φ 0 + 1) ?_
        filter_upwards [hφc.eventually (eventually_lt_nhds (lt_add_one (φ 0)))] with t ht
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow]
        calc |glue p k i (Q₀ + diagonal (δ t))| ≤ |(Q₀ + diagonal (δ t)).det| ^ 2 * φ t :=
              hbd t
          _ ≤ |(Q₀ + diagonal (δ t)).det| ^ 2 * (φ 0 + 1) := by gcongr
          _ = (φ 0 + 1) * |(Q₀ + diagonal (δ t)).det| ^ 2 := mul_comm _ _
      have ho := (hO.trans (hdetO.pow 2)).trans_isLittleO (isLittleO_pow_id (by norm_num))
      rw [hasDerivAt_iff_isLittleO]
      simpa [hg0] using ho
    · have hmem : δ 0 ∈ {v : n → ℝ | (Q₀ + diagonal v).PosSemidef}ᶜ := by
        show ¬ (Q₀ + diagonal (δ 0)).PosSemidef
        rw [hQ0]
        exact hPSD
      have hev : ∀ᶠ t in 𝓝 (0 : ℝ), ¬ (Q₀ + diagonal (δ t)).PosSemidef :=
        hδc.preimage_mem_nhds
          ((isClosed_posSemidef_family hF hFh).isOpen_compl.mem_nhds hmem)
      have heq : (fun t => glue p k i (Q₀ + diagonal (δ t))) =ᶠ[𝓝 0] fun _ => 0 := by
        filter_upwards [hev] with t ht
        have : ¬ (Q₀ + diagonal (δ t)).PosDef := fun h => ht h.posSemidef
        simp [glue, posPow, this]
      exact (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq heq

end BiluLinial.Tight
