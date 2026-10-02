/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.Defs

/-!
# Continuity of the law in the sources

Blueprint node `D-cont` (source Section 1.1, proof of Lemma "Source maximum and moments": "the
finite sign sums and the floor justify maxima"). `P̃^±` depends continuously on the sources
(through `√y` and `c(a² y_i y_j)`). The weight `1{P̃⁺ ≻ 0, P̃⁻ ≻ 0} (det P̃⁺ det P̃⁻)^p` is
continuous for `p ≥ 1` (it tends to `0` at the boundary of the positive cone), and
`W h_i^+ = 1{…} (det P̃⁺)^{p-1} adj(P̃⁺)_ii (det P̃⁻)^p`
is continuous for `p ≥ 2`.
-/

@[expose] public section

namespace BiluLinial.Tight

open Matrix Filter Topology Set

section General

variable {X n : Type*} [TopologicalSpace X] [Fintype n]

private lemma continuous_quadForm {P : X → Matrix n n ℝ} (hP : Continuous P) :
    Continuous fun q : X × (n → ℝ) => q.2 ⬝ᵥ (P q.1 *ᵥ q.2) :=
  continuous_snd.dotProduct ((hP.comp continuous_fst).matrix_mulVec continuous_snd)

/-- Along a continuous family of symmetric matrices, positive definiteness is an open
condition. -/
private lemma isOpen_posDef {P : X → Matrix n n ℝ} (hP : Continuous P)
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
    exact (continuous_quadForm hP).continuousAt.eventually (eventually_gt_nhds hpos)
  filter_upwards [hev] with x hx
  refine PosDef.of_dotProduct_mulVec_pos (hPh x) fun v hv => ?_
  rw [star_trivial]
  have hn : 0 < ‖v‖ := norm_pos_iff.2 hv
  have hw : ‖v‖⁻¹ • v ∈ Metric.sphere (0 : n → ℝ) 1 := by
    simp [norm_smul, hn.ne']
  have h := hx _ hw
  simp only [mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul] at h
  exact pos_of_mul_pos_right (pos_of_mul_pos_right h (inv_nonneg.2 hn.le)) (inv_nonneg.2 hn.le)

/-- Along a continuous family of symmetric matrices, positive semidefiniteness is a closed
condition. -/
private lemma isClosed_posSemidef {P : X → Matrix n n ℝ} (hP : Continuous P)
    (hPh : ∀ x, (P x).IsHermitian) : IsClosed {x | (P x).PosSemidef} := by
  have : {x | (P x).PosSemidef} = ⋂ v : n → ℝ, {x | 0 ≤ v ⬝ᵥ (P x *ᵥ v)} := by
    ext x
    simp only [mem_ofPred_eq, mem_iInter, posSemidef_iff_dotProduct_mulVec, hPh x, true_and,
      star_trivial]
  rw [this]
  exact isClosed_iInter fun v => isClosed_le continuous_const
    ((continuous_quadForm hP).comp (continuous_id.prodMk continuous_const))

/-- A function equal to a continuous `F` on the set where two continuous families of symmetric
matrices are both positive definite, and to `0` elsewhere, is continuous provided `F` vanishes
whenever one of the determinants does. -/
private lemma continuous_ite_posDef [DecidableEq n] {P Q : X → Matrix n n ℝ} (hP : Continuous P)
    (hQ : Continuous Q) (hPh : ∀ x, (P x).IsHermitian) (hQh : ∀ x, (Q x).IsHermitian)
    {F : X → ℝ} (hF : Continuous F) (h0 : ∀ x, (P x).det = 0 ∨ (Q x).det = 0 → F x = 0)
    {_ : ∀ x, Decidable ((P x).PosDef ∧ (Q x).PosDef)} :
    Continuous fun x => if (P x).PosDef ∧ (Q x).PosDef then F x else 0 := by
  have hU : IsOpen {x | (P x).PosDef ∧ (Q x).PosDef} :=
    (isOpen_posDef hP hPh).inter (isOpen_posDef hQ hQh)
  have hcl : closure {x | (P x).PosDef ∧ (Q x).PosDef} ⊆
      {x | (P x).PosSemidef} ∩ {x | (Q x).PosSemidef} :=
    closure_minimal (fun x hx => ⟨hx.1.posSemidef, hx.2.posSemidef⟩)
      ((isClosed_posSemidef hP hPh).inter (isClosed_posSemidef hQ hQh))
  refine Continuous.if (fun x hx => ?_) hF continuous_const
  rw [hU.frontier_eq] at hx
  obtain ⟨hxc, hxU⟩ := hx
  obtain ⟨hPs, hQs⟩ := hcl hxc
  apply h0
  by_contra hne
  obtain ⟨hP0, hQ0⟩ := not_or.1 hne
  exact hxU ⟨(PosSemidef.posDef_iff_det_ne_zero hPs).2 hP0,
    (PosSemidef.posDef_iff_det_ne_zero hQs).2 hQ0⟩

end General

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

@[fun_prop]
lemma continuous_cRoot : Continuous cRoot := by
  unfold cRoot
  fun_prop

omit [Fintype V] in
lemma continuous_precN (a τ : ℝ) (σ : Config V) (S : Finset V) :
    Continuous fun y : V → ℝ => precN G a τ y σ S := by
  refine continuous_matrix fun u w => ?_
  simp only [precN, Matrix.of_apply]
  split_ifs
  · unfold diagD cEdge
    fun_prop
  · exact continuous_const
  · fun_prop
  · exact continuous_const

omit [Fintype V] in
private lemma precN_isHermitian (a τ : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) :
    (precN G a τ y σ S).IsHermitian := by
  refine Matrix.IsHermitian.ext fun u w => ?_
  simp only [precN, Matrix.of_apply, star_trivial]
  by_cases h : u = w
  · subst h
    rfl
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]
    have hs : sgn σ w u = sgn σ u w := by
      unfold sgn
      rw [Sym2.eq_swap]
    by_cases hc : u ∈ S ∧ w ∈ S ∧ G.Adj u w
    · rw [ite_eq_left ⟨hc.2.1, hc.1, hc.2.2.symm⟩, ite_eq_left hc, hs,
        mul_comm (Real.sqrt (y w))]
    · rw [ite_eq_right (fun h' => hc ⟨h'.2.1, h'.1, h'.2.2.symm⟩), ite_eq_right hc]

lemma continuous_wt {p : ℕ} (hp : 1 ≤ p) (a : ℝ) (σ : Config V) (S : Finset V) :
    Continuous fun y : (V → ℝ) × (V → ℝ) => wt G p a y.1 y.2 σ S := by
  have hP : Continuous fun y : (V → ℝ) × (V → ℝ) => precN G a 1 y.1 σ S :=
    (continuous_precN G a 1 σ S).comp continuous_fst
  have hQ : Continuous fun y : (V → ℝ) × (V → ℝ) => precN G a (-1) y.2 σ S :=
    (continuous_precN G a (-1) σ S).comp continuous_snd
  have hp0 : p ≠ 0 := by omega
  unfold wt
  refine continuous_ite_posDef hP hQ (fun _ => precN_isHermitian G _ _ _ _ _)
    (fun _ => precN_isHermitian G _ _ _ _ _) ((hP.matrix_det.mul hQ.matrix_det).pow p) ?_
  rintro y (h | h) <;> simp [h, hp0]

lemma continuous_wt_mul_hN {p : ℕ} (hp : 2 ≤ p) (a : ℝ) (σ : Config V) (S : Finset V) (i : V) :
    Continuous fun y : (V → ℝ) × (V → ℝ) => wt G p a y.1 y.2 σ S * hN G a 1 y.1 σ S i := by
  classical
  have hP : Continuous fun y : (V → ℝ) × (V → ℝ) => precN G a 1 y.1 σ S :=
    (continuous_precN G a 1 σ S).comp continuous_fst
  have hQ : Continuous fun y : (V → ℝ) × (V → ℝ) => precN G a (-1) y.2 σ S :=
    (continuous_precN G a (-1) σ S).comp continuous_snd
  have hp0 : p ≠ 0 := by omega
  have hp1 : p - 1 ≠ 0 := by omega
  have heq : (fun y : (V → ℝ) × (V → ℝ) => wt G p a y.1 y.2 σ S * hN G a 1 y.1 σ S i) =
      fun y => if (precN G a 1 y.1 σ S).PosDef ∧ (precN G a (-1) y.2 σ S).PosDef then
        (precN G a 1 y.1 σ S).det ^ (p - 1) * (precN G a 1 y.1 σ S).adjugate i i *
          (precN G a (-1) y.2 σ S).det ^ p else 0 := by
    funext y
    unfold wt hN
    split_ifs with h
    · have hd : (precN G a 1 y.1 σ S).det ≠ 0 := h.1.det_pos.ne'
      rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv]
      obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
      rw [Nat.add_sub_cancel]
      calc ((precN G a 1 y.1 σ S).det * (precN G a (-1) y.2 σ S).det) ^ (k + 1) *
            ((precN G a 1 y.1 σ S).det⁻¹ * (precN G a 1 y.1 σ S).adjugate i i)
          = (precN G a 1 y.1 σ S).det ^ k * (precN G a 1 y.1 σ S).adjugate i i *
              (precN G a (-1) y.2 σ S).det ^ (k + 1) *
              ((precN G a 1 y.1 σ S).det * (precN G a 1 y.1 σ S).det⁻¹) := by ring
        _ = _ := by rw [mul_inv_cancel₀ hd, mul_one]
    · rw [zero_mul]
  rw [heq]
  refine continuous_ite_posDef hP hQ (fun _ => precN_isHermitian G _ _ _ _ _)
    (fun _ => precN_isHermitian G _ _ _ _ _)
    (((hP.matrix_det.pow _).mul (hP.matrix_adjugate.matrix_elem i i)).mul
      (hQ.matrix_det.pow p)) ?_
  rintro y (h | h) <;> simp [h, hp0, hp1]

theorem continuous_Zw {p : ℕ} (hp : 1 ≤ p) (a : ℝ) (S : Finset V) :
    Continuous fun y : (V → ℝ) × (V → ℝ) => Zw G p a y.1 y.2 S := by
  unfold Zw
  exact continuous_finsetSum _ fun σ _ => continuous_wt G hp a σ S

theorem continuousOn_meanPlus {d p : ℕ} (hp : 2 ≤ p) (S : Finset V) (i : V) :
    ContinuousOn (fun y : (V → ℝ) × (V → ℝ) => meanPlus G d p y.1 y.2 S i)
      {y | 0 < Zw G p (aOf d p) y.1 y.2 S} := by
  unfold meanPlus lawE
  refine ContinuousOn.div₀ ?_ (continuous_Zw G (by omega) _ S).continuousOn
    fun y (hy : 0 < _) => hy.ne'
  exact (continuous_finsetSum _ fun σ _ => continuous_wt_mul_hN G hp _ σ S i).continuousOn

end BiluLinial.Tight
