/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecB.Weak
public import BiluLinial.Tight.Tools.Alpha2
public import BiluLinial.Tight.Tools.GaussDensity
public import BiluLinial.Tight.Tools.LogConcaveDet
public import BiluLinial.Tight.Star
public import BiluLinial.Tight.Compare.Multi
public import BiluLinial.Tight.SecA.Ins

/-!
# Weighted fresh-star quadratic domination: definitions and exact lemmas

The definitions and the exact (proved) lemmas of nodes TB.sub, TB.WT3, TB.WT5 of
`docs/tight/BP_SECB.md`; the open analytic leaves are in `SecB/WTRemCore.lean` (TB.WT5r°) and
`SecB/WTRetLaw.lean` (TB.WT5v, TB.WT5l), and the parents in `SecB/WT.lean`, whose module docstring
describes the whole development.
-/

@[expose] public section

namespace BiluLinial.Tight.SecB

open Matrix

universe u

section Raw

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- `P̃^τ` with the incident signs at `i` replaced by a real star vector `x ∈ ℝ^{N_S(i)}`. -/
noncomputable def precSub (a τ : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) (i : V)
    (x : nbhd G S i → ℝ) : Matrix V V ℝ :=
  Matrix.of fun u w =>
    if hu : u = i ∧ w ∈ nbhd G S i then
      τ * a * (Real.sqrt (y u) * Real.sqrt (y w)) * x ⟨w, hu.2⟩
    else if hw : w = i ∧ u ∈ nbhd G S i then
      τ * a * (Real.sqrt (y u) * Real.sqrt (y w)) * x ⟨u, hw.2⟩
    else precN G a τ y σ S u w

open Classical in
/-- The paired weight at the star vector `x`:
`1{P̃⁺(x) ≻ 0, P̃⁻(x) ≻ 0} (det P̃⁺(x) det P̃⁻(x))^p`. -/
noncomputable def wSub (p : ℕ) (a : ℝ) (yp ym : V → ℝ) (σ : Config V) (S : Finset V) (i : V)
    (x : nbhd G S i → ℝ) : ℝ :=
  if (precSub G a 1 yp σ S i x).PosDef ∧ (precSub G a (-1) ym σ S i x).PosDef then
    ((precSub G a 1 yp σ S i x).det * (precSub G a (-1) ym σ S i x).det) ^ p
  else 0

/-- The physical inverse diagonal `y_k ((P̃^τ(x) + zY)⁻¹)_kk` at the star vector `x`
(`z = 0`: unshifted). -/
noncomputable def diagSub (a τ z : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) (i : V)
    (x : nbhd G S i → ℝ) (k : V) : ℝ :=
  y k * (precSub G a τ y σ S i x + z • srcDiag y S)⁻¹ k k

end Raw

/-! ### The gauge flip at `i` and measurability in the star vector -/

section Gauge

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The gauge flip `D = diag(-1 at i, 1 elsewhere)`. -/
noncomputable def flipD (i : V) : Matrix V V ℝ := diagonal fun k => if k = i then -1 else 1

theorem flipD_mul_self (i : V) : flipD i * flipD i = 1 := by
  rw [flipD, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext k
  split_ifs <;> norm_num

theorem flipD_conjTranspose (i : V) : (flipD i)ᴴ = flipD i := by
  rw [flipD, diagonal_conjTranspose, star_trivial]

theorem flipD_conj_apply (i : V) (M : Matrix V V ℝ) (u w : V) :
    (flipD i * M * flipD i) u w =
      (if u = i then -1 else 1) * M u w * (if w = i then -1 else 1) := by
  rw [flipD, Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem flipD_conj_conj (i : V) (M : Matrix V V ℝ) :
    flipD i * (flipD i * M * flipD i) * flipD i = M := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, flipD_mul_self, Matrix.one_mul, Matrix.mul_assoc,
    flipD_mul_self, Matrix.mul_one]

theorem flipD_mulVec_injective (i : V) : Function.Injective (flipD i).mulVec := by
  intro v w h
  have := congrArg (flipD i).mulVec h
  simpa [Matrix.mulVec_mulVec, flipD_mul_self] using this

theorem posDef_flip_iff (i : V) {M : Matrix V V ℝ} :
    (flipD i * M * flipD i).PosDef ↔ M.PosDef := by
  constructor
  · intro h
    have := h.conjTranspose_mul_mul_same (flipD_mulVec_injective i)
    rwa [flipD_conjTranspose, flipD_conj_conj] at this
  · intro h
    have := h.conjTranspose_mul_mul_same (flipD_mulVec_injective i)
    rwa [flipD_conjTranspose] at this

theorem det_flip_conj (i : V) (M : Matrix V V ℝ) : (flipD i * M * flipD i).det = M.det := by
  have h : (flipD i).det * (flipD i).det = 1 := by rw [← det_mul, flipD_mul_self, det_one]
  rw [det_mul, det_mul]
  linear_combination M.det * h

theorem flipD_conj_srcDiag (i : V) (y : V → ℝ) (S : Finset V) :
    flipD i * srcDiag y S * flipD i = srcDiag y S := by
  ext u w
  rw [flipD_conj_apply]
  by_cases h : u = w
  · subst h
    split_ifs <;> ring
  · simp [srcDiag, Matrix.diagonal_apply_ne _ h]

theorem inv_flip_conj_diag (i : V) (Q : Matrix V V ℝ) (k : V) :
    (flipD i * Q * flipD i)⁻¹ k k = Q⁻¹ k k := by
  have hD : (flipD i)⁻¹ = flipD i := Matrix.inv_eq_left_inv (flipD_mul_self i)
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, hD, ← Matrix.mul_assoc, flipD_conj_apply]
  split_ifs <;> ring

theorem nbhd_ne_self {S : Finset V} {i w : V} (hw : w ∈ nbhd G S i) : w ≠ i := fun h => by
  subst h
  exact G.irrefl (Finset.mem_filter.mp hw).2

/-- `P̃(-x) = D P̃(x) D`. -/
theorem precSub_neg (a τ : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) (i : V)
    (x : nbhd G S i → ℝ) :
    precSub G a τ y σ S i (-x) = flipD i * precSub G a τ y σ S i x * flipD i := by
  ext u w
  rw [flipD_conj_apply]
  simp only [precSub, Matrix.of_apply, Pi.neg_apply]
  by_cases h1 : u = i ∧ w ∈ nbhd G S i
  · rw [dif_pos h1, dif_pos h1, if_pos h1.1, if_neg (nbhd_ne_self G h1.2)]
    ring
  · rw [dif_neg h1, dif_neg h1]
    by_cases h2 : w = i ∧ u ∈ nbhd G S i
    · rw [dif_pos h2, dif_pos h2, if_neg (nbhd_ne_self G h2.2), if_pos h2.1]
      ring
    · rw [dif_neg h2, dif_neg h2]
      by_cases hu : u = i
      · by_cases hw : w = i
        · rw [if_pos hu, if_pos hw]
          ring
        · have hw' : w ∉ nbhd G S i := fun h => h1 ⟨hu, h⟩
          have h0 : precN G a τ y σ S u w = 0 := by
            rw [hu]
            simp only [precN, Matrix.of_apply, if_neg (Ne.symm hw)]
            rw [if_neg]
            rintro ⟨-, hwS, hadj⟩
            exact hw' (Finset.mem_filter.mpr ⟨hwS, hadj⟩)
          rw [h0]
          ring
      · by_cases hw : w = i
        · have hu' : u ∉ nbhd G S i := fun h => h2 ⟨hw, h⟩
          have h0 : precN G a τ y σ S u w = 0 := by
            rw [hw]
            simp only [precN, Matrix.of_apply, if_neg hu]
            rw [if_neg]
            rintro ⟨huS, -, hadj⟩
            exact hu' (Finset.mem_filter.mpr ⟨huS, hadj.symm⟩)
          rw [h0]
          ring
        · rw [if_neg hu, if_neg hw]
          ring

theorem diagSub_neg (a τ z : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) (i : V)
    (x : nbhd G S i → ℝ) (k : V) :
    diagSub G a τ z y σ S i (-x) k = diagSub G a τ z y σ S i x k := by
  unfold diagSub
  have e : precSub G a τ y σ S i (-x) + z • srcDiag y S =
      flipD i * (precSub G a τ y σ S i x + z • srcDiag y S) * flipD i := by
    rw [precSub_neg, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
      flipD_conj_srcDiag]
  rw [e, inv_flip_conj_diag]

theorem wSub_neg (p : ℕ) (a : ℝ) (yp ym : V → ℝ) (σ : Config V) (S : Finset V) (i : V)
    (x : nbhd G S i → ℝ) :
    wSub G p a yp ym σ S i (-x) = wSub G p a yp ym σ S i x := by
  have hc : ((precSub G a 1 yp σ S i (-x)).PosDef ∧ (precSub G a (-1) ym σ S i (-x)).PosDef) ↔
      ((precSub G a 1 yp σ S i x).PosDef ∧ (precSub G a (-1) ym σ S i x).PosDef) := by
    rw [precSub_neg, precSub_neg, posDef_flip_iff, posDef_flip_iff]
  unfold wSub
  by_cases h : (precSub G a 1 yp σ S i x).PosDef ∧ (precSub G a (-1) ym σ S i x).PosDef
  · rw [if_pos (hc.mpr h), if_pos h, precSub_neg, precSub_neg, det_flip_conj, det_flip_conj]
  · rw [if_neg (fun h' => h (hc.mp h')), if_neg h]

theorem continuous_precSub (a τ : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) (i : V) :
    Continuous (precSub G a τ y σ S i) := by
  refine continuous_matrix fun u w => ?_
  simp only [precSub, Matrix.of_apply]
  by_cases h1 : u = i ∧ w ∈ nbhd G S i
  · simp only [dif_pos h1]
    exact continuous_const.mul (continuous_apply _)
  · by_cases h2 : w = i ∧ u ∈ nbhd G S i
    · simp only [dif_neg h1, dif_pos h2]
      exact continuous_const.mul (continuous_apply _)
    · simp only [dif_neg h1, dif_neg h2]
      exact continuous_const

omit [Fintype V] in
/-- `x ↦ P̃(x)` is affine: `P̃(z+w) + P̃(z-w) = 2 P̃(z)`. -/
theorem precSub_add_sub (a τ : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) (i : V)
    (z w : nbhd G S i → ℝ) :
    precSub G a τ y σ S i (z + w) + precSub G a τ y σ S i (z - w) =
      (2 : ℝ) • precSub G a τ y σ S i z := by
  ext u v
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, precSub, Matrix.of_apply]
  by_cases h1 : u = i ∧ v ∈ nbhd G S i
  · simp only [dif_pos h1, Pi.add_apply, Pi.sub_apply]
    ring
  · simp only [dif_neg h1]
    by_cases h2 : v = i ∧ u ∈ nbhd G S i
    · simp only [dif_pos h2, Pi.add_apply, Pi.sub_apply]
      ring
    · simp only [dif_neg h2]
      ring

omit [Fintype V] in
theorem posSemidef_smul_srcDiag {y : V → ℝ} (hy : ∀ k, 0 ≤ y k) (S : Finset V) {z : ℝ}
    (hz : 0 ≤ z) : (z • srcDiag y S).PosSemidef := by
  have hD : (srcDiag y S).PosSemidef := Matrix.PosSemidef.diagonal fun k => by
    split_ifs
    · exact hy k
    · exact le_rfl
  exact hD.smul hz

theorem precSub_isHermitian (a τ : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) (i : V)
    (x : nbhd G S i → ℝ) : (precSub G a τ y σ S i x).IsHermitian := by
  refine Matrix.IsHermitian.ext fun u w => ?_
  simp only [precSub, Matrix.of_apply, star_trivial]
  by_cases h1 : u = i ∧ w ∈ nbhd G S i
  · have hw := nbhd_ne_self G h1.2
    rw [dif_neg (fun h => hw h.1), dif_pos h1, dif_pos h1, mul_comm (Real.sqrt (y w))]
  · by_cases h2 : w = i ∧ u ∈ nbhd G S i
    · rw [dif_pos h2, dif_neg h1, dif_pos h2, mul_comm (Real.sqrt (y w))]
    · rw [dif_neg h2, dif_neg h1, dif_neg h1, dif_neg h2]
      simpa using (precN_isHermitian' G a τ y σ S).apply u w

/-- Along a continuous family of symmetric matrices, positive definiteness is an open condition
(the argument of the private `isOpen_posDef` of `Tight/Continuity.lean`). -/
theorem isOpen_setOf_posDef_of_continuous {X n : Type*} [TopologicalSpace X] [Fintype n]
    {P : X → Matrix n n ℝ} (hP : Continuous P) (hPh : ∀ x, (P x).IsHermitian) :
    IsOpen {x | (P x).PosDef} := by
  have hq : Continuous fun q : X × (n → ℝ) => q.2 ⬝ᵥ (P q.1 *ᵥ q.2) :=
    continuous_snd.dotProduct ((hP.comp continuous_fst).matrix_mulVec continuous_snd)
  rw [isOpen_iff_mem_nhds]
  intro x₀ hx₀
  have hev : ∀ᶠ x in nhds x₀, ∀ v ∈ Metric.sphere (0 : n → ℝ) 1, 0 < v ⬝ᵥ (P x *ᵥ v) := by
    refine (isCompact_sphere (0 : n → ℝ) 1).eventually_forall_of_forall_eventually
      (P := fun x v => 0 < v ⬝ᵥ (P x *ᵥ v)) fun v hv => ?_
    have hv0 : v ≠ 0 := by
      rintro rfl
      simp at hv
    have hpos : 0 < v ⬝ᵥ (P x₀ *ᵥ v) := by
      simpa only [star_trivial] using PosDef.dotProduct_mulVec_pos hx₀ hv0
    exact hq.continuousAt.eventually (eventually_gt_nhds hpos)
  filter_upwards [hev] with x hx
  refine PosDef.of_dotProduct_mulVec_pos (hPh x) fun v hv => ?_
  rw [star_trivial]
  have hn : 0 < ‖v‖ := norm_pos_iff.2 hv
  have hw : ‖v‖⁻¹ • v ∈ Metric.sphere (0 : n → ℝ) 1 := by
    simp [norm_smul, hn.ne']
  have h := hx _ hw
  simp only [mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul] at h
  exact pos_of_mul_pos_right (pos_of_mul_pos_right h (inv_nonneg.2 hn.le)) (inv_nonneg.2 hn.le)

theorem measurable_wSub (p : ℕ) (a : ℝ) (yp ym : V → ℝ) (σ : Config V) (S : Finset V)
    (i : V) : Measurable (wSub G p a yp ym σ S i) := by
  have hP := continuous_precSub G a 1 yp σ S i
  have hM := continuous_precSub G a (-1) ym σ S i
  have hU : IsOpen {x | (precSub G a 1 yp σ S i x).PosDef ∧
      (precSub G a (-1) ym σ S i x).PosDef} :=
    (isOpen_setOf_posDef_of_continuous hP (precSub_isHermitian G a 1 yp σ S i)).inter
      (isOpen_setOf_posDef_of_continuous hM (precSub_isHermitian G a (-1) ym σ S i))
  unfold wSub
  exact Measurable.ite hU.measurableSet
    ((hP.matrix_det.mul hM.matrix_det).pow p).measurable measurable_const

theorem measurable_diagSub (a τ z : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) (i k : V) :
    Measurable fun x => diagSub G a τ z y σ S i x k := by
  have hQ : Measurable fun x => precSub G a τ y σ S i x + z • srcDiag y S :=
    ((continuous_precSub G a τ y σ S i).add continuous_const).measurable
  exact measurable_const.mul (measurable_matrix_inv.comp hQ).eval_matrix

end Gauge

section Contact

variable {d p : ℕ} (ct : Contact.{u} d p)

/-- `H₀` at the star vector `x` at `i`. -/
noncomputable def diagWSub (h : ℝ) (i : ct.V) (l : List (ct.V × Bool × Bool))
    (σ : Config ct.V) (x : nbhd ct.G ct.S i → ℝ) : ℝ :=
  (l.map fun t => diagSub ct.G (aOf d p) (if t.2.1 then 1 else -1) (if t.2.2 then h else 0)
    (ct.ySrc t.2.1) σ ct.S i x t.1).prod

/-- `H = H₀ (X_e)_ii² (X₊)_ii²` at the star vector `x` at `i`. -/
noncomputable def wtHSub (h : ℝ) (e : Bool) (i : ct.V) (l : List (ct.V × Bool × Bool))
    (σ : Config ct.V) (x : nbhd ct.G ct.S i → ℝ) : ℝ :=
  diagWSub ct h i l σ x *
    diagSub ct.G (aOf d p) (if e then 1 else -1) h (ct.ySrc e) σ ct.S i x i ^ 2 *
    diagSub ct.G (aOf d p) 1 h ct.yp σ ct.S i x i ^ 2

/-- The kernel `L = TᵀT` of (WT2). -/
noncomputable def kerL (h : ℝ) (e dir : Bool) (i : ct.V) (σ : Config ct.V) :
    Matrix (nbhd ct.G ct.S i) (nbhd ct.G ct.S i) ℝ :=
  (ct.tMap h e dir i σ)ᵀ * ct.tMap h e dir i σ

theorem kerL_posSemidef (h : ℝ) (e dir : Bool) (i : ct.V) (σ : Config ct.V) :
    (kerL ct h e dir i σ).PosSemidef := by
  have := Matrix.posSemidef_conjTranspose_mul_self (ct.tMap h e dir i σ)
  simpa [kerL, Matrix.conjTranspose_eq_transpose_of_trivial] using this

/-- The Gaussian numerator `x_G = Σ_σ 𝖦[W H q_L]/Z` of `E[H q_L]`. -/
noncomputable def gNumQ (h : ℝ) (e dir : Bool) (i : ct.V) (l : List (ct.V × Bool × Bool)) : ℝ :=
  (∑ σ : Config ct.V, gaussE fun x =>
      wSub ct.G p (aOf d p) ct.yp ct.ym σ ct.S i x * wtHSub ct h e i l σ x *
        qForm (kerL ct h e dir i σ) x) / Zw ct.G p (aOf d p) ct.yp ct.ym ct.S

/-- The Gaussian numerator `y_G = Σ_σ tr L · 𝖦[W H]/Z` of `E[H tr L]`. -/
noncomputable def gNumT (h : ℝ) (e dir : Bool) (i : ct.V) (l : List (ct.V × Bool × Bool)) : ℝ :=
  (∑ σ : Config ct.V, (kerL ct h e dir i σ).trace * gaussE fun x =>
      wSub ct.G p (aOf d p) ct.yp ct.ym σ ct.S i x * wtHSub ct h e i l σ x) /
    Zw ct.G p (aOf d p) ct.yp ct.ym ct.S

/-- `x = E[H q_L(ξ)]` (`ξ` the star vector at `i`). -/
noncomputable def massQ (h : ℝ) (e dir : Bool) (i : ct.V) (l : List (ct.V × Bool × Bool)) : ℝ :=
  ct.E fun σ => ct.wtH h e i l σ * qForm (kerL ct h e dir i σ) (rootSigns ct.G σ ct.S i)

/-- `y = E[H tr L]`. -/
noncomputable def massT (h : ℝ) (e dir : Bool) (i : ct.V) (l : List (ct.V × Bool × Bool)) : ℝ :=
  ct.E fun σ => ct.wtH h e i l σ * (kerL ct h e dir i σ).trace

end Contact

/-! ### TB.WT3 -/

/-- **TB.WT3g** (BLmid on the standard Gaussian with constant modulus `I`). For a measurable,
nonnegative, even and midpoint log-concave `φ` (`φ(z+w) φ(z-w) ≤ φ(z)²`) and `T ⪰ 0`:
`𝖦[φ q_T] ≤ tr T · 𝖦 φ`. Proof: BLmid (`integral_quad_le_of_midpoint`) with `ρ = φ e^{-|x|²/2}`
and `K = I` (`gaussWt_midpoint` with `H = 0`), as in `gaussE_qForm_mul_clipProd_le_const`. -/
theorem gaussE_mul_qForm_le_trace {ι : Type*} [Fintype ι] [DecidableEq ι]
    {φ : (ι → ℝ) → ℝ} (hm : Measurable φ) (h0 : ∀ x, 0 ≤ φ x) (he : ∀ x, φ (-x) = φ x)
    (hmid : ∀ z w, φ (z + w) * φ (z - w) ≤ φ z ^ 2) {T : Matrix ι ι ℝ} (hT : T.PosSemidef) :
    gaussE (fun x => φ x * qForm T x) ≤ T.trace * gaussE φ := by
  have hKs : ∀ _z : ι → ℝ, (1 + (0 : Matrix ι ι ℝ)).IsHermitian := fun _ => by
    rw [add_zero]; exact isHermitian_one
  have hKκ : ∀ (_z : ι → ℝ) (w : ι → ℝ), 1 * (w ⬝ᵥ w) ≤ w ⬝ᵥ ((1 + (0 : Matrix ι ι ℝ)) *ᵥ w) := by
    intro _ w
    rw [add_zero, one_mulVec, one_mul]
  have hmid' : ∀ z w, gaussWt φ (z + w) * gaussWt φ (z - w) ≤
      gaussWt φ z ^ 2 * Real.exp (-(w ⬝ᵥ ((1 + (0 : Matrix ι ι ℝ)) *ᵥ w))) :=
    gaussWt_midpoint (H := fun _ => 0) fun z w => by simpa using hmid z w
  have hgm : Measurable (gaussWt φ) := by
    unfold gaussWt
    exact hm.mul (by fun_prop)
  have h := integral_quad_le_of_midpoint (K := fun _ => 1 + (0 : Matrix ι ι ℝ)) hgm
    (gaussWt_nonneg h0) (gaussWt_neg he) measurable_const one_pos hKs hKκ hmid' hT
  rw [MeasureTheory.integral_const_mul] at h
  rw [gaussE_eq, gaussE_eq, mul_left_comm]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have e1 : (fun x => φ x * qForm T x * Real.exp (-(x ⬝ᵥ x) / 2)) =
      fun x => (x ⬝ᵥ (T *ᵥ x)) * gaussWt φ x := by
    funext x; simp only [qForm, gaussWt]; ring
  have e2 : (T * (1 + (0 : Matrix ι ι ℝ))⁻¹).trace = T.trace := by
    rw [add_zero, inv_one, Matrix.mul_one]
  rw [e1, ← e2]
  exact h

section WT3

variable {d p : ℕ} (ct : Contact.{u} d p)

/-- The weight `φ(x) = W(x) H(x)` of TB.WT3 at the star vector `x` at `i` (core fixed). -/
noncomputable def wt3Rho (h : ℝ) (e : Bool) (i : ct.V) (l : List (ct.V × Bool × Bool))
    (σ : Config ct.V) (x : nbhd ct.G ct.S i → ℝ) : ℝ :=
  wSub ct.G p (aOf d p) ct.yp ct.ym σ ct.S i x * wtHSub ct h e i l σ x

theorem ySrc_nonneg (e : Bool) (k : ct.V) : 0 ≤ ct.ySrc e k := by
  cases e <;> simp [Contact.ySrc, (ct.ctx.hyp k).1, (ct.ctx.hym k).1]

/-- **TB.WT3a** (nonnegativity of the weight). On the support both substituted precisions are
positive definite, so every (shifted) inverse diagonal is `≥ 0`. -/
theorem wt3Rho_nonneg {h : ℝ} (hh : 0 ≤ h) (e : Bool) (i : ct.V)
    (l : List (ct.V × Bool × Bool)) (σ : Config ct.V) (x : nbhd ct.G ct.S i → ℝ) :
    0 ≤ wt3Rho ct h e i l σ x := by
  unfold wt3Rho wSub
  split_ifs with hPD
  · obtain ⟨hP, hM⟩ := hPD
    have hdiag : ∀ (τ z : ℝ) (y : ct.V → ℝ), (∀ k, 0 ≤ y k) → 0 ≤ z →
        (precSub ct.G (aOf d p) τ y σ ct.S i x).PosDef →
        ∀ k, 0 ≤ diagSub ct.G (aOf d p) τ z y σ ct.S i x k := by
      intro τ z y hy hz hPy k
      have hD : (srcDiag y ct.S).PosSemidef := Matrix.PosSemidef.diagonal fun k => by
        split_ifs
        · exact hy k
        · exact le_rfl
      exact mul_nonneg (hy k) (hPy.add_posSemidef (hD.smul hz)).inv.posSemidef.diag_nonneg
    have hbr : ∀ br : Bool,
        (precSub ct.G (aOf d p) (if br then 1 else -1) (ct.ySrc br) σ ct.S i x).PosDef := by
      intro br
      cases br
      · simpa [Contact.ySrc] using hM
      · simpa [Contact.ySrc] using hP
    refine mul_nonneg (pow_nonneg (mul_pos hP.det_pos hM.det_pos).le _) ?_
    unfold wtHSub diagWSub
    refine mul_nonneg (mul_nonneg (List.prod_nonneg fun t ht => ?_) (sq_nonneg _)) (sq_nonneg _)
    obtain ⟨⟨k, br, sh⟩, -, rfl⟩ := List.mem_map.mp ht
    refine hdiag _ _ _ (ySrc_nonneg ct br) ?_ (hbr br) k
    split_ifs
    · exact hh
    · exact le_rfl
  · exact le_of_eq (zero_mul _).symm

/-- **TB.WT3b** (evenness of the weight; open). `φ(-x) = φ(x)`. Sketch: with
`D = diag(-1 at i, 1 elsewhere)`, `P̃^τ(-x) = D P̃^τ(x) D` (only the entries `(i, j)`, `j ∈ J`,
change sign; the other entries of row `i` vanish), and `D (Y) D = Y` for the diagonal source
matrix; so positive definiteness, determinants and every (shifted) inverse diagonal
`((D Q D)⁻¹)_kk = (D Q⁻¹ D)_kk = (Q⁻¹)_kk` are unchanged. Checked numerically (exact). -/
theorem wt3Rho_even (h : ℝ) (e : Bool) (i : ct.V) (l : List (ct.V × Bool × Bool))
    (σ : Config ct.V) (x : nbhd ct.G ct.S i → ℝ) :
    wt3Rho ct h e i l σ (-x) = wt3Rho ct h e i l σ x := by
  unfold wt3Rho wtHSub diagWSub
  rw [wSub_neg]
  simp only [diagSub_neg]

/-- **TB.WT3c** (measurability of the weight; open). Sketch: `x ↦ P̃^τ(x)` is continuous (affine)
and symmetric, so `{x | P̃⁺(x) ≻ 0, P̃⁻(x) ≻ 0}` is open (the argument of the private
`isOpen_posDef` of `Tight/Continuity.lean`: the quadratic form is positive on the compact unit
sphere at `x₀`, hence nearby); `det` is continuous; the inverse diagonals are measurable
(`measurable_matrix_inv`, `Tight/Gauss/BLmid.lean`); the list product is measurable by induction. -/
theorem wt3Rho_measurable (h : ℝ) (e : Bool) (i : ct.V) (l : List (ct.V × Bool × Bool))
    (σ : Config ct.V) : Measurable (wt3Rho ct h e i l σ) := by
  have hl : ∀ l' : List (ct.V × Bool × Bool), Measurable fun x => diagWSub ct h i l' σ x := by
    intro l'
    induction l' with
    | nil => simp only [diagWSub, List.map_nil, List.prod_nil]; exact measurable_const
    | cons t l' ih =>
      simp only [diagWSub, List.map_cons, List.prod_cons] at ih ⊢
      exact (measurable_diagSub ct.G _ _ _ _ σ ct.S i _).mul ih
  unfold wt3Rho wtHSub
  exact (measurable_wSub ct.G p (aOf d p) ct.yp ct.ym σ ct.S i).mul
    (((hl l).mul ((measurable_diagSub ct.G _ _ _ _ σ ct.S i i).pow_const 2)).mul
      ((measurable_diagSub ct.G _ _ _ _ σ ct.S i i).pow_const 2))

/-- The support `{x | P̃⁺(x) ≻ 0, P̃⁻(x) ≻ 0}` of the paired weight at the star vector at `i`. -/
def wtSupp (σ : Config ct.V) (i : ct.V) : Set (nbhd ct.G ct.S i → ℝ) :=
  {x | (precSub ct.G (aOf d p) 1 ct.yp σ ct.S i x).PosDef ∧
    (precSub ct.G (aOf d p) (-1) ct.ym σ ct.S i x).PosDef}

/-- `D(x) = det P̃⁺(x) det P̃⁻(x)`. -/
noncomputable def wtDet (σ : Config ct.V) (i : ct.V) (x : nbhd ct.G ct.S i → ℝ) : ℝ :=
  (precSub ct.G (aOf d p) 1 ct.yp σ ct.S i x).det *
    (precSub ct.G (aOf d p) (-1) ct.ym σ ct.S i x).det

/-- The diagonal factor `g_t(x)` of `H`, `t = (k, branch, shifted)`, at the star vector `x`. -/
noncomputable def wtDiag (h : ℝ) (i : ct.V) (σ : Config ct.V) (t : ct.V × Bool × Bool)
    (x : nbhd ct.G ct.S i → ℝ) : ℝ :=
  diagSub ct.G (aOf d p) (if t.2.1 then 1 else -1) (if t.2.2 then h else 0) (ct.ySrc t.2.1) σ
    ct.S i x t.1

/-- The support is midpoint convex. -/
theorem wtSupp_midpoint {σ : Config ct.V} {i : ct.V} {z w : nbhd ct.G ct.S i → ℝ}
    (h1 : z + w ∈ wtSupp ct σ i) (h2 : z - w ∈ wtSupp ct σ i) : z ∈ wtSupp ct σ i :=
  ⟨posDef_of_add_eq_two_smul h1.1 h2.1 (precSub_add_sub _ _ _ _ _ _ _ z w),
    posDef_of_add_eq_two_smul h1.2 h2.2 (precSub_add_sub _ _ _ _ _ _ _ z w)⟩

/-- `D` is midpoint log-concave on the support. -/
theorem midLC_wtDet (σ : Config ct.V) (i : ct.V) : MidLC (wtSupp ct σ i) (wtDet ct σ i) :=
  (midLC_det (precSub_add_sub _ _ _ _ σ ct.S i) fun _ hx => hx.1).mul
    (midLC_det (precSub_add_sub _ _ _ _ σ ct.S i) fun _ hx => hx.2)

/-- `D g_t` is midpoint log-concave on the support: with `b` the branch of `t`,
`D g_t = y_k det P̃^{-b} · det P̃^b ((P̃^b + zY)⁻¹)_kk`. -/
theorem midLC_wtDet_mul_wtDiag {h : ℝ} (hh : 0 ≤ h) (σ : Config ct.V) (i : ct.V)
    (t : ct.V × Bool × Bool) :
    MidLC (wtSupp ct σ i) fun x => wtDet ct σ i x * wtDiag ct h i σ t x := by
  obtain ⟨k, b, sh⟩ := t
  have hz : (0 : ℝ) ≤ if sh = true then h else 0 := by
    split_ifs
    · exact hh
    · exact le_rfl
  have hyp : ∀ k, 0 ≤ ct.yp k := fun k => (ct.ctx.hyp k).1
  have hym : ∀ k, 0 ≤ ct.ym k := fun k => (ct.ctx.hym k).1
  cases b
  · have e : (fun x => wtDet ct σ i x * wtDiag ct h i σ (k, false, sh) x) = fun x =>
        ct.ym k * ((precSub ct.G (aOf d p) 1 ct.yp σ ct.S i x).det *
          ((precSub ct.G (aOf d p) (-1) ct.ym σ ct.S i x).det *
            (precSub ct.G (aOf d p) (-1) ct.ym σ ct.S i x +
              (if sh = true then h else 0) • srcDiag ct.ym ct.S)⁻¹ k k)) := by
      funext x
      simp only [wtDet, wtDiag, diagSub, Contact.ySrc, Bool.false_eq_true, ↓reduceIte]
      ring
    rw [e]
    exact (MidLC.const (hym k)).mul ((midLC_det (precSub_add_sub _ _ _ _ σ ct.S i)
      fun _ hx => hx.1).mul (midLC_det_mul_inv_diag (precSub_add_sub _ _ _ _ σ ct.S i)
        (fun _ hx => hx.2) (posSemidef_smul_srcDiag hym ct.S hz) k))
  · have e : (fun x => wtDet ct σ i x * wtDiag ct h i σ (k, true, sh) x) = fun x =>
        ct.yp k * ((precSub ct.G (aOf d p) (-1) ct.ym σ ct.S i x).det *
          ((precSub ct.G (aOf d p) 1 ct.yp σ ct.S i x).det *
            (precSub ct.G (aOf d p) 1 ct.yp σ ct.S i x +
              (if sh = true then h else 0) • srcDiag ct.yp ct.S)⁻¹ k k)) := by
      funext x
      simp only [wtDet, wtDiag, diagSub, Contact.ySrc, ↓reduceIte]
      ring
    rw [e]
    exact (MidLC.const (hyp k)).mul ((midLC_det (precSub_add_sub _ _ _ _ σ ct.S i)
      fun _ hx => hx.2).mul (midLC_det_mul_inv_diag (precSub_add_sub _ _ _ _ σ ct.S i)
        (fun _ hx => hx.1) (posSemidef_smul_srcDiag hyp ct.S hz) k))

theorem wt3Rho_eq_zero_of_not_mem {h : ℝ} {e : Bool} {i : ct.V} {l : List (ct.V × Bool × Bool)}
    {σ : Config ct.V} {x : nbhd ct.G ct.S i → ℝ} (hx : x ∉ wtSupp ct σ i) :
    wt3Rho ct h e i l σ x = 0 := by
  have hx' : ¬((precSub ct.G (aOf d p) 1 ct.yp σ ct.S i x).PosDef ∧
      (precSub ct.G (aOf d p) (-1) ct.ym σ ct.S i x).PosDef) := hx
  unfold wt3Rho wSub
  rw [if_neg hx', zero_mul]

/-- On the support, `W H = D^{p-|L|} Π_{t ∈ L} (D g_t)` with
`L = H₀ ++ [(i,e,sh), (i,e,sh), (i,+,sh), (i,+,sh)]`. -/
theorem wt3Rho_eq_of_mem {h : ℝ} (e : Bool) (i : ct.V) (l : List (ct.V × Bool × Bool))
    (hl : l.length + 4 ≤ p) {σ : Config ct.V} {x : nbhd ct.G ct.S i → ℝ}
    (hx : x ∈ wtSupp ct σ i) :
    wt3Rho ct h e i l σ x = wtDet ct σ i x ^ (p - (l.length + 4)) *
      ((l ++ [(i, e, true), (i, e, true), (i, true, true), (i, true, true)]).map fun t =>
        wtDet ct σ i x * wtDiag ct h i σ t x).prod := by
  have hx' : (precSub ct.G (aOf d p) 1 ct.yp σ ct.S i x).PosDef ∧
      (precSub ct.G (aOf d p) (-1) ct.ym σ ct.S i x).PosDef := hx
  have hw : wSub ct.G p (aOf d p) ct.yp ct.ym σ ct.S i x = wtDet ct σ i x ^ p := by
    unfold wSub
    rw [if_pos hx']
    rfl
  have hH : wtHSub ct h e i l σ x = (l.map fun t => wtDiag ct h i σ t x).prod *
      wtDiag ct h i σ (i, e, true) x ^ 2 * wtDiag ct h i σ (i, true, true) x ^ 2 := by
    simp only [wtHSub, diagWSub, wtDiag, Contact.ySrc, ↓reduceIte]
  rw [List.prod_map_mul, List.map_const', List.prod_replicate]
  simp only [List.map_append, List.prod_append, List.map_cons, List.prod_cons, List.map_nil,
    List.prod_nil, List.length_append, List.length_cons, List.length_nil]
  unfold wt3Rho
  rw [hw, hH]
  rw [show wtDet ct σ i x ^ p =
      wtDet ct σ i x ^ (p - (l.length + 4)) * wtDet ct σ i x ^ (l.length + 4) by
    rw [← pow_add, Nat.sub_add_cancel hl]]
  ring

/-- **TB.WT3d** (midpoint log-concavity of the weight). If `|H₀| + 4 ≤ p`:
`φ(z+w) φ(z-w) ≤ φ(z)²`. Proof (AUDIT-B §2.5, (X6); elementary route,
`Tight/Tools/LogConcaveDet.lean`): the support is midpoint convex (`wtSupp_midpoint`), so if one
of `z ± w` is unsupported the left side is `0`. On the support
`φ = D^{p-|L|} Π_{t ∈ L} (D g_t)` (`wt3Rho_eq_of_mem`; `|L| = |H₀| + 4 ≤ p`), and each factor is
midpoint log-concave along the affine family `x ↦ P̃(x)`: `D` by `det A₁ det A₂ ≤ (det A)²`
(`det_mul_det_le_det_sq`), and `D g_t = y_k det P̃^{-b} · det P̃^b ((P̃^b + zY)⁻¹)_kk` by
`det_mul_inv_diag_midpoint` (Cramer, `det P / det(P + zY) = det(I - B(P + zY)⁻¹Bᵀ)` and the
midpoint operator convexity of the inverse). Products of nonnegative midpoint log-concave
functions are midpoint log-concave (`MidLC`). Checked numerically on a 6-vertex graph with
`|H₀| = 4` (worst log-gap `-0.021` over 2756 supported pairs) and the matrix lemmas on 20000
random instances. -/
theorem wt3Rho_midpoint {h : ℝ} (hh : 0 ≤ h) (e : Bool) (i : ct.V)
    (l : List (ct.V × Bool × Bool)) (hl : l.length + 4 ≤ p) (σ : Config ct.V)
    (z w : nbhd ct.G ct.S i → ℝ) :
    wt3Rho ct h e i l σ (z + w) * wt3Rho ct h e i l σ (z - w) ≤ wt3Rho ct h e i l σ z ^ 2 := by
  by_cases h12 : z + w ∈ wtSupp ct σ i ∧ z - w ∈ wtSupp ct σ i
  · have hF := ((midLC_wtDet ct σ i).pow (p - (l.length + 4))).mul
      (MidLC.list_prod _ (l ++ [(i, e, true), (i, e, true), (i, true, true), (i, true, true)])
        fun t _ => midLC_wtDet_mul_wtDiag ct hh σ i t)
    rw [wt3Rho_eq_of_mem ct e i l hl h12.1, wt3Rho_eq_of_mem ct e i l hl h12.2,
      wt3Rho_eq_of_mem ct e i l hl (wtSupp_midpoint ct h12.1 h12.2)]
    exact hF.2 z w h12.1 h12.2
  · have h0 : wt3Rho ct h e i l σ (z + w) * wt3Rho ct h e i l σ (z - w) = 0 := by
      by_cases h1 : z + w ∈ wtSupp ct σ i
      · rw [wt3Rho_eq_zero_of_not_mem ct fun h2 => h12 ⟨h1, h2⟩, mul_zero]
      · rw [wt3Rho_eq_zero_of_not_mem ct h1, zero_mul]
    rw [h0]
    exact sq_nonneg _

end WT3

/-- **TB.WT3** (weighted Gaussian step). For every signing (core fixed), when the
weight has at most `p - 4` diagonal factors besides `(X_e)_ii² (X₊)_ii²`:
`𝖦[W H q_L] ≤ tr L · 𝖦[W H]`. Proof: TB.WT3g applied to `φ = W H` (TB.WT3a–d) and
`T = L ⪰ 0`. -/
theorem wt3_gauss {d p : ℕ} (ct : Contact.{u} d p) {h : ℝ} (hh : 0 ≤ h) (e dir : Bool)
    {i : ct.V} (hi : i ∈ ct.N) (l : List (ct.V × Bool × Bool)) (hl : l.length + 4 ≤ p)
    (σ : Config ct.V) :
    gaussE (fun x => wSub ct.G p (aOf d p) ct.yp ct.ym σ ct.S i x * wtHSub ct h e i l σ x *
        qForm (kerL ct h e dir i σ) x) ≤
      (kerL ct h e dir i σ).trace *
        gaussE (fun x => wSub ct.G p (aOf d p) ct.yp ct.ym σ ct.S i x * wtHSub ct h e i l σ x) :=
  gaussE_mul_qForm_le_trace (wt3Rho_measurable ct h e i l σ) (wt3Rho_nonneg ct hh e i l σ)
    (wt3Rho_even ct h e i l σ) (wt3Rho_midpoint ct hh e i l hl σ) (kerL_posSemidef ct h e dir i σ)

theorem wtH_nonneg {d p : ℕ} (ct : Contact.{u} d p) {h : ℝ} (hh : 0 ≤ h) (e : Bool) (i : ct.V)
    (l : List (ct.V × Bool × Bool)) {σ : Config ct.V}
    (hσ : wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0) : 0 ≤ ct.wtH h e i l σ := by
  obtain ⟨hpP, hpM⟩ := posDef_of_wt_ne_zero ct.G hσ
  have hyp : ∀ k, 0 ≤ ct.yp k := fun k => (ct.ctx.hyp k).1
  have hym : ∀ k, 0 ≤ ct.ym k := fun k => (ct.ctx.hym k).1
  have hdiag : ∀ (k : ct.V) (e' sh : Bool), 0 ≤ ct.diagB h σ k e' sh := by
    intro k e' sh
    cases e' <;> cases sh
    · exact (diag_nonneg_of_posDef ct.G hpM hym hh k).1
    · exact (diag_nonneg_of_posDef ct.G hpM hym hh k).2
    · exact (diag_nonneg_of_posDef ct.G hpP hyp hh k).1
    · exact (diag_nonneg_of_posDef ct.G hpP hyp hh k).2
  unfold Contact.wtH Contact.diagW
  refine mul_nonneg (mul_nonneg (List.prod_nonneg fun x hx => ?_) (sq_nonneg _)) (sq_nonneg _)
  obtain ⟨t, -, rfl⟩ := List.mem_map.mp hx
  exact hdiag _ _ _

section InsGeneric

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `bᵀ (coreOf Q v)⁻¹ b` only sees the block off `v` when `b v = 0`. -/
theorem quadForm_coreOf {Q : Matrix V V ℝ} {v : V} (hQ : Q.IsHermitian)
    (hD : (delVertex Q v).PosDef) {b : V → ℝ} (hb : b v = 0) :
    b ⬝ᵥ ((SecA.coreOf Q v)⁻¹ *ᵥ b) =
      (fun w : {w // w ≠ v} => b w) ⬝ᵥ
        ((delVertex Q v)⁻¹ *ᵥ fun w : {w // w ≠ v} => b w) := by
  have hM : (SecA.coreOf Q v).PosDef := by
    rw [vertexSchur_posDef_iff (SecA.coreOf_isHermitian hQ v)
      (by rwa [SecA.delVertex_coreOf]), SecA.vertexSchur_coreOf]
    exact one_pos
  have hDu : IsUnit (delVertex Q v).det := (isUnit_iff_isUnit_det _).mp hD.isUnit
  have hMu : IsUnit (SecA.coreOf Q v).det := (isUnit_iff_isUnit_det _).mp hM.isUnit
  set z := (delVertex Q v)⁻¹ *ᵥ fun w : {w // w ≠ v} => b w with hz
  have hDz : delVertex Q v *ᵥ z = fun w : {w // w ≠ v} => b w := by
    rw [hz, mulVec_mulVec, mul_nonsing_inv _ hDu, one_mulVec]
  let x : V → ℝ := fun w => if h : w = v then 0 else z ⟨w, h⟩
  have hxv : x v = 0 := by simp [x]
  have hx : ∀ w : {w // w ≠ v}, x w = z w := fun w => by simp [x, w.2]
  have hMx : SecA.coreOf Q v *ᵥ x = b := by
    funext u
    rw [mulVec, dotProduct, Fintype.sum_eq_add_sum_subtype_ne _ v, hxv, mul_zero, zero_add]
    simp only [hx]
    by_cases hu : u = v
    · rw [hu, hb]
      exact Finset.sum_eq_zero fun w _ => by simp [SecA.coreOf, Ne.symm w.2]
    · refine Eq.trans ?_ (congrFun hDz (⟨u, hu⟩ : {w // w ≠ v}))
      simp only [mulVec, dotProduct, delVertex, submatrix_apply]
      refine Finset.sum_congr rfl fun w _ => ?_
      simp [SecA.coreOf, hu, w.2]
  have hinv : (SecA.coreOf Q v)⁻¹ *ᵥ b = x := by
    calc (SecA.coreOf Q v)⁻¹ *ᵥ b = (SecA.coreOf Q v)⁻¹ *ᵥ (SecA.coreOf Q v *ᵥ x) := by
          rw [hMx]
      _ = x := by rw [mulVec_mulVec, nonsing_inv_mul _ hMu, one_mulVec]
  rw [hinv]
  simp only [dotProduct]
  rw [Fintype.sum_eq_add_sum_subtype_ne _ v, hxv, mul_zero, zero_add]
  simp only [hx]

/-- Vertex insertion for a symmetric matrix with a positive definite core: with
`s = Q_vv - bᵀ (coreOf Q v)⁻¹ b`, `Q ≻ 0 ↔ s > 0` and `det Q = det (coreOf Q v) · s`. -/
theorem ins_generic {Q : Matrix V V ℝ} {v : V} (hQ : Q.IsHermitian)
    (hC : (SecA.coreOf Q v).PosDef) :
    (Q.PosDef ↔
        0 < Q v v - SecA.colOf Q v ⬝ᵥ ((SecA.coreOf Q v)⁻¹ *ᵥ SecA.colOf Q v)) ∧
      Q.det = (SecA.coreOf Q v).det *
        (Q v v - SecA.colOf Q v ⬝ᵥ ((SecA.coreOf Q v)⁻¹ *ᵥ SecA.colOf Q v)) := by
  have hD : (delVertex Q v).PosDef := by
    rw [← SecA.delVertex_coreOf]
    exact hC.submatrix Subtype.val_injective
  have hs : vertexSchur Q v =
      Q v v - SecA.colOf Q v ⬝ᵥ ((SecA.coreOf Q v)⁻¹ *ᵥ SecA.colOf Q v) := by
    rw [quadForm_coreOf hQ hD (by simp [SecA.colOf])]
    have h : (fun w : {w // w ≠ v} => SecA.colOf Q v w) = fun w : {w // w ≠ v} => Q w v :=
      funext fun w => by simp [SecA.colOf, w.2]
    rw [h]
    rfl
  have hdet : (SecA.coreOf Q v).det = (delVertex Q v).det := by
    rw [vertexSchur_det (SecA.coreOf_isHermitian hQ v) (by rwa [SecA.delVertex_coreOf]),
      SecA.vertexSchur_coreOf, SecA.delVertex_coreOf, mul_one]
  refine ⟨?_, ?_⟩
  · rw [vertexSchur_posDef_iff hQ hD, hs]
  · rw [vertexSchur_det hQ hD, hs, hdet]

end InsGeneric

section InsStar

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

omit [Fintype V] in
theorem coreOf_precSub (a τ : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) (i : V)
    (x : nbhd G S i → ℝ) :
    SecA.coreOf (precSub G a τ y σ S i x) i = precCore G a τ y σ S i := by
  ext u w
  simp only [SecA.coreOf, precCore, precSub, Matrix.of_apply]
  by_cases h : u = i ∨ w = i
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]
    obtain ⟨hu, hw⟩ := not_or.1 h
    rw [dif_neg fun h' => hu h'.1, dif_neg fun h' => hw h'.1]

theorem precSub_apply_root {a τ : ℝ} {y : V → ℝ} {σ : Config V} {S : Finset V} {i : V}
    (hi : i ∈ S) (x : nbhd G S i → ℝ) : precSub G a τ y σ S i x i i = diagD G a y S i := by
  have hni : i ∉ nbhd G S i := fun h => nbhd_ne_self G h rfl
  simp [precSub, precN, hni, hi]

/-- The zero extension of a star vector. -/
noncomputable def extStar {S : Finset V} {i : V} (x : nbhd G S i → ℝ) : V → ℝ :=
  fun w => if hw : w ∈ nbhd G S i then x ⟨w, hw⟩ else 0

theorem colOf_precSub (a τ : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) (i : V)
    (x : nbhd G S i → ℝ) :
    SecA.colOf (precSub G a τ y σ S i x) i =
      fun w => τ * a * Real.sqrt (y i) * (Real.sqrt (y w) * extStar G x w) := by
  funext w
  simp only [SecA.colOf, extStar]
  by_cases hwi : w = i
  · have hni : i ∉ nbhd G S i := fun h => nbhd_ne_self G h rfl
    rw [if_pos hwi, hwi, dif_neg hni, mul_zero, mul_zero]
  · rw [if_neg hwi, precSub, Matrix.of_apply]
    rw [dif_neg fun h => hwi h.1]
    by_cases hw : w ∈ nbhd G S i
    · rw [dif_pos ⟨rfl, hw⟩, dif_pos hw]
      ring
    · rw [dif_neg fun h => hw h.2, dif_neg hw, mul_zero, mul_zero]
      simp only [precN, Matrix.of_apply, if_neg hwi]
      rw [if_neg]
      rintro ⟨hwS, -, hadj⟩
      exact hw (Finset.mem_filter.2 ⟨hwS, hadj.symm⟩)

theorem sum_extStar {S : Finset V} {i : V} (x : nbhd G S i → ℝ) (f : V → ℝ) :
    ∑ w, extStar G x w * f w = ∑ j : nbhd G S i, x j * f j := by
  rw [← Finset.sum_subset (Finset.subset_univ (nbhd G S i)) fun w _ hw => by
    simp [extStar, hw], ← Finset.sum_coe_sort (nbhd G S i)]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [extStar, j.2]

/-- The root quadratic form at a real star vector: `bᵀ M⁻¹ b = D_i q_A(x)`. -/
theorem colOf_precSub_quad {a τ : ℝ} (hτ : τ ^ 2 = 1) {y : V → ℝ} (hy : ∀ k, 0 ≤ y k)
    (σ : Config V) {S : Finset V} {i : V} (x : nbhd G S i → ℝ) :
    SecA.colOf (precSub G a τ y σ S i x) i ⬝ᵥ
        ((precCore G a τ y σ S i)⁻¹ *ᵥ SecA.colOf (precSub G a τ y σ S i x) i) =
      diagD G a y S i * qForm (rootMat G a τ y σ S i) x := by
  have hD : 0 < diagD G a y S i := by
    have h1 : 0 ≤ ∑ j ∈ nbhd G S i, cEdge a y i j := Finset.sum_nonneg fun j _ =>
      FloorIns.cRoot_nonneg (mul_nonneg (mul_nonneg (sq_nonneg a) (hy i)) (hy j))
    unfold diagD
    linarith
  have hc : (τ * a * Real.sqrt (y i)) ^ 2 = a ^ 2 * y i := by
    rw [mul_pow, mul_pow, hτ, Real.sq_sqrt (hy i), one_mul]
  rw [colOf_precSub]
  set C := (precCore G a τ y σ S i)⁻¹
  set c := τ * a * Real.sqrt (y i)
  have hL : (fun w => c * (Real.sqrt (y w) * extStar G x w)) ⬝ᵥ
      (C *ᵥ fun w => c * (Real.sqrt (y w) * extStar G x w)) =
      ∑ j : nbhd G S i, x j * ∑ l : nbhd G S i, x l *
        (c ^ 2 * (Real.sqrt (y j) * C j l * Real.sqrt (y l))) := by
    simp only [dotProduct, mulVec]
    have e1 : ∀ w, c * (Real.sqrt (y w) * extStar G x w) *
        ∑ w', C w w' * (c * (Real.sqrt (y w') * extStar G x w')) =
        extStar G x w * ∑ w', extStar G x w' *
          (c ^ 2 * (Real.sqrt (y w) * C w w' * Real.sqrt (y w'))) := by
      intro w
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun w' _ => ?_
      ring
    have e2 : ∀ w, ∑ w', extStar G x w' *
        (c ^ 2 * (Real.sqrt (y w) * C w w' * Real.sqrt (y w'))) =
        ∑ l : nbhd G S i, x l * (c ^ 2 * (Real.sqrt (y w) * C w l * Real.sqrt (y l))) :=
      fun w => sum_extStar G x _
    simp only [e1, e2]
    exact sum_extStar G x (fun w => ∑ l : nbhd G S i, x l *
      (c ^ 2 * (Real.sqrt (y w) * C w l * Real.sqrt (y l))))
  rw [hL, qForm]
  simp only [dotProduct, mulVec, rootMat, coreGreen, Matrix.of_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  rw [hc]
  field_simp
  ring

/-- **Insertion at a real star vector** (one branch): given the core `M ≻ 0`,
`P̃(x) ≻ 0 ↔ q(x) < 1` and `det P̃(x) = det M · D_i (1 - q(x))`, `q = q_A`. -/
theorem precSub_ins {a τ : ℝ} (hτ : τ ^ 2 = 1) {y : V → ℝ} (hy : ∀ k, 0 ≤ y k)
    (σ : Config V) {S : Finset V} {i : V} (hi : i ∈ S) (x : nbhd G S i → ℝ)
    (hM : (precCore G a τ y σ S i).PosDef) :
    ((precSub G a τ y σ S i x).PosDef ↔ qForm (rootMat G a τ y σ S i) x < 1) ∧
      (precSub G a τ y σ S i x).det =
        (precCore G a τ y σ S i).det *
          (diagD G a y S i * (1 - qForm (rootMat G a τ y σ S i) x)) := by
  have hD : 0 < diagD G a y S i := by
    have h1 : 0 ≤ ∑ j ∈ nbhd G S i, cEdge a y i j := Finset.sum_nonneg fun j _ =>
      FloorIns.cRoot_nonneg (mul_nonneg (mul_nonneg (sq_nonneg a) (hy i)) (hy j))
    unfold diagD
    linarith
  have hC : (SecA.coreOf (precSub G a τ y σ S i x) i).PosDef := by
    rwa [coreOf_precSub]
  obtain ⟨h1, h2⟩ := ins_generic (precSub_isHermitian G a τ y σ S i x) hC
  rw [coreOf_precSub, precSub_apply_root G hi, colOf_precSub_quad G hτ hy σ x] at h1 h2
  have hs : diagD G a y S i - diagD G a y S i * qForm (rootMat G a τ y σ S i) x =
      diagD G a y S i * (1 - qForm (rootMat G a τ y σ S i) x) := by ring
  rw [hs] at h1 h2
  refine ⟨h1.trans ?_, h2⟩
  constructor
  · intro h
    by_contra hq
    nlinarith [not_lt.1 hq]
  · intro h
    exact mul_pos hD (by linarith)

/-- **Insertion at a real star vector**: `W(x) = W_core (D⁺_i D⁻_i)^p Φ(x)` for every `x ∈ ℝ^J`,
`Φ = α₊^p β₊^p` with the root matrices at `i`. -/
theorem wSub_eq_star {p : ℕ} (hp : 1 ≤ p) (a : ℝ) {yp ym : V → ℝ} (hyp : ∀ k, 0 ≤ yp k)
    (hym : ∀ k, 0 ≤ ym k) (σ : Config V) {S : Finset V} {i : V} (hi : i ∈ S)
    (x : nbhd G S i → ℝ) :
    wSub G p a yp ym σ S i x =
      wtCore G p a yp ym σ S i * (diagD G a yp S i * diagD G a ym S i) ^ p *
        starPhi p (rootMat G a 1 yp σ S i) (rootMat G a (-1) ym σ S i) x := by
  unfold wSub wtCore starPhi clipF
  by_cases hM : (precCore G a 1 yp σ S i).PosDef ∧ (precCore G a (-1) ym σ S i).PosDef
  · obtain ⟨hpA, hdA⟩ := precSub_ins G (a := a) (τ := 1) (by norm_num) hyp σ hi x hM.1
    obtain ⟨hpB, hdB⟩ := precSub_ins G (a := a) (τ := -1) (by norm_num) hym σ hi x hM.2
    rw [if_pos hM]
    by_cases hq : qForm (rootMat G a 1 yp σ S i) x < 1 ∧ qForm (rootMat G a (-1) ym σ S i) x < 1
    · rw [if_pos ⟨hpA.2 hq.1, hpB.2 hq.2⟩, hdA, hdB, max_eq_left (by linarith [hq.1]),
        max_eq_left (by linarith [hq.2])]
      simp only [mul_pow]
      ring
    · rw [if_neg fun h => hq ⟨hpA.1 h.1, hpB.1 h.2⟩]
      rcases not_and_or.1 hq with h | h
      · rw [max_eq_right (show 1 - qForm (rootMat G a 1 yp σ S i) x ≤ 0 by linarith [not_lt.1 h]),
          zero_pow (by omega), zero_mul, mul_zero]
      · rw [max_eq_right (show 1 - qForm (rootMat G a (-1) ym σ S i) x ≤ 0 by
          linarith [not_lt.1 h]), zero_pow (by omega), mul_zero, mul_zero]
  · rw [if_neg hM, zero_mul, zero_mul, if_neg]
    rintro ⟨h1, h2⟩
    refine hM ⟨?_, ?_⟩
    · have := SecA.coreOf_posDef h1 i
      rwa [coreOf_precSub] at this
    · have := SecA.coreOf_posDef h2 i
      rwa [coreOf_precSub] at this

end InsStar

section Linear

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem pderiv_const_mul (i : ι) (c : ℝ) (f : (ι → ℝ) → ℝ) :
    pderiv i (fun x => c * f x) = fun x => c * pderiv i f x := by
  funext x
  have e : (fun x => c * f x) = c • f := by
    funext y
    simp [smul_eq_mul]
  simp only [pderiv, e, fderiv_const_smul_field, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rfl

theorem pderivList_const_mul (l : List ι) (c : ℝ) (f : (ι → ℝ) → ℝ) :
    pderivList l (fun x => c * f x) = fun x => c * pderivList l f x := by
  induction l generalizing f with
  | nil => rfl
  | cons i l ih => simp only [pderivList_cons, pderiv_const_mul, ih]

theorem dEven_const_mul (l : List ι) (j : ι → ℕ) (c : ℝ) (f : (ι → ℝ) → ℝ) :
    dEven l j (fun x => c * f x) = fun x => c * dEven l j f x :=
  pderivList_const_mul _ c f

theorem gaussE_const_mul (c : ℝ) (f : (ι → ℝ) → ℝ) :
    gaussE (fun x => c * f x) = c * gaussE f := by
  unfold gaussE
  exact MeasureTheory.integral_const_mul c f

theorem radE_const_mul (c : ℝ) (f : (ι → ℝ) → ℝ) :
    radE (fun x => c * f x) = c * radE f := by
  unfold radE
  exact MeasureTheory.integral_const_mul c f

end Linear

section StarSigns

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- At a sign vector `ξ`, the substituted precision is the precision of the signing whose root
edges at `i` carry the signs of `ξ`. -/
theorem precSub_setRoot (a τ : ℝ) (y : V → ℝ) (σ : Config V) {S : Finset V} {i : V}
    (hi : i ∈ S) {ξ : nbhd G S i → ℝ} (hξ : ∀ j, ξ j = 1 ∨ ξ j = -1) :
    precSub G a τ y σ S i ξ = precN G a τ y (setRoot G S i σ ξ) S := by
  ext u w
  simp only [precSub, precN, Matrix.of_apply]
  by_cases h1 : u = i ∧ w ∈ nbhd G S i
  · have hne : u ≠ w := fun h => nbhd_ne_self G h1.2 (h.symm.trans h1.1)
    have hwS := Finset.mem_filter.1 h1.2
    have huS : u ∈ S := by rw [h1.1]; exact hi
    have hadj : G.Adj u w := by rw [h1.1]; exact hwS.2
    rw [dif_pos h1, if_neg hne, if_pos ⟨huS, hwS.1, hadj⟩]
    have hw := h1.2
    have hs : sgn (setRoot G S i σ ξ) u w = ξ ⟨w, hw⟩ := by
      have he : s(u, w) = s(i, ((⟨w, hw⟩ : nbhd G S i) : V)) := by rw [h1.1]
      unfold sgn
      rw [he, setRoot_apply_root G σ ξ ⟨w, hw⟩]
      rcases hξ ⟨w, hw⟩ with h | h <;> norm_num [h]
    rw [hs]
  · rw [dif_neg h1]
    by_cases h2 : w = i ∧ u ∈ nbhd G S i
    · have hne : u ≠ w := fun h => nbhd_ne_self G h2.2 (h.trans h2.1)
      have huS := Finset.mem_filter.1 h2.2
      have hwS : w ∈ S := by rw [h2.1]; exact hi
      have hadj : G.Adj u w := by rw [h2.1]; exact huS.2.symm
      rw [dif_pos h2, if_neg hne, if_pos ⟨huS.1, hwS, hadj⟩]
      have hu := h2.2
      have hs : sgn (setRoot G S i σ ξ) u w = ξ ⟨u, hu⟩ := by
        have he : s(u, w) = s(i, ((⟨u, hu⟩ : nbhd G S i) : V)) := by
          rw [h2.1, Sym2.eq_swap]
        unfold sgn
        rw [he, setRoot_apply_root G σ ξ ⟨u, hu⟩]
        rcases hξ ⟨u, hu⟩ with h | h <;> norm_num [h]
      rw [hs]
    · rw [dif_neg h2]
      by_cases huw : u = w
      · simp only [huw, ↓reduceIte]
      · rw [if_neg huw, if_neg huw]
        have hs : sgn (setRoot G S i σ ξ) u w = sgn σ u w := by
          unfold sgn
          rw [setRoot_apply_of_not G σ ξ]
          rintro ⟨j, hj⟩
          rcases Sym2.eq_iff.1 hj with ⟨hu, hw⟩ | ⟨hu, hw⟩
          · exact h1 ⟨hu, hw ▸ j.2⟩
          · exact h2 ⟨hw, hu ▸ j.2⟩
        rw [hs]

theorem wSub_setRoot (p : ℕ) (a : ℝ) (yp ym : V → ℝ) (σ : Config V) {S : Finset V} {i : V}
    (hi : i ∈ S) {ξ : nbhd G S i → ℝ} (hξ : ∀ j, ξ j = 1 ∨ ξ j = -1) :
    wSub G p a yp ym σ S i ξ = wt G p a yp ym (setRoot G S i σ ξ) S := by
  unfold wSub wt
  rw [precSub_setRoot G a 1 yp σ hi hξ, precSub_setRoot G a (-1) ym σ hi hξ]

theorem diagSub_setRoot (a τ z : ℝ) (y : V → ℝ) (σ : Config V) {S : Finset V} {i : V}
    (hi : i ∈ S) {ξ : nbhd G S i → ℝ} (hξ : ∀ j, ξ j = 1 ∨ ξ j = -1) (k : V) :
    diagSub G a τ z y σ S i ξ k =
      y k * (precN G a τ y (setRoot G S i σ ξ) S + z • srcDiag y S)⁻¹ k k := by
  unfold diagSub
  rw [precSub_setRoot G a τ y σ hi hξ]

end StarSigns

section Congr

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The substituted precision only sees the signs off the edges at `i`. -/
theorem precSub_congr' (a τ : ℝ) (y : V → ℝ) {σ σ' : Config V} (S : Finset V) {i : V}
    (h : AgreeOff i σ σ') : precSub G a τ y σ S i = precSub G a τ y σ' S i := by
  funext x
  ext u w
  simp only [precSub, Matrix.of_apply]
  by_cases h1 : u = i ∧ w ∈ nbhd G S i
  · rw [dif_pos h1, dif_pos h1]
  · rw [dif_neg h1, dif_neg h1]
    by_cases h2 : w = i ∧ u ∈ nbhd G S i
    · rw [dif_pos h2, dif_pos h2]
    · rw [dif_neg h2, dif_neg h2]
      by_cases hui : u = i ∨ w = i
      · simp only [precN, Matrix.of_apply]
        by_cases huw : u = w
        · rw [if_pos huw, if_pos huw]
        · rw [if_neg huw, if_neg huw, if_neg, if_neg] <;>
          · rintro ⟨huS, hwS, hadj⟩
            rcases hui with hu | hw
            · exact h1 ⟨hu, Finset.mem_filter.2 ⟨hwS, hu ▸ hadj⟩⟩
            · exact h2 ⟨hw, Finset.mem_filter.2 ⟨huS, hw ▸ hadj.symm⟩⟩
      · have hc := congrFun (congrFun (SecA.precCore_congr' G (a := a) (τ := τ) (y := y)
          (S := S) h) u) w
        simpa only [precCore, Matrix.of_apply, if_neg hui] using hc

end Congr

section WT5

variable {d p : ℕ} (ct : Contact.{u} d p)

theorem kerL_setRoot (h : ℝ) (e dir : Bool) (i : ct.V) (σ : Config ct.V)
    (ξ : nbhd ct.G ct.S i → ℝ) :
    kerL ct h e dir i (setRoot ct.G ct.S i σ ξ) = kerL ct h e dir i σ := by
  simp only [kerL, Contact.tMap, Contact.tDir, Contact.tCav, Contact.Cb, coreShift,
    precCore_setRoot]

theorem diagSub_setRoot_eq_diagB {h : ℝ} {i : ct.V} (hi : i ∈ ct.S) (σ : Config ct.V)
    {ξ : nbhd ct.G ct.S i → ℝ} (hξ : ∀ j, ξ j = 1 ∨ ξ j = -1) (k : ct.V) (b sh : Bool) :
    diagSub ct.G (aOf d p) (if b then 1 else -1) (if sh then h else 0) (ct.ySrc b) σ ct.S i ξ k =
      ct.diagB h (setRoot ct.G ct.S i σ ξ) k b sh := by
  rw [diagSub_setRoot ct.G _ _ _ _ σ hi hξ]
  have hyp : 0 ≤ ct.yp k := (ct.ctx.hyp k).1
  have hym : 0 ≤ ct.ym k := (ct.ctx.hym k).1
  cases b <;> cases sh <;>
    simp only [Contact.diagB, Contact.Xb, Contact.XP, Contact.XM, Contact.gp, Contact.gm,
      Contact.ySrc, shiftP, greenP, Matrix.of_apply, Bool.false_eq_true, ↓reduceIte, zero_smul,
      add_zero]
  · linear_combination (-(precN ct.G (aOf d p) (-1) ct.ym (setRoot ct.G ct.S i σ ξ) ct.S)⁻¹ k k) *
      Real.mul_self_sqrt hym
  · linear_combination (-(precN ct.G (aOf d p) (-1) ct.ym (setRoot ct.G ct.S i σ ξ) ct.S +
      h • srcDiag ct.ym ct.S)⁻¹ k k) * Real.mul_self_sqrt hym
  · linear_combination (-(precN ct.G (aOf d p) 1 ct.yp (setRoot ct.G ct.S i σ ξ) ct.S)⁻¹ k k) *
      Real.mul_self_sqrt hyp
  · linear_combination (-(precN ct.G (aOf d p) 1 ct.yp (setRoot ct.G ct.S i σ ξ) ct.S +
      h • srcDiag ct.yp ct.S)⁻¹ k k) * Real.mul_self_sqrt hyp

theorem wtHSub_setRoot {h : ℝ} (e : Bool) {i : ct.V} (hi : i ∈ ct.S)
    (l : List (ct.V × Bool × Bool)) (σ : Config ct.V) {ξ : nbhd ct.G ct.S i → ℝ}
    (hξ : ∀ j, ξ j = 1 ∨ ξ j = -1) :
    wtHSub ct h e i l σ ξ = ct.wtH h e i l (setRoot ct.G ct.S i σ ξ) := by
  have hl : diagWSub ct h i l σ ξ = ct.diagW h l (setRoot ct.G ct.S i σ ξ) := by
    unfold diagWSub Contact.diagW
    congr 1
    exact List.map_congr_left fun t _ => diagSub_setRoot_eq_diagB ct hi σ hξ t.1 t.2.1 t.2.2
  have he := diagSub_setRoot_eq_diagB ct (h := h) hi σ hξ i e true
  have hp := diagSub_setRoot_eq_diagB ct (h := h) hi σ hξ i true true
  simp only [↓reduceIte, Contact.diagB] at he
  simp only [↓reduceIte, Contact.diagB, Contact.Xb, Contact.ySrc] at hp
  unfold wtHSub Contact.wtH
  rw [hl, he, hp]

/-- The observable `F^Q_σ(x) = W(x) H(x) q_L(x)` of (WT5) at the star vector `x` at `i`. -/
noncomputable def obsQ (h : ℝ) (e dir : Bool) (i : ct.V) (l : List (ct.V × Bool × Bool))
    (σ : Config ct.V) (x : nbhd ct.G ct.S i → ℝ) : ℝ :=
  wSub ct.G p (aOf d p) ct.yp ct.ym σ ct.S i x * wtHSub ct h e i l σ x *
    qForm (kerL ct h e dir i σ) x

/-- The observable `F^T_σ(x) = tr L · W(x) H(x)` of (WT5). -/
noncomputable def obsT (h : ℝ) (e dir : Bool) (i : ct.V) (l : List (ct.V × Bool × Bool))
    (σ : Config ct.V) (x : nbhd ct.G ct.S i → ℝ) : ℝ :=
  (kerL ct h e dir i σ).trace *
    (wSub ct.G p (aOf d p) ct.yp ct.ym σ ct.S i x * wtHSub ct h e i l σ x)

/-- **TB.WT5a** (star resummation, exact): `x = E[H q_L(ξ)] = Σ_σ 𝖱[F^Q_σ] / Z`. -/
theorem massQ_eq_radE (h : ℝ) (e dir : Bool) {i : ct.V} (hi : i ∈ ct.S)
    (l : List (ct.V × Bool × Bool)) :
    massQ ct h e dir i l = (∑ σ, radE (obsQ ct h e dir i l σ)) /
      Zw ct.G p (aOf d p) ct.yp ct.ym ct.S := by
  have hpm : ∀ (ε : nbhd ct.G ct.S i → Bool) j,
      (if ε j then (1 : ℝ) else -1) = 1 ∨ (if ε j then (1 : ℝ) else -1) = -1 := by
    intro ε j
    by_cases hj : ε j <;> simp [hj]
  have hterm : ∀ σ (ε : nbhd ct.G ct.S i → Bool),
      obsQ ct h e dir i l σ (fun j => if ε j then 1 else -1) =
        (fun τ => wt ct.G p (aOf d p) ct.yp ct.ym τ ct.S *
          (ct.wtH h e i l τ * qForm (kerL ct h e dir i τ) (rootSigns ct.G τ ct.S i)))
          (setRoot ct.G ct.S i σ fun j => if ε j then 1 else -1) := by
    intro σ ε
    simp only [obsQ]
    rw [wSub_setRoot ct.G _ _ _ _ σ hi (hpm ε), wtHSub_setRoot ct e hi l σ (hpm ε),
      kerL_setRoot, rootSigns_setRoot ct.G σ (hpm ε)]
    ring
  have hsum : ∑ σ, radE (obsQ ct h e dir i l σ) = ∑ τ, wt ct.G p (aOf d p) ct.yp ct.ym τ ct.S *
      (ct.wtH h e i l τ * qForm (kerL ct h e dir i τ) (rootSigns ct.G τ ct.S i)) := by
    have hcount := sum_sum_setRoot ct.G ct.S i fun τ => wt ct.G p (aOf d p) ct.yp ct.ym τ ct.S *
      (ct.wtH h e i l τ * qForm (kerL ct h e dir i τ) (rootSigns ct.G τ ct.S i))
    beta_reduce at hcount
    simp only [radE_eq_sum, hterm]
    rw [← Finset.sum_div, hcount, mul_div_cancel_left₀ _ (pow_ne_zero _ two_ne_zero)]
  rw [hsum]
  rfl

/-- **TB.WT5a** (star resummation, exact): `y = E[H tr L] = Σ_σ 𝖱[F^T_σ] / Z`. -/
theorem massT_eq_radE (h : ℝ) (e dir : Bool) {i : ct.V} (hi : i ∈ ct.S)
    (l : List (ct.V × Bool × Bool)) :
    massT ct h e dir i l = (∑ σ, radE (obsT ct h e dir i l σ)) /
      Zw ct.G p (aOf d p) ct.yp ct.ym ct.S := by
  have hpm : ∀ (ε : nbhd ct.G ct.S i → Bool) j,
      (if ε j then (1 : ℝ) else -1) = 1 ∨ (if ε j then (1 : ℝ) else -1) = -1 := by
    intro ε j
    by_cases hj : ε j <;> simp [hj]
  have hterm : ∀ σ (ε : nbhd ct.G ct.S i → Bool),
      obsT ct h e dir i l σ (fun j => if ε j then 1 else -1) =
        (fun τ => wt ct.G p (aOf d p) ct.yp ct.ym τ ct.S *
          (ct.wtH h e i l τ * (kerL ct h e dir i τ).trace))
          (setRoot ct.G ct.S i σ fun j => if ε j then 1 else -1) := by
    intro σ ε
    simp only [obsT]
    rw [wSub_setRoot ct.G _ _ _ _ σ hi (hpm ε), wtHSub_setRoot ct e hi l σ (hpm ε),
      kerL_setRoot]
    ring
  have hsum : ∑ σ, radE (obsT ct h e dir i l σ) = ∑ τ, wt ct.G p (aOf d p) ct.yp ct.ym τ ct.S *
      (ct.wtH h e i l τ * (kerL ct h e dir i τ).trace) := by
    have hcount := sum_sum_setRoot ct.G ct.S i fun τ => wt ct.G p (aOf d p) ct.yp ct.ym τ ct.S *
      (ct.wtH h e i l τ * (kerL ct h e dir i τ).trace)
    beta_reduce at hcount
    simp only [radE_eq_sum, hterm]
    rw [← Finset.sum_div, hcount, mul_div_cancel_left₀ _ (pow_ne_zero _ two_ne_zero)]
  rw [hsum]
  rfl

theorem gNumQ_eq (h : ℝ) (e dir : Bool) (i : ct.V) (l : List (ct.V × Bool × Bool)) :
    gNumQ ct h e dir i l = (∑ σ, gaussE (obsQ ct h e dir i l σ)) /
      Zw ct.G p (aOf d p) ct.yp ct.ym ct.S := rfl

theorem gNumT_eq (h : ℝ) (e dir : Bool) (i : ct.V) (l : List (ct.V × Bool × Bool)) :
    gNumT ct h e dir i l = (∑ σ, gaussE (obsT ct h e dir i l σ)) /
      Zw ct.G p (aOf d p) ct.yp ct.ym ct.S := by
  unfold gNumT
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  unfold gaussE obsT
  rw [MeasureTheory.integral_const_mul]

/-- The coordinates of `J = N_S(i)`, each listed once. -/
noncomputable def lJ (i : ct.V) : List (nbhd ct.G ct.S i) :=
  (Finset.univ : Finset (nbhd ct.G ct.S i)).toList

/-- The (E4) remainder at depth `k`, summed over signings (absolute value outside):
`|Σ_σ (𝖦 F_σ - Σ_{|j|_g ≤ k} c_j 𝖱 ∂^{2j} F_σ)| / Z`. -/
noncomputable def remSum (i : ct.V) (F : Config ct.V → (nbhd ct.G ct.S i → ℝ) → ℝ) (k : ℕ) :
    ℝ :=
  |∑ σ, (gaussE (F σ) - ∑ j ∈ (retIdx k : Finset (nbhd ct.G ct.S i → ℕ)),
      ecoefM j * radE (dEven (lJ ct i) j (F σ)))| / Zw ct.G p (aOf d p) ct.yp ct.ym ct.S

/-- The retained terms of grades `1 … k` of (E4), summed over signings:
`Σ_σ Σ_{1 ≤ |j|_g ≤ k} c_j 𝖱 ∂^{2j} F_σ / Z`. -/
noncomputable def retSum (i : ct.V) (F : Config ct.V → (nbhd ct.G ct.S i → ℝ) → ℝ) (k : ℕ) : ℝ :=
  (∑ σ, ∑ j ∈ (retIdx k : Finset (nbhd ct.G ct.S i → ℕ)).erase 0,
      ecoefM j * radE (dEven (lJ ct i) j (F σ))) / Zw ct.G p (aOf d p) ct.yp ct.ym ct.S

theorem zero_mem_retIdx {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ) :
    (0 : ι → ℕ) ∈ (retIdx k : Finset (ι → ℕ)) := by
  simp only [retIdx, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range, Pi.zero_apply]
  refine ⟨fun _ => by omega, fun _ => zero_ne_one, ?_⟩
  simp [grade]

/-- **TB.WT5s** (splitting, exact): `|Σ_σ (𝖦 - 𝖱) F_σ| / Z ≤ remSum + |retSum|`, since the
grade-`0` retained term of (E4) is `𝖱 F_σ` (`c_0 = 1`, `∂⁰ F = F`). -/
theorem abs_sum_gauss_sub_rad_le (i : ct.V) (F : Config ct.V → (nbhd ct.G ct.S i → ℝ) → ℝ)
    (k : ℕ) :
    |(∑ σ, gaussE (F σ)) / Zw ct.G p (aOf d p) ct.yp ct.ym ct.S -
        (∑ σ, radE (F σ)) / Zw ct.G p (aOf d p) ct.yp ct.ym ct.S| ≤
      remSum ct i F k + |retSum ct i F k| := by
  have hZ := Zw_nonneg ct.G (p := p) (a := aOf d p) (yp := ct.yp) (ym := ct.ym) (S := ct.S)
  have hsplit : ∀ σ, gaussE (F σ) - radE (F σ) =
      (gaussE (F σ) - ∑ j ∈ (retIdx k : Finset (nbhd ct.G ct.S i → ℕ)),
        ecoefM j * radE (dEven (lJ ct i) j (F σ))) +
      ∑ j ∈ (retIdx k : Finset (nbhd ct.G ct.S i → ℕ)).erase 0,
        ecoefM j * radE (dEven (lJ ct i) j (F σ)) := by
    intro σ
    rw [← Finset.add_sum_erase _ _ (zero_mem_retIdx k), ecoefM_zero, dEven_zero, one_mul]
    ring
  rw [← sub_div, ← Finset.sum_sub_distrib, abs_div, abs_of_nonneg hZ]
  simp only [hsplit]
  rw [Finset.sum_add_distrib, remSum, retSum, abs_div, abs_of_nonneg hZ, ← add_div]
  exact div_le_div_of_nonneg_right (abs_add_le _ _) hZ

/-- The root matrix `A` at the deleted vertex `i` (plus branch). -/
noncomputable abbrev rootA (σ : Config ct.V) (i : ct.V) :
    Matrix (nbhd ct.G ct.S i) (nbhd ct.G ct.S i) ℝ :=
  rootMat ct.G (aOf d p) 1 ct.yp σ ct.S i

/-- The root matrix `B` at the deleted vertex `i` (minus branch). -/
noncomputable abbrev rootB (σ : Config ct.V) (i : ct.V) :
    Matrix (nbhd ct.G ct.S i) (nbhd ct.G ct.S i) ℝ :=
  rootMat ct.G (aOf d p) (-1) ct.ym σ ct.S i

/-- The insertion constant `(D⁺_i D⁻_i)^p`. -/
noncomputable abbrev dPow (i : ct.V) : ℝ :=
  (diagD ct.G (aOf d p) ct.yp ct.S i * diagD ct.G (aOf d p) ct.ym ct.S i) ^ p

/-- The normalized observable `Φ H q_L` of (WT5) on the core support (`0` off it). -/
noncomputable def starObsQ (h : ℝ) (e dir : Bool) (i : ct.V) (l : List (ct.V × Bool × Bool))
    (σ : Config ct.V) : (nbhd ct.G ct.S i → ℝ) → ℝ :=
  if wtCore ct.G p (aOf d p) ct.yp ct.ym σ ct.S i ≠ 0 then
    fun x => starPhi p (rootA ct σ i) (rootB ct σ i) x *
      (wtHSub ct h e i l σ x * qForm (kerL ct h e dir i σ) x)
  else fun _ => 0

/-- The normalized observable `tr L · Φ H` of (WT5) on the core support (`0` off it). -/
noncomputable def starObsT (h : ℝ) (e dir : Bool) (i : ct.V) (l : List (ct.V × Bool × Bool))
    (σ : Config ct.V) : (nbhd ct.G ct.S i → ℝ) → ℝ :=
  if wtCore ct.G p (aOf d p) ct.yp ct.ym σ ct.S i ≠ 0 then
    fun x => (kerL ct h e dir i σ).trace *
      (starPhi p (rootA ct σ i) (rootB ct σ i) x * wtHSub ct h e i l σ x)
  else fun _ => 0

theorem dPow_pos (i : ct.V) : 0 < dPow ct i := by
  have hD : ∀ y : ct.V → ℝ, (∀ k, 0 ≤ y k) → 0 < diagD ct.G (aOf d p) y ct.S i := by
    intro y hy
    have h1 : 0 ≤ ∑ j ∈ nbhd ct.G ct.S i, cEdge (aOf d p) y i j := Finset.sum_nonneg fun j _ =>
      FloorIns.cRoot_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (hy i)) (hy j))
    unfold diagD
    linarith
  exact pow_pos (mul_pos (hD _ fun k => (ct.ctx.hyp k).1) (hD _ fun k => (ct.ctx.hym k).1)) p

/-- **TB.WT5i** (insertion, exact): `F^Q_σ = W_core(σ) (D⁺_i D⁻_i)^p · (Φ H q_L)_σ`. -/
theorem obsQ_eq (hp : 1 ≤ p) (h : ℝ) (e dir : Bool) {i : ct.V} (hi : i ∈ ct.S)
    (l : List (ct.V × Bool × Bool)) (σ : Config ct.V) (x : nbhd ct.G ct.S i → ℝ) :
    obsQ ct h e dir i l σ x = wtCore ct.G p (aOf d p) ct.yp ct.ym σ ct.S i * dPow ct i *
      starObsQ ct h e dir i l σ x := by
  have hw := wSub_eq_star ct.G hp (aOf d p) (fun k => (ct.ctx.hyp k).1)
    (fun k => (ct.ctx.hym k).1) σ hi x
  unfold obsQ starObsQ
  by_cases hc : wtCore ct.G p (aOf d p) ct.yp ct.ym σ ct.S i ≠ 0
  · rw [if_pos hc, hw]
    ring
  · rw [if_neg hc]
    rw [not_not] at hc
    rw [hw, hc]
    ring

/-- **TB.WT5i** (insertion, exact): `F^T_σ = W_core(σ) (D⁺_i D⁻_i)^p · (tr L Φ H)_σ`. -/
theorem obsT_eq (hp : 1 ≤ p) (h : ℝ) (e dir : Bool) {i : ct.V} (hi : i ∈ ct.S)
    (l : List (ct.V × Bool × Bool)) (σ : Config ct.V) (x : nbhd ct.G ct.S i → ℝ) :
    obsT ct h e dir i l σ x = wtCore ct.G p (aOf d p) ct.yp ct.ym σ ct.S i * dPow ct i *
      starObsT ct h e dir i l σ x := by
  have hw := wSub_eq_star ct.G hp (aOf d p) (fun k => (ct.ctx.hyp k).1)
    (fun k => (ct.ctx.hym k).1) σ hi x
  unfold obsT starObsT
  by_cases hc : wtCore ct.G p (aOf d p) ct.yp ct.ym σ ct.S i ≠ 0
  · rw [if_pos hc, hw]
    ring
  · rw [if_neg hc]
    rw [not_not] at hc
    rw [hw, hc]
    ring

/-- The own-core (E4) remainder `𝖦 F_σ - Σ_{|j|_g ≤ k} c_j 𝖱 ∂^{2j} F_σ`. -/
noncomputable def coreRem (i : ct.V) (F : Config ct.V → (nbhd ct.G ct.S i → ℝ) → ℝ) (k : ℕ)
    (σ : Config ct.V) : ℝ :=
  gaussE (F σ) - ∑ j ∈ (retIdx k : Finset (nbhd ct.G ct.S i → ℕ)),
    ecoefM j * radE (dEven (lJ ct i) j (F σ))

/-- The own-core retained terms of grades `1 … k`, `Σ_{1 ≤ |j|_g ≤ k} c_j 𝖱 ∂^{2j} F_σ`. -/
noncomputable def coreRet (i : ct.V) (F : Config ct.V → (nbhd ct.G ct.S i → ℝ) → ℝ) (k : ℕ)
    (σ : Config ct.V) : ℝ :=
  ∑ j ∈ (retIdx k : Finset (nbhd ct.G ct.S i → ℕ)).erase 0,
    ecoefM j * radE (dEven (lJ ct i) j (F σ))

/-- `Σ_σ W_core(σ) D X_σ / Z = E_core X / F_H`, `D = (D⁺_i D⁻_i)^p`. -/
theorem sum_wtCore_div_Zw (hp : 1 ≤ p) {i : ct.V} (hi : i ∈ ct.S) (X : Config ct.V → ℝ) :
    (∑ σ, wtCore ct.G p (aOf d p) ct.yp ct.ym σ ct.S i * dPow ct i * X σ) /
        Zw ct.G p (aOf d p) ct.yp ct.ym ct.S =
      coreE ct.G p (aOf d p) ct.yp ct.ym ct.S i X /
        insF ct.G p (aOf d p) ct.yp ct.ym ct.S i := by
  have hstar := sum_wt_mul_eq_star ct.G hp (aOf d p) (fun k => (ct.ctx.hyp k).1)
    (fun k => (ct.ctx.hym k).1) hi (fun _ => 1)
  simp only [mul_one] at hstar
  have hZ : Zw ct.G p (aOf d p) ct.yp ct.ym ct.S = dPow ct i *
      ∑ σ, wtCore ct.G p (aOf d p) ct.yp ct.ym σ ct.S i *
        radE (starPhi p (rootA ct σ i) (rootB ct σ i)) := hstar
  have hnum : ∑ σ, wtCore ct.G p (aOf d p) ct.yp ct.ym σ ct.S i * dPow ct i * X σ =
      dPow ct i * ∑ σ, wtCore ct.G p (aOf d p) ct.yp ct.ym σ ct.S i * X σ := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun σ _ => by ring
  rw [hZ, hnum, mul_div_mul_left _ _ (dPow_pos ct i).ne', insF, SecA.coreE_div_coreE]

theorem insF_nonneg' (i : ct.V) : 0 ≤ insF ct.G p (aOf d p) ct.yp ct.ym ct.S i := by
  unfold insF coreE
  refine div_nonneg (Finset.sum_nonneg fun σ _ => mul_nonneg (SecA.wtCore_nonneg' ct.G σ) ?_)
    (Finset.sum_nonneg fun σ _ => SecA.wtCore_nonneg' ct.G σ)
  unfold radE
  refine MeasureTheory.integral_nonneg fun x => ?_
  unfold starPhi clipF
  positivity

/-- **TB.WT5c** (core-law form of the remainder, exact). -/
theorem remSum_eq_core (hp : 1 ≤ p) {i : ct.V} (hi : i ∈ ct.S)
    (obs F : Config ct.V → (nbhd ct.G ct.S i → ℝ) → ℝ)
    (hF : ∀ σ x, obs σ x = wtCore ct.G p (aOf d p) ct.yp ct.ym σ ct.S i * dPow ct i * F σ x)
    (k : ℕ) :
    remSum ct i obs k = |coreE ct.G p (aOf d p) ct.yp ct.ym ct.S i (coreRem ct i F k)| /
      insF ct.G p (aOf d p) ct.yp ct.ym ct.S i := by
  have hobs : ∀ σ, obs σ = fun x =>
      (wtCore ct.G p (aOf d p) ct.yp ct.ym σ ct.S i * dPow ct i) * F σ x :=
    fun σ => funext fun x => hF σ x
  have hterm : ∀ σ, gaussE (obs σ) - ∑ j ∈ (retIdx k : Finset (nbhd ct.G ct.S i → ℕ)),
      ecoefM j * radE (dEven (lJ ct i) j (obs σ)) =
      wtCore ct.G p (aOf d p) ct.yp ct.ym σ ct.S i * dPow ct i * coreRem ct i F k σ := by
    intro σ
    rw [hobs σ, gaussE_const_mul, coreRem, mul_sub, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [dEven_const_mul, radE_const_mul]
    ring
  rw [remSum, Finset.sum_congr rfl fun σ _ => hterm σ,
    ← abs_of_nonneg (Zw_nonneg ct.G (p := p) (a := aOf d p) (yp := ct.yp) (ym := ct.ym)
      (S := ct.S)), ← abs_div, sum_wtCore_div_Zw ct hp hi, abs_div,
    abs_of_nonneg (insF_nonneg' ct i)]

/-- **TB.WT5c** (core-law form of the retained grades, exact). -/
theorem retSum_eq_core (hp : 1 ≤ p) {i : ct.V} (hi : i ∈ ct.S)
    (obs F : Config ct.V → (nbhd ct.G ct.S i → ℝ) → ℝ)
    (hF : ∀ σ x, obs σ x = wtCore ct.G p (aOf d p) ct.yp ct.ym σ ct.S i * dPow ct i * F σ x)
    (k : ℕ) :
    retSum ct i obs k = coreE ct.G p (aOf d p) ct.yp ct.ym ct.S i (coreRet ct i F k) /
      insF ct.G p (aOf d p) ct.yp ct.ym ct.S i := by
  have hobs : ∀ σ, obs σ = fun x =>
      (wtCore ct.G p (aOf d p) ct.yp ct.ym σ ct.S i * dPow ct i) * F σ x :=
    fun σ => funext fun x => hF σ x
  have hterm : ∀ σ, ∑ j ∈ (retIdx k : Finset (nbhd ct.G ct.S i → ℕ)).erase 0,
      ecoefM j * radE (dEven (lJ ct i) j (obs σ)) =
      wtCore ct.G p (aOf d p) ct.yp ct.ym σ ct.S i * dPow ct i * coreRet ct i F k σ := by
    intro σ
    rw [hobs σ, coreRet, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [dEven_const_mul, radE_const_mul]
    ring
  rw [retSum, Finset.sum_congr rfl fun σ _ => hterm σ, sum_wtCore_div_Zw ct hp hi]

theorem wtHSub_congr (h : ℝ) (e : Bool) {i : ct.V} (l : List (ct.V × Bool × Bool))
    {σ σ' : Config ct.V} (hσ : AgreeOff i σ σ') :
    wtHSub ct h e i l σ = wtHSub ct h e i l σ' := by
  funext x
  simp only [wtHSub, diagWSub, diagSub, precSub_congr' ct.G _ _ _ ct.S hσ]

theorem kerL_congr (h : ℝ) (e dir : Bool) {i : ct.V} {σ σ' : Config ct.V}
    (hσ : AgreeOff i σ σ') : kerL ct h e dir i σ = kerL ct h e dir i σ' := by
  simp only [kerL, Contact.tMap, Contact.tDir, Contact.tCav, Contact.Cb,
    SecA.coreShift_congr ct.G hσ]

/-- The normalized observables are core-measurable at `i` (needed for A-RET). -/
theorem starObsQ_congr (h : ℝ) (e dir : Bool) {i : ct.V} (l : List (ct.V × Bool × Bool))
    {σ σ' : Config ct.V} (hσ : AgreeOff i σ σ') :
    starObsQ ct h e dir i l σ = starObsQ ct h e dir i l σ' := by
  simp only [starObsQ, rootA, rootB, SecA.wtCore_congr ct.G hσ, SecA.rootMat_congr ct.G hσ,
    wtHSub_congr ct h e l hσ, kerL_congr ct h e dir hσ]

theorem starObsT_congr (h : ℝ) (e dir : Bool) {i : ct.V} (l : List (ct.V × Bool × Bool))
    {σ σ' : Config ct.V} (hσ : AgreeOff i σ σ') :
    starObsT ct h e dir i l σ = starObsT ct h e dir i l σ' := by
  simp only [starObsT, rootA, rootB, SecA.wtCore_congr ct.G hσ, SecA.rootMat_congr ct.G hσ,
    wtHSub_congr ct h e l hσ, kerL_congr ct h e dir hσ]

theorem coreE_sum_mul {i : ct.V} {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (f : ι → Config ct.V → ℝ) :
    coreE ct.G p (aOf d p) ct.yp ct.ym ct.S i (fun σ => ∑ j ∈ s, c j * f j σ) =
      ∑ j ∈ s, c j * coreE ct.G p (aOf d p) ct.yp ct.ym ct.S i (f j) := by
  unfold coreE
  simp only [Finset.mul_sum, Finset.sum_div]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact Finset.sum_congr rfl fun σ _ => by ring

/-- **A-RET for the retained grades** (exact): for a core-measurable family `F` whose retained
derivatives vanish at the sign vectors where `Φ = 0`,
`E_core coreRet(F) / F_H = Σ_{1 ≤ |j|_g ≤ k} c_j E[∂^{2j}F(ξ)/Φ(ξ)]`. -/
theorem coreRet_div_insF_eq (hp : 1 ≤ p) {i : ct.V} (hi : i ∈ ct.S)
    (F : Config ct.V → (nbhd ct.G ct.S i → ℝ) → ℝ)
    (hFc : ∀ σ σ', AgreeOff i σ σ' → F σ = F σ') (k : ℕ)
    (hvan : ∀ σ, ∀ j ∈ (retIdx k : Finset (nbhd ct.G ct.S i → ℕ)).erase 0,
      ∀ ξ : nbhd ct.G ct.S i → ℝ, (∀ s, ξ s = 1 ∨ ξ s = -1) →
        starPhi p (rootA ct σ i) (rootB ct σ i) ξ = 0 → dEven (lJ ct i) j (F σ) ξ = 0) :
    coreE ct.G p (aOf d p) ct.yp ct.ym ct.S i (coreRet ct i F k) /
        insF ct.G p (aOf d p) ct.yp ct.ym ct.S i =
      ∑ j ∈ (retIdx k : Finset (nbhd ct.G ct.S i → ℕ)).erase 0, ecoefM j *
        ct.E (fun σ => dEven (lJ ct i) j (F σ) (rootSigns ct.G σ ct.S i) /
          starPhi p (rootA ct σ i) (rootB ct σ i) (rootSigns ct.G σ ct.S i)) := by
  have hyp : ∀ k, 0 ≤ ct.yp k := fun k => (ct.ctx.hyp k).1
  have hym : ∀ k, 0 ≤ ct.ym k := fun k => (ct.ctx.hym k).1
  unfold coreRet
  rw [coreE_sum_mul ct, Finset.sum_div]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [mul_div_assoc]
  congr 1
  have h := SecA.lawE_eq_coreE_div ct.G hp (aOf d p) hyp hym hi
    (fun σ ξ => dEven (lJ ct i) j (F σ) ξ / starPhi p (rootA ct σ i) (rootB ct σ i) ξ)
    (fun σ σ' hσ => by
      funext ξ
      simp only [rootA, rootB, SecA.rootMat_congr ct.G hσ, hFc σ σ' hσ])
  refine Eq.trans ?_ h.symm
  congr 1
  refine congrArg _ (funext fun σ => ?_)
  rw [radE_eq_sum, radE_eq_sum]
  congr 1
  refine Finset.sum_congr rfl fun ε _ => ?_
  have hpm : ∀ s, (if ε s then (1 : ℝ) else -1) = 1 ∨ (if ε s then (1 : ℝ) else -1) = -1 := by
    intro s
    by_cases h : ε s <;> simp [h]
  by_cases hΦ : starPhi p (rootA ct σ i) (rootB ct σ i) (fun s => if ε s then 1 else -1) = 0
  · rw [hΦ, zero_mul]
    exact hvan σ j hj _ hpm hΦ
  · rw [mul_div_assoc', mul_comm, mul_div_assoc, div_self hΦ, mul_one]

theorem insF_pos_ct (hR : TRegime d p) {i : ct.V} (hi : i ∈ ct.S) :
    0 < insF ct.G p (aOf d p) ct.yp ct.ym ct.S i := by
  have hs := hR.sOf_pos
  have hcube : ∀ y : ct.V → ℝ, InCube (ct.lam * sOf d p) y → InCube (sOf d p) y :=
    fun y hy k => ⟨(hy k).1, (hy k).2.trans (by
      nlinarith [ct.ctx.lam_le_one, ct.ctx.lam_nonneg])⟩
  exact SecA.insF_pos ct.G (le_trans (by norm_num) hR.two_le_p) (aOf d p)
    (fun k => (ct.ctx.hyp k).1) (fun k => (ct.ctx.hym k).1) hi
    (ct.ctx.pos ct.yp ct.ym (hcube _ ct.ctx.hyp) (hcube _ ct.ctx.hym))

end WT5

end BiluLinial.Tight.SecB
