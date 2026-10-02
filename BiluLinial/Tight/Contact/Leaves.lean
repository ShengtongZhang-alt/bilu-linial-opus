/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.Contact.Inputs
public import BiluLinial.Tight.Walk
public import BiluLinial.Tight.SourceMax.Law
public import BiluLinial.Tight.Tools.Interp
public import BiluLinial.Tight.Tools.MatrixFacts
public import BiluLinial.Tight.FloorLemma

/-!
# Analytic leaves of the contact estimate (Section 1.5)

Blueprint `docs/tight/BP_CONTACT.md`, nodes `L-*`. These are the steps of Section 1.5 that are not
pure real-number algebra: exact identities of the law at the contact (root equation, Cauchy–Schwarz
for the row), deterministic source facts, and the estimates that apply an input of Sections
1.2–1.4 to a specific observable (Hölder/interpolation, mean shift, weak loop scores). Each is
stated at a contact with an absolute constant first; the informal dependencies are listed in the
docstrings and in the blueprint.
-/

@[expose] public section

namespace BiluLinial.Tight

open Matrix

universe u

/-! ### Helpers: the paired law -/

section LawHelpers

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable {p : ℕ} {a : ℝ} {yp ym : V → ℝ} {S : Finset V}

theorem lv_posDef_of_wt {σ : Config V} (h : wt G p a yp ym σ S ≠ 0) :
    (precN G a 1 yp σ S).PosDef ∧ (precN G a (-1) ym σ S).PosDef := by
  unfold wt at h
  split_ifs at h with h'
  · exact h'
  · exact absurd rfl h

theorem lv_lawE_const (hZ : Zw G p a yp ym S ≠ 0) (c : ℝ) :
    lawE G p a yp ym S (fun _ => c) = c := by
  unfold lawE
  rw [← Finset.sum_mul]
  exact mul_div_cancel_left₀ c hZ

theorem lv_lawE_mono {f g : Config V → ℝ} (h : ∀ σ, wt G p a yp ym σ S ≠ 0 → f σ ≤ g σ) :
    lawE G p a yp ym S f ≤ lawE G p a yp ym S g := by
  unfold lawE
  refine div_le_div_of_nonneg_right (Finset.sum_le_sum fun σ _ => ?_) (Zw_nonneg G)
  by_cases hw : wt G p a yp ym σ S = 0
  · rw [hw, zero_mul, zero_mul]
  · exact mul_le_mul_of_nonneg_left (h σ hw) (wt_nonneg G σ)

theorem lv_lawE_neg (f : Config V → ℝ) :
    lawE G p a yp ym S (fun σ => -f σ) = -lawE G p a yp ym S f := by
  unfold lawE
  rw [← neg_div, ← Finset.sum_neg_distrib]
  simp only [mul_neg]

/-- Cauchy–Schwarz under the paired law from a pointwise bound `B² ≤ A C`, `A, C ≥ 0` on the
support. -/
theorem lv_lawE_cs {A B C : Config V → ℝ}
    (hA : ∀ σ, wt G p a yp ym σ S ≠ 0 → 0 ≤ A σ) (hC : ∀ σ, wt G p a yp ym σ S ≠ 0 → 0 ≤ C σ)
    (hB : ∀ σ, wt G p a yp ym σ S ≠ 0 → B σ ^ 2 ≤ A σ * C σ) :
    lawE G p a yp ym S B ^ 2 ≤ lawE G p a yp ym S A * lawE G p a yp ym S C := by
  have hpt : ∀ σ, wt G p a yp ym σ S ≠ 0 →
      |B σ| ≤ Real.sqrt (A σ) * Real.sqrt (C σ) := fun σ hσ => by
    rw [← Real.sqrt_mul (hA σ hσ)]
    exact Real.abs_le_sqrt (hB σ hσ)
  have h1 : lawE G p a yp ym S B ≤
      lawE G p a yp ym S (fun σ => Real.sqrt (A σ) * Real.sqrt (C σ)) :=
    lv_lawE_mono G fun σ hσ => (le_abs_self _).trans (hpt σ hσ)
  have h2 : -lawE G p a yp ym S (fun σ => Real.sqrt (A σ) * Real.sqrt (C σ)) ≤
      lawE G p a yp ym S B := by
    rw [← lv_lawE_neg G]
    exact lv_lawE_mono G fun σ hσ => neg_le_of_abs_le (hpt σ hσ)
  have h3 := wavg_mul_sq_le (w := fun σ => wt G p a yp ym σ S) (fun σ => wt_nonneg G σ)
    (fun σ => Real.sqrt (A σ)) (fun σ => Real.sqrt (C σ))
  have hA2 : lawE G p a yp ym S (fun σ => Real.sqrt (A σ) ^ 2) = lawE G p a yp ym S A :=
    lawE_congr G fun σ hσ => Real.sq_sqrt (hA σ hσ)
  have hC2 : lawE G p a yp ym S (fun σ => Real.sqrt (C σ) ^ 2) = lawE G p a yp ym S C :=
    lawE_congr G fun σ hσ => Real.sq_sqrt (hC σ hσ)
  calc lawE G p a yp ym S B ^ 2
      ≤ lawE G p a yp ym S (fun σ => Real.sqrt (A σ) * Real.sqrt (C σ)) ^ 2 := sq_le_sq' h2 h1
    _ ≤ lawE G p a yp ym S (fun σ => Real.sqrt (A σ) ^ 2) *
          lawE G p a yp ym S (fun σ => Real.sqrt (C σ) ^ 2) := h3
    _ = lawE G p a yp ym S A * lawE G p a yp ym S C := by rw [hA2, hC2]

end LawHelpers

/-! ### Helpers: matrices of the law -/

section MatHelpers

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Row `w` of `P̃ P̃⁻¹ = I` (local copy of `SecB.root_row_identity`). -/
theorem lv_root_row_identity {a τ : ℝ} {y : V → ℝ} {σ : Config V} {S : Finset V} {w : V}
    (hP : (precN G a τ y σ S).PosDef) (hw : w ∈ S) :
    diagD G a y S w * hN G a τ y σ S w +
      τ * a * ∑ i ∈ nbhd G S w, sgn σ w i * greenP G a τ y σ S w i = 1 := by
  set P := precN G a τ y σ S with hPdef
  have hu : IsUnit P.det := isUnit_iff_ne_zero.mpr hP.det_pos.ne'
  have hsymm : ∀ k l, P⁻¹ k l = P⁻¹ l k := fun k l => by
    have := congrFun (congrFun hP.inv.1 l) k
    simpa [Matrix.conjTranspose_apply] using this
  have h1 : (P * P⁻¹) w w = 1 := by rw [Matrix.mul_nonsing_inv P hu, Matrix.one_apply_eq]
  rw [Matrix.mul_apply] at h1
  have hPww : P w w = diagD G a y S w := by rw [hPdef]; simp [precN, hw]
  have hPwk : ∀ k, k ≠ w → P w k =
      if k ∈ nbhd G S w then τ * a * (Real.sqrt (y w) * Real.sqrt (y k)) * sgn σ w k else 0 := by
    intro k hk
    have hk' : w ≠ k := fun h => hk h.symm
    rw [hPdef]
    simp only [precN, Matrix.of_apply, hk', ↓reduceIte]
    by_cases hn : k ∈ nbhd G S w
    · have hn' : k ∈ S ∧ G.Adj w k := by simpa [nbhd] using hn
      simp [hw, hn'.1, hn'.2, hn]
    · have hn' : ¬ (w ∈ S ∧ k ∈ S ∧ G.Adj w k) := fun h => hn (by simp [nbhd, h.2.1, h.2.2])
      simp only [hn', hn, ↓reduceIte]
  have hg : ∀ k, greenP G a τ y σ S w k = Real.sqrt (y w) * P⁻¹ w k * Real.sqrt (y k) :=
    fun k => rfl
  have hh : hN G a τ y σ S w = P⁻¹ w w := rfl
  have hterm : ∀ k, P w k * P⁻¹ k w =
      (if k = w then diagD G a y S w * hN G a τ y σ S w else 0) +
        (if k ∈ nbhd G S w then τ * a * (sgn σ w k * greenP G a τ y σ S w k) else 0) := by
    intro k
    by_cases hk : k = w
    · rw [hk]
      have hn : w ∉ nbhd G S w := by simp [nbhd]
      simp only [hPww, hh, hn, ↓reduceIte, add_zero]
    · rw [hPwk k hk]
      by_cases hn : k ∈ nbhd G S w
      · simp only [hk, hn, ↓reduceIte, zero_add, hg]
        rw [hsymm k w]
        ring
      · simp only [hk, hn, ↓reduceIte, zero_add, zero_mul]
  simp_rw [hterm] at h1
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ w, ite_eq_left (Finset.mem_univ _),
    Finset.sum_ite_mem Finset.univ, Finset.univ_inter, ← Finset.mul_sum] at h1
  linarith

omit [Fintype V] in
theorem lv_precCore_symm (a τ : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) (v : V)
    (u w : V) : precCore G a τ y σ S v w u = precCore G a τ y σ S v u w := by
  have h := (precN_isHermitian' G a τ y σ S).apply u w
  simp only [star_trivial] at h
  simp only [precCore, Matrix.of_apply]
  by_cases h1 : u = v ∨ w = v
  · rw [ite_eq_left h1.symm, ite_eq_left h1]
    by_cases h3 : u = w
    · rw [ite_eq_left h3.symm, ite_eq_left h3]
    · rw [ite_eq_right (Ne.symm h3), ite_eq_right h3]
  · have h2 : ¬ (w = v ∨ u = v) := fun h => h1 h.symm
    rw [ite_eq_right h2, ite_eq_right h1, h]

theorem lv_inv_symm {n : Type*} [Fintype n] [DecidableEq n] {M : Matrix n n ℝ}
    (hM : ∀ i j, M j i = M i j) (i j : n) : M⁻¹ j i = M⁻¹ i j := by
  have hT : Mᵀ = M := by
    ext k l
    rw [Matrix.transpose_apply]
    exact hM k l
  have := congrFun (congrFun (Matrix.transpose_nonsing_inv (A := M)) i) j
  rw [hT, Matrix.transpose_apply] at this
  exact this

/-- The root matrix is symmetric for every signing. -/
theorem lv_rootMat_isHermitian (a τ : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) (v : V) :
    (rootMat G a τ y σ S v).IsHermitian := by
  refine Matrix.IsHermitian.ext fun i j => ?_
  simp only [rootMat, coreGreen, Matrix.of_apply, star_trivial]
  rw [lv_inv_symm (lv_precCore_symm G a τ y σ S v) (i : V) (j : V)]
  ring

/-- At a good core the root matrix has nonnegative trace. -/
theorem lv_rootMat_trace_nonneg {a τ : ℝ} {y : V → ℝ} (hy : ∀ i, 0 ≤ y i) {σ : Config V}
    {S : Finset V} {v : V} (hM : (precCore G a τ y σ S v).PosDef) :
    0 ≤ (rootMat G a τ y σ S v).trace := by
  have hD : 0 < diagD G a y S v := lt_of_lt_of_le one_pos (FloorIns.one_le_diagD G a hy S v)
  have hc : 0 ≤ a ^ 2 * y v / diagD G a y S v :=
    div_nonneg (mul_nonneg (sq_nonneg a) (hy v)) hD.le
  unfold Matrix.trace
  refine Finset.sum_nonneg fun i _ => ?_
  simp only [Matrix.diag, rootMat, coreGreen, Matrix.of_apply]
  exact mul_nonneg hc (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (hM.inv.diag_pos).le)
    (Real.sqrt_nonneg _))

theorem lv_greenP_diag_nonneg {a τ : ℝ} {y : V → ℝ} {σ : Config V} {S : Finset V}
    (hP : (precN G a τ y σ S).PosDef) (k : V) : 0 ≤ greenP G a τ y σ S k k :=
  mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (hP.inv.diag_pos).le) (Real.sqrt_nonneg _)

theorem lv_psd_sqrt_conj {n : Type*} [Fintype n] [DecidableEq n] {Q : Matrix n n ℝ}
    (hQ : Q.PosDef) (y : n → ℝ) :
    (Matrix.of fun i j => Real.sqrt (y i) * Q⁻¹ i j * Real.sqrt (y j)).PosSemidef := by
  have h := hQ.inv.posSemidef.mul_mul_conjTranspose_same (diagonal fun i => Real.sqrt (y i))
  convert h using 1
  ext i j
  rw [diagonal_conjTranspose, mul_diagonal, diagonal_mul, Matrix.of_apply]
  simp

/-- On the support, the physical shifted inverse is positive semidefinite. -/
theorem lv_shift_psd {a τ z : ℝ} {y : V → ℝ} {σ : Config V} {S : Finset V}
    (hP : (precN G a τ y σ S).PosDef) (hy : ∀ k, 0 ≤ y k) (hz : 0 ≤ z) :
    (Matrix.of fun i j => shiftP G a τ z y σ S i j).PosSemidef := by
  have hD : (z • srcDiag y S).PosSemidef := by
    refine Matrix.PosSemidef.smul ?_ hz
    refine Matrix.PosSemidef.diagonal fun k => ?_
    split_ifs
    · exact hy k
    · exact le_rfl
  exact lv_psd_sqrt_conj (hP.add_posSemidef hD) y

end MatHelpers

section Generic

variable {ι : Type*} [Fintype ι]

theorem lv_psd_qf_nonneg {K : Matrix ι ι ℝ} (hK : K.PosSemidef) (f : ι → ℝ) :
    0 ≤ f ⬝ᵥ (K *ᵥ f) := by
  simpa only [star_trivial] using hK.dotProduct_mulVec_nonneg f

/-- Cauchy–Schwarz for a positive semidefinite form. -/
theorem lv_psd_cs {K : Matrix ι ι ℝ} (hK : K.PosSemidef) (f g : ι → ℝ) :
    (f ⬝ᵥ (K *ᵥ g)) ^ 2 ≤ (f ⬝ᵥ (K *ᵥ f)) * (g ⬝ᵥ (K *ᵥ g)) := by
  have hsym : g ⬝ᵥ (K *ᵥ f) = f ⬝ᵥ (K *ᵥ g) := by
    rw [dotProduct_mulVec_comm_of_symm hK.isHermitian g f, dotProduct_comm]
  have hq : ∀ t : ℝ,
      0 ≤ (g ⬝ᵥ (K *ᵥ g)) * (t * t) + (2 * (f ⬝ᵥ (K *ᵥ g))) * t + f ⬝ᵥ (K *ᵥ f) := by
    intro t
    have h := lv_psd_qf_nonneg hK (f + t • g)
    simp only [mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
      smul_dotProduct, smul_eq_mul, hsym] at h
    nlinarith [h]
  have hd := discrim_le_zero hq
  unfold discrim at hd
  nlinarith [hd]

theorem lv_scaled_cs {Ω x A C : ℝ} (h : x ^ 2 ≤ A * C) : (Ω * x) ^ 2 ≤ (Ω * A) * (Ω * C) := by
  calc (Ω * x) ^ 2 = Ω ^ 2 * x ^ 2 := by ring
    _ ≤ Ω ^ 2 * (A * C) := mul_le_mul_of_nonneg_left h (sq_nonneg _)
    _ = (Ω * A) * (Ω * C) := by ring

theorem lv_mulVec_nonneg {M : Matrix ι ι ℝ} {v : ι → ℝ} (hM : ∀ i j, 0 ≤ M i j)
    (hv : ∀ i, 0 ≤ v i) (i : ι) : 0 ≤ (M *ᵥ v) i := by
  simp only [mulVec, dotProduct]
  exact Finset.sum_nonneg fun j _ => mul_nonneg (hM i j) (hv j)

theorem lv_dot_mulVec_nonneg {M : Matrix ι ι ℝ} {f g : ι → ℝ} (hM : ∀ i j, 0 ≤ M i j)
    (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i) : 0 ≤ f ⬝ᵥ (M *ᵥ g) := by
  simp only [dotProduct]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hf i) (lv_mulVec_nonneg hM hg i)

theorem lv_dot_mulVec_mono {M K : Matrix ι ι ℝ} {f g : ι → ℝ} (hMK : ∀ i j, M i j ≤ K i j)
    (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i) : f ⬝ᵥ (M *ᵥ g) ≤ f ⬝ᵥ (K *ᵥ g) := by
  simp only [dotProduct, mulVec]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hMK i j) (hg j)) (hf i)

omit [Fintype ι] in
/-- Schur product theorem, scaled: `A ∘ B / 4 ⪰ 0`. -/
theorem lv_had_psd {A B : Matrix ι ι ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (Matrix.of fun i k => A i k * B i k / 4).PosSemidef := by
  have h := (hA.hadamard hB).smul (show (0 : ℝ) ≤ 1 / 4 by norm_num)
  convert h using 1
  ext i k
  simp only [Matrix.of_apply, Matrix.smul_apply, Matrix.hadamard_apply, smul_eq_mul]
  ring

theorem lv_colsq (U : Matrix ι ι ℝ) (i : ι) : ∑ j, U j i ^ 2 = (Uᴴ * U) i i := by
  simp only [mul_apply, conjTranspose_apply, star_trivial, sq]

theorem lv_qf_col (X M : Matrix ι ι ℝ) (i : ι) :
    (fun k => M k i) ⬝ᵥ (X *ᵥ fun k => M k i) = (Mᴴ * X * M) i i := by
  simp only [dotProduct, mulVec, mul_apply, conjTranspose_apply, star_trivial, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

variable [DecidableEq ι]

theorem lv_psd_of_qf_le {X : Matrix ι ι ℝ} (hX : X.PosSemidef) {l : ℝ} (hl : 0 ≤ l)
    (hXn : ∀ w, w ⬝ᵥ (X *ᵥ w) ≤ l * (w ⬝ᵥ w)) : (l • (1 : Matrix ι ι ℝ) - X).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    ((PosSemidef.one.smul hl).isHermitian.sub hX.isHermitian) fun x => ?_
  simp only [star_trivial, sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub, dotProduct_smul,
    smul_eq_mul]
  linarith [hXn x]

theorem lv_trace_BXBY (X Y : Matrix ι ι ℝ) (b : ι → ℝ) (hYs : ∀ i j, Y j i = Y i j) :
    (diagonal b * X * diagonal b * Y).trace =
      4 * (b ⬝ᵥ (Matrix.of (fun i k => X i k * Y i k / 4) *ᵥ b)) := by
  have e : ∀ i, (diagonal b * X * diagonal b * Y) i i = ∑ k, b i * X i k * b k * Y i k := by
    intro i
    rw [mul_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_diagonal, diagonal_mul, hYs i k]
  simp only [Matrix.trace, Matrix.diag, e, dotProduct, mulVec, Matrix.of_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring

end Generic

variable {d p : ℕ}

/-- **L-root** (source "exact row equation", l.1977–1978, and the root equation of l.1394–1397;
AUDIT-D §3.1 D3 "the root equation `D₊ r = 1 - aΣ_N E[ξ_i x_i]`"). Row `v` of `P⁺G⁺ = I` on every
supported signing, `Z⁺_v G⁺_vv + a Σ_N σ_vi G⁺_vi = 1`, averaged:
`D₊ E h⁺_v + a Σ_N E[ξ_i x_i] = 1`. Exact (needs only `Zw > 0` at the contact point). -/
theorem root_equation (hR : TRegime d p) (ct : Contact.{u} d p) :
    ct.Dplus * ct.mp ct.v + aOf d p * ∑ i ∈ ct.N, ct.sx i = 1 := by
  have hs := hR.sOf_pos
  have hcube : ∀ y : ct.V → ℝ, InCube (ct.lam * sOf d p) y → InCube (sOf d p) y := fun y hy k =>
    ⟨(hy k).1, (hy k).2.trans (mul_le_of_le_one_left hs.le ct.ctx.lam_le_one)⟩
  have hZ : Zw ct.G p (aOf d p) ct.yp ct.ym ct.S ≠ 0 :=
    (ct.ctx.pos ct.yp ct.ym (hcube _ ct.ctx.hyp) (hcube _ ct.ctx.hym)).ne'
  have h := lawE_congr ct.G (p := p) (a := aOf d p) (yp := ct.yp) (ym := ct.ym) (S := ct.S)
    (f := fun σ => diagD ct.G (aOf d p) ct.yp ct.S ct.v * hN ct.G (aOf d p) 1 ct.yp σ ct.S ct.v +
      aOf d p * ∑ i ∈ nbhd ct.G ct.S ct.v,
        sgn σ ct.v i * greenP ct.G (aOf d p) 1 ct.yp σ ct.S ct.v i)
    (g := fun _ => 1) fun σ hσ => by
      have := lv_root_row_identity ct.G (lv_posDef_of_wt ct.G hσ).1 ct.ctx.mem
      linarith
  rw [lv_lawE_const ct.G hZ, lawE_add, lawE_const_mul, lawE_const_mul, lawE_sum] at h
  exact h

theorem lv_sx_sq_le (ct : Contact.{u} d p) (i : ct.V) :
    ct.sx i ^ 2 ≤ ct.E fun σ => ct.x σ i ^ 2 := by
  have hw : ∀ σ, 0 ≤ wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S := fun σ => wt_nonneg ct.G σ
  have h := wavg_mul_sq_le hw (fun σ => sgn σ ct.v i) (fun σ => ct.x σ i)
  have h1 : wavg (fun σ => wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S)
      (fun σ => sgn σ ct.v i ^ 2) ≤ 1 := by
    have e : (fun σ : Config ct.V => sgn σ ct.v i ^ 2) = fun _ => (1 : ℝ) :=
      funext fun σ => by rw [sq, FloorIns.sgn_mul_self]
    rw [e, wavg]
    simp only [mul_one]
    exact div_self_le_one _
  have h2 : 0 ≤ wavg (fun σ => wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S)
      (fun σ => ct.x σ i ^ 2) := wavg_nonneg hw fun σ => sq_nonneg _
  calc ct.sx i ^ 2 ≤ _ := h
    _ ≤ 1 * wavg (fun σ => wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S) (fun σ => ct.x σ i ^ 2) :=
        mul_le_mul_of_nonneg_right h1 h2
    _ = ct.E fun σ => ct.x σ i ^ 2 := one_mul _

/-- **L-CS** (source (D15), l.1977–1982: "Cauchy–Schwarz on the exact row equation, then Jensen").
`(Σ_N E[ξ_i x_i])² ≤ |N| · S`. -/
theorem d15_cs (ct : Contact.{u} d p) : (∑ i ∈ ct.N, ct.sx i) ^ 2 ≤ ct.N.card * ct.Srow := by
  refine sq_sum_le_card_mul_sum_sq.trans ?_
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => lv_sx_sq_le ct i)
    (Nat.cast_nonneg _)

/-- **L-source** (source l.1366–1368 "deterministic source inequalities", l.1356; AUDIT-D §3.1
"Deterministic source facts", AUDIT-C §6 "Source facts"). At a contact, in the regime:
`|N| ≤ d`; `ℓ_i ≥ 0`; `L ≤ L̄` (`|N| ≤ d`, `y ≤ s`); `0 ≤ C₊ ≤ J` (`ℓ_i τ_vi = c_vi²` and
`K_vi ≥ τ_vi`, `walk_facts`); `C₊ ≤ a² L̄ s²` (`c_vi ≤ a² s²`); `D₊ = 1 + L - C₊`
(`c(1+c) = ℓ`); `Σ_N ℓ_i δ_i ≥ 0` (the cap); `S, S₋, E tr A², E tr B², E w ≥ 0`. -/
theorem source_facts (hR : TRegime d p) (ct : Contact.{u} d p) :
    (ct.N.card : ℝ) ≤ d ∧ (∀ i, 0 ≤ ct.ell i) ∧ ct.Lsum ≤ LbarP d p ∧ 0 ≤ ct.Cplus ∧
      ct.Cplus ≤ ct.Jw ∧ ct.Cplus ≤ aOf d p ^ 2 * LbarP d p * sOf d p ^ 2 ∧
      ct.Dplus = 1 + ct.Lsum - ct.Cplus ∧ 0 ≤ ct.sumEllDelta ∧ 0 ≤ ct.Srow ∧ 0 ≤ ct.Smin ∧
      0 ≤ ct.trA2 ∧ 0 ≤ ct.trB2 ∧ 0 ≤ ct.wker := by
  have hs := hR.sOf_pos
  have hcube : ∀ y : ct.V → ℝ, InCube (ct.lam * sOf d p) y → InCube (sOf d p) y := fun y hy k =>
    ⟨(hy k).1, (hy k).2.trans (mul_le_of_le_one_left hs.le ct.ctx.lam_le_one)⟩
  have hyS : InCube (sOf d p) ct.yp := hcube _ ct.ctx.hyp
  have hy0 : ∀ k, 0 ≤ ct.yp k := fun k => (hyS k).1
  have hym0 : ∀ k, 0 ≤ ct.ym k := fun k => (ct.ctx.hym k).1
  have hp1 : 1 ≤ p := le_trans (by norm_num) hR.hp
  have hcard : (ct.N.card : ℝ) ≤ d := by
    have h1 := FloorIns.card_nbhd_le ct.G ct.S ct.v
    have h2 := ct.ctx.deg ct.v
    exact_mod_cast h1.trans h2
  have hell : ∀ i, 0 ≤ ct.ell i := fun i => FloorIns.edge_nonneg (a := aOf d p) hy0 ct.v i
  have hκ0 : 0 ≤ aOf d p ^ 2 * sOf d p ^ 2 := by positivity
  have hellκ : ∀ i, ct.ell i ≤ aOf d p ^ 2 * sOf d p ^ 2 := fun i =>
    FloorIns.edge_le_kappa (a := aOf d p) hyS ct.v i
  have hc0 : ∀ i, 0 ≤ cEdge (aOf d p) ct.yp ct.v i := fun i => FloorIns.cRoot_nonneg (hell i)
  have hcl : ∀ i, cEdge (aOf d p) ct.yp ct.v i ≤ ct.ell i := fun i => FloorIns.cRoot_le (hell i)
  have hcc : ∀ i, cEdge (aOf d p) ct.yp ct.v i * (1 + cEdge (aOf d p) ct.yp ct.v i) = ct.ell i :=
    fun i => FloorIns.cRoot_mul_self_add (hell i)
  -- `L ≤ L̄`
  have hL : ct.Lsum ≤ LbarP d p := by
    have h1 : ct.Lsum ≤ ct.N.card * (aOf d p ^ 2 * sOf d p ^ 2) := by
      have := Finset.sum_le_card_nsmul ct.N ct.ell _ fun i _ => hellκ i
      rw [nsmul_eq_mul] at this
      exact this
    calc ct.Lsum ≤ _ := h1
      _ ≤ d * (aOf d p ^ 2 * sOf d p ^ 2) := mul_le_mul_of_nonneg_right hcard hκ0
      _ = LbarP d p := by rw [LbarP]; ring
  -- `C₊ ≤ J`
  have hCJ : ct.Cplus ≤ ct.Jw := by
    have hw := (walk_facts ct.G hR ct.ctx.deg hyS ct.S).2.2.2
    refine Finset.sum_le_sum fun i hi => ?_
    have hi' := (FloorIns.mem_nbhd ct.G).1 hi
    have hτ := hw ct.v i ct.ctx.mem hi'.1 hi'.2
    have hc1 : 1 + cEdge (aOf d p) ct.yp ct.v i ≠ 0 := by linarith [hc0 i]
    have e : ct.ell i * τEdge (aOf d p) ct.yp ct.v i = cEdge (aOf d p) ct.yp ct.v i ^ 2 := by
      rw [τEdge, ← hcc i]
      field_simp
    calc cEdge (aOf d p) ct.yp ct.v i ^ 2 = ct.ell i * τEdge (aOf d p) ct.yp ct.v i := e.symm
      _ ≤ ct.ell i * walkK ct.G (aOf d p) ct.yp ct.S ct.v i :=
          mul_le_mul_of_nonneg_left hτ (hell i)
  -- `C₊ ≤ a² L̄ s²`
  have hCa : ct.Cplus ≤ aOf d p ^ 2 * LbarP d p * sOf d p ^ 2 := by
    have h1 : ct.Cplus ≤ ct.N.card * (aOf d p ^ 2 * sOf d p ^ 2) ^ 2 := by
      have := Finset.sum_le_card_nsmul ct.N (fun i => cEdge (aOf d p) ct.yp ct.v i ^ 2) _
        fun i _ => pow_le_pow_left₀ (hc0 i) ((hcl i).trans (hellκ i)) 2
      rw [nsmul_eq_mul] at this
      exact this
    calc ct.Cplus ≤ _ := h1
      _ ≤ d * (aOf d p ^ 2 * sOf d p ^ 2) ^ 2 := mul_le_mul_of_nonneg_right hcard (sq_nonneg _)
      _ = aOf d p ^ 2 * LbarP d p * sOf d p ^ 2 := by rw [LbarP]; ring
  -- `D₊ = 1 + L - C₊`
  have hD : ct.Dplus = 1 + ct.Lsum - ct.Cplus := by
    have e : ∀ i, cEdge (aOf d p) ct.yp ct.v i =
        ct.ell i - cEdge (aOf d p) ct.yp ct.v i ^ 2 := fun i => by
      linear_combination hcc i
    change diagD ct.G (aOf d p) ct.yp ct.S ct.v =
      1 + ∑ i ∈ nbhd ct.G ct.S ct.v, ct.ell i -
        ∑ i ∈ nbhd ct.G ct.S ct.v, cEdge (aOf d p) ct.yp ct.v i ^ 2
    rw [diagD, Finset.sum_congr rfl fun i _ => e i, Finset.sum_sub_distrib]
    ring
  -- `Σ ℓ δ ≥ 0`
  have hsED : 0 ≤ ct.sumEllDelta := Finset.sum_nonneg fun i hi => by
    have hiS := ((FloorIns.mem_nbhd ct.G).1 hi).1
    have hcap := (ct.ctx.cap ct.yp ct.ym ct.ctx.hyp ct.ctx.hym i hiS).1
    exact mul_nonneg (hell i) (sub_nonneg.2 hcap)
  -- core traces
  have hw : 0 ≤ ct.wker := lawE_nonneg ct.G fun σ hσ => by
    have hcore : wtCore ct.G p (aOf d p) ct.yp ct.ym σ ct.S ct.v ≠ 0 := by
      intro h0
      apply hσ
      rw [wt_eq_wtCore_mul ct.G hp1 (aOf d p) hy0 hym0 σ ct.ctx.mem, h0, zero_mul, zero_mul]
    have hM := (FloorIns.wtCore_support ct.G hcore).1
    have htr := lv_rootMat_trace_nonneg ct.G hy0 hM
    exact div_nonneg (posSemidef_mul_self (lv_rootMat_isHermitian ct.G _ _ _ _ _ _)).trace_nonneg
      (add_nonneg zero_le_one htr)
  exact ⟨hcard, hell, hL, Finset.sum_nonneg fun i _ => sq_nonneg _, hCJ, hCa, hD, hsED,
    Finset.sum_nonneg fun i _ => lawE_nonneg ct.G fun σ _ => sq_nonneg _,
    Finset.sum_nonneg fun i _ => lawE_nonneg ct.G fun σ _ => sq_nonneg _,
    lawE_nonneg ct.G fun σ _ =>
      (posSemidef_mul_self (lv_rootMat_isHermitian ct.G _ _ _ _ _ _)).trace_nonneg,
    lawE_nonneg ct.G fun σ _ =>
      (posSemidef_mul_self (lv_rootMat_isHermitian ct.G _ _ _ _ _ _)).trace_nonneg, hw⟩

/-- **L-EN** (source l.1586–1594, (E-a)–(E-b) of AUDIT-D §3.2). `K_± ⪰ 0` (Schur product theorem),
`Ω_± ≥ 0`, `u, b_± ≥ 0` entrywise, and Cauchy–Schwarz for the positive semidefinite forms
`(f, g) ↦ E[Ω_± fᵀK_± g]`: `q_± ≥ 0`, `z_± ≥ 0`, `ζ² ≤ q₊ z₊`, `ζ₋² ≤ q₋ z₋`; the off-diagonal Schur
energies `q₊ - t₊ ≥ 0`, `ζ - α ≥ 0`; and `α, β, t_± ≥ 0`. -/
theorem energy_psd (hR : TRegime d p) {h : ℝ} (hh : 0 < h) (ct : Contact.{u} d p) :
    0 ≤ ct.qP h ∧ 0 ≤ ct.zP h ∧ ct.zeta h ^ 2 ≤ ct.qP h * ct.zP h ∧ ct.tP h ≤ ct.qP h ∧
      0 ≤ ct.alphaE h ∧ ct.alphaE h ≤ ct.zeta h ∧ 0 ≤ ct.tP h ∧
      0 ≤ ct.qM h ∧ 0 ≤ ct.zM h ∧ ct.zetaM h ^ 2 ≤ ct.qM h * ct.zM h ∧
      0 ≤ ct.betaE h ∧ 0 ≤ ct.tM h := by
  have hy0 : ∀ k, 0 ≤ ct.yp k := fun k => (ct.ctx.hyp k).1
  have hym0 : ∀ k, 0 ≤ ct.ym k := fun k => (ct.ctx.hym k).1
  have hu : ∀ i, 0 ≤ ct.uvec i := fun i => by
    simp only [Contact.uvec]
    split_ifs
    · positivity
    · exact le_rfl
  have hadj : ∀ i j, 0 ≤ ct.adjS i j := fun i j => by
    simp only [Contact.adjS, Matrix.of_apply]
    split_ifs
    · exact zero_le_one
    · exact le_rfl
  have hKP0 : ∀ σ i k, 0 ≤ ct.KP h σ i k := fun σ i k => by
    simp only [Contact.KP, Matrix.of_apply]
    exact div_nonneg (mul_self_nonneg _) (by norm_num)
  have hMP0 : ∀ σ i k, 0 ≤ ct.MP h σ i k := fun σ i k => by
    simp only [Contact.MP, Matrix.diagonal_apply]
    split_ifs
    · exact sq_nonneg _
    · exact le_rfl
  have hMPK : ∀ σ i k, ct.MP h σ i k ≤ ct.KP h σ i k := fun σ i k => by
    simp only [Contact.MP, Contact.KP, Matrix.diagonal_apply, Matrix.of_apply]
    split_ifs with hik
    · subst hik
      exact le_of_eq (by ring)
    · exact div_nonneg (mul_self_nonneg _) (by norm_num)
  have hbP : ∀ σ i, 0 ≤ ct.bP h σ i := fun σ i => by
    simp only [Contact.bP, Pi.smul_apply, smul_eq_mul]
    exact mul_nonneg (by positivity) (lv_mulVec_nonneg hadj (lv_mulVec_nonneg (hMP0 σ) hu) i)
  have hOmP : ∀ σ, 0 ≤ ct.OmP σ := fun σ => sq_nonneg _
  have hsupp : ∀ σ, wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 →
      (ct.XP h σ).PosSemidef ∧ (ct.XM h σ).PosSemidef ∧ 0 ≤ ct.OmM σ := fun σ hσ => by
    obtain ⟨hPp, hPm⟩ := lv_posDef_of_wt ct.G hσ
    refine ⟨lv_shift_psd ct.G hPp hy0 hh.le, lv_shift_psd ct.G hPm hym0 hh.le, ?_⟩
    exact div_nonneg (mul_nonneg (lv_greenP_diag_nonneg ct.G hPp ct.v)
      (lv_greenP_diag_nonneg ct.G hPm ct.v)) (by norm_num)
  have hKPpsd : ∀ σ, wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 → (ct.KP h σ).PosSemidef :=
    fun σ hσ => lv_had_psd (hsupp σ hσ).1 (hsupp σ hσ).1
  have hKMpsd : ∀ σ, wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 → (ct.KM h σ).PosSemidef :=
    fun σ hσ => lv_had_psd (hsupp σ hσ).1 (hsupp σ hσ).2.1
  have hMM0 : ∀ σ, wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 → ∀ i k, 0 ≤ ct.MM h σ i k :=
    fun σ hσ i k => by
      simp only [Contact.MM, Matrix.diagonal_apply]
      split_ifs
      · exact mul_nonneg (div_nonneg (hsupp σ hσ).1.diag_nonneg (by norm_num))
          (div_nonneg (hsupp σ hσ).2.1.diag_nonneg (by norm_num))
      · exact le_rfl
  have hbM : ∀ σ, wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 → ∀ i, 0 ≤ ct.bM h σ i :=
    fun σ hσ i => by
      simp only [Contact.bM, Pi.smul_apply, smul_eq_mul]
      exact mul_nonneg (by positivity)
        (lv_mulVec_nonneg hadj (lv_mulVec_nonneg (hMM0 σ hσ) hu) i)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact lawE_nonneg ct.G fun σ _ =>
      mul_nonneg (hOmP σ) (lv_dot_mulVec_nonneg (hKP0 σ) hu hu)
  · exact lawE_nonneg ct.G fun σ _ =>
      mul_nonneg (hOmP σ) (lv_dot_mulVec_nonneg (hKP0 σ) (hbP σ) (hbP σ))
  · exact lv_lawE_cs ct.G
      (fun σ _ => mul_nonneg (hOmP σ) (lv_dot_mulVec_nonneg (hKP0 σ) hu hu))
      (fun σ _ => mul_nonneg (hOmP σ) (lv_dot_mulVec_nonneg (hKP0 σ) (hbP σ) (hbP σ)))
      (fun σ hσ => lv_scaled_cs (lv_psd_cs (hKPpsd σ hσ) _ _))
  · exact lv_lawE_mono ct.G fun σ _ =>
      mul_le_mul_of_nonneg_left (lv_dot_mulVec_mono (hMPK σ) hu hu) (hOmP σ)
  · exact lawE_nonneg ct.G fun σ _ =>
      mul_nonneg (hOmP σ) (lv_dot_mulVec_nonneg (hMP0 σ) hu (hbP σ))
  · exact lv_lawE_mono ct.G fun σ _ =>
      mul_le_mul_of_nonneg_left (lv_dot_mulVec_mono (hMPK σ) hu (hbP σ)) (hOmP σ)
  · exact lawE_nonneg ct.G fun σ _ =>
      mul_nonneg (hOmP σ) (lv_dot_mulVec_nonneg (hMP0 σ) hu hu)
  · exact lawE_nonneg ct.G fun σ hσ =>
      mul_nonneg (hsupp σ hσ).2.2 (lv_psd_qf_nonneg (hKMpsd σ hσ) _)
  · exact lawE_nonneg ct.G fun σ hσ =>
      mul_nonneg (hsupp σ hσ).2.2 (lv_psd_qf_nonneg (hKMpsd σ hσ) _)
  · exact lv_lawE_cs ct.G
      (fun σ hσ => mul_nonneg (hsupp σ hσ).2.2 (lv_psd_qf_nonneg (hKMpsd σ hσ) _))
      (fun σ hσ => mul_nonneg (hsupp σ hσ).2.2 (lv_psd_qf_nonneg (hKMpsd σ hσ) _))
      (fun σ hσ => lv_scaled_cs (lv_psd_cs (hKMpsd σ hσ) _ _))
  · exact lawE_nonneg ct.G fun σ hσ =>
      mul_nonneg (hsupp σ hσ).2.2 (lv_dot_mulVec_nonneg (hMM0 σ hσ) hu (hbM σ hσ))
  · exact lawE_nonneg ct.G fun σ hσ =>
      mul_nonneg (hsupp σ hσ).2.2 (lv_dot_mulVec_nonneg (hMM0 σ hσ) hu hu)

/-! ### Mask lemma used by the leaf BM4 -/

/-- **L-BM1** (source (BM1)–(BM3), l.1596–1641; AUDIT-D §3.3 BM1, constant 16, checked
numerically). Deterministic: for `0 ⪯ X, Y ⪯ h⁻¹ I`, `b ≥ 0`, and `X_ii ≤ D` on `I`,
`Σ_{i∈I} Σ_j F_ji² ≤ 16 D² h⁻² bᵀ(X ∘ Y/4) b`. -/
theorem bm1_det {ι : Type*} [Fintype ι] [DecidableEq ι] (X Y : Matrix ι ι ℝ) (b : ι → ℝ)
    (I : Finset ι) {h D : ℝ} (hh : 0 < h) (hX : X.PosSemidef) (hY : Y.PosSemidef)
    (hXn : ∀ w, w ⬝ᵥ (X *ᵥ w) ≤ h⁻¹ * (w ⬝ᵥ w)) (hYn : ∀ w, w ⬝ᵥ (Y *ᵥ w) ≤ h⁻¹ * (w ⬝ᵥ w))
    (hb : ∀ i, 0 ≤ b i) (hD : ∀ i ∈ I, X i i ≤ D) :
    ∑ i ∈ I, ∑ j, maskF X Y b j i ^ 2 ≤
      16 * D ^ 2 * h⁻¹ ^ 2 * (b ⬝ᵥ (Matrix.of (fun i k => X i k * Y i k / 4) *ᵥ b)) := by
  set l := h⁻¹ with hl
  have hl0 : 0 ≤ l := inv_nonneg.2 hh.le
  have hXs : ∀ i j, X j i = X i j := fun i j => by simpa using hX.isHermitian.apply i j
  have hYs : ∀ i j, Y j i = Y i j := fun i j => by simpa using hY.isHermitian.apply i j
  have hXH : Xᴴ = X := hX.isHermitian.eq
  have hYH : Yᴴ = Y := hY.isHermitian.eq
  have hBH : (diagonal b)ᴴ = diagonal b := by
    rw [diagonal_conjTranspose]
    simp
  have hXl := lv_psd_of_qf_le hX hl0 hXn
  have hYl := lv_psd_of_qf_le hY hl0 hYn
  have hX2 : (l • X - X * X).PosSemidef := posSemidef_smul_sub_mul_self hX hl0 hXl
  have hTq := lv_trace_BXBY X Y b hYs
  set B : Matrix ι ι ℝ := diagonal b with hB
  set U := X * B * Y with hU
  set W := (B * Y)ᴴ * X * (B * Y) with hW
  -- positive semidefinite auxiliaries
  have hMX : (B * X * B).PosSemidef := by
    have := hX.conjTranspose_mul_mul_same B
    rwa [hBH] at this
  have hN1 : (B * Y * Y * B).PosSemidef := by
    have := posSemidef_conjTranspose_mul_self (Y * B)
    rwa [conjTranspose_mul, hBH, hYH, ← Matrix.mul_assoc] at this
  have hWpsd : W.PosSemidef := hX.conjTranspose_mul_mul_same (B * Y)
  -- trace identities
  have htrU : (Uᴴ * U).trace = (B * Y * Y * B * (X * X)).trace := by
    have hUH : Uᴴ = Y * B * X := by
      rw [hU, conjTranspose_mul, conjTranspose_mul, hXH, hBH, hYH, ← Matrix.mul_assoc]
    rw [hUH, hU]
    calc (Y * B * X * (X * B * Y)).trace = (Y * (B * X * X * B * Y)).trace := by
          simp only [Matrix.mul_assoc]
      _ = (B * X * X * B * Y * Y).trace := trace_mul_comm _ _
      _ = (B * X * X * (B * Y * Y)).trace := by simp only [Matrix.mul_assoc]
      _ = (B * Y * Y * (B * X * X)).trace := trace_mul_comm _ _
      _ = (B * Y * Y * B * (X * X)).trace := by simp only [Matrix.mul_assoc]
  have htr2 : (B * Y * Y * B * X).trace = (B * X * B * (Y * Y)).trace := by
    calc (B * Y * Y * B * X).trace = (B * Y * Y * (B * X)).trace := by
          simp only [Matrix.mul_assoc]
      _ = (B * X * (B * Y * Y)).trace := trace_mul_comm _ _
      _ = (B * X * B * (Y * Y)).trace := by simp only [Matrix.mul_assoc]
  have htrW : W.trace = (B * X * B * (Y * Y)).trace := by
    have hMH : (B * Y)ᴴ = Y * B := by rw [conjTranspose_mul, hBH, hYH]
    rw [hW, hMH]
    calc (Y * B * X * (B * Y)).trace = (Y * (B * X * B * Y)).trace := by
          simp only [Matrix.mul_assoc]
      _ = (B * X * B * Y * Y).trace := trace_mul_comm _ _
      _ = (B * X * B * (Y * Y)).trace := by simp only [Matrix.mul_assoc]
  -- trace bounds
  have hb1 : (B * Y * Y * B * (X * X)).trace ≤ l * (B * Y * Y * B * X).trace :=
    trace_mul_mul_self_le hN1 hX hl0 hXl
  have hb2 : (B * X * B * (Y * Y)).trace ≤ l * (B * X * B * Y).trace :=
    trace_mul_mul_self_le hMX hY hl0 hYl
  have hTU : (Uᴴ * U).trace ≤ l ^ 2 * (B * X * B * Y).trace := by
    rw [htrU]
    calc (B * Y * Y * B * (X * X)).trace ≤ l * (B * Y * Y * B * X).trace := hb1
      _ = l * (B * X * B * (Y * Y)).trace := by rw [htr2]
      _ ≤ l * (l * (B * X * B * Y).trace) := mul_le_mul_of_nonneg_left hb2 hl0
      _ = l ^ 2 * (B * X * B * Y).trace := by ring
  have hTW : W.trace ≤ l * (B * X * B * Y).trace := by
    rw [htrW]
    exact hb2
  -- pointwise facts
  have hXii : ∀ i, 0 ≤ X i i := fun i => hX.diag_nonneg
  have hXX : ∀ i, (X * X) i i ≤ l * X i i := fun i => by
    have := hX2.diag_nonneg (i := i)
    rw [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at this
    linarith
  have hXX0 : ∀ i, 0 ≤ (X * X) i i := fun i => (posSemidef_mul_self hX.isHermitian).diag_nonneg
  have hUU0 : ∀ i, 0 ≤ (Uᴴ * U) i i := fun i => (posSemidef_conjTranspose_mul_self U).diag_nonneg
  have hW0 : ∀ i, 0 ≤ W i i := fun i => hWpsd.diag_nonneg
  have hcolX : ∀ i, ∑ j, X j i ^ 2 = (X * X) i i := fun i => by
    rw [mul_apply]
    exact Finset.sum_congr rfl fun j _ => by rw [sq, hXs j i]
  have hUii : ∀ i, U i i ^ 2 ≤ X i i * W i i := fun i => by
    have hcs := lv_psd_cs hX (Pi.single i 1) (fun k => (B * Y) k i)
    rw [single_one_dotProduct, single_one_dotProduct, lv_qf_col] at hcs
    have e1 : (X *ᵥ fun k => (B * Y) k i) i = U i i := by
      rw [hU, Matrix.mul_assoc]
      rfl
    have e2 : (X *ᵥ Pi.single i 1) i = X i i := by simp
    rw [e1, e2] at hcs
    exact hcs
  -- the pointwise split `(r - s)² ≤ 2r² + 2s²`
  have hpt : ∀ i, ∑ j, maskF X Y b j i ^ 2 ≤
      2 * X i i ^ 2 * ∑ j, U j i ^ 2 + 2 * U i i ^ 2 * ∑ j, X j i ^ 2 := by
    intro i
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j _ => ?_
    change (X i i * U j i - X j i * U i i) ^ 2 ≤
      2 * X i i ^ 2 * U j i ^ 2 + 2 * U i i ^ 2 * X j i ^ 2
    nlinarith [sq_nonneg (X i i * U j i + X j i * U i i)]
  have hterm : ∀ i ∈ I, 2 * X i i ^ 2 * ∑ j, U j i ^ 2 + 2 * U i i ^ 2 * ∑ j, X j i ^ 2 ≤
      2 * D ^ 2 * (Uᴴ * U) i i + 2 * D ^ 2 * l * W i i := by
    intro i hi
    rw [lv_colsq U i, hcolX i]
    have hD2 : X i i ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ (hXii i) (hD i hi) 2
    have h1 : X i i ^ 2 * (Uᴴ * U) i i ≤ D ^ 2 * (Uᴴ * U) i i :=
      mul_le_mul_of_nonneg_right hD2 (hUU0 i)
    have h2 : U i i ^ 2 * (X * X) i i ≤ l * D ^ 2 * W i i := by
      calc U i i ^ 2 * (X * X) i i ≤ (X i i * W i i) * (X * X) i i :=
            mul_le_mul_of_nonneg_right (hUii i) (hXX0 i)
        _ ≤ (X i i * W i i) * (l * X i i) :=
            mul_le_mul_of_nonneg_left (hXX i) (mul_nonneg (hXii i) (hW0 i))
        _ = l * X i i ^ 2 * W i i := by ring
        _ ≤ l * D ^ 2 * W i i :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hD2 hl0) (hW0 i)
    linarith
  have hD0 : 0 ≤ 2 * D ^ 2 := by positivity
  have hsum : ∑ i ∈ I, (2 * D ^ 2 * (Uᴴ * U) i i + 2 * D ^ 2 * l * W i i) ≤
      ∑ i, (2 * D ^ 2 * (Uᴴ * U) i i + 2 * D ^ 2 * l * W i i) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ I) fun i _ _ =>
      add_nonneg (mul_nonneg hD0 (hUU0 i)) (mul_nonneg (mul_nonneg hD0 hl0) (hW0 i))
  have heq : ∑ i, (2 * D ^ 2 * (Uᴴ * U) i i + 2 * D ^ 2 * l * W i i) =
      2 * D ^ 2 * (Uᴴ * U).trace + 2 * D ^ 2 * l * W.trace := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    rfl
  calc ∑ i ∈ I, ∑ j, maskF X Y b j i ^ 2
      ≤ ∑ i ∈ I, (2 * X i i ^ 2 * ∑ j, U j i ^ 2 + 2 * U i i ^ 2 * ∑ j, X j i ^ 2) :=
        Finset.sum_le_sum fun i _ => hpt i
    _ ≤ ∑ i ∈ I, (2 * D ^ 2 * (Uᴴ * U) i i + 2 * D ^ 2 * l * W i i) := Finset.sum_le_sum hterm
    _ ≤ ∑ i, (2 * D ^ 2 * (Uᴴ * U) i i + 2 * D ^ 2 * l * W i i) := hsum
    _ = 2 * D ^ 2 * (Uᴴ * U).trace + 2 * D ^ 2 * l * W.trace := heq
    _ ≤ 2 * D ^ 2 * (l ^ 2 * (B * X * B * Y).trace) +
          2 * D ^ 2 * l * (l * (B * X * B * Y).trace) :=
        add_le_add (mul_le_mul_of_nonneg_left hTU hD0)
          (mul_le_mul_of_nonneg_left hTW (mul_nonneg hD0 hl0))
    _ = 16 * D ^ 2 * l ^ 2 * (b ⬝ᵥ (Matrix.of (fun i k => X i k * Y i k / 4) *ᵥ b)) := by
        rw [hTq]
        ring

end BiluLinial.Tight
