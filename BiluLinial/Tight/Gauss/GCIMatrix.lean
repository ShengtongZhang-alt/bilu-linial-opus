/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import Mathlib

/-!
# Matrix lemmas for Royen's Gaussian correlation argument

Linear-algebra nodes of the GCI subtree (`docs/tight/GCI_PLAN.md`):

* `det_one_add_diagonal_mul` (GCI-R2): `det (1 + D C) = ∑_J (∏_{i ∈ J} m_i) det C[J, J]` for a
  diagonal `D = diagonal m`.
* `one_le_det_one_add_diagonal_mul` (GCI-R2b): for `C ⪰ 0` and `m ≥ 0`, `1 ≤ det (1 + D C)`.
* `det_le_det_of_posSemidef_sub` (GCI-R3a): `det` is monotone in the Loewner order on PSD
  matrices.
* `det_sideScale_antitoneOn` (GCI-R3): Royen's determinant monotonicity. If `M ⪰ 0` and the
  entries of `M` linking the two sides of a partition are multiplied by `s`, the determinant is
  antitone in `s ∈ [0, 1]`.
* `differentiable_det` (GCI-DET): a determinant of differentiable entries is differentiable.
-/

@[expose] public section

namespace BiluLinial.Tight

open Matrix
open scoped MatrixOrder

section R2

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **GCI-R2.** Principal-minor expansion of `det (1 + diagonal m * C)`. -/
theorem det_one_add_diagonal_mul (m : n → ℝ) (C : Matrix n n ℝ) :
    (1 + diagonal m * C).det =
      ∑ J : Finset n, (∏ i ∈ J, m i) * (C.submatrix (Subtype.val : J → n) Subtype.val).det := by
  let D := (detRowAlternating : (n → ℝ) [⋀^n]→ₗ[ℝ] ℝ)
  have hrow : (1 + diagonal m * C) =
      ((fun i => m i • C.row i) + fun i => (1 : Matrix n n ℝ).row i : n → n → ℝ) := by
    ext i j
    simp [diagonal_mul, add_comm, Matrix.row]
  rw [det, hrow]
  change D ((fun i => m i • C.row i) + fun i => (1 : Matrix n n ℝ).row i) = _
  rw [D.map_add_univ, ← Finset.powerset_univ]
  refine Finset.sum_congr rfl fun s _ => ?_
  have hpw : s.piecewise (fun i => m i • C.row i) (fun i => (1 : Matrix n n ℝ).row i) =
      s.piecewise (fun i => m i • (s.piecewise C.row (1 : Matrix n n ℝ).row) i)
        (s.piecewise C.row (1 : Matrix n n ℝ).row) := by
    ext i j
    by_cases hi : i ∈ s <;> simp [Finset.piecewise, hi]
  rw [hpw]
  calc D (s.piecewise (fun i => m i • (s.piecewise C.row (1 : Matrix n n ℝ).row) i)
        (s.piecewise C.row (1 : Matrix n n ℝ).row))
      = (∏ i ∈ s, m i) • D (s.piecewise C.row (1 : Matrix n n ℝ).row) :=
        D.map_piecewise_smul m _ s
    _ = _ := by
        rw [smul_eq_mul]
        congr 1
        exact det_piecewise_one_eq_submatrix_det C s

/-- **GCI-R2b.** For `C ⪰ 0` and `m ≥ 0`, `det (1 + diagonal m * C) ≥ 1`. -/
theorem one_le_det_one_add_diagonal_mul {m : n → ℝ} (hm : ∀ i, 0 ≤ m i) {C : Matrix n n ℝ}
    (hC : C.PosSemidef) : 1 ≤ (1 + diagonal m * C).det := by
  rw [det_one_add_diagonal_mul]
  have hterm : ∀ J : Finset n,
      0 ≤ (∏ i ∈ J, m i) * (C.submatrix (Subtype.val : J → n) Subtype.val).det :=
    fun J => mul_nonneg (Finset.prod_nonneg fun i _ => hm i) (hC.submatrix _).det_nonneg
  have h0 : (∏ i ∈ (∅ : Finset n), m i) *
      (C.submatrix (Subtype.val : (∅ : Finset n) → n) Subtype.val).det = 1 := by
    have : IsEmpty (∅ : Finset n) := ⟨fun x => absurd x.2 (Finset.notMem_empty _)⟩
    simp [Matrix.det_isEmpty]
  calc (1 : ℝ) = _ := h0.symm
    _ ≤ _ := Finset.single_le_sum (fun J _ => hterm J) (Finset.mem_univ _)

/-- `det (1 + K) ≥ 1` for `K ⪰ 0`. -/
theorem one_le_det_one_add {K : Matrix n n ℝ} (hK : K.PosSemidef) : 1 ≤ (1 + K).det := by
  simpa using one_le_det_one_add_diagonal_mul (m := fun _ => (1 : ℝ)) (fun _ => zero_le_one) hK

end R2

section R3a

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **GCI-R3a.** The determinant is monotone in the Loewner order on PSD matrices. -/
theorem det_le_det_of_posSemidef_sub {X Y : Matrix n n ℝ} (hX : X.PosSemidef)
    (hXY : (Y - X).PosSemidef) : X.det ≤ Y.det := by
  have hY : Y.PosSemidef := by simpa using hX.add hXY
  by_cases hdet : X.det = 0
  · rw [hdet]; exact hY.det_nonneg
  obtain ⟨a, ha⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hX.nonneg
  rw [star_eq_conjTranspose] at ha
  have hadet : a.det ≠ 0 := by
    intro h0
    apply hdet
    rw [ha, det_mul, h0, mul_zero]
  have hau : IsUnit a.det := isUnit_iff_ne_zero.mpr hadet
  set E := Y - X with hE
  set K := (a⁻¹)ᴴ * E * a⁻¹ with hK
  have hKpsd : K.PosSemidef := hXY.conjTranspose_mul_mul_same _
  have hYeq : Y = aᴴ * (1 + K) * a := by
    have h1 : a⁻¹ * a = 1 := nonsing_inv_mul a hau
    have h2 : aᴴ * (a⁻¹)ᴴ = 1 := by
      rw [← conjTranspose_mul, h1, conjTranspose_one]
    have hYXE : Y = X + E := by rw [hE]; abel
    rw [hYXE, ha, hK, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one]
    congr 1
    calc E = aᴴ * (a⁻¹)ᴴ * E * (a⁻¹ * a) := by
            rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
      _ = aᴴ * ((a⁻¹)ᴴ * E * a⁻¹) * a := by simp only [Matrix.mul_assoc]
  have hXdet : X.det = aᴴ.det * a.det := by rw [ha, det_mul]
  have hYdet : Y.det = X.det * (1 + K).det := by
    rw [hYeq, det_mul, det_mul, hXdet]; ring
  rw [hYdet]
  have hXnn : 0 ≤ X.det := hX.det_nonneg
  have h1K := one_le_det_one_add hKpsd
  nlinarith

end R3a

section R3

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- The block matrix `N` with its off-diagonal blocks multiplied by `s`. -/
def blockScale (N : Matrix (α ⊕ β) (α ⊕ β) ℝ) (s : ℝ) : Matrix (α ⊕ β) (α ⊕ β) ℝ :=
  fromBlocks N.toBlocks₁₁ (s • N.toBlocks₁₂) (s • N.toBlocks₂₁) N.toBlocks₂₂

omit [Fintype α] [Fintype β] in
theorem blockScale_add_smul_one (N : Matrix (α ⊕ β) (α ⊕ β) ℝ) (s ε : ℝ) :
    blockScale (N + ε • 1) s = blockScale N s + ε • 1 := by
  ext (i | i) (j | j) <;>
    simp [blockScale, toBlocks₁₁, toBlocks₁₂, toBlocks₂₁, toBlocks₂₂, one_apply]

/-- Royen's determinant monotonicity, case of a positive definite upper-left block. -/
theorem det_blockScale_antitoneOn_of_posDef {N : Matrix (α ⊕ β) (α ⊕ β) ℝ}
    (hN : N.PosSemidef) (hP : N.toBlocks₁₁.PosDef) :
    AntitoneOn (fun s => (blockScale N s).det) (Set.Icc 0 1) := by
  set P := N.toBlocks₁₁
  set Q := N.toBlocks₁₂
  set R := N.toBlocks₂₂
  have hQ' : N.toBlocks₂₁ = Qᴴ := by
    have := hN.1
    ext i j
    simpa [toBlocks₂₁, toBlocks₁₂, Q] using congrFun (congrFun this (Sum.inl j)) (Sum.inr i)
  have hNblk : N = fromBlocks P Q Qᴴ R := by
    rw [← hQ']; exact (fromBlocks_toBlocks N).symm
  have : Invertible P := hP.isUnit.invertible
  set K := Qᴴ * P⁻¹ * Q with hK
  have hKpsd : K.PosSemidef := hP.inv.posSemidef.conjTranspose_mul_mul_same Q
  have hSchur : (R - K).PosSemidef := by
    have h := hN
    rw [hNblk] at h
    exact (PosDef.fromBlocks₁₁ Q R hP).mp h
  have hdet : ∀ s, (blockScale N s).det = P.det * (R - (s ^ 2) • K).det := by
    intro s
    have : blockScale N s = fromBlocks P (s • Q) (s • Qᴴ) R := by
      simp [blockScale, hQ', P, Q, R]
    rw [this, det_fromBlocks₁₁, invOf_eq_nonsing_inv]
    congr 2
    simp only [hK, Matrix.smul_mul, Matrix.mul_smul, smul_smul, sq]
  intro s hs t ht hst
  simp only [hdet]
  have hPdet : 0 < P.det := hP.det_pos
  refine mul_le_mul_of_nonneg_left ?_ hPdet.le
  apply det_le_det_of_posSemidef_sub
  · have : R - (t ^ 2) • K = (R - K) + (1 - t ^ 2) • K := by
      rw [sub_smul, one_smul]; abel
    rw [this]
    refine hSchur.add (hKpsd.smul ?_)
    nlinarith [ht.1, ht.2]
  · have : R - (s ^ 2) • K - (R - (t ^ 2) • K) = (t ^ 2 - s ^ 2) • K := by
      rw [sub_smul]; abel
    rw [this]
    refine hKpsd.smul ?_
    nlinarith [hs.1, hst]

/-- Royen's determinant monotonicity for block matrices. -/
theorem det_blockScale_antitoneOn {N : Matrix (α ⊕ β) (α ⊕ β) ℝ} (hN : N.PosSemidef) :
    AntitoneOn (fun s => (blockScale N s).det) (Set.Icc 0 1) := by
  intro s hs t ht hst
  have hε : ∀ ε : ℝ, 0 < ε →
      (blockScale N t + ε • 1).det ≤ (blockScale N s + ε • 1).det := by
    intro ε hε
    have hNε : (N + ε • 1).PosSemidef := hN.add (PosSemidef.one.smul hε.le)
    have hPε : (N + ε • 1).toBlocks₁₁.PosDef := by
      have : (N + ε • 1).toBlocks₁₁ = N.toBlocks₁₁ + ε • 1 := by
        ext i j; simp [toBlocks₁₁, one_apply]
      rw [this]
      have hP0 : N.toBlocks₁₁.PosSemidef := hN.submatrix (Sum.inl : α → α ⊕ β)
      exact PosDef.posSemidef_add hP0 (PosDef.one.smul hε)
    have := det_blockScale_antitoneOn_of_posDef hNε hPε hs ht hst
    simpa [blockScale_add_smul_one] using this
  have hcont : ∀ u, Continuous fun ε : ℝ => (blockScale N u + ε • 1).det := fun u => by
    fun_prop
  have hlim : ∀ u, Filter.Tendsto (fun ε : ℝ => (blockScale N u + ε • 1).det)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (blockScale N u).det) := by
    intro u
    have := ((hcont u).tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    simpa using this
  exact le_of_tendsto_of_tendsto (hlim t) (hlim s)
    (eventually_nhdsWithin_of_forall fun ε hε0 => hε ε hε0)

end R3

section sideScale

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The matrix `M` with the entries linking `{σ}` and `{¬σ}` multiplied by `s`. -/
def sideScale (M : Matrix κ κ ℝ) (σ : κ → Prop) [DecidablePred σ] (s : ℝ) : Matrix κ κ ℝ :=
  Matrix.of fun a b => if (σ a ↔ σ b) then M a b else s * M a b

omit [Fintype κ] [DecidableEq κ] in
theorem sideScale_submatrix {μ : Type*} (M : Matrix κ κ ℝ) (σ : κ → Prop) [DecidablePred σ]
    (s : ℝ) (f : μ → κ) :
    (sideScale M σ s).submatrix f f = sideScale (M.submatrix f f) (fun a => σ (f a)) s := by
  ext a b
  simp [sideScale]

/-- **GCI-R3** (Royen's determinant monotonicity). If `M ⪰ 0`, the determinant of `M` with the
entries between the two sides of a partition multiplied by `s` is antitone in `s ∈ [0, 1]`. -/
theorem det_sideScale_antitoneOn {M : Matrix κ κ ℝ} (hM : M.PosSemidef) (σ : κ → Prop)
    [DecidablePred σ] : AntitoneOn (fun s => (sideScale M σ s).det) (Set.Icc 0 1) := by
  let e := Equiv.sumCompl σ
  have hblk : ∀ s, (sideScale M σ s).submatrix e e = blockScale (M.submatrix e e) s := by
    intro s
    ext (i | i) (j | j)
    · simp [sideScale, blockScale, e, toBlocks₁₁, i.2, j.2]
    · simp [sideScale, blockScale, e, toBlocks₁₂, i.2, j.2]
    · simp [sideScale, blockScale, e, toBlocks₂₁, i.2, j.2]
    · simp [sideScale, blockScale, e, toBlocks₂₂, i.2, j.2]
  have hdet : ∀ s, (sideScale M σ s).det = (blockScale (M.submatrix e e) s).det := by
    intro s
    rw [← hblk, det_submatrix_equiv_self]
  simp only [hdet]
  exact det_blockScale_antitoneOn (hM.submatrix e)

end sideScale

section calculus

/-- An antitone function on `[a, b]` has nonpositive derivative at interior points. -/
theorem deriv_nonpos_of_antitoneOn {f : ℝ → ℝ} {a b s : ℝ} (hf : AntitoneOn f (Set.Icc a b))
    (hs : s ∈ Set.Ioo a b) : deriv f s ≤ 0 := by
  have h1 : MonotoneOn (fun x => -f x) (Set.Ioo a b) := fun x hx y hy hxy =>
    neg_le_neg (hf (Set.Ioo_subset_Icc_self hx) (Set.Ioo_subset_Icc_self hy) hxy)
  have h2 := h1.derivWithin_nonneg (x := s)
  rw [derivWithin_of_isOpen isOpen_Ioo hs, deriv.fun_neg] at h2
  linarith

/-- **GCI-DET.** A determinant of differentiable entries is differentiable. -/
theorem differentiable_det {κ : Type*} [Fintype κ] [DecidableEq κ] {M : ℝ → Matrix κ κ ℝ}
    (hM : ∀ i j, Differentiable ℝ fun s => M s i j) : Differentiable ℝ fun s => (M s).det := by
  simp_rw [det_apply']
  exact Differentiable.fun_sum fun σ _ =>
    (differentiable_const _).mul (Differentiable.fun_finsetProd fun i _ => hM _ _)

end calculus

end BiluLinial.Tight
