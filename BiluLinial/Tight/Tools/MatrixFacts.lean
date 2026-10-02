/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Common.Spectral

/-!
# T.MAT: Loewner-order and trace facts, and the B5 matrix bound

Nodes T.MAT (i)–(viii) and B5 of `docs/tight/BP_TOOLS.md` (AUDIT-C §3, §4.3). All matrices are
real and square; `X ⪯ Y` is written `(Y - X).PosSemidef` and `‖·‖` is `BiluLinial.opNorm`.

* `trace_mul_nonneg` (T.MAT-0): `tr(XY) ≥ 0` for `X, Y ⪰ 0` (Schur product theorem:
  `tr(XY) = 1ᵀ (X ⊙ Y) 1`).
* (i) `trace_mul_le_trace_mul`: `M ⪰ 0`, `X ⪯ Y` ⇒ `tr(MX) ≤ tr(MY)`.
* (ii) `posSemidef_smul_sub_mul_self`: `0 ⪯ N ⪯ λI` ⇒ `N² ⪯ λN` (for `λ > 0`:
  `λ(λN - N²) = N(λ-N)N + (λ-N)N(λ-N)`); hence `trace_mul_mul_self_le`: `tr(MN²) ≤ λ tr(MN)`
  (`N = M` gives `tr M³ ≤ ‖M‖ tr M²`); `posSemidef_trace_smul_sub`: `N ⪯ (tr N) I`; and
  `trace_mul_le_trace_mul_trace`: `tr(MN) ≤ tr M · tr N`.
* (iii) `posSemidef_two_sq_add_two_sq_sub_sq`: `(H₁+H₂)² ⪯ 2H₁² + 2H₂²`
  (difference `(H₁ - H₂)²`).
* (iv) `posSemidef_one_sub_inv_sub`: `H ⪰ 0` ⇒ `H - H² ⪯ I - (I+H)⁻¹`; proof by congruence with
  `K = I + H`: `K (I - K⁻¹ - H + H²) K = H (H + H²) H`. Also `I - (I+H)⁻¹ ⪰ 0`, `(I+H)⁻¹ ⪰ 0`.
* (v) `posSemidef_inv_smul_sub_inv_add`: `P ⪰ 0`, `h > 0` ⇒ `(P + hI)⁻¹ ⪯ h⁻¹ I`, so
  `‖(P+hI)⁻¹‖ ≤ 1/h`; `inv_sub_inv_add_smul`: `P⁻¹ - (P+z)⁻¹ = z P⁻¹ (P+z)⁻¹` and
  `posSemidef_inv_sub_inv_add_sub`: it is `⪰ z (P+z)⁻²`, for `P ≻ 0`, `z ≥ 0`.
* (vi) `posSemidef_submatrix_mul_self_sub`: `(X²)[N,N] ⪰ (X[N,N])²` for symmetric `X` and an
  injective reindexing `N ↪ V`.
* (vii) `opNorm_le_opNorm_add`: `‖Δ‖ ≤ ‖Y + Δ‖` for `Y, Δ ⪰ 0`.
* (viii) `trace_mul_one_sub_le`: `0 ⪯ M ⪯ A`, `S ⪯ I` ⇒ `tr(M(I-S)) ≤ tr(A(I-S))`.
* **B5** `trace_mul_hess_sq_div_le`: with `H = 2(p-1)M/α + 2pN/β` (`α, β > 0`, `M, N ⪰ 0`),
  `α⁻¹ tr(MH²) ≤ 8p²(‖M‖ X₁ t₊ + ‖N‖ X₂ t₋)`, `X₁ = tr M²/α²`, `X₂ = tr(MN)/(αβ)`, `t₊ = 1/α`,
  `t₋ = 1/β`. Proof: (iii), (i), (ii).
-/

@[expose] public section

namespace BiluLinial.Tight

open Matrix BiluLinial

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### T.MAT-0: the trace of a product of PSD matrices -/

omit [DecidableEq ι] in
/-- `tr(XY) ≥ 0` for positive semidefinite `X, Y`. -/
theorem trace_mul_nonneg {X Y : Matrix ι ι ℝ} (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    0 ≤ (X * Y).trace := by
  have h := (hX.hadamard hY).dotProduct_mulVec_nonneg (fun _ => (1 : ℝ))
  have hY' : ∀ i j, Y j i = Y i j := fun i j => by simpa using hY.isHermitian.apply i j
  convert h using 1
  simp only [trace, diag, mul_apply, dotProduct, mulVec, hadamard_apply, star_trivial, one_mul,
    mul_one]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hY' i j]

omit [DecidableEq ι] in
theorem posSemidef_mul_self {X : Matrix ι ι ℝ} (hX : X.IsHermitian) : (X * X).PosSemidef := by
  have h := posSemidef_conjTranspose_mul_self X
  rwa [hX.eq] at h

/-- Congruence by an invertible symmetric matrix reflects positive semidefiniteness. -/
theorem posSemidef_of_mul_mul {K S : Matrix ι ι ℝ} (hK : K.IsHermitian) (hKu : IsUnit K)
    (h : (K * S * K).PosSemidef) : S.PosSemidef := by
  have h' := (Matrix.IsUnit.posSemidef_star_left_conjugate_iff (x := S) hKu).1
  rw [star_eq_conjTranspose, hK.eq] at h'
  exact h' h

/-! ### (i) monotonicity of `X ↦ tr(MX)` -/

omit [DecidableEq ι] in
/-- **T.MAT (i).** `M ⪰ 0`, `X ⪯ Y` ⇒ `tr(MX) ≤ tr(MY)`. -/
theorem trace_mul_le_trace_mul {M X Y : Matrix ι ι ℝ} (hM : M.PosSemidef)
    (hXY : (Y - X).PosSemidef) : (M * X).trace ≤ (M * Y).trace := by
  have h := trace_mul_nonneg hM hXY
  rw [mul_sub, trace_sub] at h
  linarith

/-! ### (ii) powers under a norm bound -/

/-- **T.MAT (ii)**, operator form: `0 ⪯ N ⪯ λ I` ⇒ `N² ⪯ λ N`. -/
theorem posSemidef_smul_sub_mul_self {N : Matrix ι ι ℝ} (hN : N.PosSemidef) {l : ℝ}
    (hl : 0 ≤ l) (hNl : (l • (1 : Matrix ι ι ℝ) - N).PosSemidef) :
    (l • N - N * N).PosSemidef := by
  rcases hl.eq_or_lt with rfl | hl
  · have h1 : (-N).PosSemidef := by simpa using hNl
    have htr : N.trace = 0 := le_antisymm
      (by have := h1.trace_nonneg; rwa [trace_neg, neg_nonneg] at this) hN.trace_nonneg
    rw [hN.trace_eq_zero_iff.1 htr]
    simpa using PosSemidef.zero
  · set P := l • (1 : Matrix ι ι ℝ) - N with hP
    have h1 : (Nᴴ * P * N).PosSemidef := hNl.conjTranspose_mul_mul_same N
    have h2 : (Pᴴ * N * P).PosSemidef := hN.conjTranspose_mul_mul_same P
    rw [hN.isHermitian.eq, hNl.isHermitian.eq] at *
    have key : l • (l • N - N * N) = N * P * N + P * N * P := by
      simp only [hP, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
        smul_sub, smul_smul, mul_assoc]
      abel
    have h3 : (l • (l • N - N * N)).PosSemidef := key ▸ h1.add h2
    have h4 := h3.smul (inv_nonneg.2 hl.le)
    rwa [smul_smul, inv_mul_cancel₀ hl.ne', one_smul] at h4

/-- **T.MAT (ii).** `M ⪰ 0`, `0 ⪯ N ⪯ λ I` ⇒ `tr(M N²) ≤ λ tr(M N)`. With `N = M`:
`tr M³ ≤ λ tr M²`. -/
theorem trace_mul_mul_self_le {M N : Matrix ι ι ℝ} (hM : M.PosSemidef) (hN : N.PosSemidef)
    {l : ℝ} (hl : 0 ≤ l) (hNl : (l • (1 : Matrix ι ι ℝ) - N).PosSemidef) :
    (M * (N * N)).trace ≤ l * (M * N).trace := by
  have h := trace_mul_nonneg hM (posSemidef_smul_sub_mul_self hN hl hNl)
  rw [mul_sub, trace_sub, mul_smul_comm, trace_smul, smul_eq_mul] at h
  linarith

/-- A symmetric matrix is at most its norm: `N ⪯ ‖N‖ I`. -/
theorem posSemidef_opNorm_smul_sub {N : Matrix ι ι ℝ} (hN : N.IsHermitian) :
    (opNorm N • (1 : Matrix ι ι ℝ) - N).PosSemidef :=
  ((opNorm_le_iff_posSemidef hN (opNorm_nonneg N)).1 le_rfl).1

/-- `‖N‖ ≤ tr N` for `N ⪰ 0`. -/
theorem opNorm_le_trace {N : Matrix ι ι ℝ} (hN : N.PosSemidef) : opNorm N ≤ N.trace := by
  rw [opNorm_eq_norm_eigenvalues hN.isHermitian]
  refine (pi_norm_le_iff_of_nonneg hN.trace_nonneg).2 fun i => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (hN.eigenvalues_nonneg i),
    hN.isHermitian.trace_eq_sum_eigenvalues]
  simp only [RCLike.ofReal_real_eq_id, id]
  exact Finset.single_le_sum (f := fun j => hN.isHermitian.eigenvalues j)
    (fun j _ => hN.eigenvalues_nonneg j) (Finset.mem_univ i)

/-- `N ⪯ (tr N) I` for `N ⪰ 0` (the largest eigenvalue is at most the trace). -/
theorem posSemidef_trace_smul_sub {N : Matrix ι ι ℝ} (hN : N.PosSemidef) :
    (N.trace • (1 : Matrix ι ι ℝ) - N).PosSemidef :=
  ((opNorm_le_iff_posSemidef hN.isHermitian hN.trace_nonneg).1 (opNorm_le_trace hN)).1

/-- **T.MAT (ii).** `tr(MN) ≤ tr M · tr N` for `M, N ⪰ 0`. -/
theorem trace_mul_le_trace_mul_trace {M N : Matrix ι ι ℝ} (hM : M.PosSemidef)
    (hN : N.PosSemidef) : (M * N).trace ≤ M.trace * N.trace := by
  have h := trace_mul_le_trace_mul hM (posSemidef_trace_smul_sub hN)
  rw [mul_smul_comm, mul_one, trace_smul, smul_eq_mul] at h
  linarith

/-! ### (iii) the square of a sum -/

omit [DecidableEq ι] in
/-- **T.MAT (iii).** `(H₁ + H₂)² ⪯ 2H₁² + 2H₂²` for symmetric `H₁, H₂`. -/
theorem posSemidef_two_sq_add_two_sq_sub_sq {H₁ H₂ : Matrix ι ι ℝ} (h₁ : H₁.IsHermitian)
    (h₂ : H₂.IsHermitian) :
    ((2 : ℝ) • (H₁ * H₁) + (2 : ℝ) • (H₂ * H₂) - (H₁ + H₂) * (H₁ + H₂)).PosSemidef := by
  have e : (2 : ℝ) • (H₁ * H₁) + (2 : ℝ) • (H₂ * H₂) - (H₁ + H₂) * (H₁ + H₂) =
      (H₁ - H₂)ᴴ * (H₁ - H₂) := by
    rw [conjTranspose_sub, h₁.eq, h₂.eq]
    simp only [two_smul, add_mul, mul_add, sub_mul, mul_sub]
    abel
  rw [e]
  exact posSemidef_conjTranspose_mul_self _

/-! ### (iv) the resolvent `(I + H)⁻¹` -/

omit [Fintype ι] in
theorem posDef_one_add {H : Matrix ι ι ℝ} (hH : H.PosSemidef) : (1 + H).PosDef :=
  PosDef.one.add_posSemidef hH

theorem isUnit_det_one_add {H : Matrix ι ι ℝ} (hH : H.PosSemidef) : IsUnit (1 + H).det :=
  ((posDef_one_add hH).isUnit).map Matrix.detMonoidHom

/-- `(I + H)⁻¹ ⪰ 0` for `H ⪰ 0`. -/
theorem posSemidef_inv_one_add {H : Matrix ι ι ℝ} (hH : H.PosSemidef) :
    ((1 + H)⁻¹).PosSemidef :=
  (posDef_one_add hH).inv.posSemidef

/-- `(I + H)⁻¹ ⪯ I` for `H ⪰ 0`. -/
theorem posSemidef_one_sub_inv_one_add {H : Matrix ι ι ℝ} (hH : H.PosSemidef) :
    (1 - (1 + H)⁻¹).PosSemidef := by
  have hK := posDef_one_add hH
  have hKR : (1 + H) * (1 + H)⁻¹ = 1 := Matrix.mul_nonsing_inv (A := 1 + H) (isUnit_det_one_add hH)
  refine posSemidef_of_mul_mul hK.isHermitian hK.isUnit ?_
  have e : (1 + H) * (1 - (1 + H)⁻¹) * (1 + H) = H + Hᴴ * H := by
    rw [mul_sub, mul_one, hKR, sub_mul, one_mul, hH.isHermitian.eq]
    noncomm_ring
  rw [e]
  exact hH.add (posSemidef_conjTranspose_mul_self H)

/-- **T.MAT (iv).** `H - H² ⪯ I - (I + H)⁻¹` for `H ⪰ 0`. -/
theorem posSemidef_one_sub_inv_sub {H : Matrix ι ι ℝ} (hH : H.PosSemidef) :
    (1 - (1 + H)⁻¹ - (H - H * H)).PosSemidef := by
  have hK := posDef_one_add hH
  have hKR : (1 + H) * (1 + H)⁻¹ = 1 := Matrix.mul_nonsing_inv (A := 1 + H) (isUnit_det_one_add hH)
  refine posSemidef_of_mul_mul hK.isHermitian hK.isUnit ?_
  have e : (1 + H) * (1 - (1 + H)⁻¹ - (H - H * H)) * (1 + H) = Hᴴ * (H + Hᴴ * H) * H := by
    rw [mul_sub, mul_sub, mul_one, hKR, sub_mul, sub_mul, one_mul, hH.isHermitian.eq]
    noncomm_ring
  rw [e]
  exact (hH.add (posSemidef_conjTranspose_mul_self H)).conjTranspose_mul_mul_same H

/-- **T.MAT (iv)**, trace form: `tr(M(H - H²)) ≤ tr(M(I - (I+H)⁻¹)) = tr M - tr(M(I+H)⁻¹)`
for `M, H ⪰ 0`. -/
theorem trace_mul_sub_sq_le {M H : Matrix ι ι ℝ} (hM : M.PosSemidef) (hH : H.PosSemidef) :
    (M * (H - H * H)).trace ≤ M.trace - (M * (1 + H)⁻¹).trace := by
  have h := trace_mul_nonneg hM (posSemidef_one_sub_inv_sub hH)
  rw [mul_sub, mul_sub, mul_one, trace_sub, trace_sub] at h
  linarith

/-- `0 ≤ tr(M(I+H)⁻¹) ≤ tr M` for `M, H ⪰ 0`. -/
theorem trace_mul_inv_one_add_mem {M H : Matrix ι ι ℝ} (hM : M.PosSemidef)
    (hH : H.PosSemidef) :
    0 ≤ (M * (1 + H)⁻¹).trace ∧ (M * (1 + H)⁻¹).trace ≤ M.trace := by
  refine ⟨trace_mul_nonneg hM (posSemidef_inv_one_add hH), ?_⟩
  have h := trace_mul_nonneg hM (posSemidef_one_sub_inv_one_add hH)
  rw [mul_sub, mul_one, trace_sub] at h
  linarith

/-! ### (v) shifted inverses -/

omit [Fintype ι] in
theorem posDef_add_smul_one {P : Matrix ι ι ℝ} (hP : P.PosSemidef) {h : ℝ} (hh : 0 < h) :
    (P + h • (1 : Matrix ι ι ℝ)).PosDef :=
  PosDef.posSemidef_add hP (PosDef.one.smul hh)

/-- **T.MAT (v).** `(P + hI)⁻¹ ⪯ h⁻¹ I` for `P ⪰ 0`, `h > 0`. -/
theorem posSemidef_inv_smul_sub_inv_add {P : Matrix ι ι ℝ} (hP : P.PosSemidef) {h : ℝ}
    (hh : 0 < h) : (h⁻¹ • (1 : Matrix ι ι ℝ) - (P + h • 1)⁻¹).PosSemidef := by
  have hK := posDef_add_smul_one hP hh
  have hKR : (P + h • 1) * (P + h • 1)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv (A := P + h • 1) (hK.isUnit.map Matrix.detMonoidHom)
  have hT : (1 - h • (P + h • 1)⁻¹).PosSemidef := by
    refine posSemidef_of_mul_mul hK.isHermitian hK.isUnit ?_
    have e : (P + h • 1) * (1 - h • (P + h • 1)⁻¹) * (P + h • 1) = Pᴴ * P + h • P := by
      rw [mul_sub, mul_one, mul_smul_comm, hKR, sub_mul, smul_mul_assoc, one_mul,
        hP.isHermitian.eq]
      simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_add,
        smul_smul]
      abel
    rw [e]
    exact (posSemidef_conjTranspose_mul_self P).add (hP.smul hh.le)
  have h4 := hT.smul (inv_nonneg.2 hh.le)
  rwa [smul_sub, smul_smul, inv_mul_cancel₀ hh.ne', one_smul] at h4

/-- **T.MAT (v).** `‖(P + hI)⁻¹‖ ≤ 1/h` for `P ⪰ 0`, `h > 0`. -/
theorem opNorm_inv_add_smul_le {P : Matrix ι ι ℝ} (hP : P.PosSemidef) {h : ℝ} (hh : 0 < h) :
    opNorm (P + h • (1 : Matrix ι ι ℝ))⁻¹ ≤ h⁻¹ := by
  have hR := (posDef_add_smul_one hP hh).inv.posSemidef
  refine (opNorm_le_iff_posSemidef hR.isHermitian (inv_nonneg.2 hh.le)).2
    ⟨posSemidef_inv_smul_sub_inv_add hP hh, ?_⟩
  exact (PosSemidef.one.smul (inv_nonneg.2 hh.le)).add hR

/-- **T.MAT (v).** `P⁻¹ - (P + zI)⁻¹ = z P⁻¹ (P + zI)⁻¹` for `P ≻ 0`, `z ≥ 0`. -/
theorem inv_sub_inv_add_smul {P : Matrix ι ι ℝ} (hP : P.PosDef) {z : ℝ} (hz : 0 ≤ z) :
    P⁻¹ - (P + z • (1 : Matrix ι ι ℝ))⁻¹ = z • (P⁻¹ * (P + z • (1 : Matrix ι ι ℝ))⁻¹) := by
  have hQ : (P + z • (1 : Matrix ι ι ℝ)).PosDef := hP.add_posSemidef (PosSemidef.one.smul hz)
  have h1 : P⁻¹ * (P + z • 1) * (P + z • 1)⁻¹ = P⁻¹ := by
    rw [mul_assoc, Matrix.mul_nonsing_inv (A := P + z • 1) (hQ.isUnit.map Matrix.detMonoidHom),
      mul_one]
  have h2 : P⁻¹ * P * (P + z • 1)⁻¹ = (P + z • 1)⁻¹ := by
    rw [Matrix.nonsing_inv_mul (A := P) (hP.isUnit.map Matrix.detMonoidHom), one_mul]
  calc P⁻¹ - (P + z • 1)⁻¹ = P⁻¹ * (P + z • 1) * (P + z • 1)⁻¹ - P⁻¹ * P * (P + z • 1)⁻¹ := by
        rw [h1, h2]
    _ = z • (P⁻¹ * (P + z • 1)⁻¹) := by
        rw [← sub_mul, ← mul_sub, add_sub_cancel_left, mul_smul_comm, mul_one, smul_mul_assoc]

/-- **T.MAT (v).** `P⁻¹ - (P + zI)⁻¹ ⪰ z (P + zI)⁻²` for `P ≻ 0`, `z ≥ 0`. -/
theorem posSemidef_inv_sub_inv_add_sub {P : Matrix ι ι ℝ} (hP : P.PosDef) {z : ℝ}
    (hz : 0 ≤ z) :
    (P⁻¹ - (P + z • (1 : Matrix ι ι ℝ))⁻¹ -
      z • ((P + z • (1 : Matrix ι ι ℝ))⁻¹ * (P + z • (1 : Matrix ι ι ℝ))⁻¹)).PosSemidef := by
  set Q := P + z • (1 : Matrix ι ι ℝ) with hQdef
  have hQ : Q.PosDef := hP.add_posSemidef (PosSemidef.one.smul hz)
  have hcomm : P⁻¹ * Q⁻¹ = Q⁻¹ * P⁻¹ := by
    rw [← Matrix.mul_inv_rev, ← Matrix.mul_inv_rev]
    congr 1
    simp only [hQdef, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
  have e : P⁻¹ - Q⁻¹ - z • (Q⁻¹ * Q⁻¹) = (z * z) • ((Q⁻¹)ᴴ * P⁻¹ * Q⁻¹) := by
    rw [inv_sub_inv_add_smul hP hz, ← smul_sub, ← sub_mul, inv_sub_inv_add_smul hP hz,
      smul_mul_assoc, smul_smul, hQ.inv.isHermitian.eq, hcomm]
  rw [e]
  exact (hP.inv.posSemidef.conjTranspose_mul_mul_same Q⁻¹).smul (mul_nonneg hz hz)

/-! ### (vi) principal blocks of a square -/

omit [DecidableEq ι] in
theorem dotProduct_mulVec_comm_of_symm {S : Matrix ι ι ℝ} (hS : S.IsHermitian) (x v : ι → ℝ) :
    x ⬝ᵥ (S *ᵥ v) = (S *ᵥ x) ⬝ᵥ v := by
  have hSt : Sᵀ = S := by simpa [conjTranspose_eq_transpose_of_trivial] using hS.eq
  rw [dotProduct_mulVec, ← mulVec_transpose, hSt]

omit [DecidableEq ι] in
/-- **T.MAT (vi).** `(X²)[N,N] ⪰ (X[N,N])²` for symmetric `X` and injective `f : κ → ι`. -/
theorem posSemidef_submatrix_mul_self_sub {κ : Type*} [Fintype κ] {X : Matrix ι ι ℝ}
    (hX : X.IsHermitian) {f : κ → ι} (hf : Function.Injective f) :
    ((X * X).submatrix f f - X.submatrix f f * X.submatrix f f).PosSemidef := by
  have hXX : (X * X).IsHermitian := by
    have h := isHermitian_mul_conjTranspose_self X
    rwa [hX.eq] at h
  have hXf : (X.submatrix f f).IsHermitian := hX.submatrix f
  have hXfXf : (X.submatrix f f * X.submatrix f f).IsHermitian := by
    have h := isHermitian_mul_conjTranspose_self (X.submatrix f f)
    rwa [hXf.eq] at h
  refine PosSemidef.of_dotProduct_mulVec_nonneg ((hXX.submatrix f).sub hXfXf) fun x => ?_
  obtain ⟨y, hyf, hsum⟩ := BiluLinial.exists_extend hf x
  set u := X *ᵥ y
  have h1 : ∀ a, ((X * X).submatrix f f *ᵥ x) a = ((X * X) *ᵥ y) (f a) := fun a =>
    (hsum ((X * X) (f a))).symm
  have h2 : ∀ a, (X.submatrix f f *ᵥ x) a = u (f a) := fun a => (hsum (X (f a))).symm
  have e1 : x ⬝ᵥ ((X * X).submatrix f f *ᵥ x) = u ⬝ᵥ u := by
    calc x ⬝ᵥ ((X * X).submatrix f f *ᵥ x) = ∑ a, ((X * X) *ᵥ y) (f a) * x a := by
          simp only [dotProduct, h1, mul_comm]
      _ = ∑ i, ((X * X) *ᵥ y) i * y i := (hsum _).symm
      _ = y ⬝ᵥ (X *ᵥ (X *ᵥ y)) := by
          simp only [dotProduct, mulVec_mulVec, mul_comm]
      _ = u ⬝ᵥ u := dotProduct_mulVec_comm_of_symm hX y u
  have e2 : x ⬝ᵥ ((X.submatrix f f * X.submatrix f f) *ᵥ x) = ∑ a, u (f a) * u (f a) := by
    rw [← mulVec_mulVec, dotProduct_mulVec_comm_of_symm hXf]
    simp only [dotProduct, h2]
  simp only [star_trivial, sub_mulVec, dotProduct_sub, e1, e2, sub_nonneg]
  exact BiluLinial.sum_comp_le_sum hf (fun i => u i * u i) fun i => mul_self_nonneg _

/-! ### (vii) monotonicity of the norm on PSD matrices -/

/-- **T.MAT (vii).** `‖Δ‖ ≤ ‖Y + Δ‖` for `Y, Δ ⪰ 0`. -/
theorem opNorm_le_opNorm_add {Y Δ : Matrix ι ι ℝ} (hY : Y.PosSemidef) (hΔ : Δ.PosSemidef) :
    opNorm Δ ≤ opNorm (Y + Δ) := by
  have hr := opNorm_nonneg (Y + Δ)
  have h1 := posSemidef_opNorm_smul_sub (hY.add hΔ).isHermitian
  refine (opNorm_le_iff_posSemidef hΔ.isHermitian hr).2 ⟨?_, (PosSemidef.one.smul hr).add hΔ⟩
  have e : opNorm (Y + Δ) • (1 : Matrix ι ι ℝ) - Δ =
      (opNorm (Y + Δ) • (1 : Matrix ι ι ℝ) - (Y + Δ)) + Y := by abel
  rw [e]
  exact h1.add hY

/-! ### (viii) -/

/-- **T.MAT (viii).** `0 ⪯ M ⪯ A` and `S ⪯ I` ⇒ `tr(M(I - S)) ≤ tr(A(I - S))`. -/
theorem trace_mul_one_sub_le {A M S : Matrix ι ι ℝ} (hMA : (A - M).PosSemidef)
    (hS : (1 - S).PosSemidef) : (M * (1 - S)).trace ≤ (A * (1 - S)).trace := by
  have h := trace_mul_nonneg hMA hS
  rw [sub_mul, trace_sub] at h
  linarith

/-! ### B5 -/

/-- **B5.** For `M, N ⪰ 0`, `α, β > 0`, `p ≥ 1` and `H = 2(p-1)M/α + 2pN/β`:
`α⁻¹ tr(M H²) ≤ 8p² (‖M‖ X₁ t₊ + ‖N‖ X₂ t₋)` with `X₁ = tr M²/α²`, `X₂ = tr(MN)/(αβ)`,
`t₊ = 1/α`, `t₋ = 1/β`. (`2((p-1 : ℕ) : ℝ)` is the coefficient of `clipHess (p-1) p`.) -/
theorem trace_mul_hess_sq_div_le {M N : Matrix ι ι ℝ} (hM : M.PosSemidef) (hN : N.PosSemidef)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (p : ℕ) :
    (M * (((2 * ((p - 1 : ℕ) : ℝ) / a) • M + (2 * (p : ℝ) / b) • N) *
        ((2 * ((p - 1 : ℕ) : ℝ) / a) • M + (2 * (p : ℝ) / b) • N))).trace / a ≤
      8 * (p : ℝ) ^ 2 * (opNorm M * ((M * M).trace / a ^ 2) * (1 / a) +
        opNorm N * ((M * N).trace / (a * b)) * (1 / b)) := by
  set q : ℝ := ((p - 1 : ℕ) : ℝ) with hq
  have hq0 : 0 ≤ q := Nat.cast_nonneg _
  have hqp : q ≤ p := by rw [hq]; exact_mod_cast Nat.sub_le p 1
  set c₁ := 2 * q / a with hc₁
  set c₂ := 2 * (p : ℝ) / b with hc₂
  have hc₁0 : 0 ≤ c₁ := by positivity
  have hc₂0 : 0 ≤ c₂ := by positivity
  have hH₁ : (c₁ • M).PosSemidef := hM.smul hc₁0
  have hH₂ : (c₂ • N).PosSemidef := hN.smul hc₂0
  -- (iii) and (i)
  have h1 := trace_mul_le_trace_mul hM
    (posSemidef_two_sq_add_two_sq_sub_sq hH₁.isHermitian hH₂.isHermitian)
  have e1 : (M * ((2 : ℝ) • (c₁ • M * (c₁ • M)) + (2 : ℝ) • (c₂ • N * (c₂ • N)))).trace =
      2 * c₁ ^ 2 * (M * (M * M)).trace + 2 * c₂ ^ 2 * (M * (N * N)).trace := by
    simp only [mul_add, trace_add, smul_mul_assoc, mul_smul_comm, trace_smul, smul_eq_mul,
      smul_smul]
    ring
  rw [e1] at h1
  -- (ii)
  have h2 := trace_mul_mul_self_le hM hM (opNorm_nonneg M)
    (posSemidef_opNorm_smul_sub hM.isHermitian)
  have h3 := trace_mul_mul_self_le hM hN (opNorm_nonneg N)
    (posSemidef_opNorm_smul_sub hN.isHermitian)
  have h4 : 0 ≤ (M * (M * M)).trace := trace_mul_nonneg hM (posSemidef_mul_self hM.isHermitian)
  have hc₁2 : 2 * c₁ ^ 2 ≤ 8 * (p : ℝ) ^ 2 / a ^ 2 := by
    rw [hc₁, div_pow, mul_pow, le_div_iff₀ (by positivity)]
    field_simp
    nlinarith
  have hc₂2 : 2 * c₂ ^ 2 = 8 * (p : ℝ) ^ 2 / b ^ 2 := by
    rw [hc₂]; field_simp; ring
  have h5 : (M * ((c₁ • M + c₂ • N) * (c₁ • M + c₂ • N))).trace ≤
      8 * (p : ℝ) ^ 2 / a ^ 2 * (opNorm M * (M * M).trace) +
        8 * (p : ℝ) ^ 2 / b ^ 2 * (opNorm N * (M * N).trace) := by
    refine h1.trans ?_
    rw [hc₂2]
    have hpa : 0 ≤ 8 * (p : ℝ) ^ 2 / a ^ 2 := by positivity
    have hpb : 0 ≤ 8 * (p : ℝ) ^ 2 / b ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_left h3 hpb
    nlinarith [mul_le_mul_of_nonneg_right hc₁2 h4, mul_le_mul_of_nonneg_left h2 hpa]
  calc (M * ((c₁ • M + c₂ • N) * (c₁ • M + c₂ • N))).trace / a ≤
        (8 * (p : ℝ) ^ 2 / a ^ 2 * (opNorm M * (M * M).trace) +
          8 * (p : ℝ) ^ 2 / b ^ 2 * (opNorm N * (M * N).trace)) / a :=
        div_le_div_of_nonneg_right h5 ha.le
    _ = _ := by field_simp

/-- **B5** with a common norm bound `‖M‖, ‖N‖ ≤ L` (e.g. `L = s a²/h`). -/
theorem trace_mul_hess_sq_div_le' {M N : Matrix ι ι ℝ} (hM : M.PosSemidef) (hN : N.PosSemidef)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (p : ℕ) {L : ℝ} (hML : opNorm M ≤ L)
    (hNL : opNorm N ≤ L) :
    (M * (((2 * ((p - 1 : ℕ) : ℝ) / a) • M + (2 * (p : ℝ) / b) • N) *
        ((2 * ((p - 1 : ℕ) : ℝ) / a) • M + (2 * (p : ℝ) / b) • N))).trace / a ≤
      8 * (p : ℝ) ^ 2 * L *
        ((M * M).trace / a ^ 2 * (1 / a) + (M * N).trace / (a * b) * (1 / b)) := by
  refine (trace_mul_hess_sq_div_le hM hN ha hb p).trans ?_
  have hX₁ : 0 ≤ (M * M).trace / a ^ 2 * (1 / a) :=
    mul_nonneg (div_nonneg (trace_mul_nonneg hM hM) (by positivity)) (by positivity)
  have hX₂ : 0 ≤ (M * N).trace / (a * b) * (1 / b) :=
    mul_nonneg (div_nonneg (trace_mul_nonneg hM hN) (by positivity)) (by positivity)
  have hp : 0 ≤ 8 * (p : ℝ) ^ 2 := by positivity
  have := add_le_add (mul_le_mul_of_nonneg_right hML hX₁) (mul_le_mul_of_nonneg_right hNL hX₂)
  calc 8 * (p : ℝ) ^ 2 * (opNorm M * ((M * M).trace / a ^ 2) * (1 / a) +
        opNorm N * ((M * N).trace / (a * b)) * (1 / b))
      = 8 * (p : ℝ) ^ 2 * (opNorm M * ((M * M).trace / a ^ 2 * (1 / a)) +
        opNorm N * ((M * N).trace / (a * b) * (1 / b))) := by ring
    _ ≤ 8 * (p : ℝ) ^ 2 * (L * ((M * M).trace / a ^ 2 * (1 / a)) +
        L * ((M * N).trace / (a * b) * (1 / b))) := mul_le_mul_of_nonneg_left this hp
    _ = _ := by ring

end BiluLinial.Tight
