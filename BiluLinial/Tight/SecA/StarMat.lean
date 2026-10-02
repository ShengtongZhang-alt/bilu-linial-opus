/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.Tools.MatrixFacts

/-!
# Prefactor domination (`A-PDOM`)

Node `A-PDOM` of `docs/tight/BP_SECA.md` (source lines 481–491; AUDIT-A §2.13). For PSD `A, B`,
`0 ⪯ M ⪯ A` and `Θ = tr(A² + B²)`:

* `tr(MA) ≤ tr A² ≤ Θ` (T.MAT (i));
* `tr(MB) ≤ (tr M² + tr B²)/2 ≤ Θ`, from `tr((M - B)²) ≥ 0` and `tr M² ≤ tr(MA) ≤ tr A²`;
* `ΘA - AMA = (Θ - λ²)A + λ(λA - A²) + A(λ - A)A + A(A - M)A ⪰ 0` with `λ = ‖A‖`,
  `λ² ≤ tr A²` (C*-identity `‖A²‖ = ‖A‖²` and `‖N‖ ≤ tr N`);
* `ΘB - BMB = (Θ - μν)B + μ(νB - B²) + B(μ - M)B ⪰ 0` with `μ = ‖M‖`, `ν = ‖B‖`,
  `μν ≤ (tr M² + tr B²)/2 ≤ Θ`.
-/

@[expose] public section

namespace BiluLinial.Tight.SecA.StarCalc

open Matrix BiluLinial

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open scoped Matrix.Norms.L2Operator in
/-- `‖X‖² ≤ tr X²` for symmetric `X` (C*-identity and `‖N‖ ≤ tr N` for `N = X² ⪰ 0`). -/
theorem opNorm_sq_le_trace_mul_self {X : Matrix ι ι ℝ} (hX : X.IsHermitian) :
    opNorm X ^ 2 ≤ (X * X).trace := by
  have h1 : opNorm (X * X) = opNorm X * opNorm X := by
    have h := CStarRing.norm_star_mul_self (x := X)
    rw [star_eq_conjTranspose, hX.eq] at h
    rw [opNorm_eq_l2_opNorm, opNorm_eq_l2_opNorm]
    exact h
  rw [sq, ← h1]
  exact opNorm_le_trace (posSemidef_mul_self hX)

/-- **A-PDOM**: prefactor domination for `0 ⪯ M ⪯ A`, `Θ = tr(A² + B²)`. -/
theorem pdom' {A B M : Matrix ι ι ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hM : M.PosSemidef) (hMA : (A - M).PosSemidef) :
    (M * A).trace ≤ (A * A + B * B).trace ∧ (M * B).trace ≤ (A * A + B * B).trace ∧
      ((A * A + B * B).trace • A - A * M * A).PosSemidef ∧
      ((A * A + B * B).trace • B - B * M * B).PosSemidef := by
  set Θ := (A * A + B * B).trace with hΘ
  have tA : 0 ≤ (A * A).trace := trace_mul_nonneg hA hA
  have tB : 0 ≤ (B * B).trace := trace_mul_nonneg hB hB
  have hΘs : Θ = (A * A).trace + (B * B).trace := by rw [hΘ, trace_add]
  -- `tr(MA) ≤ tr A²`, `tr M² ≤ tr(MA)`
  have hMA1 : (M * A).trace ≤ (A * A).trace := by
    have h := trace_mul_le_trace_mul hA hMA
    rw [trace_mul_comm A M] at h
    exact h
  have hMM : (M * M).trace ≤ (M * A).trace := trace_mul_le_trace_mul hM hMA
  -- `2 tr(MB) ≤ tr M² + tr B²`
  have hMB : 2 * (M * B).trace ≤ (M * M).trace + (B * B).trace := by
    have hsq := trace_mul_nonneg (posSemidef_mul_self (hM.isHermitian.sub hB.isHermitian))
      PosSemidef.one
    rw [mul_one, sub_mul, mul_sub, mul_sub, trace_sub, trace_sub, trace_sub,
      trace_mul_comm B M] at hsq
    linarith
  -- norms
  set lA := opNorm A with hlA
  set mu := opNorm M with hmu
  set nu := opNorm B with hnu
  have hlA0 : 0 ≤ lA := opNorm_nonneg A
  have hmu0 : 0 ≤ mu := opNorm_nonneg M
  have hnu0 : 0 ≤ nu := opNorm_nonneg B
  have hlA2 : lA ^ 2 ≤ (A * A).trace := opNorm_sq_le_trace_mul_self hA.isHermitian
  have hmu2 : mu ^ 2 ≤ (M * M).trace := opNorm_sq_le_trace_mul_self hM.isHermitian
  have hnu2 : nu ^ 2 ≤ (B * B).trace := opNorm_sq_le_trace_mul_self hB.isHermitian
  have hAl := posSemidef_opNorm_smul_sub hA.isHermitian
  have hMl := posSemidef_opNorm_smul_sub hM.isHermitian
  refine ⟨by linarith, by linarith, ?_, ?_⟩
  · -- `ΘA - AMA`
    have h1 : ((Θ - lA * lA) • A).PosSemidef := hA.smul (by nlinarith)
    have h2 : (lA • (lA • A - A * A)).PosSemidef :=
      (posSemidef_smul_sub_mul_self hA hlA0 hAl).smul hlA0
    have h3 : (A * (lA • (1 : Matrix ι ι ℝ) - A) * A).PosSemidef := by
      have h := hAl.conjTranspose_mul_mul_same A
      rwa [hA.isHermitian.eq] at h
    have h4 : (A * (A - M) * A).PosSemidef := by
      have h := hMA.conjTranspose_mul_mul_same A
      rwa [hA.isHermitian.eq] at h
    have e : Θ • A - A * M * A = (Θ - lA * lA) • A + lA • (lA • A - A * A) +
        A * (lA • (1 : Matrix ι ι ℝ) - A) * A + A * (A - M) * A := by
      simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one, smul_sub, sub_smul,
        smul_smul]
      abel
    rw [e]
    exact ((h1.add h2).add h3).add h4
  · -- `ΘB - BMB`
    have hmn : mu * nu ≤ Θ := by nlinarith [sq_nonneg (mu - nu)]
    have h1 : ((Θ - mu * nu) • B).PosSemidef := hB.smul (by linarith)
    have h2 : (mu • (nu • B - B * B)).PosSemidef :=
      (posSemidef_smul_sub_mul_self hB hnu0 (posSemidef_opNorm_smul_sub hB.isHermitian)).smul
        hmu0
    have h3 : (B * (mu • (1 : Matrix ι ι ℝ) - M) * B).PosSemidef := by
      have h := hMl.conjTranspose_mul_mul_same B
      rwa [hB.isHermitian.eq] at h
    have e : Θ • B - B * M * B = (Θ - mu * nu) • B + mu • (nu • B - B * B) +
        B * (mu • (1 : Matrix ι ι ℝ) - M) * B := by
      simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one, smul_sub, sub_smul,
        smul_smul]
      abel
    rw [e]
    exact (h1.add h2).add h3

end BiluLinial.Tight.SecA.StarCalc
