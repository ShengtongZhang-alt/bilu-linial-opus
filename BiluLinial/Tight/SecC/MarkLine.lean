/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecC.Deriv
public import BiluLinial.Tight.SecC.MarkPoly

/-!
# Line and plane polynomials of the row numerator (helpers for T.MARK)

Node T.MARK of `docs/tight/BP_SECC.md` (AUDIT-C §3, §9). Star level: `A, B ⪰ 0`, `a > 0`,
`α = 1 - q_A(x) > 0`, `β = 1 - q_B(x) > 0`, `x_j = starRow a A x j`, `z_j = starRow (-a) B x j`,
`e_kj = starCore a A x k j`, `f_kj = starCore a B x k j`, `r_i = starScale a A B x i`.

* `rowNumS`: `F` without clipping; `rowNum = rowNumS` near `x` (`rowNum_eventuallyEq`).
* `rowNumS_plane` (exact): along `x + t e_i + s e_k`,
  `F = a² α^p β^p Σ_j [(p-1) u_j² ρ₊^{p-2} ρ₋^p - p u_j w_j ρ₊^{p-1} ρ₋^{p-1}]` with
  `u_j = x_j - a e_ij t - a e_kj s`, `w_j = z_j + a f_ij t + a f_kj s`,
  `ρ₊ = 1 + 2a(x_i t + x_k s) - a²(e_ii t² + 2 e_ik ts + e_kk s²)`, and `ρ₋` likewise with
  `(z, f)` and the opposite linear sign.
* `iterate_pderiv_rowNum`: `∂_iⁿ F(x) = n! [tⁿ] linePoly`; `mixed_pderiv_rowNum`:
  `∂_i⁴ ∂_k⁴ F(x) = 576 [t⁴ s⁴] planePoly`.
* Majorants: `ρ_± ≪ (1 + c t)²` for `c ≥ a r_i`, `ρ₋ - ρ₊ ≪ (1 + a r_i t)² - 1`,
  `u_j ≪ (|x_j| + |e_ij|)(1 + c t)` for `c ≥ a`; in two variables
  `ρ_± ≪ Λ²`, `u_j ≪ μ_j Λ`, `Λ = 1 + a(1 + r_i) t + a(1 + r_k) s` (`|e_ik| ≤ r_i r_k`).
* Real cores of the three bounds: `grade_one_real`, `grade_two_real`.
-/

@[expose] public section

namespace BiluLinial.Tight

namespace SecC

open Matrix Filter Topology
open scoped Nat

variable {ι : Type*} [Fintype ι]

/-! ### Elementary facts -/

theorem abs_sub_le_add (u v : ℝ) : |u - v| ≤ |u| + |v| := by
  simpa [sub_eq_add_neg] using abs_add_le u (-v)

theorem abs_add5_le (u₁ u₂ u₃ u₄ u₅ : ℝ) :
    |u₁ + u₂ + u₃ + u₄ + u₅| ≤ |u₁| + |u₂| + |u₃| + |u₄| + |u₅| := by
  have h1 := abs_add_le (u₁ + u₂ + u₃ + u₄) u₅
  have h2 := abs_add_le (u₁ + u₂ + u₃) u₄
  have h3 := abs_add_le (u₁ + u₂) u₃
  have h4 := abs_add_le u₁ u₂
  linarith

omit [Fintype ι] in
theorem isSymm_of_posSemidef {A : Matrix ι ι ℝ} (hA : A.PosSemidef) : A.IsSymm := by
  have := hA.1
  rw [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
  exact this

omit [Fintype ι] in
private theorem psd_entry_sq_le {M : Matrix ι ι ℝ} (hM : M.PosSemidef) (j k : ι) :
    M j k ^ 2 ≤ M j j * M k k := by
  have h2 := (hM.submatrix ![j, k]).det_nonneg
  rw [Matrix.det_fin_two] at h2
  have hs : M k j = M j k := by
    have := congrFun (congrFun hM.1 j) k
    simpa [Matrix.conjTranspose_apply] using this
  simp [Matrix.submatrix_apply, hs] at h2
  nlinarith [h2]

theorem starPhi_eq {p : ℕ} {A B : Matrix ι ι ℝ} {x : ι → ℝ} (hα : 0 < starAlpha A x)
    (hβ : 0 < starAlpha B x) : starPhi p A B x = starAlpha A x ^ p * starAlpha B x ^ p := by
  unfold starPhi clipF
  rw [max_eq_left (show (0 : ℝ) ≤ 1 - qForm A x from hα.le),
    max_eq_left (show (0 : ℝ) ≤ 1 - qForm B x from hβ.le)]
  rfl

/-! ### Star facts: the unmarked scale dominates the line coefficients -/

section StarFacts

variable {a : ℝ} {A B : Matrix ι ι ℝ} {x : ι → ℝ}

theorem starCore_diag_nonneg (hA : A.PosSemidef) (hα : 0 < starAlpha A x) (i : ι) :
    0 ≤ starCore a A x i i :=
  div_nonneg hA.diag_nonneg (mul_nonneg (sq_nonneg a) hα.le)

theorem starCore_sq_le (hA : A.PosSemidef) (i k : ι) :
    starCore a A x i k ^ 2 ≤ starCore a A x i i * starCore a A x k k := by
  unfold starCore
  rw [div_pow, div_mul_div_comm, ← sq]
  have h0 : (0 : ℝ) ≤ (a ^ 2 * starAlpha A x) ^ 2 := sq_nonneg _
  have := psd_entry_sq_le hA i k
  gcongr

theorem starScale_nonneg (i : ι) : 0 ≤ starScale a A B x i := by
  unfold starScale
  positivity

theorem abs_starRow_add_le (i : ι) :
    |starRow a A x i| + |starRow (-a) B x i| ≤ starScale a A B x i := by
  unfold starScale
  have := Real.sqrt_nonneg (starCore a A x i i)
  have := Real.sqrt_nonneg (starCore a B x i i)
  linarith

theorem abs_starRow_le (i : ι) : |starRow a A x i| ≤ starScale a A B x i := by
  have := abs_starRow_add_le (a := a) (A := A) (B := B) (x := x) i
  have := abs_nonneg (starRow (-a) B x i)
  linarith

theorem abs_starRow_neg_le (i : ι) : |starRow (-a) B x i| ≤ starScale a A B x i := by
  have := abs_starRow_add_le (a := a) (A := A) (B := B) (x := x) i
  have := abs_nonneg (starRow a A x i)
  linarith

theorem sqrt_starCore_le (i : ι) : Real.sqrt (starCore a A x i i) ≤ starScale a A B x i := by
  unfold starScale
  have := abs_nonneg (starRow a A x i)
  have := abs_nonneg (starRow (-a) B x i)
  have := Real.sqrt_nonneg (starCore a B x i i)
  linarith

theorem sqrt_starCore_le' (i : ι) : Real.sqrt (starCore a B x i i) ≤ starScale a A B x i := by
  unfold starScale
  have := abs_nonneg (starRow a A x i)
  have := abs_nonneg (starRow (-a) B x i)
  have := Real.sqrt_nonneg (starCore a A x i i)
  linarith

theorem le_sq_of_sqrt_le {e r : ℝ} (he : 0 ≤ e) (h : Real.sqrt e ≤ r) : e ≤ r ^ 2 := by
  calc e = Real.sqrt e ^ 2 := (Real.sq_sqrt he).symm
    _ ≤ r ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg e) h 2

theorem abs_le_mul_of_sq_le {e₁ e₂ e r₁ r₂ : ℝ} (h₁ : 0 ≤ e₁) (h : e ^ 2 ≤ e₁ * e₂)
    (hr₁ : Real.sqrt e₁ ≤ r₁) (hr₂ : Real.sqrt e₂ ≤ r₂) : |e| ≤ r₁ * r₂ := by
  have h1 : |e| ≤ Real.sqrt e₁ * Real.sqrt e₂ := by
    rw [← Real.sqrt_mul h₁, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt h
  exact h1.trans (mul_le_mul hr₁ hr₂ (Real.sqrt_nonneg _) ((Real.sqrt_nonneg _).trans hr₁))

theorem starCore_le_sq (hA : A.PosSemidef) (hα : 0 < starAlpha A x) (i : ι) :
    starCore a A x i i ≤ starScale a A B x i ^ 2 :=
  le_sq_of_sqrt_le (starCore_diag_nonneg hA hα i) (sqrt_starCore_le i)

theorem starCore_le_sq' (hB : B.PosSemidef) (hβ : 0 < starAlpha B x) (i : ι) :
    starCore a B x i i ≤ starScale a A B x i ^ 2 :=
  le_sq_of_sqrt_le (starCore_diag_nonneg hB hβ i) (sqrt_starCore_le' i)

theorem abs_starCore_le (hA : A.PosSemidef) (hα : 0 < starAlpha A x) (i k : ι) :
    |starCore a A x i k| ≤ starScale a A B x i * starScale a A B x k :=
  abs_le_mul_of_sq_le (starCore_diag_nonneg hA hα i) (starCore_sq_le hA i k)
    (sqrt_starCore_le i) (sqrt_starCore_le k)

theorem abs_starCore_le' (hB : B.PosSemidef) (hβ : 0 < starAlpha B x) (i k : ι) :
    |starCore a B x i k| ≤ starScale a A B x i * starScale a A B x k :=
  abs_le_mul_of_sq_le (starCore_diag_nonneg hB hβ i) (starCore_sq_le hB i k)
    (sqrt_starCore_le' i) (sqrt_starCore_le' k)

end StarFacts

/-! ### The unclipped numerator and the plane formula -/

/-- `F` without clipping. -/
noncomputable def rowNumS (p : ℕ) (A B : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ :=
  ((p : ℝ) - 1) * qForm (A * A) x * starAlpha A x ^ (p - 2) * starAlpha B x ^ p +
    p * qForm (A * B) x * starAlpha A x ^ (p - 1) * starAlpha B x ^ (p - 1)

theorem contDiff_qForm' (M : Matrix ι ι ℝ) {n : WithTop ℕ∞} : ContDiff ℝ n (qForm M) := by
  unfold qForm
  simp only [dotProduct, mulVec]
  fun_prop

theorem contDiff_rowNumS (p : ℕ) (A B : Matrix ι ι ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (rowNumS p A B) := by
  have hA := contDiff_qForm' A (n := n)
  have hB := contDiff_qForm' B (n := n)
  have hAA := contDiff_qForm' (A * A) (n := n)
  have hAB := contDiff_qForm' (A * B) (n := n)
  unfold rowNumS starAlpha
  fun_prop

theorem rowNum_eventuallyEq {p : ℕ} {A B : Matrix ι ι ℝ} {x : ι → ℝ} (hα : 0 < starAlpha A x)
    (hβ : 0 < starAlpha B x) : rowNum p A B =ᶠ[𝓝 x] rowNumS p A B := by
  have hcA : Continuous (starAlpha A) := by
    unfold starAlpha
    exact continuous_const.sub (contDiff_qForm' A (n := 0)).continuous
  have hcB : Continuous (starAlpha B) := by
    unfold starAlpha
    exact continuous_const.sub (contDiff_qForm' B (n := 0)).continuous
  filter_upwards [hcA.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hα),
    hcB.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hβ)] with y hy1 hy2
  have e1 : clipF A y = starAlpha A y :=
    max_eq_left (show (0 : ℝ) ≤ 1 - qForm A y from le_of_lt hy1)
  have e2 : clipF B y = starAlpha B y :=
    max_eq_left (show (0 : ℝ) ≤ 1 - qForm B y from le_of_lt hy2)
  unfold rowNum rowNumS
  rw [e1, e2]

/-- `u_j(t, s) = x_j - a e_ij t - a e_kj s`. -/
noncomputable def planeU (a : ℝ) (A : Matrix ι ι ℝ) (x : ι → ℝ) (i k j : ι) (t s : ℝ) : ℝ :=
  starRow a A x j - a * starCore a A x i j * t - a * starCore a A x k j * s

/-- `w_j(t, s) = z_j + a f_ij t + a f_kj s`. -/
noncomputable def planeW (a : ℝ) (B : Matrix ι ι ℝ) (x : ι → ℝ) (i k j : ι) (t s : ℝ) : ℝ :=
  starRow (-a) B x j + a * starCore a B x i j * t + a * starCore a B x k j * s

/-- `ρ₊(t, s) = α(x + t e_i + s e_k)/α(x)`. -/
noncomputable def planeRp (a : ℝ) (A : Matrix ι ι ℝ) (x : ι → ℝ) (i k : ι) (t s : ℝ) : ℝ :=
  1 + 2 * a * starRow a A x i * t + 2 * a * starRow a A x k * s -
    a ^ 2 * (starCore a A x i i * t ^ 2 + 2 * starCore a A x i k * t * s +
      starCore a A x k k * s ^ 2)

/-- `ρ₋(t, s) = β(x + t e_i + s e_k)/β(x)`. -/
noncomputable def planeRm (a : ℝ) (B : Matrix ι ι ℝ) (x : ι → ℝ) (i k : ι) (t s : ℝ) : ℝ :=
  1 - 2 * a * starRow (-a) B x i * t - 2 * a * starRow (-a) B x k * s -
    a ^ 2 * (starCore a B x i i * t ^ 2 + 2 * starCore a B x i k * t * s +
      starCore a B x k k * s ^ 2)

theorem mulVec_plane [DecidableEq ι] (A : Matrix ι ι ℝ) (x : ι → ℝ) (i k j : ι) (t s : ℝ) :
    (A *ᵥ (x + t • Pi.single i 1 + s • Pi.single k 1)) j = (A *ᵥ x) j + t * A j i + s * A j k := by
  rw [mulVec_line, mulVec_line]

theorem starAlpha_plane [DecidableEq ι] {A : Matrix ι ι ℝ} (hA : A.IsSymm) (x : ι → ℝ)
    (i k : ι) (t s : ℝ) :
    starAlpha A (x + t • Pi.single i 1 + s • Pi.single k 1) =
      starAlpha A x - 2 * t * (A *ᵥ x) i - 2 * s * (A *ᵥ x) k - t ^ 2 * A i i -
        2 * t * s * A i k - s ^ 2 * A k k := by
  have hsym : ∀ k l, A k l = A l k := fun k l => by simpa using congrFun (congrFun hA l) k
  rw [starAlpha_line hA, starAlpha_line hA, mulVec_line, hsym k i]
  ring

/-- **The plane formula** (exact). -/
theorem rowNumS_plane [DecidableEq ι] {p : ℕ} (hp : 2 ≤ p) {a : ℝ} (ha : a ≠ 0) {A B : Matrix ι ι ℝ}
    (hA : A.IsSymm) (hB : B.IsSymm) {x : ι → ℝ} (hα : starAlpha A x ≠ 0)
    (hβ : starAlpha B x ≠ 0) (i k : ι) (t s : ℝ) :
    rowNumS p A B (x + t • Pi.single i 1 + s • Pi.single k 1) =
      a ^ 2 * starAlpha A x ^ p * starAlpha B x ^ p *
        ∑ j, (((p : ℝ) - 1) * planeU a A x i k j t s ^ 2 * planeRp a A x i k t s ^ (p - 2) *
              planeRm a B x i k t s ^ p -
            p * planeU a A x i k j t s * planeW a B x i k j t s *
              planeRp a A x i k t s ^ (p - 1) * planeRm a B x i k t s ^ (p - 1)) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 2 := ⟨p - 2, by omega⟩
  have hsA : ∀ k l, A k l = A l k := fun k l => by simpa using congrFun (congrFun hA l) k
  have hsB : ∀ k l, B k l = B l k := fun k l => by simpa using congrFun (congrFun hB l) k
  set y := x + t • Pi.single i 1 + s • Pi.single k 1 with hy
  have hAy : ∀ j, (A *ᵥ y) j = -(a * starAlpha A x) * planeU a A x i k j t s := by
    intro j
    rw [hy, mulVec_plane]
    unfold planeU starRow starCore
    rw [hsA j i, hsA j k]
    field_simp
    ring
  have hBy : ∀ j, (B *ᵥ y) j = a * starAlpha B x * planeW a B x i k j t s := by
    intro j
    rw [hy, mulVec_plane]
    unfold planeW starRow starCore
    rw [hsB j i, hsB j k]
    field_simp
  have hαy : starAlpha A y = starAlpha A x * planeRp a A x i k t s := by
    rw [hy, starAlpha_plane hA]
    unfold planeRp starRow starCore
    field_simp
    ring
  have hβy : starAlpha B y = starAlpha B x * planeRm a B x i k t s := by
    rw [hy, starAlpha_plane hB]
    unfold planeRm starRow starCore
    field_simp
    ring
  have hAt : y ᵥ* A = A *ᵥ y := by
    rw [← mulVec_transpose]
    congr 1
  have hqAA : qForm (A * A) y = ∑ j, (A *ᵥ y) j * (A *ᵥ y) j := by
    unfold qForm
    rw [← mulVec_mulVec, dotProduct_mulVec, hAt, dotProduct]
  have hqAB : qForm (A * B) y = ∑ j, (A *ᵥ y) j * (B *ᵥ y) j := by
    unfold qForm
    rw [← mulVec_mulVec, dotProduct_mulVec, hAt, dotProduct]
  unfold rowNumS
  rw [hqAA, hqAB, hαy, hβy, show q + 2 - 2 = q by omega, show q + 2 - 1 = q + 1 by omega]
  simp only [hAy, hBy, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  push_cast
  ring

/-! ### The line polynomial (`t = X`) -/

section Poly

open Polynomial

/-- `u_j(t) = x_j - a e_ij t`. -/
noncomputable def lineU1 (a : ℝ) (A : Matrix ι ι ℝ) (x : ι → ℝ) (i j : ι) : ℝ[X] :=
  C (starRow a A x j) + C (-(a * starCore a A x i j)) * X

/-- `w_j(t) = z_j + a f_ij t`. -/
noncomputable def lineW1 (a : ℝ) (B : Matrix ι ι ℝ) (x : ι → ℝ) (i j : ι) : ℝ[X] :=
  C (starRow (-a) B x j) + C (a * starCore a B x i j) * X

/-- `ρ₊(t) = 1 + 2a x_i t - a² e_ii t²`. -/
noncomputable def lineRp1 (a : ℝ) (A : Matrix ι ι ℝ) (x : ι → ℝ) (i : ι) : ℝ[X] :=
  C 1 + C (2 * a * starRow a A x i) * X + C (-(a ^ 2 * starCore a A x i i)) * X ^ 2

/-- `ρ₋(t) = 1 - 2a z_i t - a² f_ii t²`. -/
noncomputable def lineRm1 (a : ℝ) (B : Matrix ι ι ℝ) (x : ι → ℝ) (i : ι) : ℝ[X] :=
  C 1 + C (-(2 * a * starRow (-a) B x i)) * X + C (-(a ^ 2 * starCore a B x i i)) * X ^ 2

/-- `ρ₊^m ρ₋^{m'}`. -/
noncomputable def linePi (a : ℝ) (A B : Matrix ι ι ℝ) (x : ι → ℝ) (i : ι) (m m' : ℕ) : ℝ[X] :=
  lineRp1 a A x i ^ m * lineRm1 a B x i ^ m'

/-- The line polynomial `t ↦ F(x + t e_i)`. -/
noncomputable def linePoly (p : ℕ) (a : ℝ) (A B : Matrix ι ι ℝ) (x : ι → ℝ) (i : ι) : ℝ[X] :=
  C (a ^ 2 * starAlpha A x ^ p * starAlpha B x ^ p) *
    ∑ j, (C ((p : ℝ) - 1) * lineU1 a A x i j ^ 2 * lineRp1 a A x i ^ (p - 2) *
        lineRm1 a B x i ^ p -
      C (p : ℝ) * lineU1 a A x i j * lineW1 a B x i j * lineRp1 a A x i ^ (p - 1) *
        lineRm1 a B x i ^ (p - 1))

theorem eval_linePoly [DecidableEq ι] {p : ℕ} (hp : 2 ≤ p) {a : ℝ} (ha : a ≠ 0) {A B : Matrix ι ι ℝ}
    (hA : A.IsSymm) (hB : B.IsSymm) {x : ι → ℝ} (hα : starAlpha A x ≠ 0)
    (hβ : starAlpha B x ≠ 0) (i : ι) (t : ℝ) :
    (linePoly p a A B x i).eval t = rowNumS p A B (x + t • Pi.single i 1) := by
  have h := rowNumS_plane hp ha hA hB hα hβ i i t 0
  rw [zero_smul, add_zero] at h
  rw [h]
  have hU : ∀ j, (lineU1 a A x i j).eval t = planeU a A x i i j t 0 := fun j => by
    simp only [lineU1, planeU, eval_add, eval_mul, eval_C, eval_X]
    ring
  have hW : ∀ j, (lineW1 a B x i j).eval t = planeW a B x i i j t 0 := fun j => by
    simp only [lineW1, planeW, eval_add, eval_mul, eval_C, eval_X]
    ring
  have hRp : (lineRp1 a A x i).eval t = planeRp a A x i i t 0 := by
    simp only [lineRp1, planeRp, eval_add, eval_mul, eval_C, eval_X, eval_pow]
    ring
  have hRm : (lineRm1 a B x i).eval t = planeRm a B x i i t 0 := by
    simp only [lineRm1, planeRm, eval_add, eval_mul, eval_C, eval_X, eval_pow]
    ring
  simp only [linePoly, eval_mul, eval_C, eval_finsetSum, eval_sub, eval_pow, hU, hW, hRp, hRm]

/-- `∂_iⁿ F(x) = n! [tⁿ] linePoly`. -/
theorem iterate_pderiv_rowNum [DecidableEq ι] {p : ℕ} (hp : 2 ≤ p) {a : ℝ} (ha : a ≠ 0)
    {A B : Matrix ι ι ℝ} (hA : A.IsSymm) (hB : B.IsSymm) {x : ι → ℝ} (hα : 0 < starAlpha A x)
    (hβ : 0 < starAlpha B x) (i : ι) (n : ℕ) :
    (pderiv i)^[n] (rowNum p A B) x = n ! * (linePoly p a A B x i).coeff n := by
  rw [(pderiv_iterate_congr_nhds n (rowNum_eventuallyEq hα hβ) i).eq_of_nhds]
  have h := congrFun (iteratedDeriv_line n (contDiff_rowNumS p A B) x i) 0
  simp only [zero_smul, add_zero] at h
  rw [← h, ← iteratedDeriv_eval_zero]
  congr 1
  funext t
  exact (eval_linePoly hp ha hA hB hα.ne' hβ.ne' i t).symm

theorem coeff_lin_mul_lin_mul (u b v c : ℝ) (P : ℝ[X]) (n : ℕ) :
    ((C u + C b * X) * (C v + C c * X) * P).coeff (n + 2) =
      u * v * P.coeff (n + 2) + (u * c + b * v) * P.coeff (n + 1) + b * c * P.coeff n := by
  have e : (C u + C b * X) * (C v + C c * X) * P =
      C (u * v) * P + C (u * c + b * v) * (X * P) + C (b * c) * (X ^ 2 * P) := by
    simp only [map_mul, map_add]
    ring
  have h1 : (X * P).coeff (n + 2) = P.coeff (n + 1) := coeff_X_mul P (n + 1)
  have h2 : (X ^ 2 * P).coeff (n + 2) = P.coeff n := coeff_X_pow_mul P 2 n
  rw [e, coeff_add, coeff_add, coeff_C_mul, coeff_C_mul, coeff_C_mul, h1, h2]

theorem coeff_linePoly (p : ℕ) (a : ℝ) (A B : Matrix ι ι ℝ) (x : ι → ℝ) (i : ι) (n : ℕ) :
    (linePoly p a A B x i).coeff n = a ^ 2 * starAlpha A x ^ p * starAlpha B x ^ p *
      ∑ j, (((p : ℝ) - 1) *
          (lineU1 a A x i j * lineU1 a A x i j * linePi a A B x i (p - 2) p).coeff n -
        p * (lineU1 a A x i j * lineW1 a B x i j * linePi a A B x i (p - 1) (p - 1)).coeff n) := by
  unfold linePoly
  rw [coeff_C_mul, finsetSum_coeff]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show C ((p : ℝ) - 1) * lineU1 a A x i j ^ 2 * lineRp1 a A x i ^ (p - 2) *
        lineRm1 a B x i ^ p -
      C (p : ℝ) * lineU1 a A x i j * lineW1 a B x i j * lineRp1 a A x i ^ (p - 1) *
        lineRm1 a B x i ^ (p - 1) =
      C ((p : ℝ) - 1) * (lineU1 a A x i j * lineU1 a A x i j * linePi a A B x i (p - 2) p) -
        C (p : ℝ) * (lineU1 a A x i j * lineW1 a B x i j * linePi a A B x i (p - 1) (p - 1))
      by unfold linePi; ring]
  rw [coeff_sub, coeff_C_mul, coeff_C_mul]

/-! ### The plane polynomial (`t = C X`, `s = X`) -/

noncomputable def planeU2 (a : ℝ) (A : Matrix ι ι ℝ) (x : ι → ℝ) (i k j : ι) : ℝ[X][X] :=
  mono2 (starRow a A x j) 0 0 + mono2 (-(a * starCore a A x i j)) 1 0 +
    mono2 (-(a * starCore a A x k j)) 0 1

noncomputable def planeW2 (a : ℝ) (B : Matrix ι ι ℝ) (x : ι → ℝ) (i k j : ι) : ℝ[X][X] :=
  mono2 (starRow (-a) B x j) 0 0 + mono2 (a * starCore a B x i j) 1 0 +
    mono2 (a * starCore a B x k j) 0 1

noncomputable def planeRp2 (a : ℝ) (A : Matrix ι ι ℝ) (x : ι → ℝ) (i k : ι) : ℝ[X][X] :=
  mono2 1 0 0 + mono2 (2 * a * starRow a A x i) 1 0 + mono2 (2 * a * starRow a A x k) 0 1 +
    mono2 (-(a ^ 2 * starCore a A x i i)) 2 0 + mono2 (-(2 * a ^ 2 * starCore a A x i k)) 1 1 +
    mono2 (-(a ^ 2 * starCore a A x k k)) 0 2

noncomputable def planeRm2 (a : ℝ) (B : Matrix ι ι ℝ) (x : ι → ℝ) (i k : ι) : ℝ[X][X] :=
  mono2 1 0 0 + mono2 (-(2 * a * starRow (-a) B x i)) 1 0 +
    mono2 (-(2 * a * starRow (-a) B x k)) 0 1 + mono2 (-(a ^ 2 * starCore a B x i i)) 2 0 +
    mono2 (-(2 * a ^ 2 * starCore a B x i k)) 1 1 + mono2 (-(a ^ 2 * starCore a B x k k)) 0 2

noncomputable def planePi (a : ℝ) (A B : Matrix ι ι ℝ) (x : ι → ℝ) (i k : ι) (m m' : ℕ) :
    ℝ[X][X] :=
  planeRp2 a A x i k ^ m * planeRm2 a B x i k ^ m'

/-- The plane polynomial `(t, s) ↦ F(x + t e_i + s e_k)`. -/
noncomputable def planePoly (p : ℕ) (a : ℝ) (A B : Matrix ι ι ℝ) (x : ι → ℝ) (i k : ι) :
    ℝ[X][X] :=
  C (C (a ^ 2 * starAlpha A x ^ p * starAlpha B x ^ p)) *
    ∑ j, (C (C ((p : ℝ) - 1)) * planeU2 a A x i k j ^ 2 * planeRp2 a A x i k ^ (p - 2) *
        planeRm2 a B x i k ^ p -
      C (C (p : ℝ)) * planeU2 a A x i k j * planeW2 a B x i k j * planeRp2 a A x i k ^ (p - 1) *
        planeRm2 a B x i k ^ (p - 1))

theorem ev2_planePoly [DecidableEq ι] {p : ℕ} (hp : 2 ≤ p) {a : ℝ} (ha : a ≠ 0) {A B : Matrix ι ι ℝ}
    (hA : A.IsSymm) (hB : B.IsSymm) {x : ι → ℝ} (hα : starAlpha A x ≠ 0)
    (hβ : starAlpha B x ≠ 0) (i k : ι) (t s : ℝ) :
    ev2 t s (planePoly p a A B x i k) =
      rowNumS p A B (x + t • Pi.single i 1 + s • Pi.single k 1) := by
  rw [rowNumS_plane hp ha hA hB hα hβ i k t s]
  have hU : ∀ j, ev2 t s (planeU2 a A x i k j) = planeU a A x i k j t s := fun j => by
    simp only [planeU2, planeU, map_add, ev2_mono]
    ring
  have hW : ∀ j, ev2 t s (planeW2 a B x i k j) = planeW a B x i k j t s := fun j => by
    simp only [planeW2, planeW, map_add, ev2_mono]
    ring
  have hRp : ev2 t s (planeRp2 a A x i k) = planeRp a A x i k t s := by
    simp only [planeRp2, planeRp, map_add, ev2_mono]
    ring
  have hRm : ev2 t s (planeRm2 a B x i k) = planeRm a B x i k t s := by
    simp only [planeRm2, planeRm, map_add, ev2_mono]
    ring
  simp only [planePoly, map_mul, map_sub, map_sum, map_pow, ev2_CC, hU, hW, hRp, hRm]

/-- `∂_i⁴ ∂_k⁴ F(x) = 576 [t⁴ s⁴] planePoly` (any `i, k`). -/
theorem mixed_pderiv_rowNum [DecidableEq ι] {p : ℕ} (hp : 2 ≤ p) {a : ℝ} (ha : a ≠ 0)
    {A B : Matrix ι ι ℝ} (hA : A.IsSymm) (hB : B.IsSymm) {x : ι → ℝ} (hα : 0 < starAlpha A x)
    (hβ : 0 < starAlpha B x) (i k : ι) :
    (pderiv i)^[4] ((pderiv k)^[4] (rowNum p A B)) x =
      576 * coeff2 (planePoly p a A B x i k) 4 4 := by
  rw [(pderiv_iterate_congr_nhds 4
    (pderiv_iterate_congr_nhds 4 (rowNum_eventuallyEq hα hβ) k) i).eq_of_nhds]
  have hg : ContDiff ℝ ((4 : ℕ) : WithTop ℕ∞) ((pderiv k)^[4] (rowNumS p A B)) :=
    contDiff_pderiv_iterate (N := 4) 4 (contDiff_rowNumS p A B) k
  have h := congrFun (iteratedDeriv_line 4 hg x i) 0
  simp only [zero_smul, add_zero] at h
  rw [← h]
  have h2 : (fun t : ℝ => (pderiv k)^[4] (rowNumS p A B) (x + t • Pi.single i (1 : ℝ))) =
      fun t => (C (((4 ! : ℕ) : ℝ)) * (planePoly p a A B x i k).coeff 4).eval t := by
    funext t
    have h3 := congrFun (iteratedDeriv_line 4
      (contDiff_rowNumS p A B (n := ((4 : ℕ) : WithTop ℕ∞))) (x + t • Pi.single i (1 : ℝ)) k) 0
    simp only [zero_smul, add_zero] at h3
    rw [← h3, eval_mul, eval_C, ← iteratedDeriv_ev2]
    congr 1
    funext s
    exact (ev2_planePoly hp ha hA hB hα.ne' hβ.ne' i k t s).symm
  rw [h2, iteratedDeriv_eval_zero, coeff_C_mul, coeff2,
    show ((4 ! : ℕ) : ℝ) = 24 by norm_num [Nat.factorial]]
  ring

theorem coeff2_planePoly (p : ℕ) (a : ℝ) (A B : Matrix ι ι ℝ) (x : ι → ℝ) (i k : ι)
    (m n : ℕ) :
    coeff2 (planePoly p a A B x i k) m n = a ^ 2 * starAlpha A x ^ p * starAlpha B x ^ p *
      ∑ j, (((p : ℝ) - 1) *
          coeff2 (planeU2 a A x i k j * planeU2 a A x i k j * planePi a A B x i k (p - 2) p) m n -
        p * coeff2 (planeU2 a A x i k j * planeW2 a B x i k j *
          planePi a A B x i k (p - 1) (p - 1)) m n) := by
  unfold planePoly
  rw [coeff2_CC_mul, coeff2_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show C (C ((p : ℝ) - 1)) * planeU2 a A x i k j ^ 2 * planeRp2 a A x i k ^ (p - 2) *
        planeRm2 a B x i k ^ p -
      C (C (p : ℝ)) * planeU2 a A x i k j * planeW2 a B x i k j * planeRp2 a A x i k ^ (p - 1) *
        planeRm2 a B x i k ^ (p - 1) =
      C (C ((p : ℝ) - 1)) *
          (planeU2 a A x i k j * planeU2 a A x i k j * planePi a A B x i k (p - 2) p) -
        C (C (p : ℝ)) *
          (planeU2 a A x i k j * planeW2 a B x i k j * planePi a A B x i k (p - 1) (p - 1))
      by unfold planePi; ring]
  rw [coeff2_sub, coeff2_CC_mul, coeff2_CC_mul]

/-! ### One-variable majorants -/

theorem maj1_quad {u₀ u₁ u₂ v₀ v₁ v₂ : ℝ} (h₀ : |u₀| ≤ v₀) (h₁ : |u₁| ≤ v₁) (h₂ : |u₂| ≤ v₂) :
    Maj1 (C u₀ + C u₁ * X + C u₂ * X ^ 2) (C v₀ + C v₁ * X + C v₂ * X ^ 2) :=
  isMaj1.add (isMaj1.add (maj1_C h₀) (isMaj1.mul (maj1_C h₁) maj1_X))
    (isMaj1.mul (maj1_C h₂) (isMaj1.pow maj1_X 2))

theorem lin_sq (c : ℝ) :
    (C 1 + C c * X : ℝ[X]) ^ 2 = C 1 + C (2 * c) * X + C (c ^ 2) * X ^ 2 := by
  simp only [map_mul, map_pow, map_one, map_ofNat]
  ring

section Maj

variable {a : ℝ} {A B : Matrix ι ι ℝ} {x : ι → ℝ}

theorem maj_lineRp1 (ha : 0 ≤ a) (hA : A.PosSemidef) (hα : 0 < starAlpha A x) (i : ι)
    {c : ℝ} (hc : a * starScale a A B x i ≤ c) :
    Maj1 (lineRp1 a A x i) ((C 1 + C c * X) ^ 2) := by
  have hr0 := starScale_nonneg (a := a) (A := A) (B := B) (x := x) i
  have hx := abs_starRow_le (a := a) (A := A) (B := B) (x := x) i
  have he0 := starCore_diag_nonneg (a := a) hA hα i
  have he := starCore_le_sq (a := a) (B := B) hA hα i
  have hc0 : 0 ≤ a * starScale a A B x i := mul_nonneg ha hr0
  rw [lin_sq]
  refine maj1_quad (by simp) ?_ ?_
  · rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg ha]
    nlinarith [mul_le_mul_of_nonneg_left hx ha]
  · rw [abs_neg, abs_of_nonneg (mul_nonneg (sq_nonneg a) he0)]
    calc a ^ 2 * starCore a A x i i ≤ a ^ 2 * starScale a A B x i ^ 2 :=
          mul_le_mul_of_nonneg_left he (sq_nonneg a)
      _ = (a * starScale a A B x i) ^ 2 := by ring
      _ ≤ c ^ 2 := pow_le_pow_left₀ hc0 hc 2

theorem maj_lineRm1 (ha : 0 ≤ a) (hB : B.PosSemidef) (hβ : 0 < starAlpha B x) (i : ι)
    {c : ℝ} (hc : a * starScale a A B x i ≤ c) :
    Maj1 (lineRm1 a B x i) ((C 1 + C c * X) ^ 2) := by
  have hr0 := starScale_nonneg (a := a) (A := A) (B := B) (x := x) i
  have hz := abs_starRow_neg_le (a := a) (A := A) (B := B) (x := x) i
  have hf0 := starCore_diag_nonneg (a := a) hB hβ i
  have hf := starCore_le_sq' (a := a) (A := A) hB hβ i
  have hc0 : 0 ≤ a * starScale a A B x i := mul_nonneg ha hr0
  rw [lin_sq]
  refine maj1_quad (by simp) ?_ ?_
  · rw [abs_neg, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg ha]
    nlinarith [mul_le_mul_of_nonneg_left hz ha]
  · rw [abs_neg, abs_of_nonneg (mul_nonneg (sq_nonneg a) hf0)]
    calc a ^ 2 * starCore a B x i i ≤ a ^ 2 * starScale a A B x i ^ 2 :=
          mul_le_mul_of_nonneg_left hf (sq_nonneg a)
      _ = (a * starScale a A B x i) ^ 2 := by ring
      _ ≤ c ^ 2 := pow_le_pow_left₀ hc0 hc 2

theorem maj_lineDiff (ha : 0 ≤ a) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hα : 0 < starAlpha A x) (hβ : 0 < starAlpha B x) (i : ι) :
    Maj1 (lineRm1 a B x i - lineRp1 a A x i)
      ((C 1 + C (a * starScale a A B x i) * X) ^ 2 - 1) := by
  have hr0 := starScale_nonneg (a := a) (A := A) (B := B) (x := x) i
  have hxz := abs_starRow_add_le (a := a) (A := A) (B := B) (x := x) i
  have he0 := starCore_diag_nonneg (a := a) hA hα i
  have he := starCore_le_sq (a := a) (B := B) hA hα i
  have hf0 := starCore_diag_nonneg (a := a) hB hβ i
  have hf := starCore_le_sq' (a := a) (A := A) hB hβ i
  have e1 : lineRm1 a B x i - lineRp1 a A x i =
      C 0 + C (-(2 * a * starRow (-a) B x i) - 2 * a * starRow a A x i) * X +
        C (-(a ^ 2 * starCore a B x i i) - -(a ^ 2 * starCore a A x i i)) * X ^ 2 := by
    simp only [lineRm1, lineRp1, map_sub, map_zero]
    ring
  have e2 : (C 1 + C (a * starScale a A B x i) * X : ℝ[X]) ^ 2 - 1 =
      C 0 + C (2 * (a * starScale a A B x i)) * X +
        C ((a * starScale a A B x i) ^ 2) * X ^ 2 := by
    rw [lin_sq]
    simp only [map_one, map_zero]
    ring
  rw [e1, e2]
  refine maj1_quad (by simp) ?_ ?_
  · rw [show -(2 * a * starRow (-a) B x i) - 2 * a * starRow a A x i =
        -(2 * a) * (starRow a A x i + starRow (-a) B x i) by ring, abs_mul, abs_neg,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * a)]
    have h1 := abs_add_le (starRow a A x i) (starRow (-a) B x i)
    have h2 : 2 * a * |starRow a A x i + starRow (-a) B x i| ≤ 2 * a * starScale a A B x i :=
      mul_le_mul_of_nonneg_left (h1.trans hxz) (by positivity)
    linarith
  · rw [show -(a ^ 2 * starCore a B x i i) - -(a ^ 2 * starCore a A x i i) =
        a ^ 2 * (starCore a A x i i - starCore a B x i i) by ring, abs_mul,
      abs_of_nonneg (sq_nonneg a)]
    have h1 : |starCore a A x i i - starCore a B x i i| ≤ starScale a A B x i ^ 2 :=
      abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
    calc a ^ 2 * |starCore a A x i i - starCore a B x i i| ≤ a ^ 2 * starScale a A B x i ^ 2 :=
          mul_le_mul_of_nonneg_left h1 (sq_nonneg a)
      _ = (a * starScale a A B x i) ^ 2 := by ring

theorem maj_linePi (ha : 0 ≤ a) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hα : 0 < starAlpha A x) (hβ : 0 < starAlpha B x) (i : ι) {c : ℝ}
    (hc : a * starScale a A B x i ≤ c) (m m' : ℕ) :
    Maj1 (linePi a A B x i m m') ((C 1 + C c * X) ^ (2 * (m + m'))) := by
  have h := isMaj1.mul (isMaj1.pow (maj_lineRp1 ha hA hα i hc) m)
    (isMaj1.pow (maj_lineRm1 ha hB hβ i hc) m')
  rw [← pow_mul, ← pow_mul, ← pow_add, ← mul_add] at h
  exact h

theorem maj_linePi_sub (ha : 0 ≤ a) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hα : 0 < starAlpha A x) (hβ : 0 < starAlpha B x) (i : ι) {p : ℕ} (hp : 2 ≤ p) :
    Maj1 (linePi a A B x i (p - 2) p - linePi a A B x i (p - 1) (p - 1))
      ((C 1 + C (a * starScale a A B x i) * X) ^ (4 * p - 6 + 2) -
        (C 1 + C (a * starScale a A B x i) * X) ^ (4 * p - 6)) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 2 := ⟨p - 2, by omega⟩
  have hc := le_refl (a * starScale a A B x i)
  have h := isMaj1.mul (isMaj1.mul (isMaj1.pow (maj_lineRp1 ha hA hα i hc) q)
    (isMaj1.pow (maj_lineRm1 ha hB hβ i hc) (q + 1))) (maj_lineDiff ha hA hB hα hβ i)
  rw [show q + 2 - 2 = q by omega, show q + 2 - 1 = q + 1 by omega,
    show 4 * (q + 2) - 6 = 4 * q + 2 by omega]
  have e1 : linePi a A B x i q (q + 2) - linePi a A B x i (q + 1) (q + 1) =
      lineRp1 a A x i ^ q * lineRm1 a B x i ^ (q + 1) * (lineRm1 a B x i - lineRp1 a A x i) := by
    unfold linePi
    ring
  set L := (C 1 + C (a * starScale a A B x i) * X : ℝ[X])
  have e2 : L ^ (4 * q + 2 + 2) - L ^ (4 * q + 2) =
      (L ^ 2) ^ q * (L ^ 2) ^ (q + 1) * (L ^ 2 - 1) := by
    rw [← pow_mul, ← pow_mul, ← pow_add, mul_sub, mul_one, ← pow_add]
    ring_nf
  rw [e1, e2]
  exact h

theorem maj_lineU1 (ha : 0 ≤ a) (A : Matrix ι ι ℝ) (x : ι → ℝ) (i j : ι) {c : ℝ}
    (hc : a ≤ c) :
    Maj1 (lineU1 a A x i j) (C (|starRow a A x j| + |starCore a A x i j|) * (C 1 + C c * X)) := by
  unfold lineU1
  rw [show C (|starRow a A x j| + |starCore a A x i j|) * (C 1 + C c * X) =
      C (|starRow a A x j| + |starCore a A x i j|) +
        C ((|starRow a A x j| + |starCore a A x i j|) * c) * X by
    simp only [map_mul, map_one]; ring]
  refine isMaj1.add (maj1_C ?_) (isMaj1.mul (maj1_C ?_) maj1_X)
  · exact le_add_of_nonneg_right (abs_nonneg _)
  · rw [abs_neg, abs_mul, abs_of_nonneg ha]
    calc a * |starCore a A x i j| ≤ c * (|starRow a A x j| + |starCore a A x i j|) :=
          mul_le_mul hc (le_add_of_nonneg_left (abs_nonneg _)) (abs_nonneg _) (ha.trans hc)
      _ = _ := mul_comm _ _

theorem maj_lineW1 (ha : 0 ≤ a) (B : Matrix ι ι ℝ) (x : ι → ℝ) (i j : ι) {c : ℝ}
    (hc : a ≤ c) :
    Maj1 (lineW1 a B x i j)
      (C (|starRow (-a) B x j| + |starCore a B x i j|) * (C 1 + C c * X)) := by
  unfold lineW1
  rw [show C (|starRow (-a) B x j| + |starCore a B x i j|) * (C 1 + C c * X) =
      C (|starRow (-a) B x j| + |starCore a B x i j|) +
        C ((|starRow (-a) B x j| + |starCore a B x i j|) * c) * X by
    simp only [map_mul, map_one]; ring]
  refine isMaj1.add (maj1_C ?_) (isMaj1.mul (maj1_C ?_) maj1_X)
  · exact le_add_of_nonneg_right (abs_nonneg _)
  · rw [abs_mul, abs_of_nonneg ha]
    calc a * |starCore a B x i j| ≤ c * (|starRow (-a) B x j| + |starCore a B x i j|) :=
          mul_le_mul hc (le_add_of_nonneg_left (abs_nonneg _)) (abs_nonneg _) (ha.trans hc)
      _ = _ := mul_comm _ _

end Maj

/-! ### One-variable coefficient bounds -/

theorem abs_coeff_le_choose {P : ℝ[X]} {c : ℝ} {M : ℕ} (h : Maj1 P ((C 1 + C c * X) ^ M))
    (n : ℕ) : |P.coeff n| ≤ M.choose n * c ^ n := by
  have h1 := abs_coeff_le_of_maj1 h n
  rwa [coeff_C_add_C_mul_X_pow, one_pow, mul_one] at h1

theorem choose_mul_pow_le {M n : ℕ} {Bd c : ℝ} (hc : 0 ≤ c) (hMB : (M : ℝ) ≤ Bd) :
    (M.choose n : ℝ) * c ^ n ≤ Bd ^ n / n ! * c ^ n := by
  have h2 : (M.choose n : ℝ) ≤ (M : ℝ) ^ n / n ! := Nat.choose_le_pow_div n M
  have h3 : (M : ℝ) ^ n ≤ Bd ^ n := pow_le_pow_left₀ (Nat.cast_nonneg M) hMB n
  have h4 : (M : ℝ) ^ n / n ! ≤ Bd ^ n / n ! := by gcongr
  exact mul_le_mul_of_nonneg_right (h2.trans h4) (pow_nonneg hc n)

/-- `a^{4-n} |[tⁿ]P| ≤ Bdⁿ/n! · a⁴(1 + r)⁴` for `P ≪ (1 + a r t)^M`, `M ≤ Bd`, `n ≤ 4`. -/
theorem scaled_coeff_bound {P : ℝ[X]} {a r : ℝ} (ha : 0 ≤ a) (hr : 0 ≤ r) {M : ℕ}
    (h : Maj1 P ((C 1 + C (a * r) * X) ^ M)) {Bd : ℝ} (hMB : (M : ℝ) ≤ Bd) {n : ℕ}
    (hn : n ≤ 4) {F : ℝ} (hF : ((n ! : ℕ) : ℝ) = F) :
    a ^ (4 - n) * |P.coeff n| ≤ Bd ^ n / F * (a ^ 4 * (1 + r) ^ 4) := by
  have h1 := (abs_coeff_le_choose h n).trans (choose_mul_pow_le (mul_nonneg ha hr) hMB)
  have hBd : 0 ≤ Bd := (Nat.cast_nonneg M).trans hMB
  have hrn : r ^ n ≤ (1 + r) ^ 4 :=
    (pow_le_pow_left₀ hr (by linarith) n).trans (pow_le_pow_right₀ (by linarith) hn)
  have e : a ^ (4 - n) * (a * r) ^ n = a ^ 4 * r ^ n := by
    rw [mul_pow, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hn]
  rw [← hF]
  calc a ^ (4 - n) * |P.coeff n| ≤ a ^ (4 - n) * (Bd ^ n / n ! * (a * r) ^ n) :=
        mul_le_mul_of_nonneg_left h1 (pow_nonneg ha _)
    _ = Bd ^ n / n ! * (a ^ 4 * r ^ n) := by rw [← e]; ring
    _ ≤ Bd ^ n / n ! * (a ^ 4 * (1 + r) ^ 4) := by gcongr

/-- The cancellation bound: `|[t⁴]P| ≤ 2 Bd³/6 · a⁴(1 + r)⁴` for
`P ≪ (1 + a r t)^{N+2} - (1 + a r t)^N`, `N + 1 ≤ Bd`. -/
theorem diff_coeff_bound {P : ℝ[X]} {a r : ℝ} (hr : 0 ≤ r) {N : ℕ}
    (h : Maj1 P ((C 1 + C (a * r) * X) ^ (N + 2) - (C 1 + C (a * r) * X) ^ N)) {Bd : ℝ}
    (hNB : (N : ℝ) + 1 ≤ Bd) : |P.coeff 4| ≤ 2 * Bd ^ 3 / 6 * (a ^ 4 * (1 + r) ^ 4) := by
  have h1 := abs_coeff_le_of_maj1 h 4
  rw [coeff_sub, coeff_C_add_C_mul_X_pow, coeff_C_add_C_mul_X_pow, one_pow, one_pow, mul_one,
    mul_one] at h1
  have e1 : (N + 2).choose 4 = (N + 1).choose 3 + (N + 1).choose 4 :=
    Nat.choose_succ_succ (N + 1) 3
  have e2 : (N + 1).choose 4 = N.choose 3 + N.choose 4 := Nat.choose_succ_succ N 3
  have e : ((N + 2).choose 4 : ℝ) - N.choose 4 = (N + 1).choose 3 + N.choose 3 := by
    rw [e1, e2]
    push_cast
    ring
  have e3 : ((3 ! : ℕ) : ℝ) = 6 := by norm_num [Nat.factorial]
  have b1 : ((N + 1).choose 3 : ℝ) ≤ Bd ^ 3 / 6 := by
    have h0 := Nat.choose_le_pow_div (α := ℝ) 3 (N + 1)
    have h3 : ((N : ℝ) + 1) ^ 3 ≤ Bd ^ 3 := pow_le_pow_left₀ (by positivity) hNB 3
    rw [e3] at h0
    push_cast at h0
    linarith
  have b2 : (N.choose 3 : ℝ) ≤ Bd ^ 3 / 6 := by
    have h0 := Nat.choose_le_pow_div (α := ℝ) 3 N
    have h3 : (N : ℝ) ^ 3 ≤ Bd ^ 3 := pow_le_pow_left₀ (by positivity) (by linarith) 3
    rw [e3] at h0
    linarith
  have hrr : (a * r) ^ 4 ≤ a ^ 4 * (1 + r) ^ 4 := by
    rw [mul_pow]
    have : r ^ 4 ≤ (1 + r) ^ 4 := pow_le_pow_left₀ hr (by linarith) 4
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have hBd : 0 ≤ Bd ^ 3 / 6 := le_trans (Nat.cast_nonneg _) b2
  calc |P.coeff 4| ≤ ((N + 2).choose 4 : ℝ) * (a * r) ^ 4 - (N.choose 4 : ℝ) * (a * r) ^ 4 := h1
    _ = (((N + 1).choose 3 : ℝ) + N.choose 3) * (a * r) ^ 4 := by rw [← e]; ring
    _ ≤ (Bd ^ 3 / 6 + Bd ^ 3 / 6) * (a ^ 4 * (1 + r) ^ 4) :=
        mul_le_mul (add_le_add b1 b2) hrr (by positivity) (by positivity)
    _ = 2 * Bd ^ 3 / 6 * (a ^ 4 * (1 + r) ^ 4) := by ring

theorem coeff_lin_prod (μ ν c : ℝ) (K n : ℕ) :
    (C μ * (C 1 + C c * X) * (C ν * (C 1 + C c * X)) * (C 1 + C c * X) ^ K).coeff n =
      μ * ν * ((K + 2).choose n * c ^ n) := by
  rw [show C μ * (C 1 + C c * X) * (C ν * (C 1 + C c * X)) * (C 1 + C c * X) ^ K =
      C (μ * ν) * (C 1 + C c * X) ^ (K + 2) by rw [map_mul]; ring,
    coeff_C_mul, coeff_C_add_C_mul_X_pow, one_pow, mul_one]

/-! ### Two-variable majorants -/

/-- `Λ = 1 + c₁ t + c₂ s`. -/
noncomputable def lamP (c₁ c₂ : ℝ) : ℝ[X][X] := mono2 1 0 0 + mono2 c₁ 1 0 + mono2 c₂ 0 1

theorem lamP_eq (c₁ c₂ : ℝ) : lamP c₁ c₂ = C (C 1 + C c₁ * X) + C (C c₂) * X := by
  simp only [lamP, mono2, map_add, map_mul, pow_zero, pow_one, mul_one]

theorem coeff2_lamP_pow (c₁ c₂ : ℝ) (N m n : ℕ) :
    coeff2 (lamP c₁ c₂ ^ N) m n = N.choose n * ((N - n).choose m * c₁ ^ m) * c₂ ^ n := by
  rw [lamP_eq, coeff2, coeff_C_add_C_mul_X_pow, ← C_eq_natCast, ← C_pow, coeff_mul_C,
    coeff_C_mul, coeff_C_add_C_mul_X_pow, one_pow, mul_one]

theorem maj2_lin3 {u₀ u₁ u₂ v₀ v₁ v₂ : ℝ} (h₀ : |u₀| ≤ v₀) (h₁ : |u₁| ≤ v₁) (h₂ : |u₂| ≤ v₂) :
    Maj2 (mono2 u₀ 0 0 + mono2 u₁ 1 0 + mono2 u₂ 0 1)
      (mono2 v₀ 0 0 + mono2 v₁ 1 0 + mono2 v₂ 0 1) :=
  isMaj2.add (isMaj2.add (maj2_mono h₀ 0 0) (maj2_mono h₁ 1 0)) (maj2_mono h₂ 0 1)

theorem maj2_quad6 {u₀ u₁ u₂ u₃ u₄ u₅ v₀ v₁ v₂ v₃ v₄ v₅ : ℝ} (h₀ : |u₀| ≤ v₀) (h₁ : |u₁| ≤ v₁)
    (h₂ : |u₂| ≤ v₂) (h₃ : |u₃| ≤ v₃) (h₄ : |u₄| ≤ v₄) (h₅ : |u₅| ≤ v₅) :
    Maj2 (mono2 u₀ 0 0 + mono2 u₁ 1 0 + mono2 u₂ 0 1 + mono2 u₃ 2 0 + mono2 u₄ 1 1 + mono2 u₅ 0 2)
      (mono2 v₀ 0 0 + mono2 v₁ 1 0 + mono2 v₂ 0 1 + mono2 v₃ 2 0 + mono2 v₄ 1 1 + mono2 v₅ 0 2) :=
  isMaj2.add (isMaj2.add (isMaj2.add (isMaj2.add (isMaj2.add (maj2_mono h₀ 0 0)
    (maj2_mono h₁ 1 0)) (maj2_mono h₂ 0 1)) (maj2_mono h₃ 2 0)) (maj2_mono h₄ 1 1))
    (maj2_mono h₅ 0 2)

theorem lamP_scale (μ c₁ c₂ : ℝ) :
    mono2 μ 0 0 + mono2 (μ * c₁) 1 0 + mono2 (μ * c₂) 0 1 = C (C μ) * lamP c₁ c₂ := by
  simp only [lamP, mono2, map_mul, map_one]
  ring

theorem lamP_sq (c₁ c₂ : ℝ) : lamP c₁ c₂ ^ 2 =
    mono2 1 0 0 + mono2 (2 * c₁) 1 0 + mono2 (2 * c₂) 0 1 + mono2 (c₁ ^ 2) 2 0 +
      mono2 (2 * c₁ * c₂) 1 1 + mono2 (c₂ ^ 2) 0 2 := by
  simp only [lamP, mono2, map_mul, map_pow, map_one, map_ofNat]
  ring

private theorem bnd_lin {a u r : ℝ} (ha : 0 ≤ a) (hu : |u| ≤ r) :
    |2 * a * u| ≤ 2 * (a * (1 + r)) := by
  rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg ha]
  nlinarith [mul_le_mul_of_nonneg_left hu ha]

private theorem bnd_lin' {a u r : ℝ} (ha : 0 ≤ a) (hu : |u| ≤ r) :
    |-(2 * a * u)| ≤ 2 * (a * (1 + r)) := by
  rw [abs_neg]
  exact bnd_lin ha hu

private theorem bnd_quad {a e r : ℝ} (hr : 0 ≤ r) (he : 0 ≤ e) (her : e ≤ r ^ 2) :
    |-(a ^ 2 * e)| ≤ (a * (1 + r)) ^ 2 := by
  rw [abs_neg, abs_of_nonneg (mul_nonneg (sq_nonneg a) he)]
  nlinarith [mul_le_mul_of_nonneg_left her (sq_nonneg a),
    mul_nonneg (sq_nonneg a) (by linarith : (0 : ℝ) ≤ 1 + 2 * r)]

private theorem bnd_cross {a e r₁ r₂ : ℝ} (hr₁ : 0 ≤ r₁) (hr₂ : 0 ≤ r₂)
    (he : |e| ≤ r₁ * r₂) : |-(2 * a ^ 2 * e)| ≤ 2 * (a * (1 + r₁)) * (a * (1 + r₂)) := by
  rw [abs_neg, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    abs_of_nonneg (sq_nonneg a)]
  nlinarith [mul_le_mul_of_nonneg_left he (sq_nonneg a), mul_nonneg (sq_nonneg a) hr₁,
    mul_nonneg (sq_nonneg a) hr₂]

section Maj2

variable {a : ℝ} {A B : Matrix ι ι ℝ} {x : ι → ℝ}

theorem maj_planeRp2 (ha : 0 ≤ a) (hA : A.PosSemidef) (hα : 0 < starAlpha A x) (i k : ι) :
    Maj2 (planeRp2 a A x i k)
      (lamP (a * (1 + starScale a A B x i)) (a * (1 + starScale a A B x k)) ^ 2) := by
  rw [lamP_sq]
  exact maj2_quad6 (by simp) (bnd_lin ha (abs_starRow_le i)) (bnd_lin ha (abs_starRow_le k))
    (bnd_quad (starScale_nonneg i) (starCore_diag_nonneg hA hα i) (starCore_le_sq hA hα i))
    (bnd_cross (starScale_nonneg i) (starScale_nonneg k) (abs_starCore_le hA hα i k))
    (bnd_quad (starScale_nonneg k) (starCore_diag_nonneg hA hα k) (starCore_le_sq hA hα k))

theorem maj_planeRm2 (ha : 0 ≤ a) (hB : B.PosSemidef) (hβ : 0 < starAlpha B x) (i k : ι) :
    Maj2 (planeRm2 a B x i k)
      (lamP (a * (1 + starScale a A B x i)) (a * (1 + starScale a A B x k)) ^ 2) := by
  rw [lamP_sq]
  exact maj2_quad6 (by simp) (bnd_lin' ha (abs_starRow_neg_le i))
    (bnd_lin' ha (abs_starRow_neg_le k))
    (bnd_quad (starScale_nonneg i) (starCore_diag_nonneg hB hβ i) (starCore_le_sq' hB hβ i))
    (bnd_cross (starScale_nonneg i) (starScale_nonneg k) (abs_starCore_le' hB hβ i k))
    (bnd_quad (starScale_nonneg k) (starCore_diag_nonneg hB hβ k) (starCore_le_sq' hB hβ k))

theorem maj_planePi (ha : 0 ≤ a) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hα : 0 < starAlpha A x) (hβ : 0 < starAlpha B x) (i k : ι) (m m' : ℕ) :
    Maj2 (planePi a A B x i k m m')
      (lamP (a * (1 + starScale a A B x i)) (a * (1 + starScale a A B x k)) ^ (2 * (m + m'))) := by
  have h := isMaj2.mul (isMaj2.pow (maj_planeRp2 (B := B) ha hA hα i k) m)
    (isMaj2.pow (maj_planeRm2 (A := A) ha hB hβ i k) m')
  rw [← pow_mul, ← pow_mul, ← pow_add, ← mul_add] at h
  exact h

private theorem le_mul_of_abs {a e μ c : ℝ} (ha : 0 ≤ a) (hc : a ≤ c) (he : |e| ≤ μ) :
    |a * e| ≤ μ * c := by
  rw [abs_mul, abs_of_nonneg ha]
  calc a * |e| ≤ c * μ := mul_le_mul hc he (abs_nonneg _) (ha.trans hc)
    _ = μ * c := mul_comm _ _

theorem maj_planeU2 (ha : 0 ≤ a) (A : Matrix ι ι ℝ) (x : ι → ℝ) (i k j : ι) {c₁ c₂ : ℝ}
    (hc₁ : a ≤ c₁) (hc₂ : a ≤ c₂) :
    Maj2 (planeU2 a A x i k j)
      (C (C (|starRow a A x j| + (|starCore a A x i j| + |starCore a A x k j|))) * lamP c₁ c₂) := by
  rw [← lamP_scale]
  refine maj2_lin3 ?_ ?_ ?_
  · exact le_add_of_nonneg_right (by positivity)
  · rw [abs_neg]
    refine le_mul_of_abs ha hc₁ ?_
    have := abs_nonneg (starCore a A x k j)
    have := abs_nonneg (starRow a A x j)
    linarith
  · rw [abs_neg]
    refine le_mul_of_abs ha hc₂ ?_
    have := abs_nonneg (starCore a A x i j)
    have := abs_nonneg (starRow a A x j)
    linarith

theorem maj_planeW2 (ha : 0 ≤ a) (B : Matrix ι ι ℝ) (x : ι → ℝ) (i k j : ι) {c₁ c₂ : ℝ}
    (hc₁ : a ≤ c₁) (hc₂ : a ≤ c₂) :
    Maj2 (planeW2 a B x i k j)
      (C (C (|starRow (-a) B x j| + (|starCore a B x i j| + |starCore a B x k j|))) *
        lamP c₁ c₂) := by
  rw [← lamP_scale]
  refine maj2_lin3 ?_ ?_ ?_
  · exact le_add_of_nonneg_right (by positivity)
  · refine le_mul_of_abs ha hc₁ ?_
    have := abs_nonneg (starCore a B x k j)
    have := abs_nonneg (starRow (-a) B x j)
    linarith
  · refine le_mul_of_abs ha hc₂ ?_
    have := abs_nonneg (starCore a B x i j)
    have := abs_nonneg (starRow (-a) B x j)
    linarith

end Maj2

theorem coeff2_lamP_prod (μ ν c₁ c₂ : ℝ) (K : ℕ) :
    coeff2 (C (C μ) * lamP c₁ c₂ * (C (C ν) * lamP c₁ c₂) * lamP c₁ c₂ ^ K) 4 4 =
      μ * ν * ((K + 2).choose 4 * ((K + 2 - 4).choose 4 * c₁ ^ 4) * c₂ ^ 4) := by
  rw [show C (C μ) * lamP c₁ c₂ * (C (C ν) * lamP c₁ c₂) * lamP c₁ c₂ ^ K =
      C (C (μ * ν)) * lamP c₁ c₂ ^ (K + 2) by rw [map_mul, map_mul]; ring,
    coeff2_CC_mul, coeff2_lamP_pow]

theorem choose44_le {N : ℕ} {Bd c₁ c₂ : ℝ} (hN : (N : ℝ) ≤ Bd) :
    (N.choose 4 : ℝ) * ((N - 4).choose 4 * c₁ ^ 4) * c₂ ^ 4 ≤
      Bd ^ 8 / 576 * (c₁ ^ 4 * c₂ ^ 4) := by
  have e4 : ((4 ! : ℕ) : ℝ) = 24 := by norm_num [Nat.factorial]
  have h1 : (N.choose 4 : ℝ) ≤ Bd ^ 4 / 24 := by
    have h0 := Nat.choose_le_pow_div (α := ℝ) 4 N
    have h4 : (N : ℝ) ^ 4 ≤ Bd ^ 4 := pow_le_pow_left₀ (Nat.cast_nonneg N) hN 4
    rw [e4] at h0
    linarith
  have h2 : ((N - 4).choose 4 : ℝ) ≤ Bd ^ 4 / 24 :=
    le_trans (by exact_mod_cast Nat.choose_le_choose 4 (Nat.sub_le N 4)) h1
  have h0 : (0 : ℝ) ≤ (N - 4).choose 4 := Nat.cast_nonneg _
  have h0' : (0 : ℝ) ≤ N.choose 4 := Nat.cast_nonneg _
  calc (N.choose 4 : ℝ) * ((N - 4).choose 4 * c₁ ^ 4) * c₂ ^ 4 =
        (N.choose 4 : ℝ) * (N - 4).choose 4 * (c₁ ^ 4 * c₂ ^ 4) := by ring
    _ ≤ (Bd ^ 4 / 24) * (Bd ^ 4 / 24) * (c₁ ^ 4 * c₂ ^ 4) := by gcongr
    _ = Bd ^ 8 / 576 * (c₁ ^ 4 * c₂ ^ 4) := by ring

end Poly

/-! ### Real-number cores of the bounds -/

theorem one_marks_le (x z e f : ℝ) :
    (|x| + |e|) * (|x| + |e|) + (|x| + |e|) * (|z| + |f|) ≤
      2 * (x ^ 2 + |x * z| + |x * e| + |x * f| + |e * z| + e ^ 2 + |e * f|) := by
  rw [abs_mul x z, abs_mul x e, abs_mul x f, abs_mul e z, abs_mul e f]
  nlinarith [sq_abs x, sq_abs e, mul_nonneg (abs_nonneg x) (abs_nonneg z),
    mul_nonneg (abs_nonneg x) (abs_nonneg f), mul_nonneg (abs_nonneg e) (abs_nonneg z),
    mul_nonneg (abs_nonneg e) (abs_nonneg f), mul_nonneg (abs_nonneg x) (abs_nonneg e),
    sq_nonneg x, sq_nonneg e]

theorem two_marks_le (x z e₁ e₂ f₁ f₂ : ℝ) :
    (|x| + (|e₁| + |e₂|)) * (|x| + (|e₁| + |e₂|)) +
        (|x| + (|e₁| + |e₂|)) * (|z| + (|f₁| + |f₂|)) ≤
      2 * (x ^ 2 + |x * z| + |x| * (|e₁| + |e₂|) + |x| * (|f₁| + |f₂|) +
        (|e₁| + |e₂|) * |z| + (|e₁| + |e₂|) ^ 2 + (|e₁| + |e₂|) * (|f₁| + |f₂|)) := by
  rw [abs_mul x z]
  have hE : 0 ≤ |e₁| + |e₂| := by positivity
  have hF : 0 ≤ |f₁| + |f₂| := by positivity
  nlinarith [sq_abs x, mul_nonneg (abs_nonneg x) (abs_nonneg z), mul_nonneg (abs_nonneg x) hF,
    mul_nonneg hE (abs_nonneg z), mul_nonneg hE hF, mul_nonneg (abs_nonneg x) hE, sq_nonneg x,
    sq_nonneg (|e₁| + |e₂|)]

/-- Grade-two core: from `|U_j| ≤ μ_j² B`, `|W_j| ≤ μ_j ν_j B`, `μ_j² + μ_j ν_j ≤ 2 m_j` and
`N · 2pB ≤ Kc · Cst · p⁹`: `|N Φ Σ_j ((p-1) U_j - p W_j)| ≤ Φ Kc Cst p⁹ Σ_j m_j`. -/
theorem grade_two_real {J : Type*} (s : Finset J) {p B Φ N Kc Cst : ℝ} (hp : 1 ≤ p)
    (hB : 0 ≤ B) (hΦ : 0 ≤ Φ) (hN : 0 ≤ N) (hNB : N * (2 * p * B) ≤ Kc * Cst * p ^ 9)
    (μ ν U W m : J → ℝ) (hU : ∀ j, |U j| ≤ μ j * μ j * B) (hW : ∀ j, |W j| ≤ μ j * ν j * B)
    (hm : ∀ j, μ j * μ j + μ j * ν j ≤ 2 * m j) (hm0 : ∀ j, 0 ≤ m j) :
    |N * (Φ * ∑ j ∈ s, ((p - 1) * U j - p * W j))| ≤ Φ * Kc * Cst * p ^ 9 * ∑ j ∈ s, m j := by
  have hp0 : 0 ≤ p := by linarith
  have hterm : ∀ j, |(p - 1) * U j - p * W j| ≤ 2 * p * B * m j := by
    intro j
    have h1 : |(p - 1) * U j - p * W j| ≤ (p - 1) * |U j| + p * |W j| := by
      calc _ ≤ |(p - 1) * U j| + |p * W j| := abs_sub_le_add _ _
        _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg (by linarith), abs_of_nonneg hp0]
    have h2 : (p - 1) * |U j| ≤ p * (μ j * μ j * B) :=
      mul_le_mul (by linarith) (hU j) (abs_nonneg _) hp0
    have h3 : p * |W j| ≤ p * (μ j * ν j * B) := mul_le_mul_of_nonneg_left (hW j) hp0
    have h4 := mul_le_mul_of_nonneg_left (hm j) (mul_nonneg hp0 hB)
    nlinarith
  have hsum : |∑ j ∈ s, ((p - 1) * U j - p * W j)| ≤ 2 * p * B * ∑ j ∈ s, m j := by
    calc |∑ j ∈ s, ((p - 1) * U j - p * W j)| ≤ ∑ j ∈ s, |(p - 1) * U j - p * W j| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ s, 2 * p * B * m j := Finset.sum_le_sum fun j _ => hterm j
      _ = 2 * p * B * ∑ j ∈ s, m j := by rw [Finset.mul_sum]
  have hS0 : 0 ≤ ∑ j ∈ s, m j := Finset.sum_nonneg fun j _ => hm0 j
  rw [abs_mul, abs_mul, abs_of_nonneg hN, abs_of_nonneg hΦ]
  calc N * (Φ * |∑ j ∈ s, ((p - 1) * U j - p * W j)|) ≤
        N * (Φ * (2 * p * B * ∑ j ∈ s, m j)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum hΦ) hN
    _ = Φ * (N * (2 * p * B)) * ∑ j ∈ s, m j := by ring
    _ ≤ Φ * (Kc * Cst * p ^ 9) * ∑ j ∈ s, m j :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hNB hΦ) hS0
    _ = Φ * Kc * Cst * p ^ 9 * ∑ j ∈ s, m j := by ring

/-- Grade-one core (the `p⁵` term multiplies only `Σ x_j (x_j - z_j)`). -/
theorem grade_one_real {J : Type*} (s : Finset J) {p a K Φ : ℝ} (hp : 1 ≤ p) (ha : 0 ≤ a)
    (hK : 0 ≤ K) (hΦ : 0 ≤ Φ) {P12 P13 P14 P22 P23 P24 : ℝ}
    (h12 : a ^ 2 * |P12| ≤ (4 * p) ^ 2 / 2 * K) (h13 : a * |P13| ≤ (4 * p) ^ 3 / 6 * K)
    (h22 : a ^ 2 * |P22| ≤ (4 * p) ^ 2 / 2 * K) (h23 : a * |P23| ≤ (4 * p) ^ 3 / 6 * K)
    (h24 : |P24| ≤ (4 * p) ^ 4 / 24 * K) (hD : |P14 - P24| ≤ 2 * (4 * p) ^ 3 / 6 * K)
    (xs zs es fs U4 W4 : J → ℝ)
    (hU : ∀ j, U4 j = xs j * xs j * P14 + (xs j * -(a * es j) + -(a * es j) * xs j) * P13 +
      -(a * es j) * -(a * es j) * P12)
    (hW : ∀ j, W4 j = xs j * zs j * P24 + (xs j * (a * fs j) + -(a * es j) * zs j) * P23 +
      -(a * es j) * (a * fs j) * P22) :
    |24 * (Φ * ∑ j ∈ s, ((p - 1) * U4 j - p * W4 j))| ≤
      Φ * K * 1000 * (p ^ 5 * |∑ j ∈ s, xs j * (xs j - zs j)| +
        p ^ 4 * ∑ j ∈ s, (xs j ^ 2 + |xs j * es j| + |xs j * fs j| + |es j * zs j| + es j ^ 2 +
          |es j * fs j|)) := by
  have hp0 : 0 ≤ p := by linarith
  have hp1 : 0 ≤ p - 1 := by linarith
  have hp34 : p ^ 3 ≤ p ^ 4 := pow_le_pow_right₀ hp (by norm_num)
  have hp34K := mul_le_mul_of_nonneg_right hp34 hK
  have cS : p * |P24| ≤ 32 / 3 * p ^ 5 * K := by
    have := mul_le_mul_of_nonneg_left h24 hp0
    calc p * |P24| ≤ p * ((4 * p) ^ 4 / 24 * K) := this
      _ = 32 / 3 * p ^ 5 * K := by ring
  have cX : |(p - 1) * (P14 - P24) - P24| ≤ 32 * p ^ 4 * K := by
    have h1 : |(p - 1) * (P14 - P24) - P24| ≤ (p - 1) * |P14 - P24| + |P24| := by
      calc _ ≤ |(p - 1) * (P14 - P24)| + |P24| := abs_sub_le_add _ _
        _ = _ := by rw [abs_mul, abs_of_nonneg hp1]
    have h2 : (p - 1) * |P14 - P24| ≤ p * (2 * (4 * p) ^ 3 / 6 * K) :=
      mul_le_mul (by linarith) hD (abs_nonneg _) hp0
    have h3 : p * (2 * (4 * p) ^ 3 / 6 * K) + (4 * p) ^ 4 / 24 * K = 32 * p ^ 4 * K := by ring
    linarith
  have cXE : 2 * (p - 1) * (a * |P13|) ≤ 64 / 3 * p ^ 4 * K := by
    have := mul_le_mul (by linarith : 2 * (p - 1) ≤ 2 * p) h13 (by positivity) (by positivity)
    calc _ ≤ 2 * p * ((4 * p) ^ 3 / 6 * K) := this
      _ = 64 / 3 * p ^ 4 * K := by ring
  have cEE : (p - 1) * (a ^ 2 * |P12|) ≤ 8 * p ^ 4 * K := by
    have := mul_le_mul (by linarith : p - 1 ≤ p) h12 (by positivity) hp0
    have e : p * ((4 * p) ^ 2 / 2 * K) = 8 * p ^ 3 * K := by ring
    linarith
  have cXF : p * (a * |P23|) ≤ 32 / 3 * p ^ 4 * K := by
    have := mul_le_mul_of_nonneg_left h23 hp0
    calc _ ≤ p * ((4 * p) ^ 3 / 6 * K) := this
      _ = 32 / 3 * p ^ 4 * K := by ring
  have cEF : p * (a ^ 2 * |P22|) ≤ 8 * p ^ 4 * K := by
    have := mul_le_mul_of_nonneg_left h22 hp0
    have e : p * ((4 * p) ^ 2 / 2 * K) = 8 * p ^ 3 * K := by ring
    linarith
  obtain ⟨T, hTdef⟩ : ∃ T : J → ℝ, ∀ j, T j = ((p - 1) * (P14 - P24) - P24) * xs j ^ 2 +
      -(2 * (p - 1)) * (a * P13) * (xs j * es j) + (p - 1) * (a ^ 2 * P12) * es j ^ 2 +
      -p * (a * P23) * (xs j * fs j - es j * zs j) + p * (a ^ 2 * P22) * (es j * fs j) :=
    ⟨_, fun j => rfl⟩
  have hsum : ∑ j ∈ s, ((p - 1) * U4 j - p * W4 j) =
      p * P24 * ∑ j ∈ s, xs j * (xs j - zs j) + ∑ j ∈ s, T j := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hU, hW, hTdef]
    ring
  have hTb : ∀ j, |T j| ≤ 1000 / 24 * (K * p ^ 4) * (xs j ^ 2 + |xs j * es j| +
      |xs j * fs j| + |es j * zs j| + es j ^ 2 + |es j * fs j|) := by
    intro j
    rw [hTdef]
    have t1 : |((p - 1) * (P14 - P24) - P24) * xs j ^ 2| ≤ 32 * p ^ 4 * K * xs j ^ 2 := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg (xs j))]
      exact mul_le_mul_of_nonneg_right cX (sq_nonneg _)
    have t2 : |-(2 * (p - 1)) * (a * P13) * (xs j * es j)| ≤
        64 / 3 * p ^ 4 * K * |xs j * es j| := by
      rw [abs_mul (-(2 * (p - 1)) * (a * P13)), abs_mul (-(2 * (p - 1))), abs_neg,
        abs_mul a, abs_of_nonneg ha, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * (p - 1))]
      exact mul_le_mul_of_nonneg_right cXE (abs_nonneg _)
    have t3 : |(p - 1) * (a ^ 2 * P12) * es j ^ 2| ≤ 8 * p ^ 4 * K * es j ^ 2 := by
      rw [abs_mul ((p - 1) * (a ^ 2 * P12)), abs_mul (p - 1), abs_mul (a ^ 2),
        abs_of_nonneg hp1, abs_of_nonneg (sq_nonneg a), abs_of_nonneg (sq_nonneg (es j))]
      exact mul_le_mul_of_nonneg_right cEE (sq_nonneg _)
    have t4 : |-p * (a * P23) * (xs j * fs j - es j * zs j)| ≤
        32 / 3 * p ^ 4 * K * (|xs j * fs j| + |es j * zs j|) := by
      rw [abs_mul (-p * (a * P23)), abs_mul (-p), abs_neg, abs_mul a, abs_of_nonneg ha,
        abs_of_nonneg hp0]
      calc p * (a * |P23|) * |xs j * fs j - es j * zs j| ≤
            p * (a * |P23|) * (|xs j * fs j| + |es j * zs j|) :=
          mul_le_mul_of_nonneg_left (abs_sub_le_add _ _) (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_right cXF (by positivity)
    have t5 : |p * (a ^ 2 * P22) * (es j * fs j)| ≤ 8 * p ^ 4 * K * |es j * fs j| := by
      rw [abs_mul (p * (a ^ 2 * P22)), abs_mul p, abs_mul (a ^ 2), abs_of_nonneg hp0,
        abs_of_nonneg (sq_nonneg a)]
      exact mul_le_mul_of_nonneg_right cEF (abs_nonneg _)
    refine (abs_add5_le _ _ _ _ _).trans ?_
    have hW0 : 0 ≤ K * p ^ 4 := by positivity
    nlinarith [mul_nonneg hW0 (sq_nonneg (xs j)), mul_nonneg hW0 (abs_nonneg (xs j * es j)),
      mul_nonneg hW0 (abs_nonneg (xs j * fs j)), mul_nonneg hW0 (abs_nonneg (es j * zs j)),
      mul_nonneg hW0 (sq_nonneg (es j)), mul_nonneg hW0 (abs_nonneg (es j * fs j))]
  rw [hsum]
  have hmS : 0 ≤ ∑ j ∈ s, (xs j ^ 2 + |xs j * es j| + |xs j * fs j| + |es j * zs j| +
      es j ^ 2 + |es j * fs j|) := Finset.sum_nonneg fun j _ => by positivity
  have hSum : |∑ j ∈ s, T j| ≤ 1000 / 24 * (K * p ^ 4) * ∑ j ∈ s, (xs j ^ 2 + |xs j * es j| +
      |xs j * fs j| + |es j * zs j| + es j ^ 2 + |es j * fs j|) := by
    calc |∑ j ∈ s, T j| ≤ ∑ j ∈ s, |T j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ s, 1000 / 24 * (K * p ^ 4) * (xs j ^ 2 + |xs j * es j| + |xs j * fs j| +
          |es j * zs j| + es j ^ 2 + |es j * fs j|) := Finset.sum_le_sum fun j _ => hTb j
      _ = _ := by rw [← Finset.mul_sum]
  have hS : |p * P24 * ∑ j ∈ s, xs j * (xs j - zs j)| ≤
      32 / 3 * p ^ 5 * K * |∑ j ∈ s, xs j * (xs j - zs j)| := by
    rw [abs_mul, abs_mul, abs_of_nonneg hp0]
    exact mul_le_mul_of_nonneg_right cS (abs_nonneg _)
  have hA := abs_add_le (p * P24 * ∑ j ∈ s, xs j * (xs j - zs j)) (∑ j ∈ s, T j)
  have hK5 : 0 ≤ p ^ 5 * K * |∑ j ∈ s, xs j * (xs j - zs j)| := by positivity
  have key : |p * P24 * ∑ j ∈ s, xs j * (xs j - zs j) + ∑ j ∈ s, T j| ≤
      1000 / 24 * (K * (p ^ 5 * |∑ j ∈ s, xs j * (xs j - zs j)| +
        p ^ 4 * ∑ j ∈ s, (xs j ^ 2 + |xs j * es j| + |xs j * fs j| + |es j * zs j| +
          es j ^ 2 + |es j * fs j|))) := by
    nlinarith
  rw [abs_mul, abs_mul, abs_of_nonneg hΦ, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 24)]
  calc 24 * (Φ * |p * P24 * ∑ j ∈ s, xs j * (xs j - zs j) + ∑ j ∈ s, T j|) ≤
        24 * (Φ * (1000 / 24 * (K * (p ^ 5 * |∑ j ∈ s, xs j * (xs j - zs j)| +
          p ^ 4 * ∑ j ∈ s, (xs j ^ 2 + |xs j * es j| + |xs j * fs j| + |es j * zs j| +
            es j ^ 2 + |es j * fs j|))))) := by gcongr
    _ = _ := by ring

end SecC

end BiluLinial.Tight
