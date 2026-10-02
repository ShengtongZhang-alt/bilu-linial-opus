/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecC.MarkLine

/-!
# Marked derivative bounds for the row numerator (node T.MARK of `docs/tight/BP_SECC.md`)

AUDIT-C §3 (T.MARK), source lines 1102–1127 (CR2, mark preservation) and 1153–1162,
1180–1190 (only the first two grades need marks). Everything is at the star level: `A, B ⪰ 0`
on `ι = N`, `a > 0`, a point `x` with `α = 1 - q_A(x) > 0`, `β = 1 - q_B(x) > 0`, and the star
forms `x_j = starRow a A x j`, `z_j = starRow (-a) B x j`, `e_kj = starCore a A x k j`,
`f_kj = starCore a B x k j`, `r_i = starScale a A B x i` (at sign endpoints these are the
physical `G⁺_vj`, `G⁻_vj`, `G⁺_vv G⁺_{K,kj}`, `G⁻_vv G⁻_{K,kj}`, by `root_F1`).

**Line representation** (`rowNum_line`, exact). With `u_j(t) = x_j - a e_ij t`,
`w_j(t) = z_j + a f_ij t`, `ρ₊(t) = 1 + 2a x_i t - a² e_ii t²`, `ρ₋(t) = 1 - 2a z_i t - a² f_ii t²`
(`α(x + t e_i) = α ρ₊(t)`, `β(x + t e_i) = β ρ₋(t)`), whenever `ρ₊(t), ρ₋(t) ≥ 0`:
`F(x + t e_i) = a² α^p β^p Σ_j [(p-1) u_j² ρ₊^{p-2} ρ₋^p - p u_j w_j ρ₊^{p-1} ρ₋^{p-1}]`.
This replaces the source's derivative words (CR2) by coefficient majorants of one-variable
polynomials (AUDIT-C §9): `ρ_± ≪ (1 + a r_i t)²`, so `[tⁿ] ρ₊^m ρ₋^{m'} ≤ (4p)ⁿ (a r_i)ⁿ / n!`.

**Grade 1** (`mark_grade_one`). `∂_i⁴F(x) = 24 [t⁴]` of the line polynomial. Split the
base-point part `Σ_j [(p-1) x_j² c₁ - p x_j z_j c₂]` (`c_k = [t⁴] Π_k`) as
`p c₂ Σ_j x_j(x_j - z_j) + ((p-1)c₁ - p c₂) Σ_j x_j²`; `|p c₂| ≤ (32/3) p⁵ a⁴ r⁴` and
`|(p-1)(c₁ - c₂) - c₂| ≤ 41 p⁴ a⁴ r⁴` because `c₁ - c₂ = [t⁴] ρ₊^{p-2}ρ₋^{p-1}(ρ₋ - ρ₊)` and
`ρ₋ - ρ₊` has no constant term. Every other term carries a core mark `e_ij` or `f_ij` and a
coefficient `≤ 22 p⁴ a⁴ r³` (or `8 p³ a⁴ r²`). Times `24`, all coefficients are `≤ 1000`. This
is the source's "`Φ⁽⁴⁾ 𝓡_v` keeps the row marks with coefficient `p⁵`; every other term has
coefficient `p⁴`", in the GCI-free form of CR3′ (the `p⁵` term multiplies only `Σ x_j(x_j - z_j)`).

**Grade 2** (`mark_grade_two_diag`, `mark_grade_two_mixed`). `∂_i⁶ F = 720 [t⁶]`, and
`∂_i⁴ ∂_k⁴ F = 576 [t⁴ s⁴]` of the two-variable polynomial along `x + t e_i + s e_k` (`i ≠ k`),
with `ρ_± ≪ (1 + a r_i t + a r_k s)²` (`|e_ik| ≤ √(e_ii e_kk)`): every monomial has two marks
and coefficient `≤ 10⁶ p⁹`.

**Proofs** (helpers in `SecC/MarkPoly.lean`, `SecC/MarkLine.lean`). Near `x`, `F` agrees with its
unclipped polynomial form `rowNumS`, so `∂_iⁿF(x) = n! [tⁿ] linePoly` and
`∂_i⁴∂_k⁴F(x) = 576 [t⁴s⁴] planePoly`. Grade 1 uses the exact expansion of `[t⁴]` with the
coefficient majorants `|[tⁿ]ρ₊^mρ₋^{m'}| ≤ binom(2(m+m'), n)(a r_i)ⁿ` and the cancellation
`ρ₊^{p-2}ρ₋^p - ρ₊^{p-1}ρ₋^{p-1} = ρ₊^{p-2}ρ₋^{p-1}(ρ₋ - ρ₊)
≪ (1 + a r_i t)^{4p-4} - (1 + a r_i t)^{4p-6}`,
`[t⁴] ≤ (binom(4p-5,3) + binom(4p-6,3))(a r_i)⁴` (constants `256 p⁵`, `768 p⁴`). Grade 2 uses
majorants only: `u_j ≪ μ_j(1 + a(1+r_i)t)`, `w_j ≪ ν_j(1 + a(1+r_i)t)` (two variables:
`Λ = 1 + a(1+r_i)t + a(1+r_k)s`), so `|[t⁶](u_j²Π)| ≤ μ_j² binom(4p-2, 6) (a(1+r_i))⁶` and
`|[t⁴s⁴](u_j²Π)| ≤ μ_j² binom(4p-2,4)² (a(1+r_i))⁴(a(1+r_k))⁴`, with `μ_j² + μ_jν_j ≤ 2·(marks)`
(constants `8192 p⁷`, `131072 p⁹`).

**Checks.** `A = B = 0`: `F ≡ 0`, all marks vanish. One coordinate, `B = 0`, `A = (α₀)`,
`0 ≤ α₀ < 1`: `F(x) = (p-1) α₀² x² (1 - α₀ x²)^{p-2}`, so `∂⁴F(0) = -24 (p-1)(p-2) α₀³`. At
`x = 0`: `x_0 = z_0 = 0`, `e_00 = α₀/a²`, `r = √α₀/a`, and the grade-1 bound is
`1000 a² (1 + √α₀/a)⁴ p⁴ α₀² ≥ 6000 p⁴ α₀³` (`(1 + y)⁴ ≥ 6y²`), above `24 p² α₀³`.
-/

@[expose] public section

namespace BiluLinial.Tight

namespace SecC

open Matrix
open scoped Nat

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The exact line representation of `F` (see the module docstring). -/
theorem rowNum_line {p : ℕ} (hp : 2 ≤ p) {a : ℝ} (ha : a ≠ 0) {A B : Matrix ι ι ℝ}
    (hA : A.IsSymm) (hB : B.IsSymm) {x : ι → ℝ} (hα : 0 < starAlpha A x)
    (hβ : 0 < starAlpha B x) (i : ι) {t : ℝ}
    (hpl : 0 ≤ 1 + 2 * a * starRow a A x i * t - a ^ 2 * starCore a A x i i * t ^ 2)
    (hmi : 0 ≤ 1 - 2 * a * starRow (-a) B x i * t - a ^ 2 * starCore a B x i i * t ^ 2) :
    rowNum p A B (x + t • Pi.single i 1) =
      a ^ 2 * starAlpha A x ^ p * starAlpha B x ^ p *
        ∑ j, (((p : ℝ) - 1) * (starRow a A x j - a * starCore a A x i j * t) ^ 2 *
              (1 + 2 * a * starRow a A x i * t - a ^ 2 * starCore a A x i i * t ^ 2) ^ (p - 2) *
              (1 - 2 * a * starRow (-a) B x i * t - a ^ 2 * starCore a B x i i * t ^ 2) ^ p -
            p * (starRow a A x j - a * starCore a A x i j * t) *
              (starRow (-a) B x j + a * starCore a B x i j * t) *
              (1 + 2 * a * starRow a A x i * t - a ^ 2 * starCore a A x i i * t ^ 2) ^ (p - 1) *
              (1 - 2 * a * starRow (-a) B x i * t - a ^ 2 * starCore a B x i i * t ^ 2) ^
                (p - 1)) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 2 := ⟨p - 2, by omega⟩
  have hsA : ∀ k l, A k l = A l k := fun k l => by simpa using congrFun (congrFun hA l) k
  have hsB : ∀ k l, B k l = B l k := fun k l => by simpa using congrFun (congrFun hB l) k
  have hα0 := hα.ne'
  have hβ0 := hβ.ne'
  set y := x + t • Pi.single i 1 with hy
  set ρp := 1 + 2 * a * starRow a A x i * t - a ^ 2 * starCore a A x i i * t ^ 2 with hρp
  set ρm := 1 - 2 * a * starRow (-a) B x i * t - a ^ 2 * starCore a B x i i * t ^ 2 with hρm
  have hAy : ∀ j, (A *ᵥ y) j =
      -(a * starAlpha A x) * (starRow a A x j - a * starCore a A x i j * t) := by
    intro j
    rw [hy, mulVec_line]
    unfold starRow starCore
    rw [hsA j i]
    field_simp
    ring
  have hBy : ∀ j, (B *ᵥ y) j =
      a * starAlpha B x * (starRow (-a) B x j + a * starCore a B x i j * t) := by
    intro j
    rw [hy, mulVec_line]
    unfold starRow starCore
    rw [hsB j i]
    field_simp
  have hαy : starAlpha A y = starAlpha A x * ρp := by
    rw [hy, starAlpha_line hA, hρp]
    unfold starRow starCore
    field_simp
    ring
  have hβy : starAlpha B y = starAlpha B x * ρm := by
    rw [hy, starAlpha_line hB, hρm]
    unfold starRow starCore
    field_simp
  have hcA : clipF A y = starAlpha A x * ρp := by
    unfold clipF
    rw [show 1 - qForm A y = starAlpha A y from rfl, hαy]
    exact max_eq_left (mul_nonneg hα.le hpl)
  have hcB : clipF B y = starAlpha B x * ρm := by
    unfold clipF
    rw [show 1 - qForm B y = starAlpha B y from rfl, hβy]
    exact max_eq_left (mul_nonneg hβ.le hmi)
  have hAt : y ᵥ* A = A *ᵥ y := by
    rw [← mulVec_transpose]
    congr 1
  have hqAA : qForm (A * A) y = ∑ j, (A *ᵥ y) j * (A *ᵥ y) j := by
    unfold qForm
    rw [← mulVec_mulVec, dotProduct_mulVec, hAt, dotProduct]
  have hqAB : qForm (A * B) y = ∑ j, (A *ᵥ y) j * (B *ᵥ y) j := by
    unfold qForm
    rw [← mulVec_mulVec, dotProduct_mulVec, hAt, dotProduct]
  unfold rowNum
  rw [hqAA, hqAB, hcA, hcB, show q + 2 - 2 = q by omega, show q + 2 - 1 = q + 1 by omega]
  simp only [hAy, hBy, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  clear_value ρp ρm y
  push_cast
  ring

/-- **T.MARK, grade 1** (one coordinate, `∂_i⁴`). -/
theorem mark_grade_one {p : ℕ} (hp : 8 ≤ p) {a : ℝ} (ha : 0 < a) {A B : Matrix ι ι ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) {x : ι → ℝ} (hα : 0 < starAlpha A x)
    (hβ : 0 < starAlpha B x) (i : ι) :
    |(pderiv i)^[4] (rowNum p A B) x| ≤
      a ^ 2 * starPhi p A B x * a ^ 4 * (1 + starScale a A B x i) ^ 4 * 1000 *
        ((p : ℝ) ^ 5 * |∑ j, starRow a A x j * (starRow a A x j - starRow (-a) B x j)| +
          (p : ℝ) ^ 4 * ∑ j, (starRow a A x j ^ 2 + |starRow a A x j * starCore a A x i j| +
            |starRow a A x j * starCore a B x i j| +
            |starCore a A x i j * starRow (-a) B x j| + starCore a A x i j ^ 2 +
            |starCore a A x i j * starCore a B x i j|)) := by
  have hp2 : 2 ≤ p := by omega
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (by omega : 1 ≤ p)
  have hr0 := starScale_nonneg (a := a) (A := A) (B := B) (x := x) i
  have hMB1 : ((2 * (p - 2 + p) : ℕ) : ℝ) ≤ 4 * p := by
    exact_mod_cast (by omega : 2 * (p - 2 + p) ≤ 4 * p)
  have hMB2 : ((2 * (p - 1 + (p - 1)) : ℕ) : ℝ) ≤ 4 * p := by
    exact_mod_cast (by omega : 2 * (p - 1 + (p - 1)) ≤ 4 * p)
  have hNB : ((4 * p - 6 : ℕ) : ℝ) + 1 ≤ 4 * p := by
    exact_mod_cast (by omega : 4 * p - 6 + 1 ≤ 4 * p)
  have hc := le_refl (a * starScale a A B x i)
  have hP1 := maj_linePi ha.le hA hB hα hβ i hc (p - 2) p
  have hP2 := maj_linePi ha.le hA hB hα hβ i hc (p - 1) (p - 1)
  have hPD := maj_linePi_sub ha.le hA hB hα hβ i hp2
  have h12 : a ^ 2 * |(linePi a A B x i (p - 2) p).coeff 2| ≤
      (4 * p) ^ 2 / 2 * (a ^ 4 * (1 + starScale a A B x i) ^ 4) :=
    scaled_coeff_bound ha.le hr0 hP1 hMB1 (n := 2) (by norm_num) (by norm_num [Nat.factorial])
  have h13 : a * |(linePi a A B x i (p - 2) p).coeff 3| ≤
      (4 * p) ^ 3 / 6 * (a ^ 4 * (1 + starScale a A B x i) ^ 4) := by
    simpa using
      scaled_coeff_bound ha.le hr0 hP1 hMB1 (n := 3) (by norm_num) (by norm_num [Nat.factorial])
  have h22 : a ^ 2 * |(linePi a A B x i (p - 1) (p - 1)).coeff 2| ≤
      (4 * p) ^ 2 / 2 * (a ^ 4 * (1 + starScale a A B x i) ^ 4) :=
    scaled_coeff_bound ha.le hr0 hP2 hMB2 (n := 2) (by norm_num) (by norm_num [Nat.factorial])
  have h23 : a * |(linePi a A B x i (p - 1) (p - 1)).coeff 3| ≤
      (4 * p) ^ 3 / 6 * (a ^ 4 * (1 + starScale a A B x i) ^ 4) := by
    simpa using
      scaled_coeff_bound ha.le hr0 hP2 hMB2 (n := 3) (by norm_num) (by norm_num [Nat.factorial])
  have h24 : |(linePi a A B x i (p - 1) (p - 1)).coeff 4| ≤
      (4 * p) ^ 4 / 24 * (a ^ 4 * (1 + starScale a A B x i) ^ 4) := by
    simpa using
      scaled_coeff_bound ha.le hr0 hP2 hMB2 (n := 4) (by norm_num) (by norm_num [Nat.factorial])
  have hD : |(linePi a A B x i (p - 2) p).coeff 4 - (linePi a A B x i (p - 1) (p - 1)).coeff 4| ≤
      2 * (4 * p) ^ 3 / 6 * (a ^ 4 * (1 + starScale a A B x i) ^ 4) := by
    rw [← Polynomial.coeff_sub]
    exact diff_coeff_bound hr0 hPD hNB
  rw [iterate_pderiv_rowNum hp2 ha.ne' (isSymm_of_posSemidef hA) (isSymm_of_posSemidef hB) hα hβ
    i 4, coeff_linePoly, show ((4 ! : ℕ) : ℝ) = 24 by norm_num [Nat.factorial]]
  refine (grade_one_real Finset.univ (p := (p : ℝ)) (a := a)
    (K := a ^ 4 * (1 + starScale a A B x i) ^ 4)
    (Φ := a ^ 2 * starAlpha A x ^ p * starAlpha B x ^ p) hp1 ha.le (by positivity)
    (by positivity) h12 h13 h22 h23 h24 hD (starRow a A x) (starRow (-a) B x) (starCore a A x i)
    (starCore a B x i)
    (fun j => (lineU1 a A x i j * lineU1 a A x i j * linePi a A B x i (p - 2) p).coeff 4)
    (fun j => (lineU1 a A x i j * lineW1 a B x i j * linePi a A B x i (p - 1) (p - 1)).coeff 4)
    (fun j => coeff_lin_mul_lin_mul _ _ _ _ _ 2)
    (fun j => coeff_lin_mul_lin_mul _ _ _ _ _ 2)).trans_eq ?_
  rw [starPhi_eq hα hβ]
  ring

/-- **T.MARK, grade 2, one coordinate** (`∂_i⁶`). -/
theorem mark_grade_two_diag {p : ℕ} (hp : 8 ≤ p) {a : ℝ} (ha : 0 < a) {A B : Matrix ι ι ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) {x : ι → ℝ} (hα : 0 < starAlpha A x)
    (hβ : 0 < starAlpha B x) (i : ι) :
    |(pderiv i)^[6] (rowNum p A B) x| ≤
      a ^ 2 * starPhi p A B x * a ^ 6 * (1 + starScale a A B x i) ^ 6 * 10 ^ 6 * (p : ℝ) ^ 9 *
        ∑ j, (starRow a A x j ^ 2 + |starRow a A x j * starRow (-a) B x j| +
          |starRow a A x j * starCore a A x i j| + |starRow a A x j * starCore a B x i j| +
          |starCore a A x i j * starRow (-a) B x j| + starCore a A x i j ^ 2 +
          |starCore a A x i j * starCore a B x i j|) := by
  have hp2 : 2 ≤ p := by omega
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (by omega : 1 ≤ p)
  have hr0 := starScale_nonneg (a := a) (A := A) (B := B) (x := x) i
  have hc' : a ≤ a * (1 + starScale a A B x i) := by nlinarith
  have hcr : a * starScale a A B x i ≤ a * (1 + starScale a A B x i) := by nlinarith
  have hc0 : 0 ≤ a * (1 + starScale a A B x i) := by positivity
  have e6 : ((6 ! : ℕ) : ℝ) = 720 := by norm_num [Nat.factorial]
  have hMB1 : ((2 * (p - 2 + p) + 2 : ℕ) : ℝ) ≤ 4 * p := by
    exact_mod_cast (by omega : 2 * (p - 2 + p) + 2 ≤ 4 * p)
  have hMB2 : ((2 * (p - 1 + (p - 1)) + 2 : ℕ) : ℝ) ≤ 4 * p := by
    exact_mod_cast (by omega : 2 * (p - 1 + (p - 1)) + 2 ≤ 4 * p)
  have hU : ∀ j, |(lineU1 a A x i j * lineU1 a A x i j * linePi a A B x i (p - 2) p).coeff 6| ≤
      (|starRow a A x j| + |starCore a A x i j|) * (|starRow a A x j| + |starCore a A x i j|) *
        ((4 * p) ^ 6 / 720 * (a * (1 + starScale a A B x i)) ^ 6) := by
    intro j
    have h := isMaj1.mul (isMaj1.mul (maj_lineU1 ha.le A x i j hc') (maj_lineU1 ha.le A x i j hc'))
      (maj_linePi ha.le hA hB hα hβ i hcr (p - 2) p)
    have h1 := abs_coeff_le_of_maj1 h 6
    rw [coeff_lin_prod] at h1
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    have := choose_mul_pow_le (n := 6) hc0 hMB1
    rwa [e6] at this
  have hW : ∀ j,
      |(lineU1 a A x i j * lineW1 a B x i j * linePi a A B x i (p - 1) (p - 1)).coeff 6| ≤
      (|starRow a A x j| + |starCore a A x i j|) * (|starRow (-a) B x j| + |starCore a B x i j|) *
        ((4 * p) ^ 6 / 720 * (a * (1 + starScale a A B x i)) ^ 6) := by
    intro j
    have h := isMaj1.mul (isMaj1.mul (maj_lineU1 ha.le A x i j hc') (maj_lineW1 ha.le B x i j hc'))
      (maj_linePi ha.le hA hB hα hβ i hcr (p - 1) (p - 1))
    have h1 := abs_coeff_le_of_maj1 h 6
    rw [coeff_lin_prod] at h1
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    have := choose_mul_pow_le (n := 6) hc0 hMB2
    rwa [e6] at this
  have hNB : 720 * (2 * (p : ℝ) * ((4 * p) ^ 6 / 720 * (a * (1 + starScale a A B x i)) ^ 6)) ≤
      a ^ 6 * (1 + starScale a A B x i) ^ 6 * 10 ^ 6 * (p : ℝ) ^ 9 := by
    have hQ : 0 ≤ a ^ 6 * (1 + starScale a A B x i) ^ 6 := by positivity
    have hp79 : (p : ℝ) ^ 7 ≤ (p : ℝ) ^ 9 := pow_le_pow_right₀ hp1 (by norm_num)
    have h9 : 8192 * (p : ℝ) ^ 7 ≤ 10 ^ 6 * (p : ℝ) ^ 9 := by
      nlinarith [pow_nonneg (by positivity : (0 : ℝ) ≤ p) 9]
    calc 720 * (2 * (p : ℝ) * ((4 * p) ^ 6 / 720 * (a * (1 + starScale a A B x i)) ^ 6)) =
          8192 * (p : ℝ) ^ 7 * (a ^ 6 * (1 + starScale a A B x i) ^ 6) := by ring
      _ ≤ 10 ^ 6 * (p : ℝ) ^ 9 * (a ^ 6 * (1 + starScale a A B x i) ^ 6) :=
          mul_le_mul_of_nonneg_right h9 hQ
      _ = _ := by ring
  rw [iterate_pderiv_rowNum hp2 ha.ne' (isSymm_of_posSemidef hA) (isSymm_of_posSemidef hB) hα hβ
    i 6, coeff_linePoly, e6]
  refine (grade_two_real Finset.univ (p := (p : ℝ))
    (Φ := a ^ 2 * starAlpha A x ^ p * starAlpha B x ^ p) hp1 (by positivity) (by positivity)
    (by norm_num) hNB
    (fun j => |starRow a A x j| + |starCore a A x i j|)
    (fun j => |starRow (-a) B x j| + |starCore a B x i j|)
    (fun j => (lineU1 a A x i j * lineU1 a A x i j * linePi a A B x i (p - 2) p).coeff 6)
    (fun j => (lineU1 a A x i j * lineW1 a B x i j * linePi a A B x i (p - 1) (p - 1)).coeff 6)
    (fun j => starRow a A x j ^ 2 + |starRow a A x j * starRow (-a) B x j| +
      |starRow a A x j * starCore a A x i j| + |starRow a A x j * starCore a B x i j| +
      |starCore a A x i j * starRow (-a) B x j| + starCore a A x i j ^ 2 +
      |starCore a A x i j * starCore a B x i j|)
    hU hW (fun j => one_marks_le _ _ _ _) (fun j => by positivity)).trans_eq ?_
  rw [starPhi_eq hα hβ]
  ring

/-- **T.MARK, grade 2, two coordinates** (`∂_i⁴ ∂_k⁴`, `i ≠ k`), with the combined core marks
`ē_j = |e_ij| + |e_kj|`, `f̄_j = |f_ij| + |f_kj|`. -/
theorem mark_grade_two_mixed {p : ℕ} (hp : 8 ≤ p) {a : ℝ} (ha : 0 < a) {A B : Matrix ι ι ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) {x : ι → ℝ} (hα : 0 < starAlpha A x)
    (hβ : 0 < starAlpha B x) {i k : ι} (hik : i ≠ k) :
    |(pderiv i)^[4] ((pderiv k)^[4] (rowNum p A B)) x| ≤
      a ^ 2 * starPhi p A B x * a ^ 8 * (1 + starScale a A B x i) ^ 4 *
        (1 + starScale a A B x k) ^ 4 * 10 ^ 6 * (p : ℝ) ^ 9 *
        ∑ j, (starRow a A x j ^ 2 + |starRow a A x j * starRow (-a) B x j| +
          |starRow a A x j| * (|starCore a A x i j| + |starCore a A x k j|) +
          |starRow a A x j| * (|starCore a B x i j| + |starCore a B x k j|) +
          (|starCore a A x i j| + |starCore a A x k j|) * |starRow (-a) B x j| +
          (|starCore a A x i j| + |starCore a A x k j|) ^ 2 +
          (|starCore a A x i j| + |starCore a A x k j|) *
            (|starCore a B x i j| + |starCore a B x k j|)) := by
  have hp2 : 2 ≤ p := by omega
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (by omega : 1 ≤ p)
  have hri := starScale_nonneg (a := a) (A := A) (B := B) (x := x) i
  have hrk := starScale_nonneg (a := a) (A := A) (B := B) (x := x) k
  have hc₁ : a ≤ a * (1 + starScale a A B x i) := by nlinarith
  have hc₂ : a ≤ a * (1 + starScale a A B x k) := by nlinarith
  have hMB1 : ((2 * (p - 2 + p) + 2 : ℕ) : ℝ) ≤ 4 * p := by
    exact_mod_cast (by omega : 2 * (p - 2 + p) + 2 ≤ 4 * p)
  have hMB2 : ((2 * (p - 1 + (p - 1)) + 2 : ℕ) : ℝ) ≤ 4 * p := by
    exact_mod_cast (by omega : 2 * (p - 1 + (p - 1)) + 2 ≤ 4 * p)
  have hU : ∀ j, |coeff2 (planeU2 a A x i k j * planeU2 a A x i k j *
      planePi a A B x i k (p - 2) p) 4 4| ≤
      (|starRow a A x j| + (|starCore a A x i j| + |starCore a A x k j|)) *
        (|starRow a A x j| + (|starCore a A x i j| + |starCore a A x k j|)) *
        ((4 * p) ^ 8 / 576 *
          ((a * (1 + starScale a A B x i)) ^ 4 * (a * (1 + starScale a A B x k)) ^ 4)) := by
    intro j
    have h := isMaj2.mul (isMaj2.mul (maj_planeU2 ha.le A x i k j hc₁ hc₂)
      (maj_planeU2 ha.le A x i k j hc₁ hc₂)) (maj_planePi ha.le hA hB hα hβ i k (p - 2) p)
    have h1 := abs_coeff2_le_of_maj2 h 4 4
    rw [coeff2_lamP_prod] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left (choose44_le hMB1) (by positivity))
  have hW : ∀ j, |coeff2 (planeU2 a A x i k j * planeW2 a B x i k j *
      planePi a A B x i k (p - 1) (p - 1)) 4 4| ≤
      (|starRow a A x j| + (|starCore a A x i j| + |starCore a A x k j|)) *
        (|starRow (-a) B x j| + (|starCore a B x i j| + |starCore a B x k j|)) *
        ((4 * p) ^ 8 / 576 *
          ((a * (1 + starScale a A B x i)) ^ 4 * (a * (1 + starScale a A B x k)) ^ 4)) := by
    intro j
    have h := isMaj2.mul (isMaj2.mul (maj_planeU2 ha.le A x i k j hc₁ hc₂)
      (maj_planeW2 ha.le B x i k j hc₁ hc₂)) (maj_planePi ha.le hA hB hα hβ i k (p - 1) (p - 1))
    have h1 := abs_coeff2_le_of_maj2 h 4 4
    rw [coeff2_lamP_prod] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left (choose44_le hMB2) (by positivity))
  have hNB : 576 * (2 * (p : ℝ) * ((4 * p) ^ 8 / 576 *
      ((a * (1 + starScale a A B x i)) ^ 4 * (a * (1 + starScale a A B x k)) ^ 4))) ≤
      a ^ 8 * (1 + starScale a A B x i) ^ 4 * (1 + starScale a A B x k) ^ 4 * 10 ^ 6 *
        (p : ℝ) ^ 9 := by
    have hQ : 0 ≤ a ^ 8 * (1 + starScale a A B x i) ^ 4 * (1 + starScale a A B x k) ^ 4 := by
      positivity
    have h9 : 131072 * (p : ℝ) ^ 9 ≤ 10 ^ 6 * (p : ℝ) ^ 9 := by
      nlinarith [pow_nonneg (by positivity : (0 : ℝ) ≤ p) 9]
    calc 576 * (2 * (p : ℝ) * ((4 * p) ^ 8 / 576 *
          ((a * (1 + starScale a A B x i)) ^ 4 * (a * (1 + starScale a A B x k)) ^ 4))) =
          131072 * (p : ℝ) ^ 9 *
            (a ^ 8 * (1 + starScale a A B x i) ^ 4 * (1 + starScale a A B x k) ^ 4) := by ring
      _ ≤ 10 ^ 6 * (p : ℝ) ^ 9 *
            (a ^ 8 * (1 + starScale a A B x i) ^ 4 * (1 + starScale a A B x k) ^ 4) :=
          mul_le_mul_of_nonneg_right h9 hQ
      _ = _ := by ring
  rw [mixed_pderiv_rowNum hp2 ha.ne' (isSymm_of_posSemidef hA) (isSymm_of_posSemidef hB) hα hβ
    i k, coeff2_planePoly]
  refine (grade_two_real Finset.univ (p := (p : ℝ))
    (Φ := a ^ 2 * starAlpha A x ^ p * starAlpha B x ^ p) hp1 (by positivity) (by positivity)
    (by norm_num) hNB
    (fun j => |starRow a A x j| + (|starCore a A x i j| + |starCore a A x k j|))
    (fun j => |starRow (-a) B x j| + (|starCore a B x i j| + |starCore a B x k j|))
    (fun j => coeff2 (planeU2 a A x i k j * planeU2 a A x i k j *
      planePi a A B x i k (p - 2) p) 4 4)
    (fun j => coeff2 (planeU2 a A x i k j * planeW2 a B x i k j *
      planePi a A B x i k (p - 1) (p - 1)) 4 4)
    (fun j => starRow a A x j ^ 2 + |starRow a A x j * starRow (-a) B x j| +
      |starRow a A x j| * (|starCore a A x i j| + |starCore a A x k j|) +
      |starRow a A x j| * (|starCore a B x i j| + |starCore a B x k j|) +
      (|starCore a A x i j| + |starCore a A x k j|) * |starRow (-a) B x j| +
      (|starCore a A x i j| + |starCore a A x k j|) ^ 2 +
      (|starCore a A x i j| + |starCore a A x k j|) *
        (|starCore a B x i j| + |starCore a B x k j|))
    hU hW (fun j => two_marks_le _ _ _ _ _ _) (fun j => by positivity)).trans_eq ?_
  rw [starPhi_eq hα hβ]
  ring

end SecC

end BiluLinial.Tight
