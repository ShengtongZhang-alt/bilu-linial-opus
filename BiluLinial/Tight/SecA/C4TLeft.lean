/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecA.C4TRight

/-!
# The left observable of (C4) (sub-node `A-C4T-T0` of `A-C4T`)

Source lines 509–534; AUDIT-A §2.13 (gap A7). `F₀ = (tr M - q_M) Φ = clipObs (tr M - q_M) p p`.
`A-TRANS` (`clip_trans_abs`: sup and endpoint scale `1 + tr A`) leaves the grade-one term
`(1/12) Σ_i E[∂_i⁴F₀(ξ)/Φ(ξ)]`, bounded here by `A-EPB4` (`iter_pderiv_clipObs_le`):
`|∂_i⁴F₀(ξ)|/Φ(ξ) ≤ 4! [t⁴](m₀ + m₁t + m₂t²)(1 + b₊t + c₊t²)^p(1 + b₋t + c₋t²)^p` with
`b_± = 2a|G^±_vi|`, `c_± = a²(G^±_vvG^±_ii - (G^±_vi)²)` (F1), `m₀ = 1 + tr A`, `m₁ = 2|(Mξ)_i|`,
`m₂ = A_ii`.

* `coeff_pow_bound`: for `f = 1 + bX + cX² (+ O(X⁵))`, `b, c ≥ 0`, the coefficients `k ≤ 4` of `fⁿ`
  are `≥ 0` and `≤ E_k(nb, nc)`, `E = (1, S, V + S², SV + S³, V² + S²V + S⁴)`.
* `coeff_four_le`: `[t⁴](m₀ + m₁t + m₂t²) f₊^p f₋^p ≤ m₀(3V² + 6S²V + 5S⁴) + m₁(4SV + 4S³) +
  m₂(2V + 3S²)` with `S = p(b₊ + b₋)`, `V = p(c₊ + c₋)` (checked numerically, 20000 instances).
-/

@[expose] public section

universe u

namespace BiluLinial.Tight

open Matrix Polynomial

namespace SecA.C4

theorem coeff_mul_one_eq' (f g : ℝ[X]) :
    (f * g).coeff 1 = f.coeff 0 * g.coeff 1 + f.coeff 1 * g.coeff 0 := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ]

theorem coeff_mul_two_eq' (f g : ℝ[X]) :
    (f * g).coeff 2 = f.coeff 0 * g.coeff 2 + f.coeff 1 * g.coeff 1 + f.coeff 2 * g.coeff 0 := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ]

theorem coeff_mul_three_eq' (f g : ℝ[X]) :
    (f * g).coeff 3 = f.coeff 0 * g.coeff 3 + f.coeff 1 * g.coeff 2 + f.coeff 2 * g.coeff 1 +
      f.coeff 3 * g.coeff 0 := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ]

theorem coeff_mul_four_eq' (f g : ℝ[X]) :
    (f * g).coeff 4 = f.coeff 0 * g.coeff 4 + f.coeff 1 * g.coeff 3 + f.coeff 2 * g.coeff 2 +
      f.coeff 3 * g.coeff 1 + f.coeff 4 * g.coeff 0 := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ]

/-- Coefficient bounds for powers of `1 + bX + cX²` (`b, c ≥ 0`), degrees `≤ 4`. -/
theorem coeff_pow_bound {f : ℝ[X]} {b c : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) (h0 : f.coeff 0 = 1)
    (h1 : f.coeff 1 = b) (h2 : f.coeff 2 = c) (h3 : f.coeff 3 = 0) (h4 : f.coeff 4 = 0)
    (n : ℕ) :
    (f ^ n).coeff 0 = 1 ∧
      (0 ≤ (f ^ n).coeff 1 ∧ (f ^ n).coeff 1 ≤ n * b) ∧
      (0 ≤ (f ^ n).coeff 2 ∧ (f ^ n).coeff 2 ≤ n * c + (n * b) ^ 2) ∧
      (0 ≤ (f ^ n).coeff 3 ∧ (f ^ n).coeff 3 ≤ (n * b) * (n * c) + (n * b) ^ 3) ∧
      (0 ≤ (f ^ n).coeff 4 ∧
        (f ^ n).coeff 4 ≤ (n * c) ^ 2 + (n * b) ^ 2 * (n * c) + (n * b) ^ 4) := by
  induction n with
  | zero => simp [coeff_one]
  | succ n ih =>
    obtain ⟨e0, ⟨a1, b1⟩, ⟨a2, b2⟩, ⟨a3, b3⟩, ⟨a4, b4⟩⟩ := ih
    rw [pow_succ, mul_coeff_zero, coeff_mul_one_eq', coeff_mul_two_eq', coeff_mul_three_eq',
      coeff_mul_four_eq', e0, h0, h1, h2, h3, h4]
    push_cast
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    refine ⟨by ring, ⟨by nlinarith, by nlinarith⟩, ⟨by nlinarith, ?_⟩, ⟨by nlinarith, ?_⟩,
      ⟨by nlinarith, ?_⟩⟩
    · have key : ((n + 1) * c + ((n + 1) * b) ^ 2) - (n * c + (n * b) ^ 2 + b * (n * b) + c) =
          (n + 1) * b ^ 2 := by ring
      have hk : 0 ≤ (n + 1) * b ^ 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left b1 hb]
    · have key : ((n + 1) * b * ((n + 1) * c) + ((n + 1) * b) ^ 3) -
          ((n * b) * (n * c) + (n * b) ^ 3 + b * (n * c + (n * b) ^ 2) + c * (n * b)) =
          b * c + (2 * n ^ 2 + 3 * n + 1) * b ^ 3 := by ring
      have hk : 0 ≤ b * c + (2 * n ^ 2 + 3 * n + 1) * b ^ 3 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left b2 hb, mul_le_mul_of_nonneg_left b1 hc]
    · have key : (((n + 1) * c) ^ 2 + ((n + 1) * b) ^ 2 * ((n + 1) * c) + ((n + 1) * b) ^ 4) -
          ((n * c) ^ 2 + (n * b) ^ 2 * (n * c) + (n * b) ^ 4 +
            b * ((n * b) * (n * c) + (n * b) ^ 3) + c * (n * c + (n * b) ^ 2)) =
          (n + 1) * c ^ 2 + (n ^ 2 + 3 * n + 1) * b ^ 2 * c +
            (3 * n ^ 3 + 6 * n ^ 2 + 4 * n + 1) * b ^ 4 := by ring
      have hk : 0 ≤ (n + 1) * c ^ 2 + (n ^ 2 + 3 * n + 1) * b ^ 2 * c +
          (3 * n ^ 3 + 6 * n ^ 2 + 4 * n + 1) * b ^ 4 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left b3 hb, mul_le_mul_of_nonneg_left b2 hc]

/-- The coefficients of `1 + C b X + C c X²`. -/
theorem quadPoly_coeff (b c : ℝ) :
    (1 + C b * X + C c * X ^ 2 : ℝ[X]).coeff 0 = 1 ∧
      (1 + C b * X + C c * X ^ 2 : ℝ[X]).coeff 1 = b ∧
      (1 + C b * X + C c * X ^ 2 : ℝ[X]).coeff 2 = c ∧
      (1 + C b * X + C c * X ^ 2 : ℝ[X]).coeff 3 = 0 ∧
      (1 + C b * X + C c * X ^ 2 : ℝ[X]).coeff 4 = 0 := by
  simp only [coeff_add, coeff_one, coeff_C_mul, coeff_X, coeff_X_pow]
  norm_num

/-- The coefficients of `C m₀ + C m₁ X + C m₂ X²`. -/
theorem linPoly_coeff (m₀ m₁ m₂ : ℝ) :
    (C m₀ + C m₁ * X + C m₂ * X ^ 2 : ℝ[X]).coeff 0 = m₀ ∧
      (C m₀ + C m₁ * X + C m₂ * X ^ 2 : ℝ[X]).coeff 1 = m₁ ∧
      (C m₀ + C m₁ * X + C m₂ * X ^ 2 : ℝ[X]).coeff 2 = m₂ ∧
      (C m₀ + C m₁ * X + C m₂ * X ^ 2 : ℝ[X]).coeff 3 = 0 ∧
      (C m₀ + C m₁ * X + C m₂ * X ^ 2 : ℝ[X]).coeff 4 = 0 := by
  simp only [coeff_add, coeff_C, coeff_C_mul, coeff_X, coeff_X_pow]
  norm_num

/-- `E_k` is monotone: the bounds of `coeff_pow_bound` at `(S', V') ≤ (S, V)`. -/
theorem E_mono {S V S' V' : ℝ} (hS' : 0 ≤ S') (hV' : 0 ≤ V') (hS : S' ≤ S) (hV : V' ≤ V) :
    S' ≤ S ∧ V' + S' ^ 2 ≤ V + S ^ 2 ∧ S' * V' + S' ^ 3 ≤ S * V + S ^ 3 ∧
      V' ^ 2 + S' ^ 2 * V' + S' ^ 4 ≤ V ^ 2 + S ^ 2 * V + S ^ 4 := by
  have hS0 : 0 ≤ S := hS'.trans hS
  refine ⟨hS, ?_, ?_, ?_⟩ <;> gcongr

/-- The coefficient of degree four of a triple product. -/
theorem coeff_four_prod (g P Q : ℝ[X]) : ((g * P) * Q).coeff 4 =
    g.coeff 0 * (P.coeff 0 * Q.coeff 4 + P.coeff 1 * Q.coeff 3 + P.coeff 2 * Q.coeff 2 +
        P.coeff 3 * Q.coeff 1 + P.coeff 4 * Q.coeff 0) +
      g.coeff 1 * (P.coeff 0 * Q.coeff 3 + P.coeff 1 * Q.coeff 2 + P.coeff 2 * Q.coeff 1 +
        P.coeff 3 * Q.coeff 0) +
      g.coeff 2 * (P.coeff 0 * Q.coeff 2 + P.coeff 1 * Q.coeff 1 + P.coeff 2 * Q.coeff 0) +
      g.coeff 3 * (P.coeff 0 * Q.coeff 1 + P.coeff 1 * Q.coeff 0) +
      g.coeff 4 * (P.coeff 0 * Q.coeff 0) := by
  rw [coeff_mul_four_eq', mul_coeff_zero, coeff_mul_one_eq', coeff_mul_two_eq',
    coeff_mul_three_eq', coeff_mul_four_eq']
  ring

/-- The abstract form of `coeff_four_le`. -/
theorem coeff_four_le_of {g P Q : ℝ[X]} {m₀ m₁ m₂ S V : ℝ} (hm₀ : 0 ≤ m₀) (hm₁ : 0 ≤ m₁)
    (hm₂ : 0 ≤ m₂) (hS0 : 0 ≤ S) (hV0 : 0 ≤ V)
    (g0 : g.coeff 0 = m₀) (g1 : g.coeff 1 = m₁) (g2 : g.coeff 2 = m₂) (g3 : g.coeff 3 = 0)
    (g4 : g.coeff 4 = 0) (A0 : P.coeff 0 = 1) (B0 : Q.coeff 0 = 1)
    (A1l : 0 ≤ P.coeff 1) (A2l : 0 ≤ P.coeff 2) (A3l : 0 ≤ P.coeff 3)
    (B1l : 0 ≤ Q.coeff 1) (B2l : 0 ≤ Q.coeff 2) (B3l : 0 ≤ Q.coeff 3)
    (a1 : P.coeff 1 ≤ S) (a2 : P.coeff 2 ≤ V + S ^ 2) (a3 : P.coeff 3 ≤ S * V + S ^ 3)
    (a4 : P.coeff 4 ≤ V ^ 2 + S ^ 2 * V + S ^ 4)
    (c1 : Q.coeff 1 ≤ S) (c2 : Q.coeff 2 ≤ V + S ^ 2) (c3 : Q.coeff 3 ≤ S * V + S ^ 3)
    (c4 : Q.coeff 4 ≤ V ^ 2 + S ^ 2 * V + S ^ 4) :
    ((g * P) * Q).coeff 4 ≤ m₀ * (3 * V ^ 2 + 6 * S ^ 2 * V + 5 * S ^ 4) +
      m₁ * (4 * S * V + 4 * S ^ 3) + m₂ * (2 * V + 3 * S ^ 2) := by
  rw [coeff_four_prod, g0, g1, g2, g3, g4, A0, B0]
  have P2 : Q.coeff 2 + P.coeff 1 * Q.coeff 1 + P.coeff 2 ≤ 2 * V + 3 * S ^ 2 := by
    have := mul_le_mul a1 c1 B1l hS0
    linarith
  have P3 : Q.coeff 3 + P.coeff 1 * Q.coeff 2 + P.coeff 2 * Q.coeff 1 + P.coeff 3 ≤
      4 * S * V + 4 * S ^ 3 := by
    have h1 := mul_le_mul a2 c1 B1l (by positivity)
    have h2 := mul_le_mul a1 c2 B2l hS0
    have e : S * (V + S ^ 2) = S * V + S ^ 3 := by ring
    have e' : (V + S ^ 2) * S = S * V + S ^ 3 := by ring
    linarith
  have P4 : Q.coeff 4 + P.coeff 1 * Q.coeff 3 + P.coeff 2 * Q.coeff 2 + P.coeff 3 * Q.coeff 1 +
      P.coeff 4 ≤ 3 * V ^ 2 + 6 * S ^ 2 * V + 5 * S ^ 4 := by
    have h1 := mul_le_mul a3 c1 B1l (by positivity)
    have h2 := mul_le_mul a2 c2 B2l (by positivity)
    have h3 := mul_le_mul a1 c3 B3l hS0
    have e1 : (S * V + S ^ 3) * S = S ^ 2 * V + S ^ 4 := by ring
    have e2 : (V + S ^ 2) * (V + S ^ 2) = V ^ 2 + 2 * S ^ 2 * V + S ^ 4 := by ring
    have e3 : S * (S * V + S ^ 3) = S ^ 2 * V + S ^ 4 := by ring
    linarith
  have k2 := mul_le_mul_of_nonneg_left P2 hm₂
  have k3 := mul_le_mul_of_nonneg_left P3 hm₁
  have k4 := mul_le_mul_of_nonneg_left P4 hm₀
  have e : m₀ * (1 * Q.coeff 4 + P.coeff 1 * Q.coeff 3 + P.coeff 2 * Q.coeff 2 +
        P.coeff 3 * Q.coeff 1 + P.coeff 4 * 1) +
      m₁ * (1 * Q.coeff 3 + P.coeff 1 * Q.coeff 2 + P.coeff 2 * Q.coeff 1 + P.coeff 3 * 1) +
      m₂ * (1 * Q.coeff 2 + P.coeff 1 * Q.coeff 1 + P.coeff 2 * 1) +
      0 * (1 * Q.coeff 1 + P.coeff 1 * 1) + 0 * (1 * 1) =
      m₀ * (Q.coeff 4 + P.coeff 1 * Q.coeff 3 + P.coeff 2 * Q.coeff 2 + P.coeff 3 * Q.coeff 1 +
        P.coeff 4) +
      m₁ * (Q.coeff 3 + P.coeff 1 * Q.coeff 2 + P.coeff 2 * Q.coeff 1 + P.coeff 3) +
      m₂ * (Q.coeff 2 + P.coeff 1 * Q.coeff 1 + P.coeff 2) := by ring
  rw [e]
  linarith

/-- `A-EPB4` coefficient bound: `[t⁴](m₀ + m₁t + m₂t²)(1 + b₁t + c₁t²)^p(1 + b₂t + c₂t²)^p ≤
m₀(3V² + 6S²V + 5S⁴) + m₁(4SV + 4S³) + m₂(2V + 3S²)`, `S = p(b₁ + b₂)`, `V = p(c₁ + c₂)`. -/
theorem coeff_four_le {m₀ m₁ m₂ b₁ c₁ b₂ c₂ : ℝ} (hm₀ : 0 ≤ m₀) (hm₁ : 0 ≤ m₁) (hm₂ : 0 ≤ m₂)
    (hb₁ : 0 ≤ b₁) (hc₁ : 0 ≤ c₁) (hb₂ : 0 ≤ b₂) (hc₂ : 0 ≤ c₂) (p : ℕ) :
    ((C m₀ + C m₁ * X + C m₂ * X ^ 2) * (1 + C b₁ * X + C c₁ * X ^ 2) ^ p *
        (1 + C b₂ * X + C c₂ * X ^ 2) ^ p).coeff 4 ≤
      m₀ * (3 * ((p : ℝ) * (c₁ + c₂)) ^ 2 +
          6 * ((p : ℝ) * (b₁ + b₂)) ^ 2 * ((p : ℝ) * (c₁ + c₂)) +
          5 * ((p : ℝ) * (b₁ + b₂)) ^ 4) +
        m₁ * (4 * ((p : ℝ) * (b₁ + b₂)) * ((p : ℝ) * (c₁ + c₂)) +
          4 * ((p : ℝ) * (b₁ + b₂)) ^ 3) +
        m₂ * (2 * ((p : ℝ) * (c₁ + c₂)) + 3 * ((p : ℝ) * (b₁ + b₂)) ^ 2) := by
  obtain ⟨g0, g1, g2, g3, g4⟩ := linPoly_coeff m₀ m₁ m₂
  obtain ⟨f0, f1, f2, f3, f4⟩ := quadPoly_coeff b₁ c₁
  obtain ⟨k0, k1, k2, k3, k4⟩ := quadPoly_coeff b₂ c₂
  obtain ⟨A0, ⟨A1l, A1⟩, ⟨A2l, A2⟩, ⟨A3l, A3⟩, ⟨-, A4⟩⟩ :=
    coeff_pow_bound hb₁ hc₁ f0 f1 f2 f3 f4 p
  obtain ⟨B0, ⟨B1l, B1⟩, ⟨B2l, B2⟩, ⟨B3l, B3⟩, ⟨-, B4⟩⟩ :=
    coeff_pow_bound hb₂ hc₂ k0 k1 k2 k3 k4 p
  have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  obtain ⟨e1, e2, e3, e4⟩ := E_mono (S := (p : ℝ) * (b₁ + b₂)) (V := (p : ℝ) * (c₁ + c₂))
    (mul_nonneg hp hb₁) (mul_nonneg hp hc₁)
    (mul_le_mul_of_nonneg_left (by linarith) hp) (mul_le_mul_of_nonneg_left (by linarith) hp)
  obtain ⟨e1', e2', e3', e4'⟩ := E_mono (S := (p : ℝ) * (b₁ + b₂)) (V := (p : ℝ) * (c₁ + c₂))
    (mul_nonneg hp hb₂) (mul_nonneg hp hc₂)
    (mul_le_mul_of_nonneg_left (by linarith) hp) (mul_le_mul_of_nonneg_left (by linarith) hp)
  exact coeff_four_le_of hm₀ hm₁ hm₂ (by positivity) (by positivity) g0 g1 g2 g3 g4 A0 B0
    A1l A2l A3l B1l B2l B3l (A1.trans e1) (A2.trans e2) (A3.trans e3) (A4.trans e4)
    (B1.trans e1') (B2.trans e2') (B3.trans e3') (B4.trans e4')

/-- The scalar step of the grade-one bound: with `0 ≤ V ≤ Pu`, `S² ≤ 8P²r`, `r ≤ u`, `m₁² ≤ 4u`,
`m₂ ≤ u`, `P ≥ 1`, the coefficient bound is `≤ (1 + m₀)(10P²u² + 368P⁴ru)`. -/
theorem scalar_g1 {m₀ m₁ m₂ S V r u P : ℝ} (hP : 1 ≤ P) (hm₀ : 0 ≤ m₀) (hm₁ : 0 ≤ m₁)
    (hm₂ : 0 ≤ m₂) (hS : 0 ≤ S) (hV : 0 ≤ V) (hr : 0 ≤ r) (hVu : V ≤ P * u)
    (hS2 : S ^ 2 ≤ 8 * P ^ 2 * r) (hru : r ≤ u) (hm₁u : m₁ ^ 2 ≤ 4 * u) (hm₂u : m₂ ≤ u) :
    m₀ * (3 * V ^ 2 + 6 * S ^ 2 * V + 5 * S ^ 4) + m₁ * (4 * S * V + 4 * S ^ 3) +
        m₂ * (2 * V + 3 * S ^ 2) ≤
      (1 + m₀) * (10 * P ^ 2 * u ^ 2 + 368 * P ^ 4 * r * u) := by
  have hu : 0 ≤ u := hr.trans hru
  have hP0 : 0 ≤ P := by linarith
  have hP2 : P ≤ P ^ 2 := by nlinarith
  have hP3 : P ^ 2 ≤ P ^ 3 := by nlinarith
  have hP4 : P ^ 3 ≤ P ^ 4 := by nlinarith
  have hS2u : S ^ 2 ≤ 8 * P ^ 2 * u :=
    hS2.trans (mul_le_mul_of_nonneg_left hru (by positivity))
  have hru0 : 0 ≤ r * u := mul_nonneg hr hu
  have hPu : 0 ≤ P * u := mul_nonneg hP0 hu
  have t1 : V ^ 2 ≤ P ^ 2 * u ^ 2 := by
    have h := mul_le_mul hVu hVu hV hPu
    have e1 : V ^ 2 = V * V := sq V
    have e2 : P ^ 2 * u ^ 2 = P * u * (P * u) := by ring
    linarith
  have t2 : S ^ 2 * V ≤ 8 * P ^ 3 * (r * u) := by
    have h := mul_le_mul hS2 hVu hV (by positivity)
    have e : 8 * P ^ 2 * r * (P * u) = 8 * P ^ 3 * (r * u) := by ring
    linarith
  have t3 : S ^ 4 ≤ 64 * P ^ 4 * (r * u) := by
    have h := mul_le_mul hS2 hS2u (sq_nonneg S) (by positivity)
    have e1 : S ^ 4 = S ^ 2 * S ^ 2 := by ring
    have e2 : 8 * P ^ 2 * r * (8 * P ^ 2 * u) = 64 * P ^ 4 * (r * u) := by ring
    linarith
  have hP34 : P ^ 3 * (r * u) ≤ P ^ 4 * (r * u) := mul_le_mul_of_nonneg_right hP4 hru0
  have hm0part : m₀ * (3 * V ^ 2 + 6 * S ^ 2 * V + 5 * S ^ 4) ≤
      m₀ * (10 * P ^ 2 * u ^ 2 + 368 * P ^ 4 * (r * u)) := by
    refine mul_le_mul_of_nonneg_left ?_ hm₀
    have : 0 ≤ P ^ 2 * u ^ 2 := by positivity
    linarith
  have t4 : m₁ * S ≤ (m₁ ^ 2 + S ^ 2) / 2 := by
    have h := sq_nonneg (m₁ - S)
    have e : (m₁ - S) ^ 2 = m₁ ^ 2 - 2 * (m₁ * S) + S ^ 2 := by ring
    linarith
  have hmS : 0 ≤ m₁ * S := mul_nonneg hm₁ hS
  have t5 : m₁ * (4 * S * V) ≤ 8 * P * u ^ 2 + 16 * P ^ 3 * (r * u) := by
    have h2 : m₁ * S ≤ (4 * u + 8 * P ^ 2 * r) / 2 := t4.trans (by linarith)
    have h3 := mul_le_mul_of_nonneg_left h2 (show 0 ≤ 4 * (P * u) by positivity)
    have h4 : 4 * V * (m₁ * S) ≤ 4 * (P * u) * (m₁ * S) :=
      mul_le_mul_of_nonneg_right (by linarith) hmS
    have e1 : 4 * (P * u) * ((4 * u + 8 * P ^ 2 * r) / 2) = 8 * P * u ^ 2 + 16 * P ^ 3 * (r * u) := by
      ring
    have e2 : m₁ * (4 * S * V) = 4 * V * (m₁ * S) := by ring
    linarith
  have t6 : m₁ * (4 * S ^ 3) ≤ 64 * P ^ 2 * (r * u) + 128 * P ^ 4 * (r * u) := by
    have h1 : (m₁ * S) * S ^ 2 ≤ ((m₁ * S) ^ 2 + (S ^ 2) ^ 2) / 2 := by
      have h := sq_nonneg (m₁ * S - S ^ 2)
      have e : (m₁ * S - S ^ 2) ^ 2 = (m₁ * S) ^ 2 - 2 * ((m₁ * S) * S ^ 2) + (S ^ 2) ^ 2 := by
        ring
      linarith
    have h2 : (m₁ * S) ^ 2 ≤ 32 * P ^ 2 * (r * u) := by
      have h := mul_le_mul hm₁u hS2 (sq_nonneg S) (by linarith)
      have e1 : (m₁ * S) ^ 2 = m₁ ^ 2 * S ^ 2 := by ring
      have e2 : 4 * u * (8 * P ^ 2 * r) = 32 * P ^ 2 * (r * u) := by ring
      linarith
    have h3 : (S ^ 2) ^ 2 ≤ 64 * P ^ 4 * (r * u) := by
      have e : (S ^ 2) ^ 2 = S ^ 4 := by ring
      linarith
    have e : m₁ * (4 * S ^ 3) = 4 * ((m₁ * S) * S ^ 2) := by ring
    linarith
  have t7 : m₂ * (2 * V + 3 * S ^ 2) ≤ 2 * P * u ^ 2 + 24 * P ^ 2 * (r * u) := by
    have h1 : 2 * V + 3 * S ^ 2 ≤ 2 * (P * u) + 24 * P ^ 2 * r := by linarith
    have h2 := mul_le_mul hm₂u h1 (by positivity) hu
    have e : u * (2 * (P * u) + 24 * P ^ 2 * r) = 2 * P * u ^ 2 + 24 * P ^ 2 * (r * u) := by ring
    linarith
  have hPu2 : P * u ^ 2 ≤ P ^ 2 * u ^ 2 := mul_le_mul_of_nonneg_right hP2 (sq_nonneg u)
  have hru2 : P ^ 2 * (r * u) ≤ P ^ 4 * (r * u) :=
    mul_le_mul_of_nonneg_right (hP3.trans hP4) hru0
  have hfin : (1 + m₀) * (10 * P ^ 2 * u ^ 2 + 368 * P ^ 4 * r * u) =
      m₀ * (10 * P ^ 2 * u ^ 2 + 368 * P ^ 4 * (r * u)) +
        (10 * P ^ 2 * u ^ 2 + 368 * P ^ 4 * (r * u)) := by ring
  have hsplit : m₁ * (4 * S * V + 4 * S ^ 3) = m₁ * (4 * S * V) + m₁ * (4 * S ^ 3) := by ring
  have hP4ru : 0 ≤ P ^ 4 * (r * u) := by positivity
  rw [hfin, hsplit]
  linarith

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The majorant condition for `tr M - q_M` with scale `1 + tr A` (`0 ⪯ M ⪯ A`, `q_A(x) ≤ 1`,
weights with `A_ii ≤ λ_i²`). -/
theorem quadMaj_traceM {A M : Matrix ι ι ℝ} (hA : A.PosSemidef) (hM : M.PosSemidef)
    (hAM : (A - M).PosSemidef) {x lam : ι → ℝ} (hq : qForm A x ≤ 1) (hlam : ∀ i, 0 ≤ lam i)
    (hQ : ∀ i, A i i ≤ lam i ^ 2) :
    QuadMaj M.trace 0 (-M) x (1 + A.trace) lam := by
  have hd : ((1 : ℝ) • A - M).PosSemidef := by rwa [one_smul]
  have h := quadMaj_dom hM zero_le_one hd hq hlam hQ
  have hMs := SecA.CA.psd_symm hM
  have htr : M.trace ≤ A.trace := by
    have := hAM.trace_nonneg
    rw [Matrix.trace_sub] at this
    linarith
  have htrM := hM.trace_nonneg
  have hqM := qForm_nonneg hM x
  have hqMA : qForm M x ≤ qForm A x := by
    have h' := qForm_nonneg hAM x
    simp only [qForm, Matrix.sub_mulVec, dotProduct_sub] at h'
    simp only [qForm]
    linarith
  have hneg : ∀ i, ((-M + (-M)ᵀ) *ᵥ x) i = -(((M + Mᵀ) *ᵥ x) i) := fun i => by
    rw [show -M + (-M)ᵀ = -(M + Mᵀ) by rw [Matrix.transpose_neg]; abel, Matrix.neg_mulVec]
    rfl
  refine ⟨?_, fun i => ?_, fun i k => ?_⟩
  · have e : quadFn M.trace 0 (-M) x = M.trace - qForm M x := by
      simp only [quadFn, zero_dotProduct, add_zero, SecA.CA.qForm_neg]
      ring
    rw [e, abs_le]
    constructor <;> linarith
  · have h1 := h.h1 i
    simp only [Pi.zero_apply, zero_add] at h1 ⊢
    rw [hneg, abs_neg]
    have := hlam i
    nlinarith
  · have h2 := h.h2 i k
    simp only [Matrix.neg_apply] at h2 ⊢
    rw [show -M i k + -M k i = -(M i k + M k i) by ring, abs_neg]
    have := mul_nonneg (hlam i) (hlam k)
    nlinarith

/-- The scalar inputs of `scalar_g1` in terms of the physical entries `g = G⁺_vi`, `h = G⁻_vi`,
`P₁ = G⁺_vvG⁺_ii`, `P₂ = G⁻_vvG⁻_ii`, `A_ii ≤ a²P₁`, `(Mξ)_i² ≤ A_ii`. -/
theorem g1_inputs {a g h P1 P2 Aii Mx p : ℝ} (hp : 0 ≤ p) (hω1 : 0 ≤ a ^ 2 * (P1 - g ^ 2))
    (hω2 : 0 ≤ a ^ 2 * (P2 - h ^ 2)) (hAii : Aii ≤ a ^ 2 * P1) (hMx : Mx ^ 2 ≤ Aii) :
    p * (a ^ 2 * (P1 - g ^ 2) + a ^ 2 * (P2 - h ^ 2)) ≤ p * (a ^ 2 * P1 + a ^ 2 * P2) ∧
      (p * (2 * (a * |g|) + 2 * (a * |h|))) ^ 2 ≤ 8 * p ^ 2 * (a ^ 2 * (g ^ 2 + h ^ 2)) ∧
      a ^ 2 * (g ^ 2 + h ^ 2) ≤ a ^ 2 * P1 + a ^ 2 * P2 ∧
      (2 * |Mx|) ^ 2 ≤ 4 * (a ^ 2 * P1 + a ^ 2 * P2) ∧
      Aii ≤ a ^ 2 * P1 + a ^ 2 * P2 := by
  have hg : 0 ≤ a ^ 2 * g ^ 2 := by positivity
  have hh : 0 ≤ a ^ 2 * h ^ 2 := by positivity
  have e1 : a ^ 2 * (P1 - g ^ 2) = a ^ 2 * P1 - a ^ 2 * g ^ 2 := by ring
  have e2 : a ^ 2 * (P2 - h ^ 2) = a ^ 2 * P2 - a ^ 2 * h ^ 2 := by ring
  have hP2 : 0 ≤ a ^ 2 * P2 := by linarith
  refine ⟨mul_le_mul_of_nonneg_left (by linarith) hp, ?_, by linarith, ?_, by linarith⟩
  · have h3 : (|g| + |h|) ^ 2 ≤ 2 * (g ^ 2 + h ^ 2) := by
      have h0 := sq_nonneg (|g| - |h|)
      have e3 : (|g| - |h|) ^ 2 = |g| ^ 2 - 2 * (|g| * |h|) + |h| ^ 2 := by ring
      have e4 : (|g| + |h|) ^ 2 = |g| ^ 2 + 2 * (|g| * |h|) + |h| ^ 2 := by ring
      rw [sq_abs] at e3 e4
      rw [sq_abs] at e3 e4
      linarith
    have e : (p * (2 * (a * |g|) + 2 * (a * |h|))) ^ 2 = 4 * (p ^ 2 * a ^ 2) * (|g| + |h|) ^ 2 := by
      ring
    have e' : 8 * p ^ 2 * (a ^ 2 * (g ^ 2 + h ^ 2)) = 4 * (p ^ 2 * a ^ 2) * (2 * (g ^ 2 + h ^ 2)) := by
      ring
    rw [e, e']
    exact mul_le_mul_of_nonneg_left h3 (by positivity)
  · have e : (2 * |Mx|) ^ 2 = 4 * Mx ^ 2 := by rw [mul_pow, sq_abs]; ring
    rw [e]
    linarith

section Graph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The `A-EPB4` hypotheses for one branch at a good precision (F1, `t = D_v h_v = 1/α`):
`|((R + Rᵀ)ξ)_i| ≤ 2(a|G_vi|)α`, `|R_ii| ≤ a²(G_vvG_ii - G_vi²)α`, with `0 < α = clipF R ξ ≤ 1`,
`a²(G_vvG_ii - G_vi²) ≥ 0` and `R_ii ≤ a² G_vvG_ii`. -/
theorem branch_epb4 {a τ : ℝ} (ha : 0 < a) (hτ : τ ^ 2 = 1) {y : V → ℝ} (hy : ∀ i, 0 ≤ y i)
    {σ : Config V} {S : Finset V} {v : V} (hv : v ∈ S) (hP : (precN G a τ y σ S).PosDef)
    (hA : (rootMat G a τ y σ S v).PosSemidef) (i : nbhd G S v) :
    0 < clipF (rootMat G a τ y σ S v) (rootSigns G σ S v) ∧
    clipF (rootMat G a τ y σ S v) (rootSigns G σ S v) =
      1 - qForm (rootMat G a τ y σ S v) (rootSigns G σ S v) ∧
    |((rootMat G a τ y σ S v + (rootMat G a τ y σ S v)ᵀ) *ᵥ rootSigns G σ S v) i| ≤
      2 * (a * |greenP G a τ y σ S v i|) * clipF (rootMat G a τ y σ S v) (rootSigns G σ S v) ∧
    |rootMat G a τ y σ S v i i| ≤ a ^ 2 * (greenP G a τ y σ S v v * greenP G a τ y σ S i i -
      greenP G a τ y σ S v i ^ 2) * clipF (rootMat G a τ y σ S v) (rootSigns G σ S v) ∧
    0 ≤ a ^ 2 * (greenP G a τ y σ S v v * greenP G a τ y σ S i i -
      greenP G a τ y σ S v i ^ 2) ∧
    rootMat G a τ y σ S v i i ≤ a ^ 2 * (greenP G a τ y σ S v v * greenP G a τ y σ S i i) := by
  obtain ⟨h1, h2, h3⟩ := SecA.CA.root_F1' G hτ hy hv hP
  have hD1 : 1 ≤ diagD G a y S v := FloorIns.one_le_diagD G a hy S v
  have hh : 0 < hN G a τ y σ S v := hP.inv.diag_pos
  obtain ⟨t, ht⟩ : ∃ t, t = diagD G a y S v * hN G a τ y σ S v := ⟨_, rfl⟩
  have ht0 : 0 < t := by rw [ht]; exact mul_pos (by linarith) hh
  rw [← ht] at h1
  have h2' := h2 i
  have h3' := h3 i
  rw [← ht] at h2' h3'
  obtain ⟨R, hR⟩ : ∃ R, R = rootMat G a τ y σ S v := ⟨_, rfl⟩
  obtain ⟨ξ, hξ⟩ : ∃ ξ, ξ = rootSigns G σ S v := ⟨_, rfl⟩
  rw [← hR] at h1 h2' h3' hA ⊢
  rw [← hξ] at h1 h2' ⊢
  obtain ⟨g, hg⟩ : ∃ g, g = greenP G a τ y σ S v i := ⟨_, rfl⟩
  obtain ⟨P, hPd⟩ : ∃ P, P = greenP G a τ y σ S v v * greenP G a τ y σ S i i := ⟨_, rfl⟩
  rw [← hg] at h2' h3' ⊢
  rw [← hPd] at h3' ⊢
  set α := 1 - qForm R ξ with hα
  have hq := qForm_nonneg hA ξ
  have hα0 : 0 < α := by
    by_contra hc
    push Not at hc
    nlinarith
  have hα1 : α ≤ 1 := by linarith
  have cR : clipF R ξ = α := max_eq_left hα0.le
  have eRx : (R *ᵥ ξ) i = -(τ * a) * g * α := by
    linear_combination (-((R *ᵥ ξ) i)) * h1 + α * h2'
  have eRii : R i i = a ^ 2 * (P - g ^ 2) * α := by
    linear_combination (-(R i i)) * h1 + α * h3'
  have hRii : 0 ≤ R i i := hA.diag_nonneg
  have hω : 0 ≤ a ^ 2 * (P - g ^ 2) := by
    by_contra hc
    push Not at hc
    nlinarith
  have hτa : |τ| = 1 := by
    have : |τ| ^ 2 = 1 := by rw [sq_abs]; exact hτ
    nlinarith [abs_nonneg τ]
  have hRs := SecA.CA.psd_symm hA
  have hsym : ((R + Rᵀ) *ᵥ ξ) i = 2 * (R *ᵥ ξ) i := by
    rw [Matrix.add_mulVec]
    simp only [Pi.add_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply, ← hRs]
    ring
  refine ⟨cR ▸ hα0, cR, ?_, ?_, hω, ?_⟩
  · rw [hsym, eRx, cR, abs_mul, abs_mul, abs_mul, abs_neg, abs_mul, hτa, abs_two,
      abs_of_pos ha, abs_of_pos hα0]
    linarith
  · rw [abs_of_nonneg hRii, cR, eRii]
  · rw [eRii]
    have h4 : a ^ 2 * (P - g ^ 2) * α ≤ a ^ 2 * (P - g ^ 2) := mul_le_of_le_one_right hω hα1
    nlinarith [sq_nonneg g, pow_pos ha 2]

end Graph

end SecA.C4

namespace CapPoint

variable {d p : ℕ} (cp : CapPoint.{u} d p)

/-- The row quantity `r_i = a²((G⁺_vi)² + (G⁻_vi)²)`. -/
noncomputable def c4r (σ : Config cp.V) (v i : cp.V) : ℝ :=
  aOf d p ^ 2 * (cp.gp σ v i ^ 2 + cp.gm σ v i ^ 2)

/-- The diagonal quantity `u_i = a²(G⁺_vvG⁺_ii + G⁻_vvG⁻_ii)`. -/
noncomputable def c4u (σ : Config cp.V) (v i : cp.V) : ℝ :=
  aOf d p ^ 2 * (cp.gp σ v v * cp.gp σ i i) + aOf d p ^ 2 * (cp.gm σ v v * cp.gm σ i i)

/-- `A-EPB4` at the own signs for `F₀ = (tr M - q_M) α^p β^p`:
`|∂_i⁴F₀(ξ)|/Φ(ξ) ≤ 24 (2 + tr A)(10 p² u_i² + 368 p⁴ r_i u_i)`. -/
theorem grade_one_pt (hR : RegA d p) {v : cp.V} (hv : v ∈ cp.S)
    (M : Config cp.V → Matrix (cp.N v) (cp.N v) ℝ)
    (hMpsd : ∀ σ, 0 < wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v →
      (M σ).PosSemidef ∧ (cp.A σ v - M σ).PosSemidef)
    {σ : Config cp.V} (hσ : wt cp.G p (aOf d p) cp.yp cp.ym σ cp.S ≠ 0) (i : cp.N v) :
    |(pderiv i)^[4] (clipObs (quadFn (M σ).trace 0 (-(M σ))) p p (cp.A σ v) (cp.B σ v))
        (cp.xi σ v)| / starPhi p (cp.A σ v) (cp.B σ v) (cp.xi σ v) ≤
      24 * (2 + (cp.A σ v).trace) * (10 * (p : ℝ) ^ 2 * cp.c4u σ v i ^ 2 +
        368 * (p : ℝ) ^ 4 * cp.c4r σ v i * cp.c4u σ v i) := by
  have ha := hR.treg.aOf_pos
  have hp1 := hR.one_le_p
  have hσc := cp.wtCore_ne_zero_of_wt hR hv hσ
  obtain ⟨hA, hB⟩ := cp.root_psd_core hσc
  obtain ⟨hM, hAM⟩ := hMpsd σ (lt_of_le_of_ne (SecA.wtCore_nonneg cp.G _ _ _ _ σ _ _)
    (Ne.symm hσc))
  obtain ⟨hPp, hPm⟩ := cp.precN_pd_of_wt hσ
  obtain ⟨α0, cA, hA1, hA2, hω1, hAiiu⟩ :=
    SecA.C4.branch_epb4 cp.G ha (τ := 1) (by norm_num) cp.yp_nonneg hv hPp hA i
  obtain ⟨β0, cB, hB1, hB2, hω2, -⟩ :=
    SecA.C4.branch_epb4 cp.G ha (τ := -1) (by norm_num) cp.ym_nonneg hv hPm hB i
  change |((cp.A σ v + (cp.A σ v)ᵀ) *ᵥ cp.xi σ v) i| ≤
    2 * (aOf d p * |cp.gp σ v i|) * clipF (cp.A σ v) (cp.xi σ v) at hA1
  change |cp.A σ v i i| ≤ aOf d p ^ 2 * (cp.gp σ v v * cp.gp σ i i - cp.gp σ v i ^ 2) *
    clipF (cp.A σ v) (cp.xi σ v) at hA2
  change 0 ≤ aOf d p ^ 2 * (cp.gp σ v v * cp.gp σ i i - cp.gp σ v i ^ 2) at hω1
  change cp.A σ v i i ≤ aOf d p ^ 2 * (cp.gp σ v v * cp.gp σ i i) at hAiiu
  change |((cp.B σ v + (cp.B σ v)ᵀ) *ᵥ cp.xi σ v) i| ≤
    2 * (aOf d p * |cp.gm σ v i|) * clipF (cp.B σ v) (cp.xi σ v) at hB1
  change |cp.B σ v i i| ≤ aOf d p ^ 2 * (cp.gm σ v v * cp.gm σ i i - cp.gm σ v i ^ 2) *
    clipF (cp.B σ v) (cp.xi σ v) at hB2
  change 0 ≤ aOf d p ^ 2 * (cp.gm σ v v * cp.gm σ i i - cp.gm σ v i ^ 2) at hω2
  change 0 < clipF (cp.A σ v) (cp.xi σ v) at α0
  change 0 < clipF (cp.B σ v) (cp.xi σ v) at β0
  change clipF (cp.A σ v) (cp.xi σ v) = 1 - qForm (cp.A σ v) (cp.xi σ v) at cA
  change clipF (cp.B σ v) (cp.xi σ v) = 1 - qForm (cp.B σ v) (cp.xi σ v) at cB
  have hqA1 : qForm (cp.A σ v) (cp.xi σ v) < 1 := by linarith
  have hqB1 : qForm (cp.B σ v) (cp.xi σ v) < 1 := by linarith
  -- the prefactor conditions
  have hqM := qForm_nonneg hM (cp.xi σ v)
  have hqMA : qForm (M σ) (cp.xi σ v) ≤ qForm (cp.A σ v) (cp.xi σ v) := by
    have h' := qForm_nonneg hAM (cp.xi σ v)
    simp only [qForm, Matrix.sub_mulVec, dotProduct_sub] at h'
    simp only [qForm]
    linarith
  have htrMA : (M σ).trace ≤ (cp.A σ v).trace := by
    have := hAM.trace_nonneg
    rw [Matrix.trace_sub] at this
    linarith
  have htrM := hM.trace_nonneg
  have htrA := hA.trace_nonneg
  have h0 : |quadFn (M σ).trace 0 (-(M σ)) (cp.xi σ v)| ≤ 1 + (cp.A σ v).trace := by
    have e : quadFn (M σ).trace 0 (-(M σ)) (cp.xi σ v) =
        (M σ).trace - qForm (M σ) (cp.xi σ v) := by
      simp only [quadFn, zero_dotProduct, add_zero, SecA.CA.qForm_neg]
      ring
    rw [e, abs_le]
    constructor <;> linarith
  have hMs := SecA.CA.psd_symm hM
  have h1 : |(0 : cp.N v → ℝ) i + ((-(M σ) + (-(M σ))ᵀ) *ᵥ cp.xi σ v) i| ≤
      2 * |(M σ *ᵥ cp.xi σ v) i| := by
    have hT : -(M σ) + (-(M σ))ᵀ = (-2 : ℝ) • M σ := by
      ext j k
      simp only [Matrix.add_apply, Matrix.neg_apply, Matrix.transpose_apply, Matrix.smul_apply,
        smul_eq_mul, hMs k j]
      ring
    rw [hT, Matrix.smul_mulVec, Pi.zero_apply, zero_add, Pi.smul_apply, smul_eq_mul, abs_mul]
    norm_num
  have hMii : (M σ) i i ≤ cp.A σ v i i := by
    have := hAM.diag_nonneg (i := i)
    simp only [Matrix.sub_apply] at this
    linarith
  have hMii0 : 0 ≤ (M σ) i i := hM.diag_nonneg
  have h2 : |(-(M σ)) i i| ≤ cp.A σ v i i := by
    rw [Matrix.neg_apply, abs_neg, abs_of_nonneg hMii0]
    exact hMii
  have hAii : 0 ≤ cp.A σ v i i := hA.diag_nonneg
  have hE := SecA.iter_pderiv_clipObs_le (e₁ := p) (e₂ := p) hqA1 hqB1 i h0 h1 h2 hA1 hA2 hB1
    hB2 4
  have hco := SecA.C4.coeff_four_le (by linarith : 0 ≤ 1 + (cp.A σ v).trace)
    (by positivity : 0 ≤ 2 * |(M σ *ᵥ cp.xi σ v) i|) hAii
    (by positivity : 0 ≤ 2 * (aOf d p * |cp.gp σ v i|)) hω1
    (by positivity : 0 ≤ 2 * (aOf d p * |cp.gm σ v i|)) hω2 p
  -- the scalar inputs
  have hMx : (M σ *ᵥ cp.xi σ v) i ^ 2 ≤ cp.A σ v i i := by
    have h1' := SecA.CA.mulVec_apply_sq_le' hM (cp.xi σ v) i
    have h4 : (M σ) i i * qForm (M σ) (cp.xi σ v) ≤ (M σ) i i * 1 :=
      mul_le_mul_of_nonneg_left (by linarith) hMii0
    linarith
  obtain ⟨i1, i2, i3, i4, i5⟩ := SecA.C4.g1_inputs (by linarith : (0 : ℝ) ≤ p) hω1 hω2
    hAiiu hMx
  have hr0 : 0 ≤ aOf d p ^ 2 * (cp.gp σ v i ^ 2 + cp.gm σ v i ^ 2) := by positivity
  have hsc := SecA.C4.scalar_g1 (P := (p : ℝ)) (m₀ := 1 + (cp.A σ v).trace) hp1
    (by linarith) (by positivity) hAii (by positivity) (by positivity) hr0 i1 i2 i3 i4 i5
  have hr_def : cp.c4r σ v i = aOf d p ^ 2 * (cp.gp σ v i ^ 2 + cp.gm σ v i ^ 2) := rfl
  have hu_def : cp.c4u σ v i = aOf d p ^ 2 * (cp.gp σ v v * cp.gp σ i i) +
      aOf d p ^ 2 * (cp.gm σ v v * cp.gm σ i i) := rfl
  rw [← hr_def, ← hu_def] at hsc
  -- assemble
  have hΦ : starPhi p (cp.A σ v) (cp.B σ v) (cp.xi σ v) =
      clipF (cp.A σ v) (cp.xi σ v) ^ p * clipF (cp.B σ v) (cp.xi σ v) ^ p := rfl
  have hΦ0 : 0 < clipF (cp.A σ v) (cp.xi σ v) ^ p * clipF (cp.B σ v) (cp.xi σ v) ^ p := by
    positivity
  rw [hΦ, div_le_iff₀ hΦ0]
  have h4 : (Nat.factorial 4 : ℝ) = 24 := by norm_num
  rw [h4] at hE
  have e : 1 + (1 + (cp.A σ v).trace) = 2 + (cp.A σ v).trace := by ring
  rw [e] at hsc
  refine hE.trans ?_
  have hcf := hco.trans hsc
  have : (24 : ℝ) * clipF (cp.A σ v) (cp.xi σ v) ^ p * clipF (cp.B σ v) (cp.xi σ v) ^ p *
      ((C (1 + (cp.A σ v).trace) + C (2 * |(M σ *ᵥ cp.xi σ v) i|) * X +
          C (cp.A σ v i i) * X ^ 2) *
        (1 + C (2 * (aOf d p * |cp.gp σ v i|)) * X +
          C (aOf d p ^ 2 * (cp.gp σ v v * cp.gp σ i i - cp.gp σ v i ^ 2)) * X ^ 2) ^ p *
        (1 + C (2 * (aOf d p * |cp.gm σ v i|)) * X +
          C (aOf d p ^ 2 * (cp.gm σ v v * cp.gm σ i i - cp.gm σ v i ^ 2)) * X ^ 2) ^ p).coeff 4
      ≤ 24 * clipF (cp.A σ v) (cp.xi σ v) ^ p * clipF (cp.B σ v) (cp.xi σ v) ^ p *
        ((2 + (cp.A σ v).trace) * (10 * (p : ℝ) ^ 2 * cp.c4u σ v i ^ 2 +
          368 * (p : ℝ) ^ 4 * cp.c4r σ v i * cp.c4u σ v i)) :=
    mul_le_mul_of_nonneg_left hcf (by positivity)
  refine this.trans (le_of_eq ?_)
  ring

/-- On the support: `0 ≤ r_i ≤ u_i ≤ 4a²(h⁺_vh⁺_i + h⁻_vh⁻_i)`. -/
theorem c4ru_le (hR : RegA d p) {v : cp.V} (hv : v ∈ cp.S) {σ : Config cp.V}
    (hσ : wt cp.G p (aOf d p) cp.yp cp.ym σ cp.S ≠ 0) (i : cp.N v) :
    0 ≤ cp.c4r σ v i ∧ cp.c4r σ v i ≤ cp.c4u σ v i ∧
      cp.c4u σ v i ≤ 4 * aOf d p ^ 2 * (cp.hp σ v * cp.hp σ i + cp.hm σ v * cp.hm σ i) := by
  have ha := hR.treg.aOf_pos
  have hσc := cp.wtCore_ne_zero_of_wt hR hv hσ
  obtain ⟨hA, hB⟩ := cp.root_psd_core hσc
  obtain ⟨hPp, hPm⟩ := cp.precN_pd_of_wt hσ
  obtain ⟨-, -, -, -, hω1, -⟩ :=
    SecA.C4.branch_epb4 cp.G ha (τ := 1) (by norm_num) cp.yp_nonneg hv hPp hA i
  obtain ⟨-, -, -, -, hω2, -⟩ :=
    SecA.C4.branch_epb4 cp.G ha (τ := -1) (by norm_num) cp.ym_nonneg hv hPm hB i
  change 0 ≤ aOf d p ^ 2 * (cp.gp σ v v * cp.gp σ i i - cp.gp σ v i ^ 2) at hω1
  change 0 ≤ aOf d p ^ 2 * (cp.gm σ v v * cp.gm σ i i - cp.gm σ v i ^ 2) at hω2
  have hiS : (i : cp.V) ∈ cp.S := (Finset.mem_filter.1 i.2).1
  have hs := SecA.sOf_le_two hR.treg
  have hyp := cp.inCube_yp hR
  have hym := cp.inCube_ym hR
  have h1 : 0 < cp.hp σ v := hPp.inv.diag_pos
  have h2 : 0 < cp.hp σ i := hPp.inv.diag_pos
  have h3 : 0 < cp.hm σ v := hPm.inv.diag_pos
  have h4 : 0 < cp.hm σ i := hPm.inv.diag_pos
  have egp : ∀ x, cp.gp σ x x = cp.yp x * cp.hp σ x := fun x =>
    SecA.greenP_self cp.G (cp.yp_nonneg x)
  have egm : ∀ x, cp.gm σ x x = cp.ym x * cp.hm σ x := fun x =>
    SecA.greenP_self cp.G (cp.ym_nonneg x)
  have hP1 : cp.gp σ v v * cp.gp σ i i ≤ 4 * (cp.hp σ v * cp.hp σ i) := by
    rw [egp, egp]
    have a1 := mul_le_mul_of_nonneg_right ((hyp v).2.trans hs) h1.le
    have a2 := mul_le_mul_of_nonneg_right ((hyp (i : cp.V)).2.trans hs) h2.le
    have b1 := mul_nonneg (hyp v).1 h1.le
    have b2 := mul_nonneg (hyp (i : cp.V)).1 h2.le
    nlinarith [mul_le_mul a1 a2 b2 (by positivity)]
  have hP2 : cp.gm σ v v * cp.gm σ i i ≤ 4 * (cp.hm σ v * cp.hm σ i) := by
    rw [egm, egm]
    have a1 := mul_le_mul_of_nonneg_right ((hym v).2.trans hs) h3.le
    have a2 := mul_le_mul_of_nonneg_right ((hym (i : cp.V)).2.trans hs) h4.le
    have b1 := mul_nonneg (hym v).1 h3.le
    have b2 := mul_nonneg (hym (i : cp.V)).1 h4.le
    nlinarith [mul_le_mul a1 a2 b2 (by positivity)]
  have ha2 : 0 ≤ aOf d p ^ 2 := sq_nonneg _
  have e1 : aOf d p ^ 2 * (cp.gp σ v v * cp.gp σ i i - cp.gp σ v i ^ 2) =
      aOf d p ^ 2 * (cp.gp σ v v * cp.gp σ i i) - aOf d p ^ 2 * cp.gp σ v i ^ 2 := by ring
  have e2 : aOf d p ^ 2 * (cp.gm σ v v * cp.gm σ i i - cp.gm σ v i ^ 2) =
      aOf d p ^ 2 * (cp.gm σ v v * cp.gm σ i i) - aOf d p ^ 2 * cp.gm σ v i ^ 2 := by ring
  have hg1 : 0 ≤ aOf d p ^ 2 * cp.gp σ v i ^ 2 := by positivity
  have hg2 : 0 ≤ aOf d p ^ 2 * cp.gm σ v i ^ 2 := by positivity
  refine ⟨by unfold c4r; positivity, ?_, ?_⟩
  · show aOf d p ^ 2 * (cp.gp σ v i ^ 2 + cp.gm σ v i ^ 2) ≤
      aOf d p ^ 2 * (cp.gp σ v v * cp.gp σ i i) + aOf d p ^ 2 * (cp.gm σ v v * cp.gm σ i i)
    have e3 : aOf d p ^ 2 * (cp.gp σ v i ^ 2 + cp.gm σ v i ^ 2) =
        aOf d p ^ 2 * cp.gp σ v i ^ 2 + aOf d p ^ 2 * cp.gm σ v i ^ 2 := by ring
    linarith
  · show aOf d p ^ 2 * (cp.gp σ v v * cp.gp σ i i) + aOf d p ^ 2 * (cp.gm σ v v * cp.gm σ i i) ≤
      4 * aOf d p ^ 2 * (cp.hp σ v * cp.hp σ i + cp.hm σ v * cp.hm σ i)
    have k1 := mul_le_mul_of_nonneg_left hP1 ha2
    have k2 := mul_le_mul_of_nonneg_left hP2 ha2
    nlinarith

/-- `E (h_v h_i)^n ≤ (1+2ε)^{2n}` for `4n ≤ p` (both branches). -/
theorem E_hh_pow_le (hR : RegA d p) {v : cp.V} (hv : v ∈ cp.S) (i : cp.N v) {n : ℕ}
    (hn1 : 1 ≤ n) (hn : 4 * n ≤ p) :
    cp.E (fun σ => (cp.hp σ v * cp.hp σ i) ^ n) ≤ (1 + 2 * epsP d p) ^ (2 * n) ∧
      cp.E (fun σ => (cp.hm σ v * cp.hm σ i) ^ n) ≤ (1 + 2 * epsP d p) ^ (2 * n) := by
  have hiS : (i : cp.V) ∈ cp.S := (Finset.mem_filter.1 i.2).1
  have h2n : 1 ≤ 2 * n := by omega
  obtain ⟨mv1, mv2⟩ := cp.h_moment hR hv h2n (by omega)
  obtain ⟨mi1, mi2⟩ := cp.h_moment hR hiS h2n (by omega)
  have key : ∀ (f g : Config cp.V → ℝ),
      cp.E (fun σ => f σ ^ (2 * n)) ≤ (1 + 2 * epsP d p) ^ (2 * n) →
      cp.E (fun σ => g σ ^ (2 * n)) ≤ (1 + 2 * epsP d p) ^ (2 * n) →
      cp.E (fun σ => (f σ * g σ) ^ n) ≤ (1 + 2 * epsP d p) ^ (2 * n) := by
    intro f g hf hg
    have hpt : ∀ σ, wt cp.G p (aOf d p) cp.yp cp.ym σ cp.S ≠ 0 →
        (f σ * g σ) ^ n ≤ 1 / 2 * (f σ ^ (2 * n) + g σ ^ (2 * n)) := fun σ _ => by
      rw [mul_pow, pow_mul', pow_mul']
      nlinarith [sq_nonneg (f σ ^ n - g σ ^ n)]
    have h1 := SecA.lawE_le_of_supp cp.G hpt
    rw [lawE_const_mul, lawE_add] at h1
    unfold CapPoint.E at hf hg
    refine h1.trans ?_
    linarith
  exact ⟨key _ _ mv1 mi1, key _ _ mv2 mi2⟩

/-- The diagonal grade-one term: `Σ_i E[(2 + tr A) u_i²] ≤ 72/d`. -/
theorem sum_E_u_sq_le (hR : RegA d p) {v : cp.V} (hv : v ∈ cp.S) :
    ∑ i : cp.N v, cp.E (fun σ => (2 + (cp.A σ v).trace) * cp.c4u σ v i ^ 2) ≤ 72 / d := by
  have hd := hR.d_pos
  have hε0 := SecA.epsP_nonneg hR.treg
  have hε1 := SecA.epsP_le hR.treg
  set c := 1 + 2 * epsP d p with hc
  have hc1 : 1 ≤ c := by linarith
  have hc2 : c ≤ 101 / 100 := by linarith
  have ha4 := SecA.aOf_four_le hR
  have hp12 : 4 * 3 ≤ p := le_trans (by norm_num) hR.treg.hp
  have hp6 : 2 * 3 ≤ p := le_trans (by norm_num) hR.treg.hp
  obtain ⟨t3, -⟩ := cp.E_trace_pow_le hR hv (n := 3) (by norm_num) hp6
  have hone : ∀ i : cp.N v,
      cp.E (fun σ => (2 + (cp.A σ v).trace) * cp.c4u σ v i ^ 2) ≤ 72 / (d : ℝ) ^ 2 := by
    intro i
    obtain ⟨y1, y2⟩ := cp.E_hh_pow_le hR hv i (n := 3) (by norm_num) hp12
    set K := 16 * aOf d p ^ 4 with hK
    have hK0 : 0 ≤ K := by positivity
    have hpt : ∀ σ, wt cp.G p (aOf d p) cp.yp cp.ym σ cp.S ≠ 0 →
        (2 + (cp.A σ v).trace) * cp.c4u σ v i ^ 2 ≤
          K * (32 / 3) + K * (4 / 3) * (cp.A σ v).trace ^ 3 +
            K * (8 / 3) * (cp.hp σ v * cp.hp σ i) ^ 3 +
            K * (8 / 3) * (cp.hm σ v * cp.hm σ i) ^ 3 := by
      intro σ hσ
      obtain ⟨r0, ru, uY⟩ := cp.c4ru_le hR hv hσ i
      have htr := (cp.root_psd hR hv hσ).1.trace_nonneg
      obtain ⟨hPp, hPm⟩ := cp.precN_pd_of_wt hσ
      have q1 : 0 ≤ cp.hp σ v * cp.hp σ i := mul_nonneg hPp.inv.diag_pos.le hPp.inv.diag_pos.le
      have q2 : 0 ≤ cp.hm σ v * cp.hm σ i := mul_nonneg hPm.inv.diag_pos.le hPm.inv.diag_pos.le
      obtain ⟨Y, hY⟩ : ∃ Y, Y = cp.hp σ v * cp.hp σ i + cp.hm σ v * cp.hm σ i := ⟨_, rfl⟩
      rw [← hY] at uY
      have hY0 : 0 ≤ Y := by rw [hY]; positivity
      have hu0 : 0 ≤ cp.c4u σ v i := r0.trans ru
      have hu2 : cp.c4u σ v i ^ 2 ≤ K * Y ^ 2 := by
        have := pow_le_pow_left₀ hu0 uY 2
        have e : (4 * aOf d p ^ 2 * Y) ^ 2 = K * Y ^ 2 := by rw [hK]; ring
        linarith
      obtain ⟨X, hX⟩ : ∃ X, X = 2 + (cp.A σ v).trace := ⟨_, rfl⟩
      have hX0 : 0 ≤ X := by rw [hX]; linarith
      have amgm : X * Y ^ 2 ≤ 1 / 3 * X ^ 3 + 2 / 3 * Y ^ 3 := by
        have h1 : 0 ≤ (X + 2 * Y) * (X - Y) ^ 2 :=
          mul_nonneg (by linarith) (sq_nonneg _)
        have e : (X + 2 * Y) * (X - Y) ^ 2 = X ^ 3 - 3 * (X * Y ^ 2) + 2 * Y ^ 3 := by ring
        linarith
      have c1 : X ^ 3 ≤ 4 * (8 + (cp.A σ v).trace ^ 3) := by
        rw [hX]
        have := add_pow_le (by norm_num : (0 : ℝ) ≤ 2) htr 3
        norm_num at this ⊢
        linarith
      have c2 : Y ^ 3 ≤ 4 * ((cp.hp σ v * cp.hp σ i) ^ 3 + (cp.hm σ v * cp.hm σ i) ^ 3) := by
        rw [hY]
        have := add_pow_le q1 q2 3
        norm_num at this ⊢
        linarith
      rw [← hX]
      calc X * cp.c4u σ v i ^ 2 ≤ X * (K * Y ^ 2) := mul_le_mul_of_nonneg_left hu2 hX0
        _ = K * (X * Y ^ 2) := by ring
        _ ≤ K * (1 / 3 * X ^ 3 + 2 / 3 * Y ^ 3) := mul_le_mul_of_nonneg_left amgm hK0
        _ ≤ K * (1 / 3 * (4 * (8 + (cp.A σ v).trace ^ 3)) +
              2 / 3 * (4 * ((cp.hp σ v * cp.hp σ i) ^ 3 + (cp.hm σ v * cp.hm σ i) ^ 3))) := by
            refine mul_le_mul_of_nonneg_left ?_ hK0
            linarith
        _ = _ := by ring
    have h1 := SecA.lawE_le_of_supp cp.G hpt
    have hZ := cp.Zw_pos hR
    have e : lawE cp.G p (aOf d p) cp.yp cp.ym cp.S (fun σ =>
        K * (32 / 3) + K * (4 / 3) * (cp.A σ v).trace ^ 3 +
          K * (8 / 3) * (cp.hp σ v * cp.hp σ i) ^ 3 +
          K * (8 / 3) * (cp.hm σ v * cp.hm σ i) ^ 3) =
        K * (32 / 3) + K * (4 / 3) * cp.E (fun σ => (cp.A σ v).trace ^ 3) +
          K * (8 / 3) * cp.E (fun σ => (cp.hp σ v * cp.hp σ i) ^ 3) +
          K * (8 / 3) * cp.E (fun σ => (cp.hm σ v * cp.hm σ i) ^ 3) := by
      simp only [lawE_add, lawE_const_mul]
      rw [show lawE cp.G p (aOf d p) cp.yp cp.ym cp.S (fun _ => (32 / 3 : ℝ)) = 32 / 3 from
          wavg_const hZ _]
      rfl
    rw [e] at h1
    refine h1.trans ?_
    have hc3 : c ^ 3 ≤ 104 / 100 := by
      calc c ^ 3 ≤ (101 / 100) ^ 3 := pow_le_pow_left₀ (by linarith) hc2 3
        _ ≤ 104 / 100 := by norm_num
    have hc6 : c ^ (2 * 3) ≤ 107 / 100 := by
      calc c ^ (2 * 3) ≤ (101 / 100) ^ (2 * 3) := pow_le_pow_left₀ (by linarith) hc2 _
        _ ≤ 107 / 100 := by norm_num
    have k1 := mul_le_mul_of_nonneg_left t3 (by positivity : (0 : ℝ) ≤ K * (4 / 3))
    have k2 := mul_le_mul_of_nonneg_left y1 (by positivity : (0 : ℝ) ≤ K * (8 / 3))
    have k3 := mul_le_mul_of_nonneg_left y2 (by positivity : (0 : ℝ) ≤ K * (8 / 3))
    have hKd : K ≤ 4 / (d : ℝ) ^ 2 := by
      rw [hK]
      have : 16 * aOf d p ^ 4 ≤ 16 * (1 / (4 * (d : ℝ) ^ 2)) := by linarith
      calc 16 * aOf d p ^ 4 ≤ 16 * (1 / (4 * (d : ℝ) ^ 2)) := this
        _ = 4 / (d : ℝ) ^ 2 := by field_simp; ring
    have hsum : K * (32 / 3) + K * (4 / 3) * c ^ 3 + K * (8 / 3) * c ^ (2 * 3) +
        K * (8 / 3) * c ^ (2 * 3) ≤ 18 * K := by nlinarith
    have : 18 * K ≤ 72 / (d : ℝ) ^ 2 := by
      have := mul_le_mul_of_nonneg_left hKd (by norm_num : (0 : ℝ) ≤ 18)
      calc 18 * K ≤ 18 * (4 / (d : ℝ) ^ 2) := this
        _ = 72 / (d : ℝ) ^ 2 := by ring
    linarith
  calc ∑ i : cp.N v, cp.E (fun σ => (2 + (cp.A σ v).trace) * cp.c4u σ v i ^ 2)
      ≤ ∑ _i : cp.N v, 72 / (d : ℝ) ^ 2 := Finset.sum_le_sum fun i _ => hone i
    _ = (Fintype.card (cp.N v) : ℝ) * (72 / (d : ℝ) ^ 2) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ d * (72 / (d : ℝ) ^ 2) := mul_le_mul_of_nonneg_right (cp.card_N_le v) (by positivity)
    _ = 72 / d := by field_simp

/-- The product-space average over `(σ, i)`, `i` uniform on `N`: `(Σ_i E f(·, i))/|N|`. -/
theorem wavg_prod_N {v : cp.V} (f : Config cp.V × cp.N v → ℝ) :
    wavg (fun ω : Config cp.V × cp.N v => wt cp.G p (aOf d p) cp.yp cp.ym ω.1 cp.S) f =
      (∑ i : cp.N v, cp.E (fun σ => f (σ, i))) / Fintype.card (cp.N v) := by
  unfold wavg CapPoint.E lawE Zw
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  have e1 : ∑ σ : Config cp.V, ∑ _i : cp.N v, wt cp.G p (aOf d p) cp.yp cp.ym σ cp.S =
      (Fintype.card (cp.N v) : ℝ) * ∑ σ : Config cp.V, wt cp.G p (aOf d p) cp.yp cp.ym σ cp.S := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [e1, ← Finset.sum_div, Finset.sum_comm, div_div, mul_comm]

/-- `E r_i² ≤ 64 a⁴ (1+2ε)⁴`. -/
theorem E_c4r_sq_le (hR : RegA d p) {v : cp.V} (hv : v ∈ cp.S) (i : cp.N v) :
    cp.E (fun σ => cp.c4r σ v i ^ 2) ≤ 64 * aOf d p ^ 4 * (1 + 2 * epsP d p) ^ 4 := by
  have hp8 : 4 * 2 ≤ p := le_trans (by norm_num) hR.treg.hp
  obtain ⟨y1, y2⟩ := cp.E_hh_pow_le hR hv i (n := 2) (by norm_num) hp8
  have hpt : ∀ σ, wt cp.G p (aOf d p) cp.yp cp.ym σ cp.S ≠ 0 →
      cp.c4r σ v i ^ 2 ≤ 32 * aOf d p ^ 4 * ((cp.hp σ v * cp.hp σ i) ^ 2 +
        (cp.hm σ v * cp.hm σ i) ^ 2) := by
    intro σ hσ
    obtain ⟨r0, ru, uY⟩ := cp.c4ru_le hR hv hσ i
    obtain ⟨hPp, hPm⟩ := cp.precN_pd_of_wt hσ
    have q1 : 0 ≤ cp.hp σ v * cp.hp σ i := mul_nonneg hPp.inv.diag_pos.le hPp.inv.diag_pos.le
    have q2 : 0 ≤ cp.hm σ v * cp.hm σ i := mul_nonneg hPm.inv.diag_pos.le hPm.inv.diag_pos.le
    have h1 := pow_le_pow_left₀ r0 (ru.trans uY) 2
    have h2 : (cp.hp σ v * cp.hp σ i + cp.hm σ v * cp.hm σ i) ^ 2 ≤
        2 * ((cp.hp σ v * cp.hp σ i) ^ 2 + (cp.hm σ v * cp.hm σ i) ^ 2) := by
      nlinarith [sq_nonneg (cp.hp σ v * cp.hp σ i - cp.hm σ v * cp.hm σ i)]
    have e : (4 * aOf d p ^ 2 * (cp.hp σ v * cp.hp σ i + cp.hm σ v * cp.hm σ i)) ^ 2 =
        16 * aOf d p ^ 4 * (cp.hp σ v * cp.hp σ i + cp.hm σ v * cp.hm σ i) ^ 2 := by ring
    have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 16 * aOf d p ^ 4)
    nlinarith
  have h1 := SecA.lawE_le_of_supp cp.G hpt
  rw [lawE_const_mul, lawE_add] at h1
  refine h1.trans ?_
  unfold CapPoint.E at y1 y2
  have h0 : (0 : ℝ) ≤ 32 * aOf d p ^ 4 := by positivity
  have := mul_le_mul_of_nonneg_left (add_le_add y1 y2) h0
  have e : (1 + 2 * epsP d p) ^ (2 * 2) = (1 + 2 * epsP d p) ^ 4 := by norm_num
  rw [e] at this
  linarith

/-- `E[((2 + tr A) d u_i)₊^{2k}] ≤ 32^{2k}` for `16 k ≤ p`. -/
theorem E_Y_pow_le (hR : RegA d p) {v : cp.V} (hv : v ∈ cp.S) (i : cp.N v) {k : ℕ}
    (hk1 : 1 ≤ k) (hk : 16 * k ≤ p) :
    cp.E (fun σ => max ((2 + (cp.A σ v).trace) * d * cp.c4u σ v i) 0 ^ (2 * k)) ≤
      32 ^ (2 * k) := by
  have hd := hR.d_pos
  have hε0 := SecA.epsP_nonneg hR.treg
  have hε1 := SecA.epsP_le hR.treg
  set c := 1 + 2 * epsP d p with hc
  have hc2 : c ≤ 2 := by linarith
  have h4k : 1 ≤ 4 * k := by omega
  obtain ⟨t4, -⟩ := cp.E_trace_pow_le hR hv h4k (by omega)
  obtain ⟨y1, y2⟩ := cp.E_hh_pow_le hR hv i h4k (by omega)
  have ha := SecA.aOf_sq_le_half hR
  have hda : 4 * (d : ℝ) * aOf d p ^ 2 ≤ 2 := by
    have : (d : ℝ) * aOf d p ^ 2 ≤ (d : ℝ) * (1 / (2 * d)) := mul_le_mul_of_nonneg_left ha hd.le
    have e : (d : ℝ) * (1 / (2 * d)) = 1 / 2 := by field_simp
    linarith
  have hpt : ∀ σ, wt cp.G p (aOf d p) cp.yp cp.ym σ cp.S ≠ 0 →
      max ((2 + (cp.A σ v).trace) * d * cp.c4u σ v i) 0 ^ (2 * k) ≤
        2 ^ (2 * k) * (1 / 2) * (2 ^ (4 * k - 1) * (2 ^ (4 * k) + (cp.A σ v).trace ^ (4 * k)) +
          2 ^ (4 * k - 1) * ((cp.hp σ v * cp.hp σ i) ^ (4 * k) +
            (cp.hm σ v * cp.hm σ i) ^ (4 * k))) := by
    intro σ hσ
    obtain ⟨r0, ru, uY⟩ := cp.c4ru_le hR hv hσ i
    have htr := (cp.root_psd hR hv hσ).1.trace_nonneg
    obtain ⟨hPp, hPm⟩ := cp.precN_pd_of_wt hσ
    have q1 : 0 ≤ cp.hp σ v * cp.hp σ i := mul_nonneg hPp.inv.diag_pos.le hPp.inv.diag_pos.le
    have q2 : 0 ≤ cp.hm σ v * cp.hm σ i := mul_nonneg hPm.inv.diag_pos.le hPm.inv.diag_pos.le
    obtain ⟨X, hX⟩ : ∃ X, X = 2 + (cp.A σ v).trace := ⟨_, rfl⟩
    obtain ⟨Y, hY⟩ : ∃ Y, Y = cp.hp σ v * cp.hp σ i + cp.hm σ v * cp.hm σ i := ⟨_, rfl⟩
    rw [← hY] at uY
    have hX0 : 0 ≤ X := by rw [hX]; linarith
    have hY0 : 0 ≤ Y := by rw [hY]; positivity
    have hu0 : 0 ≤ cp.c4u σ v i := r0.trans ru
    have hval0 : 0 ≤ X * d * cp.c4u σ v i := by positivity
    rw [← hX, max_eq_left hval0]
    have hval : X * d * cp.c4u σ v i ≤ 2 * (X * Y) := by
      have h1 : (d : ℝ) * cp.c4u σ v i ≤ (d : ℝ) * (4 * aOf d p ^ 2 * Y) :=
        mul_le_mul_of_nonneg_left uY hd.le
      have h2 : (d : ℝ) * (4 * aOf d p ^ 2 * Y) ≤ 2 * Y := by nlinarith
      have h3 := mul_le_mul_of_nonneg_left (h1.trans h2) hX0
      nlinarith
    have hXY : 0 ≤ X * Y := mul_nonneg hX0 hY0
    have hp1 : (X * d * cp.c4u σ v i) ^ (2 * k) ≤ (2 * (X * Y)) ^ (2 * k) :=
      pow_le_pow_left₀ hval0 hval _
    have hp2 : (2 * (X * Y)) ^ (2 * k) = 2 ^ (2 * k) * (X ^ (2 * k) * Y ^ (2 * k)) := by
      rw [mul_pow, mul_pow]
    have hp3 : X ^ (2 * k) * Y ^ (2 * k) ≤ (1 / 2) * (X ^ (4 * k) + Y ^ (4 * k)) := by
      have e1 : X ^ (4 * k) = (X ^ (2 * k)) ^ 2 := by rw [← pow_mul]; ring_nf
      have e2 : Y ^ (4 * k) = (Y ^ (2 * k)) ^ 2 := by rw [← pow_mul]; ring_nf
      rw [e1, e2]
      nlinarith [sq_nonneg (X ^ (2 * k) - Y ^ (2 * k))]
    have hp4 : X ^ (4 * k) ≤ 2 ^ (4 * k - 1) * (2 ^ (4 * k) + (cp.A σ v).trace ^ (4 * k)) := by
      rw [hX]; exact add_pow_le (by norm_num) htr _
    have hp5 : Y ^ (4 * k) ≤ 2 ^ (4 * k - 1) * ((cp.hp σ v * cp.hp σ i) ^ (4 * k) +
        (cp.hm σ v * cp.hm σ i) ^ (4 * k)) := by
      rw [hY]; exact add_pow_le q1 q2 _
    have h2k : (0 : ℝ) ≤ 2 ^ (2 * k) := by positivity
    calc (X * d * cp.c4u σ v i) ^ (2 * k) ≤ 2 ^ (2 * k) * (X ^ (2 * k) * Y ^ (2 * k)) :=
          hp1.trans (le_of_eq hp2)
      _ ≤ 2 ^ (2 * k) * ((1 / 2) * (X ^ (4 * k) + Y ^ (4 * k))) :=
          mul_le_mul_of_nonneg_left hp3 h2k
      _ ≤ _ := by
          have := add_le_add hp4 hp5
          have h2k' : (0 : ℝ) ≤ 2 ^ (2 * k) * (1 / 2) := by positivity
          nlinarith [mul_le_mul_of_nonneg_left this h2k']
  have h1 := SecA.lawE_le_of_supp cp.G hpt
  have hZ := cp.Zw_pos hR
  have e : lawE cp.G p (aOf d p) cp.yp cp.ym cp.S (fun σ =>
      2 ^ (2 * k) * (1 / 2) * (2 ^ (4 * k - 1) * (2 ^ (4 * k) + (cp.A σ v).trace ^ (4 * k)) +
        2 ^ (4 * k - 1) * ((cp.hp σ v * cp.hp σ i) ^ (4 * k) +
          (cp.hm σ v * cp.hm σ i) ^ (4 * k)))) =
      2 ^ (2 * k) * (1 / 2) * (2 ^ (4 * k - 1) * (2 ^ (4 * k) +
        cp.E (fun σ => (cp.A σ v).trace ^ (4 * k))) +
        2 ^ (4 * k - 1) * (cp.E (fun σ => (cp.hp σ v * cp.hp σ i) ^ (4 * k)) +
          cp.E (fun σ => (cp.hm σ v * cp.hm σ i) ^ (4 * k)))) := by
    simp only [lawE_const_mul, lawE_add]
    rw [show lawE cp.G p (aOf d p) cp.yp cp.ym cp.S (fun _ => (2 : ℝ) ^ (4 * k)) = 2 ^ (4 * k)
      from wavg_const hZ _]
    rfl
  rw [e] at h1
  refine h1.trans ?_
  have hc4 : c ^ (4 * k) ≤ 2 ^ (4 * k) := pow_le_pow_left₀ (by linarith) hc2 _
  have hc8 : c ^ (2 * (4 * k)) ≤ 2 ^ (4 * k) := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (by positivity) (by nlinarith) _
  have e2 : (2 : ℝ) ^ (4 * k - 1) * 2 = 2 ^ (4 * k) := by
    rw [← pow_succ, Nat.sub_add_cancel h4k]
  have hA : 2 ^ (4 * k) + cp.E (fun σ => (cp.A σ v).trace ^ (4 * k)) ≤ 2 * 2 ^ (4 * k) := by
    linarith
  have hB : cp.E (fun σ => (cp.hp σ v * cp.hp σ i) ^ (4 * k)) +
      cp.E (fun σ => (cp.hm σ v * cp.hm σ i) ^ (4 * k)) ≤ 2 * 2 ^ (4 * k) := by linarith
  have h0 : (0 : ℝ) ≤ 2 ^ (4 * k - 1) := by positivity
  have hC := add_le_add (mul_le_mul_of_nonneg_left hA h0) (mul_le_mul_of_nonneg_left hB h0)
  have h2k' : (0 : ℝ) ≤ 2 ^ (2 * k) * (1 / 2) := by positivity
  have hD := mul_le_mul_of_nonneg_left hC h2k'
  have e3 : (2 : ℝ) ^ (2 * k) * (1 / 2) * (2 ^ (4 * k - 1) * (2 * 2 ^ (4 * k)) +
      2 ^ (4 * k - 1) * (2 * 2 ^ (4 * k))) = 32 ^ (2 * k) := by
    have e4 : (2 : ℝ) ^ (4 * k - 1) * (2 * 2 ^ (4 * k)) = 2 ^ (4 * k) * 2 ^ (4 * k) := by
      rw [← e2]; ring
    rw [e4]
    have e5 : (32 : ℝ) ^ (2 * k) = 2 ^ (2 * k) * (2 ^ (4 * k) * 2 ^ (4 * k)) := by
      rw [← pow_add, ← pow_add, show (32 : ℝ) = 2 ^ 5 by norm_num, ← pow_mul]
      ring_nf
    rw [e5]
    ring
  linarith

/-- The row grade-one term: `Σ_i E[(2 + tr A) r_i u_i] ≤ 435 m/d` if `Σ_i E r_i ≤ m`, `1/d ≤ m`
(T.IL on `(σ, i)` with `i` uniform on `N`: `X = |N| r_i`, `Y = ((2 + tr A) d u_i)₊`,
`E X ≤ m`, `E X² ≤ 5²`, `E Y^{2k} ≤ 32^{2k}`, `k = ⌈log d⌉`). -/
theorem sum_E_ru_le (hR : RegA d p) {v : cp.V} (hv : v ∈ cp.S) {m : ℝ}
    (hrow : ∑ i : cp.N v, cp.E (fun σ => cp.c4r σ v i) ≤ m) (hdm : 1 / (d : ℝ) ≤ m) :
    ∑ i : cp.N v, cp.E (fun σ => (2 + (cp.A σ v).trace) * cp.c4r σ v i * cp.c4u σ v i) ≤
      435 * m / d := by
  have hd := hR.d_pos
  have hm0 : 0 ≤ m := le_trans (by positivity) hdm
  have hε0 := SecA.epsP_nonneg hR.treg
  have hε1 := SecA.epsP_le hR.treg
  rcases Nat.eq_zero_or_pos (Fintype.card (cp.N v)) with hN | hN
  · have : IsEmpty (cp.N v) := Fintype.card_eq_zero_iff.1 hN
    rw [Finset.univ_eq_empty, Finset.sum_empty]
    positivity
  obtain ⟨n, hn⟩ : ∃ n : ℝ, n = Fintype.card (cp.N v) := ⟨_, rfl⟩
  have hn0 : 0 < n := by rw [hn]; exact_mod_cast hN
  have hnd : n ≤ d := by rw [hn]; exact cp.card_N_le v
  have hw : ∀ ω : Config cp.V × cp.N v,
      0 ≤ wt cp.G p (aOf d p) cp.yp cp.ym ω.1 cp.S := fun ω => wt_nonneg cp.G ω.1
  have hW : 0 < ∑ ω : Config cp.V × cp.N v, wt cp.G p (aOf d p) cp.yp cp.ym ω.1 cp.S := by
    rw [Fintype.sum_prod_type]
    have e : ∑ σ : Config cp.V, ∑ _i : cp.N v, wt cp.G p (aOf d p) cp.yp cp.ym σ cp.S =
        n * Zw cp.G p (aOf d p) cp.yp cp.ym cp.S := by
      rw [Zw, Finset.mul_sum]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hn]
    rw [e]
    exact mul_pos hn0 (cp.Zw_pos hR)
  have hr0 : ∀ σ (i : cp.N v), 0 ≤ cp.c4r σ v i := fun σ i => by unfold c4r; positivity
  -- the interpolation order
  obtain ⟨k, hkdef⟩ : ∃ k, k = ⌈Real.log d⌉₊ := ⟨_, rfl⟩
  have hlog := hR.logd
  have hk1 : 1 ≤ k := by rw [hkdef]; exact Nat.ceil_pos.2 (by linarith)
  have hkge : Real.log d ≤ k := by rw [hkdef]; exact Nat.le_ceil _
  have hklt : (k : ℝ) < Real.log d + 1 := by rw [hkdef]; exact Nat.ceil_lt_add_one (by linarith)
  have hk16 : 16 * k ≤ p := by
    have h := hR.interp_order_le
    have : ((16 * k : ℕ) : ℝ) ≤ p := by push_cast; linarith
    exact_mod_cast this
  -- the three moments
  have hXm : wavg (fun ω : Config cp.V × cp.N v => wt cp.G p (aOf d p) cp.yp cp.ym ω.1 cp.S)
      (fun ω => n * cp.c4r ω.1 v ω.2) ≤ m := by
    rw [cp.wavg_prod_N, ← hn]
    have e : ∀ i : cp.N v, cp.E (fun σ => n * cp.c4r σ v i) = n * cp.E (fun σ => cp.c4r σ v i) :=
      fun i => lawE_const_mul cp.G _ _
    simp only [e, ← Finset.mul_sum]
    rw [mul_div_cancel_left₀ _ hn0.ne']
    exact hrow
  have hX2 : wavg (fun ω : Config cp.V × cp.N v => wt cp.G p (aOf d p) cp.yp cp.ym ω.1 cp.S)
      (fun ω => (n * cp.c4r ω.1 v ω.2) ^ 2) ≤ 5 ^ 2 := by
    rw [cp.wavg_prod_N, ← hn]
    have e : ∀ i : cp.N v, cp.E (fun σ => (n * cp.c4r σ v i) ^ 2) =
        n ^ 2 * cp.E (fun σ => cp.c4r σ v i ^ 2) := fun i => by
      unfold CapPoint.E
      rw [← lawE_const_mul cp.G (n ^ 2)]
      exact congrArg _ (funext fun σ => by ring)
    simp only [e, ← Finset.mul_sum]
    rw [div_le_iff₀ hn0]
    have h1 : ∑ i : cp.N v, cp.E (fun σ => cp.c4r σ v i ^ 2) ≤
        n * (64 * aOf d p ^ 4 * (1 + 2 * epsP d p) ^ 4) := by
      calc ∑ i : cp.N v, cp.E (fun σ => cp.c4r σ v i ^ 2) ≤
            ∑ _i : cp.N v, 64 * aOf d p ^ 4 * (1 + 2 * epsP d p) ^ 4 :=
            Finset.sum_le_sum fun i _ => cp.E_c4r_sq_le hR hv i
        _ = n * (64 * aOf d p ^ 4 * (1 + 2 * epsP d p) ^ 4) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hn]
    have ha4 := SecA.aOf_four_le hR
    have hc4 : (1 + 2 * epsP d p) ^ 4 ≤ 105 / 100 := by
      calc (1 + 2 * epsP d p) ^ 4 ≤ (101 / 100) ^ 4 := pow_le_pow_left₀ (by linarith)
            (by linarith) 4
        _ ≤ 105 / 100 := by norm_num
    have hn2 : n ^ 2 * aOf d p ^ 4 ≤ 1 / 4 := by
      have h2 : n ^ 2 ≤ (d : ℝ) ^ 2 := pow_le_pow_left₀ hn0.le hnd 2
      calc n ^ 2 * aOf d p ^ 4 ≤ (d : ℝ) ^ 2 * (1 / (4 * (d : ℝ) ^ 2)) :=
            mul_le_mul h2 ha4 (by positivity) (by positivity)
        _ = 1 / 4 := by field_simp
    have h3 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ n ^ 2)
    have h4 : n ^ 2 * (n * (64 * aOf d p ^ 4 * (1 + 2 * epsP d p) ^ 4)) =
        n * (64 * (n ^ 2 * aOf d p ^ 4) * (1 + 2 * epsP d p) ^ 4) := by ring
    have h5 : 64 * (n ^ 2 * aOf d p ^ 4) * (1 + 2 * epsP d p) ^ 4 ≤ 25 := by
      have : 0 ≤ (1 + 2 * epsP d p) ^ 4 := by positivity
      nlinarith
    have h6 := mul_le_mul_of_nonneg_left h5 hn0.le
    nlinarith
  have hY2k : wavg (fun ω : Config cp.V × cp.N v => wt cp.G p (aOf d p) cp.yp cp.ym ω.1 cp.S)
      (fun ω => max ((2 + (cp.A ω.1 v).trace) * d * cp.c4u ω.1 v ω.2) 0 ^ (2 * k)) ≤
        32 ^ (2 * k) := by
    rw [cp.wavg_prod_N, ← hn, div_le_iff₀ hn0]
    calc ∑ i : cp.N v, cp.E (fun σ =>
          max ((2 + (cp.A σ v).trace) * d * cp.c4u σ v i) 0 ^ (2 * k)) ≤
          ∑ _i : cp.N v, (32 : ℝ) ^ (2 * k) :=
          Finset.sum_le_sum fun i _ => cp.E_Y_pow_le hR hv i hk1 hk16
      _ = 32 ^ (2 * k) * n := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hn]; ring
  have hint := wavg_mul_le_interp hw hW (X := fun ω => n * cp.c4r ω.1 v ω.2)
    (Y := fun ω => max ((2 + (cp.A ω.1 v).trace) * d * cp.c4u ω.1 v ω.2) 0)
    (fun ω => mul_nonneg hn0.le (hr0 ω.1 ω.2)) (fun ω => le_max_right _ _) hk1
    (θ := 1 / d) (m := m) (BX := 5) (BY := 32) (by positivity) hdm (by norm_num) (by norm_num)
    hXm hX2 hY2k
  -- the product average is `d` times the sum
  have eXY : wavg (fun ω : Config cp.V × cp.N v => wt cp.G p (aOf d p) cp.yp cp.ym ω.1 cp.S)
      (fun ω => n * cp.c4r ω.1 v ω.2 *
        max ((2 + (cp.A ω.1 v).trace) * d * cp.c4u ω.1 v ω.2) 0) =
      d * ∑ i : cp.N v, cp.E (fun σ => (2 + (cp.A σ v).trace) * cp.c4r σ v i * cp.c4u σ v i) := by
    rw [cp.wavg_prod_N, ← hn]
    have e : ∀ i : cp.N v, cp.E (fun σ => n * cp.c4r σ v i *
        max ((2 + (cp.A σ v).trace) * d * cp.c4u σ v i) 0) =
        n * d * cp.E (fun σ => (2 + (cp.A σ v).trace) * cp.c4r σ v i * cp.c4u σ v i) := by
      intro i
      unfold CapPoint.E
      rw [← lawE_const_mul cp.G (n * d)]
      refine lawE_congr cp.G fun σ hσ => ?_
      obtain ⟨r0, ru, -⟩ := cp.c4ru_le hR hv hσ i
      have htr := (cp.root_psd hR hv hσ).1.trace_nonneg
      have h0 : 0 ≤ (2 + (cp.A σ v).trace) * d * cp.c4u σ v i := by
        have := r0.trans ru
        positivity
      rw [max_eq_left h0]
      ring
    simp only [e]
    rw [← Finset.mul_sum, mul_assoc, mul_div_cancel_left₀ _ hn0.ne']
  -- constants
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
  have hE : (1 / (d : ℝ)) ^ (-(1 / (k : ℝ))) ≤ 2.7182818286 := by
    rw [Real.rpow_def_of_pos (by positivity)]
    have hl : Real.log (1 / (d : ℝ)) = -Real.log d := by rw [one_div, Real.log_inv]
    rw [hl]
    have : -Real.log d * -(1 / (k : ℝ)) ≤ 1 := by
      rw [neg_mul_neg, mul_one_div, div_le_one hkpos]
      exact hkge
    exact (Real.exp_le_exp.2 this).trans Real.exp_one_lt_d9.le
  have hB : (5 : ℝ) ^ (1 / (k : ℝ)) ≤ 5 := by
    calc (5 : ℝ) ^ (1 / (k : ℝ)) ≤ (5 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num)
            (by rw [div_le_one hkpos]; exact_mod_cast hk1)
      _ = 5 := Real.rpow_one 5
  have h0 : 0 ≤ (1 / (d : ℝ)) ^ (-(1 / (k : ℝ))) := by positivity
  have h1 : 0 ≤ (5 : ℝ) ^ (1 / (k : ℝ)) := by positivity
  have hfin : m * (1 / (d : ℝ)) ^ (-(1 / (k : ℝ))) * (5 : ℝ) ^ (1 / (k : ℝ)) * 32 ≤ 435 * m := by
    calc m * (1 / (d : ℝ)) ^ (-(1 / (k : ℝ))) * (5 : ℝ) ^ (1 / (k : ℝ)) * 32 ≤
          m * 2.7182818286 * 5 * 32 := by
          refine mul_le_mul_of_nonneg_right ?_ (by norm_num)
          refine mul_le_mul ?_ hB h1 (by positivity)
          exact mul_le_mul_of_nonneg_left hE hm0
      _ ≤ 435 * m := by nlinarith
  have hint' := hint.trans hfin
  have e2 : (fun ω : Config cp.V × cp.N v => n * cp.c4r ω.1 v ω.2 *
      max ((2 + (cp.A ω.1 v).trace) * d * cp.c4u ω.1 v ω.2) 0) =
      fun ω => (fun ω => n * cp.c4r ω.1 v ω.2) ω *
        (fun ω => max ((2 + (cp.A ω.1 v).trace) * d * cp.c4u ω.1 v ω.2) 0) ω := rfl
  rw [← e2, eXY] at hint'
  rw [le_div_iff₀ hd]
  linarith

/-- The grade-one term of `F₀`: `|(1/12) Σ_i E[∂_i⁴F₀(ξ)/Φ(ξ)]| ≤ 1440 p²/d + 320160 p⁴ m/d` if
`Σ_i E r_i ≤ m`, `1/d ≤ m` (`grade_one_pt`, `sum_E_u_sq_le`, `sum_E_ru_le`). -/
theorem grade_one_sum_le (hR : RegA d p) {v : cp.V} (hv : v ∈ cp.S)
    (M : Config cp.V → Matrix (cp.N v) (cp.N v) ℝ)
    (hMpsd : ∀ σ, 0 < wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v →
      (M σ).PosSemidef ∧ (cp.A σ v - M σ).PosSemidef)
    {m : ℝ} (hrow : ∑ i : cp.N v, cp.E (fun σ => cp.c4r σ v i) ≤ m) (hdm : 1 / (d : ℝ) ≤ m) :
    |∑ i : cp.N v, (1 / 12 : ℝ) * cp.E (fun σ =>
        (pderiv i)^[4] (clipObs (quadFn (M σ).trace 0 (-(M σ))) p p (cp.A σ v) (cp.B σ v))
          (cp.xi σ v) / starPhi p (cp.A σ v) (cp.B σ v) (cp.xi σ v))| ≤
      1440 * (p : ℝ) ^ 2 / d + 320160 * (p : ℝ) ^ 4 * m / d := by
  have hd := hR.d_pos
  have hU := cp.sum_E_u_sq_le hR hv
  have hRr := cp.sum_E_ru_le hR hv hrow hdm
  have hw : ∀ σ, 0 ≤ wt cp.G p (aOf d p) cp.yp cp.ym σ cp.S := fun σ => wt_nonneg cp.G σ
  have hone : ∀ i : cp.N v, |(1 / 12 : ℝ) * cp.E (fun σ =>
      (pderiv i)^[4] (clipObs (quadFn (M σ).trace 0 (-(M σ))) p p (cp.A σ v) (cp.B σ v))
        (cp.xi σ v) / starPhi p (cp.A σ v) (cp.B σ v) (cp.xi σ v))| ≤
      20 * (p : ℝ) ^ 2 * cp.E (fun σ => (2 + (cp.A σ v).trace) * cp.c4u σ v i ^ 2) +
        736 * (p : ℝ) ^ 4 *
          cp.E (fun σ => (2 + (cp.A σ v).trace) * cp.c4r σ v i * cp.c4u σ v i) := by
    intro i
    have h1 : |cp.E (fun σ =>
        (pderiv i)^[4] (clipObs (quadFn (M σ).trace 0 (-(M σ))) p p (cp.A σ v) (cp.B σ v))
          (cp.xi σ v) / starPhi p (cp.A σ v) (cp.B σ v) (cp.xi σ v))| ≤
        cp.E (fun σ => 24 * (2 + (cp.A σ v).trace) * (10 * (p : ℝ) ^ 2 * cp.c4u σ v i ^ 2 +
          368 * (p : ℝ) ^ 4 * cp.c4r σ v i * cp.c4u σ v i)) := by
      refine SecA.abs_wavg_le_of_supp hw fun σ hσ => ?_
      have hΦ := cp.starPhi_xi_pos hR hv hσ.ne'
      rw [abs_div, abs_of_pos hΦ]
      exact cp.grade_one_pt hR hv M hMpsd hσ.ne' i
    have e : cp.E (fun σ => 24 * (2 + (cp.A σ v).trace) * (10 * (p : ℝ) ^ 2 * cp.c4u σ v i ^ 2 +
          368 * (p : ℝ) ^ 4 * cp.c4r σ v i * cp.c4u σ v i)) =
        240 * (p : ℝ) ^ 2 * cp.E (fun σ => (2 + (cp.A σ v).trace) * cp.c4u σ v i ^ 2) +
          8832 * (p : ℝ) ^ 4 *
            cp.E (fun σ => (2 + (cp.A σ v).trace) * cp.c4r σ v i * cp.c4u σ v i) := by
      unfold CapPoint.E
      rw [← lawE_const_mul, ← lawE_const_mul, ← lawE_add]
      exact congrArg _ (funext fun σ => by ring)
    rw [e] at h1
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 12)]
    have := mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 1 / 12)
    linarith
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun i _ => hone i).trans ?_)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hp2 : (0 : ℝ) ≤ 20 * (p : ℝ) ^ 2 := by positivity
  have hp4 : (0 : ℝ) ≤ 736 * (p : ℝ) ^ 4 := by positivity
  have k1 := mul_le_mul_of_nonneg_left hU hp2
  have k2 := mul_le_mul_of_nonneg_left hRr hp4
  have e1 : 20 * (p : ℝ) ^ 2 * (72 / d) = 1440 * (p : ℝ) ^ 2 / d := by ring
  have e2 : 736 * (p : ℝ) ^ 4 * (435 * m / d) = 320160 * (p : ℝ) ^ 4 * m / d := by ring
  linarith

/-- Own-core and actual moments of `1 + tr A`: `≤ 3ⁿ` (`2n ≤ p`). -/
theorem one_add_trace_moments (hR : RegA d p) {v : cp.V} (hv : v ∈ cp.S) {n : ℕ} (hn1 : 1 ≤ n)
    (hn : 2 * n ≤ p) :
    cp.coreE v (fun σ => (if wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v ≠ 0 then
      1 + (cp.A σ v).trace else 0) ^ n) ≤ 3 ^ n ∧
      cp.E (fun σ => (1 + (cp.A σ v).trace) ^ n) ≤ 3 ^ n := by
  have hε0 := SecA.epsP_nonneg hR.treg
  have hε1 := SecA.epsP_le hR.treg
  have hw : ∀ σ, 0 ≤ wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v :=
    fun σ => SecA.wtCore_nonneg cp.G _ _ _ _ σ _ _
  have hZc := cp.ZwCore_pos hR hv
  have hZ := cp.Zw_pos hR
  obtain ⟨mc, -⟩ := cp.coreE_trace_pow_le hR hv hn1 hn
  obtain ⟨me, -⟩ := cp.E_trace_pow_le hR hv hn1 hn
  have h3 : (1 : ℝ) ≤ (1 + 2 * epsP d p) ^ n := one_le_pow₀ (by linarith)
  have e2 : (2 : ℝ) ^ (n - 1) * 2 = 2 ^ n := by rw [← pow_succ, Nat.sub_add_cancel hn1]
  have hfin : ∀ x : ℝ, x ≤ (1 + 2 * epsP d p) ^ n → 2 ^ (n - 1) * (1 + x) ≤ 3 ^ n := by
    intro x hx
    calc (2 : ℝ) ^ (n - 1) * (1 + x) ≤ 2 ^ (n - 1) * (2 * (1 + 2 * epsP d p) ^ n) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = (2 * (1 + 2 * epsP d p)) ^ n := by rw [mul_pow, ← e2]; ring
      _ ≤ 3 ^ n := pow_le_pow_left₀ (by positivity) (by linarith) n
  constructor
  · have hpt : ∀ σ, 0 < wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v →
        (if wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v ≠ 0 then
          1 + (cp.A σ v).trace else 0) ^ n ≤
        2 ^ (n - 1) * (1 + (if wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v ≠ 0 then
          (cp.A σ v).trace else 0) ^ n) := by
      intro σ hσ
      rw [ite_eq_left hσ.ne', ite_eq_left hσ.ne']
      have := add_pow_le zero_le_one (cp.root_psd_core hσ.ne').1.trace_nonneg n
      simpa using this
    have h1 := SecA.wavg_mono' hw hpt
    rw [SecA.wavg_const_mul, SecA.wavg_add, wavg_const hZc] at h1
    exact h1.trans (hfin _ mc)
  · have hpt : ∀ σ, wt cp.G p (aOf d p) cp.yp cp.ym σ cp.S ≠ 0 →
        (1 + (cp.A σ v).trace) ^ n ≤ 2 ^ (n - 1) * (1 + (cp.A σ v).trace ^ n) := by
      intro σ hσ
      have := add_pow_le zero_le_one (cp.root_psd hR hv hσ).1.trace_nonneg n
      simpa using this
    have h1 := SecA.lawE_le_of_supp cp.G hpt
    rw [lawE_const_mul, lawE_add,
      show lawE cp.G p (aOf d p) cp.yp cp.ym cp.S (fun _ => (1 : ℝ)) = 1 from wavg_const hZ 1]
      at h1
    exact h1.trans (hfin _ me)

/-- `A-TRANS` for `F₀ = clipObs (tr M - q_M) p p` (`clip_trans_abs`, sup and endpoint scale
`1 + tr A`, moments `≤ 3ⁿ`). -/
theorem trans_left (hR : RegA d p) {v : cp.V} (hv : v ∈ cp.S)
    (M : Config cp.V → Matrix (cp.N v) (cp.N v) ℝ) (hMc : ∀ σ σ', AgreeOff v σ σ' → M σ = M σ')
    (hMpsd : ∀ σ, 0 < wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v →
      (M σ).PosSemidef ∧ (cp.A σ v - M σ).PosSemidef) :
    |cp.coreE v (fun σ =>
        gaussE (clipObs (quadFn (M σ).trace 0 (-(M σ))) p p (cp.A σ v) (cp.B σ v)) -
        radE (clipObs (quadFn (M σ).trace 0 (-(M σ))) p p (cp.A σ v) (cp.B σ v))) / cp.FH v -
      ∑ i : cp.N v, (1 / 12 : ℝ) * cp.E (fun σ =>
        (pderiv i)^[4] (clipObs (quadFn (M σ).trace 0 (-(M σ))) p p (cp.A σ v) (cp.B σ v))
          (cp.xi σ v) / starPhi p (cp.A σ v) (cp.B σ v) (cp.xi σ v))| ≤
      2 * Real.exp 2 * 3 * (41 ^ 4 / 4 * ((p : ℝ) ^ 4 / d)) ^ 2 +
        3 * Real.exp (-(p : ℝ)) / d := by
  have hw : ∀ σ, 0 ≤ wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v :=
    fun σ => SecA.wtCore_nonneg cp.G _ _ _ _ σ _ _
  refine cp.clip_trans_abs hR hv (fun σ => (M σ).trace) (fun _ => 0) (fun σ => -(M σ)) ?_
    (fun σ => 1 + (cp.A σ v).trace) (M := 3) (by norm_num) ?_
    (fun n hn1 hn => (cp.one_add_trace_moments hR hv hn1 hn).1)
    (fun σ => 1 + (cp.A σ v).trace) ?_ (ME := 3) (by norm_num)
    (fun n hn1 hn => (cp.one_add_trace_moments hR hv hn1 hn).2)
  · intro σ σ' h
    refine ⟨?_, rfl, ?_⟩ <;> simp only [hMc σ σ' h]
  · intro σ hσ x hxA _
    obtain ⟨hA, hB⟩ := cp.root_psd_core hσ
    obtain ⟨hM, hAM⟩ := hMpsd σ (lt_of_le_of_ne (hw σ) (Ne.symm hσ))
    exact SecA.C4.quadMaj_traceM hA hM hAM hxA.le (fun i => Real.sqrt_nonneg _) fun i => by
      rw [Real.sq_sqrt (add_nonneg hA.diag_nonneg hB.diag_nonneg)]
      linarith [hB.diag_nonneg (i := i)]
  · intro σ hσ
    have hσc := cp.wtCore_ne_zero_of_wt hR hv hσ
    obtain ⟨hA, hB⟩ := cp.root_psd_core hσc
    obtain ⟨hM, hAM⟩ := hMpsd σ (lt_of_le_of_ne (hw σ) (Ne.symm hσc))
    obtain ⟨⟨hα, -, hA2⟩, -⟩ := cp.endLam_maj hR hv hσ
    have hl0 := cp.endLam_nonneg hR σ v
    have hqA := qForm_nonneg hA (cp.xi σ v)
    refine SecA.C4.quadMaj_traceM hA hM hAM (by linarith) hl0 fun i => ?_
    have h := (le_abs_self _).trans (hA2 i i)
    have : (1 - qForm (cp.A σ v) (cp.xi σ v)) * cp.endLam σ v i * cp.endLam σ v i ≤
        cp.endLam σ v i ^ 2 := by
      rw [mul_assoc, sq]
      exact mul_le_of_le_one_left (mul_nonneg (hl0 i) (hl0 i)) (by linarith)
    linarith

end CapPoint

end BiluLinial.Tight
