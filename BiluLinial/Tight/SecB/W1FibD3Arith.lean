/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecB.W1FibD3Jet

/-!
# TB.W1fib-d3: scalar estimates

* `one_add_pow_le`: `(1 + y)^m ≤ 1/(1 - my)` (`0 ≤ y`, `my < 1`; Bernoulli).
* `jpow_bounds`: bounds on the jet of `g^p` from `g^{p-r} ≤ 3` and bounds `g_r` on `|g^{(r)}|`.
* `d3_combine`: the Leibniz term `φ''' = W'''Ψ + 3W''Ψ' + 3W'Ψ'' + WΨ'''` with the `W`-bounds of
  `jpow_bounds` (`g₁ = 26κ`, `g₂ = 41 l²`, `g₃ = 96 l³`, `κ = aR + a²D²`, `l = aD`) and
  `|Ψ^{(r)}| ≤ A l^r` is at most `10⁶ W₀ A a³ D⁶ (p³R² + p)` when `R ≤ 2D`, `pa ≤ 1`, `a ≤ 1`.
  The seven monomials are bounded by `E = a³D⁶(p³R² + p)` using `p²R ≤ p³R² + p`, `p³a³ ≤ p`,
  `p²a ≤ p`, `R ≤ 2D`.
-/

@[expose] public section

namespace BiluLinial.Tight.SecB

theorem one_add_pow_le {y : ℝ} {m : ℕ} (hm : 1 ≤ m) (hy : 0 ≤ y) (hmy : (m : ℝ) * y < 1) :
    (1 + y) ^ m ≤ 1 / (1 - m * y) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hy1 : y ≤ 1 := by nlinarith
  have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ -y by linarith) m
  have h1 : 0 < 1 - (m : ℝ) * y := by linarith
  have hprod : (1 + y) ^ m * (1 - y) ^ m ≤ 1 := by
    rw [← mul_pow]
    exact pow_le_one₀ (by nlinarith) (by nlinarith)
  have hq : 1 - (m : ℝ) * y ≤ (1 - y) ^ m := by
    have e1 : (1 : ℝ) + -y = 1 - y := by ring
    have e2 : (1 : ℝ) + m * -y = 1 - m * y := by ring
    rw [e1, e2] at hb
    exact hb
  rw [le_div_iff₀ h1]
  calc (1 + y) ^ m * (1 - m * y) ≤ (1 + y) ^ m * (1 - y) ^ m :=
        mul_le_mul_of_nonneg_left hq (pow_nonneg (by linarith) m)
    _ ≤ 1 := hprod

theorem jpow_bounds (G : ℕ → ℝ → ℝ) {p : ℕ} (hp : 3 ≤ p) (t : ℝ) {g1 g2 g3 : ℝ}
    (h0 : 0 ≤ G 0 t) (hpow : ∀ r ≤ 3, G 0 t ^ (p - r) ≤ 3) (h1 : |G 1 t| ≤ g1)
    (h2 : |G 2 t| ≤ g2) (h3 : |G 3 t| ≤ g3) :
    |jpow G p 0 t| ≤ 3 ∧ |jpow G p 1 t| ≤ 3 * p * g1 ∧
      |jpow G p 2 t| ≤ 3 * p ^ 2 * g1 ^ 2 + 3 * p * g2 ∧
      |jpow G p 3 t| ≤ 3 * p ^ 3 * g1 ^ 3 + 9 * p ^ 2 * (g1 * g2) + 3 * p * g3 := by
  have hP : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have p0 : |G 0 t ^ p| ≤ 3 := by
    rw [abs_of_nonneg (pow_nonneg h0 p)]; simpa using hpow 0 (by norm_num)
  have p1 : |G 0 t ^ (p - 1)| ≤ 3 := by
    rw [abs_of_nonneg (pow_nonneg h0 _)]; exact hpow 1 (by norm_num)
  have p2 : |G 0 t ^ (p - 2)| ≤ 3 := by
    rw [abs_of_nonneg (pow_nonneg h0 _)]; exact hpow 2 (by norm_num)
  have p3 : |G 0 t ^ (p - 3)| ≤ 3 := by
    rw [abs_of_nonneg (pow_nonneg h0 _)]; exact hpow 3 le_rfl
  have cp : |(p : ℝ)| ≤ p := le_of_eq (abs_of_nonneg (by linarith))
  have hpp0 : 0 ≤ (p : ℝ) * ((p : ℝ) - 1) := by nlinarith
  have cpp : |(p : ℝ) * ((p : ℝ) - 1)| ≤ (p : ℝ) ^ 2 := by
    rw [abs_of_nonneg hpp0]; nlinarith
  have cppp : |(p : ℝ) * ((p : ℝ) - 1) * ((p : ℝ) - 2)| ≤ (p : ℝ) ^ 3 := by
    have a2 : 0 ≤ (p : ℝ) - 2 := by linarith
    rw [abs_of_nonneg (mul_nonneg hpp0 a2)]
    have a1 : (p : ℝ) * ((p : ℝ) - 1) ≤ (p : ℝ) ^ 2 := by nlinarith
    have : (p : ℝ) * ((p : ℝ) - 1) * ((p : ℝ) - 2) ≤ (p : ℝ) ^ 2 * ((p : ℝ) - 2) :=
      mul_le_mul_of_nonneg_right a1 a2
    nlinarith
  have s1sq : |G 1 t ^ 2| ≤ g1 ^ 2 := by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have s1cu : |G 1 t ^ 3| ≤ g1 ^ 3 := by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) h1 3
  refine ⟨?_, ?_, ?_, ?_⟩
  · change |G 0 t ^ p| ≤ 3
    exact p0
  · change |(p : ℝ) * G 0 t ^ (p - 1) * G 1 t| ≤ 3 * p * g1
    have := w1_abs_mul_le (w1_abs_mul_le cp p1) h1
    linarith
  · change |(p : ℝ) * ((p : ℝ) - 1) * G 0 t ^ (p - 2) * G 1 t ^ 2 +
      p * G 0 t ^ (p - 1) * G 2 t| ≤ 3 * p ^ 2 * g1 ^ 2 + 3 * p * g2
    have t1 := w1_abs_mul_le (w1_abs_mul_le cpp p2) s1sq
    have t2 := w1_abs_mul_le (w1_abs_mul_le cp p1) h2
    have := abs_add_le ((p : ℝ) * ((p : ℝ) - 1) * G 0 t ^ (p - 2) * G 1 t ^ 2)
      (p * G 0 t ^ (p - 1) * G 2 t)
    linarith
  · change |(p : ℝ) * ((p : ℝ) - 1) * ((p : ℝ) - 2) * G 0 t ^ (p - 3) * G 1 t ^ 3 +
      3 * ((p : ℝ) * ((p : ℝ) - 1)) * G 0 t ^ (p - 2) * (G 1 t * G 2 t) +
        p * G 0 t ^ (p - 1) * G 3 t| ≤ 3 * p ^ 3 * g1 ^ 3 + 9 * p ^ 2 * (g1 * g2) + 3 * p * g3
    have t1 := w1_abs_mul_le (w1_abs_mul_le cppp p3) s1cu
    have c3 : |3 * ((p : ℝ) * ((p : ℝ) - 1))| ≤ 3 * (p : ℝ) ^ 2 := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]; linarith
    have t2 := w1_abs_mul_le (w1_abs_mul_le c3 p2) (w1_abs_mul_le h1 h2)
    have t3 := w1_abs_mul_le (w1_abs_mul_le cp p1) h3
    have := abs_add_le ((p : ℝ) * ((p : ℝ) - 1) * ((p : ℝ) - 2) * G 0 t ^ (p - 3) * G 1 t ^ 3 +
      3 * ((p : ℝ) * ((p : ℝ) - 1)) * G 0 t ^ (p - 2) * (G 1 t * G 2 t))
      (p * G 0 t ^ (p - 1) * G 3 t)
    have := abs_add_le ((p : ℝ) * ((p : ℝ) - 1) * ((p : ℝ) - 2) * G 0 t ^ (p - 3) * G 1 t ^ 3)
      (3 * ((p : ℝ) * ((p : ℝ) - 1)) * G 0 t ^ (p - 2) * (G 1 t * G 2 t))
    linarith

/-- `(x + y)³ ≤ 4(x³ + y³)` for `x, y ≥ 0`. -/
theorem add_cube_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : (x + y) ^ 3 ≤ 4 * (x ^ 3 + y ^ 3) := by
  nlinarith [sq_nonneg (x - y), mul_nonneg hx hy, mul_nonneg (mul_nonneg hx hy) (add_nonneg hx hy),
    mul_nonneg (sq_nonneg (x - y)) (add_nonneg hx hy)]

-- Under the module system this proof needs slightly more than the default 200000 heartbeats.
set_option maxHeartbeats 400000 in
/-- The seven monomials of `φ'''`, bounded by `E = a³D⁶(P³R² + P)`. -/
theorem d3_monomials {a D R P : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (hD : 1 ≤ D) (hR0 : 0 ≤ R)
    (hR : R ≤ 2 * D) (hP : 1 ≤ P) (hPa : P * a ≤ 1) :
    P ^ 3 * (a * R + a ^ 2 * D ^ 2) ^ 3 ≤ 8 * (a ^ 3 * D ^ 6 * (P ^ 3 * R ^ 2 + P)) ∧
    P ^ 2 * (a * R + a ^ 2 * D ^ 2) * (a * D) ^ 2 ≤ 2 * (a ^ 3 * D ^ 6 * (P ^ 3 * R ^ 2 + P)) ∧
    P * (a * D) ^ 3 ≤ a ^ 3 * D ^ 6 * (P ^ 3 * R ^ 2 + P) ∧
    P ^ 2 * (a * R + a ^ 2 * D ^ 2) ^ 2 * (a * D) ≤ 4 * (a ^ 3 * D ^ 6 * (P ^ 3 * R ^ 2 + P)) ∧
    P * (a * R + a ^ 2 * D ^ 2) * (a * D) ^ 2 ≤ 3 * (a ^ 3 * D ^ 6 * (P ^ 3 * R ^ 2 + P)) ∧
    (a * D) ^ 3 ≤ a ^ 3 * D ^ 6 * (P ^ 3 * R ^ 2 + P) := by
  have hD0 : 0 ≤ D := by linarith
  have hP0 : 0 ≤ P := by linarith
  set X := P ^ 3 * R ^ 2 + P with hX
  have hX0 : P ≤ X := by have := mul_nonneg (pow_nonneg hP0 3) (sq_nonneg R); linarith
  have hX1 : 1 ≤ X := le_trans hP hX0
  have hXn : 0 ≤ X := by linarith
  have ha3 : 0 ≤ a ^ 3 := pow_nonneg ha 3
  have hD2 : 1 ≤ D ^ 2 := one_le_pow₀ hD
  have hDle : ∀ m n : ℕ, m ≤ n → D ^ m ≤ D ^ n := fun m n h => pow_le_pow_right₀ hD h
  have hpa2 : P ^ 2 * a ^ 2 ≤ 1 := by
    have := pow_le_pow_left₀ (by positivity) hPa 2
    nlinarith
  have hpa3 : P ^ 3 * a ^ 3 ≤ P := by
    have h1 : P * (P ^ 2 * a ^ 2) ≤ P * 1 := mul_le_mul_of_nonneg_left hpa2 hP0
    have : P ^ 3 * a ^ 3 = P * (P ^ 2 * a ^ 2) * a := by ring
    rw [this]
    nlinarith
  have hpa : P ^ 2 * a ≤ P := by
    have : P * (P * a) ≤ P * 1 := mul_le_mul_of_nonneg_left hPa hP0
    nlinarith
  have hP2R : P ^ 2 * R ≤ X := by
    have := mul_nonneg hP0 (sq_nonneg (P * R - 1))
    nlinarith
  have hP2R2 : P ^ 2 * R ^ 2 ≤ X := by
    have : P ^ 2 * R ^ 2 ≤ P ^ 3 * R ^ 2 := by
      have := mul_le_mul_of_nonneg_right (show P ^ 2 ≤ P ^ 3 by
        have := mul_le_mul_of_nonneg_left hP (sq_nonneg P); nlinarith) (sq_nonneg R)
      linarith
    linarith
  set S := R + a * D ^ 2 with hS
  have hκ : a * R + a ^ 2 * D ^ 2 = a * S := by rw [hS]; ring
  have hS0 : 0 ≤ S := by positivity
  have haD2 : a * D ^ 2 ≤ D ^ 2 := mul_le_of_le_one_left (by positivity) ha1
  rw [hκ]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `P³κ³ ≤ 8E`
    have hS3 := add_cube_le hR0 (by positivity : 0 ≤ a * D ^ 2)
    have hR3 : R ^ 3 ≤ 2 * D ^ 6 * R ^ 2 := by
      have h1 : R ^ 3 ≤ 2 * D * R ^ 2 := by
        have := mul_le_mul_of_nonneg_left hR (sq_nonneg R); nlinarith
      have h2 : 2 * D * R ^ 2 ≤ 2 * D ^ 6 * R ^ 2 := by
        have := hDle 1 6 (by norm_num); rw [pow_one] at this
        have := mul_le_mul_of_nonneg_right this (sq_nonneg R); linarith
      linarith
    have e : P ^ 3 * (a * S) ^ 3 = (P ^ 3 * a ^ 3) * S ^ 3 := by ring
    rw [e]
    have hc : 0 ≤ P ^ 3 * a ^ 3 := by positivity
    have s1 := mul_le_mul_of_nonneg_left hS3 hc
    have s2 : P ^ 3 * a ^ 3 * R ^ 3 ≤ a ^ 3 * (2 * D ^ 6 * (P ^ 3 * R ^ 2)) := by
      have := mul_le_mul_of_nonneg_left hR3 hc
      linarith [show P ^ 3 * a ^ 3 * (2 * D ^ 6 * R ^ 2) = a ^ 3 * (2 * D ^ 6 * (P ^ 3 * R ^ 2)) by
        ring]
    have s3 : P ^ 3 * a ^ 3 * (a * D ^ 2) ^ 3 ≤ a ^ 3 * D ^ 6 * P := by
      have h6 : 0 ≤ a ^ 3 * D ^ 6 := by positivity
      have := mul_le_mul_of_nonneg_right hpa3 h6
      linarith [show P ^ 3 * a ^ 3 * (a * D ^ 2) ^ 3 = P ^ 3 * a ^ 3 * (a ^ 3 * D ^ 6) by ring]
    have e2 : P ^ 3 * a ^ 3 * (4 * (R ^ 3 + (a * D ^ 2) ^ 3)) =
        4 * (P ^ 3 * a ^ 3 * R ^ 3) + 4 * (P ^ 3 * a ^ 3 * (a * D ^ 2) ^ 3) := by ring
    have h6P : 0 ≤ a ^ 3 * D ^ 6 * P := by positivity
    rw [hX]
    nlinarith
  · -- `P²κl² ≤ 2E`
    have e : P ^ 2 * (a * S) * (a * D) ^ 2 = a ^ 3 * D ^ 2 * (P ^ 2 * R + P ^ 2 * a * D ^ 2) := by
      rw [hS]; ring
    rw [e]
    have h1 : P ^ 2 * a * D ^ 2 ≤ D ^ 2 * X := by
      have := mul_le_mul_of_nonneg_right hpa (sq_nonneg D)
      have := mul_le_mul_of_nonneg_left hX0 (sq_nonneg D)
      nlinarith
    have h2 : P ^ 2 * R + P ^ 2 * a * D ^ 2 ≤ 2 * D ^ 2 * X := by
      have : X ≤ D ^ 2 * X := le_mul_of_one_le_left hXn hD2
      linarith
    have h3 : a ^ 3 * D ^ 2 * (P ^ 2 * R + P ^ 2 * a * D ^ 2) ≤ a ^ 3 * D ^ 2 * (2 * D ^ 2 * X) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    have h4 : D ^ 4 ≤ D ^ 6 := hDle 4 6 (by norm_num)
    have := mul_le_mul_of_nonneg_left h4 (by positivity : 0 ≤ 2 * a ^ 3 * X)
    nlinarith
  · -- `P l³ ≤ E`
    have h3 : D ^ 3 ≤ D ^ 6 := hDle 3 6 (by norm_num)
    have : P * (a * D) ^ 3 = a ^ 3 * D ^ 3 * P := by ring
    rw [this]
    exact mul_le_mul (mul_le_mul_of_nonneg_left h3 ha3) hX0 hP0 (by positivity)
  · -- `P²κ²l ≤ 4E`
    have hS2 : S ^ 2 ≤ 2 * (R ^ 2 + (a * D ^ 2) ^ 2) := by
      nlinarith [sq_nonneg (R - a * D ^ 2)]
    have e : P ^ 2 * (a * S) ^ 2 * (a * D) = a ^ 3 * D * (P ^ 2 * S ^ 2) := by ring
    rw [e]
    have h1 : P ^ 2 * S ^ 2 ≤ 2 * (P ^ 2 * R ^ 2) + 2 * (P ^ 2 * a ^ 2 * D ^ 4) := by
      have := mul_le_mul_of_nonneg_left hS2 (sq_nonneg P)
      nlinarith
    have h2 : P ^ 2 * a ^ 2 * D ^ 4 ≤ D ^ 4 * X := by
      have := mul_le_mul_of_nonneg_right hpa2 (by positivity : 0 ≤ D ^ 4)
      have : D ^ 4 ≤ D ^ 4 * X := le_mul_of_one_le_right (by positivity) hX1
      nlinarith
    have h3 : P ^ 2 * S ^ 2 ≤ 4 * D ^ 4 * X := by
      have : X ≤ D ^ 4 * X := le_mul_of_one_le_left hXn (one_le_pow₀ hD)
      linarith
    have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : 0 ≤ a ^ 3 * D)
    have h5 : D ^ 5 ≤ D ^ 6 := hDle 5 6 (by norm_num)
    have := mul_le_mul_of_nonneg_left h5 (by positivity : 0 ≤ 4 * a ^ 3 * X)
    nlinarith
  · -- `Pκl² ≤ 3E`
    have e : P * (a * S) * (a * D) ^ 2 = a ^ 3 * D ^ 2 * (P * S) := by ring
    rw [e]
    have h1 : P * S ≤ 3 * D ^ 2 * X := by
      have hPS : P * S ≤ P * (2 * D + D ^ 2) := by
        rw [hS]
        exact mul_le_mul_of_nonneg_left (by linarith) hP0
      have h2D : 2 * D + D ^ 2 ≤ 3 * D ^ 2 := by nlinarith
      have := mul_le_mul_of_nonneg_left h2D hP0
      have := mul_le_mul_of_nonneg_left hX0 (by positivity : (0 : ℝ) ≤ 3 * D ^ 2)
      nlinarith
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ a ^ 3 * D ^ 2)
    have h4 : D ^ 4 ≤ D ^ 6 := hDle 4 6 (by norm_num)
    have := mul_le_mul_of_nonneg_left h4 (by positivity : 0 ≤ 3 * a ^ 3 * X)
    nlinarith
  · -- `l³ ≤ E`
    have h3 : D ^ 3 ≤ D ^ 6 := hDle 3 6 (by norm_num)
    have : (a * D) ^ 3 = a ^ 3 * D ^ 3 * 1 := by ring
    rw [this]
    exact mul_le_mul (mul_le_mul_of_nonneg_left h3 ha3) hX1 zero_le_one (by positivity)

/-- The final scalar estimate of TB.W1fib-d3. -/
theorem d3_combine {W₀ A a D R P : ℝ} (hW : 0 ≤ W₀) (hA : 0 ≤ A) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hD : 1 ≤ D) (hR0 : 0 ≤ R) (hR : R ≤ 2 * D) (hP : 1 ≤ P) (hPa : P * a ≤ 1)
    {w0 w1 w2 w3 s0 s1 s2 s3 : ℝ} (hw0 : |w0| ≤ W₀ * 3)
    (hw1 : |w1| ≤ W₀ * (3 * P * (26 * (a * R + a ^ 2 * D ^ 2))))
    (hw2 : |w2| ≤ W₀ * (3 * P ^ 2 * (26 * (a * R + a ^ 2 * D ^ 2)) ^ 2 +
      3 * P * (41 * (a * D) ^ 2)))
    (hw3 : |w3| ≤ W₀ * (3 * P ^ 3 * (26 * (a * R + a ^ 2 * D ^ 2)) ^ 3 +
      9 * P ^ 2 * ((26 * (a * R + a ^ 2 * D ^ 2)) * (41 * (a * D) ^ 2)) +
        3 * P * (96 * (a * D) ^ 3)))
    (hs0 : |s0| ≤ A * (a * D) ^ 0) (hs1 : |s1| ≤ A * (a * D) ^ 1) (hs2 : |s2| ≤ A * (a * D) ^ 2)
    (hs3 : |s3| ≤ A * (a * D) ^ 3) :
    |w3 * s0 + 3 * (w2 * s1) + 3 * (w1 * s2) + w0 * s3| ≤
      1000000 * W₀ * A * (a ^ 3 * D ^ 6 * (P ^ 3 * R ^ 2 + P)) := by
  obtain ⟨m1, m2, m3, m4, m6, m7⟩ := d3_monomials ha ha1 hD hR0 hR hP hPa
  set κ := a * R + a ^ 2 * D ^ 2 with hκ
  set l := a * D with hl
  set E := a ^ 3 * D ^ 6 * (P ^ 3 * R ^ 2 + P) with hE
  have hWA : 0 ≤ W₀ * A := mul_nonneg hW hA
  have t3 : |w3 * s0| ≤ W₀ * A * (52728 * (P ^ 3 * κ ^ 3) + 9594 * (P ^ 2 * κ * l ^ 2) +
      288 * (P * l ^ 3)) := by
    have := w1_abs_mul_le hw3 hs0
    exact this.trans (le_of_eq (by ring))
  have t2 : |3 * (w2 * s1)| ≤ W₀ * A * (3 * (2028 * (P ^ 2 * κ ^ 2 * l) + 123 * (P * l ^ 3))) := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    have := w1_abs_mul_le hw2 hs1
    have := mul_le_mul_of_nonneg_left this (by norm_num : (0 : ℝ) ≤ 3)
    exact this.trans (le_of_eq (by ring))
  have t1 : |3 * (w1 * s2)| ≤ W₀ * A * (3 * (78 * (P * κ * l ^ 2))) := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    have := w1_abs_mul_le hw1 hs2
    have := mul_le_mul_of_nonneg_left this (by norm_num : (0 : ℝ) ≤ 3)
    exact this.trans (le_of_eq (by ring))
  have t0 : |w0 * s3| ≤ W₀ * A * (3 * l ^ 3) := by
    have := w1_abs_mul_le hw0 hs3
    exact this.trans (le_of_eq (by ring))
  have hB : 52728 * (P ^ 3 * κ ^ 3) + 9594 * (P ^ 2 * κ * l ^ 2) + 288 * (P * l ^ 3) +
      3 * (2028 * (P ^ 2 * κ ^ 2 * l) + 123 * (P * l ^ 3)) + 3 * (78 * (P * κ * l ^ 2)) +
        3 * l ^ 3 ≤ 1000000 * E := by
    have hE0 : 0 ≤ E := by
      have := m7; have : 0 ≤ l ^ 3 := by positivity
      linarith
    linarith
  have hsum := mul_le_mul_of_nonneg_left hB hWA
  have a1 := abs_add_le (w3 * s0 + 3 * (w2 * s1) + 3 * (w1 * s2)) (w0 * s3)
  have a2 := abs_add_le (w3 * s0 + 3 * (w2 * s1)) (3 * (w1 * s2))
  have a3 := abs_add_le (w3 * s0) (3 * (w2 * s1))
  have e : W₀ * A * (1000000 * E) = 1000000 * W₀ * A * E := by ring
  nlinarith

end BiluLinial.Tight.SecB
