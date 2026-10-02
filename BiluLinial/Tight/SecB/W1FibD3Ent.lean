/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecB.W1FibD3Wood

/-!
# TB.W1fib-d3: entry bounds on a ball, masked products

* `jb_entry_row`, `jb_entry_col`, `jb_entry_ball`: the Woodbury entry jets of `physInv y B(t)` with
  bounds `|M_xz| + c(|M_iz| + |M_jz|)` (row `x` in a ball containing `i, j` on which `|M| ≤ D`),
  `|M_xz| + c(|M_xi| + |M_xj|)` (column `z` in the ball) and `2661121 D³` (both in the ball),
  `c = 1330560 D²`.
* `jb_mulDiagMul`: the jet of `(X_e D_f X_n)_ab = Σ_x (X_e)_ax f_x (X_n)_xb` from row/column jets,
  bound `64 A_f Σ_x A_e(x) A_n(x)`; `jb_maskF`: the jet of `F_ji = (X_e)_ii U_ji - (X_e)_ji U_ii`.
* `sum_maj_le`: `Σ (|x| + c(|y| + |z|))(|x'| + c(|y'| + |z'|)) ≤ 9(1 + c)² R` when the six square
  sums are `≤ R` (Cauchy–Schwarz).
-/

@[expose] public section

namespace BiluLinial.Tight.SecB

open Matrix

theorem maj_pt {X Y Z X' Y' Z' c : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y) (hZ : 0 ≤ Z) (hX' : 0 ≤ X')
    (hY' : 0 ≤ Y') (hZ' : 0 ≤ Z') (hc : 0 ≤ c) :
    (X + c * (Y + Z)) * (X' + c * (Y' + Z')) ≤
      (1 + c) ^ 2 * (3 / 2) * (X ^ 2 + Y ^ 2 + Z ^ 2 + (X' ^ 2 + Y' ^ 2 + Z' ^ 2)) := by
  have a1 : X + c * (Y + Z) ≤ (1 + c) * (X + Y + Z) := by nlinarith [mul_nonneg hc hX]
  have a2 : X' + c * (Y' + Z') ≤ (1 + c) * (X' + Y' + Z') := by nlinarith [mul_nonneg hc hX']
  have p2 : 0 ≤ X' + c * (Y' + Z') := by positivity
  have b := mul_le_mul a1 a2 p2 (by positivity)
  have s1 : (X + Y + Z) ^ 2 ≤ 3 * (X ^ 2 + Y ^ 2 + Z ^ 2) := by
    nlinarith [sq_nonneg (X - Y), sq_nonneg (Y - Z), sq_nonneg (X - Z)]
  have s2 : (X' + Y' + Z') ^ 2 ≤ 3 * (X' ^ 2 + Y' ^ 2 + Z' ^ 2) := by
    nlinarith [sq_nonneg (X' - Y'), sq_nonneg (Y' - Z'), sq_nonneg (X' - Z')]
  have s3 := two_mul_le_add_sq (X + Y + Z) (X' + Y' + Z')
  have hc2 : 0 ≤ (1 + c) ^ 2 := sq_nonneg _
  calc (X + c * (Y + Z)) * (X' + c * (Y' + Z'))
      ≤ (1 + c) * (X + Y + Z) * ((1 + c) * (X' + Y' + Z')) := b
    _ = (1 + c) ^ 2 * ((X + Y + Z) * (X' + Y' + Z')) := by ring
    _ ≤ (1 + c) ^ 2 * (((X + Y + Z) ^ 2 + (X' + Y' + Z') ^ 2) / 2) :=
        mul_le_mul_of_nonneg_left (by linarith) hc2
    _ ≤ (1 + c) ^ 2 * ((3 * (X ^ 2 + Y ^ 2 + Z ^ 2) + 3 * (X' ^ 2 + Y' ^ 2 + Z' ^ 2)) / 2) :=
        mul_le_mul_of_nonneg_left (by linarith) hc2
    _ = (1 + c) ^ 2 * (3 / 2) * (X ^ 2 + Y ^ 2 + Z ^ 2 + (X' ^ 2 + Y' ^ 2 + Z' ^ 2)) := by ring

theorem sum_maj_le {ι : Type*} (s : Finset ι) (x y z x' y' z' : ι → ℝ) {c R : ℝ} (hc : 0 ≤ c)
    (hx : ∑ k ∈ s, x k ^ 2 ≤ R) (hy : ∑ k ∈ s, y k ^ 2 ≤ R) (hz : ∑ k ∈ s, z k ^ 2 ≤ R)
    (hx' : ∑ k ∈ s, x' k ^ 2 ≤ R) (hy' : ∑ k ∈ s, y' k ^ 2 ≤ R)
    (hz' : ∑ k ∈ s, z' k ^ 2 ≤ R) :
    ∑ k ∈ s, (|x k| + c * (|y k| + |z k|)) * (|x' k| + c * (|y' k| + |z' k|)) ≤
      9 * (1 + c) ^ 2 * R := by
  have hpt : ∀ k ∈ s, (|x k| + c * (|y k| + |z k|)) * (|x' k| + c * (|y' k| + |z' k|)) ≤
      (1 + c) ^ 2 * (3 / 2) * (x k ^ 2 + y k ^ 2 + z k ^ 2 + (x' k ^ 2 + y' k ^ 2 + z' k ^ 2)) := by
    intro k _
    have := maj_pt (abs_nonneg (x k)) (abs_nonneg (y k)) (abs_nonneg (z k)) (abs_nonneg (x' k))
      (abs_nonneg (y' k)) (abs_nonneg (z' k)) hc
    simpa only [sq_abs] using this
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [← Finset.mul_sum]
  simp only [Finset.sum_add_distrib]
  have hc2 : 0 ≤ (1 + c) ^ 2 * (3 / 2) := by positivity
  have := mul_le_mul_of_nonneg_left
    (show ∑ k ∈ s, x k ^ 2 + ∑ k ∈ s, y k ^ 2 + ∑ k ∈ s, z k ^ 2 +
      (∑ k ∈ s, x' k ^ 2 + ∑ k ∈ s, y' k ^ 2 + ∑ k ∈ s, z' k ^ 2) ≤ 6 * R by linarith) hc2
  linarith

section Gen

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The masked product `(X_e D_f X_n)_ab` from row and column jets. -/
theorem jb_mulDiagMul {U : Set ℝ} {Xe Xn : ℝ → Matrix n n ℝ} {f : ℝ → n → ℝ} {l : ℝ}
    (hl : 0 ≤ l) (a b : n) {FA FB Ff : n → ℕ → ℝ → ℝ} {Ae An : n → ℝ} {Af : ℝ}
    (he : ∀ x, JB U (fun t => Xe t a x) (FA x) (Ae x) l)
    (hn : ∀ x, JB U (fun t => Xn t x b) (FB x) (An x) l)
    (hf : ∀ x, JB U (fun t => f t x) (Ff x) Af l) (hAe : ∀ x, 0 ≤ Ae x) (hAn : ∀ x, 0 ≤ An x)
    (hAf : 0 ≤ Af) :
    ∃ F, JB U (fun t => (Xe t * diagonal (f t) * Xn t) a b) F (64 * Af * ∑ x, Ae x * An x) l := by
  have h := JB.sum Finset.univ fun x _ =>
    ((he x).mul (hf x) (hAe x) hAf hl).mul (hn x) (by have := hAe x; positivity) (hAn x) hl
  refine ⟨_, (h.congr fun t _ => ?_).mono (le_of_eq ?_) hl⟩
  · rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun x _ => by rw [Matrix.mul_diagonal]
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring

/-- The jet of `F_ji = (X_e)_ii U_ji - (X_e)_ji U_ii`, `U = X_e D_f X_n`. -/
theorem jb_maskF {U : Set ℝ} {Xe Xn : ℝ → Matrix n n ℝ} {f : ℝ → n → ℝ} {l : ℝ} (hl : 0 ≤ l)
    (j i : n) {FAj FAi FB Ff : n → ℕ → ℝ → ℝ} {Aej Aei An : n → ℝ} {Af : ℝ}
    {Fii Fji : ℕ → ℝ → ℝ} {Aii Aji : ℝ}
    (hej : ∀ x, JB U (fun t => Xe t j x) (FAj x) (Aej x) l)
    (hei : ∀ x, JB U (fun t => Xe t i x) (FAi x) (Aei x) l)
    (hn : ∀ x, JB U (fun t => Xn t x i) (FB x) (An x) l)
    (hf : ∀ x, JB U (fun t => f t x) (Ff x) Af l)
    (hii : JB U (fun t => Xe t i i) Fii Aii l) (hji : JB U (fun t => Xe t j i) Fji Aji l)
    (hAej : ∀ x, 0 ≤ Aej x) (hAei : ∀ x, 0 ≤ Aei x) (hAn : ∀ x, 0 ≤ An x) (hAf : 0 ≤ Af)
    (hAii : 0 ≤ Aii) (hAji : 0 ≤ Aji) :
    ∃ F, JB U (fun t => maskF (Xe t) (Xn t) (f t) j i) F
      (8 * (Aii * (64 * Af * ∑ x, Aej x * An x)) + 8 * (Aji * (64 * Af * ∑ x, Aei x * An x)))
      l := by
  obtain ⟨Fj, hUj⟩ := jb_mulDiagMul hl j i hej hn hf hAej hAn hAf
  obtain ⟨Fi, hUi⟩ := jb_mulDiagMul hl i i hei hn hf hAei hAn hAf
  have hS1 : 0 ≤ 64 * Af * ∑ x, Aej x * An x :=
    mul_nonneg (by positivity) (Finset.sum_nonneg fun x _ => mul_nonneg (hAej x) (hAn x))
  have hS2 : 0 ≤ 64 * Af * ∑ x, Aei x * An x :=
    mul_nonneg (by positivity) (Finset.sum_nonneg fun x _ => mul_nonneg (hAei x) (hAn x))
  exact ⟨_, ((hii.mul hUj hAii hS1 hl).sub (hji.mul hUi hAji hS2 hl)).congr fun t _ => rfl⟩

/-- Entry jets on a ball `Bl ∋ i, j` with `|M| ≤ D` on `Bl × Bl`. -/
theorem jb_entry_bounds {B : Matrix n n ℝ} (hB : B.PosDef) (y : n → ℝ) {i j : n} (hij : i ≠ j)
    {U : Set ℝ} {t₀ : ℝ} (hU : ∀ t ∈ U, |t - t₀| ≤ 3) {θ a D : ℝ} (hθ : |θ| ≤ a) (ha0 : 0 ≤ a)
    (ha1 : a ≤ 1) (hD : 1 ≤ D) (Bl : Finset n) (hiB : i ∈ Bl) (hjB : j ∈ Bl)
    (hball : ∀ x ∈ Bl, ∀ z ∈ Bl, |physInv y B x z| ≤ D)
    (hsm : a * (|physInv y B i i| + |physInv y B j j| + |physInv y B i j|) ≤ 1 / 32)
    (x z : n) :
    (x ∈ Bl → JB U (fun t => physInv y (B + ((t - t₀) * (θ * (Real.sqrt (y i) *
        Real.sqrt (y j)))) • SecA.edgeE i j) x z) (wJet (physInv y B) i j θ t₀ x z)
      (|physInv y B x z| + 1330560 * D ^ 2 * (|physInv y B i z| + |physInv y B j z|)) (a * D)) ∧
    (z ∈ Bl → JB U (fun t => physInv y (B + ((t - t₀) * (θ * (Real.sqrt (y i) *
        Real.sqrt (y j)))) • SecA.edgeE i j) x z) (wJet (physInv y B) i j θ t₀ x z)
      (|physInv y B x z| + 1330560 * D ^ 2 * (|physInv y B x i| + |physInv y B x j|)) (a * D)) ∧
    (x ∈ Bl → z ∈ Bl → JB U (fun t => physInv y (B + ((t - t₀) * (θ * (Real.sqrt (y i) *
        Real.sqrt (y j)))) • SecA.edgeE i j) x z) (wJet (physInv y B) i j θ t₀ x z)
      (2661121 * D ^ 3) (a * D)) := by
  have hl : 0 ≤ a * D := by positivity
  have hD0 : 0 ≤ D := by linarith
  have h := jb_physInv_edge hB y hij hU hθ ha0 ha1 hD (hball i hiB i hiB) (hball j hjB j hjB)
    (hball i hiB j hjB) hsm x z
  set M := physInv y B with hM
  have hc : 0 ≤ 665280 * D := by positivity
  have row : x ∈ Bl → |M x z| + 665280 * D * (|M x i * M i z| + |M x i * M j z| +
      |M x j * M i z| + |M x j * M j z|) ≤
      |M x z| + 1330560 * D ^ 2 * (|M i z| + |M j z|) := fun hx => by
    have h1 := hball x hx i hiB
    have h2 := hball x hx j hjB
    simp only [abs_mul]
    have t1 := mul_le_mul_of_nonneg_right h1 (abs_nonneg (M i z))
    have t2 := mul_le_mul_of_nonneg_right h1 (abs_nonneg (M j z))
    have t3 := mul_le_mul_of_nonneg_right h2 (abs_nonneg (M i z))
    have t4 := mul_le_mul_of_nonneg_right h2 (abs_nonneg (M j z))
    have := mul_le_mul_of_nonneg_left (add_le_add (add_le_add (add_le_add t1 t2) t3) t4) hc
    nlinarith
  have col : z ∈ Bl → |M x z| + 665280 * D * (|M x i * M i z| + |M x i * M j z| +
      |M x j * M i z| + |M x j * M j z|) ≤
      |M x z| + 1330560 * D ^ 2 * (|M x i| + |M x j|) := fun hz => by
    have h1 := hball i hiB z hz
    have h2 := hball j hjB z hz
    simp only [abs_mul]
    have t1 := mul_le_mul_of_nonneg_left h1 (abs_nonneg (M x i))
    have t2 := mul_le_mul_of_nonneg_left h2 (abs_nonneg (M x i))
    have t3 := mul_le_mul_of_nonneg_left h1 (abs_nonneg (M x j))
    have t4 := mul_le_mul_of_nonneg_left h2 (abs_nonneg (M x j))
    have := mul_le_mul_of_nonneg_left (add_le_add (add_le_add (add_le_add t1 t2) t3) t4) hc
    nlinarith
  refine ⟨fun hx => h.mono (row hx) hl, fun hz => h.mono (col hz) hl, fun hx hz => h.mono ?_ hl⟩
  refine (row hx).trans ?_
  have h0 := hball x hx z hz
  have h1 := hball i hiB z hz
  have h2 := hball j hjB z hz
  have hD3 : D ≤ D ^ 3 := by
    have h2 : 1 ≤ D ^ 2 := one_le_pow₀ hD
    calc D = D * 1 := (mul_one D).symm
      _ ≤ D * D ^ 2 := mul_le_mul_of_nonneg_left h2 hD0
      _ = D ^ 3 := by ring
  have hsum : 1330560 * D ^ 2 * (|M i z| + |M j z|) ≤ 1330560 * D ^ 2 * (2 * D) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have e : 1330560 * D ^ 2 * (2 * D) = 2661120 * D ^ 3 := by ring
  linarith

end Gen

end BiluLinial.Tight.SecB
