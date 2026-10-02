/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.Compare.Coeff
public import BiluLinial.Tight.Compare.Moments
public import BiluLinial.Tight.Compare.Taylor

/-!
# The one-dimensional Rademacher-to-Gaussian comparison

Part D (`docs/second_order_bilu_linial_tight.tex`, Section 1.2, proof of eq. (E4)): "in one
coordinate Taylor-expand through degree `2L+3`. Matching coefficients of `e^{t²/2}/cosh t` leaves a
remainder at most `C^{L+1} ‖∂^{2L+4} f‖_∞`." We take `n = L + 1` and get the constant `2`:

* `gauss_rad_compare_chain`: if `F 0, …, F (2n+2)` is a chain of successive derivatives on `ℝ`
  and `|F (2n+2)| ≤ M`, then `|𝖦 F₀ - Σ_{j ≤ n} c_j 𝖱 F_{2j}| ≤ 2M`;
* `gauss_rad_compare`: the same for `g ∈ C^{2n+2}` with `F m = g^{(m)}`;
* `gauss_eq_rad_poly`: exactness, `𝖦 p = Σ_{j ≤ n} c_j 𝖱 p^{(2j)}` for polynomials of degree
  `≤ 2n+1` (the case `M = 0`).

Proof: with `a_m = F m 0`, Taylor's bound gives
`F_{2j}(x) = Σ_{m < 2(n+1-j)} a_{2j+m} x^m/m! + r_j(x)` with
`|r_j(x)| ≤ M|x|^{2(n+1-j)}/(2(n+1-j))!`. The Gaussian moments give
`𝖦 F₀ = Σ_{k ≤ n} a_{2k}/(2^k k!) + 𝖦 r₀`, `|𝖦 r₀| ≤ M/(2^{n+1}(n+1)!) ≤ M/2`, and
`𝖱 F_{2j} = Σ_{i ≤ n-j} a_{2j+2i}/(2i)! + 𝖱 r_j`, `|𝖱 r_j| ≤ M/(2(n+1-j))!`. The recursion
`Σ_{j ≤ k} c_j/(2(k-j))! = 1/(2^k k!)` cancels the main terms, and
`Σ_j |c_j| M/(2(n+1-j))! ≤ M Σ_{m ≥ 1} 1/(2m)! ≤ 2M/3`.
-/

@[expose] public section

namespace BiluLinial.Tight

open MeasureTheory ProbabilityTheory Finset Set

/-- Splitting a sum over `range (2K)` into its even and odd terms. -/
theorem sum_range_two_mul (φ : ℕ → ℝ) (K : ℕ) :
    ∑ m ∈ range (2 * K), φ m = ∑ k ∈ range K, (φ (2 * k) + φ (2 * k + 1)) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [show 2 * (K + 1) = 2 * K + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ]
    ring

/-- Gaussian integral of an even-length Taylor polynomial. -/
theorem integral_taylorPoly_gauss (a : ℕ → ℝ) (K : ℕ) :
    ∫ x, ∑ m ∈ range (2 * K), a m * x ^ m / m.factorial ∂gaussianReal 0 1 =
      ∑ k ∈ range K, a (2 * k) / (2 ^ k * k.factorial) := by
  rw [integral_finsetSum _ (fun m _ =>
    ((integrable_pow_gaussianReal m).const_mul (a m)).div_const _)]
  simp_rw [integral_div, integral_const_mul]
  rw [sum_range_two_mul]
  apply sum_congr rfl
  intro k _
  rw [gauss_moment_even, gauss_moment_odd]
  field_simp
  ring

/-- Rademacher average of an even-length Taylor polynomial. -/
theorem rad_taylorPoly (a : ℕ → ℝ) (K : ℕ) :
    ((∑ m ∈ range (2 * K), a m * 1 ^ m / m.factorial) +
        ∑ m ∈ range (2 * K), a m * (-1) ^ m / m.factorial) / 2 =
      ∑ i ∈ range K, a (2 * i) / (2 * i).factorial := by
  rw [← sum_add_distrib, sum_range_two_mul, sum_div]
  apply sum_congr rfl
  intro i _
  simp only [one_pow, pow_succ, pow_mul]
  ring

/-- The coefficient identity behind the comparison:
`Σ_{j ≤ n} c_j Σ_{i ≤ n-j} b_{j+i}/(2i)! = Σ_{k ≤ n} b_k/(2^k k!)`. -/
theorem ecoef_double_sum (b : ℕ → ℝ) (n : ℕ) :
    ∑ j ∈ range (n + 1), ecoef j * ∑ i ∈ range (n + 1 - j), b (j + i) / (2 * i).factorial =
      ∑ k ∈ range (n + 1), b k / (2 ^ k * k.factorial) := by
  have h1 : ∀ j ∈ range (n + 1),
      ecoef j * ∑ i ∈ range (n + 1 - j), b (j + i) / (2 * i).factorial =
        ∑ k ∈ Ico j (n + 1), ecoef j * b k / (2 * (k - j)).factorial := by
    intro j _
    rw [sum_Ico_eq_sum_range, mul_sum]
    apply sum_congr rfl
    intro i _
    rw [show j + i - j = i by omega]
    ring
  rw [sum_congr rfl h1, range_eq_Ico, sum_Ico_Ico_comm]
  apply sum_congr rfl
  intro k _
  rw [← range_eq_Ico]
  calc ∑ j ∈ range (k + 1), ecoef j * b k / ((2 * (k - j)).factorial : ℝ)
      = b k * ∑ j ∈ range (k + 1), ecoef j / ((2 * (k - j)).factorial : ℝ) := by
        rw [mul_sum]; apply sum_congr rfl; intro j _; ring
    _ = b k / (2 ^ k * k.factorial) := by rw [ecoef_rec]; ring

/-- **One-dimensional comparison (chain form).** Let `F 0, …, F (2n+2)` be successive derivatives
on `ℝ` (`(F m)' = F (m+1)` for `m < 2n+2`) with `|F (2n+2)| ≤ M`. Then
`|𝖦 F₀ - Σ_{j ≤ n} c_j 𝖱 F_{2j}| ≤ 2M`, where `𝖦` is the standard Gaussian expectation and `𝖱` the
Rademacher expectation. (In the paper's notation `n = L+1` and the remainder is
`O(‖f^{(2L+4)}‖_∞)`.) -/
theorem gauss_rad_compare_chain (n : ℕ) (F : ℕ → ℝ → ℝ)
    (hF : ∀ m < 2 * n + 2, ∀ t, HasDerivAt (F m) (F (m + 1) t) t) (M : ℝ)
    (hM : ∀ t, |F (2 * n + 2) t| ≤ M) :
    |∫ t, F 0 t ∂gaussianReal 0 1 - ∑ j ∈ range (n + 1), ecoef j * ∫ t, F (2 * j) t ∂radReal| ≤
      2 * M := by
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  -- Taylor's bound for every `F (2j)`, `j ≤ n`.
  have hT : ∀ j ≤ n, ∀ x, |F (2 * j) x - ∑ m ∈ range (2 * (n + 1 - j)),
      F (2 * j + m) 0 * x ^ m / m.factorial| ≤
        M * |x| ^ (2 * (n + 1 - j)) / (2 * (n + 1 - j)).factorial := by
    intro j hj x
    have e : 2 * j + 2 * (n + 1 - j) = 2 * n + 2 := by omega
    have h := taylor_chain_bound (I := univ) ordConnected_univ (mem_univ 0) (2 * (n + 1 - j))
      (fun m => F (2 * j + m)) (fun m hm t _ => hF (2 * j + m) (by omega) t) M
      (fun t _ => by rw [e]; exact hM t) x (mem_univ x)
    simpa using h
  -- The Gaussian side.
  set P : ℝ → ℝ := fun x => ∑ m ∈ range (2 * (n + 1)), F m 0 * x ^ m / m.factorial with hP
  have hT0 : ∀ x, |F 0 x - P x| ≤ M * x ^ (2 * (n + 1)) / (2 * (n + 1)).factorial := by
    intro x
    have h := hT 0 (Nat.zero_le _) x
    simp only [mul_zero, Nat.sub_zero, zero_add] at h
    rwa [Even.pow_abs ⟨n + 1, by ring⟩] at h
  have hcont0 : Continuous (F 0) :=
    continuous_iff_continuousAt.2 fun t => (hF 0 (by omega) t).continuousAt
  have hPcont : Continuous P := by simp only [hP]; fun_prop
  have hPint : Integrable P (gaussianReal 0 1) :=
    integrable_finsetSum _ (fun m _ => ((integrable_pow_gaussianReal m).const_mul _).div_const _)
  have hBint : Integrable (fun x : ℝ => M * x ^ (2 * (n + 1)) / (2 * (n + 1)).factorial)
      (gaussianReal 0 1) := ((integrable_pow_gaussianReal _).const_mul M).div_const _
  have hr0 : Integrable (fun x => F 0 x - P x) (gaussianReal 0 1) :=
    Integrable.mono' hBint (hcont0.sub hPcont).aestronglyMeasurable
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hT0 x)
  have hG : ∫ t, F 0 t ∂gaussianReal 0 1 =
      ∫ t, (F 0 t - P t) ∂gaussianReal 0 1 +
        ∑ k ∈ range (n + 1), F (2 * k) 0 / (2 ^ k * k.factorial) := by
    rw [← integral_taylorPoly_gauss (fun m => F m 0), ← integral_add hr0 hPint]
    simp [hP]
  have hGr : |∫ t, (F 0 t - P t) ∂gaussianReal 0 1| ≤ M / 2 := by
    have h1 := norm_integral_le_of_norm_le hBint
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hT0 x)
    rw [Real.norm_eq_abs, integral_div, integral_const_mul,
      show 2 * (n + 1) = 2 * (n + 1) from rfl, gauss_moment_even] at h1
    refine h1.trans ?_
    have hfac : (0 : ℝ) < ((2 * (n + 1)).factorial : ℝ) := by positivity
    have h2 : (2 : ℝ) ≤ 2 ^ (n + 1) * ((n + 1).factorial : ℝ) := by
      have : (1 : ℝ) ≤ ((n + 1).factorial : ℝ) := Nat.one_le_cast.mpr (Nat.factorial_pos _)
      have : (2 : ℝ) ≤ 2 ^ (n + 1) := by
        calc (2 : ℝ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (n + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      nlinarith
    rw [mul_div_assoc', div_div, mul_comm ((2 ^ (n + 1) * ((n + 1).factorial : ℝ)))
      ((2 * (n + 1)).factorial : ℝ), ← div_div, mul_div_assoc, div_self hfac.ne', mul_one]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  -- The Rademacher side.
  set ρ : ℕ → ℝ := fun j => ∫ t, F (2 * j) t ∂radReal -
    ∑ i ∈ range (n + 1 - j), F (2 * j + 2 * i) 0 / (2 * i).factorial with hρ
  have hρb : ∀ j ∈ range (n + 1), |ρ j| ≤ M / (2 * (n + 1 - j)).factorial := by
    intro j hj
    have hj' : j ≤ n := by simp at hj; omega
    have h1 := hT j hj' 1
    have h2 := hT j hj' (-1)
    simp only [abs_one, abs_neg, one_pow, mul_one] at h1 h2
    have e := rad_taylorPoly (fun m => F (2 * j + m) 0) (n + 1 - j)
    simp only [one_pow, mul_one] at e
    simp only [hρ, integral_radReal]
    rw [← e]
    rw [abs_le] at h1 h2 ⊢
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hR : ∑ j ∈ range (n + 1), ecoef j * ∫ t, F (2 * j) t ∂radReal =
      ∑ k ∈ range (n + 1), F (2 * k) 0 / (2 ^ k * k.factorial) +
        ∑ j ∈ range (n + 1), ecoef j * ρ j := by
    rw [← ecoef_double_sum (fun k => F (2 * k) 0) n, ← sum_add_distrib]
    apply sum_congr rfl
    intro j _
    simp only [hρ, mul_add]
    rw [mul_sub]
    simp only [add_sub_cancel]
  have hRb : |∑ j ∈ range (n + 1), ecoef j * ρ j| ≤ 2 / 3 * M := by
    calc |∑ j ∈ range (n + 1), ecoef j * ρ j|
        ≤ ∑ j ∈ range (n + 1), |ecoef j * ρ j| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ range (n + 1), M * (1 / (2 * (n + 1 - j)).factorial) := by
          apply sum_le_sum
          intro j hj
          rw [abs_mul]
          calc |ecoef j| * |ρ j| ≤ 1 * (M / (2 * (n + 1 - j)).factorial) :=
                mul_le_mul (abs_ecoef_le_one j) (hρb j hj) (abs_nonneg _) zero_le_one
            _ = M * (1 / (2 * (n + 1 - j)).factorial) := by ring
      _ = M * ∑ m ∈ range (n + 1), (1 : ℝ) / (2 * (m + 1)).factorial := by
          rw [← mul_sum, ← sum_range_reflect]
          congr 1
          apply sum_congr rfl
          intro m hm
          simp at hm
          congr 4
          omega
      _ ≤ M * (2 / 3) := by gcongr; exact sum_inv_factorial_two_mul_succ_le _
      _ = 2 / 3 * M := by ring
  rw [hG, hR]
  have : ∫ t, (F 0 t - P t) ∂gaussianReal 0 1 +
      ∑ k ∈ range (n + 1), F (2 * k) 0 / (2 ^ k * k.factorial) -
      (∑ k ∈ range (n + 1), F (2 * k) 0 / (2 ^ k * k.factorial) +
        ∑ j ∈ range (n + 1), ecoef j * ρ j) =
      ∫ t, (F 0 t - P t) ∂gaussianReal 0 1 - ∑ j ∈ range (n + 1), ecoef j * ρ j := by ring
  rw [this]
  calc _ ≤ |∫ t, (F 0 t - P t) ∂gaussianReal 0 1| + |∑ j ∈ range (n + 1), ecoef j * ρ j| :=
        abs_sub _ _
    _ ≤ M / 2 + 2 / 3 * M := add_le_add hGr hRb
    _ ≤ 2 * M := by linarith

/-- **One-dimensional comparison.** For `g ∈ C^{2n+2}(ℝ)` with `|g^{(2n+2)}| ≤ M`,
`|𝖦 g - Σ_{j ≤ n} c_j (g^{(2j)}(1) + g^{(2j)}(-1))/2| ≤ 2M`. -/
theorem gauss_rad_compare (n : ℕ) (g : ℝ → ℝ) (hg : ContDiff ℝ ((2 * n + 2 : ℕ) : WithTop ℕ∞) g)
    (M : ℝ) (hM : ∀ t, |iteratedDeriv (2 * n + 2) g t| ≤ M) :
    |∫ t, g t ∂gaussianReal 0 1 - ∑ j ∈ range (n + 1),
        ecoef j * ((iteratedDeriv (2 * j) g 1 + iteratedDeriv (2 * j) g (-1)) / 2)| ≤ 2 * M := by
  have h := gauss_rad_compare_chain n (fun m => iteratedDeriv m g)
    (fun m hm t => by
      have hd := (hg.differentiable_iteratedDeriv m (by exact_mod_cast hm)) t
      rw [iteratedDeriv_succ]
      exact hd.hasDerivAt) M hM
  simpa [integral_radReal] using h

/-- **Exactness on polynomials.** For a real polynomial `p` of degree `≤ 2n+1`,
`𝖦 p = Σ_{j ≤ n} c_j (p^{(2j)}(1) + p^{(2j)}(-1))/2`. -/
theorem gauss_eq_rad_poly (n : ℕ) (p : Polynomial ℝ) (hp : p.natDegree ≤ 2 * n + 1) :
    ∫ t, p.eval t ∂gaussianReal 0 1 = ∑ j ∈ range (n + 1),
      ecoef j * (((Polynomial.derivative^[2 * j] p).eval 1 +
        (Polynomial.derivative^[2 * j] p).eval (-1)) / 2) := by
  have h := gauss_rad_compare_chain n (fun m t => (Polynomial.derivative^[m] p).eval t)
    (fun m _ t => by
      have := (Polynomial.derivative^[m] p).hasDerivAt t
      rwa [← Function.iterate_succ_apply' Polynomial.derivative m p] at this) 0
    (fun t => by
      rw [Polynomial.iterate_derivative_eq_zero (by omega)]
      simp)
  simp only [mul_zero] at h
  have h' := abs_nonpos_iff.mp h
  rw [sub_eq_zero] at h'
  simpa [integral_radReal] using h'

end BiluLinial.Tight
