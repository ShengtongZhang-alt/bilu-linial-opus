/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.Gauss.Basic

/-!
# Gaussian moments and Rademacher averages on `ℝ`

Part D (`docs/second_order_bilu_linial_tight.tex`, Section 1.2). One-dimensional facts used by
the comparisons (E1) and (E4):

* `gauss_moment_even`: `𝖦 x^{2k} = (2k)!/(2^k k!)`; `gauss_moment_odd`: `𝖦 x^{2k+1} = 0`;
* `integrable_pow_gaussianReal`: all monomials are Gaussian-integrable;
* `integral_radReal`: `𝖱 g = (g 1 + g (-1))/2` for every `g`; `integrable_radReal`.

The moments come from the moment generating function `t ↦ exp (t²/2)`
(`ProbabilityTheory.mgf_id_gaussianReal`, `ProbabilityTheory.iteratedDeriv_mgf_zero`) and the
recursion `h^{(n+2)}(t) = t h^{(n+1)}(t) + (n+1) h^{(n)}(t)` for `h(t) = exp (t²/2)`.
-/

@[expose] public section

namespace BiluLinial.Tight

open MeasureTheory ProbabilityTheory Finset

/-- `t ↦ exp (t²/2)`, the moment generating function of the standard Gaussian. -/
noncomputable def gaussMGF (t : ℝ) : ℝ := Real.exp (t ^ 2 / 2)

theorem contDiff_gaussMGF (n : WithTop ℕ∞) : ContDiff ℝ n gaussMGF := by
  unfold gaussMGF; fun_prop

theorem hasDerivAt_gaussMGF (t : ℝ) : HasDerivAt gaussMGF (t * gaussMGF t) t := by
  have h := ((hasDerivAt_pow 2 t).div_const 2).exp
  refine h.congr_deriv ?_
  unfold gaussMGF
  norm_num
  ring

theorem hasDerivAt_iteratedDeriv_gaussMGF (n : ℕ) (t : ℝ) :
    HasDerivAt (iteratedDeriv n gaussMGF) (iteratedDeriv (n + 1) gaussMGF t) t := by
  rw [iteratedDeriv_succ]
  exact ((contDiff_gaussMGF _).differentiable_iteratedDeriv' n t).hasDerivAt

/-- `h^{(n+2)}(t) = t h^{(n+1)}(t) + (n+1) h^{(n)}(t)` for `h(t) = exp (t²/2)`. -/
theorem iteratedDeriv_gaussMGF_rec (n : ℕ) (t : ℝ) :
    iteratedDeriv (n + 2) gaussMGF t =
      t * iteratedDeriv (n + 1) gaussMGF t + (n + 1) * iteratedDeriv n gaussMGF t := by
  induction n generalizing t with
  | zero =>
    have h1 : iteratedDeriv 1 gaussMGF = fun s => s * iteratedDeriv 0 gaussMGF s := by
      funext s
      rw [iteratedDeriv_one, iteratedDeriv_zero]
      exact (hasDerivAt_gaussMGF s).deriv
    have hd : HasDerivAt (fun s => s * iteratedDeriv 0 gaussMGF s)
        (1 * iteratedDeriv 0 gaussMGF t + t * iteratedDeriv 1 gaussMGF t) t :=
      (hasDerivAt_id t).mul (hasDerivAt_iteratedDeriv_gaussMGF 0 t)
    have h2 : deriv (iteratedDeriv 1 gaussMGF) t =
        1 * iteratedDeriv 0 gaussMGF t + t * iteratedDeriv 1 gaussMGF t := by
      conv_lhs => rw [h1]
      exact hd.deriv
    rw [show (0 + 2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, h2]
    push_cast
    ring
  | succ n ih =>
    have h1 : iteratedDeriv (n + 2) gaussMGF =
        fun s => s * iteratedDeriv (n + 1) gaussMGF s + (n + 1) * iteratedDeriv n gaussMGF s := by
      funext s; exact ih s
    have hd : HasDerivAt
        (fun s => s * iteratedDeriv (n + 1) gaussMGF s + (n + 1) * iteratedDeriv n gaussMGF s)
        (1 * iteratedDeriv (n + 1) gaussMGF t + t * iteratedDeriv (n + 1 + 1) gaussMGF t +
          (n + 1) * iteratedDeriv (n + 1) gaussMGF t) t :=
      ((hasDerivAt_id t).mul (hasDerivAt_iteratedDeriv_gaussMGF (n + 1) t)).add
        ((hasDerivAt_iteratedDeriv_gaussMGF n t).const_mul _)
    have h2 : deriv (iteratedDeriv (n + 2) gaussMGF) t =
        1 * iteratedDeriv (n + 1) gaussMGF t + t * iteratedDeriv (n + 1 + 1) gaussMGF t +
          (n + 1) * iteratedDeriv (n + 1) gaussMGF t := by
      conv_lhs => rw [h1]
      exact hd.deriv
    rw [show (n + 1 + 2 : ℕ) = (n + 2) + 1 from rfl, iteratedDeriv_succ, h2]
    push_cast
    ring

/-- The moments of the standard Gaussian are the derivatives of `exp (t²/2)` at `0`. -/
theorem integral_pow_gaussianReal (n : ℕ) :
    ∫ x, x ^ n ∂gaussianReal 0 1 = iteratedDeriv n gaussMGF 0 := by
  have h0 : (0 : ℝ) ∈ interior (integrableExpSet (fun x : ℝ => x) (gaussianReal 0 1)) := by simp
  have h := iteratedDeriv_mgf_zero h0 n
  rw [mgf_fun_id_gaussianReal] at h
  have e : (fun t : ℝ => Real.exp (0 * t + ((1 : NNReal) : ℝ) * t ^ 2 / 2)) = gaussMGF := by
    funext t; simp [gaussMGF]
  rw [e] at h
  rw [h]
  simp [Pi.pow_apply]

/-- All monomials are integrable against the standard Gaussian. -/
theorem integrable_pow_gaussianReal (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n) (gaussianReal 0 1) :=
  integrable_pow_of_mem_interior_integrableExpSet (X := fun x : ℝ => x) (by simp) n

theorem iteratedDeriv_gaussMGF_zero_zero : iteratedDeriv 0 gaussMGF 0 = 1 := by
  simp [gaussMGF]

theorem iteratedDeriv_gaussMGF_one_zero : iteratedDeriv 1 gaussMGF 0 = 0 := by
  rw [iteratedDeriv_one, (hasDerivAt_gaussMGF 0).deriv]; simp

/-- Even Gaussian moments: `𝖦 x^{2k} = (2k)!/(2^k k!)`. -/
theorem gauss_moment_even (k : ℕ) :
    ∫ x, x ^ (2 * k) ∂gaussianReal 0 1 = ((2 * k).factorial : ℝ) / (2 ^ k * k.factorial) := by
  rw [integral_pow_gaussianReal]
  induction k with
  | zero => simp [iteratedDeriv_gaussMGF_zero_zero]
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 by ring, iteratedDeriv_gaussMGF_rec, ih]
    simp only [zero_mul, zero_add]
    rw [show 2 * k + 2 = (2 * k + 1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ,
      Nat.factorial_succ k]
    push_cast
    field_simp
    ring

/-- Odd Gaussian moments vanish: `𝖦 x^{2k+1} = 0`. -/
theorem gauss_moment_odd (k : ℕ) : ∫ x, x ^ (2 * k + 1) ∂gaussianReal 0 1 = 0 := by
  rw [integral_pow_gaussianReal]
  induction k with
  | zero => simpa using iteratedDeriv_gaussMGF_one_zero
  | succ k ih =>
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by ring, iteratedDeriv_gaussMGF_rec, ih]
    simp

/-- Every function is integrable against the Rademacher law. -/
theorem integrable_radReal (g : ℝ → ℝ) : Integrable g radReal := by
  unfold radReal
  exact ((integrable_dirac (by simp)).add_measure (integrable_dirac (by simp))).smul_measure
    (by simp)

/-- The Rademacher average: `𝖱 g = (g 1 + g (-1))/2`. -/
theorem integral_radReal (g : ℝ → ℝ) : ∫ x, g x ∂radReal = (g 1 + g (-1)) / 2 := by
  unfold radReal
  rw [integral_smul_measure, integral_add_measure (integrable_dirac (by simp))
    (integrable_dirac (by simp)), integral_dirac, integral_dirac]
  simp only [ENNReal.toReal_inv, smul_eq_mul]
  norm_num
  ring

end BiluLinial.Tight
