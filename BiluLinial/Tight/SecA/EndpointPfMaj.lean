/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecA.EndpointDefs

/-!
# Coefficient majorants of the fibre polynomial (for `A-E1`)

`f ≪ F` (`epf_Maj f F`) means `|coeff f k| ≤ coeff F k` for every `k`. It is preserved by sums,
products, powers and derivatives, and gives `|f(u)| ≤ F(|u|)`. With `c = a g`:
`fibreDelta a x gvv gii ≪ (1 + c X)²` and `x - a(gvv gii - x²) X ≪ g (1 + c X)` whenever `|x| ≤ g`
and `|gvv gii - x²| ≤ g²`, so `fibrePoly ≪ g (1 + c X)^{4p-1}` and
`|Π^{(j)}(u)| ≤ g (4p-1)_j c^j (1 + c|u|)^{4p-1-j}` (`epf_fibrePoly_deriv_bound`). Consequences:
`|j! [t^j] Π| ≤ (4pa)^j g^{j+1}` (`epf_coeff_bound`) and, if `64 p a g ≤ 1` and `|u| ≤ 2`,
`|Π^{(5)}(u)| ≤ 2 (4pa)⁵ g⁶` (`epf_fifth_bound`, via `(1 + 1/(32p))^{4p} ≤ e^{1/8} < 2`).
-/

@[expose] public section

namespace BiluLinial.Tight.SecA

open Polynomial

/-- Coefficientwise majorant: `|coeff f k| ≤ coeff F k` for every `k`. -/
def epf_Maj (f F : ℝ[X]) : Prop := ∀ k, |f.coeff k| ≤ F.coeff k

theorem epf_Maj.nonneg {f F : ℝ[X]} (h : epf_Maj f F) (k : ℕ) : 0 ≤ F.coeff k :=
  (abs_nonneg _).trans (h k)

theorem epf_Maj.add {f F g H : ℝ[X]} (hf : epf_Maj f F) (hg : epf_Maj g H) :
    epf_Maj (f + g) (F + H) := fun k => by
  rw [coeff_add, coeff_add]
  exact (abs_add_le _ _).trans (add_le_add (hf k) (hg k))

theorem epf_Maj.neg {f F : ℝ[X]} (hf : epf_Maj f F) : epf_Maj (-f) F := fun k => by
  rw [coeff_neg, abs_neg]; exact hf k

theorem epf_Maj.sub {f F g H : ℝ[X]} (hf : epf_Maj f F) (hg : epf_Maj g H) :
    epf_Maj (f - g) (F + H) := by
  rw [sub_eq_add_neg]; exact hf.add hg.neg

theorem epf_Maj.mul {f F g H : ℝ[X]} (hf : epf_Maj f F) (hg : epf_Maj g H) :
    epf_Maj (f * g) (F * H) := fun k => by
  rw [coeff_mul, coeff_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  rw [abs_mul]
  exact mul_le_mul (hf _) (hg _) (abs_nonneg _) (hf.nonneg _)

theorem epf_Maj.one : epf_Maj 1 1 := fun k => by
  rw [coeff_one]; split_ifs <;> simp

theorem epf_Maj.pow {f F : ℝ[X]} (hf : epf_Maj f F) (m : ℕ) : epf_Maj (f ^ m) (F ^ m) := by
  induction m with
  | zero => simpa using epf_Maj.one
  | succ m ih => rw [pow_succ, pow_succ]; exact ih.mul hf

theorem epf_Maj.const {b B : ℝ} (h : |b| ≤ B) : epf_Maj (C b) (C B) := fun k => by
  simp only [coeff_C]; split_ifs <;> simp [h]

theorem epf_Maj.linear {b B : ℝ} (h : |b| ≤ B) : epf_Maj (C b * X) (C B * X) := fun k => by
  simp only [coeff_C_mul, coeff_X]; split_ifs <;> simp [h]

theorem epf_Maj.quad {b B : ℝ} (h : |b| ≤ B) : epf_Maj (C b * X ^ 2) (C B * X ^ 2) := fun k => by
  simp only [coeff_C_mul, coeff_X_pow]; split_ifs <;> simp [h]

theorem epf_Maj.derivative {f F : ℝ[X]} (hf : epf_Maj f F) :
    epf_Maj (Polynomial.derivative f) (Polynomial.derivative F) := fun k => by
  rw [coeff_derivative, coeff_derivative, abs_mul]
  have : |((k : ℝ) + 1)| = (k : ℝ) + 1 := abs_of_nonneg (by positivity)
  rw [this]
  exact mul_le_mul_of_nonneg_right (hf _) (by positivity)

theorem epf_Maj.iterate_derivative {f F : ℝ[X]} (hf : epf_Maj f F) (j : ℕ) :
    epf_Maj (Polynomial.derivative^[j] f) (Polynomial.derivative^[j] F) := by
  induction j with
  | zero => simpa using hf
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact ih.derivative

theorem epf_Maj.abs_eval_le {f F : ℝ[X]} (hf : epf_Maj f F) (u : ℝ) :
    |f.eval u| ≤ F.eval |u| := by
  rw [eval_eq_sum_range' (n := max f.natDegree F.natDegree + 1)
      (Nat.lt_succ_of_le (le_max_left _ _)) u,
    eval_eq_sum_range' (n := max f.natDegree F.natDegree + 1)
      (Nat.lt_succ_of_le (le_max_right _ _)) |u|]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [abs_mul, abs_pow]
  exact mul_le_mul_of_nonneg_right (hf k) (by positivity)

/-- `δ ≪ (1 + a g X)²`. -/
theorem epf_maj_delta {a x gvv gii g : ℝ} (ha : 0 ≤ a) (hx : |x| ≤ g)
    (hd : |gvv * gii - x ^ 2| ≤ g ^ 2) :
    epf_Maj (fibreDelta a x gvv gii) ((1 + C (a * g) * X) ^ 2) := by
  have e : (1 + C (a * g) * X) ^ 2 =
      1 + C (2 * a * g) * X + C (a ^ 2 * g ^ 2) * X ^ 2 := by
    simp only [map_mul, map_pow, map_ofNat]; ring
  rw [e]
  unfold fibreDelta
  refine (epf_Maj.one.add (epf_Maj.linear ?_)).sub (epf_Maj.quad ?_)
  · rw [abs_mul, abs_mul, abs_two, abs_of_nonneg ha]
    have := mul_le_mul_of_nonneg_left hx (by positivity : (0 : ℝ) ≤ 2 * a)
    linarith
  · rw [abs_mul, abs_of_nonneg (sq_nonneg a)]
    have := mul_le_mul_of_nonneg_left hd (sq_nonneg a)
    linarith

/-- The last factor `x - a (gvv gii - x²) X ≪ g (1 + a g X)`. -/
theorem epf_maj_last {a x gvv gii g : ℝ} (ha : 0 ≤ a) (hx : |x| ≤ g)
    (hd : |gvv * gii - x ^ 2| ≤ g ^ 2) :
    epf_Maj (C x - C (a * (gvv * gii - x ^ 2)) * X) (C g * (1 + C (a * g) * X)) := by
  have e : C g * (1 + C (a * g) * X) = C g + C (a * g ^ 2) * X := by
    simp only [map_mul, map_pow]; ring
  rw [e]
  refine (epf_Maj.const hx).sub (epf_Maj.linear ?_)
  rw [abs_mul, abs_of_nonneg ha]
  have := mul_le_mul_of_nonneg_left hd ha
  linarith

/-- `fibrePoly ≪ g (1 + a g X)^{4p-1}`. -/
theorem epf_maj_fibrePoly {p : ℕ} (hp : 1 ≤ p) {a x gvv gii y hvv hii g : ℝ} (ha : 0 ≤ a)
    (hx : |x| ≤ g) (hdx : |gvv * gii - x ^ 2| ≤ g ^ 2) (hy : |y| ≤ g)
    (hdy : |hvv * hii - y ^ 2| ≤ g ^ 2) :
    epf_Maj (fibrePoly p a x gvv gii y hvv hii) (C g * (1 + C (a * g) * X) ^ (4 * p - 1)) := by
  have h1 := (epf_maj_delta ha hx hdx).pow (p - 1)
  have h2 := (epf_maj_delta (x := -y) (gvv := hvv) (gii := hii) (g := g) ha (by rwa [abs_neg])
    (by rwa [neg_sq])).pow p
  have h3 := epf_maj_last ha hx hdx
  have h := (h1.mul h2).mul h3
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  have e : ((1 + C (a * g) * X) ^ 2) ^ (q + 1 - 1) * ((1 + C (a * g) * X) ^ 2) ^ (q + 1) *
      (C g * (1 + C (a * g) * X)) = C g * (1 + C (a * g) * X) ^ (4 * (q + 1) - 1) := by
    rw [show q + 1 - 1 = q by omega, show 4 * (q + 1) - 1 = 4 * q + 3 by omega]
    generalize (1 + C (a * g) * X) = Q
    ring
  rw [← e]
  exact h

/-- Derivatives of the majorant: `D^j (1 + cX)^m = (m)_j c^j (1 + cX)^{m-j}`. -/
theorem epf_iterate_derivative_pow (c : ℝ) (m j : ℕ) :
    Polynomial.derivative^[j] ((1 + C c * X) ^ m) =
      C ((m.descFactorial j : ℝ) * c ^ j) * (1 + C c * X) ^ (m - j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih, derivative_C_mul, derivative_pow]
    have hd : Polynomial.derivative (1 + C c * X) = C c := by simp
    rw [hd, Nat.descFactorial_succ, show m - (j + 1) = m - j - 1 by omega]
    push_cast
    simp only [map_mul, map_pow]
    ring

/-- `|Π^{(j)}(u)| ≤ g (4p-1)_j (ag)^j (1 + ag|u|)^{4p-1-j}`. -/
theorem epf_fibrePoly_deriv_bound {p : ℕ} (hp : 1 ≤ p) {a x gvv gii y hvv hii g : ℝ}
    (ha : 0 ≤ a) (hx : |x| ≤ g) (hdx : |gvv * gii - x ^ 2| ≤ g ^ 2) (hy : |y| ≤ g)
    (hdy : |hvv * hii - y ^ 2| ≤ g ^ 2) (j : ℕ) (u : ℝ) :
    |(Polynomial.derivative^[j] (fibrePoly p a x gvv gii y hvv hii)).eval u| ≤
      g * ((4 * p - 1).descFactorial j : ℝ) * (a * g) ^ j *
        (1 + a * g * |u|) ^ (4 * p - 1 - j) := by
  have h := ((epf_maj_fibrePoly hp ha hx hdx hy hdy).iterate_derivative j).abs_eval_le u
  rw [iterate_derivative_C_mul, epf_iterate_derivative_pow] at h
  refine h.trans (le_of_eq ?_)
  simp only [eval_mul, eval_C, eval_pow, eval_add, eval_one, eval_X]
  ring

theorem epf_eval_zero_iterate_derivative (f : ℝ[X]) (j : ℕ) :
    (Polynomial.derivative^[j] f).eval 0 = (j.factorial : ℝ) * f.coeff j := by
  rw [← coeff_zero_eq_eval_zero, coeff_iterate_derivative, zero_add, Nat.descFactorial_self,
    nsmul_eq_mul]

theorem epf_descFactorial_le {p : ℕ} (j : ℕ) :
    (((4 * p - 1).descFactorial j : ℕ) : ℝ) ≤ (4 * (p : ℝ)) ^ j := by
  have h1 := Nat.descFactorial_le_pow (4 * p - 1) j
  have h2 : (4 * p - 1) ^ j ≤ (4 * p) ^ j := Nat.pow_le_pow_left (by omega) j
  exact_mod_cast h1.trans h2

/-- `|𝒟_j| = |j! [t^j] Π| ≤ (4pa)^j g^{j+1}`. -/
theorem epf_coeff_bound {p : ℕ} (hp : 1 ≤ p) {a x gvv gii y hvv hii g : ℝ} (ha : 0 ≤ a)
    (hg : 0 ≤ g) (hx : |x| ≤ g) (hdx : |gvv * gii - x ^ 2| ≤ g ^ 2) (hy : |y| ≤ g)
    (hdy : |hvv * hii - y ^ 2| ≤ g ^ 2) (j : ℕ) :
    |(j.factorial : ℝ) * (fibrePoly p a x gvv gii y hvv hii).coeff j| ≤
      (4 * p * a) ^ j * g ^ (j + 1) := by
  rw [← epf_eval_zero_iterate_derivative]
  refine (epf_fibrePoly_deriv_bound hp ha hx hdx hy hdy j 0).trans ?_
  simp only [abs_zero, mul_zero, add_zero, one_pow, mul_one]
  calc g * (((4 * p - 1).descFactorial j : ℕ) : ℝ) * (a * g) ^ j
      ≤ g * (4 * (p : ℝ)) ^ j * (a * g) ^ j :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (epf_descFactorial_le j) hg)
          (pow_nonneg (mul_nonneg ha hg) j)
    _ = (4 * p * a) ^ j * g ^ (j + 1) := by ring

theorem epf_exp_eighth_lt_two : Real.exp (1 / 8) < 2 := by
  have h8 : Real.exp (1 / 8) ^ 8 = Real.exp 1 := by
    rw [← Real.exp_nat_mul]; norm_num
  have he := Real.exp_one_lt_d9
  by_contra hcon
  have : (2 : ℝ) ^ 8 ≤ Real.exp (1 / 8) ^ 8 := pow_le_pow_left₀ (by norm_num) (not_lt.mp hcon) 8
  rw [h8] at this
  norm_num at this
  linarith

/-- In the small regime `64 p a g ≤ 1`, `|Π^{(5)}(u)| ≤ 2 (4pa)⁵ g⁶` for `|u| ≤ 2`. -/
theorem epf_fifth_bound {p : ℕ} (hp : 1 ≤ p) {a x gvv gii y hvv hii g : ℝ} (ha : 0 ≤ a)
    (hg : 0 ≤ g) (hx : |x| ≤ g) (hdx : |gvv * gii - x ^ 2| ≤ g ^ 2) (hy : |y| ≤ g)
    (hdy : |hvv * hii - y ^ 2| ≤ g ^ 2) (hsmall : 64 * p * a * g ≤ 1) {u : ℝ} (hu : |u| ≤ 2) :
    |(Polynomial.derivative^[5] (fibrePoly p a x gvv gii y hvv hii)).eval u| ≤
      2 * (4 * p * a) ^ 5 * g ^ 6 := by
  refine (epf_fibrePoly_deriv_bound hp ha hx hdx hy hdy 5 u).trans ?_
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hag : 0 ≤ a * g := mul_nonneg ha hg
  have hp0 : (p : ℝ) ≠ 0 := ne_of_gt (by linarith)
  have hc : a * g * |u| ≤ 1 / (32 * p) := by
    rw [le_div_iff₀ (by positivity)]
    have h1 : a * g * |u| ≤ a * g * 2 := mul_le_mul_of_nonneg_left hu hag
    nlinarith [mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ 32 * p)]
  have hone : 1 ≤ 1 + a * g * |u| := by
    have := mul_nonneg hag (abs_nonneg u); linarith
  have hE : (1 + a * g * |u|) ^ (4 * p - 1 - 5) ≤ 2 := by
    have h1 : (1 + a * g * |u|) ^ (4 * p - 1 - 5) ≤ (1 + a * g * |u|) ^ (4 * p) :=
      pow_le_pow_right₀ hone (by omega)
    have h2 : (1 + a * g * |u|) ^ (4 * p) ≤ Real.exp (1 / (32 * p)) ^ (4 * p) := by
      refine pow_le_pow_left₀ (by linarith) ?_ _
      have := Real.add_one_le_exp (1 / (32 * p)); linarith
    have h3 : Real.exp (1 / (32 * p)) ^ (4 * p) = Real.exp (1 / 8) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; field_simp; ring
    linarith [epf_exp_eighth_lt_two]
  have hD := epf_descFactorial_le (p := p) 5
  have hpow : 0 ≤ (a * g) ^ 5 := pow_nonneg hag 5
  calc g * (((4 * p - 1).descFactorial 5 : ℕ) : ℝ) * (a * g) ^ 5 *
        (1 + a * g * |u|) ^ (4 * p - 1 - 5)
      ≤ g * (4 * (p : ℝ)) ^ 5 * (a * g) ^ 5 * 2 := by
        refine mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hD hg) hpow) hE
          (pow_nonneg (by linarith) _) (mul_nonneg (mul_nonneg hg (by positivity)) hpow)
    _ = 2 * (4 * p * a) ^ 5 * g ^ 6 := by ring

end BiluLinial.Tight.SecA
