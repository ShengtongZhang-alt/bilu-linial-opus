/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecA.Endpoint
public import BiluLinial.Tight.SecA.Moments

/-!
# (E1) at a capped point, with the explicit endpoint derivatives (nodes `A-K3`, `A-E1CP`)

Source lines 261–293 and 1370–1391; AUDIT-A §2.2, AUDIT-D §3.1 (D3).

* `A-K3` (`fibrePoly_coeff_one`, `fibrePoly_coeff_three`): the endpoint derivatives of the fibre
  polynomial, `𝒟₁ x = a(-P + (2p-1) x² - 2p x z)` and `𝒟₃ x = 3! [t³] Π = a³ K(x, z, P, Q)` with
  `K = Kpoly` of `Tight/Contact/Defs.lean` (`P = G⁺_vv G⁺_ii`, `Q = G⁻_vv G⁻_ii`). Proof: the low
  coefficients of `(1 + b t + c t²)^n` are `1, nb, nc + C(n,2) b², n(n-1) bc + C(n,3) b³`; collect.
  Checked in exact rational arithmetic for `p = 2, …, 9` (200 random instances).
* `A-E1CP` (`CapPoint.endpoint_E1_cp`): at a capped point,
  `|E[ξ_i x_i] - a(-E P_i + (2p-1) E x_i² - 2p E x_i z_i) + (a³/3) E K_i| ≤ 4·10¹¹ p⁵ a⁵`.
  Proof: `A-E1`, `A-K3`, and `E g*⁶ ≤ Σ_{x ∈ {v,i}, ±} E (G^±_xx)⁶ ≤ 4 (s (1 + 2ε))⁶ ≤ 275`
  ((M1) with `k = 6`, `G_xx = y_x h_x ≤ s h_x`, `s ≤ 2`).
-/

@[expose] public section

universe u

namespace BiluLinial.Tight

open Polynomial

namespace SecA

theorem coeff_mul_one_eq (f g : ℝ[X]) :
    (f * g).coeff 1 = f.coeff 0 * g.coeff 1 + f.coeff 1 * g.coeff 0 := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ]

theorem coeff_mul_two_eq (f g : ℝ[X]) :
    (f * g).coeff 2 = f.coeff 0 * g.coeff 2 + f.coeff 1 * g.coeff 1 + f.coeff 2 * g.coeff 0 := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ]

theorem coeff_mul_three_eq (f g : ℝ[X]) :
    (f * g).coeff 3 = f.coeff 0 * g.coeff 3 + f.coeff 1 * g.coeff 2 + f.coeff 2 * g.coeff 1 +
      f.coeff 3 * g.coeff 0 := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ]

/-- The low coefficients of `f^n` when `f = 1 + b X + c X² + O(X⁴)`. -/
theorem coeff_pow_low {f : ℝ[X]} {b c : ℝ} (h0 : f.coeff 0 = 1) (h1 : f.coeff 1 = b)
    (h2 : f.coeff 2 = c) (h3 : f.coeff 3 = 0) (n : ℕ) :
    (f ^ n).coeff 0 = 1 ∧ (f ^ n).coeff 1 = n * b ∧
      (f ^ n).coeff 2 = n * c + n * (n - 1) / 2 * b ^ 2 ∧
      (f ^ n).coeff 3 = n * (n - 1) * b * c + n * (n - 1) * (n - 2) / 6 * b ^ 3 := by
  induction n with
  | zero => simp [coeff_one]
  | succ n ih =>
    obtain ⟨e0, e1, e2, e3⟩ := ih
    rw [pow_succ, mul_coeff_zero, coeff_mul_one_eq, coeff_mul_two_eq, coeff_mul_three_eq, e0, e1,
      e2, e3, h0, h1, h2, h3]
    push_cast
    refine ⟨by ring, by ring, by ring, by ring⟩

theorem fibreDelta_coeff (a x gvv gii : ℝ) :
    (fibreDelta a x gvv gii).coeff 0 = 1 ∧ (fibreDelta a x gvv gii).coeff 1 = 2 * a * x ∧
      (fibreDelta a x gvv gii).coeff 2 = -(a ^ 2 * (gvv * gii - x ^ 2)) ∧
      (fibreDelta a x gvv gii).coeff 3 = 0 := by
  simp only [fibreDelta, coeff_add, coeff_sub, coeff_one, coeff_C_mul, coeff_X, coeff_X_pow]
  norm_num

theorem fibreLin_coeff (x k : ℝ) :
    (C x - C k * X : ℝ[X]).coeff 0 = x ∧ (C x - C k * X : ℝ[X]).coeff 1 = -k ∧
      (C x - C k * X : ℝ[X]).coeff 2 = 0 ∧ (C x - C k * X : ℝ[X]).coeff 3 = 0 := by
  simp [coeff_X, coeff_C]

/-- `A-K3`: `𝒟₁ x = a(-P + (2p-1) x² - 2p x z)`. -/
theorem fibrePoly_coeff_one {p : ℕ} (hp : 1 ≤ p) (a x gvv gii y hvv hii : ℝ) :
    (fibrePoly p a x gvv gii y hvv hii).coeff 1 =
      a * (-(gvv * gii) + (2 * (p : ℝ) - 1) * x ^ 2 - 2 * (p : ℝ) * x * y) := by
  obtain ⟨a0, a1, a2, a3⟩ := fibreDelta_coeff a x gvv gii
  obtain ⟨b0, b1, b2, b3⟩ := fibreDelta_coeff a (-y) hvv hii
  obtain ⟨A0, A1, -, -⟩ := coeff_pow_low a0 a1 a2 a3 (p - 1)
  obtain ⟨B0, B1, -, -⟩ := coeff_pow_low b0 b1 b2 b3 p
  obtain ⟨l0, l1, -, -⟩ := fibreLin_coeff x (a * (gvv * gii - x ^ 2))
  rw [fibrePoly, coeff_mul_one_eq, mul_coeff_zero, coeff_mul_one_eq, A0, A1, B0, B1, l0, l1,
    Nat.cast_sub hp, Nat.cast_one]
  ring

/-- `A-K3`: `𝒟₃ x = 3! [t³] Π = a³ K(x, z, P, Q)`. -/
theorem fibrePoly_coeff_three {p : ℕ} (hp : 1 ≤ p) (a x gvv gii y hvv hii : ℝ) :
    6 * (fibrePoly p a x gvv gii y hvv hii).coeff 3 =
      a ^ 3 * Kpoly p x y (gvv * gii) (hvv * hii) := by
  obtain ⟨a0, a1, a2, a3⟩ := fibreDelta_coeff a x gvv gii
  obtain ⟨b0, b1, b2, b3⟩ := fibreDelta_coeff a (-y) hvv hii
  obtain ⟨A0, A1, A2, A3⟩ := coeff_pow_low a0 a1 a2 a3 (p - 1)
  obtain ⟨B0, B1, B2, B3⟩ := coeff_pow_low b0 b1 b2 b3 p
  obtain ⟨l0, l1, l2, l3⟩ := fibreLin_coeff x (a * (gvv * gii - x ^ 2))
  rw [fibrePoly, coeff_mul_three_eq, mul_coeff_zero, coeff_mul_one_eq, coeff_mul_two_eq,
    coeff_mul_three_eq, A0, A1, A2, A3, B0, B1, B2, B3, l0, l1, l2, l3,
    Nat.cast_sub hp, Nat.cast_one]
  simp only [Kpoly]
  ring

end SecA

namespace CapPoint

variable {d p : ℕ} (cp : CapPoint.{u} d p)

/-- `A-E1CP`: (E1) at a capped point with the explicit endpoint derivatives. -/
theorem endpoint_E1_cp (hR : RegA d p) {v : cp.V} (hv : v ∈ cp.S) {i : cp.V}
    (hi : i ∈ cp.N v) :
    |cp.E (fun σ => sgn σ v i * cp.gp σ v i) -
        aOf d p * (-(cp.E fun σ => cp.gp σ v v * cp.gp σ i i) +
          (2 * (p : ℝ) - 1) * (cp.E fun σ => cp.gp σ v i ^ 2) -
          2 * (p : ℝ) * (cp.E fun σ => cp.gp σ v i * cp.gm σ v i)) +
        aOf d p ^ 3 / 3 * (cp.E fun σ => Kpoly p (cp.gp σ v i) (cp.gm σ v i)
          (cp.gp σ v v * cp.gp σ i i) (cp.gm σ v v * cp.gm σ i i))| ≤
      4e11 * (p : ℝ) ^ 5 * aOf d p ^ 5 := by
  have hp1 : 1 ≤ p := le_trans (by norm_num) hR.treg.two_le_p
  have ha := hR.treg.aOf_pos
  have hZ := cp.Zw_pos hR
  have hE1 := SecA.endpoint_E1 cp.G hp1 ha cp.yp_nonneg cp.ym_nonneg hZ hv hi
  -- the endpoint derivatives
  have hD1 : lawE cp.G p (aOf d p) cp.yp cp.ym cp.S
      (SecA.fibreD cp.G p (aOf d p) cp.yp cp.ym cp.S v i 1) =
      aOf d p * ((2 * (p : ℝ) - 1) * (cp.E fun σ => cp.gp σ v i ^ 2) -
        (cp.E fun σ => cp.gp σ v v * cp.gp σ i i) -
        2 * (p : ℝ) * (cp.E fun σ => cp.gp σ v i * cp.gm σ v i)) := by
    rw [lawE_congr cp.G (g := fun σ => aOf d p * (((2 * (p : ℝ) - 1) * cp.gp σ v i ^ 2 -
        cp.gp σ v v * cp.gp σ i i) - 2 * (p : ℝ) * (cp.gp σ v i * cp.gm σ v i))) fun σ _ => by
      simp only [SecA.fibreD, Nat.factorial_one, Nat.cast_one, one_mul,
        SecA.fibrePoly_coeff_one hp1, CapPoint.gp, CapPoint.gm]
      ring]
    unfold CapPoint.E
    rw [lawE_const_mul, lawE_sub, lawE_sub, lawE_const_mul, lawE_const_mul]
  have hD3 : lawE cp.G p (aOf d p) cp.yp cp.ym cp.S
      (SecA.fibreD cp.G p (aOf d p) cp.yp cp.ym cp.S v i 3) =
      aOf d p ^ 3 * (cp.E fun σ => Kpoly p (cp.gp σ v i) (cp.gm σ v i)
          (cp.gp σ v v * cp.gp σ i i) (cp.gm σ v v * cp.gm σ i i)) := by
    rw [lawE_congr cp.G (g := fun σ => aOf d p ^ 3 * Kpoly p (cp.gp σ v i) (cp.gm σ v i)
        (cp.gp σ v v * cp.gp σ i i) (cp.gm σ v v * cp.gm σ i i)) fun σ _ => by
      have h3 := SecA.fibrePoly_coeff_three hp1 (aOf d p) (cp.gp σ v i) (cp.gp σ v v)
        (cp.gp σ i i) (cp.gm σ v i) (cp.gm σ v v) (cp.gm σ i i)
      simp only [SecA.fibreD]
      rw [show ((Nat.factorial 3 : ℕ) : ℝ) = 6 by norm_num]
      exact h3]
    unfold CapPoint.E
    rw [lawE_const_mul]
  -- sixth moments
  have hp12 : 2 * 6 ≤ p := le_trans (by norm_num) hR.treg.hp
  have hε := SecA.epsP_le hR.treg
  have hε0 := SecA.epsP_nonneg hR.treg
  have hs2 := SecA.sOf_le_two hR.treg
  have hc6 : (1 + 2 * epsP d p) ^ 6 ≤ 107 / 100 := by
    have h1 : 1 + 2 * epsP d p ≤ 101 / 100 := by linarith
    calc (1 + 2 * epsP d p) ^ 6 ≤ (101 / 100 : ℝ) ^ 6 :=
          pow_le_pow_left₀ (by linarith) h1 6
      _ ≤ 107 / 100 := by norm_num
  have hmom : ∀ x ∈ cp.S, (cp.E fun σ => cp.gp σ x x ^ 6) ≤ 69 ∧
      (cp.E fun σ => cp.gm σ x x ^ 6) ≤ 69 := by
    intro x hx
    obtain ⟨m1, m2⟩ := cp.h_moment hR hx (by norm_num) hp12
    have hyx := (cp.inCube_yp hR x).2.trans hs2
    have hyx' := (cp.inCube_ym hR x).2.trans hs2
    have hy0 := cp.yp_nonneg x
    have hy0' := cp.ym_nonneg x
    constructor
    · have e : (cp.E fun σ => cp.gp σ x x ^ 6) = cp.yp x ^ 6 * cp.E (fun σ => cp.hp σ x ^ 6) := by
        unfold CapPoint.E
        rw [← lawE_const_mul]
        refine congrArg _ (funext fun σ => ?_)
        rw [CapPoint.gp, SecA.greenP_self cp.G hy0, CapPoint.hp, mul_pow]
      rw [e]
      have : cp.yp x ^ 6 ≤ 64 := by
        calc cp.yp x ^ 6 ≤ 2 ^ 6 := pow_le_pow_left₀ hy0 hyx 6
          _ = 64 := by norm_num
      have h0 : 0 ≤ cp.E (fun σ => cp.hp σ x ^ 6) := by
        unfold CapPoint.E
        exact lawE_nonneg cp.G fun σ _ => by positivity
      nlinarith [pow_nonneg hy0 6]
    · have e : (cp.E fun σ => cp.gm σ x x ^ 6) = cp.ym x ^ 6 * cp.E (fun σ => cp.hm σ x ^ 6) := by
        unfold CapPoint.E
        rw [← lawE_const_mul]
        refine congrArg _ (funext fun σ => ?_)
        rw [CapPoint.gm, SecA.greenP_self cp.G hy0', CapPoint.hm, mul_pow]
      rw [e]
      have : cp.ym x ^ 6 ≤ 64 := by
        calc cp.ym x ^ 6 ≤ 2 ^ 6 := pow_le_pow_left₀ hy0' hyx' 6
          _ = 64 := by norm_num
      have h0 : 0 ≤ cp.E (fun σ => cp.hm σ x ^ 6) := by
        unfold CapPoint.E
        exact lawE_nonneg cp.G fun σ _ => by positivity
      nlinarith [pow_nonneg hy0' 6]
  have hiS : i ∈ cp.S := (Finset.mem_filter.1 hi).1
  have hg6 : lawE cp.G p (aOf d p) cp.yp cp.ym cp.S
      (fun σ => SecA.gStar cp.G (aOf d p) cp.yp cp.ym cp.S v i σ ^ 6) ≤ 276 := by
    have hpt : ∀ σ, SecA.gStar cp.G (aOf d p) cp.yp cp.ym cp.S v i σ ^ 6 ≤
        cp.gp σ v v ^ 6 + cp.gp σ i i ^ 6 + (cp.gm σ v v ^ 6 + cp.gm σ i i ^ 6) := by
      intro σ
      have hmax : ∀ x y : ℝ, max x y ^ 6 ≤ x ^ 6 + y ^ 6 := by
        intro x y
        rcases le_total x y with h | h
        · rw [max_eq_right h]; nlinarith [pow_two_nonneg (x ^ 3)]
        · rw [max_eq_left h]; nlinarith [pow_two_nonneg (y ^ 3)]
      simp only [SecA.gStar]
      refine (hmax _ _).trans (add_le_add (hmax _ _) (hmax _ _))
    have h1 := SecA.lawE_le_of_supp cp.G (p := p) (a := aOf d p) (yp := cp.yp) (ym := cp.ym)
      (S := cp.S) fun σ _ => hpt σ
    rw [lawE_add, lawE_add, lawE_add] at h1
    obtain ⟨a1, a2⟩ := hmom v hv
    obtain ⟨b1, b2⟩ := hmom i hiS
    unfold CapPoint.E at a1 a2 b1 b2
    linarith
  rw [hD1, hD3] at hE1
  have hpa : 0 ≤ (p : ℝ) ^ 5 * aOf d p ^ 5 := by positivity
  have hfin : 1.15e9 * (p : ℝ) ^ 5 * aOf d p ^ 5 * lawE cp.G p (aOf d p) cp.yp cp.ym cp.S
      (fun σ => SecA.gStar cp.G (aOf d p) cp.yp cp.ym cp.S v i σ ^ 6) ≤
      4e11 * (p : ℝ) ^ 5 * aOf d p ^ 5 := by
    have := mul_le_mul_of_nonneg_left hg6 hpa
    nlinarith
  refine le_trans (le_of_eq ?_) (hE1.trans hfin)
  congr 1
  unfold CapPoint.E CapPoint.gp CapPoint.gm
  ring

end CapPoint

end BiluLinial.Tight
