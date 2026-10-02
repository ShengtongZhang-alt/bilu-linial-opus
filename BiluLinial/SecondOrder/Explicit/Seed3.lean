/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import Mathlib

/-!
# The 3 × 3 triangle matrix

Blueprint node `C2-seed3` (source Section 6: "If the triangle sign product is `η`, the root
response is `g_η = (b - 2/(a - η))⁻¹`"). After eliminating the attached trees, the triangle seed's
Schur complement on `(o, v₁, v₂)` is

```
M = [[ b, -x, -y],
     [-x,  a, -w],
     [-y, -w,  a]]
```

with signs `x, y, w = ±1` (`x = A_{o v₁}`, `y = A_{o v₂}`, `w = A_{v₁ v₂}`). With `τ = w x y`:
the `(v₁, v₂)` block `[[a, -w], [-w, a]]` is positive definite when `a > 1`, its Schur term is
`(a x² + 2 w x y + a y²) / (a² - w²) = 2 (a + τ) / (a² - 1) = 2 / (a - τ)`, so `M ≻ 0` iff
`b - 2/(a - τ) > 0`, and then `(M⁻¹)_{oo} = 1 / (b - 2/(a - τ))`.
-/

@[expose] public section

namespace BiluLinial.SecondOrder.Explicit

open Matrix

/-- The quadratic form of the triangle matrix as a sum of three weighted squares (eliminating
`v₂`, then `v₁`), where `b = D + S` and `S` is the Schur term of the block on `(v₁, v₂)`. -/
private lemma seed3_quad_identity {a b D x y w : ℝ} (v0 v1 v2 : ℝ) (ha : a ≠ 0)
    (haw : a ^ 2 - w ^ 2 ≠ 0)
    (hb : b = D + (a * x ^ 2 + 2 * w * x * y + a * y ^ 2) / (a ^ 2 - w ^ 2)) :
    b * v0 ^ 2 - 2 * x * v0 * v1 - 2 * y * v0 * v2 + a * v1 ^ 2 - 2 * w * v1 * v2 + a * v2 ^ 2
      = a * (v2 - (y * v0 + w * v1) / a) ^ 2
        + (a ^ 2 - w ^ 2) / a * (v1 - (a * x + w * y) / (a ^ 2 - w ^ 2) * v0) ^ 2
        + D * v0 ^ 2 := by
  subst hb
  field_simp
  ring

/-- An explicit solution of `M u = e₀`. -/
private lemma seed3_inv_col {a b D x y w : ℝ} (haw : a ^ 2 - w ^ 2 ≠ 0) (hD : D ≠ 0)
    (hb : b = D + (a * x ^ 2 + 2 * w * x * y + a * y ^ 2) / (a ^ 2 - w ^ 2)) :
    (!![b, -x, -y; -x, a, -w; -y, -w, a] : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ
      ![1 / D, (a * x + w * y) / (D * (a ^ 2 - w ^ 2)),
        (w * x + a * y) / (D * (a ^ 2 - w ^ 2))] = Pi.single 0 1 := by
  subst hb
  ext i
  fin_cases i
  all_goals
    simp [mulVec, dotProduct, Fin.sum_univ_three]
    field_simp
    ring

theorem seed3 {a b x y w : ℝ} (hx : x ^ 2 = 1) (hy : y ^ 2 = 1) (hw : w ^ 2 = 1) (ha : 1 < a)
    (hb : 0 < b - 2 / (a - w * x * y)) :
    (!![b, -x, -y; -x, a, -w; -y, -w, a] : Matrix (Fin 3) (Fin 3) ℝ).PosDef ∧
      (!![b, -x, -y; -x, a, -w; -y, -w, a] : Matrix (Fin 3) (Fin 3) ℝ)⁻¹ 0 0 =
        1 / (b - 2 / (a - w * x * y)) := by
  have ht : (w * x * y) ^ 2 = 1 := by linear_combination x ^ 2 * y ^ 2 * hw + y ^ 2 * hx + hy
  have ht1 : w * x * y ≤ 1 := by nlinarith
  have hs : 0 < a - w * x * y := by linarith
  have ha0 : 0 < a := by linarith
  have ha2 : 0 < a ^ 2 - w ^ 2 := by rw [hw]; nlinarith
  have hS : (a * x ^ 2 + 2 * w * x * y + a * y ^ 2) / (a ^ 2 - w ^ 2) = 2 / (a - w * x * y) := by
    rw [div_eq_div_iff ha2.ne' hs.ne', hx, hy, hw]
    linear_combination (-2) * ht
  obtain ⟨D, hD_def⟩ : ∃ D, D = b - 2 / (a - w * x * y) := ⟨_, rfl⟩
  rw [← hD_def] at hb ⊢
  have hb' : b = D + (a * x ^ 2 + 2 * w * x * y + a * y ^ 2) / (a ^ 2 - w ^ 2) := by
    rw [hS, hD_def]
    ring
  have hk2 : 0 < (a ^ 2 - w ^ 2) / a := div_pos ha2 ha0
  have hM : (!![b, -x, -y; -x, a, -w; -y, -w, a] : Matrix (Fin 3) (Fin 3) ℝ).PosDef := by
    refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
    · ext i j
      fin_cases i <;> fin_cases j <;> simp
    intro v hv
    have hQ : star v ⬝ᵥ ((!![b, -x, -y; -x, a, -w; -y, -w, a] : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v) =
        b * v 0 ^ 2 - 2 * x * v 0 * v 1 - 2 * y * v 0 * v 2 + a * v 1 ^ 2 - 2 * w * v 1 * v 2
          + a * v 2 ^ 2 := by
      simp [mulVec, dotProduct, Fin.sum_univ_three]
      ring
    rw [hQ, seed3_quad_identity (v 0) (v 1) (v 2) ha0.ne' ha2.ne' hb']
    by_contra hle
    push Not at hle
    have h2 := mul_nonneg ha0.le (sq_nonneg (v 2 - (y * v 0 + w * v 1) / a))
    have h1 := mul_nonneg hk2.le
      (sq_nonneg (v 1 - (a * x + w * y) / (a ^ 2 - w ^ 2) * v 0))
    have h0 := mul_nonneg hb.le (sq_nonneg (v 0))
    have sq0 {k s : ℝ} (hk : 0 < k) (h : k * s ^ 2 = 0) : s = 0 := by
      rcases mul_eq_zero.mp h with h | h
      · exact absurd h hk.ne'
      · exact pow_eq_zero_iff two_ne_zero |>.mp h
    have e0 : v 0 = 0 := sq0 hb (by linarith)
    have e1 : v 1 = 0 := by
      have := sq0 hk2
        (by linarith : (a ^ 2 - w ^ 2) / a * (v 1 - (a * x + w * y) / (a ^ 2 - w ^ 2) * v 0) ^ 2
          = 0)
      simpa [e0] using this
    have e2 : v 2 = 0 := by
      have := sq0 ha0 (by linarith : a * (v 2 - (y * v 0 + w * v 1) / a) ^ 2 = 0)
      simpa [e0, e1] using this
    apply hv
    ext i
    fin_cases i <;> simp [e0, e1, e2]
  refine ⟨hM, ?_⟩
  have hu := seed3_inv_col ha2.ne' hb.ne' hb'
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp hM.isUnit
  have key := congrFun (congrArg (fun u => (!![b, -x, -y; -x, a, -w; -y, -w, a] :
    Matrix (Fin 3) (Fin 3) ℝ)⁻¹ *ᵥ u) hu) 0
  simp only [mulVec_mulVec, nonsing_inv_mul _ hdet, one_mulVec, mulVec_single_one] at key
  simpa using key.symm

end BiluLinial.SecondOrder.Explicit
