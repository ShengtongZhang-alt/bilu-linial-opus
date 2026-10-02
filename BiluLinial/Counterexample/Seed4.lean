/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.ChallengeDefs

/-!
# The 4 × 4 seed matrix

Blueprint node `B-seed4` (source Step 6). After eliminating the attached trees, the seed's Schur
complement on `(o, v₀, v₁, v₂)` is

```
M = [[ a, -x,  0,  0],
     [-x,  b, -y, -z],
     [ 0, -y,  a, -w],
     [ 0, -z, -w,  a]]
```

with signs `x, y, z, w = ±1`. With `τ = w y z` (the sign of the triangle), eliminating `v₁, v₂`
then `v₀` gives `(M⁻¹)_{oo} = 1 / (a - 1 / (b - 2 / (a - τ)))`.
-/

@[expose] public section

namespace BiluLinial

open Matrix

/-- The quadratic form of the seed matrix as a sum of four weighted squares (an `LDLᵀ`
decomposition eliminating `v₃, v₂, v₁, v₀` in turn), where `b = D + S` and `S` is the Schur term
of the block on `(v₁, v₂)`. -/
private lemma seed4_quad_identity {a b D x y z w : ℝ} (v0 v1 v2 v3 : ℝ) (ha : a ≠ 0)
    (haw : a ^ 2 - w ^ 2 ≠ 0) (hD : D ≠ 0)
    (hb : b = D + (a * y ^ 2 + 2 * w * y * z + a * z ^ 2) / (a ^ 2 - w ^ 2)) :
    a * v0 ^ 2 - 2 * x * v0 * v1 + b * v1 ^ 2 - 2 * y * v1 * v2 - 2 * z * v1 * v3 + a * v2 ^ 2
        - 2 * w * v2 * v3 + a * v3 ^ 2
      = a * (v3 - (z * v1 + w * v2) / a) ^ 2
        + (a ^ 2 - w ^ 2) / a * (v2 - (a * y + z * w) / (a ^ 2 - w ^ 2) * v1) ^ 2
        + D * (v1 - x * v0 / D) ^ 2 + (a - x ^ 2 / D) * v0 ^ 2 := by
  subst hb
  field_simp
  ring

/-- An explicit solution of `M u = e₀`, where `P D = a D - x²`. -/
private lemma seed4_inv_col {a b D P x y z w : ℝ} (haw : a ^ 2 - w ^ 2 ≠ 0) (hD : D ≠ 0)
    (hP : P ≠ 0) (hPD : P * D = a * D - x ^ 2)
    (hb : b = D + (a * y ^ 2 + 2 * w * y * z + a * z ^ 2) / (a ^ 2 - w ^ 2)) :
    (!![a, -x, 0, 0; -x, b, -y, -z; 0, -y, a, -w; 0, -z, -w, a] : Matrix (Fin 4) (Fin 4) ℝ) *ᵥ
      ![1 / P, x / (P * D), x * (a * y + w * z) / (P * D * (a ^ 2 - w ^ 2)),
        x * (w * y + a * z) / (P * D * (a ^ 2 - w ^ 2))] = Pi.single 0 1 := by
  subst hb
  ext i
  fin_cases i
  · simp [mulVec, dotProduct, Fin.sum_univ_four]
    field_simp
    linear_combination -hPD
  all_goals
    simp [mulVec, dotProduct, Fin.sum_univ_four]
    field_simp
    ring

theorem seed4 {a b x y z w : ℝ} (hx : x ^ 2 = 1) (hy : y ^ 2 = 1) (hz : z ^ 2 = 1)
    (hw : w ^ 2 = 1) (ha : 1 < a) (hb : 0 < b - 2 / (a - w * y * z))
    (hc : 0 < a - 1 / (b - 2 / (a - w * y * z))) :
    (!![a, -x, 0, 0; -x, b, -y, -z; 0, -y, a, -w; 0, -z, -w, a] : Matrix (Fin 4) (Fin 4) ℝ).PosDef ∧
      (!![a, -x, 0, 0; -x, b, -y, -z; 0, -y, a, -w; 0, -z, -w, a] : Matrix (Fin 4) (Fin 4) ℝ)⁻¹ 0 0
        = 1 / (a - 1 / (b - 2 / (a - w * y * z))) := by
  have ht : (w * y * z) ^ 2 = 1 := by linear_combination y ^ 2 * z ^ 2 * hw + z ^ 2 * hy + hz
  have ht1 : w * y * z ≤ 1 := by nlinarith
  have hs : 0 < a - w * y * z := by linarith
  have ha0 : 0 < a := by linarith
  have ha2 : 0 < a ^ 2 - w ^ 2 := by rw [hw]; nlinarith
  have hS : (a * y ^ 2 + 2 * w * y * z + a * z ^ 2) / (a ^ 2 - w ^ 2) = 2 / (a - w * y * z) := by
    rw [div_eq_div_iff ha2.ne' hs.ne', hy, hz, hw]
    linear_combination (-2) * ht
  obtain ⟨D, hD_def⟩ : ∃ D, D = b - 2 / (a - w * y * z) := ⟨_, rfl⟩
  rw [← hD_def] at hb hc ⊢
  obtain ⟨P, hP_def⟩ : ∃ P, P = a - 1 / D := ⟨_, rfl⟩
  rw [← hP_def] at hc ⊢
  have hb' : b = D + (a * y ^ 2 + 2 * w * y * z + a * z ^ 2) / (a ^ 2 - w ^ 2) := by
    rw [hS, hD_def]; ring
  have hPD : P * D = a * D - x ^ 2 := by
    rw [hP_def, hx]; field_simp
  have hk2 : 0 < (a ^ 2 - w ^ 2) / a := div_pos ha2 ha0
  have hk0 : 0 < a - x ^ 2 / D := by rw [hx, ← hP_def]; exact hc
  have hM : (!![a, -x, 0, 0; -x, b, -y, -z; 0, -y, a, -w; 0, -z, -w, a] :
      Matrix (Fin 4) (Fin 4) ℝ).PosDef := by
    refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
    · ext i j
      fin_cases i <;> fin_cases j <;> simp
    intro v hv
    have hQ : star v ⬝ᵥ ((!![a, -x, 0, 0; -x, b, -y, -z; 0, -y, a, -w; 0, -z, -w, a] :
        Matrix (Fin 4) (Fin 4) ℝ) *ᵥ v) =
        a * v 0 ^ 2 - 2 * x * v 0 * v 1 + b * v 1 ^ 2 - 2 * y * v 1 * v 2 - 2 * z * v 1 * v 3
          + a * v 2 ^ 2 - 2 * w * v 2 * v 3 + a * v 3 ^ 2 := by
      simp [mulVec, dotProduct, Fin.sum_univ_four]
      ring
    rw [hQ, seed4_quad_identity (v 0) (v 1) (v 2) (v 3) ha0.ne' ha2.ne' hb.ne' hb']
    by_contra hle
    push Not at hle
    have h3 := mul_nonneg ha0.le (sq_nonneg (v 3 - (z * v 1 + w * v 2) / a))
    have h2 := mul_nonneg hk2.le
      (sq_nonneg (v 2 - (a * y + z * w) / (a ^ 2 - w ^ 2) * v 1))
    have h1 := mul_nonneg hb.le (sq_nonneg (v 1 - x * v 0 / D))
    have h0 := mul_nonneg hk0.le (sq_nonneg (v 0))
    have sq0 {k t : ℝ} (hk : 0 < k) (h : k * t ^ 2 = 0) : t = 0 := by
      rcases mul_eq_zero.mp h with h | h
      · exact absurd h hk.ne'
      · exact pow_eq_zero_iff two_ne_zero |>.mp h
    have e0 : v 0 = 0 := sq0 hk0 (by linarith)
    have e1 : v 1 = 0 := by
      have := sq0 hb (by linarith : D * (v 1 - x * v 0 / D) ^ 2 = 0)
      simpa [e0] using this
    have e2 : v 2 = 0 := by
      have := sq0 hk2
        (by linarith : (a ^ 2 - w ^ 2) / a * (v 2 - (a * y + z * w) / (a ^ 2 - w ^ 2) * v 1) ^ 2
          = 0)
      simpa [e1] using this
    have e3 : v 3 = 0 := by
      have := sq0 ha0 (by linarith : a * (v 3 - (z * v 1 + w * v 2) / a) ^ 2 = 0)
      simpa [e1, e2] using this
    apply hv
    ext i
    fin_cases i <;> simp [e0, e1, e2, e3]
  refine ⟨hM, ?_⟩
  have hu := seed4_inv_col ha2.ne' hb.ne' hc.ne' hPD hb'
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp hM.isUnit
  have key := congrFun (congrArg (fun u => (!![a, -x, 0, 0; -x, b, -y, -z; 0, -y, a, -w;
    0, -z, -w, a] : Matrix (Fin 4) (Fin 4) ℝ)⁻¹ *ᵥ u) hu) 0
  simp only [mulVec_mulVec, nonsing_inv_mul _ hdet, one_mulVec, mulVec_single_one] at key
  simpa using key.symm

end BiluLinial
