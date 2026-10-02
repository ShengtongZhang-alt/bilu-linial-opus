/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecC.Defs

/-!
# Derivative rules (CR2)

Node CR2 of `docs/tight/BP_SECC.md`; source lines 1102–1127, display (CR2); AUDIT-C §4.1.

At the star level (`A` symmetric, `a ≠ 0`, `α(x) = 1 - q_A(x) ≠ 0`), with
`x_j = -(Ax)_j/(aα)` (`starRow`) and `c_kj = A_kj/(a²α) + x_k x_j` (`starMark`), and
`D_i = a⁻¹ ∂_i` along `x + t e_i`:

* `D_i α = 2 x_i α`, i.e. `D_i log α = 2 x_i` (`hasDerivAt_starAlpha`);
* `D_i x_j = -x_i x_j - c_ij` (`hasDerivAt_starRow`);
* `D_i c_kj = -2 x_i c_kj - x_k c_ij - c_ki x_j` (`hasDerivAt_starMark`).

The minus branch is the case `(a, A) ↦ (-a, B)`: `z_j = starRow (-a) B x j`,
`d_kj = starMark (-a) B x k j`, and `D_i = a⁻¹ ∂_i = -(-a)⁻¹ ∂_i` gives `D_i z_j = z_i z_j + d_ij`,
`D_i d_kj = 2 z_i d_kj + z_k d_ij + d_ki z_j`, `D_i log β = -2 z_i`; hence
`D_i log Φ = 2p(x_i - z_i)`. At sign endpoints these are the physical rules of (E3)
(`G⁺_vj = x_j`, `G⁺_vv G⁺_kj = c_kj` by (F1), `root_F1`).

**Checks.** Symbolic re-derivation in the proofs (quotient rule, `ring`); AUDIT-C §4.1 checked
the rules by 50-digit finite differences.
-/

@[expose] public section

namespace BiluLinial.Tight

namespace SecC

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `(A (x + t e_i))_j = (A x)_j + t A_ji`. -/
theorem mulVec_line (A : Matrix ι ι ℝ) (x : ι → ℝ) (i j : ι) (t : ℝ) :
    (A *ᵥ (x + t • Pi.single i 1)) j = (A *ᵥ x) j + t * A j i := by
  rw [mulVec_add, mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mulVec_single_one]
  rfl

/-- `α(x + t e_i) = α(x) - 2t (Ax)_i - t² A_ii` for symmetric `A`. -/
theorem starAlpha_line {A : Matrix ι ι ℝ} (hA : A.IsSymm) (x : ι → ℝ) (i : ι) (t : ℝ) :
    starAlpha A (x + t • Pi.single i 1) = starAlpha A x - 2 * t * (A *ᵥ x) i - t ^ 2 * A i i := by
  have hsym : ∀ k l, A k l = A l k := fun k l => by
    simpa using congrFun (congrFun hA l) k
  have hxA : x ⬝ᵥ A.col i = (A *ᵥ x) i := by
    simp only [dotProduct, mulVec, col_apply]
    exact Finset.sum_congr rfl fun k _ => by rw [hsym k i, mul_comm]
  unfold starAlpha qForm
  rw [mulVec_add, mulVec_smul, mulVec_single_one]
  simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    single_one_dotProduct, hxA, col_apply]
  ring

/-- **CR2**, the score: `∂_i α = 2a x_i α` at `t = 0`. -/
theorem hasDerivAt_starAlpha {a : ℝ} (ha : a ≠ 0) {A : Matrix ι ι ℝ} (hA : A.IsSymm)
    {x : ι → ℝ} (hα : starAlpha A x ≠ 0) (i : ι) :
    HasDerivAt (fun t : ℝ => starAlpha A (x + t • Pi.single i 1))
      (2 * a * starRow a A x i * starAlpha A x) 0 := by
  have h : (fun t : ℝ => starAlpha A (x + t • Pi.single i 1)) =
      fun t => starAlpha A x - 2 * t * (A *ᵥ x) i - t ^ 2 * A i i :=
    funext fun t => starAlpha_line hA x i t
  rw [h]
  have h1 : HasDerivAt (fun t : ℝ => 2 * t * (A *ᵥ x) i) (2 * (A *ᵥ x) i) 0 := by
    simpa using ((hasDerivAt_id' (0 : ℝ)).const_mul 2).mul_const ((A *ᵥ x) i)
  have h2 : HasDerivAt (fun t : ℝ => t ^ 2 * A i i) 0 0 := by
    simpa using (hasDerivAt_pow 2 (0 : ℝ)).mul_const (A i i)
  have hd : HasDerivAt (fun t : ℝ => starAlpha A x - 2 * t * (A *ᵥ x) i - t ^ 2 * A i i)
      (-(2 * (A *ᵥ x) i)) 0 := by
    have h0 : HasDerivAt (fun _ : ℝ => starAlpha A x) 0 0 := hasDerivAt_const _ _
    convert (h0.sub h1).sub h2 using 1
    ring
  convert hd using 1
  unfold starRow
  field_simp

/-- **CR2**, the row rule: `∂_i x_j = a(-x_i x_j - c_ij)` at `t = 0`. -/
theorem hasDerivAt_starRow {a : ℝ} (ha : a ≠ 0) {A : Matrix ι ι ℝ} (hA : A.IsSymm)
    {x : ι → ℝ} (hα : starAlpha A x ≠ 0) (i j : ι) :
    HasDerivAt (fun t : ℝ => starRow a A (x + t • Pi.single i 1) j)
      (a * (-(starRow a A x i * starRow a A x j) - starMark a A x i j)) 0 := by
  have hsym : A j i = A i j := by simpa using congrFun (congrFun hA i) j
  have hnum : HasDerivAt (fun t : ℝ => -(A *ᵥ (x + t • Pi.single i 1)) j) (-A j i) 0 := by
    have e : (fun t : ℝ => -(A *ᵥ (x + t • Pi.single i 1)) j) =
        fun t => -((A *ᵥ x) j + t * A j i) := funext fun t => by rw [mulVec_line]
    rw [e]
    convert (((hasDerivAt_id' (0 : ℝ)).mul_const (A j i)).const_add ((A *ᵥ x) j)).neg using 1
    ring
  have hden : HasDerivAt (fun t : ℝ => a * starAlpha A (x + t • Pi.single i 1))
      (a * (2 * a * starRow a A x i * starAlpha A x)) 0 :=
    (hasDerivAt_starAlpha ha hA hα i).const_mul a
  have h0 : a * starAlpha A (x + (0 : ℝ) • Pi.single i 1) ≠ 0 := by
    simpa using mul_ne_zero ha hα
  have hq := hnum.div hden h0
  show HasDerivAt (fun t : ℝ => -(A *ᵥ (x + t • Pi.single i 1)) j /
    (a * starAlpha A (x + t • Pi.single i 1))) _ 0
  convert hq using 1
  simp only [zero_smul, add_zero]
  unfold starMark starCore starRow
  rw [hsym]
  field_simp
  ring

/-- **CR2**, the mark rule: `∂_i c_kj = a(-2 x_i c_kj - x_k c_ij - c_ki x_j)` at `t = 0`. -/
theorem hasDerivAt_starMark {a : ℝ} (ha : a ≠ 0) {A : Matrix ι ι ℝ} (hA : A.IsSymm)
    {x : ι → ℝ} (hα : starAlpha A x ≠ 0) (i k j : ι) :
    HasDerivAt (fun t : ℝ => starMark a A (x + t • Pi.single i 1) k j)
      (a * (-2 * starRow a A x i * starMark a A x k j - starRow a A x k * starMark a A x i j -
        starMark a A x k i * starRow a A x j)) 0 := by
  have hsym : A k i = A i k := by simpa using congrFun (congrFun hA i) k
  have hα' := hasDerivAt_starAlpha ha hA hα i
  have h0 : a ^ 2 * starAlpha A (x + (0 : ℝ) • Pi.single i 1) ≠ 0 := by
    simpa using mul_ne_zero (pow_ne_zero 2 ha) hα
  have hcore := (hasDerivAt_const (0 : ℝ) (A k j)).div (hα'.const_mul (a ^ 2)) h0
  have hprod := (hasDerivAt_starRow ha hA hα i k).mul (hasDerivAt_starRow ha hA hα i j)
  have hsum := hcore.add hprod
  show HasDerivAt (fun t : ℝ => A k j / (a ^ 2 * starAlpha A (x + t • Pi.single i 1)) +
    starRow a A (x + t • Pi.single i 1) k * starRow a A (x + t • Pi.single i 1) j) _ 0
  convert hsum using 1
  simp only [zero_smul, add_zero]
  unfold starMark starCore starRow
  rw [hsym]
  field_simp
  ring

end SecC

end BiluLinial.Tight
