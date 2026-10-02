/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecB.W1Defs
public import BiluLinial.Tight.SecB.RouteDR1
public import BiluLinial.Tight.Contact.RealParams

/-!
# The weak loop (W1): the secondary terms and the random-mask derivative

Nodes TB.W1sec (`weak_sec_of`) and TB.W1mask (`weak_mask_of`) of `docs/tight/BP_SECB.md` (source
l.795–838; AUDIT-B §2.4). Notation: `X_τ` the physical shifted inverses, `r^τ_k = (X_τ²)_kk`,
`D_*` (`Contact.Dstar`), `m` a bound for the mask `|f_k| ≤ m`.

* **Matrix facts on the support** (`shift_opnorm`, `shiftP_sq_le`, `shift_row_sq_le`): for vectors
  `w` supported on `S`, `h² ‖X w‖² ≤ ‖w‖²` (proof: with `z = Q⁻¹(√y ⊙ w)`, `Q = P̃ + hY_S`,
  `⟨w, Xw⟩ = ⟨Qz, z⟩ = zᵀP̃z + h zᵀY_S z ≥ h‖Xw‖²` since `z` vanishes off `S`, then
  Cauchy–Schwarz); `X_kl² ≤ X_kk X_ll`; `Σ_l X_kl² = r_k ≤ G_kk/h` (TB.ward).
* **Pointwise bounds** (pure finite sums): `|F_ji(g)| ≤ 2 m D²/h` (`maskF_abs_le`, Cauchy–Schwarz
  only: `2|U_ji| ≤ m(r_j^ε + r_i^ν)`), and for the secondary terms
  `Σ_j |2ε X_ij F_ji + Xn_ij F_ji - Xn_ii X_ij U_ij| ≤ 5 (mD/h)(r^ε_i + r^ν_i)` (`sec_sum_le`,
  using the operator bound for `‖U e_i‖` and `‖U_{i·}‖`).
* **At a contact**: `G^±_kk ≤ D_*` on the radius-two ball, `H ≤ D_*²/4`, `m = 1/√d` for `u`,
  `m = a²dD_*²/√d` for `b_±`, `|∂_ij b₊| ≤ 2a³D_*(r_i + r_j)/√d`, and the analogue for `b₋`.
  With (W5) (`ward_mean_of_cl1`, `m = 3, 5`) and `a² ≤ 1/d`: `a|wSec| ≤ C/(dh^{3/2})` and
  `a|wMask| ≤ C/(dh^{3/2})`, both `≤ C B₀`.
-/

@[expose] public section

namespace BiluLinial.Tight.SecB

open Matrix

universe u

/-! ### Finite sums -/

section Gen

variable {V : Type*} [Fintype V]

/-- `2λ Σ|a_k||b_k| ≤ λ² Σ a_k² + Σ b_k²`. -/
theorem two_mul_sum_abs_mul_le (s : Finset V) (a b : V → ℝ) (l : ℝ) :
    2 * l * ∑ k ∈ s, |a k| * |b k| ≤ l ^ 2 * ∑ k ∈ s, a k ^ 2 + ∑ k ∈ s, b k ^ 2 := by
  have h : ∀ k ∈ s, 2 * l * (|a k| * |b k|) ≤ l ^ 2 * a k ^ 2 + b k ^ 2 := fun k _ => by
    have e : (l * |a k| - |b k|) ^ 2 = l ^ 2 * a k ^ 2 - 2 * l * (|a k| * |b k|) + b k ^ 2 := by
      rw [sub_sq, mul_pow, sq_abs, sq_abs]
      ring
    nlinarith [sq_nonneg (l * |a k| - |b k|)]
  have := Finset.sum_le_sum h
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum] at this
  exact this

theorem mul_self_diag_eq {X : Matrix V V ℝ} (hX : ∀ k l, X k l = X l k) (i : V) :
    (X * X) i i = ∑ k, X i k ^ 2 := by
  rw [Matrix.mul_apply]
  exact Finset.sum_congr rfl fun k _ => by rw [hX k i]; ring

variable [DecidableEq V]

theorem maskU_apply_eq {Xe Xn : Matrix V V ℝ} (hXn : ∀ k l, Xn k l = Xn l k) (g : V → ℝ)
    (j i : V) : (Xe * diagonal g * Xn) j i = ∑ k, Xe j k * g k * Xn i k := by
  rw [Matrix.mul_apply]
  exact Finset.sum_congr rfl fun k _ => by rw [Matrix.mul_diagonal, hXn k i]

/-- `2|U_ji| ≤ m (Σ_k Xe_jk² + Σ_k Xn_ik²)` for `U = Xe D_g Xn`, `|g| ≤ m`. -/
theorem two_abs_maskU_le {Xe Xn : Matrix V V ℝ} (hXn : ∀ k l, Xn k l = Xn l k) {g : V → ℝ}
    {m : ℝ} (hm0 : 0 ≤ m) (hm : ∀ k, |g k| ≤ m) (j i : V) :
    2 * |(Xe * diagonal g * Xn) j i| ≤ m * (∑ k, Xe j k ^ 2 + ∑ k, Xn i k ^ 2) := by
  rw [maskU_apply_eq hXn]
  have h1 : |∑ k, Xe j k * g k * Xn i k| ≤ m * ∑ k, |Xe j k| * |Xn i k| := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [abs_mul, abs_mul]
    have := mul_le_mul_of_nonneg_left (hm k) (abs_nonneg (Xe j k))
    have h0 := abs_nonneg (Xn i k)
    nlinarith
  have h2 := two_mul_sum_abs_mul_le Finset.univ (Xe j) (Xn i) 1
  have h3 : 0 ≤ ∑ k, |Xe j k| * |Xn i k| :=
    Finset.sum_nonneg fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  nlinarith

/-- **Mask bound.** `|F_ji(g)| ≤ 2mD²/h` when `|g| ≤ m`, `0 ≤ Xe_ii ≤ D`, `|Xe_ji| ≤ D` and the
three row energies are `≤ D/h`. -/
theorem maskF_abs_le {Xe Xn : Matrix V V ℝ} (hXn : ∀ k l, Xn k l = Xn l k) {g : V → ℝ}
    {m D h : ℝ} (hm0 : 0 ≤ m) (hm : ∀ k, |g k| ≤ m) (hh : 0 < h) {i j : V}
    (hii : 0 ≤ Xe i i) (hiD : Xe i i ≤ D) (hji : |Xe j i| ≤ D)
    (hrj : ∑ k, Xe j k ^ 2 ≤ D / h) (hri : ∑ k, Xe i k ^ 2 ≤ D / h)
    (hrn : ∑ k, Xn i k ^ 2 ≤ D / h) :
    |maskF Xe Xn g j i| ≤ 2 * m * D ^ 2 / h := by
  have hD : 0 ≤ D := hii.trans hiD
  have u1 := two_abs_maskU_le (Xe := Xe) hXn hm0 hm j i
  have u2 := two_abs_maskU_le (Xe := Xe) hXn hm0 hm i i
  have hU1 : |(Xe * diagonal g * Xn) j i| ≤ m * D / h := by
    have : m * (∑ k, Xe j k ^ 2 + ∑ k, Xn i k ^ 2) ≤ m * (D / h + D / h) :=
      mul_le_mul_of_nonneg_left (add_le_add hrj hrn) hm0
    have e : m * (D / h + D / h) = 2 * (m * D / h) := by ring
    linarith
  have hU2 : |(Xe * diagonal g * Xn) i i| ≤ m * D / h := by
    have : m * (∑ k, Xe i k ^ 2 + ∑ k, Xn i k ^ 2) ≤ m * (D / h + D / h) :=
      mul_le_mul_of_nonneg_left (add_le_add hri hrn) hm0
    have e : m * (D / h + D / h) = 2 * (m * D / h) := by ring
    linarith
  have hmD : 0 ≤ m * D / h := div_nonneg (mul_nonneg hm0 hD) hh.le
  unfold maskF
  calc |Xe i i * (Xe * diagonal g * Xn) j i - Xe j i * (Xe * diagonal g * Xn) i i|
      ≤ |Xe i i * (Xe * diagonal g * Xn) j i| + |Xe j i * (Xe * diagonal g * Xn) i i| :=
        abs_sub _ _
    _ = Xe i i * |(Xe * diagonal g * Xn) j i| + |Xe j i| * |(Xe * diagonal g * Xn) i i| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hii]
    _ ≤ D * (m * D / h) + D * (m * D / h) :=
        add_le_add (mul_le_mul hiD hU1 (abs_nonneg _) hD)
          (mul_le_mul hji hU2 (abs_nonneg _) hD)
    _ = 2 * m * D ^ 2 / h := by ring

/-- **Secondary-term bound.** With the operator bounds `h²‖Xe w‖² ≤ ‖w‖²`, `h²‖Xn w‖² ≤ ‖w‖²`
for `w` supported on `S`, a mask `f` supported on `S` with `|f| ≤ m`, and `0 ≤ Xe_ii, Xn_ii ≤ D`,
`re = Σ_k Xe_ik² ≤ D/h`, `rn = Σ_k Xn_ik² ≤ D/h`:
`Σ_{j∈J} |2ε Xe_ij F_ji + Xn_ij F_ji - Xn_ii Xe_ij U_ij| ≤ 5 (mD/h)(re + rn)` (`|ε| ≤ 1`). -/
theorem sec_sum_le {Xe Xn : Matrix V V ℝ} (hXe : ∀ k l, Xe k l = Xe l k)
    (hXn : ∀ k l, Xn k l = Xn l k) {S : Finset V} {h m D ε : ℝ} (hh : 0 < h) (hm : 0 < m)
    (hD : 0 < D) (hε : |ε| ≤ 1)
    (hopE : ∀ w : V → ℝ, (∀ k, k ∉ S → w k = 0) → h ^ 2 * ∑ k, (Xe *ᵥ w) k ^ 2 ≤ ∑ k, w k ^ 2)
    (hopN : ∀ w : V → ℝ, (∀ k, k ∉ S → w k = 0) → h ^ 2 * ∑ k, (Xn *ᵥ w) k ^ 2 ≤ ∑ k, w k ^ 2)
    {f : V → ℝ} (hf : ∀ k, |f k| ≤ m) (hfS : ∀ k, k ∉ S → f k = 0) {i : V}
    (hei : 0 ≤ Xe i i) (heD : Xe i i ≤ D) (hni : 0 ≤ Xn i i) (hnD : Xn i i ≤ D)
    (hre : ∑ k, Xe i k ^ 2 ≤ D / h) (hrn : ∑ k, Xn i k ^ 2 ≤ D / h) (J : Finset V) :
    ∑ j ∈ J, |2 * ε * Xe i j * maskF Xe Xn f j i + Xn i j * maskF Xe Xn f j i -
        Xn i i * Xe i j * (Xe * diagonal f * Xn) i j| ≤
      5 * (m * D / h) * (∑ k, Xe i k ^ 2 + ∑ k, Xn i k ^ 2) := by
  have hh0 : h ≠ 0 := hh.ne'
  set re := ∑ k, Xe i k ^ 2 with hre_def
  set rn := ∑ k, Xn i k ^ 2 with hrn_def
  set U := Xe * diagonal f * Xn with hU
  set F : V → ℝ := fun j => maskF Xe Xn f j i with hF
  have hre0 : 0 ≤ re := Finset.sum_nonneg fun k _ => sq_nonneg _
  have hrn0 : 0 ≤ rn := Finset.sum_nonneg fun k _ => sq_nonneg _
  -- `‖U e_i‖² ≤ m² rn / h²`
  have hUcol : h ^ 2 * ∑ j, U j i ^ 2 ≤ m ^ 2 * rn := by
    have e : ∀ j, U j i = (Xe *ᵥ fun k => f k * Xn i k) j := fun j => by
      rw [hU, maskU_apply_eq hXn]
      simp only [Matrix.mulVec, dotProduct]
      exact Finset.sum_congr rfl fun k _ => by ring
    simp only [e]
    refine le_trans (hopE _ fun k hk => by simp [hfS k hk]) ?_
    rw [hrn_def, Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [mul_pow]
    have : f k ^ 2 ≤ m ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hf k) 2
    exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
  -- `‖U_{i·}‖² ≤ m² re / h²`
  have hUrow : h ^ 2 * ∑ j, U i j ^ 2 ≤ m ^ 2 * re := by
    have e : ∀ j, U i j = (Xn *ᵥ fun k => Xe i k * f k) j := fun j => by
      rw [hU, Matrix.mul_apply]
      simp only [Matrix.mulVec, dotProduct, Matrix.mul_diagonal]
      exact Finset.sum_congr rfl fun k _ => by rw [hXn k j]; ring
    simp only [e]
    refine le_trans (hopN _ fun k hk => by simp [hfS k hk]) ?_
    rw [hre_def, Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [mul_pow, mul_comm (Xe i k ^ 2)]
    have : f k ^ 2 ≤ m ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hf k) 2
    exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
  -- `|U_ii| ≤ m (re + rn)/2 ≤ mD/h`
  have hUii : 2 * |U i i| ≤ m * (re + rn) := two_abs_maskU_le hXn hm.le hf i i
  -- `‖F_{·i}‖² ≤ 2m²D²(re + rn)/h²`
  have hFsq : h ^ 2 * ∑ j, F j ^ 2 ≤ 2 * m ^ 2 * D ^ 2 * (re + rn) := by
    have hpt : ∀ j, F j ^ 2 ≤ 2 * Xe i i ^ 2 * U j i ^ 2 + 2 * U i i ^ 2 * Xe i j ^ 2 := fun j => by
      have e : F j = Xe i i * U j i - Xe j i * U i i := rfl
      rw [e, hXe j i]
      nlinarith [sq_nonneg (Xe i i * U j i + Xe i j * U i i)]
    have hsum : ∑ j, F j ^ 2 ≤ 2 * Xe i i ^ 2 * ∑ j, U j i ^ 2 + 2 * U i i ^ 2 * re := by
      refine le_trans (Finset.sum_le_sum fun j _ => hpt j) ?_
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have hXii2 : Xe i i ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ hei heD 2
    have hUii2 : U i i ^ 2 ≤ (m * D / h) ^ 2 := by
      have : |U i i| ≤ m * D / h := by
        have : m * (re + rn) ≤ m * (D / h + D / h) := mul_le_mul_of_nonneg_left (add_le_add hre hrn) hm.le
        have e : m * (D / h + D / h) = 2 * (m * D / h) := by ring
        linarith
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) this 2
    have hre' : h * re ≤ D := by rw [← le_div_iff₀' hh]; exact hre
    have hh2 : 0 < h ^ 2 := by positivity
    calc h ^ 2 * ∑ j, F j ^ 2 ≤ h ^ 2 * (2 * Xe i i ^ 2 * ∑ j, U j i ^ 2 + 2 * U i i ^ 2 * re) :=
          mul_le_mul_of_nonneg_left hsum hh2.le
      _ = 2 * Xe i i ^ 2 * (h ^ 2 * ∑ j, U j i ^ 2) + 2 * (h * U i i) ^ 2 * re := by ring
      _ ≤ 2 * D ^ 2 * (m ^ 2 * rn) + 2 * (m * D) ^ 2 * re := by
          have t1 : 2 * Xe i i ^ 2 * (h ^ 2 * ∑ j, U j i ^ 2) ≤ 2 * D ^ 2 * (m ^ 2 * rn) := by
            have := mul_le_mul hXii2 hUcol (by positivity) (sq_nonneg D)
            linarith
          have t2 : (h * U i i) ^ 2 ≤ (m * D) ^ 2 := by
            have : (h * U i i) ^ 2 = h ^ 2 * U i i ^ 2 := by ring
            rw [this]
            have h3 : h ^ 2 * (m * D / h) ^ 2 = (m * D) ^ 2 := by field_simp
            calc h ^ 2 * U i i ^ 2 ≤ h ^ 2 * (m * D / h) ^ 2 := mul_le_mul_of_nonneg_left hUii2 hh2.le
              _ = (m * D) ^ 2 := h3
          have t3 : 2 * (h * U i i) ^ 2 * re ≤ 2 * (m * D) ^ 2 * re :=
            mul_le_mul_of_nonneg_right (by linarith) hre0
          linarith
      _ = 2 * m ^ 2 * D ^ 2 * (re + rn) := by ring
  -- the three sums, via `2λ Σ|a||b| ≤ λ²Σa² + Σb²`
  have s1 : h * ∑ j, |Xe i j| * |F j| ≤ m * D * (3 / 2 * re + 1 / 2 * rn) := by
    have := two_mul_sum_abs_mul_le Finset.univ (Xe i) F (2 * m * D / h)
    -- multiply by h²/(2·2mD) ... work with `h * (2mD) *` form
    have key : 2 * (2 * m * D) * (h * ∑ j, |Xe i j| * |F j|) ≤
        (2 * m * D) ^ 2 * re + h ^ 2 * ∑ j, F j ^ 2 := by
      have e1 : 2 * (2 * m * D / h) * (∑ j, |Xe i j| * |F j|) * h ^ 2 =
          2 * (2 * m * D) * (h * ∑ j, |Xe i j| * |F j|) := by field_simp
      have e2 : ((2 * m * D / h) ^ 2 * ∑ j, Xe i j ^ 2 + ∑ j, F j ^ 2) * h ^ 2 =
          (2 * m * D) ^ 2 * re + h ^ 2 * ∑ j, F j ^ 2 := by rw [hre_def]; field_simp
      rw [← e1, ← e2]
      exact mul_le_mul_of_nonneg_right this (sq_nonneg h)
    have hmD : 0 < 2 * (2 * m * D) := by positivity
    have : 2 * (2 * m * D) * (h * ∑ j, |Xe i j| * |F j|) ≤
        2 * (2 * m * D) * (m * D * (3 / 2 * re + 1 / 2 * rn)) := by linarith
    exact le_of_mul_le_mul_left this hmD
  have s2 : h * ∑ j, |Xn i j| * |F j| ≤ m * D * (1 / 2 * re + 3 / 2 * rn) := by
    have := two_mul_sum_abs_mul_le Finset.univ (Xn i) F (2 * m * D / h)
    have key : 2 * (2 * m * D) * (h * ∑ j, |Xn i j| * |F j|) ≤
        (2 * m * D) ^ 2 * rn + h ^ 2 * ∑ j, F j ^ 2 := by
      have e1 : 2 * (2 * m * D / h) * (∑ j, |Xn i j| * |F j|) * h ^ 2 =
          2 * (2 * m * D) * (h * ∑ j, |Xn i j| * |F j|) := by field_simp
      have e2 : ((2 * m * D / h) ^ 2 * ∑ j, Xn i j ^ 2 + ∑ j, F j ^ 2) * h ^ 2 =
          (2 * m * D) ^ 2 * rn + h ^ 2 * ∑ j, F j ^ 2 := by rw [hrn_def]; field_simp
      rw [← e1, ← e2]
      exact mul_le_mul_of_nonneg_right this (sq_nonneg h)
    have hmD : 0 < 2 * (2 * m * D) := by positivity
    have : 2 * (2 * m * D) * (h * ∑ j, |Xn i j| * |F j|) ≤
        2 * (2 * m * D) * (m * D * (1 / 2 * re + 3 / 2 * rn)) := by linarith
    exact le_of_mul_le_mul_left this hmD
  have s3 : h * ∑ j, |Xe i j| * |U i j| ≤ m * re := by
    have := two_mul_sum_abs_mul_le Finset.univ (Xe i) (U i) (m / h)
    have key : 2 * m * (h * ∑ j, |Xe i j| * |U i j|) ≤ m ^ 2 * re + h ^ 2 * ∑ j, U i j ^ 2 := by
      have e1 : 2 * (m / h) * (∑ j, |Xe i j| * |U i j|) * h ^ 2 =
          2 * m * (h * ∑ j, |Xe i j| * |U i j|) := by field_simp
      have e2 : ((m / h) ^ 2 * ∑ j, Xe i j ^ 2 + ∑ j, U i j ^ 2) * h ^ 2 =
          m ^ 2 * re + h ^ 2 * ∑ j, U i j ^ 2 := by rw [hre_def]; field_simp
      rw [← e1, ← e2]
      exact mul_le_mul_of_nonneg_right this (sq_nonneg h)
    have : 2 * m * (h * ∑ j, |Xe i j| * |U i j|) ≤ 2 * m * (m * re) := by linarith
    exact le_of_mul_le_mul_left this (by positivity)
  -- assemble
  have hpt : ∀ j, |2 * ε * Xe i j * F j + Xn i j * F j - Xn i i * Xe i j * U i j| ≤
      2 * (|Xe i j| * |F j|) + |Xn i j| * |F j| + D * (|Xe i j| * |U i j|) := fun j => by
    have a1 : |2 * ε * Xe i j * F j| ≤ 2 * (|Xe i j| * |F j|) := by
      rw [abs_mul, abs_mul, abs_mul, abs_two]
      have := mul_le_mul_of_nonneg_right hε (abs_nonneg (Xe i j))
      have h0 : 0 ≤ |F j| := abs_nonneg _
      nlinarith [abs_nonneg (Xe i j)]
    have a2 : |Xn i i * Xe i j * U i j| ≤ D * (|Xe i j| * |U i j|) := by
      rw [abs_mul, abs_mul, abs_of_nonneg hni, mul_assoc]
      exact mul_le_mul_of_nonneg_right hnD (by positivity)
    calc |2 * ε * Xe i j * F j + Xn i j * F j - Xn i i * Xe i j * U i j|
        ≤ |2 * ε * Xe i j * F j + Xn i j * F j| + |Xn i i * Xe i j * U i j| := abs_sub _ _
      _ ≤ |2 * ε * Xe i j * F j| + |Xn i j * F j| + |Xn i i * Xe i j * U i j| := by
          linarith [abs_add_le (2 * ε * Xe i j * F j) (Xn i j * F j)]
      _ ≤ 2 * (|Xe i j| * |F j|) + |Xn i j| * |F j| + D * (|Xe i j| * |U i j|) := by
          rw [abs_mul (Xn i j)]; linarith
  have hJ : ∑ j ∈ J, |2 * ε * Xe i j * F j + Xn i j * F j - Xn i i * Xe i j * U i j| ≤
      ∑ j, (2 * (|Xe i j| * |F j|) + |Xn i j| * |F j| + D * (|Xe i j| * |U i j|)) :=
    le_trans (Finset.sum_le_sum fun j _ => hpt j)
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ J) fun j _ _ =>
        add_nonneg (add_nonneg (by positivity) (by positivity))
          (mul_nonneg hD.le (by positivity)))
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hJ
  have hfin : h * (2 * ∑ j, |Xe i j| * |F j| + ∑ j, |Xn i j| * |F j| +
      D * ∑ j, |Xe i j| * |U i j|) ≤ h * (5 * (m * D / h) * (re + rn)) := by
    have e : h * (5 * (m * D / h) * (re + rn)) = 5 * (m * D) * (re + rn) := by field_simp
    rw [e]
    have t3 := mul_le_mul_of_nonneg_left s3 hD.le
    have p1 : 0 ≤ m * D * re := mul_nonneg (mul_nonneg hm.le hD.le) hre0
    have p2 : 0 ≤ m * D * rn := mul_nonneg (mul_nonneg hm.le hD.le) hrn0
    nlinarith
  exact le_trans hJ (le_of_mul_le_mul_left hfin hh)

end Gen

/-! ### The physical shifted inverse on the support -/

section Shift

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem shiftMat_eq (a τ h : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) :
    shiftMat G a τ h y σ S = diagonal (fun k => Real.sqrt (y k)) *
      (precN G a τ y σ S + h • srcDiag y S)⁻¹ * diagonal (fun k => Real.sqrt (y k)) := by
  ext k l
  simp only [shiftMat, shiftP, Matrix.of_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]

/-- **Operator bound.** On the support, `h² ‖X w‖² ≤ ‖w‖²` for `w` supported on `S`. -/
theorem shift_opnorm {a τ h : ℝ} {y : V → ℝ} {σ : Config V} {S : Finset V}
    (hP : (precN G a τ y σ S).PosDef) (hy : ∀ k, 0 ≤ y k) (hh : 0 < h) (w : V → ℝ)
    (hw : ∀ k, k ∉ S → w k = 0) :
    h ^ 2 * ∑ k, (shiftMat G a τ h y σ S *ᵥ w) k ^ 2 ≤ ∑ k, w k ^ 2 := by
  have hDp : (srcDiag y S).PosSemidef := Matrix.PosSemidef.diagonal fun k => by
    split_ifs
    · exact hy k
    · exact le_rfl
  obtain ⟨Q, hQdef⟩ : ∃ Q, Q = precN G a τ y σ S + h • srcDiag y S := ⟨_, rfl⟩
  obtain ⟨L, hLdef⟩ : ∃ L : Matrix V V ℝ, L = diagonal (fun k => Real.sqrt (y k)) := ⟨_, rfl⟩
  rw [shiftMat_eq, ← hQdef, ← hLdef]
  have hQ : Q.PosDef := by rw [hQdef]; exact hP.add_posSemidef (hDp.smul hh.le)
  have hQu : IsUnit Q.det := isUnit_iff_ne_zero.mpr hQ.det_pos.ne'
  have hQcol : ∀ k, k ∉ S → ∀ m, Q m k = if m = k then 1 else 0 := by
    intro k hk m
    rw [hQdef]
    by_cases hm : m = k
    · subst hm; simp [precN, srcDiag, hk]
    · have hm' : ¬ (m ∈ S ∧ k ∈ S ∧ G.Adj m k) := fun h => hk h.2.1
      simp [precN, srcDiag, hm, hm']
  have hNcol : ∀ k, k ∉ S → ∀ j, Q⁻¹ j k = if j = k then 1 else 0 := by
    intro k hk j
    have h1 : (Q⁻¹ * Q) j k = if j = k then 1 else 0 := by
      rw [Matrix.nonsing_inv_mul Q hQu, Matrix.one_apply]
    rw [Matrix.mul_apply] at h1
    simp only [hQcol k hk, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ↓reduceIte] at h1
    exact h1
  have hNs : ∀ k l, Q⁻¹ k l = Q⁻¹ l k := fun k l => by
    have := congrFun (congrFun hQ.inv.1 l) k
    simpa [Matrix.conjTranspose_apply] using this
  obtain ⟨v, hvdef⟩ : ∃ v, v = L *ᵥ w := ⟨_, rfl⟩
  obtain ⟨z, hzdef⟩ : ∃ z, z = Q⁻¹ *ᵥ v := ⟨_, rfl⟩
  have hXw : (L * Q⁻¹ * L) *ᵥ w = L *ᵥ z := by
    rw [hzdef, hvdef]
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have hLz : ∀ k, (L *ᵥ z) k = Real.sqrt (y k) * z k := fun k => by
    rw [hLdef, Matrix.mulVec_diagonal]
  have hv : ∀ k, v k = Real.sqrt (y k) * w k := fun k => by
    rw [hvdef, hLdef, Matrix.mulVec_diagonal]
  have hz0 : ∀ k, k ∉ S → z k = 0 := by
    intro k hk
    have e : z k = ∑ j, Q⁻¹ k j * v j := by rw [hzdef]; rfl
    rw [e, Finset.sum_eq_single k (fun j _ hjk => by rw [hNs k j, hNcol k hk j, if_neg hjk,
      zero_mul]) (fun h => absurd (Finset.mem_univ k) h), hNcol k hk k, if_pos rfl, one_mul, hv,
      hw k hk, mul_zero]
  have hQz : Q *ᵥ z = v := by
    rw [hzdef, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv Q hQu, Matrix.one_mulVec]
  rw [hXw]
  set A := ∑ k, (L *ᵥ z) k ^ 2 with hA
  set B := ∑ k, w k * (L *ᵥ z) k with hB
  set W := ∑ k, w k ^ 2 with hW
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun k _ => sq_nonneg _
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun k _ => sq_nonneg _
  -- `B = zᵀ P̃ z + h A ≥ h A`
  have hAD : A = (srcDiag y S *ᵥ z) ⬝ᵥ z := by
    rw [hA]
    simp only [dotProduct, srcDiag, Matrix.mulVec_diagonal]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hLz]
    by_cases hk : k ∈ S
    · rw [if_pos hk, mul_pow, Real.sq_sqrt (hy k)]; ring
    · rw [if_neg hk, hz0 k hk]; ring
  have hBv : B = v ⬝ᵥ z := by
    rw [hB]
    simp only [dotProduct]
    exact Finset.sum_congr rfl fun k _ => by rw [hLz, hv]; ring
  have hPz : 0 ≤ (precN G a τ y σ S *ᵥ z) ⬝ᵥ z := by
    have := hP.posSemidef.dotProduct_mulVec_nonneg z
    rw [star_trivial] at this
    rwa [dotProduct_comm]
  have hBA : h * A ≤ B := by
    rw [hBv, ← hQz, hQdef, Matrix.add_mulVec, Matrix.smul_mulVec, add_dotProduct,
      smul_dotProduct, smul_eq_mul, hAD]
    linarith
  -- Cauchy–Schwarz
  have hCS : B ^ 2 ≤ W * A := by
    rw [hB, hW, hA]
    exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have h1 : (h * A) ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ (mul_nonneg hh.le hA0) hBA 2
  have h2 : h ^ 2 * A * A ≤ W * A := by nlinarith
  rcases eq_or_lt_of_le hA0 with h0 | hpos
  · rw [← h0, mul_zero]; exact hW0
  · exact le_of_mul_le_mul_right h2 hpos

/-- `X_kl² ≤ X_kk X_ll` on the support (`X` positive semidefinite). -/
theorem shiftP_sq_le {a τ h : ℝ} {y : V → ℝ} {σ : Config V} {S : Finset V}
    (hP : (precN G a τ y σ S).PosDef) (hy : ∀ k, 0 ≤ y k) (hh : 0 ≤ h) (k l : V) :
    shiftP G a τ h y σ S k l ^ 2 ≤ shiftP G a τ h y σ S k k * shiftP G a τ h y σ S l l := by
  have hDp : (srcDiag y S).PosSemidef := Matrix.PosSemidef.diagonal fun k => by
    split_ifs
    · exact hy k
    · exact le_rfl
  have hQ : (precN G a τ y σ S + h • srcDiag y S).PosDef := hP.add_posSemidef (hDp.smul hh)
  have h1 := posSemidef_entry_sq_le hQ.inv.posSemidef k l
  rw [shiftP_diag G σ S (hy k), shiftP_diag G σ S (hy l)]
  have e : shiftP G a τ h y σ S k l ^ 2 =
      y k * y l * ((precN G a τ y σ S + h • srcDiag y S)⁻¹ k l) ^ 2 := by
    unfold shiftP
    rw [mul_pow, mul_pow, Real.sq_sqrt (hy k), Real.sq_sqrt (hy l)]
    ring
  rw [e]
  calc y k * y l * ((precN G a τ y σ S + h • srcDiag y S)⁻¹ k l) ^ 2
      ≤ y k * y l * ((precN G a τ y σ S + h • srcDiag y S)⁻¹ k k *
          (precN G a τ y σ S + h • srcDiag y S)⁻¹ l l) :=
        mul_le_mul_of_nonneg_left h1 (mul_nonneg (hy k) (hy l))
    _ = y k * hzN G a τ h y σ S k * (y l * hzN G a τ h y σ S l) := by unfold hzN; ring

/-- `Σ_l X_kl² = r_k ≤ G_kk/h` for `k ∈ S` on the support (TB.ward). -/
theorem shift_row_sq_le {a τ h : ℝ} {y : V → ℝ} {σ : Config V} {S : Finset V}
    (hP : (precN G a τ y σ S).PosDef) (hy : ∀ k, 0 ≤ y k) (hh : 0 < h) {k : V} (hk : k ∈ S) :
    ∑ l, shiftP G a τ h y σ S k l ^ 2 ≤ greenP G a τ y σ S k k / h := by
  have hw := ward_diag G hy hP hh hk
  have hsym : ∀ i j, shiftMat G a τ h y σ S i j = shiftMat G a τ h y σ S j i := fun i j => by
    simp only [shiftMat, Matrix.of_apply]
    exact shiftP_symm G a τ h y σ S i j
  rw [mul_self_diag_eq hsym] at hw
  have hX0 := (diag_nonneg_of_posDef G hP hy hh.le k).2
  calc ∑ l, shiftP G a τ h y σ S k l ^ 2 = ∑ l, shiftMat G a τ h y σ S k l ^ 2 := rfl
    _ ≤ (greenP G a τ y σ S k k - shiftP G a τ h y σ S k k) / h := hw
    _ ≤ greenP G a τ y σ S k k / h := div_le_div_of_nonneg_right (by linarith) hh.le

end Shift

/-! ### At a contact -/

section ContactMom

variable {d p : ℕ} (ct : Contact.{u} d p)

/-- The radius-two ball `{v} ∪ N ∪ N(N)` over which `D_*` is taken. -/
abbrev w1Ball : Finset ct.V := insert ct.v (ct.N ∪ ct.N.biUnion (nbhd ct.G ct.S))

theorem w1Ball_v : ct.v ∈ w1Ball ct := Finset.mem_insert_self _ _

theorem w1Ball_N {i : ct.V} (hi : i ∈ ct.N) : i ∈ w1Ball ct :=
  Finset.mem_insert_of_mem (Finset.mem_union_left _ hi)

theorem w1Ball_NN {i j : ct.V} (hi : i ∈ ct.N) (hj : j ∈ nbhd ct.G ct.S i) : j ∈ w1Ball ct :=
  Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, hi, hj⟩))

theorem w1Ball_S {k : ct.V} (hk : k ∈ w1Ball ct) : k ∈ ct.S := (ball_sub_card ct).1 hk

theorem w1_diag_le_Dstar {w : ct.V} (hw : w ∈ w1Ball ct) (σ : Config ct.V) :
    ct.gp σ w w + 1 ≤ ct.Dstar σ ∧ ct.gm σ w w + 1 ≤ ct.Dstar σ := by
  have h := (w1Ball ct).le_sup' (fun w => max (ct.gp σ w w) (ct.gm σ w w)) hw
  have h1 := le_max_left (ct.gp σ w w) (ct.gm σ w w)
  have h2 := le_max_right (ct.gp σ w w) (ct.gm σ w w)
  unfold Contact.Dstar
  constructor <;> linarith

theorem w1_gp_nonneg {σ : Config ct.V} (hσ : wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0)
    (k : ct.V) : 0 ≤ ct.gp σ k k ∧ 0 ≤ ct.gm σ k k := by
  obtain ⟨hpP, hpM⟩ := posDef_of_wt_ne_zero ct.G hσ
  exact ⟨(diag_nonneg_of_posDef ct.G hpP (fun k => (ct.ctx.hyp k).1) le_rfl k).1,
    (diag_nonneg_of_posDef ct.G hpM (fun k => (ct.ctx.hym k).1) le_rfl k).1⟩

theorem w1_Dstar_ge_one {σ : Config ct.V} (hσ : wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0) :
    1 ≤ ct.Dstar σ := by
  have := (w1_diag_le_Dstar ct (w1Ball_v ct) σ).1
  have := (w1_gp_nonneg ct hσ ct.v).1
  linarith

/-- Shifted diagonals and row energies of `X₊` on the ball. -/
theorem w1_XP_facts {h : ℝ} (hh : 0 < h) {σ : Config ct.V}
    (hσ : wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0) {k : ct.V} (hk : k ∈ w1Ball ct) :
    0 ≤ ct.XP h σ k k ∧ ct.XP h σ k k ≤ ct.Dstar σ ∧
      ∑ l, ct.XP h σ k l ^ 2 ≤ ct.Dstar σ / h := by
  obtain ⟨hpP, -⟩ := posDef_of_wt_ne_zero ct.G hσ
  have hy : ∀ k, 0 ≤ ct.yp k := fun k => (ct.ctx.hyp k).1
  have hD := (w1_diag_le_Dstar ct hk σ).1
  have hX0 : 0 ≤ ct.XP h σ k k := (diag_nonneg_of_posDef ct.G hpP hy hh.le k).2
  have hXG : ct.XP h σ k k ≤ ct.gp σ k k := by
    change shiftP ct.G (aOf d p) 1 h ct.yp σ ct.S k k ≤ ct.gp σ k k
    rw [shiftP_diag ct.G σ ct.S (hy k)]
    change ct.yp k * hzN ct.G (aOf d p) 1 h ct.yp σ ct.S k ≤
      greenP ct.G (aOf d p) 1 ct.yp σ ct.S k k
    rw [greenP_diag ct.G σ ct.S (hy k)]
    exact mul_le_mul_of_nonneg_left (hzN_le_hN ct.G hpP hh.le hy k) (hy k)
  have hrow : ∑ l, ct.XP h σ k l ^ 2 ≤ ct.gp σ k k / h :=
    shift_row_sq_le ct.G hpP hy hh (w1Ball_S ct hk)
  refine ⟨hX0, by linarith, le_trans hrow ?_⟩
  exact div_le_div_of_nonneg_right (by linarith) hh.le

/-- Shifted diagonals and row energies of `X₋` on the ball. -/
theorem w1_XM_facts {h : ℝ} (hh : 0 < h) {σ : Config ct.V}
    (hσ : wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0) {k : ct.V} (hk : k ∈ w1Ball ct) :
    0 ≤ ct.XM h σ k k ∧ ct.XM h σ k k ≤ ct.Dstar σ ∧
      ∑ l, ct.XM h σ k l ^ 2 ≤ ct.Dstar σ / h := by
  obtain ⟨-, hpM⟩ := posDef_of_wt_ne_zero ct.G hσ
  have hy : ∀ k, 0 ≤ ct.ym k := fun k => (ct.ctx.hym k).1
  have hD := (w1_diag_le_Dstar ct hk σ).2
  have hX0 : 0 ≤ ct.XM h σ k k := (diag_nonneg_of_posDef ct.G hpM hy hh.le k).2
  have hXG : ct.XM h σ k k ≤ ct.gm σ k k := by
    change shiftP ct.G (aOf d p) (-1) h ct.ym σ ct.S k k ≤ ct.gm σ k k
    rw [shiftP_diag ct.G σ ct.S (hy k)]
    change ct.ym k * hzN ct.G (aOf d p) (-1) h ct.ym σ ct.S k ≤
      greenP ct.G (aOf d p) (-1) ct.ym σ ct.S k k
    rw [greenP_diag ct.G σ ct.S (hy k)]
    exact mul_le_mul_of_nonneg_left (hzN_le_hN ct.G hpM hh.le hy k) (hy k)
  have hrow : ∑ l, ct.XM h σ k l ^ 2 ≤ ct.gm σ k k / h :=
    shift_row_sq_le ct.G hpM hy hh (w1Ball_S ct hk)
  refine ⟨hX0, by linarith, le_trans hrow ?_⟩
  exact div_le_div_of_nonneg_right (by linarith) hh.le

theorem abs_le_of_sq_le_mul {x A B D : ℝ} (hA : 0 ≤ A) (hAD : A ≤ D) (hB : 0 ≤ B) (hBD : B ≤ D)
    (h : x ^ 2 ≤ A * B) : |x| ≤ D := by
  have hD : 0 ≤ D := hA.trans hAD
  have : x ^ 2 ≤ D ^ 2 := le_trans h (by nlinarith)
  exact (sq_le_sq.mp this).trans_eq (abs_of_nonneg hD)

theorem w1_XP_off_le {h : ℝ} (hh : 0 < h) {σ : Config ct.V}
    (hσ : wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0) {j k : ct.V} (hj : j ∈ w1Ball ct)
    (hk : k ∈ w1Ball ct) : |ct.XP h σ j k| ≤ ct.Dstar σ := by
  obtain ⟨hpP, -⟩ := posDef_of_wt_ne_zero ct.G hσ
  have hsq := shiftP_sq_le ct.G hpP (fun k => (ct.ctx.hyp k).1) hh.le j k
  obtain ⟨a1, a2, -⟩ := w1_XP_facts ct hh hσ hj
  obtain ⟨b1, b2, -⟩ := w1_XP_facts ct hh hσ hk
  exact abs_le_of_sq_le_mul a1 a2 b1 b2 hsq

theorem w1_XM_off_le {h : ℝ} (hh : 0 < h) {σ : Config ct.V}
    (hσ : wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0) {j k : ct.V} (hj : j ∈ w1Ball ct)
    (hk : k ∈ w1Ball ct) : |ct.XM h σ j k| ≤ ct.Dstar σ := by
  obtain ⟨-, hpM⟩ := posDef_of_wt_ne_zero ct.G hσ
  have hsq := shiftP_sq_le ct.G hpM (fun k => (ct.ctx.hym k).1) hh.le j k
  obtain ⟨a1, a2, -⟩ := w1_XM_facts ct hh hσ hj
  obtain ⟨b1, b2, -⟩ := w1_XM_facts ct hh hσ hk
  exact abs_le_of_sq_le_mul a1 a2 b1 b2 hsq

theorem w1_OmP_le {σ : Config ct.V} (hσ : wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0) :
    ct.OmP σ ≤ ct.Dstar σ ^ 2 / 4 := by
  have h1 := (w1_diag_le_Dstar ct (w1Ball_v ct) σ).1
  have h0 := (w1_gp_nonneg ct hσ ct.v).1
  unfold Contact.OmP
  have : (ct.gp σ ct.v ct.v / 2) ^ 2 ≤ (ct.Dstar σ / 2) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  linarith [show (ct.Dstar σ / 2) ^ 2 = ct.Dstar σ ^ 2 / 4 by ring]

theorem w1_OmM_le {σ : Config ct.V} (hσ : wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0) :
    ct.OmM σ ≤ ct.Dstar σ ^ 2 / 4 := by
  have h1 := w1_diag_le_Dstar ct (w1Ball_v ct) σ
  have h0 := w1_gp_nonneg ct hσ ct.v
  unfold Contact.OmM
  have : ct.gp σ ct.v ct.v * ct.gm σ ct.v ct.v ≤ ct.Dstar σ * ct.Dstar σ :=
    mul_le_mul (by linarith) (by linarith) h0.2 (by linarith)
  nlinarith

/-! #### The masks -/

theorem w1_uvec_abs_le (k : ct.V) : |ct.uvec k| ≤ 1 / Real.sqrt d := by
  unfold Contact.uvec
  split_ifs
  · rw [abs_of_nonneg (by positivity)]
  · rw [abs_zero]; positivity

theorem w1_uvec_off {k : ct.V} (hk : k ∉ ct.S) : ct.uvec k = 0 :=
  w1_uvec_zero ct fun h => hk (w1_N_sub_S ct h)

theorem w1_adjS_abs_le (k l : ct.V) : |ct.adjS k l| ≤ 1 := by
  unfold Contact.adjS
  rw [Matrix.of_apply]
  split_ifs <;> norm_num

theorem w1_adjS_off {k : ct.V} (hk : k ∉ ct.S) (l : ct.V) : ct.adjS k l = 0 := by
  unfold Contact.adjS
  rw [Matrix.of_apply, if_neg fun h => hk h.1]

theorem w1_card_N : (ct.N.card : ℝ) ≤ d := card_nbhd_le_d ct.G ct.ctx.deg ct.S ct.v

theorem w1_card_nbhd (i : ct.V) : ((nbhd ct.G ct.S i).card : ℝ) ≤ d :=
  card_nbhd_le_d ct.G ct.ctx.deg ct.S i

theorem w1_sum_N_ite (c : ℝ) :
    ∑ l, (if l ∈ ct.N then c else 0) = (ct.N.card : ℝ) * c := by
  rw [Finset.sum_ite_mem Finset.univ, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]

/-- `|(A_H v)_k| ≤ |N| c` when `|v_l| ≤ c` on `N` and `v = 0` off `N`. -/
theorem w1_adjS_mulVec_le {v : ct.V → ℝ} {c : ℝ} (hv : ∀ l ∈ ct.N, |v l| ≤ c)
    (hv0 : ∀ l, l ∉ ct.N → v l = 0) (k : ct.V) :
    |(ct.adjS *ᵥ v) k| ≤ (ct.N.card : ℝ) * c := by
  have e : (ct.adjS *ᵥ v) k = ∑ l, ct.adjS k l * v l := rfl
  rw [e, ← w1_sum_N_ite]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun l _ => ?_)
  rw [abs_mul]
  by_cases hl : l ∈ ct.N
  · rw [if_pos hl]
    have := w1_adjS_abs_le ct k l
    have h1 := hv l hl
    have h2 := abs_nonneg (v l)
    nlinarith [abs_nonneg (ct.adjS k l)]
  · rw [if_neg hl, hv0 l hl, abs_zero, mul_zero]

theorem w1_bP_abs_le {h : ℝ} (hh : 0 < h) {σ : Config ct.V}
    (hσ : wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0) (hR : TRegime d p) (k : ct.V) :
    |ct.bP h σ k| ≤ aOf d p ^ 2 * d * ct.Dstar σ ^ 2 / Real.sqrt d := by
  have hv : ∀ l ∈ ct.N, |(ct.MP h σ *ᵥ ct.uvec) l| ≤ ct.Dstar σ ^ 2 / 4 * (1 / Real.sqrt d) := by
    intro l hl
    obtain ⟨a1, a2, -⟩ := w1_XP_facts ct hh hσ (w1Ball_N ct hl)
    rw [Contact.MP, Matrix.mulVec_diagonal, abs_mul]
    have e1 : |(ct.XP h σ l l / 2) ^ 2| ≤ ct.Dstar σ ^ 2 / 4 := by
      rw [abs_of_nonneg (sq_nonneg _)]
      have := pow_le_pow_left₀ (by linarith : 0 ≤ ct.XP h σ l l / 2)
        (by linarith : ct.XP h σ l l / 2 ≤ ct.Dstar σ / 2) 2
      linarith [show (ct.Dstar σ / 2) ^ 2 = ct.Dstar σ ^ 2 / 4 by ring]
    exact mul_le_mul e1 (w1_uvec_abs_le ct l) (abs_nonneg _) (by positivity)
  have hv0 : ∀ l, l ∉ ct.N → (ct.MP h σ *ᵥ ct.uvec) l = 0 := fun l hl => by
    rw [Contact.MP, Matrix.mulVec_diagonal, w1_uvec_zero ct hl, mul_zero]
  have h1 := w1_adjS_mulVec_le ct hv hv0 k
  have hcard := w1_card_N ct
  have ha : 0 ≤ aOf d p ^ 2 := sq_nonneg _
  have e : ct.bP h σ k = 4 * aOf d p ^ 2 * (ct.adjS *ᵥ (ct.MP h σ *ᵥ ct.uvec)) k := rfl
  rw [e, abs_mul, abs_of_nonneg (by positivity)]
  have hc : 0 ≤ ct.Dstar σ ^ 2 / 4 * (1 / Real.sqrt d) := by positivity
  calc 4 * aOf d p ^ 2 * |(ct.adjS *ᵥ (ct.MP h σ *ᵥ ct.uvec)) k|
      ≤ 4 * aOf d p ^ 2 * ((ct.N.card : ℝ) * (ct.Dstar σ ^ 2 / 4 * (1 / Real.sqrt d))) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ ≤ 4 * aOf d p ^ 2 * ((d : ℝ) * (ct.Dstar σ ^ 2 / 4 * (1 / Real.sqrt d))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcard hc) (by positivity)
    _ = aOf d p ^ 2 * d * ct.Dstar σ ^ 2 / Real.sqrt d := by ring

theorem w1_bM_abs_le {h : ℝ} (hh : 0 < h) {σ : Config ct.V}
    (hσ : wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0) (hR : TRegime d p) (k : ct.V) :
    |ct.bM h σ k| ≤ aOf d p ^ 2 * d * ct.Dstar σ ^ 2 / Real.sqrt d := by
  have hv : ∀ l ∈ ct.N, |(ct.MM h σ *ᵥ ct.uvec) l| ≤ ct.Dstar σ ^ 2 / 4 * (1 / Real.sqrt d) := by
    intro l hl
    obtain ⟨a1, a2, -⟩ := w1_XP_facts ct hh hσ (w1Ball_N ct hl)
    obtain ⟨b1, b2, -⟩ := w1_XM_facts ct hh hσ (w1Ball_N ct hl)
    rw [Contact.MM, Matrix.mulVec_diagonal, abs_mul]
    have e1 : |ct.XP h σ l l / 2 * (ct.XM h σ l l / 2)| ≤ ct.Dstar σ ^ 2 / 4 := by
      rw [abs_of_nonneg (by positivity)]
      have := mul_le_mul a2 b2 b1 (by linarith)
      nlinarith
    exact mul_le_mul e1 (w1_uvec_abs_le ct l) (abs_nonneg _) (by positivity)
  have hv0 : ∀ l, l ∉ ct.N → (ct.MM h σ *ᵥ ct.uvec) l = 0 := fun l hl => by
    rw [Contact.MM, Matrix.mulVec_diagonal, w1_uvec_zero ct hl, mul_zero]
  have h1 := w1_adjS_mulVec_le ct hv hv0 k
  have hcard := w1_card_N ct
  have e : ct.bM h σ k = 4 * aOf d p ^ 2 * (ct.adjS *ᵥ (ct.MM h σ *ᵥ ct.uvec)) k := rfl
  rw [e, abs_mul, abs_of_nonneg (by positivity)]
  have hc : 0 ≤ ct.Dstar σ ^ 2 / 4 * (1 / Real.sqrt d) := by positivity
  calc 4 * aOf d p ^ 2 * |(ct.adjS *ᵥ (ct.MM h σ *ᵥ ct.uvec)) k|
      ≤ 4 * aOf d p ^ 2 * ((ct.N.card : ℝ) * (ct.Dstar σ ^ 2 / 4 * (1 / Real.sqrt d))) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ ≤ 4 * aOf d p ^ 2 * ((d : ℝ) * (ct.Dstar σ ^ 2 / 4 * (1 / Real.sqrt d))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcard hc) (by positivity)
    _ = aOf d p ^ 2 * d * ct.Dstar σ ^ 2 / Real.sqrt d := by ring

theorem w1_bP_off (h : ℝ) (σ : Config ct.V) {k : ct.V} (hk : k ∉ ct.S) : ct.bP h σ k = 0 := by
  have e : ct.bP h σ k = 4 * aOf d p ^ 2 * ∑ l, ct.adjS k l * (ct.MP h σ *ᵥ ct.uvec) l := rfl
  rw [e]
  simp [w1_adjS_off ct hk]

theorem w1_bM_off (h : ℝ) (σ : Config ct.V) {k : ct.V} (hk : k ∉ ct.S) : ct.bM h σ k = 0 := by
  have e : ct.bM h σ k = 4 * aOf d p ^ 2 * ∑ l, ct.adjS k l * (ct.MM h σ *ᵥ ct.uvec) l := rfl
  rw [e]
  simp [w1_adjS_off ct hk]

/-- `|∂_ij b₊|_k ≤ 2a³ D_* (r⁺_i + r⁺_j)/√d`. -/
theorem w1_dbP_abs_le {h : ℝ} (hh : 0 < h) {σ : Config ct.V}
    (hσ : wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0) (i j k : ct.V) :
    |dbP ct h σ i j k| ≤ 2 * aOf d p ^ 3 * ct.Dstar σ *
      ((ct.XP h σ * ct.XP h σ) i i + (ct.XP h σ * ct.XP h σ) j j) / Real.sqrt d := by
  have hs := w1_XP_symm ct h σ
  have hterm : ∀ l, |ct.adjS k l * ct.uvec l * (ct.XP h σ l l * ct.XP h σ l i * ct.XP h σ l j)| ≤
      ct.Dstar σ / Real.sqrt d * (|ct.XP h σ i l| * |ct.XP h σ j l|) := by
    intro l
    by_cases hl : l ∈ ct.N
    · obtain ⟨a1, a2, -⟩ := w1_XP_facts ct hh hσ (w1Ball_N ct hl)
      have hu : ct.uvec l = 1 / Real.sqrt d := by simp [Contact.uvec, hl]
      have hA := w1_adjS_abs_le ct k l
      rw [hu, hs l i, hs l j]
      simp only [abs_mul]
      rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / Real.sqrt d), abs_of_nonneg a1]
      calc |ct.adjS k l| * (1 / Real.sqrt d) * (ct.XP h σ l l * |ct.XP h σ i l| * |ct.XP h σ j l|)
          ≤ 1 * (1 / Real.sqrt d) * (ct.Dstar σ * |ct.XP h σ i l| * |ct.XP h σ j l|) := by gcongr
        _ = ct.Dstar σ / Real.sqrt d * (|ct.XP h σ i l| * |ct.XP h σ j l|) := by ring
    · rw [w1_uvec_zero ct hl, mul_zero, zero_mul, abs_zero]
      have := w1_Dstar_ge_one ct hσ
      positivity
  have hsum : 2 * ∑ l, |ct.XP h σ i l| * |ct.XP h σ j l| ≤
      (ct.XP h σ * ct.XP h σ) i i + (ct.XP h σ * ct.XP h σ) j j := by
    have := two_mul_sum_abs_mul_le Finset.univ (ct.XP h σ i) (ct.XP h σ j) 1
    rw [mul_self_diag_eq hs, mul_self_diag_eq hs]
    linarith
  have hD0 : 0 ≤ ct.Dstar σ / Real.sqrt d := by
    have := w1_Dstar_ge_one ct hσ
    positivity
  have hS : |∑ l, ct.adjS k l * ct.uvec l * (ct.XP h σ l l * ct.XP h σ l i * ct.XP h σ l j)| ≤
      ct.Dstar σ / Real.sqrt d * ∑ l, |ct.XP h σ i l| * |ct.XP h σ j l| := by
    rw [Finset.mul_sum]
    exact le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun l _ => hterm l)
  have ha : 0 ≤ aOf d p := by unfold aOf; positivity
  unfold dbP
  rw [abs_mul, abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * aOf d p ^ 3)]
  calc 4 * aOf d p ^ 3 * |∑ l, ct.adjS k l * ct.uvec l *
        (ct.XP h σ l l * ct.XP h σ l i * ct.XP h σ l j)|
      ≤ 4 * aOf d p ^ 3 * (ct.Dstar σ / Real.sqrt d * ∑ l, |ct.XP h σ i l| * |ct.XP h σ j l|) :=
        mul_le_mul_of_nonneg_left hS (by positivity)
    _ ≤ 4 * aOf d p ^ 3 * (ct.Dstar σ / Real.sqrt d *
          (((ct.XP h σ * ct.XP h σ) i i + (ct.XP h σ * ct.XP h σ) j j) / 2)) := by
        gcongr
        linarith
    _ = _ := by ring

/-- `|∂_ij b₋|_k ≤ a³ D_* (r⁻_i + r⁻_j + r⁺_i + r⁺_j)/√d`. -/
theorem w1_dbM_abs_le {h : ℝ} (hh : 0 < h) {σ : Config ct.V}
    (hσ : wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0) (i j k : ct.V) :
    |dbM ct h σ i j k| ≤ aOf d p ^ 3 * ct.Dstar σ *
      ((ct.XM h σ * ct.XM h σ) i i + (ct.XM h σ * ct.XM h σ) j j +
        (ct.XP h σ * ct.XP h σ) i i + (ct.XP h σ * ct.XP h σ) j j) / Real.sqrt d := by
  have hsP := w1_XP_symm ct h σ
  have hsM := w1_XM_symm ct h σ
  have hterm : ∀ l, |ct.adjS k l * ct.uvec l * (ct.XP h σ l l * ct.XM h σ l i * ct.XM h σ l j -
      ct.XM h σ l l * ct.XP h σ l i * ct.XP h σ l j)| ≤ ct.Dstar σ / Real.sqrt d *
      (|ct.XM h σ i l| * |ct.XM h σ j l| + |ct.XP h σ i l| * |ct.XP h σ j l|) := by
    intro l
    by_cases hl : l ∈ ct.N
    · obtain ⟨a1, a2, -⟩ := w1_XP_facts ct hh hσ (w1Ball_N ct hl)
      obtain ⟨b1, b2, -⟩ := w1_XM_facts ct hh hσ (w1Ball_N ct hl)
      have hu : ct.uvec l = 1 / Real.sqrt d := by simp [Contact.uvec, hl]
      have hA := w1_adjS_abs_le ct k l
      rw [hu, hsP l i, hsP l j, hsM l i, hsM l j, abs_mul, abs_mul,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / Real.sqrt d)]
      have hdiff : |ct.XP h σ l l * ct.XM h σ i l * ct.XM h σ j l -
          ct.XM h σ l l * ct.XP h σ i l * ct.XP h σ j l| ≤
          ct.Dstar σ * (|ct.XM h σ i l| * |ct.XM h σ j l| + |ct.XP h σ i l| * |ct.XP h σ j l|) := by
        refine le_trans (abs_sub _ _) ?_
        simp only [abs_mul, abs_of_nonneg a1, abs_of_nonneg b1]
        have t1 : ct.XP h σ l l * |ct.XM h σ i l| * |ct.XM h σ j l| ≤
            ct.Dstar σ * (|ct.XM h σ i l| * |ct.XM h σ j l|) := by
          rw [mul_assoc]; exact mul_le_mul_of_nonneg_right a2 (by positivity)
        have t2 : ct.XM h σ l l * |ct.XP h σ i l| * |ct.XP h σ j l| ≤
            ct.Dstar σ * (|ct.XP h σ i l| * |ct.XP h σ j l|) := by
          rw [mul_assoc]; exact mul_le_mul_of_nonneg_right b2 (by positivity)
        linarith
      calc |ct.adjS k l| * (1 / Real.sqrt d) * |ct.XP h σ l l * ct.XM h σ i l * ct.XM h σ j l -
            ct.XM h σ l l * ct.XP h σ i l * ct.XP h σ j l|
          ≤ 1 * (1 / Real.sqrt d) * (ct.Dstar σ *
              (|ct.XM h σ i l| * |ct.XM h σ j l| + |ct.XP h σ i l| * |ct.XP h σ j l|)) := by
            gcongr
        _ = _ := by ring
    · rw [w1_uvec_zero ct hl, mul_zero, zero_mul, abs_zero]
      have := w1_Dstar_ge_one ct hσ
      positivity
  have hsumM : 2 * ∑ l, |ct.XM h σ i l| * |ct.XM h σ j l| ≤
      (ct.XM h σ * ct.XM h σ) i i + (ct.XM h σ * ct.XM h σ) j j := by
    have := two_mul_sum_abs_mul_le Finset.univ (ct.XM h σ i) (ct.XM h σ j) 1
    rw [mul_self_diag_eq hsM, mul_self_diag_eq hsM]
    linarith
  have hsumP : 2 * ∑ l, |ct.XP h σ i l| * |ct.XP h σ j l| ≤
      (ct.XP h σ * ct.XP h σ) i i + (ct.XP h σ * ct.XP h σ) j j := by
    have := two_mul_sum_abs_mul_le Finset.univ (ct.XP h σ i) (ct.XP h σ j) 1
    rw [mul_self_diag_eq hsP, mul_self_diag_eq hsP]
    linarith
  have hD0 : 0 ≤ ct.Dstar σ / Real.sqrt d := by
    have := w1_Dstar_ge_one ct hσ
    positivity
  have hS : |∑ l, ct.adjS k l * ct.uvec l * (ct.XP h σ l l * ct.XM h σ l i * ct.XM h σ l j -
      ct.XM h σ l l * ct.XP h σ l i * ct.XP h σ l j)| ≤ ct.Dstar σ / Real.sqrt d *
      (∑ l, |ct.XM h σ i l| * |ct.XM h σ j l| + ∑ l, |ct.XP h σ i l| * |ct.XP h σ j l|) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    exact le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun l _ => hterm l)
  have ha : 0 ≤ aOf d p := by unfold aOf; positivity
  unfold dbM
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * aOf d p ^ 3)]
  calc 2 * aOf d p ^ 3 * |∑ l, ct.adjS k l * ct.uvec l * (ct.XP h σ l l * ct.XM h σ l i *
        ct.XM h σ l j - ct.XM h σ l l * ct.XP h σ l i * ct.XP h σ l j)|
      ≤ 2 * aOf d p ^ 3 * (ct.Dstar σ / Real.sqrt d *
          (∑ l, |ct.XM h σ i l| * |ct.XM h σ j l| + ∑ l, |ct.XP h σ i l| * |ct.XP h σ j l|)) :=
        mul_le_mul_of_nonneg_left hS (by positivity)
    _ ≤ 2 * aOf d p ^ 3 * (ct.Dstar σ / Real.sqrt d *
          ((((ct.XM h σ * ct.XM h σ) i i + (ct.XM h σ * ct.XM h σ) j j) +
            ((ct.XP h σ * ct.XP h σ) i i + (ct.XP h σ * ct.XP h σ) j j)) / 2)) := by
        gcongr
        linarith
    _ = _ := by ring

/-! #### Pointwise bounds at a signing in the support -/

/-- The secondary terms at `i ∈ N` for a configuration `(X_ε, X_ν)` with weight `H ≤ D_*²/4`. -/
theorem w1_sec_pt {h : ℝ} (hh : 0 < h) (ε : ℝ) (hε : |ε| ≤ 1) {σ : Config ct.V}
    (hσ : wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0) (Xe Xn : Matrix ct.V ct.V ℝ)
    (hXe : ∀ k l, Xe k l = Xe l k) (hXn : ∀ k l, Xn k l = Xn l k)
    (hopE : ∀ w : ct.V → ℝ, (∀ k, k ∉ ct.S → w k = 0) →
      h ^ 2 * ∑ k, (Xe *ᵥ w) k ^ 2 ≤ ∑ k, w k ^ 2)
    (hopN : ∀ w : ct.V → ℝ, (∀ k, k ∉ ct.S → w k = 0) →
      h ^ 2 * ∑ k, (Xn *ᵥ w) k ^ 2 ≤ ∑ k, w k ^ 2)
    (hfE : ∀ k ∈ w1Ball ct, 0 ≤ Xe k k ∧ Xe k k ≤ ct.Dstar σ ∧
      ∑ l, Xe k l ^ 2 ≤ ct.Dstar σ / h)
    (hfN : ∀ k ∈ w1Ball ct, 0 ≤ Xn k k ∧ Xn k k ≤ ct.Dstar σ ∧
      ∑ l, Xn k l ^ 2 ≤ ct.Dstar σ / h)
    (f : ct.V → ℝ) {m : ℝ} (hm : 0 < m) (hf : ∀ k, |f k| ≤ m) (hfS : ∀ k, k ∉ ct.S → f k = 0)
    (Hv : ℝ) (hH0 : 0 ≤ Hv) (hHD : Hv ≤ ct.Dstar σ ^ 2 / 4) {i : ct.V} (hi : i ∈ ct.N) :
    |∑ j ∈ nbhd ct.G ct.S i, Hv * (-(aOf d p) * (2 * ε * Xe i j * maskF Xe Xn f j i +
        Xn i j * maskF Xe Xn f j i - Xn i i * Xe i j * (Xe * diagonal f * Xn) i j))| ≤
      aOf d p * (ct.Dstar σ ^ 2 / 4) * (5 * (m * ct.Dstar σ / h)) *
        ((Xe * Xe) i i + (Xn * Xn) i i) := by
  obtain ⟨e1, e2, e3⟩ := hfE i (w1Ball_N ct hi)
  obtain ⟨n1, n2, n3⟩ := hfN i (w1Ball_N ct hi)
  have hD := w1_Dstar_ge_one ct hσ
  have hs := sec_sum_le hXe hXn hh hm (by linarith) hε hopE hopN hf hfS e1 e2 n1 n2 e3 n3
    (nbhd ct.G ct.S i)
  rw [mul_self_diag_eq hXe, mul_self_diag_eq hXn]
  have ha : 0 ≤ aOf d p := by unfold aOf; positivity
  rw [← Finset.mul_sum, abs_mul, abs_of_nonneg hH0, ← Finset.mul_sum, abs_mul, abs_neg,
    abs_of_nonneg ha]
  have h1 := le_trans (Finset.abs_sum_le_sum_abs _ _) hs
  have h5 : 0 ≤ 5 * (m * ct.Dstar σ / h) * (∑ k, Xe i k ^ 2 + ∑ k, Xn i k ^ 2) := by
    have : 0 ≤ ∑ k, Xe i k ^ 2 + ∑ k, Xn i k ^ 2 :=
      add_nonneg (Finset.sum_nonneg fun k _ => sq_nonneg _) (Finset.sum_nonneg fun k _ => sq_nonneg _)
    positivity
  calc Hv * (aOf d p * |∑ j ∈ nbhd ct.G ct.S i, (2 * ε * Xe i j * maskF Xe Xn f j i +
        Xn i j * maskF Xe Xn f j i - Xn i i * Xe i j * (Xe * diagonal f * Xn) i j)|)
      ≤ ct.Dstar σ ^ 2 / 4 * (aOf d p *
          (5 * (m * ct.Dstar σ / h) * (∑ k, Xe i k ^ 2 + ∑ k, Xn i k ^ 2))) :=
        mul_le_mul hHD (mul_le_mul_of_nonneg_left h1 ha) (by positivity) (by positivity)
    _ = _ := by ring

/-- The mask term at `i ∈ N`, `j ∼ i` for a configuration `(X_ε, X_ν)`, mask `g` with `|g| ≤ m`
and weight `H ≤ D_*²/4`. -/
theorem w1_mask_pt {h : ℝ} (hh : 0 < h) {σ : Config ct.V}
    (hσ : wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0) (Xe Xn : Matrix ct.V ct.V ℝ)
    (hXn : ∀ k l, Xn k l = Xn l k)
    (hfE : ∀ k ∈ w1Ball ct, 0 ≤ Xe k k ∧ Xe k k ≤ ct.Dstar σ ∧
      ∑ l, Xe k l ^ 2 ≤ ct.Dstar σ / h)
    (hfN : ∀ k ∈ w1Ball ct, 0 ≤ Xn k k ∧ Xn k k ≤ ct.Dstar σ ∧
      ∑ l, Xn k l ^ 2 ≤ ct.Dstar σ / h)
    (hoff : ∀ j ∈ w1Ball ct, ∀ k ∈ w1Ball ct, |Xe j k| ≤ ct.Dstar σ)
    (g : ct.V → ℝ) {m : ℝ} (hm : 0 ≤ m) (hg : ∀ k, |g k| ≤ m)
    (Hv : ℝ) (hH0 : 0 ≤ Hv) (hHD : Hv ≤ ct.Dstar σ ^ 2 / 4) {i j : ct.V} (hi : i ∈ ct.N)
    (hj : j ∈ nbhd ct.G ct.S i) :
    |Hv * maskF Xe Xn g j i| ≤ ct.Dstar σ ^ 2 / 4 * (2 * m * ct.Dstar σ ^ 2 / h) := by
  obtain ⟨e1, e2, e3⟩ := hfE i (w1Ball_N ct hi)
  obtain ⟨-, -, f3⟩ := hfE j (w1Ball_NN ct hi hj)
  obtain ⟨-, -, n3⟩ := hfN i (w1Ball_N ct hi)
  have hF := maskF_abs_le hXn hm hg hh e1 e2 (hoff j (w1Ball_NN ct hi hj) i (w1Ball_N ct hi))
    f3 e3 n3
  rw [abs_mul, abs_of_nonneg hH0]
  have hD := w1_Dstar_ge_one ct hσ
  exact mul_le_mul hHD hF (abs_nonneg _) (by positivity)

/-! #### Expectations and sums -/

theorem w1_sum_uvec_E (i : ct.V) (s : Finset ct.V) (g : ct.V → Config ct.V → ℝ) :
    ∑ j ∈ s, ct.uvec i * ct.E (g j) = ct.uvec i * ct.E (fun σ => ∑ j ∈ s, g j σ) := by
  rw [← Finset.mul_sum]
  congr 1
  unfold Contact.E
  rw [lawE_sum]

theorem w1_uvec_N {i : ct.V} (hi : i ∈ ct.N) : ct.uvec i = 1 / Real.sqrt d := by
  simp [Contact.uvec, hi]

/-- Expectation layer of TB.W1sec: a pointwise bound `c₁ (D_*^k r^ε_i + D_*^k r^ν_i)` and (W5)
give `|wSec| ≤ |N| (1/√d) c₁ (2C)`. -/
theorem w1_sec_E (ε : ℝ) (H : Config ct.V → ℝ) (Xe Xn : Config ct.V → Matrix ct.V ct.V ℝ)
    (f : Config ct.V → ct.V → ℝ) (k : ℕ) {c₁ C : ℝ} (hc₁ : 0 ≤ c₁)
    (hpt : ∀ σ, wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 → ∀ i ∈ ct.N,
      |∑ j ∈ nbhd ct.G ct.S i, H σ * (-(aOf d p) * (2 * ε * Xe σ i j *
        maskF (Xe σ) (Xn σ) (f σ) j i + Xn σ i j * maskF (Xe σ) (Xn σ) (f σ) j i -
        Xn σ i i * Xe σ i j * (Xe σ * diagonal (f σ) * Xn σ) i j))| ≤
      c₁ * (ct.Dstar σ ^ k * (Xe σ * Xe σ) i i + ct.Dstar σ ^ k * (Xn σ * Xn σ) i i))
    (hWe : ∀ i ∈ ct.S, ct.E (fun σ => ct.Dstar σ ^ k * (Xe σ * Xe σ) i i) ≤ C)
    (hWn : ∀ i ∈ ct.S, ct.E (fun σ => ct.Dstar σ ^ k * (Xn σ * Xn σ) i i) ≤ C) :
    |wSec ct ε H Xe Xn f| ≤ (ct.N.card : ℝ) * (1 / Real.sqrt d * (c₁ * (2 * C))) := by
  unfold wSec
  simp only [w1_sum_uvec_E]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  rw [← nsmul_eq_mul]
  refine Finset.sum_le_card_nsmul _ _ _ fun i hi => ?_
  rw [abs_mul, abs_of_nonneg (w1_uvec_nonneg ct i), w1_uvec_N ct hi]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine le_trans (w1_abs_E_le ct _) (le_trans (lawE_mono ct.G fun σ hσ => hpt σ hσ i hi) ?_)
  have hiS := w1_N_sub_S ct hi
  have e : lawE ct.G p (aOf d p) ct.yp ct.ym ct.S (fun σ => c₁ * (ct.Dstar σ ^ k *
      (Xe σ * Xe σ) i i + ct.Dstar σ ^ k * (Xn σ * Xn σ) i i)) =
      c₁ * (ct.E (fun σ => ct.Dstar σ ^ k * (Xe σ * Xe σ) i i) +
        ct.E (fun σ => ct.Dstar σ ^ k * (Xn σ * Xn σ) i i)) := by
    rw [lawE_const_mul, lawE_add]
    rfl
  rw [e]
  have := add_le_add (hWe i hiS) (hWn i hiS)
  nlinarith

/-- Expectation layer of TB.W1mask. -/
theorem w1_mask_E (H : Config ct.V → ℝ) (Xe Xn : Config ct.V → Matrix ct.V ct.V ℝ)
    (df : Config ct.V → ct.V → ct.V → ct.V → ℝ) (h : ℝ) {c₂ C : ℝ} (hc₂ : 0 ≤ c₂) (hC : 0 ≤ C)
    (hpt : ∀ σ, wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 → ∀ i ∈ ct.N, ∀ j ∈ nbhd ct.G ct.S i,
      |H σ * maskF (Xe σ) (Xn σ) (df σ i j) j i| ≤
        c₂ * (ct.Dstar σ ^ 5 * (ct.XP h σ * ct.XP h σ) i i +
          ct.Dstar σ ^ 5 * (ct.XP h σ * ct.XP h σ) j j +
          ct.Dstar σ ^ 5 * (ct.XM h σ * ct.XM h σ) i i +
          ct.Dstar σ ^ 5 * (ct.XM h σ * ct.XM h σ) j j))
    (hW : ∀ i ∈ ct.S, ct.E (fun σ => ct.Dstar σ ^ 5 * (ct.XP h σ * ct.XP h σ) i i) ≤ C ∧
      ct.E (fun σ => ct.Dstar σ ^ 5 * (ct.XM h σ * ct.XM h σ) i i) ≤ C) :
    |wMask ct H Xe Xn df| ≤ (ct.N.card : ℝ) * ((d : ℝ) * (1 / Real.sqrt d * (c₂ * (4 * C)))) := by
  unfold wMask
  have hX : 0 ≤ 1 / Real.sqrt d * (c₂ * (4 * C)) := by positivity
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  rw [← nsmul_eq_mul]
  refine Finset.sum_le_card_nsmul _ _ _ fun i hi => ?_
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_card_nsmul _ _ (1 / Real.sqrt d * (c₂ * (4 * C)))
    fun j hj => ?_) ?_
  · rw [abs_mul, abs_of_nonneg (w1_uvec_nonneg ct i), w1_uvec_N ct hi]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine le_trans (w1_abs_E_le ct _) (le_trans (lawE_mono ct.G fun σ hσ =>
      hpt σ hσ i hi j hj) ?_)
    have hiS := w1_N_sub_S ct hi
    have hjS : j ∈ ct.S := (Finset.mem_filter.mp hj).1
    rw [lawE_const_mul, lawE_add, lawE_add, lawE_add]
    have := (hW i hiS).1
    have := (hW j hjS).1
    have := (hW i hiS).2
    have := (hW j hjS).2
    have : ct.E (fun σ => ct.Dstar σ ^ 5 * (ct.XP h σ * ct.XP h σ) i i) +
        ct.E (fun σ => ct.Dstar σ ^ 5 * (ct.XP h σ * ct.XP h σ) j j) +
        ct.E (fun σ => ct.Dstar σ ^ 5 * (ct.XM h σ * ct.XM h σ) i i) +
        ct.E (fun σ => ct.Dstar σ ^ 5 * (ct.XM h σ * ct.XM h σ) j j) ≤ 4 * C := by linarith
    exact mul_le_mul_of_nonneg_left this hc₂
  · rw [nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (w1_card_nbhd ct i) hX

end ContactMom

/-! ### Parameters -/

section Par

/-- Parameters of the `u`-configurations of TB.W1sec (`s = √d`, `t = √h`). -/
theorem w1_par1 {a s h t C N X : ℝ} (hs : 0 < s) (ht : 0 < t) (hh : 0 < h) (ha : 0 ≤ a)
    (ha2 : a ^ 2 ≤ 1 / s ^ 2) (hC : 0 ≤ C) (hN0 : 0 ≤ N) (hN : N ≤ s ^ 2)
    (hX : X ≤ N * (1 / s * (5 * a / (4 * h * s) * (2 * (C / t))))) :
    a * X ≤ 5 / 2 * C * (1 / (s ^ 2 * h * t)) := by
  have e : N * (1 / s * (5 * a / (4 * h * s) * (2 * (C / t)))) =
      5 / 2 * C * (N * a) / (s ^ 2 * h * t) := by field_simp; ring
  have h3 : N * a ^ 2 ≤ s ^ 2 * (1 / s ^ 2) := mul_le_mul hN ha2 (sq_nonneg a) (sq_nonneg s)
  have h4 : s ^ 2 * (1 / s ^ 2) = 1 := by field_simp
  have hden : 0 < s ^ 2 * h * t := by positivity
  calc a * X ≤ a * (5 / 2 * C * (N * a) / (s ^ 2 * h * t)) := by
        rw [← e]; exact mul_le_mul_of_nonneg_left hX ha
    _ = 5 / 2 * C * (N * a ^ 2) / (s ^ 2 * h * t) := by ring
    _ ≤ 5 / 2 * C * 1 / (s ^ 2 * h * t) := by
        apply div_le_div_of_nonneg_right _ hden.le
        exact mul_le_mul_of_nonneg_left (h3.trans h4.le) (by positivity)
    _ = 5 / 2 * C * (1 / (s ^ 2 * h * t)) := by ring

/-- Parameters of the `b`-configurations of TB.W1sec (`dd = d = s²`). -/
theorem w1_par2 {a s dd h t C N X : ℝ} (hs : 0 < s) (hdd : dd = s ^ 2) (ht : 0 < t) (hh : 0 < h)
    (ha : 0 ≤ a) (ha2 : a ^ 2 ≤ 1 / s ^ 2) (hC : 0 ≤ C) (hN0 : 0 ≤ N) (hN : N ≤ s ^ 2)
    (hX : X ≤ N * (1 / s * (5 * a ^ 3 * dd / (4 * h * s) * (2 * (C / t))))) :
    a * X ≤ 5 / 2 * C * (1 / (s ^ 2 * h * t)) := by
  subst hdd
  have e : N * (1 / s * (5 * a ^ 3 * s ^ 2 / (4 * h * s) * (2 * (C / t)))) =
      5 / 2 * C * (N * a ^ 3) / (h * t) := by field_simp; ring
  have ha4 : a ^ 4 ≤ (1 / s ^ 2) ^ 2 := by
    rw [show a ^ 4 = (a ^ 2) ^ 2 by ring]; exact pow_le_pow_left₀ (sq_nonneg a) ha2 2
  have h3 : N * a ^ 4 ≤ s ^ 2 * (1 / s ^ 2) ^ 2 := mul_le_mul hN ha4 (by positivity) (sq_nonneg s)
  have h4 : s ^ 2 * (1 / s ^ 2) ^ 2 = 1 / s ^ 2 := by field_simp
  have hden : 0 < h * t := by positivity
  calc a * X ≤ a * (5 / 2 * C * (N * a ^ 3) / (h * t)) := by
        rw [← e]; exact mul_le_mul_of_nonneg_left hX ha
    _ = 5 / 2 * C * (N * a ^ 4) / (h * t) := by ring
    _ ≤ 5 / 2 * C * (1 / s ^ 2) / (h * t) := by
        apply div_le_div_of_nonneg_right _ hden.le
        exact mul_le_mul_of_nonneg_left (h3.trans h4.le) (by positivity)
    _ = 5 / 2 * C * (1 / (s ^ 2 * h * t)) := by field_simp

/-- Parameters of TB.W1mask (`dd = d = s²`). -/
theorem w1_par3 {a s dd h t C N X : ℝ} (hs : 0 < s) (hdd : dd = s ^ 2) (ht : 0 < t) (hh : 0 < h)
    (ha : 0 ≤ a) (ha2 : a ^ 2 ≤ 1 / s ^ 2) (hC : 0 ≤ C) (hN0 : 0 ≤ N) (hN : N ≤ s ^ 2)
    (hX : X ≤ N * (dd * (1 / s * (a ^ 3 / (h * s) * (4 * (C / t)))))) :
    a * X ≤ 4 * C * (1 / (s ^ 2 * h * t)) := by
  subst hdd
  have e : N * (s ^ 2 * (1 / s * (a ^ 3 / (h * s) * (4 * (C / t))))) =
      4 * C * (N * a ^ 3) / (h * t) := by field_simp
  have ha4 : a ^ 4 ≤ (1 / s ^ 2) ^ 2 := by
    rw [show a ^ 4 = (a ^ 2) ^ 2 by ring]; exact pow_le_pow_left₀ (sq_nonneg a) ha2 2
  have h3 : N * a ^ 4 ≤ s ^ 2 * (1 / s ^ 2) ^ 2 := mul_le_mul hN ha4 (by positivity) (sq_nonneg s)
  have h4 : s ^ 2 * (1 / s ^ 2) ^ 2 = 1 / s ^ 2 := by field_simp
  have hden : 0 < h * t := by positivity
  calc a * X ≤ a * (4 * C * (N * a ^ 3) / (h * t)) := by
        rw [← e]; exact mul_le_mul_of_nonneg_left hX ha
    _ = 4 * C * (N * a ^ 4) / (h * t) := by ring
    _ ≤ 4 * C * (1 / s ^ 2) / (h * t) := by
        apply div_le_div_of_nonneg_right _ hden.le
        exact mul_le_mul_of_nonneg_left (h3.trans h4.le) (by positivity)
    _ = 4 * C * (1 / (s ^ 2 * h * t)) := by field_simp

theorem w1_inv_le_B0P {d p : ℕ} {h : ℝ} (hh : 0 < h) :
    1 / (Real.sqrt d ^ 2 * h * Real.sqrt h) ≤ B0P d p h := by
  rw [Real.sq_sqrt (Nat.cast_nonneg d)]
  unfold B0P vth
  have h1 : 0 ≤ (p : ℝ) / (d * h) := div_nonneg (Nat.cast_nonneg _) (by positivity)
  have h2 : (0 : ℝ) ≤ 1 / (d : ℝ) ^ 10 := by positivity
  linarith

end Par

/-! ### TB.W1sec and TB.W1mask -/

/-- **TB.W1sec** (the secondary terms of (W3)). Given (CL1): `a |wSec| ≤ C B₀` in the four
configurations; in fact `a|wSec| ≤ (5/2) C_W5/(d h^{3/2})` with the (W5) constants at `D_*³`
(masks `u`) and `D_*⁵` (masks `b_±`). -/
theorem weak_sec_of {K Kb c : ℝ} (hK : 0 ≤ K) (hKb : 0 ≤ Kb) (hc : 0 < c)
    (hCL : CL1Shape.{u} K Kb c) :
    ∃ C : ℝ, 0 < C ∧ Eventually fun _c₀ _κ₀ d p h => ∀ ct : Contact.{u} d p,
      aOf d p * |wSec ct 1 ct.OmP (ct.XP h) (ct.XP h) (fun _ => ct.uvec)| ≤ C * B0P d p h ∧
      aOf d p * |wSec ct 1 ct.OmP (ct.XP h) (ct.XP h) (ct.bP h)| ≤ C * B0P d p h ∧
      aOf d p * |wSec ct (-1) ct.OmM (ct.XM h) (ct.XP h) (fun _ => ct.uvec)| ≤ C * B0P d p h ∧
      aOf d p * |wSec ct (-1) ct.OmM (ct.XM h) (ct.XP h) (ct.bM h)| ≤ C * B0P d p h := by
  obtain ⟨C₃, hC₃, hW3⟩ := ward_mean_of_cl1 3 hK hKb hc hCL
  obtain ⟨C₅, hC₅, hW5⟩ := ward_mean_of_cl1 5 hK hKb hc hCL
  refine ⟨5 / 2 * (C₃ + C₅) + 1, by positivity, ((hW3.and hW5).and eventually_h_facts).mono ?_⟩
  rintro c₀ κ₀ d p h ⟨⟨hW3', hW5'⟩, hR, h0, -⟩ ct
  have hd0 : (0 : ℝ) < d := by have := hR.ten_pow_six_le_d; linarith
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.2 hd0
  have hds : (d : ℝ) = Real.sqrt d ^ 2 := (Real.sq_sqrt hd0.le).symm
  have ht : 0 < Real.sqrt h := Real.sqrt_pos.2 h0
  have ha0 : 0 < aOf d p := hR.aOf_pos
  have ha2 : aOf d p ^ 2 ≤ 1 / Real.sqrt d ^ 2 := by rw [← hds]; exact hR.pf_a_sq_le
  have hB := w1_inv_le_B0P (d := d) (p := p) h0
  have hN0 : (0 : ℝ) ≤ ct.N.card := Nat.cast_nonneg _
  have hN : (ct.N.card : ℝ) ≤ Real.sqrt d ^ 2 := hds ▸ w1_card_N ct
  have hsP := w1_XP_symm ct h
  have hsM := w1_XM_symm ct h
  have hopP : ∀ σ, wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 → ∀ w : ct.V → ℝ,
      (∀ k, k ∉ ct.S → w k = 0) → h ^ 2 * ∑ k, (ct.XP h σ *ᵥ w) k ^ 2 ≤ ∑ k, w k ^ 2 :=
    fun σ hσ w hw => shift_opnorm ct.G (posDef_of_wt_ne_zero ct.G hσ).1
      (fun k => (ct.ctx.hyp k).1) h0 w hw
  have hopM : ∀ σ, wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 → ∀ w : ct.V → ℝ,
      (∀ k, k ∉ ct.S → w k = 0) → h ^ 2 * ∑ k, (ct.XM h σ *ᵥ w) k ^ 2 ≤ ∑ k, w k ^ 2 :=
    fun σ hσ w hw => shift_opnorm ct.G (posDef_of_wt_ne_zero ct.G hσ).2
      (fun k => (ct.ctx.hym k).1) h0 w hw
  have hc1u : 0 ≤ 5 * aOf d p / (4 * h * Real.sqrt d) := by positivity
  have hc1b : 0 ≤ 5 * aOf d p ^ 3 * d / (4 * h * Real.sqrt d) := by positivity
  have hmb : ∀ σ, wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 →
      0 < aOf d p ^ 2 * d * ct.Dstar σ ^ 2 / Real.sqrt d := fun σ hσ => by
    have := w1_Dstar_ge_one ct hσ; positivity
  have hC3t : 0 ≤ C₃ / Real.sqrt h := by positivity
  have hC5t : 0 ≤ C₅ / Real.sqrt h := by positivity
  have fin : ∀ Cw X : ℝ, 0 ≤ Cw → Cw ≤ C₃ + C₅ →
      aOf d p * X ≤ 5 / 2 * Cw * (1 / (Real.sqrt d ^ 2 * h * Real.sqrt h)) →
      aOf d p * X ≤ (5 / 2 * (C₃ + C₅) + 1) * B0P d p h := by
    intro Cw X hCw hCwle hX
    have hB0 : 0 ≤ 1 / (Real.sqrt d ^ 2 * h * Real.sqrt h) := by positivity
    have : 5 / 2 * Cw * (1 / (Real.sqrt d ^ 2 * h * Real.sqrt h)) ≤
        (5 / 2 * (C₃ + C₅) + 1) * B0P d p h := by
      have := mul_le_mul_of_nonneg_left hB (by positivity : (0 : ℝ) ≤ 5 / 2 * (C₃ + C₅) + 1)
      nlinarith
    linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `(+, Ω₊, X₊, X₊, u)`
    have k := w1_sec_E ct 1 ct.OmP (ct.XP h) (ct.XP h) (fun _ => ct.uvec) 3 hc1u
      (C := C₃ / Real.sqrt h)
      (fun σ hσ i hi => by
        refine le_trans (w1_sec_pt ct h0 1 (by norm_num) hσ (ct.XP h σ) (ct.XP h σ) (hsP σ)
          (hsP σ) (hopP σ hσ) (hopP σ hσ) (fun k hk => w1_XP_facts ct h0 hσ hk)
          (fun k hk => w1_XP_facts ct h0 hσ hk) ct.uvec (m := 1 / Real.sqrt d) (by positivity)
          (w1_uvec_abs_le ct) (fun k hk => w1_uvec_off ct hk) (ct.OmP σ) (w1_OmP_nonneg ct σ)
          (w1_OmP_le ct hσ) hi) (le_of_eq ?_)
        ring)
      (fun i hi => (hW3' ct i hi).1) (fun i hi => (hW3' ct i hi).1)
    exact fin C₃ _ hC₃.le (by linarith) (w1_par1 hs ht h0 ha0.le ha2 hC₃.le hN0 hN k)
  · -- `(+, Ω₊, X₊, X₊, b₊)`
    have k := w1_sec_E ct 1 ct.OmP (ct.XP h) (ct.XP h) (ct.bP h) 5 hc1b
      (C := C₅ / Real.sqrt h)
      (fun σ hσ i hi => by
        refine le_trans (w1_sec_pt ct h0 1 (by norm_num) hσ (ct.XP h σ) (ct.XP h σ) (hsP σ)
          (hsP σ) (hopP σ hσ) (hopP σ hσ) (fun k hk => w1_XP_facts ct h0 hσ hk)
          (fun k hk => w1_XP_facts ct h0 hσ hk) (ct.bP h σ) (hmb σ hσ)
          (w1_bP_abs_le ct h0 hσ hR) (fun k hk => w1_bP_off ct h σ hk) (ct.OmP σ)
          (w1_OmP_nonneg ct σ) (w1_OmP_le ct hσ) hi) (le_of_eq ?_)
        ring)
      (fun i hi => (hW5' ct i hi).1) (fun i hi => (hW5' ct i hi).1)
    exact fin C₅ _ hC₅.le (by linarith) (w1_par2 hs hds ht h0 ha0.le ha2 hC₅.le hN0 hN k)
  · -- `(-, Ω₋, X₋, X₊, u)`
    have k := w1_sec_E ct (-1) ct.OmM (ct.XM h) (ct.XP h) (fun _ => ct.uvec) 3 hc1u
      (C := C₃ / Real.sqrt h)
      (fun σ hσ i hi => by
        refine le_trans (w1_sec_pt ct h0 (-1) (by norm_num) hσ (ct.XM h σ) (ct.XP h σ) (hsM σ)
          (hsP σ) (hopM σ hσ) (hopP σ hσ) (fun k hk => w1_XM_facts ct h0 hσ hk)
          (fun k hk => w1_XP_facts ct h0 hσ hk) ct.uvec (m := 1 / Real.sqrt d) (by positivity)
          (w1_uvec_abs_le ct) (fun k hk => w1_uvec_off ct hk) (ct.OmM σ) (w1_OmM_nonneg ct hσ)
          (w1_OmM_le ct hσ) hi) (le_of_eq ?_)
        ring)
      (fun i hi => (hW3' ct i hi).2) (fun i hi => (hW3' ct i hi).1)
    exact fin C₃ _ hC₃.le (by linarith) (w1_par1 hs ht h0 ha0.le ha2 hC₃.le hN0 hN k)
  · -- `(-, Ω₋, X₋, X₊, b₋)`
    have k := w1_sec_E ct (-1) ct.OmM (ct.XM h) (ct.XP h) (ct.bM h) 5 hc1b
      (C := C₅ / Real.sqrt h)
      (fun σ hσ i hi => by
        refine le_trans (w1_sec_pt ct h0 (-1) (by norm_num) hσ (ct.XM h σ) (ct.XP h σ) (hsM σ)
          (hsP σ) (hopM σ hσ) (hopP σ hσ) (fun k hk => w1_XM_facts ct h0 hσ hk)
          (fun k hk => w1_XP_facts ct h0 hσ hk) (ct.bM h σ) (hmb σ hσ)
          (w1_bM_abs_le ct h0 hσ hR) (fun k hk => w1_bM_off ct h σ hk) (ct.OmM σ)
          (w1_OmM_nonneg ct hσ) (w1_OmM_le ct hσ) hi) (le_of_eq ?_)
        ring)
      (fun i hi => (hW5' ct i hi).2) (fun i hi => (hW5' ct i hi).1)
    exact fin C₅ _ hC₅.le (by linarith) (w1_par2 hs hds ht h0 ha0.le ha2 hC₅.le hN0 hN k)

/-- **TB.W1mask** (the random-mask derivative). Given (CL1): `a |wMask| ≤ C B₀` for `f = b_±`;
in fact `a|wMask| ≤ 4 C_W5/(d h^{3/2})` with the (W5) constant at `D_*⁵`. -/
theorem weak_mask_of {K Kb c : ℝ} (hK : 0 ≤ K) (hKb : 0 ≤ Kb) (hc : 0 < c)
    (hCL : CL1Shape.{u} K Kb c) :
    ∃ C : ℝ, 0 < C ∧ Eventually fun _c₀ _κ₀ d p h => ∀ ct : Contact.{u} d p,
      aOf d p * |wMask ct ct.OmP (ct.XP h) (ct.XP h) (dbP ct h)| ≤ C * B0P d p h ∧
      aOf d p * |wMask ct ct.OmM (ct.XM h) (ct.XP h) (dbM ct h)| ≤ C * B0P d p h := by
  obtain ⟨C₅, hC₅, hW5⟩ := ward_mean_of_cl1 5 hK hKb hc hCL
  refine ⟨4 * C₅ + 1, by positivity, (hW5.and eventually_h_facts).mono ?_⟩
  rintro c₀ κ₀ d p h ⟨hW5', hR, h0, -⟩ ct
  have hd0 : (0 : ℝ) < d := by have := hR.ten_pow_six_le_d; linarith
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.2 hd0
  have hds : (d : ℝ) = Real.sqrt d ^ 2 := (Real.sq_sqrt hd0.le).symm
  have ht : 0 < Real.sqrt h := Real.sqrt_pos.2 h0
  have ha0 : 0 < aOf d p := hR.aOf_pos
  have ha2 : aOf d p ^ 2 ≤ 1 / Real.sqrt d ^ 2 := by rw [← hds]; exact hR.pf_a_sq_le
  have hB := w1_inv_le_B0P (d := d) (p := p) h0
  have hN0 : (0 : ℝ) ≤ ct.N.card := Nat.cast_nonneg _
  have hN : (ct.N.card : ℝ) ≤ Real.sqrt d ^ 2 := hds ▸ w1_card_N ct
  have hsP := w1_XP_symm ct h
  have hsM := w1_XM_symm ct h
  have hc2 : 0 ≤ aOf d p ^ 3 / (h * Real.sqrt d) := by positivity
  have hC5t : 0 ≤ C₅ / Real.sqrt h := by positivity
  have hrr : ∀ (X : Matrix ct.V ct.V ℝ), (∀ k l, X k l = X l k) → ∀ k, 0 ≤ (X * X) k k :=
    fun X hX k => by
      rw [mul_self_diag_eq hX]
      exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have fin : ∀ X : ℝ, aOf d p * X ≤ 4 * C₅ * (1 / (Real.sqrt d ^ 2 * h * Real.sqrt h)) →
      aOf d p * X ≤ (4 * C₅ + 1) * B0P d p h := by
    intro X hX
    have hB0 : 0 ≤ 1 / (Real.sqrt d ^ 2 * h * Real.sqrt h) := by positivity
    have := mul_le_mul_of_nonneg_left hB (by positivity : (0 : ℝ) ≤ 4 * C₅ + 1)
    nlinarith
  constructor
  · have k := w1_mask_E ct ct.OmP (ct.XP h) (ct.XP h) (dbP ct h) h hc2 hC5t
      (fun σ hσ i hi j hj => by
        have hD := w1_Dstar_ge_one ct hσ
        have hm0 : 0 ≤ 2 * aOf d p ^ 3 * ct.Dstar σ *
            ((ct.XP h σ * ct.XP h σ) i i + (ct.XP h σ * ct.XP h σ) j j) / Real.sqrt d := by
          have := hrr (ct.XP h σ) (hsP σ) i
          have := hrr (ct.XP h σ) (hsP σ) j
          positivity
        refine le_trans (w1_mask_pt ct h0 hσ (ct.XP h σ) (ct.XP h σ) (hsP σ)
          (fun k hk => w1_XP_facts ct h0 hσ hk) (fun k hk => w1_XP_facts ct h0 hσ hk)
          (fun j hj k hk => w1_XP_off_le ct h0 hσ hj hk) (dbP ct h σ i j) hm0
          (w1_dbP_abs_le ct h0 hσ i j) (ct.OmP σ) (w1_OmP_nonneg ct σ) (w1_OmP_le ct hσ) hi hj) ?_
        have h1 := hrr (ct.XM h σ) (hsM σ) i
        have h2 := hrr (ct.XM h σ) (hsM σ) j
        have h5 : 0 ≤ ct.Dstar σ ^ 5 * (ct.XM h σ * ct.XM h σ) i i +
            ct.Dstar σ ^ 5 * (ct.XM h σ * ct.XM h σ) j j := by positivity
        have e : ct.Dstar σ ^ 2 / 4 * (2 * (2 * aOf d p ^ 3 * ct.Dstar σ *
            ((ct.XP h σ * ct.XP h σ) i i + (ct.XP h σ * ct.XP h σ) j j) / Real.sqrt d) *
            ct.Dstar σ ^ 2 / h) = aOf d p ^ 3 / (h * Real.sqrt d) *
            (ct.Dstar σ ^ 5 * (ct.XP h σ * ct.XP h σ) i i +
              ct.Dstar σ ^ 5 * (ct.XP h σ * ct.XP h σ) j j) := by ring
        rw [e]
        have := mul_le_mul_of_nonneg_left h5 hc2
        linarith)
      (fun i hi => hW5' ct i hi)
    exact fin _ (w1_par3 hs hds ht h0 ha0.le ha2 hC₅.le hN0 hN k)
  · have k := w1_mask_E ct ct.OmM (ct.XM h) (ct.XP h) (dbM ct h) h hc2 hC5t
      (fun σ hσ i hi j hj => by
        have hD := w1_Dstar_ge_one ct hσ
        have hm0 : 0 ≤ aOf d p ^ 3 * ct.Dstar σ *
            ((ct.XM h σ * ct.XM h σ) i i + (ct.XM h σ * ct.XM h σ) j j +
              (ct.XP h σ * ct.XP h σ) i i + (ct.XP h σ * ct.XP h σ) j j) / Real.sqrt d := by
          have := hrr (ct.XP h σ) (hsP σ) i
          have := hrr (ct.XP h σ) (hsP σ) j
          have := hrr (ct.XM h σ) (hsM σ) i
          have := hrr (ct.XM h σ) (hsM σ) j
          positivity
        refine le_trans (w1_mask_pt ct h0 hσ (ct.XM h σ) (ct.XP h σ) (hsP σ)
          (fun k hk => w1_XM_facts ct h0 hσ hk) (fun k hk => w1_XP_facts ct h0 hσ hk)
          (fun j hj k hk => w1_XM_off_le ct h0 hσ hj hk) (dbM ct h σ i j) hm0
          (w1_dbM_abs_le ct h0 hσ i j) (ct.OmM σ) (w1_OmM_nonneg ct hσ) (w1_OmM_le ct hσ) hi
          hj) ?_
        have h1 := hrr (ct.XP h σ) (hsP σ) i
        have h2 := hrr (ct.XP h σ) (hsP σ) j
        have h3 := hrr (ct.XM h σ) (hsM σ) i
        have h4 := hrr (ct.XM h σ) (hsM σ) j
        have h5 : 0 ≤ ct.Dstar σ ^ 5 * (ct.XP h σ * ct.XP h σ) i i +
            ct.Dstar σ ^ 5 * (ct.XP h σ * ct.XP h σ) j j +
            ct.Dstar σ ^ 5 * (ct.XM h σ * ct.XM h σ) i i +
            ct.Dstar σ ^ 5 * (ct.XM h σ * ct.XM h σ) j j := by positivity
        have e : ct.Dstar σ ^ 2 / 4 * (2 * (aOf d p ^ 3 * ct.Dstar σ *
            ((ct.XM h σ * ct.XM h σ) i i + (ct.XM h σ * ct.XM h σ) j j +
              (ct.XP h σ * ct.XP h σ) i i + (ct.XP h σ * ct.XP h σ) j j) / Real.sqrt d) *
            ct.Dstar σ ^ 2 / h) = 1 / 2 * (aOf d p ^ 3 / (h * Real.sqrt d) *
            (ct.Dstar σ ^ 5 * (ct.XP h σ * ct.XP h σ) i i +
              ct.Dstar σ ^ 5 * (ct.XP h σ * ct.XP h σ) j j +
              ct.Dstar σ ^ 5 * (ct.XM h σ * ct.XM h σ) i i +
              ct.Dstar σ ^ 5 * (ct.XM h σ * ct.XM h σ) j j)) := by ring
        rw [e]
        have := mul_nonneg hc2 h5
        linarith)
      (fun i hi => hW5' ct i hi)
    exact fin _ (w1_par3 hs hds ht h0 ha0.le ha2 hC₅.le hN0 hN k)

end BiluLinial.Tight.SecB
