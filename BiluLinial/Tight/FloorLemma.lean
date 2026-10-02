/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.Insertion
public import BiluLinial.Tight.ParamsExtra

/-!
# The uniform insertion floor

Blueprint node `D-floor` (source Section 1.1, Lemma "Uniform insertion floor"). If the inherited
core means of the neighbours of the root obey `E (M^±)⁻¹_ii ≤ 1.01`, then
`F_H = E_core E_ξ Φ ≥ 40^{-p}`, i.e. `Z_core ≤ 40^p Σ_σ W_core Φ`.

Sketch (source lines 149–186). Put `κ = a²s²`, `x_± = y_v^±/s`, `u_i^± = y_i^±/s`,
`C_± = κ x_± Σ_N u_i^±`, `t_± = C_±/D_v^±`. For large `d`: `dκ ≤ 1.01`, `c_ij ≤ .01`,
`C_± ≤ 1.01`, `D_v^± ≥ 1 + C_±/1.01`, `t_± ≤ .505`, and `E(q_A + q_B) ≤ 1.01 (t₊ + t₋)` (the
`ξ`-average of `q_A` is the trace of `A` over `N`). Parallel sums give pointwise
`q_A q_B ≥ h (q_A + q_B)` with `h = min_± (a² y_v^±/D_v^±) Σ_N 1/(Z_i⁺ + Z_i⁻)` (physically
`P_J⁺ + P_J⁻` is diagonal). If `t₊ + t₋ ≤ .95`, `E αβ ≥ 1 - 1.01·.95 > 1/40`; otherwise `h > 1/20`,
so `αβ ≥ [1 - .95 (q_A + q_B)]₊` and `E αβ ≥ 1 - .95·1.01² > 1/40`. Jensen:
`E (α₊β₊)^p ≥ (E α₊β₊)^p ≥ 40^{-p}`.

Formalization. The proof works in the normalized coordinates of `Tight/Defs.lean` and is
uniform in `a, s` (`FloorIns.floor_core`, which uses only `d a² s² ≤ 1.01` and `a² s² ≤ 1/100`).
* The `ξ`-average is the involution `flipAt s(i, v)` flipping one root edge: it fixes the core
  weight and `M^±` and negates `b_i` only (`FloorIns.sum_wt_quad`, `FloorIns.sum_wt_qRoot_le`).
* The parallel-sum bound is Cauchy–Schwarz in the `M^±`-inner products (`FloorIns.quad_cs`) for
  the test vectors `u = (P⁺ + P⁻)⁻¹ ξ` written in the two normalizations, for which
  `uᵀ M⁺ u + wᵀ M⁻ w = H` because the off-diagonal parts cancel (`FloorIns.quad_sum_eq`,
  `FloorIns.qRoot_prod`); zero sources need no special treatment.
* The constants are checked in `FloorIns.floor_numeric`, Jensen is `FloorIns.jensen_floor`.
-/

@[expose] public section

namespace BiluLinial.Tight

open Matrix

namespace FloorIns

/-! ### Scalar facts -/

theorem cRoot_mul_self_add {x : ℝ} (hx : 0 ≤ x) : cRoot x * (1 + cRoot x) = x := by
  have h := Real.sq_sqrt (show 0 ≤ 1 + 4 * x by linarith)
  rw [cRoot]
  linear_combination h / 4

theorem cRoot_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ cRoot x := by
  have h : 1 ≤ Real.sqrt (1 + 4 * x) := by
    have := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 1 + 4 * x by linarith)
    rwa [Real.sqrt_one] at this
  rw [cRoot]
  linarith

theorem cRoot_le {x : ℝ} (hx : 0 ≤ x) : cRoot x ≤ x := by
  have h1 := cRoot_mul_self_add hx
  have h2 := cRoot_nonneg hx
  nlinarith

/-- `c(x) ≥ x/(1 + x) ≥ (100/101) x` for `0 ≤ x ≤ 1/100`. -/
theorem le_cRoot {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1 / 100) : x * (100 / 101) ≤ cRoot x := by
  have h1 := cRoot_mul_self_add hx
  have h2 := cRoot_le hx
  have h3 := cRoot_nonneg hx
  nlinarith [mul_nonneg h3 (sub_nonneg.2 h2)]

theorem one_sub_le_max_mul_max {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    1 - (x + y) ≤ max (1 - x) 0 * max (1 - y) 0 := by
  have h0 : 0 ≤ max (1 - x) 0 * max (1 - y) 0 :=
    mul_nonneg (le_max_right _ _) (le_max_right _ _)
  rcases le_total x 1 with h1 | h1
  · rcases le_total y 1 with h2 | h2
    · rw [max_eq_left (by linarith), max_eq_left (by linarith)]
      nlinarith [mul_nonneg hx hy]
    · linarith
  · linarith

/-- Under the product constraint `h (x + y) ≤ x y` with `h ≥ 1/20`,
`(1 - x)₊ (1 - y)₊ ≥ 1 - (19/20)(x + y)`: if one of `x, y` exceeds one, then `x + y ≥ 20/19`. -/
theorem one_sub_le_max_mul_max' {x y h : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hh : 1 / 20 ≤ h)
    (hxy : h * (x + y) ≤ x * y) :
    1 - 19 / 20 * (x + y) ≤ max (1 - x) 0 * max (1 - y) 0 := by
  have h0 : 0 ≤ max (1 - x) 0 * max (1 - y) 0 :=
    mul_nonneg (le_max_right _ _) (le_max_right _ _)
  have hxy' : (x + y) / 20 ≤ x * y := by
    nlinarith [mul_nonneg (sub_nonneg.2 hh) (add_nonneg hx hy)]
  rcases le_total x 1 with h1 | h1
  · rcases le_total y 1 with h2 | h2
    · rw [max_eq_left (by linarith), max_eq_left (by linarith)]
      nlinarith
    · have h3 : 0 < 20 * y - 1 := by linarith
      have h4 : 0 ≤ (y - 1) * (19 * y - 1) := mul_nonneg (by linarith) (by linarith)
      by_contra hc
      have h5 : 0 < (20 - 19 * (x + y)) * (20 * y - 1) := mul_pos (by linarith) h3
      nlinarith
  · have h3 : 0 < 20 * x - 1 := by linarith
    have h4 : 0 ≤ (x - 1) * (19 * x - 1) := mul_nonneg (by linarith) (by linarith)
    by_contra hc
    have h5 : 0 < (20 - 19 * (x + y)) * (20 * x - 1) := mul_pos (by linarith) h3
    nlinarith

/-- One term of the parallel sum: `y⁺y⁻/(D⁺y⁻ + D⁻y⁺) ≥ (y⁺ + y⁻ - s)/(2 · 2.01)`. -/
theorem term_lower {yp ym Dp Dm s : ℝ} (h1 : 0 ≤ yp) (h2 : yp ≤ s) (h3 : 0 ≤ ym) (h4 : ym ≤ s)
    (hDp : 1 ≤ Dp) (hDp' : Dp ≤ 201 / 100) (hDm : 1 ≤ Dm) (hDm' : Dm ≤ 201 / 100) :
    (yp + ym - s) / (2 * (201 / 100)) ≤ yp * ym * (Dp * ym + Dm * yp)⁻¹ := by
  rcases h1.eq_or_lt with rfl | hp
  · simp only [zero_mul, zero_add]
    rw [div_nonpos_iff]
    right
    constructor <;> linarith
  rcases h3.eq_or_lt with rfl | hm
  · simp only [mul_zero, zero_mul, add_zero]
    rw [div_nonpos_iff]
    right
    constructor <;> linarith
  have hden : 0 < Dp * ym + Dm * yp := by positivity
  rw [← div_eq_mul_inv, div_le_div_iff₀ (by norm_num) hden]
  rcases le_total (yp + ym - s) 0 with h | h
  · nlinarith [mul_pos hp hm]
  · have e1 : Dp * ym + Dm * yp ≤ 201 / 100 * (yp + ym) := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left e1 h, mul_nonneg h1 (sub_nonneg.2 h2),
      mul_nonneg h3 (sub_nonneg.2 h4)]

/-- The scalar product constraint: from `k⁺ H² ≤ U E⁺`, `k⁻ H² ≤ W E⁻` and `U + W = H`,
`min(k⁺/D⁺, k⁻/D⁻) H (q_A + q_B) ≤ q_A q_B` for `q_A = E⁺/D⁺`, `q_B = E⁻/D⁻`. -/
theorem prod_scalar {kp km Ep Em Dp Dm U W H : ℝ} (hkp : 0 ≤ kp) (hkm : 0 ≤ km) (hEp : 0 ≤ Ep)
    (hEm : 0 ≤ Em) (hDp : 0 < Dp) (hDm : 0 < Dm) (hU : 0 ≤ U) (hW : 0 ≤ W) (hUW : U + W = H)
    (h1 : kp * H ^ 2 ≤ U * Ep) (h2 : km * H ^ 2 ≤ W * Em) :
    min (kp / Dp) (km / Dm) * H * (Ep / Dp + Em / Dm) ≤ Ep / Dp * (Em / Dm) := by
  set m := min (kp / Dp) (km / Dm)
  set qA := Ep / Dp
  set qB := Em / Dm
  have hqA : 0 ≤ qA := div_nonneg hEp hDp.le
  have hqB : 0 ≤ qB := div_nonneg hEm hDm.le
  have hm0 : 0 ≤ m := le_min (div_nonneg hkp hDp.le) (div_nonneg hkm hDm.le)
  have g1 : m * H ^ 2 ≤ U * qA := by
    have : kp / Dp * H ^ 2 ≤ U * qA := by
      simp only [qA]
      rw [div_mul_eq_mul_div, mul_div_assoc', div_le_div_iff_of_pos_right hDp]
      exact h1
    exact le_trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg H)) this
  have g2 : m * H ^ 2 ≤ W * qB := by
    have : km / Dm * H ^ 2 ≤ W * qB := by
      simp only [qB]
      rw [div_mul_eq_mul_div, mul_div_assoc', div_le_div_iff_of_pos_right hDm]
      exact h2
    exact le_trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg H)) this
  have hH0 : 0 ≤ H := hUW ▸ add_nonneg hU hW
  rcases hH0.eq_or_lt with h | h
  · rw [← h, mul_zero, zero_mul]
    exact mul_nonneg hqA hqB
  · have e1 := mul_le_mul_of_nonneg_right g1 hqB
    have e2 := mul_le_mul_of_nonneg_right g2 hqA
    have : H * (m * H * (qA + qB)) ≤ H * (qA * qB) := by
      have l : H * (m * H * (qA + qB)) = m * H ^ 2 * qB + m * H ^ 2 * qA := by ring
      have r : H * (qA * qB) = U * qA * qB + W * qB * qA := by rw [← hUW]; ring
      rw [l, r]
      linarith
    exact le_of_mul_le_mul_left this h

/-- The numerical core of the floor lemma, in terms of `C_± = a² y_v^± Σ_N y_i^±`,
`t_± = C_±/D_v^±` and a lower bound for the parallel sum `H`. -/
theorem floor_numeric {a s d n yvp yvm Sp Sm Dvp Dvm H : ℝ}
    (ha : 0 < a) (hs : 0 < s) (hn : n ≤ d) (hdk : d * (a ^ 2 * s ^ 2) ≤ 101 / 100)
    (hvp : 0 ≤ yvp) (hvp' : yvp ≤ s) (hvm : 0 ≤ yvm) (hvm' : yvm ≤ s)
    (hSp : 0 ≤ Sp) (hSp' : Sp ≤ n * s) (hSm : 0 ≤ Sm) (hSm' : Sm ≤ n * s)
    (hDvp : 1 + a ^ 2 * yvp * Sp * (100 / 101) ≤ Dvp) (hDvp' : Dvp ≤ 1 + a ^ 2 * yvp * Sp)
    (hDvm : 1 + a ^ 2 * yvm * Sm * (100 / 101) ≤ Dvm) (hDvm' : Dvm ≤ 1 + a ^ 2 * yvm * Sm)
    (hH : (Sp + Sm - n * s) / (2 * (201 / 100)) ≤ H) (hH0 : 0 ≤ H) :
    a ^ 2 * yvp * Sp / Dvp + a ^ 2 * yvm * Sm / Dvm ≤ 101 / 100 ∧
      (a ^ 2 * yvp * Sp / Dvp + a ^ 2 * yvm * Sm / Dvm ≤ 95 / 100 ∨
        1 / 20 ≤ min (a ^ 2 * yvp / Dvp) (a ^ 2 * yvm / Dvm) * H) := by
  have ha2 : 0 ≤ a ^ 2 := sq_nonneg a
  have hk0 : 0 ≤ a ^ 2 * s ^ 2 := by positivity
  have hn0 : 0 ≤ n := by
    by_contra h
    nlinarith [mul_neg_of_neg_of_pos (not_le.1 h) hs]
  have hns : n * (a ^ 2 * s ^ 2) ≤ 101 / 100 := le_trans (mul_le_mul_of_nonneg_right hn hk0) hdk
  have branch : ∀ {yv S' Dv : ℝ}, 0 ≤ yv → yv ≤ s → 0 ≤ S' → S' ≤ n * s →
      1 + a ^ 2 * yv * S' * (100 / 101) ≤ Dv → Dv ≤ 1 + a ^ 2 * yv * S' →
      0 < Dv ∧ a ^ 2 * yv * S' / Dv ≤ 505 / 1000 ∧
      (445 / 1000 < a ^ 2 * yv * S' / Dv →
        78 / 100 * s < yv ∧ 79 / 100 < a ^ 2 * s * S' ∧ Dv ≤ 201 / 100) := by
    intro yv S' Dv h1 h2 h3 h4 h5 h6
    have hC0 : 0 ≤ a ^ 2 * yv * S' := mul_nonneg (mul_nonneg ha2 h1) h3
    have hCs : a ^ 2 * yv * S' * s ≤ 101 / 100 * yv := by
      have e1 : a ^ 2 * yv * S' * s ≤ a ^ 2 * yv * (n * s) * s :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h4 (mul_nonneg ha2 h1)) hs.le
      have e2 : a ^ 2 * yv * (n * s) * s = yv * (n * (a ^ 2 * s ^ 2)) := by ring
      have e3 := mul_le_mul_of_nonneg_left hns h1
      linarith
    have hC1 : a ^ 2 * yv * S' ≤ 101 / 100 := by
      have : a ^ 2 * yv * S' * s ≤ 101 / 100 * s := by nlinarith
      exact le_of_mul_le_mul_right this hs
    have hD0 : 0 < Dv := by linarith
    refine ⟨hD0, ?_, ?_⟩
    · rw [div_le_iff₀ hD0]
      linarith
    · intro ht
      rw [lt_div_iff₀ hD0] at ht
      have hC79 : 79 / 100 < a ^ 2 * yv * S' := by linarith
      refine ⟨?_, ?_, by linarith⟩
      · have := mul_lt_mul_of_pos_right hC79 hs
        linarith
      · have : a ^ 2 * yv * S' ≤ a ^ 2 * s * S' :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 ha2) h3
        linarith
  obtain ⟨hDp0, htp, hBp⟩ := branch hvp hvp' hSp hSp' hDvp hDvp'
  obtain ⟨hDm0, htm, hBm⟩ := branch hvm hvm' hSm hSm' hDvm hDvm'
  refine ⟨by linarith, ?_⟩
  by_cases hcase : a ^ 2 * yvp * Sp / Dvp + a ^ 2 * yvm * Sm / Dvm ≤ 95 / 100
  · exact Or.inl hcase
  right
  replace hcase := not_le.1 hcase
  obtain ⟨hyp78, hSp79, hDp2⟩ := hBp (by linarith)
  obtain ⟨hym78, hSm79, hDm2⟩ := hBm (by linarith)
  have hX : 57 / 100 / (2 * (201 / 100)) ≤ a ^ 2 * s * H := by
    have h1 : a ^ 2 * s * ((Sp + Sm - n * s) / (2 * (201 / 100))) ≤ a ^ 2 * s * H :=
      mul_le_mul_of_nonneg_left hH (mul_nonneg ha2 hs.le)
    have h2 : a ^ 2 * s * (n * s) ≤ 101 / 100 := by
      have : a ^ 2 * s * (n * s) = n * (a ^ 2 * s ^ 2) := by ring
      linarith
    have h3 : a ^ 2 * s * ((Sp + Sm - n * s) / (2 * (201 / 100))) =
        (a ^ 2 * s * Sp + a ^ 2 * s * Sm - a ^ 2 * s * (n * s)) / (2 * (201 / 100)) := by ring
    rw [h3] at h1
    have h4 : 57 / 100 ≤ a ^ 2 * s * Sp + a ^ 2 * s * Sm - a ^ 2 * s * (n * s) := by linarith
    exact le_trans (div_le_div_of_nonneg_right h4 (by norm_num)) h1
  have key : ∀ {yv Dv : ℝ}, 0 < Dv → Dv ≤ 201 / 100 → 78 / 100 * s < yv →
      1 / 20 ≤ a ^ 2 * yv / Dv * H := by
    intro yv Dv h1 h2 h3
    rw [div_mul_eq_mul_div, le_div_iff₀ h1]
    have hH' : 0 ≤ a ^ 2 * H := mul_nonneg ha2 hH0
    have h4 := mul_le_mul_of_nonneg_left h3.le hH'
    nlinarith
  rw [min_mul_of_nonneg _ _ hH0]
  exact le_min (key hDp0 hDp2 hyp78) (key hDm0 hDm2 hym78)

/-! ### Neighbourhoods, edge weights and diagonals -/

section Graph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] in
theorem mem_nbhd {S : Finset V} {v i : V} : i ∈ nbhd G S v ↔ i ∈ S ∧ G.Adj v i := by
  simp [nbhd]

omit [Fintype V] [DecidableEq V] in
theorem ne_of_mem_nbhd {S : Finset V} {v i : V} (h : i ∈ nbhd G S v) : i ≠ v := by
  rintro rfl
  exact G.irrefl ((mem_nbhd G).1 h).2

omit [DecidableEq V] in
theorem card_nbhd_le (S : Finset V) (v : V) : (nbhd G S v).card ≤ G.degree v := by
  rw [← G.card_neighborFinset_eq_degree]
  apply Finset.card_le_card
  intro w hw
  exact (G.mem_neighborFinset v w).2 ((mem_nbhd G).1 hw).2

omit [Fintype V] [DecidableEq V] in
theorem edge_nonneg {a : ℝ} {y : V → ℝ} (hy : ∀ i, 0 ≤ y i) (i j : V) :
    0 ≤ a ^ 2 * y i * y j :=
  mul_nonneg (mul_nonneg (sq_nonneg a) (hy i)) (hy j)

omit [Fintype V] [DecidableEq V] in
theorem edge_le_kappa {a s : ℝ} {y : V → ℝ} (hy : InCube s y) (i j : V) :
    a ^ 2 * y i * y j ≤ a ^ 2 * s ^ 2 := by
  have h1 := hy i
  have h2 := hy j
  have : y i * y j ≤ s * s := mul_le_mul h1.2 h2.2 h2.1 (h1.1.trans h1.2)
  have := mul_le_mul_of_nonneg_left this (sq_nonneg a)
  linarith

omit [Fintype V] [DecidableEq V] in
theorem one_le_diagD (a : ℝ) {y : V → ℝ} (hy : ∀ i, 0 ≤ y i) (S : Finset V) (i : V) :
    1 ≤ diagD G a y S i := by
  rw [diagD]
  have : 0 ≤ ∑ j ∈ nbhd G S i, cEdge a y i j :=
    Finset.sum_nonneg fun j _ => cRoot_nonneg (edge_nonneg hy i j)
  linarith

omit [DecidableEq V] in
theorem diagD_le {a s : ℝ} {d : ℕ} (hdeg : ∀ v, G.degree v ≤ d)
    (hdk : (d : ℝ) * (a ^ 2 * s ^ 2) ≤ 101 / 100) {y : V → ℝ} (hy : InCube s y)
    (S : Finset V) (i : V) : diagD G a y S i ≤ 201 / 100 := by
  have hy0 : ∀ i, 0 ≤ y i := fun i => (hy i).1
  have hsum : ∑ j ∈ nbhd G S i, cEdge a y i j ≤ (nbhd G S i).card • (a ^ 2 * s ^ 2) :=
    Finset.sum_le_card_nsmul _ _ _ fun j _ =>
      (cRoot_le (edge_nonneg hy0 i j)).trans (edge_le_kappa hy i j)
  rw [nsmul_eq_mul] at hsum
  have hc : ((nbhd G S i).card : ℝ) ≤ d := by
    exact_mod_cast (card_nbhd_le G S i).trans (hdeg i)
  have hk0 : 0 ≤ a ^ 2 * s ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_right hc hk0
  rw [diagD]
  linarith

omit [Fintype V] [DecidableEq V] in
theorem diagD_root_bounds {a s : ℝ} (hk : a ^ 2 * s ^ 2 ≤ 1 / 100) {y : V → ℝ}
    (hy : InCube s y) (S : Finset V) (v : V) :
    1 + a ^ 2 * y v * (∑ j ∈ nbhd G S v, y j) * (100 / 101) ≤ diagD G a y S v ∧
      diagD G a y S v ≤ 1 + a ^ 2 * y v * ∑ j ∈ nbhd G S v, y j := by
  have hy0 : ∀ i, 0 ≤ y i := fun i => (hy i).1
  rw [diagD, Finset.mul_sum, Finset.sum_mul]
  constructor
  · have := Finset.sum_le_sum fun j (_ : j ∈ nbhd G S v) =>
      le_cRoot (edge_nonneg hy0 v j) ((edge_le_kappa hy v j).trans hk)
    simp only [cEdge]
    linarith
  · have := Finset.sum_le_sum fun j (_ : j ∈ nbhd G S v) =>
      cRoot_le (edge_nonneg (a := a) hy0 v j)
    simp only [cEdge]
    linarith

/-! ### The core weight -/

theorem wtCore_nonneg (p : ℕ) (a : ℝ) (yp ym : V → ℝ) (σ : Config V) (S : Finset V) (v : V) :
    0 ≤ wtCore G p a yp ym σ S v := by
  rw [wtCore]
  split_ifs with h
  · exact pow_nonneg (mul_nonneg h.1.det_pos.le h.2.det_pos.le) p
  · exact le_rfl

theorem wtCore_support {p : ℕ} {a : ℝ} {yp ym : V → ℝ} {σ : Config V} {S : Finset V} {v : V}
    (h : wtCore G p a yp ym σ S v ≠ 0) :
    (precCore G a 1 yp σ S v).PosDef ∧ (precCore G a (-1) ym σ S v).PosDef := by
  by_contra hc
  exact h (by rw [wtCore, ite_eq_right hc])

/-! ### Flipping the sign of one root edge -/

/-- Flip the sign of the pair `e`. -/
def flipAt (e : Sym2 V) (σ : Config V) : Config V := fun e' => if e' = e then -σ e' else σ e'

omit [Fintype V] in
theorem flipAt_involutive (e : Sym2 V) : Function.Involutive (flipAt (V := V) e) := by
  intro σ
  funext e'
  by_cases h : e' = e <;> simp [flipAt, h]

omit [Fintype V] in
theorem sgn_flipAt (e : Sym2 V) (σ : Config V) (u w : V) :
    sgn (flipAt e σ) u w = if s(u, w) = e then -sgn σ u w else sgn σ u w := by
  unfold sgn flipAt
  split_ifs <;> simp

omit [Fintype V] [DecidableEq V] in
theorem sgn_mul_self (σ : Config V) (u w : V) : sgn σ u w * sgn σ u w = 1 := by
  unfold sgn
  rcases Int.units_eq_one_or (σ s(u, w)) with h | h <;> simp [h]

omit [Fintype V] in
theorem precCore_flipAt (a τ : ℝ) (y : V → ℝ) (S : Finset V) {v : V} {e : Sym2 V} (he : v ∈ e)
    (σ : Config V) : precCore G a τ y (flipAt e σ) S v = precCore G a τ y σ S v := by
  ext u w
  simp only [precCore, precN, Matrix.of_apply]
  by_cases h : u = v ∨ w = v
  · simp only [ite_eq_left h]
  · simp only [ite_eq_right h]
    obtain ⟨hu, hw⟩ := not_or.1 h
    have hne : s(u, w) ≠ e := by
      rintro rfl
      rcases Sym2.mem_iff.1 he with h' | h'
      · exact hu h'.symm
      · exact hw h'.symm
    rw [sgn_flipAt, ite_eq_right hne]

theorem wtCore_flipAt (p : ℕ) (a : ℝ) (yp ym : V → ℝ) (S : Finset V) {v : V} {e : Sym2 V}
    (he : v ∈ e) (σ : Config V) :
    wtCore G p a yp ym (flipAt e σ) S v = wtCore G p a yp ym σ S v := by
  unfold wtCore
  rw [precCore_flipAt G _ _ _ _ he, precCore_flipAt G _ _ _ _ he]

omit [Fintype V] in
theorem incCol_apply (a τ : ℝ) (y : V → ℝ) (σ : Config V) {S : Finset V} {v : V} (hv : v ∈ S)
    (i : V) : incCol G a τ y σ S v i = if i ∈ nbhd G S v then
      τ * a * (Real.sqrt (y i) * Real.sqrt (y v)) * sgn σ i v else 0 := by
  by_cases hi : i = v
  · subst hi
    have : i ∉ nbhd G S i := fun h => ne_of_mem_nbhd G h rfl
    simp [incCol, this]
  · simp only [incCol, precN, Matrix.of_apply, ite_eq_right hi]
    have hN : i ∈ nbhd G S v ↔ i ∈ S ∧ v ∈ S ∧ G.Adj i v := by
      rw [mem_nbhd, G.adj_comm]
      tauto
    by_cases h : i ∈ nbhd G S v
    · rw [ite_eq_left h, ite_eq_left (hN.1 h)]
    · rw [ite_eq_right h, ite_eq_right (mt hN.2 h)]

omit [Fintype V] in
theorem incCol_flipAt_self (a τ : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) {v i : V}
    (hi : i ≠ v) : incCol G a τ y (flipAt s(i, v) σ) S v i = -incCol G a τ y σ S v i := by
  simp only [incCol, precN, Matrix.of_apply, ite_eq_right hi]
  rw [sgn_flipAt, ite_eq_left rfl]
  split_ifs <;> ring

omit [Fintype V] in
theorem incCol_flipAt_ne (a τ : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) {v i j : V}
    (hj : j ≠ i) : incCol G a τ y (flipAt s(i, v) σ) S v j = incCol G a τ y σ S v j := by
  by_cases hjv : j = v
  · simp only [incCol, ite_eq_left hjv]
  · simp only [incCol, precN, Matrix.of_apply, ite_eq_right hjv]
    have hne : s(j, v) ≠ s(i, v) := fun h => hj (Sym2.congr_left.1 h)
    rw [sgn_flipAt, ite_eq_right hne]

omit [Fintype V] in
theorem incCol_sq {τ : ℝ} (hτ : τ ^ 2 = 1) {a : ℝ} {y : V → ℝ} (hy : ∀ i, 0 ≤ y i)
    {S : Finset V} {v : V} (hv : v ∈ S) (σ : Config V) (i : V) :
    incCol G a τ y σ S v i ^ 2 = if i ∈ nbhd G S v then a ^ 2 * y i * y v else 0 := by
  rw [incCol_apply G a τ y σ hv i]
  split_ifs
  · have h1 := Real.mul_self_sqrt (hy i)
    have h2 := Real.mul_self_sqrt (hy v)
    have h3 := sgn_mul_self σ i v
    calc (τ * a * (Real.sqrt (y i) * Real.sqrt (y v)) * sgn σ i v) ^ 2
        = τ ^ 2 * a ^ 2 * (Real.sqrt (y i) * Real.sqrt (y i)) *
            (Real.sqrt (y v) * Real.sqrt (y v)) * (sgn σ i v * sgn σ i v) := by ring
      _ = a ^ 2 * y i * y v := by rw [hτ, h1, h2, h3]; ring
  · simp

theorem sum_flip_eq_zero (e : Sym2 V) {F : Config V → ℝ} (hF : ∀ σ, F (flipAt e σ) = -F σ) :
    ∑ σ, F σ = 0 := by
  have h := Equiv.sum_comp ((flipAt_involutive e).toPerm _) F
  simp only [Function.Involutive.coe_toPerm, hF, Finset.sum_neg_distrib] at h
  linarith

/-- Averaging over the signs of the root edges kills the off-diagonal part of `bᵀ M⁻¹ b`. -/
theorem sum_wt_quad (W : Config V → ℝ) (a τ : ℝ) (y : V → ℝ) (S : Finset V) (v : V)
    (hW : ∀ i, i ≠ v → ∀ σ, W (flipAt s(i, v) σ) = W σ) :
    ∑ σ, W σ * (incCol G a τ y σ S v ⬝ᵥ ((precCore G a τ y σ S v)⁻¹ *ᵥ incCol G a τ y σ S v)) =
      ∑ i, ∑ σ, W σ * (incCol G a τ y σ S v i ^ 2 * (precCore G a τ y σ S v)⁻¹ i i) := by
  have expand : ∀ σ, W σ * (incCol G a τ y σ S v ⬝ᵥ
      ((precCore G a τ y σ S v)⁻¹ *ᵥ incCol G a τ y σ S v)) =
      ∑ i, ∑ j, W σ * (incCol G a τ y σ S v i * (precCore G a τ y σ S v)⁻¹ i j *
        incCol G a τ y σ S v j) := by
    intro σ
    simp only [dotProduct, mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  simp_rw [expand]
  refine Finset.sum_comm.trans (Finset.sum_congr rfl fun i _ => ?_)
  refine Finset.sum_comm.trans ?_
  rw [Finset.sum_eq_single i]
  · exact Finset.sum_congr rfl fun σ _ => by ring
  · intro j _ hji
    by_cases hiv : i = v
    · subst hiv
      exact Finset.sum_eq_zero fun σ _ => by simp [incCol]
    · apply sum_flip_eq_zero s(i, v)
      intro σ
      rw [hW i hiv, precCore_flipAt G _ _ _ _ (Sym2.mem_mk_right i v),
        incCol_flipAt_self G _ _ _ _ _ hiv, incCol_flipAt_ne G _ _ _ _ _ hji]
      ring
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- `E q ≤ B · a² y_v Σ_N y_i / D_v` if every inherited inverse diagonal has `Σ_σ W M⁻¹_ii ≤ B`. -/
theorem sum_wt_qRoot_le {v : V} (W : Config V → ℝ)
    (hW : ∀ i, i ≠ v → ∀ σ, W (flipAt s(i, v) σ) = W σ) {τ : ℝ} (hτ : τ ^ 2 = 1) (a : ℝ)
    {y : V → ℝ} (hy : ∀ i, 0 ≤ y i) {S : Finset V} (hv : v ∈ S) (hD : 0 < diagD G a y S v)
    {B : ℝ} (hB : ∀ i ∈ nbhd G S v, ∑ σ, W σ * (precCore G a τ y σ S v)⁻¹ i i ≤ B) :
    ∑ σ, W σ * qRoot G a τ y σ S v ≤
      B * (a ^ 2 * y v * (∑ i ∈ nbhd G S v, y i) / diagD G a y S v) := by
  have h1 : ∑ σ, W σ * qRoot G a τ y σ S v =
      (∑ σ, W σ * (incCol G a τ y σ S v ⬝ᵥ
        ((precCore G a τ y σ S v)⁻¹ *ᵥ incCol G a τ y σ S v))) / diagD G a y S v := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun σ _ => by rw [qRoot, mul_div_assoc]
  rw [h1, sum_wt_quad G W a τ y S v hW, mul_div_assoc', div_le_div_iff_of_pos_right hD]
  have h2 : ∀ i, ∑ σ, W σ * (incCol G a τ y σ S v i ^ 2 * (precCore G a τ y σ S v)⁻¹ i i) =
      if i ∈ nbhd G S v then
        a ^ 2 * y i * y v * ∑ σ, W σ * (precCore G a τ y σ S v)⁻¹ i i else 0 := by
    intro i
    simp only [incCol_sq G hτ hy hv]
    by_cases hi : i ∈ nbhd G S v
    · simp only [ite_eq_left hi, Finset.mul_sum]
      exact Finset.sum_congr rfl fun σ _ => by ring
    · simp [hi]
  simp_rw [h2]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  calc a ^ 2 * y i * y v * ∑ σ, W σ * (precCore G a τ y σ S v)⁻¹ i i
      ≤ a ^ 2 * y i * y v * B :=
        mul_le_mul_of_nonneg_left (hB i hi) (edge_nonneg hy i v)
    _ = B * (a ^ 2 * y v * y i) := by ring

/-! ### The parallel-sum product bound -/

/-- Cauchy–Schwarz in the `X`-inner product: `(f ⬝ u)² ≤ (uᵀ X u)(fᵀ X⁻¹ f)`. -/
theorem quad_cs {n : Type*} [Fintype n] [DecidableEq n] {X : Matrix n n ℝ} (hX : X.PosDef)
    (f u : n → ℝ) : (f ⬝ᵥ u) ^ 2 ≤ (u ⬝ᵥ (X *ᵥ u)) * (f ⬝ᵥ (X⁻¹ *ᵥ f)) := by
  set z := X⁻¹ *ᵥ f with hz
  have hdet : IsUnit X.det := (Matrix.isUnit_iff_isUnit_det X).1 hX.isUnit
  have hXz : X *ᵥ z = f := by
    rw [hz, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv X hdet, Matrix.one_mulVec]
  have hT : Xᵀ = X := by
    have := hX.isHermitian
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hsym : ∀ x y : n → ℝ, x ⬝ᵥ (X *ᵥ y) = y ⬝ᵥ (X *ᵥ x) := by
    intro x y
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hT, dotProduct_comm]
  have hq : ∀ t : ℝ, 0 ≤ (u ⬝ᵥ (X *ᵥ u)) * (t * t) + (-2 * (f ⬝ᵥ u)) * t + (f ⬝ᵥ z) := by
    intro t
    have h0 := hX.posSemidef.dotProduct_mulVec_nonneg (t • u - z)
    rw [star_trivial] at h0
    have e1 : X *ᵥ (t • u - z) = t • (X *ᵥ u) - f := by
      rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hXz]
    rw [e1] at h0
    simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
      smul_eq_mul] at h0
    have e2 : z ⬝ᵥ (X *ᵥ u) = f ⬝ᵥ u := by rw [hsym, hXz, dotProduct_comm]
    have e3 : u ⬝ᵥ f = f ⬝ᵥ u := dotProduct_comm _ _
    have e4 : z ⬝ᵥ f = f ⬝ᵥ z := dotProduct_comm _ _
    rw [e2, e3, e4] at h0
    linarith
  have := discrim_le_zero hq
  rw [discrim] at this
  nlinarith

theorem qRoot_nonneg {a τ : ℝ} {y : V → ℝ} {σ : Config V} {S : Finset V} {v : V}
    (hM : (precCore G a τ y σ S v).PosDef) (hD : 0 < diagD G a y S v) :
    0 ≤ qRoot G a τ y σ S v := by
  unfold qRoot
  apply div_nonneg _ hD.le
  simpa using hM.inv.posSemidef.dotProduct_mulVec_nonneg (incCol G a τ y σ S v)

omit [Fintype V] [DecidableEq V] in
theorem inv_sq_mul_self (x : ℝ) : x⁻¹ ^ 2 * x = x⁻¹ := by
  rcases eq_or_ne x 0 with rfl | h
  · simp
  · field_simp

/-- The parallel sum `H = Σ_N y_i⁺ y_i⁻/(D_i⁺ y_i⁻ + D_i⁻ y_i⁺) = Σ_N 1/(Z_i⁺ + Z_i⁻)`. -/
noncomputable def parSum (a : ℝ) (yp ym : V → ℝ) (S : Finset V) (v : V) : ℝ :=
  ∑ i ∈ nbhd G S v, yp i * ym i * (diagD G a yp S i * ym i + diagD G a ym S i * yp i)⁻¹

/-- The test vectors `u = (P⁺ + P⁻)⁻¹ ξ` (in the two normalizations) satisfy
`uᵀ M⁺ u + wᵀ M⁻ w = H`: the off-diagonal parts of `M^±` cancel. -/
theorem quad_sum_eq (a : ℝ) (yp ym : V → ℝ) {S : Finset V} {v : V} (σ : Config V)
    (ρ u w : V → ℝ)
    (hρ : ∀ i, ρ i = (diagD G a yp S i * Real.sqrt (ym i) ^ 2 +
      diagD G a ym S i * Real.sqrt (yp i) ^ 2)⁻¹)
    (hu : ∀ i, u i = if i ∈ nbhd G S v then
      sgn σ i v * Real.sqrt (yp i) * Real.sqrt (ym i) ^ 2 * ρ i else 0)
    (hw : ∀ i, w i = if i ∈ nbhd G S v then
      sgn σ i v * Real.sqrt (ym i) * Real.sqrt (yp i) ^ 2 * ρ i else 0) :
    u ⬝ᵥ (precCore G a 1 yp σ S v *ᵥ u) + w ⬝ᵥ (precCore G a (-1) ym σ S v *ᵥ w) =
      ∑ i ∈ nbhd G S v, Real.sqrt (yp i) ^ 2 * Real.sqrt (ym i) ^ 2 * ρ i := by
  have entry : ∀ i j, u i * (precCore G a 1 yp σ S v i j * u j) +
      w i * (precCore G a (-1) ym σ S v i j * w j) = if i = j then
        (if i ∈ nbhd G S v then Real.sqrt (yp i) ^ 2 * Real.sqrt (ym i) ^ 2 * ρ i else 0)
        else 0 := by
    intro i j
    by_cases hi : i ∈ nbhd G S v
    · by_cases hj : j ∈ nbhd G S v
      · have hiv := ne_of_mem_nbhd G hi
        have hjv := ne_of_mem_nbhd G hj
        have hiS := ((mem_nbhd G).1 hi).1
        have hcore : ∀ (τ : ℝ) (y : V → ℝ),
            precCore G a τ y σ S v i j = precN G a τ y σ S i j := by
          intro τ y
          simp only [precCore, Matrix.of_apply]
          rw [ite_eq_right (not_or.2 ⟨hiv, hjv⟩)]
        rw [hcore, hcore]
        simp only [hu, hw, hi, hj, ↓reduceIte]
        by_cases hij : i = j
        · subst hij
          simp only [precN, Matrix.of_apply, hiS, ↓reduceIte]
          have hε := sgn_mul_self σ i v
          have hρ2 : ρ i ^ 2 * (diagD G a yp S i * Real.sqrt (ym i) ^ 2 +
              diagD G a ym S i * Real.sqrt (yp i) ^ 2) = ρ i := by
            rw [hρ i]
            exact inv_sq_mul_self _
          linear_combination (Real.sqrt (yp i) ^ 2 * Real.sqrt (ym i) ^ 2 * ρ i ^ 2 *
              (diagD G a yp S i * Real.sqrt (ym i) ^ 2 +
                diagD G a ym S i * Real.sqrt (yp i) ^ 2)) * hε +
            Real.sqrt (yp i) ^ 2 * Real.sqrt (ym i) ^ 2 * hρ2
        · simp only [precN, Matrix.of_apply, hij, ↓reduceIte]
          split_ifs <;> ring
      · have : i ≠ j := fun h => hj (h ▸ hi)
        simp only [hu, hw, hj, this, ↓reduceIte, mul_zero, add_zero]
    · simp only [hu, hw, hi, ↓reduceIte, zero_mul, add_zero, ite_self]
  have lhs : u ⬝ᵥ (precCore G a 1 yp σ S v *ᵥ u) + w ⬝ᵥ (precCore G a (-1) ym σ S v *ᵥ w) =
      ∑ i, ∑ j, (u i * (precCore G a 1 yp σ S v i j * u j) +
        w i * (precCore G a (-1) ym σ S v i j * w j)) := by
    simp only [dotProduct, mulVec, Finset.mul_sum, ← Finset.sum_add_distrib]
  rw [lhs]
  simp_rw [entry]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

/-- The pointwise product constraint `q_A q_B ≥ h (q_A + q_B)` with
`h = min_± (a² y_v^±/D_v^±) H`. -/
theorem qRoot_prod (a : ℝ) {yp ym : V → ℝ} (hyp : ∀ i, 0 ≤ yp i) (hym : ∀ i, 0 ≤ ym i)
    {S : Finset V} {v : V} (hv : v ∈ S) {σ : Config V}
    (hDp : 0 < diagD G a yp S v) (hDm : 0 < diagD G a ym S v)
    (hMp : (precCore G a 1 yp σ S v).PosDef) (hMm : (precCore G a (-1) ym σ S v).PosDef) :
    min (a ^ 2 * yp v / diagD G a yp S v) (a ^ 2 * ym v / diagD G a ym S v) *
        parSum G a yp ym S v * (qRoot G a 1 yp σ S v + qRoot G a (-1) ym σ S v) ≤
      qRoot G a 1 yp σ S v * qRoot G a (-1) ym σ S v := by
  obtain ⟨ρ, hρ⟩ : ∃ ρ : V → ℝ, ∀ i, ρ i = (diagD G a yp S i * Real.sqrt (ym i) ^ 2 +
      diagD G a ym S i * Real.sqrt (yp i) ^ 2)⁻¹ := ⟨_, fun i => rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : V → ℝ, ∀ i, u i = if i ∈ nbhd G S v then
      sgn σ i v * Real.sqrt (yp i) * Real.sqrt (ym i) ^ 2 * ρ i else 0 := ⟨_, fun i => rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : V → ℝ, ∀ i, w i = if i ∈ nbhd G S v then
      sgn σ i v * Real.sqrt (ym i) * Real.sqrt (yp i) ^ 2 * ρ i else 0 := ⟨_, fun i => rfl⟩
  set H := ∑ i ∈ nbhd G S v, Real.sqrt (yp i) ^ 2 * Real.sqrt (ym i) ^ 2 * ρ i with hH_def
  have hUW := quad_sum_eq G a yp ym σ ρ u w hρ hu hw
  have hU : 0 ≤ u ⬝ᵥ (precCore G a 1 yp σ S v *ᵥ u) := by
    simpa using hMp.posSemidef.dotProduct_mulVec_nonneg u
  have hW : 0 ≤ w ⬝ᵥ (precCore G a (-1) ym σ S v *ᵥ w) := by
    simpa using hMm.posSemidef.dotProduct_mulVec_nonneg w
  have hbu : incCol G a 1 yp σ S v ⬝ᵥ u = a * Real.sqrt (yp v) * H := by
    have e : ∀ i, incCol G a 1 yp σ S v i * u i = if i ∈ nbhd G S v then
        a * Real.sqrt (yp v) * (Real.sqrt (yp i) ^ 2 * Real.sqrt (ym i) ^ 2 * ρ i) else 0 := by
      intro i
      rw [incCol_apply G a 1 yp σ hv i, hu i]
      split_ifs
      · have hε := sgn_mul_self σ i v
        linear_combination
          (a * Real.sqrt (yp v) * Real.sqrt (yp i) ^ 2 * Real.sqrt (ym i) ^ 2 * ρ i) * hε
      · ring
    simp only [dotProduct, e]
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.mul_sum]
  have hbw : incCol G a (-1) ym σ S v ⬝ᵥ w = -(a * Real.sqrt (ym v)) * H := by
    have e : ∀ i, incCol G a (-1) ym σ S v i * w i = if i ∈ nbhd G S v then
        -(a * Real.sqrt (ym v)) * (Real.sqrt (yp i) ^ 2 * Real.sqrt (ym i) ^ 2 * ρ i)
        else 0 := by
      intro i
      rw [incCol_apply G a (-1) ym σ hv i, hw i]
      split_ifs
      · have hε := sgn_mul_self σ i v
        linear_combination
          (-(a * Real.sqrt (ym v)) * Real.sqrt (yp i) ^ 2 * Real.sqrt (ym i) ^ 2 * ρ i) * hε
      · ring
    simp only [dotProduct, e]
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.mul_sum]
  have h1 : a ^ 2 * yp v * H ^ 2 ≤ u ⬝ᵥ (precCore G a 1 yp σ S v *ᵥ u) *
      (incCol G a 1 yp σ S v ⬝ᵥ ((precCore G a 1 yp σ S v)⁻¹ *ᵥ incCol G a 1 yp σ S v)) := by
    have := quad_cs hMp (incCol G a 1 yp σ S v) u
    rwa [hbu, mul_pow, mul_pow, Real.sq_sqrt (hyp v)] at this
  have h2 : a ^ 2 * ym v * H ^ 2 ≤ w ⬝ᵥ (precCore G a (-1) ym σ S v *ᵥ w) *
      (incCol G a (-1) ym σ S v ⬝ᵥ
        ((precCore G a (-1) ym σ S v)⁻¹ *ᵥ incCol G a (-1) ym σ S v)) := by
    have := quad_cs hMm (incCol G a (-1) ym σ S v) w
    rwa [hbw, mul_pow, neg_sq, mul_pow, Real.sq_sqrt (hym v)] at this
  have hH : H = parSum G a yp ym S v := by
    rw [hH_def, parSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hρ i, Real.sq_sqrt (hyp i), Real.sq_sqrt (hym i)]
  have hEp : 0 ≤ incCol G a 1 yp σ S v ⬝ᵥ
      ((precCore G a 1 yp σ S v)⁻¹ *ᵥ incCol G a 1 yp σ S v) := by
    simpa using hMp.inv.posSemidef.dotProduct_mulVec_nonneg (incCol G a 1 yp σ S v)
  have hEm : 0 ≤ incCol G a (-1) ym σ S v ⬝ᵥ
      ((precCore G a (-1) ym σ S v)⁻¹ *ᵥ incCol G a (-1) ym σ S v) := by
    simpa using hMm.inv.posSemidef.dotProduct_mulVec_nonneg (incCol G a (-1) ym σ S v)
  unfold qRoot
  rw [← hH]
  exact prod_scalar (mul_nonneg (sq_nonneg a) (hyp v)) (mul_nonneg (sq_nonneg a) (hym v))
    hEp hEm hDp hDm hU hW hUW h1 h2

end Graph

/-! ### Averaging -/

/-- `Σ W - k (Σ W x + Σ W y) ≤ Σ W f` if `1 - k (x + y) ≤ f` on the support of `W ≥ 0`. -/
theorem sum_lower {ι : Type*} [Fintype ι] (W f x y : ι → ℝ) (k : ℝ) (hW : ∀ i, 0 ≤ W i)
    (hf : ∀ i, W i ≠ 0 → 1 - k * (x i + y i) ≤ f i) :
    ∑ i, W i - k * (∑ i, W i * x i + ∑ i, W i * y i) ≤ ∑ i, W i * f i := by
  have e : ∑ i, W i - k * (∑ i, W i * x i + ∑ i, W i * y i) =
      ∑ i, W i * (1 - k * (x i + y i)) := by
    rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases h : W i = 0
  · simp [h]
  · exact mul_le_mul_of_nonneg_left (hf i h) (hW i)

/-- Jensen: if `E g ≥ 1/40` under the weights `W`, then `E g^p ≥ 40^{-p}`. -/
theorem jensen_floor {ι : Type*} [Fintype ι] (W g : ι → ℝ) (p : ℕ) (hW : ∀ i, 0 ≤ W i)
    (hZ : 0 < ∑ i, W i) (hg : ∀ i, 0 ≤ g i) (h40 : (∑ i, W i) / 40 ≤ ∑ i, W i * g i) :
    ∑ i, W i ≤ 40 ^ p * ∑ i, W i * g i ^ p := by
  set Z := ∑ i, W i with hZdef
  have hJ := Real.pow_arith_mean_le_arith_mean_pow Finset.univ (fun i => W i / Z) g
    (fun i _ => div_nonneg (hW i) hZ.le) (by rw [← Finset.sum_div]; exact div_self hZ.ne')
    (fun i _ => hg i) p
  have e1 : ∑ i, W i / Z * g i = (∑ i, W i * g i) / Z := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∑ i, W i / Z * g i ^ p = (∑ i, W i * g i ^ p) / Z := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e1, e2] at hJ
  have h1 : 1 / 40 ≤ (∑ i, W i * g i) / Z := by
    rw [le_div_iff₀ hZ]
    linarith
  have h2 : (1 / 40 : ℝ) ^ p ≤ (∑ i, W i * g i ^ p) / Z :=
    le_trans (pow_le_pow_left₀ (by norm_num) h1 p) hJ
  rw [le_div_iff₀ hZ] at h2
  calc Z = 40 ^ p * ((1 / 40) ^ p * Z) := by
        rw [← mul_assoc, ← mul_pow]
        norm_num
    _ ≤ 40 ^ p * ∑ i, W i * g i ^ p := mul_le_mul_of_nonneg_left h2 (by positivity)

/-! ### The floor for generic parameters -/

section Floor

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The floor lemma for any `a, s > 0` with `d a² s² ≤ 1.01` and `a² s² ≤ 1/100`. -/
theorem floor_core {a s : ℝ} {d p : ℕ} (ha : 0 < a) (hs : 0 < s)
    (hdk : (d : ℝ) * (a ^ 2 * s ^ 2) ≤ 101 / 100) (hk : a ^ 2 * s ^ 2 ≤ 1 / 100)
    (hdeg : ∀ v, G.degree v ≤ d) {yp ym : V → ℝ} (hyp : InCube s yp) (hym : InCube s ym)
    {S : Finset V} {v : V} (hv : v ∈ S) (hZ : 0 < ZwCore G p a yp ym S v)
    (hmean : ∀ i ∈ nbhd G S v,
      coreE G p a yp ym S v (fun σ => (precCore G a 1 yp σ S v)⁻¹ i i) ≤ 101 / 100 ∧
        coreE G p a yp ym S v (fun σ => (precCore G a (-1) ym σ S v)⁻¹ i i) ≤ 101 / 100) :
    ZwCore G p a yp ym S v ≤
      40 ^ p * ∑ σ : Config V, wtCore G p a yp ym σ S v * PhiRoot G p a yp ym σ S v := by
  have hyp0 : ∀ i, 0 ≤ yp i := fun i => (hyp i).1
  have hym0 : ∀ i, 0 ≤ ym i := fun i => (hym i).1
  have hW0 : ∀ σ, 0 ≤ wtCore G p a yp ym σ S v := fun σ => wtCore_nonneg G p a yp ym σ S v
  have hWflip : ∀ i, i ≠ v → ∀ σ,
      wtCore G p a yp ym (flipAt s(i, v) σ) S v = wtCore G p a yp ym σ S v :=
    fun i _ σ => wtCore_flipAt G p a yp ym S (Sym2.mem_mk_right i v) σ
  have hDp1 := one_le_diagD G a hyp0 S
  have hDm1 := one_le_diagD G a hym0 S
  have hDpv : 0 < diagD G a yp S v := by linarith [hDp1 v]
  have hDmv : 0 < diagD G a ym S v := by linarith [hDm1 v]
  -- the expected root energies
  have hEp : ∑ σ, wtCore G p a yp ym σ S v * qRoot G a 1 yp σ S v ≤
      101 / 100 * ZwCore G p a yp ym S v *
        (a ^ 2 * yp v * (∑ i ∈ nbhd G S v, yp i) / diagD G a yp S v) := by
    refine sum_wt_qRoot_le G _ hWflip (by norm_num) a hyp0 hv hDpv fun i hi => ?_
    have := (hmean i hi).1
    rw [coreE, div_le_iff₀ hZ] at this
    exact this
  have hEm : ∑ σ, wtCore G p a yp ym σ S v * qRoot G a (-1) ym σ S v ≤
      101 / 100 * ZwCore G p a yp ym S v *
        (a ^ 2 * ym v * (∑ i ∈ nbhd G S v, ym i) / diagD G a ym S v) := by
    refine sum_wt_qRoot_le G _ hWflip (by norm_num) a hym0 hv hDmv fun i hi => ?_
    have := (hmean i hi).2
    rw [coreE, div_le_iff₀ hZ] at this
    exact this
  -- the parallel sum
  have hH0 : 0 ≤ parSum G a yp ym S v := by
    refine Finset.sum_nonneg fun i _ => ?_
    have h1 := hDp1 i
    have h2 := hDm1 i
    exact mul_nonneg (mul_nonneg (hyp0 i) (hym0 i)) (inv_nonneg.2 (add_nonneg
      (mul_nonneg (by linarith) (hym0 i)) (mul_nonneg (by linarith) (hyp0 i))))
  have hH : (∑ i ∈ nbhd G S v, yp i + ∑ i ∈ nbhd G S v, ym i - (nbhd G S v).card * s) /
      (2 * (201 / 100)) ≤ parSum G a yp ym S v := by
    have := Finset.sum_le_sum fun i (_ : i ∈ nbhd G S v) =>
      term_lower (hyp i).1 (hyp i).2 (hym i).1 (hym i).2 (hDp1 i)
        (diagD_le G hdeg hdk hyp S i) (hDm1 i) (diagD_le G hdeg hdk hym S i)
    rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
      nsmul_eq_mul] at this
    exact this
  have hn : ((nbhd G S v).card : ℝ) ≤ d := by
    exact_mod_cast (card_nbhd_le G S v).trans (hdeg v)
  have hSp : ∑ i ∈ nbhd G S v, yp i ≤ (nbhd G S v).card * s := by
    have := Finset.sum_le_card_nsmul (nbhd G S v) yp s fun i _ => (hyp i).2
    rwa [nsmul_eq_mul] at this
  have hSm : ∑ i ∈ nbhd G S v, ym i ≤ (nbhd G S v).card * s := by
    have := Finset.sum_le_card_nsmul (nbhd G S v) ym s fun i _ => (hym i).2
    rwa [nsmul_eq_mul] at this
  obtain ⟨hDvp, hDvp'⟩ := diagD_root_bounds G hk hyp S v
  obtain ⟨hDvm, hDvm'⟩ := diagD_root_bounds G hk hym S v
  obtain ⟨htot, hcase⟩ := floor_numeric ha hs hn hdk (hyp v).1 (hyp v).2 (hym v).1 (hym v).2
    (Finset.sum_nonneg fun i _ => hyp0 i) hSp (Finset.sum_nonneg fun i _ => hym0 i) hSm
    hDvp hDvp' hDvm hDvm' hH hH0
  -- the floor `E α₊β₊ ≥ 1/40`
  have hmain : ZwCore G p a yp ym S v / 40 ≤ ∑ σ, wtCore G p a yp ym σ S v *
      (max (1 - qRoot G a 1 yp σ S v) 0 * max (1 - qRoot G a (-1) ym σ S v) 0) := by
    have hZdef : ZwCore G p a yp ym S v = ∑ σ, wtCore G p a yp ym σ S v := rfl
    rcases hcase with hA | hB
    · have hl := sum_lower (fun σ => wtCore G p a yp ym σ S v)
        (fun σ => max (1 - qRoot G a 1 yp σ S v) 0 * max (1 - qRoot G a (-1) ym σ S v) 0)
        (fun σ => qRoot G a 1 yp σ S v) (fun σ => qRoot G a (-1) ym σ S v) 1 hW0
        fun σ hσ => by
          obtain ⟨h1, h2⟩ := wtCore_support G hσ
          have := one_sub_le_max_mul_max (qRoot_nonneg G h1 hDpv) (qRoot_nonneg G h2 hDmv)
          linarith
      beta_reduce at hl
      rw [← hZdef] at hl
      have := mul_le_mul_of_nonneg_left hA hZ.le
      nlinarith
    · have hl := sum_lower (fun σ => wtCore G p a yp ym σ S v)
        (fun σ => max (1 - qRoot G a 1 yp σ S v) 0 * max (1 - qRoot G a (-1) ym σ S v) 0)
        (fun σ => qRoot G a 1 yp σ S v) (fun σ => qRoot G a (-1) ym σ S v) (19 / 20) hW0
        fun σ hσ => by
          obtain ⟨h1, h2⟩ := wtCore_support G hσ
          exact one_sub_le_max_mul_max' (qRoot_nonneg G h1 hDpv) (qRoot_nonneg G h2 hDmv) hB
            (qRoot_prod G a hyp0 hym0 hv hDpv hDmv h1 h2)
      beta_reduce at hl
      rw [← hZdef] at hl
      have := mul_le_mul_of_nonneg_left htot hZ.le
      nlinarith
  exact jensen_floor (fun σ => wtCore G p a yp ym σ S v)
    (fun σ => max (1 - qRoot G a 1 yp σ S v) 0 * max (1 - qRoot G a (-1) ym σ S v) 0) p hW0 hZ
    (fun σ => mul_nonneg (le_max_right _ _) (le_max_right _ _)) hmain

end Floor

end FloorIns

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable {d p : ℕ}

theorem floor_ins (hR : TRegime d p) (hdeg : ∀ v, G.degree v ≤ d) {yp ym : V → ℝ}
    (hyp : InCube (sOf d p) yp) (hym : InCube (sOf d p) ym) {S : Finset V} {v : V} (hv : v ∈ S)
    (hZ : 0 < ZwCore G p (aOf d p) yp ym S v)
    (hmean : ∀ i ∈ nbhd G S v,
      coreE G p (aOf d p) yp ym S v (fun σ => (precCore G (aOf d p) 1 yp σ S v)⁻¹ i i) ≤
          101 / 100 ∧
        coreE G p (aOf d p) yp ym S v (fun σ => (precCore G (aOf d p) (-1) ym σ S v)⁻¹ i i) ≤
          101 / 100) :
    ZwCore G p (aOf d p) yp ym S v ≤
      40 ^ p * ∑ σ : Config V,
        wtCore G p (aOf d p) yp ym σ S v * PhiRoot G p (aOf d p) yp ym σ S v :=
  FloorIns.floor_core G hR.aOf_pos hR.sOf_pos hR.d_mul_kappa_le hR.kappa_le hdeg hyp hym hv hZ
    hmean

end BiluLinial.Tight
