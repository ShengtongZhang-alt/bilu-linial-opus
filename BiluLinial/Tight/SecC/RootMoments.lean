/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecC.Root
public import BiluLinial.Tight.SourceMax
public import BiluLinial.Tight.Tools.Interp

/-!
# Root moments and interpolation at a capped point (helpers for B3, MARKENV, T.TRC)

Notes `docs/tight/BP_SECC.md`; AUDIT-C §1 (F2 consequences), §3 (T.IL), R8.

* `IsBranch yp ym τ y`: `(τ, y) = (1, y⁺)` or `(-1, y⁻)`, so that one statement covers both
  branches.
* `hN_moment_le` (F2 with base `2`): at a capped point `E (h_i^τ)^n ≤ 2^n` for `i ∈ S`, `2n ≤ p`
  (`source_moments`, `(pr - n)/(p - n) ≤ 2` since `r ≤ 1.01`).
* `rootT_moment_le`: `E t^n ≤ 5^n`, `t = D_v h_v` (`D_v ≤ 2.01`, `FloorIns.diagD_le`).
* `hN_sum_moment_le`, `hN_mul_sum_moment_le`: `E (Σ_T h_j)^n ≤ |T|^n 2^n` and
  `E (h_v Σ_T h_j)^n ≤ 2 |T|^n 4^n` (power mean, `xy ≤ x² + y²`).
* `lawE_mul_le_interp` (T.IL in the paired law; nonnegativity only on the support) and
  `lawE_mul_le_vth` (the floor `ϑ = d^{-10}`, `k = kIL d = ⌈30 log d⌉`, `‖X‖₂ ≤ d^{30}`):
  `E[XY] ≤ e² B_Y m` whenever `E X ≤ m`, `ϑ ≤ m`, `‖Y‖_{2k} ≤ B_Y`. `eventually_kIL`:
  `8 kIL d ≤ p` (so moments of order `≤ 4 kIL d` are available).
-/

@[expose] public section

namespace BiluLinial.Tight

namespace SecC

open Matrix

/-! ### Branches -/

/-- The two branches: `(τ, y) = (1, y⁺)` or `(-1, y⁻)`. -/
def IsBranch {V : Type*} (yp ym : V → ℝ) (τ : ℝ) (y : V → ℝ) : Prop :=
  (τ = 1 ∧ y = yp) ∨ (τ = -1 ∧ y = ym)

theorem isBranch_plus {V : Type*} (yp ym : V → ℝ) : IsBranch yp ym 1 yp := Or.inl ⟨rfl, rfl⟩

theorem isBranch_minus {V : Type*} (yp ym : V → ℝ) : IsBranch yp ym (-1) ym :=
  Or.inr ⟨rfl, rfl⟩

theorem IsBranch.inCube {V : Type*} {yp ym : V → ℝ} {τ : ℝ} {y : V → ℝ}
    (hb : IsBranch yp ym τ y) {t : ℝ} (hyp : InCube t yp) (hym : InCube t ym) : InCube t y := by
  rcases hb with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] <;> assumption

theorem IsBranch.tau {V : Type*} {yp ym : V → ℝ} {τ : ℝ} {y : V → ℝ}
    (hb : IsBranch yp ym τ y) : τ = 1 ∨ τ = -1 := by
  rcases hb with ⟨h, -⟩ | ⟨h, -⟩
  · exact Or.inl h
  · exact Or.inr h

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- On the support both precisions of the branch (full and inherited core) are positive
definite. -/
theorem posDef_branch {p : ℕ} (hp : 1 ≤ p) {a : ℝ} {yp ym : V → ℝ} (hyp : ∀ i, 0 ≤ yp i)
    (hym : ∀ i, 0 ≤ ym i) {S : Finset V} {v : V} (hv : v ∈ S) {τ : ℝ} {y : V → ℝ}
    (hb : IsBranch yp ym τ y) {σ : Config V} (hσ : wt G p a yp ym σ S ≠ 0) :
    (precN G a τ y σ S).PosDef ∧ (precCore G a τ y σ S v).PosDef := by
  have hPp : (precN G a 1 yp σ S).PosDef := by
    by_contra hc
    exact hσ (by simp [wt, hc])
  have hPm : (precN G a (-1) ym σ S).PosDef := by
    by_contra hc
    exact hσ (by simp [wt, hc])
  obtain ⟨hc1, hc2⟩ := posDef_of_wtCore_ne_zero G (wtCore_ne_zero_of_wt G hp hyp hym hv hσ)
  rcases hb with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 h2
  · exact ⟨hPp, hc1⟩
  · exact ⟨hPm, hc2⟩

theorem hN_pos_branch {p : ℕ} {a : ℝ} {yp ym : V → ℝ} {S : Finset V} {τ : ℝ} {y : V → ℝ}
    (hb : IsBranch yp ym τ y) {σ : Config V} (h : wt G p a yp ym σ S ≠ 0) (i : V) :
    0 < hN G a τ y σ S i := by
  rcases hb with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 h2
  · exact hN_pos G h i
  · exact hN_pos_minus G h i

theorem lawE_const_one {p : ℕ} {a : ℝ} {yp ym : V → ℝ} {S : Finset V}
    (hZ : 0 < Zw G p a yp ym S) : lawE G p a yp ym S (fun _ => 1) = 1 := by
  unfold lawE
  simp only [mul_one]
  exact div_self hZ.ne'

/-- `(a + b)^n ≤ 2^n (a^n + b^n)` for `a, b ≥ 0`. -/
theorem add_pow_le_two_pow_mul {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (n : ℕ) :
    (a + b) ^ n ≤ 2 ^ n * (a ^ n + b ^ n) := by
  have hm : a + b ≤ 2 * max a b := by
    have := le_max_left a b
    have := le_max_right a b
    linarith
  have hmn : max a b ^ n ≤ a ^ n + b ^ n := by
    rcases le_total a b with h | h
    · rw [max_eq_right h]; linarith [pow_nonneg ha n]
    · rw [max_eq_left h]; linarith [pow_nonneg hb n]
  calc (a + b) ^ n ≤ (2 * max a b) ^ n := pow_le_pow_left₀ (add_nonneg ha hb) hm n
    _ = 2 ^ n * max a b ^ n := mul_pow _ _ _
    _ ≤ 2 ^ n * (a ^ n + b ^ n) := mul_le_mul_of_nonneg_left hmn (by positivity)

/-! ### Moments at a capped point -/

variable {d p : ℕ}

theorem Zw_pos_cap (hR : TRegime d p) {S : Finset V} {lam : ℝ} (hC : CapCtx G d p S lam)
    {yp ym : V → ℝ} (hyp : InCube (lam * sOf d p) yp) (hym : InCube (lam * sOf d p) ym) :
    0 < Zw G p (aOf d p) yp ym S :=
  hC.pos yp ym (inCube_of_cap G hR hC hyp) (inCube_of_cap G hR hC hym)

/-- **F2 with base 2**: `E (h_i^τ)^n ≤ 2^n` for `i ∈ S`, `2n ≤ p`. -/
theorem hN_moment_le (hR : TRegime d p) {S : Finset V} {lam : ℝ} (hC : CapCtx G d p S lam)
    {yp ym : V → ℝ} (hyp : InCube (lam * sOf d p) yp) (hym : InCube (lam * sOf d p) ym)
    {τ : ℝ} {y : V → ℝ} (hb : IsBranch yp ym τ y) {i : V} (hi : i ∈ S) {n : ℕ}
    (hn : 2 * n ≤ p) :
    lawE G p (aOf d p) yp ym S (fun σ => hN G (aOf d p) τ y σ S i ^ n) ≤ 2 ^ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn1
  · simp only [pow_zero]
    exact (lawE_const_one G (Zw_pos_cap G hR hC hyp hym)).le
  have hn1' : 1 ≤ n := hn1
  have hn2 : n + 2 ≤ p := by have := hR.hp; omega
  have hkp : (2 : ℝ) * n ≤ p := by exact_mod_cast hn
  have hk0 : (1 : ℝ) ≤ n := by exact_mod_cast hn1'
  have hr := hR.rOf_le
  have hr1 := hR.one_lt_rOf
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hpk : 0 < (p : ℝ) - n := by linarith
  have hpr1 := mul_le_mul_of_nonneg_left hr1.le hp0
  have hpr2 := mul_le_mul_of_nonneg_left hr hp0
  have hb0 : 0 ≤ ((p : ℝ) * rOf d p - n) / ((p : ℝ) - n) :=
    div_nonneg (by linarith) hpk.le
  have hb2 : ((p : ℝ) * rOf d p - n) / ((p : ℝ) - n) ≤ 2 := by
    rw [div_le_iff₀ hpk]
    linarith
  obtain ⟨h1, h2⟩ := source_moments G hR hC hyp hym hi hn1' hn2
  rcases hb with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> subst e1 e2
  · exact h1.trans (pow_le_pow_left₀ hb0 hb2 n)
  · exact h2.trans (pow_le_pow_left₀ hb0 hb2 n)

/-- `E t^n ≤ 5^n` for `t = D_v h_v` (`D_v ≤ 2.01`), `2n ≤ p`. -/
theorem rootT_moment_le (hR : TRegime d p) {S : Finset V} {lam : ℝ} (hC : CapCtx G d p S lam)
    {yp ym : V → ℝ} (hyp : InCube (lam * sOf d p) yp) (hym : InCube (lam * sOf d p) ym)
    {τ : ℝ} {y : V → ℝ} (hb : IsBranch yp ym τ y) {v : V} (hv : v ∈ S) {n : ℕ}
    (hn : 2 * n ≤ p) :
    lawE G p (aOf d p) yp ym S (fun σ => rootT G (aOf d p) τ y σ S v ^ n) ≤ 5 ^ n := by
  have hy := inCube_of_cap G hR hC (hb.inCube hyp hym)
  have hD0 : 0 < diagD G (aOf d p) y S v := diagD_pos G _ (fun i => (hy i).1) S v
  have hD := FloorIns.diagD_le G hC.deg hR.d_mul_kappa_le hy S v
  calc lawE G p (aOf d p) yp ym S (fun σ => rootT G (aOf d p) τ y σ S v ^ n)
      ≤ lawE G p (aOf d p) yp ym S
          (fun σ => (201 / 100 : ℝ) ^ n * hN G (aOf d p) τ y σ S v ^ n) :=
        lawE_mono G fun σ hσ => by
          rw [rootT, mul_pow]
          exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hD0.le hD n)
            (pow_nonneg (hN_pos_branch G hb hσ v).le n)
    _ = (201 / 100 : ℝ) ^ n *
          lawE G p (aOf d p) yp ym S (fun σ => hN G (aOf d p) τ y σ S v ^ n) :=
        lawE_const_mul G _ _
    _ ≤ (201 / 100 : ℝ) ^ n * 2 ^ n :=
        mul_le_mul_of_nonneg_left (hN_moment_le G hR hC hyp hym hb hv hn) (by positivity)
    _ ≤ 5 ^ n := by
        rw [← mul_pow]
        exact pow_le_pow_left₀ (by norm_num) (by norm_num) n

/-- `E (Σ_{j ∈ T} h_j)^n ≤ |T|^n 2^n` for `T ⊆ S`, `2n ≤ p`. -/
theorem hN_sum_moment_le (hR : TRegime d p) {S : Finset V} {lam : ℝ} (hC : CapCtx G d p S lam)
    {yp ym : V → ℝ} (hyp : InCube (lam * sOf d p) yp) (hym : InCube (lam * sOf d p) ym)
    {τ : ℝ} {y : V → ℝ} (hb : IsBranch yp ym τ y) {T : Finset V} (hT : T ⊆ S) {n : ℕ}
    (hn : 2 * n ≤ p) :
    lawE G p (aOf d p) yp ym S (fun σ => (∑ j ∈ T, hN G (aOf d p) τ y σ S j) ^ n) ≤
      (T.card : ℝ) ^ n * 2 ^ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn1
  · simp only [pow_zero, one_mul]
    exact (lawE_const_one G (Zw_pos_cap G hR hC hyp hym)).le
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  calc lawE G p (aOf d p) yp ym S (fun σ => (∑ j ∈ T, hN G (aOf d p) τ y σ S j) ^ (m + 1))
      ≤ lawE G p (aOf d p) yp ym S
          (fun σ => (T.card : ℝ) ^ m * ∑ j ∈ T, hN G (aOf d p) τ y σ S j ^ (m + 1)) :=
        lawE_mono G fun σ hσ =>
          pow_sum_le_card_mul_sum_pow (fun j _ => (hN_pos_branch G hb hσ j).le) m
    _ = (T.card : ℝ) ^ m *
          ∑ j ∈ T, lawE G p (aOf d p) yp ym S (fun σ => hN G (aOf d p) τ y σ S j ^ (m + 1)) := by
        rw [lawE_const_mul, lawE_sum]
    _ ≤ (T.card : ℝ) ^ m * ∑ _j ∈ T, (2 : ℝ) ^ (m + 1) := by
        gcongr with j hj
        exact hN_moment_le G hR hC hyp hym hb (hT hj) hn
    _ = (T.card : ℝ) ^ (m + 1) * 2 ^ (m + 1) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring

/-- `E (h_v Σ_{j ∈ T} h_j)^n ≤ 2 |T|^n 4^n` for `v ∈ S`, `T ⊆ S`, `4n ≤ p`. -/
theorem hN_mul_sum_moment_le (hR : TRegime d p) {S : Finset V} {lam : ℝ}
    (hC : CapCtx G d p S lam) {yp ym : V → ℝ} (hyp : InCube (lam * sOf d p) yp)
    (hym : InCube (lam * sOf d p) ym) {τ : ℝ} {y : V → ℝ} (hb : IsBranch yp ym τ y) {v : V}
    (hv : v ∈ S) {T : Finset V} (hT : T ⊆ S) {n : ℕ} (hn : 4 * n ≤ p) :
    lawE G p (aOf d p) yp ym S (fun σ =>
        (hN G (aOf d p) τ y σ S v * ∑ j ∈ T, hN G (aOf d p) τ y σ S j) ^ n) ≤
      2 * (T.card : ℝ) ^ n * 4 ^ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn1
  · simp only [pow_zero, mul_one]
    rw [lawE_const_one G (Zw_pos_cap G hR hC hyp hym)]
    norm_num
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hn2 : 2 * (2 * (m + 1)) ≤ p := by omega
  set c : ℝ := (T.card : ℝ) ^ m with hc
  have hc0 : 0 ≤ c := by positivity
  have hpt : ∀ σ, wt G p (aOf d p) yp ym σ S ≠ 0 →
      (hN G (aOf d p) τ y σ S v * ∑ j ∈ T, hN G (aOf d p) τ y σ S j) ^ (m + 1) ≤
        c * ∑ j ∈ T, (hN G (aOf d p) τ y σ S v ^ (2 * (m + 1)) +
          hN G (aOf d p) τ y σ S j ^ (2 * (m + 1))) := by
    intro σ hσ
    have h0 : ∀ j, 0 ≤ hN G (aOf d p) τ y σ S j := fun j => (hN_pos_branch G hb hσ j).le
    rw [mul_pow]
    calc hN G (aOf d p) τ y σ S v ^ (m + 1) * (∑ j ∈ T, hN G (aOf d p) τ y σ S j) ^ (m + 1)
        ≤ hN G (aOf d p) τ y σ S v ^ (m + 1) *
            (c * ∑ j ∈ T, hN G (aOf d p) τ y σ S j ^ (m + 1)) :=
          mul_le_mul_of_nonneg_left (pow_sum_le_card_mul_sum_pow (fun j _ => h0 j) m)
            (pow_nonneg (h0 v) _)
      _ = c * ∑ j ∈ T, hN G (aOf d p) τ y σ S v ^ (m + 1) *
            hN G (aOf d p) τ y σ S j ^ (m + 1) := by
          rw [mul_left_comm, Finset.mul_sum]
      _ ≤ c * ∑ j ∈ T, (hN G (aOf d p) τ y σ S v ^ (2 * (m + 1)) +
            hN G (aOf d p) τ y σ S j ^ (2 * (m + 1))) := by
          gcongr with j hj
          have ex : hN G (aOf d p) τ y σ S v ^ (2 * (m + 1)) =
              (hN G (aOf d p) τ y σ S v ^ (m + 1)) ^ 2 := by rw [← pow_mul, mul_comm]
          have ey : hN G (aOf d p) τ y σ S j ^ (2 * (m + 1)) =
              (hN G (aOf d p) τ y σ S j ^ (m + 1)) ^ 2 := by rw [← pow_mul, mul_comm]
          rw [ex, ey]
          have hx := pow_nonneg (h0 v) (m + 1)
          have hy := pow_nonneg (h0 j) (m + 1)
          nlinarith [sq_nonneg (hN G (aOf d p) τ y σ S v ^ (m + 1) -
            hN G (aOf d p) τ y σ S j ^ (m + 1))]
  calc lawE G p (aOf d p) yp ym S (fun σ =>
        (hN G (aOf d p) τ y σ S v * ∑ j ∈ T, hN G (aOf d p) τ y σ S j) ^ (m + 1))
      ≤ lawE G p (aOf d p) yp ym S (fun σ => c * ∑ j ∈ T,
          (hN G (aOf d p) τ y σ S v ^ (2 * (m + 1)) +
            hN G (aOf d p) τ y σ S j ^ (2 * (m + 1)))) := lawE_mono G hpt
    _ = c * ∑ j ∈ T,
          (lawE G p (aOf d p) yp ym S (fun σ => hN G (aOf d p) τ y σ S v ^ (2 * (m + 1))) +
            lawE G p (aOf d p) yp ym S (fun σ => hN G (aOf d p) τ y σ S j ^ (2 * (m + 1)))) := by
        rw [lawE_const_mul, lawE_sum]
        refine congrArg _ (Finset.sum_congr rfl fun j _ => ?_)
        exact lawE_add G _ _
    _ ≤ c * ∑ _j ∈ T, ((2 : ℝ) ^ (2 * (m + 1)) + 2 ^ (2 * (m + 1))) := by
        gcongr with j hj
        · exact hN_moment_le G hR hC hyp hym hb hv hn2
        · exact hN_moment_le G hR hC hyp hym hb (hT hj) hn2
    _ = 2 * (T.card : ℝ) ^ (m + 1) * 4 ^ (m + 1) := by
        have e4 : (2 : ℝ) ^ (2 * (m + 1)) = 4 ^ (m + 1) := by rw [pow_mul]; norm_num
        rw [Finset.sum_const, nsmul_eq_mul, hc, e4]
        ring

/-! ### Interpolation with the floor `ϑ` -/

/-- **T.IL in the paired law** (`wavg_mul_le_interp`), with nonnegativity only on the support. -/
theorem lawE_mul_le_interp {p : ℕ} {a : ℝ} {yp ym : V → ℝ} {S : Finset V}
    (hZ : 0 < Zw G p a yp ym S) {X Y : Config V → ℝ}
    (hX : ∀ σ, wt G p a yp ym σ S ≠ 0 → 0 ≤ X σ) (hY : ∀ σ, wt G p a yp ym σ S ≠ 0 → 0 ≤ Y σ)
    {k : ℕ} (hk : 1 ≤ k) {m θ BX BY : ℝ} (hθ : 0 < θ) (hθm : θ ≤ m) (hBX : 0 ≤ BX)
    (hBY : 0 ≤ BY) (hXm : lawE G p a yp ym S X ≤ m)
    (hX2 : lawE G p a yp ym S (fun σ => X σ ^ 2) ≤ BX ^ 2)
    (hY2k : lawE G p a yp ym S (fun σ => Y σ ^ (2 * k)) ≤ BY ^ (2 * k)) :
    lawE G p a yp ym S (fun σ => X σ * Y σ) ≤
      m * θ ^ (-(1 / (k : ℝ))) * BX ^ (1 / (k : ℝ)) * BY := by
  have eX : ∀ σ, wt G p a yp ym σ S ≠ 0 → max (X σ) 0 = X σ := fun σ h => max_eq_left (hX σ h)
  have eY : ∀ σ, wt G p a yp ym σ S ≠ 0 → max (Y σ) 0 = Y σ := fun σ h => max_eq_left (hY σ h)
  have h1 : lawE G p a yp ym S (fun σ => X σ * Y σ) =
      lawE G p a yp ym S (fun σ => max (X σ) 0 * max (Y σ) 0) :=
    lawE_congr G fun σ h => by rw [eX σ h, eY σ h]
  have h2 : lawE G p a yp ym S X = lawE G p a yp ym S (fun σ => max (X σ) 0) :=
    lawE_congr G fun σ h => (eX σ h).symm
  have h3 : lawE G p a yp ym S (fun σ => X σ ^ 2) =
      lawE G p a yp ym S (fun σ => max (X σ) 0 ^ 2) :=
    lawE_congr G fun σ h => by rw [eX σ h]
  have h4 : lawE G p a yp ym S (fun σ => Y σ ^ (2 * k)) =
      lawE G p a yp ym S (fun σ => max (Y σ) 0 ^ (2 * k)) :=
    lawE_congr G fun σ h => by rw [eY σ h]
  rw [h1]
  rw [h2] at hXm
  rw [h3] at hX2
  rw [h4] at hY2k
  simp only [lawE_eq_wavg] at hXm hX2 hY2k ⊢
  exact wavg_mul_le_interp (fun σ => wt_nonneg G σ) hZ (fun σ => le_max_right _ _)
    (fun σ => le_max_right _ _) hk hθ hθm hBX hBY hXm hX2 hY2k

/-- The interpolation exponent `k = ⌈30 log d⌉`. -/
noncomputable def kIL (d : ℕ) : ℕ := ⌈30 * Real.log d⌉₊

theorem kIL_ge (d : ℕ) : 30 * Real.log d ≤ (kIL d : ℝ) := Nat.le_ceil _

theorem one_le_kIL (hd : 3 ≤ d) : 1 ≤ kIL d := by
  have hd1 : (1 : ℝ) < d := by exact_mod_cast (by omega : 1 < d)
  have hlog : 0 < Real.log d := Real.log_pos hd1
  have h : (0 : ℝ) < kIL d := lt_of_lt_of_le (by linarith) (kIL_ge d)
  have h' : 0 < kIL d := by exact_mod_cast h
  omega

/-- `B^{1/k} ≤ e` when `0 ≤ B ≤ d^{30}` and `k ≥ 30 log d`. -/
theorem rpow_one_div_le_exp_one {d : ℕ} (hd : 1 ≤ d) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : B ≤ (d : ℝ) ^ 30) {k : ℝ} (hk : 0 < k) (hkd : 30 * Real.log d ≤ k) :
    B ^ (1 / k) ≤ Real.exp 1 := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  calc B ^ (1 / k) ≤ ((d : ℝ) ^ 30) ^ (1 / k) :=
        Real.rpow_le_rpow hB0 hB (one_div_nonneg.mpr hk.le)
    _ = Real.exp (30 * Real.log d / k) := by
        rw [Real.rpow_def_of_pos (pow_pos hd0 30), Real.log_pow]
        congr 1
        push_cast
        ring
    _ ≤ Real.exp 1 := Real.exp_le_exp.mpr (by rw [div_le_one hk]; exact hkd)

/-- **T.IL with the floor `ϑ = d^{-10}`** and `k = kIL d`: if `X, Y ≥ 0` on the support,
`E X ≤ m`, `ϑ ≤ m`, `E X² ≤ B_X²` with `B_X ≤ d^{30}`, and `E Y^{2k} ≤ B_Y^{2k}`, then
`E[XY] ≤ e² B_Y m`. -/
theorem lawE_mul_le_vth (hd : 3 ≤ d) {p : ℕ} {a : ℝ} {yp ym : V → ℝ} {S : Finset V}
    (hZ : 0 < Zw G p a yp ym S) {X Y : Config V → ℝ}
    (hX : ∀ σ, wt G p a yp ym σ S ≠ 0 → 0 ≤ X σ) (hY : ∀ σ, wt G p a yp ym σ S ≠ 0 → 0 ≤ Y σ)
    {m BX BY : ℝ} (hθm : vth d ≤ m) (hBX : 0 ≤ BX) (hBXd : BX ≤ (d : ℝ) ^ 30) (hBY : 0 ≤ BY)
    (hXm : lawE G p a yp ym S X ≤ m)
    (hX2 : lawE G p a yp ym S (fun σ => X σ ^ 2) ≤ BX ^ 2)
    (hY2k : lawE G p a yp ym S (fun σ => Y σ ^ (2 * kIL d)) ≤ BY ^ (2 * kIL d)) :
    lawE G p a yp ym S (fun σ => X σ * Y σ) ≤ Real.exp 2 * BY * m := by
  have hd1 : 1 ≤ d := by omega
  have hdr : (1 : ℝ) < d := by exact_mod_cast (by omega : 1 < d)
  have hlog : 0 < Real.log d := Real.log_pos hdr
  have hk30 := kIL_ge d
  have hkpos : (0 : ℝ) < kIL d := lt_of_lt_of_le (by linarith) hk30
  have hθ : 0 < vth d := by unfold vth; positivity
  have hm0 : 0 < m := hθ.trans_le hθm
  have h := lawE_mul_le_interp G hZ hX hY (one_le_kIL hd) hθ hθm hBX hBY hXm hX2 hY2k
  have e1 : vth d ^ (-(1 / (kIL d : ℝ))) ≤ Real.exp 1 :=
    vth_rpow_neg_le hd1 hkpos (by linarith)
  have e2 : BX ^ (1 / (kIL d : ℝ)) ≤ Real.exp 1 :=
    rpow_one_div_le_exp_one hd1 hBX hBXd hkpos hk30
  have hA0 : 0 ≤ vth d ^ (-(1 / (kIL d : ℝ))) := Real.rpow_nonneg hθ.le _
  have hB0 : 0 ≤ BX ^ (1 / (kIL d : ℝ)) := Real.rpow_nonneg hBX _
  have h3 : m * vth d ^ (-(1 / (kIL d : ℝ))) * BX ^ (1 / (kIL d : ℝ)) ≤
      m * Real.exp 1 * Real.exp 1 :=
    mul_le_mul (mul_le_mul_of_nonneg_left e1 hm0.le) e2 hB0
      (mul_nonneg hm0.le (Real.exp_pos 1).le)
  calc lawE G p a yp ym S (fun σ => X σ * Y σ)
      ≤ m * vth d ^ (-(1 / (kIL d : ℝ))) * BX ^ (1 / (kIL d : ℝ)) * BY := h
    _ ≤ m * Real.exp 1 * Real.exp 1 * BY := mul_le_mul_of_nonneg_right h3 hBY
    _ = Real.exp 2 * BY * m := by
        rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
        ring

/-- `8 kIL d ≤ p` for large `d` (`p ≥ 250 log d`, `log d ≥ 8`). -/
theorem eventually_kIL : Eventually fun _ _ d p _ => 8 * kIL d ≤ p := by
  refine ((eventually_log_le 250).and (eventually_le_log 8)).mono ?_
  rintro c₀ κ₀ d p h ⟨h1, h2⟩
  have hk : (kIL d : ℝ) < 30 * Real.log d + 1 := Nat.ceil_lt_add_one (by linarith)
  have : ((8 * kIL d : ℕ) : ℝ) ≤ p := by
    push_cast
    linarith
  exact_mod_cast this

end SecC

end BiluLinial.Tight
