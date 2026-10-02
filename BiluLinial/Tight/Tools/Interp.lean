/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.Defs

/-!
# Interpolation lemmas for finite weighted averages (T.IL, T.DSTAR, UMI)

Nodes T.IL, T.DSTAR (AUDIT-C §3) and UMI (AUDIT-D §2.6) of `docs/tight/BP_TOOLS.md`. The law
is a finite weighted average `wavg w f = Σ w f / Σ w` over a finite type `Ω` with weights
`w ≥ 0`, `Σ w > 0`; the paired law is the case `w = wt` (`lawE_eq_wavg`). Norms are written
through moments: `‖X‖_k ≤ B` is `wavg w (X^k) ≤ B^k`.

* `wavg_mul_le_holder` (Hölder, the core of T.IL): for `X, Y ≥ 0`, `k ≥ 1`,
  `E[XY] ≤ (E X)^{1-1/k} (E[X Y^k])^{1/k}` (weighted Hölder with weights `w X`).
* `wavg_mul_le_interp` (**T.IL**): `E X ≤ m`, `θ ≤ m`, `θ > 0`, `‖X‖₂ ≤ B_X`, `‖Y‖_{2k} ≤ B_Y`
  give `E[XY] ≤ m θ^{-1/k} B_X^{1/k} B_Y` (Cauchy–Schwarz `E[XY^k] ≤ ‖X‖₂ ‖Y‖_{2k}^k`, and
  `m^{1-1/k} ≤ m θ^{-1/k}`).
* `wavg_sup_pow_le` (**T.DSTAR**): `E[(max_{u∈S} X_u)^m] ≤ |S| max_u E[X_u^m]`
  (`(max X)^m ≤ Σ X_u^m`), and its root form.
* `wavg_mul_le_umi` (**UMI**): `‖Y‖_k ≤ M`, `‖Z‖_k ≤ B`, `k ≥ 2`, `θ > 0` give
  `E[YZ] ≤ B (M/θ)^{1/(k-1)} (E Y + θ)`. Proof: `E[YZ] ≤ (EY)^{1-λ} (E[Y Z^{k-1}])^λ` with
  `λ = 1/(k-1)` (Hölder as above), `E[Y Z^{k-1}] ≤ ‖Y‖_k ‖Z‖_k^{k-1}` (Hölder `(k, k/(k-1))`),
  then `s^{1-λ} M^λ ≤ (M/θ)^λ (s + θ)` by cases `s ≥ θ`, `s < θ`.
-/

@[expose] public section

namespace BiluLinial.Tight

open Finset

variable {Ω : Type*} [Fintype Ω]

/-- The weighted average `Σ w f / Σ w`. -/
noncomputable def wavg (w f : Ω → ℝ) : ℝ := (∑ ω, w ω * f ω) / ∑ ω, w ω

/-- The paired law is a weighted average. -/
theorem lawE_eq_wavg {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (p : ℕ) (a : ℝ) (yp ym : V → ℝ) (S : Finset V) (f : Config V → ℝ) :
    lawE G p a yp ym S f = wavg (fun σ => wt G p a yp ym σ S) f := rfl

section Basic

variable {w : Ω → ℝ}

theorem wavg_mono (hw : ∀ ω, 0 ≤ w ω) (hW : 0 < ∑ ω, w ω) {f g : Ω → ℝ}
    (hfg : ∀ ω, f ω ≤ g ω) : wavg w f ≤ wavg w g :=
  div_le_div_of_nonneg_right
    (Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hfg ω) (hw ω)) hW.le

theorem wavg_nonneg (hw : ∀ ω, 0 ≤ w ω) {f : Ω → ℝ} (hf : ∀ ω, 0 ≤ f ω) : 0 ≤ wavg w f :=
  div_nonneg (Finset.sum_nonneg fun ω _ => mul_nonneg (hw ω) (hf ω))
    (Finset.sum_nonneg fun ω _ => hw ω)

theorem wavg_const (hW : 0 < ∑ ω, w ω) (c : ℝ) : wavg w (fun _ => c) = c := by
  rw [wavg, ← Finset.sum_mul]
  field_simp

theorem wavg_sum {κ : Type*} (S : Finset κ) (f : κ → Ω → ℝ) :
    wavg w (fun ω => ∑ u ∈ S, f u ω) = ∑ u ∈ S, wavg w (f u) := by
  simp only [wavg, ← Finset.sum_div, Finset.mul_sum]
  rw [Finset.sum_comm]

end Basic

variable {w : Ω → ℝ}

/-- Hölder, the core of **T.IL**: `E[XY] ≤ (E X)^{1-1/k} (E[X Y^k])^{1/k}` for `X, Y ≥ 0`. -/
theorem wavg_mul_le_holder (hw : ∀ ω, 0 ≤ w ω) (hW : 0 < ∑ ω, w ω) {X Y : Ω → ℝ}
    (hX : ∀ ω, 0 ≤ X ω) (hY : ∀ ω, 0 ≤ Y ω) {k : ℕ} (hk : 1 ≤ k) :
    wavg w (fun ω => X ω * Y ω) ≤
      wavg w X ^ (1 - 1 / (k : ℝ)) * wavg w (fun ω => X ω * Y ω ^ k) ^ (1 / (k : ℝ)) := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hS1 : 0 ≤ ∑ ω, w ω * X ω := Finset.sum_nonneg fun ω _ => mul_nonneg (hw ω) (hX ω)
  have hS2 : 0 ≤ ∑ ω, w ω * (X ω * Y ω ^ k) := Finset.sum_nonneg fun ω _ =>
    mul_nonneg (hw ω) (mul_nonneg (hX ω) (pow_nonneg (hY ω) k))
  have h := Real.inner_le_weight_mul_Lp_of_nonneg Finset.univ hk' (fun ω => w ω * X ω) Y
    (fun ω => mul_nonneg (hw ω) (hX ω)) hY
  simp only [Real.rpow_natCast] at h
  unfold wavg
  rw [Real.div_rpow hS1 hW.le, Real.div_rpow hS2 hW.le, div_mul_div_comm,
    ← Real.rpow_add' hW.le (by rw [sub_add_cancel]; exact one_ne_zero), sub_add_cancel,
    Real.rpow_one]
  refine div_le_div_of_nonneg_right ?_ hW.le
  convert h using 2 <;> simp [one_div, mul_assoc]

/-- Weighted Cauchy–Schwarz: `E[XY]² ≤ E[X²] E[Y²]`. -/
theorem wavg_mul_sq_le (hw : ∀ ω, 0 ≤ w ω) (X Y : Ω → ℝ) :
    wavg w (fun ω => X ω * Y ω) ^ 2 ≤
      wavg w (fun ω => X ω ^ 2) * wavg w (fun ω => Y ω ^ 2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun ω => √(w ω) * X ω)
    (fun ω => √(w ω) * Y ω)
  have e1 : ∀ ω, √(w ω) * X ω * (√(w ω) * Y ω) = w ω * (X ω * Y ω) := fun ω => by
    rw [mul_mul_mul_comm, Real.mul_self_sqrt (hw ω)]
  have e2 : ∀ (ω : Ω) (Z : Ω → ℝ), (√(w ω) * Z ω) ^ 2 = w ω * Z ω ^ 2 := fun ω Z => by
    rw [mul_pow, Real.sq_sqrt (hw ω)]
  simp only [e1, e2] at h
  unfold wavg
  rw [div_pow, div_mul_div_comm, ← sq]
  exact div_le_div_of_nonneg_right h (sq_nonneg _)

/-- **T.IL.** `X, Y ≥ 0`, `k ≥ 1`, `0 < θ ≤ m`, `E X ≤ m`, `E X² ≤ B_X²`, `E Y^{2k} ≤ B_Y^{2k}`
give `E[XY] ≤ m θ^{-1/k} B_X^{1/k} B_Y`. -/
theorem wavg_mul_le_interp (hw : ∀ ω, 0 ≤ w ω) (hW : 0 < ∑ ω, w ω) {X Y : Ω → ℝ}
    (hX : ∀ ω, 0 ≤ X ω) (hY : ∀ ω, 0 ≤ Y ω) {k : ℕ} (hk : 1 ≤ k) {m θ BX BY : ℝ}
    (hθ : 0 < θ) (hθm : θ ≤ m) (hBX : 0 ≤ BX) (hBY : 0 ≤ BY) (hXm : wavg w X ≤ m)
    (hX2 : wavg w (fun ω => X ω ^ 2) ≤ BX ^ 2)
    (hY2k : wavg w (fun ω => Y ω ^ (2 * k)) ≤ BY ^ (2 * k)) :
    wavg w (fun ω => X ω * Y ω) ≤ m * θ ^ (-(1 / (k : ℝ))) * BX ^ (1 / (k : ℝ)) * BY := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h1k : 0 ≤ 1 - 1 / (k : ℝ) := by
    rw [sub_nonneg, div_le_one hkpos]; exact hk1
  have hm0 : 0 < m := hθ.trans_le hθm
  have hEX0 : 0 ≤ wavg w X := wavg_nonneg hw hX
  have hXYk0 : 0 ≤ wavg w (fun ω => X ω * Y ω ^ k) :=
    wavg_nonneg hw fun ω => mul_nonneg (hX ω) (pow_nonneg (hY ω) k)
  have hY2k' : wavg w (fun ω => (Y ω ^ k) ^ 2) ≤ (BY ^ k) ^ 2 := by
    simpa only [← pow_mul, mul_comm k 2] using hY2k
  have hXYk : wavg w (fun ω => X ω * Y ω ^ k) ≤ BX * BY ^ k := by
    have h1 : wavg w (fun ω => X ω * Y ω ^ k) ^ 2 ≤ (BX * BY ^ k) ^ 2 :=
      calc _ ≤ _ := wavg_mul_sq_le hw X (fun ω => Y ω ^ k)
        _ ≤ BX ^ 2 * (BY ^ k) ^ 2 :=
            mul_le_mul hX2 hY2k' (wavg_nonneg hw fun ω => sq_nonneg _) (sq_nonneg _)
        _ = (BX * BY ^ k) ^ 2 := by ring
    exact (sq_le_sq₀ hXYk0 (by positivity)).1 h1
  calc wavg w (fun ω => X ω * Y ω)
      ≤ wavg w X ^ (1 - 1 / (k : ℝ)) * wavg w (fun ω => X ω * Y ω ^ k) ^ (1 / (k : ℝ)) :=
        wavg_mul_le_holder hw hW hX hY hk
    _ ≤ m ^ (1 - 1 / (k : ℝ)) * (BX * BY ^ k) ^ (1 / (k : ℝ)) :=
        mul_le_mul (Real.rpow_le_rpow hEX0 hXm h1k)
          (Real.rpow_le_rpow hXYk0 hXYk (by positivity)) (by positivity) (by positivity)
    _ = m ^ (1 - 1 / (k : ℝ)) * (BX ^ (1 / (k : ℝ)) * BY) := by
        rw [Real.mul_rpow hBX (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hBY,
          mul_one_div_cancel hkpos.ne', Real.rpow_one]
    _ ≤ m * θ ^ (-(1 / (k : ℝ))) * (BX ^ (1 / (k : ℝ)) * BY) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        rw [sub_eq_add_neg, Real.rpow_add hm0, Real.rpow_one]
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos hθ hθm (neg_nonpos.2 (by positivity))) hm0.le
    _ = m * θ ^ (-(1 / (k : ℝ))) * BX ^ (1 / (k : ℝ)) * BY := by ring

/-- **T.DSTAR**, moment form: `E[(max_{u ∈ S} X_u)^m] ≤ |S| · B` when every `E[X_u^m] ≤ B`. -/
theorem wavg_sup_pow_le (hw : ∀ ω, 0 ≤ w ω) (hW : 0 < ∑ ω, w ω) {κ : Type*} (S : Finset κ)
    (hS : S.Nonempty) (X : κ → Ω → ℝ) (hX : ∀ u ω, 0 ≤ X u ω) (m : ℕ) {B : ℝ}
    (hB : ∀ u ∈ S, wavg w (fun ω => X u ω ^ m) ≤ B) :
    wavg w (fun ω => (S.sup' hS fun u => X u ω) ^ m) ≤ S.card * B := by
  have hpt : ∀ ω, (S.sup' hS fun u => X u ω) ^ m ≤ ∑ u ∈ S, X u ω ^ m := fun ω => by
    obtain ⟨u, hu, hmax⟩ := S.exists_mem_eq_sup' hS (fun u => X u ω)
    rw [hmax]
    exact Finset.single_le_sum (f := fun u => X u ω ^ m) (fun v _ => pow_nonneg (hX v ω) m) hu
  calc wavg w (fun ω => (S.sup' hS fun u => X u ω) ^ m)
      ≤ wavg w (fun ω => ∑ u ∈ S, X u ω ^ m) := wavg_mono hw hW hpt
    _ = ∑ u ∈ S, wavg w (fun ω => X u ω ^ m) := wavg_sum S (fun u ω => X u ω ^ m)
    _ ≤ ∑ _u ∈ S, B := Finset.sum_le_sum hB
    _ = S.card * B := by rw [Finset.sum_const, nsmul_eq_mul]

/-- **T.DSTAR**, norm form: `‖max_{u ∈ S} X_u‖_m ≤ |S|^{1/m} max_u ‖X_u‖_m` (`m ≥ 1`). -/
theorem wavg_sup_pow_rpow_le (hw : ∀ ω, 0 ≤ w ω) (hW : 0 < ∑ ω, w ω) {κ : Type*}
    (S : Finset κ) (hS : S.Nonempty) (X : κ → Ω → ℝ) (hX : ∀ u ω, 0 ≤ X u ω) {m : ℕ}
    (hm : 1 ≤ m) {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ u ∈ S, wavg w (fun ω => X u ω ^ m) ≤ B ^ m) :
    wavg w (fun ω => (S.sup' hS fun u => X u ω) ^ m) ^ (1 / (m : ℝ)) ≤
      (S.card : ℝ) ^ (1 / (m : ℝ)) * B := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have h := wavg_sup_pow_le hw hW S hS X hX m hB
  obtain ⟨u₀, hu₀⟩ := hS
  have h0 : 0 ≤ wavg w (fun ω => (S.sup' ⟨u₀, hu₀⟩ fun u => X u ω) ^ m) :=
    wavg_nonneg hw fun ω => pow_nonneg ((hX u₀ ω).trans (Finset.le_sup' (fun u => X u ω) hu₀)) m
  calc wavg w (fun ω => (S.sup' ⟨u₀, hu₀⟩ fun u => X u ω) ^ m) ^ (1 / (m : ℝ))
      ≤ ((S.card : ℝ) * B ^ m) ^ (1 / (m : ℝ)) := Real.rpow_le_rpow h0 h (by positivity)
    _ = (S.card : ℝ) ^ (1 / (m : ℝ)) * B := by
        rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast B m,
          ← Real.rpow_mul hB0, mul_one_div_cancel hmpos.ne', Real.rpow_one]

/-- Weighted Hölder with conjugate exponents: `E[fg] ≤ (E f^p)^{1/p} (E g^q)^{1/q}`. -/
theorem wavg_mul_le_holder_conj (hw : ∀ ω, 0 ≤ w ω) (hW : 0 < ∑ ω, w ω) {f g : Ω → ℝ}
    (hf : ∀ ω, 0 ≤ f ω) (hg : ∀ ω, 0 ≤ g ω) {p q : ℝ} (hpq : p.HolderConjugate q) :
    wavg w (fun ω => f ω * g ω) ≤
      wavg w (fun ω => f ω ^ p) ^ (1 / p) * wavg w (fun ω => g ω ^ q) ^ (1 / q) := by
  have hp := hpq.pos
  have hq := hpq.symm.pos
  have hsum : 1 / p + 1 / q = 1 := by rw [one_div, one_div, hpq.inv_add_inv_eq_one]
  have h := Real.inner_le_Lp_mul_Lq_of_nonneg Finset.univ hpq
    (f := fun ω => w ω ^ (1 / p) * f ω) (g := fun ω => w ω ^ (1 / q) * g ω)
    (fun ω _ => mul_nonneg (Real.rpow_nonneg (hw ω) _) (hf ω))
    (fun ω _ => mul_nonneg (Real.rpow_nonneg (hw ω) _) (hg ω))
  have eFG : ∀ ω, w ω ^ (1 / p) * f ω * (w ω ^ (1 / q) * g ω) = w ω * (f ω * g ω) := fun ω => by
    rw [mul_mul_mul_comm, ← Real.rpow_add' (hw ω) (by rw [hsum]; exact one_ne_zero), hsum,
      Real.rpow_one]
  have ePow : ∀ (ω : Ω) (r : ℝ) (Z : Ω → ℝ), 0 < r → (∀ ω, 0 ≤ Z ω) →
      (w ω ^ (1 / r) * Z ω) ^ r = w ω * Z ω ^ r := fun ω r Z hr hZ => by
    rw [Real.mul_rpow (Real.rpow_nonneg (hw ω) _) (hZ ω), ← Real.rpow_mul (hw ω),
      one_div_mul_cancel hr.ne', Real.rpow_one]
  simp only [eFG, ePow _ p f hp hf, ePow _ q g hq hg] at h
  have hS1 : 0 ≤ ∑ ω, w ω * f ω ^ p := Finset.sum_nonneg fun ω _ =>
    mul_nonneg (hw ω) (Real.rpow_nonneg (hf ω) _)
  have hS2 : 0 ≤ ∑ ω, w ω * g ω ^ q := Finset.sum_nonneg fun ω _ =>
    mul_nonneg (hw ω) (Real.rpow_nonneg (hg ω) _)
  unfold wavg
  rw [Real.div_rpow hS1 hW.le, Real.div_rpow hS2 hW.le, div_mul_div_comm,
    ← Real.rpow_add' hW.le (by rw [hsum]; exact one_ne_zero), hsum, Real.rpow_one]
  exact div_le_div_of_nonneg_right h hW.le

/-- Weighted Hölder with conjugate exponents `(k, k/(k-1))`:
`E[Y Z^{k-1}] ≤ (E Y^k)^{1/k} (E Z^k)^{1 - 1/k}` for `Y, Z ≥ 0`, `k ≥ 1`. -/
theorem wavg_mul_pow_pred_le (hw : ∀ ω, 0 ≤ w ω) (hW : 0 < ∑ ω, w ω) {Y Z : Ω → ℝ}
    (hY : ∀ ω, 0 ≤ Y ω) (hZ : ∀ ω, 0 ≤ Z ω) {k : ℕ} (hk : 1 ≤ k) :
    wavg w (fun ω => Y ω * Z ω ^ (k - 1)) ≤
      wavg w (fun ω => Y ω ^ k) ^ (1 / (k : ℝ)) *
        wavg w (fun ω => Z ω ^ k) ^ (1 - 1 / (k : ℝ)) := by
  rcases hk.eq_or_lt with rfl | hk2
  · simp
  have hk1 : (1 : ℝ) < k := by exact_mod_cast hk2
  have hpq := Real.HolderConjugate.conjExponent hk1
  have h := wavg_mul_le_holder_conj hw hW hY (fun ω => pow_nonneg (hZ ω) (k - 1)) hpq
  have hkr : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by rw [Nat.cast_sub hk]; simp
  have e1 : ∀ ω, Y ω ^ (k : ℝ) = Y ω ^ k := fun ω => Real.rpow_natCast _ _
  have e2 : ∀ ω, (Z ω ^ (k - 1)) ^ Real.conjExponent k = Z ω ^ k := fun ω => by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (hZ ω), hkr, Real.conjExponent,
      mul_div_cancel₀ _ (sub_ne_zero.2 hk1.ne'), Real.rpow_natCast]
  have e3 : 1 / Real.conjExponent k = 1 - 1 / (k : ℝ) := by
    rw [one_div, ← hpq.one_sub_inv, one_div]
  simp only [e1, e2, e3] at h
  exact h

/-- **UMI** (unknown-mass interpolation). `Y, Z ≥ 0`, `k ≥ 2`, `θ > 0`, `E Y^k ≤ M^k`,
`E Z^k ≤ B^k` give `E[YZ] ≤ B (M/θ)^{1/(k-1)} (E Y + θ)`. -/
theorem wavg_mul_le_umi (hw : ∀ ω, 0 ≤ w ω) (hW : 0 < ∑ ω, w ω) {Y Z : Ω → ℝ}
    (hY : ∀ ω, 0 ≤ Y ω) (hZ : ∀ ω, 0 ≤ Z ω) {k : ℕ} (hk : 2 ≤ k) {M B θ : ℝ} (hM : 0 ≤ M)
    (hB : 0 ≤ B) (hθ : 0 < θ) (hYk : wavg w (fun ω => Y ω ^ k) ≤ M ^ k)
    (hZk : wavg w (fun ω => Z ω ^ k) ≤ B ^ k) :
    wavg w (fun ω => Y ω * Z ω) ≤ B * (M / θ) ^ (1 / ((k : ℝ) - 1)) * (wavg w Y + θ) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hk1 : (1 : ℝ) ≤ (k : ℝ) - 1 := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hkr : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  set l := 1 / ((k : ℝ) - 1) with hl
  have hl0 : 0 ≤ l := by positivity
  have hl1 : l ≤ 1 := by rw [hl, div_le_one (by linarith)]; exact hk1
  set s := wavg w Y with hs
  have hs0 : 0 ≤ s := wavg_nonneg hw hY
  -- Hölder with weights `w Y` and exponent `k - 1`
  have h1 := wavg_mul_le_holder hw hW hY hZ (show 1 ≤ k - 1 by omega)
  rw [hkr] at h1
  -- `E[Y Z^{k-1}] ≤ M B^{k-1}`
  have hYk' : wavg w (fun ω => Y ω ^ k) ^ (1 / (k : ℝ)) ≤ M :=
    calc _ ≤ (M ^ k) ^ (1 / (k : ℝ)) :=
          Real.rpow_le_rpow (wavg_nonneg hw fun ω => pow_nonneg (hY ω) k) hYk (by positivity)
      _ = M := by rw [← Real.rpow_natCast, ← Real.rpow_mul hM, mul_one_div_cancel hkpos.ne',
          Real.rpow_one]
  have hZk' : wavg w (fun ω => Z ω ^ k) ^ (1 - 1 / (k : ℝ)) ≤ B ^ ((k : ℝ) - 1) := by
    have h1k : 0 ≤ 1 - 1 / (k : ℝ) := by
      rw [sub_nonneg, div_le_one hkpos]; linarith
    calc _ ≤ (B ^ k) ^ (1 - 1 / (k : ℝ)) :=
          Real.rpow_le_rpow (wavg_nonneg hw fun ω => pow_nonneg (hZ ω) k) hZk h1k
      _ = B ^ ((k : ℝ) - 1) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hB]
          congr 1
          field_simp
  have h2 : wavg w (fun ω => Y ω * Z ω ^ (k - 1)) ≤ M * B ^ ((k : ℝ) - 1) :=
    (wavg_mul_pow_pred_le hw hW hY hZ (by omega)).trans
      (mul_le_mul hYk' hZk'
        (Real.rpow_nonneg (wavg_nonneg hw fun ω => pow_nonneg (hZ ω) k) _) hM)
  have hYZ0 : 0 ≤ wavg w (fun ω => Y ω * Z ω ^ (k - 1)) :=
    wavg_nonneg hw fun ω => mul_nonneg (hY ω) (pow_nonneg (hZ ω) _)
  -- the split `s ≥ θ` / `s < θ`
  have hMθ : 0 ≤ (M / θ) ^ l := Real.rpow_nonneg (div_nonneg hM hθ.le) l
  have key : s ^ (1 - l) * M ^ l ≤ (M / θ) ^ l * (s + θ) := by
    rcases le_or_gt θ s with hsθ | hsθ
    · have hs : 0 < s := hθ.trans_le hsθ
      have e : s ^ (1 - l) * M ^ l = s * (M / s) ^ l := by
        rw [Real.div_rpow hM hs.le, Real.rpow_sub hs, Real.rpow_one, div_mul_eq_mul_div,
          mul_div_assoc]
      rw [e]
      have h3 : (M / s) ^ l ≤ (M / θ) ^ l :=
        Real.rpow_le_rpow (div_nonneg hM hs.le) (div_le_div_of_nonneg_left hM hθ hsθ) hl0
      nlinarith [mul_le_mul_of_nonneg_left h3 hs0]
    · have e : θ ^ (1 - l) * M ^ l = θ * (M / θ) ^ l := by
        rw [Real.div_rpow hM hθ.le, Real.rpow_sub hθ, Real.rpow_one, div_mul_eq_mul_div,
          mul_div_assoc]
      calc s ^ (1 - l) * M ^ l ≤ θ ^ (1 - l) * M ^ l :=
            mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hs0 hsθ.le (by linarith))
              (Real.rpow_nonneg hM _)
        _ = θ * (M / θ) ^ l := e
        _ ≤ (M / θ) ^ l * (s + θ) := by nlinarith
  calc wavg w (fun ω => Y ω * Z ω)
      ≤ s ^ (1 - l) * wavg w (fun ω => Y ω * Z ω ^ (k - 1)) ^ l := h1
    _ ≤ s ^ (1 - l) * (M * B ^ ((k : ℝ) - 1)) ^ l :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hYZ0 h2 hl0) (Real.rpow_nonneg hs0 _)
    _ = B * (s ^ (1 - l) * M ^ l) := by
        rw [Real.mul_rpow hM (Real.rpow_nonneg hB _), ← Real.rpow_mul hB, hl,
          mul_one_div_cancel (by linarith), Real.rpow_one]
        ring
    _ ≤ B * ((M / θ) ^ l * (s + θ)) := mul_le_mul_of_nonneg_left key hB
    _ = B * (M / θ) ^ (1 / ((k : ℝ) - 1)) * (wavg w Y + θ) := by rw [hl, hs]; ring

end BiluLinial.Tight
