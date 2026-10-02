/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecA.EndpointPfRank2
public import BiluLinial.Tight.SecA.EndpointPfMaj
public import BiluLinial.Tight.Compare.Endpoint

/-!
# The edge fibre of (E1), at the level of a base pair of matrices

A base pair `(N⁺, N⁻)` of normalized precisions with source square roots `(sv, si)` (plus) and
`(tv, ti)` (minus) has physical entries `x = sv N⁺⁻¹_vi si`, `g_vv = sv N⁺⁻¹_vv sv`, ... . Moving
along the edge fibre by `t` replaces `N⁺` by `N⁺ + a sv si t E` and `N⁻` by `N⁻ - a tv ti t E`.

* `epf_fibre_value`: `(det N⁺ det N⁻)^p Π(t) = (det N⁺(t) det N⁻(t))^p · sv N⁺(t)⁻¹_vi si`
  whenever `δ₊(t) ≠ 0` (rank-two formulas, `p ≥ 1`).
* `epf_fibre_poly_eq`: hence the two endpoint polynomials of a fibre coincide.
* `epf_caseA`: a fibre with a small positive definite endpoint (`64 p a g* ≤ 1`), whose other
  endpoint is positive definite (`epf_caseA_posDef_plus`/`_minus`), contributes at most
  `1000 p⁵ a⁵ W g*⁶` (`endpoint_chain` plus `epf_fifth_bound`).
* `epf_caseB`: a positive definite endpoint with `64 p a g* > 1` contributes at most
  `1.15·10⁹ p⁵ a⁵ W g*⁶` on its own.
-/

@[expose] public section

namespace BiluLinial.Tight.SecA

open Matrix Polynomial

section Fibre

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The fibre polynomial of a base pair. -/
noncomputable def epf_Pi (p : ℕ) (a : ℝ) (Np Nm : Matrix n n ℝ) (sv si tv ti : ℝ) (v i : n) :
    ℝ[X] :=
  fibrePoly p a (sv * Np⁻¹ v i * si) (sv * Np⁻¹ v v * sv) (si * Np⁻¹ i i * si)
    (tv * Nm⁻¹ v i * ti) (tv * Nm⁻¹ v v * tv) (ti * Nm⁻¹ i i * ti)

/-- `𝒟_j = j! [t^j] Π` of a base pair. -/
noncomputable def epf_D (p : ℕ) (a : ℝ) (Np Nm : Matrix n n ℝ) (sv si tv ti : ℝ) (v i : n)
    (j : ℕ) : ℝ :=
  (j.factorial : ℝ) * (epf_Pi p a Np Nm sv si tv ti v i).coeff j

/-- `g* = max(G⁺_vv, G⁺_ii, G⁻_vv, G⁻_ii)` of a base pair. -/
noncomputable def epf_gs (Np Nm : Matrix n n ℝ) (sv si tv ti : ℝ) (v i : n) : ℝ :=
  max (max (sv * Np⁻¹ v v * sv) (si * Np⁻¹ i i * si))
    (max (tv * Nm⁻¹ v v * tv) (ti * Nm⁻¹ i i * ti))

/-- The weight `(det N⁺ det N⁻)^p` without its positivity indicator. -/
noncomputable def epf_U (p : ℕ) (Np Nm : Matrix n n ℝ) : ℝ := (Np.det * Nm.det) ^ p

theorem epf_U_nonneg (p : ℕ) {Np Nm : Matrix n n ℝ} (hNp : Np.PosDef) (hNm : Nm.PosDef) :
    0 ≤ epf_U p Np Nm :=
  pow_nonneg (mul_nonneg hNp.det_pos.le hNm.det_pos.le) p

theorem epf_isUnit_det {N : Matrix n n ℝ} (hN : N.PosDef) : IsUnit N.det :=
  isUnit_iff_ne_zero.2 hN.det_pos.ne'

/-! ### Physical bounds at a positive definite base -/

theorem epf_phys_bounds {N : Matrix n n ℝ} (hN : N.PosDef) {v i : n} (hvi : v ≠ i)
    (sv si : ℝ) :
    0 ≤ sv * N⁻¹ v v * sv ∧ 0 ≤ si * N⁻¹ i i * si ∧
      0 ≤ (sv * N⁻¹ v v * sv) * (si * N⁻¹ i i * si) - (sv * N⁻¹ v i * si) ^ 2 := by
  have hG := hN.inv
  have h1 : 0 < N⁻¹ v v := hG.diag_pos
  have h2 : 0 < N⁻¹ i i := hG.diag_pos
  have h3 := epf_minor_pos hG hvi
  refine ⟨?_, ?_, ?_⟩
  · have e : sv * N⁻¹ v v * sv = N⁻¹ v v * sv ^ 2 := by ring
    rw [e]; exact mul_nonneg h1.le (sq_nonneg _)
  · have e : si * N⁻¹ i i * si = N⁻¹ i i * si ^ 2 := by ring
    rw [e]; exact mul_nonneg h2.le (sq_nonneg _)
  · have e : (sv * N⁻¹ v v * sv) * (si * N⁻¹ i i * si) - (sv * N⁻¹ v i * si) ^ 2 =
        (sv * si) ^ 2 * (N⁻¹ v v * N⁻¹ i i - N⁻¹ v i ^ 2) := by ring
    rw [e]; exact mul_nonneg (sq_nonneg _) h3.le

theorem epf_bounds_of {x gvv gii g : ℝ} (h1 : 0 ≤ gvv) (h2 : 0 ≤ gii)
    (h3 : 0 ≤ gvv * gii - x ^ 2) (hv : gvv ≤ g) (hi : gii ≤ g) :
    |x| ≤ g ∧ |gvv * gii - x ^ 2| ≤ g ^ 2 := by
  have hg : 0 ≤ g := h1.trans hv
  have hp : gvv * gii ≤ g ^ 2 := by rw [sq]; exact mul_le_mul hv hi h2 hg
  have hx2 : x ^ 2 ≤ g ^ 2 := by linarith
  constructor
  · rw [abs_le]; constructor <;> nlinarith
  · rw [abs_of_nonneg h3]; nlinarith [sq_nonneg x]

theorem epf_base_bounds {Np Nm : Matrix n n ℝ} (hNp : Np.PosDef) (hNm : Nm.PosDef) {v i : n}
    (hvi : v ≠ i) (sv si tv ti : ℝ) :
    0 ≤ epf_gs Np Nm sv si tv ti v i ∧
    |sv * Np⁻¹ v i * si| ≤ epf_gs Np Nm sv si tv ti v i ∧
    |(sv * Np⁻¹ v v * sv) * (si * Np⁻¹ i i * si) - (sv * Np⁻¹ v i * si) ^ 2| ≤
      epf_gs Np Nm sv si tv ti v i ^ 2 ∧
    |tv * Nm⁻¹ v i * ti| ≤ epf_gs Np Nm sv si tv ti v i ∧
    |(tv * Nm⁻¹ v v * tv) * (ti * Nm⁻¹ i i * ti) - (tv * Nm⁻¹ v i * ti) ^ 2| ≤
      epf_gs Np Nm sv si tv ti v i ^ 2 := by
  obtain ⟨a1, a2, a3⟩ := epf_phys_bounds hNp hvi sv si
  obtain ⟨b1, b2, b3⟩ := epf_phys_bounds hNm hvi tv ti
  unfold epf_gs
  have hv := le_trans (le_max_left (sv * Np⁻¹ v v * sv) (si * Np⁻¹ i i * si))
    (le_max_left _ (max (tv * Nm⁻¹ v v * tv) (ti * Nm⁻¹ i i * ti)))
  have hi := le_trans (le_max_right (sv * Np⁻¹ v v * sv) (si * Np⁻¹ i i * si))
    (le_max_left _ (max (tv * Nm⁻¹ v v * tv) (ti * Nm⁻¹ i i * ti)))
  have hv' := le_trans (le_max_left (tv * Nm⁻¹ v v * tv) (ti * Nm⁻¹ i i * ti))
    (le_max_right (max (sv * Np⁻¹ v v * sv) (si * Np⁻¹ i i * si)) _)
  have hi' := le_trans (le_max_right (tv * Nm⁻¹ v v * tv) (ti * Nm⁻¹ i i * ti))
    (le_max_right (max (sv * Np⁻¹ v v * sv) (si * Np⁻¹ i i * si)) _)
  obtain ⟨c1, c2⟩ := epf_bounds_of a1 a2 a3 hv hi
  obtain ⟨d1, d2⟩ := epf_bounds_of b1 b2 b3 hv' hi'
  exact ⟨a1.trans hv, c1, c2, d1, d2⟩

/-! ### Rank-two formulas in physical form -/

theorem epf_delta_eq_plus (a sv si : ℝ) (N : Matrix n n ℝ) (v i : n) (t : ℝ) :
    1 + 2 * (1 * a * (sv * si) * t) * N⁻¹ v i -
        (1 * a * (sv * si) * t) ^ 2 * (N⁻¹ v v * N⁻¹ i i - N⁻¹ v i ^ 2) =
      (fibreDelta a (sv * N⁻¹ v i * si) (sv * N⁻¹ v v * sv) (si * N⁻¹ i i * si)).eval t := by
  simp only [fibreDelta, eval_add, eval_sub, eval_mul, eval_C, eval_X, eval_one, eval_pow]
  ring

theorem epf_delta_eq_minus (a tv ti : ℝ) (N : Matrix n n ℝ) (v i : n) (t : ℝ) :
    1 + 2 * (-1 * a * (tv * ti) * t) * N⁻¹ v i -
        (-1 * a * (tv * ti) * t) ^ 2 * (N⁻¹ v v * N⁻¹ i i - N⁻¹ v i ^ 2) =
      (fibreDelta a (-(tv * N⁻¹ v i * ti)) (tv * N⁻¹ v v * tv) (ti * N⁻¹ i i * ti)).eval t := by
  simp only [fibreDelta, eval_add, eval_sub, eval_mul, eval_C, eval_X, eval_one, eval_pow]
  ring

theorem epf_det_plus {N : Matrix n n ℝ} (hN : N.IsHermitian) (hd : IsUnit N.det) {v i : n}
    (hvi : v ≠ i) (a sv si t : ℝ) :
    (N + (1 * a * (sv * si) * t) • edgeE v i).det =
      N.det * (fibreDelta a (sv * N⁻¹ v i * si) (sv * N⁻¹ v v * sv)
        (si * N⁻¹ i i * si)).eval t := by
  rw [det_add_rank_two_pf hN hd hvi, epf_delta_eq_plus]

theorem epf_det_minus {N : Matrix n n ℝ} (hN : N.IsHermitian) (hd : IsUnit N.det) {v i : n}
    (hvi : v ≠ i) (a tv ti t : ℝ) :
    (N + (-1 * a * (tv * ti) * t) • edgeE v i).det =
      N.det * (fibreDelta a (-(tv * N⁻¹ v i * ti)) (tv * N⁻¹ v v * tv)
        (ti * N⁻¹ i i * ti)).eval t := by
  rw [det_add_rank_two_pf hN hd hvi, epf_delta_eq_minus]

theorem epf_inv_plus {N : Matrix n n ℝ} (hN : N.IsHermitian) (hd : IsUnit N.det) {v i : n}
    (hvi : v ≠ i) (a sv si t : ℝ)
    (hδ : (fibreDelta a (sv * N⁻¹ v i * si) (sv * N⁻¹ v v * sv) (si * N⁻¹ i i * si)).eval t ≠ 0) :
    sv * (N + (1 * a * (sv * si) * t) • edgeE v i)⁻¹ v i * si =
      (sv * N⁻¹ v i * si - a * ((sv * N⁻¹ v v * sv) * (si * N⁻¹ i i * si) -
          (sv * N⁻¹ v i * si) ^ 2) * t) /
        (fibreDelta a (sv * N⁻¹ v i * si) (sv * N⁻¹ v v * sv) (si * N⁻¹ i i * si)).eval t := by
  rw [← epf_delta_eq_plus a sv si N v i t] at hδ ⊢
  rw [inv_add_rank_two_apply_pf hN hd hvi hδ]
  rw [show ∀ A δ : ℝ, sv * (A / δ) * si = sv * A * si / δ from fun A δ => by ring]
  congr 1
  ring

/-! ### The fibre value and the polynomial identity -/

theorem epf_fibre_value {p : ℕ} (hp : 1 ≤ p) (a : ℝ) {Np Nm : Matrix n n ℝ}
    (hNp : Np.IsHermitian) (hNm : Nm.IsHermitian) (hdp : IsUnit Np.det) (hdm : IsUnit Nm.det)
    {v i : n} (hvi : v ≠ i) (sv si tv ti t : ℝ)
    (ht : (fibreDelta a (sv * Np⁻¹ v i * si) (sv * Np⁻¹ v v * sv)
      (si * Np⁻¹ i i * si)).eval t ≠ 0) :
    epf_U p Np Nm * (epf_Pi p a Np Nm sv si tv ti v i).eval t =
      epf_U p (Np + (1 * a * (sv * si) * t) • edgeE v i)
          (Nm + (-1 * a * (tv * ti) * t) • edgeE v i) *
        (sv * (Np + (1 * a * (sv * si) * t) • edgeE v i)⁻¹ v i * si) := by
  rw [epf_U, epf_U, epf_det_plus hNp hdp hvi, epf_det_minus hNm hdm hvi,
    epf_inv_plus hNp hdp hvi _ _ _ _ ht]
  simp only [epf_Pi, fibrePoly, eval_mul, eval_pow, eval_sub, eval_C, eval_X]
  generalize (fibreDelta a (sv * Np⁻¹ v i * si) (sv * Np⁻¹ v v * sv)
    (si * Np⁻¹ i i * si)).eval t = δp at ht ⊢
  generalize (fibreDelta a (-(tv * Nm⁻¹ v i * ti)) (tv * Nm⁻¹ v v * tv)
    (ti * Nm⁻¹ i i * ti)).eval t = δm
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  rw [show q + 1 - 1 = q by omega]
  field_simp
  ring

theorem epf_fibre_poly_eq {p : ℕ} (hp : 1 ≤ p) (a : ℝ) {Np Nm Np' Nm' : Matrix n n ℝ}
    (hNp : Np.IsHermitian) (hNm : Nm.IsHermitian) (hdp : IsUnit Np.det) (hdm : IsUnit Nm.det)
    (hNp' : Np'.IsHermitian) (hNm' : Nm'.IsHermitian) (hdp' : IsUnit Np'.det)
    (hdm' : IsUnit Nm'.det) {v i : n} (hvi : v ≠ i) (sv si tv ti s₀ κ : ℝ)
    (hp' : Np' = Np + (1 * a * (sv * si) * κ) • edgeE v i)
    (hm' : Nm' = Nm + (-1 * a * (tv * ti) * κ) • edgeE v i) :
    C (epf_U p Np Nm) * (epf_Pi p a Np Nm sv si tv ti v i).comp (X - C s₀) =
      C (epf_U p Np' Nm') * (epf_Pi p a Np' Nm' sv si tv ti v i).comp (X - C (s₀ + κ)) := by
  set δ := fibreDelta a (sv * Np⁻¹ v i * si) (sv * Np⁻¹ v v * sv) (si * Np⁻¹ i i * si) with hδ
  have hq : δ.comp (X - C s₀) ≠ 0 := by
    intro h
    have := congrArg (eval s₀) h
    simp [hδ, fibreDelta] at this
  apply eq_of_infinite_eval_eq
  refine Set.Infinite.mono ?_ (finite_setOfPred_isRoot hq).infinite_compl
  intro s hs
  have hs0 : δ.eval (s - s₀) ≠ 0 := by simpa [IsRoot, eval_comp] using hs
  simp only [Set.mem_ofPred_eq, eval_mul, eval_C, eval_comp, eval_sub, eval_X]
  have e1 : Np' + (1 * a * (sv * si) * (s - (s₀ + κ))) • edgeE v i =
      Np + (1 * a * (sv * si) * (s - s₀)) • edgeE v i := by
    rw [hp', add_assoc, ← add_smul]; congr 2; ring
  have e2 : Nm' + (-1 * a * (tv * ti) * (s - (s₀ + κ))) • edgeE v i =
      Nm + (-1 * a * (tv * ti) * (s - s₀)) • edgeE v i := by
    rw [hm', add_assoc, ← add_smul]; congr 2; ring
  have hs' : (fibreDelta a (sv * Np'⁻¹ v i * si) (sv * Np'⁻¹ v v * sv)
      (si * Np'⁻¹ i i * si)).eval (s - (s₀ + κ)) ≠ 0 := by
    intro h0
    have h1 := epf_det_plus hNp' hdp' hvi a sv si (s - (s₀ + κ))
    rw [h0, mul_zero, e1, epf_det_plus hNp hdp hvi] at h1
    exact (mul_ne_zero hdp.ne_zero hs0) h1
  rw [epf_fibre_value hp a hNp hNm hdp hdm hvi sv si tv ti (s - s₀) hs0,
    epf_fibre_value hp a hNp' hNm' hdp' hdm' hvi sv si tv ti (s - (s₀ + κ)) hs', e1, e2]

theorem epf_iterate_derivative_comp_sub (f : ℝ[X]) (c : ℝ) (j : ℕ) :
    Polynomial.derivative^[j] (f.comp (X - C c)) =
      (Polynomial.derivative^[j] f).comp (X - C c) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih, derivative_comp, Function.iterate_succ_apply']
    simp

theorem epf_eval_shift (u : ℝ) (f : ℝ[X]) (c t : ℝ) (j : ℕ) :
    (Polynomial.derivative^[j] (C u * f.comp (X - C c))).eval t =
      u * (Polynomial.derivative^[j] f).eval (t - c) := by
  rw [iterate_derivative_C_mul, epf_iterate_derivative_comp_sub, eval_mul, eval_C, eval_comp,
    eval_sub, eval_X, eval_C]

theorem epf_D_zero (p : ℕ) (a : ℝ) (Np Nm : Matrix n n ℝ) (sv si tv ti : ℝ) (v i : n) :
    epf_D p a Np Nm sv si tv ti v i 0 = sv * Np⁻¹ v i * si := by
  rw [epf_D, coeff_zero_eq_eval_zero]
  simp [epf_Pi, fibrePoly, fibreDelta]

/-! ### Case A: a small endpoint -/

theorem epf_eval_delta_pos {a x gvv gii g κ : ℝ} (ha : 0 ≤ a) (hg : 0 ≤ g) (hκ : |κ| ≤ 2)
    (hx : |x| ≤ g) (hD : |gvv * gii - x ^ 2| ≤ g ^ 2) (hw : 64 * (a * g) ≤ 1) :
    0 < (fibreDelta a x gvv gii).eval κ := by
  simp only [fibreDelta, eval_add, eval_sub, eval_mul, eval_C, eval_X, eval_one, eval_pow]
  have h1 : |2 * a * x * κ| ≤ 4 * (a * g) := by
    rw [abs_mul, abs_mul, abs_mul, abs_two, abs_of_nonneg ha]
    have := mul_le_mul hx hκ (abs_nonneg κ) hg
    nlinarith [mul_le_mul_of_nonneg_left this ha]
  have h2 : |a ^ 2 * (gvv * gii - x ^ 2) * κ ^ 2| ≤ 4 * (a * g) ^ 2 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg a), abs_pow]
    have hk2 : |κ| ^ 2 ≤ 4 := by nlinarith [abs_nonneg κ]
    have := mul_le_mul hD hk2 (by positivity) (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left this (sq_nonneg a)]
  have h3 := neg_abs_le (2 * a * x * κ)
  have h4 := le_abs_self (a ^ 2 * (gvv * gii - x ^ 2) * κ ^ 2)
  have hw' : a * g ≤ 1 / 64 := by linarith
  have hw0 : 0 ≤ a * g := mul_nonneg ha hg
  nlinarith [mul_le_mul_of_nonneg_left hw' hw0]

theorem epf_small_aux {p : ℕ} (hp : 1 ≤ p) {a g : ℝ} (ha : 0 ≤ a) (hg : 0 ≤ g)
    (hsmall : 64 * p * a * g ≤ 1) : 64 * (a * g) ≤ 1 := by
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
  nlinarith [mul_nonneg ha hg]

theorem epf_caseA_posDef_plus {p : ℕ} (hp : 1 ≤ p) {a : ℝ} (ha : 0 < a) {N : Matrix n n ℝ}
    (hN : N.PosDef) {v i : n} (hvi : v ≠ i) (sv si g κ : ℝ) (hκ : |κ| ≤ 2) (hg : 0 ≤ g)
    (hx : |sv * N⁻¹ v i * si| ≤ g)
    (hD : |(sv * N⁻¹ v v * sv) * (si * N⁻¹ i i * si) - (sv * N⁻¹ v i * si) ^ 2| ≤ g ^ 2)
    (hsmall : 64 * p * a * g ≤ 1) :
    (N + (1 * a * (sv * si) * κ) • edgeE v i).PosDef := by
  refine epf_posDef_add_rank_two hN hvi ?_
  rw [epf_delta_eq_plus]
  exact epf_eval_delta_pos ha.le hg hκ hx hD (epf_small_aux hp ha.le hg hsmall)

theorem epf_caseA_posDef_minus {p : ℕ} (hp : 1 ≤ p) {a : ℝ} (ha : 0 < a) {N : Matrix n n ℝ}
    (hN : N.PosDef) {v i : n} (hvi : v ≠ i) (tv ti g κ : ℝ) (hκ : |κ| ≤ 2) (hg : 0 ≤ g)
    (hx : |tv * N⁻¹ v i * ti| ≤ g)
    (hD : |(tv * N⁻¹ v v * tv) * (ti * N⁻¹ i i * ti) - (tv * N⁻¹ v i * ti) ^ 2| ≤ g ^ 2)
    (hsmall : 64 * p * a * g ≤ 1) :
    (N + (-1 * a * (tv * ti) * κ) • edgeE v i).PosDef := by
  refine epf_posDef_add_rank_two hN hvi ?_
  rw [epf_delta_eq_minus]
  refine epf_eval_delta_pos ha.le hg hκ (by rwa [abs_neg]) (by rwa [neg_sq])
    (epf_small_aux hp ha.le hg hsmall)

/-- **Case A.** A fibre whose endpoint `(N⁺, N⁻)` is positive definite and small, and whose other
endpoint `(N⁺', N⁻')` is positive definite, contributes at most `1000 p⁵ a⁵ W g*⁶`. -/
theorem epf_caseA {p : ℕ} (hp : 1 ≤ p) {a : ℝ} (ha : 0 < a) {Np Nm Np' Nm' : Matrix n n ℝ}
    (hNp : Np.PosDef) (hNm : Nm.PosDef) (hNp' : Np'.PosDef) (hNm' : Nm'.PosDef)
    {v i : n} (hvi : v ≠ i) (sv si tv ti : ℝ) {s₀ : ℝ} (hs₀ : s₀ = 1 ∨ s₀ = -1)
    (hp' : Np' = Np + (1 * a * (sv * si) * (-2 * s₀)) • edgeE v i)
    (hm' : Nm' = Nm + (-1 * a * (tv * ti) * (-2 * s₀)) • edgeE v i)
    (hsmall : 64 * p * a * epf_gs Np Nm sv si tv ti v i ≤ 1) :
    |epf_U p Np Nm * (s₀ * (sv * Np⁻¹ v i * si) - epf_D p a Np Nm sv si tv ti v i 1 +
        epf_D p a Np Nm sv si tv ti v i 3 / 3) +
      epf_U p Np' Nm' * (-s₀ * (sv * Np'⁻¹ v i * si) - epf_D p a Np' Nm' sv si tv ti v i 1 +
        epf_D p a Np' Nm' sv si tv ti v i 3 / 3)| ≤
      1000 * (p : ℝ) ^ 5 * a ^ 5 * (epf_U p Np Nm * epf_gs Np Nm sv si tv ti v i ^ 6) := by
  obtain ⟨hg, hx, hdx, hy, hdy⟩ := epf_base_bounds hNp hNm hvi sv si tv ti
  have hU := epf_U_nonneg p hNp hNm
  have hpoly := epf_fibre_poly_eq hp a hNp.isHermitian hNm.isHermitian (epf_isUnit_det hNp)
    (epf_isUnit_det hNm) hNp'.isHermitian hNm'.isHermitian (epf_isUnit_det hNp')
    (epf_isUnit_det hNm') hvi sv si tv ti s₀ (-2 * s₀) hp' hm'
  let F : ℕ → ℝ → ℝ := fun m t =>
    (Polynomial.derivative^[m]
      (C (epf_U p Np Nm) * (epf_Pi p a Np Nm sv si tv ti v i).comp (X - C s₀))).eval t
  have hF : ∀ m < 5, ∀ t ∈ Set.Icc (-1 : ℝ) 1, HasDerivAt (F m) (F (m + 1) t) t := by
    intro m _ t _
    have h := (Polynomial.derivative^[m]
      (C (epf_U p Np Nm) * (epf_Pi p a Np Nm sv si tv ti v i).comp (X - C s₀))).hasDerivAt t
    rw [← Function.iterate_succ_apply' Polynomial.derivative] at h
    exact h
  have hM : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |F 5 t| ≤
      epf_U p Np Nm * (2 * (4 * p * a) ^ 5 * epf_gs Np Nm sv si tv ti v i ^ 6) := by
    intro t ht
    simp only [F]
    rw [epf_eval_shift, abs_mul, abs_of_nonneg hU]
    refine mul_le_mul_of_nonneg_left ?_ hU
    refine epf_fifth_bound hp ha.le hg hx hdx hy hdy hsmall ?_
    rcases hs₀ with rfl | rfl <;> rw [abs_le] <;> constructor <;> linarith [ht.1, ht.2]
  have hchain := endpoint_chain F hF _ hM
  rw [rad_mul_id, integral_radReal, integral_radReal] at hchain
  have hv1 : ∀ j, F j s₀ = epf_U p Np Nm * epf_D p a Np Nm sv si tv ti v i j := by
    intro j
    simp only [F]
    rw [epf_eval_shift, sub_self, epf_eval_zero_iterate_derivative]
    rfl
  have hv2 : ∀ j, F j (-s₀) = epf_U p Np' Nm' * epf_D p a Np' Nm' sv si tv ti v i j := by
    intro j
    simp only [F]
    rw [hpoly, epf_eval_shift, show -s₀ - (s₀ + -2 * s₀) = 0 by ring,
      epf_eval_zero_iterate_derivative]
    rfl
  rw [← epf_D_zero p a Np Nm sv si tv ti v i, ← epf_D_zero p a Np' Nm' sv si tv ti v i]
  have key : epf_U p Np Nm * (s₀ * epf_D p a Np Nm sv si tv ti v i 0 -
        epf_D p a Np Nm sv si tv ti v i 1 + epf_D p a Np Nm sv si tv ti v i 3 / 3) +
      epf_U p Np' Nm' * (-s₀ * epf_D p a Np' Nm' sv si tv ti v i 0 -
        epf_D p a Np' Nm' sv si tv ti v i 1 + epf_D p a Np' Nm' sv si tv ti v i 3 / 3) =
      2 * ((F 0 1 - F 0 (-1)) / 2 - ((F 1 1 + F 1 (-1)) / 2 - (F 3 1 + F 3 (-1)) / 2 / 3)) := by
    rcases hs₀ with rfl | rfl
    · rw [hv1 0, hv1 1, hv1 3, hv2 0, hv2 1, hv2 3]; ring
    · simp only [neg_neg] at hv2
      rw [hv1 0, hv1 1, hv1 3, hv2 0, hv2 1, hv2 3]; ring
  rw [key, abs_mul, abs_two]
  have hpos : 0 ≤ (p : ℝ) ^ 5 * a ^ 5 * (epf_U p Np Nm * epf_gs Np Nm sv si tv ti v i ^ 6) :=
    mul_nonneg (by positivity) (mul_nonneg hU (by positivity))
  have e : 2 * (13 / 60 * (epf_U p Np Nm * (2 * (4 * p * a) ^ 5 *
      epf_gs Np Nm sv si tv ti v i ^ 6))) =
      53248 / 60 * ((p : ℝ) ^ 5 * a ^ 5 * (epf_U p Np Nm * epf_gs Np Nm sv si tv ti v i ^ 6)) := by
    ring
  have e' : 1000 * (p : ℝ) ^ 5 * a ^ 5 * (epf_U p Np Nm * epf_gs Np Nm sv si tv ti v i ^ 6) =
      1000 * ((p : ℝ) ^ 5 * a ^ 5 * (epf_U p Np Nm * epf_gs Np Nm sv si tv ti v i ^ 6)) := by
    ring
  calc 2 * |(F 0 1 - F 0 (-1)) / 2 - ((F 1 1 + F 1 (-1)) / 2 - (F 3 1 + F 3 (-1)) / 2 / 3)|
      ≤ 2 * (13 / 60 * (epf_U p Np Nm * (2 * (4 * p * a) ^ 5 *
          epf_gs Np Nm sv si tv ti v i ^ 6))) := by linarith
    _ ≤ 1000 * (p : ℝ) ^ 5 * a ^ 5 * (epf_U p Np Nm * epf_gs Np Nm sv si tv ti v i ^ 6) := by
      rw [e, e']; exact mul_le_mul_of_nonneg_right (by norm_num) hpos

/-! ### Case B: a large endpoint -/

/-- **Case B.** At a positive definite endpoint with `64 p a g* > 1`,
`|W (s x - 𝒟₁ + 𝒟₃/3)| ≤ 1.15·10⁹ p⁵ a⁵ W g*⁶` for `|s| ≤ 1`. -/
theorem epf_caseB {p : ℕ} (hp : 1 ≤ p) {a : ℝ} (ha : 0 < a) {Np Nm : Matrix n n ℝ}
    (hNp : Np.PosDef) (hNm : Nm.PosDef) {v i : n} (hvi : v ≠ i) (sv si tv ti : ℝ) {s : ℝ}
    (hs : |s| ≤ 1) (hbig : 1 < 64 * p * a * epf_gs Np Nm sv si tv ti v i) :
    |epf_U p Np Nm * (s * (sv * Np⁻¹ v i * si) - epf_D p a Np Nm sv si tv ti v i 1 +
        epf_D p a Np Nm sv si tv ti v i 3 / 3)| ≤
      1.15e9 * (p : ℝ) ^ 5 * a ^ 5 * (epf_U p Np Nm * epf_gs Np Nm sv si tv ti v i ^ 6) := by
  obtain ⟨hg, hx, hdx, hy, hdy⟩ := epf_base_bounds hNp hNm hvi sv si tv ti
  have hU := epf_U_nonneg p hNp hNm
  set g := epf_gs Np Nm sv si tv ti v i with hgdef
  set P := (p : ℝ) * a * g with hP
  have hP0 : 0 ≤ P := mul_nonneg (mul_nonneg (by positivity) ha.le) hg
  have hP1 : 1 ≤ 64 * P := by rw [hP]; linarith
  set x := sv * Np⁻¹ v i * si with hxdef
  set D1 := epf_D p a Np Nm sv si tv ti v i 1 with hD1def
  set D3 := epf_D p a Np Nm sv si tv ti v i 3 with hD3def
  have hD1 : |D1| ≤ 4 * P * g := by
    have e : (4 * (p : ℝ) * a) ^ 1 * g ^ (1 + 1) = 4 * P * g := by rw [hP]; ring
    rw [← e]; exact epf_coeff_bound hp ha.le hg hx hdx hy hdy 1
  have hD3 : |D3| ≤ 64 * P ^ 3 * g := by
    have e : (4 * (p : ℝ) * a) ^ 3 * g ^ (3 + 1) = 64 * P ^ 3 * g := by rw [hP]; ring
    rw [← e]; exact epf_coeff_bound hp ha.le hg hx hdx hy hdy 3
  have hsx : |s * x| ≤ g := by
    rw [abs_mul]
    have := mul_le_mul hs hx (abs_nonneg _) zero_le_one
    linarith
  have hsub : |s * x - D1| ≤ |s * x| + |D1| := by
    have := abs_add_le (s * x) (-D1)
    rwa [abs_neg, ← sub_eq_add_neg] at this
  have hinner : |s * x - D1 + D3 / 3| ≤ g + 4 * P * g + 64 * P ^ 3 * g / 3 := by
    calc |s * x - D1 + D3 / 3| ≤ |s * x - D1| + |D3 / 3| := abs_add_le _ _
      _ ≤ (|s * x| + |D1|) + |D3| / 3 := by
          rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
          exact add_le_add hsub le_rfl
      _ ≤ (g + 4 * P * g) + 64 * P ^ 3 * g / 3 :=
          add_le_add (add_le_add hsx hD1) (div_le_div_of_nonneg_right hD3 (by norm_num))
  have e1 : g ≤ 64 ^ 5 * P ^ 5 * g := by
    have := mul_le_mul_of_nonneg_left (one_le_pow₀ hP1 (n := 5)) hg
    linarith [show g * (64 * P) ^ 5 = 64 ^ 5 * P ^ 5 * g by ring]
  have e2 : 4 * P * g ≤ 4 * 64 ^ 4 * P ^ 5 * g := by
    have h0 : 0 ≤ 4 * P * g := by positivity
    have := mul_le_mul_of_nonneg_left (one_le_pow₀ hP1 (n := 4)) h0
    linarith [show 4 * P * g * (64 * P) ^ 4 = 4 * 64 ^ 4 * P ^ 5 * g by ring]
  have e3 : 64 * P ^ 3 * g / 3 ≤ 64 * 64 ^ 2 / 3 * P ^ 5 * g := by
    have h0 : 0 ≤ 64 * P ^ 3 * g / 3 := by positivity
    have := mul_le_mul_of_nonneg_left (one_le_pow₀ hP1 (n := 2)) h0
    linarith [show 64 * P ^ 3 * g / 3 * (64 * P) ^ 2 = 64 * 64 ^ 2 / 3 * P ^ 5 * g by ring]
  have hP5 : 0 ≤ P ^ 5 * g := by positivity
  have htot : |s * x - D1 + D3 / 3| ≤ 1.15e9 * (P ^ 5 * g) := by
    calc |s * x - D1 + D3 / 3| ≤ g + 4 * P * g + 64 * P ^ 3 * g / 3 := hinner
      _ ≤ 64 ^ 5 * P ^ 5 * g + 4 * 64 ^ 4 * P ^ 5 * g + 64 * 64 ^ 2 / 3 * P ^ 5 * g :=
          add_le_add (add_le_add e1 e2) e3
      _ = ((64 : ℝ) ^ 5 + 4 * 64 ^ 4 + 64 * 64 ^ 2 / 3) * (P ^ 5 * g) := by ring
      _ ≤ 1.15e9 * (P ^ 5 * g) := mul_le_mul_of_nonneg_right (by norm_num) hP5
  rw [abs_mul, abs_of_nonneg hU]
  calc epf_U p Np Nm * |s * x - D1 + D3 / 3|
      ≤ epf_U p Np Nm * (1.15e9 * (P ^ 5 * g)) := mul_le_mul_of_nonneg_left htot hU
    _ = 1.15e9 * (p : ℝ) ^ 5 * a ^ 5 * (epf_U p Np Nm * g ^ 6) := by rw [hP]; ring

end Fibre

end BiluLinial.Tight.SecA
