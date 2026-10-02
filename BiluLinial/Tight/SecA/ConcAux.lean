/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecA.TransRel
public import BiluLinial.Tight.SecA.Star
public import BiluLinial.Tight.Compare.Symm

/-!
# Endpoint and sup majorants for the bias and the whitening step (sub-nodes of `A-C1a`,
`A-WHITEN`)

Source lines 322–361, 369–392, 413–424; AUDIT-A §2.4, §2.6, §2.9, §2.11. All names live in
`SecA.CA` or carry distinctive names in `CapPoint` (no clash with `SecA/Star*`).

* Star level: `f1Obs = clipObs (quadFn (tr A) 0 (-A)) (p-1) p`, `wΦ = clipObs (quadFn w 0 0) p p`;
  the majorant conditions `quadMaj_one_sub` (for `1 - q_A` at an interior point, scale `α`),
  `quadMaj_trace_sup` (E5 for `tr A - q_A`, scale `1 + tr A`, weights `√(A_ii + B_ii)`),
  `quadMaj_const'`, `QuadMaj.mono'`; `clip_package` (A-SMOOTH, A-E5, A-CLIP0 for exponents in
  `(N, p]`) and `endpoint_package` (A-MAJ at an interior point with weights `5pλ_i`).
* Graph level (F1 from `SecA.precN_schur`): `root_F1'` (`α t = 1`, `(Aξ)_j t = -τ a G_vj`,
  `A_ii t = a²(G_vvG_ii - G_vi²)`, `t = D_v h_v`), `root_star_bounds'`, `branch_maj`.
* Capped point: weights `endLam = a(2√(G⁺_vvG⁺_ii) + 2√(G⁻_vvG⁻_ii))` with `endLam_maj` (the
  majorant conditions at the own signs) and `endLam_moment` (`E(5pλ_i)ⁿ ≤ (41pa)ⁿ`); root traces
  `trace_root_le`, `E_trace_pow_le`, `coreE_trace_pow_le` (`≤ (1+2ε)ⁿ`, via
  `wavg_pow_le_of_le_avg`); `RegA.endL_facts` (`dL² ≥ 2`, `dL⁴ ≤ 41⁴p⁴/(4d) ≤ 1/2`).
* `CapPoint.bias_gen` (`A-C1a` for one branch `(P, Q) = (A, B)` or `(B, A)`, constant `10⁸`):
  `A-TRANSR` with `F = f₁`, sup majorant `1 + tr P`, endpoint majorant `(1 + tr P)·2H`
  (`H = h_v`, `1/α_P = D_v h_v ≤ 2 h_v`), `m = ϑ = 13`, `B = 5`, `K = 1`.
* `CapPoint.whiten_gen` (`A-WHITEN` for one branch, before T.COV): `A-INS`/`A-RET` with
  `R = wΦ`, then `A-TRANSR` with `F = wΦ`, `m = E w + ϑ`, `ϑ = d^{-10}`, `B = 2`,
  `K = ⌊log d/300⌋` (`RegA.whitenK_facts`: `ϑ^{-1/K} 2^{1/K} ≤ 2e^{12000}`), constant
  `3·10⁶ e^{12002}` (`whiten_arith`).

Checks (rule 2): `N = ∅` (all retained sums empty, `tr A = 0`, `w = 0`); `y_v = 0` (`A = 0`,
`α = 1`, every endpoint bound is `0 ≤ …`); the constants are absolute (`∃ C` before `d, p`).
-/

@[expose] public section

universe u

namespace BiluLinial.Tight.SecA.CA

open Matrix
open scoped ContDiff

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem qForm_neg (A : Matrix ι ι ℝ) (x : ι → ℝ) : qForm (-A) x = -qForm A x := by
  simp [qForm, Matrix.neg_mulVec, dotProduct_neg]

omit [DecidableEq ι] in
theorem f1Obs_eq_clipObs (p : ℕ) (A B : Matrix ι ι ℝ) :
    f1Obs p A B = clipObs (quadFn A.trace 0 (-A)) (p - 1) p A B := by
  funext x
  simp only [f1Obs, clipObs, quadFn, zero_dotProduct, add_zero, qForm_neg]
  ring

omit [DecidableEq ι] in
theorem mul_starPhi_eq_clipObs (p : ℕ) (c : ℝ) (A B : Matrix ι ι ℝ) :
    (fun x => c * starPhi p A B x) = clipObs (quadFn c 0 0) p p A B := by
  funext x
  simp only [starPhi, clipObs, quadFn, zero_dotProduct, add_zero, qForm, zero_mulVec,
    dotProduct_zero]
  ring

omit [DecidableEq ι] in
theorem contDiff_quadFn' (c : ℝ) (ℓ : ι → ℝ) (Q : Matrix ι ι ℝ) :
    ContDiff ℝ ∞ (quadFn c ℓ Q) := by
  unfold quadFn qForm
  simp only [dotProduct, mulVec]
  fun_prop

omit [Fintype ι] [DecidableEq ι] in
theorem psd_symm {A : Matrix ι ι ℝ} (hA : A.PosSemidef) (i k : ι) : A i k = A k i := by
  simpa using (hA.isHermitian.apply i k).symm

omit [Fintype ι] [DecidableEq ι] in
/-- Off-diagonal entries of a PSD matrix: `A_ik² ≤ A_ii A_kk`. -/
theorem psd_apply_sq_le' {A : Matrix ι ι ℝ} (hA : A.PosSemidef) (i k : ι) :
    A i k ^ 2 ≤ A i i * A k k := by
  have h2 := (hA.submatrix ![i, k]).det_nonneg
  rw [Matrix.det_fin_two] at h2
  simp only [Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at h2
  rw [psd_symm hA k i] at h2
  nlinarith

/-- Cauchy–Schwarz for a PSD form: `(Ax)_i² ≤ A_ii q_A(x)`. -/
theorem mulVec_apply_sq_le' {A : Matrix ι ι ℝ} (hA : A.PosSemidef) (x : ι → ℝ) (i : ι) :
    (A *ᵥ x) i ^ 2 ≤ A i i * qForm A x := by
  have hline : ∀ t : ℝ, qForm A (x + t • Pi.single i 1) =
      qForm A x + 2 * t * (A *ᵥ x) i + t ^ 2 * A i i := by
    intro t
    have hcol : A *ᵥ Pi.single i 1 = fun k => A k i := by
      funext k
      simp [mulVec, dotProduct, Pi.single_apply]
    have hs : x ⬝ᵥ (A *ᵥ Pi.single i 1) = (A *ᵥ x) i := by
      rw [hcol]
      simp only [mulVec, dotProduct]
      exact Finset.sum_congr rfl fun k _ => by rw [psd_symm hA k i, mul_comm]
    have hs2 : Pi.single i 1 ⬝ᵥ (A *ᵥ Pi.single i 1) = A i i := by
      rw [hcol, single_one_dotProduct]
    simp only [qForm, mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
      smul_dotProduct, single_one_dotProduct, hs, hs2, smul_eq_mul]
    ring
  have h : ∀ t : ℝ, 0 ≤ A i i * (t * t) + 2 * (A *ᵥ x) i * t + qForm A x := by
    intro t
    have h0 := qForm_nonneg hA (x + t • Pi.single i 1)
    rw [hline] at h0
    linarith [h0]
  have hd := discrim_le_zero h
  rw [discrim] at hd
  nlinarith [hd]

omit [DecidableEq ι] in
/-- A constant prefactor satisfies the majorant condition with scale `m ≥ |c|`. -/
theorem quadMaj_const' {c m : ℝ} (hc : |c| ≤ m) {lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i)
    (x : ι → ℝ) : QuadMaj c 0 0 x m lam := by
  have hm : 0 ≤ m := (abs_nonneg c).trans hc
  refine ⟨?_, fun i => ?_, fun i j => ?_⟩
  · simpa [quadFn, qForm] using hc
  · simp only [Pi.zero_apply, add_zero, transpose_zero, zero_mulVec, abs_zero]
    exact mul_nonneg (mul_nonneg zero_le_two hm) (hlam i)
  · simp only [Matrix.zero_apply, add_zero, abs_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg zero_le_two hm) (hlam i)) (hlam j)

omit [DecidableEq ι] in
/-- The majorant condition for `1 - q_A` at `ξ` with scale `α = 1 - q_A(ξ)`. -/
theorem quadMaj_one_sub {A : Matrix ι ι ℝ} (hAs : ∀ i k, A i k = A k i) {ξ : ι → ℝ}
    {lam : ι → ℝ} (hα : 0 < 1 - qForm A ξ) (h1 : ∀ i, |(A *ᵥ ξ) i| ≤ (1 - qForm A ξ) * lam i)
    (h2 : ∀ i k, |A i k| ≤ (1 - qForm A ξ) * lam i * lam k) :
    QuadMaj 1 0 (-A) ξ (1 - qForm A ξ) lam := by
  have hT : (-A + (-A)ᵀ) *ᵥ ξ = (-2 : ℝ) • (A *ᵥ ξ) := by
    have e : -A + (-A)ᵀ = (-2 : ℝ) • A := by
      ext i k
      simp only [Matrix.add_apply, Matrix.neg_apply, Matrix.transpose_apply, Matrix.smul_apply,
        smul_eq_mul, hAs k i]
      ring
    rw [e, Matrix.smul_mulVec]
  refine ⟨?_, fun i => ?_, fun i k => ?_⟩
  · have e : quadFn 1 0 (-A) ξ = 1 - qForm A ξ := by
      simp only [quadFn, qForm, zero_dotProduct, Matrix.neg_mulVec, dotProduct_neg]
      ring
    rw [e, abs_of_pos hα]
  · rw [hT]
    simp only [Pi.zero_apply, zero_add, Pi.smul_apply, smul_eq_mul, abs_mul]
    norm_num
    linarith [h1 i]
  · simp only [Matrix.neg_apply, hAs k i]
    rw [show -A i k + -A i k = -(2 * A i k) by ring, abs_neg, abs_mul, abs_two]
    linarith [h2 i k]

omit [DecidableEq ι] in
/-- Raising the scale of a majorant condition (the linear and quadratic parts are unchanged). -/
theorem QuadMaj.mono' {c c' m m' : ℝ} {ℓ : ι → ℝ} {Q : Matrix ι ι ℝ} {x : ι → ℝ}
    {lam : ι → ℝ} (h : QuadMaj c ℓ Q x m lam) (hlam : ∀ i, 0 ≤ lam i) (hm : m ≤ m')
    (h0 : |quadFn c' ℓ Q x| ≤ m') : QuadMaj c' ℓ Q x m' lam :=
  ⟨h0, fun i => (h.h1 i).trans (by nlinarith [hlam i]),
    fun i j => (h.h2 i j).trans (by nlinarith [mul_nonneg (hlam i) (hlam j)])⟩

/-- The sup majorant condition (E5) for `tr A - q_A` with scale `1 + tr A`, weights
`√(A_ii + B_ii)`, on `{q_A < 1}`. -/
theorem quadMaj_trace_sup {A B : Matrix ι ι ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    {x : ι → ℝ} (hx : qForm A x < 1) :
    QuadMaj A.trace 0 (-A) x (1 + A.trace) fun i => Real.sqrt (A i i + B i i) := by
  have htr := hA.trace_nonneg
  have hq := qForm_nonneg hA x
  have hAs := psd_symm hA
  have hT : (-A + (-A)ᵀ) *ᵥ x = (-2 : ℝ) • (A *ᵥ x) := by
    have e : -A + (-A)ᵀ = (-2 : ℝ) • A := by
      ext i k
      simp only [Matrix.add_apply, Matrix.neg_apply, Matrix.transpose_apply, Matrix.smul_apply,
        smul_eq_mul, hAs k i]
      ring
    rw [e, Matrix.smul_mulVec]
  have hsq : ∀ i, Real.sqrt (A i i) ≤ Real.sqrt (A i i + B i i) := fun i =>
    Real.sqrt_le_sqrt (by linarith [hB.diag_nonneg (i := i)])
  refine ⟨?_, fun i => ?_, fun i k => ?_⟩
  · have e : quadFn A.trace 0 (-A) x = A.trace - qForm A x := by
      simp only [quadFn, zero_dotProduct, add_zero, qForm_neg]
      ring
    rw [e, abs_le]
    constructor <;> linarith
  · rw [hT]
    simp only [Pi.zero_apply, zero_add, Pi.smul_apply, smul_eq_mul, abs_mul]
    have h1 : |(A *ᵥ x) i| ≤ Real.sqrt (A i i) := by
      have := mulVec_apply_sq_le' hA x i
      have hAi := hA.diag_nonneg (i := i)
      exact Real.abs_le_sqrt (by nlinarith)
    have hs0 := Real.sqrt_nonneg (A i i + B i i)
    norm_num
    nlinarith [hsq i]
  · simp only [Matrix.neg_apply, hAs k i]
    rw [show -A i k + -A i k = -(2 * A i k) by ring, abs_neg, abs_mul, abs_two]
    have h1 : |A i k| ≤ Real.sqrt (A i i) * Real.sqrt (A k k) := by
      rw [← Real.sqrt_mul (hA.diag_nonneg)]
      exact Real.abs_le_sqrt (psd_apply_sq_le' hA i k)
    have h2 : Real.sqrt (A i i) * Real.sqrt (A k k) ≤
        Real.sqrt (A i i + B i i) * Real.sqrt (A k k + B k k) :=
      mul_le_mul (hsq i) (hsq k) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have h3 := mul_nonneg (Real.sqrt_nonneg (A i i + B i i)) (Real.sqrt_nonneg (A k k + B k k))
    nlinarith

omit [DecidableEq ι] in
theorem length_dEvenList_univ' (j : ι → ℕ) :
    (dEvenList (Finset.univ : Finset ι).toList j).length = 2 * ∑ i, j i := by
  rw [length_dEvenList, Finset.sum_map_toList, Finset.mul_sum]

omit [Fintype ι] [DecidableEq ι] in
theorem prod_map_dEvenList' (l : List ι) (j : ι → ℕ) (f : ι → ℝ) :
    ((dEvenList l j).map f).prod = (l.map fun x => f x ^ (2 * j x)).prod := by
  induction l with
  | nil => simp [dEvenList]
  | cons y l ih =>
    simp only [dEvenList, List.flatMap_cons, List.map_append, List.prod_append,
      List.map_replicate, List.prod_replicate, List.map_cons, List.prod_cons] at ih ⊢
    rw [ih]

omit [DecidableEq ι] in
theorem prod_map_dEvenList_univ' (j : ι → ℕ) (f : ι → ℝ) :
    ((dEvenList (Finset.univ : Finset ι).toList j).map f).prod = ∏ i, f i ^ (2 * j i) := by
  rw [prod_map_dEvenList']
  exact Finset.prod_map_toList _ (fun i => f i ^ (2 * j i))

/-- The clip package (`A-SMOOTH`, `A-E5`, `A-CLIP0`) for a clipped observable with exponents
`e₁, e₂ ∈ [N + 1, p]` and a sup majorant of scale `m`. -/
theorem clip_package {A B : Matrix ι ι ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    {e₁ e₂ p N : ℕ} (he₁ : N < e₁) (he₂ : N < e₂) (he₁p : e₁ ≤ p) (he₂p : e₂ ≤ p) (hp : 2 ≤ p)
    {c : ℝ} {ℓ : ι → ℝ} {Q : Matrix ι ι ℝ} {m : ℝ}
    (hg : ∀ x, qForm A x < 1 → qForm B x < 1 →
      QuadMaj c ℓ Q x m fun i => Real.sqrt (A i i + B i i)) :
    SmoothBdd N (clipObs (quadFn c ℓ Q) e₁ e₂ A B) ∧
    (∀ j : ι → ℕ, 2 * ∑ i, j i ≤ N → ∀ x,
      |dEven (Finset.univ : Finset ι).toList j (clipObs (quadFn c ℓ Q) e₁ e₂ A B) x| ≤
        m * (5 * (p : ℝ)) ^ (2 * ∑ i, j i) * ∏ i, (A i i + B i i) ^ j i) ∧
    (∀ j : ι → ℕ, 2 * ∑ i, j i ≤ N → ∀ x, (1 ≤ qForm A x ∨ 1 ≤ qForm B x) →
      dEven (Finset.univ : Finset ι).toList j (clipObs (quadFn c ℓ Q) e₁ e₂ A B) x = 0) := by
  refine ⟨smoothBdd_clipObs hA hB hg (lt_min he₁ he₂), fun j hj x => ?_, fun j hj x hx => ?_⟩
  · have hlen := length_dEvenList_univ' j
    have h := pderivList_clipObs_le hA hB hg (dEvenList (Finset.univ : Finset ι).toList j)
      (by rw [hlen]; exact lt_of_le_of_lt hj (lt_min he₁ he₂)) x
    rw [hlen, prod_map_dEvenList_univ'] at h
    rw [dEven_eq_pderivList]
    refine h.trans ?_
    have hm : 0 ≤ m := by
      have := (abs_nonneg _).trans h
      have hP : 0 ≤ ∏ i, Real.sqrt (A i i + B i i) ^ (2 * j i) :=
        Finset.prod_nonneg fun i _ => pow_nonneg (Real.sqrt_nonneg _) _
      have hK : 0 < (2 * (1 + e₁ + e₂ : ℝ)) ^ (2 * ∑ i, j i) := by positivity
      by_contra hneg
      push Not at hneg
      rcases hP.eq_or_lt with h0 | h0
      · -- the product vanishes: the bound is trivially `0`
        have : m * (2 * (1 + e₁ + e₂ : ℝ)) ^ (2 * ∑ i, j i) *
            ∏ i, Real.sqrt (A i i + B i i) ^ (2 * j i) = 0 := by rw [← h0]; ring
        exact absurd (hg 0 (by simp [qForm]) (by simp [qForm])).h0 (by
          intro h'
          linarith [abs_nonneg (quadFn c ℓ Q 0)])
      · have := mul_pos hK h0
        nlinarith
    have hprod : ∏ i, Real.sqrt (A i i + B i i) ^ (2 * j i) = ∏ i, (A i i + B i i) ^ j i :=
      Finset.prod_congr rfl fun i _ => by
        rw [pow_mul, Real.sq_sqrt (add_nonneg hA.diag_nonneg hB.diag_nonneg)]
    rw [hprod]
    have hbase : 2 * (1 + (e₁ : ℝ) + e₂) ≤ 5 * p := by
      have h1 : (e₁ : ℝ) ≤ p := by exact_mod_cast he₁p
      have h2 : (e₂ : ℝ) ≤ p := by exact_mod_cast he₂p
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
      linarith
    have hb0 : 0 ≤ ∏ i, (A i i + B i i) ^ j i :=
      Finset.prod_nonneg fun i _ => pow_nonneg (add_nonneg hA.diag_nonneg hB.diag_nonneg) _
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hbase _) hm) hb0
  · rw [dEven_eq_pderivList]
    exact pderivList_clipObs_eq_zero hA hB (contDiff_quadFn' c ℓ Q) _
      (by rw [length_dEvenList_univ']; exact lt_of_le_of_lt hj (lt_min he₁ he₂)) hx

/-- The endpoint package (`A-MAJ` at an interior point): with weights `λ` satisfying the majorant
conditions for `1 - q_A` (scale `α`) and `1 - q_B` (scale `β`), and the prefactor majorant of
scale `m_g`, `|∂^{2j} F(ξ)| ≤ m_g α^{e₁} β^{e₂} Π (5pλ_i)^{2j_i}`. -/
theorem endpoint_package {A B : Matrix ι ι ℝ} (hAs : ∀ i k, A i k = A k i)
    (hBs : ∀ i k, B i k = B k i) {e₁ e₂ p : ℕ} (he₁p : e₁ ≤ p) (he₂p : e₂ ≤ p) (hp : 2 ≤ p)
    {c : ℝ} {ℓ : ι → ℝ} {Q : Matrix ι ι ℝ} {ξ : ι → ℝ} (hα : 0 < 1 - qForm A ξ)
    (hβ : 0 < 1 - qForm B ξ) {lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i)
    (hA1 : ∀ i, |(A *ᵥ ξ) i| ≤ (1 - qForm A ξ) * lam i)
    (hA2 : ∀ i k, |A i k| ≤ (1 - qForm A ξ) * lam i * lam k)
    (hB1 : ∀ i, |(B *ᵥ ξ) i| ≤ (1 - qForm B ξ) * lam i)
    (hB2 : ∀ i k, |B i k| ≤ (1 - qForm B ξ) * lam i * lam k) {mg : ℝ}
    (hg : QuadMaj c ℓ Q ξ mg lam) (j : ι → ℕ) :
    |dEven (Finset.univ : Finset ι).toList j (clipObs (quadFn c ℓ Q) e₁ e₂ A B) ξ| ≤
      mg * (1 - qForm A ξ) ^ e₁ * (1 - qForm B ξ) ^ e₂ *
        ∏ i, (5 * (p : ℝ) * lam i) ^ (2 * j i) := by
  have h := pderivList_clipObs_le_of_interior (e₁ := e₁) (e₂ := e₂)
    (by linarith : qForm A ξ < 1) (by linarith : qForm B ξ < 1) hlam hg
    (quadMaj_one_sub hAs hα hA1 hA2) (quadMaj_one_sub hBs hβ hB1 hB2)
    (dEvenList (Finset.univ : Finset ι).toList j)
  rw [length_dEvenList_univ', prod_map_dEvenList_univ'] at h
  rw [dEven_eq_pderivList]
  refine h.trans ?_
  have hmg : 0 ≤ mg := (abs_nonneg _).trans hg.h0
  have hbase : 2 * (1 + (e₁ : ℝ) + e₂) ≤ 5 * p := by
    have h1 : (e₁ : ℝ) ≤ p := by exact_mod_cast he₁p
    have h2 : (e₂ : ℝ) ≤ p := by exact_mod_cast he₂p
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have hprod : (5 * (p : ℝ)) ^ (2 * ∑ i, j i) * ∏ i, lam i ^ (2 * j i) =
      ∏ i, (5 * (p : ℝ) * lam i) ^ (2 * j i) := by
    rw [Finset.mul_sum, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => (mul_pow _ _ _).symm
  have hK : 0 ≤ mg * (1 - qForm A ξ) ^ e₁ * (1 - qForm B ξ) ^ e₂ :=
    mul_nonneg (mul_nonneg hmg (pow_nonneg hα.le _)) (pow_nonneg hβ.le _)
  have hL : 0 ≤ ∏ i, lam i ^ (2 * j i) := Finset.prod_nonneg fun i _ => pow_nonneg (hlam i) _
  calc mg * (1 - qForm A ξ) ^ e₁ * (1 - qForm B ξ) ^ e₂ *
        (2 * (1 + (e₁ : ℝ) + e₂)) ^ (2 * ∑ i, j i) * ∏ i, lam i ^ (2 * j i)
      = mg * (1 - qForm A ξ) ^ e₁ * (1 - qForm B ξ) ^ e₂ *
          ((2 * (1 + (e₁ : ℝ) + e₂)) ^ (2 * ∑ i, j i) * ∏ i, lam i ^ (2 * j i)) := by ring
    _ ≤ mg * (1 - qForm A ξ) ^ e₁ * (1 - qForm B ξ) ^ e₂ *
          ((5 * (p : ℝ)) ^ (2 * ∑ i, j i) * ∏ i, lam i ^ (2 * j i)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hbase _) hL) hK
    _ = _ := by rw [hprod]

end BiluLinial.Tight.SecA.CA

namespace BiluLinial.Tight.SecA.CA

open Matrix

section Graph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- (F1) for one branch at a good precision (`P̃ ≻ 0`, `τ² = 1`), with `t = D_v h_v`:
`(1 - q_A(ξ)) t = 1`, `(Aξ)_j t = -τ a G_vj` and `A_ii t = a² (G_vv G_ii - G_vi²)`. -/
theorem root_F1' {a τ : ℝ} (hτ : τ ^ 2 = 1) {y : V → ℝ} (hy : ∀ i, 0 ≤ y i) {σ : Config V}
    {S : Finset V} {v : V} (hv : v ∈ S) (hP : (precN G a τ y σ S).PosDef) :
    (1 - qForm (rootMat G a τ y σ S v) (rootSigns G σ S v)) *
        (diagD G a y S v * hN G a τ y σ S v) = 1 ∧
      (∀ j : nbhd G S v, (rootMat G a τ y σ S v *ᵥ rootSigns G σ S v) j *
        (diagD G a y S v * hN G a τ y σ S v) = -(τ * a) * greenP G a τ y σ S v j) ∧
      (∀ i : nbhd G S v, rootMat G a τ y σ S v i i * (diagD G a y S v * hN G a τ y σ S v) =
        a ^ 2 * (greenP G a τ y σ S v v * greenP G a τ y σ S i i -
          greenP G a τ y σ S v i ^ 2)) := by
  obtain ⟨hd, hrow, hij⟩ := precN_schur G hv hP
  have hD : diagD G a y S v ≠ 0 :=
    (lt_of_lt_of_le one_pos (FloorIns.one_le_diagD G a hy S v)).ne'
  obtain ⟨g, hg⟩ : ∃ g, g = (precN G a τ y σ S)⁻¹ v v := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K, K = (precCore G a τ y σ S v)⁻¹ := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u, u = K *ᵥ incCol G a τ y σ S v := ⟨_, rfl⟩
  have hh : hN G a τ y σ S v = g := by rw [hg]; rfl
  rw [← hK, ← hu, ← hg] at hd
  refine ⟨?_, fun j => ?_, fun i => ?_⟩
  · have hq : qForm (rootMat G a τ y σ S v) (rootSigns G σ S v) =
        incCol G a τ y σ S v ⬝ᵥ u / diagD G a y S v := by
      rw [← qRoot_eq_qForm G hτ hy σ hv, qRoot, ← hK, ← hu]
    rw [hq, hh]
    field_simp
    linear_combination hd
  · -- the row identity
    have hjv : (j : V) ≠ v := (G.ne_of_adj (Finset.mem_filter.1 j.2).2).symm
    obtain ⟨m, hm⟩ : ∃ m, m = ∑ i : nbhd G S v,
        (precCore G a τ y σ S v)⁻¹ j i * (Real.sqrt (y i) * sgn σ v i) := ⟨_, rfl⟩
    have hu' : u j = τ * a * Real.sqrt (y v) * m := by
      rw [hu, hK, hm]
      simp only [mulVec, dotProduct, incCol_eq_ite G a τ y σ hv, mul_ite, mul_zero,
        Finset.sum_ite_mem, Finset.univ_inter]
      rw [← Finset.sum_coe_sort (nbhd G S v), Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hA : (rootMat G a τ y σ S v *ᵥ rootSigns G σ S v) j =
        a ^ 2 * y v / diagD G a y S v * Real.sqrt (y j) * m := by
      rw [hm]
      simp only [mulVec, dotProduct, rootMat, coreGreen, of_apply, rootSigns, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hG : greenP G a τ y σ S v j =
        -(Real.sqrt (y v) * (g * (τ * a * Real.sqrt (y v) * m)) * Real.sqrt (y j)) := by
      simp only [greenP]
      rw [hrow j hjv, ← hK, ← hu, hu', ← hg]
      ring
    have hyv := Real.mul_self_sqrt (hy v)
    rw [hA, hG, hh]
    calc a ^ 2 * y v / diagD G a y S v * Real.sqrt (y j) * m * (diagD G a y S v * g) =
          (a ^ 2 * y v / diagD G a y S v * diagD G a y S v) * (Real.sqrt (y j) * m * g) := by
          ring
      _ = a ^ 2 * y v * (Real.sqrt (y j) * m * g) := by rw [div_mul_cancel₀ _ hD]
      _ = _ := by
          linear_combination (-(a ^ 2 * g * m * Real.sqrt (y j))) * hyv +
            (-(a ^ 2 * g * m * Real.sqrt (y j) * (Real.sqrt (y v) * Real.sqrt (y v)))) * hτ
  · -- the diagonal identity
    have hiv : (i : V) ≠ v := (G.ne_of_adj (Finset.mem_filter.1 i.2).2).symm
    have hyv := Real.mul_self_sqrt (hy v)
    have hyi := Real.mul_self_sqrt (hy i)
    have hterm : greenP G a τ y σ S v v * greenP G a τ y σ S i i -
        greenP G a τ y σ S v i ^ 2 = g * y v * (y i * K i i) := by
      simp only [greenP]
      rw [hij i i hiv hiv, hrow i hiv, ← hg, ← hK, ← hu]
      linear_combination (g * (Real.sqrt (y i) * Real.sqrt (y i)) * K i i) * hyv +
        (g * y v * K i i) * hyi
    have hAi : rootMat G a τ y σ S v i i = a ^ 2 * y v / diagD G a y S v * (y i * K i i) := by
      simp only [rootMat, coreGreen, of_apply, ← hK]
      linear_combination (a ^ 2 * y v / diagD G a y S v * K i i) * hyi
    rw [hterm, hAi, hh]
    field_simp

/-- Star bounds for one branch at a good precision: with `α = 1 - q_A(ξ)`,
`α > 0`, `|(Aξ)_i| ≤ α a √(G_vvG_ii)`, `A_ii ≤ α a² G_vvG_ii` and `G_vvG_ii ≥ 0`. -/
theorem root_star_bounds' {a τ : ℝ} (ha : 0 < a) (hτ : τ ^ 2 = 1) {y : V → ℝ}
    (hy : ∀ i, 0 ≤ y i) {σ : Config V} {S : Finset V} {v : V} (hv : v ∈ S)
    (hP : (precN G a τ y σ S).PosDef) (hA : (rootMat G a τ y σ S v).PosSemidef)
    (i : nbhd G S v) :
    0 < 1 - qForm (rootMat G a τ y σ S v) (rootSigns G σ S v) ∧
    |(rootMat G a τ y σ S v *ᵥ rootSigns G σ S v) i| ≤
      (1 - qForm (rootMat G a τ y σ S v) (rootSigns G σ S v)) *
        (a * Real.sqrt (greenP G a τ y σ S v v * greenP G a τ y σ S i i)) ∧
    rootMat G a τ y σ S v i i ≤ (1 - qForm (rootMat G a τ y σ S v) (rootSigns G σ S v)) *
        (a ^ 2 * (greenP G a τ y σ S v v * greenP G a τ y σ S i i)) ∧
    0 ≤ greenP G a τ y σ S v v * greenP G a τ y σ S i i := by
  obtain ⟨h1, h2, h3⟩ := root_F1' G hτ hy hv hP
  have hD1 := FloorIns.one_le_diagD G a hy S v
  have hg : 0 < hN G a τ y σ S v := hP.inv.diag_pos
  set t := diagD G a y S v * hN G a τ y σ S v with ht
  have ht0 : 0 < t := mul_pos (by linarith) hg
  set α := 1 - qForm (rootMat G a τ y σ S v) (rootSigns G σ S v) with hα
  have hα0 : 0 < α := by
    by_contra hc
    push Not at hc
    nlinarith
  have hαt : α = 1 / t := by rw [eq_div_iff ht0.ne']; exact h1
  have hAii : 0 ≤ rootMat G a τ y σ S v i i := hA.diag_nonneg
  have hd := h3 i
  have hG0 : greenP G a τ y σ S v i ^ 2 ≤
      greenP G a τ y σ S v v * greenP G a τ y σ S i i := by
    have := mul_nonneg hAii ht0.le
    have ha2 := pow_pos ha 2
    by_contra hc
    push Not at hc
    nlinarith
  have hGG : 0 ≤ greenP G a τ y σ S v v * greenP G a τ y σ S i i :=
    le_trans (sq_nonneg _) hG0
  refine ⟨hα0, ?_, ?_, hGG⟩
  · have hr := h2 i
    have hτa : |τ| = 1 := by
      have : |τ| ^ 2 = 1 := by rw [sq_abs]; exact hτ
      nlinarith [abs_nonneg τ]
    have e : (rootMat G a τ y σ S v *ᵥ rootSigns G σ S v) i =
        -(τ * a) * greenP G a τ y σ S v i * α := by
      rw [hαt]
      field_simp
      linarith
    rw [e, abs_mul, abs_mul, abs_neg, abs_mul, hτa, abs_of_pos ha, abs_of_pos hα0, one_mul]
    have hgi : |greenP G a τ y σ S v i| ≤
        Real.sqrt (greenP G a τ y σ S v v * greenP G a τ y σ S i i) := Real.abs_le_sqrt hG0
    nlinarith [mul_le_mul_of_nonneg_left hgi (mul_pos ha hα0).le]
  · have e : rootMat G a τ y σ S v i i = α * (a ^ 2 * (greenP G a τ y σ S v v *
        greenP G a τ y σ S i i - greenP G a τ y σ S v i ^ 2)) := by
      rw [hαt]
      field_simp
      linarith
    rw [e]
    have := sq_nonneg (greenP G a τ y σ S v i)
    have ha2 := pow_pos ha 2
    nlinarith [mul_pos hα0 ha2]

end Graph

end BiluLinial.Tight.SecA.CA


namespace BiluLinial.Tight.SecA.CA

open Matrix

section Graph2

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The majorant conditions of `A-MAJ` for one branch at a good precision, for any weights
`λ_i ≥ a √(G_vvG_ii)`. -/
theorem branch_maj {a τ : ℝ} (ha : 0 < a) (hτ : τ ^ 2 = 1) {y : V → ℝ} (hy : ∀ i, 0 ≤ y i)
    {σ : Config V} {S : Finset V} {v : V} (hv : v ∈ S) (hP : (precN G a τ y σ S).PosDef)
    (hA : (rootMat G a τ y σ S v).PosSemidef) (lam : nbhd G S v → ℝ) (hlam0 : ∀ i, 0 ≤ lam i)
    (hlam : ∀ i : nbhd G S v,
      a * Real.sqrt (greenP G a τ y σ S v v * greenP G a τ y σ S i i) ≤ lam i) :
    0 < 1 - qForm (rootMat G a τ y σ S v) (rootSigns G σ S v) ∧
    (∀ i, |(rootMat G a τ y σ S v *ᵥ rootSigns G σ S v) i| ≤
      (1 - qForm (rootMat G a τ y σ S v) (rootSigns G σ S v)) * lam i) ∧
    (∀ i k, |rootMat G a τ y σ S v i k| ≤
      (1 - qForm (rootMat G a τ y σ S v) (rootSigns G σ S v)) * lam i * lam k) := by
  have hrs := root_star_bounds' G ha hτ hy hv hP hA
  obtain ⟨h1, -, -⟩ := root_F1' G hτ hy hv hP
  have hD1 := FloorIns.one_le_diagD G a hy S v
  have hg : 0 < hN G a τ y σ S v := hP.inv.diag_pos
  have ht0 : 0 < diagD G a y S v * hN G a τ y σ S v := mul_pos (by linarith) hg
  set α := 1 - qForm (rootMat G a τ y σ S v) (rootSigns G σ S v) with hαdef
  have hα0 : 0 < α := by
    by_contra hc
    push Not at hc
    nlinarith
  refine ⟨hα0, fun i => ?_, fun i k => ?_⟩
  · obtain ⟨-, h1, -, -⟩ := hrs i
    exact h1.trans (mul_le_mul_of_nonneg_left (hlam i) hα0.le)
  · obtain ⟨-, -, hi, hGi⟩ := hrs i
    obtain ⟨-, -, hk, hGk⟩ := hrs k
    have hsq := psd_apply_sq_le' hA i k
    have hAk : 0 ≤ rootMat G a τ y σ S v k k := hA.diag_nonneg
    set gi := Real.sqrt (greenP G a τ y σ S v v * greenP G a τ y σ S i i) with hgidef
    set gk := Real.sqrt (greenP G a τ y σ S v v * greenP G a τ y σ S k k) with hgkdef
    have hgi2 : gi ^ 2 = greenP G a τ y σ S v v * greenP G a τ y σ S i i := Real.sq_sqrt hGi
    have hgk2 : gk ^ 2 = greenP G a τ y σ S v v * greenP G a τ y σ S k k := Real.sq_sqrt hGk
    have hgi0 : 0 ≤ gi := Real.sqrt_nonneg _
    have hgk0 : 0 ≤ gk := Real.sqrt_nonneg _
    have hprod : rootMat G a τ y σ S v i i * rootMat G a τ y σ S v k k ≤
        (α * (a * gi) * (a * gk)) ^ 2 := by
      calc rootMat G a τ y σ S v i i * rootMat G a τ y σ S v k k
          ≤ (α * (a ^ 2 * (greenP G a τ y σ S v v * greenP G a τ y σ S i i))) *
              (α * (a ^ 2 * (greenP G a τ y σ S v v * greenP G a τ y σ S k k))) :=
            mul_le_mul hi hk hAk (mul_nonneg hα0.le (mul_nonneg (sq_nonneg _) hGi))
        _ = (α * (a * gi) * (a * gk)) ^ 2 := by rw [← hgi2, ← hgk2]; ring
    have h0 : 0 ≤ α * (a * gi) * (a * gk) :=
      mul_nonneg (mul_nonneg hα0.le (mul_nonneg ha.le hgi0)) (mul_nonneg ha.le hgk0)
    calc |rootMat G a τ y σ S v i k|
        ≤ Real.sqrt ((α * (a * gi) * (a * gk)) ^ 2) := Real.abs_le_sqrt (hsq.trans hprod)
      _ = α * (a * gi) * (a * gk) := Real.sqrt_sq h0
      _ ≤ α * lam i * lam k :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hlam i) hα0.le) (hlam k)
            (mul_nonneg ha.le hgk0) (mul_nonneg hα0.le (hlam0 i))

/-- `2√(xy) ≤ x + y` for `x, y ≥ 0`. -/
theorem two_sqrt_mul_le' {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    2 * Real.sqrt (x * y) ≤ x + y := by
  have h : Real.sqrt (x * y) ≤ (x + y) / 2 := by
    rw [Real.sqrt_le_iff]
    exact ⟨by linarith, by nlinarith [sq_nonneg (x - y)]⟩
  linarith

end Graph2

/-- A trace-type bound in a weighted average: if `0 ≤ T ≤ (1/D) Σ_i H_i` on the support, with
`|ι| ≤ D` and `E H_iⁿ ≤ cⁿ`, then `E Tⁿ ≤ cⁿ`. -/
theorem wavg_pow_le_of_le_avg {Ω ι : Type*} [Fintype Ω] [Fintype ι] {w : Ω → ℝ}
    (hw : ∀ ω, 0 ≤ w ω) (_hW : 0 < ∑ ω, w ω) (T : Ω → ℝ) (H : ι → Ω → ℝ) {D c : ℝ} (hD : 0 < D)
    (hcard : (Fintype.card ι : ℝ) ≤ D) (hc : 0 ≤ c) {n : ℕ} (hn : 1 ≤ n)
    (hT : ∀ ω, 0 < w ω → 0 ≤ T ω ∧ T ω ≤ (1 / D) * ∑ i, H i ω)
    (hH0 : ∀ ω, 0 < w ω → ∀ i, 0 ≤ H i ω)
    (hmom : ∀ i, wavg w (fun ω => H i ω ^ n) ≤ c ^ n) :
    wavg w (fun ω => T ω ^ n) ≤ c ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hcd : (Fintype.card ι : ℝ) / D ≤ 1 := (div_le_one hD).2 hcard
  have hpt : ∀ ω, 0 < w ω → T ω ^ (m + 1) ≤ (1 / D) * ∑ i, H i ω ^ (m + 1) := by
    intro ω hω
    obtain ⟨h0, h1⟩ := hT ω hω
    have hs0 : 0 ≤ ∑ i, H i ω := Finset.sum_nonneg fun i _ => hH0 ω hω i
    have hps := pow_sum_le_card_mul_sum_pow (s := Finset.univ) (f := fun i => H i ω)
      (fun i _ => hH0 ω hω i) m
    rw [Finset.card_univ] at hps
    have hS0 : 0 ≤ ∑ i, H i ω ^ (m + 1) :=
      Finset.sum_nonneg fun i _ => pow_nonneg (hH0 ω hω i) _
    calc T ω ^ (m + 1) ≤ ((1 / D) * ∑ i, H i ω) ^ (m + 1) := pow_le_pow_left₀ h0 h1 _
      _ = (1 / D) ^ (m + 1) * (∑ i, H i ω) ^ (m + 1) := mul_pow _ _ _
      _ ≤ (1 / D) ^ (m + 1) * ((Fintype.card ι : ℝ) ^ m * ∑ i, H i ω ^ (m + 1)) :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast hps) (by positivity)
      _ = (1 / D) * (((Fintype.card ι : ℝ) / D) ^ m * ∑ i, H i ω ^ (m + 1)) := by
          have e : ((Fintype.card ι : ℝ) / D) ^ m * ∑ i, H i ω ^ (m + 1) =
              (1 / D) ^ m * ((Fintype.card ι : ℝ) ^ m * ∑ i, H i ω ^ (m + 1)) := by
            rw [div_eq_mul_one_div (Fintype.card ι : ℝ) D, mul_pow]
            ring
          rw [e, pow_succ']
          ring
      _ ≤ (1 / D) * (1 * ∑ i, H i ω ^ (m + 1)) := by
          gcongr
          exact pow_le_one₀ (by positivity) hcd
      _ = (1 / D) * ∑ i, H i ω ^ (m + 1) := by ring
  refine (SecA.wavg_mono' hw hpt).trans ?_
  rw [SecA.wavg_const_mul, wavg_sum]
  calc (1 / D) * ∑ i, wavg w (fun ω => H i ω ^ (m + 1)) ≤ (1 / D) * ∑ _i : ι, c ^ (m + 1) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hmom i) (by positivity)
    _ = ((Fintype.card ι : ℝ) / D) * c ^ (m + 1) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring
    _ ≤ 1 * c ^ (m + 1) := mul_le_mul_of_nonneg_right hcd (by positivity)
    _ = c ^ (m + 1) := one_mul _

end BiluLinial.Tight.SecA.CA

namespace BiluLinial.Tight.CapPoint

open Matrix

variable {d p : ℕ} (cp : CapPoint.{u} d p)

/-- The common endpoint weights `λ_i = a (2√(G⁺_vvG⁺_ii) + 2√(G⁻_vvG⁻_ii))`. -/
noncomputable def endLam (σ : Config cp.V) (v : cp.V) (i : cp.N v) : ℝ :=
  aOf d p * (2 * Real.sqrt (cp.gp σ v v * cp.gp σ i i) +
    2 * Real.sqrt (cp.gm σ v v * cp.gm σ i i))

theorem endLam_nonneg (hR : RegA d p) (σ : Config cp.V) (v : cp.V) (i : cp.N v) :
    0 ≤ cp.endLam σ v i :=
  mul_nonneg hR.treg.aOf_pos.le (add_nonneg (mul_nonneg zero_le_two (Real.sqrt_nonneg _))
    (mul_nonneg zero_le_two (Real.sqrt_nonneg _)))

/-- Both precisions are positive definite at a supported signing. -/
theorem precN_pd_of_wt {σ : Config cp.V} (h : wt cp.G p (aOf d p) cp.yp cp.ym σ cp.S ≠ 0) :
    (precN cp.G (aOf d p) 1 cp.yp σ cp.S).PosDef ∧
      (precN cp.G (aOf d p) (-1) cp.ym σ cp.S).PosDef := by
  by_contra hc
  unfold wt at h
  exact h (by simp [hc])

/-- The majorant conditions of `A-MAJ` at the own signs, both branches, with the weights
`endLam`. -/
theorem endLam_maj (hR : RegA d p) {v : cp.V} (hv : v ∈ cp.S) {σ : Config cp.V}
    (hσ : wt cp.G p (aOf d p) cp.yp cp.ym σ cp.S ≠ 0) :
    (0 < 1 - qForm (cp.A σ v) (cp.xi σ v) ∧
      (∀ i, |(cp.A σ v *ᵥ cp.xi σ v) i| ≤
        (1 - qForm (cp.A σ v) (cp.xi σ v)) * cp.endLam σ v i) ∧
      ∀ i k, |cp.A σ v i k| ≤
        (1 - qForm (cp.A σ v) (cp.xi σ v)) * cp.endLam σ v i * cp.endLam σ v k) ∧
    (0 < 1 - qForm (cp.B σ v) (cp.xi σ v) ∧
      (∀ i, |(cp.B σ v *ᵥ cp.xi σ v) i| ≤
        (1 - qForm (cp.B σ v) (cp.xi σ v)) * cp.endLam σ v i) ∧
      ∀ i k, |cp.B σ v i k| ≤
        (1 - qForm (cp.B σ v) (cp.xi σ v)) * cp.endLam σ v i * cp.endLam σ v k) := by
  have ha := hR.treg.aOf_pos
  obtain ⟨hPp, hPm⟩ := cp.precN_pd_of_wt hσ
  obtain ⟨hA, hB⟩ := cp.root_psd hR hv hσ
  have hl0 := cp.endLam_nonneg hR σ v
  constructor
  · refine SecA.CA.branch_maj cp.G ha (by norm_num) cp.yp_nonneg hv hPp hA (cp.endLam σ v) hl0
      fun i => ?_
    have s1 := Real.sqrt_nonneg (cp.gp σ v v * cp.gp σ i i)
    have s2 := Real.sqrt_nonneg (cp.gm σ v v * cp.gm σ i i)
    show aOf d p * Real.sqrt (cp.gp σ v v * cp.gp σ i i) ≤ cp.endLam σ v i
    unfold endLam
    exact mul_le_mul_of_nonneg_left (by linarith) ha.le
  · refine SecA.CA.branch_maj cp.G ha (by norm_num) cp.ym_nonneg hv hPm hB (cp.endLam σ v) hl0
      fun i => ?_
    have s1 := Real.sqrt_nonneg (cp.gp σ v v * cp.gp σ i i)
    have s2 := Real.sqrt_nonneg (cp.gm σ v v * cp.gm σ i i)
    show aOf d p * Real.sqrt (cp.gm σ v v * cp.gm σ i i) ≤ cp.endLam σ v i
    unfold endLam
    exact mul_le_mul_of_nonneg_left (by linarith) ha.le

/-- `λ_i ≤ 2a (h⁺_v + h⁺_i + h⁻_v + h⁻_i)` on the support (`2√(xy) ≤ x + y`, `G_xx = y_x h_x`,
`y ≤ s ≤ 2`). -/
theorem endLam_le (hR : RegA d p) {σ : Config cp.V}
    (hσ : wt cp.G p (aOf d p) cp.yp cp.ym σ cp.S ≠ 0) (v : cp.V) (i : cp.N v) :
    cp.endLam σ v i ≤ 2 * aOf d p * (cp.hp σ v + cp.hp σ i + cp.hm σ v + cp.hm σ i) := by
  have ha := hR.treg.aOf_pos
  obtain ⟨hPp, hPm⟩ := cp.precN_pd_of_wt hσ
  have hs := SecA.sOf_le_two hR.treg
  have hyp := cp.inCube_yp hR
  have hym := cp.inCube_ym hR
  have key : ∀ (τ : ℝ) (y : cp.V → ℝ), InCube (sOf d p) y →
      (precN cp.G (aOf d p) τ y σ cp.S).PosDef →
      2 * Real.sqrt (greenP cp.G (aOf d p) τ y σ cp.S v v *
        greenP cp.G (aOf d p) τ y σ cp.S i i) ≤
        2 * (hN cp.G (aOf d p) τ y σ cp.S v + hN cp.G (aOf d p) τ y σ cp.S i) := by
    intro τ y hy hP
    have hy0 : ∀ j, 0 ≤ y j := fun j => (hy j).1
    have hv0 : 0 < hN cp.G (aOf d p) τ y σ cp.S v := hP.inv.diag_pos
    have hi0 : 0 < hN cp.G (aOf d p) τ y σ cp.S i := hP.inv.diag_pos
    rw [SecA.greenP_self cp.G (hy0 v), SecA.greenP_self cp.G (hy0 i)]
    have h1 := SecA.CA.two_sqrt_mul_le' (mul_nonneg (hy0 v) hv0.le) (mul_nonneg (hy0 i) hi0.le)
    have h2 : y v * hN cp.G (aOf d p) τ y σ cp.S v ≤ 2 * hN cp.G (aOf d p) τ y σ cp.S v :=
      mul_le_mul_of_nonneg_right ((hy v).2.trans hs) hv0.le
    have h3 : y i * hN cp.G (aOf d p) τ y σ cp.S i ≤ 2 * hN cp.G (aOf d p) τ y σ cp.S i :=
      mul_le_mul_of_nonneg_right ((hy i).2.trans hs) hi0.le
    linarith
  have k1 := key 1 cp.yp hyp hPp
  have k2 := key (-1) cp.ym hym hPm
  unfold endLam
  calc aOf d p * (2 * Real.sqrt (cp.gp σ v v * cp.gp σ i i) +
        2 * Real.sqrt (cp.gm σ v v * cp.gm σ i i))
      ≤ aOf d p * (2 * (cp.hp σ v + cp.hp σ i) + 2 * (cp.hm σ v + cp.hm σ i)) :=
        mul_le_mul_of_nonneg_left (add_le_add k1 k2) ha.le
    _ = 2 * aOf d p * (cp.hp σ v + cp.hp σ i + cp.hm σ v + cp.hm σ i) := by ring

/-- Moments of the endpoint weights: `E (5pλ_i)ⁿ ≤ (41 p a)ⁿ` (`2n ≤ p`). -/
theorem endLam_moment (hR : RegA d p) {v : cp.V} (hv : v ∈ cp.S) (i : cp.N v) {n : ℕ}
    (hn1 : 1 ≤ n) (hn : 2 * n ≤ p) :
    cp.E (fun σ => (5 * (p : ℝ) * cp.endLam σ v i) ^ n) ≤ (41 * (p : ℝ) * aOf d p) ^ n := by
  have ha := hR.treg.aOf_pos
  have hp := hR.p_pos
  have hε0 := SecA.epsP_nonneg hR.treg
  have hε1 := SecA.epsP_le hR.treg
  have hiS : (i : cp.V) ∈ cp.S := (Finset.mem_filter.1 i.2).1
  obtain ⟨mv1, mv2⟩ := cp.h_moment hR hv hn1 hn
  obtain ⟨mi1, mi2⟩ := cp.h_moment hR hiS hn1 hn
  set c := 1 + 2 * epsP d p with hc
  have hc0 : 0 ≤ c := by linarith
  have hpt : ∀ σ, wt cp.G p (aOf d p) cp.yp cp.ym σ cp.S ≠ 0 →
      (5 * (p : ℝ) * cp.endLam σ v i) ^ n ≤ (10 * (p : ℝ) * aOf d p) ^ n * 4 ^ (n - 1) *
        (cp.hp σ v ^ n + cp.hp σ i ^ n + cp.hm σ v ^ n + cp.hm σ i ^ n) := by
    intro σ hσ
    obtain ⟨hPp, hPm⟩ := cp.precN_pd_of_wt hσ
    have h1 : 0 < cp.hp σ v := hPp.inv.diag_pos
    have h2 : 0 < cp.hp σ i := hPp.inv.diag_pos
    have h3 : 0 < cp.hm σ v := hPm.inv.diag_pos
    have h4 : 0 < cp.hm σ i := hPm.inv.diag_pos
    have hl := cp.endLam_le hR hσ v i
    have hl0 := cp.endLam_nonneg hR σ v i
    have e1 : 5 * (p : ℝ) * cp.endLam σ v i ≤
        10 * (p : ℝ) * aOf d p * ((cp.hp σ v + cp.hp σ i) + (cp.hm σ v + cp.hm σ i)) := by
      have := mul_le_mul_of_nonneg_left hl (by positivity : (0 : ℝ) ≤ 5 * p)
      linarith
    have e2 : ((cp.hp σ v + cp.hp σ i) + (cp.hm σ v + cp.hm σ i)) ^ n ≤
        4 ^ (n - 1) * (cp.hp σ v ^ n + cp.hp σ i ^ n + cp.hm σ v ^ n + cp.hm σ i ^ n) := by
      have a1 := add_pow_le (by positivity : 0 ≤ cp.hp σ v + cp.hp σ i)
        (by positivity : 0 ≤ cp.hm σ v + cp.hm σ i) n
      have a2 := add_pow_le h1.le h2.le n
      have a3 := add_pow_le h3.le h4.le n
      have e4 : (4 : ℝ) ^ (n - 1) = 2 ^ (n - 1) * 2 ^ (n - 1) := by
        rw [← mul_pow]; norm_num
      calc _ ≤ 2 ^ (n - 1) * ((cp.hp σ v + cp.hp σ i) ^ n + (cp.hm σ v + cp.hm σ i) ^ n) := a1
        _ ≤ 2 ^ (n - 1) * (2 ^ (n - 1) * (cp.hp σ v ^ n + cp.hp σ i ^ n) +
            2 ^ (n - 1) * (cp.hm σ v ^ n + cp.hm σ i ^ n)) := by gcongr
        _ = _ := by rw [e4]; ring
    calc (5 * (p : ℝ) * cp.endLam σ v i) ^ n
        ≤ (10 * (p : ℝ) * aOf d p * ((cp.hp σ v + cp.hp σ i) + (cp.hm σ v + cp.hm σ i))) ^ n :=
          pow_le_pow_left₀ (by positivity) e1 n
      _ = (10 * (p : ℝ) * aOf d p) ^ n *
          ((cp.hp σ v + cp.hp σ i) + (cp.hm σ v + cp.hm σ i)) ^ n := mul_pow _ _ _
      _ ≤ (10 * (p : ℝ) * aOf d p) ^ n * (4 ^ (n - 1) *
          (cp.hp σ v ^ n + cp.hp σ i ^ n + cp.hm σ v ^ n + cp.hm σ i ^ n)) :=
          mul_le_mul_of_nonneg_left e2 (by positivity)
      _ = _ := by ring
  have h1 := SecA.lawE_le_of_supp cp.G hpt
  refine h1.trans ?_
  have e : lawE cp.G p (aOf d p) cp.yp cp.ym cp.S (fun σ => (10 * (p : ℝ) * aOf d p) ^ n *
        4 ^ (n - 1) * (cp.hp σ v ^ n + cp.hp σ i ^ n + cp.hm σ v ^ n + cp.hm σ i ^ n)) =
      (10 * (p : ℝ) * aOf d p) ^ n * 4 ^ (n - 1) * (cp.E (fun σ => cp.hp σ v ^ n) +
        cp.E (fun σ => cp.hp σ i ^ n) + cp.E (fun σ => cp.hm σ v ^ n) +
        cp.E (fun σ => cp.hm σ i ^ n)) := by
    rw [lawE_const_mul, lawE_add, lawE_add, lawE_add]
    rfl
  rw [e]
  have e4 : (4 : ℝ) ^ (n - 1) * 4 = 4 ^ n := by rw [← pow_succ, Nat.sub_add_cancel hn1]
  calc (10 * (p : ℝ) * aOf d p) ^ n * 4 ^ (n - 1) * (cp.E (fun σ => cp.hp σ v ^ n) +
        cp.E (fun σ => cp.hp σ i ^ n) + cp.E (fun σ => cp.hm σ v ^ n) +
        cp.E (fun σ => cp.hm σ i ^ n))
      ≤ (10 * (p : ℝ) * aOf d p) ^ n * 4 ^ (n - 1) * (c ^ n + c ^ n + c ^ n + c ^ n) := by
        gcongr
    _ = (10 * (p : ℝ) * aOf d p) ^ n * (4 ^ (n - 1) * 4) * c ^ n := by ring
    _ = (40 * (p : ℝ) * aOf d p * c) ^ n := by
        rw [e4, ← mul_pow, ← mul_pow]
        ring_nf
    _ ≤ (41 * (p : ℝ) * aOf d p) ^ n := by
        refine pow_le_pow_left₀ (by positivity) ?_ n
        have : c ≤ 41 / 40 := by rw [hc]; linarith
        have h0 : 0 ≤ 40 * (p : ℝ) * aOf d p := by positivity
        nlinarith

/-- The root trace under the actual law: `0 ≤ tr R ≤ (1/d) Σ_{i ∈ N} h_i` at a good precision
(`R_ii = (a² y_v/D_v) C_ii ≤ (a² y_v/D_v) y_i h_i`, Schur order, `a² s² ≤ 1/d`). -/
theorem trace_root_le (hR : RegA d p) {τ : ℝ} {y : cp.V → ℝ} (hy : InCube (sOf d p) y)
    {v : cp.V} (hv : v ∈ cp.S) {σ : Config cp.V}
    (hP : (precN cp.G (aOf d p) τ y σ cp.S).PosDef)
    (hA : (rootMat cp.G (aOf d p) τ y σ cp.S v).PosSemidef) :
    0 ≤ (rootMat cp.G (aOf d p) τ y σ cp.S v).trace ∧
      (rootMat cp.G (aOf d p) τ y σ cp.S v).trace ≤
        (1 / d) * ∑ i : cp.N v, hN cp.G (aOf d p) τ y σ cp.S i := by
  have hy0 : ∀ j, 0 ≤ y j := fun j => (hy j).1
  have hd := hR.d_pos
  have hD : 1 ≤ diagD cp.G (aOf d p) y cp.S v := FloorIns.one_le_diagD cp.G _ hy0 _ _
  have hs := SecA.sOf_le_two hR.treg
  have hκ := SecA.d_mul_kappa_le_one hR.treg
  refine ⟨hA.trace_nonneg, ?_⟩
  rw [Matrix.trace, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hiv : (i : cp.V) ≠ v := (cp.G.ne_of_adj (Finset.mem_filter.1 i.2).2).symm
  have hcg := SecA.coreGreen_le_greenP cp.G hy0 hv hP hiv
  rw [SecA.greenP_self cp.G (hy0 i)] at hcg
  have hhi : 0 < hN cp.G (aOf d p) τ y σ cp.S i := hP.inv.diag_pos
  have hc0 : 0 ≤ aOf d p ^ 2 * y v / diagD cp.G (aOf d p) y cp.S v :=
    div_nonneg (mul_nonneg (sq_nonneg _) (hy0 v)) (by linarith)
  show aOf d p ^ 2 * y v / diagD cp.G (aOf d p) y cp.S v * coreGreen cp.G (aOf d p) τ y σ cp.S v i i
    ≤ 1 / d * hN cp.G (aOf d p) τ y σ cp.S i
  calc aOf d p ^ 2 * y v / diagD cp.G (aOf d p) y cp.S v *
        coreGreen cp.G (aOf d p) τ y σ cp.S v i i
      ≤ aOf d p ^ 2 * y v / diagD cp.G (aOf d p) y cp.S v *
          (y i * hN cp.G (aOf d p) τ y σ cp.S i) := mul_le_mul_of_nonneg_left hcg hc0
    _ ≤ aOf d p ^ 2 * y v * (y i * hN cp.G (aOf d p) τ y σ cp.S i) :=
        mul_le_mul_of_nonneg_right (div_le_self (mul_nonneg (sq_nonneg _) (hy0 v)) hD)
          (mul_nonneg (hy0 i) hhi.le)
    _ ≤ aOf d p ^ 2 * sOf d p * (sOf d p * hN cp.G (aOf d p) τ y σ cp.S i) := by
        have hs0 : 0 ≤ sOf d p := (hy0 v).trans (hy v).2
        have e1 : aOf d p ^ 2 * y v ≤ aOf d p ^ 2 * sOf d p :=
          mul_le_mul_of_nonneg_left (hy v).2 (sq_nonneg _)
        have e2 : y i * hN cp.G (aOf d p) τ y σ cp.S i ≤ sOf d p * hN cp.G (aOf d p) τ y σ cp.S i :=
          mul_le_mul_of_nonneg_right (hy i).2 hhi.le
        exact mul_le_mul e1 e2 (mul_nonneg (hy0 i) hhi.le) (mul_nonneg (sq_nonneg _) hs0)
    _ = (aOf d p ^ 2 * sOf d p ^ 2) * hN cp.G (aOf d p) τ y σ cp.S i := by ring
    _ ≤ 1 / d * hN cp.G (aOf d p) τ y σ cp.S i := by
        refine mul_le_mul_of_nonneg_right ?_ hhi.le
        rw [le_div_iff₀ hd]
        linarith

/-- Actual-law moments of the root traces: `E (tr A)ⁿ, E (tr B)ⁿ ≤ (1 + 2ε)ⁿ` (`2n ≤ p`). -/
theorem E_trace_pow_le (hR : RegA d p) {v : cp.V} (hv : v ∈ cp.S) {n : ℕ} (hn1 : 1 ≤ n)
    (hn : 2 * n ≤ p) :
    cp.E (fun σ => (cp.A σ v).trace ^ n) ≤ (1 + 2 * epsP d p) ^ n ∧
      cp.E (fun σ => (cp.B σ v).trace ^ n) ≤ (1 + 2 * epsP d p) ^ n := by
  have hd := hR.d_pos
  have hε0 := SecA.epsP_nonneg hR.treg
  have hw : ∀ σ, 0 ≤ wt cp.G p (aOf d p) cp.yp cp.ym σ cp.S := fun σ => wt_nonneg cp.G σ
  have hZ := cp.Zw_pos hR
  have hiS : ∀ i : cp.N v, (i : cp.V) ∈ cp.S := fun i => (Finset.mem_filter.1 i.2).1
  constructor
  · refine SecA.CA.wavg_pow_le_of_le_avg hw hZ _ (fun (i : cp.N v) σ => cp.hp σ i) hd
      (cp.card_N_le v) (by linarith) hn1 (fun σ hσ => ?_) (fun σ hσ i => ?_)
      (fun i => (cp.h_moment hR (hiS i) hn1 hn).1)
    · obtain ⟨hPp, -⟩ := cp.precN_pd_of_wt hσ.ne'
      exact cp.trace_root_le hR (cp.inCube_yp hR) hv hPp (cp.root_psd hR hv hσ.ne').1
    · exact (cp.precN_pd_of_wt hσ.ne').1.inv.diag_pos.le
  · refine SecA.CA.wavg_pow_le_of_le_avg hw hZ _ (fun (i : cp.N v) σ => cp.hm σ i) hd
      (cp.card_N_le v) (by linarith) hn1 (fun σ hσ => ?_) (fun σ hσ i => ?_)
      (fun i => (cp.h_moment hR (hiS i) hn1 hn).2)
    · obtain ⟨-, hPm⟩ := cp.precN_pd_of_wt hσ.ne'
      exact cp.trace_root_le hR (cp.inCube_ym hR) hv hPm (cp.root_psd hR hv hσ.ne').2
    · exact (cp.precN_pd_of_wt hσ.ne').2.inv.diag_pos.le

/-- Own-core moments of the (cut-off) root traces: `E_{ν_K} (tr A)ⁿ ≤ (1 + 2ε)ⁿ`, same for `B`. -/
theorem coreE_trace_pow_le (hR : RegA d p) {v : cp.V} (hv : v ∈ cp.S) {n : ℕ} (hn1 : 1 ≤ n)
    (hn : 2 * n ≤ p) :
    cp.coreE v (fun σ => (if wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v ≠ 0 then
        (cp.A σ v).trace else 0) ^ n) ≤ (1 + 2 * epsP d p) ^ n ∧
      cp.coreE v (fun σ => (if wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v ≠ 0 then
        (cp.B σ v).trace else 0) ^ n) ≤ (1 + 2 * epsP d p) ^ n := by
  have hd := hR.d_pos
  have hε0 := SecA.epsP_nonneg hR.treg
  have hw : ∀ σ, 0 ≤ wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v :=
    fun σ => SecA.wtCore_nonneg cp.G _ _ _ _ σ _ _
  have hZ := cp.ZwCore_pos hR hv
  have key : ∀ σ, wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v ≠ 0 →
      (0 ≤ (cp.A σ v).trace ∧ (cp.A σ v).trace ≤ (1 / d) * ∑ i : cp.N v,
        (precCore cp.G (aOf d p) 1 cp.yp σ cp.S v)⁻¹ i i) ∧
      (0 ≤ (cp.B σ v).trace ∧ (cp.B σ v).trace ≤ (1 / d) * ∑ i : cp.N v,
        (precCore cp.G (aOf d p) (-1) cp.ym σ cp.S v)⁻¹ i i) := by
    intro σ hσ
    have hb := fun i => cp.bdiag_mem hR hσ i
    obtain ⟨h1, h2⟩ := SecA.posDef_of_wtCore_ne_zero cp.G hσ
    have hA := fun i => SecA.rootMat_diag_mem cp.G hR.treg (cp.inCube_yp hR) h1 i
    have hB := fun i => SecA.rootMat_diag_mem cp.G hR.treg (cp.inCube_ym hR) h2 i
    refine ⟨⟨Finset.sum_nonneg fun i _ => (hA i).1, ?_⟩,
      ⟨Finset.sum_nonneg fun i _ => (hB i).1, ?_⟩⟩
    · rw [Matrix.trace, Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => (hA i).2
    · rw [Matrix.trace, Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => (hB i).2
  constructor
  · refine SecA.CA.wavg_pow_le_of_le_avg hw hZ _
      (fun (i : cp.N v) σ => (precCore cp.G (aOf d p) 1 cp.yp σ cp.S v)⁻¹ i i) hd
      (cp.card_N_le v) (by linarith) hn1 (fun σ hσ => ?_) (fun σ hσ i => ?_)
      (fun i => (cp.core_moment hR hv (i : cp.V) hn1 hn).1)
    · rw [ite_eq_left hσ.ne']
      exact (key σ hσ.ne').1
    · exact (cp.bdiag_mem hR hσ.ne' i).2.2.1
  · refine SecA.CA.wavg_pow_le_of_le_avg hw hZ _
      (fun (i : cp.N v) σ => (precCore cp.G (aOf d p) (-1) cp.ym σ cp.S v)⁻¹ i i) hd
      (cp.card_N_le v) (by linarith) hn1 (fun σ hσ => ?_) (fun σ hσ i => ?_)
      (fun i => (cp.core_moment hR hv (i : cp.V) hn1 hn).2)
    · rw [ite_eq_left hσ.ne']
      exact (key σ hσ.ne').2
    · exact (cp.bdiag_mem hR hσ.ne' i).2.2.2

end BiluLinial.Tight.CapPoint

namespace BiluLinial.Tight.SecA.CA

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
theorem pderivList_zero_fn (l : List ι) :
    pderivList l (fun _ : ι → ℝ => (0 : ℝ)) = fun _ => 0 := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    rw [pderivList_cons]
    have h : pderiv i (fun _ : ι → ℝ => (0 : ℝ)) = fun _ => 0 := by
      funext x
      simp [pderiv]
    rw [h, ih]

theorem smoothBdd_zero_fn (N : ℕ) : SmoothBdd N (fun _ : ι → ℝ => (0 : ℝ)) :=
  ⟨contDiff_const, fun l _ => ⟨0, fun x => by rw [pderivList_zero_fn]; simp⟩⟩

omit [DecidableEq ι] in
/-- `Φ(ξ) = 0` forces `q_A(ξ) ≥ 1` or `q_B(ξ) ≥ 1`. -/
theorem one_le_of_starPhi_eq_zero {p : ℕ} (hp : 1 ≤ p) {A B : Matrix ι ι ℝ} {ξ : ι → ℝ}
    (h : starPhi p A B ξ = 0) : 1 ≤ qForm A ξ ∨ 1 ≤ qForm B ξ := by
  rcases mul_eq_zero.1 h with h | h
  · left
    have := (pow_eq_zero_iff (n := p) (by omega)).1 h
    simp only [clipF] at this
    have := le_max_left (1 - qForm A ξ) 0
    linarith
  · right
    have := (pow_eq_zero_iff (n := p) (by omega)).1 h
    simp only [clipF] at this
    have := le_max_left (1 - qForm B ξ) 0
    linarith

omit [DecidableEq ι] in
theorem starPhi_eq_of_pos {p : ℕ} {A B : Matrix ι ι ℝ} {ξ : ι → ℝ} (hα : 0 < 1 - qForm A ξ)
    (hβ : 0 < 1 - qForm B ξ) :
    starPhi p A B ξ = (1 - qForm A ξ) ^ p * (1 - qForm B ξ) ^ p := by
  simp only [starPhi, clipF, max_eq_left hα.le, max_eq_left hβ.le]

omit [DecidableEq ι] in
theorem starPhi_comm (p : ℕ) (A B : Matrix ι ι ℝ) (ξ : ι → ℝ) :
    starPhi p A B ξ = starPhi p B A ξ := by
  simp only [starPhi]
  ring

end BiluLinial.Tight.SecA.CA

namespace BiluLinial.Tight

open Matrix

/-- Regime arithmetic for the endpoint scale `L = 41 p a`: `d L² ≥ 2`, `d L⁴ ≤ 41⁴ p⁴/(4d)`,
`d L⁴ ≤ 1/2`. -/
theorem RegA.endL_facts {d p : ℕ} (hR : RegA d p) :
    2 ≤ (d : ℝ) * (41 * (p : ℝ) * aOf d p) ^ 2 ∧
      (d : ℝ) * (41 * (p : ℝ) * aOf d p) ^ 4 ≤ 41 ^ 4 / 4 * ((p : ℝ) ^ 4 / d) ∧
      (d : ℝ) * (41 * (p : ℝ) * aOf d p) ^ 4 ≤ 1 / 2 := by
  have hd := hR.d_pos
  have hp := hR.p_pos
  have hp6 : (10 : ℝ) ^ 6 ≤ p := by exact_mod_cast hR.treg.hp
  have hq := hR.treg.qOf_pos
  have hdq : (d : ℝ) = qOf d + 1 := by rw [qOf]; ring
  have hd6 : (10 : ℝ) ^ 6 ≤ d := hR.treg.ten_pow_six_le_d
  have ha2 := SecA.aOf_sq_le hR.treg
  have haq := hR.treg.aOf_sq
  have hR0 := hR.treg.RsqOf_pos
  have hΔ : ΔOf p = 4 / p := rfl
  -- `d a² ≥ 1/4`
  have hda : 1 / 4 ≤ (d : ℝ) * aOf d p ^ 2 := by
    rw [haq, mul_one_div, le_div_iff₀ hR0, RsqOf, hΔ]
    have : 4 / (p : ℝ) ≤ 4 := by rw [div_le_iff₀ hp]; nlinarith
    linarith
  -- `d a⁴ ≤ 1/(4d)`
  have hda4 : (d : ℝ) * aOf d p ^ 4 ≤ 1 / (4 * d) := by
    have h1 : aOf d p ^ 4 ≤ (1 / (4 * qOf d)) ^ 2 := by
      rw [show aOf d p ^ 4 = (aOf d p ^ 2) ^ 2 by ring]
      exact pow_le_pow_left₀ (sq_nonneg _) ha2 2
    have h2 : (d : ℝ) * (1 / (4 * qOf d)) ^ 2 ≤ 1 / (4 * d) := by
      rw [div_pow, one_pow, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    calc (d : ℝ) * aOf d p ^ 4 ≤ (d : ℝ) * (1 / (4 * qOf d)) ^ 2 :=
          mul_le_mul_of_nonneg_left h1 hd.le
      _ ≤ _ := h2
  have h7 := hR.p_pow_seven_le
  refine ⟨?_, ?_, ?_⟩
  · have e : (d : ℝ) * (41 * (p : ℝ) * aOf d p) ^ 2 = 1681 * (p : ℝ) ^ 2 * (d * aOf d p ^ 2) := by
      ring
    rw [e]
    have : (1 : ℝ) ≤ (p : ℝ) ^ 2 := by nlinarith
    nlinarith
  · have e : (d : ℝ) * (41 * (p : ℝ) * aOf d p) ^ 4 = 41 ^ 4 * (p : ℝ) ^ 4 * (d * aOf d p ^ 4) := by
      ring
    rw [e]
    calc 41 ^ 4 * (p : ℝ) ^ 4 * (d * aOf d p ^ 4) ≤ 41 ^ 4 * (p : ℝ) ^ 4 * (1 / (4 * d)) :=
          mul_le_mul_of_nonneg_left hda4 (by positivity)
      _ = 41 ^ 4 / 4 * ((p : ℝ) ^ 4 / d) := by field_simp
  · have e : (d : ℝ) * (41 * (p : ℝ) * aOf d p) ^ 4 = 41 ^ 4 * (p : ℝ) ^ 4 * (d * aOf d p ^ 4) := by
      ring
    rw [e]
    have h4 : (p : ℝ) ^ 4 * 10 ^ 18 ≤ d := by
      have : (p : ℝ) ^ 4 * (10 ^ 6) ^ 3 ≤ (p : ℝ) ^ 4 * (p : ℝ) ^ 3 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) hp6 3) (by positivity)
      nlinarith
    calc 41 ^ 4 * (p : ℝ) ^ 4 * (d * aOf d p ^ 4) ≤ 41 ^ 4 * (p : ℝ) ^ 4 * (1 / (4 * d)) :=
          mul_le_mul_of_nonneg_left hda4 (by positivity)
      _ ≤ 1 / 2 := by
          rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith

namespace CapPoint

variable {d p : ℕ} (cp : CapPoint.{u} d p)

/-- The facts on a branch pair `(P, Q) = (A, B)` or `(B, A)` used by `bias_gen`, `whiten_gen`. -/
theorem pair_facts (hR : RegA d p) {v : cp.V} (hv : v ∈ cp.S)
    (P Q : Config cp.V → Matrix (cp.N v) (cp.N v) ℝ)
    (hPQ : (∀ σ, P σ = cp.A σ v ∧ Q σ = cp.B σ v) ∨ (∀ σ, P σ = cp.B σ v ∧ Q σ = cp.A σ v)) :
    (∀ σ, wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v ≠ 0 →
      (P σ).PosSemidef ∧ (Q σ).PosSemidef) ∧
    (∀ σ σ', AgreeOff v σ σ' → P σ = P σ' ∧ Q σ = Q σ') ∧
    (∀ σ ξ, starPhi p (P σ) (Q σ) ξ = starPhi p (cp.A σ v) (cp.B σ v) ξ) ∧
    (∀ σ i, P σ i i + Q σ i i = cp.bdiag σ v i) ∧
    (∀ σ, wt cp.G p (aOf d p) cp.yp cp.ym σ cp.S ≠ 0 →
      (0 < 1 - qForm (P σ) (cp.xi σ v) ∧
        (∀ i, |(P σ *ᵥ cp.xi σ v) i| ≤ (1 - qForm (P σ) (cp.xi σ v)) * cp.endLam σ v i) ∧
        ∀ i k, |P σ i k| ≤ (1 - qForm (P σ) (cp.xi σ v)) * cp.endLam σ v i * cp.endLam σ v k) ∧
      (0 < 1 - qForm (Q σ) (cp.xi σ v) ∧
        (∀ i, |(Q σ *ᵥ cp.xi σ v) i| ≤ (1 - qForm (Q σ) (cp.xi σ v)) * cp.endLam σ v i) ∧
        ∀ i k, |Q σ i k| ≤ (1 - qForm (Q σ) (cp.xi σ v)) * cp.endLam σ v i * cp.endLam σ v k))
    := by
  rcases hPQ with h | h
  · refine ⟨fun σ hσ => ?_, fun σ σ' hσ => ?_, fun σ ξ => ?_, fun σ i => ?_, fun σ hσ => ?_⟩
    · rw [(h σ).1, (h σ).2]; exact cp.root_psd_core hσ
    · rw [(h σ).1, (h σ).2, (h σ').1, (h σ').2]
      exact ⟨SecA.rootMat_congr cp.G hσ, SecA.rootMat_congr cp.G hσ⟩
    · rw [(h σ).1, (h σ).2]
    · rw [(h σ).1, (h σ).2]; rfl
    · rw [(h σ).1, (h σ).2]; exact cp.endLam_maj hR hv hσ
  · refine ⟨fun σ hσ => ?_, fun σ σ' hσ => ?_, fun σ ξ => ?_, fun σ i => ?_, fun σ hσ => ?_⟩
    · rw [(h σ).1, (h σ).2]; exact (cp.root_psd_core hσ).symm
    · rw [(h σ).1, (h σ).2, (h σ').1, (h σ').2]
      exact ⟨SecA.rootMat_congr cp.G hσ, SecA.rootMat_congr cp.G hσ⟩
    · rw [(h σ).1, (h σ).2, SecA.CA.starPhi_comm]
    · rw [(h σ).1, (h σ).2, add_comm]; rfl
    · rw [(h σ).1, (h σ).2]; exact (cp.endLam_maj hR hv hσ).symm

end CapPoint

end BiluLinial.Tight

namespace BiluLinial.Tight.CapPoint

open Matrix

variable {d p : ℕ} (cp : CapPoint.{u} d p)

/-- `A-C1a`, one branch, generic in the pair `(P, Q) = (A, B)` or `(B, A)`: the Rademacher–
Gaussian bias of `f₁ = (tr P - q_P) α_P^{p-1} α_Q^p` under the own core law is
`≤ 10⁸ (p⁴/d) F_H`. Proof: `A-TRANSR` with `F = f₁` (cut off to the core support), sup majorant
`1 + tr P` (`A-E5`), endpoint majorant `X = (1 + tr P)·2H ≥ (1 + tr P)/α_P` with weights
`5p λ_i` (`A-MAJ`, F1), `m = ϑ = 13`, `B = 5`, `K = 1`. -/
theorem bias_gen (hR : RegA d p) {v : cp.V} (hv : v ∈ cp.S)
    (P Q : Config cp.V → Matrix (cp.N v) (cp.N v) ℝ)
    (hPQ : (∀ σ, P σ = cp.A σ v ∧ Q σ = cp.B σ v) ∨ (∀ σ, P σ = cp.B σ v ∧ Q σ = cp.A σ v))
    (hmomP : ∀ n : ℕ, 1 ≤ n → 2 * n ≤ p → cp.coreE v (fun σ =>
      (if wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v ≠ 0 then (P σ).trace else 0) ^ n) ≤
        (1 + 2 * epsP d p) ^ n)
    (hEP4 : cp.E (fun σ => (P σ).trace ^ 4) ≤ (1 + 2 * epsP d p) ^ 4)
    (H : Config cp.V → ℝ)
    (hH : ∀ σ, wt cp.G p (aOf d p) cp.yp cp.ym σ cp.S ≠ 0 →
      0 ≤ H σ ∧ 1 ≤ (1 - qForm (P σ) (cp.xi σ v)) * (2 * H σ))
    (hH4 : cp.E (fun σ => H σ ^ 4) ≤ (1 + 2 * epsP d p) ^ 4) :
    |cp.coreE v (fun σ => radE (f1Obs p (P σ) (Q σ)) - gaussE (f1Obs p (P σ) (Q σ)))| ≤
      10 ^ 8 * (p : ℝ) ^ 4 / d * cp.FH v := by
  have hd := hR.d_pos
  have hp := hR.p_pos
  have hp1 : 1 ≤ p := le_trans (by norm_num) hR.treg.two_le_p
  have hp2 : 2 ≤ p := hR.treg.two_le_p
  have hk7 := hR.four_kStar_add_seven_le
  have hε0 := SecA.epsP_nonneg hR.treg
  have hε1 := SecA.epsP_le hR.treg
  have hw : ∀ σ, 0 ≤ wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v :=
    fun σ => SecA.wtCore_nonneg cp.G _ _ _ _ σ _ _
  have hwt : ∀ σ, 0 ≤ wt cp.G p (aOf d p) cp.yp cp.ym σ cp.S := fun σ => wt_nonneg cp.G σ
  have hZc := cp.ZwCore_pos hR hv
  have hZ := cp.Zw_pos hR
  obtain ⟨hpsd, hcong, hphi, hb, hmaj⟩ := cp.pair_facts hR hv P Q hPQ
  set k := kStarA d p with hk
  have hN1 : 4 * k + 4 < p - 1 := by omega
  -- the family and its sup majorant
  set F : Config cp.V → (cp.N v → ℝ) → ℝ := fun σ =>
    if wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v ≠ 0 then f1Obs p (P σ) (Q σ)
    else fun _ => 0 with hF
  set m : Config cp.V → ℝ := fun σ =>
    if wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v ≠ 0 then 1 + (P σ).trace else 0 with hm
  have hFs : ∀ σ, wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v ≠ 0 →
      F σ = clipObs (quadFn (P σ).trace 0 (-(P σ))) (p - 1) p (P σ) (Q σ) := fun σ hσ => by
    rw [hF]
    dsimp only
    rw [ite_eq_left hσ]
    exact SecA.CA.f1Obs_eq_clipObs p _ _
  have hFn : ∀ σ, ¬ wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v ≠ 0 → F σ = fun _ => 0 :=
    fun σ hσ => by rw [hF]; dsimp only; rw [ite_eq_right hσ]
  have hms : ∀ σ, wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v ≠ 0 →
      m σ = 1 + (P σ).trace := fun σ hσ => by rw [hm]; dsimp only; rw [ite_eq_left hσ]
  have hmn : ∀ σ, ¬ wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v ≠ 0 → m σ = 0 :=
    fun σ hσ => by rw [hm]; dsimp only; rw [ite_eq_right hσ]
  have hm0 : ∀ σ, 0 ≤ m σ := by
    intro σ
    by_cases hσ : wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v ≠ 0
    · rw [hms σ hσ]; linarith [(hpsd σ hσ).1.trace_nonneg]
    · rw [hmn σ hσ]
  have hmom : ∀ n : ℕ, 1 ≤ n → 2 * n ≤ p → cp.coreE v (fun σ => m σ ^ n) ≤ 3 ^ n := by
    intro n hn1 hn
    have hpt : ∀ σ, 0 < wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v →
        m σ ^ n ≤ 2 ^ (n - 1) * (1 + (if wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v ≠ 0 then
          (P σ).trace else 0) ^ n) := by
      intro σ hσ
      rw [hms σ hσ.ne', ite_eq_left hσ.ne']
      have := add_pow_le zero_le_one (hpsd σ hσ.ne').1.trace_nonneg n
      simpa using this
    have h1 := SecA.wavg_mono' hw hpt
    rw [SecA.wavg_const_mul, SecA.wavg_add, wavg_const hZc] at h1
    have h2 : wavg (fun ω => wtCore cp.G p (aOf d p) cp.yp cp.ym ω cp.S v)
        (fun ω => (if wtCore cp.G p (aOf d p) cp.yp cp.ym ω cp.S v ≠ 0 then (P ω).trace
          else 0) ^ n) ≤ (1 + 2 * epsP d p) ^ n := hmomP n hn1 hn
    have h3 : (1 : ℝ) ≤ (1 + 2 * epsP d p) ^ n := one_le_pow₀ (by linarith)
    have e2 : (2 : ℝ) ^ (n - 1) * 2 = 2 ^ n := by rw [← pow_succ, Nat.sub_add_cancel hn1]
    calc cp.coreE v (fun σ => m σ ^ n) ≤ _ := h1
      _ ≤ 2 ^ (n - 1) * (1 + (1 + 2 * epsP d p) ^ n) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ ≤ 2 ^ (n - 1) * (2 * (1 + 2 * epsP d p) ^ n) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = (2 * (1 + 2 * epsP d p)) ^ n := by rw [mul_pow, ← e2]; ring
      _ ≤ 3 ^ n := pow_le_pow_left₀ (by positivity) (by linarith) n
  have hFc : ∀ σ σ', AgreeOff v σ σ' → F σ = F σ' := by
    intro σ σ' h
    have h1 := SecA.wtCore_congr cp.G (p := p) (a := aOf d p) (yp := cp.yp) (ym := cp.ym)
      (S := cp.S) h
    obtain ⟨h2, h3⟩ := hcong σ σ' h
    simp only [hF, h1, h2, h3]
  have hpkg : ∀ σ, wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v ≠ 0 → _ := fun σ hσ =>
    SecA.CA.clip_package (hpsd σ hσ).1 (hpsd σ hσ).2 (N := 4 * k + 4) hN1 (by omega)
      (Nat.sub_le p 1) le_rfl hp2 (fun x hx _ => SecA.CA.quadMaj_trace_sup (hpsd σ hσ).1
        (hpsd σ hσ).2 hx)
  have hsm : ∀ σ, SmoothBdd (4 * kStarA d p + 4) (F σ) := by
    intro σ
    by_cases hσ : wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v ≠ 0
    · rw [hFs σ hσ]; exact (hpkg σ hσ).1
    · rw [hFn σ hσ]; exact SecA.CA.smoothBdd_zero_fn _
  have hder : ∀ σ, ∀ j ∈ (topIdx (kStarA d p) : Finset (cp.N v → ℕ)), ∀ x,
      |dEven (cp.lN v) j (F σ) x| ≤
        m σ * (5 * (p : ℝ)) ^ (2 * ∑ i, j i) * ∏ i, cp.bdiag σ v i ^ j i := by
    intro σ j hj x
    obtain ⟨hadm, hg⟩ := mem_topIdx.1 hj
    have hsum := SecA.sum_le_two_mul_grade' hadm
    by_cases hσ : wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v ≠ 0
    · rw [hFs σ hσ, hms σ hσ]
      have h := (hpkg σ hσ).2.1 j (by omega) x
      simp only [hb] at h
      exact h
    · rw [hFn σ hσ, hmn σ hσ, dEven_eq_pderivList, SecA.CA.pderivList_zero_fn]
      simp
  have hvan : ∀ σ, ∀ j ∈ (retIdx (kStarA d p) : Finset (cp.N v → ℕ)), ∀ ξ : cp.N v → ℝ,
      (∀ i, ξ i = 1 ∨ ξ i = -1) → starPhi p (cp.A σ v) (cp.B σ v) ξ = 0 →
        dEven (cp.lN v) j (F σ) ξ = 0 := by
    intro σ j hj ξ _ hΦ
    obtain ⟨hadm, hg⟩ := mem_retIdx.1 hj
    have hsum := SecA.sum_le_two_mul_grade' hadm
    by_cases hσ : wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v ≠ 0
    · rw [hFs σ hσ]
      rw [← hphi σ ξ] at hΦ
      exact (hpkg σ hσ).2.2 j (by omega) ξ (SecA.CA.one_le_of_starPhi_eq_zero hp1 hΦ)
    · rw [hFn σ hσ, dEven_eq_pderivList, SecA.CA.pderivList_zero_fn]
  -- the endpoint majorant
  set X : Config cp.V → ℝ := fun σ =>
    if wt cp.G p (aOf d p) cp.yp cp.ym σ cp.S ≠ 0 then (1 + (P σ).trace) * (2 * H σ) else 0
    with hX
  have hXs : ∀ σ, wt cp.G p (aOf d p) cp.yp cp.ym σ cp.S ≠ 0 →
      X σ = (1 + (P σ).trace) * (2 * H σ) := fun σ hσ => by
    rw [hX]; dsimp only; rw [ite_eq_left hσ]
  have htrw : ∀ σ, wt cp.G p (aOf d p) cp.yp cp.ym σ cp.S ≠ 0 → 0 ≤ (P σ).trace :=
    fun σ hσ => (hpsd σ (cp.wtCore_ne_zero_of_wt hR hv hσ)).1.trace_nonneg
  have hX0 : ∀ σ, 0 ≤ X σ := by
    intro σ
    by_cases hσ : wt cp.G p (aOf d p) cp.yp cp.ym σ cp.S ≠ 0
    · rw [hXs σ hσ]
      have := htrw σ hσ
      have := (hH σ hσ).1
      positivity
    · rw [hX]; dsimp only; rw [ite_eq_right hσ]
  have hc4 : (1 + 2 * epsP d p) ^ 4 ≤ 105 / 100 := by
    have h1 : 1 + 2 * epsP d p ≤ 101 / 100 := by linarith
    calc (1 + 2 * epsP d p) ^ 4 ≤ (101 / 100) ^ 4 := pow_le_pow_left₀ (by linarith) h1 4
      _ ≤ 105 / 100 := by norm_num
  have hX2 : cp.E (fun σ => X σ ^ 2) ≤ 5 ^ 2 := by
    have hpt : ∀ σ, wt cp.G p (aOf d p) cp.yp cp.ym σ cp.S ≠ 0 →
        X σ ^ 2 ≤ 4 + 4 * (P σ).trace ^ 4 + 8 * H σ ^ 4 := by
      intro σ hσ
      rw [hXs σ hσ]
      have ht := htrw σ hσ
      have hH0 := (hH σ hσ).1
      have a1 := add_pow_le zero_le_one ht 4
      norm_num at a1
      nlinarith [sq_nonneg ((1 + (P σ).trace) ^ 2 - (2 * H σ) ^ 2)]
    have h1 := SecA.lawE_le_of_supp cp.G hpt
    have e : lawE cp.G p (aOf d p) cp.yp cp.ym cp.S
        (fun σ => 4 + 4 * (P σ).trace ^ 4 + 8 * H σ ^ 4) =
        4 + 4 * cp.E (fun σ => (P σ).trace ^ 4) + 8 * cp.E (fun σ => H σ ^ 4) := by
      rw [lawE_add, lawE_add, lawE_const_mul, lawE_const_mul,
        show lawE cp.G p (aOf d p) cp.yp cp.ym cp.S (fun _ => (4 : ℝ)) = 4 from
          wavg_const hZ 4]
      rfl
    rw [e] at h1
    show cp.E (fun σ => X σ ^ 2) ≤ 5 ^ 2
    have : cp.E (fun σ => X σ ^ 2) ≤ 4 + 4 * cp.E (fun σ => (P σ).trace ^ 4) +
        8 * cp.E (fun σ => H σ ^ 4) := h1
    nlinarith
  have hXm : cp.E X ≤ 13 := by
    have hpt : ∀ σ, X σ ≤ 1 / 2 + 1 / 2 * X σ ^ 2 := fun σ => by nlinarith [sq_nonneg (X σ - 1)]
    have h1 := wavg_mono hwt hZ hpt
    have e : wavg (fun σ => wt cp.G p (aOf d p) cp.yp cp.ym σ cp.S)
        (fun σ => 1 / 2 + 1 / 2 * X σ ^ 2) = 1 / 2 + 1 / 2 * cp.E (fun σ => X σ ^ 2) := by
      rw [SecA.wavg_add, SecA.wavg_const_mul, wavg_const hZ]
      rfl
    rw [e] at h1
    have : cp.E X ≤ 1 / 2 + 1 / 2 * cp.E (fun σ => X σ ^ 2) := h1
    nlinarith
  -- weights
  set lam : cp.N v → Config cp.V → ℝ := fun i σ => 5 * (p : ℝ) * cp.endLam σ v i with hlam
  have hl0 : ∀ i σ, 0 ≤ lam i σ := fun i σ =>
    mul_nonneg (by positivity) (cp.endLam_nonneg hR σ v i)
  have hmoml : ∀ i, ∀ n : ℕ, 1 ≤ n → 2 * n ≤ p →
      cp.E (fun σ => lam i σ ^ n) ≤ (41 * (p : ℝ) * aOf d p) ^ n :=
    fun i n hn1 hn => cp.endLam_moment hR hv i hn1 hn
  have hend : ∀ j ∈ (retIdx (kStarA d p) : Finset (cp.N v → ℕ)), 1 ≤ grade j → ∀ σ,
      0 < wt cp.G p (aOf d p) cp.yp cp.ym σ cp.S →
        |dEven (cp.lN v) j (F σ) (cp.xi σ v)| ≤
          X σ * starPhi p (cp.A σ v) (cp.B σ v) (cp.xi σ v) * ∏ i, lam i σ ^ (2 * j i) := by
    intro j _ _ σ hσ
    have hσc := cp.wtCore_ne_zero_of_wt hR hv hσ.ne'
    obtain ⟨hP, hQ⟩ := hpsd σ hσc
    obtain ⟨⟨hα, hP1, hP2⟩, ⟨hβ, hQ1, hQ2⟩⟩ := hmaj σ hσ.ne'
    obtain ⟨hH0, hHα⟩ := hH σ hσ.ne'
    rw [hFs σ hσc, hXs σ hσ.ne', ← hphi σ, SecA.CA.starPhi_eq_of_pos hα hβ]
    have htr := hP.trace_nonneg
    have hq := qForm_nonneg hP (cp.xi σ v)
    have hg : QuadMaj (P σ).trace 0 (-(P σ)) (cp.xi σ v) (1 + (P σ).trace)
        (cp.endLam σ v) := by
      refine SecA.CA.QuadMaj.mono' (SecA.CA.quadMaj_one_sub (SecA.CA.psd_symm hP) hα hP1 hP2)
        (cp.endLam_nonneg hR σ v) (by linarith) ?_
      have e : quadFn (P σ).trace 0 (-(P σ)) (cp.xi σ v) =
          (P σ).trace - qForm (P σ) (cp.xi σ v) := by
        simp only [quadFn, zero_dotProduct, add_zero, SecA.CA.qForm_neg]
        ring
      rw [e, abs_le]
      constructor <;> linarith
    have h := SecA.CA.endpoint_package (SecA.CA.psd_symm hP) (SecA.CA.psd_symm hQ)
      (Nat.sub_le p 1) le_rfl hp2 hα hβ (cp.endLam_nonneg hR σ v) hP1 hP2 hQ1 hQ2 hg j
    refine h.trans ?_
    set α := 1 - qForm (P σ) (cp.xi σ v) with hαdef
    set β := 1 - qForm (Q σ) (cp.xi σ v) with hβdef
    have hpow : α ^ p = α ^ (p - 1) * α := by rw [← pow_succ, Nat.sub_add_cancel hp1]
    have hPi : 0 ≤ ∏ i, (5 * (p : ℝ) * cp.endLam σ v i) ^ (2 * j i) :=
      Finset.prod_nonneg fun i _ => pow_nonneg (hl0 i σ) _
    have hK : 0 ≤ (1 + (P σ).trace) * α ^ (p - 1) * β ^ p * ∏ i,
        (5 * (p : ℝ) * cp.endLam σ v i) ^ (2 * j i) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by linarith) (pow_nonneg hα.le _))
        (pow_nonneg hβ.le _)) hPi
    set Pr := ∏ i, (5 * (p : ℝ) * cp.endLam σ v i) ^ (2 * j i) with hPr
    calc (1 + (P σ).trace) * α ^ (p - 1) * β ^ p * Pr
        = (1 + (P σ).trace) * α ^ (p - 1) * β ^ p * Pr * 1 := by ring
      _ ≤ (1 + (P σ).trace) * α ^ (p - 1) * β ^ p * Pr * (α * (2 * H σ)) :=
          mul_le_mul_of_nonneg_left hHα hK
      _ = (1 + (P σ).trace) * (2 * H σ) * (α ^ p * β ^ p) * Pr := by rw [hpow]; ring
  -- the relative transfer
  obtain ⟨hdL, hdL4', hdL4⟩ := hR.endL_facts
  have hKk : 16 * 1 * kStarA d p ≤ p := by
    have h := hR.kStar_lt
    have hp6 : (10 : ℝ) ^ 6 ≤ p := by exact_mod_cast hR.treg.hp
    have : ((16 * 1 * kStarA d p : ℕ) : ℝ) ≤ p := by push_cast; linarith
    exact_mod_cast this
  have hT := cp.trans_rel hR hv F hFc m hm0 (M := 3) (by norm_num) hmom hsm hder hvan X lam
    hX0 hl0 1 le_rfl hKk (m₀ := 13) (θ := 13) (B := 5) (by norm_num) le_rfl (by norm_num)
    (by have := hR.treg.aOf_pos; positivity) hXm hX2 hmoml hend hdL hdL4
  have hfac : (13 : ℝ) * (13 : ℝ) ^ (-(1 / ((1 : ℕ) : ℝ))) * (5 : ℝ) ^ (1 / ((1 : ℕ) : ℝ)) = 5 := by
    simp only [Nat.cast_one, div_one, Real.rpow_neg_one, Real.rpow_one]
    norm_num
  rw [hfac] at hT
  have hFH := cp.FH_pos' hR hv
  -- back to `f₁`
  have e : cp.coreE v (fun σ => radE (f1Obs p (P σ) (Q σ)) - gaussE (f1Obs p (P σ) (Q σ))) =
      (-1) * cp.coreE v (fun σ => gaussE (F σ) - radE (F σ)) := by
    rw [← cp.coreE_fconst_mul]
    refine SecA.coreE_congr_of_supp cp.G fun σ hσ => ?_
    have hσ' : F σ = f1Obs p (P σ) (Q σ) := by rw [hF]; dsimp only; rw [ite_eq_left hσ]
    rw [hσ']
    ring
  rw [e, abs_mul, abs_neg, abs_one, one_mul]
  have h1 : |cp.coreE v (fun σ => gaussE (F σ) - radE (F σ))| ≤
      (2 * Real.exp 2 * 5 * ((d : ℝ) * (41 * (p : ℝ) * aOf d p) ^ 4) +
        3 * Real.exp (-(p : ℝ)) / d) * cp.FH v := by
    rw [abs_div, abs_of_pos hFH, div_le_iff₀ hFH] at hT
    exact hT
  refine h1.trans (mul_le_mul_of_nonneg_right ?_ hFH.le)
  have he2 : Real.exp 2 ≤ 739 / 100 := by
    have h := Real.exp_one_lt_d9
    have e : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    rw [e]
    have : Real.exp 1 ^ 2 ≤ 2.7182818286 ^ 2 := pow_le_pow_left₀ (Real.exp_pos 1).le h.le 2
    norm_num at this ⊢
    linarith
  have hep : Real.exp (-(p : ℝ)) / d ≤ (p : ℝ) ^ 4 / d := by
    refine div_le_div_of_nonneg_right ?_ hd.le
    have : Real.exp (-(p : ℝ)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have : (1 : ℝ) ≤ (p : ℝ) ^ 4 := one_le_pow₀ hR.one_le_p
    linarith
  have hp4 : 0 ≤ (p : ℝ) ^ 4 / d := by positivity
  have he20 := Real.exp_pos 2
  have hA : 2 * Real.exp 2 * 5 * ((d : ℝ) * (41 * (p : ℝ) * aOf d p) ^ 4) ≤
      2 * (739 / 100) * 5 * (41 ^ 4 / 4 * ((p : ℝ) ^ 4 / d)) := by
    have h0 : 0 ≤ (d : ℝ) * (41 * (p : ℝ) * aOf d p) ^ 4 := by positivity
    calc 2 * Real.exp 2 * 5 * ((d : ℝ) * (41 * (p : ℝ) * aOf d p) ^ 4)
        ≤ 2 * (739 / 100) * 5 * ((d : ℝ) * (41 * (p : ℝ) * aOf d p) ^ 4) := by gcongr
      _ ≤ 2 * (739 / 100) * 5 * (41 ^ 4 / 4 * ((p : ℝ) ^ 4 / d)) := by gcongr
  rw [show (10 : ℝ) ^ 8 * (p : ℝ) ^ 4 / d = 10 ^ 8 * ((p : ℝ) ^ 4 / d) by ring]
  have hB : 3 * Real.exp (-(p : ℝ)) / d ≤ 3 * ((p : ℝ) ^ 4 / d) := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hep (by norm_num)
  have hcoef : (2 * (739 / 100) * 5 * (41 ^ 4 / 4) + 3 : ℝ) ≤ 10 ^ 8 := by norm_num
  have hC := mul_le_mul_of_nonneg_right hcoef hp4
  linarith [hA, hB, hC]

end BiluLinial.Tight.CapPoint

namespace BiluLinial.Tight

open Matrix

theorem SecA.CA.wK_mem {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℝ}
    (hA : A.PosSemidef) : 0 ≤ wK A ∧ wK A ≤ A.trace := by
  have h0 := hA.trace_nonneg
  have hT := trace_mul_nonneg hA hA
  have hT2 := trace_mul_le_trace_mul_trace hA hA
  refine ⟨div_nonneg hT (by linarith), ?_⟩
  rw [wK, div_le_iff₀ (by linarith)]
  nlinarith

/-- The interpolation exponent `K = ⌊log d/300⌋` of `A-WHITEN`: `1 ≤ K`, `16 K k_* ≤ p` and
`ϑ^{-1/K} 2^{1/K} ≤ 2 e^{12000}`. -/
theorem RegA.whitenK_facts {d p : ℕ} (hR : RegA d p) :
    1 ≤ ⌊Real.log d / 300⌋₊ ∧ 16 * ⌊Real.log d / 300⌋₊ * kStarA d p ≤ p ∧
      vth d ^ (-(1 / (⌊Real.log d / 300⌋₊ : ℝ))) * (2 : ℝ) ^ (1 / (⌊Real.log d / 300⌋₊ : ℝ)) ≤
        2 * Real.exp 12000 := by
  have hd := hR.d_pos
  have hp := hR.p_pos
  have hL400 : 400 ≤ Real.log d := hR.logd
  have hLp : 120 * Real.log d ≤ p := hR.plog
  have hLpos : 0 < Real.log d := by linarith
  set L := Real.log d with hL
  set K := ⌊L / 300⌋₊ with hK
  have hK1 : 1 ≤ K := Nat.le_floor (by rw [Nat.cast_one, le_div_iff₀ (by norm_num)]; linarith)
  have hKle : (K : ℝ) ≤ L / 300 := Nat.floor_le (by positivity)
  have hKgt : L / 300 - 1 < (K : ℝ) := by
    have := Nat.lt_floor_add_one (L / 300)
    linarith
  have hKL : L / 1200 ≤ (K : ℝ) := by linarith
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK1
  refine ⟨hK1, ?_, ?_⟩
  · have hk : (kStarA d p : ℝ) < 16 * (p : ℝ) / L + 1 := Nat.ceil_lt_add_one (by positivity)
    have hk0 : (0 : ℝ) ≤ kStarA d p := Nat.cast_nonneg _
    have h1 : (K : ℝ) * kStarA d p ≤ L / 300 * (16 * (p : ℝ) / L + 1) :=
      mul_le_mul hKle hk.le hk0 (by positivity)
    have e : L / 300 * (16 * (p : ℝ) / L + 1) = 16 * (p : ℝ) / 300 + L / 300 := by
      field_simp
    have : ((16 * K * kStarA d p : ℕ) : ℝ) ≤ p := by
      push_cast
      nlinarith
    exact_mod_cast this
  · have hθ : 0 < vth d := by unfold vth; positivity
    have e1 : vth d ^ (-(1 / (K : ℝ))) = Real.exp (10 * L / K) := by
      rw [Real.rpow_def_of_pos hθ, vth, one_div, Real.log_inv, Real.log_pow, ← hL]
      congr 1
      push_cast
      field_simp
    have h1 : Real.exp (10 * L / K) ≤ Real.exp 12000 := by
      refine Real.exp_le_exp.2 ?_
      rw [div_le_iff₀ hKpos]
      linarith
    have h2 : (2 : ℝ) ^ (1 / (K : ℝ)) ≤ 2 := by
      calc (2 : ℝ) ^ (1 / (K : ℝ)) ≤ (2 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num)
              (by rw [div_le_one hKpos]; exact_mod_cast hK1)
        _ = 2 := Real.rpow_one 2
    rw [e1]
    have h3 : 0 ≤ (2 : ℝ) ^ (1 / (K : ℝ)) := by positivity
    calc Real.exp (10 * L / K) * (2 : ℝ) ^ (1 / (K : ℝ)) ≤ Real.exp 12000 * 2 :=
          mul_le_mul h1 h2 h3 (Real.exp_pos _).le
      _ = 2 * Real.exp 12000 := by ring

/-- The error arithmetic of `A-WHITEN`. -/
theorem whiten_arith {d p : ℕ} (hR : RegA d p) {Ew : ℝ} (hEw0 : 0 ≤ Ew) :
    2 * Real.exp 2 * ((Ew + vth d) * vth d ^ (-(1 / (⌊Real.log d / 300⌋₊ : ℝ))) *
        (2 : ℝ) ^ (1 / (⌊Real.log d / 300⌋₊ : ℝ))) * ((d : ℝ) * (41 * (p : ℝ) * aOf d p) ^ 4) +
      2 * Real.exp (-(p : ℝ)) / d ≤
      3 * 10 ^ 6 * Real.exp 12002 * ((p : ℝ) ^ 4 / d) * (Ew + vth d) := by
  have hd := hR.d_pos
  have hθ : 0 < vth d := by unfold vth; positivity
  obtain ⟨-, hdL4', -⟩ := hR.endL_facts
  obtain ⟨-, -, hKθ⟩ := hR.whitenK_facts
  have he2 : Real.exp 2 * Real.exp 12000 = Real.exp 12002 := by rw [← Real.exp_add]; norm_num
  have hm0 : 0 ≤ Ew + vth d := by linarith
  have hp4 : 0 ≤ (p : ℝ) ^ 4 / d := by positivity
  have hA : 2 * Real.exp 2 * ((Ew + vth d) * vth d ^ (-(1 / (⌊Real.log d / 300⌋₊ : ℝ))) *
        (2 : ℝ) ^ (1 / (⌊Real.log d / 300⌋₊ : ℝ))) * ((d : ℝ) * (41 * (p : ℝ) * aOf d p) ^ 4) ≤
      (2 * Real.exp 2 * (2 * Real.exp 12000) * (41 ^ 4 / 4)) * (((p : ℝ) ^ 4 / d) * (Ew + vth d)) := by
    have h0 : 0 ≤ (d : ℝ) * (41 * (p : ℝ) * aOf d p) ^ 4 := by positivity
    have e : (Ew + vth d) * vth d ^ (-(1 / (⌊Real.log d / 300⌋₊ : ℝ))) *
        (2 : ℝ) ^ (1 / (⌊Real.log d / 300⌋₊ : ℝ)) = (Ew + vth d) *
          (vth d ^ (-(1 / (⌊Real.log d / 300⌋₊ : ℝ))) *
            (2 : ℝ) ^ (1 / (⌊Real.log d / 300⌋₊ : ℝ))) := by ring
    rw [e]
    have h1 := mul_le_mul_of_nonneg_left hKθ hm0
    have h2 : 0 ≤ (Ew + vth d) * (2 * Real.exp 12000) := by positivity
    calc 2 * Real.exp 2 * ((Ew + vth d) * (vth d ^ (-(1 / (⌊Real.log d / 300⌋₊ : ℝ))) *
          (2 : ℝ) ^ (1 / (⌊Real.log d / 300⌋₊ : ℝ)))) * ((d : ℝ) * (41 * (p : ℝ) * aOf d p) ^ 4)
        ≤ 2 * Real.exp 2 * ((Ew + vth d) * (2 * Real.exp 12000)) *
          ((d : ℝ) * (41 * (p : ℝ) * aOf d p) ^ 4) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (by positivity)) h0
      _ ≤ 2 * Real.exp 2 * ((Ew + vth d) * (2 * Real.exp 12000)) *
          (41 ^ 4 / 4 * ((p : ℝ) ^ 4 / d)) :=
          mul_le_mul_of_nonneg_left hdL4' (by positivity)
      _ = _ := by ring
  have hB : 2 * Real.exp (-(p : ℝ)) / d ≤ (p : ℝ) ^ 4 / d * vth d := by
    have hed : (d : ℝ) ^ 120 ≤ Real.exp p := by
      rw [← Real.exp_log (pow_pos hd 120), Real.log_pow]
      exact Real.exp_le_exp.mpr (by push_cast; linarith [hR.plog])
    have hd1 : (2 : ℝ) ≤ d := by have := hR.treg.ten_pow_six_le_d; linarith
    have hep : Real.exp (-(p : ℝ)) ≤ 1 / (d : ℝ) ^ 120 := by
      rw [Real.exp_neg, inv_eq_one_div]
      exact one_div_le_one_div_of_le (pow_pos hd 120) hed
    have hp4' : (1 : ℝ) ≤ (p : ℝ) ^ 4 := one_le_pow₀ hR.one_le_p
    have h3 : (2 : ℝ) ≤ (d : ℝ) ^ 110 :=
      hd1.trans (le_self_pow₀ (by linarith) (by norm_num))
    have h4 : 2 * (d : ℝ) ^ 10 ≤ (d : ℝ) ^ 120 := by
      calc 2 * (d : ℝ) ^ 10 ≤ (d : ℝ) ^ 110 * (d : ℝ) ^ 10 :=
            mul_le_mul_of_nonneg_right h3 (by positivity)
        _ = (d : ℝ) ^ 120 := by rw [← pow_add]
    have h2 : 2 * (1 / (d : ℝ) ^ 120) ≤ vth d := by
      rw [vth, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      linarith
    have h5 : 2 * Real.exp (-(p : ℝ)) ≤ vth d := by linarith
    calc 2 * Real.exp (-(p : ℝ)) / d ≤ vth d / d := div_le_div_of_nonneg_right h5 hd.le
      _ ≤ (p : ℝ) ^ 4 * vth d / d :=
          div_le_div_of_nonneg_right (le_mul_of_one_le_left hθ.le hp4') hd.le
      _ = (p : ℝ) ^ 4 / d * vth d := by ring
  have hcoef : 2 * Real.exp 2 * (2 * Real.exp 12000) * (41 ^ 4 / 4) + 1 ≤
      3 * 10 ^ 6 * Real.exp 12002 := by
    have h1 : 1 ≤ Real.exp 12002 := Real.one_le_exp (by norm_num)
    have e : 2 * Real.exp 2 * (2 * Real.exp 12000) * (41 ^ 4 / 4) =
        41 ^ 4 * (Real.exp 2 * Real.exp 12000) := by ring
    rw [e, he2]
    nlinarith
  have hv : (p : ℝ) ^ 4 / d * vth d ≤ (p : ℝ) ^ 4 / d * (Ew + vth d) :=
    mul_le_mul_of_nonneg_left (by linarith) hp4
  have hX := mul_le_mul_of_nonneg_right hcoef (mul_nonneg hp4 hm0)
  have e2 : 3 * 10 ^ 6 * Real.exp 12002 * ((p : ℝ) ^ 4 / d) * (Ew + vth d) =
      3 * 10 ^ 6 * Real.exp 12002 * (((p : ℝ) ^ 4 / d) * (Ew + vth d)) := by ring
  rw [e2]
  linarith [hA, hB, hv, hX]

namespace CapPoint

variable {d p : ℕ} (cp : CapPoint.{u} d p)

/-- `A-WHITEN`, one branch, generic in the pair `(P, Q) = (A, B)` or `(B, A)`:
`E_H w(P) ≤ E_{ν_K}[w(P) 𝖦Φ]/F_H + 3·10⁶ e^{12002} (p⁴/d)(E_H w(P) + ϑ)`. Proof: `A-INS`
(`E_H w = E_{ν_K} 𝖱[wΦ]/F_H`, `A-RET` with `j = 0`) and `A-TRANSR` on `wΦ` with sup majorant
`w ≤ tr P` (`A-E5`), endpoint majorant `w` (`A-MAJ`, F1), `m = E w + ϑ`, `B = 2`,
`K = ⌊log d/300⌋`. -/
theorem whiten_gen (hR : RegA d p) {v : cp.V} (hv : v ∈ cp.S)
    (P Q : Config cp.V → Matrix (cp.N v) (cp.N v) ℝ)
    (hPQ : (∀ σ, P σ = cp.A σ v ∧ Q σ = cp.B σ v) ∨ (∀ σ, P σ = cp.B σ v ∧ Q σ = cp.A σ v))
    (hmomP : ∀ n : ℕ, 1 ≤ n → 2 * n ≤ p → cp.coreE v (fun σ =>
      (if wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v ≠ 0 then (P σ).trace else 0) ^ n) ≤
        (1 + 2 * epsP d p) ^ n)
    (hEP2 : cp.E (fun σ => (P σ).trace ^ 2) ≤ (1 + 2 * epsP d p) ^ 2) :
    cp.E (fun σ => wK (P σ)) ≤
      cp.coreE v (fun σ => (if wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v ≠ 0 then
          wK (P σ) else 0) * gaussE (starPhi p (P σ) (Q σ))) / cp.FH v +
        3 * 10 ^ 6 * Real.exp 12002 * ((p : ℝ) ^ 4 / d) * (cp.E (fun σ => wK (P σ)) + vth d) := by
  have hd := hR.d_pos
  have hp := hR.p_pos
  have hp1 : 1 ≤ p := le_trans (by norm_num) hR.treg.two_le_p
  have hp2 : 2 ≤ p := hR.treg.two_le_p
  have hk7 := hR.four_kStar_add_seven_le
  have hε0 := SecA.epsP_nonneg hR.treg
  have hε1 := SecA.epsP_le hR.treg
  have hw : ∀ σ, 0 ≤ wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v :=
    fun σ => SecA.wtCore_nonneg cp.G _ _ _ _ σ _ _
  have hwt : ∀ σ, 0 ≤ wt cp.G p (aOf d p) cp.yp cp.ym σ cp.S := fun σ => wt_nonneg cp.G σ
  have hZ := cp.Zw_pos hR
  obtain ⟨hpsd, hcong, hphi, hb, hmaj⟩ := cp.pair_facts hR hv P Q hPQ
  set k := kStarA d p with hk
  have hN1 : 4 * k + 4 < p := by omega
  -- the kernel, cut off to the core support
  set wv : Config cp.V → ℝ := fun σ =>
    if wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v ≠ 0 then wK (P σ) else 0 with hwv
  have hwvs : ∀ σ, wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v ≠ 0 → wv σ = wK (P σ) :=
    fun σ hσ => by rw [hwv]; dsimp only; rw [ite_eq_left hσ]
  have hwvn : ∀ σ, ¬ wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v ≠ 0 → wv σ = 0 :=
    fun σ hσ => by rw [hwv]; dsimp only; rw [ite_eq_right hσ]
  have hwv0 : ∀ σ, 0 ≤ wv σ := by
    intro σ
    by_cases hσ : wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v ≠ 0
    · rw [hwvs σ hσ]; exact (SecA.CA.wK_mem (hpsd σ hσ).1).1
    · rw [hwvn σ hσ]
  -- the family `F = w Φ`
  set F : Config cp.V → (cp.N v → ℝ) → ℝ := fun σ ξ =>
    wv σ * starPhi p (cp.A σ v) (cp.B σ v) ξ with hF
  have hFs : ∀ σ, wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v ≠ 0 →
      F σ = clipObs (quadFn (wv σ) 0 0) p p (cp.A σ v) (cp.B σ v) := fun σ _ =>
    SecA.CA.mul_starPhi_eq_clipObs p (wv σ) _ _
  have hFn : ∀ σ, ¬ wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v ≠ 0 → F σ = fun _ => 0 :=
    fun σ hσ => by funext ξ; rw [hF]; dsimp only; rw [hwvn σ hσ, zero_mul]
  have hmom : ∀ n : ℕ, 1 ≤ n → 2 * n ≤ p → cp.coreE v (fun σ => wv σ ^ n) ≤ 2 ^ n := by
    intro n hn1 hn
    have hpt : ∀ σ, 0 < wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v →
        wv σ ^ n ≤ (if wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v ≠ 0 then
          (P σ).trace else 0) ^ n := by
      intro σ hσ
      rw [hwvs σ hσ.ne', ite_eq_left hσ.ne']
      obtain ⟨h0, h1⟩ := SecA.CA.wK_mem (hpsd σ hσ.ne').1
      exact pow_le_pow_left₀ h0 h1 n
    have h1 := SecA.wavg_mono' hw hpt
    have h2 : wavg (fun ω => wtCore cp.G p (aOf d p) cp.yp cp.ym ω cp.S v)
        (fun ω => (if wtCore cp.G p (aOf d p) cp.yp cp.ym ω cp.S v ≠ 0 then (P ω).trace
          else 0) ^ n) ≤ (1 + 2 * epsP d p) ^ n := hmomP n hn1 hn
    have h3 : (1 + 2 * epsP d p) ^ n ≤ 2 ^ n := pow_le_pow_left₀ (by linarith) (by linarith) n
    exact h1.trans (h2.trans h3)
  have hFc : ∀ σ σ', AgreeOff v σ σ' → F σ = F σ' := by
    intro σ σ' h
    have h1 := SecA.wtCore_congr cp.G (p := p) (a := aOf d p) (yp := cp.yp) (ym := cp.ym)
      (S := cp.S) h
    obtain ⟨h2, -⟩ := hcong σ σ' h
    have h4 : cp.A σ v = cp.A σ' v := SecA.rootMat_congr cp.G h
    have h5 : cp.B σ v = cp.B σ' v := SecA.rootMat_congr cp.G h
    simp only [hF, hwv, h1, h2, h4, h5]
  have hpkg : ∀ σ, wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v ≠ 0 → _ := fun σ hσ =>
    SecA.CA.clip_package (cp.root_psd_core hσ).1 (cp.root_psd_core hσ).2 (N := 4 * k + 4) hN1
      hN1 le_rfl le_rfl hp2 (fun x _ _ => SecA.CA.quadMaj_const' (c := wv σ) (m := wv σ)
        (abs_of_nonneg (hwv0 σ)).le (fun i => Real.sqrt_nonneg _) x)
  have hsm : ∀ σ, SmoothBdd (4 * kStarA d p + 4) (F σ) := by
    intro σ
    by_cases hσ : wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v ≠ 0
    · rw [hFs σ hσ]; exact (hpkg σ hσ).1
    · rw [hFn σ hσ]; exact SecA.CA.smoothBdd_zero_fn _
  have hder : ∀ σ, ∀ j ∈ (topIdx (kStarA d p) : Finset (cp.N v → ℕ)), ∀ x,
      |dEven (cp.lN v) j (F σ) x| ≤
        wv σ * (5 * (p : ℝ)) ^ (2 * ∑ i, j i) * ∏ i, cp.bdiag σ v i ^ j i := by
    intro σ j hj x
    obtain ⟨hadm, hg⟩ := mem_topIdx.1 hj
    have hsum := SecA.sum_le_two_mul_grade' hadm
    by_cases hσ : wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v ≠ 0
    · rw [hFs σ hσ]
      exact (hpkg σ hσ).2.1 j (by omega) x
    · rw [hFn σ hσ, hwvn σ hσ, dEven_eq_pderivList, SecA.CA.pderivList_zero_fn]
      simp
  have hvan : ∀ σ, ∀ j ∈ (retIdx (kStarA d p) : Finset (cp.N v → ℕ)), ∀ ξ : cp.N v → ℝ,
      (∀ i, ξ i = 1 ∨ ξ i = -1) → starPhi p (cp.A σ v) (cp.B σ v) ξ = 0 →
        dEven (cp.lN v) j (F σ) ξ = 0 := by
    intro σ j hj ξ _ hΦ
    obtain ⟨hadm, hg⟩ := mem_retIdx.1 hj
    have hsum := SecA.sum_le_two_mul_grade' hadm
    by_cases hσ : wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v ≠ 0
    · rw [hFs σ hσ]
      exact (hpkg σ hσ).2.2 j (by omega) ξ (SecA.CA.one_le_of_starPhi_eq_zero hp1 hΦ)
    · rw [hFn σ hσ, dEven_eq_pderivList, SecA.CA.pderivList_zero_fn]
  -- moments of the endpoint majorant `X = w`
  have hEw0 : 0 ≤ cp.E wv := lawE_nonneg cp.G fun σ _ => hwv0 σ
  have hθ : 0 < vth d := by unfold vth; positivity
  have hX2 : cp.E (fun σ => wv σ ^ 2) ≤ 2 ^ 2 := by
    have hpt : ∀ σ, wt cp.G p (aOf d p) cp.yp cp.ym σ cp.S ≠ 0 →
        wv σ ^ 2 ≤ (P σ).trace ^ 2 := by
      intro σ hσ
      have hσc := cp.wtCore_ne_zero_of_wt hR hv hσ
      rw [hwvs σ hσc]
      obtain ⟨h0, h1⟩ := SecA.CA.wK_mem (hpsd σ hσc).1
      exact pow_le_pow_left₀ h0 h1 2
    have h1 := SecA.lawE_le_of_supp cp.G hpt
    have h3 : (1 + 2 * epsP d p) ^ 2 ≤ 2 ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    exact h1.trans (hEP2.trans h3)
  -- weights
  set lam : cp.N v → Config cp.V → ℝ := fun i σ => 5 * (p : ℝ) * cp.endLam σ v i with hlam
  have hl0 : ∀ i σ, 0 ≤ lam i σ := fun i σ =>
    mul_nonneg (by positivity) (cp.endLam_nonneg hR σ v i)
  have hmoml : ∀ i, ∀ n : ℕ, 1 ≤ n → 2 * n ≤ p →
      cp.E (fun σ => lam i σ ^ n) ≤ (41 * (p : ℝ) * aOf d p) ^ n :=
    fun i n hn1 hn => cp.endLam_moment hR hv i hn1 hn
  have hend : ∀ j ∈ (retIdx (kStarA d p) : Finset (cp.N v → ℕ)), 1 ≤ grade j → ∀ σ,
      0 < wt cp.G p (aOf d p) cp.yp cp.ym σ cp.S →
        |dEven (cp.lN v) j (F σ) (cp.xi σ v)| ≤
          wv σ * starPhi p (cp.A σ v) (cp.B σ v) (cp.xi σ v) * ∏ i, lam i σ ^ (2 * j i) := by
    intro j _ _ σ hσ
    have hσc := cp.wtCore_ne_zero_of_wt hR hv hσ.ne'
    obtain ⟨hA, hB⟩ := cp.root_psd_core hσc
    obtain ⟨⟨hα, hA1, hA2⟩, ⟨hβ, hB1, hB2⟩⟩ := cp.endLam_maj hR hv hσ.ne'
    rw [hFs σ hσc, SecA.CA.starPhi_eq_of_pos hα hβ]
    calc _ ≤ _ := SecA.CA.endpoint_package (SecA.CA.psd_symm hA) (SecA.CA.psd_symm hB) le_rfl
          le_rfl hp2 hα hβ (cp.endLam_nonneg hR σ v) hA1 hA2 hB1 hB2
          (SecA.CA.quadMaj_const' (abs_of_nonneg (hwv0 σ)).le (cp.endLam_nonneg hR σ v) _) j
      _ = _ := by simp only [hlam]; ring
  -- the relative transfer with `K = ⌊log d/300⌋`
  obtain ⟨hdL, hdL4', hdL4⟩ := hR.endL_facts
  obtain ⟨hK1, hKk, hKθ⟩ := hR.whitenK_facts
  have hT := cp.trans_rel hR hv F hFc wv hwv0 (M := 2) (by norm_num) hmom hsm hder hvan wv lam
    hwv0 hl0 _ hK1 hKk (m₀ := cp.E wv + vth d) (θ := vth d) (B := 2) hθ (by linarith)
    (by norm_num) (by have := hR.treg.aOf_pos; positivity) (by linarith) hX2 hmoml hend hdL hdL4
  have hFH := cp.FH_pos' hR hv
  -- `E_H w = E_{ν_K} 𝖱[wΦ]/F_H` (`A-RET` with `R = wΦ`)
  have hret := cp.coreE_radE_div_eq hR hv F hFc (fun σ ξ _ hΦ => by
    show wv σ * starPhi p (cp.A σ v) (cp.B σ v) ξ = 0
    rw [hΦ, mul_zero])
  have hEw : cp.E (fun σ => wK (P σ)) = cp.E wv :=
    lawE_congr cp.G fun σ hσ => (hwvs σ (cp.wtCore_ne_zero_of_wt hR hv hσ)).symm
  have hEw' : cp.E (fun σ => F σ (cp.xi σ v) / starPhi p (cp.A σ v) (cp.B σ v) (cp.xi σ v)) =
      cp.E wv := by
    refine lawE_congr cp.G fun σ hσ => ?_
    have hΦ := cp.starPhi_xi_pos hR hv hσ
    show wv σ * starPhi p (cp.A σ v) (cp.B σ v) (cp.xi σ v) /
      starPhi p (cp.A σ v) (cp.B σ v) (cp.xi σ v) = wv σ
    rw [mul_div_assoc, div_self hΦ.ne', mul_one]
  rw [hEw'] at hret
  -- `𝖦F = w 𝖦Φ`
  have hG : cp.coreE v (fun σ => gaussE (F σ)) = cp.coreE v (fun σ =>
      (if wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v ≠ 0 then wK (P σ) else 0) *
        gaussE (starPhi p (P σ) (Q σ))) := by
    refine congrArg _ (funext fun σ => ?_)
    show ∫ x, wv σ * starPhi p (cp.A σ v) (cp.B σ v) x ∂(gaussPi _) =
      wv σ * gaussE (starPhi p (P σ) (Q σ))
    rw [MeasureTheory.integral_const_mul]
    congr 1
    show gaussE (starPhi p (cp.A σ v) (cp.B σ v)) = gaussE (starPhi p (P σ) (Q σ))
    congr 1
    funext x
    exact (hphi σ x).symm
  -- assemble
  have hsplit : cp.coreE v (fun σ => radE (F σ)) =
      cp.coreE v (fun σ => gaussE (F σ)) - cp.coreE v (fun σ => gaussE (F σ) - radE (F σ)) := by
    rw [show (fun σ => radE (F σ)) = fun σ => gaussE (F σ) - (gaussE (F σ) - radE (F σ)) by
      funext σ; ring]
    exact SecA.wavg_sub _ _ _
  have hmain : cp.E wv = cp.coreE v (fun σ => gaussE (F σ)) / cp.FH v -
      cp.coreE v (fun σ => gaussE (F σ) - radE (F σ)) / cp.FH v := by
    rw [← hret, hsplit, sub_div]
  rw [hEw, ← hG]
  have hT' := (abs_le.1 hT).1
  have harith := whiten_arith hR hEw0
  linarith [hT', hmain, harith]

end CapPoint

end BiluLinial.Tight

namespace BiluLinial.Tight.CapPoint

variable {d p : ℕ} (cp : CapPoint.{u} d p)

/-- `1/α_A = D_v h⁺_v ≤ 2 h⁺_v` and `1/α_B ≤ 2 h⁻_v` at a supported signing (F1, `D_v ≤ 2`). -/
theorem alpha_two_h (hR : RegA d p) {v : cp.V} (hv : v ∈ cp.S) {σ : Config cp.V}
    (hσ : wt cp.G p (aOf d p) cp.yp cp.ym σ cp.S ≠ 0) :
    (0 ≤ cp.hp σ v ∧ 1 ≤ (1 - qForm (cp.A σ v) (cp.xi σ v)) * (2 * cp.hp σ v)) ∧
      (0 ≤ cp.hm σ v ∧ 1 ≤ (1 - qForm (cp.B σ v) (cp.xi σ v)) * (2 * cp.hm σ v)) := by
  obtain ⟨hPp, hPm⟩ := cp.precN_pd_of_wt hσ
  have key : ∀ (τ : ℝ) (y : cp.V → ℝ), τ ^ 2 = 1 → InCube (sOf d p) y →
      (precN cp.G (aOf d p) τ y σ cp.S).PosDef →
      0 ≤ hN cp.G (aOf d p) τ y σ cp.S v ∧
        1 ≤ (1 - qForm (rootMat cp.G (aOf d p) τ y σ cp.S v) (rootSigns cp.G σ cp.S v)) *
          (2 * hN cp.G (aOf d p) τ y σ cp.S v) := by
    intro τ y hτ hy hP
    have hy0 : ∀ j, 0 ≤ y j := fun j => (hy j).1
    obtain ⟨h1, -, -⟩ := SecA.CA.root_F1' cp.G hτ hy0 hv hP
    have hg : 0 < hN cp.G (aOf d p) τ y σ cp.S v := hP.inv.diag_pos
    have hD1 := FloorIns.one_le_diagD cp.G (aOf d p) hy0 cp.S v
    have hD2 := SecA.diagD_le_two cp.G hR.treg cp.ctx.deg hy cp.S v
    refine ⟨hg.le, ?_⟩
    set α := 1 - qForm (rootMat cp.G (aOf d p) τ y σ cp.S v) (rootSigns cp.G σ cp.S v)
    have hDg : 0 < diagD cp.G (aOf d p) y cp.S v * hN cp.G (aOf d p) τ y σ cp.S v :=
      mul_pos (by linarith) hg
    have hα : 0 < α := by
      by_contra hc
      push Not at hc
      nlinarith
    have := mul_le_mul_of_nonneg_left hD2 (mul_nonneg hα.le hg.le)
    nlinarith
  exact ⟨key 1 cp.yp (by norm_num) (cp.inCube_yp hR) hPp,
    key (-1) cp.ym (by norm_num) (cp.inCube_ym hR) hPm⟩

end BiluLinial.Tight.CapPoint
