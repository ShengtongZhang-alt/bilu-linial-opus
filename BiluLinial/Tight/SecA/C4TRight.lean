/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecA.C4TTrans
public import BiluLinial.Tight.SecA.ShiftC5

/-!
# The right-hand observables of (C4) (sub-nodes `A-C4T-T12`, `A-C4T-T34` of `A-C4T`)

Source lines 480–520; AUDIT-A §2.13. For `0 ⪯ M ⪯ A` on the core support, with `T₁ = tr(MA)`,
`T₂ = tr(MB)`, `Θ = tr(A² + B²)`:

* star level: `quadMaj_pair` (the prefactor `T₁(1 - q_B) + T₂(1 - q_A)` of
  `F₁₂ = T₁α^{p-1}β^p + T₂α^pβ^{p-1}` has majorant scale `T₁ + T₂` for any weights dominating
  `|(Ax)_i|`, `|A_ik|`, `|(Bx)_i|`, `|B_ik|`), `quadMaj_dom` (`q_L` with `0 ⪯ L ⪯ ΘQ` has scale
  `Θ` for weights with `Q_ii ≤ λ_i²`), `trace_mul_self_le_sq` (`tr A² ≤ (tr A)²`);
* moments: `Θ ≤ (tr A + tr B)²`, so `E_{ν_K} Θⁿ, E Θⁿ ≤ (4(1+2ε)²)ⁿ` for `4n ≤ p`
  (`coreE_Theta_pow_le`, `E_Theta_pow_le`); T.IL with `E Θ ≤ C(ρ + b₀)` (`A-C3b`):
  `E[Θ Y] ≤ 12 C(ρ+b₀) B_Y` for `E Y^{2k} ≤ B_Y^{2k}`, `k = ⌈log d⌉` (`E_Theta_mul_le`);
* `trans_pair` (`A-C4T-T12`): `clip_trans_rel` with sup and endpoint scale `T₁ + T₂ ≤ 2Θ`
  (`A-PDOM`), relative factor `(T₁ + T₂)τ⁺τ⁻ ≤ Θ·2τ⁺τ⁻`.
-/

@[expose] public section

universe u

namespace BiluLinial.Tight

open Matrix

namespace SecA.C4

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- `tr A² ≤ (tr A)²` for `A ⪰ 0`. -/
theorem trace_mul_self_le_sq {A : Matrix ι ι ℝ} (hA : A.PosSemidef) :
    (A * A).trace ≤ A.trace ^ 2 := by
  have e1 : (A * A).trace = ∑ i, ∑ k, A i k ^ 2 := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by
      rw [SecA.CA.psd_symm hA k i]; ring
  have e2 : A.trace ^ 2 = ∑ i, ∑ k, A i i * A k k := by
    rw [Matrix.trace, sq, Finset.sum_mul_sum]
    rfl
  rw [e1, e2]
  exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ => SecA.CA.psd_apply_sq_le' hA i k

omit [DecidableEq ι] in
/-- The majorant condition for `T₁(1 - q_B) + T₂(1 - q_A)` with scale `T₁ + T₂`. -/
theorem quadMaj_pair {A B : Matrix ι ι ℝ} (hAs : ∀ i k, A i k = A k i)
    (hBs : ∀ i k, B i k = B k i) {T₁ T₂ : ℝ} (hT₁ : 0 ≤ T₁) (hT₂ : 0 ≤ T₂) {x lam : ι → ℝ}
    (hlam : ∀ i, 0 ≤ lam i) (hqA : 0 ≤ qForm A x) (hqA1 : qForm A x ≤ 1)
    (hqB : 0 ≤ qForm B x) (hqB1 : qForm B x ≤ 1)
    (hA1 : ∀ i, |(A *ᵥ x) i| ≤ lam i) (hA2 : ∀ i k, |A i k| ≤ lam i * lam k)
    (hB1 : ∀ i, |(B *ᵥ x) i| ≤ lam i) (hB2 : ∀ i k, |B i k| ≤ lam i * lam k) :
    QuadMaj (T₁ + T₂) 0 (-(T₁ • B + T₂ • A)) x (T₁ + T₂) lam := by
  have hT : (-(T₁ • B + T₂ • A) + (-(T₁ • B + T₂ • A))ᵀ) *ᵥ x =
      (-2 : ℝ) • (T₁ • (B *ᵥ x) + T₂ • (A *ᵥ x)) := by
    have e : -(T₁ • B + T₂ • A) + (-(T₁ • B + T₂ • A))ᵀ = (-2 : ℝ) • (T₁ • B + T₂ • A) := by
      ext i k
      simp only [Matrix.add_apply, Matrix.neg_apply, Matrix.transpose_apply, Matrix.smul_apply,
        smul_eq_mul, hAs k i, hBs k i]
      ring
    rw [e, Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec]
  refine ⟨?_, fun i => ?_, fun i k => ?_⟩
  · have e : quadFn (T₁ + T₂) 0 (-(T₁ • B + T₂ • A)) x =
        T₁ * (1 - qForm B x) + T₂ * (1 - qForm A x) := by
      simp only [quadFn, qForm, zero_dotProduct, add_zero, Matrix.neg_mulVec, Matrix.add_mulVec,
        Matrix.smul_mulVec, dotProduct_neg, dotProduct_add, dotProduct_smul, smul_eq_mul]
      ring
    rw [e, abs_le]
    constructor <;> nlinarith
  · rw [hT]
    simp only [Pi.zero_apply, zero_add, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    have h : |T₁ * (B *ᵥ x) i + T₂ * (A *ᵥ x) i| ≤ (T₁ + T₂) * lam i := by
      calc _ ≤ |T₁ * (B *ᵥ x) i| + |T₂ * (A *ᵥ x) i| := abs_add_le _ _
        _ = T₁ * |(B *ᵥ x) i| + T₂ * |(A *ᵥ x) i| := by
            rw [abs_mul, abs_mul, abs_of_nonneg hT₁, abs_of_nonneg hT₂]
        _ ≤ T₁ * lam i + T₂ * lam i :=
            add_le_add (mul_le_mul_of_nonneg_left (hB1 i) hT₁)
              (mul_le_mul_of_nonneg_left (hA1 i) hT₂)
        _ = _ := by ring
    rw [abs_mul, show |(-2 : ℝ)| = 2 by norm_num]
    linarith
  · simp only [Matrix.neg_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hAs k i,
      hBs k i]
    have h : |T₁ * B i k + T₂ * A i k| ≤ (T₁ + T₂) * (lam i * lam k) := by
      calc _ ≤ |T₁ * B i k| + |T₂ * A i k| := abs_add_le _ _
        _ = T₁ * |B i k| + T₂ * |A i k| := by
            rw [abs_mul, abs_mul, abs_of_nonneg hT₁, abs_of_nonneg hT₂]
        _ ≤ T₁ * (lam i * lam k) + T₂ * (lam i * lam k) :=
            add_le_add (mul_le_mul_of_nonneg_left (hB2 i k) hT₁)
              (mul_le_mul_of_nonneg_left (hA2 i k) hT₂)
        _ = _ := by ring
    rw [show -(T₁ * B i k + T₂ * A i k) + -(T₁ * B i k + T₂ * A i k) =
      -(2 * (T₁ * B i k + T₂ * A i k)) by ring, abs_neg, abs_mul, abs_two]
    linarith

/-- The majorant condition for `q_L` with `0 ⪯ L ⪯ ΘQ`, scale `Θ`, at a point with `q_Q ≤ 1`, for
weights with `Q_ii ≤ λ_i²`. -/
theorem quadMaj_dom {L Q : Matrix ι ι ℝ} (hL : L.PosSemidef) {Θ : ℝ} (hΘ : 0 ≤ Θ)
    (hdom : (Θ • Q - L).PosSemidef) {x lam : ι → ℝ} (hq : qForm Q x ≤ 1)
    (hlam : ∀ i, 0 ≤ lam i) (hQ : ∀ i, Q i i ≤ lam i ^ 2) :
    QuadMaj 0 0 L x Θ lam := by
  have hLs := SecA.CA.psd_symm hL
  have hqL := qForm_nonneg hL x
  have hqd : qForm L x ≤ Θ * qForm Q x := by
    have h := qForm_nonneg hdom x
    simp only [qForm, Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub,
      dotProduct_smul, smul_eq_mul] at h
    simp only [qForm]
    linarith
  have hqL1 : qForm L x ≤ Θ := by nlinarith
  have hdiag : ∀ i, L i i ≤ Θ * Q i i := fun i => by
    have h := hdom.diag_nonneg (i := i)
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at h
    linarith
  have hLd : ∀ i, 0 ≤ L i i := fun i => hL.diag_nonneg
  have hΘQ : ∀ i, L i i ≤ Θ * lam i ^ 2 := fun i =>
    (hdiag i).trans (mul_le_mul_of_nonneg_left (hQ i) hΘ)
  have hT : (L + Lᵀ) *ᵥ x = (2 : ℝ) • (L *ᵥ x) := by
    have e : L + Lᵀ = (2 : ℝ) • L := by
      ext i k
      simp only [Matrix.add_apply, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul,
        hLs k i]
      ring
    rw [e, Matrix.smul_mulVec]
  refine ⟨?_, fun i => ?_, fun i k => ?_⟩
  · have e : quadFn 0 0 L x = qForm L x := by simp [quadFn]
    rw [e, abs_of_nonneg hqL]
    exact hqL1
  · rw [hT]
    simp only [Pi.zero_apply, zero_add, Pi.smul_apply, smul_eq_mul, abs_mul, abs_two]
    have h1 := SecA.CA.mulVec_apply_sq_le' hL x i
    have h2 : |(L *ᵥ x) i| ^ 2 ≤ (Θ * lam i) ^ 2 := by
      rw [sq_abs]
      calc (L *ᵥ x) i ^ 2 ≤ L i i * qForm L x := h1
        _ ≤ (Θ * lam i ^ 2) * Θ := mul_le_mul (hΘQ i) hqL1 hqL (by positivity)
        _ = (Θ * lam i) ^ 2 := by ring
    have h3 := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hΘ (hlam i))).1 h2
    linarith
  · rw [hLs k i, show L i k + L i k = 2 * L i k by ring, abs_mul, abs_two]
    have h1 := SecA.CA.psd_apply_sq_le' hL i k
    have h2 : |L i k| ^ 2 ≤ (Θ * lam i * lam k) ^ 2 := by
      rw [sq_abs]
      calc L i k ^ 2 ≤ L i i * L k k := h1
        _ ≤ (Θ * lam i ^ 2) * (Θ * lam k ^ 2) :=
            mul_le_mul (hΘQ i) (hΘQ k) (hLd k) (by positivity)
        _ = (Θ * lam i * lam k) ^ 2 := by ring
    have h3 := (sq_le_sq₀ (abs_nonneg _)
      (mul_nonneg (mul_nonneg hΘ (hlam i)) (hlam k))).1 h2
    linarith

/-- Sup weights: at a point with `q_A(x), q_B(x) ≤ 1`, `|(Ax)_i|, |(Bx)_i| ≤ √(A_ii + B_ii)` and
`|A_ik|, |B_ik| ≤ √(A_ii + B_ii) √(A_kk + B_kk)` (`A, B ⪰ 0`). -/
theorem sup_weights {A B : Matrix ι ι ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef) {x : ι → ℝ}
    (hxA : qForm A x ≤ 1) (hxB : qForm B x ≤ 1) :
    (∀ i, |(A *ᵥ x) i| ≤ Real.sqrt (A i i + B i i)) ∧
      (∀ i k, |A i k| ≤ Real.sqrt (A i i + B i i) * Real.sqrt (A k k + B k k)) ∧
      (∀ i, |(B *ᵥ x) i| ≤ Real.sqrt (A i i + B i i)) ∧
      ∀ i k, |B i k| ≤ Real.sqrt (A i i + B i i) * Real.sqrt (A k k + B k k) := by
  have ha : ∀ i, A i i ≤ A i i + B i i := fun i => by linarith [hB.diag_nonneg (i := i)]
  have hb : ∀ i, B i i ≤ A i i + B i i := fun i => by linarith [hA.diag_nonneg (i := i)]
  have hs : ∀ i, 0 ≤ A i i + B i i := fun i => add_nonneg hA.diag_nonneg hB.diag_nonneg
  refine ⟨fun i => ?_, fun i k => ?_, fun i => ?_, fun i k => ?_⟩
  · have h1 := SecA.CA.mulVec_apply_sq_le' hA x i
    have hAi := hA.diag_nonneg (i := i)
    exact Real.abs_le_sqrt (by nlinarith [ha i, qForm_nonneg hA x])
  · rw [← Real.sqrt_mul (hs i)]
    exact Real.abs_le_sqrt ((SecA.CA.psd_apply_sq_le' hA i k).trans
      (mul_le_mul (ha i) (ha k) hA.diag_nonneg (hs i)))
  · have h1 := SecA.CA.mulVec_apply_sq_le' hB x i
    have hBi := hB.diag_nonneg (i := i)
    exact Real.abs_le_sqrt (by nlinarith [hb i, qForm_nonneg hB x])
  · rw [← Real.sqrt_mul (hs i)]
    exact Real.abs_le_sqrt ((SecA.CA.psd_apply_sq_le' hB i k).trans
      (mul_le_mul (hb i) (hb k) hB.diag_nonneg (hs i)))

end SecA.C4

namespace CapPoint

variable {d p : ℕ} (cp : CapPoint.{u} d p)

/-- `0 ≤ Θ ≤ (tr A + tr B)²` at a good core. -/
theorem Theta_le_sq {v : cp.V} {σ : Config cp.V}
    (hσ : wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v ≠ 0) :
    0 ≤ cp.Theta σ v ∧ cp.Theta σ v ≤ ((cp.A σ v).trace + (cp.B σ v).trace) ^ 2 := by
  obtain ⟨hA, hB⟩ := cp.root_psd_core hσ
  have h1 := SecA.C4.trace_mul_self_le_sq hA
  have h2 := SecA.C4.trace_mul_self_le_sq hB
  have h3 := hA.trace_nonneg
  have h4 := hB.trace_nonneg
  have e : cp.Theta σ v = (cp.A σ v * cp.A σ v).trace + (cp.B σ v * cp.B σ v).trace :=
    Matrix.trace_add _ _
  rw [e]
  exact ⟨add_nonneg (trace_mul_nonneg hA hA) (trace_mul_nonneg hB hB), by nlinarith⟩

/-- Own-core moments of `Θ`: `E_{ν_K} Θⁿ ≤ (4(1+2ε)²)ⁿ` (`4n ≤ p`, cut off to the core support). -/
theorem coreE_Theta_pow_le (hR : RegA d p) {v : cp.V} (hv : v ∈ cp.S) {n : ℕ} (hn1 : 1 ≤ n)
    (hn : 4 * n ≤ p) :
    cp.coreE v (fun σ => (if wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v ≠ 0 then
      cp.Theta σ v else 0) ^ n) ≤ (4 * (1 + 2 * epsP d p) ^ 2) ^ n := by
  have hw : ∀ σ, 0 ≤ wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v :=
    fun σ => SecA.wtCore_nonneg cp.G _ _ _ _ σ _ _
  have h2n : 1 ≤ 2 * n := by omega
  obtain ⟨mA, mB⟩ := cp.coreE_trace_pow_le hR hv h2n (by omega)
  set tA : Config cp.V → ℝ := fun σ =>
    if wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v ≠ 0 then (cp.A σ v).trace else 0 with htA
  set tB : Config cp.V → ℝ := fun σ =>
    if wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v ≠ 0 then (cp.B σ v).trace else 0 with htB
  have hpt : ∀ σ, 0 < wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v →
      (if wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v ≠ 0 then cp.Theta σ v else 0) ^ n ≤
        2 ^ (2 * n - 1) * (tA σ ^ (2 * n) + tB σ ^ (2 * n)) := by
    intro σ hσ
    obtain ⟨hA, hB⟩ := cp.root_psd_core hσ.ne'
    obtain ⟨h0, h1⟩ := cp.Theta_le_sq hσ.ne'
    rw [ite_eq_left hσ.ne']
    have etA : tA σ = (cp.A σ v).trace := by rw [htA]; dsimp only; rw [ite_eq_left hσ.ne']
    have etB : tB σ = (cp.B σ v).trace := by rw [htB]; dsimp only; rw [ite_eq_left hσ.ne']
    rw [etA, etB]
    calc cp.Theta σ v ^ n ≤ (((cp.A σ v).trace + (cp.B σ v).trace) ^ 2) ^ n :=
          pow_le_pow_left₀ h0 h1 n
      _ = ((cp.A σ v).trace + (cp.B σ v).trace) ^ (2 * n) := by rw [← pow_mul]
      _ ≤ _ := add_pow_le hA.trace_nonneg hB.trace_nonneg _
  have h1 := SecA.wavg_mono' hw hpt
  rw [SecA.wavg_const_mul, SecA.wavg_add] at h1
  refine h1.trans ?_
  have e2 : (2 : ℝ) ^ (2 * n - 1) * 2 = 2 ^ (2 * n) := by
    rw [← pow_succ, Nat.sub_add_cancel h2n]
  calc (2 : ℝ) ^ (2 * n - 1) * (cp.coreE v (fun σ => tA σ ^ (2 * n)) +
        cp.coreE v (fun σ => tB σ ^ (2 * n)))
      ≤ 2 ^ (2 * n - 1) * ((1 + 2 * epsP d p) ^ (2 * n) + (1 + 2 * epsP d p) ^ (2 * n)) :=
        mul_le_mul_of_nonneg_left (add_le_add mA mB) (by positivity)
    _ = (4 * (1 + 2 * epsP d p) ^ 2) ^ n := by
        rw [← two_mul, ← mul_assoc, e2, pow_mul, pow_mul, ← mul_pow]
        norm_num

/-- Actual moments of `Θ`: `E Θⁿ ≤ (4(1+2ε)²)ⁿ` (`4n ≤ p`). -/
theorem E_Theta_pow_le (hR : RegA d p) {v : cp.V} (hv : v ∈ cp.S) {n : ℕ} (hn1 : 1 ≤ n)
    (hn : 4 * n ≤ p) :
    cp.E (fun σ => cp.Theta σ v ^ n) ≤ (4 * (1 + 2 * epsP d p) ^ 2) ^ n := by
  have h2n : 1 ≤ 2 * n := by omega
  obtain ⟨mA, mB⟩ := cp.E_trace_pow_le hR hv h2n (by omega)
  have hpt : ∀ σ, wt cp.G p (aOf d p) cp.yp cp.ym σ cp.S ≠ 0 →
      cp.Theta σ v ^ n ≤
        2 ^ (2 * n - 1) * ((cp.A σ v).trace ^ (2 * n) + (cp.B σ v).trace ^ (2 * n)) := by
    intro σ hσ
    have hσc := cp.wtCore_ne_zero_of_wt hR hv hσ
    obtain ⟨hA, hB⟩ := cp.root_psd_core hσc
    obtain ⟨h0, h1⟩ := cp.Theta_le_sq hσc
    calc cp.Theta σ v ^ n ≤ (((cp.A σ v).trace + (cp.B σ v).trace) ^ 2) ^ n :=
          pow_le_pow_left₀ h0 h1 n
      _ = ((cp.A σ v).trace + (cp.B σ v).trace) ^ (2 * n) := by rw [← pow_mul]
      _ ≤ _ := add_pow_le hA.trace_nonneg hB.trace_nonneg _
  have h1 := SecA.lawE_le_of_supp cp.G hpt
  rw [lawE_const_mul, lawE_add] at h1
  refine h1.trans ?_
  have e2 : (2 : ℝ) ^ (2 * n - 1) * 2 = 2 ^ (2 * n) := by
    rw [← pow_succ, Nat.sub_add_cancel h2n]
  unfold CapPoint.E at mA mB
  calc (2 : ℝ) ^ (2 * n - 1) * (lawE cp.G p (aOf d p) cp.yp cp.ym cp.S
        (fun σ => (cp.A σ v).trace ^ (2 * n)) +
        lawE cp.G p (aOf d p) cp.yp cp.ym cp.S (fun σ => (cp.B σ v).trace ^ (2 * n)))
      ≤ 2 ^ (2 * n - 1) * ((1 + 2 * epsP d p) ^ (2 * n) + (1 + 2 * epsP d p) ^ (2 * n)) :=
        mul_le_mul_of_nonneg_left (add_le_add mA mB) (by positivity)
    _ = (4 * (1 + 2 * epsP d p) ^ 2) ^ n := by
        rw [← two_mul, ← mul_assoc, e2, pow_mul, pow_mul, ← mul_pow]
        norm_num

/-- `0 < τ^± ≤ 2 h^±_v` on the support. -/
theorem tau_le (hR : RegA d p) {v : cp.V} {σ : Config cp.V}
    (hσ : wt cp.G p (aOf d p) cp.yp cp.ym σ cp.S ≠ 0) :
    0 < cp.taup σ v ∧ cp.taup σ v ≤ 2 * cp.hp σ v ∧
      0 < cp.taum σ v ∧ cp.taum σ v ≤ 2 * cp.hm σ v := by
  obtain ⟨hPp, hPm⟩ := cp.precN_pd_of_wt hσ
  have hh1 : 0 < cp.hp σ v := hPp.inv.diag_pos
  have hh2 : 0 < cp.hm σ v := hPm.inv.diag_pos
  have hD1 : 1 ≤ diagD cp.G (aOf d p) cp.yp cp.S v :=
    FloorIns.one_le_diagD cp.G _ cp.yp_nonneg cp.S v
  have hD2 : 1 ≤ diagD cp.G (aOf d p) cp.ym cp.S v :=
    FloorIns.one_le_diagD cp.G _ cp.ym_nonneg cp.S v
  have hD1' := SecA.diagD_le_two cp.G hR.treg cp.ctx.deg (cp.inCube_yp hR) cp.S v
  have hD2' := SecA.diagD_le_two cp.G hR.treg cp.ctx.deg (cp.inCube_ym hR) cp.S v
  refine ⟨mul_pos (by linarith) hh1, ?_, mul_pos (by linarith) hh2, ?_⟩
  · exact mul_le_mul_of_nonneg_right hD1' hh1.le
  · exact mul_le_mul_of_nonneg_right hD2' hh2.le

/-- `E (2τ⁺τ⁻)ⁿ ≤ (8(1+2ε)²)ⁿ` (`4n ≤ p`). -/
theorem E_taupm_pow_le (hR : RegA d p) {v : cp.V} (hv : v ∈ cp.S) {n : ℕ} (hn1 : 1 ≤ n)
    (hn : 4 * n ≤ p) :
    cp.E (fun σ => (2 * cp.taup σ v * cp.taum σ v) ^ n) ≤ (8 * (1 + 2 * epsP d p) ^ 2) ^ n := by
  have h2n : 1 ≤ 2 * n := by omega
  obtain ⟨m1, m2⟩ := cp.h_moment hR hv h2n (by omega)
  have hpt : ∀ σ, wt cp.G p (aOf d p) cp.yp cp.ym σ cp.S ≠ 0 →
      (2 * cp.taup σ v * cp.taum σ v) ^ n ≤
        8 ^ n * (1 / 2) * (cp.hp σ v ^ (2 * n) + cp.hm σ v ^ (2 * n)) := by
    intro σ hσ
    obtain ⟨t1, t2, t3, t4⟩ := cp.tau_le hR hσ
    obtain ⟨hPp, hPm⟩ := cp.precN_pd_of_wt hσ
    have hh1 : 0 < cp.hp σ v := hPp.inv.diag_pos
    have hh2 : 0 < cp.hm σ v := hPm.inv.diag_pos
    have h1 : 2 * cp.taup σ v * cp.taum σ v ≤ 8 * (cp.hp σ v * cp.hm σ v) := by nlinarith
    have h2 : (cp.hp σ v * cp.hm σ v) ^ n ≤ (1 / 2) * (cp.hp σ v ^ (2 * n) + cp.hm σ v ^ (2 * n)) := by
      rw [mul_pow, pow_mul', pow_mul']
      nlinarith [sq_nonneg (cp.hp σ v ^ n - cp.hm σ v ^ n)]
    calc (2 * cp.taup σ v * cp.taum σ v) ^ n ≤ (8 * (cp.hp σ v * cp.hm σ v)) ^ n :=
          pow_le_pow_left₀ (by positivity) h1 n
      _ = 8 ^ n * (cp.hp σ v * cp.hm σ v) ^ n := mul_pow _ _ _
      _ ≤ 8 ^ n * ((1 / 2) * (cp.hp σ v ^ (2 * n) + cp.hm σ v ^ (2 * n))) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = _ := by ring
  have h1 := SecA.lawE_le_of_supp cp.G hpt
  rw [lawE_const_mul, lawE_add] at h1
  refine h1.trans ?_
  unfold CapPoint.E at m1 m2
  calc (8 : ℝ) ^ n * (1 / 2) * (lawE cp.G p (aOf d p) cp.yp cp.ym cp.S
        (fun σ => cp.hp σ v ^ (2 * n)) +
        lawE cp.G p (aOf d p) cp.yp cp.ym cp.S (fun σ => cp.hm σ v ^ (2 * n)))
      ≤ 8 ^ n * (1 / 2) * ((1 + 2 * epsP d p) ^ (2 * n) + (1 + 2 * epsP d p) ^ (2 * n)) :=
        mul_le_mul_of_nonneg_left (add_le_add m1 m2) (by positivity)
    _ = (8 * (1 + 2 * epsP d p) ^ 2) ^ n := by rw [mul_pow, pow_mul]; ring

/-- T.IL with `E Θ ≤ m`: `E[Θ Y] ≤ 12 m B_Y` if `0 ≤ Y` on the support and
`E Y^{2k} ≤ B_Y^{2k}`, `k = ⌈log d⌉`. -/
theorem E_Theta_mul_le (hR : RegA d p) {v : cp.V} (hv : v ∈ cp.S) {m : ℝ}
    (hEΘ : cp.E (fun σ => cp.Theta σ v) ≤ m) (hdm : 1 / (d : ℝ) ≤ m) (Y : Config cp.V → ℝ)
    (hY0 : ∀ σ, wt cp.G p (aOf d p) cp.yp cp.ym σ cp.S ≠ 0 → 0 ≤ Y σ) {BY : ℝ} (hBY : 0 ≤ BY)
    (hY : cp.E (fun σ => Y σ ^ (2 * ⌈Real.log d⌉₊)) ≤ BY ^ (2 * ⌈Real.log d⌉₊)) :
    cp.E (fun σ => cp.Theta σ v * Y σ) ≤ 12 * m * BY := by
  have hd := hR.d_pos
  have hε0 := SecA.epsP_nonneg hR.treg
  have hε1 := SecA.epsP_le hR.treg
  have hlog := hR.logd
  set k := ⌈Real.log d⌉₊ with hkdef
  have hk1 : 1 ≤ k := Nat.ceil_pos.2 (by linarith)
  have hkge : Real.log d ≤ k := Nat.le_ceil _
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
  have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  set c := 1 + 2 * epsP d p with hc
  have hp8 : 4 * 2 ≤ p := le_trans (by norm_num) hR.treg.hp
  have hX2 : cp.E (fun σ => cp.Theta σ v ^ 2) ≤ (4 * c ^ 2) ^ 2 := cp.E_Theta_pow_le hR hv
    (by norm_num) hp8
  have hint := SecA.lawE_mul_le_interp cp.G (cp.Zw_pos hR) (X := fun σ => cp.Theta σ v) (Y := Y)
    (fun σ hσ => (cp.Theta_le_sq (cp.wtCore_ne_zero_of_wt hR hv hσ)).1) hY0 hk1
    (θ := 1 / d) (m := m) (BX := 4 * c ^ 2) (BY := BY) (by positivity) hdm (by positivity)
    hBY hEΘ hX2 hY
  refine hint.trans ?_
  have hE : (1 / (d : ℝ)) ^ (-(1 / (k : ℝ))) ≤ 2.7182818286 := by
    rw [Real.rpow_def_of_pos (by positivity)]
    have hl : Real.log (1 / (d : ℝ)) = -Real.log d := by rw [one_div, Real.log_inv]
    rw [hl]
    have : -Real.log d * -(1 / (k : ℝ)) ≤ 1 := by
      rw [neg_mul_neg, mul_one_div, div_le_one hkpos]
      exact hkge
    exact (Real.exp_le_exp.2 this).trans Real.exp_one_lt_d9.le
  have hc2 : c ^ 2 ≤ 103 / 100 := by
    have : c ≤ 101 / 100 := by rw [hc]; linarith
    nlinarith
  have hB : (4 * c ^ 2) ^ (1 / (k : ℝ)) ≤ 4 * (103 / 100) := by
    have h1 : (1 : ℝ) ≤ 4 * c ^ 2 := by nlinarith
    calc (4 * c ^ 2) ^ (1 / (k : ℝ)) ≤ (4 * c ^ 2) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le h1 (by rw [div_le_one hkpos]; exact hk1')
      _ = 4 * c ^ 2 := Real.rpow_one _
      _ ≤ _ := by linarith
  have hm0 : 0 ≤ m := le_trans (by positivity) hdm
  have h0 : 0 ≤ (1 / (d : ℝ)) ^ (-(1 / (k : ℝ))) := by positivity
  have h1 : 0 ≤ (4 * c ^ 2) ^ (1 / (k : ℝ)) := by positivity
  calc m * (1 / (d : ℝ)) ^ (-(1 / (k : ℝ))) * (4 * c ^ 2) ^ (1 / (k : ℝ)) * BY
      ≤ m * 2.7182818286 * (4 * (103 / 100)) * BY := by
        refine mul_le_mul_of_nonneg_right ?_ hBY
        refine mul_le_mul ?_ hB h1 (by positivity)
        exact mul_le_mul_of_nonneg_left hE hm0
    _ ≤ 12 * m * BY := by nlinarith [mul_nonneg hm0 hBY]

/-- `vth d = d^{-10} ≤ 1/d`. -/
theorem vth_le_inv_d (hR : RegA d p) : vth d ≤ 1 / (d : ℝ) := by
  have hd1 : (1 : ℝ) ≤ d := by have := hR.treg.ten_pow_six_le_d; linarith
  exact one_div_le_one_div_of_le (by linarith) (le_self_pow₀ hd1 (by norm_num))

/-- `A-C4T-T12` at a capped point: the transfer of `F₁₂ = T₁α^{p-1}β^p + T₂α^pβ^{p-1}`, written as
the clipped observable `(T₁(1 - q_B) + T₂(1 - q_A)) α^{p-1} β^{p-1}` (`T₁ = tr(MA)`,
`T₂ = tr(MB)`). `clip_trans_rel` with sup/endpoint scale `T₁ + T₂ ≤ 2Θ` (`A-PDOM`), core moments
`≤ 9ⁿ`, relative factor `(T₁ + T₂)τ⁺τ⁻ ≤ Θ·Y`, `Y = 2τ⁺τ⁻`, `E[ΘY] ≤ 108 m` (T.IL with
`E Θ ≤ m`), `E[(ΘY)²] ≤ 90²`. -/
theorem trans_pair (hR : RegA d p) {v : cp.V} (hv : v ∈ cp.S)
    (M : Config cp.V → Matrix (cp.N v) (cp.N v) ℝ) (hMc : ∀ σ σ', AgreeOff v σ σ' → M σ = M σ')
    (hMpsd : ∀ σ, 0 < wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v →
      (M σ).PosSemidef ∧ (cp.A σ v - M σ).PosSemidef)
    {m : ℝ} (hEΘ : cp.E (fun σ => cp.Theta σ v) ≤ m) (hdm : 1 / (d : ℝ) ≤ m) :
    |cp.coreE v (fun σ =>
        gaussE (clipObs (quadFn ((M σ * cp.A σ v).trace + (M σ * cp.B σ v).trace) 0
          (-((M σ * cp.A σ v).trace • cp.B σ v + (M σ * cp.B σ v).trace • cp.A σ v)))
          (p - 1) (p - 1) (cp.A σ v) (cp.B σ v)) -
        radE (clipObs (quadFn ((M σ * cp.A σ v).trace + (M σ * cp.B σ v).trace) 0
          (-((M σ * cp.A σ v).trace • cp.B σ v + (M σ * cp.B σ v).trace • cp.A σ v)))
          (p - 1) (p - 1) (cp.A σ v) (cp.B σ v))) / cp.FH v| ≤
      2 * Real.exp 2 * (108 * m * (2 * Real.exp 12000) * 90) * (41 ^ 4 / 4 * ((p : ℝ) ^ 4 / d)) +
        9 * Real.exp (-(p : ℝ)) / d := by
  have hd := hR.d_pos
  have hp2 : 2 ≤ p := hR.treg.two_le_p
  have hε0 := SecA.epsP_nonneg hR.treg
  have hε1 := SecA.epsP_le hR.treg
  have hw : ∀ σ, 0 ≤ wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v :=
    fun σ => SecA.wtCore_nonneg cp.G _ _ _ _ σ _ _
  set c := 1 + 2 * epsP d p with hc
  have hc1 : 1 ≤ c := by linarith
  have hc9 : 8 * c ^ 2 ≤ 9 := by
    have : c ≤ 101 / 100 := by linarith
    nlinarith
  have hpp : p - (p - 1) = 1 := by omega
  have hm0 : 0 ≤ m := le_trans (by positivity) hdm
  -- pointwise facts on the core support
  have hT : ∀ σ, wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v ≠ 0 →
      0 ≤ (M σ * cp.A σ v).trace ∧ 0 ≤ (M σ * cp.B σ v).trace ∧
        (M σ * cp.A σ v).trace + (M σ * cp.B σ v).trace ≤ 2 * cp.Theta σ v := by
    intro σ hσ
    obtain ⟨hM, hAM⟩ := hMpsd σ (lt_of_le_of_ne (hw σ) (Ne.symm hσ))
    obtain ⟨hA, hB⟩ := cp.root_psd_core hσ
    obtain ⟨d1, d2, -, -⟩ := SecA.pdom hA hB hM hAM
    refine ⟨trace_mul_nonneg hM hA, trace_mul_nonneg hM hB, ?_⟩
    have : cp.Theta σ v = (cp.A σ v * cp.A σ v + cp.B σ v * cp.B σ v).trace := rfl
    linarith
  -- the moments of `Y = 2τ⁺τ⁻`
  have hlog := hR.logd
  set k := ⌈Real.log d⌉₊ with hkdef
  have hk1 : 1 ≤ k := Nat.ceil_pos.2 (by linarith)
  have hklt : (k : ℝ) < Real.log d + 1 := Nat.ceil_lt_add_one (by linarith)
  have hk8 : 4 * (2 * k) ≤ p := by
    have h := hR.interp_order_le
    have : ((4 * (2 * k) : ℕ) : ℝ) ≤ p := by push_cast; linarith
    exact_mod_cast this
  have hY2k : cp.E (fun σ => (2 * cp.taup σ v * cp.taum σ v) ^ (2 * k)) ≤ 9 ^ (2 * k) :=
    (cp.E_taupm_pow_le hR hv (by omega) hk8).trans
      (pow_le_pow_left₀ (by positivity) hc9 _)
  have hY0 : ∀ σ, wt cp.G p (aOf d p) cp.yp cp.ym σ cp.S ≠ 0 →
      0 ≤ 2 * cp.taup σ v * cp.taum σ v := fun σ hσ => by
    obtain ⟨t1, -, t3, -⟩ := cp.tau_le hR hσ
    positivity
  have hΘY := cp.E_Theta_mul_le hR hv hEΘ hdm (fun σ => 2 * cp.taup σ v * cp.taum σ v) hY0
    (by norm_num) hY2k
  -- apply the generic relative transfer
  refine cp.clip_trans_rel hR hv
    (fun σ => (M σ * cp.A σ v).trace + (M σ * cp.B σ v).trace) (fun _ => 0)
    (fun σ => -((M σ * cp.A σ v).trace • cp.B σ v + (M σ * cp.B σ v).trace • cp.A σ v))
    ?_ (by omega) (by omega) (Nat.sub_le p 1) (Nat.sub_le p 1)
    (fun σ => (M σ * cp.A σ v).trace + (M σ * cp.B σ v).trace) (M := 9) (by norm_num) ?_ ?_
    (fun σ => (M σ * cp.A σ v).trace + (M σ * cp.B σ v).trace) ?_ (m₀ := 108 * m) (B := 90)
    ?_ (by norm_num) ?_ ?_
  · -- core measurability
    intro σ σ' h
    have hA : cp.A σ v = cp.A σ' v := SecA.rootMat_congr cp.G h
    have hB : cp.B σ v = cp.B σ' v := SecA.rootMat_congr cp.G h
    refine ⟨?_, rfl, ?_⟩ <;> simp only [hA, hB, hMc σ σ' h]
  · -- the sup majorant
    intro σ hσ x hxA hxB
    obtain ⟨hA, hB⟩ := cp.root_psd_core hσ
    obtain ⟨t1, t2, -⟩ := hT σ hσ
    obtain ⟨a1, a2, b1, b2⟩ := SecA.C4.sup_weights hA hB hxA.le hxB.le
    exact SecA.C4.quadMaj_pair (SecA.CA.psd_symm hA) (SecA.CA.psd_symm hB) t1 t2
      (fun i => Real.sqrt_nonneg _) (qForm_nonneg hA x) hxA.le (qForm_nonneg hB x) hxB.le
      a1 a2 b1 b2
  · -- own-core moments of the sup majorant
    intro n hn1 hn
    have h4n : 4 * n ≤ p := by have := hR.moment_order_le; omega
    have hΘm := cp.coreE_Theta_pow_le hR hv hn1 h4n
    have hpt : ∀ σ, 0 < wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v →
        (if wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v ≠ 0 then
          (M σ * cp.A σ v).trace + (M σ * cp.B σ v).trace else 0) ^ n ≤
        2 ^ n * (if wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v ≠ 0 then
          cp.Theta σ v else 0) ^ n := by
      intro σ hσ
      rw [ite_eq_left hσ.ne', ite_eq_left hσ.ne', ← mul_pow]
      obtain ⟨t1, t2, t3⟩ := hT σ hσ.ne'
      exact pow_le_pow_left₀ (by positivity) t3 n
    have h1 := SecA.wavg_mono' hw hpt
    rw [SecA.wavg_const_mul] at h1
    calc _ ≤ _ := h1
      _ ≤ 2 ^ n * (4 * c ^ 2) ^ n := mul_le_mul_of_nonneg_left hΘm (by positivity)
      _ = (8 * c ^ 2) ^ n := by rw [← mul_pow]; ring_nf
      _ ≤ 9 ^ n := pow_le_pow_left₀ (by positivity) hc9 n
  · -- the endpoint majorant
    intro σ hσ
    have hσc := cp.wtCore_ne_zero_of_wt hR hv hσ
    obtain ⟨hA, hB⟩ := cp.root_psd_core hσc
    obtain ⟨t1, t2, -⟩ := hT σ hσc
    obtain ⟨⟨hα, hA1, hA2⟩, ⟨hβ, hB1, hB2⟩⟩ := cp.endLam_maj hR hv hσ
    have hl0 := cp.endLam_nonneg hR σ v
    have hqA := qForm_nonneg hA (cp.xi σ v)
    have hqB := qForm_nonneg hB (cp.xi σ v)
    refine SecA.C4.quadMaj_pair (SecA.CA.psd_symm hA) (SecA.CA.psd_symm hB) t1 t2 hl0 hqA
      (by linarith) hqB (by linarith) (fun i => ?_) (fun i k => ?_) (fun i => ?_)
      (fun i k => ?_)
    · exact (hA1 i).trans (mul_le_of_le_one_left (hl0 i) (by linarith))
    · refine (hA2 i k).trans ?_
      rw [mul_assoc]
      exact mul_le_of_le_one_left (mul_nonneg (hl0 i) (hl0 k)) (by linarith)
    · exact (hB1 i).trans (mul_le_of_le_one_left (hl0 i) (by linarith))
    · refine (hB2 i k).trans ?_
      rw [mul_assoc]
      exact mul_le_of_le_one_left (mul_nonneg (hl0 i) (hl0 k)) (by linarith)
  · -- `ϑ ≤ m₀`
    have := vth_le_inv_d hR
    linarith
  · -- `E X ≤ m₀`
    simp only [hpp, pow_one]
    refine le_trans (SecA.lawE_le_of_supp cp.G fun σ hσ => ?_) (hΘY.trans (le_of_eq (by ring)))
    obtain ⟨t1, -, t3, -⟩ := cp.tau_le hR hσ
    obtain ⟨-, -, h⟩ := hT σ (cp.wtCore_ne_zero_of_wt hR hv hσ)
    have := mul_le_mul_of_nonneg_right h (mul_pos t1 t3).le
    nlinarith
  · -- `E X² ≤ B²`
    simp only [hpp, pow_one]
    have hp16 : 4 * 4 ≤ p := le_trans (by norm_num) hR.treg.hp
    have hΘ4 := cp.E_Theta_pow_le hR hv (n := 4) (by norm_num) hp16
    have hY4 := cp.E_taupm_pow_le hR hv (n := 4) (by norm_num) hp16
    have hpt : ∀ σ, wt cp.G p (aOf d p) cp.yp cp.ym σ cp.S ≠ 0 →
        (((M σ * cp.A σ v).trace + (M σ * cp.B σ v).trace) * cp.taup σ v * cp.taum σ v) ^ 2 ≤
          1 / 2 * (cp.Theta σ v ^ 4 + (2 * cp.taup σ v * cp.taum σ v) ^ 4) := by
      intro σ hσ
      obtain ⟨t1, -, t3, -⟩ := cp.tau_le hR hσ
      have hσc := cp.wtCore_ne_zero_of_wt hR hv hσ
      obtain ⟨u1, u2, h⟩ := hT σ hσc
      have hΘ0 := (cp.Theta_le_sq hσc).1
      set Y := 2 * cp.taup σ v * cp.taum σ v with hYdef
      have hY0 : 0 ≤ Y := by positivity
      have hX : 0 ≤ ((M σ * cp.A σ v).trace + (M σ * cp.B σ v).trace) * cp.taup σ v *
          cp.taum σ v := by positivity
      have hXY : ((M σ * cp.A σ v).trace + (M σ * cp.B σ v).trace) * cp.taup σ v *
          cp.taum σ v ≤ cp.Theta σ v * Y := by
        have := mul_le_mul_of_nonneg_right h (mul_pos t1 t3).le
        rw [hYdef]
        nlinarith
      have h2 := pow_le_pow_left₀ hX hXY 2
      have h3 : (cp.Theta σ v * Y) ^ 2 ≤ 1 / 2 * (cp.Theta σ v ^ 4 + Y ^ 4) := by
        nlinarith [sq_nonneg (cp.Theta σ v ^ 2 - Y ^ 2)]
      linarith
    have h1 := SecA.lawE_le_of_supp cp.G hpt
    rw [lawE_const_mul, lawE_add] at h1
    unfold CapPoint.E at hΘ4 hY4
    have h9 : (4 * c ^ 2) ^ 4 ≤ (9 : ℝ) ^ 4 :=
      pow_le_pow_left₀ (by positivity) (by nlinarith) 4
    have h9' : (8 * c ^ 2) ^ 4 ≤ (9 : ℝ) ^ 4 := pow_le_pow_left₀ (by positivity) hc9 4
    refine h1.trans ?_
    norm_num at h9 h9' ⊢
    linarith

/-- `E (τ^{±2})ⁿ ≤ (4(1+2ε)²)ⁿ` (`4n ≤ p`). -/
theorem E_tau_sq_pow_le (hR : RegA d p) {v : cp.V} (hv : v ∈ cp.S) {n : ℕ} (hn1 : 1 ≤ n)
    (hn : 4 * n ≤ p) :
    cp.E (fun σ => (cp.taup σ v ^ 2) ^ n) ≤ (4 * (1 + 2 * epsP d p) ^ 2) ^ n ∧
      cp.E (fun σ => (cp.taum σ v ^ 2) ^ n) ≤ (4 * (1 + 2 * epsP d p) ^ 2) ^ n := by
  have h2n : 1 ≤ 2 * n := by omega
  obtain ⟨m1, m2⟩ := cp.h_moment hR hv h2n (by omega)
  have key : ∀ (t h : Config cp.V → ℝ),
      (∀ σ, wt cp.G p (aOf d p) cp.yp cp.ym σ cp.S ≠ 0 → 0 < t σ ∧ t σ ≤ 2 * h σ) →
      cp.E (fun σ => h σ ^ (2 * n)) ≤ (1 + 2 * epsP d p) ^ (2 * n) →
      cp.E (fun σ => (t σ ^ 2) ^ n) ≤ (4 * (1 + 2 * epsP d p) ^ 2) ^ n := by
    intro t h ht hm
    have hpt : ∀ σ, wt cp.G p (aOf d p) cp.yp cp.ym σ cp.S ≠ 0 →
        (t σ ^ 2) ^ n ≤ 4 ^ n * h σ ^ (2 * n) := by
      intro σ hσ
      obtain ⟨h0, h1⟩ := ht σ hσ
      calc (t σ ^ 2) ^ n ≤ ((2 * h σ) ^ 2) ^ n :=
            pow_le_pow_left₀ (by positivity) (pow_le_pow_left₀ h0.le h1 2) n
        _ = 4 ^ n * h σ ^ (2 * n) := by rw [mul_pow, mul_pow, pow_mul]; norm_num
    have h1 := SecA.lawE_le_of_supp cp.G hpt
    rw [lawE_const_mul] at h1
    refine h1.trans ?_
    unfold CapPoint.E at hm
    calc (4 : ℝ) ^ n * lawE cp.G p (aOf d p) cp.yp cp.ym cp.S (fun σ => h σ ^ (2 * n)) ≤
          4 ^ n * (1 + 2 * epsP d p) ^ (2 * n) :=
          mul_le_mul_of_nonneg_left hm (by positivity)
      _ = (4 * (1 + 2 * epsP d p) ^ 2) ^ n := by rw [mul_pow, pow_mul]
  refine ⟨key (fun σ => cp.taup σ v) (fun σ => cp.hp σ v) (fun σ hσ => ?_) m1,
    key (fun σ => cp.taum σ v) (fun σ => cp.hm σ v) (fun σ hσ => ?_) m2⟩
  · obtain ⟨t1, t2, -, -⟩ := cp.tau_le hR hσ
    exact ⟨t1, t2⟩
  · obtain ⟨-, -, t3, t4⟩ := cp.tau_le hR hσ
    exact ⟨t3, t4⟩

/-- The interpolation and second-moment bounds for `X = Θ Y`, `Y = (τ^±)²`. -/
theorem E_Theta_tau_sq (hR : RegA d p) {v : cp.V} (hv : v ∈ cp.S) {m : ℝ}
    (hEΘ : cp.E (fun σ => cp.Theta σ v) ≤ m) (hdm : 1 / (d : ℝ) ≤ m) (t : Config cp.V → ℝ)
    (ht : ∀ σ, wt cp.G p (aOf d p) cp.yp cp.ym σ cp.S ≠ 0 → 0 < t σ)
    (hmom : ∀ n : ℕ, 1 ≤ n → 4 * n ≤ p →
      cp.E (fun σ => (t σ ^ 2) ^ n) ≤ (4 * (1 + 2 * epsP d p) ^ 2) ^ n) :
    cp.E (fun σ => cp.Theta σ v * t σ ^ 2) ≤ 60 * m ∧
      cp.E (fun σ => (cp.Theta σ v * t σ ^ 2) ^ 2) ≤ 90 ^ 2 := by
  have hε0 := SecA.epsP_nonneg hR.treg
  have hε1 := SecA.epsP_le hR.treg
  set c := 1 + 2 * epsP d p with hc
  have hc5 : 4 * c ^ 2 ≤ 5 := by
    have : c ≤ 101 / 100 := by linarith
    nlinarith
  have hlog := hR.logd
  set k := ⌈Real.log d⌉₊ with hkdef
  have hk1 : 1 ≤ k := Nat.ceil_pos.2 (by linarith)
  have hklt : (k : ℝ) < Real.log d + 1 := Nat.ceil_lt_add_one (by linarith)
  have hk8 : 4 * (2 * k) ≤ p := by
    have h := hR.interp_order_le
    have : ((4 * (2 * k) : ℕ) : ℝ) ≤ p := by push_cast; linarith
    exact_mod_cast this
  have hY2k : cp.E (fun σ => (t σ ^ 2) ^ (2 * k)) ≤ 5 ^ (2 * k) :=
    (hmom _ (by omega) hk8).trans (pow_le_pow_left₀ (by positivity) hc5 _)
  refine ⟨?_, ?_⟩
  · have h := cp.E_Theta_mul_le hR hv hEΘ hdm (fun σ => t σ ^ 2)
      (fun σ hσ => sq_nonneg _) (by norm_num) hY2k
    linarith
  · have hp16 : 4 * 4 ≤ p := le_trans (by norm_num) hR.treg.hp
    have hΘ4 := cp.E_Theta_pow_le hR hv (n := 4) (by norm_num) hp16
    have hY4 := hmom 4 (by norm_num) hp16
    have hpt : ∀ σ, wt cp.G p (aOf d p) cp.yp cp.ym σ cp.S ≠ 0 →
        (cp.Theta σ v * t σ ^ 2) ^ 2 ≤ 1 / 2 * (cp.Theta σ v ^ 4 + (t σ ^ 2) ^ 4) := by
      intro σ _
      nlinarith [sq_nonneg (cp.Theta σ v ^ 2 - (t σ ^ 2) ^ 2)]
    have h1 := SecA.lawE_le_of_supp cp.G hpt
    rw [lawE_const_mul, lawE_add] at h1
    unfold CapPoint.E at hΘ4 hY4
    have h5 : (4 * c ^ 2) ^ 4 ≤ (5 : ℝ) ^ 4 := pow_le_pow_left₀ (by positivity) hc5 4
    refine h1.trans ?_
    norm_num at h5 ⊢
    linarith

/-- `A-C4T-T34`, the `A` part: transfer of `F₃ = q_{AMA} α^{p-2} β^p` (`clip_trans_rel` with
sup/endpoint scale `Θ` (`quadMaj_dom`, `A-PDOM` `AMA ⪯ ΘA`), core moments `≤ 5ⁿ`, relative
factor `Θ (τ⁺)²`). -/
theorem trans_domA (hR : RegA d p) {v : cp.V} (hv : v ∈ cp.S)
    (M : Config cp.V → Matrix (cp.N v) (cp.N v) ℝ) (hMc : ∀ σ σ', AgreeOff v σ σ' → M σ = M σ')
    (hMpsd : ∀ σ, 0 < wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v →
      (M σ).PosSemidef ∧ (cp.A σ v - M σ).PosSemidef)
    {m : ℝ} (hEΘ : cp.E (fun σ => cp.Theta σ v) ≤ m) (hdm : 1 / (d : ℝ) ≤ m) :
    |cp.coreE v (fun σ =>
        gaussE (clipObs (quadFn 0 0 (cp.A σ v * M σ * cp.A σ v)) (p - 2) p
          (cp.A σ v) (cp.B σ v)) -
        radE (clipObs (quadFn 0 0 (cp.A σ v * M σ * cp.A σ v)) (p - 2) p
          (cp.A σ v) (cp.B σ v))) / cp.FH v| ≤
      2 * Real.exp 2 * (60 * m * (2 * Real.exp 12000) * 90) * (41 ^ 4 / 4 * ((p : ℝ) ^ 4 / d)) +
        5 * Real.exp (-(p : ℝ)) / d := by
  have hp2 : 2 ≤ p := hR.treg.two_le_p
  have hε0 := SecA.epsP_nonneg hR.treg
  have hε1 := SecA.epsP_le hR.treg
  have hw : ∀ σ, 0 ≤ wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v :=
    fun σ => SecA.wtCore_nonneg cp.G _ _ _ _ σ _ _
  set c := 1 + 2 * epsP d p with hc
  have hc5 : 4 * c ^ 2 ≤ 5 := by
    have : c ≤ 101 / 100 := by linarith
    nlinarith
  have hfac : ∀ σ, wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v ≠ 0 →
      (cp.A σ v * M σ * cp.A σ v).PosSemidef ∧ 0 ≤ cp.Theta σ v ∧
        (cp.Theta σ v • cp.A σ v - cp.A σ v * M σ * cp.A σ v).PosSemidef ∧
        (cp.A σ v).PosSemidef ∧ (cp.B σ v).PosSemidef := by
    intro σ hσ
    obtain ⟨hM, hAM⟩ := hMpsd σ (lt_of_le_of_ne (hw σ) (Ne.symm hσ))
    obtain ⟨hA, hB⟩ := cp.root_psd_core hσ
    obtain ⟨-, -, hdom, -⟩ := SecA.pdom hA hB hM hAM
    have hL := hM.mul_mul_conjTranspose_same (cp.A σ v)
    rw [hA.isHermitian.eq] at hL
    exact ⟨hL, (cp.Theta_le_sq hσ).1, hdom, hA, hB⟩
  have hpp : p - (p - 2) = 2 := by omega
  obtain ⟨hX1, hX2⟩ := cp.E_Theta_tau_sq hR hv hEΘ hdm (fun σ => cp.taup σ v)
    (fun σ hσ => (cp.tau_le hR hσ).1) (fun n hn1 hn => (cp.E_tau_sq_pow_le hR hv hn1 hn).1)
  refine cp.clip_trans_rel hR hv (fun _ => 0) (fun _ => 0)
    (fun σ => cp.A σ v * M σ * cp.A σ v) ?_ le_rfl (by omega) (Nat.sub_le p 2) le_rfl
    (fun σ => cp.Theta σ v) (M := 5) (by norm_num) ?_ ?_ (fun σ => cp.Theta σ v) ?_
    (m₀ := 60 * m) (B := 90) ?_ (by norm_num) ?_ ?_
  · intro σ σ' h
    have hA : cp.A σ v = cp.A σ' v := SecA.rootMat_congr cp.G h
    refine ⟨rfl, rfl, ?_⟩
    simp only [hA, hMc σ σ' h]
  · intro σ hσ x hxA _
    obtain ⟨hL, hΘ0, hdom, hA, hB⟩ := hfac σ hσ
    exact SecA.C4.quadMaj_dom hL hΘ0 hdom hxA.le (fun i => Real.sqrt_nonneg _) fun i => by
      rw [Real.sq_sqrt (add_nonneg hA.diag_nonneg hB.diag_nonneg)]
      linarith [hB.diag_nonneg (i := i)]
  · intro n hn1 hn
    have h4n : 4 * n ≤ p := by have := hR.moment_order_le; omega
    exact (cp.coreE_Theta_pow_le hR hv hn1 h4n).trans (pow_le_pow_left₀ (by positivity) hc5 n)
  · intro σ hσ
    have hσc := cp.wtCore_ne_zero_of_wt hR hv hσ
    obtain ⟨hL, hΘ0, hdom, hA, hB⟩ := hfac σ hσc
    obtain ⟨⟨hα, -, hA2⟩, -⟩ := cp.endLam_maj hR hv hσ
    have hl0 := cp.endLam_nonneg hR σ v
    have hqA := qForm_nonneg hA (cp.xi σ v)
    refine SecA.C4.quadMaj_dom hL hΘ0 hdom (by linarith) hl0 fun i => ?_
    have h := (le_abs_self _).trans (hA2 i i)
    have : (1 - qForm (cp.A σ v) (cp.xi σ v)) * cp.endLam σ v i * cp.endLam σ v i ≤
        cp.endLam σ v i ^ 2 := by
      rw [mul_assoc, sq]
      exact mul_le_of_le_one_left (mul_nonneg (hl0 i) (hl0 i)) (by linarith)
    linarith
  · have := vth_le_inv_d hR
    have : 0 ≤ m := le_trans (by positivity) hdm
    linarith
  · simp only [hpp, Nat.sub_self, pow_zero, mul_one]
    exact hX1
  · simp only [hpp, Nat.sub_self, pow_zero, mul_one]
    exact hX2

/-- `A-C4T-T34`, the `B` part: transfer of `F₄ = q_{BMB} α^p β^{p-2}`. -/
theorem trans_domB (hR : RegA d p) {v : cp.V} (hv : v ∈ cp.S)
    (M : Config cp.V → Matrix (cp.N v) (cp.N v) ℝ) (hMc : ∀ σ σ', AgreeOff v σ σ' → M σ = M σ')
    (hMpsd : ∀ σ, 0 < wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v →
      (M σ).PosSemidef ∧ (cp.A σ v - M σ).PosSemidef)
    {m : ℝ} (hEΘ : cp.E (fun σ => cp.Theta σ v) ≤ m) (hdm : 1 / (d : ℝ) ≤ m) :
    |cp.coreE v (fun σ =>
        gaussE (clipObs (quadFn 0 0 (cp.B σ v * M σ * cp.B σ v)) p (p - 2)
          (cp.A σ v) (cp.B σ v)) -
        radE (clipObs (quadFn 0 0 (cp.B σ v * M σ * cp.B σ v)) p (p - 2)
          (cp.A σ v) (cp.B σ v))) / cp.FH v| ≤
      2 * Real.exp 2 * (60 * m * (2 * Real.exp 12000) * 90) * (41 ^ 4 / 4 * ((p : ℝ) ^ 4 / d)) +
        5 * Real.exp (-(p : ℝ)) / d := by
  have hp2 : 2 ≤ p := hR.treg.two_le_p
  have hε0 := SecA.epsP_nonneg hR.treg
  have hε1 := SecA.epsP_le hR.treg
  have hw : ∀ σ, 0 ≤ wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v :=
    fun σ => SecA.wtCore_nonneg cp.G _ _ _ _ σ _ _
  set c := 1 + 2 * epsP d p with hc
  have hc5 : 4 * c ^ 2 ≤ 5 := by
    have : c ≤ 101 / 100 := by linarith
    nlinarith
  have hfac : ∀ σ, wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v ≠ 0 →
      (cp.B σ v * M σ * cp.B σ v).PosSemidef ∧ 0 ≤ cp.Theta σ v ∧
        (cp.Theta σ v • cp.B σ v - cp.B σ v * M σ * cp.B σ v).PosSemidef ∧
        (cp.A σ v).PosSemidef ∧ (cp.B σ v).PosSemidef := by
    intro σ hσ
    obtain ⟨hM, hAM⟩ := hMpsd σ (lt_of_le_of_ne (hw σ) (Ne.symm hσ))
    obtain ⟨hA, hB⟩ := cp.root_psd_core hσ
    obtain ⟨-, -, -, hdom⟩ := SecA.pdom hA hB hM hAM
    have hL := hM.mul_mul_conjTranspose_same (cp.B σ v)
    rw [hB.isHermitian.eq] at hL
    exact ⟨hL, (cp.Theta_le_sq hσ).1, hdom, hA, hB⟩
  have hpp : p - (p - 2) = 2 := by omega
  obtain ⟨hX1, hX2⟩ := cp.E_Theta_tau_sq hR hv hEΘ hdm (fun σ => cp.taum σ v)
    (fun σ hσ => (cp.tau_le hR hσ).2.2.1) (fun n hn1 hn => (cp.E_tau_sq_pow_le hR hv hn1 hn).2)
  refine cp.clip_trans_rel hR hv (fun _ => 0) (fun _ => 0)
    (fun σ => cp.B σ v * M σ * cp.B σ v) ?_ (by omega) le_rfl le_rfl (Nat.sub_le p 2)
    (fun σ => cp.Theta σ v) (M := 5) (by norm_num) ?_ ?_ (fun σ => cp.Theta σ v) ?_
    (m₀ := 60 * m) (B := 90) ?_ (by norm_num) ?_ ?_
  · intro σ σ' h
    have hB : cp.B σ v = cp.B σ' v := SecA.rootMat_congr cp.G h
    refine ⟨rfl, rfl, ?_⟩
    simp only [hB, hMc σ σ' h]
  · intro σ hσ x _ hxB
    obtain ⟨hL, hΘ0, hdom, hA, hB⟩ := hfac σ hσ
    exact SecA.C4.quadMaj_dom hL hΘ0 hdom hxB.le (fun i => Real.sqrt_nonneg _) fun i => by
      rw [Real.sq_sqrt (add_nonneg hA.diag_nonneg hB.diag_nonneg)]
      linarith [hA.diag_nonneg (i := i)]
  · intro n hn1 hn
    have h4n : 4 * n ≤ p := by have := hR.moment_order_le; omega
    exact (cp.coreE_Theta_pow_le hR hv hn1 h4n).trans (pow_le_pow_left₀ (by positivity) hc5 n)
  · intro σ hσ
    have hσc := cp.wtCore_ne_zero_of_wt hR hv hσ
    obtain ⟨hL, hΘ0, hdom, hA, hB⟩ := hfac σ hσc
    obtain ⟨-, ⟨hβ, -, hB2⟩⟩ := cp.endLam_maj hR hv hσ
    have hl0 := cp.endLam_nonneg hR σ v
    have hqB := qForm_nonneg hB (cp.xi σ v)
    refine SecA.C4.quadMaj_dom hL hΘ0 hdom (by linarith) hl0 fun i => ?_
    have h := (le_abs_self _).trans (hB2 i i)
    have : (1 - qForm (cp.B σ v) (cp.xi σ v)) * cp.endLam σ v i * cp.endLam σ v i ≤
        cp.endLam σ v i ^ 2 := by
      rw [mul_assoc, sq]
      exact mul_le_of_le_one_left (mul_nonneg (hl0 i) (hl0 i)) (by linarith)
    linarith
  · have := vth_le_inv_d hR
    have : 0 ≤ m := le_trans (by positivity) hdm
    linarith
  · simp only [hpp, Nat.sub_self, pow_zero, mul_one, one_mul]
    exact hX1
  · simp only [hpp, Nat.sub_self, pow_zero, mul_one, one_mul]
    exact hX2

end CapPoint

end BiluLinial.Tight
