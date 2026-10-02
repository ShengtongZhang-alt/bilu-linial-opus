/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecB.WTRemFac

/-!
# Derivative majorants of the (WT5) observables (sub-node (R3) of TB.WT5r°)

At an interior point `x₀` (`q_A(x₀), q_B(x₀) < 1`), with `μ₀ = min(1 - q_A(x₀), 1 - q_B(x₀))`,
`κ = (1 + 2h)/μ₀` and weights `λ_s = κ √b_s` (`b_s = A_ss + B_ss`):
* the clips `1 - q_A`, `1 - q_B` and the shifted clips `1 - q_{A_{b,h}}` satisfy `QuadMaj` with
  their exact values as scales (`quadMaj_one_sub_scaled`);
* `ñ_t`, `q_{c₊² L}` satisfy `QuadMaj` with scales `1`, `ĉ = c_L y⁺_i/a²`;
* hence `G` has a majorant (`MajN`) with constant `K_G = 4(s₊ + N) + 4(s₋ + N) + 2|l| + 2`, and
  `|∂^ν F(x₀)| ≤ 2 m_σ (8p)^{|ν|} Π_{s ∈ ν} √b_s` once `K_G + 2e₁ + 2e₂ ≤ 8p`,
  `s₊ + s₋ + N ≤ min(e₁, e₂)` and `(1+2h)^{s₊+s₋+N} ≤ 2` (`final_combine`, `deriv_bound_Q`).
-/

@[expose] public section

namespace BiluLinial.Tight.SecB.WR

open Matrix SecA.CR SecA.StarCalc

section Gen

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem QuadMaj.mono_lam {c : ℝ} {ℓ : ι → ℝ} {Q : Matrix ι ι ℝ} {x : ι → ℝ} {m : ℝ}
    {lam lam' : ι → ℝ} (h : QuadMaj c ℓ Q x m lam) (hm : 0 ≤ m) (hlam : ∀ i, 0 ≤ lam i)
    (hle : ∀ i, lam i ≤ lam' i) : QuadMaj c ℓ Q x m lam' :=
  ⟨h.h0, fun i => (h.h1 i).trans (mul_le_mul_of_nonneg_left (hle i) (by positivity)),
    fun i j => (h.h2 i j).trans (mul_le_mul (mul_le_mul_of_nonneg_left (hle i) (by positivity))
      (hle j) (hlam j) (mul_nonneg (by positivity) ((hlam i).trans (hle i))))⟩

/-- A PSD quadratic dominated by `c q_A` satisfies `QuadMaj` with scale `c`, weights `√w`. -/
theorem quadMaj_psd_dom {L A : Matrix ι ι ℝ} (hL : L.PosSemidef) {c : ℝ} (hc : 0 ≤ c)
    (hdom : ∀ x, qForm L x ≤ c * qForm A x) {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i)
    (hw : ∀ i, A i i ≤ w i) {x₀ : ι → ℝ} (hx : qForm A x₀ ≤ 1) :
    QuadMaj 0 0 L x₀ c (fun i => Real.sqrt (w i)) := by
  have hLt := psd_transpose hL
  have hq0 := qForm_nonneg hL x₀
  have hqL : qForm L x₀ ≤ c := (hdom x₀).trans (by nlinarith)
  have hdiag : ∀ i, L i i ≤ c * w i := fun i => by
    have h := hdom (Pi.single i 1)
    rw [qForm_single, qForm_single] at h
    exact h.trans (mul_le_mul_of_nonneg_left (hw i) hc)
  have hLd : ∀ i, 0 ≤ L i i := fun i => hL.diag_nonneg
  refine ⟨?_, fun i => ?_, fun i j => ?_⟩
  · simp only [quadFn, zero_dotProduct, zero_add]
    rw [abs_of_nonneg hq0]
    exact hqL
  · have e : (0 : ι → ℝ) i + ((L + Lᵀ) *ᵥ x₀) i = 2 * (L *ᵥ x₀) i := by
      rw [hLt, add_mulVec]
      simp only [Pi.zero_apply, Pi.add_apply]
      ring
    rw [e, abs_mul, abs_two]
    have h1 := SecA.CA.mulVec_apply_sq_le' hL x₀ i
    have h2 : (L *ᵥ x₀) i ^ 2 ≤ (c * Real.sqrt (w i)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (hw0 i)]
      calc (L *ᵥ x₀) i ^ 2 ≤ L i i * qForm L x₀ := h1
        _ ≤ (c * w i) * c := mul_le_mul (hdiag i) hqL hq0 (by nlinarith [hw0 i])
        _ = c ^ 2 * w i := by ring
    have h3 : |(L *ᵥ x₀) i| ≤ c * Real.sqrt (w i) := by
      have := sq_le_sq.1 h2
      rwa [abs_of_nonneg (mul_nonneg hc (Real.sqrt_nonneg (w i)))] at this
    nlinarith [abs_nonneg ((L *ᵥ x₀) i)]
  · have hji : L j i = L i j := by
      have h := congrFun (congrFun hLt i) j
      simpa using h
    have e : L i j + L j i = 2 * L i j := by rw [hji]; ring
    rw [e, abs_mul, abs_two]
    have h2 : L i j ^ 2 ≤ (c * Real.sqrt (w i) * Real.sqrt (w j)) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (hw0 i), Real.sq_sqrt (hw0 j)]
      calc L i j ^ 2 ≤ L i i * L j j := SecA.CA.psd_apply_sq_le' hL i j
        _ ≤ (c * w i) * (c * w j) := mul_le_mul (hdiag i) (hdiag j) (hLd j) (by nlinarith [hw0 i])
        _ = c ^ 2 * w i * w j := by ring
    have h3 : |L i j| ≤ c * Real.sqrt (w i) * Real.sqrt (w j) := by
      have := sq_le_sq.1 h2
      rwa [abs_of_nonneg (mul_nonneg (mul_nonneg hc (Real.sqrt_nonneg (w i)))
        (Real.sqrt_nonneg (w j)))] at this
    nlinarith [abs_nonneg (L i j)]

/-- The clip `1 - q_N` with its exact value as scale, weights `κ √w` (`κ ≥ 1`,
`κ (1 - q_N(x₀)) ≥ 1`). -/
theorem quadMaj_one_sub_scaled {N : Matrix ι ι ℝ} (hN : N.PosSemidef) {w : ι → ℝ}
    (hw0 : ∀ i, 0 ≤ w i) (hw : ∀ i, N i i ≤ w i) {x₀ : ι → ℝ} (hx : qForm N x₀ < 1) {κ : ℝ}
    (hκ1 : 1 ≤ κ) (hκ : 1 ≤ κ * (1 - qForm N x₀)) :
    QuadMaj 1 0 (-N) x₀ (1 - qForm N x₀) (fun i => κ * Real.sqrt (w i)) := by
  have hq0 := qForm_nonneg hN x₀
  have hNd : ∀ i, 0 ≤ N i i := fun i => hN.diag_nonneg
  have hpos : 0 < 1 - qForm N x₀ := by linarith
  refine SecA.CA.quadMaj_one_sub (SecA.CA.psd_symm hN) hpos (fun i => ?_) (fun i k => ?_)
  · have h1 := SecA.CA.mulVec_apply_sq_le' hN x₀ i
    have h2 : (N *ᵥ x₀) i ^ 2 ≤ Real.sqrt (w i) ^ 2 := by
      rw [Real.sq_sqrt (hw0 i)]
      calc (N *ᵥ x₀) i ^ 2 ≤ N i i * qForm N x₀ := h1
        _ ≤ w i * 1 := mul_le_mul (hw i) hx.le hq0 (hw0 i)
        _ = w i := mul_one _
    have h3 : |(N *ᵥ x₀) i| ≤ Real.sqrt (w i) := by
      have := sq_le_sq.1 h2
      rwa [abs_of_nonneg (Real.sqrt_nonneg _)] at this
    have hs := Real.sqrt_nonneg (w i)
    calc |(N *ᵥ x₀) i| ≤ Real.sqrt (w i) := h3
      _ ≤ (κ * (1 - qForm N x₀)) * Real.sqrt (w i) := le_mul_of_one_le_left hs hκ
      _ = (1 - qForm N x₀) * (κ * Real.sqrt (w i)) := by ring
  · have h2 : N i k ^ 2 ≤ (Real.sqrt (w i) * Real.sqrt (w k)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (hw0 i), Real.sq_sqrt (hw0 k)]
      exact (SecA.CA.psd_apply_sq_le' hN i k).trans
        (mul_le_mul (hw i) (hw k) (hNd k) (hw0 i))
    have h3 : |N i k| ≤ Real.sqrt (w i) * Real.sqrt (w k) := by
      have := sq_le_sq.1 h2
      rwa [abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg (w i)) (Real.sqrt_nonneg (w k)))] at this
    have hs : 0 ≤ Real.sqrt (w i) * Real.sqrt (w k) := by positivity
    have hκκ : 1 ≤ (1 - qForm N x₀) * κ * κ := by nlinarith
    calc |N i k| ≤ Real.sqrt (w i) * Real.sqrt (w k) := h3
      _ ≤ ((1 - qForm N x₀) * κ * κ) * (Real.sqrt (w i) * Real.sqrt (w k)) :=
          le_mul_of_one_le_left hs hκκ
      _ = (1 - qForm N x₀) * (κ * Real.sqrt (w i)) * (κ * Real.sqrt (w k)) := by ring

/-- `majN_recip` allowing the power `0`. -/
theorem majN_recip0 {N : ℕ} {x₀ lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i) {c : ℝ} {ℓ : ι → ℝ}
    {Q : Matrix ι ι ℝ} {m : ℝ} (hg : QuadMaj c ℓ Q x₀ m lam) (hm : quadFn c ℓ Q x₀ = m)
    {δ : ℝ} (hδ : 0 < δ) (hm2 : δ / 2 < m) (k : ℕ) :
    MajN N x₀ lam (m⁻¹ ^ k) (4 * (k + N)) (fun x => (psiCut δ (quadFn c ℓ Q x))⁻¹ ^ k) := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    have e : (fun x => (psiCut δ (quadFn c ℓ Q x))⁻¹ ^ 0) = (1 : (ι → ℝ) → ℝ) := by
      funext x
      simp
    rw [e, pow_zero]
    exact (majN_one N x₀ lam).mono hlam le_rfl le_rfl (by positivity)
  · exact majN_recip hlam hg hm hδ hm2 k hk

theorem majN_list_prod {N : ℕ} {x₀ lam : ι → ℝ} {T : Type*} (F : T → (ι → ℝ) → ℝ) (M : T → ℝ)
    (K : ℝ) :
    ∀ l : List T, (∀ t ∈ l, MajN N x₀ lam (M t) K (F t)) →
      MajN N x₀ lam (l.map M).prod (l.length * K) (fun x => (l.map fun t => F t x).prod)
  | [], _ => by
    have e : (fun x : ι → ℝ => (([] : List T).map fun t => F t x).prod) = (1 : (ι → ℝ) → ℝ) := by
      funext x
      simp
    rw [e]
    simpa using majN_one N x₀ lam
  | t :: l, h => by
    have ih := majN_list_prod F M K l (fun t' ht' => h t' (List.mem_cons_of_mem _ ht'))
    have h1 := (h t (List.mem_cons_self ..)).mul ih
    have e : (fun x => ((t :: l).map fun t => F t x).prod) =
        F t * (fun x => (l.map fun t => F t x).prod) := by
      funext x
      simp
    rw [e]
    simp only [List.map_cons, List.prod_cons, List.length_cons]
    convert h1 using 1
    push_cast
    ring

/-- The scalar bookkeeping of the final bound. -/
theorem final_combine {α β h κ rp rm C K' P p8 : ℝ} {sp sm n e₁ e₂ : ℕ} (hα0 : 0 < α)
    (hα1 : α ≤ 1) (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hh : 0 ≤ h)
    (hκ : κ = (1 + 2 * h) / min α β) (hrp : 0 < rp) (hrm : 0 < rm) (hrpκ : 1 ≤ κ * rp)
    (hrmκ : 1 ≤ κ * rm) (hE1 : sp + sm + n ≤ e₁) (hE2 : sp + sm + n ≤ e₂)
    (hh2 : (1 + 2 * h) ^ (sp + sm + n) ≤ 2) (hC : 0 ≤ C) (hK0 : 0 ≤ K') (hK : K' ≤ p8)
    (hP : 0 ≤ P) :
    rp⁻¹ ^ sp * rm⁻¹ ^ sm * C * α ^ e₁ * β ^ e₂ * K' ^ n * (κ ^ n * P) ≤
      2 * C * p8 ^ n * P := by
  set μ := min α β with hμ
  have hμ0 : 0 < μ := lt_min hα0 hβ0
  have hκ0 : 0 < κ := by rw [hκ]; positivity
  have hrp' : rp⁻¹ ≤ κ := by
    rw [inv_le_iff_one_le_mul₀ hrp]
    linarith
  have hrm' : rm⁻¹ ≤ κ := by
    rw [inv_le_iff_one_le_mul₀ hrm]
    linarith
  have hab : α ^ e₁ * β ^ e₂ ≤ μ ^ (sp + sm + n) := by
    rcases le_total α β with hle | hle
    · have hm : μ = α := min_eq_left hle
      rw [hm]
      calc α ^ e₁ * β ^ e₂ ≤ α ^ e₁ * 1 :=
            mul_le_mul_of_nonneg_left (pow_le_one₀ hβ0.le hβ1) (by positivity)
        _ = α ^ e₁ := mul_one _
        _ ≤ α ^ (sp + sm + n) := pow_le_pow_of_le_one hα0.le hα1 hE1
    · have hm : μ = β := min_eq_right hle
      rw [hm]
      calc α ^ e₁ * β ^ e₂ ≤ 1 * β ^ e₂ :=
            mul_le_mul_of_nonneg_right (pow_le_one₀ hα0.le hα1) (by positivity)
        _ = β ^ e₂ := one_mul _
        _ ≤ β ^ (sp + sm + n) := pow_le_pow_of_le_one hβ0.le hβ1 hE2
  have hκμ : κ * μ = 1 + 2 * h := by
    rw [hκ]
    field_simp
  have hKn : K' ^ n ≤ p8 ^ n := pow_le_pow_left₀ hK0 hK n
  have hp8 : 0 ≤ p8 := hK0.trans hK
  have h1 : rp⁻¹ ^ sp * rm⁻¹ ^ sm ≤ κ ^ sp * κ ^ sm :=
    mul_le_mul (pow_le_pow_left₀ (by positivity) hrp' sp)
      (pow_le_pow_left₀ (by positivity) hrm' sm) (by positivity) (by positivity)
  have h2 : κ ^ sp * κ ^ sm * κ ^ n * (α ^ e₁ * β ^ e₂) ≤ 2 := by
    calc κ ^ sp * κ ^ sm * κ ^ n * (α ^ e₁ * β ^ e₂)
        ≤ κ ^ sp * κ ^ sm * κ ^ n * μ ^ (sp + sm + n) :=
          mul_le_mul_of_nonneg_left hab (by positivity)
      _ = (κ * μ) ^ (sp + sm + n) := by ring
      _ = (1 + 2 * h) ^ (sp + sm + n) := by rw [hκμ]
      _ ≤ 2 := hh2
  calc rp⁻¹ ^ sp * rm⁻¹ ^ sm * C * α ^ e₁ * β ^ e₂ * K' ^ n * (κ ^ n * P)
      = (rp⁻¹ ^ sp * rm⁻¹ ^ sm) * κ ^ n * (α ^ e₁ * β ^ e₂) * C * K' ^ n * P := by ring
    _ ≤ (κ ^ sp * κ ^ sm) * κ ^ n * (α ^ e₁ * β ^ e₂) * C * p8 ^ n * P := by
        gcongr
    _ = (κ ^ sp * κ ^ sm * κ ^ n * (α ^ e₁ * β ^ e₂)) * C * p8 ^ n * P := by ring
    _ ≤ 2 * C * p8 ^ n * P := by
        gcongr

end Gen

end BiluLinial.Tight.SecB.WR
