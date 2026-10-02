/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.Ctx

/-!
# T.ALPHA2: the parallelogram inequality for clipped quadratic factors

Node T.ALPHA2 of `docs/tight/BP_TOOLS.md` (AUDIT-C §3 and §5.3). For `A ⪰ 0` write
`α(x) = (1 - q_A(x))₊` (`clipF A x`). Since `q_A(z+w) + q_A(z-w) = 2 q_A(z) + 2 q_A(w)`,

  `(1 - q_A(z+w)) + (1 - q_A(z-w)) = 2 (α(z) - q_A(w))` when `q_A(z) < 1`,

so by AM–GM and `1 - t ≤ e^{-t}` (`0 ≤ t = q_A(w)/α(z) < 1`):

  `α(z+w) α(z-w) ≤ (α(z) - q_A(w))² ≤ α(z)² exp(-2 q_A(w)/α(z))`,

and the product vanishes when `q_A(z) ≥ 1`. With Lean's `x / 0 = 0` the single inequality
`clipF_add_mul_clipF_sub_le` covers both cases.

For `φ = α₊^m β₊^{m'}` (`clipProd m m' A B`) this gives `φ(z+w) φ(z-w) ≤ φ(z)² e^{-⟨w, H(z) w⟩}`
with `H(z) = 2m M/α(z) + 2m' N/β(z)` (`clipHess m m' A B M N z`) for any `0 ⪯ M ⪯ A`,
`0 ⪯ N ⪯ B`; and, multiplying by the standard Gaussian weight `e^{-|x|²/2}`, the midpoint
hypothesis `hmid` of BLmid (`integral_sq_dotProduct_le_of_midpoint`) with `K = I + H`, `κ = 1`.
Off the support (`φ(z) = 0`) the value of `H(z)` is irrelevant: both sides vanish.

**Checks.** `A = 0`: `α ≡ 1` and both sides equal `1`. `w = 0`: equality. `ι` empty: `q_A ≡ 0`,
equality.
-/

@[expose] public section

namespace BiluLinial.Tight

open Matrix

variable {ι : Type*} [Fintype ι]

/-! ### Elementary facts about `qForm` and `clipF` -/

theorem qForm_neg (M : Matrix ι ι ℝ) (x : ι → ℝ) : qForm M (-x) = qForm M x := by
  simp [qForm, mulVec_neg]

/-- The parallelogram identity `q(z+w) + q(z-w) = 2 q(z) + 2 q(w)` (any square matrix). -/
theorem qForm_add_add_qForm_sub (M : Matrix ι ι ℝ) (z w : ι → ℝ) :
    qForm M (z + w) + qForm M (z - w) = 2 * qForm M z + 2 * qForm M w := by
  simp only [qForm, mulVec_add, mulVec_sub, dotProduct_add, add_dotProduct, dotProduct_sub,
    sub_dotProduct]
  ring

theorem qForm_nonneg {M : Matrix ι ι ℝ} (hM : M.PosSemidef) (x : ι → ℝ) : 0 ≤ qForm M x := by
  simpa [qForm] using hM.dotProduct_mulVec_nonneg x

/-- `M ⪯ A` gives `q_M ≤ q_A`. -/
theorem qForm_le_of_posSemidef_sub {A M : Matrix ι ι ℝ} (h : (A - M).PosSemidef) (x : ι → ℝ) :
    qForm M x ≤ qForm A x := by
  have := qForm_nonneg h x
  simp only [qForm, sub_mulVec, dotProduct_sub] at this
  simp only [qForm]
  linarith

theorem qForm_sub (A M : Matrix ι ι ℝ) (x : ι → ℝ) :
    qForm (A - M) x = qForm A x - qForm M x := by
  simp only [qForm, sub_mulVec, dotProduct_sub]

theorem clipF_nonneg (M : Matrix ι ι ℝ) (x : ι → ℝ) : 0 ≤ clipF M x := le_max_right _ _

theorem clipF_le_one {M : Matrix ι ι ℝ} (hM : M.PosSemidef) (x : ι → ℝ) : clipF M x ≤ 1 :=
  max_le (by linarith [qForm_nonneg hM x]) zero_le_one

theorem clipF_neg (M : Matrix ι ι ℝ) (x : ι → ℝ) : clipF M (-x) = clipF M x := by
  simp only [clipF, qForm_neg]

theorem clipF_eq_of_lt {M : Matrix ι ι ℝ} {x : ι → ℝ} (h : qForm M x < 1) :
    clipF M x = 1 - qForm M x :=
  max_eq_left (by linarith)

theorem clipF_eq_zero_of_le {M : Matrix ι ι ℝ} {x : ι → ℝ} (h : 1 ≤ qForm M x) :
    clipF M x = 0 :=
  max_eq_right (by linarith)

theorem continuous_qForm (M : Matrix ι ι ℝ) : Continuous (qForm M) := by
  unfold qForm; fun_prop

theorem continuous_clipF (M : Matrix ι ι ℝ) : Continuous (clipF M) :=
  (continuous_const.sub (continuous_qForm M)).max continuous_const

/-! ### T.ALPHA2 for one factor -/

/-- **T.ALPHA2**, vanishing part: if `q_A(z) ≥ 1` then `α(z+w) α(z-w) = 0`. -/
theorem clipF_add_mul_clipF_sub_eq_zero {A : Matrix ι ι ℝ} (hA : A.PosSemidef) {z : ι → ℝ}
    (hz : 1 ≤ qForm A z) (w : ι → ℝ) : clipF A (z + w) * clipF A (z - w) = 0 := by
  have hpar := qForm_add_add_qForm_sub A z w
  have hw := qForm_nonneg hA w
  rcases le_total 1 (qForm A (z + w)) with h | h
  · rw [clipF_eq_zero_of_le h, zero_mul]
  · rw [clipF_eq_zero_of_le (show 1 ≤ qForm A (z - w) by linarith), mul_zero]

/-- **T.ALPHA2.** For `A ⪰ 0`: `α(z+w) α(z-w) ≤ α(z)² exp(-2 q_A(w)/α(z))` (both sides `0` when
`q_A(z) ≥ 1`, with `x / 0 = 0`). -/
theorem clipF_add_mul_clipF_sub_le {A : Matrix ι ι ℝ} (hA : A.PosSemidef) (z w : ι → ℝ) :
    clipF A (z + w) * clipF A (z - w) ≤
      clipF A z ^ 2 * Real.exp (-(2 * qForm A w / clipF A z)) := by
  have hR : 0 ≤ clipF A z ^ 2 * Real.exp (-(2 * qForm A w / clipF A z)) := by positivity
  rcases le_or_gt 1 (qForm A z) with hz | hz
  · rw [clipF_add_mul_clipF_sub_eq_zero hA hz w]; exact hR
  have hpar := qForm_add_add_qForm_sub A z w
  have hw := qForm_nonneg hA w
  rcases le_or_gt 1 (qForm A (z + w)) with hu | hu
  · rw [clipF_eq_zero_of_le hu, zero_mul]; exact hR
  rcases le_or_gt 1 (qForm A (z - w)) with hv | hv
  · rw [clipF_eq_zero_of_le hv, mul_zero]; exact hR
  rw [clipF_eq_of_lt hu, clipF_eq_of_lt hv, clipF_eq_of_lt hz]
  have hα0 : 0 < 1 - qForm A z := by linarith
  have hs : 1 - qForm A z - qForm A w =
      ((1 - qForm A (z + w)) + (1 - qForm A (z - w))) / 2 := by linarith
  have hαQ : 0 < 1 - qForm A z - qForm A w := by rw [hs]; linarith
  have h1 : (1 - qForm A (z + w)) * (1 - qForm A (z - w)) ≤
      (1 - qForm A z - qForm A w) ^ 2 := by
    rw [hs]; nlinarith [sq_nonneg (qForm A (z + w) - qForm A (z - w))]
  have h2 : 1 - qForm A z - qForm A w ≤
      (1 - qForm A z) * Real.exp (-(qForm A w / (1 - qForm A z))) := by
    have h3 := Real.add_one_le_exp (-(qForm A w / (1 - qForm A z)))
    have h4 : (1 - qForm A z) * (-(qForm A w / (1 - qForm A z)) + 1) =
        1 - qForm A z - qForm A w := by
      field_simp
      ring
    rw [← h4]
    exact mul_le_mul_of_nonneg_left h3 hα0.le
  calc (1 - qForm A (z + w)) * (1 - qForm A (z - w)) ≤ (1 - qForm A z - qForm A w) ^ 2 := h1
    _ ≤ ((1 - qForm A z) * Real.exp (-(qForm A w / (1 - qForm A z)))) ^ 2 :=
        pow_le_pow_left₀ hαQ.le h2 2
    _ = (1 - qForm A z) ^ 2 * Real.exp (-(2 * qForm A w / (1 - qForm A z))) := by
        rw [mul_pow, ← Real.exp_nat_mul]
        congr 2
        push_cast
        ring

/-- **T.ALPHA2**, constant modulus (`α ≤ 1`): `α(z+w) α(z-w) ≤ α(z)² exp(-2 q_A(w))`. -/
theorem clipF_add_mul_clipF_sub_le_exp {A : Matrix ι ι ℝ} (hA : A.PosSemidef) (z w : ι → ℝ) :
    clipF A (z + w) * clipF A (z - w) ≤ clipF A z ^ 2 * Real.exp (-(2 * qForm A w)) := by
  rcases le_or_gt 1 (qForm A z) with hz | hz
  · rw [clipF_add_mul_clipF_sub_eq_zero hA hz w]; positivity
  refine (clipF_add_mul_clipF_sub_le hA z w).trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (sq_nonneg _))
  have hα0 : 0 < clipF A z := by rw [clipF_eq_of_lt hz]; linarith
  have hα1 := clipF_le_one hA z
  have hQ := qForm_nonneg hA w
  rw [neg_le_neg_iff, le_div_iff₀ hα0]
  nlinarith

/-! ### Products of clipped factors -/

/-- `φ = α₊^m β₊^{m'}` with `α = (1 - q_A)₊`, `β = (1 - q_B)₊`. -/
def clipProd (m m' : ℕ) (A B : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ := clipF A x ^ m * clipF B x ^ m'

/-- The variable modulus `H(z) = 2m M/α(z) + 2m' N/β(z)` (with `x / 0 = 0`; only its values on
the support of `clipProd m m' A B` matter). -/
noncomputable def clipHess (m m' : ℕ) (A B M N : Matrix ι ι ℝ) (x : ι → ℝ) : Matrix ι ι ℝ :=
  (2 * (m : ℝ) / clipF A x) • M + (2 * (m' : ℝ) / clipF B x) • N

theorem clipProd_nonneg (m m' : ℕ) (A B : Matrix ι ι ℝ) (x : ι → ℝ) : 0 ≤ clipProd m m' A B x :=
  mul_nonneg (pow_nonneg (clipF_nonneg A x) m) (pow_nonneg (clipF_nonneg B x) m')

theorem clipProd_le_one {A B : Matrix ι ι ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (m m' : ℕ) (x : ι → ℝ) : clipProd m m' A B x ≤ 1 :=
  calc clipProd m m' A B x ≤ 1 * 1 :=
        mul_le_mul (pow_le_one₀ (clipF_nonneg A x) (clipF_le_one hA x))
          (pow_le_one₀ (clipF_nonneg B x) (clipF_le_one hB x)) (pow_nonneg (clipF_nonneg B x) _)
          zero_le_one
    _ = 1 := one_mul 1

theorem clipProd_neg (m m' : ℕ) (A B : Matrix ι ι ℝ) (x : ι → ℝ) :
    clipProd m m' A B (-x) = clipProd m m' A B x := by
  simp only [clipProd, clipF_neg]

theorem continuous_clipProd (m m' : ℕ) (A B : Matrix ι ι ℝ) : Continuous (clipProd m m' A B) :=
  ((continuous_clipF A).pow m).mul ((continuous_clipF B).pow m')

theorem dotProduct_clipHess_mulVec (m m' : ℕ) (A B M N : Matrix ι ι ℝ) (z w : ι → ℝ) :
    w ⬝ᵥ (clipHess m m' A B M N z *ᵥ w) =
      2 * m / clipF A z * qForm M w + 2 * m' / clipF B z * qForm N w := by
  simp only [clipHess, add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul,
    qForm]

theorem clipHess_posSemidef {M N : Matrix ι ι ℝ} (hM : M.PosSemidef) (hN : N.PosSemidef)
    (m m' : ℕ) (A B : Matrix ι ι ℝ) (x : ι → ℝ) : (clipHess m m' A B M N x).PosSemidef :=
  (hM.smul (div_nonneg (by positivity) (clipF_nonneg A x))).add
    (hN.smul (div_nonneg (by positivity) (clipF_nonneg B x)))

theorem clipProd_mul_eq (m m' : ℕ) (A B : Matrix ι ι ℝ) (x y : ι → ℝ) :
    clipProd m m' A B x * clipProd m m' A B y =
      (clipF A x * clipF A y) ^ m * (clipF B x * clipF B y) ^ m' := by
  simp only [clipProd]; ring

/-- Raising two factor bounds to the powers `m, m'` and multiplying. -/
theorem clipProd_pow_le {a b : ℝ} {A B : Matrix ι ι ℝ} {x y : ι → ℝ}
    (ha : clipF A x * clipF A y ≤ a) (hb : clipF B x * clipF B y ≤ b) (m m' : ℕ) :
    (clipF A x * clipF A y) ^ m * (clipF B x * clipF B y) ^ m' ≤ a ^ m * b ^ m' := by
  have h0A : 0 ≤ clipF A x * clipF A y := mul_nonneg (clipF_nonneg _ _) (clipF_nonneg _ _)
  have h0B : 0 ≤ clipF B x * clipF B y := mul_nonneg (clipF_nonneg _ _) (clipF_nonneg _ _)
  exact mul_le_mul (pow_le_pow_left₀ h0A ha m) (pow_le_pow_left₀ h0B hb m')
    (pow_nonneg h0B _) (pow_nonneg (h0A.trans ha) _)

/-- **T.ALPHA2**, powered form: `φ(z+w) φ(z-w) ≤ φ(z)² exp(-(2m q_A(w)/α(z) + 2m' q_B(w)/β(z)))`
for `φ = α₊^m β₊^{m'}` (every `m, m'`). -/
theorem clipProd_add_mul_sub_le {A B : Matrix ι ι ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (m m' : ℕ) (z w : ι → ℝ) :
    clipProd m m' A B (z + w) * clipProd m m' A B (z - w) ≤ clipProd m m' A B z ^ 2 *
      Real.exp (-(2 * m * qForm A w / clipF A z + 2 * m' * qForm B w / clipF B z)) := by
  rw [clipProd_mul_eq]
  refine (clipProd_pow_le (clipF_add_mul_clipF_sub_le hA z w)
    (clipF_add_mul_clipF_sub_le hB z w) m m').trans_eq ?_
  rw [mul_pow, mul_pow, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
  have e : -(2 * (m : ℝ) * qForm A w / clipF A z + 2 * m' * qForm B w / clipF B z) =
      (m : ℝ) * -(2 * qForm A w / clipF A z) + (m' : ℝ) * -(2 * qForm B w / clipF B z) := by
    ring
  rw [e, Real.exp_add, clipProd]
  ring

/-- **T.ALPHA2**, powered form with the modulus `H = clipHess m m' A B M N` for `0 ⪯ M ⪯ A`,
`0 ⪯ N ⪯ B` (as `(A - M).PosSemidef`, `(B - N).PosSemidef`). -/
theorem clipProd_add_mul_sub_le_clipHess {A B M N : Matrix ι ι ℝ} (hA : A.PosSemidef)
    (hB : B.PosSemidef) (hMA : (A - M).PosSemidef) (hNB : (B - N).PosSemidef) (m m' : ℕ)
    (z w : ι → ℝ) :
    clipProd m m' A B (z + w) * clipProd m m' A B (z - w) ≤
      clipProd m m' A B z ^ 2 * Real.exp (-(w ⬝ᵥ (clipHess m m' A B M N z *ᵥ w))) := by
  refine (clipProd_add_mul_sub_le hA hB m m' z w).trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (neg_le_neg ?_)) (sq_nonneg _))
  rw [dotProduct_clipHess_mulVec]
  have c1 : 0 ≤ 2 * (m : ℝ) / clipF A z := div_nonneg (by positivity) (clipF_nonneg A z)
  have c2 : 0 ≤ 2 * (m' : ℝ) / clipF B z := div_nonneg (by positivity) (clipF_nonneg B z)
  calc 2 * (m : ℝ) / clipF A z * qForm M w + 2 * m' / clipF B z * qForm N w ≤
        2 * (m : ℝ) / clipF A z * qForm A w + 2 * m' / clipF B z * qForm B w :=
        add_le_add (mul_le_mul_of_nonneg_left (qForm_le_of_posSemidef_sub hMA w) c1)
          (mul_le_mul_of_nonneg_left (qForm_le_of_posSemidef_sub hNB w) c2)
    _ = 2 * m * qForm A w / clipF A z + 2 * m' * qForm B w / clipF B z := by ring

/-- **T.ALPHA2**, powered form with constant modulus: since `α, β ≤ 1`,
`φ(z+w) φ(z-w) ≤ φ(z)² exp(-(2m q_A(w) + 2m' q_B(w)))`. -/
theorem clipProd_add_mul_sub_le_exp {A B : Matrix ι ι ℝ} (hA : A.PosSemidef)
    (hB : B.PosSemidef) (m m' : ℕ) (z w : ι → ℝ) :
    clipProd m m' A B (z + w) * clipProd m m' A B (z - w) ≤
      clipProd m m' A B z ^ 2 * Real.exp (-(2 * m * qForm A w + 2 * m' * qForm B w)) := by
  rw [clipProd_mul_eq]
  refine (clipProd_pow_le (clipF_add_mul_clipF_sub_le_exp hA z w)
    (clipF_add_mul_clipF_sub_le_exp hB z w) m m').trans_eq ?_
  rw [mul_pow, mul_pow, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
  have e : -(2 * (m : ℝ) * qForm A w + 2 * m' * qForm B w) =
      (m : ℝ) * -(2 * qForm A w) + (m' : ℝ) * -(2 * qForm B w) := by ring
  rw [e, Real.exp_add, clipProd]
  ring

/-! ### Multiplying by the standard Gaussian weight: the BLmid hypothesis -/

/-- `ρ = φ e^{-|x|²/2}`. -/
noncomputable def gaussWt (φ : (ι → ℝ) → ℝ) (x : ι → ℝ) : ℝ := φ x * Real.exp (-(x ⬝ᵥ x) / 2)

theorem gaussWt_nonneg {φ : (ι → ℝ) → ℝ} (hφ : ∀ x, 0 ≤ φ x) (x : ι → ℝ) : 0 ≤ gaussWt φ x :=
  mul_nonneg (hφ x) (Real.exp_pos _).le

theorem gaussWt_neg {φ : (ι → ℝ) → ℝ} (hφ : ∀ x, φ (-x) = φ x) (x : ι → ℝ) :
    gaussWt φ (-x) = gaussWt φ x := by
  simp only [gaussWt, hφ, neg_dotProduct, dotProduct_neg, neg_neg]

/-- If `φ(z+w) φ(z-w) ≤ φ(z)² e^{-⟨w, H(z) w⟩}` then `ρ = φ e^{-|x|²/2}` satisfies
`ρ(z+w) ρ(z-w) ≤ ρ(z)² e^{-⟨w, (I + H(z)) w⟩}`, because
`|z+w|² + |z-w|² = 2|z|² + 2|w|²`. -/
theorem gaussWt_midpoint {φ : (ι → ℝ) → ℝ} [DecidableEq ι] {H : (ι → ℝ) → Matrix ι ι ℝ}
    (hφ : ∀ z w, φ (z + w) * φ (z - w) ≤ φ z ^ 2 * Real.exp (-(w ⬝ᵥ (H z *ᵥ w))))
    (z w : ι → ℝ) :
    gaussWt φ (z + w) * gaussWt φ (z - w) ≤
      gaussWt φ z ^ 2 * Real.exp (-(w ⬝ᵥ ((1 + H z) *ᵥ w))) := by
  have hexp : Real.exp (-((z + w) ⬝ᵥ (z + w)) / 2) * Real.exp (-((z - w) ⬝ᵥ (z - w)) / 2) =
      Real.exp (-(z ⬝ᵥ z) / 2) ^ 2 * Real.exp (-(w ⬝ᵥ w)) := by
    rw [← Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    simp only [add_dotProduct, dotProduct_add, sub_dotProduct, dotProduct_sub]
    push_cast
    ring
  have hK : w ⬝ᵥ ((1 + H z) *ᵥ w) = w ⬝ᵥ w + w ⬝ᵥ (H z *ᵥ w) := by
    rw [add_mulVec, one_mulVec, dotProduct_add]
  have e1 : gaussWt φ (z + w) * gaussWt φ (z - w) = (φ (z + w) * φ (z - w)) *
      (Real.exp (-(z ⬝ᵥ z) / 2) ^ 2 * Real.exp (-(w ⬝ᵥ w))) := by
    simp only [gaussWt]; rw [← hexp]; ring
  have e2 : gaussWt φ z ^ 2 * Real.exp (-(w ⬝ᵥ ((1 + H z) *ᵥ w))) =
      (φ z ^ 2 * Real.exp (-(w ⬝ᵥ (H z *ᵥ w)))) *
        (Real.exp (-(z ⬝ᵥ z) / 2) ^ 2 * Real.exp (-(w ⬝ᵥ w))) := by
    simp only [gaussWt]; rw [hK, neg_add, Real.exp_add]; ring
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_right (hφ z w) (by positivity)

/-- **T.ALPHA2 in BLmid shape** (variable modulus): `ρ = α₊^m β₊^{m'} e^{-|x|²/2}` satisfies
BLmid's `hmid` with `K = I + clipHess m m' A B M N`, for `0 ⪯ M ⪯ A`, `0 ⪯ N ⪯ B`. -/
theorem gaussWt_clipProd_midpoint [DecidableEq ι] {A B M N : Matrix ι ι ℝ} (hA : A.PosSemidef)
    (hB : B.PosSemidef) (hMA : (A - M).PosSemidef) (hNB : (B - N).PosSemidef) (m m' : ℕ)
    (z w : ι → ℝ) :
    gaussWt (clipProd m m' A B) (z + w) * gaussWt (clipProd m m' A B) (z - w) ≤
      gaussWt (clipProd m m' A B) z ^ 2 *
        Real.exp (-(w ⬝ᵥ ((1 + clipHess m m' A B M N z) *ᵥ w))) :=
  gaussWt_midpoint (clipProd_add_mul_sub_le_clipHess hA hB hMA hNB m m') z w

/-- **T.ALPHA2 in BLmid shape** (constant modulus `K = I + c A`, `c ≤ 2m`). -/
theorem gaussWt_clipProd_midpoint_const [DecidableEq ι] {A B : Matrix ι ι ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (m m' : ℕ) {c : ℝ} (hc : c ≤ 2 * m)
    (z w : ι → ℝ) :
    gaussWt (clipProd m m' A B) (z + w) * gaussWt (clipProd m m' A B) (z - w) ≤
      gaussWt (clipProd m m' A B) z ^ 2 * Real.exp (-(w ⬝ᵥ ((1 + c • A) *ᵥ w))) := by
  refine gaussWt_midpoint (H := fun _ => c • A) (fun z w => ?_) z w
  refine (clipProd_add_mul_sub_le_exp hA hB m m' z w).trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (neg_le_neg ?_)) (sq_nonneg _))
  have hQA := qForm_nonneg hA w
  have hQB := qForm_nonneg hB w
  have e : w ⬝ᵥ ((c • A) *ᵥ w) = c * qForm A w := by
    simp only [smul_mulVec, dotProduct_smul, smul_eq_mul, qForm]
  rw [e]
  nlinarith [mul_le_mul_of_nonneg_right hc hQA]

end BiluLinial.Tight
