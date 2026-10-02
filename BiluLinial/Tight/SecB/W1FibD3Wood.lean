/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecB.W1FibD3Jet
public import BiluLinial.Tight.SecA.EndpointPfRank2

/-!
# TB.W1fib-d3: the rank-two (Woodbury) representation along an edge fibre

For `B ≻ 0`, physical entries `M = physInv y B` (`M_kl = √y_k (B⁻¹)_kl √y_l`) and the edge
perturbation `B(s) = B + sθ√(y_iy_j) E` (`E = e_ie_jᵀ + e_je_iᵀ`, `i ≠ j`):

* `physInv_add_edge` (Woodbury): `physInv y B(s) = M - Σ_{α,β ∈ {i,j}} M_{·α} ρ_αβ(s) M_{β·}` with
  `ρ_ii = -s²θ²M_jj/δ`, `ρ_jj = -s²θ²M_ii/δ`, `ρ_ij = ρ_ji = (sθ + s²θ²M_ij)/δ` and
  `δ(s) = 1 + 2sθM_ij - s²θ²(M_iiM_jj - M_ij²)` (`wDelta`), whenever `δ(s) ≠ 0`. Proof: the
  explicit matrix `N` satisfies `B(s) N = 1` (the four `2 × 2` identities `wEq1`–`wEq4`).
* `det_add_edge`: `det B(s) = det B · δ(s)` (`SecA.det_add_rank_two_pf`).
* `jb_rho`: bounded jets of `ρ` on `|t - t₀| ≤ 3` when `a(|M_ii| + |M_jj| + |M_ij|) ≤ 1/32`,
  `|θ| ≤ a ≤ 1`, `|M_ii|, |M_jj|, |M_ij| ≤ D`: `|ρ^{(r)}| ≤ 665280 D (aD)^r`.
* `jb_physInv_edge`: the bounded jet (`wJet`) of every entry `t ↦ physInv y B(t - t₀) k l`.
-/

@[expose] public section

namespace BiluLinial.Tight.SecB

open Matrix

/-! ### Scalar functions -/

/-- `δ(s) = 1 + 2θk_ij s - θ²(k_ii k_jj - k_ij²) s²`. -/
noncomputable def wDelta (θ kii kjj kij s : ℝ) : ℝ :=
  1 + 2 * θ * kij * s + -(θ ^ 2 * (kii * kjj - kij ^ 2)) * s ^ 2

/-- `ρ_ii = -θ² k_jj s²/δ`. -/
noncomputable def wRii (θ kii kjj kij s : ℝ) : ℝ :=
  (0 + 0 * s + -(θ ^ 2 * kjj) * s ^ 2) * (wDelta θ kii kjj kij s)⁻¹

/-- `ρ_ij = (θ s + θ² k_ij s²)/δ`. -/
noncomputable def wRij (θ kii kjj kij s : ℝ) : ℝ :=
  (0 + θ * s + θ ^ 2 * kij * s ^ 2) * (wDelta θ kii kjj kij s)⁻¹

/-- `ρ_jj = -θ² k_ii s²/δ`. -/
noncomputable def wRjj (θ kii kjj kij s : ℝ) : ℝ :=
  (0 + 0 * s + -(θ ^ 2 * kii) * s ^ 2) * (wDelta θ kii kjj kij s)⁻¹

section Mat

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The rank-two correction `Σ_{α,β} M_kα ρ_αβ M_βl`. -/
noncomputable def wCorr (M : Matrix n n ℝ) (i j : n) (rii rij rjj : ℝ) (k l : n) : ℝ :=
  M k i * rii * M i l + M k i * rij * M j l + M k j * rij * M i l + M k j * rjj * M j l

theorem edgeE_mul_apply (i j : n) (N : Matrix n n ℝ) (k l : n) :
    (SecA.edgeE i j * N) k l = (if i = k then N j l else 0) + (if j = k then N i l else 0) := by
  rw [Matrix.mul_apply]
  simp only [SecA.epf_edgeE_apply, add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul,
    ite_and, Finset.sum_ite_irrel, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Finset.sum_const_zero]

/-- **Woodbury along an edge.** -/
theorem physInv_add_edge {B : Matrix n n ℝ} (hB : B.PosDef) (y : n → ℝ) {i j : n} (hij : i ≠ j)
    (θ s : ℝ)
    (hδ : wDelta θ (physInv y B i i) (physInv y B j j) (physInv y B i j) s ≠ 0) (k l : n) :
    physInv y (B + (s * (θ * (Real.sqrt (y i) * Real.sqrt (y j)))) • SecA.edgeE i j) k l =
      physInv y B k l - wCorr (physInv y B) i j
        (wRii θ (physInv y B i i) (physInv y B j j) (physInv y B i j) s)
        (wRij θ (physInv y B i i) (physInv y B j j) (physInv y B i j) s)
        (wRjj θ (physInv y B i i) (physInv y B j j) (physInv y B i j) s) k l := by
  have hdet : IsUnit B.det := hB.det_pos.ne'.isUnit
  set h := B⁻¹ with hh
  have hsym : ∀ a b, h a b = h b a := fun a b => SecA.epf_inv_symm hB.1 a b
  set κ := s * (θ * (Real.sqrt (y i) * Real.sqrt (y j))) with hκ
  have hK : ∀ a b, physInv y B a b = Real.sqrt (y a) * h a b * Real.sqrt (y b) := fun a b => rfl
  set δ := wDelta θ (physInv y B i i) (physInv y B j j) (physInv y B i j) s with hδdef
  have hδn : δ = (1 + κ * h i j) ^ 2 - κ ^ 2 * (h i i * h j j) := by
    rw [hδdef, wDelta, hK, hK, hK, hκ]
    ring
  set Rii := Real.sqrt (y i) * wRii θ (physInv y B i i) (physInv y B j j) (physInv y B i j) s *
    Real.sqrt (y i) with hRii
  set Rij := Real.sqrt (y i) * wRij θ (physInv y B i i) (physInv y B j j) (physInv y B i j) s *
    Real.sqrt (y j) with hRij
  set Rjj := Real.sqrt (y j) * wRjj θ (physInv y B i i) (physInv y B j j) (physInv y B i j) s *
    Real.sqrt (y j) with hRjj
  have eRii : Rii = -(κ ^ 2 * h j j) / δ := by
    rw [hRii, wRii, ← hδdef, hK, hκ]; field_simp; ring
  have eRij : Rij = κ * (1 + κ * h i j) / δ := by
    rw [hRij, wRij, ← hδdef, hK, hκ]; field_simp; ring
  have eRjj : Rjj = -(κ ^ 2 * h i i) / δ := by
    rw [hRjj, wRjj, ← hδdef, hK, hκ]; field_simp; ring
  have q1 : Rii * (1 + κ * h i j) + κ * h j j * Rij = 0 := by
    rw [eRii, eRij]; field_simp; ring
  have q2 : Rij * (1 + κ * h i j) + κ * h j j * Rjj = κ := by
    rw [eRij, eRjj]; field_simp; rw [hδn]; ring
  have q3 : κ * h i i * Rii + Rij * (1 + κ * h i j) = κ := by
    rw [eRii, eRij]; field_simp; rw [hδn]; ring
  have q4 : κ * h i i * Rij + Rjj * (1 + κ * h i j) = 0 := by
    rw [eRij, eRjj]; field_simp; ring
  set N : Matrix n n ℝ := Matrix.of fun a b => h a b -
    (h a i * Rii * h i b + h a i * Rij * h j b + h a j * Rij * h i b + h a j * Rjj * h j b) with hN
  have hBN : ∀ a b, (B * N) a b = (1 : Matrix n n ℝ) a b -
      (1 : Matrix n n ℝ) a i * (Rii * h i b + Rij * h j b) -
      (1 : Matrix n n ℝ) a j * (Rij * h i b + Rjj * h j b) := by
    intro a b
    have e : ∀ x, ∑ m, B a m * h m x = (1 : Matrix n n ℝ) a x := fun x => by
      rw [← Matrix.mul_apply, hh, Matrix.mul_nonsing_inv _ hdet]
    rw [Matrix.mul_apply]
    simp only [hN, Matrix.of_apply]
    have e2 : ∀ m, B a m * (h m b - (h m i * Rii * h i b + h m i * Rij * h j b +
        h m j * Rij * h i b + h m j * Rjj * h j b)) = B a m * h m b -
        B a m * h m i * (Rii * h i b + Rij * h j b) -
        B a m * h m j * (Rij * h i b + Rjj * h j b) := fun m => by ring
    simp only [e2, Finset.sum_sub_distrib, ← Finset.sum_mul, e]
  have hMN : (B + κ • SecA.edgeE i j) * N = 1 := by
    ext a b
    rw [Matrix.add_mul, Matrix.add_apply, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul,
      hBN, edgeE_mul_apply]
    simp only [hN, Matrix.of_apply]
    by_cases hai : a = i
    · subst hai
      rw [if_pos rfl, if_neg (fun h => hij h.symm), Matrix.one_apply_eq, Matrix.one_apply_ne hij,
        hsym j a]
      by_cases hab : a = b
      · subst hab
        rw [Matrix.one_apply_eq]
        linear_combination (-(h a a)) * q1 + (-(h j a)) * q2
      · rw [Matrix.one_apply_ne hab]
        linear_combination (-(h a b)) * q1 + (-(h j b)) * q2
    · by_cases haj : a = j
      · subst haj
        rw [if_neg (fun h => hai h.symm), if_pos rfl, Matrix.one_apply_eq,
          Matrix.one_apply_ne (Ne.symm hij)]
        linear_combination (-(h i b)) * q3 + (-(h a b)) * q4
      · rw [if_neg (fun h => hai h.symm), if_neg (fun h => haj h.symm), Matrix.one_apply_ne hai,
          Matrix.one_apply_ne haj]
        ring
  have hinv : (B + κ • SecA.edgeE i j)⁻¹ = N := Matrix.inv_eq_right_inv hMN
  have hL : physInv y (B + κ • SecA.edgeE i j) k l =
      Real.sqrt (y k) * N k l * Real.sqrt (y l) := by
    change Real.sqrt (y k) * (B + κ • SecA.edgeE i j)⁻¹ k l * Real.sqrt (y l) = _
    rw [hinv]
  rw [hL]
  simp only [hN, Matrix.of_apply, wCorr]
  rw [hK k l, hK k i, hK i l, hK k j, hK j l, hRii, hRij, hRjj]
  ring

/-- `det B(s) = det B · δ(s)`. -/
theorem det_add_edge {B : Matrix n n ℝ} (hB : B.PosDef) (y : n → ℝ) {i j : n} (hij : i ≠ j)
    (θ s : ℝ) :
    (B + (s * (θ * (Real.sqrt (y i) * Real.sqrt (y j)))) • SecA.edgeE i j).det =
      B.det * wDelta θ (physInv y B i i) (physInv y B j j) (physInv y B i j) s := by
  rw [SecA.det_add_rank_two_pf hB.1 hB.det_pos.ne'.isUnit hij]
  congr 1
  simp only [wDelta, physInv, Matrix.of_apply]
  ring

end Mat

/-! ### Jets of `ρ` -/

/-- The jet of `δ`. -/
noncomputable def dJ (θ kii kjj kij t₀ : ℝ) : ℕ → ℝ → ℝ :=
  jquad 1 (2 * θ * kij) (-(θ ^ 2 * (kii * kjj - kij ^ 2))) t₀

noncomputable def rJii (θ kii kjj kij t₀ : ℝ) : ℕ → ℝ → ℝ :=
  jmul (jquad 0 0 (-(θ ^ 2 * kjj)) t₀) (jinv (dJ θ kii kjj kij t₀))

noncomputable def rJij (θ kii kjj kij t₀ : ℝ) : ℕ → ℝ → ℝ :=
  jmul (jquad 0 θ (θ ^ 2 * kij) t₀) (jinv (dJ θ kii kjj kij t₀))

noncomputable def rJjj (θ kii kjj kij t₀ : ℝ) : ℕ → ℝ → ℝ :=
  jmul (jquad 0 0 (-(θ ^ 2 * kii)) t₀) (jinv (dJ θ kii kjj kij t₀))

/-- Bounds for the quadratic jet on `|t - t₀| ≤ 3`. -/
theorem jetLe_quad {U : Set ℝ} {t₀ : ℝ} (hU : ∀ t ∈ U, |t - t₀| ≤ 3) {c₀ c₁ c₂ A l : ℝ}
    (h0 : |c₀| + 3 * |c₁| + 9 * |c₂| ≤ A) (h1 : |c₁| + 6 * |c₂| ≤ A * l)
    (h2 : 2 * |c₂| ≤ A * l ^ 2) (h3 : 0 ≤ A * l ^ 3) : JetLe U (jquad c₀ c₁ c₂ t₀) A l := by
  intro r hr t ht
  have hs := hU t ht
  have hs0 := abs_nonneg (t - t₀)
  rcases le_three_cases hr with rfl | rfl | rfl | rfl
  · change |c₀ + c₁ * (t - t₀) + c₂ * (t - t₀) ^ 2| ≤ A * l ^ 0
    have a1 : |c₁ * (t - t₀)| ≤ |c₁| * 3 := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left hs (abs_nonneg _)
    have a2 : |c₂ * (t - t₀) ^ 2| ≤ |c₂| * 9 := by
      rw [abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_left (by nlinarith) (abs_nonneg _)
    have := abs_add_le (c₀ + c₁ * (t - t₀)) (c₂ * (t - t₀) ^ 2)
    have := abs_add_le c₀ (c₁ * (t - t₀))
    rw [pow_zero, mul_one]
    linarith
  · change |c₁ + 2 * c₂ * (t - t₀)| ≤ A * l ^ 1
    have a1 : |2 * c₂ * (t - t₀)| ≤ 6 * |c₂| := by
      rw [abs_mul, abs_mul, abs_two]; nlinarith [abs_nonneg c₂]
    have := abs_add_le c₁ (2 * c₂ * (t - t₀))
    rw [pow_one]
    linarith
  · change |2 * c₂| ≤ A * l ^ 2
    rw [abs_mul, abs_two]; exact h2
  · change |(0 : ℝ)| ≤ A * l ^ 3
    rw [abs_zero]; exact h3

/-- Bounds on the jet of `δ`. -/
theorem dJ_bounds {U : Set ℝ} {t₀ : ℝ} (hU : ∀ t ∈ U, |t - t₀| ≤ 3) {θ kii kjj kij a D : ℝ}
    (hθ : |θ| ≤ a) (ha0 : 0 ≤ a) (hD : 1 ≤ D) (hii : |kii| ≤ D) (hjj : |kjj| ≤ D)
    (hij : |kij| ≤ D) (hsm : a * (|kii| + |kjj| + |kij|) ≤ 1 / 32) :
    (∀ t ∈ U, 1 / 2 ≤ |dJ θ kii kjj kij t₀ 0 t|) ∧
      ∀ r, 1 ≤ r → r ≤ 3 → ∀ t ∈ U, |dJ θ kii kjj kij t₀ r t| ≤ 4 * (a * D) ^ r := by
  have hθ2 : θ ^ 2 ≤ a ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hθ 2
  have hai : a * |kii| ≤ 1 / 32 := by nlinarith [abs_nonneg kjj, abs_nonneg kij]
  have haj : a * |kjj| ≤ 1 / 32 := by nlinarith [abs_nonneg kii, abs_nonneg kij]
  have hak : a * |kij| ≤ 1 / 32 := by nlinarith [abs_nonneg kii, abs_nonneg kjj]
  have hΔ : |kii * kjj - kij ^ 2| ≤ |kii| * |kjj| + |kij| ^ 2 := by
    have := abs_sub (kii * kjj) (kij ^ 2)
    rw [abs_mul, abs_pow] at this
    exact this
  have hc2 : |-(θ ^ 2 * (kii * kjj - kij ^ 2))| ≤ a ^ 2 * (|kii| * |kjj| + |kij| ^ 2) := by
    rw [abs_neg, abs_mul, abs_of_nonneg (sq_nonneg θ)]
    exact mul_le_mul hθ2 hΔ (abs_nonneg _) (sq_nonneg a)
  have hc1 : |2 * θ * kij| ≤ 2 * a * |kij| := by
    rw [abs_mul, abs_mul, abs_two]; nlinarith [abs_nonneg kij]
  have e1 : a ^ 2 * (|kii| * |kjj| + |kij| ^ 2) ≤ a * D / 16 := by
    have e : a ^ 2 * (|kii| * |kjj| + |kij| ^ 2) =
        a * (|kii| * (a * |kjj|) + |kij| * (a * |kij|)) := by ring
    rw [e]
    have h1 := mul_le_mul hii haj (by positivity) (by linarith)
    have h2 := mul_le_mul hij hak (by positivity) (by linarith)
    have : |kii| * (a * |kjj|) + |kij| * (a * |kij|) ≤ D / 16 := by linarith
    have := mul_le_mul_of_nonneg_left this ha0
    linarith
  have e2 : a ^ 2 * (|kii| * |kjj| + |kij| ^ 2) ≤ 2 * (a * D) ^ 2 := by
    have : |kii| * |kjj| + |kij| ^ 2 ≤ D * D + D * D := by
      have := mul_le_mul hii hjj (abs_nonneg _) (by linarith)
      have := mul_le_mul hij hij (abs_nonneg _) (by linarith)
      nlinarith
    nlinarith
  have e3 : a ^ 2 * (|kii| * |kjj| + |kij| ^ 2) ≤ 1 / 512 := by
    have : a ^ 2 * (|kii| * |kjj| + |kij| ^ 2) = (a * |kii|) * (a * |kjj|) + (a * |kij|) ^ 2 := by
      ring
    rw [this]
    have := mul_le_mul hai haj (by positivity) (by norm_num)
    have := pow_le_pow_left₀ (by positivity) hak 2
    linarith
  refine ⟨fun t ht => ?_, fun r hr1 hr3 t ht => ?_⟩
  · have hs := hU t ht
    change 1 / 2 ≤ |1 + 2 * θ * kij * (t - t₀) + -(θ ^ 2 * (kii * kjj - kij ^ 2)) * (t - t₀) ^ 2|
    have a1 : |2 * θ * kij * (t - t₀)| ≤ 2 * a * |kij| * 3 := by
      rw [abs_mul]; exact mul_le_mul hc1 hs (abs_nonneg _) (by positivity)
    have a2 : |-(θ ^ 2 * (kii * kjj - kij ^ 2)) * (t - t₀) ^ 2| ≤
        a ^ 2 * (|kii| * |kjj| + |kij| ^ 2) * 9 := by
      rw [abs_mul, abs_pow]
      exact mul_le_mul hc2 (by nlinarith [abs_nonneg (t - t₀)]) (by positivity) (by positivity)
    have b1 := neg_abs_le (2 * θ * kij * (t - t₀))
    have b2 := neg_abs_le (-(θ ^ 2 * (kii * kjj - kij ^ 2)) * (t - t₀) ^ 2)
    have := le_abs_self
      (1 + 2 * θ * kij * (t - t₀) + -(θ ^ 2 * (kii * kjj - kij ^ 2)) * (t - t₀) ^ 2)
    linarith
  · have hs := hU t ht
    have hl : 0 ≤ a * D := by positivity
    rcases (show r = 1 ∨ r = 2 ∨ r = 3 by omega) with rfl | rfl | rfl
    · change |2 * θ * kij + 2 * -(θ ^ 2 * (kii * kjj - kij ^ 2)) * (t - t₀)| ≤ 4 * (a * D) ^ 1
      have a2 : |2 * -(θ ^ 2 * (kii * kjj - kij ^ 2)) * (t - t₀)| ≤
          2 * (a ^ 2 * (|kii| * |kjj| + |kij| ^ 2)) * 3 := by
        rw [abs_mul, abs_mul, abs_two]
        exact mul_le_mul (by linarith) hs (abs_nonneg _) (by positivity)
      have := abs_add_le (2 * θ * kij) (2 * -(θ ^ 2 * (kii * kjj - kij ^ 2)) * (t - t₀))
      have : a * |kij| ≤ a * D := mul_le_mul_of_nonneg_left hij ha0
      rw [pow_one]
      linarith
    · change |2 * -(θ ^ 2 * (kii * kjj - kij ^ 2))| ≤ 4 * (a * D) ^ 2
      rw [abs_mul, abs_two]
      linarith
    · change |(0 : ℝ)| ≤ 4 * (a * D) ^ 3
      rw [abs_zero]; positivity

theorem two_a2D_le {a D : ℝ} (ha0 : 0 ≤ a) (hD : 1 ≤ D) : 2 * (a ^ 2 * D) ≤ 12 * D * (a * D) ^ 2 := by
  have h1 : (2 : ℝ) ≤ 12 * D ^ 2 := by nlinarith
  have h2 : 0 ≤ a ^ 2 * D := by positivity
  calc 2 * (a ^ 2 * D) ≤ 12 * D ^ 2 * (a ^ 2 * D) := mul_le_mul_of_nonneg_right h1 h2
    _ = 12 * D * (a * D) ^ 2 := by ring

/-- Bounded jets of `ρ`. -/
theorem jb_rho {U : Set ℝ} {t₀ : ℝ} (hU : ∀ t ∈ U, |t - t₀| ≤ 3) {θ kii kjj kij a D : ℝ}
    (hθ : |θ| ≤ a) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hD : 1 ≤ D) (hii : |kii| ≤ D) (hjj : |kjj| ≤ D)
    (hij : |kij| ≤ D) (hsm : a * (|kii| + |kjj| + |kij|) ≤ 1 / 32) :
    JB U (fun t => wRii θ kii kjj kij (t - t₀)) (rJii θ kii kjj kij t₀) (665280 * D) (a * D) ∧
      JB U (fun t => wRij θ kii kjj kij (t - t₀)) (rJij θ kii kjj kij t₀) (665280 * D) (a * D) ∧
      JB U (fun t => wRjj θ kii kjj kij (t - t₀)) (rJjj θ kii kjj kij t₀) (665280 * D)
        (a * D) := by
  obtain ⟨d0, dr⟩ := dJ_bounds hU hθ ha0 hD hii hjj hij hsm
  have hl : 0 ≤ a * D := by positivity
  have hD0 : 0 ≤ D := by linarith
  have hθ2 : θ ^ 2 ≤ a ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hθ 2
  have hjd : JetOf U (fun t => 1 + 2 * θ * kij * (t - t₀) +
      -(θ ^ 2 * (kii * kjj - kij ^ 2)) * (t - t₀) ^ 2) (dJ θ kii kjj kij t₀) :=
    jetOf_quad U _ _ _ t₀
  have hinv := JB.inv hjd d0 (by norm_num) hl dr
  have hA : (2 + 4 * 4 + 48 * 4 ^ 2 + 96 * 4 ^ 3 : ℝ) = 6930 := by norm_num
  rw [hA] at hinv
  have ha2 : a ^ 2 ≤ a := by nlinarith
  -- numerator `-(θ² k) s²` with `|k| ≤ D`
  have hnum0 : ∀ k : ℝ, |k| ≤ D →
      JB U (fun t => 0 + 0 * (t - t₀) + -(θ ^ 2 * k) * (t - t₀) ^ 2) (jquad 0 0 (-(θ ^ 2 * k)) t₀)
        (12 * D) (a * D) := fun k hk => by
    refine ⟨jetOf_quad U _ _ _ t₀, jetLe_quad hU ?_ ?_ ?_ (by positivity)⟩
    · have : |-(θ ^ 2 * k)| ≤ a ^ 2 * D := by
        rw [abs_neg, abs_mul, abs_of_nonneg (sq_nonneg θ)]
        exact mul_le_mul hθ2 hk (abs_nonneg _) (sq_nonneg a)
      simp only [abs_zero]
      nlinarith
    · have : |-(θ ^ 2 * k)| ≤ a ^ 2 * D := by
        rw [abs_neg, abs_mul, abs_of_nonneg (sq_nonneg θ)]
        exact mul_le_mul hθ2 hk (abs_nonneg _) (sq_nonneg a)
      simp only [abs_zero]
      nlinarith
    · have : |-(θ ^ 2 * k)| ≤ a ^ 2 * D := by
        rw [abs_neg, abs_mul, abs_of_nonneg (sq_nonneg θ)]
        exact mul_le_mul hθ2 hk (abs_nonneg _) (sq_nonneg a)
      linarith [two_a2D_le ha0 hD]
  have hnum1 : JB U (fun t => 0 + θ * (t - t₀) + θ ^ 2 * kij * (t - t₀) ^ 2)
      (jquad 0 θ (θ ^ 2 * kij) t₀) (12 * D) (a * D) := by
    have hc : |θ ^ 2 * kij| ≤ a ^ 2 * D := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg θ)]
      exact mul_le_mul hθ2 hij (abs_nonneg _) (sq_nonneg a)
    refine ⟨jetOf_quad U _ _ _ t₀, jetLe_quad hU ?_ ?_ ?_ (by positivity)⟩
    · simp only [abs_zero]; nlinarith
    · nlinarith
    · linarith [two_a2D_le ha0 hD]
  have e : (8 * (12 * D * 6930) : ℝ) = 665280 * D := by ring
  have m0 := JB.mul (hnum0 kjj hjj) hinv (by positivity) (by norm_num) hl
  have m1 := JB.mul hnum1 hinv (by positivity) (by norm_num) hl
  have m2 := JB.mul (hnum0 kii hii) hinv (by positivity) (by norm_num) hl
  rw [e] at m0 m1 m2
  exact ⟨m0, m1, m2⟩

/-! ### Jets of the entries -/

section MatJet

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The jet of `t ↦ M_kl - Σ M_kα ρ_αβ(t - t₀) M_βl`. -/
noncomputable def wJet (M : Matrix n n ℝ) (i j : n) (θ t₀ : ℝ) (k l : n) : ℕ → ℝ → ℝ :=
  jsub (jconst (M k l))
    (jadd (jadd (jadd (jsmul (M k i * M i l) (rJii θ (M i i) (M j j) (M i j) t₀))
      (jsmul (M k i * M j l) (rJij θ (M i i) (M j j) (M i j) t₀)))
      (jsmul (M k j * M i l) (rJij θ (M i i) (M j j) (M i j) t₀)))
      (jsmul (M k j * M j l) (rJjj θ (M i i) (M j j) (M i j) t₀)))

/-- The entry jet along the edge fibre, with bound
`|M_kl| + 665280 D (|M_ki M_il| + |M_ki M_jl| + |M_kj M_il| + |M_kj M_jl|)`. -/
theorem jb_physInv_edge {B : Matrix n n ℝ} (hB : B.PosDef) (y : n → ℝ) {i j : n} (hij : i ≠ j)
    {U : Set ℝ} {t₀ : ℝ} (hU : ∀ t ∈ U, |t - t₀| ≤ 3) {θ a D : ℝ} (hθ : |θ| ≤ a) (ha0 : 0 ≤ a)
    (ha1 : a ≤ 1) (hD : 1 ≤ D) (hii : |physInv y B i i| ≤ D) (hjj : |physInv y B j j| ≤ D)
    (hijD : |physInv y B i j| ≤ D)
    (hsm : a * (|physInv y B i i| + |physInv y B j j| + |physInv y B i j|) ≤ 1 / 32) (k l : n) :
    JB U (fun t => physInv y (B + ((t - t₀) * (θ * (Real.sqrt (y i) * Real.sqrt (y j)))) •
        SecA.edgeE i j) k l) (wJet (physInv y B) i j θ t₀ k l)
      (|physInv y B k l| + 665280 * D * (|physInv y B k i * physInv y B i l| +
        |physInv y B k i * physInv y B j l| + |physInv y B k j * physInv y B i l| +
        |physInv y B k j * physInv y B j l|)) (a * D) := by
  obtain ⟨r1, r2, r3⟩ := jb_rho hU hθ ha0 ha1 hD hii hjj hijD hsm
  have hl : 0 ≤ a * D := by positivity
  have h := (jb_const U (physInv y B k l) hl).sub
    ((((r1.smul (physInv y B k i * physInv y B i l)).add
      (r2.smul (physInv y B k i * physInv y B j l))).add
        (r2.smul (physInv y B k j * physInv y B i l))).add
          (r3.smul (physInv y B k j * physInv y B j l)))
  obtain ⟨d0, -⟩ := dJ_bounds hU hθ ha0 hD hii hjj hijD hsm
  refine (h.congr fun t ht => ?_).mono (le_of_eq (by ring)) hl
  have hδ : wDelta θ (physInv y B i i) (physInv y B j j) (physInv y B i j) (t - t₀) ≠ 0 := by
    intro h0
    have := d0 t ht
    change 1 / 2 ≤ |wDelta θ (physInv y B i i) (physInv y B j j) (physInv y B i j) (t - t₀)|
      at this
    rw [h0, abs_zero] at this
    linarith
  rw [physInv_add_edge hB y hij θ (t - t₀) hδ k l, wCorr]
  beta_reduce
  ring

end MatJet

end BiluLinial.Tight.SecB
