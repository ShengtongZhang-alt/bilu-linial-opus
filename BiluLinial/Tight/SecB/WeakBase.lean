/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecB.S1
public import BiluLinial.Tight.Tools.Interp
public import BiluLinial.Tight.SourceMax
public import BiluLinial.Tight.ParamsExtra
public import BiluLinial.Tight.SecA.ParP

/-!
# Random-profile weak loop (W1)–(W5): the base nodes

Nodes TB.row, TB.W2, TB.ward, TB.S1w, TB.Dstar, TB.W5 of `docs/tight/BP_SECB.md` (source
Lemma "Random-profile weak loop", lines 721–911; AUDIT-B §2.4 with fixes B-2, B-3;
`docs/tight/DR1_CHECK.md` §3, W1′). The weak loop TB.W1 itself is decomposed in `SecB/W1.lean`
and assembled in `SecB/Weak.lean` (`weak_loop_of`).

Notation at a contact (`Tight/Contact/Defs.lean`): `X_± = (P^± + hI)⁻¹` (`XP`, `XM`, physical),
`u = 1_N/√d`, `T = a² A_H`, `K₊ = X₊∘X₊/4`, `K₋ = X₊∘X₋/4`, `M₊ = diag((X₊)²_ii/4)`,
`M₋ = diag((X₊)_ii (X₋)_ii/4)`, `b_± = 4 T M_± u`, the Schur column
`F_ji = (X_ε)_ii U_ji - (X_ε)_ji U_ii` of the mask `U = X_ε D_f X_ν` (`maskF`), `D_*` (`Dstar`).

* **TB.row** (`shift_row_identity`, exact): row `i ∈ S` of `(P̃ + zY)(P̃ + zY)⁻¹ = I`, multiplied by
  `√y_i √y_l`: `(D_i + z y_i) X_il + τ a y_i Σ_{k∼i} σ_ik X_kl = 1_{i=l} y_i` (physical
  `(P + z)X = I` without dividing by sources).
* **TB.W2** (`weak_w2`, exact, pointwise): for any matrix `X_ν` and mask `f`,
  `U_ii - f_i (X_ε)_ii (X_ν)_ii = -ε a Σ_{j∼i} σ_ij F_ji` (`X_ε` the branch-`ε` shifted inverse).
  Proof: `(X_ε)_ii` times row `i` of `(P^ε+h)U = D_f X_ν` minus `U_ii` times row `i` of
  `(P^ε+h)X_ε = I` (TB.row), divided by `y_i` (at `y_i = 0` both sides vanish).
* **TB.ward** (`ward_diag`): on the support, for `i ∈ S`, `h > 0`:
  `(X²)_ii ≤ (G_ii - X_ii)/h`. Proof: `G - X = h G X` (resolvent identity), so `GX` is symmetric,
  `G` and `X` commute and `X² = GX - h XGX ⪯ (G - X)/h`.
* **TB.S1w** (`mean_shift_weighted_of_cl1`, weighted S1): for `Z ≥ 0` with `‖Z‖_k ≤ B`,
  `log d + 2 ≤ k ≤ p/2`: `E[(G_ii - X_ii) Z] ≤ 3(K_S + 2) B √h y_i`. Proof: UMI (Tools `T.IL`,
  `wavg_mul_le_umi`) with `Y = G_ii - X_ii ∈ [0, G_ii]` on the support, `‖Y‖_k ≤ 2 y_i` (F2:
  `(pr-k)/(p-k) ≤ 2`), floor `θ = y_i √h`, `(2/√h)^{1/(k-1)} ≤ d^{1/(k-1)} ≤ e` (`h ≥ 1/d`), and
  S1.
* **TB.Dstar** (`dstar_moment`): `E D_*^n ≤ 3 (1 + d + d²) 12^n` for `1 ≤ n ≤ p/2` (T.DSTAR,
  `(1 + A + B)^n ≤ 3^n (1 + A^n + B^n)`, `y ≤ s ≤ 2` and F2 `E h^n ≤ 2^n`).
* **TB.W5** (`ward_mean_of_cl1`): `E[D_*^m (X_±²)_ii] ≤ C(m)/√h`, from TB.ward, TB.S1w with
  `Z = D_*^m`, `k = ⌈log d⌉ + 2`, and TB.Dstar.
* **TB.W1** (`weak_loop_of`, `SecB/Weak.lean`; sub-nodes in `SecB/W1.lean`): the four weak
  identities of Section 1.5 with the exact
  determinant score and remainder `B₀` (literal form of `in_W1`). Sketch (AUDIT-B §2.4): multiply
  TB.W2 by `H u_i`, sum over `i ∈ N`, apply the first-order endpoint identity (E1′) on every edge
  fibre `ij` (`E[σ_ij Ψ] = E[∂Ψ + Ψ ∂ log W] + R₁`, `∂ log W = 2pa(G⁺_ij - G⁻_ij)`); the exact
  edge derivative (W3) has leading term `-aν (X_ε)_ii (X_ν)_ii U_jj`, which produces
  `4εν H b_σᵀ K_σ f` (W4); the three secondary terms of (W3) and the mask derivative cost
  `C/(dh^{3/2})` (TB.W5, `‖F_{·i}‖ ≤ 2mh⁻¹ D_* √(r_i)`, `m = ‖f‖_∞ ≤ C D_*²/√d`); the endpoint
  remainder costs `C p/(dh)` with `ρ_row = C(δ + 1/d) ≤ C p^{-2}` from (C2) (B-3: no GR1); the
  root-weight derivatives `∂_ij H` and the determinant score are kept in the score `𝖲_f`.

**Checks.** `N = ∅` (isolated root): `u = 0`, `b = 0`, both sides of each weak identity vanish,
score `0`. Zero source `y_i = 0`: rows of `X` vanish, TB.W2 reads `0 = 0`. Numerically: (W2)
residual `6·10⁻¹⁷`, (W3) residual `4·10⁻¹¹` (AUDIT-B §6, `auditB_weak_identities.py`).
-/

@[expose] public section

namespace BiluLinial.Tight.SecB

open Matrix

universe u

section Raw

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The physical shifted inverse `X = (P^τ + zI)⁻¹` as a matrix (`shiftP`). -/
noncomputable def shiftMat (a τ z : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) :
    Matrix V V ℝ :=
  Matrix.of fun k l => shiftP G a τ z y σ S k l

/-- **TB.row.** Row `i ∈ S` of `(P̃ + zY)(P̃ + zY)⁻¹ = I`, multiplied by `√y_i √y_l`. -/
theorem shift_row_identity {a τ z : ℝ} {y : V → ℝ} {σ : Config V} {S : Finset V}
    (hy : ∀ k, 0 ≤ y k) (hQ : IsUnit (precN G a τ y σ S + z • srcDiag y S).det) {i : V}
    (hi : i ∈ S) (l : V) :
    (diagD G a y S i + z * y i) * shiftP G a τ z y σ S i l +
        τ * a * y i * ∑ k ∈ nbhd G S i, sgn σ i k * shiftP G a τ z y σ S k l =
      if i = l then y i else 0 := by
  set Q := precN G a τ y σ S + z • srcDiag y S with hQdef
  have h1 : (Q * Q⁻¹) i l = if i = l then 1 else 0 := by
    rw [Matrix.mul_nonsing_inv Q hQ, Matrix.one_apply]
  rw [Matrix.mul_apply] at h1
  have h2 := congrArg (fun t => t * (Real.sqrt (y i) * Real.sqrt (y l))) h1
  simp only [Finset.sum_mul] at h2
  have hyi : Real.sqrt (y i) * Real.sqrt (y i) = y i := Real.mul_self_sqrt (hy i)
  have hQii : Q i i = diagD G a y S i + z * y i := by
    rw [hQdef]; simp [Matrix.add_apply, srcDiag, precN, hi]
  have hQik : ∀ k, k ≠ i → Q i k =
      if k ∈ nbhd G S i then τ * a * (Real.sqrt (y i) * Real.sqrt (y k)) * sgn σ i k else 0 := by
    intro k hk
    have hk' : i ≠ k := fun h => hk h.symm
    rw [hQdef]
    simp only [Matrix.add_apply, Matrix.smul_apply, srcDiag, Matrix.diagonal_apply_ne _ hk',
      smul_eq_mul, mul_zero, add_zero, precN, Matrix.of_apply, hk', ↓reduceIte]
    by_cases hn : k ∈ nbhd G S i
    · have hn' : k ∈ S ∧ G.Adj i k := by simpa [nbhd] using hn
      simp [hi, hn'.1, hn'.2, hn]
    · have hn' : ¬ (i ∈ S ∧ k ∈ S ∧ G.Adj i k) := fun h => hn (by simp [nbhd, h.2.1, h.2.2])
      simp only [hn', hn, ↓reduceIte]
  have hs : ∀ m, shiftP G a τ z y σ S m l = Real.sqrt (y m) * Q⁻¹ m l * Real.sqrt (y l) :=
    fun m => rfl
  have hterm : ∀ k, Q i k * Q⁻¹ k l * (Real.sqrt (y i) * Real.sqrt (y l)) =
      (if k = i then (diagD G a y S i + z * y i) * shiftP G a τ z y σ S i l else 0) +
        (if k ∈ nbhd G S i then τ * a * y i * (sgn σ i k * shiftP G a τ z y σ S k l) else 0) := by
    intro k
    by_cases hk : k = i
    · rw [hk]
      have hn : i ∉ nbhd G S i := by simp [nbhd]
      simp only [hQii, hs, hn, ↓reduceIte, add_zero]
      ring
    · rw [hQik k hk]
      by_cases hn : k ∈ nbhd G S i
      · simp only [hk, hn, ↓reduceIte, zero_add, hs]
        linear_combination (τ * a * sgn σ i k * Q⁻¹ k l * Real.sqrt (y k) * Real.sqrt (y l)) * hyi
      · simp only [hk, hn, ↓reduceIte, zero_add, zero_mul]
  simp_rw [hterm] at h2
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ i, if_pos (Finset.mem_univ _),
    Finset.sum_ite_mem Finset.univ, Finset.univ_inter, ← Finset.mul_sum] at h2
  rw [h2]
  by_cases hil : i = l
  · rw [← hil]; simp only [↓reduceIte, one_mul, hyi]
  · simp only [hil, ↓reduceIte, zero_mul]

/-- **TB.W2.** For the branch-`ε` shifted inverse `X_ε`, any matrix `X_ν` and mask `f`, at
`i ∈ S`: `U_ii - f_i (X_ε)_ii (X_ν)_ii = -ε a Σ_{j∼i} σ_ij F_ji` with `U = X_ε D_f X_ν`. -/
theorem weak_w2 {a ε h : ℝ} {y : V → ℝ} {σ : Config V} {S : Finset V} (hy : ∀ k, 0 ≤ y k)
    (hQ : IsUnit (precN G a ε y σ S + h • srcDiag y S).det) {i : V} (hi : i ∈ S)
    (Xn : Matrix V V ℝ) (f : V → ℝ) :
    (shiftMat G a ε h y σ S * diagonal f * Xn) i i -
        f i * shiftMat G a ε h y σ S i i * Xn i i =
      -(ε * a) * ∑ j ∈ nbhd G S i, sgn σ i j * maskF (shiftMat G a ε h y σ S) Xn f j i := by
  set X := shiftMat G a ε h y σ S with hXdef
  have hX : ∀ k l, X k l = shiftP G a ε h y σ S k l := fun k l => rfl
  have hU : ∀ k l, (X * diagonal f * Xn) k l = ∑ m, X k m * f m * Xn m l := by
    intro k l; rw [Matrix.mul_apply]; simp only [Matrix.mul_diagonal]
  set c := diagD G a y S i + h * y i
  -- the scalar root equation and the masked equation at `(i, i)`
  have hrow : ∀ l, c * X i l + ε * a * y i * ∑ k ∈ nbhd G S i, sgn σ i k * X k l =
      if i = l then y i else 0 := fun l => shift_row_identity G hy hQ hi l
  have hmask : c * (X * diagonal f * Xn) i i +
      ε * a * y i * ∑ k ∈ nbhd G S i, sgn σ i k * (X * diagonal f * Xn) k i =
      y i * f i * Xn i i := by
    have e : c * (X * diagonal f * Xn) i i +
        ε * a * y i * ∑ k ∈ nbhd G S i, sgn σ i k * (X * diagonal f * Xn) k i =
        ∑ m, (c * X i m + ε * a * y i * ∑ k ∈ nbhd G S i, sgn σ i k * X k m) * f m * Xn m i := by
      simp only [hU, Finset.mul_sum, Finset.sum_mul, add_mul]
      rw [Finset.sum_add_distrib, Finset.sum_comm (s := nbhd G S i)]
      congr 1
      · exact Finset.sum_congr rfl fun m _ => by ring
      · exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun k _ => by ring
    rw [e]
    simp_rw [hrow]
    rw [Finset.sum_eq_single i (fun m _ hm => by simp only [Ne.symm hm, ↓reduceIte]; ring)
      (fun h => absurd (Finset.mem_univ i) h)]
    simp only [↓reduceIte]
  have hscal := hrow i
  simp only [↓reduceIte] at hscal
  -- combine
  have key : y i * ((X * diagonal f * Xn) i i - f i * X i i * Xn i i) =
      y i * (-(ε * a) * ∑ j ∈ nbhd G S i, sgn σ i j * maskF X Xn f j i) := by
    have hsum : ∑ j ∈ nbhd G S i, sgn σ i j * maskF X Xn f j i =
        X i i * ∑ j ∈ nbhd G S i, sgn σ i j * (X * diagonal f * Xn) j i -
          (X * diagonal f * Xn) i i * ∑ j ∈ nbhd G S i, sgn σ i j * X j i := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by unfold maskF; ring
    rw [hsum]
    linear_combination X i i * hmask - (X * diagonal f * Xn) i i * hscal
  rcases (hy i).lt_or_eq with hpos | hzero
  · exact mul_left_cancel₀ hpos.ne' key
  · -- zero source: the row `i` of `X` vanishes
    have hrowz : ∀ l, X i l = 0 := fun l => by
      rw [hX]; unfold shiftP; rw [← hzero, Real.sqrt_zero, zero_mul, zero_mul]
    have hUi : (X * diagonal f * Xn) i i = 0 := by
      rw [hU]; exact Finset.sum_eq_zero fun m _ => by rw [hrowz]; ring
    have hF : ∀ j, maskF X Xn f j i = 0 := fun j => by
      show X i i * (X * diagonal f * Xn) j i - X j i * (X * diagonal f * Xn) i i = 0
      rw [hrowz, hUi]; ring
    simp only [hUi, hrowz, hF, mul_zero, Finset.sum_const_zero, sub_zero, zero_mul]

/-- **TB.ward.** On the support (`P̃ ≻ 0`), for `i ∈ S` and `h > 0`:
`(X²)_ii ≤ (G_ii - X_ii)/h` (`X = (P + hI)⁻¹`, `G = P⁻¹` physical). -/
theorem ward_diag {a τ h : ℝ} {y : V → ℝ} {σ : Config V} {S : Finset V} (hy : ∀ k, 0 ≤ y k)
    (hP : (precN G a τ y σ S).PosDef) (hh : 0 < h) {i : V} (hi : i ∈ S) :
    (shiftMat G a τ h y σ S * shiftMat G a τ h y σ S) i i ≤
      (greenP G a τ y σ S i i - shiftP G a τ h y σ S i i) / h := by
  set P := precN G a τ y σ S with hPdef
  set D := srcDiag y S with hDdef
  set Q := P + h • D with hQdef
  have hD : D.PosSemidef := Matrix.PosSemidef.diagonal fun k => by
    split_ifs
    · exact hy k
    · exact le_rfl
  have hQ : Q.PosDef := hP.add_posSemidef (hD.smul hh.le)
  have hPu : IsUnit P.det := isUnit_iff_ne_zero.mpr hP.det_pos.ne'
  have hQu : IsUnit Q.det := isUnit_iff_ne_zero.mpr hQ.det_pos.ne'
  set N := P⁻¹ with hNdef
  set Nh := Q⁻¹ with hNhdef
  have hres : N - Nh = h • (N * D * Nh) := by
    have e1 : N * Q * Nh = N := by
      rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv Q hQu, Matrix.mul_one]
    have e2 : N * P * Nh = Nh := by rw [Matrix.nonsing_inv_mul P hPu, Matrix.one_mul]
    calc N - Nh = N * Q * Nh - N * P * Nh := by rw [e1, e2]
      _ = N * (Q - P) * Nh := by rw [Matrix.mul_sub, Matrix.sub_mul]
      _ = h • (N * D * Nh) := by
        rw [hQdef, add_sub_cancel_left, Matrix.mul_smul, Matrix.smul_mul]
  have hNt : Nᵀ = N := by
    have := hP.inv.1.eq; rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hNht : Nhᵀ = Nh := by
    have := hQ.inv.1.eq; rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hDt : Dᵀ = D := Matrix.diagonal_transpose _
  have hsym : N * D * Nh = Nh * D * N := by
    have t1 : (N * D * Nh)ᵀ = Nh * D * N := by
      rw [Matrix.transpose_mul, Matrix.transpose_mul, hNht, hDt, hNt, Matrix.mul_assoc]
    have t2 : (N - Nh)ᵀ = N - Nh := by rw [Matrix.transpose_sub, hNt, hNht]
    have t3 : h • (N * D * Nh) = h • (Nh * D * N) := by
      rw [← hres, ← t1, ← Matrix.transpose_smul, ← hres, t2]
    exact smul_right_injective (Matrix V V ℝ) hh.ne' t3
  have key : N * D * Nh - Nh * D * Nh = h • ((D * Nh)ᵀ * N * (D * Nh)) := by
    have e : N * D * Nh - Nh * D * Nh = (N - Nh) * (D * Nh) := by
      simp only [Matrix.sub_mul, Matrix.mul_assoc]
    rw [e, hres, Matrix.smul_mul, hsym, Matrix.transpose_mul, hNht, hDt]
  have hpsd : ((D * Nh)ᵀ * N * (D * Nh)).PosSemidef := by
    have := hP.inv.posSemidef.conjTranspose_mul_mul_same (D * Nh)
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hdiag : (Nh * D * Nh) i i ≤ (N * D * Nh) i i := by
    have h0 : 0 ≤ (h • ((D * Nh)ᵀ * N * (D * Nh))) i i := by
      rw [Matrix.smul_apply, smul_eq_mul]; exact mul_nonneg hh.le hpsd.diag_nonneg
    rw [← key, Matrix.sub_apply] at h0
    linarith
  -- rows of `Nh` vanish off `S`
  have hoff : ∀ k, k ∉ S → Nh i k = 0 := by
    intro k hk
    have hik : i ≠ k := fun h => hk (h ▸ hi)
    have hcol : ∀ m, Q m k = if m = k then 1 else 0 := by
      intro m
      by_cases hm : m = k
      · subst hm; simp [hQdef, hPdef, hDdef, precN, srcDiag, hk]
      · have hm' : ¬ (m ∈ S ∧ k ∈ S ∧ G.Adj m k) := fun h => hk h.2.1
        simp [hQdef, hPdef, hDdef, precN, srcDiag, hm, hm']
    have h1 : (Nh * Q) i k = 0 := by
      rw [Matrix.nonsing_inv_mul Q hQu, Matrix.one_apply_ne hik]
    rw [Matrix.mul_apply] at h1
    simp only [hcol, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ↓reduceIte] at h1
    exact h1
  have hXX : (shiftMat G a τ h y σ S * shiftMat G a τ h y σ S) i i = y i * (Nh * D * Nh) i i := by
    have hND : ∀ k, (Nh * D) i k = Nh i k * (if k ∈ S then y k else 0) := fun k => by
      rw [hDdef, srcDiag, Matrix.mul_diagonal]
    rw [Matrix.mul_apply, Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hND]
    show Real.sqrt (y i) * Nh i k * Real.sqrt (y k) * (Real.sqrt (y k) * Nh k i * Real.sqrt (y i))
      = y i * (Nh i k * (if k ∈ S then y k else 0) * Nh k i)
    by_cases hk : k ∈ S
    · simp only [hk, ↓reduceIte]
      have h1 := Real.mul_self_sqrt (hy i)
      have h2 := Real.mul_self_sqrt (hy k)
      linear_combination (Nh i k * Nh k i * Real.sqrt (y k) * Real.sqrt (y k)) * h1 +
        (y i * Nh i k * Nh k i) * h2
    · simp only [hk, ↓reduceIte, hoff k hk]
      ring
  have hGX : greenP G a τ y σ S i i - shiftP G a τ h y σ S i i = y i * (h * (N * D * Nh) i i) := by
    rw [greenP_diag G σ S (hy i), shiftP_diag G σ S (hy i)]
    have : hN G a τ y σ S i - hzN G a τ h y σ S i = (N - Nh) i i := by
      rw [Matrix.sub_apply]; rfl
    rw [← mul_sub, this, hres, Matrix.smul_apply, smul_eq_mul]
  rw [hXX, hGX, mul_comm h, ← mul_assoc, mul_div_assoc, div_self hh.ne', mul_one]
  exact mul_le_mul_of_nonneg_left hdiag (hy i)

end Raw

/-- **TB.S1w, one branch** (pointwise). If the precision of the branch is positive definite on
the support, `E h_i^k ≤ 2^k`, `E(G_ii - X_ii) ≤ A √h y_i`, `(2/√h)^{1/(k-1)} ≤ L` and
`E Z^k ≤ B^k`, then `E[(G_ii - X_ii) Z] ≤ L (A + 1) B √h y_i` (UMI with floor `θ = y_i √h`). -/
theorem s1w_branch {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {p : ℕ} {a τ h : ℝ} {yp ym y : V → ℝ} {S : Finset V}
    (hy : ∀ k, 0 ≤ y k) (hpd : ∀ σ, wt G p a yp ym σ S ≠ 0 → (precN G a τ y σ S).PosDef)
    (hZw : 0 < Zw G p a yp ym S) (h0 : 0 < h) {i : V} {k : ℕ} (hk : 2 ≤ k)
    (hmom : lawE G p a yp ym S (fun σ => hN G a τ y σ S i ^ k) ≤ 2 ^ k) {A L : ℝ}
    (hmean : lawE G p a yp ym S (fun σ => greenP G a τ y σ S i i) -
        lawE G p a yp ym S (fun σ => shiftP G a τ h y σ S i i) ≤ A * Real.sqrt h * y i)
    (hL : (2 / Real.sqrt h) ^ (1 / ((k : ℝ) - 1)) ≤ L)
    (Z : Config V → ℝ) (hZ : ∀ σ, 0 ≤ Z σ) {B : ℝ} (hB : 0 ≤ B)
    (hZk : lawE G p a yp ym S (fun σ => Z σ ^ k) ≤ B ^ k) :
    lawE G p a yp ym S (fun σ => (greenP G a τ y σ S i i - shiftP G a τ h y σ S i i) * Z σ) ≤
      L * (A + 1) * B * Real.sqrt h * y i := by
  have hdiff : ∀ σ, wt G p a yp ym σ S ≠ 0 →
      0 ≤ greenP G a τ y σ S i i - shiftP G a τ h y σ S i i ∧
        greenP G a τ y σ S i i - shiftP G a τ h y σ S i i ≤ y i * hN G a τ y σ S i := by
    intro σ hσ
    have hle := hzN_le_hN G (hpd σ hσ) h0.le hy i
    have hnn := (diag_nonneg_of_posDef G (hpd σ hσ) hy h0.le i).2
    rw [shiftP_diag G σ S (hy i)] at hnn
    rw [greenP_diag G σ S (hy i), shiftP_diag G σ S (hy i)]
    exact ⟨by nlinarith [hy i], by linarith⟩
  set Y : Config V → ℝ := fun σ =>
    if wt G p a yp ym σ S ≠ 0 then greenP G a τ y σ S i i - shiftP G a τ h y σ S i i else 0
    with hYdef
  have hY0 : ∀ σ, 0 ≤ Y σ := fun σ => by
    simp only [hYdef]
    split_ifs with hσ
    · exact (hdiff σ hσ).1
    · exact le_rfl
  have hYeq : ∀ σ, wt G p a yp ym σ S ≠ 0 →
      Y σ = greenP G a τ y σ S i i - shiftP G a τ h y σ S i i := fun σ hσ => by
    simp only [hYdef, hσ, ne_eq, not_false_eq_true, ↓reduceIte]
  rcases (hy i).lt_or_eq with hyi | hyi
  · have hsq : 0 < Real.sqrt h := Real.sqrt_pos.2 h0
    have hθ : 0 < y i * Real.sqrt h := mul_pos hyi hsq
    have hYk : wavg (fun σ => wt G p a yp ym σ S) (fun σ => Y σ ^ k) ≤ (2 * y i) ^ k := by
      rw [← lawE_eq_wavg]
      calc lawE G p a yp ym S (fun σ => Y σ ^ k)
          ≤ lawE G p a yp ym S (fun σ => y i ^ k * hN G a τ y σ S i ^ k) :=
            lawE_mono G fun σ hσ => by
              rw [hYeq σ hσ, ← mul_pow]
              exact pow_le_pow_left₀ (hdiff σ hσ).1 (hdiff σ hσ).2 k
        _ = y i ^ k * lawE G p a yp ym S (fun σ => hN G a τ y σ S i ^ k) :=
            lawE_const_mul G _ _
        _ ≤ y i ^ k * 2 ^ k := mul_le_mul_of_nonneg_left hmom (pow_nonneg (hy i) k)
        _ = (2 * y i) ^ k := by ring
    have hEY : wavg (fun σ => wt G p a yp ym σ S) Y =
        lawE G p a yp ym S (fun σ => greenP G a τ y σ S i i) -
          lawE G p a yp ym S (fun σ => shiftP G a τ h y σ S i i) := by
      rw [← lawE_eq_wavg, ← lawE_sub]
      exact lawE_congr G hYeq
    have humi := wavg_mul_le_umi (fun σ => wt_nonneg G σ) hZw hY0 hZ hk
      (by positivity : (0 : ℝ) ≤ 2 * y i) hB hθ hYk (by rwa [← lawE_eq_wavg])
    have hratio : 2 * y i / (y i * Real.sqrt h) = 2 / Real.sqrt h := by
      field_simp
    rw [hratio, hEY] at humi
    have hLHS : lawE G p a yp ym S
        (fun σ => (greenP G a τ y σ S i i - shiftP G a τ h y σ S i i) * Z σ) =
        wavg (fun σ => wt G p a yp ym σ S) (fun σ => Y σ * Z σ) := by
      rw [← lawE_eq_wavg]
      exact lawE_congr G fun σ hσ => by rw [hYeq σ hσ]
    rw [hLHS]
    refine le_trans humi ?_
    have hX0 : 0 ≤ (2 / Real.sqrt h) ^ (1 / ((k : ℝ) - 1)) := Real.rpow_nonneg (by positivity) _
    have hEY0 : 0 ≤ lawE G p a yp ym S (fun σ => greenP G a τ y σ S i i) -
        lawE G p a yp ym S (fun σ => shiftP G a τ h y σ S i i) := by
      rw [← hEY]; exact wavg_nonneg (fun σ => wt_nonneg G σ) hY0
    calc B * (2 / Real.sqrt h) ^ (1 / ((k : ℝ) - 1)) *
          (lawE G p a yp ym S (fun σ => greenP G a τ y σ S i i) -
            lawE G p a yp ym S (fun σ => shiftP G a τ h y σ S i i) + y i * Real.sqrt h)
        ≤ B * L * ((A + 1) * Real.sqrt h * y i) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hL hB) (by linarith) (by positivity)
            (mul_nonneg hB (hX0.trans hL))
      _ = L * (A + 1) * B * Real.sqrt h * y i := by ring
  · have h0E : lawE G p a yp ym S
        (fun σ => (greenP G a τ y σ S i i - shiftP G a τ h y σ S i i) * Z σ) = 0 := by
      rw [← lawE_zero G (p := p) (a := a) (yp := yp) (ym := ym) (S := S)]
      exact lawE_congr G fun σ _ => by
        rw [greenP_diag G σ S (hy i), shiftP_diag G σ S (hy i), ← hyi]; ring
    rw [h0E, ← hyi, mul_zero]

/-- **TB.S1w** (weighted mean shift). Given (CL1): for every capped point, `i ∈ S`, moment order
`log d + 2 ≤ k ≤ p/2` and `Z ≥ 0` with `E Z^k ≤ B^k`:
`E[(G^±_ii - X^±_ii) Z] ≤ 3 (K_S + 2) B √h y^±_i`. -/
theorem mean_shift_weighted_of_cl1 {K Kb c : ℝ} (hK : 0 ≤ K) (hKb : 0 ≤ Kb) (hc : 0 < c)
    (hCL : CL1Shape.{u} K Kb c) :
    Eventually fun _ _ d p h => ∀ cp : CapPoint.{u} d p, ∀ i ∈ cp.S, ∀ k : ℕ,
      Real.log d + 2 ≤ k → 2 * k ≤ p → ∀ Z : Config cp.V → ℝ, (∀ σ, 0 ≤ Z σ) →
      ∀ B : ℝ, 0 ≤ B → cp.E (fun σ => Z σ ^ k) ≤ B ^ k →
        cp.E (fun σ => (cp.gp σ i i - shiftP cp.G (aOf d p) 1 h cp.yp σ cp.S i i) * Z σ) ≤
            3 * (s1K K + 2) * B * Real.sqrt h * cp.yp i ∧
        cp.E (fun σ => (cp.gm σ i i - shiftP cp.G (aOf d p) (-1) h cp.ym σ cp.S i i) * Z σ) ≤
            3 * (s1K K + 2) * B * Real.sqrt h * cp.ym i := by
  refine ((mean_shift_of_cl1 hK hKb hc hCL).and eventually_h_facts).mono ?_
  rintro c₀ κ₀ d p h ⟨hS1, hR, h0, h1d, -, -⟩ cp i hi k hk1 hk2 Z hZ B hB hZk
  obtain ⟨-, hS⟩ := hS1 cp
  obtain ⟨⟨-, a2⟩, ⟨-, b2⟩⟩ := hS i hi
  have hs := hR.sOf_pos
  have hsub : ∀ y : cp.V → ℝ, InCube (cp.lam * sOf d p) y → InCube (sOf d p) y := fun y hy k =>
    ⟨(hy k).1, le_trans (hy k).2 (by nlinarith [cp.ctx.lam_le_one, cp.ctx.lam_nonneg])⟩
  have hZw : 0 < Zw cp.G p (aOf d p) cp.yp cp.ym cp.S :=
    cp.ctx.pos cp.yp cp.ym (hsub _ cp.hyp) (hsub _ cp.hym)
  have hd4 : (4 : ℝ) ≤ d := by have := hR.ten_pow_six_le_d; linarith
  have hlogd : 0 ≤ Real.log d := Real.log_nonneg (by linarith)
  have hk2' : 2 ≤ k := by
    have : (2 : ℝ) ≤ k := by linarith
    exact_mod_cast this
  -- the interpolation loss
  have hsq : 0 < Real.sqrt h := Real.sqrt_pos.2 h0
  have h2d : 2 / Real.sqrt h ≤ d := by
    rw [div_le_iff₀ hsq]
    have hdh : 1 ≤ (d : ℝ) * h := by
      rw [div_le_iff₀ (by linarith)] at h1d; linarith
    have hx2 : ((d : ℝ) * Real.sqrt h) ^ 2 ≥ 4 := by
      rw [mul_pow, Real.sq_sqrt h0.le]; nlinarith
    have hx0 : 0 ≤ (d : ℝ) * Real.sqrt h := by positivity
    nlinarith
  have hkpos : 0 < (k : ℝ) - 1 := by linarith
  have hL : (2 / Real.sqrt h) ^ (1 / ((k : ℝ) - 1)) ≤ 3 := by
    calc (2 / Real.sqrt h) ^ (1 / ((k : ℝ) - 1)) ≤ (d : ℝ) ^ (1 / ((k : ℝ) - 1)) :=
          Real.rpow_le_rpow (by positivity) h2d (by positivity)
      _ = Real.exp (Real.log d * (1 / ((k : ℝ) - 1))) := Real.rpow_def_of_pos (by linarith) _
      _ ≤ Real.exp 1 := Real.exp_le_exp.mpr (by
          rw [mul_one_div, div_le_one hkpos]; linarith)
      _ ≤ 3 := by have := Real.exp_one_lt_d9; linarith
  -- F2: `E h_i^k ≤ 2^k`
  have hkp : (2 : ℝ) * k ≤ p := by exact_mod_cast hk2
  have hr := hR.rOf_le
  have hr1 := hR.one_lt_rOf
  have hk0 : (0 : ℝ) < k := by linarith
  have hpk : 0 < (p : ℝ) - k := by linarith
  have hb2 : ((p : ℝ) * rOf d p - k) / ((p : ℝ) - k) ≤ 2 := by
    rw [div_le_iff₀ hpk]
    nlinarith [mul_le_mul_of_nonneg_left hr (by positivity : (0 : ℝ) ≤ p)]
  have hb0 : 0 ≤ ((p : ℝ) * rOf d p - k) / ((p : ℝ) - k) :=
    div_nonneg (by nlinarith [mul_le_mul_of_nonneg_left hr1.le (by positivity : (0 : ℝ) ≤ p)])
      hpk.le
  have hF2 := source_moments cp.G hR cp.ctx cp.hyp cp.hym hi (k := k) (by omega) (by omega)
  have hmP := hF2.1.trans (pow_le_pow_left₀ hb0 hb2 k)
  have hmM := hF2.2.trans (pow_le_pow_left₀ hb0 hb2 k)
  have hyp : ∀ j, 0 ≤ cp.yp j := fun j => (cp.hyp j).1
  have hym : ∀ j, 0 ≤ cp.ym j := fun j => (cp.hym j).1
  constructor
  · calc _ ≤ 3 * (s1K K + 1 + 1) * B * Real.sqrt h * cp.yp i :=
          s1w_branch cp.G hyp (fun σ hσ => (posDef_of_wt_ne_zero cp.G hσ).1) hZw h0 hk2' hmP a2
            hL Z hZ hB hZk
      _ = _ := by ring
  · calc _ ≤ 3 * (s1K K + 1 + 1) * B * Real.sqrt h * cp.ym i :=
          s1w_branch cp.G hym (fun σ hσ => (posDef_of_wt_ne_zero cp.G hσ).2) hZw h0 hk2' hmM b2
            hL Z hZ hB hZk
      _ = _ := by ring

/-- F2 in the form `E h^k ≤ 2^k`: for `1 ≤ k ≤ p/2`, `0 ≤ (pr - k)/(p - k) ≤ 2`. -/
theorem f2_base_le_two {d p : ℕ} (hR : TRegime d p) {k : ℕ} (hk1 : 1 ≤ k) (hk2 : 2 * k ≤ p) :
    0 ≤ ((p : ℝ) * rOf d p - k) / ((p : ℝ) - k) ∧
      ((p : ℝ) * rOf d p - k) / ((p : ℝ) - k) ≤ 2 := by
  have hkp : (2 : ℝ) * k ≤ p := by exact_mod_cast hk2
  have hk0 : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hr := hR.rOf_le
  have hr1 := hR.one_lt_rOf
  have hpk : 0 < (p : ℝ) - k := by linarith
  constructor
  · exact div_nonneg (by nlinarith [mul_le_mul_of_nonneg_left hr1.le (by positivity :
      (0 : ℝ) ≤ p)]) hpk.le
  · rw [div_le_iff₀ hpk]
    nlinarith [mul_le_mul_of_nonneg_left hr (by positivity : (0 : ℝ) ≤ p)]

/-- `(1 + A + B)^n ≤ 3^n (1 + A^n + B^n)` for `A, B ≥ 0`. -/
theorem one_add_add_pow_le {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (n : ℕ) :
    (1 + A + B) ^ n ≤ 3 ^ n * (1 + A ^ n + B ^ n) := by
  have hM : 1 + A + B ≤ 3 * max 1 (max A B) := by
    have := le_max_left 1 (max A B); have := le_max_left A B
    have := le_max_right A B; have := le_max_right 1 (max A B); linarith
  have hMn : max 1 (max A B) ^ n ≤ 1 + A ^ n + B ^ n := by
    have hAn := pow_nonneg hA n
    have hBn := pow_nonneg hB n
    rcases le_total 1 (max A B) with h | h
    · rw [max_eq_right h]
      rcases le_total A B with h' | h'
      · rw [max_eq_right h']; linarith
      · rw [max_eq_left h']; linarith
    · rw [max_eq_left h, one_pow]; linarith
  calc (1 + A + B) ^ n ≤ (3 * max 1 (max A B)) ^ n := pow_le_pow_left₀ (by positivity) hM n
    _ = 3 ^ n * max 1 (max A B) ^ n := mul_pow _ _ _
    _ ≤ 3 ^ n * (1 + A ^ n + B ^ n) := mul_le_mul_of_nonneg_left hMn (by positivity)

/-- The radius-two ball `N ∪ N(N) ∪ {v}` of a contact lies in `S` and has at most `1 + d + d²`
elements. -/
theorem ball_sub_card {d p : ℕ} (ct : Contact.{u} d p) :
    insert ct.v (ct.N ∪ ct.N.biUnion (nbhd ct.G ct.S)) ⊆ ct.S ∧
      ((insert ct.v (ct.N ∪ ct.N.biUnion (nbhd ct.G ct.S))).card : ℝ) ≤ 1 + d + (d : ℝ) ^ 2 := by
  have hnb : ∀ w, nbhd ct.G ct.S w ⊆ ct.S := fun w => Finset.filter_subset _ _
  have hcard : ∀ w, (nbhd ct.G ct.S w).card ≤ d := fun w => by
    have h1 : nbhd ct.G ct.S w ⊆ ct.G.neighborFinset w := fun i hi => by
      simp only [nbhd, Finset.mem_filter] at hi
      simpa using hi.2
    have h2 := Finset.card_le_card h1
    rw [SimpleGraph.card_neighborFinset_eq_degree] at h2
    exact h2.trans (ct.ctx.deg w)
  refine ⟨Finset.insert_subset ct.ctx.mem (Finset.union_subset (hnb _)
    (Finset.biUnion_subset.mpr fun w _ => hnb w)), ?_⟩
  have h1 := Finset.card_insert_le ct.v (ct.N ∪ ct.N.biUnion (nbhd ct.G ct.S))
  have h2 := Finset.card_union_le ct.N (ct.N.biUnion (nbhd ct.G ct.S))
  have h3 : (ct.N.biUnion (nbhd ct.G ct.S)).card ≤ d * d := by
    refine Finset.card_biUnion_le.trans ?_
    calc ∑ w ∈ ct.N, (nbhd ct.G ct.S w).card ≤ ∑ _w ∈ ct.N, d :=
          Finset.sum_le_sum fun w _ => hcard w
      _ = ct.N.card * d := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ d * d := Nat.mul_le_mul_right _ (hcard ct.v)
  have : (insert ct.v (ct.N ∪ ct.N.biUnion (nbhd ct.G ct.S))).card ≤ 1 + d + d * d := by
    have := hcard ct.v
    unfold Contact.N at h1 h2 h3 ⊢
    omega
  have : ((insert ct.v (ct.N ∪ ct.N.biUnion (nbhd ct.G ct.S))).card : ℝ) ≤ 1 + d + d * d := by
    exact_mod_cast this
  nlinarith

/-- **TB.Dstar.** Moments of `D_*`: `E D_*^n ≤ 3 (1 + d + d²) 12^n` for `1 ≤ n ≤ p/2`
(T.DSTAR over the radius-two ball, `|B₂(v)| ≤ 1 + d + d²`, and F2 for each diagonal). -/
theorem dstar_moment : Eventually fun _ _ d p _ => ∀ ct : Contact.{u} d p, ∀ n : ℕ,
    1 ≤ n → 2 * n ≤ p →
      ct.E (fun σ => ct.Dstar σ ^ n) ≤ 3 * (1 + d + (d : ℝ) ^ 2) * 12 ^ n := by
  refine (eventually_base 0).mono ?_
  rintro c₀ κ₀ d p h ⟨hR, -⟩ ct n hn1 hn2
  obtain ⟨hsubS, hcardB⟩ := ball_sub_card ct
  have hBne : (insert ct.v (ct.N ∪ ct.N.biUnion (nbhd ct.G ct.S))).Nonempty :=
    Finset.insert_nonempty _ _
  have hs := hR.sOf_pos
  have hs2 := SecA.sOf_le_two hR
  have hsub : ∀ y : ct.V → ℝ, InCube (ct.lam * sOf d p) y → InCube (sOf d p) y := fun y hy k =>
    ⟨(hy k).1, le_trans (hy k).2 (by nlinarith [ct.ctx.lam_le_one, ct.ctx.lam_nonneg])⟩
  have hZw : 0 < Zw ct.G p (aOf d p) ct.yp ct.ym ct.S :=
    ct.ctx.pos ct.yp ct.ym (hsub _ ct.ctx.hyp) (hsub _ ct.ctx.hym)
  have hyp : ∀ j, 0 ≤ ct.yp j ∧ ct.yp j ≤ 2 := fun j =>
    ⟨((hsub _ ct.ctx.hyp) j).1, ((hsub _ ct.ctx.hyp) j).2.trans hs2⟩
  have hym : ∀ j, 0 ≤ ct.ym j ∧ ct.ym j ≤ 2 := fun j =>
    ⟨((hsub _ ct.ctx.hym) j).1, ((hsub _ ct.ctx.hym) j).2.trans hs2⟩
  set X : ct.V → Config ct.V → ℝ := fun w σ => 1 + max (ct.gp σ w w) 0 + max (ct.gm σ w w) 0
    with hXdef
  have hX0 : ∀ w σ, 0 ≤ X w σ := fun w σ => by
    have := le_max_right (ct.gp σ w w) 0; have := le_max_right (ct.gm σ w w) 0
    simp only [hXdef]; linarith
  -- pointwise domination on the support
  have hpt : ∀ σ, wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 →
      ct.Dstar σ ^ n ≤ ((insert ct.v (ct.N ∪ ct.N.biUnion (nbhd ct.G ct.S))).sup' hBne
        fun w => X w σ) ^ n := by
    intro σ hσ
    obtain ⟨hpP, -⟩ := posDef_of_wt_ne_zero ct.G hσ
    obtain ⟨w, hw, hmax⟩ := (insert ct.v (ct.N ∪ ct.N.biUnion (nbhd ct.G ct.S))).exists_mem_eq_sup'
      hBne (fun w => max (ct.gp σ w w) (ct.gm σ w w))
    have hD : ct.Dstar σ = 1 + max (ct.gp σ w w) (ct.gm σ w w) := by
      unfold Contact.Dstar; rw [hmax]
    have hv := (insert ct.v (ct.N ∪ ct.N.biUnion (nbhd ct.G ct.S))).le_sup' (fun w =>
      max (ct.gp σ w w) (ct.gm σ w w)) (Finset.mem_insert_self ct.v _)
    have hgv : 0 ≤ ct.gp σ ct.v ct.v :=
      (diag_nonneg_of_posDef ct.G hpP (fun j => (hyp j).1) (le_refl (0 : ℝ)) ct.v).1
    have hD0 : 0 ≤ ct.Dstar σ := by
      unfold Contact.Dstar
      have := le_max_left (ct.gp σ ct.v ct.v) (ct.gm σ ct.v ct.v)
      linarith
    apply pow_le_pow_left₀ hD0
    rw [hD]
    refine le_trans ?_ ((insert ct.v (ct.N ∪ ct.N.biUnion (nbhd ct.G ct.S))).le_sup'
      (fun w => X w σ) hw)
    simp only [hXdef]
    have := le_max_left (ct.gp σ w w) 0; have := le_max_left (ct.gm σ w w) 0
    have := le_max_right (ct.gp σ w w) 0; have := le_max_right (ct.gm σ w w) 0
    have : max (ct.gp σ w w) (ct.gm σ w w) ≤ max (ct.gp σ w w) 0 + max (ct.gm σ w w) 0 :=
      max_le (by linarith) (by linarith)
    linarith
  -- moments of each `X_w`
  obtain ⟨hb0, hb2⟩ := f2_base_le_two hR hn1 hn2
  have hn2' : n + 2 ≤ p := by have := hR.hp; omega
  have hXmom : ∀ w ∈ insert ct.v (ct.N ∪ ct.N.biUnion (nbhd ct.G ct.S)),
      wavg (fun σ => wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S) (fun σ => X w σ ^ n) ≤
        3 * 12 ^ n := by
    intro w hw
    have hwS := hsubS hw
    have hF2 := source_moments ct.G hR ct.ctx.toCapCtx ct.ctx.hyp ct.ctx.hym hwS (k := n) hn1 hn2'
    have hmP := hF2.1.trans (pow_le_pow_left₀ hb0 hb2 n)
    have hmM := hF2.2.trans (pow_le_pow_left₀ hb0 hb2 n)
    rw [← lawE_eq_wavg]
    calc lawE ct.G p (aOf d p) ct.yp ct.ym ct.S (fun σ => X w σ ^ n)
        ≤ lawE ct.G p (aOf d p) ct.yp ct.ym ct.S (fun σ => 3 ^ n * (1 +
            2 ^ n * hN ct.G (aOf d p) 1 ct.yp σ ct.S w ^ n +
            2 ^ n * hN ct.G (aOf d p) (-1) ct.ym σ ct.S w ^ n)) := lawE_mono ct.G fun σ hσ => by
          obtain ⟨hpP, hpM⟩ := posDef_of_wt_ne_zero ct.G hσ
          have gP : 0 ≤ ct.gp σ w w :=
            (diag_nonneg_of_posDef ct.G hpP (fun j => (hyp j).1) (le_refl (0 : ℝ)) w).1
          have gM : 0 ≤ ct.gm σ w w :=
            (diag_nonneg_of_posDef ct.G hpM (fun j => (hym j).1) (le_refl (0 : ℝ)) w).1
          have eP : ct.gp σ w w = ct.yp w * hN ct.G (aOf d p) 1 ct.yp σ ct.S w :=
            greenP_diag ct.G σ ct.S (hyp w).1
          have eM : ct.gm σ w w = ct.ym w * hN ct.G (aOf d p) (-1) ct.ym σ ct.S w :=
            greenP_diag ct.G σ ct.S (hym w).1
          have hhP : 0 ≤ hN ct.G (aOf d p) 1 ct.yp σ ct.S w := hpP.inv.posSemidef.diag_nonneg
          have hhM : 0 ≤ hN ct.G (aOf d p) (-1) ct.ym σ ct.S w := hpM.inv.posSemidef.diag_nonneg
          simp only [hXdef, max_eq_left gP, max_eq_left gM]
          refine le_trans (one_add_add_pow_le gP gM n)
            (mul_le_mul_of_nonneg_left ?_ (by positivity))
          have aP : ct.gp σ w w ^ n ≤ 2 ^ n * hN ct.G (aOf d p) 1 ct.yp σ ct.S w ^ n := by
            rw [eP, mul_pow]
            exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hyp w).1 (hyp w).2 n)
              (pow_nonneg hhP n)
          have aM : ct.gm σ w w ^ n ≤ 2 ^ n * hN ct.G (aOf d p) (-1) ct.ym σ ct.S w ^ n := by
            rw [eM, mul_pow]
            exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hym w).1 (hym w).2 n)
              (pow_nonneg hhM n)
          linarith
      _ = 3 ^ n * (1 + 2 ^ n * lawE ct.G p (aOf d p) ct.yp ct.ym ct.S
            (fun σ => hN ct.G (aOf d p) 1 ct.yp σ ct.S w ^ n) +
            2 ^ n * lawE ct.G p (aOf d p) ct.yp ct.ym ct.S
            (fun σ => hN ct.G (aOf d p) (-1) ct.ym σ ct.S w ^ n)) := by
          rw [lawE_const_mul, lawE_add, lawE_add, lawE_const_mul, lawE_const_mul,
            lawE_const ct.G hZw.ne']
      _ ≤ 3 ^ n * (1 + 2 ^ n * 2 ^ n + 2 ^ n * 2 ^ n) := by
          gcongr
      _ ≤ 3 * 12 ^ n := by
          have h4 : (1 : ℝ) ≤ 4 ^ n := one_le_pow₀ (by norm_num)
          have e : (3 : ℝ) ^ n * (1 + 2 ^ n * 2 ^ n + 2 ^ n * 2 ^ n) =
              3 ^ n * (1 + 2 * 4 ^ n) := by
            rw [← mul_pow]; norm_num; ring
          rw [e, show (12 : ℝ) ^ n = 3 ^ n * 4 ^ n by rw [← mul_pow]; norm_num]
          nlinarith [pow_pos (by norm_num : (0 : ℝ) < 3) n]
  have hsup := wavg_sup_pow_le (fun σ => wt_nonneg ct.G σ) hZw _ hBne X hX0 n hXmom
  rw [← lawE_eq_wavg] at hsup
  calc ct.E (fun σ => ct.Dstar σ ^ n)
      ≤ lawE ct.G p (aOf d p) ct.yp ct.ym ct.S (fun σ =>
          ((insert ct.v (ct.N ∪ ct.N.biUnion (nbhd ct.G ct.S))).sup' hBne fun w => X w σ) ^ n) :=
        lawE_mono ct.G hpt
    _ ≤ _ := hsup
    _ ≤ (1 + d + (d : ℝ) ^ 2) * (3 * 12 ^ n) :=
        mul_le_mul_of_nonneg_right hcardB (by positivity)
    _ = 3 * (1 + d + (d : ℝ) ^ 2) * 12 ^ n := by ring

/-- Eventually `A (log d + 3) ≤ p` (since `log d ≤ 17 d^{1/17}` and `p ≥ c₀ d^{2/17}/2`). -/
theorem eventually_log_le_p (A : ℝ) : Eventually fun _ _ d p _ => A * (Real.log d + 3) ≤ p := by
  intro c₀ κ₀ hc0 hc1 hk0 hk1
  obtain ⟨D₁, hD₁⟩ := exists_tRegime_pAt hc0 hc1
  have ht : Filter.Tendsto (fun d : ℕ => (d : ℝ) ^ ((1 : ℝ) / 17)) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  obtain ⟨D₂, hD₂⟩ :=
    Filter.eventually_atTop.mp (ht.eventually_ge_atTop ((40 * |A| + 2) / c₀ + 1))
  refine ⟨max D₁ (max D₂ 1), fun d hd => ?_⟩
  obtain ⟨-, hb⟩ := hD₁ d (le_of_max_le_left hd)
  have hp := half_base_le_pAt hb
  have htT := hD₂ d (le_trans (le_max_left _ _) (le_of_max_le_right hd))
  have hd1 : (1 : ℝ) ≤ d := by
    exact_mod_cast (le_trans (le_max_right _ _) (le_of_max_le_right hd))
  have hd0 : (0 : ℝ) < d := by linarith
  obtain ⟨t, ht_def⟩ : ∃ t, t = (d : ℝ) ^ ((1 : ℝ) / 17) := ⟨_, rfl⟩
  rw [← ht_def] at htT
  have hT0 : 0 ≤ (40 * |A| + 2) / c₀ := by positivity
  have ht1 : 1 ≤ t := by linarith
  have ht2 : (d : ℝ) ^ ((2 : ℝ) / 17) = t ^ 2 := by
    rw [ht_def, ← Real.rpow_natCast, ← Real.rpow_mul hd0.le]; norm_num
  have hlog : Real.log d = 17 * Real.log t := by
    rw [ht_def, Real.log_rpow hd0]; ring
  have hlogt : Real.log t ≤ t - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have hl0 : 0 ≤ Real.log d + 3 := by have := Real.log_nonneg hd1; linarith
  have h1 : A * (Real.log d + 3) ≤ |A| * (17 * t + 3) :=
    calc A * (Real.log d + 3) ≤ |A| * (Real.log d + 3) :=
          mul_le_mul_of_nonneg_right (le_abs_self A) hl0
      _ ≤ |A| * (17 * t + 3) :=
          mul_le_mul_of_nonneg_left (by rw [hlog]; linarith) (abs_nonneg A)
  have hT : 40 * |A| + 2 ≤ t * c₀ := by
    have : (40 * |A| + 2) / c₀ ≤ t := by linarith
    rwa [div_le_iff₀ hc0] at this
  have h2 : |A| * (17 * t + 3) ≤ c₀ * t ^ 2 / 2 := by
    have := mul_le_mul_of_nonneg_left hT (by linarith : (0 : ℝ) ≤ t)
    nlinarith [abs_nonneg A]
  rw [ht2] at hp
  linarith

/-- `D_* ≥ 0` on the support. -/
theorem dstar_nonneg {d p : ℕ} (ct : Contact.{u} d p) {σ : Config ct.V}
    (hσ : wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0) : 0 ≤ ct.Dstar σ := by
  obtain ⟨hpP, -⟩ := posDef_of_wt_ne_zero ct.G hσ
  have hv := (insert ct.v (ct.N ∪ ct.N.biUnion (nbhd ct.G ct.S))).le_sup' (fun w =>
    max (ct.gp σ w w) (ct.gm σ w w)) (Finset.mem_insert_self ct.v _)
  have hgv : 0 ≤ ct.gp σ ct.v ct.v :=
    (diag_nonneg_of_posDef ct.G hpP (fun j => (ct.ctx.hyp j).1) (le_refl (0 : ℝ)) ct.v).1
  unfold Contact.Dstar
  have := le_max_left (ct.gp σ ct.v ct.v) (ct.gm σ ct.v ct.v)
  linarith

/-- **TB.W5, one branch.** If `Z ≥ 0` equals `D_*^m` on the support and
`E[(G_ii - X_ii) Z] ≤ R`, then `E[D_*^m (X²)_ii] ≤ R/h` (TB.ward). -/
theorem w5_branch {d p : ℕ} (ct : Contact.{u} d p) {τ h : ℝ} {y : ct.V → ℝ}
    (hy : ∀ k, 0 ≤ y k)
    (hpd : ∀ σ, wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 →
      (precN ct.G (aOf d p) τ y σ ct.S).PosDef) (hh : 0 < h) {i : ct.V} (hi : i ∈ ct.S) (m : ℕ)
    (Z : Config ct.V → ℝ) (hZ0 : ∀ σ, 0 ≤ Z σ)
    (hZeq : ∀ σ, wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 → Z σ = ct.Dstar σ ^ m) {R : ℝ}
    (hE : ct.E (fun σ => (greenP ct.G (aOf d p) τ y σ ct.S i i -
      shiftP ct.G (aOf d p) τ h y σ ct.S i i) * Z σ) ≤ R) :
    ct.E (fun σ => ct.Dstar σ ^ m *
      (shiftMat ct.G (aOf d p) τ h y σ ct.S * shiftMat ct.G (aOf d p) τ h y σ ct.S) i i) ≤
      R / h := by
  calc ct.E (fun σ => ct.Dstar σ ^ m *
        (shiftMat ct.G (aOf d p) τ h y σ ct.S * shiftMat ct.G (aOf d p) τ h y σ ct.S) i i)
      ≤ ct.E (fun σ => 1 / h * ((greenP ct.G (aOf d p) τ y σ ct.S i i -
          shiftP ct.G (aOf d p) τ h y σ ct.S i i) * Z σ)) := lawE_mono ct.G fun σ hσ => by
        rw [← hZeq σ hσ]
        have hw := ward_diag ct.G hy (hpd σ hσ) hh hi
        calc Z σ * (shiftMat ct.G (aOf d p) τ h y σ ct.S *
              shiftMat ct.G (aOf d p) τ h y σ ct.S) i i
            ≤ Z σ * ((greenP ct.G (aOf d p) τ y σ ct.S i i -
                shiftP ct.G (aOf d p) τ h y σ ct.S i i) / h) :=
              mul_le_mul_of_nonneg_left hw (hZ0 σ)
          _ = _ := by ring
    _ = 1 / h * ct.E (fun σ => (greenP ct.G (aOf d p) τ y σ ct.S i i -
          shiftP ct.G (aOf d p) τ h y σ ct.S i i) * Z σ) := lawE_const_mul ct.G _ _
    _ ≤ 1 / h * R := mul_le_mul_of_nonneg_left hE (by positivity)
    _ = R / h := by ring

/-- **TB.W5** (mean Ward bound), the literal form of `in_W5 m`, given (CL1), with
`C = 126 (K_S + 2) 12^m`. -/
theorem ward_mean_of_cl1 (m : ℕ) {K Kb c : ℝ} (hK : 0 ≤ K) (hKb : 0 ≤ Kb) (hc : 0 < c)
    (hCL : CL1Shape.{u} K Kb c) :
    ∃ C : ℝ, 0 < C ∧ Eventually fun _c₀ _κ₀ d p h =>
      ∀ ct : Contact.{u} d p, ∀ i ∈ ct.S,
        ct.E (fun σ => ct.Dstar σ ^ m * (ct.XP h σ * ct.XP h σ) i i) ≤ C / Real.sqrt h ∧
        ct.E (fun σ => ct.Dstar σ ^ m * (ct.XM h σ * ct.XM h σ) i i) ≤ C / Real.sqrt h := by
  have hKS := one_le_s1K hK
  refine ⟨126 * (s1K K + 2) * 12 ^ m, by positivity, ?_⟩
  refine ((((mean_shift_weighted_of_cl1 hK hKb hc hCL).and dstar_moment).and
    (eventually_log_le_p (2 * ((m : ℝ) + 1)))).and eventually_h_facts).mono ?_
  rintro c₀ κ₀ d p h ⟨⟨⟨hW, hDs⟩, hlp⟩, hR, h0, -, -, -⟩ ct i hi
  have hd1 : (1 : ℝ) ≤ d := by have := hR.ten_pow_six_le_d; linarith
  have hd0 : (0 : ℝ) < d := by linarith
  have hlogd : 0 ≤ Real.log d := Real.log_nonneg hd1
  obtain ⟨c', hc'⟩ : ∃ c' : ℕ, c' = ⌈Real.log d⌉₊ := ⟨_, rfl⟩
  have hcl : Real.log d ≤ c' := hc' ▸ Nat.le_ceil _
  have hcu : (c' : ℝ) < Real.log d + 1 := hc' ▸ Nat.ceil_lt_add_one hlogd
  have hkl : Real.log d + 2 ≤ ((c' + 2 : ℕ) : ℝ) := by push_cast; linarith
  have hmk : 2 * ((m + 1) * (c' + 2)) ≤ p := by
    have h1 : 2 * ((m : ℝ) + 1) * ((c' : ℝ) + 2) ≤ p := by
      have : (c' : ℝ) + 2 ≤ Real.log d + 3 := by linarith
      calc 2 * ((m : ℝ) + 1) * ((c' : ℝ) + 2) ≤ 2 * ((m : ℝ) + 1) * (Real.log d + 3) :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ ≤ p := hlp
    have : ((2 * ((m + 1) * (c' + 2)) : ℕ) : ℝ) ≤ p := by push_cast; linarith
    exact_mod_cast this
  have e1 : 2 * ((m + 1) * (c' + 2)) = 2 * (m * (c' + 2)) + 2 * (c' + 2) := by ring
  have hk2 : 2 * (c' + 2) ≤ p := le_trans (Nat.le_add_left _ _) (e1 ▸ hmk)
  have hmk2 : 2 * (m * (c' + 2)) ≤ p := le_trans (Nat.le_add_right _ _) (e1 ▸ hmk)
  -- `3 (1 + d + d²) ≤ 21^k`
  have hpow21 : 3 * (1 + d + (d : ℝ) ^ 2) ≤ 21 ^ (c' + 2) := by
    have hdexp : (d : ℝ) ≤ Real.exp 1 ^ c' := by
      rw [← Real.exp_nat_mul, mul_one]
      calc (d : ℝ) = Real.exp (Real.log d) := (Real.exp_log hd0).symm
        _ ≤ Real.exp c' := Real.exp_le_exp.mpr hcl
    have he : Real.exp 1 ^ 2 ≤ 8 := by
      have := Real.exp_one_lt_d9; have := Real.exp_pos 1; nlinarith
    have hd2 : (d : ℝ) ^ 2 ≤ 8 ^ c' :=
      calc (d : ℝ) ^ 2 ≤ (Real.exp 1 ^ c') ^ 2 := pow_le_pow_left₀ hd0.le hdexp 2
        _ = (Real.exp 1 ^ 2) ^ c' := by rw [← pow_mul, ← pow_mul, mul_comm]
        _ ≤ 8 ^ c' := pow_le_pow_left₀ (by positivity) he c'
    have h8 : (8 : ℝ) ^ c' ≤ 21 ^ c' := pow_le_pow_left₀ (by norm_num) (by norm_num) c'
    have : 3 * (1 + d + (d : ℝ) ^ 2) ≤ 9 * (d : ℝ) ^ 2 := by nlinarith
    rw [pow_add]
    nlinarith
  -- the weight `Z = |D_*|^m`
  set Z : Config ct.V → ℝ := fun σ => |ct.Dstar σ| ^ m with hZdef
  have hZ0 : ∀ σ, 0 ≤ Z σ := fun σ => pow_nonneg (abs_nonneg _) m
  have hZeq : ∀ σ, wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 → Z σ = ct.Dstar σ ^ m :=
    fun σ hσ => by simp only [hZdef, abs_of_nonneg (dstar_nonneg ct hσ)]
  have hs := hR.sOf_pos
  have hsub : ∀ y : ct.V → ℝ, InCube (ct.lam * sOf d p) y → InCube (sOf d p) y := fun y hy k =>
    ⟨(hy k).1, le_trans (hy k).2 (by nlinarith [ct.ctx.lam_le_one, ct.ctx.lam_nonneg])⟩
  have hZw : 0 < Zw ct.G p (aOf d p) ct.yp ct.ym ct.S :=
    ct.ctx.pos ct.yp ct.ym (hsub _ ct.ctx.hyp) (hsub _ ct.ctx.hym)
  have hZk : ct.E (fun σ => Z σ ^ (c' + 2)) ≤ (21 * 12 ^ m) ^ (c' + 2) := by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · have : ct.E (fun σ => Z σ ^ (c' + 2)) = 1 := by
        rw [← lawE_const ct.G hZw.ne' 1]
        exact lawE_congr ct.G fun σ _ => by simp [hZdef, hm]
      rw [this, hm, pow_zero, mul_one]
      exact one_le_pow₀ (by norm_num)
    · have hn1 : 1 ≤ m * (c' + 2) := Nat.one_le_iff_ne_zero.mpr (by positivity)
      calc ct.E (fun σ => Z σ ^ (c' + 2)) = ct.E (fun σ => ct.Dstar σ ^ (m * (c' + 2))) :=
            lawE_congr ct.G fun σ hσ => by rw [hZeq σ hσ, ← pow_mul]
        _ ≤ 3 * (1 + d + (d : ℝ) ^ 2) * 12 ^ (m * (c' + 2)) := hDs ct _ hn1 hmk2
        _ ≤ 21 ^ (c' + 2) * 12 ^ (m * (c' + 2)) :=
            mul_le_mul_of_nonneg_right hpow21 (by positivity)
        _ = (21 * 12 ^ m) ^ (c' + 2) := by rw [mul_pow, ← pow_mul]
  obtain ⟨hWP, hWM⟩ := hW ct.toCapPoint i hi (c' + 2) hkl hk2 Z hZ0 (21 * 12 ^ m) (by positivity)
    hZk
  have hs2 := SecA.sOf_le_two hR
  have hyp2 : ct.yp i ≤ 2 := ((hsub _ ct.ctx.hyp) i).2.trans hs2
  have hym2 : ct.ym i ≤ 2 := ((hsub _ ct.ctx.hym) i).2.trans hs2
  have hsq : 0 < Real.sqrt h := Real.sqrt_pos.2 h0
  have hss : Real.sqrt h * Real.sqrt h = h := Real.mul_self_sqrt h0.le
  have hfin : ∀ y : ℝ, y ≤ 2 →
      3 * (s1K K + 2) * (21 * 12 ^ m) * Real.sqrt h * y / h ≤
        126 * (s1K K + 2) * 12 ^ m / Real.sqrt h := by
    intro y hy2
    rw [div_le_div_iff₀ h0 hsq]
    have hA : 0 ≤ 63 * (s1K K + 2) * 12 ^ m := by positivity
    calc 3 * (s1K K + 2) * (21 * 12 ^ m) * Real.sqrt h * y * Real.sqrt h
        = 63 * (s1K K + 2) * 12 ^ m * y * (Real.sqrt h * Real.sqrt h) := by ring
      _ = 63 * (s1K K + 2) * 12 ^ m * y * h := by rw [hss]
      _ ≤ 63 * (s1K K + 2) * 12 ^ m * 2 * h :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hy2 hA) h0.le
      _ = 126 * (s1K K + 2) * 12 ^ m * h := by ring
  constructor
  · exact le_trans (w5_branch ct (fun j => (ct.ctx.hyp j).1)
      (fun σ hσ => (posDef_of_wt_ne_zero ct.G hσ).1) h0 hi m Z hZ0 hZeq hWP) (hfin _ hyp2)
  · exact le_trans (w5_branch ct (fun j => (ct.ctx.hym j).1)
      (fun σ hσ => (posDef_of_wt_ne_zero ct.G hσ).2) h0 hi m Z hZ0 hZeq hWM) (hfin _ hym2)

end BiluLinial.Tight.SecB
