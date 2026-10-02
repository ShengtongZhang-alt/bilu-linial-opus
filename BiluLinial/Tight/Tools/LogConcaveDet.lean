/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Common.Spectral
public import BiluLinial.Common.Schur

/-!
# Midpoint log-concavity of determinants along affine families

Pure matrix facts behind TB.WT3d (`docs/tight/BP_SECB.md`). All matrices are real and square;
`X ⪯ Y` is written `(Y - X).PosSemidef`. A *midpoint triple* is `A₁, A₂, A` with
`A₁ + A₂ = 2A`: the values of an affine family at `z + w`, `z - w` and `z`.

* `det_smul_one_add_smul`: `det(rI + sC) = ∏ (r + s λᵢ)` for symmetric `C`.
* `exists_factor_of_posDef`, `exists_eq_transpose_mul_self_of_posSemidef`: `A = S Sᵀ` with `S`
  invertible for `A ≻ 0`, and `Δ = BᵀB` for `Δ ⪰ 0` (spectral theorem).
* (a) `det_mul_det_le_det_sq`: `det A₁ det A₂ ≤ (det A)²` for `A₁, A₂ ≻ 0`, `A₁ + A₂ = 2A`
  (with `A₁ = S Sᵀ`, `C = S⁻¹ A₂ S⁻ᵀ`: `λ ≤ ((1 + λ)/2)²` for each eigenvalue of `C`).
* `det_le_det_of_posDef_of_sub`: `A ≻ 0`, `A ⪯ B` ⇒ `det A ≤ det B`.
* `posSemidef_half_inv_add_inv_sub_inv`: `Q₁, Q₂ ≻ 0`, `Q₁ + Q₂ = 2Q` ⇒
  `Q⁻¹ ⪯ (Q₁⁻¹ + Q₂⁻¹)/2` (sum of the blocks `[[Qᵢ⁻¹, I], [I, Qᵢ]] ⪰ 0`, Schur complement).
* (b) `det_div_det_add_midpoint`: for `Δ ⪰ 0`, `det P / det(P + Δ)` is midpoint log-concave on
  `{P ≻ 0}`. With `Δ = BᵀB` and `Q = P + Δ`: `det P / det Q = det(I - BQ⁻¹Bᵀ)`
  (Weinstein–Aronszajn), `I - BQ⁻¹Bᵀ ≻ 0` (Schur complements of `[[Q, Bᵀ], [B, I]]`), and it is
  midpoint concave in `Q`; then (a) and monotonicity of `det`.
* `inv_apply_self_mul_det`: `(Q⁻¹)_kk det Q = det Q_{-k}` (Cramer).
* (c) `det_mul_inv_diag_midpoint`: `det P · ((P + Δ)⁻¹)_kk = (det P / det Q) det Q_{-k}` is
  midpoint log-concave on `{P ≻ 0}`, by (b) and (a) for the principal submatrix `Q_{-k}`.
* `MidLC U f`: `f ≥ 0` on `U` and `f(z+w) f(z-w) ≤ f(z)²` whenever `z ± w ∈ U`; closed under
  products, powers and list products. `midLC_det`, `midLC_det_mul_inv_diag`: (a) and (c) along
  an affine family `P(z+w) + P(z-w) = 2P(z)`.
-/

@[expose] public section

namespace BiluLinial.Tight

open Matrix BiluLinial

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
theorem transpose_eq_star_real (M : Matrix n n ℝ) : Mᵀ = star M := by
  rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]

/-- The spectral theorem with an orthogonal `U`: `A = U diag(λ) Uᵀ`, `UUᵀ = UᵀU = I`. -/
theorem exists_orthogonal_spectral {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    ∃ U : Matrix n n ℝ, U * Uᵀ = 1 ∧ Uᵀ * U = 1 ∧ A = U * diagonal hA.eigenvalues * Uᵀ := by
  refine ⟨(hA.eigenvectorUnitary : Matrix n n ℝ), ?_, ?_, ?_⟩
  · rw [transpose_eq_star_real]
    exact Unitary.coe_mul_star_self _
  · rw [transpose_eq_star_real]
    exact Unitary.coe_star_mul_self _
  · rw [transpose_eq_star_real]
    exact spectral_theorem_real hA

/-- `det(rI + sC) = ∏ (r + s λᵢ)` for symmetric `C`. -/
theorem det_smul_one_add_smul {C : Matrix n n ℝ} (hC : C.IsHermitian) (r s : ℝ) :
    (r • (1 : Matrix n n ℝ) + s • C).det = ∏ i, (r + s * hC.eigenvalues i) := by
  have hU : star (hC.eigenvectorUnitary : Matrix n n ℝ) * (hC.eigenvectorUnitary : Matrix n n ℝ)
      = 1 := Unitary.coe_star_mul_self _
  rw [smul_one_add_smul_eq_conj hC r s, det_mul_comm, ← Matrix.mul_assoc, hU, Matrix.one_mul,
    det_diagonal]

/-- A positive definite matrix is `S Sᵀ` with `S` invertible (`ST = TS = I`). -/
theorem exists_factor_of_posDef {A : Matrix n n ℝ} (hA : A.PosDef) :
    ∃ S T : Matrix n n ℝ, S * T = 1 ∧ T * S = 1 ∧ A = S * Sᵀ := by
  obtain ⟨U, hU1, hU2, hAU⟩ := exists_orthogonal_spectral hA.1
  have hev : ∀ i, 0 < hA.1.eigenvalues i := hA.eigenvalues_pos
  set ev := hA.1.eigenvalues
  have hsq : ∀ i, Real.sqrt (ev i) ≠ 0 := fun i => (Real.sqrt_pos.2 (hev i)).ne'
  have hdd : diagonal (fun i => Real.sqrt (ev i)) * diagonal (fun i => 1 / Real.sqrt (ev i)) =
      1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    field_simp [hsq i]
  have hdd' : diagonal (fun i => 1 / Real.sqrt (ev i)) * diagonal (fun i => Real.sqrt (ev i)) =
      1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    field_simp [hsq i]
  have hsq2 : diagonal (fun i => Real.sqrt (ev i)) * diagonal (fun i => Real.sqrt (ev i)) =
      diagonal ev := by
    rw [diagonal_mul_diagonal]
    congr 1
    funext i
    exact Real.mul_self_sqrt (hev i).le
  refine ⟨U * diagonal (fun i => Real.sqrt (ev i)), diagonal (fun i => 1 / Real.sqrt (ev i)) * Uᵀ,
    ?_, ?_, ?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal _), hdd, Matrix.one_mul, hU1]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc Uᵀ, hU2, Matrix.one_mul, hdd']
  · calc A = U * diagonal ev * Uᵀ := hAU
      _ = U * (diagonal (fun i => Real.sqrt (ev i)) * diagonal (fun i => Real.sqrt (ev i))) * Uᵀ :=
        by rw [hsq2]
      _ = U * diagonal (fun i => Real.sqrt (ev i)) * (U * diagonal (fun i => Real.sqrt (ev i)))ᵀ :=
        by rw [transpose_mul, diagonal_transpose]; simp only [Matrix.mul_assoc]

/-- A positive semidefinite matrix is `BᵀB`. -/
theorem exists_eq_transpose_mul_self_of_posSemidef {Δ : Matrix n n ℝ} (hΔ : Δ.PosSemidef) :
    ∃ B : Matrix n n ℝ, Δ = Bᵀ * B := by
  obtain ⟨U, -, -, hΔU⟩ := exists_orthogonal_spectral hΔ.1
  have hev : ∀ i, 0 ≤ hΔ.1.eigenvalues i := hΔ.eigenvalues_nonneg
  set ev := hΔ.1.eigenvalues
  have hsq2 : diagonal (fun i => Real.sqrt (ev i)) * diagonal (fun i => Real.sqrt (ev i)) =
      diagonal ev := by
    rw [diagonal_mul_diagonal]
    congr 1
    funext i
    exact Real.mul_self_sqrt (hev i)
  refine ⟨diagonal (fun i => Real.sqrt (ev i)) * Uᵀ, ?_⟩
  rw [transpose_mul, transpose_transpose, diagonal_transpose, hΔU, ← hsq2]
  simp only [Matrix.mul_assoc]

/-- With `ST = I`: `X = S (T X Tᵀ) Sᵀ`. -/
theorem eq_conj_of_mul_eq_one {S T : Matrix n n ℝ} (hST : S * T = 1) (X : Matrix n n ℝ) :
    X = S * (T * X * Tᵀ) * Sᵀ := by
  calc X = (S * T) * X * (S * T)ᵀ := by rw [hST, transpose_one, Matrix.one_mul, Matrix.mul_one]
    _ = S * (T * X * Tᵀ) * Sᵀ := by rw [transpose_mul]; simp only [Matrix.mul_assoc]

omit [Fintype n] [DecidableEq n] in
/-- The midpoint of a midpoint triple of positive definite matrices is positive definite. -/
theorem posDef_of_add_eq_two_smul {A₁ A₂ A : Matrix n n ℝ} (h₁ : A₁.PosDef) (h₂ : A₂.PosDef)
    (h : A₁ + A₂ = (2 : ℝ) • A) : A.PosDef := by
  have e : A = (1 / 2 : ℝ) • (A₁ + A₂) := by
    rw [h, smul_smul]
    norm_num
  rw [e]
  exact (h₁.add h₂).smul (by norm_num)

/-- AM–GM per eigenvalue: `det C ≤ det((I + C)/2)²` for `C ⪰ 0`. -/
theorem det_le_det_half_one_add_sq {C : Matrix n n ℝ} (hC : C.PosSemidef) :
    C.det ≤ ((1 / 2 : ℝ) • (1 : Matrix n n ℝ) + (1 / 2 : ℝ) • C).det ^ 2 := by
  have hdet : C.det = ∏ i, hC.1.eigenvalues i := by
    simpa using det_smul_one_add_smul hC.1 0 1
  rw [hdet, det_smul_one_add_smul hC.1, ← Finset.prod_pow]
  refine Finset.prod_le_prod₀ (fun i _ => hC.eigenvalues_nonneg i) fun i _ => ?_
  nlinarith [sq_nonneg (1 - hC.1.eigenvalues i)]

/-- **(a)** `det A₁ det A₂ ≤ (det A)²` for `A₁, A₂ ≻ 0` with `A₁ + A₂ = 2A`. -/
theorem det_mul_det_le_det_sq {A₁ A₂ A : Matrix n n ℝ} (h₁ : A₁.PosDef) (h₂ : A₂.PosDef)
    (h : A₁ + A₂ = (2 : ℝ) • A) : A₁.det * A₂.det ≤ A.det ^ 2 := by
  obtain ⟨S, T, hST, hTS, hA₁⟩ := exists_factor_of_posDef h₁
  have hTu : IsUnit T := ⟨⟨T, S, hTS, hST⟩, rfl⟩
  obtain ⟨C, hC, hA₂⟩ : ∃ C : Matrix n n ℝ, C.PosDef ∧ A₂ = S * C * Sᵀ := by
    refine ⟨T * A₂ * Tᵀ, ?_, eq_conj_of_mul_eq_one hST A₂⟩
    rw [transpose_eq_star_real]
    exact (Matrix.IsUnit.posDef_star_right_conjugate_iff hTu).2 h₂
  have hA : A = S * ((1 / 2 : ℝ) • (1 : Matrix n n ℝ) + (1 / 2 : ℝ) • C) * Sᵀ := by
    have e : A = (1 / 2 : ℝ) • (A₁ + A₂) := by
      rw [h, smul_smul]
      norm_num
    rw [e, hA₁, hA₂]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      smul_add]
  have key := det_le_det_half_one_add_sq hC.posSemidef
  rw [hA₁, hA₂, hA]
  simp only [det_mul, det_transpose]
  set M := (1 / 2 : ℝ) • (1 : Matrix n n ℝ) + (1 / 2 : ℝ) • C
  calc S.det * S.det * (S.det * C.det * S.det) = (S.det ^ 2) ^ 2 * C.det := by ring
    _ ≤ (S.det ^ 2) ^ 2 * M.det ^ 2 := mul_le_mul_of_nonneg_left key (by positivity)
    _ = (S.det * M.det * S.det) ^ 2 := by ring

/-- Monotonicity of `det` in the Loewner order: `A ≻ 0`, `A ⪯ B` ⇒ `det A ≤ det B`. -/
theorem det_le_det_of_posDef_of_sub {A B : Matrix n n ℝ} (hA : A.PosDef)
    (hBA : (B - A).PosSemidef) : A.det ≤ B.det := by
  obtain ⟨S, T, hST, -, hAS⟩ := exists_factor_of_posDef hA
  obtain ⟨C, hC, hE⟩ : ∃ C : Matrix n n ℝ, C.PosSemidef ∧ B - A = S * C * Sᵀ := by
    refine ⟨T * (B - A) * Tᵀ, ?_, eq_conj_of_mul_eq_one hST _⟩
    have := hBA.mul_mul_conjTranspose_same T
    rwa [conjTranspose_eq_transpose_of_trivial] at this
  have hB : B = S * (1 + C) * Sᵀ := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, ← hE, ← hAS]
    abel
  have h1C : 1 ≤ (1 + C).det := by
    have e := det_smul_one_add_smul hC.1 1 1
    simp only [one_smul, one_mul] at e
    rw [e]
    calc (1 : ℝ) = ∏ _i : n, (1 : ℝ) := by simp
      _ ≤ ∏ i, (1 + hC.1.eigenvalues i) :=
        Finset.prod_le_prod₀ (fun _ _ => zero_le_one) fun i _ => by
          linarith [hC.eigenvalues_nonneg i]
  rw [hB, hAS, det_mul, det_mul, det_mul, det_transpose]
  nlinarith [sq_nonneg S.det, mul_le_mul_of_nonneg_left h1C (sq_nonneg S.det)]

/-- Midpoint operator convexity of the inverse: `Q₁, Q₂ ≻ 0`, `Q₁ + Q₂ = 2Q` ⇒
`Q⁻¹ ⪯ (Q₁⁻¹ + Q₂⁻¹)/2`. -/
theorem posSemidef_half_inv_add_inv_sub_inv {Q₁ Q₂ Q : Matrix n n ℝ} (h₁ : Q₁.PosDef)
    (h₂ : Q₂.PosDef) (h : Q₁ + Q₂ = (2 : ℝ) • Q) :
    ((1 / 2 : ℝ) • (Q₁⁻¹ + Q₂⁻¹) - Q⁻¹).PosSemidef := by
  have hQ : Q.PosDef := posDef_of_add_eq_two_smul h₁ h₂ h
  have hblk : ∀ R : Matrix n n ℝ, R.PosDef →
      (fromBlocks R⁻¹ (1 : Matrix n n ℝ) (1 : Matrix n n ℝ)ᵀ R).PosSemidef := fun R hR => by
    rw [schur_posSemidef_iff _ _ hR, transpose_one, Matrix.one_mul, Matrix.mul_one, sub_self]
    exact PosSemidef.zero
  have hsum := ((hblk Q₁ h₁).add (hblk Q₂ h₂)).smul (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  have e : (1 / 2 : ℝ) • (fromBlocks Q₁⁻¹ (1 : Matrix n n ℝ) (1 : Matrix n n ℝ)ᵀ Q₁ +
      fromBlocks Q₂⁻¹ (1 : Matrix n n ℝ) (1 : Matrix n n ℝ)ᵀ Q₂) =
      fromBlocks ((1 / 2 : ℝ) • (Q₁⁻¹ + Q₂⁻¹)) (1 : Matrix n n ℝ) (1 : Matrix n n ℝ)ᵀ Q := by
    have e1 : (1 / 2 : ℝ) • ((1 : Matrix n n ℝ) + 1) = 1 := by
      rw [← two_smul ℝ (1 : Matrix n n ℝ), smul_smul]
      norm_num
    have e2 : (1 / 2 : ℝ) • (Q₁ + Q₂) = Q := by
      rw [h, smul_smul]
      norm_num
    rw [fromBlocks_add, fromBlocks_smul, transpose_one, e1, e2]
  rw [e] at hsum
  have := (schur_posSemidef_iff _ _ hQ).1 hsum
  rwa [transpose_one, Matrix.one_mul, Matrix.mul_one] at this

/-- The ratio factor: for `P ≻ 0` and `Q = P + BᵀB`, `det P / det Q = det(I - BQ⁻¹Bᵀ)` and
`I - BQ⁻¹Bᵀ ≻ 0`. -/
theorem det_div_det_add_eq_and_posDef {R : Matrix n n ℝ} (hR : R.PosDef) (B : Matrix n n ℝ) :
    R.det / (R + Bᵀ * B).det = (1 - B * (R + Bᵀ * B)⁻¹ * Bᵀ).det ∧
      (1 - B * (R + Bᵀ * B)⁻¹ * Bᵀ).PosDef := by
  have hBB : (Bᵀ * B).PosSemidef := by
    have := posSemidef_conjTranspose_mul_self B
    rwa [conjTranspose_eq_transpose_of_trivial] at this
  have hQ : (R + Bᵀ * B).PosDef := hR.add_posSemidef hBB
  have hQd : (R + Bᵀ * B).det ≠ 0 := hQ.det_pos.ne'
  have hdet : R.det = (R + Bᵀ * B).det * (1 - B * (R + Bᵀ * B)⁻¹ * Bᵀ).det := by
    have e : R = (R + Bᵀ * B) * (1 - (R + Bᵀ * B)⁻¹ * Bᵀ * B) := by
      rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hQd), Matrix.one_mul]
      abel
    calc R.det = ((R + Bᵀ * B) * (1 - (R + Bᵀ * B)⁻¹ * Bᵀ * B)).det := congrArg det e
      _ = _ := by rw [det_mul, det_one_sub_mul_comm, ← Matrix.mul_assoc]
  have hratio : R.det / (R + Bᵀ * B).det = (1 - B * (R + Bᵀ * B)⁻¹ * Bᵀ).det := by
    rw [hdet]
    field_simp
  refine ⟨hratio, ?_⟩
  have hblk : (fromBlocks (R + Bᵀ * B) Bᵀ Bᵀᵀ 1).PosSemidef := by
    rw [schur_posSemidef_iff _ _ PosDef.one, inv_one, Matrix.mul_one, transpose_transpose,
      add_sub_cancel_right]
    exact hR.posSemidef
  let := hQ.isUnit.invertible
  have hM : (1 - B * (R + Bᵀ * B)⁻¹ * Bᵀ).PosSemidef := by
    have := (PosDef.fromBlocks₁₁ Bᵀ (1 : Matrix n n ℝ) hQ).1
      (by rwa [conjTranspose_eq_transpose_of_trivial])
    rwa [conjTranspose_eq_transpose_of_trivial, transpose_transpose] at this
  rw [hM.posDef_iff_det_ne_zero, ← hratio]
  exact div_ne_zero hR.det_pos.ne' hQd

/-- **(b)** For `Δ ⪰ 0`, `det P / det(P + Δ)` is midpoint log-concave on `{P ≻ 0}`. -/
theorem det_div_det_add_midpoint {P₁ P₂ P Δ : Matrix n n ℝ} (h₁ : P₁.PosDef) (h₂ : P₂.PosDef)
    (h : P₁ + P₂ = (2 : ℝ) • P) (hΔ : Δ.PosSemidef) :
    P₁.det / (P₁ + Δ).det * (P₂.det / (P₂ + Δ).det) ≤ (P.det / (P + Δ).det) ^ 2 := by
  obtain ⟨B, rfl⟩ := exists_eq_transpose_mul_self_of_posSemidef hΔ
  have hP : P.PosDef := posDef_of_add_eq_two_smul h₁ h₂ h
  obtain ⟨e₁, hM₁⟩ := det_div_det_add_eq_and_posDef h₁ B
  obtain ⟨e₂, hM₂⟩ := det_div_det_add_eq_and_posDef h₂ B
  obtain ⟨e₀, -⟩ := det_div_det_add_eq_and_posDef hP B
  rw [e₁, e₂, e₀]
  have hBB : (Bᵀ * B).PosSemidef := by
    have := posSemidef_conjTranspose_mul_self B
    rwa [conjTranspose_eq_transpose_of_trivial] at this
  have hQ : (P₁ + Bᵀ * B) + (P₂ + Bᵀ * B) = (2 : ℝ) • (P + Bᵀ * B) := by
    rw [smul_add, ← h, two_smul]
    abel
  have hinv := posSemidef_half_inv_add_inv_sub_inv (h₁.add_posSemidef hBB)
    (h₂.add_posSemidef hBB) hQ
  set Q₁ := P₁ + Bᵀ * B
  set Q₂ := P₂ + Bᵀ * B
  set Q := P + Bᵀ * B
  set N := (1 / 2 : ℝ) • ((1 - B * Q₁⁻¹ * Bᵀ) + (1 - B * Q₂⁻¹ * Bᵀ)) with hNdef
  have hN : N.PosDef := (hM₁.add hM₂).smul (by norm_num)
  have hNM : ((1 - B * Q⁻¹ * Bᵀ) - N).PosSemidef := by
    have e : (1 - B * Q⁻¹ * Bᵀ) - N = B * ((1 / 2 : ℝ) • (Q₁⁻¹ + Q₂⁻¹) - Q⁻¹) * Bᵀ := by
      rw [hNdef]
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add,
        Matrix.add_mul]
      module
    rw [e]
    have := hinv.mul_mul_conjTranspose_same B
    rwa [conjTranspose_eq_transpose_of_trivial] at this
  have hsumN : (1 - B * Q₁⁻¹ * Bᵀ) + (1 - B * Q₂⁻¹ * Bᵀ) = (2 : ℝ) • N := by
    rw [hNdef, smul_smul]
    norm_num
  have h1 := det_mul_det_le_det_sq hM₁ hM₂ hsumN
  have h2 := det_le_det_of_posDef_of_sub hN hNM
  have h3 := hN.det_pos
  exact h1.trans (pow_le_pow_left₀ h3.le h2 2)

/-- Cramer: `(Q⁻¹)_kk det Q = det Q_{-k}` for `Q ≻ 0`. -/
theorem inv_apply_self_mul_det {Q : Matrix n n ℝ} (hQ : Q.PosDef) (k : n) :
    Q⁻¹ k k * Q.det = (delVertex Q k).det := by
  have hD : (delVertex Q k).PosDef := hQ.submatrix Subtype.val_injective
  have hs : 0 < vertexSchur Q k := (vertexSchur_posDef_iff hQ.1 hD).1 hQ
  rw [vertexSchur_inv_apply hQ.1 hD hQ, vertexSchur_det hQ.1 hD]
  field_simp

/-- **(c)** For `Δ ⪰ 0`, `det P · ((P + Δ)⁻¹)_kk` is midpoint log-concave on `{P ≻ 0}`. -/
theorem det_mul_inv_diag_midpoint {P₁ P₂ P Δ : Matrix n n ℝ} (h₁ : P₁.PosDef) (h₂ : P₂.PosDef)
    (h : P₁ + P₂ = (2 : ℝ) • P) (hΔ : Δ.PosSemidef) (k : n) :
    P₁.det * (P₁ + Δ)⁻¹ k k * (P₂.det * (P₂ + Δ)⁻¹ k k) ≤ (P.det * (P + Δ)⁻¹ k k) ^ 2 := by
  have hP := posDef_of_add_eq_two_smul h₁ h₂ h
  have split : ∀ R : Matrix n n ℝ, R.PosDef →
      R.det * (R + Δ)⁻¹ k k = R.det / (R + Δ).det * (delVertex (R + Δ) k).det := by
    intro R hR
    have hQ := hR.add_posSemidef hΔ
    rw [← inv_apply_self_mul_det hQ k]
    field_simp [hQ.det_pos.ne']
  rw [split P₁ h₁, split P₂ h₂, split P hP]
  have hr := det_div_det_add_midpoint h₁ h₂ h hΔ
  have hD₁ : (delVertex (P₁ + Δ) k).PosDef :=
    (h₁.add_posSemidef hΔ).submatrix Subtype.val_injective
  have hD₂ : (delVertex (P₂ + Δ) k).PosDef :=
    (h₂.add_posSemidef hΔ).submatrix Subtype.val_injective
  have hsum : delVertex (P₁ + Δ) k + delVertex (P₂ + Δ) k = (2 : ℝ) • delVertex (P + Δ) k := by
    ext a b
    have := congrFun (congrFun h a.1) b.1
    simp only [delVertex, Matrix.add_apply, Matrix.smul_apply, Matrix.submatrix_apply,
      smul_eq_mul] at this ⊢
    linarith
  have hm := det_mul_det_le_det_sq hD₁ hD₂ hsum
  have hm0 : 0 ≤ (delVertex (P₁ + Δ) k).det * (delVertex (P₂ + Δ) k).det :=
    (mul_pos hD₁.det_pos hD₂.det_pos).le
  calc P₁.det / (P₁ + Δ).det * (delVertex (P₁ + Δ) k).det *
        (P₂.det / (P₂ + Δ).det * (delVertex (P₂ + Δ) k).det)
        = P₁.det / (P₁ + Δ).det * (P₂.det / (P₂ + Δ).det) *
          ((delVertex (P₁ + Δ) k).det * (delVertex (P₂ + Δ) k).det) := by ring
    _ ≤ (P.det / (P + Δ).det) ^ 2 * (delVertex (P + Δ) k).det ^ 2 :=
        mul_le_mul hr hm hm0 (sq_nonneg _)
    _ = (P.det / (P + Δ).det * (delVertex (P + Δ) k).det) ^ 2 := by ring

/-! ### Midpoint log-concave functions -/

section MidLC

variable {X : Type*} [Add X] [Sub X]

/-- `f ≥ 0` on `U`, and `f(z+w) f(z-w) ≤ f(z)²` whenever `z + w, z - w ∈ U`. -/
def MidLC (U : Set X) (f : X → ℝ) : Prop :=
  (∀ x ∈ U, 0 ≤ f x) ∧ ∀ z w, z + w ∈ U → z - w ∈ U → f (z + w) * f (z - w) ≤ f z ^ 2

theorem MidLC.mul {U : Set X} {f g : X → ℝ} (hf : MidLC U f) (hg : MidLC U g) :
    MidLC U fun x => f x * g x := by
  refine ⟨fun x hx => mul_nonneg (hf.1 x hx) (hg.1 x hx), fun z w h1 h2 => ?_⟩
  have e : f (z + w) * g (z + w) * (f (z - w) * g (z - w)) =
      f (z + w) * f (z - w) * (g (z + w) * g (z - w)) := by ring
  rw [e, mul_pow]
  exact mul_le_mul (hf.2 z w h1 h2) (hg.2 z w h1 h2) (mul_nonneg (hg.1 _ h1) (hg.1 _ h2))
    (sq_nonneg _)

theorem MidLC.const {U : Set X} {c : ℝ} (hc : 0 ≤ c) : MidLC U fun _ => c :=
  ⟨fun _ _ => hc, fun _ _ _ _ => (sq c).symm.le⟩

theorem MidLC.pow {U : Set X} {f : X → ℝ} (hf : MidLC U f) (m : ℕ) :
    MidLC U fun x => f x ^ m := by
  induction m with
  | zero => simpa using MidLC.const (U := U) zero_le_one
  | succ m ih => simpa only [pow_succ] using ih.mul hf

theorem MidLC.list_prod {ι : Type*} {U : Set X} (f : ι → X → ℝ) (l : List ι)
    (h : ∀ t ∈ l, MidLC U (f t)) : MidLC U fun x => (l.map fun t => f t x).prod := by
  induction l with
  | nil => simpa using MidLC.const (U := U) zero_le_one
  | cons t l ih =>
    simp only [List.map_cons, List.prod_cons]
    exact (h t List.mem_cons_self).mul (ih fun t' ht' => h t' (List.mem_cons_of_mem _ ht'))

/-- **(a)** along an affine family: `det P(x)` is midpoint log-concave on `U ⊆ {P ≻ 0}`. -/
theorem midLC_det {U : Set X} {P : X → Matrix n n ℝ}
    (hP : ∀ z w, P (z + w) + P (z - w) = (2 : ℝ) • P z) (hU : ∀ x ∈ U, (P x).PosDef) :
    MidLC U fun x => (P x).det :=
  ⟨fun x hx => (hU x hx).det_pos.le, fun z w h1 h2 =>
    det_mul_det_le_det_sq (hU _ h1) (hU _ h2) (hP z w)⟩

/-- **(c)** along an affine family: `det P(x) · ((P(x) + Δ)⁻¹)_kk` is midpoint log-concave on
`U ⊆ {P ≻ 0}`. -/
theorem midLC_det_mul_inv_diag {U : Set X} {P : X → Matrix n n ℝ}
    (hP : ∀ z w, P (z + w) + P (z - w) = (2 : ℝ) • P z) (hU : ∀ x ∈ U, (P x).PosDef)
    {Δ : Matrix n n ℝ} (hΔ : Δ.PosSemidef) (k : n) :
    MidLC U fun x => (P x).det * (P x + Δ)⁻¹ k k :=
  ⟨fun x hx => mul_nonneg (hU x hx).det_pos.le ((hU x hx).add_posSemidef hΔ).inv.diag_pos.le,
    fun z w h1 h2 => det_mul_inv_diag_midpoint (hU _ h1) (hU _ h2) (hP z w) hΔ k⟩

end MidLC

end BiluLinial.Tight
