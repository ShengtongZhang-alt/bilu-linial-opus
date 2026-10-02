/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecB.WTBase
public import BiluLinial.Tight.SecA.ClipRecip
public import BiluLinial.Tight.SecA.TransRemLo
public import BiluLinial.Tight.SecC.ShiftMat

/-!
# Star form of the (shifted) inverse diagonals at a real star vector (sub-node (R1) of TB.WT5r°)

Source lines 1043–1071 (AUDIT-B §2.5). At the deleted vertex `i`, with `Q(x) = P̃^τ(x) + zY_S`
(`precSub` with the incident signs replaced by `x ∈ ℝ^J`, `J = N_S(i)`), the vertex-Schur
formulas (`SecA.schur_of_posDef`) give, with the shifted inherited core inverse
`K_z = (P̃_core + zY_{S-i})⁻¹` (`Kz`) and `A_z = (a² y_i/(D_i + z y_i)) Y^{1/2} K_z Y^{1/2}` on `J`
(`Az`; `A_0 = A` is the root matrix, `A_z = (D_i/(D_i + z y_i)) M_z`):
* `Q(x) ≻ 0 ⇔ q_{A_z}(x) < 1` (core `≻ 0`, `z ≥ 0`);
* `y_i (Q⁻¹)_ii · (D_i + z y_i)(1 - q_{A_z}(x)) = y_i`;
* `y_k (Q⁻¹)_kk · (D_i + z y_i)(1 - q_{A_z}(x)) = y_k (K_{z,kk} (D_i+zy_i)(1 - q_{A_z}(x)) +
  a² y_i (Σ_{j ∈ J} K_{z,kj} √y_j x_j)²)` for `k ≠ i` (`star_diag`).

Checks: `x = 0` gives `y_k (K_z)_kk` and `y_i/(D_i + z y_i)`, the core values; `y_i = 0`
decouples the root (`A_z = 0`).
-/

@[expose] public section

namespace BiluLinial.Tight.SecB.WR

open Matrix

section Star

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The shifted inherited core inverse `K_z = (P̃_core + z Y_{S-i})⁻¹` at the deleted vertex. -/
noncomputable def Kz (a τ z : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) (i : V) :
    Matrix V V ℝ :=
  (precCore G a τ y σ S i + z • srcDiag y (S.erase i))⁻¹

/-- The shifted root matrix `A_z = (a² y_i/(D_i + z y_i)) Y^{1/2} K_z Y^{1/2}` on `J = N_S(i)`. -/
noncomputable def Az (a τ z : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) (i : V) :
    Matrix (nbhd G S i) (nbhd G S i) ℝ :=
  Matrix.of fun j l => a ^ 2 * y i / (diagD G a y S i + z * y i) *
    (Real.sqrt (y j) * Kz G a τ z y σ S i j l * Real.sqrt (y l))

omit [Fintype V] in
theorem coreOf_precSub_shift (a τ z : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) (i : V)
    (x : nbhd G S i → ℝ) :
    SecA.coreOf (precSub G a τ y σ S i x + z • srcDiag y S) i =
      precCore G a τ y σ S i + z • srcDiag y (S.erase i) := by
  ext u w
  by_cases h : u = i ∨ w = i
  · simp only [SecA.coreOf, precCore, Matrix.add_apply, Matrix.smul_apply, of_apply, srcDiag,
      diagonal_apply, smul_eq_mul, Finset.mem_erase, if_pos h]
    by_cases huw : u = w
    · subst huw
      have hu : u = i := by tauto
      simp [hu]
    · simp [huw]
  · have hu : u ≠ i := fun h' => h (Or.inl h')
    have hw : w ≠ i := fun h' => h (Or.inr h')
    simp only [SecA.coreOf, precCore, Matrix.add_apply, Matrix.smul_apply, of_apply, srcDiag,
      diagonal_apply, smul_eq_mul, Finset.mem_erase, if_neg h, precSub]
    rw [dif_neg fun h' => hu h'.1, dif_neg fun h' => hw h'.1]
    by_cases huw : u = w
    · subst huw
      simp [hu]
    · simp [huw]

omit [Fintype V] in
theorem colOf_precSub_shift (a τ z : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) (i : V)
    (x : nbhd G S i → ℝ) :
    SecA.colOf (precSub G a τ y σ S i x + z • srcDiag y S) i =
      SecA.colOf (precSub G a τ y σ S i x) i := by
  funext w
  by_cases hw : w = i
  · simp [SecA.colOf, hw]
  · simp [SecA.colOf, hw, srcDiag]

theorem precSub_shift_apply_root {a τ z : ℝ} {y : V → ℝ} {σ : Config V} {S : Finset V} {i : V}
    (hi : i ∈ S) (x : nbhd G S i → ℝ) :
    (precSub G a τ y σ S i x + z • srcDiag y S) i i = diagD G a y S i + z * y i := by
  rw [Matrix.add_apply, precSub_apply_root G hi x]
  simp [srcDiag, hi]

omit [Fintype V] [DecidableEq V] in
theorem diagD_add_pos (a : ℝ) {y : V → ℝ} (hy : ∀ k, 0 ≤ y k) (S : Finset V) (i : V) {z : ℝ}
    (hz : 0 ≤ z) : 0 < diagD G a y S i + z * y i := by
  have h1 : 0 ≤ ∑ j ∈ nbhd G S i, cEdge a y i j := Finset.sum_nonneg fun j _ =>
    FloorIns.cRoot_nonneg (mul_nonneg (mul_nonneg (sq_nonneg a) (hy i)) (hy j))
  have := mul_nonneg hz (hy i)
  unfold diagD
  linarith

/-- The incident column quadratic form for any matrix `C`:
`bᵀ C b = a² y_i Σ_{j,l ∈ J} x_j √y_j C_jl √y_l x_l`. -/
theorem colOf_precSub_quad_gen {a τ : ℝ} (hτ : τ ^ 2 = 1) {y : V → ℝ} (hy : ∀ k, 0 ≤ y k)
    (σ : Config V) {S : Finset V} {i : V} (x : nbhd G S i → ℝ) (C : Matrix V V ℝ) :
    SecA.colOf (precSub G a τ y σ S i x) i ⬝ᵥ (C *ᵥ SecA.colOf (precSub G a τ y σ S i x) i) =
      a ^ 2 * y i * ∑ j : nbhd G S i, ∑ l : nbhd G S i,
        x j * (Real.sqrt (y j) * C j l * Real.sqrt (y l)) * x l := by
  have hc : (τ * a * Real.sqrt (y i)) ^ 2 = a ^ 2 * y i := by
    rw [mul_pow, mul_pow, hτ, Real.sq_sqrt (hy i), one_mul]
  rw [colOf_precSub]
  set c := τ * a * Real.sqrt (y i)
  have hL : (fun w => c * (Real.sqrt (y w) * extStar G x w)) ⬝ᵥ
      (C *ᵥ fun w => c * (Real.sqrt (y w) * extStar G x w)) =
      ∑ j : nbhd G S i, x j * ∑ l : nbhd G S i, x l *
        (c ^ 2 * (Real.sqrt (y j) * C j l * Real.sqrt (y l))) := by
    simp only [dotProduct, mulVec]
    have e1 : ∀ w, c * (Real.sqrt (y w) * extStar G x w) *
        ∑ w', C w w' * (c * (Real.sqrt (y w') * extStar G x w')) =
        extStar G x w * ∑ w', extStar G x w' *
          (c ^ 2 * (Real.sqrt (y w) * C w w' * Real.sqrt (y w'))) := by
      intro w
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun w' _ => ?_
      ring
    have e2 : ∀ w, ∑ w', extStar G x w' *
        (c ^ 2 * (Real.sqrt (y w) * C w w' * Real.sqrt (y w'))) =
        ∑ l : nbhd G S i, x l * (c ^ 2 * (Real.sqrt (y w) * C w l * Real.sqrt (y l))) :=
      fun w => sum_extStar G x _
    simp only [e1, e2]
    exact sum_extStar G x (fun w => ∑ l : nbhd G S i, x l *
      (c ^ 2 * (Real.sqrt (y w) * C w l * Real.sqrt (y l))))
  rw [hL, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [hc]
  ring

theorem qForm_Az (a τ z : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) (i : V)
    (x : nbhd G S i → ℝ) :
    qForm (Az G a τ z y σ S i) x = a ^ 2 * y i / (diagD G a y S i + z * y i) *
      ∑ j : nbhd G S i, ∑ l : nbhd G S i,
        x j * (Real.sqrt (y j) * Kz G a τ z y σ S i j l * Real.sqrt (y l)) * x l := by
  simp only [qForm, dotProduct, mulVec, Az, of_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  ring

/-- `bᵀ K_z b = (D_i + z y_i) q_{A_z}(x)`. -/
theorem colOf_quad_shift {a τ z : ℝ} (hτ : τ ^ 2 = 1) {y : V → ℝ} (hy : ∀ k, 0 ≤ y k)
    (hz : 0 ≤ z) (σ : Config V) {S : Finset V} {i : V} (x : nbhd G S i → ℝ) :
    SecA.colOf (precSub G a τ y σ S i x) i ⬝ᵥ
        (Kz G a τ z y σ S i *ᵥ SecA.colOf (precSub G a τ y σ S i x) i) =
      (diagD G a y S i + z * y i) * qForm (Az G a τ z y σ S i) x := by
  rw [colOf_precSub_quad_gen G hτ hy σ x, qForm_Az]
  have hD := (diagD_add_pos G a hy S i hz).ne'
  set D' := diagD G a y S i + z * y i
  rw [← mul_assoc, mul_div_assoc', mul_div_cancel_left₀ _ hD]

/-- The `k`-th entry of `u = K_z b`: `u_k = τ a √y_i Σ_{j ∈ J} K_{z,kj} √y_j x_j`. -/
theorem Kz_mulVec_colOf (a τ z : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) (i : V)
    (x : nbhd G S i → ℝ) (k : V) :
    (Kz G a τ z y σ S i *ᵥ SecA.colOf (precSub G a τ y σ S i x) i) k =
      τ * a * Real.sqrt (y i) *
        ∑ j : nbhd G S i, Kz G a τ z y σ S i k j * (Real.sqrt (y j) * x j) := by
  rw [colOf_precSub]
  simp only [mulVec, dotProduct]
  have e : ∀ w, Kz G a τ z y σ S i k w * (τ * a * Real.sqrt (y i) *
      (Real.sqrt (y w) * extStar G x w)) =
      extStar G x w * (τ * a * Real.sqrt (y i) * (Kz G a τ z y σ S i k w * Real.sqrt (y w))) :=
    fun w => by ring
  simp only [e]
  rw [sum_extStar G x, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **Star form (R1).** For `q_{A_z}(x) < 1` (core `≻ 0`, `z ≥ 0`): `P̃(x) + zY ≻ 0` and the
physical inverse diagonals, multiplied by `(D_i + z y_i)(1 - q_{A_z}(x))`, are explicit
quadratics in `x`. -/
theorem star_diag {a τ z : ℝ} (hτ : τ ^ 2 = 1) {y : V → ℝ} (hy : ∀ k, 0 ≤ y k) (hz : 0 ≤ z)
    (σ : Config V) {S : Finset V} {i : V} (hi : i ∈ S) (hM : (precCore G a τ y σ S i).PosDef)
    (x : nbhd G S i → ℝ) (hx : qForm (Az G a τ z y σ S i) x < 1) (k : V) :
    diagSub G a τ z y σ S i x k *
        ((diagD G a y S i + z * y i) * (1 - qForm (Az G a τ z y σ S i) x)) =
      if k = i then y i else
        y k * (Kz G a τ z y σ S i k k *
            ((diagD G a y S i + z * y i) * (1 - qForm (Az G a τ z y σ S i) x)) +
          a ^ 2 * y i * (∑ j : nbhd G S i, Kz G a τ z y σ S i k j * (Real.sqrt (y j) * x j)) ^ 2) := by
  set Q := precSub G a τ y σ S i x + z • srcDiag y S with hQdef
  have hDz := diagD_add_pos G a hy S i hz
  have hQh : Q.IsHermitian :=
    (precSub_isHermitian G a τ y σ S i x).add (posSemidef_smul_srcDiag hy S hz).isHermitian
  have hC : (SecA.coreOf Q i).PosDef := by
    rw [hQdef, coreOf_precSub_shift]
    exact hM.add_posSemidef (posSemidef_smul_srcDiag hy (S.erase i) hz)
  have hroot : Q i i = diagD G a y S i + z * y i := precSub_shift_apply_root G hi x
  have hquad : SecA.colOf Q i ⬝ᵥ ((SecA.coreOf Q i)⁻¹ *ᵥ SecA.colOf Q i) =
      (diagD G a y S i + z * y i) * qForm (Az G a τ z y σ S i) x := by
    rw [hQdef, colOf_precSub_shift, coreOf_precSub_shift]
    exact colOf_quad_shift G hτ hy hz σ x
  have hpos : 0 < Q i i - SecA.colOf Q i ⬝ᵥ ((SecA.coreOf Q i)⁻¹ *ᵥ SecA.colOf Q i) := by
    rw [hroot, hquad]
    nlinarith
  have hQ : Q.PosDef := (ins_generic hQh hC).1.2 hpos
  obtain ⟨hd, -, hij⟩ := SecA.schur_of_posDef hQ hC
  rw [hroot, hquad] at hd
  have hT : (diagD G a y S i + z * y i) * (1 - qForm (Az G a τ z y σ S i) x) =
      diagD G a y S i + z * y i - (diagD G a y S i + z * y i) * qForm (Az G a τ z y σ S i) x := by
    ring
  have hdiag : diagSub G a τ z y σ S i x k = y k * Q⁻¹ k k := rfl
  rw [hdiag, hT]
  by_cases hk : k = i
  · subst hk
    simp only [↓reduceIte]
    rw [mul_assoc, hd, mul_one]
  · rw [if_neg hk, hij k k hk hk]
    have hKz : (SecA.coreOf Q i)⁻¹ = Kz G a τ z y σ S i := by
      rw [hQdef, coreOf_precSub_shift]; rfl
    have hu : ((SecA.coreOf Q i)⁻¹ *ᵥ SecA.colOf Q i) k =
        τ * a * Real.sqrt (y i) *
          ∑ j : nbhd G S i, Kz G a τ z y σ S i k j * (Real.sqrt (y j) * x j) := by
      rw [hKz, hQdef, colOf_precSub_shift]
      exact Kz_mulVec_colOf G a τ z y σ S i x k
    rw [hu, hKz]
    have hsq : (τ * a * Real.sqrt (y i)) ^ 2 = a ^ 2 * y i := by
      rw [mul_pow, mul_pow, hτ, Real.sq_sqrt (hy i), one_mul]
    set T := diagD G a y S i + z * y i -
      (diagD G a y S i + z * y i) * qForm (Az G a τ z y σ S i) x
    set g := Q⁻¹ i i
    set s := ∑ j : nbhd G S i, Kz G a τ z y σ S i k j * (Real.sqrt (y j) * x j)
    have : y k * (Kz G a τ z y σ S i k k + g * (τ * a * Real.sqrt (y i) * s) *
        (τ * a * Real.sqrt (y i) * s)) * T =
        y k * (Kz G a τ z y σ S i k k * T + (g * T) * ((τ * a * Real.sqrt (y i)) ^ 2 * s ^ 2)) := by
      ring
    rw [this, hd, one_mul, hsq]

/-- At `z = 0`, `A_0` is the root matrix. -/
theorem Az_zero (a τ : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) (i : V) :
    Az G a τ 0 y σ S i = rootMat G a τ y σ S i := by
  ext j l
  simp [Az, rootMat, coreGreen, Kz]

/-- `A_z = (D_i/(D_i + z y_i)) M_z` with `M_z = SecC.shiftM` (`a² y_i/D_i` times the shifted core
inverse). -/
theorem Az_eq_smul_shiftM {a : ℝ} (τ z : ℝ) {y : V → ℝ} (hy : ∀ k, 0 ≤ y k) (hz : 0 ≤ z)
    (σ : Config V) (S : Finset V) (i : V) :
    Az G a τ z y σ S i = (diagD G a y S i / (diagD G a y S i + z * y i)) •
      shiftM G a τ z y σ S i := by
  have hD : 0 < diagD G a y S i := by
    have := diagD_add_pos G a hy S i (le_refl 0)
    simpa using this
  have hDz := diagD_add_pos G a hy S i hz
  ext j l
  simp only [Az, shiftM, shiftY, coreShift, Kz, Matrix.smul_apply, of_apply, smul_eq_mul]
  field_simp

/-! ### Comparisons `K_z ⪯ K_0`, `A_z ⪯ A` -/

/-- The padded weighted star vector `b = Y^{1/2} x̄` on `V`. -/
noncomputable def bv (y : V → ℝ) {S : Finset V} {i : V} (x : nbhd G S i → ℝ) : V → ℝ :=
  fun w => Real.sqrt (y w) * extStar G x w

theorem dsum_eq_dot (y : V → ℝ) {S : Finset V} {i : V} (x : nbhd G S i → ℝ)
    (C : Matrix V V ℝ) :
    ∑ j : nbhd G S i, ∑ l : nbhd G S i, x j * (Real.sqrt (y j) * C j l * Real.sqrt (y l)) * x l =
      bv G y x ⬝ᵥ (C *ᵥ bv G y x) := by
  simp only [bv, dotProduct, mulVec]
  have e1 : ∀ w, Real.sqrt (y w) * extStar G x w *
      ∑ w', C w w' * (Real.sqrt (y w') * extStar G x w') =
      extStar G x w * ∑ w', extStar G x w' * (Real.sqrt (y w) * C w w' * Real.sqrt (y w')) := by
    intro w
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun w' _ => by ring
  simp only [e1]
  rw [sum_extStar G x]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sum_extStar G x, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by ring

theorem qForm_Az_dot (a τ z : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) (i : V)
    (x : nbhd G S i → ℝ) :
    qForm (Az G a τ z y σ S i) x = a ^ 2 * y i / (diagD G a y S i + z * y i) *
      (bv G y x ⬝ᵥ (Kz G a τ z y σ S i *ᵥ bv G y x)) := by
  rw [qForm_Az, dsum_eq_dot]

theorem Kz_zero (a τ : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) (i : V) :
    Kz G a τ 0 y σ S i = (precCore G a τ y σ S i)⁻¹ := by
  simp [Kz]

theorem qForm_rootMat_dot (a τ : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) (i : V)
    (x : nbhd G S i → ℝ) :
    qForm (rootMat G a τ y σ S i) x = a ^ 2 * y i / diagD G a y S i *
      (bv G y x ⬝ᵥ ((precCore G a τ y σ S i)⁻¹ *ᵥ bv G y x)) := by
  rw [← Az_zero, qForm_Az_dot, Kz_zero, zero_mul, add_zero]

theorem Kz_posDef {a τ z : ℝ} {y : V → ℝ} (hy : ∀ k, 0 ≤ y k) (hz : 0 ≤ z) {σ : Config V}
    {S : Finset V} {i : V} (hM : (precCore G a τ y σ S i).PosDef) :
    (Kz G a τ z y σ S i).PosDef :=
  (hM.add_posSemidef (posSemidef_smul_srcDiag hy (S.erase i) hz)).inv

/-- `bᵀ K_z b ≤ bᵀ K_0 b` for `z ≥ 0`. -/
theorem dot_Kz_le {a τ z : ℝ} {y : V → ℝ} (hy : ∀ k, 0 ≤ y k) (hz : 0 ≤ z) {σ : Config V}
    {S : Finset V} {i : V} (hM : (precCore G a τ y σ S i).PosDef) (b : V → ℝ) :
    b ⬝ᵥ (Kz G a τ z y σ S i *ᵥ b) ≤ b ⬝ᵥ ((precCore G a τ y σ S i)⁻¹ *ᵥ b) := by
  have hD := SecA.srcDiag_posSemidef hy (S.erase i)
  have h := SecA.quad_inv_sub_inv_add_ge hM hD hz b
  have h0 : 0 ≤ ((precCore G a τ y σ S i + z • srcDiag y (S.erase i))⁻¹ *ᵥ b) ⬝ᵥ
      (srcDiag y (S.erase i) *ᵥ
        ((precCore G a τ y σ S i + z • srcDiag y (S.erase i))⁻¹ *ᵥ b)) := by
    have := hD.dotProduct_mulVec_nonneg
      ((precCore G a τ y σ S i + z • srcDiag y (S.erase i))⁻¹ *ᵥ b)
    simpa using this
  have := mul_nonneg hz h0
  unfold Kz
  linarith

theorem Kz_diag_le {a τ z : ℝ} {y : V → ℝ} (hy : ∀ k, 0 ≤ y k) (hz : 0 ≤ z) {σ : Config V}
    {S : Finset V} {i : V} (hM : (precCore G a τ y σ S i).PosDef) (k : V) :
    Kz G a τ z y σ S i k k ≤ (precCore G a τ y σ S i)⁻¹ k k := by
  have h := dot_Kz_le G hy hz hM (Pi.single k 1)
  simpa [dotProduct, mulVec, Pi.single_apply] using h

/-- `q_{A_z} ≤ (D_i/(D_i + z y_i)) q_A`. -/
theorem qForm_Az_le {a τ z : ℝ} {y : V → ℝ} (hy : ∀ k, 0 ≤ y k) (hz : 0 ≤ z) {σ : Config V}
    {S : Finset V} {i : V} (hM : (precCore G a τ y σ S i).PosDef) (x : nbhd G S i → ℝ) :
    qForm (Az G a τ z y σ S i) x ≤
      diagD G a y S i / (diagD G a y S i + z * y i) * qForm (rootMat G a τ y σ S i) x := by
  have hD : 0 < diagD G a y S i := by simpa using diagD_add_pos G a hy S i (le_refl 0)
  have hDz := diagD_add_pos G a hy S i hz
  rw [qForm_Az_dot, qForm_rootMat_dot]
  have h := dot_Kz_le G hy hz hM (bv G y x)
  have hc : 0 ≤ a ^ 2 * y i / (diagD G a y S i + z * y i) :=
    div_nonneg (mul_nonneg (sq_nonneg a) (hy i)) hDz.le
  calc a ^ 2 * y i / (diagD G a y S i + z * y i) *
        (bv G y x ⬝ᵥ (Kz G a τ z y σ S i *ᵥ bv G y x))
      ≤ a ^ 2 * y i / (diagD G a y S i + z * y i) *
        (bv G y x ⬝ᵥ ((precCore G a τ y σ S i)⁻¹ *ᵥ bv G y x)) :=
        mul_le_mul_of_nonneg_left h hc
    _ = _ := by field_simp

theorem Az_posSemidef {a τ z : ℝ} {y : V → ℝ} (hy : ∀ k, 0 ≤ y k) (hz : 0 ≤ z) {σ : Config V}
    {S : Finset V} {i : V} (hM : (precCore G a τ y σ S i).PosDef) :
    (Az G a τ z y σ S i).PosSemidef := by
  rcases hz.eq_or_lt with h0 | hpos
  · subst h0
    rw [Az_zero]
    exact SecA.rootMat_posSemidef G hy hM
  · rw [Az_eq_smul_shiftM G τ z hy hz]
    have hD : 0 < diagD G a y S i := by simpa using diagD_add_pos G a hy S i (le_refl 0)
    exact (SecC.shift_branch G hy le_rfl hpos hM).2.1.smul
      (div_nonneg hD.le (diagD_add_pos G a hy S i hz).le)

theorem qForm_Az_le_root {a τ z : ℝ} {y : V → ℝ} (hy : ∀ k, 0 ≤ y k) (hz : 0 ≤ z)
    {σ : Config V} {S : Finset V} {i : V} (hM : (precCore G a τ y σ S i).PosDef)
    (x : nbhd G S i → ℝ) :
    qForm (Az G a τ z y σ S i) x ≤ qForm (rootMat G a τ y σ S i) x := by
  have hD : 0 < diagD G a y S i := by simpa using diagD_add_pos G a hy S i (le_refl 0)
  have hDz := diagD_add_pos G a hy S i hz
  have h := qForm_Az_le G hy hz hM x
  have hq := qForm_nonneg (SecA.rootMat_posSemidef G hy hM) x
  have hle : diagD G a y S i / (diagD G a y S i + z * y i) ≤ 1 :=
    (div_le_one hDz).2 (by nlinarith [hy i])
  nlinarith

/-! ### The per-factor star identity -/

/-- The core value `c_t`: `y_i/(D_i + z y_i)` at `k = i`, `y_k (K_z)_kk` otherwise. -/
noncomputable def cVal (a τ z : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) (i k : V) : ℝ :=
  if k = i then y i / (diagD G a y S i + z * y i) else y k * Kz G a τ z y σ S i k k

/-- The row `r_j = (K_z)_kj √y_j` (`j ∈ J`). -/
noncomputable def rVec (a τ z : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) (i k : V) :
    nbhd G S i → ℝ :=
  fun j => Kz G a τ z y σ S i k j * Real.sqrt (y j)

/-- The coefficient `κ = a² y_i/((D_i + z y_i)(K_z)_kk)`. -/
noncomputable def kap (a τ z : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) (i k : V) : ℝ :=
  a ^ 2 * y i / ((diagD G a y S i + z * y i) * Kz G a τ z y σ S i k k)

/-- The quadratic matrix of `ñ_t = 1 + q_{nMat}`: `0` at `k = i`, `-A_z + κ r rᵀ` otherwise. -/
noncomputable def nMat (a τ z : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) (i k : V) :
    Matrix (nbhd G S i) (nbhd G S i) ℝ :=
  if k = i then 0 else
    -Az G a τ z y σ S i + kap G a τ z y σ S i k • vecMulVec (rVec G a τ z y σ S i k)
      (rVec G a τ z y σ S i k)

omit [DecidableEq V] in
theorem qForm_vecMulVec_self {ι : Type*} [Fintype ι] (r x : ι → ℝ) :
    qForm (vecMulVec r r) x = (∑ j, r j * x j) ^ 2 := by
  simp only [qForm, dotProduct, mulVec, vecMulVec_apply]
  rw [sq, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by ring

omit [DecidableEq V] in
theorem qForm_neg_add_smul {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℝ) (c : ℝ) (x : ι → ℝ) :
    qForm (-A + c • B) x = -qForm A x + c * qForm B x := by
  simp only [qForm, add_mulVec, neg_mulVec, smul_mulVec, dotProduct_add, dotProduct_neg,
    dotProduct_smul, smul_eq_mul]

theorem rVec_dot (a τ z : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) (i k : V)
    (x : nbhd G S i → ℝ) :
    ∑ j, rVec G a τ z y σ S i k j * x j = (Kz G a τ z y σ S i *ᵥ bv G y x) k := by
  simp only [rVec, mulVec, dotProduct, bv]
  have e : ∀ w, Kz G a τ z y σ S i k w * (Real.sqrt (y w) * extStar G x w) =
      extStar G x w * (Kz G a τ z y σ S i k w * Real.sqrt (y w)) := fun w => by ring
  simp only [e]
  rw [sum_extStar G x]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem qForm_nMat (a τ z : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) {i k : V} (hk : k ≠ i)
    (x : nbhd G S i → ℝ) :
    qForm (nMat G a τ z y σ S i k) x = -qForm (Az G a τ z y σ S i) x +
      kap G a τ z y σ S i k * ((Kz G a τ z y σ S i *ᵥ bv G y x) k) ^ 2 := by
  rw [nMat, if_neg hk, qForm_neg_add_smul, qForm_vecMulVec_self, rVec_dot]

/-- **Per-factor star identity.** On `{q_{A_z} < 1}`:
`y_k ((P̃(x) + zY)⁻¹)_kk · (1 - q_{A_z}(x)) = c_t · (1 + q_{nMat}(x))`. -/
theorem star_factor {a τ z : ℝ} (hτ : τ ^ 2 = 1) {y : V → ℝ} (hy : ∀ k, 0 ≤ y k) (hz : 0 ≤ z)
    (σ : Config V) {S : Finset V} {i : V} (hi : i ∈ S) (hM : (precCore G a τ y σ S i).PosDef)
    (x : nbhd G S i → ℝ) (hx : qForm (Az G a τ z y σ S i) x < 1) (k : V) :
    diagSub G a τ z y σ S i x k * (1 - qForm (Az G a τ z y σ S i) x) =
      cVal G a τ z y σ S i k * quadFn 1 0 (nMat G a τ z y σ S i k) x := by
  have hDz := diagD_add_pos G a hy S i hz
  have h := star_diag G hτ hy hz σ hi hM x hx k
  have hs : ∑ j : nbhd G S i, Kz G a τ z y σ S i k j * (Real.sqrt (y j) * x j) =
      (Kz G a τ z y σ S i *ᵥ bv G y x) k := by
    rw [← rVec_dot]
    exact Finset.sum_congr rfl fun j _ => by simp only [rVec]; ring
  rw [hs] at h
  simp only [quadFn, zero_dotProduct, add_zero]
  by_cases hk : k = i
  · subst hk
    rw [if_pos rfl] at h
    have hq0 : qForm (0 : Matrix (nbhd G S k) (nbhd G S k) ℝ) x = 0 := by simp [qForm]
    simp only [cVal, nMat, ↓reduceIte, hq0, add_zero, mul_one]
    rw [eq_div_iff hDz.ne']
    linear_combination h
  · rw [if_neg hk] at h
    have hK : 0 < Kz G a τ z y σ S i k k :=
      (Kz_posDef G hy hz hM).diag_pos
    simp only [cVal, if_neg hk]
    rw [qForm_nMat G a τ z y σ S hk x]
    have hkap : kap G a τ z y σ S i k * Kz G a τ z y σ S i k k * (diagD G a y S i + z * y i) =
        a ^ 2 * y i := by
      simp only [kap]
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_iff (mul_ne_zero hDz.ne' hK.ne')]
      ring
    set q := qForm (Az G a τ z y σ S i) x
    set u := (Kz G a τ z y σ S i *ᵥ bv G y x) k
    set D' := diagD G a y S i + z * y i
    have h2 : (diagSub G a τ z y σ S i x k * (1 - q)) * D' =
        (y k * Kz G a τ z y σ S i k k * (1 + (-q + kap G a τ z y σ S i k * u ^ 2))) * D' := by
      have e : y k * Kz G a τ z y σ S i k k * (1 + (-q + kap G a τ z y σ S i k * u ^ 2)) * D' =
          y k * (Kz G a τ z y σ S i k k * (D' * (1 - q)) +
            (kap G a τ z y σ S i k * Kz G a τ z y σ S i k k * D') * u ^ 2) := by ring
      rw [e, hkap, ← h]
      ring
    exact mul_right_cancel₀ hDz.ne' h2

/-- `0 ≤ q_{-nMat} ≤ q_{A_z}`: `ñ_t ∈ [1 - q_{A_z}, 1]`. -/
theorem qForm_neg_nMat_bounds {a τ z : ℝ} {y : V → ℝ} (hy : ∀ k, 0 ≤ y k) (hz : 0 ≤ z)
    {σ : Config V} {S : Finset V} {i : V} (hM : (precCore G a τ y σ S i).PosDef) (k : V)
    (x : nbhd G S i → ℝ) :
    0 ≤ qForm (-nMat G a τ z y σ S i k) x ∧
      qForm (-nMat G a τ z y σ S i k) x ≤ qForm (Az G a τ z y σ S i) x := by
  rw [SecA.CA.qForm_neg]
  have hA := qForm_nonneg (Az_posSemidef G hy hz hM) x
  by_cases hk : k = i
  · simp only [nMat, if_pos hk, qForm, zero_mulVec, dotProduct_zero, neg_zero]
    exact ⟨le_rfl, hA⟩
  · rw [qForm_nMat G a τ z y σ S hk x]
    have hDz := diagD_add_pos G a hy S i hz
    have hKpd := Kz_posDef G hy hz hM
    have hK : 0 < Kz G a τ z y σ S i k k := hKpd.diag_pos
    have hkap : 0 ≤ kap G a τ z y σ S i k :=
      div_nonneg (mul_nonneg (sq_nonneg a) (hy i)) (mul_pos hDz hK).le
    have hcs := SecA.CA.mulVec_apply_sq_le' hKpd.posSemidef (bv G y x) k
    have hq : qForm (Kz G a τ z y σ S i) (bv G y x) =
        bv G y x ⬝ᵥ (Kz G a τ z y σ S i *ᵥ bv G y x) := rfl
    rw [hq] at hcs
    have hu := sq_nonneg ((Kz G a τ z y σ S i *ᵥ bv G y x) k)
    refine ⟨?_, by nlinarith⟩
    -- `κ u² ≤ q_{A_z}`
    have hkey : kap G a τ z y σ S i k * ((Kz G a τ z y σ S i *ᵥ bv G y x) k) ^ 2 ≤
        qForm (Az G a τ z y σ S i) x := by
      rw [qForm_Az_dot]
      simp only [kap]
      rw [div_mul_eq_mul_div, div_le_iff₀ (mul_pos hDz hK)]
      have hc : 0 ≤ a ^ 2 * y i := mul_nonneg (sq_nonneg a) (hy i)
      have := mul_le_mul_of_nonneg_left hcs hc
      have e : a ^ 2 * y i / (diagD G a y S i + z * y i) *
          (bv G y x ⬝ᵥ (Kz G a τ z y σ S i *ᵥ bv G y x)) *
            ((diagD G a y S i + z * y i) * Kz G a τ z y σ S i k k) =
          a ^ 2 * y i * (Kz G a τ z y σ S i k k *
            (bv G y x ⬝ᵥ (Kz G a τ z y σ S i *ᵥ bv G y x))) := by
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_iff hDz.ne']
        ring
      rw [e]
      exact this
    linarith

theorem neg_nMat_posSemidef {a τ z : ℝ} {y : V → ℝ} (hy : ∀ k, 0 ≤ y k) (hz : 0 ≤ z)
    {σ : Config V} {S : Finset V} {i : V} (hM : (precCore G a τ y σ S i).PosDef) (k : V) :
    (-nMat G a τ z y σ S i k).PosSemidef := by
  have hAs := (Az_posSemidef G hy hz hM).isHermitian
  have hKs := (Kz_posDef G hy hz hM).isHermitian
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · by_cases hk : k = i
    · simp only [nMat, if_pos hk, neg_zero]
      exact isHermitian_zero
    · simp only [nMat, if_neg hk]
      refine IsHermitian.neg (IsHermitian.add hAs.neg ?_)
      ext j l
      simp only [conjTranspose_apply, Matrix.smul_apply, vecMulVec_apply, star_trivial,
        smul_eq_mul]
      ring
  · have := (qForm_neg_nMat_bounds G hy hz hM k x).1
    simpa [qForm] using this

end Star

end BiluLinial.Tight.SecB.WR
