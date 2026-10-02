/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecB.WTRemStar

/-!
# The kernel envelope `L ⪯ c_L Q⁺` (sub-node (R2) of TB.WT5r°)

For the admissible maps `T ∈ {T_dir, T_cav}` of (WT1) at the deleted vertex `i` and
`L = TᵀT`, with `B(x) = bᵀ K⁰₊ b` (`b = Y₊^{1/2} x̄`, `K⁰₊` the unshifted plus core inverse):
`q_L(x) ≤ c_L B(x)`, `c_L = (1/h²)(2/d)(1/h + 4 Σ_{k ∈ N} ((K⁰₊)_kk)²)` (`env_qForm`).

Ingredients (generic, `shift_energy`): for `φ = (P + zY)⁻¹ c`, `z Σ_{K} (√y_j φ_j)² ≤ cᵀφ`; hence
the shifted physical core `C_z` satisfies `‖C_z ω‖² ≤ z⁻²‖ω‖²` (`ω` supported on `S - i`) and
`‖C_z x̄‖² ≤ z⁻¹ bᵀK_z b`; and `(C_z)_kk² x̄_k² ≤ 4 (K⁰_kk)² B` (`y ≤ 2`, `P_kk ≤ 2`).

Check: `x = 0` gives `0 ≤ 0`; `N ∩ (S - i) = ∅` makes `T = 0`.
-/

@[expose] public section

namespace BiluLinial.Tight.SecB.WR

open Matrix

section Gen

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem shift_energy {a τ z : ℝ} {y : V → ℝ} (hy : ∀ k, 0 ≤ y k) (hz : 0 ≤ z) {σ : Config V}
    {S : Finset V} {i : V} (hM : (precCore G a τ y σ S i).PosDef) (c : V → ℝ) :
    z * ∑ j ∈ S.erase i, (Real.sqrt (y j) * (Kz G a τ z y σ S i *ᵥ c) j) ^ 2 ≤
      c ⬝ᵥ (Kz G a τ z y σ S i *ᵥ c) := by
  set P := precCore G a τ y σ S i
  set Y := srcDiag y (S.erase i)
  have hQ : (P + z • Y).PosDef :=
    hM.add_posSemidef (posSemidef_smul_srcDiag hy (S.erase i) hz)
  set φ := Kz G a τ z y σ S i *ᵥ c with hφ
  have hMφ : (P + z • Y) *ᵥ φ = c := by
    have hu : IsUnit (P + z • Y).det := (isUnit_iff_isUnit_det _).mp hQ.isUnit
    rw [hφ, Kz, mulVec_mulVec, mul_nonsing_inv _ hu, one_mulVec]
  have hP : 0 ≤ φ ⬝ᵥ (P *ᵥ φ) := by simpa using hM.posSemidef.dotProduct_mulVec_nonneg φ
  have hY : φ ⬝ᵥ (Y *ᵥ φ) = ∑ j ∈ S.erase i, (Real.sqrt (y j) * φ j) ^ 2 := by
    simp only [Y, srcDiag, mulVec_diagonal, dotProduct]
    have e : ∀ j, φ j * ((if j ∈ S.erase i then y j else 0) * φ j) =
        if j ∈ S.erase i then (Real.sqrt (y j) * φ j) ^ 2 else 0 := by
      intro j
      by_cases hj : j ∈ S.erase i
      · rw [if_pos hj, if_pos hj, mul_pow, Real.sq_sqrt (hy j)]
        ring
      · rw [if_neg hj, if_neg hj]
        ring
    simp only [e]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  have hsplit : φ ⬝ᵥ ((P + z • Y) *ᵥ φ) = φ ⬝ᵥ (P *ᵥ φ) + z * (φ ⬝ᵥ (Y *ᵥ φ)) := by
    rw [add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul]
  rw [hMφ, hY] at hsplit
  rw [dotProduct_comm]
  linarith

theorem coreShift_row (a τ z : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) (i j : V)
    (ω : V → ℝ) :
    ∑ w, coreShift G a τ z y σ S i j w * ω w =
      Real.sqrt (y j) * (Kz G a τ z y σ S i *ᵥ fun w => Real.sqrt (y w) * ω w) j := by
  simp only [coreShift, Kz, mulVec, dotProduct, Finset.mul_sum]
  exact Finset.sum_congr rfl fun w _ => by ring

/-- `‖C_z ω‖²_{S-i} ≤ z⁻² ‖ω‖²` for `ω` supported on `S - i`. -/
theorem shift_row_sq {a τ z : ℝ} {y : V → ℝ} (hy : ∀ k, 0 ≤ y k) (hz : 0 < z) {σ : Config V}
    {S : Finset V} {i : V} (hM : (precCore G a τ y σ S i).PosDef) (ω : V → ℝ)
    (hω : ∀ w, w ∉ S.erase i → ω w = 0) :
    ∑ j ∈ S.erase i, (∑ w, coreShift G a τ z y σ S i j w * ω w) ^ 2 ≤
      (1 / z ^ 2) * ∑ w, ω w ^ 2 := by
  simp only [coreShift_row]
  set c : V → ℝ := fun w => Real.sqrt (y w) * ω w
  set φ := Kz G a τ z y σ S i *ᵥ c
  set Vs := ∑ j ∈ S.erase i, (Real.sqrt (y j) * φ j) ^ 2
  have h1 : z * Vs ≤ c ⬝ᵥ φ := shift_energy G hy hz.le hM c
  have hcφ : c ⬝ᵥ φ = ∑ w ∈ S.erase i, ω w * (Real.sqrt (y w) * φ w) := by
    simp only [dotProduct, c]
    rw [← Finset.sum_subset (Finset.subset_univ (S.erase i)) (fun w _ hw => by simp [hω w hw])]
    exact Finset.sum_congr rfl fun w _ => by ring
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq (S.erase i) ω (fun w => Real.sqrt (y w) * φ w)
  have h3 : ∑ w ∈ S.erase i, ω w ^ 2 ≤ ∑ w, ω w ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => sq_nonneg _
  have hV : 0 ≤ Vs := Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [hcφ] at h1
  set X := ∑ w ∈ S.erase i, ω w * (Real.sqrt (y w) * φ w)
  set W := ∑ w, ω w ^ 2
  have hW : 0 ≤ W := Finset.sum_nonneg fun _ _ => sq_nonneg _
  rcases hV.eq_or_lt with h0 | hpos
  · rw [← h0]
    positivity
  · have hsq : (z * Vs) ^ 2 ≤ W * Vs :=
      le_trans (pow_le_pow_left₀ (mul_nonneg hz.le hV) h1 2)
        (h2.trans (mul_le_mul_of_nonneg_right h3 hV))
    have h4 : z ^ 2 * Vs ≤ W := by
      have : z ^ 2 * Vs * Vs ≤ W * Vs := by nlinarith
      exact le_of_mul_le_mul_right this hpos
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
    linarith

/-- `‖C_z x̄‖²_{S-i} ≤ z⁻¹ bᵀ K_z b`. -/
theorem shift_row_sq_bv {a τ z : ℝ} {y : V → ℝ} (hy : ∀ k, 0 ≤ y k) (hz : 0 < z)
    {σ : Config V} {S : Finset V} {i : V} (hM : (precCore G a τ y σ S i).PosDef)
    (x : nbhd G S i → ℝ) :
    ∑ j ∈ S.erase i, (∑ w, coreShift G a τ z y σ S i j w * extStar G x w) ^ 2 ≤
      (1 / z) * (bv G y x ⬝ᵥ (Kz G a τ z y σ S i *ᵥ bv G y x)) := by
  simp only [coreShift_row]
  have h := shift_energy G hy hz.le hM (bv G y x)
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hz]
  have e : (fun w => Real.sqrt (y w) * extStar G x w) = bv G y x := rfl
  rw [e]
  linarith

theorem bv_sq_le {a τ : ℝ} {y : V → ℝ} {σ : Config V} {S : Finset V} {i : V}
    (hM : (precCore G a τ y σ S i).PosDef) (x : nbhd G S i → ℝ) (k : V) :
    bv G y x k ^ 2 ≤ precCore G a τ y σ S i k k *
      (bv G y x ⬝ᵥ ((precCore G a τ y σ S i)⁻¹ *ᵥ bv G y x)) := by
  set P := precCore G a τ y σ S i
  have hu : IsUnit P.det := (isUnit_iff_isUnit_det _).mp hM.isUnit
  have h := SecA.CA.mulVec_apply_sq_le' hM.posSemidef (P⁻¹ *ᵥ bv G y x) k
  have e1 : P *ᵥ (P⁻¹ *ᵥ bv G y x) = bv G y x := by
    rw [mulVec_mulVec, mul_nonsing_inv _ hu, one_mulVec]
  have e2 : qForm P (P⁻¹ *ᵥ bv G y x) = bv G y x ⬝ᵥ (P⁻¹ *ᵥ bv G y x) := by
    rw [qForm, e1, dotProduct_comm]
  rw [e1, e2] at h
  exact h

/-- `(C_z)_kk² x̄_k² ≤ 4 (K⁰_kk)² B` (`y ≤ 2`, `P_kk ≤ 2`). -/
theorem coreShift_diag_sq {a τ z : ℝ} {y : V → ℝ} (hy : ∀ k, 0 ≤ y k) (hy2 : ∀ k, y k ≤ 2)
    (hz : 0 ≤ z) {σ : Config V} {S : Finset V} {i : V} (hM : (precCore G a τ y σ S i).PosDef)
    (hP2 : ∀ k, precCore G a τ y σ S i k k ≤ 2) (x : nbhd G S i → ℝ) (k : V) :
    (coreShift G a τ z y σ S i k k * extStar G x k) ^ 2 ≤
      4 * ((precCore G a τ y σ S i)⁻¹ k k) ^ 2 *
        (bv G y x ⬝ᵥ ((precCore G a τ y σ S i)⁻¹ *ᵥ bv G y x)) := by
  have hK : 0 < Kz G a τ z y σ S i k k := (Kz_posDef G hy hz hM).diag_pos
  have hK0 := Kz_diag_le G hy hz hM k
  have hB := bv_sq_le G hM x k
  have hBnn : 0 ≤ bv G y x ⬝ᵥ ((precCore G a τ y σ S i)⁻¹ *ᵥ bv G y x) := by
    have := hM.inv.posSemidef.dotProduct_mulVec_nonneg (bv G y x)
    simpa using this
  have hcs : coreShift G a τ z y σ S i k k = y k * Kz G a τ z y σ S i k k := by
    simp only [coreShift, Kz]
    rw [mul_comm (Real.sqrt (y k)), mul_assoc, Real.mul_self_sqrt (hy k)]
    ring
  have hbk : bv G y x k ^ 2 = y k * extStar G x k ^ 2 := by
    simp only [bv]
    rw [mul_pow, Real.sq_sqrt (hy k)]
  rw [hcs]
  have hKsq : Kz G a τ z y σ S i k k ^ 2 ≤ ((precCore G a τ y σ S i)⁻¹ k k) ^ 2 :=
    pow_le_pow_left₀ hK.le hK0 2
  have e : (y k * Kz G a τ z y σ S i k k * extStar G x k) ^ 2 =
      y k * Kz G a τ z y σ S i k k ^ 2 * bv G y x k ^ 2 := by
    rw [hbk]
    ring
  rw [e]
  have hyk := hy k
  have hy2k := hy2 k
  have hP := hP2 k
  have h1 : y k * Kz G a τ z y σ S i k k ^ 2 ≤ 2 * ((precCore G a τ y σ S i)⁻¹ k k) ^ 2 := by
    nlinarith [sq_nonneg (Kz G a τ z y σ S i k k)]
  have h2 : bv G y x k ^ 2 ≤ 2 * (bv G y x ⬝ᵥ ((precCore G a τ y σ S i)⁻¹ *ᵥ bv G y x)) :=
    hB.trans (mul_le_mul_of_nonneg_right hP hBnn)
  have h3 : 0 ≤ y k * Kz G a τ z y σ S i k k ^ 2 := by positivity
  calc y k * Kz G a τ z y σ S i k k ^ 2 * bv G y x k ^ 2
      ≤ (2 * ((precCore G a τ y σ S i)⁻¹ k k) ^ 2) *
          (2 * (bv G y x ⬝ᵥ ((precCore G a τ y σ S i)⁻¹ *ᵥ bv G y x))) :=
        mul_le_mul h1 h2 (sq_nonneg _) (by positivity)
    _ = _ := by ring

omit [Fintype V] in
theorem nbhd_subset_erase (S : Finset V) (i : V) : nbhd G S i ⊆ S.erase i := by
  intro w hw
  simp only [nbhd, Finset.mem_filter] at hw
  exact Finset.mem_erase.2 ⟨(G.ne_of_adj hw.2).symm, hw.1⟩

omit [Fintype V] in
theorem extStar_coe {S : Finset V} {i : V} (x : nbhd G S i → ℝ) (j : nbhd G S i) :
    extStar G x j = x j := by
  simp [extStar, j.2]

omit [Fintype V] in
theorem extStar_eq_zero {S : Finset V} {i : V} (x : nbhd G S i → ℝ) {w : V}
    (hw : w ∉ nbhd G S i) : extStar G x w = 0 := by
  simp [extStar, hw]

theorem sum_sq_extStar {S : Finset V} {i : V} (x : nbhd G S i → ℝ) :
    ∑ w, extStar G x w ^ 2 = ∑ j : nbhd G S i, x j ^ 2 := by
  have h := sum_extStar G x (extStar G x)
  simp only [extStar_coe] at h
  simp only [sq]
  exact h

/-- A subtype sum of nonnegative terms is at most the sum over `S - i`. -/
theorem sum_nbhd_le_erase {S : Finset V} {i : V} (f : V → ℝ) (hf : ∀ w, 0 ≤ f w) :
    ∑ j : nbhd G S i, f j ≤ ∑ j ∈ S.erase i, f j := by
  rw [Finset.sum_coe_sort (nbhd G S i) f]
  exact Finset.sum_le_sum_of_subset_of_nonneg (nbhd_subset_erase G S i) fun w _ _ => hf w

end Gen

/-! ### The envelope at a contact -/

section Contact

variable {d p : ℕ}

open Contact

/-- The sign of branch `e`. -/
abbrev tau (e : Bool) : ℝ := if e then 1 else -1

/-- `B(x) = bᵀ K⁰₊ b`. -/
noncomputable def Bq (ct : Contact.{u} d p) (σ : Config ct.V) (i : ct.V)
    (x : nbhd ct.G ct.S i → ℝ) : ℝ :=
  bv ct.G ct.yp x ⬝ᵥ ((precCore ct.G (aOf d p) 1 ct.yp σ ct.S i)⁻¹ *ᵥ bv ct.G ct.yp x)

/-- The envelope constant `c_L = (1/h²)(2/d)(1/h + 4 Σ_{k ∈ N} ((K⁰₊)_kk)²)`. -/
noncomputable def cL (ct : Contact.{u} d p) (h : ℝ) (σ : Config ct.V) (i : ct.V) : ℝ :=
  1 / h ^ 2 * (2 / d) *
    (1 / h + 4 * ∑ k ∈ ct.N, ((precCore ct.G (aOf d p) 1 ct.yp σ ct.S i)⁻¹ k k) ^ 2)

theorem qForm_transpose_mul {ι : Type*} [Fintype ι] (T : Matrix ι ι ℝ) (x : ι → ℝ) :
    qForm (Tᵀ * T) x = ∑ j, (T *ᵥ x) j ^ 2 := by
  rw [qForm, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose, dotProduct]
  exact Finset.sum_congr rfl fun j _ => (sq _).symm

theorem uvec_sq (ct : Contact.{u} d p) (hd : 0 < (d : ℝ)) (k : ct.V) :
    ct.uvec k ^ 2 ≤ 1 / d := by
  simp only [Contact.uvec]
  split_ifs
  · rw [div_pow, one_pow, Real.sq_sqrt hd.le]
  · rw [sq, zero_mul]
    positivity

theorem tDir_apply_mulVec (ct : Contact.{u} d p) (h : ℝ) (e : Bool) (i : ct.V)
    (σ : Config ct.V) (x : nbhd ct.G ct.S i → ℝ) (j : nbhd ct.G ct.S i) :
    (ct.tDir h e i σ *ᵥ x) j = ∑ w, ct.Cb h e σ i j w * extStar ct.G
      (fun l : nbhd ct.G ct.S i =>
        (if (l : ct.V) ∈ ct.N then ct.uvec l * ct.Cb h true σ i l l else 0) * x l) w := by
  simp only [mulVec, dotProduct, Contact.tDir, of_apply]
  have e1 : ∀ w, ct.Cb h e σ i j w * extStar ct.G
      (fun l : nbhd ct.G ct.S i =>
        (if (l : ct.V) ∈ ct.N then ct.uvec l * ct.Cb h true σ i l l else 0) * x l) w =
      extStar ct.G
      (fun l : nbhd ct.G ct.S i =>
        (if (l : ct.V) ∈ ct.N then ct.uvec l * ct.Cb h true σ i l l else 0) * x l) w *
        ct.Cb h e σ i j w := fun w => mul_comm _ _
  simp only [e1]
  rw [sum_extStar ct.G]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs <;> ring

theorem tCav_apply_mulVec (ct : Contact.{u} d p) (h : ℝ) (e : Bool) (i : ct.V)
    (σ : Config ct.V) (x : nbhd ct.G ct.S i → ℝ) (j : nbhd ct.G ct.S i) :
    (ct.tCav h e i σ *ᵥ x) j = ∑ w, ct.Cb h e σ i j w *
      (if w ∈ ct.N.erase i then ct.uvec w *
        (∑ w', ct.Cb h true σ i w w' * extStar ct.G x w' -
          ct.Cb h true σ i w w * extStar ct.G x w) else 0) := by
  simp only [mulVec, dotProduct, Contact.tCav, of_apply]
  -- erase as a filter, then swap the sums
  have e1 : ∀ l : nbhd ct.G ct.S i,
      (∑ k ∈ (ct.N.erase i).erase (l : ct.V),
        ct.Cb h e σ i j k * ct.uvec k * ct.Cb h true σ i k l) * x l =
      ∑ k ∈ ct.N.erase i, ct.Cb h e σ i j k * ct.uvec k *
        (if k = (l : ct.V) then 0 else ct.Cb h true σ i k l * x l) := by
    intro l
    rw [← Finset.filter_ne', Finset.sum_filter, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : k = (l : ct.V)
    · simp [hk]
    · simp only [hk, if_false, ne_eq, not_false_eq_true, if_true]
      ring
  simp only [e1]
  rw [Finset.sum_comm]
  have e2 : ∀ k : ct.V, ∑ l : nbhd ct.G ct.S i, ct.Cb h e σ i j k * ct.uvec k *
      (if k = (l : ct.V) then 0 else ct.Cb h true σ i k l * x l) =
      ct.Cb h e σ i j k * ct.uvec k *
        (∑ w', ct.Cb h true σ i k w' * extStar ct.G x w' -
          ct.Cb h true σ i k k * extStar ct.G x k) := by
    intro k
    rw [← Finset.mul_sum]
    congr 1
    have h1 : ∑ l : nbhd ct.G ct.S i, (if k = (l : ct.V) then 0 else ct.Cb h true σ i k l * x l) =
        ∑ w', extStar ct.G x w' * (if k = w' then 0 else ct.Cb h true σ i k w') := by
      rw [sum_extStar ct.G]
      exact Finset.sum_congr rfl fun l _ => by split_ifs <;> ring
    rw [h1]
    have h2 : ∀ w', extStar ct.G x w' * (if k = w' then 0 else ct.Cb h true σ i k w') =
        (if w' = k then 0 else ct.Cb h true σ i k w' * extStar ct.G x w') := by
      intro w'
      by_cases hw : w' = k
      · simp [hw]
      · simp [hw, Ne.symm hw, mul_comm]
    simp only [h2]
    rw [SecA.sum_ite_zero_eq_sub]
  simp only [e2]
  rw [← Finset.sum_subset (Finset.subset_univ (ct.N.erase i)) fun w _ hw => by simp [hw]]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [if_pos hk]
  ring

theorem Cb_true (ct : Contact.{u} d p) (h : ℝ) (σ : Config ct.V) (i j l : ct.V) :
    ct.Cb h true σ i j l = coreShift ct.G (aOf d p) 1 h ct.yp σ ct.S i j l := rfl

theorem N_subset (ct : Contact.{u} d p) : ct.N ⊆ ct.S := Finset.filter_subset _ _

theorem Bq_nonneg (ct : Contact.{u} d p) {σ : Config ct.V} {i : ct.V}
    (hMp : (precCore ct.G (aOf d p) 1 ct.yp σ ct.S i).PosDef) (x : nbhd ct.G ct.S i → ℝ) :
    0 ≤ Bq ct σ i x := by
  have := hMp.inv.posSemidef.dotProduct_mulVec_nonneg (bv ct.G ct.yp x)
  simpa [Bq] using this

/-- The `N`-restricted sum: `Σ_{l ∈ J} 1_{l ∈ N} g_l ≤ Σ_{k ∈ N} g_k` (`g ≥ 0`). -/
theorem sum_nbhd_ite_le (ct : Contact.{u} d p) (i : ct.V) (g : ct.V → ℝ) (hg : ∀ k, 0 ≤ g k) :
    ∑ l : nbhd ct.G ct.S i, (if (l : ct.V) ∈ ct.N then g l else 0) ≤ ∑ k ∈ ct.N, g k := by
  rw [Finset.sum_coe_sort (nbhd ct.G ct.S i) (fun l => if l ∈ ct.N then g l else 0),
    Finset.sum_ite_mem]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right fun k _ _ => hg k

/-- **Envelope (R2).** `q_L(x) ≤ c_L B(x)` for both admissible maps. -/
theorem env_qForm (ct : Contact.{u} d p) (hd : 0 < (d : ℝ)) {h : ℝ} (hh : 0 < h) (e dir : Bool)
    {i : ct.V} (σ : Config ct.V)
    (hMp : (precCore ct.G (aOf d p) 1 ct.yp σ ct.S i).PosDef)
    (hMe : (precCore ct.G (aOf d p) (tau e) (ct.ySrc e) σ ct.S i).PosDef)
    (hye : ∀ k, 0 ≤ ct.ySrc e k) (hyp : ∀ k, 0 ≤ ct.yp k) (hy2 : ∀ k, ct.yp k ≤ 2)
    (hP2 : ∀ k, precCore ct.G (aOf d p) 1 ct.yp σ ct.S i k k ≤ 2)
    (x : nbhd ct.G ct.S i → ℝ) :
    qForm (kerL ct h e dir i σ) x ≤ cL ct h σ i * Bq ct σ i x := by
  have hB0 := Bq_nonneg ct hMp x
  set B := Bq ct σ i x with hBdef
  set S4 := ∑ k ∈ ct.N, ((precCore ct.G (aOf d p) 1 ct.yp σ ct.S i)⁻¹ k k) ^ 2 with hS4
  have hS40 : 0 ≤ S4 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hdiag : ∀ k, (ct.Cb h true σ i k k * extStar ct.G x k) ^ 2 ≤
      4 * ((precCore ct.G (aOf d p) 1 ct.yp σ ct.S i)⁻¹ k k) ^ 2 * B := fun k => by
    rw [Cb_true]
    exact coreShift_diag_sq ct.G hyp hy2 hh.le hMp hP2 x k
  have hh2 : 0 < h ^ 2 := by positivity
  rw [kerL, qForm_transpose_mul]
  cases dir with
  | true =>
    simp only [Contact.tMap, if_true]
    simp only [tDir_apply_mulVec]
    set x' : nbhd ct.G ct.S i → ℝ := fun l =>
      (if (l : ct.V) ∈ ct.N then ct.uvec l * ct.Cb h true σ i l l else 0) * x l
    have hω : ∀ w, w ∉ ct.S.erase i → extStar ct.G x' w = 0 := fun w hw =>
      extStar_eq_zero ct.G x' fun hw' => hw (nbhd_subset_erase ct.G ct.S i hw')
    have h1 := sum_nbhd_le_erase ct.G (S := ct.S) (i := i)
      (fun j => (∑ w, ct.Cb h e σ i j w * extStar ct.G x' w) ^ 2) fun _ => sq_nonneg _
    have h2 : ∑ j ∈ ct.S.erase i, (∑ w, ct.Cb h e σ i j w * extStar ct.G x' w) ^ 2 ≤
        (1 / h ^ 2) * ∑ w, extStar ct.G x' w ^ 2 :=
      shift_row_sq ct.G hye hh hMe (extStar ct.G x') hω
    rw [sum_sq_extStar] at h2
    have h3 : ∑ l : nbhd ct.G ct.S i, x' l ^ 2 ≤
        ∑ k ∈ ct.N, 1 / d * (4 * ((precCore ct.G (aOf d p) 1 ct.yp σ ct.S i)⁻¹ k k) ^ 2 * B) := by
      refine le_trans (Finset.sum_le_sum fun l _ => ?_) (sum_nbhd_ite_le ct i _ fun k => by positivity)
      simp only [x']
      split_ifs with hl
      · have hu := uvec_sq ct hd l
        have hdl := hdiag l
        rw [extStar_coe] at hdl
        have e : (ct.uvec l * ct.Cb h true σ i l l * x l) ^ 2 =
            ct.uvec l ^ 2 * (ct.Cb h true σ i l l * x l) ^ 2 := by ring
        rw [e]
        exact mul_le_mul hu hdl (sq_nonneg _) (by positivity)
      · simp
    have h3' : ∑ k ∈ ct.N, 1 / (d : ℝ) *
        (4 * ((precCore ct.G (aOf d p) 1 ct.yp σ ct.S i)⁻¹ k k) ^ 2 * B) =
        1 / d * (4 * S4 * B) := by
      rw [hS4, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
    rw [h3'] at h3
    calc ∑ j : nbhd ct.G ct.S i, (∑ w, ct.Cb h e σ i j w * extStar ct.G x' w) ^ 2
        ≤ 1 / h ^ 2 * ∑ l : nbhd ct.G ct.S i, x' l ^ 2 := h1.trans h2
      _ ≤ 1 / h ^ 2 * (1 / d * (4 * S4 * B)) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ ≤ cL ct h σ i * B := by
          rw [cL, ← hS4]
          have : 1 / d * (4 * S4 * B) ≤ 2 / d * (1 / h + 4 * S4) * B := by
            have h1h : 0 ≤ 1 / h * B := by positivity
            have hd1 : 0 ≤ 1 / (d : ℝ) := by positivity
            have : 1 / (d : ℝ) * (4 * S4 * B) ≤ 1 / d * (4 * S4 * B) + 1 / d * (4 * S4 * B) +
                2 / d * (1 / h * B) := by
              have : 0 ≤ 1 / (d : ℝ) * (4 * S4 * B) := by positivity
              have : 0 ≤ 2 / (d : ℝ) * (1 / h * B) := by positivity
              linarith
            calc 1 / (d : ℝ) * (4 * S4 * B) ≤ _ := this
              _ = 2 / d * (1 / h + 4 * S4) * B := by ring
          calc 1 / h ^ 2 * (1 / d * (4 * S4 * B)) ≤ 1 / h ^ 2 * (2 / d * (1 / h + 4 * S4) * B) :=
                mul_le_mul_of_nonneg_left this (by positivity)
            _ = _ := by ring
  | false =>
    simp only [Contact.tMap, Bool.false_eq_true, if_false]
    simp only [tCav_apply_mulVec]
    set ω : ct.V → ℝ := fun w => if w ∈ ct.N.erase i then ct.uvec w *
        (∑ w', ct.Cb h true σ i w w' * extStar ct.G x w' -
          ct.Cb h true σ i w w * extStar ct.G x w) else 0 with hωdef
    have hω : ∀ w, w ∉ ct.S.erase i → ω w = 0 := fun w hw => by
      have : w ∉ ct.N.erase i := fun hw' =>
        hw (Finset.erase_subset_erase i (N_subset ct) hw')
      simp only [hωdef]
      rw [if_neg this]
    have h1 := sum_nbhd_le_erase ct.G (S := ct.S) (i := i)
      (fun j => (∑ w, ct.Cb h e σ i j w * ω w) ^ 2) fun _ => sq_nonneg _
    have h2 : ∑ j ∈ ct.S.erase i, (∑ w, ct.Cb h e σ i j w * ω w) ^ 2 ≤
        (1 / h ^ 2) * ∑ w, ω w ^ 2 :=
      shift_row_sq ct.G hye hh hMe ω hω
    -- `‖ω‖² ≤ (2/d)(B/h + 4 S4 B)`
    set R : ct.V → ℝ := fun k => ∑ w', ct.Cb h true σ i k w' * extStar ct.G x w'
    have hR : ∑ k ∈ ct.S.erase i, R k ^ 2 ≤ 1 / h * B := by
      have h4 := shift_row_sq_bv ct.G hyp hh hMp x
      have h5 := dot_Kz_le ct.G hyp hh.le hMp (bv ct.G ct.yp x)
      simp only [R, Cb_true]
      refine h4.trans (mul_le_mul_of_nonneg_left h5 (by positivity))
    have hωsq : ∑ w, ω w ^ 2 ≤ 2 / d * (1 / h * B + 4 * S4 * B) := by
      have e1 : ∑ w, ω w ^ 2 = ∑ k ∈ ct.N.erase i, (ct.uvec k *
          (R k - ct.Cb h true σ i k k * extStar ct.G x k)) ^ 2 := by
        have : ∀ w, ω w ^ 2 = if w ∈ ct.N.erase i then (ct.uvec w *
            (R w - ct.Cb h true σ i w w * extStar ct.G x w)) ^ 2 else 0 := fun w => by
          simp only [hωdef, R]
          split_ifs <;> ring
        simp only [this]
        rw [Finset.sum_ite_mem, Finset.univ_inter]
      rw [e1]
      have hpt : ∀ k ∈ ct.N.erase i, (ct.uvec k *
          (R k - ct.Cb h true σ i k k * extStar ct.G x k)) ^ 2 ≤
          2 / d * (R k ^ 2 + 4 * ((precCore ct.G (aOf d p) 1 ct.yp σ ct.S i)⁻¹ k k) ^ 2 * B) := by
        intro k _
        have hu := uvec_sq ct hd k
        have hdk := hdiag k
        have hab : (R k - ct.Cb h true σ i k k * extStar ct.G x k) ^ 2 ≤
            2 * (R k ^ 2 + (ct.Cb h true σ i k k * extStar ct.G x k) ^ 2) := by
          nlinarith [sq_nonneg (R k + ct.Cb h true σ i k k * extStar ct.G x k)]
        rw [mul_pow]
        calc ct.uvec k ^ 2 * (R k - ct.Cb h true σ i k k * extStar ct.G x k) ^ 2
            ≤ 1 / d * (2 * (R k ^ 2 + (ct.Cb h true σ i k k * extStar ct.G x k) ^ 2)) :=
              mul_le_mul hu hab (sq_nonneg _) (by positivity)
          _ ≤ 1 / d * (2 * (R k ^ 2 +
                4 * ((precCore ct.G (aOf d p) 1 ct.yp σ ct.S i)⁻¹ k k) ^ 2 * B)) := by
              gcongr
          _ = _ := by ring
      refine (Finset.sum_le_sum hpt).trans ?_
      rw [← Finset.mul_sum, Finset.sum_add_distrib]
      have hRN : ∑ k ∈ ct.N.erase i, R k ^ 2 ≤ 1 / h * B :=
        le_trans (Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.erase_subset_erase i (N_subset ct)) fun _ _ _ => sq_nonneg _) hR
      have hDN : ∑ k ∈ ct.N.erase i,
          4 * ((precCore ct.G (aOf d p) 1 ct.yp σ ct.S i)⁻¹ k k) ^ 2 * B ≤ 4 * S4 * B := by
        rw [hS4, Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset i ct.N)
          fun _ _ _ => by positivity
      exact mul_le_mul_of_nonneg_left (add_le_add hRN hDN) (by positivity)
    calc ∑ j : nbhd ct.G ct.S i, (∑ w, ct.Cb h e σ i j w * ω w) ^ 2
        ≤ 1 / h ^ 2 * ∑ w, ω w ^ 2 := h1.trans h2
      _ ≤ 1 / h ^ 2 * (2 / d * (1 / h * B + 4 * S4 * B)) :=
          mul_le_mul_of_nonneg_left hωsq (by positivity)
      _ = cL ct h σ i * B := by rw [cL, ← hS4]; ring

theorem qForm_single {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) (l : ι) :
    qForm M (Pi.single l 1) = M l l := by
  simp [qForm, dotProduct, mulVec, Pi.single_apply]

theorem extStar_single (ct : Contact.{u} d p) {i : ct.V} (l : nbhd ct.G ct.S i) :
    extStar ct.G (Pi.single l (1 : ℝ)) = Pi.single (l : ct.V) 1 := by
  funext w
  by_cases hw : w ∈ nbhd ct.G ct.S i
  · simp only [extStar, dif_pos hw, Pi.single_apply, Subtype.ext_iff]
  · simp only [extStar, dif_neg hw, Pi.single_apply]
    rw [if_neg]
    rintro rfl
    exact hw l.2

theorem Bq_single (ct : Contact.{u} d p) (σ : Config ct.V) {i : ct.V} (l : nbhd ct.G ct.S i) :
    Bq ct σ i (Pi.single l 1) =
      ct.yp l * (precCore ct.G (aOf d p) 1 ct.yp σ ct.S i)⁻¹ l l := by
  have hb : bv ct.G ct.yp (Pi.single l 1) = Real.sqrt (ct.yp l) • Pi.single (l : ct.V) 1 := by
    funext w
    simp only [bv, extStar_single, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    split_ifs with hw
    · rw [hw]
    · simp
  rw [Bq, hb, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]
  have : Pi.single (l : ct.V) (1 : ℝ) ⬝ᵥ
      ((precCore ct.G (aOf d p) 1 ct.yp σ ct.S i)⁻¹ *ᵥ Pi.single (l : ct.V) 1) =
      (precCore ct.G (aOf d p) 1 ct.yp σ ct.S i)⁻¹ l l := qForm_single _ _
  rw [this, ← mul_assoc, Real.mul_self_sqrt (ct.ctx.hyp l).1]

/-- The trace envelope: `0 ≤ tr L ≤ c_L Σ_{l ∈ J} y⁺_l (K⁰₊)_ll`. -/
theorem env_trace (ct : Contact.{u} d p) (hd : 0 < (d : ℝ)) {h : ℝ} (hh : 0 < h) (e dir : Bool)
    {i : ct.V} (σ : Config ct.V)
    (hMp : (precCore ct.G (aOf d p) 1 ct.yp σ ct.S i).PosDef)
    (hMe : (precCore ct.G (aOf d p) (tau e) (ct.ySrc e) σ ct.S i).PosDef)
    (hye : ∀ k, 0 ≤ ct.ySrc e k) (hyp : ∀ k, 0 ≤ ct.yp k) (hy2 : ∀ k, ct.yp k ≤ 2)
    (hP2 : ∀ k, precCore ct.G (aOf d p) 1 ct.yp σ ct.S i k k ≤ 2) :
    0 ≤ (kerL ct h e dir i σ).trace ∧
      (kerL ct h e dir i σ).trace ≤ cL ct h σ i *
        ∑ l : nbhd ct.G ct.S i, ct.yp l * (precCore ct.G (aOf d p) 1 ct.yp σ ct.S i)⁻¹ l l := by
  have htr : (kerL ct h e dir i σ).trace =
      ∑ l : nbhd ct.G ct.S i, qForm (kerL ct h e dir i σ) (Pi.single l 1) := by
    simp only [Matrix.trace, Matrix.diag, qForm_single]
  rw [htr, Finset.mul_sum]
  refine ⟨Finset.sum_nonneg fun l _ => ?_, Finset.sum_le_sum fun l _ => ?_⟩
  · rw [kerL, qForm_transpose_mul]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  · rw [← Bq_single]
    exact env_qForm ct hd hh e dir σ hMp hMe hye hyp hy2 hP2 _

end Contact

end BiluLinial.Tight.SecB.WR
