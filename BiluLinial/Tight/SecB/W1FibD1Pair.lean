/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecB.W1FibD1Calc

/-!
# The endpoint derivatives of an edge fibre: the four configurations (tools for TB.W1fib-d1)

`wd1_obsD ct h k i j A B` is `DΨ` of configuration `k` evaluated on a pair `(A, B)` of normalized
precisions; at a signing it is `cfgD` (`wd1_obsD_precN`). `wd1_deriv_pair`: along
`A(t) = A + (t - t₀) a √(y⁺_i y⁺_j) E`, `B(t) = B - (t - t₀) a √(y⁻_i y⁻_j) E` with `A, B ≻ 0`,
`(det A(t) det B(t))^p Ψ(A(t), B(t))` has derivative `(det A det B)^p · wd1_obsD` at `t₀`
(`wd1_config_deriv` with `∂H = ∂Ω_±` and `∂b_± = dbP`, `dbM`).
-/

@[expose] public section

namespace BiluLinial.Tight.SecB

open Matrix

universe u

section Pair

variable {d p : ℕ} (ct : Contact.{u} d p)

/-- `DΨ` of configuration `k` on a pair `(A, B) = (P̃⁺, P̃⁻)` of normalized precisions
(cf. `cfgD`). -/
noncomputable def wd1_obsD (h : ℝ) (k : Fin 4) (i j : ct.V) (A B : Matrix ct.V ct.V ℝ) : ℝ :=
  match k with
  | 0 => wd1_fibD (2 * p * aOf d p * (physInv ct.yp A i j - physInv ct.ym B i j)) 1 (aOf d p)
      ((physInv ct.yp A ct.v ct.v / 2) ^ 2)
      (-(aOf d p) * physInv ct.yp A ct.v ct.v * physInv ct.yp A ct.v i * physInv ct.yp A ct.v j)
      (physInv ct.yp (A + h • srcDiag ct.yp ct.S)) (physInv ct.yp (A + h • srcDiag ct.yp ct.S))
      ct.uvec (fun _ => 0) i j
  | 1 => wd1_fibD (2 * p * aOf d p * (physInv ct.yp A i j - physInv ct.ym B i j)) 1 (aOf d p)
      ((physInv ct.yp A ct.v ct.v / 2) ^ 2)
      (-(aOf d p) * physInv ct.yp A ct.v ct.v * physInv ct.yp A ct.v i * physInv ct.yp A ct.v j)
      (physInv ct.yp (A + h • srcDiag ct.yp ct.S)) (physInv ct.yp (A + h • srcDiag ct.yp ct.S))
      (obsBP ct (physInv ct.yp (A + h • srcDiag ct.yp ct.S)))
      (fun m => -(4 * aOf d p ^ 3) * ∑ l, ct.adjS m l * ct.uvec l *
        (physInv ct.yp (A + h • srcDiag ct.yp ct.S) l l *
          physInv ct.yp (A + h • srcDiag ct.yp ct.S) l i *
          physInv ct.yp (A + h • srcDiag ct.yp ct.S) l j)) i j
  | 2 => wd1_fibD (2 * p * aOf d p * (physInv ct.yp A i j - physInv ct.ym B i j)) (-1) (aOf d p)
      (physInv ct.yp A ct.v ct.v * physInv ct.ym B ct.v ct.v / 4)
      (aOf d p / 2 * (physInv ct.yp A ct.v ct.v * physInv ct.ym B ct.v i *
          physInv ct.ym B ct.v j -
        physInv ct.yp A ct.v i * physInv ct.yp A ct.v j * physInv ct.ym B ct.v ct.v))
      (physInv ct.ym (B + h • srcDiag ct.ym ct.S)) (physInv ct.yp (A + h • srcDiag ct.yp ct.S))
      ct.uvec (fun _ => 0) i j
  | 3 => wd1_fibD (2 * p * aOf d p * (physInv ct.yp A i j - physInv ct.ym B i j)) (-1) (aOf d p)
      (physInv ct.yp A ct.v ct.v * physInv ct.ym B ct.v ct.v / 4)
      (aOf d p / 2 * (physInv ct.yp A ct.v ct.v * physInv ct.ym B ct.v i *
          physInv ct.ym B ct.v j -
        physInv ct.yp A ct.v i * physInv ct.yp A ct.v j * physInv ct.ym B ct.v ct.v))
      (physInv ct.ym (B + h • srcDiag ct.ym ct.S)) (physInv ct.yp (A + h • srcDiag ct.yp ct.S))
      (obsBM ct (physInv ct.yp (A + h • srcDiag ct.yp ct.S))
        (physInv ct.ym (B + h • srcDiag ct.ym ct.S)))
      (fun m => 2 * aOf d p ^ 3 * ∑ l, ct.adjS m l * ct.uvec l *
        (physInv ct.yp (A + h • srcDiag ct.yp ct.S) l l *
            physInv ct.ym (B + h • srcDiag ct.ym ct.S) l i *
            physInv ct.ym (B + h • srcDiag ct.ym ct.S) l j -
          physInv ct.ym (B + h • srcDiag ct.ym ct.S) l l *
            physInv ct.yp (A + h • srcDiag ct.yp ct.S) l i *
            physInv ct.yp (A + h • srcDiag ct.yp ct.S) l j)) i j

theorem wd1_obsD_precN (h : ℝ) (k : Fin 4) (i j : ct.V) (σ : Config ct.V) :
    wd1_obsD ct h k i j (precN ct.G (aOf d p) 1 ct.yp σ ct.S)
      (precN ct.G (aOf d p) (-1) ct.ym σ ct.S) = cfgD ct h k i j σ := by
  match k with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl

theorem wd1_obsBP_apply (X : Matrix ct.V ct.V ℝ) (m : ct.V) :
    obsBP ct X m = 4 * aOf d p ^ 2 * ∑ l, ct.adjS m l * ((X l l / 2) ^ 2 * ct.uvec l) := by
  change 4 * aOf d p ^ 2 *
    ∑ l, ct.adjS m l * (diagonal (fun l => (X l l / 2) ^ 2) *ᵥ ct.uvec) l = _
  simp only [Matrix.mulVec_diagonal]

theorem wd1_obsBM_apply (X Y : Matrix ct.V ct.V ℝ) (m : ct.V) :
    obsBM ct X Y m =
      4 * aOf d p ^ 2 * ∑ l, ct.adjS m l * (X l l / 2 * (Y l l / 2) * ct.uvec l) := by
  change 4 * aOf d p ^ 2 *
    ∑ l, ct.adjS m l * (diagonal (fun l => X l l / 2 * (Y l l / 2)) *ᵥ ct.uvec) l = _
  simp only [Matrix.mulVec_diagonal]

/-- `∂(b₊)_m = -4a³ Σ_l (A_H)_ml u_l X_ll X_li X_lj` (`dbP`). -/
theorem wd1_hasDerivAt_obsBP {X : ℝ → Matrix ct.V ct.V ℝ} {X0 : Matrix ct.V ct.V ℝ} {t₀ : ℝ}
    {i j : ct.V}
    (hX : ∀ k l, HasDerivAt (fun t => X t k l)
      (-(1 * aOf d p) * (X0 k i * X0 j l + X0 k j * X0 i l)) t₀)
    (hX0 : X t₀ = X0) (hsym : ∀ k l, X0 k l = X0 l k) (m : ct.V) :
    HasDerivAt (fun t => obsBP ct (X t) m)
      (-(4 * aOf d p ^ 3) * ∑ l, ct.adjS m l * ct.uvec l * (X0 l l * X0 l i * X0 l j)) t₀ := by
  subst hX0
  simp only [wd1_obsBP_apply]
  have h := (HasDerivAt.fun_sum (u := Finset.univ) fun l _ =>
    ((((hX l l).div_const 2).fun_pow 2).mul_const (ct.uvec l)).const_mul (ct.adjS m l)).const_mul
    (4 * aOf d p ^ 2)
  refine h.congr_deriv ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [hsym j l, hsym i l]
  simp only [Nat.reduceSub, pow_one, Nat.cast_ofNat]
  ring

/-- `∂(b₋)_m = 2a³ Σ_l (A_H)_ml u_l (X_ll Y_li Y_lj - Y_ll X_li X_lj)` (`dbM`). -/
theorem wd1_hasDerivAt_obsBM {X Y : ℝ → Matrix ct.V ct.V ℝ} {X0 Y0 : Matrix ct.V ct.V ℝ}
    {t₀ : ℝ} {i j : ct.V}
    (hX : ∀ k l, HasDerivAt (fun t => X t k l)
      (-(1 * aOf d p) * (X0 k i * X0 j l + X0 k j * X0 i l)) t₀)
    (hY : ∀ k l, HasDerivAt (fun t => Y t k l)
      (-(-1 * aOf d p) * (Y0 k i * Y0 j l + Y0 k j * Y0 i l)) t₀)
    (hX0 : X t₀ = X0) (hY0 : Y t₀ = Y0) (hsX : ∀ k l, X0 k l = X0 l k)
    (hsY : ∀ k l, Y0 k l = Y0 l k) (m : ct.V) :
    HasDerivAt (fun t => obsBM ct (X t) (Y t) m)
      (2 * aOf d p ^ 3 * ∑ l, ct.adjS m l * ct.uvec l *
        (X0 l l * Y0 l i * Y0 l j - Y0 l l * X0 l i * X0 l j)) t₀ := by
  subst hX0 hY0
  simp only [wd1_obsBM_apply]
  have h := (HasDerivAt.fun_sum (u := Finset.univ) fun l _ =>
    ((((hX l l).div_const 2).fun_mul ((hY l l).div_const 2)).mul_const (ct.uvec l)).const_mul
      (ct.adjS m l)).const_mul (4 * aOf d p ^ 2)
  refine h.congr_deriv ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [hsX j l, hsX i l, hsY j l, hsY i l]
  ring

/-- Along `A(t) = A + (t - t₀) a√(y⁺_iy⁺_j) E`, `B(t) = B - (t - t₀) a√(y⁻_iy⁻_j) E` (`A, B ≻ 0`),
`(det A(t) det B(t))^p Ψ(A(t), B(t))` has derivative `(det A det B)^p · wd1_obsD` at `t₀`. -/
theorem wd1_deriv_pair {h : ℝ} (hh : 0 ≤ h) (k : Fin 4) {i j : ct.V} (hij : i ≠ j)
    {A B : Matrix ct.V ct.V ℝ} (hA : A.PosDef) (hB : B.PosDef) (t₀ : ℝ) :
    HasDerivAt (fun t =>
        ((A + ((t - t₀) * (1 * aOf d p * (Real.sqrt (ct.yp i) * Real.sqrt (ct.yp j)))) •
            SecA.edgeE i j).det *
          (B + ((t - t₀) * (-1 * aOf d p * (Real.sqrt (ct.ym i) * Real.sqrt (ct.ym j)))) •
            SecA.edgeE i j).det) ^ p *
        obsPsi ct h k i j
          (A + ((t - t₀) * (1 * aOf d p * (Real.sqrt (ct.yp i) * Real.sqrt (ct.yp j)))) •
            SecA.edgeE i j)
          (B + ((t - t₀) * (-1 * aOf d p * (Real.sqrt (ct.ym i) * Real.sqrt (ct.ym j)))) •
            SecA.edgeE i j))
      ((A.det * B.det) ^ p * wd1_obsD ct h k i j A B) t₀ := by
  have hyp : ∀ k, 0 ≤ ct.yp k := fun k => (ct.ctx.hyp k).1
  have hym : ∀ k, 0 ≤ ct.ym k := fun k => (ct.ctx.hym k).1
  have hsrc : ∀ y : ct.V → ℝ, (∀ k, 0 ≤ y k) → (h • srcDiag y ct.S).PosSemidef := fun y hy => by
    refine Matrix.PosSemidef.smul ?_ hh
    refine Matrix.PosSemidef.diagonal fun l => ?_
    split_ifs
    · exact hy l
    · exact le_rfl
  have hAY := hA.add_posSemidef (hsrc _ hyp)
  have hBY := hB.add_posSemidef (hsrc _ hym)
  have hW := wd1_hasDerivAt_W hA hB hij p (aOf d p) t₀ ct.yp ct.ym
  have hW0 : ((A + ((t₀ - t₀) * (1 * aOf d p * (Real.sqrt (ct.yp i) * Real.sqrt (ct.yp j)))) •
        SecA.edgeE i j).det *
      (B + ((t₀ - t₀) * (-1 * aOf d p * (Real.sqrt (ct.ym i) * Real.sqrt (ct.ym j)))) •
        SecA.edgeE i j).det) ^ p = (A.det * B.det) ^ p := by
    simp only [sub_self, zero_mul, zero_smul, add_zero]
  have gA := wd1_hasDerivAt_physInv ct.yp hA.det_pos.ne' 1 (aOf d p) t₀ i j
  have gB := wd1_hasDerivAt_physInv ct.ym hB.det_pos.ne' (-1) (aOf d p) t₀ i j
  have xA := wd1_hasDerivAt_physInv_add ct.yp (S₀ := h • srcDiag ct.yp ct.S) hAY.det_pos.ne' 1
    (aOf d p) t₀ i j
  have xB := wd1_hasDerivAt_physInv_add ct.ym (S₀ := h • srcDiag ct.ym ct.S) hBY.det_pos.ne' (-1)
    (aOf d p) t₀ i j
  have sGA := wd1_physInv_symm ct.yp hA.isHermitian
  have sGB := wd1_physInv_symm ct.ym hB.isHermitian
  have sXA := wd1_physInv_symm ct.yp hAY.isHermitian
  have sXB := wd1_physInv_symm ct.ym hBY.isHermitian
  have xA0 : physInv ct.yp (A + ((t₀ - t₀) * (1 * aOf d p * (Real.sqrt (ct.yp i) *
      Real.sqrt (ct.yp j)))) • SecA.edgeE i j + h • srcDiag ct.yp ct.S) =
      physInv ct.yp (A + h • srcDiag ct.yp ct.S) := by
    simp only [sub_self, zero_mul, zero_smul, add_zero]
  have xB0 : physInv ct.ym (B + ((t₀ - t₀) * (-1 * aOf d p * (Real.sqrt (ct.ym i) *
      Real.sqrt (ct.ym j)))) • SecA.edgeE i j + h • srcDiag ct.ym ct.S) =
      physInv ct.ym (B + h • srcDiag ct.ym ct.S) := by
    simp only [sub_self, zero_mul, zero_smul, add_zero]
  have hH1 : HasDerivAt (fun t => (physInv ct.yp (A + ((t - t₀) * (1 * aOf d p *
      (Real.sqrt (ct.yp i) * Real.sqrt (ct.yp j)))) • SecA.edgeE i j) ct.v ct.v / 2) ^ 2)
      (-(aOf d p) * physInv ct.yp A ct.v ct.v * physInv ct.yp A ct.v i *
        physInv ct.yp A ct.v j) t₀ := by
    refine (((gA ct.v ct.v).div_const 2).fun_pow 2).congr_deriv ?_
    simp only [sub_self, zero_mul, zero_smul, add_zero, Nat.reduceSub, pow_one, Nat.cast_ofNat]
    rw [sGA j ct.v, sGA i ct.v]
    ring
  have hH10 : (physInv ct.yp (A + ((t₀ - t₀) * (1 * aOf d p *
      (Real.sqrt (ct.yp i) * Real.sqrt (ct.yp j)))) • SecA.edgeE i j) ct.v ct.v / 2) ^ 2 =
      (physInv ct.yp A ct.v ct.v / 2) ^ 2 := by
    simp only [sub_self, zero_mul, zero_smul, add_zero]
  have hH2 : HasDerivAt (fun t => physInv ct.yp (A + ((t - t₀) * (1 * aOf d p *
      (Real.sqrt (ct.yp i) * Real.sqrt (ct.yp j)))) • SecA.edgeE i j) ct.v ct.v *
      physInv ct.ym (B + ((t - t₀) * (-1 * aOf d p *
      (Real.sqrt (ct.ym i) * Real.sqrt (ct.ym j)))) • SecA.edgeE i j) ct.v ct.v / 4)
      (aOf d p / 2 * (physInv ct.yp A ct.v ct.v * physInv ct.ym B ct.v i *
          physInv ct.ym B ct.v j -
        physInv ct.yp A ct.v i * physInv ct.yp A ct.v j * physInv ct.ym B ct.v ct.v)) t₀ := by
    refine (((gA ct.v ct.v).fun_mul (gB ct.v ct.v)).div_const 4).congr_deriv ?_
    simp only [sub_self, zero_mul, zero_smul, add_zero]
    rw [sGA j ct.v, sGA i ct.v, sGB j ct.v, sGB i ct.v]
    ring
  have hH20 : physInv ct.yp (A + ((t₀ - t₀) * (1 * aOf d p *
      (Real.sqrt (ct.yp i) * Real.sqrt (ct.yp j)))) • SecA.edgeE i j) ct.v ct.v *
      physInv ct.ym (B + ((t₀ - t₀) * (-1 * aOf d p *
      (Real.sqrt (ct.ym i) * Real.sqrt (ct.ym j)))) • SecA.edgeE i j) ct.v ct.v / 4 =
      physInv ct.yp A ct.v ct.v * physInv ct.ym B ct.v ct.v / 4 := by
    simp only [sub_self, zero_mul, zero_smul, add_zero]
  match k with
  | 0 =>
    exact wd1_config_deriv
      (Wf := fun t => ((A + ((t - t₀) * (1 * aOf d p * (Real.sqrt (ct.yp i) *
          Real.sqrt (ct.yp j)))) • SecA.edgeE i j).det *
        (B + ((t - t₀) * (-1 * aOf d p * (Real.sqrt (ct.ym i) * Real.sqrt (ct.ym j)))) •
          SecA.edgeE i j).det) ^ p)
      (Hf := fun t => (physInv ct.yp (A + ((t - t₀) * (1 * aOf d p *
        (Real.sqrt (ct.yp i) * Real.sqrt (ct.yp j)))) • SecA.edgeE i j) ct.v ct.v / 2) ^ 2)
      (Xe := fun t => physInv ct.yp (A + ((t - t₀) * (1 * aOf d p * (Real.sqrt (ct.yp i) *
        Real.sqrt (ct.yp j)))) • SecA.edgeE i j + h • srcDiag ct.yp ct.S))
      (Xn := fun t => physInv ct.yp (A + ((t - t₀) * (1 * aOf d p * (Real.sqrt (ct.yp i) *
        Real.sqrt (ct.yp j)))) • SecA.edgeE i j + h • srcDiag ct.yp ct.S))
      (f := fun _ => ct.uvec) hW hW0 hH1 hH10 xA xA (fun m => hasDerivAt_const t₀ (ct.uvec m))
      xA0 xA0 rfl (sXA j i) (sXA j i)
  | 1 =>
    exact wd1_config_deriv
      (Wf := fun t => ((A + ((t - t₀) * (1 * aOf d p * (Real.sqrt (ct.yp i) *
          Real.sqrt (ct.yp j)))) • SecA.edgeE i j).det *
        (B + ((t - t₀) * (-1 * aOf d p * (Real.sqrt (ct.ym i) * Real.sqrt (ct.ym j)))) •
          SecA.edgeE i j).det) ^ p)
      (Hf := fun t => (physInv ct.yp (A + ((t - t₀) * (1 * aOf d p *
        (Real.sqrt (ct.yp i) * Real.sqrt (ct.yp j)))) • SecA.edgeE i j) ct.v ct.v / 2) ^ 2)
      (Xe := fun t => physInv ct.yp (A + ((t - t₀) * (1 * aOf d p * (Real.sqrt (ct.yp i) *
        Real.sqrt (ct.yp j)))) • SecA.edgeE i j + h • srcDiag ct.yp ct.S))
      (Xn := fun t => physInv ct.yp (A + ((t - t₀) * (1 * aOf d p * (Real.sqrt (ct.yp i) *
        Real.sqrt (ct.yp j)))) • SecA.edgeE i j + h • srcDiag ct.yp ct.S))
      (f := fun t => obsBP ct (physInv ct.yp (A + ((t - t₀) * (1 * aOf d p *
        (Real.sqrt (ct.yp i) * Real.sqrt (ct.yp j)))) • SecA.edgeE i j +
          h • srcDiag ct.yp ct.S)))
      hW hW0 hH1 hH10 xA xA (wd1_hasDerivAt_obsBP ct xA xA0 sXA)
      xA0 xA0 (by simp only [sub_self, zero_mul, zero_smul, add_zero]) (sXA j i) (sXA j i)
  | 2 =>
    exact wd1_config_deriv
      (Wf := fun t => ((A + ((t - t₀) * (1 * aOf d p * (Real.sqrt (ct.yp i) *
          Real.sqrt (ct.yp j)))) • SecA.edgeE i j).det *
        (B + ((t - t₀) * (-1 * aOf d p * (Real.sqrt (ct.ym i) * Real.sqrt (ct.ym j)))) •
          SecA.edgeE i j).det) ^ p)
      (Hf := fun t => physInv ct.yp (A + ((t - t₀) * (1 * aOf d p *
        (Real.sqrt (ct.yp i) * Real.sqrt (ct.yp j)))) • SecA.edgeE i j) ct.v ct.v *
        physInv ct.ym (B + ((t - t₀) * (-1 * aOf d p *
        (Real.sqrt (ct.ym i) * Real.sqrt (ct.ym j)))) • SecA.edgeE i j) ct.v ct.v / 4)
      (Xe := fun t => physInv ct.ym (B + ((t - t₀) * (-1 * aOf d p * (Real.sqrt (ct.ym i) *
        Real.sqrt (ct.ym j)))) • SecA.edgeE i j + h • srcDiag ct.ym ct.S))
      (Xn := fun t => physInv ct.yp (A + ((t - t₀) * (1 * aOf d p * (Real.sqrt (ct.yp i) *
        Real.sqrt (ct.yp j)))) • SecA.edgeE i j + h • srcDiag ct.yp ct.S))
      (f := fun _ => ct.uvec) hW hW0 hH2 hH20 xB xA (fun m => hasDerivAt_const t₀ (ct.uvec m))
      xB0 xA0 rfl (sXB j i) (sXA j i)
  | 3 =>
    exact wd1_config_deriv
      (Wf := fun t => ((A + ((t - t₀) * (1 * aOf d p * (Real.sqrt (ct.yp i) *
          Real.sqrt (ct.yp j)))) • SecA.edgeE i j).det *
        (B + ((t - t₀) * (-1 * aOf d p * (Real.sqrt (ct.ym i) * Real.sqrt (ct.ym j)))) •
          SecA.edgeE i j).det) ^ p)
      (Hf := fun t => physInv ct.yp (A + ((t - t₀) * (1 * aOf d p *
        (Real.sqrt (ct.yp i) * Real.sqrt (ct.yp j)))) • SecA.edgeE i j) ct.v ct.v *
        physInv ct.ym (B + ((t - t₀) * (-1 * aOf d p *
        (Real.sqrt (ct.ym i) * Real.sqrt (ct.ym j)))) • SecA.edgeE i j) ct.v ct.v / 4)
      (Xe := fun t => physInv ct.ym (B + ((t - t₀) * (-1 * aOf d p * (Real.sqrt (ct.ym i) *
        Real.sqrt (ct.ym j)))) • SecA.edgeE i j + h • srcDiag ct.ym ct.S))
      (Xn := fun t => physInv ct.yp (A + ((t - t₀) * (1 * aOf d p * (Real.sqrt (ct.yp i) *
        Real.sqrt (ct.yp j)))) • SecA.edgeE i j + h • srcDiag ct.yp ct.S))
      (f := fun t => obsBM ct (physInv ct.yp (A + ((t - t₀) * (1 * aOf d p *
        (Real.sqrt (ct.yp i) * Real.sqrt (ct.yp j)))) • SecA.edgeE i j +
          h • srcDiag ct.yp ct.S))
        (physInv ct.ym (B + ((t - t₀) * (-1 * aOf d p *
          (Real.sqrt (ct.ym i) * Real.sqrt (ct.ym j)))) • SecA.edgeE i j +
          h • srcDiag ct.ym ct.S)))
      hW hW0 hH2 hH20 xB xA (wd1_hasDerivAt_obsBM ct xA xB xA0 xB0 sXA sXB)
      xB0 xA0 (by simp only [sub_self, zero_mul, zero_smul, add_zero]) (sXB j i)
      (sXA j i)

end Pair

end BiluLinial.Tight.SecB
