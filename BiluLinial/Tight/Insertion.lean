/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.Params
public import BiluLinial.Common.Schur

/-!
# Root insertion and deletion

Blueprint nodes `D-ins`, `D-empty` (source Section 1.1, display (F1)), and the definitions used by
`D-del`, `D-transfer` (`Tight/Deletion.lean`).

Fix a root `v ∈ S` and the core `J = S - v`. The *inherited* core precision `M = P̃_S(y)|_J` keeps
the diagonal `D^S_i(y)` of `S` (`precCore`: `P̃_S(y)` with row and column `v` replaced by those of
the identity). With the incident column `b_w = P̃_S(y)_{wv}`, the Schur complement at `v` is
`D_v (1 - q)` with the root energy `q = bᵀ M⁻¹ b / D_v` (`qRoot`; `q_A` for the plus branch, `q_B`
for the minus branch), so
`W_S(σ) = W_core(σ) (D_v⁺ D_v⁻)^p Φ(σ)`, `Φ = (1 - q_A)₊^p (1 - q_B)₊^p` (`wt_eq_wtCore_mul`).

**Deletion** (`precCore_eq_congr`). There are smaller sources `ŷ ≤ y` with
`M = E P̃_J(ŷ) E` for a diagonal `E ≥ 1` (`E_ii = √(y_i/ŷ_i)` at positive sources): the inherited
law of the core is the law of `J` with sources `ŷ`. Proof (replacing the source's ODE lift): on
the positive-source vertices of `J`, the map `T(ŷ)_i = D^J_i(ŷ) y_i / D^S_i(y)` is monotone, and
maps the box `[y_i / D^S_i(y), y_i]` into itself because `D^J_i(y) ≤ D^S_i(y)`; Knaster–Tarski
gives a fixed point, i.e. `Z^J(ŷ) = Z^S(y)|_J`.
-/

@[expose] public section

namespace BiluLinial.Tight

open Matrix

section Defs

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The inherited core precision at the root `v`: `P̃_S(y)` with row and column `v` replaced by
those of the identity. On `J = S - v` it is `P̃_S(y)|_J` (diagonal `D^S`, not `D^J`). -/
noncomputable def precCore (a τ : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) (v : V) :
    Matrix V V ℝ :=
  Matrix.of fun u w =>
    if u = v ∨ w = v then (if u = w then 1 else 0) else precN G a τ y σ S u w

open Classical in
/-- The inherited core weight `1{M⁺ ≻ 0, M⁻ ≻ 0} (det M⁺ det M⁻)^p`. It does not depend on the
signs of the edges at `v`. -/
noncomputable def wtCore (p : ℕ) (a : ℝ) (yp ym : V → ℝ) (σ : Config V) (S : Finset V) (v : V) :
    ℝ :=
  if (precCore G a 1 yp σ S v).PosDef ∧ (precCore G a (-1) ym σ S v).PosDef then
    ((precCore G a 1 yp σ S v).det * (precCore G a (-1) ym σ S v).det) ^ p
  else 0

/-- The inherited core partition function. -/
noncomputable def ZwCore (p : ℕ) (a : ℝ) (yp ym : V → ℝ) (S : Finset V) (v : V) : ℝ :=
  ∑ σ : Config V, wtCore G p a yp ym σ S v

/-- Expectation under the inherited core law (the "own core law" `ν_K` of the source). -/
noncomputable def coreE (p : ℕ) (a : ℝ) (yp ym : V → ℝ) (S : Finset V) (v : V)
    (f : Config V → ℝ) : ℝ :=
  (∑ σ : Config V, wtCore G p a yp ym σ S v * f σ) / ZwCore G p a yp ym S v

/-- The incident column `b_w = P̃_S(y)_{wv}` (`w ≠ v`), zero at `v`. -/
noncomputable def incCol (a τ : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) (v : V) : V → ℝ :=
  fun w => if w = v then 0 else precN G a τ y σ S w v

/-- The root energy `q = bᵀ M⁻¹ b / D_v`: `q_A = ξᵀ A ξ` for `τ = 1`, `q_B = ξᵀ B ξ` for `τ = -1`. -/
noncomputable def qRoot (a τ : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) (v : V) : ℝ :=
  incCol G a τ y σ S v ⬝ᵥ ((precCore G a τ y σ S v)⁻¹ *ᵥ incCol G a τ y σ S v) /
    diagD G a y S v

/-- The insertion factor `Φ = α₊^p β₊^p`, `α = 1 - q_A`, `β = 1 - q_B`. -/
noncomputable def PhiRoot (p : ℕ) (a : ℝ) (yp ym : V → ℝ) (σ : Config V) (S : Finset V)
    (v : V) : ℝ :=
  (max (1 - qRoot G a 1 yp σ S v) 0 * max (1 - qRoot G a (-1) ym σ S v) 0) ^ p

end Defs

section CoreMat

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `P` with row and column `v` replaced by those of the identity. -/
private def coreMat (P : Matrix V V ℝ) (v : V) : Matrix V V ℝ :=
  Matrix.of fun u w => if u = v ∨ w = v then (if u = w then 1 else 0) else P u w

variable {P : Matrix V V ℝ} {v : V}

omit [Fintype V] in
private lemma coreMat_isHermitian (hP : P.IsHermitian) : (coreMat P v).IsHermitian := by
  refine IsHermitian.ext fun i j => ?_
  have h : P j i = P i j := by simpa using hP.apply i j
  simp only [coreMat, of_apply, star_trivial]
  by_cases hij : i = j
  · subst hij
    rfl
  · rw [ite_eq_right (Ne.symm hij), ite_eq_right hij, h]
    split_ifs <;> first | rfl | (exfalso; tauto)

omit [Fintype V] in
private lemma delVertex_coreMat : delVertex (coreMat P v) v = delVertex P v := by
  ext ⟨a, ha⟩ ⟨b, hb⟩
  simp [delVertex, coreMat, ha, hb]

private lemma vertexSchur_coreMat : vertexSchur (coreMat P v) v = 1 := by
  have h1 : coreMat P v v v = 1 := by simp [coreMat]
  have h2 : (fun w : {w // w ≠ v} => coreMat P v w v) = 0 := by
    funext w
    simp [coreMat, w.2]
  rw [vertexSchur, h1, h2]
  simp

private lemma coreMat_posDef_iff (hP : P.IsHermitian) :
    (coreMat P v).PosDef ↔ (delVertex P v).PosDef := by
  constructor
  · intro h
    rw [← delVertex_coreMat]
    exact h.submatrix Subtype.val_injective
  · intro h
    rw [vertexSchur_posDef_iff (coreMat_isHermitian hP) (by rwa [delVertex_coreMat]),
      vertexSchur_coreMat]
    exact one_pos

private lemma det_coreMat (hP : P.IsHermitian) (hD : (delVertex P v).PosDef) :
    (coreMat P v).det = (delVertex P v).det := by
  rw [vertexSchur_det (coreMat_isHermitian hP) (by rwa [delVertex_coreMat]),
    vertexSchur_coreMat, delVertex_coreMat, mul_one]

/-- `bᵀ (coreMat P v)⁻¹ b` only sees the block off `v`, since `coreMat P v` is block diagonal
with a `1` at `v` and `b v = 0`. -/
private lemma quadForm_coreMat (hP : P.IsHermitian) (hD : (delVertex P v).PosDef) {b : V → ℝ}
    (hb : b v = 0) :
    b ⬝ᵥ ((coreMat P v)⁻¹ *ᵥ b) =
      (fun w : {w // w ≠ v} => b w) ⬝ᵥ
        ((delVertex P v)⁻¹ *ᵥ fun w : {w // w ≠ v} => b w) := by
  have hM : (coreMat P v).PosDef := (coreMat_posDef_iff hP).2 hD
  have hDu : IsUnit (delVertex P v).det := (isUnit_iff_isUnit_det _).mp hD.isUnit
  have hMu : IsUnit (coreMat P v).det := (isUnit_iff_isUnit_det _).mp hM.isUnit
  set z := (delVertex P v)⁻¹ *ᵥ fun w : {w // w ≠ v} => b w with hz
  have hDz : delVertex P v *ᵥ z = fun w : {w // w ≠ v} => b w := by
    rw [hz, mulVec_mulVec, mul_nonsing_inv _ hDu, one_mulVec]
  let x : V → ℝ := fun w => if h : w = v then 0 else z ⟨w, h⟩
  have hxv : x v = 0 := by simp [x]
  have hx : ∀ w : {w // w ≠ v}, x w = z w := fun w => by simp [x, w.2]
  have hMx : coreMat P v *ᵥ x = b := by
    funext u
    rw [mulVec, dotProduct, Fintype.sum_eq_add_sum_subtype_ne _ v, hxv, mul_zero, zero_add]
    simp only [hx]
    by_cases hu : u = v
    · rw [hu, hb]
      exact Finset.sum_eq_zero fun w _ => by simp [coreMat, Ne.symm w.2]
    · refine Eq.trans ?_ (congrFun hDz (⟨u, hu⟩ : {w // w ≠ v}))
      simp only [mulVec, dotProduct, delVertex, submatrix_apply]
      refine Finset.sum_congr rfl fun w _ => ?_
      simp [coreMat, hu, w.2]
  have hinv : (coreMat P v)⁻¹ *ᵥ b = x := by
    calc (coreMat P v)⁻¹ *ᵥ b = (coreMat P v)⁻¹ *ᵥ (coreMat P v *ᵥ x) := by rw [hMx]
      _ = x := by rw [mulVec_mulVec, nonsing_inv_mul _ hMu, one_mulVec]
  rw [hinv]
  simp only [dotProduct]
  rw [Fintype.sum_eq_add_sum_subtype_ne _ v, hxv, mul_zero, zero_add]
  simp only [hx]

/-- The Schur complement at `v` through the core: `P_vv - bᵀ (coreMat P v)⁻¹ b`. -/
private lemma vertexSchur_eq_coreMat (hP : P.IsHermitian) (hD : (delVertex P v).PosDef)
    (b : V → ℝ) (hbv : b v = 0) (hb : ∀ w, w ≠ v → b w = P w v) :
    vertexSchur P v = P v v - b ⬝ᵥ ((coreMat P v)⁻¹ *ᵥ b) := by
  have h : (fun w : {w // w ≠ v} => b w) = fun w : {w // w ≠ v} => P w v :=
    funext fun w => hb w w.2
  rw [quadForm_coreMat hP hD hbv, h]
  rfl

end CoreMat

section InsAux

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

private lemma cRoot_nonneg_of {x : ℝ} (hx : 0 ≤ x) : 0 ≤ cRoot x := by
  unfold cRoot
  have : 1 ≤ Real.sqrt (1 + 4 * x) := Real.one_le_sqrt.2 (by linarith)
  linarith

omit [Fintype V] [DecidableEq V] in
private lemma one_le_diagD_of (a : ℝ) {y : V → ℝ} (hy : ∀ i, 0 ≤ y i) (S : Finset V) (i : V) :
    1 ≤ diagD G a y S i := by
  have : 0 ≤ ∑ j ∈ nbhd G S i, cEdge a y i j := Finset.sum_nonneg fun j _ =>
    cRoot_nonneg_of (mul_nonneg (mul_nonneg (sq_nonneg a) (hy i)) (hy j))
  unfold diagD
  linarith

omit [Fintype V] in
private lemma precN_isHermitian (a τ : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) :
    (precN G a τ y σ S).IsHermitian := by
  refine IsHermitian.ext fun i j => ?_
  simp only [precN, of_apply, star_trivial]
  by_cases hij : i = j
  · subst hij
    rfl
  · have hs : sgn σ j i = sgn σ i j := by
      unfold sgn
      rw [Sym2.eq_swap]
    rw [ite_eq_right (Ne.symm hij), ite_eq_right hij]
    by_cases h : i ∈ S ∧ j ∈ S ∧ G.Adj i j
    · rw [ite_eq_left ⟨h.2.1, h.1, h.2.2.symm⟩, ite_eq_left h, hs]
      ring
    · rw [ite_eq_right (fun h' => h ⟨h'.2.1, h'.1, h'.2.2.symm⟩), ite_eq_right h]

omit [Fintype V] in
private lemma precCore_eq_coreMat (a τ : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) (v : V) :
    precCore G a τ y σ S v = coreMat (precN G a τ y σ S) v := rfl

private lemma precCore_posDef_of (a τ : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) (v : V)
    (h : (precN G a τ y σ S).PosDef) : (precCore G a τ y σ S v).PosDef := by
  rw [precCore_eq_coreMat, coreMat_posDef_iff (precN_isHermitian G a τ y σ S)]
  exact h.submatrix Subtype.val_injective

/-- One branch of the insertion identity: given `M ≻ 0`, `P ≻ 0 ↔ q < 1` and
`det P = det M · D_v (1 - q)`. -/
private lemma ins_branch (a τ : ℝ) {y : V → ℝ} (hy : ∀ i, 0 ≤ y i) (σ : Config V)
    {S : Finset V} {v : V} (hv : v ∈ S) (hM : (precCore G a τ y σ S v).PosDef) :
    ((precN G a τ y σ S).PosDef ↔ qRoot G a τ y σ S v < 1) ∧
      (precN G a τ y σ S).det =
        (precCore G a τ y σ S v).det * (diagD G a y S v * (1 - qRoot G a τ y σ S v)) := by
  have hP := precN_isHermitian G a τ y σ S
  have hD : (delVertex (precN G a τ y σ S) v).PosDef := by
    rw [← coreMat_posDef_iff hP, ← precCore_eq_coreMat]
    exact hM
  have hDv : 0 < diagD G a y S v := lt_of_lt_of_le one_pos (one_le_diagD_of G a hy S v)
  have hS : vertexSchur (precN G a τ y σ S) v =
      diagD G a y S v * (1 - qRoot G a τ y σ S v) := by
    rw [vertexSchur_eq_coreMat hP hD (incCol G a τ y σ S v) (by simp [incCol])
      (fun w hw => by simp [incCol, hw]), qRoot, ← precCore_eq_coreMat]
    have hvv : precN G a τ y σ S v v = diagD G a y S v := by simp [precN, hv]
    rw [hvv, mul_sub, mul_one, mul_div_cancel₀ _ hDv.ne']
  refine ⟨?_, ?_⟩
  · rw [vertexSchur_posDef_iff hP hD, hS]
    constructor
    · intro h
      by_contra hq
      nlinarith [not_lt.1 hq]
    · intro h
      exact mul_pos hDv (by linarith)
  · rw [vertexSchur_det hP hD, hS, precCore_eq_coreMat, det_coreMat hP hD]

end InsAux

section Statements

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- `D-empty`: the law of the empty graph exists (`P̃ = I`, every weight is `1`). -/
theorem Zw_empty_pos (p : ℕ) (a : ℝ) (yp ym : V → ℝ) : 0 < Zw G p a yp ym ∅ := by
  have h1 : ∀ (τ : ℝ) (y : V → ℝ) (σ : Config V), precN G a τ y σ ∅ = 1 := by
    intro τ y σ
    ext u w
    by_cases h : u = w <;> simp [precN, h, one_apply]
  have hw : ∀ σ : Config V, wt G p a yp ym σ ∅ = 1 := by
    intro σ
    rw [wt, h1, h1, ite_eq_left ⟨PosDef.one, PosDef.one⟩, det_one, one_mul, one_pow]
  unfold Zw
  simp only [hw]
  exact Finset.sum_pos (fun _ _ => one_pos) Finset.univ_nonempty

/-- `D-ins`: Schur factorization at the root, `W_S = W_core (D_v⁺ D_v⁻)^p Φ`. -/
theorem wt_eq_wtCore_mul {p : ℕ} (hp : 1 ≤ p) (a : ℝ) {yp ym : V → ℝ} (hyp : ∀ i, 0 ≤ yp i)
    (hym : ∀ i, 0 ≤ ym i) (σ : Config V) {S : Finset V} {v : V} (hv : v ∈ S) :
    wt G p a yp ym σ S =
      wtCore G p a yp ym σ S v * (diagD G a yp S v * diagD G a ym S v) ^ p *
        PhiRoot G p a yp ym σ S v := by
  unfold wt wtCore PhiRoot
  by_cases hM : (precCore G a 1 yp σ S v).PosDef ∧ (precCore G a (-1) ym σ S v).PosDef
  · obtain ⟨hpA, hdA⟩ := ins_branch G a 1 hyp σ hv hM.1
    obtain ⟨hpB, hdB⟩ := ins_branch G a (-1) hym σ hv hM.2
    rw [ite_eq_left hM]
    by_cases hq : qRoot G a 1 yp σ S v < 1 ∧ qRoot G a (-1) ym σ S v < 1
    · rw [ite_eq_left ⟨hpA.2 hq.1, hpB.2 hq.2⟩, hdA, hdB, max_eq_left (by linarith [hq.1]),
        max_eq_left (by linarith [hq.2]), ← mul_pow, ← mul_pow]
      congr 1
      ring
    · rw [ite_eq_right (fun h => hq ⟨hpA.1 h.1, hpB.1 h.2⟩)]
      have h0 : max (1 - qRoot G a 1 yp σ S v) 0 * max (1 - qRoot G a (-1) ym σ S v) 0 = 0 := by
        rcases not_and_or.1 hq with h | h
        · rw [max_eq_right (show 1 - qRoot G a 1 yp σ S v ≤ 0 by linarith [not_lt.1 h]),
            zero_mul]
        · rw [max_eq_right (show 1 - qRoot G a (-1) ym σ S v ≤ 0 by linarith [not_lt.1 h]),
            mul_zero]
      rw [h0, zero_pow (by omega), mul_zero]
  · rw [ite_eq_right hM, zero_mul, zero_mul, ite_eq_right]
    exact fun h => hM ⟨precCore_posDef_of G a 1 yp σ S v h.1,
      precCore_posDef_of G a (-1) ym σ S v h.2⟩

end Statements

end BiluLinial.Tight
