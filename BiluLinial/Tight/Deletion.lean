/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.Insertion

/-!
# Deletion of the root and transfer of the core law

Blueprint nodes `D-del`, `D-transfer` (source Section 1.1, Lemma "Deletion and source
differentiation"). The inherited core precision `precCore` is a diagonal congruence of the
precision of `J = S - v` at smaller sources `ŷ ≤ y` (`precCore_eq_congr`; Knaster–Tarski replaces
the source's ODE lift). Through such congruences the inherited core law exists when the law of `J`
does, and its normalized diagonals are bounded by those of `J` (`ZwCore_pos_of_congr`,
`coreE_inv_le_of_congr`).
-/

@[expose] public section

namespace BiluLinial.Tight

open Matrix

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

section DelAux

private lemma del_cRoot_zero : cRoot 0 = 0 := by simp [cRoot]

private lemma del_cRoot_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ cRoot x := by
  unfold cRoot
  have : 1 ≤ Real.sqrt (1 + 4 * x) := Real.one_le_sqrt.2 (by linarith)
  linarith

private lemma del_cRoot_mono {x x' : ℝ} (h : x ≤ x') : cRoot x ≤ cRoot x' := by
  unfold cRoot
  have := Real.sqrt_le_sqrt (show 1 + 4 * x ≤ 1 + 4 * x' by linarith)
  linarith

omit [Fintype V] [DecidableEq V] in
private lemma del_one_le_diagD (a : ℝ) {z : V → ℝ} (hz : ∀ i, 0 ≤ z i) (J : Finset V) (i : V) :
    1 ≤ diagD G a z J i := by
  have : 0 ≤ ∑ j ∈ nbhd G J i, cEdge a z i j := Finset.sum_nonneg fun j _ =>
    del_cRoot_nonneg (mul_nonneg (mul_nonneg (sq_nonneg a) (hz i)) (hz j))
  unfold diagD
  linarith

omit [Fintype V] [DecidableEq V] in
private lemma del_diagD_mono (a : ℝ) {z z' : V → ℝ} (hz : ∀ i, 0 ≤ z i)
    (hzz : ∀ i, z i ≤ z' i) (J : Finset V) (i : V) : diagD G a z J i ≤ diagD G a z' J i := by
  have : ∑ j ∈ nbhd G J i, cEdge a z i j ≤ ∑ j ∈ nbhd G J i, cEdge a z' i j := by
    refine Finset.sum_le_sum fun j _ => del_cRoot_mono ?_
    have h1 : z i * z j ≤ z' i * z' j :=
      mul_le_mul (hzz i) (hzz j) (hz j) ((hz i).trans (hzz i))
    calc a ^ 2 * z i * z j = a ^ 2 * (z i * z j) := by ring
      _ ≤ a ^ 2 * (z' i * z' j) := mul_le_mul_of_nonneg_left h1 (sq_nonneg a)
      _ = a ^ 2 * z' i * z' j := by ring
  unfold diagD
  linarith

omit [Fintype V] [DecidableEq V] in
private lemma del_diagD_le (a : ℝ) {z y : V → ℝ} (hz : ∀ i, 0 ≤ z i) (hzy : ∀ i, z i ≤ y i)
    {J S : Finset V} (hJS : J ⊆ S) (i : V) : diagD G a z J i ≤ diagD G a y S i := by
  refine (del_diagD_mono G a hz hzy J i).trans ?_
  have hy : ∀ i, 0 ≤ y i := fun i => (hz i).trans (hzy i)
  have : ∑ j ∈ nbhd G J i, cEdge a y i j ≤ ∑ j ∈ nbhd G S i, cEdge a y i j :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset_filter _ hJS)
      fun j _ _ => del_cRoot_nonneg (mul_nonneg (mul_nonneg (sq_nonneg a) (hy i)) (hy j))
  unfold diagD
  linarith

omit [Fintype V] [DecidableEq V] in
/-- Knaster–Tarski on the box `[0, y]`: a monotone self-map of the box has a fixed point. -/
private lemma del_exists_fixed {y : V → ℝ} (hy : 0 ≤ y) (T : (V → ℝ) → V → ℝ)
    (hmaps : ∀ z, 0 ≤ z → z ≤ y → 0 ≤ T z ∧ T z ≤ y)
    (hmono : ∀ z z', 0 ≤ z → z ≤ z' → z' ≤ y → T z ≤ T z') :
    ∃ z, 0 ≤ z ∧ z ≤ y ∧ T z = z := by
  have : Fact ((0 : V → ℝ) ≤ y) := ⟨hy⟩
  let f : Set.Icc (0 : V → ℝ) y →o Set.Icc (0 : V → ℝ) y :=
    { toFun := fun z => ⟨T z.1, hmaps z.1 z.2.1 z.2.2⟩
      monotone' := fun z z' h => hmono z.1 z'.1 z.2.1 h z'.2.2 }
  exact ⟨(OrderHom.lfp f).1, (OrderHom.lfp f).2.1, (OrderHom.lfp f).2.2,
    congrArg Subtype.val f.map_lfp⟩

/-- The deletion map `T(z)_i = y_i D^J_i(z) / D^S_i(y)` on the positive-source vertices `P`. -/
private noncomputable def delT (a : ℝ) (y : V → ℝ) (S J P : Finset V) (z : V → ℝ) : V → ℝ :=
  fun i => if i ∈ P then y i * diagD G a z J i / diagD G a y S i else 0

private lemma del_isUnit_diagonal {e : V → ℝ} (he : ∀ i, 1 ≤ e i) : IsUnit (diagonal e) := by
  rw [isUnit_iff_isUnit_det, det_diagonal]
  exact (Finset.prod_pos fun i _ => lt_of_lt_of_le one_pos (he i)).ne'.isUnit

private lemma del_conj_posDef_iff {e : V → ℝ} (he : ∀ i, 1 ≤ e i) (N : Matrix V V ℝ) :
    (diagonal e * N * diagonal e).PosDef ↔ N.PosDef := by
  have h := Matrix.IsUnit.posDef_star_left_conjugate_iff (x := N) (del_isUnit_diagonal he)
  rwa [star_eq_conjTranspose, diagonal_conjTranspose, star_trivial] at h

private lemma del_det_conj (e : V → ℝ) (N : Matrix V V ℝ) :
    (diagonal e * N * diagonal e).det = (∏ i, e i) ^ 2 * N.det := by
  rw [det_mul, det_mul, det_diagonal]
  ring

private lemma del_inv_conj_apply_le {e : V → ℝ} (he : ∀ i, 1 ≤ e i) {N : Matrix V V ℝ}
    (hN : N.PosDef) (i : V) : (diagonal e * N * diagonal e)⁻¹ i i ≤ N⁻¹ i i := by
  have he0 : ∀ i, e i ≠ 0 := fun i => (lt_of_lt_of_le one_pos (he i)).ne'
  have hNu : IsUnit N.det := (isUnit_iff_isUnit_det _).mp hN.isUnit
  have h1 : diagonal (fun i => (e i)⁻¹) * diagonal e = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    exact inv_mul_cancel₀ (he0 i)
  have hinv : (diagonal e * N * diagonal e)⁻¹ =
      diagonal (fun i => (e i)⁻¹) * N⁻¹ * diagonal (fun i => (e i)⁻¹) := by
    apply inv_eq_left_inv
    calc _ = diagonal (fun i => (e i)⁻¹) *
          (N⁻¹ * ((diagonal (fun i => (e i)⁻¹) * diagonal e) * N)) * diagonal e := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h1, Matrix.one_mul, nonsing_inv_mul _ hNu, Matrix.mul_one, h1]
  rw [hinv, mul_diagonal, diagonal_mul]
  have hpos : 0 < N⁻¹ i i := hN.inv.diag_pos
  have hei : 0 < (e i)⁻¹ := inv_pos.2 (lt_of_lt_of_le one_pos (he i))
  have hei1 : (e i)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (he i)
  calc (e i)⁻¹ * N⁻¹ i i * (e i)⁻¹ = ((e i)⁻¹ * (e i)⁻¹) * N⁻¹ i i := by ring
    _ ≤ 1 * N⁻¹ i i := mul_le_mul_of_nonneg_right (by nlinarith) hpos.le
    _ = N⁻¹ i i := one_mul _

/-- Through the congruences, `W_core(σ) = K · W_J(σ)` with `K = ((Π e⁺)² (Π e⁻)²)^p`. -/
private lemma del_wtCore_eq {p : ℕ} {a : ℝ} {yp ym yp' ym' ep em : V → ℝ} {S : Finset V}
    {v : V} (hep : ∀ i, 1 ≤ ep i) (hem : ∀ i, 1 ≤ em i)
    (hcp : ∀ (τ : ℝ) (σ : Config V),
      precCore G a τ yp σ S v = diagonal ep * precN G a τ yp' σ (S.erase v) * diagonal ep)
    (hcm : ∀ (τ : ℝ) (σ : Config V),
      precCore G a τ ym σ S v = diagonal em * precN G a τ ym' σ (S.erase v) * diagonal em)
    (σ : Config V) :
    wtCore G p a yp ym σ S v =
      ((∏ i, ep i) ^ 2 * (∏ i, em i) ^ 2) ^ p * wt G p a yp' ym' σ (S.erase v) := by
  unfold wtCore wt
  rw [hcp 1 σ, hcm (-1) σ]
  by_cases h : (precN G a 1 yp' σ (S.erase v)).PosDef ∧
      (precN G a (-1) ym' σ (S.erase v)).PosDef
  · rw [ite_eq_left ⟨(del_conj_posDef_iff hep _).2 h.1, (del_conj_posDef_iff hem _).2 h.2⟩,
      ite_eq_left h, del_det_conj, del_det_conj, ← mul_pow]
    congr 1
    ring
  · rw [ite_eq_right (fun h' => h ⟨(del_conj_posDef_iff hep _).1 h'.1,
      (del_conj_posDef_iff hem _).1 h'.2⟩), ite_eq_right h, mul_zero]

omit [DecidableEq V] in
private lemma del_K_pos (p : ℕ) {ep em : V → ℝ} (hep : ∀ i, 1 ≤ ep i) (hem : ∀ i, 1 ≤ em i) :
    0 < ((∏ i, ep i) ^ 2 * (∏ i, em i) ^ 2) ^ p :=
  pow_pos (mul_pos (pow_pos (Finset.prod_pos fun i _ => lt_of_lt_of_le one_pos (hep i)) 2)
    (pow_pos (Finset.prod_pos fun i _ => lt_of_lt_of_le one_pos (hem i)) 2)) p

private lemma del_ZwCore_eq {p : ℕ} {a : ℝ} {yp ym yp' ym' ep em : V → ℝ} {S : Finset V}
    {v : V} (hep : ∀ i, 1 ≤ ep i) (hem : ∀ i, 1 ≤ em i)
    (hcp : ∀ (τ : ℝ) (σ : Config V),
      precCore G a τ yp σ S v = diagonal ep * precN G a τ yp' σ (S.erase v) * diagonal ep)
    (hcm : ∀ (τ : ℝ) (σ : Config V),
      precCore G a τ ym σ S v = diagonal em * precN G a τ ym' σ (S.erase v) * diagonal em) :
    ZwCore G p a yp ym S v =
      ((∏ i, ep i) ^ 2 * (∏ i, em i) ^ 2) ^ p * Zw G p a yp' ym' (S.erase v) := by
  unfold ZwCore Zw
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun σ _ => del_wtCore_eq G hep hem hcp hcm σ

/-- The core expectation is the expectation of the law of `J` at the smaller sources. -/
private lemma del_coreE_eq {p : ℕ} {a : ℝ} {yp ym yp' ym' ep em : V → ℝ} {S : Finset V}
    {v : V} (hep : ∀ i, 1 ≤ ep i) (hem : ∀ i, 1 ≤ em i)
    (hcp : ∀ (τ : ℝ) (σ : Config V),
      precCore G a τ yp σ S v = diagonal ep * precN G a τ yp' σ (S.erase v) * diagonal ep)
    (hcm : ∀ (τ : ℝ) (σ : Config V),
      precCore G a τ ym σ S v = diagonal em * precN G a τ ym' σ (S.erase v) * diagonal em)
    (f : Config V → ℝ) :
    coreE G p a yp ym S v f =
      (∑ σ, wt G p a yp' ym' σ (S.erase v) * f σ) / Zw G p a yp' ym' (S.erase v) := by
  have hK := del_K_pos p hep hem
  have hZ := del_ZwCore_eq G (p := p) hep hem hcp hcm
  have hs : ∑ σ, wtCore G p a yp ym σ S v * f σ =
      ((∏ i, ep i) ^ 2 * (∏ i, em i) ^ 2) ^ p * ∑ σ, wt G p a yp' ym' σ (S.erase v) * f σ := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun σ _ => by rw [del_wtCore_eq G hep hem hcp hcm σ, mul_assoc]
  unfold coreE
  rw [hZ, hs, mul_div_mul_left _ _ hK.ne']

/-- On a supported signing, the inherited diagonal is at most the diagonal of the law of `J`. -/
private lemma del_wt_mul_le {p : ℕ} {a : ℝ} {yp ym : V → ℝ} {J : Finset V} (σ : Config V)
    {N : Matrix V V ℝ}
    (hNpd : (precN G a 1 yp σ J).PosDef ∧ (precN G a (-1) ym σ J).PosDef → N.PosDef)
    {e : V → ℝ} (he : ∀ i, 1 ≤ e i) (i : V) :
    wt G p a yp ym σ J * (diagonal e * N * diagonal e)⁻¹ i i ≤ wt G p a yp ym σ J * N⁻¹ i i := by
  unfold wt
  by_cases h : (precN G a 1 yp σ J).PosDef ∧ (precN G a (-1) ym σ J).PosDef
  · rw [ite_eq_left h]
    exact mul_le_mul_of_nonneg_left (del_inv_conj_apply_le he (hNpd h) i)
      (pow_nonneg (mul_nonneg h.1.det_pos.le h.2.det_pos.le) p)
  · rw [ite_eq_right h, zero_mul, zero_mul]

end DelAux

/-- `D-del`: the inherited core precision is a diagonal congruence of the precision of `J = S - v`
with smaller sources `ŷ ≤ y` (Knaster–Tarski on the box `[y/D^S(y), y]`). -/
theorem precCore_eq_congr (a : ℝ) {y : V → ℝ} (hy : ∀ i, 0 ≤ y i) {S : Finset V} {v : V}
    (hv : v ∈ S) :
    ∃ yh e : V → ℝ, (∀ i, 0 ≤ yh i ∧ yh i ≤ y i) ∧ (∀ i, 1 ≤ e i) ∧
      ∀ (τ : ℝ) (σ : Config V),
        precCore G a τ y σ S v = diagonal e * precN G a τ yh σ (S.erase v) * diagonal e := by
  obtain ⟨J, hJ⟩ : ∃ J, S.erase v = J := ⟨_, rfl⟩
  rw [hJ]
  have hJS : J ⊆ S := hJ ▸ Finset.erase_subset v S
  have hvJ : v ∉ J := hJ ▸ Finset.notMem_erase v S
  have hJmem : ∀ x, x ≠ v → (x ∈ J ↔ x ∈ S) := fun x hx => by
    rw [← hJ, Finset.mem_erase]
    exact ⟨fun h => h.2, fun h => ⟨hx, h⟩⟩
  obtain ⟨P, hP⟩ : ∃ P : Finset V, J.filter (fun i => 0 < y i) = P := ⟨_, rfl⟩
  have hPmem : ∀ i, i ∈ P ↔ i ∈ J ∧ 0 < y i := fun i => by rw [← hP, Finset.mem_filter]
  have hDS : ∀ i, 0 < diagD G a y S i :=
    fun i => lt_of_lt_of_le one_pos (del_one_le_diagD G a hy S i)
  -- the deletion map maps the box `[0, y]` into itself and is monotone
  have hmaps : ∀ z, 0 ≤ z → z ≤ y → 0 ≤ delT G a y S J P z ∧ delT G a y S J P z ≤ y := by
    intro z hz hzy
    refine ⟨fun i => ?_, fun i => ?_⟩
    · simp only [delT, Pi.zero_apply]
      split_ifs
      · exact div_nonneg (mul_nonneg (hy i)
          (le_trans zero_le_one (del_one_le_diagD G a hz J i))) (hDS i).le
      · exact le_rfl
    · simp only [delT]
      split_ifs
      · rw [div_le_iff₀ (hDS i)]
        exact mul_le_mul_of_nonneg_left (del_diagD_le G a hz hzy hJS i) (hy i)
      · exact hy i
  have hmono : ∀ z z', 0 ≤ z → z ≤ z' → z' ≤ y → delT G a y S J P z ≤ delT G a y S J P z' := by
    intro z z' hz hzz' _ i
    simp only [delT]
    split_ifs
    · exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (del_diagD_mono G a hz hzz' J i) (hy i)) (hDS i).le
    · exact le_rfl
  obtain ⟨yh, hyh0, hyhy, hfix⟩ :=
    del_exists_fixed (fun i => hy i) (delT G a y S J P) hmaps hmono
  have hfixi : ∀ i, yh i = if i ∈ P then y i * diagD G a yh J i / diagD G a y S i else 0 :=
    fun i => (congrFun hfix i).symm
  have hyh_off : ∀ i, i ∉ P → yh i = 0 := fun i hi => by rw [hfixi i, ite_eq_right hi]
  have hyh_pos : ∀ i ∈ P, 0 < yh i := fun i hi => by
    rw [hfixi i, ite_eq_left hi]
    exact div_pos (mul_pos ((hPmem i).1 hi).2
      (lt_of_lt_of_le one_pos (del_one_le_diagD G a hyh0 J i))) (hDS i)
  have hyh_eq : ∀ i ∈ P, yh i * diagD G a y S i = y i * diagD G a yh J i := fun i hi => by
    have h := hfixi i
    rw [ite_eq_left hi] at h
    rw [h, div_mul_cancel₀ _ (hDS i).ne']
  have hzero : ∀ i ∈ J, i ∉ P → y i = 0 := fun i hiJ hi =>
    le_antisymm (not_lt.1 fun h => hi ((hPmem i).2 ⟨hiJ, h⟩)) (hy i)
  -- the congruence factors
  obtain ⟨e, he⟩ : ∃ e : V → ℝ, (fun i => if i ∈ P then Real.sqrt (y i / yh i) else 1) = e :=
    ⟨_, rfl⟩
  have heP : ∀ i ∈ P, e i = Real.sqrt (y i / yh i) := fun i hi => by
    rw [← he]
    exact ite_eq_left hi
  have heN : ∀ i, i ∉ P → e i = 1 := fun i hi => by
    rw [← he]
    exact ite_eq_right hi
  have he1 : ∀ i, i ∉ J → e i = 1 := fun i hi => heN i fun h => hi ((hPmem i).1 h).1
  have hege : ∀ i, 1 ≤ e i := fun i => by
    by_cases hi : i ∈ P
    · rw [heP i hi, Real.one_le_sqrt, one_le_div (hyh_pos i hi)]
      exact hyhy i
    · rw [heN i hi]
  have hsq : ∀ u ∈ J, Real.sqrt (y u) = e u * Real.sqrt (yh u) := fun u hu => by
    by_cases hP' : u ∈ P
    · rw [heP u hP', ← Real.sqrt_mul (div_nonneg (hy u) (hyh_pos u hP').le),
        div_mul_cancel₀ _ (hyh_pos u hP').ne']
    · rw [heN u hP', hzero u hu hP', hyh_off u hP', one_mul]
  have hdiag : ∀ u ∈ J, diagD G a y S u = e u * diagD G a yh J u * e u := fun u hu => by
    by_cases hP' : u ∈ P
    · have hq := Real.mul_self_sqrt (div_nonneg (hy u) (hyh_pos u hP').le)
      have hyhu := (hyh_pos u hP').ne'
      rw [heP u hP', mul_right_comm, hq, div_mul_eq_mul_div, eq_div_iff hyhu]
      linear_combination hyh_eq u hP'
    · have h1 : diagD G a y S u = 1 := by
        simp [diagD, cEdge, hzero u hu hP', del_cRoot_zero]
      have h2 : diagD G a yh J u = 1 := by
        simp [diagD, cEdge, hyh_off u hP', del_cRoot_zero]
      rw [h1, h2, heN u hP']
      ring
  refine ⟨yh, e, fun i => ⟨hyh0 i, hyhy i⟩, hege, fun τ σ => ?_⟩
  ext u w
  rw [mul_diagonal, diagonal_mul]
  simp only [precCore, precN, of_apply]
  by_cases huv : u = v
  · have hu : u ∉ J := huv ▸ hvJ
    rw [ite_eq_left (Or.inl huv), he1 u hu]
    by_cases huw : u = w
    · have hw : w ∉ J := huw ▸ hu
      rw [ite_eq_left huw, ite_eq_left huw, ite_eq_right hu, he1 w hw]
      ring
    · rw [ite_eq_right huw, ite_eq_right huw, ite_eq_right (fun h => hu h.1)]
      ring
  · by_cases hwv : w = v
    · have hw : w ∉ J := hwv ▸ hvJ
      have huw : u ≠ w := fun h => huv (h.trans hwv)
      rw [ite_eq_left (Or.inr hwv), he1 w hw, ite_eq_right huw, ite_eq_right huw,
        ite_eq_right (fun h => hw h.2.1)]
      ring
    · rw [ite_eq_right (not_or.2 ⟨huv, hwv⟩)]
      by_cases huw : u = w
      · rw [ite_eq_left huw, ite_eq_left huw, ← huw]
        by_cases hu : u ∈ J
        · rw [ite_eq_left ((hJmem u huv).1 hu), ite_eq_left hu, hdiag u hu]
        · rw [ite_eq_right (fun h => hu ((hJmem u huv).2 h)), ite_eq_right hu, he1 u hu]
          ring
      · rw [ite_eq_right huw, ite_eq_right huw]
        by_cases hc : u ∈ J ∧ w ∈ J ∧ G.Adj u w
        · rw [ite_eq_left ⟨(hJmem u huv).1 hc.1, (hJmem w hwv).1 hc.2.1, hc.2.2⟩,
            ite_eq_left hc, hsq u hc.1, hsq w hc.2.1]
          ring
        · rw [ite_eq_right (fun h => hc ⟨(hJmem u huv).2 h.1, (hJmem w hwv).2 h.2.1, h.2.2⟩),
            ite_eq_right hc]
          ring

/-- `D-transfer` (existence): through the congruences, the inherited core law is a positive
multiple of the law of `J` with sources `ŷ^±`. -/
theorem ZwCore_pos_of_congr {p : ℕ} {a : ℝ} {yp ym yp' ym' ep em : V → ℝ} {S : Finset V} {v : V}
    (hep : ∀ i, 1 ≤ ep i) (hem : ∀ i, 1 ≤ em i)
    (hcp : ∀ (τ : ℝ) (σ : Config V),
      precCore G a τ yp σ S v = diagonal ep * precN G a τ yp' σ (S.erase v) * diagonal ep)
    (hcm : ∀ (τ : ℝ) (σ : Config V),
      precCore G a τ ym σ S v = diagonal em * precN G a τ ym' σ (S.erase v) * diagonal em)
    (hZ : 0 < Zw G p a yp' ym' (S.erase v)) : 0 < ZwCore G p a yp ym S v := by
  rw [del_ZwCore_eq G hep hem hcp hcm]
  exact mul_pos (del_K_pos p hep hem) hZ

/-- `D-transfer` (means): the inherited normalized core diagonals are `e_i^{-2} h_i^J(ŷ) ≤ h_i^J(ŷ)`
on supported signings, so their core means are bounded by the means of the law of `J` at `ŷ`. -/
theorem coreE_inv_le_of_congr {p : ℕ} {a : ℝ} {yp ym yp' ym' ep em : V → ℝ} {S : Finset V}
    {v : V} (hep : ∀ i, 1 ≤ ep i) (hem : ∀ i, 1 ≤ em i)
    (hcp : ∀ (τ : ℝ) (σ : Config V),
      precCore G a τ yp σ S v = diagonal ep * precN G a τ yp' σ (S.erase v) * diagonal ep)
    (hcm : ∀ (τ : ℝ) (σ : Config V),
      precCore G a τ ym σ S v = diagonal em * precN G a τ ym' σ (S.erase v) * diagonal em)
    (hZ : 0 < Zw G p a yp' ym' (S.erase v)) (i : V) {B : ℝ}
    (hplus : lawE G p a yp' ym' (S.erase v) (fun σ => hN G a 1 yp' σ (S.erase v) i) ≤ B)
    (hminus : lawE G p a yp' ym' (S.erase v) (fun σ => hN G a (-1) ym' σ (S.erase v) i) ≤ B) :
    coreE G p a yp ym S v (fun σ => (precCore G a 1 yp σ S v)⁻¹ i i) ≤ B ∧
      coreE G p a yp ym S v (fun σ => (precCore G a (-1) ym σ S v)⁻¹ i i) ≤ B := by
  constructor
  · calc coreE G p a yp ym S v (fun σ => (precCore G a 1 yp σ S v)⁻¹ i i)
        = (∑ σ, wt G p a yp' ym' σ (S.erase v) * (precCore G a 1 yp σ S v)⁻¹ i i) /
            Zw G p a yp' ym' (S.erase v) := del_coreE_eq G hep hem hcp hcm _
      _ ≤ (∑ σ, wt G p a yp' ym' σ (S.erase v) * hN G a 1 yp' σ (S.erase v) i) /
            Zw G p a yp' ym' (S.erase v) := by
          refine div_le_div_of_nonneg_right (Finset.sum_le_sum fun σ _ => ?_) hZ.le
          rw [hcp 1 σ]
          exact del_wt_mul_le G σ And.left hep i
      _ ≤ B := hplus
  · calc coreE G p a yp ym S v (fun σ => (precCore G a (-1) ym σ S v)⁻¹ i i)
        = (∑ σ, wt G p a yp' ym' σ (S.erase v) * (precCore G a (-1) ym σ S v)⁻¹ i i) /
            Zw G p a yp' ym' (S.erase v) := del_coreE_eq G hep hem hcp hcm _
      _ ≤ (∑ σ, wt G p a yp' ym' σ (S.erase v) * hN G a (-1) ym' σ (S.erase v) i) /
            Zw G p a yp' ym' (S.erase v) := by
          refine div_le_div_of_nonneg_right (Finset.sum_le_sum fun σ _ => ?_) hZ.le
          rw [hcm (-1) σ]
          exact del_wt_mul_le G σ And.right hem i
      _ ≤ B := hminus

end BiluLinial.Tight
