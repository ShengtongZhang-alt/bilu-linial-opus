/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.Contact.Leaves2

/-!
# Fixed-mask and weak-loop score leaves (Section 1.5, (FS1)–(FS5))

The leaves FS1 and FS5 of Section 1.5. FS1 uses (D8) (`Contact/Leaves2.lean`); FS5 uses FS1, the
mask bound BM4 (`Contact/LeavesX.lean`) and the route input `in_DR1` (`Contact/RouteDR1.lean`).
Checks: `docs/tight/CHECK_CONTACT_LEAVES.md` §4 (L8, L15).

**New node FS2** (source (FS2), l.1686–1695; AUDIT-D §3.4), the exact Schur identity used by FS1.
Pure form (`fs2_schur`, `fs2_mask`): if `M'` is `M` with row and column `i` replaced by those of
the identity (`l3_IsCore`), `M, M'` invertible, `X = D_s M⁻¹ D_s`, `C = D_s M'⁻¹ D_s`, then for
`j, k ≠ i`
* (FS2a) `X_ii X_jk - X_ji X_ik = X_ii C_jk`;
* (FS2b) `X_ki = -X_ii Σ_{l ≠ i} C_kl w_l` whenever `M_li = s_l s_i w_l` (`l ≠ i`);
* hence, for any mask `f`, `F_ji = -(X_e)_ii (X_n)_ii Σ_{k,l ≠ i} (C_e)_jk f_k (C_n)_kl w_l`.

Contact form (`fs2`): on the support, for `i ∈ N`, `j ∈ J = N_S(i)` and either branch `e`,
`F_ji = -a (X_e)_ii (X₊)_ii ((T_dir ξ)_j + (T_cav ξ)_j)`, with the cavity maps `T_dir`, `T_cav` of
(WT1) (`Contact.tDir`, `Contact.tCav`) and `ξ` the star vector at `i`. Numerically checked
(`scripts/tight/check_fs2.py`: residual `5·10⁻¹⁶` on 199 supported instances with zero sources and
`S ⊊ V`; pure identities `10⁻¹²` on random non-symmetric matrices).

**New node FS4** (`fs4_root`, source (FS4), l.1743–1751): on the support, for `i ∈ N`, `j ∼ i`,
`(∂_ij Ω_±)² ≤ Ω_± · 4 a² D_*² (x_i² + z_i²)` (checked in the same script).

**Proof structure.**
* FS1 (`l3_fs1_of_d8`, then `fs1_fixed_mask`): FS2 gives `H Σ_j F_ji² ≤ 2a²(H q_dir + H q_cav)`
  (`l3_fs1_pt`); WT2 (`SecB.wt2 2 2`) passes to `tr L`; the direct trace is bounded pointwise by
  `(2D_*⁶/d) Σ_{l∈J∩N} ((X_e²)_ll + (X_e²)_ii)` (`l3_dir_pt`) and then by W5 (`in_W5 8`); the
  cavity trace by `8D_*²h⁻²(Y₁ + a²(D_*/h)Y₂)` (`l3_cav_pt`, `l3_fs1_cav`, from `‖X_e‖ ≤ h⁻¹`
  (`l3_shift_sq_le`) and `(X²)_ii ≤ G_ii/h`), with the exact identities `Y₁ = 4uᵀ(K₊-M₊)b₊`,
  `Y₂ = 4uᵀ(K₊-M₊)u` (`l3_Y1_eq`, `l3_Y2_eq`); `H ≤ 5D_*²Ω₊` uses `Ω₊ ≥ 1/5` (`l3_omP_ge_of`,
  from D8 and `G⁺_vv ≥ y_v/D_v`, `D_v ≤ 2`); UMI against `D_*` is `l3_umi`.
* FS5 (`l3_fs5_of`, then `fs5_scores`): joint Cauchy–Schwarz (`l3_score_le`) with FS4, DR1 at
  every `i ∈ N` (`l3_fs5_B`), (C2) at the root (`l3_fs5_G`), FS1 for the `u`-scores and BM4 at
  `m = 0` for the `b`-scores; the closing arithmetic is `l3_fs5_key`, `l3_fs5_finU/B`.
-/

@[expose] public section

namespace BiluLinial.Tight

open Matrix Finset

universe u

variable {d p : ℕ}

/-! ### FS2: the exact Schur identity -/

section FS2

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `M'` is `M` with row and column `i` replaced by those of the identity. -/
structure l3_IsCore (M M' : Matrix ι ι ℝ) (i : ι) : Prop where
  off : ∀ u w, u ≠ i → w ≠ i → M' u w = M u w
  row : ∀ w, w ≠ i → M' i w = 0
  col : ∀ u, u ≠ i → M' u i = 0
  diag : M' i i = 1

theorem l3_core_mul_inv_off {M M' : Matrix ι ι ℝ} {i : ι} (hc : l3_IsCore M M' i)
    (hM : IsUnit M.det) {m : ι} (hm : m ≠ i) (k : ι) :
    (M' * M⁻¹) m k = (if m = k then 1 else 0) - M m i * M⁻¹ i k := by
  have hMN : (M * M⁻¹) m k = if m = k then 1 else 0 := by
    rw [mul_nonsing_inv _ hM, one_apply]
  rw [mul_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hMN ⊢
  rw [hc.col m hm, zero_mul, zero_add]
  have : ∑ l ∈ univ.erase i, M' m l * M⁻¹ l k = ∑ l ∈ univ.erase i, M m l * M⁻¹ l k :=
    Finset.sum_congr rfl fun l hl => by rw [hc.off m l hm (Finset.ne_of_mem_erase hl)]
  rw [this]
  linarith

theorem l3_core_mul_inv_row {M M' : Matrix ι ι ℝ} {i : ι} (hc : l3_IsCore M M' i) (k : ι) :
    (M' * M⁻¹) i k = M⁻¹ i k := by
  rw [mul_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), hc.diag, one_mul,
    Finset.sum_eq_zero fun l hl => by rw [hc.row l (Finset.ne_of_mem_erase hl), zero_mul],
    add_zero]

theorem l3_core_inv_col {M M' : Matrix ι ι ℝ} {i : ι} (hc : l3_IsCore M M' i)
    (hM' : IsUnit M'.det) {k : ι} (hk : k ≠ i) : M'⁻¹ k i = 0 := by
  have h := congrFun (congrFun (nonsing_inv_mul M' hM') k) i
  rw [one_apply_ne hk, mul_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), hc.diag,
    mul_one, Finset.sum_eq_zero fun l hl => by rw [hc.col l (Finset.ne_of_mem_erase hl), mul_zero],
    add_zero] at h
  exact h

/-- `M⁻¹ = M'⁻¹ (M' M⁻¹)`, expanded entrywise. -/
theorem l3_inv_expand {M M' : Matrix ι ι ℝ} {i : ι} (hc : l3_IsCore M M' i) (hM : IsUnit M.det)
    (hM' : IsUnit M'.det) (j k : ι) :
    M⁻¹ j k = M'⁻¹ j i * M⁻¹ i k +
      ∑ m ∈ univ.erase i, M'⁻¹ j m * ((if m = k then 1 else 0) - M m i * M⁻¹ i k) := by
  have h1 : M⁻¹ = M'⁻¹ * (M' * M⁻¹) := by
    rw [← Matrix.mul_assoc, nonsing_inv_mul M' hM', Matrix.one_mul]
  conv_lhs => rw [h1]
  rw [mul_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), l3_core_mul_inv_row hc]
  congr 1
  exact Finset.sum_congr rfl fun m hm => by
    rw [l3_core_mul_inv_off hc hM (Finset.ne_of_mem_erase hm)]

/-- Column `i` of `M⁻¹` through the core: `N_ki = -N_ii Σ_{m ≠ i} N'_km M_mi` (`k ≠ i`). -/
theorem l3_schur_col {M M' : Matrix ι ι ℝ} {i : ι} (hc : l3_IsCore M M' i) (hM : IsUnit M.det)
    (hM' : IsUnit M'.det) {k : ι} (hk : k ≠ i) :
    M⁻¹ k i = -(M⁻¹ i i) * ∑ m ∈ univ.erase i, M'⁻¹ k m * M m i := by
  rw [l3_inv_expand hc hM hM' k i, l3_core_inv_col hc hM' hk, zero_mul, zero_add, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [if_neg (Finset.ne_of_mem_erase hm)]
  ring

/-- The Schur minor: `N_ii N_jk - N_ji N_ik = N_ii N'_jk` (`j, k ≠ i`). -/
theorem l3_schur_minor {M M' : Matrix ι ι ℝ} {i : ι} (hc : l3_IsCore M M' i) (hM : IsUnit M.det)
    (hM' : IsUnit M'.det) {j k : ι} (hj : j ≠ i) (hk : k ≠ i) :
    M⁻¹ i i * M⁻¹ j k - M⁻¹ j i * M⁻¹ i k = M⁻¹ i i * M'⁻¹ j k := by
  have e1 := l3_inv_expand hc hM hM' j k
  rw [l3_core_inv_col hc hM' hj, zero_mul, zero_add] at e1
  have e2 : ∑ m ∈ univ.erase i, M'⁻¹ j m * ((if m = k then 1 else 0) - M m i * M⁻¹ i k) =
      M'⁻¹ j k - M⁻¹ i k * ∑ m ∈ univ.erase i, M'⁻¹ j m * M m i := by
    have e : ∀ m ∈ univ.erase i, M'⁻¹ j m * ((if m = k then 1 else 0) - M m i * M⁻¹ i k) =
        (if m = k then M'⁻¹ j m else 0) - M⁻¹ i k * (M'⁻¹ j m * M m i) := fun m _ => by
      split_ifs <;> ring
    rw [Finset.sum_congr rfl e, Finset.sum_sub_distrib, Finset.sum_ite_eq' (univ.erase i) k,
      if_pos (Finset.mem_erase.2 ⟨hk, Finset.mem_univ k⟩), Finset.mul_sum]
  have e3 := l3_schur_col hc hM hM' hj
  rw [e1, e2, e3]
  ring

/-- **FS2a, FS2b** (exact Schur complementation, physical form). With `X = D_s M⁻¹ D_s` and
`C = D_s M'⁻¹ D_s`: `X_ii X_jk - X_ji X_ik = X_ii C_jk` for `j, k ≠ i`, and, if
`M_li = s_l s_i w_l` for `l ≠ i`, `X_ki = -X_ii Σ_{l ≠ i} C_kl w_l` for `k ≠ i`. -/
theorem fs2_schur {M M' : Matrix ι ι ℝ} {i : ι} (hc : l3_IsCore M M' i) (hM : IsUnit M.det)
    (hM' : IsUnit M'.det) (s : ι → ℝ) :
    (∀ j k, j ≠ i → k ≠ i →
      s i * M⁻¹ i i * s i * (s j * M⁻¹ j k * s k) - s j * M⁻¹ j i * s i * (s i * M⁻¹ i k * s k) =
        s i * M⁻¹ i i * s i * (s j * M'⁻¹ j k * s k)) ∧
    (∀ w : ι → ℝ, (∀ l, l ≠ i → M l i = s l * s i * w l) → ∀ k, k ≠ i →
      s k * M⁻¹ k i * s i =
        -(s i * M⁻¹ i i * s i) * ∑ l ∈ univ.erase i, s k * M'⁻¹ k l * s l * w l) := by
  constructor
  · intro j k hj hk
    linear_combination (s i * s i * s j * s k) * l3_schur_minor hc hM hM' hj hk
  · intro w hw k hk
    rw [l3_schur_col hc hM hM' hk]
    have : ∑ m ∈ univ.erase i, M'⁻¹ k m * M m i =
        ∑ m ∈ univ.erase i, M'⁻¹ k m * (s m * s i * w m) :=
      Finset.sum_congr rfl fun m hm => by rw [hw m (Finset.ne_of_mem_erase hm)]
    rw [this]
    simp only [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun m _ => by ring

/-- **FS2** (pure form). If `X_e, C_e` satisfy FS2a and `X_n, C_n, w` satisfy FS2b at `i`, then for
`j ≠ i` and any mask `f`: `F_ji = -(X_e)_ii (X_n)_ii Σ_{k,l ≠ i} (C_e)_jk f_k (C_n)_kl w_l`. -/
theorem fs2_mask (Xe Xn Ce Cn : Matrix ι ι ℝ) (wn f : ι → ℝ) {i j : ι}
    (hE : ∀ k, k ≠ i → Xe i i * Xe j k - Xe j i * Xe i k = Xe i i * Ce j k)
    (hN : ∀ k, k ≠ i → Xn k i = -(Xn i i) * ∑ l ∈ univ.erase i, Cn k l * wn l) :
    maskF Xe Xn f j i =
      -(Xe i i * Xn i i) *
        ∑ k ∈ univ.erase i, ∑ l ∈ univ.erase i, Ce j k * f k * Cn k l * wn l := by
  have hU : ∀ a b, (Xe * diagonal f * Xn) a b = ∑ k, Xe a k * f k * Xn k b := by
    intro a b; rw [mul_apply]; simp only [mul_diagonal]
  have e1 : maskF Xe Xn f j i = ∑ k, f k * Xn k i * (Xe i i * Xe j k - Xe j i * Xe i k) := by
    unfold maskF
    rw [hU, hU, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [e1, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have e2 : f i * Xn i i * (Xe i i * Xe j i - Xe j i * Xe i i) = 0 := by ring
  rw [e2, zero_add, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hki := Finset.ne_of_mem_erase hk
  rw [hE k hki, hN k hki]
  simp only [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun l _ => by ring

/-- The core of a positive definite matrix is positive definite. -/
theorem l3_core_posDef {M M' : Matrix ι ι ℝ} {i : ι} (hc : l3_IsCore M M' i) (hM : M.PosDef) :
    M'.PosDef := by
  have hsym : M'.IsHermitian := by
    refine Matrix.IsHermitian.ext fun u w => ?_
    simp only [star_trivial]
    by_cases hu : u = i
    · subst hu
      by_cases hw : w = u
      · subst hw; rfl
      · rw [hc.col w hw, hc.row w hw]
    · by_cases hw : w = i
      · subst hw; rw [hc.row u hu, hc.col u hu]
      · rw [hc.off w u hw hu, hc.off u w hu hw]
        simpa using hM.1.apply u w
  refine PosDef.of_dotProduct_mulVec_pos hsym fun x hx => ?_
  set x' : ι → ℝ := fun k => if k = i then 0 else x k with hx'def
  have hMx : ∀ u, u ≠ i → (M' *ᵥ x) u = (M *ᵥ x') u := by
    intro u hu
    simp only [mulVec, dotProduct]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
      ← Finset.add_sum_erase _ _ (Finset.mem_univ i), hc.col u hu]
    have hx'i : x' i = 0 := by simp [hx'def]
    rw [hx'i, zero_mul, mul_zero, zero_add, zero_add]
    exact Finset.sum_congr rfl fun w hw => by
      rw [hc.off u w hu (Finset.ne_of_mem_erase hw)]
      congr 1
      simp [hx'def, Finset.ne_of_mem_erase hw]
  have hMi : (M' *ᵥ x) i = x i := by
    simp only [mulVec, dotProduct]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), hc.diag, one_mul,
      Finset.sum_eq_zero fun w hw => by rw [hc.row w (Finset.ne_of_mem_erase hw), zero_mul],
      add_zero]
  have hx'i : x' i = 0 := by simp [hx'def]
  have hx'w : ∀ w ∈ univ.erase i, x' w = x w := fun w hw => by
    simp [hx'def, Finset.ne_of_mem_erase hw]
  have key : star x ⬝ᵥ (M' *ᵥ x) = star x' ⬝ᵥ (M *ᵥ x') + x i ^ 2 := by
    simp only [star_trivial, dotProduct]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
      ← Finset.add_sum_erase _ _ (Finset.mem_univ i), hMi, hx'i, zero_mul, zero_add]
    have s1 : ∑ w ∈ univ.erase i, x w * (M' *ᵥ x) w =
        ∑ w ∈ univ.erase i, x' w * (M *ᵥ x') w :=
      Finset.sum_congr rfl fun w hw => by
        rw [hMx w (Finset.ne_of_mem_erase hw), hx'w w hw]
    rw [s1]
    ring
  rw [key]
  by_cases hx0 : x' = 0
  · have hxi : x i ≠ 0 := by
      intro hxi
      apply hx
      funext k
      by_cases hk : k = i
      · rw [hk, hxi]; rfl
      · have := congrFun hx0 k
        simpa [hx'def, hk] using this
    rw [hx0]
    simp only [mulVec_zero, dotProduct_zero, zero_add]
    positivity
  · have := hM.dotProduct_mulVec_pos hx0
    nlinarith [sq_nonneg (x i)]

end FS2

/-! ### FS2 at a contact -/

section FS2Contact

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem l3_isCore (a τ h : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) (i : V) :
    l3_IsCore (precN G a τ y σ S + h • srcDiag y S)
      (precCore G a τ y σ S i + h • srcDiag y (S.erase i)) i where
  off u w hu hw := by
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, precCore, of_apply, hu, hw, or_self,
      if_false]
    congr 2
    unfold srcDiag
    by_cases huw : u = w
    · subst huw; simp [Finset.mem_erase, hu]
    · simp [diagonal_apply_ne _ huw]
  row w hw := by
    simp [precCore, srcDiag, diagonal_apply_ne _ (Ne.symm hw), Ne.symm hw]
  col u hu := by
    simp [precCore, srcDiag, diagonal_apply_ne _ hu, hu]
  diag := by simp [precCore, srcDiag]

theorem l3_srcDiag_psd {h : ℝ} (hh : 0 ≤ h) {y : V → ℝ} (hy : ∀ k, 0 ≤ y k)
    (S : Finset V) : (h • srcDiag y S).PosSemidef := by
  refine Matrix.PosSemidef.smul ?_ hh
  refine Matrix.PosSemidef.diagonal fun k => ?_
  split_ifs
  · exact hy k
  · exact le_rfl

theorem l3_shift_posDef {a τ h : ℝ} {y : V → ℝ} {σ : Config V} {S : Finset V} (hy : ∀ k, 0 ≤ y k)
    (hh : 0 ≤ h) (hP : (precN G a τ y σ S).PosDef) :
    (precN G a τ y σ S + h • srcDiag y S).PosDef :=
  hP.add_posSemidef (l3_srcDiag_psd hh hy S)

theorem l3_sgn_comm (σ : Config V) (u w : V) : sgn σ u w = sgn σ w u := by
  unfold sgn; rw [Sym2.eq_swap]

/-- FS2a and FS2b for one branch of a contact (on the support, `i ∈ S`). -/
theorem l3_branch_schur {a τ h : ℝ} {y : V → ℝ} {σ : Config V} {S : Finset V} {i : V}
    (hi : i ∈ S) (hy : ∀ k, 0 ≤ y k) (hh : 0 ≤ h) (hP : (precN G a τ y σ S).PosDef) :
    (∀ j k, j ≠ i → k ≠ i →
      shiftP G a τ h y σ S i i * shiftP G a τ h y σ S j k -
          shiftP G a τ h y σ S j i * shiftP G a τ h y σ S i k =
        shiftP G a τ h y σ S i i * coreShift G a τ h y σ S i j k) ∧
    (∀ k, k ≠ i → shiftP G a τ h y σ S k i =
      -(shiftP G a τ h y σ S i i) * ∑ l ∈ univ.erase i, coreShift G a τ h y σ S i k l *
        (if l ∈ nbhd G S i then τ * a * sgn σ i l else 0)) := by
  have hc := l3_isCore G a τ h y σ S i
  have hMpd := l3_shift_posDef G hy hh hP
  have hMu : IsUnit (precN G a τ y σ S + h • srcDiag y S).det :=
    isUnit_iff_ne_zero.mpr hMpd.det_pos.ne'
  have hM'u : IsUnit (precCore G a τ y σ S i + h • srcDiag y (S.erase i)).det :=
    isUnit_iff_ne_zero.mpr (l3_core_posDef hc hMpd).det_pos.ne'
  obtain ⟨hA, hB⟩ := fs2_schur hc hMu hM'u (fun k => Real.sqrt (y k))
  refine ⟨fun j k hj hk => hA j k hj hk, fun k hk => ?_⟩
  refine hB _ (fun l hl => ?_) k hk
  have hil : i ≠ l := Ne.symm hl
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, srcDiag, diagonal_apply_ne _ hl, mul_zero,
    add_zero, precN, of_apply, hl, if_false]
  by_cases hn : l ∈ nbhd G S i
  · have hn' : l ∈ S ∧ G.Adj i l := by simpa [nbhd] using hn
    rw [if_pos ⟨hn'.1, hi, hn'.2.symm⟩, if_pos hn, l3_sgn_comm σ l i]
    ring
  · have hn' : ¬ (l ∈ S ∧ i ∈ S ∧ G.Adj l i) := fun h' =>
      hn (by simp [nbhd, h'.1, h'.2.2.symm])
    rw [if_neg hn', if_neg hn, mul_zero]

/-! ### Norm bounds for the shifted inverse -/

/-- `x ⬝ P̃ x ≥ Σ_{k ∉ S} x_k²` (the normalized precision is the identity off `S`). -/
theorem l3_precN_quad_ge {a τ : ℝ} {y : V → ℝ} {σ : Config V} {S : Finset V}
    (hP : (precN G a τ y σ S).PosDef) (x : V → ℝ) :
    ∑ k, (if k ∈ S then 0 else x k ^ 2) ≤ x ⬝ᵥ (precN G a τ y σ S *ᵥ x) := by
  set P := precN G a τ y σ S with hPdef
  set x₁ : V → ℝ := fun k => if k ∈ S then x k else 0 with hx₁
  have h1 : 0 ≤ x₁ ⬝ᵥ (P *ᵥ x₁) := by
    simpa using hP.posSemidef.dotProduct_mulVec_nonneg x₁
  have hterm : ∀ u w, x u * (P u w * x w) - x₁ u * (P u w * x₁ w) =
      if u = w then (if u ∈ S then 0 else x u ^ 2) else 0 := by
    intro u w
    by_cases huw : u = w
    · subst huw
      by_cases hu : u ∈ S
      · simp [hx₁, hu]
      · simp only [hx₁, hu, if_false, if_true, hPdef, precN, of_apply]
        ring
    · by_cases h2 : u ∈ S ∧ w ∈ S
      · simp [hx₁, h2.1, h2.2, huw]
      · have hP0 : P u w = 0 := by
          simp only [hPdef, precN, of_apply, huw, if_false]
          rw [if_neg (fun h' => h2 ⟨h'.1, h'.2.1⟩)]
        simp [hP0, huw]
  have hdiff : x ⬝ᵥ (P *ᵥ x) - x₁ ⬝ᵥ (P *ᵥ x₁) = ∑ k, (if k ∈ S then 0 else x k ^ 2) := by
    simp only [dotProduct, mulVec, Finset.mul_sum, ← Finset.sum_sub_distrib]
    rw [Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun w _ => hterm u w]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  linarith

/-- `w ⬝ X w ≤ h⁻¹ |w|²` for the physical shifted inverse `X` (on the support, `h y ≤ 1`). -/
theorem l3_shift_quad_le {a τ h : ℝ} {y : V → ℝ} {σ : Config V} {S : Finset V}
    (hy : ∀ k, 0 ≤ y k) (hh : 0 < h) (hyh : ∀ k, h * y k ≤ 1) (hP : (precN G a τ y σ S).PosDef)
    (w : V → ℝ) :
    w ⬝ᵥ (SecB.shiftMat G a τ h y σ S *ᵥ w) ≤ h⁻¹ * (w ⬝ᵥ w) := by
  set P := precN G a τ y σ S with hPdef
  set Q := P + h • srcDiag y S with hQdef
  have hQpd : Q.PosDef := hP.add_posSemidef (l3_srcDiag_psd hh.le hy S)
  have hQu : IsUnit Q.det := isUnit_iff_ne_zero.mpr hQpd.det_pos.ne'
  set z : V → ℝ := fun k => Real.sqrt (y k) * w k with hz
  set x : V → ℝ := Q⁻¹ *ᵥ z with hx
  have hQx : Q *ᵥ x = z := by rw [hx, mulVec_mulVec, mul_nonsing_inv _ hQu, one_mulVec]
  have hL : w ⬝ᵥ (SecB.shiftMat G a τ h y σ S *ᵥ w) = z ⬝ᵥ x := by
    simp only [dotProduct, mulVec, SecB.shiftMat, of_apply, shiftP, hz, hx]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by rw [hQdef]; ring
  set T := z ⬝ᵥ x with hT
  set R := ∑ k, y k * x k ^ 2 with hR
  have hD : x ⬝ᵥ (srcDiag y S *ᵥ x) = ∑ k, (if k ∈ S then y k else 0) * x k ^ 2 := by
    simp only [srcDiag, mulVec_diagonal, dotProduct]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hTQ : T = x ⬝ᵥ (P *ᵥ x) + h * ∑ k, (if k ∈ S then y k else 0) * x k ^ 2 := by
    have : T = x ⬝ᵥ (Q *ᵥ x) := by rw [hQx, hT, dotProduct_comm]
    rw [this, hQdef, add_mulVec, dotProduct_add, smul_mulVec, dotProduct_smul, smul_eq_mul,
      hD]
  have hP1 : ∑ k, (if k ∈ S then 0 else x k ^ 2) ≤ x ⬝ᵥ (P *ᵥ x) := l3_precN_quad_ge G hP x
  have hTR : h * R ≤ T := by
    have hsum : ∑ k, h * (y k * x k ^ 2) ≤
        ∑ k, ((if k ∈ S then 0 else x k ^ 2) + h * ((if k ∈ S then y k else 0) * x k ^ 2)) :=
      Finset.sum_le_sum fun k _ => by
        by_cases hk : k ∈ S
        · simp [hk]
        · simp only [hk, if_false, zero_mul, mul_zero, add_zero]
          nlinarith [hyh k, sq_nonneg (x k)]
    have e1 : h * R = ∑ k, h * (y k * x k ^ 2) := by rw [hR, Finset.mul_sum]
    have e2 : ∑ k, ((if k ∈ S then 0 else x k ^ 2) + h * ((if k ∈ S then y k else 0) * x k ^ 2)) =
        ∑ k, (if k ∈ S then 0 else x k ^ 2) + h * ∑ k, (if k ∈ S then y k else 0) * x k ^ 2 := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    linarith
  have hCS : T ^ 2 ≤ (w ⬝ᵥ w) * R := by
    have h0 := Finset.sum_mul_sq_le_sq_mul_sq univ w (fun k => Real.sqrt (y k) * x k)
    have e1 : T = ∑ k, w k * (Real.sqrt (y k) * x k) := by
      rw [hT]; simp only [dotProduct, hz]; exact Finset.sum_congr rfl fun k _ => by ring
    have e2 : ∑ k, (Real.sqrt (y k) * x k) ^ 2 = R := by
      rw [hR]; exact Finset.sum_congr rfl fun k _ => by rw [mul_pow, Real.sq_sqrt (hy k)]
    have e3 : ∑ k, w k ^ 2 = w ⬝ᵥ w := by simp only [dotProduct, sq]
    rw [e1]; rw [e2, e3] at h0; exact h0
  have hW0 : 0 ≤ w ⬝ᵥ w := by
    simp only [dotProduct]; exact Finset.sum_nonneg fun k _ => mul_self_nonneg _
  rw [hL]
  rcases le_or_gt T 0 with hT0 | hT0
  · exact hT0.trans (by positivity)
  · have h1 : h * T ^ 2 ≤ (w ⬝ᵥ w) * T := by
      calc h * T ^ 2 ≤ h * ((w ⬝ᵥ w) * R) := mul_le_mul_of_nonneg_left hCS hh.le
        _ = (w ⬝ᵥ w) * (h * R) := by ring
        _ ≤ (w ⬝ᵥ w) * T := mul_le_mul_of_nonneg_left hTR hW0
    have h2 : h * T ≤ w ⬝ᵥ w := by nlinarith
    calc T = h⁻¹ * (h * T) := by field_simp
      _ ≤ h⁻¹ * (w ⬝ᵥ w) := mul_le_mul_of_nonneg_left h2 (inv_nonneg.2 hh.le)

/-- The physical shifted inverse is positive semidefinite on the support. -/
theorem l3_shift_posSemidef {a τ h : ℝ} {y : V → ℝ} {σ : Config V} {S : Finset V}
    (hy : ∀ k, 0 ≤ y k) (hh : 0 ≤ h) (hP : (precN G a τ y σ S).PosDef) :
    (SecB.shiftMat G a τ h y σ S).PosSemidef := by
  have hQpd := l3_shift_posDef G hy hh hP
  set D : Matrix V V ℝ := diagonal fun k => Real.sqrt (y k) with hDdef
  have e : SecB.shiftMat G a τ h y σ S =
      Dᴴ * (precN G a τ y σ S + h • srcDiag y S)⁻¹ * D := by
    ext k l
    simp only [SecB.shiftMat, shiftP, of_apply, hDdef, diagonal_conjTranspose, mul_diagonal,
      diagonal_mul, Pi.star_apply, star_trivial]
  rw [e]
  exact hQpd.inv.posSemidef.conjTranspose_mul_mul_same D

/-- `|X w|² ≤ h⁻² |w|²` (on the support, `h y ≤ 1`). -/
theorem l3_shift_sq_le {a τ h : ℝ} {y : V → ℝ} {σ : Config V} {S : Finset V}
    (hy : ∀ k, 0 ≤ y k) (hh : 0 < h) (hyh : ∀ k, h * y k ≤ 1) (hP : (precN G a τ y σ S).PosDef)
    (w : V → ℝ) :
    ∑ j, (SecB.shiftMat G a τ h y σ S *ᵥ w) j ^ 2 ≤ h⁻¹ ^ 2 * ∑ j, w j ^ 2 := by
  set X := SecB.shiftMat G a τ h y σ S with hXdef
  have hX := l3_shift_posSemidef G hy hh.le hP
  have hXt : Xᵀ = X := by
    have := hX.1.eq; rwa [conjTranspose_eq_transpose_of_trivial] at this
  have hXn : (h⁻¹ • (1 : Matrix V V ℝ) - X).PosSemidef := by
    refine PosSemidef.of_dotProduct_mulVec_nonneg
      ((isHermitian_one.smul (IsSelfAdjoint.all _)).sub hX.1) fun v => ?_
    simp only [star_trivial, sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub,
      dotProduct_smul, smul_eq_mul]
    linarith [l3_shift_quad_le G hy hh hyh hP v]
  have h2 := posSemidef_smul_sub_mul_self hX (inv_nonneg.2 hh.le) hXn
  have q1 := h2.dotProduct_mulVec_nonneg w
  simp only [star_trivial, sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul,
    smul_eq_mul] at q1
  have q2 := l3_shift_quad_le G hy hh hyh hP w
  have e : ∑ j, (X *ᵥ w) j ^ 2 = w ⬝ᵥ ((X * X) *ᵥ w) := by
    rw [← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose, hXt]
    simp only [dotProduct, sq]
  have e2 : ∑ j, w j ^ 2 = w ⬝ᵥ w := by simp only [dotProduct, sq]
  rw [e, e2]
  have hi0 : 0 ≤ h⁻¹ := inv_nonneg.2 hh.le
  nlinarith [mul_le_mul_of_nonneg_left q2 hi0]

/-- Splitting the FS2 double sum into the direct (`k = l`) and cavity (`k ≠ l`) parts. -/
theorem l3_sum_split (N J : Finset V) (i : V) (hJ : J ⊆ univ.erase i) (g : V → V → ℝ)
    (hg : ∀ k l, k ∉ N → g k l = 0) (c : V → ℝ) :
    ∑ k ∈ univ.erase i, ∑ l ∈ univ.erase i, g k l * (if l ∈ J then c l else 0) =
      ∑ l ∈ J, ((if l ∈ N then g l l else 0) + ∑ k ∈ (N.erase i).erase l, g k l) * c l := by
  rw [Finset.sum_comm]
  have e1 : ∀ l ∈ univ.erase i, ∑ k ∈ univ.erase i, g k l * (if l ∈ J then c l else 0) =
      if l ∈ J then (∑ k ∈ univ.erase i, g k l) * c l else 0 := fun l _ => by
    rw [← Finset.sum_mul]; split_ifs <;> simp
  rw [Finset.sum_congr rfl e1, Finset.sum_ite_mem, Finset.inter_eq_right.2 hJ]
  refine Finset.sum_congr rfl fun l hl => ?_
  congr 1
  have hli : l ≠ i := Finset.ne_of_mem_erase (hJ hl)
  have hsub : ∑ k ∈ univ.erase i, g k l = ∑ k ∈ N.erase i, g k l := by
    refine (Finset.sum_subset (fun k hk => Finset.mem_erase.2
      ⟨Finset.ne_of_mem_erase hk, Finset.mem_univ k⟩) fun k hk hkN => ?_).symm
    exact hg k l fun hN' => hkN (Finset.mem_erase.2 ⟨Finset.ne_of_mem_erase hk, hN'⟩)
  rw [hsub]
  by_cases hlN : l ∈ N
  · rw [if_pos hlN]
    exact (Finset.add_sum_erase _ _ (Finset.mem_erase.2 ⟨hli, hlN⟩)).symm
  · rw [if_neg hlN, zero_add,
      Finset.erase_eq_of_notMem (fun h' => hlN (Finset.mem_of_mem_erase h'))]

end FS2Contact

namespace Contact

variable (ct : Contact.{u} d p)

theorem l3_Xb_eq (h : ℝ) (e : Bool) (σ : Config ct.V) :
    ct.Xb h e σ = Matrix.of fun u w =>
      shiftP ct.G (aOf d p) (if e then 1 else -1) h (ct.ySrc e) σ ct.S u w := by
  cases e <;> rfl

theorem l3_posDef_branch (e : Bool) {σ : Config ct.V}
    (hσ : wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0) :
    (precN ct.G (aOf d p) (if e then 1 else -1) (ct.ySrc e) σ ct.S).PosDef := by
  obtain ⟨hP, hM⟩ := SecB.posDef_of_wt_ne_zero ct.G hσ
  cases e
  · exact hM
  · exact hP

theorem l3_ySrc_nonneg (e : Bool) (k : ct.V) : 0 ≤ ct.ySrc e k := by
  cases e
  · exact (ct.ctx.hym k).1
  · exact (ct.ctx.hyp k).1

theorem l3_not_mem_nbhd_self (i : ct.V) : i ∉ nbhd ct.G ct.S i := by
  simp [nbhd]

end Contact

/-- **FS2** (source (FS2), l.1686–1695; AUDIT-D §3.4; checked numerically in
`scripts/tight/check_fs2.py`). At a contact, on the support, for `i ∈ N`, `j ∈ J = N_S(i)` and
either branch `e` (`X_e = Xb h e`): with `U = X_e D_u X₊`,
`F_ji = -a (X_e)_ii (X₊)_ii Σ_{k ∈ N∖i, l ∼ i} (C^e_i)_jk u_k (C^+_i)_kl ξ_l
      = -a (X_e)_ii (X₊)_ii ((T_dir ξ)_j + (T_cav ξ)_j)`,
the split `k = l` / `k ≠ l` being exactly the two cavity maps of (WT1). -/
theorem fs2 (ct : Contact.{u} d p) {h : ℝ} (hh : 0 ≤ h) (e : Bool) {σ : Config ct.V}
    (hσ : wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0) {i : ct.V} (hi : i ∈ ct.N)
    (j : nbhd ct.G ct.S i) :
    maskF (ct.Xb h e σ) (ct.XP h σ) ct.uvec j i =
      -(aOf d p) * ct.Xb h e σ i i * ct.XP h σ i i *
        ((ct.tDir h e i σ *ᵥ rootSigns ct.G σ ct.S i) j +
          (ct.tCav h e i σ *ᵥ rootSigns ct.G σ ct.S i) j) := by
  have hiS : i ∈ ct.S := (Finset.mem_filter.1 hi).1
  have hji : (j : ct.V) ≠ i := fun h' => by
    have hj := j.2
    rw [h'] at hj
    exact ct.l3_not_mem_nbhd_self i hj
  obtain ⟨hE, -⟩ := l3_branch_schur ct.G hiS (ct.l3_ySrc_nonneg e) hh (ct.l3_posDef_branch e hσ)
  obtain ⟨-, hN⟩ := l3_branch_schur ct.G hiS (ct.l3_ySrc_nonneg true) hh
    (ct.l3_posDef_branch true hσ)
  have hmask := fs2_mask (ct.Xb h e σ) (ct.XP h σ) (Matrix.of fun u w => ct.Cb h e σ i u w)
    (Matrix.of fun u w => ct.Cb h true σ i u w)
    (fun l => if l ∈ nbhd ct.G ct.S i then (if true = true then 1 else -1) * aOf d p * sgn σ i l
      else 0) ct.uvec (i := i) (j := j)
    (fun k hk => by
      rw [ct.l3_Xb_eq h e σ]
      exact hE j k hji hk)
    (fun k hk => hN k hk)
  have hJsub : nbhd ct.G ct.S i ⊆ univ.erase i := fun l hl =>
    Finset.mem_erase.2 ⟨fun h' => by
      rw [h'] at hl
      exact ct.l3_not_mem_nbhd_self i hl, Finset.mem_univ l⟩
  have hsplit := l3_sum_split ct.N (nbhd ct.G ct.S i) i hJsub
    (fun k l => ct.Cb h e σ i j k * ct.uvec k * ct.Cb h true σ i k l)
    (fun k l hk => by simp [Contact.uvec, hk])
    (fun l => (if true = true then 1 else -1) * aOf d p * sgn σ i l)
  simp only [of_apply] at hmask hsplit
  rw [hmask, hsplit]
  have hdir : (ct.tDir h e i σ *ᵥ rootSigns ct.G σ ct.S i) j = ∑ l ∈ nbhd ct.G ct.S i,
      (if l ∈ ct.N then ct.Cb h e σ i j l * ct.uvec l * ct.Cb h true σ i l l else 0) *
        sgn σ i l := by
    simp only [mulVec, dotProduct, Contact.tDir, of_apply, rootSigns]
    exact Finset.sum_coe_sort (nbhd ct.G ct.S i) (fun l =>
      (if l ∈ ct.N then ct.Cb h e σ i j l * ct.uvec l * ct.Cb h true σ i l l else 0) * sgn σ i l)
  have hcav : (ct.tCav h e i σ *ᵥ rootSigns ct.G σ ct.S i) j = ∑ l ∈ nbhd ct.G ct.S i,
      (∑ k ∈ (ct.N.erase i).erase l, ct.Cb h e σ i j k * ct.uvec k * ct.Cb h true σ i k l) *
        sgn σ i l := by
    simp only [mulVec, dotProduct, Contact.tCav, of_apply, rootSigns]
    exact Finset.sum_coe_sort (nbhd ct.G ct.S i) (fun l =>
      (∑ k ∈ (ct.N.erase i).erase l, ct.Cb h e σ i j k * ct.uvec k * ct.Cb h true σ i k l) *
        sgn σ i l)
  rw [hdir, hcav, ← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [↓reduceIte]
  ring

/-! ### Pointwise facts for the FS1 kernels -/

section Pure

variable {κ : Type*} [Fintype κ]

/-- `tr(Aᵀ A) = Σ_{l,j} A_jl²`. -/
theorem l3_trace_tt (A : Matrix κ κ ℝ) : (Aᵀ * A).trace = ∑ l, ∑ j, A j l ^ 2 := by
  simp only [Matrix.trace, Matrix.diag, mul_apply, transpose_apply, sq]

/-- `q_{AᵀA}(x) = |A x|²`. -/
theorem l3_qForm_tt (A : Matrix κ κ ℝ) (x : κ → ℝ) : qForm (Aᵀ * A) x = ∑ j, (A *ᵥ x) j ^ 2 := by
  unfold qForm
  rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
  simp only [dotProduct, sq]

/-- The two-term estimate of the cavity part: for symmetric `X` with `|Xw|² ≤ A|w|²` and
`Σ_j X_ij² ≤ B`, `Σ_{j∈J} (X_ii (Xw)_j - X_ji (Xw)_i)² ≤ 2(X_ii² A + B²)|w|²`. -/
theorem l3_two_term (X : Matrix κ κ ℝ) (hsym : ∀ k l, X k l = X l k) (J : Finset κ) (i : κ)
    (w : κ → ℝ) {A B : ℝ} (hA : ∑ j, (X *ᵥ w) j ^ 2 ≤ A * ∑ j, w j ^ 2)
    (hB : ∑ j, X i j ^ 2 ≤ B) :
    ∑ j ∈ J, (X i i * (X *ᵥ w) j - X j i * (X *ᵥ w) i) ^ 2 ≤
      2 * (X i i ^ 2 * A + B ^ 2) * ∑ j, w j ^ 2 := by
  have hw0 : 0 ≤ ∑ j, w j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hB0 : 0 ≤ B := le_trans (Finset.sum_nonneg fun j _ => sq_nonneg _) hB
  have hXi : (X *ᵥ w) i ^ 2 ≤ B * ∑ j, w j ^ 2 := by
    have := Finset.sum_mul_sq_le_sq_mul_sq univ (fun j => X i j) w
    simp only [mulVec, dotProduct]
    exact this.trans (mul_le_mul_of_nonneg_right hB hw0)
  have t1 : X i i ^ 2 * ∑ j, (X *ᵥ w) j ^ 2 ≤ X i i ^ 2 * (A * ∑ j, w j ^ 2) :=
    mul_le_mul_of_nonneg_left hA (sq_nonneg _)
  have t2 : (∑ j, X i j ^ 2) * (X *ᵥ w) i ^ 2 ≤ B * (B * ∑ j, w j ^ 2) :=
    mul_le_mul hB hXi (sq_nonneg _) hB0
  calc ∑ j ∈ J, (X i i * (X *ᵥ w) j - X j i * (X *ᵥ w) i) ^ 2
      ≤ ∑ j ∈ J, (2 * (X i i ^ 2 * (X *ᵥ w) j ^ 2) + 2 * (X i j ^ 2 * (X *ᵥ w) i ^ 2)) :=
        Finset.sum_le_sum fun j _ => by
          rw [hsym j i]
          nlinarith [sq_nonneg (X i i * (X *ᵥ w) j + X i j * (X *ᵥ w) i)]
    _ ≤ ∑ j, (2 * (X i i ^ 2 * (X *ᵥ w) j ^ 2) + 2 * (X i j ^ 2 * (X *ᵥ w) i ^ 2)) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ J) fun j _ _ => by positivity
    _ = 2 * (X i i ^ 2 * ∑ j, (X *ᵥ w) j ^ 2) + 2 * ((∑ j, X i j ^ 2) * (X *ᵥ w) i ^ 2) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
          ← Finset.sum_mul]
    _ ≤ 2 * (X i i ^ 2 * (A * ∑ j, w j ^ 2)) + 2 * (B * (B * ∑ j, w j ^ 2)) := by linarith
    _ = 2 * (X i i ^ 2 * A + B ^ 2) * ∑ j, w j ^ 2 := by ring

end Pure

section RawFacts

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The facts about one branch of the shifted inverse used by FS1 (on the support, `h y ≤ 1`). -/
theorem l3_raw_facts {a τ h : ℝ} {y : V → ℝ} {σ : Config V} {S : Finset V} (hy : ∀ k, 0 ≤ y k)
    (hh : 0 < h) (hyh : ∀ k, h * y k ≤ 1) (hP : (precN G a τ y σ S).PosDef) :
    (∀ k l, SecB.shiftMat G a τ h y σ S k l = SecB.shiftMat G a τ h y σ S l k) ∧
    (∀ w : V → ℝ, ∑ j, (SecB.shiftMat G a τ h y σ S *ᵥ w) j ^ 2 ≤ h⁻¹ ^ 2 * ∑ j, w j ^ 2) ∧
    (∀ k ∈ S, ∑ j, SecB.shiftMat G a τ h y σ S k j ^ 2 ≤ greenP G a τ y σ S k k / h) ∧
    (∀ k, 0 ≤ SecB.shiftMat G a τ h y σ S k k ∧
      SecB.shiftMat G a τ h y σ S k k ≤ greenP G a τ y σ S k k) ∧
    (∀ k l, SecB.shiftMat G a τ h y σ S k l ^ 2 ≤
      SecB.shiftMat G a τ h y σ S k k * SecB.shiftMat G a τ h y σ S l l) := by
  have hX := l3_shift_posSemidef G hy hh.le hP
  have hsym : ∀ k l, SecB.shiftMat G a τ h y σ S k l = SecB.shiftMat G a τ h y σ S l k :=
    fun k l => by simpa using (hX.1.apply k l).symm
  have hdiag : ∀ k, 0 ≤ SecB.shiftMat G a τ h y σ S k k ∧
      SecB.shiftMat G a τ h y σ S k k ≤ greenP G a τ y σ S k k := fun k => by
    refine ⟨(SecB.diag_nonneg_of_posDef G hP hy hh.le k).2, ?_⟩
    show shiftP G a τ h y σ S k k ≤ greenP G a τ y σ S k k
    rw [SecB.shiftP_diag G σ S (hy k), SecB.greenP_diag G σ S (hy k)]
    exact mul_le_mul_of_nonneg_left (SecB.hzN_le_hN G hP hh.le hy k) (hy k)
  refine ⟨hsym, fun w => l3_shift_sq_le G hy hh hyh hP w, fun k hk => ?_, hdiag,
    fun k l => SecB.posSemidef_entry_sq_le hX k l⟩
  have hw := SecB.ward_diag G hy hP hh hk
  have e1 : ∑ j, SecB.shiftMat G a τ h y σ S k j ^ 2 =
      (SecB.shiftMat G a τ h y σ S * SecB.shiftMat G a τ h y σ S) k k := by
    rw [mul_apply]
    exact Finset.sum_congr rfl fun j _ => by rw [sq, hsym j k]
  rw [e1]
  refine hw.trans (div_le_div_of_nonneg_right ?_ hh.le)
  have := (hdiag k).1
  have e2 : SecB.shiftMat G a τ h y σ S k k = shiftP G a τ h y σ S k k := rfl
  linarith

end RawFacts

namespace Contact

variable (ct : Contact.{u} d p)

/-- The radius-two ball `{v} ∪ N ∪ N(N)` of the definition of `D_*`. -/
abbrev l3_ball : Finset ct.V := insert ct.v (ct.N ∪ ct.N.biUnion (nbhd ct.G ct.S))

theorem l3_mem_ball_v : ct.v ∈ ct.l3_ball := Finset.mem_insert_self _ _

theorem l3_mem_ball_N {i : ct.V} (hi : i ∈ ct.N) : i ∈ ct.l3_ball :=
  Finset.mem_insert_of_mem (Finset.mem_union_left _ hi)

theorem l3_mem_ball_nbhd {i l : ct.V} (hi : i ∈ ct.N) (hl : l ∈ nbhd ct.G ct.S i) :
    l ∈ ct.l3_ball :=
  Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨i, hi, hl⟩))

theorem l3_diagB_eq (h : ℝ) (σ : Config ct.V) (k : ct.V) (e : Bool) :
    ct.diagB h σ k e false =
      greenP ct.G (aOf d p) (if e then 1 else -1) (ct.ySrc e) σ ct.S k k := by
  cases e <;> rfl

theorem l3_diagB_le (h : ℝ) (σ : Config ct.V) (e : Bool) {k : ct.V} (hk : k ∈ ct.l3_ball) :
    ct.diagB h σ k e false ≤ ct.Dstar σ - 1 := by
  have hs := ct.l3_ball.le_sup' (fun w => max (ct.gp σ w w) (ct.gm σ w w)) hk
  have hD : ct.Dstar σ = 1 + ct.l3_ball.sup' (Finset.insert_nonempty _ _)
      (fun w => max (ct.gp σ w w) (ct.gm σ w w)) := rfl
  rw [hD]
  cases e
  · show ct.gm σ k k ≤ _
    have := le_max_right (ct.gp σ k k) (ct.gm σ k k); linarith
  · show ct.gp σ k k ≤ _
    have := le_max_left (ct.gp σ k k) (ct.gm σ k k); linarith

theorem l3_diagB_nonneg (h : ℝ) {σ : Config ct.V}
    (hσ : wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0) (e : Bool) (k : ct.V) :
    0 ≤ ct.diagB h σ k e false := by
  rw [ct.l3_diagB_eq]
  exact (SecB.diag_nonneg_of_posDef ct.G (ct.l3_posDef_branch e hσ) (ct.l3_ySrc_nonneg e)
    (le_refl (0 : ℝ)) k).1

theorem l3_one_le_dstar {σ : Config ct.V} (hσ : wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0) :
    1 ≤ ct.Dstar σ := by
  have h1 := ct.l3_diagB_le 0 σ true ct.l3_mem_ball_v
  have h2 := ct.l3_diagB_nonneg 0 hσ true ct.v
  linarith

theorem l3_Xb_shiftMat (h : ℝ) (e : Bool) (σ : Config ct.V) :
    ct.Xb h e σ = SecB.shiftMat ct.G (aOf d p) (if e then 1 else -1) h (ct.ySrc e) σ ct.S := by
  cases e <;> rfl

theorem l3_ySrc_le_two (hR : TRegime d p) (e : Bool) (k : ct.V) : ct.ySrc e k ≤ 2 := by
  have hs := hR.sOf_pos
  have hs2 := SecA.sOf_le_two hR
  have hl1 := ct.ctx.lam_le_one
  have hl0 := ct.ctx.lam_nonneg
  have hy : ct.ySrc e k ≤ ct.lam * sOf d p := by
    cases e
    · exact (ct.ctx.hym k).2
    · exact (ct.ctx.hyp k).2
  nlinarith

/-- The branch facts at a contact, with the inverse diagonals bounded by `D_*` on the ball. -/
theorem l3_branch_facts (hR : TRegime d p) {h : ℝ} (hh : 0 < h) (hh2 : h ≤ 1 / 2) (e : Bool)
    {σ : Config ct.V} (hσ : wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0) :
    (∀ k l, ct.Xb h e σ k l = ct.Xb h e σ l k) ∧
    (∀ w : ct.V → ℝ, ∑ j, (ct.Xb h e σ *ᵥ w) j ^ 2 ≤ h⁻¹ ^ 2 * ∑ j, w j ^ 2) ∧
    (∀ k ∈ ct.l3_ball, ∑ j, ct.Xb h e σ k j ^ 2 ≤ ct.Dstar σ / h) ∧
    (∀ k ∈ ct.l3_ball, 0 ≤ ct.Xb h e σ k k ∧ ct.Xb h e σ k k ≤ ct.Dstar σ) ∧
    (∀ k, 0 ≤ ct.Xb h e σ k k) ∧
    (∀ k l, ct.Xb h e σ k l ^ 2 ≤ ct.Xb h e σ k k * ct.Xb h e σ l l) := by
  have hy := ct.l3_ySrc_nonneg e
  have hyh : ∀ k, h * ct.ySrc e k ≤ 1 := fun k => by
    have := ct.l3_ySrc_le_two hR e k; have := hy k; nlinarith
  obtain ⟨F1, F2, F3, F4, F5⟩ := l3_raw_facts ct.G hy hh hyh (ct.l3_posDef_branch e hσ)
  have hball : ∀ k ∈ ct.l3_ball, k ∈ ct.S := fun k hk => (SecB.ball_sub_card ct).1 hk
  rw [ct.l3_Xb_shiftMat h e σ]
  refine ⟨F1, F2, fun k hk => ?_, fun k hk => ⟨(F4 k).1, ?_⟩, fun k => (F4 k).1, F5⟩
  · refine (F3 k (hball k hk)).trans (div_le_div_of_nonneg_right ?_ hh.le)
    have := ct.l3_diagB_le h σ e hk
    rw [ct.l3_diagB_eq] at this
    linarith
  · have := ct.l3_diagB_le h σ e hk
    rw [ct.l3_diagB_eq] at this
    linarith [(F4 k).2]

/-- FS2a for one branch at a contact, in terms of `Xb` and `Cb`. -/
theorem l3_fs2a (h : ℝ) (hh : 0 ≤ h) (e : Bool) {σ : Config ct.V}
    (hσ : wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0) {i : ct.V} (hi : i ∈ ct.N) {j k : ct.V}
    (hj : j ≠ i) (hk : k ≠ i) :
    ct.Xb h e σ i i * ct.Cb h e σ i j k =
      ct.Xb h e σ i i * ct.Xb h e σ j k - ct.Xb h e σ j i * ct.Xb h e σ i k := by
  have hiS : i ∈ ct.S := (Finset.mem_filter.1 hi).1
  obtain ⟨hE, -⟩ := l3_branch_schur ct.G hiS (ct.l3_ySrc_nonneg e) hh (ct.l3_posDef_branch e hσ)
  rw [ct.l3_Xb_eq h e σ]
  exact (hE j k hj hk).symm

theorem l3_uvec_sq_le (k : ct.V) : ct.uvec k ^ 2 ≤ 1 / (d : ℝ) := by
  unfold Contact.uvec
  split_ifs
  · rw [div_pow, one_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
  · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]; positivity

theorem l3_mem_nbhd_ne {i l : ct.V} (hl : l ∈ nbhd ct.G ct.S i) : l ≠ i := fun h' => by
  rw [h'] at hl
  exact ct.l3_not_mem_nbhd_self i hl

end Contact

/-- **Cavity part, pointwise** (source (FS3), l.1703–1725). On the support, for `i ∈ N`:
`(X_e)_ii² (X₊)_ii² tr(T_cavᵀ T_cav)
  ≤ 4 D_*² h⁻² · (2/d) ((X₊)_ii² Σ_{l∼i} Σ_{k∈N∖l} (X₊)_kl² + (D_*/h) Σ_{k∈N∖i} (X₊)_ki²)`,
from FS2a (`(X_e)_ii C^e_jk = (X_e)_ii (X_e)_jk - (X_e)_ji (X_e)_ik`, the same for `C⁺`),
`‖X_e‖ ≤ h⁻¹`, `(X²)_ii ≤ G_ii/h ≤ D_*/h` and Cauchy–Schwarz. -/
theorem l3_cav_pt (ct : Contact.{u} d p) (hR : TRegime d p) {h : ℝ} (hh : 0 < h)
    (hh2 : h ≤ 1 / 2) (e : Bool) {σ : Config ct.V}
    (hσ : wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0) {i : ct.V} (hi : i ∈ ct.N) :
    ct.Xb h e σ i i ^ 2 * ct.XP h σ i i ^ 2 * ((ct.tCav h e i σ)ᵀ * ct.tCav h e i σ).trace ≤
      4 * ct.Dstar σ ^ 2 * h⁻¹ ^ 2 * (2 / d * (ct.XP h σ i i ^ 2 *
        ∑ l ∈ nbhd ct.G ct.S i, ∑ k ∈ ct.N.erase l, ct.XP h σ k l ^ 2 +
        ct.Dstar σ / h * ∑ k ∈ ct.N.erase i, ct.XP h σ k i ^ 2)) := by
  obtain ⟨E1, E2, E3, E4, -, -⟩ := ct.l3_branch_facts hR hh hh2 e hσ
  obtain ⟨P1, -, P3, P4, -, -⟩ := ct.l3_branch_facts hR hh hh2 true hσ
  have hXP : ct.Xb h true σ = ct.XP h σ := rfl
  rw [hXP] at P1 P3 P4
  have hiB := ct.l3_mem_ball_N hi
  have hD1 := ct.l3_one_le_dstar hσ
  set D := ct.Dstar σ with hDdef
  have hD0 : 0 ≤ D := by linarith
  set J := nbhd ct.G ct.S i with hJ
  set Xe := ct.Xb h e σ with hXe
  set Xp := ct.XP h σ with hXp
  -- the vectors `w^l`
  set w : ct.V → ct.V → ℝ := fun l k =>
    if k ∈ (ct.N.erase i).erase l then ct.uvec k * (Xp i i * Xp k l - Xp k i * Xp i l) else 0
    with hw
  have htr : ((ct.tCav h e i σ)ᵀ * ct.tCav h e i σ).trace =
      ∑ l : J, ∑ j : J, (ct.tCav h e i σ j l) ^ 2 := l3_trace_tt _
  have hrow : ∀ l : J, ∀ j : J, Xe i i * Xp i i * ct.tCav h e i σ j l =
      Xe i i * (Xe *ᵥ w l) j - Xe j i * (Xe *ᵥ w l) i := by
    intro l j
    have hji := ct.l3_mem_nbhd_ne j.2
    have hli := ct.l3_mem_nbhd_ne l.2
    simp only [Contact.tCav, of_apply, mulVec, dotProduct, Finset.mul_sum, ← Finset.sum_sub_distrib]
    rw [← Finset.sum_subset (Finset.subset_univ ((ct.N.erase i).erase l))
      (fun k _ hk => by simp only [hw, hk, if_false, mul_zero, sub_self])]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hki : k ≠ i := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hk)
    have hE := ct.l3_fs2a h hh.le e hσ hi hji hki
    have hP : Xp i i * ct.Cb h true σ i k l = Xp i i * Xp k l - Xp k i * Xp i l :=
      ct.l3_fs2a h hh.le true hσ hi hki hli
    simp only [hw, hk, if_true]
    change Xe i i * Xp i i * (ct.Cb h e σ i j k * ct.uvec k * ct.Cb h true σ i k l) = _
    rw [show Xe i i * Xp i i * (ct.Cb h e σ i j k * ct.uvec k * ct.Cb h true σ i k l) =
      (Xe i i * ct.Cb h e σ i j k) * ct.uvec k * (Xp i i * ct.Cb h true σ i k l) by ring, hE, hP]
    ring
  have hl_bound : ∀ l : J, ∑ j : J, (Xe i i * Xp i i * ct.tCav h e i σ j l) ^ 2 ≤
      4 * D ^ 2 * h⁻¹ ^ 2 * ∑ k, w l k ^ 2 := by
    intro l
    have hB : ∑ j, Xe i j ^ 2 ≤ D / h := E3 i hiB
    have hXii : Xe i i ^ 2 ≤ D ^ 2 := by
      have := E4 i hiB; nlinarith [this.1, this.2]
    have h2 := l3_two_term Xe E1 J i (w l) (E2 (w l)) hB
    have e1 : ∑ j : J, (Xe i i * Xp i i * ct.tCav h e i σ j l) ^ 2 =
        ∑ j ∈ J, (Xe i i * (Xe *ᵥ w l) j - Xe j i * (Xe *ᵥ w l) i) ^ 2 := by
      rw [← Finset.sum_coe_sort J]
      exact Finset.sum_congr rfl fun j _ => by rw [hrow l j]
    rw [e1]
    refine h2.trans (mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun k _ => sq_nonneg _))
    have : (D / h) ^ 2 = D ^ 2 * h⁻¹ ^ 2 := by rw [div_eq_mul_inv, mul_pow]
    nlinarith [sq_nonneg h⁻¹]
  -- the `w` masses
  have hwl : ∀ l ∈ J, ∑ k, w l k ^ 2 ≤ 2 / d * (Xp i i ^ 2 * ∑ k ∈ ct.N.erase l, Xp k l ^ 2 +
      ∑ k ∈ ct.N.erase i, Xp k i ^ 2 * Xp i l ^ 2) := by
    intro l _
    have e1 : ∑ k, w l k ^ 2 = ∑ k ∈ (ct.N.erase i).erase l,
        ct.uvec k ^ 2 * (Xp i i * Xp k l - Xp k i * Xp i l) ^ 2 := by
      rw [← Finset.sum_subset (Finset.subset_univ ((ct.N.erase i).erase l))
        (fun k _ hk => by simp only [hw, hk, if_false]; ring)]
      exact Finset.sum_congr rfl fun k hk => by simp only [hw, hk, if_true]; ring
    rw [e1]
    have hd0 : (0 : ℝ) ≤ 1 / d := by positivity
    calc ∑ k ∈ (ct.N.erase i).erase l, ct.uvec k ^ 2 * (Xp i i * Xp k l - Xp k i * Xp i l) ^ 2
        ≤ ∑ k ∈ (ct.N.erase i).erase l,
            1 / d * (2 * (Xp i i ^ 2 * Xp k l ^ 2) + 2 * (Xp k i ^ 2 * Xp i l ^ 2)) :=
          Finset.sum_le_sum fun k _ => by
            apply mul_le_mul (ct.l3_uvec_sq_le k) _ (sq_nonneg _) hd0
            nlinarith [sq_nonneg (Xp i i * Xp k l + Xp k i * Xp i l)]
      _ = 2 / d * (Xp i i ^ 2 * ∑ k ∈ (ct.N.erase i).erase l, Xp k l ^ 2 +
            ∑ k ∈ (ct.N.erase i).erase l, Xp k i ^ 2 * Xp i l ^ 2) := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
      _ ≤ 2 / d * (Xp i i ^ 2 * ∑ k ∈ ct.N.erase l, Xp k l ^ 2 +
            ∑ k ∈ ct.N.erase i, Xp k i ^ 2 * Xp i l ^ 2) := by
          have s1 : ∑ k ∈ (ct.N.erase i).erase l, Xp k l ^ 2 ≤ ∑ k ∈ ct.N.erase l, Xp k l ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg
              (fun k hk => Finset.mem_erase.2 ⟨Finset.ne_of_mem_erase hk,
                Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hk)⟩)
              fun k _ _ => sq_nonneg _
          have s2 : ∑ k ∈ (ct.N.erase i).erase l, Xp k i ^ 2 * Xp i l ^ 2 ≤
              ∑ k ∈ ct.N.erase i, Xp k i ^ 2 * Xp i l ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
              fun k _ _ => by positivity
          have : (0 : ℝ) ≤ 2 / d := by positivity
          nlinarith [mul_le_mul_of_nonneg_left s1 (sq_nonneg (Xp i i))]
  have hJl : ∑ l ∈ J, Xp i l ^ 2 ≤ D / h :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ J) fun l _ _ => sq_nonneg _).trans
      (P3 i hiB)
  -- assemble
  rw [htr, Finset.mul_sum]
  calc ∑ l : J, Xe i i ^ 2 * Xp i i ^ 2 * ∑ j : J, ct.tCav h e i σ j l ^ 2
      = ∑ l : J, ∑ j : J, (Xe i i * Xp i i * ct.tCav h e i σ j l) ^ 2 :=
        Finset.sum_congr rfl fun l _ => by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    _ ≤ ∑ l : J, 4 * D ^ 2 * h⁻¹ ^ 2 * ∑ k, w l k ^ 2 := Finset.sum_le_sum fun l _ => hl_bound l
    _ = 4 * D ^ 2 * h⁻¹ ^ 2 * ∑ l ∈ J, ∑ k, w l k ^ 2 := by
        rw [← Finset.mul_sum]
        congr 1
        exact Finset.sum_coe_sort J (fun l => ∑ k, w l k ^ 2)
    _ ≤ 4 * D ^ 2 * h⁻¹ ^ 2 * ∑ l ∈ J, 2 / d * (Xp i i ^ 2 * ∑ k ∈ ct.N.erase l, Xp k l ^ 2 +
          ∑ k ∈ ct.N.erase i, Xp k i ^ 2 * Xp i l ^ 2) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hwl) (by positivity)
    _ ≤ 4 * D ^ 2 * h⁻¹ ^ 2 * (2 / d * (Xp i i ^ 2 *
          ∑ l ∈ J, ∑ k ∈ ct.N.erase l, Xp k l ^ 2 + D / h * ∑ k ∈ ct.N.erase i, Xp k i ^ 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [Finset.sum_comm]
        have : ∑ k ∈ ct.N.erase i, ∑ l ∈ J, Xp k i ^ 2 * Xp i l ^ 2 =
            (∑ k ∈ ct.N.erase i, Xp k i ^ 2) * ∑ l ∈ J, Xp i l ^ 2 := by
          rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun k _ => by rw [Finset.mul_sum]
        rw [this]
        have h0 : 0 ≤ ∑ k ∈ ct.N.erase i, Xp k i ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
        nlinarith [mul_le_mul_of_nonneg_left hJl h0]

/-- **Direct part, pointwise** (source l.1727–1737). On the support, for `i ∈ N`:
`(X_e)_ii² (X₊)_ii² tr(T_dirᵀ T_dir) ≤ (2 D_*⁶/d) Σ_{l∈J∩N} ((X_e²)_ll + (X_e²)_ii)`, from
`0 ≤ (X₊)_ii C⁺_ll ≤ (X₊)_ii (X₊)_ll` and the Schur subtraction
`(X_e)_ii² ((C^e)²)_ll ≤ 2 (X_e)_ii² (X_e²)_ll + 2 (X_e)_il² (X_e²)_ii`. -/
theorem l3_dir_pt (ct : Contact.{u} d p) (hR : TRegime d p) {h : ℝ} (hh : 0 < h)
    (hh2 : h ≤ 1 / 2) (e : Bool) {σ : Config ct.V}
    (hσ : wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0) {i : ct.V} (hi : i ∈ ct.N) :
    ct.Xb h e σ i i ^ 2 * ct.XP h σ i i ^ 2 * ((ct.tDir h e i σ)ᵀ * ct.tDir h e i σ).trace ≤
      2 * ct.Dstar σ ^ 6 / d * ∑ l ∈ (nbhd ct.G ct.S i).filter (· ∈ ct.N),
        (∑ j, ct.Xb h e σ l j ^ 2 + ∑ j, ct.Xb h e σ i j ^ 2) := by
  obtain ⟨E1, -, -, E4, E5, E6⟩ := ct.l3_branch_facts hR hh hh2 e hσ
  obtain ⟨P1, -, -, P4, P5, P6⟩ := ct.l3_branch_facts hR hh hh2 true hσ
  have hXP : ct.Xb h true σ = ct.XP h σ := rfl
  rw [hXP] at P1 P4 P5 P6
  have hiB := ct.l3_mem_ball_N hi
  have hD1 := ct.l3_one_le_dstar hσ
  set D := ct.Dstar σ with hDdef
  have hD0 : 0 ≤ D := by linarith
  set J := nbhd ct.G ct.S i with hJ
  set Xe := ct.Xb h e σ with hXe
  set Xp := ct.XP h σ with hXp
  have htr : ((ct.tDir h e i σ)ᵀ * ct.tDir h e i σ).trace =
      ∑ l : J, ∑ j : J, (ct.tDir h e i σ j l) ^ 2 := l3_trace_tt _
  have hterm : ∀ l : J, Xe i i ^ 2 * Xp i i ^ 2 * ∑ j : J, ct.tDir h e i σ j l ^ 2 ≤
      if (l : ct.V) ∈ ct.N then 2 * D ^ 6 / d * (∑ j, Xe l j ^ 2 + ∑ j, Xe i j ^ 2) else 0 := by
    intro l
    have hli := ct.l3_mem_nbhd_ne l.2
    by_cases hlN : (l : ct.V) ∈ ct.N
    · rw [if_pos hlN]
      have hlB := ct.l3_mem_ball_N hlN
      have hP : Xp i i * ct.Cb h true σ i l l = Xp i i * Xp l l - Xp l i * Xp i l :=
        ct.l3_fs2a h hh.le true hσ hi hli hli
      -- `0 ≤ X_ii C_ll ≤ X_ii X_ll`
      have hPl : (Xp i i * ct.Cb h true σ i l l) ^ 2 ≤ D ^ 4 := by
        rw [hP, P1 l i]
        have a1 := P6 i l
        have b1 := P4 i hiB
        have b2 := P4 l hlB
        have c1 : 0 ≤ Xp i i * Xp l l - Xp i l * Xp i l := by nlinarith
        have c2 : Xp i i * Xp l l - Xp i l * Xp i l ≤ D ^ 2 := by
          nlinarith [mul_le_mul b1.2 b2.2 b2.1 hD0, mul_self_nonneg (Xp i l)]
        have : (Xp i i * Xp l l - Xp i l * Xp i l) ^ 2 ≤ (D ^ 2) ^ 2 :=
          pow_le_pow_left₀ c1 c2 2
        nlinarith
      have hrowsum : ∑ j : J, (Xe i i * ct.Cb h e σ i j l) ^ 2 ≤
          2 * D ^ 2 * (∑ j, Xe l j ^ 2 + ∑ j, Xe i j ^ 2) := by
        have e1 : ∀ j : J, Xe i i * ct.Cb h e σ i j l = Xe i i * Xe j l - Xe j i * Xe i l :=
          fun j => ct.l3_fs2a h hh.le e hσ hi (ct.l3_mem_nbhd_ne j.2) hli
        have hXii : Xe i i ^ 2 ≤ D ^ 2 := by have := E4 i hiB; nlinarith [this.1, this.2]
        have hXil : Xe i l ^ 2 ≤ D ^ 2 := by
          have := E6 i l; have b1 := E4 i hiB; have b2 := E4 l hlB; nlinarith [b1.1, b2.1]
        calc ∑ j : J, (Xe i i * ct.Cb h e σ i j l) ^ 2
            = ∑ j ∈ J, (Xe i i * Xe j l - Xe j i * Xe i l) ^ 2 := by
              rw [← Finset.sum_coe_sort J]; exact Finset.sum_congr rfl fun j _ => by rw [e1 j]
          _ ≤ ∑ j, (2 * (Xe i i ^ 2 * Xe l j ^ 2) + 2 * (Xe i l ^ 2 * Xe i j ^ 2)) := by
              refine (Finset.sum_le_sum fun j _ => ?_).trans
                (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ J)
                  fun j _ _ => by positivity)
              rw [E1 j l, E1 j i]
              nlinarith [sq_nonneg (Xe i i * Xe l j + Xe i j * Xe i l)]
          _ = 2 * (Xe i i ^ 2 * ∑ j, Xe l j ^ 2) + 2 * (Xe i l ^ 2 * ∑ j, Xe i j ^ 2) := by
              rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
                ← Finset.mul_sum]
          _ ≤ 2 * (D ^ 2 * ∑ j, Xe l j ^ 2) + 2 * (D ^ 2 * ∑ j, Xe i j ^ 2) := by
              have s1 : 0 ≤ ∑ j, Xe l j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
              have s2 : 0 ≤ ∑ j, Xe i j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
              nlinarith [mul_le_mul_of_nonneg_right hXii s1, mul_le_mul_of_nonneg_right hXil s2]
          _ = 2 * D ^ 2 * (∑ j, Xe l j ^ 2 + ∑ j, Xe i j ^ 2) := by ring
      have e2 : Xe i i ^ 2 * Xp i i ^ 2 * ∑ j : J, ct.tDir h e i σ j l ^ 2 =
          ct.uvec l ^ 2 * (Xp i i * ct.Cb h true σ i l l) ^ 2 *
            ∑ j : J, (Xe i i * ct.Cb h e σ i j l) ^ 2 := by
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [Contact.tDir, of_apply, hlN, if_true]
        ring
      rw [e2]
      have s0 : 0 ≤ ∑ j, Xe l j ^ 2 + ∑ j, Xe i j ^ 2 := by positivity
      have q0 : 0 ≤ ∑ j : J, (Xe i i * ct.Cb h e σ i j l) ^ 2 :=
        Finset.sum_nonneg fun j _ => sq_nonneg _
      calc ct.uvec l ^ 2 * (Xp i i * ct.Cb h true σ i l l) ^ 2 *
            ∑ j : J, (Xe i i * ct.Cb h e σ i j l) ^ 2
          ≤ 1 / d * D ^ 4 * (2 * D ^ 2 * (∑ j, Xe l j ^ 2 + ∑ j, Xe i j ^ 2)) := by
            apply mul_le_mul _ hrowsum q0 (by positivity)
            exact mul_le_mul (ct.l3_uvec_sq_le l) hPl (sq_nonneg _) (by positivity)
        _ = 2 * D ^ 6 / d * (∑ j, Xe l j ^ 2 + ∑ j, Xe i j ^ 2) := by ring
    · rw [if_neg hlN]
      have : ∀ j : J, ct.tDir h e i σ j l = 0 := fun j => by
        simp only [Contact.tDir, of_apply, hlN, if_false]
      simp [this]
  rw [htr, Finset.mul_sum]
  calc ∑ l : J, Xe i i ^ 2 * Xp i i ^ 2 * ∑ j : J, ct.tDir h e i σ j l ^ 2
      ≤ ∑ l : J, (if (l : ct.V) ∈ ct.N then
          2 * D ^ 6 / d * (∑ j, Xe l j ^ 2 + ∑ j, Xe i j ^ 2) else 0) :=
        Finset.sum_le_sum fun l _ => hterm l
    _ = ∑ l ∈ J, (if l ∈ ct.N then 2 * D ^ 6 / d * (∑ j, Xe l j ^ 2 + ∑ j, Xe i j ^ 2) else 0) :=
        Finset.sum_coe_sort J (fun l =>
          if l ∈ ct.N then 2 * D ^ 6 / d * (∑ j, Xe l j ^ 2 + ∑ j, Xe i j ^ 2) else 0)
    _ = 2 * D ^ 6 / d * ∑ l ∈ J.filter (· ∈ ct.N), (∑ j, Xe l j ^ 2 + ∑ j, Xe i j ^ 2) := by
        rw [Finset.sum_filter, Finset.mul_sum]
        exact Finset.sum_congr rfl fun l _ => by split_ifs <;> simp

/-! ### The off-diagonal Schur energies as sums -/

theorem l3_sum_comm3 {α : Type*} [Fintype α] (F : α → α → α → ℝ) :
    ∑ k, ∑ l, ∑ m, F k l m = ∑ m, ∑ k, ∑ l, F k l m :=
  calc ∑ k, ∑ l, ∑ m, F k l m = ∑ k, ∑ m, ∑ l, F k l m :=
        Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = ∑ m, ∑ k, ∑ l, F k l m := Finset.sum_comm

namespace Contact

variable (ct : Contact.{u} d p)

theorem l3_sum_uvec (F : ct.V → ℝ) : ∑ k, ct.uvec k * F k = 1 / Real.sqrt d * ∑ k ∈ ct.N, F k := by
  rw [Finset.mul_sum, ← Finset.sum_subset (Finset.subset_univ ct.N)
    (fun k _ hk => by simp [Contact.uvec, hk])]
  exact Finset.sum_congr rfl fun k hk => by simp [Contact.uvec, hk]

theorem l3_sum_ne (l : ct.V) (f : ct.V → ℝ) :
    ∑ k ∈ ct.N, (if k = l then 0 else f k) = ∑ k ∈ ct.N.erase l, f k := by
  rw [← Finset.filter_ne', Finset.sum_filter]
  exact Finset.sum_congr rfl fun k _ => by by_cases hkl : k = l <;> simp [hkl]

theorem l3_adjS_of_mem {l m : ct.V} (hm : m ∈ ct.N) :
    ct.adjS l m = if l ∈ nbhd ct.G ct.S m then 1 else 0 := by
  have hmS : m ∈ ct.S := (Finset.mem_filter.1 hm).1
  simp only [Contact.adjS, of_apply, nbhd, Finset.mem_filter]
  by_cases h1 : l ∈ ct.S ∧ ct.G.Adj m l
  · rw [if_pos ⟨h1.1, hmS, h1.2.symm⟩, if_pos h1]
  · rw [if_neg (fun h' => h1 ⟨h'.1, h'.2.2.symm⟩), if_neg h1]

theorem l3_KM_diff (h : ℝ) (σ : Config ct.V) (f : ct.V → ℝ) :
    ct.uvec ⬝ᵥ (ct.KP h σ *ᵥ f) - ct.uvec ⬝ᵥ (ct.MP h σ *ᵥ f) =
      ∑ k, ∑ l, ct.uvec k * (if k = l then 0 else ct.XP h σ k l ^ 2 / 4) * f l := by
  have hMv : ∀ k, (ct.MP h σ *ᵥ f) k = (ct.XP h σ k k / 2) ^ 2 * f k := fun k => by
    simp [Contact.MP, mulVec_diagonal]
  simp only [dotProduct, hMv]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e : ∀ l, ct.uvec k * (if k = l then 0 else ct.XP h σ k l ^ 2 / 4) * f l =
      ct.uvec k * (ct.KP h σ k l * f l) -
        (if k = l then ct.uvec k * ((ct.XP h σ k k / 2) ^ 2 * f k) else 0) := fun l => by
    by_cases hkl : k = l
    · subst hkl; simp only [Contact.KP, of_apply, if_true]; ring
    · simp only [Contact.KP, of_apply, hkl, if_false]; ring
  rw [Finset.sum_congr rfl fun l _ => e l, Finset.sum_sub_distrib, Finset.sum_ite_eq,
    if_pos (Finset.mem_univ k), mulVec, dotProduct, Finset.mul_sum]

/-- `4 uᵀ(K₊ - M₊) b₊ = (a²/d) Σ_{i∈N} (X₊)_ii² Σ_{l∼i} Σ_{k∈N∖l} (X₊)_kl²` (exact; source
l.1711–1716). -/
theorem l3_Y1_eq (h : ℝ) (σ : Config ct.V) :
    4 * (ct.uvec ⬝ᵥ (ct.KP h σ *ᵥ ct.bP h σ) - ct.uvec ⬝ᵥ (ct.MP h σ *ᵥ ct.bP h σ)) =
      aOf d p ^ 2 / d * ∑ i ∈ ct.N, ct.XP h σ i i ^ 2 *
        ∑ l ∈ nbhd ct.G ct.S i, ∑ k ∈ ct.N.erase l, ct.XP h σ k l ^ 2 := by
  have hMv : ∀ k, (ct.MP h σ *ᵥ ct.uvec) k = (ct.XP h σ k k / 2) ^ 2 * ct.uvec k := fun k => by
    simp [Contact.MP, mulVec_diagonal]
  have hb : ∀ l, ct.bP h σ l =
      ∑ m, aOf d p ^ 2 * ct.adjS l m * ct.XP h σ m m ^ 2 * ct.uvec m := fun l => by
    have e : ct.bP h σ l = 4 * aOf d p ^ 2 * ∑ m, ct.adjS l m * (ct.MP h σ *ᵥ ct.uvec) m := rfl
    rw [e, Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => by rw [hMv]; ring
  have hL : 4 * (ct.uvec ⬝ᵥ (ct.KP h σ *ᵥ ct.bP h σ) - ct.uvec ⬝ᵥ (ct.MP h σ *ᵥ ct.bP h σ)) =
      ∑ m, ∑ k, ∑ l, 4 * (ct.uvec k * (if k = l then 0 else ct.XP h σ k l ^ 2 / 4) *
        (aOf d p ^ 2 * ct.adjS l m * ct.XP h σ m m ^ 2 * ct.uvec m)) := by
    rw [ct.l3_KM_diff h σ, Finset.mul_sum]
    refine Eq.trans ?_ (l3_sum_comm3 _)
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hb l, Finset.mul_sum, Finset.mul_sum]
  rw [hL, ← Finset.sum_subset (Finset.subset_univ ct.N) (fun m _ hm => by
    refine Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun l _ => ?_
    simp [Contact.uvec, hm]), Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hum : ct.uvec m = 1 / Real.sqrt d := by simp [Contact.uvec, hm]
  have e1 : ∀ k, ∑ l, 4 * (ct.uvec k * (if k = l then 0 else ct.XP h σ k l ^ 2 / 4) *
      (aOf d p ^ 2 * ct.adjS l m * ct.XP h σ m m ^ 2 * ct.uvec m)) =
      ct.uvec k * (aOf d p ^ 2 * ct.XP h σ m m ^ 2 * (1 / Real.sqrt d) *
        ∑ l ∈ nbhd ct.G ct.S m, (if k = l then 0 else ct.XP h σ k l ^ 2)) := fun k => by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_subset (Finset.subset_univ _)
      (fun l _ hl => by rw [ct.l3_adjS_of_mem hm, if_neg hl]; ring)]
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [ct.l3_adjS_of_mem hm, if_pos hl, hum]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl fun k _ => e1 k, ct.l3_sum_uvec]
  have hd : 1 / Real.sqrt d * (1 / Real.sqrt d) = 1 / (d : ℝ) := by
    rw [div_mul_div_comm, one_mul, Real.mul_self_sqrt (Nat.cast_nonneg d)]
  have e2 : ∑ k ∈ ct.N, aOf d p ^ 2 * ct.XP h σ m m ^ 2 * (1 / Real.sqrt d) *
      ∑ l ∈ nbhd ct.G ct.S m, (if k = l then 0 else ct.XP h σ k l ^ 2) =
      aOf d p ^ 2 * ct.XP h σ m m ^ 2 * (1 / Real.sqrt d) *
        ∑ l ∈ nbhd ct.G ct.S m, ∑ k ∈ ct.N.erase l, ct.XP h σ k l ^ 2 := by
    rw [← Finset.mul_sum, Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun l _ => ?_
    exact ct.l3_sum_ne l (fun k => ct.XP h σ k l ^ 2)
  rw [e2]
  calc 1 / Real.sqrt d * (aOf d p ^ 2 * ct.XP h σ m m ^ 2 * (1 / Real.sqrt d) *
        ∑ l ∈ nbhd ct.G ct.S m, ∑ k ∈ ct.N.erase l, ct.XP h σ k l ^ 2)
      = (1 / Real.sqrt d * (1 / Real.sqrt d)) * (aOf d p ^ 2 * (ct.XP h σ m m ^ 2 *
        ∑ l ∈ nbhd ct.G ct.S m, ∑ k ∈ ct.N.erase l, ct.XP h σ k l ^ 2)) := by ring
    _ = _ := by rw [hd]; ring

/-- `4 uᵀ(K₊ - M₊) u = d⁻¹ Σ_{i∈N} Σ_{k∈N∖i} (X₊)_ki²` (exact; source l.1718–1725). -/
theorem l3_Y2_eq (h : ℝ) (σ : Config ct.V) :
    4 * (ct.uvec ⬝ᵥ (ct.KP h σ *ᵥ ct.uvec) - ct.uvec ⬝ᵥ (ct.MP h σ *ᵥ ct.uvec)) =
      1 / d * ∑ i ∈ ct.N, ∑ k ∈ ct.N.erase i, ct.XP h σ k i ^ 2 := by
  have hL : 4 * (ct.uvec ⬝ᵥ (ct.KP h σ *ᵥ ct.uvec) - ct.uvec ⬝ᵥ (ct.MP h σ *ᵥ ct.uvec)) =
      ∑ l, ct.uvec l * ∑ k, ct.uvec k * (if k = l then 0 else ct.XP h σ k l ^ 2) := by
    rw [ct.l3_KM_diff h σ]
    calc 4 * ∑ k, ∑ l, ct.uvec k * (if k = l then 0 else ct.XP h σ k l ^ 2 / 4) * ct.uvec l
        = ∑ k, ∑ l, 4 * (ct.uvec k * (if k = l then 0 else ct.XP h σ k l ^ 2 / 4) *
            ct.uvec l) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => Finset.mul_sum _ _ _
      _ = ∑ l, ∑ k, 4 * (ct.uvec k * (if k = l then 0 else ct.XP h σ k l ^ 2 / 4) *
            ct.uvec l) := Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun l _ => by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by split_ifs <;> ring
  rw [hL]
  have e2 : ∀ l, ct.uvec l * ∑ k, ct.uvec k * (if k = l then 0 else ct.XP h σ k l ^ 2) =
      ct.uvec l * (1 / Real.sqrt d * ∑ k ∈ ct.N.erase l, ct.XP h σ k l ^ 2) := fun l => by
    rw [ct.l3_sum_uvec, ct.l3_sum_ne]
  rw [Finset.sum_congr rfl fun l _ => e2 l, ct.l3_sum_uvec]
  have hd : 1 / Real.sqrt d * (1 / Real.sqrt d) = 1 / (d : ℝ) := by
    rw [div_mul_div_comm, one_mul, Real.mul_self_sqrt (Nat.cast_nonneg d)]
  rw [← Finset.mul_sum, ← mul_assoc, hd]

end Contact

/-! ### The law at a contact; interpolation against `D_*` (UMI) -/

namespace Contact

variable (ct : Contact.{u} d p)

theorem l3_E_mono {f g : Config ct.V → ℝ}
    (h : ∀ σ, wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 → f σ ≤ g σ) : ct.E f ≤ ct.E g :=
  SecB.lawE_mono ct.G h

theorem l3_E_nonneg {f : Config ct.V → ℝ}
    (h : ∀ σ, wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 → 0 ≤ f σ) : 0 ≤ ct.E f :=
  lawE_nonneg ct.G h

theorem l3_E_congr {f g : Config ct.V → ℝ}
    (h : ∀ σ, wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 → f σ = g σ) : ct.E f = ct.E g :=
  lawE_congr ct.G h

theorem l3_E_add (f g : Config ct.V → ℝ) : ct.E (fun σ => f σ + g σ) = ct.E f + ct.E g :=
  lawE_add ct.G f g

theorem l3_E_sub (f g : Config ct.V → ℝ) : ct.E (fun σ => f σ - g σ) = ct.E f - ct.E g :=
  lawE_sub ct.G f g

theorem l3_E_const_mul (c : ℝ) (f : Config ct.V → ℝ) : ct.E (fun σ => c * f σ) = c * ct.E f :=
  lawE_const_mul ct.G c f

theorem l3_E_sum {ι : Type*} (s : Finset ι) (f : ι → Config ct.V → ℝ) :
    ct.E (fun σ => ∑ l ∈ s, f l σ) = ∑ l ∈ s, ct.E (f l) :=
  lawE_sum ct.G s f

theorem l3_Zw_pos (hR : TRegime d p) : 0 < Zw ct.G p (aOf d p) ct.yp ct.ym ct.S := by
  have hs := hR.sOf_pos
  have hsub : ∀ y : ct.V → ℝ, InCube (ct.lam * sOf d p) y → InCube (sOf d p) y := fun y hy k =>
    ⟨(hy k).1, le_trans (hy k).2 (by nlinarith [ct.ctx.lam_le_one, ct.ctx.lam_nonneg])⟩
  exact ct.ctx.pos ct.yp ct.ym (hsub _ ct.ctx.hyp) (hsub _ ct.ctx.hym)

end Contact

/-- `e⁴ ≤ 55`. -/
theorem l3_exp_four_le : Real.exp 4 ≤ 55 := by
  have h := Real.exp_one_lt_d9
  have h0 := Real.exp_pos 1
  have e : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
  rw [e]
  have : Real.exp 1 ^ 4 ≤ (2.7182818286 : ℝ) ^ 4 := pow_le_pow_left₀ h0.le h.le 4
  nlinarith

/-- **UMI at a contact** (Tools `wavg_mul_le_umi` with `D_*` moments `SecB.dstar_moment`, moment
order `k = ⌈log d⌉ + 2`, floor `θ = d⁻²`): if `0 ≤ Y ≤ d² D_*^n` on the support, then
`E[D_*^m Y] ≤ C(m, n) (E Y + θ)`. -/
theorem l3_umi (m n : ℕ) : ∃ C : ℝ, 0 < C ∧ Eventually fun _c₀ _κ₀ d p _h =>
    ∀ ct : Contact.{u} d p, ∀ Y : Config ct.V → ℝ,
      (∀ σ, wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 →
        0 ≤ Y σ ∧ Y σ ≤ (d : ℝ) ^ 2 * ct.Dstar σ ^ n) →
      ct.E (fun σ => ct.Dstar σ ^ m * Y σ) ≤ C * (ct.E Y + thP d) := by
  refine ⟨21 * 12 ^ m * (21 * 12 ^ (n + 1) * 55), by positivity, ?_⟩
  refine ((SecB.dstar_moment.and (SecB.eventually_log_le_p (2 * ((m : ℝ) + n + 2)))).and
    SecB.eventually_h_facts).mono ?_
  rintro c₀ κ₀ d p h ⟨⟨hDs, hlp⟩, hR, -, -, -, -⟩ ct Y hY
  have hd1 : (1 : ℝ) ≤ d := by have := hR.ten_pow_six_le_d; linarith
  have hd0 : (0 : ℝ) < d := by linarith
  have hlogd : 0 ≤ Real.log d := Real.log_nonneg hd1
  obtain ⟨c', hc'⟩ : ∃ c' : ℕ, c' = ⌈Real.log d⌉₊ := ⟨_, rfl⟩
  have hcl : Real.log d ≤ c' := hc' ▸ Nat.le_ceil _
  have hcu : (c' : ℝ) < Real.log d + 1 := hc' ▸ Nat.ceil_lt_add_one hlogd
  have hkp : ∀ j : ℕ, j ≤ m + n + 1 → 2 * (j * (c' + 2)) ≤ p := by
    intro j hj
    have hj' : (j : ℝ) ≤ m + n + 1 := by exact_mod_cast hj
    have h1 : 2 * (j : ℝ) * ((c' : ℝ) + 2) ≤ p := by
      have : (c' : ℝ) + 2 ≤ Real.log d + 3 := by linarith
      calc 2 * (j : ℝ) * ((c' : ℝ) + 2) ≤ 2 * ((m : ℝ) + n + 2) * (Real.log d + 3) :=
            mul_le_mul (by linarith) this (by positivity) (by positivity)
        _ ≤ p := hlp
    have : ((2 * (j * (c' + 2)) : ℕ) : ℝ) ≤ p := by push_cast; linarith
    exact_mod_cast this
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
  have hZw := ct.l3_Zw_pos hR
  -- the weights
  set Z : Config ct.V → ℝ := fun σ => |ct.Dstar σ| ^ m with hZdef
  have hZ0 : ∀ σ, 0 ≤ Z σ := fun σ => pow_nonneg (abs_nonneg _) m
  have hZeq : ∀ σ, wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 → Z σ = ct.Dstar σ ^ m :=
    fun σ hσ => by simp only [hZdef, abs_of_nonneg (SecB.dstar_nonneg ct hσ)]
  set Y' : Config ct.V → ℝ := fun σ =>
    if wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 then Y σ else 0 with hY'def
  have hY'0 : ∀ σ, 0 ≤ Y' σ := fun σ => by
    simp only [hY'def]; split_ifs with hσ
    · exact (hY σ hσ).1
    · exact le_rfl
  have hY'eq : ∀ σ, wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 → Y' σ = Y σ := fun σ hσ => by
    simp only [hY'def, hσ, ne_eq, not_false_eq_true, ↓reduceIte]
  have hDmom : ∀ j : ℕ, 1 ≤ j → j ≤ m + n + 1 →
      ct.E (fun σ => ct.Dstar σ ^ (j * (c' + 2))) ≤ (21 * 12 ^ j) ^ (c' + 2) := by
    intro j hj1 hj2
    have hn1 : 1 ≤ j * (c' + 2) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    calc ct.E (fun σ => ct.Dstar σ ^ (j * (c' + 2)))
        ≤ 3 * (1 + d + (d : ℝ) ^ 2) * 12 ^ (j * (c' + 2)) := hDs ct _ hn1 (hkp j hj2)
      _ ≤ 21 ^ (c' + 2) * 12 ^ (j * (c' + 2)) := mul_le_mul_of_nonneg_right hpow21 (by positivity)
      _ = (21 * 12 ^ j) ^ (c' + 2) := by rw [mul_pow, ← pow_mul, mul_comm j]
  have hZk : ct.E (fun σ => Z σ ^ (c' + 2)) ≤ (21 * 12 ^ m) ^ (c' + 2) := by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · have : ct.E (fun σ => Z σ ^ (c' + 2)) = 1 := by
        rw [← SecB.lawE_const ct.G hZw.ne' 1]
        exact lawE_congr ct.G fun σ _ => by simp [hZdef, hm]
      rw [this, hm, pow_zero, mul_one]
      exact one_le_pow₀ (by norm_num)
    · calc ct.E (fun σ => Z σ ^ (c' + 2)) = ct.E (fun σ => ct.Dstar σ ^ (m * (c' + 2))) :=
            lawE_congr ct.G fun σ hσ => by rw [hZeq σ hσ, ← pow_mul]
        _ ≤ _ := hDmom m hm (by omega)
  have hYk : ct.E (fun σ => Y' σ ^ (c' + 2)) ≤ (21 * 12 ^ (n + 1) * (d : ℝ) ^ 2) ^ (c' + 2) := by
    calc ct.E (fun σ => Y' σ ^ (c' + 2))
        ≤ ct.E (fun σ => (d : ℝ) ^ (2 * (c' + 2)) * ct.Dstar σ ^ ((n + 1) * (c' + 2))) :=
          ct.l3_E_mono fun σ hσ => by
            rw [hY'eq σ hσ]
            have hD1 := ct.l3_one_le_dstar hσ
            have h1 : Y σ ≤ (d : ℝ) ^ 2 * ct.Dstar σ ^ (n + 1) := by
              refine (hY σ hσ).2.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
              exact pow_le_pow_right₀ hD1 (Nat.le_succ n)
            calc Y σ ^ (c' + 2) ≤ ((d : ℝ) ^ 2 * ct.Dstar σ ^ (n + 1)) ^ (c' + 2) :=
                  pow_le_pow_left₀ (hY σ hσ).1 h1 _
              _ = _ := by rw [mul_pow, ← pow_mul, ← pow_mul]
      _ = (d : ℝ) ^ (2 * (c' + 2)) * ct.E (fun σ => ct.Dstar σ ^ ((n + 1) * (c' + 2))) :=
          ct.l3_E_const_mul _ _
      _ ≤ (d : ℝ) ^ (2 * (c' + 2)) * (21 * 12 ^ (n + 1)) ^ (c' + 2) :=
          mul_le_mul_of_nonneg_left (hDmom (n + 1) (by omega) (by omega)) (by positivity)
      _ = _ := by rw [mul_comm ((d : ℝ) ^ (2 * (c' + 2))), mul_pow _ ((d : ℝ) ^ 2), ← pow_mul]
  -- UMI
  have hθ : (0 : ℝ) < thP d := by unfold thP; positivity
  have humi := wavg_mul_le_umi (fun σ => wt_nonneg ct.G σ) hZw hY'0 hZ0
    (show 2 ≤ c' + 2 by omega) (by positivity : (0 : ℝ) ≤ 21 * 12 ^ (n + 1) * (d : ℝ) ^ 2)
    (by positivity : (0 : ℝ) ≤ 21 * 12 ^ m) hθ hYk hZk
  -- the loss `(M/θ)^{1/(k-1)} ≤ 55 · 21 · 12^{n+1}`
  have hk1 : (0 : ℝ) < ((c' + 2 : ℕ) : ℝ) - 1 := by push_cast; linarith
  have hloss : (21 * 12 ^ (n + 1) * (d : ℝ) ^ 2 / thP d) ^ (1 / (((c' + 2 : ℕ) : ℝ) - 1)) ≤
      21 * 12 ^ (n + 1) * 55 := by
    have e1 : 21 * 12 ^ (n + 1) * (d : ℝ) ^ 2 / thP d = 21 * 12 ^ (n + 1) * (d : ℝ) ^ 4 := by
      unfold thP; field_simp
    rw [e1, Real.mul_rpow (by positivity) (by positivity)]
    set r := 1 / (((c' + 2 : ℕ) : ℝ) - 1) with hr
    have hr0 : 0 ≤ r := by positivity
    have hr1 : r ≤ 1 := by rw [hr, div_le_one hk1]; push_cast; linarith
    have hc1 : (1 : ℝ) ≤ 21 * 12 ^ (n + 1) := by
      have : (1 : ℝ) ≤ 12 ^ (n + 1) := one_le_pow₀ (by norm_num)
      linarith
    have a1 : (21 * 12 ^ (n + 1) : ℝ) ^ r ≤ 21 * 12 ^ (n + 1) := by
      calc (21 * 12 ^ (n + 1) : ℝ) ^ r ≤ (21 * 12 ^ (n + 1) : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hc1 hr1
        _ = _ := Real.rpow_one _
    have a2 : ((d : ℝ) ^ 4) ^ r ≤ 55 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hd0.le, Real.rpow_def_of_pos hd0]
      refine le_trans (Real.exp_le_exp.mpr ?_) l3_exp_four_le
      have : Real.log d * r ≤ 1 := by
        rw [hr, mul_one_div, div_le_one hk1]; push_cast; linarith
      push_cast
      nlinarith
    calc (21 * 12 ^ (n + 1) : ℝ) ^ r * ((d : ℝ) ^ 4) ^ r ≤ (21 * 12 ^ (n + 1)) * 55 :=
          mul_le_mul a1 a2 (by positivity) (by positivity)
      _ = _ := by ring
  rw [← lawE_eq_wavg, ← lawE_eq_wavg] at humi
  have hLHS : ct.E (fun σ => ct.Dstar σ ^ m * Y σ) = ct.E (fun σ => Y' σ * Z σ) :=
    ct.l3_E_congr fun σ hσ => by rw [hY'eq σ hσ, hZeq σ hσ, mul_comm]
  have hEY : lawE ct.G p (aOf d p) ct.yp ct.ym ct.S Y' = ct.E Y :=
    ct.l3_E_congr fun σ hσ => hY'eq σ hσ
  rw [hLHS]
  refine humi.trans ?_
  rw [hEY]
  have hEY0 : 0 ≤ ct.E Y + thP d := by
    have : 0 ≤ ct.E Y := ct.l3_E_nonneg fun σ hσ => (hY σ hσ).1
    linarith
  calc 21 * 12 ^ m * (21 * 12 ^ (n + 1) * (d : ℝ) ^ 2 / thP d) ^ (1 / (((c' + 2 : ℕ) : ℝ) - 1)) *
        (ct.E Y + thP d) ≤ 21 * 12 ^ m * (21 * 12 ^ (n + 1) * 55) * (ct.E Y + thP d) := by
        apply mul_le_mul_of_nonneg_right _ hEY0
        exact mul_le_mul_of_nonneg_left hloss (by positivity)
    _ = _ := by ring

/-- `1 ≤ M_ii (M⁻¹)_ii` for positive definite `M` (Cauchy–Schwarz for the form of `M⁻¹` at
`e_i - t M e_i`, `t = 1/M_ii`). -/
theorem l3_inv_diag_ge {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Matrix ι ι ℝ} (hM : M.PosDef)
    (i : ι) : 1 ≤ M i i * M⁻¹ i i := by
  have hMu : IsUnit M.det := isUnit_iff_ne_zero.mpr hM.det_pos.ne'
  have hNsym : ∀ k l, M⁻¹ k l = M⁻¹ l k := fun k l => by simpa using (hM.inv.1.apply l k)
  have hMii : 0 < M i i := hM.diag_pos
  set c : ι → ℝ := fun k => M k i with hc
  set s : ι → ℝ := Pi.single i 1 with hs
  set t := 1 / M i i with ht
  have hNc : M⁻¹ *ᵥ c = s := by
    funext k
    have h1 := congrFun (congrFun (nonsing_inv_mul M hMu) k) i
    rw [mul_apply, one_apply] at h1
    simp only [mulVec, dotProduct, hc, hs, Pi.single_apply, h1]
  have hq := hM.inv.posSemidef.dotProduct_mulVec_nonneg (s - t • c)
  rw [star_trivial, mulVec_sub, mulVec_smul, hNc] at hq
  simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul] at hq
  have e1 : s ⬝ᵥ (M⁻¹ *ᵥ s) = M⁻¹ i i := by
    simp [hs, mulVec, dotProduct, Pi.single_apply]
  have e2 : s ⬝ᵥ s = 1 := by simp [hs, dotProduct, Pi.single_apply]
  have e3 : c ⬝ᵥ (M⁻¹ *ᵥ s) = 1 := by
    have h1 := congrFun (congrFun (nonsing_inv_mul M hMu) i) i
    rw [mul_apply, one_apply, if_pos rfl] at h1
    rw [← h1]
    simp only [hc, hs, mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact Finset.sum_congr rfl fun k _ => by rw [hNsym k i, mul_comm]
  have e4 : c ⬝ᵥ s = M i i := by simp [hc, hs, dotProduct, Pi.single_apply]
  rw [e1, e2, e3, e4] at hq
  have : M⁻¹ i i - 1 / M i i ≥ 0 := by
    have h2 : t * 1 + t * 1 - t * (t * M i i) = 1 / M i i := by
      rw [ht]; field_simp; ring
    nlinarith
  have := mul_le_mul_of_nonneg_left (show 1 / M i i ≤ M⁻¹ i i by linarith) hMii.le
  rwa [mul_one_div_cancel hMii.ne'] at this

/-- **`Ω₊ ≥ 1/5` on the support** ("source saturation gives `Ω₊ ≥ c`", source l.1669–1671), given
the root-source estimate of (D8): `G⁺_vv = y_v h_v ≥ y_v/D_v`, `D_v = 1 + Σ_N c_vi ≤ 2` and
`y_v ≥ 1.95`. -/
theorem l3_omP_ge_of (C₈ : ℝ) : Eventually fun _c₀ _κ₀ d p _h => ∀ ct : Contact.{u} d p,
    |ct.yp ct.v - 2| ≤ C₈ * (epsS d p + η0Of d p + 1 / (d : ℝ)) →
    ∀ σ, wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 → 1 / 5 ≤ ct.OmP σ := by
  obtain ⟨P₀, hPF⟩ := param_facts
  refine ((SecB.eventually_base (80 * |C₈| + 1)).and (eventually_treg_ge P₀)).mono ?_
  rintro c₀ κ₀ d p h ⟨⟨hR, hB, -, -, -, -⟩, -, hP₀⟩ ct hD8 σ hσ
  have hp0 : (0 : ℝ) < p := SecB.regime_p_pos hR
  have hp1 : (1 : ℝ) ≤ p := by have := hR.two_le_p; exact_mod_cast (by omega : 1 ≤ p)
  have hd8 := SecB.regime_p8_le hR
  have hd0 : (0 : ℝ) < d := by have := hR.ten_pow_six_le_d; linarith
  have hpd : (p : ℝ) ≤ d := by nlinarith [pow_le_pow_right₀ hp1 (show 1 ≤ 8 by norm_num)]
  -- smallness of `ε_s + η₀ + 1/d`
  have hes : epsS d p ≤ 1 / p := by
    unfold epsS
    have hsd : (p : ℝ) ^ 4 ≤ Real.sqrt d :=
      calc (p : ℝ) ^ 4 = Real.sqrt (((p : ℝ) ^ 4) ^ 2) := (Real.sqrt_sq (by positivity)).symm
        _ ≤ Real.sqrt d := Real.sqrt_le_sqrt (by nlinarith)
    have hsp : Real.sqrt p ≤ p :=
      calc Real.sqrt p ≤ Real.sqrt ((p : ℝ) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
        _ = p := Real.sqrt_sq hp0.le
    have hsd0 : 0 < Real.sqrt d := Real.sqrt_pos.2 hd0
    rw [div_le_div_iff₀ hsd0 hp0, one_mul]
    have hp3 : (p : ℝ) ^ 3 ≤ (p : ℝ) ^ 4 := pow_le_pow_right₀ hp1 (by norm_num)
    have hsp0 : 0 ≤ Real.sqrt p := Real.sqrt_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left hsp (by positivity : (0 : ℝ) ≤ p * p)]
  have heta : η0Of d p ≤ 2 / p := by
    have h1 := (hPF d p hR hP₀).2.2.2.2.2.1
    refine h1.trans (div_le_div_of_nonneg_left (by norm_num) hp0 ?_)
    calc (p : ℝ) = Real.sqrt ((p : ℝ) ^ 2) := (Real.sqrt_sq hp0.le).symm
      _ ≤ Real.sqrt ((p : ℝ) * d) := Real.sqrt_le_sqrt (by nlinarith)
  have hdinv : 1 / (d : ℝ) ≤ 1 / p := one_div_le_one_div_of_le hp0 hpd
  have hsmall : C₈ * (epsS d p + η0Of d p + 1 / (d : ℝ)) ≤ 1 / 20 := by
    have h4 : epsS d p + η0Of d p + 1 / (d : ℝ) ≤ 4 / p := by
      have : 1 / (p : ℝ) + 2 / p + 1 / p = 4 / p := by ring
      linarith
    have hsum0 : 0 ≤ epsS d p + η0Of d p + 1 / (d : ℝ) := by
      have := hR.η0Of_pos; unfold epsS; positivity
    calc C₈ * (epsS d p + η0Of d p + 1 / (d : ℝ)) ≤ |C₈| * (4 / p) :=
          mul_le_mul (le_abs_self _) h4 hsum0 (abs_nonneg _)
      _ ≤ 1 / 20 := by
          rw [mul_div_assoc', div_le_div_iff₀ hp0 (by norm_num)]
          linarith
  have hyv : 1.95 ≤ ct.yp ct.v := by
    have := (abs_le.mp (hD8.trans hsmall)).1; linarith
  -- `G⁺_vv ≥ y_v/D_v`
  obtain ⟨hP, -⟩ := SecB.posDef_of_wt_ne_zero ct.G hσ
  have hvS : ct.v ∈ ct.S := ct.ctx.mem
  have hPvv : precN ct.G (aOf d p) 1 ct.yp σ ct.S ct.v ct.v = diagD ct.G (aOf d p) ct.yp ct.S ct.v := by
    simp [precN, hvS]
  have hinv := l3_inv_diag_ge hP ct.v
  rw [hPvv] at hinv
  have hDv : diagD ct.G (aOf d p) ct.yp ct.S ct.v ≤ 2 := by
    have hs := hR.sOf_pos
    have hyc : InCube (sOf d p) ct.yp := fun k =>
      ⟨(ct.ctx.hyp k).1, le_trans (ct.ctx.hyp k).2 (by nlinarith [ct.ctx.lam_le_one, ct.ctx.lam_nonneg])⟩
    unfold diagD
    have hc : ∑ j ∈ nbhd ct.G ct.S ct.v, cEdge (aOf d p) ct.yp ct.v j ≤
        ∑ _j ∈ nbhd ct.G ct.S ct.v, 1 / (d : ℝ) :=
      Finset.sum_le_sum fun j _ => SecA.cEdge_le hR hyc ct.v j
    rw [Finset.sum_const, nsmul_eq_mul] at hc
    have hcard := SecB.card_nbhd_le_d ct.G ct.ctx.deg ct.S ct.v
    have : ((nbhd ct.G ct.S ct.v).card : ℝ) * (1 / d) ≤ 1 := by
      rw [mul_one_div, div_le_one hd0]; exact hcard
    linarith
  have hDv1 : 1 ≤ diagD ct.G (aOf d p) ct.yp ct.S ct.v := by
    unfold diagD
    have : 0 ≤ ∑ j ∈ nbhd ct.G ct.S ct.v, cEdge (aOf d p) ct.yp ct.v j :=
      Finset.sum_nonneg fun j _ => FloorIns.cRoot_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _)
        (ct.ctx.hyp _).1) (ct.ctx.hyp _).1)
    linarith
  have hgv : ct.gp σ ct.v ct.v = ct.yp ct.v * hN ct.G (aOf d p) 1 ct.yp σ ct.S ct.v :=
    SecB.greenP_diag ct.G σ ct.S (ct.ctx.hyp _).1
  have hhv : (1 : ℝ) / 2 ≤ hN ct.G (aOf d p) 1 ct.yp σ ct.S ct.v := by
    have e : hN ct.G (aOf d p) 1 ct.yp σ ct.S ct.v = (precN ct.G (aOf d p) 1 ct.yp σ ct.S)⁻¹ ct.v ct.v :=
      rfl
    rw [e]
    nlinarith
  have hG : 0.975 ≤ ct.gp σ ct.v ct.v := by rw [hgv]; nlinarith
  unfold Contact.OmP
  nlinarith

/-! ### FS1: assembly helpers -/

theorem l3_sum_le_card {V : Type*} (s : Finset V) {d : ℝ} (hs : (s.card : ℝ) ≤ d) (f : V → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hf : ∀ x ∈ s, f x ≤ B) : ∑ x ∈ s, f x ≤ d * B :=
  calc ∑ x ∈ s, f x ≤ ∑ _x ∈ s, B := Finset.sum_le_sum hf
    _ = s.card * B := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ d * B := mul_le_mul_of_nonneg_right hs hB

namespace Contact

variable (ct : Contact.{u} d p)

/-- The kernel `L = TᵀT` of (WT2) (definitionally `SecB.kerL`). -/
noncomputable abbrev l3_kerL (h : ℝ) (e dir : Bool) (i : ct.V) (σ : Config ct.V) :
    Matrix (nbhd ct.G ct.S i) (nbhd ct.G ct.S i) ℝ :=
  (ct.tMap h e dir i σ)ᵀ * ct.tMap h e dir i σ

theorem l3_card_nbhd (w : ct.V) : ((nbhd ct.G ct.S w).card : ℝ) ≤ d :=
  SecB.card_nbhd_le_d ct.G ct.ctx.deg ct.S w

/-- The weights `H ∈ {1, Ω₊, Ω₋}` as `c · H₀`, `H₀` a product of at most two physical inverse
diagonals (`diagW`), with `H₀ ≤ D_*²` and (given `Ω₊ ≥ 1/5`) `H ≤ 5 D_*² Ω₊`. -/
theorem l3_H_cases (h : ℝ) (H : Config ct.V → ℝ)
    (hH : H = (fun _ => 1) ∨ H = ct.OmP ∨ H = ct.OmM) :
    ∃ c : ℝ, ∃ l : List (ct.V × Bool × Bool), 0 ≤ c ∧ c ≤ 1 ∧ l.length ≤ 2 ∧
      (∀ σ, H σ = c * ct.diagW h l σ) ∧
      ∀ σ, wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 →
        0 ≤ ct.diagW h l σ ∧ ct.diagW h l σ ≤ ct.Dstar σ ^ 2 ∧
        (1 / 5 ≤ ct.OmP σ → H σ ≤ 5 * ct.Dstar σ ^ 2 * ct.OmP σ) := by
  have hvB := ct.l3_mem_ball_v
  rcases hH with rfl | rfl | rfl
  · refine ⟨1, [], by norm_num, le_rfl, by simp, fun σ => by simp [Contact.diagW],
      fun σ hσ => ?_⟩
    have hD1 := ct.l3_one_le_dstar hσ
    have e : ct.diagW h [] σ = 1 := by simp [Contact.diagW]
    rw [e]
    exact ⟨by norm_num, by nlinarith, fun hO => by nlinarith⟩
  · refine ⟨1 / 4, [(ct.v, true, false), (ct.v, true, false)], by norm_num, by norm_num,
      by simp, fun σ => ?_, fun σ hσ => ?_⟩
    · have e : ct.diagB h σ ct.v true false = ct.gp σ ct.v ct.v := rfl
      simp only [Contact.diagW, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, e,
        Contact.OmP]
      ring
    · have h1 := ct.l3_diagB_le h σ true hvB
      have h0 := ct.l3_diagB_nonneg h hσ true ct.v
      have hD1 := ct.l3_one_le_dstar hσ
      have e : ct.diagW h [(ct.v, true, false), (ct.v, true, false)] σ =
          ct.diagB h σ ct.v true false * ct.diagB h σ ct.v true false := by
        simp [Contact.diagW]
      rw [e]
      refine ⟨mul_nonneg h0 h0, by nlinarith, fun hO => ?_⟩
      have hO0 : 0 ≤ ct.OmP σ := by unfold Contact.OmP; positivity
      have hD2 : 1 ≤ ct.Dstar σ ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hD2 hO0]
  · refine ⟨1 / 4, [(ct.v, true, false), (ct.v, false, false)], by norm_num, by norm_num,
      by simp, fun σ => ?_, fun σ hσ => ?_⟩
    · have e1 : ct.diagB h σ ct.v true false = ct.gp σ ct.v ct.v := rfl
      have e2 : ct.diagB h σ ct.v false false = ct.gm σ ct.v ct.v := rfl
      simp only [Contact.diagW, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, e1, e2,
        Contact.OmM]
      ring
    · have h1 := ct.l3_diagB_le h σ true hvB
      have h0 := ct.l3_diagB_nonneg h hσ true ct.v
      have h1' := ct.l3_diagB_le h σ false hvB
      have h0' := ct.l3_diagB_nonneg h hσ false ct.v
      have hD1 := ct.l3_one_le_dstar hσ
      have e : ct.diagW h [(ct.v, true, false), (ct.v, false, false)] σ =
          ct.diagB h σ ct.v true false * ct.diagB h σ ct.v false false := by
        simp [Contact.diagW]
      rw [e]
      refine ⟨mul_nonneg h0 h0', by nlinarith, fun hO => ?_⟩
      have e1 : ct.diagB h σ ct.v true false = ct.gp σ ct.v ct.v := rfl
      have e2 : ct.diagB h σ ct.v false false = ct.gm σ ct.v ct.v := rfl
      rw [e1] at h1 h0
      rw [e2] at h1' h0'
      unfold Contact.OmM
      nlinarith [mul_le_mul h1 h1' h0' (by linarith)]

/-- FS2 consequence, pointwise: `c H₀ Σ_{j∼i} F_ji² ≤ 2 a² c (H q_{L_dir}(ξ) + H q_{L_cav}(ξ))`
with `H = H₀ (X_e)_ii² (X₊)_ii²` the weight of (WT2). -/
theorem l3_fs1_pt {h : ℝ} (hh : 0 ≤ h) (e : Bool) {σ : Config ct.V}
    (hσ : wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0) {i : ct.V} (hi : i ∈ ct.N) {c : ℝ}
    (hc : 0 ≤ c) (l : List (ct.V × Bool × Bool)) (hW0 : 0 ≤ ct.diagW h l σ) :
    c * ct.diagW h l σ * ∑ j ∈ nbhd ct.G ct.S i, maskF (ct.Xb h e σ) (ct.XP h σ) ct.uvec j i ^ 2 ≤
      2 * aOf d p ^ 2 * c *
        (ct.wtH h e i l σ * qForm (ct.l3_kerL h e true i σ) (rootSigns ct.G σ ct.S i) +
          ct.wtH h e i l σ * qForm (ct.l3_kerL h e false i σ) (rootSigns ct.G σ ct.S i)) := by
  set ξ := rootSigns ct.G σ ct.S i
  have hq : ∀ dir : Bool, qForm (ct.l3_kerL h e dir i σ) ξ =
      ∑ j, (ct.tMap h e dir i σ *ᵥ ξ) j ^ 2 := fun dir => l3_qForm_tt _ _
  rw [hq true, hq false, show ct.tMap h e true i σ = ct.tDir h e i σ from rfl,
    show ct.tMap h e false i σ = ct.tCav h e i σ from rfl]
  have hF : ∑ j ∈ nbhd ct.G ct.S i, maskF (ct.Xb h e σ) (ct.XP h σ) ct.uvec j i ^ 2 =
      (aOf d p * ct.Xb h e σ i i * ct.XP h σ i i) ^ 2 *
        ∑ j : nbhd ct.G ct.S i, ((ct.tDir h e i σ *ᵥ ξ) j + (ct.tCav h e i σ *ᵥ ξ) j) ^ 2 := by
    rw [← Finset.sum_coe_sort (nbhd ct.G ct.S i), Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [fs2 ct hh e hσ hi j]; ring
  have hsq : ∑ j : nbhd ct.G ct.S i, ((ct.tDir h e i σ *ᵥ ξ) j + (ct.tCav h e i σ *ᵥ ξ) j) ^ 2 ≤
      2 * (∑ j, (ct.tDir h e i σ *ᵥ ξ) j ^ 2 + ∑ j, (ct.tCav h e i σ *ᵥ ξ) j ^ 2) := by
    rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun j _ => by
      nlinarith [sq_nonneg ((ct.tDir h e i σ *ᵥ ξ) j - (ct.tCav h e i σ *ᵥ ξ) j)]
  rw [hF]
  have hA : 0 ≤ c * ct.diagW h l σ * (aOf d p * ct.Xb h e σ i i * ct.XP h σ i i) ^ 2 := by
    positivity
  calc c * ct.diagW h l σ * ((aOf d p * ct.Xb h e σ i i * ct.XP h σ i i) ^ 2 *
        ∑ j : nbhd ct.G ct.S i, ((ct.tDir h e i σ *ᵥ ξ) j + (ct.tCav h e i σ *ᵥ ξ) j) ^ 2)
      = c * ct.diagW h l σ * (aOf d p * ct.Xb h e σ i i * ct.XP h σ i i) ^ 2 *
        ∑ j : nbhd ct.G ct.S i, ((ct.tDir h e i σ *ᵥ ξ) j + (ct.tCav h e i σ *ᵥ ξ) j) ^ 2 := by
        ring
    _ ≤ c * ct.diagW h l σ * (aOf d p * ct.Xb h e σ i i * ct.XP h σ i i) ^ 2 *
        (2 * (∑ j, (ct.tDir h e i σ *ᵥ ξ) j ^ 2 + ∑ j, (ct.tCav h e i σ *ᵥ ξ) j ^ 2)) :=
        mul_le_mul_of_nonneg_left hsq hA
    _ = _ := by unfold Contact.wtH; ring

/-- The direct part of FS1 in mean: with `W5` at weight `D_*⁸`,
`E[H tr(T_dirᵀ T_dir)] ≤ 4 C₅/√h` for `H = H₀ (X_e)_ii² (X₊)_ii²`, `H₀ ≤ D_*²`. -/
theorem l3_fs1_dir (hR : TRegime d p) {h : ℝ} (hh : 0 < h) (hh2 : h ≤ 1 / 2) (e : Bool)
    (l : List (ct.V × Bool × Bool))
    (hW : ∀ σ, wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 →
      0 ≤ ct.diagW h l σ ∧ ct.diagW h l σ ≤ ct.Dstar σ ^ 2) {C₅ : ℝ}
    (hW5 : ∀ k ∈ ct.S, ct.E (fun σ => ct.Dstar σ ^ 8 * (ct.Xb h e σ * ct.Xb h e σ) k k) ≤
      C₅ / Real.sqrt h) {i : ct.V} (hi : i ∈ ct.N) :
    ct.E (fun σ => ct.wtH h e i l σ * (ct.l3_kerL h e true i σ).trace) ≤
      4 * C₅ / Real.sqrt h := by
  have hd0 : (0 : ℝ) < d := by have := hR.ten_pow_six_le_d; linarith
  have hiS : i ∈ ct.S := (Finset.mem_filter.1 hi).1
  set J' := (nbhd ct.G ct.S i).filter (· ∈ ct.N) with hJ'
  have hsq : ∀ σ, wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 → ∀ k,
      ∑ j, ct.Xb h e σ k j ^ 2 = (ct.Xb h e σ * ct.Xb h e σ) k k := fun σ hσ k => by
    obtain ⟨E1, -⟩ := ct.l3_branch_facts hR hh hh2 e hσ
    rw [mul_apply]; exact Finset.sum_congr rfl fun j _ => by rw [sq, E1 j k]
  have hpt : ∀ σ, wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 →
      ct.wtH h e i l σ * (ct.l3_kerL h e true i σ).trace ≤
        2 / d * ∑ k ∈ J', (ct.Dstar σ ^ 8 * (ct.Xb h e σ * ct.Xb h e σ) k k +
          ct.Dstar σ ^ 8 * (ct.Xb h e σ * ct.Xb h e σ) i i) := by
    intro σ hσ
    have hdir := l3_dir_pt ct hR hh hh2 e hσ hi
    have htr0 : 0 ≤ ct.Xb h e σ i i ^ 2 * ct.XP h σ i i ^ 2 *
        ((ct.tDir h e i σ)ᵀ * ct.tDir h e i σ).trace := by
      have := Matrix.posSemidef_conjTranspose_mul_self (ct.tDir h e i σ)
      rw [conjTranspose_eq_transpose_of_trivial] at this
      exact mul_nonneg (by positivity) this.trace_nonneg
    obtain ⟨hW0, hW1⟩ := hW σ hσ
    have hD1 := ct.l3_one_le_dstar hσ
    have e1 : ct.wtH h e i l σ * (ct.l3_kerL h e true i σ).trace = ct.diagW h l σ *
        (ct.Xb h e σ i i ^ 2 * ct.XP h σ i i ^ 2 *
          ((ct.tDir h e i σ)ᵀ * ct.tDir h e i σ).trace) := by
      unfold Contact.wtH l3_kerL; rw [show ct.tMap h e true i σ = ct.tDir h e i σ from rfl]
      ring
    rw [e1]
    calc ct.diagW h l σ * (ct.Xb h e σ i i ^ 2 * ct.XP h σ i i ^ 2 *
          ((ct.tDir h e i σ)ᵀ * ct.tDir h e i σ).trace)
        ≤ ct.Dstar σ ^ 2 * (2 * ct.Dstar σ ^ 6 / d * ∑ k ∈ J',
            (∑ j, ct.Xb h e σ k j ^ 2 + ∑ j, ct.Xb h e σ i j ^ 2)) :=
          mul_le_mul hW1 hdir htr0 (by positivity)
      _ = _ := by
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [hsq σ hσ k, hsq σ hσ i]
          ring
  calc ct.E (fun σ => ct.wtH h e i l σ * (ct.l3_kerL h e true i σ).trace)
      ≤ ct.E (fun σ => 2 / d * ∑ k ∈ J', (ct.Dstar σ ^ 8 * (ct.Xb h e σ * ct.Xb h e σ) k k +
          ct.Dstar σ ^ 8 * (ct.Xb h e σ * ct.Xb h e σ) i i)) := ct.l3_E_mono hpt
    _ = 2 / d * ∑ k ∈ J', (ct.E (fun σ => ct.Dstar σ ^ 8 * (ct.Xb h e σ * ct.Xb h e σ) k k) +
          ct.E (fun σ => ct.Dstar σ ^ 8 * (ct.Xb h e σ * ct.Xb h e σ) i i)) := by
        rw [ct.l3_E_const_mul, ct.l3_E_sum]
        congr 1
        exact Finset.sum_congr rfl fun k _ => ct.l3_E_add _ _
    _ ≤ 2 / d * (d * (2 * (C₅ / Real.sqrt h))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have hcard : (J'.card : ℝ) ≤ d :=
          le_trans (by exact_mod_cast Finset.card_filter_le _ _) (ct.l3_card_nbhd i)
        refine l3_sum_le_card J' hcard _ ?_ fun k hk => ?_
        · have : 0 ≤ ct.E (fun σ => ct.Dstar σ ^ 8 * (ct.Xb h e σ * ct.Xb h e σ) i i) :=
            ct.l3_E_nonneg fun σ hσ => by
              rw [← hsq σ hσ i]
              exact mul_nonneg (by have := ct.l3_one_le_dstar hσ; positivity)
                (Finset.sum_nonneg fun j _ => sq_nonneg _)
          linarith [hW5 i hiS]
        · have hkN : k ∈ ct.N := (Finset.mem_filter.1 hk).2
          have hkS : k ∈ ct.S := (Finset.mem_filter.1 hkN).1
          linarith [hW5 k hkS, hW5 i hiS]
    _ = 4 * C₅ / Real.sqrt h := by field_simp; ring

/-- The cavity part of FS1, pointwise and summed over `i ∈ N`:
`a² Σ_{i∈N} (X_e)_ii² (X₊)_ii² tr(T_cavᵀ T_cav) ≤ 8 D_*² h⁻² (Y₁ + a² (D_*/h) Y₂)` with
`Y₁ = 4uᵀ(K₊-M₊)b₊`, `Y₂ = 4uᵀ(K₊-M₊)u`. -/
theorem l3_fs1_cav (hR : TRegime d p) {h : ℝ} (hh : 0 < h) (hh2 : h ≤ 1 / 2) (e : Bool)
    {σ : Config ct.V} (hσ : wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0) :
    aOf d p ^ 2 * ∑ i ∈ ct.N, ct.Xb h e σ i i ^ 2 * ct.XP h σ i i ^ 2 *
        ((ct.tCav h e i σ)ᵀ * ct.tCav h e i σ).trace ≤
      8 * ct.Dstar σ ^ 2 * h⁻¹ ^ 2 *
        (4 * (ct.uvec ⬝ᵥ (ct.KP h σ *ᵥ ct.bP h σ) - ct.uvec ⬝ᵥ (ct.MP h σ *ᵥ ct.bP h σ)) +
          aOf d p ^ 2 * (ct.Dstar σ / h) *
            (4 * (ct.uvec ⬝ᵥ (ct.KP h σ *ᵥ ct.uvec) - ct.uvec ⬝ᵥ (ct.MP h σ *ᵥ ct.uvec)))) := by
  rw [ct.l3_Y1_eq, ct.l3_Y2_eq]
  have hsum := Finset.sum_le_sum fun i (hi : i ∈ ct.N) => l3_cav_pt ct hR hh hh2 e hσ hi
  have hrhs : ∑ i ∈ ct.N, 4 * ct.Dstar σ ^ 2 * h⁻¹ ^ 2 * (2 / d * (ct.XP h σ i i ^ 2 *
        ∑ l ∈ nbhd ct.G ct.S i, ∑ k ∈ ct.N.erase l, ct.XP h σ k l ^ 2 +
        ct.Dstar σ / h * ∑ k ∈ ct.N.erase i, ct.XP h σ k i ^ 2)) =
      8 * ct.Dstar σ ^ 2 * h⁻¹ ^ 2 * (1 / d * ∑ i ∈ ct.N, ct.XP h σ i i ^ 2 *
        ∑ l ∈ nbhd ct.G ct.S i, ∑ k ∈ ct.N.erase l, ct.XP h σ k l ^ 2 +
        ct.Dstar σ / h * (1 / d * ∑ i ∈ ct.N, ∑ k ∈ ct.N.erase i, ct.XP h σ k i ^ 2)) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hrhs] at hsum
  have ha0 : 0 ≤ aOf d p ^ 2 := sq_nonneg _
  calc aOf d p ^ 2 * ∑ i ∈ ct.N, ct.Xb h e σ i i ^ 2 * ct.XP h σ i i ^ 2 *
        ((ct.tCav h e i σ)ᵀ * ct.tCav h e i σ).trace
      ≤ aOf d p ^ 2 * (8 * ct.Dstar σ ^ 2 * h⁻¹ ^ 2 * (1 / d * ∑ i ∈ ct.N, ct.XP h σ i i ^ 2 *
        ∑ l ∈ nbhd ct.G ct.S i, ∑ k ∈ ct.N.erase l, ct.XP h σ k l ^ 2 +
        ct.Dstar σ / h * (1 / d * ∑ i ∈ ct.N, ∑ k ∈ ct.N.erase i, ct.XP h σ k i ^ 2))) :=
        mul_le_mul_of_nonneg_left hsum ha0
    _ = _ := by ring

/-- Envelopes of the two energies: `0 ≤ Y₁ ≤ d D_*⁴`, `0 ≤ Y₂ ≤ d D_*²` (on the support). -/
theorem l3_Y_env (hR : TRegime d p) {h : ℝ} (hh : 0 < h) (hh2 : h ≤ 1 / 2) {σ : Config ct.V}
    (hσ : wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0) :
    (0 ≤ 4 * (ct.uvec ⬝ᵥ (ct.KP h σ *ᵥ ct.bP h σ) - ct.uvec ⬝ᵥ (ct.MP h σ *ᵥ ct.bP h σ)) ∧
      4 * (ct.uvec ⬝ᵥ (ct.KP h σ *ᵥ ct.bP h σ) - ct.uvec ⬝ᵥ (ct.MP h σ *ᵥ ct.bP h σ)) ≤
        d * ct.Dstar σ ^ 4) ∧
    (0 ≤ 4 * (ct.uvec ⬝ᵥ (ct.KP h σ *ᵥ ct.uvec) - ct.uvec ⬝ᵥ (ct.MP h σ *ᵥ ct.uvec)) ∧
      4 * (ct.uvec ⬝ᵥ (ct.KP h σ *ᵥ ct.uvec) - ct.uvec ⬝ᵥ (ct.MP h σ *ᵥ ct.uvec)) ≤
        d * ct.Dstar σ ^ 2) := by
  rw [ct.l3_Y1_eq, ct.l3_Y2_eq]
  obtain ⟨-, -, -, P4, -, P6⟩ := ct.l3_branch_facts hR hh hh2 true hσ
  have hXP : ct.Xb h true σ = ct.XP h σ := rfl
  rw [hXP] at P4 P6
  have hd0 : (0 : ℝ) < d := by have := hR.ten_pow_six_le_d; linarith
  have ha := hR.pf_a_sq_le
  have hD1 := ct.l3_one_le_dstar hσ
  set D := ct.Dstar σ with hD
  have hent : ∀ k l, k ∈ ct.l3_ball → l ∈ ct.l3_ball → ct.XP h σ k l ^ 2 ≤ D ^ 2 := by
    intro k l hk hl
    have a1 := P6 k l; have b1 := P4 k hk; have b2 := P4 l hl
    nlinarith [mul_le_mul b1.2 b2.2 b2.1 (by linarith : (0 : ℝ) ≤ D)]
  have hN : (ct.N.card : ℝ) ≤ d := ct.l3_card_nbhd ct.v
  refine ⟨⟨by positivity, ?_⟩, ⟨by positivity, ?_⟩⟩
  · have h1 : ∑ i ∈ ct.N, ct.XP h σ i i ^ 2 *
        ∑ l ∈ nbhd ct.G ct.S i, ∑ k ∈ ct.N.erase l, ct.XP h σ k l ^ 2 ≤ d * (D ^ 2 * (d * (d * D ^ 2))) := by
      refine l3_sum_le_card _ hN _ (by positivity) fun i hi => ?_
      refine mul_le_mul (hent i i (ct.l3_mem_ball_N hi) (ct.l3_mem_ball_N hi)) ?_
        (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
      refine l3_sum_le_card _ (ct.l3_card_nbhd i) _ (by positivity) fun l hl => ?_
      refine l3_sum_le_card _ (le_trans (by exact_mod_cast Finset.card_erase_le) hN) _
        (by positivity) fun k hk => ?_
      exact hent k l (ct.l3_mem_ball_N (Finset.mem_of_mem_erase hk)) (ct.l3_mem_ball_nbhd hi hl)
    calc aOf d p ^ 2 / d * ∑ i ∈ ct.N, ct.XP h σ i i ^ 2 *
          ∑ l ∈ nbhd ct.G ct.S i, ∑ k ∈ ct.N.erase l, ct.XP h σ k l ^ 2
        ≤ 1 / d / d * (d * (D ^ 2 * (d * (d * D ^ 2)))) := by
          apply mul_le_mul _ h1 (by positivity) (by positivity)
          exact div_le_div_of_nonneg_right ha hd0.le
      _ = d * D ^ 4 := by field_simp
  · have h1 : ∑ i ∈ ct.N, ∑ k ∈ ct.N.erase i, ct.XP h σ k i ^ 2 ≤ d * (d * D ^ 2) := by
      refine l3_sum_le_card _ hN _ (by positivity) fun i hi => ?_
      refine l3_sum_le_card _ (le_trans (by exact_mod_cast Finset.card_erase_le) hN) _
        (by positivity) fun k hk => ?_
      exact hent k i (ct.l3_mem_ball_N (Finset.mem_of_mem_erase hk)) (ct.l3_mem_ball_N hi)
    calc 1 / d * ∑ i ∈ ct.N, ∑ k ∈ ct.N.erase i, ct.XP h σ k i ^ 2 ≤ 1 / d * (d * (d * D ^ 2)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = d * D ^ 2 := by field_simp

/-- `E[Ω₊ · 4uᵀ(K₊-M₊)f] = 4 (E[Ω₊ uᵀK₊f] - E[Ω₊ uᵀM₊f])`. -/
theorem l3_E_energy (h : ℝ) (f : Config ct.V → ct.V → ℝ) :
    ct.E (fun σ => ct.OmP σ *
        (4 * (ct.uvec ⬝ᵥ (ct.KP h σ *ᵥ f σ) - ct.uvec ⬝ᵥ (ct.MP h σ *ᵥ f σ)))) =
      4 * (ct.E (fun σ => ct.OmP σ * (ct.uvec ⬝ᵥ (ct.KP h σ *ᵥ f σ))) -
        ct.E (fun σ => ct.OmP σ * (ct.uvec ⬝ᵥ (ct.MP h σ *ᵥ f σ)))) := by
  rw [← ct.l3_E_sub, ← ct.l3_E_const_mul]
  exact ct.l3_E_congr fun σ _ => by ring

end Contact

/-- The closing real arithmetic of FS1. -/
theorem l3_fs1_real {K C₅ CU1 CU2 A Dd Cc Er sh hi2 ZA QT β θ E1 E2 b : ℝ}
    (hK : 0 < K) (hC₅ : 0 < C₅) (hCU1 : 0 < CU1) (hCU2 : 0 < CU2) (hsh : 0 < sh)
    (hhi : 1 ≤ hi2) (hZA : 0 ≤ ZA) (hQT : 0 ≤ QT) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hθ : 0 < θ)
    (hb0 : 0 ≤ b) (hbβ : b ≤ β) (hA : A ≤ Dd + Cc + Er) (hDd : Dd ≤ 8 * K * C₅ / sh)
    (hEr : Er ≤ 8 * K * θ) (hCc : Cc ≤ K * (80 * hi2 * (E1 + b * E2)))
    (hE1 : E1 ≤ CU1 * (4 * ZA + θ)) (hE2 : E2 ≤ CU2 * (4 * QT + θ)) :
    A ≤ (8 * K * C₅ + 320 * K * (CU1 + CU2) + 8 * K + 1) * hi2 * (ZA + β * QT + θ) +
      (8 * K * C₅ + 320 * K * (CU1 + CU2) + 8 * K + 1) / sh := by
  have hZ0 : 0 ≤ ZA + β * QT + θ := by positivity
  have hbE2 : b * E2 ≤ CU2 * (4 * β * QT + θ) := by
    have t1 : b * E2 ≤ b * (CU2 * (4 * QT + θ)) := mul_le_mul_of_nonneg_left hE2 hb0
    have t2 : b * QT ≤ β * QT := mul_le_mul_of_nonneg_right hbβ hQT
    have t3 : b * θ ≤ θ := by nlinarith
    have t4 : b * (CU2 * (4 * QT + θ)) = CU2 * (4 * (b * QT) + b * θ) := by ring
    have t5 : CU2 * (4 * (b * QT) + b * θ) ≤ CU2 * (4 * (β * QT) + θ) :=
      mul_le_mul_of_nonneg_left (by linarith) hCU2.le
    have t6 : CU2 * (4 * (β * QT) + θ) = CU2 * (4 * β * QT + θ) := by ring
    linarith
  have hS : E1 + b * E2 ≤ 4 * (CU1 + CU2) * (ZA + β * QT + θ) := by
    have h1 : 0 ≤ CU1 * (β * QT) := mul_nonneg hCU1.le (mul_nonneg hβ0 hQT)
    have h2 : 0 ≤ CU2 * ZA := mul_nonneg hCU2.le hZA
    have h3 : 0 ≤ CU1 * θ := mul_nonneg hCU1.le hθ.le
    have h4 : 0 ≤ CU2 * θ := mul_nonneg hCU2.le hθ.le
    have e1 : 4 * (CU1 + CU2) * (ZA + β * QT + θ) = 4 * (CU1 * ZA) + 4 * (CU1 * (β * QT)) +
        4 * (CU1 * θ) + 4 * (CU2 * ZA) + 4 * (CU2 * (β * QT)) + 4 * (CU2 * θ) := by ring
    have e2 : CU1 * (4 * ZA + θ) = 4 * (CU1 * ZA) + CU1 * θ := by ring
    have e3 : CU2 * (4 * β * QT + θ) = 4 * (CU2 * (β * QT)) + CU2 * θ := by ring
    linarith
  have hCc' : Cc ≤ 320 * K * (CU1 + CU2) * hi2 * (ZA + β * QT + θ) := by
    have hi0 : 0 ≤ hi2 := by linarith
    calc Cc ≤ K * (80 * hi2 * (E1 + b * E2)) := hCc
      _ ≤ K * (80 * hi2 * (4 * (CU1 + CU2) * (ZA + β * QT + θ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hS (by positivity)) hK.le
      _ = _ := by ring
  have hEr' : Er ≤ 8 * K * hi2 * (ZA + β * QT + θ) := by
    have t1 : θ ≤ ZA + β * QT + θ := by nlinarith [mul_nonneg hβ0 hQT]
    have t2 : ZA + β * QT + θ ≤ hi2 * (ZA + β * QT + θ) := by nlinarith
    calc Er ≤ 8 * K * θ := hEr
      _ ≤ 8 * K * (hi2 * (ZA + β * QT + θ)) :=
          mul_le_mul_of_nonneg_left (t1.trans t2) (by positivity)
      _ = _ := by ring
  have hDd' : Dd ≤ (8 * K * C₅ + 320 * K * (CU1 + CU2) + 8 * K + 1) / sh :=
    hDd.trans (div_le_div_of_nonneg_right (by nlinarith [mul_pos hK hCU1, mul_pos hK hCU2])
      hsh.le)
  have hP : 0 ≤ hi2 * (ZA + β * QT + θ) := by
    have : 0 ≤ hi2 := by linarith
    positivity
  have hfin : 320 * K * (CU1 + CU2) * hi2 * (ZA + β * QT + θ) +
      8 * K * hi2 * (ZA + β * QT + θ) ≤
      (8 * K * C₅ + 320 * K * (CU1 + CU2) + 8 * K + 1) * hi2 * (ZA + β * QT + θ) := by
    have e : (8 * K * C₅ + 320 * K * (CU1 + CU2) + 8 * K + 1) * hi2 * (ZA + β * QT + θ) =
        320 * K * (CU1 + CU2) * hi2 * (ZA + β * QT + θ) + 8 * K * hi2 * (ZA + β * QT + θ) +
          (8 * K * C₅ + 1) * (hi2 * (ZA + β * QT + θ)) := by ring
    rw [e]
    have : 0 ≤ (8 * K * C₅ + 1) * (hi2 * (ZA + β * QT + θ)) := mul_nonneg (by positivity) hP
    linarith
  linarith

/-- **FS1 from (D8)** (the parent check of `fs1_fixed_mask`). Children: FS2 (`fs2`), WT2
(`SecB.wt2`, `m₀ = 2`, `M = 2`), W5 (`in_W5 8`), UMI (`l3_umi`), the pointwise direct/cavity bounds
(`l3_dir_pt`, `l3_cav_pt`), the energy identities (`l3_Y1_eq`, `l3_Y2_eq`) and `Ω₊ ≥ 1/5`
(`l3_omP_ge_of`). -/
theorem l3_fs1_of_d8 {C₈ : ℝ} (hD8 : Eventually fun _c₀ _κ₀ d p _h => ∀ ct : Contact.{u} d p,
      |ct.yp ct.v - 2| + |(ct.N.card : ℝ) / d - 1| + 1 / (d : ℝ) * ∑ i ∈ ct.N, |ct.yp i - 2| ≤
        C₈ * (epsS d p + η0Of d p + 1 / (d : ℝ)))
    {K : ℝ} (hK : 0 < K) (hWT : Eventually fun _ _ d p h =>
      ∀ ct : Contact.{u} d p, ∀ i ∈ ct.N, ∀ e dir : Bool, ∀ l : List (ct.V × Bool × Bool),
        l.length ≤ 2 →
        ct.E (fun σ => ct.wtH h e i l σ *
            qForm (ct.l3_kerL h e dir i σ) (rootSigns ct.G σ ct.S i)) ≤
          K * ct.E (fun σ => ct.wtH h e i l σ * (ct.l3_kerL h e dir i σ).trace) +
            K / (d : ℝ) ^ 2 + K * Real.exp (-(p : ℝ)))
    {C₅ : ℝ} (hC₅ : 0 < C₅) (hW5 : Eventually fun _c₀ _κ₀ d p h =>
      ∀ ct : Contact.{u} d p, ∀ i ∈ ct.S,
        ct.E (fun σ => ct.Dstar σ ^ 8 * (ct.XP h σ * ct.XP h σ) i i) ≤ C₅ / Real.sqrt h ∧
        ct.E (fun σ => ct.Dstar σ ^ 8 * (ct.XM h σ * ct.XM h σ) i i) ≤ C₅ / Real.sqrt h) :
    ∃ C : ℝ, 0 < C ∧ Eventually fun _c₀ _κ₀ d p h =>
    ∀ ct : Contact.{u} d p, ∀ Xe : Config ct.V → Matrix ct.V ct.V ℝ,
      (Xe = ct.XP h ∨ Xe = ct.XM h) → ∀ H : Config ct.V → ℝ,
      (H = (fun _ => 1) ∨ H = ct.OmP ∨ H = ct.OmM) →
      ∑ i ∈ ct.N, ∑ j ∈ nbhd ct.G ct.S i,
          ct.E (fun σ => H σ * maskF (Xe σ) (ct.XP h σ) ct.uvec j i ^ 2) ≤
        C * h⁻¹ ^ 2 * (ct.zeta h - ct.alphaE h + 1 / (d * h) * (ct.qP h - ct.tP h) + thP d) +
          C / Real.sqrt h := by
  obtain ⟨CU1, hCU1, hU1⟩ := l3_umi.{u} 4 6
  obtain ⟨CU2, hCU2, hU2⟩ := l3_umi.{u} 5 4
  refine ⟨8 * K * C₅ + 320 * K * (CU1 + CU2) + 8 * K + 1, by positivity, ?_⟩
  refine ((((((((hWT.and hW5).and hU1).and hU2).and hD8).and (l3_omP_ge_of C₈)).and
    (SecB.eventually_log_le_p 2)).and (SecB.eventually_base 2)).and
    SecB.eventually_h_facts).mono ?_
  rintro c₀ κ₀ d p h ⟨⟨⟨⟨⟨⟨⟨⟨HWT, HW5⟩, HU1⟩, HU2⟩, HD8⟩, HΩ⟩, Hlog⟩,
    ⟨-, hp2, -, hhκ, hk0, hk1⟩⟩, hR, h0, hdh, h1, -⟩ ct Xe hXe H hH
  -- parameters
  have hd1 : (1 : ℝ) ≤ d := by have := hR.ten_pow_six_le_d; linarith
  have hd0 : (0 : ℝ) < d := by linarith
  have hdd : (d : ℝ) ≤ (d : ℝ) ^ 2 := by nlinarith
  have hh2 : h ≤ 1 / 2 := by
    rw [hhκ]
    have h16 : (16 : ℝ) ≤ (p : ℝ) ^ 4 := by
      have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hp2 4
      norm_num at this ⊢; linarith
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have ha := hR.pf_a_sq_le
  have had : (d : ℝ) * aOf d p ^ 2 ≤ 1 := by
    have := hR.pf_d_a_sq_le
    have : 1 / (d : ℝ) ≤ 1 / 4 :=
      one_div_le_one_div_of_le (by norm_num) (by have := hR.ten_pow_six_le_d; linarith)
    linarith
  have hθ0 : 0 < thP d := by unfold thP; positivity
  have hexp : Real.exp (-(p : ℝ)) ≤ thP d := by
    have hlog0 : 0 ≤ Real.log d := Real.log_nonneg hd1
    have e2 : Real.exp (2 * Real.log d) = (d : ℝ) ^ 2 := by
      rw [show 2 * Real.log d = Real.log d + Real.log d by ring, Real.exp_add, Real.exp_log hd0]
      ring
    calc Real.exp (-(p : ℝ)) ≤ Real.exp (-(2 * Real.log d)) := Real.exp_le_exp.mpr (by linarith)
      _ = thP d := by rw [Real.exp_neg, e2, thP, one_div]
  have hsqh : 0 < Real.sqrt h := Real.sqrt_pos.2 h0
  have hD8v : |ct.yp ct.v - 2| ≤ C₈ * (epsS d p + η0Of d p + 1 / (d : ℝ)) := by
    have h8 := HD8 ct
    have a1 := abs_nonneg ((ct.N.card : ℝ) / d - 1)
    have a2 : 0 ≤ 1 / (d : ℝ) * ∑ i ∈ ct.N, |ct.yp i - 2| := by positivity
    linarith
  have hhinv : 1 ≤ h⁻¹ ^ 2 := by
    have : 1 ≤ h⁻¹ := by rw [le_inv_comm₀ (by norm_num) h0, inv_one]; exact h1
    nlinarith
  have hβ : aOf d p ^ 2 * h⁻¹ ≤ 1 / (d * h) := by
    rw [one_div, mul_inv]
    exact mul_le_mul_of_nonneg_right (by rw [← one_div]; exact ha) (inv_nonneg.2 h0.le)
  have hβ1 : 1 / (d * h) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have := (div_le_iff₀ hd0).1 (show 1 / (d : ℝ) ≤ h from hdh); linarith
  -- the energies are nonnegative and are the means of `Ω₊ Y₁`, `Ω₊ Y₂`
  set Y1 : Config ct.V → ℝ := fun σ =>
    4 * (ct.uvec ⬝ᵥ (ct.KP h σ *ᵥ ct.bP h σ) - ct.uvec ⬝ᵥ (ct.MP h σ *ᵥ ct.bP h σ)) with hY1
  set Y2 : Config ct.V → ℝ := fun σ =>
    4 * (ct.uvec ⬝ᵥ (ct.KP h σ *ᵥ ct.uvec) - ct.uvec ⬝ᵥ (ct.MP h σ *ᵥ ct.uvec)) with hY2
  have hOm : ∀ σ, wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 →
      0 ≤ ct.OmP σ ∧ ct.OmP σ ≤ ct.Dstar σ ^ 2 := fun σ hσ => by
    have h1' := ct.l3_diagB_le h σ true ct.l3_mem_ball_v
    have h0' := ct.l3_diagB_nonneg h hσ true ct.v
    have e : ct.diagB h σ ct.v true false = ct.gp σ ct.v ct.v := rfl
    rw [e] at h1' h0'
    have hD1 := ct.l3_one_le_dstar hσ
    unfold Contact.OmP
    constructor
    · positivity
    · nlinarith
  have hEY1 : ct.E (fun σ => ct.OmP σ * Y1 σ) = 4 * (ct.zeta h - ct.alphaE h) :=
    ct.l3_E_energy h (ct.bP h)
  have hEY2 : ct.E (fun σ => ct.OmP σ * Y2 σ) = 4 * (ct.qP h - ct.tP h) :=
    ct.l3_E_energy h (fun _ => ct.uvec)
  have hY1pos : 0 ≤ ct.E (fun σ => ct.OmP σ * Y1 σ) := ct.l3_E_nonneg fun σ hσ =>
    mul_nonneg (hOm σ hσ).1 (ct.l3_Y_env hR h0 hh2 hσ).1.1
  have hY2pos : 0 ≤ ct.E (fun σ => ct.OmP σ * Y2 σ) := ct.l3_E_nonneg fun σ hσ =>
    mul_nonneg (hOm σ hσ).1 (ct.l3_Y_env hR h0 hh2 hσ).2.1
  have hZA : 0 ≤ ct.zeta h - ct.alphaE h := by linarith
  have hQT : 0 ≤ ct.qP h - ct.tP h := by linarith
  -- UMI for the two energies
  have hUY1 : ct.E (fun σ => ct.Dstar σ ^ 4 * (ct.OmP σ * Y1 σ)) ≤
      CU1 * (4 * (ct.zeta h - ct.alphaE h) + thP d) := by
    rw [← hEY1]
    refine HU1 ct _ fun σ hσ => ⟨mul_nonneg (hOm σ hσ).1 (ct.l3_Y_env hR h0 hh2 hσ).1.1, ?_⟩
    have hD1 := ct.l3_one_le_dstar hσ
    have a1 := (hOm σ hσ).2
    have a2 := (ct.l3_Y_env hR h0 hh2 hσ).1.2
    have a3 := (ct.l3_Y_env hR h0 hh2 hσ).1.1
    calc ct.OmP σ * Y1 σ ≤ ct.Dstar σ ^ 2 * (d * ct.Dstar σ ^ 4) :=
          mul_le_mul a1 a2 a3 (by positivity)
      _ = d * ct.Dstar σ ^ 6 := by ring
      _ ≤ (d : ℝ) ^ 2 * ct.Dstar σ ^ 6 := mul_le_mul_of_nonneg_right hdd (by positivity)
  have hUY2 : ct.E (fun σ => ct.Dstar σ ^ 5 * (ct.OmP σ * Y2 σ)) ≤
      CU2 * (4 * (ct.qP h - ct.tP h) + thP d) := by
    rw [← hEY2]
    refine HU2 ct _ fun σ hσ => ⟨mul_nonneg (hOm σ hσ).1 (ct.l3_Y_env hR h0 hh2 hσ).2.1, ?_⟩
    have hD1 := ct.l3_one_le_dstar hσ
    have a1 := (hOm σ hσ).2
    have a2 := (ct.l3_Y_env hR h0 hh2 hσ).2.2
    have a3 := (ct.l3_Y_env hR h0 hh2 hσ).2.1
    calc ct.OmP σ * Y2 σ ≤ ct.Dstar σ ^ 2 * (d * ct.Dstar σ ^ 2) :=
          mul_le_mul a1 a2 a3 (by positivity)
      _ = d * ct.Dstar σ ^ 4 := by ring
      _ ≤ (d : ℝ) ^ 2 * ct.Dstar σ ^ 4 := mul_le_mul_of_nonneg_right hdd (by positivity)
  -- the claim for a branch `e`
  have main : ∀ e : Bool, ∑ i ∈ ct.N, ∑ j ∈ nbhd ct.G ct.S i,
      ct.E (fun σ => H σ * maskF (ct.Xb h e σ) (ct.XP h σ) ct.uvec j i ^ 2) ≤
      (8 * K * C₅ + 320 * K * (CU1 + CU2) + 8 * K + 1) * h⁻¹ ^ 2 *
          (ct.zeta h - ct.alphaE h + 1 / (d * h) * (ct.qP h - ct.tP h) + thP d) +
        (8 * K * C₅ + 320 * K * (CU1 + CU2) + 8 * K + 1) / Real.sqrt h := by
    intro e
    obtain ⟨c, l, hc0, hc1, hl, hHc, hHW⟩ := ct.l3_H_cases h H hH
    have hW5e : ∀ k ∈ ct.S, ct.E (fun σ => ct.Dstar σ ^ 8 * (ct.Xb h e σ * ct.Xb h e σ) k k) ≤
        C₅ / Real.sqrt h := fun k hk => by
      cases e
      · exact (HW5 ct k hk).2
      · exact (HW5 ct k hk).1
    set Ed : ct.V → ℝ := fun i => ct.E (fun σ => ct.wtH h e i l σ *
      (ct.l3_kerL h e true i σ).trace) with hEd
    set Ec : ct.V → ℝ := fun i => ct.E (fun σ => ct.wtH h e i l σ *
      (ct.l3_kerL h e false i σ).trace) with hEc
    -- step 1: FS2 pointwise, then WT2
    have hstep : ∀ i ∈ ct.N, ∑ j ∈ nbhd ct.G ct.S i,
        ct.E (fun σ => H σ * maskF (ct.Xb h e σ) (ct.XP h σ) ct.uvec j i ^ 2) ≤
        2 * aOf d p ^ 2 * c * (K * Ed i + K * Ec i +
          2 * (K / (d : ℝ) ^ 2 + K * Real.exp (-(p : ℝ)))) := by
      intro i hi
      have e1 : ∑ j ∈ nbhd ct.G ct.S i,
          ct.E (fun σ => H σ * maskF (ct.Xb h e σ) (ct.XP h σ) ct.uvec j i ^ 2) =
          ct.E (fun σ => c * ct.diagW h l σ *
            ∑ j ∈ nbhd ct.G ct.S i, maskF (ct.Xb h e σ) (ct.XP h σ) ct.uvec j i ^ 2) := by
        rw [← ct.l3_E_sum]
        exact ct.l3_E_congr fun σ _ => by rw [hHc σ, Finset.mul_sum]
      rw [e1]
      have hWd := HWT ct i hi e true l hl
      have hWc := HWT ct i hi e false l hl
      calc ct.E (fun σ => c * ct.diagW h l σ *
            ∑ j ∈ nbhd ct.G ct.S i, maskF (ct.Xb h e σ) (ct.XP h σ) ct.uvec j i ^ 2)
          ≤ ct.E (fun σ => 2 * aOf d p ^ 2 * c *
            (ct.wtH h e i l σ * qForm (ct.l3_kerL h e true i σ) (rootSigns ct.G σ ct.S i) +
              ct.wtH h e i l σ * qForm (ct.l3_kerL h e false i σ) (rootSigns ct.G σ ct.S i))) :=
            ct.l3_E_mono fun σ hσ => ct.l3_fs1_pt h0.le e hσ hi hc0 l (hHW σ hσ).1
        _ = 2 * aOf d p ^ 2 * c *
            (ct.E (fun σ => ct.wtH h e i l σ *
              qForm (ct.l3_kerL h e true i σ) (rootSigns ct.G σ ct.S i)) +
            ct.E (fun σ => ct.wtH h e i l σ *
              qForm (ct.l3_kerL h e false i σ) (rootSigns ct.G σ ct.S i))) := by
            rw [ct.l3_E_const_mul, ct.l3_E_add]
        _ ≤ 2 * aOf d p ^ 2 * c *
            ((K * Ed i + K / (d : ℝ) ^ 2 + K * Real.exp (-(p : ℝ))) +
              (K * Ec i + K / (d : ℝ) ^ 2 + K * Real.exp (-(p : ℝ)))) :=
            mul_le_mul_of_nonneg_left (add_le_add hWd hWc) (by positivity)
        _ = _ := by ring
    -- step 2: the direct part
    have hdir : ∀ i ∈ ct.N, Ed i ≤ 4 * C₅ / Real.sqrt h := fun i hi =>
      ct.l3_fs1_dir hR h0 hh2 e l (fun σ hσ => ⟨(hHW σ hσ).1, (hHW σ hσ).2.1⟩) hW5e hi
    -- step 3: the cavity part
    have hcav : 2 * aOf d p ^ 2 * c * ∑ i ∈ ct.N, Ec i ≤
        80 * h⁻¹ ^ 2 * (ct.E (fun σ => ct.Dstar σ ^ 4 * (ct.OmP σ * Y1 σ)) +
          aOf d p ^ 2 * h⁻¹ * ct.E (fun σ => ct.Dstar σ ^ 5 * (ct.OmP σ * Y2 σ))) := by
      have e1 : 2 * aOf d p ^ 2 * c * ∑ i ∈ ct.N, Ec i = ct.E (fun σ => 2 * c * ct.diagW h l σ *
          (aOf d p ^ 2 * ∑ i ∈ ct.N, ct.Xb h e σ i i ^ 2 * ct.XP h σ i i ^ 2 *
            ((ct.tCav h e i σ)ᵀ * ct.tCav h e i σ).trace)) := by
        rw [hEc, ← ct.l3_E_sum, ← ct.l3_E_const_mul]
        refine ct.l3_E_congr fun σ _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        unfold Contact.wtH Contact.l3_kerL
        rw [show ct.tMap h e false i σ = ct.tCav h e i σ from rfl]
        ring
      rw [e1]
      calc ct.E (fun σ => 2 * c * ct.diagW h l σ *
            (aOf d p ^ 2 * ∑ i ∈ ct.N, ct.Xb h e σ i i ^ 2 * ct.XP h σ i i ^ 2 *
              ((ct.tCav h e i σ)ᵀ * ct.tCav h e i σ).trace))
          ≤ ct.E (fun σ => 80 * h⁻¹ ^ 2 * (ct.Dstar σ ^ 4 * (ct.OmP σ * Y1 σ) +
              aOf d p ^ 2 * h⁻¹ * (ct.Dstar σ ^ 5 * (ct.OmP σ * Y2 σ)))) :=
            ct.l3_E_mono fun σ hσ => by
              have hcv := ct.l3_fs1_cav hR h0 hh2 e hσ
              obtain ⟨hW0, -, hH5⟩ := hHW σ hσ
              have hHle : c * ct.diagW h l σ ≤ 5 * ct.Dstar σ ^ 2 * ct.OmP σ := by
                rw [← hHc σ]; exact hH5 (HΩ ct hD8v σ hσ)
              have hD1 := ct.l3_one_le_dstar hσ
              have hY1e := (ct.l3_Y_env hR h0 hh2 hσ).1.1
              have hY2e := (ct.l3_Y_env hR h0 hh2 hσ).2.1
              have hR0 : 0 ≤ 8 * ct.Dstar σ ^ 2 * h⁻¹ ^ 2 * (Y1 σ +
                  aOf d p ^ 2 * (ct.Dstar σ / h) * Y2 σ) := by positivity
              have hcW : 0 ≤ c * ct.diagW h l σ := mul_nonneg hc0 hW0
              calc 2 * c * ct.diagW h l σ * (aOf d p ^ 2 * ∑ i ∈ ct.N, ct.Xb h e σ i i ^ 2 *
                    ct.XP h σ i i ^ 2 * ((ct.tCav h e i σ)ᵀ * ct.tCav h e i σ).trace)
                  ≤ 2 * (c * ct.diagW h l σ) * (8 * ct.Dstar σ ^ 2 * h⁻¹ ^ 2 * (Y1 σ +
                    aOf d p ^ 2 * (ct.Dstar σ / h) * Y2 σ)) := by
                    rw [mul_assoc 2 c]
                    exact mul_le_mul_of_nonneg_left hcv (by positivity)
                _ ≤ 2 * (5 * ct.Dstar σ ^ 2 * ct.OmP σ) * (8 * ct.Dstar σ ^ 2 * h⁻¹ ^ 2 * (Y1 σ +
                    aOf d p ^ 2 * (ct.Dstar σ / h) * Y2 σ)) :=
                    mul_le_mul_of_nonneg_right (by linarith) hR0
                _ = _ := by rw [div_eq_mul_inv]; ring
        _ = 80 * h⁻¹ ^ 2 * (ct.E (fun σ => ct.Dstar σ ^ 4 * (ct.OmP σ * Y1 σ)) +
              aOf d p ^ 2 * h⁻¹ * ct.E (fun σ => ct.Dstar σ ^ 5 * (ct.OmP σ * Y2 σ))) := by
            rw [ct.l3_E_const_mul, ct.l3_E_add, ct.l3_E_const_mul]
    -- step 4: sum and conclude
    have hNd : (ct.N.card : ℝ) ≤ d := ct.l3_card_nbhd ct.v
    have hsum := Finset.sum_le_sum hstep
    have hsplit : ∑ i ∈ ct.N, 2 * aOf d p ^ 2 * c * (K * Ed i + K * Ec i +
          2 * (K / (d : ℝ) ^ 2 + K * Real.exp (-(p : ℝ)))) =
        2 * aOf d p ^ 2 * c * K * ∑ i ∈ ct.N, Ed i + K * (2 * aOf d p ^ 2 * c * ∑ i ∈ ct.N, Ec i) +
          ct.N.card * (2 * aOf d p ^ 2 * c * (2 * (K / (d : ℝ) ^ 2 + K * Real.exp (-(p : ℝ))))) := by
      have e : ∀ i ∈ ct.N, 2 * aOf d p ^ 2 * c * (K * Ed i + K * Ec i +
          2 * (K / (d : ℝ) ^ 2 + K * Real.exp (-(p : ℝ)))) =
          2 * aOf d p ^ 2 * c * K * Ed i + K * (2 * aOf d p ^ 2 * c) * Ec i +
            2 * aOf d p ^ 2 * c * (2 * (K / (d : ℝ) ^ 2 + K * Real.exp (-(p : ℝ)))) :=
        fun i _ => by ring
      rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum, ← Finset.mul_sum]
      ring
    rw [hsplit] at hsum
    have hD : 2 * aOf d p ^ 2 * c * K * ∑ i ∈ ct.N, Ed i ≤ 8 * K * C₅ / Real.sqrt h := by
      have h1' : ∑ i ∈ ct.N, Ed i ≤ d * (4 * C₅ / Real.sqrt h) :=
        l3_sum_le_card _ hNd _ (by positivity) hdir
      have hEd0 : 0 ≤ ∑ i ∈ ct.N, Ed i := by
        refine Finset.sum_nonneg fun i _ => ct.l3_E_nonneg fun σ hσ => ?_
        have hw0 : 0 ≤ ct.wtH h e i l σ := by
          unfold Contact.wtH
          exact mul_nonneg (mul_nonneg (hHW σ hσ).1 (sq_nonneg _)) (sq_nonneg _)
        have htr := Matrix.posSemidef_conjTranspose_mul_self (ct.tMap h e true i σ)
        rw [conjTranspose_eq_transpose_of_trivial] at htr
        exact mul_nonneg hw0 htr.trace_nonneg
      calc 2 * aOf d p ^ 2 * c * K * ∑ i ∈ ct.N, Ed i
          ≤ 2 * aOf d p ^ 2 * 1 * K * (d * (4 * C₅ / Real.sqrt h)) :=
            mul_le_mul (by gcongr) h1' hEd0 (by positivity)
        _ = 8 * K * C₅ / Real.sqrt h * (d * aOf d p ^ 2) := by ring
        _ ≤ 8 * K * C₅ / Real.sqrt h * 1 := mul_le_mul_of_nonneg_left had (by positivity)
        _ = _ := by ring
    have hE : ct.N.card * (2 * aOf d p ^ 2 * c * (2 * (K / (d : ℝ) ^ 2 +
        K * Real.exp (-(p : ℝ))))) ≤ 8 * K * thP d := by
      have hK2 : K / (d : ℝ) ^ 2 = K * thP d := by unfold thP; ring
      rw [hK2]
      calc (ct.N.card : ℝ) * (2 * aOf d p ^ 2 * c * (2 * (K * thP d + K * Real.exp (-(p : ℝ)))))
          ≤ d * (2 * aOf d p ^ 2 * 1 * (2 * (K * thP d + K * thP d))) := by
            apply mul_le_mul hNd _ (by positivity) hd0.le
            gcongr
        _ = 8 * K * thP d * (d * aOf d p ^ 2) := by ring
        _ ≤ 8 * K * thP d * 1 := mul_le_mul_of_nonneg_left had (by positivity)
        _ = _ := by ring
    have hCc : K * (2 * aOf d p ^ 2 * c * ∑ i ∈ ct.N, Ec i) ≤
        K * (80 * h⁻¹ ^ 2 * (ct.E (fun σ => ct.Dstar σ ^ 4 * (ct.OmP σ * Y1 σ)) +
          aOf d p ^ 2 * h⁻¹ * ct.E (fun σ => ct.Dstar σ ^ 5 * (ct.OmP σ * Y2 σ)))) :=
      mul_le_mul_of_nonneg_left hcav hK.le
    exact l3_fs1_real hK hC₅ hCU1 hCU2 hsqh hhinv hZA hQT (by positivity) hβ1 hθ0
      (by positivity) hβ hsum hD hE hCc hUY1 hUY2
  rcases hXe with rfl | rfl
  · exact main true
  · exact main false

/-! ### FS4 and the score Cauchy–Schwarz -/

/-- **FS4** (source (FS4), l.1743–1751; AUDIT-D §3.4 FS4). Root-weight derivatives, pointwise on
the support, for `i ∈ N`, `j ∼ i`: `(∂_ij Ω_±)² ≤ Ω_± · 4 a² D_*² (x_i² + z_i²)`, from
`(G_vj)² ≤ G_vv G_jj` (no inverse source). -/
theorem fs4_root (ct : Contact.{u} d p) {σ : Config ct.V}
    (hσ : wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0) {i j : ct.V} (hi : i ∈ ct.N)
    (hj : j ∈ nbhd ct.G ct.S i) :
    ct.dOmP σ i j ^ 2 ≤ ct.OmP σ * (4 * aOf d p ^ 2 * ct.Dstar σ ^ 2 *
      (ct.x σ i ^ 2 + ct.z σ i ^ 2)) ∧
    ct.dOmM σ i j ^ 2 ≤ ct.OmM σ * (4 * aOf d p ^ 2 * ct.Dstar σ ^ 2 *
      (ct.x σ i ^ 2 + ct.z σ i ^ 2)) := by
  obtain ⟨hpP, hpM⟩ := SecB.posDef_of_wt_ne_zero ct.G hσ
  have hyp : ∀ k, 0 ≤ ct.yp k := fun k => (ct.ctx.hyp k).1
  have hym : ∀ k, 0 ≤ ct.ym k := fun k => (ct.ctx.hym k).1
  show (-(aOf d p) * ct.gp σ ct.v ct.v * ct.gp σ ct.v i * ct.gp σ ct.v j) ^ 2 ≤
      (ct.gp σ ct.v ct.v / 2) ^ 2 * (4 * aOf d p ^ 2 * ct.Dstar σ ^ 2 *
        (ct.gp σ ct.v i ^ 2 + ct.gm σ ct.v i ^ 2)) ∧
    (aOf d p / 2 * (ct.gp σ ct.v ct.v * ct.gm σ ct.v i * ct.gm σ ct.v j -
        ct.gp σ ct.v i * ct.gp σ ct.v j * ct.gm σ ct.v ct.v)) ^ 2 ≤
      ct.gp σ ct.v ct.v * ct.gm σ ct.v ct.v / 4 * (4 * aOf d p ^ 2 * ct.Dstar σ ^ 2 *
        (ct.gp σ ct.v i ^ 2 + ct.gm σ ct.v i ^ 2))
  have hvB := ct.l3_mem_ball_v
  have hjB := ct.l3_mem_ball_nbhd hi hj
  have hD1 := ct.l3_one_le_dstar hσ
  set D := ct.Dstar σ
  set P := ct.gp σ ct.v ct.v
  set M := ct.gm σ ct.v ct.v
  set Pj := ct.gp σ j j
  set Mj := ct.gm σ j j
  have hP := ct.l3_diagB_le 0 σ true hvB
  have hM := ct.l3_diagB_le 0 σ false hvB
  have hPj := ct.l3_diagB_le 0 σ true hjB
  have hMj := ct.l3_diagB_le 0 σ false hjB
  have hP0 := ct.l3_diagB_nonneg 0 hσ true ct.v
  have hM0 := ct.l3_diagB_nonneg 0 hσ false ct.v
  have hPj0 := ct.l3_diagB_nonneg 0 hσ true j
  have hMj0 := ct.l3_diagB_nonneg 0 hσ false j
  change P ≤ D - 1 at hP
  change M ≤ D - 1 at hM
  change Pj ≤ D - 1 at hPj
  change Mj ≤ D - 1 at hMj
  change 0 ≤ P at hP0
  change 0 ≤ M at hM0
  change 0 ≤ Pj at hPj0
  change 0 ≤ Mj at hMj0
  have hxj : ct.gp σ ct.v j ^ 2 ≤ P * Pj := SecB.greenP_sq_le ct.G hpP hyp ct.v j
  have hzj : ct.gm σ ct.v j ^ 2 ≤ M * Mj := SecB.greenP_sq_le ct.G hpM hym ct.v j
  set xi := ct.gp σ ct.v i
  set zi := ct.gm σ ct.v i
  set xj := ct.gp σ ct.v j
  set zj := ct.gm σ ct.v j
  set a := aOf d p
  have hPPj : P * Pj ≤ D ^ 2 := by nlinarith
  have hPMj : P * Mj ≤ D ^ 2 := by nlinarith
  have hPjM : Pj * M ≤ D ^ 2 := by nlinarith
  have hxi0 := sq_nonneg xi
  have hzi0 := sq_nonneg zi
  have ha0 := sq_nonneg a
  constructor
  · have e1 : (-a * P * xi * xj) ^ 2 = a ^ 2 * P ^ 2 * xi ^ 2 * xj ^ 2 := by ring
    have e2 : (P / 2) ^ 2 * (4 * a ^ 2 * D ^ 2 * (xi ^ 2 + zi ^ 2)) =
        a ^ 2 * P ^ 2 * D ^ 2 * (xi ^ 2 + zi ^ 2) := by ring
    rw [e1, e2]
    have t1 : xj ^ 2 ≤ D ^ 2 := hxj.trans hPPj
    have t2 : 0 ≤ a ^ 2 * P ^ 2 * xi ^ 2 := by positivity
    have t3 : a ^ 2 * P ^ 2 * xi ^ 2 * xj ^ 2 ≤ a ^ 2 * P ^ 2 * xi ^ 2 * D ^ 2 :=
      mul_le_mul_of_nonneg_left t1 t2
    have t4 : 0 ≤ a ^ 2 * P ^ 2 * D ^ 2 * zi ^ 2 := by positivity
    nlinarith
  · have e1 : (a / 2 * (P * zi * zj - xi * xj * M)) ^ 2 =
        a ^ 2 / 4 * (P * zi * zj - xi * xj * M) ^ 2 := by ring
    have e2 : P * M / 4 * (4 * a ^ 2 * D ^ 2 * (xi ^ 2 + zi ^ 2)) =
        a ^ 2 * (P * M) * D ^ 2 * (xi ^ 2 + zi ^ 2) := by ring
    rw [e1, e2]
    have s1 : (P * zi * zj - xi * xj * M) ^ 2 ≤
        2 * (P ^ 2 * zi ^ 2 * zj ^ 2) + 2 * (xi ^ 2 * xj ^ 2 * M ^ 2) := by
      nlinarith [sq_nonneg (P * zi * zj + xi * xj * M)]
    have s2 : P ^ 2 * zi ^ 2 * zj ^ 2 ≤ P * M * (D ^ 2 * zi ^ 2) := by
      have : P ^ 2 * zi ^ 2 * zj ^ 2 ≤ P ^ 2 * zi ^ 2 * (M * Mj) :=
        mul_le_mul_of_nonneg_left hzj (by positivity)
      have h2 : P * Mj * (P * M * zi ^ 2) ≤ D ^ 2 * (P * M * zi ^ 2) :=
        mul_le_mul_of_nonneg_right hPMj (by positivity)
      nlinarith
    have s3 : xi ^ 2 * xj ^ 2 * M ^ 2 ≤ P * M * (D ^ 2 * xi ^ 2) := by
      have : xi ^ 2 * xj ^ 2 * M ^ 2 ≤ xi ^ 2 * (P * Pj) * M ^ 2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hxj (by positivity)) (by positivity)
      have h2 : Pj * M * (P * M * xi ^ 2) ≤ D ^ 2 * (P * M * xi ^ 2) :=
        mul_le_mul_of_nonneg_right hPjM (by positivity)
      nlinarith
    have hPM0 : 0 ≤ P * M := mul_nonneg hP0 hM0
    have t : a ^ 2 / 4 * (P * zi * zj - xi * xj * M) ^ 2 ≤
        a ^ 2 / 4 * (2 * (P * M * (D ^ 2 * zi ^ 2)) + 2 * (P * M * (D ^ 2 * xi ^ 2))) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have t2 : 0 ≤ a ^ 2 * (P * M) * D ^ 2 * (xi ^ 2 + zi ^ 2) := by positivity
    nlinarith

/-- Cauchy–Schwarz for the paired law: `E[fg] ≤ √(E f²) √(E g²)`. -/
theorem l3_E_cs (ct : Contact.{u} d p) (f g : Config ct.V → ℝ) :
    ct.E (fun σ => f σ * g σ) ≤
      Real.sqrt (ct.E (fun σ => f σ ^ 2)) * Real.sqrt (ct.E (fun σ => g σ ^ 2)) := by
  have h := wavg_mul_sq_le (w := fun σ => wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S)
    (fun σ => wt_nonneg ct.G σ) f g
  rw [← lawE_eq_wavg, ← lawE_eq_wavg, ← lawE_eq_wavg] at h
  have hf0 : 0 ≤ ct.E (fun σ => f σ ^ 2) := lawE_nonneg ct.G fun σ _ => sq_nonneg _
  calc ct.E (fun σ => f σ * g σ) ≤ |ct.E (fun σ => f σ * g σ)| := le_abs_self _
    _ = Real.sqrt (ct.E (fun σ => f σ * g σ) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (ct.E (fun σ => f σ ^ 2) * ct.E (fun σ => g σ ^ 2)) := Real.sqrt_le_sqrt h
    _ = _ := Real.sqrt_mul hf0 _

/-- Cauchy–Schwarz over a double index. -/
theorem l3_cs2 {V : Type*} (s : Finset V) (t : V → Finset V) (A B : V → V → ℝ) :
    ∑ i ∈ s, ∑ j ∈ t i, A i j * B i j ≤
      Real.sqrt (∑ i ∈ s, ∑ j ∈ t i, A i j ^ 2) * Real.sqrt (∑ i ∈ s, ∑ j ∈ t i, B i j ^ 2) := by
  calc ∑ i ∈ s, ∑ j ∈ t i, A i j * B i j
      ≤ ∑ i ∈ s, Real.sqrt (∑ j ∈ t i, A i j ^ 2) * Real.sqrt (∑ j ∈ t i, B i j ^ 2) :=
        Finset.sum_le_sum fun i _ => Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ ≤ Real.sqrt (∑ i ∈ s, Real.sqrt (∑ j ∈ t i, A i j ^ 2) ^ 2) *
        Real.sqrt (∑ i ∈ s, Real.sqrt (∑ j ∈ t i, B i j ^ 2) ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = _ := by
        rw [Finset.sum_congr rfl fun i _ => Real.sq_sqrt (Finset.sum_nonneg fun j _ =>
          sq_nonneg (A i j)), Finset.sum_congr rfl fun i _ => Real.sq_sqrt
          (Finset.sum_nonneg fun j _ => sq_nonneg (B i j))]

/-- The score bound by joint Cauchy–Schwarz (source l.1752–1756): if `H ≥ 0` and
`(∂_ij H)² ≤ H · G₂(i)` with `G₂ ≥ 0` on the support (FS4), then
`𝖲 ≤ a √(Σ E[H F²]) (2pa √(Σ_i u_i² Σ_j E[H Δ_ij²]) + √(Σ_i u_i² Σ_j E[G₂(i)]))`. -/
theorem l3_score_le (ct : Contact.{u} d p) (H : Config ct.V → ℝ)
    (dH : Config ct.V → ct.V → ct.V → ℝ) (Xe Xn : Config ct.V → Matrix ct.V ct.V ℝ)
    (f : Config ct.V → ct.V → ℝ) (G2 : Config ct.V → ct.V → ℝ)
    (hH : ∀ σ, wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 → 0 ≤ H σ)
    (hG2 : ∀ σ, wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 → ∀ i, 0 ≤ G2 σ i)
    (hdH : ∀ σ, wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 → ∀ i ∈ ct.N,
      ∀ j ∈ nbhd ct.G ct.S i, dH σ i j ^ 2 ≤ H σ * G2 σ i) :
    ct.score H dH Xe Xn f ≤ aOf d p *
      Real.sqrt (∑ i ∈ ct.N, ∑ j ∈ nbhd ct.G ct.S i,
        ct.E (fun σ => H σ * maskF (Xe σ) (Xn σ) (f σ) j i ^ 2)) *
      (2 * p * aOf d p * Real.sqrt (∑ i ∈ ct.N, ∑ j ∈ nbhd ct.G ct.S i, ct.uvec i ^ 2 *
          ct.E (fun σ => H σ * (ct.gp σ i j - ct.gm σ i j) ^ 2)) +
        Real.sqrt (∑ i ∈ ct.N, ∑ j ∈ nbhd ct.G ct.S i, ct.uvec i ^ 2 *
          ct.E (fun σ => G2 σ i))) := by
  have ha0 : 0 ≤ aOf d p := by unfold aOf; positivity
  have hu0 : ∀ i, 0 ≤ ct.uvec i := fun i => by unfold Contact.uvec; split_ifs <;> positivity
  set F := fun σ i j => maskF (Xe σ) (Xn σ) (f σ) j i with hFdef
  set Aij := fun i j => ct.E (fun σ => H σ * F σ i j ^ 2) with hA
  set Bij := fun i j => ct.E (fun σ => H σ * (ct.gp σ i j - ct.gm σ i j) ^ 2) with hB
  set Gi := fun i => ct.E (fun σ => G2 σ i) with hG
  have hA0 : ∀ i j, 0 ≤ Aij i j := fun i j =>
    ct.l3_E_nonneg fun σ hσ => mul_nonneg (hH σ hσ) (sq_nonneg _)
  have hB0 : ∀ i j, 0 ≤ Bij i j := fun i j =>
    ct.l3_E_nonneg fun σ hσ => mul_nonneg (hH σ hσ) (sq_nonneg _)
  have hG0 : ∀ i, 0 ≤ Gi i := fun i => ct.l3_E_nonneg fun σ hσ => hG2 σ hσ i
  -- the per-term bound
  have hterm : ∀ i ∈ ct.N, ∀ j ∈ nbhd ct.G ct.S i,
      ct.E (fun σ => |F σ i j| * (2 * p * aOf d p * H σ * |ct.gp σ i j - ct.gm σ i j| +
        |dH σ i j|)) ≤
      2 * p * aOf d p * (Real.sqrt (Aij i j) * Real.sqrt (Bij i j)) +
        Real.sqrt (Aij i j) * Real.sqrt (Gi i) := by
    intro i hi j hj
    have hpt : ∀ σ, wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 →
        |F σ i j| * (2 * p * aOf d p * H σ * |ct.gp σ i j - ct.gm σ i j| + |dH σ i j|) ≤
          2 * p * aOf d p * ((Real.sqrt (H σ) * |F σ i j|) *
            (Real.sqrt (H σ) * |ct.gp σ i j - ct.gm σ i j|)) +
          (Real.sqrt (H σ) * |F σ i j|) * Real.sqrt (G2 σ i) := by
      intro σ hσ
      have hHs : Real.sqrt (H σ) * Real.sqrt (H σ) = H σ := Real.mul_self_sqrt (hH σ hσ)
      have hdHs : |dH σ i j| ≤ Real.sqrt (H σ) * Real.sqrt (G2 σ i) := by
        rw [← Real.sqrt_mul (hH σ hσ), ← Real.sqrt_sq_eq_abs]
        exact Real.sqrt_le_sqrt (hdH σ hσ i hi j hj)
      have h1 : |F σ i j| * |dH σ i j| ≤
          |F σ i j| * (Real.sqrt (H σ) * Real.sqrt (G2 σ i)) :=
        mul_le_mul_of_nonneg_left hdHs (abs_nonneg _)
      have e1 : |F σ i j| * (2 * p * aOf d p * H σ * |ct.gp σ i j - ct.gm σ i j|) =
          2 * p * aOf d p * ((Real.sqrt (H σ) * |F σ i j|) *
            (Real.sqrt (H σ) * |ct.gp σ i j - ct.gm σ i j|)) := by
        linear_combination (-(2 * (p : ℝ) * aOf d p * |F σ i j| *
          |ct.gp σ i j - ct.gm σ i j|)) * hHs
      calc |F σ i j| * (2 * p * aOf d p * H σ * |ct.gp σ i j - ct.gm σ i j| + |dH σ i j|)
          = |F σ i j| * (2 * p * aOf d p * H σ * |ct.gp σ i j - ct.gm σ i j|) +
            |F σ i j| * |dH σ i j| := by ring
        _ ≤ _ := by rw [e1]; linarith
    have hsqH : ∀ σ, wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 → ∀ y : ℝ,
        (Real.sqrt (H σ) * |y|) ^ 2 = H σ * y ^ 2 := fun σ hσ y => by
      rw [mul_pow, Real.sq_sqrt (hH σ hσ), sq_abs]
    have c1 := l3_E_cs ct (fun σ => Real.sqrt (H σ) * |F σ i j|)
      (fun σ => Real.sqrt (H σ) * |ct.gp σ i j - ct.gm σ i j|)
    have c2 := l3_E_cs ct (fun σ => Real.sqrt (H σ) * |F σ i j|) (fun σ => Real.sqrt (G2 σ i))
    have eA : ct.E (fun σ => (Real.sqrt (H σ) * |F σ i j|) ^ 2) = Aij i j :=
      ct.l3_E_congr fun σ hσ => hsqH σ hσ _
    have eB : ct.E (fun σ => (Real.sqrt (H σ) * |ct.gp σ i j - ct.gm σ i j|) ^ 2) = Bij i j :=
      ct.l3_E_congr fun σ hσ => hsqH σ hσ _
    have eG : ct.E (fun σ => Real.sqrt (G2 σ i) ^ 2) = Gi i :=
      ct.l3_E_congr fun σ hσ => Real.sq_sqrt (hG2 σ hσ i)
    rw [eA, eB] at c1
    rw [eA, eG] at c2
    have hpa : 0 ≤ 2 * (p : ℝ) * aOf d p := by positivity
    calc ct.E (fun σ => |F σ i j| * (2 * p * aOf d p * H σ * |ct.gp σ i j - ct.gm σ i j| +
          |dH σ i j|))
        ≤ ct.E (fun σ => 2 * p * aOf d p * ((Real.sqrt (H σ) * |F σ i j|) *
            (Real.sqrt (H σ) * |ct.gp σ i j - ct.gm σ i j|)) +
          (Real.sqrt (H σ) * |F σ i j|) * Real.sqrt (G2 σ i)) := ct.l3_E_mono hpt
      _ = 2 * p * aOf d p * ct.E (fun σ => (Real.sqrt (H σ) * |F σ i j|) *
            (Real.sqrt (H σ) * |ct.gp σ i j - ct.gm σ i j|)) +
          ct.E (fun σ => (Real.sqrt (H σ) * |F σ i j|) * Real.sqrt (G2 σ i)) := by
          rw [ct.l3_E_add, ct.l3_E_const_mul]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left c1 hpa) c2
  -- sum and the joint Cauchy–Schwarz
  have hscore : ct.score H dH Xe Xn f = aOf d p * ∑ i ∈ ct.N, ∑ j ∈ nbhd ct.G ct.S i,
      ct.uvec i * ct.E (fun σ => |F σ i j| *
        (2 * p * aOf d p * H σ * |ct.gp σ i j - ct.gm σ i j| + |dH σ i j|)) := rfl
  rw [hscore, mul_assoc (aOf d p)]
  refine mul_le_mul_of_nonneg_left ?_ ha0
  have hcs1 := l3_cs2 ct.N (nbhd ct.G ct.S) (fun i j => Real.sqrt (Aij i j))
    (fun i j => ct.uvec i * Real.sqrt (Bij i j))
  have hcs2 := l3_cs2 ct.N (nbhd ct.G ct.S) (fun i j => Real.sqrt (Aij i j))
    (fun i j => ct.uvec i * Real.sqrt (Gi i))
  simp only [Real.sq_sqrt (hA0 _ _), mul_pow, Real.sq_sqrt (hB0 _ _), Real.sq_sqrt (hG0 _)]
    at hcs1 hcs2
  have hpa : 0 ≤ 2 * (p : ℝ) * aOf d p := by positivity
  calc ∑ i ∈ ct.N, ∑ j ∈ nbhd ct.G ct.S i, ct.uvec i * ct.E (fun σ => |F σ i j| *
        (2 * p * aOf d p * H σ * |ct.gp σ i j - ct.gm σ i j| + |dH σ i j|))
      ≤ ∑ i ∈ ct.N, ∑ j ∈ nbhd ct.G ct.S i,
          (2 * p * aOf d p * (Real.sqrt (Aij i j) * (ct.uvec i * Real.sqrt (Bij i j))) +
            Real.sqrt (Aij i j) * (ct.uvec i * Real.sqrt (Gi i))) :=
        Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => by
          have := mul_le_mul_of_nonneg_left (hterm i hi j hj) (hu0 i)
          refine this.trans (le_of_eq ?_)
          ring
    _ = 2 * p * aOf d p * ∑ i ∈ ct.N, ∑ j ∈ nbhd ct.G ct.S i,
          Real.sqrt (Aij i j) * (ct.uvec i * Real.sqrt (Bij i j)) +
        ∑ i ∈ ct.N, ∑ j ∈ nbhd ct.G ct.S i, Real.sqrt (Aij i j) * (ct.uvec i * Real.sqrt (Gi i)) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    _ ≤ 2 * p * aOf d p * (Real.sqrt (∑ i ∈ ct.N, ∑ j ∈ nbhd ct.G ct.S i, Aij i j) *
          Real.sqrt (∑ i ∈ ct.N, ∑ j ∈ nbhd ct.G ct.S i, ct.uvec i ^ 2 * Bij i j)) +
        Real.sqrt (∑ i ∈ ct.N, ∑ j ∈ nbhd ct.G ct.S i, Aij i j) *
          Real.sqrt (∑ i ∈ ct.N, ∑ j ∈ nbhd ct.G ct.S i, ct.uvec i ^ 2 * Gi i) :=
        add_le_add (mul_le_mul_of_nonneg_left hcs1 hpa) hcs2
    _ = _ := by ring

/-! ### FS5: assembly -/

theorem l3_sqrt_add_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  have h1 := Real.sq_sqrt hx
  have h2 := Real.sq_sqrt hy
  have h3 := mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)
  calc Real.sqrt (x + y) ≤ Real.sqrt ((Real.sqrt x + Real.sqrt y) ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith)
    _ = Real.sqrt x + Real.sqrt y := Real.sqrt_sq (by positivity)

theorem l3_h34 {h : ℝ} (hh : 0 < h) : h * Real.sqrt (1 / Real.sqrt h) = h ^ ((3 : ℝ) / 4) := by
  have e1 : 1 / Real.sqrt h = h ^ (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_neg hh.le, one_div]
  have e2 : Real.sqrt (h ^ (-(1 / 2 : ℝ))) = h ^ (-(1 / 4 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hh.le]; norm_num
  rw [e1, e2, ← Real.rpow_one_add' hh.le (by norm_num)]
  norm_num

/-- `√A ≤ √C₁ (h⁻¹ √Z + √(1/√h))` from `A ≤ C₁ h⁻² Z + C₁/√h` (any sign of `Z`). -/
theorem l3_sqrt_fs1 {A C₁ h Z : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C₁) (hh : 0 < h)
    (hAle : A ≤ C₁ * h⁻¹ ^ 2 * Z + C₁ / Real.sqrt h) :
    Real.sqrt A ≤ Real.sqrt C₁ * (h⁻¹ * Real.sqrt Z + Real.sqrt (1 / Real.sqrt h)) := by
  have hs : 0 < Real.sqrt h := Real.sqrt_pos.2 hh
  have hy : 0 ≤ C₁ / Real.sqrt h := by positivity
  have hsy : Real.sqrt (C₁ / Real.sqrt h) = Real.sqrt C₁ * Real.sqrt (1 / Real.sqrt h) := by
    rw [← Real.sqrt_mul hC, mul_one_div]
  rcases le_or_gt 0 Z with hZ | hZ
  · have hx : 0 ≤ C₁ * h⁻¹ ^ 2 * Z := by positivity
    have hsx : Real.sqrt (C₁ * h⁻¹ ^ 2 * Z) = Real.sqrt C₁ * (h⁻¹ * Real.sqrt Z) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_mul hC, Real.sqrt_sq (by positivity)]
      ring
    calc Real.sqrt A ≤ Real.sqrt (C₁ * h⁻¹ ^ 2 * Z + C₁ / Real.sqrt h) := Real.sqrt_le_sqrt hAle
      _ ≤ Real.sqrt (C₁ * h⁻¹ ^ 2 * Z) + Real.sqrt (C₁ / Real.sqrt h) := l3_sqrt_add_le hx hy
      _ = _ := by rw [hsx, hsy]; ring
  · have hx : C₁ * h⁻¹ ^ 2 * Z ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hZ.le
    rw [Real.sqrt_eq_zero'.2 hZ.le, mul_zero, zero_add, ← hsy]
    exact Real.sqrt_le_sqrt (by linarith)

/-- The closing real arithmetic of FS5: `a (2pa √B + √G) ≤ K₅ √(pδ̄)/√d` with
`K₅ = √(4 C_U (4 C_D + 1)) + √(4 C_U (2 C₂ + 1))`. -/
theorem l3_fs5_key {a p d B G δ θ CU CD C₂ : ℝ} (ha : 0 ≤ a) (ha2 : a ^ 2 ≤ 1 / d) (hp : 1 ≤ p)
    (hd : 0 < d) (hB0 : 0 ≤ B) (hB : B ≤ CU * (4 * d * CD * δ / p + θ)) (hG0 : 0 ≤ G)
    (hG : G ≤ 4 * CU * (2 * C₂ + 1) * δ) (hθ : 0 ≤ θ) (hθδ : p * θ ≤ d * δ) (hCU : 0 ≤ CU)
    (hCD : 0 ≤ CD) (hC₂ : 0 ≤ C₂) (hδ : 0 ≤ δ) :
    a * (2 * p * a * Real.sqrt B + Real.sqrt G) ≤
      (Real.sqrt (4 * CU * (4 * CD + 1)) + Real.sqrt (4 * CU * (2 * C₂ + 1))) *
        (Real.sqrt (p * δ) / Real.sqrt d) := by
  have hp0 : 0 < p := by linarith
  have hsd : Real.sqrt (p * δ) / Real.sqrt d = Real.sqrt (p * δ / d) :=
    (Real.sqrt_div' _ hd.le).symm
  rw [hsd]
  have hpd : 0 ≤ p * δ / d := by positivity
  have ha4 : a ^ 4 ≤ 1 / d ^ 2 := by
    have : a ^ 4 = (a ^ 2) ^ 2 := by ring
    rw [this, show (1 : ℝ) / d ^ 2 = (1 / d) ^ 2 by ring]
    exact pow_le_pow_left₀ (sq_nonneg a) ha2 2
  -- the determinant part
  have t1 : 2 * p * a ^ 2 * Real.sqrt B ≤
      Real.sqrt (4 * CU * (4 * CD + 1)) * Real.sqrt (p * δ / d) := by
    rw [← Real.sqrt_mul (by positivity)]
    have hx : 0 ≤ 2 * p * a ^ 2 * Real.sqrt B := by positivity
    rw [show 2 * p * a ^ 2 * Real.sqrt B = Real.sqrt ((2 * p * a ^ 2 * Real.sqrt B) ^ 2) from
      (Real.sqrt_sq hx).symm]
    apply Real.sqrt_le_sqrt
    have e : (2 * p * a ^ 2 * Real.sqrt B) ^ 2 = 4 * p ^ 2 * a ^ 4 * B := by
      rw [mul_pow, Real.sq_sqrt hB0]; ring
    rw [e]
    have s1 : 4 * p ^ 2 * a ^ 4 * B ≤ 4 * p ^ 2 * (1 / d ^ 2) * (CU * (4 * d * CD * δ / p + θ)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left ha4 (by positivity)) hB hB0 (by positivity)
    have s2 : 4 * p ^ 2 * (1 / d ^ 2) * (CU * (4 * d * CD * δ / p + θ)) =
        4 * CU * (4 * CD * (p * δ / d) + p * (p * θ) / d ^ 2) := by
      field_simp
    have s3 : p * (p * θ) / d ^ 2 ≤ p * δ / d := by
      rw [div_le_div_iff₀ (by positivity) hd]
      have := mul_le_mul_of_nonneg_left hθδ (by positivity : (0 : ℝ) ≤ p * d)
      nlinarith
    have s4 : 4 * CU * (4 * CD * (p * δ / d) + p * (p * θ) / d ^ 2) ≤
        4 * CU * (4 * CD + 1) * (p * δ / d) := by
      have := mul_le_mul_of_nonneg_left s3 (by positivity : (0 : ℝ) ≤ 4 * CU)
      nlinarith
    linarith
  -- the root-weight part
  have t2 : a * Real.sqrt G ≤ Real.sqrt (4 * CU * (2 * C₂ + 1)) * Real.sqrt (p * δ / d) := by
    rw [← Real.sqrt_mul (by positivity)]
    have hx : 0 ≤ a * Real.sqrt G := by positivity
    rw [show a * Real.sqrt G = Real.sqrt ((a * Real.sqrt G) ^ 2) from (Real.sqrt_sq hx).symm]
    apply Real.sqrt_le_sqrt
    rw [mul_pow, Real.sq_sqrt hG0]
    have s1 : a ^ 2 * G ≤ 1 / d * (4 * CU * (2 * C₂ + 1) * δ) :=
      mul_le_mul ha2 hG hG0 (by positivity)
    have s2 : 1 / d * (4 * CU * (2 * C₂ + 1) * δ) ≤ 4 * CU * (2 * C₂ + 1) * (p * δ / d) := by
      have h0 : 0 ≤ 4 * CU * (2 * C₂ + 1) * δ / d := by positivity
      have e1 : 1 / d * (4 * CU * (2 * C₂ + 1) * δ) = 4 * CU * (2 * C₂ + 1) * δ / d := by ring
      have e2 : 4 * CU * (2 * C₂ + 1) * (p * δ / d) = p * (4 * CU * (2 * C₂ + 1) * δ / d) := by
        ring
      rw [e1, e2]; nlinarith
    linarith
  calc a * (2 * p * a * Real.sqrt B + Real.sqrt G) =
      2 * p * a ^ 2 * Real.sqrt B + a * Real.sqrt G := by ring
    _ ≤ _ := by rw [add_mul]; exact add_le_add t1 t2

namespace Contact

variable (ct : Contact.{u} d p)

theorem l3_diag_ball {σ : Config ct.V} (hσ : wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0)
    {k : ct.V} (hk : k ∈ ct.l3_ball) :
    (0 ≤ ct.gp σ k k ∧ ct.gp σ k k ≤ ct.Dstar σ) ∧ (0 ≤ ct.gm σ k k ∧ ct.gm σ k k ≤ ct.Dstar σ) := by
  have a1 := ct.l3_diagB_le 0 σ true hk
  have a2 := ct.l3_diagB_le 0 σ false hk
  have b1 := ct.l3_diagB_nonneg 0 hσ true k
  have b2 := ct.l3_diagB_nonneg 0 hσ false k
  have e1 : ct.diagB 0 σ k true false = ct.gp σ k k := rfl
  have e2 : ct.diagB 0 σ k false false = ct.gm σ k k := rfl
  rw [e1] at a1 b1
  rw [e2] at a2 b2
  exact ⟨⟨b1, by linarith⟩, ⟨b2, by linarith⟩⟩

theorem l3_green_sq_ball {σ : Config ct.V} (hσ : wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0)
    {k l : ct.V} (hk : k ∈ ct.l3_ball) (hl : l ∈ ct.l3_ball) :
    ct.gp σ k l ^ 2 ≤ ct.Dstar σ ^ 2 ∧ ct.gm σ k l ^ 2 ≤ ct.Dstar σ ^ 2 := by
  obtain ⟨hpP, hpM⟩ := SecB.posDef_of_wt_ne_zero ct.G hσ
  have s1 : ct.gp σ k l ^ 2 ≤ ct.gp σ k k * ct.gp σ l l :=
    SecB.greenP_sq_le ct.G hpP (fun k => (ct.ctx.hyp k).1) k l
  have s2 : ct.gm σ k l ^ 2 ≤ ct.gm σ k k * ct.gm σ l l :=
    SecB.greenP_sq_le ct.G hpM (fun k => (ct.ctx.hym k).1) k l
  obtain ⟨⟨k1, k2⟩, ⟨k3, k4⟩⟩ := ct.l3_diag_ball hσ hk
  obtain ⟨⟨l1, l2⟩, ⟨l3, l4⟩⟩ := ct.l3_diag_ball hσ hl
  have hD0 : 0 ≤ ct.Dstar σ := by linarith [ct.l3_one_le_dstar hσ]
  have t1 := mul_le_mul k2 l2 l1 hD0
  have t2 := mul_le_mul k4 l4 l3 hD0
  constructor <;> nlinarith

/-- The root-weight majorant of FS4: `G₂(i) = 4 a² D_*² (x_i² + z_i²)`. -/
noncomputable def l3_G2 (σ : Config ct.V) (i : ct.V) : ℝ :=
  4 * aOf d p ^ 2 * ct.Dstar σ ^ 2 * (ct.x σ i ^ 2 + ct.z σ i ^ 2)

theorem l3_G2_nonneg (σ : Config ct.V) (i : ct.V) : 0 ≤ ct.l3_G2 σ i := by
  unfold l3_G2; positivity

/-- The determinant-score row mass (FS5, DR1 at every `i ∈ N` and UMI):
`Σ_{i∈N} Σ_{j∼i} u_i² E[H Δ_ij²] ≤ C_U (4 d C_D δ̄/p + θ)` for `0 ≤ H ≤ D_*²`. -/
theorem l3_fs5_B (hR : TRegime d p) {CU CD : ℝ} (hCU : 0 < CU) (hCD : 0 ≤ CD)
    (hU : ∀ Y : Config ct.V → ℝ, (∀ σ, wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 →
        0 ≤ Y σ ∧ Y σ ≤ (d : ℝ) ^ 2 * ct.Dstar σ ^ 2) →
      ct.E (fun σ => ct.Dstar σ ^ 2 * Y σ) ≤ CU * (ct.E Y + thP d))
    (hDR : ∀ w ∈ ct.S, aOf d p ^ 2 * ∑ j ∈ nbhd ct.G ct.S w,
      ct.E (fun σ => (ct.gp σ w j - ct.gm σ w j) ^ 2) ≤ CD * dbar d p / p)
    (Hw : Config ct.V → ℝ)
    (hHw : ∀ σ, wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 → 0 ≤ Hw σ ∧ Hw σ ≤ ct.Dstar σ ^ 2) :
    ∑ i ∈ ct.N, ∑ j ∈ nbhd ct.G ct.S i, ct.uvec i ^ 2 *
        ct.E (fun σ => Hw σ * (ct.gp σ i j - ct.gm σ i j) ^ 2) ≤
      CU * (4 * d * CD * dbar d p / p + thP d) := by
  have hd4 : (4 : ℝ) ≤ d := by have := hR.ten_pow_six_le_d; linarith
  have hd0 : (0 : ℝ) < d := by linarith
  have hp0 : (0 : ℝ) < p := SecB.regime_p_pos hR
  have ha' := hR.pf_a_sq_ge
  have hδ0 : 0 ≤ dbar d p := le_trans (by positivity) (SecB.le_dbar hR).2
  have hper : ∀ i ∈ ct.N, ∑ j ∈ nbhd ct.G ct.S i, ct.uvec i ^ 2 *
      ct.E (fun σ => Hw σ * (ct.gp σ i j - ct.gm σ i j) ^ 2) ≤
      1 / d * (CU * (4 * d * CD * dbar d p / p + thP d)) := by
    intro i hi
    have hiS : i ∈ ct.S := (Finset.mem_filter.1 hi).1
    have hiB := ct.l3_mem_ball_N hi
    rw [← Finset.mul_sum, ← ct.l3_E_sum]
    have hY : ∀ σ, wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 →
        0 ≤ ∑ j ∈ nbhd ct.G ct.S i, (ct.gp σ i j - ct.gm σ i j) ^ 2 ∧
        ∑ j ∈ nbhd ct.G ct.S i, (ct.gp σ i j - ct.gm σ i j) ^ 2 ≤
          (d : ℝ) ^ 2 * ct.Dstar σ ^ 2 := by
      intro σ hσ
      refine ⟨Finset.sum_nonneg fun j _ => sq_nonneg _, ?_⟩
      have hD0 : 0 ≤ ct.Dstar σ ^ 2 := sq_nonneg _
      have h1 : ∑ j ∈ nbhd ct.G ct.S i, (ct.gp σ i j - ct.gm σ i j) ^ 2 ≤
          d * (4 * ct.Dstar σ ^ 2) := by
        refine l3_sum_le_card _ (ct.l3_card_nbhd i) _ (by positivity) fun j hj => ?_
        obtain ⟨g1, g2⟩ := ct.l3_green_sq_ball hσ hiB (ct.l3_mem_ball_nbhd hi hj)
        nlinarith [sq_nonneg (ct.gp σ i j + ct.gm σ i j)]
      have h2 : (d : ℝ) * (4 * ct.Dstar σ ^ 2) ≤ (d : ℝ) ^ 2 * ct.Dstar σ ^ 2 := by
        have := mul_le_mul_of_nonneg_right hd4 (mul_nonneg hd0.le hD0)
        nlinarith
      linarith
    have hUi := hU _ hY
    have hEsum : ct.E (fun σ => ∑ j ∈ nbhd ct.G ct.S i, (ct.gp σ i j - ct.gm σ i j) ^ 2) ≤
        4 * d * CD * dbar d p / p := by
      rw [ct.l3_E_sum]
      have hdr := hDR i hiS
      have hs0 : 0 ≤ ∑ j ∈ nbhd ct.G ct.S i, ct.E (fun σ => (ct.gp σ i j - ct.gm σ i j) ^ 2) :=
        Finset.sum_nonneg fun j _ => ct.l3_E_nonneg fun σ _ => sq_nonneg _
      have h4 : 1 ≤ 4 * d * aOf d p ^ 2 := by
        have := mul_le_mul_of_nonneg_left ha' (by positivity : (0 : ℝ) ≤ 4 * d)
        rwa [show 4 * (d : ℝ) * (1 / (4 * d)) = 1 by field_simp] at this
      calc ∑ j ∈ nbhd ct.G ct.S i, ct.E (fun σ => (ct.gp σ i j - ct.gm σ i j) ^ 2)
          ≤ 4 * d * aOf d p ^ 2 *
              ∑ j ∈ nbhd ct.G ct.S i, ct.E (fun σ => (ct.gp σ i j - ct.gm σ i j) ^ 2) :=
            le_mul_of_one_le_left hs0 h4
        _ = 4 * d * (aOf d p ^ 2 *
              ∑ j ∈ nbhd ct.G ct.S i, ct.E (fun σ => (ct.gp σ i j - ct.gm σ i j) ^ 2)) := by ring
        _ ≤ 4 * d * (CD * dbar d p / p) := mul_le_mul_of_nonneg_left hdr (by positivity)
        _ = _ := by ring
    have hu2 := ct.l3_uvec_sq_le i
    have hE0 : 0 ≤ ct.E (fun σ => ∑ j ∈ nbhd ct.G ct.S i,
        Hw σ * (ct.gp σ i j - ct.gm σ i j) ^ 2) := ct.l3_E_nonneg fun σ hσ =>
      Finset.sum_nonneg fun j _ => mul_nonneg (hHw σ hσ).1 (sq_nonneg _)
    calc ct.uvec i ^ 2 * ct.E (fun σ => ∑ j ∈ nbhd ct.G ct.S i,
          Hw σ * (ct.gp σ i j - ct.gm σ i j) ^ 2)
        ≤ 1 / d * ct.E (fun σ => ct.Dstar σ ^ 2 *
            ∑ j ∈ nbhd ct.G ct.S i, (ct.gp σ i j - ct.gm σ i j) ^ 2) := by
          apply mul_le_mul hu2 _ hE0 (by positivity)
          refine ct.l3_E_mono fun σ hσ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_le_sum fun j _ =>
            mul_le_mul_of_nonneg_right (hHw σ hσ).2 (sq_nonneg _)
      _ ≤ 1 / d * (CU * (4 * d * CD * dbar d p / p + thP d)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact hUi.trans (mul_le_mul_of_nonneg_left (by linarith) hCU.le)
  calc ∑ i ∈ ct.N, ∑ j ∈ nbhd ct.G ct.S i, ct.uvec i ^ 2 *
        ct.E (fun σ => Hw σ * (ct.gp σ i j - ct.gm σ i j) ^ 2)
      ≤ d * (1 / d * (CU * (4 * d * CD * dbar d p / p + thP d))) := by
        have hθ0 : 0 ≤ thP d := by unfold thP; positivity
        have hX : 0 ≤ 4 * d * CD * dbar d p / p + thP d :=
          add_nonneg (div_nonneg (mul_nonneg (mul_nonneg (by positivity) hCD) hδ0) hp0.le) hθ0
        exact l3_sum_le_card _ (ct.l3_card_nbhd ct.v) _
          (mul_nonneg (by positivity) (mul_nonneg hCU.le hX)) hper
    _ = _ := by field_simp

/-- The root-weight mass (FS4 summed, (C2) at the root and UMI):
`Σ_{i∈N} Σ_{j∼i} u_i² E[G₂(i)] ≤ 4 C_U (2 C₂ + 1) δ̄`. -/
theorem l3_fs5_G (hR : TRegime d p) {CU C₂ : ℝ} (hCU : 0 < CU) (hC₂ : 0 < C₂)
    (hU : ∀ Y : Config ct.V → ℝ, (∀ σ, wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 →
        0 ≤ Y σ ∧ Y σ ≤ (d : ℝ) ^ 2 * ct.Dstar σ ^ 2) →
      ct.E (fun σ => ct.Dstar σ ^ 2 * Y σ) ≤ CU * (ct.E Y + thP d))
    (hC2a : aOf d p ^ 2 * ct.Srow ≤ C₂ * dbar d p)
    (hC2b : aOf d p ^ 2 * ct.Smin ≤ C₂ * dbar d p) :
    ∑ i ∈ ct.N, ∑ j ∈ nbhd ct.G ct.S i, ct.uvec i ^ 2 * ct.E (fun σ => ct.l3_G2 σ i) ≤
      4 * CU * (2 * C₂ + 1) * dbar d p := by
  have hd4 : (4 : ℝ) ≤ d := by have := hR.ten_pow_six_le_d; linarith
  have hd0 : (0 : ℝ) < d := by linarith
  have ha := hR.pf_a_sq_le
  have hδ := (SecB.le_dbar hR).2
  have hp1 : (1 : ℝ) ≤ p := by have := hR.two_le_p; exact_mod_cast (by omega : 1 ≤ p)
  have hθ1 : thP d ≤ dbar d p := by
    have h1 : thP d ≤ 1 / (d : ℝ) := by
      unfold thP; exact one_div_le_one_div_of_le hd0 (by nlinarith)
    have h2 : 1 / (d : ℝ) ≤ (p : ℝ) ^ 4 / d :=
      div_le_div_of_nonneg_right (one_le_pow₀ hp1) hd0.le
    linarith
  have hper : ∀ i ∈ ct.N, ∑ j ∈ nbhd ct.G ct.S i, ct.uvec i ^ 2 * ct.E (fun σ => ct.l3_G2 σ i) ≤
      ct.E (fun σ => ct.l3_G2 σ i) := by
    intro i _
    have hE0 : 0 ≤ ct.E (fun σ => ct.l3_G2 σ i) := ct.l3_E_nonneg fun σ _ => ct.l3_G2_nonneg σ i
    rw [Finset.sum_const, nsmul_eq_mul]
    calc ((nbhd ct.G ct.S i).card : ℝ) * (ct.uvec i ^ 2 * ct.E (fun σ => ct.l3_G2 σ i))
        ≤ d * (1 / d * ct.E (fun σ => ct.l3_G2 σ i)) :=
          mul_le_mul (ct.l3_card_nbhd i)
            (mul_le_mul_of_nonneg_right (ct.l3_uvec_sq_le i) hE0) (by positivity) hd0.le
      _ = _ := by field_simp
  have hY : ∀ σ, wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 →
      0 ≤ ∑ i ∈ ct.N, (ct.x σ i ^ 2 + ct.z σ i ^ 2) ∧
      ∑ i ∈ ct.N, (ct.x σ i ^ 2 + ct.z σ i ^ 2) ≤ (d : ℝ) ^ 2 * ct.Dstar σ ^ 2 := by
    intro σ hσ
    refine ⟨Finset.sum_nonneg fun i _ => add_nonneg (sq_nonneg _) (sq_nonneg _), ?_⟩
    have hD0 : 0 ≤ ct.Dstar σ ^ 2 := sq_nonneg _
    have h1 : ∑ i ∈ ct.N, (ct.x σ i ^ 2 + ct.z σ i ^ 2) ≤ d * (2 * ct.Dstar σ ^ 2) := by
      refine l3_sum_le_card _ (ct.l3_card_nbhd ct.v) _ (by positivity) fun i hi => ?_
      obtain ⟨g1, g2⟩ := ct.l3_green_sq_ball hσ ct.l3_mem_ball_v (ct.l3_mem_ball_N hi)
      have e1 : ct.x σ i = ct.gp σ ct.v i := rfl
      have e2 : ct.z σ i = ct.gm σ ct.v i := rfl
      rw [e1, e2]; linarith
    have h2 : (d : ℝ) * (2 * ct.Dstar σ ^ 2) ≤ (d : ℝ) ^ 2 * ct.Dstar σ ^ 2 := by
      have := mul_le_mul_of_nonneg_right hd4 (mul_nonneg hd0.le hD0)
      nlinarith
    linarith
  have hU2 := hU _ hY
  have hEs : ct.E (fun σ => ∑ i ∈ ct.N, (ct.x σ i ^ 2 + ct.z σ i ^ 2)) = ct.Srow + ct.Smin := by
    rw [ct.l3_E_sum]
    simp only [ct.l3_E_add, Finset.sum_add_distrib]
    rfl
  have ha1 : aOf d p ^ 2 ≤ 1 := ha.trans (by rw [div_le_one hd0]; linarith)
  have hθ0 : 0 ≤ thP d := by unfold thP; positivity
  calc ∑ i ∈ ct.N, ∑ j ∈ nbhd ct.G ct.S i, ct.uvec i ^ 2 * ct.E (fun σ => ct.l3_G2 σ i)
      ≤ ∑ i ∈ ct.N, ct.E (fun σ => ct.l3_G2 σ i) := Finset.sum_le_sum hper
    _ = 4 * aOf d p ^ 2 * ct.E (fun σ => ct.Dstar σ ^ 2 *
          ∑ i ∈ ct.N, (ct.x σ i ^ 2 + ct.z σ i ^ 2)) := by
        rw [← ct.l3_E_sum, ← ct.l3_E_const_mul]
        refine ct.l3_E_congr fun σ _ => ?_
        simp only [l3_G2, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ ≤ 4 * aOf d p ^ 2 * (CU * (ct.Srow + ct.Smin + thP d)) := by
        rw [← hEs]; exact mul_le_mul_of_nonneg_left hU2 (by positivity)
    _ = 4 * CU * (aOf d p ^ 2 * ct.Srow + aOf d p ^ 2 * ct.Smin + aOf d p ^ 2 * thP d) := by
        ring
    _ ≤ 4 * CU * (C₂ * dbar d p + C₂ * dbar d p + dbar d p) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have : aOf d p ^ 2 * thP d ≤ dbar d p := by
          have := mul_le_mul ha1 hθ1 hθ0 zero_le_one
          linarith
        linarith
    _ = _ := by ring

end Contact

/-- The closing real arithmetic of FS5 for the `u`-scores. -/
theorem l3_fs5_finU {a p h C₁ K₅ R C e A Bv Gv sc Z : ℝ} (h0 : 0 < h) (hC₁ : 0 < C₁)
    (hK₅ : 0 ≤ K₅) (hR0 : 0 ≤ R) (he : e = R * h⁻¹) (hC : K₅ * Real.sqrt C₁ ≤ C)
    (hsc : sc ≤ a * Real.sqrt A * (2 * p * a * Real.sqrt Bv + Real.sqrt Gv))
    (hk : a * (2 * p * a * Real.sqrt Bv + Real.sqrt Gv) ≤ K₅ * R) (hA0 : 0 ≤ A)
    (hA : A ≤ C₁ * h⁻¹ ^ 2 * Z + C₁ / Real.sqrt h) :
    sc ≤ C * e * Real.sqrt Z + C * e * h ^ ((3 : ℝ) / 4) := by
  have hsA := l3_sqrt_fs1 hA0 hC₁.le h0 hA
  have hsZ := Real.sqrt_nonneg Z
  have hs1 := Real.sqrt_nonneg (1 / Real.sqrt h)
  have hh34 := l3_h34 h0
  have hhi : 0 ≤ h⁻¹ := inv_nonneg.2 h0.le
  have he0 : 0 ≤ e := by rw [he]; positivity
  have h34 : 0 ≤ h ^ ((3 : ℝ) / 4) := Real.rpow_nonneg h0.le _
  calc sc ≤ a * Real.sqrt A * (2 * p * a * Real.sqrt Bv + Real.sqrt Gv) := hsc
    _ = Real.sqrt A * (a * (2 * p * a * Real.sqrt Bv + Real.sqrt Gv)) := by ring
    _ ≤ (Real.sqrt C₁ * (h⁻¹ * Real.sqrt Z + Real.sqrt (1 / Real.sqrt h))) * (K₅ * R) :=
        (mul_le_mul_of_nonneg_left hk (Real.sqrt_nonneg _)).trans
          (mul_le_mul_of_nonneg_right hsA (by positivity))
    _ = K₅ * Real.sqrt C₁ * (R * h⁻¹) * Real.sqrt Z +
          K₅ * Real.sqrt C₁ * (R * h⁻¹) * (h * Real.sqrt (1 / Real.sqrt h)) := by
        field_simp
    _ = K₅ * Real.sqrt C₁ * e * Real.sqrt Z + K₅ * Real.sqrt C₁ * e * h ^ ((3 : ℝ) / 4) := by
        rw [← he, hh34]
    _ ≤ C * e * Real.sqrt Z + C * e * h ^ ((3 : ℝ) / 4) := by
        have t1 := mul_le_mul_of_nonneg_right hC (mul_nonneg he0 hsZ)
        have t2 := mul_le_mul_of_nonneg_right hC (mul_nonneg he0 h34)
        nlinarith

/-- The closing real arithmetic of FS5 for the `b`-scores. -/
theorem l3_fs5_finB {a p h CB K₅ R C e A Bv Gv sc z : ℝ} (h0 : 0 < h) (hCB : 0 < CB)
    (hK₅ : 0 ≤ K₅) (hR0 : 0 ≤ R) (he : e = R * h⁻¹) (hC : K₅ * Real.sqrt CB ≤ C)
    (hsc : sc ≤ a * Real.sqrt A * (2 * p * a * Real.sqrt Bv + Real.sqrt Gv))
    (hk : a * (2 * p * a * Real.sqrt Bv + Real.sqrt Gv) ≤ K₅ * R)
    (hA : A ≤ CB * h⁻¹ ^ 2 * z) :
    sc ≤ C * e * Real.sqrt z := by
  have hsA : Real.sqrt A ≤ Real.sqrt CB * h⁻¹ * Real.sqrt z := by
    calc Real.sqrt A ≤ Real.sqrt (CB * h⁻¹ ^ 2 * z) := Real.sqrt_le_sqrt hA
      _ = _ := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_mul hCB.le,
          Real.sqrt_sq (inv_nonneg.2 h0.le)]
  have he0 : 0 ≤ e := by rw [he]; positivity
  have hsz := Real.sqrt_nonneg z
  calc sc ≤ a * Real.sqrt A * (2 * p * a * Real.sqrt Bv + Real.sqrt Gv) := hsc
    _ = Real.sqrt A * (a * (2 * p * a * Real.sqrt Bv + Real.sqrt Gv)) := by ring
    _ ≤ (Real.sqrt CB * h⁻¹ * Real.sqrt z) * (K₅ * R) :=
        (mul_le_mul_of_nonneg_left hk (Real.sqrt_nonneg _)).trans
          (mul_le_mul_of_nonneg_right hsA (by positivity))
    _ = K₅ * Real.sqrt CB * e * Real.sqrt z := by rw [he]; ring
    _ ≤ C * e * Real.sqrt z :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC he0) hsz

/-- **FS5 from FS1, BM4, DR1 and C2** (the parent check of `fs5_scores`). Children: FS1
(`fs1_fixed_mask`), BM4 at `m = 0` (`bm4_mask 0`), DR1 at every `i ∈ N` (`in_DR1`), (C2) at the root
(`in_C2`), FS4 (`fs4_root`), the joint Cauchy–Schwarz (`l3_score_le`) and UMI (`l3_umi 2 2`). -/
theorem l3_fs5_of {C₁ : ℝ} (hC₁ : 0 < C₁) (hFS1 : Eventually fun _c₀ _κ₀ d p h =>
      ∀ ct : Contact.{u} d p, ∀ Xe : Config ct.V → Matrix ct.V ct.V ℝ,
      (Xe = ct.XP h ∨ Xe = ct.XM h) → ∀ H : Config ct.V → ℝ,
      (H = (fun _ => 1) ∨ H = ct.OmP ∨ H = ct.OmM) →
      ∑ i ∈ ct.N, ∑ j ∈ nbhd ct.G ct.S i,
          ct.E (fun σ => H σ * maskF (Xe σ) (ct.XP h σ) ct.uvec j i ^ 2) ≤
        C₁ * h⁻¹ ^ 2 * (ct.zeta h - ct.alphaE h + 1 / (d * h) * (ct.qP h - ct.tP h) + thP d) +
          C₁ / Real.sqrt h)
    {CB : ℝ} (hCB : 0 < CB) (hBM4 : Eventually fun _c₀ _κ₀ d p h =>
      ∀ ct : Contact.{u} d p,
      ∑ i ∈ ct.N, ∑ j ∈ ct.S, ct.E (fun σ => ct.Dstar σ ^ 0 * ct.OmP σ *
          maskF (ct.XP h σ) (ct.XP h σ) (ct.bP h σ) j i ^ 2) ≤
        CB * h⁻¹ ^ 2 * (ct.zP h + thP d) ∧
      ∑ i ∈ ct.N, ∑ j ∈ ct.S, ct.E (fun σ => ct.Dstar σ ^ 0 * ct.OmM σ *
          maskF (ct.XM h σ) (ct.XP h σ) (ct.bM h σ) j i ^ 2) ≤
        CB * h⁻¹ ^ 2 * (ct.zM h + thP d))
    {CD : ℝ} (hCD : 0 < CD) (hDR1 : Eventually fun _c₀ _κ₀ d p _h =>
      ∀ ct : Contact.{u} d p, ∀ w ∈ ct.S,
        aOf d p ^ 2 * ∑ j ∈ nbhd ct.G ct.S w,
          ct.E (fun σ => (ct.gp σ w j - ct.gm σ w j) ^ 2) ≤ CD * dbar d p / p)
    {C₂ : ℝ} (hC₂ : 0 < C₂) (hC2 : Eventually fun _c₀ _κ₀ d p _h =>
      ∀ ct : Contact.{u} d p,
        aOf d p ^ 2 * ct.Srow ≤ C₂ * dbar d p ∧ aOf d p ^ 2 * ct.Smin ≤ C₂ * dbar d p ∧
          ct.trA2 ≤ C₂ * dbar d p ∧ ct.trB2 ≤ C₂ * dbar d p) :
    ∃ C : ℝ, 0 < C ∧ Eventually fun _c₀ _κ₀ d p h =>
    ∀ ct : Contact.{u} d p,
      ct.score ct.OmP ct.dOmP (ct.XP h) (ct.XP h) (fun _ => ct.uvec) ≤
          C * eP d p h * Real.sqrt (ct.zeta h - ct.alphaE h +
            1 / (d * h) * (ct.qP h - ct.tP h) + thP d) + C * eP d p h * h ^ ((3 : ℝ) / 4) ∧
      ct.score ct.OmP ct.dOmP (ct.XP h) (ct.XP h) (ct.bP h) ≤
          C * eP d p h * Real.sqrt (ct.zP h + thP d) ∧
      ct.score ct.OmM ct.dOmM (ct.XM h) (ct.XP h) (fun _ => ct.uvec) ≤
          C * eP d p h * Real.sqrt (ct.zeta h - ct.alphaE h +
            1 / (d * h) * (ct.qP h - ct.tP h) + thP d) + C * eP d p h * h ^ ((3 : ℝ) / 4) ∧
      ct.score ct.OmM ct.dOmM (ct.XM h) (ct.XP h) (ct.bM h) ≤
          C * eP d p h * Real.sqrt (ct.zM h + thP d) := by
  obtain ⟨CU, hCU, hU⟩ := l3_umi.{u} 2 2
  set K₅ := Real.sqrt (4 * CU * (4 * CD + 1)) + Real.sqrt (4 * CU * (2 * C₂ + 1)) with hK₅
  have hK₅0 : 0 ≤ K₅ := by positivity
  refine ⟨K₅ * (Real.sqrt C₁ + Real.sqrt CB) + 1, by positivity, ?_⟩
  refine ((((((hFS1.and hBM4).and hDR1).and hC2).and hU).and (SecB.eventually_base 4)).and
    SecB.eventually_h_facts).mono ?_
  rintro c₀ κ₀ d p h ⟨⟨⟨⟨⟨⟨HFS1, HBM4⟩, HDR1⟩, HC2⟩, HU⟩, ⟨-, hp4, -, -, -, -⟩⟩,
    hR, h0, hdh, h1, -⟩ ct
  -- parameters
  have hd4 : (4 : ℝ) ≤ d := by have := hR.ten_pow_six_le_d; linarith
  have hd0 : (0 : ℝ) < d := by linarith
  have hp1 : (1 : ℝ) ≤ p := by linarith
  have ha := hR.pf_a_sq_le
  have ha' := hR.pf_a_sq_ge
  have ha0 : 0 ≤ aOf d p := by unfold aOf; positivity
  have hδ := (SecB.le_dbar hR).2
  have hθ0 : 0 ≤ thP d := by unfold thP; positivity
  have hθ1 : thP d ≤ 1 / (d : ℝ) := by
    unfold thP; exact one_div_le_one_div_of_le hd0 (by nlinarith)
  have hp4d : 1 / (d : ℝ) ≤ (p : ℝ) ^ 4 / d :=
    div_le_div_of_nonneg_right (one_le_pow₀ hp1) hd0.le
  have hδ0 : 0 ≤ dbar d p := le_trans (by positivity) hδ
  have hθδ0 : thP d ≤ dbar d p := by linarith
  have hθδ : (p : ℝ) * thP d ≤ d * dbar d p := by
    have e1 : (d : ℝ) * ((p : ℝ) ^ 4 / d) = (p : ℝ) ^ 4 := by field_simp
    have e2 : (p : ℝ) * thP d ≤ p := by
      have : thP d ≤ 1 := hθ1.trans (by rw [div_le_one hd0]; linarith)
      nlinarith
    have e3 : (p : ℝ) ≤ (p : ℝ) ^ 4 := le_self_pow₀ hp1 (by norm_num)
    have e4 : (d : ℝ) * ((p : ℝ) ^ 4 / d) ≤ d * dbar d p := mul_le_mul_of_nonneg_left hδ hd0.le
    linarith
  have hsqh : 0 < Real.sqrt h := Real.sqrt_pos.2 h0
  have hD1 : ∀ σ, wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 → 1 ≤ ct.Dstar σ :=
    fun σ hσ => ct.l3_one_le_dstar hσ
  have hBb := fun Hw hHw => ct.l3_fs5_B hR hCU hCD.le (HU ct) (HDR1 ct) Hw hHw
  -- the root-weight part
  have hGb := ct.l3_fs5_G hR hCU hC₂ (HU ct) (HC2 ct).1 (HC2 ct).2.1
  -- the key factor `a (2pa √B + √G) ≤ K₅ √(pδ̄)/√d`
  have hkey : ∀ Hw : Config ct.V → ℝ,
      (∀ σ, wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 → 0 ≤ Hw σ ∧ Hw σ ≤ ct.Dstar σ ^ 2) →
      aOf d p * (2 * p * aOf d p * Real.sqrt (∑ i ∈ ct.N, ∑ j ∈ nbhd ct.G ct.S i,
          ct.uvec i ^ 2 * ct.E (fun σ => Hw σ * (ct.gp σ i j - ct.gm σ i j) ^ 2)) +
        Real.sqrt (∑ i ∈ ct.N, ∑ j ∈ nbhd ct.G ct.S i, ct.uvec i ^ 2 *
          ct.E (fun σ => ct.l3_G2 σ i))) ≤
      K₅ * (Real.sqrt (p * dbar d p) / Real.sqrt d) := fun Hw hHw =>
    l3_fs5_key ha0 ha hp1 hd0
      (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => mul_nonneg (sq_nonneg _)
        (ct.l3_E_nonneg fun σ hσ => mul_nonneg (hHw σ hσ).1 (sq_nonneg _)))
      (hBb Hw hHw)
      (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => mul_nonneg (sq_nonneg _)
        (ct.l3_E_nonneg fun σ _ => ct.l3_G2_nonneg σ i))
      hGb hθ0 hθδ hCU.le hCD.le hC₂.le hδ0
  -- the two weights
  have hOmP : ∀ σ, wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 →
      0 ≤ ct.OmP σ ∧ ct.OmP σ ≤ ct.Dstar σ ^ 2 := fun σ hσ => by
    obtain ⟨⟨a1, a2⟩, -⟩ := ct.l3_diag_ball hσ ct.l3_mem_ball_v
    have := hD1 σ hσ
    unfold Contact.OmP
    exact ⟨by positivity, by nlinarith⟩
  have hOmM : ∀ σ, wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 →
      0 ≤ ct.OmM σ ∧ ct.OmM σ ≤ ct.Dstar σ ^ 2 := fun σ hσ => by
    obtain ⟨⟨a1, a2⟩, ⟨a3, a4⟩⟩ := ct.l3_diag_ball hσ ct.l3_mem_ball_v
    have := hD1 σ hσ
    unfold Contact.OmM
    exact ⟨by positivity, by nlinarith [mul_le_mul a2 a4 a3 (by linarith)]⟩
  have hdP : ∀ σ, wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 → ∀ i ∈ ct.N,
      ∀ j ∈ nbhd ct.G ct.S i, ct.dOmP σ i j ^ 2 ≤ ct.OmP σ * ct.l3_G2 σ i :=
    fun σ hσ i hi j hj => (fs4_root ct hσ hi hj).1
  have hdM : ∀ σ, wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 → ∀ i ∈ ct.N,
      ∀ j ∈ nbhd ct.G ct.S i, ct.dOmM σ i j ^ 2 ≤ ct.OmM σ * ct.l3_G2 σ i :=
    fun σ hσ i hi j hj => (fs4_root ct hσ hi hj).2
  -- `e = R/h`
  set R := Real.sqrt (p * dbar d p) / Real.sqrt d with hRdef
  have hR0 : 0 ≤ R := by positivity
  have he : eP d p h = R * h⁻¹ := by rw [eP, hRdef, div_mul_eq_div_div, div_eq_mul_inv]
  have hC₁le : K₅ * Real.sqrt C₁ ≤ K₅ * (Real.sqrt C₁ + Real.sqrt CB) + 1 := by
    have := Real.sqrt_nonneg CB; nlinarith
  have hCBle : K₅ * Real.sqrt CB ≤ K₅ * (Real.sqrt C₁ + Real.sqrt CB) + 1 := by
    have := Real.sqrt_nonneg C₁; nlinarith
  set C := K₅ * (Real.sqrt C₁ + Real.sqrt CB) + 1 with hCdef
  -- the `u`-scores (FS1) and the `b`-scores (BM4 at `m = 0`)
  have hA0 : ∀ (Hw : Config ct.V → ℝ) (Xe : Config ct.V → Matrix ct.V ct.V ℝ)
      (b : Config ct.V → ct.V → ℝ),
      (∀ σ, wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 → 0 ≤ Hw σ ∧ Hw σ ≤ ct.Dstar σ ^ 2) →
      0 ≤ ∑ i ∈ ct.N, ∑ j ∈ nbhd ct.G ct.S i,
        ct.E (fun σ => Hw σ * maskF (Xe σ) (ct.XP h σ) (b σ) j i ^ 2) := fun Hw Xe b hHb =>
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      ct.l3_E_nonneg fun σ hσ => mul_nonneg (hHb σ hσ).1 (sq_nonneg _)
  have hBMsub : ∀ (Hw : Config ct.V → ℝ) (Xe : Config ct.V → Matrix ct.V ct.V ℝ)
      (b : Config ct.V → ct.V → ℝ),
      (∀ σ, wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 → 0 ≤ Hw σ ∧ Hw σ ≤ ct.Dstar σ ^ 2) →
      ∑ i ∈ ct.N, ∑ j ∈ nbhd ct.G ct.S i,
        ct.E (fun σ => Hw σ * maskF (Xe σ) (ct.XP h σ) (b σ) j i ^ 2) ≤
      ∑ i ∈ ct.N, ∑ j ∈ ct.S, ct.E (fun σ => ct.Dstar σ ^ 0 * Hw σ *
          maskF (Xe σ) (ct.XP h σ) (b σ) j i ^ 2) := fun Hw Xe b hHb => by
    refine Finset.sum_le_sum fun i _ => ?_
    refine le_trans (le_of_eq ?_) (Finset.sum_le_sum_of_subset_of_nonneg
      (show nbhd ct.G ct.S i ⊆ ct.S from Finset.filter_subset _ _)
      fun j _ _ => ct.l3_E_nonneg fun σ hσ => by
        rw [pow_zero, one_mul]; exact mul_nonneg (hHb σ hσ).1 (sq_nonneg _))
    exact Finset.sum_congr rfl fun j _ => ct.l3_E_congr fun σ _ => by rw [pow_zero, one_mul]
  obtain ⟨hB1, hB2⟩ := HBM4 ct
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact l3_fs5_finU h0 hC₁ hK₅0 hR0 he hC₁le
      (l3_score_le ct _ _ _ _ _ _ (fun σ hσ => (hOmP σ hσ).1) (fun σ _ => ct.l3_G2_nonneg σ) hdP)
      (hkey _ hOmP) (hA0 _ _ _ hOmP) (HFS1 ct _ (Or.inl rfl) _ (Or.inr (Or.inl rfl)))
  · exact l3_fs5_finB h0 hCB hK₅0 hR0 he hCBle
      (l3_score_le ct _ _ _ _ _ _ (fun σ hσ => (hOmP σ hσ).1) (fun σ _ => ct.l3_G2_nonneg σ) hdP)
      (hkey _ hOmP) ((hBMsub _ _ _ hOmP).trans hB1)
  · exact l3_fs5_finU h0 hC₁ hK₅0 hR0 he hC₁le
      (l3_score_le ct _ _ _ _ _ _ (fun σ hσ => (hOmM σ hσ).1) (fun σ _ => ct.l3_G2_nonneg σ) hdM)
      (hkey _ hOmM) (hA0 _ _ _ hOmM) (HFS1 ct _ (Or.inr rfl) _ (Or.inr (Or.inr rfl)))
  · exact l3_fs5_finB h0 hCB hK₅0 hR0 he hCBle
      (l3_score_le ct _ _ _ _ _ _ (fun σ hσ => (hOmM σ hσ).1) (fun σ _ => ct.l3_G2_nonneg σ) hdM)
      (hkey _ hOmM) ((hBMsub _ _ _ hOmM).trans hB2)

/-! ### The leaves -/

/-- **L-FS1** (source (FS1)–(FS3), l.1656–1737, using the Schur identity (FS2), the weighted
quadratic domination (WT2), the mean Ward bound (W5), (D8) and interpolation; AUDIT-D §3.4 FS1–FS2).
For `ε ∈ {+, -}`, `H ∈ {1, Ω₊, Ω₋}` and `U = X_ε D_u X₊`:
`Σ_{i∈N} Σ_{j∼i} E[H F_ji²] ≤ C h⁻² (ζ - α + β_h(q₊ - t₊) + θ) + C h^{-1/2}`. -/
theorem fs1_fixed_mask : ∃ C : ℝ, 0 < C ∧ Eventually fun _c₀ _κ₀ d p h =>
    ∀ ct : Contact.{u} d p, ∀ Xe : Config ct.V → Matrix ct.V ct.V ℝ,
      (Xe = ct.XP h ∨ Xe = ct.XM h) → ∀ H : Config ct.V → ℝ,
      (H = (fun _ => 1) ∨ H = ct.OmP ∨ H = ct.OmM) →
      ∑ i ∈ ct.N, ∑ j ∈ nbhd ct.G ct.S i,
          ct.E (fun σ => H σ * maskF (Xe σ) (ct.XP h σ) ct.uvec j i ^ 2) ≤
        C * h⁻¹ ^ 2 * (ct.zeta h - ct.alphaE h + 1 / (d * h) * (ct.qP h - ct.tP h) + thP d) +
          C / Real.sqrt h := by
  obtain ⟨C₈, -, hD8⟩ := d8_profile.{u}
  obtain ⟨K, hK, hWT⟩ := SecB.wt2.{u} 2 2
  obtain ⟨C₅, hC₅, hW5⟩ := in_W5.{u} 8
  exact l3_fs1_of_d8 hD8 hK hWT hC₅ hW5

/-- **L-FS5** (source (FS5), l.1739–1763, with (FS4), l.1743–1751; AUDIT-D §3.4 FS4–FS5;
AUDIT-B §3.3 FS5′). Joint-index Cauchy–Schwarz, the fixed-mask bound (FS1), the mask bound (BM4),
the root-weight derivative bound (FS4) and the row envelope at the neighbours (GR1 on the paper
route, DR1 on the GCI-free route) bound the four weak-loop scores:
`𝖲_u ≤ C e √(ζ - α + β_h(q₊ - t₊) + θ) + C e h^{3/4}` (for both `(ε, H) = (+, Ω₊), (-, Ω₋)`),
`𝖲_{b₊} ≤ C e √(z₊ + θ)`, `𝖲_{b₋} ≤ C e √(z₋ + θ)`, with `β_h = (dh)⁻¹`, `θ = d⁻²`. -/
theorem fs5_scores : ∃ C : ℝ, 0 < C ∧ Eventually fun _c₀ _κ₀ d p h =>
    ∀ ct : Contact.{u} d p,
      ct.score ct.OmP ct.dOmP (ct.XP h) (ct.XP h) (fun _ => ct.uvec) ≤
          C * eP d p h * Real.sqrt (ct.zeta h - ct.alphaE h +
            1 / (d * h) * (ct.qP h - ct.tP h) + thP d) + C * eP d p h * h ^ ((3 : ℝ) / 4) ∧
      ct.score ct.OmP ct.dOmP (ct.XP h) (ct.XP h) (ct.bP h) ≤
          C * eP d p h * Real.sqrt (ct.zP h + thP d) ∧
      ct.score ct.OmM ct.dOmM (ct.XM h) (ct.XP h) (fun _ => ct.uvec) ≤
          C * eP d p h * Real.sqrt (ct.zeta h - ct.alphaE h +
            1 / (d * h) * (ct.qP h - ct.tP h) + thP d) + C * eP d p h * h ^ ((3 : ℝ) / 4) ∧
      ct.score ct.OmM ct.dOmM (ct.XM h) (ct.XP h) (ct.bM h) ≤
          C * eP d p h * Real.sqrt (ct.zM h + thP d) := by
  obtain ⟨C₁, hC₁, hFS1⟩ := fs1_fixed_mask.{u}
  obtain ⟨CB, hCB, hBM4⟩ := bm4_mask.{u} 0
  obtain ⟨CD, hCD, hDR1⟩ := in_DR1.{u}
  obtain ⟨C₂, hC₂, hC2⟩ := in_C2.{u}
  exact l3_fs5_of hC₁ hFS1 hCB hBM4 hCD hDR1 hC₂ hC2

end BiluLinial.Tight
