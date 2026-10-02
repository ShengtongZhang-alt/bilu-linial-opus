/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecB.WTRetVan
public import BiluLinial.Tight.SecB.WTRetCnt
public import BiluLinial.Tight.SecB.WTRetPt
public import BiluLinial.Tight.SecB.LawE
public import BiluLinial.Tight.SecB.RouteDR1
public import BiluLinial.Tight.SecA.WAvg

/-!
# Second moments of the WT multiplier (helpers for TB.WT5l)

The truncation step of TB.WT5l needs `E X² ≤ poly(d)` for `X = H (q_L + tr L)`.

* `inv_diag_mul_le_one`: `f_j ((A + diag f)⁻¹)_jj ≤ 1` for `A ⪰ 0`, `f ≥ 0`.
* `coreShift_abs_le`: the physical shifted core inverse has entries `≤ 1/h` on `S - i`.
* `tMap_abs_le`, `trace_kerL_le`, `qForm_kerL_le`: `|T_jl| ≤ d/h²`, `tr L ≤ d⁴/h⁴`,
  `q_L(ξ) ≤ |N| tr L` (deterministic, on the core support).
* `diagB_le`: every physical inverse diagonal (shifted or not) is at most `3 h^b_k`.
* `hN_pow_moment`: `E (h^b_k)^{2n} ≤ 4^n` for every `k` (`k ∉ S`: `h_k = 1`).
* `lawE_prod_sq_le` (A-HOLD): `E (Π_{t ∈ L} U_t)² ≤ c^{2|L|}` from `E U_t^{2|L|} ≤ c^{2|L|}`.
* `X_sq_moment`: `E[(H (q_L + tr L))²] ≤ ((d+1) d⁴/h⁴)² 6^{2|L'|}`.
-/

@[expose] public section

namespace BiluLinial.Tight.SecB

open Matrix

universe u

section Generic

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `f_j ((A + diag f)⁻¹)_jj ≤ 1` for `A ⪰ 0`, `f ≥ 0`, `A + diag f ≻ 0`. -/
theorem inv_diag_mul_le_one {A : Matrix n n ℝ} (hA : A.PosSemidef) {f : n → ℝ}
    (hf : ∀ k, 0 ≤ f k) (hM : (A + diagonal f).PosDef) (j : n) :
    f j * (A + diagonal f)⁻¹ j j ≤ 1 := by
  set M := A + diagonal f with hMdef
  set w := M⁻¹ *ᵥ Pi.single j 1 with hw
  have hdet : IsUnit M.det := isUnit_iff_ne_zero.2 hM.det_pos.ne'
  have hMw : M *ᵥ w = Pi.single j 1 := by
    rw [hw, mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]
  have hwj : w j = M⁻¹ j j := by
    simp [hw, mulVec, dotProduct, Pi.single_apply]
  have hq : w ⬝ᵥ (M *ᵥ w) = w j := by
    rw [hMw]
    simp [dotProduct, Pi.single_apply]
  have hsplit : w ⬝ᵥ (M *ᵥ w) = w ⬝ᵥ (A *ᵥ w) + ∑ k, f k * w k ^ 2 := by
    rw [hMdef, add_mulVec, dotProduct_add]
    congr 1
    simp only [mulVec_diagonal, dotProduct]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hA0 : 0 ≤ w ⬝ᵥ (A *ᵥ w) := by
    have := hA.dotProduct_mulVec_nonneg w
    simp only [star_trivial] at this
    exact this
  have hfj : f j * w j ^ 2 ≤ ∑ k, f k * w k ^ 2 :=
    Finset.single_le_sum (f := fun k => f k * w k ^ 2)
      (fun k _ => mul_nonneg (hf k) (sq_nonneg _)) (Finset.mem_univ j)
  have hm : 0 < M⁻¹ j j := hM.inv.diag_pos
  rw [← hwj] at hm ⊢
  have h1 : f j * w j * w j ≤ 1 * w j := by nlinarith
  exact le_of_mul_le_mul_right h1 hm

/-- `E (Π_{t ∈ L} U_t)² ≤ c^{2|L|}` from `E U_t^{2|L|} ≤ c^{2|L|}` (generalized Hölder). -/
theorem wavg_prod_sq_le {Ω α : Type*} [Fintype Ω] {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω)
    (L : List α) (hL : 1 ≤ L.length) (U : α → Ω → ℝ) {c : ℝ} (hc : 0 < c)
    (hm : ∀ t ∈ L, wavg w (fun ω => U t ω ^ (2 * L.length)) ≤ c ^ (2 * L.length)) :
    wavg w (fun ω => (L.map fun t => U t ω).prod ^ 2) ≤ c ^ (2 * L.length) := by
  have h := SecA.wavg_prod_pow_le hw (fun a : Fin L.length => fun ω => |U L[a.1] ω|)
    (fun a ω => abs_nonneg _) (fun _ => 2) (2 * L.length)
    (by simp [Finset.sum_const, Finset.card_univ, mul_comm]) (by omega) (fun _ => c)
    (fun _ => hc) (fun a _ => by
      have := hm L[a.1] (List.getElem_mem _)
      refine le_trans (le_of_eq ?_) this
      congr 1
      funext ω
      exact (Even.pow_abs ⟨L.length, by ring⟩ _))
  have e1 : (fun ω => (L.map fun t => U t ω).prod ^ 2) =
      fun ω => ∏ a : Fin L.length, |U L[a.1] ω| ^ 2 := by
    funext ω
    rw [← Fin.prod_univ_fun_getElem L (fun t => U t ω), ← Finset.prod_pow]
    exact Finset.prod_congr rfl fun a _ => (sq_abs _).symm
  rw [e1]
  refine h.trans_eq ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, mul_comm]

end Generic

section Graph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem smul_srcDiag_eq (h : ℝ) (y : V → ℝ) (T : Finset V) :
    h • srcDiag y T = diagonal fun k => h * (if k ∈ T then y k else 0) := by
  ext u w
  by_cases huw : u = w
  · subst huw
    simp [srcDiag]
  · simp [srcDiag, diagonal_apply_ne _ huw]

/-- The physical shifted core inverse has diagonal `≤ 1/h` on `S - i`. -/
theorem coreShift_diag_le {a τ h : ℝ} (hh : 0 < h) {y : V → ℝ} (hy : ∀ k, 0 ≤ y k)
    {σ : Config V} {S : Finset V} {i : V} (hM : (precCore G a τ y σ S i).PosDef) {j : V}
    (hj : j ∈ S.erase i) : coreShift G a τ h y σ S i j j ≤ 1 / h := by
  have e := smul_srcDiag_eq h y (S.erase i)
  have hPD : (precCore G a τ y σ S i + diagonal fun k =>
      h * (if k ∈ S.erase i then y k else 0)).PosDef := by
    rw [← e]
    exact hM.add_posSemidef (posSemidef_smul_srcDiag hy _ hh.le)
  have h1 := inv_diag_mul_le_one hM.posSemidef (fun k => by
    split_ifs
    · exact mul_nonneg hh.le (hy k)
    · simp) hPD j
  simp only [hj, if_true] at h1
  unfold coreShift
  rw [e, mul_comm (Real.sqrt (y j)), mul_assoc, Real.mul_self_sqrt (hy j),
    le_div_iff₀ hh]
  linarith

/-- Entries of the physical shifted core inverse are at most `1/h` on `S - i`. -/
theorem coreShift_abs_le {a τ h : ℝ} (hh : 0 < h) {y : V → ℝ} (hy : ∀ k, 0 ≤ y k)
    {σ : Config V} {S : Finset V} {i : V} (hM : (precCore G a τ y σ S i).PosDef) {j l : V}
    (hj : j ∈ S.erase i) (hl : l ∈ S.erase i) : |coreShift G a τ h y σ S i j l| ≤ 1 / h := by
  have hQ : (precCore G a τ y σ S i + h • srcDiag y (S.erase i)).PosDef :=
    hM.add_posSemidef (posSemidef_smul_srcDiag hy _ hh.le)
  set X := (precCore G a τ y σ S i + h • srcDiag y (S.erase i))⁻¹ with hX
  have hXe := psd_entry_abs_le hQ.inv.posSemidef j l
  have hj' := coreShift_diag_le G hh hy hM hj
  have hl' := coreShift_diag_le G hh hy hM hl
  have hXj : 0 ≤ X j j := hQ.inv.diag_pos.le
  have hXl : 0 ≤ X l l := hQ.inv.diag_pos.le
  unfold coreShift at hj' hl' ⊢
  rw [← hX] at hj' hl' ⊢
  have ej : Real.sqrt (y j) * X j j * Real.sqrt (y j) =
      (Real.sqrt (y j) * Real.sqrt (X j j)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (hy j), Real.sq_sqrt hXj, mul_comm (Real.sqrt (y j)), mul_assoc,
      Real.mul_self_sqrt (hy j)]
    ring
  have el : Real.sqrt (y l) * X l l * Real.sqrt (y l) =
      (Real.sqrt (y l) * Real.sqrt (X l l)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (hy l), Real.sq_sqrt hXl, mul_comm (Real.sqrt (y l)), mul_assoc,
      Real.mul_self_sqrt (hy l)]
    ring
  rw [ej] at hj'
  rw [el] at hl'
  have hsj : Real.sqrt (y j) * Real.sqrt (X j j) ≤ Real.sqrt (1 / h) :=
    Real.le_sqrt_of_sq_le hj'
  have hsl : Real.sqrt (y l) * Real.sqrt (X l l) ≤ Real.sqrt (1 / h) :=
    Real.le_sqrt_of_sq_le hl'
  have h0 : 0 ≤ 1 / h := by positivity
  calc |Real.sqrt (y j) * X j l * Real.sqrt (y l)|
      = Real.sqrt (y j) * |X j l| * Real.sqrt (y l) := by
        rw [abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _),
          abs_of_nonneg (Real.sqrt_nonneg (y l))]
    _ ≤ Real.sqrt (y j) * (Real.sqrt (X j j) * Real.sqrt (X l l)) * Real.sqrt (y l) := by
        gcongr
    _ = (Real.sqrt (y j) * Real.sqrt (X j j)) * (Real.sqrt (y l) * Real.sqrt (X l l)) := by
        ring
    _ ≤ Real.sqrt (1 / h) * Real.sqrt (1 / h) :=
        mul_le_mul hsj hsl (by positivity) (Real.sqrt_nonneg _)
    _ = 1 / h := Real.mul_self_sqrt h0

/-- Off `S` the normalized precision is the identity row: `(P̃⁻¹)_kk = 1`. -/
theorem hN_of_not_mem {a τ : ℝ} {y : V → ℝ} {σ : Config V} {S : Finset V}
    (hP : (precN G a τ y σ S).PosDef) {k : V} (hk : k ∉ S) : hN G a τ y σ S k = 1 := by
  have hdet : IsUnit (precN G a τ y σ S).det := isUnit_iff_ne_zero.2 hP.det_pos.ne'
  have hcol : precN G a τ y σ S *ᵥ Pi.single k 1 = Pi.single k 1 := by
    funext u
    simp only [mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simp only [precN, Matrix.of_apply]
    by_cases hu : u = k
    · subst hu
      simp [hk]
    · simp [hu, hk]
  have h2 : (precN G a τ y σ S)⁻¹ *ᵥ Pi.single k 1 = Pi.single k 1 := by
    conv_lhs => rw [← hcol]
    rw [mulVec_mulVec, nonsing_inv_mul _ hdet, one_mulVec]
  have h3 := congrFun h2 k
  simp only [mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at h3
  exact h3

end Graph

section Contact

variable {d p : ℕ} (ct : Contact.{u} d p)

theorem corePD_of_wtCore {i : ct.V} {σ : Config ct.V}
    (hc : wtCore ct.G p (aOf d p) ct.yp ct.ym σ ct.S i ≠ 0) (e : Bool) :
    (precCore ct.G (aOf d p) (if e then 1 else -1) (ct.ySrc e) σ ct.S i).PosDef := by
  have hM : (precCore ct.G (aOf d p) 1 ct.yp σ ct.S i).PosDef ∧
      (precCore ct.G (aOf d p) (-1) ct.ym σ ct.S i).PosDef := by
    by_contra hn
    exact hc (by unfold wtCore; rw [if_neg hn])
  cases e
  · simpa [Contact.ySrc] using hM.2
  · simpa [Contact.ySrc] using hM.1

theorem nbhd_mem_erase {i : ct.V} (j : nbhd ct.G ct.S i) : (j : ct.V) ∈ ct.S.erase i :=
  Finset.mem_erase.2 ⟨nbhd_ne_self ct.G j.2, (Finset.mem_filter.1 j.2).1⟩

theorem uvec_abs_le (hd : (1 : ℝ) ≤ d) (k : ct.V) : |ct.uvec k| ≤ 1 := by
  unfold Contact.uvec
  split_ifs
  · have hs : 1 ≤ Real.sqrt d := by rw [Real.one_le_sqrt]; exact hd
    rw [abs_of_nonneg (by positivity), div_le_one (by positivity)]
    exact hs
  · simp

theorem card_N_le_d : ((ct.N).card : ℝ) ≤ d := card_nbhd_le_d ct.G ct.ctx.deg ct.S ct.v

theorem card_nbhd_le_d' (i : ct.V) : (Fintype.card (nbhd ct.G ct.S i) : ℝ) ≤ d := by
  rw [Fintype.card_coe]
  exact card_nbhd_le_d ct.G ct.ctx.deg ct.S i

/-- `|T_jl| ≤ d/h²` for both admissible maps (on the core support). -/
theorem tMap_abs_le (hd : (1 : ℝ) ≤ d) {h : ℝ} (hh : 0 < h) {i : ct.V} {σ : Config ct.V}
    (hc : wtCore ct.G p (aOf d p) ct.yp ct.ym σ ct.S i ≠ 0) (e dir : Bool)
    (j l : nbhd ct.G ct.S i) : |ct.tMap h e dir i σ j l| ≤ d / h ^ 2 := by
  have hC : ∀ (e' : Bool) {u w : ct.V}, u ∈ ct.S.erase i → w ∈ ct.S.erase i →
      |ct.Cb h e' σ i u w| ≤ 1 / h := fun e' u w hu hw =>
    coreShift_abs_le ct.G hh (fun k => ySrc_nonneg ct e' k) (corePD_of_wtCore ct hc e') hu hw
  have hj := nbhd_mem_erase ct j
  have hl := nbhd_mem_erase ct l
  have hh2 : 1 / h * 1 * (1 / h) = 1 / h ^ 2 := by field_simp
  have hterm : ∀ {u w k : ct.V}, u ∈ ct.S.erase i → w ∈ ct.S.erase i → k ∈ ct.S.erase i →
      |ct.Cb h e σ i u k * ct.uvec k * ct.Cb h true σ i k w| ≤ 1 / h ^ 2 := by
    intro u w k hu hw hk
    rw [abs_mul, abs_mul, ← hh2]
    exact mul_le_mul (mul_le_mul (hC e hu hk) (uvec_abs_le ct hd k) (abs_nonneg _)
      (by positivity)) (hC true hk hw) (abs_nonneg _) (by positivity)
  have h1d : 1 / h ^ 2 ≤ d / h ^ 2 := div_le_div_of_nonneg_right hd (by positivity)
  cases dir
  · simp only [Contact.tMap, Bool.false_eq_true, ↓reduceIte, Contact.tCav, Matrix.of_apply]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ k ∈ (ct.N.erase i).erase (l : ct.V),
          |ct.Cb h e σ i j k * ct.uvec k * ct.Cb h true σ i k l|
        ≤ ∑ _k ∈ (ct.N.erase i).erase (l : ct.V), 1 / h ^ 2 := by
          refine Finset.sum_le_sum fun k hk => hterm hj hl ?_
          have hk' := Finset.mem_of_mem_erase hk
          exact Finset.mem_erase.2 ⟨Finset.ne_of_mem_erase hk',
            Finset.filter_subset _ _ (Finset.mem_of_mem_erase hk')⟩
      _ = ((ct.N.erase i).erase (l : ct.V)).card * (1 / h ^ 2) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ d * (1 / h ^ 2) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          have h1 : ((ct.N.erase i).erase (l : ct.V)).card ≤ ct.N.card :=
            (Finset.card_le_card (Finset.erase_subset _ _)).trans
              (Finset.card_le_card (Finset.erase_subset _ _))
          exact le_trans (by exact_mod_cast h1) (card_N_le_d ct)
      _ = d / h ^ 2 := by ring
  · simp only [Contact.tMap, ↓reduceIte, Contact.tDir, Matrix.of_apply]
    split_ifs
    · exact (hterm hj hl hl).trans h1d
    · simp only [abs_zero]; positivity

/-- `tr L ≤ d⁴/h⁴` on the core support. -/
theorem trace_kerL_le (hd : (1 : ℝ) ≤ d) {h : ℝ} (hh : 0 < h) {i : ct.V} {σ : Config ct.V}
    (hc : wtCore ct.G p (aOf d p) ct.yp ct.ym σ ct.S i ≠ 0) (e dir : Bool) :
    (kerL ct h e dir i σ).trace ≤ (d : ℝ) ^ 4 / h ^ 4 := by
  unfold kerL
  rw [kerT_trace]
  have hT : ∀ a s : nbhd ct.G ct.S i, ct.tMap h e dir i σ a s ^ 2 ≤ (d / h ^ 2) ^ 2 := by
    intro a s
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (tMap_abs_le ct hd hh hc e dir a s) 2
  have hcard := card_nbhd_le_d' ct i
  calc ∑ s, ∑ a, ct.tMap h e dir i σ a s ^ 2 ≤ ∑ _s : nbhd ct.G ct.S i,
        ∑ _a : nbhd ct.G ct.S i, (d / h ^ 2) ^ 2 :=
        Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun a _ => hT a s
    _ = (Fintype.card (nbhd ct.G ct.S i) : ℝ) ^ 2 * (d / h ^ 2) ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring
    _ ≤ (d : ℝ) ^ 2 * (d / h ^ 2) ^ 2 :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 2) (by positivity)
    _ = (d : ℝ) ^ 4 / h ^ 4 := by field_simp

/-- `q_L(ξ) ≤ |N_S(i)| tr L` for a sign vector `ξ`. -/
theorem qForm_kerL_le {h : ℝ} (e dir : Bool) (i : ct.V) (σ : Config ct.V)
    {ξ : nbhd ct.G ct.S i → ℝ} (hξ : ∀ s, ξ s = 1 ∨ ξ s = -1) :
    qForm (kerL ct h e dir i σ) ξ ≤
      Fintype.card (nbhd ct.G ct.S i) * (kerL ct h e dir i σ).trace := by
  unfold kerL
  rw [kerT_qForm, kerT_trace]
  set T := ct.tMap h e dir i σ
  have hξ2 : ∑ s, ξ s ^ 2 = Fintype.card (nbhd ct.G ct.S i) := by
    rw [Finset.card_univ.symm, Finset.cast_card]
    exact Finset.sum_congr rfl fun s _ => by rcases hξ s with h1 | h1 <;> rw [h1] <;> norm_num
  have hpt : ∀ a, (T *ᵥ ξ) a ^ 2 ≤ (∑ s, T a s ^ 2) * Fintype.card (nbhd ct.G ct.S i) := by
    intro a
    rw [← hξ2]
    exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  calc ∑ a, (T *ᵥ ξ) a ^ 2 ≤ ∑ a, (∑ s, T a s ^ 2) * Fintype.card (nbhd ct.G ct.S i) :=
        Finset.sum_le_sum fun a _ => hpt a
    _ = _ := by
        rw [← Finset.sum_mul, Finset.sum_comm, mul_comm]

/-- Every physical inverse diagonal is between `0` and `3 h^b_k` on the support. -/
theorem diagB_le (hR : TRegime d p) {h : ℝ} (hh : 0 ≤ h) {σ : Config ct.V}
    (hσ : wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0) (k : ct.V) (b sh : Bool) :
    0 ≤ ct.diagB h σ k b sh ∧
      ct.diagB h σ k b sh ≤ 3 * hN ct.G (aOf d p) (if b then 1 else -1) (ct.ySrc b) σ ct.S k := by
  have hP : (precN ct.G (aOf d p) (if b then 1 else -1) (ct.ySrc b) σ ct.S).PosDef := by
    obtain ⟨h1, h2⟩ := posDef_of_wt_ne_zero ct.G hσ
    cases b
    · simpa [Contact.ySrc] using h2
    · simpa [Contact.ySrc] using h1
  have hy : ∀ k, 0 ≤ ct.ySrc b k := fun k => ySrc_nonneg ct b k
  have hy3 : ct.ySrc b k ≤ 3 := by
    have hc := SecC.inCube_of_cap ct.G hR ct.ctx.toCapCtx
      (show InCube (ct.lam * sOf d p) (ct.ySrc b) by cases b <;> simp [Contact.ySrc, ct.ctx.hyp, ct.ctx.hym])
    exact (hc k).2.trans (SecC.TRegime.sOf_le_three hR)
  have hN0 : 0 ≤ hN ct.G (aOf d p) (if b then 1 else -1) (ct.ySrc b) σ ct.S k :=
    hP.inv.diag_pos.le
  obtain ⟨hg0, hs0⟩ := diag_nonneg_of_posDef ct.G hP hy hh k
  have key : ct.diagB h σ k b sh = if sh then
      shiftP ct.G (aOf d p) (if b then 1 else -1) h (ct.ySrc b) σ ct.S k k
      else greenP ct.G (aOf d p) (if b then 1 else -1) (ct.ySrc b) σ ct.S k k := by
    cases b <;> cases sh <;> rfl
  rw [key]
  have hmul : ct.ySrc b k * hN ct.G (aOf d p) (if b then 1 else -1) (ct.ySrc b) σ ct.S k ≤
      3 * hN ct.G (aOf d p) (if b then 1 else -1) (ct.ySrc b) σ ct.S k :=
    mul_le_mul_of_nonneg_right hy3 hN0
  cases sh
  · simp only [Bool.false_eq_true, ↓reduceIte]
    refine ⟨hg0, ?_⟩
    rw [SecC.greenP_self ct.G hy σ ct.S k]
    exact hmul
  · simp only [↓reduceIte]
    refine ⟨hs0, ?_⟩
    have e1 : shiftP ct.G (aOf d p) (if b then 1 else -1) h (ct.ySrc b) σ ct.S k k =
        ct.ySrc b k * hzN ct.G (aOf d p) (if b then 1 else -1) h (ct.ySrc b) σ ct.S k := by
      unfold shiftP hzN
      rw [mul_comm (Real.sqrt _), mul_assoc, Real.mul_self_sqrt (hy k)]
      ring
    rw [e1]
    exact (mul_le_mul_of_nonneg_left (hzN_le_hN ct.G hP hh hy k) (hy k)).trans hmul

theorem wtH_eq_prod (h : ℝ) (e : Bool) (i : ct.V) (l : List (ct.V × Bool × Bool))
    (σ : Config ct.V) :
    ct.wtH h e i l σ = ((l ++ [(i, e, true), (i, e, true), (i, true, true), (i, true, true)]).map
      fun t => ct.diagB h σ t.1 t.2.1 t.2.2).prod := by
  have e1 : ct.diagB h σ i e true = ct.Xb h e σ i i := rfl
  have e2 : ct.diagB h σ i true true = ct.XP h σ i i := rfl
  simp only [Contact.wtH, Contact.diagW, List.map_append, List.prod_append, List.map_cons,
    List.prod_cons, List.map_nil, List.prod_nil, e1, e2]
  ring

/-- `E (h^b_k)^{2n} ≤ 4^n` for every vertex `k` (`4n ≤ p`). -/
theorem hN_pow_moment (hR : TRegime d p) (k : ct.V) (b : Bool) {n : ℕ} (hn : 4 * n ≤ p) :
    ct.E (fun σ => hN ct.G (aOf d p) (if b then 1 else -1) (ct.ySrc b) σ ct.S k ^ (2 * n)) ≤
      4 ^ n := by
  have hZ := SecC.Zw_pos_cap ct.G hR ct.ctx.toCapCtx ct.ctx.hyp ct.ctx.hym
  by_cases hk : k ∈ ct.S
  · have hb : SecC.IsBranch ct.yp ct.ym (if b then 1 else -1) (ct.ySrc b) := by
      cases b
      · simpa [Contact.ySrc] using SecC.isBranch_minus ct.yp ct.ym
      · simpa [Contact.ySrc] using SecC.isBranch_plus ct.yp ct.ym
    have := SecC.hN_moment_le ct.G hR ct.ctx.toCapCtx ct.ctx.hyp ct.ctx.hym hb hk
      (n := 2 * n) (by omega)
    refine this.trans_eq ?_
    rw [pow_mul]
    norm_num
  · have h1 : ct.E (fun σ => hN ct.G (aOf d p) (if b then 1 else -1) (ct.ySrc b) σ ct.S k ^
        (2 * n)) ≤ ct.E (fun _ => 1) := by
      refine lawE_mono ct.G fun σ hσ => ?_
      have hP : (precN ct.G (aOf d p) (if b then 1 else -1) (ct.ySrc b) σ ct.S).PosDef := by
        obtain ⟨h1, h2⟩ := posDef_of_wt_ne_zero ct.G hσ
        cases b
        · simpa [Contact.ySrc] using h2
        · simpa [Contact.ySrc] using h1
      rw [hN_of_not_mem ct.G hP hk, one_pow]
    refine h1.trans ?_
    rw [show ct.E (fun _ => (1 : ℝ)) = 1 from SecC.lawE_const_one ct.G hZ]
    exact one_le_pow₀ (by norm_num)

/-- `E H² ≤ 6^{2|L'|}` (`|L'| = |H₀| + 4`, `4|L'| ≤ p`). -/
theorem wtH_sq_moment (hR : TRegime d p) {h : ℝ} (hh : 0 ≤ h) (e : Bool) (i : ct.V)
    (l : List (ct.V × Bool × Bool)) (hp : 4 * (l.length + 4) ≤ p) :
    ct.E (fun σ => ct.wtH h e i l σ ^ 2) ≤ 6 ^ (2 * (l.length + 4)) := by
  set L' := l ++ [(i, e, true), (i, e, true), (i, true, true), (i, true, true)] with hL'
  have hlen : L'.length = l.length + 4 := by rw [hL']; simp
  set U : ct.V × Bool × Bool → Config ct.V → ℝ := fun t σ =>
    3 * hN ct.G (aOf d p) (if t.2.1 then 1 else -1) (ct.ySrc t.2.1) σ ct.S t.1 with hU
  have hpt : ∀ σ, wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 →
      ct.wtH h e i l σ ^ 2 ≤ (L'.map fun t => U t σ).prod ^ 2 := by
    intro σ hσ
    rw [wtH_eq_prod]
    have h0 : ∀ t : ct.V × Bool × Bool, 0 ≤ ct.diagB h σ t.1 t.2.1 t.2.2 := fun t =>
      (diagB_le ct hR hh hσ t.1 t.2.1 t.2.2).1
    exact pow_le_pow_left₀ (prod_map_nonneg' h0 _)
      (list_prod_map_le h0 (fun t => (diagB_le ct hR hh hσ t.1 t.2.1 t.2.2).2) _) 2
  have hm : ∀ t ∈ L', ct.E (fun σ => U t σ ^ (2 * L'.length)) ≤ 6 ^ (2 * L'.length) := by
    intro t _
    have h1 := hN_pow_moment ct hR t.1 t.2.1 (n := L'.length) (by rw [hlen]; exact hp)
    have e1 : (fun σ => U t σ ^ (2 * L'.length)) = fun σ => 9 ^ L'.length *
        hN ct.G (aOf d p) (if t.2.1 then 1 else -1) (ct.ySrc t.2.1) σ ct.S t.1 ^ (2 * L'.length) := by
      funext σ
      simp only [hU]
      rw [mul_pow, pow_mul]
      norm_num
    rw [e1, Contact.E, lawE_const_mul]
    calc 9 ^ L'.length * lawE ct.G p (aOf d p) ct.yp ct.ym ct.S (fun σ =>
          hN ct.G (aOf d p) (if t.2.1 then 1 else -1) (ct.ySrc t.2.1) σ ct.S t.1 ^ (2 * L'.length))
        ≤ 9 ^ L'.length * 4 ^ L'.length := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 6 ^ (2 * L'.length) := by rw [pow_mul, ← mul_pow]; norm_num
  have h2 := wavg_prod_sq_le (w := fun σ => wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S)
    (fun σ => wt_nonneg ct.G σ) L' (by rw [hlen]; omega) U (by norm_num) hm
  calc ct.E (fun σ => ct.wtH h e i l σ ^ 2)
      ≤ ct.E (fun σ => (L'.map fun t => U t σ).prod ^ 2) := lawE_mono ct.G hpt
    _ ≤ 6 ^ (2 * L'.length) := h2
    _ = 6 ^ (2 * (l.length + 4)) := by rw [hlen]

/-- **The second moment of the multiplier**: `E[(H (q_L + tr L))²] ≤ ((d+1) d⁴/h⁴)² 6^{2|L'|}`. -/
theorem X_sq_moment (hR : TRegime d p) {h : ℝ} (hh : 0 < h) (e dir : Bool) {i : ct.V}
    (hi : i ∈ ct.S) (l : List (ct.V × Bool × Bool)) (hp : 4 * (l.length + 4) ≤ p) :
    ct.E (fun σ => (ct.wtH h e i l σ * (qForm (kerL ct h e dir i σ) (rootSigns ct.G σ ct.S i) +
      (kerL ct h e dir i σ).trace)) ^ 2) ≤
      (((d : ℝ) + 1) * ((d : ℝ) ^ 4 / h ^ 4)) ^ 2 * 6 ^ (2 * (l.length + 4)) := by
  have hd : (1 : ℝ) ≤ d := le_trans (by norm_num) hR.ten_pow_six_le_d
  have hp1 : 1 ≤ p := le_trans (by norm_num) hR.two_le_p
  have hyp0 : ∀ k, 0 ≤ ct.yp k := fun k => (ct.ctx.hyp k).1
  have hym0 : ∀ k, 0 ≤ ct.ym k := fun k => (ct.ctx.hym k).1
  set B := ((d : ℝ) + 1) * ((d : ℝ) ^ 4 / h ^ 4) with hB
  have hpt : ∀ σ, wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 →
      (ct.wtH h e i l σ * (qForm (kerL ct h e dir i σ) (rootSigns ct.G σ ct.S i) +
        (kerL ct h e dir i σ).trace)) ^ 2 ≤ B ^ 2 * ct.wtH h e i l σ ^ 2 := by
    intro σ hσ
    have hc := SecC.wtCore_ne_zero_of_wt ct.G hp1 hyp0 hym0 hi hσ
    have hH0 := wtH_nonneg ct hh.le e i l hσ
    have hq0 : 0 ≤ qForm (kerL ct h e dir i σ) (rootSigns ct.G σ ct.S i) := by
      have := (kerL_posSemidef ct h e dir i σ).dotProduct_mulVec_nonneg (rootSigns ct.G σ ct.S i)
      simp only [star_trivial] at this
      exact this
    have htr0 : 0 ≤ (kerL ct h e dir i σ).trace := (kerL_posSemidef ct h e dir i σ).trace_nonneg
    have htr := trace_kerL_le ct hd hh hc e dir
    have hq := qForm_kerL_le ct (h := h) e dir i σ (rootSigns_pm ct σ i)
    have hcard := card_nbhd_le_d' ct i
    have hsum : qForm (kerL ct h e dir i σ) (rootSigns ct.G σ ct.S i) +
        (kerL ct h e dir i σ).trace ≤ B := by
      calc _ ≤ (Fintype.card (nbhd ct.G ct.S i) : ℝ) * (kerL ct h e dir i σ).trace +
            (kerL ct h e dir i σ).trace := by linarith
        _ ≤ (d : ℝ) * (kerL ct h e dir i σ).trace + (kerL ct h e dir i σ).trace := by
            gcongr
        _ = ((d : ℝ) + 1) * (kerL ct h e dir i σ).trace := by ring
        _ ≤ B := mul_le_mul_of_nonneg_left htr (by positivity)
    have h0 : 0 ≤ qForm (kerL ct h e dir i σ) (rootSigns ct.G σ ct.S i) +
        (kerL ct h e dir i σ).trace := by linarith
    calc _ = ct.wtH h e i l σ ^ 2 * (qForm (kerL ct h e dir i σ) (rootSigns ct.G σ ct.S i) +
          (kerL ct h e dir i σ).trace) ^ 2 := by ring
      _ ≤ ct.wtH h e i l σ ^ 2 * B ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 hsum 2) (sq_nonneg _)
      _ = B ^ 2 * ct.wtH h e i l σ ^ 2 := by ring
  calc _ ≤ ct.E (fun σ => B ^ 2 * ct.wtH h e i l σ ^ 2) := lawE_mono ct.G hpt
    _ = B ^ 2 * ct.E (fun σ => ct.wtH h e i l σ ^ 2) := lawE_const_mul ct.G _ _
    _ ≤ B ^ 2 * 6 ^ (2 * (l.length + 4)) :=
        mul_le_mul_of_nonneg_left (wtH_sq_moment ct hR hh.le e i l hp) (sq_nonneg _)

end Contact

end BiluLinial.Tight.SecB
