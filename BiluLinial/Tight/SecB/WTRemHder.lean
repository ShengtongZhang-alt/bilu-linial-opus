/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecB.WTRemDer

/-!
# The derivative hypotheses of `trans_rem_lo` for the (WT5) observables

`hder_Q`, `hder_T`: for every `σ`, `x` and derivative list `ν` (`|ν| ≤ N`),
`|∂^ν F(σ)(x)| ≤ m(σ) (8p)^{|ν|} Π_{s ∈ ν} √b_s` with `m = 0` off the core support;
`smoothBdd_Q`, `smoothBdd_T`: `F(σ)` is `SmoothBdd N`.
-/

@[expose] public section

namespace BiluLinial.Tight.SecB.WR

open Matrix SecA.CR SecA.StarCalc

section Contact

variable {d p : ℕ}

/-- `ĉ = c_L y⁺_i/a²`. -/
noncomputable def cHat (ct : Contact.{u} d p) (h : ℝ) (σ : Config ct.V) (i : ct.V) : ℝ :=
  cL ct h σ i * (ct.yp i / aOf d p ^ 2)

/-- The majorant constant of `Φ H q_L` (`0` off the core support). -/
noncomputable def mQ (ct : Contact.{u} d p) (h : ℝ) (e : Bool) (i : ct.V)
    (l : List (ct.V × Bool × Bool)) (σ : Config ct.V) : ℝ :=
  if wtCore ct.G p (aOf d p) ct.yp ct.ym σ ct.S i ≠ 0 then
    2 * (l.map fun t => |fc ct h σ i t|).prod * (cE ct h e σ i ^ 2 * cHat ct h σ i)
  else 0

/-- The majorant constant of `tr L · Φ H` (`0` off the core support). -/
noncomputable def mT (ct : Contact.{u} d p) (h : ℝ) (e dir : Bool) (i : ct.V)
    (l : List (ct.V × Bool × Bool)) (σ : Config ct.V) : ℝ :=
  if wtCore ct.G p (aOf d p) ct.yp ct.ym σ ct.S i ≠ 0 then
    2 * (l.map fun t => |fc ct h σ i t|).prod *
      |cE ct h e σ i ^ 2 * (cE ct h true σ i ^ 2 * (kerL ct h e dir i σ).trace)|
  else 0

theorem cL_nonneg (ct : Contact.{u} d p) {h : ℝ} (hh : 0 < h) (σ : Config ct.V) (i : ct.V) :
    0 ≤ cL ct h σ i := by
  unfold cL
  have : 0 ≤ ∑ k ∈ ct.N, ((precCore ct.G (aOf d p) 1 ct.yp σ ct.S i)⁻¹ k k) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  positivity

theorem cHat_nonneg (ct : Contact.{u} d p) {h : ℝ} (hh : 0 < h) (σ : Config ct.V) (i : ct.V) :
    0 ≤ cHat ct h σ i :=
  mul_nonneg (cL_nonneg ct hh σ i) (div_nonneg (ct.ctx.hyp i).1 (sq_nonneg _))

theorem mQ_nonneg (ct : Contact.{u} d p) {h : ℝ} (hh : 0 < h) (e : Bool) (i : ct.V)
    (l : List (ct.V × Bool × Bool)) (σ : Config ct.V) : 0 ≤ mQ ct h e i l σ := by
  unfold mQ
  split_ifs
  · have h1 : 0 ≤ (l.map fun t => |fc ct h σ i t|).prod := List.prod_nonneg fun a ha => by
      obtain ⟨t, -, rfl⟩ := List.mem_map.1 ha
      exact abs_nonneg _
    have := cHat_nonneg ct hh σ i
    positivity
  · exact le_rfl

theorem mT_nonneg (ct : Contact.{u} d p) (h : ℝ) (e dir : Bool) (i : ct.V)
    (l : List (ct.V × Bool × Bool)) (σ : Config ct.V) : 0 ≤ mT ct h e dir i l σ := by
  unfold mT
  split_ifs
  · have h1 : 0 ≤ (l.map fun t => |fc ct h σ i t|).prod := List.prod_nonneg fun a ha => by
      obtain ⟨t, -, rfl⟩ := List.mem_map.1 ha
      exact abs_nonneg _
    positivity
  · exact le_rfl

theorem cE_true_eq (ct : Contact.{u} d p) (h : ℝ) (σ : Config ct.V) (i : ct.V) :
    cE ct h true σ i =
      ct.yp i / (diagD ct.G (aOf d p) ct.yp ct.S i + h * ct.yp i) := by
  unfold cE cVal
  rw [if_pos rfl]
  rfl

theorem precCore_diag_le_two (hR : TRegime d p) (ct : Contact.{u} d p) {τ : ℝ} {y : ct.V → ℝ}
    (hy : InCube (sOf d p) y) (σ : Config ct.V) (i k : ct.V) :
    precCore ct.G (aOf d p) τ y σ ct.S i k k ≤ 2 := by
  have hD := SecA.diagD_le_two ct.G hR ct.ctx.deg hy ct.S k
  simp only [precCore, precN, of_apply]
  split_ifs <;> linarith

theorem yp_inCube (hR : TRegime d p) (ct : Contact.{u} d p) : InCube (sOf d p) ct.yp :=
  ct.ctx.hyp.of_mul_le_one ct.ctx.lam_le_one hR.sOf_pos.le

/-- `q_{c₊² L} ≤ ĉ q_A`. -/
theorem qForm_LQ_le (hR : TRegime d p) (ct : Contact.{u} d p) {h : ℝ} (hh : 0 < h)
    (e dir : Bool) {i : ct.V} {σ : Config ct.V}
    (hw : wtCore ct.G p (aOf d p) ct.yp ct.ym σ ct.S i ≠ 0) (x : nbhd ct.G ct.S i → ℝ) :
    qForm (cE ct h true σ i ^ 2 • kerL ct h e dir i σ) x ≤
      cHat ct h σ i * qForm (rootA ct σ i) x := by
  have hd : (0 : ℝ) < d := Nat.cast_pos.2 (by have := hR.ten_pow_six_le_nat; omega)
  have hMp : (precCore ct.G (aOf d p) 1 ct.yp σ ct.S i).PosDef := wtCore_pd ct hw true
  have hMe := wtCore_pd ct hw e
  have hyp : ∀ k, 0 ≤ ct.yp k := fun k => (ct.ctx.hyp k).1
  have hy2 : ∀ k, ct.yp k ≤ 2 := fun k => ySrc_le_two hR ct true k
  have hP2 : ∀ k, precCore ct.G (aOf d p) 1 ct.yp σ ct.S i k k ≤ 2 :=
    fun k => precCore_diag_le_two hR ct (yp_inCube hR ct) σ i k
  have henv := env_qForm ct hd hh e dir σ hMp hMe (ySrc_nonneg ct e) hyp hy2 hP2 x
  have hBq0 := Bq_nonneg ct hMp x
  have hqA : qForm (rootA ct σ i) x =
      aOf d p ^ 2 * ct.yp i / diagD ct.G (aOf d p) ct.yp ct.S i * Bq ct σ i x :=
    qForm_rootMat_dot ct.G (aOf d p) 1 ct.yp σ ct.S i x
  have ha := hR.aOf_pos
  have hD1 : 1 ≤ diagD ct.G (aOf d p) ct.yp ct.S i := FloorIns.one_le_diagD ct.G _ hyp _ _
  have hy0 := hyp i
  have hcL := cL_nonneg ct hh σ i
  rw [qForm_smul', hqA, cE_true_eq]
  unfold cHat
  set y := ct.yp i
  set D := diagD ct.G (aOf d p) ct.yp ct.S i
  have hDh : D ≤ (D + h * y) ^ 2 := by nlinarith [mul_nonneg hh.le hy0]
  have hcoef : (y / (D + h * y)) ^ 2 ≤ y ^ 2 / D := by
    rw [div_pow]
    exact div_le_div_of_nonneg_left (sq_nonneg y) (by linarith) hDh
  calc (y / (D + h * y)) ^ 2 * qForm (kerL ct h e dir i σ) x
      ≤ (y / (D + h * y)) ^ 2 * (cL ct h σ i * Bq ct σ i x) :=
        mul_le_mul_of_nonneg_left henv (sq_nonneg _)
    _ ≤ y ^ 2 / D * (cL ct h σ i * Bq ct σ i x) :=
        mul_le_mul_of_nonneg_right hcoef (mul_nonneg hcL hBq0)
    _ = cL ct h σ i * (y / aOf d p ^ 2) * (aOf d p ^ 2 * y / D * Bq ct σ i x) := by
        field_simp

namespace Interior

variable {ct : Contact.{u} d p} {h : ℝ} {σ : Config ct.V} {i : ct.V}
  {x₀ : nbhd ct.G ct.S i → ℝ} (I : Interior ct h σ i x₀)
include I

theorem majN_LQ (hR : TRegime d p) (e dir : Bool) (N : ℕ) :
    MajN N x₀ (lamW ct h σ i x₀) (cE ct h e σ i ^ 2 * cHat ct h σ i) 2
      (fun x => cE ct h e σ i ^ 2 * qForm (cE ct h true σ i ^ 2 • kerL ct h e dir i σ) x) := by
  have hLp : (cE ct h true σ i ^ 2 • kerL ct h e dir i σ).PosSemidef := by
    have h1 := posSemidef_conjTranspose_mul_self (ct.tMap h e dir i σ)
    rw [conjTranspose_eq_transpose_of_trivial] at h1
    exact h1.smul (sq_nonneg _)
  have hQ := quadMaj_psd_dom hLp (cHat_nonneg ct I.hh σ i) (qForm_LQ_le hR ct I.hh e dir I.hw)
    I.bd_nonneg (I.Xb_diag_le true) I.hA0.le
  have hQ' := QuadMaj.mono_lam hQ (cHat_nonneg ct I.hh σ i) (fun s => Real.sqrt_nonneg _)
    (fun s => le_mul_of_one_le_left (Real.sqrt_nonneg _) I.one_le_kappa)
  have hM := (majN_const N x₀ (lamW ct h σ i x₀) (cE ct h e σ i ^ 2)).mul
    (majN_quadFn I.lam_nonneg hQ')
  have e1 : (fun _ : nbhd ct.G ct.S i → ℝ => cE ct h e σ i ^ 2) *
      quadFn 0 0 (cE ct h true σ i ^ 2 • kerL ct h e dir i σ) =
      fun x => cE ct h e σ i ^ 2 * qForm (cE ct h true σ i ^ 2 • kerL ct h e dir i σ) x := by
    funext x
    simp [quadFn]
  rw [e1, abs_of_nonneg (sq_nonneg _), zero_add] at hM
  exact hM

theorem majN_LT (e dir : Bool) (N : ℕ) :
    MajN N x₀ (lamW ct h σ i x₀)
      |cE ct h e σ i ^ 2 * (cE ct h true σ i ^ 2 * (kerL ct h e dir i σ).trace)| 2
      (fun _ => cE ct h e σ i ^ 2 * (cE ct h true σ i ^ 2 * (kerL ct h e dir i σ).trace)) :=
  (majN_const N x₀ _ _).mono I.lam_nonneg le_rfl le_rfl (by norm_num)

end Interior

/-- The parameter conditions of the derivative bounds. -/
structure Params (h : ℝ) (p N : ℕ) {T : Type*} (l : List (T × Bool × Bool)) : Prop where
  hl : l.length < p
  hE1 : l.length + 4 + N ≤ eOne p l
  hE2 : l.length + 4 + N ≤ eTwo p l
  hK : 4 * ((l.length : ℝ) + 4) + 8 * N + 2 * l.length + 2 + 2 * (eOne p l : ℝ) +
    2 * (eTwo p l : ℝ) ≤ 8 * p
  hh2 : (1 + 2 * h) ^ (l.length + 4 + N) ≤ 2

theorem hder_Q (hR : TRegime d p) (ct : Contact.{u} d p) {h : ℝ} (hh : 0 < h) (e dir : Bool)
    {i : ct.V} (hi : i ∈ ct.S) (l : List (ct.V × Bool × Bool)) {N : ℕ} (hP : Params h p N l)
    (σ : Config ct.V) (L : List (nbhd ct.G ct.S i)) (hL : L.length ≤ N)
    (x : nbhd ct.G ct.S i → ℝ) :
    |pderivList L (starObsQ ct h e dir i l σ) x| ≤
      mQ ct h e i l σ * (8 * p) ^ L.length * (L.map fun s => Real.sqrt (bd ct σ i s)).prod := by
  have hy2 := ySrc_le_two hR ct
  by_cases hw : wtCore ct.G p (aOf d p) ct.yp ct.ym σ ct.S i ≠ 0
  · rw [starObsQ_eq_clip ct hh hy2 e dir hi l hP.hl hw]
    simp only [mQ, if_pos hw]
    exact deriv_global hh hi hw hy2 e l hP.hE1 hP.hE2 hP.hK hP.hh2 _
      (fun x₀ hA hB => (Interior.majN_LQ ⟨hh, hi, hw, hA, hB, hy2⟩ hR e dir N)) L hL x
  · have hF : starObsQ ct h e dir i l σ = fun _ => 0 := by
      simp only [starObsQ, if_neg hw]
    rw [hF, SecA.CA.pderivList_zero_fn]
    simp only [mQ, if_neg hw, abs_zero, zero_mul, le_refl]

theorem hder_T (hR : TRegime d p) (ct : Contact.{u} d p) {h : ℝ} (hh : 0 < h) (e dir : Bool)
    {i : ct.V} (hi : i ∈ ct.S) (l : List (ct.V × Bool × Bool)) {N : ℕ} (hP : Params h p N l)
    (σ : Config ct.V) (L : List (nbhd ct.G ct.S i)) (hL : L.length ≤ N)
    (x : nbhd ct.G ct.S i → ℝ) :
    |pderivList L (starObsT ct h e dir i l σ) x| ≤
      mT ct h e dir i l σ * (8 * p) ^ L.length *
        (L.map fun s => Real.sqrt (bd ct σ i s)).prod := by
  have hy2 := ySrc_le_two hR ct
  by_cases hw : wtCore ct.G p (aOf d p) ct.yp ct.ym σ ct.S i ≠ 0
  · rw [starObsT_eq_clip ct hh hy2 e dir hi l hP.hl hw]
    simp only [mT, if_pos hw]
    exact deriv_global hh hi hw hy2 e l hP.hE1 hP.hE2 hP.hK hP.hh2 _
      (fun x₀ hA hB => (Interior.majN_LT ⟨hh, hi, hw, hA, hB, hy2⟩ e dir N)) L hL x
  · have hF : starObsT ct h e dir i l σ = fun _ => 0 := by
      simp only [starObsT, if_neg hw]
    rw [hF, SecA.CA.pderivList_zero_fn]
    simp only [mT, if_neg hw, abs_zero, zero_mul, le_refl]

theorem smoothBdd_Q (hR : TRegime d p) (ct : Contact.{u} d p) {h : ℝ} (hh : 0 < h)
    (e dir : Bool) {i : ct.V} (hi : i ∈ ct.S) (l : List (ct.V × Bool × Bool)) {N : ℕ}
    (hP : Params h p N l) (σ : Config ct.V) : SmoothBdd N (starObsQ ct h e dir i l σ) := by
  have hy2 := ySrc_le_two hR ct
  by_cases hw : wtCore ct.G p (aOf d p) ct.yp ct.ym σ ct.S i ≠ 0
  · refine ⟨?_, fun L hL => ⟨_, fun x => hder_Q hR ct hh e dir hi l hP σ L hL x⟩⟩
    rw [starObsQ_eq_clip ct hh hy2 e dir hi l hP.hl hw]
    have h0A : qForm (rootA ct σ i) 0 < 1 := by rw [qForm_zero_vec]; exact one_pos
    have h0B : qForm (rootB ct σ i) 0 < 1 := by rw [qForm_zero_vec]; exact one_pos
    have I0 : Interior ct h σ i 0 := ⟨hh, hi, hw, h0A, h0B, hy2⟩
    have hsm := (I0.majN_G e l N _ (I0.majN_LQ hR e dir N)).1
    exact (SecA.contDiff_clipObs hsm _ _ _ _).of_le
      (by exact_mod_cast (by have := hP.hE1; have := hP.hE2; omega :
        N ≤ min (eOne p l) (eTwo p l) - 1))
  · have hF : starObsQ ct h e dir i l σ = fun _ => 0 := by
      simp only [starObsQ, if_neg hw]
    rw [hF]
    exact SecA.CA.smoothBdd_zero_fn N

theorem smoothBdd_T (hR : TRegime d p) (ct : Contact.{u} d p) {h : ℝ} (hh : 0 < h)
    (e dir : Bool) {i : ct.V} (hi : i ∈ ct.S) (l : List (ct.V × Bool × Bool)) {N : ℕ}
    (hP : Params h p N l) (σ : Config ct.V) : SmoothBdd N (starObsT ct h e dir i l σ) := by
  have hy2 := ySrc_le_two hR ct
  by_cases hw : wtCore ct.G p (aOf d p) ct.yp ct.ym σ ct.S i ≠ 0
  · refine ⟨?_, fun L hL => ⟨_, fun x => hder_T hR ct hh e dir hi l hP σ L hL x⟩⟩
    rw [starObsT_eq_clip ct hh hy2 e dir hi l hP.hl hw]
    have h0A : qForm (rootA ct σ i) 0 < 1 := by rw [qForm_zero_vec]; exact one_pos
    have h0B : qForm (rootB ct σ i) 0 < 1 := by rw [qForm_zero_vec]; exact one_pos
    have I0 : Interior ct h σ i 0 := ⟨hh, hi, hw, h0A, h0B, hy2⟩
    have hsm := (I0.majN_G e l N _ (I0.majN_LT e dir N)).1
    exact (SecA.contDiff_clipObs hsm _ _ _ _).of_le
      (by exact_mod_cast (by have := hP.hE1; have := hP.hE2; omega :
        N ≤ min (eOne p l) (eTwo p l) - 1))
  · have hF : starObsT ct h e dir i l σ = fun _ => 0 := by
      simp only [starObsT, if_neg hw]
    rw [hF]
    exact SecA.CA.smoothBdd_zero_fn N

end Contact

end BiluLinial.Tight.SecB.WR
