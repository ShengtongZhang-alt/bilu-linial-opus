/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecB.WTRemMajC

/-!
# Pointwise derivative bounds of the (WT5) observables (sub-node (R3′) of TB.WT5r°)

For every configuration `σ`, star vector `x` and derivative list `ν` of length `≤ N`:
`|∂^ν (Φ H q_L)(x)| ≤ m_Q(σ) (8p)^{|ν|} Π_{s ∈ ν} √b_s` and the same for `tr L · Φ H` with
`m_T(σ)` (`hder_Q`, `hder_T`), where (on the core support, `0` off it)
`m_Q = 2 Π_t |c_t| · c_e² · c_L y⁺_i/a²`, `m_T = 2 Π_t |c_t| · |c_e² c₊² tr L|`.
Hypotheses on the parameters: `|l| + 4 + N ≤ e₁, e₂`, `K_G + 2e₁ + 2e₂ ≤ 8p`,
`(1 + 2h)^{|l|+4+N} ≤ 2`.
-/

@[expose] public section

namespace BiluLinial.Tight.SecB.WR

open Matrix SecA.CR SecA.StarCalc

section Contact

variable {d p : ℕ}

namespace Interior

variable {ct : Contact.{u} d p} {h : ℝ} {σ : Config ct.V} {i : ct.V}
  {x₀ : nbhd ct.G ct.S i → ℝ} (I : Interior ct h σ i x₀)
include I

/-- The interior derivative bound. -/
theorem deriv_interior (e : Bool) (l : List (ct.V × Bool × Bool)) {N : ℕ}
    (hE1 : l.length + 4 + N ≤ eOne p l) (hE2 : l.length + 4 + N ≤ eTwo p l)
    (hK : 4 * ((l.length : ℝ) + 4) + 8 * N + 2 * l.length + 2 + 2 * (eOne p l : ℝ) +
      2 * (eTwo p l : ℝ) ≤ 8 * p)
    (hh2 : (1 + 2 * h) ^ (l.length + 4 + N) ≤ 2)
    (Lfac : (nbhd ct.G ct.S i → ℝ) → ℝ) {ML : ℝ} (hLf : MajN N x₀ (lamW ct h σ i x₀) ML 2 Lfac)
    (L : List (nbhd ct.G ct.S i)) (hL : L.length ≤ N) :
    |pderivList L (clipObs (fun x => wR ct h true σ i (sP e l) x * wR ct h false σ i (sM e l) x *
        Pl ct h σ i l x * Lfac x) (eOne p l) (eTwo p l) (rootA ct σ i) (rootB ct σ i)) x₀| ≤
      2 * (l.map fun t => |fc ct h σ i t|).prod * ML * (8 * p) ^ L.length *
        (L.map fun s => Real.sqrt (bd ct σ i s)).prod := by
  have hG := I.majN_G e l N Lfac hLf
  have hQA := I.quadMaj_X true
  have hQB := I.quadMaj_X false
  have hb := pderivList_clipObs_le_majN (e₁ := eOne p l) (e₂ := eTwo p l) I.hA0 I.hB0
    I.lam_nonneg hG hQA hQB L hL
  refine hb.trans ?_
  obtain ⟨hκp, -, -, -⟩ := I.shift_facts true
  obtain ⟨hκm, -, -, -⟩ := I.shift_facts false
  have hκ1 := I.one_le_kappa
  set κ := (1 + 2 * h) / min (1 - qForm (rootA ct σ i) x₀) (1 - qForm (rootB ct σ i) x₀)
    with hκdef
  have hprod : (L.map (lamW ct h σ i x₀)).prod =
      κ ^ L.length * (L.map fun s => Real.sqrt (bd ct σ i s)).prod := by
    have e1 : lamW ct h σ i x₀ = fun s => κ * Real.sqrt (bd ct σ i s) := rfl
    rw [e1, List.prod_map_mul, List.map_const', List.prod_replicate]
  rw [hprod]
  have hML : 0 ≤ ML := by
    have := hLf.2 [] (by simp)
    simp only [List.length_nil, pow_zero, mul_one, List.map_nil, List.prod_nil] at this
    exact (abs_nonneg _).trans this
  have hspm := sP_add_sM_le e l
  have hκ0 : 0 < κ := by linarith
  have hrp : 0 < 1 - qForm (Ash ct h true σ i) x₀ :=
    pos_of_mul_pos_right (by linarith : 0 < κ * (1 - qForm (Ash ct h true σ i) x₀)) hκ0.le
  have hrm : 0 < 1 - qForm (Ash ct h false σ i) x₀ :=
    pos_of_mul_pos_right (by linarith : 0 < κ * (1 - qForm (Ash ct h false σ i) x₀)) hκ0.le
  have hα0 : 0 < 1 - qForm (rootA ct σ i) x₀ := by linarith [I.hA0]
  have hβ0 : 0 < 1 - qForm (rootB ct σ i) x₀ := by linarith [I.hB0]
  have hα1 : 1 - qForm (rootA ct σ i) x₀ ≤ 1 := by linarith [qForm_nonneg I.rootA_psd x₀]
  have hβ1 : 1 - qForm (rootB ct σ i) x₀ ≤ 1 := by linarith [qForm_nonneg I.rootB_psd x₀]
  have hE1' : sP e l + sM e l + L.length ≤ eOne p l := by omega
  have hE2' : sP e l + sM e l + L.length ≤ eTwo p l := by omega
  have hh2' : (1 + 2 * h) ^ (sP e l + sM e l + L.length) ≤ 2 :=
    le_trans (pow_le_pow_right₀ (by linarith [I.hh]) (by omega)) hh2
  have hC : 0 ≤ (l.map fun t => |fc ct h σ i t| * 1).prod * ML :=
    mul_nonneg (List.prod_nonneg fun a ha => by
      obtain ⟨t, -, rfl⟩ := List.mem_map.1 ha
      positivity) hML
  have hspm' : (sP e l : ℝ) + sM e l ≤ l.length + 4 := by exact_mod_cast hspm
  have hK0 : 0 ≤ 4 * ((sP e l : ℝ) + N) + 4 * ((sM e l : ℝ) + N) + l.length * (0 + 2) + 2 +
      2 * (eOne p l : ℝ) + 2 * (eTwo p l : ℝ) := by positivity
  have hK' : 4 * ((sP e l : ℝ) + N) + 4 * ((sM e l : ℝ) + N) + l.length * (0 + 2) + 2 +
      2 * (eOne p l : ℝ) + 2 * (eTwo p l : ℝ) ≤ 8 * p := by linarith
  have hP : 0 ≤ (L.map fun s => Real.sqrt (bd ct σ i s)).prod :=
    List.prod_nonneg fun a ha => by
      obtain ⟨s, -, rfl⟩ := List.mem_map.1 ha
      exact Real.sqrt_nonneg _
  have hfin := final_combine (α := 1 - qForm (rootA ct σ i) x₀)
    (β := 1 - qForm (rootB ct σ i) x₀) (h := h) (κ := κ)
    (rp := 1 - qForm (Ash ct h true σ i) x₀) (rm := 1 - qForm (Ash ct h false σ i) x₀)
    (C := (l.map fun t => |fc ct h σ i t| * 1).prod * ML)
    (K' := 4 * ((sP e l : ℝ) + N) + 4 * ((sM e l : ℝ) + N) + l.length * (0 + 2) + 2 +
      2 * (eOne p l : ℝ) + 2 * (eTwo p l : ℝ))
    (P := (L.map fun s => Real.sqrt (bd ct σ i s)).prod) (p8 := 8 * p)
    (sp := sP e l) (sm := sM e l) (n := L.length) (e₁ := eOne p l) (e₂ := eTwo p l)
    hα0 hα1 hβ0 hβ1 I.hh.le hκdef hrp hrm hκp hκm hE1' hE2' hh2' hC hK0 hK' hP
  have hfc : (l.map fun t => |fc ct h σ i t| * 1).prod = (l.map fun t => |fc ct h σ i t|).prod := by
    simp only [mul_one]
  rw [hfc] at hfin
  calc (1 - qForm (Ash ct h true σ i) x₀)⁻¹ ^ sP e l *
          (1 - qForm (Ash ct h false σ i) x₀)⁻¹ ^ sM e l *
          (l.map fun t => |fc ct h σ i t| * 1).prod * ML *
          (1 - qForm (Xb ct true σ i) x₀) ^ eOne p l *
          (1 - qForm (Xb ct false σ i) x₀) ^ eTwo p l *
          (4 * ((sP e l : ℝ) + N) + 4 * ((sM e l : ℝ) + N) + l.length * (0 + 2) + 2 +
            2 * (eOne p l : ℝ) + 2 * (eTwo p l : ℝ)) ^ L.length *
          (κ ^ L.length * (L.map fun s => Real.sqrt (bd ct σ i s)).prod)
        = (1 - qForm (Ash ct h true σ i) x₀)⁻¹ ^ sP e l *
          (1 - qForm (Ash ct h false σ i) x₀)⁻¹ ^ sM e l *
          ((l.map fun t => |fc ct h σ i t|).prod * ML) *
          (1 - qForm (Xb ct true σ i) x₀) ^ eOne p l *
          (1 - qForm (Xb ct false σ i) x₀) ^ eTwo p l *
          (4 * ((sP e l : ℝ) + N) + 4 * ((sM e l : ℝ) + N) + l.length * (0 + 2) + 2 +
            2 * (eOne p l : ℝ) + 2 * (eTwo p l : ℝ)) ^ L.length *
          (κ ^ L.length * (L.map fun s => Real.sqrt (bd ct σ i s)).prod) := by
          rw [hfc]
          ring
      _ ≤ 2 * ((l.map fun t => |fc ct h σ i t|).prod * ML) * (8 * p) ^ L.length *
          (L.map fun s => Real.sqrt (bd ct σ i s)).prod := hfin
      _ = _ := by ring

end Interior

theorem qForm_zero_vec {ι : Type*} [Fintype ι] (M : Matrix ι ι ℝ) : qForm M 0 = 0 := by
  simp [qForm]

/-- The global derivative bound (zero off `{q_A, q_B < 1}`). -/
theorem deriv_global {ct : Contact.{u} d p} {h : ℝ} (hh : 0 < h) {σ : Config ct.V} {i : ct.V}
    (hi : i ∈ ct.S) (hw : wtCore ct.G p (aOf d p) ct.yp ct.ym σ ct.S i ≠ 0)
    (hy2 : ∀ b k, ct.ySrc b k ≤ 2) (e : Bool) (l : List (ct.V × Bool × Bool)) {N : ℕ}
    (hE1 : l.length + 4 + N ≤ eOne p l) (hE2 : l.length + 4 + N ≤ eTwo p l)
    (hK : 4 * ((l.length : ℝ) + 4) + 8 * N + 2 * l.length + 2 + 2 * (eOne p l : ℝ) +
      2 * (eTwo p l : ℝ) ≤ 8 * p)
    (hh2 : (1 + 2 * h) ^ (l.length + 4 + N) ≤ 2)
    (Lfac : (nbhd ct.G ct.S i → ℝ) → ℝ) {ML : ℝ}
    (hLf : ∀ x₀, qForm (rootA ct σ i) x₀ < 1 → qForm (rootB ct σ i) x₀ < 1 →
      MajN N x₀ (lamW ct h σ i x₀) ML 2 Lfac)
    (L : List (nbhd ct.G ct.S i)) (hL : L.length ≤ N) (x : nbhd ct.G ct.S i → ℝ) :
    |pderivList L (clipObs (fun x => wR ct h true σ i (sP e l) x * wR ct h false σ i (sM e l) x *
        Pl ct h σ i l x * Lfac x) (eOne p l) (eTwo p l) (rootA ct σ i) (rootB ct σ i)) x| ≤
      2 * (l.map fun t => |fc ct h σ i t|).prod * ML * (8 * p) ^ L.length *
        (L.map fun s => Real.sqrt (bd ct σ i s)).prod := by
  have h0A : qForm (rootA ct σ i) 0 < 1 := by rw [qForm_zero_vec]; exact one_pos
  have h0B : qForm (rootB ct σ i) 0 < 1 := by rw [qForm_zero_vec]; exact one_pos
  have I0 : Interior ct h σ i 0 := ⟨hh, hi, hw, h0A, h0B, hy2⟩
  by_cases hU : qForm (rootA ct σ i) x < 1 ∧ qForm (rootB ct σ i) x < 1
  · have I : Interior ct h σ i x := ⟨hh, hi, hw, hU.1, hU.2, hy2⟩
    exact I.deriv_interior e l hE1 hE2 hK hh2 Lfac (hLf x hU.1 hU.2) L hL
  · have hsm := (I0.majN_G e l N Lfac (hLf 0 h0A h0B)).1
    have hx : 1 ≤ qForm (rootA ct σ i) x ∨ 1 ≤ qForm (rootB ct σ i) x :=
      (not_and_or.1 hU).imp not_lt.1 not_lt.1
    rw [SecA.pderivList_clipObs_eq_zero I0.rootA_psd I0.rootB_psd hsm L
      (lt_min (by omega) (by omega)) hx, abs_zero]
    have hML : 0 ≤ ML := by
      have := (hLf 0 h0A h0B).2 [] (by simp)
      simp only [List.length_nil, pow_zero, mul_one, List.map_nil, List.prod_nil] at this
      exact (abs_nonneg _).trans this
    have h1 : 0 ≤ (l.map fun t => |fc ct h σ i t|).prod := List.prod_nonneg fun a ha => by
      obtain ⟨t, -, rfl⟩ := List.mem_map.1 ha
      exact abs_nonneg _
    have h2 : 0 ≤ (L.map fun s => Real.sqrt (bd ct σ i s)).prod := List.prod_nonneg fun a ha => by
      obtain ⟨s, -, rfl⟩ := List.mem_map.1 ha
      exact Real.sqrt_nonneg _
    positivity

end Contact

end BiluLinial.Tight.SecB.WR
