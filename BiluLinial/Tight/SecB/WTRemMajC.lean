/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecB.WTRemMaj

/-!
# Contact-level derivative majorants of the (WT5) observables (sub-node (R3) of TB.WT5r°)

`majN_G`: the prefactor `G = w₊^{s₊} w₋^{s₋} Π_t c_t ñ_t · L(x)` has a majorant at every interior
point with weights `λ_s = κ √b_s`, `κ = (1 + 2h)/min(1 - q_A(x₀), 1 - q_B(x₀))`.
`deriv_global`: `|∂^ν (clipObs G e₁ e₂ A B)(x)| ≤ 2 Π_t |c_t| M_L (8p)^{|ν|} Π_{s ∈ ν} √b_s` for every
`x` (zero off `{q_A, q_B < 1}`).
-/

@[expose] public section

namespace BiluLinial.Tight.SecB.WR

open Matrix SecA.CR SecA.StarCalc

section Contact

variable {d p : ℕ}

/-- `b_s = A_ss + B_ss`. -/
noncomputable def bd (ct : Contact.{u} d p) (σ : Config ct.V) (i : ct.V)
    (s : nbhd ct.G ct.S i) : ℝ :=
  rootA ct σ i s s + rootB ct σ i s s

/-- The weights `λ_s = κ √b_s`. -/
noncomputable def lamW (ct : Contact.{u} d p) (h : ℝ) (σ : Config ct.V) (i : ct.V)
    (x₀ : nbhd ct.G ct.S i → ℝ) (s : nbhd ct.G ct.S i) : ℝ :=
  (1 + 2 * h) / min (1 - qForm (rootA ct σ i) x₀) (1 - qForm (rootB ct σ i) x₀) *
    Real.sqrt (bd ct σ i s)

theorem cnt_shift_le {T : Type*} (l : List (T × Bool × Bool)) :
    cntK (fun t => t.2) (true, true) l + cntK (fun t => t.2) (false, true) l ≤ l.length := by
  induction l with
  | nil => simp [cntK]
  | cons t l ih =>
    rw [cntK_cons, cntK_cons, List.length_cons]
    split_ifs with h1 h2 h2
    · rw [h1] at h2
      simp at h2
    · omega
    · omega
    · omega

theorem sP_add_sM_le {T : Type*} (e : Bool) (l : List (T × Bool × Bool)) :
    sP e l + sM e l ≤ l.length + 4 := by
  have := cnt_shift_le l
  unfold sP sM
  cases e <;> simp <;> omega

/-- The interior setup shared by the majorant lemmas. -/
structure Interior (ct : Contact.{u} d p) (h : ℝ) (σ : Config ct.V) (i : ct.V)
    (x₀ : nbhd ct.G ct.S i → ℝ) : Prop where
  hh : 0 < h
  hi : i ∈ ct.S
  hw : wtCore ct.G p (aOf d p) ct.yp ct.ym σ ct.S i ≠ 0
  hA0 : qForm (rootA ct σ i) x₀ < 1
  hB0 : qForm (rootB ct σ i) x₀ < 1
  hy2 : ∀ b k, ct.ySrc b k ≤ 2

namespace Interior

variable {ct : Contact.{u} d p} {h : ℝ} {σ : Config ct.V} {i : ct.V}
  {x₀ : nbhd ct.G ct.S i → ℝ} (I : Interior ct h σ i x₀)
include I

theorem rootA_psd : (rootA ct σ i).PosSemidef :=
  SecA.rootMat_posSemidef ct.G (ySrc_nonneg ct true) (wtCore_pd ct I.hw true)

theorem rootB_psd : (rootB ct σ i).PosSemidef :=
  SecA.rootMat_posSemidef ct.G (ySrc_nonneg ct false) (wtCore_pd ct I.hw false)

theorem bd_nonneg (s : nbhd ct.G ct.S i) : 0 ≤ bd ct σ i s :=
  add_nonneg I.rootA_psd.diag_nonneg I.rootB_psd.diag_nonneg

theorem Xb_diag_le (b : Bool) (s : nbhd ct.G ct.S i) : (Xb ct b σ i) s s ≤ bd ct σ i s := by
  cases b
  · exact le_add_of_nonneg_left I.rootA_psd.diag_nonneg
  · exact le_add_of_nonneg_right I.rootB_psd.diag_nonneg

theorem Xb_lt (b : Bool) : qForm (Xb ct b σ i) x₀ < 1 := by
  cases b
  · exact I.hB0
  · exact I.hA0

theorem mu_pos : 0 < min (1 - qForm (rootA ct σ i) x₀) (1 - qForm (rootB ct σ i) x₀) :=
  lt_min (by linarith [I.hA0]) (by linarith [I.hB0])

theorem mu_le (b : Bool) :
    min (1 - qForm (rootA ct σ i) x₀) (1 - qForm (rootB ct σ i) x₀) ≤
      1 - qForm (Xb ct b σ i) x₀ := by
  cases b
  · exact min_le_right _ _
  · exact min_le_left _ _

theorem mu_le_one : min (1 - qForm (rootA ct σ i) x₀) (1 - qForm (rootB ct σ i) x₀) ≤ 1 :=
  (min_le_left _ _).trans (by linarith [qForm_nonneg I.rootA_psd x₀])

theorem one_le_kappa :
    1 ≤ (1 + 2 * h) / min (1 - qForm (rootA ct σ i) x₀) (1 - qForm (rootB ct σ i) x₀) := by
  rw [le_div_iff₀ I.mu_pos]
  linarith [I.mu_le_one, I.hh]

theorem lam_nonneg (s : nbhd ct.G ct.S i) : 0 ≤ lamW ct h σ i x₀ s :=
  mul_nonneg (by linarith [I.one_le_kappa]) (Real.sqrt_nonneg _)

/-- The clip of branch `b` with its exact value as scale. -/
theorem quadMaj_X (b : Bool) :
    QuadMaj 1 0 (-Xb ct b σ i) x₀ (1 - qForm (Xb ct b σ i) x₀) (lamW ct h σ i x₀) := by
  have hXp : (Xb ct b σ i).PosSemidef := by
    cases b
    · exact I.rootB_psd
    · exact I.rootA_psd
  refine quadMaj_one_sub_scaled hXp I.bd_nonneg (I.Xb_diag_le b) (I.Xb_lt b) I.one_le_kappa ?_
  have hμ := I.mu_pos
  have hle := I.mu_le b
  rw [div_mul_eq_mul_div, le_div_iff₀ hμ, one_mul]
  nlinarith [I.hh]

/-- The shifted clip of branch `b`: `κ (1 - q_{A_{b,h}}(x₀)) ≥ 1`, `δ_b/2 < 1 - q_{A_{b,h}}(x₀)`,
and its `QuadMaj` with exact scale. -/
theorem shift_facts (b : Bool) :
    1 ≤ (1 + 2 * h) / min (1 - qForm (rootA ct σ i) x₀) (1 - qForm (rootB ct σ i) x₀) *
        (1 - qForm (Ash ct h b σ i) x₀) ∧
      0 < dlt ct h b i ∧ dlt ct h b i / 2 < 1 - qForm (Ash ct h b σ i) x₀ ∧
      QuadMaj 1 0 (-Ash ct h b σ i) x₀ (1 - qForm (Ash ct h b σ i) x₀) (lamW ct h σ i x₀) := by
  have hM := wtCore_pd ct I.hw b
  have hy := ySrc_nonneg ct b
  obtain ⟨hδ, hδq, hlow, hle⟩ := Ash_facts ct I.hh b hM (I.hy2 b i) x₀ (I.Xb_lt b)
  have hAshp : (Ash ct h b σ i).PosSemidef := Az_posSemidef ct.G hy I.hh.le hM
  have hAshd : ∀ s, Ash ct h b σ i s s ≤ bd ct σ i s := fun s => by
    have := qForm_Az_le_root ct.G hy I.hh.le hM (Pi.single s 1)
    rw [qForm_single, qForm_single] at this
    exact this.trans (I.Xb_diag_le b s)
  have hq1 : qForm (Ash ct h b σ i) x₀ < 1 := lt_of_le_of_lt hle (I.Xb_lt b)
  have hμ := I.mu_pos
  have h2h : 0 < 1 + 2 * h := by linarith [I.hh]
  have hκA : 1 ≤ (1 + 2 * h) / min (1 - qForm (rootA ct σ i) x₀) (1 - qForm (rootB ct σ i) x₀) *
      (1 - qForm (Ash ct h b σ i) x₀) := by
    have h1 : min (1 - qForm (rootA ct σ i) x₀) (1 - qForm (rootB ct σ i) x₀) / (1 + 2 * h) ≤
        1 - qForm (Ash ct h b σ i) x₀ :=
      le_trans (div_le_div_of_nonneg_right (I.mu_le b) h2h.le) hlow
    rw [div_le_iff₀ h2h] at h1
    rw [div_mul_eq_mul_div, le_div_iff₀ hμ, one_mul]
    linarith
  exact ⟨hκA, hδ, by linarith,
    quadMaj_one_sub_scaled hAshp I.bd_nonneg hAshd hq1 I.one_le_kappa hκA⟩

theorem majN_wR (N : ℕ) (b : Bool) (k : ℕ) :
    MajN N x₀ (lamW ct h σ i x₀) ((1 - qForm (Ash ct h b σ i) x₀)⁻¹ ^ k) (4 * (k + N))
      (wR ct h b σ i k) := by
  obtain ⟨-, hδ, hδ2, hQ⟩ := I.shift_facts b
  exact majN_recip0 I.lam_nonneg hQ (quadFn_one_zero_neg _ _) hδ hδ2 k

theorem majN_factor (N : ℕ) (t : ct.V × Bool × Bool) :
    MajN N x₀ (lamW ct h σ i x₀) (|fc ct h σ i t| * 1) (0 + 2)
      (fun x => fc ct h σ i t * quadFn 1 0 (fN ct h σ i t) x) := by
  obtain ⟨k, b, sh⟩ := t
  have hM := wtCore_pd ct I.hw b
  have hy := ySrc_nonneg ct b
  have hz : (0 : ℝ) ≤ zOf h sh := by cases sh <;> simp [zOf, I.hh.le]
  have hneg : (-fN ct h σ i (k, b, sh)).PosSemidef := neg_nMat_posSemidef ct.G hy hz hM k
  have hbnd : ∀ y, qForm (-fN ct h σ i (k, b, sh)) y ≤ qForm (Xb ct b σ i) y := fun y =>
    (qForm_neg_nMat_bounds ct.G hy hz hM k y).2.trans (qForm_Az_le_root ct.G hy hz hM y)
  have hdg : ∀ s, (-fN ct h σ i (k, b, sh)) s s ≤ bd ct σ i s := fun s => by
    have := hbnd (Pi.single s 1)
    rw [qForm_single, qForm_single] at this
    exact this.trans (I.Xb_diag_le b s)
  have hx1 : qForm (-fN ct h σ i (k, b, sh)) x₀ < 1 := lt_of_le_of_lt (hbnd x₀) (I.Xb_lt b)
  have hQ := quadMaj_clip hneg hdg hx1
  rw [neg_neg] at hQ
  have hQ' := QuadMaj.mono_lam hQ zero_le_one (fun s => Real.sqrt_nonneg _)
    (fun s => le_mul_of_one_le_left (Real.sqrt_nonneg _) I.one_le_kappa)
  exact (majN_const N x₀ _ (fc ct h σ i (k, b, sh))).mul (majN_quadFn I.lam_nonneg hQ')

/-- **The prefactor majorant.** -/
theorem majN_G (e : Bool) (l : List (ct.V × Bool × Bool)) (N : ℕ)
    (Lfac : (nbhd ct.G ct.S i → ℝ) → ℝ) {ML : ℝ} (hLf : MajN N x₀ (lamW ct h σ i x₀) ML 2 Lfac) :
    MajN N x₀ (lamW ct h σ i x₀)
      ((1 - qForm (Ash ct h true σ i) x₀)⁻¹ ^ sP e l *
          (1 - qForm (Ash ct h false σ i) x₀)⁻¹ ^ sM e l *
        (l.map fun t => |fc ct h σ i t| * 1).prod * ML)
      (4 * ((sP e l : ℝ) + N) + 4 * ((sM e l : ℝ) + N) + l.length * (0 + 2) + 2)
      (fun x => wR ct h true σ i (sP e l) x * wR ct h false σ i (sM e l) x * Pl ct h σ i l x *
        Lfac x) := by
  have hPl := majN_list_prod (N := N) (x₀ := x₀) (lam := lamW ct h σ i x₀)
    (fun t x => fc ct h σ i t * quadFn 1 0 (fN ct h σ i t) x)
    (fun t => |fc ct h σ i t| * 1) (0 + 2) l (fun t _ => I.majN_factor N t)
  exact (((I.majN_wR N true (sP e l)).mul (I.majN_wR N false (sM e l))).mul hPl).mul hLf

end Interior

end Contact

end BiluLinial.Tight.SecB.WR
