/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecB.WTRemHder

/-!
# Own-core moments of the majorant constants (sub-node (R4) of TB.WT5r°)

With `X(σ) = 1 + Σ_{k ∈ R} ((K⁰₊)_kk + (K⁰₋)_kk)` (`R = N ∪ J ∪ {k_t}`, `|R| ≤ 2d + |l|`):
* `E_{ν_K} X^q ≤ (2(2|R| + 1)(1 + 2ε))^q` for `2q ≤ p` (`mom_X`, from (M3) `core_moment`);
* on the core support `m_Q, m_T ≤ C_m X^{|l|+3}` with
  `C_m = 128 · 2^{|l|} (R² + 1)(1/h + 4)/(h² d)` (`mQ_le`, `mT_le`);
* hence `E_{ν_K} m^n ≤ (C_m (2(2|R|+1)(1+2ε))^{|l|+3})^n` for `2(|l|+3) n ≤ p` (`mom_m`).
-/

@[expose] public section

namespace BiluLinial.Tight.SecB.WR

open Matrix

theorem prod_map_le_pow {T : Type*} (l : List T) (f : T → ℝ) {c : ℝ} (hf0 : ∀ t ∈ l, 0 ≤ f t)
    (hfc : ∀ t ∈ l, f t ≤ c) (hc : 0 ≤ c) : (l.map f).prod ≤ c ^ l.length := by
  induction l with
  | nil => simp
  | cons t l ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons, pow_succ]
    have h1 := ih (fun t' ht' => hf0 t' (List.mem_cons_of_mem _ ht'))
      (fun t' ht' => hfc t' (List.mem_cons_of_mem _ ht'))
    have h2 : 0 ≤ (l.map f).prod := List.prod_nonneg fun a ha => by
      obtain ⟨t', ht', rfl⟩ := List.mem_map.1 ha
      exact hf0 t' (List.mem_cons_of_mem _ ht')
    calc f t * (l.map f).prod ≤ c * c ^ l.length :=
          mul_le_mul (hfc t (List.mem_cons_self ..)) h1 h2 hc
      _ = c ^ l.length * c := by ring

section CapPt

variable {d p : ℕ} (cp : CapPoint.{u} d p)

/-- `X = 1 + Σ_{k ∈ R} ((K⁰₊)_kk + (K⁰₋)_kk)`. -/
noncomputable def Xv (v : cp.V) (R : Finset cp.V) (σ : Config cp.V) : ℝ :=
  1 + ∑ k ∈ R, ((precCore cp.G (aOf d p) 1 cp.yp σ cp.S v)⁻¹ k k +
    (precCore cp.G (aOf d p) (-1) cp.ym σ cp.S v)⁻¹ k k)

theorem coreE_one' (hR : RegA d p) {v : cp.V} (hv : v ∈ cp.S) :
    cp.coreE v (fun _ => (1 : ℝ)) = 1 := by
  unfold CapPoint.coreE BiluLinial.Tight.coreE
  simp only [mul_one]
  exact div_self (cp.ZwCore_pos hR hv).ne'

/-- `E_{ν_K} X^q ≤ (2(2|R|+1)(1+2ε))^q`. -/
theorem mom_X (hR : RegA d p) {v : cp.V} (hv : v ∈ cp.S) (R : Finset cp.V) {q : ℕ}
    (hq1 : 1 ≤ q) (hq : 2 * q ≤ p) :
    cp.coreE v (fun σ => Xv cp v R σ ^ q) ≤
      (2 * (2 * R.card + 1) * (1 + 2 * epsP d p)) ^ q := by
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  have hε := SecA.epsP_nonneg hR.treg
  set c := 1 + 2 * epsP d p with hc
  have hc1 : 1 ≤ c := by linarith
  set r : ℝ := (R.card : ℝ) with hr
  have hr0 : 0 ≤ r := Nat.cast_nonneg _
  set Kp : cp.V → Config cp.V → ℝ := fun k σ => (precCore cp.G (aOf d p) 1 cp.yp σ cp.S v)⁻¹ k k
  set Km : cp.V → Config cp.V → ℝ :=
    fun k σ => (precCore cp.G (aOf d p) (-1) cp.ym σ cp.S v)⁻¹ k k
  -- pointwise convexity on the core support
  have hpt : ∀ σ, wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v ≠ 0 →
      Xv cp v R σ ^ (q' + 1) ≤ 2 ^ q' * (1 + r ^ q' * 2 ^ q' *
        ∑ k ∈ R, (Kp k σ ^ (q' + 1) + Km k σ ^ (q' + 1))) := by
    intro σ hσ
    obtain ⟨h1, h2⟩ := SecC.posDef_of_wtCore_ne_zero cp.G hσ
    have hKp : ∀ k, 0 ≤ Kp k σ := fun k => h1.inv.diag_pos.le
    have hKm : ∀ k, 0 ≤ Km k σ := fun k => h2.inv.diag_pos.le
    have hY : 0 ≤ ∑ k ∈ R, (Kp k σ + Km k σ) :=
      Finset.sum_nonneg fun k _ => add_nonneg (hKp k) (hKm k)
    have e1 := add_pow_le zero_le_one hY (q' + 1)
    simp only [one_pow, Nat.add_sub_cancel] at e1
    have e2 := pow_sum_le_card_mul_sum_pow (s := R) (f := fun k => Kp k σ + Km k σ)
      (fun k _ => add_nonneg (hKp k) (hKm k)) q'
    have e3 : ∀ k ∈ R, (Kp k σ + Km k σ) ^ (q' + 1) ≤
        2 ^ q' * (Kp k σ ^ (q' + 1) + Km k σ ^ (q' + 1)) := fun k _ => by
      have := add_pow_le (hKp k) (hKm k) (q' + 1)
      simpa using this
    have e4 : ∑ k ∈ R, (Kp k σ + Km k σ) ^ (q' + 1) ≤
        2 ^ q' * ∑ k ∈ R, (Kp k σ ^ (q' + 1) + Km k σ ^ (q' + 1)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum e3
    have hXv : Xv cp v R σ = 1 + ∑ k ∈ R, (Kp k σ + Km k σ) := rfl
    rw [hXv]
    calc (1 + ∑ k ∈ R, (Kp k σ + Km k σ)) ^ (q' + 1)
        ≤ 2 ^ q' * (1 + (∑ k ∈ R, (Kp k σ + Km k σ)) ^ (q' + 1)) := e1
      _ ≤ 2 ^ q' * (1 + r ^ q' * (2 ^ q' *
            ∑ k ∈ R, (Kp k σ ^ (q' + 1) + Km k σ ^ (q' + 1)))) := by
          gcongr
          exact e2.trans (mul_le_mul_of_nonneg_left e4 (by positivity))
      _ = _ := by ring
  have hmom : ∀ k, cp.coreE v (Kp k ^ (q' + 1)) ≤ c ^ (q' + 1) ∧
      cp.coreE v (Km k ^ (q' + 1)) ≤ c ^ (q' + 1) := fun k =>
    cp.core_moment hR hv k hq1 hq
  calc cp.coreE v (fun σ => Xv cp v R σ ^ (q' + 1))
      ≤ cp.coreE v (fun σ => 2 ^ q' * (1 + r ^ q' * 2 ^ q' *
          ∑ k ∈ R, (Kp k σ ^ (q' + 1) + Km k σ ^ (q' + 1)))) := SecC.coreE_mono cp.G hpt
    _ = 2 ^ q' * (1 + r ^ q' * 2 ^ q' *
          ∑ k ∈ R, (cp.coreE v (Kp k ^ (q' + 1)) + cp.coreE v (Km k ^ (q' + 1)))) := by
        rw [cp.coreE_fconst_mul, cp.coreE_fadd, coreE_one' cp hR hv, cp.coreE_fconst_mul,
          cp.coreE_fsum]
        congr 3
        refine Finset.sum_congr rfl fun k _ => ?_
        exact cp.coreE_fadd v _ _
    _ ≤ 2 ^ q' * (1 + r ^ q' * 2 ^ q' * ∑ k ∈ R, (c ^ (q' + 1) + c ^ (q' + 1))) := by
        gcongr with k hk
        · exact (hmom k).1
        · exact (hmom k).2
    _ ≤ (2 * (2 * r + 1) * c) ^ (q' + 1) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        have hcq : 1 ≤ c ^ (q' + 1) := one_le_pow₀ hc1
        have h2r : (2 * r) ^ (q' + 1) ≤ (2 * r + 1) ^ (q' + 1) :=
          pow_le_pow_left₀ (by positivity) (by linarith) _
        have h1r : 1 ≤ (2 * r + 1) ^ (q' + 1) := one_le_pow₀ (by linarith)
        have e : r ^ q' * 2 ^ q' * (r * (c ^ (q' + 1) + c ^ (q' + 1))) =
            (2 * r) ^ (q' + 1) * c ^ (q' + 1) := by ring
        rw [e]
        calc 2 ^ q' * (1 + (2 * r) ^ (q' + 1) * c ^ (q' + 1))
            ≤ 2 ^ q' * ((2 * r + 1) ^ (q' + 1) * c ^ (q' + 1) +
                (2 * r + 1) ^ (q' + 1) * c ^ (q' + 1)) := by
              gcongr
              · nlinarith
          _ = (2 * (2 * r + 1) * c) ^ (q' + 1) := by
              rw [mul_pow, mul_pow, pow_succ (2 : ℝ) q']
              ring

/-- `E_{ν_K} m^n ≤ (C (2(2|R|+1)(1+2ε))^{e})^n` when `0 ≤ m ≤ C X^e` on the core support. -/
theorem mom_m (hR : RegA d p) {v : cp.V} (hv : v ∈ cp.S) (R : Finset cp.V) {C : ℝ} (hC : 0 ≤ C)
    (ex : ℕ) (m : Config cp.V → ℝ) (hm0 : ∀ σ, 0 ≤ m σ)
    (hm : ∀ σ, wtCore cp.G p (aOf d p) cp.yp cp.ym σ cp.S v ≠ 0 → m σ ≤ C * Xv cp v R σ ^ ex)
    {n : ℕ} (hn1 : 1 ≤ n) (hex : 1 ≤ ex) (hn : 2 * (ex * n) ≤ p) :
    cp.coreE v (fun σ => m σ ^ n) ≤
      (C * (2 * (2 * R.card + 1) * (1 + 2 * epsP d p)) ^ ex) ^ n := by
  have hq1 : 1 ≤ ex * n := Nat.one_le_iff_ne_zero.2 (by positivity)
  calc cp.coreE v (fun σ => m σ ^ n)
      ≤ cp.coreE v (fun σ => C ^ n * Xv cp v R σ ^ (ex * n)) := by
        refine SecC.coreE_mono cp.G fun σ hσ => ?_
        rw [pow_mul, ← mul_pow]
        exact pow_le_pow_left₀ (hm0 σ) (hm σ hσ) n
    _ = C ^ n * cp.coreE v (fun σ => Xv cp v R σ ^ (ex * n)) := cp.coreE_fconst_mul v _ _
    _ ≤ C ^ n * (2 * (2 * R.card + 1) * (1 + 2 * epsP d p)) ^ (ex * n) :=
        mul_le_mul_of_nonneg_left (mom_X cp hR hv R hq1 hn) (by positivity)
    _ = _ := by rw [pow_mul, ← mul_pow]

end CapPt

section Contact

variable {d p : ℕ}

/-- `R = N ∪ J ∪ {k_t}`. -/
noncomputable def Rset (ct : Contact.{u} d p) (i : ct.V) (l : List (ct.V × Bool × Bool)) :
    Finset ct.V :=
  ct.N ∪ nbhd ct.G ct.S i ∪ (l.map Prod.fst).toFinset

/-- The constant `C_m = 128 · 2^{|l|} (R² + 1)(1/h + 4)/(h² d)`. -/
noncomputable def Cm (h : ℝ) (d p n : ℕ) : ℝ :=
  128 * 2 ^ n * (RsqOf d p + 1) * (1 / h + 4) / (h ^ 2 * d)

theorem nbhd_card_le {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {d : ℕ} (hdeg : ∀ v, G.degree v ≤ d) (S : Finset V) (v : V) :
    (nbhd G S v).card ≤ d := by
  have h1 : (nbhd G S v).card ≤ G.degree v := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    refine Finset.card_le_card fun x hx => ?_
    rw [SimpleGraph.mem_neighborFinset]
    simp only [nbhd, Finset.mem_filter] at hx
    exact hx.2
  exact h1.trans (hdeg v)

theorem Rset_card_le (ct : Contact.{u} d p) (i : ct.V) (l : List (ct.V × Bool × Bool)) :
    (Rset ct i l).card ≤ 2 * d + l.length := by
  unfold Rset
  have h1 := nbhd_card_le ct.ctx.deg ct.S ct.v
  have h2 := nbhd_card_le ct.ctx.deg ct.S i
  have h3 : (l.map Prod.fst).toFinset.card ≤ l.length :=
    (List.toFinset_card_le _).trans (by simp)
  calc (ct.N ∪ nbhd ct.G ct.S i ∪ (l.map Prod.fst).toFinset).card
      ≤ (ct.N ∪ nbhd ct.G ct.S i).card + (l.map Prod.fst).toFinset.card := Finset.card_union_le _ _
    _ ≤ ct.N.card + (nbhd ct.G ct.S i).card + (l.map Prod.fst).toFinset.card := by
        gcongr
        exact Finset.card_union_le _ _
    _ ≤ d + d + l.length := by
        unfold Contact.N at *
        omega
    _ = 2 * d + l.length := by ring

theorem Cm_nonneg {h : ℝ} (hh : 0 < h) (hR : TRegime d p) (n : ℕ) : 0 ≤ Cm h d p n := by
  have := hR.RsqOf_pos
  unfold Cm
  positivity

/-- Facts on the core support used by both constants. -/
theorem supp_facts (hR : TRegime d p) (ct : Contact.{u} d p) {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1)
    {i : ct.V} (l : List (ct.V × Bool × Bool)) {σ : Config ct.V}
    (hw : wtCore ct.G p (aOf d p) ct.yp ct.ym σ ct.S i ≠ 0) :
    1 ≤ Xv ct.toCapPoint i (Rset ct i l) σ ∧
      (l.map fun t => |fc ct h σ i t|).prod ≤ (2 * Xv ct.toCapPoint i (Rset ct i l) σ) ^ l.length ∧
      (∀ b, cE ct h b σ i ^ 2 ≤ 4) ∧
      cL ct h σ i ≤ 2 / (h ^ 2 * d) * (1 / h + 4) * Xv ct.toCapPoint i (Rset ct i l) σ ^ 2 ∧
      ∑ l' : nbhd ct.G ct.S i, ct.yp l' * (precCore ct.G (aOf d p) 1 ct.yp σ ct.S i)⁻¹ l' l' ≤
        2 * Xv ct.toCapPoint i (Rset ct i l) σ := by
  obtain ⟨h1, h2⟩ := SecC.posDef_of_wtCore_ne_zero ct.G hw
  have hd : (0 : ℝ) < d := Nat.cast_pos.2 (by have := hR.ten_pow_six_le_nat; omega)
  set X := Xv ct.toCapPoint i (Rset ct i l) σ with hXdef
  set Kp : ct.V → ℝ := fun k => (precCore ct.G (aOf d p) 1 ct.yp σ ct.S i)⁻¹ k k
  set Km : ct.V → ℝ := fun k => (precCore ct.G (aOf d p) (-1) ct.ym σ ct.S i)⁻¹ k k
  have hKp : ∀ k, 0 < Kp k := fun k => h1.inv.diag_pos
  have hKm : ∀ k, 0 < Km k := fun k => h2.inv.diag_pos
  have hXe : X = 1 + ∑ k ∈ Rset ct i l, (Kp k + Km k) := rfl
  have hsum0 : 0 ≤ ∑ k ∈ Rset ct i l, (Kp k + Km k) :=
    Finset.sum_nonneg fun k _ => (add_pos (hKp k) (hKm k)).le
  have hX1 : 1 ≤ X := by rw [hXe]; linarith
  have hKle : ∀ k ∈ Rset ct i l, Kp k ≤ X ∧ Km k ≤ X := fun k hk => by
    have hs := Finset.single_le_sum (f := fun k => Kp k + Km k)
      (fun k _ => (add_pos (hKp k) (hKm k)).le) hk
    constructor <;> linarith [hKp k, hKm k]
  have hy : ∀ b k, 0 ≤ ct.ySrc b k := ySrc_nonneg ct
  have hy2 := ySrc_le_two hR ct
  have hsubR : ∀ s : Finset ct.V, s ⊆ Rset ct i l →
      ∑ k ∈ s, Kp k ≤ X := fun s hs => by
    have : ∑ k ∈ s, Kp k ≤ ∑ k ∈ Rset ct i l, (Kp k + Km k) :=
      (Finset.sum_le_sum fun k _ => le_add_of_nonneg_right (hKm k).le).trans
        (Finset.sum_le_sum_of_subset_of_nonneg hs fun k _ _ => (add_pos (hKp k) (hKm k)).le)
    linarith
  refine ⟨hX1, ?_, ?_, ?_, ?_⟩
  · refine prod_map_le_pow l _ (fun t _ => abs_nonneg _) (fun t ht => ?_) (by linarith)
    obtain ⟨k, b, sh⟩ := t
    have hM := wtCore_pd ct hw b
    have hz : (0 : ℝ) ≤ zOf h sh := by cases sh <;> simp [zOf, hh.le]
    have hkR : k ∈ Rset ct i l := by
      unfold Rset
      refine Finset.mem_union_right _ (List.mem_toFinset.2 (List.mem_map.2 ⟨(k, b, sh), ht, rfl⟩))
    simp only [fc, cVal]
    split_ifs with hk
    · have hD1 : 1 ≤ diagD ct.G (aOf d p) (ct.ySrc b) ct.S i + zOf h sh * ct.ySrc b i := by
        have := FloorIns.one_le_diagD ct.G (aOf d p) (hy b) ct.S i
        nlinarith [hy b i]
      rw [abs_of_nonneg (div_nonneg (hy b i) (by linarith))]
      calc ct.ySrc b i / (diagD ct.G (aOf d p) (ct.ySrc b) ct.S i + zOf h sh * ct.ySrc b i)
          ≤ ct.ySrc b i := div_le_self (hy b i) hD1
        _ ≤ 2 := hy2 b i
        _ ≤ 2 * X := by linarith
    · have hKz := (Kz_posDef ct.G (hy b) hz hM).diag_pos (i := k)
      have hKz0 := Kz_diag_le ct.G (hy b) hz hM k
      have hKb : (precCore ct.G (aOf d p) (tau b) (ct.ySrc b) σ ct.S i)⁻¹ k k ≤ X := by
        cases b
        · exact (hKle k hkR).2
        · exact (hKle k hkR).1
      rw [abs_of_nonneg (mul_nonneg (hy b k) hKz.le)]
      exact mul_le_mul (hy2 b k) (hKz0.trans hKb) hKz.le (by norm_num)
  · intro b
    have hD1 : 1 ≤ diagD ct.G (aOf d p) (ct.ySrc b) ct.S i + h * ct.ySrc b i := by
      have := FloorIns.one_le_diagD ct.G (aOf d p) (hy b) ct.S i
      nlinarith [hy b i]
    have h0 : 0 ≤ cE ct h b σ i := by
      unfold cE cVal
      rw [if_pos rfl]
      exact div_nonneg (hy b i) (by linarith)
    have h2' : cE ct h b σ i ≤ 2 := by
      unfold cE cVal
      rw [if_pos rfl]
      exact (div_le_self (hy b i) hD1).trans (hy2 b i)
    nlinarith
  · have hS : ∑ k ∈ ct.N, ((precCore ct.G (aOf d p) 1 ct.yp σ ct.S i)⁻¹ k k) ^ 2 ≤ X ^ 2 := by
      have hNR : ct.N ⊆ Rset ct i l := by
        unfold Rset
        exact Finset.subset_union_left.trans Finset.subset_union_left
      calc ∑ k ∈ ct.N, ((precCore ct.G (aOf d p) 1 ct.yp σ ct.S i)⁻¹ k k) ^ 2
          ≤ ∑ k ∈ ct.N, Kp k * X := Finset.sum_le_sum fun k hk => by
            rw [sq]
            exact mul_le_mul_of_nonneg_left (hKle k (hNR hk)).1 (hKp k).le
        _ = (∑ k ∈ ct.N, Kp k) * X := by rw [Finset.sum_mul]
        _ ≤ X * X := mul_le_mul_of_nonneg_right (hsubR _ hNR) (by linarith)
        _ = X ^ 2 := by ring
    unfold cL
    have hX2 : 1 ≤ X ^ 2 := one_le_pow₀ hX1
    have hih : 0 ≤ 1 / h := by positivity
    calc 1 / h ^ 2 * (2 / d) *
          (1 / h + 4 * ∑ k ∈ ct.N, ((precCore ct.G (aOf d p) 1 ct.yp σ ct.S i)⁻¹ k k) ^ 2)
        ≤ 1 / h ^ 2 * (2 / d) * (1 / h + 4 * X ^ 2) := by gcongr
      _ ≤ 1 / h ^ 2 * (2 / d) * ((1 / h + 4) * X ^ 2) := by
          gcongr
          nlinarith
      _ = 2 / (h ^ 2 * d) * (1 / h + 4) * X ^ 2 := by field_simp
  · have hJR : nbhd ct.G ct.S i ⊆ Rset ct i l := by
      unfold Rset
      exact Finset.subset_union_right.trans Finset.subset_union_left
    calc ∑ l' : nbhd ct.G ct.S i, ct.yp l' * (precCore ct.G (aOf d p) 1 ct.yp σ ct.S i)⁻¹ l' l'
        ≤ ∑ l' : nbhd ct.G ct.S i, 2 * Kp l' := Finset.sum_le_sum fun l' _ =>
          mul_le_mul_of_nonneg_right (hy2 true l') (hKp l').le
      _ = 2 * ∑ k ∈ nbhd ct.G ct.S i, Kp k := by
          rw [← Finset.mul_sum, Finset.sum_coe_sort (nbhd ct.G ct.S i) Kp]
      _ ≤ 2 * X := by linarith [hsubR _ hJR]

theorem mQ_le (hR : TRegime d p) (ct : Contact.{u} d p) {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1)
    (e : Bool) {i : ct.V} (l : List (ct.V × Bool × Bool)) {σ : Config ct.V}
    (hw : wtCore ct.G p (aOf d p) ct.yp ct.ym σ ct.S i ≠ 0) :
    mQ ct h e i l σ ≤ Cm h d p l.length * Xv ct.toCapPoint i (Rset ct i l) σ ^ (l.length + 3) := by
  obtain ⟨hX1, hprod, hcE, hcL, -⟩ := supp_facts hR ct hh hh1 l hw
  set X := Xv ct.toCapPoint i (Rset ct i l) σ
  have hd : (0 : ℝ) < d := Nat.cast_pos.2 (by have := hR.ten_pow_six_le_nat; omega)
  have hRs := hR.RsqOf_pos
  have hcHat : cHat ct h σ i ≤ 2 * RsqOf d p * cL ct h σ i := by
    unfold cHat
    rw [hR.aOf_sq, div_div_eq_mul_div, div_one]
    have hy2i : ct.yp i ≤ 2 := ySrc_le_two hR ct true i
    have hcL0 := cL_nonneg ct hh σ i
    nlinarith [mul_le_mul_of_nonneg_left hy2i (mul_nonneg hcL0 hRs.le)]
  have hcL0 := cL_nonneg ct hh σ i
  have hcH0 := cHat_nonneg ct hh σ i
  have hP0 : 0 ≤ (l.map fun t => |fc ct h σ i t|).prod := List.prod_nonneg fun a ha => by
    obtain ⟨t, -, rfl⟩ := List.mem_map.1 ha
    exact abs_nonneg _
  simp only [mQ, if_pos hw]
  have hX0 : 0 ≤ X := by linarith
  have hih : 0 ≤ 1 / h := by positivity
  calc 2 * (l.map fun t => |fc ct h σ i t|).prod * (cE ct h e σ i ^ 2 * cHat ct h σ i)
      ≤ 2 * (2 * X) ^ l.length * (4 * (2 * RsqOf d p *
          (2 / (h ^ 2 * d) * (1 / h + 4) * X ^ 2))) := by
        gcongr
        · exact hcE e
        · exact hcHat.trans (mul_le_mul_of_nonneg_left hcL (by positivity))
    _ = 32 * 2 ^ l.length * RsqOf d p * (1 / h + 4) / (h ^ 2 * d) * X ^ (l.length + 2) := by
        rw [mul_pow]
        field_simp
        ring
    _ ≤ Cm h d p l.length * X ^ (l.length + 3) := by
        unfold Cm
        have hXp : X ^ (l.length + 2) ≤ X ^ (l.length + 3) := pow_le_pow_right₀ hX1 (by omega)
        have hc : 32 * 2 ^ l.length * RsqOf d p * (1 / h + 4) / (h ^ 2 * d) ≤
            128 * 2 ^ l.length * (RsqOf d p + 1) * (1 / h + 4) / (h ^ 2 * d) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          have h2l : (0 : ℝ) ≤ 2 ^ l.length := by positivity
          have h14 : (0 : ℝ) ≤ 1 / h + 4 := by positivity
          have : 32 * 2 ^ l.length * RsqOf d p ≤ 128 * 2 ^ l.length * (RsqOf d p + 1) := by
            nlinarith
          exact mul_le_mul_of_nonneg_right this h14
        calc 32 * 2 ^ l.length * RsqOf d p * (1 / h + 4) / (h ^ 2 * d) * X ^ (l.length + 2)
            ≤ 128 * 2 ^ l.length * (RsqOf d p + 1) * (1 / h + 4) / (h ^ 2 * d) *
                X ^ (l.length + 3) := mul_le_mul hc hXp (by positivity) (by positivity)
          _ = _ := rfl

theorem mT_le (hR : TRegime d p) (ct : Contact.{u} d p) {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1)
    (e dir : Bool) {i : ct.V} (l : List (ct.V × Bool × Bool)) {σ : Config ct.V}
    (hw : wtCore ct.G p (aOf d p) ct.yp ct.ym σ ct.S i ≠ 0) :
    mT ct h e dir i l σ ≤
      Cm h d p l.length * Xv ct.toCapPoint i (Rset ct i l) σ ^ (l.length + 3) := by
  obtain ⟨hX1, hprod, hcE, hcL, hJ⟩ := supp_facts hR ct hh hh1 l hw
  set X := Xv ct.toCapPoint i (Rset ct i l) σ
  have hd : (0 : ℝ) < d := Nat.cast_pos.2 (by have := hR.ten_pow_six_le_nat; omega)
  have hRs := hR.RsqOf_pos
  have hMp : (precCore ct.G (aOf d p) 1 ct.yp σ ct.S i).PosDef := wtCore_pd ct hw true
  have hyp : ∀ k, 0 ≤ ct.yp k := fun k => (ct.ctx.hyp k).1
  have hy2 : ∀ k, ct.yp k ≤ 2 := fun k => ySrc_le_two hR ct true k
  have hP2 : ∀ k, precCore ct.G (aOf d p) 1 ct.yp σ ct.S i k k ≤ 2 :=
    fun k => precCore_diag_le_two hR ct (yp_inCube hR ct) σ i k
  obtain ⟨htr0, htr⟩ := env_trace ct hd hh e dir σ hMp (wtCore_pd ct hw e) (ySrc_nonneg ct e)
    hyp hy2 hP2
  have hcL0 := cL_nonneg ct hh σ i
  have hP0 : 0 ≤ (l.map fun t => |fc ct h σ i t|).prod := List.prod_nonneg fun a ha => by
    obtain ⟨t, -, rfl⟩ := List.mem_map.1 ha
    exact abs_nonneg _
  have htr' : (kerL ct h e dir i σ).trace ≤ cL ct h σ i * (2 * X) :=
    htr.trans (mul_le_mul_of_nonneg_left hJ hcL0)
  have habs : |cE ct h e σ i ^ 2 * (cE ct h true σ i ^ 2 * (kerL ct h e dir i σ).trace)| ≤
      4 * (4 * (cL ct h σ i * (2 * X))) := by
    rw [abs_of_nonneg (by positivity)]
    have := hcE e
    have := hcE true
    gcongr
  simp only [mT, if_pos hw]
  have hX0 : 0 ≤ X := by linarith
  have hih : 0 ≤ 1 / h := by positivity
  calc 2 * (l.map fun t => |fc ct h σ i t|).prod *
        |cE ct h e σ i ^ 2 * (cE ct h true σ i ^ 2 * (kerL ct h e dir i σ).trace)|
      ≤ 2 * (2 * X) ^ l.length * (4 * (4 * ((2 / (h ^ 2 * d) * (1 / h + 4) * X ^ 2) *
          (2 * X)))) := by
        gcongr
        exact habs.trans (by gcongr)
    _ = 128 * 2 ^ l.length * (1 / h + 4) / (h ^ 2 * d) * X ^ (l.length + 3) := by
        rw [mul_pow]
        field_simp
        ring
    _ ≤ Cm h d p l.length * X ^ (l.length + 3) := by
        unfold Cm
        have h0 : 0 ≤ 128 * 2 ^ l.length * (1 / h + 4) / (h ^ 2 * d) * X ^ (l.length + 3) := by
          positivity
        calc 128 * 2 ^ l.length * (1 / h + 4) / (h ^ 2 * d) * X ^ (l.length + 3)
            ≤ (RsqOf d p + 1) *
                (128 * 2 ^ l.length * (1 / h + 4) / (h ^ 2 * d) * X ^ (l.length + 3)) :=
              le_mul_of_one_le_left h0 (by linarith)
          _ = _ := by ring

end Contact

end BiluLinial.Tight.SecB.WR
