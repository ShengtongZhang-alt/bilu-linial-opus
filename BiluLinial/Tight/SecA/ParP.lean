/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecA.Defs
public import BiluLinial.Tight.FloorLemma

/-!
# Source and parameter facts (node `A-PARP`)

AUDIT-A §1.2 (PAR′), refining source lines 67–68 ("`τ_ij ≤ τ_*`, `s ≤ 2 + C/d`,
`d a² s² ≤ 1 + C/d`, `c_ij ≤ C/d`"). In the structural regime `TRegime d p`:

* `p ≤ 2q/9`, `η₀ ≥ 3/q`, `a² ≤ 1/(4q)`;
* `s ≤ 2` (equivalent to `η₀ ≥ 2 τ_*`) and `d a² s² ≤ 1` (equivalent to
  `q² η₀ - 3q(1 - η₀) + (1 - η₀)² ≥ 0`, implied by `η₀ ≥ 3/q`);
* `1/d ≤ ε` (from `η₀ ≥ 3/q ≥ 2/d`), `ε ≤ 1/200`;
* for sources `y ∈ [0, s]^V` and a root `v`: `c_vi ≤ a² y_v y_i ≤ 1/d`,
  `L_v = a² y_v Σ_{i ∈ N} y_i ≤ 1`, `C_v = Σ_{i ∈ N} c_vi² ≤ 1/d`, `D_v = 1 + L_v - C_v ∈ [1, 2]`
  (from `c (1 + c) = a² y_v y_i`), and `L_v / D_v ≤ 51/100`.

`η₀ ≥ 3/q`: if `η₀ q < 3` then `η₀ ≤ 1/2`, so `q η₀² p = 4(1 - η₀) ≥ 2` and, with `p ≤ 2q/9`,
`q² η₀² ≥ 9`, a contradiction.
-/

@[expose] public section

namespace BiluLinial.Tight.SecA

open Matrix

variable {d p : ℕ}

/-- `p^8 ≤ d`, hence `p ≤ 2q/9`. -/
theorem p_le_two_q_div_nine (hR : TRegime d p) : (p : ℝ) ≤ 2 * qOf d / 9 := by
  have hp1 : (1 : ℝ) ≤ p := by
    have : (10 : ℝ) ^ 6 ≤ p := by exact_mod_cast hR.hp
    linarith
  have h17 : (p : ℝ) ^ 17 ≤ (d : ℝ) ^ 2 := by exact_mod_cast hR.hpd
  have h8 : (p : ℝ) ^ 8 ≤ d := by
    have : ((p : ℝ) ^ 8) ^ 2 ≤ (d : ℝ) ^ 2 :=
      calc ((p : ℝ) ^ 8) ^ 2 = (p : ℝ) ^ 16 := by ring
        _ ≤ (p : ℝ) ^ 17 := pow_le_pow_right₀ hp1 (by norm_num)
        _ ≤ _ := h17
    exact (pow_le_pow_iff_left₀ (by positivity) (Nat.cast_nonneg d) two_ne_zero).1 this
  have hp6 : (10 : ℝ) ^ 6 ≤ p := by exact_mod_cast hR.hp
  have h9 : 9 * (p : ℝ) ≤ (p : ℝ) ^ 8 := by
    have : (9 : ℝ) ≤ (p : ℝ) ^ 7 := by
      calc (9 : ℝ) ≤ p := by linarith
        _ ≤ (p : ℝ) ^ 7 := le_self_pow₀ hp1 (by norm_num)
    nlinarith
  rw [qOf]
  have hd := hR.ten_pow_six_le_d
  linarith

private theorem qOf_ge (hR : TRegime d p) : (10 : ℝ) ^ 6 - 1 ≤ qOf d := by
  have h := hR.ten_pow_six_le_d
  rw [qOf]
  linarith

/-- `η₀ ≥ 3/q`. -/
theorem three_div_le_η0Of (hR : TRegime d p) : 3 / qOf d ≤ η0Of d p := by
  have hq := hR.qOf_pos
  have hq6 := qOf_ge hR
  have he := hR.η0Of_eq
  have h0 := hR.η0Of_pos
  have hpq := p_le_two_q_div_nine hR
  have hp : (0 : ℝ) < p := by
    have : (10 : ℝ) ^ 6 ≤ p := by exact_mod_cast hR.hp
    linarith
  have hΔ : ΔOf p * p = 4 := by rw [ΔOf]; field_simp
  rw [div_le_iff₀ hq]
  by_contra h
  push Not at h
  have hη : η0Of d p ≤ 1 / 2 := by
    have : η0Of d p * qOf d ≤ 3 := h.le
    nlinarith
  have h2 : 2 ≤ qOf d * η0Of d p ^ 2 * p := by
    have : qOf d * η0Of d p ^ 2 * p = 4 * (1 - η0Of d p) := by
      rw [he]; linear_combination (1 - η0Of d p) * hΔ
    rw [this]; linarith
  have h3 : qOf d * η0Of d p ^ 2 * p ≤ qOf d * η0Of d p ^ 2 * (2 * qOf d / 9) :=
    mul_le_mul_of_nonneg_left hpq (by positivity)
  have h4 : (η0Of d p * qOf d) ^ 2 < 9 := by nlinarith [mul_pos h0 hq]
  have h5 : qOf d * η0Of d p ^ 2 * (2 * qOf d / 9) = 2 * (η0Of d p * qOf d) ^ 2 / 9 := by ring
  linarith

/-- `a² ≤ 1/(4q)`. -/
theorem aOf_sq_le (hR : TRegime d p) : aOf d p ^ 2 ≤ 1 / (4 * qOf d) := by
  rw [hR.aOf_sq]
  have hq := hR.qOf_pos
  exact one_div_le_one_div_of_le (by positivity) (by rw [RsqOf]; linarith [hR.ΔOf_pos])

/-- `s ≤ 2`. -/
theorem sOf_le_two (hR : TRegime d p) : sOf d p ≤ 2 := by
  have hq := hR.qOf_pos
  have hq6 := qOf_ge hR
  have h3 := three_div_le_η0Of hR
  have h1 := hR.η0Of_lt_one
  have hτ := hR.τsOf_lt_one
  have hτq := hR.qOf_mul_τsOf
  rw [sOf, hR.one_add_qOf_mul_τsOf, div_le_iff₀ (by linarith)]
  rw [div_le_iff₀ hq] at h3
  have h0 := hR.η0Of_pos
  have hτ' : 2 * τsOf d p * qOf d ≤ η0Of d p * qOf d := by nlinarith
  have : 2 * τsOf d p ≤ η0Of d p := le_of_mul_le_mul_right hτ' hq
  linarith

/-- `d a² s² ≤ 1`. -/
theorem d_mul_kappa_le_one (hR : TRegime d p) :
    (d : ℝ) * (aOf d p ^ 2 * sOf d p ^ 2) ≤ 1 := by
  have hq := hR.qOf_pos
  have h3 := three_div_le_η0Of hR
  have h0 := hR.η0Of_pos
  have hτ0 := hR.τsOf_pos
  have hτ1 := hR.τsOf_lt_one
  have hτq := hR.qOf_mul_τsOf
  have hne : (1 - τsOf d p) ≠ 0 := (sub_pos.2 hτ1).ne'
  have hx : 0 ≤ aOf d p ^ 2 * sOf d p * sOf d p :=
    mul_nonneg (mul_nonneg (sq_nonneg _) hR.sOf_pos.le) hR.sOf_pos.le
  have key := FloorIns.cRoot_mul_self_add hx
  rw [hR.cRoot_const] at key
  have hk : aOf d p ^ 2 * sOf d p ^ 2 = τsOf d p / (1 - τsOf d p) ^ 2 := by
    rw [sq (sOf d p), ← mul_assoc, ← key]
    field_simp
    ring
  have hd : (d : ℝ) = qOf d + 1 := by rw [qOf]; ring
  rw [div_le_iff₀ hq] at h3
  have h3τ' : 3 * τsOf d p * qOf d ≤ η0Of d p * qOf d := by nlinarith
  have h3τ : 3 * τsOf d p ≤ η0Of d p := le_of_mul_le_mul_right h3τ' hq
  rw [hk, hd, mul_div_assoc', div_le_one (pow_pos (sub_pos.2 hτ1) 2)]
  nlinarith

/-- `1/d ≤ ε`. -/
theorem inv_d_le_epsP (hR : TRegime d p) : 1 / (d : ℝ) ≤ epsP d p := by
  have hq := hR.qOf_pos
  have h3 := three_div_le_η0Of hR
  have hd : (d : ℝ) = qOf d + 1 := by rw [qOf]; ring
  have hε : epsP d p = η0Of d p / 2 := by rw [epsP, rOf]; ring
  rw [hε, hd, div_le_iff₀ (by linarith)]
  rw [div_le_iff₀ hq] at h3
  nlinarith

/-- `0 ≤ ε`. -/
theorem epsP_nonneg (hR : TRegime d p) : 0 ≤ epsP d p := by
  rw [epsP, rOf]; linarith [hR.η0Of_pos]

/-- `ε ≤ 1/200`. -/
theorem epsP_le (hR : TRegime d p) : epsP d p ≤ 1 / 200 := by
  have hq6 := qOf_ge hR
  have he := hR.η0Of_eq
  have h0 := hR.η0Of_pos
  have h1 := hR.η0Of_lt_one
  have hΔ := hR.ΔOf_le_two
  have hε : epsP d p = η0Of d p / 2 := by rw [epsP, rOf]; ring
  rw [hε]
  by_contra h
  push Not at h
  have h2 : 1 / 100 < η0Of d p := by linarith
  have e1 : ((10 : ℝ) ^ 6 - 1) * η0Of d p ^ 2 ≤ qOf d * η0Of d p ^ 2 :=
    mul_le_mul_of_nonneg_right hq6 (sq_nonneg _)
  have e2 : (1 / 100 : ℝ) ^ 2 < η0Of d p ^ 2 := pow_lt_pow_left₀ h2 (by norm_num) two_ne_zero
  have e3 : ΔOf p * (1 - η0Of d p) ≤ 2 := by nlinarith [hR.ΔOf_pos]
  nlinarith

section Graph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] in
/-- `c_ij ≤ a² y_i y_j ≤ 1/d` on the cube `[0, s]^V`. -/
theorem cEdge_le (hR : TRegime d p) {y : V → ℝ} (hy : InCube (sOf d p) y) (i j : V) :
    cEdge (aOf d p) y i j ≤ 1 / (d : ℝ) := by
  have hd : (0 : ℝ) < d := by have := hR.ten_pow_six_le_d; linarith
  have h0 : 0 ≤ aOf d p ^ 2 * y i * y j :=
    mul_nonneg (mul_nonneg (sq_nonneg _) (hy i).1) (hy j).1
  have h1 := FloorIns.cRoot_le h0
  have h2 := FloorIns.edge_le_kappa (a := aOf d p) hy i j
  have h3 := d_mul_kappa_le_one hR
  rw [le_div_iff₀ hd]
  calc cEdge (aOf d p) y i j * d ≤ aOf d p ^ 2 * sOf d p ^ 2 * d :=
        mul_le_mul_of_nonneg_right (h1.trans h2) hd.le
    _ ≤ 1 := by linarith

omit [DecidableEq V] in
/-- `L_v = a² y_v Σ_{i ∈ N} y_i ≤ 1` for maximum degree `≤ d`. -/
theorem Lsum_le_one (hR : TRegime d p) (hdeg : ∀ v, G.degree v ≤ d) {y : V → ℝ}
    (hy : InCube (sOf d p) y) (S : Finset V) (v : V) :
    aOf d p ^ 2 * y v * ∑ i ∈ nbhd G S v, y i ≤ 1 := by
  have hs := hR.sOf_pos
  have hcard : ((nbhd G S v).card : ℝ) ≤ d := by
    exact_mod_cast (FloorIns.card_nbhd_le G S v).trans (hdeg v)
  have hsum : ∑ i ∈ nbhd G S v, y i ≤ (nbhd G S v).card * sOf d p := by
    have := Finset.sum_le_card_nsmul (nbhd G S v) y (sOf d p) fun i _ => (hy i).2
    simpa [nsmul_eq_mul] using this
  have h3 := d_mul_kappa_le_one hR
  have hyv := hy v
  have hsum0 : 0 ≤ ∑ i ∈ nbhd G S v, y i := Finset.sum_nonneg fun i _ => (hy i).1
  calc aOf d p ^ 2 * y v * ∑ i ∈ nbhd G S v, y i
      ≤ aOf d p ^ 2 * sOf d p * ((nbhd G S v).card * sOf d p) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hyv.2 (sq_nonneg _)) hsum hsum0
        positivity
    _ ≤ aOf d p ^ 2 * sOf d p * (d * sOf d p) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_right hcard hs.le
    _ = d * (aOf d p ^ 2 * sOf d p ^ 2) := by ring
    _ ≤ 1 := h3

omit [Fintype V] [DecidableEq V] in
/-- `D_v = 1 + L_v - C_v` with `C_v = Σ_{i ∈ N} c_vi²` (from `c (1 + c) = a² y_v y_i`). -/
theorem diagD_eq_one_add_L_sub_C (a : ℝ) {y : V → ℝ} (hy : ∀ i, 0 ≤ y i) (S : Finset V)
    (v : V) :
    diagD G a y S v =
      1 + a ^ 2 * y v * ∑ i ∈ nbhd G S v, y i - ∑ i ∈ nbhd G S v, cEdge a y v i ^ 2 := by
  have h : ∀ i, cEdge a y v i = a ^ 2 * y v * y i - cEdge a y v i ^ 2 := fun i => by
    have := FloorIns.cRoot_mul_self_add
      (mul_nonneg (mul_nonneg (sq_nonneg a) (hy v)) (hy i))
    unfold cEdge
    linear_combination this
  rw [diagD, Finset.mul_sum, Finset.sum_congr rfl fun i _ => h i, Finset.sum_sub_distrib]
  ring

/-- `C_v = Σ_{i ∈ N} c_vi² ≤ 1/d`. -/
theorem Csum_le (hR : TRegime d p) (hdeg : ∀ v, G.degree v ≤ d) {y : V → ℝ}
    (hy : InCube (sOf d p) y) (S : Finset V) (v : V) :
    ∑ i ∈ nbhd G S v, cEdge (aOf d p) y v i ^ 2 ≤ 1 / (d : ℝ) := by
  have hd : (0 : ℝ) < d := by have := hR.ten_pow_six_le_d; linarith
  have hcard : ((nbhd G S v).card : ℝ) ≤ d := by
    exact_mod_cast (FloorIns.card_nbhd_le G S v).trans (hdeg v)
  have hc : ∀ i, cEdge (aOf d p) y v i ^ 2 ≤ (1 / (d : ℝ)) ^ 2 := fun i => by
    have h0 : 0 ≤ cEdge (aOf d p) y v i :=
      FloorIns.cRoot_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (hy v).1) (hy i).1)
    exact pow_le_pow_left₀ h0 (cEdge_le hR hy v i) 2
  calc ∑ i ∈ nbhd G S v, cEdge (aOf d p) y v i ^ 2
      ≤ (nbhd G S v).card * (1 / (d : ℝ)) ^ 2 := by
        have := Finset.sum_le_card_nsmul (nbhd G S v) _ _ fun i _ => hc i
        simpa [nsmul_eq_mul] using this
    _ ≤ d * (1 / (d : ℝ)) ^ 2 := mul_le_mul_of_nonneg_right hcard (sq_nonneg _)
    _ = 1 / (d : ℝ) := by field_simp

omit [DecidableEq V] in
/-- `D_v ≤ 2`. -/
theorem diagD_le_two (hR : TRegime d p) (hdeg : ∀ v, G.degree v ≤ d) {y : V → ℝ}
    (hy : InCube (sOf d p) y) (S : Finset V) (v : V) : diagD G (aOf d p) y S v ≤ 2 := by
  rw [diagD_eq_one_add_L_sub_C G _ (fun i => (hy i).1)]
  have h1 := Lsum_le_one G hR hdeg hy S v
  have h2 : 0 ≤ ∑ i ∈ nbhd G S v, cEdge (aOf d p) y v i ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  linarith

/-- `U₀ = L_v / D_v ≤ 51/100`. -/
theorem Lsum_div_diagD_le (hR : TRegime d p) (hdeg : ∀ v, G.degree v ≤ d)
    {y : V → ℝ} (hy : InCube (sOf d p) y) (S : Finset V) (v : V) :
    aOf d p ^ 2 * y v * (∑ i ∈ nbhd G S v, y i) / diagD G (aOf d p) y S v ≤ 51 / 100 := by
  have hD := FloorIns.one_le_diagD G (aOf d p) (fun i => (hy i).1) S v
  have hd : (10 : ℝ) ^ 6 ≤ d := hR.ten_pow_six_le_d
  have h1 := Lsum_le_one G hR hdeg hy S v
  have h2 := Csum_le G hR hdeg hy S v
  have he := diagD_eq_one_add_L_sub_C G (aOf d p) (fun i => (hy i).1) S v
  have hinv : 1 / (d : ℝ) ≤ 1 / 10 ^ 6 := one_div_le_one_div_of_le (by norm_num) hd
  rw [div_le_iff₀ (by linarith)]
  linarith

end Graph

end BiluLinial.Tight.SecA
