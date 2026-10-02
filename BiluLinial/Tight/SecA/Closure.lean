/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecA.Shift

/-!
# The scalar closure and (C2) (nodes `A-SCALAR`, `A-THETA`, `A-C2`)

Source lines 600–623; AUDIT-A §2.15 (gaps A10, A11).

* `A-SCALAR`: for every shift `z > 0` with `dz ≥ 1` and `θ` the largest shifted deficit
  (`DefZMax`), `θ² ≤ C {z + p(θ + b₀)/(dz) + p⁵(θ + b₀)/d + p²/d + p⁹/d² + e^{-p}}`. Proof at a
  maximizing `(v, +)` (the minus case by the swap symmetry): Jensen on `A-C5d` gives
  `m_v⁻¹ ≤ D_v + z y_v - D_v E q_{M_z}(ξ)` (normalized),
  `E q_{M_z} = E tr M_z - E(tr M_z - q_{M_z})`,
  `D_v tr M_z = a² y_v Σ_{i ∈ N} C_{z,ii} = a² y_v Σ y_i m_i - a² y_v Σ (X_{z,ii} - C_{z,ii})`;
  with `m_v = 1 - θ`, `m_i ≥ 1 - θ`, `D_v = 1 + L_v - C_v`:
  `θ²/(1-θ) ≤ (L_v - 1)θ - C_v + y_v z + D_v E(tr M_z - q_{M_z}) + a² y_v D_v E(h_v - h_{z,v})/z`;
  then `L_v ≤ 1`, `C_v ≥ 0`, `y_v ≤ 2`, `D_v ≤ 2`, (C6) and `E(h_v - h_{z,v}) ≤ ε + θ` (the cap).
* `A-THETA`: at `z = u²`, `θ ≤ C u` (`u = (p/d)^{1/3}`): REG gives `p/(dz) = u`, `b₀ ≤ 3u`,
  `p⁵/d ≤ u`, `p²/d, p⁹/d², e^{-p} ≤ u²`, so `θ² ≤ K(2uθ + 10u²)`, `θ ≤ (2K + 5)u`.
* `A-C2` (C2): `E(h^±_i - 1)² + (1 - E h^±_i) + a² Σ_{i ∼ v} E(G^±_vi)² + E_H Θ ≤ C u` (each term),
  from `A-THETA` (`ρ ≤ θ`), `A-SM2`, `A-ROW`, `A-C3b`.
-/

@[expose] public section

universe u

namespace BiluLinial.Tight

open Matrix

namespace CapPoint

variable {d p : ℕ} (cp : CapPoint.{u} d p)

theorem E_swap (f : Config cp.V → ℝ) : cp.E f = cp.swap.E (fun σ => f (-σ)) :=
  lawE_swap cp.G p (aOf d p) cp.yp cp.ym cp.S f

theorem _root_.BiluLinial.Tight.SecA.hzN_neg_branch {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (a z : ℝ) (y : V → ℝ) (σ : Config V)
    (S : Finset V) (i : V) : hzN G a (-1) z y σ S i = hzN G a 1 z y (-σ) S i := by
  unfold hzN
  rw [precN_neg G a 1 y σ S]

theorem E_hzm_eq_swap (z : ℝ) (i : cp.V) :
    cp.E (fun σ => cp.hzm z σ i) = cp.swap.E (fun σ => cp.swap.hzp z σ i) := by
  show lawE cp.G p (aOf d p) cp.yp cp.ym cp.S
      (fun σ => hzN cp.G (aOf d p) (-1) z cp.ym σ cp.S i) =
    lawE cp.G p (aOf d p) cp.ym cp.yp cp.S (fun σ => hzN cp.G (aOf d p) 1 z cp.ym σ cp.S i)
  rw [lawE_swap cp.G p (aOf d p) cp.yp cp.ym cp.S]
  refine congrArg _ (funext fun σ => ?_)
  rw [SecA.hzN_neg_branch, neg_neg]

theorem E_hzp_eq_swap (z : ℝ) (i : cp.V) :
    cp.E (fun σ => cp.hzp z σ i) = cp.swap.E (fun σ => cp.swap.hzm z σ i) := by
  show lawE cp.G p (aOf d p) cp.yp cp.ym cp.S
      (fun σ => hzN cp.G (aOf d p) 1 z cp.yp σ cp.S i) =
    lawE cp.G p (aOf d p) cp.ym cp.yp cp.S (fun σ => hzN cp.G (aOf d p) (-1) z cp.yp σ cp.S i)
  rw [lawE_swap cp.G p (aOf d p) cp.yp cp.ym cp.S]
  refine congrArg _ (funext fun σ => ?_)
  rw [SecA.hzN_neg_branch]

theorem DefZLe.swap {z θ : ℝ} (h : cp.DefZLe z θ) : cp.swap.DefZLe z θ := by
  intro i hi
  obtain ⟨h1, h2⟩ := h i hi
  have e1 := cp.E_hzp_eq_swap z i
  have e2 := cp.E_hzm_eq_swap z i
  exact ⟨by linarith, by linarith⟩

end CapPoint

namespace SecA

section ScalarHelpers

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Physical shifted diagonal `X_{z,ii} = y_i h_{z,i}`. -/
theorem shiftP_self {a τ z : ℝ} {y : V → ℝ} {σ : Config V} {S : Finset V} {i : V}
    (hy : 0 ≤ y i) : shiftP G a τ z y σ S i i = y i * hzN G a τ z y σ S i := by
  rw [shiftP, hzN, mul_comm (Real.sqrt (y i)), mul_assoc, Real.mul_self_sqrt hy, mul_comm]

/-- Jensen for `x ↦ 1/x` (Cauchy–Schwarz form): `E X · E[1/X] ≥ 1` for `X > 0` on the support. -/
theorem one_le_lawE_mul_lawE_inv {p : ℕ} {a : ℝ} {yp ym : V → ℝ} {S : Finset V}
    (hZ : 0 < Zw G p a yp ym S) {X : Config V → ℝ}
    (hX : ∀ σ, wt G p a yp ym σ S ≠ 0 → 0 < X σ) :
    1 ≤ lawE G p a yp ym S X * lawE G p a yp ym S (fun σ => 1 / X σ) := by
  have hcs := wavg_mul_sq_le (w := fun σ => wt G p a yp ym σ S) (fun σ => wt_nonneg G σ)
    (fun σ => Real.sqrt (X σ)) (fun σ => Real.sqrt (1 / X σ))
  rw [← lawE_eq_wavg, ← lawE_eq_wavg, ← lawE_eq_wavg] at hcs
  have e1 : lawE G p a yp ym S (fun σ => Real.sqrt (X σ) * Real.sqrt (1 / X σ)) = 1 := by
    rw [lawE_congr G (g := fun _ => 1) fun σ hσ => by
      rw [← Real.sqrt_mul (hX σ hσ).le, mul_one_div_cancel (hX σ hσ).ne', Real.sqrt_one]]
    exact lawE_one G hZ
  have e2 : lawE G p a yp ym S (fun σ => Real.sqrt (X σ) ^ 2) = lawE G p a yp ym S X :=
    lawE_congr G fun σ hσ => Real.sq_sqrt (hX σ hσ).le
  have e3 : lawE G p a yp ym S (fun σ => Real.sqrt (1 / X σ) ^ 2) =
      lawE G p a yp ym S (fun σ => 1 / X σ) :=
    lawE_congr G fun σ hσ => Real.sq_sqrt (by have := hX σ hσ; positivity)
  rw [e1, e2, e3, one_pow] at hcs
  exact hcs

end ScalarHelpers

/-- The real algebra of `A-SCALAR` (source lines 603–611): Jensen `1 ≤ m E[1/h]`, the root Schur
identity in expectation, the trace correction, the neighbour deficits and the cap give
`θ² ≤ (1-θ)(E' - C_v) ≤ (2K₆+2)(z + X)`. -/
theorem scalar_alg {D L Cv θ Ei Eq T B EW SY Sy a2yv z yv ε Ehv m K₆ X : ℝ}
    (hJ : 1 ≤ m * Ei) (hEi : Ei = D * (1 - Eq) + z * yv) (hEq : Eq = T - B)
    (hDT : D * T = a2yv * SY - a2yv * EW) (hEW : EW ≤ D / z * (Ehv - m))
    (hSY : (1 - θ) * Sy ≤ SY) (hLdef : L = a2yv * Sy) (hDe : D = 1 + L - Cv)
    (hcap : Ehv ≤ 1 + ε) (hm : m = 1 - θ) (hEi0 : 0 ≤ Ei) (ha2yv : 0 ≤ a2yv) (hCv : 0 ≤ Cv)
    (hL1 : L ≤ 1) (hD1 : 1 ≤ D) (hD2 : D ≤ 2) (hθ0 : 0 ≤ θ) (hz : 0 < z)
    (hfirst : a2yv * (D / z * (ε + θ)) ≤ 2 * X) (hB : B ≤ K₆ * X) (hX0 : 0 ≤ X)
    (hK₆ : 0 ≤ K₆) (hyv : yv ≤ 2) :
    θ ^ 2 ≤ (2 * K₆ + 2) * (z + X) := by
  have hDz : 0 ≤ D / z := div_nonneg (by linarith) hz.le
  have h1 : a2yv * EW ≤ a2yv * (D / z * (ε + θ)) := by
    refine mul_le_mul_of_nonneg_left (hEW.trans ?_) ha2yv
    exact mul_le_mul_of_nonneg_left (by linarith) hDz
  have h2 : (1 - θ) * L ≤ a2yv * SY := by
    rw [hLdef]
    have := mul_le_mul_of_nonneg_left hSY ha2yv
    have e : (1 - θ) * (a2yv * Sy) = a2yv * ((1 - θ) * Sy) := by ring
    rw [e]; exact this
  have hEi2 : Ei ≤ 1 - Cv + θ * L + (a2yv * (D / z * (ε + θ)) + D * B + z * yv) := by
    have e : Ei = D - (a2yv * SY - a2yv * EW) + D * B + z * yv := by
      rw [hEi, hEq, ← hDT]; ring
    have e2 : (1 - θ) * L = L - θ * L := by ring
    rw [e]
    linarith
  have hm0 : 0 < m := by
    by_contra hc
    push Not at hc
    have := mul_nonpos_of_nonpos_of_nonneg hc hEi0
    linarith
  have hθ1 : θ ≤ 1 := by linarith
  set E' := a2yv * (D / z * (ε + θ)) + D * B + z * yv with hE'
  have hkey : 1 ≤ (1 - θ) * (1 - Cv + θ * L + E') := by
    rw [← hm]; exact hJ.trans (mul_le_mul_of_nonneg_left hEi2 hm0.le)
  have h3 : θ * θ ≤ θ * (1 - L + θ * L) := by
    refine mul_le_mul_of_nonneg_left ?_ hθ0
    have h := mul_nonneg (sub_nonneg.2 hL1) (sub_nonneg.2 hθ1)
    nlinarith
  have h4 : θ * (1 - L + θ * L) ≤ (1 - θ) * E' := by
    have h := mul_nonneg (sub_nonneg.2 hθ1) hCv
    nlinarith
  have hDB : D * B ≤ 2 * (K₆ * X) := by
    rcases le_total 0 B with h | h
    · calc D * B ≤ 2 * B := mul_le_mul_of_nonneg_right hD2 h
        _ ≤ 2 * (K₆ * X) := by linarith
    · have h' := mul_nonpos_of_nonneg_of_nonpos (by linarith : (0 : ℝ) ≤ D) h
      have := mul_nonneg hK₆ hX0
      linarith
  have hzy : z * yv ≤ z * 2 := mul_le_mul_of_nonneg_left hyv hz.le
  have hE'b : E' ≤ (2 * K₆ + 2) * (z + X) := by
    have e : (2 * K₆ + 2) * (z + X) = 2 * (K₆ * z) + 2 * (K₆ * X) + 2 * z + 2 * X := by ring
    have := mul_nonneg hK₆ hz.le
    rw [e, hE']
    linarith
  have hR0 : 0 ≤ (2 * K₆ + 2) * (z + X) := by positivity
  have h5 : (1 - θ) * E' ≤ (2 * K₆ + 2) * (z + X) := by
    rcases le_total 0 E' with h | h
    · have := mul_nonneg hθ0 h
      have e : (1 - θ) * E' = E' - θ * E' := by ring
      linarith
    · have := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 hθ1) h
      linarith
  calc θ ^ 2 = θ * θ := sq θ
    _ ≤ θ * (1 - L + θ * L) := h3
    _ ≤ (1 - θ) * E' := h4
    _ ≤ (2 * K₆ + 2) * (z + X) := h5

/-- The plus case of `A-SCALAR`, at a vertex `v` realizing the largest shifted deficit `θ`, given
the bias bound `E(tr M_z - q_{M_z}) ≤ K₆ X` and `p(θ + b₀)/(dz) ≤ X`. -/
theorem scalar_plus {d p : ℕ} (hR : RegA d p) (cp : CapPoint.{u} d p) {z : ℝ} (hz : 0 < z)
    (hdz : 1 ≤ (d : ℝ) * z) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : cp.DefZLe z θ) {v : cp.V}
    (hv : v ∈ cp.S) (heq : 1 - cp.E (fun σ => cp.hzp z σ v) = θ) {K₆ X : ℝ} (hK₆ : 0 ≤ K₆)
    (hX0 : 0 ≤ X) (hXp : (p : ℝ) * (θ + b0Of d p) / (d * z) ≤ X)
    (hB : cp.E (fun σ => (cp.Mz z σ v).trace - qForm (cp.Mz z σ v) (cp.xi σ v)) ≤ K₆ * X) :
    θ ^ 2 ≤ (2 * K₆ + 2) * (z + X) := by
  have hZ := cp.Zw_pos hR
  have hy0 := cp.yp_nonneg
  have hyc := cp.inCube_yp hR
  have hPD : ∀ σ, wt cp.G p (aOf d p) cp.yp cp.ym σ cp.S ≠ 0 →
      (precN cp.G (aOf d p) 1 cp.yp σ cp.S).PosDef := by
    intro σ hσ
    by_contra hc
    unfold wt at hσ
    exact hσ (by simp [hc])
  have hD1 : 1 ≤ diagD cp.G (aOf d p) cp.yp cp.S v :=
    FloorIns.one_le_diagD cp.G (aOf d p) hy0 cp.S v
  have hD0 : diagD cp.G (aOf d p) cp.yp cp.S v ≠ 0 := by linarith
  -- Jensen
  have hJ := one_le_lawE_mul_lawE_inv cp.G hZ (X := fun σ => cp.hzp z σ v)
    fun σ hσ => hzN_pos cp.G hz.le hy0 (hPD σ hσ) v
  -- `E[1/h_{z,v}] = D (1 - E q) + z y_v`
  have hEi : cp.E (fun σ => 1 / cp.hzp z σ v) =
      diagD cp.G (aOf d p) cp.yp cp.S v *
        (1 - cp.E (fun σ => qForm (cp.Mz z σ v) (cp.xi σ v))) + z * cp.yp v := by
    unfold CapPoint.E
    rw [lawE_congr cp.G (g := fun σ => (diagD cp.G (aOf d p) cp.yp cp.S v + z * cp.yp v) * 1 -
      diagD cp.G (aOf d p) cp.yp cp.S v * qForm (cp.Mz z σ v) (cp.xi σ v)) fun σ hσ => by
        rw [CapPoint.hzp, inv_hzN_root cp.G (by norm_num) hz.le hy0 hv (hPD σ hσ)]
        have hqq : qForm (cp.Mz z σ v) (cp.xi σ v) =
            qForm (rootMzG cp.G (aOf d p) 1 z cp.yp σ cp.S v) (rootSigns cp.G σ cp.S v) := rfl
        rw [hqq]
        ring]
    rw [lawE_sub, lawE_const_mul, lawE_const_mul, lawE_one cp.G hZ]
    ring
  have hEq : cp.E (fun σ => qForm (cp.Mz z σ v) (cp.xi σ v)) =
      cp.E (fun σ => (cp.Mz z σ v).trace) -
        cp.E (fun σ => (cp.Mz z σ v).trace - qForm (cp.Mz z σ v) (cp.xi σ v)) := by
    unfold CapPoint.E; rw [lawE_sub]; ring
  -- `D tr M_z = a² y_v (Σ y_i h_{z,i} - W)`
  have htr : ∀ σ, diagD cp.G (aOf d p) cp.yp cp.S v * (cp.Mz z σ v).trace =
      aOf d p ^ 2 * cp.yp v * (∑ i ∈ nbhd cp.G cp.S v, cp.yp i * cp.hzp z σ i) -
        aOf d p ^ 2 * cp.yp v * (∑ i ∈ nbhd cp.G cp.S v,
          (shiftP cp.G (aOf d p) 1 z cp.yp σ cp.S i i -
            coreShift cp.G (aOf d p) 1 z cp.yp σ cp.S v i i)) := by
    intro σ
    have e : (cp.Mz z σ v).trace = aOf d p ^ 2 * cp.yp v /
        diagD cp.G (aOf d p) cp.yp cp.S v *
          ∑ i ∈ nbhd cp.G cp.S v, coreShift cp.G (aOf d p) 1 z cp.yp σ cp.S v i i := by
      rw [← Finset.sum_coe_sort (nbhd cp.G cp.S v), Finset.mul_sum]
      rfl
    rw [e, ← mul_assoc,
      mul_div_assoc', mul_comm (diagD cp.G (aOf d p) cp.yp cp.S v) (aOf d p ^ 2 * cp.yp v),
      mul_div_assoc, div_self hD0, mul_one, ← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [shiftP_self cp.G (hy0 i), CapPoint.hzp]
    ring
  have hDT : diagD cp.G (aOf d p) cp.yp cp.S v * cp.E (fun σ => (cp.Mz z σ v).trace) =
      aOf d p ^ 2 * cp.yp v * (∑ i ∈ nbhd cp.G cp.S v, cp.yp i * cp.E (fun σ => cp.hzp z σ i)) -
        aOf d p ^ 2 * cp.yp v * cp.E (fun σ => ∑ i ∈ nbhd cp.G cp.S v,
          (shiftP cp.G (aOf d p) 1 z cp.yp σ cp.S i i -
            coreShift cp.G (aOf d p) 1 z cp.yp σ cp.S v i i)) := by
    unfold CapPoint.E
    rw [← lawE_const_mul, funext htr, lawE_sub, lawE_const_mul, lawE_const_mul, lawE_sum]
    congr 2
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [lawE_const_mul]
  -- the trace correction (C5(iv))
  have hEW : cp.E (fun σ => ∑ i ∈ nbhd cp.G cp.S v,
      (shiftP cp.G (aOf d p) 1 z cp.yp σ cp.S i i -
        coreShift cp.G (aOf d p) 1 z cp.yp σ cp.S v i i)) ≤
      diagD cp.G (aOf d p) cp.yp cp.S v / z *
        (cp.E (fun σ => cp.hp σ v) - cp.E (fun σ => cp.hzp z σ v)) := by
    have h1 := lawE_le_of_supp cp.G (p := p) (a := aOf d p) (yp := cp.yp) (ym := cp.ym)
      (S := cp.S) (f := fun σ => ∑ i ∈ nbhd cp.G cp.S v,
        (shiftP cp.G (aOf d p) 1 z cp.yp σ cp.S i i -
          coreShift cp.G (aOf d p) 1 z cp.yp σ cp.S v i i))
      (g := fun σ => diagD cp.G (aOf d p) cp.yp cp.S v / z * (cp.hp σ v - cp.hzp z σ v))
      fun σ hσ => by
        have := sum_shift_sub_core_le cp.G (by norm_num) hz hy0 hv (hPD σ hσ)
        rw [div_mul_eq_mul_div]
        exact this
    unfold CapPoint.E
    rw [lawE_const_mul, lawE_sub] at h1
    exact h1
  -- neighbour deficits
  have hSY : (1 - θ) * ∑ i ∈ nbhd cp.G cp.S v, cp.yp i ≤
      ∑ i ∈ nbhd cp.G cp.S v, cp.yp i * cp.E (fun σ => cp.hzp z σ i) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    have hiS : i ∈ cp.S := (Finset.mem_filter.1 hi).1
    have := (hθ i hiS).1
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (by linarith) (hy0 i)
  have hcap : cp.E (fun σ => cp.hp σ v) ≤ 1 + epsP d p := by
    have := (cp.h_mean_le hv).1
    have hr : rOf d p = 1 + epsP d p := by rw [epsP]; ring
    linarith
  have hEi0 : 0 ≤ cp.E (fun σ => 1 / cp.hzp z σ v) :=
    lawE_nonneg cp.G fun σ hσ => (one_div_pos.2 (hzN_pos cp.G hz.le hy0 (hPD σ hσ) v)).le
  -- the first error term
  have hs2 := sOf_le_two hR.treg
  have hyv2 : cp.yp v ≤ 2 := (hyc v).2.trans hs2
  have hD2 := diagD_le_two cp.G hR.treg cp.ctx.deg hyc cp.S v
  have ha2 := aOf_sq_le hR.treg
  have hq := hR.treg.qOf_pos
  have hd := hR.d_pos
  have hdq : (d : ℝ) ≤ 2 * qOf d := by
    have := hR.treg.ten_pow_six_le_d; rw [qOf]; linarith
  have hε0 := epsP_nonneg hR.treg
  have hεb : epsP d p ≤ b0Of d p := by
    rw [b0Of]
    have : 0 ≤ (p : ℝ) ^ 4 / d := by positivity
    have : 0 ≤ 1 / (d : ℝ) := by positivity
    linarith
  have hp1 : (1 : ℝ) ≤ p := hR.one_le_p
  have hb0 := hR.b0Of_pos
  have hfirst : aOf d p ^ 2 * cp.yp v * (diagD cp.G (aOf d p) cp.yp cp.S v / z *
      (epsP d p + θ)) ≤ 2 * X := by
    have hA1 : aOf d p ^ 2 * cp.yp v * diagD cp.G (aOf d p) cp.yp cp.S v ≤ 2 / d := by
      have h4a : 4 * aOf d p ^ 2 ≤ 2 / d := by
        have : 4 * aOf d p ^ 2 ≤ 1 / qOf d := by
          have := mul_le_mul_of_nonneg_left ha2 (by norm_num : (0 : ℝ) ≤ 4)
          rwa [show 4 * (1 / (4 * qOf d)) = 1 / qOf d by field_simp] at this
        refine this.trans ?_
        rw [div_le_div_iff₀ hq hd]
        linarith
      have hyD : cp.yp v * diagD cp.G (aOf d p) cp.yp cp.S v ≤ 4 := by nlinarith [hy0 v]
      nlinarith [sq_nonneg (aOf d p), mul_le_mul_of_nonneg_left hyD (sq_nonneg (aOf d p))]
    have ht0 : 0 ≤ (epsP d p + θ) / z := by positivity
    have e : aOf d p ^ 2 * cp.yp v * (diagD cp.G (aOf d p) cp.yp cp.S v / z *
        (epsP d p + θ)) = aOf d p ^ 2 * cp.yp v * diagD cp.G (aOf d p) cp.yp cp.S v *
          ((epsP d p + θ) / z) := by ring
    rw [e]
    have h2 : 2 / (d : ℝ) * ((epsP d p + θ) / z) ≤ 2 * ((p : ℝ) * (θ + b0Of d p) / (d * z)) := by
      rw [show 2 / (d : ℝ) * ((epsP d p + θ) / z) = 2 * ((epsP d p + θ) / (d * z)) by
        field_simp]
      refine mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right ?_ (by positivity))
        (by norm_num)
      nlinarith
    calc _ ≤ 2 / (d : ℝ) * ((epsP d p + θ) / z) := mul_le_mul_of_nonneg_right hA1 ht0
      _ ≤ 2 * ((p : ℝ) * (θ + b0Of d p) / (d * z)) := h2
      _ ≤ 2 * X := by linarith
  exact scalar_alg hJ hEi hEq hDT hEW hSY rfl
    (diagD_eq_one_add_L_sub_C cp.G (aOf d p) hy0 cp.S v) hcap
    (by have h := heq; unfold CapPoint.E at h; linarith) hEi0
    (mul_nonneg (sq_nonneg _) (hy0 v)) (Finset.sum_nonneg fun i _ => sq_nonneg _)
    (Lsum_le_one cp.G hR.treg cp.ctx.deg hyc cp.S v) hD1 hD2 hθ0 hz hfirst hB hX0 hK₆ hyv2

/-- `A-SCALAR`: the scalar inequality for every admissible shift (also used at `z = h`). -/
theorem scalar_ineq : ∃ C : ℝ, 0 < C ∧ ∀ d p : ℕ, RegA d p → ∀ cp : CapPoint.{u} d p,
    ∀ z : ℝ, 0 < z → 1 ≤ (d : ℝ) * z → ∀ θ : ℝ, cp.DefZMax z θ →
      θ ^ 2 ≤ C * (z + (p : ℝ) * (θ + b0Of d p) / (d * z) + (p : ℝ) ^ 5 * (θ + b0Of d p) / d +
        (p : ℝ) ^ 2 / d + (p : ℝ) ^ 9 / (d : ℝ) ^ 2 + Real.exp (-(p : ℝ))) := by
  obtain ⟨K₆, hK₆, h6⟩ := bias_C6.{u}
  refine ⟨2 * K₆ + 2, by linarith, fun d p hR cp z hz hdz θ hθ => ?_⟩
  obtain ⟨hθ0, hle, hcases⟩ := hθ
  have hd := hR.d_pos
  have hb := hR.b0Of_pos
  set X := (p : ℝ) * (θ + b0Of d p) / (d * z) + (p : ℝ) ^ 5 * (θ + b0Of d p) / d +
    (p : ℝ) ^ 2 / d + (p : ℝ) ^ 9 / (d : ℝ) ^ 2 + Real.exp (-(p : ℝ)) with hXdef
  have hX0 : 0 ≤ X := by positivity
  have hXp : (p : ℝ) * (θ + b0Of d p) / (d * z) ≤ X := by
    have : 0 ≤ (p : ℝ) ^ 5 * (θ + b0Of d p) / d + (p : ℝ) ^ 2 / d +
      (p : ℝ) ^ 9 / (d : ℝ) ^ 2 + Real.exp (-(p : ℝ)) := by positivity
    rw [hXdef]; linarith
  have hgoal : (2 * K₆ + 2) * (z + X) = (2 * K₆ + 2) * (z + (p : ℝ) * (θ + b0Of d p) / (d * z) +
      (p : ℝ) ^ 5 * (θ + b0Of d p) / d + (p : ℝ) ^ 2 / d + (p : ℝ) ^ 9 / (d : ℝ) ^ 2 +
      Real.exp (-(p : ℝ))) := by
    rw [hXdef]; ring
  rcases hcases with h0 | ⟨v, hv, hpl | hmi⟩
  · have hθ2 : θ ^ 2 = 0 := by rw [h0]; ring
    rw [hθ2, ← hgoal]
    positivity
  · rw [← hgoal]
    exact scalar_plus hR cp hz hdz hθ0 hle hv hpl hK₆.le hX0 hXp
      (h6 d p hR cp z hz hdz θ hθ0 hle v hv)
  · rw [← hgoal]
    have hle' := CapPoint.DefZLe.swap cp hle
    have hpl' : 1 - cp.swap.E (fun σ => cp.swap.hzp z σ v) = θ := by
      rw [← cp.E_hzm_eq_swap]; exact hmi
    exact scalar_plus hR cp.swap hz hdz hθ0 hle' hv hpl' hK₆.le hX0 hXp
      (h6 d p hR cp.swap z hz hdz θ hθ0 hle' v hv)

end SecA

/-- Every capped point has a largest shifted deficit. -/
theorem CapPoint.exists_defZMax {d p : ℕ} (cp : CapPoint.{u} d p) (z : ℝ) :
    ∃ θ, cp.DefZMax z θ := by
  set f : cp.V → ℝ := fun i =>
    max (1 - cp.E (fun σ => cp.hzp z σ i)) (1 - cp.E (fun σ => cp.hzm z σ i)) with hf
  rcases cp.S.eq_empty_or_nonempty with hS | hS
  · exact ⟨0, le_rfl, fun i hi => by simp [hS] at hi, Or.inl rfl⟩
  set m := cp.S.sup' hS f with hm
  refine ⟨max m 0, le_max_right _ _, fun i hi => ?_, ?_⟩
  · have h := Finset.le_sup' f hi
    rw [← hm] at h
    exact ⟨(le_max_left _ _).trans (h.trans (le_max_left _ _)),
      (le_max_right _ _).trans (h.trans (le_max_left _ _))⟩
  · rcases le_total m 0 with h0 | h0
    · exact Or.inl (max_eq_right h0)
    · right
      obtain ⟨i, hi, hfi⟩ := Finset.exists_mem_eq_sup' hS f
      refine ⟨i, hi, ?_⟩
      rw [max_eq_left h0, hm, hfi]
      rcases max_choice (1 - cp.E (fun σ => cp.hzp z σ i))
          (1 - cp.E (fun σ => cp.hzm z σ i)) with h | h
      · exact Or.inl h.symm
      · exact Or.inr h.symm

namespace SecA

/-- `A-THETA`: the shifted deficits at `z = u²` are `O(u)`. -/
theorem theta_bound : ∃ C : ℝ, 0 < C ∧ ∀ d p : ℕ, RegA d p → ∀ cp : CapPoint.{u} d p,
    cp.DefZLe (uOf d p ^ 2) (C * uOf d p) := by
  obtain ⟨K, hK, hS⟩ := scalar_ineq.{u}
  refine ⟨2 * K + 5, by linarith, fun d p hR cp => ?_⟩
  have hu : 0 < uOf d p := hR.uOf_pos
  have hd := hR.d_pos
  have hz : 0 < uOf d p ^ 2 := by positivity
  obtain ⟨θ, hθ⟩ := cp.exists_defZMax (uOf d p ^ 2)
  have h := hS d p hR cp (uOf d p ^ 2) hz hR.one_le_d_mul_u_sq θ hθ
  have hθ0 : 0 ≤ θ := hθ.1
  have hb0 : 0 < b0Of d p := hR.b0Of_pos
  have hpd : (p : ℝ) = d * uOf d p ^ 3 := by rw [uOf_pow_three]; field_simp
  have e1 : (p : ℝ) * (θ + b0Of d p) / (d * uOf d p ^ 2) = uOf d p * (θ + b0Of d p) := by
    rw [hpd]; field_simp
  have e2 : (p : ℝ) ^ 5 * (θ + b0Of d p) / d ≤ uOf d p * (θ + b0Of d p) := by
    rw [mul_div_right_comm]
    exact mul_le_mul_of_nonneg_right hR.p5_div_le_u (by positivity)
  have h3 := hR.p2_div_le_u_sq
  have h4 := hR.p9_div_le_u_sq
  have h5 := hR.exp_neg_p_le_u_sq
  have h6 := hR.b0Of_le
  have hθ2 : θ ^ 2 ≤ K * (2 * uOf d p * θ + 10 * uOf d p ^ 2) := by
    refine h.trans (mul_le_mul_of_nonneg_left ?_ hK.le)
    rw [e1]
    nlinarith
  have hθle : θ ≤ (2 * K + 5) * uOf d p := by
    by_contra hc
    push Not at hc
    have hθp : 0 < θ := lt_of_le_of_lt (by positivity) hc
    have h7 : (2 * K + 5) * uOf d p * θ < θ * θ := mul_lt_mul_of_pos_right hc hθp
    have h8 : 5 * uOf d p * ((2 * K + 5) * uOf d p) ≤ 5 * uOf d p * θ :=
      mul_le_mul_of_nonneg_left hc.le (by positivity)
    nlinarith
  intro i hi
  obtain ⟨h1, h2⟩ := hθ.2.1 i hi
  exact ⟨h1.trans hθle, h2.trans hθle⟩

/-- `A-C2` (C2): the concentration bounds, each `≤ C (p/d)^{1/3}`. -/
theorem concentration_C2 : ∃ C : ℝ, 0 < C ∧ ∀ d p : ℕ, RegA d p → ∀ cp : CapPoint.{u} d p,
    (∀ i ∈ cp.S,
      cp.E (fun σ => (cp.hp σ i - 1) ^ 2) ≤ C * uOf d p ∧
      cp.E (fun σ => (cp.hm σ i - 1) ^ 2) ≤ C * uOf d p ∧
      1 - cp.E (fun σ => cp.hp σ i) ≤ C * uOf d p ∧
      1 - cp.E (fun σ => cp.hm σ i) ≤ C * uOf d p) ∧
    (∀ v ∈ cp.S,
      aOf d p ^ 2 * ∑ i ∈ cp.N v, cp.E (fun σ => cp.gp σ v i ^ 2) ≤ C * uOf d p ∧
      aOf d p ^ 2 * ∑ i ∈ cp.N v, cp.E (fun σ => cp.gm σ v i ^ 2) ≤ C * uOf d p ∧
      cp.E (fun σ => cp.Theta σ v) ≤ C * uOf d p) := by
  obtain ⟨Ct, hCt, hT⟩ := theta_bound.{u}
  obtain ⟨Cr, hCr, hRow⟩ := row_bound.{u}
  obtain ⟨Cb, hCb, hB⟩ := preclosure_C3b.{u}
  refine ⟨5 + 2 * Ct + (Cr + Cb) * (Ct + 3), by positivity, fun d p hR cp => ?_⟩
  have hu : 0 < uOf d p := hR.uOf_pos
  have hρ : cp.DefLe (Ct * uOf d p) :=
    CapPoint.DefZLe.defLe cp hR (sq_nonneg _) (hT d p hR cp)
  have hρ0 : 0 ≤ Ct * uOf d p := by positivity
  have hb := hR.b0Of_le
  have hε := hR.epsP_le_u
  have hρb : Ct * uOf d p + b0Of d p ≤ (Ct + 3) * uOf d p := by linarith
  have hk1 : Cr * (Ct * uOf d p + b0Of d p) ≤
      (5 + 2 * Ct + (Cr + Cb) * (Ct + 3)) * uOf d p := by
    have := mul_le_mul_of_nonneg_left hρb hCr.le
    nlinarith [mul_pos hCb (by positivity : (0 : ℝ) < (Ct + 3) * uOf d p)]
  have hk2 : Cb * (Ct * uOf d p + b0Of d p) ≤
      (5 + 2 * Ct + (Cr + Cb) * (Ct + 3)) * uOf d p := by
    have := mul_le_mul_of_nonneg_left hρb hCb.le
    nlinarith [mul_pos hCr (by positivity : (0 : ℝ) < (Ct + 3) * uOf d p)]
  have hk3 : 5 * epsP d p + 2 * (Ct * uOf d p) ≤
      (5 + 2 * Ct + (Cr + Cb) * (Ct + 3)) * uOf d p := by
    nlinarith [mul_pos (by positivity : (0 : ℝ) < Cr + Cb) (by positivity :
      (0 : ℝ) < (Ct + 3) * uOf d p)]
  have hk4 : Ct * uOf d p ≤ (5 + 2 * Ct + (Cr + Cb) * (Ct + 3)) * uOf d p := by
    nlinarith [mul_pos (by positivity : (0 : ℝ) < Cr + Cb) (by positivity :
      (0 : ℝ) < (Ct + 3) * uOf d p)]
  refine ⟨fun i hi => ?_, fun v hv => ?_⟩
  · obtain ⟨s1, s2⟩ := second_moment hR cp hρ hi
    obtain ⟨d1, d2⟩ := hρ i hi
    exact ⟨s1.trans hk3, s2.trans hk3, d1.trans hk4, d2.trans hk4⟩
  · obtain ⟨r1, r2⟩ := hRow d p hR cp _ hρ0 hρ v hv
    exact ⟨r1.trans hk1, r2.trans hk1, (hB d p hR cp _ hρ0 hρ v hv).trans hk2⟩

end SecA

end BiluLinial.Tight
