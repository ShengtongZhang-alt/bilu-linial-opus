/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.Contact.Leaves
public import BiluLinial.Tight.SecB.Export

/-!
# Export-based leaves of the contact estimate (Section 1.5)

The leaves of Section 1.5 that apply an input of Sections 1.2–1.4 (moment caps, mean shift, the
shifted-core comparison, uniform moment interpolation) to a specific observable. Checks:
`docs/tight/CHECK_CONTACT_LEAVES.md` §4 (L4, L6, L9, L11, L14).
-/

@[expose] public section

namespace BiluLinial.Tight

open Matrix

universe u

variable {d p : ℕ}

/-! ### Helpers (prefix `lx_`) -/

section Helpers

theorem lx_amgm2 (a b : ℝ) : a ^ 2 * b ^ 2 ≤ (a ^ 4 + b ^ 4) / 2 := by
  nlinarith [sq_nonneg (a ^ 2 - b ^ 2)]

theorem lx_amgm3 {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    a * b * c ≤ (a ^ 3 + b ^ 3 + c ^ 3) / 3 := by
  have hs : 0 ≤ a + b + c := by linarith
  nlinarith [mul_nonneg hs (sq_nonneg (a - b)), mul_nonneg hs (sq_nonneg (b - c)),
    mul_nonneg hs (sq_nonneg (c - a))]

theorem lx_amgm4 (a b c e : ℝ) : a * b * c * e ≤ (a ^ 4 + b ^ 4 + c ^ 4 + e ^ 4) / 4 := by
  nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (c ^ 2 - e ^ 2), sq_nonneg (a * b - c * e)]

/-- Diagonal facts of one branch on the support. -/
theorem lx_branch {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {a τ h : ℝ} {y : V → ℝ} {σ : Config V} {S : Finset V}
    (hy : ∀ k, 0 ≤ y k ∧ y k ≤ 2) (hP : (precN G a τ y σ S).PosDef) (hh : 0 ≤ h) (i : V) :
    0 ≤ hN G a τ y σ S i ∧ 0 ≤ shiftP G a τ h y σ S i i ∧
      shiftP G a τ h y σ S i i ≤ greenP G a τ y σ S i i ∧
      greenP G a τ y σ S i i ≤ 2 * hN G a τ y σ S i := by
  have hy0 : ∀ k, 0 ≤ y k := fun k => (hy k).1
  have hh0 : 0 ≤ hN G a τ y σ S i := hP.inv.posSemidef.diag_nonneg
  have hX0 := (SecB.diag_nonneg_of_posDef G hP hy0 hh i).2
  have hle := SecB.hzN_le_hN G hP hh hy0 i
  have eG := SecB.greenP_diag G (a := a) (τ := τ) σ S (hy0 i)
  have eX := SecB.shiftP_diag G (a := a) (τ := τ) (z := h) σ S (hy0 i)
  refine ⟨hh0, hX0, ?_, ?_⟩
  · rw [eG, eX]; exact mul_le_mul_of_nonneg_left hle (hy0 i)
  · rw [eG]; exact mul_le_mul_of_nonneg_right (hy i).2 hh0

section Contact

variable (ct : Contact.{u} d p)

theorem lx_src (hR : TRegime d p) (i : ct.V) :
    (0 ≤ ct.yp i ∧ ct.yp i ≤ 2) ∧ (0 ≤ ct.ym i ∧ ct.ym i ≤ 2) := by
  have hs := hR.sOf_pos
  have hs2 := SecA.sOf_le_two hR
  have hl : ct.lam * sOf d p ≤ sOf d p := mul_le_of_le_one_left hs.le ct.ctx.lam_le_one
  have h1 := ct.ctx.hyp i
  have h2 := ct.ctx.hym i
  exact ⟨⟨h1.1, by linarith [h1.2]⟩, ⟨h2.1, by linarith [h2.2]⟩⟩

theorem lx_Zw (hR : TRegime d p) : 0 < Zw ct.G p (aOf d p) ct.yp ct.ym ct.S :=
  ct.ctx.pos ct.yp ct.ym (ct.ctx.hyp.of_mul_le_one ct.ctx.lam_le_one hR.sOf_pos.le)
    (ct.ctx.hym.of_mul_le_one ct.ctx.lam_le_one hR.sOf_pos.le)

theorem lx_card_N : (ct.N.card : ℝ) ≤ d := by
  change ((nbhd ct.G ct.S ct.v).card : ℝ) ≤ d
  exact_mod_cast (FloorIns.card_nbhd_le ct.G ct.S ct.v).trans (ct.ctx.deg ct.v)

theorem lx_N_sub {i : ct.V} (hi : i ∈ ct.N) : i ∈ ct.S := (Finset.mem_filter.1 hi).1

theorem lx_E_mono {f g : Config ct.V → ℝ}
    (h : ∀ σ, wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 → f σ ≤ g σ) : ct.E f ≤ ct.E g :=
  SecB.lawE_mono ct.G h

theorem lx_E_congr {f g : Config ct.V → ℝ}
    (h : ∀ σ, wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 → f σ = g σ) : ct.E f = ct.E g :=
  lawE_congr ct.G h

theorem lx_E_nonneg {f : Config ct.V → ℝ}
    (h : ∀ σ, wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 → 0 ≤ f σ) : 0 ≤ ct.E f :=
  lawE_nonneg ct.G h

theorem lx_E_add (f g : Config ct.V → ℝ) : ct.E (fun σ => f σ + g σ) = ct.E f + ct.E g :=
  lawE_add ct.G f g

theorem lx_E_sub (f g : Config ct.V → ℝ) : ct.E (fun σ => f σ - g σ) = ct.E f - ct.E g :=
  lawE_sub ct.G f g

theorem lx_E_const_mul (c : ℝ) (f : Config ct.V → ℝ) :
    ct.E (fun σ => c * f σ) = c * ct.E f :=
  lawE_const_mul ct.G c f

theorem lx_E_sum {ι : Type*} (s : Finset ι) (f : ι → Config ct.V → ℝ) :
    ct.E (fun σ => ∑ l ∈ s, f l σ) = ∑ l ∈ s, ct.E (f l) :=
  lawE_sum ct.G s f

theorem lx_E_const (hZ : 0 < Zw ct.G p (aOf d p) ct.yp ct.ym ct.S) (c : ℝ) :
    ct.E (fun _ => c) = c :=
  SecB.lawE_const ct.G hZ.ne' c

/-- Diagonal facts of both branches on the support. -/
theorem lx_supp (hR : TRegime d p) {h : ℝ} (hh : 0 ≤ h) {σ : Config ct.V}
    (hσ : wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0) (i : ct.V) :
    (0 ≤ hN ct.G (aOf d p) 1 ct.yp σ ct.S i ∧ 0 ≤ ct.XP h σ i i ∧
        ct.XP h σ i i ≤ ct.gp σ i i ∧ ct.gp σ i i ≤ 2 * hN ct.G (aOf d p) 1 ct.yp σ ct.S i) ∧
      (0 ≤ hN ct.G (aOf d p) (-1) ct.ym σ ct.S i ∧ 0 ≤ ct.XM h σ i i ∧
        ct.XM h σ i i ≤ ct.gm σ i i ∧ ct.gm σ i i ≤ 2 * hN ct.G (aOf d p) (-1) ct.ym σ ct.S i) := by
  obtain ⟨hP, hM⟩ := SecB.posDef_of_wt_ne_zero ct.G hσ
  exact ⟨lx_branch ct.G (fun k => (lx_src ct hR k).1) hP hh i,
    lx_branch ct.G (fun k => (lx_src ct hR k).2) hM hh i⟩

/-- (F2) in the crude form `E h^k ≤ 2^k` for `1 ≤ k ≤ p/2`. -/
theorem lx_F2 (hR : TRegime d p) {i : ct.V} (hi : i ∈ ct.S) {k : ℕ} (hk1 : 1 ≤ k)
    (hk2 : 2 * k ≤ p) :
    ct.E (fun σ => hN ct.G (aOf d p) 1 ct.yp σ ct.S i ^ k) ≤ 2 ^ k ∧
      ct.E (fun σ => hN ct.G (aOf d p) (-1) ct.ym σ ct.S i ^ k) ≤ 2 ^ k := by
  obtain ⟨hb0, hb2⟩ := SecB.f2_base_le_two hR hk1 hk2
  have h4 : 4 ≤ p := le_trans (by norm_num) hR.hp
  have hk3 : k + 2 ≤ p := by omega
  have hF := source_moments ct.G hR ct.ctx.toCapCtx ct.ctx.hyp ct.ctx.hym hi hk1 hk3
  exact ⟨hF.1.trans (pow_le_pow_left₀ hb0 hb2 k), hF.2.trans (pow_le_pow_left₀ hb0 hb2 k)⟩

theorem lx_uvec_sq (i : ct.V) :
    ct.uvec i * ct.uvec i = if i ∈ ct.N then 1 / (d : ℝ) else 0 := by
  unfold Contact.uvec
  split_ifs
  · rw [one_div_mul_one_div, Real.mul_self_sqrt (Nat.cast_nonneg _)]
  · simp

theorem lx_uvec_diag (f : ct.V → ℝ) :
    ct.uvec ⬝ᵥ (diagonal f *ᵥ ct.uvec) = (∑ i ∈ ct.N, f i) / d := by
  have e : ∀ i, ct.uvec i * (f i * ct.uvec i) = if i ∈ ct.N then f i / d else 0 := by
    intro i
    rw [mul_left_comm, lx_uvec_sq]
    split_ifs <;> ring
  simp only [dotProduct, mulVec_diagonal, e]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_div]

theorem lx_tP_integrand (h : ℝ) (σ : Config ct.V) :
    ct.OmP σ * (ct.uvec ⬝ᵥ (ct.MP h σ *ᵥ ct.uvec)) =
      1 / (16 * d) * (ct.gp σ ct.v ct.v ^ 2 * ∑ i ∈ ct.N, ct.XP h σ i i ^ 2) := by
  unfold Contact.OmP Contact.MP
  rw [lx_uvec_diag]
  have e : ∑ i ∈ ct.N, (ct.XP h σ i i / 2) ^ 2 = (∑ i ∈ ct.N, ct.XP h σ i i ^ 2) / 4 := by
    rw [Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [e]
  ring

theorem lx_tM_integrand (h : ℝ) (σ : Config ct.V) :
    ct.OmM σ * (ct.uvec ⬝ᵥ (ct.MM h σ *ᵥ ct.uvec)) =
      1 / (16 * d) * (ct.gp σ ct.v ct.v * ct.gm σ ct.v ct.v *
        ∑ i ∈ ct.N, ct.XP h σ i i * ct.XM h σ i i) := by
  unfold Contact.OmM Contact.MM
  rw [lx_uvec_diag]
  have e : ∑ i ∈ ct.N, ct.XP h σ i i / 2 * (ct.XM h σ i i / 2) =
      (∑ i ∈ ct.N, ct.XP h σ i i * ct.XM h σ i i) / 4 := by
    rw [Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [e]
  ring

/-- Moments of a weight dominated by `16 f₁ f₂ f₃` with `E f_j^{3k} ≤ 8^k`. -/
theorem lx_E_pow_le {k : ℕ} (f₁ f₂ f₃ : Config ct.V → ℝ)
    (h0 : ∀ σ, wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 → 0 ≤ f₁ σ ∧ 0 ≤ f₂ σ ∧ 0 ≤ f₃ σ)
    (h1 : ct.E (fun σ => f₁ σ ^ (3 * k)) ≤ 8 ^ k) (h2 : ct.E (fun σ => f₂ σ ^ (3 * k)) ≤ 8 ^ k)
    (h3 : ct.E (fun σ => f₃ σ ^ (3 * k)) ≤ 8 ^ k) (Z : Config ct.V → ℝ)
    (hZb : ∀ σ, wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 →
      0 ≤ Z σ ∧ Z σ ≤ 16 * (f₁ σ * f₂ σ * f₃ σ)) :
    ct.E (fun σ => Z σ ^ k) ≤ 128 ^ k := by
  have e : ∀ f : ℝ, f ^ (3 * k) = (f ^ k) ^ 3 := fun f => by rw [← pow_mul, mul_comm]
  calc ct.E (fun σ => Z σ ^ k)
      ≤ ct.E (fun σ => 16 ^ k / 3 * (f₁ σ ^ (3 * k) + f₂ σ ^ (3 * k) + f₃ σ ^ (3 * k))) := by
        refine lx_E_mono ct fun σ hσ => ?_
        obtain ⟨a0, b0, c0⟩ := h0 σ hσ
        obtain ⟨z0, zb⟩ := hZb σ hσ
        rw [e, e, e]
        have hg := lx_amgm3 (pow_nonneg a0 k) (pow_nonneg b0 k) (pow_nonneg c0 k)
        have h16 : (0 : ℝ) ≤ 16 ^ k := by positivity
        calc Z σ ^ k ≤ (16 * (f₁ σ * f₂ σ * f₃ σ)) ^ k := pow_le_pow_left₀ z0 zb k
          _ = 16 ^ k * (f₁ σ ^ k * f₂ σ ^ k * f₃ σ ^ k) := by
              rw [mul_pow, mul_pow, mul_pow]
          _ ≤ 16 ^ k * (((f₁ σ ^ k) ^ 3 + (f₂ σ ^ k) ^ 3 + (f₃ σ ^ k) ^ 3) / 3) :=
              mul_le_mul_of_nonneg_left hg h16
          _ = _ := by ring
    _ = 16 ^ k / 3 * (ct.E (fun σ => f₁ σ ^ (3 * k)) + ct.E (fun σ => f₂ σ ^ (3 * k)) +
          ct.E (fun σ => f₃ σ ^ (3 * k))) := by
        rw [lx_E_const_mul, lx_E_add, lx_E_add]
    _ ≤ 16 ^ k / 3 * (8 ^ k + 8 ^ k + 8 ^ k) := by gcongr
    _ = 128 ^ k := by
        rw [show (128 : ℝ) = 16 * 8 by norm_num, mul_pow]; ring

end Contact

/-- `c₄ = (pr - 4)/(p - 4)` satisfies `0 ≤ c₄` and `c₄⁴ ≤ 1 + 5ε` for `p ≥ 404`. -/
theorem lx_c4 (hR : TRegime d p) (hp : 404 ≤ p) :
    0 ≤ ((p : ℝ) * rOf d p - 4) / ((p : ℝ) - 4) ∧
      (((p : ℝ) * rOf d p - 4) / ((p : ℝ) - 4)) ^ 4 ≤ 1 + 5 * epsP d p := by
  have hp' : (404 : ℝ) ≤ p := by exact_mod_cast hp
  have he0 := SecA.epsP_nonneg hR
  have he1 := SecA.epsP_le hR
  have hr : rOf d p = 1 + epsP d p := by rw [epsP]; ring
  have hp4 : 0 < (p : ℝ) - 4 := by linarith
  set ε := epsP d p
  set x := (p : ℝ) * ε / ((p : ℝ) - 4) with hx
  have hc : ((p : ℝ) * rOf d p - 4) / ((p : ℝ) - 4) = 1 + x := by
    rw [hr, hx]; field_simp; ring
  have hx0 : 0 ≤ x := div_nonneg (mul_nonneg (by linarith) he0) hp4.le
  have hx1 : x ≤ 101 / 100 * ε := by
    rw [hx, div_le_iff₀ hp4]
    nlinarith [mul_nonneg he0 (show (0 : ℝ) ≤ p - 404 by linarith)]
  have hx2 : x ≤ 1 / 100 := by linarith
  rw [hc]
  refine ⟨by linarith, ?_⟩
  have h4 : 4 + 6 * x + 4 * x ^ 2 + x ^ 3 ≤ 41 / 10 := by
    nlinarith [pow_le_pow_left₀ hx0 hx2 2, pow_le_pow_left₀ hx0 hx2 3]
  have e : (1 + x) ^ 4 = 1 + x * (4 + 6 * x + 4 * x ^ 2 + x ^ 3) := by ring
  rw [e]
  nlinarith [mul_le_mul_of_nonneg_left h4 hx0]

/-- A moment order `k ≥ log d + 2` with `A k ≤ p`. -/
theorem lx_choose_k (hR : TRegime d p) {A : ℝ} (hA : 0 ≤ A)
    (hlp : A * (Real.log d + 3) ≤ p) : ∃ k : ℕ, Real.log d + 2 ≤ k ∧ A * k ≤ p := by
  have hd1 : (1 : ℝ) ≤ d := by have := hR.ten_pow_six_le_d; linarith
  have hlogd : 0 ≤ Real.log d := Real.log_nonneg hd1
  refine ⟨⌈Real.log d⌉₊ + 2, ?_, ?_⟩
  · have := Nat.le_ceil (Real.log d)
    push_cast; linarith
  · have hcu : (⌈Real.log d⌉₊ : ℝ) < Real.log d + 1 := Nat.ceil_lt_add_one hlogd
    have : ((⌈Real.log d⌉₊ + 2 : ℕ) : ℝ) ≤ Real.log d + 3 := by push_cast; linarith
    exact le_trans (mul_le_mul_of_nonneg_left this hA) hlp

/-- `a² ≤ 1/d`. -/
theorem lx_a2_le (hR : TRegime d p) : aOf d p ^ 2 ≤ 1 / (d : ℝ) := by
  have h1 := SecA.aOf_sq_le hR
  have hq := hR.qOf_pos
  have hd : (10 : ℝ) ^ 6 ≤ d := hR.ten_pow_six_le_d
  refine h1.trans (one_div_le_one_div_of_le (by positivity) ?_)
  rw [qOf]; linarith

/-- Eventually `h ≤ 1/2` and `h⁻¹ ≤ d`. -/
theorem lx_ev_h : Eventually fun _ _ d p h => TRegime d p ∧ 0 < h ∧ h ≤ 1 / 2 ∧ h⁻¹ ≤ d := by
  refine (SecB.eventually_h_facts.and (SecB.eventually_base 0)).mono ?_
  rintro c₀ κ₀ d p h ⟨⟨hR, h0, h1d, -, -⟩, -, -, -, hhd, hk0, hk1⟩
  have hd0 : (0 : ℝ) < d := by have := hR.ten_pow_six_le_d; linarith
  refine ⟨hR, h0, ?_, ?_⟩
  · have hp : (2 : ℝ) ≤ p := by exact_mod_cast hR.two_le_p
    have h16 : (16 : ℝ) ≤ (p : ℝ) ^ 4 := by
      have := pow_le_pow_left₀ (by norm_num) hp 4
      norm_num at this; linarith
    rw [hhd, div_le_iff₀ (by positivity)]
    linarith
  · rw [inv_le_comm₀ h0 hd0]
    simpa [one_div] using h1d

/-- Bounds on `U = (q-1)x - qz` for `|x|, |z| ≤ D`. -/
theorem lx_kp_U {q x z D : ℝ} (hq1 : 1 ≤ q) (hx : |x| ≤ D) (hz : |z| ≤ D) :
    |(q - 1) * x - q * z| ≤ 2 * q * D ∧ ((q - 1) * x - q * z) ^ 2 ≤ 4 * q ^ 2 * D ^ 2 ∧
      ((q - 1) * x - q * z) ^ 2 ≤ 2 * q ^ 2 * (x ^ 2 + z ^ 2) ∧
      |x * ((q - 1) * x - q * z)| ≤ 2 * q * (x ^ 2 + z ^ 2) := by
  have hq0 : 0 ≤ q - 1 := by linarith
  have hq0' : 0 ≤ q := by linarith
  have hs0 : 0 ≤ x ^ 2 + z ^ 2 := by positivity
  have hD : 0 ≤ D := le_trans (abs_nonneg x) hx
  have hUb : |(q - 1) * x - q * z| ≤ 2 * q * D := by
    calc |(q - 1) * x - q * z| ≤ |(q - 1) * x| + |q * z| := abs_sub _ _
      _ = (q - 1) * |x| + q * |z| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hq0, abs_of_nonneg hq0']
      _ ≤ (q - 1) * D + q * D :=
          add_le_add (mul_le_mul_of_nonneg_left hx hq0) (mul_le_mul_of_nonneg_left hz hq0')
      _ ≤ 2 * q * D := by linarith
  refine ⟨hUb, ?_, ?_, ?_⟩
  · have := pow_le_pow_left₀ (abs_nonneg _) hUb 2
    rw [sq_abs] at this; nlinarith
  · have h1 : (q - 1) ^ 2 ≤ q ^ 2 := by nlinarith
    nlinarith [sq_nonneg ((q - 1) * x + q * z), mul_le_mul_of_nonneg_right h1 (sq_nonneg x)]
  · have e : x * ((q - 1) * x - q * z) = (q - 1) * x ^ 2 - q * (x * z) := by ring
    rw [e]
    have hxz : |x * z| ≤ (x ^ 2 + z ^ 2) / 2 := by
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg (x + z), sq_nonneg (x - z)]
    have hxz' := abs_le.1 hxz
    have h1 : q * (x * z) ≤ q * ((x ^ 2 + z ^ 2) / 2) := mul_le_mul_of_nonneg_left hxz'.2 hq0'
    have h2 := mul_le_mul_of_nonneg_left hxz'.1 hq0'
    have h3 : 0 ≤ (q - 1) * x ^ 2 := mul_nonneg hq0 (sq_nonneg x)
    have h4 : 0 ≤ q * z ^ 2 := mul_nonneg hq0' (sq_nonneg z)
    have h5 : 0 ≤ q * (x ^ 2 + z ^ 2) := mul_nonneg hq0' hs0
    rw [abs_le]; constructor <;> linarith [sq_nonneg x]

/-- Bounds on `V = (q-1)(P + x²) + q(Q + z²)` and `V₁ = (q-1)x² + qz²`. -/
theorem lx_kp_V {q x z P Q D : ℝ} (hq1 : 1 ≤ q) (hx2 : x ^ 2 ≤ D ^ 2) (hz2 : z ^ 2 ≤ D ^ 2)
    (hP : |P| ≤ D ^ 2) (hQ : |Q| ≤ D ^ 2) :
    |(q - 1) * (P + x ^ 2) + q * (Q + z ^ 2)| ≤ 4 * q * D ^ 2 ∧
      0 ≤ (q - 1) * x ^ 2 + q * z ^ 2 ∧ (q - 1) * x ^ 2 + q * z ^ 2 ≤ q * (x ^ 2 + z ^ 2) := by
  have hq0 : 0 ≤ q - 1 := by linarith
  have hq0' : 0 ≤ q := by linarith
  have hPa := abs_le.1 hP
  have hQa := abs_le.1 hQ
  have b1 := mul_le_mul_of_nonneg_left (show P + x ^ 2 ≤ 2 * D ^ 2 by linarith) hq0
  have b2 := mul_le_mul_of_nonneg_left (show -(2 * D ^ 2) ≤ P + x ^ 2 by
    nlinarith [sq_nonneg x]) hq0
  have b3 := mul_le_mul_of_nonneg_left (show Q + z ^ 2 ≤ 2 * D ^ 2 by linarith) hq0'
  have b4 := mul_le_mul_of_nonneg_left (show -(2 * D ^ 2) ≤ Q + z ^ 2 by
    nlinarith [sq_nonneg z]) hq0'
  refine ⟨?_, by positivity, ?_⟩
  · rw [abs_le]; constructor <;> nlinarith
  · nlinarith [sq_nonneg x]

/-- The bound on `x W`, `W = (q-1)(3Px + x³) - q(3Qz + z³)`. -/
theorem lx_kp_W {q x z P Q D : ℝ} (hq1 : 1 ≤ q) (hx2 : x ^ 2 ≤ D ^ 2) (hz2 : z ^ 2 ≤ D ^ 2)
    (hP : |P| ≤ D ^ 2) (hQ : |Q| ≤ D ^ 2) :
    |x * ((q - 1) * (3 * P * x + x ^ 3) - q * (3 * Q * z + z ^ 3))| ≤
      6 * q * D ^ 2 * (x ^ 2 + z ^ 2) := by
  have hq0 : 0 ≤ q - 1 := by linarith
  have hq0' : 0 ≤ q := by linarith
  have hPa := abs_le.1 hP
  have hxs : x ^ 2 ≤ x ^ 2 + z ^ 2 := by linarith [sq_nonneg z]
  have hxz : |x * z| ≤ (x ^ 2 + z ^ 2) / 2 := by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg (x + z), sq_nonneg (x - z)]
  have e : x * ((q - 1) * (3 * P * x + x ^ 3) - q * (3 * Q * z + z ^ 3)) =
      (q - 1) * (3 * P * x ^ 2 + x ^ 2 * x ^ 2) -
        q * (3 * Q * (x * z) + (x * z) * z ^ 2) := by ring
  rw [e]
  have a1 : |3 * P * x ^ 2 + x ^ 2 * x ^ 2| ≤ 4 * D ^ 2 * x ^ 2 := by
    have c1 := mul_le_mul_of_nonneg_right hx2 (sq_nonneg x)
    have c2 := mul_le_mul_of_nonneg_right hPa.1 (sq_nonneg x)
    have c3 := mul_le_mul_of_nonneg_right hPa.2 (sq_nonneg x)
    have c4 := mul_nonneg (sq_nonneg x) (sq_nonneg x)
    rw [abs_le]; constructor <;> nlinarith
  have a2 : |3 * Q * (x * z) + (x * z) * z ^ 2| ≤ 4 * D ^ 2 * |x * z| := by
    calc |3 * Q * (x * z) + (x * z) * z ^ 2| ≤ |3 * Q * (x * z)| + |(x * z) * z ^ 2| :=
          abs_add_le _ _
      _ = 3 * |Q| * |x * z| + |x * z| * z ^ 2 := by
          rw [abs_mul, abs_mul, abs_mul (x * z), abs_of_nonneg (sq_nonneg z)]; norm_num
      _ ≤ 3 * D ^ 2 * |x * z| + |x * z| * D ^ 2 := by gcongr
      _ = 4 * D ^ 2 * |x * z| := by ring
  have h1 : (q - 1) * (4 * D ^ 2 * x ^ 2) ≤ q * (4 * D ^ 2 * x ^ 2) := by
    nlinarith [mul_nonneg (sq_nonneg D) (sq_nonneg x)]
  have h2 : q * (4 * D ^ 2 * x ^ 2) ≤ q * (4 * D ^ 2 * (x ^ 2 + z ^ 2)) := by gcongr
  have h3 : q * (4 * D ^ 2 * |x * z|) ≤ q * (4 * D ^ 2 * ((x ^ 2 + z ^ 2) / 2)) := by gcongr
  calc |(q - 1) * (3 * P * x ^ 2 + x ^ 2 * x ^ 2) - q * (3 * Q * (x * z) + (x * z) * z ^ 2)|
      ≤ |(q - 1) * (3 * P * x ^ 2 + x ^ 2 * x ^ 2)| +
          |q * (3 * Q * (x * z) + (x * z) * z ^ 2)| := abs_sub _ _
    _ = (q - 1) * |3 * P * x ^ 2 + x ^ 2 * x ^ 2| +
          q * |3 * Q * (x * z) + (x * z) * z ^ 2| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hq0, abs_of_nonneg hq0']
    _ ≤ (q - 1) * (4 * D ^ 2 * x ^ 2) + q * (4 * D ^ 2 * |x * z|) := by gcongr
    _ ≤ 6 * q * D ^ 2 * (x ^ 2 + z ^ 2) := by nlinarith

/-- Combination of the seven monomial groups of `K - 6[(p-1)P² + pPQ]`. -/
theorem lx_kp_combine {q D s x P U Vv W V₁ : ℝ} (hq1 : 1 ≤ q) (hs0 : 0 ≤ s) (hxs : x ^ 2 ≤ s)
    (hP : |P| ≤ D ^ 2) (hU2 : U ^ 2 ≤ 4 * q ^ 2 * D ^ 2) (hU2s : U ^ 2 ≤ 2 * q ^ 2 * s)
    (hxU : |x * U| ≤ 2 * q * s) (hVb : |Vv| ≤ 4 * q * D ^ 2) (hxW : |x * W| ≤ 6 * q * D ^ 2 * s)
    (hV1 : 0 ≤ V₁ ∧ V₁ ≤ q * s) :
    |8 * (x * U) * U ^ 2 - 12 * (x * U) * Vv + 4 * (x * W) - 12 * P * U ^ 2 + 6 * P * V₁ +
        12 * x ^ 2 * U ^ 2 - 6 * x ^ 2 * Vv| ≤ 300 * q ^ 3 * (D ^ 2 * s) := by
  have hq0' : 0 ≤ q := by linarith
  have hU0 : 0 ≤ U ^ 2 := sq_nonneg U
  have hD2 : 0 ≤ D ^ 2 := sq_nonneg D
  have t1 : |8 * (x * U) * U ^ 2| ≤ 64 * q ^ 3 * (D ^ 2 * s) := by
    rw [abs_mul, abs_mul, abs_of_nonneg hU0, abs_of_pos (by norm_num : (0 : ℝ) < 8)]
    calc 8 * |x * U| * U ^ 2 ≤ 8 * (2 * q * s) * (4 * q ^ 2 * D ^ 2) := by gcongr
      _ = 64 * q ^ 3 * (D ^ 2 * s) := by ring
  have t2 : |12 * (x * U) * Vv| ≤ 96 * q ^ 2 * (D ^ 2 * s) := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 12)]
    calc 12 * |x * U| * |Vv| ≤ 12 * (2 * q * s) * (4 * q * D ^ 2) := by gcongr
      _ = 96 * q ^ 2 * (D ^ 2 * s) := by ring
  have t3 : |4 * (x * W)| ≤ 24 * q * (D ^ 2 * s) := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    calc 4 * |x * W| ≤ 4 * (6 * q * D ^ 2 * s) := by gcongr
      _ = 24 * q * (D ^ 2 * s) := by ring
  have t4 : |12 * P * U ^ 2| ≤ 24 * q ^ 2 * (D ^ 2 * s) := by
    rw [abs_mul, abs_mul, abs_of_nonneg hU0, abs_of_pos (by norm_num : (0 : ℝ) < 12)]
    calc 12 * |P| * U ^ 2 ≤ 12 * D ^ 2 * (2 * q ^ 2 * s) := by gcongr
      _ = 24 * q ^ 2 * (D ^ 2 * s) := by ring
  have t5 : |6 * P * V₁| ≤ 6 * q * (D ^ 2 * s) := by
    rw [abs_mul, abs_mul, abs_of_nonneg hV1.1, abs_of_pos (by norm_num : (0 : ℝ) < 6)]
    calc 6 * |P| * V₁ ≤ 6 * D ^ 2 * (q * s) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hP (by norm_num)) hV1.2 hV1.1 (by positivity)
      _ = 6 * q * (D ^ 2 * s) := by ring
  have t6 : |12 * x ^ 2 * U ^ 2| ≤ 48 * q ^ 2 * (D ^ 2 * s) := by
    rw [abs_of_nonneg (by positivity)]
    calc 12 * x ^ 2 * U ^ 2 ≤ 12 * s * (4 * q ^ 2 * D ^ 2) := by gcongr
      _ = 48 * q ^ 2 * (D ^ 2 * s) := by ring
  have t7 : |6 * x ^ 2 * Vv| ≤ 24 * q * (D ^ 2 * s) := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 6 * x ^ 2)]
    calc 6 * x ^ 2 * |Vv| ≤ 6 * s * (4 * q * D ^ 2) := by gcongr
      _ = 24 * q * (D ^ 2 * s) := by ring
  have hDs : 0 ≤ D ^ 2 * s := mul_nonneg hD2 hs0
  have hq2 := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hq1 (by norm_num : 2 ≤ 3)) hDs
  have hq3 := mul_le_mul_of_nonneg_right (le_self_pow₀ hq1 (by norm_num : 3 ≠ 0)) hDs
  have hq4 : 0 ≤ q ^ 3 * (D ^ 2 * s) := mul_nonneg (pow_nonneg hq0' 3) hDs
  have a1 := abs_le.1 t1
  have a2 := abs_le.1 t2
  have a3 := abs_le.1 t3
  have a4 := abs_le.1 t4
  have a5 := abs_le.1 t5
  have a6 := abs_le.1 t6
  have a7 := abs_le.1 t7
  rw [abs_le]
  constructor <;> linarith

/-- The part of `K_i` with two root-row factors (every monomial of `K` other than the row-free
part `6[(p-1)P² + pPQ]`): `|K - 6[(p-1)P² + pPQ]| ≤ 300 p³ D² (x² + z²)` for `|x|, |z| ≤ D`,
`|P|, |Q| ≤ D²`. -/
theorem lx_kpoly_rest {p : ℕ} (hp : 1 ≤ p) {x z P Q D : ℝ} (hx : |x| ≤ D) (hz : |z| ≤ D)
    (hP : |P| ≤ D ^ 2) (hQ : |Q| ≤ D ^ 2) :
    |Kpoly p x z P Q - 6 * (((p : ℝ) - 1) * P ^ 2 + p * P * Q)| ≤
      300 * (p : ℝ) ^ 3 * (D ^ 2 * (x ^ 2 + z ^ 2)) := by
  have hq1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hx2 : x ^ 2 ≤ D ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg x) hx 2
  have hz2 : z ^ 2 ≤ D ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg z) hz 2
  generalize hq : (p : ℝ) = q at hq1 ⊢
  have eR : Kpoly p x z P Q - 6 * ((q - 1) * P ^ 2 + q * P * Q) =
      8 * (x * ((q - 1) * x - q * z)) * ((q - 1) * x - q * z) ^ 2 -
        12 * (x * ((q - 1) * x - q * z)) * ((q - 1) * (P + x ^ 2) + q * (Q + z ^ 2)) +
        4 * (x * ((q - 1) * (3 * P * x + x ^ 3) - q * (3 * Q * z + z ^ 3))) -
        12 * P * ((q - 1) * x - q * z) ^ 2 + 6 * P * ((q - 1) * x ^ 2 + q * z ^ 2) +
        12 * x ^ 2 * ((q - 1) * x - q * z) ^ 2 -
        6 * x ^ 2 * ((q - 1) * (P + x ^ 2) + q * (Q + z ^ 2)) := by
    rw [← hq]; simp only [Kpoly]; ring
  rw [eR]
  obtain ⟨-, hU2, hU2s, hxU⟩ := lx_kp_U hq1 hx hz
  obtain ⟨hVb, hV1⟩ := lx_kp_V hq1 hx2 hz2 hP hQ
  exact lx_kp_combine hq1 (by positivity) (by linarith [sq_nonneg z]) hP hU2 hU2s hxU hVb
    (lx_kp_W hq1 hx2 hz2 hP hQ) hV1

section ShiftMat

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The physical shifted inverse as a matrix: `X = Y^{1/2} Q⁻¹ Y^{1/2}`, `Q = P̃ + h Y_S`. -/
theorem lx_shiftMat_eq (a τ h : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) :
    (Matrix.of fun i j => shiftP G a τ h y σ S i j) =
      diagonal (fun k => Real.sqrt (y k)) * (precN G a τ y σ S + h • srcDiag y S)⁻¹ *
        diagonal (fun k => Real.sqrt (y k)) := by
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.of_apply]
  rfl

/-- `P̃ + h Y_S = 1_S P̃ 1_S + diag(f)` with `f = h y` on `S` and `1` off `S`. -/
theorem lx_Q_decomp (a τ h : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) :
    precN G a τ y σ S + h • srcDiag y S =
      diagonal (fun k => if k ∈ S then (1 : ℝ) else 0) * precN G a τ y σ S *
          diagonal (fun k => if k ∈ S then (1 : ℝ) else 0) +
        diagonal (fun k => if k ∈ S then h * y k else 1) := by
  ext u w
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.mul_diagonal, Matrix.diagonal_mul,
    srcDiag, Matrix.diagonal_apply, precN, Matrix.of_apply, smul_eq_mul]
  by_cases huw : u = w
  · subst huw
    by_cases hu : u ∈ S <;> simp [hu]
  · by_cases hu : u ∈ S <;> by_cases hw : w ∈ S <;> simp [hu, hw, huw]

theorem lx_shift_psd {a τ h : ℝ} {y : V → ℝ} {σ : Config V} {S : Finset V}
    (hy : ∀ k, 0 ≤ y k) (hh : 0 ≤ h) (hP : (precN G a τ y σ S).PosDef) :
    (Matrix.of fun i j => shiftP G a τ h y σ S i j).PosSemidef := by
  have hQ : (precN G a τ y σ S + h • srcDiag y S).PosDef :=
    hP.add_posSemidef (SecA.srcDiag_smul_posSemidef hh hy S)
  rw [lx_shiftMat_eq]
  have := hQ.inv.posSemidef.conjTranspose_mul_mul_same (diagonal fun k => Real.sqrt (y k))
  rwa [diagonal_conjTranspose, star_trivial] at this

end ShiftMat

/-- The variational bound for `D Q⁻¹ D` with `Q = P + diag(f)`, `P ⪰ 0`. -/
theorem lx_quad_le {ι : Type*} [Fintype ι] [DecidableEq ι] {P : Matrix ι ι ℝ}
    (hP : P.PosSemidef) (f : ι → ℝ) (hQ : (P + diagonal f).PosDef) (s w g : ι → ℝ)
    (hg : ∀ k t, 2 * (s k * w k) * t - f k * t ^ 2 ≤ g k) :
    w ⬝ᵥ ((diagonal s * (P + diagonal f)⁻¹ * diagonal s) *ᵥ w) ≤ ∑ k, g k := by
  have hQu : IsUnit (P + diagonal f).det :=
    ((P + diagonal f).isUnit_iff_isUnit_det).1 hQ.isUnit
  set u := diagonal s *ᵥ w with hu
  set x := (P + diagonal f)⁻¹ *ᵥ u with hx
  have hQx : (P + diagonal f) *ᵥ x = u := by
    rw [hx, mulVec_mulVec, Matrix.mul_nonsing_inv _ hQu, one_mulVec]
  have e1 : w ⬝ᵥ ((diagonal s * (P + diagonal f)⁻¹ * diagonal s) *ᵥ w) = u ⬝ᵥ x := by
    rw [← mulVec_mulVec, ← mulVec_mulVec, ← hx]
    simp only [hu, dotProduct, mulVec_diagonal]
    exact Finset.sum_congr rfl fun k _ => by ring
  have e2 : x ⬝ᵥ ((P + diagonal f) *ᵥ x) = u ⬝ᵥ x := by rw [hQx, dotProduct_comm]
  have hPx := hP.dotProduct_mulVec_nonneg x
  rw [star_trivial] at hPx
  have e3 : x ⬝ᵥ ((P + diagonal f) *ᵥ x) = x ⬝ᵥ (P *ᵥ x) + ∑ k, f k * x k ^ 2 := by
    rw [add_mulVec, dotProduct_add]
    congr 1
    simp only [dotProduct, mulVec_diagonal]
    exact Finset.sum_congr rfl fun k _ => by ring
  have e4 : u ⬝ᵥ x = ∑ k, s k * w k * x k := by
    simp only [hu, dotProduct, mulVec_diagonal]
  have e5 : ∑ k, (2 * (s k * w k) * x k - f k * x k ^ 2) =
      2 * ∑ k, s k * w k * x k - ∑ k, f k * x k ^ 2 := by
    rw [Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [e1]
  calc u ⬝ᵥ x ≤ ∑ k, (2 * (s k * w k) * x k - f k * x k ^ 2) := by
        rw [e5, ← e4]; linarith
    _ ≤ ∑ k, g k := Finset.sum_le_sum fun k _ => hg k (x k)

/-- `X ⪯ h⁻¹ I` for the physical shifted inverse, when every source is at most `h⁻¹`. -/
theorem lx_shift_quad {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {a τ h : ℝ} {y : V → ℝ} {σ : Config V} {S : Finset V}
    (hy : ∀ k, 0 ≤ y k ∧ y k ≤ h⁻¹) (hh : 0 < h) (hP : (precN G a τ y σ S).PosDef)
    (w : V → ℝ) :
    w ⬝ᵥ ((Matrix.of fun i j => shiftP G a τ h y σ S i j) *ᵥ w) ≤ h⁻¹ * (w ⬝ᵥ w) := by
  have hy0 : ∀ k, 0 ≤ y k := fun k => (hy k).1
  have hdec := lx_Q_decomp G a τ h y σ S
  have hP' : (diagonal (fun k => if k ∈ S then (1 : ℝ) else 0) * precN G a τ y σ S *
      diagonal (fun k => if k ∈ S then (1 : ℝ) else 0)).PosSemidef := by
    have := hP.posSemidef.conjTranspose_mul_mul_same
      (diagonal fun k => if k ∈ S then (1 : ℝ) else 0)
    rwa [diagonal_conjTranspose, star_trivial] at this
  have hQ : (precN G a τ y σ S + h • srcDiag y S).PosDef :=
    hP.add_posSemidef (SecA.srcDiag_smul_posSemidef hh.le hy0 S)
  rw [hdec] at hQ
  rw [lx_shiftMat_eq, hdec]
  refine le_trans (lx_quad_le hP' _ hQ (fun k => Real.sqrt (y k)) w
    (fun k => h⁻¹ * w k ^ 2) ?_) ?_
  · intro k t
    have hs2 : Real.sqrt (y k) ^ 2 = y k := Real.sq_sqrt (hy0 k)
    split_ifs with hk
    · have e : (w k - h * Real.sqrt (y k) * t) ^ 2 =
          w k ^ 2 - 2 * h * (Real.sqrt (y k) * w k) * t + h ^ 2 * Real.sqrt (y k) ^ 2 * t ^ 2 := by
        ring
      rw [hs2] at e
      have e' : h⁻¹ * w k ^ 2 - (2 * (Real.sqrt (y k) * w k) * t - h * y k * t ^ 2) =
          h⁻¹ * (w k - h * Real.sqrt (y k) * t) ^ 2 := by
        rw [e]; field_simp; ring
      have : 0 ≤ h⁻¹ * (w k - h * Real.sqrt (y k) * t) ^ 2 := by positivity
      linarith
    · have e : (Real.sqrt (y k) * w k - t) ^ 2 =
          Real.sqrt (y k) ^ 2 * w k ^ 2 - 2 * (Real.sqrt (y k) * w k) * t + t ^ 2 := by ring
      rw [hs2] at e
      have h2 : y k * w k ^ 2 ≤ h⁻¹ * w k ^ 2 :=
        mul_le_mul_of_nonneg_right (hy k).2 (sq_nonneg _)
      nlinarith [sq_nonneg (Real.sqrt (y k) * w k - t)]
  · rw [← Finset.mul_sum]
    simp only [dotProduct, sq, le_refl]

/-- A diagonal entry is at most the quadratic-form bound. -/
theorem lx_diag_le_of_quad {ι : Type*} [Fintype ι] [DecidableEq ι] {X : Matrix ι ι ℝ} {c : ℝ}
    (hX : ∀ w, w ⬝ᵥ (X *ᵥ w) ≤ c * (w ⬝ᵥ w)) (i : ι) : X i i ≤ c := by
  have := hX (Pi.single i 1)
  simpa [mulVec_single_one, dotProduct_single, single_dotProduct] using this

/-- Entries of a PSD matrix with diagonal at most `c`: `|X_ik| ≤ c`. -/
theorem lx_entry_le {ι : Type*} [Fintype ι] [DecidableEq ι] {X : Matrix ι ι ℝ}
    (hX : X.PosSemidef) {c : ℝ} (hd : ∀ i, X i i ≤ c) (i k : ι) : |X i k| ≤ c := by
  have h := SecB.posSemidef_entry_sq_le hX i k
  have h0i : 0 ≤ X i i := hX.diag_nonneg
  have h0k : 0 ≤ X k k := hX.diag_nonneg
  have hc : 0 ≤ c := h0i.trans (hd i)
  have : X i k ^ 2 ≤ c ^ 2 := h.trans (by nlinarith [hd i, hd k])
  exact (sq_le_sq.mp this).trans_eq (abs_of_nonneg hc)

/-- Restricting a quadratic form to `N`. -/
theorem lx_quad_restrict {ι : Type*} [Fintype ι] [DecidableEq ι] (N : Finset ι)
    (X : Matrix ι ι ℝ) (ω : ι → ℝ) :
    (fun i => if i ∈ N then ω i else 0) ⬝ᵥ (X *ᵥ fun i => if i ∈ N then ω i else 0) =
        ∑ i ∈ N, ∑ j ∈ N, ω i * X i j * ω j ∧
      (fun i => if i ∈ N then ω i else 0) ⬝ᵥ (fun i => if i ∈ N then ω i else 0) =
        ∑ i ∈ N, ω i ^ 2 := by
  constructor
  · have e : ∀ i, (if i ∈ N then ω i else 0) * ∑ j, X i j * (if j ∈ N then ω j else 0) =
        if i ∈ N then ∑ j ∈ N, ω i * X i j * ω j else 0 := by
      intro i
      split_ifs with hi
      · rw [Finset.mul_sum]
        have e2 : ∀ j, ω i * (X i j * (if j ∈ N then ω j else 0)) =
            if j ∈ N then ω i * X i j * ω j else 0 := by
          intro j; split_ifs <;> ring
        simp only [e2]
        rw [Finset.sum_ite_mem, Finset.univ_inter]
      · simp
    simp only [dotProduct, mulVec, e]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  · have e : ∀ i, (if i ∈ N then ω i else 0) * (if i ∈ N then ω i else 0) =
        if i ∈ N then ω i ^ 2 else 0 := by
      intro i; split_ifs <;> ring
    simp only [dotProduct, e]
    rw [Finset.sum_ite_mem, Finset.univ_inter]

/-- A rank-one perturbation inside the Frobenius energy: if `X = Y + ωωᵀ` on `N × N` and
`X ⪯ c`, then `‖X[N,N]‖_F² - ‖Y[N,N]‖_F² ≤ 2c |ω_N|²`. -/
theorem lx_rank_one_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (N : Finset ι)
    (X : Matrix ι ι ℝ) (Y : ι → ι → ℝ) (ω : ι → ℝ)
    (hXY : ∀ i ∈ N, ∀ j ∈ N, X i j = Y i j + ω i * ω j) {c : ℝ}
    (hq : ∀ w, w ⬝ᵥ (X *ᵥ w) ≤ c * (w ⬝ᵥ w)) :
    ∑ i ∈ N, ∑ j ∈ N, X i j ^ 2 - ∑ i ∈ N, ∑ j ∈ N, Y i j ^ 2 ≤
      2 * c * ∑ i ∈ N, ω i ^ 2 := by
  obtain ⟨e1, e2⟩ := lx_quad_restrict N X ω
  have hq' := hq (fun i => if i ∈ N then ω i else 0)
  rw [e1, e2] at hq'
  have hY2 : ∀ i ∈ N, ∀ j ∈ N, Y i j ^ 2 =
      X i j ^ 2 - (2 * (ω i * X i j * ω j) - ω i ^ 2 * ω j ^ 2) := by
    intro i hi j hj
    rw [show Y i j = X i j - ω i * ω j by linarith [hXY i hi j hj]]
    ring
  have hs : ∑ i ∈ N, ∑ j ∈ N, Y i j ^ 2 = ∑ i ∈ N, ∑ j ∈ N, X i j ^ 2 -
      (2 * ∑ i ∈ N, ∑ j ∈ N, ω i * X i j * ω j - (∑ i ∈ N, ω i ^ 2) ^ 2) := by
    rw [Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => hY2 i hi j hj]
    simp only [Finset.sum_sub_distrib, Finset.mul_sum]
    rw [sq (∑ i ∈ N, ω i ^ 2), Finset.sum_mul_sum]
  rw [hs]
  nlinarith [sq_nonneg (∑ i ∈ N, ω i ^ 2)]

/-- The mixed version: `⟨X, X'⟩_N - ⟨Y, Y'⟩_N ≤ c (|ω_N|² + |ω'_N|²)`. -/
theorem lx_rank_one_mixed {ι : Type*} [Fintype ι] [DecidableEq ι] (N : Finset ι)
    (X X' : Matrix ι ι ℝ) (Y Y' : ι → ι → ℝ) (ω ω' : ι → ℝ)
    (hXY : ∀ i ∈ N, ∀ j ∈ N, X i j = Y i j + ω i * ω j)
    (hXY' : ∀ i ∈ N, ∀ j ∈ N, X' i j = Y' i j + ω' i * ω' j) {c : ℝ}
    (hq : ∀ w, w ⬝ᵥ (X *ᵥ w) ≤ c * (w ⬝ᵥ w)) (hq' : ∀ w, w ⬝ᵥ (X' *ᵥ w) ≤ c * (w ⬝ᵥ w)) :
    ∑ i ∈ N, ∑ j ∈ N, X i j * X' i j - ∑ i ∈ N, ∑ j ∈ N, Y i j * Y' i j ≤
      c * (∑ i ∈ N, ω i ^ 2 + ∑ i ∈ N, ω' i ^ 2) := by
  obtain ⟨e1, e2⟩ := lx_quad_restrict N X ω'
  obtain ⟨e1', e2'⟩ := lx_quad_restrict N X' ω
  have h1 := hq (fun i => if i ∈ N then ω' i else 0)
  rw [e1, e2] at h1
  have h2 := hq' (fun i => if i ∈ N then ω i else 0)
  rw [e1', e2'] at h2
  have hYY : ∀ i ∈ N, ∀ j ∈ N, Y i j * Y' i j = X i j * X' i j -
      (ω' i * X i j * ω' j + ω i * X' i j * ω j - ω i * ω' i * (ω j * ω' j)) := by
    intro i hi j hj
    rw [show Y i j = X i j - ω i * ω j by linarith [hXY i hi j hj],
      show Y' i j = X' i j - ω' i * ω' j by linarith [hXY' i hi j hj]]
    ring
  have hs : ∑ i ∈ N, ∑ j ∈ N, Y i j * Y' i j = ∑ i ∈ N, ∑ j ∈ N, X i j * X' i j -
      (∑ i ∈ N, ∑ j ∈ N, ω' i * X i j * ω' j + ∑ i ∈ N, ∑ j ∈ N, ω i * X' i j * ω j -
        (∑ i ∈ N, ω i * ω' i) ^ 2) := by
    rw [Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => hYY i hi j hj]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [sq, Finset.sum_mul_sum]
  rw [hs]
  nlinarith [sq_nonneg (∑ i ∈ N, ω i * ω' i)]

/-- Deleting a row and column: for `i, j ≠ v`,
`(Q with row/column v replaced by the identity)⁻¹_ij = Z_ij - Z_iv Z_vj / Z_vv`, `Z = Q⁻¹`. -/
theorem lx_inv_delete {ι : Type*} [Fintype ι] [DecidableEq ι] (Q : Matrix ι ι ℝ)
    (hQ : IsUnit Q.det) (v : ι) (hv : Q⁻¹ v v ≠ 0) {i j : ι} (hi : i ≠ v) (hj : j ≠ v) :
    (Matrix.of fun a b => if a = v ∨ b = v then (if a = b then (1 : ℝ) else 0) else Q a b)⁻¹ i j =
      Q⁻¹ i j - Q⁻¹ i v * Q⁻¹ v j / Q⁻¹ v v := by
  set Z := Q⁻¹ with hZ
  set Z' : Matrix ι ι ℝ := Matrix.of fun a b =>
    if a = v ∨ b = v then (if a = b then 1 else 0) else Z a b - Z a v * Z v b / Z v v with hZ'
  have hQZ : Q * Z = 1 := Matrix.mul_nonsing_inv Q hQ
  have key : (Matrix.of fun a b => if a = v ∨ b = v then (if a = b then (1 : ℝ) else 0)
      else Q a b) * Z' = 1 := by
    ext a b
    rw [Matrix.mul_apply, Matrix.one_apply]
    by_cases ha : a = v
    · subst ha
      simp only [Matrix.of_apply, true_or, ↓reduceIte, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq, Finset.mem_univ, hZ']
    · by_cases hb : b = v
      · subst hb
        have e : ∀ c, (Matrix.of fun a' b' => if a' = b ∨ b' = b then
            (if a' = b' then (1 : ℝ) else 0) else Q a' b') a c * Z' c b =
            if c = b then (if a = b then 1 else 0) else 0 := by
          intro c
          by_cases hc : c = b
          · subst hc; simp [hZ']
          · simp [hZ', hc]
        simp only [e, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, ha]
      · have h1 : ∑ c, Q a c * Z c b = if a = b then 1 else 0 := by
          have := congrFun (congrFun hQZ a) b
          rwa [Matrix.mul_apply, Matrix.one_apply] at this
        have h2 : ∑ c, Q a c * Z c v = 0 := by
          have := congrFun (congrFun hQZ a) v
          rwa [Matrix.mul_apply, Matrix.one_apply_ne ha] at this
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ v)] at h1 h2 ⊢
        have hterm : ∀ c ∈ Finset.univ.erase v,
            (Matrix.of fun a' b' => if a' = v ∨ b' = v then (if a' = b' then (1 : ℝ) else 0)
              else Q a' b') a c * Z' c b =
            Q a c * Z c b - Z v b / Z v v * (Q a c * Z c v) := by
          intro c hc
          have hcv : c ≠ v := Finset.ne_of_mem_erase hc
          simp only [Matrix.of_apply, ha, hcv, hb, or_self, ↓reduceIte, hZ']
          ring
        rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.mul_sum]
        have hv0 : (Matrix.of fun a' b' => if a' = v ∨ b' = v then
            (if a' = b' then (1 : ℝ) else 0) else Q a' b') a v * Z' v b = 0 := by
          simp [ha, hZ', Ne.symm hb]
        rw [hv0]
        have e1 : ∑ c ∈ Finset.univ.erase v, Q a c * Z c b =
            (if a = b then 1 else 0) - Q a v * Z v b := by linarith
        have e2 : ∑ c ∈ Finset.univ.erase v, Q a c * Z c v = -(Q a v * Z v v) := by linarith
        rw [e1, e2]
        field_simp
        ring
  rw [Matrix.inv_eq_right_inv key]
  simp [hZ', hi, hj]

section RankOne

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

omit [Fintype V] in
theorem lx_Qc_eq (a τ h : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) (v : V) :
    precCore G a τ y σ S v + h • srcDiag y (S.erase v) =
      Matrix.of fun u w => if u = v ∨ w = v then (if u = w then (1 : ℝ) else 0) else
        (precN G a τ y σ S + h • srcDiag y S) u w := by
  ext u w
  simp only [Matrix.add_apply, Matrix.smul_apply, precCore, srcDiag, Matrix.of_apply,
    Matrix.diagonal_apply, smul_eq_mul, Finset.mem_erase]
  by_cases huv : u = v
  · subst huv
    by_cases huw : u = w <;> simp [huw]
  · by_cases hwv : w = v
    · subst hwv
      simp [huv]
    · simp [huv, hwv]

/-- The full shifted inverse minus the core shifted inverse is rank one off the root. -/
theorem lx_rank_one {a τ h : ℝ} {y : V → ℝ} {σ : Config V} {S : Finset V} (v : V)
    (hy : ∀ k, 0 ≤ y k) (hh : 0 ≤ h) (hP : (precN G a τ y σ S).PosDef) :
    ∃ ω : V → ℝ, ∀ i, i ≠ v → ∀ j, j ≠ v →
      shiftP G a τ h y σ S i j = coreShift G a τ h y σ S v i j + ω i * ω j := by
  have hQ : (precN G a τ y σ S + h • srcDiag y S).PosDef :=
    hP.add_posSemidef (SecA.srcDiag_smul_posSemidef hh hy S)
  have hQu : IsUnit (precN G a τ y σ S + h • srcDiag y S).det :=
    ((precN G a τ y σ S + h • srcDiag y S).isUnit_iff_isUnit_det).1 hQ.isUnit
  have hvv : 0 < (precN G a τ y σ S + h • srcDiag y S)⁻¹ v v := hQ.inv.diag_pos
  have hsym : ∀ i j, (precN G a τ y σ S + h • srcDiag y S)⁻¹ i j =
      (precN G a τ y σ S + h • srcDiag y S)⁻¹ j i := fun i j => by
    have := hQ.inv.isHermitian.apply j i
    simpa using this
  refine ⟨fun i => Real.sqrt (y i) * (precN G a τ y σ S + h • srcDiag y S)⁻¹ i v /
    Real.sqrt ((precN G a τ y σ S + h • srcDiag y S)⁻¹ v v), fun i hi j hj => ?_⟩
  have hdel := lx_inv_delete _ hQu v hvv.ne' hi hj
  have hs : Real.sqrt ((precN G a τ y σ S + h • srcDiag y S)⁻¹ v v) ^ 2 =
      (precN G a τ y σ S + h • srcDiag y S)⁻¹ v v := Real.sq_sqrt hvv.le
  unfold coreShift shiftP
  rw [lx_Qc_eq, hdel, hsym v j]
  rw [show Real.sqrt (y i) * (precN G a τ y σ S + h • srcDiag y S)⁻¹ i v /
      Real.sqrt ((precN G a τ y σ S + h • srcDiag y S)⁻¹ v v) *
      (Real.sqrt (y j) * (precN G a τ y σ S + h • srcDiag y S)⁻¹ j v /
        Real.sqrt ((precN G a τ y σ S + h • srcDiag y S)⁻¹ v v)) =
      Real.sqrt (y i) * Real.sqrt (y j) * (precN G a τ y σ S + h • srcDiag y S)⁻¹ i v *
        (precN G a τ y σ S + h • srcDiag y S)⁻¹ j v /
        Real.sqrt ((precN G a τ y σ S + h • srcDiag y S)⁻¹ v v) ^ 2 by ring, hs]
  ring

end RankOne

section Contact2

variable (ct : Contact.{u} d p)

theorem lx_uvec_mat (g : ct.V → ct.V → ℝ) :
    ct.uvec ⬝ᵥ (Matrix.of g *ᵥ ct.uvec) = (∑ i ∈ ct.N, ∑ j ∈ ct.N, g i j) / d := by
  have e : ∀ i, ct.uvec i * ∑ j, g i j * ct.uvec j =
      if i ∈ ct.N then ∑ j ∈ ct.N, g i j / d else 0 := by
    intro i
    unfold Contact.uvec
    split_ifs with hi
    · rw [Finset.mul_sum]
      have e2 : ∀ j, 1 / Real.sqrt d * (g i j * (if j ∈ ct.N then 1 / Real.sqrt d else 0)) =
          if j ∈ ct.N then g i j / d else 0 := by
        intro j
        split_ifs
        · rw [show 1 / Real.sqrt d * (g i j * (1 / Real.sqrt d)) =
              g i j * (1 / Real.sqrt d * (1 / Real.sqrt d)) by ring, one_div_mul_one_div,
            Real.mul_self_sqrt (Nat.cast_nonneg _)]
          ring
        · ring
      simp only [e2]
      rw [Finset.sum_ite_mem, Finset.univ_inter]
    · simp
  simp only [dotProduct, mulVec, Matrix.of_apply, e]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_div]
  exact Finset.sum_congr rfl fun i _ => by rw [Finset.sum_div]

theorem lx_qP_integrand (h : ℝ) (σ : Config ct.V) :
    ct.OmP σ * (ct.uvec ⬝ᵥ (ct.KP h σ *ᵥ ct.uvec)) =
      1 / (16 * d) * (ct.gp σ ct.v ct.v ^ 2 * ∑ i ∈ ct.N, ∑ j ∈ ct.N, ct.XP h σ i j ^ 2) := by
  unfold Contact.OmP Contact.KP
  rw [lx_uvec_mat]
  have e : ∑ i ∈ ct.N, ∑ j ∈ ct.N, ct.XP h σ i j * ct.XP h σ i j / 4 =
      (∑ i ∈ ct.N, ∑ j ∈ ct.N, ct.XP h σ i j ^ 2) / 4 := by
    rw [Finset.sum_div]; refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_div]; exact Finset.sum_congr rfl fun j _ => by ring
  rw [e]; ring

theorem lx_qM_integrand (h : ℝ) (σ : Config ct.V) :
    ct.OmM σ * (ct.uvec ⬝ᵥ (ct.KM h σ *ᵥ ct.uvec)) =
      1 / (16 * d) * (ct.gp σ ct.v ct.v * ct.gm σ ct.v ct.v *
        ∑ i ∈ ct.N, ∑ j ∈ ct.N, ct.XP h σ i j * ct.XM h σ i j) := by
  unfold Contact.OmM Contact.KM
  rw [lx_uvec_mat]
  have e : ∑ i ∈ ct.N, ∑ j ∈ ct.N, ct.XP h σ i j * ct.XM h σ i j / 4 =
      (∑ i ∈ ct.N, ∑ j ∈ ct.N, ct.XP h σ i j * ct.XM h σ i j) / 4 := by
    rw [Finset.sum_div]; refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_div]
  rw [e]; ring

/-- `D_*` dominates `1 + G^±_ww` on the radius-two ball. -/
theorem lx_dstar_ge (σ : Config ct.V) {w : ct.V}
    (hw : w ∈ insert ct.v (ct.N ∪ ct.N.biUnion (nbhd ct.G ct.S))) :
    1 + ct.gp σ w w ≤ ct.Dstar σ ∧ 1 + ct.gm σ w w ≤ ct.Dstar σ := by
  have := (insert ct.v (ct.N ∪ ct.N.biUnion (nbhd ct.G ct.S))).le_sup'
    (fun w => max (ct.gp σ w w) (ct.gm σ w w)) hw
  unfold Contact.Dstar
  have h1 := le_max_left (ct.gp σ w w) (ct.gm σ w w)
  have h2 := le_max_right (ct.gp σ w w) (ct.gm σ w w)
  constructor <;> linarith

theorem lx_mem_ball_v : ct.v ∈ insert ct.v (ct.N ∪ ct.N.biUnion (nbhd ct.G ct.S)) :=
  Finset.mem_insert_self _ _

theorem lx_mem_ball_N {i : ct.V} (hi : i ∈ ct.N) :
    i ∈ insert ct.v (ct.N ∪ ct.N.biUnion (nbhd ct.G ct.S)) :=
  Finset.mem_insert_of_mem (Finset.mem_union_left _ hi)

/-- Uniform moment interpolation (UMI) against powers of `D_*`: if `0 ≤ Y ≤ d^a D_*^b` on the
support, then `E[D_*^c Y] ≤ 27·12^c (27·12^b e^{a+e}) (E Y + d^{-e})`. -/
theorem lx_umi (hR : TRegime d p)
    (hDs : ∀ n : ℕ, 1 ≤ n → 2 * n ≤ p →
      ct.E (fun σ => ct.Dstar σ ^ n) ≤ 3 * (1 + d + (d : ℝ) ^ 2) * 12 ^ n)
    {k : ℕ} (hk : Real.log d + 2 ≤ k) {a b c e : ℕ} (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hbk : 2 * (b * k) ≤ p) (hck : 2 * (c * k) ≤ p) (Y : Config ct.V → ℝ)
    (hY : ∀ σ, wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 →
      0 ≤ Y σ ∧ Y σ ≤ (d : ℝ) ^ a * ct.Dstar σ ^ b) :
    ct.E (fun σ => ct.Dstar σ ^ c * Y σ) ≤
      27 * 12 ^ c * (27 * 12 ^ b * Real.exp (a + e)) * (ct.E Y + 1 / (d : ℝ) ^ e) := by
  classical
  have hd1 : (1 : ℝ) ≤ d := by have := hR.ten_pow_six_le_d; linarith
  have hd0 : (0 : ℝ) < d := by linarith
  have hlogd : 0 ≤ Real.log d := Real.log_nonneg hd1
  have hk2 : 2 ≤ k := by
    have : (2 : ℝ) ≤ k := by linarith
    exact_mod_cast this
  have hZ := lx_Zw ct hR
  have h27 : 3 * (1 + d + (d : ℝ) ^ 2) ≤ 27 ^ k := by
    have hdk : (d : ℝ) ≤ 3 ^ k := by
      calc (d : ℝ) = Real.exp (Real.log d) := (Real.exp_log hd0).symm
        _ ≤ Real.exp k := Real.exp_le_exp.2 (by linarith)
        _ = Real.exp 1 ^ k := by rw [← Real.exp_nat_mul, mul_one]
        _ ≤ 3 ^ k := pow_le_pow_left₀ (Real.exp_pos 1).le
            (by linarith [Real.exp_one_lt_d9]) k
    have h9 : (9 : ℝ) ≤ 3 ^ k :=
      calc (9 : ℝ) = 3 ^ 2 := by norm_num
        _ ≤ 3 ^ k := pow_le_pow_right₀ (by norm_num) hk2
    have e27 : (27 : ℝ) ^ k = 3 ^ k * (3 ^ k * 3 ^ k) := by
      rw [← mul_pow, ← mul_pow]; norm_num
    have hd2 : (d : ℝ) ^ 2 ≤ 3 ^ k * 3 ^ k := by
      rw [sq]; exact mul_le_mul hdk hdk hd0.le (by positivity)
    have h3 : 3 * (1 + d + (d : ℝ) ^ 2) ≤ 9 * (d : ℝ) ^ 2 := by nlinarith
    rw [e27]
    nlinarith [mul_le_mul h9 hd2 (sq_nonneg _) (by positivity : (0 : ℝ) ≤ 3 ^ k)]
  set Y' : Config ct.V → ℝ := fun σ =>
    if wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 then Y σ else 0 with hY'
  set Z' : Config ct.V → ℝ := fun σ => |ct.Dstar σ| ^ c with hZ'
  have hY'0 : ∀ σ, 0 ≤ Y' σ := fun σ => by
    simp only [hY']
    split_ifs with h
    · exact (hY σ h).1
    · exact le_rfl
  have hZ'0 : ∀ σ, 0 ≤ Z' σ := fun σ => pow_nonneg (abs_nonneg _) c
  have hY'eq : ∀ σ, wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 → Y' σ = Y σ := fun σ h => by
    simp only [hY', h, ne_eq, not_false_eq_true, ↓reduceIte]
  have hD0 : ∀ σ, wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 → 0 ≤ ct.Dstar σ :=
    fun σ h => SecB.dstar_nonneg ct h
  have hYk : ct.E (fun σ => Y' σ ^ k) ≤ (27 * 12 ^ b * (d : ℝ) ^ a) ^ k := by
    calc ct.E (fun σ => Y' σ ^ k)
        ≤ ct.E (fun σ => (d : ℝ) ^ (a * k) * ct.Dstar σ ^ (b * k)) := by
          refine lx_E_mono ct fun σ hσ => ?_
          rw [hY'eq σ hσ, pow_mul, pow_mul, ← mul_pow]
          exact pow_le_pow_left₀ (hY σ hσ).1 (hY σ hσ).2 k
      _ = (d : ℝ) ^ (a * k) * ct.E (fun σ => ct.Dstar σ ^ (b * k)) := lx_E_const_mul ct _ _
      _ ≤ (d : ℝ) ^ (a * k) * (27 ^ k * 12 ^ (b * k)) := by
          gcongr
          calc ct.E (fun σ => ct.Dstar σ ^ (b * k))
              ≤ 3 * (1 + d + (d : ℝ) ^ 2) * 12 ^ (b * k) :=
                hDs _ (Nat.mul_pos (by omega) (by omega)) hbk
            _ ≤ 27 ^ k * 12 ^ (b * k) := by gcongr
      _ = (27 * 12 ^ b * (d : ℝ) ^ a) ^ k := by
          rw [pow_mul, pow_mul, mul_pow, mul_pow]; ring
  have hZk : ct.E (fun σ => Z' σ ^ k) ≤ (27 * 12 ^ c) ^ k := by
    calc ct.E (fun σ => Z' σ ^ k) = ct.E (fun σ => ct.Dstar σ ^ (c * k)) :=
          lx_E_congr ct fun σ hσ => by
            simp only [hZ']; rw [abs_of_nonneg (hD0 σ hσ), ← pow_mul]
      _ ≤ 3 * (1 + d + (d : ℝ) ^ 2) * 12 ^ (c * k) :=
          hDs _ (Nat.mul_pos (by omega) (by omega)) hck
      _ ≤ 27 ^ k * 12 ^ (c * k) := by gcongr
      _ = (27 * 12 ^ c) ^ k := by rw [pow_mul, mul_pow]
  have hθ : (0 : ℝ) < 1 / (d : ℝ) ^ e := by positivity
  have humi := wavg_mul_le_umi (fun σ => wt_nonneg ct.G σ) hZ hY'0 hZ'0 hk2
    (by positivity : (0 : ℝ) ≤ 27 * 12 ^ b * (d : ℝ) ^ a) (by positivity : (0 : ℝ) ≤ 27 * 12 ^ c)
    hθ hYk hZk
  have eL : ct.E (fun σ => ct.Dstar σ ^ c * Y σ) =
      wavg (fun σ => wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S) (fun σ => Y' σ * Z' σ) := by
    rw [← lawE_eq_wavg]
    exact lx_E_congr ct fun σ hσ => by
      simp only [hZ']; rw [hY'eq σ hσ, abs_of_nonneg (hD0 σ hσ)]; ring
  have eY : wavg (fun σ => wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S) Y' = ct.E Y := by
    rw [← lawE_eq_wavg]; exact lx_E_congr ct fun σ hσ => hY'eq σ hσ
  have hk1 : (1 : ℝ) ≤ (k : ℝ) - 1 := by linarith
  have hL1 : 1 / ((k : ℝ) - 1) ≤ 1 := by rw [div_le_one (by linarith)]; exact hk1
  have hlogL : Real.log d * (1 / ((k : ℝ) - 1)) ≤ 1 := by
    rw [mul_one_div, div_le_one (by linarith)]; linarith
  have hL : (27 * 12 ^ b * (d : ℝ) ^ a / (1 / (d : ℝ) ^ e)) ^ (1 / ((k : ℝ) - 1)) ≤
      27 * 12 ^ b * Real.exp (a + e) := by
    have eM : 27 * 12 ^ b * (d : ℝ) ^ a / (1 / (d : ℝ) ^ e) =
        (27 * 12 ^ b) * (d : ℝ) ^ (a + e) := by
      rw [pow_add]; field_simp
    rw [eM, Real.mul_rpow (by positivity) (by positivity)]
    have hA1 : (1 : ℝ) ≤ 27 * 12 ^ b := by
      have : (1 : ℝ) ≤ 12 ^ b := one_le_pow₀ (by norm_num)
      linarith
    have t1 : ((27 : ℝ) * 12 ^ b) ^ (1 / ((k : ℝ) - 1)) ≤ 27 * 12 ^ b := by
      calc ((27 : ℝ) * 12 ^ b) ^ (1 / ((k : ℝ) - 1)) ≤ (27 * 12 ^ b) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hA1 hL1
        _ = 27 * 12 ^ b := Real.rpow_one _
    have t2 : ((d : ℝ) ^ (a + e)) ^ (1 / ((k : ℝ) - 1)) ≤ Real.exp (a + e) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hd0.le, Real.rpow_def_of_pos hd0]
      apply Real.exp_le_exp.2
      push_cast
      have hae : (0 : ℝ) ≤ a + e := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hlogL hae]
    exact mul_le_mul t1 t2 (by positivity) (by positivity)
  rw [eL]
  refine humi.trans ?_
  rw [eY]
  have hEY : 0 ≤ ct.E Y + 1 / (d : ℝ) ^ e :=
    add_nonneg (lx_E_nonneg ct fun σ hσ => (hY σ hσ).1) hθ.le
  gcongr

/-- The mask vector `b = 4a² A_H diag(g) u` and its Hadamard energy: `b ≥ 0` and
`bᵀKb ≤ 16 d⁴ c³` for `0 ≤ g ≤ c`, `|K| ≤ c`. -/
theorem lx_bKb (hR : TRegime d p) {c : ℝ} (hc : 0 ≤ c) (g : ct.V → ℝ) (hg0 : ∀ l, 0 ≤ g l)
    (hg1 : ∀ l, g l ≤ c) (K : Matrix ct.V ct.V ℝ) (hK : ∀ i k, |K i k| ≤ c) :
    (∀ i, 0 ≤ ((4 * aOf d p ^ 2) • (ct.adjS *ᵥ (diagonal g *ᵥ ct.uvec))) i) ∧
      ((4 * aOf d p ^ 2) • (ct.adjS *ᵥ (diagonal g *ᵥ ct.uvec))) ⬝ᵥ
        (K *ᵥ ((4 * aOf d p ^ 2) • (ct.adjS *ᵥ (diagonal g *ᵥ ct.uvec)))) ≤
        16 * (d : ℝ) ^ 4 * c ^ 3 := by
  set b := (4 * aOf d p ^ 2) • (ct.adjS *ᵥ (diagonal g *ᵥ ct.uvec)) with hbdef
  have hd1 : (1 : ℝ) ≤ d := by have := hR.ten_pow_six_le_d; linarith
  have hd0 : (0 : ℝ) < d := by linarith
  have ha2 : aOf d p ^ 2 ≤ 1 := (lx_a2_le hR).trans (by rw [div_le_one hd0]; exact hd1)
  have hu0 : ∀ l, 0 ≤ ct.uvec l := fun l => by
    unfold Contact.uvec; split_ifs <;> positivity
  have hu1 : ∀ l, ct.uvec l ≤ if l ∈ ct.N then 1 else 0 := fun l => by
    unfold Contact.uvec
    split_ifs
    · rw [div_le_one (Real.sqrt_pos.2 hd0)]; exact Real.one_le_sqrt.2 hd1
    · exact le_rfl
  have hA0 : ∀ i l, 0 ≤ ct.adjS i l := fun i l => by
    unfold Contact.adjS; simp only [Matrix.of_apply]; split_ifs <;> norm_num
  have hcol : ∀ l, ∑ i, ct.adjS i l ≤ d := fun l => by
    unfold Contact.adjS
    simp only [Matrix.of_apply]
    rw [Finset.sum_boole]
    have h1 : (Finset.univ.filter fun i => i ∈ ct.S ∧ l ∈ ct.S ∧ ct.G.Adj i l) ⊆
        ct.G.neighborFinset l := by
      intro i hi
      simp only [Finset.mem_filter] at hi
      rw [SimpleGraph.mem_neighborFinset]
      exact hi.2.2.2.symm
    have h2 := Finset.card_le_card h1
    rw [SimpleGraph.card_neighborFinset_eq_degree] at h2
    exact_mod_cast h2.trans (ct.ctx.deg l)
  have hb : ∀ i, b i = 4 * aOf d p ^ 2 * ∑ l, ct.adjS i l * (g l * ct.uvec l) := fun i => by
    simp only [hbdef, Pi.smul_apply, smul_eq_mul, mulVec, dotProduct, Matrix.diagonal_apply,
      ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  have hb0 : ∀ i, 0 ≤ b i := fun i => by
    rw [hb]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun l _ =>
      mul_nonneg (hA0 i l) (mul_nonneg (hg0 l) (hu0 l)))
  refine ⟨hb0, ?_⟩
  have hwl : ∀ l, g l * ct.uvec l ≤ if l ∈ ct.N then c else 0 := fun l => by
    have := hu1 l
    split_ifs at this ⊢
    · nlinarith [hg0 l, hg1 l, hu0 l]
    · have : ct.uvec l = 0 := le_antisymm this (hu0 l)
      rw [this, mul_zero]
  have hsum : ∑ i, b i ≤ 4 * (d : ℝ) ^ 2 * c := by
    simp only [hb]
    rw [← Finset.mul_sum, Finset.sum_comm]
    simp only [← Finset.sum_mul]
    have h1 : ∑ l, (∑ i, ct.adjS i l) * (g l * ct.uvec l) ≤
        ∑ l, (d : ℝ) * (if l ∈ ct.N then c else 0) := Finset.sum_le_sum fun l _ =>
      mul_le_mul (hcol l) (hwl l) (mul_nonneg (hg0 l) (hu0 l)) hd0.le
    have h2 : ∑ l, (d : ℝ) * (if l ∈ ct.N then c else 0) = d * (ct.N.card * c) := by
      rw [← Finset.mul_sum, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
        nsmul_eq_mul]
    have h3 : (d : ℝ) * (ct.N.card * c) ≤ d * (d * c) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (lx_card_N ct) hc) hd0.le
    have h4 : 0 ≤ ∑ l, (∑ i, ct.adjS i l) * (g l * ct.uvec l) :=
      Finset.sum_nonneg fun l _ => mul_nonneg (Finset.sum_nonneg fun i _ => hA0 i l)
        (mul_nonneg (hg0 l) (hu0 l))
    calc 4 * aOf d p ^ 2 * ∑ l, (∑ i, ct.adjS i l) * (g l * ct.uvec l)
        ≤ 4 * 1 * (d * (d * c)) := by
          apply mul_le_mul (by linarith) (h1.trans (h2 ▸ h3)) h4 (by norm_num)
      _ = 4 * (d : ℝ) ^ 2 * c := by ring
  have hS0 : 0 ≤ ∑ i, b i := Finset.sum_nonneg fun i _ => hb0 i
  have hbKb : b ⬝ᵥ (K *ᵥ b) ≤ c * (∑ i, b i) ^ 2 := by
    simp only [dotProduct, mulVec]
    calc ∑ i, b i * ∑ k, K i k * b k ≤ ∑ i, b i * ∑ k, c * b k := by
          refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum fun k _ => ?_) (hb0 i)
          exact mul_le_mul_of_nonneg_right ((le_abs_self _).trans (hK i k)) (hb0 k)
      _ = c * (∑ i, b i) ^ 2 := by
          rw [sq, ← Finset.sum_mul, ← Finset.mul_sum]
          simp only [Finset.mul_sum, Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
  calc b ⬝ᵥ (K *ᵥ b) ≤ c * (∑ i, b i) ^ 2 := hbKb
    _ ≤ c * (4 * (d : ℝ) ^ 2 * c) ^ 2 := by gcongr
    _ = 16 * (d : ℝ) ^ 4 * c ^ 3 := by ring

/-- Row bounds at a neighbour of the root, on the support (`|G_vi|² ≤ G_vv G_ii ≤ D_*²`). -/
theorem lx_row_bounds (hR : TRegime d p) {σ : Config ct.V}
    (hσ : wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0) {i : ct.V} (hi : i ∈ ct.N) :
    ct.x σ i ^ 2 ≤ ct.Dstar σ ^ 2 ∧ ct.z σ i ^ 2 ≤ ct.Dstar σ ^ 2 ∧
      0 ≤ ct.gp σ ct.v ct.v * ct.gp σ i i ∧ ct.gp σ ct.v ct.v * ct.gp σ i i ≤ ct.Dstar σ ^ 2 ∧
      0 ≤ ct.gm σ ct.v ct.v * ct.gm σ i i ∧ ct.gm σ ct.v ct.v * ct.gm σ i i ≤ ct.Dstar σ ^ 2 ∧
      0 ≤ ct.Dstar σ := by
  obtain ⟨hP, hM⟩ := SecB.posDef_of_wt_ne_zero ct.G hσ
  have hyp0 : ∀ k, 0 ≤ ct.yp k := fun k => (lx_src ct hR k).1.1
  have hym0 : ∀ k, 0 ≤ ct.ym k := fun k => (lx_src ct hR k).2.1
  obtain ⟨⟨-, hXv0, hXGv, -⟩, ⟨-, hYv0, hYGv, -⟩⟩ := lx_supp ct hR le_rfl hσ ct.v
  obtain ⟨⟨-, hXi0, hXGi, -⟩, ⟨-, hYi0, hYGi, -⟩⟩ := lx_supp ct hR le_rfl hσ i
  obtain ⟨dA, dC⟩ := lx_dstar_ge ct σ (lx_mem_ball_v ct)
  obtain ⟨dB, dD⟩ := lx_dstar_ge ct σ (lx_mem_ball_N ct hi)
  have hxs : ct.x σ i ^ 2 ≤ ct.gp σ ct.v ct.v * ct.gp σ i i :=
    SecB.greenP_sq_le ct.G hP hyp0 ct.v i
  have hzs : ct.z σ i ^ 2 ≤ ct.gm σ ct.v ct.v * ct.gm σ i i :=
    SecB.greenP_sq_le ct.G hM hym0 ct.v i
  have hA0 : 0 ≤ ct.gp σ ct.v ct.v := hXv0.trans hXGv
  have hB0 : 0 ≤ ct.gp σ i i := hXi0.trans hXGi
  have hC0 : 0 ≤ ct.gm σ ct.v ct.v := hYv0.trans hYGv
  have hD0 : 0 ≤ ct.gm σ i i := hYi0.trans hYGi
  have hAB : ct.gp σ ct.v ct.v * ct.gp σ i i ≤ ct.Dstar σ ^ 2 := by
    have := mul_le_mul (show ct.gp σ ct.v ct.v ≤ ct.Dstar σ by linarith)
      (show ct.gp σ i i ≤ ct.Dstar σ by linarith) hB0 (by linarith)
    nlinarith
  have hCD : ct.gm σ ct.v ct.v * ct.gm σ i i ≤ ct.Dstar σ ^ 2 := by
    have := mul_le_mul (show ct.gm σ ct.v ct.v ≤ ct.Dstar σ by linarith)
      (show ct.gm σ i i ≤ ct.Dstar σ by linarith) hD0 (by linarith)
    nlinarith
  exact ⟨hxs.trans hAB, hzs.trans hCD, mul_nonneg hA0 hB0, hAB, mul_nonneg hC0 hD0, hCD,
    by linarith⟩

/-- The pointwise bound on `|K_i|` at a neighbour, on the support: the row-free part by the
moments of the normalized diagonals, the rest by `lx_kpoly_rest`. -/
theorem lx_kpoly_pt (hR : TRegime d p) {σ : Config ct.V}
    (hσ : wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0) {i : ct.V} (hi : i ∈ ct.N) :
    |Kpoly p (ct.x σ i) (ct.z σ i) (ct.gp σ ct.v ct.v * ct.gp σ i i)
        (ct.gm σ ct.v ct.v * ct.gm σ i i)| ≤
      72 * p * (hN ct.G (aOf d p) 1 ct.yp σ ct.S ct.v ^ 4 +
        hN ct.G (aOf d p) 1 ct.yp σ ct.S i ^ 4 +
        hN ct.G (aOf d p) (-1) ct.ym σ ct.S ct.v ^ 4 +
        hN ct.G (aOf d p) (-1) ct.ym σ ct.S i ^ 4) +
      300 * (p : ℝ) ^ 3 * (ct.Dstar σ ^ 2 * (ct.x σ i ^ 2 + ct.z σ i ^ 2)) := by
  have hp1 : 1 ≤ p := le_trans (by norm_num) hR.hp
  have hq1 : (1 : ℝ) ≤ p := by exact_mod_cast hp1
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  obtain ⟨hx2, hz2, hAB0, hAB, hCD0, hCD, hD0⟩ := lx_row_bounds ct hR hσ hi
  obtain ⟨⟨a0, hXv0, hXGv, a2⟩, ⟨c0, hYv0, hYGv, c2⟩⟩ := lx_supp ct hR le_rfl hσ ct.v
  obtain ⟨⟨b0, hXi0, hXGi, b2⟩, ⟨e0, hYi0, hYGi, e2⟩⟩ := lx_supp ct hR le_rfl hσ i
  have hx : |ct.x σ i| ≤ ct.Dstar σ := (sq_le_sq.mp hx2).trans_eq (abs_of_nonneg hD0)
  have hz : |ct.z σ i| ≤ ct.Dstar σ := (sq_le_sq.mp hz2).trans_eq (abs_of_nonneg hD0)
  have hPa : |ct.gp σ ct.v ct.v * ct.gp σ i i| ≤ ct.Dstar σ ^ 2 := by
    rw [abs_of_nonneg hAB0]; exact hAB
  have hQa : |ct.gm σ ct.v ct.v * ct.gm σ i i| ≤ ct.Dstar σ ^ 2 := by
    rw [abs_of_nonneg hCD0]; exact hCD
  have hrest := lx_kpoly_rest hp1 hx hz hPa hQa
  set A := ct.gp σ ct.v ct.v
  set B := ct.gp σ i i
  set Cm := ct.gm σ ct.v ct.v
  set Dm := ct.gm σ i i
  set ha := hN ct.G (aOf d p) 1 ct.yp σ ct.S ct.v
  set hb := hN ct.G (aOf d p) 1 ct.yp σ ct.S i
  set hc := hN ct.G (aOf d p) (-1) ct.ym σ ct.S ct.v
  set he := hN ct.G (aOf d p) (-1) ct.ym σ ct.S i
  have hB0 : 0 ≤ B := hXi0.trans hXGi
  have hD0' : 0 ≤ Dm := hYi0.trans hYGi
  have hp1' : 0 ≤ (p : ℝ) - 1 := by linarith
  have hRF0 : 0 ≤ 6 * (((p : ℝ) - 1) * (A * B) ^ 2 + p * (A * B) * (Cm * Dm)) :=
    mul_nonneg (by norm_num) (add_nonneg (mul_nonneg hp1' (sq_nonneg _))
      (mul_nonneg (mul_nonneg hp0 hAB0) hCD0))
  have hRF : 6 * (((p : ℝ) - 1) * (A * B) ^ 2 + p * (A * B) * (Cm * Dm)) ≤
      6 * p * ((A * B) ^ 2 + (A * B) * (Cm * Dm)) := by
    linarith [sq_nonneg (A * B)]
  have hPP : (A * B) ^ 2 + (A * B) * (Cm * Dm) ≤ 12 * (ha ^ 4 + hb ^ 4 + hc ^ 4 + he ^ 4) := by
    have h1 : A * B ≤ (2 * ha) * (2 * hb) := mul_le_mul a2 b2 hB0 (by linarith)
    have h2 : Cm * Dm ≤ (2 * hc) * (2 * he) := mul_le_mul c2 e2 hD0' (by linarith)
    have h3 : (A * B) ^ 2 ≤ ((2 * ha) * (2 * hb)) ^ 2 := pow_le_pow_left₀ hAB0 h1 2
    have h4 : (A * B) * (Cm * Dm) ≤ ((2 * ha) * (2 * hb)) * ((2 * hc) * (2 * he)) :=
      mul_le_mul h1 h2 hCD0 (mul_nonneg (by linarith) (by linarith))
    have h5 := lx_amgm2 ha hb
    have h6 := lx_amgm4 ha hb hc he
    have h7 : 0 ≤ hc ^ 4 := by positivity
    have h8 : 0 ≤ he ^ 4 := by positivity
    linarith
  have t1 : 6 * (((p : ℝ) - 1) * (A * B) ^ 2 + p * (A * B) * (Cm * Dm)) ≤
      72 * p * (ha ^ 4 + hb ^ 4 + hc ^ 4 + he ^ 4) := by
    have := mul_le_mul_of_nonneg_left hPP (by positivity : (0 : ℝ) ≤ 6 * p)
    linarith
  have t2 := abs_le.1 hrest
  rw [abs_le]
  constructor <;> linarith

/-- The per-neighbour estimate `|E K_i| ≤ 4608 p + 300 p³ K_U (E x_i² + E z_i² + ϑ)`. -/
theorem lx_kpoly_E (hR : TRegime d p)
    (hDs : ∀ n : ℕ, 1 ≤ n → 2 * n ≤ p →
      ct.E (fun σ => ct.Dstar σ ^ n) ≤ 3 * (1 + d + (d : ℝ) ^ 2) * 12 ^ n)
    {k : ℕ} (hk1 : Real.log d + 2 ≤ k) (hbk : 2 * (2 * k) ≤ p) {i : ct.V} (hi : i ∈ ct.N) :
    |ct.E (fun σ => Kpoly p (ct.x σ i) (ct.z σ i)
      (ct.gp σ ct.v ct.v * ct.gp σ i i) (ct.gm σ ct.v ct.v * ct.gm σ i i))| ≤
      4608 * p + 300 * (p : ℝ) ^ 3 *
        (27 * 12 ^ 2 * (27 * 12 ^ 2 * Real.exp (((1 : ℕ) : ℝ) + ((10 : ℕ) : ℝ))) *
          (ct.E (fun σ => ct.x σ i ^ 2) + ct.E (fun σ => ct.z σ i ^ 2) + vth d)) := by
  have hiS := lx_N_sub ct hi
  have hv := ct.ctx.mem
  have hd2 : (2 : ℝ) ≤ d := by have := hR.ten_pow_six_le_d; linarith
  have h16 : ∀ w ∈ ct.S,
      ct.E (fun σ => hN ct.G (aOf d p) 1 ct.yp σ ct.S w ^ 4) ≤ 16 ∧
        ct.E (fun σ => hN ct.G (aOf d p) (-1) ct.ym σ ct.S w ^ 4) ≤ 16 := by
    intro w hw
    have h24 : (2 : ℝ) ^ 4 = 16 := by norm_num
    rw [← h24]
    exact lx_F2 ct hR hw (k := 4) (by norm_num) (le_trans (by norm_num) hR.hp)
  have hU := lx_umi ct hR hDs hk1 (a := 1) (b := 2) (c := 2) (e := 10) (by norm_num)
    (by norm_num) hbk hbk (fun σ => ct.x σ i ^ 2 + ct.z σ i ^ 2) (fun σ hσ => by
      obtain ⟨hx2, hz2, -, -, -, -, -⟩ := lx_row_bounds ct hR hσ hi
      refine ⟨by positivity, ?_⟩
      rw [pow_one]
      nlinarith [sq_nonneg (ct.Dstar σ)])
  calc |ct.E (fun σ => Kpoly p (ct.x σ i) (ct.z σ i)
        (ct.gp σ ct.v ct.v * ct.gp σ i i) (ct.gm σ ct.v ct.v * ct.gm σ i i))|
      ≤ ct.E (fun σ => |Kpoly p (ct.x σ i) (ct.z σ i)
        (ct.gp σ ct.v ct.v * ct.gp σ i i) (ct.gm σ ct.v ct.v * ct.gm σ i i)|) :=
        SecB.abs_lawE_le ct.G _
    _ ≤ ct.E (fun σ => 72 * p * (hN ct.G (aOf d p) 1 ct.yp σ ct.S ct.v ^ 4 +
        hN ct.G (aOf d p) 1 ct.yp σ ct.S i ^ 4 +
        hN ct.G (aOf d p) (-1) ct.ym σ ct.S ct.v ^ 4 +
        hN ct.G (aOf d p) (-1) ct.ym σ ct.S i ^ 4) +
        300 * (p : ℝ) ^ 3 * (ct.Dstar σ ^ 2 * (ct.x σ i ^ 2 + ct.z σ i ^ 2))) :=
        lx_E_mono ct fun σ hσ => lx_kpoly_pt ct hR hσ hi
    _ = 72 * p * (ct.E (fun σ => hN ct.G (aOf d p) 1 ct.yp σ ct.S ct.v ^ 4) +
        ct.E (fun σ => hN ct.G (aOf d p) 1 ct.yp σ ct.S i ^ 4) +
        ct.E (fun σ => hN ct.G (aOf d p) (-1) ct.ym σ ct.S ct.v ^ 4) +
        ct.E (fun σ => hN ct.G (aOf d p) (-1) ct.ym σ ct.S i ^ 4)) +
        300 * (p : ℝ) ^ 3 * ct.E (fun σ => ct.Dstar σ ^ 2 * (ct.x σ i ^ 2 + ct.z σ i ^ 2)) := by
        rw [lx_E_add, lx_E_const_mul, lx_E_const_mul, lx_E_add, lx_E_add, lx_E_add]
    _ ≤ 72 * p * (16 + 16 + 16 + 16) +
        300 * (p : ℝ) ^ 3 *
          (27 * 12 ^ 2 * (27 * 12 ^ 2 * Real.exp (((1 : ℕ) : ℝ) + ((10 : ℕ) : ℝ))) *
            (ct.E (fun σ => ct.x σ i ^ 2 + ct.z σ i ^ 2) + 1 / (d : ℝ) ^ 10)) := by
        gcongr
        · exact (h16 _ hv).1
        · exact (h16 _ hiS).1
        · exact (h16 _ hv).2
        · exact (h16 _ hiS).2
    _ = _ := by rw [lx_E_add]; unfold vth; ring

end Contact2

/-- The final arithmetic of `qstar_bound`. -/
theorem lx_qstar_arith {A n S Sm θ δ p K C₂ : ℝ} (hA0 : 0 ≤ A) (hAn : A * n ≤ 1)
    (hS : A * S ≤ C₂ * δ) (hSm : A * Sm ≤ C₂ * δ) (hθ : θ ≤ δ) (hθ0 : 0 ≤ θ) (hp0 : 0 ≤ p)
    (hK0 : 0 ≤ K) (hC₂ : 0 ≤ C₂) :
    A * A / 3 * (4608 * p * n + 300 * p ^ 3 * K * (S + Sm + n * θ)) ≤
      (1536 + 100 * K * (2 * C₂ + 1)) * A * (p + p ^ 3 * δ) := by
  have hδ0 : 0 ≤ δ := hθ0.trans hθ
  have hp3 : 0 ≤ p ^ 3 := by positivity
  have b1 : A * (A * n) ≤ A := by nlinarith
  have b2 : A * (A * S) ≤ A * (C₂ * δ) := mul_le_mul_of_nonneg_left hS hA0
  have b3 : A * (A * Sm) ≤ A * (C₂ * δ) := mul_le_mul_of_nonneg_left hSm hA0
  have b4 : A * (A * n) * θ ≤ A * δ := by
    have h1 : A * (A * n) * θ ≤ A * θ := mul_le_mul_of_nonneg_right b1 hθ0
    have h2 : A * θ ≤ A * δ := mul_le_mul_of_nonneg_left hθ hA0
    linarith
  have hpK : 0 ≤ 100 * p ^ 3 * K := by positivity
  have key : A * A / 3 * (4608 * p * n + 300 * p ^ 3 * K * (S + Sm + n * θ)) =
      1536 * p * (A * (A * n)) + 100 * p ^ 3 * K *
        (A * (A * S) + A * (A * Sm) + A * (A * n) * θ) := by ring
  rw [key]
  have s1 : 1536 * p * (A * (A * n)) ≤ 1536 * p * A :=
    mul_le_mul_of_nonneg_left b1 (by positivity)
  have s2 : 100 * p ^ 3 * K * (A * (A * S) + A * (A * Sm) + A * (A * n) * θ) ≤
      100 * p ^ 3 * K * (A * (C₂ * δ) + A * (C₂ * δ) + A * δ) :=
    mul_le_mul_of_nonneg_left (add_le_add (add_le_add b2 b3) b4) hpK
  have s3 : 0 ≤ A * p := mul_nonneg hA0 hp0
  have s4 : 0 ≤ A * (p ^ 3 * δ) := mul_nonneg hA0 (mul_nonneg hp3 hδ0)
  have hC0 : 0 ≤ 100 * K * (2 * C₂ + 1) := by positivity
  have s5 := mul_le_mul_of_nonneg_left (show (1536 : ℝ) ≤ 1536 + 100 * K * (2 * C₂ + 1) by
    linarith) s3
  have s6 := mul_le_mul_of_nonneg_right
    (show 100 * K * (2 * C₂ + 1) ≤ 1536 + 100 * K * (2 * C₂ + 1) by linarith) s4
  linarith

end Helpers

/-- **L-QSTAR** (source l.1414–1422; AUDIT-C §6 QSTAR, AUDIT-D §3.1 "|Q_*| bound"). The row-free
part of `K_i` is `6[(p-1)P_i² + pP_iQ_i]`; every other monomial has two root-row factors and a
coefficient of degree `≤ 3` in `p`. With (C2) and interpolation:
`|Q_*| ≤ C a² (p + p³ δ̄)`. -/
theorem qstar_bound : ∃ C : ℝ, 0 < C ∧ Eventually fun _c₀ _κ₀ d p _h =>
    ∀ ct : Contact.{u} d p,
      |ct.Qstar| ≤ C * aOf d p ^ 2 * (p + (p : ℝ) ^ 3 * dbar d p) := by
  obtain ⟨C₂, hC₂, hc2⟩ := in_C2.{u}
  obtain ⟨KU, hKU0, hKU⟩ : ∃ KU : ℝ, 0 ≤ KU ∧
      KU = 27 * 12 ^ 2 * (27 * 12 ^ 2 * Real.exp (((1 : ℕ) : ℝ) + ((10 : ℕ) : ℝ))) :=
    ⟨_, by positivity, rfl⟩
  have hC0 : 0 ≤ 100 * KU * (2 * C₂ + 1) :=
    mul_nonneg (mul_nonneg (by norm_num) hKU0) (by linarith)
  refine ⟨1536 + 100 * KU * (2 * C₂ + 1), by linarith, ?_⟩
  refine (((hc2.and SecB.dstar_moment).and (SecB.eventually_log_le_p 4)).and
    (SecB.eventually_base 0)).mono ?_
  rintro c₀ κ₀ d p h ⟨⟨⟨hC2, hDs⟩, hlp⟩, hR, -⟩ ct
  obtain ⟨hS, hSm, -, -⟩ := hC2 ct
  obtain ⟨k, hk1, hk4⟩ := lx_choose_k hR (by norm_num : (0 : ℝ) ≤ 4) hlp
  have hk4' : 4 * k ≤ p := by exact_mod_cast hk4
  have hbk : 2 * (2 * k) ≤ p := by omega
  have hd1 : (1 : ℝ) ≤ d := by have := hR.ten_pow_six_le_d; linarith
  have hd0 : (0 : ℝ) < d := by linarith
  have hp1 : 1 ≤ p := le_trans (by norm_num) hR.hp
  have hq1 : (1 : ℝ) ≤ p := by exact_mod_cast hp1
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hKi : ∀ i ∈ ct.N, |ct.E (fun σ => Kpoly p (ct.x σ i) (ct.z σ i)
      (ct.gp σ ct.v ct.v * ct.gp σ i i) (ct.gm σ ct.v ct.v * ct.gm σ i i))| ≤
      4608 * p + 300 * (p : ℝ) ^ 3 * (KU * (ct.E (fun σ => ct.x σ i ^ 2) +
        ct.E (fun σ => ct.z σ i ^ 2) + vth d)) := fun i hi => by
    rw [hKU]; exact lx_kpoly_E ct hR (hDs ct) hk1 hbk hi
  have e : ∑ i ∈ ct.N, (4608 * (p : ℝ) + 300 * (p : ℝ) ^ 3 * (KU * (ct.E (fun σ => ct.x σ i ^ 2) +
      ct.E (fun σ => ct.z σ i ^ 2) + vth d))) =
      4608 * p * ct.N.card + 300 * (p : ℝ) ^ 3 * KU * (ct.Srow + ct.Smin + ct.N.card * vth d) := by
    unfold Contact.Srow Contact.Smin
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum,
      ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const,
      nsmul_eq_mul]
    ring
  have hA0 : 0 ≤ aOf d p ^ 2 := sq_nonneg _
  have hAd : aOf d p ^ 2 * ct.N.card ≤ 1 := by
    calc aOf d p ^ 2 * ct.N.card ≤ aOf d p ^ 2 * d :=
          mul_le_mul_of_nonneg_left (lx_card_N ct) hA0
      _ ≤ 1 / d * d := mul_le_mul_of_nonneg_right (lx_a2_le hR) hd0.le
      _ = 1 := by field_simp
  have hvth : vth d ≤ dbar d p := by
    have h1 : vth d ≤ 1 / (d : ℝ) := by
      unfold vth; exact one_div_le_one_div_of_le hd0 (le_self_pow₀ hd1 (by norm_num))
    have h2 : 1 / (d : ℝ) ≤ (p : ℝ) ^ 4 / d :=
      div_le_div_of_nonneg_right (one_le_pow₀ hq1) hd0.le
    exact h1.trans (h2.trans (SecB.le_dbar hR).2)
  have hvth0 : 0 ≤ vth d := by unfold vth; positivity
  have hsum : |ct.Qstar| ≤ aOf d p ^ 4 / 3 *
      (4608 * p * ct.N.card + 300 * (p : ℝ) ^ 3 * KU *
        (ct.Srow + ct.Smin + ct.N.card * vth d)) := by
    unfold Contact.Qstar
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ aOf d p ^ 4 / 3), ← e]
    gcongr
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hKi)
  refine hsum.trans ?_
  rw [show aOf d p ^ 4 = aOf d p ^ 2 * aOf d p ^ 2 by ring]
  exact lx_qstar_arith hA0 hAd hS hSm hvth hvth0 hp0 hKU0 hC₂.le

/-- **L-D10corr** (source l.1532–1545; AUDIT-C §6 (D10), AUDIT-D §3.1 D9b). With
`Δ_± = X_±[N,N] - Y_± ⪰ 0`, (C5) gives `tr Δ_± ≤ h⁻¹ Z_v^±(G^±_vv - X^±_vv)`, and (S1) with
interpolation gives `E[Ω tr Δ_±] ≤ C h^{-1/2}`; expanding the trace products with `‖·‖ ≤ h⁻¹`:
`L_d[(p-1)q₊ + p q₋] (= Q_full) ≤ Q + C p/(d h^{3/2})`. -/
theorem d10_corr : ∃ C : ℝ, 0 < C ∧ Eventually fun _c₀ _κ₀ d p h =>
    ∀ ct : Contact.{u} d p,
      LdP d p * (((p : ℝ) - 1) * ct.qP h + p * ct.qM h) ≤
        ct.Qbl h + C * p / (d * h * Real.sqrt h) := by
  obtain ⟨K, hK, hCL⟩ := SecB.cl1_bridge.{u}
  have hKS := SecB.one_le_s1K hK
  refine ⟨6144 * (SecB.s1K K + 2), by linarith, ?_⟩
  refine (((SecB.mean_shift_weighted_of_cl1 hK zero_le_one one_pos hCL).and
    (SecB.eventually_log_le_p 6)).and lx_ev_h).mono ?_
  rintro c₀ κ₀ d p h ⟨⟨hW, hlp⟩, hR, hh, hh2, hhd⟩ ct
  obtain ⟨k, hk1, hk6⟩ := lx_choose_k hR (by norm_num : (0 : ℝ) ≤ 6) hlp
  have hk6' : 6 * k ≤ p := by exact_mod_cast hk6
  have hk2 : 2 * k ≤ p := by omega
  have hk3 : 2 * (3 * k) ≤ p := by omega
  have hd1 : (1 : ℝ) ≤ d := by have := hR.ten_pow_six_le_d; linarith
  have hd0 : (0 : ℝ) < d := by linarith
  have hkpos : 1 ≤ 3 * k := by
    have : (1 : ℝ) ≤ k := by have := Real.log_nonneg hd1; linarith
    have : 1 ≤ k := by exact_mod_cast this
    omega
  have hv := ct.ctx.mem
  have hp1 : 1 ≤ p := le_trans (by norm_num) hR.hp
  have hq1 : (1 : ℝ) ≤ p := by exact_mod_cast hp1
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hp1' : 0 ≤ (p : ℝ) - 1 := by linarith
  have hyp0 : ∀ k, 0 ≤ ct.yp k := fun k => (lx_src ct hR k).1.1
  have hym0 : ∀ k, 0 ≤ ct.ym k := fun k => (lx_src ct hR k).2.1
  have hinv0 : 0 ≤ h⁻¹ := inv_nonneg.2 hh.le
  have hyq : ∀ k, (0 ≤ ct.yp k ∧ ct.yp k ≤ h⁻¹) ∧ (0 ≤ ct.ym k ∧ ct.ym k ≤ h⁻¹) := fun k => by
    obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ := lx_src ct hR k
    have : (2 : ℝ) ≤ h⁻¹ := by rw [le_inv_comm₀ (by norm_num) hh]; linarith
    exact ⟨⟨a1, by linarith⟩, ⟨b1, by linarith⟩⟩
  set KS := SecB.s1K K
  have hKS2 : 0 ≤ KS + 2 := by linarith
  have hZ := lx_Zw ct hR
  have h8 : ct.E (fun σ => hN ct.G (aOf d p) 1 ct.yp σ ct.S ct.v ^ (3 * k)) ≤ 8 ^ k ∧
      ct.E (fun σ => hN ct.G (aOf d p) (-1) ct.ym σ ct.S ct.v ^ (3 * k)) ≤ 8 ^ k := by
    have e : (2 : ℝ) ^ (3 * k) = 8 ^ k := by rw [pow_mul]; norm_num
    rw [← e]
    exact lx_F2 ct hR hv hkpos hk3
  have h1E : ct.E (fun _ : Config ct.V => (1 : ℝ) ^ (3 * k)) ≤ 8 ^ k := by
    rw [one_pow, lx_E_const ct hZ]; exact one_le_pow₀ (by norm_num)
  have hS1 : ∀ Z : Config ct.V → ℝ, (∀ σ, 0 ≤ Z σ) → ct.E (fun σ => Z σ ^ k) ≤ 128 ^ k →
      ct.E (fun σ => (ct.gp σ ct.v ct.v - ct.XP h σ ct.v ct.v) * Z σ) ≤
          768 * (KS + 2) * Real.sqrt h ∧
        ct.E (fun σ => (ct.gm σ ct.v ct.v - ct.XM h σ ct.v ct.v) * Z σ) ≤
          768 * (KS + 2) * Real.sqrt h := by
    intro Z hZ0 hZk
    obtain ⟨h1, h2⟩ := hW ct.toCapPoint ct.v hv k hk1 hk2 Z hZ0 128 (by norm_num) hZk
    obtain ⟨⟨-, hyv⟩, ⟨-, hymv⟩⟩ := lx_src ct hR ct.v
    have hc : 0 ≤ 3 * (KS + 2) * 128 * Real.sqrt h := by
      have := mul_nonneg hKS2 (Real.sqrt_nonneg h); nlinarith
    constructor
    · refine le_trans (show ct.E (fun σ => (ct.gp σ ct.v ct.v - ct.XP h σ ct.v ct.v) * Z σ) ≤
        3 * (KS + 2) * 128 * Real.sqrt h * ct.yp ct.v from h1) ?_
      nlinarith [mul_nonneg hc (sub_nonneg.2 hyv)]
    · refine le_trans (show ct.E (fun σ => (ct.gm σ ct.v ct.v - ct.XM h σ ct.v ct.v) * Z σ) ≤
        3 * (KS + 2) * 128 * Real.sqrt h * ct.ym ct.v from h2) ?_
      nlinarith [mul_nonneg hc (sub_nonneg.2 hymv)]
  -- the integrands
  set F₁ : Config ct.V → ℝ := fun σ =>
    ((p : ℝ) - 1) * ct.gp σ ct.v ct.v ^ 2 * ∑ i ∈ ct.N, ∑ j ∈ ct.N, ct.XP h σ i j ^ 2 +
      p * ct.gp σ ct.v ct.v * ct.gm σ ct.v ct.v *
        ∑ i ∈ ct.N, ∑ j ∈ ct.N, ct.XP h σ i j * ct.XM h σ i j with hF₁
  set F₂ : Config ct.V → ℝ := fun σ =>
    ((p : ℝ) - 1) * ct.gp σ ct.v ct.v ^ 2 * ∑ i ∈ ct.N, ∑ j ∈ ct.N, ct.YP h σ i j ^ 2 +
      p * ct.gp σ ct.v ct.v * ct.gm σ ct.v ct.v *
        ∑ i ∈ ct.N, ∑ j ∈ ct.N, ct.YP h σ i j * ct.YM h σ i j with hF₂
  set Z₁ : Config ct.V → ℝ := fun σ => ct.yp ct.v * hN ct.G (aOf d p) 1 ct.yp σ ct.S ct.v ^ 2
    with hZ₁
  set Z₂ : Config ct.V → ℝ := fun σ =>
    |ct.gm σ ct.v ct.v| * |hN ct.G (aOf d p) 1 ct.yp σ ct.S ct.v| with hZ₂
  set Z₃ : Config ct.V → ℝ := fun σ =>
    |ct.gp σ ct.v ct.v| * |hN ct.G (aOf d p) (-1) ct.ym σ ct.S ct.v| with hZ₃
  set Bd : Config ct.V → ℝ := fun σ => h⁻¹ ^ 2 *
    (4 * ((p : ℝ) - 1) * ((ct.gp σ ct.v ct.v - ct.XP h σ ct.v ct.v) * Z₁ σ) +
      2 * p * ((ct.gp σ ct.v ct.v - ct.XP h σ ct.v ct.v) * Z₂ σ) +
      2 * p * ((ct.gm σ ct.v ct.v - ct.XM h σ ct.v ct.v) * Z₃ σ)) with hBd
  -- the pointwise comparison of the full and core trace budgets
  have hpt : ∀ σ, wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 → F₁ σ - F₂ σ ≤ Bd σ := by
    intro σ hσ
    obtain ⟨hP, hM⟩ := SecB.posDef_of_wt_ne_zero ct.G hσ
    obtain ⟨⟨hp0', hXv0, hXGv, -⟩, ⟨hm0', hYv0, hYGv, -⟩⟩ := lx_supp ct hR hh.le hσ ct.v
    have hG0 : 0 ≤ ct.gp σ ct.v ct.v := hXv0.trans hXGv
    have hGm0 : 0 ≤ ct.gm σ ct.v ct.v := hYv0.trans hYGv
    have hXPn : ∀ w, w ⬝ᵥ (ct.XP h σ *ᵥ w) ≤ h⁻¹ * (w ⬝ᵥ w) :=
      lx_shift_quad ct.G (fun k => (hyq k).1) hh hP
    have hXMn : ∀ w, w ⬝ᵥ (ct.XM h σ *ᵥ w) ≤ h⁻¹ * (w ⬝ᵥ w) :=
      lx_shift_quad ct.G (fun k => (hyq k).2) hh hM
    obtain ⟨ωp, hωp⟩ := lx_rank_one ct.G ct.v hyp0 hh.le hP
    obtain ⟨ωm, hωm⟩ := lx_rank_one ct.G ct.v hym0 hh.le hM
    have hXYp : ∀ i ∈ ct.N, ∀ j ∈ ct.N, ct.XP h σ i j = ct.YP h σ i j + ωp i * ωp j :=
      fun i hi j hj => hωp i (FloorIns.ne_of_mem_nbhd ct.G hi) j (FloorIns.ne_of_mem_nbhd ct.G hj)
    have hXYm : ∀ i ∈ ct.N, ∀ j ∈ ct.N, ct.XM h σ i j = ct.YM h σ i j + ωm i * ωm j :=
      fun i hi j hj => hωm i (FloorIns.ne_of_mem_nbhd ct.G hi) j (FloorIns.ne_of_mem_nbhd ct.G hj)
    have hA := lx_rank_one_sum ct.N (ct.XP h σ) (ct.YP h σ) ωp hXYp hXPn
    have hB := lx_rank_one_mixed ct.N (ct.XP h σ) (ct.XM h σ) (ct.YP h σ) (ct.YM h σ) ωp ωm
      hXYp hXYm hXPn hXMn
    -- the traces of the corrections, (C5c)
    have hyS : InCube (sOf d p) ct.yp := ct.ctx.hyp.of_mul_le_one ct.ctx.lam_le_one hR.sOf_pos.le
    have hymS : InCube (sOf d p) ct.ym := ct.ctx.hym.of_mul_le_one ct.ctx.lam_le_one hR.sOf_pos.le
    have c5p := SecA.sum_shift_sub_core_le ct.G (by norm_num : (1 : ℝ) ^ 2 = 1) hh hyp0 hv hP
    have c5m := SecA.sum_shift_sub_core_le ct.G (by norm_num : (-1 : ℝ) ^ 2 = 1) hh hym0 hv hM
    have hDp := SecA.diagD_le_two ct.G hR ct.ctx.deg hyS ct.S ct.v
    have hDm := SecA.diagD_le_two ct.G hR ct.ctx.deg hymS ct.S ct.v
    have hδp : 0 ≤ hN ct.G (aOf d p) 1 ct.yp σ ct.S ct.v -
        hzN ct.G (aOf d p) 1 h ct.yp σ ct.S ct.v :=
      sub_nonneg.2 (SecB.hzN_le_hN ct.G hP hh.le hyp0 ct.v)
    have hδm : 0 ≤ hN ct.G (aOf d p) (-1) ct.ym σ ct.S ct.v -
        hzN ct.G (aOf d p) (-1) h ct.ym σ ct.S ct.v :=
      sub_nonneg.2 (SecB.hzN_le_hN ct.G hM hh.le hym0 ct.v)
    set δp := hN ct.G (aOf d p) 1 ct.yp σ ct.S ct.v - hzN ct.G (aOf d p) 1 h ct.yp σ ct.S ct.v
    set δm := hN ct.G (aOf d p) (-1) ct.ym σ ct.S ct.v -
      hzN ct.G (aOf d p) (-1) h ct.ym σ ct.S ct.v
    have hTp : ∑ i ∈ ct.N, ωp i ^ 2 ≤ 2 * δp * h⁻¹ := by
      have e : ∑ i ∈ ct.N, ωp i ^ 2 = ∑ i ∈ ct.N, (ct.XP h σ i i - ct.YP h σ i i) :=
        Finset.sum_congr rfl fun i hi => by rw [hXYp i hi i hi]; ring
      rw [e]
      refine c5p.trans ?_
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hDp hδp) hinv0
    have hTm : ∑ i ∈ ct.N, ωm i ^ 2 ≤ 2 * δm * h⁻¹ := by
      have e : ∑ i ∈ ct.N, ωm i ^ 2 = ∑ i ∈ ct.N, (ct.XM h σ i i - ct.YM h σ i i) :=
        Finset.sum_congr rfl fun i hi => by rw [hXYm i hi i hi]; ring
      rw [e]
      refine c5m.trans ?_
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hDm hδm) hinv0
    -- identities `G² δ = (G - X) Z`
    have eGp : ct.gp σ ct.v ct.v = ct.yp ct.v * hN ct.G (aOf d p) 1 ct.yp σ ct.S ct.v :=
      SecB.greenP_diag ct.G σ ct.S (hyp0 ct.v)
    have eXp : ct.XP h σ ct.v ct.v = ct.yp ct.v * hzN ct.G (aOf d p) 1 h ct.yp σ ct.S ct.v :=
      SecB.shiftP_diag ct.G σ ct.S (hyp0 ct.v)
    have eGm : ct.gm σ ct.v ct.v = ct.ym ct.v * hN ct.G (aOf d p) (-1) ct.ym σ ct.S ct.v :=
      SecB.greenP_diag ct.G σ ct.S (hym0 ct.v)
    have eXm : ct.XM h σ ct.v ct.v = ct.ym ct.v * hzN ct.G (aOf d p) (-1) h ct.ym σ ct.S ct.v :=
      SecB.shiftP_diag ct.G σ ct.S (hym0 ct.v)
    have hZ1 : ct.gp σ ct.v ct.v ^ 2 * δp = (ct.gp σ ct.v ct.v - ct.XP h σ ct.v ct.v) * Z₁ σ := by
      simp only [hZ₁, δp]; rw [eXp, eGp]; ring
    have hZ2 : ct.gp σ ct.v ct.v * ct.gm σ ct.v ct.v * δp =
        (ct.gp σ ct.v ct.v - ct.XP h σ ct.v ct.v) * Z₂ σ := by
      simp only [hZ₂, δp]
      rw [abs_of_nonneg hGm0, abs_of_nonneg hp0', eXp, eGp]; ring
    have hZ3 : ct.gp σ ct.v ct.v * ct.gm σ ct.v ct.v * δm =
        (ct.gm σ ct.v ct.v - ct.XM h σ ct.v ct.v) * Z₃ σ := by
      simp only [hZ₃, δm]
      rw [abs_of_nonneg hG0, abs_of_nonneg hm0', eXm, eGm]; ring
    have eF : F₁ σ - F₂ σ = ((p : ℝ) - 1) * ct.gp σ ct.v ct.v ^ 2 *
        (∑ i ∈ ct.N, ∑ j ∈ ct.N, ct.XP h σ i j ^ 2 - ∑ i ∈ ct.N, ∑ j ∈ ct.N, ct.YP h σ i j ^ 2) +
        p * (ct.gp σ ct.v ct.v * ct.gm σ ct.v ct.v) *
          (∑ i ∈ ct.N, ∑ j ∈ ct.N, ct.XP h σ i j * ct.XM h σ i j -
            ∑ i ∈ ct.N, ∑ j ∈ ct.N, ct.YP h σ i j * ct.YM h σ i j) := by
      simp only [hF₁, hF₂]; ring
    have m1 : 0 ≤ ((p : ℝ) - 1) * ct.gp σ ct.v ct.v ^ 2 := mul_nonneg hp1' (sq_nonneg _)
    have m2 : 0 ≤ (p : ℝ) * (ct.gp σ ct.v ct.v * ct.gm σ ct.v ct.v) :=
      mul_nonneg hp0 (mul_nonneg hG0 hGm0)
    rw [eF]
    calc ((p : ℝ) - 1) * ct.gp σ ct.v ct.v ^ 2 *
          (∑ i ∈ ct.N, ∑ j ∈ ct.N, ct.XP h σ i j ^ 2 - ∑ i ∈ ct.N, ∑ j ∈ ct.N, ct.YP h σ i j ^ 2) +
        p * (ct.gp σ ct.v ct.v * ct.gm σ ct.v ct.v) *
          (∑ i ∈ ct.N, ∑ j ∈ ct.N, ct.XP h σ i j * ct.XM h σ i j -
            ∑ i ∈ ct.N, ∑ j ∈ ct.N, ct.YP h σ i j * ct.YM h σ i j)
        ≤ ((p : ℝ) - 1) * ct.gp σ ct.v ct.v ^ 2 * (2 * h⁻¹ * ∑ i ∈ ct.N, ωp i ^ 2) +
          p * (ct.gp σ ct.v ct.v * ct.gm σ ct.v ct.v) *
            (h⁻¹ * (∑ i ∈ ct.N, ωp i ^ 2 + ∑ i ∈ ct.N, ωm i ^ 2)) :=
          add_le_add (mul_le_mul_of_nonneg_left hA m1) (mul_le_mul_of_nonneg_left hB m2)
      _ ≤ ((p : ℝ) - 1) * ct.gp σ ct.v ct.v ^ 2 * (2 * h⁻¹ * (2 * δp * h⁻¹)) +
          p * (ct.gp σ ct.v ct.v * ct.gm σ ct.v ct.v) *
            (h⁻¹ * (2 * δp * h⁻¹ + 2 * δm * h⁻¹)) :=
          add_le_add
            (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hTp
              (mul_nonneg (by norm_num) hinv0)) m1)
            (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (add_le_add hTp hTm) hinv0) m2)
      _ = h⁻¹ ^ 2 * (4 * ((p : ℝ) - 1) * (ct.gp σ ct.v ct.v ^ 2 * δp) +
            2 * p * (ct.gp σ ct.v ct.v * ct.gm σ ct.v ct.v * δp) +
            2 * p * (ct.gp σ ct.v ct.v * ct.gm σ ct.v ct.v * δm)) := by ring
      _ = Bd σ := by rw [hZ1, hZ2, hZ3]
  -- moments of the weights
  have m1 : ct.E (fun σ => Z₁ σ ^ k) ≤ 128 ^ k := by
    refine lx_E_pow_le ct (fun σ => hN ct.G (aOf d p) 1 ct.yp σ ct.S ct.v)
      (fun σ => hN ct.G (aOf d p) 1 ct.yp σ ct.S ct.v) (fun _ => 1) ?_ h8.1 h8.1 h1E _ ?_
    · intro σ hσ
      obtain ⟨⟨a0, -⟩, -⟩ := lx_supp ct hR hh.le hσ ct.v
      exact ⟨a0, a0, zero_le_one⟩
    · intro σ hσ
      obtain ⟨⟨a0, -⟩, -⟩ := lx_supp ct hR hh.le hσ ct.v
      obtain ⟨⟨-, hyv⟩, -⟩ := lx_src ct hR ct.v
      refine ⟨mul_nonneg (hyp0 _) (sq_nonneg _), ?_⟩
      simp only [hZ₁]
      nlinarith [sq_nonneg (hN ct.G (aOf d p) 1 ct.yp σ ct.S ct.v)]
  have m2 : ct.E (fun σ => Z₂ σ ^ k) ≤ 128 ^ k := by
    refine lx_E_pow_le ct (fun σ => hN ct.G (aOf d p) 1 ct.yp σ ct.S ct.v)
      (fun σ => hN ct.G (aOf d p) (-1) ct.ym σ ct.S ct.v) (fun _ => 1) ?_ h8.1 h8.2 h1E _ ?_
    · intro σ hσ
      obtain ⟨⟨a0, -⟩, ⟨b0, -⟩⟩ := lx_supp ct hR hh.le hσ ct.v
      exact ⟨a0, b0, zero_le_one⟩
    · intro σ hσ
      obtain ⟨⟨a0, -⟩, ⟨b0, hYv0, hYGv, hm2⟩⟩ := lx_supp ct hR hh.le hσ ct.v
      refine ⟨by positivity, ?_⟩
      simp only [hZ₂]
      rw [abs_of_nonneg (hYv0.trans hYGv), abs_of_nonneg a0]
      nlinarith [mul_nonneg a0 b0]
  have m3 : ct.E (fun σ => Z₃ σ ^ k) ≤ 128 ^ k := by
    refine lx_E_pow_le ct (fun σ => hN ct.G (aOf d p) 1 ct.yp σ ct.S ct.v)
      (fun σ => hN ct.G (aOf d p) (-1) ct.ym σ ct.S ct.v) (fun _ => 1) ?_ h8.1 h8.2 h1E _ ?_
    · intro σ hσ
      obtain ⟨⟨a0, -⟩, ⟨b0, -⟩⟩ := lx_supp ct hR hh.le hσ ct.v
      exact ⟨a0, b0, zero_le_one⟩
    · intro σ hσ
      obtain ⟨⟨a0, hXv0, hXGv, hp2⟩, ⟨b0, -⟩⟩ := lx_supp ct hR hh.le hσ ct.v
      refine ⟨by positivity, ?_⟩
      simp only [hZ₃]
      rw [abs_of_nonneg (hXv0.trans hXGv), abs_of_nonneg b0]
      nlinarith [mul_nonneg a0 b0]
  have t1 := (hS1 Z₁ (fun σ => mul_nonneg (hyp0 _) (sq_nonneg _)) m1).1
  have t2 := (hS1 Z₂ (fun σ => by positivity) m2).1
  have t3 := (hS1 Z₃ (fun σ => by positivity) m3).2
  have hW0 : 0 ≤ 768 * (KS + 2) * Real.sqrt h := by
    have := mul_nonneg hKS2 (Real.sqrt_nonneg h); nlinarith
  have hE : ct.E F₁ - ct.E F₂ ≤ h⁻¹ ^ 2 * (768 * (KS + 2) * Real.sqrt h * (8 * p)) := by
    rw [← lx_E_sub]
    refine (lx_E_mono ct hpt).trans ?_
    have eB : ct.E Bd = h⁻¹ ^ 2 *
        (4 * ((p : ℝ) - 1) * ct.E (fun σ => (ct.gp σ ct.v ct.v - ct.XP h σ ct.v ct.v) * Z₁ σ) +
          2 * p * ct.E (fun σ => (ct.gp σ ct.v ct.v - ct.XP h σ ct.v ct.v) * Z₂ σ) +
          2 * p * ct.E (fun σ => (ct.gm σ ct.v ct.v - ct.XM h σ ct.v ct.v) * Z₃ σ)) := by
      simp only [hBd]
      rw [lx_E_const_mul, lx_E_add, lx_E_add, lx_E_const_mul, lx_E_const_mul, lx_E_const_mul]
    rw [eB]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    nlinarith [mul_le_mul_of_nonneg_left t1 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hp1'),
      mul_le_mul_of_nonneg_left t2 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hp0),
      mul_le_mul_of_nonneg_left t3 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hp0)]
  -- the two sides
  have eL : LdP d p * (((p : ℝ) - 1) * ct.qP h + p * ct.qM h) = aOf d p ^ 2 * ct.E F₁ := by
    have e1 : ct.qP h = 1 / (16 * d) * ct.E (fun σ => ct.gp σ ct.v ct.v ^ 2 *
        ∑ i ∈ ct.N, ∑ j ∈ ct.N, ct.XP h σ i j ^ 2) := by
      unfold Contact.qP
      rw [← lx_E_const_mul]
      exact lx_E_congr ct fun σ _ => lx_qP_integrand ct h σ
    have e2 : ct.qM h = 1 / (16 * d) * ct.E (fun σ => ct.gp σ ct.v ct.v * ct.gm σ ct.v ct.v *
        ∑ i ∈ ct.N, ∑ j ∈ ct.N, ct.XP h σ i j * ct.XM h σ i j) := by
      unfold Contact.qM
      rw [← lx_E_const_mul]
      exact lx_E_congr ct fun σ _ => lx_qM_integrand ct h σ
    have e3 : ct.E F₁ = ((p : ℝ) - 1) * ct.E (fun σ => ct.gp σ ct.v ct.v ^ 2 *
          ∑ i ∈ ct.N, ∑ j ∈ ct.N, ct.XP h σ i j ^ 2) +
        p * ct.E (fun σ => ct.gp σ ct.v ct.v * ct.gm σ ct.v ct.v *
          ∑ i ∈ ct.N, ∑ j ∈ ct.N, ct.XP h σ i j * ct.XM h σ i j) := by
      rw [← lx_E_const_mul, ← lx_E_const_mul, ← lx_E_add]
      exact lx_E_congr ct fun σ _ => by simp only [hF₁]; ring
    have hdne : (d : ℝ) ≠ 0 := hd0.ne'
    rw [e1, e2, e3, LdP]
    field_simp
  have eQ : ct.Qbl h = aOf d p ^ 2 * ct.E F₂ := rfl
  rw [eL, eQ]
  have ha2 := lx_a2_le hR
  have hsq : Real.sqrt h * Real.sqrt h = h := Real.mul_self_sqrt hh.le
  have hsq0 : 0 < Real.sqrt h := Real.sqrt_pos.2 hh
  have hX0 : 0 ≤ h⁻¹ ^ 2 * (768 * (KS + 2) * Real.sqrt h * (8 * p)) :=
    mul_nonneg (sq_nonneg _) (mul_nonneg hW0 (by positivity))
  have key : h⁻¹ ^ 2 * Real.sqrt h * (h * Real.sqrt h) = 1 := by
    have e : h⁻¹ ^ 2 * Real.sqrt h * (h * Real.sqrt h) =
        h⁻¹ ^ 2 * h * (Real.sqrt h * Real.sqrt h) := by ring
    rw [e, hsq]; field_simp
  have hfin : 1 / (d : ℝ) * (h⁻¹ ^ 2 * (768 * (KS + 2) * Real.sqrt h * (8 * p))) =
      6144 * (KS + 2) * p / (d * h * Real.sqrt h) := by
    rw [eq_div_iff (mul_pos (mul_pos hd0 hh) hsq0).ne']
    have hd' : 1 / (d : ℝ) * d = 1 := by field_simp
    calc 1 / (d : ℝ) * (h⁻¹ ^ 2 * (768 * (KS + 2) * Real.sqrt h * (8 * p))) *
          (d * h * Real.sqrt h)
        = (1 / (d : ℝ) * d) * (6144 * (KS + 2) * p) *
            (h⁻¹ ^ 2 * Real.sqrt h * (h * Real.sqrt h)) := by
          ring
      _ = 6144 * (KS + 2) * p := by rw [hd', key]; ring
  calc aOf d p ^ 2 * ct.E F₁ = aOf d p ^ 2 * ct.E F₂ + aOf d p ^ 2 * (ct.E F₁ - ct.E F₂) := by ring
    _ ≤ aOf d p ^ 2 * ct.E F₂ +
        1 / (d : ℝ) * (h⁻¹ ^ 2 * (768 * (KS + 2) * Real.sqrt h * (8 * p))) := by
        refine add_le_add le_rfl ?_
        exact (mul_le_mul_of_nonneg_left hE (sq_nonneg _)).trans
          (mul_le_mul_of_nonneg_right ha2 hX0)
    _ = aOf d p ^ 2 * ct.E F₂ + 6144 * (KS + 2) * p / (d * h * Real.sqrt h) := by rw [hfin]

/-- **L-RC1** (source (RC1), l.1819–1824; AUDIT-D §3.5 RC1: `(s/2)⁴ ≤ 1 + 4/q ≤ 1 + ε` and the
fourth-moment cap (F2)). `t₊ ≤ 1 + Cε`, `t₋ ≤ 1 + Cε`. -/
theorem rc1_tbounds : ∃ C : ℝ, 0 < C ∧ Eventually fun _c₀ _κ₀ d p h =>
    ∀ ct : Contact.{u} d p, ct.tP h ≤ 1 + C * epsP d p ∧ ct.tM h ≤ 1 + C * epsP d p := by
  refine ⟨5, by norm_num, (SecB.eventually_base 404).mono ?_⟩
  rintro c₀ κ₀ d p h ⟨hR, hp404, -, hhd, hk0, -⟩ ct
  have hh : 0 ≤ h := by rw [hhd]; positivity
  have hp : 404 ≤ p := by exact_mod_cast hp404
  obtain ⟨hc0, hc4⟩ := lx_c4 hR hp
  set c := ((p : ℝ) * rOf d p - 4) / ((p : ℝ) - 4) with hcdef
  have hd : (0 : ℝ) < d := by have := hR.ten_pow_six_le_d; linarith
  have hNd := lx_card_N ct
  have hp6 : 4 + 2 ≤ p := by omega
  have hF : ∀ i ∈ ct.S, ct.E (fun σ => hN ct.G (aOf d p) 1 ct.yp σ ct.S i ^ 4) ≤ c ^ 4 ∧
      ct.E (fun σ => hN ct.G (aOf d p) (-1) ct.ym σ ct.S i ^ 4) ≤ c ^ 4 := by
    intro i hi
    have := source_moments ct.G hR ct.ctx.toCapCtx ct.ctx.hyp ct.ctx.hym hi (k := 4)
      (by norm_num) hp6
    push_cast at this
    exact this
  have hv := ct.ctx.mem
  have hc4' : (0 : ℝ) ≤ c ^ 4 := by positivity
  have hfin : ∀ n : ℝ, 1 / (n * d) * (ct.N.card * (n * c ^ 4)) ≤ c ^ 4 →
      1 / (n * d) * (ct.N.card * (n * c ^ 4)) ≤ 1 + 5 * epsP d p := fun n hn => hn.trans hc4
  constructor
  · have hpt : ∀ σ, wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 →
        ct.OmP σ * (ct.uvec ⬝ᵥ (ct.MP h σ *ᵥ ct.uvec)) ≤
          1 / (2 * d) * ∑ i ∈ ct.N, (hN ct.G (aOf d p) 1 ct.yp σ ct.S ct.v ^ 4 +
            hN ct.G (aOf d p) 1 ct.yp σ ct.S i ^ 4) := by
      intro σ hσ
      rw [lx_tP_integrand]
      simp only [Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      obtain ⟨⟨hv0, hXv0, hXGv, hv2⟩, -⟩ := lx_supp ct hR hh hσ ct.v
      obtain ⟨⟨hi0, hX0, hXG, hi2⟩, -⟩ := lx_supp ct hR hh hσ i
      set a := hN ct.G (aOf d p) 1 ct.yp σ ct.S ct.v
      set b := hN ct.G (aOf d p) 1 ct.yp σ ct.S i
      have h1 : ct.gp σ ct.v ct.v ^ 2 ≤ 4 * a ^ 2 := by nlinarith
      have h2 : ct.XP h σ i i ^ 2 ≤ 4 * b ^ 2 := by nlinarith
      have h3 : ct.gp σ ct.v ct.v ^ 2 * ct.XP h σ i i ^ 2 ≤ 8 * (a ^ 4 + b ^ 4) := by
        calc _ ≤ (4 * a ^ 2) * (4 * b ^ 2) := mul_le_mul h1 h2 (sq_nonneg _) (by positivity)
          _ ≤ 8 * (a ^ 4 + b ^ 4) := by nlinarith [lx_amgm2 a b]
      have hd' : (0 : ℝ) ≤ 1 / (16 * d) := by positivity
      calc 1 / (16 * (d : ℝ)) * (ct.gp σ ct.v ct.v ^ 2 * ct.XP h σ i i ^ 2)
          ≤ 1 / (16 * d) * (8 * (a ^ 4 + b ^ 4)) := mul_le_mul_of_nonneg_left h3 hd'
        _ = 1 / (2 * d) * (a ^ 4 + b ^ 4) := by field_simp; ring
    calc ct.tP h ≤ ct.E (fun σ => 1 / (2 * d) * ∑ i ∈ ct.N,
          (hN ct.G (aOf d p) 1 ct.yp σ ct.S ct.v ^ 4 + hN ct.G (aOf d p) 1 ct.yp σ ct.S i ^ 4)) :=
          lx_E_mono ct hpt
      _ = 1 / (2 * d) * ∑ i ∈ ct.N,
          (ct.E (fun σ => hN ct.G (aOf d p) 1 ct.yp σ ct.S ct.v ^ 4) +
            ct.E (fun σ => hN ct.G (aOf d p) 1 ct.yp σ ct.S i ^ 4)) := by
          rw [lx_E_const_mul, lx_E_sum]
          congr 1
          exact Finset.sum_congr rfl fun i _ => lx_E_add ct _ _
      _ ≤ 1 / (2 * d) * ∑ _i ∈ ct.N, (c ^ 4 + c ^ 4) := by
          gcongr with i hi
          · exact (hF _ hv).1
          · exact (hF i (lx_N_sub ct hi)).1
      _ = 1 / (2 * d) * (ct.N.card * (2 * c ^ 4)) := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ 1 + 5 * epsP d p := by
          refine hfin 2 ?_
          rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
          nlinarith
  · have hpt : ∀ σ, wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 →
        ct.OmM σ * (ct.uvec ⬝ᵥ (ct.MM h σ *ᵥ ct.uvec)) ≤
          1 / (4 * d) * ∑ i ∈ ct.N, (hN ct.G (aOf d p) 1 ct.yp σ ct.S ct.v ^ 4 +
            hN ct.G (aOf d p) (-1) ct.ym σ ct.S ct.v ^ 4 +
            hN ct.G (aOf d p) 1 ct.yp σ ct.S i ^ 4 +
            hN ct.G (aOf d p) (-1) ct.ym σ ct.S i ^ 4) := by
      intro σ hσ
      rw [lx_tM_integrand]
      simp only [Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      obtain ⟨⟨hv0, hXv0, hXGv, hv2⟩, ⟨hw0, hYv0, hYGv, hw2⟩⟩ := lx_supp ct hR hh hσ ct.v
      obtain ⟨⟨hi0, hX0, hXG, hi2⟩, ⟨hj0, hY0, hYG, hj2⟩⟩ := lx_supp ct hR hh hσ i
      set a := hN ct.G (aOf d p) 1 ct.yp σ ct.S ct.v
      set b := hN ct.G (aOf d p) (-1) ct.ym σ ct.S ct.v
      set c1 := hN ct.G (aOf d p) 1 ct.yp σ ct.S i
      set e1 := hN ct.G (aOf d p) (-1) ct.ym σ ct.S i
      have h3 : ct.gp σ ct.v ct.v * ct.gm σ ct.v ct.v * (ct.XP h σ i i * ct.XM h σ i i) ≤
          4 * (a ^ 4 + b ^ 4 + c1 ^ 4 + e1 ^ 4) := by
        have hA : ct.gp σ ct.v ct.v * ct.gm σ ct.v ct.v ≤ (2 * a) * (2 * b) :=
          mul_le_mul hv2 hw2 (by linarith) (by linarith)
        have hB : ct.XP h σ i i * ct.XM h σ i i ≤ (2 * c1) * (2 * e1) :=
          mul_le_mul (hXG.trans hi2) (hYG.trans hj2) hY0 (by linarith)
        calc _ ≤ ((2 * a) * (2 * b)) * ((2 * c1) * (2 * e1)) :=
              mul_le_mul hA hB (mul_nonneg hX0 hY0) (by positivity)
          _ = 16 * (a * b * c1 * e1) := by ring
          _ ≤ 4 * (a ^ 4 + b ^ 4 + c1 ^ 4 + e1 ^ 4) := by nlinarith [lx_amgm4 a b c1 e1]
      have hd' : (0 : ℝ) ≤ 1 / (16 * d) := by positivity
      calc 1 / (16 * (d : ℝ)) * (ct.gp σ ct.v ct.v * ct.gm σ ct.v ct.v *
            (ct.XP h σ i i * ct.XM h σ i i))
          ≤ 1 / (16 * d) * (4 * (a ^ 4 + b ^ 4 + c1 ^ 4 + e1 ^ 4)) :=
            mul_le_mul_of_nonneg_left h3 hd'
        _ = 1 / (4 * d) * (a ^ 4 + b ^ 4 + c1 ^ 4 + e1 ^ 4) := by field_simp; ring
    calc ct.tM h ≤ ct.E (fun σ => 1 / (4 * d) * ∑ i ∈ ct.N,
          (hN ct.G (aOf d p) 1 ct.yp σ ct.S ct.v ^ 4 +
            hN ct.G (aOf d p) (-1) ct.ym σ ct.S ct.v ^ 4 +
            hN ct.G (aOf d p) 1 ct.yp σ ct.S i ^ 4 +
            hN ct.G (aOf d p) (-1) ct.ym σ ct.S i ^ 4)) := lx_E_mono ct hpt
      _ = 1 / (4 * d) * ∑ i ∈ ct.N,
          (ct.E (fun σ => hN ct.G (aOf d p) 1 ct.yp σ ct.S ct.v ^ 4) +
            ct.E (fun σ => hN ct.G (aOf d p) (-1) ct.ym σ ct.S ct.v ^ 4) +
            ct.E (fun σ => hN ct.G (aOf d p) 1 ct.yp σ ct.S i ^ 4) +
            ct.E (fun σ => hN ct.G (aOf d p) (-1) ct.ym σ ct.S i ^ 4)) := by
          rw [lx_E_const_mul, lx_E_sum]
          congr 1
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [lx_E_add, lx_E_add, lx_E_add]
      _ ≤ 1 / (4 * d) * ∑ _i ∈ ct.N, (c ^ 4 + c ^ 4 + c ^ 4 + c ^ 4) := by
          gcongr with i hi
          · exact (hF _ hv).1
          · exact (hF _ hv).2
          · exact (hF i (lx_N_sub ct hi)).1
          · exact (hF i (lx_N_sub ct hi)).2
      _ = 1 / (4 * d) * (ct.N.card * (4 * c ^ 4)) := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ 1 + 5 * epsP d p := by
          refine hfin 4 ?_
          rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
          nlinarith

/-- **L-RC4** (source (RC4), l.1927–1932; AUDIT-D §3.7). The mean shift (S1) with fixed-degree
physical diagonal weights and interpolation: `0 ≤ t_{±,0} - t_± ≤ C √h`. -/
theorem rc4_centres : ∃ C : ℝ, 0 < C ∧ Eventually fun _c₀ _κ₀ d p h =>
    ∀ ct : Contact.{u} d p,
      (0 ≤ ct.tP0 - ct.tP h ∧ ct.tP0 - ct.tP h ≤ C * Real.sqrt h) ∧
        (0 ≤ ct.tM0 - ct.tM h ∧ ct.tM0 - ct.tM h ≤ C * Real.sqrt h) := by
  obtain ⟨K, hK, hCL⟩ := SecB.cl1_bridge.{u}
  have hKS := SecB.one_le_s1K hK
  refine ⟨96 * (SecB.s1K K + 2), by linarith, ?_⟩
  refine (((SecB.mean_shift_weighted_of_cl1 hK zero_le_one one_pos hCL).and
    (SecB.eventually_log_le_p 6)).and SecB.eventually_h_facts).mono ?_
  rintro c₀ κ₀ d p h ⟨⟨hW, hlp⟩, hR, h0, -, -, -⟩ ct
  obtain ⟨k, hk1, hk6⟩ := lx_choose_k hR (by norm_num : (0 : ℝ) ≤ 6) hlp
  have hk6' : 6 * k ≤ p := by exact_mod_cast hk6
  have hk2 : 2 * k ≤ p := by omega
  have hk3 : 2 * (3 * k) ≤ p := by omega
  have hkpos : 1 ≤ 3 * k := by
    have : (1 : ℝ) ≤ k := by have := Real.log_nonneg (show (1 : ℝ) ≤ d by
      have := hR.ten_pow_six_le_d; linarith); linarith
    have : 1 ≤ k := by exact_mod_cast this
    omega
  have hh : 0 ≤ h := h0.le
  have hd : (0 : ℝ) < d := by have := hR.ten_pow_six_le_d; linarith
  have hNd := lx_card_N ct
  have hv := ct.ctx.mem
  have hsq := Real.sqrt_nonneg h
  set KS := SecB.s1K K
  have h8 : ∀ w ∈ ct.S,
      ct.E (fun σ => hN ct.G (aOf d p) 1 ct.yp σ ct.S w ^ (3 * k)) ≤ 8 ^ k ∧
        ct.E (fun σ => hN ct.G (aOf d p) (-1) ct.ym σ ct.S w ^ (3 * k)) ≤ 8 ^ k := by
    intro w hw
    have e : (2 : ℝ) ^ (3 * k) = 8 ^ k := by rw [pow_mul]; norm_num
    rw [← e]
    exact lx_F2 ct hR hw hkpos hk3
  -- the weighted mean shift at `i ∈ N`, both branches
  have hS1 : ∀ i ∈ ct.N, ∀ Z : Config ct.V → ℝ, (∀ σ, 0 ≤ Z σ) →
      ct.E (fun σ => Z σ ^ k) ≤ 128 ^ k →
      ct.E (fun σ => (ct.gp σ i i - ct.XP h σ i i) * Z σ) ≤ 768 * (KS + 2) * Real.sqrt h ∧
        ct.E (fun σ => (ct.gm σ i i - ct.XM h σ i i) * Z σ) ≤ 768 * (KS + 2) * Real.sqrt h := by
    intro i hi Z hZ0 hZk
    have hiS := lx_N_sub ct hi
    obtain ⟨h1, h2⟩ := hW ct.toCapPoint i hiS k hk1 hk2 Z hZ0 128 (by norm_num) hZk
    obtain ⟨⟨-, hyi⟩, ⟨-, hymi⟩⟩ := lx_src ct hR i
    have hc : 0 ≤ 3 * (KS + 2) * 128 * Real.sqrt h := by
      have : 0 ≤ KS + 2 := by linarith
      have := mul_nonneg this hsq
      nlinarith
    constructor
    · refine le_trans (show ct.E (fun σ => (ct.gp σ i i - ct.XP h σ i i) * Z σ) ≤
        3 * (KS + 2) * 128 * Real.sqrt h * ct.yp i from h1) ?_
      nlinarith [mul_nonneg hc (sub_nonneg.2 hyi)]
    · refine le_trans (show ct.E (fun σ => (ct.gm σ i i - ct.XM h σ i i) * Z σ) ≤
        3 * (KS + 2) * 128 * Real.sqrt h * ct.ym i from h2) ?_
      nlinarith [mul_nonneg hc (sub_nonneg.2 hymi)]
  have hfin : ∀ (n T : ℝ), 0 ≤ T → T ≤ ct.N.card * (n * (768 * (KS + 2) * Real.sqrt h)) →
      0 ≤ n → n ≤ 2 → 1 / (16 * d) * T ≤ 96 * (KS + 2) * Real.sqrt h := by
    intro n T hT hTb hn0 hn
    have hKS2 : 0 ≤ KS + 2 := by linarith
    have hA : 0 ≤ 768 * (KS + 2) * Real.sqrt h := by
      have := mul_nonneg hKS2 hsq
      nlinarith
    have : T ≤ d * (2 * (768 * (KS + 2) * Real.sqrt h)) := by
      refine hTb.trans ?_
      exact mul_le_mul hNd (mul_le_mul_of_nonneg_right hn hA) (mul_nonneg hn0 hA) hd.le
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
    nlinarith
  constructor
  · -- plus branch
    set F : Config ct.V → ℝ := fun σ =>
      ct.gp σ ct.v ct.v ^ 2 * ∑ i ∈ ct.N, (ct.gp σ i i ^ 2 - ct.XP h σ i i ^ 2) with hF
    have eP : ct.tP0 - ct.tP h = 1 / (16 * d) * ct.E F := by
      have e1 : ct.tP h = 1 / (16 * d) *
          ct.E (fun σ => ct.gp σ ct.v ct.v ^ 2 * ∑ i ∈ ct.N, ct.XP h σ i i ^ 2) := by
        unfold Contact.tP
        rw [← lx_E_const_mul]
        exact lx_E_congr ct fun σ _ => lx_tP_integrand ct h σ
      rw [e1]
      unfold Contact.tP0
      rw [← mul_sub, ← lx_E_sub]
      congr 2
      funext σ
      simp only [hF, Finset.sum_sub_distrib]
      ring
    have hF0 : 0 ≤ ct.E F := lx_E_nonneg ct fun σ hσ => by
      refine mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ => ?_)
      obtain ⟨⟨-, hX0, hXG, -⟩, -⟩ := lx_supp ct hR hh hσ i
      nlinarith
    have hFle : ct.E F ≤ ∑ i ∈ ct.N,
        ct.E (fun σ => (ct.gp σ i i - ct.XP h σ i i) *
          (2 * ct.gp σ ct.v ct.v ^ 2 * |ct.gp σ i i|)) := by
      rw [← lx_E_sum]
      refine lx_E_mono ct fun σ hσ => ?_
      simp only [hF, Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      obtain ⟨⟨-, hX0, hXG, -⟩, -⟩ := lx_supp ct hR hh hσ i
      have hG0 : 0 ≤ ct.gp σ i i := hX0.trans hXG
      rw [abs_of_nonneg hG0]
      have : ct.gp σ i i ^ 2 - ct.XP h σ i i ^ 2 ≤ (ct.gp σ i i - ct.XP h σ i i) *
          (2 * ct.gp σ i i) := by nlinarith
      calc ct.gp σ ct.v ct.v ^ 2 * (ct.gp σ i i ^ 2 - ct.XP h σ i i ^ 2)
          ≤ ct.gp σ ct.v ct.v ^ 2 * ((ct.gp σ i i - ct.XP h σ i i) * (2 * ct.gp σ i i)) :=
            mul_le_mul_of_nonneg_left this (sq_nonneg _)
        _ = _ := by ring
    have hterm : ∀ i ∈ ct.N, ct.E (fun σ => (ct.gp σ i i - ct.XP h σ i i) *
        (2 * ct.gp σ ct.v ct.v ^ 2 * |ct.gp σ i i|)) ≤ 1 * (768 * (KS + 2) * Real.sqrt h) := by
      intro i hi
      rw [one_mul]
      refine (hS1 i hi _ (fun σ => by positivity) ?_).1
      refine lx_E_pow_le ct (fun σ => hN ct.G (aOf d p) 1 ct.yp σ ct.S ct.v)
        (fun σ => hN ct.G (aOf d p) 1 ct.yp σ ct.S ct.v)
        (fun σ => hN ct.G (aOf d p) 1 ct.yp σ ct.S i) ?_ (h8 _ hv).1 (h8 _ hv).1
        (h8 _ (lx_N_sub ct hi)).1 _ ?_
      · intro σ hσ
        obtain ⟨⟨a0, -⟩, -⟩ := lx_supp ct hR hh hσ ct.v
        obtain ⟨⟨b0, -⟩, -⟩ := lx_supp ct hR hh hσ i
        exact ⟨a0, a0, b0⟩
      · intro σ hσ
        obtain ⟨⟨a0, hXv0, hXGv, hv2⟩, -⟩ := lx_supp ct hR hh hσ ct.v
        obtain ⟨⟨b0, hX0, hXG, hi2⟩, -⟩ := lx_supp ct hR hh hσ i
        have hG0 : 0 ≤ ct.gp σ i i := hX0.trans hXG
        have hGv0 : 0 ≤ ct.gp σ ct.v ct.v := hXv0.trans hXGv
        refine ⟨by positivity, ?_⟩
        rw [abs_of_nonneg hG0]
        have h1 : ct.gp σ ct.v ct.v ^ 2 ≤ (2 * hN ct.G (aOf d p) 1 ct.yp σ ct.S ct.v) ^ 2 :=
          pow_le_pow_left₀ hGv0 hv2 2
        calc 2 * ct.gp σ ct.v ct.v ^ 2 * ct.gp σ i i
            ≤ 2 * (2 * hN ct.G (aOf d p) 1 ct.yp σ ct.S ct.v) ^ 2 *
                (2 * hN ct.G (aOf d p) 1 ct.yp σ ct.S i) := by gcongr
          _ = _ := by ring
    have hsum := Finset.sum_le_sum hterm
    rw [Finset.sum_const, nsmul_eq_mul] at hsum
    rw [eP]
    exact ⟨mul_nonneg (by positivity) hF0, hfin 1 _ hF0 (hFle.trans hsum) zero_le_one
      (by norm_num)⟩
  · -- minus branch
    set F : Config ct.V → ℝ := fun σ =>
      ct.gp σ ct.v ct.v * ct.gm σ ct.v ct.v *
        ∑ i ∈ ct.N, (ct.gp σ i i * ct.gm σ i i - ct.XP h σ i i * ct.XM h σ i i) with hF
    have eM : ct.tM0 - ct.tM h = 1 / (16 * d) * ct.E F := by
      have e1 : ct.tM h = 1 / (16 * d) * ct.E (fun σ => ct.gp σ ct.v ct.v * ct.gm σ ct.v ct.v *
          ∑ i ∈ ct.N, ct.XP h σ i i * ct.XM h σ i i) := by
        unfold Contact.tM
        rw [← lx_E_const_mul]
        exact lx_E_congr ct fun σ _ => lx_tM_integrand ct h σ
      rw [e1]
      unfold Contact.tM0
      rw [← mul_sub, ← lx_E_sub]
      congr 2
      funext σ
      simp only [hF, Finset.sum_sub_distrib]
      ring
    have hF0 : 0 ≤ ct.E F := lx_E_nonneg ct fun σ hσ => by
      obtain ⟨⟨-, hXv0, hXGv, -⟩, ⟨-, hYv0, hYGv, -⟩⟩ := lx_supp ct hR hh hσ ct.v
      refine mul_nonneg (mul_nonneg (hXv0.trans hXGv) (hYv0.trans hYGv))
        (Finset.sum_nonneg fun i _ => ?_)
      obtain ⟨⟨-, hX0, hXG, -⟩, ⟨-, hY0, hYG, -⟩⟩ := lx_supp ct hR hh hσ i
      have := mul_le_mul hXG hYG hY0 (hX0.trans hXG)
      linarith
    have hFle : ct.E F ≤ ∑ i ∈ ct.N,
        (ct.E (fun σ => (ct.gp σ i i - ct.XP h σ i i) *
            (|ct.gp σ ct.v ct.v| * |ct.gm σ ct.v ct.v| * |ct.gm σ i i|)) +
          ct.E (fun σ => (ct.gm σ i i - ct.XM h σ i i) *
            (|ct.gp σ ct.v ct.v| * |ct.gm σ ct.v ct.v| * |ct.gp σ i i|))) := by
      simp only [← lx_E_add]
      rw [← lx_E_sum]
      refine lx_E_mono ct fun σ hσ => ?_
      simp only [hF, Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      obtain ⟨⟨-, hXv0, hXGv, -⟩, ⟨-, hYv0, hYGv, -⟩⟩ := lx_supp ct hR hh hσ ct.v
      obtain ⟨⟨-, hX0, hXG, -⟩, ⟨-, hY0, hYG, -⟩⟩ := lx_supp ct hR hh hσ i
      have hG0 : 0 ≤ ct.gp σ i i := hX0.trans hXG
      have hM0 : 0 ≤ ct.gm σ i i := hY0.trans hYG
      have hGv0 : 0 ≤ ct.gp σ ct.v ct.v := hXv0.trans hXGv
      have hMv0 : 0 ≤ ct.gm σ ct.v ct.v := hYv0.trans hYGv
      rw [abs_of_nonneg hG0, abs_of_nonneg hM0, abs_of_nonneg hGv0, abs_of_nonneg hMv0]
      have key : ct.gp σ i i * ct.gm σ i i - ct.XP h σ i i * ct.XM h σ i i ≤
          (ct.gp σ i i - ct.XP h σ i i) * ct.gm σ i i +
            (ct.gm σ i i - ct.XM h σ i i) * ct.gp σ i i := by
        nlinarith [mul_le_mul_of_nonneg_left hXG (sub_nonneg.2 hYG)]
      have hvv : 0 ≤ ct.gp σ ct.v ct.v * ct.gm σ ct.v ct.v := mul_nonneg hGv0 hMv0
      calc ct.gp σ ct.v ct.v * ct.gm σ ct.v ct.v *
            (ct.gp σ i i * ct.gm σ i i - ct.XP h σ i i * ct.XM h σ i i)
          ≤ ct.gp σ ct.v ct.v * ct.gm σ ct.v ct.v * ((ct.gp σ i i - ct.XP h σ i i) * ct.gm σ i i +
            (ct.gm σ i i - ct.XM h σ i i) * ct.gp σ i i) := mul_le_mul_of_nonneg_left key hvv
        _ = _ := by ring
    have hmom : ∀ i ∈ ct.N, ∀ (f₃ : Config ct.V → ℝ) (g : Config ct.V → ℝ),
        (∀ σ, wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 → 0 ≤ f₃ σ ∧ g σ ≤ 2 * f₃ σ ∧
          0 ≤ g σ) →
        ct.E (fun σ => f₃ σ ^ (3 * k)) ≤ 8 ^ k →
        ct.E (fun σ => (|ct.gp σ ct.v ct.v| * |ct.gm σ ct.v ct.v| * |g σ|) ^ k) ≤ 128 ^ k := by
      intro i hi f₃ g hg h3
      refine lx_E_pow_le ct (fun σ => hN ct.G (aOf d p) 1 ct.yp σ ct.S ct.v)
        (fun σ => hN ct.G (aOf d p) (-1) ct.ym σ ct.S ct.v) f₃ ?_ (h8 _ hv).1 (h8 _ hv).2 h3 _ ?_
      · intro σ hσ
        obtain ⟨⟨a0, -⟩, ⟨b0, -⟩⟩ := lx_supp ct hR hh hσ ct.v
        exact ⟨a0, b0, (hg σ hσ).1⟩
      · intro σ hσ
        obtain ⟨⟨a0, hXv0, hXGv, hv2⟩, ⟨b0, hYv0, hYGv, hw2⟩⟩ := lx_supp ct hR hh hσ ct.v
        obtain ⟨f0, gle, g0⟩ := hg σ hσ
        have hGv0 : 0 ≤ ct.gp σ ct.v ct.v := hXv0.trans hXGv
        have hMv0 : 0 ≤ ct.gm σ ct.v ct.v := hYv0.trans hYGv
        refine ⟨by positivity, ?_⟩
        rw [abs_of_nonneg hGv0, abs_of_nonneg hMv0, abs_of_nonneg g0]
        calc ct.gp σ ct.v ct.v * ct.gm σ ct.v ct.v * g σ
            ≤ (2 * hN ct.G (aOf d p) 1 ct.yp σ ct.S ct.v) *
                (2 * hN ct.G (aOf d p) (-1) ct.ym σ ct.S ct.v) * (2 * f₃ σ) := by gcongr
          _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg a0 b0) f0]
    have hterm : ∀ i ∈ ct.N,
        ct.E (fun σ => (ct.gp σ i i - ct.XP h σ i i) *
            (|ct.gp σ ct.v ct.v| * |ct.gm σ ct.v ct.v| * |ct.gm σ i i|)) +
          ct.E (fun σ => (ct.gm σ i i - ct.XM h σ i i) *
            (|ct.gp σ ct.v ct.v| * |ct.gm σ ct.v ct.v| * |ct.gp σ i i|)) ≤
          2 * (768 * (KS + 2) * Real.sqrt h) := by
      intro i hi
      have hiS := lx_N_sub ct hi
      have m1 := hmom i hi (fun σ => hN ct.G (aOf d p) (-1) ct.ym σ ct.S i)
        (fun σ => ct.gm σ i i) (fun σ hσ => by
          obtain ⟨-, ⟨b0, hY0, hYG, hj2⟩⟩ := lx_supp ct hR hh hσ i
          exact ⟨b0, hj2, hY0.trans hYG⟩) (h8 i hiS).2
      have m2 := hmom i hi (fun σ => hN ct.G (aOf d p) 1 ct.yp σ ct.S i)
        (fun σ => ct.gp σ i i) (fun σ hσ => by
          obtain ⟨⟨b0, hX0, hXG, hi2⟩, -⟩ := lx_supp ct hR hh hσ i
          exact ⟨b0, hi2, hX0.trans hXG⟩) (h8 i hiS).1
      have t1 := (hS1 i hi _ (fun σ => by positivity) m1).1
      have t2 := (hS1 i hi _ (fun σ => by positivity) m2).2
      linarith
    have hsum := Finset.sum_le_sum hterm
    rw [Finset.sum_const, nsmul_eq_mul] at hsum
    rw [eM]
    exact ⟨mul_nonneg (by positivity) hF0, hfin 2 _ hF0 (hFle.trans hsum) zero_le_two
      le_rfl⟩

/-- BM1 with the weight `D^m Ω`, summed over any column set `J`. -/
theorem lx_bm1_pt {ι : Type*} [Fintype ι] [DecidableEq ι] (X Y : Matrix ι ι ℝ) (b : ι → ℝ)
    (I J : Finset ι) {h D Ω : ℝ} (m : ℕ) (hh : 0 < h) (hX : X.PosSemidef) (hY : Y.PosSemidef)
    (hXn : ∀ w, w ⬝ᵥ (X *ᵥ w) ≤ h⁻¹ * (w ⬝ᵥ w)) (hYn : ∀ w, w ⬝ᵥ (Y *ᵥ w) ≤ h⁻¹ * (w ⬝ᵥ w))
    (hb : ∀ i, 0 ≤ b i) (hD : ∀ i ∈ I, X i i ≤ D) (hD0 : 0 ≤ D) (hΩ : 0 ≤ Ω) :
    ∑ i ∈ I, ∑ j ∈ J, D ^ m * Ω * maskF X Y b j i ^ 2 ≤
      16 * h⁻¹ ^ 2 * (D ^ (m + 2) *
        (Ω * (b ⬝ᵥ (Matrix.of (fun i k => X i k * Y i k / 4) *ᵥ b)))) := by
  have hF := bm1_det X Y b I hh hX hY hXn hYn hb hD
  have hS : ∑ i ∈ I, ∑ j ∈ J, maskF X Y b j i ^ 2 ≤ ∑ i ∈ I, ∑ j, maskF X Y b j i ^ 2 :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_univ_sum_of_nonneg fun j => sq_nonneg _
  calc ∑ i ∈ I, ∑ j ∈ J, D ^ m * Ω * maskF X Y b j i ^ 2
      = D ^ m * Ω * ∑ i ∈ I, ∑ j ∈ J, maskF X Y b j i ^ 2 := by simp only [Finset.mul_sum]
    _ ≤ D ^ m * Ω * (16 * D ^ 2 * h⁻¹ ^ 2 *
          (b ⬝ᵥ (Matrix.of (fun i k => X i k * Y i k / 4) *ᵥ b))) :=
        mul_le_mul_of_nonneg_left (hS.trans hF) (by positivity)
    _ = _ := by ring

/-- **L-BM4** (source (BM4), l.1643–1654; AUDIT-D §3.3 BM4). BM1 pointwise with `D = D_*`, then
interpolation with floor `θ = d⁻²`: `Σ_{i∈N, j∈S} E[D_*^m Ω_± F_ji(b_±)²] ≤ C(m) h⁻² (z_± + θ)`. -/
theorem bm4_mask (m : ℕ) : ∃ C : ℝ, 0 < C ∧ Eventually fun _c₀ _κ₀ d p h =>
    ∀ ct : Contact.{u} d p,
      ∑ i ∈ ct.N, ∑ j ∈ ct.S, ct.E (fun σ => ct.Dstar σ ^ m * ct.OmP σ *
          maskF (ct.XP h σ) (ct.XP h σ) (ct.bP h σ) j i ^ 2) ≤
        C * h⁻¹ ^ 2 * (ct.zP h + thP d) ∧
      ∑ i ∈ ct.N, ∑ j ∈ ct.S,         ct.E (fun σ => ct.Dstar σ ^ m * ct.OmM σ *
          maskF (ct.XM h σ) (ct.XP h σ) (ct.bM h σ) j i ^ 2) ≤
        C * h⁻¹ ^ 2 * (ct.zM h + thP d) := by
  obtain ⟨KU, hKU0, hKU⟩ : ∃ KU : ℝ, 0 < KU ∧
      KU = 27 * 12 ^ (m + 2) * (27 * 12 ^ 2 * Real.exp (((10 : ℕ) : ℝ) + ((2 : ℕ) : ℝ))) :=
    ⟨_, by positivity, rfl⟩
  refine ⟨16 * KU, by linarith, ?_⟩
  refine ((SecB.dstar_moment.and (SecB.eventually_log_le_p (2 * ((m : ℝ) + 2)))).and
    lx_ev_h).mono ?_
  rintro c₀ κ₀ d p h ⟨⟨hDs, hlp⟩, hR, hh, hh2, hhd⟩ ct
  obtain ⟨k, hk1, hkp⟩ := lx_choose_k hR (by positivity) hlp
  have hkp' : 2 * ((m + 2) * k) ≤ p := by
    have : ((2 * ((m + 2) * k) : ℕ) : ℝ) ≤ p := by push_cast; linarith
    exact_mod_cast this
  have hk2 : 2 * (2 * k) ≤ p :=
    le_trans (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right k (by omega))) hkp'
  have hd1 : (1 : ℝ) ≤ d := by have := hR.ten_pow_six_le_d; linarith
  have hd0 : (0 : ℝ) < d := by linarith
  have hinv0 : 0 ≤ h⁻¹ := inv_nonneg.2 hh.le
  have hyq : ∀ k, (0 ≤ ct.yp k ∧ ct.yp k ≤ h⁻¹) ∧ (0 ≤ ct.ym k ∧ ct.ym k ≤ h⁻¹) := fun k => by
    obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ := lx_src ct hR k
    have : (2 : ℝ) ≤ h⁻¹ := by rw [le_inv_comm₀ (by norm_num) hh]; linarith
    exact ⟨⟨a1, by linarith⟩, ⟨b1, by linarith⟩⟩
  have h6 : h⁻¹ ^ 6 ≤ (d : ℝ) ^ 6 := pow_le_pow_left₀ hinv0 hhd 6
  have hc4 : 0 ≤ h⁻¹ ^ 2 / 4 := by positivity
  -- the generic interpolation step
  have hgen : ∀ (F : Config ct.V → ct.V → ct.V → ℝ) (Yf : Config ct.V → ℝ),
      (∀ σ, wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 →
        ∑ i ∈ ct.N, ∑ j ∈ ct.S, F σ j i ≤ 16 * h⁻¹ ^ 2 * (ct.Dstar σ ^ (m + 2) * Yf σ)) →
      (∀ σ, wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 →
        0 ≤ Yf σ ∧ Yf σ ≤ (d : ℝ) ^ 10 * ct.Dstar σ ^ 2) →
      ∑ i ∈ ct.N, ∑ j ∈ ct.S, ct.E (fun σ => F σ j i) ≤
        16 * KU * h⁻¹ ^ 2 * (ct.E Yf + thP d) := by
    intro F Yf hpt hY
    have hU := lx_umi ct hR (hDs ct) hk1 (a := 10) (b := 2) (c := m + 2) (e := 2) (by norm_num)
      (by omega) hk2 hkp' Yf hY
    rw [← hKU] at hU
    calc ∑ i ∈ ct.N, ∑ j ∈ ct.S, ct.E (fun σ => F σ j i)
        = ct.E (fun σ => ∑ i ∈ ct.N, ∑ j ∈ ct.S, F σ j i) := by
          rw [lx_E_sum]; exact Finset.sum_congr rfl fun i _ => (lx_E_sum ct _ _).symm
      _ ≤ ct.E (fun σ => 16 * h⁻¹ ^ 2 * (ct.Dstar σ ^ (m + 2) * Yf σ)) := lx_E_mono ct hpt
      _ = 16 * h⁻¹ ^ 2 * ct.E (fun σ => ct.Dstar σ ^ (m + 2) * Yf σ) := lx_E_const_mul ct _ _
      _ ≤ 16 * h⁻¹ ^ 2 * (KU * (ct.E Yf + 1 / (d : ℝ) ^ 2)) := by gcongr
      _ = 16 * KU * h⁻¹ ^ 2 * (ct.E Yf + thP d) := by unfold thP; ring
  -- support facts for both branches
  have hsupp : ∀ σ, wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 →
      (ct.XP h σ).PosSemidef ∧ (∀ w, w ⬝ᵥ (ct.XP h σ *ᵥ w) ≤ h⁻¹ * (w ⬝ᵥ w)) ∧
      (ct.XM h σ).PosSemidef ∧ (∀ w, w ⬝ᵥ (ct.XM h σ *ᵥ w) ≤ h⁻¹ * (w ⬝ᵥ w)) := by
    intro σ hσ
    obtain ⟨hP, hM⟩ := SecB.posDef_of_wt_ne_zero ct.G hσ
    exact ⟨lx_shift_psd ct.G (fun k => (hyq k).1.1) hh.le hP,
      lx_shift_quad ct.G (fun k => (hyq k).1) hh hP,
      lx_shift_psd ct.G (fun k => (hyq k).2.1) hh.le hM,
      lx_shift_quad ct.G (fun k => (hyq k).2) hh hM⟩
  have hDN : ∀ σ, wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 →
      0 ≤ ct.Dstar σ ∧ (∀ i ∈ ct.N, ct.XP h σ i i ≤ ct.Dstar σ ∧ ct.XM h σ i i ≤ ct.Dstar σ) ∧
      0 ≤ ct.gp σ ct.v ct.v ∧ ct.gp σ ct.v ct.v ≤ ct.Dstar σ ∧
      0 ≤ ct.gm σ ct.v ct.v ∧ ct.gm σ ct.v ct.v ≤ ct.Dstar σ := by
    intro σ hσ
    obtain ⟨⟨-, hXv0, hXGv, -⟩, ⟨-, hYv0, hYGv, -⟩⟩ := lx_supp ct hR hh.le hσ ct.v
    obtain ⟨dA, dC⟩ := lx_dstar_ge ct σ (lx_mem_ball_v ct)
    refine ⟨by linarith, fun i hi => ?_, hXv0.trans hXGv, by linarith, hYv0.trans hYGv,
      by linarith⟩
    obtain ⟨⟨-, -, hXG, -⟩, ⟨-, -, hYG, -⟩⟩ := lx_supp ct hR hh.le hσ i
    obtain ⟨dB, dD⟩ := lx_dstar_ge ct σ (lx_mem_ball_N ct hi)
    exact ⟨by linarith, by linarith⟩
  constructor
  · refine hgen (fun σ j i => ct.Dstar σ ^ m * ct.OmP σ *
      maskF (ct.XP h σ) (ct.XP h σ) (ct.bP h σ) j i ^ 2)
      (fun σ => ct.OmP σ * (ct.bP h σ ⬝ᵥ (ct.KP h σ *ᵥ ct.bP h σ))) ?_ ?_
    · intro σ hσ
      obtain ⟨hX, hXn, -, -⟩ := hsupp σ hσ
      obtain ⟨hD0, hD, -⟩ := hDN σ hσ
      have hXd : ∀ i, ct.XP h σ i i ≤ h⁻¹ := lx_diag_le_of_quad hXn
      have hb := (lx_bKb ct hR hc4 (fun l => (ct.XP h σ l l / 2) ^ 2) (fun l => sq_nonneg _)
        (fun l => by
          have h0 : 0 ≤ ct.XP h σ l l := hX.diag_nonneg
          have := pow_le_pow_left₀ h0 (hXd l) 2
          nlinarith) (ct.KP h σ) (fun i k => by
          have := lx_entry_le hX hXd i k
          simp only [Contact.KP, Matrix.of_apply]
          rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
          have h0 := abs_nonneg (ct.XP h σ i k)
          have := mul_le_mul this this h0 hinv0
          nlinarith)).1
      have hΩ : 0 ≤ ct.OmP σ := by unfold Contact.OmP; positivity
      exact lx_bm1_pt (ct.XP h σ) (ct.XP h σ) (ct.bP h σ) ct.N ct.S m hh hX hX hXn hXn hb
        (fun i hi => (hD i hi).1) hD0 hΩ
    · intro σ hσ
      obtain ⟨hX, hXn, -, -⟩ := hsupp σ hσ
      obtain ⟨hD0, -, hG0, hGD, -⟩ := hDN σ hσ
      have hXd : ∀ i, ct.XP h σ i i ≤ h⁻¹ := lx_diag_le_of_quad hXn
      have hbb := lx_bKb ct hR hc4 (fun l => (ct.XP h σ l l / 2) ^ 2) (fun l => sq_nonneg _)
        (fun l => by
          have h0 : 0 ≤ ct.XP h σ l l := hX.diag_nonneg
          have := pow_le_pow_left₀ h0 (hXd l) 2
          nlinarith) (ct.KP h σ) (fun i k => by
          have := lx_entry_le hX hXd i k
          simp only [Contact.KP, Matrix.of_apply]
          rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
          have h0 := abs_nonneg (ct.XP h σ i k)
          have := mul_le_mul this this h0 hinv0
          nlinarith)
      have hb0 : ∀ i, 0 ≤ ct.bP h σ i := hbb.1
      have hbK : ct.bP h σ ⬝ᵥ (ct.KP h σ *ᵥ ct.bP h σ) ≤ 16 * (d : ℝ) ^ 4 * (h⁻¹ ^ 2 / 4) ^ 3 :=
        hbb.2
      have hbK0 : 0 ≤ ct.bP h σ ⬝ᵥ (ct.KP h σ *ᵥ ct.bP h σ) := by
        simp only [dotProduct, mulVec]
        refine Finset.sum_nonneg fun i _ => mul_nonneg (hb0 i)
          (Finset.sum_nonneg fun k _ => mul_nonneg ?_ (hb0 k))
        simp only [Contact.KP, Matrix.of_apply]
        nlinarith [mul_self_nonneg (ct.XP h σ i k)]
      have hΩ : 0 ≤ ct.OmP σ := by unfold Contact.OmP; positivity
      have hΩD : ct.OmP σ ≤ ct.Dstar σ ^ 2 := by
        unfold Contact.OmP
        have := pow_le_pow_left₀ hG0 hGD 2
        nlinarith
      refine ⟨mul_nonneg hΩ hbK0, ?_⟩
      have hb6 : 16 * (d : ℝ) ^ 4 * (h⁻¹ ^ 2 / 4) ^ 3 ≤ (d : ℝ) ^ 10 := by
        have e : 16 * (d : ℝ) ^ 4 * (h⁻¹ ^ 2 / 4) ^ 3 = (d : ℝ) ^ 4 * h⁻¹ ^ 6 / 4 := by ring
        rw [e]
        have : (d : ℝ) ^ 4 * h⁻¹ ^ 6 ≤ (d : ℝ) ^ 4 * (d : ℝ) ^ 6 :=
          mul_le_mul_of_nonneg_left h6 (by positivity)
        have e2 : (d : ℝ) ^ 4 * (d : ℝ) ^ 6 = (d : ℝ) ^ 10 := by ring
        have : (0 : ℝ) ≤ (d : ℝ) ^ 10 := by positivity
        linarith
      calc ct.OmP σ * (ct.bP h σ ⬝ᵥ (ct.KP h σ *ᵥ ct.bP h σ))
          ≤ ct.Dstar σ ^ 2 * (d : ℝ) ^ 10 :=
            mul_le_mul hΩD (hbK.trans hb6) hbK0 (sq_nonneg _)
        _ = (d : ℝ) ^ 10 * ct.Dstar σ ^ 2 := by ring
  · refine hgen (fun σ j i => ct.Dstar σ ^ m * ct.OmM σ *
      maskF (ct.XM h σ) (ct.XP h σ) (ct.bM h σ) j i ^ 2)
      (fun σ => ct.OmM σ * (ct.bM h σ ⬝ᵥ (ct.KM h σ *ᵥ ct.bM h σ))) ?_ ?_
    · intro σ hσ
      obtain ⟨hXp, hXpn, hXm, hXmn⟩ := hsupp σ hσ
      obtain ⟨hD0, hD, hG0, -, hGm0, -⟩ := hDN σ hσ
      have hXpd : ∀ i, ct.XP h σ i i ≤ h⁻¹ := lx_diag_le_of_quad hXpn
      have hXmd : ∀ i, ct.XM h σ i i ≤ h⁻¹ := lx_diag_le_of_quad hXmn
      have hb := (lx_bKb ct hR hc4 (fun l => ct.XP h σ l l / 2 * (ct.XM h σ l l / 2))
        (fun l => mul_nonneg (by have := hXp.diag_nonneg (i := l); linarith)
          (by have := hXm.diag_nonneg (i := l); linarith))
        (fun l => by
          have h0 : 0 ≤ ct.XP h σ l l := hXp.diag_nonneg
          have h1 : 0 ≤ ct.XM h σ l l := hXm.diag_nonneg
          have := mul_le_mul (hXpd l) (hXmd l) h1 hinv0
          nlinarith) (ct.KM h σ) (fun i k => by
          have hp := lx_entry_le hXp hXpd i k
          have hm := lx_entry_le hXm hXmd i k
          simp only [Contact.KM, Matrix.of_apply]
          rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
          have := mul_le_mul hp hm (abs_nonneg _) hinv0
          nlinarith)).1
      have hΩ : 0 ≤ ct.OmM σ := by unfold Contact.OmM; have := mul_nonneg hG0 hGm0; linarith
      have e : Matrix.of (fun i k => ct.XM h σ i k * ct.XP h σ i k / 4) = ct.KM h σ := by
        ext i k; simp only [Contact.KM, Matrix.of_apply]; ring
      have := lx_bm1_pt (ct.XM h σ) (ct.XP h σ) (ct.bM h σ) ct.N ct.S m hh hXm hXp hXmn hXpn hb
        (fun i hi => (hD i hi).2) hD0 hΩ
      rwa [e] at this
    · intro σ hσ
      obtain ⟨hXp, hXpn, hXm, hXmn⟩ := hsupp σ hσ
      obtain ⟨hD0, -, hG0, hGD, hGm0, hGmD⟩ := hDN σ hσ
      have hXpd : ∀ i, ct.XP h σ i i ≤ h⁻¹ := lx_diag_le_of_quad hXpn
      have hXmd : ∀ i, ct.XM h σ i i ≤ h⁻¹ := lx_diag_le_of_quad hXmn
      have hbb := lx_bKb ct hR hc4 (fun l => ct.XP h σ l l / 2 * (ct.XM h σ l l / 2))
        (fun l => mul_nonneg (by have := hXp.diag_nonneg (i := l); linarith)
          (by have := hXm.diag_nonneg (i := l); linarith))
        (fun l => by
          have h0 : 0 ≤ ct.XP h σ l l := hXp.diag_nonneg
          have h1 : 0 ≤ ct.XM h σ l l := hXm.diag_nonneg
          have := mul_le_mul (hXpd l) (hXmd l) h1 hinv0
          nlinarith) (ct.KM h σ) (fun i k => by
          have hp := lx_entry_le hXp hXpd i k
          have hm := lx_entry_le hXm hXmd i k
          simp only [Contact.KM, Matrix.of_apply]
          rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
          have := mul_le_mul hp hm (abs_nonneg _) hinv0
          nlinarith)
      have hbK : ct.bM h σ ⬝ᵥ (ct.KM h σ *ᵥ ct.bM h σ) ≤ 16 * (d : ℝ) ^ 4 * (h⁻¹ ^ 2 / 4) ^ 3 :=
        hbb.2
      have hK : (ct.KM h σ).PosSemidef := by
        have e : ct.KM h σ = (1 / 4 : ℝ) • (ct.XP h σ ⊙ ct.XM h σ) := by
          ext i k
          simp only [Contact.KM, Matrix.of_apply, Matrix.smul_apply, Matrix.hadamard_apply,
            smul_eq_mul]
          ring
        rw [e]
        exact (hXp.hadamard hXm).smul (by norm_num)
      have hbK0 : 0 ≤ ct.bM h σ ⬝ᵥ (ct.KM h σ *ᵥ ct.bM h σ) := by
        have := hK.dotProduct_mulVec_nonneg (ct.bM h σ)
        rwa [star_trivial] at this
      have hΩ : 0 ≤ ct.OmM σ := by unfold Contact.OmM; have := mul_nonneg hG0 hGm0; linarith
      have hΩD : ct.OmM σ ≤ ct.Dstar σ ^ 2 := by
        unfold Contact.OmM
        have := mul_le_mul hGD hGmD hGm0 hD0
        nlinarith
      refine ⟨mul_nonneg hΩ hbK0, ?_⟩
      have hb6 : 16 * (d : ℝ) ^ 4 * (h⁻¹ ^ 2 / 4) ^ 3 ≤ (d : ℝ) ^ 10 := by
        have e : 16 * (d : ℝ) ^ 4 * (h⁻¹ ^ 2 / 4) ^ 3 = (d : ℝ) ^ 4 * h⁻¹ ^ 6 / 4 := by ring
        rw [e]
        have : (d : ℝ) ^ 4 * h⁻¹ ^ 6 ≤ (d : ℝ) ^ 4 * (d : ℝ) ^ 6 :=
          mul_le_mul_of_nonneg_left h6 (by positivity)
        have e2 : (d : ℝ) ^ 4 * (d : ℝ) ^ 6 = (d : ℝ) ^ 10 := by ring
        have : (0 : ℝ) ≤ (d : ℝ) ^ 10 := by positivity
        linarith
      calc ct.OmM σ * (ct.bM h σ ⬝ᵥ (ct.KM h σ *ᵥ ct.bM h σ))
          ≤ ct.Dstar σ ^ 2 * (d : ℝ) ^ 10 :=
            mul_le_mul hΩD (hbK.trans hb6) hbK0 (sq_nonneg _)
        _ = (d : ℝ) ^ 10 * ct.Dstar σ ^ 2 := by ring

end BiluLinial.Tight
