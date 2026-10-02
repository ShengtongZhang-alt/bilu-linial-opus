/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.Contact.Chain1
public import BiluLinial.Tight.SecB.WeakBase

/-!
# Chain-dependent leaves of the contact estimate (Section 1.5)

The leaves of `Contact/Leaves.lean` whose proofs need (D6)/(D7) from `Contact/Chain1.lean` or the
route input `in_DR1` (`Contact/RouteDR1.lean`); see `docs/tight/CHECK_CONTACT_LEAVES.md` §1.
They are used only by `Contact/Chain2.lean`.
-/

@[expose] public section

namespace BiluLinial.Tight

open Matrix

universe u

variable {d p : ℕ}

/-! ### (D8) -/

/-- The real core of (D8). With `T = d s² - y_v Y`, `Y = n s - S_d`, `S_d = Σ_N (s - y_i)`:
`T = s²(d - n) + s S_d + Y (s - y_v)` is a sum of nonnegative terms and `a² T ≤ e`, `a² ≥ 1/(4d)`,
`s ≥ 1.98`, `e ≤ 1/10`. -/
theorem l2_d8_real {d s yv n Sd Sa Y a2 e : ℝ} (hd : 0 < d) (ha : 1 / (4 * d) ≤ a2)
    (hs : 198 / 100 ≤ s) (hyv : yv ≤ s) (hn0 : 0 ≤ n) (hn : n ≤ d) (hSd : 0 ≤ Sd)
    (hY : Y = n * s - Sd) (hY0 : 0 ≤ Y) (hXe : a2 * (d * s ^ 2 - yv * Y) ≤ e)
    (he : e ≤ 1 / 10) (hSa : Sa ≤ Sd + n * |s - 2|) :
    |yv - 2| + |n / d - 1| + 1 / d * Sa ≤ 6 * e + 2 * |s - 2| := by
  have hs0 : 0 < s := by linarith
  have hT : d * s ^ 2 - yv * Y = s ^ 2 * (d - n) + s * Sd + Y * (s - yv) := by rw [hY]; ring
  have t1 : 0 ≤ s ^ 2 * (d - n) := mul_nonneg (sq_nonneg _) (by linarith)
  have t2 : 0 ≤ s * Sd := mul_nonneg hs0.le hSd
  have t3 : 0 ≤ Y * (s - yv) := mul_nonneg hY0 (by linarith)
  have hT0 : 0 ≤ d * s ^ 2 - yv * Y := by rw [hT]; linarith
  have hTle : d * s ^ 2 - yv * Y ≤ e * (4 * d) := by
    have h1 : 1 / (4 * d) * (d * s ^ 2 - yv * Y) ≤ e :=
      (mul_le_mul_of_nonneg_right ha hT0).trans hXe
    rwa [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)] at h1
  have he0 : 0 ≤ e := by
    have : 0 ≤ 1 / (4 * d) * (d * s ^ 2 - yv * Y) := mul_nonneg (by positivity) hT0
    linarith [mul_le_mul_of_nonneg_right ha hT0]
  -- the three pieces
  have hs2 : (198 / 100) ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ (by norm_num) hs 2
  have hi : (d - n) * ((198 / 100) ^ 2) ≤ e * (4 * d) := by
    have : (d - n) * ((198 / 100) ^ 2) ≤ s ^ 2 * (d - n) := by
      rw [mul_comm]; exact mul_le_mul_of_nonneg_right hs2 (by linarith)
    linarith
  have hii : Sd * (198 / 100) ≤ e * (4 * d) := by
    have : Sd * (198 / 100) ≤ s * Sd := by rw [mul_comm]; exact mul_le_mul_of_nonneg_right hs hSd
    linarith
  have hn' : 897 / 1000 * d ≤ n := by nlinarith
  have hns : 897 / 1000 * d * (198 / 100) ≤ n * s := mul_le_mul hn' hs (by norm_num) hn0
  have hYd : 3 / 2 * d ≤ Y := by nlinarith
  have hiii : 3 / 2 * d * (s - yv) ≤ e * (4 * d) := by
    have : 3 / 2 * d * (s - yv) ≤ Y * (s - yv) := mul_le_mul_of_nonneg_right hYd (by linarith)
    linarith
  -- assemble
  have a1 : |yv - 2| ≤ (s - yv) + |s - 2| := by
    have := abs_sub_le yv s 2
    rwa [abs_of_nonpos (by linarith : yv - s ≤ 0), neg_sub] at this
  have a1' : s - yv ≤ 8 / 3 * e := by nlinarith
  have a2' : |n / d - 1| ≤ 103 / 100 * e := by
    rw [abs_sub_comm, abs_of_nonneg (by rw [sub_nonneg, div_le_one hd]; exact hn)]
    rw [show 1 - n / d = (d - n) / d by field_simp, div_le_iff₀ hd]
    nlinarith
  have a3 : 1 / d * Sa ≤ Sd / d + n / d * |s - 2| := by
    have : 1 / d * Sa ≤ 1 / d * (Sd + n * |s - 2|) := mul_le_mul_of_nonneg_left hSa (by positivity)
    calc 1 / d * Sa ≤ 1 / d * (Sd + n * |s - 2|) := this
      _ = Sd / d + n / d * |s - 2| := by ring
  have a3' : Sd / d ≤ 203 / 100 * e := by rw [div_le_iff₀ hd]; nlinarith
  have a3'' : n / d * |s - 2| ≤ |s - 2| :=
    mul_le_of_le_one_left (abs_nonneg _) (by rw [div_le_one hd]; exact hn)
  linarith

/-- **L-D8** (source (D8), l.1493–1500; AUDIT-D §3.1 D8, AUDIT-C §6 (D7)/(D8): constant `2.1`).
From (D7) (`L̄ - L ≤ C ε_s`) and the identity
`L̄ - L = a²[ds² - y_v Σ_N y_i] ≥ a² max{ds(s - y_v), s(ds - Σ_N y_i)}`:
`|y⁺_v - 2| + ||N|/d - 1| + d⁻¹ Σ_N |y⁺_i - 2| ≤ C(ε_s + η₀ + 1/d)`. Used by the leaves FS1 and
RC2 (`Ω₊ ≥ 1/5`, profile estimates). -/
theorem d8_profile : ∃ C : ℝ, 0 < C ∧ Eventually fun _c₀ _κ₀ d p _h =>
    ∀ ct : Contact.{u} d p,
      |ct.yp ct.v - 2| + |(ct.N.card : ℝ) / d - 1| + 1 / (d : ℝ) * ∑ i ∈ ct.N, |ct.yp i - 2| ≤
        C * (epsS d p + η0Of d p + 1 / (d : ℝ)) := by
  obtain ⟨C₇, hC₇, hD7⟩ := d7.{u}
  refine ⟨6 * C₇ + 2, by positivity, (hD7.and (eventually_treg_ge ⌈10 * C₇⌉₊)).mono ?_⟩
  rintro c₀ κ₀ d p h ⟨H7, hR, hp⟩ ct
  obtain ⟨-, -, hL⟩ := H7 ct
  have hd0 : (0 : ℝ) < d := hR.pfA_d_pos
  have hs2 := SecA.sOf_le_two hR
  have hη := hR.η0Of_pos
  have hη1 := hR.η0Of_le
  have hsge : 2 - η0Of d p ≤ sOf d p :=
    pf_s_ge (by linarith [hR.qOf_ge]) hη.le hη1 hR.pf_s_mul
  have habs : |sOf d p - 2| ≤ η0Of d p := by rw [abs_le]; constructor <;> linarith
  have hy : ∀ i, 0 ≤ ct.yp i ∧ ct.yp i ≤ sOf d p :=
    ct.ctx.hyp.of_mul_le_one ct.ctx.lam_le_one (by linarith)
  have hcard := (source_facts hR ct).1
  have hp10 : 10 * C₇ ≤ (p : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hp)
  have hes0 := pfA_epsS_nonneg d p
  have hes : C₇ * epsS d p ≤ 1 / 10 := by
    have h1 := hR.pfA_epsS_mul_p
    nlinarith [mul_le_mul_of_nonneg_right hp10 hes0]
  have hY : ∑ i ∈ ct.N, ct.yp i =
      (ct.N.card : ℝ) * sOf d p - ∑ i ∈ ct.N, (sOf d p - ct.yp i) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]; ring
  have hX : LbarP d p - ct.Lsum =
      aOf d p ^ 2 * ((d : ℝ) * sOf d p ^ 2 - ct.yp ct.v * ∑ i ∈ ct.N, ct.yp i) := by
    have e : ct.Lsum = aOf d p ^ 2 * ct.yp ct.v * ∑ i ∈ ct.N, ct.yp i := by
      rw [Finset.mul_sum]; rfl
    rw [e]; unfold LbarP; ring
  have hSa : ∑ i ∈ ct.N, |ct.yp i - 2| ≤
      ∑ i ∈ ct.N, (sOf d p - ct.yp i) + (ct.N.card : ℝ) * |sOf d p - 2| := by
    have e : ∑ i ∈ ct.N, (sOf d p - ct.yp i) + (ct.N.card : ℝ) * |sOf d p - 2| =
        ∑ i ∈ ct.N, ((sOf d p - ct.yp i) + |sOf d p - 2|) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    rw [e]
    refine Finset.sum_le_sum fun i _ => ?_
    have := abs_sub_le (ct.yp i) (sOf d p) 2
    rw [abs_of_nonpos (by linarith [(hy i).2] : ct.yp i - sOf d p ≤ 0)] at this
    linarith
  have hSd : 0 ≤ ∑ i ∈ ct.N, (sOf d p - ct.yp i) :=
    Finset.sum_nonneg fun i _ => by linarith [(hy i).2]
  have hY0 : 0 ≤ ∑ i ∈ ct.N, ct.yp i := Finset.sum_nonneg fun i _ => (hy i).1
  have key := l2_d8_real hd0 hR.pf_a_sq_ge (by linarith) (hy ct.v).2 (Nat.cast_nonneg _) hcard
    hSd hY hY0 (by rw [← hX]; exact hL) hes hSa
  have hd1 : 0 ≤ 1 / (d : ℝ) := by positivity
  have e2 : (6 * C₇ + 2) * (epsS d p + η0Of d p + 1 / (d : ℝ)) =
      6 * (C₇ * epsS d p) + 2 * η0Of d p +
        (6 * C₇ * η0Of d p + 6 * C₇ * (1 / (d : ℝ)) + 2 * epsS d p + 2 * (1 / (d : ℝ))) := by
    ring
  have : 0 ≤ 6 * C₇ * η0Of d p + 6 * C₇ * (1 / (d : ℝ)) + 2 * epsS d p + 2 * (1 / (d : ℝ)) := by
    positivity
  rw [e2]
  linarith

/-! ### Helpers for (RC2) and (D13) -/

/-- `a m ≤ A M` from `|a| ≤ A`, `|m| ≤ M`. -/
theorem l2_mul_le_of_abs {a m A M : ℝ} (ha : |a| ≤ A) (hm : |m| ≤ M) : a * m ≤ A * M :=
  (le_abs_self _).trans (by
    rw [abs_mul]; exact mul_le_mul ha hm (abs_nonneg _) ((abs_nonneg _).trans ha))

/-- `|a m| ≤ A M` from `|a| ≤ A`, `|m| ≤ M`. -/
theorem l2_abs_mul_le {a m A M : ℝ} (ha : |a| ≤ A) (hm : |m| ≤ M) : |a * m| ≤ A * M := by
  rw [abs_mul]; exact mul_le_mul ha hm (abs_nonneg _) ((abs_nonneg _).trans ha)

/-- Coefficient bounds for the row part of `K_i` (`q ≥ 2`). -/
theorem l2_kcoef {q : ℝ} (hq : 2 ≤ q) :
    |2 * (q - 1) * (2 * q - 3) * (2 * q - 1)| ≤ 8 * q ^ 3 ∧
    |-(12 * q * (q - 1) * (2 * q - 1))| ≤ 24 * q ^ 3 ∧
    |6 * q * (2 * q - 1) ^ 2| ≤ 24 * q ^ 3 ∧
    |-(12 * (q - 1) * (2 * q - 3))| ≤ 24 * q ^ 3 ∧
    |-(6 * q * (2 * q - 1))| ≤ 12 * q ^ 3 ∧
    |-(4 * q * (q - 1) * (2 * q - 1))| ≤ 8 * q ^ 3 ∧
    |36 * q * (q - 1)| ≤ 36 * q ^ 3 ∧ |12 * q * (q - 1)| ≤ 12 * q ^ 3 := by
  have h2 : 2 * q ≤ q ^ 2 := by nlinarith
  have h3 : 2 * q ^ 2 ≤ q ^ 3 := by nlinarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [abs_le] <;> constructor <;> nlinarith

/-- The exact split of `K_i` beyond its row-free part (sympy-checked,
`scripts/tight/check_leaves_sym.py`). -/
theorem l2_kpoly_split (p : ℕ) (x z P Q : ℝ) :
    Kpoly p x z P Q - 6 * (((p : ℝ) - 1) * P ^ 2 + p * P * Q) =
      -(6 * (p : ℝ) * (2 * p - 1)) * P * z ^ 2 +
      x ^ 2 * (2 * ((p : ℝ) - 1) * (2 * p - 3) * (2 * p - 1) * x ^ 2 +
        (-(12 * (p : ℝ) * (p - 1) * (2 * p - 1))) * (x * z) +
        6 * (p : ℝ) * (2 * p - 1) ^ 2 * z ^ 2 +
        (-(12 * ((p : ℝ) - 1) * (2 * p - 3))) * P + (-(6 * (p : ℝ) * (2 * p - 1))) * Q) +
      (x * z) * ((-(4 * (p : ℝ) * (p - 1) * (2 * p - 1))) * z ^ 2 +
        36 * (p : ℝ) * (p - 1) * P + 12 * (p : ℝ) * (p - 1) * Q) := by
  simp only [Kpoly]; ring

/-- The polynomial bound behind (D13): on the support (`x², z² ≤ D²`, `0 ≤ P, Q ≤ D²`),
`K_i - 6((p-1)P² + pPQ) ≤ 92p³D²x² + 56p³D²|xz|`. -/
theorem l2_kpoly_le {p : ℕ} (hp : 2 ≤ p) {x z P Q D : ℝ} (hx : x ^ 2 ≤ D ^ 2)
    (hz : z ^ 2 ≤ D ^ 2) (hP0 : 0 ≤ P) (hP : P ≤ D ^ 2) (hQ0 : 0 ≤ Q) (hQ : Q ≤ D ^ 2) :
    Kpoly p x z P Q - 6 * (((p : ℝ) - 1) * P ^ 2 + p * P * Q) ≤
      92 * (p : ℝ) ^ 3 * D ^ 2 * x ^ 2 + 56 * (p : ℝ) ^ 3 * D ^ 2 * |x * z| := by
  have hq : (2 : ℝ) ≤ p := by exact_mod_cast hp
  rw [l2_kpoly_split]
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩ := l2_kcoef hq
  have hD2 : 0 ≤ D ^ 2 := sq_nonneg D
  have hxz : |x * z| ≤ D ^ 2 := by
    have h1 : |x * z| ^ 2 ≤ (D ^ 2) ^ 2 := by
      rw [sq_abs, mul_pow, sq (D ^ 2)]; exact mul_le_mul hx hz (sq_nonneg _) hD2
    exact (pow_le_pow_iff_left₀ (abs_nonneg _) hD2 two_ne_zero).1 h1
  have ax : |x ^ 2| ≤ D ^ 2 := by rw [abs_of_nonneg (sq_nonneg x)]; exact hx
  have az : |z ^ 2| ≤ D ^ 2 := by rw [abs_of_nonneg (sq_nonneg z)]; exact hz
  have aP : |P| ≤ D ^ 2 := by rw [abs_of_nonneg hP0]; exact hP
  have aQ : |Q| ≤ D ^ 2 := by rw [abs_of_nonneg hQ0]; exact hQ
  have hT1 := add_le_add (add_le_add (add_le_add (add_le_add (l2_mul_le_of_abs c1 ax)
    (l2_mul_le_of_abs c2 hxz)) (l2_mul_le_of_abs c3 az)) (l2_mul_le_of_abs c4 aP))
    (l2_mul_le_of_abs c5 aQ)
  have hT2 : |(-(4 * (p : ℝ) * (p - 1) * (2 * p - 1))) * z ^ 2 + 36 * (p : ℝ) * (p - 1) * P +
      12 * (p : ℝ) * (p - 1) * Q| ≤ 8 * (p : ℝ) ^ 3 * D ^ 2 + 36 * (p : ℝ) ^ 3 * D ^ 2 +
        12 * (p : ℝ) ^ 3 * D ^ 2 := by
    refine (abs_add_le _ _).trans ?_
    refine (add_le_add (abs_add_le _ _) le_rfl).trans ?_
    exact add_le_add (add_le_add (l2_abs_mul_le c6 az) (l2_abs_mul_le c7 aP))
      (l2_abs_mul_le c8 aQ)
  have h1 : -(6 * (p : ℝ) * (2 * p - 1)) * P * z ^ 2 ≤ 0 := by
    have : 0 ≤ 6 * (p : ℝ) * (2 * p - 1) * P * z ^ 2 :=
      mul_nonneg (mul_nonneg (by nlinarith) hP0) (sq_nonneg z)
    linarith
  have h2 := mul_le_mul_of_nonneg_left hT1 (sq_nonneg x)
  have h3 := l2_mul_le_of_abs (le_refl |x * z|) hT2
  have e1 : x ^ 2 * (8 * (p : ℝ) ^ 3 * D ^ 2 + 24 * (p : ℝ) ^ 3 * D ^ 2 +
      24 * (p : ℝ) ^ 3 * D ^ 2 + 24 * (p : ℝ) ^ 3 * D ^ 2 + 12 * (p : ℝ) ^ 3 * D ^ 2) =
      92 * (p : ℝ) ^ 3 * D ^ 2 * x ^ 2 := by ring
  have e2 : |x * z| * (8 * (p : ℝ) ^ 3 * D ^ 2 + 36 * (p : ℝ) ^ 3 * D ^ 2 +
      12 * (p : ℝ) ^ 3 * D ^ 2) = 56 * (p : ℝ) ^ 3 * D ^ 2 * |x * z| := by ring
  linarith


/-- `(M⁻¹)_ij² ≤ (M⁻¹)_ii (M⁻¹)_jj` for `M ≻ 0` (the `2 × 2` principal minor of `M⁻¹ ⪰ 0`). -/
theorem l2_inv_offdiag_sq {n : Type*} [Fintype n] [DecidableEq n] {M : Matrix n n ℝ}
    (hM : M.PosDef) (i j : n) : M⁻¹ i j ^ 2 ≤ M⁻¹ i i * M⁻¹ j j := by
  have hS : (M⁻¹.submatrix ![i, j] ![i, j]).PosSemidef := hM.inv.posSemidef.submatrix _
  have h := hS.det_nonneg
  rw [Matrix.det_fin_two] at h
  simp only [Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] at h
  have hsym : M⁻¹ j i = M⁻¹ i j := by
    have := hM.inv.isHermitian.apply i j
    simpa using this
  rw [hsym] at h
  nlinarith

/-- On a supported signing, `(G_ij)² ≤ G_ii G_jj` for the physical inverse. -/
theorem l2_green_sq_le {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {a τ : ℝ} {y : V → ℝ} {σ : Config V} {S : Finset V}
    (hP : (precN G a τ y σ S).PosDef) (hy : ∀ k, 0 ≤ y k) (i j : V) :
    greenP G a τ y σ S i j ^ 2 ≤ greenP G a τ y σ S i i * greenP G a τ y σ S j j := by
  have h := l2_inv_offdiag_sq hP i j
  rw [SecB.greenP_diag G σ S (hy i), SecB.greenP_diag G σ S (hy j)]
  unfold greenP hN
  have hi := Real.sq_sqrt (hy i)
  have hj := Real.sq_sqrt (hy j)
  calc (Real.sqrt (y i) * (precN G a τ y σ S)⁻¹ i j * Real.sqrt (y j)) ^ 2
      = y i * y j * (precN G a τ y σ S)⁻¹ i j ^ 2 := by rw [mul_pow, mul_pow, hi, hj]; ring
    _ ≤ y i * y j * ((precN G a τ y σ S)⁻¹ i i * (precN G a τ y σ S)⁻¹ j j) :=
        mul_le_mul_of_nonneg_left h (mul_nonneg (hy i) (hy j))
    _ = _ := by ring

/-- The quadratic form of the masks: `uᵀ D_f (c (A D_f u)) = c Σ_{i,k} u_i u_k A_ik f_i f_k`. -/
theorem l2_quad {ι : Type*} [Fintype ι] [DecidableEq ι] (u f : ι → ℝ) (A : Matrix ι ι ℝ)
    (c : ℝ) : u ⬝ᵥ (diagonal f *ᵥ (c • (A *ᵥ (diagonal f *ᵥ u)))) =
      c * ∑ i, ∑ k, u i * u k * A i k * (f i * f k) := by
  have h2 : ∀ w : ι → ℝ, diagonal f *ᵥ w = fun k => f k * w k :=
    fun w => funext fun k => mulVec_diagonal f w k
  rw [h2, h2]
  simp only [dotProduct, Pi.smul_apply, smul_eq_mul, mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring

/-- For `c, a, b ≥ 0`: `(cab)² ≥ 1 - 2(|c-1| + |a-1| + |b-1|)` (via `min(·,1)` and
`xyz ≥ x + y + z - 2` on `[0,1]³`). -/
theorem l2_prod_sq_ge {c a b : ℝ} (hc : 0 ≤ c) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    1 - 2 * (|c - 1| + |a - 1| + |b - 1|) ≤ (c * a * b) ^ 2 := by
  have hm : ∀ t : ℝ, 0 ≤ t → 1 - |t - 1| ≤ min t 1 ∧ 0 ≤ min t 1 ∧ min t 1 ≤ 1 ∧ min t 1 ≤ t :=
    fun t ht => by
      refine ⟨?_, le_min ht zero_le_one, min_le_right _ _, min_le_left _ _⟩
      rcases le_total t 1 with h | h
      · rw [min_eq_left h, abs_of_nonpos (by linarith)]; linarith
      · rw [min_eq_right h]; linarith [abs_nonneg (t - 1)]
  obtain ⟨x1, x0, x2, x3⟩ := hm c hc
  obtain ⟨y1, y0, y2, y3⟩ := hm a ha
  obtain ⟨z1, z0, z2, z3⟩ := hm b hb
  have hxy : min c 1 + min a 1 - 1 ≤ min c 1 * min a 1 := by
    nlinarith [mul_nonneg (sub_nonneg.2 x2) (sub_nonneg.2 y2)]
  have hxy1 : min c 1 * min a 1 ≤ 1 := by nlinarith
  have hxyz : min c 1 * min a 1 + min b 1 - 1 ≤ min c 1 * min a 1 * min b 1 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hxy1) (sub_nonneg.2 z2)]
  have hmono : min c 1 * min a 1 * min b 1 ≤ c * a * b :=
    mul_le_mul (mul_le_mul x3 y3 y0 hc) z3 z0 (mul_nonneg hc ha)
  nlinarith [sq_nonneg (c * a * b - 1)]

/-- The termwise bound of (RC2): for `c, a_i, a_k ≥ 0`,
`2(c d a_i b_i a_k b_k - c² a_i² a_k²) ≤ d² b_i² b_k² - 1 + 2(|c-1| + |a_i-1| + |a_k-1|)`. -/
theorem l2_rc2_term {c dv ai bi ak bk : ℝ} (hc : 0 ≤ c) (hai : 0 ≤ ai) (hak : 0 ≤ ak) :
    2 * (c * dv * (ai * bi * (ak * bk)) - c ^ 2 * (ai ^ 2 * ak ^ 2)) ≤
      dv ^ 2 * bi ^ 2 * bk ^ 2 - 1 + 2 * (|c - 1| + |ai - 1| + |ak - 1|) := by
  have h := l2_prod_sq_ge hc hai hak
  nlinarith [sq_nonneg (c * ai * ak - dv * bi * bk)]


/-- `B₂² - 2r + 1 ≤ 8(ε/p + ε²)` for `B₂ = (pr - 2)/(p - 2)`, `r = 1 + ε`, `p ≥ 4`. -/
theorem l2_B2_real' {P ε : ℝ} (hP : 4 ≤ P) (hε : 0 ≤ ε) :
    ((P * (1 + ε) - 2) / (P - 2)) ^ 2 - 2 * (1 + ε) + 1 ≤ 8 * (ε / P + ε ^ 2) := by
  have hu : 0 < P - 2 := by linarith
  have hP0 : 0 < P := by linarith
  have e : ((P * (1 + ε) - 2) / (P - 2)) ^ 2 - 2 * (1 + ε) + 1 =
      4 * ε / (P - 2) + (P / (P - 2)) ^ 2 * ε ^ 2 := by
    field_simp; ring
  have h1 : 4 * ε / (P - 2) ≤ 8 * ε / P := by
    rw [div_le_div_iff₀ hu hP0]; nlinarith
  have h2 : (P / (P - 2)) ^ 2 ≤ 4 := by
    rw [div_pow, div_le_iff₀ (pow_pos hu 2)]; nlinarith
  have h3 := mul_le_mul_of_nonneg_right h2 (sq_nonneg ε)
  have e2 : 8 * (ε / P + ε ^ 2) = 8 * ε / P + 8 * ε ^ 2 := by ring
  rw [e, e2]
  nlinarith [sq_nonneg ε]

/-- `B₂² - 2r + 1 ≤ 8((r-1)/p + (r-1)²)`, `B₂ = (pr - 2)/(p - 2)`. -/
theorem l2_B2_real {P r : ℝ} (hP : 4 ≤ P) (hr : 1 ≤ r) :
    ((P * r - 2) / (P - 2)) ^ 2 - 2 * r + 1 ≤ 8 * ((r - 1) / P + (r - 1) ^ 2) := by
  have h := l2_B2_real' hP (sub_nonneg.2 hr)
  rwa [add_sub_cancel] at h

/-- `B₆⁶ ≤ 1 + 24ε` for `B₆ = (pr - 6)/(p - 6)`, `r = 1 + ε ≤ 1.01`, `p ≥ 12`. -/
theorem l2_B6_real' {P ε : ℝ} (hP : 12 ≤ P) (hε : 0 ≤ ε) (hε1 : ε ≤ 1 / 100) :
    ((P * (1 + ε) - 6) / (P - 6)) ^ 6 ≤ 1 + 24 * ε := by
  have hu : 0 < P - 6 := by linarith
  have hB : (P * (1 + ε) - 6) / (P - 6) = 1 + P * ε / (P - 6) := by field_simp; ring
  have hB1 : P * ε / (P - 6) ≤ 2 * ε := by rw [div_le_iff₀ hu]; nlinarith
  have hB0 : 0 ≤ P * ε / (P - 6) := div_nonneg (by positivity) hu.le
  rw [hB]
  set y := 2 * ε with hy
  have hy0 : 0 ≤ y := by positivity
  have hy1 : y ≤ 1 / 50 := by linarith
  have s0 : (1 + P * ε / (P - 6)) ^ 6 ≤ (1 + y) ^ 6 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 6
  have s1 : (1 + y) ^ 2 ≤ 1 + 3 * y := by nlinarith
  have s2 : (1 + 3 * y) ^ 2 ≤ 1 + 7 * y := by nlinarith
  have s3 : (1 + y) ^ 6 ≤ (1 + 3 * y) ^ 3 := by
    rw [show (1 + y) ^ 6 = ((1 + y) ^ 2) ^ 3 by ring]
    exact pow_le_pow_left₀ (by positivity) s1 3
  have s4 : (1 + 3 * y) ^ 3 ≤ (1 + 7 * y) * (1 + 3 * y) := by
    rw [pow_succ]; exact mul_le_mul_of_nonneg_right s2 (by positivity)
  have s5 : (1 + 7 * y) * (1 + 3 * y) ≤ 1 + 11 * y := by nlinarith
  linarith

theorem l2_B6_real {P r : ℝ} (hP : 12 ≤ P) (hr : 1 ≤ r) (hr1 : r ≤ 101 / 100) :
    ((P * r - 6) / (P - 6)) ^ 6 ≤ 1 + 24 * (r - 1) := by
  have h := l2_B6_real' hP (sub_nonneg.2 hr) (by linarith)
  rwa [add_sub_cancel] at h

/-- AM–GM for three nonnegative reals. -/
theorem l2_amgm3 {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    x * y * z ≤ (x ^ 3 + y ^ 3 + z ^ 3) / 3 := by
  nlinarith [mul_nonneg (add_nonneg (add_nonneg hx hy) hz)
    (add_nonneg (add_nonneg (sq_nonneg (x - y)) (sq_nonneg (y - z))) (sq_nonneg (z - x)))]

/-- The closing algebra of (D13). -/
theorem l2_d13_real {A q d δ S Sm CU C₇ C₂ X : ℝ} (hd : 0 < d) (hq1 : 1 ≤ q) (hA0 : 0 ≤ A)
    (hA : A ≤ 1 / d) (hδq : q / d ≤ δ) (hδ1 : 1 / d ≤ δ) (hS : S ≤ C₇ * q)
    (hSm : A * Sm ≤ C₂ * δ) (hCU : 0 ≤ CU) (hC₇ : 0 ≤ C₇) (hC₂ : 0 ≤ C₂)
    (hX : X ≤ (92 + 28 * (d * Real.sqrt (q * δ / d) / q)) * q ^ 3 * (CU * (S + 1)) +
      28 / (d * Real.sqrt (q * δ / d) / q) * q ^ 3 * (CU * (Sm + 1))) :
    A ^ 2 / 3 * X ≤ A * (50 * CU * (C₇ + C₂ + 1) * q ^ 3 * Real.sqrt (q * δ / d)) := by
  have hq : 0 < q := by linarith
  have hδ0 : 0 < δ := lt_of_lt_of_le (by positivity) hδ1
  set w := Real.sqrt (q * δ / d) with hw
  have hw0 : 0 < w := Real.sqrt_pos.2 (by positivity)
  have hw2 : w ^ 2 = q * δ / d := Real.sq_sqrt (by positivity)
  set t := d * w / q with ht
  have ht0 : 0 < t := by positivity
  have hqw : q / d ≤ w := by
    have h : (q / d) ^ 2 ≤ q * δ / d := by
      rw [sq, show q * δ / d = q / d * δ by ring]
      exact mul_le_mul_of_nonneg_left hδq (by positivity)
    exact (le_abs_self _).trans (Real.abs_le_sqrt h)
  have htq : t * (q / d) = w := by rw [ht]; field_simp
  have hδt : δ / t = w := by
    rw [ht, div_div_eq_mul_div, div_eq_iff (by positivity)]
    have : δ * q = w ^ 2 * d := by rw [hw2]; field_simp
    nlinarith
  have a1 : A * (S + 1) ≤ (C₇ + 1) * (q / d) := by
    calc A * (S + 1) ≤ A * (C₇ * q + 1) := mul_le_mul_of_nonneg_left (by linarith) hA0
      _ ≤ 1 / d * (C₇ * q + 1) := mul_le_mul_of_nonneg_right hA (by positivity)
      _ ≤ 1 / d * (C₇ * q + q) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = (C₇ + 1) * (q / d) := by ring
  have a2 : A * (Sm + 1) ≤ (C₂ + 1) * δ := by nlinarith
  have hAX : A * X ≤
      q ^ 3 * CU * ((92 + 28 * t) * (A * (S + 1)) + 28 * ((1 / t) * (A * (Sm + 1)))) := by
    have := mul_le_mul_of_nonneg_left hX hA0
    have e : A * ((92 + 28 * t) * q ^ 3 * (CU * (S + 1)) + 28 / t * q ^ 3 * (CU * (Sm + 1))) =
        q ^ 3 * CU * ((92 + 28 * t) * (A * (S + 1)) + 28 * ((1 / t) * (A * (Sm + 1)))) := by
      field_simp
    linarith
  have b1 : (92 + 28 * t) * (A * (S + 1)) ≤ (C₇ + 1) * (92 * w + 28 * w) := by
    have := mul_le_mul_of_nonneg_left a1 (by positivity : (0 : ℝ) ≤ 92 + 28 * t)
    have e : (92 + 28 * t) * ((C₇ + 1) * (q / d)) =
        (C₇ + 1) * (92 * (q / d) + 28 * (t * (q / d))) := by
      ring
    rw [e, htq] at this
    nlinarith
  have b2 : (1 / t) * (A * (Sm + 1)) ≤ (C₂ + 1) * w := by
    have := mul_le_mul_of_nonneg_left a2 (by positivity : (0 : ℝ) ≤ 1 / t)
    rw [show 1 / t * ((C₂ + 1) * δ) = (C₂ + 1) * (δ / t) by ring, hδt] at this
    exact this
  have hB : q ^ 3 * CU * ((92 + 28 * t) * (A * (S + 1)) + 28 * ((1 / t) * (A * (Sm + 1)))) ≤
      q ^ 3 * CU * (150 * (C₇ + C₂ + 1) * w) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    nlinarith
  calc A ^ 2 / 3 * X = A / 3 * (A * X) := by ring
    _ ≤ A / 3 * (q ^ 3 * CU * (150 * (C₇ + C₂ + 1) * w)) :=
        mul_le_mul_of_nonneg_left (hAX.trans hB) (by positivity)
    _ = A * (50 * CU * (C₇ + C₂ + 1) * q ^ 3 * w) := by ring


/-- `3(1 + d + d²) ≤ 21^{c'+2}` once `log d ≤ c'`. -/
theorem l2_pow21 {d : ℝ} (hd1 : 1 ≤ d) {c' : ℕ} (hcl : Real.log d ≤ c') :
    3 * (1 + d + d ^ 2) ≤ 21 ^ (c' + 2) := by
  have hd0 : 0 < d := by linarith
  have hdexp : d ≤ Real.exp 1 ^ c' := by
    rw [← Real.exp_nat_mul, mul_one]
    calc d = Real.exp (Real.log d) := (Real.exp_log hd0).symm
      _ ≤ Real.exp c' := Real.exp_le_exp.mpr hcl
  have he : Real.exp 1 ^ 2 ≤ 8 := by
    have := Real.exp_one_lt_d9; have := Real.exp_pos 1; nlinarith
  have hd2 : d ^ 2 ≤ 8 ^ c' :=
    calc d ^ 2 ≤ (Real.exp 1 ^ c') ^ 2 := pow_le_pow_left₀ hd0.le hdexp 2
      _ = (Real.exp 1 ^ 2) ^ c' := by rw [← pow_mul, ← pow_mul, mul_comm]
      _ ≤ 8 ^ c' := pow_le_pow_left₀ (by positivity) he c'
  have h8 : (8 : ℝ) ^ c' ≤ 21 ^ c' := pow_le_pow_left₀ (by norm_num) (by norm_num) c'
  have : 3 * (1 + d + d ^ 2) ≤ 9 * d ^ 2 := by nlinarith
  rw [pow_add]
  nlinarith

/-- **UMI with `D_*` envelopes** (Tools `wavg_mul_le_umi`, `SecB.dstar_moment`): if
`0 ≤ Y ≤ D_*^{m₁}` and `0 ≤ Z ≤ D_*^{m₂}` on the support, then `E[YZ] ≤ C(E Y + 1/d)`, with
moment order `k = ⌈log d⌉ + 2` and floor `θ = 1/d`. -/
theorem l2_umi (m₁ m₂ : ℕ) (hm₁ : 1 ≤ m₁) (hm₂ : 1 ≤ m₂) :
    ∃ C : ℝ, 0 < C ∧ Eventually fun _c₀ _κ₀ d p _h => ∀ ct : Contact.{u} d p,
      ∀ Y Z : Config ct.V → ℝ,
      (∀ σ, wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 → 0 ≤ Y σ ∧ Y σ ≤ ct.Dstar σ ^ m₁) →
      (∀ σ, wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 → 0 ≤ Z σ ∧ Z σ ≤ ct.Dstar σ ^ m₂) →
      ct.E (fun σ => Y σ * Z σ) ≤ C * (ct.E Y + 1 / (d : ℝ)) := by
  refine ⟨3 * (21 * 12 ^ m₁) * (21 * 12 ^ m₂), by positivity, ?_⟩
  refine ((SecB.dstar_moment.and (SecB.eventually_log_le_p (2 * ((m₁ : ℝ) + m₂)))).and
    (SecB.eventually_base 0)).mono ?_
  rintro c₀ κ₀ d p h ⟨⟨hDs, hlp⟩, hR, -⟩ ct Y Z hY hZ
  have hd1 : (1 : ℝ) ≤ d := by have := hR.ten_pow_six_le_d; linarith
  have hd0 : (0 : ℝ) < d := by linarith
  have hlogd : 0 ≤ Real.log d := Real.log_nonneg hd1
  obtain ⟨c', hc'⟩ : ∃ c' : ℕ, c' = ⌈Real.log d⌉₊ := ⟨_, rfl⟩
  have hcl : Real.log d ≤ c' := hc' ▸ Nat.le_ceil _
  have hcu : (c' : ℝ) < Real.log d + 1 := hc' ▸ Nat.ceil_lt_add_one hlogd
  have hk2 : 2 ≤ c' + 2 := by omega
  have hmk : ∀ m : ℕ, m ≤ m₁ + m₂ → 2 * (m * (c' + 2)) ≤ p := by
    intro m hm
    have h1 : 2 * ((m₁ : ℝ) + m₂) * ((c' : ℝ) + 2) ≤ p := by
      have : (c' : ℝ) + 2 ≤ Real.log d + 3 := by linarith
      calc 2 * ((m₁ : ℝ) + m₂) * ((c' : ℝ) + 2) ≤ 2 * ((m₁ : ℝ) + m₂) * (Real.log d + 3) :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ ≤ p := hlp
    have hm' : (m : ℝ) ≤ m₁ + m₂ := by exact_mod_cast hm
    have h2 : ((2 * (m * (c' + 2)) : ℕ) : ℝ) ≤ 2 * ((m₁ : ℝ) + m₂) * ((c' : ℝ) + 2) := by
      push_cast
      nlinarith
    exact_mod_cast h2.trans h1
  have hpow21 := l2_pow21 hd1 hcl
  have hs := hR.sOf_pos
  have hsub : ∀ y : ct.V → ℝ, InCube (ct.lam * sOf d p) y → InCube (sOf d p) y :=
    fun y hy => hy.of_mul_le_one ct.ctx.lam_le_one hs.le
  have hZw : 0 < Zw ct.G p (aOf d p) ct.yp ct.ym ct.S :=
    ct.ctx.pos ct.yp ct.ym (hsub _ ct.ctx.hyp) (hsub _ ct.ctx.hym)
  have henv : ∀ m : ℕ, 1 ≤ m → m ≤ m₁ + m₂ → ∀ F : Config ct.V → ℝ,
      (∀ σ, wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 → 0 ≤ F σ ∧ F σ ≤ ct.Dstar σ ^ m) →
      ct.E (fun σ => max (F σ) 0 ^ (c' + 2)) ≤ (21 * 12 ^ m) ^ (c' + 2) := by
    intro m hm1 hm2 F hF
    have hn1 : 1 ≤ m * (c' + 2) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    calc ct.E (fun σ => max (F σ) 0 ^ (c' + 2)) ≤ ct.E (fun σ => ct.Dstar σ ^ (m * (c' + 2))) :=
          SecB.lawE_mono ct.G fun σ hσ => by
            rw [max_eq_left (hF σ hσ).1, pow_mul]
            exact pow_le_pow_left₀ (hF σ hσ).1 (hF σ hσ).2 _
      _ ≤ 3 * (1 + d + (d : ℝ) ^ 2) * 12 ^ (m * (c' + 2)) := hDs ct _ hn1 (hmk m hm2)
      _ ≤ 21 ^ (c' + 2) * 12 ^ (m * (c' + 2)) :=
          mul_le_mul_of_nonneg_right hpow21 (by positivity)
      _ = (21 * 12 ^ m) ^ (c' + 2) := by rw [mul_pow, ← pow_mul]
  have hYk := henv m₁ hm₁ (by omega) Y hY
  have hZk := henv m₂ hm₂ (by omega) Z hZ
  have humi := wavg_mul_le_umi (fun σ => wt_nonneg ct.G σ) hZw
    (Y := fun σ => max (Y σ) 0) (Z := fun σ => max (Z σ) 0) (fun σ => le_max_right _ _)
    (fun σ => le_max_right _ _) hk2 (M := 21 * 12 ^ m₁) (B := 21 * 12 ^ m₂) (θ := 1 / (d : ℝ))
    (by positivity) (by positivity) (by positivity) hYk hZk
  have eYZ : ct.E (fun σ => Y σ * Z σ) = wavg (fun σ => wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S)
      (fun σ => max (Y σ) 0 * max (Z σ) 0) :=
    lawE_congr ct.G fun σ hσ => by rw [max_eq_left (hY σ hσ).1, max_eq_left (hZ σ hσ).1]
  have eY : ct.E Y = wavg (fun σ => wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S)
      (fun σ => max (Y σ) 0) :=
    lawE_congr ct.G fun σ hσ => by rw [max_eq_left (hY σ hσ).1]
  have hEY0 : 0 ≤ ct.E Y := lawE_nonneg ct.G fun σ hσ => (hY σ hσ).1
  -- the interpolation loss
  set M : ℝ := 21 * 12 ^ m₁ with hM
  have hM1 : 1 ≤ M := by
    rw [hM]; have := one_le_pow₀ (M₀ := ℝ) (by norm_num : (1:ℝ) ≤ 12) (n := m₁); nlinarith
  have hk1 : (1 : ℝ) ≤ ((c' + 2 : ℕ) : ℝ) - 1 := by
    push_cast; linarith [Nat.cast_nonneg (α := ℝ) c']
  set l := 1 / (((c' + 2 : ℕ) : ℝ) - 1) with hl
  have hl0 : 0 ≤ l := by rw [hl]; exact div_nonneg zero_le_one (by linarith)
  have hl1 : l ≤ 1 := by rw [hl, div_le_one (by linarith)]; exact hk1
  have hloss : (M / (1 / (d : ℝ))) ^ l ≤ 3 * M := by
    rw [show M / (1 / (d : ℝ)) = M * d by field_simp, Real.mul_rpow (by linarith) hd0.le]
    have h1 : M ^ l ≤ M := by
      calc M ^ l ≤ M ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hM1 hl1
        _ = M := Real.rpow_one M
    have h2 : (d : ℝ) ^ l ≤ 3 := by
      calc (d : ℝ) ^ l = Real.exp (Real.log d * l) := Real.rpow_def_of_pos hd0 _
        _ ≤ Real.exp 1 := Real.exp_le_exp.mpr (by
            rw [hl, mul_one_div, div_le_one (by linarith)]; push_cast; linarith)
        _ ≤ 3 := by have := Real.exp_one_lt_d9; linarith
    have h3 : 0 ≤ M ^ l := Real.rpow_nonneg (by linarith) _
    have h4 : 0 ≤ (d : ℝ) ^ l := Real.rpow_nonneg hd0.le _
    nlinarith
  rw [eYZ]
  rw [← eY] at humi
  calc _ ≤ (21 * 12 ^ m₂) * (M / (1 / (d : ℝ))) ^ l * (ct.E Y + 1 / (d : ℝ)) := humi
    _ ≤ (21 * 12 ^ m₂) * (3 * M) * (ct.E Y + 1 / (d : ℝ)) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left hloss (by positivity)
    _ = 3 * M * (21 * 12 ^ m₂) * (ct.E Y + 1 / (d : ℝ)) := by ring


/-- `2|xz| ≤ t x² + z²/t` for `t > 0`. -/
theorem l2_amgm_t {x z t : ℝ} (ht : 0 < t) : 2 * |x * z| ≤ t * x ^ 2 + z ^ 2 / t := by
  rw [abs_mul, ← sq_abs x, ← sq_abs z]
  have h : 0 ≤ (t * |x| - |z|) ^ 2 / t := div_nonneg (sq_nonneg _) ht.le
  have e : (t * |x| - |z|) ^ 2 / t = t * |x| ^ 2 + |z| ^ 2 / t - 2 * (|x| * |z|) := by
    field_simp; ring
  linarith

/-- `√(a + b) ≤ √a + √b`. -/
theorem l2_sqrt_add_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]

/-- `√x ≤ (v + x/v)/2` for `v > 0`. -/
theorem l2_sqrt_le_amgm {x v : ℝ} (hx : 0 ≤ x) (hv : 0 < v) : Real.sqrt x ≤ (v + x / v) / 2 := by
  have h := sq_nonneg (Real.sqrt x - v)
  have e := Real.sq_sqrt hx
  have : Real.sqrt x * (2 * v) ≤ v ^ 2 + x := by nlinarith
  have e2 : (v + x / v) / 2 = (v ^ 2 + x) / (2 * v) := by field_simp
  rw [e2, le_div_iff₀ (by positivity)]
  exact this

section ContactHelpers


theorem l2_E_add (ct : Contact.{u} d p) (f g : Config ct.V → ℝ) :
    ct.E (fun σ => f σ + g σ) = ct.E f + ct.E g := lawE_add ct.G f g

theorem l2_E_sub (ct : Contact.{u} d p) (f g : Config ct.V → ℝ) :
    ct.E (fun σ => f σ - g σ) = ct.E f - ct.E g := lawE_sub ct.G f g

theorem l2_E_const_mul (ct : Contact.{u} d p) (c : ℝ) (f : Config ct.V → ℝ) :
    ct.E (fun σ => c * f σ) = c * ct.E f := lawE_const_mul ct.G c f

theorem l2_E_sum (ct : Contact.{u} d p) {ι : Type*} (s : Finset ι) (f : ι → Config ct.V → ℝ) :
    ct.E (fun σ => ∑ l ∈ s, f l σ) = ∑ l ∈ s, ct.E (f l) := lawE_sum ct.G s f

theorem l2_E_mono (ct : Contact.{u} d p) {f g : Config ct.V → ℝ}
    (h : ∀ σ, wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 → f σ ≤ g σ) : ct.E f ≤ ct.E g :=
  SecB.lawE_mono ct.G h

theorem l2_inCube (hR : TRegime d p) (ct : Contact.{u} d p) :
    InCube (sOf d p) ct.yp ∧ InCube (sOf d p) ct.ym :=
  ⟨ct.ctx.hyp.of_mul_le_one ct.ctx.lam_le_one hR.sOf_pos.le,
    ct.ctx.hym.of_mul_le_one ct.ctx.lam_le_one hR.sOf_pos.le⟩

theorem l2_Zw_pos (hR : TRegime d p) (ct : Contact.{u} d p) :
    0 < Zw ct.G p (aOf d p) ct.yp ct.ym ct.S :=
  ct.ctx.pos ct.yp ct.ym (l2_inCube hR ct).1 (l2_inCube hR ct).2

theorem l2_E_const (hR : TRegime d p) (ct : Contact.{u} d p) (c : ℝ) :
    ct.E (fun _ => c) = c := SecB.lawE_const ct.G (l2_Zw_pos hR ct).ne' c

theorem l2_y_le_two (hR : TRegime d p) (ct : Contact.{u} d p) (k : ct.V) :
    (0 ≤ ct.yp k ∧ ct.yp k ≤ 2) ∧ (0 ≤ ct.ym k ∧ ct.ym k ≤ 2) := by
  have hs := SecA.sOf_le_two hR
  obtain ⟨h1, h2⟩ := l2_inCube hR ct
  exact ⟨⟨(h1 k).1, (h1 k).2.trans hs⟩, ⟨(h2 k).1, (h2 k).2.trans hs⟩⟩

/-- Jensen: `E|f| ≤ √(E f²)`. -/
theorem l2_E_abs_le (hR : TRegime d p) (ct : Contact.{u} d p) (f : Config ct.V → ℝ) :
    ct.E (fun σ => |f σ|) ≤ Real.sqrt (ct.E fun σ => f σ ^ 2) := by
  have h := wavg_mul_sq_le (w := fun σ => wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S)
    (fun σ => wt_nonneg ct.G σ) (fun σ => |f σ|) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, sq_abs] at h
  rw [wavg_const (l2_Zw_pos hR ct), mul_one] at h
  exact (le_abs_self _).trans (Real.abs_le_sqrt h)

/-- (F2) with `k = 2`: `E(h_i⁺ - 1)² ≤ 8ρ + 2(r - E h_i⁺)`, `ρ = ε/p + ε²`. -/
theorem l2_var_bound (hR : TRegime d p) (ct : Contact.{u} d p) {i : ct.V} (hi : i ∈ ct.S) :
    ct.E (fun σ => (hN ct.G (aOf d p) 1 ct.yp σ ct.S i - 1) ^ 2) ≤
      8 * (epsP d p / p + epsP d p ^ 2) + 2 * (rOf d p - ct.mp i) := by
  have hp4 : (4 : ℝ) ≤ p := by have := hR.pfA_p_ge; linarith
  have hF2 : ct.E (fun σ => hN ct.G (aOf d p) 1 ct.yp σ ct.S i ^ 2) ≤
      (((p : ℝ) * rOf d p - 2) / ((p : ℝ) - 2)) ^ 2 := by
    have := (source_moments ct.G hR ct.ctx.toCapCtx ct.ctx.hyp ct.ctx.hym hi (k := 2)
      (by norm_num) (by have := hR.hp; omega)).1
    push_cast at this
    exact this
  have e : ct.E (fun σ => (hN ct.G (aOf d p) 1 ct.yp σ ct.S i - 1) ^ 2) =
      ct.E (fun σ => hN ct.G (aOf d p) 1 ct.yp σ ct.S i ^ 2) - 2 * ct.mp i + 1 := by
    have e1 : (fun σ => (hN ct.G (aOf d p) 1 ct.yp σ ct.S i - 1) ^ 2) = fun σ =>
        (hN ct.G (aOf d p) 1 ct.yp σ ct.S i ^ 2 - 2 * hN ct.G (aOf d p) 1 ct.yp σ ct.S i) + 1 := by
      funext σ; ring
    rw [e1, l2_E_add, l2_E_sub, l2_E_const_mul, l2_E_const hR ct]
    rfl
  rw [e]
  have hB := l2_B2_real (P := p) (r := rOf d p) hp4 hR.one_lt_rOf.le
  unfold epsP
  linarith

/-- The contact-root estimate: `E|G⁺_vv/2 - 1| ≤ 3√ρ + |y_v - 2|/2`. -/
theorem l2_E1 (hR : TRegime d p) (ct : Contact.{u} d p) :
    ct.E (fun σ => |ct.gp σ ct.v ct.v / 2 - 1|) ≤
      3 * Real.sqrt (epsP d p / p + epsP d p ^ 2) + |ct.yp ct.v - 2| / 2 := by
  have hρ : 0 ≤ epsP d p / p + epsP d p ^ 2 := by
    have := hR.pfA_epsP_nonneg; have := hR.pfA_p_pos; positivity
  have hy := (l2_y_le_two hR ct ct.v).1
  have hvar := l2_var_bound hR ct ct.ctx.mem
  have hc : ct.mp ct.v = rOf d p := ct.ctx.contact
  rw [hc, sub_self, mul_zero, add_zero] at hvar
  have h1 : ct.E (fun σ => |hN ct.G (aOf d p) 1 ct.yp σ ct.S ct.v - 1|) ≤
      3 * Real.sqrt (epsP d p / p + epsP d p ^ 2) := by
    refine (l2_E_abs_le hR ct _).trans ?_
    calc Real.sqrt (ct.E fun σ => (hN ct.G (aOf d p) 1 ct.yp σ ct.S ct.v - 1) ^ 2)
        ≤ Real.sqrt (9 * (epsP d p / p + epsP d p ^ 2)) := Real.sqrt_le_sqrt (by linarith)
      _ = 3 * Real.sqrt (epsP d p / p + epsP d p ^ 2) := by
          rw [Real.sqrt_mul (by norm_num), show (9 : ℝ) = 3 ^ 2 by norm_num,
            Real.sqrt_sq (by norm_num)]
  have hpt : ∀ σ, |ct.gp σ ct.v ct.v / 2 - 1| ≤
      1 * |hN ct.G (aOf d p) 1 ct.yp σ ct.S ct.v - 1| + |ct.yp ct.v - 2| / 2 := by
    intro σ
    have e : ct.gp σ ct.v ct.v = ct.yp ct.v * hN ct.G (aOf d p) 1 ct.yp σ ct.S ct.v :=
      SecB.greenP_diag ct.G σ ct.S hy.1
    rw [e]
    have e2 : ct.yp ct.v * hN ct.G (aOf d p) 1 ct.yp σ ct.S ct.v / 2 - 1 =
        ct.yp ct.v / 2 * (hN ct.G (aOf d p) 1 ct.yp σ ct.S ct.v - 1) + (ct.yp ct.v - 2) / 2 := by
      ring
    rw [e2]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ ct.yp ct.v / 2), abs_div, abs_two]
    have := abs_nonneg (hN ct.G (aOf d p) 1 ct.yp σ ct.S ct.v - 1)
    have h2 : ct.yp ct.v / 2 ≤ 1 := by linarith
    nlinarith
  calc ct.E (fun σ => |ct.gp σ ct.v ct.v / 2 - 1|)
      ≤ ct.E (fun σ => 1 * |hN ct.G (aOf d p) 1 ct.yp σ ct.S ct.v - 1| +
          |ct.yp ct.v - 2| / 2) := l2_E_mono ct fun σ _ => hpt σ
    _ = ct.E (fun σ => |hN ct.G (aOf d p) 1 ct.yp σ ct.S ct.v - 1|) + |ct.yp ct.v - 2| / 2 := by
        rw [l2_E_add, l2_E_const_mul, l2_E_const hR ct, one_mul]
    _ ≤ _ := by linarith

/-- The neighbour profile estimate at one vertex `i ∈ S`:
`E|X⁺_ii/2 - 1| ≤ C_S√h y_i/2 + (y_i/2)(3√ρ + (v + 2δ_i/v)/2) + |y_i - 2|/2`. -/
theorem l2_E2i (hR : TRegime d p) {h : ℝ} (hh : 0 < h) (ct : Contact.{u} d p) {i : ct.V}
    (hi : i ∈ ct.S) {CS v : ℝ} (hv : 0 < v)
    (hS1 : ct.E (fun σ => ct.gp σ i i - ct.XP h σ i i) ≤ CS * Real.sqrt h * ct.yp i) :
    ct.E (fun σ => |ct.XP h σ i i / 2 - 1|) ≤
      CS * Real.sqrt h * ct.yp i / 2 + ct.yp i / 2 * (3 * Real.sqrt (epsP d p / p + epsP d p ^ 2) +
        (v + 2 * ct.delta i / v) / 2) + |ct.yp i - 2| / 2 := by
  change _ ≤ CS * Real.sqrt h * ct.yp i / 2 + ct.yp i / 2 *
    (3 * Real.sqrt (epsP d p / p + epsP d p ^ 2) + (v + 2 * (rOf d p - ct.mp i) / v) / 2) +
      |ct.yp i - 2| / 2
  have hρ : 0 ≤ epsP d p / p + epsP d p ^ 2 := by
    have := hR.pfA_epsP_nonneg; have := hR.pfA_p_pos; positivity
  have hyp : ∀ k, 0 ≤ ct.yp k := fun k => (l2_y_le_two hR ct k).1.1
  have hy2 := (l2_y_le_two hR ct i).1.2
  have hδ : 0 ≤ rOf d p - ct.mp i := by
    have := (ct.ctx.cap ct.yp ct.ym ct.ctx.hyp ct.ctx.hym i hi).1
    unfold Contact.mp; linarith
  have hvar := l2_var_bound hR ct hi
  have h1 : ct.E (fun σ => |hN ct.G (aOf d p) 1 ct.yp σ ct.S i - 1|) ≤
      3 * Real.sqrt (epsP d p / p + epsP d p ^ 2) + (v + 2 * (rOf d p - ct.mp i) / v) / 2 := by
    refine (l2_E_abs_le hR ct _).trans ((Real.sqrt_le_sqrt hvar).trans ?_)
    refine (l2_sqrt_add_le (by positivity) (by positivity)).trans (add_le_add ?_ ?_)
    · calc Real.sqrt (8 * (epsP d p / p + epsP d p ^ 2))
          ≤ Real.sqrt (9 * (epsP d p / p + epsP d p ^ 2)) := Real.sqrt_le_sqrt (by linarith)
        _ = 3 * Real.sqrt (epsP d p / p + epsP d p ^ 2) := by
            rw [Real.sqrt_mul (by norm_num), show (9 : ℝ) = 3 ^ 2 by norm_num,
              Real.sqrt_sq (by norm_num)]
    · exact l2_sqrt_le_amgm (by positivity) hv
  have hpt : ∀ σ, wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 →
      |ct.XP h σ i i / 2 - 1| ≤ 1 / 2 * (ct.gp σ i i - ct.XP h σ i i) +
        (ct.yp i / 2 * |hN ct.G (aOf d p) 1 ct.yp σ ct.S i - 1| + |ct.yp i - 2| / 2) := by
    intro σ hσ
    obtain ⟨hpP, -⟩ := SecB.posDef_of_wt_ne_zero ct.G hσ
    have hX0 : 0 ≤ ct.XP h σ i i := (SecB.diag_nonneg_of_posDef ct.G hpP hyp hh.le i).2
    have hXG : ct.XP h σ i i ≤ ct.gp σ i i := by
      change shiftP ct.G (aOf d p) 1 h ct.yp σ ct.S i i ≤
        greenP ct.G (aOf d p) 1 ct.yp σ ct.S i i
      rw [SecB.shiftP_diag ct.G σ ct.S (hyp i), SecB.greenP_diag ct.G σ ct.S (hyp i)]
      exact mul_le_mul_of_nonneg_left (SecB.hzN_le_hN ct.G hpP hh.le hyp i) (hyp i)
    have e : ct.gp σ i i = ct.yp i * hN ct.G (aOf d p) 1 ct.yp σ ct.S i :=
      SecB.greenP_diag ct.G σ ct.S (hyp i)
    have a1 : |ct.XP h σ i i / 2 - 1| ≤
        (ct.gp σ i i - ct.XP h σ i i) / 2 + |ct.gp σ i i / 2 - 1| := by
      have := abs_sub_le (ct.XP h σ i i / 2) (ct.gp σ i i / 2) 1
      rw [abs_of_nonpos (by linarith : ct.XP h σ i i / 2 - ct.gp σ i i / 2 ≤ 0)] at this
      linarith
    have a2 : |ct.gp σ i i / 2 - 1| ≤
        ct.yp i / 2 * |hN ct.G (aOf d p) 1 ct.yp σ ct.S i - 1| + |ct.yp i - 2| / 2 := by
      rw [e, show ct.yp i * hN ct.G (aOf d p) 1 ct.yp σ ct.S i / 2 - 1 =
        ct.yp i / 2 * (hN ct.G (aOf d p) 1 ct.yp σ ct.S i - 1) + (ct.yp i - 2) / 2 by ring]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_of_nonneg (by linarith [hyp i] : 0 ≤ ct.yp i / 2), abs_div, abs_two]
    linarith
  calc ct.E (fun σ => |ct.XP h σ i i / 2 - 1|)
      ≤ ct.E (fun σ => 1 / 2 * (ct.gp σ i i - ct.XP h σ i i) +
          (ct.yp i / 2 * |hN ct.G (aOf d p) 1 ct.yp σ ct.S i - 1| + |ct.yp i - 2| / 2)) :=
        l2_E_mono ct hpt
    _ = 1 / 2 * ct.E (fun σ => ct.gp σ i i - ct.XP h σ i i) +
          (ct.yp i / 2 * ct.E (fun σ => |hN ct.G (aOf d p) 1 ct.yp σ ct.S i - 1|) +
            |ct.yp i - 2| / 2) := by
        rw [l2_E_add, l2_E_const_mul, l2_E_add, l2_E_const_mul, l2_E_const hR ct]
    _ ≤ _ := by
        have := mul_le_mul_of_nonneg_left h1 (by linarith [hyp i] : (0 : ℝ) ≤ ct.yp i / 2)
        linarith

/-- The minus-branch triple product: for `i, k ∈ S`,
`E[(G⁻_vv/2)² (X⁻_ii/2)² (X⁻_kk/2)²] ≤ 1 + 24ε` (AM–GM and (F2) with `k = 6`). -/
theorem l2_E3 (hR : TRegime d p) {h : ℝ} (hh : 0 < h) (ct : Contact.{u} d p) {i k : ct.V}
    (hi : i ∈ ct.S) (hk : k ∈ ct.S) :
    ct.E (fun σ => (ct.gm σ ct.v ct.v / 2) ^ 2 * (ct.XM h σ i i / 2) ^ 2 *
      (ct.XM h σ k k / 2) ^ 2) ≤ 1 + 24 * epsP d p := by
  have hym : ∀ j, 0 ≤ ct.ym j := fun j => (l2_y_le_two hR ct j).2.1
  have hF6 : ∀ j ∈ ct.S, ct.E (fun σ => hN ct.G (aOf d p) (-1) ct.ym σ ct.S j ^ 6) ≤
      1 + 24 * epsP d p := by
    intro j hj
    have h6 := (source_moments ct.G hR ct.ctx.toCapCtx ct.ctx.hyp ct.ctx.hym hj (k := 6)
      (by norm_num) (by have := hR.hp; omega)).2
    push_cast at h6
    have hB := l2_B6_real (P := p) (r := rOf d p) (by have := hR.pfA_p_ge; linarith)
      hR.one_lt_rOf.le hR.rOf_le
    unfold epsP
    exact h6.trans hB
  have hpt : ∀ σ, wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 →
      (ct.gm σ ct.v ct.v / 2) ^ 2 * (ct.XM h σ i i / 2) ^ 2 * (ct.XM h σ k k / 2) ^ 2 ≤
        1 / 3 * (hN ct.G (aOf d p) (-1) ct.ym σ ct.S ct.v ^ 6 +
          hN ct.G (aOf d p) (-1) ct.ym σ ct.S i ^ 6 +
          hN ct.G (aOf d p) (-1) ct.ym σ ct.S k ^ 6) := by
    intro σ hσ
    obtain ⟨-, hpM⟩ := SecB.posDef_of_wt_ne_zero ct.G hσ
    have h0 : ∀ j, 0 ≤ hN ct.G (aOf d p) (-1) ct.ym σ ct.S j :=
      fun j => hpM.inv.posSemidef.diag_nonneg
    have hG : ∀ j, ct.gm σ j j = ct.ym j * hN ct.G (aOf d p) (-1) ct.ym σ ct.S j :=
      fun j => SecB.greenP_diag ct.G σ ct.S (hym j)
    have hb : ∀ j, 0 ≤ ct.XM h σ j j / 2 ∧
        ct.XM h σ j j / 2 ≤ hN ct.G (aOf d p) (-1) ct.ym σ ct.S j := by
      intro j
      have hX0 : 0 ≤ ct.XM h σ j j := (SecB.diag_nonneg_of_posDef ct.G hpM hym hh.le j).2
      have hXG : ct.XM h σ j j ≤ ct.gm σ j j := by
        change shiftP ct.G (aOf d p) (-1) h ct.ym σ ct.S j j ≤
          greenP ct.G (aOf d p) (-1) ct.ym σ ct.S j j
        rw [SecB.shiftP_diag ct.G σ ct.S (hym j), SecB.greenP_diag ct.G σ ct.S (hym j)]
        exact mul_le_mul_of_nonneg_left (SecB.hzN_le_hN ct.G hpM hh.le hym j) (hym j)
      have hy2 := (l2_y_le_two hR ct j).2.2
      rw [hG] at hXG
      refine ⟨by linarith, ?_⟩
      nlinarith [h0 j]
    have hbv : 0 ≤ ct.gm σ ct.v ct.v / 2 ∧
        ct.gm σ ct.v ct.v / 2 ≤ hN ct.G (aOf d p) (-1) ct.ym σ ct.S ct.v := by
      rw [hG]
      have hy2 := (l2_y_le_two hR ct ct.v).2.2
      have := h0 ct.v
      constructor
      · have := hym ct.v; positivity
      · nlinarith
    have a1 := pow_le_pow_left₀ hbv.1 hbv.2 2
    have a2 := pow_le_pow_left₀ (hb i).1 (hb i).2 2
    have a3 := pow_le_pow_left₀ (hb k).1 (hb k).2 2
    have am := l2_amgm3 (sq_nonneg (hN ct.G (aOf d p) (-1) ct.ym σ ct.S ct.v))
      (sq_nonneg (hN ct.G (aOf d p) (-1) ct.ym σ ct.S i))
      (sq_nonneg (hN ct.G (aOf d p) (-1) ct.ym σ ct.S k))
    calc (ct.gm σ ct.v ct.v / 2) ^ 2 * (ct.XM h σ i i / 2) ^ 2 * (ct.XM h σ k k / 2) ^ 2
        ≤ hN ct.G (aOf d p) (-1) ct.ym σ ct.S ct.v ^ 2 *
            hN ct.G (aOf d p) (-1) ct.ym σ ct.S i ^ 2 *
            hN ct.G (aOf d p) (-1) ct.ym σ ct.S k ^ 2 :=
          mul_le_mul (mul_le_mul a1 a2 (sq_nonneg _) (sq_nonneg _)) a3 (sq_nonneg _)
            (by positivity)
      _ ≤ _ := by
          refine am.trans (le_of_eq ?_)
          ring
  calc _ ≤ ct.E (fun σ => 1 / 3 * (hN ct.G (aOf d p) (-1) ct.ym σ ct.S ct.v ^ 6 +
          hN ct.G (aOf d p) (-1) ct.ym σ ct.S i ^ 6 +
          hN ct.G (aOf d p) (-1) ct.ym σ ct.S k ^ 6)) := l2_E_mono ct hpt
    _ = 1 / 3 * (ct.E (fun σ => hN ct.G (aOf d p) (-1) ct.ym σ ct.S ct.v ^ 6) +
          ct.E (fun σ => hN ct.G (aOf d p) (-1) ct.ym σ ct.S i ^ 6) +
          ct.E (fun σ => hN ct.G (aOf d p) (-1) ct.ym σ ct.S k ^ 6)) := by
        rw [l2_E_const_mul, l2_E_add, l2_E_add]
    _ ≤ 1 / 3 * ((1 + 24 * epsP d p) + (1 + 24 * epsP d p) + (1 + 24 * epsP d p)) := by
        gcongr
        · exact hF6 _ ct.ctx.mem
        · exact hF6 _ hi
        · exact hF6 _ hk
    _ = 1 + 24 * epsP d p := by ring

/-- `|N_S(w)| ≤ d`. -/
theorem l2_card_nbhd (ct : Contact.{u} d p) (w : ct.V) : ((nbhd ct.G ct.S w).card : ℝ) ≤ d := by
  have h1 : nbhd ct.G ct.S w ⊆ ct.G.neighborFinset w := fun i hi => by
    simp only [nbhd, Finset.mem_filter] at hi
    simpa using hi.2
  have h2 := Finset.card_le_card h1
  rw [SimpleGraph.card_neighborFinset_eq_degree] at h2
  exact_mod_cast h2.trans (ct.ctx.deg w)

/-- The mask weights `w_ik = u_i u_k (A_H)_ik`: nonnegative, symmetric, supported on `N × N`,
with row sums at most `1_N`. -/
theorem l2_weights (ct : Contact.{u} d p) (hd : 0 < (d : ℝ)) :
    (∀ i k, 0 ≤ ct.uvec i * ct.uvec k * ct.adjS i k) ∧
    (∀ i k, ct.uvec i * ct.uvec k * ct.adjS i k = ct.uvec k * ct.uvec i * ct.adjS k i) ∧
    (∀ i k, ct.uvec i * ct.uvec k * ct.adjS i k ≠ 0 → i ∈ ct.N ∧ k ∈ ct.N) ∧
    (∀ i, ∑ k, ct.uvec i * ct.uvec k * ct.adjS i k ≤ if i ∈ ct.N then 1 else 0) := by
  have hu0 : ∀ i, 0 ≤ ct.uvec i := fun i => by
    unfold Contact.uvec; split_ifs <;> positivity
  have hu1 : ∀ i, ct.uvec i ≤ 1 / Real.sqrt d := fun i => by
    unfold Contact.uvec; split_ifs <;> [exact le_rfl; positivity]
  have hA0 : ∀ i k, 0 ≤ ct.adjS i k := fun i k => by
    simp only [Contact.adjS, Matrix.of_apply]; split_ifs <;> norm_num
  have hAsym : ∀ i k, ct.adjS i k = ct.adjS k i := fun i k => by
    simp only [Contact.adjS, Matrix.of_apply]
    split_ifs with h1 h2 h2 <;> first | rfl | exact absurd ⟨h1.2.1, h1.1, h1.2.2.symm⟩ h2 |
      exact absurd ⟨h2.2.1, h2.1, h2.2.2.symm⟩ h1
  refine ⟨fun i k => mul_nonneg (mul_nonneg (hu0 i) (hu0 k)) (hA0 i k), fun i k => by
    rw [hAsym, mul_comm (ct.uvec i)], fun i k hne => ?_, fun i => ?_⟩
  · constructor
    · by_contra hc
      apply hne
      simp [Contact.uvec, hc]
    · by_contra hc
      apply hne
      simp [Contact.uvec, hc]
  · by_cases hi : i ∈ ct.N
    · simp only [hi, ↓reduceIte]
      have hsum : ∑ k, ct.adjS i k ≤ d := by
        calc ∑ k, ct.adjS i k ≤ ∑ k, (if k ∈ nbhd ct.G ct.S i then (1 : ℝ) else 0) := by
              refine Finset.sum_le_sum fun k _ => ?_
              simp only [Contact.adjS, Matrix.of_apply]
              split_ifs with h1 h2 <;> norm_num
              exact h2 (by simp [nbhd, h1.2.1, h1.2.2])
          _ = (nbhd ct.G ct.S i).card := by rw [Finset.sum_boole]; simp
          _ ≤ d := l2_card_nbhd ct i
      have hsd : Real.sqrt d * Real.sqrt d = d := Real.mul_self_sqrt hd.le
      have hsq : 0 < Real.sqrt d := Real.sqrt_pos.2 hd
      calc ∑ k, ct.uvec i * ct.uvec k * ct.adjS i k
          ≤ ∑ k, 1 / Real.sqrt d * (1 / Real.sqrt d) * ct.adjS i k :=
            Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right
              (mul_le_mul (hu1 i) (hu1 k) (hu0 k) (by positivity)) (hA0 i k)
        _ = 1 / d * ∑ k, ct.adjS i k := by
            rw [← Finset.mul_sum, div_mul_div_comm, one_mul, hsd]
        _ ≤ 1 / d * d := mul_le_mul_of_nonneg_left hsum (by positivity)
        _ = 1 := by field_simp
    · simp only [hi, ↓reduceIte]
      refine le_of_eq (Finset.sum_eq_zero fun k _ => ?_)
      simp [Contact.uvec, hi]

/-- `D_*` dominates every physical diagonal on the radius-two ball. -/
theorem l2_diag_le_dstar (ct : Contact.{u} d p) (σ : Config ct.V) {w : ct.V}
    (hw : w ∈ insert ct.v (ct.N ∪ ct.N.biUnion (nbhd ct.G ct.S))) :
    ct.gp σ w w ≤ ct.Dstar σ - 1 ∧ ct.gm σ w w ≤ ct.Dstar σ - 1 := by
  have h := (insert ct.v (ct.N ∪ ct.N.biUnion (nbhd ct.G ct.S))).le_sup'
    (fun w => max (ct.gp σ w w) (ct.gm σ w w)) hw
  unfold Contact.Dstar
  constructor
  · linarith [le_max_left (ct.gp σ w w) (ct.gm σ w w)]
  · linarith [le_max_right (ct.gp σ w w) (ct.gm σ w w)]

/-- Row bounds on the support at a neighbour `i ∈ N`: `x_i², z_i² ≤ D_*²`, `0 ≤ P_i, Q_i ≤ D_*²`. -/
theorem l2_row_bounds (hR : TRegime d p) (ct : Contact.{u} d p) {σ : Config ct.V}
    (hσ : wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0) {i : ct.V} (hi : i ∈ ct.N) :
    1 ≤ ct.Dstar σ ∧ ct.x σ i ^ 2 ≤ ct.Dstar σ ^ 2 ∧ ct.z σ i ^ 2 ≤ ct.Dstar σ ^ 2 ∧
      0 ≤ ct.gp σ ct.v ct.v * ct.gp σ i i ∧ ct.gp σ ct.v ct.v * ct.gp σ i i ≤ ct.Dstar σ ^ 2 ∧
      0 ≤ ct.gm σ ct.v ct.v * ct.gm σ i i ∧ ct.gm σ ct.v ct.v * ct.gm σ i i ≤ ct.Dstar σ ^ 2 := by
  obtain ⟨hpP, hpM⟩ := SecB.posDef_of_wt_ne_zero ct.G hσ
  have hyp : ∀ k, 0 ≤ ct.yp k := fun k => (l2_y_le_two hR ct k).1.1
  have hym : ∀ k, 0 ≤ ct.ym k := fun k => (l2_y_le_two hR ct k).2.1
  have hv := l2_diag_le_dstar ct σ (Finset.mem_insert_self ct.v _)
  have hi' := l2_diag_le_dstar ct σ (Finset.mem_insert_of_mem (Finset.mem_union_left _ hi))
  have gPv : 0 ≤ ct.gp σ ct.v ct.v := (SecB.diag_nonneg_of_posDef ct.G hpP hyp le_rfl ct.v).1
  have gPi : 0 ≤ ct.gp σ i i := (SecB.diag_nonneg_of_posDef ct.G hpP hyp le_rfl i).1
  have gMv : 0 ≤ ct.gm σ ct.v ct.v := (SecB.diag_nonneg_of_posDef ct.G hpM hym le_rfl ct.v).1
  have gMi : 0 ≤ ct.gm σ i i := (SecB.diag_nonneg_of_posDef ct.G hpM hym le_rfl i).1
  have hx : ct.x σ i ^ 2 ≤ ct.gp σ ct.v ct.v * ct.gp σ i i := l2_green_sq_le ct.G hpP hyp ct.v i
  have hz : ct.z σ i ^ 2 ≤ ct.gm σ ct.v ct.v * ct.gm σ i i := l2_green_sq_le ct.G hpM hym ct.v i
  have hD1 : 1 ≤ ct.Dstar σ := by linarith [hv.1]
  have hP : ct.gp σ ct.v ct.v * ct.gp σ i i ≤ ct.Dstar σ ^ 2 := by
    have := mul_le_mul hv.1 hi'.1 gPi (by linarith)
    nlinarith
  have hQ : ct.gm σ ct.v ct.v * ct.gm σ i i ≤ ct.Dstar σ ^ 2 := by
    have := mul_le_mul hv.2 hi'.2 gMi (by linarith)
    nlinarith
  exact ⟨hD1, hx.trans hP, hz.trans hQ, mul_nonneg gPv gPi, hP, mul_nonneg gMv gMi, hQ⟩

/-- Weighted row sums of the mask weights. -/
theorem l2_wsum (ct : Contact.{u} d p) (hd : 0 < (d : ℝ)) (g : ct.V → ℝ) (hg : ∀ i, 0 ≤ g i) :
    ∑ i, ∑ k, ct.uvec i * ct.uvec k * ct.adjS i k * g i ≤ ∑ i ∈ ct.N, g i := by
  obtain ⟨-, -, -, hrow⟩ := l2_weights ct hd
  calc ∑ i, ∑ k, ct.uvec i * ct.uvec k * ct.adjS i k * g i
      = ∑ i, g i * ∑ k, ct.uvec i * ct.uvec k * ct.adjS i k := by
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
    _ ≤ ∑ i, g i * (if i ∈ ct.N then 1 else 0) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hrow i) (hg i)
    _ = ∑ i ∈ ct.N, g i := by
        simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_mem, Finset.univ_inter]

theorem l2_wsum' (ct : Contact.{u} d p) (hd : 0 < (d : ℝ)) (g : ct.V → ℝ) (hg : ∀ i, 0 ≤ g i) :
    ∑ i, ∑ k, ct.uvec i * ct.uvec k * ct.adjS i k * g k ≤ ∑ i ∈ ct.N, g i := by
  obtain ⟨-, hsym, -, -⟩ := l2_weights ct hd
  calc ∑ i, ∑ k, ct.uvec i * ct.uvec k * ct.adjS i k * g k
      = ∑ k, ∑ i, ct.uvec k * ct.uvec i * ct.adjS k i * g k := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by rw [hsym]
    _ ≤ ∑ i ∈ ct.N, g i := l2_wsum ct hd g hg

theorem l2_wsum1 (ct : Contact.{u} d p) (hd : 0 < (d : ℝ)) :
    ∑ i, ∑ k, ct.uvec i * ct.uvec k * ct.adjS i k ≤ d := by
  have h := l2_wsum ct hd (fun _ => 1) (fun _ => zero_le_one)
  simp only [mul_one, Finset.sum_const, nsmul_eq_mul] at h
  exact h.trans (l2_card_nbhd ct ct.v)

/-- The core of (RC2): the termwise inequality `cdab·cdab ≤ ((ca²)² + (db²)²)/2`, the lower bound
`(c a_i a_k)² ≥ 1 - 2(|c-1| + |a_i-1| + |a_k-1|)` and the mask weights give
`β - α ≤ 2a²(d(24ε + 2E|c-1|) + 4 Σ_N E|a_i - 1|)`, with `c = G⁺_vv/2`, `a_i = X⁺_ii/2`. -/
theorem l2_rc2_core (hR : TRegime d p) {h : ℝ} (hh : 0 < h) (ct : Contact.{u} d p) :
    ct.betaE h - ct.alphaE h ≤ 2 * aOf d p ^ 2 * ((d : ℝ) * (24 * epsP d p +
      2 * ct.E (fun σ => |ct.gp σ ct.v ct.v / 2 - 1|)) +
      4 * ∑ i ∈ ct.N, ct.E (fun σ => |ct.XP h σ i i / 2 - 1|)) := by
  have hd0 : (0 : ℝ) < d := hR.pfA_d_pos
  have hyp : ∀ k, 0 ≤ ct.yp k := fun k => (l2_y_le_two hR ct k).1.1
  obtain ⟨hw0, -, hwN, -⟩ := l2_weights ct hd0
  set a := aOf d p with ha
  set G : ct.V → ct.V → Config ct.V → ℝ := fun i k σ =>
    (ct.gm σ ct.v ct.v / 2) ^ 2 * (ct.XM h σ i i / 2) ^ 2 * (ct.XM h σ k k / 2) ^ 2 - 1 +
      2 * (|ct.gp σ ct.v ct.v / 2 - 1| + |ct.XP h σ i i / 2 - 1| + |ct.XP h σ k k / 2 - 1|)
    with hG
  set e : ct.V → ℝ := fun i => ct.E (fun σ => |ct.XP h σ i i / 2 - 1|) with he
  set E1 := ct.E (fun σ => |ct.gp σ ct.v ct.v / 2 - 1|) with hE1
  have he0 : ∀ i, 0 ≤ e i := fun i => lawE_nonneg ct.G fun σ _ => abs_nonneg _
  have hE10 : 0 ≤ E1 := lawE_nonneg ct.G fun σ _ => abs_nonneg _
  have hε := hR.pfA_epsP_nonneg
  -- the two quadratic forms
  have hFα : ∀ σ, ct.OmP σ * (ct.uvec ⬝ᵥ (ct.MP h σ *ᵥ ct.bP h σ)) =
      (ct.gp σ ct.v ct.v / 2) ^ 2 * (4 * a ^ 2 * ∑ i, ∑ k, ct.uvec i * ct.uvec k * ct.adjS i k *
        ((ct.XP h σ i i / 2) ^ 2 * (ct.XP h σ k k / 2) ^ 2)) := by
    intro σ
    simp only [Contact.OmP, Contact.bP, Contact.MP]
    rw [l2_quad]
  have hFβ : ∀ σ, ct.OmM σ * (ct.uvec ⬝ᵥ (ct.MM h σ *ᵥ ct.bM h σ)) =
      ct.gp σ ct.v ct.v * ct.gm σ ct.v ct.v / 4 * (4 * a ^ 2 * ∑ i, ∑ k, ct.uvec i * ct.uvec k *
        ct.adjS i k * ((ct.XP h σ i i / 2 * (ct.XM h σ i i / 2)) *
          (ct.XP h σ k k / 2 * (ct.XM h σ k k / 2)))) := by
    intro σ
    simp only [Contact.OmM, Contact.bM, Contact.MM]
    rw [l2_quad]
  -- pointwise
  have hA : ∀ σ, wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 →
      ct.OmM σ * (ct.uvec ⬝ᵥ (ct.MM h σ *ᵥ ct.bM h σ)) -
        ct.OmP σ * (ct.uvec ⬝ᵥ (ct.MP h σ *ᵥ ct.bP h σ)) ≤
      2 * a ^ 2 * ∑ i, ∑ k, ct.uvec i * ct.uvec k * ct.adjS i k * G i k σ := by
    intro σ hσ
    obtain ⟨hpP, -⟩ := SecB.posDef_of_wt_ne_zero ct.G hσ
    have hc : 0 ≤ ct.gp σ ct.v ct.v / 2 := by
      have := (SecB.diag_nonneg_of_posDef ct.G hpP hyp le_rfl ct.v).1
      exact div_nonneg this zero_le_two
    have hai : ∀ j, 0 ≤ ct.XP h σ j j / 2 := fun j => by
      have : 0 ≤ ct.XP h σ j j := (SecB.diag_nonneg_of_posDef ct.G hpP hyp hh.le j).2
      exact div_nonneg this zero_le_two
    have key : ∀ i k, 2 * (ct.gp σ ct.v ct.v * ct.gm σ ct.v ct.v / 4 *
        ((ct.XP h σ i i / 2 * (ct.XM h σ i i / 2)) * (ct.XP h σ k k / 2 * (ct.XM h σ k k / 2))) -
        (ct.gp σ ct.v ct.v / 2) ^ 2 * ((ct.XP h σ i i / 2) ^ 2 * (ct.XP h σ k k / 2) ^ 2)) ≤
        G i k σ := by
      intro i k
      have := l2_rc2_term (dv := ct.gm σ ct.v ct.v / 2) (bi := ct.XM h σ i i / 2)
        (bk := ct.XM h σ k k / 2) hc (hai i) (hai k)
      calc _ = 2 * (ct.gp σ ct.v ct.v / 2 * (ct.gm σ ct.v ct.v / 2) *
            (ct.XP h σ i i / 2 * (ct.XM h σ i i / 2) * (ct.XP h σ k k / 2 * (ct.XM h σ k k / 2))) -
            (ct.gp σ ct.v ct.v / 2) ^ 2 * ((ct.XP h σ i i / 2) ^ 2 * (ct.XP h σ k k / 2) ^ 2)) := by
            ring
        _ ≤ G i k σ := this
    rw [hFα, hFβ]
    calc ct.gp σ ct.v ct.v * ct.gm σ ct.v ct.v / 4 * (4 * a ^ 2 * ∑ i, ∑ k,
          ct.uvec i * ct.uvec k * ct.adjS i k * ((ct.XP h σ i i / 2 * (ct.XM h σ i i / 2)) *
            (ct.XP h σ k k / 2 * (ct.XM h σ k k / 2)))) -
        (ct.gp σ ct.v ct.v / 2) ^ 2 * (4 * a ^ 2 * ∑ i, ∑ k, ct.uvec i * ct.uvec k *
          ct.adjS i k * ((ct.XP h σ i i / 2) ^ 2 * (ct.XP h σ k k / 2) ^ 2))
        = ∑ i, ∑ k, 2 * a ^ 2 * (ct.uvec i * ct.uvec k * ct.adjS i k *
            (2 * (ct.gp σ ct.v ct.v * ct.gm σ ct.v ct.v / 4 *
              ((ct.XP h σ i i / 2 * (ct.XM h σ i i / 2)) *
                (ct.XP h σ k k / 2 * (ct.XM h σ k k / 2))) -
              (ct.gp σ ct.v ct.v / 2) ^ 2 * ((ct.XP h σ i i / 2) ^ 2 *
                (ct.XP h σ k k / 2) ^ 2)))) := by
          simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
      _ ≤ ∑ i, ∑ k, 2 * a ^ 2 * (ct.uvec i * ct.uvec k * ct.adjS i k * G i k σ) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ =>
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (key i k) (hw0 i k))
              (by positivity)
      _ = 2 * a ^ 2 * ∑ i, ∑ k, ct.uvec i * ct.uvec k * ct.adjS i k * G i k σ := by
          simp only [Finset.mul_sum]
  -- expectation
  have hB : ct.betaE h - ct.alphaE h ≤
      2 * a ^ 2 * ∑ i, ∑ k, ct.uvec i * ct.uvec k * ct.adjS i k * ct.E (G i k) := by
    unfold Contact.betaE Contact.alphaE
    rw [← l2_E_sub]
    refine (l2_E_mono ct hA).trans (le_of_eq ?_)
    rw [l2_E_const_mul, l2_E_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [l2_E_sum]
    exact Finset.sum_congr rfl fun k _ => l2_E_const_mul ct _ _
  -- each `E G_ik`
  have hGik : ∀ i ∈ ct.S, ∀ k ∈ ct.S,
      ct.E (G i k) ≤ 24 * epsP d p + 2 * E1 + 2 * e i + 2 * e k := by
    intro i hi k hk
    have h3 := l2_E3 hR hh ct hi hk
    have e1 : ct.E (G i k) = ct.E (fun σ => (ct.gm σ ct.v ct.v / 2) ^ 2 * (ct.XM h σ i i / 2) ^ 2 *
        (ct.XM h σ k k / 2) ^ 2) - 1 + 2 * (E1 + e i + e k) := by
      simp only [hG]
      rw [l2_E_add, l2_E_sub, l2_E_const hR ct, l2_E_const_mul, l2_E_add, l2_E_add]
    rw [e1]; linarith
  -- weights
  have hW : ∑ i, ∑ k, ct.uvec i * ct.uvec k * ct.adjS i k * ct.E (G i k) ≤
      ∑ i, ∑ k, ct.uvec i * ct.uvec k * ct.adjS i k *
        ((24 * epsP d p + 2 * E1) + 2 * e i + 2 * e k) := by
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ => ?_
    by_cases hz : ct.uvec i * ct.uvec k * ct.adjS i k = 0
    · rw [hz, zero_mul, zero_mul]
    · obtain ⟨hi, hk⟩ := hwN i k hz
      have := hGik i (ct.mem_S_of_mem_N hi) k (ct.mem_S_of_mem_N hk)
      exact mul_le_mul_of_nonneg_left (by linarith) (hw0 i k)
  have hsplit : ∑ i, ∑ k, ct.uvec i * ct.uvec k * ct.adjS i k *
      ((24 * epsP d p + 2 * E1) + 2 * e i + 2 * e k) =
      (24 * epsP d p + 2 * E1) * ∑ i, ∑ k, ct.uvec i * ct.uvec k * ct.adjS i k +
      2 * ∑ i, ∑ k, ct.uvec i * ct.uvec k * ct.adjS i k * e i +
      2 * ∑ i, ∑ k, ct.uvec i * ct.uvec k * ct.adjS i k * e k := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
  have w1 := l2_wsum1 ct hd0
  have w2 := l2_wsum ct hd0 e he0
  have w3 := l2_wsum' ct hd0 e he0
  have hA0 : 0 ≤ 24 * epsP d p + 2 * E1 := by positivity
  have hfin : ∑ i, ∑ k, ct.uvec i * ct.uvec k * ct.adjS i k * ct.E (G i k) ≤
      (d : ℝ) * (24 * epsP d p + 2 * E1) + 4 * ∑ i ∈ ct.N, e i := by
    rw [hsplit] at hW
    have := mul_le_mul_of_nonneg_left w1 hA0
    linarith
  calc ct.betaE h - ct.alphaE h ≤ _ := hB
    _ ≤ 2 * a ^ 2 * ((d : ℝ) * (24 * epsP d p + 2 * E1) + 4 * ∑ i ∈ ct.N, e i) :=
        mul_le_mul_of_nonneg_left hfin (by positivity)

/-- (D13) at one contact, given the UMI bound for `D_*²`-weights, `S ≤ C₇ p` and
`a² S₋ ≤ C₂ δ̄`. -/
theorem l2_d13_core (hR : TRegime d p) (ct : Contact.{u} d p) {CU C₇ C₂ : ℝ} (hCU : 0 ≤ CU)
    (hC₇ : 0 ≤ C₇) (hC₂ : 0 ≤ C₂)
    (HU : ∀ Y Z : Config ct.V → ℝ,
      (∀ σ, wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 → 0 ≤ Y σ ∧ Y σ ≤ ct.Dstar σ ^ 2) →
      (∀ σ, wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 → 0 ≤ Z σ ∧ Z σ ≤ ct.Dstar σ ^ 2) →
      ct.E (fun σ => Y σ * Z σ) ≤ CU * (ct.E Y + 1 / (d : ℝ)))
    (hS : ct.Srow ≤ C₇ * p) (hSm : aOf d p ^ 2 * ct.Smin ≤ C₂ * dbar d p) :
    ct.Qstar ≤ aOf d p ^ 2 * (2 * LdP d p * (((p : ℝ) - 1) * ct.tP0 + p * ct.tM0) +
      50 * CU * (C₇ + C₂ + 1) * (p : ℝ) ^ 3 * Real.sqrt ((p : ℝ) * dbar d p / d)) := by
  have hd0 : (0 : ℝ) < d := hR.pfA_d_pos
  have hp1 : (1 : ℝ) ≤ p := hR.pfA_one_le_p
  have hδ1 : 1 / (d : ℝ) ≤ dbar d p := by
    have := hR.pfA_epsP_nonneg; have := pfA_cbrt_nonneg d p
    have : 1 / (d : ℝ) ≤ (p : ℝ) ^ 4 / d :=
      div_le_div_of_nonneg_right (one_le_pow₀ hp1) hd0.le
    unfold dbar; linarith
  have hδq : (p : ℝ) / d ≤ dbar d p := by
    have := hR.pfA_epsP_nonneg; have := pfA_cbrt_nonneg d p
    have : (p : ℝ) / d ≤ (p : ℝ) ^ 4 / d :=
      div_le_div_of_nonneg_right (le_self_pow₀ hp1 (by norm_num)) hd0.le
    unfold dbar; linarith
  have hδ0 : 0 < dbar d p := lt_of_lt_of_le (by positivity) hδ1
  set t : ℝ := (d : ℝ) * Real.sqrt ((p : ℝ) * dbar d p / d) / p with ht
  have ht0 : 0 < t := by
    have : 0 < Real.sqrt ((p : ℝ) * dbar d p / d) := Real.sqrt_pos.2 (by positivity)
    positivity
  set K : ct.V → Config ct.V → ℝ := fun i σ => Kpoly p (ct.x σ i) (ct.z σ i)
    (ct.gp σ ct.v ct.v * ct.gp σ i i) (ct.gm σ ct.v ct.v * ct.gm σ i i) with hKdef
  set K0 : ct.V → Config ct.V → ℝ := fun i σ =>
    6 * (((p : ℝ) - 1) * (ct.gp σ ct.v ct.v * ct.gp σ i i) ^ 2 +
      p * (ct.gp σ ct.v ct.v * ct.gp σ i i) * (ct.gm σ ct.v ct.v * ct.gm σ i i)) with hK0def
  -- per neighbour
  have hK : ∀ i ∈ ct.N, ct.E (K i) - ct.E (K0 i) ≤
      (92 + 28 * t) * (p : ℝ) ^ 3 * (CU * ((ct.E fun σ => ct.x σ i ^ 2) + 1 / (d : ℝ))) +
        28 / t * (p : ℝ) ^ 3 * (CU * ((ct.E fun σ => ct.z σ i ^ 2) + 1 / (d : ℝ))) := by
    intro i hi
    have hx : ct.E (fun σ => ct.x σ i ^ 2 * ct.Dstar σ ^ 2) ≤
        CU * ((ct.E fun σ => ct.x σ i ^ 2) + 1 / (d : ℝ)) :=
      HU (fun σ => ct.x σ i ^ 2) (fun σ => ct.Dstar σ ^ 2)
        (fun σ hσ => ⟨sq_nonneg _, (l2_row_bounds hR ct hσ hi).2.1⟩)
        (fun σ _ => ⟨sq_nonneg _, le_rfl⟩)
    have hz : ct.E (fun σ => ct.z σ i ^ 2 * ct.Dstar σ ^ 2) ≤
        CU * ((ct.E fun σ => ct.z σ i ^ 2) + 1 / (d : ℝ)) :=
      HU (fun σ => ct.z σ i ^ 2) (fun σ => ct.Dstar σ ^ 2)
        (fun σ hσ => ⟨sq_nonneg _, (l2_row_bounds hR ct hσ hi).2.2.1⟩)
        (fun σ _ => ⟨sq_nonneg _, le_rfl⟩)
    rw [← l2_E_sub]
    calc _ ≤ ct.E (fun σ => (92 + 28 * t) * (p : ℝ) ^ 3 * (ct.x σ i ^ 2 * ct.Dstar σ ^ 2) +
          28 / t * (p : ℝ) ^ 3 * (ct.z σ i ^ 2 * ct.Dstar σ ^ 2)) :=
        l2_E_mono ct fun σ hσ => by
          obtain ⟨hD1, hx2, hz2, hP0, hP, hQ0, hQ⟩ := l2_row_bounds hR ct hσ hi
          have h1 := l2_kpoly_le (p := p) hR.two_le_p hx2 hz2 hP0 hP hQ0 hQ
          have h2 := l2_amgm_t (x := ct.x σ i) (z := ct.z σ i) ht0
          have h3 : 0 ≤ (p : ℝ) ^ 3 * ct.Dstar σ ^ 2 := by positivity
          have h4 := mul_le_mul_of_nonneg_left h2 h3
          have e : (92 + 28 * t) * (p : ℝ) ^ 3 * (ct.x σ i ^ 2 * ct.Dstar σ ^ 2) +
              28 / t * (p : ℝ) ^ 3 * (ct.z σ i ^ 2 * ct.Dstar σ ^ 2) =
              92 * (p : ℝ) ^ 3 * ct.Dstar σ ^ 2 * ct.x σ i ^ 2 +
                28 * ((p : ℝ) ^ 3 * ct.Dstar σ ^ 2 * (t * ct.x σ i ^ 2 + ct.z σ i ^ 2 / t)) := by
            field_simp; ring
          simp only [hKdef, hK0def]
          rw [e]; linarith
      _ = (92 + 28 * t) * (p : ℝ) ^ 3 * ct.E (fun σ => ct.x σ i ^ 2 * ct.Dstar σ ^ 2) +
          28 / t * (p : ℝ) ^ 3 * ct.E (fun σ => ct.z σ i ^ 2 * ct.Dstar σ ^ 2) := by
        rw [l2_E_add, l2_E_const_mul, l2_E_const_mul]
      _ ≤ _ := by
        have c1 : 0 ≤ (92 + 28 * t) * (p : ℝ) ^ 3 := by positivity
        have c2 : 0 ≤ 28 / t * (p : ℝ) ^ 3 := by positivity
        exact add_le_add (mul_le_mul_of_nonneg_left hx c1) (mul_le_mul_of_nonneg_left hz c2)
  -- summed
  have hN : (ct.N.card : ℝ) * (1 / (d : ℝ)) ≤ 1 := by
    rw [← div_eq_mul_one_div, div_le_one hd0]
    exact l2_card_nbhd ct ct.v
  have hSm0 : 0 ≤ ct.Smin := Finset.sum_nonneg fun i _ => lawE_nonneg ct.G fun σ _ => sq_nonneg _
  have hX : ∑ i ∈ ct.N, (ct.E (K i) - ct.E (K0 i)) ≤
      (92 + 28 * t) * (p : ℝ) ^ 3 * (CU * (ct.Srow + 1)) +
        28 / t * (p : ℝ) ^ 3 * (CU * (ct.Smin + 1)) := by
    refine (Finset.sum_le_sum hK).trans ?_
    have e : ∑ i ∈ ct.N, ((92 + 28 * t) * (p : ℝ) ^ 3 *
          (CU * ((ct.E fun σ => ct.x σ i ^ 2) + 1 / (d : ℝ))) +
        28 / t * (p : ℝ) ^ 3 * (CU * ((ct.E fun σ => ct.z σ i ^ 2) + 1 / (d : ℝ)))) =
        (92 + 28 * t) * (p : ℝ) ^ 3 * (CU * (ct.Srow + ct.N.card * (1 / (d : ℝ)))) +
          28 / t * (p : ℝ) ^ 3 * (CU * (ct.Smin + ct.N.card * (1 / (d : ℝ)))) := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
      rfl
    rw [e]
    have c1 : 0 ≤ (92 + 28 * t) * (p : ℝ) ^ 3 * CU := by positivity
    have c2 : 0 ≤ 28 / t * (p : ℝ) ^ 3 * CU := by positivity
    have := mul_le_mul_of_nonneg_left hN c1
    have := mul_le_mul_of_nonneg_left hN c2
    nlinarith
  -- the row-free part
  have hK0 : aOf d p ^ 4 / 3 * ∑ i ∈ ct.N, ct.E (K0 i) =
      aOf d p ^ 2 * (2 * LdP d p * (((p : ℝ) - 1) * ct.tP0 + p * ct.tM0)) := by
    have hsum : ∑ i ∈ ct.N, ct.E (K0 i) = 6 * (((p : ℝ) - 1) *
        ct.E (fun σ => ct.gp σ ct.v ct.v ^ 2 * ∑ i ∈ ct.N, ct.gp σ i i ^ 2) +
        p * ct.E (fun σ => ct.gp σ ct.v ct.v * ct.gm σ ct.v ct.v *
          ∑ i ∈ ct.N, ct.gp σ i i * ct.gm σ i i)) := by
      rw [← l2_E_sum, ← l2_E_const_mul, ← l2_E_const_mul, ← l2_E_add, ← l2_E_const_mul]
      congr 1
      funext σ
      simp only [hK0def, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hsum]
    unfold LdP Contact.tP0 Contact.tM0
    field_simp
    ring
  have hQ : ct.Qstar = aOf d p ^ 4 / 3 * ∑ i ∈ ct.N, ct.E (K0 i) +
      aOf d p ^ 4 / 3 * ∑ i ∈ ct.N, (ct.E (K i) - ct.E (K0 i)) := by
    rw [← mul_add, ← Finset.sum_add_distrib]
    unfold Contact.Qstar
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  have hfin := l2_d13_real (A := aOf d p ^ 2) hd0 hp1 (sq_nonneg _) hR.pf_a_sq_le hδq hδ1 hS hSm
    hCU hC₇ hC₂ hX
  rw [hQ, hK0, show aOf d p ^ 4 = (aOf d p ^ 2) ^ 2 by ring]
  linarith

/-- Per-neighbour simplification of the profile estimate (`0 ≤ y ≤ 2`). -/
theorem l2_rc2_ei_real {e y δ cs sρ v : ℝ} (hv : 0 < v) (hy2 : y ≤ 2)
    (hc : 0 ≤ cs) (hsρ : 0 ≤ sρ)
    (h1 : e ≤ cs * y / 2 + y / 2 * (3 * sρ + (v + 2 * δ / v) / 2) + |y - 2| / 2) :
    e ≤ cs + 3 * sρ + v / 2 + y * δ / (2 * v) + |y - 2| / 2 := by
  have t1 : cs * y / 2 ≤ cs := by nlinarith
  have t2 : y / 2 * (3 * sρ + (v + 2 * δ / v) / 2) =
      y / 2 * (3 * sρ) + y * v / 4 + y * δ / (2 * v) := by
    field_simp; ring
  have t3 : y / 2 * (3 * sρ) ≤ 3 * sρ := by nlinarith
  have t4 : y * v / 4 ≤ v / 2 := by nlinarith
  linarith

/-- The summed neighbour profile estimate:
`Σ_N E|X⁺_ii/2 - 1| ≤ d(C_S√h + 3√ρ + v/2 + C₇v/2 + C₈χ/2)` with `v = √(p/d)`. -/
theorem l2_rc2_sum (hR : TRegime d p) {h : ℝ} (hh : 0 < h) (ct : Contact.{u} d p)
    {C₈ C₇ CS χ v : ℝ} (hCS : 0 ≤ CS) (hv0 : 0 < v) (hpv : (p : ℝ) / v = d * v)
    (hs8 : 1 / (d : ℝ) * ∑ i ∈ ct.N, |ct.yp i - 2| ≤ C₈ * χ)
    (hYD : ∑ i ∈ ct.N, ct.yp i * ct.delta i ≤ C₇ * p)
    (HS : ∀ i ∈ ct.S, ct.E (fun σ => ct.gp σ i i - ct.XP h σ i i) ≤ CS * Real.sqrt h * ct.yp i) :
    ∑ i ∈ ct.N, ct.E (fun σ => |ct.XP h σ i i / 2 - 1|) ≤
      (d : ℝ) * (CS * Real.sqrt h + 3 * Real.sqrt (epsP d p / p + epsP d p ^ 2) + v / 2 +
        C₇ * v / 2 + C₈ * χ / 2) := by
  have hd0 : (0 : ℝ) < d := hR.pfA_d_pos
  set ρ := epsP d p / p + epsP d p ^ 2 with hρ
  have hsqρ := Real.sqrt_nonneg ρ
  have hc : 0 ≤ CS * Real.sqrt h := mul_nonneg hCS (Real.sqrt_nonneg h)
  have hei : ∀ i ∈ ct.N, ct.E (fun σ => |ct.XP h σ i i / 2 - 1|) ≤
      CS * Real.sqrt h + 3 * Real.sqrt ρ + v / 2 + ct.yp i * ct.delta i / (2 * v) +
        |ct.yp i - 2| / 2 := by
    intro i hi
    have hiS := ct.mem_S_of_mem_N hi
    exact l2_rc2_ei_real hv0 (l2_y_le_two hR ct i).1.2 hc hsqρ
      (l2_E2i hR hh ct hiS hv0 (HS i hiS))
  refine (Finset.sum_le_sum hei).trans ?_
  have e : ∑ i ∈ ct.N, (CS * Real.sqrt h + 3 * Real.sqrt ρ + v / 2 +
      ct.yp i * ct.delta i / (2 * v) + |ct.yp i - 2| / 2) =
      (ct.N.card : ℝ) * (CS * Real.sqrt h + 3 * Real.sqrt ρ + v / 2) +
        1 / (2 * v) * ∑ i ∈ ct.N, ct.yp i * ct.delta i +
        (d : ℝ) / 2 * (1 / (d : ℝ) * ∑ i ∈ ct.N, |ct.yp i - 2|) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
      Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    have h1 : ∀ i ∈ ct.N, (d : ℝ) / 2 * (1 / (d : ℝ) * |ct.yp i - 2|) = |ct.yp i - 2| / 2 :=
      fun i _ => by field_simp
    have h2 : ∀ i ∈ ct.N, 1 / (2 * v) * (ct.yp i * ct.delta i) =
        ct.yp i * ct.delta i / (2 * v) := fun i _ => by field_simp
    rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2]
  rw [e]
  have hN : (ct.N.card : ℝ) ≤ d := l2_card_nbhd ct ct.v
  have c0 : 0 ≤ CS * Real.sqrt h + 3 * Real.sqrt ρ + v / 2 := by positivity
  have a1 := mul_le_mul_of_nonneg_right hN c0
  have a2 : 1 / (2 * v) * ∑ i ∈ ct.N, ct.yp i * ct.delta i ≤ (d : ℝ) * (C₇ * v / 2) := by
    calc 1 / (2 * v) * ∑ i ∈ ct.N, ct.yp i * ct.delta i ≤ 1 / (2 * v) * (C₇ * p) :=
          mul_le_mul_of_nonneg_left hYD (by positivity)
      _ = C₇ / 2 * ((p : ℝ) / v) := by field_simp
      _ = (d : ℝ) * (C₇ * v / 2) := by rw [hpv]; ring
  have a3 := mul_le_mul_of_nonneg_left hs8 (by positivity : (0 : ℝ) ≤ (d : ℝ) / 2)
  have e2 : (d : ℝ) * (CS * Real.sqrt h + 3 * Real.sqrt ρ + v / 2 + C₇ * v / 2 + C₈ * χ / 2) =
      (d : ℝ) * (CS * Real.sqrt h + 3 * Real.sqrt ρ + v / 2) + (d : ℝ) * (C₇ * v / 2) +
        (d : ℝ) / 2 * (C₈ * χ) := by ring
  rw [e2]
  linarith

/-- The closing algebra of (RC2): `ξ` dominates each piece of the bound. -/
theorem l2_rc2_xi_real {β α ε sρ χ sh v X2 xi id1 C₈ CS C₇ : ℝ} (hC₈ : 0 ≤ C₈) (hCS : 0 ≤ CS)
    (hC₇ : 0 ≤ C₇) (hε : 0 ≤ ε) (hsρ : 0 ≤ sρ) (hχ : 0 ≤ χ) (hsh : 0 ≤ sh) (hv : v ≤ X2)
    (hv0 : 0 ≤ v) (hd1 : 0 ≤ id1) (hxi : xi = sh + (X2 + χ) + sρ + ε + id1)
    (hfin : β - α ≤ 24 * ε + 18 * sρ + 3 * C₈ * χ + 4 * CS * sh + 2 * (1 + C₇) * v) :
    β ≤ α + (44 + 3 * C₈ + 4 * CS + 2 * C₇) * xi := by
  have k1 : ε ≤ xi := by rw [hxi]; linarith
  have k2 : sρ ≤ xi := by rw [hxi]; linarith
  have k3 : χ ≤ xi := by rw [hxi]; linarith
  have k4 : sh ≤ xi := by rw [hxi]; linarith
  have k5 : v ≤ xi := by rw [hxi]; linarith
  have m3 := mul_le_mul_of_nonneg_left k3 hC₈
  have m4 := mul_le_mul_of_nonneg_left k4 hCS
  have m5 := mul_le_mul_of_nonneg_left k5 hC₇
  linarith

/-- (RC2) at one contact, given (D8), its smallness, (D7) for `Σℓδ`, and (S1). -/
theorem l2_rc2_bound (hR : TRegime d p) {h : ℝ} (hh : 0 < h) (ct : Contact.{u} d p)
    {C₈ C₇ CS : ℝ} (hC₈ : 0 ≤ C₈) (hC₇ : 0 ≤ C₇) (hCS : 0 ≤ CS)
    (H8 : |ct.yp ct.v - 2| + |(ct.N.card : ℝ) / d - 1| + 1 / (d : ℝ) * ∑ i ∈ ct.N, |ct.yp i - 2| ≤
      C₈ * (epsS d p + η0Of d p + 1 / (d : ℝ)))
    (hχ : C₈ * (epsS d p + η0Of d p + 1 / (d : ℝ)) ≤ 1)
    (H7 : ct.sumEllDelta ≤ C₇ * p * aOf d p ^ 2)
    (HS : ∀ i ∈ ct.S, ct.E (fun σ => ct.gp σ i i - ct.XP h σ i i) ≤ CS * Real.sqrt h * ct.yp i) :
    ct.betaE h ≤ ct.alphaE h + (44 + 3 * C₈ + 4 * CS + 2 * C₇) * xiP d p h := by
  have hd0 : (0 : ℝ) < d := hR.pfA_d_pos
  have hp0 : (0 : ℝ) < p := hR.pfA_p_pos
  have hε := hR.pfA_epsP_nonneg
  have hη := hR.η0Of_pos
  have hes := pfA_epsS_nonneg d p
  set ρ := epsP d p / p + epsP d p ^ 2 with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  set χ := epsS d p + η0Of d p + 1 / (d : ℝ) with hχdef
  have hχ0 : 0 ≤ χ := by positivity
  have hyp : ∀ k, 0 ≤ ct.yp k ∧ ct.yp k ≤ 2 := fun k => (l2_y_le_two hR ct k).1
  have hs0 : 0 ≤ 1 / (d : ℝ) * ∑ i ∈ ct.N, |ct.yp i - 2| :=
    mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => abs_nonneg _)
  have hn0 := abs_nonneg ((ct.N.card : ℝ) / d - 1)
  have hv8 : |ct.yp ct.v - 2| ≤ C₈ * χ := by linarith
  have hs8 : 1 / (d : ℝ) * ∑ i ∈ ct.N, |ct.yp i - 2| ≤ C₈ * χ := by
    have := abs_nonneg (ct.yp ct.v - 2); linarith
  have hyv1 : 1 ≤ ct.yp ct.v := by have := (abs_le.1 (hv8.trans hχ)).1; linarith
  -- `Σ_N y_i δ_i ≤ C₇ p`
  have hδ : ∀ i ∈ ct.N, 0 ≤ ct.delta i := fun i hi => by
    have := (ct.ctx.cap ct.yp ct.ym ct.ctx.hyp ct.ctx.hym i (ct.mem_S_of_mem_N hi)).1
    unfold Contact.delta Contact.mp; linarith
  have hYD0 : 0 ≤ ∑ i ∈ ct.N, ct.yp i * ct.delta i :=
    Finset.sum_nonneg fun i hi => mul_nonneg (hyp i).1 (hδ i hi)
  have hsED : ct.sumEllDelta = aOf d p ^ 2 * (ct.yp ct.v * ∑ i ∈ ct.N, ct.yp i * ct.delta i) := by
    unfold Contact.sumEllDelta Contact.ell
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have ha2 : 0 < aOf d p ^ 2 := pow_pos hR.aOf_pos 2
  have hYD : ∑ i ∈ ct.N, ct.yp i * ct.delta i ≤ C₇ * p := by
    rw [hsED, show C₇ * p * aOf d p ^ 2 = aOf d p ^ 2 * (C₇ * p) by ring] at H7
    have h1 := le_of_mul_le_mul_left H7 ha2
    nlinarith
  -- `v = √(p/d)`
  set v := Real.sqrt ((p : ℝ) / d) with hvdef
  have hv0 : 0 < v := Real.sqrt_pos.2 (by positivity)
  have hv2 : v ^ 2 = (p : ℝ) / d := Real.sq_sqrt (by positivity)
  have hpv : (p : ℝ) / v = d * v := by
    rw [div_eq_iff hv0.ne']
    have : (p : ℝ) = d * v ^ 2 := by rw [hv2]; field_simp
    rw [this]; ring
  have hsum := l2_rc2_sum hR hh ct hCS hv0 hpv hs8 hYD HS
  have hE1 := l2_E1 hR ct
  have hcore := l2_rc2_core hR hh ct
  set E1 := ct.E (fun σ => |ct.gp σ ct.v ct.v / 2 - 1|)
  set SE := ∑ i ∈ ct.N, ct.E (fun σ => |ct.XP h σ i i / 2 - 1|)
  have hB : (d : ℝ) * (24 * epsP d p + 2 * E1) + 4 * SE ≤ (d : ℝ) * (24 * epsP d p +
      18 * Real.sqrt ρ + 3 * C₈ * χ + 4 * CS * Real.sqrt h + 2 * (1 + C₇) * v) := by
    have h1 : 2 * E1 ≤ 2 * (3 * Real.sqrt ρ + C₈ * χ / 2) := by linarith
    have h2 := mul_le_mul_of_nonneg_left h1 hd0.le
    have e : (d : ℝ) * (24 * epsP d p + 18 * Real.sqrt ρ + 3 * C₈ * χ + 4 * CS * Real.sqrt h +
        2 * (1 + C₇) * v) = (d : ℝ) * (24 * epsP d p) + (d : ℝ) * (2 * (3 * Real.sqrt ρ +
          C₈ * χ / 2)) + 4 * ((d : ℝ) * (CS * Real.sqrt h + 3 * Real.sqrt ρ + v / 2 +
            C₇ * v / 2 + C₈ * χ / 2)) := by ring
    rw [e, mul_add]
    linarith
  have hda : 2 * aOf d p ^ 2 * d ≤ 1 := by
    have h1 := hR.pf_d_a_sq_le
    have h2 : 1 / (d : ℝ) ≤ 1 / 4 := by
      rw [div_le_div_iff₀ hd0 (by norm_num)]; linarith [hR.ten_pow_six_le_d]
    nlinarith
  have hBpos : 0 ≤ 24 * epsP d p + 18 * Real.sqrt ρ + 3 * C₈ * χ + 4 * CS * Real.sqrt h +
      2 * (1 + C₇) * v := by positivity
  have hfin : ct.betaE h - ct.alphaE h ≤ 24 * epsP d p + 18 * Real.sqrt ρ + 3 * C₈ * χ +
      4 * CS * Real.sqrt h + 2 * (1 + C₇) * v := by
    refine hcore.trans ?_
    calc 2 * aOf d p ^ 2 * ((d : ℝ) * (24 * epsP d p + 2 * E1) + 4 * SE)
        ≤ 2 * aOf d p ^ 2 * ((d : ℝ) * (24 * epsP d p + 18 * Real.sqrt ρ + 3 * C₈ * χ +
            4 * CS * Real.sqrt h + 2 * (1 + C₇) * v)) :=
          mul_le_mul_of_nonneg_left hB (by positivity)
      _ = 2 * aOf d p ^ 2 * d * (24 * epsP d p + 18 * Real.sqrt ρ + 3 * C₈ * χ +
            4 * CS * Real.sqrt h + 2 * (1 + C₇) * v) := by ring
      _ ≤ 1 * (24 * epsP d p + 18 * Real.sqrt ρ + 3 * C₈ * χ + 4 * CS * Real.sqrt h +
            2 * (1 + C₇) * v) := mul_le_mul_of_nonneg_right hda hBpos
      _ = _ := one_mul _
  have hX2 : v ≤ Real.sqrt (ρ + (p : ℝ) / d) := Real.sqrt_le_sqrt (by linarith)
  have hxi : xiP d p h = Real.sqrt h + (Real.sqrt (ρ + (p : ℝ) / d) + χ) + Real.sqrt ρ +
      epsP d p + 1 / (d : ℝ) := by
    unfold xiP; rw [hρ, hχdef]; ring
  exact l2_rc2_xi_real hC₈ hCS hC₇ hε (Real.sqrt_nonneg _) hχ0 (Real.sqrt_nonneg _) hX2 hv0.le
    (by positivity) hxi hfin

end ContactHelpers

/-- `ε_s + η₀ + 1/d ≤ 4/p` in the regime (`ε_s p ≤ 1`, `η₀ √(pd) ≤ 2`, `p ≤ d`). -/
theorem l2_chi_le (hR : TRegime d p) : epsS d p + η0Of d p + 1 / (d : ℝ) ≤ 4 / p := by
  have hp0 := hR.pfA_p_pos
  have hd0 := hR.pfA_d_pos
  have hpd : (p : ℝ) ≤ d := by have := hR.pf_sq_le_d; nlinarith [hR.pfA_one_le_p]
  have h1 : epsS d p ≤ 1 / p := by rw [le_div_iff₀ hp0]; exact hR.pfA_epsS_mul_p
  have hsq : (p : ℝ) ≤ Real.sqrt ((p : ℝ) * d) := by
    rw [Real.le_sqrt hp0.le (by positivity)]; nlinarith
  have h2 : η0Of d p ≤ 2 / p := by
    have hu := hR.pf_u_sqrt.2
    have := mul_le_mul_of_nonneg_left hsq hR.η0Of_pos.le
    rw [le_div_iff₀ hp0]
    linarith
  have h3 : 1 / (d : ℝ) ≤ 1 / p := one_div_le_one_div_of_le hp0 hpd
  have : (4 : ℝ) / p = 1 / p + 2 / p + 1 / p := by ring
  linarith

/-! ### (RC2) and (D13) -/

/-- **L-RC2** (source "Averaged profile inequalities" and (RC2), l.1800–1842; AUDIT-D §3.5 PROF,
RC2). From (F2) at `k = 2`, (D7), (D8), (S1) and interpolation (the `y_i`-weighted
Cauchy–Schwarz avoids small sources): `β ≤ α + C ξ`. -/
theorem rc2_profile : ∃ C : ℝ, 0 < C ∧ Eventually fun _c₀ _κ₀ d p h =>
    ∀ ct : Contact.{u} d p, ct.betaE h ≤ ct.alphaE h + C * xiP d p h := by
  obtain ⟨C₈, hC₈, hD8⟩ := d8_profile.{u}
  obtain ⟨C₇, hC₇, hD7⟩ := d7.{u}
  obtain ⟨CS, hCS, hS1⟩ := in_S1.{u}
  refine ⟨44 + 3 * C₈ + 4 * CS + 2 * C₇, by positivity,
    (((hD8.and hD7).and hS1).and (eventually_reg_ge (fun _ => ⌈4 * C₈⌉₊))).mono ?_⟩
  rintro c₀ κ₀ d p h ⟨⟨⟨H8, H7⟩, HS⟩, hReg, hp⟩ ct
  have hR := hReg.treg
  have hp0 := hR.pfA_p_pos
  have hp4 : 4 * C₈ ≤ (p : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hp)
  have hχ : C₈ * (epsS d p + η0Of d p + 1 / (d : ℝ)) ≤ 1 := by
    have h1 := mul_le_mul_of_nonneg_left (l2_chi_le hR) hC₈.le
    have h2 : C₈ * (4 / p) ≤ 1 := by rw [mul_div_assoc', div_le_one hp0]; linarith
    linarith
  exact l2_rc2_bound hR hReg.h_pos ct hC₈.le hC₇.le hCS.le (H8 ct) hχ (H7 ct).2.1
    fun i hi => (HS ct i hi).1.2

/-- **L-D13** (source (RC5) and (D13), l.1933–1951; AUDIT-D §3.7, AUDIT-B B-5). The row-free part of
`Q_*/a²` is exactly `2L_d[(p-1)t_{+,0} + p t_{-,0}]`; at `x_i = 0` the row part is
`-6p(2p-1)P_i z_i² ≤ 0`; the rest has a plus row factor and a second row factor. With
`d⁻¹ Σ_N E x_i² ≤ C p/d` (D7) and `d⁻¹ Σ_N E z_i² ≤ C δ̄` (C2):
`Q_* ≤ a²(2L_d[(p-1)t_{+,0} + p t_{-,0}] + C p³ √(p δ̄/d))`. (Stated with `δ̄` rather than the
paper's `δ_row`, so that it holds on both routes; `p³√(pδ̄/d) = O(c₀^{17/3} p^{-2})`.) -/
theorem d13_centering : ∃ C : ℝ, 0 < C ∧ Eventually fun _c₀ _κ₀ d p _h =>
    ∀ ct : Contact.{u} d p,
      ct.Qstar ≤ aOf d p ^ 2 * (2 * LdP d p * (((p : ℝ) - 1) * ct.tP0 + p * ct.tM0) +
        C * (p : ℝ) ^ 3 * Real.sqrt ((p : ℝ) * dbar d p / d)) := by
  obtain ⟨CU, hCU, hU⟩ := l2_umi.{u} 2 2 (by norm_num) (by norm_num)
  obtain ⟨C₇, hC₇, hD7⟩ := d7.{u}
  obtain ⟨C₂, hC₂, hC2⟩ := in_C2.{u}
  refine ⟨50 * CU * (C₇ + C₂ + 1), by positivity,
    (((hU.and hD7).and hC2).and (eventually_treg_ge 0)).mono ?_⟩
  rintro c₀ κ₀ d p h ⟨⟨⟨HU, H7⟩, H2⟩, hR, -⟩ ct
  exact l2_d13_core hR ct hCU.le hC₇.le hC₂.le (HU ct) (H7 ct).1 (H2 ct).2.1

end BiluLinial.Tight
