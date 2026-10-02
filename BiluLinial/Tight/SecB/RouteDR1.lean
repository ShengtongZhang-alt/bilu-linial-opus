/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecB.S1
public import BiluLinial.Tight.SourceMax
public import BiluLinial.Tight.ParamsExtra
public import BiluLinial.Tight.FloorLemma
public import BiluLinial.Tight.SecA.ParP

/-!
# The GCI-free route: row equations and the score-difference energy (DR1)

Nodes TB.E1row, TB.root, TB.RE, TB.B, TB.DR1 of `docs/tight/BP_SECB.md` (source lines 674–690, the
row-equation part of the proof of Lemma "Uniform incident-row gain"; AUDIT-B §2.2–2.2′,
`docs/tight/DR1_CHECK.md` §2, verdict **confirmed**).

Notation at a vertex `w ∈ S`, `N = N_S(w)`: `x_i = G⁺_wi`, `z_i = G⁻_wi` (physical),
`S^± = Σ_N E x_i²` (resp. `z_i²`), `T = Σ_N E x_i z_i`, `m^± = E h^±_w`,
`B^± = 1 - D^±_w m^± + a² Σ_N E G^±_ww G^±_ii`, `ε = r - 1`, `δ̄ = ε + p⁴/d + (p/d)^{1/3}`.

* **TB.Kmom** (`kpoly_moment`, elementary): `|E K(x_i, z_i, P_i, Q_i)| ≤ C p³` for the
  third-order endpoint polynomial (`Kpoly`), from F2 and `|G_jk| ≤ √(G_jj G_kk)`.
* **TB.E1row** (`row_endpoint_plus_of`, `row_endpoint_of`): with
  `𝒟₁x_i = -a G⁺_ww G⁺_ii + (2p-1) a x_i² - 2pa x_i z_i` and
  `𝒟₁z_i = a G⁻_ww G⁻_ii - (2p-1) a z_i² + 2pa x_i z_i`,
  `|E[σ_wi x_i] - E 𝒟₁x_i| ≤ K p³ a³` and `|E[σ_wi z_i] - E 𝒟₁z_i| ≤ K p³ a³`. The plus branch is
  the endpoint calculus (E1) of Section A (input `E1Shape`, bridged from
  `CapPoint.endpoint_E1_cp` in `Export.lean`) with `p⁵a⁵ ≤ p³a³` and TB.Kmom; the minus branch is
  the plus branch at the swapped point `(y⁻, y⁺)` under `σ ↦ -σ` (`lawE_swap`, `d1z_neg`).
* **TB.root** (`root_row_identity`, exact): row `w` of `P̃ P̃⁻¹ = I` reads
  `D_w h_w + τ a Σ_N σ_wi G^τ_wi = 1` on the support.
* **TB.RE** (`row_eq_of`): `(2p-1)a²S⁺ - 2pa²T = B⁺ - aΣ_N R⁺_i`,
  `(2p-1)a²S⁻ - 2pa²T = B⁻ + aΣ_N R⁻_i` (`R^±_i` the residuals of TB.E1row), hence
  `|(2p-1)a²S^± - 2pa²T - B^±| ≤ K₃ p³/d` with `K₃ = K` (since `a⁴ d ≤ 1/(4d)`, `|N| ≤ d`).
* **TB.B** (`rowB_le`): `B^± ≤ 2.01 ρ + 1.04/d + 3.03 ε` for any `ρ ≥ max(0, 1 - m^±)`, from
  `D_w = 1 + L_w - C_w` (`c(1+c) = a²y_wy_i`), `L_w ≤ d a² s² ≤ 1.01`, `C_w ≤ 1.0201/d`, and
  `E h_w h_i ≤ ((pr-2)/(p-2))² ≤ 1 + 3ε` (F2 with `k = 2`).
* **TB.DR1** (`dr1_pt`, `dr1_of_c2`): adding the two equations,
  `(2p-1) a² Σ_N E(x_i - z_i)² = B⁺ + B⁻ + E3⁺ + E3⁻ + 2a²T`, and `2a²T ≤ a²(S⁺ + S⁻)`
  (no sign of `T` is used: this is where GCI is avoided). With (C2) (`1 - m^± ≤ K_δ δ̄`,
  `a² S^± ≤ K_δ δ̄`): `a² Σ_N E(x_i - z_i)² ≤ K_DR δ̄ / p`, `K_DR = 6.02 K_δ + 8.14 + 2K₃`.

**Checks.** Isolated `w`: all sums vanish, `B = 1 - D m = 1 - m`; DR1 reads `0 ≤ …`. Zero plus
source at `w`: `x ≡ 0`, `B⁺ = 1 - m⁺ = 0` (`h_w = 1`); DR1 becomes a minus-row bound. Numerical
checks of the exact identity on `K₂, K₄, K_{3,3}, K₅, Q₃`, Petersen: DR1_CHECK §5.
-/

@[expose] public section

namespace BiluLinial.Tight.SecB

open Matrix SecB

universe u

section Raw

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- `𝒟₁x_i = -a G⁺_ww G⁺_ii + (2p-1) a x_i² - 2pa x_i z_i` (`x_i = G⁺_wi`, `z_i = G⁻_wi`). -/
noncomputable def d1x (d p : ℕ) (yp ym : V → ℝ) (S : Finset V) (w i : V) (σ : Config V) : ℝ :=
  -(aOf d p) * greenP G (aOf d p) 1 yp σ S w w * greenP G (aOf d p) 1 yp σ S i i +
    (2 * p - 1) * aOf d p * greenP G (aOf d p) 1 yp σ S w i ^ 2 -
    2 * p * aOf d p * (greenP G (aOf d p) 1 yp σ S w i * greenP G (aOf d p) (-1) ym σ S w i)

/-- `𝒟₁z_i = a G⁻_ww G⁻_ii - (2p-1) a z_i² + 2pa x_i z_i`. -/
noncomputable def d1z (d p : ℕ) (yp ym : V → ℝ) (S : Finset V) (w i : V) (σ : Config V) : ℝ :=
  aOf d p * greenP G (aOf d p) (-1) ym σ S w w * greenP G (aOf d p) (-1) ym σ S i i -
    (2 * p - 1) * aOf d p * greenP G (aOf d p) (-1) ym σ S w i ^ 2 +
    2 * p * aOf d p * (greenP G (aOf d p) 1 yp σ S w i * greenP G (aOf d p) (-1) ym σ S w i)

/-- **TB.root.** Row `w` of `P̃ P̃⁻¹ = I`: `D_w h_w + τ a Σ_{i ∈ N_S(w)} σ_wi G_wi = 1`. -/
theorem root_row_identity {a τ : ℝ} {y : V → ℝ} {σ : Config V} {S : Finset V} {w : V}
    (hP : (precN G a τ y σ S).PosDef) (hw : w ∈ S) :
    diagD G a y S w * hN G a τ y σ S w +
      τ * a * ∑ i ∈ nbhd G S w, sgn σ w i * greenP G a τ y σ S w i = 1 := by
  set P := precN G a τ y σ S with hPdef
  have hu : IsUnit P.det := isUnit_iff_ne_zero.mpr hP.det_pos.ne'
  have hsymm : ∀ k l, P⁻¹ k l = P⁻¹ l k := fun k l => by
    have := congrFun (congrFun hP.inv.1 l) k
    simpa [Matrix.conjTranspose_apply] using this
  have h1 : (P * P⁻¹) w w = 1 := by rw [Matrix.mul_nonsing_inv P hu, Matrix.one_apply_eq]
  rw [Matrix.mul_apply] at h1
  have hPww : P w w = diagD G a y S w := by rw [hPdef]; simp [precN, hw]
  have hPwk : ∀ k, k ≠ w → P w k =
      if k ∈ nbhd G S w then τ * a * (Real.sqrt (y w) * Real.sqrt (y k)) * sgn σ w k else 0 := by
    intro k hk
    have hk' : w ≠ k := fun h => hk h.symm
    rw [hPdef]
    simp only [precN, Matrix.of_apply, hk', ↓reduceIte]
    by_cases hn : k ∈ nbhd G S w
    · have hn' : k ∈ S ∧ G.Adj w k := by simpa [nbhd] using hn
      simp [hw, hn'.1, hn'.2, hn]
    · have hn' : ¬ (w ∈ S ∧ k ∈ S ∧ G.Adj w k) := fun h => hn (by simp [nbhd, h.2.1, h.2.2])
      simp only [hn', hn, ↓reduceIte]
  have hg : ∀ k, greenP G a τ y σ S w k = Real.sqrt (y w) * P⁻¹ w k * Real.sqrt (y k) :=
    fun k => rfl
  have hh : hN G a τ y σ S w = P⁻¹ w w := rfl
  have hterm : ∀ k, P w k * P⁻¹ k w =
      (if k = w then diagD G a y S w * hN G a τ y σ S w else 0) +
        (if k ∈ nbhd G S w then τ * a * (sgn σ w k * greenP G a τ y σ S w k) else 0) := by
    intro k
    by_cases hk : k = w
    · rw [hk]
      have hn : w ∉ nbhd G S w := by simp [nbhd]
      simp only [hPww, hh, hn, ↓reduceIte, add_zero]
    · rw [hPwk k hk]
      by_cases hn : k ∈ nbhd G S w
      · simp only [hk, hn, ↓reduceIte, zero_add, hg]
        rw [hsymm k w]
        ring
      · simp only [hk, hn, ↓reduceIte, zero_add, zero_mul]
  simp_rw [hterm] at h1
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ w, if_pos (Finset.mem_univ _),
    Finset.sum_ite_mem Finset.univ, Finset.univ_inter, ← Finset.mul_sum] at h1
  linarith

/-- A `2 × 2` principal minor of a positive semidefinite matrix: `M_jk² ≤ M_jj M_kk`. -/
theorem posSemidef_entry_sq_le {n : Type*} [Fintype n] [DecidableEq n] {M : Matrix n n ℝ}
    (hM : M.PosSemidef) (j k : n) : M j k ^ 2 ≤ M j j * M k k := by
  have h2 := (hM.submatrix ![j, k]).det_nonneg
  rw [Matrix.det_fin_two] at h2
  have hs : M k j = M j k := by
    have := congrFun (congrFun hM.1 j) k
    simpa [Matrix.conjTranspose_apply] using this
  simp [Matrix.submatrix_apply, hs] at h2
  nlinarith [h2]

/-- `(G_jk)² ≤ G_jj G_kk` for the physical inverse on the support. -/
theorem greenP_sq_le {a τ : ℝ} {y : V → ℝ} {σ : Config V} {S : Finset V}
    (hP : (precN G a τ y σ S).PosDef) (hy : ∀ k, 0 ≤ y k) (j k : V) :
    greenP G a τ y σ S j k ^ 2 ≤ greenP G a τ y σ S j j * greenP G a τ y σ S k k := by
  have h := posSemidef_entry_sq_le hP.inv.posSemidef j k
  rw [greenP_diag G σ S (hy j), greenP_diag G σ S (hy k)]
  have e : greenP G a τ y σ S j k ^ 2 = y j * y k * ((precN G a τ y σ S)⁻¹ j k) ^ 2 := by
    unfold greenP
    rw [mul_pow, mul_pow, Real.sq_sqrt (hy j), Real.sq_sqrt (hy k)]
    ring
  rw [e]
  calc y j * y k * ((precN G a τ y σ S)⁻¹ j k) ^ 2
      ≤ y j * y k * ((precN G a τ y σ S)⁻¹ j j * (precN G a τ y σ S)⁻¹ k k) :=
        mul_le_mul_of_nonneg_left h (mul_nonneg (hy j) (hy k))
    _ = y j * hN G a τ y σ S j * (y k * hN G a τ y σ S k) := by unfold hN; ring

end Raw

section Kmom

/-- `|8U³ - 12UV + 4W| ≤ 8|U|³ + 12|U|V + 4|W|` for `V ≥ 0`. -/
theorem kpoly_abs_aux1 {U Vv W : ℝ} (hV : 0 ≤ Vv) :
    |8 * U ^ 3 - 12 * U * Vv + 4 * W| ≤ 8 * |U| ^ 3 + 12 * |U| * Vv + 4 * |W| := by
  calc |8 * U ^ 3 - 12 * U * Vv + 4 * W| ≤ |8 * U ^ 3 - 12 * U * Vv| + |4 * W| := abs_add_le _ _
    _ ≤ |8 * U ^ 3| + |12 * U * Vv| + |4 * W| := by
        have := abs_sub (8 * U ^ 3) (12 * U * Vv); linarith
    _ = 8 * |U| ^ 3 + 12 * |U| * Vv + 4 * |W| := by
        simp only [abs_mul, abs_pow, abs_of_nonneg hV, Nat.abs_ofNat]

/-- `|4U² - 2V| ≤ 4|U|² + 2V` for `V ≥ 0`. -/
theorem kpoly_abs_aux2 {U Vv : ℝ} (hV : 0 ≤ Vv) : |4 * U ^ 2 - 2 * Vv| ≤ 4 * |U| ^ 2 + 2 * Vv := by
  rw [sq_abs, abs_le]
  constructor <;> nlinarith [sq_nonneg U]

/-- The real bound behind TB.Kmom: if `|x|, |z| ≤ g` and `0 ≤ P, Q ≤ g²`, then
`|K(x, z, P, Q)| ≤ 264 p³ g⁴` (`p ≥ 1`). -/
theorem kpoly_abs_le {p : ℕ} (hp : 1 ≤ p) {x z P Q g : ℝ} (hx : |x| ≤ g) (hz : |z| ≤ g)
    (hP0 : 0 ≤ P) (hP : P ≤ g ^ 2) (hQ0 : 0 ≤ Q) (hQ : Q ≤ g ^ 2) :
    |Kpoly p x z P Q| ≤ 264 * (p : ℝ) ^ 3 * g ^ 4 := by
  have hq1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hg : 0 ≤ g := le_trans (abs_nonneg x) hx
  have hx2 : x ^ 2 ≤ g ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg x) hx 2
  have hz2 : z ^ 2 ≤ g ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg z) hz 2
  generalize hq : (p : ℝ) = q at hq1 ⊢
  have eK : Kpoly p x z P Q =
      x * (8 * ((q - 1) * x - q * z) ^ 3 -
          12 * ((q - 1) * x - q * z) * ((q - 1) * (P + x ^ 2) + q * (Q + z ^ 2)) +
          4 * ((q - 1) * (3 * P * x + x ^ 3) - q * (3 * Q * z + z ^ 3))) -
        3 * (P - x ^ 2) * (4 * ((q - 1) * x - q * z) ^ 2 -
          2 * ((q - 1) * (P + x ^ 2) + q * (Q + z ^ 2))) := by
    rw [← hq]; simp only [Kpoly]
  rw [eK]
  generalize hU : (q - 1) * x - q * z = U
  generalize hV : (q - 1) * (P + x ^ 2) + q * (Q + z ^ 2) = Vv
  generalize hW : (q - 1) * (3 * P * x + x ^ 3) - q * (3 * Q * z + z ^ 3) = W
  have hq0 : 0 ≤ q - 1 := by linarith
  have hUb : |U| ≤ 2 * q * g := by
    rw [← hU]
    calc |(q - 1) * x - q * z| ≤ |(q - 1) * x| + |q * z| := abs_sub _ _
      _ = (q - 1) * |x| + q * |z| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hq0, abs_of_nonneg (by linarith : (0 : ℝ) ≤ q)]
      _ ≤ (q - 1) * g + q * g :=
          add_le_add (mul_le_mul_of_nonneg_left hx hq0) (mul_le_mul_of_nonneg_left hz (by linarith))
      _ ≤ 2 * q * g := by nlinarith
  have hV0 : 0 ≤ Vv := by
    rw [← hV]
    exact add_nonneg (mul_nonneg hq0 (by positivity)) (mul_nonneg (by linarith) (by positivity))
  have hVb : Vv ≤ 4 * q * g ^ 2 := by
    rw [← hV]
    have h1 : (q - 1) * (P + x ^ 2) ≤ (q - 1) * (2 * g ^ 2) :=
      mul_le_mul_of_nonneg_left (by linarith) hq0
    have h2 : q * (Q + z ^ 2) ≤ q * (2 * g ^ 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    nlinarith [sq_nonneg g]
  have hcube : ∀ t : ℝ, ∀ R : ℝ, 0 ≤ R → R ≤ g ^ 2 → |t| ≤ g →
      |3 * R * t + t ^ 3| ≤ 4 * g ^ 3 := by
    intro t R hR0 hR ht
    have ht0 := abs_nonneg t
    calc |3 * R * t + t ^ 3| ≤ |3 * R * t| + |t ^ 3| := abs_add_le _ _
      _ = 3 * R * |t| + |t| ^ 3 := by
          simp only [abs_mul, abs_pow, abs_of_nonneg hR0, Nat.abs_ofNat]
      _ ≤ 3 * g ^ 2 * g + g ^ 3 := by
          have := mul_le_mul hR ht ht0 (sq_nonneg g)
          have := pow_le_pow_left₀ ht0 ht 3
          nlinarith
      _ = 4 * g ^ 3 := by ring
  have hWb : |W| ≤ 8 * q * g ^ 3 := by
    rw [← hW]
    calc |(q - 1) * (3 * P * x + x ^ 3) - q * (3 * Q * z + z ^ 3)|
        ≤ |(q - 1) * (3 * P * x + x ^ 3)| + |q * (3 * Q * z + z ^ 3)| := abs_sub _ _
      _ = (q - 1) * |3 * P * x + x ^ 3| + q * |3 * Q * z + z ^ 3| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hq0, abs_of_nonneg (by linarith : (0 : ℝ) ≤ q)]
      _ ≤ (q - 1) * (4 * g ^ 3) + q * (4 * g ^ 3) :=
          add_le_add (mul_le_mul_of_nonneg_left (hcube x P hP0 hP hx) hq0)
            (mul_le_mul_of_nonneg_left (hcube z Q hQ0 hQ hz) (by linarith))
      _ ≤ 8 * q * g ^ 3 := by nlinarith [pow_nonneg hg 3]
  have hU0 := abs_nonneg U
  -- first bracket
  have hB1 : |8 * U ^ 3 - 12 * U * Vv + 4 * W| ≤
      64 * q ^ 3 * g ^ 3 + 96 * q ^ 2 * g ^ 3 + 32 * q * g ^ 3 := by
    refine le_trans (kpoly_abs_aux1 hV0) ?_
    have a1 : |U| ^ 3 ≤ (2 * q * g) ^ 3 := pow_le_pow_left₀ hU0 hUb 3
    have a2 : |U| * Vv ≤ (2 * q * g) * (4 * q * g ^ 2) := mul_le_mul hUb hVb hV0 (by positivity)
    linarith
  -- second bracket
  have hB2 : |4 * U ^ 2 - 2 * Vv| ≤ 16 * q ^ 2 * g ^ 2 + 8 * q * g ^ 2 := by
    refine le_trans (kpoly_abs_aux2 hV0) ?_
    have a1 : |U| ^ 2 ≤ (2 * q * g) ^ 2 := pow_le_pow_left₀ hU0 hUb 2
    linarith
  have hPx : |P - x ^ 2| ≤ g ^ 2 := by
    rw [abs_le]; constructor <;> linarith [sq_nonneg x]
  have hq2 : q ^ 2 ≤ q ^ 3 := pow_le_pow_right₀ hq1 (by norm_num)
  have hq3 : q ≤ q ^ 3 := le_self_pow₀ hq1 (by norm_num)
  have hg3 : 0 ≤ g ^ 3 := pow_nonneg hg 3
  have hg4 : 0 ≤ g ^ 4 := pow_nonneg hg 4
  calc |x * (8 * U ^ 3 - 12 * U * Vv + 4 * W) - 3 * (P - x ^ 2) * (4 * U ^ 2 - 2 * Vv)|
      ≤ |x * (8 * U ^ 3 - 12 * U * Vv + 4 * W)| + |3 * (P - x ^ 2) * (4 * U ^ 2 - 2 * Vv)| :=
        abs_sub _ _
    _ = |x| * |8 * U ^ 3 - 12 * U * Vv + 4 * W| +
          3 * |P - x ^ 2| * |4 * U ^ 2 - 2 * Vv| := by
        simp only [abs_mul, Nat.abs_ofNat]
    _ ≤ g * (64 * q ^ 3 * g ^ 3 + 96 * q ^ 2 * g ^ 3 + 32 * q * g ^ 3) +
          3 * g ^ 2 * (16 * q ^ 2 * g ^ 2 + 8 * q * g ^ 2) := by
        have b1 := mul_le_mul hx hB1 (abs_nonneg _) hg
        have b2 := mul_le_mul hPx hB2 (abs_nonneg _) (sq_nonneg g)
        linarith
    _ = g ^ 4 * (64 * q ^ 3 + 144 * q ^ 2 + 56 * q) := by ring
    _ ≤ g ^ 4 * (264 * q ^ 3) := by
        apply mul_le_mul_of_nonneg_left _ hg4; linarith
    _ = 264 * q ^ 3 * g ^ 4 := by ring

/-- `(A + B + C + D)⁴ ≤ 64 (A⁴ + B⁴ + C⁴ + D⁴)`. -/
theorem sum4_pow4_le (A B C D : ℝ) :
    (A + B + C + D) ^ 4 ≤ 64 * (A ^ 4 + B ^ 4 + C ^ 4 + D ^ 4) := by
  have h1 : (A + B + C + D) ^ 2 ≤ 4 * (A ^ 2 + B ^ 2 + C ^ 2 + D ^ 2) := by
    linarith [sq_nonneg (A - B), sq_nonneg (A - C), sq_nonneg (A - D), sq_nonneg (B - C),
      sq_nonneg (B - D), sq_nonneg (C - D)]
  have h2 : (A ^ 2 + B ^ 2 + C ^ 2 + D ^ 2) ^ 2 ≤ 4 * (A ^ 4 + B ^ 4 + C ^ 4 + D ^ 4) := by
    linarith [sq_nonneg (A ^ 2 - B ^ 2), sq_nonneg (A ^ 2 - C ^ 2), sq_nonneg (A ^ 2 - D ^ 2),
      sq_nonneg (B ^ 2 - C ^ 2), sq_nonneg (B ^ 2 - D ^ 2), sq_nonneg (C ^ 2 - D ^ 2)]
  have h0 : 0 ≤ (A + B + C + D) ^ 2 := sq_nonneg _
  calc (A + B + C + D) ^ 4 = ((A + B + C + D) ^ 2) ^ 2 := by ring
    _ ≤ (4 * (A ^ 2 + B ^ 2 + C ^ 2 + D ^ 2)) ^ 2 := pow_le_pow_left₀ h0 h1 2
    _ = 16 * (A ^ 2 + B ^ 2 + C ^ 2 + D ^ 2) ^ 2 := by ring
    _ ≤ 16 * (4 * (A ^ 4 + B ^ 4 + C ^ 4 + D ^ 4)) := by linarith
    _ = 64 * (A ^ 4 + B ^ 4 + C ^ 4 + D ^ 4) := by ring

/-- `|E f| ≤ E |f|` for the paired law. -/
theorem abs_lawE_le {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {p : ℕ} {a : ℝ} {yp ym : V → ℝ} {S : Finset V} (f : Config V → ℝ) :
    |lawE G p a yp ym S f| ≤ lawE G p a yp ym S (fun σ => |f σ|) := by
  rw [abs_le]
  constructor
  · have h := lawE_mono G (p := p) (a := a) (yp := yp) (ym := ym) (S := S)
      (f := fun σ => (-1) * |f σ|) (g := f) fun σ _ => by linarith [neg_abs_le (f σ)]
    rw [lawE_const_mul] at h
    linarith
  · exact lawE_mono G fun σ _ => le_abs_self _

end Kmom

/-- **TB.Kmom** (moment bound for the third-order endpoint polynomial). At every capped point,
every root `v ∈ S` and `i ∈ N_S(v)`: `|E K(x_i, z_i, P_i, Q_i)| ≤ C p³`. Sketch: with
`g = G⁺_vv + G⁺_ii + G⁻_vv + G⁻_ii`, `|x_i|, |z_i| ≤ g` (`|G_vi| ≤ √(G_vv G_ii)`), `P_i, Q_i ≤ g²`,
so `|U| ≤ 2pg`, `|V| ≤ 4pg²`, `|W| ≤ 8pg³` and `|K| ≤ 264 p³ g⁴` (`kpoly_abs_le`);
`g⁴ ≤ 64 Σ G⁴ ≤ 64 · 16 Σ h⁴` (`y ≤ s ≤ 2`) and `E h⁴ ≤ 2⁴` by F2 (`k = 4`). -/
theorem kpoly_moment : ∃ C : ℝ, 0 ≤ C ∧ Eventually fun _ _ d p _ =>
    ∀ cp : CapPoint.{u} d p, ∀ v ∈ cp.S, ∀ i ∈ cp.N v,
      |cp.E (fun σ => Kpoly p (cp.gp σ v i) (cp.gm σ v i) (cp.gp σ v v * cp.gp σ i i)
        (cp.gm σ v v * cp.gm σ i i))| ≤ C * (p : ℝ) ^ 3 := by
  refine ⟨264 * 64 * 16 * 64, by norm_num, (eventually_base 0).mono ?_⟩
  rintro c₀ κ₀ d p h ⟨hR, -⟩ cp v hv i hi
  have hiS : i ∈ cp.S := (Finset.mem_filter.mp hi).1
  have hp6 : 4 + 2 ≤ p := le_trans (by norm_num) hR.hp
  have hp8 : 2 * 4 ≤ p := le_trans (by norm_num) hR.hp
  have hp1 : 1 ≤ p := le_trans (by norm_num) hR.hp
  have hs := hR.sOf_pos
  have hs2 := SecA.sOf_le_two hR
  have hsub : ∀ y : cp.V → ℝ, InCube (cp.lam * sOf d p) y → ∀ k, 0 ≤ y k ∧ y k ≤ 2 :=
    fun y hy k => ⟨(hy k).1, le_trans (hy k).2
      (by nlinarith [cp.ctx.lam_le_one, cp.ctx.lam_nonneg])⟩
  have hyp := hsub _ cp.hyp
  have hym := hsub _ cp.hym
  -- F2 with `k = 4`
  have hb : 0 ≤ ((p : ℝ) * rOf d p - (4 : ℕ)) / ((p : ℝ) - (4 : ℕ)) ∧
      ((p : ℝ) * rOf d p - (4 : ℕ)) / ((p : ℝ) - (4 : ℕ)) ≤ 2 := by
    have hkp : (2 : ℝ) * 4 ≤ p := by exact_mod_cast hp8
    have hr := hR.rOf_le
    have hr1 := hR.one_lt_rOf
    have hpk : 0 < (p : ℝ) - (4 : ℕ) := by push_cast; linarith
    have hp0 : (0 : ℝ) ≤ p := by positivity
    have hr1p := mul_le_mul_of_nonneg_left hr1.le hp0
    have hrp := mul_le_mul_of_nonneg_left hr hp0
    constructor
    · refine div_nonneg ?_ hpk.le
      push_cast
      linarith
    · rw [div_le_iff₀ hpk]
      push_cast
      linarith
  have hmom : ∀ k ∈ cp.S, cp.E (fun σ => cp.hp σ k ^ 4) ≤ 16 ∧ cp.E (fun σ => cp.hm σ k ^ 4) ≤ 16 :=
    fun k hk => by
      have hF := source_moments cp.G hR cp.ctx cp.hyp cp.hym hk (k := 4) (by norm_num) hp6
      have h16 : (((p : ℝ) * rOf d p - (4 : ℕ)) / ((p : ℝ) - (4 : ℕ))) ^ 4 ≤ 16 :=
        calc _ ≤ (2 : ℝ) ^ 4 := pow_le_pow_left₀ hb.1 hb.2 4
          _ = 16 := by norm_num
      exact ⟨hF.1.trans h16, hF.2.trans h16⟩
  -- pointwise bound on the support
  set Hs : Config cp.V → ℝ := fun σ =>
    cp.hp σ v ^ 4 + cp.hp σ i ^ 4 + cp.hm σ v ^ 4 + cp.hm σ i ^ 4 with hHs
  have hpt : ∀ σ, wt cp.G p (aOf d p) cp.yp cp.ym σ cp.S ≠ 0 →
      |Kpoly p (cp.gp σ v i) (cp.gm σ v i) (cp.gp σ v v * cp.gp σ i i)
        (cp.gm σ v v * cp.gm σ i i)| ≤ (264 * 64 * 16) * (p : ℝ) ^ 3 * Hs σ := by
    intro σ hσ
    obtain ⟨hpP, hpM⟩ := posDef_of_wt_ne_zero cp.G hσ
    have hyp0 : ∀ k, 0 ≤ cp.yp k := fun k => (hyp k).1
    have hym0 : ∀ k, 0 ≤ cp.ym k := fun k => (hym k).1
    -- nonnegative diagonals and their normalized bounds
    have dP : ∀ k, 0 ≤ cp.gp σ k k ∧ cp.gp σ k k ≤ 2 * cp.hp σ k := fun k => by
      have hh : 0 ≤ cp.hp σ k := hpP.inv.posSemidef.diag_nonneg
      have e : cp.gp σ k k = cp.yp k * cp.hp σ k := greenP_diag cp.G σ cp.S (hyp k).1
      rw [e]
      exact ⟨mul_nonneg (hyp k).1 hh, mul_le_mul_of_nonneg_right (hyp k).2 hh⟩
    have dM : ∀ k, 0 ≤ cp.gm σ k k ∧ cp.gm σ k k ≤ 2 * cp.hm σ k := fun k => by
      have hh : 0 ≤ cp.hm σ k := hpM.inv.posSemidef.diag_nonneg
      have e : cp.gm σ k k = cp.ym k * cp.hm σ k := greenP_diag cp.G σ cp.S (hym k).1
      rw [e]
      exact ⟨mul_nonneg (hym k).1 hh, mul_le_mul_of_nonneg_right (hym k).2 hh⟩
    have hA := dP v
    have hB := dP i
    have hC := dM v
    have hD := dM i
    have hxs : cp.gp σ v i ^ 2 ≤ cp.gp σ v v * cp.gp σ i i := greenP_sq_le cp.G hpP hyp0 v i
    have hzs : cp.gm σ v i ^ 2 ≤ cp.gm σ v v * cp.gm σ i i := greenP_sq_le cp.G hpM hym0 v i
    simp only [hHs]
    generalize cp.gp σ v v = A at hA hxs ⊢
    generalize cp.gp σ i i = B at hB hxs ⊢
    generalize cp.gm σ v v = C at hC hzs ⊢
    generalize cp.gm σ i i = D at hD hzs ⊢
    generalize cp.gp σ v i = x at hxs ⊢
    generalize cp.gm σ v i = z at hzs ⊢
    have hg0 : 0 ≤ A + B + C + D := by linarith [hA.1, hB.1, hC.1, hD.1]
    have hAB : A * B ≤ (A + B + C + D) ^ 2 := by
      have h1 : A * B ≤ (A + B) ^ 2 := by nlinarith [sq_nonneg A, sq_nonneg B, mul_nonneg hA.1 hB.1]
      have h2 := pow_le_pow_left₀ (add_nonneg hA.1 hB.1)
        (show A + B ≤ A + B + C + D by linarith [hC.1, hD.1]) 2
      linarith
    have hCD : C * D ≤ (A + B + C + D) ^ 2 := by
      have h1 : C * D ≤ (C + D) ^ 2 := by nlinarith [sq_nonneg C, sq_nonneg D, mul_nonneg hC.1 hD.1]
      have h2 := pow_le_pow_left₀ (add_nonneg hC.1 hD.1)
        (show C + D ≤ A + B + C + D by linarith [hA.1, hB.1]) 2
      linarith
    have hx : |x| ≤ A + B + C + D :=
      (sq_le_sq.mp (hxs.trans hAB)).trans_eq (abs_of_nonneg hg0)
    have hz : |z| ≤ A + B + C + D :=
      (sq_le_sq.mp (hzs.trans hCD)).trans_eq (abs_of_nonneg hg0)
    have hK := kpoly_abs_le hp1 hx hz (mul_nonneg hA.1 hB.1) hAB (mul_nonneg hC.1 hD.1) hCD
    have p4 : ∀ t w : ℝ, 0 ≤ t → t ≤ 2 * w → t ^ 4 ≤ 16 * w ^ 4 := fun t w ht htw => by
      have := pow_le_pow_left₀ ht htw 4
      linarith [show (2 * w) ^ 4 = 16 * w ^ 4 by ring]
    have hg4 : (A + B + C + D) ^ 4 ≤ 64 * (16 * (cp.hp σ v ^ 4 + cp.hp σ i ^ 4 +
        cp.hm σ v ^ 4 + cp.hm σ i ^ 4)) := by
      have h1 := sum4_pow4_le A B C D
      have := p4 _ _ hA.1 hA.2
      have := p4 _ _ hB.1 hB.2
      have := p4 _ _ hC.1 hC.2
      have := p4 _ _ hD.1 hD.2
      linarith
    have hp3 : (0 : ℝ) ≤ 264 * (p : ℝ) ^ 3 := by positivity
    calc _ ≤ 264 * (p : ℝ) ^ 3 * (A + B + C + D) ^ 4 := hK
      _ ≤ 264 * (p : ℝ) ^ 3 * (64 * (16 * (cp.hp σ v ^ 4 + cp.hp σ i ^ 4 +
            cp.hm σ v ^ 4 + cp.hm σ i ^ 4))) := mul_le_mul_of_nonneg_left hg4 hp3
      _ = _ := by ring
  have hEH : cp.E Hs ≤ 64 := by
    have e : cp.E Hs = cp.E (fun σ => cp.hp σ v ^ 4) + cp.E (fun σ => cp.hp σ i ^ 4) +
        cp.E (fun σ => cp.hm σ v ^ 4) + cp.E (fun σ => cp.hm σ i ^ 4) := by
      unfold CapPoint.E; simp only [hHs]; rw [lawE_add, lawE_add, lawE_add]
    rw [e]
    linarith [(hmom v hv).1, (hmom i hiS).1, (hmom v hv).2, (hmom i hiS).2]
  unfold CapPoint.E at hEH ⊢
  refine le_trans (abs_lawE_le cp.G _) ?_
  refine le_trans (lawE_mono cp.G hpt) ?_
  rw [lawE_const_mul]
  calc (264 * 64 * 16) * (p : ℝ) ^ 3 * lawE cp.G p (aOf d p) cp.yp cp.ym cp.S Hs
      ≤ (264 * 64 * 16) * (p : ℝ) ^ 3 * 64 :=
        mul_le_mul_of_nonneg_left hEH (by positivity)
    _ = 264 * 64 * 16 * 64 * (p : ℝ) ^ 3 := by ring

/-- The endpoint calculus (E1) of Section A (`CapPoint.endpoint_E1_cp`) with constant `C`, at
every capped point, root `v ∈ S` and `i ∈ N_S(v)`:
`|E[σ_vi x_i] - a(-E P_i + (2p-1) E x_i² - 2p E x_i z_i) + (a³/3) E K_i| ≤ C p⁵ a⁵`. -/
def E1Shape (C : ℝ) : Prop :=
  Eventually fun _ _ d p _ => ∀ cp : CapPoint.{u} d p, ∀ v ∈ cp.S, ∀ i ∈ cp.N v,
    |cp.E (fun σ => sgn σ v i * cp.gp σ v i) -
        aOf d p * (-(cp.E fun σ => cp.gp σ v v * cp.gp σ i i) +
          (2 * (p : ℝ) - 1) * (cp.E fun σ => cp.gp σ v i ^ 2) -
          2 * (p : ℝ) * (cp.E fun σ => cp.gp σ v i * cp.gm σ v i)) +
        aOf d p ^ 3 / 3 * (cp.E fun σ => Kpoly p (cp.gp σ v i) (cp.gm σ v i)
          (cp.gp σ v v * cp.gp σ i i) (cp.gm σ v v * cp.gm σ i i))| ≤
      C * (p : ℝ) ^ 5 * aOf d p ^ 5

/-- **TB.E1row⁺** (the first-order endpoint identity (E1′) at root rows, plus branch). Given (E1)
with constant `C ≥ 0`: at every capped point, `w ∈ S`, `i ∈ N_S(w)`,
`|E[σ_wi x_i] - E 𝒟₁x_i| ≤ K p³ a³` with `K = C + C_K/3` (`p⁵a⁵ ≤ p³a³` since `pa ≤ 1`, and
TB.Kmom for the third-order term `(a³/3) E K_i`). -/
theorem row_endpoint_plus_of {C : ℝ} (hC : 0 ≤ C) (hE1 : E1Shape.{u} C) :
    ∃ K : ℝ, 0 ≤ K ∧ Eventually fun _ _ d p _ =>
    ∀ cp : CapPoint.{u} d p, ∀ w ∈ cp.S, ∀ i ∈ cp.N w,
      |cp.E (fun σ => sgn σ w i * cp.gp σ w i) - cp.E (d1x cp.G d p cp.yp cp.ym cp.S w i)| ≤
        K * (p : ℝ) ^ 3 * aOf d p ^ 3 := by
  obtain ⟨Ck, hCk, hKm⟩ := kpoly_moment.{u}
  refine ⟨C + Ck / 3, by positivity, ((hKm.and hE1).and (eventually_base 0)).mono ?_⟩
  rintro c₀ κ₀ d p h ⟨⟨hk, hE⟩, hR, -⟩ cp w hw i hi
  have hE1' := hE cp w hw i hi
  have hK := hk cp w hw i hi
  have ha : 0 < aOf d p := hR.aOf_pos
  have hp := regime_p_pos hR
  -- `p a ≤ 1`
  have hpa2 : ((p : ℝ) * aOf d p) ^ 2 ≤ 1 := by
    have ha2 := SecA.aOf_sq_le hR
    have hq := hR.qOf_pos
    have h8 := regime_p8_le hR
    have hp1 : (1 : ℝ) ≤ p := by linarith [(show (2 : ℝ) ≤ p by exact_mod_cast hR.two_le_p)]
    have hp2 : (p : ℝ) ^ 2 ≤ 4 * qOf d := by
      have : (p : ℝ) ^ 2 ≤ (p : ℝ) ^ 8 := pow_le_pow_right₀ hp1 (by norm_num)
      have hd : (10 : ℝ) ^ 6 ≤ d := hR.ten_pow_six_le_d
      rw [qOf]; linarith
    rw [mul_pow]
    calc (p : ℝ) ^ 2 * aOf d p ^ 2 ≤ (p : ℝ) ^ 2 * (1 / (4 * qOf d)) :=
          mul_le_mul_of_nonneg_left ha2 (by positivity)
      _ ≤ 1 := by rw [mul_one_div, div_le_one (by positivity)]; exact hp2
  have h5 : (p : ℝ) ^ 5 * aOf d p ^ 5 ≤ (p : ℝ) ^ 3 * aOf d p ^ 3 := by
    have e : (p : ℝ) ^ 5 * aOf d p ^ 5 =
        ((p : ℝ) * aOf d p) ^ 2 * ((p : ℝ) ^ 3 * aOf d p ^ 3) := by ring
    rw [e]
    exact mul_le_of_le_one_left (by positivity) hpa2
  have hd1 : cp.E (d1x cp.G d p cp.yp cp.ym cp.S w i) =
      aOf d p * (-(cp.E fun σ => cp.gp σ w w * cp.gp σ i i) +
        (2 * (p : ℝ) - 1) * (cp.E fun σ => cp.gp σ w i ^ 2) -
        2 * (p : ℝ) * (cp.E fun σ => cp.gp σ w i * cp.gm σ w i)) := by
    unfold CapPoint.E
    have e : lawE cp.G p (aOf d p) cp.yp cp.ym cp.S (d1x cp.G d p cp.yp cp.ym cp.S w i) =
        lawE cp.G p (aOf d p) cp.yp cp.ym cp.S (fun σ =>
          -aOf d p * (cp.gp σ w w * cp.gp σ i i) + (2 * (p : ℝ) - 1) * aOf d p *
            cp.gp σ w i ^ 2 - 2 * (p : ℝ) * aOf d p * (cp.gp σ w i * cp.gm σ w i)) :=
      lawE_congr cp.G fun σ _ => by simp only [d1x, CapPoint.gp, CapPoint.gm]; ring
    rw [e, lawE_sub, lawE_add, lawE_const_mul, lawE_const_mul, lawE_const_mul]
    ring
  rw [hd1]
  set T := aOf d p ^ 3 / 3 * (cp.E fun σ => Kpoly p (cp.gp σ w i) (cp.gm σ w i)
    (cp.gp σ w w * cp.gp σ i i) (cp.gm σ w w * cp.gm σ i i)) with hT
  have hTb : |T| ≤ Ck / 3 * ((p : ℝ) ^ 3 * aOf d p ^ 3) := by
    rw [hT, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ aOf d p ^ 3 / 3)]
    calc aOf d p ^ 3 / 3 * |cp.E fun σ => Kpoly p (cp.gp σ w i) (cp.gm σ w i)
          (cp.gp σ w w * cp.gp σ i i) (cp.gm σ w w * cp.gm σ i i)|
        ≤ aOf d p ^ 3 / 3 * (Ck * (p : ℝ) ^ 3) :=
          mul_le_mul_of_nonneg_left hK (by positivity)
      _ = Ck / 3 * ((p : ℝ) ^ 3 * aOf d p ^ 3) := by ring
  have hC5 : C * (p : ℝ) ^ 5 * aOf d p ^ 5 ≤ C * ((p : ℝ) ^ 3 * aOf d p ^ 3) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h5 hC
  have hE1'' := abs_le.mp hE1'
  have hTb' := abs_le.mp hTb
  rw [abs_le]
  constructor <;> nlinarith

section Swap

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem greenP_neg (a : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) (j k : V) :
    greenP G a (-1) y (-σ) S j k = greenP G a 1 y σ S j k ∧
      greenP G a 1 y (-σ) S j k = greenP G a (-1) y σ S j k := by
  unfold greenP
  rw [precN_neg, precN_neg, neg_neg]
  exact ⟨rfl, rfl⟩

/-- Under `σ ↦ -σ` the minus root-row residual at `(y⁺, y⁻)` is minus the plus residual at
`(y⁻, y⁺)`: `𝒟₁z(-σ) = -𝒟₁x'(σ)`. -/
theorem d1z_neg (d p : ℕ) (yp ym : V → ℝ) (S : Finset V) (w i : V) (σ : Config V) :
    d1z G d p yp ym S w i (-σ) = -d1x G d p ym yp S w i σ := by
  unfold d1z d1x
  simp only [(greenP_neg G _ _ σ S _ _).1, (greenP_neg G _ _ σ S _ _).2]
  ring

end Swap

/-- **TB.E1row** (the first-order endpoint identity (E1′) at root rows, both branches). The
minus branch is the plus branch at the swapped point `(y⁻, y⁺)` under `σ ↦ -σ` (`lawE_swap`,
`d1z_neg`). -/
theorem row_endpoint_of {C : ℝ} (hC : 0 ≤ C) (hE1 : E1Shape.{u} C) :
    ∃ K : ℝ, 0 ≤ K ∧ Eventually fun _ _ d p _ =>
    ∀ cp : CapPoint.{u} d p, ∀ w ∈ cp.S, ∀ i ∈ cp.N w,
      |cp.E (fun σ => sgn σ w i * cp.gp σ w i) - cp.E (d1x cp.G d p cp.yp cp.ym cp.S w i)| ≤
          K * (p : ℝ) ^ 3 * aOf d p ^ 3 ∧
        |cp.E (fun σ => sgn σ w i * cp.gm σ w i) - cp.E (d1z cp.G d p cp.yp cp.ym cp.S w i)| ≤
          K * (p : ℝ) ^ 3 * aOf d p ^ 3 := by
  obtain ⟨K, hK, hE⟩ := row_endpoint_plus_of hC hE1
  refine ⟨K, hK, hE.mono ?_⟩
  intro c₀ κ₀ d p h hE cp w hw i hi
  refine ⟨hE cp w hw i hi, ?_⟩
  have h' := hE cp.swap w hw i hi
  have e1 : cp.E (fun σ => sgn σ w i * cp.gm σ w i) =
      -cp.swap.E (fun σ => sgn σ w i * cp.swap.gp σ w i) := by
    refine (lawE_swap cp.G p (aOf d p) cp.yp cp.ym cp.S _).trans ?_
    rw [neg_eq_neg_one_mul]
    refine Eq.trans ?_ (lawE_const_mul _ (-1) _)
    refine lawE_congr _ fun σ _ => ?_
    simp only [CapPoint.gm, CapPoint.gp, CapPoint.swap, sgn_neg]
    rw [(greenP_neg _ _ _ σ _ w i).1, neg_mul, neg_one_mul]
    rfl
  have e2 : cp.E (d1z cp.G d p cp.yp cp.ym cp.S w i) =
      -cp.swap.E (d1x cp.swap.G d p cp.swap.yp cp.swap.ym cp.swap.S w i) := by
    refine (lawE_swap cp.G p (aOf d p) cp.yp cp.ym cp.S _).trans ?_
    rw [neg_eq_neg_one_mul]
    refine Eq.trans ?_ (lawE_const_mul _ (-1) _)
    refine lawE_congr _ fun σ _ => ?_
    simp only [CapPoint.swap]
    rw [d1z_neg, neg_one_mul]
    rfl
  rw [e1, e2, show ∀ x y : ℝ, -x - -y = -(x - y) from fun x y => by ring, abs_neg]
  exact h'

section RE

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem CapPt.Zw_ne_zero {d p : ℕ} {S : Finset V} {lam : ℝ} {yp ym : V → ℝ}
    (hR : TRegime d p) (hC : CapPt G d p S lam yp ym) : Zw G p (aOf d p) yp ym S ≠ 0 := by
  have hs := hR.sOf_pos
  have hsub : ∀ y : V → ℝ, InCube (lam * sOf d p) y → InCube (sOf d p) y := fun y hy k =>
    ⟨(hy k).1, le_trans (hy k).2 (by nlinarith [hC.lam_le_one, hC.lam_nonneg])⟩
  exact (hC.pos yp ym (hsub yp hC.hyp) (hsub ym hC.hym)).ne'

/-- The root equations in mean: `D⁺_w m⁺ + a Σ_N E[σ_wi x_i] = 1` and
`D⁻_w m⁻ - a Σ_N E[σ_wi z_i] = 1`. -/
theorem root_row_mean {d p : ℕ} {S : Finset V} {lam : ℝ} {yp ym : V → ℝ} (hR : TRegime d p)
    (hC : CapPt G d p S lam yp ym) {w : V} (hw : w ∈ S) :
    diagD G (aOf d p) yp S w * meanPlus G d p yp ym S w +
        aOf d p * ∑ i ∈ nbhd G S w,
          lawE G p (aOf d p) yp ym S (fun σ => sgn σ w i * greenP G (aOf d p) 1 yp σ S w i) = 1 ∧
      diagD G (aOf d p) ym S w * meanMinus G d p yp ym S w -
        aOf d p * ∑ i ∈ nbhd G S w,
          lawE G p (aOf d p) yp ym S
            (fun σ => sgn σ w i * greenP G (aOf d p) (-1) ym σ S w i) = 1 := by
  have hZ := CapPt.Zw_ne_zero G hR hC
  constructor
  · have h := lawE_congr G (p := p) (a := aOf d p) (yp := yp) (ym := ym) (S := S)
      (f := fun σ => diagD G (aOf d p) yp S w * hN G (aOf d p) 1 yp σ S w +
        aOf d p * ∑ i ∈ nbhd G S w, sgn σ w i * greenP G (aOf d p) 1 yp σ S w i)
      (g := fun _ => 1) fun σ hσ => by
        have := root_row_identity G (posDef_of_wt_ne_zero G hσ).1 hw
        linarith
    rw [lawE_const G hZ, lawE_add, lawE_const_mul, lawE_const_mul, lawE_sum] at h
    exact h
  · have h := lawE_congr G (p := p) (a := aOf d p) (yp := yp) (ym := ym) (S := S)
      (f := fun σ => diagD G (aOf d p) ym S w * hN G (aOf d p) (-1) ym σ S w -
        aOf d p * ∑ i ∈ nbhd G S w, sgn σ w i * greenP G (aOf d p) (-1) ym σ S w i)
      (g := fun _ => 1) fun σ hσ => by
        have := root_row_identity G (posDef_of_wt_ne_zero G hσ).2 hw
        linarith
    rw [lawE_const G hZ, lawE_sub, lawE_const_mul, lawE_const_mul, lawE_sum] at h
    exact h

/-- `|N_S(w)| ≤ d`. -/
theorem card_nbhd_le_d {d : ℕ} (hdeg : ∀ v, G.degree v ≤ d) (S : Finset V) (w : V) :
    ((nbhd G S w).card : ℝ) ≤ d := by
  have h1 : nbhd G S w ⊆ G.neighborFinset w := fun i hi => by
    simp only [nbhd, Finset.mem_filter] at hi
    simpa using hi.2
  have h2 := Finset.card_le_card h1
  rw [SimpleGraph.card_neighborFinset_eq_degree] at h2
  exact_mod_cast h2.trans (hdeg w)

/-- `a² ≤ 1/(4q)` and `a⁴ d ≤ 1/(4d)`. -/
theorem regime_a4_mul_d_le {d p : ℕ} (hR : TRegime d p) :
    aOf d p ^ 4 * d ≤ 1 / (4 * (d : ℝ)) := by
  have hq := hR.qOf_pos
  have hd : (10 : ℝ) ^ 6 ≤ d := hR.ten_pow_six_le_d
  have ha2 : aOf d p ^ 2 = 1 / RsqOf d p := hR.aOf_sq
  have hR2 : 4 * qOf d ≤ RsqOf d p := by rw [RsqOf]; linarith [hR.ΔOf_pos]
  have hqd : (d : ℝ) = qOf d + 1 := by rw [qOf]; ring
  have ha2' : aOf d p ^ 2 ≤ 1 / (4 * qOf d) := by
    rw [ha2]; exact one_div_le_one_div_of_le (by positivity) hR2
  have ha0 : 0 ≤ aOf d p ^ 2 := sq_nonneg _
  have h4 : aOf d p ^ 4 ≤ (1 / (4 * qOf d)) ^ 2 := by
    rw [show aOf d p ^ 4 = (aOf d p ^ 2) ^ 2 by ring]
    exact pow_le_pow_left₀ ha0 ha2' 2
  rw [div_pow, one_pow] at h4
  rw [le_div_iff₀ (by positivity)]
  have : aOf d p ^ 4 * d * (4 * d) ≤ 1 / (4 * qOf d) ^ 2 * d * (4 * d) := by
    have := mul_le_mul_of_nonneg_right h4 (by positivity : (0 : ℝ) ≤ d * (4 * d))
    linarith
  refine le_trans this ?_
  rw [hqd, div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_one (by positivity)]
  nlinarith

/-- **TB.RE, pointwise.** The two branch identities with their residuals, at a point of the capped
family: `(2p-1)a²S⁺ - 2pa²T - B⁺ = -a Σ_N R⁺_i` and `(2p-1)a²S⁻ - 2pa²T - B⁻ = a Σ_N R⁻_i`. -/
theorem row_eq_exact {d p : ℕ} {S : Finset V} {lam : ℝ} {yp ym : V → ℝ} (hR : TRegime d p)
    (hC : CapPt G d p S lam yp ym) {w : V} (hw : w ∈ S) :
    (2 * p - 1) * aOf d p ^ 2 * rowSP G d p yp ym S w -
          2 * p * aOf d p ^ 2 * rowT G d p yp ym S w - rowBP G d p yp ym S w =
        -(aOf d p * ∑ i ∈ nbhd G S w,
          (lawE G p (aOf d p) yp ym S (fun σ => sgn σ w i * greenP G (aOf d p) 1 yp σ S w i) -
            lawE G p (aOf d p) yp ym S (d1x G d p yp ym S w i))) ∧
      (2 * p - 1) * aOf d p ^ 2 * rowSM G d p yp ym S w -
          2 * p * aOf d p ^ 2 * rowT G d p yp ym S w - rowBM G d p yp ym S w =
        aOf d p * ∑ i ∈ nbhd G S w,
          (lawE G p (aOf d p) yp ym S
              (fun σ => sgn σ w i * greenP G (aOf d p) (-1) ym σ S w i) -
            lawE G p (aOf d p) yp ym S (d1z G d p yp ym S w i)) := by
  obtain ⟨hrp, hrm⟩ := root_row_mean G hR hC hw
  have ex : ∀ i, lawE G p (aOf d p) yp ym S (d1x G d p yp ym S w i) =
      -aOf d p * lawE G p (aOf d p) yp ym S
          (fun σ => greenP G (aOf d p) 1 yp σ S w w * greenP G (aOf d p) 1 yp σ S i i) +
        (2 * p - 1) * aOf d p *
          lawE G p (aOf d p) yp ym S (fun σ => greenP G (aOf d p) 1 yp σ S w i ^ 2) -
        2 * p * aOf d p * lawE G p (aOf d p) yp ym S
          (fun σ => greenP G (aOf d p) 1 yp σ S w i * greenP G (aOf d p) (-1) ym σ S w i) := by
    intro i
    rw [← lawE_const_mul, ← lawE_const_mul, ← lawE_const_mul, ← lawE_add, ← lawE_sub]
    exact lawE_congr G fun σ _ => by simp only [d1x]; ring
  have ez : ∀ i, lawE G p (aOf d p) yp ym S (d1z G d p yp ym S w i) =
      aOf d p * lawE G p (aOf d p) yp ym S
          (fun σ => greenP G (aOf d p) (-1) ym σ S w w * greenP G (aOf d p) (-1) ym σ S i i) -
        (2 * p - 1) * aOf d p *
          lawE G p (aOf d p) yp ym S (fun σ => greenP G (aOf d p) (-1) ym σ S w i ^ 2) +
        2 * p * aOf d p * lawE G p (aOf d p) yp ym S
          (fun σ => greenP G (aOf d p) 1 yp σ S w i * greenP G (aOf d p) (-1) ym σ S w i) := by
    intro i
    rw [← lawE_const_mul, ← lawE_const_mul, ← lawE_const_mul, ← lawE_sub, ← lawE_add]
    exact lawE_congr G fun σ _ => by simp only [d1z]; ring
  have sx : ∑ i ∈ nbhd G S w, lawE G p (aOf d p) yp ym S (d1x G d p yp ym S w i) =
      -aOf d p * ∑ i ∈ nbhd G S w, lawE G p (aOf d p) yp ym S
          (fun σ => greenP G (aOf d p) 1 yp σ S w w * greenP G (aOf d p) 1 yp σ S i i) +
        (2 * p - 1) * aOf d p * rowSP G d p yp ym S w -
        2 * p * aOf d p * rowT G d p yp ym S w := by
    rw [Finset.sum_congr rfl fun i _ => ex i, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
    rfl
  have sz : ∑ i ∈ nbhd G S w, lawE G p (aOf d p) yp ym S (d1z G d p yp ym S w i) =
      aOf d p * ∑ i ∈ nbhd G S w, lawE G p (aOf d p) yp ym S
          (fun σ => greenP G (aOf d p) (-1) ym σ S w w * greenP G (aOf d p) (-1) ym σ S i i) -
        (2 * p - 1) * aOf d p * rowSM G d p yp ym S w +
        2 * p * aOf d p * rowT G d p yp ym S w := by
    rw [Finset.sum_congr rfl fun i _ => ez i, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
    rfl
  constructor
  · rw [Finset.sum_sub_distrib, sx, rowBP]
    linear_combination hrp
  · rw [Finset.sum_sub_distrib, sz, rowBM]
    linear_combination hrm

end RE

/-- **TB.RE.** `|(2p-1)a²S^±_w - 2pa²T_w - B^±_w| ≤ K₃ p³/d` at every point of the capped family
and every `w ∈ S` (`K₃` absolute; from TB.E1row and TB.root). -/
theorem row_eq_of {C : ℝ} (hC : 0 ≤ C) (hE1 : E1Shape.{u} C) :
    ∃ K₃ : ℝ, 0 ≤ K₃ ∧ Eventually fun _ _ d p _ =>
    ∀ cp : CapPoint.{u} d p, ∀ w ∈ cp.S,
      |(2 * p - 1) * aOf d p ^ 2 * rowSP cp.G d p cp.yp cp.ym cp.S w -
          2 * p * aOf d p ^ 2 * rowT cp.G d p cp.yp cp.ym cp.S w -
          rowBP cp.G d p cp.yp cp.ym cp.S w| ≤ K₃ * (p : ℝ) ^ 3 / d ∧
      |(2 * p - 1) * aOf d p ^ 2 * rowSM cp.G d p cp.yp cp.ym cp.S w -
          2 * p * aOf d p ^ 2 * rowT cp.G d p cp.yp cp.ym cp.S w -
          rowBM cp.G d p cp.yp cp.ym cp.S w| ≤ K₃ * (p : ℝ) ^ 3 / d := by
  obtain ⟨K, hK, hE⟩ := row_endpoint_of hC hE1
  refine ⟨K, hK, (hE.and (eventually_base 0)).mono ?_⟩
  rintro c₀ κ₀ d p h ⟨hE1, hR, -⟩ cp w hw
  have hC : CapPt cp.G d p cp.S cp.lam cp.yp cp.ym := ⟨cp.ctx, cp.hyp, cp.hym⟩
  set G := cp.G
  set S := cp.S
  set yp := cp.yp
  set ym := cp.ym
  obtain ⟨e1, e2⟩ := row_eq_exact G hR hC hw
  have ha : 0 < aOf d p := hR.aOf_pos
  have hd0 : (0 : ℝ) < d := by have := hR.ten_pow_six_le_d; linarith
  have hcard := card_nbhd_le_d G hC.deg S w
  have ha4 := regime_a4_mul_d_le hR
  have hbound : ∀ R : cp.V → ℝ, (∀ i ∈ nbhd G S w, |R i| ≤ K * (p : ℝ) ^ 3 * aOf d p ^ 3) →
      |aOf d p * ∑ i ∈ nbhd G S w, R i| ≤ K * (p : ℝ) ^ 3 / d := by
    intro R hRb
    rw [abs_mul, abs_of_pos ha]
    have h1 : |∑ i ∈ nbhd G S w, R i| ≤ (nbhd G S w).card * (K * (p : ℝ) ^ 3 * aOf d p ^ 3) := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      have := Finset.sum_le_sum hRb
      simpa using this
    have hKp : 0 ≤ K * (p : ℝ) ^ 3 := by positivity
    calc aOf d p * |∑ i ∈ nbhd G S w, R i|
        ≤ aOf d p * ((nbhd G S w).card * (K * (p : ℝ) ^ 3 * aOf d p ^ 3)) :=
          mul_le_mul_of_nonneg_left h1 ha.le
      _ ≤ aOf d p * (d * (K * (p : ℝ) ^ 3 * aOf d p ^ 3)) := by
          apply mul_le_mul_of_nonneg_left _ ha.le
          exact mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = K * (p : ℝ) ^ 3 * (aOf d p ^ 4 * d) := by ring
      _ ≤ K * (p : ℝ) ^ 3 * (1 / (4 * d)) := mul_le_mul_of_nonneg_left ha4 hKp
      _ ≤ K * (p : ℝ) ^ 3 / d := by
          rw [mul_one_div]
          exact div_le_div_of_nonneg_left hKp hd0 (by linarith)
  constructor
  · rw [e1, abs_neg]
    exact hbound _ fun i hi => (hE1 cp w hw i hi).1
  · rw [e2]
    exact hbound _ fun i hi => (hE1 cp w hw i hi).2

/-! ### The bound on `B^±` (G4) -/

section Bbound

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem cRoot_add_sq {x : ℝ} (hx : 0 ≤ x) : cRoot x + cRoot x ^ 2 = x := by
  have h := Real.sq_sqrt (show 0 ≤ 1 + 4 * x by linarith)
  rw [cRoot]
  nlinarith

/-- `((p r - 2)/(p - 2))² ≤ 1 + 3ε` in the regime. -/
theorem regime_m2_le {d p : ℕ} (hR : TRegime d p) :
    (((p : ℝ) * rOf d p - 2) / ((p : ℝ) - 2)) ^ 2 ≤ 1 + 3 * epsP d p := by
  have hp : (10 : ℝ) ^ 6 ≤ p := by exact_mod_cast hR.hp
  have hε0 := regime_eps_nonneg hR
  have hε1 : epsP d p ≤ 1 / (p : ℝ) ^ 3 := regime_eps_le hR
  have hε2 : epsP d p ≤ 1 / 10 := by
    refine le_trans hε1 ?_
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [pow_le_pow_left₀ (by norm_num) hp 3]
  have hr : rOf d p = 1 + epsP d p := by rw [epsP]; ring
  have hp2 : 0 < (p : ℝ) - 2 := by linarith
  have e : ((p : ℝ) * rOf d p - 2) / ((p : ℝ) - 2) = 1 + (p : ℝ) * epsP d p / ((p : ℝ) - 2) := by
    rw [hr]; field_simp; ring
  have hq : (p : ℝ) * epsP d p / ((p : ℝ) - 2) ≤ 101 / 100 * epsP d p := by
    rw [div_le_iff₀ hp2]; nlinarith
  have hq0 : 0 ≤ (p : ℝ) * epsP d p / ((p : ℝ) - 2) := by positivity
  rw [e]
  nlinarith

/-- **TB.B (G4).** At a point of the capped family, for `ρ ≥ 0` with `1 - E h^±_w ≤ ρ`:
`B^±_w ≤ 2.01 ρ + 1.04/d + 3.03 ε`. -/
theorem rowB_le {d p : ℕ} {S : Finset V} {lam : ℝ} {yp ym : V → ℝ} (hR : TRegime d p)
    (hC : CapPt G d p S lam yp ym) {w : V} (hw : w ∈ S) {ρ : ℝ} (hρ0 : 0 ≤ ρ) :
    (1 - meanPlus G d p yp ym S w ≤ ρ →
      rowBP G d p yp ym S w ≤ 201 / 100 * ρ + 104 / (100 * d) + 303 / 100 * epsP d p) ∧
    (1 - meanMinus G d p yp ym S w ≤ ρ →
      rowBM G d p yp ym S w ≤ 201 / 100 * ρ + 104 / (100 * d) + 303 / 100 * epsP d p) := by
  have hp4 : 2 + 2 ≤ p := le_trans (by norm_num) hR.hp
  have hs := hR.sOf_pos
  have hd0 : (0 : ℝ) < d := by have := hR.ten_pow_six_le_d; linarith
  have hdk := hR.d_mul_kappa_le
  have hr1 := hR.rOf_le
  have hm2 := regime_m2_le hR
  have hε0 := regime_eps_nonneg hR
  have hcard := card_nbhd_le_d G hC.deg S w
  set M₂ := (((p : ℝ) * rOf d p - 2) / ((p : ℝ) - 2)) ^ 2
  set a := aOf d p
  set s := sOf d p
  -- a branch-generic argument
  have key : ∀ (τ : ℝ) (y : V → ℝ), (∀ k, 0 ≤ y k ∧ y k ≤ s) →
      (∀ k ∈ S, lawE G p a yp ym S (fun σ => hN G a τ y σ S k ^ 2) ≤ M₂) →
      lawE G p a yp ym S (fun σ => hN G a τ y σ S w) ≤ rOf d p →
      1 - lawE G p a yp ym S (fun σ => hN G a τ y σ S w) ≤ ρ →
      1 - diagD G a y S w * lawE G p a yp ym S (fun σ => hN G a τ y σ S w) +
          a ^ 2 * ∑ i ∈ nbhd G S w, lawE G p a yp ym S (fun σ =>
            greenP G a τ y σ S w w * greenP G a τ y σ S i i) ≤
        201 / 100 * ρ + 104 / (100 * d) + 303 / 100 * epsP d p := by
    intro τ y hy hmom hcap hρ
    set m := lawE G p a yp ym S (fun σ => hN G a τ y σ S w)
    set L := ∑ i ∈ nbhd G S w, a ^ 2 * y w * y i
    set C := ∑ i ∈ nbhd G S w, cEdge a y w i ^ 2
    have hxi : ∀ i, 0 ≤ a ^ 2 * y w * y i := fun i =>
      mul_nonneg (mul_nonneg (sq_nonneg _) (hy w).1) (hy i).1
    have hD : diagD G a y S w = 1 + L - C := by
      rw [diagD]
      have : ∀ i, cEdge a y w i = a ^ 2 * y w * y i - cEdge a y w i ^ 2 := fun i => by
        have := cRoot_add_sq (hxi i); rw [cEdge]; linarith
      rw [Finset.sum_congr rfl fun i _ => this i, Finset.sum_sub_distrib]
      ring
    have hL0 : 0 ≤ L := Finset.sum_nonneg fun i _ => hxi i
    have hL : L ≤ 101 / 100 := by
      have : L ≤ ∑ i ∈ nbhd G S w, a ^ 2 * s * s := Finset.sum_le_sum fun i _ => by
        apply mul_le_mul (mul_le_mul_of_nonneg_left (hy w).2 (sq_nonneg _)) (hy i).2 (hy i).1
        positivity
      rw [Finset.sum_const, nsmul_eq_mul] at this
      nlinarith
    have hC0 : 0 ≤ C := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hCb : C ≤ 10201 / (10000 * d) := by
      have : C ≤ ∑ i ∈ nbhd G S w, (a ^ 2 * s * s) ^ 2 := Finset.sum_le_sum fun i _ => by
        have hc0 := FloorIns.cRoot_nonneg (hxi i)
        have hc1 := FloorIns.cRoot_le (hxi i)
        have hx2 : a ^ 2 * y w * y i ≤ a ^ 2 * s * s :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hy w).2 (sq_nonneg _)) (hy i).2 (hy i).1
            (by positivity)
        rw [cEdge]
        exact pow_le_pow_left₀ hc0 (hc1.trans hx2) 2
      rw [Finset.sum_const, nsmul_eq_mul] at this
      rw [le_div_iff₀ (by positivity)]
      have hk0 : 0 ≤ a ^ 2 * s * s := by positivity
      have e : (d : ℝ) * (a ^ 2 * s ^ 2) = d * (a ^ 2 * s * s) := by ring
      rw [e] at hdk
      have : C * (10000 * d) ≤ (d : ℝ) * (a ^ 2 * s * s) ^ 2 * (10000 * d) := by
        have h2 : C ≤ (d : ℝ) * (a ^ 2 * s * s) ^ 2 :=
          le_trans this (mul_le_mul_of_nonneg_right hcard (sq_nonneg _))
        exact mul_le_mul_of_nonneg_right h2 (by positivity)
      have hk2 : ((d : ℝ) * (a ^ 2 * s * s)) ^ 2 ≤ (101 / 100) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hdk 2
      have e2 : (d : ℝ) * (a ^ 2 * s * s) ^ 2 * (10000 * d) =
          10000 * ((d : ℝ) * (a ^ 2 * s * s)) ^ 2 := by ring
      rw [e2] at this
      linarith
    have hGG : ∀ i ∈ nbhd G S w, lawE G p a yp ym S (fun σ =>
        greenP G a τ y σ S w w * greenP G a τ y σ S i i) ≤ y w * y i * M₂ := by
      intro i hi
      have hiS : i ∈ S := (Finset.mem_filter.mp hi).1
      have e : lawE G p a yp ym S (fun σ => greenP G a τ y σ S w w * greenP G a τ y σ S i i) =
          y w * y i * lawE G p a yp ym S (fun σ => hN G a τ y σ S w * hN G a τ y σ S i) := by
        rw [← lawE_const_mul]
        exact lawE_congr G fun σ _ => by
          rw [greenP_diag G σ S (hy w).1, greenP_diag G σ S (hy i).1]; ring
      rw [e]
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (hy w).1 (hy i).1)
      have hle : lawE G p a yp ym S (fun σ => hN G a τ y σ S w * hN G a τ y σ S i) ≤
          lawE G p a yp ym S (fun σ => (1 / 2) * (hN G a τ y σ S w ^ 2) +
            (1 / 2) * hN G a τ y σ S i ^ 2) :=
        lawE_mono G fun σ _ => by nlinarith [sq_nonneg (hN G a τ y σ S w - hN G a τ y σ S i)]
      rw [lawE_add, lawE_const_mul, lawE_const_mul] at hle
      linarith [hmom w hw, hmom i hiS]
    have hsumGG : a ^ 2 * ∑ i ∈ nbhd G S w, lawE G p a yp ym S (fun σ =>
        greenP G a τ y σ S w w * greenP G a τ y σ S i i) ≤ L * M₂ := by
      rw [Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_le_sum fun i hi => by
        have := mul_le_mul_of_nonneg_left (hGG i hi) (sq_nonneg a)
        linarith
    rw [hD]
    have hM2 : M₂ - 1 ≤ 3 * epsP d p := by linarith
    have h1 : 1 - (1 + L - C) * m + L * M₂ ≤ ρ + C * rOf d p + L * (M₂ - 1) + L * ρ := by
      nlinarith [mul_nonneg hC0 (sub_nonneg.mpr hcap),
        mul_nonneg hL0 (by linarith : 0 ≤ ρ - (1 - m))]
    have h2 : C * rOf d p ≤ 104 / (100 * d) := by
      calc C * rOf d p ≤ 10201 / (10000 * d) * (101 / 100) :=
            mul_le_mul hCb hr1 (by linarith [hR.one_lt_rOf]) (by positivity)
        _ ≤ 104 / (100 * d) := by
            rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
            nlinarith
    have h3 : L * (M₂ - 1) ≤ 101 / 100 * (3 * epsP d p) := by
      rcases le_or_gt (M₂ - 1) 0 with hneg | hpos
      · nlinarith
      · exact mul_le_mul hL hM2 hpos.le (by norm_num)
    have h4 : L * ρ ≤ 101 / 100 * ρ := mul_le_mul_of_nonneg_right hL hρ0
    linarith
  have hyp : ∀ k, 0 ≤ yp k ∧ yp k ≤ s := fun k =>
    ⟨(hC.hyp k).1, le_trans (hC.hyp k).2 (by nlinarith [hC.lam_le_one, hC.lam_nonneg])⟩
  have hym : ∀ k, 0 ≤ ym k ∧ ym k ≤ s := fun k =>
    ⟨(hC.hym k).1, le_trans (hC.hym k).2 (by nlinarith [hC.lam_le_one, hC.lam_nonneg])⟩
  have hmomP : ∀ k ∈ S, lawE G p a yp ym S (fun σ => hN G a 1 yp σ S k ^ 2) ≤ M₂ := fun k hk =>
    (source_moments G hR hC.toCapCtx hC.hyp hC.hym hk (k := 2) (by norm_num) hp4).1
  have hmomM : ∀ k ∈ S, lawE G p a yp ym S (fun σ => hN G a (-1) ym σ S k ^ 2) ≤ M₂ :=
    fun k hk => (source_moments G hR hC.toCapCtx hC.hyp hC.hym hk (k := 2) (by norm_num) hp4).2
  obtain ⟨hcP, hcM⟩ := hC.cap yp ym hC.hyp hC.hym w hw
  exact ⟨fun hρ => key 1 yp hyp hmomP hcP hρ, fun hρ => key (-1) ym hym hmomM hcM hρ⟩

end Bbound

/-! ### DR1 -/

section DR1

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- `Σ_N E(x - z)² = S⁺ + S⁻ - 2T` and `2T ≤ S⁺ + S⁻`. -/
theorem rowDiff_eq {d p : ℕ} (yp ym : V → ℝ) (S : Finset V) (w : V) :
    rowDiff G d p yp ym S w =
      rowSP G d p yp ym S w + rowSM G d p yp ym S w - 2 * rowT G d p yp ym S w := by
  simp only [rowDiff, rowSP, rowSM, rowT, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← lawE_const_mul, ← lawE_add, ← lawE_sub]
  exact lawE_congr G fun σ _ => by ring

theorem two_rowT_le {d p : ℕ} (yp ym : V → ℝ) (S : Finset V) (w : V) :
    2 * rowT G d p yp ym S w ≤ rowSP G d p yp ym S w + rowSM G d p yp ym S w := by
  simp only [rowSP, rowSM, rowT, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← lawE_const_mul, ← lawE_add]
  exact lawE_mono G fun σ _ => by
    nlinarith [sq_nonneg (greenP G (aOf d p) 1 yp σ S w i - greenP G (aOf d p) (-1) ym σ S w i)]

theorem rowDiff_nonneg {d p : ℕ} (yp ym : V → ℝ) (S : Finset V) (w : V) :
    0 ≤ rowDiff G d p yp ym S w :=
  Finset.sum_nonneg fun i _ => lawE_nonneg G fun σ _ => sq_nonneg _

/-- `δ̄ ≥ ε`, `δ̄ ≥ p⁴/d`. -/
theorem le_dbar {d p : ℕ} (hR : TRegime d p) :
    epsP d p ≤ dbar d p ∧ (p : ℝ) ^ 4 / d ≤ dbar d p := by
  have h1 : 0 ≤ ((p : ℝ) / d) ^ ((1 : ℝ) / 3) := Real.rpow_nonneg (by positivity) _
  have h2 : 0 ≤ (p : ℝ) ^ 4 / d := by positivity
  have h3 := regime_eps_nonneg hR
  rw [dbar]
  constructor <;> linarith

/-- **TB.DR1, pointwise.** At a point of the capped family, if `1 - m^±_w ≤ δ`, `a² S^±_w ≤ δ`
and the residuals satisfy `|E3^±| ≤ e₃`, then
`(2p-1) a² Σ_N E(x - z)² ≤ 2(2.01 δ + 1.04/d + 3.03 ε) + 2 e₃ + 2δ`. -/
theorem dr1_pt {d p : ℕ} {S : Finset V} {lam : ℝ} {yp ym : V → ℝ} (hR : TRegime d p)
    (hC : CapPt G d p S lam yp ym) {w : V} (hw : w ∈ S) {δ e₃ : ℝ} (hδ : 0 ≤ δ)
    (hmP : 1 - meanPlus G d p yp ym S w ≤ δ) (hmM : 1 - meanMinus G d p yp ym S w ≤ δ)
    (hSP : aOf d p ^ 2 * rowSP G d p yp ym S w ≤ δ)
    (hSM : aOf d p ^ 2 * rowSM G d p yp ym S w ≤ δ)
    (hEP : |(2 * p - 1) * aOf d p ^ 2 * rowSP G d p yp ym S w -
          2 * p * aOf d p ^ 2 * rowT G d p yp ym S w - rowBP G d p yp ym S w| ≤ e₃)
    (hEM : |(2 * p - 1) * aOf d p ^ 2 * rowSM G d p yp ym S w -
          2 * p * aOf d p ^ 2 * rowT G d p yp ym S w - rowBM G d p yp ym S w| ≤ e₃) :
    (2 * p - 1) * (aOf d p ^ 2 * rowDiff G d p yp ym S w) ≤
      2 * (201 / 100 * δ + 104 / (100 * d) + 303 / 100 * epsP d p) + 2 * e₃ + 2 * δ := by
  obtain ⟨hBP, -⟩ := rowB_le G hR hC hw hδ
  obtain ⟨-, hBM⟩ := rowB_le G hR hC hw hδ
  have b1 := hBP hmP
  have b2 := hBM hmM
  have hT := two_rowT_le G (d := d) (p := p) yp ym S w
  have ha2 : 0 ≤ aOf d p ^ 2 := sq_nonneg _
  have hT' : 2 * aOf d p ^ 2 * rowT G d p yp ym S w ≤
      aOf d p ^ 2 * rowSP G d p yp ym S w + aOf d p ^ 2 * rowSM G d p yp ym S w := by
    nlinarith
  rw [rowDiff_eq]
  have e1 := (abs_le.mp hEP).2
  have e2 := (abs_le.mp hEM).2
  nlinarith

end DR1

/-- **TB.DR1.** Given (C2) with constant `K_δ ≥ 0`: there is an absolute `K` (namely
`6.02 K_δ + 8.14 + 2K₃`) such that eventually, at every point of the capped family and every
`w ∈ S`, `a² Σ_{i ∈ N_S(w)} E(G⁺_wi - G⁻_wi)² ≤ K δ̄ / p`. -/
theorem dr1_of_c2 {C Kδ : ℝ} (hC : 0 ≤ C) (hE1 : E1Shape.{u} C) (hKδ : 0 ≤ Kδ)
    (hC2 : C2RowShape.{u} Kδ) :
    ∃ K : ℝ, 0 ≤ K ∧ Eventually fun _ _ d p _ => ∀ cp : CapPoint.{u} d p, ∀ w ∈ cp.S,
      aOf d p ^ 2 * rowDiff cp.G d p cp.yp cp.ym cp.S w ≤ K * dbar d p / p := by
  obtain ⟨K₃, hK₃, hRE⟩ := row_eq_of hC hE1
  refine ⟨602 / 100 * Kδ + 814 / 100 + 2 * K₃, by positivity,
    ((hRE.and hC2).and (eventually_base 0)).mono ?_⟩
  rintro c₀ κ₀ d p h ⟨⟨hre, hc2⟩, hR, -⟩ cp w hw
  have hC : CapPt cp.G d p cp.S cp.lam cp.yp cp.ym := ⟨cp.ctx, cp.hyp, cp.hym⟩
  obtain ⟨hmP, hmM, hSP, hSM⟩ := hc2 cp w hw
  obtain ⟨hEP, hEM⟩ := hre cp w hw
  have hdb0 : 0 ≤ dbar d p := le_trans (regime_eps_nonneg hR) (le_dbar hR).1
  have hδ : 0 ≤ Kδ * dbar d p := mul_nonneg hKδ hdb0
  have key := dr1_pt cp.G hR hC hw hδ hmP hmM hSP hSM hEP hEM
  have hp := regime_p_pos hR
  have hp1 : (1 : ℝ) ≤ p := by have := hR.two_le_p; exact_mod_cast le_trans (by norm_num) this
  have hd0 : (0 : ℝ) < d := by have := hR.ten_pow_six_le_d; linarith
  obtain ⟨hεd, hpd⟩ := le_dbar hR
  have h1d : 1 / (d : ℝ) ≤ dbar d p := by
    refine le_trans ?_ hpd
    exact div_le_div_of_nonneg_right (one_le_pow₀ hp1) hd0.le
  have hp3 : (p : ℝ) ^ 3 / d ≤ dbar d p := by
    refine le_trans ?_ hpd
    exact div_le_div_of_nonneg_right (pow_le_pow_right₀ hp1 (by norm_num)) hd0.le
  have hX : 2 * (201 / 100 * (Kδ * dbar d p) + 104 / (100 * d) + 303 / 100 * epsP d p) +
      2 * (K₃ * (p : ℝ) ^ 3 / d) + 2 * (Kδ * dbar d p) ≤
      (602 / 100 * Kδ + 814 / 100 + 2 * K₃) * dbar d p := by
    have e1 : 104 / (100 * (d : ℝ)) = 104 / 100 * (1 / d) := by field_simp
    have e2 : K₃ * (p : ℝ) ^ 3 / d = K₃ * ((p : ℝ) ^ 3 / d) := by ring
    rw [e1, e2]
    nlinarith [mul_le_mul_of_nonneg_left hp3 hK₃]
  have hD0 := rowDiff_nonneg cp.G (d := d) (p := p) cp.yp cp.ym cp.S w
  have hl : (p : ℝ) * (aOf d p ^ 2 * rowDiff cp.G d p cp.yp cp.ym cp.S w) ≤
      (2 * p - 1) * (aOf d p ^ 2 * rowDiff cp.G d p cp.yp cp.ym cp.S w) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  rw [le_div_iff₀ hp]
  nlinarith

end BiluLinial.Tight.SecB
