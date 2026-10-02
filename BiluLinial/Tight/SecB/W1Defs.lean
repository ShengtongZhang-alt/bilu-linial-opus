/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecB.WeakBase

/-!
# The random-profile weak loop (W1): definitions and exact algebra

Sub-nodes of TB.W1 of `docs/tight/BP_SECB.md` (source Lemma "Random-profile weak loop",
lines 721–911; AUDIT-B §2.4 with fixes B-2, B-3; `docs/tight/DR1_CHECK.md` §3, W1′). This file
holds the definitions and TB.W1alg; TB.W1sec and TB.W1mask are proved in `SecB/W1Mom.lean`,
TB.W1fib is in `SecB/W1Fib.lean`, the assembly TB.W1ibp in `SecB/W1.lean`, and the parent
`weak_loop_of` in `SecB/Weak.lean`.

Notation at a contact (`Tight/Contact/Defs.lean`): `X_± = (P^± + hI)⁻¹`, `u = 1_N/√d`,
`U = X_ε D_f X_ν`, `F_ji = (X_ε)_ii U_ji - (X_ε)_ji U_ii` (`maskF`), `K = X_ε ∘ X_ν/4`,
`M = diag((X_ε)_ii (X_ν)_ii/4)`, `b = 4 T M u`, `T = a² A_H`. The four configurations of `in_W1`
all have `ν = +`:

| # | `ε` | `H` | `X_ε` | `X_ν` | `f` | target `T_k` |
|---|---|---|---|---|---|---|
| 1 | `+` | `Ω₊` | `X₊` | `X₊` | `u` | `q₊ - ζ - t₊` |
| 2 | `+` | `Ω₊` | `X₊` | `X₊` | `b₊` | `ζ - z₊ - α` |
| 3 | `-` | `Ω₋` | `X₋` | `X₊` | `u` | `q₋ + ζ₋ - t₋` |
| 4 | `-` | `Ω₋` | `X₋` | `X₊` | `b₋` | `ζ₋ + z₋ - β` |

Write `wEdge = Σ_{i∈N} Σ_{j∼i} u_i E[σ_ij H F_ji]` and `wMain = Σ_{i∈N} Σ_{j∼i} u_i E[H (X_ε)_ii
(X_ν)_ii U_jj]` (`j ∼ i` means `j ∈ N_S(i)`).

* **TB.W1alg** (`weak_config_ids`, exact): TB.W2 multiplied by `H u_i` and summed over `i ∈ N`
  gives `4E[H uᵀKf] - 4E[H uᵀMf] = -εa·wEdge`; and `a²·wMain = Σ_j E[H b_j U_jj] = 4E[H fᵀKb]`
  (`U_jj = 4(Kf)_j`, `K` symmetric). Hence `4 T_k = -ε (a·wEdge + a²·wMain)`
  (`weak_targets`).
* **TB.W1fib** (`weak_fibre_of`, `SecB/W1Fib.lean`; open below: `weak_fibre_edge`): the
  first-order endpoint identity (E1′) on every
  edge fibre `ij`, `i ∈ N`, `j ∼ i`: `E[σ_ij Ψ] = E[∂Ψ + Ψ ∂ log W] + R_ij` for `Ψ = H F_ji`, with
  the exact derivatives `∂ log W = 2pa(G⁺_ij - G⁻_ij)` and
  `∂(H F_ji) = ∂H·F_ji - aH(ν (X_ε)_ii (X_ν)_ii U_jj + 2ε (X_ε)_ij F_ji + ν (X_ν)_ij F_ji
  - ν (X_ν)_ii (X_ε)_ij U_ij) + H F_ji(∂f)` (W3 plus the mask derivative `∂_ij b_±` = `dbP`,
  `dbM`). Summed with the weights `a u_i`, the leading term of (W3) is `-a²·wMain`, so
  `|a·wEdge + a²·wMain - a(wScore + wSec + wMask)| ≤ C B₀` where the right side bounds
  `|a Σ u_i R_ij|`. Sketch (source l.840–903; AUDIT-B §2.4): on a regular fibre (endpoint diagonal
  sum `≤ (64pa)⁻¹`) the whole segment `s ∈ [-1, 1]` is positive definite, `G(s) ⪯ 2G(σ)`, weight
  ratios are bounded, and the trapezoid rule `|E_ξ[ξφ] - E_ξ[φ']| ≤ sup|φ'''|/3` applies to
  `φ(s) = W(s)Ψ(s)`; `W⁻¹|∂³(WHF)| ≤ (Ca³D_*^C/(√d h)){p³R³ + p²R + p²R² + p + 1}` with
  `R = |G⁺_ij| + |G⁻_ij|`, and capped moments with (C2) give `E[D_*^C R^k] ≤ C ρ` (`k = 2, 3`),
  `≤ C√ρ` (`k = 1`), `ρ = C(δ̄ + 1/d) ≤ Cp⁻²` (B-3: no GR1), so the coefficient is `≤ Cp` and the
  total is `Cp/(dh)`; non-regular fibres cost `Cp⁸d^{-7/2}h⁻¹` by Markov with eight extra
  moments. Checked numerically: the derivative formulas by finite differences (residual
  `5·10⁻¹³`, all four configurations, including `dbP`, `dbM` and `∂H = dOmP, dOmM`).
* **TB.W1sec** (`weak_sec_of`, `SecB/W1Mom.lean`, proved): the secondary terms of (W3) cost
  `a|wSec| ≤ C B₀`. Sketch (source l.795–822): `m = ‖f‖_∞ ≤ C D_*²/√d`, `X ⪯ h⁻¹`,
  `‖F_{·i}‖ ≤ 2mh⁻¹D_*√r_i`, `Σ_{j∼i}|(X_τ)_ij F_ji| ≤ 2mh⁻¹D_*√(r_i^τ r_i^ν)`,
  `Σ_{j∼i}|(X_ε)_ij U_ij| ≤ mh⁻¹ r_i^ε` (`r_i^τ = (X_τ²)_ii`), and (W5) (`ward_mean_of_cl1`):
  each `E[H ·]` is `≤ C d^{-1/2} h^{-3/2}`; the factor `a² u_i` summed over `N` gives
  `C/(d h^{3/2})`.
* **TB.W1mask** (`weak_mask_of`, `SecB/W1Mom.lean`, proved): for the random masks `b_±`,
  `a|wMask| ≤ C B₀`. Sketch (source l.824–838): `‖∂_ij b‖_∞ ≤ (CaD_*/d^{3/2}) Σ_τ √(r_i^τ r_j^τ)`,
  `|F_ji(g)| ≤ Ch⁻¹D_*²‖g‖_∞`, (W5), at most `d²` pairs and the outer `a u_i`.
* **TB.W1ibp** (`weak_ibp_of`, `SecB/W1.lean`, proved from the three nodes above):
  `|a·wEdge + a²·wMain| ≤ C 𝖲_f + C B₀`, because `a|wScore| ≤ 𝖲_f` (`w1_score_le`: `H ≥ 0`).

**Checks.** Exact algebra (`4 T_k = -ε(a·wEdge + a²·wMain)` and TB.W2 summed) checked numerically
on a 6-vertex graph with the full paired law, all four configurations (residual `≤ 2·10⁻¹⁷`).
`N = ∅`: all sums vanish. Zero sources: rows of `X` vanish and TB.W2 reads `0 = 0`.
-/

@[expose] public section

namespace BiluLinial.Tight.SecB

open Matrix

universe u

/-! ### Generic algebra -/

section Alg

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem maskU_diag_eq {Xe Xn : Matrix V V ℝ} (hXn : ∀ k l, Xn k l = Xn l k) (f : V → ℝ)
    (j : V) : (Xe * diagonal f * Xn) j j = ∑ k, Xe j k * Xn j k * f k := by
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mul_diagonal, hXn k j]
  ring

/-- `Σ_j w_j U_jj = 4 wᵀ K f` for `U = X_ε D_f X_ν`, `K = X_ε ∘ X_ν / 4`, `X_ν` symmetric. -/
theorem sum_mul_maskU_diag {Xe Xn K : Matrix V V ℝ} (hXn : ∀ k l, Xn k l = Xn l k)
    (hK : ∀ k l, K k l = Xe k l * Xn k l / 4) (f w : V → ℝ) :
    ∑ j, w j * (Xe * diagonal f * Xn) j j = 4 * (w ⬝ᵥ (K *ᵥ f)) := by
  have e : ∀ j, (K *ᵥ f) j = ∑ k, K j k * f k := fun j => rfl
  simp only [maskU_diag_eq hXn, dotProduct, e, hK, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring

/-- `Σ_i w_i f_i (X_ε)_ii (X_ν)_ii = 4 wᵀ M f` for `M = diag((X_ε)_ii (X_ν)_ii / 4)`. -/
theorem sum_mul_diag_eq {Xe Xn M : Matrix V V ℝ}
    (hM : M = diagonal fun i => Xe i i * Xn i i / 4) (f w : V → ℝ) :
    ∑ i, w i * (f i * Xe i i * Xn i i) = 4 * (w ⬝ᵥ (M *ᵥ f)) := by
  simp only [hM, dotProduct, Matrix.mulVec_diagonal, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

omit [DecidableEq V] in
theorem dotProduct_mulVec_swap {K : Matrix V V ℝ} (hK : ∀ k l, K k l = K l k) (b f : V → ℝ) :
    b ⬝ᵥ (K *ᵥ f) = f ⬝ᵥ (K *ᵥ b) := by
  have e : ∀ (g : V → ℝ) j, (K *ᵥ g) j = ∑ k, K j k * g k := fun g j => rfl
  simp only [dotProduct, e, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by rw [hK l k]; ring

variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem shiftP_symm (a τ z : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) (k l : V) :
    shiftP G a τ z y σ S k l = shiftP G a τ z y σ S l k := by
  set Q := precN G a τ y σ S + z • srcDiag y S with hQdef
  have hQ : Qᵀ = Q := by
    have h1 : (precN G a τ y σ S)ᵀ = precN G a τ y σ S := by
      have := (precN_isHermitian' G a τ y σ S).eq
      rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
    rw [hQdef, Matrix.transpose_add, Matrix.transpose_smul, h1, srcDiag,
      Matrix.diagonal_transpose]
  have hinv : Q⁻¹ k l = Q⁻¹ l k := by
    have := congrArg (fun M : Matrix V V ℝ => M l k) (Matrix.transpose_nonsing_inv Q)
    simp only [Matrix.transpose_apply, hQ] at this
    exact this
  show Real.sqrt (y k) * Q⁻¹ k l * Real.sqrt (y l) = Real.sqrt (y l) * Q⁻¹ l k * Real.sqrt (y k)
  rw [hinv]
  ring

theorem isUnit_det_shift {a τ h : ℝ} {y : V → ℝ} {σ : Config V} {S : Finset V}
    (hP : (precN G a τ y σ S).PosDef) (hy : ∀ k, 0 ≤ y k) (hh : 0 ≤ h) :
    IsUnit (precN G a τ y σ S + h • srcDiag y S).det := by
  have hD : (srcDiag y S).PosSemidef := Matrix.PosSemidef.diagonal fun k => by
    split_ifs
    · exact hy k
    · exact le_rfl
  exact isUnit_iff_ne_zero.mpr (hP.add_posSemidef (hD.smul hh)).det_pos.ne'

end Alg

/-! ### Objects at a contact -/

section ContactW1

variable {d p : ℕ} (ct : Contact.{u} d p)

theorem w1_uvec_zero {i : ct.V} (hi : i ∉ ct.N) : ct.uvec i = 0 := by
  simp [Contact.uvec, hi]

theorem w1_uvec_nonneg (i : ct.V) : 0 ≤ ct.uvec i := by
  unfold Contact.uvec
  split_ifs
  · positivity
  · exact le_rfl

theorem w1_N_sub_S {i : ct.V} (hi : i ∈ ct.N) : i ∈ ct.S := (Finset.mem_filter.mp hi).1

theorem w1_sum_N (g : ct.V → ℝ) : ∑ i ∈ ct.N, ct.uvec i * g i = ∑ i, ct.uvec i * g i :=
  Finset.sum_subset (Finset.subset_univ _) fun i _ hi => by rw [w1_uvec_zero ct hi, zero_mul]

theorem w1_E_const_mul (c : ℝ) (g : Config ct.V → ℝ) : ct.E (fun σ => c * g σ) = c * ct.E g :=
  lawE_const_mul ct.G c g

theorem w1_E_sub (g₁ g₂ : Config ct.V → ℝ) :
    ct.E (fun σ => g₁ σ - g₂ σ) = ct.E g₁ - ct.E g₂ := lawE_sub ct.G g₁ g₂

theorem w1_E_congr {g₁ g₂ : Config ct.V → ℝ}
    (h : ∀ σ, wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 → g₁ σ = g₂ σ) : ct.E g₁ = ct.E g₂ :=
  lawE_congr ct.G h

theorem w1_abs_E_le (g : Config ct.V → ℝ) : |ct.E g| ≤ ct.E (fun σ => |g σ|) := by
  have h1 : ct.E g ≤ ct.E (fun σ => |g σ|) := lawE_mono ct.G fun σ _ => le_abs_self _
  have h2 : ct.E (fun σ => -g σ) ≤ ct.E (fun σ => |g σ|) := lawE_mono ct.G fun σ _ => neg_le_abs _
  have h3 : ct.E (fun σ => -g σ) = -ct.E g := by
    have := w1_E_const_mul ct (-1) g
    simp only [neg_one_mul] at this
    exact this
  rw [abs_le]
  constructor <;> linarith

theorem B0P_nonneg {h : ℝ} (hh : 0 ≤ h) : 0 ≤ B0P d p h := by
  unfold B0P vth
  have h1 : (0 : ℝ) ≤ d * h := mul_nonneg (Nat.cast_nonneg _) hh
  have h2 : (0 : ℝ) ≤ d * h * Real.sqrt h := mul_nonneg h1 (Real.sqrt_nonneg _)
  have h3 : (0 : ℝ) ≤ 1 / (d : ℝ) ^ 10 := by positivity
  exact add_nonneg (add_nonneg (div_nonneg (Nat.cast_nonneg _) h1) (div_nonneg zero_le_one h2)) h3

theorem w1_E_sum2 (c : ct.V → ℝ) (g : Config ct.V → ct.V → ct.V → ℝ) :
    ct.E (fun σ => ∑ i ∈ ct.N, ∑ j ∈ nbhd ct.G ct.S i, c i * g σ i j) =
      ∑ i ∈ ct.N, ∑ j ∈ nbhd ct.G ct.S i, c i * ct.E (fun σ => g σ i j) := by
  unfold Contact.E
  rw [lawE_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [lawE_sum]
  exact Finset.sum_congr rfl fun j _ => lawE_const_mul ct.G _ _

/-- `a² Σ_{i∈N} Σ_{j∼i} u_i c_i w_j = bᵀ w` with `b = 4a² A_H diag(c/4) u`. -/
theorem w1_main_reorg (c w : ct.V → ℝ) (M : Matrix ct.V ct.V ℝ)
    (hM : M = diagonal fun i => c i / 4) :
    aOf d p ^ 2 * ∑ i ∈ ct.N, ∑ j ∈ nbhd ct.G ct.S i, ct.uvec i * c i * w j =
      ((4 * aOf d p ^ 2) • (ct.adjS *ᵥ (M *ᵥ ct.uvec))) ⬝ᵥ w := by
  have hrow : ∀ l ∈ ct.N, ∑ j ∈ nbhd ct.G ct.S l, ct.uvec l * c l * w j =
      ∑ j, ct.adjS j l * (ct.uvec l * c l * w j) := by
    intro l hl
    have hlS := w1_N_sub_S ct hl
    have e : ∀ j, ct.adjS j l * (ct.uvec l * c l * w j) =
        if j ∈ nbhd ct.G ct.S l then ct.uvec l * c l * w j else 0 := by
      intro j
      simp only [Contact.adjS, Matrix.of_apply, nbhd, Finset.mem_filter]
      by_cases hj : j ∈ ct.S ∧ ct.G.Adj l j
      · rw [ite_eq_left ⟨hj.1, hlS, hj.2.symm⟩, ite_eq_left hj, one_mul]
      · rw [ite_eq_right (fun h => hj ⟨h.1, h.2.2.symm⟩), ite_eq_right hj, zero_mul]
    rw [Finset.sum_congr rfl fun j _ => e j, Finset.sum_ite_mem Finset.univ, Finset.univ_inter]
  have hR : ((4 * aOf d p ^ 2) • (ct.adjS *ᵥ (M *ᵥ ct.uvec))) ⬝ᵥ w =
      aOf d p ^ 2 * ∑ l, ∑ j, ct.adjS j l * (ct.uvec l * c l * w j) := by
    have e : ∀ (X : ct.V → ℝ) j, (ct.adjS *ᵥ X) j = ∑ l, ct.adjS j l * X l := fun X j => rfl
    rw [hM]
    simp only [dotProduct, Pi.smul_apply, smul_eq_mul, e, Matrix.mulVec_diagonal,
      Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_comm.trans
      (Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => by ring)
  rw [hR, Finset.sum_congr rfl hrow]
  congr 1
  refine Finset.sum_subset (Finset.subset_univ _) fun l _ hl => ?_
  simp [w1_uvec_zero ct hl]

/-- The edge sum `Σ_{i∈N} Σ_{j∼i} u_i E[σ_ij H F_ji]`. -/
noncomputable def wEdge (H : Config ct.V → ℝ) (Xe Xn : Config ct.V → Matrix ct.V ct.V ℝ)
    (f : Config ct.V → ct.V → ℝ) : ℝ :=
  ∑ i ∈ ct.N, ∑ j ∈ nbhd ct.G ct.S i, ct.uvec i *
    ct.E fun σ => sgn σ i j * (H σ * maskF (Xe σ) (Xn σ) (f σ) j i)

/-- The main term `Σ_{i∈N} Σ_{j∼i} u_i E[H (X_ε)_ii (X_ν)_ii U_jj]`. -/
noncomputable def wMain (H : Config ct.V → ℝ) (Xe Xn : Config ct.V → Matrix ct.V ct.V ℝ)
    (f : Config ct.V → ct.V → ℝ) : ℝ :=
  ∑ i ∈ ct.N, ∑ j ∈ nbhd ct.G ct.S i, ct.uvec i *
    ct.E fun σ => H σ * (Xe σ i i * Xn σ i i) * (Xe σ * diagonal (f σ) * Xn σ) j j

/-- The first-order score terms
`Σ_{i∈N} Σ_{j∼i} u_i E[∂_ij H · F_ji + 2pa(G⁺_ij - G⁻_ij) H F_ji]`. -/
noncomputable def wScore (H : Config ct.V → ℝ) (dH : Config ct.V → ct.V → ct.V → ℝ)
    (Xe Xn : Config ct.V → Matrix ct.V ct.V ℝ) (f : Config ct.V → ct.V → ℝ) : ℝ :=
  ∑ i ∈ ct.N, ∑ j ∈ nbhd ct.G ct.S i, ct.uvec i * ct.E fun σ =>
    dH σ i j * maskF (Xe σ) (Xn σ) (f σ) j i +
      2 * p * aOf d p * (ct.gp σ i j - ct.gm σ i j) * (H σ * maskF (Xe σ) (Xn σ) (f σ) j i)

/-- The secondary terms of (W3) (`ν = +`):
`Σ_{i∈N} Σ_{j∼i} u_i E[H · (-a)(2ε (X_ε)_ij F_ji + (X_ν)_ij F_ji - (X_ν)_ii (X_ε)_ij U_ij)]`. -/
noncomputable def wSec (ε : ℝ) (H : Config ct.V → ℝ) (Xe Xn : Config ct.V → Matrix ct.V ct.V ℝ)
    (f : Config ct.V → ct.V → ℝ) : ℝ :=
  ∑ i ∈ ct.N, ∑ j ∈ nbhd ct.G ct.S i, ct.uvec i * ct.E fun σ =>
    H σ * (-(aOf d p) * (2 * ε * Xe σ i j * maskF (Xe σ) (Xn σ) (f σ) j i +
      Xn σ i j * maskF (Xe σ) (Xn σ) (f σ) j i -
      Xn σ i i * Xe σ i j * (Xe σ * diagonal (f σ) * Xn σ) i j))

/-- The mask-derivative term `Σ_{i∈N} Σ_{j∼i} u_i E[H F_ji(∂_ij f)]` (`df σ i j = ∂_ij f`). -/
noncomputable def wMask (H : Config ct.V → ℝ) (Xe Xn : Config ct.V → Matrix ct.V ct.V ℝ)
    (df : Config ct.V → ct.V → ct.V → ct.V → ℝ) : ℝ :=
  ∑ i ∈ ct.N, ∑ j ∈ nbhd ct.G ct.S i, ct.uvec i * ct.E fun σ =>
    H σ * maskF (Xe σ) (Xn σ) (df σ i j) j i

/-- `∂_ij (b₊)_k = -4a³ Σ_l (A_H)_kl u_l (X₊)_ll (X₊)_li (X₊)_lj`. -/
noncomputable def dbP (h : ℝ) (σ : Config ct.V) (i j k : ct.V) : ℝ :=
  -(4 * aOf d p ^ 3) *
    ∑ l, ct.adjS k l * ct.uvec l * (ct.XP h σ l l * ct.XP h σ l i * ct.XP h σ l j)

/-- `∂_ij (b₋)_k = 2a³ Σ_l (A_H)_kl u_l ((X₊)_ll (X₋)_li (X₋)_lj - (X₋)_ll (X₊)_li (X₊)_lj)`. -/
noncomputable def dbM (h : ℝ) (σ : Config ct.V) (i j k : ct.V) : ℝ :=
  2 * aOf d p ^ 3 * ∑ l, ct.adjS k l * ct.uvec l *
    (ct.XP h σ l l * ct.XM h σ l i * ct.XM h σ l j - ct.XM h σ l l * ct.XP h σ l i * ct.XP h σ l j)

/-- **TB.W1alg.** TB.W2 summed with the weights `H u_i` (for a branch-`ε` shifted inverse `X_ε`,
given as the hypothesis `hW2`), and the reorganization of the main term. -/
theorem weak_config_ids (ε : ℝ) (H : Config ct.V → ℝ)
    (Xe Xn K M : Config ct.V → Matrix ct.V ct.V ℝ) (f b : Config ct.V → ct.V → ℝ)
    (hW2 : ∀ σ, wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 → ∀ i ∈ ct.S,
      (Xe σ * diagonal (f σ) * Xn σ) i i - f σ i * Xe σ i i * Xn σ i i =
        -(ε * aOf d p) * ∑ j ∈ nbhd ct.G ct.S i, sgn σ i j * maskF (Xe σ) (Xn σ) (f σ) j i)
    (hXn : ∀ σ k l, Xn σ k l = Xn σ l k) (hK : ∀ σ k l, K σ k l = Xe σ k l * Xn σ k l / 4)
    (hKs : ∀ σ k l, K σ k l = K σ l k)
    (hM : ∀ σ, M σ = diagonal fun i => Xe σ i i * Xn σ i i / 4)
    (hb : ∀ σ, b σ = (4 * aOf d p ^ 2) • (ct.adjS *ᵥ (M σ *ᵥ ct.uvec))) :
    4 * ct.E (fun σ => H σ * (ct.uvec ⬝ᵥ (K σ *ᵥ f σ))) -
        4 * ct.E (fun σ => H σ * (ct.uvec ⬝ᵥ (M σ *ᵥ f σ))) =
        -(ε * aOf d p) * wEdge ct H Xe Xn f ∧
      aOf d p ^ 2 * wMain ct H Xe Xn f = 4 * ct.E (fun σ => H σ * (f σ ⬝ᵥ (K σ *ᵥ b σ))) := by
  constructor
  · have hpt : ∀ σ, wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 →
        4 * (H σ * (ct.uvec ⬝ᵥ (K σ *ᵥ f σ))) - 4 * (H σ * (ct.uvec ⬝ᵥ (M σ *ᵥ f σ))) =
          -(ε * aOf d p) * ∑ i ∈ ct.N, ∑ j ∈ nbhd ct.G ct.S i,
            ct.uvec i * (sgn σ i j * (H σ * maskF (Xe σ) (Xn σ) (f σ) j i)) := by
      intro σ hσ
      have e1 := sum_mul_maskU_diag (hXn σ) (hK σ) (f σ) ct.uvec
      have e2 := sum_mul_diag_eq (hM σ) (f σ) ct.uvec
      have e3 : ∑ i, ct.uvec i *
            ((Xe σ * diagonal (f σ) * Xn σ) i i - f σ i * Xe σ i i * Xn σ i i) =
          ∑ i ∈ ct.N, ct.uvec i * (-(ε * aOf d p) *
            ∑ j ∈ nbhd ct.G ct.S i, sgn σ i j * maskF (Xe σ) (Xn σ) (f σ) j i) := by
        rw [← w1_sum_N ct]
        exact Finset.sum_congr rfl fun i hi => by rw [hW2 σ hσ i (w1_N_sub_S ct hi)]
      have e4 : ∑ i, ct.uvec i *
            ((Xe σ * diagonal (f σ) * Xn σ) i i - f σ i * Xe σ i i * Xn σ i i) =
          4 * (ct.uvec ⬝ᵥ (K σ *ᵥ f σ)) - 4 * (ct.uvec ⬝ᵥ (M σ *ᵥ f σ)) := by
        rw [← e1, ← e2, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [e4] at e3
      have e5 : -(ε * aOf d p) * ∑ i ∈ ct.N, ∑ j ∈ nbhd ct.G ct.S i,
            ct.uvec i * (sgn σ i j * (H σ * maskF (Xe σ) (Xn σ) (f σ) j i)) =
          H σ * ∑ i ∈ ct.N, ct.uvec i * (-(ε * aOf d p) *
            ∑ j ∈ nbhd ct.G ct.S i, sgn σ i j * maskF (Xe σ) (Xn σ) (f σ) j i) := by
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      rw [e5, ← e3]
      ring
    have hE := w1_E_congr ct hpt
    rw [w1_E_sub, w1_E_const_mul, w1_E_const_mul, w1_E_const_mul, w1_E_sum2] at hE
    rw [hE]
    rfl
  · have hpt : ∀ σ, aOf d p ^ 2 * ∑ i ∈ ct.N, ∑ j ∈ nbhd ct.G ct.S i,
          ct.uvec i * (H σ * (Xe σ i i * Xn σ i i) * (Xe σ * diagonal (f σ) * Xn σ) j j) =
        4 * (H σ * (f σ ⬝ᵥ (K σ *ᵥ b σ))) := by
      intro σ
      have e1 := w1_main_reorg ct (fun i => Xe σ i i * Xn σ i i)
        (fun j => (Xe σ * diagonal (f σ) * Xn σ) j j) (M σ) (hM σ)
      rw [← hb σ] at e1
      have e2 := sum_mul_maskU_diag (hXn σ) (hK σ) (f σ) (b σ)
      have e3 := dotProduct_mulVec_swap (hKs σ) (b σ) (f σ)
      have e4 : ∑ i ∈ ct.N, ∑ j ∈ nbhd ct.G ct.S i,
            ct.uvec i * (H σ * (Xe σ i i * Xn σ i i) * (Xe σ * diagonal (f σ) * Xn σ) j j) =
          H σ * ∑ i ∈ ct.N, ∑ j ∈ nbhd ct.G ct.S i,
            ct.uvec i * (Xe σ i i * Xn σ i i) * (Xe σ * diagonal (f σ) * Xn σ) j j := by
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      calc aOf d p ^ 2 * ∑ i ∈ ct.N, ∑ j ∈ nbhd ct.G ct.S i,
            ct.uvec i * (H σ * (Xe σ i i * Xn σ i i) * (Xe σ * diagonal (f σ) * Xn σ) j j)
          = H σ * (aOf d p ^ 2 * ∑ i ∈ ct.N, ∑ j ∈ nbhd ct.G ct.S i,
              ct.uvec i * (Xe σ i i * Xn σ i i) * (Xe σ * diagonal (f σ) * Xn σ) j j) := by
            rw [e4]; ring
        _ = H σ * (b σ ⬝ᵥ fun j => (Xe σ * diagonal (f σ) * Xn σ) j j) := by rw [e1]
        _ = H σ * ∑ j, b σ j * (Xe σ * diagonal (f σ) * Xn σ) j j := rfl
        _ = H σ * (4 * (b σ ⬝ᵥ (K σ *ᵥ f σ))) := by rw [e2]
        _ = 4 * (H σ * (f σ ⬝ᵥ (K σ *ᵥ b σ))) := by rw [e3]; ring
    have hE : ct.E (fun σ => aOf d p ^ 2 * ∑ i ∈ ct.N, ∑ j ∈ nbhd ct.G ct.S i,
          ct.uvec i * (H σ * (Xe σ i i * Xn σ i i) * (Xe σ * diagonal (f σ) * Xn σ) j j)) =
        ct.E (fun σ => 4 * (H σ * (f σ ⬝ᵥ (K σ *ᵥ b σ)))) :=
      w1_E_congr ct fun σ _ => hpt σ
    rw [w1_E_const_mul, w1_E_const_mul, w1_E_sum2] at hE
    rw [← hE]
    rfl

/-- `a |wScore| ≤ 𝖲_f` when `H ≥ 0` on the support. -/
theorem w1_score_le {H : Config ct.V → ℝ} (dH : Config ct.V → ct.V → ct.V → ℝ)
    (Xe Xn : Config ct.V → Matrix ct.V ct.V ℝ) (f : Config ct.V → ct.V → ℝ)
    (hH : ∀ σ, wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 → 0 ≤ H σ) (ha : 0 ≤ aOf d p) :
    aOf d p * |wScore ct H dH Xe Xn f| ≤ ct.score H dH Xe Xn f := by
  unfold Contact.score wScore
  refine mul_le_mul_of_nonneg_left ?_ ha
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun i _ => ?_)
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul, abs_of_nonneg (w1_uvec_nonneg ct i)]
  refine mul_le_mul_of_nonneg_left ?_ (w1_uvec_nonneg ct i)
  refine le_trans (w1_abs_E_le ct _) (lawE_mono ct.G fun σ hσ => ?_)
  have hH0 := hH σ hσ
  have hp : (0 : ℝ) ≤ 2 * p * aOf d p := by positivity
  calc |dH σ i j * maskF (Xe σ) (Xn σ) (f σ) j i +
        2 * p * aOf d p * (ct.gp σ i j - ct.gm σ i j) * (H σ * maskF (Xe σ) (Xn σ) (f σ) j i)|
      ≤ |dH σ i j * maskF (Xe σ) (Xn σ) (f σ) j i| +
        |2 * p * aOf d p * (ct.gp σ i j - ct.gm σ i j) *
          (H σ * maskF (Xe σ) (Xn σ) (f σ) j i)| := abs_add_le _ _
    _ = |maskF (Xe σ) (Xn σ) (f σ) j i| *
          (2 * p * aOf d p * H σ * |ct.gp σ i j - ct.gm σ i j| + |dH σ i j|) := by
        rw [abs_mul (dH σ i j), abs_mul (2 * p * aOf d p * (ct.gp σ i j - ct.gm σ i j)),
          abs_mul (2 * p * aOf d p), abs_mul (H σ), abs_of_nonneg hp, abs_of_nonneg hH0]
        ring

theorem w1_score_nonneg {H : Config ct.V → ℝ} (dH : Config ct.V → ct.V → ct.V → ℝ)
    (Xe Xn : Config ct.V → Matrix ct.V ct.V ℝ) (f : Config ct.V → ct.V → ℝ)
    (hH : ∀ σ, wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 → 0 ≤ H σ) (ha : 0 ≤ aOf d p) :
    0 ≤ ct.score H dH Xe Xn f := by
  unfold Contact.score
  refine mul_nonneg ha (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    mul_nonneg (w1_uvec_nonneg ct i) (lawE_nonneg ct.G fun σ hσ => ?_))
  have hp : (0 : ℝ) ≤ 2 * p * aOf d p := mul_nonneg (by positivity) ha
  exact mul_nonneg (abs_nonneg _) (add_nonneg (mul_nonneg (mul_nonneg hp (hH σ hσ))
    (abs_nonneg _)) (abs_nonneg _))

theorem w1_OmP_nonneg (σ : Config ct.V) : 0 ≤ ct.OmP σ := sq_nonneg _

theorem w1_OmM_nonneg {σ : Config ct.V} (hσ : wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0) :
    0 ≤ ct.OmM σ := by
  obtain ⟨hpP, hpM⟩ := posDef_of_wt_ne_zero ct.G hσ
  have h1 := (diag_nonneg_of_posDef ct.G hpP (fun k => (ct.ctx.hyp k).1) le_rfl ct.v).1
  have h2 := (diag_nonneg_of_posDef ct.G hpM (fun k => (ct.ctx.hym k).1) le_rfl ct.v).1
  exact div_nonneg (mul_nonneg h1 h2) (by norm_num)

/-- TB.W2 at a contact, plus branch (`X_ε = X₊`). -/
theorem w1_W2_plus {h : ℝ} (hh : 0 ≤ h) (Xn : Config ct.V → Matrix ct.V ct.V ℝ)
    (f : Config ct.V → ct.V → ℝ) :
    ∀ σ, wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 → ∀ i ∈ ct.S,
      (ct.XP h σ * diagonal (f σ) * Xn σ) i i - f σ i * ct.XP h σ i i * Xn σ i i =
        -(1 * aOf d p) * ∑ j ∈ nbhd ct.G ct.S i,
          sgn σ i j * maskF (ct.XP h σ) (Xn σ) (f σ) j i := by
  intro σ hσ i hi
  have hy : ∀ k, 0 ≤ ct.yp k := fun k => (ct.ctx.hyp k).1
  exact weak_w2 ct.G hy (isUnit_det_shift ct.G (posDef_of_wt_ne_zero ct.G hσ).1 hy hh) hi
    (Xn σ) (f σ)

/-- TB.W2 at a contact, minus branch (`X_ε = X₋`). -/
theorem w1_W2_minus {h : ℝ} (hh : 0 ≤ h) (Xn : Config ct.V → Matrix ct.V ct.V ℝ)
    (f : Config ct.V → ct.V → ℝ) :
    ∀ σ, wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 → ∀ i ∈ ct.S,
      (ct.XM h σ * diagonal (f σ) * Xn σ) i i - f σ i * ct.XM h σ i i * Xn σ i i =
        -(-1 * aOf d p) * ∑ j ∈ nbhd ct.G ct.S i,
          sgn σ i j * maskF (ct.XM h σ) (Xn σ) (f σ) j i := by
  intro σ hσ i hi
  have hy : ∀ k, 0 ≤ ct.ym k := fun k => (ct.ctx.hym k).1
  exact weak_w2 ct.G hy (isUnit_det_shift ct.G (posDef_of_wt_ne_zero ct.G hσ).2 hy hh) hi
    (Xn σ) (f σ)

theorem w1_XP_symm (h : ℝ) (σ : Config ct.V) (k l : ct.V) : ct.XP h σ k l = ct.XP h σ l k := by
  simp only [Contact.XP, Matrix.of_apply]
  exact shiftP_symm ct.G _ _ _ _ σ ct.S k l

theorem w1_XM_symm (h : ℝ) (σ : Config ct.V) (k l : ct.V) : ct.XM h σ k l = ct.XM h σ l k := by
  simp only [Contact.XM, Matrix.of_apply]
  exact shiftP_symm ct.G _ _ _ _ σ ct.S k l

/-- The four targets of `in_W1` in terms of the edge sum and the main term:
`4 T_k = -ε (a·wEdge + a²·wMain)`. -/
theorem weak_targets {h : ℝ} (hh : 0 ≤ h) :
    4 * (ct.qP h - ct.zeta h - ct.tP h) =
        -(aOf d p * wEdge ct ct.OmP (ct.XP h) (ct.XP h) (fun _ => ct.uvec) +
          aOf d p ^ 2 * wMain ct ct.OmP (ct.XP h) (ct.XP h) (fun _ => ct.uvec)) ∧
      4 * (ct.zeta h - ct.zP h - ct.alphaE h) =
        -(aOf d p * wEdge ct ct.OmP (ct.XP h) (ct.XP h) (ct.bP h) +
          aOf d p ^ 2 * wMain ct ct.OmP (ct.XP h) (ct.XP h) (ct.bP h)) ∧
      4 * (ct.qM h + ct.zetaM h - ct.tM h) =
        aOf d p * wEdge ct ct.OmM (ct.XM h) (ct.XP h) (fun _ => ct.uvec) +
          aOf d p ^ 2 * wMain ct ct.OmM (ct.XM h) (ct.XP h) (fun _ => ct.uvec) ∧
      4 * (ct.zetaM h + ct.zM h - ct.betaE h) =
        aOf d p * wEdge ct ct.OmM (ct.XM h) (ct.XP h) (ct.bM h) +
          aOf d p ^ 2 * wMain ct ct.OmM (ct.XM h) (ct.XP h) (ct.bM h) := by
  have hKP : ∀ σ k l, ct.KP h σ k l = ct.XP h σ k l * ct.XP h σ k l / 4 := fun _ _ _ => rfl
  have hKPs : ∀ σ k l, ct.KP h σ k l = ct.KP h σ l k := fun σ k l => by
    rw [hKP, hKP, w1_XP_symm ct h σ k l]
  have hKM : ∀ σ k l, ct.KM h σ k l = ct.XM h σ k l * ct.XP h σ k l / 4 := fun σ k l => by
    show ct.XP h σ k l * ct.XM h σ k l / 4 = _
    ring
  have hKMs : ∀ σ k l, ct.KM h σ k l = ct.KM h σ l k := fun σ k l => by
    rw [hKM, hKM, w1_XP_symm ct h σ k l, w1_XM_symm ct h σ k l]
  have hMP : ∀ σ, ct.MP h σ = diagonal fun i => ct.XP h σ i i * ct.XP h σ i i / 4 :=
    fun σ => by
      unfold Contact.MP
      congr 1
      funext i
      ring
  have hMM : ∀ σ, ct.MM h σ = diagonal fun i => ct.XM h σ i i * ct.XP h σ i i / 4 :=
    fun σ => by
      unfold Contact.MM
      congr 1
      funext i
      ring
  have hbP : ∀ σ, ct.bP h σ = (4 * aOf d p ^ 2) • (ct.adjS *ᵥ (ct.MP h σ *ᵥ ct.uvec)) :=
    fun _ => rfl
  have hbM : ∀ σ, ct.bM h σ = (4 * aOf d p ^ 2) • (ct.adjS *ᵥ (ct.MM h σ *ᵥ ct.uvec)) :=
    fun _ => rfl
  have hsP := w1_XP_symm ct h
  obtain ⟨a1, b1⟩ := weak_config_ids ct 1 ct.OmP (ct.XP h) (ct.XP h) (ct.KP h) (ct.MP h)
    (fun _ => ct.uvec) (ct.bP h) (w1_W2_plus ct hh _ _) hsP hKP hKPs hMP hbP
  obtain ⟨a2, b2⟩ := weak_config_ids ct 1 ct.OmP (ct.XP h) (ct.XP h) (ct.KP h) (ct.MP h)
    (ct.bP h) (ct.bP h) (w1_W2_plus ct hh _ _) hsP hKP hKPs hMP hbP
  obtain ⟨a3, b3⟩ := weak_config_ids ct (-1) ct.OmM (ct.XM h) (ct.XP h) (ct.KM h) (ct.MM h)
    (fun _ => ct.uvec) (ct.bM h) (w1_W2_minus ct hh _ _) hsP hKM hKMs hMM hbM
  obtain ⟨a4, b4⟩ := weak_config_ids ct (-1) ct.OmM (ct.XM h) (ct.XP h) (ct.KM h) (ct.MM h)
    (ct.bM h) (ct.bM h) (w1_W2_minus ct hh _ _) hsP hKM hKMs hMM hbM
  unfold Contact.qP Contact.zeta Contact.tP Contact.zP Contact.alphaE Contact.qM Contact.zetaM
    Contact.tM Contact.zM Contact.betaE
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

end ContactW1


end BiluLinial.Tight.SecB
