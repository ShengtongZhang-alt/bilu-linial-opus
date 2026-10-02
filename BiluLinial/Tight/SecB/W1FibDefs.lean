/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecB.W1Mom
public import BiluLinial.Tight.Compare.Endpoint

/-!
# The weak loop (W1), edge fibres: definitions and generic tools

Definitions and generic lemmas for TB.W1fib (`docs/tight/BP_SECB.md`; source l.776–779, 840–903).
Sketches of the nodes are in the module docstrings of `SecB/W1Fib.lean` and `SecB/W1FibEdge.lean`.

* `trapezoid_chain`: `|E_ξ[ξφ(ξ)] - E_ξ[φ'(ξ)]| ≤ (2/3) sup_{[-1,1]} |φ'''|` (chain form).
* `sum_sgn_fibre`, `sum_fibre_neg`, `sum_fibre_pair`: sums over signings split along the fibres
  `{σ, σ^e}` of an edge `e` (`σ^e` = `σ` with `σ_e = -1`).
* `FibChain Φ₀ Φ₁ σ σ' B`: a `C³` chain `F` on `[-1, 1]` with `F₀(1) = Φ₀(σ)`, `F₀(-1) = Φ₀(σ')`,
  `F₁(1) = Φ₁(σ)`, `F₁(-1) = Φ₁(σ')` and `|F₃| ≤ B`; `fibChain_bound`:
  `|Φ₀σ - Φ₀σ' - (Φ₁σ + Φ₁σ')| ≤ (4/3) B`.
* `fibre_ibp_bound` (abstract first-order fibre integration by parts): if every regular fibre carries
  a `FibChain` for `(Φ₀, Φ₁) = (WΨ, W DΨ)`, then `|Σ_σ σ_e Φ₀ - Σ_σ Φ₁|` is at most the sum over the
  fibres of `(4/3) B` (regular) or of the four endpoint terms (non-regular).
* `fibR`, `fibD`, `fibRem`, `fibB`: `R_ij`, the first-order derivative `DΨ`, the per-edge remainder
  `Rem_ij = E[σ_ij Ψ] - E[DΨ]` and the bound of TB.W1fib-edge; `weak_fibre_alg` (TB.W1fib-alg).
-/

@[expose] public section

namespace BiluLinial.Tight.SecB

open Matrix

universe u

/-! ### Tools -/

/-- **First-order endpoint identity (trapezoid rule).** For a chain `F 0, …, F 3` of successive
derivatives on `[-1, 1]` with `|F 3| ≤ M`:
`|(F₀(1) - F₀(-1))/2 - (F₁(1) + F₁(-1))/2| ≤ (2/3) M`, i.e. `|E_ξ[ξ φ(ξ)] - E_ξ[φ'(ξ)]| ≤ (2/3) M`. -/
theorem trapezoid_chain (F : ℕ → ℝ → ℝ)
    (hF : ∀ m < 3, ∀ t ∈ Set.Icc (-1 : ℝ) 1, HasDerivAt (F m) (F (m + 1) t) t) (M : ℝ)
    (hM : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |F 3 t| ≤ M) :
    |(F 0 1 - F 0 (-1)) / 2 - (F 1 1 + F 1 (-1)) / 2| ≤ 2 / 3 * M := by
  have hI : (Set.Icc (-1 : ℝ) 1).OrdConnected := Set.ordConnected_Icc
  have h0 : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have h1 : (1 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hm1 : (-1 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have T0 := taylor_chain_bound hI h0 3 F hF M hM
  have T1 := taylor_chain_bound hI h0 2 (fun m => F (1 + m))
    (fun m hm t ht => hF (1 + m) (by omega) t ht) M (fun t ht => hM t ht)
  have a := T0 1 h1
  have b := T0 (-1) hm1
  have c := T1 1 h1
  have e := T1 (-1) hm1
  norm_num [Finset.sum_range_succ, Nat.factorial] at a b c e
  rw [abs_le] at a b c e ⊢
  constructor <;> linarith [a.1, a.2, b.1, b.2, c.1, c.2, e.1, e.2]

/-- **Sign-fibre identity.** `Σ_σ σ_e Φ(σ) = Σ_σ 1_{σ_e = 1} (Φ(σ) - Φ(σ^e))`, `σ^e` the signing
flipped at `e`. -/
theorem sum_sgn_fibre {V : Type*} [Fintype V] [DecidableEq V] (e : Sym2 V)
    (Φ : Config V → ℝ) :
    ∑ σ : Config V, ((σ e : ℤ) : ℝ) * Φ σ =
      ∑ σ : Config V, if σ e = 1 then Φ σ - Φ (Function.update σ e (-1)) else 0 := by
  -- the flip at `e` is an involution
  let ι : Config V ≃ Config V :=
    { toFun := fun σ => Function.update σ e (-σ e)
      invFun := fun σ => Function.update σ e (-σ e)
      left_inv := fun σ => by
        funext x
        by_cases hx : x = e
        · subst hx; simp
        · simp [Function.update_of_ne hx]
      right_inv := fun σ => by
        funext x
        by_cases hx : x = e
        · subst hx; simp
        · simp [Function.update_of_ne hx] }
  have hval : ∀ σ : Config V, σ e = 1 ∨ σ e = -1 := fun σ => Int.units_eq_one_or (σ e)
  have hne : (-1 : ℤˣ) ≠ 1 := by decide
  have hne' : (1 : ℤˣ) ≠ -1 := by decide
  have hsplit : ∀ σ : Config V, ((σ e : ℤ) : ℝ) * Φ σ =
      (if σ e = 1 then Φ σ else 0) - (if σ e = -1 then Φ σ else 0) := fun σ => by
    rcases hval σ with h | h <;> simp [h, hne, hne']
  have hneg : ∑ σ : Config V, (if σ e = -1 then Φ σ else 0) =
      ∑ σ : Config V, if σ e = 1 then Φ (Function.update σ e (-1)) else 0 := by
    rw [← Equiv.sum_comp ι]
    refine Finset.sum_congr rfl fun σ _ => ?_
    have hιe : (ι σ) e = -σ e := by simp [ι]
    rcases hval σ with h | h
    · have : ι σ = Function.update σ e (-1) := by simp [ι, h]
      rw [hιe, h, this]; simp
    · rw [hιe, h]; simp [hne, hne']
  rw [Finset.sum_congr rfl fun σ _ => hsplit σ, Finset.sum_sub_distrib, hneg,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun σ _ => ?_
  split_ifs <;> ring

/-! ### The per-edge remainder -/

section Fib

variable {d p : ℕ} (ct : Contact.{u} d p)

/-- `R_ij = |G⁺_ij| + |G⁻_ij|`. -/
noncomputable def fibR (σ : Config ct.V) (i j : ct.V) : ℝ := |ct.gp σ i j| + |ct.gm σ i j|

/-- The first-order fibre derivative `DΨ = ∂Ψ + Ψ ∂ log W` of `Ψ = H F_ji` along the edge `ij`
(`ν = +`). -/
noncomputable def fibD (ε : ℝ) (H : Config ct.V → ℝ) (dH : Config ct.V → ct.V → ct.V → ℝ)
    (Xe Xn : Config ct.V → Matrix ct.V ct.V ℝ) (f : Config ct.V → ct.V → ℝ)
    (df : Config ct.V → ct.V → ct.V → ct.V → ℝ) (i j : ct.V) (σ : Config ct.V) : ℝ :=
  (dH σ i j * maskF (Xe σ) (Xn σ) (f σ) j i +
      2 * p * aOf d p * (ct.gp σ i j - ct.gm σ i j) * (H σ * maskF (Xe σ) (Xn σ) (f σ) j i)) +
    H σ * (-(aOf d p) * (2 * ε * Xe σ i j * maskF (Xe σ) (Xn σ) (f σ) j i +
      Xn σ i j * maskF (Xe σ) (Xn σ) (f σ) j i -
      Xn σ i i * Xe σ i j * (Xe σ * diagonal (f σ) * Xn σ) i j)) +
    H σ * maskF (Xe σ) (Xn σ) (df σ i j) j i -
    aOf d p * (H σ * (Xe σ i i * Xn σ i i) * (Xe σ * diagonal (f σ) * Xn σ) j j)

/-- The per-edge remainder `Rem_ij = E[σ_ij H F_ji] - E[DΨ]`. -/
noncomputable def fibRem (ε : ℝ) (H : Config ct.V → ℝ) (dH : Config ct.V → ct.V → ct.V → ℝ)
    (Xe Xn : Config ct.V → Matrix ct.V ct.V ℝ) (f : Config ct.V → ct.V → ℝ)
    (df : Config ct.V → ct.V → ct.V → ct.V → ℝ) (i j : ct.V) : ℝ :=
  ct.E (fun σ => sgn σ i j * (H σ * maskF (Xe σ) (Xn σ) (f σ) j i)) -
    ct.E (fibD ct ε H dH Xe Xn f df i j)

/-- The bound of TB.W1fib-edge: `C (a³/(√d h)) E[D_*^M (p³ R_ij² + p)]`. -/
noncomputable def fibB (C : ℝ) (M : ℕ) (h : ℝ) (i j : ct.V) : ℝ :=
  C * (aOf d p ^ 3 / (Real.sqrt d * h)) *
    ct.E (fun σ => ct.Dstar σ ^ M * ((p : ℝ) ^ 3 * fibR ct σ i j ^ 2 + p))

theorem maskF_zero_mask {V : Type*} [Fintype V] [DecidableEq V] (Xe Xn : Matrix V V ℝ)
    (j i : V) : maskF Xe Xn (fun _ => 0) j i = 0 := by
  simp [maskF]

theorem wMask_zero (H : Config ct.V → ℝ) (Xe Xn : Config ct.V → Matrix ct.V ct.V ℝ) :
    wMask ct H Xe Xn (fun _ _ _ _ => 0) = 0 := by
  unfold wMask
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  have : ct.E (fun σ => H σ * maskF (Xe σ) (Xn σ) (fun _ => 0) j i) = 0 := by
    have e : (fun σ => H σ * maskF (Xe σ) (Xn σ) (fun _ => 0) j i) = fun _ => (0 : ℝ) := by
      funext σ; rw [maskF_zero_mask, mul_zero]
    rw [e]
    exact lawE_zero ct.G
  rw [this, mul_zero]

/-- **TB.W1fib-alg** (exact). -/
theorem weak_fibre_alg (ε : ℝ) (H : Config ct.V → ℝ) (dH : Config ct.V → ct.V → ct.V → ℝ)
    (Xe Xn : Config ct.V → Matrix ct.V ct.V ℝ) (f : Config ct.V → ct.V → ℝ)
    (df : Config ct.V → ct.V → ct.V → ct.V → ℝ) :
    aOf d p * wEdge ct H Xe Xn f + aOf d p ^ 2 * wMain ct H Xe Xn f -
        aOf d p * (wScore ct H dH Xe Xn f + wSec ct ε H Xe Xn f + wMask ct H Xe Xn df) =
      aOf d p * ∑ i ∈ ct.N, ∑ j ∈ nbhd ct.G ct.S i,
        ct.uvec i * fibRem ct ε H dH Xe Xn f df i j := by
  have hpt : ∀ i j, ct.uvec i * fibRem ct ε H dH Xe Xn f df i j =
      ct.uvec i * ct.E (fun σ => sgn σ i j * (H σ * maskF (Xe σ) (Xn σ) (f σ) j i)) -
        (ct.uvec i * ct.E (fun σ => dH σ i j * maskF (Xe σ) (Xn σ) (f σ) j i +
            2 * p * aOf d p * (ct.gp σ i j - ct.gm σ i j) *
              (H σ * maskF (Xe σ) (Xn σ) (f σ) j i)) +
          ct.uvec i * ct.E (fun σ => H σ * (-(aOf d p) *
            (2 * ε * Xe σ i j * maskF (Xe σ) (Xn σ) (f σ) j i +
              Xn σ i j * maskF (Xe σ) (Xn σ) (f σ) j i -
              Xn σ i i * Xe σ i j * (Xe σ * diagonal (f σ) * Xn σ) i j))) +
          ct.uvec i * ct.E (fun σ => H σ * maskF (Xe σ) (Xn σ) (df σ i j) j i)) +
        aOf d p * (ct.uvec i * ct.E (fun σ => H σ * (Xe σ i i * Xn σ i i) *
          (Xe σ * diagonal (f σ) * Xn σ) j j)) := by
    intro i j
    unfold fibRem fibD Contact.E
    rw [lawE_sub ct.G, lawE_add ct.G, lawE_add ct.G, lawE_const_mul ct.G]
    ring
  unfold wEdge wMain wScore wSec wMask
  simp only [hpt, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

end Fib

/-! ### Fibre sums and the abstract first-order fibre integration by parts -/

/-- `Σ_σ 1_{σ_e = -1} Φ(σ) = Σ_σ 1_{σ_e = 1} Φ(σ^e)`. -/
theorem sum_fibre_neg {V : Type*} [Fintype V] [DecidableEq V] (e : Sym2 V)
    (Φ : Config V → ℝ) :
    ∑ σ : Config V, (if σ e = -1 then Φ σ else 0) =
      ∑ σ : Config V, if σ e = 1 then Φ (Function.update σ e (-1)) else 0 := by
  let ι : Config V ≃ Config V :=
    { toFun := fun σ => Function.update σ e (-σ e)
      invFun := fun σ => Function.update σ e (-σ e)
      left_inv := fun σ => by
        funext x
        by_cases hx : x = e
        · subst hx; simp
        · simp [Function.update_of_ne hx]
      right_inv := fun σ => by
        funext x
        by_cases hx : x = e
        · subst hx; simp
        · simp [Function.update_of_ne hx] }
  have hval : ∀ σ : Config V, σ e = 1 ∨ σ e = -1 := fun σ => Int.units_eq_one_or (σ e)
  have hne : (-1 : ℤˣ) ≠ 1 := by decide
  have hne' : (1 : ℤˣ) ≠ -1 := by decide
  rw [← Equiv.sum_comp ι]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hιe : (ι σ) e = -σ e := by simp [ι]
  rcases hval σ with h | h
  · have : ι σ = Function.update σ e (-1) := by simp [ι, h]
    rw [hιe, h, this]; simp
  · rw [hιe, h]; simp [hne, hne']

/-- `Σ_σ Φ(σ) = Σ_σ 1_{σ_e = 1} (Φ(σ) + Φ(σ^e))`. -/
theorem sum_fibre_pair {V : Type*} [Fintype V] [DecidableEq V] (e : Sym2 V)
    (Φ : Config V → ℝ) :
    ∑ σ : Config V, Φ σ =
      ∑ σ : Config V, if σ e = 1 then Φ σ + Φ (Function.update σ e (-1)) else 0 := by
  have hval : ∀ σ : Config V, σ e = 1 ∨ σ e = -1 := fun σ => Int.units_eq_one_or (σ e)
  have hne : (-1 : ℤˣ) ≠ 1 := by decide
  have hsplit : ∀ σ : Config V, Φ σ =
      (if σ e = 1 then Φ σ else 0) + (if σ e = -1 then Φ σ else 0) := fun σ => by
    rcases hval σ with h | h
    · rw [if_pos h, if_neg (by rw [h]; exact hne.symm), add_zero]
    · rw [if_neg (by rw [h]; exact hne), if_pos h, zero_add]
  rw [Finset.sum_congr rfl fun σ _ => hsplit σ, Finset.sum_add_distrib, sum_fibre_neg,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun σ _ => ?_
  split_ifs <;> ring

/-- A `C³` chain on `[-1, 1]` joining the endpoints of a fibre: `F₀(1) = Φ₀(σp)`,
`F₀(-1) = Φ₀(σm)`, `F₁(1) = Φ₁(σp)`, `F₁(-1) = Φ₁(σm)`, `|F₃| ≤ B`. -/
def FibChain {V : Type*} (Φ₀ Φ₁ : Config V → ℝ) (σp σm : Config V) (B : ℝ) : Prop :=
  ∃ F : ℕ → ℝ → ℝ, (∀ m < 3, ∀ t ∈ Set.Icc (-1 : ℝ) 1, HasDerivAt (F m) (F (m + 1) t) t) ∧
    F 0 1 = Φ₀ σp ∧ F 0 (-1) = Φ₀ σm ∧ F 1 1 = Φ₁ σp ∧ F 1 (-1) = Φ₁ σm ∧
    ∀ t ∈ Set.Icc (-1 : ℝ) 1, |F 3 t| ≤ B

theorem fibChain_bound {V : Type*} {Φ₀ Φ₁ : Config V → ℝ} {σp σm : Config V} {B : ℝ}
    (h : FibChain Φ₀ Φ₁ σp σm B) :
    |Φ₀ σp - Φ₀ σm - (Φ₁ σp + Φ₁ σm)| ≤ 4 / 3 * B := by
  obtain ⟨F, hF, h0p, h0m, h1p, h1m, hB⟩ := h
  have := trapezoid_chain F hF B hB
  rw [h0p, h0m, h1p, h1m] at this
  have e : Φ₀ σp - Φ₀ σm - (Φ₁ σp + Φ₁ σm) =
      2 * ((Φ₀ σp - Φ₀ σm) / 2 - (Φ₁ σp + Φ₁ σm) / 2) := by ring
  rw [e, abs_mul, abs_two]
  linarith

/-- **Abstract first-order fibre integration by parts.** With `σ' = σ^e`:
`|Σ_σ σ_e Φ₀(σ) - Σ_σ Φ₁(σ)| ≤ Σ_{σ_e = 1} (reg σ ? (4/3) B σ : |Φ₀σ| + |Φ₀σ'| + |Φ₁σ| + |Φ₁σ'|)`
when every regular fibre carries a `FibChain`. -/
theorem fibre_ibp_bound {V : Type*} [Fintype V] [DecidableEq V] (e : Sym2 V)
    (Φ₀ Φ₁ B : Config V → ℝ) (reg : Config V → Prop) [DecidablePred reg]
    (hreg : ∀ σ, σ e = 1 → reg σ → FibChain Φ₀ Φ₁ σ (Function.update σ e (-1)) (B σ)) :
    |∑ σ : Config V, ((σ e : ℤ) : ℝ) * Φ₀ σ - ∑ σ : Config V, Φ₁ σ| ≤
      ∑ σ : Config V, if σ e = 1 then
        (if reg σ then 4 / 3 * B σ else
          |Φ₀ σ| + |Φ₀ (Function.update σ e (-1))| + |Φ₁ σ| +
            |Φ₁ (Function.update σ e (-1))|) else 0 := by
  rw [sum_sgn_fibre, sum_fibre_pair e Φ₁, ← Finset.sum_sub_distrib]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun σ _ => ?_)
  by_cases he : σ e = 1
  · rw [if_pos he, if_pos he, if_pos he]
    by_cases hr : reg σ
    · rw [if_pos hr]
      exact fibChain_bound (hreg σ he hr)
    · rw [if_neg hr]
      rw [abs_le]
      constructor <;> linarith [abs_nonneg (Φ₀ σ), le_abs_self (Φ₀ σ), neg_abs_le (Φ₀ σ),
        le_abs_self (Φ₀ (Function.update σ e (-1))), neg_abs_le (Φ₀ (Function.update σ e (-1))),
        le_abs_self (Φ₁ σ), neg_abs_le (Φ₁ σ),
        le_abs_self (Φ₁ (Function.update σ e (-1))), neg_abs_le (Φ₁ (Function.update σ e (-1)))]
  · rw [if_neg he, if_neg he, if_neg he, sub_zero, abs_zero]

end BiluLinial.Tight.SecB
