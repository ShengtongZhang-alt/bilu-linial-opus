/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.Compare.Moments
public import BiluLinial.Tight.Compare.Taylor

/-!
# The scalar endpoint identity behind (E1)

Part D (`docs/second_order_bilu_linial_tight.tex`, Section 1.2, Lemma "Endpoint calculus", proof):
"Taylor's endpoint identity `𝔼_ξ ξ f(ξ) = 𝔼_ξ (f'(ξ) - f'''(ξ)/3) + O(‖f^{(5)}‖_∞)` is exact through
degree four." Here `ξ` is a Rademacher sign. We make the constant explicit: `13/60`.

* `rad_mul_id`: `𝖱[ξ f(ξ)] = (f 1 - f (-1))/2`;
* `endpoint_chain`: for a chain `F 0, …, F 5` of successive derivatives on `[-1, 1]` with
  `|F 5| ≤ M` there, `|𝖱[ξ F₀(ξ)] - (𝖱 F₁ - 𝖱 F₃/3)| ≤ (13/60) M`;
* `endpoint_identity`: the same for `f ∈ C⁵(ℝ)` with `|f^{(5)}| ≤ M` on `[-1, 1]`.

Proof: Taylor-expand `F₀` (degree 4), `F₁` (degree 3) and `F₃` (degree 1) at `0`; the main terms
cancel and the remainders contribute at most `M/120 + M/24 + M/6 = 13M/60`.
-/

@[expose] public section

namespace BiluLinial.Tight

open MeasureTheory Finset Set

/-- `𝖱[ξ f(ξ)] = (f 1 - f (-1))/2`. -/
theorem rad_mul_id (f : ℝ → ℝ) : ∫ t, t * f t ∂radReal = (f 1 - f (-1)) / 2 := by
  rw [integral_radReal]; ring

/-- **Endpoint identity (chain form).** If `F 0, …, F 5` satisfy `(F m)' = F (m+1)` on `[-1, 1]`
for `m < 5` and `|F 5| ≤ M` on `[-1, 1]`, then
`|𝖱[ξ F₀(ξ)] - (𝖱 F₁ - 𝖱 F₃ / 3)| ≤ (13/60) M`. -/
theorem endpoint_chain (F : ℕ → ℝ → ℝ)
    (hF : ∀ m < 5, ∀ t ∈ Icc (-1 : ℝ) 1, HasDerivAt (F m) (F (m + 1) t) t) (M : ℝ)
    (hM : ∀ t ∈ Icc (-1 : ℝ) 1, |F 5 t| ≤ M) :
    |∫ t, t * F 0 t ∂radReal - (∫ t, F 1 t ∂radReal - (∫ t, F 3 t ∂radReal) / 3)| ≤
      13 / 60 * M := by
  have hI : (Icc (-1 : ℝ) 1).OrdConnected := ordConnected_Icc
  have h0 : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have h1 : (1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hm1 : (-1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have T0 := taylor_chain_bound hI h0 5 F hF M hM
  have T1 := taylor_chain_bound hI h0 4 (fun m => F (1 + m))
    (fun m hm t ht => hF (1 + m) (by omega) t ht) M (fun t ht => hM t ht)
  have T3 := taylor_chain_bound hI h0 2 (fun m => F (3 + m))
    (fun m hm t ht => hF (3 + m) (by omega) t ht) M (fun t ht => hM t ht)
  have a := T0 1 h1
  have b := T0 (-1) hm1
  have c := T1 1 h1
  have d := T1 (-1) hm1
  have e := T3 1 h1
  have f := T3 (-1) hm1
  norm_num [Finset.sum_range_succ, Nat.factorial] at a b c d e f
  rw [integral_radReal, integral_radReal, integral_radReal]
  rw [abs_le] at a b c d e f ⊢
  constructor <;> linarith [a.1, a.2, b.1, b.2, c.1, c.2, d.1, d.2, e.1, e.2, f.1, f.2]

/-- **Endpoint identity.** For `f ∈ C⁵(ℝ)` with `|f^{(5)}| ≤ M` on `[-1, 1]`,
`|𝖱[ξ f(ξ)] - (𝖱 f' - 𝖱 f'''/3)| ≤ (13/60) M`. -/
theorem endpoint_identity (f : ℝ → ℝ) (hf : ContDiff ℝ 5 f) (M : ℝ)
    (hM : ∀ t ∈ Icc (-1 : ℝ) 1, |iteratedDeriv 5 f t| ≤ M) :
    |∫ t, t * f t ∂radReal -
        (∫ t, deriv f t ∂radReal - (∫ t, iteratedDeriv 3 f t ∂radReal) / 3)| ≤ 13 / 60 * M := by
  have h := endpoint_chain (fun m => iteratedDeriv m f)
    (fun m hm t _ => by
      have hd := (hf.differentiable_iteratedDeriv m (by exact_mod_cast hm)) t
      rw [iteratedDeriv_succ]
      exact hd.hasDerivAt) M hM
  simpa [iteratedDeriv_one] using h

end BiluLinial.Tight
