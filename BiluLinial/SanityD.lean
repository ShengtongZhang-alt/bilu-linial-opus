/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Sanity
public import BiluLinial.Common.OpNorm
public import BiluLinial.SecondOrder.Explicit.Theorem

/-!
# Sanity checks for the Part D statement `near_ramanujan_signing`

The upper bound of Theorem 1 of `docs/second_order_bilu_linial_tight.tex`,
`γ_{q+1} ≤ √(4q + C q^{-2/17})`, is rendered with `d = q + 1` as `NearRamanujanStatement`, which
is verbatim the Challenge statement `near_ramanujan_signing`. The lemmas below show:

* Equivalent forms. Because `C` is existential, the strict `<` and the paper's `≤` give equivalent
  statements, and so do `d^{-2/17}` and the paper's `(d-1)^{-2/17}`
  (`nearRamanujanStatement_iff_le`, `nearRamanujanStatement_iff_subOne`,
  `nearRamanujanStatement_iff_subOneLt`).
* The exponent: `d^{-2/17}` (`Real.rpow`) is the positive real number whose `17`-th power is
  `1/d²` (`natCast_rpow_neg_two_div_seventeen_pos`, `natCast_rpow_neg_two_div_seventeen_pow`).
* Asymptotics: for `C ≥ 0` and `d ≥ 2` the radius lies between `2√(d-1)` and
  `2√(d-1) + C d^{-2/17} / (4√(d-1)) ≤ 2√(d-1) + C d^{-1/2-2/17}`.
* Strength: the statement implies the Part C upper bound `‖A_σ‖ < 2√d + C d^{1/6}`
  (`secondOrderStatement_of_nearRamanujan`).
* The correction term is needed: by the proved `explicit_excess`, the statement fails for every
  `C ≤ 0`, in particular for `C = 0` (`not_nearRamanujan_const_zero`,
  `not_nearRamanujan_const_nonpos`, `nearRamanujan_const_pos`).
* Non-vacuity: in every universe and for every `d` there is a graph of maximum degree at most `d`
  with a vertex of degree `d` (`exists_graph_degree_eq`); on it every signing has `‖A_σ‖ ≥ √d`,
  so no radius `≤ √d` works (`not_signableBelow_sqrt`). The trivial bound `‖A_σ‖ ≤ d` does not
  give the statement either, since the radius is eventually below `d`
  (`nearRamanujan_radius_lt_self`).
-/

@[expose] public section

namespace BiluLinial

open Matrix

universe u

/-- **Theorem 1, upper bound**, of `docs/second_order_bilu_linial_tight.tex`, verbatim the
Challenge statement `near_ramanujan_signing`. There is an absolute constant `C` such that for every
sufficiently large integer `d` (that is, `d ≥ d₀` for some fixed `d₀`), every finite simple graph
`G` of maximum degree at most `d` has an edge signing `σ` with `‖A_σ‖ < √(4(d-1) + C d^{-2/17})`.
With `q = d - 1` this is the paper's `γ_{q+1} ≤ √(4q + C q^{-2/17})`
(`nearRamanujanStatement_iff_subOne`). -/
def NearRamanujanStatement : Prop :=
  ∃ C : ℝ, ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
    ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      (∀ v, G.degree v ≤ d) →
        ∃ σ : Signing G, opNorm (signedAdjMatrix G σ) <
          Real.sqrt (4 * ((d : ℝ) - 1) + C * (d : ℝ) ^ (-(2 : ℝ) / 17))

/-- `NearRamanujanStatement` with the non-strict `≤` of the paper. -/
def NearRamanujanStatementLe : Prop :=
  ∃ C : ℝ, ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
    ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      (∀ v, G.degree v ≤ d) →
        ∃ σ : Signing G, opNorm (signedAdjMatrix G σ) ≤
          Real.sqrt (4 * ((d : ℝ) - 1) + C * (d : ℝ) ^ (-(2 : ℝ) / 17))

/-- The paper's form `γ_{q+1} ≤ √(4q + C q^{-2/17})` with `q = d - 1`: non-strict `≤` and the
correction `C (d-1)^{-2/17}`. (`γ_d ≤ R` means that every graph of maximum degree at most `d`
has a signing with `‖A_σ‖ ≤ R`, the minimum over the finitely many signings being attained.) -/
def NearRamanujanStatementSubOne : Prop :=
  ∃ C : ℝ, ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
    ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      (∀ v, G.degree v ≤ d) →
        ∃ σ : Signing G, opNorm (signedAdjMatrix G σ) ≤
          Real.sqrt (4 * ((d : ℝ) - 1) + C * ((d : ℝ) - 1) ^ (-(2 : ℝ) / 17))

/-- The strict form with the correction `C (d-1)^{-2/17}`. -/
def NearRamanujanStatementSubOneLt : Prop :=
  ∃ C : ℝ, ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
    ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      (∀ v, G.degree v ≤ d) →
        ∃ σ : Signing G, opNorm (signedAdjMatrix G σ) <
          Real.sqrt (4 * ((d : ℝ) - 1) + C * ((d : ℝ) - 1) ^ (-(2 : ℝ) / 17))

/-- The Part C upper bound (Theorem 1.1 of `docs/second_order_bilu_linial.tex`), verbatim the
Challenge statement `second_order_signing` that `near_ramanujan_signing` replaces:
`‖A_σ‖ < 2√d + C d^{1/6}`. -/
def SecondOrderStatement : Prop :=
  ∃ C : ℝ, ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
    ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      (∀ v, G.degree v ≤ d) →
        ∃ σ : Signing G, opNorm (signedAdjMatrix G σ) <
          2 * Real.sqrt d + C * (d : ℝ) ^ ((1 : ℝ) / 6)

namespace SanityD

/-! ### Helpers: the graph part of the statements, and transfer between radii -/

/-- Every finite simple graph `G` on a type `V : Type u` of maximum degree at most `d` has a
signing with `‖A_σ‖ < r`. -/
def SignableBelow (d : ℕ) (r : ℝ) : Prop :=
  ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    (∀ v, G.degree v ≤ d) → ∃ σ : Signing G, opNorm (signedAdjMatrix G σ) < r

/-- Every finite simple graph `G` on a type `V : Type u` of maximum degree at most `d` has a
signing with `‖A_σ‖ ≤ r`. -/
def SignableAtMost (d : ℕ) (r : ℝ) : Prop :=
  ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    (∀ v, G.degree v ≤ d) → ∃ σ : Signing G, opNorm (signedAdjMatrix G σ) ≤ r

/-- The radius `√(4(d-1) + C d^{-2/17})` of `near_ramanujan_signing`. -/
noncomputable def nrRadius (C : ℝ) (d : ℕ) : ℝ :=
  Real.sqrt (4 * ((d : ℝ) - 1) + C * (d : ℝ) ^ (-(2 : ℝ) / 17))

/-- The paper's radius `√(4q + C q^{-2/17})`, `q = d - 1`. -/
noncomputable def nrRadiusSubOne (C : ℝ) (d : ℕ) : ℝ :=
  Real.sqrt (4 * ((d : ℝ) - 1) + C * ((d : ℝ) - 1) ^ (-(2 : ℝ) / 17))

variable {d : ℕ} {r r' : ℝ}

/-- A larger radius is easier. -/
theorem SignableBelow.mono (H : SignableBelow.{u} d r) (h : r ≤ r') : SignableBelow.{u} d r' := by
  intro V _ _ G _ hG
  obtain ⟨σ, hσ⟩ := H V G hG
  exact ⟨σ, hσ.trans_le h⟩

/-- `<` implies `≤`. -/
theorem SignableBelow.atMost (H : SignableBelow.{u} d r) : SignableAtMost.{u} d r := by
  intro V _ _ G _ hG
  obtain ⟨σ, hσ⟩ := H V G hG
  exact ⟨σ, hσ.le⟩

/-- A larger radius is easier. -/
theorem SignableAtMost.mono (H : SignableAtMost.{u} d r) (h : r ≤ r') :
    SignableAtMost.{u} d r' := by
  intro V _ _ G _ hG
  obtain ⟨σ, hσ⟩ := H V G hG
  exact ⟨σ, hσ.trans h⟩

/-- `≤ r` implies `< r'` for every `r' > r`. -/
theorem SignableAtMost.below (H : SignableAtMost.{u} d r) (h : r < r') :
    SignableBelow.{u} d r' := by
  intro V _ _ G _ hG
  obtain ⟨σ, hσ⟩ := H V G hG
  exact ⟨σ, hσ.trans_lt h⟩

/-- Transfer between statements of the shape `∃ C, ∃ d₀, ∀ d ≥ d₀, P d (b C d)`: it suffices that
every `C` has a `C'` with `P d (b C d) → Q d (b' C' d)` for all large `d`. -/
theorem exists_const_imp {P Q : ℕ → ℝ → Prop} {b b' : ℝ → ℕ → ℝ}
    (h : ∀ C : ℝ, ∃ C' : ℝ, ∃ d₁ : ℕ, ∀ d : ℕ, d₁ ≤ d → P d (b C d) → Q d (b' C' d))
    (H : ∃ C : ℝ, ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → P d (b C d)) :
    ∃ C : ℝ, ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → Q d (b' C d) := by
  obtain ⟨C, d₀, H⟩ := H
  obtain ⟨C', d₁, h⟩ := h C
  exact ⟨C', max d₀ d₁, fun d hd => h d (le_of_max_le_right hd) (H d (le_of_max_le_left hd))⟩

/-! ### Real-number facts about the radius -/

theorem natCast_rpow_nonneg (d : ℕ) : 0 ≤ (d : ℝ) ^ (-(2 : ℝ) / 17) :=
  Real.rpow_nonneg (Nat.cast_nonneg d) _

theorem natCast_rpow_le_one (hd : 1 ≤ d) : (d : ℝ) ^ (-(2 : ℝ) / 17) ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hd) (by norm_num)

theorem mul_natCast_rpow_le_max (hd : 1 ≤ d) (C : ℝ) :
    C * (d : ℝ) ^ (-(2 : ℝ) / 17) ≤ max C 0 :=
  calc C * (d : ℝ) ^ (-(2 : ℝ) / 17) ≤ max C 0 * (d : ℝ) ^ (-(2 : ℝ) / 17) :=
        mul_le_mul_of_nonneg_right (le_max_left C 0) (natCast_rpow_nonneg d)
    _ ≤ max C 0 * 1 := mul_le_mul_of_nonneg_left (natCast_rpow_le_one hd) (le_max_right C 0)
    _ = max C 0 := mul_one _

/-- `d^{-2/17} ≤ (d-1)^{-2/17}` for `d ≥ 2`. -/
theorem natCast_rpow_le_sub_one_rpow (hd : 2 ≤ d) :
    (d : ℝ) ^ (-(2 : ℝ) / 17) ≤ ((d : ℝ) - 1) ^ (-(2 : ℝ) / 17) := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  exact Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by norm_num)

/-- `(d-1)^{-2/17} ≤ 2^{2/17} d^{-2/17} ≤ 2 d^{-2/17}` for `d ≥ 2`. -/
theorem sub_one_rpow_le_two_mul_rpow (hd : 2 ≤ d) :
    ((d : ℝ) - 1) ^ (-(2 : ℝ) / 17) ≤ 2 * (d : ℝ) ^ (-(2 : ℝ) / 17) := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have h1 : ((d : ℝ) - 1) ^ (-(2 : ℝ) / 17) ≤ ((d : ℝ) / 2) ^ (-(2 : ℝ) / 17) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by norm_num)
  have h2 : (d : ℝ) ^ (-(2 : ℝ) / 17) =
      (2 : ℝ) ^ (-(2 : ℝ) / 17) * ((d : ℝ) / 2) ^ (-(2 : ℝ) / 17) := by
    rw [← Real.mul_rpow (by norm_num) (by linarith)]
    congr 1
    ring
  have h3 : (2 : ℝ)⁻¹ ≤ (2 : ℝ) ^ (-(2 : ℝ) / 17) := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have h4 : 0 ≤ ((d : ℝ) / 2) ^ (-(2 : ℝ) / 17) := Real.rpow_nonneg (by linarith) _
  rw [h2]
  nlinarith [mul_le_mul_of_nonneg_right h3 h4]

theorem nrRadius_mono {C C' : ℝ} (h : C ≤ C') (d : ℕ) : nrRadius C d ≤ nrRadius C' d := by
  unfold nrRadius
  exact Real.sqrt_le_sqrt (by linarith [mul_le_mul_of_nonneg_right h (natCast_rpow_nonneg d)])

theorem nrRadiusSubOne_mono {C C' : ℝ} (h : C ≤ C') (hd : 1 ≤ d) :
    nrRadiusSubOne C d ≤ nrRadiusSubOne C' d := by
  unfold nrRadiusSubOne
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hx : 0 ≤ ((d : ℝ) - 1) ^ (-(2 : ℝ) / 17) := Real.rpow_nonneg (by linarith) _
  exact Real.sqrt_le_sqrt (by linarith [mul_le_mul_of_nonneg_right h hx])

/-- Increasing `C ≥ 0` by `1` strictly increases the radius. -/
theorem nrRadius_lt_add_one (hd : 1 ≤ d) {C : ℝ} (hC : 0 ≤ C) :
    nrRadius C d < nrRadius (C + 1) d := by
  unfold nrRadius
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hx : 0 < (d : ℝ) ^ (-(2 : ℝ) / 17) := Real.rpow_pos_of_pos (by linarith) _
  have hCx : 0 ≤ C * (d : ℝ) ^ (-(2 : ℝ) / 17) := mul_nonneg hC hx.le
  exact Real.sqrt_lt_sqrt (by linarith) (by linarith)

theorem nrRadiusSubOne_lt_add_one (hd : 2 ≤ d) {C : ℝ} (hC : 0 ≤ C) :
    nrRadiusSubOne C d < nrRadiusSubOne (C + 1) d := by
  unfold nrRadiusSubOne
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hx : 0 < ((d : ℝ) - 1) ^ (-(2 : ℝ) / 17) := Real.rpow_pos_of_pos (by linarith) _
  have hCx : 0 ≤ C * ((d : ℝ) - 1) ^ (-(2 : ℝ) / 17) := mul_nonneg hC hx.le
  exact Real.sqrt_lt_sqrt (by linarith) (by linarith)

theorem nrRadius_le_nrRadiusSubOne (hd : 2 ≤ d) {C : ℝ} (hC : 0 ≤ C) :
    nrRadius C d ≤ nrRadiusSubOne C d := by
  unfold nrRadius nrRadiusSubOne
  exact Real.sqrt_le_sqrt
    (by linarith [mul_le_mul_of_nonneg_left (natCast_rpow_le_sub_one_rpow hd) hC])

theorem nrRadiusSubOne_le_nrRadius (hd : 2 ≤ d) {C : ℝ} (hC : 0 ≤ C) :
    nrRadiusSubOne C d ≤ nrRadius (2 * C) d := by
  unfold nrRadius nrRadiusSubOne
  exact Real.sqrt_le_sqrt
    (by linarith [mul_le_mul_of_nonneg_left (sub_one_rpow_le_two_mul_rpow hd) hC])

theorem two_mul_sqrt_eq_sqrt (x : ℝ) : 2 * Real.sqrt x = Real.sqrt (4 * x) := by
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4) x, show (4 : ℝ) = 2 ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]

/-- `√(a² + y) ≤ a + y/(2a)` for `a > 0`, `y ≥ 0`. -/
theorem sqrt_sq_add_le {a y : ℝ} (ha : 0 < a) (hy : 0 ≤ y) :
    Real.sqrt (a ^ 2 + y) ≤ a + y / (2 * a) := by
  have ha' : a ≠ 0 := ha.ne'
  have ht : 0 ≤ y / (2 * a) := div_nonneg hy (by linarith)
  have hty : 2 * a * (y / (2 * a)) = y := by field_simp
  rw [Real.sqrt_le_left (by linarith)]
  nlinarith [sq_nonneg (y / (2 * a))]

/-- `√(x + y) ≤ √x + √y` for `x, y ≥ 0`. -/
theorem sqrt_add_le_sqrt_add_sqrt {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy,
    mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)]

/-- The excess of `explicit_excess` is positive, so its threshold exceeds `2√(d-1) = √(4(d-1))`. -/
theorem sqrt_four_mul_lt_excess (hd : 4 ≤ d) :
    Real.sqrt (4 * ((d : ℝ) - 1)) <
      2 * Real.sqrt ((d : ℝ) - 1) + 1 / (25 * ((d : ℝ) - 1) ^ 5 * Real.sqrt ((d : ℝ) - 1)) := by
  have hq : (0 : ℝ) < (d : ℝ) - 1 := by
    have : (4 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hpos : 0 < 1 / (25 * ((d : ℝ) - 1) ^ 5 * Real.sqrt ((d : ℝ) - 1)) :=
    one_div_pos.2 (mul_pos (mul_pos (by norm_num) (pow_pos hq 5)) (Real.sqrt_pos.2 hq))
  rw [← two_mul_sqrt_eq_sqrt]
  linarith

/-! ### Transport of graphs along an equivalence of vertex types (for universe lifting) -/

theorem degree_comap_equiv {V W : Type*} [Fintype V] [Fintype W] (G : SimpleGraph V)
    [DecidableRel G.Adj] (e : W ≃ V) (w : W) : (G.comap e).degree w = G.degree (e w) :=
  ((SimpleGraph.Iso.comap e G).degree_eq w).symm

/-- Every signing of the pulled-back graph `G.comap e` has the norm of some signing of `G`. -/
theorem exists_signing_opNorm_eq_comap {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W]
    [DecidableEq W] (G : SimpleGraph V) [DecidableRel G.Adj] (e : W ≃ V)
    (σ' : Signing (G.comap e)) :
    ∃ σ : Signing G, opNorm (signedAdjMatrix G σ) = opNorm (signedAdjMatrix (G.comap e) σ') := by
  let φ : G.comap e ≃g G := SimpleGraph.Iso.comap e G
  obtain ⟨σ, rfl⟩ : ∃ σ : Signing G, σ' = fun x => σ (φ.mapEdgeSet x) :=
    ⟨fun x => σ' (φ.mapEdgeSet.symm x),
      funext fun x => (congrArg σ' (φ.mapEdgeSet.symm_apply_apply x)).symm⟩
  refine ⟨σ, ?_⟩
  rw [← opNorm_submatrix_equiv (signedAdjMatrix G σ) e]
  congr 1

/-- For `d ≥ 4`, no radius `r` up to the threshold `2√(d-1) + (d-1)^{-11/2}/25` of
`explicit_excess` works in any universe: the graph of `explicit_excess`, lifted to `Type u`, has
no signing of norm `< r`. -/
theorem not_signableBelow_of_le_excess (hd : 4 ≤ d)
    (hr : r ≤ 2 * Real.sqrt ((d : ℝ) - 1) +
      1 / (25 * ((d : ℝ) - 1) ^ 5 * Real.sqrt ((d : ℝ) - 1))) :
    ¬ SignableBelow.{u} d r := by
  intro H
  obtain ⟨V, _, _, G, _, -, hreg, hG⟩ := SecondOrder.Explicit.explicit_excess_thm d hd
  obtain ⟨σ', hσ'⟩ := H (ULift.{u} V) (G.comap (Equiv.ulift : ULift.{u} V ≃ V))
    fun w => (degree_comap_equiv G _ w).trans_le (hreg.degree_eq _).le
  obtain ⟨σ, hσ⟩ := exists_signing_opNorm_eq_comap G _ σ'
  have := hG σ
  linarith

end SanityD

open SanityD

/-! ### Equivalent forms of the statement -/

/-- The strict `<` and the paper's `≤` give equivalent statements (`C` is existential: replace it
by `max C 0 + 1`). -/
theorem nearRamanujanStatement_iff_le :
    NearRamanujanStatement.{u} ↔ NearRamanujanStatementLe.{u} := by
  constructor
  · intro H
    exact exists_const_imp (P := SignableBelow.{u}) (Q := SignableAtMost.{u}) (b := nrRadius)
      (b' := nrRadius) (fun C => ⟨C, 0, fun _ _ h => h.atMost⟩) H
  · intro H
    exact exists_const_imp (P := SignableAtMost.{u}) (Q := SignableBelow.{u}) (b := nrRadius)
      (b' := nrRadius)
      (fun C => ⟨max C 0 + 1, 1, fun d hd h => h.below
        ((nrRadius_mono (le_max_left C 0) d).trans_lt (nrRadius_lt_add_one hd (le_max_right C 0)))⟩)
      H

/-- With `≤`, the corrections `C d^{-2/17}` and `C (d-1)^{-2/17}` give equivalent statements,
since `d^{-2/17} ≤ (d-1)^{-2/17} ≤ 2 d^{-2/17}` for `d ≥ 2`. -/
theorem nearRamanujanStatementLe_iff_subOne :
    NearRamanujanStatementLe.{u} ↔ NearRamanujanStatementSubOne.{u} := by
  constructor
  · intro H
    exact exists_const_imp (P := SignableAtMost.{u}) (Q := SignableAtMost.{u}) (b := nrRadius)
      (b' := nrRadiusSubOne)
      (fun C => ⟨max C 0, 2, fun d hd h => h.mono ((nrRadius_mono (le_max_left C 0) d).trans
        (nrRadius_le_nrRadiusSubOne hd (le_max_right C 0)))⟩) H
  · intro H
    exact exists_const_imp (P := SignableAtMost.{u}) (Q := SignableAtMost.{u})
      (b := nrRadiusSubOne) (b' := nrRadius)
      (fun C => ⟨2 * max C 0, 2, fun d hd h => h.mono
        ((nrRadiusSubOne_mono (le_max_left C 0) (by omega)).trans
          (nrRadiusSubOne_le_nrRadius hd (le_max_right C 0)))⟩) H

/-- `near_ramanujan_signing` is equivalent to the paper's form `γ_{q+1} ≤ √(4q + C q^{-2/17})`,
`q = d - 1`. -/
theorem nearRamanujanStatement_iff_subOne :
    NearRamanujanStatement.{u} ↔ NearRamanujanStatementSubOne.{u} :=
  nearRamanujanStatement_iff_le.trans nearRamanujanStatementLe_iff_subOne

/-- `near_ramanujan_signing` is equivalent to the strict form with `(d-1)^{-2/17}`. -/
theorem nearRamanujanStatement_iff_subOneLt :
    NearRamanujanStatement.{u} ↔ NearRamanujanStatementSubOneLt.{u} := by
  rw [nearRamanujanStatement_iff_subOne]
  constructor
  · intro H
    exact exists_const_imp (P := SignableAtMost.{u}) (Q := SignableBelow.{u})
      (b := nrRadiusSubOne) (b' := nrRadiusSubOne)
      (fun C => ⟨max C 0 + 1, 2, fun d hd h => h.below
        ((nrRadiusSubOne_mono (le_max_left C 0) (by omega)).trans_lt
          (nrRadiusSubOne_lt_add_one hd (le_max_right C 0)))⟩) H
  · intro H
    exact exists_const_imp (P := SignableBelow.{u}) (Q := SignableAtMost.{u})
      (b := nrRadiusSubOne) (b' := nrRadiusSubOne) (fun C => ⟨C, 0, fun _ _ h => h.atMost⟩) H

/-! ### The exponent and the asymptotics of the radius -/

/-- `d^{-2/17}` is positive for `d ≥ 1` (no junk value of `Real.rpow`: the base is positive). -/
theorem natCast_rpow_neg_two_div_seventeen_pos {d : ℕ} (hd : 1 ≤ d) :
    0 < (d : ℝ) ^ (-(2 : ℝ) / 17) :=
  Real.rpow_pos_of_pos (Nat.cast_pos.2 (by omega)) _

/-- `(d^{-2/17})^{17} = 1/d²`: `d^{-2/17}` is the intended real power. -/
theorem natCast_rpow_neg_two_div_seventeen_pow (d : ℕ) :
    ((d : ℝ) ^ (-(2 : ℝ) / 17)) ^ 17 = 1 / (d : ℝ) ^ 2 := by
  rw [← Real.rpow_natCast _ 17, ← Real.rpow_mul (Nat.cast_nonneg d),
    show -(2 : ℝ) / 17 * ((17 : ℕ) : ℝ) = -((2 : ℕ) : ℝ) by norm_num,
    Real.rpow_neg (Nat.cast_nonneg d), Real.rpow_natCast, one_div]

/-- Lower end: for `C ≥ 0` the radius is at least the Ramanujan value `2√(d-1)`. -/
theorem two_sqrt_sub_one_le_nearRamanujan_radius (d : ℕ) {C : ℝ} (hC : 0 ≤ C) :
    2 * Real.sqrt ((d : ℝ) - 1) ≤
      Real.sqrt (4 * ((d : ℝ) - 1) + C * (d : ℝ) ^ (-(2 : ℝ) / 17)) := by
  rw [two_mul_sqrt_eq_sqrt]
  exact Real.sqrt_le_sqrt (le_add_of_nonneg_right (mul_nonneg hC (natCast_rpow_nonneg d)))

/-- Upper end: for `C ≥ 0` and `d ≥ 2`,
`√(4(d-1) + C d^{-2/17}) ≤ 2√(d-1) + C d^{-2/17}/(4√(d-1))`. -/
theorem nearRamanujan_radius_le {d : ℕ} (hd : 2 ≤ d) {C : ℝ} (hC : 0 ≤ C) :
    Real.sqrt (4 * ((d : ℝ) - 1) + C * (d : ℝ) ^ (-(2 : ℝ) / 17)) ≤
      2 * Real.sqrt ((d : ℝ) - 1) +
        C * (d : ℝ) ^ (-(2 : ℝ) / 17) / (4 * Real.sqrt ((d : ℝ) - 1)) := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hq : 0 < Real.sqrt ((d : ℝ) - 1) := Real.sqrt_pos.2 (by linarith)
  have h := sqrt_sq_add_le (a := 2 * Real.sqrt ((d : ℝ) - 1))
    (y := C * (d : ℝ) ^ (-(2 : ℝ) / 17)) (by linarith) (mul_nonneg hC (natCast_rpow_nonneg d))
  have e1 : (2 * Real.sqrt ((d : ℝ) - 1)) ^ 2 = 4 * ((d : ℝ) - 1) := by
    rw [mul_pow, Real.sq_sqrt (by linarith)]
    norm_num
  have e2 : 2 * (2 * Real.sqrt ((d : ℝ) - 1)) = 4 * Real.sqrt ((d : ℝ) - 1) := by ring
  rwa [e1, e2] at h

/-- The radius is `2√(d-1) + O(d^{-1/2-2/17})`: for `C ≥ 0` and `d ≥ 2`,
`√(4(d-1) + C d^{-2/17}) ≤ 2√(d-1) + C d^{-2/17-1/2}`. -/
theorem nearRamanujan_radius_le_rpow {d : ℕ} (hd : 2 ≤ d) {C : ℝ} (hC : 0 ≤ C) :
    Real.sqrt (4 * ((d : ℝ) - 1) + C * (d : ℝ) ^ (-(2 : ℝ) / 17)) ≤
      2 * Real.sqrt ((d : ℝ) - 1) + C * (d : ℝ) ^ (-(2 : ℝ) / 17 - 1 / 2) := by
  refine (nearRamanujan_radius_le hd hC).trans (add_le_add le_rfl ?_)
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  have hs : Real.sqrt (d : ℝ) ≤ 4 * Real.sqrt ((d : ℝ) - 1) := by
    rw [Real.sqrt_le_left (by positivity), mul_pow, Real.sq_sqrt (by linarith)]
    linarith
  have e3 : (d : ℝ) ^ (-(2 : ℝ) / 17 - 1 / 2) =
      (d : ℝ) ^ (-(2 : ℝ) / 17) / Real.sqrt (d : ℝ) := by
    rw [Real.rpow_sub hdpos, Real.sqrt_eq_rpow]
  rw [e3, ← mul_div_assoc]
  exact div_le_div_of_nonneg_left (mul_nonneg hC (natCast_rpow_nonneg d))
    (Real.sqrt_pos.2 hdpos) hs

/-- The statement is not implied by the trivial bound `‖A_σ‖ ≤ d`
(`opNorm_signedAdjMatrix_le_of_degree_le`): for every `C`, the radius is eventually below `d`. -/
theorem nearRamanujan_radius_lt_self (C : ℝ) : ∃ d₁ : ℕ, ∀ d : ℕ, d₁ ≤ d →
    Real.sqrt (4 * ((d : ℝ) - 1) + C * (d : ℝ) ^ (-(2 : ℝ) / 17)) < d := by
  refine ⟨⌈max C 0⌉₊ + 3, fun d hd => ?_⟩
  have hK : max C 0 ≤ ⌈max C 0⌉₊ := Nat.le_ceil _
  have hN : (0 : ℝ) ≤ ⌈max C 0⌉₊ := Nat.cast_nonneg _
  have hd' : ((⌈max C 0⌉₊ + 3 : ℕ) : ℝ) ≤ d := by exact_mod_cast hd
  push_cast at hd'
  have hCx := mul_natCast_rpow_le_max (d := d) (by omega) C
  have h2 : (1 : ℝ) ≤ (d : ℝ) - 2 := by linarith
  have h3 : ((d : ℝ) - 2) * 1 ≤ ((d : ℝ) - 2) * ((d : ℝ) - 2) :=
    mul_le_mul_of_nonneg_left h2 (by linarith)
  rw [Real.sqrt_lt' (by linarith)]
  nlinarith

/-! ### Strength: the new statement implies the Part C upper bound -/

theorem nearRamanujan_radius_le_secondOrder {d : ℕ} (hd : 1 ≤ d) (C : ℝ) :
    Real.sqrt (4 * ((d : ℝ) - 1) + C * (d : ℝ) ^ (-(2 : ℝ) / 17)) ≤
      2 * Real.sqrt d + Real.sqrt (max C 0) * (d : ℝ) ^ ((1 : ℝ) / 6) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hK : 0 ≤ max C 0 := le_max_right C 0
  have hCx := mul_natCast_rpow_le_max hd C
  have h6 : (1 : ℝ) ≤ (d : ℝ) ^ ((1 : ℝ) / 6) := Real.one_le_rpow hd1 (by norm_num)
  calc Real.sqrt (4 * ((d : ℝ) - 1) + C * (d : ℝ) ^ (-(2 : ℝ) / 17))
      ≤ Real.sqrt (4 * (d : ℝ) + max C 0) := Real.sqrt_le_sqrt (by linarith)
    _ ≤ Real.sqrt (4 * (d : ℝ)) + Real.sqrt (max C 0) :=
        sqrt_add_le_sqrt_add_sqrt (by positivity) hK
    _ = 2 * Real.sqrt d + Real.sqrt (max C 0) := by rw [two_mul_sqrt_eq_sqrt]
    _ ≤ 2 * Real.sqrt d + Real.sqrt (max C 0) * (d : ℝ) ^ ((1 : ℝ) / 6) := by
        nlinarith [mul_le_mul_of_nonneg_left h6 (Real.sqrt_nonneg (max C 0))]

/-- `near_ramanujan_signing` implies the Part C upper bound `second_order_signing`
(`‖A_σ‖ < 2√d + C' d^{1/6}`, with `C' = √(max C 0)`), so the new statement is stronger. -/
theorem secondOrderStatement_of_nearRamanujan (H : NearRamanujanStatement.{u}) :
    SecondOrderStatement.{u} :=
  exists_const_imp (P := SignableBelow.{u}) (Q := SignableBelow.{u}) (b := nrRadius)
    (b' := fun C d => 2 * Real.sqrt d + C * (d : ℝ) ^ ((1 : ℝ) / 6))
    (fun C => ⟨Real.sqrt (max C 0), 1, fun _ hd h =>
      h.mono (nearRamanujan_radius_le_secondOrder hd C)⟩) H

/-! ### The correction term is necessary -/

/-- The statement with `C = 0`, `‖A_σ‖ < √(4(d-1)) = 2√(d-1)` for all large `d`, is false: the
proved `explicit_excess` gives, for every `d ≥ 4`, a connected `d`-regular graph all of whose
signings have `‖A_σ‖ ≥ 2√(d-1) + (d-1)^{-11/2}/25`. -/
theorem not_nearRamanujan_const_zero :
    ¬ ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
      ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        (∀ v, G.degree v ≤ d) →
          ∃ σ : Signing G, opNorm (signedAdjMatrix G σ) < Real.sqrt (4 * ((d : ℝ) - 1)) := by
  rintro ⟨d₀, H⟩
  have hd : 4 ≤ max d₀ 4 := le_max_right _ _
  exact not_signableBelow_of_le_excess.{u} (r := Real.sqrt (4 * (((max d₀ 4 : ℕ) : ℝ) - 1))) hd
    (sqrt_four_mul_lt_excess hd).le (H _ (le_max_left _ _))

/-- More generally, the statement fails for every fixed `C ≤ 0`. -/
theorem not_nearRamanujan_const_nonpos {C : ℝ} (hC : C ≤ 0) :
    ¬ ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
      ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        (∀ v, G.degree v ≤ d) →
          ∃ σ : Signing G, opNorm (signedAdjMatrix G σ) <
            Real.sqrt (4 * ((d : ℝ) - 1) + C * (d : ℝ) ^ (-(2 : ℝ) / 17)) := by
  rintro ⟨d₀, H⟩
  have hd : 4 ≤ max d₀ 4 := le_max_right _ _
  have hx := natCast_rpow_nonneg (max d₀ 4)
  have hle : Real.sqrt (4 * (((max d₀ 4 : ℕ) : ℝ) - 1) +
      C * ((max d₀ 4 : ℕ) : ℝ) ^ (-(2 : ℝ) / 17)) ≤ Real.sqrt (4 * (((max d₀ 4 : ℕ) : ℝ) - 1)) :=
    Real.sqrt_le_sqrt (by nlinarith)
  exact not_signableBelow_of_le_excess.{u} hd (hle.trans (sqrt_four_mul_lt_excess hd).le)
    (H _ (le_max_left _ _))

/-- Every constant `C` that witnesses `near_ramanujan_signing` is positive. -/
theorem nearRamanujan_const_pos {C : ℝ} {d₀ : ℕ}
    (H : ∀ d : ℕ, d₀ ≤ d →
      ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        (∀ v, G.degree v ≤ d) →
          ∃ σ : Signing G, opNorm (signedAdjMatrix G σ) <
            Real.sqrt (4 * ((d : ℝ) - 1) + C * (d : ℝ) ^ (-(2 : ℝ) / 17))) :
    0 < C := by
  by_contra hC
  exact not_nearRamanujan_const_nonpos.{u} (not_lt.mp hC) ⟨d₀, H⟩

/-! ### Non-vacuity -/

/-- In every universe and for every `d`, the hypotheses are satisfiable by a graph with a vertex
of degree exactly `d`: the complete graph on `d + 1` vertices (lifted to `Type u`). -/
theorem exists_graph_degree_eq (d : ℕ) :
    ∃ (V : Type u) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V)
      (_ : DecidableRel G.Adj), (∀ v, G.degree v ≤ d) ∧ ∃ v, G.degree v = d := by
  have h : (⊤ : SimpleGraph (ULift.{u} (Fin (d + 1)))).IsRegularOfDegree d := by
    have h := SimpleGraph.IsRegularOfDegree.top (V := ULift.{u} (Fin (d + 1)))
    rwa [Fintype.card_ulift, Fintype.card_fin, Nat.add_sub_cancel] at h
  exact ⟨ULift.{u} (Fin (d + 1)), inferInstance, inferInstance, ⊤, inferInstance,
    fun v => (h.degree_eq v).le, ⟨ULift.up 0, h.degree_eq _⟩⟩

/-- A vertex of degree `d` forces `‖A_σ‖ ≥ √d` for every signing. -/
theorem sqrt_le_opNorm_of_degree_eq {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {d : ℕ} {v : V} (hv : G.degree v = d) (σ : Signing G) :
    Real.sqrt d ≤ opNorm (signedAdjMatrix G σ) := by
  rw [← hv]
  exact sqrt_degree_le_opNorm G σ v

/-- The conclusion is a genuine restriction: for every `d`, no radius `≤ √d` works. So the
statement says that the radius may be taken near `2√(d-1)`, between this lower limit `√d` and the
trivial bound `d`. -/
theorem not_signableBelow_sqrt (d : ℕ) : ¬ SignableBelow.{u} d (Real.sqrt d) := by
  intro H
  obtain ⟨V, _, _, G, _, hG, v, hv⟩ := exists_graph_degree_eq.{u} d
  obtain ⟨σ, hσ⟩ := H V G hG
  exact absurd (sqrt_le_opNorm_of_degree_eq G hv σ) (not_le.mpr hσ)

/-- The trivial bound: every graph of maximum degree at most `d` has a signing with `‖A_σ‖ ≤ d`
(any signing). -/
theorem signableAtMost_self (d : ℕ) : SignableAtMost.{u} d d := by
  intro V _ _ G _ hG
  exact ⟨fun _ => 1, opNorm_signedAdjMatrix_le_of_degree_le G _ hG⟩

end BiluLinial
