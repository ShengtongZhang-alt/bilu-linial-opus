/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Common.Spectral

/-!
# Sanity checks for the statement surface

These lemmas show that the definitions of `Challenge.lean` mean what the sources say, and that
the three main statements are neither vacuous nor trivially true.

* `opNorm` is the Euclidean operator norm (the least `c` with `‖M x‖₂ ≤ c ‖x‖₂`), and for a
  symmetric matrix it is the largest absolute value of an eigenvalue.
* `signedAdjMatrix` is symmetric, has zero diagonal, has entries `±1` exactly on edges (namely
  `σ(uv)`), and the all-`+1` signing gives the ordinary adjacency matrix.
* A signing is exactly a choice of sign for each edge: there are `2 ^ |E|` of them.
* The degree hypotheses are the intended ones.
* Non-vacuity: every `d` admits graphs of maximum degree `d` (complete graphs), every signing has
  `‖A_σ‖ ≥ √(deg v)`, and `‖A_σ‖ ≤ d` when the maximum degree is at most `d`. In particular the
  conclusion of Theorem B fails for every `2`-regular graph, while complete graphs witness that its
  hypotheses (finite, connected, `d`-regular) are satisfiable for every `d`.
-/

@[expose] public section

namespace BiluLinial

open Matrix

section OperatorNorm

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- The Euclidean norm of `y ∈ EuclideanSpace ℝ V` is `√(y ⬝ᵥ y)`. -/
theorem norm_euclideanSpace_eq_sqrt (y : EuclideanSpace ℝ V) :
    ‖y‖ = Real.sqrt (WithLp.ofLp y ⬝ᵥ WithLp.ofLp y) := by
  have h : WithLp.ofLp y ⬝ᵥ WithLp.ofLp y = ‖y‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  rw [h, Real.sqrt_sq (norm_nonneg y)]

/-- `‖M x‖₂ ≤ opNorm M · ‖x‖₂`. -/
theorem sqrt_mulVec_le_opNorm_mul (M : Matrix V V ℝ) (x : V → ℝ) :
    Real.sqrt ((M *ᵥ x) ⬝ᵥ (M *ᵥ x)) ≤ opNorm M * Real.sqrt (x ⬝ᵥ x) := by
  have h := (toEuclideanCLM (n := V) (𝕜 := ℝ) M).le_opNorm (WithLp.toLp 2 x)
  rw [norm_euclideanSpace_eq_sqrt (toEuclideanCLM (n := V) (𝕜 := ℝ) M (WithLp.toLp 2 x)),
    norm_euclideanSpace_eq_sqrt (WithLp.toLp 2 x), ofLp_toEuclideanCLM, WithLp.ofLp_toLp] at h
  exact h

/-- `opNorm M` is the least such constant. -/
theorem opNorm_le_of_forall_sqrt_mulVec_le (M : Matrix V V ℝ) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x : V → ℝ, Real.sqrt ((M *ᵥ x) ⬝ᵥ (M *ᵥ x)) ≤ c * Real.sqrt (x ⬝ᵥ x)) :
    opNorm M ≤ c := by
  unfold opNorm
  refine ContinuousLinearMap.opNorm_le_bound _ hc fun y => ?_
  rw [norm_euclideanSpace_eq_sqrt (toEuclideanCLM (n := V) (𝕜 := ℝ) M y),
    norm_euclideanSpace_eq_sqrt y, ofLp_toEuclideanCLM]
  exact h (WithLp.ofLp y)

/-- A Schur-test bound: if every entry `a` of `A` satisfies `|a| a = a` (that is, `a ∈ {0, ±1}`)
and every row and every column has squared length at most `d`, then `‖A‖ ≤ d`. -/
theorem opNorm_le_of_sum_sq_le {A : Matrix V V ℝ} {d : ℝ} (hd : 0 ≤ d)
    (habs : ∀ u w, |A u w| * A u w = A u w)
    (hrow : ∀ u, ∑ w, A u w ^ 2 ≤ d) (hcol : ∀ w, ∑ u, A u w ^ 2 ≤ d) : opNorm A ≤ d := by
  refine opNorm_le_of_forall_sqrt_mulVec_le A hd fun x => ?_
  have hr : ∀ u, (A *ᵥ x) u ^ 2 ≤ d * ∑ w, A u w ^ 2 * x w ^ 2 := by
    intro u
    have cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun w => |A u w|)
      (fun w => A u w * x w)
    have e1 : ∑ w, |A u w| * (A u w * x w) = (A *ᵥ x) u := by
      have e : (A *ᵥ x) u = ∑ w, A u w * x w := rfl
      rw [e]
      exact Finset.sum_congr rfl fun w _ => by rw [← mul_assoc, habs]
    simp only [sq_abs, mul_pow, e1] at cs
    exact cs.trans (mul_le_mul_of_nonneg_right (hrow u)
      (Finset.sum_nonneg fun w _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)))
  have hs : (A *ᵥ x) ⬝ᵥ (A *ᵥ x) ≤ d ^ 2 * (x ⬝ᵥ x) := by
    calc (A *ᵥ x) ⬝ᵥ (A *ᵥ x) = ∑ u, (A *ᵥ x) u ^ 2 := by simp only [dotProduct, sq]
      _ ≤ ∑ u, d * ∑ w, A u w ^ 2 * x w ^ 2 := Finset.sum_le_sum fun u _ => hr u
      _ = d * ∑ w, (∑ u, A u w ^ 2) * x w ^ 2 := by
          rw [← Finset.mul_sum, Finset.sum_comm]
          simp only [Finset.sum_mul]
      _ ≤ d * ∑ w, d * x w ^ 2 :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_right (hcol w) (sq_nonneg _)) hd
      _ = d ^ 2 * (x ⬝ᵥ x) := by
          rw [← Finset.mul_sum, ← mul_assoc, ← sq]
          congr 1
          simp only [dotProduct, sq]
  calc Real.sqrt ((A *ᵥ x) ⬝ᵥ (A *ᵥ x)) ≤ Real.sqrt (d ^ 2 * (x ⬝ᵥ x)) := Real.sqrt_le_sqrt hs
    _ = d * Real.sqrt (x ⬝ᵥ x) := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hd]

end OperatorNorm

section SignedAdjacency

variable {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] (σ : Signing G)

theorem signedAdjMatrix_apply (u v : V) :
    signedAdjMatrix G σ u v = if h : G.Adj u v then ((σ ⟨s(u, v), h⟩ : ℤ) : ℝ) else 0 :=
  rfl

omit [DecidableRel G.Adj] in
theorem signing_swap {u v : V} (h : G.Adj u v) : σ ⟨s(v, u), h.symm⟩ = σ ⟨s(u, v), h⟩ :=
  congrArg σ (Subtype.ext Sym2.eq_swap)

theorem signedAdjMatrix_isSymm : (signedAdjMatrix G σ).IsSymm := by
  refine IsSymm.ext fun u v => ?_
  by_cases h : G.Adj u v
  · rw [signedAdjMatrix_apply, signedAdjMatrix_apply, dite_eq_left h, dite_eq_left h.symm,
      signing_swap G σ h]
  · rw [signedAdjMatrix_apply, signedAdjMatrix_apply, dite_eq_right h, dite_eq_right (fun h' => h h'.symm)]

theorem signedAdjMatrix_isHermitian : (signedAdjMatrix G σ).IsHermitian :=
  isHermitian_iff_isSymm.mpr (signedAdjMatrix_isSymm G σ)

theorem signedAdjMatrix_apply_self (v : V) : signedAdjMatrix G σ v v = 0 := by
  rw [signedAdjMatrix_apply, dite_eq_right G.irrefl]

theorem signedAdjMatrix_apply_of_adj {u v : V} (h : G.Adj u v) :
    signedAdjMatrix G σ u v = ((σ ⟨s(u, v), h⟩ : ℤ) : ℝ) := by
  rw [signedAdjMatrix_apply, dite_eq_left h]

theorem signedAdjMatrix_apply_of_not_adj {u v : V} (h : ¬ G.Adj u v) :
    signedAdjMatrix G σ u v = 0 := by
  rw [signedAdjMatrix_apply, dite_eq_right h]

/-- The entries are `±1` exactly on the edges. -/
theorem signedAdjMatrix_apply_eq_one_or_neg_one_iff (u v : V) :
    (signedAdjMatrix G σ u v = 1 ∨ signedAdjMatrix G σ u v = -1) ↔ G.Adj u v := by
  by_cases h : G.Adj u v
  · rw [signedAdjMatrix_apply_of_adj G σ h]
    simp only [h, iff_true]
    rcases Int.units_eq_one_or (σ ⟨s(u, v), h⟩) with h1 | h1 <;> simp [h1]
  · rw [signedAdjMatrix_apply_of_not_adj G σ h]
    simp [h]

/-- The all-`+1` signing gives the ordinary adjacency matrix. -/
theorem signedAdjMatrix_one : signedAdjMatrix G (fun _ => 1) = G.adjMatrix ℝ := by
  ext u v
  by_cases h : G.Adj u v
  · rw [signedAdjMatrix_apply_of_adj G _ h, SimpleGraph.adjMatrix_apply, ite_eq_left h]
    simp
  · rw [signedAdjMatrix_apply_of_not_adj G _ h, SimpleGraph.adjMatrix_apply, ite_eq_right h]

/-- Negating a signing negates its matrix. -/
theorem signedAdjMatrix_neg : signedAdjMatrix G (fun e => -σ e) = -signedAdjMatrix G σ := by
  ext u v
  by_cases h : G.Adj u v
  · rw [Matrix.neg_apply, signedAdjMatrix_apply_of_adj G (fun e => -σ e) h,
      signedAdjMatrix_apply_of_adj G σ h]
    simp
  · rw [Matrix.neg_apply, signedAdjMatrix_apply_of_not_adj G (fun e => -σ e) h,
      signedAdjMatrix_apply_of_not_adj G σ h, neg_zero]

/-- A signing is a free choice of sign on every edge. -/
theorem card_signing [Fintype V] [DecidableEq V] :
    Fintype.card (Signing G) = 2 ^ G.edgeFinset.card := by
  rw [Fintype.card_fun, Fintype.card_units_int, SimpleGraph.edgeFinset_card]

/-- The diagonal of `A_σ²` is the degree sequence. -/
theorem sq_signedAdjMatrix_apply_self [Fintype V] [DecidableEq V] (v : V) :
    (signedAdjMatrix G σ ^ 2) v v = G.degree v := by
  rw [sq, Matrix.mul_apply, ← G.adjMatrix_mul_self_apply_self (α := ℝ) v, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun w _ => ?_
  by_cases h : G.Adj v w
  · rw [signedAdjMatrix_apply_of_adj G σ h, signedAdjMatrix_apply_of_adj G σ h.symm,
      signing_swap G σ h, SimpleGraph.adjMatrix_apply, SimpleGraph.adjMatrix_apply, ite_eq_left h,
      ite_eq_left h.symm, mul_one, ← Int.cast_mul, Int.units_coe_mul_self, Int.cast_one]
  · rw [signedAdjMatrix_apply_of_not_adj G σ h, SimpleGraph.adjMatrix_apply, ite_eq_right h, zero_mul,
      zero_mul]

/-- Each row of `A_σ` has squared length `deg u`. -/
theorem sum_sq_signedAdjMatrix_row [Fintype V] [DecidableEq V] (u : V) :
    ∑ w, signedAdjMatrix G σ u w ^ 2 = G.degree u := by
  rw [← sq_signedAdjMatrix_apply_self G σ u, sq (signedAdjMatrix G σ), Matrix.mul_apply]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [sq, (signedAdjMatrix_isSymm G σ).apply u w]

/-- Each column of `A_σ` has squared length `deg w`. -/
theorem sum_sq_signedAdjMatrix_col [Fintype V] [DecidableEq V] (w : V) :
    ∑ u, signedAdjMatrix G σ u w ^ 2 = G.degree w := by
  rw [← sum_sq_signedAdjMatrix_row G σ w]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [(signedAdjMatrix_isSymm G σ).apply u w]

/-- Every entry `a` of `A_σ` lies in `{0, ±1}`, so `|a| a = a`. -/
theorem abs_mul_signedAdjMatrix_apply (u w : V) :
    |signedAdjMatrix G σ u w| * signedAdjMatrix G σ u w = signedAdjMatrix G σ u w := by
  by_cases h : G.Adj u w
  · rw [signedAdjMatrix_apply_of_adj G σ h]
    rcases Int.units_eq_one_or (σ ⟨s(u, w), h⟩) with h1 | h1 <;> simp [h1]
  · rw [signedAdjMatrix_apply_of_not_adj G σ h, mul_zero]

/-- For a symmetric matrix the norm is the largest absolute value of an eigenvalue. -/
theorem opNorm_signedAdjMatrix_eq_sup_abs_eigenvalues [Fintype V] [DecidableEq V] [Nonempty V] :
    opNorm (signedAdjMatrix G σ) =
      Finset.univ.sup' Finset.univ_nonempty
        (fun i => |(signedAdjMatrix_isHermitian G σ).eigenvalues i|) :=
  opNorm_eq_sup_abs_eigenvalues (signedAdjMatrix_isHermitian G σ)

/-- Lower bound `‖A_σ‖ ≥ √(deg v)`: no signing beats `√d` on a graph with a vertex of degree `d`,
so the bounds `(2 + γ) √d` are sharp up to a constant factor. -/
theorem sqrt_degree_le_opNorm [Fintype V] [DecidableEq V] (v : V) :
    Real.sqrt (G.degree v) ≤ opNorm (signedAdjMatrix G σ) := by
  have h := sqrt_mulVec_le_opNorm_mul (signedAdjMatrix G σ) (Pi.single v 1)
  have h1 : (signedAdjMatrix G σ *ᵥ Pi.single v 1) ⬝ᵥ (signedAdjMatrix G σ *ᵥ Pi.single v 1) =
      G.degree v := by
    rw [mulVec_single_one, ← sum_sq_signedAdjMatrix_col G σ v]
    simp only [dotProduct, col_apply, sq]
  have h2 : (Pi.single v 1 : V → ℝ) ⬝ᵥ Pi.single v 1 = 1 := by
    rw [dotProduct_single, Pi.single_eq_same, mul_one]
  rwa [h1, h2, Real.sqrt_one, mul_one] at h

/-- Trivial upper bound `‖A_σ‖ ≤ d` for maximum degree at most `d`. -/
theorem opNorm_signedAdjMatrix_le_of_degree_le [Fintype V] [DecidableEq V] {d : ℕ}
    (h : ∀ v, G.degree v ≤ d) : opNorm (signedAdjMatrix G σ) ≤ d :=
  opNorm_le_of_sum_sq_le (Nat.cast_nonneg d) (abs_mul_signedAdjMatrix_apply G σ)
    (fun u => (sum_sq_signedAdjMatrix_row G σ u).trans_le (by exact_mod_cast h u))
    (fun w => (sum_sq_signedAdjMatrix_col G σ w).trans_le (by exact_mod_cast h w))

end SignedAdjacency

section Hypotheses

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- "Maximum degree at most `d`" in the form used by Theorems 1.1 and 1.2. -/
theorem forall_degree_le_iff_maxDegree_le (d : ℕ) :
    (∀ v, G.degree v ≤ d) ↔ G.maxDegree ≤ d :=
  ⟨G.maxDegree_le_of_forall_degree_le d, fun h v => (G.degree_le_maxDegree v).trans h⟩

omit [DecidableEq V] in
/-- `d`-regularity in the form used by Theorem B. -/
theorem isRegularOfDegree_iff (d : ℕ) : G.IsRegularOfDegree d ↔ ∀ v, G.degree v = d :=
  Iff.rfl

/-- The complete graph on `d + 1` vertices is connected and `d`-regular; in particular the
hypotheses of all three theorems are satisfiable for every `d`. -/
theorem complete_graph_connected_regular (d : ℕ) :
    (⊤ : SimpleGraph (Fin (d + 1))).Connected ∧
      (⊤ : SimpleGraph (Fin (d + 1))).IsRegularOfDegree d := by
  refine ⟨SimpleGraph.connected_top, ?_⟩
  have h := SimpleGraph.IsRegularOfDegree.top (V := Fin (d + 1))
  rwa [Fintype.card_fin, Nat.add_sub_cancel] at h

/-- The conclusion of Theorem B fails for every `2`-regular graph (Bilu–Linial holds for `d = 2`),
so the hypothesis `3 ≤ d` of `bilu_linial_counterexample` is needed. -/
theorem not_theoremB_conclusion_two (h : G.IsRegularOfDegree 2) (σ : Signing G) :
    ¬ (2 * Real.sqrt ((2 : ℕ) - 1 : ℝ) < opNorm (signedAdjMatrix G σ)) := by
  have h2 := opNorm_signedAdjMatrix_le_of_degree_le G σ (d := 2) fun v => (h v).le
  have e : 2 * Real.sqrt ((2 : ℕ) - 1 : ℝ) = ((2 : ℕ) : ℝ) := by norm_num
  rw [e]
  exact not_lt.mpr h2

end Hypotheses

end BiluLinial
