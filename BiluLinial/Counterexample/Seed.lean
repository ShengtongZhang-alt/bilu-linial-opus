/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Counterexample.Tree
public import BiluLinial.Counterexample.Seed4
public import BiluLinial.Counterexample.SeedNumeric

/-!
# The seed responses

Blueprint node `B-seed` (source Steps 2 and 6, Xu Lemma 3.4). For every signed adjacency matrix
`A` of the seed `H_h`: `r I - A ≻ 0`, and the two responses satisfy
`g(H_h, A) + g(H_h, -A) = u₁ + u₋₁` (`seedResp`, evaluated at the tree response `g_h`).
Positive definiteness is obtained directly from the Schur complements (instead of Xu's
unicyclic Lemma 6.1(i)).
-/

@[expose] public section

namespace BiluLinial.Counterexample

open Matrix

/-- The vertex type of `seed n h`. -/
local notation "SeedV" n:max h:max =>
  Fin 4 ⊕ (RGraph.V (tree n h) × (Σ c : Fin 4, Fin (seedMult n c)))

private theorem seed_card_filter_fst {α : Type} [Fintype α] [DecidableEq α] (β : α → Type)
    [∀ a, Fintype (β a)] (a : α) :
    (Finset.univ.filter fun i : Sigma β => i.1 = a).card = Fintype.card (β a) := by
  have : (Finset.univ.filter fun i : Sigma β => i.1 = a) =
      ({a} : Finset α).sigma fun _ => Finset.univ := by
    ext ⟨a', b⟩
    simp
  rw [this, Finset.card_sigma]
  simp

/-- The sign `τ = A₂₃ A₁₂ A₁₃` of the triangle of the seed is `±1`. -/
theorem seed_tau (n h : ℕ)
    {A : Matrix (SeedV n h) (SeedV n h) ℝ}
    (hA : IsSignedAdj (attachGraph seedCore (tree n h)
      (Sigma.fst : (Σ c : Fin 4, Fin (seedMult n c)) → Fin 4)) A) :
    A (.inl 2) (.inl 3) * A (.inl 1) (.inl 2) * A (.inl 1) (.inl 3) = 1 ∨
      A (.inl 2) (.inl 3) * A (.inl 1) (.inl 2) * A (.inl 1) (.inl 3) = -1 := by
  have h1 := hA.sq_eq_one (.inl 2) (.inl 3) (show seedCore.Adj 2 3 by decide)
  have h2 := hA.sq_eq_one (.inl 1) (.inl 2) (show seedCore.Adj 1 2 by decide)
  have h3 := hA.sq_eq_one (.inl 1) (.inl 3) (show seedCore.Adj 1 3 by decide)
  refine sq_eq_one_iff.1 ?_
  rw [mul_pow, mul_pow, h1, h2, h3]
  norm_num

/-- The seed response of one signing: `r I - A ≻ 0` and `g(H_h, A) = u_τ` with
`τ = A₂₃ A₁₂ A₁₃` the sign of the triangle. -/
theorem seed_green_one (n h : ℕ)
    {A : Matrix (SeedV n h) (SeedV n h) ℝ}
    (hA : IsSignedAdj (attachGraph seedCore (tree n h)
      (Sigma.fst : (Σ c : Fin 4, Fin (seedMult n c)) → Fin 4)) A) :
    (rad n • (1 : Matrix (SeedV n h) (SeedV n h) ℝ) - A).PosDef ∧
      (rad n • (1 : Matrix (SeedV n h) (SeedV n h) ℝ) - A)⁻¹ (.inl 0) (.inl 0) =
        seedResp n (treeGreen n h)
          (A (.inl 2) (.inl 3) * A (.inl 1) (.inl 2) * A (.inl 1) (.inl 3)) := by
  have hD : ∀ i, (rad n • (1 : Matrix (tree n h).V (tree n h).V ℝ) -
      copyBlock (tree n h) A i).PosDef := fun i => (tree_green n h (hA.copy i)).1
  have hDg : ∀ i, (rad n • (1 : Matrix (tree n h).V (tree n h).V ℝ) -
      copyBlock (tree n h) A i)⁻¹ (tree n h).root (tree n h).root = treeGreen n h :=
    fun i => (tree_green n h (hA.copy i)).2
  have hs : ∀ i : (Σ c : Fin 4, Fin (seedMult n c)),
      (-A (.inl i.1) (.inr ((tree n h).root, i))) ^ 2 = 1 := fun i => by
    rw [neg_sq]
    exact hA.attach_sq i
  have hP : (rad n • (1 : Matrix (Fin 4) (Fin 4) ℝ) - A.toBlocks₁₁).IsHermitian :=
    (isHermitian_one.smul (IsSelfAdjoint.all _)).sub hA.toBlocks₁₁.isHermitian
  have hdec := hA.attach_decomp (rad n)
  have hsum : ∀ c : Fin 4, ∑ i ∈ Finset.univ.filter
      (fun i : (Σ c : Fin 4, Fin (seedMult n c)) => i.1 = c),
      (rad n • (1 : Matrix (tree n h).V (tree n h).V ℝ) - copyBlock (tree n h) A i)⁻¹
        (tree n h).root (tree n h).root = (seedMult n c : ℝ) * treeGreen n h := by
    intro c
    rw [Finset.sum_congr rfl fun i _ => hDg i, Finset.sum_const,
      seed_card_filter_fst (fun c => Fin (seedMult n c)), Fintype.card_fin, nsmul_eq_mul]
  -- the entries of the core block
  have hadj : ∀ a b : Fin 4, seedCore.Adj a b →
      (attachGraph seedCore (tree n h)
        (Sigma.fst : (Σ c : Fin 4, Fin (seedMult n c)) → Fin 4)).Adj (.inl a) (.inl b) :=
    fun _ _ hab => hab
  have hnadj : ∀ a b : Fin 4, ¬ seedCore.Adj a b → A (.inl a) (.inl b) = 0 :=
    fun a b hab => hA.eq_zero (.inl a) (.inl b) hab
  have e00 : A (.inl 0) (.inl 0) = 0 := hA.apply_self _
  have e11 : A (.inl 1) (.inl 1) = 0 := hA.apply_self _
  have e22 : A (.inl 2) (.inl 2) = 0 := hA.apply_self _
  have e33 : A (.inl 3) (.inl 3) = 0 := hA.apply_self _
  have e02 : A (.inl 0) (.inl 2) = 0 := hnadj 0 2 (by decide)
  have e03 : A (.inl 0) (.inl 3) = 0 := hnadj 0 3 (by decide)
  have e20 : A (.inl 2) (.inl 0) = 0 := hnadj 2 0 (by decide)
  have e30 : A (.inl 3) (.inl 0) = 0 := hnadj 3 0 (by decide)
  obtain ⟨x, hx⟩ : ∃ x, A (.inl 0) (.inl 1) = x := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, A (.inl 1) (.inl 2) = y := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z, A (.inl 1) (.inl 3) = z := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w, A (.inl 2) (.inl 3) = w := ⟨_, rfl⟩
  have e10 : A (.inl 1) (.inl 0) = x := (hA.apply_comm _ _).trans hx
  have e21 : A (.inl 2) (.inl 1) = y := (hA.apply_comm _ _).trans hy
  have e31 : A (.inl 3) (.inl 1) = z := (hA.apply_comm _ _).trans hz
  have e32 : A (.inl 3) (.inl 2) = w := (hA.apply_comm _ _).trans hw
  have hx2 : x ^ 2 = 1 := by rw [← hx]; exact hA.sq_eq_one _ _ (hadj 0 1 (by decide))
  have hy2 : y ^ 2 = 1 := by rw [← hy]; exact hA.sq_eq_one _ _ (hadj 1 2 (by decide))
  have hz2 : z ^ 2 = 1 := by rw [← hz]; exact hA.sq_eq_one _ _ (hadj 1 3 (by decide))
  have hw2 : w ^ 2 = 1 := by rw [← hw]; exact hA.sq_eq_one _ _ (hadj 2 3 (by decide))
  -- the Schur complement onto the core is the 4 × 4 seed matrix
  have hcompl : attachCompl (rad n • (1 : Matrix (Fin 4) (Fin 4) ℝ) - A.toBlocks₁₁)
      (tree n h).root (Sigma.fst : (Σ c : Fin 4, Fin (seedMult n c)) → Fin 4)
      (fun i => rad n • (1 : Matrix (tree n h).V (tree n h).V ℝ) - copyBlock (tree n h) A i) =
      !![rad n - (n + 1) * treeGreen n h, -x, 0, 0;
        -x, rad n - n * treeGreen n h, -y, -z;
        0, -y, rad n - (n + 1) * treeGreen n h, -w;
        0, -z, -w, rad n - (n + 1) * treeGreen n h] := by
    ext i j
    simp only [attachCompl, Matrix.sub_apply, Matrix.diagonal_apply, hsum]
    have hm0 : seedMult n 0 = n + 1 := rfl
    have hm1 : seedMult n 1 = n := rfl
    have hm2 : seedMult n 2 = n + 1 := rfl
    have hm3 : seedMult n 3 = n + 1 := rfl
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.toBlocks₁₁, hm0, hm1, hm2, hm3, e00, e11, e22, e33, e02,
        e03, e20, e30, hx, hy, hz, hw, e10, e21, e31, e32]
  have hτ : w * y * z = 1 ∨ w * y * z = -1 := by
    refine sq_eq_one_iff.1 ?_
    rw [mul_pow, mul_pow, hw2, hy2, hz2]
    norm_num
  obtain ⟨ha, hb, hc⟩ := seed_denoms_pos n (treeGreen_pos n h).le (treeGreen_lt n h).le hτ
  obtain ⟨hMpd, hMinv⟩ := BiluLinial.seed4 hx2 hy2 hz2 hw2 ha hb hc
  have hNpd := (attach_posDef_iff hP (tree n h).root
    (Sigma.fst : (Σ c : Fin 4, Fin (seedMult n c)) → Fin 4) hs hD).2 (by rw [hcompl]; exact hMpd)
  refine ⟨by rw [hdec]; exact hNpd, ?_⟩
  have hinv := congrFun (congrFun (attach_inv_toBlocks₁₁ hP (tree n h).root
    (Sigma.fst : (Σ c : Fin 4, Fin (seedMult n c)) → Fin 4) hs hD hNpd) 0) 0
  rw [hcompl, hMinv] at hinv
  rw [hw, hy, hz, hdec]
  exact hinv

/-- Both responses of the seed, on the concrete vertex type. -/
theorem seed_green_aux (n h : ℕ)
    {A : Matrix (SeedV n h) (SeedV n h) ℝ}
    (hA : IsSignedAdj (attachGraph seedCore (tree n h)
      (Sigma.fst : (Σ c : Fin 4, Fin (seedMult n c)) → Fin 4)) A) :
    (rad n • (1 : Matrix (SeedV n h) (SeedV n h) ℝ) - A).PosDef ∧
      (rad n • (1 : Matrix (SeedV n h) (SeedV n h) ℝ) - A)⁻¹ (.inl 0) (.inl 0) +
          (rad n • (1 : Matrix (SeedV n h) (SeedV n h) ℝ) - -A)⁻¹ (.inl 0) (.inl 0) =
        seedResp n (treeGreen n h) 1 + seedResp n (treeGreen n h) (-1) := by
  obtain ⟨hpd, h1⟩ := seed_green_one n h hA
  obtain ⟨-, h2⟩ := seed_green_one n h hA.neg
  refine ⟨hpd, ?_⟩
  simp only [Matrix.neg_apply] at h2
  rw [h1, h2]
  have e : -A (.inl 2) (.inl 3) * -A (.inl 1) (.inl 2) * -A (.inl 1) (.inl 3) =
      -(A (.inl 2) (.inl 3) * A (.inl 1) (.inl 2) * A (.inl 1) (.inl 3)) := by ring
  rw [e]
  rcases seed_tau n h hA with hτ | hτ
  · rw [hτ]
  · rw [hτ, neg_neg, add_comm]

theorem seed_green (n h : ℕ) {A : Matrix (seed n h).V (seed n h).V ℝ}
    (hA : IsSignedAdj (seed n h).G A) :
    (rad n • (1 : Matrix (seed n h).V (seed n h).V ℝ) - A).PosDef ∧
      green (rad n) A (seed n h).root + green (rad n) (-A) (seed n h).root =
        seedResp n (treeGreen n h) 1 + seedResp n (treeGreen n h) (-1) :=
  seed_green_aux n h hA

end BiluLinial.Counterexample
