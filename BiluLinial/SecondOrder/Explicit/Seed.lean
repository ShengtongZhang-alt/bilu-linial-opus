/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.SecondOrder.Explicit.Tree
public import BiluLinial.SecondOrder.Explicit.Seed3
public import BiluLinial.SecondOrder.Explicit.SeedNumeric
public import BiluLinial.Counterexample.AttachSchur
public import BiluLinial.Counterexample.AttachDecomp
public import BiluLinial.Counterexample.Structure

/-!
# The responses of the triangle seed

Blueprint node `C2-seed` (source Section 6: "eliminating these trees leaves effective diagonal
entries `a`, `b` … the root response is `g_η = (b - 2/(a - η))⁻¹`. Changing the spectral side
exchanges `η` and `-η`"). For `t > 0`, `R = thr n t` and every signed adjacency matrix `A` of the
triangle seed: `R I - A ≻ 0`, and the mean two-sided root response is `seedMean n t h`.

Proof (as Part B's `seed_green_one`, with the triangle core): `attach_decomp` writes `R I - A` in
block form; every tree copy is positive definite with response `g_h = treeResp n R h`
(`tree_resp`); by `attach_posDef_iff` / `attach_inv_toBlocks₁₁` the question reduces to the Schur
complement on `Fin 3`, which is the matrix of `seed3` with `a = R - (n+1) g_h`, `b = R - n g_h`
(`n` trees at `o`, `n + 1` at `v₁, v₂`); `seed3` applies by `tri_seed_denoms_pos` (with
`g_h < t`, `treeResp_pos_lt`). For `-A` the triangle sign `τ = w x y` becomes `-τ`, so the two
responses are `seedResp3 n R g_h 1` and `seedResp3 n R g_h (-1)` in some order.
-/

@[expose] public section

namespace BiluLinial.SecondOrder.Explicit

open Matrix BiluLinial.Counterexample

/-- The vertex type of `triSeed n h`. -/
local notation "TriV" n:max h:max =>
  Fin 3 ⊕ (RGraph.V (tree n h) × (Σ c : Fin 3, Fin (triMult n c)))

/-- The sign `τ = A₁₂ A₀₁ A₀₂` of the triangle is `±1`. -/
theorem tri_seed_tau (n h : ℕ) {A : Matrix (TriV n h) (TriV n h) ℝ}
    (hA : IsSignedAdj (attachGraph (⊤ : SimpleGraph (Fin 3)) (tree n h)
      (Sigma.fst : (Σ c : Fin 3, Fin (triMult n c)) → Fin 3)) A) :
    A (.inl 1) (.inl 2) * A (.inl 0) (.inl 1) * A (.inl 0) (.inl 2) = 1 ∨
      A (.inl 1) (.inl 2) * A (.inl 0) (.inl 1) * A (.inl 0) (.inl 2) = -1 := by
  have h1 := hA.sq_eq_one (.inl 1) (.inl 2) (show (⊤ : SimpleGraph (Fin 3)).Adj 1 2 by decide)
  have h2 := hA.sq_eq_one (.inl 0) (.inl 1) (show (⊤ : SimpleGraph (Fin 3)).Adj 0 1 by decide)
  have h3 := hA.sq_eq_one (.inl 0) (.inl 2) (show (⊤ : SimpleGraph (Fin 3)).Adj 0 2 by decide)
  refine sq_eq_one_iff.1 ?_
  rw [mul_pow, mul_pow, h1, h2, h3]
  norm_num

/-- The seed response of one signing: `R I - A ≻ 0` and `g(A) = seedResp3 n R g_h τ` with
`τ = A₁₂ A₀₁ A₀₂` the sign of the triangle. -/
theorem tri_seed_green_one (n h : ℕ) {t : ℝ} (ht : 0 < t) {A : Matrix (TriV n h) (TriV n h) ℝ}
    (hA : IsSignedAdj (attachGraph (⊤ : SimpleGraph (Fin 3)) (tree n h)
      (Sigma.fst : (Σ c : Fin 3, Fin (triMult n c)) → Fin 3)) A) :
    (thr n t • (1 : Matrix (TriV n h) (TriV n h) ℝ) - A).PosDef ∧
      (thr n t • (1 : Matrix (TriV n h) (TriV n h) ℝ) - A)⁻¹ (.inl 0) (.inl 0) =
        seedResp3 n (thr n t) (treeResp n (thr n t) h)
          (A (.inl 1) (.inl 2) * A (.inl 0) (.inl 1) * A (.inl 0) (.inl 2)) := by
  have hD : ∀ i, (thr n t • (1 : Matrix (tree n h).V (tree n h).V ℝ) -
      copyBlock (tree n h) A i).PosDef := fun i => (tree_resp n ht h (hA.copy i)).1
  have hDg : ∀ i, (thr n t • (1 : Matrix (tree n h).V (tree n h).V ℝ) -
      copyBlock (tree n h) A i)⁻¹ (tree n h).root (tree n h).root = treeResp n (thr n t) h :=
    fun i => (tree_resp n ht h (hA.copy i)).2
  have hs : ∀ i : (Σ c : Fin 3, Fin (triMult n c)),
      (-A (.inl i.1) (.inr ((tree n h).root, i))) ^ 2 = 1 := fun i => by
    rw [neg_sq]
    exact hA.attach_sq i
  have hP : (thr n t • (1 : Matrix (Fin 3) (Fin 3) ℝ) - A.toBlocks₁₁).IsHermitian :=
    (isHermitian_one.smul (IsSelfAdjoint.all _)).sub hA.toBlocks₁₁.isHermitian
  have hdec := hA.attach_decomp (thr n t)
  have hsum : ∀ c : Fin 3, ∑ i ∈ Finset.univ.filter
      (fun i : (Σ c : Fin 3, Fin (triMult n c)) => i.1 = c),
      (thr n t • (1 : Matrix (tree n h).V (tree n h).V ℝ) - copyBlock (tree n h) A i)⁻¹
        (tree n h).root (tree n h).root = (triMult n c : ℝ) * treeResp n (thr n t) h := by
    intro c
    rw [Finset.sum_congr rfl fun i _ => hDg i, Finset.sum_const,
      card_filter_sigma_fst (fun c => Fin (triMult n c)), Fintype.card_fin, nsmul_eq_mul]
  have hadj : ∀ a b : Fin 3, a ≠ b →
      (attachGraph (⊤ : SimpleGraph (Fin 3)) (tree n h)
        (Sigma.fst : (Σ c : Fin 3, Fin (triMult n c)) → Fin 3)).Adj (.inl a) (.inl b) :=
    fun _ _ hab => hab
  have e00 : A (.inl 0) (.inl 0) = 0 := hA.apply_self _
  have e11 : A (.inl 1) (.inl 1) = 0 := hA.apply_self _
  have e22 : A (.inl 2) (.inl 2) = 0 := hA.apply_self _
  obtain ⟨x, hx⟩ : ∃ x, A (.inl 0) (.inl 1) = x := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, A (.inl 0) (.inl 2) = y := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w, A (.inl 1) (.inl 2) = w := ⟨_, rfl⟩
  have e10 : A (.inl 1) (.inl 0) = x := (hA.apply_comm _ _).trans hx
  have e20 : A (.inl 2) (.inl 0) = y := (hA.apply_comm _ _).trans hy
  have e21 : A (.inl 2) (.inl 1) = w := (hA.apply_comm _ _).trans hw
  have hx2 : x ^ 2 = 1 := by rw [← hx]; exact hA.sq_eq_one _ _ (hadj 0 1 (by decide))
  have hy2 : y ^ 2 = 1 := by rw [← hy]; exact hA.sq_eq_one _ _ (hadj 0 2 (by decide))
  have hw2 : w ^ 2 = 1 := by rw [← hw]; exact hA.sq_eq_one _ _ (hadj 1 2 (by decide))
  -- the Schur complement onto the triangle is the 3 × 3 matrix of `seed3`
  have hcompl : attachCompl (thr n t • (1 : Matrix (Fin 3) (Fin 3) ℝ) - A.toBlocks₁₁)
      (tree n h).root (Sigma.fst : (Σ c : Fin 3, Fin (triMult n c)) → Fin 3)
      (fun i => thr n t • (1 : Matrix (tree n h).V (tree n h).V ℝ) - copyBlock (tree n h) A i) =
      !![thr n t - n * treeResp n (thr n t) h, -x, -y;
        -x, thr n t - (n + 1) * treeResp n (thr n t) h, -w;
        -y, -w, thr n t - (n + 1) * treeResp n (thr n t) h] := by
    ext i j
    simp only [attachCompl, Matrix.sub_apply, Matrix.diagonal_apply, hsum]
    have hm0 : triMult n 0 = n := rfl
    have hm1 : triMult n 1 = n + 1 := rfl
    have hm2 : triMult n 2 = n + 1 := rfl
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.toBlocks₁₁, hm0, hm1, hm2, e00, e11, e22, hx, hy, hw, e10, e20, e21]
  have hτ : w * x * y = 1 ∨ w * x * y = -1 := by
    refine sq_eq_one_iff.1 ?_
    rw [mul_pow, mul_pow, hw2, hx2, hy2]
    norm_num
  obtain ⟨ha, hb⟩ := tri_seed_denoms_pos n ht (treeResp_pos_lt n ht h).2.le hτ
  obtain ⟨hMpd, hMinv⟩ := seed3 hx2 hy2 hw2 ha hb
  have hNpd := (attach_posDef_iff hP (tree n h).root
    (Sigma.fst : (Σ c : Fin 3, Fin (triMult n c)) → Fin 3) hs hD).2 (by rw [hcompl]; exact hMpd)
  refine ⟨by rw [hdec]; exact hNpd, ?_⟩
  have hinv := congrFun (congrFun (attach_inv_toBlocks₁₁ hP (tree n h).root
    (Sigma.fst : (Σ c : Fin 3, Fin (triMult n c)) → Fin 3) hs hD hNpd) 0) 0
  rw [hcompl, hMinv] at hinv
  rw [hw, hx, hy, hdec]
  exact hinv

/-- Both responses of the seed, on the concrete vertex type. -/
theorem tri_seed_green_aux (n h : ℕ) {t : ℝ} (ht : 0 < t) {A : Matrix (TriV n h) (TriV n h) ℝ}
    (hA : IsSignedAdj (attachGraph (⊤ : SimpleGraph (Fin 3)) (tree n h)
      (Sigma.fst : (Σ c : Fin 3, Fin (triMult n c)) → Fin 3)) A) :
    (thr n t • (1 : Matrix (TriV n h) (TriV n h) ℝ) - A).PosDef ∧
      (thr n t • (1 : Matrix (TriV n h) (TriV n h) ℝ) - A)⁻¹ (.inl 0) (.inl 0) +
          (thr n t • (1 : Matrix (TriV n h) (TriV n h) ℝ) - -A)⁻¹ (.inl 0) (.inl 0) =
        seedResp3 n (thr n t) (treeResp n (thr n t) h) 1 +
          seedResp3 n (thr n t) (treeResp n (thr n t) h) (-1) := by
  obtain ⟨hpd, h1⟩ := tri_seed_green_one n h ht hA
  obtain ⟨-, h2⟩ := tri_seed_green_one n h ht hA.neg
  refine ⟨hpd, ?_⟩
  simp only [Matrix.neg_apply] at h2
  rw [h1, h2]
  have e : -A (.inl 1) (.inl 2) * -A (.inl 0) (.inl 1) * -A (.inl 0) (.inl 2) =
      -(A (.inl 1) (.inl 2) * A (.inl 0) (.inl 1) * A (.inl 0) (.inl 2)) := by ring
  rw [e]
  rcases tri_seed_tau n h hA with hτ | hτ
  · rw [hτ]
  · rw [hτ, neg_neg, add_comm]

theorem seed_resp (n h : ℕ) {t : ℝ} (ht : 0 < t) {A : Matrix (triSeed n h).V (triSeed n h).V ℝ}
    (hA : IsSignedAdj (triSeed n h).G A) :
    (thr n t • (1 : Matrix (triSeed n h).V (triSeed n h).V ℝ) - A).PosDef ∧
      mresp (thr n t) A (triSeed n h).root = seedMean n t h := by
  obtain ⟨hpd, hsum⟩ := tri_seed_green_aux n h ht hA
  exact ⟨hpd, congrArg (· / 2) hsum⟩

end BiluLinial.SecondOrder.Explicit
