/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Counterexample.Seed
public import BiluLinial.Counterexample.Step4
public import BiluLinial.Counterexample.Pendant

/-!
# Amplification along the joins

Blueprint node `B-amplify` (source Steps 5 and 7, Xu §4 claim (7)). Fix `N ≥ 2` with
`t(h) > 1 + 1/N` and put `c_j = 1 + 1/(N - j)`. For `j ≤ N - 1` and every signed adjacency matrix
`A` of `join 1 Q_j` (a copy of `Q_j` together with its parent) with `r I ∓ A ⪰ 0`, the copy
`A_j` of `Q_j` satisfies `r I ∓ A_j ≻ 0` and `t(Q_j, A_j) > c_j`.
-/

@[expose] public section

namespace BiluLinial.Counterexample

open Matrix

namespace AmplifyAux

/-- Restricting `r I + A` to a principal submatrix along an injective map. -/
theorem smul_one_add_submatrix {V V' : Type*} [DecidableEq V] [DecidableEq V'] (r : ℝ)
    (A : Matrix V V ℝ) {f : V' → V} (hf : Function.Injective f) :
    (r • (1 : Matrix V V ℝ) + A).submatrix f f = r • (1 : Matrix V' V' ℝ) + A.submatrix f f := by
  ext a b
  simp [Matrix.one_apply, hf.eq_iff]

theorem copyBlock_neg (Y : RGraph) (k : ℕ) (A : Matrix (join k Y).V (join k Y).V ℝ) (i : Fin k) :
    copyBlock Y (-A : Matrix (join k Y).V (join k Y).V ℝ) i = -copyBlock Y A i :=
  rfl

/-- `copyBlock_submatrix_joinSub`, with the submatrix typed on `(join 1 Y).V`. -/
theorem copyBlock_joinSub (Y : RGraph) (k : ℕ) (i : Fin k)
    (A : Matrix (join k Y).V (join k Y).V ℝ) :
    copyBlock Y (A.submatrix (joinSub Y k i) (joinSub Y k i) :
      Matrix (join 1 Y).V (join 1 Y).V ℝ) 0 = copyBlock Y A i :=
  copyBlock_submatrix_joinSub Y k i A

theorem copyBlock_inr_injective {K ι : Type} (Y : RGraph) (i : ι) :
    Function.Injective (fun w : Y.V => (Sum.inr (w, i) : K ⊕ (Y.V × ι))) := by
  intro a b hab
  simpa using hab

theorem copyBlock_smul_sub_psd {K ι : Type} [DecidableEq K] [DecidableEq ι] (Y : RGraph) {r : ℝ}
    {A : Matrix (K ⊕ (Y.V × ι)) (K ⊕ (Y.V × ι)) ℝ}
    (hA : (r • (1 : Matrix (K ⊕ (Y.V × ι)) (K ⊕ (Y.V × ι)) ℝ) - A).PosSemidef) (i : ι) :
    (r • (1 : Matrix Y.V Y.V ℝ) - copyBlock Y A i).PosSemidef := by
  have := hA.submatrix (fun w : Y.V => (Sum.inr (w, i) : K ⊕ (Y.V × ι)))
  rw [smul_one_sub_submatrix r A (copyBlock_inr_injective Y i)] at this
  exact this

theorem copyBlock_smul_add_psd {K ι : Type} [DecidableEq K] [DecidableEq ι] (Y : RGraph) {r : ℝ}
    {A : Matrix (K ⊕ (Y.V × ι)) (K ⊕ (Y.V × ι)) ℝ}
    (hA : (r • (1 : Matrix (K ⊕ (Y.V × ι)) (K ⊕ (Y.V × ι)) ℝ) + A).PosSemidef) (i : ι) :
    (r • (1 : Matrix Y.V Y.V ℝ) + copyBlock Y A i).PosSemidef := by
  have := hA.submatrix (fun w : Y.V => (Sum.inr (w, i) : K ⊕ (Y.V × ι)))
  rw [smul_one_add_submatrix r A (copyBlock_inr_injective Y i)] at this
  exact this

/-- The branch `{root} ∪ (copy i)` of `join k Y`, viewed as `join 1 Y`, inherits the hypotheses. -/
theorem joinSub_branch (Y : RGraph) (k : ℕ) (i : Fin k) {r : ℝ}
    {A : Matrix (join k Y).V (join k Y).V ℝ} (hA : IsSignedAdj (join k Y).G A)
    (hm : (r • (1 : Matrix (join k Y).V (join k Y).V ℝ) - A).PosSemidef)
    (hp : (r • (1 : Matrix (join k Y).V (join k Y).V ℝ) + A).PosSemidef) :
    IsSignedAdj (join 1 Y).G (A.submatrix (joinSub Y k i) (joinSub Y k i)) ∧
      (r • (1 : Matrix (join 1 Y).V (join 1 Y).V ℝ) -
        A.submatrix (joinSub Y k i) (joinSub Y k i)).PosSemidef ∧
      (r • (1 : Matrix (join 1 Y).V (join 1 Y).V ℝ) +
        A.submatrix (joinSub Y k i) (joinSub Y k i)).PosSemidef := by
  refine ⟨hA.submatrix (joinSub_injective Y k i) (joinSub_adj_iff Y k i), ?_, ?_⟩
  · rw [← smul_one_sub_submatrix r A (joinSub_injective Y k i)]
    exact hm.submatrix _
  · rw [← smul_one_add_submatrix r A (joinSub_injective Y k i)]
    exact hp.submatrix _

theorem rad_pos (n : ℕ) : 0 < rad n := by
  unfold rad
  positivity

end AmplifyAux

private theorem amplify_zero (n h N : ℕ) (hseed : 1 + 1 / (N : ℝ) < tseed n h)
    {B : Matrix (seed n h).V (seed n h).V ℝ} (hB : IsSignedAdj (seed n h).G B) :
    (rad n • (1 : Matrix (seed n h).V (seed n h).V ℝ) - B).PosDef ∧
      (rad n • (1 : Matrix (seed n h).V (seed n h).V ℝ) + B).PosDef ∧
      1 + 1 / (N : ℝ) < tval n B (seed n h).root := by
  obtain ⟨h1, hg⟩ := seed_green n h hB
  obtain ⟨h2, -⟩ := seed_green n h hB.neg
  refine ⟨h1, by rwa [sub_neg_eq_add] at h2, ?_⟩
  have ht : tval n B (seed n h).root = tseed n h := by
    unfold tval tseed
    rw [hg]
  rw [ht]
  exact hseed

private theorem amplify_step (n : ℕ) (Y : RGraph) {c : ℝ}
    (IH : ∀ A : Matrix (join 1 Y).V (join 1 Y).V ℝ, IsSignedAdj (join 1 Y).G A →
      (rad n • (1 : Matrix (join 1 Y).V (join 1 Y).V ℝ) - A).PosSemidef →
      (rad n • (1 : Matrix (join 1 Y).V (join 1 Y).V ℝ) + A).PosSemidef →
      (rad n • (1 : Matrix Y.V Y.V ℝ) - copyBlock Y A 0).PosDef ∧
        (rad n • (1 : Matrix Y.V Y.V ℝ) + copyBlock Y A 0).PosDef ∧
        c < tval n (copyBlock Y A 0) Y.root)
    (A : Matrix (join 1 (join (n + 2) Y)).V (join 1 (join (n + 2) Y)).V ℝ)
    (hA : IsSignedAdj (join 1 (join (n + 2) Y)).G A)
    (hm : (rad n • (1 : Matrix (join 1 (join (n + 2) Y)).V (join 1 (join (n + 2) Y)).V ℝ) -
      A).PosSemidef)
    (hp : (rad n • (1 : Matrix (join 1 (join (n + 2) Y)).V (join 1 (join (n + 2) Y)).V ℝ) +
      A).PosSemidef) :
    (rad n • (1 : Matrix (join (n + 2) Y).V (join (n + 2) Y).V ℝ) -
        copyBlock (join (n + 2) Y) A 0).PosDef ∧
      (rad n • (1 : Matrix (join (n + 2) Y).V (join (n + 2) Y).V ℝ) +
        copyBlock (join (n + 2) Y) A 0).PosDef ∧
      1 / (2 - c) < tval n (copyBlock (join (n + 2) Y) A 0) (join (n + 2) Y).root := by
  have hr := AmplifyAux.rad_pos n
  have hB : IsSignedAdj (join (n + 2) Y).G (copyBlock (join (n + 2) Y) A 0) := hA.copy 0
  have hBm := AmplifyAux.copyBlock_smul_sub_psd (join (n + 2) Y) hm 0
  have hBp := AmplifyAux.copyBlock_smul_add_psd (join (n + 2) Y) hp 0
  have hYi : ∀ i, (rad n • (1 : Matrix Y.V Y.V ℝ) -
        copyBlock Y (copyBlock (join (n + 2) Y) A 0) i).PosDef ∧
      (rad n • (1 : Matrix Y.V Y.V ℝ) + copyBlock Y (copyBlock (join (n + 2) Y) A 0) i).PosDef ∧
      c < tval n (copyBlock Y (copyBlock (join (n + 2) Y) A 0) i) Y.root := by
    intro i
    obtain ⟨h1, h2, h3⟩ := AmplifyAux.joinSub_branch Y (n + 2) i hB hBm hBp
    have := IH _ h1 h2 h3
    rw [AmplifyAux.copyBlock_joinSub] at this
    exact this
  have hBpd := pendant_posDef (n + 2) Y hr hA hm (fun i => (hYi i).1)
  have hBpd' : (rad n • (1 : Matrix (join (n + 2) Y).V (join (n + 2) Y).V ℝ) +
      copyBlock (join (n + 2) Y) A 0).PosDef := by
    have := pendant_posDef (n + 2) Y hr hA.neg (by rwa [sub_neg_eq_add]) (fun i => by
      rw [AmplifyAux.copyBlock_neg, AmplifyAux.copyBlock_neg, sub_neg_eq_add]
      exact (hYi i).2.1)
    rw [AmplifyAux.copyBlock_neg, sub_neg_eq_add] at this
    exact this
  obtain ⟨hpos, hge⟩ := join_tval_ge n Y hB (fun i => ⟨(hYi i).1, (hYi i).2.1⟩) ⟨hBpd, hBpd'⟩
  refine ⟨hBpd, hBpd', ?_⟩
  have hmean : c < (∑ i, tval n (copyBlock Y (copyBlock (join (n + 2) Y) A 0) i) Y.root) /
      (n + 2) := by
    rw [lt_div_iff₀ (by positivity)]
    have := Finset.sum_lt_sum_of_nonempty (s := (Finset.univ : Finset (Fin (n + 2))))
      (f := fun _ => c)
      (g := fun i => tval n (copyBlock Y (copyBlock (join (n + 2) Y) A 0) i) Y.root)
      ⟨0, Finset.mem_univ _⟩ (fun i _ => (hYi i).2.2)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    push_cast at this
    linarith [mul_comm c ((n : ℝ) + 2)]
  calc 1 / (2 - c)
      < 1 / (2 - (∑ i, tval n (copyBlock Y (copyBlock (join (n + 2) Y) A 0) i) Y.root) /
          (n + 2)) := one_div_lt_one_div_of_lt hpos (by linarith)
    _ ≤ _ := hge

private theorem c_step {a : ℝ} (ha : 2 ≤ a) : 1 + 1 / (a - 1) = 1 / (2 - (1 + 1 / a)) := by
  have ha0 : a ≠ 0 := (by linarith : (0 : ℝ) < a).ne'
  have ha1 : a - 1 ≠ 0 := (by linarith : (0 : ℝ) < a - 1).ne'
  have e2 : 2 - (1 + 1 / a) = (a - 1) / a := by
    rw [eq_div_iff ha0, sub_mul, add_mul, one_div_mul_cancel ha0]
    ring
  rw [e2, one_div_div, eq_div_iff ha1, add_mul, one_div_mul_cancel ha1]
  ring

theorem amplify (n h N : ℕ) (hN : 2 ≤ N) (hseed : 1 + 1 / (N : ℝ) < tseed n h) :
    ∀ j : ℕ, j + 1 ≤ N →
      ∀ A : Matrix (join 1 (Qgraph n h j)).V (join 1 (Qgraph n h j)).V ℝ,
        IsSignedAdj (join 1 (Qgraph n h j)).G A →
        (rad n • (1 : Matrix (join 1 (Qgraph n h j)).V (join 1 (Qgraph n h j)).V ℝ) - A).PosSemidef →
        (rad n • (1 : Matrix (join 1 (Qgraph n h j)).V (join 1 (Qgraph n h j)).V ℝ) + A).PosSemidef →
        (rad n • (1 : Matrix (Qgraph n h j).V (Qgraph n h j).V ℝ) -
            copyBlock (Qgraph n h j) A 0).PosDef ∧
          (rad n • (1 : Matrix (Qgraph n h j).V (Qgraph n h j).V ℝ) +
            copyBlock (Qgraph n h j) A 0).PosDef ∧
          1 + 1 / ((N : ℝ) - j) < tval n (copyBlock (Qgraph n h j) A 0) (Qgraph n h j).root := by
  intro j
  induction j with
  | zero =>
    intro _ A hA _ _
    obtain ⟨h1, h2, h3⟩ :=
      amplify_zero n h N hseed (B := copyBlock (Qgraph n h 0) A 0) (hA.copy 0)
    refine ⟨h1, h2, ?_⟩
    rw [Nat.cast_zero, sub_zero]
    exact h3
  | succ j ih =>
    intro hj A hA hm hp
    have hNj : (2 : ℝ) ≤ (N : ℝ) - j := by
      have : ((j + 2 : ℕ) : ℝ) ≤ N := by exact_mod_cast (by omega : j + 2 ≤ N)
      push_cast at this
      linarith
    obtain ⟨h1, h2, h3⟩ := amplify_step n (Qgraph n h j) (ih (by omega)) A hA hm hp
    refine ⟨h1, h2, ?_⟩
    have e : 1 + 1 / ((N : ℝ) - ((j + 1 : ℕ) : ℝ)) = 1 / (2 - (1 + 1 / ((N : ℝ) - j))) := by
      have h1' : (N : ℝ) - ((j + 1 : ℕ) : ℝ) = ((N : ℝ) - j) - 1 := by
        push_cast
        ring
      rw [h1']
      exact c_step hNj
    exact lt_of_eq_of_lt e h3

end BiluLinial.Counterexample
