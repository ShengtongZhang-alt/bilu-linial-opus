/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.FloorLemma
public import BiluLinial.Tight.Deletion
public import BiluLinial.Tight.ParamsExtra

/-!
# The law exists on the whole source cube

Blueprint node `D-floor-pos` (source Section 1.1: Lemma "Deletion and source differentiation" and
Lemma "Uniform insertion floor"). If every proper induced subgraph satisfies the capped-law
invariant, then for all sources in `[0, s]^V` the law of `G[S]` exists: delete a root `v`, pass to
the smaller sources `ŷ ≤ y` of the core `J = S - v` with the inherited precisions
(`precCore_eq_congr`), so that the inherited core law exists and has means `≤ r ≤ 1.01` by the
invariant of `J` (`ZwCore_pos_of_congr`, `coreE_inv_le_of_congr`); the floor (`floor_ins`) and the
Schur factorization (`wt_eq_wtCore_mul`) conclude.
-/

@[expose] public section

namespace BiluLinial.Tight

open Matrix

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable {d p : ℕ}

theorem floor_pos (hR : TRegime d p) (hdeg : ∀ v, G.degree v ≤ d) (S : Finset V)
    (ih : ∀ T ⊂ S, TInv G d p T) (yp ym : V → ℝ) (hyp : InCube (sOf d p) yp)
    (hym : InCube (sOf d p) ym) : 0 < Zw G p (aOf d p) yp ym S := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨v, hv⟩
  · exact Zw_empty_pos G p (aOf d p) yp ym
  have hp1 : 1 ≤ p := le_trans (by norm_num) hR.two_le_p
  have hyp0 : ∀ i, 0 ≤ yp i := fun i => (hyp i).1
  have hym0 : ∀ i, 0 ≤ ym i := fun i => (hym i).1
  obtain ⟨yp', ep, hyp', hep, hcp⟩ := precCore_eq_congr G (aOf d p) hyp0 hv
  obtain ⟨ym', em, hym', hem, hcm⟩ := precCore_eq_congr G (aOf d p) hym0 hv
  have hc1 : InCube (sOf d p) yp' := fun i => ⟨(hyp' i).1, (hyp' i).2.trans (hyp i).2⟩
  have hc2 : InCube (sOf d p) ym' := fun i => ⟨(hym' i).1, (hym' i).2.trans (hym i).2⟩
  obtain ⟨hZJ, hmJ⟩ := ih (S.erase v) (Finset.erase_ssubset hv) yp' ym' hc1 hc2
  have hZc := ZwCore_pos_of_congr G hep hem hcp hcm hZJ
  have hmean : ∀ i ∈ nbhd G S v,
      coreE G p (aOf d p) yp ym S v (fun σ => (precCore G (aOf d p) 1 yp σ S v)⁻¹ i i) ≤
          101 / 100 ∧
        coreE G p (aOf d p) yp ym S v (fun σ => (precCore G (aOf d p) (-1) ym σ S v)⁻¹ i i) ≤
          101 / 100 := by
    intro i hi
    have hiJ : i ∈ S.erase v := by
      have hi' := Finset.mem_filter.1 hi
      exact Finset.mem_erase.2 ⟨(G.ne_of_adj hi'.2).symm, hi'.1⟩
    exact coreE_inv_le_of_congr G hep hem hcp hcm hZJ i
      (((hmJ i hiJ).1).trans hR.rOf_le) (((hmJ i hiJ).2).trans hR.rOf_le)
  have hfl := floor_ins G hR hdeg hyp hym hv hZc hmean
  have hsum : Zw G p (aOf d p) yp ym S =
      (diagD G (aOf d p) yp S v * diagD G (aOf d p) ym S v) ^ p *
        ∑ σ : Config V, wtCore G p (aOf d p) yp ym σ S v * PhiRoot G p (aOf d p) yp ym σ S v := by
    rw [Zw, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [wt_eq_wtCore_mul G hp1 (aOf d p) hyp0 hym0 σ hv]
    ring
  have hD : ∀ y : V → ℝ, (∀ i, 0 ≤ y i) → 0 < diagD G (aOf d p) y S v := by
    intro y hy
    have : ∀ j ∈ nbhd G S v, 0 ≤ cEdge (aOf d p) y v j := by
      intro j _
      unfold cEdge cRoot
      have h0 : 0 ≤ aOf d p ^ 2 * y v * y j := by
        have := hy v
        have := hy j
        positivity
      have : 1 ≤ Real.sqrt (1 + 4 * (aOf d p ^ 2 * y v * y j)) :=
        Real.one_le_sqrt.2 (by linarith)
      linarith
    unfold diagD
    linarith [Finset.sum_nonneg this]
  rw [hsum]
  have h40 : (0 : ℝ) < 40 ^ p := by positivity
  have hpos : 0 < ∑ σ : Config V,
      wtCore G p (aOf d p) yp ym σ S v * PhiRoot G p (aOf d p) yp ym σ S v := by
    by_contra h
    push Not at h
    nlinarith
  exact mul_pos (pow_pos (mul_pos (hD yp hyp0) (hD ym hym0)) p) hpos

end BiluLinial.Tight
