/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.Params
public import BiluLinial.Common.Spectral

/-!
# Extracting the signing at the constant sources

Blueprint node `D-extract` (source Section 1.1, last display). At `y^± = s 1` on `S = V`,
`D_i = 1 + deg(i) c(a²s²) ≤ s` because `Z_i(s 1) = (1 + (deg i - 1) τ_*)/(1 + q τ_*) ≤ 1`. A signing
of positive weight has `P̃^± = diag D ± a s A_σ ≻ 0`, hence `s I ± a s A_σ ≻ 0`, i.e.
`‖A_σ‖ < 1/a = R`.
-/

@[expose] public section

namespace BiluLinial.Tight

open Matrix

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable {d p : ℕ}

omit [DecidableEq V] in
/-- At the constant sources, `D_i = 1 + deg(i) c(a²s²) ≤ s` for every vertex of degree `≤ d`. -/
theorem diagD_const_le (hR : TRegime d p) (hdeg : ∀ v, G.degree v ≤ d) (i : V) :
    diagD G (aOf d p) (fun _ => sOf d p) Finset.univ i ≤ sOf d p := by
  have hτ0 := hR.τsOf_pos
  have hτ1 : 0 < 1 - τsOf d p := sub_pos.mpr hR.τsOf_lt_one
  have hcard : (nbhd G Finset.univ i).card = G.degree i := by
    rw [nbhd, ← SimpleGraph.neighborFinset_eq_filter, SimpleGraph.card_neighborFinset_eq_degree]
  have h1 : diagD G (aOf d p) (fun _ => sOf d p) Finset.univ i =
      1 + (G.degree i : ℝ) * (τsOf d p / (1 - τsOf d p)) := by
    simp only [diagD, cEdge, hR.cRoot_const, Finset.sum_const, hcard, nsmul_eq_mul]
  have hdi : (G.degree i : ℝ) * τsOf d p ≤ d * τsOf d p :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hdeg i) hτ0.le
  have e : (1 + (G.degree i : ℝ) * (τsOf d p / (1 - τsOf d p))) * (1 - τsOf d p) =
      1 - τsOf d p + G.degree i * τsOf d p := by
    field_simp
  rw [h1, sOf, le_div_iff₀ hτ1, e, qOf]
  linarith

theorem signing_of_Zw_pos (hR : TRegime d p) (hdeg : ∀ v, G.degree v ≤ d)
    (hZ : 0 < Zw G p (aOf d p) (fun _ => sOf d p) (fun _ => sOf d p) Finset.univ) :
    ∃ σ : Signing G, opNorm (signedAdjMatrix G σ) < Real.sqrt (RsqOf d p) := by
  have hZ' : ∑ σ : Config V,
      wt G p (aOf d p) (fun _ => sOf d p) (fun _ => sOf d p) σ Finset.univ ≠ 0 := hZ.ne'
  obtain ⟨σ, -, hσ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hZ'
  have hpos : (precN G (aOf d p) 1 (fun _ => sOf d p) σ Finset.univ).PosDef ∧
      (precN G (aOf d p) (-1) (fun _ => sOf d p) σ Finset.univ).PosDef := by
    by_contra h
    exact hσ (by rw [wt, ite_eq_right h])
  refine ⟨fun e => σ e.1, ?_⟩
  have hA : (signedAdjMatrix G (fun e => σ e.1)).IsHermitian := by
    refine isHermitian_iff_isSymm.mpr (IsSymm.ext fun u w => ?_)
    by_cases h : G.Adj u w
    · simp only [signedAdjMatrix, of_apply, dite_eq_left h, dite_eq_left h.symm]
      rw [Sym2.eq_swap]
    · simp only [signedAdjMatrix, of_apply, dite_eq_right h,
        dite_eq_right (fun h' : G.Adj w u => h h'.symm)]
  have hr : 0 < Real.sqrt (RsqOf d p) := Real.sqrt_pos.mpr hR.RsqOf_pos
  have hs := hR.sOf_pos
  have hss : Real.sqrt (sOf d p) * Real.sqrt (sOf d p) = sOf d p := Real.mul_self_sqrt hs.le
  have key : ∀ τ : ℝ, Real.sqrt (RsqOf d p) • (1 : Matrix V V ℝ) +
      τ • signedAdjMatrix G (fun e => σ e.1) =
      (Real.sqrt (RsqOf d p) / sOf d p) • (precN G (aOf d p) τ (fun _ => sOf d p) σ Finset.univ +
        diagonal (fun i => sOf d p - diagD G (aOf d p) (fun _ => sOf d p) Finset.univ i)) := by
    intro τ
    ext u w
    by_cases huw : u = w
    · subst huw
      simp [precN, signedAdjMatrix]
      field_simp
    · by_cases hadj : G.Adj u w
      · simp [precN, signedAdjMatrix, huw, hadj, hss, sgn, aOf]
        field_simp
      · simp [precN, signedAdjMatrix, huw, hadj]
  have hdiag : (diagonal (fun i => sOf d p -
      diagD G (aOf d p) (fun _ => sOf d p) Finset.univ i)).PosSemidef :=
    PosSemidef.diagonal (fun i => sub_nonneg.mpr (diagD_const_le G hR hdeg i))
  have hrs : 0 < Real.sqrt (RsqOf d p) / sOf d p := div_pos hr hs
  rw [opNorm_lt_iff_posDef hA hr]
  constructor
  · have h := key (-1)
    rw [neg_one_smul, ← sub_eq_add_neg] at h
    rw [h]
    exact (hpos.2.add_posSemidef hdiag).smul hrs
  · have h := key 1
    rw [one_smul] at h
    rw [h]
    exact (hpos.1.add_posSemidef hdiag).smul hrs

end BiluLinial.Tight
