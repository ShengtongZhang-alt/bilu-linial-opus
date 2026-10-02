/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.Step
public import BiluLinial.Tight.Extract

/-!
# The graph-order induction

Blueprint node `D-core`. Strong induction on the vertex set with `tinv_step` gives the invariant
for every `S`; at `S = V` and the constant sources `y^± = s 1` the law exists, and
`signing_of_Zw_pos` extracts a signing with `‖A_σ‖ < R`.
-/

@[expose] public section

namespace BiluLinial.Tight

universe u

variable {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable {d p : ℕ}

theorem tinv_all (hR : TRegime d p) (hCF : ContactFree.{u} d p) (hdeg : ∀ v, G.degree v ≤ d)
    (S : Finset V) : TInv G d p S :=
  Finset.strongInduction (p := fun S => TInv G d p S)
    (fun S ih => tinv_step G hR hCF hdeg S ih) S

theorem tight_signing (hR : TRegime d p) (hCF : ContactFree.{u} d p)
    (hdeg : ∀ v, G.degree v ≤ d) :
    ∃ σ : Signing G, opNorm (signedAdjMatrix G σ) < Real.sqrt (RsqOf d p) := by
  have hc : InCube (sOf d p) (fun _ : V => sOf d p) := fun _ => ⟨hR.sOf_pos.le, le_rfl⟩
  exact signing_of_Zw_pos G hR hdeg ((tinv_all G hR hCF hdeg Finset.univ) _ _ hc hc).1

end BiluLinial.Tight
