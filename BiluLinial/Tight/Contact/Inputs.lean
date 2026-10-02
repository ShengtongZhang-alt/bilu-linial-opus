/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.Contact.InputsA
public import BiluLinial.Tight.Contact.InputsB
public import BiluLinial.Tight.Contact.InputsC

/-!
# Inputs from Sections 1.2–1.4, in the form used by Section 1.5

Blueprint `docs/tight/BP_CONTACT.md`, nodes `I-*`. Each input is stated at a contact
(`Contact d p`, Lean file `Tight/Contact/Defs.lean`), with an absolute constant first and then the
quantifier wrapper `Eventually` of `Tight/Ctx.lean` (`c₀, κ₀ ∈ (0,1]`, then a threshold on `d`, at
`p = ⌊c₀ d^{2/17}⌋`, `h = κ₀ p^{-4}`). The source states these lemmas "uniformly throughout the
capped source family"; the contact point is a point of that family, which is the only place
Section 1.5 uses them. Exponentially small terms `e^{-cp}` are written as `ϑ = d^{-10}`.

Not restated here (imported where used): (F2) `source_moments` and (F3) `source_covariance`
(`Tight/SourceMax.lean`), the walk facts `walk_facts` (`Tight/Walk.lean`), BLmid
(`Tight/Gauss/BLmid.lean`). The route-dependent inputs (DR1 and CR3′) are in
`Tight/Contact/RouteDR1.lean`.

The weighted-quadratic-domination input (WT1)–(WT2) of Section 1.3 is used only inside the proof
of the leaf `fs1_fixed_mask` (FS1, `Tight/Contact/Leaves.lean`); its cavity kernels are defined by
that leaf's decomposition and it is not stated here.
-/

@[expose] public section

namespace BiluLinial.Tight

open Matrix

universe u

end BiluLinial.Tight
