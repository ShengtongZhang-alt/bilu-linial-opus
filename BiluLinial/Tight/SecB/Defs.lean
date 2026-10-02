/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.Contact.Defs

/-!
# Vocabulary of Section B (source lines 626–1076)

Definitions used by the nodes of `docs/tight/BP_SECB.md` (source
`docs/second_order_bilu_linial_tight.tex`, Lemma "Uniform incident-row gain", Section 1.3 and the
paragraph "Weighted fresh-star quadratic domination"; audit `docs/tight/AUDIT_B.md`,
`docs/tight/DR1_CHECK.md`). Everything already defined in `Tight/Ctx.lean` or
`Tight/Contact/Defs.lean` (`maskF`, `coreShift`, the shifted inverses `X_±`, the Hadamard kernels,
the masks `u`, `b_±`, the weak-loop `score`, `D_*`, `dbar`) is reused, not redefined.

* `CapPt`: a point of the capped family (`CapCtx` and a source pair in `[0, λ s]^V`), the
  unbundled form of `CapPoint` (`Tight/SecA/Defs.lean`). Every contact context is one
  (`ContactCtx.toCapPt`). The normalized shifted diagonal is `hzN` of `Tight/SecA/Defs.lean`
  (not imported here, to keep this file free of Section A definitions).
* Root rows at a vertex `w` (lines 674–690, DR1): `rowSP` (`S⁺_w = Σ_{i∼w} E (G⁺_wi)²`), `rowSM`,
  `rowT` (`T_w = Σ_{i∼w} E G⁺_wi G⁻_wi`), `rowBP`, `rowBM`
  (`B^±_w = 1 - D^±_w E h^±_w + a² Σ_{i∼w} E G^±_ww G^±_ii`) and the difference energy `rowDiff`
  (`Σ_{i∼w} E (G⁺_wi - G⁻_wi)²`).
* Cavity kernels of (WT1) at a contact (`Contact.tDir`, `Contact.tCav`) and the fixed-degree
  diagonal weights (`Contact.diagW`).
-/

@[expose] public section

namespace BiluLinial.Tight

open Matrix

universe u

section Raw

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A point of the capped family: the context `CapCtx` at stage `λ` and a source pair in the cube
`[0, λ s]^V`. -/
structure CapPt (d p : ℕ) (S : Finset V) (lam : ℝ) (yp ym : V → ℝ) : Prop
    extends CapCtx G d p S lam where
  hyp : InCube (lam * sOf d p) yp
  hym : InCube (lam * sOf d p) ym

variable {G} in
theorem ContactCtx.toCapPt {d p : ℕ} {S : Finset V} {lam : ℝ} {yp ym : V → ℝ} {v : V}
    (h : ContactCtx G d p S lam yp ym v) : CapPt G d p S lam yp ym :=
  ⟨h.toCapCtx, h.hyp, h.hym⟩

/-- `S⁺_w = Σ_{i ∈ N_S(w)} E (G⁺_wi)²`. -/
noncomputable def rowSP (d p : ℕ) (yp ym : V → ℝ) (S : Finset V) (w : V) : ℝ :=
  ∑ i ∈ nbhd G S w, lawE G p (aOf d p) yp ym S fun σ => greenP G (aOf d p) 1 yp σ S w i ^ 2

/-- `S⁻_w = Σ_{i ∈ N_S(w)} E (G⁻_wi)²`. -/
noncomputable def rowSM (d p : ℕ) (yp ym : V → ℝ) (S : Finset V) (w : V) : ℝ :=
  ∑ i ∈ nbhd G S w, lawE G p (aOf d p) yp ym S fun σ => greenP G (aOf d p) (-1) ym σ S w i ^ 2

/-- The cross term `T_w = Σ_{i ∈ N_S(w)} E G⁺_wi G⁻_wi`. -/
noncomputable def rowT (d p : ℕ) (yp ym : V → ℝ) (S : Finset V) (w : V) : ℝ :=
  ∑ i ∈ nbhd G S w, lawE G p (aOf d p) yp ym S fun σ =>
    greenP G (aOf d p) 1 yp σ S w i * greenP G (aOf d p) (-1) ym σ S w i

/-- `B⁺_w = 1 - D⁺_w E h⁺_w + a² Σ_{i ∈ N_S(w)} E G⁺_ww G⁺_ii` (`D_w Eh_w = Z_w E G_ww`). -/
noncomputable def rowBP (d p : ℕ) (yp ym : V → ℝ) (S : Finset V) (w : V) : ℝ :=
  1 - diagD G (aOf d p) yp S w * meanPlus G d p yp ym S w +
    aOf d p ^ 2 * ∑ i ∈ nbhd G S w, lawE G p (aOf d p) yp ym S fun σ =>
      greenP G (aOf d p) 1 yp σ S w w * greenP G (aOf d p) 1 yp σ S i i

/-- `B⁻_w = 1 - D⁻_w E h⁻_w + a² Σ_{i ∈ N_S(w)} E G⁻_ww G⁻_ii`. -/
noncomputable def rowBM (d p : ℕ) (yp ym : V → ℝ) (S : Finset V) (w : V) : ℝ :=
  1 - diagD G (aOf d p) ym S w * meanMinus G d p yp ym S w +
    aOf d p ^ 2 * ∑ i ∈ nbhd G S w, lawE G p (aOf d p) yp ym S fun σ =>
      greenP G (aOf d p) (-1) ym σ S w w * greenP G (aOf d p) (-1) ym σ S i i

/-- The score-difference energy `Σ_{i ∈ N_S(w)} E (G⁺_wi - G⁻_wi)²` of DR1. -/
noncomputable def rowDiff (d p : ℕ) (yp ym : V → ℝ) (S : Finset V) (w : V) : ℝ :=
  ∑ i ∈ nbhd G S w, lawE G p (aOf d p) yp ym S fun σ =>
    (greenP G (aOf d p) 1 yp σ S w i - greenP G (aOf d p) (-1) ym σ S w i) ^ 2

end Raw

/-! ### Objects at a contact -/

namespace Contact

variable {d p : ℕ} (ct : Contact.{u} d p)

/-- Branch sources: `y⁺` for `e = true`, `y⁻` for `e = false`. -/
def ySrc (e : Bool) : ct.V → ℝ := if e then ct.yp else ct.ym

/-- The shifted inverse `X_e` of branch `e` (`X₊` or `X₋`). -/
noncomputable def Xb (h : ℝ) (e : Bool) (σ : Config ct.V) : Matrix ct.V ct.V ℝ :=
  if e then ct.XP h σ else ct.XM h σ

/-- The physical inverse diagonal of branch `e`, shifted (`X_kk`, `sh = true`) or not
(`G_kk`). -/
noncomputable def diagB (h : ℝ) (σ : Config ct.V) (k : ct.V) (e sh : Bool) : ℝ :=
  if sh then ct.Xb h e σ k k else if e then ct.gp σ k k else ct.gm σ k k

/-- A fixed-degree product of physical inverse diagonals (shifted or not), listed as
`(k, branch, shifted)`: the weights `H₀` of (WT2). -/
noncomputable def diagW (h : ℝ) (l : List (ct.V × Bool × Bool)) (σ : Config ct.V) : ℝ :=
  (l.map fun t => ct.diagB h σ t.1 t.2.1 t.2.2).prod

/-- The core shifted inverse `C_e = (P^e_{S-i} + hI)⁻¹` of (WT1) at the deleted vertex `i`
(physical, inherited precision). Only its entries off `i` are used. -/
noncomputable def Cb (h : ℝ) (e : Bool) (σ : Config ct.V) (i j l : ct.V) : ℝ :=
  coreShift ct.G (aOf d p) (if e then 1 else -1) h (ct.ySrc e) σ ct.S i j l

/-- The direct cavity map of (WT1) on `J = N_S(i)`:
`(T_dir)_jl = 1_{l ∈ N} (C_e)_jl u_l (C₊)_ll`. -/
noncomputable def tDir (h : ℝ) (e : Bool) (i : ct.V) (σ : Config ct.V) :
    Matrix (nbhd ct.G ct.S i) (nbhd ct.G ct.S i) ℝ :=
  Matrix.of fun j l =>
    if (l : ct.V) ∈ ct.N then ct.Cb h e σ i j l * ct.uvec l * ct.Cb h true σ i l l else 0

/-- The cavity map of (WT1) on `J = N_S(i)`:
`(T_cav)_jl = Σ_{k ∈ N \ {i, l}} (C_e)_jk u_k (C₊)_kl`. -/
noncomputable def tCav (h : ℝ) (e : Bool) (i : ct.V) (σ : Config ct.V) :
    Matrix (nbhd ct.G ct.S i) (nbhd ct.G ct.S i) ℝ :=
  Matrix.of fun j l =>
    ∑ k ∈ (ct.N.erase i).erase (l : ct.V), ct.Cb h e σ i j k * ct.uvec k * ct.Cb h true σ i k l

/-- The admissible map of (WT1): `T_dir` (`dir = true`) or `T_cav` (`dir = false`). -/
noncomputable def tMap (h : ℝ) (e dir : Bool) (i : ct.V) (σ : Config ct.V) :
    Matrix (nbhd ct.G ct.S i) (nbhd ct.G ct.S i) ℝ :=
  if dir then ct.tDir h e i σ else ct.tCav h e i σ

/-- The weight `H = H₀ (X_e)_ii² (X₊)_ii²` of (WT2). -/
noncomputable def wtH (h : ℝ) (e : Bool) (i : ct.V) (l : List (ct.V × Bool × Bool))
    (σ : Config ct.V) : ℝ :=
  ct.diagW h l σ * ct.Xb h e σ i i ^ 2 * ct.XP h σ i i ^ 2

end Contact

end BiluLinial.Tight
