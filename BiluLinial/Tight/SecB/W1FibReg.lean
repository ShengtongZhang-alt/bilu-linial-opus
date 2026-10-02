/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecB.W1FibSmooth

/-!
# The weak loop (W1), edge fibres: the regular-fibre calculus (TB.W1fib-reg)

Node TB.W1fib-reg of `docs/tight/BP_SECB.md` (source l.892–899; AUDIT-B §2.4). Fix a contact, an
edge `ij` (`i ∈ N`, `j ∼ i`), a configuration `k` and a signing `σ` with `σ_ij = 1`;
`σ' = σ^e` (`fibFlip`). Along the fibre the edge value becomes a real `t`:
`P̃^±(t) = P̃^±(σ) + (t - 1)(±a √(y_i y_j))(e_i e_jᵀ + e_j e_iᵀ)` (`precT`, `fibPp`, `fibPm`), so
`t = 1` gives `σ` and `t = -1` gives `σ'` (`precN_update`). The observables are evaluated on the
pair of precisions (`physInv`, `obsPsi`; `obsPsi_precN`: at a signing they are `cfgPsi`), and
`φ(t) = (det P̃⁺(t) det P̃⁻(t))^p Ψ(P̃⁺(t), P̃⁻(t))` (`fibPhi`).

Sub-nodes (TB.W1fib-reg is proved from them in `SecB/W1FibRegAsm.lean`):

* `fibChain_of_contDiffOn` (generic, proved): `C³` on an open set `⊇ [-1, 1]` + endpoint values +
  endpoint derivatives + `|φ'''| ≤ B` on `[-1, 1]` give a `FibChain`.
* `precN_update`, `fibPp_one`, `fibPp_neg_one`, … , `obsPsi_precN`, `fibPhi_one`,
  `fibPhi_neg_one` (exact, proved): the endpoint values `φ(1) = W(σ)Ψ(σ)`, `φ(-1) = W(σ')Ψ(σ')`
  (the endpoints are positive definite, so `W = (det P̃⁺ det P̃⁻)^p` there).
* **TB.W1fib-seg** (`fib_seg_pd`, proved; tools in `SecB/W1FibSeg.lean`): on a regular fibre
  `P̃^±(t) ≻ 0` for `t ∈ [-2, 2]`.
  Sketch: with `τ₀` the good endpoint (`t₀ = ±1`), `P̃(t) = P̃(τ₀) + (t - t₀) c E`,
  `c = ±a√(y_i y_j)`; for `x ≠ 0`, `Q = xᵀP̃(τ₀)x > 0` and `x_k² ≤ (P̃(τ₀)⁻¹)_kk Q` (Cauchy–Schwarz
  for the form of `P̃(τ₀)⁻¹`), so `|2(t - t₀) c x_i x_j| ≤ 2·3·a √(G_ii G_jj) Q ≤ 3 a g* Q ≤ 3Q/64`
  (`G_kk = y_k (P̃⁻¹)_kk`, `64 p a g*(τ₀) ≤ 1`), whence `xᵀP̃(t)x ≥ (61/64) Q > 0`.
* **TB.W1fib-smooth** (`fibPhi_contDiffOn`, proved; tools in `SecB/W1FibSmooth.lean`): `φ` is `C³`
  on any set where `P̃^±(t) ≻ 0` (`h ≥ 0`).
  Sketch: `t ↦ P̃^±(t)` is affine; `det` and `adjugate` are polynomial in the entries;
  `A⁻¹ = (det A)⁻¹ • adj A` with `det ≠ 0`; `P̃ + hY_S ≻ 0` (`Y_S ⪰ 0`); `φ` is a polynomial in
  these entries and in `(det)⁻¹` (`maskF`, `obsBP`, `obsBM` are finite sums of products).
* **TB.W1fib-d1** (`fibPhi_deriv_one`, `fibPhi_deriv_neg_one`, open, `SecB/W1FibD1.lean`):
  `φ'(1) = W(σ) DΨ(σ)`,
  `φ'(-1) = W(σ') DΨ(σ')` at positive-definite endpoints. Sketch: `∂_t P̃^± = ±a√(y_iy_j) E`;
  `∂ log det P̃^± = tr(P̃⁻¹ ∂P̃) = ±2a G^±_ij` (so `∂ log W = 2pa(G⁺_ij - G⁻_ij)`);
  `∂(√y_k (P̃ + zY)⁻¹_kl √y_l) = ∓a (X_ki X_jl + X_kj X_il)` for the physical `X` (`z = 0`: `G`);
  hence `∂Ω₊ = -a G⁺_vv G⁺_vi G⁺_vj` (`dOmP`), `∂Ω₋` (`dOmM`), `∂X_ε = -εa X_ε E X_ε`,
  `∂X₊ = -a X₊ E X₊`, `∂b₊ = dbP`, `∂b₋ = dbM`, and the product rule on
  `F_ji = (X_ε)_ii U_ji - (X_ε)_ji U_ii`, `U = X_ε D_f X₊`, gives exactly `fibD`. Checked by central
  finite differences (6-vertex graph, random sources `y`, all four configurations).
* **TB.W1fib-d3** (`fibPhi_d3`, open, `SecB/W1FibD3.lean`):
  `|φ'''(t)| ≤ K (W(σ)Yb(σ) + W(σ')Yb(σ'))` on `[-1, 1]`.
  Sketch (source l.892–899): let `τ₀` be the good endpoint, `s = t - t₀`, `|s| ≤ 2`.
  (i) Segment comparison: `P(t) ⪰ (1 - 2a g*) P(τ₀) ⪰ P(τ₀)/2` (as in TB.W1fib-seg), so
  `G(t) ⪯ 2G(τ₀)`, `X(t) ⪯ 2X(τ₀)`, `D_*(t) ≤ 2D_*(τ₀)`, and (rank-two inverse formula,
  `SecA.inv_add_rank_two_apply`) `R(t) ≤ R(τ₀) + 8a D_*(τ₀)²`; `W(t)/W(τ₀) = (δ₊(s)δ₋(s))^p` with
  `δ_±(s) = 1 ± 2sa G^±_ij - s²a²(G^±_iiG^±_jj - (G^±_ij)²)` (`SecA.det_add_rank_two`), and
  `|δ_± - 1| ≤ 4aR + 4a²g*² ≤ 1/(8p)` gives `W(t) ≤ e^{1/4} W(τ₀)`.
  (ii) Derivatives: with `ℓ = log W`, `ℓ' = 2pa(G⁺_ij - G⁻_ij)`, `ℓ'' = -2pa²Σ_±(G^±_iiG^±_jj +
  (G^±_ij)²)`, `ℓ''' = 4pa³ Σ_± ±(3G_iiG_jjG_ij + G_ij³)`: `|ℓ'| ≤ 2paR`, `|ℓ''| ≤ 4pa²D_*²`,
  `|ℓ'''| ≤ 32pa³D_*³`; `∂^r X_kl = (-1)^r r! (X(cE)^r X)_kl`, `|∂^r X_kl| ≤ r!(2aD_*)^r D_*` on the
  ball, and the same for `G`, so `|∂^r Ψ| ≤ C a^r D_*^{C}/(√d h)` (`r ≤ 3`; masks as in
  `SecB/W1Mom.lean`). (iii) `φ''' = W[(ℓ'³ + 3ℓ'ℓ'' + ℓ''')Ψ + 3(ℓ'² + ℓ'')Ψ' + 3ℓ'Ψ'' + Ψ''']`, so
  `|φ'''| ≤ C W(t) a³ D_*(t)^C (p³R(t)³ + p²R(t)D_*² + pD_*³ + …)/(√d h)
  ≤ C' W(τ₀) a³ D_*(τ₀)^{C'} (p³R(τ₀)² + p)/(√d h)` using `R ≤ 2D_*`, `p²R ≤ p³R² + p`,
  `p³a²D_*⁴ ≤ pD_*⁴` (`pa ≤ 1`), and (i). Checked numerically (6-vertex graph, `M = 10`:
  ratio `≤ 4·10⁻⁷`).
-/

@[expose] public section

namespace BiluLinial.Tight.SecB

open Matrix

universe u

/-! ### The generic chain -/

/-- A `C³` function on an open set containing `[-1, 1]`, with the given endpoint values and endpoint
derivatives and `|φ'''| ≤ B` on `[-1, 1]`, is a `FibChain`. -/
theorem fibChain_of_contDiffOn {V : Type*} {U : Set ℝ} (hU : IsOpen U)
    (hIU : Set.Icc (-1 : ℝ) 1 ⊆ U) {φ : ℝ → ℝ} (hφ : ContDiffOn ℝ 3 φ U)
    {Φ₀ Φ₁ : Config V → ℝ} {σp σm : Config V} {B : ℝ} (h0p : φ 1 = Φ₀ σp)
    (h0m : φ (-1) = Φ₀ σm) (h1p : deriv φ 1 = Φ₁ σp) (h1m : deriv φ (-1) = Φ₁ σm)
    (hB : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |iteratedDeriv 3 φ t| ≤ B) :
    FibChain Φ₀ Φ₁ σp σm B := by
  have hd : ∀ m < 3, ∀ t ∈ U, HasDerivAt (iteratedDeriv m φ) (iteratedDeriv (m + 1) φ t) t := by
    intro m hm t ht
    have hdiff : DifferentiableOn ℝ (iteratedDerivWithin m φ U) U :=
      hφ.differentiableOn_iteratedDerivWithin (by exact_mod_cast hm) hU.uniqueDiffOn
    have hdt : DifferentiableAt ℝ (iteratedDerivWithin m φ U) t :=
      (hdiff t ht).differentiableAt (hU.mem_nhds ht)
    have heq : iteratedDeriv m φ =ᶠ[nhds t] iteratedDerivWithin m φ U :=
      Filter.eventually_of_mem (hU.mem_nhds ht) fun x hx =>
        (iteratedDerivWithin_of_isOpen hU hx).symm
    rw [iteratedDeriv_succ]
    exact (hdt.congr_of_eventuallyEq heq).hasDerivAt
  refine ⟨fun m => iteratedDeriv m φ, fun m hm t ht => hd m hm t (hIU ht), ?_, ?_, ?_, ?_, hB⟩
  · simpa using h0p
  · simpa using h0m
  · simpa [iteratedDeriv_one] using h1p
  · simpa [iteratedDeriv_one] using h1m

/-! ### Edge interpolation -/

section Interp

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The edge-interpolated normalized precision: `precN` with the edge value `σ_ij` replaced by `t`,
`P̃(t) = P̃(σ) + (t - σ_ij) τ a √(y_i y_j) (e_i e_jᵀ + e_j e_iᵀ)`. -/
noncomputable def precT (a τ : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) (i j : V) (t : ℝ) :
    Matrix V V ℝ :=
  precN G a τ y σ S +
    ((t - sgn σ i j) * (τ * a * (Real.sqrt (y i) * Real.sqrt (y j)))) • SecA.edgeE i j

omit [Fintype V] in
theorem precT_sgn (a τ : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) (i j : V) :
    precT G a τ y σ S i j (sgn σ i j) = precN G a τ y σ S := by
  simp [precT]

omit [Fintype V] in
theorem precT_recenter (a τ : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) (i j : V) (t t₀ : ℝ) :
    precT G a τ y σ S i j t = precT G a τ y σ S i j t₀ +
      ((t - t₀) * (τ * a * (Real.sqrt (y i) * Real.sqrt (y j)))) • SecA.edgeE i j := by
  unfold precT
  rw [add_assoc, ← add_smul]
  congr 2
  ring

omit [Fintype V] [DecidableEq V] in
theorem sgn_comm (σ : Config V) (i j : V) : sgn σ j i = sgn σ i j := by
  simp [sgn, Sym2.eq_swap]

omit [Fintype V] in
/-- Changing the edge value is a rank-two update. -/
theorem precN_update {a τ : ℝ} {y : V → ℝ} {σ : Config V} {S : Finset V} {i j : V}
    (hi : i ∈ S) (hj : j ∈ S) (hij : G.Adj i j) (u : ℤˣ) :
    precN G a τ y (Function.update σ s(i, j) u) S = precT G a τ y σ S i j ((u : ℤ) : ℝ) := by
  have hne : i ≠ j := G.ne_of_adj hij
  have hupd : ∀ k l, s(k, l) = s(i, j) →
      sgn (Function.update σ s(i, j) u) k l = ((u : ℤ) : ℝ) := fun k l hkl => by
    simp [sgn, hkl]
  have hkeep : ∀ k l, s(k, l) ≠ s(i, j) →
      sgn (Function.update σ s(i, j) u) k l = sgn σ k l := fun k l hkl => by
    simp [sgn, Function.update_of_ne hkl]
  ext k l
  simp only [precT, precN, Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, SecA.edgeE,
    Matrix.single_apply, smul_eq_mul]
  by_cases hkl : k = l
  · subst hkl
    have h1 : ¬(i = k ∧ j = k) := fun h => hne (h.1.trans h.2.symm)
    have h2 : ¬(j = k ∧ i = k) := fun h => hne (h.2.trans h.1.symm)
    simp [h1, h2]
  · rw [if_neg hkl, if_neg hkl]
    by_cases he : s(k, l) = s(i, j)
    · rw [hupd k l he]
      rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have hS : k ∈ S ∧ l ∈ S ∧ G.Adj k l := ⟨hi, hj, hij⟩
        rw [if_pos hS, if_pos hS]
        simp [hne, Ne.symm hne]
        ring
      · have hS : k ∈ S ∧ l ∈ S ∧ G.Adj k l := ⟨hj, hi, hij.symm⟩
        rw [if_pos hS, if_pos hS, sgn_comm σ l k]
        simp [hne, Ne.symm hne]
        ring
    · rw [hkeep k l he]
      have h1 : ¬(i = k ∧ j = l) := fun h => he (by rw [h.1, h.2])
      have h2 : ¬(j = k ∧ i = l) := fun h => he (by rw [← h.1, ← h.2, Sym2.eq_swap])
      simp [h1, h2]

/-- The physical inverse `√y_k A⁻¹_kl √y_l` of a normalized matrix `A`. -/
noncomputable def physInv (y : V → ℝ) (A : Matrix V V ℝ) : Matrix V V ℝ :=
  Matrix.of fun k l => Real.sqrt (y k) * A⁻¹ k l * Real.sqrt (y l)

omit [Fintype V] in
theorem entCD_precT (a τ : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) (i j : V) (t₀ : ℝ) :
    EntCD (fun t => precT G a τ y σ S i j t) t₀ :=
  entCD_add (entCD_const _ _)
    (entCD_smul ((contDiffAt_id.sub contDiffAt_const).mul contDiffAt_const) _)

omit [DecidableRel G.Adj] in
theorem entCD_physInv (y : V → ℝ) {A : ℝ → Matrix V V ℝ} {t₀ : ℝ} (hA : EntCD A t₀)
    (hdet : (A t₀).det ≠ 0) : EntCD (fun t => physInv y (A t)) t₀ :=
  fun a b => by
    simp only [physInv, Matrix.of_apply]
    exact (contDiffAt_const.mul (entCD_inv hA hdet a b)).mul contDiffAt_const

end Interp

/-! ### The observables on a pair of precisions -/

section Obs

variable {d p : ℕ} (ct : Contact.{u} d p)

/-- `b₊ = 4a² A_H diag((X_ll/2)²) u` for a shifted inverse `X`. -/
noncomputable def obsBP (X : Matrix ct.V ct.V ℝ) : ct.V → ℝ :=
  (4 * aOf d p ^ 2) • (ct.adjS *ᵥ (diagonal (fun l => (X l l / 2) ^ 2) *ᵥ ct.uvec))

/-- `b₋ = 4a² A_H diag((X_ll/2)(Y_ll/2)) u` for shifted inverses `X = X₊`, `Y = X₋`. -/
noncomputable def obsBM (X Y : Matrix ct.V ct.V ℝ) : ct.V → ℝ :=
  (4 * aOf d p ^ 2) • (ct.adjS *ᵥ (diagonal (fun l => X l l / 2 * (Y l l / 2)) *ᵥ ct.uvec))

/-- `Ψ = H F_ji` of configuration `k` as a function of the pair of normalized precisions
`(A, B) = (P̃⁺, P̃⁻)`: `G^± = physInv y^± (A, B)`, `X_± = physInv y^± ((A, B) + h Y^±_S)`. -/
noncomputable def obsPsi (h : ℝ) (k : Fin 4) (i j : ct.V) (A B : Matrix ct.V ct.V ℝ) : ℝ :=
  match k with
  | 0 => (physInv ct.yp A ct.v ct.v / 2) ^ 2 *
      maskF (physInv ct.yp (A + h • srcDiag ct.yp ct.S))
        (physInv ct.yp (A + h • srcDiag ct.yp ct.S)) ct.uvec j i
  | 1 => (physInv ct.yp A ct.v ct.v / 2) ^ 2 *
      maskF (physInv ct.yp (A + h • srcDiag ct.yp ct.S))
        (physInv ct.yp (A + h • srcDiag ct.yp ct.S))
        (obsBP ct (physInv ct.yp (A + h • srcDiag ct.yp ct.S))) j i
  | 2 => physInv ct.yp A ct.v ct.v * physInv ct.ym B ct.v ct.v / 4 *
      maskF (physInv ct.ym (B + h • srcDiag ct.ym ct.S))
        (physInv ct.yp (A + h • srcDiag ct.yp ct.S)) ct.uvec j i
  | 3 => physInv ct.yp A ct.v ct.v * physInv ct.ym B ct.v ct.v / 4 *
      maskF (physInv ct.ym (B + h • srcDiag ct.ym ct.S))
        (physInv ct.yp (A + h • srcDiag ct.yp ct.S))
        (obsBM ct (physInv ct.yp (A + h • srcDiag ct.yp ct.S))
          (physInv ct.ym (B + h • srcDiag ct.ym ct.S))) j i

theorem obsPsi_precN (h : ℝ) (k : Fin 4) (i j : ct.V) (σ : Config ct.V) :
    obsPsi ct h k i j (precN ct.G (aOf d p) 1 ct.yp σ ct.S)
      (precN ct.G (aOf d p) (-1) ct.ym σ ct.S) = cfgPsi ct h k i j σ := by
  match k with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl

/-- `P̃⁺(t)` along the fibre of `σ` at the edge `ij`. -/
noncomputable def fibPp (σ : Config ct.V) (i j : ct.V) (t : ℝ) : Matrix ct.V ct.V ℝ :=
  precT ct.G (aOf d p) 1 ct.yp σ ct.S i j t

/-- `P̃⁻(t)` along the fibre of `σ` at the edge `ij`. -/
noncomputable def fibPm (σ : Config ct.V) (i j : ct.V) (t : ℝ) : Matrix ct.V ct.V ℝ :=
  precT ct.G (aOf d p) (-1) ct.ym σ ct.S i j t

/-- `φ(t) = W(t) Ψ(t)` along the fibre, `W(t) = (det P̃⁺(t) det P̃⁻(t))^p`. -/
noncomputable def fibPhi (h : ℝ) (k : Fin 4) (i j : ct.V) (σ : Config ct.V) (t : ℝ) : ℝ :=
  ((fibPp ct σ i j t).det * (fibPm ct σ i j t).det) ^ p *
    obsPsi ct h k i j (fibPp ct σ i j t) (fibPm ct σ i j t)

theorem vecCD_obsBP {X : ℝ → Matrix ct.V ct.V ℝ} {t₀ : ℝ} (hX : EntCD X t₀) :
    VecCD (fun t => obsBP ct (X t)) t₀ := by
  unfold obsBP
  exact vecCD_smul _ (vecCD_mulVec (entCD_const _ t₀)
    (vecCD_mulVec (entCD_diagonal fun l => ((hX l l).div_const 2).pow 2) (vecCD_const _ t₀)))

theorem vecCD_obsBM {X Y : ℝ → Matrix ct.V ct.V ℝ} {t₀ : ℝ} (hX : EntCD X t₀)
    (hY : EntCD Y t₀) : VecCD (fun t => obsBM ct (X t) (Y t)) t₀ := by
  unfold obsBM
  exact vecCD_smul _ (vecCD_mulVec (entCD_const _ t₀)
    (vecCD_mulVec (entCD_diagonal fun l => ((hX l l).div_const 2).mul ((hY l l).div_const 2))
      (vecCD_const _ t₀)))

/-- `φ` is `C³` at every `t₀` where `P̃^±(t₀) ≻ 0` (`h ≥ 0`). -/
theorem fibPhi_cdAt {h : ℝ} (hh : 0 ≤ h) (k : Fin 4) (i j : ct.V) (σ : Config ct.V) {t₀ : ℝ}
    (hPD : (fibPp ct σ i j t₀).PosDef ∧ (fibPm ct σ i j t₀).PosDef) :
    ContDiffAt ℝ 3 (fibPhi ct h k i j σ) t₀ := by
  have hsrc : ∀ y : ct.V → ℝ, (∀ k, 0 ≤ y k) → (h • srcDiag y ct.S).PosSemidef := fun y hy => by
    refine Matrix.PosSemidef.smul ?_ hh
    refine Matrix.PosSemidef.diagonal fun l => ?_
    split_ifs
    · exact hy l
    · exact le_rfl
  have hyp : ∀ k, 0 ≤ ct.yp k := fun k => (ct.ctx.hyp k).1
  have hym : ∀ k, 0 ≤ ct.ym k := fun k => (ct.ctx.hym k).1
  have hA : EntCD (fun t => fibPp ct σ i j t) t₀ := entCD_precT ct.G _ _ _ _ _ _ _ t₀
  have hB : EntCD (fun t => fibPm ct σ i j t) t₀ := entCD_precT ct.G _ _ _ _ _ _ _ t₀
  have hAX : EntCD (fun t => fibPp ct σ i j t + h • srcDiag ct.yp ct.S) t₀ :=
    entCD_add hA (entCD_const _ _)
  have hBX : EntCD (fun t => fibPm ct σ i j t + h • srcDiag ct.ym ct.S) t₀ :=
    entCD_add hB (entCD_const _ _)
  have gA := entCD_physInv ct.yp hA hPD.1.det_pos.ne'
  have gB := entCD_physInv ct.ym hB hPD.2.det_pos.ne'
  have xA := entCD_physInv ct.yp hAX (hPD.1.add_posSemidef (hsrc _ hyp)).det_pos.ne'
  have xB := entCD_physInv ct.ym hBX (hPD.2.add_posSemidef (hsrc _ hym)).det_pos.ne'
  have hW : ContDiffAt ℝ 3
      (fun t => ((fibPp ct σ i j t).det * (fibPm ct σ i j t).det) ^ p) t₀ :=
    ((cd_det hA).mul (cd_det hB)).pow p
  have hPsi : ContDiffAt ℝ 3
      (fun t => obsPsi ct h k i j (fibPp ct σ i j t) (fibPm ct σ i j t)) t₀ := by
    match k with
    | 0 =>
      exact (((gA ct.v ct.v).div_const 2).pow 2).mul (cd_maskF xA xA (vecCD_const _ _) j i)
    | 1 =>
      exact (((gA ct.v ct.v).div_const 2).pow 2).mul (cd_maskF xA xA (vecCD_obsBP ct xA) j i)
    | 2 =>
      exact (((gA ct.v ct.v).mul (gB ct.v ct.v)).div_const 4).mul
        (cd_maskF xB xA (vecCD_const _ _) j i)
    | 3 =>
      exact (((gA ct.v ct.v).mul (gB ct.v ct.v)).div_const 4).mul
        (cd_maskF xB xA (vecCD_obsBM ct xA xB) j i)
  exact hW.mul hPsi

theorem sgn_of_eq_one {σ : Config ct.V} {i j : ct.V} (he : σ s(i, j) = 1) : sgn σ i j = 1 := by
  simp [sgn, he]

theorem fibPp_one {σ : Config ct.V} {i j : ct.V} (he : σ s(i, j) = 1) :
    fibPp ct σ i j 1 = precN ct.G (aOf d p) 1 ct.yp σ ct.S := by
  have := precT_sgn ct.G (aOf d p) 1 ct.yp σ ct.S i j
  rwa [sgn_of_eq_one ct he] at this

theorem fibPm_one {σ : Config ct.V} {i j : ct.V} (he : σ s(i, j) = 1) :
    fibPm ct σ i j 1 = precN ct.G (aOf d p) (-1) ct.ym σ ct.S := by
  have := precT_sgn ct.G (aOf d p) (-1) ct.ym σ ct.S i j
  rwa [sgn_of_eq_one ct he] at this

theorem fibPp_neg_one {σ : Config ct.V} {i j : ct.V} (hi : i ∈ ct.S) (hj : j ∈ ct.S)
    (hij : ct.G.Adj i j) :
    fibPp ct σ i j (-1) = precN ct.G (aOf d p) 1 ct.yp (fibFlip ct σ i j) ct.S := by
  rw [fibPp, fibFlip, precN_update ct.G hi hj hij]
  norm_num

theorem fibPm_neg_one {σ : Config ct.V} {i j : ct.V} (hi : i ∈ ct.S) (hj : j ∈ ct.S)
    (hij : ct.G.Adj i j) :
    fibPm ct σ i j (-1) = precN ct.G (aOf d p) (-1) ct.ym (fibFlip ct σ i j) ct.S := by
  rw [fibPm, fibFlip, precN_update ct.G hi hj hij]
  norm_num

/-- `φ(1) = W(σ) Ψ(σ)` at a positive-definite endpoint `σ` (`σ_ij = 1`). -/
theorem fibPhi_one (h : ℝ) (k : Fin 4) {i j : ct.V} {σ : Config ct.V} (he : σ s(i, j) = 1)
    (hPD : (precN ct.G (aOf d p) 1 ct.yp σ ct.S).PosDef ∧
      (precN ct.G (aOf d p) (-1) ct.ym σ ct.S).PosDef) :
    fibPhi ct h k i j σ 1 = wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S * cfgPsi ct h k i j σ := by
  rw [fibPhi, fibPp_one ct he, fibPm_one ct he, obsPsi_precN, wt, if_pos hPD]

/-- `φ(-1) = W(σ') Ψ(σ')` at a positive-definite endpoint `σ'`. -/
theorem fibPhi_neg_one (h : ℝ) (k : Fin 4) {i j : ct.V} {σ : Config ct.V} (hi : i ∈ ct.S)
    (hj : j ∈ ct.S) (hij : ct.G.Adj i j)
    (hPD : (precN ct.G (aOf d p) 1 ct.yp (fibFlip ct σ i j) ct.S).PosDef ∧
      (precN ct.G (aOf d p) (-1) ct.ym (fibFlip ct σ i j) ct.S).PosDef) :
    fibPhi ct h k i j σ (-1) =
      wt ct.G p (aOf d p) ct.yp ct.ym (fibFlip ct σ i j) ct.S *
        cfgPsi ct h k i j (fibFlip ct σ i j) := by
  rw [fibPhi, fibPp_neg_one ct hi hj hij, fibPm_neg_one ct hi hj hij, obsPsi_precN, wt,
    if_pos hPD]

end Obs

/-! ### The analytic sub-nodes -/

/-- **TB.W1fib-seg** (segment positivity). On a regular fibre, `P̃^±(t) ≻ 0` for `t ∈ [-2, 2]`.
Sketch: module docstring. -/
theorem fib_seg_pd {d p : ℕ} (ct : Contact.{u} d p) (hp : 1 ≤ p) {i j : ct.V} (hi : i ∈ ct.N)
    (hj : j ∈ nbhd ct.G ct.S i) {σ : Config ct.V} (he : σ s(i, j) = 1)
    (hreg : fibGood ct i j σ ∨ fibGood ct i j (fibFlip ct σ i j)) {t : ℝ}
    (ht : t ∈ Set.Icc (-2 : ℝ) 2) : (fibPp ct σ i j t).PosDef ∧ (fibPm ct σ i j t).PosDef := by
  have hiS := w1_N_sub_S ct hi
  have hjS : j ∈ ct.S := (Finset.mem_filter.mp hj).1
  have hij : ct.G.Adj i j := (Finset.mem_filter.mp hj).2
  have hyp : ∀ k, 0 ≤ ct.yp k := fun k => (ct.ctx.hyp k).1
  have hym : ∀ k, 0 ≤ ct.ym k := fun k => (ct.ctx.hym k).1
  have ha : 0 ≤ aOf d p := by unfold aOf; positivity
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have key : ∀ τ₀ : Config ct.V, fibGood ct i j τ₀ → ∀ s : ℝ, |s| ≤ 3 →
      (precN ct.G (aOf d p) 1 ct.yp τ₀ ct.S +
        (s * (1 * aOf d p * (Real.sqrt (ct.yp i) * Real.sqrt (ct.yp j)))) •
          SecA.edgeE i j).PosDef ∧
      (precN ct.G (aOf d p) (-1) ct.ym τ₀ ct.S +
        (s * (-1 * aOf d p * (Real.sqrt (ct.ym i) * Real.sqrt (ct.ym j)))) •
          SecA.edgeE i j).PosDef := by
    rintro τ₀ ⟨hw, hg⟩ s hs
    obtain ⟨hPp, hPm⟩ := posDef_of_wt_ne_zero ct.G hw
    obtain ⟨gi1, gi2⟩ := w1_gp_nonneg ct hw i
    obtain ⟨gj1, gj2⟩ := w1_gp_nonneg ct hw j
    have hG0 : 0 ≤ fibG ct τ₀ i j := by unfold fibG; linarith
    have hag : aOf d p * fibG ct τ₀ i j ≤ 1 / 64 := by
      have h0 : 0 ≤ aOf d p * fibG ct τ₀ i j := mul_nonneg ha hG0
      have : 64 * (aOf d p * fibG ct τ₀ i j) ≤ 64 * p * aOf d p * fibG ct τ₀ i j := by
        nlinarith
      linarith
    unfold fibG at hag
    have t1 := mul_nonneg ha gi1
    have t2 := mul_nonneg ha gj1
    have t3 := mul_nonneg ha gi2
    have t4 := mul_nonneg ha gj2
    rw [← abs_of_nonneg ha] at t1 t2 t3 t4 hag
    exact ⟨posDef_precN_add_edge ct.G (by norm_num) hyp hPp hs
        (by unfold Contact.gp at *; nlinarith) (by unfold Contact.gp at *; nlinarith),
      posDef_precN_add_edge ct.G (by norm_num) hym hPm hs (by unfold Contact.gm at *; nlinarith)
        (by unfold Contact.gm at *; nlinarith)⟩
  rcases hreg with hg | hg
  · have hs : |t - 1| ≤ 3 := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
    obtain ⟨k1, k2⟩ := key σ hg (t - 1) hs
    constructor
    · have e : fibPp ct σ i j t = precN ct.G (aOf d p) 1 ct.yp σ ct.S +
          ((t - 1) * (1 * aOf d p * (Real.sqrt (ct.yp i) * Real.sqrt (ct.yp j)))) •
            SecA.edgeE i j := by
        rw [fibPp, precT_recenter _ _ _ _ _ _ _ _ t 1]
        congr 1
        exact fibPp_one ct he
      rw [e]; exact k1
    · have e : fibPm ct σ i j t = precN ct.G (aOf d p) (-1) ct.ym σ ct.S +
          ((t - 1) * (-1 * aOf d p * (Real.sqrt (ct.ym i) * Real.sqrt (ct.ym j)))) •
            SecA.edgeE i j := by
        rw [fibPm, precT_recenter _ _ _ _ _ _ _ _ t 1]
        congr 1
        exact fibPm_one ct he
      rw [e]; exact k2
  · have hs : |t - -1| ≤ 3 := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
    obtain ⟨k1, k2⟩ := key (fibFlip ct σ i j) hg (t - -1) hs
    constructor
    · have e : fibPp ct σ i j t = precN ct.G (aOf d p) 1 ct.yp (fibFlip ct σ i j) ct.S +
          ((t - -1) * (1 * aOf d p * (Real.sqrt (ct.yp i) * Real.sqrt (ct.yp j)))) •
            SecA.edgeE i j := by
        rw [fibPp, precT_recenter _ _ _ _ _ _ _ _ t (-1)]
        congr 1
        exact fibPp_neg_one ct hiS hjS hij
      rw [e]; exact k1
    · have e : fibPm ct σ i j t = precN ct.G (aOf d p) (-1) ct.ym (fibFlip ct σ i j) ct.S +
          ((t - -1) * (-1 * aOf d p * (Real.sqrt (ct.ym i) * Real.sqrt (ct.ym j)))) •
            SecA.edgeE i j := by
        rw [fibPm, precT_recenter _ _ _ _ _ _ _ _ t (-1)]
        congr 1
        exact fibPm_neg_one ct hiS hjS hij
      rw [e]; exact k2

/-- **TB.W1fib-smooth**. `φ` is `C³` on any set where `P̃^±(t) ≻ 0` (`h ≥ 0`). Sketch: module
docstring. -/
theorem fibPhi_contDiffOn {d p : ℕ} (ct : Contact.{u} d p) {h : ℝ} (hh : 0 ≤ h) (k : Fin 4)
    (i j : ct.V) (σ : Config ct.V) {U : Set ℝ}
    (hU : ∀ t ∈ U, (fibPp ct σ i j t).PosDef ∧ (fibPm ct σ i j t).PosDef) :
    ContDiffOn ℝ 3 (fibPhi ct h k i j σ) U :=
  fun t ht => (fibPhi_cdAt ct hh k i j σ (hU t ht)).contDiffWithinAt

end BiluLinial.Tight.SecB
