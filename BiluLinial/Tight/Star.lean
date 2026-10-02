/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.Ctx

/-!
# The root star representation of the paired law

Blueprint node `D-star` (source Section 1.2, "the actual law is `E[ψ] = E_{ν_K} 𝖱[ψΦ]/F_H`";
AUDIT-A §1.3, AUDIT-C §1). For a root `v ∈ S` with `N = N_S(v)`:

* `qRoot_eq_qForm`, `PhiRoot_eq_starPhi`: the root energies of `Tight/Insertion.lean` are the
  quadratic forms of the root matrices `A`, `B` (`rootMat`) at the star vector `ξ = rootSigns σ`,
  and `Φ = starPhi p A B ξ`.
* `wtCore_setRoot`, `rootMat_setRoot`: the core weight and the root matrices do not depend on the
  root signs (`setRoot σ ξ` resets the signs of the root edges `s(v, i)`, `i ∈ N`, to the signs
  of `ξ`).
* `radE_eq_sum`: `𝖱 f` is the uniform average over the sign vectors.
* `sum_wt_mul_eq_star`, `lawE_eq_star`: summing over the root signs first,
  `Σ_σ W(σ) f(σ) = (D_v⁺ D_v⁻)^p Σ_σ W_core(σ) 𝖱[ξ ↦ Φ_σ(ξ) f(setRoot σ ξ)]`.

**Sketch.** `qRoot = bᵀ M⁻¹ b / D_v` with `b_w = τ a √y_w √y_v σ(wv)` on `N` (zero elsewhere) and
`τ² = 1`, so `qRoot = Σ_{i,j ∈ N} ξ_i (a² y_v / D_v) √y_i (M⁻¹)_ij √y_j ξ_j`. The matrices
`precCore` and the diagonal `D` never read the signs of root edges. For each sign vector `ε`,
`σ ↦ setRoot σ ε` is `2^{|N|}`-to-one onto `{σ' : rootSigns σ' = ε}`, so
`Σ_σ g σ = 2^{-|N|} Σ_σ Σ_ε g (setRoot σ ε)`; combine with `wt_eq_wtCore_mul`.

**Checks.** `S = {v}`: `N = ∅`, `𝖱 h = h(0)`, `Φ = 1`, `setRoot σ ξ = σ`, `D_v = 1`. Zero
sources: `√y = 0` kills the corresponding entries on both sides.
-/

@[expose] public section

namespace BiluLinial.Tight

open Matrix MeasureTheory

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

open Classical in
/-- Reset the signs of the root edges `s(v, i)`, `i ∈ N_S(v)`, to the signs of `ξ` (`+1` where
`0 ≤ ξ i`, `-1` otherwise); all other edges keep their sign. -/
noncomputable def setRoot (S : Finset V) (v : V) (σ : Config V) (ξ : nbhd G S v → ℝ) :
    Config V :=
  fun e => if h : ∃ i : nbhd G S v, e = s(v, (i : V)) then (if 0 ≤ ξ h.choose then 1 else -1)
    else σ e

/-- `radPi ι` is the uniform measure on the sign vectors. -/
theorem radPi_eq_sum (ι : Type*) [Fintype ι] [DecidableEq ι] :
    radPi ι = ∑ ε : ι → Bool,
      (2 : ENNReal)⁻¹ ^ Fintype.card ι • Measure.dirac fun i => if ε i then (1 : ℝ) else -1 := by
  classical
  unfold radPi
  refine Measure.pi_eq fun s _ => ?_
  have h1 : ∀ i, radReal (s i) = ∑ b : Bool,
      (2 : ENNReal)⁻¹ * (if (if b then (1 : ℝ) else -1) ∈ s i then 1 else 0) := by
    intro i
    simp only [radReal, Measure.smul_apply, Measure.add_apply, Measure.dirac_apply,
      Set.indicator_apply, Pi.one_apply, smul_eq_mul, Fintype.sum_bool, ↓reduceIte,
      Bool.false_eq_true, mul_add]
  rw [Measure.finsetSum_apply]
  simp only [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply, Set.indicator_apply,
    Pi.one_apply, Set.mem_univ_pi, h1, Fintype.prod_sum, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.prod_boole]

/-- `𝖱 f` is the uniform average of `f` over the sign vectors. -/
theorem radE_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (f : (ι → ℝ) → ℝ) :
    radE f = (∑ ε : ι → Bool, f fun i => if ε i then 1 else -1) / 2 ^ Fintype.card ι := by
  rw [radE, radPi_eq_sum, integral_finsetSum_measure]
  · simp only [integral_smul_measure, integral_dirac, smul_eq_mul, ENNReal.toReal_pow,
      ENNReal.toReal_inv, ENNReal.toReal_ofNat, ← Finset.mul_sum]
    rw [inv_pow, div_eq_inv_mul]
  · exact fun ε _ => (integrable_dirac (by simp)).smul_measure (by simp)

/-! ### Resetting the root signs -/

omit [Fintype V] [DecidableEq V] in
theorem nbhd_adj {S : Finset V} {v : V} (i : nbhd G S v) : G.Adj v i :=
  (Finset.mem_filter.1 i.2).2

omit [Fintype V] in
theorem setRoot_apply_root {S : Finset V} {v : V} (σ : Config V) (ξ : nbhd G S v → ℝ)
    (i : nbhd G S v) : setRoot G S v σ ξ s(v, (i : V)) = if 0 ≤ ξ i then 1 else -1 := by
  have h : ∃ j : nbhd G S v, s(v, (i : V)) = s(v, (j : V)) := ⟨i, rfl⟩
  have hc : h.choose = i := by
    rcases Sym2.eq_iff.1 h.choose_spec with ⟨_, h2⟩ | ⟨_, h2⟩
    · exact Subtype.ext h2.symm
    · exact absurd h2.symm (G.ne_of_adj (nbhd_adj G i))
  simp only [setRoot]
  rw [dite_eq_left h, hc]

omit [Fintype V] in
theorem setRoot_apply_of_not {S : Finset V} {v : V} (σ : Config V) (ξ : nbhd G S v → ℝ)
    {e : Sym2 V} (he : ¬∃ i : nbhd G S v, e = s(v, (i : V))) : setRoot G S v σ ξ e = σ e := by
  simp only [setRoot]
  rw [dite_eq_right he]

omit [Fintype V] in
theorem setRoot_apply_of_ne {S : Finset V} {v : V} (σ : Config V) (ξ : nbhd G S v → ℝ)
    {u w : V} (hu : u ≠ v) (hw : w ≠ v) : setRoot G S v σ ξ s(u, w) = σ s(u, w) := by
  refine setRoot_apply_of_not G σ ξ ?_
  rintro ⟨i, hi⟩
  rcases Sym2.eq_iff.1 hi with ⟨h1, _⟩ | ⟨_, h2⟩
  · exact hu h1
  · exact hw h2

omit [Fintype V] in
theorem setRoot_setRoot {S : Finset V} {v : V} (σ : Config V) (ξ ξ' : nbhd G S v → ℝ) :
    setRoot G S v (setRoot G S v σ ξ) ξ' = setRoot G S v σ ξ' := by
  funext e
  by_cases he : ∃ i : nbhd G S v, e = s(v, (i : V))
  · obtain ⟨i, rfl⟩ := he
    rw [setRoot_apply_root, setRoot_apply_root]
  · rw [setRoot_apply_of_not G _ _ he, setRoot_apply_of_not G _ _ he,
      setRoot_apply_of_not G _ _ he]

omit [Fintype V] in
theorem setRoot_rootSigns {S : Finset V} {v : V} (σ : Config V) :
    setRoot G S v σ (rootSigns G σ S v) = σ := by
  funext e
  by_cases he : ∃ i : nbhd G S v, e = s(v, (i : V))
  · obtain ⟨i, rfl⟩ := he
    rw [setRoot_apply_root]
    simp only [rootSigns, sgn]
    rcases Int.units_eq_one_or (σ s(v, (i : V))) with h | h <;> simp [h]
  · rw [setRoot_apply_of_not G _ _ he]

omit [Fintype V] [DecidableEq V] in
/-- The signs of `σ` at the root, read back from `rootSigns`. -/
theorem signs_rootSigns {S : Finset V} {v : V} (σ : Config V) :
    (fun i => if decide (0 ≤ rootSigns G σ S v i) then (1 : ℝ) else -1) = rootSigns G σ S v := by
  funext i
  simp only [rootSigns, sgn]
  rcases Int.units_eq_one_or (σ s(v, (i : V))) with h | h <;> simp [h]

theorem rootSigns_setRoot {S : Finset V} {v : V} (σ : Config V) {ξ : nbhd G S v → ℝ}
    (hξ : ∀ i, ξ i = 1 ∨ ξ i = -1) : rootSigns G (setRoot G S v σ ξ) S v = ξ := by
  funext i
  simp only [rootSigns, sgn]
  rw [setRoot_apply_root]
  rcases hξ i with h | h <;> norm_num [h]

omit [Fintype V] in
theorem precCore_setRoot (a τ : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) (v : V)
    (ξ : nbhd G S v → ℝ) :
    precCore G a τ y (setRoot G S v σ ξ) S v = precCore G a τ y σ S v := by
  ext u w
  simp only [precCore, precN, Matrix.of_apply]
  by_cases h : u = v ∨ w = v
  · simp only [ite_eq_left h]
  · simp only [ite_eq_right h]
    obtain ⟨hu, hw⟩ := not_or.1 h
    have hs : sgn (setRoot G S v σ ξ) u w = sgn σ u w := by
      unfold sgn
      rw [setRoot_apply_of_ne G σ ξ hu hw]
    rw [hs]

theorem wtCore_setRoot (p : ℕ) (a : ℝ) (yp ym : V → ℝ) (σ : Config V) (S : Finset V) (v : V)
    (ξ : nbhd G S v → ℝ) :
    wtCore G p a yp ym (setRoot G S v σ ξ) S v = wtCore G p a yp ym σ S v := by
  unfold wtCore
  rw [precCore_setRoot, precCore_setRoot]

theorem rootMat_setRoot (a τ : ℝ) (y : V → ℝ) (σ : Config V) (S : Finset V) (v : V)
    (ξ : nbhd G S v → ℝ) :
    rootMat G a τ y (setRoot G S v σ ξ) S v = rootMat G a τ y σ S v := by
  simp only [rootMat, coreGreen, precCore_setRoot]

/-! ### The root energies as quadratic forms -/

omit [Fintype V] in
/-- The incident column: `b_w = τ a √y_v · √y_w σ(vw)` on `N_S(v)`, zero elsewhere. -/
theorem incCol_eq_ite (a τ : ℝ) (y : V → ℝ) (σ : Config V) {S : Finset V} {v : V} (hv : v ∈ S)
    (w : V) : incCol G a τ y σ S v w = if w ∈ nbhd G S v then
      τ * a * Real.sqrt (y v) * (Real.sqrt (y w) * sgn σ v w) else 0 := by
  have hs : sgn σ w v = sgn σ v w := by
    unfold sgn
    rw [Sym2.eq_swap]
  by_cases hw : w = v
  · subst hw
    have : w ∉ nbhd G S w := by simp [nbhd]
    rw [ite_eq_right this]
    simp [incCol]
  · simp only [incCol, precN, Matrix.of_apply, ite_eq_right hw]
    have hN : w ∈ nbhd G S v ↔ w ∈ S ∧ v ∈ S ∧ G.Adj w v := by
      simp only [nbhd, Finset.mem_filter, G.adj_comm v w]
      tauto
    by_cases h : w ∈ nbhd G S v
    · rw [ite_eq_left h, ite_eq_left (hN.1 h), hs]
      ring
    · rw [ite_eq_right h, ite_eq_right (mt hN.2 h)]

theorem qRoot_eq_qForm {a τ : ℝ} (hτ : τ ^ 2 = 1) {y : V → ℝ} (hy : ∀ i, 0 ≤ y i)
    (σ : Config V) {S : Finset V} {v : V} (hv : v ∈ S) :
    qRoot G a τ y σ S v = qForm (rootMat G a τ y σ S v) (rootSigns G σ S v) := by
  have hc : (τ * a * Real.sqrt (y v)) ^ 2 = a ^ 2 * y v := by
    rw [mul_pow, mul_pow, hτ, Real.sq_sqrt (hy v), one_mul]
  have hnum : incCol G a τ y σ S v ⬝ᵥ
      ((precCore G a τ y σ S v)⁻¹ *ᵥ incCol G a τ y σ S v) =
      ∑ i : nbhd G S v, ∑ j : nbhd G S v,
        τ * a * Real.sqrt (y v) * (Real.sqrt (y i) * sgn σ v i) *
          ((precCore G a τ y σ S v)⁻¹ i j *
            (τ * a * Real.sqrt (y v) * (Real.sqrt (y j) * sgn σ v j))) := by
    simp only [dotProduct, mulVec, incCol_eq_ite G a τ y σ hv, mul_ite, mul_zero, ite_mul,
      zero_mul, Finset.sum_ite_mem, Finset.univ_inter]
    simp only [Finset.mul_sum]
    rw [← Finset.sum_coe_sort (nbhd G S v)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_coe_sort (nbhd G S v)]
  rw [qRoot, hnum, qForm]
  simp only [dotProduct, mulVec, rootMat, rootSigns, coreGreen, Matrix.of_apply,
    Finset.sum_div, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  linear_combination (Real.sqrt (y i) * sgn σ v i * (precCore G a τ y σ S v)⁻¹ i j *
    (Real.sqrt (y j) * sgn σ v j) / diagD G a y S v) * hc

theorem PhiRoot_eq_starPhi (p : ℕ) (a : ℝ) {yp ym : V → ℝ} (hyp : ∀ i, 0 ≤ yp i)
    (hym : ∀ i, 0 ≤ ym i) (σ : Config V) {S : Finset V} {v : V} (hv : v ∈ S) :
    PhiRoot G p a yp ym σ S v =
      starPhi p (rootMat G a 1 yp σ S v) (rootMat G a (-1) ym σ S v) (rootSigns G σ S v) := by
  rw [PhiRoot, starPhi, clipF, clipF, qRoot_eq_qForm G (a := a) (τ := 1) (by norm_num) hyp σ hv,
    qRoot_eq_qForm G (a := a) (τ := -1) (by norm_num) hym σ hv, mul_pow]

/-! ### Summing over the root signs -/

/-- Each sign pattern at the root is hit `2^{|N|}` times: `(σ, ε) ↦ (setRoot σ ε, signs of σ)`
is an involution of `Config V × (N → Bool)`. -/
theorem sum_sum_setRoot (S : Finset V) (v : V) (F : Config V → ℝ) :
    ∑ σ : Config V, ∑ ε : nbhd G S v → Bool, F (setRoot G S v σ fun i => if ε i then 1 else -1) =
      2 ^ Fintype.card (nbhd G S v) * ∑ σ, F σ := by
  let Ψ : Config V × (nbhd G S v → Bool) → Config V × (nbhd G S v → Bool) := fun x =>
    (setRoot G S v x.1 (fun i => if x.2 i then 1 else -1),
      fun i => decide (0 ≤ rootSigns G x.1 S v i))
  have hpm : ∀ (ε : nbhd G S v → Bool) i,
      (if ε i then (1 : ℝ) else -1) = 1 ∨ (if ε i then (1 : ℝ) else -1) = -1 := by
    intro ε i
    by_cases h : ε i <;> simp [h]
  have hΨ : Function.Involutive Ψ := by
    rintro ⟨σ, ε⟩
    refine Prod.ext ?_ ?_
    · show setRoot G S v (setRoot G S v σ fun i => if ε i then 1 else -1)
          (fun i => if decide (0 ≤ rootSigns G σ S v i) then 1 else -1) = σ
      rw [setRoot_setRoot, signs_rootSigns, setRoot_rootSigns]
    · show (fun i => decide (0 ≤ rootSigns G (setRoot G S v σ fun i => if ε i then 1 else -1)
          S v i)) = ε
      rw [rootSigns_setRoot G σ (hpm ε)]
      funext i
      by_cases h : ε i <;> simp [h]
  calc ∑ σ : Config V, ∑ ε : nbhd G S v → Bool, F (setRoot G S v σ fun i => if ε i then 1 else -1)
      = ∑ x : Config V × (nbhd G S v → Bool), F (Ψ x).1 := (Fintype.sum_prod_type' _).symm
    _ = ∑ x : Config V × (nbhd G S v → Bool), F x.1 :=
        Equiv.sum_comp hΨ.toPerm (fun x => F x.1)
    _ = ∑ σ : Config V, ∑ _ε : nbhd G S v → Bool, F σ :=
        Fintype.sum_prod_type' fun σ (_ : nbhd G S v → Bool) => F σ
    _ = 2 ^ Fintype.card (nbhd G S v) * ∑ σ, F σ := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, nsmul_eq_mul]
      push_cast
      ring

/-- `D-star`: `Σ_σ W(σ) f(σ) = (D_v⁺ D_v⁻)^p Σ_σ W_core(σ) 𝖱[ξ ↦ Φ_σ(ξ) f(setRoot σ ξ)]`. -/
theorem sum_wt_mul_eq_star {p : ℕ} (hp : 1 ≤ p) (a : ℝ) {yp ym : V → ℝ} (hyp : ∀ i, 0 ≤ yp i)
    (hym : ∀ i, 0 ≤ ym i) {S : Finset V} {v : V} (hv : v ∈ S) (f : Config V → ℝ) :
    ∑ σ : Config V, wt G p a yp ym σ S * f σ =
      (diagD G a yp S v * diagD G a ym S v) ^ p *
        ∑ σ : Config V, wtCore G p a yp ym σ S v *
          radE (fun ξ => starPhi p (rootMat G a 1 yp σ S v) (rootMat G a (-1) ym σ S v) ξ *
            f (setRoot G S v σ ξ)) := by
  have hpm : ∀ (ε : nbhd G S v → Bool) i,
      (if ε i then (1 : ℝ) else -1) = 1 ∨ (if ε i then (1 : ℝ) else -1) = -1 := by
    intro ε i
    by_cases h : ε i <;> simp [h]
  have hcount := sum_sum_setRoot G S v
    (fun σ => wtCore G p a yp ym σ S v * PhiRoot G p a yp ym σ S v * f σ)
  beta_reduce at hcount
  have hF : ∀ σ : Config V, wtCore G p a yp ym σ S v *
      radE (fun ξ => starPhi p (rootMat G a 1 yp σ S v) (rootMat G a (-1) ym σ S v) ξ *
        f (setRoot G S v σ ξ)) =
      (∑ ε : nbhd G S v → Bool,
        wtCore G p a yp ym (setRoot G S v σ fun i => if ε i then 1 else -1) S v *
          PhiRoot G p a yp ym (setRoot G S v σ fun i => if ε i then 1 else -1) S v *
            f (setRoot G S v σ fun i => if ε i then 1 else -1)) /
        2 ^ Fintype.card (nbhd G S v) := by
    intro σ
    rw [radE_eq_sum, mul_div_assoc', Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun ε _ => ?_
    rw [wtCore_setRoot, PhiRoot_eq_starPhi G p a hyp hym _ hv, rootMat_setRoot, rootMat_setRoot,
      rootSigns_setRoot G σ (hpm ε)]
    ring
  simp only [hF]
  rw [← Finset.sum_div, hcount, mul_div_cancel_left₀ _ (pow_ne_zero _ two_ne_zero),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [wt_eq_wtCore_mul G hp a hyp hym σ hv]
  ring

/-- `D-star`, law form: `E f = E_core 𝖱[Φ f] / E_core 𝖱[Φ]`. -/
theorem lawE_eq_star {p : ℕ} (hp : 1 ≤ p) (a : ℝ) {yp ym : V → ℝ} (hyp : ∀ i, 0 ≤ yp i)
    (hym : ∀ i, 0 ≤ ym i) {S : Finset V} {v : V} (hv : v ∈ S) (f : Config V → ℝ) :
    lawE G p a yp ym S f =
      (∑ σ : Config V, wtCore G p a yp ym σ S v *
          radE (fun ξ => starPhi p (rootMat G a 1 yp σ S v) (rootMat G a (-1) ym σ S v) ξ *
            f (setRoot G S v σ ξ))) /
        ∑ σ : Config V, wtCore G p a yp ym σ S v *
          radE (fun ξ => starPhi p (rootMat G a 1 yp σ S v) (rootMat G a (-1) ym σ S v) ξ) := by
  have hD : ∀ y : V → ℝ, (∀ i, 0 ≤ y i) → 0 < diagD G a y S v := by
    intro y hy
    have hs : 0 ≤ ∑ j ∈ nbhd G S v, cEdge a y v j := Finset.sum_nonneg fun j _ => by
      have h0 : 0 ≤ a ^ 2 * y v * y j := by
        have := hy v
        have := hy j
        positivity
      have h1 : 1 ≤ Real.sqrt (1 + 4 * (a ^ 2 * y v * y j)) :=
        Real.one_le_sqrt.mpr (by linarith)
      unfold cEdge cRoot
      exact div_nonneg (by linarith) (by norm_num)
    unfold diagD
    linarith
  have hpos : (diagD G a yp S v * diagD G a ym S v) ^ p ≠ 0 :=
    pow_ne_zero _ (mul_pos (hD yp hyp) (hD ym hym)).ne'
  have h1 := sum_wt_mul_eq_star G hp a hyp hym hv f
  have h2 := sum_wt_mul_eq_star G hp a hyp hym hv (fun _ => 1)
  simp only [mul_one] at h2
  rw [lawE, Zw, h1, h2, mul_div_mul_left _ _ hpos]

end BiluLinial.Tight
