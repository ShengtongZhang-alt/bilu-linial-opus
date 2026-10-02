/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecA.Star
public import BiluLinial.Tight.SecA.ConcAux

/-!
# Length-bounded majorants, reciprocals and clipped observables with a smooth prefactor
(node `A-MAJr`)

Extension of `A-MAJ` (`SecA.StarCalc.MajAt`, `SecA/StarSmooth.lean`) used by TB.WT5r°: the
weights of (WT2) contain shifted inverse diagonals, whose star form has the reciprocal of a
shifted quadratic `α_h = 1 - q_{A_h}`.

* `MajN N x₀ λ M K f`: `f` smooth and `|∂^l f(x₀)| ≤ M K^{|l|} λ^l` for every list `l` with
  `|l| ≤ N`; closed under products (`MajN.mul`, Leibniz with sublists only) and powers.
* `psiCut δ`: a smooth function with `psiCut δ t = t` for `t ≥ δ/2` and `psiCut δ t ≥ δ/4`
  (`Real.smoothTransition`), so `(psiCut δ ∘ g)⁻¹` is a global smooth version of `1/g` where
  `g ≥ δ/2`.
* `majN_recip`: if `g` is a quadratic satisfying `QuadMaj` at `x₀` with scale `m = g(x₀) > δ/2`,
  then `(psiCut δ ∘ g)⁻¹^k` is `MajN N` with `M = m^{-k}`, `K = 4(k + N)`. Proof: near `x₀`,
  `∂_i (1/g)^{k'} = -k' ∂_i g · (1/g)^{k'+1}`; induction on the length with `k' + |l| ≤ k + N`,
  the affine factor `∂_i g` having `MajN` with `M = 2mλ_i`, `K = 1`, and
  `2k'(1+K)^n ≤ 4k' K^n ≤ K^{n+1}` (`(1 + 1/K)^n ≤ e^{1/4} ≤ 2` for `n ≤ K/4`).
* `pderivList_clipObs_le_majN`: `A-MAJ` for `clipObs G e₁ e₂ A B` at an interior point with any
  smooth prefactor `G` having `MajN`.

Checks: `k = 1`, `l = [i]`: `|∂_i(1/g)| = |∂_i g|/m² ≤ 2λ_i/m ≤ m⁻¹ · 4(1+N) λ_i`.
-/

@[expose] public section

namespace BiluLinial.Tight.SecA.CR

open Matrix StarCalc
open scoped ContDiff Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `f` is smooth and `|∂^l f(x₀)| ≤ M K^{|l|} λ^l` for every list `l` of length `≤ N`. -/
def MajN (N : ℕ) (x₀ lam : ι → ℝ) (M K : ℝ) (f : (ι → ℝ) → ℝ) : Prop :=
  ContDiff ℝ ∞ f ∧ ∀ l : List ι, l.length ≤ N →
    |pderivList l f x₀| ≤ M * K ^ l.length * (l.map lam).prod

/-- Leibniz closure with sublists only. -/
theorem majBoundN_mul {x₀ lam : ι → ℝ} {K₁ K₂ : ℝ} :
    ∀ (l : List ι) {f g : (ι → ℝ) → ℝ} {M₁ M₂ : ℝ}, ContDiff ℝ ∞ f → ContDiff ℝ ∞ g →
      (∀ l' : List ι, l'.length ≤ l.length →
        |pderivList l' f x₀| ≤ M₁ * K₁ ^ l'.length * (l'.map lam).prod) →
      (∀ l' : List ι, l'.length ≤ l.length →
        |pderivList l' g x₀| ≤ M₂ * K₂ ^ l'.length * (l'.map lam).prod) →
      |pderivList l (f * g) x₀| ≤ M₁ * M₂ * (K₁ + K₂) ^ l.length * (l.map lam).prod
  | [], f, g, M₁, M₂, _, _, hf, hg => by
    have h1 := hf [] le_rfl
    have h2 := hg [] le_rfl
    simp only [pderivList_nil, List.length_nil, pow_zero, mul_one, List.map_nil,
      List.prod_nil] at h1 h2
    simp only [pderivList_nil, Pi.mul_apply, abs_mul, List.length_nil, pow_zero, mul_one,
      List.map_nil, List.prod_nil]
    exact mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1)
  | i :: l, f, g, M₁, M₂, hfc, hgc, hf, hg => by
    have hf' : ∀ l' : List ι, l'.length ≤ l.length → |pderivList l' (pderiv i f) x₀| ≤
        (M₁ * K₁ * lam i) * K₁ ^ l'.length * (l'.map lam).prod := fun l' hl' => by
      have h := hf (i :: l') (by simp; omega)
      simp only [pderivList_cons, List.length_cons, List.map_cons, List.prod_cons,
        pow_succ] at h
      exact h.trans_eq (by ring)
    have hg' : ∀ l' : List ι, l'.length ≤ l.length → |pderivList l' (pderiv i g) x₀| ≤
        (M₂ * K₂ * lam i) * K₂ ^ l'.length * (l'.map lam).prod := fun l' hl' => by
      have h := hg (i :: l') (by simp; omega)
      simp only [pderivList_cons, List.length_cons, List.map_cons, List.prod_cons,
        pow_succ] at h
      exact h.trans_eq (by ring)
    have hfr : ∀ l' : List ι, l'.length ≤ l.length →
        |pderivList l' f x₀| ≤ M₁ * K₁ ^ l'.length * (l'.map lam).prod :=
      fun l' hl' => hf l' (by simp; omega)
    have hgr : ∀ l' : List ι, l'.length ≤ l.length →
        |pderivList l' g x₀| ≤ M₂ * K₂ ^ l'.length * (l'.map lam).prod :=
      fun l' hl' => hg l' (by simp; omega)
    have h1 := majBoundN_mul l (contDiff_pderiv_top hfc i) hgc hf' hgr
    have h2 := majBoundN_mul l hfc (contDiff_pderiv_top hgc i) hfr hg'
    rw [pderivList_cons, pderiv_mul (differentiable_of_top hfc) (differentiable_of_top hgc),
      pderivList_add l (f := pderiv i f * g) (g := f * pderiv i g)
        ((contDiff_pderiv_top hfc i).mul hgc) (hfc.mul (contDiff_pderiv_top hgc i)), Pi.add_apply]
    simp only [List.length_cons, List.map_cons, List.prod_cons, pow_succ]
    calc _ ≤ _ := abs_add_le _ _
      _ ≤ _ := add_le_add h1 h2
      _ = _ := by ring

theorem MajN.mul {N : ℕ} {x₀ lam : ι → ℝ} {M₁ M₂ K₁ K₂ : ℝ} {f g : (ι → ℝ) → ℝ}
    (hf : MajN N x₀ lam M₁ K₁ f) (hg : MajN N x₀ lam M₂ K₂ g) :
    MajN N x₀ lam (M₁ * M₂) (K₁ + K₂) (f * g) :=
  ⟨hf.1.mul hg.1, fun l hl => majBoundN_mul l hf.1 hg.1 (fun l' hl' => hf.2 l' (hl'.trans hl))
    (fun l' hl' => hg.2 l' (hl'.trans hl))⟩

theorem MajN.of_majAt {N : ℕ} {x₀ lam : ι → ℝ} {M K : ℝ} {f : (ι → ℝ) → ℝ}
    (hf : MajAt x₀ lam M K f) : MajN N x₀ lam M K f :=
  ⟨hf.1, fun l _ => hf.2 l⟩

theorem majN_one (N : ℕ) (x₀ lam : ι → ℝ) : MajN N x₀ lam 1 0 (1 : (ι → ℝ) → ℝ) :=
  MajN.of_majAt (majAt_one x₀ lam)

theorem MajN.pow {N : ℕ} {x₀ lam : ι → ℝ} {M K : ℝ} {f : (ι → ℝ) → ℝ}
    (hf : MajN N x₀ lam M K f) (e : ℕ) : MajN N x₀ lam (M ^ e) (e * K) (f ^ e) := by
  induction e with
  | zero => simpa using majN_one N x₀ lam
  | succ e ih =>
    have e' : ((e + 1 : ℕ) : ℝ) * K = e * K + K := by push_cast; ring
    rw [e', pow_succ, pow_succ]
    exact ih.mul hf

theorem majN_quadFn {N : ℕ} {c : ℝ} {ℓ : ι → ℝ} {Q : Matrix ι ι ℝ} {x₀ : ι → ℝ} {m : ℝ}
    {lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i) (h : QuadMaj c ℓ Q x₀ m lam) :
    MajN N x₀ lam m 2 (quadFn c ℓ Q) :=
  MajN.of_majAt (majAt_quadFn hlam h)

/-- A constant: `M = |c|`, `K = 0`. -/
theorem majN_const (N : ℕ) (x₀ lam : ι → ℝ) (c : ℝ) :
    MajN N x₀ lam |c| 0 (fun _ : ι → ℝ => c) := by
  refine ⟨contDiff_const, fun l _ => ?_⟩
  cases l with
  | nil => simp
  | cons i l =>
    rw [pderivList_cons, pderiv_const c i, pderivList_zero]
    simp

theorem MajN.mono {N : ℕ} {x₀ lam : ι → ℝ} {M M' K K' : ℝ} {f : (ι → ℝ) → ℝ}
    (hf : MajN N x₀ lam M K f) (hlam : ∀ i, 0 ≤ lam i) (hK : 0 ≤ K) (hM : M ≤ M')
    (hKK : K ≤ K') : MajN N x₀ lam M' K' f := by
  refine ⟨hf.1, fun l hl => (hf.2 l hl).trans ?_⟩
  have hP := prod_map_nonneg hlam l
  have hM0 : 0 ≤ M := (abs_nonneg _).trans ((hf.2 [] (Nat.zero_le _)).trans (by simp))
  have h1 : K ^ l.length ≤ K' ^ l.length := pow_le_pow_left₀ hK hKK _
  have h2 : M * K ^ l.length ≤ M' * K' ^ l.length :=
    mul_le_mul hM h1 (pow_nonneg hK _) (hM0.trans hM)
  exact mul_le_mul_of_nonneg_right h2 hP

/-! ### A smooth cut-off of `t ↦ t` away from `0` -/

/-- `psiCut δ t = t` for `t ≥ δ/2` and `psiCut δ t ≥ δ/4`. -/
noncomputable def psiCut (δ t : ℝ) : ℝ :=
  δ / 4 + (t - δ / 4) * Real.smoothTransition ((t - δ / 4) / (δ / 4))

theorem contDiff_psiCut (δ : ℝ) : ContDiff ℝ ∞ (psiCut δ) := by
  unfold psiCut
  have h : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  exact contDiff_const.add ((contDiff_id.sub contDiff_const).mul
    (h.comp ((contDiff_id.sub contDiff_const).div_const _)))

theorem psiCut_ge {δ : ℝ} (hδ : 0 < δ) (t : ℝ) : δ / 4 ≤ psiCut δ t := by
  unfold psiCut
  rcases le_or_gt (δ / 4) t with h | h
  · have := Real.smoothTransition.nonneg ((t - δ / 4) / (δ / 4))
    nlinarith
  · rw [Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith)
      (by linarith))]
    linarith

theorem psiCut_eq {δ : ℝ} (hδ : 0 < δ) {t : ℝ} (ht : δ / 2 ≤ t) : psiCut δ t = t := by
  unfold psiCut
  rw [Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ (by linarith)]; linarith)]
  ring

/-! ### Reciprocals of quadratics -/

/-- The affine factor `∂_i g` of a quadratic with `QuadMaj` scale `m`: `M = 2mλ_i`, `K = 1`. -/
theorem majN_pderiv_quadFn {N : ℕ} {c : ℝ} {ℓ : ι → ℝ} {Q : Matrix ι ι ℝ} {x₀ : ι → ℝ}
    {m : ℝ} {lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i) (h : QuadMaj c ℓ Q x₀ m lam) (i : ι) :
    MajN N x₀ lam (2 * m * lam i) 1 (pderiv i (quadFn c ℓ Q)) := by
  have hm : 0 ≤ m := (abs_nonneg _).trans h.h0
  have hφ : pderiv i (quadFn c ℓ Q) = fun x => ℓ i + ((Q + Qᵀ) *ᵥ x) i := pderiv_quadFn c ℓ Q i
  refine ⟨contDiff_pderiv_top (contDiff_quadFn c ℓ Q) i, fun l _ => ?_⟩
  rw [hφ]
  rcases l with _ | ⟨j, _ | ⟨k, l⟩⟩
  · simpa using h.h1 i
  · simp only [pderivList_cons, pderivList_nil, pderiv_affine, List.length_cons,
      List.length_nil, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      Matrix.add_apply, Matrix.transpose_apply]
    have h2 := h.h2 i j
    norm_num
    linarith
  · rw [pderivList_cons, pderivList_cons, pderiv_affine, pderiv_const, pderivList_zero]
    simp only [Pi.zero_apply, abs_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg zero_le_two hm) (hlam i))
      (pow_nonneg zero_le_one _)) (prod_map_nonneg hlam _)

/-- Near a point where `g > δ/2`: `∂_i (ψ∘g)^{-k} = -k ∂_i g (ψ∘g)^{-(k+1)}`. -/
theorem pderiv_recip_pow_eventually {g : (ι → ℝ) → ℝ} (hg : ContDiff ℝ ∞ g) {δ : ℝ}
    (hδ : 0 < δ) {x₀ : ι → ℝ} (hx₀ : δ / 2 < g x₀) (k : ℕ) (i : ι) :
    pderiv i (fun x => (psiCut δ (g x))⁻¹ ^ k) =ᶠ[𝓝 x₀]
      fun x => -(k : ℝ) * (pderiv i g x * (psiCut δ (g x))⁻¹ ^ (k + 1)) := by
  have hU : IsOpen {x | δ / 2 < g x} := isOpen_lt continuous_const hg.continuous
  filter_upwards [hU.mem_nhds hx₀] with x hx
  have hloc : (fun y => (psiCut δ (g y))⁻¹ ^ k) =ᶠ[𝓝 x] fun y => (g y)⁻¹ ^ k := by
    filter_upwards [hU.mem_nhds hx] with y hy
    rw [psiCut_eq hδ hy.le]
  have hgx : g x ≠ 0 := by linarith
  have hd : HasFDerivAt g (fderiv ℝ g x) x := (differentiable_of_top hg x).hasFDerivAt
  have hinv : HasFDerivAt (fun y => (g y)⁻¹) (-((g x ^ 2)⁻¹ • fderiv ℝ g x)) x := by
    have := (hasDerivAt_inv hgx).comp_hasFDerivAt x hd
    simpa [Function.comp_def, smul_eq_mul] using this
  have hpow := hinv.pow k
  unfold pderiv
  rw [hloc.fderiv_eq, hpow.fderiv]
  simp only [_root_.smul_apply, smul_eq_mul, _root_.neg_apply]
  rw [psiCut_eq hδ hx.le]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [Nat.add_sub_cancel, ← inv_pow]
    push_cast
    ring

/-- `A-MAJr`: majorant of the cut-off reciprocal powers of a quadratic. -/
theorem majN_recip {N : ℕ} {x₀ lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i) {c : ℝ} {ℓ : ι → ℝ}
    {Q : Matrix ι ι ℝ} {m : ℝ} (hg : QuadMaj c ℓ Q x₀ m lam) (hm : quadFn c ℓ Q x₀ = m)
    {δ : ℝ} (hδ : 0 < δ) (hm2 : δ / 2 < m) (k : ℕ) (hk : 1 ≤ k) :
    MajN N x₀ lam (m⁻¹ ^ k) (4 * (k + N)) (fun x => (psiCut δ (quadFn c ℓ Q x))⁻¹ ^ k) := by
  set g := quadFn c ℓ Q with hgdef
  have hgc : ContDiff ℝ ∞ g := contDiff_quadFn c ℓ Q
  have hm0 : 0 < m := by linarith
  have hψ : ContDiff ℝ ∞ fun x => psiCut δ (g x) := (contDiff_psiCut δ).comp hgc
  have hψ0 : ∀ x, psiCut δ (g x) ≠ 0 := fun x => by linarith [psiCut_ge hδ (g x)]
  have hwc : ∀ k' : ℕ, ContDiff ℝ ∞ fun x => (psiCut δ (g x))⁻¹ ^ k' := fun k' =>
    (hψ.inv hψ0).pow k'
  have hw₀ : (psiCut δ (g x₀))⁻¹ = m⁻¹ := by rw [hm, psiCut_eq hδ hm2.le]
  set K : ℝ := 4 * ((k : ℝ) + N) with hK
  have hK1 : (1 : ℝ) ≤ K := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    linarith
  have hK0 : 0 < K := by linarith
  -- the main claim, by induction on the length bound
  have key : ∀ n : ℕ, ∀ l : List ι, l.length ≤ n → l.length ≤ N → ∀ k' : ℕ, 1 ≤ k' →
      k' + l.length ≤ k + N →
      |pderivList l (fun x => (psiCut δ (g x))⁻¹ ^ k') x₀| ≤
        m⁻¹ ^ k' * K ^ l.length * (l.map lam).prod := by
    intro n
    induction n with
    | zero =>
      intro l hl _ k' _ _
      rcases l with _ | ⟨i, l⟩
      · simp only [pderivList_nil, List.length_nil, pow_zero, mul_one, List.map_nil,
          List.prod_nil, hw₀]
        rw [abs_of_nonneg (pow_nonneg (inv_nonneg.2 hm0.le) _)]
      · simp at hl
    | succ n ih =>
      intro l hl hlN k' hk' hkl
      rcases Nat.lt_or_ge l.length (n + 1) with hlt | hge
      · exact ih l (by omega) hlN k' hk' hkl
      rcases l with _ | ⟨i, l'⟩
      · simp at hge
      have hl' : l'.length = n := by simp at hl hge; omega
      -- `∂_i w^{k'} = -k' ∂_i g w^{k'+1}` near `x₀`
      have hev := pderiv_recip_pow_eventually hgc hδ (hm ▸ hm2 : δ / 2 < g x₀) k' i
      rw [pderivList_cons, (pderivList_congr_nhds hev l').eq_of_nhds]
      have hφ := majN_pderiv_quadFn (N := N) hlam hg i
      have hprod : |pderivList l' ((fun _ : ι → ℝ => -(k' : ℝ)) *
          (pderiv i g * fun x => (psiCut δ (g x))⁻¹ ^ (k' + 1))) x₀| ≤
          |(-(k' : ℝ))| * ((2 * m * lam i) * m⁻¹ ^ (k' + 1)) * (0 + (1 + K)) ^ l'.length *
            (l'.map lam).prod := by
        refine majBoundN_mul l' contDiff_const
          ((contDiff_pderiv_top hgc i).mul (hwc (k' + 1)))
          (fun l'' hl'' => (majN_const N x₀ lam (-(k' : ℝ))).2 l'' (by simp at hlN; omega))
          (fun l'' hl'' => ?_)
        exact majBoundN_mul l'' (contDiff_pderiv_top hgc i) (hwc (k' + 1))
          (fun l₃ hl₃ => hφ.2 l₃ (by simp at hlN; omega))
          (fun l₃ hl₃ => ih l₃ (by omega) (by simp at hlN; omega) (k' + 1) (by omega)
            (by simp at hkl; omega))
      have e : (fun x => -(k' : ℝ) * (pderiv i g x * (psiCut δ (g x))⁻¹ ^ (k' + 1))) =
          (fun _ : ι → ℝ => -(k' : ℝ)) *
            (pderiv i g * fun x => (psiCut δ (g x))⁻¹ ^ (k' + 1)) := rfl
      rw [e]
      refine hprod.trans ?_
      -- `2 k' (1 + K)^n ≤ K^{n+1}`
      have hn : (n : ℝ) ≤ K / 4 := by
        have : (n : ℝ) ≤ N := by exact_mod_cast (show n ≤ N by simp at hlN; omega)
        have : (0 : ℝ) ≤ k := Nat.cast_nonneg _
        rw [hK]; linarith
      have hk'K : 4 * (k' : ℝ) ≤ K := by
        have : (k' : ℝ) + n + 1 ≤ k + N := by
          have := hkl; simp at this; exact_mod_cast (by omega : k' + n + 1 ≤ k + N)
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg _
        rw [hK]; linarith
      have hexp : (1 + K) ^ n ≤ 2 * K ^ n := by
        have h1 : (1 + K) ^ n = K ^ n * (1 + 1 / K) ^ n := by
          rw [← mul_pow, show K * (1 + 1 / K) = 1 + K by
            rw [mul_add, mul_one, mul_one_div_cancel hK0.ne']; ring]
        have h2 : (1 + 1 / K) ^ n ≤ Real.exp (1 / K * (K / 4)) :=
          SecA.one_add_pow_le_exp (by positivity) hn
        have h3 : Real.exp (1 / K * (K / 4)) ≤ 2 := by
          rw [show 1 / K * (K / 4) = 1 / 4 by field_simp]
          have h4 : Real.exp (1 / 4) ^ 4 = Real.exp 1 := by
            rw [← Real.exp_nat_mul]; norm_num
          by_contra hc
          push Not at hc
          have h5 := pow_lt_pow_left₀ hc (by norm_num) (by norm_num : (4 : ℕ) ≠ 0)
          have h6 := Real.exp_one_lt_d9
          rw [h4] at h5
          norm_num at h5 h6
          linarith
        rw [h1]
        exact (mul_le_mul_of_nonneg_left (h2.trans h3) (pow_nonneg hK0.le _)).trans_eq
          (by ring)
      have hP := prod_map_nonneg hlam l'
      have hmi : 0 ≤ m⁻¹ := inv_nonneg.2 hm0.le
      simp only [List.length_cons, List.map_cons, List.prod_cons, hl', abs_neg,
        Nat.abs_cast, zero_add]
      have hmm : (2 * m * lam i) * m⁻¹ ^ (k' + 1) = 2 * lam i * m⁻¹ ^ k' := by
        rw [pow_succ]; field_simp
      rw [hmm]
      have hli := hlam i
      have hA : (k' : ℝ) * (2 * lam i * m⁻¹ ^ k') * (1 + K) ^ n ≤
          (k' : ℝ) * (2 * lam i * m⁻¹ ^ k') * (2 * K ^ n) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
      calc (k' : ℝ) * (2 * lam i * m⁻¹ ^ k') * (1 + K) ^ n * (l'.map lam).prod
          ≤ (k' : ℝ) * (2 * lam i * m⁻¹ ^ k') * (2 * K ^ n) * (l'.map lam).prod :=
            mul_le_mul_of_nonneg_right hA hP
        _ = m⁻¹ ^ k' * (4 * k') * K ^ n * (lam i * (l'.map lam).prod) := by ring
        _ ≤ m⁻¹ ^ k' * K * K ^ n * (lam i * (l'.map lam).prod) := by
            gcongr
        _ = m⁻¹ ^ k' * K ^ (n + 1) * (lam i * (l'.map lam).prod) := by ring
  refine ⟨hwc k, fun l hl => ?_⟩
  exact key l.length l le_rfl hl k hk (by omega)

/-- `A-MAJ` for a clipped observable with a smooth prefactor having `MajN`, at an interior
point. -/
theorem pderivList_clipObs_le_majN {A B : Matrix ι ι ℝ} {e₁ e₂ N : ℕ} {G : (ι → ℝ) → ℝ}
    {x₀ lam : ι → ℝ} (hα : qForm A x₀ < 1) (hβ : qForm B x₀ < 1) (hlam : ∀ i, 0 ≤ lam i)
    {MG KG mα mβ : ℝ} (hG : MajN N x₀ lam MG KG G) (hA : QuadMaj 1 0 (-A) x₀ mα lam)
    (hB : QuadMaj 1 0 (-B) x₀ mβ lam) (l : List ι) (hl : l.length ≤ N) :
    |pderivList l (clipObs G e₁ e₂ A B) x₀| ≤
      MG * mα ^ e₁ * mβ ^ e₂ * (KG + 2 * e₁ + 2 * e₂) ^ l.length * (l.map lam).prod := by
  have hM := (hG.mul ((majN_quadFn (N := N) hlam hA).pow e₁)).mul
    ((majN_quadFn (N := N) hlam hB).pow e₂)
  have hev : clipObs G e₁ e₂ A B =ᶠ[𝓝 x₀]
      G * quadFn 1 0 (-A) ^ e₁ * quadFn 1 0 (-B) ^ e₂ := by
    filter_upwards [(isOpen_lt (continuous_qForm A) continuous_const).mem_nhds hα,
      (isOpen_lt (continuous_qForm B) continuous_const).mem_nhds hβ] with x hxA hxB
    simp only [clipObs, Pi.mul_apply, Pi.pow_apply, clipF_eq_of_lt hxA, clipF_eq_of_lt hxB,
      quadFn_one_zero_neg]
  rw [(pderivList_congr_nhds hev l).eq_of_nhds]
  have h := hM.2 l hl
  have hK : KG + e₁ * 2 + e₂ * 2 = KG + 2 * e₁ + 2 * e₂ := by ring
  rw [hK] at h
  calc _ ≤ _ := h
    _ = _ := by ring

end BiluLinial.Tight.SecA.CR
