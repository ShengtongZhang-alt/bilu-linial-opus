/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecA.Star

/-!
# Derivative bounds at a point (helpers for TB.WT5l)

Generic estimates for iterated partial derivatives `∂^l f(x₀) = pderivList l f x₀` of smooth
functions on `ι → ℝ`, with weights `w ≥ 0` (`Π_{s ∈ l} w_s = (l.map w).prod`):

* `rfac m n = m (m+1) ⋯ (m+n-1)`; the class `|∂^l f(x₀)| ≤ B rfac m |l| Π w` is closed under
  products, `(B₁, m₁) · (B₂, m₂) ↦ (B₁B₂, m₁+m₂)` (`rfBound_mul`), by head-splitting and
  `rfac m (n+1) = m · rfac (m+1) n` (no Vandermonde identity needed).
* `majBound_mul_len`: the class `|∂^l f(x₀)| ≤ M K^{|l|} Π w` for lists of length `≤ n` is closed
  under products, `K ↦ K₁ + K₂`.
* `quad_leibniz`: for `|∂^l f(x₀)| ≤ M κ^{|l|}` and a quadratic `q`, the three-term Leibniz
  bound `κ² |∂^l(f q)(x₀)| ≤ M (κ^{n+2}|q(x₀)| + κ^{n+1} Q₁(l) + κ^n Q₂(l))`, `Q₁`, `Q₂` the
  sums of first and (unordered pair) second derivatives of `q` over the positions of `l`.
-/

@[expose] public section

namespace BiluLinial.Tight.SecB

open Matrix SecA.StarCalc
open scoped ContDiff Topology

/-! ### A smooth cut-off -/

/-- `psiW δ t = δ/4 + (t - δ/4) s((t - δ/4)/(δ/4))`, `s` the smooth transition. -/
noncomputable def psiW (δ t : ℝ) : ℝ :=
  δ / 4 + (t - δ / 4) * Real.smoothTransition ((t - δ / 4) / (δ / 4))

theorem contDiff_psiW (δ : ℝ) : ContDiff ℝ ∞ (psiW δ) := by
  unfold psiW
  exact contDiff_const.add ((contDiff_id.sub contDiff_const).mul
    (Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)))

theorem psiW_ge {δ : ℝ} (hδ : 0 < δ) (t : ℝ) : δ / 4 ≤ psiW δ t := by
  unfold psiW
  rcases le_or_gt t (δ / 4) with ht | ht
  · rw [Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith)
      (by linarith)), mul_zero, add_zero]
  · have := Real.smoothTransition.nonneg ((t - δ / 4) / (δ / 4))
    nlinarith

theorem psiW_eq {δ : ℝ} (hδ : 0 < δ) {t : ℝ} (ht : δ / 2 ≤ t) : psiW δ t = t := by
  unfold psiW
  rw [Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ (by linarith)]; linarith)]
  ring

theorem psiW_pos {δ : ℝ} (hδ : 0 < δ) (t : ℝ) : 0 < psiW δ t :=
  lt_of_lt_of_le (by linarith) (psiW_ge hδ t)

/-! ### Smoothness of determinants and adjugate entries -/

section Smooth

variable {ι V : Type*} [Fintype ι] [Fintype V] [DecidableEq V]

theorem contDiff_det_of_entries {M : (ι → ℝ) → Matrix V V ℝ}
    (hM : ∀ u w, ContDiff ℝ ∞ fun x => M x u w) : ContDiff ℝ ∞ fun x => (M x).det := by
  simp only [Matrix.det_apply']
  exact ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun k _ => hM _ _)

theorem contDiff_adjugate_apply_of_entries {M : (ι → ℝ) → Matrix V V ℝ}
    (hM : ∀ u w, ContDiff ℝ ∞ fun x => M x u w) (k l : V) :
    ContDiff ℝ ∞ fun x => (M x).adjugate k l := by
  simp only [Matrix.adjugate_apply]
  refine contDiff_det_of_entries fun u w => ?_
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact contDiff_const
  · exact hM u w

theorem inv_apply_eq_adjugate_div {M : Matrix V V ℝ}
    (hM : M.det ≠ 0) (k l : V) : M⁻¹ k l = M.adjugate k l / M.det := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul, div_eq_inv_mul]

end Smooth

/-! ### Rising factorials -/

/-- The rising factorial `rfac m n = m (m+1) ⋯ (m+n-1)` (real `m`). -/
noncomputable def rfac (m : ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => rfac m n * (m + n)

@[simp] theorem rfac_zero (m : ℝ) : rfac m 0 = 1 := rfl

theorem rfac_succ (m : ℝ) (n : ℕ) : rfac m (n + 1) = rfac m n * (m + n) := rfl

theorem rfac_succ' (m : ℝ) (n : ℕ) : rfac m (n + 1) = m * rfac (m + 1) n := by
  induction n with
  | zero => simp [rfac]
  | succ n ih =>
    rw [rfac_succ, ih, rfac_succ]
    push_cast
    ring

theorem rfac_nonneg {m : ℝ} (hm : 0 ≤ m) (n : ℕ) : 0 ≤ rfac m n := by
  induction n with
  | zero => simp
  | succ n ih => rw [rfac_succ]; positivity

theorem rfac_le_pow {m : ℝ} (hm : 0 ≤ m) {n N : ℕ} (hn : n ≤ N) : rfac m n ≤ (m + N) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [rfac_succ, pow_succ]
    have h1 := ih (by omega)
    have h2 : m + (n : ℝ) ≤ m + N := by
      have : (n : ℝ) ≤ N := by exact_mod_cast (by omega : n ≤ N)
      linarith
    exact mul_le_mul h1 h2 (by positivity) (by positivity)

theorem rfac_one (n : ℕ) : rfac 1 (n + 1) = rfac 2 n := by
  rw [rfac_succ']
  norm_num

/-! ### Product closure -/

section Closure

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem prod_map_nonneg' {w : ι → ℝ} (hw : ∀ s, 0 ≤ w s) (l : List ι) :
    0 ≤ (l.map w).prod :=
  List.prod_nonneg fun a ha => by
    obtain ⟨b, -, rfl⟩ := List.mem_map.1 ha
    exact hw b

/-- Rising-factorial bounds are closed under products (lists of length `≤ |l|`). -/
theorem rfBound_mul {x₀ w : ι → ℝ} :
    ∀ (l : List ι) {f g : (ι → ℝ) → ℝ} {A B a b : ℝ}, 0 ≤ a → 0 ≤ b →
      ContDiff ℝ ∞ f → ContDiff ℝ ∞ g →
      (∀ l' : List ι, l'.length ≤ l.length →
        |pderivList l' f x₀| ≤ A * rfac a l'.length * (l'.map w).prod) →
      (∀ l' : List ι, l'.length ≤ l.length →
        |pderivList l' g x₀| ≤ B * rfac b l'.length * (l'.map w).prod) →
      |pderivList l (f * g) x₀| ≤ A * B * rfac (a + b) l.length * (l.map w).prod
  | [], f, g, A, B, a, b, _, _, _, _, hf, hg => by
    have h1 := hf [] le_rfl
    have h2 := hg [] le_rfl
    simp only [pderivList_nil, List.length_nil, rfac_zero, mul_one, List.map_nil,
      List.prod_nil] at h1 h2
    simp only [pderivList_nil, Pi.mul_apply, abs_mul, List.length_nil, rfac_zero, mul_one,
      List.map_nil, List.prod_nil]
    exact mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1)
  | i :: l, f, g, A, B, a, b, ha, hb, hfc, hgc, hf, hg => by
    have hf' : ∀ l' : List ι, l'.length ≤ l.length → |pderivList l' (pderiv i f) x₀| ≤
        (A * a * w i) * rfac (a + 1) l'.length * (l'.map w).prod := fun l' hl' => by
      have h := hf (i :: l') (by simp; omega)
      simp only [pderivList_cons, List.length_cons, List.map_cons, List.prod_cons,
        rfac_succ'] at h
      exact h.trans_eq (by ring)
    have hg' : ∀ l' : List ι, l'.length ≤ l.length → |pderivList l' (pderiv i g) x₀| ≤
        (B * b * w i) * rfac (b + 1) l'.length * (l'.map w).prod := fun l' hl' => by
      have h := hg (i :: l') (by simp; omega)
      simp only [pderivList_cons, List.length_cons, List.map_cons, List.prod_cons,
        rfac_succ'] at h
      exact h.trans_eq (by ring)
    have hfr : ∀ l' : List ι, l'.length ≤ l.length →
        |pderivList l' f x₀| ≤ A * rfac a l'.length * (l'.map w).prod :=
      fun l' hl' => hf l' (by simp; omega)
    have hgr : ∀ l' : List ι, l'.length ≤ l.length →
        |pderivList l' g x₀| ≤ B * rfac b l'.length * (l'.map w).prod :=
      fun l' hl' => hg l' (by simp; omega)
    have h1 := rfBound_mul l (by linarith) hb (contDiff_pderiv_top hfc i) hgc hf' hgr
    have h2 := rfBound_mul l ha (by linarith) hfc (contDiff_pderiv_top hgc i) hfr hg'
    rw [pderivList_cons, pderiv_mul (differentiable_of_top hfc) (differentiable_of_top hgc),
      pderivList_add l (f := pderiv i f * g) (g := f * pderiv i g)
        ((contDiff_pderiv_top hfc i).mul hgc) (hfc.mul (contDiff_pderiv_top hgc i)), Pi.add_apply]
    simp only [List.length_cons, List.map_cons, List.prod_cons, rfac_succ']
    calc _ ≤ _ := abs_add_le _ _
      _ ≤ _ := add_le_add h1 h2
      _ = _ := by rw [show a + 1 + b = a + b + 1 by ring, show a + (b + 1) = a + b + 1 by ring]; ring

/-- `K^n` bounds for lists of length `≤ |l|` are closed under products, `K ↦ K₁ + K₂`. -/
theorem majBound_mul_len {x₀ w : ι → ℝ} {K₁ K₂ : ℝ} :
    ∀ (l : List ι) {f g : (ι → ℝ) → ℝ} {M₁ M₂ : ℝ}, ContDiff ℝ ∞ f → ContDiff ℝ ∞ g →
      (∀ l' : List ι, l'.length ≤ l.length →
        |pderivList l' f x₀| ≤ M₁ * K₁ ^ l'.length * (l'.map w).prod) →
      (∀ l' : List ι, l'.length ≤ l.length →
        |pderivList l' g x₀| ≤ M₂ * K₂ ^ l'.length * (l'.map w).prod) →
      |pderivList l (f * g) x₀| ≤ M₁ * M₂ * (K₁ + K₂) ^ l.length * (l.map w).prod
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
        (M₁ * K₁ * w i) * K₁ ^ l'.length * (l'.map w).prod := fun l' hl' => by
      have h := hf (i :: l') (by simp; omega)
      simp only [pderivList_cons, List.length_cons, List.map_cons, List.prod_cons,
        pow_succ] at h
      exact h.trans_eq (by ring)
    have hg' : ∀ l' : List ι, l'.length ≤ l.length → |pderivList l' (pderiv i g) x₀| ≤
        (M₂ * K₂ * w i) * K₂ ^ l'.length * (l'.map w).prod := fun l' hl' => by
      have h := hg (i :: l') (by simp; omega)
      simp only [pderivList_cons, List.length_cons, List.map_cons, List.prod_cons,
        pow_succ] at h
      exact h.trans_eq (by ring)
    have hfr : ∀ l' : List ι, l'.length ≤ l.length →
        |pderivList l' f x₀| ≤ M₁ * K₁ ^ l'.length * (l'.map w).prod :=
      fun l' hl' => hf l' (by simp; omega)
    have hgr : ∀ l' : List ι, l'.length ≤ l.length →
        |pderivList l' g x₀| ≤ M₂ * K₂ ^ l'.length * (l'.map w).prod :=
      fun l' hl' => hg l' (by simp; omega)
    have h1 := majBound_mul_len l (contDiff_pderiv_top hfc i) hgc hf' hgr
    have h2 := majBound_mul_len l hfc (contDiff_pderiv_top hgc i) hfr hg'
    rw [pderivList_cons, pderiv_mul (differentiable_of_top hfc) (differentiable_of_top hgc),
      pderivList_add l (f := pderiv i f * g) (g := f * pderiv i g)
        ((contDiff_pderiv_top hfc i).mul hgc) (hfc.mul (contDiff_pderiv_top hgc i)), Pi.add_apply]
    simp only [List.length_cons, List.map_cons, List.prod_cons, pow_succ]
    calc _ ≤ _ := abs_add_le _ _
      _ ≤ _ := add_le_add h1 h2
      _ = _ := by ring

/-! ### The three-term Leibniz bound for a quadratic factor -/

/-- First-derivative sum `Σ_p |∂_{l_p} q(x₀)|` of `q = quadFn c ℓ Q` over the positions of `l`. -/
noncomputable def qd1 (ℓ : ι → ℝ) (Q : Matrix ι ι ℝ) (x₀ : ι → ℝ) (l : List ι) : ℝ :=
  (l.map fun s => |ℓ s + ((Q + Qᵀ) *ᵥ x₀) s|).sum

/-- Second-derivative sum `Σ_{p < p'} |∂_{l_p}∂_{l_{p'}} q|` over unordered pairs of positions. -/
noncomputable def qd2 (Q : Matrix ι ι ℝ) : List ι → ℝ
  | [] => 0
  | i :: l => (l.map fun s => |(Q + Qᵀ) s i|).sum + qd2 Q l

theorem qd1_nonneg (ℓ : ι → ℝ) (Q : Matrix ι ι ℝ) (x₀ : ι → ℝ) (l : List ι) :
    0 ≤ qd1 ℓ Q x₀ l :=
  List.sum_nonneg fun a ha => by
    obtain ⟨b, -, rfl⟩ := List.mem_map.1 ha
    exact abs_nonneg _

theorem qd2_nonneg (Q : Matrix ι ι ℝ) : ∀ l : List ι, 0 ≤ qd2 Q l
  | [] => le_rfl
  | i :: l => by
    rw [qd2]
    refine add_nonneg (List.sum_nonneg fun a ha => ?_) (qd2_nonneg Q l)
    obtain ⟨b, -, rfl⟩ := List.mem_map.1 ha
    exact abs_nonneg _

theorem qd2_zero : ∀ l : List ι, qd2 (0 : Matrix ι ι ℝ) l = 0
  | [] => rfl
  | i :: l => by
    rw [qd2, qd2_zero l]
    simp

/-- **Three-term Leibniz bound.** If `|∂^{l'} f(x₀)| ≤ M κ^{|l'|}` for `|l'| ≤ |l|` (`κ ≥ 0`), then
for `q = quadFn c ℓ Q`:
`κ² |∂^l(f q)(x₀)| ≤ M (κ^{n+2} |q(x₀)| + κ^{n+1} qd1(l) + κ^n qd2(l))`, `n = |l|`. -/
theorem quad_leibniz {x₀ : ι → ℝ} {κ : ℝ} (hκ : 0 ≤ κ) :
    ∀ (l : List ι) {f : (ι → ℝ) → ℝ} {M : ℝ} {c : ℝ} {ℓ : ι → ℝ} {Q : Matrix ι ι ℝ},
      ContDiff ℝ ∞ f →
      (∀ l' : List ι, l'.length ≤ l.length → |pderivList l' f x₀| ≤ M * κ ^ l'.length) →
      κ ^ 2 * |pderivList l (f * quadFn c ℓ Q) x₀| ≤
        M * (κ ^ (l.length + 2) * |quadFn c ℓ Q x₀| + κ ^ (l.length + 1) * qd1 ℓ Q x₀ l +
          κ ^ l.length * qd2 Q l)
  | [], f, M, c, ℓ, Q, _, hf => by
    have h1 := hf [] le_rfl
    simp only [pderivList_nil, List.length_nil, pow_zero, mul_one] at h1
    simp only [pderivList_nil, Pi.mul_apply, abs_mul, List.length_nil, zero_add, qd1, qd2,
      List.map_nil, List.sum_nil, mul_zero, add_zero, pow_zero, mul_one]
    have hq := abs_nonneg (quadFn c ℓ Q x₀)
    nlinarith [mul_le_mul_of_nonneg_right h1 hq, sq_nonneg κ]
  | i :: l, f, M, c, ℓ, Q, hfc, hf => by
    have hf' : ∀ l' : List ι, l'.length ≤ l.length → |pderivList l' (pderiv i f) x₀| ≤
        (M * κ) * κ ^ l'.length := fun l' hl' => by
      have h := hf (i :: l') (by simp; omega)
      simp only [pderivList_cons, List.length_cons, pow_succ] at h
      exact h.trans_eq (by ring)
    have hfr : ∀ l' : List ι, l'.length ≤ l.length → |pderivList l' f x₀| ≤ M * κ ^ l'.length :=
      fun l' hl' => hf l' (by simp; omega)
    have hqc := contDiff_quadFn c ℓ Q (n := ∞)
    -- the derivative of the quadratic is affine
    have hdq : pderiv i (quadFn c ℓ Q) =
        quadFn (ℓ i) (fun s => (Q + Qᵀ) i s) 0 := by
      rw [pderiv_quadFn]
      funext x
      simp only [quadFn, qForm, zero_mulVec, dotProduct_zero, add_zero]
      rfl
    have h1 := quad_leibniz hκ l (contDiff_pderiv_top hfc i) (c := c) (ℓ := ℓ) (Q := Q) hf'
    have h2 := quad_leibniz hκ l hfc (c := ℓ i) (ℓ := fun s => (Q + Qᵀ) i s) (Q := 0) hfr
    rw [pderivList_cons, pderiv_mul (differentiable_of_top hfc) (differentiable_of_top hqc),
      hdq, pderivList_add l (f := pderiv i f * quadFn c ℓ Q)
        (g := f * quadFn (ℓ i) (fun s => (Q + Qᵀ) i s) 0)
        ((contDiff_pderiv_top hfc i).mul hqc) (hfc.mul (contDiff_quadFn _ _ _)), Pi.add_apply]
    -- evaluate the affine factor and its derivatives
    have hv : quadFn (ℓ i) (fun s => (Q + Qᵀ) i s) 0 x₀ = ℓ i + ((Q + Qᵀ) *ᵥ x₀) i := by
      simp only [quadFn, qForm, zero_mulVec, dotProduct_zero, add_zero]
      rfl
    have hd1 : qd1 (fun s => (Q + Qᵀ) i s) (0 : Matrix ι ι ℝ) x₀ l =
        (l.map fun s => |(Q + Qᵀ) s i|).sum := by
      unfold qd1
      congr 1
      refine List.map_congr_left fun s _ => ?_
      simp only [zero_add, transpose_zero, zero_mulVec, Pi.zero_apply, add_zero]
      congr 1
      simp only [Matrix.add_apply, Matrix.transpose_apply]
      ring
    have hd2 : qd2 (0 : Matrix ι ι ℝ) l = 0 := qd2_zero l
    rw [hv, hd1, hd2] at h2
    have hsplit : qd1 ℓ Q x₀ (i :: l) = |ℓ i + ((Q + Qᵀ) *ᵥ x₀) i| + qd1 ℓ Q x₀ l := by
      simp [qd1]
    have hsplit2 : qd2 Q (i :: l) = (l.map fun s => |(Q + Qᵀ) s i|).sum + qd2 Q l := rfl
    simp only [List.length_cons]
    rw [hsplit, hsplit2]
    have habs := abs_add_le (pderivList l (pderiv i f * quadFn c ℓ Q) x₀)
      (pderivList l (f * quadFn (ℓ i) (fun s => (Q + Qᵀ) i s) 0) x₀)
    calc κ ^ 2 * |pderivList l (pderiv i f * quadFn c ℓ Q) x₀ +
          pderivList l (f * quadFn (ℓ i) (fun s => (Q + Qᵀ) i s) 0) x₀|
        ≤ κ ^ 2 * |pderivList l (pderiv i f * quadFn c ℓ Q) x₀| +
            κ ^ 2 * |pderivList l (f * quadFn (ℓ i) (fun s => (Q + Qᵀ) i s) 0) x₀| := by
          rw [← mul_add]
          exact mul_le_mul_of_nonneg_left habs (sq_nonneg κ)
      _ ≤ M * κ * (κ ^ (l.length + 2) * |quadFn c ℓ Q x₀| +
            κ ^ (l.length + 1) * qd1 ℓ Q x₀ l + κ ^ l.length * qd2 Q l) +
          M * (κ ^ (l.length + 2) * |ℓ i + ((Q + Qᵀ) *ᵥ x₀) i| +
            κ ^ (l.length + 1) * (l.map fun s => |(Q + Qᵀ) s i|).sum + κ ^ l.length * 0) :=
          add_le_add h1 h2
      _ = _ := by ring

end Closure

/-! ### Entries of the inverse of an affine matrix family -/

section Inverse

variable {ι V : Type*} [Fintype ι] [DecidableEq ι] [Fintype V] [DecidableEq V]

theorem pderiv_cmul (i : ι) (c : ℝ) (f : (ι → ℝ) → ℝ) :
    pderiv i (fun x => c * f x) = fun x => c * pderiv i f x := by
  funext x
  have e : (fun x => c * f x) = c • f := by
    funext y
    simp [smul_eq_mul]
  simp only [pderiv, e, fderiv_const_smul_field, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rfl

theorem pderivList_cmul (l : List ι) (c : ℝ) (f : (ι → ℝ) → ℝ) :
    pderivList l (fun x => c * f x) = fun x => c * pderivList l f x := by
  induction l generalizing f with
  | nil => rfl
  | cons i l ih => simp only [pderivList_cons, pderiv_cmul, ih]

theorem pderiv_finset_sum {α : Type*} (t : Finset α) (f : α → (ι → ℝ) → ℝ)
    (hf : ∀ a ∈ t, Differentiable ℝ (f a)) (s : ι) :
    pderiv s (fun x => ∑ a ∈ t, f a x) = fun x => ∑ a ∈ t, pderiv s (f a) x := by
  funext x
  simp only [pderiv]
  rw [fderiv_fun_sum fun a ha => (hf a ha) x]
  simp

/-- A global smooth version of `(M x)⁻¹_{uw}`, equal to it where `det M x ≥ δ/2`. -/
noncomputable def invSm (M : (ι → ℝ) → Matrix V V ℝ) (δ : ℝ) (u w : V) (x : ι → ℝ) : ℝ :=
  (M x).adjugate u w / psiW δ (M x).det

theorem contDiff_invSm {M : (ι → ℝ) → Matrix V V ℝ} (hMc : ∀ u w, ContDiff ℝ ∞ fun x => M x u w)
    {δ : ℝ} (hδ : 0 < δ) (u w : V) : ContDiff ℝ ∞ (invSm M δ u w) :=
  (contDiff_adjugate_apply_of_entries hMc u w).div
    ((contDiff_psiW δ).comp (contDiff_det_of_entries hMc)) fun x => (psiW_pos hδ _).ne'

theorem invSm_eq {M : (ι → ℝ) → Matrix V V ℝ} {δ : ℝ} (hδ : 0 < δ) {x : ι → ℝ}
    (hx : δ / 2 ≤ (M x).det) (u w : V) : invSm M δ u w x = (M x)⁻¹ u w := by
  have hpos : 0 < (M x).det := lt_of_lt_of_le (by linarith) hx
  rw [invSm, psiW_eq hδ hx, inv_apply_eq_adjugate_div hpos.ne']

/-- **Derivative of the inverse** of an affine family whose derivative in `x_s` is
`c_s (e_i e_{φ s}ᵀ + e_{φ s} e_iᵀ)`: near a point with `det M > δ/2`,
`∂_s (M⁻¹)_{uw} = -c_s ((M⁻¹)_{ui} (M⁻¹)_{φ s, w} + (M⁻¹)_{u, φ s} (M⁻¹)_{iw})`. -/
theorem pderiv_invSm_eventually {M : (ι → ℝ) → Matrix V V ℝ}
    (hMc : ∀ u w, ContDiff ℝ ∞ fun x => M x u w) {i : V} {φ : ι → V} {c : ι → ℝ}
    (hE : ∀ s u w, pderiv s (fun x => M x u w) = fun _ =>
      c s * ((if u = i ∧ w = φ s then 1 else 0) + (if u = φ s ∧ w = i then 1 else 0)))
    {δ : ℝ} (hδ : 0 < δ) {x₀ : ι → ℝ} (hx₀ : δ / 2 < (M x₀).det) (s : ι) (u w : V) :
    pderiv s (invSm M δ u w) =ᶠ[𝓝 x₀] fun x =>
      -(c s * (invSm M δ u i x * invSm M δ (φ s) w x +
        invSm M δ u (φ s) x * invSm M δ i w x)) := by
  have hcont : Continuous fun x => (M x).det := (contDiff_det_of_entries hMc).continuous
  have hU : ∀ᶠ x in 𝓝 x₀, δ / 2 < (M x).det :=
    (isOpen_lt continuous_const hcont).mem_nhds hx₀
  refine hU.mono fun x hx => ?_
  show pderiv s (invSm M δ u w) x = -(c s * (invSm M δ u i x * invSm M δ (φ s) w x +
    invSm M δ u (φ s) x * invSm M δ i w x))
  have hxU : ∀ᶠ y in 𝓝 x, δ / 2 < (M y).det := (isOpen_lt continuous_const hcont).mem_nhds hx
  have hdet : (M x).det ≠ 0 := (lt_of_lt_of_le (by linarith) hx.le).ne'
  have hdiff : ∀ a b, Differentiable ℝ (invSm M δ a b) := fun a b =>
    differentiable_of_top (contDiff_invSm hMc hδ a b)
  have hMd : ∀ a b, Differentiable ℝ fun y => M y a b := fun a b => differentiable_of_top (hMc a b)
  set X := (M x)⁻¹ with hXdef
  have hXt : ∀ a b, invSm M δ a b x = X a b := fun a b => invSm_eq hδ hx.le a b
  set Dm : Matrix V V ℝ := Matrix.of fun a b => pderiv s (invSm M δ a b) x with hDm
  -- differentiate `Σ_a M_{ua} (M⁻¹)_{ab} = δ_{ub}`
  have hrow : ∀ a b, ∑ k, M x a k * Dm k b = -∑ k, (c s * ((if a = i ∧ k = φ s then 1 else 0) +
      (if a = φ s ∧ k = i then 1 else 0))) * X k b := by
    intro a b
    have hev : (fun y => ∑ k, M y a k * invSm M δ k b y) =ᶠ[𝓝 x]
        fun _ => (1 : Matrix V V ℝ) a b := hxU.mono fun y hy => by
      have hy0 : (M y).det ≠ 0 := (lt_of_lt_of_le (by linarith) hy.le).ne'
      simp only [invSm_eq hδ hy.le]
      rw [← Matrix.mul_apply, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hy0)]
    have h0 : pderiv s (fun y => ∑ k, M y a k * invSm M δ k b y) x = 0 := by
      simp only [pderiv]
      rw [Filter.EventuallyEq.fderiv_eq hev]
      simp
    rw [pderiv_finset_sum Finset.univ (fun k y => M y a k * invSm M δ k b y)
      (fun k _ => (hMd a k).mul (hdiff k b))] at h0
    have hprod : ∀ k, pderiv s (fun y => M y a k * invSm M δ k b y) x =
        (c s * ((if a = i ∧ k = φ s then 1 else 0) + (if a = φ s ∧ k = i then 1 else 0))) *
          X k b + M x a k * Dm k b := by
      intro k
      have := congrFun (pderiv_mul (hMd a k) (hdiff k b) s) x
      simp only [Pi.mul_apply, Pi.add_apply, hE s a k, hXt k b] at this
      exact this
    simp only [hprod, Finset.sum_add_distrib] at h0
    linarith
  have hMD : M x * Dm = -(Matrix.of (fun a k => c s * ((if a = i ∧ k = φ s then 1 else 0) +
      (if a = φ s ∧ k = i then 1 else 0))) * X) := by
    ext a b
    simp only [Matrix.mul_apply, Matrix.neg_apply, Matrix.of_apply]
    exact hrow a b
  have hD : Dm = -(X * (Matrix.of (fun a k => c s * ((if a = i ∧ k = φ s then 1 else 0) +
      (if a = φ s ∧ k = i then 1 else 0))) * X)) := by
    calc Dm = X * (M x * Dm) := by
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdet),
            Matrix.one_mul]
      _ = _ := by rw [hMD, Matrix.mul_neg]
  have hentry := congrFun (congrFun hD u) w
  simp only [hDm, Matrix.of_apply] at hentry
  rw [hentry, hXt, hXt, hXt, hXt]
  simp only [Matrix.neg_apply, Matrix.mul_apply, Matrix.of_apply, mul_add, add_mul,
    Finset.sum_add_distrib, mul_ite, ite_mul, mul_one, mul_zero, zero_mul, ite_and,
    Finset.mul_sum, Finset.sum_mul]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]
  ring

/-- Entries of a positive semidefinite matrix: `|X_uw| ≤ √X_uu √X_ww`. -/
theorem psd_entry_abs_le {X : Matrix V V ℝ} (hX : X.PosSemidef) (u w : V) :
    |X u w| ≤ Real.sqrt (X u u) * Real.sqrt (X w w) := by
  have h2 := (hX.submatrix ![u, w]).det_nonneg
  rw [Matrix.det_fin_two] at h2
  simp only [Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at h2
  have hsym : X w u = X u w := by simpa using hX.isHermitian.apply u w
  rw [hsym] at h2
  rw [← Real.sqrt_mul hX.diag_nonneg (X w w)]
  exact Real.abs_le_sqrt (by nlinarith)

/-- **Derivative bounds for the inverse entries.** At a point with `M ≻ 0` and `det M > δ/2`,
with `X = M(x₀)⁻¹` and `r_k = √X_kk`:
`|∂^l (M⁻¹)_{uw}(x₀)| ≤ r_u r_w |l|! Π_{s ∈ l} 2|c_s| r_i r_{φ s}`. -/
theorem invSm_deriv_le {M : (ι → ℝ) → Matrix V V ℝ}
    (hMc : ∀ u w, ContDiff ℝ ∞ fun x => M x u w) {i : V} {φ : ι → V} {c : ι → ℝ}
    (hE : ∀ s u w, pderiv s (fun x => M x u w) = fun _ =>
      c s * ((if u = i ∧ w = φ s then 1 else 0) + (if u = φ s ∧ w = i then 1 else 0)))
    {δ : ℝ} (hδ : 0 < δ) {x₀ : ι → ℝ} (hx₀ : δ / 2 < (M x₀).det) (hP : (M x₀).PosDef) :
    ∀ (n : ℕ) (l : List ι), l.length ≤ n → ∀ u w,
      |pderivList l (invSm M δ u w) x₀| ≤
        Real.sqrt ((M x₀)⁻¹ u u) * Real.sqrt ((M x₀)⁻¹ w w) * rfac 1 l.length *
          (l.map fun s => 2 * |c s| * (Real.sqrt ((M x₀)⁻¹ i i) *
            Real.sqrt ((M x₀)⁻¹ (φ s) (φ s)))).prod := by
  intro n
  induction n with
  | zero =>
    intro l hl u w
    rcases l with _ | ⟨s, l⟩
    · simp only [pderivList_nil, List.length_nil, rfac_zero, mul_one, List.map_nil,
        List.prod_nil]
      rw [invSm_eq hδ hx₀.le]
      exact psd_entry_abs_le hP.inv.posSemidef u w
    · simp at hl
  | succ n ih =>
    intro l hl u w
    rcases l with _ | ⟨s, l⟩
    · exact ih [] (Nat.zero_le _) u w
    · have hl' : l.length ≤ n := by simp at hl; omega
      have hev := pderiv_invSm_eventually hMc hE hδ hx₀ s u w
      rw [pderivList_cons, (pderivList_congr_nhds hev l).eq_of_nhds]
      have hc : ∀ a b, ContDiff ℝ ∞ (invSm M δ a b) := contDiff_invSm hMc hδ
      have e : (fun x => -(c s * (invSm M δ u i x * invSm M δ (φ s) w x +
          invSm M δ u (φ s) x * invSm M δ i w x))) = fun x => (-c s) *
            ((invSm M δ u i * invSm M δ (φ s) w + invSm M δ u (φ s) * invSm M δ i w) x) := by
        funext x
        simp only [Pi.add_apply, Pi.mul_apply]
        ring
      rw [e, pderivList_cmul, pderivList_add l (f := invSm M δ u i * invSm M δ (φ s) w)
        (g := invSm M δ u (φ s) * invSm M δ i w) ((hc u i).mul (hc (φ s) w))
        ((hc u (φ s)).mul (hc i w))]
      beta_reduce
      rw [Pi.add_apply]
      have h1 := rfBound_mul l zero_le_one zero_le_one (hc u i) (hc (φ s) w)
        (fun l'' hl'' => ih l'' (le_trans hl'' hl') u i)
        (fun l'' hl'' => ih l'' (le_trans hl'' hl') (φ s) w)
      have h2 := rfBound_mul l zero_le_one zero_le_one (hc u (φ s)) (hc i w)
        (fun l'' hl'' => ih l'' (le_trans hl'' hl') u (φ s))
        (fun l'' hl'' => ih l'' (le_trans hl'' hl') i w)
      rw [show (1 : ℝ) + 1 = 2 by norm_num] at h1 h2
      simp only [List.length_cons, List.map_cons, List.prod_cons, rfac_one]
      rw [abs_mul, abs_neg]
      calc |c s| * |pderivList l (invSm M δ u i * invSm M δ (φ s) w) x₀ +
            pderivList l (invSm M δ u (φ s) * invSm M δ i w) x₀|
          ≤ |c s| * (|pderivList l (invSm M δ u i * invSm M δ (φ s) w) x₀| +
            |pderivList l (invSm M δ u (φ s) * invSm M δ i w) x₀|) :=
            mul_le_mul_of_nonneg_left (abs_add_le _ _) (abs_nonneg _)
        _ ≤ |c s| * (_ + _) := mul_le_mul_of_nonneg_left (add_le_add h1 h2) (abs_nonneg _)
        _ = _ := by ring

end Inverse

/-! ### Products over a list of factors -/

section ListProd

variable {ι α : Type*} [Fintype ι] [DecidableEq ι]

theorem pderivList_const_eq (c : ℝ) : ∀ l : List ι, l ≠ [] →
    pderivList l (fun _ : ι → ℝ => c) = fun _ => 0
  | [], h => (h rfl).elim
  | i :: l, _ => by
    rw [pderivList_cons]
    have h : pderiv i (fun _ : ι → ℝ => c) = fun _ => 0 := by
      funext x
      simp [pderiv]
    rw [h]
    clear h
    induction l with
    | nil => rfl
    | cons j l ih =>
      rw [pderivList_cons]
      have h : pderiv j (fun _ : ι → ℝ => (0 : ℝ)) = fun _ => 0 := by
        funext x
        simp [pderiv]
      rw [h, ih (List.cons_ne_nil _ _)]

theorem rfac_zero_succ (n : ℕ) : rfac 0 (n + 1) = 0 := by
  rw [rfac_succ']
  simp

/-- Rising-factorial bounds for a product over a list of factors, each with `rfac 1`. -/
theorem rfBound_listProd {x₀ w : ι → ℝ} (hw : ∀ s, 0 ≤ w s) {N : ℕ} (F : α → (ι → ℝ) → ℝ)
    (A : α → ℝ) :
    ∀ L : List α, (∀ t ∈ L, ContDiff ℝ ∞ (F t)) →
      (∀ t ∈ L, ∀ l' : List ι, l'.length ≤ N →
        |pderivList l' (F t) x₀| ≤ A t * rfac 1 l'.length * (l'.map w).prod) →
      ∀ l : List ι, l.length ≤ N →
        |pderivList l (fun x => (L.map fun t => F t x).prod) x₀| ≤
          (L.map A).prod * rfac L.length l.length * (l.map w).prod
  | [], _, _, l, _ => by
    rcases l with _ | ⟨s, l⟩
    · simp
    · simp only [List.map_nil, List.prod_nil, List.length_nil, Nat.cast_zero, List.length_cons,
        rfac_zero_succ, mul_zero, zero_mul]
      rw [pderivList_const_eq 1 (s :: l) (List.cons_ne_nil s l)]
      simp
  | t :: L, hc, hb, l, hl => by
    have hcL : ∀ t' ∈ L, ContDiff ℝ ∞ (F t') := fun t' ht' => hc t' (List.mem_cons_of_mem _ ht')
    have hbL : ∀ t' ∈ L, ∀ l' : List ι, l'.length ≤ N →
        |pderivList l' (F t') x₀| ≤ A t' * rfac 1 l'.length * (l'.map w).prod :=
      fun t' ht' => hb t' (List.mem_cons_of_mem _ ht')
    have hP : ContDiff ℝ ∞ fun x => (L.map fun t => F t x).prod := by
      clear hb hbL hl l
      induction L with
      | nil => simpa using contDiff_const
      | cons t' L ih =>
        simp only [List.map_cons, List.prod_cons]
        exact (hcL t' List.mem_cons_self).mul (ih (fun t'' ht'' => hc t'' (by
          rcases List.mem_cons.1 ht'' with h | h
          · exact h ▸ List.mem_cons_self
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)))
          fun t'' ht'' => hcL t'' (List.mem_cons_of_mem _ ht''))
    have e : (fun x => ((t :: L).map fun t => F t x).prod) =
        F t * fun x => (L.map fun t => F t x).prod := by
      funext x
      simp
    rw [e]
    have h := rfBound_mul l zero_le_one (Nat.cast_nonneg L.length) (hc t List.mem_cons_self) hP
      (fun l' hl' => hb t List.mem_cons_self l' (le_trans hl' hl))
      (fun l' hl' => rfBound_listProd hw F A L hcL hbL l' (le_trans hl' hl))
    simp only [List.map_cons, List.prod_cons, List.length_cons, Nat.cast_succ]
    rw [show (L.length : ℝ) + 1 = 1 + L.length by ring]
    exact h.trans_eq (by ring)

end ListProd

end BiluLinial.Tight.SecB
