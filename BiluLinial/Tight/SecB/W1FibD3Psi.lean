/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecB.W1FibD3Ent

/-!
# TB.W1fib-d3: the jet of `Ψ` along a regular fibre

Let `τ₀` be a good endpoint (`W(τ₀) > 0`, `64 p a g*(τ₀) ≤ 1`) and `P̃^±(t) = P̃^±(τ₀) + (t - t₀)
(±a)√(y_iy_j) E` on `|t - t₀| ≤ 3`. With `D = D_*(τ₀)`, `Q = 2661121 D³` and `l = aD`,
`d3_psi_jet`: `Ψ(t) = obsPsi(P̃⁺(t), P̃⁻(t))` has a 3-jet with `|Ψ^{(r)}| ≤ 4718592 Q⁸/(√d h) · l^r`
in all four configurations.

Ingredients: the Woodbury entry jets (`jb_entry_bounds`) of `G^± = physInv y^± P̃^±(t)` and
`X_± = physInv y^± (P̃^±(t) + hY^±)`; `a(|M_ii| + |M_jj| + |M_ij|) ≤ 1/32` for the four `{i,j}`
blocks (`d3_small`); `|M| ≤ D` on the ball and the row energies `Σ_x X_{ax}² ≤ D/h` at `τ₀`;
`jb_maskF` with `sum_maj_le` (`d3_maskF_jet`); the masks `u` and `b_±` (`d3_mask_jet`:
`|b^{(r)}| ≤ 8Q²/√d · l^r`, from `a²d ≤ 1`, `|N| ≤ d`).
-/

@[expose] public section

namespace BiluLinial.Tight.SecB

open Matrix

universe u

theorem abs_le_half_add {x A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (h : x ^ 2 ≤ A * B) :
    |x| ≤ (A + B) / 2 := by
  have h2 : x ^ 2 ≤ ((A + B) / 2) ^ 2 := by nlinarith [sq_nonneg (A - B)]
  rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_sq (show 0 ≤ (A + B) / 2 by positivity)]
  exact Real.sqrt_le_sqrt h2

/-! ### Generic: the masked entry `F_ji` -/

section Gen

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem d3_maskF_jet {U : Set ℝ} {Xe Xn : ℝ → Matrix n n ℝ} {f : ℝ → n → ℝ} {l c Q R Af h : ℝ}
    (hl : 0 ≤ l) {Me Mn : Matrix n n ℝ} (j i : n) {FAj FAi FB Ff : n → ℕ → ℝ → ℝ}
    {Fii Fji : ℕ → ℝ → ℝ}
    (hej : ∀ x, JB U (fun t => Xe t j x) (FAj x) (|Me j x| + c * (|Me i x| + |Me j x|)) l)
    (hei : ∀ x, JB U (fun t => Xe t i x) (FAi x) (|Me i x| + c * (|Me i x| + |Me j x|)) l)
    (hn : ∀ x, JB U (fun t => Xn t x i) (FB x) (|Mn x i| + c * (|Mn x i| + |Mn x j|)) l)
    (hf : ∀ x, JB U (fun t => f t x) (Ff x) Af l)
    (hii : JB U (fun t => Xe t i i) Fii Q l) (hji : JB U (fun t => Xe t j i) Fji Q l)
    (rei : ∑ x, Me i x ^ 2 ≤ R) (rej : ∑ x, Me j x ^ 2 ≤ R) (rni : ∑ x, Mn x i ^ 2 ≤ R)
    (rnj : ∑ x, Mn x j ^ 2 ≤ R) (hc : 0 ≤ c) (hcQ : 1 + c ≤ 2 * Q) (hh : 0 < h)
    (hRQ : R ≤ Q / h) (hQ : 0 ≤ Q) (hAf : 0 ≤ Af) :
    ∃ F, JB U (fun t => maskF (Xe t) (Xn t) (f t) j i) F (36864 * Af * Q ^ 4 / h) l := by
  have nn : ∀ (M : Matrix n n ℝ) a b x, 0 ≤ |M a x| + c * (|M b x| + |M a x|) := fun M a b x => by
    positivity
  obtain ⟨F, hF⟩ := jb_maskF hl j i hej hei hn hf hii hji (fun x => by positivity)
    (fun x => by positivity) (fun x => by positivity) hAf hQ hQ
  refine ⟨F, hF.mono ?_ hl⟩
  have s1 := sum_maj_le Finset.univ (fun x => Me j x) (fun x => Me i x) (fun x => Me j x)
    (fun x => Mn x i) (fun x => Mn x i) (fun x => Mn x j) hc rej rei rej rni rni rnj
  have s2 := sum_maj_le Finset.univ (fun x => Me i x) (fun x => Me i x) (fun x => Me j x)
    (fun x => Mn x i) (fun x => Mn x i) (fun x => Mn x j) hc rei rei rej rni rni rnj
  have e1 : ∑ x, (|Me j x| + c * (|Me i x| + |Me j x|)) * (|Mn x i| + c * (|Mn x i| + |Mn x j|)) ≤
      9 * (1 + c) ^ 2 * R := by
    refine le_trans (le_of_eq ?_) s1
    refine Finset.sum_congr rfl fun x _ => ?_
    ring
  have hR0 : 0 ≤ R := le_trans (Finset.sum_nonneg fun x _ => sq_nonneg (Me i x)) rei
  have hc2 : (1 + c) ^ 2 ≤ (2 * Q) ^ 2 := pow_le_pow_left₀ (by linarith) hcQ 2
  have hS : 9 * (1 + c) ^ 2 * R ≤ 36 * Q ^ 3 / h := by
    have := mul_le_mul hc2 hRQ hR0 (by positivity)
    have e : 9 * ((2 * Q) ^ 2 * (Q / h)) = 36 * Q ^ 3 / h := by ring
    nlinarith
  have hA1 : 64 * Af * ∑ x, (|Me j x| + c * (|Me i x| + |Me j x|)) *
      (|Mn x i| + c * (|Mn x i| + |Mn x j|)) ≤ 64 * Af * (36 * Q ^ 3 / h) :=
    mul_le_mul_of_nonneg_left (e1.trans hS) (by positivity)
  have hA2 : 64 * Af * ∑ x, (|Me i x| + c * (|Me i x| + |Me j x|)) *
      (|Mn x i| + c * (|Mn x i| + |Mn x j|)) ≤ 64 * Af * (36 * Q ^ 3 / h) :=
    mul_le_mul_of_nonneg_left (s2.trans hS) (by positivity)
  have t1 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hA1 hQ) (by norm_num : (0:ℝ) ≤ 8)
  have t2 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hA2 hQ) (by norm_num : (0:ℝ) ≤ 8)
  have e : 8 * (Q * (64 * Af * (36 * Q ^ 3 / h))) + 8 * (Q * (64 * Af * (36 * Q ^ 3 / h))) =
      36864 * Af * Q ^ 4 / h := by ring
  linarith

end Gen

/-! ### Contact-level facts at a good endpoint -/

section Psi

variable {d p : ℕ} (ct : Contact.{u} d p)

theorem w1_XP_le_gp {h : ℝ} (hh : 0 < h) {σ : Config ct.V}
    (hσ : wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0) (k : ct.V) : ct.XP h σ k k ≤ ct.gp σ k k := by
  obtain ⟨hpP, -⟩ := posDef_of_wt_ne_zero ct.G hσ
  have hy : ∀ k, 0 ≤ ct.yp k := fun k => (ct.ctx.hyp k).1
  change shiftP ct.G (aOf d p) 1 h ct.yp σ ct.S k k ≤ ct.gp σ k k
  rw [shiftP_diag ct.G σ ct.S (hy k)]
  change ct.yp k * hzN ct.G (aOf d p) 1 h ct.yp σ ct.S k ≤
    greenP ct.G (aOf d p) 1 ct.yp σ ct.S k k
  rw [greenP_diag ct.G σ ct.S (hy k)]
  exact mul_le_mul_of_nonneg_left (hzN_le_hN ct.G hpP hh.le hy k) (hy k)

theorem w1_XM_le_gm {h : ℝ} (hh : 0 < h) {σ : Config ct.V}
    (hσ : wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0) (k : ct.V) : ct.XM h σ k k ≤ ct.gm σ k k := by
  obtain ⟨-, hpM⟩ := posDef_of_wt_ne_zero ct.G hσ
  have hy : ∀ k, 0 ≤ ct.ym k := fun k => (ct.ctx.hym k).1
  change shiftP ct.G (aOf d p) (-1) h ct.ym σ ct.S k k ≤ ct.gm σ k k
  rw [shiftP_diag ct.G σ ct.S (hy k)]
  change ct.ym k * hzN ct.G (aOf d p) (-1) h ct.ym σ ct.S k ≤
    greenP ct.G (aOf d p) (-1) ct.ym σ ct.S k k
  rw [greenP_diag ct.G σ ct.S (hy k)]
  exact mul_le_mul_of_nonneg_left (hzN_le_hN ct.G hpM hh.le hy k) (hy k)

/-- `a(|M_ii| + |M_jj| + |M_ij|) ≤ 1/32` for the four `{i,j}` blocks at a good endpoint. -/
theorem d3_small {h : ℝ} (hh : 0 < h) (hp : 1 ≤ p) {τ₀ : Config ct.V} {i j : ct.V}
    (hg : fibGood ct i j τ₀) :
    aOf d p * (|ct.gp τ₀ i i| + |ct.gp τ₀ j j| + |ct.gp τ₀ i j|) ≤ 1 / 32 ∧
    aOf d p * (|ct.gm τ₀ i i| + |ct.gm τ₀ j j| + |ct.gm τ₀ i j|) ≤ 1 / 32 ∧
    aOf d p * (|ct.XP h τ₀ i i| + |ct.XP h τ₀ j j| + |ct.XP h τ₀ i j|) ≤ 1 / 32 ∧
    aOf d p * (|ct.XM h τ₀ i i| + |ct.XM h τ₀ j j| + |ct.XM h τ₀ i j|) ≤ 1 / 32 := by
  obtain ⟨hw, hG⟩ := hg
  obtain ⟨hpP, hpM⟩ := posDef_of_wt_ne_zero ct.G hw
  have hyp : ∀ k, 0 ≤ ct.yp k := fun k => (ct.ctx.hyp k).1
  have hym : ∀ k, 0 ≤ ct.ym k := fun k => (ct.ctx.hym k).1
  have ha : 0 ≤ aOf d p := by unfold aOf; positivity
  obtain ⟨gi1, gi2⟩ := w1_gp_nonneg ct hw i
  obtain ⟨gj1, gj2⟩ := w1_gp_nonneg ct hw j
  have hG0 : 0 ≤ fibG ct τ₀ i j := by unfold fibG; linarith
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hag : aOf d p * fibG ct τ₀ i j ≤ 1 / 64 := by
    have h0 : 0 ≤ aOf d p * fibG ct τ₀ i j := mul_nonneg ha hG0
    have : 64 * (aOf d p * fibG ct τ₀ i j) ≤ 64 * p * aOf d p * fibG ct τ₀ i j := by nlinarith
    linarith
  unfold fibG at hag
  have opP : |ct.gp τ₀ i j| ≤ (ct.gp τ₀ i i + ct.gp τ₀ j j) / 2 :=
    abs_le_half_add gi1 gj1 (greenP_sq_le ct.G hpP hyp i j)
  have opM : |ct.gm τ₀ i j| ≤ (ct.gm τ₀ i i + ct.gm τ₀ j j) / 2 :=
    abs_le_half_add gi2 gj2 (greenP_sq_le ct.G hpM hym i j)
  obtain ⟨-, xi1⟩ := diag_nonneg_of_posDef ct.G hpP hyp hh.le i
  obtain ⟨-, xj1⟩ := diag_nonneg_of_posDef ct.G hpP hyp hh.le j
  obtain ⟨-, xi2⟩ := diag_nonneg_of_posDef ct.G hpM hym hh.le i
  obtain ⟨-, xj2⟩ := diag_nonneg_of_posDef ct.G hpM hym hh.le j
  have lpi := w1_XP_le_gp ct hh hw i
  have lpj := w1_XP_le_gp ct hh hw j
  have lmi := w1_XM_le_gm ct hh hw i
  have lmj := w1_XM_le_gm ct hh hw j
  have oxP : |ct.XP h τ₀ i j| ≤ (ct.XP h τ₀ i i + ct.XP h τ₀ j j) / 2 :=
    abs_le_half_add xi1 xj1 (shiftP_sq_le ct.G hpP hyp hh.le i j)
  have oxM : |ct.XM h τ₀ i j| ≤ (ct.XM h τ₀ i i + ct.XM h τ₀ j j) / 2 :=
    abs_le_half_add xi2 xj2 (shiftP_sq_le ct.G hpM hym hh.le i j)
  change 0 ≤ ct.XP h τ₀ i i at xi1
  change 0 ≤ ct.XP h τ₀ j j at xj1
  change 0 ≤ ct.XM h τ₀ i i at xi2
  change 0 ≤ ct.XM h τ₀ j j at xj2
  rw [abs_of_nonneg gi1, abs_of_nonneg gj1, abs_of_nonneg gi2, abs_of_nonneg gj2,
    abs_of_nonneg xi1, abs_of_nonneg xj1, abs_of_nonneg xi2, abs_of_nonneg xj2]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := mul_le_mul_of_nonneg_left opP ha; nlinarith
  · have := mul_le_mul_of_nonneg_left opM ha; nlinarith
  · have := mul_le_mul_of_nonneg_left oxP ha
    have := mul_le_mul_of_nonneg_left lpi ha
    have := mul_le_mul_of_nonneg_left lpj ha
    nlinarith
  · have := mul_le_mul_of_nonneg_left oxM ha
    have := mul_le_mul_of_nonneg_left lmi ha
    have := mul_le_mul_of_nonneg_left lmj ha
    nlinarith

theorem obsBP_apply (X : Matrix ct.V ct.V ℝ) (x : ct.V) :
    obsBP ct X x = 4 * aOf d p ^ 2 * ∑ m, ct.adjS x m * ((X m m / 2) ^ 2 * ct.uvec m) := by
  rw [obsBP, Pi.smul_apply, smul_eq_mul, funext (Matrix.mulVec_diagonal _ ct.uvec)]
  rfl

theorem obsBM_apply (X Y : Matrix ct.V ct.V ℝ) (x : ct.V) :
    obsBM ct X Y x =
      4 * aOf d p ^ 2 * ∑ m, ct.adjS x m * (X m m / 2 * (Y m m / 2) * ct.uvec m) := by
  rw [obsBM, Pi.smul_apply, smul_eq_mul, funext (Matrix.mulVec_diagonal _ ct.uvec)]
  rfl

theorem obsBP_apply_N (X : Matrix ct.V ct.V ℝ) (x : ct.V) :
    obsBP ct X x = 4 * aOf d p ^ 2 * ∑ m ∈ ct.N, ct.adjS x m * ((X m m / 2) ^ 2 * ct.uvec m) := by
  rw [obsBP_apply]
  congr 1
  refine (Finset.sum_subset (Finset.subset_univ _) fun m _ hm => ?_).symm
  rw [w1_uvec_zero ct hm, mul_zero, mul_zero]

theorem obsBM_apply_N (X Y : Matrix ct.V ct.V ℝ) (x : ct.V) :
    obsBM ct X Y x =
      4 * aOf d p ^ 2 * ∑ m ∈ ct.N, ct.adjS x m * (X m m / 2 * (Y m m / 2) * ct.uvec m) := by
  rw [obsBM_apply]
  congr 1
  refine (Finset.sum_subset (Finset.subset_univ _) fun m _ hm => ?_).symm
  rw [w1_uvec_zero ct hm, mul_zero, mul_zero]

/-- The jet of the random mask `x ↦ 4a² Σ_{m ∈ N} (A_H)_xm q_m u_m`. -/
theorem d3_mask_jet {U : Set ℝ} {q : ℝ → ct.V → ℝ} {Fq : ct.V → ℕ → ℝ → ℝ} {Aq : ct.V → ℝ}
    {Q l : ℝ} (hl : 0 ≤ l) (hd : 0 < (d : ℝ)) (had : aOf d p ^ 2 * d ≤ 1)
    (hq : ∀ m ∈ ct.N, JB U (fun t => q t m) (Fq m) (Aq m) l) (hAq0 : ∀ m ∈ ct.N, 0 ≤ Aq m)
    (hAq : ∀ m ∈ ct.N, Aq m ≤ 2 * Q ^ 2) (x : ct.V) :
    ∃ F, JB U (fun t => 4 * aOf d p ^ 2 * ∑ m ∈ ct.N, ct.adjS x m * (q t m * ct.uvec m)) F
      (8 * Q ^ 2 / Real.sqrt d) l := by
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd
  have h := (JB.sum ct.N fun m hm => (hq m hm).smul (ct.adjS x m * ct.uvec m)).smul
    (4 * aOf d p ^ 2)
  refine ⟨_, (h.congr fun t _ => ?_).mono ?_ hl⟩
  · congr 1
    exact Finset.sum_congr rfl fun m _ => by ring
  · have hpt : ∀ m ∈ ct.N, |ct.adjS x m * ct.uvec m| * Aq m ≤ 2 * Q ^ 2 / Real.sqrt d :=
      fun m hm => by
        rw [abs_mul, w1_uvec_N ct hm,
          abs_of_pos (by positivity : (0 : ℝ) < 1 / Real.sqrt d)]
        have h1 := w1_adjS_abs_le ct x m
        have h2 := hAq m hm
        have h3 := hAq0 m hm
        calc |ct.adjS x m| * (1 / Real.sqrt d) * Aq m ≤ 1 * (1 / Real.sqrt d) * (2 * Q ^ 2) := by
              gcongr
          _ = 2 * Q ^ 2 / Real.sqrt d := by ring
    have hsum := Finset.sum_le_sum hpt
    rw [Finset.sum_const, nsmul_eq_mul] at hsum
    have hcard := w1_card_N ct
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * aOf d p ^ 2)]
    have hQ2 : 0 ≤ 2 * Q ^ 2 / Real.sqrt d := by positivity
    have step1 : 4 * aOf d p ^ 2 * ∑ m ∈ ct.N, |ct.adjS x m * ct.uvec m| * Aq m ≤
        4 * aOf d p ^ 2 * ((ct.N.card : ℝ) * (2 * Q ^ 2 / Real.sqrt d)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    have step2 : (ct.N.card : ℝ) * (2 * Q ^ 2 / Real.sqrt d) ≤ d * (2 * Q ^ 2 / Real.sqrt d) :=
      mul_le_mul_of_nonneg_right hcard hQ2
    have step3 : 4 * aOf d p ^ 2 * (d * (2 * Q ^ 2 / Real.sqrt d)) ≤ 8 * Q ^ 2 / Real.sqrt d := by
      have e : 4 * aOf d p ^ 2 * (d * (2 * Q ^ 2 / Real.sqrt d)) =
          (aOf d p ^ 2 * d) * (8 * Q ^ 2 / Real.sqrt d) := by ring
      rw [e]
      exact mul_le_of_le_one_left (by positivity) had
    have := mul_le_mul_of_nonneg_left step2 (by positivity : (0 : ℝ) ≤ 4 * aOf d p ^ 2)
    linarith

end Psi

end BiluLinial.Tight.SecB
