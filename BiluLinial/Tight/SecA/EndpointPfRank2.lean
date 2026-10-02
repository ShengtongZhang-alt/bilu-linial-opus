/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecA.EndpointDefs
public import BiluLinial.Tight.FloorLemma

/-!
# Rank-two edge perturbations (proofs for `A-RANK2`)

For an invertible symmetric `P`, `G = P⁻¹` and `E = e_v e_iᵀ + e_i e_vᵀ` (`v ≠ i`):

* `det_add_rank_two_pf`: `det(P + tE) = det P · δ(t)`, `δ(t) = 1 + 2t G_vi - t²(G_vv G_ii - G_vi²)`
  (matrix determinant lemma with `E = U W`, `U = [e_v, e_i]`, `W = [e_i, e_v]ᵀ`);
* `inv_add_rank_two_apply_pf`: `(P + tE)⁻¹_vi = (G_vi - t(G_vv G_ii - G_vi²))/δ(t)` if `δ(t) ≠ 0`
  (the explicit column `x = G((1 + tG_vi) e_i - t G_ii e_v)/δ` solves `(P + tE) x = e_i`);
* `epf_posDef_add_rank_two`: if `P ≻ 0` and `δ(t) > 0` then `P + tE ≻ 0` (Cauchy–Schwarz in the
  `P`-inner product gives `xᵀPx · Δ ≥ G_ii α² - 2G_vi αβ + G_vv β²` for `α = x_v`, `β = x_i`,
  `Δ = G_vv G_ii - G_vi²`, and the binary form `G_ii α² + 2(tΔ - G_vi) αβ + G_vv β²` has
  determinant `Δ δ(t) > 0`).
-/

@[expose] public section

namespace BiluLinial.Tight.SecA

open Matrix

section Rank2

variable {n : Type*} [Fintype n] [DecidableEq n]


omit [Fintype n] in
theorem epf_edgeE_apply (v i a b : n) :
    edgeE v i a b = (if v = a ∧ i = b then 1 else 0) + (if i = a ∧ v = b then 1 else 0) := by
  simp [edgeE, Matrix.single_apply]

theorem epf_inv_symm {P : Matrix n n ℝ} (hP : P.IsHermitian) (a b : n) : P⁻¹ a b = P⁻¹ b a := by
  simpa using hP.inv.apply b a

/-- `A-RANK2`: the determinant of a rank-two edge perturbation. -/
theorem det_add_rank_two_pf {P : Matrix n n ℝ} (hP : P.IsHermitian) (hdet : IsUnit P.det)
    {v i : n} (hvi : v ≠ i) (t : ℝ) :
    (P + t • edgeE v i).det = P.det * (1 + 2 * t * P⁻¹ v i -
      t ^ 2 * (P⁻¹ v v * P⁻¹ i i - P⁻¹ v i ^ 2)) := by
  let U : Matrix n (Fin 2) ℝ := Matrix.of fun a k =>
    if k = 0 then (if a = v then t else 0) else (if a = i then t else 0)
  let W : Matrix (Fin 2) n ℝ := Matrix.of fun k b =>
    if k = 0 then (if b = i then 1 else 0) else (if b = v then 1 else 0)
  have hUW : t • edgeE v i = U * W := by
    ext a b
    simp only [Matrix.smul_apply, epf_edgeE_apply, mul_apply, Fin.sum_univ_two, U, W, of_apply,
      smul_eq_mul]
    by_cases ha : a = v <;> by_cases hb : b = i <;> by_cases ha' : a = i <;>
      by_cases hb' : b = v <;> simp_all [eq_comm]
  rw [hUW, det_add_mul U W hdet]
  congr 1
  have hs := epf_inv_symm hP i v
  rw [det_fin_two]
  simp only [Matrix.add_apply, Matrix.mul_apply, U, W, Matrix.of_apply, Matrix.one_apply]
  simp [ite_mul, mul_ite, Finset.sum_ite_eq', hs]
  ring

/-- `A-RANK2`: the inverse entry of a rank-two edge perturbation. -/
theorem inv_add_rank_two_apply_pf {P : Matrix n n ℝ} (hP : P.IsHermitian) (hdet : IsUnit P.det)
    {v i : n} (hvi : v ≠ i) {t : ℝ}
    (hδ : 1 + 2 * t * P⁻¹ v i - t ^ 2 * (P⁻¹ v v * P⁻¹ i i - P⁻¹ v i ^ 2) ≠ 0) :
    (P + t • edgeE v i)⁻¹ v i = (P⁻¹ v i - t * (P⁻¹ v v * P⁻¹ i i - P⁻¹ v i ^ 2)) /
      (1 + 2 * t * P⁻¹ v i - t ^ 2 * (P⁻¹ v v * P⁻¹ i i - P⁻¹ v i ^ 2)) := by
  set δ := 1 + 2 * t * P⁻¹ v i - t ^ 2 * (P⁻¹ v v * P⁻¹ i i - P⁻¹ v i ^ 2) with hδdef
  have hs := epf_inv_symm hP i v
  have hM : IsUnit (P + t • edgeE v i).det := by
    rw [det_add_rank_two_pf hP hdet hvi t]
    exact hdet.mul (isUnit_iff_ne_zero.2 hδ)
  set α := (1 + t * P⁻¹ v i) / δ with hα
  set β := -(t * P⁻¹ i i) / δ with hβ
  set x : n → ℝ := P⁻¹ *ᵥ (Pi.single i α + Pi.single v β) with hx
  have hxk : ∀ k, x k = P⁻¹ k i * α + P⁻¹ k v * β := by
    intro k
    simp [hx, mulVec_add]
    ring
  have hPx : P *ᵥ x = Pi.single i α + Pi.single v β := by
    rw [hx, mulVec_mulVec, mul_nonsing_inv P hdet, one_mulVec]
  have hEx : ∀ k, (edgeE v i *ᵥ x) k = (if k = v then x i else 0) + (if k = i then x v else 0) := by
    intro k
    simp only [mulVec, dotProduct, epf_edgeE_apply, add_mul, Finset.sum_add_distrib, ite_mul,
      one_mul, zero_mul]
    by_cases hk : k = v <;> by_cases hk' : k = i <;> simp_all [eq_comm]
  have hsol : (P + t • edgeE v i) *ᵥ x = Pi.single i 1 := by
    rw [add_mulVec, smul_mulVec, hPx]
    funext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hEx]
    by_cases hk : k = i
    · subst hk
      simp only [Pi.single_eq_same, Pi.single_eq_of_ne hvi.symm, ite_eq_right hvi.symm, ite_true,
        hxk, hs]
      rw [hα, hβ]
      field_simp
      ring
    · by_cases hk' : k = v
      · subst hk'
        simp only [Pi.single_eq_of_ne hvi, Pi.single_eq_same, ite_true, ite_eq_right hvi, hxk, hs]
        rw [hα, hβ]
        field_simp
        ring
      · simp [hk, hk']
  have hinv : (P + t • edgeE v i)⁻¹ *ᵥ Pi.single i 1 = x := by
    rw [← hsol, mulVec_mulVec, nonsing_inv_mul _ hM, one_mulVec]
  have h2 := congrFun hinv v
  simp only [mulVec_single, MulOpposite.op_one, one_smul, col_apply] at h2
  rw [h2, hxk, hα, hβ]
  field_simp
  ring

theorem epf_edgeE_mulVec (v i : n) (x : n → ℝ) :
    edgeE v i *ᵥ x = Pi.single v (x i) + Pi.single i (x v) := by
  funext k
  simp only [mulVec, dotProduct, epf_edgeE_apply, add_mul, Finset.sum_add_distrib, ite_mul,
    one_mul, zero_mul, Pi.add_apply, Pi.single_apply]
  by_cases hk : k = v <;> by_cases hk' : k = i <;> simp_all [eq_comm]

/-- The quadratic form at a vector supported on `{v, i}`. -/
theorem epf_quad_two (M : Matrix n n ℝ) {v i : n} (u w : ℝ) :
    (Pi.single v u + Pi.single i w) ⬝ᵥ (M *ᵥ (Pi.single v u + Pi.single i w)) =
      u * (M v v * u + M v i * w) + w * (M i v * u + M i i * w) := by
  simp [add_dotProduct, mulVec_add, mulVec_single]
  ring

theorem epf_dot_two (x : n → ℝ) {v i : n} (u w : ℝ) :
    (Pi.single v u + Pi.single i w) ⬝ᵥ x = u * x v + w * x i := by
  simp [add_dotProduct]

/-- A positive definite binary quadratic form is positive off the origin. -/
theorem epf_binary_pos {A B C α β : ℝ} (hA : 0 < A) (hD : 0 < A * C - B ^ 2)
    (hne : α ≠ 0 ∨ β ≠ 0) : 0 < A * α ^ 2 + 2 * B * α * β + C * β ^ 2 := by
  have key : A * (A * α ^ 2 + 2 * B * α * β + C * β ^ 2) =
      (A * α + B * β) ^ 2 + (A * C - B ^ 2) * β ^ 2 := by ring
  rcases eq_or_ne β 0 with hβ | hβ
  · subst hβ
    have hα : α ≠ 0 := by simpa using hne
    have : 0 < α ^ 2 := by positivity
    nlinarith
  · have h1 : 0 < (A * C - B ^ 2) * β ^ 2 := by positivity
    have h2 : 0 < A * (A * α ^ 2 + 2 * B * α * β + C * β ^ 2) := by
      rw [key]; nlinarith [sq_nonneg (A * α + B * β)]
    exact pos_of_mul_pos_right h2 hA.le

/-- The `2 × 2` principal minor of a positive definite matrix is positive. -/
theorem epf_minor_pos {G : Matrix n n ℝ} (hG : G.PosDef) {v i : n} (hvi : v ≠ i) :
    0 < G v v * G i i - G v i ^ 2 := by
  have hs : G i v = G v i := by simpa using hG.isHermitian.apply v i
  have hii : 0 < G i i := hG.diag_pos
  set z : n → ℝ := Pi.single v (G i i) + Pi.single i (-G v i)
  have hz : z ≠ 0 := by
    intro h
    have := congrFun h v
    simp [z, Pi.single_eq_of_ne hvi] at this
    exact hii.ne' this
  have hpos := hG.dotProduct_mulVec_pos hz
  rw [star_trivial, epf_quad_two, hs] at hpos
  have : G i i * (G v v * G i i - G v i ^ 2) = G i i * (G v v * G i i + G v i * -G v i) +
      -G v i * (G v i * G i i + G i i * -G v i) := by ring
  rw [← this] at hpos
  exact pos_of_mul_pos_right hpos hii.le

/-- If `P ≻ 0`, `v ≠ i` and `δ(t) > 0`, then `P + tE ≻ 0`. -/
theorem epf_posDef_add_rank_two {P : Matrix n n ℝ} (hP : P.PosDef) {v i : n} (hvi : v ≠ i)
    {t : ℝ} (hδ : 0 < 1 + 2 * t * P⁻¹ v i - t ^ 2 * (P⁻¹ v v * P⁻¹ i i - P⁻¹ v i ^ 2)) :
    (P + t • edgeE v i).PosDef := by
  have hG : (P⁻¹).PosDef := hP.inv
  have hs : P⁻¹ i v = P⁻¹ v i := epf_inv_symm hP.isHermitian i v
  have hΔ := epf_minor_pos hG hvi
  have hii : 0 < P⁻¹ i i := hG.diag_pos
  have hvv : 0 < P⁻¹ v v := hG.diag_pos
  set Gvi := P⁻¹ v i
  set Gvv := P⁻¹ v v
  set Gii := P⁻¹ i i
  set Δ := Gvv * Gii - Gvi ^ 2 with hΔdef
  have hherm : (P + t • edgeE v i).IsHermitian := by
    refine IsHermitian.ext fun a b => ?_
    have hPab : P b a = P a b := by simpa using hP.isHermitian.apply a b
    simp only [star_trivial, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, epf_edgeE_apply,
      hPab]
    by_cases ha : a = v <;> by_cases hb : b = i <;> by_cases ha' : a = i <;>
      by_cases hb' : b = v <;> simp_all [eq_comm]
  refine PosDef.of_dotProduct_mulVec_pos hherm fun x hx => ?_
  rw [star_trivial, add_mulVec, dotProduct_add, smul_mulVec, dotProduct_smul, smul_eq_mul]
  have hEx : x ⬝ᵥ (edgeE v i *ᵥ x) = 2 * x v * x i := by
    rw [epf_edgeE_mulVec, dotProduct_add, dotProduct_single, dotProduct_single]
    ring
  rw [hEx]
  set Q := x ⬝ᵥ (P *ᵥ x) with hQ
  have hQpos : 0 < Q := by simpa using hP.dotProduct_mulVec_pos hx
  set α := x v
  set β := x i
  by_cases h0 : α = 0 ∧ β = 0
  · rw [h0.1]; simpa using hQpos
  have hne : α ≠ 0 ∨ β ≠ 0 := by tauto
  -- Cauchy–Schwarz with `y = u e_v + w e_i`, `(u, w) = adj(G₂)(α, β)`
  have hcs := FloorIns.quad_cs hP
    (Pi.single v (Gii * α - Gvi * β) + Pi.single i (Gvv * β - Gvi * α)) x
  rw [epf_dot_two, epf_quad_two, hs] at hcs
  set N := Gii * α ^ 2 + 2 * (-Gvi) * α * β + Gvv * β ^ 2 with hN
  have e1 : (Gii * α - Gvi * β) * α + (Gvv * β - Gvi * α) * β = N := by rw [hN]; ring
  have e2 : (Gii * α - Gvi * β) * (Gvv * (Gii * α - Gvi * β) + Gvi * (Gvv * β - Gvi * α)) +
      (Gvv * β - Gvi * α) * (Gvi * (Gii * α - Gvi * β) + Gii * (Gvv * β - Gvi * α)) =
      Δ * N := by rw [hN, hΔdef]; ring
  rw [e1, e2] at hcs
  have hNpos : 0 < N := epf_binary_pos hii (by rw [neg_sq, mul_comm]; exact hΔ) hne
  have hNle : N ≤ Q * Δ := by
    have : N * N ≤ (Q * Δ) * N := by nlinarith
    exact le_of_mul_le_mul_right this hNpos
  have hform : 0 < Gii * α ^ 2 + 2 * (t * Δ - Gvi) * α * β + Gvv * β ^ 2 := by
    refine epf_binary_pos hii ?_ hne
    have : Gii * Gvv - (t * Δ - Gvi) ^ 2 = Δ * (1 + 2 * t * Gvi - t ^ 2 * Δ) := by
      rw [hΔdef]; ring
    rw [this]
    exact mul_pos hΔ hδ
  have : 0 < Δ * (Q + t * (2 * α * β)) := by nlinarith
  exact pos_of_mul_pos_right this hΔ.le

end Rank2

end BiluLinial.Tight.SecA
