/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.Ctx

/-!
# The walk matrix `𝓑` and its inverse `K`

Blueprint node `D-walk` (source Section 1.1, Lemma "Deletion and source differentiation", and its
last paragraph; AUDIT-D X7). On sources `0 ≤ y ≤ s` every edge has `τ_ij ≤ τ_*`, so `𝓑` is
strictly diagonally dominant: `𝓑_ii - Σ_j |𝓑_ij| = 1 - Σ_j τ_ij/(1+τ_ij) ≥ 1 - dτ_*/(1+τ_*)
= η₀/(1+τ_*) > 0`. Hence `𝓑 ≻ 0`. Its inverse is the nonbacktracking walk sum
`K_ij = Σ_{walks i → j} Π τ_e` (empty walk included): with `S_{·w}` the walk sums to `w` and
`M_{i→j,w}` the part starting with the step `i → j`,
`S_iw = 1_{i=w} + Σ_j M_{i→j,w}`, `M_{i→j,w} = τ_ij (S_jw - M_{j→i,w})`, and elimination gives
`𝓑 S_{·w} = e_w`. The series converges because the directed walk operator applied to
`f_{i→j} = 1/(1+τ_ij)` is strictly smaller than `f` (the same dominance inequality). Hence
`K ≥ 0`, `K_ii ≥ 1` (empty walk) and `K_ij ≥ τ_ij` on edges (the one-step walk). At a zero source
all `τ` at that vertex vanish and `𝓑` has an identity row, so the statement covers the
positive-source subgraph (AUDIT-D, gap G1). Off `S`, `𝓑` is the identity.

**Formal route.** No series: from a column `x = K e_w` we define the directed-edge quantities
`M_{i→j} = (τ x_j - τ² x_i)/(1 - τ²)`, which satisfy both relations above, hence
`M_{i→j} = τ_ij (1_{j=w} + Σ_{k ∈ N(j), k ≠ i} M_{j→k})`. Each row of this directed walk
operator has mass at most `τ_* (d - 1) = 1 - η₀ < 1`, so a minimum principle gives `M ≥ 0`, and
the three bounds follow.
-/

@[expose] public section

namespace BiluLinial.Tight

open Matrix

/-- A symmetric real matrix with nonpositive off-diagonal entries and positive row sums is
positive definite: `xᵀBx = Σ_i (Σ_j B_ij) x_i² - ½ Σ_{i,j} B_ij (x_i - x_j)²`. -/
theorem posDef_of_offDiag_nonpos_rowSum_pos {n : Type*} [Fintype n] [DecidableEq n]
    (B : Matrix n n ℝ) (hsymm : ∀ i j, B i j = B j i) (hoff : ∀ i j, i ≠ j → B i j ≤ 0)
    (hrow : ∀ i, 0 < ∑ j, B i j) : B.PosDef := by
  refine PosDef.of_dotProduct_mulVec_pos (IsHermitian.ext fun i j => by simp [hsymm j i])
    fun x hx => ?_
  have hQ : star x ⬝ᵥ (B *ᵥ x) = ∑ i, ∑ j, B i j * x i * x j := by
    simp only [dotProduct, mulVec, star_trivial, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have h3 : ∑ i, ∑ j, B i j * x j ^ 2 = ∑ i, ∑ j, B i j * x i ^ 2 := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hsymm]
  have hexp : ∑ i, ∑ j, B i j * (x i - x j) ^ 2 = ∑ i, ∑ j, B i j * x i ^ 2 -
      2 * ∑ i, ∑ j, B i j * x i * x j + ∑ i, ∑ j, B i j * x j ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hneg : ∑ i, ∑ j, B i j * (x i - x j) ^ 2 ≤ 0 := by
    refine Finset.sum_nonpos fun i _ => Finset.sum_nonpos fun j _ => ?_
    by_cases h : i = j
    · subst h
      simp
    · nlinarith [hoff i j h, sq_nonneg (x i - x j)]
  have hpos : 0 < ∑ i, ∑ j, B i j * x i ^ 2 := by
    obtain ⟨k, hk⟩ := Function.ne_iff.mp hx
    have hk2 : 0 < x k ^ 2 := lt_of_le_of_ne (sq_nonneg _) (pow_ne_zero 2 hk).symm
    simp_rw [← Finset.sum_mul]
    exact Finset.sum_pos' (fun i _ => mul_nonneg (hrow i).le (sq_nonneg _))
      ⟨k, Finset.mem_univ _, mul_pos (hrow k) hk2⟩
  rw [hQ]
  linarith

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable {d p : ℕ}

omit [Fintype V] [DecidableEq V] in
private theorem walk_τEdge_comm (a : ℝ) (y : V → ℝ) (i j : V) :
    τEdge a y i j = τEdge a y j i := by
  unfold τEdge cEdge
  rw [mul_right_comm (a ^ 2) (y i) (y j)]

omit [DecidableEq V] in
private theorem walk_card_nbhd_le (hdeg : ∀ v, G.degree v ≤ d) (S : Finset V) (i : V) :
    (nbhd G S i).card ≤ d := by
  refine le_trans ?_ (hdeg i)
  rw [← G.card_neighborFinset_eq_degree]
  refine Finset.card_le_card fun j hj => ?_
  rw [nbhd, Finset.mem_filter] at hj
  exact (G.mem_neighborFinset i j).mpr hj.2

omit [Fintype V] in
/-- A row of `𝓑` at a vertex of `S`. -/
theorem walkB_apply_of_mem {a : ℝ} {y : V → ℝ} {S : Finset V} {i : V} (hi : i ∈ S) (u : V) :
    walkB G a y S i u =
      (if i = u then 1 + ∑ j ∈ nbhd G S i, τEdge a y i j ^ 2 / (1 - τEdge a y i j ^ 2)
        else 0) - (if u ∈ nbhd G S i then τEdge a y i u / (1 - τEdge a y i u ^ 2) else 0) := by
  by_cases h : i = u
  · subst h
    simp [walkB, nbhd, hi]
  · by_cases hu : u ∈ S <;> by_cases ha : G.Adj i u <;> simp [walkB, nbhd, h, hi, hu, ha]

omit [Fintype V] in
/-- Off `S`, `𝓑` has identity rows. -/
theorem walkB_apply_of_not_mem {a : ℝ} {y : V → ℝ} {S : Finset V} {i : V} (hi : i ∉ S)
    (u : V) : walkB G a y S i u = if i = u then 1 else 0 := by
  by_cases h : i = u
  · subst h
    simp [walkB, hi]
  · simp [walkB, h, hi]

omit [Fintype V] in
theorem walkB_comm (a : ℝ) (y : V → ℝ) (S : Finset V) (i u : V) :
    walkB G a y S i u = walkB G a y S u i := by
  by_cases h : i = u
  · rw [h]
  · have h' : u ≠ i := Ne.symm h
    by_cases ha : G.Adj i u
    · by_cases hi : i ∈ S <;> by_cases hu : u ∈ S <;>
        simp [walkB, h, h', hi, hu, ha, ha.symm, walk_τEdge_comm a y u i]
    · have ha' : ¬G.Adj u i := fun h => ha h.symm
      by_cases hi : i ∈ S <;> by_cases hu : u ∈ S <;> simp [walkB, h, h', hi, hu, ha, ha']

/-- `(𝓑 x)_i` at a vertex `i ∈ S`. -/
theorem walkB_sum_mul_of_mem {a : ℝ} {y : V → ℝ} {S : Finset V} {i : V} (hi : i ∈ S)
    (x : V → ℝ) :
    ∑ u, walkB G a y S i u * x u =
      (1 + ∑ j ∈ nbhd G S i, τEdge a y i j ^ 2 / (1 - τEdge a y i j ^ 2)) * x i -
        ∑ j ∈ nbhd G S i, τEdge a y i j / (1 - τEdge a y i j ^ 2) * x j := by
  simp only [walkB_apply_of_mem G hi, sub_mul, ite_mul, zero_mul, Finset.sum_sub_distrib,
    Finset.sum_ite_eq, Finset.sum_ite_mem, Finset.mem_univ, Finset.univ_inter, ↓reduceIte]

/-- `D-walk` for any edge weights `0 ≤ τ_ij ≤ t < 1` with `(d - 1) t < 1`, on a graph of maximum
degree at most `d`. -/
theorem walk_facts_of_bound (hdeg : ∀ v, G.degree v ≤ d) {a : ℝ} {y : V → ℝ} (S : Finset V)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (hdt : ((d : ℝ) - 1) * t < 1)
    (hτ0 : ∀ i j, 0 ≤ τEdge a y i j) (hτt : ∀ i j, τEdge a y i j ≤ t) :
    (walkB G a y S).PosDef ∧ (∀ i j, 0 ≤ walkK G a y S i j) ∧
      (∀ i, 1 ≤ walkK G a y S i i) ∧
      ∀ i j, i ∈ S → j ∈ S → G.Adj i j → τEdge a y i j ≤ walkK G a y S i j := by
  have hden : ∀ i j, 0 < 1 - τEdge a y i j ^ 2 := fun i j => by
    nlinarith [hτ0 i j, hτt i j]
  -- Positive definiteness: positive row sums.
  have hPD : (walkB G a y S).PosDef := by
    refine posDef_of_offDiag_nonpos_rowSum_pos _ (walkB_comm G a y S) (fun i u h => ?_)
      (fun i => ?_)
    · simp only [walkB, of_apply, h, ↓reduceIte]
      split_ifs
      · exact neg_nonpos.mpr (div_nonneg (hτ0 i u) (hden i u).le)
      · exact le_rfl
    · by_cases hi : i ∈ S
      · have hsum := walkB_sum_mul_of_mem G (a := a) (y := y) hi (fun _ => (1 : ℝ))
        simp only [mul_one] at hsum
        rw [hsum]
        have hterm : ∀ j ∈ nbhd G S i, τEdge a y i j / (1 - τEdge a y i j ^ 2) -
            τEdge a y i j ^ 2 / (1 - τEdge a y i j ^ 2) =
            τEdge a y i j / (1 + τEdge a y i j) := by
          intro j _
          have h1 := (hden i j).ne'
          have h2 : 1 + τEdge a y i j ≠ 0 := by linarith [hτ0 i j]
          field_simp
          ring
        have hle : ∀ j ∈ nbhd G S i, τEdge a y i j / (1 + τEdge a y i j) ≤ t / (1 + t) := by
          intro j _
          rw [div_le_div_iff₀ (by linarith [hτ0 i j]) (by linarith)]
          nlinarith [hτt i j]
        have hcard : ((nbhd G S i).card : ℝ) ≤ d := by
          exact_mod_cast walk_card_nbhd_le G hdeg S i
        have hsum2 : ∑ j ∈ nbhd G S i, τEdge a y i j / (1 + τEdge a y i j) ≤
            d * (t / (1 + t)) := by
          refine (Finset.sum_le_card_nsmul _ _ _ hle).trans ?_
          rw [nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right hcard (div_nonneg ht0 (by linarith))
        have hdt' : (d : ℝ) * (t / (1 + t)) < 1 := by
          rw [mul_div_assoc', div_lt_one (by linarith)]
          nlinarith
        have hdiff : ∑ j ∈ nbhd G S i, τEdge a y i j / (1 - τEdge a y i j ^ 2) -
            ∑ j ∈ nbhd G S i, τEdge a y i j ^ 2 / (1 - τEdge a y i j ^ 2) =
            ∑ j ∈ nbhd G S i, τEdge a y i j / (1 + τEdge a y i j) := by
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl hterm
        linarith
      · simp [walkB_apply_of_not_mem G hi]
  have hBK : walkB G a y S * walkK G a y S = 1 :=
    mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hPD.det_pos.ne')
  -- Column `w` of `K`.
  have hcol : ∀ w, (∀ i, 0 ≤ walkK G a y S i w) ∧ 1 ≤ walkK G a y S w w ∧
      ∀ i, i ∈ S → w ∈ S → G.Adj i w → τEdge a y i w ≤ walkK G a y S i w := by
    intro w
    obtain ⟨x, hxdef⟩ : ∃ x : V → ℝ, ∀ u, walkK G a y S u w = x u := ⟨_, fun _ => rfl⟩
    have hx : ∀ i, ∑ u, walkB G a y S i u * x u = if i = w then 1 else 0 := by
      intro i
      have h := congrFun (congrFun hBK i) w
      rw [mul_apply, one_apply] at h
      simpa only [hxdef] using h
    have hxout : ∀ i, i ∉ S → x i = if i = w then 1 else 0 := by
      intro i hi
      rw [← hx i]
      simp [walkB_apply_of_not_mem G hi]
    obtain ⟨M, hM⟩ : ∃ M : V → V → ℝ, ∀ i j, M i j =
        (τEdge a y i j * x j - τEdge a y i j ^ 2 * x i) / (1 - τEdge a y i j ^ 2) :=
      ⟨_, fun _ _ => rfl⟩
    have hvert : ∀ i, i ∈ S → x i = (if i = w then 1 else 0) + ∑ j ∈ nbhd G S i, M i j := by
      intro i hi
      have h := hx i
      rw [walkB_sum_mul_of_mem G hi] at h
      rw [← h]
      have hMsum : ∑ j ∈ nbhd G S i, M i j =
          ∑ j ∈ nbhd G S i, τEdge a y i j / (1 - τEdge a y i j ^ 2) * x j -
            (∑ j ∈ nbhd G S i, τEdge a y i j ^ 2 / (1 - τEdge a y i j ^ 2)) * x i := by
        rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun j _ => by rw [hM]; ring
      rw [hMsum]
      ring
    have hedge : ∀ i j, i ∈ S → j ∈ nbhd G S i → M i j =
        τEdge a y i j * ((if j = w then 1 else 0) + ∑ k ∈ (nbhd G S j).erase i, M j k) := by
      intro i j hi hj
      simp only [nbhd, Finset.mem_filter] at hj
      have hij : i ∈ nbhd G S j := Finset.mem_filter.mpr ⟨hi, hj.2.symm⟩
      have h1 : (if j = w then (1 : ℝ) else 0) + ∑ k ∈ (nbhd G S j).erase i, M j k =
          x j - M j i := by
        rw [hvert j hj.1, ← Finset.add_sum_erase _ _ hij]
        ring
      rw [h1, hM i j, hM j i, walk_τEdge_comm a y j i]
      have h2 := (hden i j).ne'
      field_simp
      ring
    -- Minimum principle on directed edges.
    have hMnn : ∀ i j, i ∈ S → j ∈ nbhd G S i → 0 ≤ M i j := by
      by_contra hneg
      simp only [not_forall, not_le] at hneg
      obtain ⟨i₀, j₀, hi₀, hj₀, hlt⟩ := hneg
      set E := (S ×ˢ (Finset.univ : Finset V)).filter (fun e => e.2 ∈ nbhd G S e.1) with hE
      have hmemE : ∀ i j, i ∈ S → j ∈ nbhd G S i → (i, j) ∈ E := fun i j hi hj =>
        Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hi, Finset.mem_univ _⟩, hj⟩
      obtain ⟨e, he, hmin⟩ := E.exists_min_image (fun e => M e.1 e.2) ⟨_, hmemE i₀ j₀ hi₀ hj₀⟩
      have he' := Finset.mem_filter.mp he
      have hi : e.1 ∈ S := (Finset.mem_product.mp he'.1).1
      have hj : e.2 ∈ nbhd G S e.1 := he'.2
      have hm : M e.1 e.2 < 0 := lt_of_le_of_lt (hmin _ (hmemE i₀ j₀ hi₀ hj₀)) hlt
      have hj2 := Finset.mem_filter.mp hj
      have hij : e.1 ∈ nbhd G S e.2 := Finset.mem_filter.mpr ⟨hi, hj2.2.symm⟩
      have hsum : (((nbhd G S e.2).erase e.1).card : ℝ) * M e.1 e.2 ≤
          ∑ k ∈ (nbhd G S e.2).erase e.1, M e.2 k := by
        rw [← nsmul_eq_mul]
        exact Finset.card_nsmul_le_sum _ _ _ fun k hk =>
          hmin _ (hmemE _ _ hj2.1 (Finset.mem_of_mem_erase hk))
      have hcard : (((nbhd G S e.2).erase e.1).card : ℝ) ≤ (d : ℝ) - 1 := by
        have h1 := Finset.card_erase_add_one hij
        have h2 := walk_card_nbhd_le G hdeg S e.2
        have h3 : ((nbhd G S e.2).erase e.1).card + 1 ≤ d := h1 ▸ h2
        have h4 : (((nbhd G S e.2).erase e.1).card : ℝ) + 1 ≤ d := by exact_mod_cast h3
        linarith
      have hrec := hedge e.1 e.2 hi hj
      have hδ : (0 : ℝ) ≤ if e.2 = w then 1 else 0 := by split_ifs <;> norm_num
      have hτ := hτ0 e.1 e.2
      have hτ' := hτt e.1 e.2
      have hc0 : (0 : ℝ) ≤ ((nbhd G S e.2).erase e.1).card := Nat.cast_nonneg _
      have k1 := mul_le_mul_of_nonneg_left hsum hτ
      have k2 := mul_nonneg hτ hδ
      have k3 : τEdge a y e.1 e.2 * (((nbhd G S e.2).erase e.1).card : ℝ) ≤
          t * ((d : ℝ) - 1) := mul_le_mul hτ' hcard hc0 ht0
      have k4 := mul_le_mul_of_nonpos_right k3 hm.le
      have k5 : 0 < (t * ((d : ℝ) - 1) - 1) * M e.1 e.2 :=
        mul_pos_of_neg_of_neg (by linarith) hm
      nlinarith
    have hMlb : ∀ i j, i ∈ S → j ∈ nbhd G S i →
        τEdge a y i j * (if j = w then 1 else 0) ≤ M i j := by
      intro i j hi hj
      have hjS : j ∈ S := (Finset.mem_filter.mp hj).1
      rw [hedge i j hi hj]
      refine mul_le_mul_of_nonneg_left (le_add_of_nonneg_right ?_) (hτ0 i j)
      exact Finset.sum_nonneg fun k hk => hMnn j k hjS (Finset.mem_of_mem_erase hk)
    refine ⟨fun i => ?_, ?_, fun i hi hw hadj => ?_⟩
    · rw [hxdef]
      by_cases hi : i ∈ S
      · rw [hvert i hi]
        exact add_nonneg (by split_ifs <;> norm_num)
          (Finset.sum_nonneg fun j hj => hMnn i j hi hj)
      · rw [hxout i hi]
        split_ifs <;> norm_num
    · rw [hxdef]
      by_cases hw : w ∈ S
      · rw [hvert w hw]
        have := Finset.sum_nonneg fun j hj => hMnn w j hw hj
        simp only [↓reduceIte]
        linarith
      · rw [hxout w hw]
        simp
    · rw [hxdef, hvert i hi]
      have hne : i ≠ w := G.ne_of_adj hadj
      have hwN : w ∈ nbhd G S i := Finset.mem_filter.mpr ⟨hw, hadj⟩
      have h1 := hMlb i w hi hwN
      have h2 := Finset.single_le_sum (fun j hj => hMnn i j hi hj) hwN
      simp only [hne, ↓reduceIte, mul_one, zero_add] at h1 ⊢
      linarith
  exact ⟨hPD, fun i j => (hcol j).1 i, fun i => (hcol i).2.1,
    fun i j hi hj hadj => (hcol j).2.2 i hi hj hadj⟩

private theorem walk_cRoot_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ cRoot x := by
  have h : 1 ≤ Real.sqrt (1 + 4 * x) := by
    have := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 1 + 4 * x by linarith)
    rwa [Real.sqrt_one] at this
  rw [cRoot]
  linarith

private theorem walk_cRoot_mono {x x' : ℝ} (h : x ≤ x') : cRoot x ≤ cRoot x' := by
  have := Real.sqrt_le_sqrt (show 1 + 4 * x ≤ 1 + 4 * x' by linarith)
  rw [cRoot, cRoot]
  linarith

omit [Fintype V] [DecidableEq V] in
/-- On sources `0 ≤ y ≤ s`, every edge weight satisfies `0 ≤ τ_ij ≤ τ_*`. -/
private theorem walk_τEdge_bounds (hR : TRegime d p) {y : V → ℝ} (hy : InCube (sOf d p) y)
    (i j : V) : 0 ≤ τEdge (aOf d p) y i j ∧ τEdge (aOf d p) y i j ≤ τsOf d p := by
  have hs := hR.sOf_pos
  obtain ⟨hi0, his⟩ := hy i
  obtain ⟨hj0, hjs⟩ := hy j
  have hx0 : 0 ≤ aOf d p ^ 2 * y i * y j := mul_nonneg (mul_nonneg (sq_nonneg _) hi0) hj0
  have hxs : aOf d p ^ 2 * y i * y j ≤ aOf d p ^ 2 * sOf d p * sOf d p := by
    have h1 := mul_le_mul his hjs hj0 hs.le
    calc aOf d p ^ 2 * y i * y j = aOf d p ^ 2 * (y i * y j) := by ring
      _ ≤ aOf d p ^ 2 * (sOf d p * sOf d p) := mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
      _ = aOf d p ^ 2 * sOf d p * sOf d p := by ring
  have hc0 : 0 ≤ cEdge (aOf d p) y i j := walk_cRoot_nonneg hx0
  have hcs : cEdge (aOf d p) y i j ≤ τsOf d p / (1 - τsOf d p) := by
    have h := walk_cRoot_mono hxs
    rw [hR.cRoot_const] at h
    exact h
  have hτ1 : 0 < 1 - τsOf d p := sub_pos.mpr hR.τsOf_lt_one
  refine ⟨div_nonneg hc0 (by linarith), ?_⟩
  rw [τEdge, div_le_iff₀ (by linarith)]
  rw [le_div_iff₀ hτ1] at hcs
  linarith

/-- `D-walk`: `𝓑 ≻ 0`, `K = 𝓑⁻¹ ≥ 0`, `K_ii ≥ 1`, `K_ij ≥ τ_ij` on edges of `G[S]`. -/
theorem walk_facts (hR : TRegime d p) (hdeg : ∀ v, G.degree v ≤ d) {y : V → ℝ}
    (hy : InCube (sOf d p) y) (S : Finset V) :
    (walkB G (aOf d p) y S).PosDef ∧ (∀ i j, 0 ≤ walkK G (aOf d p) y S i j) ∧
      (∀ i, 1 ≤ walkK G (aOf d p) y S i i) ∧
      ∀ i j, i ∈ S → j ∈ S → G.Adj i j → τEdge (aOf d p) y i j ≤ walkK G (aOf d p) y S i j := by
  refine walk_facts_of_bound G hdeg S hR.τsOf_pos.le hR.τsOf_lt_one ?_
    (fun i j => (walk_τEdge_bounds hR hy i j).1) (fun i j => (walk_τEdge_bounds hR hy i j).2)
  have h := hR.qOf_mul_τsOf
  have h0 := hR.η0Of_pos
  rw [qOf] at h
  linarith

end BiluLinial.Tight
