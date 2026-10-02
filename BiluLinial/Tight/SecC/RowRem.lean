/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecC.RowCompareParts
public import BiluLinial.Tight.Tools.MatrixFacts
public import BiluLinial.Tight.SecC.RootMoments

/-!
# The averaged remainder of (E4) for `F = rowNum` (node CR-REM of `docs/tight/BP_SECC.md`)

Source lines 1153–1162 (step 4 of AUDIT-C §4.2). A-REM (`CapPoint.trans_rem`) for the family
`F_σ = rowNum p A_σ B_σ` on the core support (`0` off it), with
`rowNum = clipObs((p-1) q_{A²}) (p-2) p + clipObs(p q_{AB}) (p-1) (p-1)` (`rowNum_eq_clipObs`).

* Quadratic majorants (`quadMaj_AA`, `quadMaj_AB`): on `{q_A < 1}`, with `T = tr A + tr B`,
  weights `√b_i`, `b_i = A_ii + B_ii`, the prefactors satisfy `QuadMaj` with scales `(p-1)T` and
  `pT`. They follow from `A² ⪯ (tr A) A` (`posSemidef_smul_sub_mul_self`,
  `posSemidef_trace_smul_sub`), i.e. `q_{A²} ≤ tr A · q_A`, `(A²)_ii ≤ tr A · A_ii`, and
  Cauchy–Schwarz for `((AB)x)_i = A[·,i] ⬝ Bx` and `(AB)_ij = A[·,i] ⬝ B[·,j]`.
* A-SMOOTH and A-E5 for both terms (orders `< p - 2`), so `F_σ ∈ C^{4k_*+4}` with
  `|∂^{2j}F_σ| ≤ 2pT (5p)^{2Σj} Π_i b_i^{j_i}`.
* Own-core moments (`trace_sum_moment_le`): `A_ii ≤ a² s² (P_K⁻¹)_ii ≤ (1.01/d)(P_K⁻¹)_ii`, so by
  (M3) (`core_moment`, `1 + 2ε ≤ 3`) and the power mean over `|N| ≤ d`, `E_{ν_K} T^n ≤ 13^n`; hence
  the sup majorant `m = 2pT` has `E_{ν_K} m^n ≤ (26p)^n`.
* `row_rem`: `|E_{ν_K}(𝖦F - Σ_{j ∈ ret} c_j 𝖱∂^{2j}F)| ≤ 26 p e^{-p}/d · F_H`.
-/

@[expose] public section

namespace BiluLinial.Tight

namespace SecC

universe u

open Matrix
open scoped ContDiff

/-! ### Star-level majorants -/

section StarMaj

variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
private theorem symm_of_psd {A : Matrix ι ι ℝ} (hA : A.PosSemidef) (i j : ι) : A i j = A j i := by
  simpa using hA.isHermitian.apply j i

/-- `q_{A²}(x) ≤ tr A · q_A(x)` for `A ⪰ 0` (`A² ⪯ (tr A) A`). -/
theorem qForm_mul_self_le_trace {A : Matrix ι ι ℝ} (hA : A.PosSemidef) (x : ι → ℝ) :
    qForm (A * A) x ≤ A.trace * qForm A x := by
  classical
  have h := (posSemidef_smul_sub_mul_self hA hA.trace_nonneg
    (posSemidef_trace_smul_sub hA)).dotProduct_mulVec_nonneg x
  simp only [star_trivial, sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul,
    smul_eq_mul] at h
  unfold qForm
  linarith

theorem qForm_mul_eq_dot {A B : Matrix ι ι ℝ} (hA : A.PosSemidef) (x : ι → ℝ) :
    qForm (A * B) x = (A *ᵥ x) ⬝ᵥ (B *ᵥ x) := by
  have hAt : x ᵥ* A = A *ᵥ x := by
    rw [← mulVec_transpose]
    congr 1
    ext i j
    exact symm_of_psd hA j i
  unfold qForm
  rw [← mulVec_mulVec, dotProduct_mulVec, hAt]

theorem mulVec_mul_apply_eq {A B : Matrix ι ι ℝ} (hA : A.PosSemidef) (x : ι → ℝ) (i : ι) :
    ((A * B) *ᵥ x) i = ∑ l, A l i * (B *ᵥ x) l := by
  rw [← mulVec_mulVec]
  simp only [mulVec, dotProduct]
  exact Finset.sum_congr rfl fun l _ => by rw [symm_of_psd hA i l]

theorem mul_apply_eq_dot {A B : Matrix ι ι ℝ} (hA : A.PosSemidef) (i j : ι) :
    (A * B) i j = ∑ l, A l i * B l j := by
  rw [mul_apply]
  exact Finset.sum_congr rfl fun l _ => by rw [symm_of_psd hA i l]

theorem mul_self_diag_eq {A : Matrix ι ι ℝ} (hA : A.PosSemidef) (i : ι) :
    (A * A) i i = ∑ l, A l i ^ 2 := by
  rw [mul_apply_eq_dot hA]
  exact Finset.sum_congr rfl fun l _ => by ring

theorem qForm_mul_self_eq {A : Matrix ι ι ℝ} (hA : A.PosSemidef) (x : ι → ℝ) :
    qForm (A * A) x = ∑ l, (A *ᵥ x) l ^ 2 := by
  rw [qForm_mul_eq_dot hA, dotProduct]
  exact Finset.sum_congr rfl fun l _ => by ring

theorem mul_self_diag_le_trace {A : Matrix ι ι ℝ} (hA : A.PosSemidef) (i : ι) :
    (A * A) i i ≤ A.trace * A i i := by
  classical
  have h := qForm_mul_self_le_trace hA (Pi.single i 1)
  have e : ∀ M : Matrix ι ι ℝ, qForm M (Pi.single i 1) = M i i := fun M => by
    simp [qForm, mulVec, dotProduct, Pi.single_apply]
  rwa [e, e] at h

private theorem abs_dot_le_sqrt (f g : ι → ℝ) :
    |∑ l, f l * g l| ≤ Real.sqrt (∑ l, f l ^ 2) * Real.sqrt (∑ l, g l ^ 2) := by
  refine abs_le.mpr ⟨?_, Real.sum_mul_le_sqrt_mul_sqrt _ f g⟩
  have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i => -f i) g
  simp only [neg_mul, Finset.sum_neg_distrib, neg_sq] at h
  linarith

private theorem sqrt_mul_sqrt_le {u w T b : ℝ} (hu : 0 ≤ u) (hT : 0 ≤ T) (hb : 0 ≤ b)
    (hub : u ≤ T * b) (hw : w ≤ T) : Real.sqrt u * Real.sqrt w ≤ T * Real.sqrt b := by
  rw [← Real.sqrt_mul hu]
  calc Real.sqrt (u * w) ≤ Real.sqrt (T ^ 2 * b) := by
        apply Real.sqrt_le_sqrt
        rcases le_total 0 w with hw0 | hw0
        · nlinarith [mul_le_mul hub hw hw0 (by positivity)]
        · nlinarith
    _ = T * Real.sqrt b := by rw [Real.sqrt_mul (sq_nonneg T), Real.sqrt_sq hT]

private theorem sqrt_mul_sqrt_le' {u w T b c : ℝ} (hu : 0 ≤ u) (hw : 0 ≤ w) (hT : 0 ≤ T)
    (hb : 0 ≤ b) (hub : u ≤ T * b) (hwc : w ≤ T * c) :
    Real.sqrt u * Real.sqrt w ≤ T * (Real.sqrt b * Real.sqrt c) := by
  rw [← Real.sqrt_mul hu, ← Real.sqrt_mul hb]
  calc Real.sqrt (u * w) ≤ Real.sqrt (T ^ 2 * (b * c)) := by
        apply Real.sqrt_le_sqrt
        nlinarith [mul_le_mul hub hwc hw (by positivity)]
    _ = T * Real.sqrt (b * c) := by rw [Real.sqrt_mul (sq_nonneg T), Real.sqrt_sq hT]

/-- Generic product bounds: if `(X²)_ii ≤ T b_i`, `(Y²)_jj ≤ T b_j` and `q_{Y²}(x) ≤ T`, then
`|((XY)x)_i| ≤ T √b_i` and `|(XY)_ij| ≤ T √b_i √b_j` (Cauchy–Schwarz). -/
theorem prod_bounds {X Y : Matrix ι ι ℝ} (hX : X.PosSemidef) (hY : Y.PosSemidef) {T : ℝ}
    (hT : 0 ≤ T) {b : ι → ℝ} (hb : ∀ i, 0 ≤ b i) (hXi : ∀ i, (X * X) i i ≤ T * b i)
    (hYi : ∀ i, (Y * Y) i i ≤ T * b i) {x : ι → ℝ} (hYx : qForm (Y * Y) x ≤ T) :
    (∀ i, |((X * Y) *ᵥ x) i| ≤ T * Real.sqrt (b i)) ∧
    (∀ i j, |(X * Y) i j| ≤ T * (Real.sqrt (b i) * Real.sqrt (b j))) := by
  have hXi0 : ∀ i, 0 ≤ (X * X) i i := fun i => by rw [mul_self_diag_eq hX]; positivity
  have hYi0 : ∀ i, 0 ≤ (Y * Y) i i := fun i => by rw [mul_self_diag_eq hY]; positivity
  refine ⟨fun i => ?_, fun i j => ?_⟩
  · rw [mulVec_mul_apply_eq hX]
    refine (abs_dot_le_sqrt _ _).trans ?_
    rw [← mul_self_diag_eq hX, ← qForm_mul_self_eq hY]
    exact sqrt_mul_sqrt_le (hXi0 i) hT (hb i) (hXi i) hYx
  · rw [mul_apply_eq_dot hX]
    refine (abs_dot_le_sqrt _ _).trans ?_
    rw [← mul_self_diag_eq hX, ← mul_self_diag_eq hY]
    exact sqrt_mul_sqrt_le' (hXi0 i) (hYi0 j) hT (hb i) (hXi i) (hYi j)

/-- The ingredients for `T = tr A + tr B`, `b_i = A_ii + B_ii` on `{q_A ≤ 1, q_B ≤ 1}`. -/
theorem psd_pair_facts {A B : Matrix ι ι ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    {x : ι → ℝ} (hxA : qForm A x ≤ 1) (hxB : qForm B x ≤ 1) :
    0 ≤ A.trace + B.trace ∧ (∀ i, 0 ≤ A i i + B i i) ∧
    (∀ i, (A * A) i i ≤ (A.trace + B.trace) * (A i i + B i i)) ∧
    (∀ i, (B * B) i i ≤ (A.trace + B.trace) * (A i i + B i i)) ∧
    qForm (A * A) x ≤ A.trace + B.trace ∧ qForm (B * B) x ≤ A.trace + B.trace := by
  have htA := hA.trace_nonneg
  have htB := hB.trace_nonneg
  have hqA : 0 ≤ qForm A x := by simpa [qForm] using hA.dotProduct_mulVec_nonneg x
  have hqB : 0 ≤ qForm B x := by simpa [qForm] using hB.dotProduct_mulVec_nonneg x
  refine ⟨add_nonneg htA htB, fun i => add_nonneg hA.diag_nonneg hB.diag_nonneg,
    fun i => ?_, fun i => ?_, ?_, ?_⟩
  · have := mul_self_diag_le_trace hA i
    have := hA.diag_nonneg (i := i)
    have := hB.diag_nonneg (i := i)
    nlinarith
  · have := mul_self_diag_le_trace hB i
    have := hA.diag_nonneg (i := i)
    have := hB.diag_nonneg (i := i)
    nlinarith
  · have := qForm_mul_self_le_trace hA x
    nlinarith
  · have := qForm_mul_self_le_trace hB x
    nlinarith

theorem transpose_mul_psd {A B : Matrix ι ι ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (A * B)ᵀ = B * A := by
  rw [transpose_mul]
  congr 1 <;> ext i j
  · exact symm_of_psd hB j i
  · exact symm_of_psd hA j i

/-- `QuadMaj` for `c q_{XY}` (`(X, Y) = (A, A)` or `(A, B)`), scale `c (tr A + tr B)`, weights
`√(A_ii + B_ii)`. -/
theorem quadMaj_prod {A B X Y : Matrix ι ι ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hX : X.PosSemidef) (hY : Y.PosSemidef)
    (hXY : (X = A ∧ Y = A) ∨ (X = A ∧ Y = B)) {c : ℝ} (hc : 0 ≤ c) {x : ι → ℝ}
    (hxA : qForm A x ≤ 1) (hxB : qForm B x ≤ 1) :
    QuadMaj 0 0 (c • (X * Y)) x (c * (A.trace + B.trace))
      (fun i => Real.sqrt (A i i + B i i)) := by
  obtain ⟨hT, hb, hAi, hBi, hAx, hBx⟩ := psd_pair_facts hA hB hxA hxB
  have hXi : ∀ i, (X * X) i i ≤ (A.trace + B.trace) * (A i i + B i i) := by
    rcases hXY with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact hAi
  have hYi : ∀ i, (Y * Y) i i ≤ (A.trace + B.trace) * (A i i + B i i) := by
    rcases hXY with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hAi
    · exact hBi
  have hXx : qForm (X * X) x ≤ A.trace + B.trace := by
    rcases hXY with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact hAx
  have hYx : qForm (Y * Y) x ≤ A.trace + B.trace := by
    rcases hXY with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hAx
    · exact hBx
  obtain ⟨h1, h2⟩ := prod_bounds hX hY hT hb hXi hYi hYx
  obtain ⟨h1', h2'⟩ := prod_bounds hY hX hT hb hYi hXi hXx
  have hq : |qForm (X * Y) x| ≤ A.trace + B.trace := by
    rw [qForm_mul_eq_dot hX, dotProduct]
    refine (abs_dot_le_sqrt _ _).trans ?_
    rw [← qForm_mul_self_eq hX, ← qForm_mul_self_eq hY]
    calc Real.sqrt (qForm (X * X) x) * Real.sqrt (qForm (Y * Y) x)
        ≤ Real.sqrt (A.trace + B.trace) * Real.sqrt (A.trace + B.trace) :=
          mul_le_mul (Real.sqrt_le_sqrt hXx) (Real.sqrt_le_sqrt hYx) (Real.sqrt_nonneg _)
            (Real.sqrt_nonneg _)
      _ = A.trace + B.trace := Real.mul_self_sqrt hT
  refine ⟨?_, fun i => ?_, fun i j => ?_⟩
  · simp only [quadFn, zero_add, zero_dotProduct, qForm, smul_mulVec, dotProduct_smul,
      smul_eq_mul]
    rw [abs_mul, abs_of_nonneg hc]
    exact mul_le_mul_of_nonneg_left (by simpa [qForm] using hq) hc
  · rw [transpose_smul, transpose_mul_psd hX hY]
    simp only [Pi.zero_apply, zero_add, add_mulVec, smul_mulVec, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
    rw [← mul_add]
    rw [abs_mul, abs_of_nonneg hc]
    have := abs_add_le (((X * Y) *ᵥ x) i) (((Y * X) *ᵥ x) i)
    have := h1 i
    have := h1' i
    have hs := Real.sqrt_nonneg (A i i + B i i)
    nlinarith
  · simp only [Matrix.smul_apply, smul_eq_mul]
    rw [← mul_add, abs_mul, abs_of_nonneg hc]
    have := abs_add_le ((X * Y) i j) ((X * Y) j i)
    have := h2 i j
    have := h2 j i
    have hs := mul_nonneg (Real.sqrt_nonneg (A i i + B i i)) (Real.sqrt_nonneg (A j j + B j j))
    nlinarith

variable [DecidableEq ι]

theorem smoothBdd_add' {N : ℕ} {f g : (ι → ℝ) → ℝ} (hf : SmoothBdd N f) (hg : SmoothBdd N g) :
    SmoothBdd N (f + g) := by
  refine ⟨hf.1.add hg.1, fun l hl => ?_⟩
  obtain ⟨Cf, hCf⟩ := hf.2 l hl
  obtain ⟨Cg, hCg⟩ := hg.2 l hl
  refine ⟨Cf + Cg, fun x => ?_⟩
  rw [pderivList_add l (hf.1.of_le (by exact_mod_cast hl)) (hg.1.of_le (by exact_mod_cast hl)),
    Pi.add_apply]
  exact (abs_add_le _ _).trans (add_le_add (hCf x) (hCg x))

omit [DecidableEq ι] in
/-- The `QuadMaj` hypotheses of A-E5 for the two prefactors of `rowNum`. -/
theorem quadMaj_rowNum {A B : Matrix ι ι ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef) {p : ℕ}
    (hp : 1 ≤ p) :
    (∀ x, qForm A x < 1 → qForm B x < 1 →
      QuadMaj 0 0 (((p : ℝ) - 1) • (A * A)) x (((p : ℝ) - 1) * (A.trace + B.trace))
        fun i => Real.sqrt (A i i + B i i)) ∧
    (∀ x, qForm A x < 1 → qForm B x < 1 →
      QuadMaj 0 0 ((p : ℝ) • (A * B)) x ((p : ℝ) * (A.trace + B.trace))
        fun i => Real.sqrt (A i i + B i i)) := by
  have hp1 : (0 : ℝ) ≤ (p : ℝ) - 1 := by
    have : (1 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  exact ⟨fun x hxA hxB => quadMaj_prod hA hB hA hA (Or.inl ⟨rfl, rfl⟩) hp1 hxA.le hxB.le,
    fun x hxA hxB => quadMaj_prod hA hB hA hB (Or.inr ⟨rfl, rfl⟩) (Nat.cast_nonneg p) hxA.le
      hxB.le⟩

/-- A-SMOOTH for `rowNum`. -/
theorem smoothBdd_rowNum {A B : Matrix ι ι ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef) {p n : ℕ}
    (hn : n + 3 ≤ p) : SmoothBdd n (rowNum p A B) := by
  obtain ⟨h1, h2⟩ := quadMaj_rowNum hA hB (p := p) (by omega)
  rw [rowNum_eq_clipObs]
  exact smoothBdd_add' (SecA.smoothBdd_clipObs (e₁ := p - 2) (e₂ := p) hA hB h1 (by omega))
    (SecA.smoothBdd_clipObs (e₁ := p - 1) (e₂ := p - 1) hA hB h2 (by omega))

/-- A-E5 for `rowNum`: `|∂^l F(x)| ≤ 2p(tr A + tr B) (5p)^{|l|} Π_{i ∈ l} √(A_ii + B_ii)`. -/
theorem pderivList_rowNum_le {A B : Matrix ι ι ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    {p : ℕ} (l : List ι) (hl : l.length + 3 ≤ p) (x : ι → ℝ) :
    |pderivList l (rowNum p A B) x| ≤
      2 * p * (A.trace + B.trace) * (5 * (p : ℝ)) ^ l.length *
        (l.map fun i => Real.sqrt (A i i + B i i)).prod := by
  obtain ⟨h1, h2⟩ := quadMaj_rowNum hA hB (p := p) (by omega)
  have hg1 : ContDiff ℝ ∞ (quadFn 0 0 (((p : ℝ) - 1) • (A * A))) := by
    rw [quadFn_zero_zero]; exact contDiff_qForm' _
  have hg2 : ContDiff ℝ ∞ (quadFn 0 0 ((p : ℝ) • (A * B))) := by
    rw [quadFn_zero_zero]; exact contDiff_qForm' _
  have hc1 := SecA.contDiff_clipObs hg1 (p - 2) p A B
  have hc2 := SecA.contDiff_clipObs hg2 (p - 1) (p - 1) A B
  have hm1 : l.length ≤ min (p - 2) p - 1 := by omega
  have hm2 : l.length ≤ min (p - 1) (p - 1) - 1 := by omega
  rw [rowNum_eq_clipObs, pderivList_add l (hc1.of_le (by exact_mod_cast hm1))
    (hc2.of_le (by exact_mod_cast hm2)), Pi.add_apply]
  have e1 := SecA.pderivList_clipObs_le (e₁ := p - 2) (e₂ := p) hA hB h1 l (by omega) x
  have e2 := SecA.pderivList_clipObs_le (e₁ := p - 1) (e₂ := p - 1) hA hB h2 l (by omega) x
  have hT : 0 ≤ A.trace + B.trace := add_nonneg hA.trace_nonneg hB.trace_nonneg
  have hP : 0 ≤ (l.map fun i => Real.sqrt (A i i + B i i)).prod :=
    List.prod_nonneg fun y hy => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hy
      exact Real.sqrt_nonneg _
  have hp1 : (2 : ℝ) ≤ p := by exact_mod_cast (by omega : 2 ≤ p)
  have hb1 : 2 * (1 + ((p - 2 : ℕ) : ℝ) + (p : ℝ)) ≤ 5 * p := by
    have : ((p - 2 : ℕ) : ℝ) ≤ p := by exact_mod_cast Nat.sub_le p 2
    linarith
  have hb2 : 2 * (1 + ((p - 1 : ℕ) : ℝ) + ((p - 1 : ℕ) : ℝ)) ≤ 5 * p := by
    have : ((p - 1 : ℕ) : ℝ) = p - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    rw [this]
    linarith
  have hk1 := pow_le_pow_left₀ (by positivity) hb1 l.length
  have hk2 := pow_le_pow_left₀ (by positivity) hb2 l.length
  have hm1' : 0 ≤ ((p : ℝ) - 1) * (A.trace + B.trace) := mul_nonneg (by linarith) hT
  have hm2' : 0 ≤ (p : ℝ) * (A.trace + B.trace) := by positivity
  calc |pderivList l (clipObs (quadFn 0 0 (((p : ℝ) - 1) • (A * A))) (p - 2) p A B) x +
        pderivList l (clipObs (quadFn 0 0 ((p : ℝ) • (A * B))) (p - 1) (p - 1) A B) x|
      ≤ |pderivList l (clipObs (quadFn 0 0 (((p : ℝ) - 1) • (A * A))) (p - 2) p A B) x| +
        |pderivList l (clipObs (quadFn 0 0 ((p : ℝ) • (A * B))) (p - 1) (p - 1) A B) x| :=
        abs_add_le _ _
    _ ≤ ((p : ℝ) - 1) * (A.trace + B.trace) * (5 * (p : ℝ)) ^ l.length *
          (l.map fun i => Real.sqrt (A i i + B i i)).prod +
        (p : ℝ) * (A.trace + B.trace) * (5 * (p : ℝ)) ^ l.length *
          (l.map fun i => Real.sqrt (A i i + B i i)).prod := by
        refine add_le_add (e1.trans ?_) (e2.trans ?_)
        · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk1 hm1') hP
        · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk2 hm2') hP
    _ ≤ _ := by
        have h5 : 0 ≤ (5 * (p : ℝ)) ^ l.length := by positivity
        have := mul_nonneg (mul_nonneg hT h5) hP
        nlinarith

omit [Fintype ι] [DecidableEq ι] in
theorem prod_map_dEvenList_aux (l : List ι) (j : ι → ℕ) (f : ι → ℝ) :
    ((dEvenList l j).map f).prod = (l.map fun x => f x ^ (2 * j x)).prod := by
  induction l with
  | nil => simp [dEvenList]
  | cons y l ih =>
    simp only [dEvenList, List.flatMap_cons, List.map_append, List.prod_append,
      List.map_replicate, List.prod_replicate, List.map_cons, List.prod_cons] at ih ⊢
    rw [ih]

omit [DecidableEq ι] in
theorem prod_map_dEvenList_univ_aux (j : ι → ℕ) (f : ι → ℝ) :
    ((dEvenList (Finset.univ : Finset ι).toList j).map f).prod = ∏ i, f i ^ (2 * j i) := by
  rw [prod_map_dEvenList_aux]
  exact Finset.prod_map_toList _ (fun i => f i ^ (2 * j i))

end StarMaj

/-! ### Own-core moments of the sup majorant -/

section Moment

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable {d p : ℕ}

theorem coreE_finset_sum {a : ℝ} {yp ym : V → ℝ} {S : Finset V} {v : V} {ι : Type*}
    (s : Finset ι) (f : ι → Config V → ℝ) :
    coreE G p a yp ym S v (fun σ => ∑ l ∈ s, f l σ) = ∑ l ∈ s, coreE G p a yp ym S v (f l) := by
  unfold coreE
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm, Finset.sum_div]

/-- On the core support, `A_ii ≤ (1.01/d) (P_K⁻¹)_ii` (`y ≤ s`, `D_v ≥ 1`, `a²s² ≤ 1.01/d`). -/
theorem rootMat_diag_le_core (hR : TRegime d p) {S : Finset V} {τ : ℝ} {y : V → ℝ}
    (hy : InCube (sOf d p) y) {v : V} {σ : Config V}
    (hPc : (precCore G (aOf d p) τ y σ S v).PosDef) (i : nbhd G S v) :
    rootMat G (aOf d p) τ y σ S v i i ≤
      101 / 100 / d * (precCore G (aOf d p) τ y σ S v)⁻¹ i i := by
  have hy0 : ∀ j, 0 ≤ y j := fun j => (hy j).1
  have hD := one_le_diagD G (aOf d p) hy0 S v
  have hc : 0 ≤ (precCore G (aOf d p) τ y σ S v)⁻¹ i i := hPc.inv.diag_pos.le
  have hdR := hR.ten_pow_six_le_d
  have hd0 : (0 : ℝ) < d := lt_of_lt_of_le (by norm_num) hdR
  have hκ := hR.d_mul_kappa_le
  have hs := hR.sOf_pos
  have e : rootMat G (aOf d p) τ y σ S v i i = aOf d p ^ 2 * y v / diagD G (aOf d p) y S v *
      (y i * (precCore G (aOf d p) τ y σ S v)⁻¹ i i) := by
    simp only [rootMat, Matrix.of_apply, coreGreen]
    have h : Real.sqrt (y i) * (precCore G (aOf d p) τ y σ S v)⁻¹ i i * Real.sqrt (y i) =
        y i * (precCore G (aOf d p) τ y σ S v)⁻¹ i i := by
      rw [mul_comm (Real.sqrt (y i)) _, mul_assoc, Real.mul_self_sqrt (hy0 i), mul_comm]
    rw [h]
  rw [e]
  have h1 : aOf d p ^ 2 * y v / diagD G (aOf d p) y S v ≤ aOf d p ^ 2 * sOf d p := by
    rw [div_le_iff₀ (by linarith)]
    have h1 := mul_le_mul_of_nonneg_left (hy v).2 (sq_nonneg (aOf d p))
    have h2 := mul_le_mul_of_nonneg_left hD (by positivity : (0 : ℝ) ≤ aOf d p ^ 2 * sOf d p)
    linarith
  have h2 : y i * (precCore G (aOf d p) τ y σ S v)⁻¹ i i ≤
      sOf d p * (precCore G (aOf d p) τ y σ S v)⁻¹ i i :=
    mul_le_mul_of_nonneg_right (hy i).2 hc
  have h3 : aOf d p ^ 2 * sOf d p ^ 2 ≤ 101 / 100 / d := by
    rw [le_div_iff₀ hd0]; linarith
  calc aOf d p ^ 2 * y v / diagD G (aOf d p) y S v * (y i * (precCore G (aOf d p) τ y σ S v)⁻¹ i i)
      ≤ aOf d p ^ 2 * sOf d p * (sOf d p * (precCore G (aOf d p) τ y σ S v)⁻¹ i i) :=
        mul_le_mul h1 h2 (mul_nonneg (hy0 i) hc) (by positivity)
    _ = aOf d p ^ 2 * sOf d p ^ 2 * (precCore G (aOf d p) τ y σ S v)⁻¹ i i := by ring
    _ ≤ 101 / 100 / d * (precCore G (aOf d p) τ y σ S v)⁻¹ i i :=
        mul_le_mul_of_nonneg_right h3 hc

/-- **Own-core moments** of `m = 2p (tr A + tr B)` on the core support: `E_{ν_K} m^n ≤ (26p)^n`. -/
theorem rowRem_moment (hRA : RegA d p) {S : Finset V} {lam : ℝ} (hC : CapCtx G d p S lam)
    {yp ym : V → ℝ} (hyp : InCube (lam * sOf d p) yp) (hym : InCube (lam * sOf d p) ym) {v : V}
    (hv : v ∈ S) {n : ℕ} (hn1 : 1 ≤ n) (hn : 2 * n ≤ p) :
    coreE G p (aOf d p) yp ym S v (fun σ =>
        (if wtCore G p (aOf d p) yp ym σ S v ≠ 0 then
          2 * p * ((rootMat G (aOf d p) 1 yp σ S v).trace +
            (rootMat G (aOf d p) (-1) ym σ S v).trace) else 0) ^ n) ≤ (26 * p) ^ n := by
  classical
  have hR := hRA.treg
  have hdR := hR.ten_pow_six_le_d
  have hd0 : (0 : ℝ) < d := lt_of_lt_of_le (by norm_num) hdR
  have hyp' := inCube_of_cap G hR hC hyp
  have hym' := inCube_of_cap G hR hC hym
  have hcard : ((Finset.univ : Finset (nbhd G S v)).card : ℝ) ≤ d := by
    rw [Finset.card_univ]
    exact_mod_cast card_nbhd_le G hC.deg S v
  have hε0 := SecA.epsP_nonneg hR
  have hε3 : 1 + 2 * epsP d p ≤ 3 := by
    have := hRA.epsP_le_u
    have := hRA.uOf_le_one
    linarith
  let cp : CapPoint.{_} d p :=
    { V := V, G := G, S := S, lam := lam, yp := yp, ym := ym, ctx := hC, hyp := hyp, hym := hym }
  have hvS : v ∈ cp.S := hv
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  set N := (Finset.univ : Finset (nbhd G S v)).card with hNdef
  set cP : Config V → nbhd G S v → ℝ := fun σ i => (precCore G (aOf d p) 1 yp σ S v)⁻¹ i i
    with hcP
  set cM : Config V → nbhd G S v → ℝ := fun σ i => (precCore G (aOf d p) (-1) ym σ S v)⁻¹ i i
    with hcM
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = 2 * p * (101 / 100 / d) := ⟨_, rfl⟩
  have hκ0 : 0 ≤ κ := by rw [hκ]; positivity
  have hpt : ∀ σ, wtCore G p (aOf d p) yp ym σ S v ≠ 0 →
      (if wtCore G p (aOf d p) yp ym σ S v ≠ 0 then
          2 * p * ((rootMat G (aOf d p) 1 yp σ S v).trace +
            (rootMat G (aOf d p) (-1) ym σ S v).trace) else 0) ^ (m + 1) ≤
        κ ^ (m + 1) * ((N : ℝ) ^ m *
          ∑ i : nbhd G S v, (2 ^ (m + 1) * (cP σ i ^ (m + 1) + cM σ i ^ (m + 1)))) := by
    intro σ hσ
    rw [ite_eq_left_of_eq_true _ _ (eq_true hσ)]
    obtain ⟨h1, h2⟩ := posDef_of_wtCore_ne_zero G hσ
    have hc1 : ∀ i, 0 ≤ cP σ i := fun i => h1.inv.diag_pos.le
    have hc2 : ∀ i, 0 ≤ cM σ i := fun i => h2.inv.diag_pos.le
    have hA := (shift_branch G (fun j => (hyp j).1) le_rfl one_pos h1).1
    have hB := (shift_branch G (fun j => (hym j).1) le_rfl one_pos h2).1
    have hT : (rootMat G (aOf d p) 1 yp σ S v).trace + (rootMat G (aOf d p) (-1) ym σ S v).trace ≤
        101 / 100 / d * ∑ i : nbhd G S v, (cP σ i + cM σ i) := by
      rw [Finset.mul_sum, Matrix.trace, Matrix.trace, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun i _ => ?_
      have := rootMat_diag_le_core G hR hyp' h1 i
      have := rootMat_diag_le_core G hR hym' h2 i
      simp only [Matrix.diag_apply, hcP, hcM]
      linarith
    have hT0 : 0 ≤ (rootMat G (aOf d p) 1 yp σ S v).trace +
        (rootMat G (aOf d p) (-1) ym σ S v).trace := add_nonneg hA.trace_nonneg hB.trace_nonneg
    have hs0 : 0 ≤ ∑ i : nbhd G S v, (cP σ i + cM σ i) :=
      Finset.sum_nonneg fun i _ => add_nonneg (hc1 i) (hc2 i)
    have hpow : (∑ i : nbhd G S v, (cP σ i + cM σ i)) ^ (m + 1) ≤
        (N : ℝ) ^ m * ∑ i : nbhd G S v, (2 ^ (m + 1) * (cP σ i ^ (m + 1) + cM σ i ^ (m + 1))) := by
      refine (pow_sum_le_card_mul_sum_pow (fun i _ => add_nonneg (hc1 i) (hc2 i)) m).trans ?_
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ =>
        add_pow_le_two_pow_mul (hc1 i) (hc2 i) _) (by positivity)
    have hmT : 2 * p * ((rootMat G (aOf d p) 1 yp σ S v).trace +
        (rootMat G (aOf d p) (-1) ym σ S v).trace) ≤ κ * ∑ i : nbhd G S v, (cP σ i + cM σ i) := by
      have := mul_le_mul_of_nonneg_left hT (by positivity : (0 : ℝ) ≤ 2 * p)
      calc _ ≤ 2 * p * (101 / 100 / d * ∑ i : nbhd G S v, (cP σ i + cM σ i)) := this
        _ = κ * ∑ i : nbhd G S v, (cP σ i + cM σ i) := by rw [hκ]; ring
    calc (2 * p * ((rootMat G (aOf d p) 1 yp σ S v).trace +
          (rootMat G (aOf d p) (-1) ym σ S v).trace)) ^ (m + 1)
        ≤ (κ * ∑ i : nbhd G S v, (cP σ i + cM σ i)) ^ (m + 1) :=
          pow_le_pow_left₀ (by positivity) hmT _
      _ = κ ^ (m + 1) * (∑ i : nbhd G S v, (cP σ i + cM σ i)) ^ (m + 1) := mul_pow _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)
  have hmom : ∀ i : nbhd G S v,
      coreE G p (aOf d p) yp ym S v (fun σ => cP σ i ^ (m + 1) + cM σ i ^ (m + 1)) ≤
        2 * 3 ^ (m + 1) := by
    intro i
    obtain ⟨h1, h2⟩ := cp.core_moment hRA hvS (i : V) hn1 hn
    have e1 : (1 + 2 * epsP d p) ^ (m + 1) ≤ 3 ^ (m + 1) := pow_le_pow_left₀ (by linarith) hε3 _
    rw [coreE_add]
    have h1' : coreE G p (aOf d p) yp ym S v (fun σ => cP σ i ^ (m + 1)) ≤
        (1 + 2 * epsP d p) ^ (m + 1) := h1
    have h2' : coreE G p (aOf d p) yp ym S v (fun σ => cM σ i ^ (m + 1)) ≤
        (1 + 2 * epsP d p) ^ (m + 1) := h2
    linarith
  have hκN : κ * N * 6 ≤ 1212 / 100 * p := by
    have h1 : κ * N = 2 * p * (101 / 100) * (N / d) := by rw [hκ]; ring
    have h2 : (N : ℝ) / d ≤ 1 := by rw [div_le_one hd0]; exact hcard
    have h3 : 0 ≤ 2 * (p : ℝ) * (101 / 100) := by positivity
    rw [h1]
    nlinarith [mul_le_mul_of_nonneg_left h2 h3]
  calc _ ≤ coreE G p (aOf d p) yp ym S v (fun σ => κ ^ (m + 1) * ((N : ℝ) ^ m *
        ∑ i : nbhd G S v, (2 ^ (m + 1) * (cP σ i ^ (m + 1) + cM σ i ^ (m + 1))))) :=
        coreE_mono G hpt
    _ = κ ^ (m + 1) * ((N : ℝ) ^ m * ∑ i : nbhd G S v, (2 ^ (m + 1) *
          coreE G p (aOf d p) yp ym S v (fun σ => cP σ i ^ (m + 1) + cM σ i ^ (m + 1)))) := by
        rw [coreE_const_mul, coreE_const_mul, coreE_finset_sum]
        congr 2
        exact Finset.sum_congr rfl fun i _ => coreE_const_mul G _ _
    _ ≤ κ ^ (m + 1) * ((N : ℝ) ^ m * ∑ _i : nbhd G S v, (2 ^ (m + 1) * (2 * 3 ^ (m + 1)))) := by
        gcongr with i
        exact hmom i
    _ = 2 * (κ * N * 6) ^ (m + 1) := by
        have e6 : (κ * N * 6) ^ (m + 1) = κ ^ (m + 1) * (N : ℝ) ^ (m + 1) *
            (2 ^ (m + 1) * 3 ^ (m + 1)) := by
          rw [mul_pow, mul_pow, show (6 : ℝ) = 2 * 3 by norm_num, mul_pow]
        rw [Finset.sum_const, nsmul_eq_mul, ← hNdef, e6, pow_succ (N : ℝ) m]
        ring
    _ ≤ 2 * (1212 / 100 * p) ^ (m + 1) := by
        gcongr
    _ ≤ (26 * p) ^ (m + 1) := by
        have e : (26 * (p : ℝ)) ^ (m + 1) =
            (26 / (1212 / 100)) ^ (m + 1) * (1212 / 100 * p) ^ (m + 1) := by
          rw [← mul_pow]; congr 1; ring
        rw [e]
        have h3 : (2 : ℝ) ≤ (26 / (1212 / 100)) ^ (m + 1) :=
          le_trans (by norm_num) (le_self_pow₀ (by norm_num) (by omega))
        exact mul_le_mul_of_nonneg_right h3 (by positivity)

end Moment

/-- **CR-REM** (A-REM for `F = rowNum`, source lines 1153–1162). See the module docstring. -/
theorem row_rem : ∃ C : ℝ, 0 < C ∧ Eventually fun _ _ d p _ =>
    ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
      (S : Finset V) (lam : ℝ) (yp ym : V → ℝ) (v : V), CapCtx G d p S lam →
      InCube (lam * sOf d p) yp → InCube (lam * sOf d p) ym → v ∈ S →
      |coreE G p (aOf d p) yp ym S v (fun σ =>
          gaussE (rowNum p (rootMat G (aOf d p) 1 yp σ S v) (rootMat G (aOf d p) (-1) ym σ S v)) -
          ∑ j ∈ (retIdx (kStar d p) : Finset (nbhd G S v → ℕ)), ecoefM j *
            radE (dEven (Finset.univ : Finset (nbhd G S v)).toList j
              (rowNum p (rootMat G (aOf d p) 1 yp σ S v) (rootMat G (aOf d p) (-1) ym σ S v))))| ≤
        C * p * Real.exp (-(p : ℝ)) / d * insFH G d p yp ym S v := by
  refine ⟨26, by norm_num, SecA.eventually_regA.mono ?_⟩
  rintro c₀ κ₀ d p h hRA V _ _ G _ S lam yp ym v hC hyp hym hv
  classical
  have hR : TRegime d p := hRA.treg
  have hk := hRA.moment_order_le
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (le_trans (by norm_num) hR.two_le_p : 1 ≤ p)
  let cp : CapPoint.{u} d p :=
    { V := V, G := G, S := S, lam := lam, yp := yp, ym := ym, ctx := hC, hyp := hyp, hym := hym }
  have hvS : v ∈ cp.S := hv
  have hPSD : ∀ σ, wtCore G p (aOf d p) yp ym σ S v ≠ 0 →
      (rootMat G (aOf d p) 1 yp σ S v).PosSemidef ∧
        (rootMat G (aOf d p) (-1) ym σ S v).PosSemidef := by
    intro σ hσ
    obtain ⟨h1, h2⟩ := posDef_of_wtCore_ne_zero G hσ
    exact ⟨(shift_branch G (fun j => (hyp j).1) le_rfl one_pos h1).1,
      (shift_branch G (fun j => (hym j).1) le_rfl one_pos h2).1⟩
  set F : Config V → (nbhd G S v → ℝ) → ℝ := fun σ =>
    if wtCore G p (aOf d p) yp ym σ S v ≠ 0 then
      rowNum p (rootMat G (aOf d p) 1 yp σ S v) (rootMat G (aOf d p) (-1) ym σ S v)
    else fun _ => 0 with hF
  set mσ : Config V → ℝ := fun σ =>
    if wtCore G p (aOf d p) yp ym σ S v ≠ 0 then
      2 * p * ((rootMat G (aOf d p) 1 yp σ S v).trace +
        (rootMat G (aOf d p) (-1) ym σ S v).trace) else 0 with hmσ
  have hFs : ∀ σ, wtCore G p (aOf d p) yp ym σ S v ≠ 0 → F σ =
      rowNum p (rootMat G (aOf d p) 1 yp σ S v) (rootMat G (aOf d p) (-1) ym σ S v) :=
    fun σ hσ => by rw [hF]; simp [hσ]
  have hFn : ∀ σ, ¬ wtCore G p (aOf d p) yp ym σ S v ≠ 0 → F σ = fun _ => 0 :=
    fun σ hσ => by rw [hF]; simp only [ne_eq, not_not] at hσ; simp [hσ]
  have hm0 : ∀ σ, 0 ≤ mσ σ := by
    intro σ
    simp only [hmσ]
    split_ifs with hσ
    · obtain ⟨hA, hB⟩ := hPSD σ hσ
      exact mul_nonneg (by positivity) (add_nonneg hA.trace_nonneg hB.trace_nonneg)
    · exact le_rfl
  have hM : (0 : ℝ) < 26 * p := by positivity
  have hmom : ∀ n : ℕ, 1 ≤ n → 2 * n ≤ p → cp.coreE v (fun σ => mσ σ ^ n) ≤ (26 * p) ^ n :=
    fun n hn1 hn => rowRem_moment G hRA hC hyp hym hv hn1 hn
  have hord : 4 * kStarA d p + 4 + 3 ≤ p := by omega
  have hsm : ∀ σ, SmoothBdd (4 * kStarA d p + 4) (F σ) := by
    intro σ
    by_cases hσ : wtCore G p (aOf d p) yp ym σ S v ≠ 0
    · rw [hFs σ hσ]
      obtain ⟨hA, hB⟩ := hPSD σ hσ
      exact smoothBdd_rowNum hA hB hord
    · rw [hFn σ hσ]
      exact ⟨contDiff_const, fun l _ => ⟨0, fun x => by rw [pderivList_zero_fun]; simp⟩⟩
  have hder : ∀ σ, ∀ j ∈ (topIdx (kStarA d p) : Finset (nbhd G S v → ℕ)), ∀ x,
      |dEven (Finset.univ : Finset (nbhd G S v)).toList j (F σ) x| ≤
        mσ σ * (5 * (p : ℝ)) ^ (2 * ∑ i, j i) * ∏ i, (rootMat G (aOf d p) 1 yp σ S v i i +
          rootMat G (aOf d p) (-1) ym σ S v i i) ^ j i := by
    intro σ j hj x
    obtain ⟨hadm, hgr⟩ := mem_topIdx.1 hj
    have hsum := sum_le_two_mul_grade_aux hadm
    by_cases hσ : wtCore G p (aOf d p) yp ym σ S v ≠ 0
    · obtain ⟨hA, hB⟩ := hPSD σ hσ
      have hlen : (dEvenList (Finset.univ : Finset (nbhd G S v)).toList j).length =
          2 * ∑ i, j i := length_dEvenList_univ_aux j
      have h5 := pderivList_rowNum_le (p := p) hA hB
        (dEvenList (Finset.univ : Finset (nbhd G S v)).toList j) (by rw [hlen]; omega) x
      rw [hlen] at h5
      simp only [prod_map_dEvenList_univ_aux] at h5
      have hprod : ∏ i, Real.sqrt (rootMat G (aOf d p) 1 yp σ S v i i +
            rootMat G (aOf d p) (-1) ym σ S v i i) ^ (2 * j i) =
          ∏ i, (rootMat G (aOf d p) 1 yp σ S v i i + rootMat G (aOf d p) (-1) ym σ S v i i) ^ j i :=
        Finset.prod_congr rfl fun i _ => by
          rw [pow_mul, Real.sq_sqrt (add_nonneg hA.diag_nonneg hB.diag_nonneg)]
      rw [hprod] at h5
      have hmσ' : mσ σ = 2 * p * ((rootMat G (aOf d p) 1 yp σ S v).trace +
          (rootMat G (aOf d p) (-1) ym σ S v).trace) := by simp only [hmσ]; simp [hσ]
      rw [hFs σ hσ, dEven_eq_pderivList, hmσ']
      exact h5
    · have hmσ' : mσ σ = 0 := by
        simp only [hmσ]; simp only [ne_eq, not_not] at hσ; simp [hσ]
      rw [hFn σ hσ, dEven_eq_pderivList, pderivList_zero_fun, hmσ']
      simp
  have hrem := cp.trans_rem hRA hvS F mσ hm0 hM hmom hsm hder
  have hL : coreE G p (aOf d p) yp ym S v (fun σ =>
        gaussE (rowNum p (rootMat G (aOf d p) 1 yp σ S v) (rootMat G (aOf d p) (-1) ym σ S v)) -
        ∑ j ∈ (retIdx (kStar d p) : Finset (nbhd G S v → ℕ)), ecoefM j *
          radE (dEven (Finset.univ : Finset (nbhd G S v)).toList j
            (rowNum p (rootMat G (aOf d p) 1 yp σ S v) (rootMat G (aOf d p) (-1) ym σ S v)))) =
      cp.coreE v (fun σ => gaussE (F σ) -
        ∑ j ∈ (retIdx (kStarA d p) : Finset (cp.N v → ℕ)),
          ecoefM j * radE (dEven (cp.lN v) j (F σ))) :=
    SecA.coreE_congr_of_supp G fun σ hσ => by rw [hFs σ hσ]; rfl
  rw [hL]
  exact hrem

end SecC

end BiluLinial.Tight
