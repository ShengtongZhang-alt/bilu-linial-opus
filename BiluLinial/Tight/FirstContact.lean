/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.Defs

/-!
# The first-contact argument

Blueprint node `D-first-contact` (source Section 1.1, last paragraph: "The induction uses a cube
expanding from zero … A first contact supplies (F2)–(F3) … Ruling out that contact therefore
completes the graph-order induction").

Abstract form: finitely many functions `f_j`, continuous on the cube `[0, s]^ι × [0, s]^ι`, at most
`r` at the origin, such that whenever all of them are at most `r` on the cube of side `t s`
(`0 ≤ t ≤ 1`) they are strictly below `r` there. Then they are at most `r` on the whole cube.
Proof: the set of good `t` is a closed initial segment of `[0, 1]` containing `0`; at its supremum
`t* < 1` the strict inequality on the compact cube and uniform continuity extend it beyond `t*`.
-/

@[expose] public section

namespace BiluLinial.Tight

open Set Filter Topology

private lemma inCube_mono {ι : Type*} {s t : ℝ} (hst : s ≤ t) {y : ι → ℝ} (hy : InCube s y) :
    InCube t y := fun i => ⟨(hy i).1, (hy i).2.trans hst⟩

private lemma inCube_smul {ι : Type*} {s t : ℝ} (ht : 0 ≤ t) {y : ι → ℝ} (hy : InCube s y) :
    InCube (t * s) (t • y) := fun i => by
  rw [Pi.smul_apply, smul_eq_mul]
  exact ⟨mul_nonneg ht (hy i).1, mul_le_mul_of_nonneg_left (hy i).2 ht⟩

private lemma inCube_exists_smul {ι : Type*} {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) {y : ι → ℝ}
    (hy : InCube (t * s) y) : ∃ z, InCube s z ∧ t • z = y := by
  rcases ht.eq_or_lt with rfl | ht
  · refine ⟨0, fun _ => ⟨le_rfl, hs⟩, funext fun i => ?_⟩
    have h := hy i
    rw [zero_mul] at h
    simp only [smul_zero, Pi.zero_apply]
    linarith [h.1, h.2]
  · refine ⟨t⁻¹ • y, fun i => ?_, smul_inv_smul₀ ht.ne' y⟩
    rw [Pi.smul_apply, smul_eq_mul]
    exact ⟨mul_nonneg (inv_nonneg.2 ht.le) (hy i).1, (inv_mul_le_iff₀ ht).2 (hy i).2⟩

private lemma inCube_iff_mem_Icc {ι : Type*} (s : ℝ) (y : ι → ℝ) :
    InCube s y ↔ y ∈ Icc (0 : ι → ℝ) (fun _ => s) := by
  simp only [InCube, mem_Icc, Pi.le_def, Pi.zero_apply]
  exact forall_and

theorem first_contact_cube {ι m : Type*} [Finite ι] [Finite m] {s r : ℝ} (hs : 0 < s)
    (f : m → (ι → ℝ) × (ι → ℝ) → ℝ)
    (hcont : ∀ j, ContinuousOn (f j) {y | InCube s y.1 ∧ InCube s y.2})
    (h0 : ∀ j, f j (0, 0) ≤ r)
    (hstep : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      (∀ y : (ι → ℝ) × (ι → ℝ), InCube (t * s) y.1 → InCube (t * s) y.2 → ∀ j, f j y ≤ r) →
        ∀ y : (ι → ℝ) × (ι → ℝ), InCube (t * s) y.1 → InCube (t * s) y.2 → ∀ j, f j y < r) :
    ∀ y : (ι → ℝ) × (ι → ℝ), InCube s y.1 → InCube s y.2 → ∀ j, f j y ≤ r := by
  obtain ⟨K, hK⟩ : ∃ K : Set ((ι → ℝ) × (ι → ℝ)), K = {y | InCube s y.1 ∧ InCube s y.2} :=
    ⟨_, rfl⟩
  rw [← hK] at hcont
  have hKmem : ∀ z, z ∈ K ↔ InCube s z.1 ∧ InCube s z.2 := fun z => by rw [hK]; rfl
  have hKc : IsCompact K := by
    have : K = Icc (0 : ι → ℝ) (fun _ => s) ×ˢ Icc (0 : ι → ℝ) (fun _ => s) := by
      ext z
      rw [hKmem, mem_prod, inCube_iff_mem_Icc, inCube_iff_mem_Icc]
    rw [this]
    exact isCompact_Icc.prod isCompact_Icc
  -- the map `(t, z) ↦ f j (t • z)` is continuous on `[0, 1] × K`
  have hmaps : MapsTo (fun q : ℝ × ((ι → ℝ) × (ι → ℝ)) => q.1 • q.2) (Icc 0 1 ×ˢ K) K := by
    rintro ⟨t, z⟩ ⟨ht, hz⟩
    rw [hKmem] at hz ⊢
    have hts : t * s ≤ s := mul_le_of_le_one_left hs.le ht.2
    exact ⟨inCube_mono hts (inCube_smul ht.1 hz.1), inCube_mono hts (inCube_smul ht.1 hz.2)⟩
  have hgcont : ∀ j, ContinuousOn (fun q : ℝ × ((ι → ℝ) × (ι → ℝ)) => f j (q.1 • q.2))
      (Icc 0 1 ×ˢ K) := fun j =>
    (hcont j).comp (continuous_fst.smul continuous_snd).continuousOn hmaps
  have hline : ∀ j, ∀ z ∈ K, ContinuousOn (fun t : ℝ => f j (t • z)) (Icc 0 1) := fun j z hz =>
    (hgcont j).comp (continuous_id.prodMk continuous_const).continuousOn fun t ht => ⟨ht, hz⟩
  -- the set of good scalings
  set A : Set ℝ := {t | ∀ z ∈ K, ∀ j, f j (t • z) ≤ r} with hA
  have hAc : IsClosed (A ∩ Icc 0 1) := by
    have : A ∩ Icc 0 1 =
        Icc 0 1 ∩ ⋂ z ∈ K, ⋂ j, (Icc 0 1 ∩ (fun t : ℝ => f j (t • z)) ⁻¹' Iic r) := by
      ext t
      simp only [hA, mem_inter_iff, mem_ofPred_eq, mem_iInter, mem_preimage, mem_Iic]
      constructor
      · rintro ⟨h, ht⟩
        exact ⟨ht, fun z hz j => ⟨ht, h z hz j⟩⟩
      · rintro ⟨ht, h⟩
        exact ⟨fun z hz j => (h z hz j).2, ht⟩
    rw [this]
    refine isClosed_Icc.inter (isClosed_biInter fun z hz => isClosed_iInter fun j => ?_)
    exact (hline j z hz).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hA0 : (0 : ℝ) ∈ A := fun z _ j => by
    rw [zero_smul]
    exact h0 j
  have hgt : ∀ x ∈ A ∩ Ico 0 1, A ∈ 𝓝[>] x := by
    rintro x ⟨hxA, hx0, hx1⟩
    have hle : ∀ y : (ι → ℝ) × (ι → ℝ), InCube (x * s) y.1 → InCube (x * s) y.2 →
        ∀ j, f j y ≤ r := by
      intro y hy1 hy2 j
      obtain ⟨z1, hz1, hz1e⟩ := inCube_exists_smul hs.le hx0 hy1
      obtain ⟨z2, hz2, hz2e⟩ := inCube_exists_smul hs.le hx0 hy2
      have hy : x • (z1, z2) = y := Prod.ext hz1e hz2e
      rw [← hy]
      exact hxA (z1, z2) ((hKmem _).2 ⟨hz1, hz2⟩) j
    have hlt := hstep x hx0 hx1.le hle
    have hlt' : ∀ z ∈ K, ∀ j, f j (x • z) < r := fun z hz j =>
      hlt (x • z) (inCube_smul hx0 ((hKmem z).1 hz).1) (inCube_smul hx0 ((hKmem z).1 hz).2) j
    have hev : ∀ᶠ t in 𝓝 x, ∀ z ∈ K, z ∈ K → t ∈ Icc (0 : ℝ) 1 → ∀ j, f j (t • z) < r := by
      refine hKc.eventually_forall_of_forall_eventually
        (P := fun t z => z ∈ K → t ∈ Icc (0 : ℝ) 1 → ∀ j, f j (t • z) < r) fun z hz => ?_
      have hmem : (x, z) ∈ Icc (0 : ℝ) 1 ×ˢ K := ⟨⟨hx0, hx1.le⟩, hz⟩
      have hj : ∀ j, ∀ᶠ q in 𝓝[Icc (0 : ℝ) 1 ×ˢ K] (x, z), f j (q.1 • q.2) < r := fun j =>
        ((hgcont j) (x, z) hmem).eventually (eventually_lt_nhds (hlt' z hz j))
      have hall := eventually_nhdsWithin_iff.1 (eventually_all.2 hj)
      filter_upwards [hall] with q hq hqK hqI
      exact hq ⟨hqI, hqK⟩
    have hI : ∀ᶠ t in 𝓝[>] x, t ∈ Icc (0 : ℝ) 1 := by
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (eventually_lt_nhds hx1)]
        with t ht1 ht2
      exact ⟨hx0.trans (le_of_lt ht1), le_of_lt ht2⟩
    filter_upwards [hI, nhdsWithin_le_nhds hev] with t ht htev
    exact fun z hz j => (htev z hz hz ht j).le
  have h1A : (1 : ℝ) ∈ A :=
    IsClosed.Icc_subset_of_forall_mem_nhdsWithin hAc hA0 hgt ⟨zero_le_one, le_rfl⟩
  intro y hy1 hy2 j
  simpa using h1A y ((hKmem y).2 ⟨hy1, hy2⟩) j

end BiluLinial.Tight
