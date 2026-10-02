/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecB.WTRetVan
public import BiluLinial.Tight.SecB.WTRetSum

/-!
# The retained grades of the WT observables (nodes TB.WT5v, TB.WT5l)

See the module docstring of `BiluLinial.Tight.SecB.WT` for the development.
-/

@[expose] public section

namespace BiluLinial.Tight.SecB

open Matrix

universe u

/-- **TB.WT5v** (vanishing at the clipped sign vectors). Eventually, for every signing, every
retained multi-index `1 ≤ |j|_g ≤ k_*` and every sign vector `ξ` with `Φ(ξ) = 0`,
`∂^{2j}F°(ξ) = 0` for both normalized observables. Proof (`starObs_dEven_eq_zero`,
`SecB/WTRetVan.lean`): if `q_A(ξ) > 1` or `q_B(ξ) > 1`, `F°` vanishes near `ξ`; otherwise the
shifted precisions are positive definite at `ξ` (`shiftSub_posDef`) and near `ξ`
`F° = c α₊^{p-|L|} β₊^{p-|L|} Π_t Γ_t · q` with smooth `Γ_t` (`D g_t` through adjugates and the
cut-off `psiW`; `det P̃(x) = c α(x)` by `precSub_ins`), so A-CLIP0
(`SecA.pderivList_clipObs_eq_zero`) applies: the order `2Σj ≤ 4k_* < p - m₀ - 4`
(`RegA.moment_order_le`). -/
theorem starObs_vanish (m₀ : ℕ) : Eventually fun _ _ d p h =>
    ∀ ct : Contact.{u} d p, ∀ i ∈ ct.N, ∀ e dir : Bool, ∀ l : List (ct.V × Bool × Bool),
      l.length ≤ m₀ → ∀ σ : Config ct.V,
      ∀ j ∈ (retIdx (kStarA d p) : Finset (nbhd ct.G ct.S i → ℕ)).erase 0,
      ∀ ξ : nbhd ct.G ct.S i → ℝ, (∀ s, ξ s = 1 ∨ ξ s = -1) →
        starPhi p (rootA ct σ i) (rootB ct σ i) ξ = 0 →
          dEven (lJ ct i) j (starObsQ ct h e dir i l σ) ξ = 0 ∧
            dEven (lJ ct i) j (starObsT ct h e dir i l σ) ξ = 0 := by
  refine (SecA.eventually_regA.and (eventually_base (2 * m₀ + 8))).mono ?_
  rintro c₀ κ₀ d p h ⟨hRA, -, hB, -, hh, hk0, -⟩ ct i hi e dir l hl σ j hj ξ _ hΦ
  have hiS : i ∈ ct.S := (Finset.mem_filter.1 hi).1
  have hp0 : (0 : ℝ) < p := by
    have : (0 : ℝ) ≤ (m₀ : ℝ) := Nat.cast_nonneg _
    push_cast at hB
    linarith
  have hh0 : 0 < h := by rw [hh]; exact div_pos hk0 (pow_pos hp0 4)
  have hmo := hRA.moment_order_le
  have hBn : 2 * m₀ + 8 ≤ p := by exact_mod_cast hB
  obtain ⟨hadm, hgr⟩ := mem_retIdx.1 (Finset.mem_of_mem_erase hj)
  have hlen : (dEvenList (lJ ct i) j).length < p - (l.length + 4) := by
    have e1 : (dEvenList (lJ ct i) j).length = 2 * ∑ s, j s := SecC.length_dEvenList_univ j
    have e2 := SecC.sum_le_two_mul_grade hadm
    rw [e1]
    omega
  exact starObs_dEven_eq_zero ct hh0 e dir hiS l (by omega) σ j hlen ξ hΦ

/-- **TB.WT5l** (retained grades under the actual law; analytic, open). The form of TRC-G
(`SecC.retained_grades_le`) for the observables `Φ H q_L`, `tr L Φ H`:
`|Σ_{1 ≤ |j|_g ≤ k_*} c_j E[∂^{2j}F°(ξ)/Φ(ξ)]| ≤ K (p⁴/d)(x + y + d^{-M})` (both observables).
Sketch (source lines 987–1041, (WT4)):
* (G2) at a supported signing `ξ` is interior (F1); a grade `g` with `l` active coordinates has
  order `n = 2(g + l) ≤ 4g`, and `|∂^{2j}F°(ξ)|/Φ(ξ) ≤ X_σ Π_s μ_s^{j_s}` with
  `X_σ ∈ {H q_L, √(H q_L · H tr L), H tr L}` up to fixed-degree diagonal multipliers
  (`|∂_s G_kk| ≤ 2a G_kk √(G_ii G_ss)`; at most two derivatives on `q_L`:
  `|(Lξ)_s|² ≤ L_ss q_L`, `Σ_s √L_ss ≤ √(d tr L)`, `Σ_{s,t} |L_st| ≤ d tr L`) and
  `μ_s = C p² a² r_s²` (as `SecC.retained_pointwise`, `SecC.lamR`);
* (G3) per grade, A-CNT (`SecC.sum_ret_prod_le`) and truncation/Cauchy–Schwarz
  (`SecC.trunc_moment`) or T.IL (`wavg_mul_le_interp`) against `x = E[H q_L]`, `y = E[H tr L]` with
  the floor `ϑ = d^{-M}` (mixed term `≤ √((x+ϑ)(y+ϑ))`), multiplier moments by F2 and T.DSTAR;
  grade `g` costs `(Kp⁴/d)^g (x + y + ϑ)`; geometric sum over `g ≥ 1`.
Checks: `J = ∅` (`(retIdx k).erase 0 = ∅`); `H = 0` (zero source at `i`). -/
theorem wt5_ret_law (m₀ M : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ Eventually fun _ _ d p h =>
    ∀ ct : Contact.{u} d p, ∀ i ∈ ct.N, ∀ e dir : Bool, ∀ l : List (ct.V × Bool × Bool),
      l.length ≤ m₀ →
      |∑ j ∈ (retIdx (kStarA d p) : Finset (nbhd ct.G ct.S i → ℕ)).erase 0, ecoefM j *
          ct.E (fun σ => dEven (lJ ct i) j (starObsQ ct h e dir i l σ) (rootSigns ct.G σ ct.S i) /
            starPhi p (rootA ct σ i) (rootB ct σ i) (rootSigns ct.G σ ct.S i))| +
        |∑ j ∈ (retIdx (kStarA d p) : Finset (nbhd ct.G ct.S i → ℕ)).erase 0, ecoefM j *
          ct.E (fun σ => dEven (lJ ct i) j (starObsT ct h e dir i l σ) (rootSigns ct.G σ ct.S i) /
            starPhi p (rootA ct σ i) (rootB ct σ i) (rootSigns ct.G σ ct.S i))| ≤
        K * ((p : ℝ) ^ 4 / d) *
          (massQ ct h e dir i l + massT ct h e dir i l + 1 / (d : ℝ) ^ M) := by
  refine ⟨52 * Real.exp 2 * (676 * 1024 ^ 2), by positivity, ?_⟩
  refine (((eventually_base (4 * 36 ^ (m₀ + 4) + 4 * m₀ + 64)).and
    (eventually_reg_ge fun κ₀ => ⌈1 / κ₀⌉₊)).and (eventually_trunc M)).mono ?_
  rintro c₀ κ₀ d p h ⟨⟨⟨hR, hB, -, hh, hk0, -⟩, -, hκp⟩, htr⟩ ct i hi e dir l hl
  classical
  have hiS : i ∈ ct.S := (Finset.mem_filter.1 hi).1
  have hdR := hR.ten_pow_six_le_d
  have hd0 : (0 : ℝ) < d := lt_of_lt_of_le (by norm_num) hdR
  have hd1 : (1 : ℝ) ≤ d := le_trans (by norm_num) hdR
  have hd5 : 5 ≤ d := le_trans (by norm_num) hR.ten_pow_six_le_nat
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast le_trans (by norm_num) hR.two_le_p
  have hp0 : (0 : ℝ) < p := by linarith
  have hh0 : 0 < h := by rw [hh]; positivity
  have hp8 := SecC.TRegime.p8_le hR
  have hpd : (p : ℝ) ≤ d := le_trans (le_self_pow₀ hp1 (by norm_num)) hp8
  have h36 : (0 : ℝ) ≤ 4 * 36 ^ (m₀ + 4) := by positivity
  have hinvh : 1 / h ≤ d := by
    have h1 : 1 / κ₀ ≤ p := (Nat.le_ceil _).trans (by exact_mod_cast hκp)
    rw [hh, one_div_div]
    calc (p : ℝ) ^ 4 / κ₀ = (p : ℝ) ^ 4 * (1 / κ₀) := by ring
      _ ≤ (p : ℝ) ^ 4 * p := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (p : ℝ) ^ 5 := by ring
      _ ≤ (p : ℝ) ^ 8 := pow_le_pow_right₀ hp1 (by norm_num)
      _ ≤ d := hp8
  set k := kStarA d p with hkdef
  have hk : 16 * k + 8 * mT M d ≤ p := htr
  have hm₀p : 4 * m₀ + 64 ≤ p := by
    have : ((4 * m₀ + 64 : ℕ) : ℝ) ≤ p := by push_cast; linarith
    exact_mod_cast this
  have hlk : l.length + 4 + 4 * k ≤ p := by omega
  have hl4 : 4 * (l.length + 4) ≤ p := by omega
  have hθ0 : (0 : ℝ) ≤ 1 / (d : ℝ) ^ M := by positivity
  have hyp0 : ∀ k, 0 ≤ ct.yp k := fun k => (ct.ctx.hyp k).1
  have hym0 : ∀ k, 0 ≤ ct.ym k := fun k => (ct.ctx.hym k).1
  set X : Config ct.V → ℝ := fun σ => ct.wtH h e i l σ *
    (qForm (kerL ct h e dir i σ) (rootSigns ct.G σ ct.S i) + (kerL ct h e dir i σ).trace)
    with hXdef
  have hq0 : ∀ σ, 0 ≤ qForm (kerL ct h e dir i σ) (rootSigns ct.G σ ct.S i) := fun σ => by
    have := (kerL_posSemidef ct h e dir i σ).dotProduct_mulVec_nonneg (rootSigns ct.G σ ct.S i)
    simp only [star_trivial] at this
    exact this
  have htr0 : ∀ σ, 0 ≤ (kerL ct h e dir i σ).trace := fun σ =>
    (kerL_posSemidef ct h e dir i σ).trace_nonneg
  have hX0 : ∀ σ, wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0 → 0 ≤ X σ := fun σ hσ =>
    mul_nonneg (wtH_nonneg ct hh0.le e i l hσ) (add_nonneg (hq0 σ) (htr0 σ))
  have hEX : ct.E X = massQ ct h e dir i l + massT ct h e dir i l := by
    unfold massQ massT Contact.E
    rw [← lawE_add]
    exact congrArg _ (funext fun σ => by simp only [hXdef]; ring)
  have hEX0 : 0 ≤ ct.E X := lawE_nonneg ct.G hX0
  have hRHS0 : 0 ≤ 52 * Real.exp 2 * (676 * 1024 ^ 2) * ((p : ℝ) ^ 4 / d) *
      (massQ ct h e dir i l + massT ct h e dir i l + 1 / (d : ℝ) ^ M) := by
    rw [← hEX]
    have : 0 ≤ ct.E X + 1 / (d : ℝ) ^ M := by linarith
    positivity
  rcases isEmpty_or_nonempty (nbhd ct.G ct.S i) with hN | hN
  · have hE : (retIdx k : Finset (nbhd ct.G ct.S i → ℕ)).erase 0 = ∅ := by
      ext j
      simp only [Finset.mem_erase, Finset.notMem_empty, iff_false, not_and]
      intro hj
      exact absurd (funext fun s => (IsEmpty.false s).elim) hj
    rw [hE, Finset.sum_empty, Finset.sum_empty, abs_zero, add_zero]
    exact hRHS0
  haveI := hN
  set Z : Config ct.V → ℝ := fun σ => SecC.ZR ct.G (aOf d p) ct.yp ct.ym σ ct.S i with hZdef
  have hZ1 : ∀ σ, 1 ≤ Z σ := fun σ => by
    simp only [hZdef, SecC.ZR]
    nlinarith [sq_nonneg (Finset.univ.sup' Finset.univ_nonempty
      (SecC.rhoR ct.G (aOf d p) ct.yp ct.ym σ ct.S i))]
  -- the second moment of `X`
  have hXs : ct.E (fun σ => X σ ^ 2) ≤ (d : ℝ) ^ 20 := by
    refine (X_sq_moment ct hR hh0 e dir hiS l hl4).trans ?_
    have hA' : (d : ℝ) ^ 4 / h ^ 4 ≤ (d : ℝ) ^ 8 := by
      calc (d : ℝ) ^ 4 / h ^ 4 = (d : ℝ) ^ 4 * (1 / h) ^ 4 := by field_simp
        _ ≤ (d : ℝ) ^ 4 * (d : ℝ) ^ 4 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hinvh 4) (by positivity)
        _ = (d : ℝ) ^ 8 := by ring
    have h6 : (6 : ℝ) ^ (2 * (l.length + 4)) ≤ 36 ^ (m₀ + 4) := by
      rw [pow_mul]
      norm_num
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    have hC : 4 * (36 : ℝ) ^ (m₀ + 4) ≤ d := by
      have : (4 * 36 ^ (m₀ + 4) : ℝ) ≤ p := by linarith
      linarith
    calc (((d : ℝ) + 1) * ((d : ℝ) ^ 4 / h ^ 4)) ^ 2 * 6 ^ (2 * (l.length + 4))
        ≤ (2 * (d : ℝ) * (d : ℝ) ^ 8) ^ 2 * 36 ^ (m₀ + 4) := by
          gcongr
          linarith
      _ = 4 * 36 ^ (m₀ + 4) * (d : ℝ) ^ 18 := by ring
      _ ≤ (d : ℝ) * (d : ℝ) ^ 18 := mul_le_mul_of_nonneg_right hC (by positivity)
      _ = (d : ℝ) ^ 19 := by ring
      _ ≤ (d : ℝ) ^ 20 := pow_le_pow_right₀ hd1 (by norm_num)
  -- per-grade truncation
  have htrunc : ∀ g ∈ Finset.range k, ct.E (fun σ => X σ * Z σ ^ (2 * (g + 1))) ≤
      1024 ^ (2 * (g + 1)) * (ct.E X + 1 / (d : ℝ) ^ M) := by
    intro g hg
    have hgk : g + 1 ≤ k := Finset.mem_range.1 hg
    refine SecC.trunc_moment ct.G hX0 (fun σ _ => (zero_le_one).trans (hZ1 σ)) (n := g + 1)
      (m := mT M d) (by norm_num) hθ0 ?_
    have hZm := SecC.Z_moment_le ct.G hR ct.ctx.toCapCtx ct.ctx.hyp ct.ctx.hym hiS
      (n := 2 * (2 * (g + 1) + mT M d)) (by omega)
    have h2 := two_pow_mT M hd5
    have hXs0 : 0 ≤ ct.E (fun σ => X σ ^ 2) := lawE_nonneg ct.G fun σ _ => sq_nonneg _
    calc ct.E (fun σ => X σ ^ 2) *
          lawE ct.G p (aOf d p) ct.yp ct.ym ct.S (fun σ => Z σ ^ (2 * (2 * (g + 1) + mT M d)))
        ≤ (d : ℝ) ^ 20 * (5 * d * 512 ^ (2 * (2 * (g + 1) + mT M d))) :=
          mul_le_mul hXs hZm (lawE_nonneg ct.G fun σ _ =>
            pow_nonneg ((zero_le_one).trans (hZ1 σ)) _) (by positivity)
      _ ≤ (1024 ^ mT M d * 1024 ^ (2 * (g + 1)) * (1 / (d : ℝ) ^ M)) ^ 2 := by
          set A := 2 * (g + 1) + mT M d with hA
          have hLA : (1024 : ℝ) ^ mT M d * 1024 ^ (2 * (g + 1)) = 1024 ^ A := by
            rw [← pow_add, add_comm]
          have h2A : (2 : ℝ) ^ (2 * mT M d) ≤ 2 ^ (2 * A) :=
            pow_le_pow_right₀ (by norm_num) (by omega)
          have h1024 : (512 : ℝ) ^ (2 * A) * 2 ^ (2 * A) = 1024 ^ (2 * A) := by
            rw [← mul_pow]; norm_num
          have hRHS : (1024 ^ mT M d * 1024 ^ (2 * (g + 1)) * (1 / (d : ℝ) ^ M)) ^ 2 =
              512 ^ (2 * A) * 2 ^ (2 * A) / (d : ℝ) ^ (2 * M) := by
            rw [hLA, h1024]
            field_simp
            ring
          rw [hRHS, le_div_iff₀ (by positivity)]
          calc (d : ℝ) ^ 20 * (5 * d * 512 ^ (2 * A)) * (d : ℝ) ^ (2 * M)
              = 512 ^ (2 * A) * (5 * (d : ℝ) ^ (21 + 2 * M)) := by ring
            _ ≤ 512 ^ (2 * A) * 2 ^ (2 * A) :=
                mul_le_mul_of_nonneg_left (h2.trans h2A) (by positivity)
  -- the geometric sum
  have hq : 676 * 1024 ^ 2 * (p : ℝ) ^ 4 / d ≤ 1 / 2 := by
    have hp6 : (10 : ℝ) ^ 6 ≤ p := by exact_mod_cast hR.hp
    have hp4 : (10 : ℝ) ^ 24 ≤ (p : ℝ) ^ 4 := by
      calc (10 : ℝ) ^ 24 = ((10 : ℝ) ^ 6) ^ 4 := by norm_num
        _ ≤ (p : ℝ) ^ 4 := pow_le_pow_left₀ (by norm_num) hp6 4
    rw [div_le_iff₀ hd0]
    nlinarith [mul_le_mul_of_nonneg_right hp4 (by positivity : (0 : ℝ) ≤ (p : ℝ) ^ 4)]
  have hq0 : 0 ≤ 676 * 1024 ^ 2 * (p : ℝ) ^ 4 / d := by positivity
  have hgeom : ∑ g ∈ Finset.range k, (676 * 1024 ^ 2 * (p : ℝ) ^ 4 / d) ^ (g + 1) ≤
      2 * (676 * 1024 ^ 2 * (p : ℝ) ^ 4 / d) := by
    calc ∑ g ∈ Finset.range k, (676 * 1024 ^ 2 * (p : ℝ) ^ 4 / d) ^ (g + 1)
        = (676 * 1024 ^ 2 * (p : ℝ) ^ 4 / d) *
            ∑ g ∈ Finset.range k, (676 * 1024 ^ 2 * (p : ℝ) ^ 4 / d) ^ g := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun g _ => by ring
      _ ≤ (676 * 1024 ^ 2 * (p : ℝ) ^ 4 / d) * ∑ g ∈ Finset.range k, (1 / 2 : ℝ) ^ g := by
          gcongr
      _ ≤ (676 * 1024 ^ 2 * (p : ℝ) ^ 4 / d) * 2 :=
          mul_le_mul_of_nonneg_left (sum_geometric_two_le k) hq0
      _ = _ := by ring
  -- the retained terms, one multi-index at a time
  have hc1 : ∀ j : nbhd ct.G ct.S i → ℕ, |ecoefM j| ≤ 1 := fun j => by
    rw [ecoefM, Finset.abs_prod]
    exact Finset.prod_le_one₀ (fun s _ => abs_nonneg _) fun s _ => abs_ecoef_le_one _
  have hterm : ∀ (j : nbhd ct.G ct.S i → ℕ) (F : Config ct.V → ℝ),
      |ecoefM j * ct.E F| ≤ ct.E (fun σ => |F σ|) := fun j F => by
    rw [abs_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _) (hc1 j)).trans
      (SecC.abs_lawE_le ct.G fun σ _ => le_rfl)
  have hsig := fun σ (hσ : wt ct.G p (aOf d p) ct.yp ct.ym σ ct.S ≠ 0) =>
    retained_sigma_le ct hR hh0 e dir hiS l hlk hσ
  calc _ ≤ ∑ j ∈ (retIdx k : Finset (nbhd ct.G ct.S i → ℕ)).erase 0,
          ct.E (fun σ => |dEven (lJ ct i) j (starObsQ ct h e dir i l σ) (rootSigns ct.G σ ct.S i) /
            starPhi p (rootA ct σ i) (rootB ct σ i) (rootSigns ct.G σ ct.S i)|) +
        ∑ j ∈ (retIdx k : Finset (nbhd ct.G ct.S i → ℕ)).erase 0,
          ct.E (fun σ => |dEven (lJ ct i) j (starObsT ct h e dir i l σ) (rootSigns ct.G σ ct.S i) /
            starPhi p (rootA ct σ i) (rootB ct σ i) (rootSigns ct.G σ ct.S i)|) :=
        add_le_add ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ =>
          hterm j _)) ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ =>
            hterm j _))
    _ = ct.E (fun σ => ∑ j ∈ (retIdx k : Finset (nbhd ct.G ct.S i → ℕ)).erase 0,
          (|dEven (lJ ct i) j (starObsQ ct h e dir i l σ) (rootSigns ct.G σ ct.S i) /
              starPhi p (rootA ct σ i) (rootB ct σ i) (rootSigns ct.G σ ct.S i)| +
            |dEven (lJ ct i) j (starObsT ct h e dir i l σ) (rootSigns ct.G σ ct.S i) /
              starPhi p (rootA ct σ i) (rootB ct σ i) (rootSigns ct.G σ ct.S i)|)) := by
        unfold Contact.E
        rw [← lawE_sum, ← lawE_sum, ← lawE_add]
        exact congrArg _ (funext fun σ => (Finset.sum_add_distrib).symm)
    _ ≤ ct.E (fun σ => 26 * Real.exp 2 * ∑ g ∈ Finset.range k,
          (676 * (p : ℝ) ^ 4 / d) ^ (g + 1) * (X σ * Z σ ^ (2 * (g + 1)))) :=
        lawE_mono ct.G hsig
    _ = 26 * Real.exp 2 * ∑ g ∈ Finset.range k, (676 * (p : ℝ) ^ 4 / d) ^ (g + 1) *
          ct.E (fun σ => X σ * Z σ ^ (2 * (g + 1))) := by
        unfold Contact.E
        rw [lawE_const_mul, lawE_sum]
        congr 1
        exact Finset.sum_congr rfl fun g _ => lawE_const_mul ct.G _ _
    _ ≤ 26 * Real.exp 2 * ∑ g ∈ Finset.range k, (676 * (p : ℝ) ^ 4 / d) ^ (g + 1) *
          (1024 ^ (2 * (g + 1)) * (ct.E X + 1 / (d : ℝ) ^ M)) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun g hg =>
          mul_le_mul_of_nonneg_left (htrunc g hg) (by positivity)) (by positivity)
    _ = 26 * Real.exp 2 * (ct.E X + 1 / (d : ℝ) ^ M) *
          ∑ g ∈ Finset.range k, (676 * 1024 ^ 2 * (p : ℝ) ^ 4 / d) ^ (g + 1) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [show (676 * 1024 ^ 2 * (p : ℝ) ^ 4 / d) ^ (g + 1) =
          (676 * (p : ℝ) ^ 4 / d) ^ (g + 1) * 1024 ^ (2 * (g + 1)) by
            rw [pow_mul, ← mul_pow]; ring_nf]
        ring
    _ ≤ 26 * Real.exp 2 * (ct.E X + 1 / (d : ℝ) ^ M) *
          (2 * (676 * 1024 ^ 2 * (p : ℝ) ^ 4 / d)) :=
        mul_le_mul_of_nonneg_left hgeom (mul_nonneg (by positivity) (by linarith))
    _ = _ := by rw [hEX]; ring

end BiluLinial.Tight.SecB
