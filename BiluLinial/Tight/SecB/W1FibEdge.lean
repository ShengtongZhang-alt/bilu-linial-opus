/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecB.W1FibRegAsm

/-!
# The weak loop (W1): the per-edge remainder (TB.W1fib-edge)

Node TB.W1fib-edge of `docs/tight/BP_SECB.md` (source l.840–903; AUDIT-B §2.4). Fix a contact, an
edge `e = ij` (`i ∈ N`, `j ∼ i`) and a configuration `k` (`cfgPsi`, `cfgD` of `SecB/W1FibCfg.lean`:
`Ψ = H F_ji` and its first-order derivative `DΨ`). For a signing `σ` with `σ_e = 1` let
`σ' = σ^e` (`fibFlip`). The fibre `{σ, σ'}` is *regular* if one of its endpoints is good
(`fibGood`: `W > 0` and `64 p a g* ≤ 1`).

* **TB.W1fib-reg** (`weak_fibre_reg`, `SecB/W1FibReg.lean`): on a regular fibre the
  edge-interpolated `φ(t) = W(t)Ψ(t)` is a `FibChain` for `(WΨ, W DΨ)` with
  `sup_{[-1,1]} |φ'''| ≤ K (W(σ)Yb(σ) + W(σ')Yb(σ'))`.
* **TB.W1fib-nonreg** (`weak_fibre_nonreg`, proved): at a signing `τ` with `W(τ) > 0` and
  `64 p a g*(τ) > 1`: `|Ψ| + |DΨ| ≤ 9·256⁴ Yb` (`M = 11`). Proof: `w1_nonreg_cfg` gives
  `|Ψ| + |DΨ| ≤ 9 D_*⁷/(√d h)`; then `1 < 256 p a D_*` (since `g* ≤ 4 D_*`) and `p³ a ≤ 1`
  (`p⁶ ≤ p⁸ ≤ d`, `a² ≤ 1/d`) give `D_*⁷ ≤ (256 p a D_*)⁴ D_*⁷ ≤ 256⁴ a³ p D_*¹¹`
  (`nonreg_absorb`).
* **TB.W1fib-edge** (`weak_fibre_edge`, proved from the two): `fibre_ibp_bound`, then each fibre
  costs `≤ K'(W(σ)Yb(σ) + W(σ')Yb(σ'))` and `sum_fibre_pair` resums to `K' Z E[Yb]`.
-/

@[expose] public section

namespace BiluLinial.Tight.SecB

open Matrix

universe u

/-! ### Non-regular fibres -/

/-- **TB.W1fib-nonreg** (non-regular fibres). There are `K > 0` and `M` such that eventually, at
every contact, edge `ij`, configuration `k` and signing `τ` with `W(τ) ≠ 0` and `64 p a g*(τ) > 1`:
`|Ψ(τ)| + |DΨ(τ)| ≤ K Yb(τ)`. Sketch: module docstring. -/
theorem weak_fibre_nonreg :
    ∃ K : ℝ, 0 < K ∧ ∃ M : ℕ, Eventually fun _c₀ _κ₀ d p h => ∀ ct : Contact.{u} d p,
      ∀ i ∈ ct.N, ∀ j ∈ nbhd ct.G ct.S i, ∀ k : Fin 4, ∀ τ : Config ct.V,
      wt ct.G p (aOf d p) ct.yp ct.ym τ ct.S ≠ 0 → 1 < 64 * p * aOf d p * fibG ct τ i j →
      |cfgPsi ct h k i j τ| + |cfgD ct h k i j τ| ≤ K * fibYb ct M h i j τ := by
  refine ⟨9 * 256 ^ 4, by norm_num, 11, eventually_h_facts.mono ?_⟩
  rintro c₀ κ₀ d p h ⟨hR, h0, hdh, -, -⟩ ct i hi j hj k τ hτ hbig
  have ha := hR.aOf_pos
  have hd6 := hR.ten_pow_six_le_d
  have hd : (0 : ℝ) < d := by linarith
  have ha2 := hR.pf_a_sq_le
  have had : aOf d p ^ 2 * d ≤ 1 := by
    have := mul_le_mul_of_nonneg_right ha2 hd.le
    rwa [one_div_mul_cancel hd.ne'] at this
  have hinv : 1 / (d : ℝ) ≤ 1 := by rw [div_le_one hd]; linarith
  have ha1 : aOf d p ≤ 1 := by nlinarith
  have hah : aOf d p ^ 2 ≤ h := ha2.trans hdh
  have hp1 : (1 : ℝ) ≤ p := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hR.two_le_p
    linarith
  have hp8 := regime_p8_le hR
  have hP3 : (p : ℝ) ^ 3 * aOf d p ≤ 1 := by
    have h6 : (p : ℝ) ^ 6 ≤ d := (pow_le_pow_right₀ hp1 (by norm_num : 6 ≤ 8)).trans hp8
    have hsq : ((p : ℝ) ^ 3 * aOf d p) ^ 2 ≤ 1 := by
      have e : ((p : ℝ) ^ 3 * aOf d p) ^ 2 = (p : ℝ) ^ 6 * aOf d p ^ 2 := by ring
      rw [e]
      calc (p : ℝ) ^ 6 * aOf d p ^ 2 ≤ d * aOf d p ^ 2 :=
            mul_le_mul_of_nonneg_right h6 (sq_nonneg _)
        _ ≤ 1 := by rw [mul_comm]; exact had
    have h0' : 0 ≤ (p : ℝ) ^ 3 * aOf d p := by positivity
    nlinarith
  have hPa : (p : ℝ) * aOf d p ≤ 1 :=
    (mul_le_mul_of_nonneg_right (le_self_pow₀ hp1 (by norm_num : 3 ≠ 0)) ha.le).trans hP3
  have main := w1_nonreg_cfg ct h0 hR ha1 hPa hah had hτ hi hj k
  have hD := w1_Dstar_ge_one ct hτ
  have hx : 1 < 256 * (p : ℝ) * aOf d p * ct.Dstar τ := by
    obtain ⟨a1, a2⟩ := w1_diag_le_Dstar ct (w1Ball_N ct hi) τ
    obtain ⟨b1, b2⟩ := w1_diag_le_Dstar ct (w1Ball_NN ct hi hj) τ
    have hG : fibG ct τ i j ≤ 4 * ct.Dstar τ := by unfold fibG; linarith
    have h64 : 0 ≤ 64 * (p : ℝ) * aOf d p := by positivity
    have := mul_le_mul_of_nonneg_left hG h64
    linarith [show 64 * (p : ℝ) * aOf d p * (4 * ct.Dstar τ) =
      256 * (p : ℝ) * aOf d p * ct.Dstar τ by ring]
  refine main.trans ?_
  unfold fibYb
  exact nonreg_absorb ha.le (Nat.cast_nonneg p) hD (Real.sqrt_pos.mpr hd) h0 hP3 hx

/-! ### Assembly -/

/-- **TB.W1fib-edge** (per-edge remainder of the first-order endpoint identity). There are `C > 0`
and `M` such that eventually, at every contact, `i ∈ N`, `j ∼ i`, and in the four configurations:
`|Rem_ij| ≤ C (a³/(√d h)) E[D_*^M (p³ R_ij² + p)]`. Proof: `fibre_ibp_bound` with TB.W1fib-reg on
regular fibres and TB.W1fib-nonreg on the others, then `sum_fibre_pair`. -/
theorem weak_fibre_edge :
    ∃ C : ℝ, 0 < C ∧ ∃ M : ℕ, Eventually fun _c₀ _κ₀ d p h => ∀ ct : Contact.{u} d p,
      ∀ i ∈ ct.N, ∀ j ∈ nbhd ct.G ct.S i,
      |fibRem ct 1 ct.OmP ct.dOmP (ct.XP h) (ct.XP h) (fun _ => ct.uvec) (fun _ _ _ _ => 0) i j| ≤
          fibB ct C M h i j ∧
        |fibRem ct 1 ct.OmP ct.dOmP (ct.XP h) (ct.XP h) (ct.bP h) (dbP ct h) i j| ≤
          fibB ct C M h i j ∧
        |fibRem ct (-1) ct.OmM ct.dOmM (ct.XM h) (ct.XP h) (fun _ => ct.uvec)
            (fun _ _ _ _ => 0) i j| ≤ fibB ct C M h i j ∧
        |fibRem ct (-1) ct.OmM ct.dOmM (ct.XM h) (ct.XP h) (ct.bM h) (dbM ct h) i j| ≤
          fibB ct C M h i j := by
  obtain ⟨K₁, hK₁, M₁, hB⟩ := weak_fibre_reg.{u}
  obtain ⟨K₂, hK₂, M₂, hC⟩ := weak_fibre_nonreg.{u}
  refine ⟨4 / 3 * K₁ + K₂, by positivity, M₁ + M₂, ((hB.and hC).and eventually_h_facts).mono ?_⟩
  rintro c₀ κ₀ d p h ⟨⟨hB', hC'⟩, hR, h0, -⟩ ct i hi j hj
  classical
  set K := 4 / 3 * K₁ + K₂ with hKdef
  set M := M₁ + M₂ with hMdef
  have hs := hR.sOf_pos
  have hsub : ∀ y : ct.V → ℝ, InCube (ct.lam * sOf d p) y → InCube (sOf d p) y := fun y hy k =>
    ⟨(hy k).1, le_trans (hy k).2 (by nlinarith [ct.ctx.lam_le_one, ct.ctx.lam_nonneg])⟩
  have hZw : 0 < Zw ct.G p (aOf d p) ct.yp ct.ym ct.S :=
    ct.ctx.pos ct.yp ct.ym (hsub _ ct.ctx.hyp) (hsub _ ct.ctx.hym)
  set w : Config ct.V → ℝ := fun τ => wt ct.G p (aOf d p) ct.yp ct.ym τ ct.S with hwdef
  set Yb : Config ct.V → ℝ := fun τ => w τ * fibYb ct M h i j τ with hYbdef
  have hYb0 : ∀ τ, 0 ≤ Yb τ := fun τ => wt_fibYb_nonneg ct M h0 i j τ
  have key : ∀ k : Fin 4,
      |ct.E (fun σ => sgn σ i j * cfgPsi ct h k i j σ) - ct.E (cfgD ct h k i j)| ≤
        fibB ct K M h i j := by
    intro k
    set Φ₀ : Config ct.V → ℝ := fun τ => w τ * cfgPsi ct h k i j τ with hΦ₀
    set Φ₁ : Config ct.V → ℝ := fun τ => w τ * cfgD ct h k i j τ with hΦ₁
    -- the per-fibre bound
    have hfib : ∀ σ : Config ct.V, (if σ s(i, j) = 1 then
        (if (fibGood ct i j σ ∨ fibGood ct i j (fibFlip ct σ i j)) then
          4 / 3 * (K₁ * (w σ * fibYb ct M₁ h i j σ +
            w (fibFlip ct σ i j) * fibYb ct M₁ h i j (fibFlip ct σ i j))) else
          |Φ₀ σ| + |Φ₀ (Function.update σ s(i, j) (-1))| + |Φ₁ σ| +
            |Φ₁ (Function.update σ s(i, j) (-1))|) else 0) ≤
        if σ s(i, j) = 1 then K * (Yb σ + Yb (Function.update σ s(i, j) (-1))) else 0 := by
      intro σ
      by_cases he : σ s(i, j) = 1
      · rw [if_pos he, if_pos he]
        have hfl : fibFlip ct σ i j = Function.update σ s(i, j) (-1) := rfl
        by_cases hr : fibGood ct i j σ ∨ fibGood ct i j (fibFlip ct σ i j)
        · rw [if_pos hr, hfl]
          have m1 := fibYb_mono ct (Nat.le_add_right M₁ M₂) h0 i j σ
          have m2 := fibYb_mono ct (Nat.le_add_right M₁ M₂) h0 i j
            (Function.update σ s(i, j) (-1))
          have y1 := hYb0 σ
          have y2 := hYb0 (Function.update σ s(i, j) (-1))
          have : 4 / 3 * (K₁ * (w σ * fibYb ct M₁ h i j σ + w (Function.update σ s(i, j) (-1)) *
              fibYb ct M₁ h i j (Function.update σ s(i, j) (-1)))) ≤
              4 / 3 * K₁ * (Yb σ + Yb (Function.update σ s(i, j) (-1))) := by
            have := add_le_add m1 m2
            have hK0 : 0 ≤ 4 / 3 * K₁ := by positivity
            calc 4 / 3 * (K₁ * (w σ * fibYb ct M₁ h i j σ + w (Function.update σ s(i, j) (-1)) *
                  fibYb ct M₁ h i j (Function.update σ s(i, j) (-1))))
                = 4 / 3 * K₁ * (w σ * fibYb ct M₁ h i j σ + w (Function.update σ s(i, j) (-1)) *
                  fibYb ct M₁ h i j (Function.update σ s(i, j) (-1))) := by ring
              _ ≤ 4 / 3 * K₁ * (Yb σ + Yb (Function.update σ s(i, j) (-1))) :=
                  mul_le_mul_of_nonneg_left this hK0
          have hK2 : 0 ≤ K₂ * (Yb σ + Yb (Function.update σ s(i, j) (-1))) := by positivity
          rw [hKdef]
          nlinarith
        · rw [if_neg hr]
          -- each endpoint has zero weight or a large diagonal sum
          have hend : ∀ τ : Config ct.V, (τ = σ ∨ τ = Function.update σ s(i, j) (-1)) →
              |Φ₀ τ| + |Φ₁ τ| ≤ K₂ * Yb τ := by
            intro τ hτ
            by_cases hw : w τ = 0
            · simp only [hΦ₀, hΦ₁, hYbdef, hw, zero_mul, abs_zero, mul_zero, add_zero, le_refl]
            · have hng : ¬ fibGood ct i j τ := by
                rcases hτ with rfl | rfl
                · exact fun h => hr (Or.inl h)
                · exact fun h => hr (Or.inr (hfl ▸ h))
              have hbig : 1 < 64 * p * aOf d p * fibG ct τ i j := by
                by_contra hle
                exact hng ⟨hw, not_lt.mp hle⟩
              have hb := hC' ct i hi j hj k τ hw hbig
              have hm := fibYb_mono ct (Nat.le_add_left M₂ M₁) h0 i j τ
              have hw0 : 0 ≤ w τ := wt_nonneg ct.G τ
              simp only [hΦ₀, hΦ₁, hYbdef]
              rw [abs_mul, abs_mul, abs_of_nonneg hw0]
              calc w τ * |cfgPsi ct h k i j τ| + w τ * |cfgD ct h k i j τ|
                  = w τ * (|cfgPsi ct h k i j τ| + |cfgD ct h k i j τ|) := by ring
                _ ≤ w τ * (K₂ * fibYb ct M₂ h i j τ) := mul_le_mul_of_nonneg_left hb hw0
                _ = K₂ * (w τ * fibYb ct M₂ h i j τ) := by ring
                _ ≤ K₂ * (w τ * fibYb ct (M₁ + M₂) h i j τ) :=
                    mul_le_mul_of_nonneg_left hm hK₂.le
          have e1 := hend σ (Or.inl rfl)
          have e2 := hend (Function.update σ s(i, j) (-1)) (Or.inr rfl)
          have hK1 : 0 ≤ 4 / 3 * K₁ * (Yb σ + Yb (Function.update σ s(i, j) (-1))) := by
            have := hYb0 σ; have := hYb0 (Function.update σ s(i, j) (-1)); positivity
          rw [hKdef]
          nlinarith
      · rw [if_neg he, if_neg he]
    have hibp := fibre_ibp_bound s(i, j) Φ₀ Φ₁
      (fun σ => K₁ * (w σ * fibYb ct M₁ h i j σ +
        w (fibFlip ct σ i j) * fibYb ct M₁ h i j (fibFlip ct σ i j)))
      (fun σ => fibGood ct i j σ ∨ fibGood ct i j (fibFlip ct σ i j))
      (fun σ he hr => hB' ct i hi j hj k σ he hr)
    have hsum : (∑ σ : Config ct.V, if σ s(i, j) = 1 then
        K * (Yb σ + Yb (Function.update σ s(i, j) (-1))) else 0) = K * ∑ σ, Yb σ := by
      rw [sum_fibre_pair s(i, j) Yb, Finset.mul_sum]
      refine Finset.sum_congr rfl fun σ _ => ?_
      split_ifs <;> ring
    have hE1 : ct.E (fun σ => sgn σ i j * cfgPsi ct h k i j σ) =
        (∑ σ : Config ct.V, ((σ s(i, j) : ℤ) : ℝ) * Φ₀ σ) / Zw ct.G p (aOf d p) ct.yp ct.ym ct.S := by
      unfold Contact.E lawE
      congr 1
      exact Finset.sum_congr rfl fun σ _ => by simp only [hΦ₀, sgn]; ring
    have hE2 : ct.E (cfgD ct h k i j) =
        (∑ σ : Config ct.V, Φ₁ σ) / Zw ct.G p (aOf d p) ct.yp ct.ym ct.S := by
      unfold Contact.E lawE
      rfl
    have hfB : fibB ct K M h i j = K * ((∑ σ, Yb σ) / Zw ct.G p (aOf d p) ct.yp ct.ym ct.S) := by
      have hsw : ∀ (A : ℝ) (f : Config ct.V → ℝ),
          ∑ τ, wt ct.G p (aOf d p) ct.yp ct.ym τ ct.S * (A * f τ) =
            A * ∑ τ, wt ct.G p (aOf d p) ct.yp ct.ym τ ct.S * f τ := fun A f => by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
      unfold fibB Contact.E lawE
      simp only [hYbdef, hwdef, fibYb]
      rw [hsw]
      ring
    rw [hE1, hE2, ← sub_div, abs_div, abs_of_pos hZw, hfB, mul_div_assoc']
    refine div_le_div_of_nonneg_right ?_ hZw.le
    refine le_trans hibp (le_trans (Finset.sum_le_sum fun σ _ => hfib σ) ?_)
    rw [hsum]
  refine ⟨key 0, key 1, key 2, key 3⟩

end BiluLinial.Tight.SecB
