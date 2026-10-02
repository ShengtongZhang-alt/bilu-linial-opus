/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.SecondOrder.Explicit.Defs
public import BiluLinial.SecondOrder.Explicit.Root

/-!
# Choice of the parameter `t`

Blueprint node `C2-param` (source Section 6: "Fix any threshold `R` with `2√q < R < R_q`, and set
`t = (R - √(R² - 4q))/(2q)` … `√z_q < t < q^{-1/2}`"). Instead of solving for `t`, we pick `t`
slightly above `√z` by continuity, which also covers `R ≤ 2√q` (then the construction proves the
stronger bound `‖A_σ‖ ≥ thr n t > R`).

For `q = n + 2 ≥ 3`, a positive root `z` of `q z (1 + z + z² + 2z³) = 1 + z + z² + 4z⁴` and
`R < 1/√z + q √z`, there is `t` with `t > 0`, `q t² < 1`, `F_q(t²) > 0` and `R < thr n t`.

Proof: `z < 1/q` (`root_lt_inv`), so `q (√z)² < 1`; `s ↦ q s + 1/s` and `s ↦ q s²` are continuous at
`s₀ = √z > 0`, so for `s` in a right neighbourhood of `s₀`: `R < q s + 1/s`, `q s² < 1`, `s > s₀`.
Then `t² > z` and `F_q(t²) > F_q(z) = 0` by `rootPoly_strictMonoOn`.
-/

@[expose] public section

namespace BiluLinial.SecondOrder.Explicit

open Filter Topology

theorem exists_param (n : ℕ) (hn : 1 ≤ n) {z : ℝ} (hz : 0 < z)
    (hroot : ((n : ℝ) + 2) * z * (1 + z + z ^ 2 + 2 * z ^ 3) = 1 + z + z ^ 2 + 4 * z ^ 4)
    {R : ℝ} (hR : R < 1 / Real.sqrt z + ((n : ℝ) + 2) * Real.sqrt z) :
    ∃ t : ℝ, 0 < t ∧ ((n : ℝ) + 2) * t ^ 2 < 1 ∧
      1 + t ^ 2 + (t ^ 2) ^ 2 + 4 * (t ^ 2) ^ 4 <
        ((n : ℝ) + 2) * t ^ 2 * (1 + t ^ 2 + (t ^ 2) ^ 2 + 2 * (t ^ 2) ^ 3) ∧
      R < thr n t := by
  set q : ℝ := (n : ℝ) + 2 with hq_def
  have hq3 : 3 ≤ q := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hq0 : 0 < q := by linarith
  have hzq : z < 1 / q := root_lt_inv hq3 hz hroot
  have hqz : q * z < 1 := by
    rw [lt_div_iff₀ hq0] at hzq
    linarith
  set s₀ := Real.sqrt z with hs₀_def
  have hs₀ : 0 < s₀ := Real.sqrt_pos.2 hz
  have hs₀2 : s₀ ^ 2 = z := Real.sq_sqrt hz.le
  have hf : ContinuousAt (fun s : ℝ => q * s + 1 / s) s₀ :=
    (continuousAt_const.mul continuousAt_id).add (continuousAt_const.div continuousAt_id hs₀.ne')
  have hg : ContinuousAt (fun s : ℝ => q * s ^ 2) s₀ :=
    continuousAt_const.mul (continuousAt_id.pow 2)
  have e1 : ∀ᶠ s in 𝓝 s₀, R < q * s + 1 / s :=
    hf.eventually (lt_mem_nhds (by linarith))
  have e2 : ∀ᶠ s in 𝓝 s₀, q * s ^ 2 < 1 :=
    hg.eventually (gt_mem_nhds (by change q * s₀ ^ 2 < 1; rw [hs₀2]; exact hqz))
  have e12 : ∀ᶠ s in 𝓝[>] s₀, R < q * s + 1 / s ∧ q * s ^ 2 < 1 :=
    nhdsWithin_le_nhds (e1.and e2)
  have e3 : ∀ᶠ s in 𝓝[>] s₀, s₀ < s := self_mem_nhdsWithin
  obtain ⟨t, ⟨h1, h2⟩, h3⟩ := (e12.and e3).exists
  refine ⟨t, by linarith, h2, ?_, h1⟩
  have hzt : z < t ^ 2 := by
    rw [← hs₀2]
    exact pow_lt_pow_left₀ h3 hs₀.le two_ne_zero
  have hmono := rootPoly_strictMonoOn hq3 (Set.mem_Ici.2 hz.le)
    (Set.mem_Ici.2 (by positivity : (0 : ℝ) ≤ t ^ 2)) hzt
  simp only at hmono
  linarith

end BiluLinial.SecondOrder.Explicit
