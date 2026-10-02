# BP_SECA: Section 1.2 (endpoint comparison and concentration), lines 237–625

Sub-blueprint for `docs/second_order_bilu_linial_tight.tex`, Section 1.2 (Lemma "Endpoint
calculus" (E1)/(E3), the comparison (E4), derivative accounting (E5), (E6), Lemma "Bias and
reference concentration" (C1)–(C6), (C3a), (C3b) and the closing scalar step, lines 600–625).
Audit: `docs/tight/AUDIT_A.md` (gap fixes A1–A14 applied). Files: `BiluLinial/Tight/SecA/`.
The coordinator merges this table into `docs/BLUEPRINT.md`.

Statuses: `stated` (Lean statement, `sorry`), `proved` (own proof sorry-free, may use stated
nodes), `proved*` (proved and every node below proved). `#print axioms` (2026-10-01) on the
`proved*` nodes `SecA.wavg_prod_pow_le`, `lawE_eq_coreE_div`, `insF_pos`, `rootMat_posSemidef`,
`hzN_le_hN`, `sum_topIdx_prod_pow_le`, `CapPoint.coreE_radE_div_eq`, `eventually_regA`,
`d_mul_kappa_le_one`, `Lsum_div_diagD_le`: `[propext, Classical.choice, Quot.sound]`. The exports
still depend on `sorryAx` through the stated nodes.

## Design

* **Regime** `RegA d p` (AUDIT-A (R)): `TRegime d p`, `log d ≥ 400`, `120 log d ≤ p`. Every node is
  stated as `∃ C, 0 < C ∧ ∀ d p, RegA d p → …` (absolute constants first, uniform in the graph);
  `SecA.eventually_regA : Eventually fun _ _ d p _ => RegA d p` converts to the `Eventually`
  form of `Tight/Ctx.lean` (threshold depends on `c₀` only).
* **Capped point** `CapPoint d p` (`SecA/Defs.lean`): a `CapCtx` (gap A1: the four implicit
  hypotheses — law moments, cap, own-core moments via IH + deletion, floor — all follow from it)
  bundled with its graph and a point of the capped cube `[0, λs]^V`. `Contact.toCapPoint`.
* Deficits are passed as bounds: `cp.DefLe ρ` (`1 - E h^±_i ≤ ρ`, all `i ∈ S`), `cp.DefZLe z θ`
  (shifted), `cp.DefZMax z θ` (θ is the largest shifted deficit). Zero sources are handled by the
  normalized precisions (gap A12): every quantity is defined there and the root factor `a²/Z_v` is
  written `a² y_v/D_v`.
* `b₀ = ε + p⁴/d + 1/d` (`b0Of`), `u = (p/d)^{1/3}` (`uOf`), `k_* = ⌈16p/log d⌉` (`kStarA`, same
  as SecC's `kStar`).
* Names: definitions in `BiluLinial.Tight` (SecB uses `hzN`); theorems in `BiluLinial.Tight.SecA`
  or in the namespaces `RegA`, `CapPoint`.
* Reused, not restated: D-star (`Tight/Star.lean`: `lawE_eq_star`, `sum_wt_mul_eq_star`,
  `qRoot_eq_qForm`, `PhiRoot_eq_starPhi`, `radE_eq_sum`, `setRoot`), T.COV (`gaussE_NG_ge_whitened`,
  `gaussE_NG_nonneg` = (C1b)), T.GIBP2 (`two_mul_gaussE_starF`: `N_G = 2𝖦F`), T.IL
  (`wavg_mul_le_holder`, `wavg_mul_le_interp`, `wavg_mul_sq_le` = INTERP and Cauchy–Schwarz),
  T.MAT (`trace_mul_nonneg`, …), E4 (`Compare/Multi.gauss_rad_expansion`, constant 2), the endpoint
  identity (`Compare/Endpoint.endpoint_chain`, constant 13/60), F2 (`source_moments`), the floor
  (`floor_ins`), the law helpers (`SourceMax/Law.lean`), `lawE_swap`.

## Exports (literal copies of `Tight/Contact/Inputs.lean`)

| Inputs name | export (`SecA/Export.lean`) | proved from | status |
|---|---|---|---|
| `in_E1` | `SecA.in_E1` | `CapPoint.endpoint_E1_cp` (C = 4·10¹¹) | proved |
| `in_C2` | `SecA.in_C2` | `SecA.concentration_C2` (`u ≤ δ̄`, `tr A² ≤ Θ`) | proved |
| `in_C1` | `SecA.in_C1` | `gaussE_NG_nonneg`, `two_mul_gaussE_starF`, `SecA.rootMat_posSemidef` | proved |
| `in_whiten` | `SecA.in_whiten` | `SecA.whiten`, T.GIBP2 (`E_{ν_K}N_G/F_H = 2a² Gterm`) | proved |
| `in_C3a` | `SecA.in_C3a` | `SecA.trace_sq_le_two_wK`, `SecA.core_tail` (`e^{-p/10} ≤ d^{-10}`) | proved |

All five statements are **literally** those of `Inputs.lean` (copied; the `Contact` quantities are
definitionally the `CapPoint` ones). No discrepancy. Also exported for Sections 1.3 and 1.5:
`SecA.scalar_ineq` (every shift `z` with `dz ≥ 1`, gap A10; used at `z = h` by S1) and
`SecA.concentration_C2` in its **all-vertex** form (deficits and rows at every `w ∈ S`, the Θ bound
at every root), consumed by `SecB.cl1_bridge`, `SecB.c2_bridge` (DR1 route).

## Node table

| id | statement (constants explicit) | source | Lean name (file) | deps | status |
|---|---|---|---|---|---|
| A-REG | REG list under `RegA`: `p^7 ≤ d`, `p^25 ≤ d^4`; `p⁴/d, p⁵/d, ε ≤ u`; `1/d, p²/d, p⁹/d², e^{-p} ≤ u²`; `b₀ ≤ 3u`; `du² ≥ 1`; `k_*`: `16p ≤ k_* log d`, `1920 ≤ k_*`, `4k_*+7 ≤ p`, `2(8k_*+12) ≤ p`; `2·16(log d+1) ≤ p`; `eventually_regA` | l.240–248, 615–622; A §1.1 | `RegA.*`, `SecA.uOf_pow_three`, `SecA.le_uOf_*`, `SecA.eventually_regA` (Reg) | D-params | proved* |
| A-PARP | `p ≤ 2q/9`, `η₀ ≥ 3/q`, `a² ≤ 1/(4q)`, `s ≤ 2`, `d a²s² ≤ 1`, `1/d ≤ ε ≤ 1/200`; on `[0,s]^V`: `c_ij ≤ 1/d`, `L_v ≤ 1`, `D_v = 1 + L_v - C_v`, `C_v ≤ 1/d`, `D_v ≤ 2`, `L_v/D_v ≤ 0.51` | l.67–68; A §1.2 | `SecA.p_le_two_q_div_nine`, `three_div_le_η0Of`, `aOf_sq_le`, `sOf_le_two`, `d_mul_kappa_le_one`, `inv_d_le_epsP`, `epsP_le`, `cEdge_le`, `Lsum_le_one`, `diagD_eq_one_add_L_sub_C`, `Csum_le`, `diagD_le_two`, `Lsum_div_diagD_le` (ParP) | D-params, FloorLemma | proved* |
| A-HOLD | generalized Hölder: `n = Σe_i`, `E X_i^n ≤ c_i^n` ⇒ `E Π X_i^{e_i} ≤ Π c_i^{e_i}` | A §2.5 | `SecA.wavg_prod_pow_le` (WAvg) | — | proved* |
| A-INS-cong | core weight, root matrices, core shifted inverses only see signs off `v` (`AgreeOff`) | l.125–135 | `SecA.wtCore_congr`, `rootMat_congr`, `coreShift_congr` (Ins) | — | proved* |
| A-INS | `E_H[g(σ,ξ_σ)] = E_{ν_K}[𝖱(Φ g)]/F_H` (g core-measurable); `F_H > 0` | l.255–257; A §1.3 | `SecA.lawE_eq_coreE_div`, `insF_pos` (Ins) | D-star | proved* |
| A-ROOTPSD | good core ⇒ root matrix PSD | — | `SecA.rootMat_posSemidef` (Ins) | — | proved* |
| A-C3 | (C3) both branches: `E_{ν_K}N_R/F_H = 1 - D_v E h_v + a²Σ E(G_vvG_ii - G_vi²)` | l.400–405 | `CapPoint.schur_C3`, `schur_C3_minus` (Ins) | A-INS, F1 (Schur at `v`) | proved* |
| A-MT | (M0) `Zw > 0`; (M2) cap; (M1) `E h^k ≤ (1+2ε)^k`, `k ≤ p/2`; (M3) own-core `E (M⁻¹)_ii^k ≤ (1+2ε)^k`; `Z_core > 0`; (M4) `40^p F_H ≥ 1`; root PSD on the support | l.244–248; A §1.4–1.5 | `CapPoint.Zw_pos`, `h_mean_le`, `h_moment`, `core_moment`, `ZwCore_pos`, `floor`, `root_psd`, `root_psd_core` (Moments) | F2, floor_ins, D-del, D-transfer, D-star, A-PARP | proved (`core_moment` proved*) |
| A-CLIP | `t ↦ t₊^e` is `C^{e-1}`; clipped observables `C^{min(e₁,e₂)-1}` | l.320; A §2.4 CLIP | `SecA.contDiff_posPow`, `contDiff_clipObs` (Star; proof in `StarSmooth`) | — | proved* |
| A-CLIP0 | derivatives of order `< min(e)` vanish off `{q_A,q_B<1}` | l.360 | `SecA.pderivList_clipObs_eq_zero` (Star; proof in `StarSmooth`) | A-CLIP | proved* |
| A-MAJ | majorant lemma at an interior point: `|∂^ν(gα^{e₁}β^{e₂})| ≤ m_g m_α^{e₁} m_β^{e₂}(2(1+e₁+e₂))^n λ^ν` | l.322–343; A §2.4 MAJ | `SecA.pderivList_clipObs_le_of_interior` (Star; proof in `StarSmooth`) | — | proved* |
| A-E5 | (E5) sup bounds `m (2(1+e₁+e₂))^n Π√b_i` everywhere (`n < min e`) | l.322–335 | `SecA.pderivList_clipObs_le` (Star; proof in `StarSmooth`) | A-MAJ, A-CLIP0 | proved* |
| A-SMOOTH | `SmoothBdd n` for `n < min e` | — | `SecA.smoothBdd_clipObs` (Star; proof in `StarSmooth`) | A-CLIP, A-E5 | proved* |
| A-EPB4 | refined one-coordinate bound (coefficient majorant), gap A7 | l.509–527 | `SecA.iter_pderiv_clipObs_le` (Star; proof in `StarLine`) | — | proved* |
| A-CR | (C4) Cramér–Rao form, `p ≥ 3`, any `M ⪰ 0` | l.456–478; A §2.12 | `SecA.gaussE_C4` (Star; proof in `StarCR`) | Gauss IBP | proved* |
| A-PDOM | `0 ⪯ M ⪯ A` ⇒ `tr(MA), tr(MB) ≤ Θ`, `AMA ⪯ ΘA`, `BMB ⪯ ΘB` | l.481–491 | `SecA.pdom` (Star; proof in `StarMat`) | T.MAT | proved* |
| A-RANK2 | rank-two edge perturbation: `det`, inverse entry | A §2.2 | `SecA.det_add_rank_two`, `inv_add_rank_two_apply` (Endpoint) | C-schur | stated |
| A-E1 | (E1) `|E[σ_viG⁺_vi] - E𝒟₁ + E𝒟₃/3| ≤ 1.15·10⁹ p⁵a⁵ E g*⁶` (law's own normalizer) | l.261–293; A §2.2 | `SecA.endpoint_E1` (Endpoint) | A-RANK2, `endpoint_chain` | stated |
| A-K3 | `𝒟₁x = a(-P + (2p-1)x² - 2pxz)`, `3![t³]Π = a³ Kpoly` | l.1370–1391 | `SecA.fibrePoly_coeff_one`, `fibrePoly_coeff_three` (E1) | — | proved* |
| A-E1CP | (E1) at a capped point: error `≤ 4·10¹¹ p⁵a⁵` | — | `CapPoint.endpoint_E1_cp` (E1) | A-E1, A-K3, A-MT | proved* |
| A-CNT | `Σ_{|j|_g=k+1}Π x^{j_i} ≤ T^{-(k+1)}(1 + x²T/(1-xT))^{|ι|}` | l.339–343 | `SecA.sum_topIdx_prod_pow_le` (Transfer) | — | proved* |
| A-E6 | (E6) `p 40^p (8p)^{4k_*+4} 8^{k_*+1} d^{-k_*} ≤ e^{-p}` | l.362–367; A §2.7 | `RegA.E6` (Transfer) | A-REG | proved* |
| A-CREM | `E_{ν_K}[m Σ_{top} Π b_i^{j_i}] ≤ M (5/d)^{k+1} e³` | l.337–343; A §2.5 | `CapPoint.crem` (Transfer) | A-HOLD, A-CNT, A-MT | proved* |
| A-REM | averaged (E4) remainder at depth `k_*` `≤ M e^{-p}/d · F_H` | l.362 | `CapPoint.trans_rem` (Transfer) | E4, A-CREM, A-E6, (M4) | proved* |
| A-RET | retained terms pass to the actual law exactly | l.360–361 | `CapPoint.coreE_radE_div_eq` (Transfer) | A-INS | proved* |
| A-HGR | retained grades `≥ 2`: `≤ 2e² M (dL⁴)²` | l.353–359; A §2.6 | `CapPoint.hgr` (Transfer) | A-HOLD, A-CNT | proved* |
| A-TRANS | generic transfer: `|E_{ν_K}(𝖦F-𝖱F)/F_H - (1/12)Σ_i E_H[∂_i⁴F/Φ]| ≤ 2e²M_E(dL⁴)² + M e^{-p}/d` | A §2.8 | `CapPoint.trans` (Transfer) | A-REM, A-RET, A-HGR | proved* |
| A-C1a | (C1) bias `|E_{ν_K}(N_R - N_G)| ≤ C (p⁴/d) F_H`, both branches | l.369–392 | `SecA.bias_C1a` (Conc) | A-TRANS, A-E5, A-MAJ, (F1), A-MT | proved* |
| A-SM2 | `E(h-1)² ≤ 5ε + 2ρ` | l.411–412 | `SecA.second_moment` (Conc) | A-MT | proved |
| A-BIASB | `E_{ν_K}N_R/F_H + a²Σ_{i∼v}E G_vi² ≤ 2ρ + 5ε + 1/d`, both branches | l.405–410 | `SecA.bias_branch`, `SecA.bias_bound` (Conc) | A-C3, A-MT, A-PARP | proved |
| A-ROW | `a²Σ_{i∼v}E(G^±_vi)² ≤ C(ρ + b₀)` (C = 5 + C_C1) | l.409–410; A §2.10 | `SecA.row_bound` (Conc) | A-BIASB, A-C1a, T.COV | proved* |
| A-WHITEN | `E_H w ≤ E_{ν_K}N_G/F_H + C(p⁴/d)(E_H w + d^{-10})`, both branches | l.413–424; A §2.11 | `SecA.whiten` (Conc) | A-INS, A-TRANS (on `wΦ`), T.COV, T.IL | proved* |
| A-WLE | `E_H w ≤ 1` | — | `SecA.wK_mean_le_one` (Conc) | A-MT, A-PARP, A-C5b | proved |
| A-CK | `E_H w ≤ C(ρ + b₀)` (C = 5 + C_C1 + 2C_W) | l.413–424 | `SecA.core_kernel` (Conc) | A-WHITEN, A-C1a, A-BIASB, A-WLE | proved* |
| A-C3a | `trA² 1{trA ≤ 1} ≤ 2w` (proved); `E_H[trA² 1{trA > 1}] ≤ e^{-p/10}` | l.425–435 | `SecA.trace_sq_le_two_wK`, `trace_sq_le_split`, `SecA.core_tail` (with `trace_rootMat_le`, `tail_branch`) (Conc) | A-MT, A-PARP, A-C5b (`coreGreen_le_greenP`), Jensen (`Real.pow_arith_mean_le_arith_mean_pow`) | proved |
| A-C3b | `E_H Θ ≤ C(ρ + b₀)` (C = 4C_K + 2) | l.437–442 | `SecA.preclosure_C3b` (Conc) | A-CK, A-C3a | proved* |
| A-C5a | `0 < h_z ≤ h` (PD precision, `z ≥ 0`) | l.446–448 | `SecA.hzN_pos`, `SecA.hzN_le_hN`, `inv_diag_add_le'` (Shift) | — | proved* (SecB has its own `hzN_le_hN`) |
| A-C5b | `C_{z,ii} ≤ X_{z,ii}`, `C_ii ≤ G_ii` (`i ≠ v`), `C_{z,ii} ≤ C_ii` | l.554–555 | `SecA.coreShift_le_shiftP`, `coreShift_le_coreGreen` (Shift), `coreGreen_le_greenP` (Moments) | C-schur | proved* |
| A-C5c | (C5(iv)) `Σ_{i∈N}(X_{z,ii} - C_{z,ii}) ≤ D_v(h_v - h_{z,v})/z` | l.547–559 | `SecA.sum_shift_sub_core_le` (Shift) | C-schur, T.MAT (v),(vi) | proved* |
| A-C5d | root Schur of `P̃ + zY`: `1/h_{z,v} = D_v(1 - q_{M_z}(ξ)) + z y_v` | l.604 | `SecA.inv_hzN_root` (Shift) | C-schur | proved* |
| A-C5e | (C5(vi)) mixed core traces `≤ (2/z) Σ_ν tr(C_ν - C_{z,ν})[N,N]` | l.571–578 | `SecA.sum_coreShift_mul_coreGreen_le` (Shift) | T.MAT | proved* |
| A-C5f | `q_{RM_zR}(ξ)τ² ≤ (a²y_v/(D_v z)) a²Σ G_vi²` | l.586–590 | `CapPoint.qForm_Mz_le` (Shift) | (F1) | proved* |
| A-C5g | good core ⇒ `0 ⪯ M_z ⪯ A` | l.451–453 | `SecA.rootMz_psd_le` (Shift) | T.MAT (v) | proved* |
| A-DEFZ | shifted deficits dominate unshifted ones | l.446 | `CapPoint.DefZLe.defLe` (Shift) | A-C5a | proved |
| A-C4T | transfer of (C4): `E[trM - q_M] ≤ 2pE[tr(MA)τ⁺ + tr(MB)τ⁻] + 4pE[q_{AMA}τ⁺² + q_{BMB}τ⁻²] + C{p⁵(ρ+b₀)/d + p²/d + p⁹/d² + e^{-p}/d}` | l.480–540; A §2.13 | `SecA.transfer_C4T` (Shift) | A-CR, A-PDOM, A-TRANS, A-EPB4, T.IL, A-C3b, A-ROW | proved* (`SecA.transfer_C4T := transfer_C4T_pf`, `SecA/C4T*.lean`: RET ×3, CR, T0, T12, T34) |
| A-TT | transferred terms at `M = M_z` `≤ C(θ+b₀)/(dz)` | l.542–591 | `SecA.transferred_TT` (Shift) | A-C5, A-MT, T.IL, A-ROW | proved* (C = 720 + 2C_row) |
| A-C6 | (C6) `E[tr M_z - q_{M_z}] ≤ C{p(θ+b₀)/(dz) + p⁵(θ+b₀)/d + p²/d + p⁹/d² + e^{-p}}` (C = C₄ + 6C_T) | l.592–599 | `SecA.bias_C6` (Shift) | A-C4T, A-TT, A-C5g, A-DEFZ | proved* |
| A-SCALAR | `θ² ≤ C{z + p(θ+b₀)/(dz) + p⁵(θ+b₀)/d + p²/d + p⁹/d² + e^{-p}}`, every `z > 0`, `dz ≥ 1` (C = 2C₆ + 2) | l.600–613; A §2.15 | `SecA.scalar_ineq`, with `SecA.scalar_alg`, `SecA.scalar_plus`, swap lemmas (Closure) | A-C6, A-C5a/c/d, A-PARP, A-MT, `lawE_swap` | proved* |
| A-THETA | `cp.DefZLe (u²) (C u)` (C = 2C_S + 5) | l.614–622 | `SecA.theta_bound`, `CapPoint.exists_defZMax` (Closure) | A-SCALAR, A-REG | proved* |
| A-C2 | (C2) all-vertex: `E(h^±_i-1)², 1-E h^±_i ≤ Cu` (`i ∈ S`); `a²ΣE(G^±_vi)², E Θ ≤ Cu` (`v ∈ S`) | l.378–386, 623 | `SecA.concentration_C2` (Closure) | A-THETA, A-SM2, A-ROW, A-C3b | proved* |

## Sketches (rule 2) and checks

**A-REG.** Each closure inequality `x ≤ u` (resp. `≤ u²`) is reduced to `x³ ≤ p/d`
(resp. `≤ (p/d)²`) and to a polynomial consequence of `p^17 ≤ d²`; `ε³ ≤ ε²·1 ≤ 1/(pq) ≤ p/d`;
`e^{-p} ≤ e^{-log d}`; `k_* < 16p/log d + 1 ≤ p/25 + 1`. `eventually_regA`: `exists_tRegime_pAt`,
`log x = o(x^{2/17})`, `⌊x⌋ ≥ x/2`. Checks: the constraints are compatible (`p ≥ 120 log d` and
`p ≤ d^{2/17}` for large `d`); `k_* ≥ 1920` makes the E4 depth large.

**A-PARP.** `η₀ ≥ 3/q` by contradiction (if `η₀ q < 3` then `η₀ ≤ 1/2`, `qη₀²p = 4(1-η₀) ≥ 2`,
and `p ≤ 2q/9` gives `q²η₀² ≥ 9`); `s ≤ 2 ⇔ 2τ_* ≤ η₀`; `d a²s² = (q+1)τ_*/(1-τ_*)² ≤ 1 ⇐ 3τ_* ≤ η₀`;
`c(1+c) = x ⇒ c = x - c²` gives `D_v = 1 + L_v - C_v`. Check: AUDIT-A §5 grid (no failure).

**A-C3 / A-BIASB.** (C3): `A-INS` with `g = f₁/Φ = (tr A - q_A)/α` (on the support `Φ > 0` and
`f₁ = 0` where `Φ = 0`, `p ≥ 2`), `(tr A - q_A)/α = 1 + (trA - 1)τ⁺`, `τ⁺ = D_v h_v = 1/α`,
`trA·τ⁺ = a² Σ (G_vvG_ii - G_vi²)` (F1, `G_ii = G_{K,ii} + G_vi²/G_vv`). Then `bias_branch`:
`Σ E(G_vvG_ii - G_vi²) + Σ E G_vi² = Σ E G_vvG_ii ≤ Σ y_vy_i(1+2ε)²` (Cauchy–Schwarz, (M1) with
`k = 2`), `-D_v E h_v ≤ -D_v(1-ρ)`, `1 - D_v + L_v = C_v ≤ 1/d`, `D_v ≤ 2`, `L_v ≤ 1`,
`(1+2ε)² ≤ 1 + 5ε`. Small cases: `S = {v}`, `y_v = 0` (both sides `0`).

**A-ROW / A-CK / A-C3b.** `E_{ν_K}N_G/F_H ≤ E_{ν_K}N_R/F_H + C_C1 p⁴/d` (`gauss_le_rad_of_bias`,
`F_H > 0` from the floor) and `N_G ≥ 0` (T.COV); ROW: `a²ΣEG² ≤ 2ρ + 5ε + 1/d + C_C1p⁴/d`.
CK: `E w ≤ N_G/F_H + C_W(p⁴/d)(E w + d^{-10})`, `E w ≤ 1`, drop the row term. C3b:
`tr A² ≤ 2w + trA²1{trA > 1}` on the support, `e^{-p/10} ≤ d^{-10} ≤ 1/d ≤ b₀`.

**A-C6.** C4T at `M = M_z` (core-measurable by `coreShift_congr`; `0 ⪯ M_z ⪯ A` on good cores by
A-C5g; `ρ = θ` by A-DEFZ), then A-TT: `2p·C_T(θ+b₀)/(dz) + 4p·C_T(θ+b₀)/(dz)`, `e^{-p}/d ≤ e^{-p}`.

**A-SCALAR** (fully checked in Lean). At a maximizing `(v,+)` (minus: swap symmetry
`lawE_swap`, `hzN(-1)(σ) = hzN(1)(-σ)`): Jensen `1 ≤ m E[1/h_{z,v}]` (Cauchy–Schwarz), A-C5d in
expectation, `E q = E tr M_z - B`, `D_v tr M_z = a²y_v(Σ y_i h_{z,i} - Σ(X_ii - C_ii))`, A-C5c with
the cap `E h_v ≤ 1+ε`, `m = 1 - θ`, `E h_{z,i} ≥ 1 - θ` (`i ∈ N`): `scalar_alg` gives
`θ² ≤ θ(1 - L + θL) ≤ (1-θ)E' ≤ (2C₆+2)(z + X)`, `E' = a²y_vD_v(ε+θ)/z + D_vB + zy_v`,
`a²y_vD_v ≤ 4a² ≤ 2/d`, `D_v B ≤ 2C₆X`, `zy_v ≤ 2z`. No `d^{-1}` term is needed (`L_v ≤ 1`, A11).

**A-THETA / A-C2** (fully checked in Lean). `z = u²`: `p(θ+b₀)/(du²) = u(θ+b₀)`,
`θ² ≤ K(2uθ + 10u²)` ⇒ `θ ≤ (2K+5)u`; then SM2, ROW, C3b with `ρ = C_t u`.

**A-E1CP** (checked in Lean): `fibreD 1 = a(-P + (2p-1)x² - 2pxz)`, `fibreD 3 = a³K`,
`g*⁶ ≤ Σ` of the four sixth powers, `E G_xx⁶ ≤ 2⁶(1+2ε)⁶ ≤ 68.5`, `1.15·10⁹ · 276 ≤ 4·10¹¹`.
**A-K3** checked in exact rational arithmetic (`p = 2..9`, 200 random instances): both identities
hold exactly.

**A-TRANS** (generic). E4 at depth `k_*` (needs `SmoothBdd (4k_*+4)`, given by A-SMOOTH since
`4k_*+4 < p - 2`), retained terms `= E_H[∂^{2j}F/Φ]` (A-RET; derivatives of order `≤ 4k_*+2` vanish
where `Φ = 0`, A-CLIP0), grades `≥ 2` by A-HGR (`|c_j| ≤ 1`), remainder by A-REM. Grade one is
`j = 2e_i`, `c_j = 1/12`, `∂^{2j} = ∂_i⁴`. The parent proof (combinatorics of `retIdx`) is not yet
written.

**A-E6.** The coefficient of `k_*` in the logarithm, `4 log(8p) + log 8 - log d`, is
`≤ 5 log 8 - (9/17)log d < 0`, so `k_* ≥ 16p/log d` may be used; the coefficient of `p` is then
`≤ log 40 + 0.42 + 128/17 - 16 < -4`.

**A-CNT.** `T^{k+1} = Π_{active} T^{j_i - 1}`; the sum is `≤ Π_i(Σ_{a ∈ {0,2,…}} x^aT^{a-1})`
(`Finset.prod_univ_sum` over `piFinset`). Used with `T = 1/(2x)` (CREM) and `T = 1/(dx²)` (HGR;
the generating bound `(1+x)^{|N|}` with `T = 1/(2x)` would cost `e^{p²}` in HGR — checked, that is
why `T` is a parameter).

**Small cases.** `S = {v}` (`N = ∅`): `A = B = 0`, `Φ = 1`, `F_H = 1`, `𝖦F = 𝖱F`, all bounds
trivial. `y_v = 0`: root decoupled, `A = 0`, `h_v = 1`. `S = ∅`: `DefZMax z 0`. Regime extremes:
`p = 10⁶`, `d = e^{400}` satisfy `RegA` only if `120·400 ≤ 10⁶` ✓ and `p^17 ≤ d²` ✓.

## Remaining `sorry`s (34)

* Infrastructure, root Schur block (F1-type, shared with SecC's `root_F1`): `schur_C3`,
  `schur_C3_minus` (Ins); `coreGreen_le_greenP` (Moments); `coreShift_le_shiftP`,
  `coreShift_le_coreGreen`, `sum_shift_sub_core_le`, `inv_hzN_root`,
  `sum_coreShift_mul_coreGreen_le`, `rootMz_psd_le`, `CapPoint.qForm_Mz_le` (Shift). All follow
  from one identity `Q⁻¹ = C - e_veᵥᵀ + s⁻¹(e_v - u)(e_v - u)ᵀ` (`C = (coreMat Q v)⁻¹`, `u = C b`,
  `s = vertexSchur Q v`), checked by hand: `Q·R = I` using `Mc C = I`, `C e_v = e_v`, `b_v = 0`.
* Moments: `core_moment` (k-th power version of D-transfer; only CREM uses it).
* Star analysis: `contDiff_posPow`, `contDiff_clipObs`, `pderivList_clipObs_eq_zero`,
  `pderivList_clipObs_le_of_interior` (MAJ), `pderivList_clipObs_le` (E5), `smoothBdd_clipObs`,
  `iter_pderiv_clipObs_le` (EPB4), `gaussE_C4` (CR), `pdom`.
* Transfer: `RegA.E6`, `crem`, `trans_rem`, `hgr`, `trans` (the last is a parent of REM/RET/HGR,
  combinatorics of `retIdx` not yet written).
* Graph-level analytic: `bias_C1a`, `whiten` (Conc), `transfer_C4T`, `transferred_TT` (Shift).
* Endpoint: `endpoint_E1`, `det_add_rank_two`, `inv_add_rank_two_apply` (Endpoint),
  `fibrePoly_coeff_one`, `fibrePoly_coeff_three` (E1).

## Gaps and findings

* No false statement found. The paper's (C2) form `δ = C{ε + p⁴/d + u}` is equivalent to `Cu`
  under (R) (`b₀ ≤ 3u`); exports use `δ̄ = dbar` (Inputs) via `u ≤ δ̄`.
* `whiten`: cannot be derived from `SecC.core_transfer` (needs `0 ≤ w ≤ d^{20}` on the core
  support; CHECK_SECS (a)); route through `CapPoint.trans` (moment bounds only).
* HGR needs the scale parameter `T = 1/(dL⁴)` in A-CNT (see above).
* Duplicates (kept, different namespaces): `SecA.hzN_le_hN` (SecB has its own),
  `SecA.rootMat_congr` (SecC), `SecA.greenP_self` (SecC). `kStarA` = SecC's `kStar`.
* F1 is used inside A-C3 / A-C5f; SecC states the same facts as `root_F1` (sorry). The coordinator
  may share one proof.
