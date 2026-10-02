# BP_SECB — Section B (source lines 626–1076), GCI-free route

Source: `docs/second_order_bilu_linial_tight.tex`, Lemma "Uniform incident-row gain" (626–693),
mean shift (696–719), Lemma "Random-profile weak loop" (721–911), "Weighted fresh-star quadratic
domination" (913–1075). Audits: `docs/tight/AUDIT_B.md`, `docs/tight/DR1_CHECK.md` (verdict
**CONFIRMED**: GCI is not needed), statement check `docs/tight/CHECK_SECS.md` (no false
statement). Lean files: `BiluLinial/Tight/SecB/` (namespace `BiluLinial.Tight.SecB`, except the
definitions of `Defs.lean`, which live in `BiluLinial.Tight` because `SecC/Defs.lean` imports them).
Every node's sketch is in the module docstring of its file. Import chain of the weak loop:
`WeakBase.lean` (TB.row … TB.W5) ← `W1Defs.lean` (W1 definitions, TB.W1alg) ← `W1Mom.lean` (TB.W1sec,
TB.W1mask) ← `W1FibDefs.lean` (fibre tools, TB.W1fib-alg) ← `W1FibNonreg.lean` ← `W1FibCfg.lean` ←
`W1FibSeg.lean` ← `W1FibSmooth.lean` ← `W1FibReg.lean` (TB.W1fib-reg and sub-nodes) ← `W1FibEdge.lean`
(TB.W1fib-nonreg, TB.W1fib-edge) ← `W1Fib.lean` (TB.W1fib-avg, TB.W1fib) ← `W1.lean` (TB.W1ibp) ← `Weak.lean` (`weak_loop_of`)
← `WT.lean` ← `Export.lean`; `Contact/Leaves2.lean` imports `Weak` and still sees everything.

## Route

DR1 route (DR1_CHECK §3): GR1, the transfer `T_v ≤ Cp⁴` and the whole GCI subtree are **not
formalized** in this section (the paper's GR1 is recorded in `Tight/Contact/RouteGCI.lean` by the
contact agent). W1 is stated with the exact determinant score `2pa|G⁺_ij − G⁻_ij|` (W1′) and its
remainder uses only (C2) (`ρ_row = C(δ + 1/d) ≤ Cp^{-2}`, AUDIT-B B-3). DR1 replaces GR1 for
FS5′ and CR3′/D9a′.

## Quantifiers and inputs

Every analytic node is `∃ C, Eventually …` (`Tight/Ctx.lean`): absolute constants, then
`c₀, κ₀ ∈ (0,1]`, then a threshold on `d`, at `p = ⌊c₀ d^{2/17}⌋`, `h = κ₀ p^{-4}`. Nodes are stated
for every capped point (`CapPoint`, `Tight/SecA/Defs.lean`) or every contact (`Contact`,
`Tight/Contact/Defs.lean`). Inputs from Section A enter as Prop-valued shapes, supplied by the
bridges of `Export.lean`:

* `CL1Shape K K_b c` (S1.lean): (CL1) at every capped point, `z ∈ [1/d, 1]`, largest deficit `θ`
  (`DefZMax`): `θ² ≤ K(z + p(θ+b)/(dz) + p⁵(θ+b)/d + p²/d + p⁹/d² + 1/d + e^{-cp})`,
  `b = ε + K_b p⁴/d + 1/d`. Bridge `cl1_bridge` ← `SecA.scalar_ineq` (`K_b = c = 1`).
* `C2RowShape K_δ` (S1.lean): at every capped point and `w ∈ S`, `1 − E h^±_w ≤ K_δ δ̄`,
  `a² S^±_w ≤ K_δ δ̄`. Bridge `c2_bridge` ← `SecA.concentration_C2` (`(p/d)^{1/3} ≤ δ̄`).
* `E1Shape C` (RouteDR1.lean): (E1) at every capped point, root `v`, `i ∈ N_S(v)`, with the
  explicit `𝒟₁` and `𝒟₃ = a³K_i` terms and error `C p⁵a⁵`. Bridge `e1_bridge` ←
  `CapPoint.endpoint_E1_cp` (`C = 4·10¹¹`).
* F2 `source_moments` (`Tight/SourceMax.lean`, proved), Tools `wavg_mul_le_umi` (UMI),
  `wavg_sup_pow_le` (T.DSTAR) (`Tight/Tools/Interp.lean`, proved), BLmid (WT3), `lawE_swap`
  (`Tight/Symmetry.lean`).

## Node table

Status: `proved` = own proof sorry-free (may use open nodes); `proved*` = no `sorry` below either
(`#print axioms` reports only `propext`, `Classical.choice`, `Quot.sound`; checked 2026-10-01);
`stated` = `sorry`. Nodes taking a Section A shape (`CL1Shape`, `C2RowShape`, `E1Shape`) as a
hypothesis are `proved*` as implications.

| id | statement | src | Lean (file) | deps | status |
|---|---|---|---|---|---|
| TB.law | `lawE` monotone/constant; precisions PD on the support; `G_ii = y_i h_i`, `X_ii = y_i hzN_i`; `(A+D)⁻¹_ii ≤ A⁻¹_ii`; `hzN ≤ hN`; diagonals `≥ 0` | — | `lawE_mono`, `lawE_const`, `posDef_of_wt_ne_zero`, `greenP_diag`, `shiftP_diag`, `inv_diag_add_le`, `hzN_le_hN`, `diag_nonneg_of_posDef` (LawE) | SourceMax/Law | proved |
| TB.exp | `p⁸ ≤ d`, `p⁵ ≤ q`, `0 ≤ ε ≤ p^{-3}`, `ε²pq ≤ 1`; eventual regime with `p ≥ B` | — | `eventually_base`, `regime_*` (Arith) | Params | proved |
| TB.S1s | (CL1) at `z = h` ⇒ `t ≤ K_S √h`, `K_S = (1+√(1+4(K+1)))/2` | 696–712 | `s1_scalar_real`, `s1_scalar` (S1) | TB.exp | proved* |
| TB.S1p | `0 ≤ E(G_ii − X_ii) ≤ (t_z + ε) y_i` pointwise in the capped family | 712–713 | `mean_shift_pt`, `tShift`, `defZMax_tShift` (S1) | TB.law | proved |
| TB.S1 | (S1): `t_h ≤ K_S√h`, `0 ≤ E(G^±_ii − X^±_ii) ≤ (K_S+1)√h y^±_i` | 696–719 | `mean_shift_of_cl1` (S1) | CL1Shape, TB.S1s, TB.S1p, `eventually_h_facts` | proved* |
| TB.row | row `i` of `(P̃+zY)(P̃+zY)⁻¹ = I` times `√y_i√y_l` | 755–761 | `shift_row_identity` (WeakBase) | — | proved |
| TB.W2 | `U_ii − f_i X_ε,ii X_ν,ii = −εa Σ_{j∼i} σ_ij F_ji` (any `X_ν`, `f`) | 750–761 | `weak_w2` (WeakBase) | TB.row | proved* |
| TB.ward | `(X²)_ii ≤ (G_ii − X_ii)/h` on the support, `i ∈ S` | 790–792 | `ward_diag` (WeakBase) | — | proved* |
| TB.S1w | weighted S1: `E[(G_ii−X_ii)Z] ≤ 3(K_S+2) B √h y_i` for `Z ≥ 0`, `‖Z‖_k ≤ B`, `log d + 2 ≤ k ≤ p/2` | 714–719 | `s1w_branch`, `mean_shift_weighted_of_cl1` (WeakBase) | TB.S1, UMI, F2 | proved* |
| TB.Dstar | `E D_*^n ≤ 3(1+d+d²) 12^n`, `1 ≤ n ≤ p/2` | 784–788 | `dstar_moment`, `ball_sub_card`, `one_add_add_pow_le`, `f2_base_le_two` (WeakBase) | T.DSTAR, F2, `SecA.sOf_le_two` | proved* |
| TB.W5 | `E[D_*^m (X_±²)_ii] ≤ 126(K_S+2)12^m/√h` = `in_W5 m` | 790–797 | `ward_mean_of_cl1`, `w5_branch`, `eventually_log_le_p`, `dstar_nonneg` (WeakBase) | TB.ward, TB.S1w, TB.Dstar | proved* |
| TB.W1alg | TB.W2 summed with weights `H u_i`: `4E[H uᵀKf] − 4E[H uᵀMf] = −εa·wEdge`, `a²·wMain = 4E[H fᵀKb]`; hence `4T_k = ∓(a·wEdge + a²·wMain)` for the four targets | 750–779 | `weak_config_ids`, `weak_targets`, `w1_main_reorg`, `sum_mul_maskU_diag`, `sum_mul_diag_eq`, `shiftP_symm` (W1Defs) | TB.W2 | proved* |
| TB.W1fib-alg | the left side of TB.W1fib equals `a Σ_{i∈N} Σ_{j∼i} u_i Rem_ij`, `Rem_ij = E[σ_ij H F_ji] − E[DΨ_ij]` (`DΨ = fibD`: W3 with `ν = +`, `∂ log W = 2pa(G⁺−G⁻)`, `∂_ij b_± = dbP, dbM`, `∂H = dOmP, dOmM`) | 776–779 | `weak_fibre_alg`, `fibD`, `fibRem`, `wMask_zero` (W1FibDefs) | — | proved* |
| TB.W1fib-ibp | abstract fibre IBP: if every regular fibre carries a `FibChain` for `(WΨ, W DΨ)` with bound `B`, then `|Σ_σ σ_e Φ₀ − Σ_σ Φ₁| ≤ Σ_{σ_e=1} [(4/3)B (regular) or the four endpoint terms]`; `sum_fibre_pair` | 840–870 | `fibre_ibp_bound`, `fibChain_bound`, `sum_fibre_pair`, `sum_fibre_neg` (W1FibDefs) | TB.W1fib-tools | proved* |
| TB.W1fib-nonreg | at `τ` with `W(τ) > 0`, `64pa g*(τ) > 1`: `|Ψ| + |DΨ| ≤ 9·256⁴ Yb` (`M = 11`; pointwise `|Ψ| + |DΨ| ≤ 9 D_*⁷/(√d h)`, then `1 < 256paD_*`, `p³a ≤ 1`) | 900–903 | `weak_fibre_nonreg` (W1FibEdge), `w1_nonreg_cfg` (W1FibCfg), `w1_nonreg_pt`, `fibD_real_le`, `nonreg_absorb`, `w1_g_off_le`, `w1_dOmP_le`, `w1_dOmM_le`, `w1_dbP_le4`, `w1_dbM_le4`, `w1_bP_le_m`, `w1_bM_le_m`, `w1_maskU_le` (W1FibNonreg) | W1Mom bounds | proved* |
| TB.W1fib-end | edge interpolation `P̃(t) = P̃(σ) + (t − σ_ij)τa√(y_iy_j)E` (`precT`; `precN_update`: changing `σ_ij` is this rank-two update), observables on precision pairs (`physInv`, `obsPsi`, `obsPsi_precN`), `φ = (det P̃⁺ det P̃⁻)^p Ψ` (`fibPhi`), endpoint values `φ(1) = W(σ)Ψ(σ)`, `φ(−1) = W(σ')Ψ(σ')`; generic chain `fibChain_of_contDiffOn` | 892–899 | `precT`, `precN_update`, `fibPp_one`, `fibPp_neg_one`, `fibPm_one`, `fibPm_neg_one`, `fibPhi_one`, `fibPhi_neg_one`, `fibChain_of_contDiffOn` (W1FibReg) | — | proved* |
| TB.W1fib-seg | on a regular fibre `P̃^±(t) ≻ 0` for `t ∈ [−2, 2]` | 892–895 | `fib_seg_pd` (W1FibReg), `psd_cauchy`, `sq_le_inv_diag_mul`, `posDef_add_edge`, `posDef_precN_add_edge` (W1FibSeg) | `greenP_diag` | proved* |
| TB.W1fib-smooth | `φ` is `C³` wherever `P̃^±(t) ≻ 0` (`h ≥ 0`) | — | `fibPhi_contDiffOn`, `fibPhi_cdAt`, `entCD_precT`, `entCD_physInv`, `vecCD_obsBP`, `vecCD_obsBM` (W1FibReg), `EntCD`, `cd_det`, `entCD_inv`, `cd_maskF` (W1FibSmooth) | — | proved* |
| TB.W1fib-d1 | `φ'(1) = W(σ) DΨ(σ)`, `φ'(−1) = W(σ') DΨ(σ')` at positive-definite endpoints (`h ≥ 0`) | 776–779, 892 | `fibPhi_deriv_one`, `fibPhi_deriv_neg_one` (W1FibReg) | (`SecA.det_add_rank_two` may be used) | **stated** |
| TB.W1fib-d3 | `∃ K M`, eventually, on regular fibres: `|φ'''(t)| ≤ K (W(σ)Yb(σ) + W(σ')Yb(σ'))`, `t ∈ [−1, 1]` | 892–899 | `fibPhi_d3` (W1FibReg) | TB.W1fib-seg; (`SecA.det_add_rank_two`, `SecA.inv_add_rank_two_apply` may be used) | **stated** |
| TB.W1fib-reg | regular fibres: `φ` is a `FibChain` for `(WΨ, W DΨ)` with `B = K (W(σ)Yb(σ) + W(σ')Yb(σ'))` | 892–899 | `weak_fibre_reg` (W1FibReg) | TB.W1fib-end, -seg, -smooth, -d1, -d3 | proved |
| TB.W1fib-edge | per-edge remainder: `∃ C M`, `|Rem_ij| ≤ C (a³/(√d h)) E[D_*^M (p³ R_ij² + p)]`, `R_ij = |G⁺_ij| + |G⁻_ij|` (four configurations; `C = (4/3)K_reg + K_nonreg`) | 840–903 | `weak_fibre_edge` (W1FibEdge), `fibB`, `fibR` (W1FibDefs), `cfgPsi`, `cfgD`, `fibGood`, `fibYb` (W1FibCfg) | TB.W1fib-ibp, TB.W1fib-reg, TB.W1fib-nonreg | proved |
| TB.W1fib-avg | `Σ_{i∈N} Σ_{j∼i} E[D_*^M R_ij²] ≤ C d² (δ̄ + 1/d)` and `E[D_*^M] ≤ C`, every `M` | 885–891 | `weak_fibre_avg`, `abs_add_abs_sq_le` (W1Fib) | C2RowShape, TB.Dstar, UMI, `greenP_sq_le` | proved* |
| TB.W1fib-tools | trapezoid rule `|E_ξ[ξφ] − E_ξ[φ']| ≤ (2/3) sup|φ'''|`; sign-fibre identity `Σ_σ σ_e Φ = Σ_{σ_e = 1}(Φ(σ) − Φ(σ^e))` | 840–870 | `trapezoid_chain`, `sum_sgn_fibre` (W1FibDefs) | `taylor_chain_bound` | proved* |
| TB.W1fib | first-order endpoint IBP (E1′) on all edge fibres `ij`, `i ∈ N`: `|a·wEdge + a²·wMain − a(wScore + wSec + wMask)| ≤ C B₀`; in fact `≤ 5 C_edge C_avg p/(dh)` (`a⁴d ≤ 1/d`, `δ̄ + 1/d ≤ 4/p²`) | 776–779, 840–903 | `weak_fibre_of`, `w1_fib_par`, `dbar_add_le` (W1Fib) | TB.W1fib-alg, TB.W1fib-edge, TB.W1fib-avg | proved |
| TB.W1sec | secondary W3 terms: `a·|wSec| ≤ (5/2) C_W5/(dh^{3/2}) ≤ C B₀` (four configurations) | 795–822 | `weak_sec_of`, `sec_sum_le`, `w1_sec_pt`, `w1_sec_E`, `shift_opnorm`, `shift_row_sq_le`, `w1_bP_abs_le`, `w1_bM_abs_le`, `w1_par1`, `w1_par2` (W1Mom) | TB.W5, `greenP_sq_le` | proved* |
| TB.W1mask | random-mask derivative: `a·|wMask(dbP/dbM)| ≤ 4 C_W5/(dh^{3/2}) ≤ C B₀` | 824–838 | `weak_mask_of`, `maskF_abs_le`, `w1_mask_pt`, `w1_mask_E`, `shiftP_sq_le`, `w1_dbP_abs_le`, `w1_dbM_abs_le`, `w1_par3` (W1Mom) | TB.W5 | proved* |
| TB.W1ibp | `|a·wEdge + a²·wMain| ≤ C 𝖲_f + C B₀` (assembly; `a|wScore| ≤ 𝖲_f` since `H ≥ 0`) | 776–779 | `weak_ibp_of`, `w1_assemble` (W1), `w1_score_le`, `w1_score_nonneg` (W1Defs) | TB.W1fib, TB.W1sec, TB.W1mask | proved |
| TB.W1 | the four weak identities with score `𝖲_f` (exact determinant score) and remainder `B₀` = `in_W1` | 721–911 | `weak_loop_of` (Weak) | TB.W1alg, TB.W1ibp | proved |
| TB.root | `D_w h_w + τa Σ_{i∼w} σ_wi G^τ_wi = 1`; in mean | 674–677 | `root_row_identity`, `root_row_mean` (RouteDR1) | TB.law | proved |
| TB.Kmom | `|E K(x_i,z_i,P_i,Q_i)| ≤ C p³` (third-order endpoint polynomial `Kpoly`), `C = 264·64·16·64` | 680, 1370–1391 | `kpoly_moment`, `kpoly_abs_le`, `greenP_sq_le`, `posSemidef_entry_sq_le`, `sum4_pow4_le`, `abs_lawE_le` (RouteDR1) | F2 | proved* |
| TB.E1row⁺ | `|E[σ_wi x_i] − E𝒟₁x_i| ≤ K p³a³`, `K = C + C_K/3` | 674–681 | `row_endpoint_plus_of` (RouteDR1) | E1Shape, TB.Kmom | proved* |
| TB.E1row | both branches (minus = plus at `(y⁻,y⁺)`, `σ ↦ −σ`) | 674–681 | `row_endpoint_of`, `greenP_neg`, `d1z_neg` (RouteDR1) | TB.E1row⁺, `lawE_swap` | proved* |
| TB.RE | `(2p−1)a²S^± − 2pa²T − B^± = ∓aΣR^±_i`; `|…| ≤ K₃p³/d` | 674–681 | `row_eq_exact`, `row_eq_of` (RouteDR1) | TB.root, TB.E1row | proved* |
| TB.B | `B^± ≤ 2.01ρ + 1.04/d + 3.03ε` for `ρ ≥ max(0, 1 − m^±)` | 682–686 | `rowB_le` (RouteDR1) | F2 (`k=2`), `d_mul_kappa_le` | proved* |
| TB.DR1 | `a² Σ_{i∼w} E(G⁺_wi − G⁻_wi)² ≤ K_DR δ̄/p`, `K_DR = 6.02K_δ + 8.14 + 2K₃` | DR1_CHECK §2 | `dr1_pt`, `dr1_of_c2` (RouteDR1) | TB.RE, TB.B, E1Shape, C2RowShape | proved* |
| TB.sub | star-substituted precision/weight/diagonals; Gaussian numerators `x_G, y_G`; masses `x, y` | 960–995 | `precSub`, `wSub`, `diagSub`, `wtHSub`, `kerL`, `gNumQ`, `gNumT`, `massQ`, `massT` (WT) | Defs (`tDir`, `tCav`, `wtH`) | defs |
| TB.WT3g | `𝖦[φ q_T] ≤ tr T · 𝖦φ` for measurable, nonnegative, even, midpoint log-concave `φ`, `T ⪰ 0` | 978–985 | `gaussE_mul_qForm_le_trace` (WT) | BLmid (`integral_quad_le_of_midpoint`), `gaussWt_midpoint`, `gaussE_eq` | proved* |
| TB.WT3a | `φ = W·H ≥ 0` (`wt3Rho`) | 960–975 | `wt3Rho_nonneg` (WT) | — | proved* |
| TB.WT3b | `φ(−x) = φ(x)`: gauge flip `P̃(−x) = D P̃(x) D`, `D = diag(−1 at i)` | 975 | `wt3Rho_even`, `precSub_neg`, `diagSub_neg`, `wSub_neg`, `posDef_flip_iff`, `det_flip_conj`, `inv_flip_conj_diag` (WT) | — | proved* |
| TB.WT3c | `φ` measurable (open PD set along the affine family, `measurable_matrix_inv`) | — | `wt3Rho_measurable`, `measurable_wSub`, `measurable_diagSub`, `continuous_precSub`, `precSub_isHermitian`, `isOpen_setOf_posDef_of_continuous` (WT) | — | proved* |
| TB.WT3d | `φ(z+w) φ(z−w) ≤ φ(z)²` when `|H₀| + 4 ≤ p` (log-concavity of `det`, of principal minors and of `det P/det(P+hY)`; convex support) | 960–975 | `wt3Rho_midpoint` (WT) | (X6) | proved* |
| TB.WT3 | `𝖦[W H q_L] ≤ tr L · 𝖦[W H]` per signing (`|H₀| + 4 ≤ p`) | 960–985 | `wt3_gauss` (WT) | TB.WT3g, TB.WT3a–d | proved* |
| TB.WT5 | `|x_G − x| + |y_G − y| ≤ K(p⁴/d)(x + y + d^{-M}) + e^{-p}` | 987–1071 | `wt5_transfer` (WT) | TB.WT5a, TB.WT5s, TB.WT5r, TB.WT5g | proved* |
| TB.WT5a | star resummation (exact): `x = Σ_σ 𝖱[W H q_L]/Z`, `y = Σ_σ 𝖱[tr L · W H]/Z`; `x_G`, `y_G` likewise with `𝖦` | 987–995 | `massQ_eq_radE`, `massT_eq_radE`, `gNumQ_eq`, `gNumT_eq`, `precSub_setRoot`, `wSub_setRoot`, `wtHSub_setRoot`, `kerL_setRoot` (WT) | `sum_sum_setRoot` | proved* |
| TB.WT5s | split (exact): `|Σ_σ(𝖦 − 𝖱)F_σ|/Z ≤ remSum + |retSum|` (E4 remainder at depth `k_* = kStarA d p`, retained grades `≥ 1`) | 987–1041 | `abs_sum_gauss_sub_rad_le`, `remSum`, `retSum`, `lJ`, `zero_mem_retIdx` (WT) | Compare (`retIdx`, `dEven`) | proved* |
| TB.WT5i | insertion at a real star vector (exact): `P̃(x) ≻ 0 ↔ q_A(x) < 1`, `det P̃(x) = det P̃_core · D_i(1 − q_A(x))`, `W(x) = W_core (D⁺_iD⁻_i)^p Φ(x)`; hence `F_σ = W_core (D⁺_iD⁻_i)^p F°_σ` (`starObsQ`, `starObsT`) | 960–975 | `wSub_eq_star`, `precSub_ins`, `ins_generic`, `quadForm_coreOf`, `colOf_precSub_quad`, `obsQ_eq`, `obsT_eq` (WT) | `SecA.coreOf`, `vertexSchur_*` | proved* |
| TB.WT5c | core-law forms (exact): `remSum = |E_core coreRem|/F_H`, `retSum = E_core coreRet/F_H`; core-measurability of `F°` | — | `remSum_eq_core`, `retSum_eq_core`, `sum_wtCore_div_Zw`, `dEven_const_mul`, `starObsQ_congr`, `starObsT_congr`, `precSub_congr'` (WT) | `sum_wt_mul_eq_star`, `SecA.coreE_div_coreE` | proved* |
| TB.WT5r° | own-core (E4) remainder: `|E_core coreRem(F°_Q)| + |E_core coreRem(F°_T)| ≤ F_H d^{-M-1}` | 1043–1071 | `wt5_rem_core` (WT) | E4, star smoothness/sup bounds (A-SMOOTH/A-MAJ generalised to shifted factors `1/α_h`), A-CREM, (M3), (M4), (E6) | proved* (94ce5f1; `SecB/WTRemCore.lean` from `WTRem{Star,Env,Fac,Maj,MajC,Der,Hder,Mom,Arith}.lean`, `SecA/TransRemLo.lean`, `SecA/ClipRecip.lean`) |
| TB.WT5g° | own-core retained grades: `|E_core coreRet(F°_Q)| + |E_core coreRet(F°_T)| ≤ K(p⁴/d)(x + y + d^{-M}) F_H` | 987–1041 | `wt5_ret_core`, `coreRet_div_insF_eq` (A-RET for the retained grades), `coreE_sum_mul`, `insF_pos_ct` (WT) | TB.WT5c, TB.WT5v, TB.WT5l, `SecA.lawE_eq_coreE_div`, `SecA.insF_pos` | proved* |
| TB.WT5v | vanishing: `∂^{2j}F°(ξ) = 0` at sign vectors with `Φ(ξ) = 0`, `1 ≤ |j|_g ≤ k_*` | — | `starObs_vanish` (`SecB/WTRetLaw.lean`); `starObs_dEven_eq_zero` (any real `ξ`), `shiftSub_posDef`, `gamT`, `gamT_eq` (`SecB/WTRetVan.lean`); `psiW`, `contDiff_det_of_entries`, `contDiff_adjugate_apply_of_entries` (`SecB/WTRetCalc.lean`). Route: if `q_A(ξ) > 1` or `q_B(ξ) > 1`, `F°` vanishes near `ξ`; otherwise `P̃(ξ) + hY ≻ 0` and near `ξ` `F° = c α₊^{p−|L|} β₊^{p−|L|} Π_t Γ_t · q` with smooth `Γ_t` (adjugates, cut-off `psiW`), so A-CLIP0 applies (order `2Σj ≤ 4k_* < p − m₀ − 4`, `RegA.moment_order_le`) | star form (R1), A-CLIP0 | proved* |
| TB.WT5l | retained grades under the actual law (TRC-G form): `|Σ_{1≤|j|_g≤k_*} c_j E[∂^{2j}F°(ξ)/Φ(ξ)]| ≤ K(p⁴/d)(x + y + d^{-M})` (both observables), `K = 52e²·676·1024²` | 987–1041 | `wt5_ret_law` (`SecB/WTRetLaw.lean`); pointwise `starObs_pointwise`, `facM_root`, `facM_weight_le`, `pderiv_shiftSub_apply` (`SecB/WTRetPt.lean`); `invSm_deriv_le` (`|∂^l(M⁻¹)_uw| ≤ r_u r_w |l|! Π 2|c_s| r_i r_s`), `rfBound_listProd`, `majBound_mul_len`, `quad_leibniz` (`SecB/WTRetCalc.lean`); weighted A-CNT `sum_topIdx_weight_le`, `sum_ret_weight_le` (`SecB/WTRetCnt.lean`); `X_sq_moment`, `coreShift_abs_le`, `trace_kerL_le`, `diagB_le`, `hN_pow_moment` (`SecB/WTRetMom.lean`); `retained_sigma_le`, `eventually_trunc`, `two_pow_mT` (`SecB/WTRetSum.lean`). Route: at a supported signing `ξ` is interior; near `ξ`, `F_Q = Φ̃ H̃ q_L`, `F_T = tr L Φ̃ H̃` with `Φ̃ = (1−q_A)^p(1−q_B)^p` (`MajAt`, `K = 4p`, weights `λ = lamR`) and `H̃ = Π_{t∈L'} y_k (M_t⁻¹)_kk` (rising factorials, weights `2a√(y_iX_ii)√(y_sX_ss) ≤ λ_s`); with `κ² = 26p²Z/d ≥ (5pλ_s)²` (`SecC.lam_sq_le`, `|L'| + 4k_* ≤ p`), `quad_leibniz` gives `|∂^{2j}F|/Φ ≤ H κ^{2Σj}(q + qd1_j/κ + qd2_j/κ² + tr L)`. The derivatives on `q_L` force `j_s ≥ 2` on their coordinates (weighted A-CNT: cost `x²T` instead of `1`); with `L = TᵀT`, `Σ_s|(Lξ)_s| ≤ tr L/κ + κ|N|q`, `Σ|L_st| ≤ |N| tr L`, grade `g` costs `26e²(676p⁴/d)^{g+1} X Z^{2(g+1)}`, `X = H(q_L + tr L)`. Truncation (`SecC.trunc_moment`, `Λ = 1024`, extra exponent `mT = ⌈(22+2M) log d⌉`) with `E X² ≤ d^{20}` (`|T_jl| ≤ d/h²`, `tr L ≤ d⁴/h⁴`, `q_L ≤ |N| tr L`, diagonals `≤ 3h^b_k`, A-HOLD; `1/h ≤ d` from `p ≥ ⌈1/κ₀⌉`) and `SecC.Z_moment_le`; geometric sum (`676·1024² p⁴/d ≤ 1/2`) | (WT4) endpoint bounds, A-CNT, truncation | proved* |
| TB.WT5r | `remSum_Q + remSum_T ≤ d^{-M-1}` | 1043–1071 | `wt5_rem` (WT) | TB.WT5c, TB.WT5i, TB.WT5r° | proved* |
| TB.WT5g | `|retSum_Q| + |retSum_T| ≤ K(p⁴/d)(x + y + d^{-M})` | 987–1041 | `wt5_ret` (WT) | TB.WT5c, TB.WT5i, TB.WT5g° | proved* |
| TB.abs | absorption `x ≤ 3y + ϑ + 4e` | 1072–1075 | `wt2_absorb` (WT) | — | proved* |
| TB.WT2 | `E[H q_L] ≤ 4E[H tr L] + 4d^{-M} + 4e^{-p}` | 913–1075 | `wt2`, `gNumQ_le_gNumT`, `wtH_nonneg` (WT) | TB.WT3, TB.WT5, TB.abs | proved |
| bridges | `E1Shape 4·10¹¹`, `CL1Shape K 1 1`, `C2RowShape K` from Section A | — | `e1_bridge`, `cl1_bridge`, `c2_bridge` (Export) | `CapPoint.endpoint_E1_cp`, `SecA.scalar_ineq`, `SecA.concentration_C2` | proved |
| exports | `in_S1`, `in_W5 m`, `in_W1` (literal copies of `Contact/Inputs.lean`), `in_DR1` | — | `SecB.in_S1`, `SecB.in_W5`, `SecB.in_W1`, `SecB.in_DR1` (Export) | above | proved |

## Exports vs `Tight/Contact/Inputs.lean`

* `SecB.in_S1`: literal copy of `in_S1`. Proved from TB.S1 + `cl1_bridge` (`C = K_S + 1`).
  Open below: only `SecA.scalar_ineq`.
* `SecB.in_W5 m`: literal copy of `in_W5 m`. Proved from TB.W5 + `cl1_bridge`. Open below: only
  `SecA.scalar_ineq` (UMI, T.DSTAR, F2 are proved).
* `SecB.in_W1`: literal copy of `in_W1`. Proved from TB.W1 + bridges. Open below: TB.W1fib-d1
  and TB.W1fib-d3 only (and the Section A bridges).
* `SecB.in_DR1` (new input of the DR1 route; no `in_DR1` exists in Inputs yet): at every contact
  and **every** `w ∈ S`, `a² Σ_{i∈N_S(w)} E(G⁺_wi − G⁻_wi)² ≤ C δ̄/p`. Proved from TB.DR1 +
  `e1_bridge`, `c2_bridge`. Open below: `CapPoint.endpoint_E1_cp`, `SecA.concentration_C2`
  (`kpoly_moment` is proved*).
* WT2 is not an Input (it is used inside the FS1 leaf of Section 1.5); its statement uses the
  cavity kernels `Contact.tDir`/`tCav` and weights `Contact.wtH` of `SecB/Defs.lean`.

## Checks (rule 2)

* Small cases: `S = ∅` (`t_h = 0`); isolated root (`N = ∅`: rows, scores, masks vanish; DR1 `0 ≤ …`;
  `J = ∅` in WT: `q_L = tr L = 0`); zero source `y_i = 0` (physical rows vanish; W2 `0 = 0`; S1w
  LHS `0`); zero plus source at `w` (DR1 becomes a minus-row bound, DR1_CHECK §2 / §5).
* Numerical: W2 residual `6·10⁻¹⁷`, W3 `4·10⁻¹¹` (AUDIT-B §6); DR1 identity on `K₂, K₄, K_{3,3},
  K₅, Q₃`, Petersen (DR1_CHECK §5).
* Parent checks compiled: `in_S1`, `in_W5`, `in_W1`, `in_DR1` from the nodes; `row_endpoint` from
  `row_endpoint_plus_of`; `row_endpoint_plus_of` from `E1Shape` and `kpoly_moment`; `row_eq_of`
  from `row_endpoint_of`; `dr1_of_c2` from `row_eq`, `rowB_le`, C2; `wt2` from WT3, WT5;
  `weak_loop_of` from `weak_targets` and `weak_ibp_of`; `weak_ibp_of` from TB.W1fib, TB.W1sec,
  TB.W1mask; `weak_fibre_of` from TB.W1fib-alg, TB.W1fib-edge, TB.W1fib-avg; `weak_fibre_edge`
  from TB.W1fib-ibp, TB.W1fib-reg, TB.W1fib-nonreg; `weak_fibre_reg` from TB.W1fib-end, -seg,
  -smooth, -d1, -d3; `wt3_gauss` from
  TB.WT3g and TB.WT3a–d.
* TB.W1fib-edge (2026-10-01): checked on a 6-vertex graph with the full paired law, all four
  configurations, `a = 0.08 … 0.01`: `max |Rem_ij|/a³` is constant (configurations 1, 3; `O(a⁵)` for
  2, 4) and `|Rem_ij|` divided by the bound with `C = 1`, `M = 6` stays `≤ 7.4·10⁻⁵`.
* W1 sub-nodes (2026-10-01): the exact algebra (`4T_k = −ε(a·wEdge + a²·wMain)` and TB.W2 summed)
  checked numerically with the full paired law on a 6-vertex graph, all four configurations
  (residual `≤ 2·10⁻¹⁷`); the derivative formulas of TB.W1fib (W3 with `ν = +`, `dbP`, `dbM`,
  `dOmP`, `dOmM`, `∂ log W = 2pa(G⁺_ij − G⁻_ij)`) by finite differences on a 7-vertex graph
  (residuals `5·10⁻¹³`, `6·10⁻⁹`). The asymptotic bounds themselves (`∃ C`, eventually) are not
  testable on small instances.
* WT3 sub-nodes: TB.WT3b and TB.WT3d checked numerically (6-vertex graph, `|H₀| = 4` with shifted
  and unshifted diagonals of both branches, `p = 8`): evenness exact; worst midpoint log-gap
  `log φ(z+w) + log φ(z−w) − 2 log φ(z) = −0.021` over 2756 pairs with both endpoints supported.
* TB.W1fib-reg sub-nodes (2026-10-01, numerically in the exact Lean model: normalized
  precisions with random sources `y ∈ [0.5, 1.5]`, physical `G`, `X`, 6-vertex graph, `p = 3`,
  `h = 0.3`, all 4096 fibres × 4 configurations, `a = 0.0025, 0.005, 0.0075` with 4096, 3072, 512
  regular fibres): TB.W1fib-seg — no failure of `P̃^±(t) ≻ 0` on `t ∈ [−2, 2]`; TB.W1fib-d1 —
  `|φ'(±1) − W DΨ|/(|WΨ| + |W DΨ|) ≤ 4·10⁻⁷` (central differences, step `10⁻³`; `5·10⁻⁵` at step
  `10⁻⁵`, floating-point noise); TB.W1fib-d3 — `sup_{[−1,1]}|φ'''|/(W(σ)Yb(σ) + W(σ')Yb(σ')) ≤
  4·10⁻⁷` (`M = 10`). Small cases: a fibre with `W(σ') = 0` cannot be regular unless `σ` is good,
  and then TB.W1fib-seg forces `W(σ') > 0`; `f = u` gives `∂f = 0` (`dbP`, `dbM` only for `b_±`).

## Decisions and deviations

* W1 is stated exactly as `in_W1` (configurations `(ε,ν) = (+,+)` with `H = Ω₊` and `(−,+)` with
  `H = Ω₋`, masks `u`, `b_σ`), i.e. the cases Section 1.5 uses; the paper's general `H ∈ {1, Ω₊,
  Ω₋}`, all `(ε,ν)` is not needed.
* TB.Dstar's constant is `3(1+d+d²)12^n` (the elementary `max` bound) instead of the draft's
  `(1+d+d²)10^n`; only W5 uses it.
* WT2 is stated with the constant `4` and floor `e^{-p}`; `H₀` is a list of at most `m₀`
  `(vertex, branch, shifted?)` diagonals; the radius-two restriction on its indices is dropped (not
  needed by the log-concavity argument, and the statement is stronger without it).
* The `B^±` bound uses `E h² ≤ 1 + 3ε` (F2, `k = 2`, `p ≥ 10⁶`) — slightly cruder than DR1_CHECK's
  `2.2ε`, absorbed in `K_DR`.

## Gaps / false statements

None found. No statement was weakened.

## Remaining `sorry`s (Section B)

None: every Section B node is proved* (last: TB.W1fib-d1 dd767f5, TB.W1fib-d3 a6694b9, TB.WT5v/WT5l
4b68f70, TB.WT5r° 94ce5f1; these hashes refer to the development history, which is not included in
this repository).

New nodes of TB.WT5r° (all proved*; small cases `x = 0`, `y_i = 0`, `N ∩ (S−i) = ∅`; the envelope
and the `α_h` lower bound checked on 2924 random instances):

| node | Lean | statement |
|---|---|---|
| A-REMlo | `CapPoint.crem_lo`, `trans_rem_lo` (`SecA/TransRemLo.lean`) | A-CREM/A-REM with own-core moments only for `n ≤ 2k*+3`; derivative factor `(8p)^{2Σj}` |
| A-MAJr | `SecA.CR.MajN`, `majN_recip`, `psiCut`, `pderivList_clipObs_le_majN` (`SecA/ClipRecip.lean`) | majorant algebra to order `N`; smooth reciprocal of a clip, constant `4(k+N)` |
| R1 | `WR.star_diag`, `star_factor`, `qForm_Az_le` (`SecB/WTRemStar.lean`) | Schur at `i` for `P̃(x)+zY`: diagonal `= c_t ñ_t/(1−q_{A_z})`, `0 ≤ q_{−ñ} ≤ q_{A_z} ≤ (D/(D+zy_i)) q_A` |
| R1′ | `WR.starObsQ_eq_clip`, `starObsT_eq_clip` (`SecB/WTRemFac.lean`) | `F_σ = clipObs G e₁ e₂ A B`, `e_{1,2} = p − #unshifted±` |
| R2 | `WR.env_qForm`, `env_trace`, `shift_energy` (`SecB/WTRemEnv.lean`) | `q_L ≤ c_L B`, `c_L = h⁻²(2/d)(1/h + 4Σ_{k∈N}(K⁰₊)_kk²)` |
| R3 | `WR.majN_G`, `deriv_interior`, `deriv_global`, `hder_Q/T`, `final_combine` (`SecB/WTRemMaj*.lean`, `WTRemDer.lean`, `WTRemHder.lean`) | `|∂^ν F_σ| ≤ m_σ (8p)^{|ν|} Π√b_s`, `m_σ = 0` off the core support |
| R4 | `WR.mom_X`, `mom_m`, `mQ_le`, `mT_le` (`SecB/WTRemMom.lean`) | `E X^q ≤ (2(2|R|+1)(1+2ε))^q` for `2q ≤ p`; `m ≤ C_m X^{|l|+3}` |
| arith | `WR.params_of`, `final_bound` (`SecB/WTRemArith.lean`) | thresholds `log d ≥ 128(m₀+3)`, `p ≥ (M+m₀+7)(log d+3)`, … |

`WTRemStar` imports `SecC.ShiftMat` (allowed: SecB may import SecC; no cycle).

## Notes for the coordinator

* `SecB/Defs.lean` is imported by `SecC/Defs.lean`; it must not import `SecA/Defs.lean`, because
  `SecA/Defs.lean` and `SecC/Defs.lean` both define `BiluLinial.Tight.kStar` (a clash as soon as both
  are imported together, e.g. by `BiluLinial.lean`).
* `SecB.hzN_le_hN` (proved) has the same statement as the `sorry` `SecA.hzN_le_hN`.
* The `lawE` helpers duplicated earlier were removed; `SecB` uses `SourceMax/Law.lean`.
* `SecA/Closure.lean` (source of `scalar_ineq`, `concentration_C2`) is untracked and was mid-edit,
  and `SecA/E1.lean` was being rebuilt, at the time of writing; `Export.lean` is the only SecB
  file importing them (all other SecB files take Section A inputs as the shapes `E1Shape`,
  `CL1Shape`, `C2RowShape`).
