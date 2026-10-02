# CHECK_SECS: pre-dispatch statement checks for Sections A–C (workflow rule 2)

Scope: every theorem stated in `BiluLinial/Tight/SecA/*.lean`, `SecB/*.lean`, `SecC/*.lean` and
`Tight/Star.lean`, against `docs/second_order_bilu_linial_tight.tex` (lines 237–1333),
`docs/tight/AUDIT_{A,B,C}.md` and `docs/tight/DR1_CHECK.md`, plus the interface to
`Tight/Contact/Inputs.lean`. No Lean file was edited.

**Read log (UTC, 2026-10-01).** The files were being edited during the check; every section below
was re-read before it was written.

| files | first read | last re-read (file mtime, UTC) |
|---|---|---|
| `Contact/Inputs.lean`, `Contact/Defs.lean`, `Ctx.lean`, `Params.lean`, `Defs.lean` | 05:23 | 05:23 (Inputs 05:19) |
| `SecA/{Defs,Reg,Conc,Transfer,Star,Closure,Shift,Moments,ParP,Ins,WAvg}` | 05:24–05:27 | 05:41 (mtimes 05:37–05:39) |
| `SecA/{Endpoint,E1,Export}` (new during the check) | 05:36 / 05:40 | 05:41 |
| `SecB/{Defs,LawE,Arith,S1,RouteDR1}` | 05:25–05:26 | 05:39 (mtimes 05:25–05:37) |
| `SecB/Weak.lean` (new) | 05:41 | 05:41 (mtime 05:40) |
| `SecC/{Defs,Regime,Root}`; `SecC/{RowCompare,MarkEnv,Shifted,Transfer,Mark,Deriv}` (new) | 05:26; 05:31–05:37 | 05:41 |
| `Star.lean` | 05:25 | 05:41 (mtime 05:24, sorry-free) |

Scripts written (all run with `/tmp/tight-venv/bin/python`, total runtime about 4 minutes):

- `scripts/tight/check_secs_enum.py`: exact enumeration of the paired law and the own core law in
  the **Lean normalized formulation** (`precN`, `precCore`, `greenP`, `hN`, `hzN`, `shiftP`,
  `coreGreen`, `coreShift`, `rootMat`, `rootMzG`, `rootSigns`), 180 instances: graphs `K4`, `K33`,
  `star+`, `P4`, `K2`, `C5`; `p ∈ {3,5,12}`; `d ∈ {max deg, max deg + 3}`; random sources in
  `[0, s]` with zero plus-root source, zero neighbour sources, `S ⊊ V`, and `S = {v}`.
- `scripts/tight/check_secs_sym.py`: symbolic (sympy, symbolic `p`) fibre-polynomial identities.
- `scripts/tight/check_secs_star.py`: Gaussian star-level inequalities by quadrature (dim 1, 2).
- `scripts/tight/check_secs_mark.py`: T.MARK by exact polynomial arithmetic along lines/planes.
- `scripts/tight/check_secs_regime.py`: PARP and E6 at the regime boundary (mpmath, 400 digits),
  A-CNT by brute force.
- `scripts/tight/check_secs_dups.py`: duplicate fully qualified names in `BiluLinial/Tight`.

---

## 0. Summary

**No statement was found FALSE.** Every exactly checkable identity holds to `10⁻¹⁴`, and every
inequality with an explicit constant holds on all instances, including the degenerate ones.

Items for the coordinator, in order of urgency:

1. **Compile error outside my scope (hard clash).** `Contact/Chain1.lean:28` declares
   `BiluLinial.Tight.lawE_const_mul` and imports `Tight.SourceMax`, which imports
   `SourceMax/Law.lean:49` with the same fully qualified name ("already declared"). Delete the
   Chain1 copy.
2. **Hard clash, latent.** `BiluLinial.Tight.clipPow` is defined in `SecC/Defs.lean:51`
   (`p m m' A B x`) and in `Gauss/GCIEllipsoid.lean:182` (`A p x`). Any file importing both fails.
   The GCI files are slated for deletion on the DR1 route (DR1_CHECK §6.1); until then, rename one.
3. **`in_whiten`: proof-route constraint (statement OK).** `SecA.whiten` is correct, but it must
   not be proved from `SecC.core_transfer` (T.TRC): that node assumes `0 ≤ w ≤ d^{20}` on the core
   support, and `w = tr A²/(1+tr A)` is **not** bounded there (`G_K` blows up near the boundary of
   the PD cone, which the continuum of sources reaches). Truncating at `d^{20}` fails too, since the
   floor costs `40^p ≫ d^{20}`. Use the moment-hypothesis transfer `CapPoint.trans` (A-TRANS), whose
   `hmom` holds for `w ≤ tr A ≤ U_K` by (M3), plus an interpolation bound on its grade-one term.
4. **`row_endpoint` minus conjunct needs a swap lemma.** `SecA.endpoint_E1` and
   `CapPoint.endpoint_E1_cp` cover only the plus row `G⁺_vi`. The minus conjunct of
   `SecB.row_endpoint` (and of W1's endpoint step) follows from the law symmetry
   `(y⁺, y⁻, σ) ↦ (y⁻, y⁺, −σ)`, under which `G⁻_vi ↦ G⁺_vi` and `σ_vi z_i ↦ −σ_vi x_i`. Only the
   `hN`-power case exists (`lawE_hN_neg_pow_swap`, SourceMax). Add a node `lawE_swap_neg` for
   general observables, checked as in rule 2.
5. **`in_markenv` first conclusion.** `Srow/d ≤ 4λ`, with the literal constant 4, does not follow
   from `SecC.mark_envelope`, which gives `C·λ`. It follows directly: `d a² ≥ 1/4`
   (`TRegime.d_aOf_sq`) and `trA2 ≥ 0`. The second conclusion is literally `mark_envelope` (`markE`
   is `frobP`).
6. **Route: Contact layer still on GR1.** `Contact/RouteGCI.lean` (`in_GR1`) and
   `Contact/RouteD9a.lean` use GR1. On the DR1 route they should take `in_DR1 ← SecB.dr1_of_c2`
   (with `C2RowShape ← SecA.concentration_C2`) and `in_CR3′ ← SecC.row_comparison_diff`. **No
   section statement assumes GR1.** `SecC.row_comparison_split` (CR3) is the GR1-route variant,
   but it is conditional and not wrong. CR1 (`row_comparison`) uses only `δ` for the minus marks.
7. **Duplicates and ambiguity hazards** (§7): `hzN_le_hN` exists in SecA and SecB with
   **different argument orders**. `eventually_base` exists in SecB and SecC with **different
   conclusions**. `qRoot_eq_qForm` and `rootMat_congr` appear twice, and the `lawE_*` helpers
   three times. Two sorried statements duplicate proved ones: `SecC.qRoot_eq_qForm` duplicates the
   proved `Star.qRoot_eq_qForm`, and `SecA.CapPoint.exists_defZMax` duplicates the proved
   `SecB.CapPoint.defZMax_tShift`. The sorried `SecC.lawE_eq_coreE_rad`, SecA's `lawE_eq_coreE_div`
   and the proved `Star.lawE_eq_star` are three forms of the same identity. `SecC.insFH_ge` equals
   `SecA.CapPoint.floor`.
8. **Name resolution in `RouteDR1.lean`.** Under `namespace BiluLinial.Tight` + `open SecB`, the
   identifiers `lawE_add/sub/const_mul/congr/nonneg` resolve to `BiluLinial.Tight.*` from
   `SourceMax/Law.lean`, not to `SecB.*`: the current namespace shadows `open` (confirmed with a
   scratch Lean file, `/tmp/check_secs_ns.lean`, at 05:44). Law.lean is now
   sorry-free, so this is harmless, but `proved*` of RouteDR1 depends on it. Prefer explicit
   `SecB.` or one shared copy.

---

## 1. Route check: `SecB/RouteDR1.lean` against DR1_CHECK §2

Verdict: **OK, exactly DR1_CHECK §2**, with weaker but valid constants. Only `row_endpoint` is
open.

- **Identity.** `row_eq_exact` (proved) gives the two branch identities of DR1_CHECK §2.2 step 3
  verbatim:
  - `(2p−1)a²S⁺ − 2pa²T − B⁺ = −aΣR⁺_i`;
  - `(2p−1)a²S⁻ − 2pa²T − B⁻ = +aΣR⁻_i`.

  Here `R^±_i = E[σ_wi·] − E[𝒟₁·]`, with `𝒟₁` given by `d1x` and `d1z`, which are the DR1_CHECK step
  2 formulas. Adding them and using `rowDiff_eq` (`ΣE(x−z)² = S⁺+S⁻−2T`) gives
  `(2p−1)a²ΣE(x−z)² = B⁺+B⁻+2a²T+E3`, `E3 = −aΣR⁺+aΣR⁻`. Re-checked numerically in the Lean
  normalized form: residual `4.6·10⁻¹⁵` (180 instances, including zero sources and `S={v}`).
  `rowBP` uses `D_w·E h_w = Z_w E G_ww` ✓.
- **Bound.** `dr1_pt` uses `2T ≤ S⁺+S⁻` (`two_rowT_le`): no sign of `T`, so no GCI.
  `rowB_le` gives `B ≤ 2.01ρ + 1.04/d + 3.03ε`, against DR1_CHECK's `2.3ε` and `1.03/d`. The Lean
  constants are weaker because `E h_w h_i ≤ 1+3ε` is used, and they are valid. `dr1_of_c2` gives
  `a²ΣE(x−z)² ≤ K δ̄/p` with `K = 6.02K_δ + 8.14 + 2K₃`; the arithmetic was re-derived and is
  correct. DR1_CHECK's `K_DR = 12.7 + K₃` uses `p³/d ≤ δ/(K_δp)`, while Lean uses the cruder
  `p³/d ≤ δ̄`. Both give `δ̄/p`, because the factor `2p−1` sits on the left.
- **`row_endpoint` (TB.E1row, sorry).** OK.
  - Sketch: E1 at the edge `wi` (`CapPoint.endpoint_E1_cp` once `w` is a root) gives
    `|E[σx] − E𝒟₁x| ≤ |E𝒟₃x|/3 + 4·10¹¹p⁵a⁵`, and `𝒟₃x = a³K_i` (symbolic check below).
  - `|K_i| ≤ Cp³g*⁴` (`|U| ≤ 2pg*`, `|V| ≤ 2pg*²`, `|W| ≤ 8pg*³`), and `E g*⁴ ≤ C` by (M1). Then
    `p²a² ≤ 1` gives `K p³a³`.
  - The minus conjunct needs the swap lemma (item 4).
  - Info only: the ratio `|E[σx]−E𝒟₁x|/(p³a³|N|)` is at most `0.82` on the instances.
- **GR1 use.** None. AUDIT_D's claim that W1's remainder needs GR1 is answered by
  `SecB.weak_loop_of`, which takes only `C2RowShape` and `CL1Shape` ✓.

---

## 2. Section A (`SecA/*.lean`)

Regime: `RegA d p` (`TRegime`, `log d ≥ 400`, `120 log d ≤ p`). The graph-level nodes are
`∃ C, ∀ d p, RegA d p → ∀ cp : CapPoint d p`, which is stronger than `Eventually`.
`eventually_regA` (proved) bridges the two. I checked that nothing in the sketches needs more
than `RegA`. Hölder and interpolation losses use `log d ≤ p/120`, and moments of order
`8k_*+12 ≤ p/2` hold by `RegA.moment_order_le`.

### `Reg.lean` (all proved)
OK. Closure inequalities, `k_*` facts and `eventually_regA`.

### `ParP.lean` (A-PARP; 11 sorries)
All **OK**, by exact algebra and by high-precision margins at
`p ∈ [10⁶, 10²⁰]`, `d ∈ [p^{17/2}, 10³⁰⁰]`. All margins are positive. The smallest are
`2·10⁻¹⁶⁰` for `η₀ − 3/q`, `2 − s` and `1 − d a²s²` at `d = 10³⁰⁰`, `0.005` for `1/200 − ε`, and
`0.01` for `51/100 − L/D`.

- `three_div_le_η0Of`: `qη²+Δη−Δ` at `η = 3/q` is `≤ 0` iff `9p+12 ≤ 4q` ⟸ `p ≤ 2q/9` ✓.
- `sOf_le_two`: `⟺ η₀ ≥ 2τ_*` ✓.
- `d_mul_kappa_le_one`: `⟺ q²η₀ − 3q(1−η₀) + (1−η₀)² ≥ 0`; I re-derived this equivalence ✓.
- `inv_d_le_epsP`, `epsP_le`, `cEdge_le`, `Lsum_le_one`, `Csum_le`, `diagD_le_two`,
  `diagD_eq_one_add_L_sub_C`, `Lsum_div_diagD_le` ✓ (worst case `L/(1+L−C) ≤ 1/(2−1/d)`).

### `WAvg.lean` (A-HOLD, A-INTERP)
OK. Weighted AM–GM and Hölder for the measure `X·w`.

### `Moments.lean` (A-MT)
- `Zw_pos`, `ZwCore_pos`, `h_moment`: OK. `(pr−k)/(p−k) = 1+pε/(p−k) ≤ 1+2ε` for `k ≤ p/2`,
  and `k+2 ≤ p` ✓.
- `core_moment`: OK.
  - Sketch: the inherited core law is the law of `J = S−v` at deletion sources `ŷ ≤ y`, so
    `(precCore⁻¹)_ii = (ŷ_i/y_i)h^J_i(ŷ) ≤ h^J_i(ŷ)`. Apply (F2) for `J` (from `ih`/`TInv J`).
  - Indices `i ∉ S∖{v}` give the identity row, value `1` ✓.
- `floor`: OK (`floor_ins`).

### `Ins.lean` (A-INS, A-ROOTPSD, A-C3)
- `wtCore_congr`, `rootMat_congr`, `coreShift_congr`, `rootMat_posSemidef`: OK (core signs only;
  `G_K ≻ 0` gives `A ⪰ 0`).
- `lawE_eq_coreE_div` (A-INS): OK. It follows from the proved `Star.lawE_eq_star` with
  `f σ = g σ ξ_σ`. Enumeration residual `3·10⁻¹⁵`.
- `insF_pos`: OK.
- `schur_C3`, `schur_C3_minus`: OK, exactly.
  - Sketch: INS with `g = f₁/Φ = (trA−q_A)/α = 1+(trA−1)τ⁺`, then (F1) `trA·τ⁺ = a²Σ(G_vvG_ii−G_vi²)`.
  - Residual `4·10⁻¹⁵` on both branches.
  - At `S={v}` and at an isolated root, both sides are `0` ✓.

### `Star.lean` of SecA (star level)
- `contDiff_posPow`, `contDiff_clipObs`, `pderivList_clipObs_eq_zero`, `smoothBdd_clipObs`: OK.
- `pderivList_clipObs_le_of_interior` (A-MAJ): OK. Per quadratic, `|∂^νq| ≤ m2^nλ^ν`; the
  multinomial identity gives `(2K)^n` for `K = 1+e₁+e₂` factors.
- `pderivList_clipObs_le` (A-E5): OK. QuadMaj of `1−q_A` with `λ_i = √b_i` follows from
  `(Ax)_i² ≤ A_ii q_A ≤ A_ii` and `|A_ij| ≤ √(A_iiA_jj)`.
- `iter_pderiv_clipObs_le` (A-EPB4): OK (one-variable coefficient majorant).
- `gaussE_C4` (A-CR, (C4) l.469–476): OK.
  - Sketch: Cramér–Rao `Σ ⪰ (I+E∇²V)⁻¹`, then `tr(M(I−Σ)) ≤ tr(M E∇²V)` for any `M ⪰ 0`, and
    `∇²(−log α) = 2A/α + 4Axxᵀ A/α²`.
  - Numerical: 978 nondegenerate quadrature cases, `max (lhs−rhs)/|rhs| = −0.006`, so nearly
    tight for small `A`. At `A=B=0` both sides are exactly 0.
- `pdom`: OK. `‖M‖_F ≤ ‖A‖_F` for `0 ⪯ M ⪯ A`, `AMA ⪯ A³ ⪯ ‖A‖²A`,
  `BMB ⪯ ‖M‖‖B‖B ⪯ ΘB`. Random matrices: violation `3·10⁻¹⁵` (roundoff).
- A-C1b moved to `Tools/Cov.gaussE_NG_ge_whitened`: OK. `G[Φ]·w(A) ≤ G[f₁]` for `p ≥ 2`; all
  cases `≤ 0`.

### `Transfer.lean`
- `sum_topIdx_prod_pow_le` (A-CNT): OK. Brute force gives `max lhs/rhs = 0.19`.
- `RegA.E6`: OK. `max (log LHS + p) = −8.7·10⁶` over the `RegA` boundary (`log d ≥ 400`,
  `120 log d ≤ p ≤ d^{2/17}`). In the worst direction, `p ≈ d^{2/17}`, the coefficient of `p` is
  `log 40 + 64(2/17) − 16 ≈ −4.78`.
- `crem`: OK. `x = 2.01/d`, `T = 1/(2x)` gives `(4.02/d)^{k+1}(1+x)^d ≤ (5/d)^{k+1}e³`, with Hölder
  order `≤ 2k+3`.
- `trans_rem`, `coreE_radE_div_eq` (A-RET, INS with `g = R/Φ`), `hgr` (A-CNT with `T = 1/(dL⁴)`,
  `(1+2/d)^d ≤ e²`), `trans` (grade 0 cancels, grade 1 kept with `c₂ = 1/12`, grades `≥ 2` via
  `hend`/`hgr`): OK. These need `|c_j| ≤ 1`. The coefficients of `e^{t²/2}/cosh t` are
  `1, 0, 1/12, −1/45, …` and decay like `(2/π)^{2j}` ✓.

### `Endpoint.lean`, `E1.lean`
- `det_add_rank_two`, `inv_add_rank_two_apply`: OK (symbolic `0` residual).
- `fibrePoly_coeff_one`, `fibrePoly_coeff_three`: OK. sympy with symbolic `p` gives
  `1![t¹]Π − a(−P+(2p−1)x²−2pxz) = 0` and `3![t³]Π − a³·Kpoly = 0`, and the minus fibre
  `𝒟₁z` also matches `d1z` ✓.
- `endpoint_E1` (constant `1.15·10⁹`): OK.
  - On omitted endpoints (`64pag* > 1`), `64⁵ + 4·64⁴ + 64·4096/3 = 1.141·10⁹`, using
    `|𝒟_jψ| ≤ (4pa)^j g*^{j+1}` from `δ_± ≪ (1+ag*t)²`.
  - On regular fibres, `2·(13/60)·4⁵e^{1/8}·…` is about `5·10²`. The Peano check gives
    `L(t⁵) = 16 ≤ (13/60)·120` ✓.
- `endpoint_E1_cp` (`4·10¹¹`): OK, since `1.15·10⁹·275 = 3.2·10¹¹` and
  `E g*⁶ ≤ 4(2·1.01)⁶ = 273`.

### `Conc.lean` (C1, C3, C3a, C3b)
- `bias_C1a`: OK. `|E_{ν_K}(N_R−N_G)| ≤ C(p⁴/d)F_H` is (C1) l.375 times `F_H`.
- `row_bound`: OK. (C3) + C1a + `N_G ≥ 0` give `a²ΣEG_vi² ≤ C_v + D_vρ + L_v((1+2ε)²−1) + Cp⁴/d`.
- `second_moment`: OK. `Eh² ≤ (1+2ε)² ≤ 1+5ε` and `Eh ≥ 1−ρ` give `≤ 5ε+2ρ`; the sharp value
  is `4ε+2ρ+4ε²`.
- `whiten`: OK as a statement. INS gives `E_H w = E_{ν_K}[w𝖱Φ]/F_H`, and A-C1b pointwise gives
  `w𝖦Φ ≤ 𝖦f₁`. The transfer error `C(p⁴/d)(E w + d^{-10})` has to come from A-TRANS with moments,
  not from T.TRC (item 3).
- `wK_mean_le_one`: OK. `w ≤ trA ≤ U`, `E U ≤ U₀(1+2ε) ≤ 0.52`.
- `core_kernel`, `preclosure_C3b`: OK. `trace_sq_le_two_wK` is proved.
- `core_tail`: OK, explicit. `k = ⌊p/4⌋`, `‖U‖_k ≤ 0.51(1+2ε) ≤ 0.52`, and
  `0.52^{⌊p/4⌋} ≤ e^{-p/10}` for `p ≥ 11`. Also `trA ≤ U` by `coreGreen_le_greenP`, and
  `trA² ≤ (trA)²` for PSD `A`.

### `Shift.lean` (C5, C4 transfer, C6)
Enumeration covers the pointwise facts on the support, with `z = 0.37`, both branches, zero
sources included:

| statement | check | worst |
|---|---|---|
| `hzN_pos` | `min hzN` on support | `0.43 > 0` |
| `hzN_le_hN` | `max(hzN−hN)` | `0` (exactly, at zero source) |
| `coreShift_le_shiftP` (`i≠v`), `coreGreen_le_greenP`, `coreShift_le_coreGreen` | max differences | `0` |
| `sum_shift_sub_core_le` (C5c) | `max(lhs−rhs)` | `0` |
| `inv_hzN_root` (C5d) | identity | `9·10⁻¹⁶` |
| `sum_coreShift_mul_coreGreen_le` (C5e), `ν = ±` | `max(lhs−rhs)` | `0` |
| `qForm_Mz_le` (C5f), both conjuncts | `max(lhs−rhs)` | `0` |

Sketches:

- **C5c.** `a²X_vv ξᵀC_z[N,N]²ξ ≤ (X_vv/z)(X_vv⁻¹−G_vv⁻¹−z)` and `G_vv⁻¹ ≤ Z_v` (`h_v ≥ 1/D_v`).
- **C5e.** `tr(C_z C_ν) ≤ ½trC_z² + ½trC_{z,ν}² + ‖C_z‖ tr(C_ν−C_{z,ν})` and
  `trC_z[N,N]² ≤ z⁻¹tr(C−C_z)[N,N]`. This holds for any real `τ` given `precCore τ y ≻ 0`.
- **C5f.** `(Aξ)_iτ⁺ = −aG_vi` (F1) and `‖M_z‖ ≤ a²y_v/(D_vz)`.

The remaining statements:

- `DefZLe.defLe`: OK (`hz ≤ h`).
- `transfer_C4T`: OK.
  - Sketch: INS, then (C4) pointwise in the core, then A-TRANS on `F₀…F₄` (A-PDOM, A-EPB4 for
    `F₀`), then INTERP with `ρ`.
  - Stating it with the unshifted `ρ` instead of the paper's `t` is fine, since `ρ ≤ t`.
- `transferred_TT`: OK.
  - Sketch: `tr(M_zB)τ⁻ = a⁴G⁻_vv tr(C_{z,+}C_−)/Z⁺_v ≤ (2a⁴s/z)·G⁻_vv·dW` (C5e).
  - Then `E W ≤ C(t+ε)(1+1/(dz))`, from `C−C_z ⪯ (G−X_z)+(X_z−C_z)` and C5c.
  - Hölder with `t+ε ≥ ε ≥ 1/d` (PARP) and `a⁴d ≤ 1/(4d)`.
- `bias_C6`: OK (`C4T` at `M = M_z`, then `TT`).

### `Closure.lean`
- `scalar_ineq`: OK.
  - Sketch: maximizing `(v,±)`, Jensen on C5d, `D_v trM_z = a²y_vΣC_{z,ii}`,
    `C_{z,ii} = X_{z,ii} − (X−C)_ii`, then C5c and `E(h_v−h_{z,v}) ≤ ε+θ`, which gives
    `θ²/(1−θ) ≤ (L_v−1)θ − C_v + err`.
  - `z > 0` is unrestricted above; for `z ≥ 1/C` the claim is trivial since `θ ≤ 1`.
- `CapPoint.exists_defZMax`: OK, and already proved as `SecB.CapPoint.defZMax_tShift`.
- `theta_bound` (`z = u²`, `θ ≤ (2K+5)u`), `concentration_C2`: OK.

### `Export.lean`
These are literal copies of the Inputs statements (§6). The derivations are recorded there.

---

## 3. Section B (`SecB/*.lean`)

- `LawE.lean`, `Arith.lean` (renamed `regime_*`), `Defs.lean`: proved or definitions; OK.
- `S1.lean` (all proved): `s1_scalar_real`, `s1_scalar`, `mean_shift_pt`, `defZMax_tShift`,
  `eventually_h_facts`, `mean_shift_of_cl1`. OK.
  - Hypothesis interface: `CL1Shape K 1 1` ⟸ `SecA.scalar_ineq` + `eventually_regA`. The
    reasons: `bCL 1 = b0Of`, `1/d ≤ z ⟺ 1 ≤ dz`, `z ≤ 1` is unused, and the extra `+1/d` is
    harmless.
  - Pointwise sign `G_ii − X_ii ≥ 0`: minimum over the enumeration `0` (zero source), otherwise
    `> 0`.
  - `K_S` depends only on `K` ✓ (quantifier order).
- `RouteDR1.lean`: §1.
- `Weak.lean` (new):
  - `shift_row_identity`, `weak_w2`: proved; (W2) l.760 ✓.
  - `ward_diag`: OK. `G − X = hGX`, which commute, give `(G−X)/h − X² = hG X² ⪰ 0`. Enumeration:
    `max((XX)_ii − (G_ii−X_ii)/h) = 0` (zero source), `< 0` otherwise. Indices `k ∉ S` give
    `X_ik = 0` ✓.
  - `mean_shift_weighted_of_cl1`: OK.
    - Sketch: `‖Y‖_{k′} ≤ (EY)^{(k−2)/(k−1)}‖Y‖_k^{1/(k−1)}`, with `‖Y‖_k ≤ 2y_i` (F2) and
      `EY ≤ (K_S+1)√h y_i`.
    - `(2/√h)^{1/(k−1)} ≤ e` because `k−1 ≥ log d + 1 ≥ log(2√d)`, using `h ≥ 1/d`.
    - Result `e(K_S+1)B√hy_i ≤ 3(K_S+2)B√hy_i` ✓.
  - `dstar_moment`: OK. `(1+max)^n ≤ Σ_{w,±}(1+G^±_ww)^n`, the ball has at most `1+d+d²`
    vertices, and `2·3.02^n ≤ 10^n`.
  - `ward_mean_of_cl1` (= `in_W5 m`): OK. `ward_diag` and S1w with `Z = D_*^m` and
    `k = ⌈log d⌉+2` give `B ≤ (1+d+d²)^{1/k}10^m ≤ e³10^m`; `mk ≤ p/2` holds eventually.
  - `weak_loop_of` (= `in_W1`): OK.
    - The four expansions (bilinearity, `K_σ` symmetric):
      - `(+,+), f=u`: `q₊−ζ−t₊`;
      - `(+,+), f=b₊`: `ζ−z₊−α`;
      - `(−,+), w = u+b₋`: `q₋+ζ₋−t₋` and `ζ₋+z₋−β`.
    - `dOmP = −aG_vvG_viG_vj` and `dOmM = (a/2)(G⁺_vvG⁻_viG⁻_vj − G⁺_viG⁺_vjG⁻_vv)` were
      re-derived from (E3).
    - Uses `C2RowShape` (`ρ_row ≤ Cp⁻²`) and `CL1Shape`; no GR1, no DR1 ✓.
    - The endpoint step on interior edges `ij` needs a general first-order endpoint lemma. It
      shares its proof with `endpoint_E1` and could be one node.

---

## 4. Section C (`SecC/*.lean`)

- `Regime.lean` (proved): OK.
- `Deriv.lean` (CR2, proved): OK.
- `Root.lean`:
  - `qRoot_eq_qForm`: OK, a duplicate of the proved `Star.qRoot_eq_qForm`.
  - `lawE_eq_coreE_rad`: OK, a duplicate of A-INS.
  - `insFH_ge`: OK, a duplicate of `CapPoint.floor`.
  - `root_F1`: OK. All identities hold to `3.6·10⁻¹⁵`. At `y_v = 0` both sides are `0`
    (`t₊ = 1 = 1/α`).
  - `rowNum_eq`: OK (`5.9·10⁻¹⁷` relative).
  - `frob_root_le`: OK (`min(rhs−lhs) = 0` at `y_v = 0`, `> 0` otherwise).
  - `shiftQ_eq`: OK (`3·10⁻¹⁶`). Pointwise, no support needed: `Y_±` are symmetric even when
    singular, by `transpose_nonsing_inv`.
- `Mark.lean` (T.MARK):
  - `rowNum_line`: OK (relative residual `1.4·10⁻¹³`).
  - Explicit-constant bounds on 400 random instances, `dim ≤ 3`, `p ∈ {8,9,12,20}`,
    `a ∈ [0.02, 1]`:
    - `mark_grade_one` (1000): `max |∂⁴F|/bound = 7.5·10⁻⁴`;
    - `mark_grade_two_diag` (10⁶): `6.8·10⁻¹⁰`;
    - `mark_grade_two_mixed` (10⁶): `8.6·10⁻⁹`.

    All OK with large margins.
- `MarkEnv.lean` (`mark_envelope`): OK.
  - Sketch: `frob_root_le` and `(a⁴d²)⁻¹ ≤ 16`, then INTERP with floor `ϑ = d⁻¹⁰` and
    `k = ⌈10 log d⌉`.
  - Moments come from `tr A² ≤ U²` and `R ≤ a²ΣG_vvG_ii`.
- `RowCompare.lean`:
  - `row_comparison_split` (CR3): OK; the GR1-route form.
  - `row_comparison_diff` (CR3′): OK. It matches DR1_CHECK §3 exactly. The bound `δ_c ≤ 1` is
    rightly dropped, since `p⁴λ_r ≤ p⁴√(λ_cδ_c)` needs only `λ_r ≤ λ_c ≤ δ_c`. `diffRowE` is
    literally `SecB.rowDiff`.
  - `row_comparison` (CR1, proved from CR3 + MARKENV): OK. The contact hypothesis of the paper
    is unused (AUDIT-C G4).
  - Degenerate `N = ∅`: `𝓡 = 0` and `rowNum ≡ 0`, so `Gterm = 0` ✓.
- `Transfer.lean` (`core_transfer`, T.TRC): OK *as stated*, with `0 ≤ w ≤ d^{20}` and core
  functional `w`, `m_± ≤ 3`.
  - Grade 0 is exact by INS + F1.
  - The B4 instances satisfy the bound: `trM² ≤ |N|(sa²/z)² ≤ 2.25d^{19}` for `z ≥ ϑ`.
  - It does not apply to `w = tr A²/(1+trA)` (item 3).
- `Shifted.lean`:
  - `shift_mat_facts`: OK. Enumeration on the core support gives PSD violation `2·10⁻¹⁸`
    (roundoff) for `A,B,M,𝒩 ⪰ 0`, `M ⪯ A`, `𝒩 ⪯ B`, `M,𝒩 ⪯ (sa²/z)I`.
  - `shift_trace_bounds`: OK.
  - `gauss_rowNum_ge` (B25): OK. Quadrature, `p ∈ {4,5,8,20}`, dims 1–2, random
    `0 ⪯ M ⪯ A`, `0 ⪯ 𝒩 ⪯ B`, `m₀ ≥ max‖·‖`: every nondegenerate case satisfies `lhs ≤ 𝖦F`.
  - `shift_interp` (B3): OK (INTERP).
  - `b_assembly_real` (proved).
  - `rowGauss_ge_shiftQ`, `shifted_trace_comparison` (B1): OK. These are (B1) l.1192–1207 with
    `η_BL = C(p⁴/d+p/(dz))` and `ε_BL = C(p⁵+p²/z)ϑ+e^{−2p}` for every `z ∈ [ϑ,1]`.
- `Defs.lean`: the duplicate `kStar` is resolved. SecA renamed its copy `kStarA`, with the same
  definition `⌈16p/log d⌉₊`, so SecA's `RegA` facts transfer to SecC's `kStar` by `rfl`.

---

## 5. `Tight/Star.lean`

Sorry-free: `setRoot`, `radPi_eq_sum`, `radE_eq_sum`, `sum_sum_setRoot`, `qRoot_eq_qForm`,
`PhiRoot_eq_starPhi`, `sum_wt_mul_eq_star`, `lawE_eq_star`. Statements OK. The consequence A-INS
was re-checked numerically (`3·10⁻¹⁵`). Degenerate `S={v}` gives `𝖱h = h(0)`, `Φ = 1` ✓.

---

## 6. Interface: `Contact/Inputs.lean` ← section exports

| input | export (file) | relation |
|---|---|---|
| `in_E1` | `SecA.in_E1` (`SecA/Export.lean`) ← `CapPoint.endpoint_E1_cp` (`E1.lean`) | **literally identical**; `Contact.toCapPoint`, `ct.N = cp.N v`, `ct.sx` = `E[sgn·gp]`; `Kpoly` arguments in the same order |
| `in_C2` | `SecA.in_C2` ← `concentration_C2` (`Closure.lean`) | identical; `u ≤ δ̄`, `trA² ≤ Θ` (`tr B² ≥ 0`, `B` symmetric) |
| `in_C1` | `SecA.in_C1` ← `Tools/Cov.gaussE_NG_ge_whitened` + `Tools/GIBP2.two_mul_gaussE_starF` + `SecA.rootMat_posSemidef` | identical; needs the small conversions `starF = rowNum` for `p ≥ 1` (`((p−1:ℕ):ℝ) = p−1`) and `f1Obs = (trA−q_A)·starG` (`clipProd`); `Gterm ≥ 0` also when `F_H = 0` (junk `x/0 = 0`) |
| `in_whiten` | `SecA.in_whiten` ← `SecA.whiten` + GIBP2 (`E_{ν_K}N_G/F_H = 2a²·Gterm`) | identical (`d^{-10} = vth d`); see item 3 for the proof route |
| `in_C3a` | `SecA.in_C3a` ← `trace_sq_le_two_wK` + `core_tail` | identical; `e^{-p/10} ≤ d^{-10}` eventually (`p ≥ 100 log d`) |
| `in_markenv` | `SecC.mark_envelope` (`MarkEnv.lean`) | second conjunct literal (`markE = frobP`, `incRowE = Srow`, `trSqE = trA2`); first conjunct `Srow/d ≤ 4λ` direct from R2 (item 5) |
| `in_B1` | `SecC.rowGauss_ge_shiftQ` (`Shifted.lean`) at `z = h` | follows: `rowGauss` ≡ `Gterm`, `shiftQ` ≡ `Qbl` (same expressions); `h ∈ [ϑ,1]` and `e^{−2p} ≤ ϑ` eventually; `Q ≥ 0` (needed when enlarging `C`) |
| `in_S1` | `SecB.mean_shift_of_cl1` (`S1At`, `S1.lean`) + `CL1Shape` ← `SecA.scalar_ineq` | follows; `S1At` gives `(K_S+1)√h y_i`, the literal form |
| `in_W5 m` | `SecB.ward_mean_of_cl1 m` (`Weak.lean`) | **literally identical**, given `CL1Shape` |
| `in_W1` | `SecB.weak_loop_of` (`Weak.lean`) | **literally identical**, given `CL1Shape`, `C2RowShape` |
| (new) `in_DR1` | `SecB.dr1_of_c2` (`RouteDR1.lean`) + `C2RowShape` ← `SecA.concentration_C2` | for D9a′/FS5′ on the DR1 route; replaces `in_GR1` of `Contact/RouteGCI.lean` |
| (new) `in_CR3′` | `SecC.row_comparison_diff` | replaces CR3 in `Contact/RouteD9a.lean` |
| `in_GR1` (RouteGCI) | none (GR1 deleted on the DR1 route) | delete |

Missing shared hypotheses: `CL1Shape K 1 1` and `C2RowShape K_δ` must be discharged from SecA
(`scalar_ineq`, `concentration_C2`) by a small bridge lemma. Both are pure re-packagings:
`CapPoint` gives the same objects, and `rowSP` is definitionally `Σ_{i∈cp.N w} cp.E(cp.gp σ w i²)`.

---

## 7. Duplicate names (`scripts/tight/check_secs_dups.py`, run 05:41)

**Hard clashes** (same fully qualified name, error if co-imported):

- `BiluLinial.Tight.lawE_const_mul`: `Contact/Chain1.lean:28` and `SourceMax/Law.lean:49`.
  Chain1 imports SourceMax, so this is an **active error**.
- `BiluLinial.Tight.clipPow`: `SecC/Defs.lean:51` and `Gauss/GCIEllipsoid.lean:182`.
- Resolved since the start of the check:
  - `kStar` (SecA/Defs vs SecC/Defs; SecA's copy is now `kStarA`);
  - `qRoot_eq_qForm`, `PhiRoot_eq_starPhi`, `radE_eq_sum` (SecA/Ins vs Star.lean), now taken from
    Star;
  - the `TRegime.epsP_le` / `epsP_nonneg` / `p8_le` collision in Arith, renamed `regime_*`.

**Same name in different sub-namespaces** (ambiguous or silently shadowed under `open`):

| name | copies | note |
|---|---|---|
| `hzN_le_hN` | `SecA` (Shift:58, sorry), `SecB` (LawE:143, proved) | **different argument order** (`hz hy hP i` vs `hP hz hy i`) |
| `eventually_base` | `SecB` (Arith:25), `SecC` (Regime:38) | **different conclusions** (SecB also gives `h = κ₀/p⁴`, `0<κ₀≤1`) |
| `qRoot_eq_qForm` | root (`Star.lean`, proved), `SecC` (Root:203, sorry) | different argument order |
| `rootMat_congr` | `SecA` (Ins), `SecC` (Root, proved) | different hypothesis form (`AgreeOff` vs `∀ e, v ∉ e → …`) |
| `wt_nonneg`, `Zw_nonneg`, `lawE_add/sub/const_mul/congr/nonneg` | root (`SourceMax/Law`), `SecB` (LawE), `SecC` (Root) | identical statements; root shadows `open SecB` in RouteDR1 (item 8) |
| `lawE_mono` | `SecB`, `SecC` | identical |
| `in_E1`, `in_C2`, `in_C1`, `in_whiten`, `in_C3a` | root (Inputs), `SecA` (Export) | intended (exports to plug in) |

---

## 8. Reproduce

```bash
/tmp/tight-venv/bin/python scripts/tight/check_secs_enum.py    # ~8 s
/tmp/tight-venv/bin/python scripts/tight/check_secs_sym.py     # ~3 s
/tmp/tight-venv/bin/python scripts/tight/check_secs_mark.py    # ~9 s
/tmp/tight-venv/bin/python scripts/tight/check_secs_regime.py  # ~2 s
/tmp/tight-venv/bin/python scripts/tight/check_secs_star.py    # ~3 min
/tmp/tight-venv/bin/python scripts/tight/check_secs_dups.py    # <1 s
```
