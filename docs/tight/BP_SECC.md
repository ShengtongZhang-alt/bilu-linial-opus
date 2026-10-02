# BP_SECC — Section 1.4, lines 1077–1333 (fresh-star row energies)

Source `docs/second_order_bilu_linial_tight.tex`, Section 1.4: Lemma "Contact row comparison"
(CR1)–(CR3) and Lemma "Multiplicative shifted trace comparison" (B1)–(B5). Audit
`docs/tight/AUDIT_C.md` (§1 setting, §2 regime R1–R9, §3 tools, §4 restatements, §5 BLmid);
GCI-free route `docs/tight/DR1_CHECK.md` §3 (CR3′). Independent statement check:
`docs/tight/CHECK_SECS.md` (no false statement; Mark constants `1000`, `10⁶` hold with margin).
Lean files: `BiluLinial/Tight/SecC/`.

## Conventions

* Quantifiers: every analytic node is `∃ C, Eventually fun c₀ κ₀ d p h => ∀ V G S λ y⁺ y⁻ v, …`
  (absolute constants first, then `κ₀, c₀`, then the degree threshold; uniform in the graph).
* Context "Cap(H, y)" (AUDIT-C §1): `CapCtx G d p S λ`, sources in `[0, λ s]^V`, `v ∈ S`. A contact
  (`ContactCtx`, `Contact d p`) is such a point.
* Reused definitions: `rowNum` (`F`), `coreShift` (`(P_K + zI)⁻¹`), `vth` (`ϑ`) from
  `Contact/Defs.lean`; `lawE_*` from `SourceMax/Law.lean`; the star decomposition
  (`qRoot_eq_qForm`, `lawE_eq_star`, `radE_eq_sum`, `setRoot`) from `Tight/Star.lean`; Tools
  (`Cov.lean` B2, `MatrixFacts.lean` B5 and T.MAT, `Alpha2.lean`, `Interp.lean` T.IL).
* New definitions (`SecC/Defs.lean`): `kStar`, `clipPow`, `starAlpha`, `starRow`, `starCore`,
  `starMark`, `starScale`, `CoreInv`, `rootT`, `incRowE`, `diffRowE`, `markE`, `trSqE`, `rowMean`
  (= `Contact.Rrow`), `insFH`, `rowGauss` (= `Contact.Gterm`), `shiftY`, `shiftM`, `shiftQ`
  (= `Contact.Qbl`), `shiftX1`, `shiftX2`. The `Contact.*` quantities are definitionally the
  unbundled ones (used by `change` in `SecC/Export.lean`).
* `e^{-cp}` of the source is `e^{-3p}` (CR, T.TRC) or `e^{-2p}` (B1); both are `≤ ϑ` eventually.

## DAG

Status: `proved*` = this node and everything below it sorry-free; `proved` = own proof
sorry-free (may use stated nodes); `stated` = Lean statement with `sorry`.

| id | statement | source | Lean (file) | deps | status |
|---|---|---|---|---|---|
| PD | regime R1–R9: `p⁸ ≤ d`, `1/4 ≤ d a² ≤ 1/2`, `s ≤ 3`, `K log d ≤ p`, `2(8k_*+12) ≤ p`, `ϑ^{-1/k} ≤ e` (`k ≥ 10 log d`), `(8dp + 24p²d¹⁰)e^{-3p} ≤ e^{-2p}`, `e^{-2p}, e^{-3p} ≤ ϑ`, `h ∈ [ϑ,1]`, E6 with exponent 4 | AUDIT-C §2 | `eventually_regime`, `TRegime.p8_le`, `TRegime.d_aOf_sq`, `TRegime.sOf_le_three`, `TRegime.pow_le_d`, `eventually_log_le`, `eventually_le_log`, `eventually_kStar`, `vth_rpow_neg_le`, `eventually_exp_absorb`, `eventually_exp_le_vth`, `eventually_h_mem`, `forty_le_exp`, `eventually_E6` (`Regime.lean`) | D-params | proved* |
| CR2 | `D_iα = 2x_iα`, `D_ix_j = -x_ix_j - c_ij`, `D_ic_kj = -2x_ic_kj - x_kc_ij - c_kix_j` (minus branch: `a ↦ -a`) | l.1102–1127 | `hasDerivAt_starAlpha`, `hasDerivAt_starRow`, `hasDerivAt_starMark`, `starAlpha_line`, `mulVec_line` (`Deriv.lean`) | — | proved* |
| ROOT-core | `coreE` linear/monotone on the core support; `precCore`, `rootMat`, `shiftM`, `wtCore` are core functionals; `precCore`, `A` symmetric, `tr A² ≥ 0` | — | `coreE_add/sub/const_mul/mono`, `precCore_congr`, `rootMat_eq_of_offRoot`, `shiftM_congr`, `coreInv_of_mats`, `precCore_isHermitian`, `rootMat_apply_comm`, `trace_rootMat_sq_nonneg` (`Root.lean`) | — | proved* |
| ROOT-law | `E ψ = E_{ν_K}𝖱[ψΦ]/F_H` for core-invariant `Ψ` | l.135–141 | `lawE_eq_coreE_rad` (`Root.lean`) | D-star (`lawE_eq_star`) | proved* |
| FLOOR | `F_H ≥ 40^{-p}` at a capped point | l.143–186 | `insFH_ge`, `insFH_pos` | D-floor, D-del, D-transfer, D-star | proved |
| ROOT-supp | support facts: `W ≠ 0 ⇒ W_core ≠ 0`, `t_± ≥ 0`, `h^-_v > 0`, `|N| ≤ d`, cube inclusion | — | `wtCore_ne_zero_of_wt`, `rootT_nonneg`, `hN_pos_minus`, `card_nbhd_le`, `inCube_of_cap`, `diagD_pos` | D-ins | proved* |
| SCHUR | off `v`, column `j` of `P⁻¹` is `P_c⁻¹(e_j' - (P⁻¹)_vj b)`; `(P⁻¹)_vv(P_vv - bᵀP_c⁻¹b) = 1` | — | `inv_col`, `inv_diag` (`F1.lean`) | — | proved* |
| F1 | on the support: `t = 1/α`, `G_vj = x_j`, `G_vvG_ij = c_ij` (one branch, `τ = ±1`; both branches) | (F1) l.137–141 | `root_branch`, `root_F1` (`F1.lean`) | SCHUR, D-star (`qRoot_eq_qForm`) | proved* |
| ROWF | `F(ξ) = a²Φ(ξ)𝓡_v` at sign endpoints | l.141, AUDIT-C §1 | `rowNum_eq` (`F1.lean`) | F1, T.MARK-line | proved* |
| FROB | `a⁴G_vv²‖G[N,N]‖_F² ≤ 2t₊²trA² + 2(a²Σx²)²` (both branches) | l.1135–1140 | `frob_of_marks`, `frob_branch`, `frob_root_le` (`F1.lean`) | F1 | proved* |
| QPHYS | `(p-1)E X₁ + p E X₂ = a² Q` | l.1323–1325 | `shiftQ_eq` (`Root.lean`) | `coreShift` symmetric | proved* |
| T.MARK-line | `F(x+te_i) = a²α^pβ^p Σ_j[(p-1)u_j²ρ₊^{p-2}ρ₋^p - p u_jw_jρ₊^{p-1}ρ₋^{p-1}]` | AUDIT-C §9 | `rowNum_line` (`Mark.lean`) | CR2 (`starAlpha_line`, `mulVec_line`) | proved* |
| T.MARK-1 | `|∂_i⁴F| ≤ a⁶Φ(1+r_i)⁴·1000·[p⁵|Σx_j(x_j-z_j)| + p⁴Σ(marks)]` | l.1153–1190 | `mark_grade_one` | T.MARK-line | proved* |
| T.MARK-2 | `|∂_i⁶F|`, `|∂_i⁴∂_k⁴F| ≤ … 10⁶ p⁹ Σ(two marks)` | l.1153–1162 | `mark_grade_two_diag`, `mark_grade_two_mixed` | T.MARK-line | proved* |
| T.TRC | `|E_{ν_K}𝖦[wα^{p-m₊}β^{p-m₋}]/F_H - E[w t₊^{m₊}t₋^{m₋}]| ≤ C(p⁴/d)(x_w+ϑ) + e^{-3p}`, `0 ≤ w ≤ d²⁰` on the core support, `m_± ≤ 3` | l.1281–1310, AUDIT-C §3 | `core_transfer` (`Transfer.lean`) | E4, E5, CREM, T.IL, ROOT-law, F1, FLOOR, PD | proved (open below: SecA A-REM `CapPoint.trans_rem`, A-SMOOTH, A-E5, A-CLIP0, A-MAJ) |
| MARKENV-row | `a²S_τ + E trA_τ² ≤ λ ⇒ S_τ/d ≤ 4λ` | l.1131–1133 | `mark_envelope_row` (`MarkEnv.lean`) | ROOT-core, PD | proved* |
| MARKENV-frob | `… ⇒ d⁻²E[(G_vv)²‖G[N,N]‖_F²] ≤ Cλ` (`λ ≥ ϑ`) | l.1135–1148 | `mark_envelope_frob` | FROB, T.IL, F2, PD | proved* |
| MARKENV | both, `C = max(4, C_F)` | AUDIT-C §4.2 | `mark_envelope` | MARKENV-row, MARKENV-frob | proved* |
| CR3 | `|𝓡 - 𝖦F/(a²F_H)| ≤ C{p⁵√(λ_rρ_r) + p⁴√(λ_cδ_c) + p¹³/d²} + e^{-3p}` | (CR3) l.1170–1190 | `row_comparison_split` (`RowCompare.lean`) | E4, T.MARK, F1, ROWF, ROOT-law, T.IL, T.DSTAR, E5, CREM, FLOOR, PD | proved (open below: `row_grade1_le`, `row_grade2_le`; `row_grade3_le` proved*, `RowG3.lean`) |
| CR3′ | as CR3 with `ρ_Δ` (difference energy) for the `p⁵` term, `δ_c` for the minus row | DR1_CHECK §3 | `row_comparison_diff` | as CR3 | proved (open below: `row_grade1_le`, `row_grade2_le`; `row_grade3_le` proved*, `RowG3.lean`) |
| CR1 | `ϑ ≤ λ ≤ δ`, `a²S₊+EtrA² ≤ λ`, `a²S₋+EtrB² ≤ δ` ⇒ `|𝓡 - 𝖦F/(a²F_H)| ≤ C{p⁵√(λδ) + p¹³/d²} + e^{-3p}` | (CR1) l.1078–1168 | `row_comparison` | CR3, MARKENV | proved |
| SHIFTMAT | on the core support: `A,B,M,𝒩 ⪰ 0`, `M ⪯ A`, `𝒩 ⪯ B`, `M,𝒩 ⪯ (sa²/z)I` | l.1216–1221 | `inv_quad_antitone`, `inv_quad_le_of_diag`, `compR`, `shift_branch` (`ShiftMat.lean`), `shift_mat_facts` (`Shifted.lean`) | — | proved* |
| TRB | `0 ≤ trM² ≤ |N|m₀²`, `0 ≤ tr(M𝒩) ≤ |N|m₀²` | T.MAT (i),(ii) | `shift_trace_bounds` | T.MAT | proved* |
| B25 | `𝖦F ≥ (p-1)trM²𝖦[α^{p-2}β^p] + p tr(M𝒩)𝖦[α^{p-1}β^{p-1}] - 4p²m₀(trM²𝖦[α^{p-3}β^p] + tr(M𝒩)𝖦[α^{p-1}β^{p-2}])` | (B2),(B5) l.1215–1317 | `gauss_rowNum_ge` | Tools B2 (`gaussE_starPhi_B2_le`: GIBP2 + BLmid + ALPHA2 + T.MAT), B5 (`trace_mul_hess_sq_div_le'`) | proved* |
| B3 | `E[X₁t₊ + X₂t₋] ≤ C(E[X₁+X₂] + ϑ)` | (B3) l.1259–1279 | `shift_interp` | T.IL, F2, Schur order, PD | proved* |
| B4-real | real assembly with explicit `C = max(8C_TR, 12K₁)`, `K₁ = (1+C_TR)C_B3 + 2C_TR` | l.1319–1328, AUDIT-C §4.3 | `b_assembly_real`, `b_assembly_real'` | — | proved* |
| B4 | `𝖦F/(a²F_H) ≥ (1 - C(p⁴/d + p/(dz)))Q - C(p⁵+p²/z)ϑ - e^{-2p}`, `z ∈ [ϑ,1]` | l.1319–1328 | `rowGauss_ge_shiftQ` | SHIFTMAT, TRB, B25, T.TRC, B3, QPHYS, FLOOR, ROOT-supp, PD, B4-real | proved (open below: SecA leaves of T.TRC) |
| QNN | `Q ≥ 0` | l.1197 | `shiftQ_nonneg` | QPHYS, SHIFTMAT, TRB | proved* |
| B1 | `𝓡 ≥ 𝖦F/(a²F_H) - E_row ⇒ 𝓡 ≥ (1-η_BL)Q - E_row - ε_BL` | (B1) l.1205 | `shifted_trace_comparison` | B4 | proved (open below: SecA leaves of T.TRC) |
| EXPORTS | literal copies of `in_markenv`, `in_B1` (`Contact/Inputs.lean`), `in_CR3` (`Contact/RouteGCI.lean`) | — | `in_markenv_pf`, `in_B1_pf`, `in_CR3_pf` (`Export.lean`) | MARKENV, B4, QNN, CR3, PD | proved (`in_markenv_pf` proved*) |

## Sketches (with constants)

**PD.** `d a² = d/(4d - 4 + 4/p) ∈ [1/4, 1/2]`; `s = (2-η₀)/(1-τ_*)`, `τ_* ≤ 1/q ≤ 1/3`;
`p¹⁶ ≤ p¹⁷ ≤ d²`. `log d = o(d^{2/17})` (`isLittleO_log_rpow_atTop`) gives `K log d ≤ c₀d^{2/17}/2
≤ p`. E6: `(Cp)⁸ ≤ d` once `p ≥ C¹⁶`, so `(Cp)^{4k}/d^k ≤ d^{-k/2} ≤ e^{-8p}` (`k ≥ 16p/log d`),
`40 ≤ e^{3.9}`, `p(Cp)⁴ ≤ e^{p/10}` for `p ≥ 7!·10⁷C⁴`: `≤ e^{-4p}`.

**CR2.** Quotient rule on `x_j(t) = -((Ax)_j + tA_ji)/(a(α - 2t(Ax)_i - t²A_ii))`, then
`(Ax)_j = -aαx_j`, `A_ij = a²α(c_ij - x_ix_j)`.

**ROOT-law.** `lawE_eq_star` (D-star) gives `E f = Σ W_core 𝖱[Φ f(setRoot σ ·)]/Σ W_core 𝖱Φ`;
`Ψ(setRoot σ ξ) = Ψ σ` (root pairs contain `v`), `ξ(setRoot σ ε) = ε` on sign vectors
(`radE_eq_sum`); divide numerator and denominator by `Z_core` (both vanish if `Z_core = 0`).

**FLOOR.** Exactly the floor side of the induction (`floor_pos`): deletion congruence, IH means
`≤ r ≤ 1.01`, `floor_ins`; `Σ W_core Φ(ξ(σ)) = Σ W_core 𝖱Φ` from `sum_wt_mul_eq_star` with `f = 1`
and `wt_eq_wtCore_mul`, cancelling `(D_v⁺D_v⁻)^p > 0`.

**MARKENV-row.** `S ≥ 0`, `tr A² ≥ 0` (symmetric `A`), `S = S·1 ≤ S·4da² ≤ 4d(λ - E trA²)`.

**MARKENV-frob.** Frobenius bound, `a⁴d² ≥ 1/16`, then T.IL (`k = ⌈10 log d⌉`, moments `≤ p/2`)
for `E[t₊² trA²]` and `E[R²]`, `R = a²Σ_N G_vj²`, with mass `≤ λ` and floor `ϑ ≤ λ`.

**T.MARK.** Line representation (exact, from `(Ax+tAe_i)_j = -aα u_j(t)` and
`α(x+te_i) = αρ₊(t)`); coefficient majorants `ρ_± ≪ (1 + a r_i t)²`; `∂_i⁴F = 24[t⁴]`. The base
part `Σ_j[(p-1)x_j²c₁ - px_jz_jc₂] = pc₂Σx_j(x_j - z_j) + ((p-1)c₁ - pc₂)Σx_j²` with
`|pc₂| ≤ (32/3)p⁵a⁴r⁴` and `|(p-1)(c₁-c₂) - c₂| ≤ 41p⁴a⁴r⁴` (`ρ₋ - ρ₊` has no constant term); all
other terms carry a core mark with coefficient `≤ 22p⁴a⁴r³` or `8p³a⁴r²`. Grade 2: `720[t⁶]`,
`576[t⁴s⁴]` with `ρ_± ≪ (1 + ar_it + ar_ks)²` (`|e_ik| ≤ √(e_iie_kk)`).

**CR3/CR3′.** (E4) with `k = k_*` pointwise in the core; grade 0 = `𝓡` (ROOT-law, ROWF); grade 1:
T.MARK-1 at endpoints (F1), summed over `i,j` (`a⁴|N| ≤ a²/2`), Cauchy–Schwarz in the law, T.IL
(`m = λ_r, λ_c ≥ ϑ`, unmarked `(1+r_i)⁴ ≤ CD⁴`, `‖D⁴‖_{2k} ≤ C` by T.DSTAR + F2): CR3 uses
`|Σx(x-z)| ≤ Σx² + |Σxz|`, CR3′ uses `|Σx(x-z)| ≤ √(Σx²)√(Σ(x-z)²)`; grade 2 costs
`C(p⁹/d)√(λ_cδ_c) ≤ Cp⁴√(λ_cδ_c)`; grades `≥ 3`: `Σ_g p(Cp)^{4g}d^{1-g} ≤ Cp¹³/d²`; remainder:
E5 sup bound, CREM, FLOOR, E6 (exponent 4), `a⁻² ≤ 4d`: `≤ e^{-3p}`.

**CR1 (proved).** CR3 with `λ_r = λ_c = C_MEλ`, `ρ_r = δ_c = C_MEδ`; `C = 2C_CR C_ME`.

**B25 (proved).** Write `p = q+4`, `u = α`, `w = β`. On `{u,w > 0}`: B5 times `Φ/2` gives
`Φ tr(MH²)/(2α) ≤ 4p²m₀(trM²u^{q+1}w^{q+4} + tr(M𝒩)u^{q+3}w^{q+2})`, so the lower integrand is
`≤` the expanded B2 integrand `g`; off the support both vanish (`p ≥ 4`). `|g| ≤
(q+4)(T₁+T₂) + 4(q+4)²m₀(T₁+T₂)` gives integrability; integrate and use Tools B2,
`starF = rowNum`.

**B4 (proved).** B25 on the core support (SHIFTMAT), `coreE` monotone and linear, divide by
`F_H > 0` (FLOOR); T.TRC for `(w,m₊,m₋) = (trM²,2,0), (tr(M𝒩),1,1), (trM²,3,0), (tr(M𝒩),1,2)`
(`w ≤ |N|m₀² ≤ d·(3d⁹/2)² ≤ d²⁰` for `z ≥ ϑ`); B3; `(p-1)x₁+px₂ = a²Q` (QPHYS); B4-real:
`x ≤ 2a²Q/p`, `a⁻² ≤ 4d`, `sa²d ≤ 3/2`, `1/z ≤ d¹⁰`, `(8dp + 24p²d¹⁰)e^{-3p} ≤ e^{-2p}`.

**SHIFTMAT.** `(P̃_K + zY_K)⁻¹ ⪯ P̃_K⁻¹` (antitonicity) compressed by `√y`; `wᵀ(P̃+zY)⁻¹w ≤
wᵀ(zY)⁺w` for `w ∈ range Y` (variational formula), i.e. `Y ⪯ z⁻¹I`; `a²y_v/D_v ≤ a²s`.

**B3.** `X₁ ≤ μ_A²t₊²`, `X₂ ≤ μ_Aμ_Bt₊t₋`, `μ_A ≤ (a²y_v/D_v)Σ_N G_ii` (Schur order), F2 moments,
T.IL with `Y = t₊ + t₋`, `k = ⌈10 log d⌉`.

**T.TRC.** See the module docstring of `Transfer.lean` (grade-`g` term `(Cp⁴/d)^g E[X Z_g]`, T.IL
with `k_g = ⌊p/(C'g)⌋`, remainder `d²⁰ e^{-4p} ≤ e^{-3p}`).

## Checks (rule 2)

* Parent checks done (compile): CR1 ⇐ CR3 + MARKENV; MARKENV ⇐ row + frob; B4 ⇐ SHIFTMAT + TRB +
  B25 + T.TRC + B3 + QPHYS + FLOOR + PD (+ B4-real); B1 ⇐ B4; QNN ⇐ QPHYS + SHIFTMAT + TRB;
  exports ⇐ MARKENV halves, B4, QNN, CR3, PD.
* Small cases: `N = ∅` (rowObs `= 0`, `rowNum = 0`, `𝖦F = 0`; CR3/CR1 trivially true; B25 `0 ≤ 0`;
  T.TRC exact since `𝖦f = 𝖱f = w`); zero source at `v` (`G_vv = 0`, `x = 0`, `A = M = 0`; FROB,
  MARKENV, QPHYS give `0`); one coordinate `B = 0`, `A = (α₀)`: `∂⁴F(0) = -24(p-1)(p-2)α₀³` against
  the grade-1 bound `≥ 6000p⁴α₀³`; B25 with `A = M = (α₀)`, `B = N = 0` is the 1-D covariance
  bound `𝖦[α^{p-2}] - 𝖦[x²α^{p-2}] ≲ 2p α₀ 𝖦[α^{p-3}]`.
* Statement check `CHECK_SECS.md`: no false statement.

## Gaps and deviations

* G4 (AUDIT-C): the contact hypothesis of CR1 and the upper bounds `δ_c ≤ 1` are not needed; the
  envelope floor `λ ≥ ϑ` is a hypothesis.
* T.TRC requires `0 ≤ w ≤ d²⁰` on the core support; the whitening instance `wΦ` of D6 is not
  covered (Section A proves it via `CapPoint.trans`).
* E6 is used with exponent 4 (to absorb the `d²⁰` envelope), valid at `p ≤ d^{2/17}` (exponent
  `→ -4.78p`), not at `p ≤ d^{1/7}`.
* No false statement found.

## Remaining `sorry`s

`Mark.lean`: `mark_grade_one`, `mark_grade_two_diag`, `mark_grade_two_mixed`.
`Transfer.lean`: `core_transfer`. `MarkEnv.lean`: `mark_envelope_frob`. `RowCompare.lean`:
`row_comparison_split`, `row_comparison_diff`. `Shifted.lean`: `shift_interp`.

Plan: B3 (`shift_interp`) and MARKENV-frob from T.IL (`wavg_mul_le_interp`) with the moment
toolkit of Section A (`CapPoint.h_moment`, M1: `E h^k ≤ (1+2ε)^k` for `2k ≤ p`), Schur order
`G_{K,ii} ≤ G_ii` (from `inv_col`) and `μ_A ≤ a²s Σ_N G_ii`; T.MARK from `rowNum_line` with
polynomial coefficient majorants; then T.TRC and CR3/CR3′ from (E4) and Section A's E5/CREM/HGR.
