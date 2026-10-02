# BP_CONTACT — the Section 1.5 chain (contact estimate and conclusion)

Blueprint fragment for node `D-contact` (`exists_contact_free`, `BiluLinial/Tight/Contact.lean`).
The coordinator merges it into `docs/BLUEPRINT.md`. Source: `docs/second_order_bilu_linial_tight.tex`
lines 1334–2073 (Section 1.5), with the inputs of Sections 1.2–1.4. Audits: AUDIT-C §6 (D1–D10),
AUDIT-D §3 (D1–D16 and the conclusion), AUDIT-D §1.3/§4.1 (quantifiers), AUDIT-D §2.6 (UMI),
AUDIT-B §3.3 and `docs/tight/DR1_CHECK.md` (GCI-free route).

Files (all under `BiluLinial/Tight/Contact/`):

| file | content |
|---|---|
| `Defs.lean` | bundled contact `Contact d p`; deterministic parameters (`epsP, LbarP, LdP, cpP, vth, thP, dbar, GamP, eP, B0P, epsS, xiP`, error aggregates `ErowP, etaBL, epsBL, Err10, ErrRC3, Err12, TotErr`); the quantities at a contact (`Contact.*`); `Kpoly`, `rowNum`, `maskF`, `coreShift`; the regime `Reg` |
| `Real.lean` | regime helpers (proved), `param_facts`, all real-number lemmas `R-*` (leaves) |
| `Inputs.lean` | route-independent inputs `I-*` from Sections 1.2–1.4 |
| `RouteDR1.lean` | **active route (GCI-free)**: inputs all-vertex C2, DR1-from-C2, CR3′; node `in_DR1`; real lemma R-CR1′; node `cr1` (proved) |
| `Leaves.lean` | analytic leaves `L-*` of Section 1.5 |
| `Chain1.lean` | proved nodes LOOP, F3sum, D3, D4, D6, D7 (imports `RouteDR1`) |
| `RouteDR1D9a.lean` | **active route**: real lemma R-D9a′; node `d9a` (proved) |
| `RouteGCI.lean`, `RouteD9a.lean` | **inactive** paper route (GR1, CR3): `cr1_gci`, `d9a_gci`; compile, not imported by the chain |
| `Chain2.lean` | proved nodes D9b, D10, E-c, FS6, RC3, D12, D15, final |

`Tight/Contact.lean`: `exists_contact_free` is **proved** from `contact_final` and `ledger_choice`.

## 0. Design

**Bundled contact.** `Contact.{u} d p` packages a vertex type, a graph, `S`, `λ`, `(y⁺, y⁻)`, the
root `v` and a proof of `ContactCtx G d p S λ y⁺ y⁻ v`. `ContactFree d p` holds iff
`Contact d p` is empty (used directly in the proof of `exists_contact_free`). Every quantity of
Section 1.5 is a function of a contact (and of the shift `h` for shifted objects); every node is a
statement `∀ ct : Contact d p, …`.

**Quantifiers.** Every input, leaf and node has the form
`∃ C > 0, Eventually fun c₀ κ₀ d p h => ∀ ct : Contact d p, …` (`Eventually` from `Tight/Ctx.lean`:
for all `c₀, κ₀ ∈ (0,1]` there is `D(c₀, κ₀)` with the statement at all `d ≥ D`,
`p = ⌊c₀ d^{2/17}⌋`, `h = κ₀ p^{-4}`). So constants are absolute (chosen first), then `κ₀, c₀`, then
the threshold — AUDIT-D §4.1. The real lemmas have the shape
`∃ C > 0, [∀ κ₀ ∈ (0,1] | ∀ c₀ κ₀ ∈ (0,1]], ∃ P₀, ∀ d p h, Reg κ₀ d p h → P₀ ≤ p → …` and are
turned into `Eventually` statements by the proved helpers `Eventually.of_real`, `of_reg`,
`of_treg`, `of_treg_h` (using `eventually_reg`, `eventually_ge`). The only node whose conclusion
depends on `c₀, κ₀` is `contact_final`:
`∃ Ccrit > 0, Eventually fun c₀ κ₀ d p h => Ccrit(√κ₀ + c₀^{17/3} + κ₀⁻² c₀^{34/3}) ≤ 1/8 → no contact`.

**Constants and exponential terms.** The source's `δ = C{ε + p⁴/d + (p/d)^{1/3}}` is `C·dbar`;
`δ_row = C δ/p`; `e = p√δ_row/(√d h) = C·eP`; `ε_s = C·epsS`. Every `e^{-cp}` of the source is
written `C ϑ` with `ϑ = d^{-10}`: equivalent under `Eventually` because `p ≥ c₀d^{2/17}/2`
(so `e^{-cp} ≤ d^{-10}` for `d ≥ D(c₀, c)`), and it keeps every error term a monomial in `d, p, h`.

**Zero sources.** All quantities are physical (`greenP`, `shiftP`, `coreShift` have zero rows at
zero sources), so no statement divides by a source. Padding outside `S`: `shiftP` has junk diagonal
`y_j` at `j ∉ S`, but every quantity only reads entries indexed by `S` (energies: `u`, `b_±` are
supported in `S`; scores: `i ∈ N`, `j ∼ i`; `D_*`: `N ∪ N(N) ∪ {v} ⊆ S`); checked for each
definition.

## 1. Node table

Status: `proved` = own proof sorry-free (uses stated children); `stated` = `sorry`. Route column: **R**
= route-dependent (GCI route), swapped under DR1.

### Inputs (Sections 1.1–1.4)

| id | informal statement (at the contact) | source | Lean (file) | deps (informal) | status |
|---|---|---|---|---|---|
| I-E1 | `\|E[ξ_ix_i] − a(−EP_i + (2p−1)Ex_i² − 2pEx_iz_i) + (a³/3)EK_i\| ≤ Cp⁵a⁵`, `i ∈ N` (E1 with `𝒟₁, 𝒟₃` explicit, KID) | l.261–293, 1370–1391 | `in_E1` (Inputs) | E3, Taylor endpoint identity, F2 | stated |
| I-C2 | `a²S₊, a²S₋, E trA², E trB² ≤ C δ̄` | l.378–385 | `in_C2` | C1, C3–C6 closure | stated |
| I-C1 | `Gterm = E_{ν_K}𝖦F/(a²F_H) ≥ 0` | l.373–397, 1249 | `in_C1` | BLmid (a), GIBP2 | stated |
| I-whiten | `Ew ≤ 2a²Gterm + C(p⁴/d)(Ew + ϑ)`, `w = trA²/(1+trA)` | l.413–424, 1463–1472 | `in_whiten` | BLmid (whitening), E4/T.TRC | stated |
| I-C3a | `E trA² ≤ 2Ew + Cϑ` | l.428–435 | `in_C3a` | F2 | stated |
| I-MARKENV | `a²S₊ + EtrA² ≤ λ, ϑ ≤ λ ⇒ S₊/d ≤ 4λ, d⁻²E[G_vv²‖G[N,N]‖_F²] ≤ Cλ`; same minus | l.1129–1149 | `in_markenv` | T.ROOT, UMI | stated |
| I-B1 | `Gterm ≥ (1 − Cη_BL)Q − Cε_BL`, `η_BL = p⁴/d + p/(dh)`, `ε_BL = ϑ(p⁵ + p²/h) + ϑ` | l.1192–1331 | `in_B1` | BLmid, GIBP2, T.TRC, B5 | stated |
| I-S1 | `0 ≤ E(G^±_ii − X^±_ii) ≤ C√h y^±_i`, `i ∈ S` | l.696–719 | `in_S1` | C6 closure | stated |
| I-W5 | `E[D_*^m (X_±²)_ii] ≤ C(m)/√h`, `i ∈ S` | l.790–797 | `in_W5` | S1, UMI | stated |
| I-W1 | the four weak residuals `≤ C·score + C B₀` (exact difference score) | l.721–911 | `in_W1` | W2–W4, E1-type endpoint identity | stated |
| I-C2all | **R(DR1)** (C2) at every `w ∈ S`: `1 − Eh^±_w ≤ Kδ̄`, `a²Σ_{j∼w}E(G^±_wj)² ≤ Kδ̄` (`C2All K`) | l.378–385 | `in_C2_all` (RouteDR1) | `SecA.concentration_C2` | stated |
| I-DR1c | **R(DR1)** `C2All K ⇒ a²Σ_{j∼w}E(G⁺_wj − G⁻_wj)² ≤ Cδ̄/p`, `w ∈ S` | DR1_CHECK §2 | `in_DR1_of_C2` (RouteDR1) | `SecB.dr1_of_c2` | stated |
| I-CR3′ | **R(DR1)** row comparison with the difference mass: `\|𝓡 − Gterm\| ≤ C(p⁵√(λ_rρ_Δ) + p⁴√(λ_cδ_c) + p¹³/d²) + Cϑ` for `ϑ ≤ λ_r ≤ λ_c ≤ δ_c ≤ 1`, `ϑ ≤ ρ_Δ`, `S₊/d ≤ λ_r`, `S₋/d ≤ δ_c`, `d⁻¹Σ_NE(x−z)² ≤ ρ_Δ`, marked envelopes | l.1170–1190, DR1_CHECK §3 | `in_CR3'` (RouteDR1) | `SecC.row_comparison_diff` | stated |
| I-GR1, I-CR3 | (inactive paper route) | l.626–693, 1170–1190 | `in_GR1`, `in_CR3` (RouteGCI) | Royen GCI | stated, unused |
| D-F3 | (existing) covariance inequality at the contact | l.198–201 | `source_covariance` (`Tight/SourceMax.lean`) | — | (other agent) |
| D-F2, D-walk | (existing) moments, walk facts | — | `source_moments`, `walk_facts` | — | (other agent) |

Not stated (used only inside leaves): WT1–WT2 (inside FS1), E4/E5/E6 as abstract comparison
(`Tight/Compare/*`), UMI (inside the leaves that interpolate).

### Analytic leaves of Section 1.5 (`Leaves.lean`)

| id | statement | source | Lean | informal deps | status |
|---|---|---|---|---|---|
| L-root | `D₊ E h⁺_v + aΣ_N E[ξ_ix_i] = 1` (exact) | l.1394–1397, 1977 | `root_equation` | `Zw > 0` | stated |
| L-CS | `(Σ_N E[ξ_ix_i])² ≤ \|N\|·S` | l.1977–1982 | `d15_cs` | CS, Jensen | stated |
| L-source | `\|N\| ≤ d`, `ℓ ≥ 0`, `L ≤ L̄`, `0 ≤ C₊ ≤ J`, `C₊ ≤ a²L̄s²`, `D₊ = 1+L−C₊`, `Σℓδ ≥ 0`, `S, S₋, EtrA², EtrB², Ew ≥ 0` | l.1352–1368 | `source_facts` | `walk_facts`, cap | stated |
| L-QSTAR | `\|Q_*\| ≤ Ca²(p + p³δ̄)` | l.1414–1422 | `qstar_bound` | KID structure, C2, UMI | stated |
| L-D8 | `\|y_v−2\| + \|\|N\|/d−1\| + d⁻¹Σ\|y_i−2\| ≤ C(ε_s+η₀+1/d)` | l.1493–1500 | `d8_profile` | D7, source identity | stated |
| L-D10corr | `L_d[(p−1)q₊ + pq₋] ≤ Q + Cp/(dh^{3/2})` | l.1532–1545 | `d10_corr` | C5, S1, UMI | stated |
| L-EN | Gram/positivity facts of the Hadamard energies | l.1586–1594 | `energy_psd` | Schur product theorem, CS | stated |
| L-FS5 | the four score bounds | l.1739–1763 | `fs5_scores` | FS1, BM4, FS4, GR1 (or DR1), UMI | stated |
| L-FS1 | fixed-mask bound | l.1656–1737 | `fs1_fixed_mask` | FS2, WT2, W5, D8, UMI | stated |
| L-BM1 | deterministic mask inequality (constant 16) | l.1596–1641 | `bm1_det` | Loewner facts | stated |
| L-BM4 | `Σ E[D_*^mΩ_±F(b_±)²] ≤ C h⁻²(z_± + θ)` | l.1643–1654 | `bm4_mask` | BM1, UMI | stated |
| L-RC1 | `t_± ≤ 1 + Cε` | l.1819–1824 | `rc1_tbounds` | F2, Hölder | stated |
| L-RC2 | `β ≤ α + Cξ` (with PROF) | l.1800–1842 | `rc2_profile` | F2, D7, D8, S1, UMI | stated |
| L-RC4 | `0 ≤ t_{±,0} − t_± ≤ C√h` | l.1927–1932 | `rc4_centres` | S1, UMI | stated |
| L-D13 | `Q_* ≤ a²(2L_d[(p−1)t_{+,0} + pt_{−,0}] + Cp³√(pδ̄/d))` (RC5 + D13) | l.1933–1951 | `d13_centering` | KID, D7, C2, UMI | stated |

### Real-number lemmas (`Real.lean`, route ones in the route files)

| id | content | Lean | status |
|---|---|---|---|
| R-param | deterministic facts (D1)–(D2): `a²`, `ε`, `η₀` bounds; `1 − rL̄ ≥ 0`; `d(r−1)(1−rL̄) ≥ 1/p − 2η₀`; `rL̄s² ≤ 4`; `L̄s² ≥ 4 − 8η₀`; `1/2 ≤ L̄ ≤ 2`; `s² ≤ 5` | `param_facts` (proof `param_facts_pf`, `RealParams.lean`, proved) | stated (copy proved) |
| R-D4 | D3 + QSTAR ⇒ D4 | `d4_real` | stated |
| R-D6 | λ-bootstrap with Young | `d6_real` | stated |
| R-D7 | D4 with `b = O(1)` | `d7_real` | stated |
| R-D9b | `Q ≤ Cp` | `d9b_real` | stated |
| R-D10 | B1 + D9a + D9b + D10corr ⇒ D10 (hypothesis `0 ≤ CB` added after the statement check found it false for `CB < 0`) | `d10_real` | stated |
| R-Ec | `q₊ ≤ C` | `qP_le_real` | stated |
| R-FS7 | raw residuals ⇒ `K·E_c` (AM–GM on `e√\|r₁\|`) | `fs7_real` | stated |
| R-JR | α-cap, JR3, JR2 | `jr_real` | stated |
| R-RC3 | Young absorption of `pe√z_±` | `rc3_young_real` | stated |
| R-D12 | D10 + RC3 + RC4 ⇒ D12 | `d12_real` | stated |
| R-D15 | `S ≥ 4 − C(ε_s + η₀ + 1/d)` | `d15_real` | stated |
| R-final | D14, absorption, D2 ⇒ `1/p − 2η₀ ≤ 2(1+9/d)c_p + K·TotErr` | `final_assembly_real` | stated |
| R-ledger | D16 exponent ledger ⇒ strict reverse inequality | `ledger_real` | stated |
| R-choice | choice of `κ₀, c₀` | `ledger_choice` | stated |
| R-CR1′ | **R(DR1)** CR1 from CR3′, DR1 at the root, MARKENV, C2 | `cr1_real_dr1` (RouteDR1) | stated |
| R-D9a′ | **R(DR1)** D9a from CR3′, DR1 at the root, MARKENV, C2, D6, D7 (witnesses of CHECK_CONTACT) | `d9a_real_dr1` (RouteDR1D9a) | stated |
| R-CR1, R-D9a | (inactive paper route) | `cr1_real` (RouteGCI), `d9a_real` (RouteD9a) | stated, unused |
| helpers | `eventually_reg`, `eventually_ge`, `Eventually.of_real/of_reg/of_treg/of_treg_h`, `eventually_treg_ge`, `eventually_reg_ge`, `Reg.h_pos`, `epsP_le_xiP`, `vth_le_dbar`; `lawE_const_mul`, `Contact.E_gp_diag`, `E_gp_root` (Chain1) | — | proved |

### Proved nodes (parent checks)

| id | statement | source | Lean | children | status |
|---|---|---|---|---|---|
| N-DR1 | `a²Σ_{j∼w}E(G⁺_wj − G⁻_wj)² ≤ Cδ̄/p`, `w ∈ S` | DR1_CHECK §2 | `in_DR1` (RouteDR1) | I-C2all, I-DR1c | proved |
| N-CR1 | `\|𝓡 − Gterm\| ≤ C(M)(p⁵√(λδ̄) + p¹³/d² + ϑ)` for `a²S + EtrA² ≤ λ`, `ϑ ≤ λ ≤ Mδ̄` | l.1078–1100 | `cr1` (RouteDR1) | I-CR3′, I-MARKENV, I-C2, N-DR1, R-CR1′ | proved |
| N-LOOP | `\|D₊r − (1 + a²ΣEP − (2p−1)a²S + 2pa²T + Q_*)\| ≤ Cp⁵/d²` | l.1394–1400 | `loop` (Chain1) | I-E1, L-root, L-source, R-param | proved |
| N-F3sum | `a²ΣEP ≤ r(rL − Σℓδ) + (a²/p)S − (r/p)J` | l.1401–1406 | `f3_summed` | D-F3, `E_gp_diag` | proved |
| N-D3 | (D3) | l.1407–1412 | `d3` | N-LOOP, N-F3sum, L-source | proved |
| N-D4 | (D4) | l.1423–1436 | `d4` | N-D3, L-QSTAR, L-source, R-D4 | proved |
| N-D6 | `a²S + EtrA² + ϑ ≤ Cp/d` | l.1438–1487 | `d6` | I-C2, N-CR1, I-C1, I-whiten, I-C3a, N-D4, L-source, R-D6 | proved |
| N-D7 | `S ≤ Cp`, `Σℓδ ≤ Cpa²`, `L̄ − L ≤ Cε_s` | l.1487–1491 | `d7` | I-C2, N-CR1, I-C1, N-D4, N-D6, R-D7 | proved |
| N-D9a | `\|𝓡 − Gterm\| ≤ C(Γ√(S+1) + p¹³/d² + ϑ)` | l.1504–1518 | `d9a` (RouteDR1D9a) | I-CR3′, N-DR1, I-MARKENV, I-C2, N-D6, N-D7, R-D9a′ | proved |
| N-D9b | `Q ≤ Cp` | l.1520–1531 | `d9b` (Chain2) | I-B1, N-D9a, N-D4, N-D7, R-D9b | proved |
| N-D10 | `𝓡 ≥ L_d[(p−1)q₊ + pq₋] − C·Err10` | l.1546–1558 | `d10` | I-B1, N-D9a, N-D9b, L-D10corr, R-D10 | proved |
| N-Ec | `q₊ ≤ C` | l.1590–1592 | `qP_le` | N-D9b, L-D10corr, L-EN, R-Ec | proved |
| N-FS6 | four raw weak residual bounds | l.1765–1776 | `weak_res` | I-W1, L-FS5 | proved |
| N-RC3 | `(p−1)(q₊−t₊) + p(q₋−t₋) ≥ −c_p − Cp·ErrRC3` | l.1776–1918 | `rc3` | N-FS6, N-Ec, L-EN, L-RC1, L-RC2, R-FS7, R-JR, R-RC3 | proved |
| N-D12 | `𝒟 ≥ −L_dc_p − C·Err12` | l.1955–1963 | `d12` | N-D10, N-RC3, L-RC4, R-D12 | proved |
| N-D15 | `S ≥ 4 − C(ε_s + η₀ + 1/d)` | l.1977–1982 | `d15` | L-root, L-CS, N-D7, L-source, R-D15 | proved |
| N-final | no contact once `Ccrit(√κ₀ + c₀^{17/3} + κ₀⁻²c₀^{34/3}) ≤ 1/8` | l.1965–2053 | `contact_final` | N-D3, N-D12, L-D13, N-D15, L-source, R-final, R-ledger | proved |
| D-contact | `exists_contact_free` | — | `Tight/Contact.lean` | N-final, R-choice | proved |

## 2. Sketches (at the level of the Lean proofs) and checks

Throughout: `a = aOf d p`, `r = 1 + ε`, `x_i = G⁺_vi`, `z_i = G⁻_vi`, `P_i = G⁺_vvG⁺_ii`,
`Q_i = G⁻_vvG⁻_ii`, `S = Σ_N Ex_i²`, `T = Σ_N Ex_iz_i`, `𝓡 = (p−1)S − pT`, `ℓ_i = a²y_vy_i`.

**N-LOOP** (proved). `root_equation`: `D₊r + aΣ_N E[ξ_ix_i] = 1` (contact: `E h_v = r`). Write
`E[ξ_ix_i] = g_i + err_i` with `g_i = a(−EP_i + (2p−1)Ex_i² − 2pEx_iz_i) − (a³/3)EK_i`
(I-E1: `|err_i| ≤ C₁p⁵a⁵`). Summing, `aΣg_i = −a²ΣEP + (2p−1)a²S − 2pa²T − Q_*`. So the defect is
`−aΣerr_i`, bounded by `a|N|C₁p⁵a⁵ ≤ C₁p⁵a⁶d ≤ C₁p⁵/d²` (`|N| ≤ d`, `a² ≤ 1/d`). Constant: `C₁`.
Check: `S = {v}`: no contact (`E h_v = 1/D_v = 1 < r`), so vacuous; `y_i = 0`: `x_i = P_i = K_i = 0`.

**N-F3sum** (proved). F3 at `i ∈ N ⊆ S`, with `EG⁺_vv = y_vr` (contact) and `EG⁺_ii = y_i Eh_i`
(`E_gp_diag`: `√y·(P̃⁻¹)_ii·√y = y·h_i`), multiplied by `a²/p > 0`, summed; then
`Σℓ_i Eh_i = rL − Σℓδ`.

**N-D3** (proved). LOOP (upper half), F3sum, `D₊ = 1 + L − C₊`; the identity
`(2p−1−1/p)a²S − 2pa²T = (1−1/p)a²S + 2a²𝓡`; `nlinarith`. Constant: LOOP's.
Check (AUDIT-C, sympy): residual 0.

**N-D4** (proved; real part R-D4). Each left term of D3 except `2a²𝓡` is `≥ 0`
(`(r−1)(1−rL) ≥ (r−1)(1−rL̄) ≥ 0`, `J ≥ C₊ ≥ 0`, `Σℓδ ≥ 0`, `S ≥ 0`). With `|Q_*| ≤ CQa²(p+p³δ̄)`,
`rC₊ ≤ r a²L̄s² ≤ 4a²`, `p²δ̄ ≤ 1`, `p⁵/(a²d²) ≤ 8p⁵/d`: `𝓡 ≤ C(p + p⁵/d)`. If `𝓡 ≥ −b`, each
nonnegative term is `≤ a²K(1 + p + p⁵/d + b)`; divide by `(1−1/p)a² ≥ a²/2`, `r ≥ 1`,
`r(r−1)` respectively. Constant `C = C(C₃, CQ)`.

**N-D6** (proved; real part R-D6). `λ := a²S + EtrA² + ϑ`; C2 gives `ϑ ≤ λ ≤ (2C₂+1)δ̄`
(`ϑ ≤ δ̄` by `vth_le_dbar`), so CR1 with `M = 2C₂+1` applies: `|𝓡 − Gterm| ≤ E_λ`,
`E_λ = C₁(p⁵√(λδ̄) + p¹³/d² + ϑ)`. C1: `𝓡 ≥ −E_λ`; D4(ii): `a²S ≤ C(p+E_λ)/d`; whitening and C3a:
`EtrA² ≤ C(p+E_λ)/d + Cϑ` after absorbing `Cw p⁴/d ≤ 1/2`. Young:
`Cp⁵√(λδ̄)/d ≤ λ/2 + C'p¹⁰δ̄/d²`; then `p⁹δ̄ ≤ d`, `p¹² ≤ d²`, `ϑ ≤ p/d`. Order: `C₂` before `M`,
`C₁ = C₁(M)`, then `C`. Check: AUDIT-C §6 (D6) and G7 (`E_λ ≤ C(c₀^{17/3} + o(1))`).

**N-D7** (proved; real part R-D7). With `λ ≤ C₆p/d`: `p⁵√(λδ̄) ≤ √C₆ p⁵√(pδ̄/d) ≤ √(3C₆)`
(`pδ̄/d ≤ 3p^{-10}` from `p¹⁷ ≤ d²`), so `𝓡 ≥ −K`; D4(ii) with `b = K`; `a²p/(r−1) ≤ 2ε_s`
(`a² ≤ 1/d`, `r − 1 ≥ 1/(2√(pd))`).

**N-CR1** (proved, route DR1; real part R-CR1′). `λ' = max(M, 2C₂+1)δ̄`,
`λ_r = λ_c = max(4, C_M)λ`, `δ_c = max(4, C_M)λ'` (MARKENV(+) with `λ`, MARKENV(−) with `λ'`,
C2 for the minus masses), `ρ_Δ = max(4C_Dδ̄/p, ϑ)` (DR1 at the root, `1/d ≤ 4a²`); `δ_c ≤ 1` from
`δ̄ ≤ 3p^{-5/2}`. CR3′ gives `C(p⁵√(λ_rρ_Δ) + p⁴√(λ_cδ_c)) ≤ C'p⁵√(λδ̄)`. (Paper route, inactive:
`cr1_gci` from CR3 with `ρ_r = δ_c`.)

**N-D9a** (proved, route DR1; real part R-D9a′; witnesses from CHECK_CONTACT).
`λ_r = 4(S+1)/d`, `ρ_Δ = 4(|C_D|+1)δ̄/p`, `λ_c = (|C_M|+4)(|C₆|+|C₇|+2)p/d`,
`δ_c = 4(|C_M|+4)(2|C₂|+1)δ̄`; orderings for large `p`. Then `p⁵√(λ_rρ_Δ) = 4√(|C_D|+1)Γ√(S+1)`
and `p⁴√(λ_cδ_c) = O(Γ)`. Check (AUDIT-C G8, DR1_CHECK): a bare (C2) bound `ρ = Cδ` for the root
row would give `≍ c₀^{17/3}p^{-1/2}`; the gain `δ̄/p` (DR1, or GR1 on the paper route) is essential.

**N-D9b** (proved; R-D9b). `Gterm ≤ 𝓡 + C₉E_row ≤ C₄(p + p⁵/d) + C₉(Γ√(C₇p+1) + …) ≤ Kp`; B1;
`C_Bη_BL ≤ 1/2` needs `p⁵/(κ₀d)` small (threshold depends on `κ₀`).

**N-D10** (proved; R-D10). `𝓡 ≥ Gterm − C₉E_row ≥ (1−C_Bη)Q − C_Bε_BL − C₉E_row`,
`ηQ ≤ η C₉b p = C(p⁵/d + p²/(dh))`, `Q ≥ Q_full − C_cp/(dh^{3/2})` (D10corr). Includes `ε_BL`
(AUDIT-D G6).

**N-Ec** (proved; R-Ec). `L_d ≥ 4`, `q₋ ≥ 0`, `L_d(p−1)q₊ ≤ Q_full ≤ C₉bp + C_cp/(dh^{3/2})`,
`p/(dh^{3/2}) ≤ 1` (κ₀-dependent threshold).

**N-FS6** (proved). W1 residual `≤ C_W·score + C_W B₀`, FS5 `score ≤ C_F(·)`; combine with
`C = C_W(C_F+1)` using `e, √·, h^{3/4}, B₀ ≥ 0`.

**N-RC3** (proved; R-FS7, R-JR, R-RC3). FS7: `√(ζ−α+β_h(q₊−t₊)+θ) ≤ √(z₊ + |r₁|) + √(C_qβ_h) + √θ`,
`e√|r₁| ≤ C(e√z₊ + e² + B₀ + e√θ)`: all four residuals `≤ K₁E_c`. JR: α-cap
`α ≤ ζ/(1+ζ) + e' + E` from `ζ² ≤ q₊z₊ ≤ (ζ+1+e')(ζ−α+E)`; JR3 from the minus Gram form with
`λ_m = β/(t₋+β)`; JR2 from `f(x) = x²/(2(1+x)) − x` (decreasing, 1-Lipschitz) and
`A_pα̂² − α̂ ≥ −1/(4A_p)`. Young: `K p e√z ≤ ((p−1)/2)z + K²pe²`. The four energy inputs (EN) are
pointwise PSD facts.

**N-D12** (proved; R-D12). Telescoping
`𝓡 − L_d[(p−1)t₊₀ + pt₋₀] = (𝓡 − L_d[(p−1)q₊+pq₋]) + L_d[(p−1)(q₊−t₊)+p(q₋−t₋)] − L_d[(p−1)(t₊₀−t₊)+p(t₋₀−t₋)]`,
`L_d ≤ 8`.

**N-D15** (proved; R-D15). `rD₊ − 1 = −aΣ_N E[ξ_ix_i]` (L-root), so
`(rD₊ − 1)² ≤ a²|N|S` (L-CS). Real: `rD₊ − 1 ≥ L − C₊ ≥ L̄ − C₇ε_s − a²L̄s²`, `a²|N| ≤ L̄/s²`,
`L̄s² ≥ 4 − 8η₀`.

**N-final** (proved; R-final, R-ledger). D3 with `(r−1)(1−rL) ≥ (r−1)(1−rL̄)`, `Σℓδ ≥ 0`;
D14: `𝔇/a² ≥ (1−1/p)(S−4) + 2𝒟 − C₁₃p³√(pδ̄/d)` (`(r/p)J − rC₊ ≥ −(1−1/p)rC₊ ≥ −4a²(1−1/p)`);
D12; absorption `2C₁₂Γ√(S+1) ≤ (S−4)/4 + C₁₅x/4 + 4C₁₂²Γ² + 2√5C₁₂Γ` with D15; `32(da²)² ≤
2(1+9/d)`; D2: `d(r−1)(1−rL̄) ≥ 1/p − 2η₀`. Result `1/p − 2η₀ ≤ 2(1+9/d)c_p + K·TotErr`. Ledger:
`Γ ≤ √3 c₀^{17/3}/p`, `p√h = √κ₀/p` (appears twice: RC4 and `ξ ∋ √h`), `pe² ≤ 3κ₀⁻²c₀^{34/3}/p`,
all other terms `≤ C κ₀^{-3/2}p^{-3/2}` (AUDIT-D §4.3 table); so `K·TotErr ≤ 3K(√κ₀ + c₀^{17/3} +
κ₀⁻²c₀^{34/3})/p + Kκ₀^{-3/2}C'p^{-3/2}`, `Ccrit := 3K`. With critical sum `≤ 1/8`:
`1/p − 1/(2(p−1)) − 1/(8p) ≈ 3/(8p)` beats the rest for `p ≥ P₀(c₀, κ₀)`.

**D-contact** (proved). `contact_final` → `Ccrit`; `ledger_choice Ccrit` →
`κ₀ = min(1, (24Ccrit)⁻²)`, `c₀ = min(1, (24Ccrit)^{-3/17}, (κ₀²/(24Ccrit))^{3/34})` (each critical
term `≤ 1/24`); `Eventually` at `(c₀, κ₀)` gives `D`; a `ContactCtx` gives a `Contact`. Final
theorem constant `C = 8/c₀` (already in `Tight/Theorem.lean`).

### Small cases and consistency checks

- `S = {v}` or `N = ∅`: `E h_v = 1/D_v = 1 < r`, so `ContactCtx` is impossible; all `∀ ct` statements
  are vacuous there. In general `N ≠ ∅` at a contact (L-root with `N = ∅` gives `E h_v = 1`).
- Non-vacuity: `ContactCtx` is satisfiable as a set of hypotheses only if the theorem were false;
  every input/leaf is a true statement of the source at a point of the capped family, and none
  assumes anything beyond `ContactCtx` and the regime. The inputs do not quantify over arbitrary
  envelopes without the source's hypotheses (CR3: orderings and envelope bounds, CR1: `ϑ ≤ λ ≤ Mδ̄`,
  MARKENV: `ϑ ≤ λ`).
- Zero sources: every observable is physical; `y_i = 0` ⇒ row `i` of `G^±`, `X^±`, `Y^±` vanishes
  (checked for E1, F3sum (`y_i Eh_i`), source facts, energies).
- Degenerate parameters: all real lemmas require `TRegime` (`p ≥ 10⁶`, `p¹⁷ ≤ d²`) and a further
  threshold `P₀` of their own; `h = κ₀p^{-4} ∈ (0, 1]`.
- Algebraic identities re-checked by hand: D3 algebra; `Q_full = L_d[(p−1)q₊ + pq₋]` from the
  definitions (`uᵀK₊u = (4d)⁻¹Σ_{i,k∈N}X_ik²`); the row-free part of `K_i` is
  `6P((p−1)P + pQ)` (set `x = z = 0`: `U = W = 0`, `K = 6PV`), matching RC5; the W1 residuals at
  `(+,+)` and `(−,+)` expand to `q₊ − ζ − t₊`, `ζ − z₊ − α`, `q₋ + ζ₋ − t₋`, `ζ₋ + z₋ − β`
  (symmetry of `K_±`); `∂_ijΩ₊ = −aG_vvG_viG_vj`, `∂_ijΩ₋ = (a/2)(G⁺_vvG⁻_viG⁻_vj − G⁺_viG⁺_vjG⁻_vv)`.

## 3. Route-dependent items — the chain is on the GCI-free route (DR1)

Active route files: `RouteDR1.lean` (inputs `in_C2_all`, `in_DR1_of_C2`, `in_CR3'`; proved
`in_DR1`, `cr1`; real lemma `cr1_real_dr1`) and `RouteDR1D9a.lean` (real lemma `d9a_real_dr1`;
proved `d9a`). `Chain1` imports `RouteDR1`, `Chain2` imports `RouteDR1D9a`. Section exports that
will supply the inputs (`docs/tight/CHECK_SECS.md` item 6, §6): `in_C2_all ← SecA.concentration_C2`
(`uOf ≤ δ̄`), `in_DR1_of_C2 ← SecB.dr1_of_c2` (via `C2All ↔ C2RowShape`, `Contact ↔ CapPoint`),
`in_CR3' ← SecC.row_comparison_diff` (which has no `δ_c ≤ 1` hypothesis, so it is stronger).

The inactive paper route (GR1 via Royen's GCI) is kept compiling under distinct names:
`RouteGCI.lean` (`in_GR1`, `in_CR3`, `cr1_real`, `cr1_gci`) and `RouteD9a.lean` (`d9a_real`,
`d9a_gci`); nothing in the chain imports them.

Route-independent statements (valid on both routes; only their leaf proofs differ):
- `in_W1` is stated with the exact difference score `|G⁺_ij − G⁻_ij|` (W1′, AUDIT-B B-2); its
  remainder needs (C2) at the neighbours (now `in_C2_all`), not GR1.
- `fs5_scores` (FS5′): same right side (`e = √(pδ̄)/(√dh)`); on this route its proof uses DR1 at
  the neighbours (`in_DR1`) and the trivial (C2) bound for the root rows.
- `d13_centering` (D13′): stated with `δ̄`; proof uses (C2) for the minus row.
- `cr1`, `d9a`: same statements as on the paper route.

`in_C2` (root only) is still used by D6, D7, `cr1`, `d9a` (it also has the core parts
`E trA², E trB²`, which `in_C2_all` does not).

## 4. Gaps and doubtful steps found while stating the chain

None that changes a statement or needs a weakening. Minor points, all recorded in the statements:

1. **(D10) `ε_BL`** (AUDIT-D G6): included in `Err10`.
2. **CR1's envelope** (AUDIT-C G4): the floor `ϑ ≤ λ` and `λ ≤ Mδ̄` are explicit hypotheses of
   `cr1`; the contact hypothesis is not used.
3. **D13** stated with `δ̄` (weaker than the paper, valid on both routes; non-critical loss).
4. **Critical `p√h` appears twice** (RC4's `L_d(2p−1)C√h` and `pξ ∋ p√h`): the ledger constant
   accounts for both (`Ccrit = 3K` in the sketch).
5. **D15 at `N = ∅`**: not an issue at a contact (see checks).
6. **The paper's "`C_+/a² = 4 + O(·)`"** (l.1967) is not needed; only `rC₊ ≤ 4a²` (via
   `C₊ ≤ a²L̄s²`, `rL̄s² ≤ 4`, AUDIT-D §3.1) is used.
7. The source's `e^{-cp}` terms are restated as `Cϑ`; R-final/R-ledger must check that
   `ϑ(p⁵ + p²/h)` (in `ε_BL`) is negligible: `d^{-10}p⁶/κ₀ = o(p^{-3/2})`.

## 5. Parallelization notes for provers

- Pure real leaves (independent, no law): `param_facts`, `d4_real`, `d6_real`, `d7_real`,
  `d9b_real`, `d10_real`, `qP_le_real`, `fs7_real`, `jr_real`, `rc3_young_real`, `d12_real`,
  `d15_real`, `final_assembly_real`, `ledger_real`, `ledger_choice`, `cr1_real`, `d9a_real`.
  `ledger_real` can be split into `ledger_crit` (three critical bounds) and `ledger_rest`.
- Exact law-level leaves (small): `root_equation`, `d15_cs`, `source_facts`, `energy_psd`, `bm1_det`.
- Analytic leaves (need inputs + UMI): `qstar_bound`, `d8_profile`, `d10_corr`, `fs5_scores`
  (with `fs1_fixed_mask`, `bm4_mask`), `rc1_tbounds`, `rc2_profile`, `rc4_centres`, `d13_centering`.
- A shared **UMI** node (AUDIT-D §2.6: `E[YZ] ≤ B(M/θ)^{1/(k−1)}(EY + θ)` for finite weighted
  averages) should be stated once (e.g. `Tight/Tools/UMI.lean`) before the analytic leaves are
  dispatched; it is used by about 10 of them.
