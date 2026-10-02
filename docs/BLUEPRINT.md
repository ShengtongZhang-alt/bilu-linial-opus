# Blueprint

The lemma DAGs, with per-node status, for the upper bound of Theorem 1 of
`docs/second_order_bilu_linial_tight.tex` (Part D, `near_ramanujan_signing`), Section 6 of
`docs/second_order_bilu_linial.tex` (Part C2, `explicit_excess`) and Theorem B of
`docs/COUNTEREXAMPLE_ALL_DEGREES.md` (Part B). The DAGs of the superseded upper bounds (Part A,
`docs/asymptotic_bilu_linial.tex`, and Part C1, Theorem 1.1 of `docs/second_order_bilu_linial.tex`)
were deleted with their code once Part D was proved.

Statuses: `todo` (not stated in Lean), `stated` (Lean statement with `sorry`), `proved` (the
node's own proof has no `sorry`; it may use open nodes), `proved*` (it and every node below it are
proved; `#print axioms` checked). "Checks" records the pre-dispatch checks of
`.cursor/rules/formalization-workflow.mdc` §2: sketch, parent check (the parent proved from the
node's statement), small cases.

## Common (shared linear algebra) — `BiluLinial/Common/`

| id | statement | Lean | deps | status |
|---|---|---|---|---|
| C-opnorm | basic facts about `opNorm` (nonneg, triangle, submultiplicative, `‖M^k‖ ≤ ‖M‖^k`, principal submatrix `≤`, Cauchy–Schwarz bounds `|xᵀMy| ≤ ‖M‖‖x‖‖y‖`, row/column sums of squares `≤ ‖M‖²`) | `Common/OpNorm.lean` | Mathlib | proved* |
| C-spectral | for symmetric `A`: `‖A‖ = max |λᵢ|`; `‖A‖ ≤ r ↔ rI ∓ A ⪰ 0`; `‖A‖ < r ↔ rI ∓ A ≻ 0`; empty matrix has norm 0 | `Common/Spectral.lean` | C-opnorm | proved* |
| C-schur | Schur complements for `[[A, B], [Bᵀ, D]]` with `D ≻ 0` (PD/PSD iff, determinant, top-left block of the inverse); one-vertex version `vertexSchur` (PD iff `> 0`, `det M = det(M−v)·s`, `(M⁻¹)_{vv} = 1/s`) | `Common/Schur.lean` | Mathlib | proved* |
| sanity | sanity lemmas for the Challenge definitions | `Sanity.lean` | C-spectral | proved* |

## Main — `BiluLinial/Main.lean`

`near_ramanujan_signing_proof` (Challenge, Part D) from D-main: **proved***.
`explicit_excess_proof` (Challenge) from C2-thm: **proved***. `bilu_linial_counterexample_proof`
(Part B library theorem, formerly a Challenge statement; it covers `d = 3`) from B-main:
**proved***.

**Final assembly (done, Part C).** The comparator loads `Challenge` and `Solution` as separate
environments and requires `Solution` to declare the two theorems under the Challenge names, so
`Solution`'s imports must not contain `Challenge`. The proof modules import
`BiluLinial/ChallengeDefs.lean` (verbatim copy of the three Challenge definitions) instead of
`Challenge`, `Main.lean` states the Challenge theorems verbatim (the two main theorems and the
norm–eigenvalue equality `opNorm_eq_iSup_abs_eigenvalues₀`), and `Solution.lean` restates them
under the Challenge names. `scripts/check_statements.sh` confirms that both environments agree
(3 definitions and 3 theorems).

## Part D — upper bound of Theorem 1 of `docs/second_order_bilu_linial_tight.tex` (`BiluLinial/Tight/`)

Target: `near_ramanujan_signing` (Challenge), proved in `Main.lean` as
`near_ramanujan_signing_proof := Tight.near_ramanujan_signing_thm` (**proved***: `#print axioms`
gives `propext`, `Classical.choice`, `Quot.sound`).

**Status (2026-10-01): every Part D node is proved*.** No `sorry` remains in `BiluLinial/Tight/`
(last leaves: `wt5_rem_core` 94ce5f1, `wt5_ret_law` 4b68f70, `transfer_C4T` dc15c12, `fibPhi_d3`
a6694b9). The status column below is current; the prose notes after the tables are a dated log of
how the open nodes were closed, and its "open"/"prover assigned" remarks are historical. Commit
hashes in this file refer to the development history, which is not included in this repository.

**Design** (`Tight/Defs.lean`). Part A framework: ambient `G` on `V`, induced subgraphs as
`S : Finset V`, signings as `Config V`, expectations as ratios of plain sums. The paired law uses
the *normalized* precisions `P̃^± = diag D(y^±) ± a Y^{1/2} A_σ Y^{1/2}` (`precN`, identity outside
`S`), `D_i = 1 + Σ_{j∼i} c_ij`, so zero sources are identity rows; `h_i^± = (P̃^±)⁻¹_ii`. Weight
`wt = 1{P̃⁺ ≻ 0, P̃⁻ ≻ 0}(det P̃⁺ det P̃⁻)^p`. Parameters `qOf, ΔOf, RsqOf, aOf, η0Of, τsOf, sOf, rOf`
as functions of `(d, p)`. Regime of the structural nodes `TRegime d p := 10⁶ ≤ p ∧ p^17 ≤ d²`
(`Tight/Params.lean`). The constant `c₀` of `p = pAt c₀ d = ⌊c₀ d^{2/17}⌋` is **existential**: it
is produced by `exists_contact_free` (Section 1.5 ledger, after the absolute constants and `κ₀`;
gap D-G3), and `exists_tRegime_pAt` puts `pAt c₀ d` in the regime for large `d`. Invariant
`TInv S`: for all `y^± ∈ [0, s]^V`, `Zw > 0` and `E h_i^± ≤ r` for `i ∈ S`.

### Top-level skeleton (parent checks done: `Step`, `Core`, `Theorem` compile from the children)

| id | statement | Lean | deps | status |
|---|---|---|---|---|
| D-main | `near_ramanujan_signing` with `C = 8/c₀`, `d₀ = max D D₁` | `Tight/Theorem.lean` `near_ramanujan_signing_thm` | D-core, D-params, D-contact | proved* |
| D-core | strong induction: `TInv S` for all `S`; signing with `‖A_σ‖ < √(R²)` | `Tight/Core.lean` `tinv_all`, `tight_signing` | D-step, D-extract | proved* |
| D-step | `(∀ T ⊂ S, TInv T) → TInv S` (given `ContactFree d p`) | `Tight/Step.lean` `tinv_step` | D-floor-pos, D-cont, D-swap, D-zero, D-first-contact | proved* |
| D-params | positivity of `q, R², a, η₀, τ_*, s`, `η₀ < 1`, `τ_* < 1`, `r > 1`, `q η₀² = Δ(1−η₀)`, `c(a²s²) = τ_*/(1−τ_*)`, `2 ≤ p`; `pAt c₀ d` in the regime for large `d`; `R² ≤ 4(d−1) + (8/c₀) d^{−2/17}` at `pAt c₀ d` | `Tight/Params.lean` | — | proved* |
| D-extract | `Zw(V, s1, s1) > 0 → ∃ σ, ‖A_σ‖ < √(R²)` | `Tight/Extract.lean` `signing_of_Zw_pos` | D-params, C-spectral | proved* |
| D-swap | `Zw(y⁺,y⁻) = Zw(y⁻,y⁺)`, `E h_i^-(y⁺,y⁻) = E h_i^+(y⁻,y⁺)` (`σ ↦ −σ`) | `Tight/Symmetry.lean` | — | proved* |
| D-zero | `y_i = 0` ⇒ `h_i = 1` on invertible `P̃`, `E h_i^+ = 1` | `Tight/Symmetry.lean` | — | proved* |
| D-cont | `Zw` continuous in `(y⁺, y⁻)` for `p ≥ 1`; `E h_i^+` continuous on `{Zw > 0}` for `p ≥ 2` | `Tight/Continuity.lean` | — | proved* |
| D-first-contact | abstract expanding-cube argument | `Tight/FirstContact.lean` `first_contact_cube` | — | proved* |
| D-floor-pos | IH ⇒ `Zw > 0` on `[0, s]^V` | `Tight/Floor.lean` `floor_pos` | D-empty, D-del, D-transfer, D-floor, D-ins, D-params-r | proved* |
| D-empty | `Zw(∅) > 0` (`P̃ = I`) | `Tight/Insertion.lean` `Zw_empty_pos` | — | proved* |
| D-ins | Schur at the root: `W_S = W_core (D_v⁺D_v⁻)^p Φ`, `Φ = (1−q_A)₊^p(1−q_B)₊^p` | `Tight/Insertion.lean` `wt_eq_wtCore_mul` | C-schur | proved* |
| D-del | inherited core precision `= diag(e) P̃_J(ŷ) diag(e)` with `0 ≤ ŷ ≤ y`, `e ≥ 1` | `Tight/Deletion.lean` `precCore_eq_congr` | — | proved* |
| D-transfer | through D-del: `Z_core > 0` and core means of `(M^±)⁻¹_ii` `≤` the `J`-law means at `ŷ` | `Tight/Deletion.lean` `ZwCore_pos_of_congr`, `coreE_inv_le_of_congr` | — | proved* |
| D-floor | neighbour core means `≤ 1.01` ⇒ `Z_core ≤ 40^p Σ W_core Φ` | `Tight/FloorLemma.lean` `floor_ins` | D-params, D-params-κ (`d κ ≤ 1.01`, `κ ≤ 1/100`, `Tight/ParamsExtra.lean`) | proved* |
| D-params-r | `r ≤ 1.01` | `Tight/ParamsExtra.lean` `TRegime.rOf_le` (also `d_mul_kappa_le`, `kappa_le`) | D-params | proved* |
| D-contact | `∃ c₀ ∈ (0,1], ∃ D, ∀ d ≥ D, ContactFree d (pAt c₀ d)`: no `ContactCtx` (IH, law on `[0,s]^V`, caps on `[0, λs]^V`, contact `E h_v^+ = r` there) | `Tight/Contact.lean` `exists_contact_free` | Sections 1.2–1.5 (decomposition below) | proved* |

**Sketches and checks (skeleton).**
- D-extract: at `y = s1` on `S = V`, `√s√s = s`, so `P̃^± = diag D ± a s A_σ`; `D_i = 1 + deg(i)·τ_*/(1−τ_*) ≤ s = (1+qτ_*)/(1−τ_*)` iff `deg(i) ≤ q + 1 = d`; a signing of positive weight has `P̃^± ≻ 0`, so `sI ± a s A_σ ⪰ P̃^± ≻ 0` and `opNorm_lt_iff_posDef` with `r = 1/a = R`. Small cases: `V = ∅` (norm 0); one edge (`D = 1 + c ≤ s`).
- D-swap: `precN a (−1) y σ = precN a 1 y (−σ)`, so `wt(y⁺,y⁻,σ) = wt(y⁻,y⁺,−σ)`; reindex by the involution `σ ↦ −σ`.
- D-zero: `c(0) = 0` and `√0 = 0`, so row and column `i` of `P̃` are `e_i`; then `(P̃⁻¹)_ii = 1`. `i ∉ S` is the same.
- D-cont: `y ↦ P̃` is continuous (`√`, `cRoot`); `1{P ≻ 0} det^p` is continuous for `p ≥ 1` (it is `0` on the boundary of the cone and outside); `W h_i = 1{…} det(P̃⁺)^{p−1} adj(P̃⁺)_ii det(P̃⁻)^p` needs `p ≥ 2` (counterexample `p = 1`: jump at the cone boundary). Hypotheses `1 ≤ p`, `2 ≤ p` are therefore necessary.
- D-first-contact: good `t` form a down-closed subset of `[0,1]` containing `0` (cube of side 0 is the origin); closed by continuity (scale points of the cube of side `t*`); if `t* < 1`, strict inequality on the compact cube of side `t*` and uniform continuity on `[0,s]^{2V}` (clamping `y ↦ min(y, t* s)` moves points by `≤ (t − t*) s`) extend it. 
- D-step: as in the source's last paragraph of Section 1.1; the minus contact reduces to a plus contact at swapped sources (the cube and the cap are swap-invariant).
- D-floor-pos: `S = ∅`: `P̃ = I`, `Zw = #Config`. Otherwise delete `v ∈ S`, use the deletion lemma for sources `ŷ ∈ [0, y]` on `J = S − v` (IH applies since `ŷ ∈ [0, s]^V`), Schur: `W_S(σ) = W_J(σ|_J)·(D_v⁺α)^p(D_v⁻β)^p` up to the normalization factors, and the floor lemma with core means `≤ r ≤ 1.01`.
- D-ins: `precCore` is `P̃_S(y)` with row/column `v` replaced by the identity, so
  `delVertex P̃_S v = delVertex precCore v`; if `M^± ≻ 0`, `vertexSchur = D_v(1 − q)`, PD iff
  `q < 1`, `det P̃_S = det M · D_v(1−q)`; if `M^±` is not PD neither is `P̃_S` (principal
  submatrix), both sides vanish. Needs `p ≥ 1` (`0^p = 0`) and `y ≥ 0` (`D_v ≥ 1`).
- D-del (replaces the source's ODE lift, no Jacobian needed): on `P = {i ∈ J : y_i > 0}`, the map
  `T(ŷ)_i = D^J_i(ŷ) y_i / D^S_i(y)` is monotone (`c` is increasing) and maps the box
  `[0, y_i]` into itself since `D^J_i(y) ≤ D^S_i(y)` (a fixed point satisfies `ŷ_i ≥ y_i/D^S_i(y)`
  automatically); Knaster–Tarski
  (`OrderHom.lfp` on the complete lattice `Π i, Set.Icc …`) gives a fixed point, i.e.
  `Z^J(ŷ) = Z^S(y)|_J`. Take `ŷ_i = 0`, `e_i = 1` off `P`, `e_i = √(y_i/ŷ_i)` on `P`. Entry check:
  diagonal `D^S_i(y) = e_i² D^J_i(ŷ)` is the fixed-point equation; off-diagonal
  `√y_u√y_w = e_u√ŷ_u e_w√ŷ_w`; zero sources give identity rows on both sides. Small case:
  `S = {v}` (`J = ∅`, both sides `I`).
- D-transfer: `wt_core(σ) = (Π e⁺_i)^{2p}(Π e⁻_i)^{2p} wt_J(ŷ, σ)` (congruence by an invertible
  diagonal preserves PD, multiplies `det` by `(Π e_i)²`), and `(M⁻¹)_ii = e_i^{−2}(P̃_J(ŷ)⁻¹)_ii ≤
  (P̃_J(ŷ)⁻¹)_ii` on supported signings (positive diagonal of the inverse of a PD matrix).
- D-floor: sketch in the module docstring (source lines 149–186, numerics checked by the
  coordinator). Only the neighbour means enter, through `E_ξ q_A = Σ_{i∈N} A_ii`.
- D-contact: `S = {v}`: `h_v = 1/D_v = 1 < r`, no contact; one edge at `y = s1`: `h_v = 1`. The statement is the source's "ruling out the contact".

**Long poles.** Proved (sorry-free): Gaussian IBP (`Tight/Gauss/IBP.lean`, `IBPCorr.lean`:
Stein's identity on `ℝⁿ`, derivative of the correlation `s ↦ E f(X) g(Y_s)`); midpoint
Prékopa–Leindler on `ℝⁿ` and `Cov ⪯ M⁻¹` for even midpoint-log-concave perturbations of the Gaussian
`exp(−xᵀMx/2)` (`Tight/Gauss/PrekopaLeindler*.lean`, `CovBound.lean`). The Gaussian correlation
inequality is no longer needed (DR1 route), but its derivative form for the clipped factors is
proved anyway (`gci_clipped`, `Tight/Gauss/GCI*.lean`, plan `docs/tight/GCI_PLAN.md`: Royen's
argument tested against finite exponential sums, slab boxes → ellipsoids by rational supporting
slabs, derivative at `s = 1` by a rotation and Stein's identity); it is a fallback for the paper's
GR1 route and will be deleted at the end if unused. Proved: Rademacher–Gaussian comparison
(`Tight/Compare/`): `|c_j| ≤ 1`; one-dimensional comparison with constant `2`; endpoint identity
(E1) with `K = 13/60`; multi-coordinate expansion (E4) `gauss_rad_expansion` with remainder
`≤ 2 Σ_{|j| = k+1} M_j` (better than the paper's `C^{k+1}`). Shared measures `radReal`, `gaussPi`, `radPi`, `mixPi` in
`Tight/Gauss/Basic.lean` (proved*).

**Audits (done; `docs/tight/AUDIT_{A,B,C,D}.md`, scripts in `scripts/tight/`).** Sections 1.2–1.5
(lines 237–2073) and the induction closure were checked claim by claim. **Verdict: correct, with
fixable gaps only; no fatal gap, no statement weakened.** Gaps recorded (fixes in the audits):

| id | where | issue | fix |
|---|---|---|---|
| A1, B-CAP | §1.2 "capped source family" | implicit hypotheses: moments of the law, the cap, moments of every own core law (from the induction hypothesis + deletion), the floor | stated as the context `CapCtx` (`Tight/Ctx.lean`) |
| A2, B-6, D-G3 | constants | "`C` absolute", "`o(1)`", "large `d`" | every analytic lemma is `∃ C, Eventually …` (`Tight/Ctx.lean`): absolute constants, then `κ₀`, `c₀`, then the threshold |
| A4 | (E4) | `α₊^{p−2}` is only `C^{p−3}` | require `4k*+4 ≤ p−3` |
| A7 | C4 transfer | the crude majorant loses the rate | keep the refined single-coordinate bound (EPB4) as its own node |
| A12, D-G1 | zero sources | the law at a zero plus-source and positive minus-source is not that of a smaller graph | normalized precisions make zero sources identity rows; `walkB` has identity rows there, so `walkK` is the inverse for the positive-source subgraph automatically |
| D-G2 | deletion lemma | ODE lift | Knaster–Tarski fixed point (`precCore_eq_congr`) |
| D-G4 | constants | the paper never evaluates `c₀, κ₀, d₀` | existential: `κ₀ = min(1, (24C₁)⁻²)`, `c₀ = min(1, (24C₂)^{-3/17}, (κ₀²/(24C₃))^{3/34})` from the critical coefficients, `C = 8/c₀` |
| D-G6 | (D10) | `ε_BL` missing | add it |
| C | B1 | Brascamp–Lieb with variable Hessian (the paper's PDE sketch) | **BLmid** (AUDIT-C §5.3): for `ρ` even with `ρ(z+w)ρ(z−w) ≤ ρ(z)² exp(−⟨w,K(z)w⟩)`, `K ⪰ κI`: `∫⟨θ,x⟩²ρ ≤ ∫⟨θ,K⁻¹θ⟩ρ`, from midpoint Prékopa–Leindler |
| B-1…B-5 | GR1 (Royen's GCI) | GCI is very hard to formalize | **GCI-free route, confirmed** (`docs/tight/DR1_CHECK.md`, independent check; numerics `scripts/tight/dr1_*.py`): GR1 is used in five places (W1 remainder, FS5 determinant and root-weight parts, D9a, D13), none of which needs individual-row gain. GR1 is replaced by **DR1** `a²Σ_{i∼v}E(G⁺_vi−G⁻_vi)² ≤ K_DR δ/p` (exact identity `(2p−1)a²ΣE(G⁺−G⁻)² = B⁺+B⁻+2a²T_v+E3`, only `|T_v|` used), and W1′, FS5′, CR3′, D9a′, D13′ are restated; the end-game ledger keeps its three critical terms and the 2/17 rate. AUDIT-C/D (G8) are right about the paper's estimates as written but did not consider the difference score; AUDIT-D's claim that W1 needs GR1 is wrong. **No GCI is needed**; the GCI subtree (`Tight/Gauss/GCI*.lean`, `gci_clipped`) was finished anyway (b10ba0b, proved*) and is kept in the library, unused by the proof. |

The true margin at the final contradiction is `1/p − 2c_p ≈ 1/(2p)` (the paper allots `1/(4p)`).
2/17 comes from `δ ≍ (p/d)^{1/3}` (C2) and `Γ ≍ p^{14/3}d^{-2/3} ≍ 1/p` iff `p^{17} ≍ d²`.

**External inputs actually needed** (after the replacements): Gaussian integration by parts
(`Tight/Gauss/IBP.lean`), the even log-concave covariance bound `Cov ⪯ M⁻¹` from midpoint
Prékopa–Leindler (`Tight/Gauss/PrekopaLeindler*.lean`, `CovBound.lean`), BLmid (same route), the
Rademacher–Gaussian comparison E4 (`Tight/Compare/`, proved). Royen's GCI is **not** needed (DR1
route confirmed). The Schur product theorem is in Mathlib
(`Matrix.PosSemidef.hadamard`).

### Contact exclusion (Sections 1.2–1.5): decomposition (all nodes proved*)

Shared vocabulary `Tight/Ctx.lean` (committed): `Eventually` (quantifier order), `CapCtx`,
`ContactCtx`, physical inverses `greenP`, `shiftP`, `coreGreen`, walk matrix `walkB`/`walkK`, star
layer `rootMat` (`A`, `B`), `qForm`, `clipF`, `starPhi` (`Φ`), `radE` (`𝖱`), `gaussE` (`𝖦`),
`rootSigns` (`ξ`).

| id | statement | Lean | deps | status |
|---|---|---|---|---|
| D-walk | `𝓑 ≻ 0`, `K = 𝓑⁻¹ ≥ 0`, `K_ii ≥ 1`, `K_ij ≥ τ_ij` on edges, for `0 ≤ y ≤ s` | `Tight/Walk.lean` `walk_facts` (general form `walk_facts_of_bound`) | D-params | proved* |
| D-F2 | on the capped cube, `E(h_i^±)^k ≤ ((pr−k)/(p−k))^k`, `1 ≤ k ≤ p−2` | `Tight/SourceMax.lean` `source_moments`, `source_moments_plus` | D-walk, D-cont, D-del | proved* |
| D-F3 | at a contact, `p Cov(G⁺_vv, G⁺_ii) − E(G⁺_vi)² ≤ −r y_v y_i K_vi` | `Tight/SourceMax.lean` `source_covariance` | D-walk, D-cont, D-del | proved* |
| D-star | root star representation: `qRoot = q_A(ξ)`, `Φ = starPhi p A B ξ`, core weight and `A, B` independent of root signs, `Σ_σ W f = (D_v⁺D_v⁻)^p Σ_σ W_core 𝖱[Φ f(setRoot σ ·)]`, `E f = E_core𝖱[Φf]/E_core𝖱[Φ]` | `Tight/Star.lean` | D-ins | proved* |
| D-BLmid | `ρ` even, `ρ(z+w)ρ(z−w) ≤ ρ(z)² e^{−⟨w,K(z)w⟩}`, `K ⪰ κI` ⇒ `∫⟨θ,x⟩²ρ ≤ ∫⟨θ,K⁻¹θ⟩ρ`; trace form `∫xᵀMxρ ≤ ∫tr(MK⁻¹)ρ` | `Tight/Gauss/BLmid.lean` | PL | proved* |
| R-param | (D1)–(D2) deterministic parameter facts (`param_facts`, `Contact/Real.lean`); verbatim copy `param_facts_pf` | `Tight/Contact/RealParams.lean` | D-params, D-params-r | proved* |
| R-leaves | real leaves of the Section 1.5 chain: `d4, d6, d7, d9b, d10, qP_le, d15` (`RealPfA`) and `fs7, jr, rc3_young, d12, final_assembly, ledger, ledger_choice` (`RealPfB`); `Contact/Real.lean` closes each leaf with its `_pf` copy | `Tight/Contact/Real.lean`, `RealPfA.lean`, `RealPfB.lean` | R-param | proved* |
| R-route | pure real parts of CR1 and D9a on the DR1 route: `cr1_real_dr1`, `d9a_real_dr1` | `Tight/Contact/RouteReal.lean` | R-param | proved* |
| D-chain | Section 1.5 chain `d3 … contact_final`, `exists_contact_free` from the leaves and inputs below (GCI-free DR1 route: `cr1` in `RouteDR1.lean`, `d9a` in `RouteDR1D9a.lean`; the paper's GCI-route files `RouteGCI.lean`, `RouteD9a.lean` were deleted unproved, see FORMALIZATION.md) | `Tight/Contact.lean`, `Contact/Chain1.lean`, `Chain2.lean` | all rows below | proved* (was: proved (parent check: compiles from sorried leaves)) |
| I-A | inputs (E1), (C2), (C1), whitening, (C3a) at a contact ← `SecA/Export.lean` | `Tight/Contact/InputsA.lean` | Section 1.2 | proved* (`exact SecA.in_*`) |
| I-B | inputs (S1), (W5), (W1) ← `SecB/Export.lean`, with `CL1Shape`/`C2RowShape` from SecA | `Tight/Contact/InputsB.lean` | Section 1.3, 1.2 | proved* (`exact SecB.in_*`) |
| I-C | inputs MARKENV, (B1) ← `SecC.mark_envelope`, `SecC.rowGauss_ge_shiftQ` | `Tight/Contact/InputsC.lean` | Section 1.4 | proved* (fd62610; inlined from SecC's `mark_envelope_row/frob`, `rowGauss_ge_shiftQ`) |
| I-route | `in_C2_all` (C2 at every vertex ← `SecA.concentration_C2`), `in_DR1_of_C2` (pointwise `SecB.dr1_pt`), `in_CR3'` (`SecC.row_comparison_diff`) | `Tight/Contact/RouteDR1.lean` | Sections 1.2–1.4 | proved* (was: proved (fd62610; `in_DR1_of_C2` proved*; `in_C2_all`, `in_CR3'` wait on SecA/SecC nodes)) |
| L-pure | `root_equation` (now with `hR`; corollary of `SecB.root_row_mean`), `d15_cs`, `source_facts`, `energy_psd`, `bm1_det` | `Tight/Contact/Leaves.lean` | D-walk, SecA/SecB lemmas | proved* |
| L-export | `qstar_bound`, `d10_corr`, `rc1_tbounds`, `rc4_centres`, `bm4_mask` | `Tight/Contact/LeavesX.lean` | I-A, I-B, D-F2, UMI | proved* (was: proved (fd62610; `rc1_tbounds`, `bm4_mask` proved*)) |
| L-chain | `d8_profile`, `rc2_profile`, `d13_centering` (need D6/D7 of `Chain1`; moved out of `Leaves.lean`, CHECK_CONTACT_LEAVES (F1)) | `Tight/Contact/Leaves2.lean` | `Chain1` | proved* (was: proved (fd62610)) |
| L-FS | FS2 `fs2` (exact Schur identity for `maskF`: `F_ji = -a (X_e)_ii (X₊)_ii ((T_dir ξ)_j + (T_cav ξ)_j)`), FS4 `fs4_root` (`(∂_ij Ω±)² ≤ Ω± 4a²D_*²(x_i² + z_i²)`), `fs1_fixed_mask` (from D8, WT2, W5), `fs5_scores` (from FS1, BM4, DR1, C2) | `Tight/Contact/Leaves3.lean` | L-chain, L-export, I-B, I-route | FS2, FS4 proved* (checked numerically, `check_fs2.py`); FS1, FS5 proved (765d34c) |

**Status 08:30 UTC (2026-10-01).** The contact chain derives `exists_contact_free` on the GCI-free
DR1 route and builds through `Tight/Theorem.lean`. The open sorries are the leaves and inputs in the
table above (each assigned to one prover, one file each) and the section files `SecA/*`, `SecB/*`,
`SecC/*` (drafters still running). D-F2/F3, the real leaves and `Star` are proved*. Rule-2
checks of the leaves: `docs/tight/CHECK_CONTACT_LEAVES.md` (nothing false; placement fix (F1) applied
by moving the chain-dependent leaves to `Leaves2.lean`/`Leaves3.lean`; FS2 must become a node).
Section 1.3 (`SecB/`, notes `docs/tight/BP_SECB.md`, committed f509edc): exports `SecB.in_S1`,
`SecB.in_W5`, `SecB.in_W1`, `SecB.in_DR1`, `SecB.wt2` and bridges from SecA proved; S1/W5 chain and
`dr1_pt`, `kpoly_moment`, `dr1_of_c2` (from `E1Shape`/`C2RowShape`) proved*; `weak_loop_of` and
`wt3_gauss` proved from open sub-lemmas (2d041eb); `weak_sec_of`, `weak_mask_of`, `weak_fibre_alg`,
`weak_fibre_avg` proved* (7d6089b). `weak_fibre_edge` proved (f9be82b) from the fibre IBP
(`fibre_ibp_bound`), the non-regular fibre bound `weak_fibre_nonreg` (Markov, `K = 9·256⁴`), and
TB.W1fib-reg; the latter is proved from the rank-two interpolation `precN_update`, endpoint
values, segment positive-definiteness `fib_seg_pd` and `C³` smoothness (all proved*) and two open
sub-nodes: TB.W1fib-d1 (`fibPhi_deriv_one/neg_one`, `SecB/W1FibD1.lean`; proved* dd767f5) and
TB.W1fib-d3 (`fibPhi_d3`, `SecB/W1FibD3*.lean`; proved*, constants `K = 10⁶·4718592·2661121⁸`,
`M = 30`, via rank-two recentring at the good endpoint); both checked numerically on the
exact Lean model (`scripts/tight/check_w1_reg2.py`). `wt5_rem` and `wt5_ret` proved (f769f66)
from star insertion at real vectors (`wSub_eq_star`, `precSub_ins`), the normalized observables
(`obsQ_eq`, `obsT_eq`), the core-law forms and A-RET (`coreRet_div_insF_eq`), all proved*, and three
open leaves, split into their own files (b23b8b1): TB.WT5r° `wt5_rem_core` (`SecB/WTRemCore.lean`,
proved* 94ce5f1), TB.WT5v `starObs_vanish` and TB.WT5l `wt5_ret_law` (`SecB/WTRetLaw.lean`, proved*
4b68f70). Finding: `CapPoint.trans_rem` cannot be applied as stated, since it asks for own-core
moments up to order `p` and `H₀` has two unshifted core diagonals while (M3) gives order `≤ p/2`;
A-CREM uses only `n ≤ 2k_*+3`, so a relaxed copy (new node) is planned; the clip-observable lemmas
need an extension to the reciprocal factors `1/α_h` of the shifted diagonals. Previously open: `wt5_rem`, `wt5_ret` under `wt5_transfer` (`SecB/WT.lean`,
prover assigned). `wt3Rho_midpoint` and hence `wt3_gauss` are proved* (9841fce) by the route below,
with the generic lemmas in `Tight/Tools/LogConcaveDet.lean` (`det_mul_det_le_det_sq`, midpoint
operator convexity of the inverse, `MidLC` closure).
**Route for `wt3Rho_midpoint` (supervisor hint, 09:00 UTC; elementary, no matrix calculus, no
integral over t).** (a) `det A det B ≤ det((A+B)/2)²` for `A, B ≻ 0`: with `C = A^{-1/2} B A^{-1/2}`
(CFC sqrt), `det((A+B)/2) = det A · ∏(1+λᵢ)/2 ≥ det A · ∏√λᵢ` by AM–GM per eigenvalue
(`IsHermitian.det_eq_prod_eigenvalues`); principal submatrices are the same lemma. (b) For
`det P/det(P+hY)`, `Y = D²` diagonal `⪰ 0`, put `Q = P + hY` (affine in x). Sylvester
(`Matrix.det_one_add_mul_comm`) gives `det P/det Q = det(I − h D Q⁻¹ D)`. Midpoint operator convexity
of the inverse, `((Q₁+Q₂)/2)⁻¹ ⪯ (Q₁⁻¹+Q₂⁻¹)/2`, from the block matrices `[[Q, I],[I, Q⁻¹]] ⪰ 0`
(Schur complement zero, `Matrix.PosSemidef.fromBlocks₁₁`), summed, then Schur again. So
`M_mid ⪰ (M₁+M₂)/2` in Loewner order, `M = I − h D Q⁻¹ D ≻ 0` on the support; `det` is monotone on
the PSD order, then (a) gives `det M_mid² ≥ det M₁ det M₂`. (Check Mathlib names before use.) Section 1.4 (`SecC/`, notes `docs/tight/BP_SECC.md`, committed 08acc9a): exports
`SecC.in_markenv_pf`, `SecC.in_B1_pf`, `SecC.in_CR3_pf` (literal copies of the Contact inputs) and
`row_comparison_diff` (CR3′, for `in_CR3'`) proved from open nodes; SHIFTMAT, F1, QPHYS (`shiftQ_eq`),
B25, `insFH_ge` proved*. T.MARK-1/2 (`mark_grade_one`, `mark_grade_two_diag`,
`mark_grade_two_mixed`) proved* (a71c488). CR3 and CR3′ (`row_comparison_split`,
`row_comparison_diff`) proved from the shared `row_comparison_core` with the new nodes CR-REM
(`RowRem`), CR-RET, CR-G0 (`RowCompareParts`), CR-X5 (`RowX5`, separate X₅ bounds for CR3 and CR3′;
CR3′ does not follow from CR3) all proved*, and CR-GR (`row_grades_le`) proved from CR-G1, CR-G2,
CR-G3; CR-G3 (`row_grade3_le`, `RowG3`/`RowG3Pt`) proved* (08e62f7), CR-G1/G2 (`RowG1`/`RowG2`,
helpers `RowG12Aux`/`RowG12Mom`, row-wise interpolation since `(1+r_i)⁴` varies with `i`) proved*
(832db45). **All of SecC is proved*.** `mark_envelope_frob`, `shift_interp` proved* (so
`in_markenv_pf` is proved*); `core_transfer` proved from SecA's A-REM (`trans_rem`), A-SMOOTH,
A-E5, A-CLIP0, A-MAJ through the new node TRC-G (`SecC/TransferRet.lean`, `retained_grades_le`),
committed d6b60a5.
Section 1.2 (`SecA/`, notes `docs/tight/BP_SECA.md`, committed 68ef8d8): all files compile; exports
`SecA.in_E1`, `in_C2`, `in_C1`, `in_whiten`, `in_C3a` proved from open nodes; closing argument
(`scalar_ineq`, `theta_bound`, `concentration_C2` in all-vertex form), `bias_C6`, `row_bound`,
`core_kernel`, `preclosure_C3b`, `endpoint_E1_cp`, Hölder proved. New node A-SCHUR
(`SecA/Schur.lean`, `inv_eq_core_sub_add`: `Q⁻¹ = C − e_ve_vᵀ + s⁻¹(e_v−u)(e_v−u)ᵀ`, checked on 2000
random matrices) proved*, and with it `schur_C3`, `schur_C3_minus`, `coreGreen_le_greenP`,
`core_moment` (copy of the private deletion transfer as `SecA.coreE_eq_lawE_of_diagConj`) and the
seven Shift nodes (6b0c7ea). All nine Star nodes (A-CLIP, A-CLIP0, A-MAJ, A-E5, A-SMOOTH, A-EPB4,
A-CR, A-PDOM) proved* (b72cc49; calculus in `StarSmooth`, `StarLine`, `StarMat`, `StarCR`), so SecC's
`core_transfer` now waits only on A-REM (`trans_rem`). Transfer (A-E6, A-CREM, A-REM, A-HGR,
A-TRANS) and Conc (A-C1a `bias_C1a`, A-WHITEN `whiten`) proved* (9297875), hence also A-ROW, A-CK,
A-C3b and SecC's `core_transfer`. Statement finding: `whiten` (relative error
`C(p⁴/d)(E w + d⁻¹⁰)`) does not follow from the absolute grade-≥2 bound of `CapPoint.trans`, as
CHECK_SECS item 3 suggested; new nodes A-HGRR `CapPoint.hgr_rel` and A-TRANSR `CapPoint.trans_rel`
(`SecA/TransRel.lean`, T.TRC interpolation per retained term, `16Kk ≤ p`, `K = ⌊log d/300⌋`) and the
helper layer `SecA/ConcAux.lean` (`bias_gen`, `whiten_gen`), all proved*. The paper's whitening step
(l.413–424) claims only an absolute `Cp⁴/d`; the export needs the relative form, which these give.
Endpoint (A-RANK2 ×2, A-E1) proved* (9065681) through `SecA/EndpointPf*.lean` (rank-two inverse
by an explicit column, PD criterion by Cauchy–Schwarz, coefficient majorants of the fibre
polynomial, polynomial identity between the two endpoint expansions; Case A constant ≈ 888, Case B
≈ 1.141·10⁹ ≤ 1.15·10⁹). Shift (`transferred_TT`, `transfer_C4T`) proved* (dc15c12): `transfer_C4T_pf` in `SecA/C4T.lean` (sub-nodes: star-average identities `c4_ret0/12/34`, averaged Cramér–Rao `c4_cr`, transfers `c4_trans0/12/34` through `clip_trans_rel`/`clip_trans_abs` in `C4TTrans.lean`, using the low-moment variants `crem_w`/`trans_rem_w`/`trans_rel_w`; the constant is absolute but contains `e^{12000}` from the exponent `⌊log d/300⌋` of `trans_rel`). **All of SecA is proved*.** The
unused GCI-route files `Contact/RouteGCI.lean` and `Contact/RouteD9a.lean` (4 sorries, imported by
nothing on the main path) were deleted unproved (see FORMALIZATION.md, Part D, "Proof route"). Independent rule-2 check of
all remaining open sub-nodes running (`docs/tight/CHECK_FINAL.md`). The endpoint definitions moved to `SecA/EndpointDefs.lean` (6ab3d29, no
statement change) so that a separate prover proves `_pf` copies in `SecA/EndpointPf.lean`; rule-2
check of A-E1 redone against `precN`/`greenP` conventions (normalized rank-two step `t' = tτa√(y_vy_i)`
gives exactly `fibreDelta`), and Case A needs goodness only at the other endpoint, by the elementary
criterion `P ≻ 0, δ(t) > 0 ⇒ P + t·edgeE ≻ 0` (Cauchy–Schwarz in the `P` inner product; the reduced
2×2 form has determinant `δ/Δ`).

**Earlier notes.** D-walk and D-params-r (minimum principle on directed edges instead of
the walk series: `T(i→j) = τ_ij Σ_{k∼j, k≠i}` has row sums `≤ (d−1)τ_* = 1 − η₀`; `K' = I + Σ_j
M(i→j, ·)` solves `𝓑K' = I`). D-F2/F3 decomposition (`Tight/SourceMax/`, notes
`docs/tight/BP_SOURCEMAX.md`): direct chain rule in the sources, `DZ = −D_y⁻¹𝓑D_y⁻¹` on the positive
plus-sources, so neither the implicit function theorem nor the deletion lift of AUDIT-D §2.5 is
needed; `1{P≻0}det^{p−k}adj^k` is `C¹` for `k ≤ p−2`. Section 1.5 chain and its inputs
(`Tight/Contact/`, notes `docs/tight/BP_CONTACT.md`), paper's GR1 route with the route-dependent
nodes isolated. Generic tools T.ALPHA2, T.MAT, T.GIBP2, T.COV, B5, T.IL, T.DSTAR, UMI
(`Tight/Tools/`, notes `docs/tight/BP_TOOLS.md`). BLmid proof. Independent check of the GCI-free
route (`docs/tight/DR1_CHECK.md`). Section drafters (DAG from the audits, exports stated literally
as the Section 1.5 inputs, then proofs): lines 237–625 (`Tight/SecA/`, `docs/tight/BP_SECA.md`),
626–1076 (`Tight/SecB/`, `BP_SECB.md`; route-dependent GR1/DR1 nodes isolated), 1077–1333
(`Tight/SecC/`, `BP_SECC.md`). Independent rule-2 checks (sketches with explicit constants, small
cases, junk values, interfaces) of the stated nodes, read-only: `docs/tight/CHECK_CONTACT.md`
(Contact layer), `CHECK_TOOLS.md` (Tools, SourceMax), `CHECK_SECS.md` (sections A–C, Star).
Known clash to reconcile on merge: `kStar` is defined in both `SecA/Defs.lean` and
`SecC/Defs.lean`. **Check outcomes.** CHECK_CONTACT: every real leaf and every input of the contact layer
holds, except `d10_real`, which is false when its constant `CB < 0` (exact counterexample
`scripts/tight/check_contact_d10.py`); fix: add `0 ≤ CB` (the chain uses `CB` from `in_B1`, which is
positive). `in_C2` covers only the root, but the DR1 route needs (C2) at every vertex of `S` (DR1 at
the neighbours, W1′ remainder). CHECK_TOOLS: no false statement in `Tools/` or `SourceMax/`; the
hypotheses `k + 2 ≤ p`, `k + 1 ≤ p`, `3 ≤ p` (GIBP2) and `c ≤ 2m` (T.BLG) are necessary and present.

Sketches and checks: in the module docstrings. D-walk: strict diagonal dominance
`1 − Σ_j τ_ij/(1+τ_ij) ≥ η₀/(1+τ_*)`; walk-sum elimination `𝓑 S_{·w} = e_w` re-derived. D-F2: the
maximizer argument plus Lyapunov gives `m_k ≤ ((pr−k)/(p−k))^k` directly (no induction on `k`);
small cases `S = {i}` (`h = 1`), `λ = 0`. D-F3: `S = {v}` would violate F3 (`−y_v² ≤ −r y_v²`
fails) but has no contact (`E h_v = 1 < r`), so the contact hypothesis is essential and present.

## Part B — Theorem B

Parameters: `n : ℕ`, `q = n + 2`, `d = n + 3`, `r = rad n = 2√q = 2√(d−1)`. Rooted graphs are
`RGraph` (`Counterexample/Defs.lean`). All constructions are instances of `attachGraph C Y att`:
a core graph `C` on `K`, plus one copy of `Y` for each `i : ι`, the root of copy `i` joined to
`att i`. `join k Y` = new root + `k` copies of `Y` (Xu's `B`); `tree n h` = `T_h`;
`seed n h` = `H_h` (core `seedCore` on `Fin 4` = `o, v₀, v₁, v₂` as `0,1,2,3`, trees attached
with multiplicities `seedMult n = (n+1, n, n+1, n+1)`); `Qgraph n h j` = `Q_j`;
`coreGraph n h L` = `J = join (n+3) (Q_L)`.
`IsSignedAdj G A` (symmetric, `A_{uv}² = 1` on edges, `0` off edges) replaces signings inside the
proof: it is closed under negation and principal restriction. `green r A o = ((rI − A)⁻¹)_{oo}`
(Xu's `g`), `tval n A o = (√q/2)(green r A o + green r (−A) o)` (Xu's normalized `t`).

Design decisions: (1) the seed's positivity is proved directly by Schur complements (trees, then
the explicit 4×4 matrix) instead of Xu's unicyclic Lemma 6.1(i) (source Step 2), which is not
needed; (2) Step 5 eliminates the exterior pendant parent first (Schur complement of the `1×1`
block `r`), leaving the join lemma with root entry `r − 1/r`; (3) `h` is chosen through the limit
`g_h → 1/√q` (workflow §1).

| id | statement (source) | Lean name — file | deps | status |
|---|---|---|---|---|
| B-main | Theorem B | `bilu_linial_counterexample_proof` — `Counterexample/TheoremB.lean` | B-centre, B-structure, B-completion, B-decomp, C-spectral | proved* |
| B-completion | every connected finite graph of max degree `≤ d` is an induced subgraph of a connected `d`-regular finite graph (Construction 5) | `exists_regular_supergraph` — `Counterexample/Completion.lean` | — | proved* |
| B-structure | degree formulas and connectivity of `attachGraph`; `RootedDegLe (n+3)` for trees, seed, `Q_j`; `J` connected with max degree `≤ n+3` (Construction 1–4) | `Counterexample/Structure.lean` | — | proved* |
| B-decomp | `IsSignedAdj` closure (neg, submatrix, of a signing); the block decomposition of `rI − A` for `attachGraph`; `joinSub` (a branch of `join k Y` as `join 1 Y`); `(rI − A)` restricted = `rI − A` restricted | `Counterexample/AttachDecomp.lean` | — | proved* |
| B-attachschur | Schur complement for attached copies: `[[P, B],[Bᵀ, ⊕ᵢ Dᵢ]] ≻ 0 ↔ P − diag(Σ_{att i = c} (Dᵢ⁻¹)_{oo}) ≻ 0` (and `⪰`, inverse block) (Step 1) | `Counterexample/AttachSchur.lean` | C-schur | proved* |
| B-join | join lemma: with `p = r − Σᵢ green(Aᵢ)`, `rI − A ≻ 0 ↔ p > 0`, `⪰ ↔ ≥`, `green(A) = 1/p`; general root entry `α` via `rootShift` (Step 1, Xu Lemma 3.3) | `Counterexample/JoinGreen.lean` | B-attachschur, B-decomp | proved* |
| B-tree | `rI − A ≻ 0` and `green = (h+1)/((h+2)√q)` for every signed `T_h` (Step 3) | `tree_green` — `Counterexample/Tree.lean` | B-join | proved* |
| B-seed4 | the 4×4 matrix `M_τ` is PD with `(M⁻¹)_{00} = 1/(a − 1/(b − 2/(a − τ)))`, `τ = wyz` (Step 6) | `seed4` — `Counterexample/Seed4.lean` | — | proved* |
| B-seednum | `0 < g_h < 1/√q`; positivity of the seed denominators for `g ∈ [0, 1/√q]`; seed gain `∃ h, t(h) > 1` via the limit (Step 6, "Seed gain") | `Counterexample/SeedNumeric.lean` | — | proved* |
| B-seed | for every signed `H_h`: `rI − A ≻ 0` and `green(A) + green(−A) = u₁ + u₋₁` (Step 6) | `seed_green` — `Counterexample/Seed.lean` | B-tree, B-seed4, B-seednum, B-attachschur, B-decomp | proved* |
| B-step4 | `t(Z) ≥ 1/(2 − mean tᵢ)` with positive denominator (Step 4, Xu Lemma 3.3) | `join_tval_ge` — `Counterexample/Step4.lean` | B-join | proved* |
| B-pendant | if `rI − A ⪰ 0` on `join 1 X`, `X = join k Y`, and the copies of `Y` in `X` are PD, then `rI − A_X ≻ 0` (Step 5) | `pendant_posDef` — `Counterexample/Pendant.lean` | B-join, C-schur | proved* |
| B-amplify | Step 7 with Step 5 folded in: for `j + 1 ≤ N`, every `A` on `join 1 (Q_j)` with `rI ∓ A ⪰ 0` has `rI ∓ A_{Q_j} ≻ 0` and `t(Q_j) > 1 + 1/(N − j)` | `amplify` — `Counterexample/Amplify.lean` | B-seed, B-step4, B-pendant, B-decomp | proved* |
| B-centre | `∃ h L`, no signed `A` on `J` has `rI ∓ A ⪰ 0` (Step 8) | `core_not_bounded` — `Counterexample/Centre.lean` | B-amplify, B-seednum, B-join, B-decomp | proved* |

### Sketches and checks (B)

**B-main** (proved from children, compiles). `n := d − 3`; `core_not_bounded n` gives `h, L`;
`exists_regular_supergraph` applied to `J` (connected, degree `≤ n+3`) gives `F ⊇ J` induced,
connected, `(n+3)`-regular. For a signing `σ` of `F` with `‖A_σ‖ ≤ r`: `rI ∓ A_σ ⪰ 0`
(`opNorm_le_iff_posSemidef`), restrict along the embedding (`PosSemidef.submatrix`,
`smul_one_sub_submatrix`); the restriction is `IsSignedAdj J` — contradiction.

**B-centre.** `seed_gain n` gives `h` with `1 < tseed n h`; pick `N ≥ 2` with
`1 + 1/N < tseed n h`, `L := N − 1`. Given `A` on `J = join (n+3) Q_L` with `rI ∓ A ⪰ 0`: for each
branch `i`, restrict `A` along `joinSub Q_L (n+3) i` to `join 1 Q_L` (signed, `⪰` both); `amplify`
with `j = L` gives the branch copies PD and `tval > 2`. `join_posSemidef_iff` for `A` and for
`−A` (copy blocks of `−A` are `−` those of `A`) give `Σᵢ green(Aᵢ) ≤ r` and
`Σᵢ green(−Aᵢ) ≤ r`, so `Σᵢ tval ≤ (√q/2)·2r = 2q = 2(n+2)`, but `Σᵢ tval > 2(n+3)`.
Checks: parent B-main proved from it; `L = N − 1` gives `c_L = 2`, and `2(n+3) > 2(n+2)`.

**B-amplify.** Induction on `j`. `j = 0`: `Q_0 = seed`; the copy block of `A` is signed
(`IsSignedAdj.copy`), `seed_green` for it and its negation gives PD and
`tval = tseed n h > 1 + 1/N`. Step `j → j+1` (`j + 2 ≤ N`): `B :=` copy block of `A` on
`join (n+2) Q_j`; each branch of `B` restricted along `joinSub` is a signed `join 1 Q_j` with
`rI ∓ · ⪰ 0` (restrictions of `rI ∓ A`), so the IH gives the copies of `Q_j` PD with
`tval > c_j := 1 + 1/(N − j)`; `pendant_posDef` for `A` and `−A` gives `rI ∓ B ≻ 0`;
`join_tval_ge` gives `tval(B) ≥ 1/(2 − mean) > 1/(2 − c_j) = 1 + 1/(N − j − 1)` (`2 − mean > 0`,
`2 − c_j = 1 − 1/(N−j) > 0` since `N − j ≥ 2`). Checks: parent B-centre sketch uses it at
`j = N − 1`; `N = 2`, `j = 1` gives `c = 2`.

**B-pendant.** `A` on `join 1 X`: `rI − A = [[r, s e_oᵀ],[s e_o, rI − B]]` (`attach_decomp`, the
core `Unit` has zero block). The `1×1` block `r > 0`, so (`PosSemidef.fromBlocks₁₁`)
`rI − B − (1/r) e_o e_oᵀ = rootShift r (r − 1/r) B ⪰ 0`. `join_schur_root` with `α = r − 1/r`
gives `r − 1/r − Σ green(Bᵢ) ≥ 0`, so `r − Σ green(Bᵢ) > 0`, and `join_posDef_iff` gives
`rI − B ≻ 0`. Checks: `k = 0` gives `rI − 0 = r > 0`; used by B-amplify for `A` and `−A`.

**B-step4.** `join_green_eq` for `A` and `−A`: `green(±A) = 1/p_±`, `p_± > 0`. Then
`tval = (√q/2)(1/p₊ + 1/p₋) ≥ (√q/2)·4/(p₊+p₋)` and `p₊ + p₋ = 2√q(2 − mean tᵢ)`.

**B-seed.** `attach_decomp` + `attach_posDef_iff`: the copies are trees, PD with
`green = g_h` (`tree_green`); the complement on `Fin 4` is `M_τ` with `a = r − (n+1)g_h`,
`b = r − n g_h`, off-diagonal `−A` entries. `seed4` (denominators positive by
`seed_denoms_pos`, `τ = wyz = ±1`) gives PD and the `00` entry of the inverse, which equals
`green` by `attach_inv_toBlocks₁₁`. For `−A`, `τ ↦ −τ`, so the sum is `seedResp 1 + seedResp (−1)`.
Checks: `n = 0` gives multiplicities `(1,0,1,1)` = Xu's `H_h`.

**B-tree.** Induction on `h`. `h = 0`: one vertex, `A = 0`, `green = 1/r = 1/(2√q)`.
Step: `join_posDef_iff`, `p = 2√q − q(h+1)/((h+2)√q) = √q(h+3)/(h+2) > 0`, `green = 1/p`.

**B-join.** `join k Y = attachGraph ⊥ Y (fun _ => ())` with core `Unit`: `attach_decomp` then
`attach_posDef_iff` / `attach_posSemidef_iff` / `attach_inv_toBlocks₁₁`; the complement is the
`1×1` matrix `α − Σᵢ green(Aᵢ)`. Checks: `k = 0` gives `p = α`.

**B-seednum.** `s = √q`. `a ≥ (q+1)/s > 1`; `a − τ ≥ (q+1−s)/s > 0`; `b − 2/(a−τ) > 0` since
`(q+2)(q+1−s) > 2q`; the expressions decrease in `g`, so check at `g = 1/s`. Gain:
`t(∞) − 1 = 2(q²−2)/(q⁶+q⁵+q⁴+4q+4) > 0`; `g_h → 1/s` and continuity give a finite `h`.

**B-seed4.** `τ = wyz`, `a² − 1 = (a−τ)(a+τ)`; the `v₁v₂` Schur term is
`(ay² + 2wyz + az²)/(a²−1) = 2/(a−τ)`, then `a − x²/b' = a − 1/b'`. PD via completing squares
(coefficients `a, (a²−1)/a, b', p`); the inverse entry by the explicit solution of `Mu = e₀`.
Checks: parent B-seed proved from it.
**B-attachschur.** `(blockDiagonal D)⁻¹ = blockDiagonal D⁻¹`;
`B D⁻¹ Bᵀ = diag_c Σ_{att i = c} (D_i⁻¹)_{oo}` (only `w = w' = o` survive, `s_i² = 1`); then
`schur_posDef_iff`, `schur_posSemidef_iff`, `schur_inv_toBlocks₁₁`. Checks: parents B-join, B-seed
proved from it; `ι = ∅` gives `P`.
**A-star.** Flip `s(v,w)` is an involution fixing `F, M` and negating `s_w` only (`v ∉ N`);
off-diagonal terms vanish; variance terms survive only for `{c,d} = {a,b}`; column bound
`Σ_b M_ab² ≤ ‖M‖²`. **A-wnorm.** `wnorm` is a Euclidean norm of `(√wᵢ fᵢ)`; Chebyshev termwise.
**A-minor.** `(Σ_{j<2m}(−U)^j)(1+U) = 1 − U^{2m}`, so `(1+U)⁻¹ − P = U^m(1+U)⁻¹U^m ⪰ 0`;
`‖P‖ ≤ Σ‖τU‖^j ≤ 2m`. **A-lowerq-l2** dispatched after A-lowerq was proved from it.

**B-decomp, B-structure, B-completion**: see the file docstrings; the
completion doubles `G` (two copies, each vertex of degree `< d` joined to its twin) `d` times.

## Part C2 — Section 6, explicit excess (`BiluLinial/SecondOrder/Explicit/`)

Challenge form (maintainer's choice, 2026-09-30 04:30 UTC): every signing of some connected `d`-regular graph has
`‖A_σ‖ ≥ 2√q + q^{−11/2}/25`, `q = d − 1 ≥ 3`. Route: the Section 6 construction for every threshold
`R = q t + 1/t` with `0 < t`, `q t² < 1`, `F_q(t²) > 0`; then `t₀ = (1 − 1/(5q³))/√q`.

| id | statement | Lean (`Explicit/…`) | deps | status |
|---|---|---|---|---|
| C2-root | `F_q` increasing, unique root `z_q < 1/q` (sanity facts only) | `Root` | — | proved* |
| C2-num | `t₀` satisfies `q t₀² < 1`, `F_q(t₀²) > 0`, `q t₀ + 1/t₀ ≥ 2√q + q^{−11/2}/25` | `Excess` | — | proved* |
| C2-defs | `thr` (`R = q t + 1/t`), `treeResp`, `mresp`, `triMult = (n, n+1, n+1)`, `triSeed` (core `⊤` on `Fin 3`), `triQ`, `triCentre`, `seedResp3`, `seedMean` | `Defs` | B-defs | done |
| C2-treenum | `0 < g_h < t`, `R − q g_h > 0`, `g_h → t` when `q t² < 1` | `TreeNumeric` | defs | proved* |
| C2-tree | every signed `T_h` has `R I − A ≻ 0` and response `treeResp n R h` | `Tree` (`tree_resp`) | treenum, B-join | proved* |
| C2-seed3 | `[[b,−x,−y],[−x,a,−w],[−y,−w,a]] ≻ 0`, `(0,0)` inverse entry `1/(b − 2/(a − wxy))` | `Seed3` (`seed3`) | Mathlib | proved* |
| C2-seednum | seed denominators positive for `g ≤ t`; limit mean (6.3); some `h` with `seedMean > t₊` | `SeedNumeric` | treenum | proved* |
| C2-seed | the seed has `R I ∓ A ≻ 0` and `mresp = seedMean n t h` | `Seed` (`seed_resp`) | tree, seed3, seednum, B-attachschur, B-decomp, B-structure | proved* |
| C2-join | PD passes to copies; on `join k Y`: `R − Σ mᵢ > 0`, `m ≥ 1/(R − Σ mᵢ)` | `Join` (`copy_posDef`, `join_mresp_ge`) | B-join, B-decomp | proved* |
| C2-scalar | `u₀ > t₊` gives a uniform gain `ε > 0`: `c + ε ≤ 1/(R − q c)` for `c ≥ u₀` | `Scalar` (`step_gain`) | treenum | proved* |
| C2-amplify | `mresp ≥ u₀ + j ε` on `Q_j` | `Amplify` (`tri_amplify`) | seed, join | proved* |
| C2-centre | `tri_centre_not_bounded`: no signed `A` on `triCentre n h L` with `R I ∓ A ≻ 0` | `Centre` | seednum, scalar, amplify, join | proved* |
| C2-struct | root degrees `≤ d − 1`, core max degree `≤ d`, connected | `Structure` | B-structure | proved* |
| C2-param | (paper form) root `z`, `R < R_q` ⇒ admissible `t` with `R < thr n t` (continuity at `√z`) | `Param` (`exists_param`) | root | proved* |
| C2-main | (paper form) `explicit_excess_proof`: `γ_d ≥ R_q` | `Main` | param, centre, struct, B-completion, C-spectral | proved* |
| C2-thm | `explicit_excess_thm` (verbatim Challenge) at `t = t₀` | `Theorem` | centre, struct, num, root, B-completion | proved* |

**Sketches (C2), from the designer's report.** *centre*: `u₀ = seedMean > t₊`, gain `ε`, `L ≥ (R/(q+1) − u₀)/ε`;
`join_mresp_ge` gives `Σ mᵢ < R` but each `mᵢ ≥ u₀ + Lε ≥ R/(q+1)`. *amplify*: induction; `R − qc ≥ R − Σ mᵢ > 0`,
`m ≥ 1/(R − qc) ≥ c + ε`. *scalar*: `1/(R − qc) − c = (c − t)(qc − 1/t)/(R − qc)`, `ε = (u₀ − t)(q u₀ − 1/t)/R`.
*join*: `p± = R − Σ green(±Aᵢ)`, `green(±A) = 1/p±`, harmonic mean. *seed*: as B-seed with the triangle core;
`a = R − (n+1)g_h`, `b = R − n g_h`; `−A` flips `τ`. *seednum*: `(2t + 1/t)(t + 1/t − 1) − 2 =
(2t⁴ − 2t³ + t² − t + 1)/t² > 0`; `m(t) − t₊` has the sign of `F_q(t²)`. *treenum*: `t R = q t² + 1`,
`t − g_{h+1} ≤ q t²(t − g_h)`. *thr*: `‖A_σ‖ < 2√q + q^{−11/2}/25 ≤ thr n t₀` makes `thr I ∓ A_σ ≻ 0`, restrict to the core.
**Checks (C2).** Parent checks: `Main`, `Centre`, `Amplify` compiled while `Seed*` were `sorry`. Numerics on actual
graphs (random signings): tree responses exact (`q = 3, h ≤ 2`; `q = 4, h ≤ 1`); seed PD and `g(±A) = seedResp3(g_h, ±τ)`;
(6.3) and `m(t) > t₊ ⟺ F_q(t²) > 0` for `q ∈ {3,4,5,10}`; join inequality on an actual join; `k = 0` join gives `1/R`.
Degenerate `q = 2`: `q t² < 1` and `F₂(t²) > 0` are incompatible (`F₂(1/2) = 0`), so `tri_centre_not_bounded` is vacuous there.
No gap in Section 6 was found.

**C2-num sketch.** `t₀ = u₀/√q`, `u₀ = 1 − w`, `w = 1/(5q³)`. `q t₀ + 1/t₀ − 2√q = √q (1−u₀)²/u₀ ≥
√q w² = q^{−11/2}/25`. `P(u) = q⁴ F_q(u²/q) = −q⁴ + (q−1)q³u² + (q−1)q²u⁴ + q²u⁶ + (2q−4)u⁸` is convex
on `u ≥ 0`, `P(1) = 2q − 4`, `P'(1) = 2q⁴ + 2q³ + 2q² + 16q − 32`, so
`P(u₀) ≥ 2q − 4 − P'(1) w = 1.6q − 4.4 − 0.4/q − 3.2/q² + 6.4/q³ > 0` for `q ≥ 3` (`0.148` at `q = 3`;
exact `P(u₀) ≈ 0.167` at `q = 3`).
