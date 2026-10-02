# CHECK_FINAL — independent rule-2 check of the last open nodes (2026-10-01)

Read-only check of the open statements listed below, as of the working tree at about 04:15–05:00.
No `.lean` file was edited. For each node: the statement in mathematics, a proof sketch with the
constants made explicit, degenerate cases, and (where feasible) a numerical test. Script:
`scripts/tight/check_final_w1fib.py`.

Conventions. `Eventually P` means: for all `c₀, κ₀ ∈ (0,1]` there is `D(c₀,κ₀)` such that `P`
holds for all `d ≥ D` at `p = ⌊c₀d^{2/17}⌋`, `h = κ₀/p⁴` (`Tight/Ctx.lean`). A constant written
before `Eventually` (`∃ C, Eventually …`) is absolute, i.e. chosen before `c₀` and `κ₀`. In the
regime, `p ≥ c₀d^{2/17}/2 → ∞`, `p/log d → ∞`, `p⁵a² ≤ 1`, `pa ≤ 1` and `h > 0`.

**Summary: no node is FALSE and none is SUSPECT.** All ten open statements are OK as stated. The
hints at the end of the relevant sections are optional.

| node | file | verdict |
|---|---|---|
| TB.WT5r° `wt5_rem_core` | `SecB/WTRemCore.lean` (moved verbatim from `WT.lean`) | OK |
| TB.WT5v `starObs_vanish` | `SecB/WTRetLaw.lean` (moved verbatim) | OK |
| TB.WT5l `wt5_ret_law` | `SecB/WTRetLaw.lean` (moved verbatim) | OK |
| A-C4T-T0 `c4_trans0` | `SecA/C4T.lean` | OK |
| A-C4T-T34 `c4_trans34` | `SecA/C4T.lean` | OK |
| A-C4T `transfer_C4T` | `SecA/Shift.lean` (verbatim copy of `transfer_C4T_pf`) | OK |
| CR-G1 `row_grade1_le` | `SecC/RowG1.lean` | OK |
| CR-G2 `row_grade2_le` | `SecC/RowG2.lean` | OK |
| TB.W1fib-d1 `fibPhi_deriv_one`, `fibPhi_deriv_neg_one` | `SecB/W1FibD1.lean` | OK (verified numerically to 2·10⁻³²) |
| TB.W1fib-d3 `fibPhi_d3` | `SecB/W1FibD3.lean` | OK |

`A-C4T-T12` (`c4_trans12`) is already proved. `WT.lean` now imports `WTBase.lean` (definitions)
and `WTRemCore.lean`/`WTRetLaw.lean` (the three open nodes). I compared the moved definitions
(`precSub`, `wSub`, `diagSub`, `diagWSub`, `wtHSub`, `kerL`, `massQ`, `massT`, `starObsQ`,
`starObsT`, `coreRem`, `lJ`, `rootA`, `rootB`) with `HEAD`: they are identical.

---

## 1. SecB, weighted fresh-star domination (TB.WT5)

Common objects: a contact `ct`, `i ∈ N = N_S(v)`, `J = N_S(i)` (nonempty: `v ∈ J`), branch `e`,
map `T ∈ {T_dir, T_cav}`, `L = TᵀT ⪰ 0` (core-measurable), `|l| ≤ m₀`. The normalized
observables are `F°_Q = Φ·H(x)·q_L(x)` and `F°_T = tr L·Φ·H(x)` on the core support (`0` off
it), with `Φ = α₊^pβ₊^p`. `H(x) = H₀(x)·(X_e)_ii(x)²·(X₊)_ii(x)²`, where each diagonal is
`y_k((P̃(x) + zY)⁻¹)_kk`, `z ∈ {0, h}`.

### 1.1 `starObs_vanish` — OK

*Statement.* Eventually, for every contact, `i ∈ N`, `e`, `dir`, `l` (`|l| ≤ m₀`), signing `σ`,
`j ∈ retIdx(k_*) \ {0}` and sign vector `ξ` with `Φ(ξ) = 0`, `∂^{2j}F°_Q(ξ) = ∂^{2j}F°_T(ξ) = 0`.
There is no existential constant.

*Proof sketch.* If `W_core(σ) = 0`, then `F° ≡ 0`. Otherwise both cores are PD and `Φ(ξ) = 0`
gives `q_A(ξ) ≥ 1` or `q_B(ξ) ≥ 1`.
- If `q_A(ξ) > 1` or `q_B(ξ) > 1`, then `Φ ≡ 0` near `ξ`, hence `F° ≡ 0` near `ξ` (junk values
  of `Matrix.inv` are multiplied by `0`).
- Boundary `q_A(ξ) = 1` (the case `q_B = 1` is symmetric). By the vertex Schur formula,
  `P̃⁺(x) ≻ 0 ⟺ q_A(x) < 1` and `det P̃⁺(x) = det(core)·D_i·α(x)`. An unshifted diagonal is
  `y_k(core⁻¹_kk + (core⁻¹b(x))_k²/(D_iα(x)))` for `k ≠ i` and `y_i/(D_iα(x))` for `k = i`, so it
  has a pole of order exactly 1 in `α`. A shifted diagonal (`z = h > 0`) is smooth near `ξ`: at
  `q_A(ξ) = 1` the kernel vector `w` of `P̃⁺(ξ)` has `w_i ≠ 0`, so `wᵀ(hY⁺)w ≥ h y⁺_i w_i² > 0`
  (here `y⁺_i > 0`, since otherwise `A = 0` and `q_A ≡ 0`).
- Hence near `ξ`, `F° = α₊^{p-m₊}β₊^{p-m₋}·R̃` with `R̃` smooth and `m₊ + m₋ ≤ m₀`, where `m₊`
  (`m₋`) counts the unshifted plus (minus) entries of `l`. This identity also holds on
  `{α ≤ 0}`, where both sides vanish: junk `0` on `{α = 0}`, `Φ = 0` on `{α < 0}`. Derivatives
  of order `< p - m₀` vanish there.
- Derivative order: `2Σ_s j_s ≤ 4·grade(j) ≤ 4k_*` (since `j_s ≠ 1`). Moreover
  `4k_* ≤ 64p/log d + 4 < p - m₀` as soon as `log d > 128` and `p > 2(m₀+4)`. Both hold
  eventually.

*Degenerate cases.* `y_i = 0`: `A = B = 0`, so `Φ ≡ 1` and the hypothesis is never met.
`W_core = 0`: trivial. The `+4` in the docstring's `m_± ≤ m₀ + 4` is only needed if `h = 0`;
with `h > 0` the shifted factors have no pole.

### 1.2 `wt5_rem_core` — OK

*Statement.* Eventually (no `∃ C`; this holds for each fixed `m₀, M`),
`|E_core[𝖦F°_Q − Σ_{|j|_g ≤ k_*} c_j 𝖱∂^{2j}F°_Q]| + (same for F°_T) ≤ F_H·d^{-M-1}`.

*Size check.* By (E4), the remainder at depth `k_*` is at most `poly(d, h⁻¹)·(Cp)^{4k_*+4}
(5/d)^{k_*+1}` times core moments. Against the floor `F_H ≥ 40^{-p}` (M4) and (E6), this is
`≤ M_poly·e^{-p}/d·F_H` (the shape of `trans_rem_w`). Since `p/log d → ∞`,
`e^{-p}·poly(d) ≤ d^{-M-1}` eventually for every fixed `M`. The bound has the right form.

*Checks.*
- `h⁻¹` factors: derivatives of a shifted diagonal cost `√b_s/α`, not `h^{-1/2}`, because
  `α_h ≥ (D_iα + hy_i)/(D_i + hy_i)` (from `bᵀ(core+hY)⁻¹b ≤ bᵀcore⁻¹b`). The `1/α` powers
  are absorbed by `α^{p-m₀}`. A per-derivative `1/√h` would cost `e^{+15p}` and break the
  bound, so the docstring's reciprocal bound (R3) is the essential point.
- The remaining `poly(d, h⁻¹)` (`X ≤ 1/h`, `‖T‖`, `q_L`) is harmless.
- `SmoothBdd (4k_*+4)` holds globally. `F°` is `C^{p-m₀-1}`. It is constant in each coordinate
  `s` with `y⁺_s = y⁻_s = 0`: `precSub` has `√y_s` in the incident entries, and column `s` of
  both `T_dir` and `T_cav` carries `√y⁺_s` through `C₊(·, s)`. In the other coordinates its
  support `{q_A < 1, q_B < 1}` is bounded.
- The missing `√b_s` factors of the (at most two) derivatives that fall on `q_L` are paid by
  `L_ss/A_ss ≲ poly(d)/y_i`. The `1/y_i` cancels against `(X₊)_ii² ∝ y_i²` in `H`; this is the
  source's "`Z_i⁺` cancels against `(X₊)_ii²`".

*Hint.* `CapPoint.trans_rem_w` (`SecA/C4TTrans.lean`) is exactly the A-REM with own-core moments
only up to order `2k_* + 3` that the docstring asks for. A `Contact` yields a `CapPoint`
(`ContactCtx` extends `CapCtx`), so the moment obstacle noted in the docstring is already removed.

*Degenerate cases.* All cores unsupported gives `E_core = 0` (`coreE` divides by `0`). `F_H > 0`
by `insF_pos_ct`.

### 1.3 `wt5_ret_law` — OK

*Statement.* `∃ K ≥ 0` (depending on `m₀, M` only), Eventually:
`|Σ_{1≤|j|_g≤k_*} c_j E[∂^{2j}F°_Q(ξ)/Φ(ξ)]| + (same for F°_T) ≤ K(p⁴/d)(x + y + d^{-M})`,
with `x = massQ = E[H q_L(ξ)]` and `y = massT = E[H tr L]` (the full law, the same `H`).

*Sketch (source (WT4)/(WT5), AUDIT-B §2.5).*
- On the support, `ξ` is interior and `Φ(ξ) > 0`. Unsupported `σ` have weight `0`, so the junk
  division is harmless.
- Every derivative of `H` is multiplicative: `|∂_s X_kk| ≤ 2aX_kk√(X_iiX_ss)`, and a zero
  source makes the factor `≡ 0` in `x`. At most two derivatives fall on `q_L`
  (`|(Lξ)_s|² ≤ L_ss q_L`, `Σ_s√L_ss ≤ √(d tr L)`).
- Grade one (`j = 2e_s`) gives `≤ C(p⁴/d)x + C(p²/d)y + C(p³/d)√(xy)` times multipliers
  (`D_*` powers, `1/α` powers, both with `e^{-cp}` tails).
- The multipliers are removed by truncation at an absolute threshold plus Cauchy–Schwarz:
  `E[(Hq_L)²] ≤ poly(d)` and `P(Mult > T) ≤ e^{-cp} ≪ d^{-2M-C}`. This yields the floor
  `d^{-M}`, and `K` independent of `c₀, κ₀` (shifted diagonals are bounded by unshifted ones, so
  no `h` enters `K`).
- Grade `g` costs `(Kp⁴/d)^g`, and the geometric sum converges since `p⁴/d → 0`.

*Degenerate cases.* `y⁺_i = 0` or a zero source in `l`: `H ≡ 0` in `x`, so both sides vanish.
`L = 0` on a core: `F° ≡ 0` there. In particular there is no case with `x = y = 0` and a nonzero
left side.

The parents `wt5_ret_core`, `wt5_rem`, `wt5_ret`, `wt5_transfer`, `wt2` consume exactly these
forms (`wt5_rem` turns `F_H d^{-M-1}` into `d^{-M-1} ≤ (p⁴/d)d^{-M}`).

---

## 2. SecA, transfer of (C4) — `c4_trans0`, `c4_trans34`, `transfer_C4T`

Common hypotheses: `RegA d p`, `cp.DefLe ρ`, `M` core-measurable with `0 ⪯ M ⪯ A` on good cores.
The constant `C` is absolute (`∃ C` before `∀ d p`).

### 2.1 `c4_trans34` — OK

*Statement.* `|E_core(𝖦F₃₄ − 𝖱F₃₄)/F_H| ≤ C(p⁴(ρ+b₀)/d + e^{-p}/d)`, where
`F₃₄ = q_{AMA}α^{p-2}β^p + q_{BMB}α^pβ^{p-2}`.

*Sketch.* Apply `clip_trans_rel` (`C4TTrans.lean`) to each term separately: `quadFn 0 0 (AMA)`
with `(e₁, e₂) = (p-2, p)`, and `quadFn 0 0 (BMB)` with `(p, p-2)`.
- Sup and endpoint majorants come from `C4.quadMaj_dom`. `A-PDOM` (`SecA.pdom`) gives
  `AMA ⪯ ΘA` and `BMB ⪯ ΘB`, so take `Q = A`, resp. `B`. Then `q_Q ≤ 1` on the support,
  `Q_ii ≤ A_ii + B_ii` (sup weights) and `Q_ii ≤ endLam_i²` (from `endLam_maj`), with scale
  `Θ = tr(A² + B²)`.
- Core moments come from `coreE_Theta_pow_le` (`≤ 9ⁿ`, `4n ≤ p`, and `2k_*+3 ≤ p/4`).
- The relative factor is `X = Θ(τ^±)²`: `E[Θ(τ⁺)²] ≤ 12·C_Θ(ρ+b₀)·B_Y` by `E_Theta_mul_le`
  (T.IL, `preclosure_C3b`), and `E X² ≤ B²` by `E_Theta_pow_le`/`h_moment`.
- This is the same pattern as the proved `trans_pair`; the result has the stated form, with
  `M = 9` and an `e^{-p}/d` remainder.

### 2.2 `c4_trans0` — OK

*Statement.* `|E_core(𝖦F₀ − 𝖱F₀)/F_H| ≤ C(p⁴(ρ+b₀)/d + p²/d + p⁸/d² + e^{-p}/d)`, where
`F₀ = (tr M − q_M)Φ`.

*Sketch.* Use `trans` (A-TRANS, `Transfer.lean`), which keeps grade one separate. Sup majorant
`1 + tr A` (core trace moments for `2n ≤ p`); endpoint majorant for grades `≥ 2` of size `O(1)`,
giving `e(K_g p⁴/d)²·O(1) = Cp⁸/d²`; remainder `e^{-p}/d`. Grade one,
`Σ_i (1/12)E[∂_i⁴F₀/Φ]`, uses EPB4 (`iter_pderiv_clipObs_le`):
- `r_i = a(|G⁺_vi| + |G⁻_vi|)`, from F1 `(Aξ)_iτ⁺ = −aG⁺_vi`.
- Monomials with `≥ 2` row factors: T.IL against `row_bound`
  (`a²ΣE(G^±_vi)² ≤ C(ρ+b₀)` under `DefLe ρ`) gives `p⁴(ρ+b₀)/d`.
- Monomials with one row factor: `p³a³√d·√(ρ+b₀) ≤ p²/d + p⁴(ρ+b₀)/d`.
- Monomials with no row factor: `12p²Σ_iA_ii²·|tr M − q_M| ≲ p²/d`.

This is AUDIT-A §2.13 (gap A7). The `p²/d` term is genuinely needed and is present in the
statement and in the parent.

### 2.3 `transfer_C4T` (`Shift.lean` l.558) — OK

Its type is token-for-token that of `transfer_C4T_pf` (`C4T.lean`), which is proved from
RET×3 (proved), CR (proved), T12 (proved) and the two nodes above. `C4T.lean` imports
`C4TRight → {C4TTrans → Conc, ShiftC5}`. `Shift.lean` imports only `ShiftC5`, so adding
`import BiluLinial.Tight.SecA.C4T` to `Shift.lean` creates no cycle (`Closure` imports `Shift`,
and nothing in the C4T chain imports `Shift`/`Closure`). Degenerate case `N(v) = ∅`: everything
is `0`.

---

## 3. SecC, row grades — `row_grade1_le`, `row_grade2_le`

*Statements.* `∃ C > 0`, Eventually, for every `CapCtx` point and root `v`, and every
`ϑ ≤ λ_r ≤ λ_c ≤ δ_c` with `S₊/d ≤ λ_r`, `S₋/d ≤ δ_c`, `markE₊/d² ≤ λ_c`, `markE₋/d² ≤ δ_c`:
- G1: `|Σ_{|j|_g=1} c_j rowRet j| ≤ a²C(p⁵X₅ + p⁴√(λ_cδ_c))`;
- G2: `|Σ_{|j|_g=2} c_j rowRet j| ≤ a²C·p⁴√(λ_cδ_c)`.

### 3.1 `row_grade1_le` — OK

`j = 2e_i` and `c_j = 1/12`. At supported `σ`, `mark_grade_one` at `ξ` divided by `Φ(ξ) > 0`
gives `1000a⁶(1+r_i)⁴(p⁵|Σ_jx_j(x_j−z_j)| + p⁴Σ_jm_ij)`. Write
`Σ_ia⁶(1+r_i)⁴ = a⁴·rowWt`, `R₊ = a²Σx²`, `E₊ = a⁴Σ_{ij}e_ij²`, `F₋ = a⁴Σf²`.
- The `p⁵` part is exactly `a²p⁵X₅`. Note that `X₅` keeps `|·|` inside `E`, as the pointwise
  bound needs.
- `x²` marks: `a²·rowWt·R₊`, and `E[rowWt·R₊] ≤ C(E R₊ ∨ ϑ) ≤ C'λ_r` (T.IL with
  `θ = ϑ = d^{-10}`; this is why `ϑ ≤ λ_r` is a hypothesis). Also `E R₊ = a²S₊ ≤ λ_r/2`.
- `e²` marks: `a²(1+r_i)⁴ ≤ rowWt`, and `E₊ ≤ 2a⁴G_vv²‖G[N,N]‖_F² + 2R₊²`, so this is
  `≤ rowWt·E₊`; `a⁴markE₊ ≤ λ_c/4` (`a²d ≤ 1/2`).
- Cross marks, e.g. `|x_jf_ij|`: Cauchy–Schwarz over `(i,j)` gives `≤ a²√(W₈R₊F₋)` with
  `W₈ = a²Σ(1+r_i)⁸`. In expectation this is `≤ a²C√(λ_rδ_c)`.
- Every term is `≤ a²Cp⁴√(λ_cδ_c)`, using `λ_r ≤ λ_c ≤ δ_c`. No `f²`/`z²` mark appears alone
  (only cross terms), which is why the minus-branch hypotheses carry `δ_c`.

### 3.2 `row_grade2_le` — OK

`j = 3e_i` (`c = −1/45`) and `j = 2e_i+2e_k` (`c = 1/144`). By `mark_grade_two_diag/mixed`,
every term carries `a²·10⁶p⁹` and two marks.
- Diagonal: `a²·10⁶p⁹·a²W₆R₊` etc. (`W₆ = a²Σ(1+r_i)⁶`); the extra mark `|x_jz_j|` gives
  `W₆√(R₊R₋) → √(λ_rδ_c)`.
- Mixed: `Σ_{i≠k}a⁸(1+r_i)⁴(1+r_k)⁴ ≤ (a²rowWt)·a²·rowWt`.
- Total `≤ a²·C·(p⁹a²)·√(λ_cδ_c)`, and `p⁹a² ≤ p⁴` because `p⁵a² ≤ d^{10/17}/(4(d−1)) ≤ 1`
  in `TRegime`.
- The order of `i, k` in `dEven` (list order of `univ.toList`) does not matter: the
  `mark_grade_two_mixed` bound is symmetric in `i, k`, and `F` is `C^{p-3}` near interior `ξ`.

*Degenerate cases (both).* `N = ∅`: empty sums, and the right side is `≥ 0` (`C > 0`,
`X₅ ≥ 0`). `y_v = 0`: `A = B = 0`, `F ≡ 0`. `p ≥ 8` holds (needed by the mark lemmas).

---

## 4. SecB, W1 edge fibres — `fibPhi_deriv_one/neg_one`, `fibPhi_d3`

### 4.1 `fibPhi_deriv_one`, `fibPhi_deriv_neg_one` — OK

*Statement.* At a PD endpoint (`h ≥ 0`, `σ_ij = 1`, `j ∈ N_S(i)`):
`φ'(1) = W(σ)·cfgD(σ)` and `φ'(−1) = W(σ')·cfgD(σ')`.

*Hand derivation (matches `fibD` term by term).*
- `∂_tP̃^± = ±a√(y_iy_j)E`, so `∂log W = 2pa(G⁺_ij − G⁻_ij)`.
- `∂X_ε,kl = −εa(X_kiX_jl + X_kjX_il)` for shifted or unshifted `X`, zero sources included.
- `∂Ω₊ = dOmP`, `∂Ω₋ = dOmM`.
- `∂U = −εa(X_e,·iU_j· + X_e,·jU_i·) − a(U_·iX₊,j· + U_·jX₊,i·) + X_e diag(∂f) X₊`.
- `∂F_ji = −2εaX_e,ijF − aX₊,ijF + aX₊,iiX_e,ijU_ij − aX_e,iiX₊,iiU_jj + maskF(∂f)`.
- `∂b₊ = dbP`, `∂b₋ = dbM`.
- At `t = −1` the direction `E` is the same, so the formula evaluated at `σ'` is right.

*Numerical check (independent, exact Lean model).* `check_final_w1fib.py`: `V = S ∪ {padded
vertex}`, `diagD = 1 + Σc(a²y_iy_j)`, `a = 1/√(4(d−1)+4/p)`, `srcDiag` only on `S`, `physInv`
with the identity padding, about 20 % zero sources, fibres with `j = v`, `j ∈ N` and
`j ∈ N(N)\N`, `d ∈ {7, 30, 1000}`, `p ∈ {2, 3, 7}`, all four configurations, 2560 PD endpoints.
At 100 digits (step `10⁻⁴⁰`) the maximal relative error is `2·10⁻³²`. At 40–60 digits, apparent
failures occur only where `W·cfgD = W·Ψ = 0` analytically; that is roundoff, and it disappears
with precision.

### 4.2 `fibPhi_d3` — OK

*Statement.* `∃ K > 0, ∃ M` (absolute), Eventually, on every regular fibre (`fibGood` at `σ` or
at `σ'`) and every `t ∈ [−1,1]`: `|φ'''(t)| ≤ K(W(σ)Yb_M(σ) + W(σ')Yb_M(σ'))`, where
`Yb_M = a³D_*^M(p³R² + p)/(√d h)`.

*Sketch with constants.* Let `τ₀` be the good endpoint, `|s| ≤ 2`, `64pag* ≤ 1`.
- Segment comparison: `|xᵀ(scE)x| ≤ 4a√(G_iiG_jj)Q ≤ Q/(32p)`, so `G(t) ⪯ (1+1/(31p))G(τ₀)`
  and `D_*(t) ≤ 2D_*(τ₀)`.
- Weight: `|δ_± − 1| ≤ 2ag* + a²g*² ≤ 1/(30p)`, so `W(t) ≤ e^{1/15}W(τ₀)`.
- Off-diagonal: `R(t) ≤ R(τ₀) + 8aD_*²` (rank-two inverse formula).
- Derivatives of the weight: `|ℓ'| ≤ 2paR`, `|ℓ''| ≤ 4pa²D_*²`, `|ℓ'''| ≤ 32pa³D_*³`.
- Derivatives of the observable: `|Ψ^{(r)}| ≤ C_ra^rD_*^{C}/(√d h)`, with one `1/h` from
  `X² ⪯ X/h` (valid with zero sources since `Y ⪯ (P̃+hY)/h`) and `‖u‖_∞, ‖b‖_∞ ≲ D_*²/√d`.
  All needed diagonals lie in `{v} ∪ N ∪ N(N)` (`i ∈ N`, `j ∈ N(N)`, `supp b ⊂ N(N)`).
- Assembly: `R ≤ 2D_*`, `p²R ≤ (p³R² + p)/2`, `p³a²D_*⁴ ≤ pD_*⁴`. Then `K` and `M` are
  absolute (`M` is a fixed degree count, of order 10–15).

*Numerical check.* With the exact model, `d` decoupled (`√d = 1024p`, so regular fibres exist)
and `p ∈ {3, 10, 30, 100}`, take `Q_M = sup_{[−1,1]}|φ'''|/(W Yb_M + W'Yb'_M)` over 128 regular
fibres each. `Q_0` decreases from `4.2·10⁻³` (`p = 3`) to `7.4·10⁻⁸` (`p = 100`); `Q_4` from
`5·10⁻⁵` to `10⁻⁹`. There is no growth in `p`, so an absolute `K` is consistent even with `M = 0`. On a regular
fibre the second endpoint has `W > 0` by the proved `fib_seg_pd`.
