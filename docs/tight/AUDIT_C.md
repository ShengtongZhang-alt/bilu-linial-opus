# AUDIT-C: lines 1077–1560 of `docs/second_order_bilu_linial_tight.tex`

Scope: Section 1.4 "Comparison of fresh-star row energies" (Contact row comparison CR1–CR3,
Multiplicative shifted trace comparison B1–B5 with the Brascamp–Lieb step) and the first part of
Section 1.5 (D1–D10). Context read: lines 1–1076 (notation, F1–F3, E1–E6, C1–C6, GR1, S1, W1–W5,
WT1–WT5) and, to calibrate what the endgame needs, lines 1935–2053.
Scripts: `scripts/tight/auditC_symbolic.py`, `auditC_numeric.py`, `auditC_params.py`.

---

## 0. Summary

### 0.1 Verdict

**Correct, with minor fixes only. No fatal gap and no gap that forces a statement change.**
Every displayed claim in lines 1077–1560 was re-derived. The algebraic identities (CR2, the
`K_i` third-derivative identity, the loop-to-(D3) algebra, the Schur identities, C5, B5, the
CR1 Frobenius decomposition) were checked symbolically or numerically. All constants are
absolute or depend explicitly on `c_0, κ_0`, and nothing is circular: `c_0, κ_0` are fixed by the
endgame from absolute constants, and `d_0 = d_0(c_0, κ_0)`.

The **Brascamp–Lieb step in B1 is needed in its variable-Hessian form**: the constant-Hessian
(Prékopa-only) covariance bound and the exact IBP identity both fail by a factor that is fatal
for the endgame (§5.2). **However, the variable-Hessian BL needed here follows in about one page
from midpoint Prékopa–Leindler** (which the project needs anyway for fact (a)). The argument is a
tilt plus a parallelogram inequality for `α = 1 − xᵀAx`. It needs no PDE, no smoothing, no
Hessians and no operator monotonicity (§5.3–5.4). The paper's PDE sketch (`Lw = f − Ef`) is
correct as mathematics, but formalizing it would need elliptic existence and regularity theory
that Mathlib lacks. Replace it.

### 0.2 Gaps and fixes

| id | where | severity | issue | fix |
|---|---|---|---|---|
| G1 | B1 proof, l.1231–1242 | minor (proof replacement) | BL proved via the Neumann problem `Lw = f − Ef` plus Bochner plus "smooth convex approximation". Mathematically fine, but it needs existence/regularity of a degenerate elliptic problem on a convex domain, which is unformalizable at reasonable cost. | Use **BLmid** (§5.3): midpoint PL with a tilt `e^{±ε⟨θ,x⟩}` and the exact inequality `α(z+w)α(z−w) ≤ α(z)² exp(−2q_A(w)/α(z))`. It gives `Σ_ν ⪯ E_ν(I+H)^{-1}` directly with the paper's `H`. |
| G2 | B1, l.1227–1228 | minor | `E_ν(I+∇²V)^{-1} ⪯ E_ν(I+H)^{-1}` uses operator antitonicity of the inverse. | Not needed: apply BLmid with modulus `K = I + H` directly, since the midpoint hypothesis holds with `H ⪯ H_A`. |
| G3 | B1, l.1243 | minor | `H(I+H)^{-1} ⪰ H − H²` is stated without proof. | `I−(I+H)^{-1} − (H−H²) = H·[H(I+H)^{-1}]·H ⪰ 0` (commuting PSD); then `tr(M·PSD) ≥ 0`. |
| G4 | CR1 statement | minor (hypothesis made explicit) | "λ is a polynomial envelope": the floor `λ ≥ ϑ = d^{-10}` is needed by the interpolation. "At a plus mean contact" is not used. | State CR1 with hypotheses `ϑ ≤ λ ≤ C_λ δ`, and drop the contact hypothesis (keep the capped law). Better: prove only the split form CR3 (CR1 is the special case `λ_r=λ_c=C λ`, `ρ_r=δ_c=Cδ`). |
| G5 | B3/B4, l.1277–1293 | minor | Interpolating a degree-`O(j)` multiplier at grade `j` needs a grade-dependent Hölder exponent `k_j ≍ p/j`, so that only moments `≤ p/2` are used. The display `(Cp⁴/d)^j(x+ϑ)ϑ^{-Cj/p}` is consistent with that, but the paper does not say so. | Make `k_j = ⌊p/(C' j)⌋` explicit. Then `ϑ^{-1/k_j} = e^{10 C' j log d/p} ≤ 2^j` for `d ≥ d_0`. |
| G6 | B1 notation | cosmetic | `N` denotes both the neighbourhood `N(v)` and the matrix `a²Y_-/Z_v^-`. | Rename the matrix `𝒩`. |
| G7 | D6, l.1486 | cosmetic (sharper) | "`E_λ ≤ Cp`" | In fact `E_λ ≤ C(c_0^{17/3}+o(1))`, since `p⁵√(λ_1δ) ≤ C c_0^{17/12}p^{17/4}d^{-1/2} ≤ C c_0^{17/3}`. |
| G8 | D9a, l.1508 | remark | The floor "+1" in `λ_r = C(S+1)/d` is harmless because `S ≈ 4` anyway (D15). **GR1's `√p` gain is load-bearing here**: with `ρ_r = Cδ` instead of `Cδ/p`, `E_row` grows to `≍ c_0^{17/3}p^{-1/2}`, which is far above the endgame margin `p^{-1}` (checked numerically; `auditC_params.py`). Royen/GR1 cannot be bypassed in D9a. | none (record the dependence) |
| G9 | D2 | cosmetic | The `O(η_0)` term is negative: `p·d(r−1)(1−r L̄) = 1 − (3/2)pη_0 + …`. Lines 1077–1560 use only `1−r L̄ ≥ 0`. | Record the explicit bound `d(r−1)(1−r L̄) ≥ 1/p − 2η_0` for `d ≥ d_0` (numerically verified for `10^{20} ≤ d ≤ 10^{200}`, `c_0 ∈ {1, 0.1}`). |

No other issues. In particular, CR1–CR3, B2–B5, D3–D10 hold as stated, with the constants listed
in §0.5.

### 0.3 Brascamp–Lieb conclusion (short form)

- **Measure.** Fix the core (so `A, B, M, 𝒩 ⪰ 0` are fixed `n×n` matrices, `n = |N(v)| ≤ d`).
  `ν(dx) ∝ α_+(x)^{p−1} β_+(x)^p γ_n(dx)` with `α = 1 − xᵀAx`, `β = 1 − xᵀBx`, `γ_n` the standard
  Gaussian on `ℝ^N`. This is a Gaussian times an even log-concave factor. Its Lebesgue density is
  `e^{−U}`, with `U = |x|²/2 + V`, `V = −(p−1)log α − p log β` on `Ω = {α>0, β>0}`, and `+∞` off `Ω`.
  `∇²V = (p−1)(2A/α + 4Axxᵀ A/α²) + p(2B/β + 4Bxxᵀ B/β²) ⪰ H(x) := 2(p−1)M/α + 2p𝒩/β`.
- **Function.** BL is applied only to **linear** functions `x ↦ ⟨θ,x⟩`, and only through
  `tr(MΣ_ν) ≤ E_ν tr(M(I+H)^{-1})` (`θ` ranging over a factorization `M = Σ_k θ_kθ_kᵀ`).
- **Needed statement (BLmid).** For `ρ ≥ 0` even and integrable on `ℝⁿ`, and `K(z) ⪰ κI` measurable
  (`κ > 0`) with `ρ(z+w)ρ(z−w) ≤ ρ(z)² e^{−⟨w,K(z)w⟩}` for all `z, w`:
  `∫⟨θ,x⟩²ρ ≤ ∫⟨θ,K(x)^{-1}θ⟩ρ`. Here `ρ = α_+^{p−1}β_+^p e^{−|x|²/2}` and `K = I + H`.
- **Proof.** Midpoint PL applied to `ρe^{±ε⟨θ,x⟩}` gives `E_ν cosh(ε⟨θ,x⟩) ≤ E_ν e^{(ε²/2)⟨θ,K^{-1}θ⟩}`;
  then `ε → 0`. The same lemma with constant `K` **is** fact (a) (`Cov ⪯ M^{-1}`), so one node serves
  N_G ≥ 0 (C1), the whitening `N_G ≥ f_G w` (C2/D6), WT3, and B1.
- **Not sufficient:** (a) with constant modulus (`H_0 = 2(p−1)M + 2p𝒩`) loses the factor
  `α ≈ 1/D_v h_v ≈ 1/2` on the main term, which must cancel exactly against the row-free part of
  `Q_*` (RC5). (c) the exact identity `I−Σ = E∇²V − E∇V∇Vᵀ` gives an upper bound of the wrong
  quality: its error term `4p²E_ν q_{B M B}/β²` is `≍ p⁵δ/κ_0 ≫ p^{-1}`. (b) Gaussian IBP is needed
  separately (for `2𝖦F = N_G`). (d) E4 is needed separately (transfers). See §5.2.

### 0.4 External theorems needed (exact special cases)

1. **Midpoint Prékopa–Leindler** on `ι → ℝ` (Lebesgue), `ι` finite: for measurable
   `f, g, h : (ι→ℝ) → [0,∞]` with `h((x+y)/2)² ≥ f(x)g(y)` for all `x, y`:
   `(∫⁻h)² ≥ (∫⁻f)(∫⁻g)`. Used only through BLmid (§5.3). Not in Mathlib. This is the long pole of
   this section.
2. **Gaussian integration by parts** on `gaussPi ι` for `C¹` functions whose value and gradient
   grow polynomially: `E[x_i φ(x)] = E[∂_iφ(x)]`. Needed for `φ = x_j g` and `φ = g` with
   `g = α_+^{p−1}β_+^p` (`C¹` once `p ≥ 3`). Partly present (`Tight/Gauss/IBP.lean`:
   `stein_gaussianReal`).
3. **E4** (Gaussian/sign comparison through `e^{t²/2}/cosh t`), **E5** (derivative accounting) and
   **E6**, from Section 1.2: internal nodes, not external. Used in CR1/CR3, B4 and D6.
4. Elementary matrix analysis (Mathlib or `Common/`): the Schur complement determinant and block
   inverse; Loewner-order facts (§3, T.MAT); `|G_ij| ≤ √(G_ii G_jj)`.
5. Hölder, Minkowski, Jensen and Young (Mathlib).
6. **Royen's GCI** (Milman's monotonicity form) enters this range only through GR1 in D9a, and is
   load-bearing there (G8). It is used nowhere else in lines 1077–1560.

### 0.5 Explicit constants and quantifier levels

Order of choices: absolute constants `C_E4, C_der, C_mom, C_IL, C_δ, C_row, C_S1, C_E1, …` (from
earlier sections, independent of `c_0, κ_0, d`, the graph and the sources) → `κ_0, c_0 ∈ (0,1]`
(endgame, l.2034) → `d_0(c_0, κ_0)` → `d ≥ d_0`, `p = ⌊c_0 d^{2/17}⌋`, `h = κ_0 p^{-4}`,
`ϑ = d^{-10}`, `k_* = ⌈16p/log d⌉`.

| quantity | paper | explicit form here |
|---|---|---|
| `a²d` | `≍1` | `1/4 ≤ a²d ≤ 1/4 + 1/d` (exact from `a² = 1/(4(d−1)+4/p)`) |
| `s` | `2+O(d^{-1}+η_0)` | `2−η_0 ≤ s ≤ 2 + 2/(q−1)` |
| `r−1` | `≍(pd)^{-1/2}` | `(1−η_0)/√(pq) ≤ r−1 ≤ 1/√(pq)`, so `∈ [1/(2√(pd)), 1.01/√(pd)]` |
| `‖M‖, ‖𝒩‖` | `≤ Ca²/h` | `≤ s a²/h` |
| B5 | `C p²a²/h` | `α^{-1}tr(MH²) ≤ 8p² (s a²/h)(X_1t_+ + X_2t_−)` |
| CR1 Frobenius | `2, 2` | exact: `a⁴G_vv²‖G[N,N]‖_F² ≤ 2t_+²trA² + 2(a²Σx_i²)²` |
| `E\|x_J\|² ≤ Cλ` | `C` | `S_+/d ≤ (a²d)^{-1} a²S_+ ≤ 4λ` |
| `x` vs `Q` | – | `x ≤ a²Q/(p−1)` (exact) |
| `η_BL` | `C{p/(dh)+p⁴/d}` | `η_BL = 8C_TR p⁴/d + 32 s C_IL p/(dh)` (see §4.3) |
| `ε_BL` | `C(p⁵+p²/h)d^{-10}+e^{-cp}` | `(9C_TR p⁵ + 32sC_IL p²/h)ϑ + e^{-2p}` |
| `c` in `e^{-cp}` | absolute | `c = 3` in the transfers (R9) and `c = 2` after absorbing polynomial prefactors, for `d ≥ d_0`. The E6 exponent tends to `log 40 − 16(1−8/17) = −4.78` for `p ≤ d^{2/17}` (`auditC_params.py`). |
| `δ` | `C{r−1+p⁴/d+(p/d)^{1/3}}` | `≤ 3C_δ c_0^{17/6} p^{-5/2}` (each term `≤ c_0^{17/6}p^{-5/2}`) |
| `λ` | `≤Cδ` | `ϑ ≤ λ := a²S + E trA² + ϑ ≤ 2δ + ϑ ≤ 3δ` |
| `λ_1` | `Cp/d` | `C_{λ1}p/d` with `C_{λ1}` absolute (D6) |
| `E_λ` | `≤Cp` | `≤ C(c_0^{17/3}+o(1))` |
| `ε_s` | `Cp^{3/2}d^{-1/2}` | `C p^{3/2}d^{-1/2}` from `L̄−L ≤ C a² p/(r−1)` |
| `Γ` | `p⁴√(pδ/d)` | `≤ C c_0^{17/3} p^{-1}` |
| `Q_*` | `\|Q_*\|/a² ≤ C(p+p³δ)` | the row-free part of `Q_*/a²` is exactly `2a²Σ_N E[(p−1)P_i²+pP_iQ_i]` (`≤ C p`); the rest is `≤ C p³ δ` |

All "o(1)" in this range are explicit powers `d^{-α}` with `α > 0` once `p = ⌊c_0 d^{2/17}⌋`. The
critical (non-vanishing) scales `c_0^{17/3}/p` and `√κ_0/p` appear only through `Γ` and `h`, and
are handled in the endgame.

---

## 1. Setting and standing hypotheses

**Parameters.** `q = d−1`, `p = ⌊c_0 d^{2/17}⌋`, `Δ = 4/p`, `R² = 4q+Δ`, `a = 1/R`; `η_0 ∈ (0,1)`
solves `qη_0² = Δ(1−η_0)`; `τ_* = (1−η_0)/q`, `s = (1+qτ_*)/(1−τ_*) = (2−η_0)/(1−(1−η_0)/q)`,
`r = 1 + η_0/2`, `L̄ = d a² s²`. Shift `h = κ_0 p^{-4}` (any `h ∈ [d^{-10},1]` in B1).
`ϑ = d^{-10}`, `k_* = ⌈16p/log d⌉`.

**Graph and law.** `H` is a finite simple graph with maximum degree `≤ d`, with sources
`y^± ∈ [0,s]^V`, `c_ij(1+c_ij) = a²y_iy_j`, `Z_i = (1+Σ_{j∼i}c_ij)/y_i`, `D_i = y_iZ_i`, and
`P^± = diag Z(y^±) ± aA_σ`. The weight is `W(σ) = 1{P^±≻0}(det P^+ det P^−)^p`, `E` is the
expectation of the normalized law, `G^± = (P^±)^{-1}` and `h_i^± = G^±_ii/y_i^±` (zero sources by
the normalized convention of l.73–78).

**Fresh star at a root `v`.** `N = N_H(v)` (size `≤ d`), `K = H − v` with inherited precisions
(principal submatrices). `ν_K` is the own core law. `ξ = (σ_vi)_{i∈N}` and
`A = (a²/Z_v^+)G_K^+[N,N]`, `B = (a²/Z_v^−)G_K^−[N,N]`. `α = (1−ξᵀAξ)_+`, `β = (1−ξᵀBξ)_+`,
`Φ = α^pβ^p`, `F_H = E_{ν_K}𝖱Φ`. The actual law is `E[ψ] = E_{ν_K}𝖱[ψΦ]/F_H`.
`x_j = G^+_vj`, `z_j = G^-_vj`, `t_+ = 1/α = Z_v^+G^+_vv`, `t_− = 1/β = Z_v^-G^-_vv`.
`q_M(x) = xᵀMx`, and

`F(x) = (p−1)q_{A²}(x)α(x)^{p−2}β(x)^p + p q_{AB}(x)α(x)^{p−1}β(x)^{p−1}`,
`𝓡_v = (p−1)Σ_N x_j² − pΣ_N x_jz_j`, `𝓡 = E𝓡_v`. At every sign endpoint with `Φ > 0`,
`F = a²Φ𝓡_v` (checked numerically, `auditC_numeric.py` (a)). Hence `𝓡 = E_{ν_K}𝖱F/(a²F_H)` exactly.

**Hypothesis Cap(H, y).** The law exists, `F_H ≥ 40^{-p}` for every root, and `E h_i^± ≤ r` for
all `i, ±` (capped law). Imported consequences (nodes of other sections):
- (F2) moment caps: for `k ≤ p/2`, `‖h_i^±‖_{L^k} ≤ 1 + 2(r−1)`, so physical diagonals have
  `‖G_ii^±‖_{L^k} ≤ 1.01 s`;
- (C2) with `δ = C_δ{(r−1) + p⁴/d + (p/d)^{1/3}}`: `a²Σ_N E(G^±_vi)² ≤ δ`, `E tr(A²+B²) ≤ δ`, etc.;
- (GR1) `a²Σ_N E(G^±_vi)² ≤ δ_row = C_row δ/p`;
- (S1) `0 ≤ E(G^±_ii − X^±_ii)/y_i^± ≤ C_S1√h`, `X^± = (P^± + hI)^{-1}`;
- (C3a) `E[trA² 1{trA>1}] ≤ e^{-3p}`, `trA² 1{trA≤1} ≤ 2w`, `w = trA²/(1+trA)`.

**Hypothesis Contact(H, y, v).** Cap holds, `E h_v^+ = r`, and (F3) holds at `v`:
`p Cov(G^+_vv, G^+_ii) − E x_i² ≤ −r y_v^+ y_i^+ K_vi` for all `i ∈ N`, with `K = 𝓑(y^+)^{-1}`.
The deletion lemma gives `K_vi ≥ τ_vi` on edges.

---

## 2. Regime facts (all for `d ≥ d_0(c_0, κ_0)`)

R1. `p ≤ c_0 d^{2/17} ≤ d^{1/7}`, so `p⁷ ≤ d`. `p ≥ 10³ log d`. `4k_*+7 ≤ p` and
`8k_*+12 ≤ p/2` (`k_* ≈ 16p/log d`).
R2. `1/4 ≤ a²d ≤ 1/4 + 1/d`.
R3. `2 − η_0 ≤ s ≤ 2 + 2/(q−1)`, and `1/Z_v ≤ y_v ≤ s` (because `D_v ≥ 1`).
R4. `L̄ = dq(1−η_0)/(q−1+η_0)²` (exact; checked to 500 digits). `1 − rL̄ ≥ 0` and
`d(r−1)(1−rL̄) ≥ 1/p − 2η_0`. Numerically `p·d(r−1)(1−rL̄) = 1 − 1.5pη_0 + …`.
R5. `η_0 ≤ 2/√(pq)`, so `r−1 ∈ [1/(2√(pd)), 1.01/√(pd)]`.
R6. `δ ≤ 3C_δ c_0^{17/6}p^{-5/2}`: `(p/d)^{1/3} ≤ c_0^{17/6}p^{-5/2}` because `d ≥ (p/c_0)^{17/2}`;
`p⁴/d ≤ c_0^{17/2}p^{-9/2}`; `r−1 ≤ (pd)^{-1/2}`.
R7. Exponent inequalities used in D6–D10: `p⁹δ ≤ d`, `p^{12} ≤ d²`, `p⁵ ≤ d`,
`p⁸/(κ_0^{3/2}d) → 0`, `p^{10}δ/d → 0`.
R8. Interpolation floors: `ϑ^{-1/k} ≤ e` whenever `k ≥ 10 log d`; `d^{C/k} ≤ e` whenever
`k ≥ C log d`; `e^{-3p} d^{40} ≤ ϑ`.
R9. (E6) `p·40^p(C p)^{4k_*+4}d^{-k_*} ≤ e^{-3p}` for every fixed `C`, once `d ≥ d_0(C)`.

`auditC_params.py` checks R2–R7 and R9 numerically, from `d = 10^{20}` to `10^{1000}`.

---

## 3. Tools (nodes used across this range)

**T.IL (interpolation).** On a probability space, let `X, Y ≥ 0`, `k ≥ 2`, `m ≥ ϑ > 0`,
`EX ≤ m`, `‖X‖_2 ≤ B_X` and `‖Y‖_{2k} ≤ B_Y`. Then `E[XY] ≤ m·ϑ^{-1/k}·B_X^{1/k}·B_Y`.
Proof: Hölder, `E[XY] ≤ (EX)^{1−1/k}(E[XY^k])^{1/k}`, and `m^{1−1/k} ≤ mϑ^{-1/k}`.
Every "high-moment interpolation" in this range is this lemma with `k ∈ [10 log d, p/(C·deg Y)]`.
The joint expectation over uniform indices `I, J ∈ N` (padded to `d` slots) and the law is a
single probability space, so T.IL applies there too.

**T.DSTAR.** For a finite index set `S` and `m ≥ 1`:
`‖max_{u∈S}(1+G_uu)‖_{L^m} ≤ |S|^{1/m} max_u ‖1+G_uu‖_{L^m}`. With `|S| ≤ d²` and `m ≥ log d`
the factor is `≤ e²`.

**T.ROOT (root Schur identities; checked numerically).** At a sign endpoint with `Φ > 0`:
`G^+_vv = 1/(Z_v^+α)`, `G^+_vi = −a^{-1}(Aξ)_i/α`, `G^-_vi = a^{-1}(Bξ)_i/β`, and
`G[N,N] = G_K[N,N] + xxᵀ/G_vv`. Hence `A_ii/α = a²(G_vvG_ii − x_i²)` and the CR1 Frobenius bound
`a⁴G_vv²‖G[N,N]‖_F² ≤ 2t_+²trA² + 2(a²Σx_i²)²`. Also
`trM²/α² = a⁴(G^+_vv)²trY_+²` and `tr(M𝒩)/(αβ) = a⁴G^+_vvG^-_vv tr(Y_+Y_−)`. C5 (l.548) is reused:
`tr[X_z[N,N] − C_z[N,N]] = a²(X_z)_vv ξᵀC_z[N,N]²ξ ≤ (Z_v/z)(G_vv − (X_z)_vv)` (verified).

**T.MAT (matrix lemmas).** For PSD `M, X, Y, H, H_1, H_2` of the same size:
(i) `X ⪯ Y ⇒ tr(MX) ≤ tr(MY)`; (ii) `tr(M³) ≤ ‖M‖trM²`, `tr(M𝒩²) ≤ ‖𝒩‖tr(M𝒩)`,
`tr(M𝒩) ≤ trM·tr𝒩`; (iii) `(H_1+H_2)² ⪯ 2H_1² + 2H_2²`;
(iv) `I − (I+H)^{-1} − H + H² = H[H(I+H)^{-1}]H ⪰ 0`;
(v) `P ⪰ 0 ⇒ ‖(P+hI)^{-1}‖ ≤ 1/h` and `P^{-1} − (P+z)^{-1} = zP^{-1}(P+z)^{-1} ⪰ z(P+z)^{-2}`;
(vi) `(X²)[N,N] ⪰ (X[N,N])²`; (vii) `‖Δ‖ ≤ ‖Y+Δ‖` for `Y, Δ ⪰ 0`;
(viii) for `0 ⪯ M ⪯ A` and `0 ⪯ S ⪯ I`, `tr(A(I−S)) ≥ tr(M(I−S))`.

**T.ALPHA2 (parallelogram).** For `A ⪰ 0`, `α(x) = 1 − xᵀAx`, and `z, w` with `α(z±w) > 0`:
`α(z) − q_A(w) = (α(z+w)+α(z−w))/2 > 0` and
`α(z+w)α(z−w) = (α(z)−q_A(w))² − 4(zᵀAw)² ≤ α(z)² exp(−2q_A(w)/α(z))`.
For `φ = α_+^{m}β_+^{m'}`: `φ(z+w)φ(z−w) ≤ φ(z)² exp(−⟨w,H_A(z)w⟩)` with
`H_A(z) = 2mA/α(z) + 2m'B/β(z)` on `{φ(z) > 0}`, and `φ(z+w)φ(z−w) = 0` otherwise. (Verified on
20000 random cases; `auditC_numeric.py` (d).)

**T.BLmid** and **T.GIBP2**: §5.

**T.TRC (transfer of core-constant numerators; an instance of E4+E5+E6).** Assume Cap. Let
`w ≥ 0` be a core functional with a polynomial envelope (`w ≤ d^{C}·∏` of normalized core
diagonals) and `m_±` integers in `[0,3]`. Put `X = w t_+^{m_+}t_−^{m_−}` and `x_w = EX`. Then
`|E_{ν_K}𝖦[wα^{p−m_+}β^{p−m_−}]/F_H − x_w| ≤ C_TR(p⁴/d)(x_w + ϑ) + e^{-3p}`.
Proof outline: E4 with `k = k_*`. Every derivative hits only `α^{p−m_+}β^{p−m_−}`. At sign
endpoints `Φ^{-1}∂^{2𝐣}(Φt_+^{m_+}t_−^{m_−})` is `t_+^{m_+}t_−^{m_−}` times a polynomial in physical
inverse entries with coefficient mass `(Cp)^{n}a^{n}`, `n = 2(g+l)`. Summing `d^l` coordinate
choices gives `(Cp⁴/d)^g` times `E[X·Z_g]` with `deg Z_g = O(g)`. T.IL with `k_g = ⌊p/(C'g)⌋` gives
`≤ C^g(x_w+ϑ)·2^g`. The remainder is `≤ 40^p(Cp)^{4k_*+4}d^{-k_*-1}·E[core moments] ≤ e^{-3p}` by
R9. Instances: the four B4 numerators and `wΦ` in D6.

**T.MARK (pointwise marked derivative bounds for `F`).** At a support point, set
`R_± = a²Σ_N (G^±_vj)²`, `Kc_± = a⁴(G^±_vv)²‖G^±[N,N]‖_F²` and
`D = 1 + max_{u∈N∪{v},±}G^±_uu`. Then:
- (grade 1) `Σ_{i∈N}|∂_i⁴F|/(a²Φ) ≤ C_M D^{C_M}{p⁵(R_+ + √(R_+R_−)) + p⁴(R_+ + Kc_+ + √((R_++Kc_+)(R_−+Kc_−)))}`;
- (grade 2) `Σ_i|∂_i⁶F|/(a²Φ) + Σ_{i≠k}|∂_i⁴∂_k⁴F|/(a²Φ) ≤ C_M D^{C_M}(p⁹/d)(R_+ + Kc_+ + √((R_++Kc_+)(R_−+Kc_−)))`.

These follow from CR2 (§4.1): every monomial of `Φ^{-1}D^w(Φ𝓡_v)` carries exactly two marks. The
first term `Φ^{(4)}𝓡_v/Φ` keeps row marks only, with coefficient `≤ C p⁵`. All other terms have
coefficient `≤ C p⁴`. Sum over `i, j` with Cauchy–Schwarz:
`Σ_{i,j}a⁴x_j² = a²|N|·R_+ ≤ R_+/3.99` and `Σ_{i,j}a⁴c_ij² = Kc_+`. Unmarked factors are
`≤ D^{C}`. (Formalization hint: for one coordinate, `F(x+te_i)` is a polynomial in `t`;
coefficient majorants of `α(t)^m = (α − 2(Ax)_i t − A_ii t²)^m` give the needed bounds without
symbolic "derivative words".)

---

## 4. Section 1.4

### 4.1 CR2: derivative rules (l.1102–1127). **OK.**

With `D_i = a^{-1}∂_i` (entry `(v,i)` perturbed), (E3) gives
`D_ix_j = −x_ix_j − c_ij`, `D_ic_kj = −2x_ic_kj − x_kc_ij − G_vvG_kix_j`,
`D_iz_j = z_iz_j + d_ij`, `D_id_kj = 2z_id_kj + z_kd_ij + G^-_vvG^-_kiz_j`, and
`D_i log Φ = 2p(x_i − z_i)`. Checked by finite differences in 50-digit arithmetic
(`auditC_numeric.py` (b)). **Mark preservation:** each marked factor's derivative is a sum of terms
with exactly one marked factor of the same branch and the same free index `j`. Every new first
index is an active coordinate, and unmarked factors involve only active indices and `v`. So every
monomial of `Φ^{-1}D^w(Φ·((p−1)x_j² − px_jz_j))` has exactly two marks: two plus marks, or one of
each branch. Correct.

### 4.2 CR1 and CR3 (l.1078–1190)

**Restatement (CR3, general; CR1 is a corollary).** Assume Cap and fix `v`. Let `λ_r, ρ_r, λ_c, δ_c`
satisfy `ϑ ≤ λ_r ≤ ρ_r ≤ δ_c ≤ 1` and `λ_r ≤ λ_c ≤ δ_c`, together with the marked envelopes
- `S_+/d ≤ λ_r` and `S_−/d ≤ ρ_r` (with `S_± = Σ_N E(G^±_vj)²`);
- `d^{-2}E[(G^+_vv)²‖G^+[N,N]‖_F²] ≤ λ_c` and `d^{-2}E[(G^-_vv)²‖G^-[N,N]‖_F²] ≤ δ_c`.

Then
`|𝓡 − E_{ν_K}𝖦F/(a²F_H)| ≤ C_CR{p⁵√(λ_rρ_r) + p⁴√(λ_cδ_c) + p^{13}/d²} + e^{-3p}`.

**CR1** is the case `λ_r = λ_c = C_ME λ` and `ρ_r = δ_c = C_ME δ`, where **MARKENV** (Cap) says:
if `a²S_+ + E trA² ≤ λ` and `ϑ ≤ λ`, then `S_+/d ≤ 4λ` and
`d^{-2}E[(G^+_vv)²‖G^+[N,N]‖_F²] ≤ 32C_IL(λ + 2ϑ) ≤ 96C_IL λ`. This uses T.ROOT's Frobenius bound,
`a⁴d² ≥ 1/16`, and T.IL for `t_+²·trA²` and `(a²S_v)·(a²S_v)`. The same holds for the minus
branch with C2's `δ`. The contact hypothesis in the paper's CR1 is not used.

**Proof check.**
1. E4 applied to `F` (`k = k_*`): `𝖦F − 𝖱F = Σ_{1≤|𝐣|_g≤k_*}c_𝐣𝖱∂^{2𝐣}F + ℰ`. Divide by
   `a²F_H` and average over `ν_K`. The grade-0 term is exactly `𝓡`. **OK.**
2. Grade 1 (`∂_i⁴`, `c_2 = 1/12`) and grade 2 (`∂_i⁶` with `c_3`, `∂_i⁴∂_k⁴` with `c_2²`): T.MARK,
   then the expectation. Mixed terms:
   `E[D^C√((R_++Kc_+)(R_−+Kc_−))] ≤ √(E[D^{2C}(R_++Kc_+)]·E[R_−+Kc_−])`, and T.IL turns this into
   `≤ C√((λ_r+λ_c)(ρ_r+δ_c))`. Here `E R_+ = a²S_+ ≤ (a²d)λ_r` and `E Kc_+ ≤ a⁴d²λ_c ≤ λ_c/15.9`.
   Envelope ordering gives grade 1 `≤ C(p⁵√(λ_rρ_r) + p⁴√(λ_cδ_c))` and grade 2
   `≤ C(p⁹/d)√(λ_cδ_c) ≤ Cp⁴√(λ_cδ_c)` (R7). **OK.** The paper's remark that coordinates may
   repeat (`I = J`) is covered: `Kc_±` includes the diagonal terms `j = k`.
3. Grades `3 ≤ g ≤ k_*`: unmarked bound `p(Cp)^{4g}d^{1−g}` (E5; one free row index, so
   `𝓡_v = O(pd)` pointwise). This sums to `≤ Cp^{13}/d²`. **OK.**
4. Remainder: `≤ e^{-3p}` by E6/R9 (division by `F_H ≥ 40^{-p}`; derivatives up to
   `4k_*+4 < p−3` vanish where `Φ = 0`). **OK.**
5. CR3's improvement (l.1180–1190):
   `∂_i⁴(Φ𝓡_v) = Φ^{(4)}𝓡_v + Σ_{k≥1}binom(4,k)Φ^{(4−k)}∂_i^k𝓡_v`. The first term has coefficient
   `≤ Cp⁴·p` and row marks only. The others have coefficient `≤ Cp^{4−k}·p ≤ Cp⁴`, with arbitrary
   marks. Each product of marks is dominated through the orderings: `λ_r ≤ λ_c`, `ρ_r ≤ δ_c`,
   `λ_c ≤ δ_c`, and `λ_r ≤ ρ_r` (two-plus row terms). **OK.**

**Constants.** `C_CR` depends on `C_E4, C_M, C_mom, C_IL` only. It is absolute.

### 4.3 B1: multiplicative shifted trace comparison (l.1192–1331)

**Restatement.** Assume Cap and fix `v` and `h ∈ [d^{-10}, 1]`. Put
`Y_± = ((P^±)_{KK} + hI)^{-1}[N,N]` (core-constant) and
`Q = a²E{(p−1)(G^+_vv)²trY_+² + pG^+_vvG^-_vv tr(Y_+Y_−)} ≥ 0`. Let `E_row ≥ 0` satisfy the
one-sided comparison `𝓡 ≥ E_{ν_K}𝖦F/(a²F_H) − E_row`. Then

`𝓡 ≥ (1 − η_BL)Q − E_row − ε_BL`,
`η_BL = 8C_TR p⁴/d + 32 s C_IL p/(dh)`, `ε_BL = (9C_TR p⁵ + 32 s C_IL p²/h)ϑ + e^{-2p}`
(assuming `C_IL ≥ 1`; the assembly actually gives `4C_TR` and `4.01sC_IL`, so these are safe upper
choices).

Consequences used later: `𝓡 ≥ −E_row − ε_BL`; and if `𝓡 + E_row ≤ Cp` and `η_BL ≤ 1/2`, then
`Q ≤ 2(Cp + ε_BL)`.

**Proof check (core fixed).** `M = a²Y_+/Z_v^+` and `𝒩 = a²Y_−/Z_v^−` satisfy `0 ⪯ M ⪯ A`
(since `(P_K+h)^{-1} ⪯ P_K^{-1}`) and `0 ⪯ 𝒩 ⪯ B`, with `‖M‖, ‖𝒩‖ ≤ s a²/h` (R3, T.MAT(v)).
Let `H = 2(p−1)M/α + 2p𝒩/β` on `{α, β > 0}` and `g = α_+^{p−1}β_+^p`.

- **(BL step)** BLmid with `ρ = g e^{−|x|²/2}` and `K = I + H`. The hypothesis is T.ALPHA2
  (exponent `H_A ⪰ H`). Conclusion: `⟨θ,Σ_νθ⟩ ≤ E_ν⟨θ,(I+H)^{-1}θ⟩` for all `θ`. In particular
  `Σ_ν ⪯ I`, and summing over a factorization of `M` gives `tr(MΣ_ν) ≤ E_ν tr(M(I+H)^{-1})`.
  **OK (§5).**
- **(Gaussian IBP)** `2𝖦F = 𝖦[(trA − q_A)g]` (T.GIBP2; checked by quadrature to 7 digits).
  **OK.**
- **(B2)** `2𝖦F = 𝖦g·tr(A(I−Σ_ν)) ≥ 𝖦g·tr(M(I−Σ_ν)) ≥ 𝖦[g·tr(M(H−H²))]` by T.MAT(viii), BL and
  T.MAT(iv). Expanding `g·tr(MH)/2` and `g·tr(MH²)/2` gives exactly
  `𝖦F ≥ 𝖦[Φ{(p−1)trM²/α² + p tr(M𝒩)/(αβ) − tr(MH²)/(2α)}]`. **OK.**
- **(B3)** `X_1 = trM²/α² ≤ μ_A²t_+²` and `X_2 = tr(M𝒩)/(αβ) ≤ μ_Aμ_Bt_+t_−`
  (T.MAT(ii), `trM ≤ trA`). These are polynomial envelopes with `L^{cp}` bases (`μ_A ≤ U`, Schur
  order, F2). T.IL gives `E[(X_1+X_2)Z] ≤ C_IL(x+ϑ)` for fixed-degree diagonal products `Z`.
  **OK (fix G5 for grade-dependent degree).**
- **(B4)** T.TRC for the four numerators `trM²α^{p−2}β^p`, `tr(M𝒩)α^{p−1}β^{p−1}`,
  `trM²α^{p−3}β^p` and `tr(M𝒩)α^{p−1}β^{p−2}` (`X = X_1, X_2, X_1t_+, X_2t_−`). This gives
  `|⟨Φ((p−1)X_1+pX_2)⟩_G − E((p−1)X_1+pX_2)| ≤ 2C_TR(p⁵/d)(x+ϑ) + 2pe^{-3p}` and
  `⟨Φ(X_1t_++X_2t_−)⟩_G ≤ (C_IL + C_TR p⁴/d)(x+ϑ) + 2e^{-3p}`. **OK.**
- **(B5)** `α^{-1}tr(MH²) ≤ 8p²(‖M‖X_1t_+ + ‖𝒩‖X_2t_−) ≤ 8p²(sa²/h)(X_1t_+ + X_2t_−)` by
  T.MAT(ii)–(iii). (Numerically checked.) **OK.**
- **(Assembly)** Since `(p−1)X_1 + pX_2 = a²·[integrand of Q]` at sign endpoints (T.ROOT):
  `E_{ν_K}𝖦F/(a²F_H) ≥ Q − a^{-2}{2C_TR(p⁵/d) + 8p²(sa²/h)C_IL}(x+ϑ) − a^{-2}(2p + 8p²sa²/h)e^{-3p}`.
  Use `x ≤ a²Q/(p−1)`, `p/(p−1) ≤ 2`, `a^{-2} ≤ 4d`, and `a²d ≤ 1/4+1/d`. This gives the
  multiplicative loss `(4C_TR p⁴/d + 4.01sC_IL p/(dh))Q`. The exponential term is
  `≤ (8dp + 8p²s/h)e^{-3p} ≤ e^{-2p}` (R8). **OK.**

The numbers `η_BL` and `ε_BL` above come out of this computation. With
`h = κ_0p^{-4}`, `η_BL ≤ C(p⁴/d + p⁵/(κ_0d)) → 0` and `ε_BL = o(p^{-1})`.

---

## 5. Brascamp–Lieb: analysis and replacement

### 5.1 Exactly what is used

The measure and function are given in §0.3. Only the following inequality is used, for one fixed
core:
`tr(M Σ_ν) ≤ E_ν tr(M(I + H(x))^{-1})`, with `H(x) = 2(p−1)M/α(x) + 2p𝒩/β(x)`, and `Σ_ν ⪯ I`.
The paper writes `Σ_ν ⪯ E_ν(I+∇²V)^{-1} ⪯ E_ν(I+H)^{-1}`, i.e. BL for linear functions in
dimension `n = |N(v)| ≤ d`, with potential `U = |x|²/2 − (p−1)log(1−q_A) − p log(1−q_B)` (convex,
`+∞` off `Ω`).

### 5.2 Can easier facts replace it? No; quantitative reasons

**(a) Constant modulus (Prékopa only).** Since `α, β ≤ 1`, `∇²V ⪰ H_0 = 2(p−1)M + 2p𝒩`, and (a)
gives `Σ_ν ⪯ (I+H_0)^{-1}`. Then B2 holds with `trM²/α` and `tr(M𝒩)/β` in place of `trM²/α²` and
`tr(M𝒩)/(αβ)`. At sign endpoints this replaces the weights `(G^+_vv)²` and `G^+_vvG^-_vv` in `Q`
by `G^+_vv/Z_v^+` and `G^+_vv/Z_v^−`, i.e. it multiplies the integrand by `α = 1/t_+` (resp. `β`).
At contact and saturation `E t_+ = D_v^+ r = 2 + o(1)` (D8), so the main term is halved. The
endgame needs this main term to cancel *exactly* against the row-free part of `Q_*`, which is
`2a²Σ_N E[(p−1)(G^+_vvG^+_ii)² + pG^+_vvG^+_iiG^-_vvG^-_ii]` (RC5, l.1935–1940; the D10 trace
contains the matching diagonal). So the loss is `≍ 1·(main term)`, while the margin is
`≍ p^{-1}·(main term)`: **fatal.**
(Toy 2-D quadrature with `α ≈ 1` shows the two bounds coincide, as they must. The difference is
the factor `E[1/α]`, which equals `≈ 2` exactly in the application regime.)

**(c) Exact identity `I − Σ = E∇²V − E∇V∇Vᵀ`.** This gives
`tr(M(I−Σ)) = E tr(M∇²V) − E∇VᵀM∇V`, and `E tr(M∇²V) ≥ E tr(MH) + 4(p−1)E q_{AMA}/α² + 4pE q_{BMB}/β²`.
To use this as a lower bound one must bound `E∇VᵀM∇V` from above. Its `B`-part
`4p²E_ν q_{BMB}/β²` is matched by only `4pE_ν q_{BMB}/β²` from `E tr(M∇²V)`. The cross term
`8p(p−1)E xᵀAMBx/(αβ)` has no sign, so it cannot be relied on to cancel the rest in general. At
signs, `q_{BMB}/β² = a²zᵀMz ≤ a²(sa²/h)|z|²`, so in `𝓡` units the uncompensated error is
`≈ 4p²(s/h)a²S_− ≤ 4sp²C_rowδ/(ph) = O(c_0^{17/6}p^{5/2}/κ_0)`. The endgame tolerates
`O(p^{-1})`. Replacing `zᵀMz` by quadratic domination (`E_ν q_{BMB} ≤ tr(BMB)` under the even
log-concave weight) gives `≈ p²‖M‖E trB²/a² ≍ p⁶δ/κ_0`. **Fails** by a polynomial factor either
way. Also, (c)-type Cauchy–Schwarz gives *lower* bounds `Σ ⪰ (I + E∇²V)^{-1}` (used in C4), but B1
needs an *upper* bound on `Σ`.

**(b) Gaussian IBP** and **(d) E4** are needed *in addition* (for `2𝖦F = N_G` and the transfers),
not as substitutes.

**Conclusion:** B1 needs BL with a variable modulus, but only in the form BLmid below, which is a
short consequence of midpoint PL.

### 5.3 BLmid: statement and complete proof from midpoint Prékopa–Leindler

**Lemma (BLmid).** Let `n ≥ 0`. Let `ρ : ℝⁿ → [0,∞)` be measurable and even, with
`0 < ∫ρ < ∞` and `ρ(0) < ∞`. Let `K : ℝⁿ → Sym(n)` be measurable with `K(z) ⪰ κI` (`κ > 0`) for
all `z`, and suppose
`ρ(z+w)ρ(z−w) ≤ ρ(z)² exp(−⟨w, K(z)w⟩)` for all `z, w ∈ ℝⁿ`. (★)
Then for every `θ ∈ ℝⁿ`, `∫⟨θ,x⟩²ρ(x)dx ≤ ∫⟨θ,K(x)^{-1}θ⟩ρ(x)dx`.

*Proof.* Putting `z = 0` in (★) and using evenness gives `ρ(w) ≤ ρ(0)e^{-κ|w|²/2}`. So every
`ρe^{c|x|}` is integrable. Fix `ε > 0` and set `f(x) = ρ(x)e^{ε⟨θ,x⟩}`, `g(y) = ρ(y)e^{−ε⟨θ,y⟩}`,
`h(z) = ρ(z)exp((ε²/2)⟨θ,K(z)^{-1}θ⟩)` (measurable). For `x = z+w`, `y = z−w`:
`f(x)g(y) = ρ(z+w)ρ(z−w)e^{2ε⟨θ,w⟩} ≤ ρ(z)²exp(−⟨w,K w⟩ + 2ε⟨θ,w⟩) ≤ ρ(z)²exp(ε²⟨θ,K^{-1}θ⟩) = h(z)²`,
using `2ε⟨θ,w⟩ ≤ ⟨w,Kw⟩ + ε²⟨θ,K^{-1}θ⟩` (Cauchy–Schwarz in the `K` inner product). Midpoint PL
gives `∫h ≥ √(∫f ∫g)`. By evenness `∫f = ∫g = ∫cosh(ε⟨θ,x⟩)ρ`. With `c(x) = ⟨θ,K(x)^{-1}θ⟩ ∈ [0, |θ|²/κ]`
and the bounds `cosh u ≥ 1 + u²/2` and `e^u ≤ 1 + u + u²e^u/2` (`u ≥ 0`):
`∫(1 + ε²⟨θ,x⟩²/2)ρ ≤ ∫(1 + ε²c/2)ρ + (ε⁴|θ|⁴/(8κ²))e^{ε²|θ|²/(2κ)}∫ρ`.
Subtract `∫ρ`, divide by `ε²/2`, and let `ε → 0`. ∎

**Corollaries.**
- **(a)** `ρ = f e^{−xᵀMx/2}` with `f` even and log-concave (midpoint form
  `f(z+w)f(z−w) ≤ f(z)²`) satisfies (★) with `K ≡ M`. Hence `Cov ⪯ M^{-1}`. This gives N_G ≥ 0
  (C1, with `M = I`), WT3, and the whitening `N_G ≥ 𝖦g·2(p−1)trA²/(1+2(p−1)‖A‖) ≥ f_G w`
  (C2/D6: `K ≡ I + 2(p−1)A`, valid since `1/α ≥ 1`).
- **(B1)** `ρ = α_+^{p−1}β_+^p e^{−|x|²/2}` satisfies (★) with `K = I + H` by T.ALPHA2 and
  `M ⪯ A`, `𝒩 ⪯ B`, `κ = 1`.

Lean shape: work on `ι → ℝ` with `volume`; express `𝖦`-expectations through the density
`(2π)^{-n/2}e^{−|x|²/2}`; `K x := 1 + H x` (with `H := 0` off the support). Measurability: `H` is
piecewise rational in `x`. Integrability: `ρ ≤ e^{−|x|²/2}`. The `ε → 0` step is
`le_of_forall_pos_le_add`. Estimated size: about 300 lines given PL. **This single lemma covers
every covariance bound in the paper's upper bound.**

### 5.4 Midpoint PL itself

Needed form: for measurable `f, g, h : ℝⁿ → [0,∞]` with `h((x+y)/2)² ≥ f(x)g(y)` everywhere,
`(∫⁻h)² ≥ ∫⁻f·∫⁻g`. Standard route: (1) 1-D from `|K+L| ≥ |K|+|L|` for compact `K, L ⊂ ℝ` and
inner regularity applied to level sets, after rescaling `f ↦ cf`, `g ↦ g/c` to equalize
essential suprema (or use the AM–GM version `∫h ≥ (∫f+∫g)/2` under `sup f = sup g`); (2) induction
on `n` through sections and Tonelli (`lintegral_prod`). It is a well-understood formalization of
roughly 1000 lines. It is not in Mathlib.

### 5.5 The paper's PDE sketch (l.1231–1242)

Formally the computation is correct: with `Lw = f − Ef` and `L = −Δ + ∇U·∇`,
`Var f = E∇f·∇w ≤ √(E∇fᵀ(∇²U)^{-1}∇f)·√(E∇wᵀ∇²U∇w)` and
`E(Lw)² = E‖∇²w‖² + E∇wᵀ∇²U∇w`. Rigour, however, needs: existence of `w` (Lax–Milgram in
`H¹(ν)`, which needs a Poincaré inequality for `ν`, itself a BL-type statement); `H²` regularity
up to `∂Ω`, where `∇²U` blows up; Neumann boundary terms; or a smoothing `U_k → U` by smooth
uniformly convex potentials with convergence of `Σ_{ν_k}` and `E(∇²U_k)^{-1}`. None of this
exists in Mathlib, and it is weeks of work. **Do not formalize; use §5.3.** The paper's "smooth
convex approximation" is not needed under §5.3, because the parallelogram inequality is exact for
the clipped powers.

### 5.6 Log-concavity claims in and near this range

- `α_+^{p−1}β_+^p` is even and log-concave (`α` concave and positive on its support). **OK.**
- `∇²V ⪰ H` on `Ω` (`∇²(−log α) = 2A/α + 4Axxᵀ A/α² ⪰ 2A/α ⪰ 2M/α`). **OK** (not needed under
  §5.3).
- Whitening: `−log(1−q_A) − q_A` is convex on `{q_A<1}` (Hessian `2A(1/α−1) + 4Axxᵀ A/α² ⪰ 0`).
  **OK.** Under §5.3 this is replaced by (★) with `K = I + 2(p−1)A`.
- WT3 (l.969–979, outside the range): `ξ ↦ log det P(ξ)` is concave for `P` affine in `ξ` with
  `P ≻ 0`, and `log det P − log det(P+hI) = −∫_0^h tr(P+tI)^{-1}dt` is concave. **OK.** In midpoint
  form, `det((P+P')/2)² ≥ det P·det P'` (Ky Fan: reduce to AM–GM on the eigenvalues of
  `P^{-1/2}P'P^{-1/2}`). This is a separate small node.

---

## 6. Section 1.5, first part (D1–D10)

All statements assume **Contact(H, y, v)** with the global parameters, `d ≥ d_0(c_0,κ_0)`.
Notation: `ℓ_i = a²y_v^+y_i^+`, `L = Σ_Nℓ_i ≤ L̄`, `C_+ = Σ_N(c^+_vi)²`, `D_+ = 1 + L − C_+`,
`δ_i = r − E h_i^+ ≥ 0`, `J = Σ_Nℓ_iK_vi`, `S = Σ_N E x_i²`, `T = Σ_N E x_iz_i`, `𝓡 = (p−1)S − pT`.

**D1/D2 (parameters).** Restated in R2–R5. The closed form of `L̄` is exact. `d(r−1)(1−rL̄)` equals
`p^{-1} − (3/2)η_0 + O(η_0/p + 1/(pd))`. **OK** (see G9 for the sign of the `O(η_0)` term).

**Source facts (l.1367).** `L ≤ L̄` (since `|N| ≤ d` and `y ≤ s`). `J ≥ C_+`, because
`ℓ_iK_vi ≥ c(1+c)·c/(1+c) = c²`. `C_+/a² ≤ a²ds⁴ ≤ s⁴(1/4 + 1/d)`. **OK.**

**LOOP (l.1394–1400).** `D_+r = 1 + a²Σ_N E[G^+_vvG^+_ii − (2p−1)x_i² + 2px_iz_i] + Q_* + e_1`, with
`|e_1| ≤ C_E1 p⁵a⁶d·max E D⁶ ≤ C p⁵/d²`. Derivation: the root equation
`Z_vEG_vv + aΣ_iE[ξ_iG_vi] = 1`, E1 for each `i ∈ N`, and
`Φ^{-1}D_i(Φx_i) = (2p−1)x_i² − 2px_iz_i − P_i`. **KID** (`Φ^{-1}D_i³(Φx_i) = K_i`) is verified
symbolically from CR2 (`auditC_symbolic.py`) and numerically by a third finite difference of
`det(P^+)^p det(P^−)^p G^+_vi` (agreement to 12 digits). **OK.**

**(D3).** Substituting (F3) (summed over `N`, divided by `p`) and `E G_vvG_ii = y_vr·y_i(r−δ_i) + Cov`
into LOOP gives exactly
`(r−1)(1−rL) + rΣℓ_iδ_i + (1−p^{-1})a²S + (r/p)J + 2a²𝓡 ≤ Q_* + rC_+ + e_1`.
Checked symbolically (residual 0). **OK.**

**QSTAR (l.1414–1422).** The row-free part of `K_i` is `6[(p−1)P_i² + pP_iQ_i]`. Every other
monomial has `≥ 2` row factors and `p`-degree `≤ 3` (both checked symbolically). Using C2
(`d^{-1}Σ_N E x_i² ≤ 4δ`, same for `z`), T.IL and `a²d ≤ 1/4 + 1/d`:
`|Q_*|/a² ≤ C_Q(p + p³δ) ≤ 2C_Q p` (R6: `p²δ ≤ 3C_δ p^{-1/2}`). **OK.**

**(D4).** On the left of (D3) every term except `2a²𝓡` is `≥ 0` (R4, `δ_i ≥ 0`, `J ≥ 0`). Hence
`𝓡 ≤ (Q_* + rC_+ + e_1)/(2a²) ≤ C_4(p + p⁵/d)`. If `𝓡 ≥ −b` (`b ≥ 0`), then term by term:
`S ≤ 2a^{-2}(Q_* + rC_+ + e_1 + 2a²b) ≤ C_4(1+p+p⁵/d+b)`, the same bound for
`a^{-2}Σℓ_iδ_i`, and `L̄ − L ≤ C_4a²(1+p+p⁵/d+b)/(r−1)`. **OK.**

**(D5).** `h = κ_0p^{-4}` and `δ ≤ 3C_δc_0^{17/6}p^{-5/2}` (R6). `λ := a²S + E trA² + ϑ` satisfies
`ϑ ≤ λ ≤ 2δ + ϑ ≤ 3δ` by C2. **OK.**

**(D6) λ-bootstrap.**
1. CR1 with envelope `λ` (MARKENV) gives `E_λ = C_CR'{p⁵√(λδ) + p^{13}/d²} + e^{-3p}`.
2. `N_G = 2𝖦F ≥ 0` (BLmid(a) and T.GIBP2) gives `𝓡 ≥ −E_λ`.
3. D4 with `b = E_λ` gives `a²S ≤ C(p+E_λ)/d`, and
   `E_{ν_K}N_G/F_H = 2a²·E_{ν_K}𝖦F/(a²F_H) ≤ 2a²(𝓡 + E_λ) ≤ C(p+E_λ)/d`.
4. Whitening `N_G ≥ f_Gw` (BLmid(a)) and T.TRC for `wΦ` (`m_± = 0`) give
   `x = Ew ≤ C(p+E_λ)/d + C_TR(p⁴/d)(x+ϑ) + e^{-3p}`. Absorb, then use (C3a):
   `E trA² ≤ 2x + e^{-3p}`.
5. Altogether `λ ≤ Cp/d + Cp⁵√(λδ)/d + Cp^{13}/d³ + Cϑ`. Young gives
   `λ ≤ C{p/d + p^{10}δ/d² + p^{13}/d³ + ϑ} ≤ C_{λ1}p/d =: λ_1`, using `p⁹δ ≤ d`,
   `p^{12} ≤ d²` and `ϑ ≤ p/d` (R7).

There is no circularity: CR1 holds for any envelope `λ ≥` the mass, and it is applied to the
mass itself. `E_λ ≤ C(c_0^{17/3} + o(1))` (G7). **OK.**

**(D7)/(D8).** D4 with `b = E_λ ≤ C` gives `S ≤ C_7p`, `Σℓ_iδ_i ≤ C_7pa²`, and
`L̄ − L ≤ C_7a²p/(r−1) ≤ C_7'p^{3/2}d^{-1/2} =: ε_s` (R5). Next,
`L̄ − L = a²[ds² − y_vΣ_Ny_i] ≥ a²·max{ds(s−y_v), s(ds−Σ_Ny_i)}`. Hence `s − y_v ≤ ε_s/(a²ds)` and
`(d−|N|)/d + d^{-1}Σ_N(s−y_i) ≤ ε_s/(a²ds)`. With `|s−2| ≤ η_0 + 2/(q−1)` this gives (D8) with
`C = 2.1`. **OK.**

**(D9a).** CR3 with `λ_r = 4(S+1)/d` (valid: `S/d ≤ λ_r`), `ρ_r = 4δ_row`, `λ_c = C_ME λ_1` and
`δ_c = C_ME δ`. The orderings follow from `S ≤ C_7p` and `p²/d ≤ δ` (R7), for `d ≥ d_0`, after
enlarging `C_ME` if needed so that `C_ME C_{λ1} ≥ 4(C_7+1)`. Result:
`E_row = C_9{Γ√(S+1) + p^{13}/d² } + e^{-3p}` with `Γ = p⁴√(pδ/d) ≤ C c_0^{17/3}p^{-1}`. In
particular `E_row ≤ Cp`. **OK.** GR1 is load-bearing (G8): with `ρ_r = Cδ` the first term
becomes `≍ c_0^{17/3}p^{-1/2}`, because `S ≈ 4` by D15.

**(D9b).** B1 with this `E_row`: `(1−η_BL)Q ≤ 𝓡 + E_row + ε_BL ≤ Cp`, so `Q ≤ C_9'p`. Since both
summands of `Q` are `≥ 0` and `a²(p−1) ≥ (p−1)/(4d)`:
`E[Ω_+d^{-1}trY_+²] + E[Ω_−d^{-1}tr(Y_+Y_−)] ≤ C`, with `Ω_+ = (G^+_vv/2)²` and
`Ω_− = G^+_vvG^-_vv/4`. By D8, `G^+_vv ≥ 1/Z_v^+ ≥ y_v/(1+L̄) ≥ 0.99`. **OK.**

**(D10).** With `Δ_± = X_±[N,N] − Y_± ⪰ 0` (rank one, by C5),
`trΔ_± ≤ h^{-1}Z_v^±(G^±_vv − X^±_vv)`. S1 and T.IL (multiplier `Ω·Z_v`, normalized) give
`E[Ω trΔ_±] ≤ Ch^{-1/2}`. Then T.MAT(v),(vii):
`trX_+[N,N]² ≤ trY_+² + 3h^{-1}trΔ_+` and
`tr(X_+[N,N]X_−[N,N]) ≤ tr(Y_+Y_−) + h^{-1}(2trΔ_+ + trΔ_−)`. So
`Q_full ≤ Q + Cp/(dh^{3/2})`, where `Q_full` is `Q` with `Y_±` replaced by `X_±[N,N]`. B1 with
`η_BLQ ≤ C(p⁵/d + p²/(dh))` gives
`𝓡 ≥ Q_full − C{E_row + p⁵/d + p²/(dh) + p/(dh^{3/2})} − ε_BL`. **OK.** (In the endgame unit
`p^{-1}`, `p/(dh^{3/2}) = O(κ_0^{-3/2}p^{-3/2})` and `p²/(dh) = O(p^{-5/2}/κ_0)`.)

---

## 7. Proposed DAG

Difficulty: E = easy (< 150 lines), M = medium, H = hard, X = external long pole. "Ext" lists
dependencies outside this range (labels of the paper).

| id | statement (constants explicit) | deps | ext | diff |
|---|---|---|---|---|
| T.PL | midpoint Prékopa–Leindler on `ι→ℝ`, lintegral form (§5.4) | – | Mathlib measure theory | X |
| T.BLmid | §5.3 lemma (★) ⇒ `∫⟨θ,x⟩²ρ ≤ ∫⟨θ,K^{-1}θ⟩ρ`; Gaussian corollary on `gaussPi` | T.PL | – | M |
| T.ALPHA2 | parallelogram inequality and its `α_+^mβ_+^{m'}` form (§3) | – | – | E |
| T.COV | (i) `N_G ≥ 0`; (ii) `N_G ≥ 𝖦g·2(p−1)trA²/(1+2(p−1)‖A‖) ≥ f_Gw`; (iii) B2 (`2𝖦F ≥ 𝖦[g·tr(M(H−H²))]`) for `p ≥ 3`, `M ⪯ A`, `𝒩 ⪯ B` | T.BLmid, T.ALPHA2, T.GIBP2, T.MAT | – | M |
| T.GIBP2 | `2𝖦F = 𝖦[(trA−q_A)α_+^{p−1}β_+^p]` (`p ≥ 3`) | n-dim Stein | `Gauss/IBP` | M |
| T.MAT | matrix lemmas (i)–(viii) of §3 | – | `Common/` | E–M |
| T.ROOT | root Schur identities, Frobenius bound, `X_1, X_2` physical forms | T.MAT | F1, C5, `Common/Schur` | M |
| T.IL | interpolation lemma; T.DSTAR max lemma | – | – | E |
| T.TRC | core-constant numerator transfer, error `C_TR(p⁴/d)(x_w+ϑ) + e^{-3p}` | T.IL | E4, E5, E6, F2 | H |
| T.MARK | pointwise marked bounds for `∂_i⁴F`, `∂_i⁶F`, `∂_i⁴∂_k⁴F` (§3) | CR2 | E3 | H |
| CR2 | derivative rules for `x_j, c_kj, z_j, d_kj` and `log Φ` | – | E3 | E |
| MARKENV | `a²S_+ + E trA² ≤ λ`, `λ ≥ ϑ` ⇒ marked envelopes `≤ Cλ` | T.ROOT, T.IL | F2 | E |
| CR3 | §4.2 restatement, `C_CR` absolute | T.MARK, T.IL, MARKENV | E4, E5, E6, F2 | H |
| CR1 | corollary of CR3 + MARKENV + C2 | CR3, MARKENV | C2 | E |
| B5 | `α^{-1}tr(MH²) ≤ 8p²(sa²/h)(X_1t_+ + X_2t_−)` | T.MAT | – | E |
| B1 | §4.3 restatement with `η_BL, ε_BL` explicit | T.COV, B5, T.TRC, T.IL, T.ROOT | F2 | M |
| PD | R1–R9 | – | `Tight/Params` | M |
| KID | `Φ^{-1}D_i³(Φx_i) = K_i` | CR2 | – | M |
| LOOP | corrected loop with `\|e_1\| ≤ Cp⁵/d²` | KID | E1, F1 | M |
| D3 | exact scalar inequality | LOOP | F3, deletion lemma (`K_vi ≥ τ_vi`) | E |
| QSTAR | `\|Q_*\|/a² ≤ C_Q(p+p³δ)`, row-free part exact | KID, T.IL | C2, F2 | E–M |
| D4 | bootstrap: `𝓡 ≤ C(p+p⁵/d)`; `𝓡 ≥ −b ⇒ S, Σℓδ, L̄−L` bounds | D3, QSTAR, PD | – | E |
| D6 | `λ ≤ λ_1 = C_{λ1}p/d` | CR1, D4, T.COV, T.GIBP2, T.TRC, PD | C2, C3a | M |
| D78 | `S ≤ Cp`, `Σℓδ ≤ Cpa²`, `L̄−L ≤ ε_s`; profile saturation (D8) | D4, D6, PD | – | E |
| D9a | `E_row = C{Γ√(S+1) + p^{13}/d²} + e^{-3p}` | CR3, MARKENV, D6, D78 | GR1, C2 | E |
| D9b | `Q ≤ Cp`; budgets with `Ω_±` | B1, D9a, D4, D78 | – | E |
| D10 | the full-compression lower bound | B1, D9b, T.ROOT, T.IL | C5, S1 | E–M |

Critical path in this range: **T.PL → T.BLmid → T.COV → B1**, in parallel with
**(E4/E5) → T.MARK/T.TRC → CR3 → D6**. All D-nodes after D6 are easy.

Simplifications recommended for the Lean DAG:
1. State and prove only **CR3**; CR1 is a two-line corollary.
2. One **T.BLmid** node replaces "Prékopa ⇒ Cov ⪯ M^{-1}", "Brascamp–Lieb", and WT3's covariance
   claim.
3. Phrase every "high-moment interpolation" as **T.IL** with explicit `k`, and every `D_*`
   maximum as **T.DSTAR**.

---

## 8. Numerical and symbolic checks performed

- `auditC_symbolic.py`: `K_i` identity (residual 0); first-order score identity; row-free part of
  `K_i` and "≥ 2 row factors, `p`-degree ≤ 3"; (D3) algebra (residual 0).
- `auditC_numeric.py` (random graph, `d = 4`, `p = 6`): F1 identities (to `1e-16`); the CR1
  Frobenius bound; C5 (exact identity plus bound, two shifts); B5; `M ⪯ A`, `‖M‖ ≤ sa²/h`; CR2 rule
  `D_ic_kj` and `Φ^{-1}∂_i³(Φx_i) = a³K_i` by 50-digit finite differences (12-digit agreement);
  Gaussian IBP `2𝖦F = 𝖦[(trA−q_A)g]` by 2-D quadrature (7 digits); BLmid conclusion
  `Σ_ν ⪯ E_ν(I+H)^{-1}` (min eigenvalue of the difference `> 0` in 3 trials) and
  `tr(M(I−Σ)) ≥ E tr(MH(I+H)^{-1}) ≥ tr(MH_0(I+H_0)^{-1})` in small-`H` regimes; the
  parallelogram inequality on 20000 random cases.
- `auditC_params.py` (500-digit arithmetic, `d = 10^{20}…10^{1000}`, `c_0 ∈ {1, 0.1, 0.001}`): the
  closed form of `L̄`, `p·d(r−1)(1−rL̄) → 1`, `(r−1)√(pd) → 1`, the `δ` bound, the exponent
  inequalities of D6/D7/D10, the E6 exponent (`→ −4.78`), and the GR1-necessity comparison of
  G8.

## 9. Notes for other audits

- Lines 1560–2073: the endgame needs `E_row = O(c_0^{17/3}/p)`. D9a delivers it only with GR1
  (G8). The `√(S+1)` is absorbed with `S − 4 ≥ −o(1)` (D15). That step is consistent with what
  D9a provides.
- Section 1.2 (E4/E5): the "derivative-word" bookkeeping can be replaced, for formalization, by
  coefficient majorants of one-variable polynomials `t ↦ F(x+te_i)` (all functions are polynomials
  in `t` times integer powers of quadratics). This yields `(Cp)^n a^n` bounds and marked bounds
  uniformly.
- Sections 1.1–1.3 (C1, C2, WT3): use T.BLmid (constant `K`) for all "covariance at most `M^{-1}`"
  claims.
