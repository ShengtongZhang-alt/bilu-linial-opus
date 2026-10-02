# AUDIT-B: lines 600–1076 of `docs/second_order_bilu_linial_tight.tex`

Scope: the end of the concentration proof (closing of (C6) into (C2)), Lemma "Uniform
incident-row gain" (GR1), Section 1.3 (mean shift (S1), Lemma "Random-profile weak loop"
(W1)–(W5)), and the paragraph "Weighted fresh-star quadratic domination" (WT1)–(WT5).
Every later use of `δ_row` / GR1 (Sections 1.4–1.5, lines 1077–2073) was also traced.
Scripts: `scripts/tight/auditB_checks.py`, `auditB_constants.py`, `auditB_condpos.py`,
`auditB_weak_identities.py` (run with `/tmp/tight-venv/bin/python`).

## 0. Verdict

**Verdict: correct, with fixable minor gaps. No fatal gap in lines 600–1076.**

**Main finding: Royen's Gaussian correlation inequality (GCI) can be avoided at zero cost.**
GR1 is used downstream in exactly two critical places, (FS5) and (D9a)/(CR3), and in
both the quantity that really has to be small is the *branch difference* of an incident
row, `G⁺_ij − G⁻_ij` (it is the determinant score `∂ log W = 2pa(G⁺_ij − G⁻_ij)`), not
the individual rows. The two exact row equations used in the proof of GR1 bound the
difference energy by `δ/p` with **no sign information on `T_v`**, hence without GCI:

```
(DR1)  sup_v a² Σ_{i~v} E(G⁺_vi − G⁻_vi)²  =  (B⁺_v + B⁻_v + 2a²T_v + E3_v)/(2p−1)
                                          ≤  K_DR (δ/p + p²/d).
```

(`|2a²T_v| ≤ a²(S⁺_v + S⁻_v) ≤ 2δ` by Cauchy–Schwarz and (C2).) With (DR1), the
weak-loop score in (W1) stated with its exact difference factor, the row observable in
(CR3) rewritten as `R_v = pΣx_j(x_j − z_j) − Σx_j²`, and `δ` used in place of `δ_row`
in (W1)'s remainder and in (D13), every estimate of Sections 1.3–1.5 closes with the
**same exponents and the same critical ledger (D16)**. GR1 itself (individual rows
`≤ δ/p`) is then never needed. Details: §3.3.

### Gaps and fixes (severity)

| id | where | severity | issue / fix |
|---|---|---|---|
| B-1 | GR1, lines 637–648 | minor (citation; avoidable) | Uses Royen monotonicity in `s` (not only GCI at `s=0`). Correct, but the cited "Milman §3.3" should be backed by Royen 2014 / Latała–Matlak 2017 (monotonicity in `τ` for symmetric slabs) plus slab approximation of ellipsoids. Whole GCI step removable via DR1 (§3.3). |
| B-2 | W1 score `S_f`, line 744 | minor (needed for the GCI-free route) | The proof produces the exact score factor `|G⁺_ij − G⁻_ij|`; the statement weakens it to `|G⁺_ij|+|G⁻_ij|`. State W1 with the difference. |
| B-3 | W1 remainder, lines 840–903 | minor | Only `ρ_row ≤ Kp^{-2}` is needed; the (C2) envelope `δ` already satisfies `δ ≤ Kp^{-2}` when `p^7 ≤ d`. Drop the dependence on GR1. |
| B-4 | (D9a)/(CR3), lines 1170–1190, 1505–1515 (outside range) | minor (needed for GCI-free route) | Use `R_v = pΣ_j x_j(x_j−z_j) − Σ_j x_j²`; the `Φ⁽⁴⁾R_v` term then costs `p⁵√(λ_r δ_diff) + p⁴λ_r` instead of `p⁵√(λ_r ρ_r)`. Same Γ. |
| B-5 | (D13), line 1951 (outside range) | minor | `δ` instead of `δ_row` costs `p³√(λ₁δ) = O(c₀^{17/3}p^{-2}) = o(p^{-1})`. |
| B-6 | closure of C2, lines 600–624 | minor | Needs `1/d ≤ z ≤ 1` (the bound `EW ≤ K(t+ε)` uses `dz ≥ 1`); `p⁹/d² ≤ u²` needs `p ≤ d^{4/25}` (true since `2/17 < 1/7 < 4/25`); `e^{-cp} ≤ u²` needs `p ≥ (2/(3c)) log d`. State these. |
| B-7 | (S1), lines 698–719 | minor (quantifiers) | "Absolute `C`" holds for `d ≥ d_S(c₀, κ₀)`; `K_S` itself does not depend on `c₀, κ₀`. This order (absolute K's → κ₀ → c₀ → d₀) is consistent with (D16). |
| B-8 | everywhere ("high-moment interpolation") | minor (make explicit) | One explicit lemma (I1, §2.0) with a polynomial floor `ϑ = d^{-M}` and moment order `k ≥ 2(M+M_env) log d` covers every use. |
| B-9 | GR1 statement | minor | With GCI the paper's bound is right; if one only had `T_v ≤ Kp⁵`, GR1 would still hold for `p ≤ d^{2/17}` (exact threshold), not for all `p ≤ d^{1/7}`. Irrelevant under the DR1 route. |

### Explicit constants and quantifier order

All constants below are absolute unless a dependence is shown. Order of choice:

1. **Absolute numerics:** `c₂ = 1/12`, `|c_j| ≤ 0.39^j` for `2 ≤ j ≤ 20` (asymptotically
   `|c_j|^{1/j} → 4/π² ≈ 0.405`; a Cauchy estimate on `|t| = √2 < π/2` gives
   `|c_j| ≤ M₀ 2^{-j}` for all `j`); endpoint remainders `|R₁| ≤ ‖f'''‖/3`,
   `|R₅| ≤ (2/15)‖f⁽⁵⁾‖` (computed); `log 40 − 48/7 = −3.168`.
2. **Absolute structural constants** `K_E4, K_E5` (derivative growth), `K_mom` (moment caps),
   `K_δ, K_b` (concentration), `K_CL, K_S, K_W, K_WT(m,M,C_h), K_DR`: each defined in §2 by
   an explicit inequality; none depends on `c₀, κ₀, d, p`, the graph or its order.
3. `κ₀ ∈ (0,1]` and then `c₀ ∈ (0,1]` (Section 1.5, from (D16)); they depend only on the
   absolute `K`'s.
4. `d₀ = d₀(c₀, κ₀)`: all "large d" conditions (listed per node) hold for `d ≥ d₀`.

Standing numerical facts at `p = ⌊c₀d^{2/17}⌋`, `c₀ ≤ 1`: `p^{17} ≤ c₀^{17} d² ≤ d²`, so
`p^7 ≤ d` once `d ≥ 1`; `ε = η₀/2 ≤ (pq)^{-1/2}`; `δ ≤ K_δ(1+o(1))c₀^{17/6}p^{-5/2}`;
`(p/d)^{1/3} ≤ c₀^{17/6} p^{-5/2}·(1+o(1))`; `k_* = ⌈16p/log d⌉` and the derivative
order `4k_*+4 ≤ p−2` once `log d ≥ 128`, `p ≥ 20`; (E6) holds with `c_E = 3` once
`64 log K_E5 / log d + (5 log p + 8 log K_E5)/p ≤ 0.168`.

### External theorems needed (exact special cases)

* **(X1) Gaussian covariance domination** (planned fact (a)): `M ≻ 0`, `f ≥ 0` even,
  log-concave on an open convex set and zero outside, `μ ∝ f·γ_M` ⇒ `Cov_μ ⪯ M^{-1}`.
  Used in (WT3) with `M = I`, `f = H·Φ`; in the (C1)/(C2) whitening with
  `M = I + 2(p−1)A`. Only covariance against PSD *quadratic forms* is used:
  `E_μ q_L ≤ tr(L M^{-1})`.
* **(X2) Gaussian IBP** (fact (b)): `E_γ[x_i g] = E_γ[∂_i g]` for `g` locally Lipschitz
  with polynomial growth (clipped powers `(1−q)_+^m`, `m ≥ 1`, qualify).
* **(X3) Cramér–Rao lower bound** (used in (C4), feeding (C6)): `μ ∝ e^{-V}γ`, `V` convex
  `C²` on an open convex set with `e^{-V}|∇V| → 0` at its boundary ⇒
  `Σ_μ ⪰ (I + E_μ∇²V)^{-1}`; from (X2) and the matrix Cauchy–Schwarz inequality.
  (Planned fact (c) is the same IBP computation.)
* **(X4) Rademacher–Gaussian comparison (E4)** (fact (d)), graded multi-coordinate form.
* **(X5) 1-D endpoint identities** for `ξ` uniform on `{±1}` (elementary Taylor).
* **(X6) Log-concavity of determinant weights:** `P ↦ log det P` concave on PD;
  `P ↦ tr(P+tI)^{-1}` convex on PD, hence `log det P − log det(P+hI)` concave; composed
  with affine `x ↦ P(x)`; products; extension by zero. Numerically confirmed (§6).
* **(X7) Matrix toolkit:** Schur inverse formula; `(P^{-1})_{JJ} ⪰ (P_{JJ})^{-1}`;
  `(C²)[N,N] ⪰ (C[N,N])²`; commuting spectral calculus (`X² ⪯ h^{-1}(G−X)`,
  `C − C_z ⪰ zC_z²`); `|G_ij| ≤ √(G_ii G_jj)`; resolvent derivatives.
* **(X8)** Jensen, Hölder, Markov, Cauchy–Schwarz (Mathlib).
* **(X9) GCI — NOT needed** on the DR1 route. If GR1 is kept verbatim: Royen's
  monotonicity for symmetric slabs (Latała–Matlak), extended to centered ellipsoids, in the
  form `E_γ⟨∇α^p, ∇β^p⟩ ≥ 0`. Very hard to formalize (multivariate gamma densities,
  Laplace-transform uniqueness).

### Conclusion on GCI

1. Exact inequality used: `G[q_AB α^{p−1} β^{p−1}] ≥ 0`, `q_AB(x) = ⟨Ax,Bx⟩`,
   `A = (a²/Z⁺_v) G⁺_K[N,N]`, `B = (a²/Z⁻_v) G⁻_K[N,N]` (compressed core inverses of the
   two branches, `K = H−v`, `N = N(v)`), `α = (1−q_A)_+`, `β = (1−q_B)_+`. It equals
   `(4p²)^{-1} E_γ⟨∇α^p, ∇β^p⟩`, the `s = 1` derivative of Royen's monotone function.
2. Slack: `T_v ≤ Kp⁵` would suffice (exact threshold, because `p ≤ d^{2/17}`);
   `T_v ≤ Kp^{5+ε}` and the trivial `T_v ≲ δd ≍ p⁶` do not. With no row gain at all the
   method only gives the exponent `4/37 < 2/17`.
3. No cheap proof of the inequality itself was found: it is equivalent to the
   conditional positivity `E_γ[⟨Ax,Bx⟩ | q_A, q_B] ≥ 0` (two-ellipsoid infinitesimal GCI);
   it is elementary only for exponential profiles (`tr(AB(I+c₁A+c₂B)^{-1}) ≥ 0`, proved in
   §3.2), and a perturbative proof needs `‖A‖ ≲ 1/p` pointwise, which is not available.
4. **But GCI is not needed**: replace GR1 by DR1 (§3.3). Cost: none.

## 1. Standing hypotheses and definitions

**Parameters.** `d ≥ d₀`, `q = d−1`, `p = ⌊c₀d^{2/17}⌋` (`0 < c₀ ≤ 1`), `R² = 4q+4/p`,
`a = 1/R`, `qη₀²/(1−η₀) = 4/p`, `τ_* = (1−η₀)/q`, `s = (2−η₀)/(1−τ_*)`, `r = 1+ε`,
`ε = η₀/2`. Explicit: `η₀ ≤ 2(pq)^{-1/2}`, `ε ≤ (pq)^{-1/2}`, `s ≤ 2q/(q−1) ≤ 2.01`
(`q ≥ 201`), `L̄ = da²s² = dq(1−η₀)/(q−1+η₀)² ≤ 1 + 4/q` (`q ≥ 7`), `c_ij ≤ a²s² ≤ 1.01/d`,
`C_v = Σ_i c_vi² ≤ 1.03/d`, `D_v = y_vZ_v = 1 + L_v − C_v ∈ [1, 2.01]`, `1/Z_v ≤ y_v ≤ s`.

**Graph and law.** `H` finite simple, max degree `≤ d`, any order. Sources
`y^± ∈ [0,s]^V`, precisions `P^± = diag Z(y^±) ± aA_σ`, paired weight
`W = 1{P^±≻0}(det P⁺ det P⁻)^p`, `G^± = (P^±)^{-1}`, `h_i^± = G^±_ii / y_i^±` (`:= 1` at
`y_i = 0`). `E` = expectation under the paired law of `H` at the given sources.

**(CAP) capped source law.** The law exists on the whole source cube below `y^±`, and
every normalized first mean is `≤ r` (for `H`; proper cores inherit it by induction).
Consequences used below (from (F2), audited elsewhere):
* (M) for `1 ≤ k ≤ min(p/2, p−2)` and `pε ≤ 1/8` (true for `p ≤ q/64`):
  `E(h_i^±)^k ≤ (1+2ε)^k ≤ e^{1/8} < 1.14`; physical `G_ii ≤ 2.01 h_i`,
  `Z_iG_ii = D_ih_i ≤ 2.01 h_i`.
* (C2) from the concentration lemma: `ρ := sup_{i,±}(1−Eh_i^±)_+ ≤ δ`,
  `sup_{v,±} a²S_v^± ≤ δ`, `sup_v E tr(A²+B²) ≤ δ`, `sup E(h_i−1)² ≤ δ`, with
  `δ = K_δ{ε + p⁴/d + (p/d)^{1/3}}`.

**Root quantities** (root `v`, `N = N(v)`, core `K = H−v` with inherited precisions,
`ξ ∈ {±1}^N` the fresh star): `A = (a²/Z⁺_v)G⁺_K[N,N]`, `B = (a²/Z⁻_v)G⁻_K[N,N]` (PSD),
`α = (1−ξᵀAξ)_+`, `β = (1−ξᵀBξ)_+`, `Φ = α^pβ^p`, `q_M(x) = xᵀMx`,
`q_AB(x) = ⟨Ax,Bx⟩ = xᵀABx`, `μ₀ = tr(A+B)`, `b_i = A_ii + B_ii`, `Θ = tr(A²+B²)`.
`G[·]` = expectation over `x ~ N(0, I_N)`, `R[·]` over uniform `ξ`; `ν_K` = own law of the
core; `F_H = E_{ν_K}R[Φ] ≥ 40^{-p}`; actual expectation of `ψ(core, ξ)` is
`E_{ν_K}R[ψΦ]/F_H`. On good endpoints (F1): `Z⁺_vG⁺_vv = 1/α`,
`(Aξ)_i/α = −aG⁺_vi`, `(Bξ)_i/β = aG⁻_vi`.

**Row quantities.** `S_v^± = Σ_{i~v}E(G^±_vi)²`, `T_v = Σ_{i~v}E G⁺_vi G⁻_vi`,
`m_v^± = Eh_v^±`, `B_v^± = 1 − D_v^±m_v^± + a²Σ_{i~v}E G^±_vv G^±_ii`.

**Shifted.** `X_z^± = (P^± + zI)^{-1}`, `t_z = sup_{i,±}(1 − E(X_z^±)_ii/y_i^±)_+`
(ratio `:= 1` at `y_i = 0`), `C_{z,ν} = (P^ν_{−v}+zI)^{-1}`, `C_ν = (P^ν_{−v})^{-1}`,
`b = ε + K_b p⁴/d + 1/d`, `u = (p/d)^{1/3}`.

## 2. Claim-by-claim audit

### 2.0 Support lemmas used throughout

**(I1) Interpolation with a polynomial floor.** Let `Y ≥ 0`, `Z ≥ 0` be random variables
with `EY ≤ m`, `‖Y‖₂ ≤ d^{M_env}`, `‖Z‖_k ≤ K_Z`. If `ϑ = d^{-M}` and
`k ≥ 2(M + M_env) log d`, then `E[YZ] ≤ e² K_Z (m + ϑ)`.
*Proof.* Hölder with `θ = 2/k`: `E[YZ] ≤ m'^{1−θ}‖Y‖₂^θ‖Z‖_k` with `m' = max(m, ϑ)`;
`m'^{-θ} ≤ d^{2M/k} ≤ e`, `‖Y‖₂^θ ≤ e`. Status: OK. This is the paper's "high-moment
interpolation"; the paper's variants `(t+ε)^{1−O(1/p)} ≤ C(t+ε)` use the floor
`ε ≥ (2(pq)^{1/2})^{-1}·…` — any floor `≥ d^{-M}` works. Needs `p/log d` large because
`k ≤ p/2` is the available moment order.

**(I2) Maxima over a deterministic set.** For a deterministic set `S` of vertices,
`‖max_{i∈S}(1+G_ii)‖_k ≤ |S|^{1/k} max_i ‖1+G_ii‖_k`. With `|S| ≤ d²+d+1` and
`k ≥ 2 log d`, the factor is `≤ e^{3/2}`. Used for `D_*` in (W1). OK.

**(E1′) first-order endpoint identity** (for (W1)): for `f ∈ C³[−1,1]`,
`E_ξ[ξf(ξ)] = E_ξ[f'(ξ)] + R₁`, `|R₁| ≤ (1/3) sup_{[−1,1]}|f'''|` (trapezoid rule).
Third-order version (for (E1)): `E_ξ[ξf] = E_ξ[f' − f'''/3] + R₅`,
`|R₅| ≤ (2/15) sup|f⁽⁵⁾|` (Peano kernel, computed in `auditB_constants.py`). OK.

### 2.1 Closing (C6) into (C2) (lines 599–624)

**Statement (CL1).** Assume (CAP), `p ≤ d^{1/7}`, `d ≥ d_CL`. For every `z` with
`1/d ≤ z ≤ 1`,
```
t_z² ≤ K_CL { z + p(t_z+b)/(dz) + p⁵(t_z+b)/d + p²/d + p⁹/d² + 1/d + e^{-c_E p} }.
```
**(CL2).** With `z = u²`: `t := t_{u²} ≤ K'_CL u`, `K'_CL = (K + √(K²+4K))/2` where
`K = K_CL(3 + K_b)` (see step 8). Consequently `ρ ≤ t ≤ K'_CL u` and (C2) holds with
`K_δ` explicit in `K'_CL` and the constants of (C3), (C3b).

Proof, step by step (all verified):
1. *Root Schur identity* at the maximizing branch (say `+`):
   `1/(X_z)_vv = Z_v + z − q_z`, `q_z = a²ξᵀC_{z,+}[N,N]ξ`. OK (X7).
2. *Jensen:* `1/m_v ≤ E[1/(X_z)_vv]`, `m_v = E(X_z)_vv > 0`. OK.
3. *Bias* (C6, audited with C4–C5): `E(μ_z − q_z) ≤ Z_v·ℰ`, where
   `ℰ = K₆{p(t+b)/(dz) + p⁵(t+b)/d + p²/d + p⁹/d² + e^{-c_E p}}`. Requires `dz ≥ 1`
   (used in `EW ≤ K(t+ε)`, line 561: `tr_N(C−C_z) ≤ Σ_{i∈N}(G_ii−X_ii) + Z_v(G_vv−X_vv)/z`).
4. *Core replacement:* `μ_z = a² tr C_{z,+}[N,N] = a²Σ_{i∈N}(X_z)_ii − a² tr_N(X_z − C_z)`,
   and by (C5) `a² E tr_N(X_z − C_z) ≤ a² Z_v E(G_vv − X_vv)/z ≤ a²Z_vy_v(ε+t)/z ≤
   2.01(ε+t)/(4qz)` (using `EG_vv ≤ ry_v`, `E X_vv ≥ (1−t)y_v`). OK.
5. If `t = 0` nothing to prove. Else pick `(v,±)` attaining `t` (finite sup). Then
   `y_v > 0` (zero sources have ratio 1), `m_v = y_v(1−t)`, `m_i ≥ y_i(1−t)`.
6. Steps 1–5 give `1/(y_v(1−t)) ≤ Z_v + z − a²(1−t)Σ_i y_i + e_v`; multiply by `y_v`, use
   `y_vZ_v = 1 + L_v − C_v`: `t²/(1−t) ≤ (L_v−1)t − C_v + y_v(z+e_v)`. Verified
   symbolically. With `L_v ≤ 1+4/q`, `C_v ≥ 0`, `y_v ≤ 2.01`, `t ≤ 1`:
   `t² ≤ 4/q + 2.01(z + e_v)`. Here `e_v = E(μ_z−q_z) + a²E tr_N(X_z−C_z)`, so
   `y_v e_v ≤ D_vℰ + 1.02(ε+t)/(dz) ≤ 2.01ℰ + 1.02 p(t+b)/(dz)` — i.e. (CL1). OK.
7. (CL1) is what (S1) reuses with `z = h` (B-6: needs `1/d ≤ z ≤ 1`).
8. With `z = u²`: `p(t+b)/(dz) = u(t+b)`. In powers (checked in `auditB_checks.py`):
   `p⁵/d ≤ u ⟺ p^7 ≤ d`; `ε ≤ u ⟺ 1 ≤ p⁵d` (true); `p⁴/d ≤ u ⟺ p^{11} ≤ d²`;
   `p²/d ≤ u² ⟺ p⁴ ≤ d`; `p⁹/d² ≤ u² ⟺ p^{25} ≤ d⁴` (needs `p ≤ d^{4/25}`; holds);
   `1/d ≤ u²`; `e^{-c_E p} ≤ u²` for `p ≥ (2/(3c_E)) log d`. Hence
   `b ≤ (2 + K_b)u` and `t² ≤ K(ut + u²)`, giving (CL2). OK.

**Status: OK (minor B-6).** Constants: `K_CL = 2.01(2.01K₆ + 1.02) + 5` suffices for the
form shown (the `4/q` term is absorbed into `1/d` with factor 5). Quantifier: absolute;
`d_CL` depends only on `K₆, c_E` (for `e^{-c_E p} ≤ u²`) and on (E6)'s threshold.

### 2.2 Lemma "Uniform incident-row gain" (GR1, lines 626–693)

**Statement (as in the paper, made explicit).** Assume (CAP), (C2), `p ≤ d^{1/7}`,
`d ≥ d_GR`. Then for every vertex `v` and branch `ν`:
`a² S_v^ν ≤ δ_row := K_GR δ/p`.

**Proof steps and verification.**
* **G1 (GCI).** For each fixed core: `G[q_AB α^{p−1}β^{p−1}] ≥ 0`. Route: `X, Y_s`
  standard Gaussian in `ℝ^N` with `Cov(X,Y_s) = sI`; `H(s) = E α(X)^p β(Y_s)^p` is
  nondecreasing on `[0,1]` (Royen; `α^p`, `β^p` are even, quasi-concave, superlevel sets
  closed symmetric convex, possibly unbounded cylinders when `A` is singular);
  `H'(s) = E[∇α^p(X)·∇β^p(Y_s)]` by (X2) (`|∇α^p| ≤ 2p‖A‖^{1/2}` on the support, so
  bounded gradients; continuity of `H'` at `s=1` by dominated convergence);
  `H'(1) = 4p² G[q_AB α^{p−1}β^{p−1}] ≥ 0`. **OK given Royen's monotone form** (B-1).
* **G2 (transfer, `T_v ≤ K_T p⁴`).** On the support `|q_AB| ≤ (‖A‖‖B‖)^{1/2} ≤ μ₀`,
  `|∂_i q_AB| ≤ 2μ₀√b_i`, `|∂_i∂_j q_AB| ≤ 2μ₀√(b_ib_j)`, third derivatives vanish; hence
  `|∂^νF| ≤ (K_E5 p)^{|ν|} μ₀ Π b_i^{ν_i/2}` for `F = q_AB α^{p−1}β^{p−1}` and
  `|ν| ≤ 4k_*+4 ≤ p−2`. At sign endpoints `F/(a²Φ) = −Σ_{j∈N}G⁺_vjG⁻_vj` (from (F1)).
  Retained grade `j` (`l ≤ j` active coordinates, derivative order `2(j+l)`, one free
  index): `a^{2(j+l)}d^{l+1}(K p)^{4j} ≤ (Kp)^{4j}d^{1−j}` after dividing by `a²`, using
  `|G_kl| ≤ √(G_kkG_ll)` and (M). Remainder `≤ d·40^p(Kp)^{4k_*+4}d^{-k_*-1}·K ≤ e^{-3p}`
  by (E6). With `G[F] ≥ 0`: `T_v ≤ 2(Kp)⁴ + e^{-3p} =: K_T p⁴` once `(Kp)⁴ ≤ d/2`. OK.
* **G3 (row equations).** Summing (E1) over `i ~ v` against the exact identity
  `aΣ_iσ_viG⁺_vi = 1 − Z⁺_vG⁺_vv`, and using (E3)
  (`D₁G⁺_vi = −aG⁺_vvG⁺_ii + (2p−1)a(G⁺_vi)² − 2paG⁺_viG⁻_vi`; for the minus branch
  `−aD₁G⁻_vi` has the same form with `+2pa²G⁺_viG⁻_vi`; signs re-derived):
  ```
  (2p−1)a²S_v^± − 2p a²T_v = B_v^± + E3_v^±,   |E3_v^±| ≤ K₃(p³/d + p⁵/d²).
  ```
  (`|D₃G_vi| ≤ K p³a³D⁴` summed with the outer `a` over `≤ d` indices; (E1)'s remainder
  `K p⁵a⁵` likewise.) OK.
* **G4.** `B_v^± ≤ 1 − D_v(1−ρ) + L_v max_i E[h_vh_i] ≤ C_v + D_vρ + L_v(1+Kε)
  ≤ 1.03/d + 2.01ρ + 1.01Kε`, using `E h² ≤ ((pr−2)/(p−2))² ≤ 1 + 5ε`. OK.
* **G5.** `a²S_v^± ≤ [B_v^± + 2pa²K_Tp⁴ + |E3|]/(2p−1) ≤ K(ρ+ε+1/d)/p + K p⁴/d`, and
  `p⁴/d ≤ (p/d)^{1/3}/p ⟺ p^7 ≤ d`. OK.

**Status: OK given GCI (B-1); every later use can avoid it (§3.3).**

### 2.2′ New node (DR1): score-difference energy, GCI-free

**Statement.** Assume (CAP), (C2), `p ≤ d^{1/7}`, `d ≥ d_DR`. For every vertex `v`:
```
a² Σ_{i~v} E(G⁺_vi − G⁻_vi)² ≤ δ_diff := K_DR (δ/p + p²/d).
```
**Proof.** Solve the two equations of G3 for `a²S⁺_v, a²S⁻_v` (sympy check in
`auditB_constants.py`): `a²(S⁺+S⁻−2T) = (B⁺ + B⁻ + 2a²T + E3⁺ + E3⁻)/(2p−1)`. Bound
`2a²T ≤ a²(S⁺+S⁻) ≤ 2δ` (Cauchy–Schwarz, (C2)), `B^±` by G4, `E3` by G3:
`δ_diff ≤ [2(1.03/d + 2.01δ + 1.01Kε) + 2δ + 2K₃(p³/d + p⁵/d²)]/(2p−1)`.
Since `ε + 1/d ≤ δ/K_δ` this is `≤ K_DR(δ/p + p²/d)`. **No sign of `T_v` is used.**
Moreover `p²/d ≤ δ/p` because `p³/d ≤ (p/d)^{1/3} ⟺ p⁴ ≤ d`, so
`δ_diff ≤ 2K_DR δ/p`: the same order as the paper's `δ_row`. Difficulty: easy given G3.

Why the two equations cannot bound `S⁺+S⁻` alone: summing gives
`(2p−1)a²(S⁺+S⁻) = B⁺+B⁻+4p a²T + E3`, and `4p a²T ≤ 2p a²(S⁺+S⁻)` is too weak; the
weight's repulsion acts only on the difference `G⁺−G⁻`.

### 2.3 Mean shift (S1, lines 696–719)

**Statement (S1).** Assume (CAP), `p = ⌊c₀d^{2/17}⌋`, `h = κ₀p^{-4}`, `κ₀ ∈ (0,1]`.
There are an absolute `K_S` and `d_S(c₀,κ₀)` such that for `d ≥ d_S`, all `i`, `±`:
`t_h ≤ K_S√h` and `0 ≤ E(G^±_ii − X^±_ii)/y_i^± ≤ (K_S+1)√h`. **Weighted form:** for any
product `Π` of at most `m` normalized (or physical) inverse diagonals, shifted or not,
`E[(G_ii−X_ii)Π]/y_i ≤ K_S(m)√h` (zero sources: the ratio is 0 by convention/continuity).

**Proof.** (CL1) with `z = h` (`dh = κ₀ d p^{-4} ≥ 1` for `d ≥ d_S`). In powers of `p`
(`d ≍ p^{17/2}`): `p/(dh) ≍ p^{-7/2}`, `p⁵/d ≍ p^{-7/2}`, `√h ≍ p^{-2}`, `pb/(dh)`,
`p⁵b/d`, `p²/d ≍ p^{-13/2}`, `p⁹/d² ≍ p^{-8}`, `1/d`, `e^{-3p}` all `≤ h/K_CL` for
`d ≥ d_S`; and `K_CL(p/(dh) + p⁵/d) ≤ √h`. Then `t_h² ≤ K_CL h + √h t_h + h`, so
`t_h ≤ ½(1 + √(1+4(K_CL+1)))√h =: K_S√h`. The difference bound: `EG_ii ≤ ry_i`,
`EX_ii ≥ (1−t_h)y_i`, `ε ≤ √h`. Weighted form by (I1) with envelope
`(G_ii−X_ii)/y_i ≤ h_i` and floor `ϑ = d^{-10} ≤ √h`. **Status: OK (B-7).**

### 2.4 Lemma "Random-profile weak loop" (W1)–(W5), lines 721–911

**Statement (explicit, with fixes B-2, B-3).** Assume (CAP), (C2), (S1),
`p = ⌊c₀d^{2/17}⌋`, `h = κ₀p^{-4}`, `d ≥ d_W(c₀,κ₀)`. Fix a vertex `v`, `N = N(v)`,
`u = 1_N/√d`, `T = a²A_H` (unsigned), `ε,ν ∈ {±}`, `X_τ = (P^τ+hI)^{-1}`,
`K_σ = X_ε∘X_ν/4`, `M_σ = diag((X_ε)_ii(X_ν)_ii/4)`, `b_σ = 4TM_σu`,
`w_σ = u − εν b_σ`, `H ∈ {1, (G⁺_vv/2)², G⁺_vvG⁻_vv/4}`, `f ∈ {u, b_σ}`,
`U = X_ε D_f X_ν`, `F_ji = (X_ε)_ii U_ji − (X_ε)_ji U_ii`,
`D_* = 1 + max{G^τ_kk : τ = ±, k ∈ N ∪ N_H(N) ∪ {v}}`. Then
```
|E[H w_σᵀK_σ f] − E[H uᵀM_σ f]| ≤ S_f + K_W {p/(dh) + 1/(dh^{3/2})},
S_f = (a/4) Σ_{i∈N} Σ_{j~i} u_i E[ |F_ji| { 2pa H |G⁺_ij − G⁻_ij| + |∂_ij H| } ].
```
(The paper writes `|G⁺_ij| + |G⁻_ij|`; the proof produces the difference, which is what
the GCI-free route needs. The paper's `B₀` also carries `e^{-cp}`; this proof does not
produce it, and it is harmless.)

**Proof steps.**
* **(W2)** exact, pointwise: `U_ii − f_i(X_ε)_ii(X_ν)_ii = −εaΣ_{j~i}σ_ijF_ji`
  (row `i` of `(P^ε+h)U = D_fX_ν` times `(X_ε)_ii` minus row `i` of `(P^ε+h)X_ε = I`
  times `U_ii`). **Verified** numerically (`auditB_weak_identities.py`, residual `1e-17`).
  With `U_ii = 4(K_σf)_i`: `Σ_i u_iU_ii = 4uᵀKf`, `Σ_i u_if_i(X_ε)_ii(X_ν)_ii = 4uᵀMf`.
* **(W3)** exact edge derivative (mask fixed): **verified** by finite differences
  (residual `4e-11`) and by hand expansion.
* **(W4)** apply (E1′) to each edge `ij`, `i ∈ N`, `j ~ i`, with
  `g(s) = W·H·u_i·F_ji` on the two-point fiber: `E[σ_ijΨ] = E[∂Ψ + Ψ∂ℓ] + R₁`,
  `∂ℓ = 2pa(G⁺_ij − G⁻_ij)` exactly. The main term `−aν(X_ε)_ii(X_ν)_iiU_jj` of (W3)
  gives `εν a²Σ_{i,j~i}Hu_i(X_ε)_ii(X_ν)_iiU_jj = 4εν H b_σᵀK_σ f`
  (`(b_σ)_j = Σ_{i~j} a²(X_ε)_ii(X_ν)_ii u_i`), i.e. (W4). OK.
* **(W5)** `E[D_*^C r_i^τ] ≤ K h^{-1/2}`, `r_i^τ = (X_τ²)_ii`: `X² ⪯ GX = h^{-1}(G−X)`
  (commuting spectral calculus), (S1), and (I1) with envelope `r_i/y_i ≤ h^{-1}h_i` and
  loss `h^{-O(1/p)} = O(1)`. OK.
* **Secondary terms of (W3).** `‖Ue_i‖ ≤ mh^{-1}√r_i^ν`, `|U_ii| ≤ m√(r_i^εr_i^ν)`,
  `‖F_{·i}‖ ≤ 2mh^{-1}D_*√r_i^ν` (`m = ‖f‖_∞ ≤ 1.02·D_*²/√d`; for `b_σ` use
  `‖b‖_∞ ≤ a²d·D_*²/√d`), then `Σ_{j~i}|(X_τ)_ijF_ji| ≤ 2mh^{-1}D_*√(r_i^τr_i^ν)`,
  `Σ_{j~i}|(X_ε)_ijU_ij| ≤ mh^{-1}r_i^ε`; with (W5) each is `≤ K d^{-1/2}h^{-3/2}`; the
  outer `a²u_i` summed over `i ∈ N` gives `K/(dh^{3/2})`. All re-derived. OK.
* **Random mask.** `∂_ij(b_σ)_k = −2aΣ_{l∈N}T_kl u_l{ε(X_ν)_ll(X_ε)_li(X_ε)_lj +
  ν(X_ε)_ll(X_ν)_li(X_ν)_lj}` (re-derived), `‖∂_ijb‖_∞ ≤ (KaD_*/d^{3/2})Σ_τ√(r_i^τr_j^τ)`,
  `|F_ji(g)| ≤ Kh^{-1}D_*²‖g‖_∞`, total `K/(dh^{3/2})` after `≤ d²` pairs and `au_i`. OK.
* **Endpoint remainder** `R₁`: on regular fibers (endpoint diagonal sum `≤ (64pa)^{-1}`),
  `G(s) ⪯ 2G(endpoint)`, weight ratios `≤ e^{1/16}`, `sup_s R_ij(s) ≤ R_ij + KaD_*²`;
  `W^{-1}|∂³(WHF_ji)| ≤ (Ka³D_*^C/(√d h)){p³R³ + p²R + p²R² + p + 1}` with
  `R = R_ij = |G⁺_ij|+|G⁻_ij|`; averaging over `i ∈ N`, `j ~ i` (both padded to `d`):
  `E[D_*^CR^k] ≤ Kρ_row` (`k = 2,3`), `≤ K√ρ_row` (`k=1`), where it suffices to take
  **`ρ_row = K(δ + 1/d)`** from (C2): `δ ≤ Kp^{-2}` whenever `p^7 ≤ d` (B-3). Coefficient
  `K(p³ρ + p²√ρ + p) ≤ Kp`; with the outer `au_i`: `Kp/(dh)`. Omitted (non-regular) good
  endpoints: Markov with 8 extra moments, `K p⁸ d^{-7/2} h^{-1} = o(p/(dh))`. OK.

**Status: OK, with fixes B-2 (state the exact score) and B-3 (no GR1 needed).** Constants:
`K_W` absolute (depends on the moment constants and on the number of fixed root-weight
factors). `d_W(c₀,κ₀)` ensures `dh ≥ 1`, `p^7 ≤ d`, and the interpolation conditions.

### 2.5 Weighted fresh-star quadratic domination (WT1)–(WT5), lines 913–1075

**Statement (explicit).** Freeze `H − i`; `ξ` = incident signs at `i`, `J = N(i)`,
`N = N(v)`, `u_k = 1_N(k)/√d`, `G_τ = P_τ^{-1}`, `X_τ = (P_τ+hI)^{-1}`,
`C_τ = (P_{τ,−i}+hI)^{-1}` (core, zero `i` coordinate), `d^{-C_h} ≤ h ≤ 1`,
`p/log d ≥ L₀`, `p ≤ d^{1/7}`. For `T ∈ {T_dir, T_cav}` of (WT1) (or a sum of a bounded
number `n_L` of their PSD forms), `L = TᵀT`, and
`H = H₀(X_ε)_ii²(X₊)_ii²`, `H₀` a product of at most `m₀` physical inverse diagonals
(shifted or not) with indices in the radius-2 ball: for every `M > 0`, `ϑ = d^{-M}`,
```
E[H q_L(ξ)] ≤ K_WT E[H tr L] + K_WT ϑ + e^{-3p},   K_WT = K_WT(m₀, n_L, M, C_h).
```
Uniform in graph order and sources (zero-source limits included).

**Proof steps.**
* **Log-concavity (X6).** Per branch, `det(P)^p·H = Π(principal minors)^{+}·
  det(P)^{p−m−n}(det P/det(P+hI))^n`, `m+n ≤ m₀ ≤ p`. Each factor is log-concave in the
  star vector `x` (`P(x)` affine in `x`): `log det` concave on PD;
  `log det P − log det(P+hI) = −∫₀^h tr(P+tI)^{-1}dt` concave since `tr(·)^{-1}` is convex.
  Positive powers of principal minors (`det P_{−k}`, `det(P+h)_{−k}`) are log-concave.
  Support `{P⁺(x)≻0, P⁻(x)≻0}` is convex; extension by zero preserves log-concavity.
  Numerically confirmed for the shifted ratio (`auditB_checks.py`, max second difference
  `−9e-8`). The gauge flip at `i` (`x ↦ −x`) fixes every principal minor ⇒ even. OK.
* **(WT3).** By (X1) with `M = I`, `f = HΦ`: `Cov ⪯ I`, mean zero, so for the core-fixed
  PSD `L`: `G[Hq_LΦ] ≤ tr(L)·G[HΦ]`. Only (X1) is needed, not the full Brascamp–Lieb.
  This also covers root diagonals `G_vv` (`v ≠ i`) in `H₀`: `G_vv = det P_{−v}/det P`.
  OK.
* **(WT4)** table, re-derived: derivative order `n = 2(g+l) ≤ 4g`; 0, 1, 2 derivatives
  on `q_L` give `a^nd^l q_L ≤ C^g d^{-g}q_L`; `a^{n−1}d^{l−1}Σ_s|(Lξ)_s| ≤
  C^gd^{-g}√(tr L·q_L)` (`|(Lξ)_s|² ≤ L_ss q_L`, `Σ_s√L_ss ≤ √(d trL)`);
  `a^{n−2}d^{l−1}Σ_sL_ss ≤ C^gd^{-g}trL`; `a^{n−2}d^{l−2}Σ_{s,t}|L_st| ≤ C^gd^{-g}trL`
  (`l ≥ 2`). Derivatives of `HΦ/Φ` keep `H` up to diagonal multipliers
  (`|∂_sG_kk| ≤ 2aG_kk√(G_iiG_ss)`). OK.
* **(WT5).** (I1) with the floor `ϑ` against the masses `x = E[Hq_L]`, `y = E[H trL]`
  (mixed term `≤ K√((x+ϑ)(y+ϑ))`); grade `g` costs `(Kp⁴/d)^g`, polynomial-floor factor
  `C^g` (because `p/log d → ∞`): `|x_G−x| + |y_G−y| ≤ K(p⁴/d)(x+y+ϑ) + e^{-3p}`. OK.
* **Absolute remainder.** Envelopes `ξᵀQ[J,J]ξ ≤ Z_i⁺/a²` on the support,
  `C₊² ⪯ h^{-1}C₊ ⪯ h^{-1}Q`, `ξ_l² ≤ Z_l⁺ξᵀQ[J,J]ξ` (padding and Cauchy–Schwarz in `Q`),
  `Z_i⁺(X₊)_ii² ≤ 1/(Z_i⁺α₊²) ≤ s/α₊²`: the remainder is `poly(d,h^{-1})·
  40^p(Kp)^{4k_*+4}d^{-k_*-1} ≤ e^{-3p}` for `d ≥ d_WT(C_h, M)`. All re-derived. OK.
* **Conclusion.** `x ≤ x_G + K(p⁴/d)(x+y+ϑ) + e^{-3p} ≤ y_G + … ≤ y + 2K(p⁴/d)(x+y+ϑ)
  + 2e^{-3p}`; absorb: `x ≤ (1+4Kp⁴/d)y + Kϑ + 3e^{-3p}`. OK.

**Status: OK.** No gap. `K_WT` depends only on `(m₀, n_L, M, C_h)`; in Section 1.5 these
are fixed numbers (`C_h = 1` since `h = κ₀p^{-4} ≥ d^{-1}` for `d ≥ d₀(c₀,κ₀)`).

## 3. The Gaussian correlation inequality in GR1

### 3.1 (i) The exact inequality

`G[q_AB α^{p−1}β^{p−1}] ≥ 0` for every fixed core, with `A`, `B` the two compressed core
inverses of §1 (PSD, `A = (a²/Z⁺_v)G⁺_K[N,N]`, `B = (a²/Z⁻_v)G⁻_K[N,N]`),
`q_AB(x) = ⟨Ax,Bx⟩`. Equivalent forms:
* `E_γ⟨∇α^p, ∇β^p⟩ ≥ 0` (`= 4p² G[q_AB α^{p−1}β^{p−1}]`), the `s = 1` derivative of
  Royen's monotone function `H(s) = Eα(X)^pβ(Y_s)^p`;
* by layer cake in `q_A`, `q_B`: **conditional positivity (CP)**
  `E_γ[⟨Ax,Bx⟩ | q_A, q_B] ≥ 0`, i.e. `E_γ[⟨Ax,Bx⟩φ(q_A)ψ(q_B)] ≥ 0` for all Borel
  `φ, ψ ≥ 0` (the infinitesimal GCI for two centered ellipsoids). Monte Carlo over 60
  random pairs `(A,B)` in dimensions 2–5 found no negative bin (min z-score −2.56 over
  8640 bins, consistent with noise; `auditB_condpos.py`).

### 3.2 (ii) Slack, and (iii) attempts to prove the inequality without GCI

**Slack.** GR1 enters only through `a²T_v`, via `a²S_v ≤ [B + 2pa²T_v + O(p³/d)]/(2p−1)`.
If `T_v ≤ Kp^m`, then `δ_row = K(δ/p + p^m/d)`. In powers of `p` (`d ≍ p^{17/2}`,
`auditB_checks.py`):

| `m` | `δ_row` | `p e²` (FS5/D16) | `p⁵√(δ_row/d)` (D9a) | closes? |
|---|---|---|---|---|
| 4 (paper) | `p^{-7/2}` | `p^{-1}` | `p^{-1}` | yes |
| 5 | `p^{-7/2}` | `p^{-1}` (coefficient `κ₀^{-2}c₀^{17}`) | `p^{-1}` (coefficient `c₀^{17/2}`) | yes, `c₀` small after `κ₀` |
| 5.5 | `p^{-3}` | `p^{-1/2}` | `p^{-3/4}` | no |
| 6 (trivial CS, `T_v ≲ δd`) | `p^{-5/2}` | `p⁰` | `p^{-1/2}` | no |

So `T_v ≤ Kp⁵` suffices exactly because `p ≤ d^{2/17}` (`p^{17} ≤ d²`); `p^{5+ε}` does
not. With no row gain at all (`δ_row = δ`), both critical terms force
`p^{37/3} ≲ d^{4/3}`, i.e. the method would give only `γ_d² ≤ 4(d−1) + Cd^{-4/37}`.

**Elementary special case (proved).** For PSD `A, B` and real `c₁, c₂` with
`X = I + c₁A + c₂B ≻ 0`: `tr(AB X^{-1}) ≥ 0`. Proof: if `c₂ = 0` it is
`tr(B^{1/2}AX^{-1}B^{1/2})` with `X^{-1}` commuting with `A`; if `c₂ ≠ 0`, write
`c₂B = X − (I + c₁A)` (note `I + c₁A ≻ 0`), so
`c₂ tr(ABX^{-1}) = tr A − tr(A(I+c₁A)X^{-1})`; for `c₂ > 0`, `X ⪰ I+c₁A` gives
`tr(A(I+c₁A)X^{-1}) ≤ tr A`; for `c₂ < 0` the inequalities reverse. Random tests:
min normalized value `≥ 0` (`auditB_checks.py`). This proves CP *against exponential
profiles* `e^{−λq_A−μq_B}` (all real `λ, μ`), hence against completely monotone profiles
`∫e^{−λu}dm(λ)`. **It does not reach `(1−u)_+^{p−1}`**, which is not completely monotone
(it vanishes for `u ≥ 1`), and positivity of a Laplace transform does not imply positivity
of the measure.

**Perturbative route (fails).** Whitening at the typical value `q̄_A`:
`μ ∝ α^{p−1}β^{p−1}γ = N(0, Σ₀)·e^{−(p−1)(ψ(q_A)+ψ(q_B))}`, `Σ₀^{-1} = I +
2(p−1)(A/(1−q̄_A) + B/(1−q̄_B))`, `tr(ABΣ₀) ≥ 0` by the lemma above. The correction is
`|tr(AB(Σ_μ−Σ₀))| ≲ p(‖A‖+‖B‖)Θ`, while the allowed error is `Θ/p`: one needs
`‖A‖, ‖B‖ ≲ p^{-2}` (or `pΘ ≲ p^{-1}`) **pointwise**. Only `EΘ ≤ δ ≍ p^{-5/2}` is
known, and the exceptional event `{Θ > p^{-2}}` can carry the full row mass `δ ≫ δ/p`.
`‖A‖` is the compressed norm of an unshifted inverse near the spectral edge; no a priori
bound is available.

**Contact-only / bootstrap (fails).** (FS5) sums the score over the rows of *all*
neighbours `i ∈ N(v)` of the contact vertex; the sharp bound `λ ≤ Kp/d` of (D6) holds only
at the contact vertex (it uses the maximum principle (F3) there). No maximum principle is
available at the other vertices, so the GR1 information cannot come from (D6).

**Conclusion:** no route to the inequality `T_v ≤ Kp⁵` without GCI was found.

### 3.3 The GCI-free route: replace GR1 by DR1 (recommended)

Every later use of GR1 / `δ_row` (grep of the whole file):

| use | lines | what is really needed | GCI-free replacement |
|---|---|---|---|
| (W1) remainder | 840–903 | `ρ_row ≤ Kp^{-2}` | `ρ_row = K(δ + 1/d)` (B-3) |
| (FS5) score `e` | 1740–1756 | score `2pa(G⁺_ij − G⁻_ij)` at neighbours `i` | `δ_diff` from DR1 |
| (FS4) root-weight part of `S_u` | 1743–1752 | rows `G^±_vi` at `v` | `λ₁ + δ` (smaller by `√p`) |
| (CR3)/(D9a) `ρ_r` | 1170–1190, 1505–1515 | minus row at `v` in `Φ⁽⁴⁾R_v` | rewrite `R_v` (below), `δ_diff` |
| (D13) | 1943–1951 | `p³√(λ₁δ_row) = o(p^{-1})` | `δ`: `p³√(λ₁δ) = O(c₀^{17/3}p^{-2})` |

**(FS5′).** With `Δ_ij = G⁺_ij − G⁻_ij` and (W1) as in §2.4, Cauchy–Schwarz over
`(i, j, ω)`, (FS1), (I1) and DR1 at each `i ∈ N`:
```
(a/4)Σ_{i,j~i}u_iE[|F_ji| 2paH|Δ_ij|]
   ≤ (pa²/2)(Σ_{i,j}E[HF_ji²])^{1/2}(Σ_{i,j}u_i²E[HΔ_ij²])^{1/2}
   ≤ K e (√(ζ−α+β_h(q−t)+θ) + h^{3/4}),
```
with `Σ_{i,j}u_i²E[HΔ_ij²] ≤ (1/d)Σ_{i∈N}K(δ_diff/a² + ϑ) ≤ Kdδ_diff`, and
`e := (p√δ_diff + √(λ₁+δ))/(√d h) ≤ K√(pδ)/(√d h)` — the paper's `e` up to a constant.
The root-weight part uses (FS4): `Σ_{i,j}u_i²E[|∂_ijH|²/H] ≤ K(a²S⁺_v + a²S⁻_v + ϑ)
≤ K(λ₁ + δ)` (trivial (C2) bound for the minus row at `v`). Hence (FS5)–(FS7) and the
ledger entry `pe² ≤ Kκ₀^{-2}c₀^{34/3}p^{-1}` of (D16) are unchanged.

**(CR3′).** Write `R_v = (p−1)Σ_jx_j² − pΣ_jx_jz_j = pΣ_jx_j(x_j−z_j) − Σ_jx_j²`
(`x_j = G⁺_vj`, `z_j = G⁻_vj`). In `∂_i⁴(ΦR_v) = Φ⁽⁴⁾R_v + Σ_{k≥1}…`, only the first term
carries undifferentiated incident factors; with `|Φ⁽⁴⁾/Φ| ≤ Kp⁴a⁴D^C`,
`|Σ_jx_j(x_j−z_j)| ≤ (Σ_jx_j²)^{1/2}(Σ_j(x_j−z_j)²)^{1/2}` and (I1), it costs
`K{p⁵√(λ_r(δ_diff+ϑ)) + p⁴λ_r}`. The other terms are unchanged (core marks, coefficient
`Kp⁴a⁴`). So
`E_row = K{p⁵√(λ_rδ_diff) + p⁴λ_r + p⁴√(λ_cδ_c) + p^{13}/d² + e^{-3p}}`, and with
`λ_r = K(S+1)/d`, `δ_diff ≤ 2K_DRδ/p`: `p⁵√(λ_rδ_diff) ≤ KΓ√(S+1)`,
`Γ = p⁴√(pδ/d)`, `p⁴λ_r = O(p^{-7/2})`. (D9a) and the Young step at line 1987 are
unchanged; the envelope ordering `λ_r ≤ ρ_r` of (CR3) is no longer needed.

**Net effect:** GR1 and the GCI subtree are removed; DR1 (easy) is added; (W1), (FS5),
(CR3), (D13) are restated as above. Exponents and the constant ledger (D16) unchanged.

## 4. External facts: what each node uses

| node | external facts |
|---|---|
| CL (closure of C2) | (X7) Schur, C5; (X8) Jensen; C6 (which uses (X1)-type C1/C2, (X3), (X4)) |
| S1 | CL; (I1) |
| W1 | (X7) resolvent algebra; (E1′); (I1), (I2); Markov |
| WT | (X6) log-concavity; (X1) with `M = I`; (X4); (I1) |
| GR1 (paper) | (X9) GCI (Royen, monotone form); (X2); (X4); (E1) |
| DR1 (new) | (E1) only (plus C2) |

Planned facts check: (a) = (X1) is exactly what (WT3) and the (C1)/(C2) whitening need
(covariance against PSD quadratic forms; the mgf bound is not used in lines 600–1076);
(b) = (X2); (c) is the IBP identity behind (X3); (d) = (X4). The log-concavity claim
"`1{P(x)≻0} det P(x)^p` is log-concave for affine `P`" is correct (and so are the shifted
ratio and principal-minor factors used in (WT3)).

## 5. Proposed DAG for lines 600–1076 (GCI-free)

Context nodes from other audits are referred to by the paper's labels: (F2) moment caps,
(E1) endpoint calculus, (E3) score/derivative identities, (E4) comparison, (E6), (C1),
(C3), (C3b), (C5), (C6), (X1) Gaussian covariance domination, (X2) Gaussian IBP.
Difficulty: E = easy (< 150 Lean lines), M = medium (150–600), H = hard (> 600).

| id | informal statement (explicit constants as in §2) | deps | diff. |
|---|---|---|---|
| TB.par | `ε ≤ (pq)^{-1/2}`, `s ≤ 2q/(q−1)`, `L̄ ≤ 1+4/q`, `c_ij ≤ 1.01/d`, `C_v ≤ 1.03/d`, `1 ≤ D_v ≤ 2.01` for `d ≥ d_par` | — | E |
| TB.exp | at `p = ⌊c₀d^{2/17}⌋`: `p^7 ≤ d`, `p^{17} ≤ d²`, `(p/d)^{1/3} ≤ 2c₀^{17/6}p^{-5/2}`, `p ≥ L log d`, `4k_*+4 ≤ p−2`, (E6) with `c_E = 3`, all for `d ≥ d(c₀, L, K_E5)` | — | M |
| TB.I1 | interpolation with floor (§2.0) | Hölder | E |
| TB.I2 | moments of a max over `≤ d²+d+1` vertices | — | E |
| TB.E1p | `E_ξ[ξf] = E_ξ f' + R₁`, `|R₁| ≤ ‖f'''‖/3`; `R₅ ≤ (2/15)‖f⁽⁵⁾‖` | Taylor | E |
| TB.mat | `X² ⪯ h^{-1}(G−X)`, `C−C_z ⪰ zC_z²`, `(C²)[N,N] ⪰ C[N,N]²`, `(P^{-1})_{JJ} ⪰ (P_JJ)^{-1}`, `|G_ij| ≤ √(G_iiG_jj)`, resolvent derivative | Common/ | M |
| TB.CL | (CL1) for `1/d ≤ z ≤ 1`; (CL2) `t ≤ K'_CL u`; assembly of (C2) | (C6),(C3),(C3b),(C5),TB.mat,TB.par,TB.exp | M |
| TB.S1 | `t_h ≤ K_S√h`, weighted mean shift | TB.CL, TB.I1 | E |
| TB.W5 | `E[D_*^Cr_i^τ] ≤ Kh^{-1/2}` | TB.S1, TB.mat, TB.I1, TB.I2 | E |
| TB.RE | `(2p−1)a²S_v^± − 2pa²T_v = B_v^± + E3_v^±`, `|E3| ≤ K₃(p³/d+p⁵/d²)`; `B_v^± ≤ 1.03/d + 2.01ρ + Kε` | (E1),(E3),(F2),TB.par | M |
| TB.DR1 | `a²Σ_{i~v}E(G⁺_vi−G⁻_vi)² ≤ K_DR(δ/p+p²/d)` | TB.RE, (C2) | E |
| TB.W23 | exact (W2), (W3), mask derivative | TB.mat | M |
| TB.W1 | weak loop with exact score `S_f` (§2.4) | TB.W23, TB.W5, TB.E1p, TB.I1, TB.I2, (C2), fiber-regularity lemma of (E1) | H |
| TB.LC | log-concavity and evenness of `H·Φ` in the star vector | (X6) | M |
| TB.WT3 | `G[Hq_LΦ] ≤ tr L·G[HΦ]` | TB.LC, (X1) | E |
| TB.WT5 | retained-term transfer `|x_G−x|+|y_G−y| ≤ K(p⁴/d)(x+y+ϑ) + e^{-3p}` | (E4), TB.I1, TB.mat, TB.exp | H |
| TB.WT2 | `E[Hq_L] ≤ K_WT E[H tr L] + K_WTϑ + e^{-3p}` | TB.WT3, TB.WT5 | E |
| (edit) FS5′ | (FS5) with `e = (p√δ_diff + √(λ₁+δ))/(√d h)` | TB.W1, TB.DR1, (FS1), (FS4) | (Section 1.5 audit) |
| (edit) CR3′ | `E_row = K{p⁵√(λ_rδ_diff) + p⁴λ_r + p⁴√(λ_cδ_c) + p^{13}/d² + e^{-3p}}` | TB.DR1, (CR1) | (Section 1.4 audit) |
| (edit) D13′ | `Q_*/a² ≤ 2L_d[…] + Kp³√(λ₁δ)` | (C2) | (Section 1.5 audit) |
| *(optional)* TB.GR1 | paper's GR1 | TB.GCI, (E4), TB.RE | M |
| *(optional)* TB.GCI | `E_γ⟨∇α^p,∇β^p⟩ ≥ 0` via Royen (slabs) + ellipsoid approximation + layer cake | — | very H |

Parent checks to run before dispatch (workflow rule 2): (i) derive (C2) from TB.CL with
(C3), (C3b) stated; (ii) derive (FS5′) from TB.W1 + TB.DR1 + (FS1) stated; (iii) derive
(D9a) from (CR3′) + (D6); (iv) small cases: empty `N(v)` (then `S = T = 0`, DR1 trivial,
`u = 0`), one vertex, zero sources (normalized ratios = 1, physical rows 0), `t = 0`.

## 6. Numerical checks performed

* `auditB_checks.py`: (E6) constant `log 40 − 48/7 = −3.168`; every power inequality of
  the closure and of (S1) at `d = p^{17/2}`; the slack table of §3.2 and the no-gain
  exponent `4/37`; `tr(AB(I+c₁A+c₂B)^{-1}) ≥ 0` (20 000 random tests); 2-D quadrature of
  `G[q_AB α^{p−1}β^{p−1}]` for `p ∈ {3,10,40}`, scales 1–30 (all positive); concavity of
  `log det P − log det(P+h)` along random lines.
* `auditB_constants.py`: `c₂ = 1/12`, `c₃ = −1/45`, `max_{2≤j≤20}|c_j|^{1/j} = 0.386`;
  Peano constant `2/15` for (E1)'s remainder; the DR1 identity
  `S⁺+S⁻−2T = (B⁺+B⁻+E3⁺+E3⁻+2T)/(2p−1)` (sympy).
* `auditB_weak_identities.py`: (W2) residual `6e-17`, (W3) residual `4e-11`
  (finite differences, all four branch pairs).
* `auditB_condpos.py`: Monte Carlo of conditional positivity (§3.1).
