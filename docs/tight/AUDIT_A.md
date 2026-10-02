# AUDIT-A: Endpoint comparison and concentration (tex lines 237–625)

Scope: `docs/second_order_bilu_linial_tight.tex`, lines 237–625: the preamble of §"Endpoint
comparison and concentration", Lemma "Endpoint calculus" (E1, E3), the high-order comparison
(E4), the derivative accounting (E5), (E6), and Lemma "Bias and reference concentration"
(C1)–(C6), (C3a), (C3b), including its closing scalar step (lines 600–625). Lines 1–236 were
read as context. Scripts: `scripts/tight/auditA_constants.py`, `auditA_identities.py`,
`auditA_gaussian.py`, `auditA_e4cos.py`, `auditA_e6.py` (outputs in §5).

---

## 0. Summary

### 0.1 Verdict

**Correct, with fixable gaps only.** I found no false step. Every displayed inequality in lines
237–625 holds as written once its hidden hypotheses are made explicit, and all constants can be
made explicit and absolute. The open items are statement-level hypotheses, unspecified
constants, one regularity margin, notation collisions, and one place where a crude bound is not
enough and the paper's refined bound has to be kept as a node of its own. The only deep
external input is Prékopa's theorem, used once, in the form "an even log-concave perturbation
of a Gaussian has smaller covariance". I found no elementary substitute for it.

### 0.2 Gaps, with severity

| id | where | severity | issue and fix |
|----|-------|----------|---------------|
| A1 | "capped source family" (l. 244, 373) | minor (statement) | The lemma needs four hypotheses that the text leaves implicit: (M1) moments of the H-law, (M2) the first-mean cap, (M3) moments of every **own core law** ν_K up to order p/2 (used only in the averaged E4 remainders), (M4) the floor F_H ≥ 40^{-p}. Stated in §1.4. (M3) comes from the graph-order induction hypothesis together with the deletion lemma. |
| A2 | "large d", "C", "o(1)" | minor (constants) | One regime suffices for the whole section: **(R)** log d ≥ 400 and 120·log d ≤ p ≤ d^{1/7}. With p = ⌊c₀d^{2/17}⌋, (R) holds for d ≥ d₀(c₀). Explicit constants are in §0.3. All of them are absolute and are chosen before c₀ and d₀. |
| A3 | (E4) | minor | The constant C^{k+1} and the count "2^k grade compositions" are unnecessary: each remainder multi-index occurs exactly once. With \|c_j\| ≤ 1, which follows from the recursion by a three-line induction, the remainder constant is **K_E4 = 1/8 + cosh 1 − 1 < 0.67** (≤ 1/6 with the exact c_j). |
| A4 | (E4) regularity | minor | F contains α₊^{p−2}, which is only C^{p−3}. Require **4k\*+4 ≤ p−3**, which holds under (R). Then no smoothing or weak derivatives are needed. |
| A5 | (E5), retained terms | minor (proof route) | The paper's coefficient-mass induction is correct (C = 5). A **majorant lemma** (§2.4) gives C = 4 and handles the sup bounds (E5) and the sign-endpoint bounds (l. 345–361) uniformly. (E3) is then not needed for E1 or for the C-lemma. |
| A6 | (E1) | minor | Correct. Explicit route through the rank-two fibre polynomial: \|D_jG^+_{vi}\| ≤ (4pa)^j g\*^{j+1} and error ≤ **1.15·10⁹·p⁵a⁵·E g\*⁶**, where g\* = max_± max(G^±_vv, G^±_ii). |
| A7 | C4 transfer, left function F₀ (l. 509–534) | minor, but **must not be simplified** | The grade-one correction of F₀ needs the refined single-coordinate bound that separates row factors R_i = \|G⁺_vi\|+\|G⁻_vi\| from diagonal factors. The crude majorant gives only Cp⁴/d. That would yield θ ≲ p²/√d, which exceeds u = (p/d)^{1/3} by a factor ≍ c₀^{5/3}d^{1/34} → ∞ when p ≍ d^{2/17}, so the closure would lose the rate. Keep the paper's display as its own node (EPB4). |
| A8 | "high-moment interpolation" (l. 506, 531, 565, 718) | minor | Explicit lemma (INTERP, §2.8): if E X ≤ η, η ≥ 1/d and q ≥ log d, then E[XY] ≤ e·η·(E[XY^q])^{1/q}. Its use needs H-law moments of order ≤ 16(log d + 1) ≤ p/2, which (R) provides. |
| A9 | W bound (l. 562–569) | trivial | It uses ε ≥ d^{-1}, which is true (ε ≥ (2pq)^{-1/2}). Simpler to write (θ + b₀) with b₀ ≥ 1/d throughout. |
| A10 | (C6) and the scalar step | minor (statement) | Line 699 reuses them with shift h = κ₀p^{-4}. State both for **every shift z with dz ≥ 1**. The proof does not depend on z. |
| A11 | PAR facts (l. 67–68) | improvement | In regime p ≤ 2q/9 one has s ≤ 2, **L_v ≤ d a² s² ≤ 1**, c_ij ≤ 1/d, C_v ≤ 1/d and D_x ∈ [1,2] (proved in §1.2). In particular (L_v − 1)θ ≤ 0 in the scalar step. |
| A12 | zero sources (l. 74–78, 540, 692) | minor | Reduce to positive sources. A zero-source vertex is an identity row, so the law on H at y equals the law on H − {y_x = 0}, with independent uniform signs on the edges at the removed vertices (and h_x = 1 there). State every lemma for positive sources. |
| A13 | notation | minor | Symbol collisions: `t` (Z_vG_vv versus the closure supremum), `W` (weight versus trace average), `M` (three meanings), `b` (b_i versus b), `D` (y_iZ_i versus E1's D versus l. 500's D_i), `C_v` versus `C_ν`, `K` (𝓑^{-1} versus the core). Renamed in §1.6. |
| A14 | (C1) N_G ≥ 0 and the core kernel | dependency (long pole) | Needs Prékopa in arbitrary finite dimension, in the form of external fact (a). One application suffices, the whitened one: it gives N_G ≥ f_G·w, and with it N_G ≥ 0. N_G ≥ 0 **alone** also follows from Royen's inequality (GR1, next lemma) via the identity N_G = 2·𝖦[F] (checked numerically). The whitened bound N_G ≥ f_G w has no route around Prékopa that I could find (§3). |

No gap is fatal, and no statement needs weakening.

### 0.3 Explicit constants (all absolute)

Base constants (numeric):

| constant | value | where |
|----------|-------|-------|
| K_T (Peano constant of the endpoint functional) | **2/15** (kernel has one sign; `auditA_constants.py`) | E1 |
| c_j | c₀=1, c₁=0, c₂=1/12, c₃=−1/45, …; **\|c_j\| ≤ 1** for all j; \|c_{j+1}/c_j\| → 4/π² | E4 |
| K_E4 (one-coordinate remainder) | **≤ 1/8 + cosh 1 − 1 < 0.67** (proved from \|c_j\| ≤ 1); 1/6 with exact c_j | E4 |
| E5 majorant | **(4p)^n** for f₁, Φ, F, F₁…F₄; **(4p+2)^n** for F₀ | E5 |
| C_j in \|D_jG^+_vi\| ≤ C_j p^j a^j g\*^{j+1} | **4^j** | E1 |
| C_E1 | **1.15·10⁹** (times E g\*⁶ ≤ 275) | E1 |
| E6 | (C₁, C₂) = (8, 8) or any pair with 64 log C₁ + 16 log C₂ ≤ log d; bound **e^{−p}** | E6 |
| moment toolkit | ‖h‖_m ≤ 1.01, ‖G_xx‖_m ≤ 2.02, ‖U‖_m ≤ 0.52, ‖κ_i‖_m ≤ 6.4 (m ≤ p/2) | §1.5 |
| core averages | E_{ν_K}[M·Σ_{\|j\|_g=k+1} Π b_i^{j_i}] ≤ 4.1·M̄·(4.2/d)^{k+1} | CREM |
| grade-one crude factor | 1.5·(p⁴/d)·max_i E_H[m_g κ_i⁴] | HGR |
| grades ≥ 2 | Σ_{j≥2} ≤ e·‖m_g‖₂·(K_g p⁴/d)², **K_g = 6·10⁴** | HGR |
| C_C1 | **2·10⁴** | (C1) |
| C_w | **2·10³** | core kernel |
| C_Θ | **9·10⁴** (E Θ ≤ 8ρ + C_Θ b₀) | (C3b) |
| C3a tail | E[T_A 1{μ>1}] ≤ 0.52^{⌊p/4⌋} ≤ e^{−0.16p} | (C3a) |
| W bounds | E W_z ≤ 8(θ_z + ε), E[(h⁺_v + h⁻_v)W_z] ≤ 53(θ_z + b₀) | (C5)ff |

Composite constants (explicit formulas; orders of magnitude are approximate):

- K₄ (error of the C4 transfer), ≲ 10^{12}. Its coefficient of p⁵(ρ+b₀)/d is the grade-one correction of F₁…F₄, ≈ 5.4·10⁵·C_Θ ≈ 5·10^{10}. Its coefficient of p⁹/d² comes from the grades ≥ 2 of F₃, F₄ with outer factor 4p, ≈ 8·e·K_g²·‖2Θ(τ)²‖₂ ≲ 10^{12}.
- K₆ = max(8.5·10⁴, K₄).
- K_s = 2K₆ + 2 (scalar inequality).
- C_t = 2K_s + 5 (θ ≤ C_t·u).
- C_δ = 13·C_t + 4·10⁵ (δ ≤ C_δ·u).

They are crude but absolute: none depends on d, p, c₀, the graph or its order.

### 0.4 External theorems actually used (exact forms in §3)

1. **Gaussian integration by parts** on ℝ^n, for C¹ functions of polynomial growth with polynomially bounded gradient (fact (b)). Used only in the Cramér–Rao step (C4), applied to x_jΦ and x_jΦ − ∂_jΦ (needs p ≥ 3).
2. **Prékopa / midpoint Prékopa–Leindler**, through its consequence (fact (a)): for ψ even, continuous and log-concave on ℝ^n with ∫ψ dγ > 0, the probability ψγ/Z has ∫(θ·x)² ≤ \|θ\|². Applied **once**, after whitening (M = I + 2(p−1)A, ψ = e^{(p−1)(log(1−q_A)+q_A)}(1−q_B)₊^p). Dimension n = \|N(v)\| ≤ d.
3. **Rademacher-to-Gaussian comparison (E4)**, which is elementary: one-dimensional Taylor with Lagrange remainder, Gaussian moments E g^{2m} = (2m−1)!!, Fubini for the product Gaussian. This is fact (d). The one-coordinate remainder constant is < 0.67, below the coordinator's planned 2.
4. **Taylor endpoint functional** (one-dimensional Peano kernel, K_T = 2/15).
5. Elementary finite-sum inequalities: Hölder (finitely many factors), Minkowski, Cauchy–Schwarz, Jensen for 1/x, and matrix Cauchy–Schwarz (Cramér–Rao).
6. Linear algebra: Schur complement (block inverse and determinant), Loewner monotonicity of the inverse, |G_xy|² ≤ G_xxG_yy, compression (PC²P ⪰ (PCP)²), the rank-two determinant and Woodbury formulas, and trace inequalities.
7. **Not used** in lines 237–625: Brascamp–Lieb (beyond the linear-function case, which is item 2), Royen/Milman GCI (optional alternative for N_G ≥ 0 only), hypercontractivity, Chebyshev, smoothing. Fact (c), I − Cov = E∇²V − E∇V∇Vᵀ, is equivalent to the two integration-by-parts identities of the Cramér–Rao step and is needed only in that form.

### 0.5 Quantifier order (no circularity)

1. The absolute constants of this section (§0.3) are fixed first. They depend on nothing.
2. c₀ ∈ (0,1] is chosen in a later section and may depend on them.
3. d₀ is chosen last, depending on c₀, so that p = ⌊c₀d^{2/17}⌋ satisfies (R). Everything here uses only p ≤ d^{1/7}, which holds for any c₀ ≤ 1, and p ≥ 120·log d.

Inside the lemma the order is as follows:
- ρ := max(1 − E h)₊ enters the row, second-moment and core bounds.
- For any shift z with dz ≥ 1, θ_z ≥ ρ enters (C4)–(C6).
- The scalar inequality bounds θ_z, and z = u² closes the argument.

No bound is used before it is proved.

---

## 1. Setting

### 1.1 Parameters and regime

- d ≥ 3, q = d − 1, p ∈ ℕ, Δ = 4/p, R² = 4q + Δ, a = 1/R, so a² ≤ 1/(4q).
- η₀ ∈ (0,1) is the unique root of qη² + Δη − Δ = 0. Put ε := η₀/2, r := 1 + ε, τ\* := (1 − η₀)/q and s := (1 + qτ\*)/(1 − τ\*).
- u := (p/d)^{1/3}, b₀ := ε + p⁴/d + 1/d (the paper's b without its C), k\* := ⌈16p/log d⌉.

**Regime (R):** log d ≥ 400 and 120·log d ≤ p ≤ d^{1/7}.

**REG (consequences of (R)), checked in `auditA_e6.py` and by hand:**
- p ≤ 2q/9.
- k\* ≤ p/25 + 1, hence 8k\* + 12 ≤ p/2 and 4k\* + 4 ≤ p − 3.
- 32(log d + 1) ≤ p/2. This covers the moment orders ≤ 16(log d + 1) used by INTERP.
- e^{−p} ≤ d^{−120}.
- p⁴/d ≤ d^{−3/7} ≤ e^{−171}.
- Closure inequalities: p⁴/d ≤ u, p⁵/d ≤ u (equivalent to p⁷ ≤ d), ε ≤ u, 1/d ≤ u², p²/d ≤ u² (p⁴ ≤ d), p⁹/d² ≤ u² (p ≤ d^{4/25}), e^{−p} ≤ u². Hence **b₀ ≤ 3u**.

### 1.2 Source and parameter facts (PAR′), regime p ≤ 2q/9 and q ≥ 6

These refine lines 67–68. The proofs are short real inequalities.

1. **η₀ bounds.** qη₀² = Δ(1−η₀) ≤ Δ gives η₀ ≤ 2(pq)^{−1/2}, so ε ≤ (pq)^{−1/2}. If η₀ ≤ 1/2 then qη₀² ≥ Δ/2, so η₀ ≥ (2/(pq))^{1/2} ≥ 3/q. In either case **η₀ ≥ 3/q**. Also ε ≥ (2pq)^{−1/2} ≥ 1/d.
2. **Key identity.** a²s² = τ\*/(1−τ\*)². This is equivalent to the definition of η₀: q(2−η₀)² = (1−η₀)(4q+Δ) ⇔ qη₀² = Δ(1−η₀). Since c(1+c) is increasing, c_ij(1+c_ij) = a²y_iy_j ≤ a²s² gives **τ_ij ≤ τ\***.
3. **s ≤ 2**, which is equivalent to η₀ ≥ 2τ\* and implied by η₀ ≥ 2/q.
4. **d a² s² = (q+1)q(1−η₀)/(q−1+η₀)² ≤ 1**, which is equivalent to q²η₀ − 3q(1−η₀) + (1−η₀)² ≥ 0 and implied by η₀ ≥ 3/q.
5. **Degree-sum quantities.** c_ij ≤ a²y_iy_j ≤ a²s² ≤ 1/d. L_v := a²y_vΣ_{i∼v}y_i ≤ 1. C_v := Σ_i c_vi² ≤ 1/d. D_v := y_vZ_v = 1 + Σ_i c_vi = 1 + L_v − C_v ∈ [1, 2], using c = a²y_vy_i − c². Also 1/Z_v ≤ y_v ≤ 2.
6. **U₀ := L_v/D_v ≤ 1/(2 − 1/d) ≤ 0.51** for d ≥ 50, because x ↦ x/(1+x−c) is increasing.

Numerical check: `auditA_constants.py` §5 finds no failure on a (d,p) grid with p ≤ 2q/9.

### 1.3 The paired law and the root insertion

Graph H = (V,E) with max degree ≤ d. Diagonals Z^± = Z(y^±) with y^± ∈ (0,s]^V (see A12 for zero sources).

- For σ ∈ {±1}^E: P^±(σ) = diag Z^± ± aA_σ and W_H(σ) = 1[P⁺≻0, P⁻≻0]·(det P⁺ det P⁻)^p.
- E_H[g] = Σ_σ W_H g / Σ_σ W_H. This is the paper's E and "actual law".
- G^± = (P^±)^{-1}, h_x^± = G^±_xx/y^±_x, and **τ_x^± := Z_x^±G^±_xx = D_x^±h_x^±** (the paper's t and t_ν).

Root v, N = N_H(v), K = V∖{v} (the paper's K = H − v), σ = (σ_K, ξ) with ξ ∈ {±1}^N.

- **Own core law ν_K:** the paired law of H[K] with the inherited diagonals Z^±|_K. By lem:fw-deletion this equals the law of H − v at deletion sources ŷ ≤ y.
- C_± := G_K^± = (P^±_{−v})^{-1}.
- A = (a²/Z_v⁺)G_K⁺[N,N] and B = (a²/Z_v⁻)G_K⁻[N,N] are PSD and depend on σ_K only.
- q_M(x) = xᵀMx, α = (1−q_A)₊, β = (1−q_B)₊, Φ = α^pβ^p on x ∈ ℝ^N.
- 𝖱 = 2^{−|N|}Σ_{ξ∈{±1}^N}, 𝖦 = ∫ dγ_N, f = 𝖱Φ, f_G = 𝖦Φ, F_H = E_{ν_K} f.
- b_i = A_ii + B_ii, μ₀ = tr(A+B), μ = tr A, T_A = tr A², w = T_A/(1+μ), Θ = tr(A² + B²).

**INS (lines 125–141, all exact):**
- (i) W_H(σ_K, ξ) = (Z_v⁺Z_v⁻)^p W_K(σ_K)Φ(ξ), and P_H^± ≻ 0 ⇔ P_K^± ≻ 0 ∧ α(ξ), β(ξ) > 0. Hence **E_H[g] = E_{ν_K}[𝖱(Φ g)]/F_H**.
- (ii) **F1.** At Φ(ξ) > 0: τ_v⁺ = 1/α, τ_v⁻ = 1/β, G⁺_vi = −(Aξ)_i/(aα) and G⁻_vi = (Bξ)_i/(aβ).
- (iii) G^±_ii = G^±_{K,ii} + (G^±_vi)²/G^±_vv, so G_{K,ii} ≤ G_ii (Schur order). Also A_ij/α(ξ) = a²G⁺_vvG⁺_{K,ij}.

Checked by exact enumeration (`auditA_identities.py` I1).

### 1.4 Hypotheses "capped source law" (CSL), at given (H, y⁺, y⁻)

- (M0) Σ_σ W_H > 0.
- (M1) E_H(h_x^±)^k ≤ (1+2ε)^k for all x ∈ V, both signs and 1 ≤ k ≤ p/2. This follows from F2 with B₀ = r, since (pr−k)/(p−k) ≤ 1 + 2ε for k ≤ p/2.
- (M2) E_H h_x^± ≤ r = 1 + ε for all x (the cap).
- (M3) For every root v: Σ W_K > 0 and E_{ν_K}(G^±_{K,ii})^k ≤ (2(1+2ε))^k for all i ∈ K and k ≤ p/2. This follows from F2 for H − v at ŷ ≤ y ≤ s, i.e. from the induction hypothesis together with deletion.
- (M4) F_H ≥ 40^{−p} for every root v (lem:fw-floor).

### 1.5 Moment toolkit (MT), from CSL + PAR′ + (R), for m ≤ p/2

- ‖h_x‖_m ≤ 1.01 and ‖G_xx‖_m ≤ 2.02.
- g_x := G⁺_xx + G⁻_xx has ‖g_x‖_m ≤ 4.04.
- ‖τ_v‖_m ≤ 2.02.
- U := (a²/Z_v)Σ_{i∈N}G_ii ≥ μ has ‖U‖_m ≤ 0.51·1.01 ≤ 0.52 (Minkowski).
- ‖μ₀‖_m ≤ 1.04.
- Θ ≤ μ₀², so ‖Θ‖_m ≤ 1.09 for 2m ≤ p/2.
- **κ_i := (2(1+g_v)g_i)^{1/2}** has ‖κ_i‖_m ≤ (2·5.04·4.04)^{1/2} ≤ 6.4.
- Under ν_K: b_i ≤ (2/(4q))(G⁺_{K,ii}+G⁻_{K,ii}), so ‖b_i‖_{ν_K,m} ≤ 2.1/d and ‖μ₀‖_{ν_K,m} ≤ 2.1.

### 1.6 Renamings used below (A13)

| paper | here |
|-------|------|
| t (l. 351) and t_ν (l. 497) | τ_v^± = Z_v^± G^±_vv |
| t (l. 444, closure) | θ_z = max_{i,±}(1 − E X^±_{z,ii}/y^±_i)₊ |
| W (l. 544) | W_z |
| M (l. 274) | M_E1 |
| M (l. 452) | M_z = (a²/Z_v⁺)C_{z,+}[N,N] |
| b (l. 400) | b₀ (constants written explicitly) |
| D (l. 274) | D_E1, or g\* |
| D_i (l. 500) | κ_i |

---

## 2. Claim-by-claim audit

### 2.1 Preamble (lines 239–259)

- "The source maximum bounds the L^j norms of physical diagonals and of Z_iG_ii = D_ih_i by an absolute constant for j ≤ p/2." **OK**, see MT: Z_iG_ii = D_ih_i ≤ 2h_i.
- "all moments of order 8k\*+12 used below are available for large d". **OK** under (R) (REG).
- Definitions of A, B, α, β, Φ, ν_K, F_H, f, q_M, b_i and μ₀ are as in §1.3. The identity "actual core marginal = (f/F_H)·ν_K" is INS(i). **OK.**

### 2.2 Lemma "Endpoint calculus": (E3) and (E1)

**(E3), restated.** Let P^±(s) be P^± with the sign of edge vi replaced by s ∈ ℝ, the diagonal held fixed. Wherever P^±(s) ≻ 0:

∂_s G^±_{jl} = ∓a(G^±_{jv}G^±_{il} + G^±_{ji}G^±_{vl}) and ∂_s log W = 2pa(G⁺_vi − G⁻_vi).

**OK**: derivative of the inverse and Jacobi's formula, tr(G^±E) = 2G^±_vi with E = e_ve_iᵀ + e_ie_vᵀ. Verified by finite differences (I3, error 2·10^{−32}).

**Rank-two fibre formula (RANK2), recommended instead of (E3).** For symmetric P ≻ 0 with G = P^{-1} and P(t) = P + taE:

- det P(t) = det P · δ(t), with δ(t) = 1 + 2taG_vi − t²a²(G_vvG_ii − G_vi²).
- G(t)_vi = (G_vi − ta(G_vvG_ii − G_vi²))/δ(t).
- G(t)_vv = G_vv/δ(t) and G(t)_ii = G_ii/δ(t).

The minus branch is the same with t ↦ −t. Checked symbolically in `auditA_constants.py` §6.

Hence on a fibre segment that is good throughout, with t = s − σ_vi:

φ(s) := W(s)G⁺(s)_vi = W(σ)·Π(t),   Π(t) = δ₊(t)^{p−1}δ₋(t)^p·(G⁺_vi − ta(G⁺_vvG⁺_ii − (G⁺_vi)²)).

Π is a polynomial of degree ≤ 4p−1. Coefficientwise, δ_± ≪ (1 + ag\*r)², and the last factor is ≪ g\*(1 + ag\*r), where g\* := max_± max(G^±_vv, G^±_ii). Therefore

**|Π^{(j)}(t)| ≤ (4p)^j a^j g\*^{j+1}(1 + ag\*|t|)^{4p−1−j}**.

In particular **D_jG⁺_vi := Π^{(j)}(0) satisfies |D_jG⁺_vi| ≤ (4pa)^j g\*^{j+1}**, which is the paper's |D_jG⁺_vi| ≤ C_j p^j a^j D^{j+1} with C_j = 4^j and g\* ≤ D. Explicitly,

D₁G⁺_vi = −aG⁺_vvG⁺_ii + (2p−1)a(G⁺_vi)² − 2paG⁺_viG⁻_vi.

D₃ is obtained the same way, by expanding Π.

**Taylor endpoint functional (TAY5).** For φ ∈ C⁵[−1,1] put

L(φ) = (φ(1)−φ(−1))/2 − (φ′(1)+φ′(−1))/2 + (φ‴(1)+φ‴(−1))/6.

L vanishes on polynomials of degree ≤ 4 ("exact through degree four": **OK**), and **|L(φ)| ≤ (2/15)·sup|φ^{(5)}|**. The Peano kernel K(u) = (1−u)⁴/48 − (1−u)³/12 + (1−u)/6 has one sign on [−1,1] and integral 2/15; check L(x⁵) = 16 = 120·(2/15).

**(E1), restated.** Assume (M0), H any graph, vi an edge, and σ_vi the corresponding sign. Then

|E_H[σ_vi G⁺_vi] − E_H[D₁G⁺_vi] + (1/3)E_H[D₃G⁺_vi]| ≤ 1.15·10⁹·p⁵a⁵·E_H[g\*⁶],

with the law's own normalizer and no insertion factor (**OK**, as claimed). Under (M1), E_H g\*⁶ ≤ Σ E(G^±_xx)⁶ ≤ 4·2.02⁶ ≤ 275.

*Proof.* Split fibres {ξ_i = ±1} with the other signs fixed. Call an endpoint *small* if it is good and g\* ≤ 1/(64pa) (the paper's M/2 with M = 1/(32pa)).

- **Case A: the fibre has a small endpoint σ.** For |t| ≤ 2, δ_±(t) ≥ 1 − 4ag\* − 4a²g\*² ≥ 1/2. The determinant never vanishes, so the whole segment is good and both endpoints are good. Then Σ_fibre[σ_viWψ − W(D₁ψ − D₃ψ/3)] = 2L(φ). Also |φ^{(5)}| ≤ W(σ)(4pa)⁵g\*⁶(1+2ag\*)^{4p} ≤ e^{1/8}(4pa)⁵g\*(σ)⁶W(σ). The fibre therefore contributes at most 310·p⁵a⁵·W(σ)g\*(σ)⁶.
- **Case B: no small endpoint.** Every good endpoint has g\* > 1/(64pa), so (64pag\*)^{5−j} ≥ 1. Bound each term separately: |ψ| ≤ g\*, |D₁ψ| ≤ 4pag\*² and |D₃ψ|/3 ≤ (4pa)³g\*⁴/3. Multiplying by (64pag\*)^{5−j} gives a total of (64⁵ + 4·64⁴ + 4³·64²/3)p⁵a⁵g\*⁶ ≤ 1.15·10⁹p⁵a⁵g\*⁶ per endpoint.

Bad endpoints have weight 0. Summing and dividing by Σ W_H gives the claim. ∎

**Status: OK.** The paper's version (D = the sum of four diagonals, G(s) ⪯ 2G(ξ), W(s) ≤ e^{1/16}W(ξ)) is also correct: the rank-two relative perturbation is ≤ 2aD ≤ 1/(32p) and W(s)/W(ξ) ≤ e^{2paD} ≤ e^{1/32}. The fibre-level identity and the bound were checked by exact enumeration with mpmath derivatives (I4: max |L(φ)|/sup|φ^{(5)}| = 0.086 ≤ 2/15).

### 2.3 The coefficients c_j and the high-order comparison (E4)

**CJ.** Define c_j by the recursion Σ_{j=0}^m c_j/(2m−2j)! = 1/(2^m m!). This is equivalent to e^{t²/2}/cosh t = Σ c_j t^{2j}, so no power series is needed in Lean. Then:

- c₀ = 1, c₁ = 0, **c₂ = 1/12** (**OK**), c₃ = −1/45, c₄ = 103/10080.
- **|c_j| ≤ 1 for all j.** By induction, |c_m| ≤ 1/(2^m m!) + Σ_{k≥1}1/(2k)! ≤ 1/8 + (cosh 1 − 1) < 0.67 for m ≥ 2. So the paper's |c_j| ≤ C^j holds with C = 1.
- The true size is |c_j| ≍ (4/π²)^j: the singularity of 1/cosh is at ±iπ/2.

**One coordinate (GS1).** Let L ≥ 0 and f ∈ C^{2L+4}(ℝ) with |f^{(2L+4)}| ≤ B on ℝ (hence of polynomial growth). Then

|𝖦f − Σ_{j∈J_L} c_j·(f^{(2j)}(1) + f^{(2j)}(−1))/2| ≤ K_L·B,

where J_L = {0, 2, 3, …, L+1} and K_L = 1/(2^{L+2}(L+2)!) + Σ_{j∈J_L}|c_j|/(2L+4−2j)! ≤ 1/8 + cosh 1 − 1 < 0.67. Numerically sup_L K_L = K₀ = 1/6.

*Proof.*
- The identity is exact for polynomials of degree ≤ 2L+3: the coefficient of t^{2m} in cosh t·Σc_jt^{2j} = e^{t²/2} is Σ_j c_j/(2m−2j)! = 1/(2^m m!), and m ≤ L+1 needs only j ≤ L+1.
- For the remainder r = f − T_{2L+3}: |r^{(2j)}(x)| ≤ B|x|^{2L+4−2j}/(2L+4−2j)!, and E|g|^{2L+4}/(2L+4)! = 1/(2^{L+2}(L+2)!). ∎

Grade bookkeeping: derivative order 2j costs grade j − 1, and order 2L+4 is grade L+1. **OK.**

**Several coordinates (GSM), restated.**

- Multi-indices j : N → ℕ with j_i ∈ {0} ∪ {2,3,…}. S(j) = {j_i > 0}, l = |S(j)|, grade |j|_g = Σ_{S}(j_i − 1), c_j = Π_S c_{j_i}, ∂^{2j} = Π_S ∂_i^{2j_i}. The order is 2|j|_g + 2l ≤ 4|j|_g.
- Let f ∈ C^{4k+4}(ℝ^N) with every partial derivative of order ≤ 4k+4 bounded. Then

𝖦f = Σ_{|j|_g≤k} c_j 𝖱∂^{2j}f + 𝓔_k(f),   |𝓔_k(f)| ≤ K_E4·Σ_{|j|_g=k+1} sup_{ℝ^N}|∂^{2j}f|.

*Proof.* Enumerate N. Apply GS1 in coordinate m to x_m ↦ ∂^{2j_{<m}}f with budget L = k − |j_{<m}|_g; the other coordinates are already signs (finite average) or still Gaussian (Fubini). The remainder of the term with prefix j_{<m} has multi-index (j_{<m}, k − |j_{<m}|_g + 2 at m), of grade exactly k + 1. This map is a **bijection** onto {|j|_g = k+1} (m is the last active coordinate), and |c_{j_{<m}}| ≤ 1. ∎

- "every derivative has order at most 4k+4", "distinct active coordinates", "first remainder has exact total grade k+1": **OK**.
- "number of grade compositions is at most 2^k": unnecessary (A3).
- "also for bounded weak highest derivatives by smoothing": not needed if 4k\*+4 ≤ p−3 (A4).

Tests: `auditA_e4cos.py` covers f = cos⟨λ,x⟩ in 1–3 coordinates for k ≤ 6, with error/bound ≤ 0.085. `auditA_gaussian.py` G4 covers a clipped power in 2 coordinates. **Status: OK.**

### 2.4 Derivative accounting (E5) through a majorant lemma

**MAJ (majorant lemma).** Let S be finite, λ ∈ [0,∞)^S, and P₁,…,P_K polynomials of degree ≤ 2 on ℝ^S with |P_k(0)| ≤ m_k, |∂_iP_k(0)| ≤ 2m_kλ_i and |∂_i∂_jP_k(0)| ≤ 2m_kλ_iλ_j (including i = j). Then for |ν| = n and h ∈ ℝ^S:

|∂^ν(Π_kP_k)(h)| ≤ (Π m_k)·(2K)^{(n)}·λ^ν·(1 + Σλ_i|h_i|)^{2K−n} ≤ Πm_k·(2K)^n·λ^ν·(1+Σλ_i|h_i|)^{2K}.

Here (2K)^{(n)} is the falling factorial.

*Proof.* Coefficientwise, P_k ≪ m_k(1+Σλ_ih_i)²: constant m_k, linear 2m_kλ_i, coefficient of h_ih_j (i<j) 2m_kλ_iλ_j and of h_i² m_kλ_i². Majorants multiply, and ∂^ν(1+Σλh)^{2K} = (2K)^{(n)}λ^ν(1+Σλh)^{2K−n}. ∎

**CLIP.** t ↦ t₊^m is C^{m−1}, and its derivatives of order < m vanish at t ≤ 0. Hence Q·α₊^{e₁}β₊^{e₂} with Q polynomial is C^{min(e₁,e₂)−1}. Its derivatives of order ≤ min(e₁,e₂)−1 are polynomial on U = {q_A<1, q_B<1} and vanish off U.

**(E5), restated (sup bounds).** Let A, B ⪰ 0 on N, 0 ⪯ M′ ⪯ A, and n ≤ p−3. For all x ∈ ℝ^N and |ν| = n:

| observable | sup\|∂^ν\| ≤ |
|------------|--------------|
| f₁ = (trA − q_A)α^{p−1}β^p | (1+μ₀)(4p)^n Π b_i^{ν_i/2} |
| Φ | (4p)^n Π b_i^{ν_i/2} |
| F = (p−1)q_{A²}α^{p−2}β^p + p q_{AB}α^{p−1}β^{p−1} | (2p−1)μ₀(4p)^n Π b_i^{ν_i/2} |
| F₀ = (trM′ − q_{M′})Φ | (1+μ)(4p+2)^n Π b_i^{ν_i/2} |
| F₁, F₂ = tr(M′A)α^{p−1}β^p, tr(M′B)α^pβ^{p−1} | Θ(4p)^n Π b_i^{ν_i/2} |
| F₃, F₄ = q_{AM′A}α^{p−2}β^p, q_{BM′B}α^pβ^{p−2} | Θ(4p)^n Π b_i^{ν_i/2} |

The paper has (Cp)^n(2+μ₀) for f₁ and p(Cp)^nμ₀ for F; the bounds above are slightly better.

*Proof.*
- At x ∈ U, apply MAJ in h_i = s_i/√b_i. When b_i = 0 the observable does not depend on x_i and both sides vanish.
- Factors α(x+h): constant α(x) ≤ 1; linear coefficient 2|(Ax)_i| ≤ 2√(A_ii q_A(x)) ≤ 2√b_i; quadratic |A_ij| ≤ √(b_ib_j).
- Prefactors: |trA − q_A(x)| ≤ 1 + μ₀. For q_{A²}: |Ax|² ≤ ‖A‖ ≤ μ₀, |(A²x)_i| ≤ ‖A‖√A_ii and |(A²)_ij| ≤ ‖A‖√(A_iiA_jj). For q_{AB}, the same with ‖A‖‖B‖ ≤ μ₀²/4. For q_L with L ⪯ ΘA: q_L ≤ Θq_A ≤ Θ, |(Lx)_i| ≤ Θ√A_ii and |L_ij| ≤ Θ√(A_iiA_jj).
- Count of quadratic factors: 2p for f₁ and Φ; 2p+1 for F₀; 2p−1 for F (with α^{p−2}), F₁, F₂, F₃, F₄. The derivative factor is (2·count)^n, i.e. at most (4p+2)^n.
- Off U: CLIP.

The paper's "coefficient mass grows by at most 4p+n+1" is also correct and gives (5p)^n for n ≤ p. "The quadratic prefactors … and their first two normalized derivatives are bounded": **OK**. Numerical check G5: max ratio 0.014 against the (5p)^n(2+μ₀) normalisation. **Status: OK.**

### 2.5 Averaged remainders (lines 337–343), CREM

**Statement.** Assume CSL (M3), and let k satisfy 2k+3 ≤ p/2. Let M ≥ 0 be core-measurable with M̄ := max_{m≤p/2}‖M‖_{ν_K,m}. Then

E_{ν_K}[M·Σ_{|j|_g=k+1}Π_i b_i^{j_i}] ≤ 4.1·M̄·(4.2/d)^{k+1}.

*Proof.*
- Hölder with J+1 factors, where J = Σj_i = k+1+l ≤ 2k+2, using ‖b_i‖ ≤ 2.1/d.
- The number of j with given l is ≤ C(d,l)·C(k,l−1).
- Σ_l(2.1/d)^{k+1+l}(d^l/l!)C(k,l−1) ≤ (2.1/d)^{k+1}2^ke^{2.1}. ∎

Combined with (E5) and GSM, using M̄ = max‖1+μ₀‖_{ν_K} ≤ 3.1: E_{ν_K}|𝓔_k(f₁)| ≤ 0.67·(4p)^{4k+4}·4.1·3.1·(4.2/d)^{k+1}. This matches the paper's "(Cp)^{4k+4}d^{−k−1}". **OK.** Note that this is the only place where the own core law enters (A1).

### 2.6 Retained terms at sign endpoints (lines 345–361), EPB / EPB4 / HGR

**EPB (all grades, crude).** At a sign endpoint ξ with Φ(ξ) > 0, write everything relative to α(ξ), β(ξ). By F1:

- α(ξ+h)/α(ξ) = 1 + 2aΣG⁺_vih_i − a²G⁺_vvΣ_{ij}G⁺_{K,ij}h_ih_j.
- β(ξ+h)/β(ξ) is the same with G⁻ and with the sign of the linear term flipped.

These satisfy MAJ with m = 1 and λ_i = aκ_i, because κ_i ≥ √(G_vvG_ii) and κ_iκ_j ≥ G_vv√(G_iiG_jj) ≥ G_vv|G_{K,ij}|. The prefactors satisfy MAJ with:

- m = 1 + (trA+1)τ_v⁺ for (trA − q_A)/α(ξ), since F1 gives the constant term 1 + (trA−1)τ_v⁺;
- m = μ + 1 for trM′ − q_{M′};
- m = Θτ⁺ for tr(M′A)/α;
- m = 2Θ(τ⁺)² for q_{AM′A}/α².

These use √A_ii ≤ a√(2G_ii) ≤ aκ_i and |L_ij| ≤ 2Θa²κ_iκ_j. Hence, for every root observable gΦ in the list of §2.4,

|∂^ν(gΦ)(ξ)|/Φ(ξ) ≤ m_g·(4p+2)^n·a^n·Π κ_i^{ν_i}.

This is the paper's "coefficient mass (Cp)^n, a factor a^n, inverse-entry degree n". The identity (trA − q_A)α^{p−1}β^p/Φ = 1 + (trA − 1)τ⁺ (l. 350) is **OK**, as are ∂_iτ⁺ = −2aτ⁺G⁺_vi and trA ≤ Ca²ΣG⁺_ii (Schur order, C = 2).

**HGR (H-law averages).** Under CSL and (R), for 1 ≤ j ≤ k\*:

- Σ_{|j|_g=j} |c_j|·|E_H[∂^{2j}(gΦ)/Φ]| ≤ (e/2)‖m_g‖₂(K_g p⁴/d)^j with **K_g = 6·10⁴**.
- Grade one: Σ_{i∈N}(1/12)E_H|∂_i⁴(gΦ)|/Φ ≤ **1.5·(p⁴/d)·max_i E_H[m_g κ_i⁴]**.
- Σ_{j=2}^{k\*} ≤ e·‖m_g‖₂·(K_gp⁴/d)².

*Proof.*
- Hölder: ‖Π_i κ_i^{ν_i}‖₂ ≤ Π‖κ_i‖_{2n}^{ν_i} ≤ 6.4^n, with moments of order 2n ≤ 8j ≤ p/2. This is the paper's "moments at most 8j+4".
- Count C(d,l)C(j−1,l−1) and a² ≤ 1/(4q).
- Σ_{l≤j}(dx)^l/l! ≤ e(dx)^j with x = (4.1·6.4·p·a)². ∎

"Diagonal moments then bound a retained grade-j term by (Cp)^{4j}d^{−j}": **OK** (C⁴ = K_g). "All derivatives vanish at excluded endpoints, so passing to the actual law is exact": **OK**, by CLIP (orders ≤ 4k\*+2 ≤ p−3) and INS(i).

**EPB4 (refined, single coordinate, for F₀ and any observable needing row factors).** Fix i ∈ N and put

- r := a(|G⁺_vi| + |G⁻_vi|) = aR_i,
- ω := a²(G⁺_vvG⁺_ii + G⁻_vvG⁻_ii),
- m₀, m₁, m₂ := bounds on the coefficients of the prefactor in h (for F₀: m₀ ≤ μ+1, m₁ ≤ 2√2·a√G_ii, m₂ ≤ 2a²G_ii).

Then

|∂_i^k(gΦ)(ξ)|/Φ(ξ) ≤ k!·[h^k](m₀ + m₁h + m₂h²)(1 + 2rh + ωh²)^{2p}.

The reason: (1+2r₊h+ω₊h²)(1+2r₋h+ω₋h²) ≪ (1+2rh+ωh²)². For k = 4 this is exactly the paper's display (l. 515–527):

|∂_i⁴F₀|/Φ ≤ 24{m₀[(4pr)⁴/24 + 4(2p)³r²ω + 2(2p)²ω²] + m₁[(4pr)³/6 + 4(2p)²rω] + m₂[(4pr)²/2 + 2pω]}
  ≲ a⁴(1+μ)·g-polynomial·{p⁴R_i⁴ + p³(R_i² + R_i³) + p²(1 + R_i + R_i²)}.

**OK** (A7: necessary).

### 2.7 (E6)

**Statement.** If L := log d ≥ 400, 64 log C₁ + 16 log C₂ ≤ L and 120L ≤ p ≤ d^{1/7}, then

p·40^p·(C₁p)^{4k\*+4}·C₂^{k\*+1}·d^{−k\*} ≤ e^{−p}.

*Proof.*
- 4 log(C₁p) + log C₂ − L ≤ 4 log C₁ + log C₂ − 3L/7 < 0, so k\* ≥ 16p/L may be used.
- log LHS ≤ 5 log p + 4 log C₁ + log C₂ + p[log 40 + (64 log C₁ + 16 log C₂)/L − 48/7].
- The bracket is ≤ 3.689 + 1 − 6.857 = −2.168, and 5 log p + L/16 ≤ 1.168p. ∎

The paper's "logarithm at most [log 40 − 16(1−4/7) + o(1)]p" is **OK**; the o(1) is (64 log C₁ + 16 log C₂)/L + O(log p/p). `auditA_e6.py` samples p ∈ [120L, d^{1/7}]: with (C₁, C₂) = (8,8) the margin is ≤ −1.6p for L ≥ 300, and the binding constraint for L ≈ 256 is 8k\*+12 ≤ p/2, not E6. **Status: OK.**

### 2.8 Generic transfer and interpolation (used by C1, CK, C4T and later sections)

**TRANS.** Assume CSL and (R), and let gΦ be a root observable with sup-majorant M_g (§2.4) and endpoint majorant m_g (§2.6). Then

|E_{ν_K}(𝖱[gΦ] − 𝖦[gΦ])/F_H + Σ_{i∈N} c₂E_H[∂_i⁴(gΦ)/Φ]| ≤ e‖m_g‖₂(K_gp⁴/d)² + M̄_g·e^{−p}/(p d).

*Proof.*
- GSM with k = k\*. The retained terms equal E_H[∂^{2j}(gΦ)/Φ] by INS(i) and CLIP.
- Grades 2…k\* are bounded by HGR.
- The remainder is bounded by (M4), CREM and (E6) with (8,8): 40^p·0.67·4.1·(4p)^{4k+4}(4.2/d)^{k+1} ≤ (1/30)·40^p(8p)^{4k+4}8^{k+1}d^{−k}/d, valid for k ≥ 2 (k\* ≥ 16·120 under (R)). ∎

**INTERP.** For X, Y ≥ 0 and q ≥ 1, E[XY] ≤ (EX)^{1−1/q}(E[XY^q])^{1/q} (Hölder). If moreover EX ≤ η with η ≥ 1/d and q ≥ log d, then **E[XY] ≤ e·η·(E[XY^q])^{1/q}**.

### 2.9 (C1)

**(C1a), restated.** Under CSL and (R), for every root v:

|E_{ν_K}(N_R − N_G)/F_H| ≤ **2·10⁴·p⁴/d**,

where N_R := 𝖱[f₁], N_G := 𝖦[f₁] and f₁ = (trA − q_A)α^{p−1}β^p.

*Proof.* TRANS with m_{f₁} = 1 + (trA+1)τ⁺, so ‖m‖₂ ≤ 1 + 1.52·2.02 ≤ 4.1. Grade one gives ≤ 1.5·4.1·6.4⁴·p⁴/d ≤ 1.04·10⁴p⁴/d; grades ≥ 2 and the remainder are ≤ p⁴/d by REG. ∎

"grade one costs Cp⁴/d, higher grades … Cp⁸/d², only floor loss exponentially small": **OK.**

**(C1b), restated (stronger than N_G ≥ 0).** For PSD A, B on N and p ≥ 2,

**N_G ≥ f_G·w ≥ 0**, with f_G = 𝖦Φ and w = T_A/(1+μ).

*Proof.*
- On U, α^{p−1} = e^{−(p−1)q_A}·e^{(p−1)φ(q_A)} with φ(u) = log(1−u) + u, which is concave and nonincreasing on [0,1). So ψ := e^{(p−1)φ(q_A)}β^p·1_U is even, continuous and log-concave, and α^{p−1}β^pγ ∝ ψ·γ_{M^{−1}} with M = I + 2(p−1)A.
- PREK (§3) gives Cov ⪯ M^{−1}. Evenness gives mean 0.
- So N_G = Z′·tr(A(I − Cov)) ≥ Z′·tr(A(I − M^{−1})) = Z′·2(p−1)tr(A²(I+2(p−1)A)^{−1}) ≥ Z′·2(p−1)T_A/(1 + 2(p−1)‖A‖), where Z′ = 𝖦[α^{p−1}β^p] ≥ f_G.
- Finally c ↦ c/(1+c‖A‖) is increasing, c = 2(p−1) ≥ 1, and ‖A‖ ≤ μ, so the last expression is ≥ f_G·w. ∎

The paper's derivation (l. 393–397 and 417–422) is **OK**. The unwhitened statement N_G ≥ 0 is implied, so only the whitened application of Prékopa is needed. Numerical check G1: min(N_G − f_Gw) = 0.02 > 0 over 25 random 2-D instances.

**Identity (optional).** N_G = 2𝖦[F] with F as in (E5): Gaussian integration by parts gives N_G = −𝖦[(Ax)·∇(α^{p−1}β^p)]. Checked to 4·10^{−14} (G2, p ≥ 5). Hence N_G ≥ 0 also follows from Royen's 𝖦[q_{AB}α^{p−1}β^{p−1}] ≥ 0 (GR1); this route is not enough for CK.

### 2.10 (C3), the row bound, second moments

**(C3), restated (exact, any H and v with (M0)).**

E_{ν_K}N_R/F_H = 1 − D_vE_Hh_v⁺ + a²Σ_{i∼v}E_H(G⁺_vvG⁺_ii − (G⁺_vi)²).

*Proof.* By INS(i) it equals E_H[1 + (trA−1)τ⁺]. Then τ⁺ = D_vh_v and trA·τ⁺ = a²G⁺_vvΣG⁺_{K,ii} = a²Σ(G_vvG_ii − G_vi²) by INS(iii). ∎

Checked by exact enumeration (I2, difference 1.4·10^{−16}). The minus branch is analogous, with (trB − q_B)α^pβ^{p−1}.

**ROW, restated.** Under CSL and (R), for every v and both signs:

a²Σ_{i∼v}E_H(G^±_vi)² ≤ 2ρ + 5ε + 1/d + C_C1·p⁴/d ≤ 2ρ + 2·10⁴b₀,   ρ := max_{x,±}(1 − E_Hh_x^±)₊.

*Proof.* (C1a) and (C1b) give E_{ν_K}N_R/F_H ≥ −C_C1p⁴/d. In (C3):

- E G_vvG_ii ≤ y_vy_i(1+2ε)² (Cauchy–Schwarz and (M1));
- −D_vEh_v ≤ −D_v(1−ρ);
- 1 − D_v + L_v = C_v ≤ 1/d, D_v ≤ 2 and L_v ≤ 1 (PAR′). ∎

The paper writes C(ρ+b); **OK**.

**SM2.** E_H(h_x^± − 1)² ≤ (1+2ε)² − 2(1−ρ) + 1 ≤ **5ε + 2ρ**. The paper writes Cε + 2ρ; **OK**.

### 2.11 Core kernel, (C3a), (C3b)

**CK.** Under CSL and (R),

E_H[w] ≤ 2ρ + 5ε + 1/d + (C_C1 + C_w)p⁴/d, with C_w = 2·10³.

*Proof.*
- TRANS on wΦ, with m = w and ‖w‖₂ ≤ 0.52, gives |E_{ν_K}w(f_G − f)/F_H| ≤ C_wp⁴/d. That is, E_{ν_K}[wf_G]/F_H ≥ E_H[w] − C_wp⁴/d. This is the paper's "endpoint expansion of the core-constant numerator wΦ".
- Then (C1b), (C1a) and (C3), dropping −a²ΣE G_vi² ≤ 0. ∎

**OK.**

**(C3a).** With k₀ = ⌊p/4⌋, Minkowski and (M1) give ‖U‖_{k₀} ≤ U₀·1.01 ≤ 0.52. The paper has ≤ 3/5; **OK**. Then

E_H[T_A1{μ>1}] ≤ E[U²1{U>1}] ≤ E U^{k₀} ≤ 0.52^{⌊p/4⌋} ≤ e^{−0.16p},  T_A1{μ≤1} ≤ 2w.

This uses T_A ≤ μ² and μ ≤ U (Schur order). **OK.**

**(C3b).** E_HΘ ≤ Σ_± (2E w_± + e^{−0.16p}) ≤ **8ρ + C_Θb₀** with C_Θ = 4(C_C1 + C_w) + 22 ≤ 9·10⁴. Both branches are symmetric. **OK.**

### 2.12 Cramér–Rao form of (C4), CR

**Statement.** Let A, B, M be PSD on N, p ≥ 3, μ ∝ Φγ, V = −p log α − p log β on U, and Σ = Cov_μ. Then

- Σ ⪰ (I + E_μ∇²V)^{−1}, and
- 𝖦[(trM − q_M)Φ] ≤ 2p𝖦[(tr(MA)α^{−1} + tr(MB)β^{−1})Φ] + 4p𝖦[(q_{AMA}α^{−2} + q_{BMB}β^{−2})Φ].

The integrands are set to 0 off U. **M need not satisfy M ⪯ A here.**

*Proof.* Put Y_j := x_jΦ − ∂_jΦ, which is C^{p−2} with polynomial growth.

- GIBP on x_jΦ gives 𝖦[x_jY_i] = δ_ij𝖦Φ, i.e. E_μ[x(x+∇V)ᵀ] = I.
- GIBP on Y_j, together with ∂_iV·Y_j = −x_j∂_iΦ + ∂_iΦ∂_jΦ/Φ, gives 𝖦[Y_iY_j/Φ] = 𝖦[Φ(δ_ij + ∂_i∂_jV)], i.e. E_μ[(x+∇V)(x+∇V)ᵀ] = I + E∇²V. All terms are bounded because ∂Φ∂Φ/Φ ~ α^{p−2}.
- Scalar Cauchy–Schwarz in L²(μ) gives the matrix bound.
- Then tr M − E_μq_M = tr(M(I − Σ)) ≤ tr(M(I − (I+Q)^{−1})) ≤ tr(MQ), with Q = E_μ∇²V ⪰ 0. Finally use ∇²(−log α) = 2A/α + 4Axxᵀ A/α². ∎

The paper's "boundary terms vanish because p is large" is **OK** for p ≥ 3. Numerical check G3: min(RHS − LHS) = 0.055 > 0 over 25 random 2-D instances.

### 2.13 Transfer of (C4) to signs, C4T

**PDOM.** For 0 ⪯ M ⪯ A and A, B ⪰ 0:

- tr(MA) ≤ trA² ≤ Θ;
- tr(MB) ≤ tr(AB) ≤ Θ;
- AMA ⪯ A³ ⪯ ‖A‖²A ⪯ ΘA;
- BMB ⪯ BAB ⪯ ‖A‖B² ⪯ ‖A‖‖B‖B ⪯ ΘB.

Consequently, for L ∈ {AMA, BMB} with Q ∈ {A, B} the matching factor: q_L ≤ Θq_Q, |(Lx)_i| ≤ Θ√Q_ii·√q_Q and |L_ij| ≤ Θ√(Q_iiQ_jj). **OK** (l. 483–491).

**C4T, restated.** Under CSL and (R), for every root v and every core-measurable 0 ⪯ M ⪯ A:

E_H[trM − q_M(ξ)] ≤ 2pE_H[tr(MA)τ⁺ + tr(MB)τ⁻] + 4pE_H[q_{AMA}(ξ)(τ⁺)² + q_{BMB}(ξ)(τ⁻)²]
          + K₄{p⁵(ρ + b₀)/d + p²/d + p⁹/d² + e^{−p}/d}.

The paper writes t in place of ρ; ρ ≤ θ_z for every z.

*Proof.*
- CR is applied pointwise in the core. TRANS is applied to the five observables F₀,…,F₄; the left side is F₀ and the right sides carry the factors 2p and 4p.
- Grade one, F₁…F₄ (EPB): ≤ 1.5(p⁴/d)E_H[m κ_i⁴] with m ∈ {Θτ^±, 2Θ(τ^±)²}. INTERP with η = 8ρ + C_Θb₀ ≥ 1/d (from C3b) and q = ⌈log d⌉ gives E[Θ·Y] ≤ e·η·‖Θ‖₂^{1/q}‖Y‖_{2q} with ‖Y‖_{2q} ≤ 2.02²·6.4⁴. The required moment orders are ≤ 16(log d + 1) ≤ p/2. Total ≲ 5.4·10⁵·p⁵η/d. This is the paper's "Cp⁵(t+b)/d".
- Grade one, F₀ (EPB4): the monomials with ≥ 2 row factors are handled by INTERP with η_R := E_I E_H R_I² ≤ (2/(da²))·Σ_± row_± ≤ 8·Σ_± row_± ≤ 3.2·10⁵(ρ + b₀), where I is uniform on d padded slots. The monomials with ≤ 1 row factor give Cp²/d, using p²R ≤ p²(1+R²)/2. Total C{p⁴(ρ+b₀) + p²}/d, which is the paper's display at l. 534.
- Grades ≥ 2: e·(K_gp⁴/d)²·‖m‖₂ per observable. With the outer p this is Cp⁹/d² (l. 535–536).
- Remainders: ≤ e^{−p}/d (l. 537–538).

All five derivative bounds use only physical entries and τ, so they also hold at zero sources (and A12 removes the issue anyway). **OK.**

### 2.14 (C5), W bounds, transferred terms, (C6)

**C5 (deterministic matrix facts).** Let P be symmetric positive definite on V, v a root with P_vv = Z_v and P_{vN} = ±aξ, z > 0, X_z = (P+zI)^{−1}, C = (P_{−v})^{−1} and C_z = (P_{−v}+zI)^{−1}. Then:

- (i) X_z[N,N] − C_z[N,N] = a²(X_z)_vv(C_zξ)(C_zξ)ᵀ restricted to N; its trace is a²(X_z)_vvξᵀC_z[N,N]²ξ.
- (ii) C − C_z = zC_zC ⪰ zC_z², and (C_z²)[N,N] ⪰ (C_z[N,N])².
- (iii) a²ξᵀ(C − C_z)[N,N]ξ = (X_z)_vv^{−1} − G_vv^{−1} − z.
- (iv) **tr[X_z[N,N] − C_z[N,N]] ≤ (Z_v/z)(G_vv − (X_z)_vv)**, using 1/G_vv = Z_vα ≤ Z_v.
- (v) G[K,K] ⪰ C and ‖C_z‖ ≤ 1/z.
- (vi) tr(C_{z,+}[N,N]C_ν[N,N]) ≤ ½tr(C_{z,+}[N,N]² + C_{z,ν}[N,N]²) + z^{−1}tr((C_ν − C_{z,ν})[N,N]) ≤ 2dW_z/z, with W_z := (1/d)Σ_νtr((C_ν − C_{z,ν})[N,N]).

**OK.** Numerical check I5 (200 random instances): identity error 4·10^{−15}, max(mid − rhs) = −0.27 < 0, max(trace lhs − 2trW/z) = −0.35 < 0.

**WB.** Assume CSL and dz ≥ 1, and put θ_z := max_{i,±}(1 − E X^±_{z,ii}/y^±_i)₊. Then ρ ≤ θ_z and E(G_ii − X_{z,ii}) ≤ y_i(ε + θ_z). Moreover:

- E W_z ≤ (1/d)Σ_ν[2d(ε+θ_z) + (D_v/z)(ε+θ_z)] ≤ **8(θ_z + ε)**, using C5(iv), (v) and dz ≥ 1;
- W_z ≤ (1/d)Σ_νΣ_{i∈N}G^ν_ii, so ‖W_z‖₂ ≤ 4.04;
- INTERP with η = 8(θ_z + b₀) gives **E[(h⁺_v + h⁻_v)W_z] ≤ 53(θ_z + b₀)**.

**OK** (A9).

**TT (transferred terms).**

- tr(M_zA)τ⁺ = a⁴G⁺_vv tr(C_{z,+}[N,N]C₊[N,N])/Z_v⁺ ≤ 8a⁴d·h⁺_vW_z/z, and similarly for tr(M_zB)τ⁻. Hence E_H[tr(M_zA)τ⁺ + tr(M_zB)τ⁻] ≤ **27(θ_z + b₀)/(dz)**.
- q_{AM_zA}(ξ)(τ⁺)² = (Aξ)ᵀM_z(Aξ)/α² ≤ ‖M_z‖a²Σ_i(G⁺_vi)², with ‖M_z‖ ≤ 2a²/z. Hence E_H[q_{AM_zA}(τ⁺)² + q_{BM_zB}(τ⁻)²] ≤ (2.1/(dz))(2ρ + 2·10⁴b₀).

**OK** (l. 580–591).

**(C6), restated (any z with dz ≥ 1).** With q_z = a²ξᵀC_{z,+}[N,N]ξ and μ_z = a²trC_{z,+}[N,N], so that trM_z − q_{M_z} = (μ_z − q_z)/Z_v⁺:

E_H(μ_z − q_z)/Z_v⁺ ≤ K₆{p(θ_z+b₀)/(dz) + p⁵(θ_z+b₀)/d + p²/d + p⁹/d² + e^{−p}},  K₆ = max(8.5·10⁴, K₄).

This is C4T + TT. **OK.**

### 2.15 Scalar closure and (C2) (lines 600–625)

**SCALAR, restated (any z with dz ≥ 1; also used at l. 699).** Under CSL and (R),

θ_z² ≤ K_s{z + p(θ_z+b₀)/(dz) + p⁵(θ_z+b₀)/d + p²/d + p⁹/d² + e^{−p}},  K_s = 2K₆ + 2.

*Proof.*
- Put m_i = E X_{z,ii}. Schur gives (X_z)_vv^{−1} = Z_v + z − q_z; Jensen gives m_v^{−1} ≤ Z_v + z − Eq_z.
- E q_z = Eμ_z − E(μ_z − q_z), and Eμ_z = a²Σm_i − a²E tr[(X_z − C_z)[N,N]]. So m_v^{−1} ≤ Z_v + z − a²Σ_{i∼v}m_i + e_v with e_v := E(μ_z − q_z) + a²E tr[(X_z − C_z)[N,N]].
- Bound y_ve_v. By C5(iv), y_v·a²E tr[(X_z−C_z)[N,N]] ≤ 2a²D_v(ε+θ_z)/z ≤ 1.1(θ_z+b₀)/(dz). By (C6), y_vE(μ_z − q_z) = D_v·E(μ_z−q_z)/Z_v ≤ 2K₆{…}.
- At a maximising (v, ±) with θ_z > 0: m_v = y_v(1−θ_z) and m_i ≥ y_i(1−θ_z).
- Multiplying by y_v and using y_vZ_v = 1 + L_v − C_v gives θ_z²/(1−θ_z) ≤ (L_v−1)θ_z − C_v + y_v(z + e_v). Here (L_v−1)θ_z ≤ 0 (PAR′, A11), C_v ≥ 0 and y_v ≤ 2. Hence θ_z² ≤ 2z + y_ve_v. ∎

The paper's "t² ≤ C{…+d^{−1}+…}" is **OK**; the d^{−1} term is absent with L_v ≤ 1.

**(C2), restated.** Under CSL and (R),

ρ ≤ θ_{u²} ≤ C_t·u, with u = (p/d)^{1/3} and C_t = 2K_s + 5,

and

sup E(h^±_x − 1)² + ρ + sup_{v,±}a²Σ_{i∼v}E(G^±_vi)² + sup_v E_HΘ ≤ δ := C_δ·u (≤ C_δ(ε + p⁴/d + u)).

*Proof.*
- With z = u²: p/(dz) = u, dz = d^{1/3}p^{2/3} ≥ 1, and REG gives b₀ ≤ 3u, p⁵/d ≤ u, and p²/d, p⁹/d², e^{−p} ≤ u².
- So θ² ≤ K_s(2uθ + 10u²): four terms ≤ u² (z, p²/d, p⁹/d², e^{−p}) plus 2ub₀ ≤ 6u². Hence θ ≤ (K_s + (K_s² + 10K_s)^{1/2})u ≤ (2K_s + 5)u.
- Then SM2, ROW and C3b give C_δ = 13C_t + 4·10⁵. ∎

"For p ≤ d^{1/7}: p⁵/d ≤ u, b ≤ Cu, p²/d ≤ u², p⁹/d² ≤ u²": **OK** (p⁷ ≤ d, p^{11} ≤ d², p⁴ ≤ d, p^{25} ≤ d⁴). Note that "e^{−cp} ≤ u²" also needs a lower bound on p (p ≥ C log d), which the text does not state; (R) supplies it.

---

## 3. External theorems: exact forms needed

**X1, Gaussian integration by parts (fact (b)).** For h ∈ C¹(ℝ^n) with |h(x)| + |∇h(x)| ≤ C(1+|x|)^m: ∫x_ih dγ_n = ∫∂_ih dγ_n.

- Uses here: h = x_jΦ and h = x_jΦ − ∂_jΦ (Φ ∈ C^{p−1}, p ≥ 3); optionally h = (Ax)_iα^{p−1}β^p for N_G = 2𝖦F.
- Proof: one-dimensional Stein plus Fubini.

**X2, log-concave covariance bound (fact (a); Prékopa).** For n ≥ 1, let ψ : ℝ^n → [0,∞) be continuous and even with ψ((x+y)/2) ≥ √(ψ(x)ψ(y)) and ∫ψ dγ_n > 0. Then μ = ψγ_n/Z satisfies ∫(θ·x)²dμ ≤ |θ|² for all θ. With the linear map x = M^{−1/2}y this extends to γ_{M^{−1}}.

- Route: midpoint Prékopa–Leindler in ℝ^n makes θ ↦ ∫ψ(x)e^{−|x−θ|²/2}dx midpoint log-concave, take h(z) = ψ(z)e^{−|z−(θ₁+θ₂)/2|²/2}. Evenness then gives value ≤ the value at 0, i.e. E_μe^{θ·x} ≤ e^{|θ|²/2}. Expanding at θ → 0 (the mean is 0) gives the claim. Hessians are not needed.
- Used once (C1b), with ψ = e^{(p−1)(log(1−q_A)+q_A)}(1−q_B)₊^p·1_U and M = I + 2(p−1)A, in dimension |N(v)| ≤ d.
- A weaker fact does not suffice: the lower bound N_G ≥ f_G·w genuinely needs an upper bound on the covariance. Royen's inequality gives only N_G ≥ 0, and Cramér–Rao gives only lower covariance bounds.
- The mgf form of (a) is not used in lines 237–625.

**X3, Rademacher-to-Gaussian comparison (fact (d)).** GS1 and GSM of §2.3: remainder constant K_E4 < 0.67 in one coordinate and the same constant in several coordinates. Needs f ∈ C^{4k+4} with bounded derivatives. Ingredients: Taylor with Lagrange remainder (Mathlib `taylor_mean_remainder_lagrange`), Gaussian even moments, Fubini on `Measure.pi`.

**X4, Taylor endpoint functional.** |L(φ)| ≤ (2/15)sup|φ^{(5)}| on [−1,1]. Proof by Taylor with remainder at 0 for φ, φ′ and φ‴; any constant ≤ 1 would do.

**X5, elementary inequalities.** Hölder for finitely many factors on finite probability spaces; Minkowski; Cauchy–Schwarz; Jensen for x ↦ 1/x. Plus matrix Cauchy–Schwarz: E[xuᵀ] = I ⇒ E[xxᵀ] ⪰ (E[uuᵀ])^{−1}.

**X6, linear algebra.**
- Schur complement inverse and determinant (reuse `BiluLinial/Common`).
- Loewner antitonicity of the inverse.
- |G_xy|² ≤ G_xxG_yy for G ⪰ 0.
- Compression: PC²P ⪰ (PCP)².
- Rank-two determinant and Woodbury on span{e_v, e_i} (RANK2).
- tr(XY) ≤ ‖X‖trY for X, Y ⪰ 0; tr(XY) ≤ ½tr(X² + Y²).
- A(I+cA)^{−1}A ⪰ A²/(1+c‖A‖); I − (I+Q)^{−1} ⪯ Q.

**X7, clipped powers.** t ↦ t₊^m is C^{m−1} with vanishing derivatives of order < m at t ≤ 0.

**Not needed here:** Brascamp–Lieb beyond X2, Royen/Milman (optional alternative for N_G ≥ 0 only), hypercontractivity, smoothing, Chebyshev.

---

## 4. Proposed DAG for lines 237–625

Prefix `T.` is the tight-bound DAG. The difficulty scale is E (easy, < 150 Lean lines), M (medium), H (hard).

**Inputs from other sections (not audited here):**
- `T.PAR` (l. 52–68; restated as PAR′, §1.2)
- `T.LAW` (paired law, l. 69–78)
- `T.ZS` (zero sources, A12)
- `T.INS` (root insertion + F1, l. 125–141)
- `T.DEL` (lem:fw-deletion)
- `T.FLOOR` (lem:fw-floor)
- `T.MOM` (F2 plus the induction, producing CSL (M1)–(M4))

| id | statement (constants explicit) | deps | diff |
|----|-------------------------------|------|------|
| T.REG | (R) implies the list in §1.1 (k\* bounds, moment orders, closure inequalities, b₀ ≤ 3u) | – | E |
| T.PARP | PAR′ 1–6: s ≤ 2, L_v ≤ 1, c_ij ≤ 1/d, C_v ≤ 1/d, D_x ∈ [1,2], U₀ ≤ 0.51, ε ∈ [1/d, (pq)^{−1/2}] when p ≤ 2q/9 | T.PAR | E |
| T.MT | moment toolkit §1.5 from CSL | T.PARP, T.MOM | E |
| T.CJ | recursion for c_j; c₂ = 1/12; \|c_j\| ≤ 1 | – | E |
| T.GS1 | one-coordinate E4 with K_E4 < 0.67 | T.CJ, X3 | M |
| T.GSM | several-coordinate E4: 𝖦f = Σ_{\|j\|_g≤k}c_j𝖱∂^{2j}f + 𝓔, \|𝓔\| ≤ 0.67Σ_{\|j\|_g=k+1}sup\|∂^{2j}f\| | T.GS1, Fubini | M–H |
| T.TAY5 | \|L(φ)\| ≤ (2/15)sup\|φ^{(5)}\| | X4 | E |
| T.RANK2 | rank-two fibre formulas (det, G(t)_vi, G(t)_vv, G(t)_ii) | X6 | E–M |
| T.E1 | E1 with error 1.15·10⁹p⁵a⁵E g\*⁶ and explicit D₁, D₃ | T.RANK2, T.TAY5, T.MAJ1 | M |
| T.E3 | (E3) derivative calculus (optional, only if later sections need it, e.g. W3) | X6 | M |
| T.MAJ1 | one-variable majorant: coefficient bounds of products of quadratics, including the sup over \|t\| ≤ 2 | – | E–M |
| T.MAJ | several-variable majorant lemma (§2.4) | Leibniz for iterated partials or MvPolynomial coefficients | M–H |
| T.CLIP | regularity and vanishing of clipped powers | X7 | M |
| T.E5 | sup bounds of §2.4 for f₁, Φ, wΦ, F, F₀…F₄ | T.MAJ, T.CLIP | M |
| T.CREM | core averages ≤ 4.1M̄(4.2/d)^{k+1} | (M3), Hölder | E–M |
| T.EPB | endpoint majorant bound \|∂^ν(gΦ)\|/Φ ≤ m_g(4p+2)^na^nΠκ^ν | T.MAJ, T.INS | M |
| T.EPB4 | refined single-coordinate bound (row/diagonal split) | T.MAJ1, T.INS | M |
| T.HGR | grade-j H-averages: (e/2)‖m_g‖₂(K_gp⁴/d)^j; grade one 1.5(p⁴/d)max E[m_gκ⁴] | T.EPB, T.MT | M |
| T.E6 | (E6) with (C₁, C₂) such that 64 log C₁ + 16 log C₂ ≤ log d | T.REG | E |
| T.INTERP | INTERP | Hölder | E |
| T.TRANS | generic transfer (§2.8) | T.GSM, T.E5, T.CREM, T.HGR, T.E6, T.FLOOR, T.INS, T.CLIP | M |
| T.PREK | X2 (log-concave covariance bound), whitened form | midpoint PL in ℝ^n | **H (long pole)** |
| T.GIBP | X1 | – | M |
| T.C1a | \|E_{ν_K}(N_R − N_G)/F_H\| ≤ 2·10⁴p⁴/d | T.TRANS | E |
| T.C1b | N_G ≥ f_G·w ≥ 0 | T.PREK, X6 | M |
| T.C3 | Schur identity (C3), both branches | T.INS | E–M |
| T.ROW | a²ΣE(G^±_vi)² ≤ 2ρ + 5ε + 1/d + 2·10⁴p⁴/d | T.C1a, T.C1b, T.C3, T.PARP, T.MT | E |
| T.SM2 | E(h−1)² ≤ 5ε + 2ρ | T.MT | E |
| T.CK | E w ≤ 2ρ + 5ε + 1/d + 2.2·10⁴p⁴/d | T.TRANS, T.C1a, T.C1b, T.C3 | E |
| T.C3a | E[T_A1{μ>1}] ≤ 0.52^{⌊p/4⌋}; T_A1{μ≤1} ≤ 2w | T.MT | E |
| T.C3b | EΘ ≤ 8ρ + 9·10⁴b₀ | T.CK, T.C3a | E |
| T.CR | Cramér–Rao form of (C4), for every PSD M | T.GIBP | M |
| T.PDOM | prefactor domination | X6 | E |
| T.C4T | transfer of (C4), error K₄{p⁵(ρ+b₀)/d + p²/d + p⁹/d² + e^{−p}/d} | T.CR, T.PDOM, T.TRANS, T.EPB, T.EPB4, T.INTERP, T.C3b, T.ROW | M–H |
| T.C5 | matrix facts C5 (i)–(vi) | X6 | E–M |
| T.WB | E W_z ≤ 8(θ_z+ε); E[(h⁺+h⁻)W_z] ≤ 53(θ_z+b₀) (dz ≥ 1) | T.C5, T.MT, T.INTERP, (M2) | E |
| T.TT | trace and quadratic transferred terms (§2.14) | T.C5, T.WB, T.ROW | E |
| T.C6 | (C6) for every z with dz ≥ 1 | T.C4T, T.TT | E |
| T.SCALAR | scalar inequality for every z with dz ≥ 1 | T.C6, T.C5, T.PARP, Jensen | E–M |
| T.C2 | θ ≤ C_tu and δ = C_δu | T.SCALAR, T.ROW, T.SM2, T.C3b, T.REG | E |

**Exports used later in the paper:**
- T.E1: GR1, l. 676.
- T.GSM/T.E5/T.TRANS/T.E6: l. 650, 1089, 1281, 1296.
- T.C3a: l. 1475.
- T.C5: l. 1534.
- T.C6 and T.SCALAR with general z: l. 699.
- T.ROW and T.C2: GR1.

**Design notes for Lean:**
- Represent E_H, E_{ν_K} and 𝖱 as finite sums. Represent 𝖦 as an integral over `N → ℝ` with `Measure.pi (fun _ => gaussianReal 0 1)`.
- State every derivative bound pointwise ("∀ x, |∂^ν f x| ≤ …"), with ∂^ν defined as iterated partial derivatives in a fixed order of the coordinates. GSM only applies them in that order, so commuting partials is never needed.
- The coefficient-majorant route (MAJ) avoids Faà di Bruno. A Mathlib `norm_iteratedFDeriv_comp_le` route would lose a factor n! ≈ n^n. That is affordable for p ≤ d^{2/17} with a larger k\* (about k\* = ⌈100p/log d⌉ and log d ≥ 1600), because the exponent becomes −Kp/17 + 4.69p. It **fails for p ≤ d^{1/7}**, where the exponent is +Kp/7. If this route is taken, record that the C-lemma then needs p ≤ d^{2/17}, which the application p = ⌊c₀d^{2/17}⌋ satisfies.
- Work with positive sources only (A12).

---

## 5. Numerical checks (all pass)

- `auditA_constants.py`:
  - c₀…c₈ = 1, 0, 1/12, −1/45, 103/10080, −229/56700, …; max_{j≤60}|c_j| = 1; |c_{j+1}/c_j| → 0.40528 = 4/π². The series agrees with e^{t²/2}/cosh t to 10^{−41}.
  - K_T = 0.13333 = 2/15; L(x^k) = 0 for k ≤ 4 and L(x⁵) = 16.
  - K₀ = 1/6, K₁ = 0.0639, …; sup_L K_L = 1/6.
  - Regime facts s ≤ 2, d a²s² ≤ 1, η₀ ≥ 3/q for p ≤ 2q/9: 0 failures.
  - RANK2 formulas verified symbolically.
- `auditA_identities.py` (graph with 7 vertices and 12 edges, d = 4, p = 3, random sources, exact enumeration):
  - (C3): both sides 0.007392992859, difference 1.4·10^{−16}.
  - F1 error 4·10^{−15}.
  - (E3) error 2·10^{−32}.
  - E1 fibre ratio 0.086 ≤ 2/15.
  - C5 identities error ≤ 4·10^{−15}; inequalities hold with margins 0.27 and 0.35.
- `auditA_gaussian.py` (2-D grid quadrature, 25 random instances):
  - N_G − f_Gw ≥ 0.020.
  - N_G = 2𝖦F to 7·10^{−9} (4·10^{−14} for p ≥ 5).
  - (C4) RHS − LHS ≥ 0.055.
  - E4 in 2 coordinates within bound.
  - E5 ratio ≤ 0.014 against (5p)^n(2+μ₀)Πb^{ν/2}.
- `auditA_e4cos.py`: E4 on cos⟨λ,x⟩ in 1–3 coordinates, k ≤ 6: max error/bound = 0.085.
- `auditA_e6.py`:
  - E6 with (C₁, C₂) = (8, 8) on p ∈ [120 log d, d^{1/7}]: max[(log LHS) + p]/p = −1.61 (log d = 300), −1.75 (400), −2.13 (4000). The asymptotic coefficient is log 40 + 1 − 16 + 64/7 = −2.168.
  - The binding constraint near log d ≈ 256 is 8k\*+12 ≤ p/2.
