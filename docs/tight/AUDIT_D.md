# AUDIT-D — contact estimate, conclusion, and closing the induction

Source: `docs/second_order_bilu_linial_tight.tex`. Lines 1–236 (setup, paired law, deletion, insertion
floor, source maximum) and 1557–2073 (end of §1.5 and the conclusion) were read line by line. Lines
1334–1558 (D1–D10) were re-derived because the final contradiction uses them. Lines 237–1333 were read
for their statements only: those lemmas are cited here as inputs and audited elsewhere.

Scripts (all checks pass):
- `scripts/tight/auditD_params.py` checks the parameter identities, the drift reserve D2, the `C_+`
  envelope, the regime conditions at `p = ⌊c₀d^{2/17}⌋`, and the D16 exponent ledger.
- `scripts/tight/auditD_identities.py` checks the exact `K_i` identity behind `Q_*`, the D3 algebra,
  BM1, FS2, C5, the walk-sum bounds `K ≥ 0`, `K_vv ≥ 1`, `K_vi ≥ τ_vi`, the JR2 scalar step, and a
  monotone (Jacobi) construction of the deletion lift.

---

## 0. Verdict

**Lines 1557–2073: correct, with only minor fixes. No fatal gap.** Every display from "Retaining both
physical root weights" to the final inequality `γ_d² ≤ 4(d−1)+4/⌊c₀d^{2/17}⌋` was re-derived. The exact
identities hold symbolically (`Φ^{-1}∂_i³(Φx_i) = a³K_i`, the row-free part RC5, the `x_i=0` part in
D13, the D3 algebra) and the deterministic inequalities hold exactly (BM1 with constant 16, FS2, C5, JR2,
JR3, D8, D15). The drift reserve is `d(r−1)(1−rL̄) = 1/p − (3/2)η₀ + O(1/(pd))`. The ledger exponents
are as claimed: three critical terms at scale `p^{-1}` and everything else `O(κ₀^{-3/2}p^{-3/2})`. The
contradiction `p^{-1} ≤ (3/4+o(1))p^{-1}` follows. The true margin is larger than the paper states:
`1/p − 2c_p ≈ 1/(2p)`, against the `1/(4p)` the paper allots to errors.

**This verdict is conditional** on the earlier global lemmas F2, F3, the insertion floor, deletion, E1,
E4/E6, C1–C3b, C2, GR1, S1, W1, W5, WT2, CR1, CR3 and B1. They carry all the deep external inputs: the
Royen/Milman correlation inequality, Brascamp–Lieb and Prékopa. AUDIT-D has not re-verified their
proofs.

**Induction closure (lines 186–235, 2055–2071): correct, with fixable gaps.** The invariant, the
expanding-cube contact argument and the extraction of `σ` all work. Two points need fixes (zero-source
faces in the source-maximum lemma; the ODE lift in the deletion lemma), and the constants must follow a
fixed quantifier order.

### Gaps and fixes

| id | where | severity | issue | fix |
|----|-------|----------|-------|-----|
| G1 | Lemma fw-maximum (l.204–222) | minor, fixable | At a box maximum with some zero source coordinates, the paper says "other zero coordinates can be removed first". For a zero plus-source with a positive minus-source, the law is **not** the law of a smaller graph: the plus branch lives on `H−j`, the minus branch on `H`. | Impose the first-order conditions only in the positive plus-coordinates `S⁺`. On `S⁺` the Jacobian of `Z⁺` is `−D_y^{-1}B_{S⁺}D_y^{-1}`, where `B_{S⁺}` is the `B` matrix of `H[S⁺]` (edges to zero-source vertices have `τ=0`). Its inverse `K_{S⁺}` has the same walk-sum bounds, and terms with `y_i⁺=0` vanish in (D3) because `ℓ_i=0` and `G⁺_{ii}=G⁺_{vi}=0`. F2 and F3 then hold with `K_{S⁺}`; only `K_vv ≥ 1` and `K_vi ≥ τ_vi` are used. |
| G2 | Lemma fw-deletion (l.103–107) | minor, fixable | The lift `y(t)` is built by ODE continuation, which is heavy in Lean. | (i) Existence of `ŷ ≤ y` with `Z^J(ŷ) = Z^H(y)|_J` by monotone Jacobi iteration. Each `Z_i` is strictly decreasing in `y_i` and nondecreasing in `y_j`, so the iterates decrease, stay `≥ 1/target`, and converge by monotone convergence and continuity (checked numerically, §8 of `auditD_identities.py`). (ii) Uniqueness from the strict monotonicity `⟨Z(y¹)−Z(y²), y¹−y²⟩ < 0`. (iii) For F2/F3, the lift along `Z*+te_i` has right derivative `−D_yKD_ye_i`, by the integral mean value theorem and a uniform negative-definiteness bound (§2.5). |
| G3 | §1.2–1.5 throughout | structural (not a math gap) | "C absolute, may change"; "o(1) as d→∞ with κ₀, c₀ fixed". The final choice "κ₀ small, then c₀ small" is valid only if every `C` is independent of `κ₀` and `c₀`. | Checked for the three critical coefficients (§4.2): they come only from the constants of S1, C2, D6, CR3, GR1 and FS5, none of which depends on `κ₀` or `c₀` once `d ≥ d₀(κ₀,c₀)`. In Lean, state every analytic lemma as `∃ C, ∃ K, ∀ d p h, Regime K d p h → …` (§4.1). |
| G4 | constants | fixable, existential only | No explicit `c₀`, `κ₀` or `d₀`: the paper never evaluates its constants. | Obtain them existentially (§4.3). An explicit `c₀` would need explicit constants in S1, C2, D6, CR3, GR1, FS5, JR2/RC2 and the UMI loss factor. |
| G5 | l.1972 | cosmetic | "use `J ≥ C_+` in (D13) to obtain (D14)": `J ≥ C_+` is used in the definition of `𝔇`, together with (D13). | Rewording. |
| G6 | D10 vs final list | cosmetic | `ε_BL` from (B1) is missing in (D10) and only reappears in the final list. | Add `+ε_BL` to D10. |
| G7 | §1.5 notation | cosmetic, Lean-relevant | Heavy symbol overloading: `a` vs `a_i`, `α, β` (two meanings each), `q, t, z, c, d_v, T, B, K, Q, H, M, N`. | Use the disambiguated names of §1.2. |
| G8 | dependency risk | not a gap here; blocking for Lean | The four weak identities need W1 (whose remainder needs GR1, hence Royen), FS1 needs WT2 (Prékopa or Brascamp–Lieb covariance), and D10 needs B1 (matrix Brascamp–Lieb). Without GR1, `pe²` becomes `Θ(1)` instead of `Θ(1/p)` and the argument fails. | §5. |

### Explicit constants

- **`c₀`, `κ₀`, `d₀`** are not explicit in the paper. They must be chosen in this order:
  1. the absolute lemma constants (∃ at the top level), which define three critical coefficients
     `C₁, C₂, C₃`;
  2. `κ₀ := min(1, (24C₁)^{-2})`;
  3. `c₀ := min(1, (24C₂)^{-3/17}, (κ₀²/(24C₃))^{3/34})`, which makes
     `C₁√κ₀ + C₂c₀^{17/3} + C₃κ₀^{-2}c₀^{34/3} ≤ 1/8`;
  4. `d₀(c₀,κ₀)` large: it must make `p = ⌊c₀d^{2/17}⌋` satisfy the regime `K log d ≤ p`, `p ≥ 80`,
     `log d ≥ 512` (so that moment orders `8k*+12 ≤ p/2`), and make the non-critical ledger
     `C_rest κ₀^{-3/2} p^{-3/2} + 2η₀ + 1/(2p(p−1)) ≤ 1/(4p)`.

  As an illustration only: if all absolute constants were ≤ 100, then `κ₀ ≈ 1.7·10⁻⁷` and
  `c₀ ≈ 0.03`.
- **Final theorem constant:** `C = 8/c₀`, because `4/⌊c₀d^{2/17}⌋ ≤ 8/(c₀d^{2/17})` once
  `c₀d^{2/17} ≥ 2`. The strict `<` comes from `I ± aA_σ ≻ 0`.
- **Regime at `p = ⌊c₀d^{2/17}⌋`** (checked numerically): `p ≤ d^{2/17} < d^{1/7}`, `p⁷ ≤ d`,
  `p/log d → ∞`, `h = κ₀p^{-4} ≥ d^{-1}`, and (E6) has `log[p·40^p(Cp)^{4k*+4}d^{-k*}]/p ≈ −4.8`. The
  bound `8k*+12 ≤ p/2` needs `log d ≥ 512` with the paper's `k* = ⌈16p/log d⌉`. Since `2/17 < 1/7`,
  the choice `k* = ⌈7p/log d⌉` already makes E6 hold. `d₀` is astronomically large, which is
  irrelevant for an existential statement.

### External theorems needed (details in §5)

1. Royen's Gaussian correlation inequality (Milman's monotone form), only for the derivative at `s=1`
   with centred-ellipsoid truncated powers: `𝖦[q_{AB}α^{p−1}β^{p−1}] ≥ 0` with `α=(1−xᵀAx)₊`,
   `β=(1−xᵀBx)₊`, `A,B ⪰ 0`. Used in GR1.
2. Brascamp–Lieb for linear functions in matrix form, `Σ_ν ⪯ E_ν(I+∇²V)^{-1}`, for `V` convex on a
   convex domain with barrier behaviour (clipped powers). Used in B1.
3. "An even log-concave perturbation of the standard Gaussian has covariance `⪯ I`", by Prékopa or as
   a corollary of item 2. Used in C1, the C3 whitening step and WT3.
4. Elementary but sizeable: Gaussian integration by parts in `ℝⁿ`; the Rademacher endpoint Taylor
   identities E1/E4; the Schur product theorem (not in Mathlib, which has only
   `IsHermitian.hadamard`); M-matrix and walk-sum positivity; Hölder interpolation (UMI, §2.6).

None of items 1–3 is used *directly* in lines 1557–2073. They enter through GR1, WT2, B1, C1 and C2.

---

## 1. Parameters, notation, regime

### 1.1 Parameters (D1), exact

`q = d−1`, `p = ⌊c₀d^{2/17}⌋`, `Δ = 4/p`, `R² = 4q+Δ`, `a = 1/R`.
`η₀ = (−Δ + √(Δ²+4qΔ))/(2q)`, the positive root of `qη²/(1−η) = Δ`. Then `0 < η₀ ≤ 2/√(pq)`.
`τ_* = (1−η₀)/q`, `s = (1+qτ_*)/(1−τ_*) = (2−η₀)/(1−(1−η₀)/q)`, `r = 1+η₀/2`, `ε := r−1 = η₀/2`.

Checked exactly:
- `a²s² = τ_*/(1−τ_*)²`, so every edge has `τ_ij ≤ τ_*` when `0 ≤ y ≤ s`.
- The diagonal-dominance margin is `1 − dτ_*/(1+τ_*) = η₀/(1+τ_*)`.
- `Z_i(s𝟙) = (1+(deg i −1)τ_*)/(1+qτ_*) ≤ 1`, with equality exactly when `deg i = d`.
- `L̄ := da²s² = dq(1−η₀)/(q−1+η₀)²`.
- `c(x) := (√(1+4x)−1)/2` solves `c(1+c) = x`. Hence `c_ij = c(a²y_iy_j) ≤ a²y_iy_j`, and
  `τ = c/(1+c)`.

### 1.2 Disambiguated names (proposed Lean names)

| paper | meaning | name |
|---|---|---|
| `a` | `1/R` | `a` |
| `a_i, b_i` | `(X₊)_ii/2`, `(X₋)_ii/2` | `xpHalf i`, `xmHalf i` |
| `c`, `d_v` (l.1563) | `G⁺_vv/2`, `G⁻_vv/2` | `gpRoot`, `gmRoot` |
| `α, β` (§1.1–1.4) | `(1−ξᵀAξ)₊`, `(1−ξᵀBξ)₊` | `insA`, `insB` |
| `α, β` (l.1581–1583) | `E[Ω₊uᵀM₊b₊]`, `E[Ω₋uᵀM₋b₋]` | `alphaE`, `betaE` |
| `q, t` (l.1592) | `q₊, t₊` | `qPlus`, `tPlus` |
| `z, z₋` | `E[Ω₊b₊ᵀK₊b₊]`, `E[Ω₋b₋ᵀK₋b₋]` | `zPlus`, `zMinus` |
| `T` (§1.5 top) | `Σ_N E x_iz_i` | `Tmix` |
| `T` (l.697) | `a²A_H` (unsigned) | `Tadj` |
| `K` (l.88) | `𝓑^{-1}` | `Kwalk` |
| `K_±` (l.1569) | `X₊∘X_±/4` | `Khad±` |
| `Q` (B1) / `Q_*` | positive shifted trace / fourth-order term | `Qbl`, `Qstar` |
| `ξ` (l.1804) | profile error | `xiProf` |
| `ε` | `r−1 = η₀/2` | `eps` |

### 1.3 Regime used by all lemmas (recommended Lean form)

`Regime K d p h :≡ K ≤ d ∧ K·log d ≤ p ∧ p⁷ ≤ d ∧ 1/d ≤ h ≤ 1`.

Every lemma of §1.2–1.5 should read `∃ C K, ∀ d p h, Regime K d p h → …`, with `C` and `K` absolute.
The specific choices `p = ⌊c₀d^{2/17}⌋` and `h = κ₀p^{-4}` enter only in (i) the ledger (§4) and
(ii) checking the side conditions of S1, namely `p/(dh)+p⁵/d ≤ ϵ√h` and
`p²/d + p⁹/d² + p(ε+p⁴/d)/(dh) ≤ ϵh`, which hold for `d ≥ d₀(κ₀,c₀)`.

---

## 2. Induction architecture

### 2.1 Objects

Fix `d, p, a, s, r` as above and a finite simple graph `G` on `V` with `maxDeg ≤ d`. For `S ⊆ V`
(a Finset), let `H = G[S]`. Sources are `y = (y⁺,y⁻) ∈ [0,s]^S × [0,s]^S`. The **normalized
precision** is

```
P̃^±(y,σ)_ii = 𝒟_i(y) := 1 + Σ_{j∼i} c(a²y_iy_j),      P̃^±(y,σ)_ij = ± a √(y_iy_j) σ_ij  (i∼j),
```

and the weight and law are

```
w(y,σ) = 1[P̃⁺≻0 ∧ P̃⁻≻0] · (det P̃⁺ · det P̃⁻)^p,     𝒵(y) = Σ_σ w(y,σ),     E_y f = Σ_σ w f / 𝒵.
```

`h_i^± = (P̃^±)^{-1}_ii`. Physical quantities are `G^± = D_y^{1/2}(P̃^±)^{-1}D_y^{1/2}` (rows of zero
sources are zero) and `Z_i = 𝒟_i/y_i`. The physical weight differs from `w` by the factor
`Π(y_i⁺y_i⁻)^p`, which does not depend on `σ`, so the two laws coincide. At `y_j = 0`, row `j` of `P̃`
is `e_j` and `h_j = 1`: this is the paper's convention, now built into the definition.

### 2.2 Invariant

```
Inv(S) :≡ ∀ y ∈ Q₁(S) := [0,s]^{2S},   𝒵_S(y) > 0  ∧  ∀ i∈S, ∀±,  E_y h_i^± ≤ r.
```

**Theorem IND.** For `d ≥ d₀`, `Inv(S)` holds for every `S ⊆ V`. The proof is strong induction on
`|S|`, assuming `Inv(T)` for every `T ⊊ S`. Only `T = S∖{w}` is used.

1. **Existence (FLOOR-EXIST).** For `y ∈ Q₁(S)` and any root `v ∈ S`, the deletion lift gives
   `ŷ ≤ y|_{S∖v}` with `Z^{S∖v}(ŷ) = Z^S(y)|_{S∖v}`. `Inv(S∖v)` at `ŷ` gives
   `E G_{J,ii} ≤ rŷ_i ≤ 1.01y_i`, and Lemma fw-floor gives `F_S ≥ 40^{-p}`. The insertion
   factorization `𝒵_S(y) = const(y) · 𝒵_{S∖v}(ŷ) · F_S` with `const > 0` then gives `𝒵_S(y) > 0`.
   For `S = ∅` the normalizer is `1`.
2. **Continuity (CONT).** `y ↦ E_y h_i^±` is continuous on `Q₁(S)` (§2.4).
3. **Contact exclusion (CONTACT).** For every `λ ∈ [0,1]`: if `E_y h_i^± ≤ r` for all `y ∈ Q_λ`
   (`Q_λ = [0,λs]^{2S}`) and all `i, ±`, then `E_y h_i^± < r` for all `y ∈ Q_λ`.
4. **IVT closing.** Let `M(λ) := sup_{y∈Q₁} max_{i,±} E_{λy} h_i^±`. `M` is continuous on `[0,1]` by
   `IsCompact.continuous_sSup` (Mathlib, `Topology/Order/Compact.lean:477`), and the supremum is
   attained. `M(0) = 1 < r`, because all sources are zero and `P̃ = I`. If `M(λ) = r`, the caps hold
   on `Q_λ` and some point attains `r`, which contradicts step 3. So `M` never equals `r`, and the IVT
   gives `M(1) < r`, hence `Inv(S)`.

The paper's "first contact" is exactly the first `λ` with `M(λ) = r`. Neither compactness of a
moving family nor differentiability in `λ` is needed beyond step 4.

### 2.3 Extraction (EXTRACT), the last display

`Inv(V)` at `y⁺ = y⁻ = s𝟙` gives `𝒵 > 0`, so some `σ` has `P̃^±(s𝟙,σ) ≻ 0`. Congruence by
`s^{-1/2}I` gives `P^± = diag Z(s𝟙) ± aA_σ ≻ 0`. Since `Z_i(s𝟙) ≤ 1`,
`I ± aA_σ = P^± + diag(1−Z) ≻ 0`, so every eigenvalue of `A_σ` lies in `(−R, R)` and
`‖A_σ‖ < R = √(4(d−1)+4/p)`. Then `4/p ≤ (8/c₀)d^{-2/17}`. This also handles empty graphs and
vertices of degree `< d`.

### 2.4 Continuity, compactness, IVT and differentiability facts (each a small node)

| node | statement |
|---|---|
| CT1 | `c(x) = (√(1+4x)−1)/2` is continuous, increasing, `0 ≤ c(x) ≤ x`, and `C¹` on `x > −1/4`. |
| CT2 | `y ↦ P̃^±(y,σ)` is continuous on `[0,∞)^S` (continuity of `√`). |
| CT3 | `λ_min` is 1-Lipschitz in operator norm (Weyl), and `A ≻ 0 ⟺ λ_min(A) > 0`. |
| CT4 | `y ↦ 1[P̃≻0]·(det P̃)^p` and `y ↦ 1[P̃≻0]·(det P̃)^{p−1}·adj(P̃)_ii` are continuous for `p ≥ 2`: they are locally the smooth formula, or locally 0, or bounded by `|det|^{p−1}·C → 0`. |
| CT5 | `𝒵 > 0` on `Q₁` implies `E_y h_i^±` is continuous on `Q₁`. |
| CT6 | `Q₁` is compact, `M(λ)` is continuous, and sups are attained (`IsCompact.exists_isMaxOn`). |
| CT7 | IVT on `[0,1]`. |
| CT8 | Symmetry: `(y⁺,y⁻,σ) ↦ (y⁻,y⁺,−σ)` preserves `w`, so a minus contact reduces to a plus contact. |
| DF1 | One-sided derivative: for `P̃` with plus-positive set `S⁺`, `t ↦ E_{Z⁺+te_i}[(G⁺_vv)^k]` has right derivative `C_i = p·Cov((G⁺_vv)^k, G⁺_ii) − k·E[(G⁺_vv)^{k−1}(G⁺_vi)²]` at `0⁺` when `k ≤ p−2`. Signings with `P⁺_σ` positive semidefinite and singular contribute `O(t^{p−k}) = o(t)`; increasing `Z_i` only moves `P⁺` up in Loewner order. |
| DF2 | Lift derivative (G2 fix): §2.5. |
| DF3 | Jacobi iteration for the deletion lift: monotone bounded sequences converge, and each scalar step uses the IVT, since `y_i ↦ Z_i` is continuous, strictly decreasing and tends to `∞` as `y_i → 0⁺`. |
| DF4 | `Z` is injective on `(0,s']^S` for some `s' > s`, because `B ≻ 0` there by strict diagonal dominance. |
| DF5 (other sections) | Taylor with remainder on `[−1,1]` along regular edge fibres (E1, E4); Gaussian integration by parts for `C¹` functions with `|∇g| ≤ poly` (Stein's lemma on `ℝⁿ`). |

### 2.5 Source maximum (F2, F3) without the implicit function theorem

Let `y*` maximize `m_k(y) = E_y (G⁺_vv)^k/(y⁺_v)^k` over `Q_λ`, with `y⁺_v* > 0`. Fix
`i ∈ S⁺ = {y⁺ > 0}`.

- The deletion-lift construction (Jacobi iteration on the coordinates `S⁺`) gives `y(t) ≤ y*` in
  `Q_λ` with `Z⁺(y(t)) = Z⁺(y*) + te_i` and `y⁻(t) = y⁻*`.
- `⟨Z(y(t))−Z(y*), y(t)−y*⟩ = ⟨te_i, y(t)−y*⟩ ≤ −c|y(t)−y*|²`, with `c > 0` uniform on
  `{1/(Z*+1) ≤ y ≤ s}`. Hence `|y(t)−y*| ≤ t/c`.
- The integral mean value theorem gives `te_i = M(t)(y(t)−y*)` with
  `M(t) = ∫₀¹ DZ(y*+u(y(t)−y*))du → DZ(y*) = −D_y^{-1}BD_y^{-1}`, so
  `(y(t)−y*)/t → −D_yKD_ye_i`.
- `m_k(y(t)) ≤ m_k(y*)`, together with DF1, gives
  `C_i + k·m_k·(y_v*)^k·y_i*·K_vi ≤ 0`, i.e. the paper's `C_i ≤ −k m_k y_v^k y_i K_vi`.

For `i = v` with `K_vv ≥ 1` and moment log-convexity this gives F2; for `k = 1` at the contact it gives
F3. `K` here is the inverse of `B_{S⁺}` (G1).

### 2.6 Unknown-mass interpolation (UMI), used about 20 times in §1.5

Let the law be a finite weighted average, `Y, Z ≥ 0`, `‖Y‖_k ≤ M`, `‖Z‖_k ≤ B`, `k ≥ 2`, and `θ > 0`.
Then

```
E[YZ] ≤ B·(M/θ)^{1/(k−1)}·(E Y + θ).
```

Proof: Hölder with exponents `(k/(k−1), k)`, then
`‖Y‖_{k/(k−1)} ≤ ‖Y‖₁^{1−1/(k−1)} ‖Y‖_k^{1/(k−1)}`, then split on `EY ≥ θ` or `EY < θ`.

In the regime, `k ≍ p`, `M/θ ≤ (d/h)^{O(1)}` and `p ≥ K log d` give `(M/θ)^{1/(k−1)} ≤ 2`. Every
"high-moment interpolation" and "polynomial floor" step in the paper is an instance: `Y` is an unknown
nonnegative energy with a polynomial envelope, and `Z` is a fixed-degree product of diagonals, possibly
including `D_*` (a maximum over at most `d+d²` indices, with `‖D_*‖_k ≤ (d²)^{1/k}·C`). The moment
inputs come from F2 with `k ≤ p/2`: `sup E h^k ≤ (1+2ε)^k ≤ e^{εp} ≤ e`.

---

## 3. Claims of §1.5, restated with explicit constants, and verified

### 3.0 Context at a contact (hypotheses of CONTACT)

`CTX`:
- (H1) `Regime K d p h`, `p = ⌊c₀d^{2/17}⌋`, `h = κ₀p^{-4}`, `d ≥ d₀(c₀,κ₀)`.
- (H2) `Inv(S∖w)` for all `w ∈ S`.
- (H3) the law exists on `Q_λ` and `E_y h_i^± ≤ r` on `Q_λ`.
- (H4) `y* ∈ Q_λ`, `E_{y*}h_v⁺ = r`. Then `y⁺_v* > 0`, because a zero source has `h = 1 < r`.

Expectations are at `y*`. `N = N(v)`, `x_i = G⁺_vi`, `z_i = G⁻_vi`, `S = Σ_N E x_i²`,
`Tmix = Σ_N E x_iz_i`, `𝓡 = (p−1)S − p·Tmix`, `ℓ_i = a²y⁺_vy⁺_i`, `L = Σ_N ℓ_i`,
`C₊ = Σ_N (c⁺_vi)²`, `D₊ = 1+L−C₊`, `δ_i = r − E h_i⁺ ≥ 0`, `J = Σ_N ℓ_i K_vi`.

Inputs valid at every point of `Q_λ` under (H1)–(H3), from other sections: F2, C1–C3b, C2 (with
`δ = C_δ(ε+p⁴/d+(p/d)^{1/3})`), GR1 (`δ_row = C_rδ/p`), S1, W5, W1, WT2, CR1, CR3, B1, E1, E4/E6. At
`y*` only: F3.

Constants written `C` below are absolute (∃ at the top level, before `κ₀, c₀`). "Large `d`" means
`d ≥ d₀(κ₀,c₀)`.

### 3.1 D1–D10 (lines 1334–1558; re-derived because the conclusion uses them)

- **D1.** Definitions as in §1.1. **OK** (identities checked exactly).
- **D2.** `L̄ = dq(1−η₀)/(q−1+η₀)²` and `d(r−1)(1−rL̄) = 1/p − (3/2)η₀ + O(1/(pd))`, so
  `d(r−1)(1−rL̄) ≥ 1/p − 2η₀` for large `d`. Numerically `(drift−1/p)/η₀ = −1.500` for
  `d = 10⁸…10⁴⁰`. **OK**; the error is `O(η₀) = O((pd)^{-1/2}) = o(1/p)`.
- **Deterministic source facts** (l.1366–1368):
  - `L ≤ L̄`, since `y ≤ s` and `|N| ≤ d`.
  - `J ≥ C₊`, since `ℓ_iτ_vi = c_vi²` and `K_vi ≥ τ_vi` (walk sum; checked numerically).
  - `C₊/a² ≤ da²s⁴ = L̄s²`, and `rL̄s² ≤ 4` throughout the regime (numerically
    `rL̄s² − 4 ≈ −6η₀ + 20/q < 0`). The paper's two-sided `C₊/a² = 4+O(·)` is more than needed: only
    this upper bound is used.

  **OK.** `K_vi ≥ τ_vi` is **load-bearing**: without `J ≥ C₊`, the term `−(1−1/p)C₊` costs about `1/p`
  in `d𝔇`, which exceeds the margin.
- **D3** (exact scalar inequality). Inputs:
  - E1 at each `i ∈ N`: `E[ξ_iG⁺_vi] = E[𝒟₁x_i − ⅓𝒟₃x_i] + O(p⁵a⁵)`;
  - `𝒟₁x_i = −aP_i + (2p−1)ax_i² − 2pa·x_iz_i`, with `P_i = G⁺_vvG⁺_ii` (checked);
  - `Φ^{-1}∂_i³(Φx_i) = a³K_i`, which defines `Q_* = (a⁴/3)Σ_N E K_i` (checked symbolically for
    random PSD `A, B` and several values of `p, a, ξ_i`);
  - the root equation `D₊r = 1 − aΣ_N E[ξ_ix_i]`;
  - F3: `p·Cov(G⁺_vv,G⁺_ii) ≤ E x_i² − r y_v y_i K_vi`;
  - the cap `E G⁺_ii = y_i(r−δ_i)`.

  Conclusion:

  ```
  (r−1)(1−rL) + rΣℓ_iδ_i + (1−1/p)a²S + (r/p)J + 2a²𝓡 ≤ Q_* + rC₊ + C_{E1}·p⁵d^{-2}.
  ```

  **OK.** The algebra was checked with sympy. Zero-source neighbours contribute 0 (G1).
- **|Q_*| bound.** `|Q_*|/a² ≤ C(p+p³δ) ≤ Cp`. The row-free part is `6[(p−1)P_i²+pP_iQ_i]`. Every
  other monomial has at least two row factors and a coefficient of degree at most 3 in `p` (checked).
  The C2 row bound and UMI give `p³δ`. **OK.**
- **D4.**
  - `𝓡 ≤ C(p+p⁵/d)`. All other left-hand terms are `≥ 0`: `1−rL̄ ≥ 0` by D2,
    `(r−1)(1−rL) = (r−1)(1−rL̄) + r(r−1)(L̄−L)`, `K ≥ 0`, and `δ_i ≥ 0`.
  - If `𝓡 ≥ −b`, then `S + a^{-2}Σℓδ ≤ C(1+p+p⁵/d+b)` and `L̄−L ≤ Ca²(1+p+p⁵/d+b)/(r−1)`.

  **OK.**
- **D5.** `δ ≤ 3C_δ c₀^{17/6} p^{-5/2}`. This is exact given `d ≥ (p/c₀)^{17/2}` and `c₀ ≤ 1`: the
  three terms are `c₀^{17/4}p^{-19/4}`, `c₀^{17/2}p^{-9/2}` and `c₀^{17/6}p^{-5/2}`. **OK.**
- **D6.** With `ϑ = d^{-10}`, `λ := a²S + E tr A² + ϑ ≤ λ₁ := C_λ p/d`. The chain is:
  1. C2 gives `λ ≤ Cδ`.
  2. CR1 with C1 and `N_G = 2𝖦F` (Gaussian integration by parts, checked:
     `𝖦[(trA−q_A)g] = −𝖦[xᵀA∇g] = 2𝖦F`) gives `𝓡 ≥ −E_λ`.
  3. D4 gives `a²S ≤ C(p+E_λ)/d`.
  4. Whitening `N_G ≥ f_G w`, the (B3)–(B4) transfer for `wΦ`, C3a, and `e^{−cp} ≤ ϑ` give the
     bound on `E tr A²`.
  5. Young on `Cp⁵√(λδ)/d` gives `λ ≤ C(p/d + p¹⁰δ/d² + p¹³/d³ + ϑ) ≤ C_λ p/d`, using `p⁹δ ≤ d` and
     `p¹² ≤ d²`.

  **OK.**
- **D7.** `S ≤ C_S p`, `Σ_Nℓ_iδ_i ≤ Cpa²`, `L̄−L ≤ ε_s := C_s p^{3/2}d^{-1/2}`. **OK.**
- **D8.** `|y⁺_v−2| + ||N|/d−1| + d^{-1}Σ_N|y⁺_i−2| ≤ C(ε_s+η₀+1/d)`. Deterministic: the identity
  `ds² − y_vΣy_i = (s−y_v)Σy_i + s(ds−Σy_i)` has both terms `≥ 0`, and `|s−2| ≤ C(η₀+1/d)`. Consequence
  used later: `G⁺_vv ≥ 1/Z⁺_v ≥ y⁺_v/(1+L̄) ≥ 0.9`, so `Ω₊ := (G⁺_vv/2)² ≥ 1/5`. **OK.**
- **D9a.** CR3 applies with `λ_r = C(S+1)/d`, `ρ_r = δ_row`, `λ_c = λ₁`, `δ_c = δ`. The required
  orderings follow from `S ≤ Cp` and `p²/d ≤ Cδ`. With `Γ = p⁴√(pδ/d)`:

  ```
  E_row = C{Γ√(S+1) + Γ + p¹³/d² + e^{−cp}}.
  ```

  Here `p⁵√(λ_rρ_r) = CΓ√(S+1)` and `p⁴√(λ_cδ_c) = CΓ`. **OK.**
- **D9b.** B1 with `𝓡, E_row ≤ Cp` gives `Qbl ≤ Cp`, hence
  `E[Ω₊d^{-1}trY₊²] + E[Ω₋d^{-1}tr(Y₊Y₋)] ≤ C`, where `Ω₋ = G⁺_vvG⁻_vv/4` and `tr(Y₊Y₋) ≥ 0`. By C5
  (checked numerically), `0 ≤ trΔ_± ≤ h^{-1}Z_v^±(G^±_vv − X^±_vv)`. S1 then gives
  `E[Ω trΔ_±] ≤ Ch^{-1/2}`. Expanding with `‖·‖ ≤ h^{-1}` costs `C/(dh^{3/2})`. **OK.**
- **D10.**

  ```
  𝓡 ≥ L_d[(p−1)q₊ + pq₋] − C{E_row + p⁵/d + p²/(dh) + p/(dh^{3/2})} − ε_BL,
  ```

  with `L_d = 16da²` and
  `L_d[(p−1)q₊+pq₋] = a²E{(p−1)(G⁺_vv)²trX₊[N,N]² + pG⁺_vvG⁻_vv tr(X₊[N,N]X₋[N,N])}` exactly, since
  `q₊ = (16d)^{-1}E[(G⁺_vv)²trX₊[N,N]²]`. **OK**, with `ε_BL` added (G6).

### 3.2 Root weights and energies (l.1560–1594)

Definitions: `Ω₊ = (G⁺_vv/2)²`, `Ω₋ = G⁺_vvG⁻_vv/4`, `K₊ = X₊∘X₊/4`, `K₋ = X₊∘X₋/4`,
`M₊ = diag(xpHalf_i²)`, `M₋ = diag(xpHalf_i·xmHalf_i)`, `u = 𝟙_N/√d`, `b_± = 4·Tadj·M_±u`. The energies
`q_±, ζ, z₊, t_±, alphaE, betaE, z₋` are as in l.1577–1585.

- (E-a) `K_± ⪰ 0` by the **Schur product theorem** (a needed node; not in Mathlib). All the energies
  are `≥ 0`, because the entries of `K_±`, `u` and `b_±` are `≥ 0`.
  `q₊−t₊ = E[Ω₊Σ_{i≠j}u_iu_j(X₊)_ij²/4] ≥ 0` and `ζ − alphaE ≥ 0`. **OK.**
- (E-b) `ζ² ≤ q₊z₊`, by Cauchy–Schwarz for the positive semidefinite bilinear form
  `(f,g) ↦ E[Ω₊fᵀK₊g]` on random vectors. **OK.**
- (E-c) `q₊ = (1/4)E[Ω₊d^{-1}trX₊[N,N]²] ≤ C_q` (D9b). **OK.**

### 3.3 Mask energies: BM1–BM4 (l.1596–1654)

- **BM1** (deterministic). Let `X, Y ⪰ 0` with `‖X‖, ‖Y‖ ≤ h^{-1}`, `b ≥ 0`, `U = X·diag(b)·Y`,
  `F_ji = X_iiU_ji − X_jiU_ii`, `K = X∘Y/4`, and `X_ii ≤ D` on `I`. Then

  ```
  Σ_{i∈I,j} F_ji² ≤ 16 D²h^{-2} bᵀKb.
  ```

  Proof as in BM2/BM3:
  - `tr(BX²BY²) ≤ h^{-2}tr(BXBY)`;
  - `U_ii² ≤ X_ii(YBXBY)_ii`;
  - `(X²)_ii ≤ h^{-1}X_ii`;
  - `tr(BXBY) = 4bᵀKb`.

  **OK.** Random tests give a maximum ratio of 0.079, well below 1.
- **BM4.** For `(X,Y,b) = (X₊,X₊,b₊)` or `(X₋,X₊,b₋)`, `I = N`, `D = D_*`, and `θ = d^{-2}`:

  ```
  Σ_{i∈N,j} E[D_*^m Ω_± F_ji(b_±)²] ≤ C(m)·h^{-2}(z_± + θ).
  ```

  BM1 pointwise, then UMI. The envelope is `z_± ≤ C d D_*^C/h`. **OK.**

### 3.4 Fixed mask, weak errors: FS1–FS7 (l.1656–1798)

- **FS2** (exact Schur identity; checked numerically to `2·10⁻¹⁶`):

  ```
  F_ji = −a (X_ε)_ii (X₊)_ii Σ_{k∈N∖i, l∼i} (C_i^ε)_jk u_k (C_i^+)_kl ξ_l,
  ```

  where `C_i^τ = (P^τ_{−i}+hI)^{-1}`, padded with a zero at `i`. **OK.**
- **FS1.** For `ε ∈ {±}`, `H ∈ {1, Ω₊, Ω₋}`, `U = X_εD_uX₊`, `β_h = (dh)^{-1}`, `θ = d^{-2}`, and any
  fixed `m`:

  ```
  Σ_{i∈N,j∼i} E[D_*^m H F_ji²] ≤ C(m)·h^{-2}{ζ − alphaE + β_h(q₊−t₊) + θ} + C(m)·h^{-1/2}.
  ```

  Inputs:
  - D8 (`Ω₊ ≥ 1/5`, so `H ≤ 5D_*²Ω₊`);
  - WT2 with `H₀ = H` and `L = T_dirᵀT_dir` or `T_cavᵀT_cav`;
  - `‖C^ε‖ ≤ h^{-1}`;
  - the Schur subtraction `(C_i⁺)_kl = (X₊)_kl − (X₊)_ki(X₊)_il/(X₊)_ii`;
  - `Σ_l(X₊)_il² ≤ h^{-1}(X₊)_ii`;
  - the exact identities `(a²/d)Σ_{i∈N}(X₊)_ii²Σ_{l∼i,k∈N∖l}(X₊)_kl² = 4uᵀ(K₊−M₊)b₊` and
    `(1/d)Σ_{i≠k∈N}(X₊)_ki² = 4uᵀ(K₊−M₊)u` (re-derived);
  - W5 (`E[D_*^C(X_τ²)_ii] ≤ Ch^{-1/2}`, from `X² ⪯ h^{-1}(G−X)` and S1);
  - `a²·#{(i,k)∈N²: i∼k}/d ≤ a²d ≤ 1/3`;
  - UMI.

  **OK.**
- **FS4.** For `H = Ω₊`: `|∂_ijH|²/H = 4a²(G⁺_viG⁺_vj)² ≤ 4a²D_*²(G⁺_vi)²`. For `H = Ω₋`:
  `|∂_ijH|²/H ≤ 2a²D_*²{(G⁺_vi)²+(G⁻_vi)²}`. For `H = 1` it is 0. This holds for every edge `ij` with
  `i ∈ N`, including `j = v`. **OK** with constant 4.
- **FS5.** With `e := p√δ_row/(√d·h)`:

  ```
  𝖲_u ≤ C e √(ζ − alphaE + β_h(q₊−t₊) + θ) + C e h^{3/4},       𝖲_{b_±} ≤ C e √(z_± + θ).
  ```

  The proof is Cauchy–Schwarz in the joint index `(i,j)`: `√(Σ E[HF²])` times
  `√(Σ u_i² E[(2paHR_ij + |∂H|)²/H])`. The second factor is `≤ Cp√δ_row`, by GR1 at vertex `i`
  (`a²Σ_{j∼i}E R_ij² ≤ 2δ_row`), GR1 at `v`, FS4 and UMI. With `a ≤ 1/√(4q)` this gives the bound.
  **OK.**
- **FS6.** With `r₀ = q₊−ζ−t₊`, `r₁ = ζ−z₊−alphaE` and `B₀ = C{p/(dh) + 1/(dh^{3/2}) + e^{−cp}}`
  (from W1):
  - `|r₁| ≤ Ce√(z₊+θ) + CB₀`;
  - `|r₀| ≤ Ce√(z₊+|r₁|+β_h(q₊−t₊)+θ) + Ceh^{3/4} + CB₀`.

  These are W1 with `(ε,ν) = (+,+)`, `w = u − b₊`, `f = u` or `b₊`. W2 was re-derived exactly, and
  `ζ − alphaE = z₊ + r₁`. **OK.**
- **FS7.** Using `0 ≤ q₊−t₊ ≤ C_q` and AM–GM (`e√|r₁| ≤ C(e√z₊ + e² + B₀ + e√θ)`), every weak residual
  with `(ε,ν) ∈ {(+,+), (−,+)}` and `f ∈ {u, b₊}` or `{u, b₋}` is at most

  ```
  E_c = C{e√z₊ + e√z₋ + e² + B₀ + e[h^{3/4} + (dh)^{-1/2} + √θ]}.
  ```

  The mixed fixed-mask score uses FS1 with `ε = −`, whose right-hand side contains only the **plus**
  energies, because the cavity part uses only `‖C^−‖ ≤ h^{-1}`. **OK.**
- **Four weak identities** (W1 at `(ε,ν) = (+,+)` and `(−,+)`, with `w = u − b₊` and `w = u + b₋`
  respectively). Each holds up to `O(E_c)`, and every mask stays inside its expectation:

  ```
  q₊ − ζ = t₊ + O(E_c);                    ζ − z₊ = alphaE + O(E_c);
  E[Ω₋uᵀK₋(u+b₋)] = t₋ + O(E_c);           E[Ω₋b₋ᵀK₋(u+b₋)] = betaE + O(E_c).
  ```

  **OK.**

### 3.5 Profiles, RC1, RC2 (l.1800–1842)

Set `χ₊ = √(ε/p+ε²+p/d) + ε_s + η₀ + 1/d`, `ρ_v = ε/p + ε²` and
`xiProf = √h + χ₊ + √ρ_v + ε + 1/d`.

- `E(h_i⁺−1)² ≤ 2δ_i + C(ε/p+ε²)`: F2 with `k = 2` gives `((pr−2)/(p−2))² = 1+2ε+4ε/(p−2)+O(ε²)`.
  **OK.**
- `Σ_N y_i⁺δ_i ≤ Cp`, from D7 and `y_v⁺ ≥ 1`. **OK.**
- `d^{-1}Σ_N E|xpHalf_i − 1| ≤ C(√h + χ₊)`. The **`y_i`-weighted** Cauchy–Schwarz
  `(1/d)Σ(y_i/2)E|h_i−1| ≤ C√((1/d)Σy_i(2δ_i+Cρ_v)) ≤ C√(p/d+ρ_v)` avoids dividing by small sources;
  add D8 and S1 for `X_ii` versus `G_ii`. The same bound holds with fixed-degree diagonal multipliers,
  by UMI. **OK.**
- `E|gpRoot − 1| ≤ C(√ρ_v + ε_s + η₀ + 1/d)`, from `(p−1)Var h_v⁺ ≤ r(r−1)` and `E h_v⁺ = r`. **OK.**
- **RC1.** `0 ≤ t₊, t₋ ≤ 1 + Cε`. This needs `(s/2)⁴ ≤ 1 + 4/q ≤ 1 + ε` (since `1/q = o(η₀)`) and the
  fourth-moment cap. **OK.**
- **RC2.** `betaE ≤ alphaE + C·xiProf`, via:
  - `α₀ = uᵀ(A_H/d)u ≤ 1`;
  - `4a² = 1/(q+1/p)`, so replacing `4·Tadj` by `A_H/d` costs `O(1/d)`;
  - `|alphaE − α₀| ≤ C·xiProf`, by telescoping `|c²a_l²a_k²−1|`, UMI, and Jensen over pairs `l∼k`,
    where `Σ_{k∼l} ≤ d`;
  - in `betaE`, only the plus factors are replaced, and `E[d_vb_lb_k] ≤ (s/2)³E[h⁻_vh⁻_lh⁻_k] ≤ 1+Cε`.

  No lower bound on minus sources is needed. **OK.**

### 3.6 Reserve: JR3, JR2, RC3 (l.1844–1918)

- **α-cap.** From (E-b), `q₊ ≤ ζ + 1 + C(E_c+ε)` and `z₊ = ζ − alphaE + O(E_c)`:
  `alphaE(1+ζ+e′) ≤ ζ(1+2e′) + e′(1+e′)` with `e′ = C(E_c+ε)`, hence
  `alphaE ≤ ζ/(1+ζ) + C₀(E_c+ε)`. `ζ` is bounded, since `ζ² ≤ C_q(ζ + CE_c)`. Put
  `α̂ = (alphaE − C₀(E_c+ε))₊`. Then `α̂ ≤ ζ/(1+ζ) < 1` and `ζ ≥ α̂/(1−α̂)`. **OK.**
- **JR3.** With `λ_m = betaE/(t₋+betaE) ∈ [0,1]`, the test vector `b₋ − λ_m(u+b₋)` gives

  ```
  z₋ ≥ betaE²/(t₋+betaE) − CE_c ≥ betaE²/(1+betaE) − C(E_c+ε),
  ```

  and also `q₋ − t₋ = z₋ − betaE + O(E_c)`. **OK.**
- **JR2.** With `A_p = p−1`, `𝒫 = A_p(q₊−t₊) + p(q₋−t₋)`:

  ```
  𝒫 ≥ (A_p/2)z₊ + (p/2)z₋ − 1/(4A_p) − Cp(E_c + xiProf).
  ```

  Ingredients:
  - `f(x) = x²/(2(1+x)) − x` has slope in `[−1, −1/2]` (checked);
  - `−x + (x²/2)(A_p/(1−x) + p/(1+x)) ≥ A_px² − x ≥ −1/(4A_p)` on `[0,1)`. Numerically the minimum
    is between `0.80/(4A_p)` (at `p = 3`) and `1/(4A_p)`, so the bound holds with room.

  **OK.**
- **RC3.** Substituting `E_c` and applying Young (`Cpe√z ≤ (A_p/2)z + C′pe²`):

  ```
  (p−1)(q₊−t₊) + p(q₋−t₋) ≥ −1/(4(p−1)) − Cp{e² + B₀ + e[h^{3/4}+(dh)^{-1/2}+√θ] + xiProf}.
  ```

  **OK.**

### 3.7 Centres: RC4, RC5, D13, D12 (l.1920–1963)

- **RC4.** With `t_{+,0} = (16d)^{-1}E[(G⁺_vv)²Σ_N(G⁺_ii)²]` and
  `t_{−,0} = (16d)^{-1}E[G⁺_vvG⁻_vvΣ_NG⁺_iiG⁻_ii]`: `0 ≤ t_{±,0} − t_± ≤ C√h`, from S1 (physical form
  `E(G_ii−X_ii) ≤ Cs√h`) and UMI. **OK.**
- **RC5.** The row-free part of `Q_*/a²` equals `2L_d[(p−1)t_{+,0} + p t_{−,0}]` exactly (sympy:
  `6P(P(p−1)+pQ)`). **OK.**
- **D13.** `Q_*/a² ≤ 2L_d[(p−1)t_{+,0}+pt_{−,0}] + Cp³(λ₁ + √(λ₁δ_row))`. The `x_i = 0` part of the
  row terms is exactly `−6p(2p−1)P_iz_i² ≤ 0`; every monomial of `K − K|_{x=0}` contains `x_i` and a
  second row factor (sympy: none lacks one); and `λ₁ ≤ δ_row`, so
  `λ₁ ≤ √(λ₁δ_row)`. **OK.**
- **D12.** D10, RC3 and RC4 give `𝒟 := 𝓡 − L_d[(p−1)t_{+,0}+pt_{−,0}] ≥ −L_dc_p − 𝓔`, with
  `c_p = 1/(4(p−1))` and

  ```
  𝓔 = C{E_row + p⁵/d + p²/(dh) + p/(dh^{3/2}) + ε_BL + p(e² + B₀ + e[…] + xiProf)}.
  ```

  The `p√h` from RC4 is contained in `p·xiProf`. **OK.**

### 3.8 Final drift and contradiction (l.1965–2053)

- `𝔇 := (2p−1−1/p)a²S − 2pa²Tmix + (r/p)J − Q_* − rC₊`. The identity
  `(1−1/p)a²S + 2a²𝓡 = (2p−1−1/p)a²S − 2pa²Tmix` holds, so D3 reads
  `(r−1)(1−rL) + rΣℓδ + 𝔇 ≤ C_{E1}p⁵/d²`.
- **D14.** `𝔇/a² ≥ 2𝒟 + (1−1/p)(S−4) − 𝓔′`. It uses `J ≥ C₊` (so `(r/p)J − rC₊ ≥ −r(1−1/p)C₊`),
  `rC₊/a² ≤ 4` (§3.1), and D13. **OK** (G5).
- **D15.** Cauchy–Schwarz on the exact row equation `aΣ_Nσ_vix_i = 1 − Z⁺_vG⁺_vv`, then Jensen, give
  `a²|N|S ≥ (rD₊−1)²`, so `S ≥ (rD₊−1)²/(a²|N|) ≥ L̄s²(1 − (ε_s+5a²)/L̄)² ≥ 4 − C(ε_s+η₀+1/d)`.
  **OK.**
- **Absorption.** `CΓ√(S+1) ≤ ¼(S−4) + C′{Γ + Γ² + ε_s + η₀ + 1/d}`: write
  `S′ = S − 4 + C₁(ε_s+η₀+1/d) ≥ 0`, then use `√(S+1) ≤ √S′ + √5` and Young. **OK.**
- **Conclusion.** `d𝔇 = da²·(𝔇/a²)` with `2da²L_d = 32(da²)² ≤ 2(1+1/q)²`. Then

  ```
  d𝔇 ≥ −2c_p(1+3/q) − 𝓔₀,       𝓔₀ ≤ [C₁√κ₀ + C₂c₀^{17/3} + C₃κ₀^{-2}c₀^{34/3}]/p + C_rest κ₀^{-3/2} p^{-3/2},
  ```

  where `c₀ ≤ 1` and the `e^{−cp}`, `ε_BL` terms are absorbed. D3 and D2 give
  `1/p − 2η₀ ≤ d(r−1)(1−rL̄) ≤ −d𝔇 + C p⁵/d`. Hence

  ```
  1/p ≤ 1/(2(p−1)) + 1/(8p) + C_rest κ₀^{-3/2} p^{-3/2} + 2η₀ + Cp⁵/d + 3/(2pq),
  ```

  which is false for `p ≥ p₀(κ₀)` once the critical sum is `≤ 1/8`. The left side exceeds the first two
  right-hand terms by about `(3/8)/p`. **OK.** The paper's "`<1/4`" also suffices, because
  `1/p − 2c_p − 1/(4p) ≈ 1/(4p) > 0`.

### 3.9 Closing (l.2055–2071)

This is the architecture of §2.2–2.3. "All degree thresholds are independent of graph order" holds,
because every estimate is local: neighbourhoods `N ∪ N(N)` of size at most `d+d²`, and moments of
order at most `p/2`. **OK.**

---

## 4. Ledger and constants

### 4.1 Quantifier order (for Lean)

1. `∃ K C_δ C_r C_λ C_S1 C_CR3 C_FS5 … C₁ C₂ C₃ C_rest` (absolute).
2. `∀ κ₀ ∈ (0,1], ∀ c₀ ∈ (0,1], ∃ d₀`.
3. `∀ d ≥ d₀`, with `p = ⌊c₀d^{2/17}⌋` and `h = κ₀p^{-4}`, `Regime K d p h` holds, the side conditions
   of S1 hold, and the contact-exclusion inequality holds whenever
   `C₁√κ₀ + C₂c₀^{17/3} + C₃κ₀^{-2}c₀^{34/3} ≤ 1/8`.
4. Choose `κ₀, c₀` as in §0, then `d₀`. Final `C = 8/c₀`.

### 4.2 Critical coefficients and where they come from

- `C₁√κ₀ = p·√h·p⁰` comes from RC4 (`4p·C√h`) and from `xiProf ∋ √h` in RC2/JR2. Its constant is the
  S1 constant (`t_h ≤ C√h`) times the RC2/JR2 constants. S1's constant is absolute: `t_h² ≤ C₆(h + …)`,
  with the other terms `o(h)` and `o(√h)·t_h` for `d ≥ d₀(κ₀,c₀)`.
- `C₂c₀^{17/3} = Γ·p` comes from CR3's constant times `√(C_δC_λ)` (D9a), multiplied by `3√5` from the
  absorption. Absolute.
- `C₃κ₀^{-2}c₀^{34/3} = pe²·p` comes from the FS5 constant, GR1's `C_r` and Young in RC3. Absolute.
  Note the exact relation `pe² = κ₀^{-2}·pΓ²`.

### 4.3 Exponent ledger

From `auditD_params.py`, with `d = (p/c₀)^{17/2}` and `h = κ₀p^{-4}`; each entry is
`c₀^A κ₀^K p^E`.

| term | value | status |
|---|---|---|
| `δ` | `c₀^{17/6} p^{-5/2}` | |
| `δ_row` | `c₀^{17/6} p^{-7/2}` | |
| `λ₁` | `c₀^{17/2} p^{-15/2}` | |
| `ε` | `c₀^{17/4} p^{-19/4}` | |
| `ε_s` | `c₀^{17/4} p^{-11/4}` | |
| `e` | `c₀^{17/3} κ₀^{-1} p^{-1}` | |
| `p√h` | `κ₀^{1/2} p^{-1}` | critical |
| `Γ` | `c₀^{17/3} p^{-1}` | critical |
| `pe²` | `c₀^{34/3} κ₀^{-2} p^{-1}` | critical |
| `p/(dh^{3/2})`, `pB₀` | `c₀^{17/2} κ₀^{-3/2} p^{-3/2}` | largest non-critical |
| `pe(dh)^{-1/2}` | `c₀^{119/12} κ₀^{-3/2} p^{-9/4}` | |
| `p·√(ε/p)`, `p√ρ_v` | `c₀^{17/8} p^{-15/8}` | |
| `pχ₊` (through `ε_s`) | `c₀^{17/4} p^{-7/4}` | |
| `Γ²` | `p^{-2}` | |
| `p²/(dh)` | `κ₀^{-1} p^{-5/2}` | |
| `p³√(λ₁δ_row)` | `p^{-5/2}` | |
| `peh^{3/4}` | `p^{-3}` | |
| `p⁵/d`, D3 remainder | `p^{-7/2}` | |
| `p¹³/d²` | `p^{-4}` | |
| `pe√θ` | `p^{-17/2}` | |
| `dη₀` (D2) | `p^{-19/4}` | |

Every non-critical term is `≤ c₀^{(…)}κ₀^{-3/2}p^{-3/2}`. With `c₀ ≤ 1` this gives
`C_rest κ₀^{-3/2} p^{-3/2}`.

**Why 2/17.** `Γ = p⁴(p/d)^{1/2}δ^{1/2}`, and `δ ≍ (p/d)^{1/3}` is the C2 concentration rate, from the
choice `z = (p/d)^{2/3}` in C6. So `Γ ≍ p^{14/3}d^{-2/3}`, and `Γ ≍ 1/p` exactly when `p^{17} ≍ d²`.
The term `pe²` balances at the same exponent because `pe² = κ₀^{-2}pΓ²`, and `h ≍ p^{-4}` is forced by
`p√h ≍ 1/p`. Improving C2's rate `(p/d)^{1/3}` would improve the exponent.

---

## 5. External theorems and the exact special cases needed

| # | theorem | used in | exact special case | notes |
|---|---|---|---|---|
| X1 | Royen GCI, Milman's monotone form | GR1 | For `A, B ⪰ 0` and integer `p ≥ 3`: `E_γ[⟨Ax,Bx⟩ (1−xᵀAx)₊^{p−1} (1−xᵀBx)₊^{p−1}] ≥ 0`, i.e. `E_γ[∇α^p·∇β^p] ≥ 0`, the derivative at `s=1` of `H(s) = E α(X)^pβ(Y_s)^p`. By layer cake this follows from monotonicity in `s` of `P(X∈E, Y_s∈F)` for centred ellipsoids `E, F`. | It is not implied by the Gaussian-function case. Hargé (1999) proves the GCI when one set is an ellipsoid; whether that yields the `s=1` derivative needs a literature check. **Blocking for GR1**, and GR1 is essential: without it `pe² = Θ(1)`. |
| X2 | Brascamp–Lieb, linear functions, matrix form | B1 | `ν ∝ e^{−|x|²/2−V}` with `V = −(p−1)log α − p log β` convex on `{α,β>0}`, and `Σ_ν ⪯ E_ν(I+∇²V)^{-1}`. In fact only `Σ_ν ⪯ E_ν(I+H)^{-1}` with `H = 2(p−1)M/α + 2pN/β ⪯ ∇²V` is used. | The paper sketches the proof by solving `Lw = f−Ef`. Alternatives: derive it from Prékopa–Leindler (Bobkov–Ledoux); or, in finite dimension with a barrier, from strict convexity plus smoothing. Note that the matrix Cauchy–Schwarz in C4 gives only the reverse inequality. **Blocking for D10**, without which there is no `q_±` term. |
| X3 | Even log-concave perturbation of the Gaussian has `Cov ⪯ I` | C1 (`N_G ≥ 0`), C3 whitening, WT3 | Density `e^{−|x|²/2}F(x)` with `F` even and log-concave on a convex set. Instances: `F = α^{p−1}β^p`; `F = (1−q_A)^{p−1}e^{(p−1)q_A}`-type after whitening; `F = HΦ` with `H` a product of principal-determinant powers and `(det P/det(P+hI))^n`. | Follows from X2 with `V` convex. Alternatively Prékopa marginal log-concavity applied to `e^{−|x−y|²/2}F(x)`, then the Hessian at 0. The 1D case is elementary. WT3 also needs concavity of `log det` on principal submatrices and of `P ↦ log det P − log det(P+hI)` (shown in the paper via convexity of `tr(P+tI)^{-1}`). |
| X4 | Gaussian integration by parts | C1, C4, B1, GR1 | Stein's lemma on `ℝⁿ` for `C¹` functions with polynomial growth, vanishing at the boundary of a convex support. Used for `2𝖦F = 𝖦[(trA−q_A)α^{p−1}β^p]` (checked by hand). | Mathlib has the Gaussian measure; the lemma itself is probably not there. |
| X5 | Rademacher endpoint Taylor identities | E1, E4 (everywhere) | `E ξ f(ξ) = E(f′(ξ) − f‴(ξ)/3) + O(‖f^{(5)}‖)`, exact through degree 4; the multi-coordinate expansion E4 with `|c_j| ≤ C^j`. | Elementary (Mathlib Taylor), but bookkeeping-heavy. |
| X6 | Schur product theorem | §1.5 (`K_± ⪰ 0`), W-section | `X, Y ⪰ 0 ⇒ X∘Y ⪰ 0` | Not in Mathlib. Small. |
| X7 | M-matrix and nonbacktracking walk sum | deletion, F2, F3, D3, D14 | `B ≻ 0`, `K = B^{-1} ≥ 0`, `K_vv ≥ 1`, `K_vi ≥ τ_vi` | Neumann series for the weighted nonbacktracking operator (spectral radius `< 1` via the supersolution `f_{i→j} = 1/(1+τ_ij)`), then `M ≥ 0` and `S = δ + ΣM`. Checked numerically. |
| X8 | Hölder interpolation (UMI) | everywhere | §2.6 | Finite weighted sums. Mathlib has Hölder for sums and integrals. |

---

## 6. Proposed DAG (section 1.5 and the induction skeleton)

Difficulty: S (≤ 1 day), M (a few days), L (a week or more), XL (research-grade formalization).
Nodes from other sections are cited by equation label (`F1`, `F2`, `F3`, `FLOOR`, `DEL`, `E1`, `E4`,
`E6`, `C1`, `C2`, `C3a`, `C5`, `C6`, `GR1`, `S1`, `W1`, `W5`, `WT2`, `CR1`, `CR3`, `B1`).

### 6.1 Skeleton

| id | statement | deps | diff |
|---|---|---|---|
| MAIN | `near_ramanujan_signing` | CONST, IND, EXTRACT, PARAM | S |
| CONST | From absolute `C₁, C₂, C₃, C_rest, K`, choose `κ₀, c₀, d₀` (§0) so that for `d ≥ d₀`, `p = ⌊c₀d^{2/17}⌋ ≥ max(80, K log d)`, `log d ≥ 512`, `h = κ₀p^{-4}`, the S1 side conditions hold, and LEDGER holds. | LEDGER | M |
| LEDGER | Real inequality: for all such `d, p, h`, `1/p − 2η₀ − 2c_p(1+3/q) − 3/(2pq) − Cp⁵/d > crit/p + C_rest κ₀^{-3/2}p^{-3/2}` with `crit ≤ 1/8`, plus all monomial bounds of §4.3. | PARAM | M |
| PARAM | `a²s² = τ_*/(1−τ_*)²`; `Z_i(s𝟙) ≤ 1`; `0 < η₀ ≤ 2/√(pq)`; `L̄` formula; D2 lower bound `d(r−1)(1−rL̄) ≥ 1/p − 2η₀`; `rL̄s² ≤ 4`; `L̄s² ≥ 4 − 8η₀ − C/d`; `4/p ≤ (8/c₀)d^{-2/17}`. | — | M |
| EXTRACT | `𝒵_V(s𝟙) > 0` ⇒ `∃σ, opNorm(A_σ) < √(4(d−1)+4/p)`. | PARAM, NORM-PD | S |
| NORM-PD | `I ± aA ≻ 0` ⇒ `opNorm A < 1/a` (opNorm equals the maximal absolute eigenvalue; reuse `BiluLinial/Common`). | — | S |
| LAW | Definitions of §2.1; the `±` symmetry CT8; zero-source decoupling (row `e_j`, `h_j = 1`); physical/normalized dictionary. | CT1, CT2 | M |
| IND | `∀ S ⊆ V, Inv(S)`, by strong induction on Finsets. | FLOOR-EXIST, CONT, CONTACT, CT6, CT7 | M |
| FLOOR-EXIST | `(∀w, Inv(S∖w))` ⇒ `𝒵_S > 0` on `Q₁(S)` and `F_S ≥ 40^{-p}`. | FLOOR, DEL-JACOBI, INSERT | M |
| INSERT | Insertion factorization `w_H(σ) = w_J(σ_J)·(Z_v⁺Z_v⁻)^p·α^pβ^p` (F1 Schur formulas); `𝒵_H = (Z_v⁺Z_v⁻)^p 2^{|N|} 𝒵_J(ŷ) F_H`. | Schur complement (Mathlib) | M |
| DEL-JACOBI | `∃ ŷ ≤ y|_J`, `ŷ ≥ 1/Z^H(y)`, with `Z^J(ŷ) = Z^H(y)|_J`. | DF3, CT1 | M |
| CONT | CT3–CT5. | LAW, CT3, CT4 | M |
| CONTACT | `CTX` (H1)–(H4) ⇒ False. | CTR-FINAL | S (assembly) |

### 6.2 Contact chain (§1.5)

All nodes assume `CTX`.

| id | statement (explicit form in §3) | deps | diff |
|---|---|---|---|
| FW-MAX | F2 on `Q_λ` and F3 at `y*`, including zero-source faces (G1) | DF1, DF2, X7 | L |
| D3 | the exact scalar inequality | E1, F3, KI-ID, X7 | M |
| KI-ID | `Φ^{-1}∂_i³(Φx_i) = a³K_i`; `𝒟₁x_i` formula; row-free part and `x=0` part (polynomial identities) | INSERT | S |
| QSTAR-BD | `|Q_*|/a² ≤ C(p+p³δ)` | KI-ID, C2, UMI, FW-MAX | S |
| D4 | `𝓡 ≤ C(p+p⁵/d)`; conditional bounds on `S`, `Σℓδ`, `L̄−L` | D3, QSTAR-BD, PARAM | S |
| D6 | `λ ≤ C_λp/d` | D4, C2, CR1, C1, C3a, UMI, GIBP | M |
| D7-D8 | `S ≤ C_Sp`, `Σℓδ ≤ Cpa²`, `L̄−L ≤ ε_s`, saturation D8, `Ω₊ ≥ 1/5` | D4, D6 | S |
| D9a | `E_row = C{Γ√(S+1) + Γ + p¹³/d² + e^{−cp}}` | CR3, GR1, D6, D7-D8 | S |
| D9b | `Qbl ≤ Cp`; trace budgets for `Y_±` and for `X_±[N,N]` | B1, D9a, C5, S1, UMI | S |
| D10 | lower bound on `𝓡` by the shifted traces | B1, D9b | S |
| EN | energy definitions; (E-a) to (E-c); Schur product theorem | X6, D9b | S |
| BM1 | deterministic mask inequality (constant 16) | Loewner facts | S |
| BM4 | `Σ E[D_*^mΩ_±F(b_±)²] ≤ Ch^{-2}(z_±+θ)` | BM1, UMI | S |
| FS2 | Schur identity for `F_ji` | Schur complement | S |
| FS1 | fixed-mask bound | FS2, WT2, W5, D7-D8, UMI | M |
| FS4 | `|∂H|²/H ≤ 4a²D_*²(G⁺_vi² + G⁻_vi²)` | inverse derivative formula (E3) | S |
| FS5 | score bounds `𝖲_u`, `𝖲_{b_±}` | FS1, BM4, FS4, GR1, UMI | M |
| WEAK4 | FS6, FS7 and the four weak identities, error `E_c` | W1, FS5, EN | M |
| PROF | profile estimates of §3.5 | FW-MAX, D7-D8, S1, UMI | M |
| RC1-2 | `t_± ≤ 1+Cε`; `betaE ≤ alphaE + C·xiProf` | PROF, FW-MAX | M |
| JR | α-cap, JR3, JR2 (scalar loss `1/(4(p−1))`) | WEAK4, RC1-2, EN | S |
| RC3 | after Young | JR, WEAK4 | S |
| RC4-5 | `0 ≤ t_{±,0}−t_± ≤ C√h`; RC5 exact | S1, UMI, KI-ID | S |
| D13 | `Q_*/a² ≤ 2L_d[…] + Cp³(λ₁+√(λ₁δ_row))` | KI-ID, D6, GR1, UMI | S |
| D12 | `𝒟 ≥ −L_dc_p − 𝓔` | D10, RC3, RC4-5 | S |
| D14-15 | D14 and D15 | D3, D13, D12, PARAM, D7-D8, X7 | S |
| CTR-FINAL | absorption and contradiction, given LEDGER | D14-15, D12, D9a, PARAM, LEDGER | S |

### 6.3 Shared support nodes

| id | statement | diff |
|---|---|---|
| UMI | §2.6 (Hölder interpolation with a floor) for finite weighted averages, plus the `D_*` maximum bound `‖max_{i∈I} X_i‖_k ≤ |I|^{1/k} max‖X_i‖_k` | S |
| MOM | moment inputs: F2 ⇒ `‖h_i‖_k ≤ e^{2ε}` for `k ≤ p/2`; physical `G_ii ≤ s·h_i`; `X_ii ≤ G_ii`; `|G_ij| ≤ √(G_iiG_jj)` | S |
| LOEW | `0 ⪯ X ⪯ h^{-1}I ⇒ X² ⪯ h^{-1}X`; `tr(SY)` monotone in `S` for `Y ⪰ 0`; `(C²)[N,N] ⪰ (C[N,N])²`; `P^{-1} − (P+h)^{-1} ⪰ h(P+h)^{-2}`; positive semidefinite Cauchy–Schwarz | S |
| X7 | walk-sum / M-matrix bounds | M |
| X6 | Schur product theorem | S |
| GIBP | Gaussian integration by parts in `ℝⁿ` (X4) | M |
| DF1, DF2, DF3, DF4 | §2.4 | M each |
| CT1–CT8 | §2.4 | S–M |
| X1, X2, X3 | external theorems (§5) | XL |

**Recommended order.** Start X1, X2 and X3 immediately (they decide the timeline). In parallel:
PARAM, LEDGER, KI-ID, BM1, FS2, LOEW, UMI, X6, X7, D3-algebra, JR and D14-15. These are pure algebra
or deterministic inequalities, checkable now. Then LAW, CONT, DEL-JACOBI, INSERT, FLOOR-EXIST and IND;
then FW-MAX. The contact chain can be stated end to end, with CONTACT derived from its children,
before any analytic leaf is proved.
