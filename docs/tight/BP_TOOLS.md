# BP_TOOLS: generic analytic tools for Sections 1.3–1.5 (Part D)

Sub-blueprint for the self-contained tools of `docs/second_order_bilu_linial_tight.tex`, Sections
1.3–1.5, as audited in `docs/tight/AUDIT_C.md` (§3 Tools, §5 Gaussian layer, §7 DAG) and
`docs/tight/AUDIT_D.md` (§2.6 UMI). All files are under `BiluLinial/Tight/Tools/`. Vocabulary from
`BiluLinial/Tight/Ctx.lean`: `qForm M x = xᵀMx`, `clipF M x = (1 - q_M(x))₊`,
`starPhi p A B = α^p β^p`, `gaussE f = ∫ f ∂gaussPi`. Loewner order `X ⪯ Y` is written
`(Y - X).PosSemidef`; `‖·‖` is `BiluLinial.opNorm`.

Status: `stated` (Lean statement with `sorry`), `proved` (own proof sorry-free, may use stated
nodes), `proved*` (proved and everything below proved). External node used: `D-BLmid`
(`Gauss/BLmid.lean`, `integral_quad_le_of_midpoint`; sorry-free at 2026-09-30 22:13, and
`#print axioms` on every node below reports only `propext`, `Classical.choice`, `Quot.sound`).

**All nodes of this file are `proved*`** (2026-09-30). Files: `Tools/Alpha2.lean`,
`Tools/MatrixFacts.lean`, `Tools/GaussDensity.lean`, `Tools/GIBP2.lean`, `Tools/Cov.lean`,
`Tools/Interp.lean` (not yet imported from `BiluLinial.lean`; checked with `lake env lean`).
No audited statement was found false. Deviations from the audit's wording (all harmless or
more general) are listed at the end.

## Table

| id | statement | source | Lean name (file) | deps | status |
|---|---|---|---|---|---|
| T.ALPHA2 | `α(z+w)α(z−w) ≤ α(z)² e^{−2q_A(w)/α(z)}` (`A ⪰ 0`); `= 0` if `q_A(z) ≥ 1`; constant form `≤ α(z)² e^{−2q_A(w)}` | C §3, §5.3; tex l.1222–1243 | `clipF_add_mul_clipF_sub_le`, `clipF_add_mul_clipF_sub_eq_zero`, `clipF_add_mul_clipF_sub_le_exp` (Alpha2) | – | proved* |
| T.ALPHA2-pow | `φ = α^mβ^{m'}`: `φ(z+w)φ(z−w) ≤ φ(z)² e^{−⟨w,H(z)w⟩}`, `H = 2mM/α + 2m'N/β`, `0 ⪯ M ⪯ A`, `0 ⪯ N ⪯ B`; constant form | C §3 | `clipProd_add_mul_sub_le`, `clipProd_add_mul_sub_le_clipHess`, `clipProd_add_mul_sub_le_exp` (Alpha2) | T.ALPHA2 | proved* |
| T.ALPHA2-G | BLmid's `hmid` for `ρ = φe^{−\|x\|²/2}` with `K = I + H` (and `K = I + cA`, `0 ≤ c ≤ 2m`) | C §5.3 (B1 application) | `gaussWt_midpoint`, `gaussWt_clipProd_midpoint`, `gaussWt_clipProd_midpoint_const` (Alpha2) | T.ALPHA2-pow | proved* |
| T.MAT-0 | `tr(XY) ≥ 0` for `X, Y ⪰ 0` | standard | `trace_mul_nonneg` (MatrixFacts) | – | proved* |
| T.MAT (i) | `M ⪰ 0`, `X ⪯ Y` ⇒ `tr(MX) ≤ tr(MY)` | C §3 | `trace_mul_le_trace_mul` | T.MAT-0 | proved* |
| T.MAT (ii) | `0 ⪯ N ⪯ λI` ⇒ `N² ⪯ λN`, `tr(MN²) ≤ λ tr(MN)` (`N = M`: `tr M³ ≤ ‖M‖tr M²`); `N ⪯ ‖N‖I`; `N ⪯ (tr N)I`; `tr(MN) ≤ tr M tr N` | C §3 | `posSemidef_smul_sub_mul_self`, `trace_mul_mul_self_le`, `posSemidef_opNorm_smul_sub`, `posSemidef_trace_smul_sub`, `trace_mul_le_trace_mul_trace` | T.MAT-0, `Common/Spectral` | proved* |
| T.MAT (iii) | `(H₁+H₂)² ⪯ 2H₁² + 2H₂²` | C §3 | `posSemidef_two_sq_add_two_sq_sub_sq` | – | proved* |
| T.MAT (iv) | `H ⪰ 0` ⇒ `H − H² ⪯ I − (I+H)⁻¹`; `0 ⪯ (I+H)⁻¹ ⪯ I`; trace forms | C §3, G3 | `posSemidef_one_sub_inv_sub`, `posSemidef_inv_one_add`, `posSemidef_one_sub_inv_one_add`, `trace_mul_sub_sq_le`, `trace_mul_inv_one_add_mem` | T.MAT-0 | proved* |
| T.MAT (v) | `(P+hI)⁻¹ ⪯ h⁻¹I`, `‖(P+hI)⁻¹‖ ≤ 1/h`; `P⁻¹ − (P+z)⁻¹ = zP⁻¹(P+z)⁻¹ ⪰ z(P+z)⁻²` | C §3 | `posSemidef_inv_smul_sub_inv_add`, `opNorm_inv_add_smul_le`, `inv_sub_inv_add_smul`, `posSemidef_inv_sub_inv_add_sub` | `Common/Spectral` | proved* |
| T.MAT (vi) | `(X²)[N,N] ⪰ (X[N,N])²` (`X` symmetric, `N ↪ V`) | C §3 | `posSemidef_submatrix_mul_self_sub` | `Common/OpNorm` | proved* |
| T.MAT (vii) | `‖Δ‖ ≤ ‖Y+Δ‖` for `Y, Δ ⪰ 0` | C §3 | `opNorm_le_opNorm_add` | `Common/Spectral` | proved* |
| T.MAT (viii) | `M ⪯ A`, `S ⪯ I` ⇒ `tr(M(I−S)) ≤ tr(A(I−S))` | C §3 | `trace_mul_one_sub_le` | T.MAT-0 | proved* |
| B5 | `α⁻¹tr(MH²) ≤ 8p²(‖M‖X₁t₊ + ‖N‖X₂t₋)`; with `‖M‖,‖N‖ ≤ L` | C §4.3 (B5), tex l.1300–1331 | `trace_mul_hess_sq_div_le`, `trace_mul_hess_sq_div_le'` (MatrixFacts) | T.MAT (i)–(iii) | proved* |
| T.BLG | BLmid under `gaussPi`: `𝖦[q_Tφ] ≤ 𝖦[tr(T(I+H)⁻¹)φ]`; constant `K = I + cA`: `𝖦[q_Tφ] ≤ tr(T(I+cA)⁻¹)𝖦φ`; Gaussian density | C §5.3 | `gaussE_qForm_mul_clipProd_le`, `gaussE_qForm_mul_clipProd_le_const`, `integral_gaussPi_eq`, `gaussPi_eq_withDensity` (GaussDensity) | T.ALPHA2-G, D-BLmid | proved* |
| T.GIBP2 | `2𝖦F = 𝖦[(tr A − q_A)α^{p−1}β^p]` (`p ≥ 3`, `A, B ⪰ 0`) | C §5, tex l.1248–1250 | `two_mul_gaussE_starF` (GIBP2) | `Gauss/IBP` (Stein) | proved* |
| T.COV (i) | `N_G ≥ 0` | C §7; A §2.9 | `gaussE_NG_nonneg` (Cov) | T.COV (ii) | proved* |
| T.COV (ii) | `N_G ≥ 𝖦g·2(p−1)tr A²/(1+2(p−1)λ)` for `A ⪯ λI`; `λ = ‖A‖`; `≥ f_G w` (`p ≥ 2`) | C §5.3 (a); A (C1b) | `trace_sub_trace_mul_inv_ge`, `gaussE_NG_ge_of_le`, `gaussE_NG_ge_opNorm`, `gaussE_NG_ge_whitened` | T.BLG, T.MAT | proved* |
| T.COV (iii) | B2: `𝖦[g·tr(M(H−H²))] ≤ 2𝖦F` (`p ≥ 3`, `M ⪯ A`, `N ⪯ B`); expanded B2 | C §4.3 (B2) | `gaussE_starG_trace_le`, `gaussE_starPhi_B2_le` | T.BLG, T.GIBP2, T.MAT (iv) | proved* |
| T.IL | `E X ≤ m`, `0 < θ ≤ m`, `‖X‖₂ ≤ B_X`, `‖Y‖_{2k} ≤ B_Y` ⇒ `E[XY] ≤ mθ^{−1/k}B_X^{1/k}B_Y`; Hölder core `E[XY] ≤ (EX)^{1−1/k}(E[XY^k])^{1/k}` | C §3 | `wavg_mul_le_interp`, `wavg_mul_le_holder`, `wavg_mul_sq_le` (Interp) | – | proved* |
| T.DSTAR | `E[(max_S X_u)^m] ≤ \|S\| max E[X_u^m]`; root form | C §3 | `wavg_sup_pow_le`, `wavg_sup_pow_rpow_le` (Interp) | – | proved* |
| UMI | `‖Y‖_k ≤ M`, `‖Z‖_k ≤ B`, `k ≥ 2`, `θ > 0` ⇒ `E[YZ] ≤ B(M/θ)^{1/(k−1)}(EY+θ)` | D §2.6 | `wavg_mul_le_umi`, `wavg_mul_pow_pred_le` (Interp) | T.IL Hölder core | proved* |

Finite weighted averages: `wavg w f = Σ w f / Σ w` (`w ≥ 0`, `Σ w > 0`), and
`lawE G p a y⁺ y⁻ S f = wavg (wt G p a y⁺ y⁻ · S) f` by `rfl` (`lawE_eq_wavg`), so T.IL, T.DSTAR
and UMI apply to the paired law directly. Norms are written through moments
(`‖X‖_k ≤ B` as `wavg w (X^k) ≤ B^k`).

## Sketches and checks (rule 2)

### T.ALPHA2
*Sketch.* `q_A(z+w) + q_A(z−w) = 2q_A(z) + 2q_A(w)` (any matrix). If `u = 1 − q_A(z+w) ≤ 0` or
`v = 1 − q_A(z−w) ≤ 0` the left side is `0`. Otherwise `u + v = 2(α − Q)` with
`α = 1 − q_A(z)`, `Q = q_A(w) ≥ 0`, so `α > Q ≥ 0`; AM–GM `uv ≤ (α − Q)²` and
`0 < α − Q = α(1 − Q/α) ≤ α e^{−Q/α}`. If `q_A(z) ≥ 1` then `u + v ≤ −2Q ≤ 0`, so the product is
`0`, and the right side is `0` too (`clipF A z = 0`). Constant form: `α ≤ 1 ⇒ Q/α ≥ Q`. Powered
form: raise to the powers `m, m'` and multiply (valid for all `m, m'`, with `x/0 = 0`); the `H`
variant uses `q_M ≤ q_A`, `q_N ≤ q_B` and `2m/α ≥ 0`. Gaussian form:
`|z+w|² + |z−w|² = 2|z|² + 2|w|²` and `⟨w,(I+H)w⟩ = |w|² + ⟨w,Hw⟩`.
*Checks.* `A = 0`: `α ≡ 1`, both sides `1`. `w = 0`: equality. `ι` empty: equality.
`q_A(z) ≥ 1`: both sides `0`. One dimension, `A = 1`, `z = 1/2`, `w = 1/4`:
`(1 − 9/16)(1 − 1/16) = 0.41 ≤ (3/4)² e^{−(1/8)/(3/4)} = 0.476`. The audit verified 20000 random
cases (`auditC_numeric.py` (d)). Serves: BLmid's `hmid` with `K = I + H`, `κ = 1`, exactly
the hypothesis shape of `integral_quad_le_of_midpoint`.

### T.MAT
*Sketches.* (0) `tr(XY) = Σ_{ij} X_ij Y_ij = 1ᵀ(X⊙Y)1 ≥ 0` (`PosSemidef.hadamard`).
(i) `tr(M(Y−X)) ≥ 0`. (ii) For `λ > 0`, `λ(λN − N²) = N(λ−N)N + (λ−N)N(λ−N)`, both congruences
of PSD matrices; for `λ = 0`, `N ⪰ 0 ⪰ N` forces `N = 0`; then `tr(M(λN − N²)) ≥ 0`.
`N ⪯ ‖N‖I` from `opNorm_le_iff_posSemidef` (Common/Spectral); `‖N‖ = max λᵢ ≤ Σλᵢ = tr N`.
(iii) `2H₁² + 2H₂² − (H₁+H₂)² = (H₁−H₂)ᵀ(H₁−H₂)`. (iv) With `K = I + H` (invertible, symmetric),
`K(I − K⁻¹ − H + H²)K = K² − K − KHK + KH²K = H⁴ + H³ = H(H + H²)H ⪰ 0`; congruence by an
invertible matrix preserves PSD (`IsUnit.posSemidef_star_left_conjugate_iff`). Similarly
`K(I − K⁻¹)K = H + H²` and `K K⁻¹ K = K`. (v) `K = P + hI`:
`K(h⁻¹I − K⁻¹)K = h⁻¹P² + P`; the identity from `P⁻¹((P+z) − P)(P+z)⁻¹`; and
`P⁻¹ − (P+z)⁻¹ − z(P+z)⁻² = z²(P+z)⁻¹P⁻¹(P+z)⁻¹` (commuting inverses). (vi) For `x : κ → ℝ`
extended by zero to `y`, `xᵀ[(X²)_{NN} − X_{NN}²]x = |Xy|² − Σ_{a}(Xy)_{f a}² ≥ 0`.
(vii) `‖Y+Δ‖I − Δ = (‖Y+Δ‖I − (Y+Δ)) + Y ⪰ 0` and `‖Y+Δ‖I + Δ ⪰ 0`. (viii) `tr((A−M)(I−S)) ≥ 0`.
*Checks.* All hold with equality for `ι` empty and for `1×1` matrices with the equality cases
`H = 0`, `z = 0`, `P = 0` (in (v), `(hI)⁻¹ = h⁻¹I`). (ii) `1×1`: `n² ≤ λn` for `0 ≤ n ≤ λ`.
(vi) with `f` non-injective is false (`f` constant, `κ` of size 2: `(X²)_{ii} = Σ_k X_ik²` vs
`2X_ii²`), hence the injectivity hypothesis.

### B5
*Sketch.* `H = H₁ + H₂`, `H₁ = c₁M`, `H₂ = c₂N`, `c₁ = 2(p−1)/α`, `c₂ = 2p/β`. By (iii) and (i),
`tr(MH²) ≤ 2c₁² tr M³ + 2c₂² tr(MN²)`; by (ii), `tr M³ ≤ ‖M‖ tr M²` and `tr(MN²) ≤ ‖N‖ tr(MN)`;
`tr M³ ≥ 0` and `(p−1)² ≤ p²`. Divide by `α`.
*Checks.* `p = 0`: both sides `0`. `M = 0`: both sides `0`. `1×1`, `M = N = 1`, `α = β = 1`,
`p = 1`: `H = 2`, `tr(MH²) = 4 ≤ 8(1 + 1) = 16`.

### T.BLG
*Sketch.* `gaussPi = volume.withDensity (∏ φ₁(xᵢ))` by `Measure.pi_eq` on boxes (product of
indicators, `integral_fintype_prod_eq_prod`, `gaussianReal_apply_eq_integral`);
`∏ φ₁(xᵢ) = (2π)^{−n/2}e^{−|x|²/2}`; so `𝖦f = c∫ f e^{−|x|²/2}` for all `f`. Apply BLmid's trace
form to `ρ = gaussWt φ` (measurable, `≥ 0`, even) and `K = I + H` (measurable entrywise,
symmetric, `⟨w,Kw⟩ ≥ |w|²` since `H ⪰ 0`), `hmid` = T.ALPHA2-G; multiply by `c > 0`.
*Checks.* `T = 0`: `0 ≤ 0`. `A = B = M = N = 0`: `φ ≡ 1`, `H = 0`, and the claim
`𝖦 q_T ≤ tr T` is an equality (`𝖦 xxᵀ = I`). Constant form with `c = 0`: `𝖦[q_Tφ] ≤ tr T 𝖦φ`,
equality at `φ ≡ 1`.

### T.GIBP2
*Sketch.* See the file docstring: Stein on `fᵢ = (Ax)ᵢ g`, summed over `i`.
`t ↦ (t₊)^k` has derivative `k(t₊)^{k−1}` for `k ≥ 2` (here `k = p−1` and `k = p`), and the line
derivative of `q_A(x + te_i)` is `2(Ax)ᵢ` (`A` symmetric). Polynomial bounds: `|g| ≤ 1`,
`|(Ax)ᵢ| ≤ (Σ|A_jk|)‖x‖`, so `|fᵢ| ≤ K(1+‖x‖)` and `|∂ᵢfᵢ| ≤ K(1+‖x‖)²`.
*Checks.* `A = 0`: both sides `0`. `ι` empty: both `0`. One dimension, `B = 0`, `A = a`, `p = 3`:
`F = 2a²x²(1−ax²)₊`, `g = (1−ax²)₊²`, the identity reads `𝖦[4a²x²(1−ax²)₊] =
𝖦[(a − ax²)(1−ax²)₊²]`, the Stein identity for `ax(1−ax²)₊²`. The audit checked the identity
by 2-D quadrature to 7 digits.

### T.COV
*Sketch.* (ii) `N_G = tr A·𝖦g − 𝖦[q_Ag]` (integrable: `0 ≤ g ≤ 1`, `q_A` polynomial); T.BLG
constant with `T = A`, `c = 2(p−1)`, `m = p−1`; matrix input: with `K = I + cA`, `R = K⁻¹`,
`I − R = cRA`, so `tr A − tr(AR) = c tr(RA²)`; and `tr A² = tr(RA²) + c tr(RA³)`,
`λ tr(RA²) − tr(RA³) = tr(R·A(λI − A)A) ≥ 0`, so `(1 + cλ)tr(RA²) ≥ tr A²`.
(i) from (ii) (right side `≥ 0`). Whitened: `λ = tr A` (`A ⪯ (tr A)I`), `c ≥ 1 ⇒
c/(1+cλ) ≥ 1/(1+λ)`, and `Φ ≤ g` (`α ≤ 1`). (iii) as in the file docstring.
*Checks.* `A = 0`: `N_G = 0`, bounds `0`. `B = 0, p = 1`: `g = 1`, `N_G = tr A − 𝖦q_A = 0` and
the (ii) bound is `0` (`c = 0`). One dimension, `B = 0`, `p = 2`, `A = a ∈ [0,1]`:
`N_G = a𝖦[(1−x²)(1−ax²)₊]`; for `a = 1`, `𝖦[(1−x²)²1_{|x|<1}] = 0.3975…` vs the bound
`𝖦[(1−x²)₊]·2/3 = 0.3226…` (midpoint quadrature): holds. Serves D6 (`N_G ≥ 0`, `N_G ≥ f_G w`) and B1 (B2).

### T.IL, T.DSTAR, UMI
*Sketches.* In the file docstring (Hölder with weights `wX`; Cauchy–Schwarz; `(max X)^m ≤ ΣX^m`;
UMI by `E[YZ] ≤ (EY)^{1−λ}(E[YZ^{k−1}])^λ`, `λ = 1/(k−1)`, and `E[YZ^{k−1}] ≤ M B^{k−1}`, then
the split `EY ≥ θ` / `EY < θ`).
*Checks.* T.IL `k = 1`: `E[XY] ≤ m θ^{-1}B_X B_Y`, from `E[XY] ≤ B_X B_Y` and `m/θ ≥ 1`.
Constants `X ≡ x`, `Y ≡ y`: `xy ≤ m θ^{−1/k}x^{1/k}y` since `x ≤ m`, `θ ≤ m`
(`x^{1−1/k} ≤ m^{1−1/k} ≤ mθ^{−1/k}`). UMI `Y ≡ M`, `Z ≡ B`: `MB ≤ B(M/θ)^{1/(k−1)}(M + θ)`:
if `M ≥ θ` then `(M/θ)^λ ≥ 1`; if `M < θ` then `M ≤ θ(M/θ)^λ` since `(M/θ)^{1−λ} ≤ 1`. T.DSTAR
`|S| = 1`: equality.

## Deviations from the audit's wording

* **T.ALPHA2.** Only AM–GM is used (`uv ≤ ((u+v)/2)²`), not the exact identity
  `α(z+w)α(z−w) = (α(z)−q_A(w))² − 4(zᵀAw)²`; no symmetry of `A` is needed. With `x/0 = 0` one
  inequality covers the support and its complement, and the powered forms hold for every
  `m, m' ∈ ℕ` (the task's `m, m' ≥ 1` is not needed). The constant-modulus Gaussian form needs
  only `c ≤ 2m` (BLmid then needs `c ≥ 0` for `κ = 1`, which `gaussE_qForm_mul_clipProd_le_const`
  assumes).
* **`H` off the support.** `clipHess m m' A B M N x = (2m/α(x))M + (2m'/β(x))N` with `x/0 = 0`.
  It is PSD everywhere, so `(I + H)⁻¹` and T.MAT (iv) apply pointwise; on `{φ = 0}` its value is
  irrelevant because the weight vanishes.
* **`F`.** `starF` uses the coefficient `((p − 1 : ℕ) : ℝ)`, equal to the paper's `p − 1` for
  `p ≥ 1`; T.GIBP2 needs `p ≥ 3` (so that `α₊^{p−1}` is `C¹`).
* **T.COV.** (i) and (ii) hold for every `p` (with `c = 2(p−1 : ℕ)`); the whitened form needs
  `p ≥ 2` (`c ≥ 1`). (ii) is stated for any `λ ≥ 0` with `A ⪯ λI`, with corollaries `λ = ‖A‖`
  (the audit's form) and `λ = tr A`. (iii) replaces T.MAT (viii) by a second BLmid application
  with `K = I` to the PSD matrix `A − M`.
* **B5** is stated for `p ∈ ℕ` (`p = 0` gives `0 ≤ 0`), with explicit `‖M‖`, `‖N‖` and a corollary
  with a common bound `L` (`L = s a²/h` in B1).
* **T.IL** holds for `k ≥ 1` (audit: `k ≥ 2`). **UMI** as in AUDIT-D §2.6 (`k ≥ 2`).
* **T.MAT (vi)** needs the reindexing `N → V` to be injective (false otherwise; see the checks).
* Helper lemmas reproved privately (to avoid importing files under active development):
  `hasDerivAt_posPart_pow` (same as `GCIDeriv.hasDerivAt_max_zero_pow`) in `GIBP2.lean`.
