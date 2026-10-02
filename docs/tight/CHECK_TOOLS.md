# CHECK_TOOLS: rule-2 statement checks for the Tools and SourceMax files

Pre-dispatch checks (workflow rule 2: proof sketch, small and degenerate cases, satisfiability)
for every theorem stated in `BiluLinial/Tight/Tools/{MatrixFacts,Interp,Alpha2,Cov,GaussDensity,
GIBP2}.lean` and `BiluLinial/Tight/SourceMax.lean`, `BiluLinial/Tight/SourceMax/{Glue,Law,Phys,
Jacobian,Deriv,FOC,LinAlg}.lean`. No Lean file was edited.

**Scripts** (all under `scripts/tight/`, run with `/tmp/tight-venv/bin/python`):
`check_tools_matrix.py` (T.MAT, B5, Cov matrix input, Interp), `check_tools_gauss.py` (Alpha2,
GaussDensity, GIBP2, Cov by quadrature, n = 0..3), `check_tools_gibp2_1d.py` (T.GIBP2 exactly:
adaptive 1-D quadrature and 2-D polar quadrature), `check_tools_sourcemax.py` (an exact enumerator of
the normalized paired law, with Lean's junk values: inverse of a singular matrix = 0,
`√(negative) = 0`, `x/0 = 0`).

**File snapshots read** (2026-09-30, local time; the files were still being edited):

| file | read at | mtime of the version checked | `sorry` count at that time |
|---|---|---|---|
| Tools/MatrixFacts | 22:22, again 22:33 | 22:25:36 | 0 (proved) |
| Tools/Interp | 22:22, again 22:33 | 22:28:23 | 0 (proved) |
| Tools/Alpha2 | 22:22, again 22:34 | 22:22:34 | 0 (proved) |
| Tools/Cov | 22:22 | 22:18:10 | 7 |
| Tools/GaussDensity | 22:22, again 22:33 | 22:30:44 | 0 (proved) |
| Tools/GIBP2 | 22:22, again 22:36 | 22:35:16 | 0 (proved) |
| SourceMax | 22:22, again 22:33 | 22:31:35 | 0 (proved from its children) |
| SourceMax/Glue | 22:22, again 22:33 | 22:24:14 | 0 (proved) |
| SourceMax/Law | 22:22, again 22:36 | 22:36:03 (statements identical to 22:33:51) | 0 (proved) |
| SourceMax/Phys | 22:22, again 22:33 | 22:25:44 | 12 |
| SourceMax/Jacobian | 22:22 | 22:15:35 | 1 |
| SourceMax/Deriv | 22:22 | 22:15:40 | 1 |
| SourceMax/FOC | 22:22 | 22:15:45 | 1 |
| SourceMax/LinAlg | 22:22, again 22:33 | 22:31:35 | 5 |

## Summary

**No statement is FALSE.** One statement **failed to elaborate** in the 22:15 version and was
fixed by its owner at 22:31 (see LinAlg below). Everything else is **OK**: its hypotheses suffice,
it survives every degenerate case tried, and it agrees numerically with the source.

* `le_mulVec_of_mulVec_le` (SourceMax/LinAlg), version 22:15:49: `(hKB : K * B = 1)` over
  `{n : Type*} [Fintype n]` with no `[DecidableEq n]`. The literal `1 : Matrix n n ℝ` needs
  `DecidableEq n`, so the declaration did not typecheck (checked with a scratch file:
  `failed to synthesize OfNat (Matrix n n ℝ) 1`). **Fixed** in the 22:31:35 version, which has
  `[DecidableEq n]`.
* Hypotheses whose necessity the tests confirm (none may be dropped):
  * `k + 2 ≤ p` in `hasDerivAt_glue` / `hasDerivAt_moment`: at a support boundary of `K4` the
    one-sided slopes differ for `p = k + 1`.
  * `k + 1 ≤ p` in `continuousOn_moment`: at `k = p` the moment jumps by `0.0043` across the same
    boundary.
  * `3 ≤ p` in `two_mul_gaussE_starF`: at `p = 2` the identity fails, `0.389 ≠ 0.350`. Lean's
    `α^0 = 1` makes `starF` nonzero off the support of `α`.
  * `c ≤ 2m` in the constant-modulus BLG: with `c = 6m` the bound fails by `0.17`.
  * `P ≻ 0` in `inv_sub_inv_add_smul`: false for a singular PSD `P`, where Lean has `P⁻¹ = 0`.
  * Injectivity in (vi): a constant `f` gives a negative eigenvalue (`-8`).
  * `y ≥ 0` in `precN_eq_scale`: false with a negative source.
* Docstring-only remarks (no change needed to any statement):
  * `gaussE_qForm_mul_clipProd_le` says "`m, m' ≥ 1`", but the statement has no such hypothesis.
    The statement holds for every `m, m'`, including `0` (tested).
  * `gaussWt_clipProd_midpoint_const` dropped `0 ≤ c` at 22:22. It is still true for every
    `c ≤ 2m`: a negative `c` only enlarges the right side.
  * `BP_TOOLS.md`'s T.MAT-0 sketch cites `PosSemidef.hadamard`, which does not exist in Mathlib
    (only `IsHermitian.hadamard` does). This is moot, since the lemma is proved.
  * `walkB_symm` duplicates `walkB_comm` (`Walk.lean`, already proved).
* Satisfiability (check 4):
  * `TRegime` holds for `p = 10⁶`, `d = 10⁵¹` (`p¹⁷ = d²`).
  * `CapCtx G d p S λ` holds for every `λ ∈ [0, 1]` when `S = ∅`, `S = {v}` or `S` is one edge. In
    those cases `P̃⁺ = diag(1+c) ± …` has `det = 1 + c > 0` and `h ≡ 1` exactly (enumerator), so the
    caps hold since `r > 1`, and `ih` concerns only such sets.
  * `ContactCtx` needs a mean exactly equal to `r`. The contact exclusion derives a contradiction
    from it, so it is expected to be unsatisfiable in the regime once the main theorem is proved.
    It is meant to be used only inside that argument, so non-vacuity cannot (and need not) be
    shown. Small graphs never have a contact (`h ≡ 1` for `|S| ≤ 2`).

---

## Tools/MatrixFacts.lean (T.MAT, B5) — all proved; statements checked

Evidence for all (`check_tools_matrix.py`): 6000 random trials, sizes 0..6. The matrix kinds are
generic, zero, rank-one, singular of random rank, ill-conditioned (`10⁻⁸..10³`) and large.
Result: 0 failures for every lemma below. `ι` empty: every statement reduces to `0 ≤ 0` or `0 = 0`.

| lemma | verdict | Lean-level sketch (Mathlib names) |
|---|---|---|
| `trace_mul_nonneg` | OK | `X = BᵀB` (`exists_eq_transpose_mul_self`, Gauss/BLmid, or `CStarAlgebra.nonneg_iff_eq_star_mul_self`); `tr(BᵀBY) = tr(BYBᵀ)` (`Matrix.trace_mul_comm`); `BYBᵀ ⪰ 0` (`PosSemidef.mul_mul_conjTranspose_same`); `PosSemidef.trace_nonneg`. |
| `trace_mul_le_trace_mul` | OK | `tr(MY) - tr(MX) = tr(M(Y-X)) ≥ 0` (`Matrix.mul_sub`, `trace_sub`, T.MAT-0). No symmetry of `X, Y` needed. |
| `posSemidef_smul_sub_mul_self` | OK | For `λ > 0`: `λ(λN - N²) = N(λ-N)N + (λ-N)N(λ-N)`, both terms congruences of PSD matrices (`conjTranspose_mul_mul_same`); `λ = 0`: `N = 0`. 1×1: `n² ≤ λn` for `0 ≤ n ≤ λ`. |
| `trace_mul_mul_self_le` | OK | previous lemma and T.MAT-0. |
| `posSemidef_opNorm_smul_sub` | OK | `Common/Spectral.opNorm_le_iff_posSemidef` with `r = ‖N‖`. |
| `opNorm_le_trace`, `posSemidef_trace_smul_sub` | OK | `opNorm_eq_norm_eigenvalues`, `PosSemidef.eigenvalues_nonneg`, `trace_eq_sum_eigenvalues`. |
| `trace_mul_le_trace_mul_trace` | OK | `N ⪯ (tr N) I` and (i). |
| `posSemidef_two_sq_add_two_sq_sub_sq` | OK | the difference is `(H₁-H₂)ᵀ(H₁-H₂)` (`posSemidef_conjTranspose_mul_self`), using symmetry. |
| `posDef_one_add`, `posSemidef_inv_one_add`, `posSemidef_one_sub_inv_one_add`, `posSemidef_one_sub_inv_sub` | OK | `K = I + H ≻ 0` (so the inverse is genuine, no junk); congruence by `K` (`IsUnit.posSemidef_star_left_conjugate_iff`): `K(I - K⁻¹ - H + H²)K = H(H+H²)H`. Per eigenvalue: `h³/(1+h) ≥ 0`. |
| `trace_mul_sub_sq_le`, `trace_mul_inv_one_add_mem` | OK | (iv) with T.MAT-0. |
| `posDef_add_smul_one`, `posSemidef_inv_smul_sub_inv_add`, `opNorm_inv_add_smul_le` | OK | `h > 0` makes `P + hI ≻ 0`; `K(h⁻¹I - K⁻¹)K = h⁻¹P² + P`. At `h = 0` the statement would be false (junk `0⁻¹ = 0`), so `0 < h` is needed and is present. |
| `inv_sub_inv_add_smul`, `posSemidef_inv_sub_inv_add_sub` | OK | `P⁻¹((P+z) - P)(P+z)⁻¹` (`Matrix.nonsing_inv_mul`, `Matrix.mul_nonsing_inv`); the remainder is `z²(P+z)⁻¹P⁻¹(P+z)⁻¹`. False for a singular PSD `P` (junk), so `P ≻ 0` is needed and is present. |
| `posSemidef_submatrix_mul_self_sub` | OK | `(X²)_{ff} - X_{ff}² = Σ_{k ∉ range f} X_{f·,k}X_{k,f·} = YYᵀ`; needs `Function.Injective f` (constant `f`: eigenvalue `-8`). |
| `opNorm_le_opNorm_add` | OK | `‖Y+Δ‖I - Δ = (‖Y+Δ‖I - (Y+Δ)) + Y ⪰ 0`, `‖Y+Δ‖I + Δ ⪰ 0`; `opNorm_le_iff_posSemidef`. |
| `trace_mul_one_sub_le` | OK | `tr((A-M)(I-S)) ≥ 0`; `M` need not be PSD. |
| `trace_mul_hess_sq_div_le` (B5) | OK | `H = c₁M + c₂N`, `c₁ = 2(p-1)/a`, `c₂ = 2p/b`. By (iii) and (i), `tr(MH²) ≤ 2c₁²tr M³ + 2c₂²tr(MN²)`. By (ii) with `λ = ‖M‖, ‖N‖` (`posSemidef_opNorm_smul_sub`), `tr M³ ≤ ‖M‖tr M²` and `tr(MN²) ≤ ‖N‖tr(MN)`. Finally `(p-1 : ℕ)² ≤ p²`. `p = 0`: both sides `0`. |
| `trace_mul_hess_sq_div_le'` | OK | B5 with `tr M² ≥ 0` and `tr(MN) ≥ 0` (T.MAT-0). |
| helpers `posSemidef_mul_self`, `posSemidef_of_mul_mul`, `dotProduct_mulVec_comm_of_symm` | OK | standard; `posSemidef_of_mul_mul` needs `K` symmetric and a unit, both present. |

## Tools/Interp.lean (T.IL, T.DSTAR, UMI) — all proved; statements checked

Evidence: 20000 random trials (`check_tools_matrix.py`). Ω has 1..8 points; weights are ≥ 0 with
about 20 % zero; `X, Y ≥ 0` with zeros; 5 % of trials have `X ≡ 0`; `k = 1..5`. The constants are
taken at the tight boundary (`m = EX`, `B_X = (EX²)^{1/2}`, `B_Y = (EY^{2k})^{1/(2k)}`, `θ ∈ (0, m]`;
for UMI, `M`, `B` equal to the actual norms). Result: 0 failures.

| lemma | verdict | sketch |
|---|---|---|
| `lawE_eq_wavg` | OK | `rfl` (`Zw = Σ wt`). |
| `wavg_mono`, `wavg_nonneg`, `wavg_const`, `wavg_sum` | OK | `div_le_div_of_nonneg_right`, `Finset.sum_le_sum`; `wavg_nonneg` and `wavg_sum` hold even when `Σw = 0` (both sides 0). |
| `wavg_mul_le_holder` | OK | Weighted Hölder with weights `wX`: `Real.inner_le_Lp_mul_Lq_of_nonneg` with exponents `(k/(k-1), k)`, or Jensen `Real.rpow_arith_mean_le_arith_mean_rpow`. `k = 1`: `Real.rpow_zero` makes it an equality (also at `EX = 0`, as `0^0 = 1`). |
| `wavg_mul_sq_le` | OK | Cauchy–Schwarz (`inner_mul_le_norm_mul_norm`, or `Finset.inner_mul_le_norm_mul_norm`). The 22:28 version dropped `hW`; still true, since `Σw = 0` gives `0 ≤ 0`. |
| `wavg_mul_le_interp` (T.IL) | OK | Hölder core, then `E[XY^k] ≤ B_X B_Y^k` (Cauchy–Schwarz, `Real.sqrt_le_sqrt`, `pow_le_pow_left₀`), then `m^{1-1/k} ≤ mθ^{-1/k}` (`Real.rpow_le_rpow_of_exponent_nonpos`, `θ ≤ m`). Constants come from the hypotheses. |
| `wavg_sup_pow_le`, `wavg_sup_pow_rpow_le` (T.DSTAR) | OK | `(sup' X)^m ≤ Σ_{u∈S} X_u^m` (`Finset.exists_mem_eq_sup'`, `Finset.single_le_sum`); `m = 0`: `1 ≤ |S|B` since `B ≥ E 1 = 1`; root form by `Real.rpow_le_rpow`, `Real.mul_rpow`, `Real.pow_rpow_inv_natCast`. |
| `wavg_mul_le_holder_conj`, `wavg_mul_pow_pred_le` | OK | Weighted Hölder with `p.HolderConjugate q`; `k = 1` reduces to `EY ≤ EY`. |
| `wavg_mul_le_umi` (UMI) | OK | Hölder core with `k-1`, then `wavg_mul_pow_pred_le`, giving `E[YZ] ≤ s^{1-λ}M^λB` (`λ = 1/(k-1)`). Then `s^{1-λ}θ^λ ≤ (1-λ)s + λθ ≤ s + θ` (`Real.geom_mean_le_arith_mean2_weighted`). `M = 0` forces `Y = 0` on the support, both sides `0`; `k = 2`: `MB ≤ BM(EY/θ + 1)`. |

## Tools/Alpha2.lean (T.ALPHA2) — all proved (no `sorry`); statements checked

Verdict **OK** for all lemmas (`qForm_*`, `clipF_*`, `clipF_add_mul_clipF_sub_le(_exp/_eq_zero)`,
`clipProd_*`, `clipHess_posSemidef`, `dotProduct_clipHess_mulVec`, `gaussWt_*`,
`gaussWt_clipProd_midpoint(_const)`). The proofs are in the file and match the BP_TOOLS sketch:
the parallelogram law, AM–GM, `1 + t ≤ eᵗ` (`Real.add_one_le_exp`), and `x/0 = 0` off the support.
The 22:22 version of `gaussWt_clipProd_midpoint_const` has only `c ≤ 2m`. This is still true:
for `c ≤ 0`, `exp(-c q_A(w)) ≥ 1`. Evidence: 20000 pointwise trials (`n = 1..4`; generic,
rank-one and zero `A`): 0 failures. The constant form fails for `c = 6m` (by `0.17` after Gaussian
integration), so `c ≤ 2m` is needed.

## Tools/GaussDensity.lean (T.BLG) — all proved; statements checked

| lemma | verdict | sketch / evidence |
|---|---|---|
| `prod_gaussianPDFReal` | OK | `gaussianPDFReal_zero_one` (Gauss/IBP), `Finset.prod_mul_distrib`, `Real.exp_sum`; empty `ι`: `1 = 1`. |
| `gaussPi_eq_withDensity` | OK | `Measure.pi_eq` on boxes with `gaussianReal_of_var_ne_zero`; empty `ι`: both sides are `dirac`. |
| `integral_gaussPi_eq`, `gaussE_eq` | OK | Holds for **every** `f`, integrable or not: `integral_withDensity_eq_integral_smul` (`ofReal` density written as `↑(Real.toNNReal …)`) has no integrability hypothesis, and `integral_mul_left` (or `integral_const_mul`) holds always. So there is no Bochner-integral junk trap here. |
| `measurable_prod_gaussianPDFReal`, `measurable_one_add_clipHess`, `measurable_gaussWt_clipProd` | OK | `Measurable.div` / `continuous_clipF`; `x/0 = 0` is measurable. |
| `gaussE_qForm_mul_clipProd_le` | OK | BLmid trace form (`integral_quad_le_of_midpoint`) with `ρ = gaussWt (clipProd m m' A B)`, `K = I + clipHess`, `κ = 1` (`⟨w,Kw⟩ ≥ |w|²` since `clipHess_posSemidef`), and `hmid = gaussWt_clipProd_midpoint`; then multiply by `(2π)^{-n/2}` (`integral_gaussPi_eq`). `(I + H)⁻¹` is genuine, since `I + H ≻ 0`. Valid for all `m, m'` (the docstring's "`m, m' ≥ 1`" is unnecessary). Evidence: 110 parameter sets, n = 0..3, with `M = A`, `N = B`, `M = 0` and random `0 ⪯ M ⪯ A`; 0 failures. |
| `gaussE_qForm_mul_clipProd_le_const` | OK | the same with the constant `K = I + cA`, `0 ≤ c ≤ 2m` (`gaussWt_clipProd_midpoint_const`); `∫ tr(T K⁻¹)ρ = tr(T K⁻¹)∫ρ` (`integral_mul_left`). Evidence: 330 sets (`c ∈ {0, random, 2m}`); 0 failures. |

## Tools/GIBP2.lean — `two_mul_gaussE_starF` — proved at 22:35; statement checked

**OK.** Sketch: Stein along coordinate lines (`stein_gaussPi_of_hasDerivAt`, Gauss/IBP) for
`f_i = (Ax)_i g`, with `g = α^{p-1}β^p` and `∂_i g = -2(p-1)α^{p-2}β^p(Ax)_i - 2pα^{p-1}β^{p-1}(Bx)_i`.
This uses `t ↦ max(t,0)^k ∈ C¹` for `k ≥ 2` (`p - 1 ≥ 2`). The polynomial bounds have `m = 2` and
`K = O(p Σ|A_jk| (Σ|A_jk| + Σ|B_jk|))`, chosen after `A, B, p`. Summing over `i` with `Aᵀ = A` gives
`Σ x_i(Ax)_i = q_A`, `Σ(Ax)_i² = q_{A²}` and `Σ(Ax)_i(Bx)_i = q_{AB}`, so
`𝖦[q_A g] = tr A 𝖦g - 2𝖦F`; the integrands are polynomially bounded, so `integral_sub` applies.

Evidence (`check_tools_gibp2_1d.py`):
* n = 1, adaptive quadrature split at `|x| = a^{-1/2}, b^{-1/2}`, 400 cases (`a, b ∈ {0} ∪ [10⁻², 10²]`,
  `p ∈ {3,4,5,8,20}`): worst relative residual `7·10⁻¹⁶`.
* n = 2, polar quadrature with general non-commuting PSD `A, B` (including rank one and zero):
  `2.6·10⁻¹⁰`.
* Uniform grids, n = 1..3: residuals at most `3·10⁻⁵` relative, except one 2-D case with
  `eig(A) = 25.8` (support about 9 grid points wide), where the grid misses by `2·10⁻³`. The polar
  value there is exact (`1.0538495909 = 1.0538495909`).
* The docstring check `p = 3`, `B = 0` matches to 12 digits.
* `p = 2` (excluded by `3 ≤ p`): `0.389 ≠ 0.350`, because `clipF A x ^ 0 = 1` off the support.

## Tools/Cov.lean (T.COV) — 7 `sorry`, statements checked

Evidence (`check_tools_gauss.py`): quadrature, n = 0..3, 110 parameter sets. `A, B` are generic,
rank-one or zero with scales `10^{-1..1.3}`; `p ∈ {0,1,2,3,4,6,12}`; `(M, N)` is random with
`0 ⪯ M ⪯ A`, or `(A, B)`, `(0, 0)` or `(A, 0)`. Result: 0 failures for every statement. The
BP_TOOLS numbers (`N_G = 0.3975`, bound `0.3226`) are reproduced.

* **`trace_sub_trace_mul_inv_ge`** — OK. Sketch: `R = (I + cA)⁻¹`, genuine since
  `posDef_one_add (hA.smul hc)`. Diagonalize (`IsHermitian.spectral_theorem` /
  `Common/Spectral.spectral_theorem_real`); per eigenvalue `0 ≤ a ≤ λ` (`hAl` gives `a ≤ λ`):
  `a - a/(1+ca) = ca²/(1+ca) ≥ ca²/(1+cλ)`. Alternatively, trace identities:
  `tr A - tr(AR) = c tr(RA²)` and `(1+cλ)tr(RA²) - tr A² = c tr(R·A(λ-A)A) ≥ 0` (T.MAT-0,
  `posSemidef_inv_one_add`). Evidence: 6000 matrix trials (`c` up to `10³`, `λ ∈ {‖A‖, 3‖A‖}`), 0 failures.
* **`gaussE_NG_ge_of_le`** — OK. Sketch: `N_G = tr A 𝖦g - 𝖦[q_A g]` (`integral_sub`, `integral_mul_left`).
  Integrability: `|q_A g| ≤ ‖A‖·n·‖x‖²` (`integrable_of_polyBound_gaussPi`, m = 2), and `0 ≤ g ≤ 1`
  (`clipProd_le_one`). Then `gaussE_qForm_mul_clipProd_le_const` with `T = A`, `m = p-1`, `m' = p`
  and **constant `c = 2((p-1 : ℕ) : ℝ)`, chosen here** (`hc : c ≤ 2m` by `le_refl`, `0 ≤ c` by
  positivity). Finally `trace_sub_trace_mul_inv_ge` and `𝖦g ≥ 0` (`integral_nonneg`). `p ∈ {0,1}`:
  `c = 0`, and the bound is `0 ≤ N_G`.
* **`gaussE_NG_ge_opNorm`** — OK. Take `λ = opNorm A` (`norm_nonneg`, `posSemidef_opNorm_smul_sub hA.1`).
* **`gaussE_NG_ge_whitened`** (`p ≥ 2`) — OK. Take `λ = tr A` (`posSemidef_trace_smul_sub`,
  `PosSemidef.trace_nonneg`). Since `c = 2(p-1) ≥ 1`, `c/(1+cλ) ≥ 1/(1+λ)` (`div_le_div_iff₀`). And
  `Φ ≤ g` pointwise (`α ≤ 1`, `pow_le_pow_of_le_one`; `integral_mono`) times `tr A²/(1+tr A) ≥ 0`.
* **`gaussE_NG_nonneg`** — OK. Follows from `_opNorm`: the left side is `𝖦g · c tr A²/(1+cλ) ≥ 0`.
* **`gaussE_starG_trace_le`** (B2, `p ≥ 3`) — OK. Sketch:
  * Start from `2𝖦F = N_G` (`two_mul_gaussE_starF`) and split
    `N_G = 𝖦[(tr(A-M) - q_{A-M})g] + 𝖦[(tr M - q_M)g]` (`qForm_sub`, `trace_sub`, `integral_add`).
  * First term `≥ 0`: BLG const with `T = A - M`, `c = 0`.
  * Second term `≥ 𝖦[g tr(M(I - (I+H)⁻¹))]`: BLG variable with `T = M`, `m = p-1`, `m' = p`, so `H`
    matches `clipHess (p-1) p A B M N`.
  * Pointwise `tr(M(I-(I+H)⁻¹)) ≥ tr(M(H-H²))` (`trace_mul_sub_sq_le`, `clipHess_posSemidef`,
    `g ≥ 0`).
  * Integrability: `g·tr(M(H-H²))` is bounded, since its terms `α^{p-3}β^p`, `α^{p-2}β^{p-1}`,
    `α^{p-1}β^{p-2}` are bounded for `p ≥ 3`, and with `x/0 = 0` it vanishes off the support (the
    grid maximum stays bounded in every trial). Otherwise use the docstring's case split
    (non-integrable ⇒ the integral is `0 ≤ N_G`).
* **`gaussE_starPhi_B2_le`** — OK. The integrand equals `g·tr(M(H-H²))/2` pointwise: on the support
  by `field_simp` with `trace_add`/`trace_smul`; off it both are `0`, since `p-1 ≥ 1` and `p ≥ 1`
  give `zero_pow`. Checked to `10⁻⁹` relative on every grid point set. Then `integral_congr_ae`,
  `integral_div` and B2.

---

## SourceMax/Glue.lean — proved; statements checked

Verdict **OK** for `posPow`, `glue`, `glueDeriv`, `glue_zero`, `isOpen_posDef_family`,
`isClosed_posSemidef_family`, `continuous_ite_posDef_family`, `differentiableAt_det_of_entries`,
`hasDerivAt_det_add_diagonal`, `hasDerivAt_inv_add_diagonal` and `hasDerivAt_glue`. The proofs in
the file follow the docstring: Jacobi via `MultilinearMap.map_add_eq_map_add_linearDeriv_add`, the
inverse via `adjugate`, and the three cases PD / PSD-singular (`|glue| ≤ |det|²·φ = O(t²)`) / not PSD.
The `trace_state` left at line 309 in the 22:15 version is gone in the 22:24 version.

Evidence: 3000 finite-difference trials of `hasDerivAt_glue` (Richardson-extrapolated one-sided
slopes), `n = 1..4`, `Q₀` PD / singular PSD / indefinite, curves `δ(t) = tδ' + t²δ''`,
`k ∈ 0..3`, `p ∈ {k+2, k+3, k+4}`: 0 failures. At `Q₀ = 0` (1×1), `p = 1`, `k = 0`, the right and
left slopes are `1` and `0` (no derivative), so `k + 2 ≤ p` is needed.

## SourceMax/Law.lean — proved at 22:33; statements checked

Evidence: the exact enumerator, graphs `K1, K2, P3, K13, K3, C4, K4, paw, diamond`, random `S`.
Sources lie in `[0, s]` or `[0, 3s]` with zero sources and sources at the cap; `p ∈ {1,2,3,5,8}`;
`a ∈ {a(d,p), 2.5 a(d,p)}`. Result: 0 failures.

| lemma | verdict | sketch / evidence |
|---|---|---|
| `wt_nonneg`, `Zw_nonneg` | OK | `PosDef.det_pos`, `pow_nonneg`, `Finset.sum_nonneg`. 3393 configurations. |
| `lawE_add/sub/const_mul/zero/congr/nonneg` | OK | `Finset.sum_add_distrib`, `add_div`, `Finset.mul_sum`, `mul_div_assoc`; all hold even when `Zw = 0` (`x/0 = 0` on both sides). |
| `lawE_pow_succ_le` | OK | Jensen with normalized weights `wt/Zw` and exponent `(k+1)/k` applied to `f^k` (`Real.rpow_arith_mean_le_arith_mean_rpow`), raised to the `k`-th power; `k = 0`: `E 1 = 1` (needs `hZ`). 3625 checks. |
| `hN_pos` | OK | `wt ≠ 0` ⇒ `P̃⁺ ≻ 0` ⇒ `PosDef.inv`, `PosDef.diag_pos`. 12933 checks. |
| `lawE_hN_pow_of_source_zero` | OK | At `y_i = 0` row/column `i` of `P̃⁺` is `e_i`: `D_i = 1 + Σ cRoot(0) = 1` (`Real.sqrt_one`), and the off-diagonal entries contain `√0 = 0`. So `P̃ *ᵥ e_i = e_i`, which gives `(P̃⁻¹)_ii = 1` on supported `σ` (`Matrix.mulVec_mulVec`, `nonsing_inv_mul`), then `lawE_congr` and `E 1 = 1`. Holds whether or not `i ∈ S`, and for any other (even negative) sources. 3625 checks. |
| `lawE_hN_neg_pow_swap` | OK | `Equiv.neg` on `Config V` (`σ ↦ -σ`; `sgn (-σ) = -sgn σ`): `precN a (-1) y σ = precN a 1 y (-σ)`, so `wt(y⁺,y⁻,σ) = wt(y⁻,y⁺,-σ)` (`Equiv.sum_comp`). 2900 checks, relative error `< 10⁻¹⁰`. |
| `precN_isHermitian'` | OK | `Sym2.eq_swap`, `G.adj_comm`. |
| `continuousOn_moment` (`k + 1 ≤ p`) | OK | Per `σ`, `wt·hN^k = 1{P̃⁺≻0 ∧ P̃⁻≻0}·det(P̃⁻)^p det(P̃⁺)^{p-k} adj(P̃⁺)_ii^k`. This is continuous in `y` by `continuous_ite_posDef_family` (Glue): `F` vanishes when `det P̃⁺ = 0` since `p - k ≥ 1`, and `√·` and `cRoot` are continuous everywhere. Then `ContinuousOn.div` on `{Zw > 0}`; `Continuity.lean` already has `continuous_Zw` and the `k = 1` case. Evidence: across a genuine support boundary of `K4` (8 sign vectors with `λ_min(P̃⁺) = 2·10⁻¹⁶`), jumps `< 10⁻⁵` for `k = 0, 2, 3 ≤ p - 1`; at `k = p = 4` the jump is `0.0043` (the hypothesis is needed). |
| `isCompact_cube` | OK | `{y | InCube c y} = Set.univ.pi (fun _ => Set.Icc 0 c)`, `isCompact_univ_pi`, `isCompact_Icc` (empty if `c < 0`). |

## SourceMax/Phys.lean — 12 `sorry`; statements checked

Evidence: the enumerator above (3393 sign configurations, 225 source pairs, zero sources, random
`S`). Result: 0 failures for every identity below. With one negative source `precN_eq_scale` fails,
so `hy : ∀ u, 0 ≤ y u` is needed and present.

| lemma | verdict | Lean-level sketch |
|---|---|---|
| `physFactor_pos` | OK | `Finset.prod_pos` over `posSrc` (membership gives `0 < y u`). |
| `precPhys_isHermitian` | OK | entrywise `ext`; `sgn σ u w = sgn σ w u` (`Sym2.eq_swap`), `G.adj_comm`. |
| `precN_eq_scale` (`y ≥ 0`) | OK | `ext u w`; `diagonal_mul`, `mul_diagonal`. Diagonal, `u ∈ S⁺`: `√y·(D/y)·√y = D` (`Real.mul_self_sqrt`, `div_mul_cancel₀`). Diagonal, `u ∈ S \ S⁺`: `y_u = 0` by `hy`, so `D_u = 1` (`cRoot 0 = 0`). Off-diagonal entries with a zero source: `√0 = 0`. |
| `det_precN` | OK | `det_mul`, `det_diagonal`, `Finset.prod_ite_mem`-style rewriting, `Real.mul_self_sqrt`. |
| `posDef_precN_iff` | OK | `diagonal physScale` is a unit with real (self-adjoint) entries; `Matrix.IsUnit.posDef_star_right_conjugate_iff` (Mathlib `PosDef.lean`:627), as used in `Common/Spectral`. |
| `greenP_eq_phys`, `hN_eq_phys` | OK | `Matrix.mul_inv_rev` holds **unconditionally** in Mathlib, and `Matrix.inv_diagonal`. So `P̃⁻¹ = M⁻¹P⁻¹M⁻¹` even when `P` is singular (both sides junk `0`), and no invertibility hypothesis is needed. Then `Real.sqrt` cancellation on `S⁺`. 31737 + 9859 checks. |
| `wt_eq_phys` | OK | unfold `wt`, `posPow`, `wtMinus`; `if_congr` with `posDef_precN_iff`; `det_precN`, `mul_pow`; any `p` (including `p = 0`). |
| `wt_mul_hN_pow_eq_phys` | OK | `wt_eq_phys`, `hN_eq_phys`, `div_pow`, `glue` unfolding. 39436 checks. |
| `lawE_eq_phys` | OK | factor `physFactor^p > 0` out of both sums (`Finset.mul_sum`, `mul_div_mul_left`); also correct when the sums vanish. |
| `posSrc_update` | OK | `Finset.filter_congr`, `Function.update_apply`; `0 < y_j - t ↔ t < y_j`; `t` may be negative. |
| `precPhys_update` | OK | the off-diagonal entries depend on `y` only through `posSrc` (unchanged); diagonal `Z_u(y') = Z_u(y) + δ_u` on `S⁺`, `1 = 1 + 0` elsewhere. 993 checks (random `t ∈ (-y_j, y_j)`). |

## SourceMax/Jacobian.lean — `hasDerivAt_precZ_update` — 1 `sorry`; statement checked

**OK.** Sketch: `Z_u(y(t)) = (1 + Σ_{m∈N_S(u)} cRoot(a² y_u(t) y_m(t)))/y_u(t)`, with
`Function.update_apply` splitting the cases `u = j`, `m = j`.
* Derivative of `cRoot` at `x ≥ 0`: `Real.hasDerivAt_sqrt` (`1 + 4x ≠ 0`) composed with the affine
  inner map (`HasDerivAt.comp`, `.const_mul`, `.const_add`).
* Assemble with `HasDerivAt.fun_sum` and `HasDerivAt.div` (`y_u ≠ 0`).
* Algebra with `s = √(1+4x)`, `c = (s-1)/2`: `c' = 1/s = 1/(1+2c)` and `c(1+c) = x`
  (`Real.sq_sqrt`). For `u = j` this gives `(1 + Σ c²/(1+2c))/y_u² = 𝓑_uu/y_u²`; for `u ∼ j`,
  `-a²/(1+2c) = 𝓑_uj/(y_u y_j)`; otherwise `0`. Use `τ²/(1-τ²) = c²/(1+2c)` and
  `τ/(1-τ²) = c(1+c)/(1+2c)`, then `field_simp; ring`.
* Zero-source neighbours (`y_m = 0`) contribute `0` to both sides. `hy` makes every `x ≥ 0`, so the
  `cRoot` identities hold. No constants.

Evidence: 1255 central-difference checks (`K1`..`diamond`, `a ∈ [0, 1.5]`, zero neighbours
included): 0 failures (relative error `< 10⁻⁶`).

## SourceMax/Deriv.lean — `hasDerivAt_moment` — 1 `sorry`; statement checked

**OK.** Sketch (the file docstring, made Lean-level):
* On `t ∈ (-y_j, y_j)` (`HasDerivAt.congr_of_eventuallyEq`), write
  `lawE(y(t)) = Ñ(t)/(y_i(t)^k D̃(t))`, with `Ñ = Σ_σ W⁻(σ)·glue p k i (P_σ + diag δ(t))` and
  `D̃ = Σ_σ W⁻·glue p 0 i (…)`. This uses `wt_mul_hN_pow_eq_phys` per `σ` and cancels `physFactor^p`;
  `y(t) ≥ 0` there, and `posSrc_update` and `precPhys_update` apply with
  `δ_u(t) = 1_{u∈S⁺}(Z_u(y(t)) - Z_u(y))`, so `δ(0) = 0`.
* `δ'_u = 1_{u∈S⁺} 𝓑_uj/(y_u y_j)` by `hasDerivAt_precZ_update` (and `hasDerivAt_const` off `S⁺`).
* Term by term `hasDerivAt_glue` (needs `k + 2 ≤ p`; also `0 + 2 ≤ p` for `D̃`), then
  `HasDerivAt.fun_sum`.
* `D̃(0) > 0` because `Zw = physFactor^p·D̃ > 0`.
* `HasDerivAt.div`, plus `HasDerivAt.pow` for `(y_i - t)^k` when `i = j` (constant otherwise).
* `greenP_eq_phys` turns `Σ_σ W⁻ posPow (P⁻¹)_{··}` into `lawE` of `greenP`; `glueDeriv`'s `Σ_l`
  over `V` reduces to `S⁺` since `δ'_l = 0` there.
* Finish with `field_simp; ring` against `momC`. No constants.

Evidence: 1812 central-difference checks on `K2, P3, K13, K3, C4`. They use `p ∈ {3,4,6,9}`,
`a ∈ {a(d,p), 1.6a(d,p)}`, random sources with zeros, all `i, j ∈ S⁺` and every `k ≤ p - 2`
(including `k = 0`): 0 failures. **Support boundary:** `K4` at a point where 8 sign vectors have
`λ_min(P̃⁺) = 2·10⁻¹⁶`. There the Richardson one-sided slopes agree with the formula for
`(k,p) ∈ {(0,4),(1,4),(2,4)}` (6 checks). For `p = k + 1` they differ (e.g. `0.087` vs `-0.236`),
so the hypothesis is sharp. The small case `S = {i}` gives `0` (BP_SOURCEMAX).

## SourceMax/FOC.lean — `foc_of_max` — 1 `sorry`; statement checked

**OK.** Sketch:
* With `m(t) = lawE(update yp j (yp j - t))`, `hasDerivAt_moment` gives `m'(0) = D`.
* For `t ∈ (0, y_j]` the point stays in `[0,c]^V` (only coordinate `j` changes, to
  `y_j - t ∈ [0, y_j] ⊆ [0, c]`), so `m(t) ≤ m(0)` by `hmax`.
* Hence `D ≤ 0`: `hasDerivWithinAt_iff_tendsto_slope` on `𝓝[>] 0` with slopes `≤ 0`
  (`le_of_tendsto`), or `IsLocalMaxOn.hasFDerivWithinAt_nonpos`.
* Multiply by `y_i^k y_j > 0` (`mul_nonpos_of_nonpos_of_nonneg`, `Finset.sum_mul`, `field_simp`).
  When `i = j`, `y_j = y_i` turns `k E h^k y_i^k y_j / y_i` into `k E h^k y_i^k`.
* No constants; `hk` is only passed to `hasDerivAt_moment`.

Evidence: at numerical maximizers (L-BFGS-B, 4 starts) of `m_k` over `[0, s]^V` on
`K1, K2, P3, K13, C4, K3, paw, diamond, K4`. They use `p ∈ {3,4,5,6}` and `y⁻ ∈ {0, s·1, random}`,
and evaluate the FOC for every `j ∈ S⁺`. Result: 409 checks, 0 failures; interior coordinates give
`≈ 0`.

## SourceMax/LinAlg.lean — 5 `sorry`; statements checked

| lemma | verdict | sketch |
|---|---|---|
| `walkB_symm` | OK | identical to `walkB_comm` (`Walk.lean`, proved): `exact walkB_comm G a y S u w`. |
| `walkK_symm` | OK | `(walkB)ᵀ = walkB` (from `walkB_symm`), `Matrix.transpose_nonsing_inv` (unconditional). |
| `walkB_eq_zero_of_not_mem` | OK | `u ≠ w`; if `u ∉ S`, `w ∉ S` or `¬Adj` the entry is `0`. Otherwise `y_u = 0` (or `y_w = 0`) by `hy`, so `τEdge = cRoot 0/(1 + cRoot 0) = 0` and `-(0/(1-0)) = 0`. |
| `le_mulVec_of_mulVec_le` | **was NEEDS FIX, now OK** | The 22:15:49 version lacked `[DecidableEq n]`, and `K * B = 1` did not elaborate (scratch check). The 22:31:35 version has it. Sketch: `x = (K*B) *ᵥ x = K *ᵥ (B *ᵥ x)` (`Matrix.mulVec_mulVec`, `one_mulVec`), then `Finset.sum_le_sum` with `mul_le_mul_of_nonneg_left`. |
| `walk_dual` | OK | Set `x_l = 1_{l∈S⁺} C_l/y_l` and `b = -c e_i`. For `j ∈ S⁺`, `(𝓑x)_j = Σ_{l∈S⁺}𝓑_lj C_l/y_l ≤ b_j` (`walkB_symm`, `Finset.sum_filter`, `hfoc`; mind `if i = j` vs `if j = i`). For `j ∉ S⁺`, `(𝓑x)_j = 0 = b_j` (`walkB_eq_zero_of_not_mem`, `j ≠ i`). `walk_facts` gives `𝓑 ≻ 0`, hence `K𝓑 = 1` (`nonsing_inv_mul`, `isUnit_iff_ne_zero`, `PosDef.det_pos`), and `K ≥ 0`. Then `le_mulVec_of_mulVec_le` and `(K b)_l = -c K_li` (`Finset.sum_ite_eq`); multiply by `y_l > 0` (`div_le_iff₀`). Any sign of `c`. |

Evidence: 270 random instances with paper parameters `a(d,p), s(d,p)` and random `S`, zero sources
included. `walkB`/`walkK` are symmetric, the zero entries hold, and `K ≥ 0`, `K_ii ≥ 1`. For
`walk_dual`, `C` was built to satisfy `hfoc` with random slack and random signs of `c`: 259
instances. Result: 0 failures.

## SourceMax.lean — `source_moments_plus`, `source_moments` (F2), `source_covariance` (F3)

Proved from the children (version 22:31:35); the statements match the paper's (F2) with `B₀ = r`
and (F3). Verdict **OK**.

Sketch: the file docstring.
* F2: maximize `m_k` over the compact cube `[0,λs]^V` (`IsCompact.exists_isMaxOn`,
  `continuousOn_moment` with `k + 1 ≤ p`). If `y*_i = 0`, the moment is `1 ≤ B^k` with
  `B = (pr - k)/(p - k) ≥ 1` (`r > 1`). Otherwise apply `foc_of_max` and then `walk_dual` with
  `c = k m y_i^k`, which gives `C_i ≤ -k m y_i^{k+1} K_ii`.
* Then `C_i = y_i^{k+1}((p-k)M - p m μ)`, `K_ii ≥ 1`, the cap `μ ≤ r` at `y*`, and Lyapunov
  (`lawE_pow_succ_le`). The minus branch follows by `lawE_hN_neg_pow_swap` and the symmetric cap.
* F3: `foc_of_max` with `k = 1` (`p ≥ 3` from `TRegime`), then `walk_dual` with `c = r y_v`
  (`y_v > 0`, since a zero source has mean `1 < r`). The `y_i = 0` case: both sides `0`.
* Constants: `B = (pr - k)/(p - k)` is fixed by the statement; there is nothing else to choose.

Evidence (`check_tools_sourcemax.py`). The regime (`d ≥ 10⁵¹`) cannot be simulated. Instead the
lemma's mathematical content is tested with paper-shaped parameters at small `d` (where
`walk_facts_of_bound` holds, since `(d-1)τ_* = 1 - η₀ < 1`) and with **the weakest cap the proof
uses**, `B₀ = sup_y E h_i(y, y⁻)` over the cube for the same `i` and `y⁻`:
* (F2) `sup_y m_k(y) ≤ ((pB₀-k)/(p-k))^k`: 141 cases, 0 failures. Nontrivial cases (`sup m_k > 1`)
  occur on `K3`, paw, diamond and `K4`. Example: `K3`, `p = 6`, `k = 4`: `6.51 ≤ 33.8`; `k = 1`:
  `1.470 ≤ 1.565`. On trees and `C4` the means stay `≤ 1`.
* The intermediate steps `(p-k)E h^{k+1} - p m μ ≤ -k m K_ii` and `m ≤ ((pμ-k)/(p-k))^k` at the
  maximizer: 136 + 136 checks, 0 failures.
* (F3) at the maximizer of the first mean (playing the contact with `r := B₀`), for all `i ∈ S`:
  194 checks, 0 failures. At interior maxima the inequality holds with equality, as expected from
  an equality FOC (e.g. paw, `p = 4`: `-4.2173 ≤ -4.2173`).
* The paper's consequence `(p-1)Var(h_v) ≤ r(r-1)`: 63 checks, 0 failures.
