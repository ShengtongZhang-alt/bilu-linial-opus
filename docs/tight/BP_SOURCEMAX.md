# Sub-DAG of `D-F2` / `D-F3` (source maximum), for merging into `docs/BLUEPRINT.md`

Source: `docs/second_order_bilu_linial_tight.tex` §1.1, Lemma "Source maximum and moments" and
Lemma "Deletion and source differentiation"; AUDIT-D §2.4 (DF1) and §2.5.

**Route (differs from the paper and from AUDIT-D §2.5).** No implicit function theorem and no
deletion lift: at a maximizer `y*` of `m_k(y) = E_{(y, y⁻)} (h_i^+)^k` over the cube
`[0, λ s]^V` (second source fixed), we only decrease one positive plus-source at a time,
`y ↦ y - t e_j`, which stays in the cube. In physical coordinates on `S⁺ = {u ∈ S : y_u > 0}` this
moves the physical precision `P` along a *diagonal* curve, `P(t) = P + diag δ(t)`,
`δ'_u = 𝓑_uj/(y_u y_j)` (the Jacobian `DZ = -D_y⁻¹ 𝓑 D_y⁻¹`). The first-order conditions are then
`(𝓑 x)_j ≤ -k m_k y_i^k 1_{j=i}` with `x_l = C_l/y_l` on `S⁺`, and `K = 𝓑⁻¹ ≥ 0` inverts them.

## Status (2026-10-01)

All nodes below are `proved*`: `lake build BiluLinial.Tight.SourceMax` succeeds, no `sorry` in
`SourceMax.lean` or `SourceMax/*.lean`, and `#print axioms` on `source_moments`,
`source_moments_plus`, `source_covariance` (and on `hasDerivAt_moment`, `foc_of_max`,
`walk_dual`, `hasDerivAt_glue`, `continuousOn_moment`, `lawE_eq_phys`, `hasDerivAt_precZ_update`)
reports only `propext`, `Classical.choice`, `Quot.sound`. Extra helpers added along the way:
`differentiableAt_det_of_entries` (Glue), `lawE_sum`, `precN_isHermitian'` (Law), `physScale_pos`,
`inv_precN_apply` (Phys), `cRoot_nonneg`, `cRoot_mul_one_add_self`, `hasDerivAt_cRoot`,
`tau_identities` (Jacobian), `InCube.of_mul_le_one` (SourceMax).

## Parent check

`BiluLinial/Tight/SourceMax.lean` proves `source_moments` (D-F2) and `source_covariance` (D-F3)
from the sub-nodes below; it compiles (2026-09-30), with the statements unchanged. The plus branch
of F2 is the lemma `source_moments_plus` in the same file; the minus branch is the swap.

## Nodes

| id | Lean name | file | statement (one line) | depends on | status |
|---|---|---|---|---|---|
| D-SM-glue | `hasDerivAt_glue` | `SourceMax/Glue.lean` | for symmetric `Q₀`, `δ(0) = 0`, `k + 2 ≤ p`: `t ↦ 1{Q(t) ≻ 0} det(Q(t))^p (Q(t)⁻¹_ii)^k`, `Q(t) = Q₀ + diag δ(t)`, has derivative `glueDeriv = 1{Q₀ ≻ 0} det^p (p G_ii^k Σ G_ll δ'_l - k G_ii^{k-1} Σ G_il² δ'_l)` at `0` | — (Mathlib) | proved* |
| D-SM-glue-jac | `hasDerivAt_det_add_diagonal` | `SourceMax/Glue.lean` | Jacobi along a diagonal curve: derivative `Σ_l adj(Q₀)_ll δ'_l` | — | proved* |
| D-SM-glue-inv | `hasDerivAt_inv_add_diagonal` | `SourceMax/Glue.lean` | `(Q(t)⁻¹)_ab' = -Σ_l G_al δ'_l G_lb` for `det Q₀ ≠ 0` | glue-jac | proved* |
| D-SM-glue-top | `isOpen_posDef_family`, `isClosed_posSemidef_family`, `continuous_ite_posDef_family` | `SourceMax/Glue.lean` | PD open / PSD closed along continuous families; glued continuity | — | proved* |
| D-SM-law | `lawE_add/sub/const_mul/zero/congr/nonneg`, `lawE_pow_succ_le` (Lyapunov), `hN_pos`, `lawE_hN_pow_of_source_zero`, `lawE_hN_neg_pow_swap`, `continuousOn_moment` (`k < p`), `isCompact_cube` | `SourceMax/Law.lean` | elementary facts on `lawE` | glue-top, `Symmetry.lean` | proved* |
| D-SM-phys | `precN_eq_scale`, `det_precN`, `posDef_precN_iff`, `greenP_eq_phys`, `hN_eq_phys`, `wt_eq_phys`, `wt_mul_hN_pow_eq_phys`, `lawE_eq_phys`, `posSrc_update`, `precPhys_update` | `SourceMax/Phys.lean` | `P̃ = M P M` on `S⁺` (`M = diag √y`, identity elsewhere), so `W = (Π_{S⁺} y)^p W⁻ 1{P ≻ 0} det(P)^p`, `greenP = P⁻¹` on `S⁺`, `h_i = P⁻¹_ii/y_i`; moving `y_j` (`j ∈ S⁺`, `t < y_j`) is a diagonal curve of `P` | glue (defs) | proved* |
| D-SM-jac | `hasDerivAt_precZ_update` | `SourceMax/Jacobian.lean` | `∂_t Z_u(y - t e_j)|₀ = 𝓑_uj/(y_u y_j)` for `u, j ∈ S⁺` | — | proved* |
| D-SM-deriv | `hasDerivAt_moment` | `SourceMax/Deriv.lean` | `∂_t E_{y - t e_j}(h_i^+)^k|₀ = (Σ_{l ∈ S⁺} 𝓑_lj/(y_l y_j) C_l)/y_i^k + 1_{i=j} k m_k / y_i`, `C_l = momC = p Cov(G_ii^k, G_ll) - k E(G_ii^{k-1} G_il²)` | glue, phys, jac, law | proved* |
| D-SM-foc | `foc_of_max` | `SourceMax/FOC.lean` | at a maximizer over `[0, c]^V`, for `i, j ∈ S⁺`: `Σ_{l ∈ S⁺} 𝓑_lj C_l/y_l + 1_{i=j} k m_k y_i^k ≤ 0` | deriv | proved* |
| D-SM-la | `walk_dual` (+ `walkB_symm`, `walkK_symm`, `walkB_eq_zero_of_not_mem`, `le_mulVec_of_mulVec_le`) | `SourceMax/LinAlg.lean` | the FOC on `S⁺` imply `C_l ≤ -c y_l K_li` on `S⁺` | `walk_facts` (D-walk) | proved* |
| D-F2 | `source_moments` (+ `source_moments_plus`) | `SourceMax.lean` | as frozen | law, foc, la, `walk_facts` | proved* |
| D-F3 | `source_covariance` | `SourceMax.lean` | as frozen | law, foc, la, `walk_facts`, `meanPlus_of_source_zero` | proved* |

## Sketches (rule 2, check 1)

* **D-SM-glue.** See the module docstring. PD case: `Q(t) ≻ 0` near `0` (openness along the
  continuous family `v ↦ Q₀ + diag v`), product rule with Jacobi (`adj_ll = det G_ll`) and the
  inverse derivative (`G` symmetric). Not PSD: `Q(t)` not PSD near `0`, `g ≡ 0`. PSD singular:
  `|g| ≤ |det|^{p-k} |adj_ii|^k ≤ C |det|² = O(t²) = o(t)` (needs `p - k ≥ 2`). Jacobi: multilinear
  expansion of `det` in the rows (`map_add_eq_map_add_linearDeriv_add`); terms with `≥ 2` rows of
  `diag δ(t)` are `Π_{l ∈ s} δ_l(t)` times constants and have derivative `0`.
* **D-SM-phys.** Entrywise: `m_u P_uw m_w = P̃_uw` (zero sources: `D_u = 1` since `c(0) = 0`, and
  `√0 = 0` kills the off-diagonal entries). `det(MPM) = (Π m)² det P`, congruence by the invertible
  diagonal `M` preserves PD (`IsUnit.posDef_star_right_conjugate_iff`), `(MPM)⁻¹ = M⁻¹P⁻¹M⁻¹`
  (`Matrix.mul_inv_rev`, unconditional). Requires `y ≥ 0`.
* **D-SM-jac.** `c'(x) = 1/(1 + 2c)`; `u = j`: `(1 + Σ c²/(1+2c))/y_j²`; `u ∼ j`:
  `-c(1+c)/((1+2c) y_u y_j)`; `τ²/(1-τ²) = c²/(1+2c)`, `τ/(1-τ²) = c(1+c)/(1+2c)`.
* **D-SM-deriv.** For `t < y_j`: `m(t) = Ñ(t)/(y_i(t)^k D̃(t))`, `Ñ = Σ_σ W⁻ glue_k(P_σ(t))`,
  `D̃ = Σ_σ W⁻ glue_0(P_σ(t))` (the factor `(Π_{S⁺} y)^p` cancels); `D̃(0) > 0` from `Zw > 0`.
  `glue_k` derivative from D-SM-glue with `δ'` from D-SM-jac; quotient rule; `P⁻¹ = greenP` on
  `S⁺` turns the sums into `lawE` of physical entries.
* **D-SM-foc.** Slopes of `t ↦ m(y - t e_j)` on `(0, y_j]` are `≤ 0` (points stay in the cube),
  so the derivative is `≤ 0`; multiply by `y_i^k y_j`.
* **D-SM-la.** `x_l = C_l/y_l` on `S⁺`, `0` elsewhere; `(𝓑x)_j ≤ -c 1_{j=i}` for all `j` (rows of
  `𝓑` outside `S⁺` are identity rows); `x = K𝓑x ≤ -c K e_i` since `K ≥ 0`.
* **D-F2 / D-F3.** See the docstring of `SourceMax.lean`.

## Small cases (rule 2, check 3)

* `S = {i}` (no edges): `h_i = 1`, `m_k ≡ 1`; D-SM-deriv gives `-k/y_i + k/y_i = 0` (checked by
  hand: `𝓑_ii = 1`, `C_i = -k y_i^{k+1}`). F2: `1 ≤ ((pr-k)/(p-k))^k` since `r ≥ 1`.
* `λ = 0`: the cube is `{0}`, the maximizer has `y_i = 0`, handled by the zero-source branch.
* D-SM-glue `1 × 1`, `Q₀ = q`: `g = 1{q+δ>0}(q+δ)^{p-k}`; formula gives `(p-k) q^{p-k-1} δ'` for
  `q > 0` and `0` otherwise; at `q = 0`, `p - k = 1` it would fail (so `k + 2 ≤ p` is needed).
* F3 at `S = {v}` would read `-y_v² ≤ -r y_v²` (false), but there is no contact there
  (`E h_v = 1 < r`): the contact hypothesis is essential and is used (via `foc_of_max`).
* F3 with `y_i^+ = 0`: `greenP_vi = greenP_ii = 0`, both sides `0`.

## Statement issues found

None. The frozen statements of `source_moments` and `source_covariance` are proved from the
sub-nodes without change. Note that `walk_dual` uses `walk_facts` with `hy : InCube (sOf d p) y`,
which holds since `λ ≤ 1`.
