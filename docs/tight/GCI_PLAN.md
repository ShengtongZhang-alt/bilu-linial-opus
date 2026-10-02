# GCI node (GR1): plan

Owner: GCI subagent. Files: `BiluLinial/Tight/Gauss/GCI*.lean`, `scripts/tight/gci_*.py`.
Source: `docs/second_order_bilu_linial_tight.tex`, Lemma "Uniform incident-row gain" (GR1),
lines 626–693, first display of the proof (line 640).

## 1. What the paper needs

`Royen`, `correlation`, `Milman` occur only in the proof of GR1 (lines 637–648). The Prékopa
(line 393) and Brascamp–Lieb (lines 980, 1225) uses are separate long poles and are not
covered here. The only GCI input is

```
(GCI-T)   G[ q_AB · α^{p-1} β^{p-1} ] ≥ 0,
          α = (1 - xᵀAx)_+,  β = (1 - xᵀBx)_+,  q_AB(x) = xᵀABx = ⟨Ax, Bx⟩,
```

for PSD `A, B` of finite size (`|N(v)| ≤ d`), `G` the standard Gaussian expectation, and the
integer `p = ⌊c₀ d^{2/17}⌋` (large). Only the value at `s = 1` of the derivative is used; the
monotonicity of `H(s) = E α(X)^p β(Y_s)^p` on `[0,1]` is the paper's way to obtain it
(`H'(1) = 4p² G[q_AB α^{p-1} β^{p-1}]`, checked: `d/ds E f(X) g(Y_s) = E ∇f(X)·∇g(Y_s)`).
The sign is what matters downstream: line 670 turns (GCI-T), via (E4), into
`T_v = Σ_i E G⁺_{vi} G⁻_{vi} ≤ C p⁴`, which enters `(2p−1) a² S_v = B_v + 2p a² T_v + …`.
A lower bound `G[F] ≥ −η` would suffice only with `η ≲ δ/p` in the normalization of GR1,
far below the natural size of the term, so an approximate inequality is not an easy way out.

**Lean form of the target** (file `GCIDeriv.lean`):

```lean
theorem gci_clipped (A B : Matrix ι ι ℝ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (p : ℕ) (hp : 2 ≤ p) :
    0 ≤ ∫ x, (A *ᵥ x) ⬝ᵥ (B *ᵥ x) * max (1 - x ⬝ᵥ (A *ᵥ x)) 0 ^ (p - 1) *
      max (1 - x ⬝ᵥ (B *ᵥ x)) 0 ^ (p - 1) ∂(gaussPi ι)
```

**Equivalent forms.** For nonnegative Borel `φ, ψ` the statement
`E[⟨AX,BX⟩ φ(q_A) ψ(q_B)] ≥ 0` is equivalent to `E[⟨AX,BX⟩ | q_A, q_B] ≥ 0` a.s. and, by the
layer-cake formula, to `E[⟨AX,BX⟩ 1{q_A ≤ t} 1{q_B ≤ u}]·(density) ≥ 0`, i.e. to the
derivative at `s = 1` of the GCI monotonicity for two centred (possibly degenerate) ellipsoids.
It is Pitt's inequality `∫ ∇f·∇g dγ ≥ 0` for the even log-concave `f = α^p, g = β^p`.
Hargé (1999, Section 3) notes that Pitt's inequality "seems stronger than" GCI; it follows from
Royen's monotone form (Milman 2025, Section 3.3). After simultaneous diagonalisation it is
equivalent to a statement about Bingham distributions (see §3), so no cheap pointwise argument
exists: `⟨Ax,Bx⟩` is negative on a set of positive measure whenever `AB + BA` is indefinite.

## 2. Special cases (proved on paper; checked by `scripts/tight/gci_checks.py`)

(i) **Exponential weights.** `E[⟨AX,BX⟩ e^{-a q_A - b q_B}] = det(I+2aA+2bB)^{-1/2}
tr(AB (I+2aA+2bB)^{-1})`. With `X = 2aA`, `Y = 2bB`, `Ỹ = (I+X)^{-1/2} Y (I+X)^{-1/2}`:
`I+X+Y = (I+X)^{1/2}(I+Ỹ)(I+X)^{1/2}` and `XY = X(I+X)^{1/2}Ỹ(I+X)^{1/2}`, hence
`tr(XY(I+X+Y)^{-1}) = tr(X · Ỹ(I+Ỹ)^{-1}) ≥ 0` (trace of a product of two PSD matrices).
Numerically: minimum over 2000 random PSD pairs `1.7e-5 > 0`; MC matches the closed form.

(ii) **One exponential, one arbitrary factor.** For any `ψ ≥ 0` and `a` with `I + 2aA ≻ 0`:
`E[⟨AX,BX⟩ e^{-a q_A} ψ(q_B)] = det(Σ)^{1/2} tr(A·B'N) ≥ 0`, where `Σ = (I+2aA)^{-1}`,
`B' = Σ^{1/2}BΣ^{1/2}`, `N = E[zzᵀ ψ(zᵀB'z)]`. Indeed `Σ^{1/2}` commutes with `A`, so
`Σ^{1/2}ABΣ^{1/2} = AB'`; `N` is diagonal in an eigenbasis of `B'` (coordinate sign flips), so
`B'N ⪰ 0`. Consequently (GCI-T) holds whenever one factor is a positive mixture of
exponentials `e^{-a q}`; the clipped `(1-q)_+^{p-1}` is not (it vanishes for `q > 1`).

(iii) **Commuting `A, B`.** `AB ⪰ 0`, so the integrand is pointwise `≥ 0`.

(iv) **Rank one / `n = 2`.** For `A = uuᵀ`, `B = vvᵀ`, `ρ = u·v`:
`E[⟨AX,BX⟩ | |u·X| = a, |v·X| = b] = ρ a b tanh(ρab/(1-ρ²)) ≥ 0`; in 2D this is Pitt's theorem.

(v) **Lebesgue limit** (`A, B → 0` after rescaling): `∫_{K∩L} ⟨Ax,Bx⟩ dx ≥ 0` for centred
ellipsoids `K, L`: whiten `K` to a ball; the second-moment matrix of `ball ∩ L'` commutes
with `B'`, so the integral is `tr(A·B'M') ≥ 0`. The Gaussian weight breaks this symmetry.

(vi) **Reduction used in thinking, not in Lean.** Whitening by `A+B` makes the two forms
`yᵀDy`, `yᵀ(I-D)y` (`D` diagonal in `[0,1]`) and the Gaussian `N(0, Γ)` arbitrary; given
`|y| = r` the direction is Bingham-distributed, so (GCI-T) is a positivity statement for
`E[θᵀDΓ(I-D)θ | θᵀDθ]` under every Bingham law. Coordinate-sign symmetry fails, which is why
the general case needs Royen's argument.

Numerical checks (`gci_checks.py`): 12 random MC instances of (GCI-T) all positive (worst
z-score 1.7 on an instance whose value is ~1e-6); conditional means on an 8×8 histogram of
`(q_A, q_B)` all positive (min z = 112) even though `⟨AX,BX⟩ < 0` on 0.5% of samples.

## 3. Candidate routes

* **Hargé 1999** (one set an ellipsoid). His proof compares the semigroup adapted to the
  ellipsoid; its derivative at `t = 0` is `E[φ'(|y|²) y·∇g]`, trivially signed, but it is the
  derivative of a *different* interpolation. In original coordinates it is
  `E[∇fᵀ A⁻¹ ∇g] ≥ 0`, not `E[∇f·∇g]`. Hargé proves `E[∇f·∇g] ≥ 0` only for Gaussian `f`
  (his Theorem 5 = our case (i)/(ii)). Rejected: does not give the needed derivative.
* **Schechtman–Schlumprecht–Zinn 1998** (two ellipsoids): variational argument over rotations
  for `γ(E ∩ F) ≥ γ(E)γ(F)`; gives no derivative/monotone form. Rejected.
* **Milman 2025** (inverse Brascamp–Lieb): proves GCI, not monotonicity (Milman, §3.3: "we do
  not know how to obtain the full monotonicity"), and needs compactness + CLT. Rejected.
* **Royen 2014 / Latała–Matlak 2015** for boxes, then polytopes → ellipsoids, then `s → 1`.
  Gives monotonicity in `s` for all symmetric convex sets. **Chosen**, with a simplification
  below that removes all densities, Laplace-transform inversion and differentiation under the
  integral from Royen's part.
* **A direct 2D Royen argument for `(q_A, q_B)`** (boxes in `(q_A, q_B)` are what we need):
  the Laplace transform of `∂_s` of the law is `L³·P(λ,μ)/(λμ)` with `P` a polynomial with
  nonnegative coefficients, but higher powers of `λ, μ` correspond to derivatives of a density
  and the termwise argument fails on simplices. Rejected.
* **Approximate route through Brascamp–Lieb** (`G[F] ≥ −O(p² E tr(A(A+B)²))`): requires the
  variable-Hessian Brascamp–Lieb inequality (another long pole) and an error far below the
  natural size of the term (see §1). Rejected.

### Royen's argument without densities ("Royen-exp")

Let `V(s) = S(s) G` with `G` standard on `ι ⊕ ι`,
`S(s) = fromBlocks P₁ 0 (s P₂) (√(1-s²) P₂)`, so `Cov V(s) = C(s) =
fromBlocks (P₁P₁ᵀ) (s P₁P₂ᵀ) (s P₂P₁ᵀ) (P₂P₂ᵀ)` on `[0,1]`; `Z_i = V_i²/2`.
For one-dimensional exponential sums `φ_i(z) = Σ_j a_{ij} e^{-λ_{ij} z}` (`λ ≥ 0`) with
`φ_i ≥ 0` and `ψ_i := -φ_i' = Σ_j a_{ij} λ_{ij} e^{-λ_{ij} z} ≥ 0` on `[0,∞)`:

1. `E Π_i φ_i(Z_i(s)) = Σ_ω c_ω det(I + Λ_ω C(s))^{-1/2}` (distributivity + Gaussian Laplace
   transform R1), an explicit smooth function of `s`.
2. `det(I + ΛC) = Σ_J λ^J det C_J` (R2), and `s ↦ det C(s)_J` is antitone on `[0,1]` (R3), so
   `a_J(s) := -∂_s det C(s)_J ≥ 0`.
3. `∂_s E Π φ_i(Z_i) = ½ Σ_J a_J(s) Σ_ω c_ω λ_ω^J det(I+Λ_ωC(s))^{-3/2}
   = ½ Σ_J a_J(s) E[Π_{i∈J} ψ_i(Z̃_i) Π_{i∉J} φ_i(Z̃_i)] ≥ 0`, where `Z̃` is the sum of three
   independent copies of `Z` (R4: Laplace transform `det^{-3/2}`).
4. Take `φ_i = φ_{k,t_i}`, `φ_{k,t}(z) = 1 - (1 - e^{-k² z})^{b}`, `b = ⌈e^{k² t + k}⌉`:
   an exponential sum with `0 ≤ φ ≤ 1`, `ψ = b k² e^{-k² z}(1-e^{-k² z})^{b-1} ≥ 0`, and
   `φ_{k,t}(z) → 1{z ≤ t}` for **every** `z ≥ 0` (so no atom analysis is needed).
   Dominated convergence gives monotonicity of `P(∀i, |V_i(s)| ≤ c_i)`.

This is Royen's computation, but tested only against exponential sums, so Laplace inversion,
the multivariate gamma densities and Lemma 6 of Latała–Matlak are not needed. Numerically
(`gci_checks.py`, §5) the explicit `F(s)` matches Monte Carlo and is nondecreasing.

## 4. The DAG

Namespace `BiluLinial.Tight`. Notation: `X G = G ∘ Sum.inl`,
`Y s G = s • X G + √(1-s²) • (G ∘ Sum.inr)` under `gaussPi (ι ⊕ ι)`.

| id | Lean name (file) | statement | deps | difficulty |
|---|---|---|---|---|
| GCI-R2 | `det_one_add_diagonal_mul` (GCIMatrix) | `det(1 + diagonal m * C) = Σ_J (Π_{i∈J} m i) * det C[J,J]` | Mathlib `det_piecewise_one_eq_submatrix_det`, `map_add_univ` | easy |
| GCI-R2b | `one_le_det_one_add_diagonal_mul` (GCIMatrix) | `C ⪰ 0`, `m ≥ 0` ⟹ `1 ≤ det(1 + diagonal m * C)` | R2 | easy |
| GCI-R3a | `det_le_det_of_posSemidef_sub` (GCIMatrix) | `0 ⪯ X`, `Y - X ⪰ 0` ⟹ `det X ≤ det Y` | R2b | easy-med |
| GCI-R3 | `det_sideScale_antitoneOn` (GCIMatrix) | `M ⪰ 0` ⟹ `s ↦ det(sideScale M σ s)` antitone on `[0,1]` (off-block entries scaled by `s`) | R3a, Schur (`det_fromBlocks₁₁`, `PosSemidef.fromBlocks₁₁`) | medium |
| GCI-DET | `differentiable_det_of_entries` (GCIMatrix) | entries differentiable ⟹ `det` differentiable | `det_apply` | easy |
| GCI-ROT | `gaussPi_map_orthogonal` (GCILaplace) | `Uᵀ U = 1` ⟹ `(gaussPi κ).map (U *ᵥ ·) = gaussPi κ` | Mathlib `map_pi_eq_stdGaussian`, `charFun` | medium |
| GCI-R1 | `integral_exp_neg_quadForm` (GCILaplace) | `m ≥ 0` ⟹ `E exp(-½ Σ m_i (S G)_i²) = det(1 + diagonal m * S Sᵀ)^{-1/2}` | ROT, spectral thm, `integral_gaussian`, `det_one_add_mul_comm` | medium |
| GCI-R4 | `integral_exp_neg_quadForm_three` (GCILaplace) | three copies: `= det(…)^{-3/2}` | R1, `det_kronecker` | easy-med |
| GCI-R5 | `approxStep` + lemmas (GCIRoyen) | exp-sum form, `0 ≤ φ ≤ 1`, `ψ ≥ 0`, pointwise limit `1{z ≤ t}` | — | easy-med |
| GCI-R6 | `royen_expSum_monotoneOn` (GCIRoyen) | Royen-exp, step 1–3 above | R1, R2, R2b, R3, R4, DET | medium-hard |
| GCI-R7 | `royen_box_monotoneOn` (GCIRoyen) | `s ↦ P(∀k, |(P₁ X)_k| ≤ c_k ∧ ∀k, |(P₂ Y_s)_k| ≤ d_k)` monotone on `[0,1]` | R5, R6, dominated convergence | medium |
| GCI-SLAB | `setOf_quadForm_le_eq_iInter` (GCIEllipsoid) | `{x | xᵀAx ≤ t} = ⋂_{y ∈ ℚ^ι} {x | |(Ay)·x| ≤ √(t yᵀAy)}` | PSD Cauchy–Schwarz, density of `ℚ` | medium |
| GCI-E1 | `ellipsoid_pair_monotoneOn` (GCIEllipsoid) | `s ↦ P(q_A(X) ≤ t ∧ q_B(Y_s) ≤ u)` monotone | SLAB, R7, `tendsto_measure_iInter_atTop` | medium |
| GCI-E2 | `clipped_pair_monotoneOn` (GCIEllipsoid) | `s ↦ E[α(X)^p β(Y_s)^p]` monotone | E1; uniform step approximations `⌊n v⌋/n = (1/n) Σ_j 1{j/n ≤ v}` (no Fubini) | medium |
| GCI-E3 | `pitt_of_monotoneOn` (GCIDeriv) | `f, g ∈ C¹` (poly. bounds), `s ↦ E f(X) g(Y_s)` monotone ⟹ `E ∇f·∇g ≥ 0` | ROT, IBP `stein_gaussPi_of_hasDerivAt`, differentiation under ∫ | medium-hard |
| GCI-E4 | `hasFDerivAt_clipPow` etc. (GCIDeriv) | `∇(α^p) = -2p α^{p-1} A x`, `C¹`, bounds | — | easy-med |
| GCI-T | `gci_clipped` (GCIDeriv) | the target | E2, E3, E4 | easy |

**GCI-E3 sketch (θ-rotation; only first derivatives).** `H(θ) = E f(X) g(cos θ X + sin θ Z)`.
`H'(θ) = E f(X) ∇g(Y_θ)·Y'_θ`, `Y'_θ = -sin θ X + cos θ Z`. Rotating `(X,Z) ↦ (Y_θ, Y'_θ)`
(ROT) gives `E f(cos θ Y − sin θ Y') ∇g(Y)·Y'`; Stein in the `Y'` coordinates gives
`H'(θ) = −sin θ · E ∇f(X)·∇g(Y_θ)`. `H` antitone on `[0,π/2]` (from E2, `s = cos θ`) gives
`E ∇f(X)·∇g(Y_θ) ≥ 0` for `θ ∈ (0,π/2)`; let `θ → 0` (dominated convergence).

**GCI-T from E2–E4.** `f = α^p`, `g = β^p` are `C¹` for `p ≥ 2` with
`∇f·∇g = 4p² α^{p-1} β^{p-1} ⟨Ax,Bx⟩`; divide by `4p² > 0`.

## 5. Mathlib inventory

Present: `integral_gaussian`, `gaussianReal`, `integral_fintype_prod_eq_prod`,
`map_pi_eq_stdGaussian`, `stdGaussian_map`, `Measure.ext_of_charFun`, `charFun_pi`,
`IsHermitian.spectral_theorem`, `PosSemidef.eigenvalues_nonneg`, `det_one_add_mul_comm`
(Sylvester), `det_kronecker`, `det_fromBlocks₁₁`, `PosSemidef.fromBlocks₁₁`,
`PosSemidef.submatrix`, `posSemidef_self_mul_conjTranspose`, `PosSemidef.det_nonneg`,
`det_piecewise_one_eq_submatrix_det`, `MultilinearMap.map_add_univ`, `Finset.prod_univ_sum`,
`monotoneOn_of_deriv_nonneg`, `HasDerivWithinAt.nonneg_of_monotoneOn`,
`tendsto_measure_iInter_atTop`, `tendsto_integral_of_dominated_convergence`,
`hasDerivAt_integral_of_dominated_loc_of_deriv_le`, `measurePreserving_sumPiEquivProdPi_symm`.
From the IBP agent (`IBP.lean`): `stein_gaussPi_of_hasDerivAt`, polynomial-bound integrability.

Missing (to be proved here): Loewner monotonicity of `det`; principal-minor expansion of
`det(1 + D C)` for diagonal `D` (only its polynomial-coefficient form is in Mathlib); rotation
invariance of `gaussPi` on `ι → ℝ` (via `stdGaussian`); Gaussian Laplace transform of a
quadratic form; everything Royen-specific. Not needed thanks to Royen-exp: multivariate
Laplace-transform uniqueness, multivariate gamma densities, differentiation of densities.

Actual size: 2098 lines of Lean. No step depends on an unproved external theorem. Status of
each node: §6.

## 6. Status

All nodes are **proved\*** (sorry-free down to Mathlib and `IBP.lean`). `#print axioms` on
`gci_clipped`, `royen_box_monotoneOn`, `ellipsoid_pair_monotoneOn`, `pitt_of_monotoneOn`:
`[propext, Classical.choice, Quot.sound]`. Total 2098 lines in five files; modules build with
`lake build BiluLinial.Tight.Gauss.GCIDeriv`.

| id | Lean name | file | status |
|---|---|---|---|
| GCI-R2 | `det_one_add_diagonal_mul` | GCIMatrix | proved* |
| GCI-R2b | `one_le_det_one_add_diagonal_mul`, `one_le_det_one_add` | GCIMatrix | proved* |
| GCI-R3a | `det_le_det_of_posSemidef_sub` | GCIMatrix | proved* |
| GCI-R3 | `det_blockScale_antitoneOn`, `det_sideScale_antitoneOn` | GCIMatrix | proved* |
| GCI-DET | `differentiable_det`, `deriv_nonpos_of_antitoneOn` | GCIMatrix | proved* |
| GCI-ROT | `gaussPi_map_mulVec_orthogonal` | GCILaplace | proved* |
| GCI-R1 | `integral_exp_neg_quadForm` (via `integral_exp_neg_posSemidef_quadForm`) | GCILaplace | proved* |
| GCI-R4 | `integral_exp_neg_quadForm_three` | GCILaplace | proved* |
| GCI-R5 | `approxStep`, `approxStep_eval`, `approxStep_evalD`, `approxStep_eval_mem_Icc`, `approxStep_evalD_nonneg`, `tendsto_approxStep_eval` | GCIRoyen | proved* |
| GCI-R6 | `royen_expSum_monotoneOn` | GCIRoyen | proved* |
| GCI-R7 | `royen_box_monotoneOn` | GCIRoyen | proved* |
| GCI-SLAB | `sq_mulVec_dotProduct_le`, `setOf_quadForm_le_eq_iInter` | GCIEllipsoid | proved* |
| GCI-E1 | `ellipsoid_pair_monotoneOn` | GCIEllipsoid | proved* |
| GCI-E2 | `clipped_pair_monotoneOn` (step functions `⌊n v⌋/n` instead of Fubini) | GCIEllipsoid | proved* |
| GCI-E3 | `pitt_of_monotoneOn` | GCIDeriv | proved* |
| GCI-E4 | `hasDerivAt_max_zero_pow`, `hasFDerivAt_quadForm`, `hasFDerivAt_clipPow` | GCIDeriv | proved* |
| GCI-T | `gci_clipped` | GCIDeriv | proved* |

External dependency: `BiluLinial/Tight/Gauss/IBP.lean` (`stein_gaussPi_of_hasDerivAt`,
`integrable_of_polyBound_gaussPi`, `integrable_one_add_norm_pow_gaussPi`), owned by the IBP agent.

Interface notes for downstream users:
* The pair `(X, Yₛ)` is `gX G = G ∘ inl`, `gY s G = s X + √(1-s²) Z` under `gaussPi (ι ⊕ ι)`.
* `pitt_of_monotoneOn` takes gradients as functions `f' g' : (ι → ℝ) → ι → ℝ` with
  `HasFDerivAt f (dotCLM (f' x)) x`, continuity and polynomial bounds in the sup norm.
* `royen_box_monotoneOn` is Royen's theorem in monotone form for arbitrary (possibly
  degenerate) slab families; `ellipsoid_pair_monotoneOn` for arbitrary PSD `A, B` and levels.
