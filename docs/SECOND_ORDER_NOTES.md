# Notes on `docs/second_order_bilu_linial.tex` (Part C)

Reviewer notes written before formalization started. They map the paper's results to the Lean
targets, record which steps were checked and how, and point at existing Lean infrastructure. They
do not replace the paper; read it in full.

**Historical (2026-10-01).** Part C is complete. Its upper bound (Theorem 1.1) was later
superseded by `near_ramanujan_signing` and deleted together with the Part A code
(`BiluLinial/Asymptotic/`) referred to below; Section 6 is `explicit_excess`.

## Results and section map

| Target | Source | Content |
|---|---|---|
| C1 (primary) | Theorem 1.1; proof in Sections 2–5 | `∃ C`, for all large `d`, every graph of max degree `≤ d` has a signing with `‖A_σ‖ < 2√d + C d^{1/6}` |
| C1′ | "Consequently" after Theorem 1.1 | the same with `2√(d−1)` in place of `2√d` |
| C2 | Section 6, eqs (6.1)–(6.2) | for every `d ≥ 4`, `q = d−1`: `γ_d ≥ R_q = z_q^{-1/2} + q z_q^{1/2}` with `z_q` the unique positive root of `q z(1+z+z²+2z³) = 1+z+z²+4z⁴`; `R_q > 2√q` |
| C2′ | end of Section 6 | `R_q − 2√q = (1 + O(1/q)) q^{-11/2}` |
| C3 | Section 7, eq (7.1) | `liminf_q q^{7/2}(γ_{q+1} − 2√q) ≥ 1/4`: for every `c < 1/4` and all large `q` there is a finite connected `(q+1)`-regular graph with no signing of norm `< 2√q + c q^{-7/2}` |

`γ_d` itself need not be defined in Lean; state the graph-level facts it abbreviates (see
`AGENTS.md`, Part C).

## C1: step-by-step check of the upper-bound proof

Every step of Sections 2–5 was re-derived by hand; no gap was found. Algebra worth reusing:

- **Kernel ratio (proof of Lemma 3.1).** With `u = λ²/R²`, `κ = R/ζ`, `κ² = 1/(1+k)`:
  `h_ζ − e_ζ = 2κ²u/(1−κ²u)²`, `e_R − e_ζ = u(1−κ²)/((1−u)(1−κ²u))`, so the ratio is
  `(2/k)(1−u)/(1−κ²u) ≤ 2/k`. The matrix-square kernel symmetrised over `±λ` is exactly `h_ζ`:
  `((1−x)^{-2} + (1+x)^{-2})/2 = (1+x²)/(1−x²)²`.
- **Contraction constant.** `1 − B²p = 1 − (1−β)/(1+β) = β/a`, and `ζ^{-2} = p/d ≤ 1/(4d)`.
- **Inverse deletion.** `D_ww = G_ww − G_wu²/G_uu`; `Σ_w G_wu²/G_uu ≤ (G²)_uu/G_uu ≤ ‖G‖ ≤ ζ/(ζ−R)`
  for positive definite `G` (`G² ≤ ‖G‖ G`).
- **Rademacher variance.** `Var(Σ_{i≠j} s_i s_j D_ij) = 2 Σ_{i≠j} D_ij² ≤ 2 Σ_i (D²)_ii`.
- **Density bound 8.** `dν_H / d(ν_K ⊗ signs) = α Z_K/Z_H ≤ 8` because `0 ≤ α ≤ 1` and `Z_H/Z_K ≥ 1/8`.
- **Fresh insertion.** `z ↦ 1/(z(z−λ))` decreases on `z ≥ R > |λ|`, so `q_{R,−} ≥ q_ζ` as quadratic forms.
- **Coupling lemma 4.1, pointwise inequalities.** On the good event `α = r² − r(u+v) + uv` and
  `uv ≥ −L` (case split on signs; when `u < 0 ≤ v < r`, `min(v₊, r) = v₊`). Off the good event, if
  `u ≥ r`: for `v ≥ 0` the right side is `≤ r² − r·r ≤ 0`; for `v < 0`, `L ≥ r v₋` gives `≤ 0`. The
  second inequality off the good event needs `u + v ≥ r − q = 1 − 2q ≥ 0`, which uses `q ≤ 1/2` and
  `q_± ≥ 0`.
- **Proposition 4.2.** The identity `βa² − (1+βa)(βx_R+k) = β²a(1−x_R) − k[1+β(a+x)]` follows from
  `a² − x = βa` and `x_R = (1+k)x`. The numerics (`m ≤ 0.251β`, `√2 e ≤ 0.045β`, `C < 0.055β²`,
  `f > 1/5`, `0.3739β² > 0.2255β²`) all check.
- **Induction (Section 5).** With `β = L d^{-1/6}`: `e/β^{3/2} ≤ C_τ(L^{-3} + L^{-11/2} d^{-1/12})`;
  `E(u+v) ≤ 2kq + βh = M` from the cofactor invariant, `R^{-2} = (1+k)ζ^{-2}`, and `h = deg/R²`.
  Finally `R − 2√d = 2√d((1−β²)^{-1/2}(1+β²/1000)^{-1/2} − 1) = O(L² d^{1/6})`.

Points that need care in Lean:

- `C_τ` in Lemma 3.1 must be uniform in `d`, `β`, the graph family and the graph order. Prefer
  explicit numeric constants (with `τ = 1/1000` fixed), or at least an `∃ C` proved before `d`
  and `β` are introduced.
- `F` and `M` are maxima over a finite family (zero if empty). The bound `F ≤ B²(pF + …)` is
  self-referential: derive it for each `(H, u)` with the maximum on the right, then take the
  maximum. `F ≤ B` and `‖G_{H,ζ}‖ ≤ C_ζ` make both finite.
- Spectral calculus: the `(u,u)` entry of `f(A)` for symmetric `A` is `Σ_i f(λ_i) U_{ui}²`, so a
  pointwise kernel inequality on `(−R, R)` gives the inequality of diagonal entries.
  Sign-reversal symmetry (`W_H(−σ) = W_H(σ)`) symmetrises `λ ↦ f(λ)` to `(f(λ)+f(−λ))/2`.
- Two radii are in play: the weights, `J`, and `q_±` use `R`; the path-tree reference `b_H` and
  the deficit resolvent use `ζ > R`.

Existing Lean to reuse (Part A, `BiluLinial/Asymptotic/`): `T`, `W`, `Z`, `J`, `qPlus`, `qMinus`,
`inc`, `starVec`, `flipAt` (`Defs.lean`); the insertion identities (`Insertion.lean`,
`InsertMatrix.lean`: `W_insert`, `W_mul_inv_insert`, `W_le_erase`, `insert_facts`,
`posDef_one_{add,sub}_vertexExt_iff`, ...); the path tree `pathG` with `1 ≤ pathG ≤ 1/aParam x`
and its recursion (`PathTree.lean`); the scalar lemmas (`Scalar.lean`); the Common linear algebra
(`Common/{OpNorm,Schur,Spectral}.lean`). Deletion monotonicity `b_{H−u}(v) ≤ b_H(v)` may be new.
Read these files before stating Part C nodes, and reuse their definitions rather than duplicating
them.

## C2: explicit excess (Section 6)

Checked symbolically (`scripts/second_order_numeric_check.py`, sympy):

- the triangle root response: the `(o,o)` entry of `[[b,−σ₁,−σ₂],[−σ₁,a,−σ₃],[−σ₂,−σ₃,a]]⁻¹` is
  `g_η = (b − 2/(a−η))⁻¹` with `η = σ₁σ₂σ₃`;
- the mean formula (6.3): `(g₊ + g₋)/2 = t(1+t²+t⁴+2t⁶)/(1+t²+t⁴+4t⁸)` for `a = t⁻¹ + t`, `b = t⁻¹ + 2t`;
- `m(t) > 1/(qt) ⟺ F_q(t²) > 0`, with `F_q(z) = −1 + (q−1)z + (q−1)z² + qz³ + (2q−4)z⁴` the
  difference of the two sides of (6.1).

Numerically (mpmath, 60 digits): `0 < z_q < 1/q` for `q ∈ {3,4,5,10,30,100}`;
`q^{11/2}(R_q − 2√q) = 0.048, 0.135, 0.223, 0.514, 0.814, 0.941` for those `q`, which is
consistent with `1 + O(1/q)` but converges slowly. For `q = 2` the construction gives no excess
(`z₂ = 1/2`, `R₂ = 2√2`), which is why `d ≥ 4`.

The construction is Theorem B's with a different threshold: a triangle seed with no pendant root
(`q−2` trees at the distinguished vertex, `q−1` at each of the other two), `q`-joins, a centre of
degree `q+1`, and an induced regular completion. The Part B Lean code (`BiluLinial/Counterexample/`)
is specialised to `r = 2√q`: `rad`, and the closed form `treeGreen = (h+1)/((h+2)√q)` for the tree
response, hold only at that threshold. For `R > 2√q` the height-`h` tree response is the `h`-th
iterate of `u ↦ 1/(R − qu)` and increases to `t = (R − √(R²−4q))/(2q)`, so a new tree lemma is
needed. The join, centre and completion lemmas (`JoinGreen`, `Centre`, `Amplify`,
`Completion.exists_regular_supergraph`) take the threshold or the graph as a parameter and should
transfer. Any induced connected regular completion suffices; the doubling construction already
proved is fine in place of the paper's `d`-copies construction.

## C3: buffered excess (Section 7)

Checked numerically for `(q, c, L) ∈ {(10³, 0.2, 20), (10⁴, 0.2, 20), (10⁵, 0.2, 20), (10⁶, 0.24, 60)}`:

- the exact map (7.4) equals a brute-force minimisation of `(χ₊(y+w) + χ₋(y−w))/2` to 60 digits,
  and the closed-form optimiser `w = −Δ(Cy+D)/(2E₀)` matches, with `w ≈ −2q^{-3/2}/(L+1)`;
- `C < 0`, `E± < 0`; the poles are `≈ 1 + 1/(L+1)` and the numerator zero is `≈ 1 + 1/L`; the
  optimiser lies below both poles;
- `q³(M_L(y₊) − y₊) → 4L/(L+1) − 2 − 4√c` (0.01541, 0.02014, 0.02062 against 0.02067 for
  `c = 0.2`, `L = 20`; −0.025171 against −0.025166 at `c = 0.24`, `L = 60`, where `L` is too small
  for the buffer condition (7.2) and the drift is correctly negative);
- `q(M_L′(τ) − 1) → −2`, as in (7.6).

The proof uses asymptotic expansions with `O_L(·)` errors. The contradiction only needs sign
facts for large `q`: positive drift at `y₊`, `M_L′ < 1` on `[τ − O(q^{-3}), y₊]`, and the
finite-height approximation. Consider getting each from a limit (`Filter.Tendsto … atTop`, e.g.
`q³(M_L(y₊) − y₊) → 2(L−1)/(L+1) − 4s`) rather than from explicit `O`-bounds. The Jensen step
needs `F_L = φ^{-L}` increasing and concave on `(φ^{∘L}(0), ∞)`, by induction on `L`.
