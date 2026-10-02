# The Bilu–Linial signing conjecture fails in every degree d ≥ 3

**Status of this note.** Xu ([`Xu_2609.15591v3.pdf`](Xu_2609.15591v3.pdf), arXiv:2609.15591v3)
proves the case `d = 3`. The extension to every `d ≥ 3` below comes from a discussion on
2026-09-29; it has not been reviewed by anyone else. Its algebra was checked with sympy (the seed
formula and the exact seed gain) and numerically (direct matrix computations for `d = 4`,
`h = 3`: the seed responses for both triangle signs, and one join of three seeds with mixed
signs, agreed with the formulas). Treat it as an unverified draft: if a step fails, record the
gap and report it; do not weaken the theorem.

An earlier argument from the same discussion, which claimed the seed gain is positive for every
`d` by comparing closed walks in a double cover with the `(d−1)`-ary tree, is **wrong** (both
lifts of the root have reduced degree; putting the triangle directly on the root at `d = 3`
gives gain exactly 0). Do not use it. The positivity of the gain rests on the exact formula in
step 6 below.

Xu's lemma numbers are used throughout; each step names the lemma it generalizes.

## Statement

> **Theorem B.** For every integer `d ≥ 3` there is a finite, connected, simple, `d`-regular
> graph `F` such that every signing `σ : E(F) → {−1, 1}` satisfies `‖A_σ(F)‖ > 2√(d−1)`.

Here `A_σ(F)` is the signed adjacency matrix (`σ(uv)` on edges, `0` elsewhere, zero diagonal)
and `‖·‖` is the Euclidean operator norm, equal to the largest absolute value of an eigenvalue.
For `d = 3` this is Xu's Theorem 1.1. (For `d = 2` the conjecture is true: signed cycles have
spectrum in `[−2, 2]`.)

## Notation

Fix `d ≥ 3`. Put `q = d − 1 ≥ 2` and `r = 2√q`. For a rooted graph `X` with root `o_X` and a
signing `σ` such that `rI − A_σ(X) ≻ 0` and `rI + A_σ(X) ≻ 0`, define (Xu (4))

```
g_ε(X, σ) = e_{o_X}ᵀ (rI − ε A_σ(X))⁻¹ e_{o_X}     (ε ∈ {−1, 1}),
s(X, σ)   = g_1(X, σ) + g_{−1}(X, σ),
t(X, σ)   = (√q / 2) · s(X, σ)                     (normalized: the infinite q-ary tree has t = 1).
```

## Construction

1. **Trees.** `T_h` is the complete rooted `q`-ary tree of height `h` (every vertex above level
   `h` has exactly `q` children).
2. **Seed `H_h`.** Vertices `o, v₀, v₁, v₂`; edges `o v₀`, `v₀ v₁`, `v₀ v₂`, `v₁ v₂` (a triangle
   `v₀ v₁ v₂` with a pendant root `o`). Attach `d − 2` disjoint copies of `T_h` to each of
   `o, v₁, v₂` and `d − 3` copies to `v₀`, each by one edge from the attachment vertex to the
   tree's root. The root of `H_h` is `o`. Degrees: `o` has `d − 1`; the level-`h` tree vertices
   have 1; every other vertex has `d`. `H_h` is connected with exactly one cycle. For `d = 3` this
   is Xu's `H_h` (trees at `o, v₁, v₂`, none at `v₀`).
3. **Joins.** `B(X₁, …, X_q)`: a new root joined by one edge to the roots of `q` vertex-disjoint
   rooted graphs. `Q₀ = H_h`, `Q_{j+1} = B(Q_j, …, Q_j)` (`q` disjoint copies). The root of every
   `Q_j` has degree `q`.
4. **Core `J = J(h, L)`.** A new centre `z` joined to the roots of `d` disjoint copies of `Q_L`.
   `J` is finite and connected, every vertex has degree `d` except the tree leaves (degree 1), so
   `J` has maximum degree `d`.
5. **Completion.** Every finite graph `G` of maximum degree `≤ d` is an induced subgraph of a
   finite `d`-regular graph, which is connected when `G` is. Doubling construction: take two
   disjoint copies of `G` and join each vertex of degree `< d` to its own copy. The result is
   simple, has maximum degree `≤ d`, contains `G` as an induced subgraph, and raises every
   degree below `d` by exactly one; it is connected if `G` is connected and some vertex has degree
   `< d`. After `d` rounds (or `d − minDegree`) the graph is `d`-regular. Xu's leaf-triple
   completion is specific to `d = 3`; any completion that keeps `J` induced works. Let `F` be the
   completion of `J`.

The graphs are astronomically large (about `q^(h+L)` vertices; `h, L` grow like `q⁴`), but
finite. A formal proof must build them abstractly (recursive types, sums, `Fin`-indexed
products) and argue structurally; no computation on the graph itself is feasible.

## Proof

**Reduction to `J`.** `A_σ(J)` is a principal submatrix of `A_σ(F)`, so
`‖A_σ(J)‖ ≤ ‖A_σ(F)‖`. It suffices to show `‖A_σ(J)‖ > r` for every signing of `J`. Suppose,
for contradiction, `‖A_σ(J)‖ ≤ r`, i.e. `rI ∓ A_σ(J) ⪰ 0` (Xu (3)).

**Step 1 (Xu Lemma 3.1, degree-free).** For symmetric `M = [[D, W], [Wᵀ, Γ]]` with `D ≻ 0`:
`M ⪰ 0 ⟺ Γ − WᵀD⁻¹W ⪰ 0`, likewise with `≻`, and if `M ≻ 0` the lower-right block of `M⁻¹` is
`(Γ − WᵀD⁻¹W)⁻¹`.

**Step 2 (Xu Lemma 6.1(i), degree `d`).** If `U` is connected with exactly one cycle and maximum
degree `≤ d`, then `‖A_σ(U)‖ < r` for every signing. Proof as in Xu: orient the cycle cyclically
and the attached trees away from it, so every vertex has in-degree 1 and out-degree
`d⁺(v) ≤ q`. Summing `2|x_u x_v| ≤ x_u²/√q + √q·x_v²` over directed edges `u → v` gives
`|xᵀA_σx| ≤ Σ_v (√q + d⁺(v)/√q) x_v² ≤ 2√q‖x‖²`. Strictness: `Σ_v d⁺(v) = |E| = |V| < q|V|`, so
some vertex has `d⁺(v) < q`; equality forces `x_v = 0` there and then, through the
edge-by-edge equality `|x_u| = √q|x_v|`, everywhere.

**Step 3 (Xu Lemma 6.1(ii), degree `d`).** For every signing of `T_h` and both `ε`,
`rI − εA_σ(T_h) ≻ 0` and `g_ε(T_h, σ) = (h + 1) / ((h + 2)√q)`. Induction on `h`: the Schur
complement at the root is `p = r − q·(h+1)/((h+2)√q) = (h + 3)√q / (h + 2) > 0`.

**Step 4 (Xu Lemma 3.3, degree `d`).** Let `Z = B(X₁, …, X_q)` with `rI_Z − εA_σ(Z) ≻ 0` for
both `ε`. Then `p_ε := r − Σᵢ g_ε(Xᵢ, σ) > 0`, `g_ε(Z, σ) = 1/p_ε`, and by
`1/p₁ + 1/p₋₁ ≥ 4/(p₁ + p₋₁)`,

```
s(Z, σ) ≥ 4 / (2r − Σᵢ s(Xᵢ, σ)),   with 2r − Σᵢ s(Xᵢ, σ) = p₁ + p₋₁ > 0.
```

In normalized form: `t(Z) ≥ 1 / (2 − (1/q) Σᵢ t(Xᵢ))`, the denominator being positive. The
signs of the joining edges drop out because they appear squared.

**Step 5 (Xu Lemma 3.2, degree `d`).** If `‖A_σ(J)‖ ≤ r`, then `rI − εA_σ(X) ≻ 0` for both `ε`
and every copy `X` of every `Q_j` in `J` (`0 ≤ j ≤ L`). Induction on `j`: `Q₀` by Step 2. For
`X = B(X₁, …, X_q)` with exterior parent `v` (the next join vertex toward `z`, or `z`), the
principal submatrix of `rI − εA_σ(J)` on `X ∪ {v}` is `⪰ 0`; eliminating the `Xᵢ` leaves
`[[p, a], [a, r]] ⪰ 0` with `a = ±1`, so `pr − 1 ≥ 0`, `p ≥ 1/r > 0`, and `rI − εA_σ(X) ≻ 0` by
Step 1.

**Step 6 (Xu Lemma 3.4, degree `d`): the seed.** Both matrices `rI ∓ A_σ(H_h)` are positive
definite for every signing (Step 2). Switch (conjugate by a diagonal `±1` matrix, which keeps the
spectrum and the diagonal of every inverse) so that the spanning tree `H_h − v₁v₂` is all `+1`;
the edge `v₁v₂` then carries `τ = σ(v₀v₁)σ(v₁v₂)σ(v₂v₀)`, and negating `σ` turns `τ` into `−τ`.
Eliminate the attached trees with Step 3: with

```
g_h = (h + 1) / ((h + 2)√q),   a = r − (d − 2)·g_h,   b = r − (d − 3)·g_h,
```

the Schur complement on `(o, v₀, v₁, v₂)` is

```
M_τ = [[ a, −1,  0,  0],
       [−1,  b, −1, −1],
       [ 0, −1,  a, −τ],
       [ 0, −1, −τ,  a]].
```

Eliminating `v₁, v₂` together (the vector `(1, 1)` is an eigenvector of `[[a, −τ], [−τ, a]]` with
eigenvalue `a − τ`) and then `v₀` gives

```
u_τ := (M_τ⁻¹)_{oo} = 1 / (a − 1 / (b − 2 / (a − τ))).
```

For `d = 3` (`b = r`) this is Xu's (16). The two responses of `σ` are `u₁` and `u₋₁` in some
order, so `s(H_h, σ) = u₁ + u₋₁` for every signing; write `t(h) = (√q/2)(u₁ + u₋₁)`.

**Seed gain.** As `h → ∞`, `g_h ↑ 1/√q`, so `a → (q + 1)/√q` and `b → (q + 2)/√q`, and (sympy)

```
t(∞) − 1 = 2(q² − 2) / (q⁶ + q⁵ + q⁴ + 4q + 4)  > 0   for every q ≥ 2.
```

At `q = 2` this is `1/31` (Xu's `h = 62` value is `140300416/138131009 ≈ 1 + 1/63.7`); for large
`q` it is about `2/q⁴`. In terms of `s = √q` the two denominator factors are
`s⁶ ± s⁵ + s⁴ ± 2s³ + 2s² ± 2s + 2`, neither of which has a real root; their product is
`q⁶ + q⁵ + q⁴ + 4q + 4`. The responses
increase with `h` (`M_τ` decreases in the Loewner order as `g_h` grows), and `t` is continuous in
`g_h` at the limit (all denominators stay positive: at `h = ∞`, `a − τ ≥ (q + 1)/√q − 1 > 0`,
etc.), so some finite `h` has `t(h) > 1`. The smallest such `h` is 30 for `d = 3`, 80 for
`d = 4`, 197 for `d = 5`, 427 for `d = 6`, 3785 for `d = 10`, about `q⁴/2` for large `q`
(numerics). A formal proof can pick `h` through the limit, with no explicit value.

**Step 7 (Xu §4, claim (7), degree `d`): amplification.** Fix `h` with `t(h) > 1`, then an integer
`N ≥ 2` with `t(h) > 1 + 1/N`. Put `c_j = 1 + 1/(N − j)` and `L = N − 1`. Claim: every copy `X`
of `Q_j` in `J` has `t(X, σ) > c_j` (`0 ≤ j ≤ L`). The case `j = 0` is Step 6. For the step,
Step 4 gives `t(Z) ≥ 1/(2 − mean t(Xᵢ))`, and `mean t(Xᵢ) > c_j` with `c_j < 2` for `j ≤ N − 2`,
so `t(Z) > 1/(2 − c_j) = c_{j+1}`, because `1/(2 − (1 + 1/m)) = 1 + 1/(m − 1)`. (Fewer levels
suffice, e.g. Xu's `N = 64`, `L = 61` at `q = 2`; any `L` with `c_L ≥ 2q/d` works.)

**Step 8: the centre.** With the `d` branches `X₁, …, X_d` at `z` positive definite (Step 5),
Step 1 applied to `rI − εA_σ(J)` gives `r − Σᵢ g_ε(Xᵢ, σ) ≥ 0` for each `ε`. Adding the two sides:
`Σᵢ s(Xᵢ, σ) ≤ 2r`, i.e. `Σᵢ t(Xᵢ, σ) ≤ 2q`. But Step 7 gives `t(Xᵢ, σ) > c_L = 2 > 2q/d` for
each of the `d` branches, so `Σᵢ t(Xᵢ, σ) > 2q`, a contradiction. Hence `‖A_σ(J)‖ > r` for every
signing, and so `‖A_σ(F)‖ > r` for every signing of the `d`-regular graph `F`. ∎

## Verification scripts (from the discussion)

Seed formula and exact gain (sympy):

```python
import sympy as sp
s = sp.symbols('s', positive=True)           # s = sqrt(q), q = d - 1 >= 2
r = 2*s; g = 1/s                              # infinite q-ary tree response at r
a = r - (s**2 - 1)*g                          # o, v1, v2 carry d-2 = q-1 trees
b = r - (s**2 - 2)*g                          # v0 carries d-3 = q-2 trees
u = lambda tau: 1/(a - 1/(b - 2/(a - tau)))
print(sp.factor(sp.simplify(s/2*(u(1) + u(-1)) - 1)))
# 2*(s**4 - 2)/((s**6 - s**5 + s**4 - 2*s**3 + 2*s**2 - 2*s + 2)
#               *(s**6 + s**5 + s**4 + 2*s**3 + 2*s**2 + 2*s + 2))
```

The continued fraction equals the `(o, o)` cofactor of `M_τ` for symbolic `a, b, r, τ` with
`τ² = 1`; for `d = 3`, `h = 62` it reproduces Xu's `140300416/138131009` exactly.
