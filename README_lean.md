## Lean statements

**Status: complete.** The three Challenge theorems are proved with no `sorry`. `#print axioms`
reports only `propext`, `Classical.choice` and `Quot.sound` for each. `lake comparator` (Lean's
kernel, NanoDa, con-ron) accepts `Solution` against `Challenge`; see
[`VERIFICATION.md`](VERIFICATION.md).

[`Challenge.lean`](Challenge.lean) imports only Mathlib. Its declarations, in namespace
`BiluLinial`, carry short docstrings; this section gives precise versions, in the same order.
All three theorems are stated with `sorry` in `Challenge.lean` and proved in
[`Solution.lean`](Solution.lean). [`FORMALIZATION.md`](FORMALIZATION.md) gives the correspondence
with the sources and every modelling decision. The code below is that of `Challenge.lean`,
without the docstrings.

### Signed adjacency matrix of a graph

```lean
abbrev Signing {V : Type*} (G : SimpleGraph V) : Type _ :=
  G.edgeSet → ℤˣ

noncomputable def signedAdjMatrix {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    (σ : Signing G) : Matrix V V ℝ :=
  Matrix.of fun u v => if h : G.Adj u v then ((σ ⟨s(u, v), h⟩ : ℤ) : ℝ) else 0
```

- `Signing G` is the type of signings of a simple graph `G` on a vertex type `V`: functions from
  the edge set `G.edgeSet` (unordered pairs `s(u, v)` with `G.Adj u v`) to the units
  `ℤˣ = {1, -1}`. A signing assigns one sign to each undirected edge.
- `signedAdjMatrix G σ` is the signed adjacency matrix `A_σ`, a real `V × V` matrix. Its `(u, v)`
  entry is `σ(s(u, v))`, read as the real number `1` or `-1`, when `u` and `v` are adjacent, and
  `0` otherwise. Since `s(u, v) = s(v, u)` and adjacency in a simple graph is symmetric and
  irreflexive, `A_σ` is symmetric, has zero diagonal, and has entries in `{-1, 0, 1}`, with
  `±1` exactly on the edges. The all-`+1` signing gives the ordinary adjacency matrix. The
  `DecidableRel G.Adj` instance only serves to write the `if`; any two instances give the same
  matrix. The sanity lemmas `signedAdjMatrix_isSymm`, `signedAdjMatrix_apply_self`,
  `signedAdjMatrix_apply_eq_one_or_neg_one_iff` and `signedAdjMatrix_one` in
  `BiluLinial/Sanity.lean` prove these facts.

### Spectral norm, and its equality with the largest absolute value of an eigenvalue

```lean
noncomputable def opNorm {V : Type*} [Fintype V] [DecidableEq V] (M : Matrix V V ℝ) : ℝ :=
  ‖Matrix.toEuclideanCLM (n := V) (𝕜 := ℝ) M‖

theorem opNorm_eq_iSup_abs_eigenvalues₀ {V : Type*} [Fintype V] [DecidableEq V]
    (M : Matrix V V ℝ) (hM : M.IsHermitian) : opNorm M = ⨆ i, |hM.eigenvalues₀ i| := by
  sorry
```

- `opNorm M`, for a real square matrix `M` indexed by a finite type `V`, is the spectral norm:
  the operator norm of `x ↦ M x` on `ℝ^V` with the Euclidean norm,
  `opNorm M = sup_{x ≠ 0} ‖M x‖₂ / ‖x‖₂`, which is the largest singular value of `M`. Formally it
  is the norm of the continuous linear map
  `Matrix.toEuclideanCLM M : EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V`. That type carries
  only one norm, the operator norm, so neither of Mathlib's scoped entrywise norms (sup and
  Frobenius) is involved. `opNorm M` agrees by definition with Mathlib's scoped
  `Matrix.Norms.L2Operator` norm. For an empty `V` it is `0`. The sanity lemmas
  `sqrt_mulVec_le_opNorm_mul` and `opNorm_le_of_forall_sqrt_mulVec_le` characterise it, using
  only dot products, as the least `c ≥ 0` with `‖M x‖₂ ≤ c ‖x‖₂` for all `x`.
- `opNorm_eq_iSup_abs_eigenvalues₀`: for every finite `V` and every real matrix `M` with
  `M.IsHermitian`, `opNorm M = max_i |λ_i|`. For a real matrix, `IsHermitian` means `Mᵀ = M`.
  Here `hM.eigenvalues₀ : Fin (Fintype.card V) → ℝ` is Mathlib's
  `Matrix.IsHermitian.eigenvalues₀`: the eigenvalues of `M`, with multiplicity, in decreasing
  order (`eigenvalues₀_antitone`). They are the roots of the characteristic polynomial
  (`roots_charpoly_eq_eigenvalues₀`). The supremum `⨆ i` runs over a finite index set, so for
  nonempty `V` it is a maximum, `max(λ_0, -λ_{n-1})`. For empty `V` it is `0`
  (`Real.iSup_of_isEmpty`), matching `opNorm` of the empty matrix. `A_σ` is symmetric
  (`signedAdjMatrix_isHermitian` in `BiluLinial/Sanity.lean`), so both main theorems can equally
  be read with the largest absolute value of an eigenvalue of `A_σ` in place of
  `opNorm (signedAdjMatrix G σ)`. The proof is `opNorm_eq_iSup_abs_eigenvalues₀_proof` in
  `BiluLinial/Main.lean`.

### Main upper bound on Bilu–Linial

```lean
theorem near_ramanujan_signing :
    ∃ C : ℝ, ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
      ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        (∀ v, G.degree v ≤ d) →
          ∃ σ : Signing G, opNorm (signedAdjMatrix G σ) <
            Real.sqrt (4 * ((d : ℝ) - 1) + C * (d : ℝ) ^ (-(2 : ℝ) / 17)) := by
  sorry
```

There are a real constant `C` and a natural number `d₀` with the following property. For every
integer `d ≥ d₀`, every finite type `V` (in any universe `u`), and every simple graph `G` on `V`
in which every vertex has at most `d` neighbours, some signing `σ` of `G` satisfies
`‖A_σ‖ < √(4(d-1) + C d^{-2/17})`.

- `C` and `d₀` are chosen before `d`, `V` and `G`, so they are absolute constants. In particular
  the bound is uniform in the number of vertices.
- `G` need not be regular, connected or nonempty. `G.degree v` is the number of neighbours of
  `v`.
- `d - 1` and `d^{-2/17}` are computed in `ℝ` (`Real.rpow`), so there is no truncated
  subtraction. If the argument of `Real.sqrt` were negative, the right-hand side would be `0`
  and the conclusion false, so this junk value can only make the statement harder.
- Since `√(4(d-1) + C d^{-2/17}) = 2√(d-1) + O(d^{-1/2-2/17})`, the bound is
  `2√(d-1) + O(d^{-1/2-2/17})`.

This is the upper bound of Theorem 1 of
[`docs/second_order_bilu_linial_tight.tex`](docs/second_order_bilu_linial_tight.tex), which
writes `γ_{q+1} ≤ √(4q + C q^{-2/17})` with `q = d - 1` and
`γ_d = sup_G min_σ ‖A_σ(G)‖`. With `∃ C`, the strict and non-strict forms, and `d^{-2/17}`
versus `(d-1)^{-2/17}`, are equivalent (`nearRamanujanStatement_iff_subOne` in
`BiluLinial/SanityD.lean`; see `FORMALIZATION.md`).

### Main lower bound on Bilu–Linial

```lean
theorem explicit_excess (d : ℕ) (hd : 4 ≤ d) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V) (_ : DecidableRel G.Adj),
      G.Connected ∧ G.IsRegularOfDegree d ∧
        ∀ σ : Signing G,
          2 * Real.sqrt ((d : ℝ) - 1) + 1 / (25 * ((d : ℝ) - 1) ^ 5 * Real.sqrt ((d : ℝ) - 1)) ≤
            opNorm (signedAdjMatrix G σ) := by
  sorry
```

For every integer `d ≥ 4` there is a finite simple graph `G` with the following three properties:
- `G` is connected (Mathlib's `Connected` includes that the vertex type is nonempty);
- `G` is `d`-regular: every vertex has exactly `d` neighbours;
- every signing `σ` of `G` satisfies `‖A_σ‖ ≥ 2√(d-1) + (d-1)^{-11/2}/25`.

- The excess `(d-1)^{-11/2}/25` is written as `1 / (25 (d-1)^5 √(d-1))` to avoid `Real.rpow`.
  Since `d ≥ 4`, `d - 1 ≥ 3 > 0`, so no junk value of division or `Real.sqrt` occurs.
- The vertex type lives in `Type`, which is no restriction for an existence statement. The
  `Fintype`, `DecidableEq` and `DecidableRel` instances are part of the witness; any two
  instances of each agree, so this changes nothing.

This is Section 6 of [`docs/second_order_bilu_linial.tex`](docs/second_order_bilu_linial.tex)
with an explicit constant. For every `R < R_q = 2√q + (1 + O(1/q)) q^{-11/2}`, `q = d - 1`, the
draft constructs such a graph, depending on `R`, whose signings all have `‖A_σ‖ ≥ R`. The constant
`1/25` is ours: numerically, `q^{11/2}(R_q - 2√q)` increases from `0.0481` at `q = 3` towards
`1`. Together with the upper bound, `γ_d` lies between `2√(d-1) + (d-1)^{-11/2}/25` and
`2√(d-1) + O(d^{-1/2-2/17})` for large `d`.

### Not in the Challenge

Theorem B of [`docs/COUNTEREXAMPLE_ALL_DEGREES.md`](docs/COUNTEREXAMPLE_ALL_DEGREES.md), which also
covers `d = 3`, is proved as a library theorem in `BiluLinial/Main.lean`. The superseded upper
bounds of `docs/asymptotic_bilu_linial.tex` and of Theorem 1.1 of
`docs/second_order_bilu_linial.tex`, which `near_ramanujan_signing` implies, were formalized
earlier and deleted once it was proved; they are not included here.

## Layout

| Path | Contents |
|---|---|
| `Challenge.lean` | Mathlib-only statement module, with short docstrings: the three definitions, the norm–eigenvalue equality and the two main theorems, with `sorry`. |
| `Solution.lean` | The three Challenge theorems under the same names, proved from `BiluLinial/Main.lean`. |
| `comparator.json` | Comparator configuration: `Challenge` against `Solution`, the three theorem names, the three standard axioms. |
| `BiluLinial/Main.lean` | `near_ramanujan_signing_proof`, `explicit_excess_proof`, `opNorm_eq_iSup_abs_eigenvalues₀_proof`, and the library theorem `bilu_linial_counterexample_proof` (every degree `d ≥ 3`). |
| `BiluLinial/Tight/` | The upper bound (Part D). |
| `BiluLinial/SecondOrder/Explicit/` | The lower bound (Part C2). |
| `BiluLinial/Counterexample/` | Theorem B (Part B). |
| `BiluLinial/Common/` | Shared linear algebra: operator norm, spectral facts, Schur complements. |
| `BiluLinial/ChallengeDefs.lean` | A verbatim copy of the Challenge definitions; the proof modules cannot import `Challenge`. |
| `BiluLinial/Sanity*.lean` | Sanity lemmas for the definitions and statements. |
| `FORMALIZATION.md` | Source-to-Lean correspondence and modelling decisions. |
| `VERIFICATION.md` | The checks run on the submitted state and their results. |
| `docs/` | The sources. `docs/BLUEPRINT.md` (lemma DAGs, all nodes proved) and `docs/tight/` (audit and planning notes for Part D) are the completed working record. |
| `scripts/` | Submission checks (below). `scripts/tight/` holds the numerical checks used while planning Part D. |
| `AGENTS.md`, `.cursor/rules/` | The instructions the agents worked under (historical). |

Every Lean file uses the module system (`module`, `public import`, `@[expose] public section`).
Lean `v4.35.0-rc2` and Mathlib `v4.35.0-rc2` are pinned in `lean-toolchain`, `lakefile.toml` and
`lake-manifest.json`.

## Building and checking

```bash
lake exe cache get                     # only needed on a fresh clone
lake build                             # BiluLinial, Challenge (3 sorry warnings), Solution
scripts/check_statements.sh            # Solution's statements and definitions equal Challenge's
ruby scripts/check-axioms.rb           # #print axioms agrees with comparator.json and the metadata
ruby scripts/check-submission-files.rb # Palomar's mechanical rules for the submission files
scripts/check-metadata-schema.sh       # formalization.yaml against the v0.4 JSON schema
python3 scripts/check-lean-sources.py  # module headers and the 10,000-line cap
scripts/verify-comparator.sh           # lake comparator with the bundled NanoDa and con-ron kernels
```

On macOS, which lacks `bwrap`, run the last command as
`PALOMAR_COMPARATOR_NO_SANDBOX=1 scripts/verify-comparator.sh`. The CI workflow
(`.github/workflows/ci.yml`) runs all of these on Linux, the comparator inside its sandbox.
