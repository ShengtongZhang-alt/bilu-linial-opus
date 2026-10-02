# Agent instructions

## Status (2026-10-01): all parts complete

Part D is complete (`near_ramanujan_signing` proved, 2026-10-01 12:47 UTC), and the repository has
been prepared for the Palomar registry. Every Lean file uses the module system (`module`,
`public import`, `@[expose] public section` after the module docstring). The submission surface is
`formalization.yaml`, `VERIFICATION.md`, `scripts/` and `.github/workflows/ci.yml`. The task
sections below are the historical record of how the work was specified. A new or edited Lean file
must keep the module header and pass `python3 scripts/check-lean-sources.py`; rerun the checks
listed in `README_lean.md` after any change. `Challenge.lean` holds the three definitions, the
norm–eigenvalue equality `opNorm_eq_iSup_abs_eigenvalues₀` and the two main theorems, with no
proofs and only short docstrings written by the maintainer (user instruction, 2026-10-01); the
precise documentation lives in `README_lean.md`.

## Part D, the tight upper bound (added 2026-10-01 04:05 UTC; completed)

Parts A, B and C below are **complete** and independently checked. The new task is to formalize
the **upper bound** of `docs/second_order_bilu_linial_tight.tex` (Theorem 1 there, the right-hand
inequality; proof in Section 1, "Upper bound"). It **replaces** the current upper-bound Challenge
theorem `second_order_signing`. The paper's lower bound (left-hand inequality, Section 2, via the
Sherrington–Kirkpatrick constant and random regular graphs) is **not a target** (user instruction).

**`Challenge.lean` after this change** holds the three existing definitions and exactly two
theorems: `explicit_excess` (unchanged; already proved) and the new upper bound, which replaces
`second_order_signing`. Statements are written in terms of `d` (standing user preference: no
auxiliary variables such as `q` or roots in the statement):

```lean
theorem near_ramanujan_signing :
    ∃ C : ℝ, ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
      ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        (∀ v, G.degree v ≤ d) →
          ∃ σ : Signing G, opNorm (signedAdjMatrix G σ) <
            Real.sqrt (4 * ((d : ℝ) - 1) + C * (d : ℝ) ^ (-(2 : ℝ) / 17))
```

This is the paper's `γ_{q+1} ≤ √(4q + C q^{-2/17})` with `d = q + 1`. The proof's last display
gives `‖A_σ‖ < R` with `R² = 4(d−1) + 4/⌊c₀ d^{2/17}⌋ ≤ 4(d−1) + C d^{-2/17}`. With `∃ C`, the
strict `<` and the paper's `≤`, and `d^{-2/17}` and `(d−1)^{-2/17}`, are equivalent. Record this in
`FORMALIZATION.md` and add sanity lemmas (e.g. that the bound is `2√(d−1) + O(d^{-1/2-2/17})`).

**Read the whole paper before designing the DAG.** It is an unreviewed draft of about 2000 lines,
with many unspecified absolute constants (`C`, `c`, `o(1)`, "sufficiently large `d`"). Every one of
them must become explicit, or an existential at the right quantifier level, uniform in the graph
order. If a step is wrong or a constant cannot be made to work, record the gap in
`docs/BLUEPRINT.md` and report it in a commit message. Never weaken the statement to route around
a gap.

**Long poles: deep external theorems that are not in Mathlib.** A search of
`.lake/packages/mathlib` finds no Prékopa, Prékopa–Leindler, Brascamp–Lieb or log-concavity API.
The proof uses:

- Royen's Gaussian correlation inequality, in E. Milman's monotonicity formulation (Lemma "Uniform
  incident-row gain", around line 636 of the `.tex`): `s ↦ E α(X)^p β(Y_s)^p` is nondecreasing for
  even quasi-concave factors;
- Prékopa's theorem (log-concavity is preserved by convolution with a translated Gaussian; Lemma
  "Bias and reference concentration", around line 393), used for "an even log-concave density has
  covariance at most `I` relative to the standard Gaussian";
- the Brascamp–Lieb variance inequality for linear functions (Lemma "Multiplicative shifted trace
  comparison", around line 1225; the paper sketches a proof through the elliptic equation
  `Lw = f − E f`);
- Gaussian integration by parts and the Rademacher-to-Gaussian comparisons (`R[·]` vs `G[·]`).

No axioms are allowed, so each of these is a DAG subtree that must be proved. Start them **first
and in parallel**, because they decide the timeline. Before committing to a general proof, check
whether this proof needs only a special case that is much easier: finite dimension, the specific
factors `α = (1 − xᵀAx)₊`, `β = (1 − xᵀBx)₊` with PSD `A`, `B`, covariance bounds only for linear
functions, or bounds that follow from strong log-concavity alone. If a route around one of them
exists, take it and record it. If one is infeasible, record it in `docs/BLUEPRINT.md` as the
blocking node and keep proving everything else.

**Reuse and deletion.** Reuse anything useful from `BiluLinial/Common/`, `BiluLinial/Asymptotic/`
and `BiluLinial/SecondOrder/Upper/` (Schur complements, insertion identities, operator norm and
spectral lemmas). The user allows deleting obsolete code. Once `near_ramanujan_signing` is fully
proved (not before; git keeps history), delete the modules that only served superseded upper
bounds: the old C1 chain `BiluLinial/SecondOrder/Upper/` and the Part A chain
`BiluLinial/Asymptotic/`, except any file the new proof imports. Delete them together with their
library theorems in `Main.lean`, their sanity lemmas and their `FORMALIZATION.md`/`BLUEPRINT.md`
sections. Keep `BiluLinial/Common/`, everything `explicit_excess` imports, and Part B's
`bilu_linial_counterexample` (it covers `d = 3`, which nothing else does). New proof files go
under `BiluLinial/Tight/`.

**Packaging at the end.** `Main.lean`, `Solution.lean`, `comparator.json` and
`scripts/check_statements.sh` must cover exactly `near_ramanujan_signing` and `explicit_excess`.
Rerun the statement comparison and `#print axioms` on both, and keep `lake build` green throughout.

## Part C, second-order bounds (completed; its upper bound C1 is superseded by Part D)

Parts A and B below are **complete**: sorry-free, packaged in `Main.lean` / `Solution.lean` /
`comparator.json`, and independently checked (statement comparison, `#print axioms`). Keep them
that way: never change their statements or break their proofs, and keep `lake build` green.

The new task is to formalize, statements and proofs, `docs/second_order_bilu_linial.tex`
(Part C), with the same workflow, parallelism, deliverables and acceptance checks as Parts A and B
(sections below). Read `docs/SECOND_ORDER_NOTES.md` first: it maps the paper's results to targets,
records a step-by-step check of the upper-bound proof and numerical checks of both lower bounds,
and lists the existing Lean code to reuse. The paper is an unreviewed draft. If a step fails,
record the gap in `docs/BLUEPRINT.md` and report it rather than weakening a statement.

**`Challenge.lean` holds exactly two theorems** (user instruction, 2026-09-30 04:17 UTC: the
file was getting cluttered). They are the upper bound and the explicit lower bound below, plus the
three existing definitions (`Signing`, `signedAdjMatrix`, `opNorm`). Everything else leaves
`Challenge.lean`:

- The Part A/B theorems (`asymptotic_signing`, `asymptotic_signing_rate`,
  `bilu_linial_counterexample`) stay proved in `BiluLinial/` (e.g. in `Main.lean`, stated in full
  there), but they are no longer Challenge statements. C1 implies Theorems 1.1 and 1.2. C2 implies
  Theorem B for `d ≥ 4`, but not for `d = 3`.
- `second_order_signing_sub_one`, `explicit_excess_root`, `explicit_excess_asymptotic` and
  `buffered_excess` are removed. The Section 7 bound (C3) and the `q^{-11/2}` asymptotics are
  **no longer targets**: assign them no work. Facts about the root, such as `z < 1/q` and hence
  `R_q > 2√q`, may be sanity lemmas in `BiluLinial/Sanity*.lean`.

The two Challenge theorems. Keep the meaning; record rendering choices in `FORMALIZATION.md`.

- **C1 (primary; the user's main interest)**, Theorem 1.1 of the paper:
  `BiluLinial.second_order_signing` —
  `∃ C : ℝ, ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
  [DecidableRel G.Adj], (∀ v, G.degree v ≤ d) → ∃ σ : Signing G,
  opNorm (signedAdjMatrix G σ) < 2 * Real.sqrt d + C * (d : ℝ) ^ ((1 : ℝ) / 6)`.
- **C2**, Section 6, the explicit lower bound. Per the user (04:30 UTC), it is stated **purely in
  terms of `d`, with no root `z`**, and with the explicit constant `1/25`:
  `theorem explicit_excess (d : ℕ) (hd : 4 ≤ d) : ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
  (G : SimpleGraph V) (_ : DecidableRel G.Adj), G.Connected ∧ G.IsRegularOfDegree d ∧
  ∀ σ : Signing G, 2 * Real.sqrt ((d : ℝ) - 1) + 1 / (25 * ((d : ℝ) - 1) ^ 5 * Real.sqrt ((d : ℝ) - 1))
  ≤ opNorm (signedAdjMatrix G σ)`,
  i.e. every signing has norm at least `2√(d−1) + (d−1)^{-11/2}/25`. This is Section 6's
  `γ_d ≥ R_q` combined with `R_q − 2√q > q^{-11/2}/25` for all `q = d − 1 ≥ 3`. Numerically
  `q^{11/2}(R_q − 2√q)` increases from 0.0481 (`q = 3`) to 1, so the margin is at least 20 %. The
  constant `1/25` is ours, not the paper's (the paper states `1 + O(1/q)`). Proof route: the
  construction works for every threshold `R > 2√q` with `F_q(t(R)²) > 0`, where
  `t(R) = (R − √(R²−4q))/(2q)` and `F_q(z) = −1 + (q−1)z + (q−1)z² + qz³ + (2q−4)z⁴`. For
  `R = 2√q + q^{-11/2}/25`, verify `F_q(t(R)²) > 0` directly as a real inequality (e.g. writing
  `R = √q(u + 1/u)`, `t = 1/(u√q)`); the root `z_q` itself need not appear in Lean at all.

**Priorities.** C1 first and fastest; C2 runs in parallel on the remaining subagent slots, but it
must never delay C1. When C1 is fully proved, commit it immediately with a message that says so.

**Where things go.** New proof files go under `BiluLinial/SecondOrder/Upper/` (C1) and
`BiluLinial/SecondOrder/Explicit/` (C2). No new definitions in `Challenge.lean`; if one is
unavoidable, add it verbatim to both `Challenge.lean` and `BiluLinial/ChallengeDefs.lean`. Update
`FORMALIZATION.md` (the Part A/B entries now describe library theorems, no longer Challenge
statements), `docs/BLUEPRINT.md` (the C1 and C2 DAGs), and at the end `Main.lean`,
`Solution.lean`, `comparator.json` and `scripts/check_statements.sh`, so that exactly the two
Challenge theorems are restated and compared. Rerun the statement comparison and `#print axioms`.

## Task (Parts A and B, completed)

Formalize in Lean 4 / Mathlib, **statements and proofs**, two recent results about signings of
graphs (the Bilu–Linial signing problem). Both live in this one repository and share one
statement module. The goal is a complete, sorry-free formalization **as fast as possible**.

**(A) Asymptotically optimal graph signings** — `docs/asymptotic_bilu_linial.tex`.

> **Theorem 1.1.** For every $\gamma>0$ there is an integer $d_0(\gamma)$ such that, for every
> integer $d\ge d_0(\gamma)$ and every finite simple graph $G$ of maximum degree at most $d$,
> there is an edge signing $\sigma$ satisfying $\|A_\sigma\|<(2+\gamma)\sqrt d$.
>
> **Theorem 1.2.** There is an absolute constant $C$ such that, for every sufficiently large
> integer $d$, every finite simple graph of maximum degree at most $d$ has an edge signing
> $\sigma$ satisfying $\|A_\sigma\| \le \bigl(2+C\,\log\log d/\log d\bigr)\sqrt d$.

The proof (Sections 2–7 of the `.tex`, about 8 pages) is self-contained: determinant weights
$W_H(\sigma)=\det(I-T_H^2)\mathbf 1_{\|T_H\|<1}$, their vertex-insertion identities (Schur
complements), the simple-path tree, moment comparison (Lemma 4.1), lower resolvent estimates via
Chebyshev (Lemma 4.2), a scalar coupling inequality (Lemma 5.1), and a strong induction on the
number of vertices (Section 6). Theorem 1.2 reruns the same induction with explicit parameters
(Section 7).

**(B) The Bilu–Linial conjecture fails in every degree $d\ge3$** —
`docs/COUNTEREXAMPLE_ALL_DEGREES.md`, which extends Xu's `d = 3` counterexample
(`docs/Xu_2609.15591v3.pdf`) to all degrees and follows Xu's proof step by step.

> **Theorem B.** For every integer $d\ge3$ there is a finite, connected, simple, $d$-regular graph
> $F$ such that every signing $\sigma:E(F)\to\{-1,1\}$ satisfies $\|A_\sigma(F)\|>2\sqrt{d-1}$.

Conventions (both sources): graphs are finite, simple and undirected; a signing is a map
$\sigma:E\to\{-1,1\}$; $A_\sigma$ has $\sigma(uv)$ at $(u,v)$ for every edge and $0$ elsewhere
(zero diagonal); $\|\cdot\|$ is the Euclidean operator norm, equal to the largest absolute value
of an eigenvalue; the norm of the empty matrix is $0$ and its determinant $1$; logarithms are
natural.

**Priorities.** Theorem 1.1 of (A) and Theorem B are the primary targets; work on both DAGs in
parallel from the start. Theorem 1.2 of (A) comes after Theorem 1.1's induction is in place (it
reuses it with explicit constants), but its statement goes into `Challenge.lean` with the others
at the start.

The statements must mean exactly what the sources mean: not weaker, not stronger, and not
vacuous. Where a source leaves something implicit, choose the reading it intends and record the
choice and the reason in `FORMALIZATION.md`. **Both proofs are unreviewed drafts**: the `.tex`
says so, and the all-degree extension in (B) is our own. If a step is wrong, record the gap in
`docs/BLUEPRINT.md` and report it rather than weakening a statement to route around it.

## Recommended workflow

`.cursor/rules/formalization-workflow.mdc` refines this workflow and is binding for the
coordinator and every subagent.

1. **Statements first.** Formalize all three statements in `Challenge.lean` with their sanity
   lemmas and `FORMALIZATION.md` (deliverables 1–3 below), check them, and commit. From then on
   the statements are frozen; change one only to fix a genuine error, and document the change.
2. **Decompose into a DAG.** Before proving anything, break each theorem into a DAG of
   intermediate lemmas, each small enough to formalize on its own, and record both DAGs in
   `docs/BLUEPRINT.md`. For every node give: an id, the informal statement with its source
   reference (section, lemma, equation), the Lean name and file, the ids of the nodes it depends
   on, and a status (`todo` / `stated` / `proved` / `proved*`). Standard facts the sources use
   without proof are nodes too (Schur complement positivity and inverse block formula, operator
   norm = largest absolute eigenvalue, norm of a principal submatrix is at most the norm,
   Chebyshev, Minkowski, the variance of a Rademacher quadratic form, the doubling completion to
   a regular graph, ...); search Mathlib for each before planning to prove it. Linear-algebra
   nodes that both parts use belong in a shared `BiluLinial/Common/` directory.
3. **State the whole DAG in Lean.** Write every node's Lean statement with a `sorry` proof, and
   derive each main theorem from its children, so both DAGs type-check end to end before any leaf
   is proved. This catches mis-stated interfaces early.
4. **Formalize along the DAGs**, leaves first, keeping `lake build` green and the statuses in
   `docs/BLUEPRINT.md` current. If a node turns out false or much harder than planned, revise
   the DAG rather than forcing it.

## Parallelism

Time is pivotal: deploy as many subagents as possible in parallel (10 at once is fine) and keep
them busy. The agent that owns the DAGs coordinates; each subagent gets one node or a small
cluster of nodes whose dependencies are already stated in Lean. Give each subagent the source
reference, the exact Lean statement it must prove, the file it owns, the proof sketch, and these
rules:

- Edit only the files you own, usually one file per node, e.g.
  `BiluLinial/Asymptotic/<Node>.lean`, `BiluLinial/Counterexample/<Node>.lean` or
  `BiluLinial/Common/<Node>.lean`. Only the coordinator edits shared files: `Challenge.lean`,
  `BiluLinial.lean`, `docs/BLUEPRINT.md`, `FORMALIZATION.md`, `README.md`, `lakefile.toml`.
- Never change the statement of a node you were given. If it is false, unprovable as stated, or
  needs an extra hypothesis, stop and report back so the coordinator revises the DAG.
- Check your own file with `lake env lean <file>` (the coordinator builds its imports first with
  `lake build`). Avoid running `lake build` concurrently with other agents, but never wait for
  one with `pgrep -f "lake build"` (or any `pgrep -f` pattern that appears in your own command):
  it matches the waiting shell's own command line, so the test is always true and the loop runs
  to its timeout or forever (2026-10-01: three agents deadlocked this way for 8 min). To wait,
  test `pgrep -x lake`, which matches only the lake binary, or just run the build.
- Commit only your own files (`git add <your paths>`), or leave commits to the coordinator.

The machine has 64 GiB of RAM and 16 cores, and its disk is nearly full (about 35 GiB free).
Each Lean process that imports Mathlib holds several GB of memory; if the machine starts
swapping, reduce the number of agents compiling at the same time. Do not write large files.

## Deliverables

1. **`Challenge.lean`** — imports only `Mathlib`. Contains every definition the statements use
   (signing, signed adjacency matrix, the operator norm used) and the three main theorems, in
   namespace `BiluLinial`, each with a docstring that restates it in words and proved by `sorry`:
   `BiluLinial.asymptotic_signing` (A, Theorem 1.1), `BiluLinial.asymptotic_signing_rate`
   (A, Theorem 1.2) and `BiluLinial.bilu_linial_counterexample` (Theorem B). It stays the audited
   statement surface once the proofs exist.
2. **Sanity lemmas in `BiluLinial/`** (e.g. `BiluLinial/Sanity.lean`, imported from
   `BiluLinial.lean`; these files may `import Challenge`), fully proved. They should show that
   the definitions mean what the sources say: the formal norm is the Euclidean operator norm and
   equals the largest absolute eigenvalue; the signed adjacency matrix is symmetric with zero
   diagonal and entries $\pm1$ exactly on edges, and the all-$+1$ signing gives the ordinary
   adjacency matrix; the degree and regularity hypotheses are the intended ones; and the
   statements are not vacuous or trivially true (e.g. the hypotheses of each theorem are
   satisfiable, and Theorem B's conclusion fails for some regular graph, such as a cycle with
   $d=2$).
3. **`FORMALIZATION.md`** — a source-to-Lean correspondence for each theorem: each ingredient of
   the statement, its Lean rendering, every modelling decision with its justification,
   hypotheses deliberately absent, and any known discrepancy.
4. **`docs/BLUEPRINT.md`** — both lemma DAGs with per-node status, kept current.
5. **The proofs**, in `BiluLinial/`, ending in `BiluLinial/Main.lean` with one theorem per main
   result whose type is literally the Challenge statement, e.g.
   `theorem asymptotic_signing_proof : type_of% @BiluLinial.asymptotic_signing := ...`.
6. Keep the **Status** section of `README.md` current.
7. When everything is proved: a `Solution.lean` (its own `lean_lib` in `lakefile.toml`) that
   imports `BiluLinial.Main` and restates each Challenge theorem under the same name, plus a
   `comparator.json` listing the three theorem names and the permitted axioms `propext`,
   `Quot.sound`, `Classical.choice`.

Things that commonly make a formal statement wrong without failing to compile: truncated
subtraction and division in `ℕ` (e.g. `d - 1`), junk values of `Real.sqrt`, `Real.log`
(`log log d` for small `d`) and of division by zero, **Mathlib's matrix norms** (there is no
global norm on `Matrix`; the scoped instances are elementwise sup, Frobenius and `ℓ²`-operator
norms, and only the last one is right here, e.g. `‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖`), Mathlib
conventions for degenerate cases such as empty vertex types (read the docstrings of the
definitions you use), quantifier order (in Theorem 1.1, $d_0$ depends only on $\gamma$; in
Theorem 1.2, $C$ is absolute), universe levels, and `Fintype`/`Finite`/decidability instance
choices in the statements.

## Acceptance checks

- `lake build` succeeds.
- Until the proofs are complete, `sorry` appears only in `Challenge.lean`'s main theorems and in
  DAG nodes whose status in `docs/BLUEPRINT.md` is not `proved`. When they are complete,
  `rg -n 'sorry' --glob '*.lean'` shows only `Challenge.lean`.
- No `axiom` declarations, no `native_decide`, no `set_option` that weakens checking.
- `#print axioms` on every sanity lemma, every `proved*` node, and (at the end) the main proofs
  reports at most `propext`, `Classical.choice`, `Quot.sound`:

  ```bash
  printf 'import BiluLinial\n#print axioms BiluLinial.some_lemma\n' > /tmp/axioms.lean
  lake env lean /tmp/axioms.lean
  ```

## Rules

- Work only inside this repository. Do not read, list, or reference other directories under
  `~/Math` or any other formalization attempt of these results. Mathlib sources under
  `.lake/packages/mathlib` and public documentation are fine.
- Do not change `lean-toolchain`, the Mathlib `rev`, or `lake-manifest.json`. Never run
  `lake update` or `lake clean`, and never delete `.lake`: Mathlib is prebuilt locally and
  rebuilding it takes hours.
- Commit your work with git in this repository at meaningful checkpoints.

## Useful commands and API

```bash
lake build                     # whole project (Mathlib is prebuilt)
lake env lean Challenge.lean   # check one file
```

Relevant Mathlib files (under `.lake/packages/mathlib/Mathlib/`):

- `Combinatorics/SimpleGraph/Finite.lean` — `SimpleGraph.degree`, `SimpleGraph.IsRegularOfDegree`,
  `SimpleGraph.maxDegree`.
- `Combinatorics/SimpleGraph/AdjMatrix.lean` — `SimpleGraph.adjMatrix`.
- `Combinatorics/SimpleGraph/Maps.lean`, `.../Subgraph.lean` — `SimpleGraph.induce`, embeddings.
- `Combinatorics/SimpleGraph/Connectivity/` — `SimpleGraph.Connected`.
- `Analysis/CStarAlgebra/Matrix.lean` — `Matrix.toEuclideanCLM` and the scoped `ℓ²` operator
  norm (`open scoped Matrix.Norms.L2Operator`).
- `LinearAlgebra/Matrix/Hermitian.lean`, `Analysis/Matrix/Spectrum.lean` —
  `Matrix.IsHermitian.eigenvalues` of symmetric matrices.
- `LinearAlgebra/Matrix/PosDef.lean` — `Matrix.PosDef`, `Matrix.PosSemidef`, and
  Schur-complement positivity (`Matrix.PosSemidef.fromBlocks₁₁`, `...fromBlocks₂₂`).
- `LinearAlgebra/Matrix/SchurComplement.lean` — block inverses and determinants,
  `Matrix.det_fromBlocks₁₁`, `Matrix.invOf_fromBlocks₂₂_eq`.
- `Analysis/InnerProductSpace/Spectrum.lean`, `Analysis/InnerProductSpace/Rayleigh.lean` —
  spectral theorem and Rayleigh quotients.
- `Analysis/SpecialFunctions/Pow/NNRpow.lean`, `Analysis/SpecialFunctions/Sqrt.lean`,
  `Analysis/SpecialFunctions/Log/Basic.lean` — `Real.sqrt`, `Real.log`.
