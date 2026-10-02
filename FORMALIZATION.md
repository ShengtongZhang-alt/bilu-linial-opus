# Formalization notes

Source-to-Lean correspondence for the two main statements in `Challenge.lean`: the Part D upper
bound `near_ramanujan_signing` (`docs/second_order_bilu_linial_tight.tex`) and the Part C explicit
lower bound `explicit_excess` (`docs/second_order_bilu_linial.tex`). `Challenge.lean` also states
the equality `opNorm_eq_iSup_abs_eigenvalues₀` between the norm and the largest absolute value of
an eigenvalue (see the norm row below). It carries short docstrings; `README_lean.md` gives
precise versions. Theorem B of Part B
(`bilu_linial_counterexample`, which covers `d = 3`) is a library theorem stated in full in
`BiluLinial/Main.lean`. The superseded upper bounds of Part A (`asymptotic_signing`,
`asymptotic_signing_rate`) and Part C (`second_order_signing`) were deleted, with their proofs and
sections here, once `near_ramanujan_signing` was proved; they are not included here. Sanity lemmas
supporting each claim below are in `BiluLinial/Sanity*.lean` (and `BiluLinial/Common/`); those of Part D are in
`BiluLinial/SanityD.lean`, where the statement is the proposition `NearRamanujanStatement`,
verbatim the Challenge theorem.

## Shared definitions

| Source | Lean | Notes |
|---|---|---|
| finite simple undirected graph | `G : SimpleGraph V` with `[Fintype V] [DecidableEq V] [DecidableRel G.Adj]` | Mathlib's `SimpleGraph` is simple and loopless by construction. The decidability instances are needed for `degree` and for the matrix; since `Decidable p` is a subsingleton, the choice does not affect any value. |
| signing `σ : E → {−1, 1}` | `Signing G := G.edgeSet → ℤˣ` | `ℤˣ = {1, −1}`; each edge `e = s(u, v) ∈ Sym2 V` gets one sign, so `σ(uv) = σ(vu)` automatically. `card_signing`: there are `2^{|E|}` signings. |
| `A_σ`: `σ(uv)` at `(u, v)` for edges, `0` elsewhere | `signedAdjMatrix G σ : Matrix V V ℝ` | Dependent `if h : G.Adj u v`. Sanity: symmetric (`signedAdjMatrix_isSymm`), zero diagonal (`signedAdjMatrix_apply_self`), entry `±1` exactly on edges (`signedAdjMatrix_apply_eq_one_or_neg_one_iff`), the all-`+1` signing gives `G.adjMatrix ℝ` (`signedAdjMatrix_one`), `(A_σ²)_{vv} = deg v`. |
| Euclidean operator norm `‖·‖` | `opNorm M := ‖Matrix.toEuclideanCLM (𝕜 := ℝ) M‖` | The norm of the linear map `EuclideanSpace ℝ V → EuclideanSpace ℝ V`, i.e. the `ℓ²` operator norm. It agrees with Mathlib's scoped `Matrix.Norms.L2Operator` norm (`opNorm_eq_l2_opNorm`), is characterised by `‖Mx‖₂ ≤ c‖x‖₂` (`opNorm_le_of_forall_sqrt_mulVec_le`, `sqrt_mulVec_le_opNorm_mul`), equals the largest absolute eigenvalue for symmetric matrices (stated in `Challenge.lean` as the third compared theorem, `opNorm_eq_iSup_abs_eigenvalues₀`: `opNorm M = ⨆ i, |hM.eigenvalues₀ i|` with Mathlib's `Matrix.IsHermitian.eigenvalues₀`, proved in `BiluLinial/Main.lean`; in the library also `opNorm_eq_sup_abs_eigenvalues`, `opNorm_signedAdjMatrix_eq_sup_abs_eigenvalues`), and is `0` for the empty matrix (`opNorm_of_isEmpty`), as the sources stipulate. Mathlib has no global matrix norm; the elementwise and Frobenius norms are deliberately not used. |
| maximum degree at most `d` | `∀ v, G.degree v ≤ d` | Equivalent to `G.maxDegree ≤ d` (`forall_degree_le_iff_maxDegree_le`), including for the empty graph. |
| `d`-regular | `G.IsRegularOfDegree d` | `∀ v, G.degree v = d` (`isRegularOfDegree_iff`). |
| connected | `G.Connected` | Mathlib's `Connected` includes nonemptiness, as intended (a counterexample graph is nonempty). |

## Part D, Theorem 1, upper bound (`BiluLinial.near_ramanujan_signing`, Challenge)

> (`docs/second_order_bilu_linial_tight.tex`, Theorem 1, right-hand inequality.) There is an
> absolute constant `C` such that, for all sufficiently large integers `q`,
> `γ_{q+1} ≤ √(4q + C q^{−2/17})`, where `γ_d = sup_{Δ(G) ≤ d} min_σ ‖A_σ(G)‖`.

```lean
theorem near_ramanujan_signing :
    ∃ C : ℝ, ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
      ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        (∀ v, G.degree v ≤ d) →
          ∃ σ : Signing G, opNorm (signedAdjMatrix G σ) <
            Real.sqrt (4 * ((d : ℝ) - 1) + C * (d : ℝ) ^ (-(2 : ℝ) / 17))
```

### Ingredients

| Source | Lean | Notes |
|---|---|---|
| `q`, `d = q + 1` | `d : ℕ`, `q` written as `(d : ℝ) - 1` | The statement is in terms of `d` (the maintainer's choice: no auxiliary variable `q` in the statement). The subtraction is in `ℝ`, so truncated `ℕ` subtraction never occurs; for `d ≥ 2` it is the intended `q ≥ 1`. |
| `C`, absolute | `∃ C : ℝ` first | `C` is chosen before `d₀`, `d` and the graph, so it is absolute. `∃ C : ℝ` rather than `C > 0` is not weaker: every witness is positive (`nearRamanujan_const_pos`), and the radius increases with `C` (`SanityD.nrRadius_mono`). |
| "for all sufficiently large `q`" | `∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → …` | `d₀` is chosen before `d` and the graph and depends on nothing, so the threshold is uniform in the graph order, as in the proof ("All degree thresholds are independent of graph order"). |
| `q^{−2/17}` | `(d : ℝ) ^ (-(2 : ℝ) / 17)` | `Real.rpow` with a negative real exponent. For `d ≥ 1` the base is positive, so there is no junk value (`rpow` is irregular only for negative bases): it is positive (`natCast_rpow_neg_two_div_seventeen_pos`) and `(d^{−2/17})^{17} = 1/d²` (`natCast_rpow_neg_two_div_seventeen_pow`). At `d = 0` Mathlib gives `0^{−2/17} = 0`, which is irrelevant since `d₀` may be taken `≥ 1`. The base `d` instead of the paper's `q = d − 1` is equivalent (see below). |
| `√(4q + C q^{−2/17})` | `Real.sqrt (4 * ((d : ℝ) - 1) + C * d ^ (−2/17))` | For `C ≥ 0` and `d ≥ 1` the radicand is nonnegative, so `Real.sqrt` has no junk value. Since every witness has `C > 0`, the junk value at negative radicands (`√x = 0`) never matters. |
| `Δ(G) ≤ d`, finite simple graph | `∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj], (∀ v, G.degree v ≤ d) → …` | Every finite simple graph, universe-polymorphic, no connectivity or nonemptiness assumption; `∀ v, G.degree v ≤ d` is `G.maxDegree ≤ d` (`forall_degree_le_iff_maxDegree_le`). |
| `γ_{q+1} ≤ R` | `∃ σ : Signing G, opNorm (signedAdjMatrix G σ) < R` for each such `G` | `γ_d = sup_G min_σ ‖A_σ(G)‖`; a graph has finitely many signings, so `γ_d ≤ R` says exactly that every graph of maximum degree `≤ d` has a signing with `‖A_σ‖ ≤ R`. `γ_d` itself is not formalized; the statement is the per-graph form, with `<` (see below). |
| `‖·‖` | `opNorm` | The Euclidean (`ℓ²`) operator norm (shared definitions). |

### Equivalent forms (`<` vs `≤`, `d^{−2/17}` vs `(d−1)^{−2/17}`)

Because `C` is existential, all four combinations give equivalent statements:

- `nearRamanujanStatement_iff_le`: `<` is equivalent to `≤` (`NearRamanujanStatementLe`). For
  `≤ ⇒ <`, replace `C` by `max C 0 + 1`. For `C ≥ 0` and `d ≥ 1` this strictly increases the
  radius, since `d^{−2/17} > 0` and `√` is strictly increasing on `[0, ∞)`.
- `nearRamanujanStatementLe_iff_subOne`: with `≤`, the corrections `C d^{−2/17}` and
  `C (d−1)^{−2/17}` are equivalent, because `d^{−2/17} ≤ (d−1)^{−2/17} ≤ 2^{2/17} d^{−2/17} ≤
  2 d^{−2/17}` for `d ≥ 2` (`SanityD.natCast_rpow_le_sub_one_rpow`,
  `SanityD.sub_one_rpow_le_two_mul_rpow`). The constant changes from `C` to `max C 0` or `2 max C 0`.
- `nearRamanujanStatement_iff_subOne`: the Challenge statement is equivalent to the paper's form
  `γ_{q+1} ≤ √(4q + C q^{−2/17})` (`NearRamanujanStatementSubOne`: `≤`, with `(d−1)^{−2/17}`).
- `nearRamanujanStatement_iff_subOneLt`: and to the strict form with `(d−1)^{−2/17}`.

**Relation to the proof.** The proof's last display (end of Section 1, "Closing the induction")
gives, for every `d ≥ d₀` and every graph of maximum degree `≤ d`, a signing in the support of
the Gibbs law with `I ± a A_σ ≻ 0`, where `a = 1/R`, `R² = 4(d−1) + 4/p` and
`p = ⌊c₀ d^{2/17}⌋` (`c₀ ∈ (0, 1]` absolute). That is, `‖A_σ‖ < R`, strictly, so the `<` of the
Lean statement matches the proof directly. Moreover `⌊x⌋ ≥ x/2` for `x ≥ 1`, so once
`c₀ d^{2/17} ≥ 1`:
`R² = 4(d−1) + 4/⌊c₀ d^{2/17}⌋ ≤ 4(d−1) + (8/c₀) d^{−2/17}`.
Hence `C = 8/c₀` works, with `d₀` the maximum of the proof's threshold and `⌈c₀^{−17/2}⌉`. This
is the paper's `γ_d² ≤ 4(d−1) + 4/⌊c₀ d^{2/17}⌋ ≤ 4(d−1) + C d^{−2/17}`, written with `d^{−2/17}`
as the paper itself does in that display.

### Content and strength

- **Asymptotics.** For `C ≥ 0` and `d ≥ 2`, the radius lies between the Ramanujan value and a
  small correction above it:
  `2√(d−1) ≤ √(4(d−1) + C d^{−2/17}) ≤ 2√(d−1) + C d^{−2/17}/(4√(d−1)) ≤ 2√(d−1) + C d^{−1/2−2/17}`.
  The three inequalities are `two_sqrt_sub_one_le_nearRamanujan_radius`,
  `nearRamanujan_radius_le` and `nearRamanujan_radius_le_rpow`. So the bound is
  `2√(d−1) + O(d^{−1/2−2/17})`.
- **Supersedes `second_order_signing`.** `secondOrderStatement_of_nearRamanujan`: the statement
  implies the Part C upper bound `‖A_σ‖ < 2√d + C′ d^{1/6}` (with `C′ = √(max C 0)`, `d₀′ ≥ 1`;
  `SecondOrderStatement` is the old Challenge statement verbatim). Through it, the statement
  also implies Theorems 1.1 and 1.2 of Part A.
- **The correction term is necessary.** By the proved `explicit_excess`, for every `d ≥ 4` some
  connected `d`-regular graph has `‖A_σ‖ ≥ 2√(d−1) + (d−1)^{−11/2}/25 > √(4(d−1))` for every
  signing. Hence the statement fails for `C = 0` (`not_nearRamanujan_const_zero`) and for every
  fixed `C ≤ 0` (`not_nearRamanujan_const_nonpos`), and every witness `C` is positive
  (`nearRamanujan_const_pos`). The witness graph of `explicit_excess` lives in `Type`; it is
  lifted to `Type u` with `ULift` and `SimpleGraph.comap`, which preserves degrees and the
  attainable norms (`SanityD.degree_comap_equiv`, `SanityD.exists_signing_opNorm_eq_comap`,
  `SanityD.not_signableBelow_of_le_excess`). Together, the two main theorems pin the optimal
  radius between `2√(d−1) + (d−1)^{−11/2}/25` and `2√(d−1) + O(d^{−1/2−2/17})`.
- **Non-vacuity.** In every universe and for every `d`, the hypotheses hold for a graph with a
  vertex of degree exactly `d`: the complete graph on `ULift (Fin (d+1))`
  (`exists_graph_degree_eq`). On such a graph every signing has `‖A_σ‖ ≥ √d`
  (`sqrt_le_opNorm_of_degree_eq`, from `sqrt_degree_le_opNorm`), so no radius `≤ √d` works
  (`not_signableBelow_sqrt`). The conclusion is not trivially true either: the trivial bound
  `‖A_σ‖ ≤ d` (`signableAtMost_self`) does not give it, because for every `C` the radius is
  eventually `< d` (`nearRamanujan_radius_lt_self`).

### Scope

- Only the **upper bound** of the paper's Theorem 1 is a target. The lower bound
  `2√q + 2q^{−5/2} − (32P_*/√3 + o(1)) q^{−3} ≤ γ_{q+1}` (Section 2, through the
  Sherrington–Kirkpatrick constant `P_*` and random regular graphs) was excluded by the
  maintainer and does not appear in `Challenge.lean`.
- `near_ramanujan_signing` **replaces** the Part C upper bound `second_order_signing` in
  `Challenge.lean`, which then holds `near_ramanujan_signing` and `explicit_excess` as its main
  theorems (plus the three shared definitions and the norm–eigenvalue equality). The implication `secondOrderStatement_of_nearRamanujan` shows
  that nothing is lost.

### Known discrepancies

None in the statement. The paper's `q^{−2/17}` is rendered as `d^{−2/17}` (the maintainer's
convention of stating everything in `d`), and the paper's `≤` as `<`; both changes give an
equivalent statement (proved above). The paper is an unreviewed draft with unspecified absolute
constants (`c₀`, `κ₀`, `C`, the degree threshold). The formal statement only asserts that
some such `C` and `d₀` exist, so it is independent of their values.

### Proof route

The proof follows the paper's Section 1 except in one place in the contact estimate
(Section 1.5). The paper's input GR1, the uniform incident-row gain (around l.636), uses Royen's
Gaussian correlation inequality in E. Milman's monotonicity form. The formal proof replaces GR1 and
the row comparison CR3 by the GCI-free inputs DR1 and CR3′ (`Tight/Contact/RouteDR1.lean`,
`RouteDR1D9a.lean`; derivation in `docs/tight/DR1_CHECK.md` and `docs/tight/CHECK_CONTACT.md`,
"DR1-route replacements"). The files that stated the paper's route, `Tight/Contact/RouteGCI.lean`
(`in_GR1`, `in_CR3`, `cr1_real`, `cr1_gci`) and `Tight/Contact/RouteD9a.lean` (`d9a_real`,
`d9a_gci`), were imported by nothing on the proof path. They were **deleted, not proved**, so that
the library is sorry-free. The Gaussian correlation inequality for the
clipped quadratic factors (`gci_clipped`, `Tight/Gauss/GCI*.lean`) is proved and stays in the
library, but the final proof does not use it.

## Part C, Section 6 (`BiluLinial.explicit_excess`, Challenge)

> For every integer `d ≥ 4` there is a finite, connected, simple, `d`-regular graph every signing
> of which has `‖A_σ‖ ≥ 2√(d−1) + (d−1)^{−11/2}/25`.

- `d : ℕ`, `4 ≤ d`; `∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V)
  (_ : DecidableRel G.Adj), G.Connected ∧ G.IsRegularOfDegree d ∧ ∀ σ,
  2 * √((d : ℝ) − 1) + 1 / (25 * ((d : ℝ) − 1) ^ 5 * √((d : ℝ) − 1)) ≤ opNorm (A_σ)`.
- `q = d − 1` is computed in `ℝ` (no truncated subtraction), and `q ≥ 3`, so `√q` and the
  division have their intended values; `1/(25 q⁵ √q) = q^{−11/2}/25`.
- Relation to the source: for every threshold `R < R_q = z_q^{−1/2} + q z_q^{1/2}` (`z_q` the
  positive root of `q z(1+z+z²+2z³) = 1+z+z²+4z⁴`), the paper constructs a connected `d`-regular
  graph, depending on `R`, all of whose signings have norm at least `R`; letting `R` increase to
  `R_q` gives `γ_d ≥ R_q`, and `R_q = 2√q + (1+O(1/q)) q^{−11/2}`.
  By the maintainer's choice the statement avoids `z_q` and uses the explicit constant
  `1/25`, which is ours: numerically `q^{11/2}(R_q − 2√q)` increases from `0.0481` (`q = 3`) to `1`,
  so `1/25` has a margin of at least 20 %. The proof applies the Section 6 construction at a
  threshold `R = q t + 1/t ≥ 2√q + q^{−11/2}/25` with `F_q(t²) > 0`, verified directly, so the root
  never appears in the proof either.
- `≤` for every signing, as the construction gives (`‖A_σ‖ ≥ R`). The witness type lives in
  `Type`; the instances are part of the witness.
- Content: the excess is strictly positive, so the statement implies Theorem B for `d ≥ 4`.

## Theorem B (`BiluLinial.bilu_linial_counterexample`, library theorem)

> For every integer `d ≥ 3` there is a finite, connected, simple, `d`-regular graph `F` such that
> every signing `σ : E(F) → {−1, 1}` satisfies `‖A_σ(F)‖ > 2√(d − 1)`.

- `d : ℕ`, `3 ≤ d`; `∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V)
  (_ : DecidableRel G.Adj), G.Connected ∧ G.IsRegularOfDegree d ∧ ∀ σ, 2 * √((d : ℝ) - 1) < opNorm (A_σ)`.
- `d − 1` is computed in `ℝ` (no truncated subtraction); for `d ≥ 3` it is the intended value.
- The witness type lives in `Type`; the instances are part of the witness (any choice gives the
  same matrix).
- Strict inequality for every signing, as in the source.
- Non-vacuity / not trivially true: for `d = 2` the analogous conclusion fails for every
  2-regular graph (`not_theoremB_conclusion_two`: every signing has `‖A_σ‖ ≤ 2 = 2√(2−1)`), so the
  conclusion is a genuine property; connected `d`-regular graphs exist for every `d`
  (`complete_graph_connected_regular`).

## Proof-level choices (not affecting the statements)

Recorded in detail in `docs/BLUEPRINT.md`.

- (D) Induced subgraphs are vertex sets `S ⊆ V` of the ambient graph; expectations over uniform
  signs are unnormalised sums over `Sym2 V → ℤˣ`; the paired law uses normalized precisions, so
  zero sources are identity rows. Every "absolute constant", `o(1)` and "sufficiently large `d`" of
  the paper is an existential `∃ C, Eventually …` (absolute constants first, then `κ₀`, then `c₀`,
  then the degree threshold), uniform in the graph. The constants are explicit but huge (e.g. a
  factor `e^{12000}` in `transfer_C4T`). The contact estimate uses the GCI-free DR1 route (see
  Part D, "Proof route").
- (B) The degree is parametrised as `d = n + 3` internally to avoid natural-number subtraction.
  The positivity of the seed is proved directly by Schur complements, so Xu's unicyclic
  Lemma 6.1(i) (source Step 2) is not needed. `h` is chosen through the limit `g_h → 1/√q`. The
  completion to a regular graph is the doubling construction of the source.
- (C2) The threshold is parametrised as `R = q t + 1/t` (`t` the smaller fixed point); the
  construction (triangle seed, `q`-ary trees, iterated joins, centre, regular completion) reuses
  the rooted-graph and Schur-complement infrastructure of Part B. The Challenge form uses the
  explicit `t₀ = (1 − 1/(5q³))/√q`; the paper's form `γ_d ≥ R_q` is also proved
  (`SecondOrder.Explicit.explicit_excess_proof`).

## From `Challenge.lean` to `Solution.lean`

The comparator (`comparator.json`) loads `Challenge` and `Solution` as separate environments and
requires `Solution` to declare the two theorems (`near_ramanujan_signing`, `explicit_excess`) under
the Challenge names, with every declaration used in their statements identical to the Challenge
one. Therefore the proof modules do not import `Challenge`: they import
`BiluLinial/ChallengeDefs.lean`, a verbatim copy of the three definitions of `Challenge.lean`
(`Signing`, `signedAdjMatrix`, `opNorm`, same names and bodies). `BiluLinial/Main.lean` states the
two theorems verbatim (as `near_ramanujan_signing_proof`, `explicit_excess_proof`, together with
the Part B library theorem), and `Solution.lean` restates the two under the Challenge names.
`scripts/check_statements.sh` compares, in the two environments, the universe parameters, types and
bodies of the three definitions and the types of the two theorems; they agree up to the hygienic
names of anonymous instance binders (which embed the module name and are irrelevant to the
kernel). The sanity lemmas in `BiluLinial/Sanity*.lean` are stated for these identical
definitions.

Every file, `Challenge.lean` included, uses the Lean module system: `module`, `public import`, and
`@[expose] public section`. The definitions are therefore public with exposed bodies in both
`Challenge` and `ChallengeDefs`, so importers and the comparator see the same terms as before the
port.

## Known discrepancies

None in the statements. All source proofs are unreviewed drafts; the formalization followed the
DAGs of `docs/BLUEPRINT.md`. No gap was found in the Part B proof or in Section 6 of Part C. The
constant `1/25` in `explicit_excess` is ours (the paper states the excess as
`(1 + O(1/q)) q^{-11/2}`).

The Part D paper (`docs/second_order_bilu_linial_tight.tex`) has local gaps, all repaired without
changing the statement. They are recorded in `docs/BLUEPRINT.md` (Part D, "Audits" and the
section notes):

- implicit hypotheses of the capped source family, which became the context `CapCtx`;
- unevaluated constants (`c₀`, `κ₀`, `d₀`), which became existentials;
- the exponent in (E4) needs `4k*+4 ≤ p−3`;
- the crude C4 majorant loses the rate, so the single-coordinate bound (EPB4) is kept;
- at a zero source the law is not that of a smaller graph, which normalized precisions fix;
- the deletion lemma's ODE lift became a Knaster–Tarski fixed point;
- `ε_BL` is missing in (D10);
- the Brascamp–Lieb step with variable Hessian became BLmid, from midpoint Prékopa–Leindler;
- the whitening step (l.413–424) gives only an absolute `Cp⁴/d` error where a relative one is
  needed, which became a relative transfer (`CapPoint.trans_rel`);
- the remainder transfer asks for own-core moments beyond what (M3) supplies, so low-moment
  variants are used;
- GR1 (Royen's GCI) became DR1, with the companion row comparison CR3′, which does not follow
  from the paper's CR3.
