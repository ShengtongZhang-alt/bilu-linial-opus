# CHECK_CONTACT: pre-dispatch statement checks for `Tight/Contact/Real.lean` and `Inputs.lean`

Workflow rule 2, checks (1) proof sketch and (3) small cases, for every theorem of
`BiluLinial/Tight/Contact/Real.lean` and `BiluLinial/Tight/Contact/Inputs.lean` and the definitions
of `Contact/Defs.lean` they use. Check (2), the parent check, belongs to the drafter (`Chain*.lean`).

**Files read (UTC, 2026-10-01).** `Defs.lean`: 05:22, re-read 05:29 (mtime 05:24:10; the only
change was `ErrRC3`, where `1/√(dh)` became `√(1/(dh))`, equal for `dh > 0`). `Real.lean`: 05:22,
re-read 05:28 (mtime 05:25:46; changes in §R2 and §R13: `d4_real` and `final_assembly_real` now
take `0 ≤ Cp`, `Cp ≤ J`, `Cp ≤ a²L̄s²`, and `fs7_real` uses `EcF`). `Inputs.lean`: 05:22, unchanged
(mtime 05:19:07). All three mtimes were rechecked unchanged at 05:31. `RouteGCI.lean` and
`RouteD9a.lean` were read at 05:28 for the route question only.

**Scripts** (run with `/tmp/tight-venv/bin/python`):

- `scripts/tight/check_contact_d10.py`: exact rational counterexample to `d10_real` when `CB < 0`.
- `scripts/tight/check_contact_params.py`: `param_facts` and the regime bounds the sketches use, at
  1200 digits; also the `ledger_real` summands, critical coefficients and margin.
- `scripts/tight/check_contact_alg.py`: adversarial sampling of `jr_real`, `fs7_real` and
  `rc3_young_real` with the witnesses below, and the worst case of the `d6_real` bootstrap.

## Verdicts

| theorem | verdict |
|---|---|
| `param_facts` | OK (`P₀ = 0`; all 13 facts hold on all of `TRegime`) |
| `d4_real` | OK |
| `d6_real` | OK |
| `d7_real` | OK |
| `d9b_real` | OK (`C` independent of `κ₀`) |
| **`d10_real`** | **FALSE for `CB < 0`; NEEDS FIX: add `0 ≤ CB`** |
| `qP_le_real` | OK (`C` independent of `κ₀`) |
| `fs7_real` | OK |
| `jr_real` | OK |
| `rc3_young_real` | OK |
| `d12_real` | OK |
| `d15_real` | OK |
| `final_assembly_real` | OK |
| `ledger_real` | OK (docstring scalings confirmed; margin ≈ `1/(2p)` − critical part) |
| `ledger_choice` | OK (simpler witnesses below) |
| `in_E1`, `in_C2`, `in_C1`, `in_whiten`, `in_C3a`, `in_markenv`, `in_B1`, `in_S1`, `in_W5`, `in_W1` | OK; all route-independent (`in_W1` is already W1′) |
| `eP`, `ErowP` (Defs) | match the DR1-route `e` and `E_row` up to absolute constants |

Conventions below: `TRegime d p` means `10⁶ ≤ p` and `p¹⁷ ≤ d²`, so `d ≥ p^{17/2}`, `p⁷ ≤ d`,
`p ≤ d`. Note that it gives **no upper bound on `d` in terms of `p`**: every sketch was checked
both at `d = p^{17/2}` and at `d ≫ p^{17/2}` (`p = 10⁶`, `d = 10⁶⁰⁰`). Regime facts used repeatedly:

- (T1) `1/(4d) ≤ a² ≤ 1/d`, `d a² ≤ 1/4 + 1/d`, hence `4 ≤ L_d = 16da² ≤ 5`. These are from
  `param_facts`; `L_d ≥ 4` is just `a² ≥ 1/(4d)`.
- (T2) `δ̄ ≤ 3(p/d)^{1/3} ≤ 3p^{-5/2}`, hence `p³δ̄ ≤ p`. Proof: `ε ≤ (p/d)^{1/3}` because
  `ε ≤ 1/√(pd)`, and `p⁴/d ≤ (p/d)^{1/3}` iff `p¹¹ ≤ d²`. Existing lemmas: `RegA.epsP_le_u`,
  `RegA.p4_div_le_u` (`Tight/SecA/Reg.lean`, with `uOf = (p/d)^{1/3}`) or `le_uOf_of_pow_three_le`;
  `regime_eps_le` (`SecB/Arith.lean`: `ε ≤ p⁻³`).
- (T3) `Γ ≤ √3/p` under `TRegime` alone: `Γ² = p⁹δ̄/d ≤ 3p⁹(p/d)^{1/3}/d ≤ 3p⁻²`. The last step
  is equivalent to `p³⁴ ≤ d⁴`, which is `hpd` squared.
- (T4) `ε_s = p^{3/2}d^{-1/2} ≤ p^{-11/4}`, and `p⁵/d ≤ p^{-7/2} ≤ 1`.

**Lean note.** `TRegime.η0Of_le` (`η₀ ≤ 1/50`), `TRegime.kappa_eq` (`a²s² = τ/(1-τ)²`),
`TRegime.τsOf_le` and `TRegime.qOf_ge` in `Tight/ParamsExtra.lean` are `private`. The
`param_facts` prover needs them: make them public, or re-derive them.

---

## Real.lean

### R1. `param_facts` — OK

**Witness:** `P₀ := 0`. Every fact holds for all `d, p` with `TRegime d p`.

**Sketch.** Write `u = η₀`, `Q = q = d − 1`. From `TRegime.η0Of_eq`, `Q u² = Δ(1−u)` with
`Δ = 4/p`, so `1/p = Q u²/(4(1−u))`. Hence `p` can be eliminated, and every fact becomes a
rational inequality in `u, Q` under the side conditions below.

- Side conditions:
  - `0 < u ≤ 1/50` (`η0Of_le`);
  - `Q ≥ 10⁵¹`;
  - `Q u² ≤ 4·10⁻⁶`, from `p ≥ 10⁶`;
  - `(Qu)² ≥ 3.9 Q/p ≥ 100`, from `Qu² = 4(1−u)/p` and `Q ≥ p^{17/2} − 1`.
- `a² = 1/(4Q+Δ)` (`TRegime.aOf_sq`) gives the three `a²` facts by `one_div_le_one_div_of_le` and
  `field_simp; nlinarith`.
- `ε = u/2`. Then `1/(2√(pd)) ≤ ε ≤ 1/√(pd)` and `η₀ ≤ 2/√(pd)` follow by squaring
  (`Real.le_sqrt`, `Real.sqrt_le_left`):
  - `u² = 4(1−u)/(pQ) ≤ 4/(pd)` iff `d u ≥ 1`;
  - `u² ≥ 1/(pd)` iff `4(1−u)d ≥ Q`.
- `L̄ = d τ/(1−τ)² = (Q+1)Q(1−u)/(Q−1+u)²` (`kappa_eq`) and `s = (2−u)Q/(Q−1+u)`. Then:
  - `1 − rL̄ ≥ 0` needs `u/2 ≳ 3/Q`;
  - `rL̄s² ≤ 4` needs `1.5u ≥ 5/Q + O(u²)`;
  - both follow from `Qu ≥ 10`.
- **Drift reserve.** `dε(1−rL̄) − 1/p + 2u = u/2 − Qu⁴/4 + O(u², u/Q) > 0`, using `Qu³ ≤ 4·10⁻⁶u`.
  Clear the denominators `(Q−1+u)²` and `(1−u)`, then `nlinarith` or `polyrith` with the side
  conditions. This is the hardest of the 13 facts.

**Numerics** (`check_contact_params.py`). All 13 margins are positive in 15 cases: `p = 10⁶…10³⁰`
at the smallest `d` allowed, and `d = 10⁶⁰…10⁶⁰⁰` with `p = 10⁶` and with `p = ⌊d^{2/17}⌋`. In
every case:

- `(dε(1−rL̄) − 1/p)/η₀ = −1.500`, matching AUDIT-D: the reserve is `1/p − 1.5η₀`, and the margin
  against `−2η₀` is `η₀/2`;
- `(rL̄s² − 4)/η₀ = −6.0`.

**Junk:** none (`√(pd) > 0`).

### R2. `d4_real` — OK (re-read after the 05:25 change)

The current hypotheses are `0 ≤ Cp`, `Cp ≤ J` and `Cp ≤ a² L̄ s²`, replacing `0 ≤ J` and
`r·Cp ≤ 4a²`.

**Witnesses:** `C := 4|CQ| + 8|C₃| + 12`, `P₀ := 0`.

**Sketch.**

- Nonnegative pieces:
  - `ε(1−rL) = ε(1−rL̄) + rε(L̄−L) ≥ 0`, using `param_facts` (`1−rL̄ ≥ 0`) and `L ≤ L̄`;
  - `(r/p)J ≥ 0`, because `J ≥ Cp ≥ 0`;
  - `r·sED ≥ 0`, and `(1−1/p)a²S ≥ 0`.
- Bounds on the right-hand side:
  - `r·Cp ≤ r a² L̄ s² ≤ 4a²` (`param_facts`: `rL̄s² ≤ 4`);
  - `Q ≤ |CQ| a²(p + p³δ̄) ≤ 2|CQ| a² p` by (T2);
  - `C₃p⁵/d² ≤ 4|C₃| a² p⁵/d` by (T1).
- First conclusion: `2a²R ≤ a²(2|CQ|p + 4 + 4|C₃|p⁵/d)`.
- Bootstrap: with `−b ≤ R`, `(1−1/p)a²S + r·sED ≤ a²(2|CQ|p + 4 + 4|C₃|p⁵/d + 2b)`. Use
  `1−1/p ≥ 1/2` and `r ≥ 1` to get `S + sED/a²`. For `L̄ − L`, divide the term `rε(L̄−L)` by
  `ε > 0` (`TRegime.one_lt_rOf`).

`CQ < 0` makes the hypothesis on `|Q|` unsatisfiable, and `C₃ < 0` only helps; the proof uses
`|CQ|` and `|C₃|`.

**Lemmas:** `abs_le`, `le_div_iff₀`, `div_le_div_iff₀`, `nlinarith`.

**Junk:** none (`a² > 0`, `ε > 0`).

### R3. `d6_real` — OK

Write `A := |C₁|`, `B := |C₄|`.

**Witnesses:** `C := 60(B+8)²(A+1)² + 2|Ca| + 6`, and `P₀ := ⌈2|Cw|⌉ + 1`, so that
`|Cw|p⁴/d ≤ |Cw|p^{-9/2} ≤ 1/2`.

**Sketch.** Set `λ := a²S + A2 + ϑ` and let `E` be the right-hand side of the CR1 hypothesis.

1. `E ≥ |R − Gt| ≥ 0`, and `Gt ≥ 0` gives `R ≥ −E`. The bootstrap with `b := E` gives
   `S ≤ B(1 + p + p⁵/d + E)`. A negative `C₁` or `C₄` makes the hypotheses inconsistent.
2. `Gt ≤ R + E ≤ B(p + p⁵/d) + E`.
3. `W(1 − |Cw|p⁴/d) ≤ 2a²Gt + |Cw|p⁴ϑ/d`, so `W ≤ 4a²Gt + ϑ`. Then
   `A2 ≤ 2W + |Ca|ϑ ≤ 8a²Gt + (2+|Ca|)ϑ`.
4. With `a² ≤ 1/d` and `1 + p + p⁵/d ≤ 3p`:
   `λ ≤ 27Bp/d + (B+8)E/d + (3+|Ca|)ϑ`.
5. Young (`two_mul_le_add_sq`):
   `(B+8)A p⁵√(λδ̄)/d ≤ λ/2 + (B+8)²A² p¹⁰δ̄/(2d²)`.
6. Each leftover term is at most `p/d` in `TRegime`:
   - `p¹⁰δ̄/d² ≤ 3p/d` iff `p⁷ ≤ d`, by (T2);
   - `p¹³/d³ ≤ p/d`;
   - `ϑ ≤ p/d`.

**Numerics.** The worst case of the bootstrap (largest fixed point of the hypotheses, with
`C₁ = C₄ = Cw = Ca = 1`) is `λ·d/p = 1.25` at `(p, d) = (10⁶, 10⁵¹), (10⁶, 10¹²⁰),
(10⁹, 10^{76.5}), (10³⁰, 10²⁵⁵)`. It is uniform in `d` and `p`.

**Junk:** the argument of `√` is `≥ 0`.

### R4. `d7_real` — OK

Write `B₁ := |C₁|(√(3|C₆|) + 2)`.

**Witnesses:** `C := 2|C₄|(3 + B₁) + 1`, `P₀ := 0`.

**Sketch.**

- Let `b :=` the right-hand side of the CR1 hypothesis. Then `b ≥ 0` and `−b ≤ R` because `Gt ≥ 0`.
- From `λ ≤ C₆p/d`: `p⁵√(λδ̄) ≤ √|C₆|·pΓ ≤ √(3|C₆|)` by (T3), and `p¹³/d² + ϑ ≤ 2`. So `b ≤ B₁`.
  A negative `C₆` is impossible, since `λ ≥ ϑ > 0`.
- The bootstrap gives `S + sED/a² ≤ |C₄|(3+B₁)p`.
- `L̄ − L ≤ |C₄|(3+B₁)·a²p/ε ≤ 2|C₄|(3+B₁)ε_s`, since `a²p/ε ≤ (1/d)·p·2√(pd) = 2ε_s` (T1 and
  `param_facts`).

**Junk:** `sED/a²` with `a² > 0`.

### R5. `d9b_real` — OK

**Witnesses:** `C := 4|C₄| + 4|C₉|(√(|C₇|+1) + 1) + 2|CB| + 1`. It does not depend on `κ₀`, as
required. `P₀(κ₀) := max(10⁶, ⌈4(|CB|+1)/κ₀⌉)`, which gives `|CB|η_BL ≤ 1/2` and `ε_BL ≤ 1`. Here
`η_BL = p⁴/d + p⁵/(κ₀d) ≤ 2p^{-7/2}/κ₀`.

**Sketch.**

- If `Qb < 0` the conclusion is trivial.
- Otherwise `Qb/2 ≤ (1 − CBη)Qb ≤ Gt + |CB|ε_BL`. This holds for either sign of `CB`.
- `Gt ≤ R + |C₉|Erow`, with:
  - `R ≤ 2|C₄|p`;
  - `Γ√(S+1) ≤ (√3/p)√(|C₇|p+1) ≤ 2√(|C₇|+1)`, by (T3) and `S ≤ C₇p`;
  - `p¹³/d² + ϑ ≤ 2`.

**Junk:** `√(S+1)` with `S ≥ 0`.

### R6. `d10_real` — FALSE when `CB < 0`; NEEDS FIX

**Counterexample** (exact, `check_contact_d10.py`). Fix any `C`.

- Constants: `CB = −1, C₉ = 1, C₉b = 1, Cc = 0`.
- Point: `d = 10⁵¹, p = 10⁶` (`p¹⁷ = d²`, so `TRegime` holds), `h = 1`, `S = 0`.
- Variables: `η := p⁴/d + p/d`, `M := (C·U + ε_BL)/η + 1` with a rational `U ≥ Err10`,
  `Qb = Qf = −M`, `Gt = R = −(1+η)M + ε_BL`.
- All four hypotheses hold: the first with equality, then `|R−Gt| = 0 ≤ ErowP`, `Qb ≤ p`, and
  `Qf ≤ Qb`.
- The conclusion `Qf − C·Err10 ≤ R` reduces to `ηM ≤ C·Err10 + ε_BL`, and it fails by exactly
  `η > 0`.

The cause: with `CB < 0`, `(1 − CBη)Qb` is unbounded below, at rate `|CB|η·|Qb|`, as `Qb → −∞`.

**Fix:** add `(hCB : 0 ≤ CB)`. The chain instantiates `CB` with `in_B1`'s constant, which is
positive. Alternatively add `0 ≤ Qb` (true, since `Qbl ≥ 0`), but `0 ≤ CB` is simpler.

**Sketch with the fix.** Witness `C := |Cc| + CB·|C₉b| + CB + |C₉| + 1`, no regime facts needed.

- `R ≥ (1−CBη)Qb − CBε_BL − |C₉|Erow`.
- `−CBηQb ≥ −CBη|C₉b|p` in both cases:
  - `Qb ≥ 0`: use `Qb ≤ C₉b p`;
  - `Qb < 0`: the term is `≥ 0`.
- `ηp = p⁵/d + p²/(dh)`, and `Qf − Cc·p/(dh√h) ≤ Qb`.
- Every summand of `Err10` is `≥ 0` for `h > 0`.

`S` is unconstrained, but the junk `√(S+1) = 0` for `S < −1` is harmless, because the same `S`
appears in the hypothesis and in the conclusion.

### R7. `qP_le_real` — OK

**Witnesses:** `C := |C₉b| + 1`, independent of `κ₀`. `P₀(κ₀) := max(10⁶, ⌈(|Cc|+1)/κ₀^{3/2}⌉)`,
so that `|Cc|p/(dh^{3/2}) = |Cc|p⁷/(dκ₀^{3/2}) ≤ 1`.

**Sketch.**

- `L_d ≥ 4` by (T1), and `p·qm ≥ 0`.
- So `(p−1)qp ≤ (|C₉b|p + 1)/4`, i.e. `qp ≤ (|C₉b|+1)/2`.
- A negative right-hand side gives `qp ≤ 0` directly.

**Junk:** `√h` with `h = κ₀/p⁴ > 0`.

### R8. `fs7_real` — OK

**Witness:** `K := 3(1+|Cw|)²(1+|Cq|)`.

**Sketch.** Write `c := |Cw|`; `|r| ≤ Cw·X` with `X ≥ 0` gives `|r| ≤ cX`. Let
`r₁ := ζ − z − α`, so `ζ − α = z + r₁ ≤ z + |r₁|`.

- `√(z+θ) ≤ √z + √θ`, so `|r₁| ≤ c(e√z + e√θ + B₀)`.
- `√(ζ−α+bh(q−t)+θ) ≤ √z + √|r₁| + √|Cq|·√bh + √θ`, using `q − t ≤ Cq`.
- AM–GM: `e√|r₁| ≤ √c·(3e² + e√z + e√θ + B₀)/2`, from `e√(e√z) ≤ (e² + e√z)/2` and similar.
- Every coefficient is then at most `c(1 + 1.5√c + √|Cq|) ≤ K`.
- Mixed residuals: the third uses the same bound as the first; the fourth is
  `≤ c(e√zm + e√θ + B₀)`.

A helper `√(x+y) ≤ √x + √y` (from `Real.sqrt_le_iff`, `Real.sq_sqrt`, `nlinarith`) is needed;
Mathlib has no `Real.sqrt_add_le`.

**Numerics:** 3·10⁵ samples with all four residuals saturated; minimum relative slack `0.9`.

**Junk:** every `√` has a nonnegative argument (`α ≤ ζ`, `θ, bh, z, zm ≥ 0`).

### R9. `jr_real` — OK

**Witness:** `K := 2|C₁| + |C₂| + 9`. No regime is needed (`2 ≤ p` only).

**Sketch.** Write `r₀ = q−ζ−t`, `r₁ = ζ−z−α`, `r₂ = qm+ζm−tm`, `r₃ = ζm+zm−β`, each `|rᵢ| ≤ E`.

1. **Exact algebra.**
   `𝒫 − (p−1)z/2 − p·zm/2 = (p−1)ζ/2 + (p−1)α/2 + p·zm/2 − pβ + [(p−1)(r₀ + r₁/2) + p(r₂ − r₃)]`.
   The bracket is at least `−3.5pE`.
2. **JR3 from the Gram facts.** `ζm² ≤ qm·zm` with `qm, zm ≥ 0` is the 2×2 Gram matrix PSD; test
   `b₋ − λw` with `λ = β/(tm+β) ∈ [0,1]`:
   - `zm ≥ β²/(tm+β) − 4E ≥ β²/(1+β) − 4E − |C₁|ε`;
   - if `tm + β = 0` then `β = 0` and the bound is trivial.
3. **RC2.** `f(x) = x²/(2(1+x)) − x` has `f′ ∈ [−1, −1/2]`, so `f(β) ≥ f(α) − |C₂|ξ`.
4. **α-cap, uniform in `E, ε`.**
   - `ζ² ≤ qz ≤ (ζ+1+e′)(ζ−α+E)` with `e′ = |C₁|ε + E`, which gives
     `α(1+ζ+e′) ≤ ζ(1+e′+E) + (1+e′)E`.
   - Hence `α ≤ ζ/(1+ζ) + e′ + 2E`, valid for all `E, ε ≥ 0`, not only small ones.
   - Put `α̂ := (α − (|C₁|+3)(E+ε))₊`. Then `α̂ ≤ ζ/(1+ζ) < 1` and `ζ ≥ α̂/(1−α̂)`.
5. **Monotonicity.** `H(ζ,α) = (p−1)ζ/2 + (p−1)α/2 + p·f(α)` has `∂_α H ≥ −(p+1)/2` and
   `∂_ζ H > 0`. Then
   `H ≥ H(α̂/(1−α̂), α̂) − p(|C₁|+3)(E+ε) ≥ (p−1)α̂² − α̂ − … ≥ −1/(4(p−1)) − …`
   (l.1900–1905).
6. **Total.** The error is at most `p(E+ξ)(2|C₁| + |C₂| + 8.5)`, using `ε ≤ ξ`.

The hypotheses `0 ≤ t` and `t ≤ q` are not needed (harmless).

**Numerics** (`check_contact_alg.py`):

- 10⁵ feasible adversarial points (`p ∈ {2, 3, 5, 10, 100, 10⁶}`, `E, ξ` from 0 to 10³, residuals
  at `±E`); minimum relative slack `+2.5·10⁻⁷`;
- the tight family at `E = ξ = 0` gives `min (𝒫 − base)·4(p−1) = −0.669, −0.800, −0.947, −0.9995`
  for `p = 2, 3, 10, 1000`, always `≥ −1`.

### R10. `rc3_young_real` — OK

**Witness:** `K := 1.5K₁² + |K₁| + 1`.

**Sketch.**

- `|K₁|pe√z ≤ (p−1)z/2 + K₁²p²e²/(2(p−1)) ≤ (p−1)z/2 + K₁²pe²`, using `p/(p−1) ≤ 2`.
- `|K₁|pe√zm ≤ p·zm/2 + K₁²pe²/2`.

**Numerics:** 3·10⁵ samples, minimum slack `0` (attained when everything is zero).

### R11. `d12_real` — OK

**Witnesses:** `C := |C₁₀| + 5|C₃| + 10|C₄| + 1`, `P₀ := 0`.

**Sketch.**

- Decompose:
  `R − L_d[(p−1)tp0 + p·tm0] ≥ L_d[(p−1)(qp−tp) + p(qm−tm)] + L_d[(p−1)(tp−tp0) + p(tm−tm0)] − C₁₀Err10`.
- Use `0 ≤ L_d ≤ 5` (T1), the RC3 hypothesis, and `tp0 − tp ≤ |C₄|√h`.
- `Err12 = Err10 + p·ErrRC3 + p√h`, and all its summands are `≥ 0` for `h > 0`.

### R12. `d15_real` — OK

**Witnesses:** `C := 11|C₇| + 48`, `P₀ := ⌈8|C₇|⌉ + 1`, which makes
`X := L̄ − 1.01|C₇|ε_s − 4/d ≥ 1/4`.

**Sketch.**

- `rDp − 1 ≥ r(1 + L̄ − C₇ε_s − a²L̄s²) − 1 ≥ X > 0`, using `r ≥ 1`, `r ≤ 1.01` (`rOf_le`),
  `r·a²L̄s² ≤ 4a² ≤ 4/d`, and `L` bounded below only.
- `n = 0` contradicts `(rDp−1)² ≤ 0`, so `n > 0`.
- Then `S ≥ X²/(a²n) ≥ X²/(a²d)`.
- Using `L̄ = da²s²`:
  `X²/(a²d) ≥ L̄s² − 2s²(1.01|C₇|ε_s + 4/d) ≥ 4 − 8η₀ − 10.1|C₇|ε_s − 40/d`, with `s² ≤ 5`.

**Small cases:** `n = 0` is excluded by the other hypotheses, so the statement is not vacuous in
this case. `L > L̄` is allowed and only helps.

### R13. `final_assembly_real` — OK (re-read after the 05:25 change)

The current hypotheses are `0 ≤ Cp`, `Cp ≤ J` and `Cp ≤ a²L̄s²`, replacing `r·Cp ≤ 4a²`.

**Witnesses:** `K := |C₃| + |C₁₃| + 7|C₁₂| + 2C₁₂² + |C₁₅| + 1`, `P₀ := 0`.

**Sketch.**

1. From D3, drop `rε(L̄−L)` and `r·sED`, and use `(r/p)J ≥ (r/p)Cp` and
   `r(1−1/p)Cp ≤ 4(1−1/p)a²`. This gives
   `ε(1−rL̄) ≤ Q − 2a²R − (1−1/p)a²(S−4) + |C₃|p⁵/d²`.
2. Combine with `R ≥ L_dTc − L_dc_p − |C₁₂|Err12(S)` (D12) and
   `Q ≤ 2a²L_dTc + |C₁₃|a²p³√(pδ̄/d)` (D13); `Tc` cancels for either sign.
3. **Absorption.** Let `γ := |C₁₅|(ε_s + η₀ + 1/d)` and `S′ := S − 4 + γ ≥ 0` (D15). Use
   `√(S+1) ≤ √S′ + √5` and `−(1−1/p)S′ + 2|C₁₂|Γ√S′ ≤ 2C₁₂²Γ²`. The `S`-terms are then at most
   `γ + 5|C₁₂|Γ + 2C₁₂²Γ²`.
4. Multiply by `d`:
   - `dε(1−rL̄) ≥ 1/p − 2η₀` (`param_facts`);
   - `d·2a²L_dc_p = 32(da²)²c_p ≤ 2(1+4/d)²c_p ≤ 2(1+9/d)c_p` for `d ≥ 16`;
   - `da² ≤ 1/2`.
   Every remaining term is a summand of `TotErr`.

### R14. `ledger_real` — OK

**Witnesses:** `Ccrit := 24(|K|+1)`, and `P₀(c₀, κ₀, K)` such that
`(1+9/d)/(2(p−1)) + 1/(64p) + 10|K|κ₀^{-3/2}p^{-3/2} + 2η₀ < 1/p`, e.g.
`P₀ := ⌈(2000(|K|+1))²κ₀⁻³⌉ + 10⁶`.

**Sketch.** With `d ≥ (p/c₀)^{17/2}` and `h = κ₀p⁻⁴`:

- Critical terms:
  - `p√h` appears twice in `TotErr` (directly and inside `p·ξ ⊂ p·ErrRC3`), giving `2√κ₀/p`;
  - `Γ ≤ √3·c₀^{17/3}/p` (proof of T3 with `d ≥ (p/c₀)^{17/2}`);
  - `pe² = pΓ²/κ₀² ≤ 3κ₀⁻²c₀^{34/3}/p`, from the exact identity `e = Γ/κ₀`.
- Every other summand is at most `10κ₀^{-3/2}p^{-3/2}` (uses `c₀, κ₀ ≤ 1`). The largest are
  `p/(dh^{3/2})` and `pB₀`, about `c₀^{17/2}κ₀^{-3/2}p^{-3/2}`.
- So `K·TotErr ≤ 3|K|·(√κ₀ + c₀^{17/3} + κ₀⁻²c₀^{34/3})/p + rest ≤ 1/(64p) + rest`.
- `2(1+9/d)c_p = (1+9/d)/(2(p−1))`.

**Numerics** (`check_contact_params.py`).

- At `p = ⌊c₀d^{2/17}⌋` (`d = 10²⁰…10³⁰⁰`; `c₀, κ₀ ∈ {1, 10⁻², 10⁻⁶}`), the ratios
  `(p√h)·p/√κ₀`, `Γp/c₀^{17/3}` and `pe²·pκ₀²/c₀^{34/3}` are all `1.000`. The docstring bounds
  `√3` and `3` hold with room.
- `p·TotErr/(2√κ₀ + c₀^{17/3} + κ₀⁻²c₀^{34/3}) → 1`.
- `rest·p^{3/2}κ₀^{3/2} ≈ 2c₀^{17/2}`, which confirms `O(κ₀^{-3/2}p^{-3/2})`.
- With `K = 1`, `Ccrit = 48` and the `ledger_choice` witnesses (`κ₀ = 7.2·10⁻⁷`,
  `c₀ = 4.4·10⁻¹⁶`), `p(1/p − LHS) = 0.498` at `d = 10⁷⁰⁰…10³⁰⁰⁰`. The margin is `1/2` minus the
  critical part; the docstring's `3/(8p)` is the worst case once the critical coefficient is `1/8`.

**Junk:** none (`c₀, κ₀ > 0` for `rpow` and `⁻¹`).

### R15. `ledger_choice` — OK

**Simpler witnesses** (no fractional `rpow` inverses): `κ₀ := (24Ccrit + 24)⁻²` and
`c₀ := κ₀²/(24Ccrit + 24)`, both in `(0, 1]`.

- `Ccrit√κ₀ ≤ 1/24` (`Real.sqrt_sq`).
- `c₀^{17/3} ≤ c₀` and `c₀^{34/3} ≤ c₀` by `Real.rpow_le_rpow_of_exponent_ge` (base `≤ 1`,
  exponent `≥ 1`) and `Real.rpow_one`.
- So each of the other two terms is `≤ 1/24`.

Numerically `Ccrit·(…) = 0.0408 ≤ 1/8` at `Ccrit = 48`. The docstring's
`min(1, (24C)^{-3/17}, …)` witnesses also work.

---

## Inputs.lean

All inputs have the shape `∃ C > 0, Eventually …`: an absolute `C`, then `c₀, κ₀`, then
`D(c₀, κ₀)`, at `p = ⌊c₀d^{2/17}⌋` and `h = κ₀p⁻⁴`. That is the order of AUDIT-D §4.1, and all
statements are uniform in the graph and its order. `in_C1` has no constant. `in_W5 m` has `C(m)`
with `m` fixed by the chain, which is fine.

Exponentially small terms `e^{−cp}` are replaced by `ϑ = d⁻¹⁰`. This is valid inside `Eventually`,
because `p ≥ c₀d^{2/17}/2` gives `e^{−cp} ≤ d⁻¹¹` for `d ≥ D(c₀)`. That covers C3a's `0.52^{⌊p/4⌋}`,
B1's `e^{−2p}` and the `d·e^{−cp}` produced by dividing by `a²`.

**Junk-value audit of the shared definitions.**

- `lawE` divides by `Zw > 0`: the contact point lies in `[0, λs] ⊆ [0, s]` and `CapCtx.pos`
  applies.
- `Gterm` divides by `a²·coreE(radE Φ)`. Here `ZwCore > 0`, because principal blocks of a PD
  `precN` are PD. `F_H > 0`, because a supported `σ` has `α, β > 0` at its own root signs.
  So `Gterm` is not a junk `0`. This matters: `in_B1` and `in_whiten` use `Gterm` as an upper
  bound.
- `greenP` and `shiftP` equal `y_i` (not `0`) at `i ∉ S`, from the identity padding. This never
  leaks:
  - `N`, `N(N)`, `adjS`, `uvec`, `b_±` all live in `S`;
  - `(X²)_ii` for `i ∈ S` only sees the `S`-block, since the matrix is block diagonal.
- `rowNum` uses `p − 2` in ℕ, which is harmless since `p ≥ 10⁶`. `gaussE` of a
  polynomially bounded continuous function is a genuine integral (`A, B ⪰ 0` on the support).

| input | paper | audits | Lean matches? | route |
|---|---|---|---|---|
| `in_E1` | Lemma "Endpoint calculus" (E1) l.261–293; `𝒟₁x_i`, `K_i` l.1370–1391 | AUDIT-A §2.2 (A6), AUDIT-D §3.1 D3 | yes: `𝒟₁x_i = −aP_i + (2p−1)ax_i² − 2pax_iz_i`, `𝒟₃x_i = a³K_i`, error `Cp⁵a⁵` (moment caps `ED⁶ ≤ C`); `Kpoly` matches l.1372–1383 term by term | independent |
| `in_C2` | (C2) l.378–385 at the root | AUDIT-A §2.15, AUDIT-B §2.1 | yes: the row parts `a²S_± ≤ Cδ̄` and core parts `E trA², E trB² ≤ Cδ̄` (the full-law expectation of a core function is the actual-core expectation) | independent; see note (N1) |
| `in_C1` | `N_G ≥ 0` l.373–376, l.393–397; `N_G = 2𝖦F` l.1249–1250 | AUDIT-A §2.9, AUDIT-C §5.3(a) | yes (`rowNum` = `F` of (E5)) | independent (Prékopa / BLmid) |
| `in_whiten` | l.413–424 (`N_G ≥ f_Gw`) and l.1463–1472 (transfer of `wΦ`) | AUDIT-A §2.11, AUDIT-C §6 (D6) step 4 | yes: `Ew ≤ E_{ν_K}(wf_G)/F_H + C(p⁴/d)(Ew+ϑ) ≤ 2a²Gterm + …`; the factor 2 is `N_G = 2𝖦F` | independent |
| `in_C3a` | (C3a) l.428–435 | AUDIT-A §2.11 (`0.52^{⌊p/4⌋}`) | yes: `T_A1{μ≤1} ≤ 2w` and `E[T_A1{μ>1}] ≤ ϑ` eventually | independent |
| `in_markenv` | l.1129–1149 | AUDIT-C §4.2 MARKENV | yes: `S/d ≤ 4a²S ≤ 4λ` (`a² ≥ 1/(4d)`, `trA2 ≥ 0`); Schur `G[N,N] = G_K[N,N] + xxᵀ/G_vv` plus interpolation with floor `λ ≥ ϑ` | independent |
| `in_B1` | Lemma "Multiplicative shifted trace comparison" (B1) l.1192–1331 | AUDIT-C §4.3 (BLmid, §5.3) | yes: AUDIT-C's assembly is exactly `Gterm ≥ (1−η_BL)Q − ε_BL` with `η_BL = C(p⁴/d + p/(dh))` and `ε_BL = C(p⁵+p²/h)ϑ + e^{−2p}`; `Qbl` uses the core shift (`coreShift` on `S−v`) and `tr Y² = Σ_{ij}Y_ij²` (symmetric) | independent |
| `in_S1` | (S1) l.696–719 | AUDIT-B §2.3, B-7 | yes, physical form `0 ≤ E(G_ii − X_ii) ≤ C√h·y_i`. `≥ 0` is pointwise (`P̃ + hY ⪰ P̃ ≻ 0`). `K_S` is absolute with threshold `d_S(c₀, κ₀)` | independent |
| `in_W5` | (W5) l.790–797 | AUDIT-B §2.4 | yes, for every `i ∈ S`: `X² ⪯ h⁻¹(G−X)` plus S1 plus interpolation; the loss `h^{−O(1/p)} = O(1)` | independent |
| `in_W1` | Lemma "Random-profile weak loop" (W1)–(W4) l.721–911 | AUDIT-B §2.4, B-2, B-3; DR1_CHECK §3 W1′ | yes. The four residuals check out: `(+,+)` with `f = u` gives `q₊−ζ−t₊`, `f = b₊` gives `ζ−z₊−α`; `(−,+)` with `w = u + b₋` gives `q₋+ζ₋−t₋` and `ζ₋+z₋−β`. Both root-weight derivatives are re-derived: `dOmP = −aG⁺_vvG⁺_viG⁺_vj` and `dOmM = (a/2)(G⁺_vvG⁻_viG⁻_vj − G⁺_viG⁺_vjG⁻_vv)`. `maskF` matches; `score` sums over `j ∈ N_S(i)`, including `j = v` | **already W1′** (exact difference score `|G⁺_ij − G⁻_ij|`; remainder `B₀` needs only `ρ_row = C(δ̄+1/d) ≤ Cp⁻²` from (C2) at every `i ∈ N`); valid on both routes |

**(N1) `in_C2` covers only the root `v`.** The DR1 route also needs (C2) at **every** `w ∈ S`:

- DR1 at the neighbours `i ∈ N(v)` (FS5′), and W1′'s `ρ_row` at `i ∈ N`;
- in the form of `C2RowShape` (`Tight/SecB/RouteDR1.lean`): deficits `1 − Eh^±_w ≤ K_δδ̄` and row
  masses `a²S^±_w ≤ K_δδ̄`.

The paper's (C2) is a `sup` over vertices, so this is a restatement, not a new fact. Derive DR1
from `dr1_of_c2` with the all-vertex (C2) of Section A, not from `in_C2`.

### Defs vs the DR1 route (DR1_CHECK §3–4)

- **`eP = √(pδ̄)/(√d·h)`.** DR1's `e = (p√δ_Δ + √(λ₁+δ))/(√d·h)`, with `δ_Δ = K_DR·δ/p` and
  `δ = Cδ̄`, satisfies `e ≤ (√(K_DR·C) + √(2C))·eP`, using `λ₁ = Cp/d ≤ Cδ̄`. The paper's
  `p√δ_row/(√d·h)` is `√C·eP`. **Matches** up to an absolute factor; FS6, FS7, JR2 and RC3 are
  unchanged.
- **`ErowP = Γ√(S+1) + p¹³/d² + ϑ`.** D9a′ gives `C₉{Γ√(S+1) + Γ + p¹³/d²} + e^{−3p}`, and for
  `S ≥ 0`, `Γ ≤ Γ√(S+1)`. The term `p⁵√(λ_r·ρ_Δ)` with `λ_r = 4(S+1)/d` and
  `ρ_Δ = 4(|Cr|+1)δ̄/p` equals `4√(|Cr|+1)·Γ√(S+1)` exactly. **Matches.**
- **D13 hypothesis of `final_assembly_real`** (`C₁₃p³√(pδ̄/d)`) is D13′: `p³√(λ₁δ) = Cp³√(pδ̄/d)`,
  and `p³λ₁ = Cp⁴/d ≤ Cp³√(pδ̄/d)` because `p/d ≤ δ̄`. It is valid on both routes.

### DR1-route replacements for `RouteGCI.lean` / `RouteD9a.lean`

These two files are outside the requested scope; this answers the route question. Only `in_GR1`
uses GCI. `in_CR3` and `cr1` are conditional or route-independent statements; `cr1` can keep its
CR3-based proof with `ρ_r = δ_c = Cδ̄` from (C2), since that proof does not use GR1. D9a needs CR3′
plus DR1. Proposed Lean statements:

```lean
/-- I-DR1 [route DR1] (DR1_CHECK §2; from `dr1_of_c2` with the all-vertex (C2)). -/
theorem in_DR1 : ∃ C : ℝ, 0 < C ∧ Eventually fun _c₀ _κ₀ d p _h =>
    ∀ ct : Contact.{u} d p, ∀ w ∈ ct.S,
      aOf d p ^ 2 * ∑ j ∈ nbhd ct.G ct.S w,
        ct.E (fun σ => (ct.gp σ w j - ct.gm σ w j) ^ 2) ≤ C * dbar d p / p

/-- I-CR3′ [route DR1] (DR1_CHECK §3; `p⁴λ_r ≤ p⁴√(λ_c δ_c)` by the ordering). -/
theorem in_CR3' : ∃ C : ℝ, 0 < C ∧ Eventually fun _c₀ _κ₀ d p _h =>
    ∀ ct : Contact.{u} d p, ∀ lr rd lc dc : ℝ, vth d ≤ lr → lr ≤ lc → lc ≤ dc → dc ≤ 1 →
      vth d ≤ rd → ct.Srow / d ≤ lr → ct.Smin / d ≤ dc →
      (∑ j ∈ ct.N, ct.E (fun σ => (ct.x σ j - ct.z σ j) ^ 2)) / d ≤ rd →
      ct.frobP / (d : ℝ) ^ 2 ≤ lc → ct.frobM / (d : ℝ) ^ 2 ≤ dc →
      |ct.Rrow - ct.Gterm| ≤ C * ((p : ℝ) ^ 5 * Real.sqrt (lr * rd) +
        (p : ℝ) ^ 4 * Real.sqrt (lc * dc) + (p : ℝ) ^ 13 / (d : ℝ) ^ 2) + C * vth d
```

`d9a_real′` keeps `d9a_real`'s statement with two changes:

- the GR1 hypothesis `a²·Sm ≤ Cr·δ̄/p` becomes `0 ≤ Dv` and `a²·Dv ≤ Cr·δ̄/p`, where
  `Dv = Σ_N E(x−z)²` (DR1 at `v`);
- the CR3 callback becomes CR3′'s: `vth ≤ lr ≤ lc ≤ dc ≤ 1`, `vth ≤ rd`, `S/d ≤ lr`, `Sm/d ≤ dc`,
  `Dv/d ≤ rd`, plus the `fP`, `fM` bounds.

Its conclusion `|R − Gt| ≤ C·ErowP d p S` is **true**, with these witnesses:

- `lr = 4(S+1)/d` and `rd = 4(|Cr|+1)δ̄/p` (`Dv/d ≤ 4a²·Dv`);
- `lc = (|CM|+4)(|C₆|+|C₇|+2)p/d` (MARKENV with the envelope `C₆p/d`, `S ≤ C₇p`);
- `dc = 4(|CM|+4)(2|C₂|+1)δ̄` (MARKENV minus with `l = a²Sm + B2 + ϑ ≤ (2|C₂|+1)δ̄`, using
  `vth_le_dbar`).

The orderings hold for large `p`: `lc ≤ dc` because `p/d ≪ (p/d)^{1/3}`, and `dc ≤ 1` by (T2).
Then `p⁴√(lc·dc) = O(Γ) ≤ O(Γ√(S+1))`.
