# DR1_CHECK: is Royen's Gaussian correlation inequality needed for the upper bound?

Source: `docs/second_order_bilu_linial_tight.tex` (Section 1, upper bound). Audits compared:
`AUDIT_B.md` §3.3 (proposes the GCI-free route DR1), `AUDIT_C.md` G8 and §9, and `AUDIT_D.md` G8,
X1 and §4.2 (which call GR1 essential). Scripts: `scripts/tight/dr1_enum.py` (exact enumeration of
the paired law) and `scripts/tight/dr1_ledger.py` (exact exponent ledger). Run both with
`/tmp/tight-venv/bin/python`.

---

## 0. Verdict

**CONFIRMED.** The GCI-free route of AUDIT_B §3.3 is correct. GCI enters the upper bound only
through Lemma "Uniform incident-row gain" (GR1, l.626–693). Every downstream use of GR1 is one
of two kinds:

- it needs only the energy of the **branch difference** `G⁺_ij − G⁻_ij`, which is the
  determinant score `∂_ij log W = 2pa(G⁺_ij − G⁻_ij)`; or
- it is already satisfied by the concentration envelope `δ` of (C2), or by `δ` up to an
  `o(1/p)` loss.

The difference energy is bounded by `K_DR δ/p` (DR1), with `K_DR` absolute. The proof uses only
the two exact root-row equations, the first-order endpoint identity, the moment caps and (C2).
It uses no sign of the cross term `T_v`, so no GCI. With DR1 and four restated lemmas (W1′, FS5′,
CR3′/D9a′, D13′), the end-game ledger (D16) closes with the **same three critical terms, the same
exponents, and the same quantifier order**:

- absolute constants first, then `κ₀`, then `c₀`, then `d₀(c₀, κ₀)`;
- the critical terms are `p√h = √κ₀/p`, `Γ ≤ C c₀^{17/3}/p` and `pe² ≤ C κ₀^{-2} c₀^{34/3}/p`;
- the rate is `2/17`.

**No use of GCI remains.** What remains are the Prékopa / Brascamp–Lieb covariance bounds of
(C1), the (C2) whitening step, (WT3) and (B1) (midpoint Prékopa–Leindler, AUDIT_C §5). These are
separate long poles; DR1 does not touch them.

**On the disagreement.** AUDIT_C G8 and AUDIT_D G8 are correct *about the estimates written in
the paper*: those estimates bound individual rows, and without GR1 they lose a factor `√p`. Their
conclusion that GCI cannot be bypassed does not follow, for two reasons:

- the dangerous terms involve individual rows only through the way the paper bounds them;
  rewritten, they involve only the difference (§3);
- AUDIT_D's claim that W1's *remainder* needs GR1 is wrong: it needs only `ρ_row ≤ Kp^{-2}`,
  which `δ` satisfies (§1, use U1).

The numerical checks in `AUDIT_C`/`AUDIT_D` reproduce exactly (§5): with no row gain at all,
the D9a term is `c₀^{17/3}p^{-1/2}` and `pe² = Θ(1)`.

---

## 1. Every use of GCI and of GR1

**GCI.** It is used once, in the proof of GR1 (l.637–648), to get
`𝖦[q_AB α^{p−1}β^{p−1}] ≥ 0`. Through the E4 transfer (l.650–671) this gives
`T_v := Σ_{i∼v} E G⁺_vi G⁻_vi ≤ Cp⁴`. That inequality is used only in the line
`(2p−1)a²S_v = B_v + 2pa²T_v + O(p³/d)` of the same proof. GCI appears nowhere else: a grep for
"Royen", "Milman", "correlation" and "GR1" finds only l.626–693 and the uses below.

**GR1** (`a²Σ_{i∼v}E(G^ν_vi)² ≤ δ_row = Cδ/p`) is used in five places. The end game tolerates
an error `c/p` with `c` small (the true margin `1/p − 2c_p ≈ 1/(2p)`, of which the paper allots
`1/(4p)`). Write `≪ 1/p` for `o(1/p)` at fixed `c₀, κ₀`. All values are at `p = ⌊c₀d^{2/17}⌋`,
`h = κ₀p^{-4}`, `δ ≍ c₀^{17/6}p^{-5/2}`.

| id | place | what is really bounded | required size | paper (GR1) | GCI-free replacement |
|---|---|---|---|---|---|
| U1 | W1 remainder, l.840–903 | `E[D_*^C R_ij^k]`, `R_ij = |G⁺_ij|+|G⁻_ij|`, averaged over `i∈N, j∼i` | `ρ_row ≤ Kp^{-2}` (so `p³ρ+p²√ρ ≤ Kp`) | `δ_row` | `ρ_row = K(δ+1/d)` from (C2): `p³δ ≍ p^{1/2}`, `p²√δ ≍ p^{3/4}` ✓ |
| U2 | FS5 determinant part, l.1752–1756 | score `2paH(·)` at the **neighbours** `i∈N(v)`: `Σ_{j∼i} a²E[·]²` | `pe² ≤ c/p` | `(|G⁺_ij|+|G⁻_ij|)`, GR1 at `i` | exact score `|G⁺_ij−G⁻_ij|` (W1′), **DR1 at `i`** |
| U3 | FS5 root-weight part (via FS4), l.1743–1752 | `a²(S⁺_v+S⁻_v)` at the contact vertex `v` | same | GR1 at `v` | `λ₁ + δ` (D6 and C2); smaller than U2 by `√p` |
| U4 | D9a / CR3 `ρ_r`, l.1170–1190, 1505–1515 | the minus row at `v` in the term `Φ⁽⁴⁾𝓡_v` (coefficient `p⁵`) | `E_row ≤ c/p` up to `√(S+1)` | `ρ_r = δ_row` | rewrite `𝓡_v = pΣx_j(x_j−z_j) − Σx_j²`, **DR1 at `v`** |
| U5 | D13, l.1943–1951 | `p³√(λ₁·d^{-1}ΣEz_i²)` | `≪ 1/p` | `δ_row` | `δ`: `p³√(λ₁δ) = O(c₀^{17/3}p^{-2})` ✓ |

The ledger line l.2013 (`δ_row = O(p^{-7/2})`) only records U2, U4 and U5. No other line of
Sections 1.2–1.5 uses `δ_row` or GR1. This was checked by grep and by reading the following:

- Q_* bound (l.1417): uses (C2), not GR1.
- D6: CR1 uses `δ` for the minus marks.
- B1, D9b, D10: use `E_row` only.
- FS1, BM1–BM4, JR2, RC1–RC5, S1, C6: no rows at all.

**Why individual rows are not enough.** Row gain enters the end game through two scales.

- The weak-loop score: `e = p√(row)/(√d h)`, with `pe² ∝ p³·row/(dh²)`.
- The CR3 first term: `p⁵√(λ_r·row)`.

With `row = δ` instead of `δ/p`, both are larger by a factor `p` (respectively `√p`). The method
then gives only the exponent `4/37` (AUDIT_B §3.2). So a `1/p` gain *in the score* is necessary,
and DR1 provides exactly that gain.

---

## 2. DR1: statement and line-by-line proof

### 2.1 Statement

**DR1 (score-difference energy).** The hypotheses are:

- `(CAP)`: the paired law exists on the whole capped source cube below `(y⁺,y⁻)`, and every
  normalized first mean is at most `r = 1+ε`;
- the regime `p ≥ 50`, `pε ≤ 1/8`, `p⁷ ≤ d`, `d ≥ 201`, with moments of order 6 available
  (`p ≥ 12`);
- (C2) with `δ = K_δ{ε + p⁴/d + (p/d)^{1/3}}`, `K_δ ≥ 1`.

Then for **every** vertex `v`, with `x_i = G⁺_vi` and `z_i = G⁻_vi`:

```
(2p−1)·a²Σ_{i∼v} E(x_i − z_i)²  =  B⁺_v + B⁻_v + 2a²T_v + E3_v          (exact)
B^±_v = 1 − Z^±_v E G^±_vv + a²Σ_{i∼v} E G^±_vv G^±_ii,    T_v = Σ_{i∼v} E x_i z_i,
E3_v  = −aΣ_i R⁺_i + aΣ_i R⁻_i,   R⁺_i = E[σ_vi x_i] − E[𝒟₁x_i],  R⁻_i = E[σ_vi z_i] − E[𝒟₁z_i],
```

and consequently

```
a²Σ_{i∼v} E(G⁺_vi − G⁻_vi)²  ≤  δ_Δ := K_DR·δ/p,        K_DR = 12.7 + K₃   (absolute).
```

`K₃` is the constant of `|E3_v| ≤ K₃p³/d` (§2.2, step 5).

### 2.2 Proof (every step re-derived; signs checked numerically, §5)

1. **Root-row equations (pointwise, exact).** Row `v` of `P^±G^± = I` gives
   `Z⁺_vG⁺_vv + aΣ_iσ_vi x_i = 1` and `Z⁻_vG⁻_vv − aΣ_iσ_vi z_i = 1`. Take expectations; note
   `Z_vEG_vv = D_v m_v`, where `D_v = y_vZ_v` and `m_v = Eh_v`.
2. **Derivatives.**
   - `∂_{σ_vi}P^± = ±a(e_ve_iᵀ + e_ie_vᵀ)`, so `∂x_i = −a(G⁺_vvG⁺_ii + x_i²)` and
     `∂z_i = +a(G⁻_vvG⁻_ii + z_i²)`.
   - `∂ log W = p·tr(G⁺∂P⁺) + p·tr(G⁻∂P⁻) = 2pa(x_i − z_i)`.
   - Hence, with `𝒟₁ψ = W^{-1}∂(Wψ)`:
     `𝒟₁x_i = −aG⁺_vvG⁺_ii + (2p−1)a x_i² − 2pa x_iz_i` and
     `𝒟₁z_i = +aG⁻_vvG⁻_ii − (2p−1)a z_i² + 2pa x_iz_i`.
3. **Branch identities.** Insert `E[σ_vi ψ] = E[𝒟₁ψ] + R_i` into step 1 and multiply by `±a`:
   ```
   (2p−1)a²S⁺_v − 2pa²T_v = B⁺_v − aΣR⁺_i,      (2p−1)a²S⁻_v − 2pa²T_v = B⁻_v + aΣR⁻_i.
   ```
   Add them, then add `2a²T_v` to both sides. Since `S⁺+S⁻−2T = ΣE(x−z)²`, this gives the exact
   identity. (Equivalent form: `2a²𝓡^± = N^± + E3^±`, with `𝓡^± = (p−1)S^± − pT` and
   `N^± = B^± − a²S^± = E_{ν_K}N_R^±/F_H`, the Schur identity (C3). Summing over `±`:
   `p·a²ΣE(x−z)² = a²(S⁺+S⁻) + (N⁺+N⁻+E3)/2`. GCI controls `T` only in each branch identity
   separately. The sum over branches does not need it.)
4. **`B^±` from above** (no lower bound is needed, since the left side is `≥ 0`):
   - `a²ΣEG_vvG_ii = a²y_vΣy_iE[h_vh_i] ≤ L_v·max_kEh_k²`;
   - (F2) with `k = 2`: `Eh² ≤ (1 + pε/(p−2))² ≤ 1 + 2.2ε`;
   - `m_v ≥ 1−ρ`, `D_v = 1 + L_v − C_v ≤ 2.01`, `L_v ≤ L̄ ≤ 1.01`, `C_v ≤ 1.03/d`.

   Hence `B^±_v ≤ C_v + D_vρ + 2.2L_vε ≤ 1.03/d + 2.01ρ + 2.3ε`.
5. **`E3`.** Only the **first-order** endpoint identity is needed:
   - `E_ξ[ξf] = E_ξf′ + R`, with `|R| ≤ (1/3)sup_{[−1,1]}|f‴|` (trapezoid rule). It is applied
     to `f(s) = W(s)ψ(s)` on each edge fibre. `f ∈ C³` because `p ≥ 5`, even across the support
     boundary, where `Wψ = det^{p−1}·adj`.
   - Regular-fibre control as in E1 (AUDIT_A §2.2, Case A/B with `M = (32pa)^{-1}`):
     `|R_i| ≤ C_{E1′}p³a³E g*⁴`, with `g* = max_±max(G^±_vv, G^±_ii)` and `C_{E1′}` absolute.
   - Summing `≤ d` edges with the outer `a`, over both branches, and using `a⁴d ≤ 1/(16d)·1.01`
     and the moment caps (`Eg*⁴ ≤ C`): `|E3_v| ≤ K₃p³/d`.
   - The full E1 (third order) is not needed here; the paper's `O(p³/d + p⁵/d²)` is the same
     bound.
6. **Cross term without a sign.** `|T_v| ≤ √(S⁺S⁻) ≤ (S⁺+S⁻)/2`, so
   `2a²T_v ≤ a²(S⁺_v+S⁻_v) ≤ 2δ` by (C2). This is the only place where `T_v` enters, and only its
   absolute value is used.
7. **Collect.**
   - `(2p−1)·LHS ≤ 2(1.03/d + 2.01ρ + 2.3ε) + 2δ + K₃p³/d`.
   - Use `ρ ≤ δ`, `ε ≤ δ/K_δ`, and `1/d ≤ p⁴/d ≤ δ/K_δ`.
   - Use `p³/d ≤ δ/(K_δp)`, which holds because `p⁴/d ≤ (p/d)^{1/3} ⟺ p^{11} ≤ d²`, implied by
     `p⁷ ≤ d`.
   - Then `(2p−1)·LHS ≤ (12.7 + K₃)δ`, i.e. `LHS ≤ K_DRδ/p` since `2p−1 ≥ p`.

**Dependencies.**

- E1′, the first-order endpoint lemma. W1 needs it already, and E1 contains it.
- (E3), only the derivative formulas.
- (F2), with `k = 2` and moments of order `≤ 6`.
- (C2).
- The parameter facts `C_v, D_v, L_v` (TB.par).

None of these uses GCI. Prékopa enters only through (C2): its (C1) step and the whitening step.

**Quantifiers.**

- `K_DR` depends only on `K_δ` (C2), `C_{E1′}` and the moment-cap constants. All are absolute:
  none depends on `c₀`, `κ₀`, `d`, `p`, the graph, its order or the sources.
- DR1 holds for every `(d, p)` in the abstract regime (AUDIT_D §1.3, `Regime K d p h`). In the
  application, its threshold is part of `d₀(c₀, κ₀)`.
- This is the order the end game needs: absolute `K`s, then `κ₀`, then `c₀`, then `d₀`.

**No circularity.**

- DR1 uses only (CAP) and its consequences (F2) and (C2). These hold at every point of the
  capped family, in particular at a first contact `y*`.
- At `y*`, DR1 holds at the contact vertex `v` and at all its neighbours `i`, which is what U2
  and U4 need.
- It does not use (F3), the contact estimate, D6 or anything downstream.

**Degenerate cases.**

- **Isolated `v`:** both sides are 0 (`D_v = 1`, `h_v ≡ 1`, `B = 0`).
- **Zero plus-source at `v`:** the physical row `x ≡ 0`, `B⁺ = 0`, `R⁺ = 0`. DR1 becomes
  `a²S⁻_v = (B⁻ + E3⁻)/(2p−1)`, a genuine minus-row gain, checked numerically.
- **Zero sources at neighbours:** they contribute 0.
- **One edge, extreme `p`:** checked numerically (`K2`, `p = 3…25`).

---

## 3. The restated lemmas (GCI-free route)

GR1 is **deleted**, together with `T_v ≤ Cp⁴` (an E4 transfer) and the whole GCI subtree of
`GCI_PLAN.md`. The following statements change. Notation as in the paper and AUDIT_B §1.
`ϑ = d^{-M}` is the interpolation floor.

**W1′ (Random-profile weak loop).** The hypotheses and the left-hand side are those of (W1).
The bound is

```
|E[H w_σᵀK_σ f] − E[H uᵀM_σ f]| ≤ 𝖲_f + K_W{p/(dh) + 1/(dh^{3/2})},
𝖲_f = (a/4) Σ_{i∈N} Σ_{j∼i} u_i E[ |F_ji| { 2pa H |G⁺_ij − G⁻_ij| + |∂_ij H| } ].
```

The changes from W1 are:

- **Score.** The exact determinant derivative `|G⁺_ij − G⁻_ij|` replaces `|G⁺_ij|+|G⁻_ij|`.
  W1's proof produces exactly this: l.779, `∂_ij log W = 2pa(G⁺_ij−G⁻_ij)`.
- **Remainder.** It is proved with `ρ_row := C(δ + 1/d)` from (C2). This needs
  `δ ≤ Kp^{-2} ⟸ p⁷ ≤ d`, and the coefficient stays `K(p³ρ + p²√ρ + p) ≤ Kp`.
- **Constants.** `K_W` is absolute; there is no dependence on GR1.

**FS5′ (score bounds).** At a contact, with (FS1), (BM4), (FS4), D6, (C2) and DR1 at every
`i ∈ N(v)`:

```
𝖲_u ≤ K e √(ζ − α + β_h(q₊−t₊) + θ) + K e h^{3/4},       𝖲_{b±} ≤ K e √(z_± + θ),
e := (p√δ_Δ + √(λ₁ + δ)) / (√d h)  ≤  K √(pδ) / (√d h).
```

- **Proof.** Cauchy–Schwarz over `(i, j, ω)`:
  `(a/4)Σu_iE[|F|·2paH|Δ_ij|] ≤ (pa²/2)(ΣE[HF_ji²])^{1/2}(Σu_i²E[HΔ_ij²])^{1/2}`. Then:
  - (FS1) gives `ΣE[HF²] ≤ Kh^{-2}{…} + Kh^{-1/2}`;
  - DR1 at `i` plus interpolation gives `Σ_{j∼i}E[HΔ_ij²] ≤ K(δ_Δ + ϑ)/a²`;
  - so `Σu_i²E[HΔ²] ≤ Kdδ_Δ`.
- **Root-weight part.** By (FS4), `Σu_i²E[|∂H|²/H] ≤ Ka²(S⁺_v+S⁻_v) ≤ K(λ₁+δ)`.
- **Consequences.** `e` is the paper's `e` up to an absolute factor, so (FS6), (FS7), (JR2) and
  (RC3) are unchanged verbatim.

**CR3′ (row-observable comparison, split marks).** Assume Cap and fix `v`. Take envelopes
`ϑ ≤ λ_r ≤ λ_c ≤ δ_c ≤ 1` and `ϑ ≤ ρ_Δ` such that:

- `S⁺/d ≤ λ_r`, `S⁻/d ≤ δ_c`, and `d^{-1}Σ_{j∈N}E(x_j−z_j)² ≤ ρ_Δ`;
- `d^{-2}E[(G⁺_vv)²‖G⁺[N,N]‖_F²] ≤ λ_c` and `d^{-2}E[(G⁻_vv)²‖G⁻[N,N]‖_F²] ≤ δ_c`.

Then

```
|𝓡 − E_{ν_K}𝖦F/(a²F_H)| ≤ C_CR{ p⁵√(λ_r ρ_Δ) + p⁴√(λ_c δ_c) + p¹³/d² } + e^{-3p}.
```

Proof (only the grade-1 term `Φ⁽⁴⁾𝓡_v` changes):

- The algebraic identity
  `𝓡_v = (p−1)Σx_j² − pΣx_jz_j = p Σ_j x_j(x_j − z_j) − Σ_j x_j²` holds.
- With `|Φ^{-1}∂_i⁴Φ| ≤ Cp⁴a⁴D^C`, summed over `i ∈ N` (`a⁴d ≤ 1.01/(16d)`), we get
  `|Σ_jx_j(x_j−z_j)| ≤ (Σx_j²)^{1/2}(Σ(x_j−z_j)²)^{1/2}`, plus Cauchy–Schwarz in `ω` and
  interpolation. Together these give `Cp⁵√(λ_rρ_Δ) + Cp⁴λ_r`.
- `p⁴λ_r ≤ p⁴√(λ_cδ_c)` follows from the ordering.
- The terms `Φ^{(4−k)}∂^k𝓡_v` with `k ≥ 1` have coefficient `≤ Cp⁴` and are bounded exactly as
  in CR3. Every plus mark is covered by `λ_c ≥ λ_r` and every minus mark (row or core) by `δ_c`.
- Grade 2 and higher, and the remainder, are unchanged.
- Hypotheses no longer needed: the old orderings `λ_r ≤ ρ_r`, `ρ_r ≤ δ_c`, and any individual
  minus-row gain.

**D9a′.** At the contact, apply CR3′ with:

- `λ_r = 4(S+1)/d` and `ρ_Δ = 4δ_Δ` (DR1 at `v`; `a²d ≥ 1/4`);
- `λ_c = C max(λ₁, λ_r) ≤ C′p/d`, using `S ≤ Cp` from D7;
- `δ_c = Cδ`, from (C2) and MARKENV.

Then

```
E_row = C₉{ Γ√(S+1) + Γ + p¹³/d² } + e^{-3p},      Γ = p⁴√(pδ/d) ≤ C c₀^{17/3} p^{-1},
```

since `p⁵√(λ_rρ_Δ) = 4√K_DR·Γ√(S+1)` and `p⁴√(λ_cδ_c) ≤ CΓ`. This is literally AUDIT_D's D9a.
D9b, D10, the absorption step `CΓ√(S+1) ≤ ¼(S−4) + C{Γ+Γ²+ε_s+η₀+d^{-1}}` and (D16) are all
unchanged.

**D13′.**

```
Q_*/a² ≤ 2L_d[(p−1)t_{+,0} + p t_{−,0}] + C p³(λ₁ + √(λ₁δ)),     p³√(λ₁δ) = O(c₀^{17/3}p^{-2}) = o(p^{-1}).
```

Same proof (the `x_i = 0` part is exactly `−6p(2p−1)P_iz_i² ≤ 0`), with the (C2) minus-row
envelope `d^{-1}ΣEz_i² ≤ 4δ` replacing `δ_row`.

**DR1** (new node; §2).

No other statement changes:

- (C1)–(C6), (S1), (W5), (WT1)–(WT5), CR1, (B1)–(B5), D1–D8 and D9b–D12 do not involve GR1;
- D14–D16 involve it only through `E_row`, `e` and D13, all treated above.

---

## 4. Exponent bookkeeping

`dr1_ledger.py` computes every monomial exactly as `c₀^A κ₀^K p^E`, using:

- `d = (p/c₀)^{17/2}` and `h = κ₀p^{-4}`;
- `δ ≍ (p/d)^{1/3}`, `λ₁ = p/d` and `λ_r = 5/d`;
- `δ_Δ = δ/p + p²/d`.

Output (verbatim exponents):

| term | GR1 route (paper) | no row gain | DR1 route |
|---|---|---|---|
| D9a, `p⁵√(λ_r·row)` | `c₀^{17/3} p^{-1}` | `c₀^{17/3} p^{-1/2}` ✗ | `c₀^{17/3} p^{-1}` + `c₀^{17/2} p^{-5/2}` + (`p⁴λ_r`) `c₀^{17/2} p^{-7/2}` |
| D9a, `p⁴√(λ₁δ)` (core marks) | `c₀^{17/3} p^{-1}` | same | same |
| `pe²` (FS5 → RC3) | `c₀^{34/3} κ₀^{-2} p^{-1}` | `c₀^{34/3} κ₀^{-2} p^{0}` ✗ | `c₀^{34/3} κ₀^{-2} p^{-1}` + `c₀^{17} κ₀^{-2} p^{-4}`; root part `c₀^{34/3}κ₀^{-2}p^{-2}` |
| `pe h^{3/4}`, `pe(dh)^{-1/2}` | `p^{-3}`, `p^{-9/4}` | — | unchanged |
| D13 | `c₀^{17/3} p^{-5/2}` | `c₀^{17/3} p^{-2}` | `c₀^{17/3} p^{-2}` + `c₀^{17/2} p^{-9/2}` |
| W1 coefficient `p³ρ + p²√ρ` (needs `≤ Kp`) | — | `p^{1/2}`, `p^{3/4}` ✓ | same (ρ = δ) |
| DR1 internal `(p²/d)/(δ/p)` | — | — | `c₀^{17/3} p^{-3} ≤ 1` |

So the DR1 route keeps every critical term at the scale `p^{-1}`, with the same coefficients up to
absolute factors:

```
total error ≤ [C₁√κ₀ + C₂c₀^{17/3} + C₃κ₀^{-2}c₀^{34/3}] p^{-1} + C_rest κ₀^{-3/2} p^{-3/2},
```

where `C₂` now carries `√K_DR` (instead of `√C_row`) and `C₃` carries `K_DR` (instead of
`C_row`). Both are absolute. The answer to "does `δ/p + p²/d` beat `1/p` by a factor that `c₀`
makes small?" is yes:

- `δ/p` gives exactly the paper's critical coefficients `c₀^{17/3}` (D9a) and
  `κ₀^{-2}c₀^{34/3}` (`pe²`);
- `p²/d` gives `o(1/p)` in both places.

Choose `κ₀` with `C₁√κ₀ ≤ 1/24`, then `c₀` with `C₂c₀^{17/3} + C₃κ₀^{-2}c₀^{34/3} ≤ 1/12`, then
`d₀(c₀, κ₀)`. This is AUDIT_D §0, unchanged.

**Why the rate stays `2/17`.** `Γ = p⁴√(pδ/d) ≍ p^{14/3}d^{-2/3}` with `δ ≍ (p/d)^{1/3}`, and
`pe² = κ₀^{-2}pΓ²` exactly. Both are `≍ 1/p` iff `p^{17} ≍ d²`. DR1 reproduces the `1/p` factor
of GR1 in the score: `δ_Δ = Θ(δ/p)`, against the paper's `δ_row = Θ(δ/p)`. The exponent is
therefore identical.

---

## 5. Numerical checks

`scripts/tight/dr1_enum.py` enumerates the paired law exactly:

- all `2^{|E|}` signings;
- weight `1{P⁺≻0, P⁻≻0}(det P⁺ det P⁻)^p`;
- `P^± = diag Z^± ± aA_σ`, with `Z^±` from random sources by the paper's map
  `c(1+c) = a²y_iy_j`, `Z_i = (1+Σc_ij)/y_i`, and `a = (4(d−1)+4/p)^{-1/2}`.

Graphs: `K2`, `K4`, `K_{3,3}`, `K5`, the cube `Q3`, Petersen, and a non-regular graph `star+`.
Values `p ∈ {3, 6, 12, 25}`. Root `v = 0`, all neighbours.

1. **Exact DR1 identity.** `(2p−1)a²ΣE(x−z)² = B⁺+B⁻+2a²T+E3`, with `E3` built from the exact
   first-order residuals. The worst relative residual over 28 cases is `1.2·10⁻¹⁴`. The pointwise
   root-row equations hold to `10⁻¹⁴`. The sign-free bound
   `ΣE(x−z)²a² ≤ (B⁺+B⁻+a²(S⁺+S⁻)+|E3|)/(2p−1)` holds in every case. (In these tiny graphs
   `pa ≈ 1–10`, so `E3` dominates; the identity is what is tested, not the asymptotics.)
2. **Zero plus-source at `v`** (`Z⁺_v = 10¹²`). We get `a²S⁺ = 4·10⁻²⁶` and
   `diff = a²S⁻ = (B⁻+E3)/(2p−1) = 1.106·10⁻²`, exactly as predicted.
3. **Pointwise derivative formulas.** `𝒟₁x_i`, `𝒟₁z_i` and the score `2pa(G⁺_vi−G⁻_vi)` were
   compared with `d/dt(Wψ)/W` from the exact rank-two fibre formulas:
   - `det P(t) = det P·[(1+taG_vi)² − t²a²G_vvG_ii]`;
   - `G(t)_vi` by Woodbury, evaluated in 40-digit mpmath.

   The maximum discrepancy is `2·10⁻¹⁶` (K4, K33, K5).
4. **Size of `E3`.** In a perturbative regime (`Z ∈ [1, 1.3]`, `a ∈ {0.04, 0.02}`,
   `p ∈ {3, 6}`), `E3` agrees with the third-order endpoint term
   `(a/3)ΣE𝒟₃x − (a/3)ΣE𝒟₃z`. The relative remainder is `1.9·10⁻² → 4.7·10⁻³` when `a` is
   halved, i.e. it drops by a factor 4, consistent with `O(a⁶)` against `O(a⁴)`. Also
   `|E3|/(p³a⁴·deg)` stays between 0.1 and 0.5, consistent with `|E3| ≤ K₃p³a⁴d`.
5. **Observation.** In every enumerated case `a²T < 0`. This is consistent with GCI's direction
   (`T ≲ 0`), but DR1 never uses it.

`scripts/tight/dr1_ledger.py` checks the exponents of §4, including both "no row gain" failures,
which reproduce AUDIT_C G8 (`p^{-1/2}`) and AUDIT_D G8 (`pe² = Θ(1)`).

---

## 6. Resolution of the audit disagreement, and new gaps

- **AUDIT_C G8 / §9** says "D9a delivers `E_row = O(c₀^{17/3}/p)` only with GR1". This is
  **true for CR3 as written**, where the `p⁵`-coefficient term has `pΣx_jz_j` bounded by
  `√(λ_rρ_r)` with the *individual* minus row. It is **superseded** by CR3′: after the identity
  `𝓡_v = pΣx_j(x_j−z_j) − Σx_j²`, the `p⁵` coefficient multiplies only the difference, and DR1
  bounds that at `δ/p`. The `p⁴` terms already use `δ_c = Cδ` (no gain) in the paper itself.
- **AUDIT_D G8 / X1 / §4.2** says "W1's remainder needs GR1" and "without GR1, `pe² = Θ(1)`".
  - The first claim is **incorrect**: U1 needs only `ρ_row ≤ Kp^{-2}`, and `δ ≤ 3K_δc₀^{17/6}p^{-5/2}`.
  - The second is **true only for the individual-row score** `|G⁺_ij|+|G⁻_ij|`. With the exact
    score of W1′ and DR1, `pe² = Θ(κ₀^{-2}c₀^{34/3}/p)`, as in the paper.
  - Where AUDIT_D §4.2 attributes `C₂, C₃` to "GR1's `C_r`", read `K_DR`.
- **AUDIT_B §3.3** is correct as written. Clarifications made here, none of them a correction of
  substance:
  - CR3′ needs its full hypothesis list (§3): the minus row and minus core marks are covered by
    `δ_c` from (C2);
  - DR1 needs only the first-order endpoint identity E1′, not E1;
  - `δ_Δ ≤ K_DRδ/p` with `K_DR = 12.7 + K₃`;
  - D13′ may carry `p³λ₁` in addition (harmless, since `λ₁ ≤ δ`).

**A tempting alternative that fails.** Without the rewrite, one could try to exploit that the
leading terms of `Φ^{-1}∂_i⁴Φ` carry `(x_i−z_i)⁴` and `(x_i−z_i)²`. The `p³(x_i−z_i)²·𝓡_v` term
is then a product of **two** quadratic row energies. Bounding it needs fourth moments of row
energies, which are not available (only first moments with a polynomial floor). The rewrite in
CR3′ is the right fix: it leaves a product of two square roots, which Cauchy–Schwarz splits into
two first moments.

**New gaps: none.** DR1 is strictly easier than GR1:

- it is the same row equations, without the E4 transfer of `T_v` and without GCI;
- its only nontrivial dependencies (E1′, F2, C2) are needed elsewhere anyway.

**DAG consequences for the coordinator.**

1. Delete GR1, the `T_v ≤ Cp⁴` transfer and the whole GCI subtree (`GCI_PLAN.md`, files
   `BiluLinial/Tight/Gauss/GCI*.lean`). No other node depends on them.
2. Add `TB.RE` (the two branch identities with exact residual `E3`, `|E3| ≤ K₃p³/d`) and
   `TB.DR1`.
3. Restate W1, FS5, CR3, D9a and D13 as in §3.
4. Parent checks to run before dispatch:
   - (i) DR1 from TB.RE + (C2) + (F2);
   - (ii) FS5′ from W1′ + DR1 + FS1 + FS4 + BM4;
   - (iii) D9a′ from CR3′ + D6 + D7 + DR1 + MARKENV;
   - (iv) D13′ from KI-ID + (C2) + D6.

   Small cases: empty `N(v)`, zero sources and one edge are covered by §2.2 and §5.
