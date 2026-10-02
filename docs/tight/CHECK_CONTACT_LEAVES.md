# CHECK_CONTACT_LEAVES: rule-2 checks of `Contact/Leaves.lean`, `RouteGCI.lean`, `RouteD9a.lean`

This file records workflow rule 2, checks (1) proof sketch and (3) small cases, plus the parent
check *by reading* of how `Contact/Chain1.lean`, `Chain2.lean` and `Contact.lean` use each leaf.
The chain was not built, because `SourceMax/Phys.lean` was mid-edit. Companion reports:
`CHECK_CONTACT.md` (Real.lean, Inputs.lean) and `CHECK_SECS.md` (section exports; its §6 interface
table is used for the "export" column below).

**Files read (UTC, 2026-10-01).**

- `Leaves.lean`, `Inputs.lean` and `Defs.lean`: read at 05:45, unchanged at 07:25 (mtimes 05:23,
  05:19, 05:24).
- `Real.lean`: re-read at 07:23 (mtime 07:20). `d10_real` now has `(hCB : 0 ≤ CB)`.
- `Chain1.lean`, `Chain2.lean`, `RouteGCI.lean`, `RouteD9a.lean`: re-read at 07:23 (mtimes 07:21).
  - `Chain1` imports `RouteDR1`; `Chain2` imports `RouteDR1D9a` and passes `hCB.le` to `d10_real`.
  - The GCI files changed only by renaming `cr1` → `cr1_gci` and `d9a` → `d9a_gci` (inactive).
- **New** `RouteDR1.lean` and `RouteDR1D9a.lean`: read at 07:23 (mtimes 07:21).
- `Contact.lean`: diff checked at 07:21. `CHECK_SECS.md`: read at 07:21.

**Scripts** (run with `/tmp/tight-venv/bin/python`):

- `scripts/tight/check_leaves_enum.py` enumerates the paired law exactly with the Lean definitions:
  - graphs `K₄`, `K₃,₃`, `Q₃` and a non-regular star+ (`d` = max degree);
  - `p ∈ {3, 6, 12}` and `h ∈ {0.05, 0.3, 1}`;
  - 30 cases with random sources including zeros, plus 30 with sources in `[0.2s, s]`.
- `scripts/tight/check_leaves_sym.py` checks the structure of `Kpoly` symbolically (sympy) and runs
  2·10⁴ random or adversarial `bm1_det` instances.

## Verdicts

| leaf | verdict | kind |
|---|---|---|
| `root_equation` | OK; adding `hR` would make it a corollary of the proved `root_row_mean` | exact, pure |
| `d15_cs` | OK | exact, pure |
| `source_facts` | OK | exact/deterministic, pure + `walk_facts` |
| `qstar_bound` | OK | export (C2, F2, UMI) |
| `d8_profile` | OK as a statement; **NEEDS FIX (placement)**: needs `d7` | chain (D7) |
| `d10_corr` | OK | export (C5c, S1w, UMI) |
| `energy_psd` | OK | pure linear algebra (Mathlib `PosSemidef.hadamard`) |
| `fs5_scores` | OK as a statement; **NEEDS FIX (placement)**: needs `fs1` (D8 ⇒ D7) and a route input | chain + route |
| `rc1_tbounds` | OK | export (F2, Hölder) |
| `rc2_profile` | OK as a statement; **NEEDS FIX (placement)**: needs D7, D8 | chain (D7, D8) |
| `rc4_centres` | OK | export (S1w) |
| `d13_centering` | OK as a statement; **NEEDS FIX (placement)**: needs D6 or D7 | chain (D6/D7) |
| `bm1_det` | OK (constant 16; worst observed ratio 0.25) | pure linear algebra |
| `bm4_mask` | OK | export (BM1, D_* moments, UMI) |
| `fs1_fixed_mask` | OK as a statement; **NEEDS FIX (placement)**: needs D8 ⇒ D7; uses FS2, which is not a node | chain (D8) |
| `in_GR1` (RouteGCI, inactive) | OK on the GCI route; unused on the DR1 route | route GCI |
| `in_CR3` (RouteGCI, inactive) | OK; actually route-independent (follows from `SecC.row_comparison_split`) | export |
| `cr1_real`, `cr1_gci` (RouteGCI, inactive) | OK | pure real / corollary |
| `d9a_real`, `d9a_gci` (RouteD9a, inactive) | OK (GCI route) | pure real / corollary |
| `in_C2_all` (RouteDR1) | OK | export `SecA.concentration_C2` |
| `in_DR1_of_C2` (RouteDR1) | OK (see §6 for the proof route) | export `SecB.row_eq` + `SecB.dr1_pt` |
| `in_DR1` (RouteDR1) | OK (proved from the two above) | corollary |
| `in_CR3'` (RouteDR1) | OK | export `SecC.row_comparison_diff` |
| `cr1_real_dr1` (RouteDR1) | OK | pure real |
| `cr1` (RouteDR1) | OK (parent check passes) | corollary |
| `d9a_real_dr1` (RouteDR1D9a) | OK | pure real |
| `d9a` (RouteDR1D9a) | OK (parent check passes) | corollary |

Nothing in these files is FALSE. **One required fix remains:**

- **(F1)** File placement of the five chain-dependent leaves (§1).

(F2), the `d10_real` fix and its `Chain2` edit, was applied at 07:20 (§2).

## 1. (F1) Five leaves cannot be proved where they are stated

`Leaves.lean` is imported by `Chain1.lean`, and `Chain1.lean` proves `d6` and `d7`. A declaration's
proof must live in its own file, so a leaf in `Leaves.lean` can never use `d6`, `d7`, or a route
input from `RouteGCI.lean` (also imported by `Chain1`). Five leaves need them:

| leaf | needs | why (source) |
|---|---|---|
| `d8_profile` | `d7` (`L̄ − L ≤ Cε_s`) | (D8) is the source identity applied to (D7) (l.1493–1500) |
| `fs1_fixed_mask` | `d8_profile` (`Ω₊ ≥ c`, so `H ≤ D_*^C Ω₊` for `H ∈ {1, Ω₋}`) | l.1669–1671 "source saturation gives `Ω₊ ≥ c`" |
| `rc2_profile` | `d7` (`Σℓδ ≤ Cpa²` ⇒ `Σ_N y_iδ_i ≤ Cp`), `d8_profile` | l.1810–1818 |
| `d13_centering` | `d6` or `d7` (`S/d ≤ Cp/d`) | with only (C2), `S/d ≤ 4C₂δ̄`, and the error would be `p³δ̄ ≍ p^{1/2}`, not `o(1/p)` |
| `fs5_scores` | `fs1_fixed_mask`, plus `in_DR1` (`RouteDR1.lean`) at every `i ∈ N(v)` | l.1752–1756, FS5′ |

There is no mathematical cycle: `d7`'s proof uses only `in_C2`, `cr1`, `in_C1`, `in_whiten`,
`in_C3a`, `qstar_bound`, `source_facts`, `root_equation`, `in_E1`, `param_facts` and
`source_covariance`.

Since 07:21 the route input `in_DR1` lives in `RouteDR1.lean`, which imports only `Inputs`, `Real`
and `SourceMax.Law`. So `Leaves.lean` *could* import it without a cycle, and `fs5_scores`'s route
dependence alone would not force a move. Its dependence on D7 through `fs1_fixed_mask` still does.

None of the five is used by `Chain1`. `fs5_scores` (in `weak_res`), `rc2_profile` (in `rc3`) and
`d13_centering` (in `contact_final`) are used only in `Chain2`. `d8_profile` and `fs1_fixed_mask`
are used only inside other leaves.

**Proposal (no statement changes).** Create `Contact/Leaves2.lean`:

- it imports `Contact/Chain1.lean`, which already imports `Contact/RouteDR1.lean`;
- move `d8_profile`, `fs1_fixed_mask`, `rc2_profile`, `d13_centering` and `fs5_scores` into it,
  verbatim;
- `Chain2.lean` imports it (`Chain2` already imports `RouteDR1D9a`, which imports `Chain1`, so there
  is no cycle).

`bm1_det` and `bm4_mask` stay in `Leaves.lean`: they have no chain dependence. Their proofs may
import the section files freely: `CHECK_SECS`/`rg` show that no `SecA/SecB/SecC/SourceMax/Tools`
file imports `Contact.{Inputs,Leaves,Chain*,Route*}`.

(The alternative of restating the five with the D6/D7 conclusions as hypotheses would require
`∀ C₇, ∃ C, …` forms and more chain plumbing; the move is simpler.)

## 2. (F2) `d10_real` and `Chain2.d10` — resolved

- `d10_real` now takes `(hCB : 0 ≤ CB)`; with it the statement is true (CHECK_CONTACT.md §R6).
- `Chain2.d10` now does `obtain ⟨CB, hCB, hB1⟩ := in_B1.{u}` and calls
  `d10_real CB C₉ C₉b Cc hCB.le`, which is correct.
- `d9b_real` holds for every sign of `CB`, so `d9b` (still discarding the positivity) is fine.

## 3. Parent check by reading (Chain1, Chain2, Contact.lean)

Each call site was matched against the leaf's exact statement and conjunct order:

- **`source_facts`** has 13 conjuncts: card, ℓ≥0, L≤L̄, 0≤C₊, C₊≤J, C₊≤a²L̄s², D₊=…, 0≤Σℓδ, 0≤S,
  0≤S₋, 0≤trA², 0≤trB², 0≤w.
  - Every destructuring pattern selects the intended conjunct:
    - `d3`: `.2.2.2.2.2.2.1`, the D₊ identity;
    - `d4` and `contact_final`: `⟨-, -, hL, hC0, hCJ, hCa, -, hsED, hS, -⟩`;
    - `d6`: 13-tuple, using `hS, hA2, hw`;
    - `d7`: 13-tuple, using `hsED, hS, hA2`;
    - `d9b`: `.2.2.2.2.2.2.2.2.1`, i.e. 0 ≤ S;
    - `d15`: `⟨hcard, -, -, hC0, -, hCa, hDp, -, hS, -⟩`;
    - `RouteDR1D9a.d9a` (and the inactive `RouteD9a.d9a_gci`): 13-tuple.
  - The arguments then fed to `d4_real` (`hS hC0 hCJ hsED hL hCa`), `d15_real` and
    `final_assembly_real` (`hS hsED hL hC0 hCJ hCa`) match their hypothesis order (CHECK_CONTACT §R2,
    §R12, §R13).
- **`energy_psd`** (12 conjuncts): `qP_le` uses `.2.2.2.2.2.2.2.1` (`0 ≤ q₋`), and `rc3`
  destructures all 12. The values fed to `fs7_real` and `jr_real` are in the required order.
- **`root_equation`** and **`d15_cs`**: `loop` rewrites with `mp_root`; `d15` turns the root
  equation plus CS into `(rD₊−1)² ≤ a²|N|S`. Correct.
- **`qstar_bound`** feeds `d4_real`'s `|Q| ≤ CQ a²(p + p³δ̄)`. **`d10_corr`** feeds `d10_real`/`qP_le_real`
  with `Qf ≤ Qb + Cc·p/(d·h·√h)` (same expression). **`rc1_tbounds`**, **`rc2_profile`** and
  **`rc4_centres`** feed `jr_real`/`d12_real` with the right conjuncts (`(H4 ct).1.2`, `.2.2` are the
  upper bounds). **`fs5_scores`** matches the score expressions of `in_W1` term for term
  (`weak_res`). **`d13_centering`** is literally the D13 hypothesis of `final_assembly_real` with
  `Tc = (p−1)t_{+,0} + p·t_{−,0}`.
- **`Contact.lean`** (uncommitted diff): `exists_contact_free` follows from `contact_final` and
  `ledger_choice` as in CHECK_CONTACT §R15. Correct.
- **`f3_summed`** calls `source_covariance ct.G hR ct.ctx hi`, which matches `SourceMax.lean:170`.

Apart from (F1), every leaf is used with hypotheses the chain can discharge. (F2) is already
applied.

---

## 4. Leaves

The quantifier level is correct throughout. Every analytic leaf is `∃ C > 0, Eventually …`: an
absolute `C` first, then `c₀, κ₀`, then `D(c₀, κ₀)`. `bm4_mask m` has `C(m)` with `m` fixed by the
chain. All statements are uniform in the graph and its order (local quantities; moments of order
`≤ p/2`). "UMI" means `Tools/Interp.wavg_mul_le_umi`:
`E[YZ] ≤ B(M/θ)^{1/(k−1)}(EY + θ)` for `EY^k ≤ M^k`, `EZ^k ≤ B^k`. Its loss is absolute once
`k ≥ 10 log d + 1` (RegA: `p ≥ 120 log d`) and `M` is polynomial in `d, h⁻¹`. That needs a threshold
depending on `κ₀`, which `Eventually` allows.

### L1. `root_equation` — OK
- **Source:** l.1394–1397 and l.1977–1978. **Audit:** AUDIT-D §3.1 D3.
- **Kind:** exact, pure.
- **Sketch.** Row `v` of `P̃P̃⁻¹ = I` on the support is `SecB.root_row_identity` (proved), averaged
  over the law. This is literally `(SecB.root_row_mean ct.G hR ct.ctx.toCapPt ct.ctx.mem).1`
  (proved), with `Dplus = diagD`, `mp v = meanPlus`, `sx i = E[sgn·greenP]` all definitional.
- **Note.** The statement has no `hR`, and `root_row_mean` needs `TRegime` (only for `Zw ≠ 0`).
  `Zw > 0` does hold at every contact without the regime:
  - if `s ≥ 0`, the contact point is in `[0, s]^V` and `CapCtx.pos` applies;
  - if `s < 0`, `InCube(λs)` forces `λ = 0` and `y = 0`, where `P̃ = I` and `Zw = #configs`.

  Simplest: **add `(hR : TRegime d p)`**. Both call sites (`loop`, `d15`) already have it.
- **Small cases** (enumeration): residual `≤ 2·10⁻¹⁴` in all 60 cases, including zero sources.

### L2. `d15_cs` — OK
- **Source:** l.1977–1982.
- **Kind:** pure.
- **Sketch.**
  - `(Σ_N E[ξ_ix_i])² ≤ |N|·Σ_N (E[ξ_ix_i])²` (`sq_sum_le_card_mul_sum_sq`);
  - then `(E[ξx])² ≤ E[ξ²x²] = E[x²]`, using `lawE_eq_wavg` with `wavg_mul_sq_le` (Tools/Interp) and
    `sgn² = 1` (units of ℤ).
  - If `Zw = 0` both sides are `0`. No hypotheses are needed.
- **Small cases:** slack `≥ 0`; `0.061` with positive sources.

### L3. `source_facts` — OK
- **Source:** l.1352–1368. **Audit:** AUDIT-D §3.1 "deterministic source facts".
- **Kind:** pure + `walk_facts`.
- **Sketch.** `yp ∈ [0, s]^V` follows from the contact cube via `InCube.of_mul_le_one`.
  - `|N| ≤ d`: `card_nbhd_le` (SecB).
  - `ℓ ≥ 0`, and `L ≤ L̄` (`y ≤ s`, `|N| ≤ d`).
  - `C₊ ≤ J`: `ℓ_iτ_vi = c_vi²`, because `c(1+c) = ℓ` (`cRoot_add_sq`) and `τ = c/(1+c)`; then
    `walk_facts` (Walk.lean, proved) gives `τ_vi ≤ K_vi` for `v, i ∈ S` adjacent.
  - `C₊ ≤ a²L̄s²`: `c ≤ ℓ ≤ a²s²` (`cRoot_le`), summed over at most `d` terms.
  - `D₊ = 1 + L − C₊`: `diagD_eq_one_add_L_sub_C` (SecA/ParP).
  - `Σℓδ ≥ 0`: the cap at `N ⊆ S`.
  - `S, S₋ ≥ 0`: `lawE_nonneg`.
  - `trA², trB² ≥ 0`: `A` is symmetric for every `σ`, since the inverse of a symmetric matrix is
    symmetric (`Matrix.transpose_nonsing_inv`).
  - `w ≥ 0`: on the support `A ⪰ 0` (`SecA.rootMat_posSemidef`), so `1 + trA ≥ 1`.
- **Small cases.** `J − C₊ ≥ −7·10⁻¹⁸`, i.e. equality up to rounding at zero sources; `≥ 1.4·10⁻³`
  with positive sources. The `D₊` identity holds to `4·10⁻¹⁶`.

### L4. `qstar_bound` — OK
- **Source:** l.1414–1422. **Audit:** AUDIT-D §3.1, AUDIT-C §6 QSTAR.
- **Kind:** export (`in_C2` ← `SecA.in_C2`; F2 `source_moments`; `SecB.dstar_moment`; UMI).
- **Sketch.** The structure is checked by sympy (`check_leaves_sym.py`):
  - the row-free part is `6[(p−1)P²+pPQ]`;
  - every other monomial has row degree `≥ 2`, with `p`-degree `≤ 2` at row degree 2 and `≤ 3` at
    row degree 4;
  - the coefficient mass is `C_K = 462`.
- **Row-free part.** `2a⁴·|N|·2p·max E[P²+PQ] ≤ 144·a⁴dp ≤ 40a²p`, using `s ≤ 2`, `Eh⁴ ≤ 1.1`
  (F2 with `k = 4`) and `a²d ≤ 1/2`.
- **Rest.** `|x|, |z| ≤ D_*` and `P, Q ≤ D_*²` give `|mono| ≤ (x²+z²)D_*²`. UMI gives
  `E[(x_i²+z_i²)D_*²] ≤ C_U(E(x_i²+z_i²) + ϑ)`. Then
  `(a⁴/3)·462p³·C_U(S + S₋ + dϑ) ≤ 154C_U·a²p³(2C₂+1)δ̄`, using `in_C2` and `ϑ ≤ δ̄`.
- **Witness:** `C = 40 + 154·C_U·(2C₂+1)`, absolute.

### L5. `d8_profile` — statement OK; NEEDS FIX (placement, §1)
- **Source:** l.1493–1500. **Audit:** AUDIT-D §3.1 D8.
- **Kind:** chain (D7) plus deterministic algebra.
- **Sketch.** Start from `L̄ − L = a²[(s−y_v)Σ_N y_i + s(s(d−|N|) + Σ_N(s−y_i))]`, a sum of
  nonnegative terms, and `d7`: `L̄ − L ≤ C₇ε_s`.
  - `a² ≥ 1/(4d)` and `s ≥ 1.9` give `||N|/d − 1| ≤ 1.2C₇ε_s` and
    `d⁻¹Σ|y_i − s| ≤ 1.2C₇ε_s`.
  - Then `Σ_N y_i ≥ d` gives `s − y_v ≤ 4.1C₇ε_s`.
  - `|s − 2| ≤ 2η₀ + 4/q`, since `s − 2 = (2τ_* − η₀)/(1 − τ_*)`.
- **Witness:** `C = 10C₇ + 10`.
- **Degenerate case.** `N = ∅` would give `L̄ − L = L̄ ≥ 1/2`, contradicting D7 for large `d`. This
  is consistent with the fact that an isolated root has `Eh_v = 1 < r`.

### L6. `d10_corr` — OK
- **Source:** l.1532–1545. **Audit:** AUDIT-C §6 (D10), AUDIT-D §3.1 D9b.
- **Kind:** export: `SecA.sum_shift_sub_core_le` (C5c; numerically checked in CHECK_SECS §2), and
  `SecB.mean_shift_weighted_of_cl1` (S1w, given `CL1Shape` ← `SecA.scalar_ineq`).
- **Sketch.**
  - Exact identity: `L_d(p−1)q₊ = a²(p−1)E[G_vv² Σ_{N×N}X_ij²]` (`16d·a²·(1/4)·(1/(4d)) = a²`).
    Checked to `7·10⁻¹³`.
  - `Δ = X[N,N] − Y ⪰ 0` (Schur), and `trX² − trY² = 2tr(YΔ) + trΔ² ≤ 3h⁻¹trΔ`. Mixed:
    `tr(X⁺X⁻) − tr(Y⁺Y⁻) ≤ h⁻¹(2trΔ⁺ + trΔ⁻)`.
  - C5c: `trΔ ≤ D_v(h_v − hz_v)/h`.
  - S1w with weights `Z = h_v²`, `h_v⁺h_v⁻` (F2 moments): `E[(h_v − hz_v)Z] ≤ 3(K_S+2)B√h`.
  - Total `≤ C·a²p·h^{−3/2} ≤ C·p/(dh^{3/2})`.
- **Witness:** `C = 3·2.01·s⁴·(p/(p−1))·3(K_S+2)B·3 ≤ 400(K_S+2)B`. It is absolute; `K_S` and `B`
  come from SecB/F2.
- **Small cases:** `Q_full − Q ≥ 0` in all cases (`≥ 9.4·10⁻³` with positive sources).

### L7. `energy_psd` — OK
- **Source:** l.1586–1594. **Audit:** AUDIT-D §3.2 (E-a)–(E-b).
- **Kind:** pure linear algebra.
- **Sketch.** On the support, `X± = Y^{1/2}(P̃± + hY)⁻¹Y^{1/2} ⪰ 0`.
  - `K₊ = X₊∘X₊/4` and `K₋ = X₊∘X₋/4` are PSD by **`Matrix.PosSemidef.hadamard`**
    (Mathlib `Analysis/Matrix/Order.lean:221`; contrary to AUDIT-D, it *is* in Mathlib).
  - `Ω₊ ≥ 0`, and `Ω₋ ≥ 0` (diagonals of PSD matrices).
  - `u ≥ 0`, and `b± ≥ 0` entrywise (`adjS ≥ 0`, `M± ≥ 0`).
  - Gram CS for `(f, g) ↦ E[Ω fᵀKg]`: pointwise `(fᵀKg)² ≤ (fᵀKf)(gᵀKg)`, then weighted CS
    (`wavg_mul_sq_le`).
  - `q₊ − t₊ = E[Ω₊uᵀ(K₊−M₊)u]` and `ζ − α = E[Ω₊uᵀ(K₊−M₊)b₊]`: `K₊ − M₊` is the zero-diagonal part
    of `K₊`, with entries `≥ 0`.
  - `α, β, t± ≥ 0` entrywise.
  - Uses `hh : 0 < h`; `hR` is only for `y ≥ 0`.
- **Small cases:** all 12 conjuncts hold in 60 cases, with strictly positive margins for positive
  sources. `α = β = 0` on `K₃,₃` is genuine: `N(v)` has no internal edges, so `uᵀMb = 0`.

### L8. `fs5_scores` — statement OK; NEEDS FIX (placement, §1)
- **Source:** (FS4)–(FS5), l.1739–1763. **Audit:** AUDIT-D §3.4; DR1_CHECK §3 FS5′.
- **Kind:** chain plus route: `fs1_fixed_mask`, `bm4_mask`, **`in_DR1` at every `i ∈ N(v)`**,
  `in_C2`, UMI.
- **Sketch** (DR1 route). Joint Cauchy–Schwarz over `(i, j, σ)`.
  - **Determinant part:**
    `2pa²(ΣE[HF²])^{1/2}(Σ_i u_i²Σ_{j∼i}E[HΔ_ij²])^{1/2}`, with `Δ_ij = G⁺_ij − G⁻_ij`.
    - DR1 at `i` with weight `H ≤ D_*^C` (UMI) gives `Σ_{j∼i}E[HΔ²] ≤ C(K_DRδ̄/p + ϑ)/a²`.
    - `Σ_i u_i²(…) ≤ C'δ̄/(pa²)`, so the part is `≤ C√(pδ̄)/√d·√(ΣE[HF²])`.
    - FS1 gives `√(ΣE[HF²]) ≤ Ch⁻¹√(ζ−α+β_h(q₊−t₊)+θ) + Ch^{−1/4}`.
    - Hence `≤ C·eP·√(…) + C·eP·h^{3/4}`.
  - **Root-weight part (FS4, pointwise, no inverse source).**
    - `|∂Ω₊| ≤ √Ω₊·2a|G⁺_vi||G⁺_vj|`, and `|G⁺_vj|² ≤ G⁺_vvG⁺_jj`.
    - `|∂Ω₋|²/Ω₋ ≤ a²(G⁺_vv G⁻_vi² G⁻_jj + G⁻_vv G⁺_vi² G⁺_jj)`.
    - So `Σ_i u_i²Σ_j(…) ≤ C(a²S + a²S₋ + ϑ) ≤ C(2C₂+1)δ̄` by `in_C2`. D6 is not needed.
  - **b-scores:** BM4 with `m = 0` gives `ΣE[ΩF(b)²] ≤ Ch⁻²(z± + θ)`.
- **New node suggested:** FS4 (`|∂_{ij}Ω±| ≤ √Ω±·g_ij` with
  `g_ij² ≤ Ca²D_*²(G⁺_vi² + G⁻_vi²)`), pointwise and pure.

### L9. `rc1_tbounds` — OK
- **Source:** (RC1), l.1819–1824. **Audit:** AUDIT-D §3.5.
- **Kind:** export (F2 `source_moments` with `k = 4`; Hölder `SecA.wavg_prod_pow_le`).
- **Sketch.**
  - `t₊ ≤ (|N|/d)(1/16)max_i E[G_vv²G_ii²] ≤ (s/2)⁴ max E[h_v²h_i²]`, using `X_ii ≤ G_ii`,
    `|N| ≤ d` and `G = yh`.
  - That is `≤ (s/2)⁴((pr−4)/(p−4))⁴ ≤ (1+1.01ε)⁴`, using `s ≤ 2` (`SecA.sOf_le_two`, sorry,
    true: `qη₀ ≥ 2(1−η₀)`).
  - `t₋ ≤ (s/2)⁴E[h⁺_vh⁻_vh⁺_ih⁻_i]`, bounded by the same with four-fold Hölder.
- **Witness:** `C = 5`.

### L10. `rc2_profile` — statement OK; NEEDS FIX (placement, §1)
- **Source:** l.1800–1842. **Audit:** AUDIT-D §3.5 PROF, RC2.
- **Kind:** chain (D7, D8) plus F2 (`k = 2`), S1w and UMI.
- **Sketch.**
  - The `y_i`-weighted CS gives `d⁻¹Σ_N(y_i/2)E|h_i−1| ≤ C√(p/d + ρ_v)`, using D7
    (`Σ_N y_iδ_i ≤ Cp`).
  - D8 and S1 handle `X_ii` versus `G_ii`.
  - `E|c−1| ≤ C(√ρ_v + ε_s + η₀ + 1/d)` follows from `(p−1)Var h_v ≤ r(r−1)` and `Eh_v = r` (contact).
  - Telescoping in `α`, plus `E[d_vb_ib_j] ≤ 1 + Cε`, gives `β ≤ α + Cξ` with `C` absolute.

### L11. `rc4_centres` — OK
- **Source:** (RC4), l.1927–1932. **Audit:** AUDIT-D §3.7.
- **Kind:** export (S1w `SecB.mean_shift_weighted_of_cl1`; F2).
- **Sketch.**
  - Lower bounds, pointwise on the support: `G_ii ≥ X_ii ≥ 0` and
    `G⁺G⁻ − X⁺X⁻ = (G⁺−X⁺)G⁻ + X⁺(G⁻−X⁻) ≥ 0`.
  - Upper bound: `G_ii² − X_ii² ≤ 2G_ii(G_ii − X_ii)`, then S1w with
    `Z = G_vv²G_ii/y_i`-type weights.
  - `(16d)⁻¹·d·s·3(K_S+2)B√h·2 ≤ (K_S+2)B√h`.
- **Witness:** `C = (K_S+2)B`, absolute. This is the critical `√κ₀` coefficient (AUDIT-D §4.2).
- **Small cases:** both differences `≥ 0`; `≥ 1.2·10⁻³` with positive sources.

### L12. `d13_centering` — statement OK; NEEDS FIX (placement, §1)
- **Source:** (RC5), (D13), l.1933–1951. **Audit:** AUDIT-D §3.7.
- **Kind:** chain (D6 or D7) plus `in_C2` and UMI.
- **Sketch** (sympy-checked):
  - the row-free part of `Q_*/a²` equals `2L_d[(p−1)t_{+,0} + p·t_{−,0}]` exactly;
  - the `x = 0` part is `−6p(2p−1)P z² ≤ 0`, dropped since `P ≥ 0`;
  - every monomial of `K − K|_{x=0}` has a factor `x` and a second row factor (mass 444).
- **Bound.** `(a⁴/3)·444p³·√(ΣE[x²D^c])·√(ΣE[(x²+z²)D^c])`, then UMI. With `S ≤ C₇p` (D7) and
  `a²S₋ ≤ C₂δ̄` (`in_C2`), this is `≤ Ca²p³√(pδ̄/d)`. The `x²` terms give
  `Cp⁴a⁴S/… ≤ Ca²p⁴/d ≤ Ca²p³√(pδ̄/d)`, because `p/d ≤ δ̄`.
- Valid on both routes (`δ̄` rather than `δ_row`).

### L13. `bm1_det` — OK
- **Source:** (BM1)–(BM3), l.1596–1641. **Audit:** AUDIT-D §3.3.
- **Kind:** pure linear algebra.
- **Sketch.**
  - `(r−s)² ≤ 2r² + 2s²`.
  - First part: `Σ_{i∈I,j}X_ii²U_ji² ≤ D²tr(BX²BY²)`, with `X_ii ∈ [0, D]` and `X ⪰ 0`.
  - `X² ⪯ h⁻¹X`: `Tools/MatrixFacts.posSemidef_smul_sub_mul_self`, from `hXn`, i.e.
    `h⁻¹I − X ⪰ 0`.
  - Then `tr(BX²BY²) ≤ h⁻¹tr(BXBY²) ≤ h⁻²tr(BXBY)` (`trace_mul_mul_self_le`,
    `trace_mul_le_trace_mul`).
  - Second part: `U_ii² ≤ X_ii(YBXBY)_ii` (CS in the `X`-inner product; `Matrix.PosSemidef.sqrt`)
    and `(X²)_ii ≤ h⁻¹X_ii`.
  - Finally `tr(BXBY) = 4bᵀ(X∘Y/4)b`.
- **Junk / degenerate cases.**
  - `I = ∅`, `b = 0`, empty `ι`: trivial.
  - `I ≠ ∅` forces `D ≥ 0`.
  - The padded diagonal `y_j` of `XP` outside `S` has `y_j ≤ s ≤ h⁻¹`, so `hXn` holds for the
    contact matrices (`h ≤ 1/2`).
- **Small cases:** worst ratio `0.25` in 2·10⁴ random or adversarial instances (rank one, flat
  spectrum, `Y = X`), and `0.013` on graph matrices.

### L14. `bm4_mask` — OK
- **Source:** (BM4), l.1643–1654. **Audit:** AUDIT-D §3.3.
- **Kind:** export (`bm1_det`; `SecB.dstar_moment`; UMI).
- **Sketch.**
  - Apply BM1 pointwise with `D = D_*`, valid since `X±_ii ≤ G±_ii ≤ D_* − 1` on `N`.
  - The sum over `j ∈ S` is at most the sum over all `j`.
  - Then `E[D_*^{m+2}·Ω bᵀKb] ≤ C_U(m)(z + θ)` by UMI with `θ = d⁻²` (envelope polynomial in
    `d, h⁻¹, D_*`).
- **Witness:** `C(m) = 16C_U(m)`.

### L15. `fs1_fixed_mask` — statement OK; NEEDS FIX (placement, §1)
- **Source:** (FS1)–(FS3), l.1656–1737. **Audit:** AUDIT-D §3.4.
- **Kind:** chain (D8) plus exports `SecB.wt2` (WT2), `SecB.ward_mean_of_cl1`/`in_W5` (W5), and UMI.
- **Sketch** (as in AUDIT-D §3.4):
  - the Schur identity FS2 splits `F_ji` into the direct and cavity maps of WT1;
  - WT2 applies with weight `H(X_ε)_ii²(X₊)_ii²`;
  - the cavity part uses `‖C^ε‖ ≤ h⁻¹`, the core/full subtraction, and the exact identities
    `4uᵀ(K₊−M₊)b₊` and `4uᵀ(K₊−M₊)u`;
  - the direct part uses W5;
  - `H ≤ 5D_*²Ω₊` uses **D8**.
- **Missing node.** FS2 (`F_ji = −a(X_ε)_ii(X₊)_ii Σ_{k∈N∖i, l∼i}(C_i^ε)_jk u_k (C_i^+)_kl ξ_l`, an
  exact Schur-complement identity; AUDIT-D lists it as a pure node) is stated nowhere. Per rule 3,
  add it as a node, e.g. `Contact/FS2.lean` or `SecB`, before dispatching FS1.

---

## 5. Route files, paper route (`RouteGCI.lean`, `RouteD9a.lean`; inactive since 07:21)

These files are now imported by nothing on the active chain. `RouteD9a` imports `Chain1` and
`RouteGCI`, and no name clashes with the DR1 files. All of them are true; they can stay as the
documented paper route or be deleted.

- **`in_GR1`**: GR1, l.626–693, through Royen's GCI. No GCI-free proof exists (DR1_CHECK §1).
  Unused on the DR1 route.
- **`in_CR3`**: actually route-independent. It is a conditional lemma (envelopes in, error out),
  and it follows from `SecC.row_comparison_split`, which takes fewer hypotheses (no `dc ≤ 1`), plus
  `e^{−3p} ≤ ϑ` eventually.
- **`cr1_real`** — OK. Witnesses:
  - `λ' = max(M, 2C₂+1)δ̄`;
  - `lr = lc = max(4, CM)·lam`;
  - `rr = dc = max(4, CM)·λ'`;
  - `C = 2|CC|·max(4, CM)·√max(M, 2C₂+1) + |CC| + 1`;
  - `P₀` with `max(4,CM)·max(M,2C₂+1)·3p^{−5/2} ≤ 1`.

  `ϑ ≤ λ'` holds because `λ' ≥ Mδ̄ ≥ lam ≥ ϑ`, even when `C₂ < 0`.
- **`cr1_gci`** — OK by reading. Its arguments `(HM ct).1/.2`, `(H2 ct).2.1`, `(H2 ct).2.2.2` and
  `(H3 ct)` match.
- **`d9a_real`** — OK. Witnesses:
  - `lr = 4(S+1)/d`;
  - `rr = 4(|Cr|+1)δ̄/p` (`Sm/d ≤ 4a²Sm` if `Sm ≥ 0`, trivial otherwise);
  - `lc = (|CM|+4)(|C₆|+|C₇|+2)p/d`;
  - `dc = 4(|CM|+4)(2|C₂|+1)δ̄`.

  The orderings hold for large `p`, and `p⁵√(lr·rr) = 4√(|Cr|+1)Γ√(S+1)`.
- **`d9a_gci`** — OK by reading. It uses the 13-tuple of `source_facts`, and
  `(HG ct ct.v ct.ctx.mem).2` is definitionally `a²·ct.Smin ≤ Cr·δ̄/p`.

## 6. Route files, GCI-free route (`RouteDR1.lean`, `RouteDR1D9a.lean`; active since 07:21)

The drafter implemented the replacements proposed in CHECK_CONTACT.md and in the first version of
this report, with one difference: (C2) at every vertex is now a Contact-level input `in_C2_all`.
Checks follow.

### `C2All`, `in_C2_all` — OK
- `C2All Kδ` says, at every contact and every `w ∈ S`:
  - `1 − ct.mp w ≤ Kδδ̄` and `1 − meanMinus … w ≤ Kδδ̄`;
  - `a²Σ_{j∼w}E(G±_wj)² ≤ Kδδ̄`.
- These are exactly (C2) at `w` (l.378–385, a supremum over vertices).
- **Export:** `SecA.concentration_C2` (CapPoint form, all `i, v ∈ cp.S`), applied to
  `ct.toCapPoint` (`cp.hp = hN`, `cp.N w = nbhd`, all definitional), with `uOf ≤ δ̄` (`ε ≥ 0`,
  `p⁴/d ≥ 0`) and `SecA.eventually_regA` for `RegA`.
- **Witness:** `Kδ := C` of `concentration_C2` (> 0).
- This is **the carrier of all-vertex (C2)**. Its consumers in the contact layer are `in_DR1` (all
  `w ∈ S`): `fs5_scores` uses it at `i ∈ N(v)`, and `d9a` and `cr1` at `w = v`.
- Inside the section proofs, `SecB.weak_loop_of` (the export behind `in_W1`) takes the CapPoint
  version `SecB.C2RowShape`. It should be fed from `concentration_C2` directly; there is no need to
  go through `in_C2_all`.
- `in_C2` (root only, Inputs.lean) stays as it is for its root-only consumers: `qstar_bound`, `d6`,
  `d7`, `cr1`, `d9a`, and the root-weight part of `fs5_scores`.

### `in_DR1_of_C2` — OK (proof route note)
- The statement is DR1 at every `w ∈ S` from the Contact-level `C2All Kδ`, with `∃ C` after `Kδ`.
  Since `Kδ` is absolute, the order is correct.
- **Proof route.** `SecB.dr1_of_c2` cannot be applied directly: its hypothesis is the CapPoint-wide
  `SecB.C2RowShape`, while `C2All` speaks only about contacts. Redo its 30-line proof pointwise
  instead. The argument is local to the point:
  1. `SecB.row_eq` (`∀ cp : CapPoint`) at `cp := ct.toCapPoint` gives the two residual bounds
     `≤ K₃p³/d`;
  2. `hC2 ct w hw` gives the four (C2) bounds at `w` (`rowSP`/`rowSM` are definitionally the sums
     in `C2All`);
  3. `SecB.dr1_pt` (with `ct.ctx.toCapPt`) and the closing algebra of `dr1_of_c2` (`le_dbar`,
     `1/d ≤ δ̄`, `p³/d ≤ δ̄`, `2p−1 ≥ p`) finish.
- **Witness:** `C := 6.02Kδ + 8.14 + 2K₃ + 1`.
- Alternatively, ignore `hC2` and use `SecB.dr1_of_c2` together with a CapPoint-level
  `C2RowShape` from `SecA.concentration_C2`. This is legal but bypasses the hypothesis.
- **Small cases.** These are covered by DR1_CHECK §5: isolated `w`, zero plus-source, `K₂` with
  `p = 3…25`.

### `in_DR1` — OK
- It is proved from `in_C2_all` and `in_DR1_of_C2` (`hKδ.le`); the proof compiles by reading.

### `in_CR3'` — OK
- **Export:** `SecC.row_comparison_diff` at `(ct.V, ct.G, ct.S, ct.lam, ct.yp, ct.ym, ct.v)` with
  `ct.ctx.toCapCtx`, `hyp`, `hym`, `mem`. The identifications are definitional: `incRowE` =
  `Srow`/`Smin`, `diffRowE`, `markE` = `frobP`/`frobM`, `rowMean` = `Rrow`, `rowGauss` = `Gterm`.
- `e^{−3p} ≤ ϑ` holds once `3p ≥ 10 log d` (`SecC.eventually_log_le`).
- The drafter's version keeps the hypothesis `dc ≤ 1`, which the export does not need. That is
  harmless: both consumers can discharge it (below).

### `cr1_real_dr1` — OK
- **Witnesses** (from its docstring):
  - `λ' = max(M, 2C₂+1)δ̄`;
  - `lr = lc = max(4, CM)·lam`;
  - `dc = max(4, CM)·λ'`;
  - `rd = max(4|CD|δ̄/p, ϑ)`.
- Hypotheses of the callback:
  - `S/d ≤ 4lam ≤ lr` and `Sm/d ≤ 4λ'`, from MARKENV;
  - `Dv/d ≤ 4a²Dv ≤ 4CDδ̄/p ≤ rd`, using `Dv ≥ 0`; if `CD < 0` the DR1 hypothesis is
    unsatisfiable;
  - `fP/d² ≤ CM·lam ≤ lc` and `fM/d² ≤ CM·λ' ≤ dc`;
  - `lc ≤ dc` because `lam ≤ Mδ̄ ≤ λ'`;
  - `dc ≤ 1` for `p ≥ P₀` (`δ̄ ≤ 3p^{−5/2}`).
- Conclusion: `p⁵√(lr·rd) ≤ √max(4,CM)·(2√|CD|·p⁵√(lamδ̄) + p⁵√(lamϑ))`, with `ϑ ≤ δ̄`, and
  `p⁴√(lc·dc) = max(4,CM)√max(M,2C₂+1)·p⁴√(lamδ̄)`.
- **Witness:** `C = |CC|·max(4,CM)·(2√|CD| + 1 + √max(M,2C₂+1)) + |CC| + 1`. True.
- Remark: CR1 does not need DR1. `SecC.row_comparison`, or `in_CR3` with `ρ_r = δ_c = Cδ̄`, gives it
  without the difference energy. The DR1-based proof is also correct.

### `cr1` (RouteDR1) — OK by reading
- Its arguments `(HM ct).1/.2`, `(H2 ct).2.1`, `(H2 ct).2.2.2`, `ct.rowDiff_nonneg`,
  `(HD ct ct.v ct.ctx.mem)`, `(H3 ct)`, `hl1`, `hl2`, `hl3` follow `cr1_real_dr1`'s hypothesis order.
- `HD` at `w = v` is definitionally `a²·Σ_{j∈N}E(x_j − z_j)²`, since `N = nbhd S v`, `x = gp v`
  and `z = gm v`.

### `d9a_real_dr1` — OK
- This is `d9a_real′` of the first version of this report, with `CD` for `Cr`, `0 ≤ Dv` moved, and
  `dc ≤ 1` added to the callback.
- **Witnesses:**
  - `lr = 4(S+1)/d` and `rd = 4(|CD|+1)δ̄/p` (`rd ≥ 4p³/d ≥ ϑ`);
  - `lc = (|CM|+4)(|C₆|+|C₇|+2)p/d`, from MARKENV plus with `l = C₆p/d`; `ϑ ≤ l` follows from
    the D6 hypothesis;
  - `dc = 4(|CM|+4)(2|C₂|+1)δ̄`, from MARKENV minus with `l = (2|C₂|+1)δ̄ ≥ ϑ` (`vth_le_dbar`).
- Orderings:
  - `lr ≤ lc` by `S ≤ C₇p`;
  - `lc ≤ dc` and `dc ≤ 1` for `p ≥ P₀(CM, C₂, C₆, C₇)`, because `p/d ≤ p^{−15/2}` and
    `δ̄ ≤ 3p^{−5/2}`.
- Conclusion: `p⁵√(lr·rd) = 4√(|CD|+1)Γ√(S+1)` and `p⁴√(lc·dc) = √(K₁K₂)Γ ≤ √(K₁K₂)Γ√(S+1)`.
- **Witness:** `C = |CC|(4√(|CD|+1) + √(K₁K₂) + 1) + 1`, with `K₁ = (|CM|+4)(|C₆|+|C₇|+2)` and
  `K₂ = 4(|CM|+4)(2|C₂|+1)`.

### `d9a` (RouteDR1D9a) — OK by reading
- `source_facts` 13-tuple gives `hS`, `hA2`.
- `ct.rowDiff_nonneg`, `(HD ct ct.v ct.ctx.mem)`, `(H6 ct)`, `(H7 ct).1` and `(H3 ct)` match
  `d9a_real_dr1`.
- The statement is unchanged, so `Chain2.d9b`/`d10` are unaffected.

### Remaining route items
- `fs5_scores` should import `RouteDR1.lean` when it moves to `Leaves2.lean` (§1). `Leaves2`
  imports `Chain1`, which already imports `RouteDR1`.
- `in_W1`'s export `SecB.weak_loop_of` needs `CL1Shape` (from `SecA.scalar_ineq`) and
  `C2RowShape` (from `SecA.concentration_C2`), both at the CapPoint level (CHECK_SECS §6).

## 7. Reproduce

```bash
/tmp/tight-venv/bin/python scripts/tight/check_leaves_enum.py   # exact enumeration, ~20 s
/tmp/tight-venv/bin/python scripts/tight/check_leaves_sym.py    # sympy K-structure + bm1_det, ~10 s
```
