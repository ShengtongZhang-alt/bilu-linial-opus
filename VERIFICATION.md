# Verification record

Date: 2026-10-01 (UTC−7), on the Lean sources of the commit that adds this file.

Toolchain:

- Lean `v4.35.0-rc2` (`lean-toolchain`, identical to Mathlib's), which bundles `lake comparator`
  and the NanoDa and con-ron kernels
- Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55` (tag `v4.35.0-rc2`)

Commands, run from the repository root on macOS:

```bash
lake build                              # BiluLinial, Challenge, Solution
scripts/check_statements.sh
python3 scripts/check-lean-sources.py
ruby scripts/validate-formalization.rb
ruby scripts/check-submission-files.rb
scripts/check-metadata-schema.sh        # check-jsonschema 0.38.0
ruby scripts/check-axioms.rb
PALOMAR_COMPARATOR_NO_SANDBOX=1 scripts/verify-comparator.sh
```

Results:

- `lake build` succeeds. The module-system port changed all 225 Lean files, so every project module
  was recompiled. The only `sorry` warnings are the three deliberate holes in `Challenge.lean`.
- `scripts/check_statements.sh` reports "statements identical (3 definitions and 3 theorems
  compared)". It compares universe parameters, types and definition bodies in the `Challenge`
  and `Solution` environments.
- `scripts/check-lean-sources.py` passes: every Lean file starts with the `module` header, and the
  largest file has 2,818 lines, under the 10,000-line cap. `Challenge.lean` has 52 lines, under
  the 300-line warning threshold. It carries short docstrings; `README_lean.md`
  gives precise versions.
- The third compared theorem, `opNorm_eq_iSup_abs_eigenvalues₀`, states that `opNorm` equals the
  largest absolute value of an eigenvalue for symmetric matrices, with Mathlib's
  `Matrix.IsHermitian.eigenvalues₀`. `#print axioms` on it in `Solution` reports only `propext`,
  `Classical.choice` and `Quot.sound`.
- `scripts/validate-formalization.rb`: "formalization.yaml contains no TEMPLATE values".
  `scripts/check-submission-files.rb`: "submission files OK". `scripts/check-metadata-schema.sh`:
  `formalization.yaml` validates against the pinned upstream v0.4 schema.
- `#print axioms` reports exactly `propext`, `Classical.choice` and `Quot.sound` for
  `BiluLinial.near_ramanujan_signing` and `BiluLinial.explicit_excess` (in `Solution`), for
  `near_ramanujan_signing_proof`, `explicit_excess_proof` and the library theorem
  `bilu_linial_counterexample_proof` (in `BiluLinial.Main`). `scripts/check-axioms.rb`: "axiom
  reports agree with comparator.json and formalization.yaml".
- `lake comparator` with the toolchain's NanoDa and con-ron kernels, configured as Palomar does by
  `scripts/verify-comparator.sh`: "con-ron: accepted 69872 declarations", "con-ron kernel accepts
  the solution", "nanoda kernel accepts the solution", "Lean default kernel accepts the solution",
  "Your solution is okay!".
  - macOS has no `bwrap`, so this run used `--inadvisably-no-sandbox`.
  - The CI workflow runs the same script inside the sandbox on Linux.

No `sorry` outside `Challenge.lean`, no `admit`, `native_decide` or `axiom` declaration is
present. The only `set_option` in the project is `maxHeartbeats 400000` on the lemma
`d3_monomials` (`BiluLinial/Tight/SecB/W1FibD3Arith.lean`). It changes the elaboration budget,
not what the kernel checks.
