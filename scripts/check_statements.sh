#!/usr/bin/env bash
# Local analogue of the comparator's statement check: the three Challenge theorems and the
# definitions their statements use must be identical in the `Challenge` and `Solution`
# environments (same names, universe parameters, types, and definition bodies).
# Usage: scripts/check_statements.sh   (after `lake build Challenge Solution`)
set -euo pipefail
cd "$(dirname "$0")/.."
tmp=$(mktemp -d)
for m in Challenge Solution; do
  cat > "$tmp/$m.lean" <<EOF
import $m
open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  for n in [\`\`BiluLinial.Signing, \`\`BiluLinial.signedAdjMatrix, \`\`BiluLinial.opNorm] do
    let some ci := env.find? n | throwError "missing {n}"
    IO.println s!"{n} {ci.levelParams} {repr ci.type} {repr ci.value?}"
  for n in [\`\`BiluLinial.near_ramanujan_signing, \`\`BiluLinial.explicit_excess,
      \`\`BiluLinial.opNorm_eq_iSup_abs_eigenvalues₀] do
    let some ci := env.find? n | throwError "missing {n}"
    IO.println s!"{n} {ci.levelParams} {repr ci.type}"
EOF
  # Hygienic names of anonymous binders embed the module name; binder names are irrelevant to
  # the kernel (`Expr` equality is up to binder names), so they are normalised.
  lake env lean "$tmp/$m.lean" | sed -E 's/«_@»\.[A-Za-z0-9_.]+ /«_@».M /g' > "$tmp/$m.out"
done
if diff -q "$tmp/Challenge.out" "$tmp/Solution.out" > /dev/null; then
  echo "statements identical (3 definitions and 3 theorems compared)"
else
  diff "$tmp/Challenge.out" "$tmp/Solution.out" | head -40
  echo "MISMATCH"
  exit 1
fi
