#!/usr/bin/env bash
# Verification gate for the RoughHeatKernel package.
set -euo pipefail
cd "$(dirname "$0")"
artifacts="${VERIFY_ARTIFACTS_DIR:-$PWD/.lake/verification}"
mkdir -p "$artifacts"

echo "toolchain: $(lean --version | sed -n '1p')"
echo "manifest mathlib revision: $(grep -B8 '"name": "mathlib"' lake-manifest.json | grep -m1 '"rev"' | sed 's/^ *//')"

# 1. No placeholders or project axioms in library sources.
if grep -n -w -E 'sorry|admit|axiom|opaque' RoughHeatKernel.lean RoughHeatKernel/*.lean; then
  echo "placeholder or project axiom found" >&2; exit 1
fi
echo "placeholder audit: PASS"

# References are fully proved snapshots; test witnesses also contain no holes.
reference_sources=(RoughHeatKernelChallenge.lean RoughHeatKernelSolution.lean)
while IFS= read -r source; do reference_sources+=("$source"); done < <(find RoughHeatKernelChallenge -name '*.lean' | LC_ALL=C sort)
if grep -n -w -E 'sorry|admit|axiom|opaque|unsafe|native_decide|implemented_by|skipKernelTC|trustLevel|include_str|include_bytes|run_io|run_cmd|run_elab' "${reference_sources[@]}"; then
  echo "reference proof escape found" >&2; exit 1
fi
if grep -n -w -E 'sorry|admit|axiom|opaque|unsafe|native_decide|implemented_by|skipKernelTC|trustLevel|include_str|include_bytes|run_io|run_cmd|run_elab' RoughHeatKernelTest/*.lean RoughHeatKernelTest/*.lean.disabled; then
  echo "test proof escape found" >&2; exit 1
fi

# 2. Fresh own production, reference and test builds in separate environments.
# One complete unfiltered ordered build window. The exact upstream predicate
# permits a replay only after that SAME module's earlier actual Built event.
# Per-target checks additionally require every expected source module to build.
export LAKE_ARTIFACT_CACHE=false
export LAKE_CACHE_DIR="$(mktemp -d "$artifacts/lake-cache.XXXXXX")"
: > "$artifacts/all-build.log"
rm -rf .lake/build
build_scoped() {
  local target="$1" raw="$artifacts/build-$1.log" rc
  set +e
  lake --no-cache --verbose --log-level info --no-ansi build "$target" > "$raw" 2>&1
  rc=$?
  set -e
  cat "$raw" | tee -a "$artifacts/all-build.log"
  [ "$rc" -eq 0 ] || return "$rc"
  bash scripts/lake_guard.sh fresh "$artifacts/all-build.log" "$target"
  echo "scoped-build-log-sha256: $target $(sha256sum "$raw" | cut -d' ' -f1)"
}
echo "lean-pkg-build: begin"
build_scoped RoughHeatKernel
build_scoped RoughHeatKernelChallenge
# Serialize test modules explicitly; Lean threads alone do not limit Lake jobs.
build_scoped RoughHeatKernelTest.Counterexamples
for source in RoughHeatKernelTest/*.lean; do
  [ "$source" = RoughHeatKernelTest/Counterexamples.lean ] && continue
  module="${source%.lean}"
  build_scoped "${module//\//.}"
done
build_scoped RoughHeatKernelTest
build_scoped RoughHeatKernelSolution
echo "lean-pkg-build: end"
bash scripts/lake_guard.sh fresh "$artifacts/all-build.log" RoughHeatKernel RoughHeatKernelTest RoughHeatKernelChallenge RoughHeatKernelSolution
bash scripts/lake_guard.sh shadow "$(lake env printenv LEAN_PATH)" "$PWD/.lake/build/lib/lean" RoughHeatKernel RoughHeatKernelTest RoughHeatKernelChallenge RoughHeatKernelSolution

# 3. Exact inventory: source theorems == inventory == #check list == #print axioms list.
tmp="$artifacts"
awk -f scripts/theorem_names.awk RoughHeatKernel/*.lean | LC_ALL=C sort > "$tmp/source"
LC_ALL=C sort THEOREM_INVENTORY.txt > "$tmp/inventory"
sed -n 's/^#check @//p' RoughHeatKernelTest/TypeCheck.lean | LC_ALL=C sort > "$tmp/check"
sed -n 's/^#print axioms //p' RoughHeatKernelTest/AxiomCheck.lean | LC_ALL=C sort > "$tmp/axioms"
for f in source check axioms; do
  if ! diff -u "$tmp/inventory" "$tmp/$f"; then
    echo "theorem inventory mismatch ($f)" >&2; exit 1
  fi
done
echo "theorem inventory: PASS ($(wc -l < "$tmp/inventory") public theorems)"

# 4. Axiom audit: every inventoried theorem reports only the standard axioms.
lake lean RoughHeatKernelTest/AxiomCheck.lean > "$tmp/axiom-out"
# Print the per-theorem axiom reports into the log, so receipts can bind them.
cat "$tmp/axiom-out"
reported="$(grep -c "depends on axioms" "$tmp/axiom-out" || true)"
if [ "$reported" -ne "$(wc -l < "$tmp/inventory")" ]; then
  echo "axiom result count $reported does not match the inventory" >&2; exit 1
fi
# Lean wraps long axiom lists across lines, so join the output before parsing the lists.
if tr '\n' ' ' < "$tmp/axiom-out" | grep -o 'depends on axioms: \[[^]]*\]' \
    | sed 's/.*\[//; s/\]//' | tr ',' '\n' | sed 's/^ *//; s/ *$//' | sed '/^$/d' | sort -u \
    | grep -v -x -E 'propext|Classical.choice|Quot.sound'; then
  echo "unexpected axiom dependency" >&2; exit 1
fi
echo "axiom audit: PASS (only propext, Classical.choice, Quot.sound)"

# Complete compiler ownership and the Std3 union are checked once in the native
# stage below, with exact prior production-owner names and per-module replay.
# Keep the independent public-theorem #print-axioms audit above. The former
# per-constant legacy loop duplicated ownership/allowlist work without replay.

# 5. Elaborated types.
lake lean RoughHeatKernelTest/TypeCheck.lean > "$tmp/types"
echo "type check: PASS ($(grep -c '^@\?RoughHeatKernel' "$tmp/types" || true) declarations printed)"

# 6. Usage examples must compile.
lake lean RoughHeatKernelTest/Examples.lean
echo "usage examples: PASS"

# 7. Strict G17 expected-reason controls. Witness modules build one at a time.
# A false universal statement is retained in each disabled file; the independently
# compiled positive witness proves its concrete counterexample and iff False.
count=0
for neg in RoughHeatKernelTest/*.lean.disabled; do
  base="${neg%.lean.disabled}"
  witness="${base}Witness.lean"
  module="${base//\//.}Witness"
  [ -f "$witness" ] || { echo "missing witness: $witness" >&2; exit 1; }
  set +e
  lake lean "$witness" > "$artifacts/$(basename "$base")-witness.log" 2>&1
  wexit=$?
  set -e
  bash scripts/lake_guard.sh witness "$witness" "$artifacts/$(basename "$base")-witness.log" "$wexit"
  set +e
  lake lean "$neg" > "$artifacts/$(basename "$base")-negative.log" 2>&1
  nexit=$?
  set -e
  bash scripts/lake_guard.sh negative-control "$neg" "$artifacts/$(basename "$base")-negative.log" "$nexit" "$module"
  count=$((count + 1))
done
[ "$count" -eq 11 ] || { echo "expected exactly eleven strict controls, found $count" >&2; exit 1; }
echo "negative controls: PASS ($count strict sole-False mutations with compiled witnesses)"

# All compiled production/test/reference owners, exact first providers, three
# compiled escape controls and every selected module's leanchecker replay.
LIBRARY_AUDIT_DIR=${LIBRARY_AUDIT_DIR:?set an absent external directory for native reports}
export LIBRARY_AUDIT_DIR
python3 scripts/native_owned.py

echo "verification gate: PASS"
