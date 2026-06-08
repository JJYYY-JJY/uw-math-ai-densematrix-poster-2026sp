#!/usr/bin/env bash
set -euo pipefail

BUNDLE_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
REPO="${1:-${DENSEMATRIX_REPO:-$BUNDLE_DIR/repo}}"

if [[ ! -f "$REPO/lakefile.toml" || ! -d "$REPO/ProvableComputation" ]]; then
  echo "usage: $0 [/path/to/provable_computation]" >&2
  echo "default bundled repo not found: $REPO" >&2
  exit 2
fi

cd "$REPO"
echo "Using repository source: $REPO"
if [[ ! -d "$REPO/.lake/packages/mathlib" ]]; then
  echo "No bundled .lake mathlib checkout found; Lake may clone/build dependencies." >&2
fi
OUT_DIR="${DENSEMATRIX_OUT_DIR:-bench-results/densematrix-smoke-reproduced}"
CORE="${DENSEMATRIX_CORE:-3}"

bench-tools/run_densematrix_48h.sh \
  --out-dir "$OUT_DIR" \
  --core "$CORE" \
  --sizes "4,8" \
  --warmups 1 \
  --repeats 1 \
  --quiet

bench-tools/summarize_densematrix_jsonl.py "$OUT_DIR/results.jsonl" --out-dir "$OUT_DIR/summary"
if [[ "$OUT_DIR" = /* ]]; then
  RESULT_PATH="$OUT_DIR"
else
  RESULT_PATH="$REPO/$OUT_DIR"
fi
echo "Smoke reproduction complete: $RESULT_PATH"
