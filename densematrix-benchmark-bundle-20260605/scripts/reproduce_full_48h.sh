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
test -x bench-tools/run_densematrix_48h.sh || {
  echo "missing bench-tools/run_densematrix_48h.sh in $REPO" >&2
  echo "Use the benchmark branch/source snapshot included in this bundle." >&2
  exit 2
}
test -x bench-tools/summarize_densematrix_jsonl.py || {
  echo "missing bench-tools/summarize_densematrix_jsonl.py in $REPO" >&2
  exit 2
}

OUT_DIR="${DENSEMATRIX_OUT_DIR:-bench-results/densematrix-48h-reproduced}"
CORE="${DENSEMATRIX_CORE:-3}"

bench-tools/run_densematrix_48h.sh \
  --out-dir "$OUT_DIR" \
  --core "$CORE" \
  --sizes "4,8,16,24,32,48,64,80,96,128,160,192,256,384,512,768,1024,1536,2048" \
  --warmups 10 \
  --repeats 50

bench-tools/summarize_densematrix_jsonl.py "$OUT_DIR/results.jsonl" --out-dir "$OUT_DIR/summary"
if [[ "$OUT_DIR" = /* ]]; then
  RESULT_PATH="$OUT_DIR"
else
  RESULT_PATH="$REPO/$OUT_DIR"
fi
echo "Full reproduction complete: $RESULT_PATH"
echo "Reference bundle: $BUNDLE_DIR"
