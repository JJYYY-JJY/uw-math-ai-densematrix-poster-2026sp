#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

OUT_DIR="bench-results/densematrix-48h"
CORE="3"
SIZES="4,8,16,24,32,48,64,80,96,128,160,192,256,384,512,768,1024,1536,2048"
WARMUPS="10"
REPEATS="50"
QUIET=0

usage() {
  cat <<'USAGE'
Usage: bench-tools/run_densematrix_48h.sh [options]

Runs the single-thread DenseMatrix-vs-mathlib benchmark profile intended for
poster data collection. Results stream to JSONL and can be resumed safely.

Options:
  --out-dir DIR     Result directory (default: bench-results/densematrix-48h).
  --core N          CPU core for taskset pinning (default: 3).
  --sizes LIST      Comma-separated square sizes.
  --warmups N       Warmup runs per benchmark record (default: 10).
  --repeats N       Measured repeats per benchmark record (default: 50).
  --quiet           Suppress per-repeat progress from the Lean harness.
  -h, --help        Show this help.

Resume behavior:
  The runner always uses --skip-existing. If results.jsonl already contains a
  completed record with the same backend/operation/size/warmups/repeats key,
  that record is skipped and the remaining records continue.
USAGE
}

need_cmd() {
  command -v "$1" >/dev/null 2>&1 || {
    echo "missing required command: $1" >&2
    exit 1
  }
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --out-dir)
      OUT_DIR="${2:?--out-dir requires a value}"
      shift 2
      ;;
    --core)
      CORE="${2:?--core requires a value}"
      shift 2
      ;;
    --sizes)
      SIZES="${2:?--sizes requires a value}"
      shift 2
      ;;
    --warmups)
      WARMUPS="${2:?--warmups requires a value}"
      shift 2
      ;;
    --repeats)
      REPEATS="${2:?--repeats requires a value}"
      shift 2
      ;;
    --quiet)
      QUIET=1
      shift
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    *)
      echo "unknown argument: $1" >&2
      usage >&2
      exit 2
      ;;
  esac
done

[[ "$CORE" =~ ^[0-9]+$ ]] || {
  echo "--core must be a natural number" >&2
  exit 2
}
[[ "$WARMUPS" =~ ^[0-9]+$ ]] || {
  echo "--warmups must be a natural number" >&2
  exit 2
}
[[ "$REPEATS" =~ ^[0-9]+$ ]] || {
  echo "--repeats must be a natural number" >&2
  exit 2
}

need_cmd git
need_cmd lean
need_cmd lake
need_cmd taskset
need_cmd lscpu
need_cmd date

mkdir -p "$OUT_DIR"

RESULTS="$OUT_DIR/results.jsonl"
PROGRESS="$OUT_DIR/progress.log"

{
  echo "repo=$ROOT"
  echo "out_dir=$OUT_DIR"
  echo "core=$CORE"
  echo "sizes=$SIZES"
  echo "warmups=$WARMUPS"
  echo "repeats=$REPEATS"
  echo "results=$RESULTS"
  echo "progress_log=$PROGRESS"
} >"$OUT_DIR/run-config.txt"

if git rev-parse --is-inside-work-tree >/dev/null 2>&1; then
  git rev-parse HEAD >"$OUT_DIR/git-rev.txt"
  git status --short >"$OUT_DIR/git-status.txt"
  git diff --stat >"$OUT_DIR/git-diff-stat.txt"
  git diff >"$OUT_DIR/git-diff.patch"
else
  echo "not a git checkout; running from source snapshot" >"$OUT_DIR/git-rev.txt"
  echo "not a git checkout; running from source snapshot" >"$OUT_DIR/git-status.txt"
  echo "not a git checkout; running from source snapshot" >"$OUT_DIR/git-diff-stat.txt"
  : >"$OUT_DIR/git-diff.patch"
fi
lean --version >"$OUT_DIR/lean-version.txt"
lake --version >"$OUT_DIR/lake-version.txt"
lscpu >"$OUT_DIR/lscpu.txt"
uname -a >"$OUT_DIR/uname.txt"
date -Is >"$OUT_DIR/start-time.txt"

args=(
  lake exe densematrix_bench
  --sizes "$SIZES"
  --warmups "$WARMUPS"
  --repeats "$REPEATS"
  --skip-existing
  --jsonl "$RESULTS"
)

if [[ "$QUIET" -eq 1 ]]; then
  args+=(--quiet)
fi

{
  printf '$ taskset -c %q' "$CORE"
  printf ' %q' "${args[@]}"
  printf '\n'
} >"$OUT_DIR/command.txt"

echo "Starting DenseMatrix benchmark. Progress: $PROGRESS" >&2
set +e
taskset -c "$CORE" "${args[@]}" 2>>"$PROGRESS"
status=$?
set -e

date -Is >"$OUT_DIR/end-time.txt"
echo "$status" >"$OUT_DIR/exit-status.txt"

if [[ "$status" -ne 0 ]]; then
  echo "benchmark failed with exit status $status; see $PROGRESS" >&2
  exit "$status"
fi

echo "benchmark complete: $RESULTS" >&2
echo "summarize with: bench-tools/summarize_densematrix_jsonl.py $RESULTS --out-dir $OUT_DIR/summary" >&2
