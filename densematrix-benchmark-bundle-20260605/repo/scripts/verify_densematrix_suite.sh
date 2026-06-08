#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

usage() {
  cat <<'USAGE'
Usage: scripts/verify_densematrix_suite.sh SUITE_DIR_OR_TAR_GZ

Verifies a DenseMatrix benchmark suite package produced by package/run suite scripts.
USAGE
}

need_cmd() {
  if [[ "$1" == */* ]]; then
    [[ -x "$1" ]] || {
      echo "missing required command: $1" >&2
      exit 1
    }
    return
  fi
  command -v "$1" >/dev/null 2>&1 || {
    echo "missing required command: $1" >&2
    exit 1
  }
}

require_file() {
  local file="$1"
  [[ -f "$file" ]] || {
    echo "missing required file: $file" >&2
    exit 1
  }
}

line_count() {
  wc -l <"$1" | tr -d '[:space:]'
}

assert_eq() {
  local name="$1"
  local expected="$2"
  local actual="$3"
  if [[ "$expected" != "$actual" ]]; then
    echo "$name mismatch: expected $expected, got $actual" >&2
    exit 1
  fi
}

verify_archive_sidecar_sha256() {
  local archive="$1"
  local sidecar="$2"
  local expected actual

  [[ -f "$sidecar" ]] || return 0
  if (cd "$ROOT" && sha256sum -c "$sidecar" >/dev/null 2>&1); then
    return 0
  fi

  expected="$(awk 'NF >= 1 { print $1; exit }' "$sidecar")"
  if [[ ! "$expected" =~ ^[0-9A-Fa-f]{64}$ ]]; then
    echo "invalid SHA256 sidecar: $sidecar" >&2
    exit 1
  fi
  actual="$(sha256sum "$archive" | awk '{ print $1 }')"
  if [[ "${expected,,}" != "$actual" ]]; then
    echo "archive SHA256 mismatch for $archive: expected ${expected,,}, got $actual" >&2
    exit 1
  fi
}

if [[ "${1:-}" == "-h" || "${1:-}" == "--help" ]]; then
  usage
  exit 0
fi

if [[ $# -ne 1 ]]; then
  usage >&2
  exit 2
fi

need_cmd jq
need_cmd tar
need_cmd sha256sum
need_cmd diff
need_cmd "$ROOT/scripts/verify_densematrix_bench.sh"
need_cmd "$ROOT/scripts/summarize_densematrix_suite.sh"

INPUT="$1"
WORK_DIR=""
TMP_DIR=""

cleanup() {
  if [[ -n "$TMP_DIR" && -d "$TMP_DIR" ]]; then
    rm -rf "$TMP_DIR"
  fi
}
trap cleanup EXIT

if [[ -d "$INPUT" ]]; then
  WORK_DIR="$INPUT"
elif [[ -f "$INPUT" ]]; then
  case "$INPUT" in
    *.tar.gz|*.tgz)
      if [[ -f "$INPUT.sha256" ]]; then
        verify_archive_sidecar_sha256 "$INPUT" "$INPUT.sha256"
      fi
      TMP_DIR="$(mktemp -d)"
      tar -xzf "$INPUT" -C "$TMP_DIR"
      mapfile -t extracted_dirs < <(find "$TMP_DIR" -mindepth 1 -maxdepth 1 -type d | sort)
      if [[ "${#extracted_dirs[@]}" -ne 1 ]]; then
        echo "expected archive to contain exactly one top-level directory" >&2
        exit 1
      fi
      WORK_DIR="${extracted_dirs[0]}"
      ;;
    *)
      echo "unsupported suite input: $INPUT" >&2
      exit 2
      ;;
  esac
else
  echo "suite input does not exist: $INPUT" >&2
  exit 2
fi

required_files=(
  REPRODUCE.md
  SHA256SUMS
  git-diff.patch
  git-diff-stat.txt
  git-log.txt
  git-rev-parse.txt
  git-status.txt
  git-untracked-files.txt
  git-untracked.patch
  package.log
  suite-config.json
  suite-manifest.csv
  suite-manifest.json
  suite-summary.csv
)

for file in "${required_files[@]}"; do
  require_file "$WORK_DIR/$file"
done

[[ -d "$WORK_DIR/bundles" ]] || {
  echo "missing required directory: $WORK_DIR/bundles" >&2
  exit 1
}

(cd "$WORK_DIR" && sha256sum -c SHA256SUMS >/dev/null)

jq -e . "$WORK_DIR/suite-config.json" >/dev/null
jq -e . "$WORK_DIR/suite-manifest.json" >/dev/null

expected_manifest_header="\"path\",\"role\",\"bytes\",\"sha256\""
actual_manifest_header="$(head -n 1 "$WORK_DIR/suite-manifest.csv")"
assert_eq "suite-manifest.csv header" "$expected_manifest_header" "$actual_manifest_header"

diff -u \
  <(cd "$WORK_DIR" && find . -type f \
      ! -name SHA256SUMS \
      ! -name suite-manifest.csv \
      ! -name suite-manifest.json \
      -printf '%P\n' | sort) \
  <(jq -r '.[].path' "$WORK_DIR/suite-manifest.json" | sort) >/dev/null || {
  echo "suite-manifest.json does not match suite file inventory" >&2
  exit 1
}

assert_eq "suite-manifest.csv line count" \
  "$(($(jq 'length' "$WORK_DIR/suite-manifest.json") + 1))" \
  "$(line_count "$WORK_DIR/suite-manifest.csv")"

jq -e '
  length > 5 and
  all(.[]; (.path | type == "string" and length > 0) and
    (.role | type == "string" and length > 0) and
    (.bytes | type == "number" and . >= 0) and
    (.sha256 | type == "string" and test("^[0-9a-f]{64}$"))) and
  ([.[].role] | index("benchmark_bundle")) != null and
  ([.[].role] | index("suite_summary")) != null and
  ([.[].role] | index("reproducibility")) != null and
  ([.[].role] | index("repository_state")) != null and
  ([.[].role] | index("suite_audit")) != null
' "$WORK_DIR/suite-manifest.json" >/dev/null

while IFS=$'\t' read -r path role bytes sha256; do
  require_file "$WORK_DIR/$path"
  actual_bytes="$(stat -c '%s' "$WORK_DIR/$path")"
  actual_sha256="$(sha256sum "$WORK_DIR/$path" | awk '{print $1}')"
  assert_eq "suite manifest bytes for $path" "$bytes" "$actual_bytes"
  assert_eq "suite manifest sha256 for $path" "$sha256" "$actual_sha256"
  case "$role" in
    benchmark_bundle|suite_summary|reproducibility|repository_state|suite_audit)
      ;;
    *)
      echo "suite manifest has unknown role for $path: $role" >&2
      exit 1
      ;;
  esac
done < <(jq -r '.[] | [.path, .role, (.bytes | tostring), .sha256] | @tsv' \
  "$WORK_DIR/suite-manifest.json")

shopt -s nullglob
bundle_archives=("$WORK_DIR"/bundles/*.tar.gz)
shopt -u nullglob
if [[ "${#bundle_archives[@]}" -lt 1 ]]; then
  echo "suite has no bundled benchmark archives" >&2
  exit 1
fi

assert_eq "suite-config bundle_count" \
  "$(jq -r '.bundle_count' "$WORK_DIR/suite-config.json")" \
  "${#bundle_archives[@]}"
assert_eq "suite-summary.csv line count" \
  "$((${#bundle_archives[@]} + 1))" \
  "$(line_count "$WORK_DIR/suite-summary.csv")"

for bundle in "${bundle_archives[@]}"; do
  require_file "$bundle.sha256"
  verify_archive_sidecar_sha256 "$bundle" "$bundle.sha256"
  "$ROOT/scripts/verify_densematrix_bench.sh" "$bundle" >/dev/null
done

tmp_summary="$(mktemp)"
"$ROOT/scripts/summarize_densematrix_suite.sh" --out "$tmp_summary" "${bundle_archives[@]}"
diff -u <(cut -d, -f2- "$WORK_DIR/suite-summary.csv") <(cut -d, -f2- "$tmp_summary") >/dev/null || {
  echo "suite-summary.csv does not match recomputed summary" >&2
  rm -f "$tmp_summary"
  exit 1
}
rm -f "$tmp_summary"

grep -q 'scripts/verify_densematrix_suite.sh' "$WORK_DIR/REPRODUCE.md" || {
  echo "REPRODUCE.md missing suite verify command" >&2
  exit 1
}
grep -q 'scripts/run_densematrix_suite.sh' "$WORK_DIR/REPRODUCE.md" || {
  echo "REPRODUCE.md missing suite run command" >&2
  exit 1
}

echo "verified DenseMatrix benchmark suite: $WORK_DIR"
