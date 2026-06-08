#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

OUT_PARENT="bench-results"
NAME=""
ORIGINAL_ARGS=("$@")

usage() {
  cat <<'USAGE'
Usage: scripts/package_densematrix_suite.sh [options] BUNDLE_DIR_OR_TAR_GZ...

Verifies DenseMatrix benchmark bundles and packages them into one suite archive.

Options:
  --out-dir DIR        Parent directory for the suite directory (default: bench-results).
  --name NAME          Suite directory name (default: densematrix-suite-<timestamp>-<git>).
  -h, --help           Show this help.
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

csv_quote() {
  local value="${1//\"/\"\"}"
  printf '"%s"' "$value"
}

json_array_from_lines() {
  jq -R . | jq -s .
}

suite_manifest_role() {
  local path="$1"
  case "$path" in
    bundles/*)
      echo "benchmark_bundle"
      ;;
    suite-summary.csv|suite-config.json)
      echo "suite_summary"
      ;;
    REPRODUCE.md)
      echo "reproducibility"
      ;;
    git-*)
      echo "repository_state"
      ;;
    *)
      echo "suite_audit"
      ;;
  esac
}

write_suite_manifest() {
  local out_dir="$1"
  {
    echo '"path","role","bytes","sha256"'
    while IFS= read -r rel; do
      local role bytes hash
      role="$(suite_manifest_role "$rel")"
      bytes="$(stat -c '%s' "$out_dir/$rel")"
      hash="$(sha256sum "$out_dir/$rel" | awk '{print $1}')"
      csv_quote "$rel"
      printf ','
      csv_quote "$role"
      printf ',%s,' "$bytes"
      csv_quote "$hash"
      printf '\n'
    done < <(
      cd "$out_dir"
      find . -type f \
        ! -name SHA256SUMS \
        ! -name suite-manifest.csv \
        ! -name suite-manifest.json \
        -printf '%P\n' | sort
    )
  } >"$out_dir/suite-manifest.csv"

  {
    echo '['
    local first=1
    while IFS= read -r rel; do
      local role bytes hash
      role="$(suite_manifest_role "$rel")"
      bytes="$(stat -c '%s' "$out_dir/$rel")"
      hash="$(sha256sum "$out_dir/$rel" | awk '{print $1}')"
      if [[ "$first" -eq 0 ]]; then
        echo ','
      fi
      first=0
      jq -n \
        --arg path "$rel" \
        --arg role "$role" \
        --arg sha256 "$hash" \
        --argjson bytes "$bytes" \
        '{path: $path, role: $role, bytes: $bytes, sha256: $sha256}'
    done < <(
      cd "$out_dir"
      find . -type f \
        ! -name SHA256SUMS \
        ! -name suite-manifest.csv \
        ! -name suite-manifest.json \
        -printf '%P\n' | sort
    )
    echo
    echo ']'
  } >"$out_dir/suite-manifest.json"
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --out-dir)
      OUT_PARENT="${2:?--out-dir requires a value}"
      shift 2
      ;;
    --name)
      NAME="${2:?--name requires a value}"
      shift 2
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    --)
      shift
      break
      ;;
    -*)
      echo "unknown argument: $1" >&2
      usage >&2
      exit 2
      ;;
    *)
      break
      ;;
  esac
done

if [[ $# -lt 1 ]]; then
  usage >&2
  exit 2
fi

need_cmd jq
need_cmd tar
need_cmd sha256sum
need_cmd "$ROOT/scripts/verify_densematrix_bench.sh"
need_cmd "$ROOT/scripts/summarize_densematrix_suite.sh"

mkdir -p "$OUT_PARENT"
STAMP="$(date -u +%Y%m%dT%H%M%SZ)"
GIT_SHORT="$(git rev-parse --short HEAD 2>/dev/null || echo unknown)"
if [[ -z "$NAME" ]]; then
  NAME="densematrix-suite-${STAMP}-${GIT_SHORT}"
fi

SUITE_DIR="$OUT_PARENT/$NAME"
if [[ -e "$SUITE_DIR" || -e "$SUITE_DIR.tar.gz" ]]; then
  echo "suite output already exists: $SUITE_DIR" >&2
  exit 1
fi
mkdir -p "$SUITE_DIR/bundles"

bundle_archives=()
original_inputs=("$@")

for input in "$@"; do
  "$ROOT/scripts/verify_densematrix_bench.sh" "$input" >/dev/null
  if [[ -f "$input" ]]; then
    case "$input" in
      *.tar.gz|*.tgz)
        dest="$SUITE_DIR/bundles/$(basename "$input")"
        cp "$input" "$dest"
        archive_sha="$(sha256sum "$dest" | awk '{print $1}')"
        echo "$archive_sha  bundles/$(basename "$dest")" >"$dest.sha256"
        ;;
      *)
        echo "unsupported bundle file: $input" >&2
        exit 2
        ;;
    esac
  elif [[ -d "$input" ]]; then
    base="$(basename "$input")"
    parent="$(cd "$(dirname "$input")" && pwd)"
    dest="$SUITE_DIR/bundles/${base}.tar.gz"
    tar -czf "$dest" -C "$parent" "$base"
    archive_sha="$(sha256sum "$dest" | awk '{print $1}')"
    echo "$archive_sha  bundles/$(basename "$dest")" >"$dest.sha256"
  else
    echo "bundle input does not exist: $input" >&2
    exit 2
  fi
  bundle_archives+=("$dest")
done

"$ROOT/scripts/summarize_densematrix_suite.sh" --out "$SUITE_DIR/suite-summary.csv" \
  "${bundle_archives[@]}"

{
  echo "\$ scripts/package_densematrix_suite.sh ${ORIGINAL_ARGS[*]}"
  echo "generated_at_utc=$STAMP"
  echo "git=$GIT_SHORT"
  echo "suite_dir=$SUITE_DIR"
  echo "bundle_count=${#bundle_archives[@]}"
} >"$SUITE_DIR/package.log"

git status --short --branch >"$SUITE_DIR/git-status.txt" 2>&1 || true
git rev-parse HEAD >"$SUITE_DIR/git-rev-parse.txt" 2>&1 || true
git log --oneline -5 >"$SUITE_DIR/git-log.txt" 2>&1 || true
git diff --stat >"$SUITE_DIR/git-diff-stat.txt" 2>&1 || true
git diff --no-color >"$SUITE_DIR/git-diff.patch" 2>&1 || true
git ls-files --others --exclude-standard >"$SUITE_DIR/git-untracked-files.txt" 2>&1 || true
{
  while IFS= read -r file; do
    [[ -f "$file" ]] || continue
    git diff --no-index -- /dev/null "$file" || true
  done <"$SUITE_DIR/git-untracked-files.txt"
} >"$SUITE_DIR/git-untracked.patch"

inputs_json="$(printf '%s\n' "${original_inputs[@]}" | json_array_from_lines)"
bundles_json="$(
  for bundle in "${bundle_archives[@]}"; do
    printf '%s\n' "bundles/$(basename "$bundle")"
  done | json_array_from_lines
)"

jq -n \
  --arg generated_at_utc "$STAMP" \
  --arg git "$GIT_SHORT" \
  --arg suite_dir "$SUITE_DIR" \
  --arg script_invocation "scripts/package_densematrix_suite.sh ${ORIGINAL_ARGS[*]}" \
  --argjson bundle_count "${#bundle_archives[@]}" \
  --argjson inputs "$inputs_json" \
  --argjson bundles "$bundles_json" \
  '{
    generated_at_utc: $generated_at_utc,
    git: $git,
    suite_dir: $suite_dir,
    script_invocation: $script_invocation,
    bundle_count: $bundle_count,
    inputs: $inputs,
    bundled_archives: $bundles
  }' >"$SUITE_DIR/suite-config.json"

cat >"$SUITE_DIR/REPRODUCE.md" <<EOF
# DenseMatrix Benchmark Suite Package

Generated: $STAMP

This suite package contains verified DenseMatrix benchmark bundle archives under
\`bundles/\` plus \`suite-summary.csv\`, which summarizes profile, matrix
envelope, timing coverage, kernel/compiler match status, RSS, and archive
checksums for each bundle.

Verify the suite archive:

\`\`\`bash
scripts/verify_densematrix_suite.sh $NAME.tar.gz
\`\`\`

Regenerate the suite summary from the bundled archives:

\`\`\`bash
scripts/summarize_densematrix_suite.sh --out /tmp/densematrix-suite-summary.csv bundles/*.tar.gz
\`\`\`

Run a fresh post-reboot full suite:

\`\`\`bash
scripts/run_densematrix_suite.sh --install-tools --tune-system --core 2
\`\`\`
EOF

write_suite_manifest "$SUITE_DIR"

(
  cd "$SUITE_DIR"
  find . -type f ! -name SHA256SUMS -printf '%P\n' | sort | xargs sha256sum
) >"$SUITE_DIR/SHA256SUMS"

ARCHIVE="$SUITE_DIR.tar.gz"
tar -czf "$ARCHIVE" -C "$(dirname "$SUITE_DIR")" "$(basename "$SUITE_DIR")"
sha256sum "$ARCHIVE" >"$ARCHIVE.sha256"

echo "suite package: $ARCHIVE"
echo "checksum: $ARCHIVE.sha256"
