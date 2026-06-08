#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

OUT=""

usage() {
  cat <<'USAGE'
Usage: scripts/summarize_densematrix_suite.sh [--out FILE] BUNDLE_DIR_OR_TAR_GZ...

Verifies each DenseMatrix benchmark bundle, then writes one CSV row per bundle.
Both result directories and .tar.gz archives are accepted.
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

TMP_DIRS=()

cleanup() {
  local dir
  for dir in "${TMP_DIRS[@]}"; do
    [[ -d "$dir" ]] && rm -rf "$dir"
  done
}
trap cleanup EXIT

resolve_bundle() {
  local input="$1"
  local -n out_var="$2"
  if [[ -d "$input" ]]; then
    out_var="$input"
    return
  fi
  if [[ -f "$input" ]]; then
    case "$input" in
      *.tar.gz|*.tgz)
        local tmp
        tmp="$(mktemp -d)"
        TMP_DIRS+=("$tmp")
        tar -xzf "$input" -C "$tmp"
        mapfile -t extracted_dirs < <(find "$tmp" -mindepth 1 -maxdepth 1 -type d | sort)
        if [[ "${#extracted_dirs[@]}" -ne 1 ]]; then
          echo "expected archive to contain exactly one top-level directory: $input" >&2
          exit 1
        fi
        out_var="${extracted_dirs[0]}"
        return
        ;;
    esac
  fi
  echo "unsupported bundle input: $input" >&2
  exit 2
}

kernel_match_count() {
  local file="$1"
  local status="$2"
  awk -F, -v status="$status" '
    NR == 1 { next }
    {
      row_status = $9
      gsub(/^"|"$/, "", row_status)
      if (row_status == status) {
        count++
      }
    }
    END { print count + 0 }
  ' "$file"
}

kernel_suite_sizes_for_status() {
  local file="$1"
  local status="$2"
  awk -F, -v status="$status" '
    NR == 1 { next }
    {
      category = $1
      row_status = $9
      gsub(/^"|"$/, "", category)
      gsub(/^"|"$/, "", row_status)
      if (category == "suite" && row_status == status) {
        sizes[++n] = $3
      }
    }
    END {
      for (i = 1; i <= n; i++) {
        if (i > 1) {
          printf(";")
        }
        printf("%s", sizes[i])
      }
      printf("\n")
    }
  ' "$file"
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --out)
      OUT="${2:?--out requires a value}"
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

RUN_TMP="$(mktemp -d)"
TMP_DIRS+=("$RUN_TMP")
CSV_TMP="$RUN_TMP/densematrix-suite-summary.csv"

{
  printf '%s\n' '"input","profile","git","core","pin_command","compiler_records","compiler_sample_count","compiler_sample_total_s","compiler_measured_to_elapsed_ratio","compiler_max_rows","compiler_max_cols","compiler_max_inner","compiler_max_work_items","dense_mathlib_pair_count","dense_only_case_count","dense_mathlib_checksum_mismatch_count","exact_kernel_compiler_rows","missing_kernel_compiler_rows","exact_kernel_compiler_suite_sizes","missing_kernel_compiler_suite_sizes","compiler_elapsed_s","compiler_max_rss_kb","archive_sha256"'
  for input in "$@"; do
    "$ROOT/scripts/verify_densematrix_bench.sh" "$input" >/dev/null
    bundle_dir=""
    resolve_bundle "$input" bundle_dir

    archive_sha=""
    if [[ -f "$input" ]]; then
      archive_sha="$(sha256sum "$input" | awk '{print $1}')"
    fi

    exact_rows="$(kernel_match_count "$bundle_dir/kernel-compiler-comparison.csv" "exact_compiler_match")"
    missing_rows="$(kernel_match_count "$bundle_dir/kernel-compiler-comparison.csv" "missing_compiler_match")"
    exact_sizes="$(kernel_suite_sizes_for_status "$bundle_dir/kernel-compiler-comparison.csv" "exact_compiler_match")"
    missing_sizes="$(kernel_suite_sizes_for_status "$bundle_dir/kernel-compiler-comparison.csv" "missing_compiler_match")"

    mapfile -t fields < <(
      jq -r '
        . as $s
        | [
            .profile,
            .git,
            .core,
            .pin_command,
            (.compiler_records | tostring),
            (.compiler_sample_count | tostring),
            (.compiler_sample_total_s | tostring),
            (.compiler_measured_to_elapsed_ratio | tostring),
            (.compiler_max_rows | tostring),
            (.compiler_max_cols | tostring),
            (.compiler_max_inner | tostring),
            (.compiler_max_work_items | tostring),
            (.dense_mathlib_pair_count | tostring),
            (.dense_only_case_count | tostring),
            (.dense_mathlib_checksum_mismatch_count | tostring),
            (.compiler_process_metrics.elapsed_s | tostring),
            (.compiler_process_metrics.max_rss_kb | tostring)
          ][]
      ' "$bundle_dir/summary.json"
    )

    values=(
      "$input"
      "${fields[0]}"
      "${fields[1]}"
      "${fields[2]}"
      "${fields[3]}"
      "${fields[4]}"
      "${fields[5]}"
      "${fields[6]}"
      "${fields[7]}"
      "${fields[8]}"
      "${fields[9]}"
      "${fields[10]}"
      "${fields[11]}"
      "${fields[12]}"
      "${fields[13]}"
      "${fields[14]}"
      "$exact_rows"
      "$missing_rows"
      "$exact_sizes"
      "$missing_sizes"
      "${fields[15]}"
      "${fields[16]}"
      "$archive_sha"
    )

    for i in "${!values[@]}"; do
      if [[ "$i" -gt 0 ]]; then
        printf ','
      fi
      csv_quote "${values[$i]}"
    done
    printf '\n'
  done
} >"$CSV_TMP"

if [[ -n "$OUT" ]]; then
  cp "$CSV_TMP" "$OUT"
else
  cat "$CSV_TMP"
fi
