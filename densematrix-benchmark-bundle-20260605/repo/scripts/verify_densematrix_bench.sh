#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

usage() {
  cat <<'USAGE'
Usage: scripts/verify_densematrix_bench.sh BUNDLE_DIR_OR_TAR_GZ

Verifies a DenseMatrix benchmark bundle produced by run_densematrix_bench.sh.
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
need_cmd sha256sum
need_cmd tar
need_cmd awk

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
      elif [[ -f "${INPUT%.tar.gz}.tar.gz.sha256" ]]; then
        verify_archive_sidecar_sha256 "$INPUT" "${INPUT%.tar.gz}.tar.gz.sha256"
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
      echo "unsupported bundle input: $INPUT" >&2
      exit 2
      ;;
  esac
else
  echo "bundle does not exist: $INPUT" >&2
  exit 2
fi

required_files=(
  REPRODUCE.md
  SHA256SUMS
  api-coverage.csv
  benchmark-env.json
  build.log
  bundle-manifest.csv
  bundle-manifest.json
  compiler.stderr
  compiler.stdout
  compiler.jsonl
  compiler.csv
  compiler-case-manifest.csv
  compiler-samples.csv
  compiler-throughput.csv
  compiler-command.txt
  compiler-process-metrics.json
  compiler-time.txt
  coverage.md
  cgroup-after.txt
  cgroup-before.txt
  cpu-after.txt
  cpu-before.txt
  dense-mathlib-pairs.csv
  dense-mathlib-summary.csv
  dense-only-cases.csv
  executable-artifact.json
  git-diff.patch
  git-diff-stat.txt
  git-log.txt
  git-ls-files.txt
  git-rev-parse.txt
  git-status.txt
  git-untracked-files.stderr
  git-untracked-files.txt
  git-untracked.patch
  install-tools.txt
  kernel-compiler-comparison.csv
  kernel.jsonl
  kernel.csv
  kernel-profile-summary.csv
  lake-manifest.json
  lake-version.txt
  lakefile.toml
  lean-features.txt
  lean-toolchain
  lean-version.txt
  matrix-size-envelope.csv
  measurement-quality.json
  operation-scaling.csv
  pinning-preflight.txt
  pinning-postflight.txt
  profile-plan.csv
  rerun.sh
  run-config.json
  summary.json
  summary.md
  system-release.txt
  tool-availability.json
  tool-paths.txt
  tune-system.txt
)

for file in "${required_files[@]}"; do
  require_file "$WORK_DIR/$file"
done

[[ -x "$WORK_DIR/rerun.sh" ]] || {
  echo "rerun.sh is not executable: $WORK_DIR/rerun.sh" >&2
  exit 1
}

grep -q 'scripts/run_densematrix_bench.sh' "$WORK_DIR/REPRODUCE.md" || {
  echo "REPRODUCE.md missing run command" >&2
  exit 1
}
grep -q 'scripts/verify_densematrix_bench.sh' "$WORK_DIR/REPRODUCE.md" || {
  echo "REPRODUCE.md missing verify command" >&2
  exit 1
}
grep -q 'scripts/compare_densematrix_bench.sh' "$WORK_DIR/REPRODUCE.md" || {
  echo "REPRODUCE.md missing compare command" >&2
  exit 1
}
grep -q 'REPO_ROOT' "$WORK_DIR/rerun.sh" || {
  echo "rerun.sh missing REPO_ROOT override support" >&2
  exit 1
}
grep -q 'scripts/run_densematrix_bench.sh' "$WORK_DIR/rerun.sh" || {
  echo "rerun.sh missing benchmark command" >&2
  exit 1
}
for cgroup_file in cgroup-before.txt cgroup-after.txt; do
  grep -q '== /proc/self/cgroup ==' "$WORK_DIR/$cgroup_file" || {
    echo "$cgroup_file missing /proc/self/cgroup section" >&2
    exit 1
  }
  grep -q '== cgroup limits ==' "$WORK_DIR/$cgroup_file" || {
    echo "$cgroup_file missing cgroup limits section" >&2
    exit 1
  }
done
for privileged_file in install-tools.txt tune-system.txt; do
  grep -q '^step=' "$WORK_DIR/$privileged_file" || {
    echo "$privileged_file missing step marker" >&2
    exit 1
  }
  grep -q '^requested=' "$WORK_DIR/$privileged_file" || {
    echo "$privileged_file missing requested marker" >&2
    exit 1
  }
  grep -q '^status=' "$WORK_DIR/$privileged_file" || {
    echo "$privileged_file missing status marker" >&2
    exit 1
  }
  grep -q '^pkexec_timeout_seconds=' "$WORK_DIR/$privileged_file" || {
    echo "$privileged_file missing pkexec timeout marker" >&2
    exit 1
  }
done

[[ -d "$WORK_DIR/kernel" ]] || {
  echo "missing required directory: $WORK_DIR/kernel" >&2
  exit 1
}

(cd "$WORK_DIR" && sha256sum -c SHA256SUMS >/dev/null)

expected_api_header="api,visibility,coverage_kind,compiler_operations,mathlib_operations,kernel_operations,correctness_or_static,shapes,elements,data_profiles,notes"
actual_api_header="$(head -n 1 "$WORK_DIR/api-coverage.csv")"
assert_eq "api-coverage.csv header" "$expected_api_header" "$actual_api_header"

require_api_coverage_row() {
  local api="$1"
  awk -F, -v api="$api" '
    NR == 1 { next }
    $1 == api {
      found = 1
      if (NF != 11) {
        bad = 1
      }
      for (i = 2; i <= NF; i++) {
        if ($i == "") {
          bad = 1
        }
      }
    }
    END { exit found && !bad ? 0 : 1 }
  ' "$WORK_DIR/api-coverage.csv" || {
    echo "api-coverage.csv missing or incomplete row for $api" >&2
    exit 1
  }
}

required_apis=(
  DenseMatrix.structure_data
  DenseMatrix.rowMajorIndex
  DenseMatrix.rowMajorIndex_lt
  DenseMatrix.get!
  DenseMatrix.set!
  DenseMatrix.get
  DenseMatrix.set
  DenseMatrix.ToString
  DenseMatrix.toMatrix
  DenseMatrix.ofMatrix
  DenseMatrix.toMatrix_ofMatrix
  DenseMatrix.ofMatrix_toMatrix
  DenseMatrix.of
  DenseMatrix.add
  DenseMatrix.smul
  DenseMatrix.dot
  DenseMatrix.mul_helper
  DenseMatrix.mul
  DenseMatrix.transpose_helper
  DenseMatrix.transpose
  DenseMatrix.private_index_proofs
)

for api in "${required_apis[@]}"; do
  require_api_coverage_row "$api"
done

jq -e . "$WORK_DIR/summary.json" >/dev/null
jq -e . "$WORK_DIR/run-config.json" >/dev/null
jq -e . "$WORK_DIR/tool-availability.json" >/dev/null
jq -e . "$WORK_DIR/benchmark-env.json" >/dev/null
jq -e . "$WORK_DIR/bundle-manifest.json" >/dev/null
jq -e . "$WORK_DIR/executable-artifact.json" >/dev/null
jq -e . "$WORK_DIR/compiler.jsonl" >/dev/null
jq -e . "$WORK_DIR/compiler-process-metrics.json" >/dev/null
jq -e . "$WORK_DIR/kernel.jsonl" >/dev/null
jq -e . "$WORK_DIR/measurement-quality.json" >/dev/null
jq -e '
  .exit_status == 0 and
  (.elapsed_s | type == "number" and . >= 0) and
  (.user_s | type == "number" and . >= 0) and
  (.system_s | type == "number" and . >= 0) and
  (.max_rss_kb | type == "number" and . >= 0) and
  (.major_page_faults | type == "number" and . >= 0) and
  (.minor_page_faults | type == "number" and . >= 0) and
  (.voluntary_context_switches | type == "number" and . >= 0) and
  (.involuntary_context_switches | type == "number" and . >= 0)
' "$WORK_DIR/compiler-process-metrics.json" >/dev/null
jq -s -e '
  .[0].compiler_process_metrics.exit_status == 0 and
  .[0].compiler_process_metrics.max_rss_kb == .[1].max_rss_kb and
  .[0].compiler_process_metrics.elapsed_s == .[1].elapsed_s
' "$WORK_DIR/summary.json" "$WORK_DIR/compiler-process-metrics.json" >/dev/null
jq -s -e '
  .[0].executable_artifact.path == .[1].path and
  .[0].executable_artifact.sha256 == .[1].sha256 and
  .[0].executable_artifact.bytes == .[1].bytes
' "$WORK_DIR/summary.json" "$WORK_DIR/executable-artifact.json" >/dev/null
jq -s -e --rawfile compilerCommand "$WORK_DIR/compiler-command.txt" '
  .[0].profile == .[1].profile and
  .[0].core == .[1].core and
  .[0].pin_command == .[1].pin_command and
  .[0].pkexec_timeout_seconds == .[1].pkexec_timeout_seconds and
  .[0].compiler.command == ($compilerCommand | rtrimstr("\n"))
' "$WORK_DIR/run-config.json" "$WORK_DIR/summary.json" >/dev/null
jq -e '
  (.kernel.sizes_effective | type == "string" and length > 0) and
  (.pkexec_timeout_seconds | type == "number" and . >= 1) and
  (.compiler.command | startswith("lake exe densematrix_bench")) and
  (.script_invocation | startswith("scripts/run_densematrix_bench.sh"))
' "$WORK_DIR/run-config.json" >/dev/null
jq -e '
  . as $root |
  $root.required_available == true and
  ($root.optional_missing | type == "array") and
  all(["lake","lean","taskset","jq","tar","sha256sum","time"][]; . as $name
    | ($root.tools[$name].required == true and $root.tools[$name].available == true
      and ($root.tools[$name].path | type == "string" and length > 0))) and
  all(["numactl","perf","cpupower","pkexec","dnf"][]; . as $name
    | ($root.tools[$name].required == false and ($root.tools[$name].available | type == "boolean")))
' "$WORK_DIR/tool-availability.json" >/dev/null
jq -e '
  . as $root
  | (.generated_at_utc | type == "string" and length > 0) and
    (.git | type == "string" and length > 0) and
    (.cwd | type == "string" and length > 0) and
    (.path_sha256 | type == "string" and test("^[0-9a-f]{64}$")) and
    (.variables | type == "object") and
    (.present_keys | type == "array") and
    (.absent_keys | type == "array") and
    (.notes | type == "array" and length > 0) and
    all(["PATH","SHELL","LANG","LC_ALL","TZ","LEAN_PATH","LD_LIBRARY_PATH","LD_PRELOAD","MALLOC_ARENA_MAX","OMP_NUM_THREADS"][]; . as $key
      | ($root.variables | has($key))) and
    all($root.variables[]; . == null or type == "string") and
    ((($root.present_keys + $root.absent_keys) | sort) == ($root.variables | keys | sort))
' "$WORK_DIR/benchmark-env.json" >/dev/null
for section in '/etc/os-release' 'glibc' 'ldd --version' 'locale' 'date/timezone' 'ulimit'; do
  grep -q "== $section ==" "$WORK_DIR/system-release.txt" || {
    echo "system-release.txt missing section: $section" >&2
    exit 1
  }
done
jq -e '
  .path == ".lake/build/bin/densematrix_bench" and
  (.absolute_path | type == "string" and endswith("/.lake/build/bin/densematrix_bench")) and
  (.bytes | type == "number" and . > 0) and
  (.sha256 | type == "string" and test("^[0-9a-f]{64}$")) and
  .executable == true and
  .binary_bundled == false and
  (.binary_bundled_reason | type == "string" and length > 0) and
  (.file.available | type == "boolean") and
  (.file.output | type == "string") and
  (.ldd.available | type == "boolean") and
  (.ldd.output | type == "string")
' "$WORK_DIR/executable-artifact.json" >/dev/null

expected_bundle_manifest_header="\"path\",\"role\",\"bytes\",\"sha256\""
actual_bundle_manifest_header="$(head -n 1 "$WORK_DIR/bundle-manifest.csv")"
assert_eq "bundle-manifest.csv header" "$expected_bundle_manifest_header" "$actual_bundle_manifest_header"

diff -u \
  <(cd "$WORK_DIR" && find . -type f \
      ! -name SHA256SUMS \
      ! -name bundle-manifest.csv \
      ! -name bundle-manifest.json \
      -printf '%P\n' | sort) \
  <(jq -r '.[].path' "$WORK_DIR/bundle-manifest.json" | sort) >/dev/null || {
  echo "bundle-manifest.json does not match bundle file inventory" >&2
  exit 1
}

assert_eq "bundle-manifest.csv line count" \
  "$(($(jq 'length' "$WORK_DIR/bundle-manifest.json") + 1))" \
  "$(line_count "$WORK_DIR/bundle-manifest.csv")"

jq -e '
  length > 20 and
  all(.[]; (.path | type == "string" and length > 0) and
    (.role | type == "string" and length > 0) and
    (.bytes | type == "number" and . >= 0) and
    (.sha256 | type == "string" and test("^[0-9a-f]{64}$"))) and
  ([.[].role] | index("reproducibility")) != null and
  ([.[].role] | index("build_source")) != null and
  ([.[].role] | index("build_artifact")) != null and
  ([.[].role] | index("compiler_measurement")) != null and
  ([.[].role] | index("kernel_measurement")) != null and
  ([.[].role] | index("audit_summary")) != null and
  ([.[].role] | index("environment")) != null and
  ([.[].role] | index("repository_state")) != null and
  ([.[].role] | index("other")) == null
' "$WORK_DIR/bundle-manifest.json" >/dev/null

while IFS=$'\t' read -r path role bytes sha256; do
  require_file "$WORK_DIR/$path"
  actual_bytes="$(stat -c '%s' "$WORK_DIR/$path")"
  actual_sha256="$(sha256sum "$WORK_DIR/$path" | awk '{print $1}')"
  assert_eq "bundle manifest bytes for $path" "$bytes" "$actual_bytes"
  assert_eq "bundle manifest sha256 for $path" "$sha256" "$actual_sha256"
  case "$role" in
    reproducibility|build_source|build_artifact|compiler_measurement|kernel_measurement|audit_summary|environment|repository_state)
      ;;
    *)
      echo "bundle manifest has unknown role for $path: $role" >&2
      exit 1
      ;;
  esac
done < <(jq -r '.[] | [.path, .role, (.bytes | tostring), .sha256] | @tsv' "$WORK_DIR/bundle-manifest.json")

expected_profile_header="profile,command,use_case,compiler_sizes,repeats,warmups,rat_max,string_max,data_max,kernel_sizes,max_base_size,max_rows,max_cols,max_inner,max_work_items,notes"
actual_profile_header="$(head -n 1 "$WORK_DIR/profile-plan.csv")"
assert_eq "profile-plan.csv header" "$expected_profile_header" "$actual_profile_header"
assert_eq "profile-plan.csv line count" "6" "$(line_count "$WORK_DIR/profile-plan.csv")"

require_profile_plan_row() {
  local profile="$1"
  awk -F, -v profile="$profile" '
    NR == 1 { next }
    $1 == profile {
      found = 1
      if (NF != 16) {
        bad = 1
      }
      for (i = 2; i <= NF; i++) {
        if ($i == "") {
          bad = 1
        }
      }
      if ($5 !~ /^[0-9]+$/ || $6 !~ /^[0-9]+$/ || $7 !~ /^[0-9]+$/ ||
          $8 !~ /^[0-9]+$/ || $9 !~ /^[0-9]+$/ || $11 !~ /^[0-9]+$/ ||
          $12 !~ /^[0-9]+$/ || $13 !~ /^[0-9]+$/ || $14 !~ /^[0-9]+$/ ||
          $15 !~ /^[0-9]+$/) {
        bad = 1
      }
    }
    END { exit found && !bad ? 0 : 1 }
  ' "$WORK_DIR/profile-plan.csv" || {
    echo "profile-plan.csv missing or invalid row for $profile" >&2
    exit 1
  }
}

for profile in quick full stress xl mega; do
  require_profile_plan_row "$profile"
done

run_profile="$(jq -r '.profile' "$WORK_DIR/run-config.json")"
require_profile_plan_row "$run_profile"

jq -s -e '
  all(.[]; has("q1_ms") and has("q3_ms") and has("p90_ms") and has("p95_ms")
    and has("mad_ms") and has("cv"))
' "$WORK_DIR/compiler.jsonl" >/dev/null
jq -s -e '
  all(.[]; has("samples_ns") and (.samples_ns | type == "array")
    and (.samples_ns | length) == .count
    and all(.samples_ns[]?; type == "number" and . >= 0))
' "$WORK_DIR/compiler.jsonl" >/dev/null
jq -s -e '
  def absval: if . < 0 then -1 * . else . end;
  def near($actual; $reported; $epsilon):
    (($actual - $reported) | absval) <= $epsilon;
  all(.[]; . as $case
    | ($case.count > 0) and
      (($case.samples_ns | map(. / 1000000)) as $ms
      | ($ms | sort) as $sorted
      | ($case.count) as $count
      | (($count * 25 / 100) | floor) as $q1Idx
      | (($count * 75 / 100) | floor) as $q3Idx
      | (($count * 90 / 100) | floor) as $p90Idx
      | (($count * 95 / 100) | floor) as $p95Idx
      | ($ms | add / $count) as $mean
      | ($sorted[($count / 2 | floor)]) as $median
      | ($ms | map(. as $x | ($x - $mean) * ($x - $mean)) | add / $count | sqrt) as $stddev
      | ($ms | map(if . < $median then $median - . else . - $median end) | sort) as $absDev
      | near($sorted[0]; $case.min_ms; 0.00001) and
        near($sorted[$q1Idx]; $case.q1_ms; 0.00001) and
        near($median; $case.median_ms; 0.00001) and
        near($mean; $case.mean_ms; 0.00001) and
        near($sorted[$p90Idx]; $case.p90_ms; 0.00001) and
        near($sorted[$p95Idx]; $case.p95_ms; 0.00001) and
        near($sorted[$q3Idx]; $case.q3_ms; 0.00001) and
        near($sorted[$count - 1]; $case.max_ms; 0.00001) and
        near($stddev; $case.stddev_ms; 0.00001) and
        near($absDev[($count / 2 | floor)]; $case.mad_ms; 0.00001) and
        near((if $mean == 0 then 0 else $stddev / $mean end); $case.cv; 0.000001)))
' "$WORK_DIR/compiler.jsonl" >/dev/null
jq -s -e '
  all(.[]; (.data_profile // "deterministic") | type == "string")
' "$WORK_DIR/compiler.jsonl" >/dev/null

compiler_records="$(line_count "$WORK_DIR/compiler.jsonl")"
compiler_samples="$(jq -s 'map(.samples_ns | length) | add // 0' "$WORK_DIR/compiler.jsonl")"
compiler_sample_total_ns="$(jq -s 'map((.samples_ns // []) | (add // 0)) | add // 0' "$WORK_DIR/compiler.jsonl")"
kernel_records="$(line_count "$WORK_DIR/kernel.jsonl")"
summary_compiler_records="$(jq -r '.compiler_records' "$WORK_DIR/summary.json")"
summary_compiler_samples="$(jq -r '.compiler_sample_count' "$WORK_DIR/summary.json")"
summary_compiler_sample_total_ns="$(jq -r '.compiler_sample_total_ns' "$WORK_DIR/summary.json")"
summary_pair_count="$(jq -r '.dense_mathlib_pair_count' "$WORK_DIR/summary.json")"
summary_dense_only_count="$(jq -r '.dense_only_case_count' "$WORK_DIR/summary.json")"
summary_mismatch_count="$(jq -r '.dense_mathlib_checksum_mismatch_count' "$WORK_DIR/summary.json")"
summary_core="$(jq -r '.core' "$WORK_DIR/summary.json")"
quality_compiler_records="$(jq -r '.compiler_records' "$WORK_DIR/measurement-quality.json")"
quality_compiler_samples="$(jq -r '.compiler_sample_count' "$WORK_DIR/measurement-quality.json")"
quality_compiler_sample_total_ns="$(jq -r '.compiler_sample_total_ns' "$WORK_DIR/measurement-quality.json")"
quality_min_samples="$(jq -r '.min_samples_per_record' "$WORK_DIR/measurement-quality.json")"
quality_max_samples="$(jq -r '.max_samples_per_record' "$WORK_DIR/measurement-quality.json")"

assert_eq "compiler_records" "$compiler_records" "$summary_compiler_records"
assert_eq "measurement compiler_records" "$summary_compiler_records" "$quality_compiler_records"
assert_eq "compiler.csv line count" "$((compiler_records + 1))" "$(line_count "$WORK_DIR/compiler.csv")"
assert_eq "compiler-case-manifest.csv line count" "$((compiler_records + 1))" \
  "$(line_count "$WORK_DIR/compiler-case-manifest.csv")"
assert_eq "compiler_sample_count" "$compiler_samples" "$summary_compiler_samples"
assert_eq "measurement compiler_sample_count" "$summary_compiler_samples" "$quality_compiler_samples"
assert_eq "compiler_sample_total_ns" "$compiler_sample_total_ns" "$summary_compiler_sample_total_ns"
assert_eq "measurement compiler_sample_total_ns" \
  "$summary_compiler_sample_total_ns" "$quality_compiler_sample_total_ns"
assert_eq "measurement min_samples_per_record" \
  "$(jq -r '.compiler_min_samples_per_record' "$WORK_DIR/summary.json")" "$quality_min_samples"
assert_eq "measurement max_samples_per_record" \
  "$(jq -r '.compiler_max_samples_per_record' "$WORK_DIR/summary.json")" "$quality_max_samples"
assert_eq "compiler-samples.csv line count" "$((compiler_samples + 1))" \
  "$(line_count "$WORK_DIR/compiler-samples.csv")"
assert_eq "compiler-throughput.csv line count" "$((compiler_records + 1))" \
  "$(line_count "$WORK_DIR/compiler-throughput.csv")"
expected_size_header="\"track\",\"setup_policy\",\"shape_family\",\"operation\",\"element\",\"data_profile\",\"case_count\",\"min_rows\",\"max_rows\",\"min_cols\",\"max_cols\",\"min_inner\",\"max_inner\",\"max_work_items\",\"max_output_cells\",\"max_input_cells\",\"max_total_matrix_cells\""
actual_size_header="$(head -n 1 "$WORK_DIR/matrix-size-envelope.csv")"
assert_eq "matrix-size-envelope.csv header" "$expected_size_header" "$actual_size_header"
expected_size_envelope_groups="$(
  jq -s '
    def shapeFamily:
      if (.operation | contains("zero_rows")) then "zero_rows"
      elif (.operation | contains("zero_cols")) then "zero_cols"
      elif (.operation | contains("wide_inner")) then "mul_wide_inner"
      elif (.operation | contains("tall_output")) then "mul_tall_output"
      elif (.operation | contains("skinny_inner")) then "mul_skinny_inner"
      elif (.operation | contains("wide")) then "wide"
      elif (.operation | contains("tall")) then "tall"
      else "square" end;
    def setupPolicy:
      if (.track | endswith("_prebuilt")) then "prebuilt_inputs" else "setup_inclusive" end;
    group_by([.track, setupPolicy, shapeFamily, .operation, .element, (.data_profile // "deterministic")])
    | length
  ' "$WORK_DIR/compiler.jsonl"
)"
assert_eq "matrix-size-envelope.csv line count" "$((expected_size_envelope_groups + 1))" \
  "$(line_count "$WORK_DIR/matrix-size-envelope.csv")"
assert_eq "kernel.csv line count" "$((kernel_records + 1))" "$(line_count "$WORK_DIR/kernel.csv")"
assert_eq "dense-mathlib-pairs.csv line count" "$((summary_pair_count + 1))" \
  "$(line_count "$WORK_DIR/dense-mathlib-pairs.csv")"
expected_dense_summary_header="\"dense_track\",\"baseline_track\",\"setup_policy\",\"shape_family\",\"operation\",\"element\",\"data_profile\",\"pair_count\",\"max_rows\",\"max_cols\",\"max_inner\",\"max_work_items\",\"median_ratio_min\",\"median_ratio_median\",\"median_ratio_mean\",\"median_ratio_max\",\"p95_ratio_min\",\"p95_ratio_median\",\"p95_ratio_mean\",\"p95_ratio_max\",\"checksum_mismatch_count\",\"worst_median_rows\",\"worst_median_cols\",\"worst_median_inner\",\"worst_p95_rows\",\"worst_p95_cols\",\"worst_p95_inner\""
actual_dense_summary_header="$(head -n 1 "$WORK_DIR/dense-mathlib-summary.csv")"
assert_eq "dense-mathlib-summary.csv header" "$expected_dense_summary_header" "$actual_dense_summary_header"
expected_pair_summary_groups="$(
  awk -F, '
    NR > 1 {
      key = $1 FS $2 FS $3 FS $4 FS $5 FS $6 FS $7
      seen[key] = 1
    }
    END {
      count = 0
      for (key in seen) {
        count++
      }
      print count
    }
  ' "$WORK_DIR/dense-mathlib-pairs.csv"
)"
assert_eq "dense-mathlib-summary.csv line count" "$((expected_pair_summary_groups + 1))" \
  "$(line_count "$WORK_DIR/dense-mathlib-summary.csv")"
assert_eq "dense-only-cases.csv line count" "$((summary_dense_only_count + 1))" \
  "$(line_count "$WORK_DIR/dense-only-cases.csv")"
expected_scaling_header="\"track\",\"setup_policy\",\"shape_family\",\"operation\",\"element\",\"data_profile\",\"case_count\",\"min_work_items\",\"max_work_items\",\"min_rows\",\"max_rows\",\"min_cols\",\"max_cols\",\"min_inner\",\"max_inner\",\"median_ms_at_min_work\",\"median_ms_at_max_work\",\"median_growth_ratio\",\"p95_ms_at_min_work\",\"p95_ms_at_max_work\",\"p95_growth_ratio\",\"max_cv\",\"max_p95_over_median\""
actual_scaling_header="$(head -n 1 "$WORK_DIR/operation-scaling.csv")"
assert_eq "operation-scaling.csv header" "$expected_scaling_header" "$actual_scaling_header"
assert_eq "operation-scaling.csv line count" "$((expected_size_envelope_groups + 1))" \
  "$(line_count "$WORK_DIR/operation-scaling.csv")"

actual_pair_bad="$(
  awk -F, 'NR > 1 && $NF != "\"ok\"" { bad++ } END { print bad + 0 }' \
    "$WORK_DIR/dense-mathlib-pairs.csv"
)"
assert_eq "dense/mathlib checksum mismatch count" "$summary_mismatch_count" "$actual_pair_bad"
assert_eq "dense/mathlib checksum mismatch count" "0" "$actual_pair_bad"
actual_pair_summary_pairs="$(
  awk -F, 'NR > 1 { sum += $8 } END { print sum + 0 }' \
    "$WORK_DIR/dense-mathlib-summary.csv"
)"
assert_eq "dense/mathlib summary pair count" "$summary_pair_count" "$actual_pair_summary_pairs"
actual_pair_summary_bad="$(
  awk -F, 'NR > 1 { bad += $21 } END { print bad + 0 }' \
    "$WORK_DIR/dense-mathlib-summary.csv"
)"
assert_eq "dense/mathlib summary checksum mismatch count" "$summary_mismatch_count" "$actual_pair_summary_bad"

actual_dense_only_bad="$(
  awk -F, 'NR > 1 && $11 != "\"dense_only_no_direct_mathlib_operation\"" { bad++ } END { print bad + 0 }' \
    "$WORK_DIR/dense-only-cases.csv"
)"
assert_eq "dense-only reason count" "0" "$actual_dense_only_bad"

awk -F, '
  NR == 1 { next }
  NF != 17 { bad = 1 }
  {
    for (i = 7; i <= 17; i++) {
      if ($i !~ /^[0-9]+$/) {
        bad = 1
      }
    }
    if ($7 + 0 < 1 || $8 + 0 > $9 + 0 || $10 + 0 > $11 + 0 ||
        $12 + 0 > $13 + 0 || $14 + 0 < 0 || $15 + 0 < 0 ||
        $16 + 0 < 0 || $17 + 0 < 0) {
      bad = 1
    }
  }
  END { exit bad ? 1 : 0 }
' "$WORK_DIR/matrix-size-envelope.csv" || {
  echo "matrix-size-envelope.csv has invalid numeric bounds" >&2
  exit 1
}

awk -F, '
  function numeric_or_empty(value) {
    gsub(/^"|"$/, "", value)
    return value == "" || value ~ /^[0-9]+([.][0-9]+)?([eE][-+]?[0-9]+)?$/
  }
  NR == 1 { next }
  NF != 27 { bad = 1 }
  {
    for (i = 8; i <= 12; i++) {
      if ($i !~ /^[0-9]+$/) {
        bad = 1
      }
    }
    for (i = 13; i <= 20; i++) {
      if (!numeric_or_empty($i)) {
        bad = 1
      }
    }
    if ($21 !~ /^[0-9]+$/) {
      bad = 1
    }
    for (i = 22; i <= 27; i++) {
      if ($i !~ /^[0-9]+$/) {
        bad = 1
      }
    }
  }
  END { exit bad ? 1 : 0 }
' "$WORK_DIR/dense-mathlib-summary.csv" || {
  echo "dense-mathlib-summary.csv has invalid numeric bounds" >&2
  exit 1
}

actual_scaling_cases="$(
  awk -F, 'NR > 1 { sum += $7 } END { print sum + 0 }' \
    "$WORK_DIR/operation-scaling.csv"
)"
assert_eq "operation-scaling case count" "$summary_compiler_records" "$actual_scaling_cases"

awk -F, '
  function numeric_or_empty(value) {
    gsub(/^"|"$/, "", value)
    return value == "" || value ~ /^[0-9]+([.][0-9]+)?([eE][-+]?[0-9]+)?$/
  }
  NR == 1 { next }
  NF != 23 { bad = 1 }
  {
    for (i = 7; i <= 17; i++) {
      if ($i !~ /^[0-9]+([.][0-9]+)?([eE][-+]?[0-9]+)?$/) {
        bad = 1
      }
    }
    if (!numeric_or_empty($18)) {
      bad = 1
    }
    for (i = 19; i <= 20; i++) {
      if ($i !~ /^[0-9]+([.][0-9]+)?([eE][-+]?[0-9]+)?$/) {
        bad = 1
      }
    }
    if (!numeric_or_empty($21) || !numeric_or_empty($23)) {
      bad = 1
    }
    if ($22 !~ /^[0-9]+([.][0-9]+)?([eE][-+]?[0-9]+)?$/) {
      bad = 1
    }
    if ($7 + 0 < 1 || $8 + 0 > $9 + 0 || $10 + 0 > $11 + 0 ||
        $12 + 0 > $13 + 0 || $14 + 0 > $15 + 0) {
      bad = 1
    }
  }
  END { exit bad ? 1 : 0 }
' "$WORK_DIR/operation-scaling.csv" || {
  echo "operation-scaling.csv has invalid numeric bounds" >&2
  exit 1
}

matrix_envelope_max_col() {
  local column="$1"
  awk -F, -v column="$column" '
    NR == 1 { next }
    $column + 0 > max { max = $column + 0 }
    END { print max + 0 }
  ' "$WORK_DIR/matrix-size-envelope.csv"
}

assert_eq "matrix-size max rows" "$(jq -r '.compiler_max_rows' "$WORK_DIR/summary.json")" \
  "$(matrix_envelope_max_col 9)"
assert_eq "matrix-size max cols" "$(jq -r '.compiler_max_cols' "$WORK_DIR/summary.json")" \
  "$(matrix_envelope_max_col 11)"
assert_eq "matrix-size max inner" "$(jq -r '.compiler_max_inner' "$WORK_DIR/summary.json")" \
  "$(matrix_envelope_max_col 13)"
assert_eq "matrix-size max work items" "$(jq -r '.compiler_max_work_items' "$WORK_DIR/summary.json")" \
  "$(matrix_envelope_max_col 14)"
assert_eq "summary compiler_scaling_group_count" \
  "$(jq -r '.compiler_scaling_group_count' "$WORK_DIR/summary.json")" \
  "$expected_size_envelope_groups"
jq -e '
  (.dense_mathlib_median_ratio_max == null or (.dense_mathlib_median_ratio_max | type == "number" and . >= 0)) and
  (.dense_mathlib_p95_ratio_max == null or (.dense_mathlib_p95_ratio_max | type == "number" and . >= 0))
' "$WORK_DIR/summary.json" >/dev/null

jq -n -e \
  --slurpfile compiler "$WORK_DIR/compiler.jsonl" \
  --slurpfile summary "$WORK_DIR/summary.json" \
  --slurpfile quality "$WORK_DIR/measurement-quality.json" \
  --slurpfile process "$WORK_DIR/compiler-process-metrics.json" '
    def sampleCount: ((.samples_ns // []) | length);
    def p95OverMedian:
      if ((.median_ms // 0) == 0) then null else ((.p95_ms // 0) / .median_ms) end;
    def caseShapeOk:
      (.track | type == "string") and
      (.operation | type == "string") and
      (.element | type == "string") and
      (.data_profile | type == "string") and
      (.rows | type == "number" and . >= 0) and
      (.cols | type == "number" and . >= 0) and
      (.inner | type == "number" and . >= 0) and
      (.sample_count | type == "number" and . > 0) and
      (.median_ms | type == "number" and . >= 0) and
      (.p95_ms | type == "number" and . >= 0) and
      (.stddev_ms | type == "number" and . >= 0) and
      (.mad_ms | type == "number" and . >= 0) and
      (.cv | type == "number" and . >= 0);
    $compiler as $all
    | $summary[0] as $s
    | $quality[0] as $q
    | ($all | map(sampleCount)) as $counts
    | ($all | map(.cv // 0)) as $cvs
    | ($all | map(.mad_ms // 0)) as $mads
    | ($all | map(.stddev_ms // 0)) as $stddevs
    | ($all | map(p95OverMedian) | map(select(. != null))) as $p95Ratios
    | ($all | map((.samples_ns // []) | (add // 0)) | add) as $sampleTotalNs
    | ($all | map(select(sampleCount != (.count // -1))) | length) as $declaredMismatches
    | ($all | map(select(sampleCount != (.repeats // -1))) | length) as $repeatMismatches
    | $q.compiler_records == ($all | length) and
      $q.compiler_records == $s.compiler_records and
      $q.compiler_sample_count == ($counts | add) and
      $q.compiler_sample_count == $s.compiler_sample_count and
      $q.compiler_sample_total_ns == $sampleTotalNs and
      $q.compiler_sample_total_ns == $s.compiler_sample_total_ns and
      $q.compiler_sample_total_ms == ($sampleTotalNs / 1000000) and
      $q.compiler_sample_total_ms == $s.compiler_sample_total_ms and
      $q.compiler_sample_total_s == ($sampleTotalNs / 1000000000) and
      $q.compiler_sample_total_s == $s.compiler_sample_total_s and
      $q.compiler_process_elapsed_s == $process[0].elapsed_s and
      $q.compiler_measured_to_elapsed_ratio == $s.compiler_measured_to_elapsed_ratio and
      (if (($process[0].elapsed_s // 0) > 10) then
        (($q.compiler_measured_to_elapsed_ratio // 0) > 0.01)
       else true end) and
      $q.min_samples_per_record == ($counts | min) and
      $q.min_samples_per_record == $s.compiler_min_samples_per_record and
      $q.max_samples_per_record == ($counts | max) and
      $q.max_samples_per_record == $s.compiler_max_samples_per_record and
      $q.sample_count_declared_mismatch_count == $declaredMismatches and
      $q.sample_count_repeat_mismatch_count == $repeatMismatches and
      $q.sample_count_declared_mismatch_count == 0 and
      $q.sample_count_repeat_mismatch_count == 0 and
      $q.records_with_cv_gt_0_05 == ($all | map(select((.cv // 0) > 0.05)) | length) and
      $q.records_with_cv_gt_0_10 == ($all | map(select((.cv // 0) > 0.10)) | length) and
      $q.records_with_cv_gt_0_25 == ($all | map(select((.cv // 0) > 0.25)) | length) and
      $q.records_with_cv_gt_0_50 == ($all | map(select((.cv // 0) > 0.50)) | length) and
      $q.records_with_mad_gt_0 == ($all | map(select((.mad_ms // 0) > 0)) | length) and
      $q.max_cv == ($cvs | max) and
      $q.max_mad_ms == ($mads | max) and
      $q.max_stddev_ms == ($stddevs | max) and
      $q.max_p95_over_median == ($p95Ratios | max) and
      ($q.by_track | type == "array" and length > 0) and
      ($q.by_operation | type == "array" and length > 0) and
      ($q.top_cv_cases | type == "array" and length <= 20) and
      ($q.top_mad_cases | type == "array" and length <= 20) and
      ($q.top_p95_over_median_cases | type == "array" and length <= 20) and
      all($q.top_cv_cases[]; caseShapeOk) and
      all($q.top_mad_cases[]; caseShapeOk) and
      all($q.top_p95_over_median_cases[]; caseShapeOk and (.p95_over_median | type == "number" and . >= 0)) and
      (if ($q.top_cv_cases | length) > 0 then $q.top_cv_cases[0].cv == $q.max_cv else true end) and
      (if ($q.top_mad_cases | length) > 0 then $q.top_mad_cases[0].mad_ms == $q.max_mad_ms else true end) and
      (if ($q.top_p95_over_median_cases | length) > 0 then
        $q.top_p95_over_median_cases[0].p95_over_median == $q.max_p95_over_median
      else true end)
  ' >/dev/null

jq -e '
  ([.compiler_by_track[].track] | sort) ==
  (["compiler_dense","compiler_dense_prebuilt","compiler_mathlib","compiler_mathlib_prebuilt"] | sort)
' "$WORK_DIR/summary.json" >/dev/null

jq -e '
  ([.compiler_by_setup_policy[].setup_policy] | sort) ==
  (["prebuilt_inputs","setup_inclusive"] | sort)
' "$WORK_DIR/summary.json" >/dev/null

jq -e '
  ([.compiler_by_shape_family[].shape_family] | index("square")) != null
' "$WORK_DIR/summary.json" >/dev/null

for shape_family in square zero_rows zero_cols wide tall mul_wide_inner mul_tall_output mul_skinny_inner; do
  jq -e --arg shape_family "$shape_family" '
    ([.compiler_by_shape_family[].shape_family] | index($shape_family)) != null
  ' "$WORK_DIR/summary.json" >/dev/null || {
    echo "missing compiler shape family: $shape_family" >&2
    exit 1
  }
done

required_elements=(Nat Int)
if [[ "$(jq -r '.rat_max_override' "$WORK_DIR/summary.json")" != "0" ]]; then
  required_elements+=(Rat)
fi

for element in "${required_elements[@]}"; do
  jq -e --arg element "$element" '
    ([.compiler_by_element[].element] | index($element)) != null
  ' "$WORK_DIR/summary.json" >/dev/null || {
    echo "missing compiler element family: $element" >&2
    exit 1
  }
done

jq -e '
  .compiler_max_work_items >= 0 and
  ([.compiler_by_work_model[].work_model] | sort) == (["rows_cols","rows_cols_inner"] | sort)
' "$WORK_DIR/summary.json" >/dev/null

jq -e '
  ([.compiler_by_data_profile[].data_profile] | index("deterministic")) != null and
  ([.compiler_by_data_profile[].count] | add) == .compiler_records
' "$WORK_DIR/summary.json" >/dev/null

required_data_profiles=(deterministic)
if jq -e '([.compiler_by_data_profile[].data_profile] | length) > 1' \
  "$WORK_DIR/summary.json" >/dev/null; then
  required_data_profiles+=(zero identity large_magnitude)
fi

for data_profile in "${required_data_profiles[@]}"; do
  jq -e --arg data_profile "$data_profile" '
    ([.compiler_by_data_profile[].data_profile] | index($data_profile)) != null
  ' "$WORK_DIR/summary.json" >/dev/null || {
    echo "missing compiler data profile: $data_profile" >&2
    exit 1
  }
done

require_compiler_operation() {
  local operation="$1"
  awk -F, -v operation="\"$operation\"" '
    NR > 1 && $4 == operation { found = 1 }
    END { exit found ? 0 : 1 }
  ' "$WORK_DIR/compiler-case-manifest.csv" || {
    echo "missing compiler operation: $operation" >&2
    exit 1
  }
}

required_compiler_operations=(
  of
  ofMatrix
  toMatrix
  get
  get!
  set
  set!
  add
  smul
  transpose
  mul_square
  mul_rect
  of_zero_rows
  of_zero_cols
  of_wide
  of_tall
  transpose_wide
  transpose_tall
  mul_wide_inner
  mul_tall_output
  mul_skinny_inner
)
if [[ "$run_profile" == "quick" || "$run_profile" == "full" ]]; then
  required_compiler_operations+=(toString)
fi

for operation in "${required_compiler_operations[@]}"; do
  require_compiler_operation "$operation"
done

require_kernel_operation() {
  local operation="$1"
  jq -s -e --arg operation "$operation" '
    any(.[]; .operation == $operation)
  ' "$WORK_DIR/kernel.jsonl" >/dev/null || {
    echo "missing kernel operation: $operation" >&2
    exit 1
  }
}

required_kernel_operations=(
  import_baseline
  suite
  construction
  conversion
  access_update
  arithmetic
  formatting
  data_profiles
  profile_densematrix_defs
  profile_densematrix_bench
)

for operation in "${required_kernel_operations[@]}"; do
  require_kernel_operation "$operation"
done

awk -F, '
  NR == 1 { next }
  {
    gsub(/"/, "", $10)
    if ($10 != "rows_cols" && $10 != "rows_cols_inner") {
      bad++
    }
    if ($11 < 0) {
      bad++
    }
  }
  END { exit bad == 0 ? 0 : 1 }
' "$WORK_DIR/compiler-throughput.csv" || {
  echo "compiler-throughput.csv has invalid work model or negative work items" >&2
  exit 1
}

if grep -q 'Build completed successfully' "$WORK_DIR/build.log"; then
  :
else
  echo "build log does not show successful build" >&2
  exit 1
fi

if [[ "$(line_count "$WORK_DIR/kernel-compiler-comparison.csv")" -lt 2 ]]; then
  echo "kernel-compiler-comparison.csv has no data rows" >&2
  exit 1
fi
expected_kernel_compiler_header="\"category\",\"kernel_operation\",\"kernel_size\",\"kernel_adjusted_ms\",\"compiler_dense_setup_inclusive_sum_ms\",\"compiler_dense_prebuilt_sum_ms\",\"compiler_setup_missing_count\",\"compiler_prebuilt_missing_count\",\"match_status\",\"notes\""
actual_kernel_compiler_header="$(head -n 1 "$WORK_DIR/kernel-compiler-comparison.csv")"
assert_eq "kernel-compiler-comparison.csv header" "$expected_kernel_compiler_header" "$actual_kernel_compiler_header"
expected_kernel_compiler_rows="$(
  jq -s '
    (map(select(.track == "kernel" and .operation == "suite")) | length) + 6
  ' "$WORK_DIR/kernel.jsonl"
)"
assert_eq "kernel-compiler-comparison.csv line count" "$((expected_kernel_compiler_rows + 1))" \
  "$(line_count "$WORK_DIR/kernel-compiler-comparison.csv")"
awk -F, '
  function numeric_or_empty(value) {
    gsub(/^"|"$/, "", value)
    return value == "" || value ~ /^[0-9]+([.][0-9]+)?([eE][-+]?[0-9]+)?$/
  }
  NR == 1 { next }
  NF != 10 { bad = 1 }
  {
    status = $9
    gsub(/^"|"$/, "", status)
    if ($3 !~ /^[0-9]+$/ || !numeric_or_empty($4) || !numeric_or_empty($5) ||
        !numeric_or_empty($6) || $7 !~ /^[0-9]+$/ || $8 !~ /^[0-9]+$/) {
      bad = 1
    }
    if (status != "exact_compiler_match" && status != "missing_compiler_match") {
      bad = 1
    }
  }
  END { exit bad ? 1 : 0 }
' "$WORK_DIR/kernel-compiler-comparison.csv" || {
  echo "kernel-compiler-comparison.csv has invalid rows" >&2
  exit 1
}
while IFS= read -r size; do
  awk -F, -v size="$size" '
    NR > 1 {
      category = $1
      gsub(/^"|"$/, "", category)
      if (category == "suite" && $3 == size) {
        found = 1
      }
    }
    END { exit found ? 0 : 1 }
  ' "$WORK_DIR/kernel-compiler-comparison.csv" || {
    echo "kernel-compiler-comparison.csv missing suite size: $size" >&2
    exit 1
  }
done < <(jq -r 'select(.track == "kernel" and .operation == "suite") | .size' "$WORK_DIR/kernel.jsonl" | sort -n)

override_at_least() {
  local value="$1"
  local threshold="$2"
  if [[ "$value" == "default" ]]; then
    return 0
  fi
  [[ "$value" =~ ^[0-9]+$ ]] && [[ "$value" -ge "$threshold" ]]
}

compiler_has_square_size() {
  local size="$1"
  jq -s -e --argjson size "$size" '
    any(.[]; .rows == $size and .cols == $size)
  ' "$WORK_DIR/compiler.jsonl" >/dev/null
}

kernel_comparison_exact() {
  local category="$1"
  local size="$2"
  awk -F, -v category="$category" -v size="$size" '
    NR > 1 {
      row_category = $1
      status = $9
      gsub(/^"|"$/, "", row_category)
      gsub(/^"|"$/, "", status)
      if (row_category == category && $3 == size) {
        found = 1
        if ($7 + 0 != 0 || $8 + 0 != 0 || status != "exact_compiler_match") {
          bad = 1
        }
      }
    }
    END { exit found && !bad ? 0 : 1 }
  ' "$WORK_DIR/kernel-compiler-comparison.csv"
}

require_kernel_comparison_exact() {
  local category="$1"
  local size="$2"
  kernel_comparison_exact "$category" "$size" || {
    echo "kernel-compiler-comparison.csv missing exact match for $category size $size" >&2
    exit 1
  }
}

rat_override="$(jq -r '.compiler.rat_max_override' "$WORK_DIR/run-config.json")"
string_override="$(jq -r '.compiler.string_max_override' "$WORK_DIR/run-config.json")"
data_override="$(jq -r '.compiler.data_max_override' "$WORK_DIR/run-config.json")"

if override_at_least "$rat_override" 2 && override_at_least "$string_override" 2 &&
    compiler_has_square_size 2; then
  for category in suite construction conversion access_update arithmetic formatting; do
    require_kernel_comparison_exact "$category" 2
  done
  if override_at_least "$data_override" 2; then
    require_kernel_comparison_exact data_profiles 2
  fi
fi

while IFS= read -r size; do
  if override_at_least "$rat_override" "$size" && override_at_least "$string_override" "$size" &&
      compiler_has_square_size "$size"; then
    require_kernel_comparison_exact suite "$size"
  fi
done < <(jq -r 'select(.track == "kernel" and .operation == "suite") | .size' \
  "$WORK_DIR/kernel.jsonl" | sort -n)

expected_kernel_profile_header="\"profile_case\",\"metric\",\"ms\""
actual_kernel_profile_header="$(head -n 1 "$WORK_DIR/kernel-profile-summary.csv")"
assert_eq "kernel-profile-summary.csv header" "$expected_kernel_profile_header" "$actual_kernel_profile_header"
if [[ "$(line_count "$WORK_DIR/kernel-profile-summary.csv")" -lt 8 ]]; then
  echo "kernel-profile-summary.csv has too few data rows" >&2
  exit 1
fi
awk -F, '
  NR == 1 { next }
  NF != 3 { bad = 1 }
  {
    metric = $2
    gsub(/^"|"$/, "", metric)
    profile = $1
    gsub(/^"|"$/, "", profile)
    if (profile != "profile_densematrix_defs" && profile != "profile_densematrix_bench") {
      bad = 1
    }
    if (metric == "") {
      bad = 1
    }
    if ($3 !~ /^[0-9]+([.][0-9]+)?$/) {
      bad = 1
    }
  }
  END { exit bad ? 1 : 0 }
' "$WORK_DIR/kernel-profile-summary.csv" || {
  echo "kernel-profile-summary.csv has invalid rows" >&2
  exit 1
}

require_kernel_profile_metric() {
  local profile_case="$1"
  local metric="$2"
  awk -F, -v profile_case="\"$profile_case\"" -v metric="\"$metric\"" '
    NR > 1 && $1 == profile_case && $2 == metric { found = 1 }
    END { exit found ? 0 : 1 }
  ' "$WORK_DIR/kernel-profile-summary.csv" || {
    echo "missing kernel profile metric: $profile_case / $metric" >&2
    exit 1
  }
}

for profile_case in profile_densematrix_defs profile_densematrix_bench; do
  for metric in import_took elaboration "typeclass inference" "type checking"; do
    require_kernel_profile_metric "$profile_case" "$metric"
  done
done

while IFS=$'\t' read -r track operation size; do
  [[ -n "$track" ]] || continue
  case "$track" in
    kernel)
      if [[ "$operation" == "import_baseline" ]]; then
        stem="$WORK_DIR/kernel/import_baseline"
      else
        stem="$WORK_DIR/kernel/${operation}_${size}"
      fi
      ;;
    kernel_profile)
      stem="$WORK_DIR/kernel/${operation}"
      ;;
    *)
      echo "unexpected kernel track: $track" >&2
      exit 1
      ;;
  esac
  require_file "$stem.time"
  require_file "$stem.stdout"
  require_file "$stem.stderr"
done < <(jq -r '[.track, .operation, (.size | tostring)] | @tsv' "$WORK_DIR/kernel.jsonl")

if ! grep -q '== pinned probe ==' "$WORK_DIR/pinning-preflight.txt"; then
  echo "pinning-preflight.txt does not include pinned probe evidence" >&2
  exit 1
fi

if ! grep -q '== pinned probe ==' "$WORK_DIR/pinning-postflight.txt"; then
  echo "pinning-postflight.txt does not include pinned probe evidence" >&2
  exit 1
fi

pinned_cpu_list() {
  awk '
    /^== pinned probe ==$/ { in_probe = 1; next }
    in_probe && /^Cpus_allowed_list:/ {
      sub(/^Cpus_allowed_list:[[:space:]]*/, "")
      print
      exit
    }
  ' "$1"
}

preflight_cpu_list="$(pinned_cpu_list "$WORK_DIR/pinning-preflight.txt")"
postflight_cpu_list="$(pinned_cpu_list "$WORK_DIR/pinning-postflight.txt")"

assert_eq "preflight pinned CPU list" "$summary_core" "$preflight_cpu_list"
assert_eq "postflight pinned CPU list" "$summary_core" "$postflight_cpu_list"

current_processor_bad_count() {
  awk -v core="$summary_core" '
    /^== pinned probe ==$/ { in_probe = 1; next }
    in_probe && /^current_processor=/ {
      sub(/^current_processor=/, "")
      seen++
      if ($0 != core) {
        bad++
      }
    }
    END {
      if (seen == 0) {
        print "missing"
      } else {
        print bad + 0
      }
    }
  ' "$1"
}

assert_eq "preflight current processor samples" "0" \
  "$(current_processor_bad_count "$WORK_DIR/pinning-preflight.txt")"
assert_eq "postflight current processor samples" "0" \
  "$(current_processor_bad_count "$WORK_DIR/pinning-postflight.txt")"

echo "verified DenseMatrix benchmark bundle: $WORK_DIR"
