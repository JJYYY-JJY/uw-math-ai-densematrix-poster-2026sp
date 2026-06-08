#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

THRESHOLD="1.25"
OUT=""
ALLOW_CONFIG_MISMATCH=0

usage() {
  cat <<'USAGE'
Usage: scripts/compare_densematrix_bench.sh [options] BASELINE_BUNDLE CURRENT_BUNDLE

Compares two DenseMatrix benchmark bundles produced by run_densematrix_bench.sh.
Both directory bundles and .tar.gz archives are accepted.

Options:
  --threshold R        Regression ratio threshold for current/baseline (default: 1.25).
  --out FILE           Write comparison CSV to FILE instead of stdout.
  --allow-config-mismatch
                       Compare bundles even when run-config.json settings differ.
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

write_size_envelope_summary_json() {
  local input="$1"
  local output="$2"
  jq -Rn '
    [inputs][1:]
    | map(split(","))
    | map({
        case_count: (.[6] | tonumber),
        max_rows: (.[8] | tonumber),
        max_cols: (.[10] | tonumber),
        max_inner: (.[12] | tonumber),
        max_work_items: (.[13] | tonumber),
        max_output_cells: (.[14] | tonumber),
        max_input_cells: (.[15] | tonumber),
        max_total_matrix_cells: (.[16] | tonumber)
      })
    | {
        group_count: length,
        total_case_count: (map(.case_count) | add),
        max_rows: (map(.max_rows) | max),
        max_cols: (map(.max_cols) | max),
        max_inner: (map(.max_inner) | max),
        max_work_items: (map(.max_work_items) | max),
        max_output_cells: (map(.max_output_cells) | max),
        max_input_cells: (map(.max_input_cells) | max),
        max_total_matrix_cells: (map(.max_total_matrix_cells) | max)
      }
  ' <"$input" >"$output"
}

write_dense_mathlib_summary_json() {
  local input="$1"
  local output="$2"
  jq -Rn '
    def clean: gsub("^\"|\"$"; "");
    def num:
      clean as $value
      | if $value == "" then null else ($value | tonumber) end;
    [inputs][1:]
    | map(split(","))
    | map({
        pair_count: (.[7] | tonumber),
        max_work_items: (.[11] | tonumber),
        median_ratio_max: (.[15] | num),
        p95_ratio_max: (.[19] | num),
        checksum_mismatch_count: (.[20] | tonumber)
      })
    | {
        group_count: length,
        total_pair_count: (map(.pair_count) | add),
        max_work_items: (map(.max_work_items) | max),
        max_median_ratio: (map(.median_ratio_max) | map(select(. != null)) | max),
        max_p95_ratio: (map(.p95_ratio_max) | map(select(. != null)) | max),
        checksum_mismatch_count: (map(.checksum_mismatch_count) | add)
      }
  ' <"$input" >"$output"
}

write_operation_scaling_summary_json() {
  local input="$1"
  local output="$2"
  jq -Rn '
    def clean: gsub("^\"|\"$"; "");
    def num:
      clean as $value
      | if $value == "" then null else ($value | tonumber) end;
    [inputs][1:]
    | map(split(","))
    | map({
        case_count: (.[6] | tonumber),
        max_work_items: (.[8] | tonumber),
        median_growth_ratio: (.[17] | num),
        p95_growth_ratio: (.[20] | num),
        max_cv: (.[21] | num),
        max_p95_over_median: (.[22] | num)
      })
    | {
        group_count: length,
        total_case_count: (map(.case_count) | add),
        max_work_items: (map(.max_work_items) | max),
        max_median_growth_ratio: (map(.median_growth_ratio) | map(select(. != null)) | max),
        max_p95_growth_ratio: (map(.p95_growth_ratio) | map(select(. != null)) | max),
        max_cv: (map(.max_cv) | map(select(. != null)) | max),
        max_p95_over_median: (map(.max_p95_over_median) | map(select(. != null)) | max)
      }
  ' <"$input" >"$output"
}

write_kernel_profile_summary_json() {
  local input="$1"
  local output="$2"
  jq -Rn '
    [inputs][1:]
    | map(split(","))
    | map({
        profile_case: (.[0] | gsub("^\"|\"$"; "")),
        metric: (.[1] | gsub("^\"|\"$"; "")),
        ms: (.[2] | tonumber)
      })
    | map({key: "\(.profile_case)|\(.metric)", value: .})
    | from_entries
  ' <"$input" >"$output"
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --threshold)
      THRESHOLD="${2:?--threshold requires a value}"
      shift 2
      ;;
    --out)
      OUT="${2:?--out requires a value}"
      shift 2
      ;;
    --allow-config-mismatch)
      ALLOW_CONFIG_MISMATCH=1
      shift
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

if [[ $# -ne 2 ]]; then
  usage >&2
  exit 2
fi

need_cmd jq
need_cmd tar
need_cmd awk
need_cmd "$ROOT/scripts/verify_densematrix_bench.sh"

if ! jq -n --argjson threshold "$THRESHOLD" '$threshold | numbers' >/dev/null; then
  echo "--threshold must be numeric: $THRESHOLD" >&2
  exit 2
fi

BASE_INPUT="$1"
CURRENT_INPUT="$2"

"$ROOT/scripts/verify_densematrix_bench.sh" "$BASE_INPUT" >/dev/null
"$ROOT/scripts/verify_densematrix_bench.sh" "$CURRENT_INPUT" >/dev/null

BASE_DIR=""
CURRENT_DIR=""
resolve_bundle "$BASE_INPUT" BASE_DIR
resolve_bundle "$CURRENT_INPUT" CURRENT_DIR

if [[ "$ALLOW_CONFIG_MISMATCH" -eq 0 ]]; then
  config_mismatch="$(
    jq -n -r \
      --slurpfile base "$BASE_DIR/run-config.json" \
      --slurpfile current "$CURRENT_DIR/run-config.json" '
      def fields:
        [
          ["profile", .profile],
          ["mode_flags.quick", .mode_flags.quick],
          ["mode_flags.stress", .mode_flags.stress],
          ["mode_flags.xl", .mode_flags.xl],
          ["mode_flags.mega", .mode_flags.mega],
          ["core", .core],
          ["pin_command", .pin_command],
          ["compiler.sizes_override", .compiler.sizes_override],
          ["compiler.repeats_override", .compiler.repeats_override],
          ["compiler.warmups_override", .compiler.warmups_override],
          ["compiler.rat_max_override", .compiler.rat_max_override],
          ["compiler.string_max_override", .compiler.string_max_override],
          ["compiler.data_max_override", .compiler.data_max_override],
          ["pkexec_timeout_seconds", .pkexec_timeout_seconds],
          ["kernel.sizes_effective", .kernel.sizes_effective]
        ];
      (($base[0] | fields) as $baseFields
        | ($current[0] | fields) as $currentFields
        | [range(0; $baseFields | length) as $i
            | select($baseFields[$i][1] != $currentFields[$i][1])
            | "\($baseFields[$i][0]): baseline=\($baseFields[$i][1]) current=\($currentFields[$i][1])"])
      | .[]
    '
  )"
  if [[ -n "$config_mismatch" ]]; then
    echo "comparison refused: benchmark run configs differ" >&2
    echo "$config_mismatch" >&2
    echo "rerun with --allow-config-mismatch to compare anyway" >&2
    exit 1
  fi
fi

RUN_TMP="$(mktemp -d)"
TMP_DIRS+=("$RUN_TMP")
CSV_TMP="$RUN_TMP/compare.csv"
BASE_SIZE_SUMMARY="$RUN_TMP/base-size-envelope-summary.json"
CURRENT_SIZE_SUMMARY="$RUN_TMP/current-size-envelope-summary.json"
BASE_DENSE_SUMMARY="$RUN_TMP/base-dense-mathlib-summary.json"
CURRENT_DENSE_SUMMARY="$RUN_TMP/current-dense-mathlib-summary.json"
BASE_SCALING_SUMMARY="$RUN_TMP/base-operation-scaling-summary.json"
CURRENT_SCALING_SUMMARY="$RUN_TMP/current-operation-scaling-summary.json"
BASE_KERNEL_PROFILE="$RUN_TMP/base-kernel-profile-summary.json"
CURRENT_KERNEL_PROFILE="$RUN_TMP/current-kernel-profile-summary.json"
write_size_envelope_summary_json "$BASE_DIR/matrix-size-envelope.csv" "$BASE_SIZE_SUMMARY"
write_size_envelope_summary_json "$CURRENT_DIR/matrix-size-envelope.csv" "$CURRENT_SIZE_SUMMARY"
write_dense_mathlib_summary_json "$BASE_DIR/dense-mathlib-summary.csv" "$BASE_DENSE_SUMMARY"
write_dense_mathlib_summary_json "$CURRENT_DIR/dense-mathlib-summary.csv" "$CURRENT_DENSE_SUMMARY"
write_operation_scaling_summary_json "$BASE_DIR/operation-scaling.csv" "$BASE_SCALING_SUMMARY"
write_operation_scaling_summary_json "$CURRENT_DIR/operation-scaling.csv" "$CURRENT_SCALING_SUMMARY"
write_kernel_profile_summary_json "$BASE_DIR/kernel-profile-summary.csv" "$BASE_KERNEL_PROFILE"
write_kernel_profile_summary_json "$CURRENT_DIR/kernel-profile-summary.csv" "$CURRENT_KERNEL_PROFILE"

jq -n -r \
  --argjson threshold "$THRESHOLD" \
  --slurpfile baseCompiler "$BASE_DIR/compiler.jsonl" \
  --slurpfile currentCompiler "$CURRENT_DIR/compiler.jsonl" \
  --slurpfile baseKernel "$BASE_DIR/kernel.jsonl" \
  --slurpfile currentKernel "$CURRENT_DIR/kernel.jsonl" \
  --slurpfile baseProcess "$BASE_DIR/compiler-process-metrics.json" \
  --slurpfile currentProcess "$CURRENT_DIR/compiler-process-metrics.json" \
  --slurpfile baseQuality "$BASE_DIR/measurement-quality.json" \
  --slurpfile currentQuality "$CURRENT_DIR/measurement-quality.json" \
  --slurpfile baseSize "$BASE_SIZE_SUMMARY" \
  --slurpfile currentSize "$CURRENT_SIZE_SUMMARY" \
  --slurpfile baseDenseSummary "$BASE_DENSE_SUMMARY" \
  --slurpfile currentDenseSummary "$CURRENT_DENSE_SUMMARY" \
  --slurpfile baseScalingSummary "$BASE_SCALING_SUMMARY" \
  --slurpfile currentScalingSummary "$CURRENT_SCALING_SUMMARY" \
  --slurpfile baseKernelProfile "$BASE_KERNEL_PROFILE" \
  --slurpfile currentKernelProfile "$CURRENT_KERNEL_PROFILE" \
  --slurpfile baseExecutable "$BASE_DIR/executable-artifact.json" \
  --slurpfile currentExecutable "$CURRENT_DIR/executable-artifact.json" \
  --slurpfile baseEnv "$BASE_DIR/benchmark-env.json" \
  --slurpfile currentEnv "$CURRENT_DIR/benchmark-env.json" \
  --slurpfile baseManifest "$BASE_DIR/bundle-manifest.json" \
  --slurpfile currentManifest "$CURRENT_DIR/bundle-manifest.json" '
  def dataProfile: (.data_profile // "deterministic");
  def compilerKey:
    "\(.track)|\(.operation)|\(.element)|\(dataProfile)|\(.rows)|\(.cols)|\(.inner)";
  def kernelKey:
    "\(.track)|\(.operation)|\(.size)";
  def valueRatio($base; $current):
    if $base == null or $current == null or $base == 0 then "" else ($current / $base) end;
  def status($base; $current):
    if $base == null then "missing_baseline"
    elif $current == null then "missing_current"
    elif $base == 0 and $current == 0 then "ok"
    elif $base == 0 then "baseline_zero"
    elif ($current / $base) > $threshold then "regression"
    elif ($current / $base) < (1 / $threshold) then "speedup"
    else "ok" end;
  def auditStatus($base; $current):
    if $base == null then "missing_baseline"
    elif $current == null then "missing_current"
    else "audit" end;
  def coverageStatus($base; $current):
    if $base == null then "missing_baseline"
    elif $current == null then "missing_current"
    elif $current < $base then "coverage_loss"
    elif $current > $base then "coverage_gain"
    else "ok" end;
  def compilerRows:
    ($baseCompiler | map({key: compilerKey, value: .}) | from_entries) as $baseMap
    | ($currentCompiler | map({key: compilerKey, value: .}) | from_entries) as $currentMap
    | (($baseMap | keys) + ($currentMap | keys) | unique[]) as $key
    | ($baseMap[$key] // null) as $base
    | ($currentMap[$key] // null) as $current
    | ($base // $current) as $meta
    | [
        "compiler",
        "median_ms",
        $meta.track,
        $meta.operation,
        $meta.element,
        ($meta.data_profile // "deterministic"),
        $meta.rows,
        $meta.cols,
        $meta.inner,
        (if $base == null then "" else $base.median_ms end),
        (if $current == null then "" else $current.median_ms end),
        valueRatio((if $base == null then null else $base.median_ms end);
          (if $current == null then null else $current.median_ms end)),
        status((if $base == null then null else $base.median_ms end);
          (if $current == null then null else $current.median_ms end))
      ],
      [
        "compiler",
        "p95_ms",
        $meta.track,
        $meta.operation,
        $meta.element,
        ($meta.data_profile // "deterministic"),
        $meta.rows,
        $meta.cols,
        $meta.inner,
        (if $base == null then "" else $base.p95_ms end),
        (if $current == null then "" else $current.p95_ms end),
        valueRatio((if $base == null then null else $base.p95_ms end);
          (if $current == null then null else $current.p95_ms end)),
        status((if $base == null then null else $base.p95_ms end);
          (if $current == null then null else $current.p95_ms end))
      ];
  def kernelRows:
    ($baseKernel | map({key: kernelKey, value: .}) | from_entries) as $baseMap
    | ($currentKernel | map({key: kernelKey, value: .}) | from_entries) as $currentMap
    | (($baseMap | keys) + ($currentMap | keys) | unique[]) as $key
    | ($baseMap[$key] // null) as $base
    | ($currentMap[$key] // null) as $current
    | ($base // $current) as $meta
    | [
        "kernel",
        "adjusted_ms",
        $meta.track,
        $meta.operation,
        "",
        "",
        "",
        "",
        $meta.size,
        (if $base == null then "" else ($base.adjusted_s * 1000) end),
        (if $current == null then "" else ($current.adjusted_s * 1000) end),
        valueRatio((if $base == null then null else ($base.adjusted_s * 1000) end);
          (if $current == null then null else ($current.adjusted_s * 1000) end)),
        status((if $base == null then null else ($base.adjusted_s * 1000) end);
          (if $current == null then null else ($current.adjusted_s * 1000) end))
      ];
  def kernelProfileRows:
    $baseKernelProfile[0] as $baseMap
    | $currentKernelProfile[0] as $currentMap
    | (($baseMap | keys) + ($currentMap | keys) | unique[]) as $key
    | ($baseMap[$key] // null) as $base
    | ($currentMap[$key] // null) as $current
    | ($base // $current) as $meta
    | [
        "kernel_profile",
        $meta.metric,
        $meta.profile_case,
        "lean_profile",
        "",
        "",
        "",
        "",
        "",
        (if $base == null then "" else $base.ms end),
        (if $current == null then "" else $current.ms end),
        valueRatio((if $base == null then null else $base.ms end);
          (if $current == null then null else $current.ms end)),
        status((if $base == null then null else $base.ms end);
          (if $current == null then null else $current.ms end))
      ];
  def processMetricRow($metric; $statusPolicy):
    ($baseProcess[0][$metric] // null) as $base
    | ($currentProcess[0][$metric] // null) as $current
    | [
        "process",
        $metric,
        "compiler_process",
        "",
        "",
        "",
        "",
        "",
        "",
        (if $base == null then "" else $base end),
        (if $current == null then "" else $current end),
        valueRatio($base; $current),
        (if $statusPolicy == "threshold" then status($base; $current) else auditStatus($base; $current) end)
      ];
  def processRows:
    processMetricRow("elapsed_s"; "threshold"),
    processMetricRow("user_s"; "threshold"),
    processMetricRow("system_s"; "threshold"),
    processMetricRow("max_rss_kb"; "threshold"),
    processMetricRow("major_page_faults"; "audit"),
    processMetricRow("minor_page_faults"; "audit"),
    processMetricRow("voluntary_context_switches"; "audit"),
    processMetricRow("involuntary_context_switches"; "audit"),
    processMetricRow("file_system_inputs"; "audit"),
    processMetricRow("file_system_outputs"; "audit");
  def executableNumericRow($metric):
    ($baseExecutable[0][$metric] // null) as $base
    | ($currentExecutable[0][$metric] // null) as $current
    | [
        "executable_artifact",
        $metric,
        "densematrix_bench",
        "",
        "",
        "",
        "",
        "",
        "",
        (if $base == null then "" else $base end),
        (if $current == null then "" else $current end),
        valueRatio($base; $current),
        auditStatus($base; $current)
      ];
  def executableStringRow($metric):
    ($baseExecutable[0][$metric] // null) as $base
    | ($currentExecutable[0][$metric] // null) as $current
    | [
        "executable_artifact",
        $metric,
        "densematrix_bench",
        "",
        "",
        "",
        "",
        "",
        "",
        (if $base == null then "" else $base end),
        (if $current == null then "" else $current end),
        "",
        auditStatus($base; $current)
      ];
  def executableRows:
    executableStringRow("path"),
    executableNumericRow("bytes"),
    executableStringRow("sha256");
  def envTopLevelRow($metric):
    ($baseEnv[0][$metric] // null) as $base
    | ($currentEnv[0][$metric] // null) as $current
    | [
        "benchmark_env",
        $metric,
        "allowlisted_environment",
        "",
        "",
        "",
        "",
        "",
        "",
        (if $base == null then "" else $base end),
        (if $current == null then "" else $current end),
        "",
        auditStatus($base; $current)
      ];
  def envVariableRow($key):
    ($baseEnv[0].variables | has($key)) as $baseHas
    | ($currentEnv[0].variables | has($key)) as $currentHas
    | (if $baseHas then ($baseEnv[0].variables[$key] // "(unset)") else null end) as $base
    | (if $currentHas then ($currentEnv[0].variables[$key] // "(unset)") else null end) as $current
    | [
        "benchmark_env",
        $key,
        "allowlisted_environment",
        "variable",
        "",
        "",
        "",
        "",
        "",
        (if $base == null then "" else $base end),
        (if $current == null then "" else $current end),
        "",
        auditStatus($base; $current)
      ];
  def envCountRow($metric; $field):
    ($baseEnv[0][$field] // []) as $baseList
    | ($currentEnv[0][$field] // []) as $currentList
    | [
        "benchmark_env",
        $metric,
        "allowlisted_environment",
        "",
        "",
        "",
        "",
        "",
        "",
        ($baseList | length),
        ($currentList | length),
        valueRatio(($baseList | length); ($currentList | length)),
        auditStatus(($baseList | length); ($currentList | length))
      ];
  def envRows:
    envTopLevelRow("path_sha256"),
    envCountRow("present_key_count"; "present_keys"),
    envCountRow("absent_key_count"; "absent_keys"),
    envVariableRow("LANG"),
    envVariableRow("LC_ALL"),
    envVariableRow("TZ"),
    envVariableRow("LEAN_PATH"),
    envVariableRow("LD_LIBRARY_PATH"),
    envVariableRow("LD_PRELOAD"),
    envVariableRow("MALLOC_ARENA_MAX"),
    envVariableRow("OMP_NUM_THREADS"),
    envVariableRow("OPENBLAS_NUM_THREADS"),
    envVariableRow("MKL_NUM_THREADS");
  def qualityMetricRow($metric; $statusPolicy):
    ($baseQuality[0][$metric] // null) as $base
    | ($currentQuality[0][$metric] // null) as $current
    | [
        "measurement_quality",
        $metric,
        "compiler_noise",
        "",
        "",
        "",
        "",
        "",
        "",
        (if $base == null then "" else $base end),
        (if $current == null then "" else $current end),
        valueRatio($base; $current),
        (if $statusPolicy == "threshold" then status($base; $current)
         elif $statusPolicy == "coverage" then coverageStatus($base; $current)
         else auditStatus($base; $current) end)
      ];
  def qualityRows:
    qualityMetricRow("compiler_records"; "coverage"),
    qualityMetricRow("compiler_sample_count"; "coverage"),
    qualityMetricRow("compiler_sample_total_s"; "coverage"),
    qualityMetricRow("compiler_process_elapsed_s"; "audit"),
    qualityMetricRow("compiler_measured_to_elapsed_ratio"; "coverage"),
    qualityMetricRow("min_samples_per_record"; "coverage"),
    qualityMetricRow("max_samples_per_record"; "coverage"),
    qualityMetricRow("sample_count_declared_mismatch_count"; "threshold"),
    qualityMetricRow("sample_count_repeat_mismatch_count"; "threshold"),
    qualityMetricRow("records_with_cv_gt_0_10"; "threshold"),
    qualityMetricRow("records_with_cv_gt_0_25"; "threshold"),
    qualityMetricRow("records_with_cv_gt_0_50"; "threshold"),
    qualityMetricRow("max_cv"; "threshold"),
    qualityMetricRow("max_mad_ms"; "threshold"),
    qualityMetricRow("max_stddev_ms"; "threshold");
  def sizeMetricRow($metric):
    ($baseSize[0][$metric] // null) as $base
    | ($currentSize[0][$metric] // null) as $current
    | [
        "size_envelope",
        $metric,
        "compiler_coverage",
        "",
        "",
        "",
        "",
        "",
        "",
        (if $base == null then "" else $base end),
        (if $current == null then "" else $current end),
        valueRatio($base; $current),
        coverageStatus($base; $current)
      ];
  def sizeRows:
    sizeMetricRow("group_count"),
    sizeMetricRow("total_case_count"),
    sizeMetricRow("max_rows"),
    sizeMetricRow("max_cols"),
    sizeMetricRow("max_inner"),
    sizeMetricRow("max_work_items"),
    sizeMetricRow("max_output_cells"),
    sizeMetricRow("max_input_cells"),
    sizeMetricRow("max_total_matrix_cells");
  def denseSummaryMetricRow($metric; $statusPolicy):
    ($baseDenseSummary[0][$metric] // null) as $base
    | ($currentDenseSummary[0][$metric] // null) as $current
    | [
        "dense_mathlib_summary",
        $metric,
        "pair_ratio_summary",
        "",
        "",
        "",
        "",
        "",
        "",
        (if $base == null then "" else $base end),
        (if $current == null then "" else $current end),
        valueRatio($base; $current),
        (if $statusPolicy == "coverage" then coverageStatus($base; $current)
         elif $statusPolicy == "threshold" then status($base; $current)
         else auditStatus($base; $current) end)
      ];
  def denseSummaryRows:
    denseSummaryMetricRow("group_count"; "coverage"),
    denseSummaryMetricRow("total_pair_count"; "coverage"),
    denseSummaryMetricRow("max_work_items"; "coverage"),
    denseSummaryMetricRow("max_median_ratio"; "threshold"),
    denseSummaryMetricRow("max_p95_ratio"; "threshold"),
    denseSummaryMetricRow("checksum_mismatch_count"; "threshold");
  def scalingSummaryMetricRow($metric; $statusPolicy):
    ($baseScalingSummary[0][$metric] // null) as $base
    | ($currentScalingSummary[0][$metric] // null) as $current
    | [
        "operation_scaling",
        $metric,
        "scaling_summary",
        "",
        "",
        "",
        "",
        "",
        "",
        (if $base == null then "" else $base end),
        (if $current == null then "" else $current end),
        valueRatio($base; $current),
        (if $statusPolicy == "coverage" then coverageStatus($base; $current)
         elif $statusPolicy == "threshold" then status($base; $current)
         else auditStatus($base; $current) end)
      ];
  def scalingSummaryRows:
    scalingSummaryMetricRow("group_count"; "coverage"),
    scalingSummaryMetricRow("total_case_count"; "coverage"),
    scalingSummaryMetricRow("max_work_items"; "coverage"),
    scalingSummaryMetricRow("max_median_growth_ratio"; "threshold"),
    scalingSummaryMetricRow("max_p95_growth_ratio"; "threshold"),
    scalingSummaryMetricRow("max_cv"; "threshold"),
    scalingSummaryMetricRow("max_p95_over_median"; "threshold");
  def roleCountMap($items):
    ($items | group_by(.role) | map({key: .[0].role, value: length}) | from_entries);
  def roleBytesMap($items):
    ($items | group_by(.role) | map({key: .[0].role, value: (map(.bytes) | add)}) | from_entries);
  def manifestRow($metric; $role; $base; $current; $statusPolicy):
    [
      "bundle_manifest",
      $metric,
      "package_inventory",
      $role,
      "",
      "",
      "",
      "",
      "",
      (if $base == null then "" else $base end),
      (if $current == null then "" else $current end),
      valueRatio($base; $current),
      (if $statusPolicy == "coverage" then coverageStatus($base; $current)
       else auditStatus($base; $current) end)
    ];
  def manifestRows:
    ($baseManifest[0] // []) as $baseItems
    | ($currentManifest[0] // []) as $currentItems
    | (roleCountMap($baseItems)) as $baseRoleCounts
    | (roleCountMap($currentItems)) as $currentRoleCounts
    | (roleBytesMap($baseItems)) as $baseRoleBytes
    | (roleBytesMap($currentItems)) as $currentRoleBytes
    | ((
        manifestRow("file_count"; "all"; ($baseItems | length); ($currentItems | length); "coverage"),
        manifestRow("total_bytes"; "all"; ($baseItems | map(.bytes) | add); ($currentItems | map(.bytes) | add); "audit")
      ),
      ((($baseRoleCounts | keys) + ($currentRoleCounts | keys) | unique[]) as $role
        | manifestRow("role_count"; $role; ($baseRoleCounts[$role] // null); ($currentRoleCounts[$role] // null); "coverage")),
      ((($baseRoleBytes | keys) + ($currentRoleBytes | keys) | unique[]) as $role
        | manifestRow("role_bytes"; $role; ($baseRoleBytes[$role] // null); ($currentRoleBytes[$role] // null); "audit")));
  ["suite","metric","track","operation","element","data_profile","rows","cols","inner_or_size",
    "baseline","current","ratio","status"],
  compilerRows,
  kernelRows,
  kernelProfileRows,
  processRows,
  executableRows,
  envRows,
  qualityRows,
  sizeRows,
  denseSummaryRows,
  scalingSummaryRows,
  manifestRows
  | @csv
' >"$CSV_TMP"

if [[ -n "$OUT" ]]; then
  cp "$CSV_TMP" "$OUT"
else
  cat "$CSV_TMP"
fi

summary="$(
  awk -F, '
    NR == 1 { next }
    {
      gsub(/"/, "", $13)
      counts[$13]++
      total++
    }
    END {
      printf("rows=%d", total)
      for (status in counts) {
        printf(" %s=%d", status, counts[status])
      }
      printf("\n")
    }
  ' "$CSV_TMP"
)"
echo "comparison summary: $summary" >&2

bad_count="$(
  awk -F, '
    NR == 1 { next }
    {
      gsub(/"/, "", $13)
      if ($13 == "regression" || $13 == "missing_baseline" || $13 == "missing_current" ||
          $13 == "baseline_zero" || $13 == "coverage_loss") {
        bad++
      }
    }
    END { print bad + 0 }
  ' "$CSV_TMP"
)"

if [[ "$bad_count" != "0" ]]; then
  echo "comparison failed: $bad_count regression or missing-key rows exceeded policy" >&2
  exit 1
fi
