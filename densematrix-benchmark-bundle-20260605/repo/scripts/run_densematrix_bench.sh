#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

ORIGINAL_ARGS=("$@")

QUICK=0
STRESS=0
XL=0
MEGA=0
INSTALL_TOOLS=0
TUNE_SYSTEM=0
CORE=2
REPEATS=""
WARMUPS=""
SIZES=""
RAT_MAX=""
STRING_MAX=""
DATA_MAX=""
KERNEL_SIZES=""
OUT_PARENT="bench-results"
PKEXEC_TIMEOUT_SECONDS="${PKEXEC_TIMEOUT_SECONDS:-60}"

usage() {
  cat <<'USAGE'
Usage: scripts/run_densematrix_bench.sh [options]

Options:
  --quick              Short validation run.
  --stress             Large runtime run: sizes 2,3,4,128,192,256; repeats 5; Rat bridge <=4.
  --xl                 XL runtime run: sizes 2,3,4,256,384,512; repeats 3; Rat bridge <=4.
  --mega               Very large post-reboot run: sizes 2,3,4,512,768,1024; repeats 2; Rat bridge <=4.
  --install-tools      Install optional benchmark tools with pkexec dnf.
  --tune-system        Set CPU governor to performance with pkexec cpupower.
  --core N             CPU core used for pinned benchmark runs (default: 2).
  --repeats N          Compiler benchmark measured repeats.
  --warmups N          Compiler benchmark warmup runs.
  --sizes A,B,C        Compiler benchmark base sizes.
  --rat-max N          Only run Rat compiler cases for sizes <= N.
  --string-max N       Only run DenseMatrix.toString compiler cases for sizes <= N.
  --data-max N         Only run extra data-profile cases for sizes <= N.
  --kernel-sizes A,B   Kernel #reduce suite sizes (default quick: 2; other: 2,3,4).
  --out-dir DIR        Parent directory for timestamped result directories.
  -h, --help           Show this help.
USAGE
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --quick)
      QUICK=1
      shift
      ;;
    --stress)
      STRESS=1
      shift
      ;;
    --xl)
      XL=1
      shift
      ;;
    --mega)
      MEGA=1
      shift
      ;;
    --install-tools)
      INSTALL_TOOLS=1
      shift
      ;;
    --tune-system)
      TUNE_SYSTEM=1
      shift
      ;;
    --core)
      CORE="${2:?--core requires a value}"
      shift 2
      ;;
    --repeats)
      REPEATS="${2:?--repeats requires a value}"
      shift 2
      ;;
    --warmups)
      WARMUPS="${2:?--warmups requires a value}"
      shift 2
      ;;
    --sizes)
      SIZES="${2:?--sizes requires a value}"
      shift 2
      ;;
    --rat-max)
      RAT_MAX="${2:?--rat-max requires a value}"
      shift 2
      ;;
    --string-max)
      STRING_MAX="${2:?--string-max requires a value}"
      shift 2
      ;;
    --data-max)
      DATA_MAX="${2:?--data-max requires a value}"
      shift 2
      ;;
    --kernel-sizes)
      KERNEL_SIZES="${2:?--kernel-sizes requires a value}"
      shift 2
      ;;
    --out-dir)
      OUT_PARENT="${2:?--out-dir requires a value}"
      shift 2
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

if [[ ! "$PKEXEC_TIMEOUT_SECONDS" =~ ^[0-9]+$ || "$PKEXEC_TIMEOUT_SECONDS" -lt 1 ]]; then
  echo "PKEXEC_TIMEOUT_SECONDS must be a positive integer" >&2
  exit 2
fi

need_cmd() {
  if [[ "$1" == */* ]]; then
    if [[ ! -x "$1" ]]; then
      echo "missing required command: $1" >&2
      exit 1
    fi
    return
  fi
  if ! command -v "$1" >/dev/null 2>&1; then
    echo "missing required command: $1" >&2
    exit 1
  fi
}

cmd_path_or_empty() {
  command -v "$1" 2>/dev/null || true
}

write_tool_availability_json() {
  local out="$1"
  local time_path=""
  [[ -x /usr/bin/time ]] && time_path="/usr/bin/time"

  jq -n \
    --arg generated_at_utc "$STAMP" \
    --arg lake "$(cmd_path_or_empty lake)" \
    --arg lean "$(cmd_path_or_empty lean)" \
    --arg taskset "$(cmd_path_or_empty taskset)" \
    --arg numactl "$(cmd_path_or_empty numactl)" \
    --arg perf "$(cmd_path_or_empty perf)" \
    --arg jq_path "$(cmd_path_or_empty jq)" \
    --arg tar_path "$(cmd_path_or_empty tar)" \
    --arg sha256sum "$(cmd_path_or_empty sha256sum)" \
    --arg cpupower "$(cmd_path_or_empty cpupower)" \
    --arg pkexec "$(cmd_path_or_empty pkexec)" \
    --arg dnf "$(cmd_path_or_empty dnf)" \
    --arg time_path "$time_path" \
    '
      def tool($path; $required; $role; $package_hint):
        {
          available: ($path != ""),
          path: (if $path == "" then null else $path end),
          required: $required,
          role: $role,
          package_hint: $package_hint
        };
      {
        generated_at_utc: $generated_at_utc,
        tools: {
          lake: tool($lake; true; "build and run Lean targets"; "elan/lake"),
          lean: tool($lean; true; "direct Lean file checks"; "elan/lean"),
          taskset: tool($taskset; true; "fallback CPU pinning"; "util-linux"),
          jq: tool($jq_path; true; "JSON and CSV post-processing"; "jq"),
          tar: tool($tar_path; true; "bundle archive creation"; "tar"),
          sha256sum: tool($sha256sum; true; "bundle integrity checks"; "coreutils"),
          time: tool($time_path; true; "process timing and RSS capture"; "time"),
          numactl: tool($numactl; false; "preferred CPU and NUMA pinning when available"; "numactl"),
          perf: tool($perf; false; "hardware counter capture when permitted"; "perf"),
          cpupower: tool($cpupower; false; "optional performance governor tuning"; "kernel-tools"),
          pkexec: tool($pkexec; false; "optional privileged package install and tuning"; "polkit"),
          dnf: tool($dnf; false; "optional Fedora package installation"; "dnf")
        }
      }
      | .required_available = ([.tools[] | select(.required) | .available] | all)
      | .optional_missing = ([.tools | to_entries[] | select((.value.required | not) and (.value.available | not)) | .key])
    ' >"$out"
}

write_step_not_requested() {
  local out="$1"
  local name="$2"
  {
    echo "step=$name"
    echo "requested=false"
    echo "status=not_requested"
    echo "pkexec_timeout_seconds=$PKEXEC_TIMEOUT_SECONDS"
  } >"$out"
}

run_logged_with_timeout() {
  local out="$1"
  shift
  local status
  {
    printf '$'
    printf ' %q' "$@"
    echo
    echo "pkexec_timeout_seconds=$PKEXEC_TIMEOUT_SECONDS"
    if command -v timeout >/dev/null 2>&1; then
      if timeout --foreground "${PKEXEC_TIMEOUT_SECONDS}s" "$@"; then
        status=0
      else
        status=$?
      fi
    else
      if "$@"; then
        status=0
      else
        status=$?
      fi
    fi
    echo "exit_status=$status"
  } >"$out" 2>&1
  return "$status"
}

install_optional_tools() {
  local out="$OUT_DIR/install-tools.txt"
  {
    echo "step=install-tools"
    echo "requested=true"
    echo "status=started"
    echo "pkexec_timeout_seconds=$PKEXEC_TIMEOUT_SECONDS"
  } >"$out"

  if ! command -v dnf >/dev/null 2>&1; then
    {
      echo "status=skipped"
      echo "reason=dnf_not_available"
      echo "--install-tools currently supports Fedora/dnf only"
    } >>"$out"
    echo "--install-tools skipped: dnf is not available" >&2
    return 0
  fi
  if ! command -v pkexec >/dev/null 2>&1; then
    {
      echo "status=skipped"
      echo "reason=pkexec_not_available"
      echo "--install-tools requires pkexec"
    } >>"$out"
    echo "--install-tools skipped: pkexec is not available" >&2
    return 0
  fi

  local packages=()
  command -v perf >/dev/null 2>&1 || packages+=(perf)
  command -v numactl >/dev/null 2>&1 || packages+=(numactl)
  command -v jq >/dev/null 2>&1 || packages+=(jq)
  command -v taskset >/dev/null 2>&1 || packages+=(util-linux)
  command -v cpupower >/dev/null 2>&1 || packages+=(kernel-tools)
  command -v tar >/dev/null 2>&1 || packages+=(tar)
  command -v sha256sum >/dev/null 2>&1 || packages+=(coreutils)

  if [[ ${#packages[@]} -gt 0 ]]; then
    {
      echo "packages=${packages[*]}"
      echo "status=running_pkexec"
    } >>"$out"
    local tmp="$out.command"
    local status
    if run_logged_with_timeout "$tmp" pkexec dnf install -y "${packages[@]}"; then
      status=0
    else
      status=$?
    fi
    cat "$tmp" >>"$out"
    rm -f "$tmp"
    if [[ "$status" -eq 0 ]]; then
      echo "status=ok" >>"$out"
    else
      {
        echo "status=failed_or_timed_out"
        echo "exit_status=$status"
        echo "continuing_with_available_tools=true"
      } >>"$out"
      echo "--install-tools failed or timed out after ${PKEXEC_TIMEOUT_SECONDS}s; continuing with available tools" >&2
    fi
  else
    echo "status=ok" >>"$out"
    echo "packages=" >>"$out"
    echo "all_requested_tools_already_available=true" >>"$out"
  fi
}

capture_cmd() {
  local out="$1"
  shift
  {
    echo "\$ $*"
    "$@" || true
  } >"$out" 2>&1
}

write_benchmark_env_json() {
  local out="$1"
  local path_sha
  path_sha="$(printf '%s' "${PATH:-}" | sha256sum | awk '{print $1}')"
  jq -n \
    --arg generated_at_utc "$STAMP" \
    --arg git "$GIT_SHORT" \
    --arg cwd "$ROOT" \
    --arg path_sha256 "$path_sha" \
    '
      [
        "PATH",
        "SHELL",
        "LANG",
        "LC_ALL",
        "LC_COLLATE",
        "LC_CTYPE",
        "LC_MESSAGES",
        "LC_MONETARY",
        "LC_NUMERIC",
        "LC_TIME",
        "TZ",
        "ELAN_HOME",
        "LAKE_HOME",
        "LEAN_PATH",
        "LEAN_SRC_PATH",
        "LEAN_SYSROOT",
        "LEAN_ABORT_ON_PANIC",
        "LEAN_CC",
        "CC",
        "CXX",
        "CFLAGS",
        "CXXFLAGS",
        "LDFLAGS",
        "LD_LIBRARY_PATH",
        "LD_PRELOAD",
        "MALLOC_ARENA_MAX",
        "MALLOC_CONF",
        "OMP_NUM_THREADS",
        "OPENBLAS_NUM_THREADS",
        "MKL_NUM_THREADS"
      ] as $keys
      | env as $e
      | (reduce $keys[] as $key ({}; .[$key] = ($e[$key] // null))) as $vars
      | {
          generated_at_utc: $generated_at_utc,
          git: $git,
          cwd: $cwd,
          path_sha256: $path_sha256,
          variables: $vars,
          present_keys: ($vars | to_entries | map(select(.value != null) | .key)),
          absent_keys: ($vars | to_entries | map(select(.value == null) | .key)),
          notes: [
            "Only an allowlist of benchmark-relevant environment variables is recorded.",
            "Full process environment is intentionally not bundled to avoid capturing secrets."
          ]
        }
    ' >"$out"
}

record_system_release() {
  local out="$1"
  {
    echo "== /etc/os-release =="
    if [[ -r /etc/os-release ]]; then
      cat /etc/os-release
    else
      echo "missing"
    fi
    echo
    echo "== uname =="
    uname -a
    echo
    echo "== glibc =="
    getconf GNU_LIBC_VERSION 2>/dev/null || true
    getconf GNU_LIBPTHREAD_VERSION 2>/dev/null || true
    echo
    echo "== ldd --version =="
    ldd --version 2>&1 | head -n 5 || true
    echo
    echo "== locale =="
    locale 2>&1 || true
    echo
    echo "== date/timezone =="
    date -Ins
    date '+%Z %z'
    if [[ -L /etc/localtime ]]; then
      readlink /etc/localtime
    elif [[ -e /etc/localtime ]]; then
      echo "/etc/localtime exists"
    else
      echo "/etc/localtime missing"
    fi
    echo
    echo "== ulimit =="
    ulimit -a
  } >"$out" 2>&1
}

record_cpu_state() {
  local out="$1"
  {
    echo "== uname =="
    uname -a
    echo
    echo "== lscpu =="
    lscpu
    echo
    echo "== cpufreq =="
    for cpu in /sys/devices/system/cpu/cpu[0-9]*; do
      local base="$cpu/cpufreq"
      [[ -d "$base" ]] || continue
      printf '%s ' "$(basename "$cpu")"
      [[ -r "$base/scaling_governor" ]] && printf 'governor=%s ' "$(cat "$base/scaling_governor")"
      [[ -r "$base/scaling_cur_freq" ]] && printf 'cur=%s ' "$(cat "$base/scaling_cur_freq")"
      [[ -r "$base/scaling_min_freq" ]] && printf 'min=%s ' "$(cat "$base/scaling_min_freq")"
      [[ -r "$base/scaling_max_freq" ]] && printf 'max=%s ' "$(cat "$base/scaling_max_freq")"
      [[ -r "$base/energy_performance_preference" ]] &&
        printf 'epp=%s ' "$(cat "$base/energy_performance_preference")"
      echo
    done
    echo
    echo "== smt =="
    if [[ -r /sys/devices/system/cpu/smt/active ]]; then
      cat /sys/devices/system/cpu/smt/active
    else
      echo "unknown"
    fi
    echo
    echo "== loadavg =="
    cat /proc/loadavg
    echo
    echo "== uptime =="
    uptime
    echo
    echo "== kernel cmdline =="
    cat /proc/cmdline
    echo
    echo "== thermal zones =="
    for zone in /sys/class/thermal/thermal_zone*; do
      [[ -d "$zone" ]] || continue
      printf '%s ' "$(basename "$zone")"
      [[ -r "$zone/type" ]] && printf 'type=%s ' "$(cat "$zone/type")"
      [[ -r "$zone/temp" ]] && printf 'temp=%s ' "$(cat "$zone/temp")"
      echo
    done
    echo
    echo "== turbo =="
    if [[ -r /sys/devices/system/cpu/intel_pstate/no_turbo ]]; then
      printf 'intel_pstate/no_turbo=%s\n' "$(cat /sys/devices/system/cpu/intel_pstate/no_turbo)"
    fi
    if [[ -r /sys/devices/system/cpu/cpufreq/boost ]]; then
      printf 'cpufreq/boost=%s\n' "$(cat /sys/devices/system/cpu/cpufreq/boost)"
    fi
  } >"$out"
}

record_cgroup_state() {
  local out="$1"
  {
    echo "== /proc/self/cgroup =="
    cat /proc/self/cgroup || true
    echo
    echo "== cgroup mountinfo =="
    awk '$0 ~ / - cgroup/ || $0 ~ / - cgroup2/' /proc/self/mountinfo || true
    echo
    echo "== cgroup limits =="
    local rel=""
    rel="$(awk -F: '$1 == "0" { print $3 }' /proc/self/cgroup | tail -n 1)"
    local candidates=()
    candidates+=("/sys/fs/cgroup")
    if [[ -n "$rel" && "$rel" != "/" ]]; then
      candidates+=("/sys/fs/cgroup$rel")
    fi
    local seen=""
    local base
    for base in "${candidates[@]}"; do
      [[ -d "$base" ]] || continue
      case ":$seen:" in
        *":$base:"*) continue ;;
      esac
      seen="$seen:$base"
      echo "-- $base --"
      for file in \
        cgroup.controllers cgroup.events cgroup.procs cgroup.subtree_control \
        cpu.max cpu.weight cpu.stat cpu.pressure \
        cpuset.cpus cpuset.cpus.effective cpuset.mems cpuset.mems.effective \
        memory.current memory.high memory.max memory.swap.current memory.swap.max memory.events memory.pressure \
        pids.current pids.max io.max io.stat io.pressure; do
        if [[ -r "$base/$file" ]]; then
          echo "[$file]"
          cat "$base/$file" || true
        fi
      done
      echo
    done
  } >"$out" 2>&1
}

tune_system() {
  local out="$OUT_DIR/tune-system.txt"
  {
    echo "step=tune-system"
    echo "requested=true"
    echo "status=started"
    echo "pkexec_timeout_seconds=$PKEXEC_TIMEOUT_SECONDS"
  } >"$out"

  if ! command -v pkexec >/dev/null 2>&1; then
    {
      echo "status=skipped"
      echo "reason=pkexec_not_available"
      echo "--tune-system requires pkexec"
    } >>"$out"
    echo "--tune-system skipped: pkexec is not available" >&2
    return 0
  fi
  if command -v cpupower >/dev/null 2>&1; then
    local tmp="$out.command"
    local status
    if run_logged_with_timeout "$tmp" pkexec cpupower frequency-set -g performance; then
      status=0
    else
      status=$?
    fi
    cat "$tmp" >>"$out"
    rm -f "$tmp"
    if [[ "$status" -eq 0 ]]; then
      echo "status=ok" >>"$out"
    else
      {
        echo "status=failed_or_timed_out"
        echo "exit_status=$status"
        echo "continuing_without_governor_change=true"
      } >>"$out"
      echo "--tune-system failed or timed out after ${PKEXEC_TIMEOUT_SECONDS}s; continuing without governor change" >&2
    fi
  else
    {
      echo "status=skipped"
      echo "reason=cpupower_not_available"
      echo "cpupower is not installed; run with --install-tools first"
    } >>"$out"
    echo "--tune-system skipped: cpupower is not installed" >&2
    return 0
  fi
}

PIN_CMD=()

set_pin_cmd() {
  if command -v numactl >/dev/null 2>&1; then
    PIN_CMD=(numactl --physcpubind="$CORE" --localalloc)
  else
    PIN_CMD=(taskset -c "$CORE")
  fi
}

validate_pin_cmd() {
  if ! "${PIN_CMD[@]}" true >/dev/null 2>&1; then
    echo "pinning command failed for core $CORE: ${PIN_CMD[*]}" >&2
    exit 1
  fi
}

record_pinning_state() {
  local out="$1"
  {
    echo "== requested core =="
    echo "$CORE"
    echo
    echo "== pin command =="
    printf '%q ' "${PIN_CMD[@]}"
    echo
    echo
    echo "== core sysfs =="
    local cpu_dir="/sys/devices/system/cpu/cpu${CORE}"
    if [[ -d "$cpu_dir" ]]; then
      echo "$cpu_dir exists"
      for file in online topology/core_id topology/physical_package_id topology/thread_siblings_list topology/core_siblings_list; do
        [[ -r "$cpu_dir/$file" ]] && printf '%s=%s\n' "$file" "$(cat "$cpu_dir/$file")"
      done
    else
      echo "$cpu_dir missing"
    fi
    echo
    echo "== lscpu extended =="
    lscpu -e=CPU,CORE,SOCKET,NODE,ONLINE,MAXMHZ,MINMHZ,MHZ || true
    echo
    echo "== shell affinity before pin =="
    taskset -pc $$ || true
    grep -E 'Cpus_allowed|Mems_allowed' /proc/$$/status || true
    echo
    echo "== pinned probe =="
    "${PIN_CMD[@]}" bash -c '
      echo "pid=$$"
      taskset -pc $$ || true
      grep -E "Cpus_allowed|Mems_allowed" /proc/$$/status || true
      if command -v numactl >/dev/null 2>&1; then
        numactl --show || true
      fi
      echo "current processor samples:"
      for _ in 1 2 3 4 5; do
        read -r stat_line < "/proc/$$/stat"
        set -- $stat_line
        echo "current_processor=${39:-unknown}"
      done
    '
  } >"$out" 2>&1
}

run_pinned() {
  "${PIN_CMD[@]}" "$@"
}

append_time_jsonl() {
  local metrics="$1"
  local jsonl="$2"
  local track="$3"
  local operation="$4"
  local size="$5"
  local baseline_elapsed="$6"
  awk -v track="$track" -v operation="$operation" -v size="$size" \
    -v baseline="$baseline_elapsed" '
    {
      adjusted = $1 - baseline
      if (adjusted < 0) adjusted = 0
      printf("{\"track\":\"%s\",\"operation\":\"%s\",\"size\":%s,", track, operation, size)
      printf("\"elapsed_s\":%s,\"baseline_s\":%s,\"adjusted_s\":%.6f,", $1, baseline, adjusted)
      printf("\"user_s\":%s,\"system_s\":%s,\"max_rss_kb\":%s}\n", $2, $3, $4)
    }' "$metrics" >>"$jsonl"
}

write_time_v_json() {
  local input="$1"
  local output="$2"
  jq -Rn '
    def elapsedSeconds:
      (split(":") | map(tonumber)) as $parts
      | if ($parts | length) == 3 then
          $parts[0] * 3600 + $parts[1] * 60 + $parts[2]
        elif ($parts | length) == 2 then
          $parts[0] * 60 + $parts[1]
        else
          $parts[0]
        end;
    reduce inputs as $line ({};
      if ($line | test("^\\s*Command being timed:")) then
        .command = ($line | sub("^\\s*Command being timed:\\s*"; ""))
      elif ($line | test("^\\s*User time \\(seconds\\):")) then
        .user_s = ($line | sub("^\\s*User time \\(seconds\\):\\s*"; "") | tonumber)
      elif ($line | test("^\\s*System time \\(seconds\\):")) then
        .system_s = ($line | sub("^\\s*System time \\(seconds\\):\\s*"; "") | tonumber)
      elif ($line | test("^\\s*Percent of CPU this job got:")) then
        .cpu_percent = ($line | sub("^\\s*Percent of CPU this job got:\\s*"; "") | sub("%$"; "") | tonumber)
      elif ($line | test("^\\s*Elapsed \\(wall clock\\) time \\(h:mm:ss or m:ss\\):")) then
        ($line | sub("^\\s*Elapsed \\(wall clock\\) time \\(h:mm:ss or m:ss\\):\\s*"; "")) as $elapsed
        | .elapsed_raw = $elapsed
        | .elapsed_s = ($elapsed | elapsedSeconds)
      elif ($line | test("^\\s*Maximum resident set size \\(kbytes\\):")) then
        .max_rss_kb = ($line | sub("^\\s*Maximum resident set size \\(kbytes\\):\\s*"; "") | tonumber)
      elif ($line | test("^\\s*Major \\(requiring I/O\\) page faults:")) then
        .major_page_faults = ($line | sub("^\\s*Major \\(requiring I/O\\) page faults:\\s*"; "") | tonumber)
      elif ($line | test("^\\s*Minor \\(reclaiming a frame\\) page faults:")) then
        .minor_page_faults = ($line | sub("^\\s*Minor \\(reclaiming a frame\\) page faults:\\s*"; "") | tonumber)
      elif ($line | test("^\\s*Voluntary context switches:")) then
        .voluntary_context_switches = ($line | sub("^\\s*Voluntary context switches:\\s*"; "") | tonumber)
      elif ($line | test("^\\s*Involuntary context switches:")) then
        .involuntary_context_switches = ($line | sub("^\\s*Involuntary context switches:\\s*"; "") | tonumber)
      elif ($line | test("^\\s*Swaps:")) then
        .swaps = ($line | sub("^\\s*Swaps:\\s*"; "") | tonumber)
      elif ($line | test("^\\s*File system inputs:")) then
        .file_system_inputs = ($line | sub("^\\s*File system inputs:\\s*"; "") | tonumber)
      elif ($line | test("^\\s*File system outputs:")) then
        .file_system_outputs = ($line | sub("^\\s*File system outputs:\\s*"; "") | tonumber)
      elif ($line | test("^\\s*Page size \\(bytes\\):")) then
        .page_size_bytes = ($line | sub("^\\s*Page size \\(bytes\\):\\s*"; "") | tonumber)
      elif ($line | test("^\\s*Exit status:")) then
        .exit_status = ($line | sub("^\\s*Exit status:\\s*"; "") | tonumber)
      else
        .
      end)
  ' <"$input" >"$output"
}

write_executable_artifact_json() {
  local exe="$1"
  local output="$2"

  if [[ ! -x "$exe" ]]; then
    echo "missing benchmark executable artifact: $exe" >&2
    exit 1
  fi

  local abs bytes sha file_output ldd_output file_available ldd_available
  abs="$(cd "$(dirname "$exe")" && pwd)/$(basename "$exe")"
  bytes="$(stat -c '%s' "$exe")"
  sha="$(sha256sum "$exe" | awk '{print $1}')"
  file_available=false
  ldd_available=false
  file_output=""
  ldd_output=""
  if command -v file >/dev/null 2>&1; then
    file_available=true
    file_output="$(file "$exe" 2>&1 || true)"
  fi
  if command -v ldd >/dev/null 2>&1; then
    ldd_available=true
    ldd_output="$(ldd "$exe" 2>&1 || true)"
  fi

  jq -n \
    --arg generated_at_utc "$STAMP" \
    --arg git "$GIT_SHORT" \
    --arg path "$exe" \
    --arg absolute_path "$abs" \
    --arg sha256 "$sha" \
    --arg file_output "$file_output" \
    --arg ldd_output "$ldd_output" \
    --argjson bytes "$bytes" \
    --argjson file_available "$file_available" \
    --argjson ldd_available "$ldd_available" \
    '{
      generated_at_utc: $generated_at_utc,
      git: $git,
      path: $path,
      absolute_path: $absolute_path,
      bytes: $bytes,
      sha256: $sha256,
      executable: true,
      binary_bundled: false,
      binary_bundled_reason: "binary is intentionally not embedded; sha256, size, and loader metadata are recorded instead",
      file: {
        available: $file_available,
        output: $file_output
      },
      ldd: {
        available: $ldd_available,
        output: $ldd_output
      }
    }' >"$output"
}

bundle_manifest_role() {
  local path="$1"
  case "$path" in
    REPRODUCE.md|rerun.sh)
      echo "reproducibility"
      ;;
    build.log|lakefile.toml|lake-manifest.json|lean-toolchain)
      echo "build_source"
      ;;
    executable-artifact.json)
      echo "build_artifact"
      ;;
    compiler.jsonl|compiler.csv|compiler-case-manifest.csv|compiler-samples.csv|compiler-throughput.csv|compiler-command.txt|compiler-process-metrics.json|compiler-time.txt|compiler.stdout|compiler.stderr)
      echo "compiler_measurement"
      ;;
    kernel.jsonl|kernel.csv|kernel-compiler-comparison.csv|kernel-profile-summary.csv|kernel/*)
      echo "kernel_measurement"
      ;;
    api-coverage.csv|coverage.md|dense-mathlib-pairs.csv|dense-mathlib-summary.csv|dense-only-cases.csv|matrix-size-envelope.csv|measurement-quality.json|operation-scaling.csv|profile-plan.csv|run-config.json|summary.json|summary.md)
      echo "audit_summary"
      ;;
    benchmark-env.json|cgroup-after.txt|cgroup-before.txt|cpu-after.txt|cpu-before.txt|install-tools.txt|lake-version.txt|lean-features.txt|lean-version.txt|pinning-preflight.txt|pinning-postflight.txt|system-release.txt|tool-availability.json|tool-paths.txt|tune-system.txt)
      echo "environment"
      ;;
    git-*)
      echo "repository_state"
      ;;
    *)
      echo "other"
      ;;
  esac
}

csv_quote() {
  local value="${1//\"/\"\"}"
  printf '"%s"' "$value"
}

write_bundle_manifest() {
  local out_dir="$1"
  {
    echo '"path","role","bytes","sha256"'
    while IFS= read -r rel; do
      local role bytes hash
      role="$(bundle_manifest_role "$rel")"
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
        ! -name bundle-manifest.csv \
        ! -name bundle-manifest.json \
        -printf '%P\n' | sort
    )
  } >"$out_dir/bundle-manifest.csv"

  {
    echo '['
    local first=1
    while IFS= read -r rel; do
      local role bytes hash
      role="$(bundle_manifest_role "$rel")"
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
        ! -name bundle-manifest.csv \
        ! -name bundle-manifest.json \
        -printf '%P\n' | sort
    )
    echo
    echo ']'
  } >"$out_dir/bundle-manifest.json"
}

run_kernel_case() {
  local name="$1"
  local size="$2"
  local expr="$3"
  local baseline_elapsed="$4"
  local file="$KERNEL_DIR/${name}_${size}.lean"
  local metrics="$KERNEL_DIR/${name}_${size}.time"

cat >"$file" <<LEAN
import ProvableComputation.Bench.DenseMatrixKernel

set_option maxRecDepth 1000000

#reduce $expr
LEAN

  /usr/bin/time -f '%e %U %S %M' -o "$metrics" \
    "${PIN_CMD[@]}" lake env lean -j1 "$file" \
    >"$KERNEL_DIR/${name}_${size}.stdout" \
    2>"$KERNEL_DIR/${name}_${size}.stderr"
  append_time_jsonl "$metrics" "$KERNEL_JSONL" "kernel" "$name" "$size" "$baseline_elapsed"
}

run_kernel_profile_case() {
  local name="$1"
  local source="$2"
  local metrics="$KERNEL_DIR/${name}.time"

  /usr/bin/time -f '%e %U %S %M' -o "$metrics" \
    "${PIN_CMD[@]}" lake env lean --profile -j1 "$source" \
    >"$KERNEL_DIR/${name}.stdout" \
    2>"$KERNEL_DIR/${name}.stderr"
  append_time_jsonl "$metrics" "$KERNEL_JSONL" "kernel_profile" "$name" 0 0
}

PROFILE_COUNT=$((QUICK + STRESS + XL + MEGA))
if [[ "$PROFILE_COUNT" -gt 1 ]]; then
  echo "choose only one of --quick, --stress, --xl, or --mega" >&2
  exit 2
fi

RUN_PROFILE="full"
if [[ "$QUICK" -eq 1 ]]; then
  RUN_PROFILE="quick"
elif [[ "$STRESS" -eq 1 ]]; then
  RUN_PROFILE="stress"
elif [[ "$XL" -eq 1 ]]; then
  RUN_PROFILE="xl"
elif [[ "$MEGA" -eq 1 ]]; then
  RUN_PROFILE="mega"
fi

if [[ "$STRESS" -eq 1 ]]; then
  SIZES="${SIZES:-2,3,4,128,192,256}"
  REPEATS="${REPEATS:-5}"
  WARMUPS="${WARMUPS:-2}"
  RAT_MAX="${RAT_MAX:-4}"
  KERNEL_SIZES="${KERNEL_SIZES:-2,3,4}"
fi

if [[ "$XL" -eq 1 ]]; then
  SIZES="${SIZES:-2,3,4,256,384,512}"
  REPEATS="${REPEATS:-3}"
  WARMUPS="${WARMUPS:-1}"
  RAT_MAX="${RAT_MAX:-4}"
  KERNEL_SIZES="${KERNEL_SIZES:-2,3,4}"
fi

if [[ "$MEGA" -eq 1 ]]; then
  SIZES="${SIZES:-2,3,4,512,768,1024}"
  REPEATS="${REPEATS:-2}"
  WARMUPS="${WARMUPS:-1}"
  RAT_MAX="${RAT_MAX:-4}"
  KERNEL_SIZES="${KERNEL_SIZES:-2,3,4}"
fi

if [[ -z "$KERNEL_SIZES" ]]; then
  if [[ "$QUICK" -eq 1 ]]; then
    KERNEL_SIZES="2"
  else
    KERNEL_SIZES="2,3,4"
  fi
fi

mkdir -p "$OUT_PARENT"
STAMP="$(date -u +%Y%m%dT%H%M%SZ)"
GIT_SHORT="$(git rev-parse --short HEAD 2>/dev/null || echo unknown)"
OUT_DIR="$OUT_PARENT/densematrix-${STAMP}-${GIT_SHORT}"
KERNEL_DIR="$OUT_DIR/kernel"
mkdir -p "$KERNEL_DIR"

COMPILER_JSONL="$OUT_DIR/compiler.jsonl"
KERNEL_JSONL="$OUT_DIR/kernel.jsonl"
BUILD_LOG="$OUT_DIR/build.log"
PERF_LOG="$OUT_DIR/perf-stat.txt"
COMPILER_TIME_LOG="$OUT_DIR/compiler-time.txt"
COMPILER_PROCESS_METRICS="$OUT_DIR/compiler-process-metrics.json"

echo "writing benchmark output to $OUT_DIR"

if [[ "$INSTALL_TOOLS" -eq 1 ]]; then
  install_optional_tools
else
  write_step_not_requested "$OUT_DIR/install-tools.txt" "install-tools"
fi

need_cmd lake
need_cmd taskset
need_cmd jq
need_cmd /usr/bin/time
need_cmd tar
need_cmd sha256sum
set_pin_cmd
validate_pin_cmd

if [[ "$TUNE_SYSTEM" -eq 1 ]]; then
  tune_system
else
  write_step_not_requested "$OUT_DIR/tune-system.txt" "tune-system"
fi

capture_cmd "$OUT_DIR/git-status.txt" git status --short --branch
capture_cmd "$OUT_DIR/git-rev-parse.txt" git rev-parse HEAD
capture_cmd "$OUT_DIR/git-log.txt" git log --oneline -5
capture_cmd "$OUT_DIR/git-diff-stat.txt" git diff --stat
capture_cmd "$OUT_DIR/git-diff.patch" git diff --no-color
git ls-files --others --exclude-standard \
  >"$OUT_DIR/git-untracked-files.txt" \
  2>"$OUT_DIR/git-untracked-files.stderr" || true
{
  while IFS= read -r file; do
    [[ -f "$file" ]] || continue
    git diff --no-index -- /dev/null "$file" || true
  done <"$OUT_DIR/git-untracked-files.txt"
} >"$OUT_DIR/git-untracked.patch"
capture_cmd "$OUT_DIR/git-ls-files.txt" git ls-files
capture_cmd "$OUT_DIR/lean-version.txt" lake env lean --version
capture_cmd "$OUT_DIR/lean-features.txt" lake env lean --features
capture_cmd "$OUT_DIR/lake-version.txt" lake --version
capture_cmd "$OUT_DIR/tool-paths.txt" bash -lc 'for c in lake lean taskset numactl perf jq tar sha256sum cpupower; do command -v "$c" || true; done'
write_benchmark_env_json "$OUT_DIR/benchmark-env.json"
record_system_release "$OUT_DIR/system-release.txt"
write_tool_availability_json "$OUT_DIR/tool-availability.json"
cp lakefile.toml lean-toolchain lake-manifest.json "$OUT_DIR"/
record_cpu_state "$OUT_DIR/cpu-before.txt"
record_cgroup_state "$OUT_DIR/cgroup-before.txt"
record_pinning_state "$OUT_DIR/pinning-preflight.txt"

echo "building benchmark targets"
lake build ProvableComputation TEST ProvableComputation.Bench.DenseMatrixKernel densematrix_bench \
  >"$BUILD_LOG" 2>&1
write_executable_artifact_json ".lake/build/bin/densematrix_bench" "$OUT_DIR/executable-artifact.json"

BENCH_ARGS=()
if [[ "$QUICK" -eq 1 ]]; then
  BENCH_ARGS+=(--quick)
fi
if [[ -n "$REPEATS" ]]; then
  BENCH_ARGS+=(--repeats "$REPEATS")
fi
if [[ -n "$WARMUPS" ]]; then
  BENCH_ARGS+=(--warmups "$WARMUPS")
fi
if [[ -n "$SIZES" ]]; then
  BENCH_ARGS+=(--sizes "$SIZES")
fi
if [[ -n "$RAT_MAX" ]]; then
  BENCH_ARGS+=(--rat-max "$RAT_MAX")
fi
if [[ -n "$STRING_MAX" ]]; then
  BENCH_ARGS+=(--string-max "$STRING_MAX")
fi
if [[ -n "$DATA_MAX" ]]; then
  BENCH_ARGS+=(--data-max "$DATA_MAX")
fi
BENCH_ARGS+=(--jsonl "$COMPILER_JSONL")

{
  printf 'lake exe densematrix_bench'
  printf ' %q' "${BENCH_ARGS[@]}"
  echo
} >"$OUT_DIR/compiler-command.txt"

SCRIPT_INVOCATION="scripts/run_densematrix_bench.sh"
if [[ "${#ORIGINAL_ARGS[@]}" -gt 0 ]]; then
  printf -v SCRIPT_ARGS ' %q' "${ORIGINAL_ARGS[@]}"
  SCRIPT_INVOCATION+="$SCRIPT_ARGS"
fi

jq -n \
  --arg generated_at_utc "$STAMP" \
  --arg git "$GIT_SHORT" \
  --arg profile "$RUN_PROFILE" \
  --arg core "$CORE" \
  --arg pin_command "${PIN_CMD[*]}" \
  --arg out_dir "$OUT_DIR" \
  --arg script_invocation "$SCRIPT_INVOCATION" \
  --arg compiler_command "$(cat "$OUT_DIR/compiler-command.txt")" \
  --arg sizes_override "${SIZES:-default}" \
  --arg repeats_override "${REPEATS:-default}" \
  --arg warmups_override "${WARMUPS:-default}" \
  --arg rat_max_override "${RAT_MAX:-default}" \
  --arg string_max_override "${STRING_MAX:-default}" \
  --arg data_max_override "${DATA_MAX:-default}" \
  --arg kernel_sizes_effective "$KERNEL_SIZES" \
  --arg out_parent "$OUT_PARENT" \
  --argjson pkexec_timeout_seconds "$PKEXEC_TIMEOUT_SECONDS" \
  --argjson quick "$QUICK" \
  --argjson stress "$STRESS" \
  --argjson xl "$XL" \
  --argjson mega "$MEGA" \
  --argjson install_tools "$INSTALL_TOOLS" \
  --argjson tune_system "$TUNE_SYSTEM" \
  '{
    generated_at_utc: $generated_at_utc,
    git: $git,
    profile: $profile,
    mode_flags: {
      quick: ($quick == 1),
      stress: ($stress == 1),
      xl: ($xl == 1),
      mega: ($mega == 1)
    },
    install_tools_requested: ($install_tools == 1),
    tune_system_requested: ($tune_system == 1),
    core: $core,
    pin_command: $pin_command,
    out_parent: $out_parent,
    out_dir: $out_dir,
    script_invocation: $script_invocation,
    pkexec_timeout_seconds: $pkexec_timeout_seconds,
    compiler: {
      command: $compiler_command,
      sizes_override: $sizes_override,
      repeats_override: $repeats_override,
      warmups_override: $warmups_override,
      rat_max_override: $rat_max_override,
      string_max_override: $string_max_override,
      data_max_override: $data_max_override
    },
    kernel: {
      sizes_effective: $kernel_sizes_effective
    }
  }' >"$OUT_DIR/run-config.json"

cat >"$OUT_DIR/profile-plan.csv" <<'CSV'
profile,command,use_case,compiler_sizes,repeats,warmups,rat_max,string_max,data_max,kernel_sizes,max_base_size,max_rows,max_cols,max_inner,max_work_items,notes
quick,scripts/run_densematrix_bench.sh --quick,short_validation,0;1;2;3;4,3,1,4,4,4,2,4,8,8,8,128,fast schema and smoke validation before long runs
full,scripts/run_densematrix_bench.sh --install-tools --tune-system --core 2 --repeats 30 --warmups 5,default_enterprise_baseline,0;1;2;3;4;8;16;32;64;96;128,30,5,16,16,16,2;3;4,128,256,256,256,4194304,balanced baseline with Rat and data profiles bounded to 16
stress,scripts/run_densematrix_bench.sh --install-tools --tune-system --core 2 --stress,large_runtime,2;3;4;128;192;256,5,2,4,16,16,2;3;4,256,512,512,512,33554432,large compiled runtime run with small Rat kernel/compiler bridge sizes
xl,scripts/run_densematrix_bench.sh --install-tools --tune-system --core 2 --xl,post_reboot_xl,2;3;4;256;384;512,3,1,4,16,16,2;3;4,512,1024,1024,1024,268435456,extra large post-reboot run with small Rat kernel/compiler bridge sizes
mega,scripts/run_densematrix_bench.sh --install-tools --tune-system --core 2 --mega,post_reboot_capacity,2;3;4;512;768;1024,2,1,4,16,16,2;3;4,1024,2048,2048,2048,2147483648,largest built-in post-reboot capacity run with small Rat kernel/compiler bridge sizes
CSV

echo "running compiler benchmark pinned to core $CORE"
if command -v perf >/dev/null 2>&1 && perf stat -o /dev/null true >/dev/null 2>&1; then
  /usr/bin/time -v -o "$COMPILER_TIME_LOG" \
    perf stat -o "$PERF_LOG" -- \
      "${PIN_CMD[@]}" lake exe densematrix_bench "${BENCH_ARGS[@]}" \
    >"$OUT_DIR/compiler.stdout" \
    2>"$OUT_DIR/compiler.stderr"
else
  /usr/bin/time -v -o "$COMPILER_TIME_LOG" \
    "${PIN_CMD[@]}" lake exe densematrix_bench "${BENCH_ARGS[@]}" \
    >"$OUT_DIR/compiler.stdout" \
    2>"$OUT_DIR/compiler.stderr"
fi
write_time_v_json "$COMPILER_TIME_LOG" "$COMPILER_PROCESS_METRICS"

BASELINE_FILE="$KERNEL_DIR/import_baseline.lean"
BASELINE_TIME="$KERNEL_DIR/import_baseline.time"
cat >"$BASELINE_FILE" <<'LEAN'
import ProvableComputation.Bench.DenseMatrixKernel

#eval ()
LEAN

echo "running kernel import baseline pinned to core $CORE"
/usr/bin/time -f '%e %U %S %M' -o "$BASELINE_TIME" \
  "${PIN_CMD[@]}" lake env lean -j1 "$BASELINE_FILE" \
  >"$KERNEL_DIR/import_baseline.stdout" \
  2>"$KERNEL_DIR/import_baseline.stderr"
BASELINE_ELAPSED="$(awk '{print $1}' "$BASELINE_TIME")"
append_time_jsonl "$BASELINE_TIME" "$KERNEL_JSONL" "kernel" "import_baseline" 0 0

echo "running kernel #reduce cases pinned to core $CORE"
IFS=',' read -ra KSIZE_ARRAY <<< "$KERNEL_SIZES"
for raw_size in "${KSIZE_ARRAY[@]}"; do
  size="$(echo "$raw_size" | tr -d '[:space:]')"
  [[ -n "$size" ]] || continue
  run_kernel_case "suite" "$size" "DenseMatrixBench.Kernel.suiteFor ${size}" "$BASELINE_ELAPSED"
done
run_kernel_case "construction" 2 "DenseMatrixBench.Kernel.construction2" "$BASELINE_ELAPSED"
run_kernel_case "conversion" 2 "DenseMatrixBench.Kernel.conversion2" "$BASELINE_ELAPSED"
run_kernel_case "access_update" 2 "DenseMatrixBench.Kernel.accessAndUpdate2" "$BASELINE_ELAPSED"
run_kernel_case "arithmetic" 2 "DenseMatrixBench.Kernel.arithmetic2" "$BASELINE_ELAPSED"
run_kernel_case "formatting" 2 "DenseMatrixBench.Kernel.formatting2" "$BASELINE_ELAPSED"
run_kernel_case "data_profiles" 2 "DenseMatrixBench.Kernel.dataProfiles2" "$BASELINE_ELAPSED"

echo "running Lean profile cases pinned to core $CORE"
run_kernel_profile_case "profile_densematrix_defs" \
  "ProvableComputation/LinearAlgebra/DenseMatrix/Defs.lean"
run_kernel_profile_case "profile_densematrix_bench" \
  "ProvableComputation/Bench/DenseMatrixBench.lean"

record_cpu_state "$OUT_DIR/cpu-after.txt"
record_cgroup_state "$OUT_DIR/cgroup-after.txt"
record_pinning_state "$OUT_DIR/pinning-postflight.txt"

if command -v jq >/dev/null 2>&1; then
  jq -s -r '
    ["track","operation","element","data_profile","rows","cols","inner","warmups","repeats",
      "checksum","duration_unit","count","min_ms","q1_ms","median_ms","mean_ms","p90_ms",
      "p95_ms","q3_ms","max_ms","stddev_ms","mad_ms","cv"],
    (.[] | [.track,.operation,.element,(.data_profile // "deterministic"),
      .rows,.cols,.inner,.warmups,.repeats,.checksum,
      .duration_unit,.count,.min_ms,.q1_ms,.median_ms,.mean_ms,.p90_ms,.p95_ms,
      .q3_ms,.max_ms,.stddev_ms,.mad_ms,.cv])
    | @csv
  ' "$COMPILER_JSONL" >"$OUT_DIR/compiler.csv"
  jq -s -r '
    ["track","operation","element","data_profile","rows","cols","inner","warmups","repeats",
      "sample_index","sample_unit","sample_ns","sample_ms"],
    (.[] as $case
      | (($case.samples_ns // []) | to_entries[])
      | [$case.track,$case.operation,$case.element,($case.data_profile // "deterministic"),
          $case.rows,$case.cols,$case.inner,
          $case.warmups,$case.repeats,.key,"ns",.value,(.value / 1000000)])
    | @csv
  ' "$COMPILER_JSONL" >"$OUT_DIR/compiler-samples.csv"
  jq -s -r '
    ["track","operation","size","elapsed_s","baseline_s","adjusted_s","user_s",
      "system_s","max_rss_kb"],
    (.[] | [.track,.operation,.size,.elapsed_s,.baseline_s,.adjusted_s,.user_s,
      .system_s,.max_rss_kb])
    | @csv
  ' "$KERNEL_JSONL" >"$OUT_DIR/kernel.csv"

  {
    echo '"profile_case","metric","ms"'
    for profile_stderr in "$KERNEL_DIR"/profile_*.stderr; do
      [[ -f "$profile_stderr" ]] || continue
      profile_case="$(basename "$profile_stderr" .stderr)"
      awk -v profile_case="$profile_case" '
        function csv_quote(s) {
          gsub(/"/, "\"\"", s)
          return "\"" s "\""
        }
        /^import took [0-9.]+(ms|s)$/ {
          value = $3
          if (value ~ /ms$/) {
            sub(/ms$/, "", value)
          } else if (value ~ /s$/) {
            sub(/s$/, "", value)
            value = value * 1000
          }
          print csv_quote(profile_case) "," csv_quote("import_took") "," value
          next
        }
        /^\t/ {
          line = $0
          sub(/^\t/, "", line)
          if (match(line, / [0-9.]+(ms|s)$/)) {
            metric = substr(line, 1, RSTART - 1)
            value = substr(line, RSTART + 1)
            if (value ~ /ms$/) {
              sub(/ms$/, "", value)
            } else if (value ~ /s$/) {
              sub(/s$/, "", value)
              value = value * 1000
            }
            print csv_quote(profile_case) "," csv_quote(metric) "," value
          }
        }
      ' "$profile_stderr"
    done
  } >"$OUT_DIR/kernel-profile-summary.csv"

  jq -s -r '
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
    ["track","setup_policy","shape_family","operation","element","data_profile","rows","cols","inner",
      "warmups","repeats","checksum"],
    (.[] | [.track,setupPolicy,shapeFamily,.operation,.element,
      (.data_profile // "deterministic"),.rows,.cols,.inner,
      .warmups,.repeats,.checksum])
    | @csv
  ' "$COMPILER_JSONL" >"$OUT_DIR/compiler-case-manifest.csv"

  jq -s -r '
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
    def workModel:
      if (.operation | startswith("mul")) then "rows_cols_inner"
      else "rows_cols" end;
    def workItems:
      if (.operation | startswith("mul")) then (.rows * .cols * .inner)
      else (.rows * .cols) end;
    ["track","setup_policy","shape_family","operation","element","data_profile","rows","cols","inner",
      "work_model","work_items","median_ms","p95_ms","items_per_ms","items_per_s",
      "p95_items_per_ms","p95_items_per_s"],
    (.[] | workItems as $items
      | [.track,setupPolicy,shapeFamily,.operation,.element,
          (.data_profile // "deterministic"),.rows,.cols,.inner,
          workModel,$items,.median_ms,.p95_ms,
          (if .median_ms == 0 then "" else ($items / .median_ms) end),
          (if .median_ms == 0 then "" else (($items / .median_ms) * 1000) end),
          (if .p95_ms == 0 then "" else ($items / .p95_ms) end),
          (if .p95_ms == 0 then "" else (($items / .p95_ms) * 1000) end)])
    | @csv
  ' "$COMPILER_JSONL" >"$OUT_DIR/compiler-throughput.csv"

  jq -s -r '
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
    def dataProfile: (.data_profile // "deterministic");
    def workItems:
      if (.operation | startswith("mul")) then (.rows * .cols * .inner)
      else (.rows * .cols) end;
    def outputCells: (.rows * .cols);
    def inputCells:
      if (.operation | startswith("mul")) then (.rows * .inner + .inner * .cols)
      else (.rows * .cols) end;
    def totalMatrixCells:
      if (.operation | startswith("mul")) then (.rows * .inner + .inner * .cols + .rows * .cols)
      else (.rows * .cols) end;
    ["track","setup_policy","shape_family","operation","element","data_profile","case_count",
      "min_rows","max_rows","min_cols","max_cols","min_inner","max_inner",
      "max_work_items","max_output_cells","max_input_cells","max_total_matrix_cells"],
    (map(. + {
        setup_policy: setupPolicy,
        shape_family: shapeFamily,
        data_profile: dataProfile,
        work_items: workItems,
        output_cells: outputCells,
        input_cells: inputCells,
        total_matrix_cells: totalMatrixCells
      })
      | group_by([.track,.setup_policy,.shape_family,.operation,.element,.data_profile])
      | .[]
      | [
          .[0].track,
          .[0].setup_policy,
          .[0].shape_family,
          .[0].operation,
          .[0].element,
          .[0].data_profile,
          length,
          (map(.rows) | min),
          (map(.rows) | max),
          (map(.cols) | min),
          (map(.cols) | max),
          (map(.inner) | min),
          (map(.inner) | max),
          (map(.work_items) | max),
          (map(.output_cells) | max),
          (map(.input_cells) | max),
          (map(.total_matrix_cells) | max)
        ])
    | @csv
  ' "$COMPILER_JSONL" >"$OUT_DIR/matrix-size-envelope.csv"

  jq -s -r '
    def dataProfile: (.data_profile // "deterministic");
    def recKey: "\(.track)|\(.operation)|\(.element)|\(dataProfile)|\(.rows)|\(.cols)|\(.inner)";
    def baselineTrack:
      if .track == "compiler_dense" then "compiler_mathlib"
      elif .track == "compiler_dense_prebuilt" then "compiler_mathlib_prebuilt"
      else empty end;
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
    ["dense_track","baseline_track","setup_policy","shape_family","operation","element",
      "data_profile","rows","cols","inner","dense_median_ms","baseline_median_ms","median_ratio",
      "dense_p95_ms","baseline_p95_ms","p95_ratio","dense_checksum","baseline_checksum",
      "checksum_status"],
    (
      . as $all
      | ($all
          | map(select(.track == "compiler_mathlib" or .track == "compiler_mathlib_prebuilt")
            | {key: recKey, value: .})
          | from_entries) as $baselines
      | $all[]
      | select(.track == "compiler_dense" or .track == "compiler_dense_prebuilt")
      | . as $dense
      | (baselineTrack) as $bt
      | ($dense | dataProfile) as $profile
      | ($baselines["\($bt)|\($dense.operation)|\($dense.element)|\($profile)|\($dense.rows)|\($dense.cols)|\($dense.inner)"] // null) as $baseline
      | select($baseline != null)
      | [
          $dense.track,
          $bt,
          ($dense | setupPolicy),
          ($dense | shapeFamily),
          $dense.operation,
          $dense.element,
          $profile,
          $dense.rows,
          $dense.cols,
          $dense.inner,
          $dense.median_ms,
          $baseline.median_ms,
          (if $baseline.median_ms == 0 then "" else ($dense.median_ms / $baseline.median_ms) end),
          $dense.p95_ms,
          $baseline.p95_ms,
          (if $baseline.p95_ms == 0 then "" else ($dense.p95_ms / $baseline.p95_ms) end),
          $dense.checksum,
          $baseline.checksum,
          (if $dense.checksum == $baseline.checksum then "ok" else "mismatch" end)
        ]
    )
    | @csv
  ' "$COMPILER_JSONL" >"$OUT_DIR/dense-mathlib-pairs.csv"

  jq -s -r '
    def dataProfile: (.data_profile // "deterministic");
    def recKey: "\(.track)|\(.operation)|\(.element)|\(dataProfile)|\(.rows)|\(.cols)|\(.inner)";
    def baselineTrack:
      if .track == "compiler_dense" then "compiler_mathlib"
      elif .track == "compiler_dense_prebuilt" then "compiler_mathlib_prebuilt"
      else empty end;
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
    ["dense_track","setup_policy","shape_family","operation","element","data_profile","rows","cols",
      "inner","checksum","reason"],
    (
      . as $all
      | ($all
          | map(select(.track == "compiler_mathlib" or .track == "compiler_mathlib_prebuilt")
            | {key: recKey, value: .})
          | from_entries) as $baselines
      | $all[]
      | select(.track == "compiler_dense" or .track == "compiler_dense_prebuilt")
      | . as $dense
      | (baselineTrack) as $bt
      | ($dense | dataProfile) as $profile
      | ($baselines["\($bt)|\($dense.operation)|\($dense.element)|\($profile)|\($dense.rows)|\($dense.cols)|\($dense.inner)"] // null) as $baseline
      | select($baseline == null)
      | [
          $dense.track,
          ($dense | setupPolicy),
          ($dense | shapeFamily),
          $dense.operation,
          $dense.element,
          $profile,
          $dense.rows,
          $dense.cols,
          $dense.inner,
          $dense.checksum,
          "dense_only_no_direct_mathlib_operation"
        ]
    )
    | @csv
  ' "$COMPILER_JSONL" >"$OUT_DIR/dense-only-cases.csv"

  jq -s -r '
    def dataProfile: (.data_profile // "deterministic");
    def recKey: "\(.track)|\(.operation)|\(.element)|\(dataProfile)|\(.rows)|\(.cols)|\(.inner)";
    def baselineTrack:
      if .track == "compiler_dense" then "compiler_mathlib"
      elif .track == "compiler_dense_prebuilt" then "compiler_mathlib_prebuilt"
      else empty end;
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
    def workItems:
      if (.operation | startswith("mul")) then (.rows * .cols * .inner)
      else (.rows * .cols) end;
    def maybe($x): if $x == null then "" else $x end;
    def avg: if length == 0 then null else add / length end;
    def median:
      if length == 0 then null
      else (sort as $s | $s[(length / 2 | floor)])
      end;
    def pairRows:
      . as $all
      | ($all
          | map(select(.track == "compiler_mathlib" or .track == "compiler_mathlib_prebuilt")
            | {key: recKey, value: .})
          | from_entries) as $baselines
      | $all[]
      | select(.track == "compiler_dense" or .track == "compiler_dense_prebuilt")
      | . as $dense
      | (baselineTrack) as $bt
      | ($dense | dataProfile) as $profile
      | ($baselines["\($bt)|\($dense.operation)|\($dense.element)|\($profile)|\($dense.rows)|\($dense.cols)|\($dense.inner)"] // null) as $baseline
      | select($baseline != null)
      | {
          dense_track: $dense.track,
          baseline_track: $bt,
          setup_policy: ($dense | setupPolicy),
          shape_family: ($dense | shapeFamily),
          operation: $dense.operation,
          element: $dense.element,
          data_profile: $profile,
          rows: $dense.rows,
          cols: $dense.cols,
          inner: $dense.inner,
          work_items: ($dense | workItems),
          median_ratio: (if $baseline.median_ms == 0 then null else ($dense.median_ms / $baseline.median_ms) end),
          p95_ratio: (if $baseline.p95_ms == 0 then null else ($dense.p95_ms / $baseline.p95_ms) end),
          checksum_status: (if $dense.checksum == $baseline.checksum then "ok" else "mismatch" end)
        };
    ["dense_track","baseline_track","setup_policy","shape_family","operation","element",
      "data_profile","pair_count","max_rows","max_cols","max_inner","max_work_items",
      "median_ratio_min","median_ratio_median","median_ratio_mean","median_ratio_max",
      "p95_ratio_min","p95_ratio_median","p95_ratio_mean","p95_ratio_max",
      "checksum_mismatch_count","worst_median_rows","worst_median_cols","worst_median_inner",
      "worst_p95_rows","worst_p95_cols","worst_p95_inner"],
    (
      [pairRows]
      | group_by([.dense_track,.baseline_track,.setup_policy,.shape_family,.operation,.element,.data_profile])
      | .[]
      | . as $group
      | ($group | map(select(.median_ratio != null) | .median_ratio)) as $medianRatios
      | ($group | map(select(.p95_ratio != null) | .p95_ratio)) as $p95Ratios
      | ($group | max_by(.median_ratio // -1)) as $worstMedian
      | ($group | max_by(.p95_ratio // -1)) as $worstP95
      | [
          $group[0].dense_track,
          $group[0].baseline_track,
          $group[0].setup_policy,
          $group[0].shape_family,
          $group[0].operation,
          $group[0].element,
          $group[0].data_profile,
          ($group | length),
          ($group | map(.rows) | max),
          ($group | map(.cols) | max),
          ($group | map(.inner) | max),
          ($group | map(.work_items) | max),
          maybe($medianRatios | min),
          maybe($medianRatios | median),
          maybe($medianRatios | avg),
          maybe($medianRatios | max),
          maybe($p95Ratios | min),
          maybe($p95Ratios | median),
          maybe($p95Ratios | avg),
          maybe($p95Ratios | max),
          ($group | map(select(.checksum_status != "ok")) | length),
          $worstMedian.rows,
          $worstMedian.cols,
          $worstMedian.inner,
          $worstP95.rows,
          $worstP95.cols,
          $worstP95.inner
        ]
    )
    | @csv
  ' "$COMPILER_JSONL" >"$OUT_DIR/dense-mathlib-summary.csv"

  jq -s -r '
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
    def dataProfile: (.data_profile // "deterministic");
    def workItems:
      if (.operation | startswith("mul")) then (.rows * .cols * .inner)
      else (.rows * .cols) end;
    def maybe($x): if $x == null then "" else $x end;
    def p95OverMedian:
      if .median_ms == 0 then null else (.p95_ms / .median_ms) end;
    ["track","setup_policy","shape_family","operation","element","data_profile","case_count",
      "min_work_items","max_work_items","min_rows","max_rows","min_cols","max_cols",
      "min_inner","max_inner","median_ms_at_min_work","median_ms_at_max_work",
      "median_growth_ratio","p95_ms_at_min_work","p95_ms_at_max_work","p95_growth_ratio",
      "max_cv","max_p95_over_median"],
    (
      map(. + {
        setup_policy: setupPolicy,
        shape_family: shapeFamily,
        data_profile: dataProfile,
        work_items: workItems,
        p95_over_median: p95OverMedian
      })
      | group_by([.track,.setup_policy,.shape_family,.operation,.element,.data_profile])
      | .[]
      | sort_by(.work_items,.rows,.cols,.inner)
      | . as $group
      | $group[0] as $first
      | $group[-1] as $last
      | [
          $group[0].track,
          $group[0].setup_policy,
          $group[0].shape_family,
          $group[0].operation,
          $group[0].element,
          $group[0].data_profile,
          ($group | length),
          $first.work_items,
          $last.work_items,
          ($group | map(.rows) | min),
          ($group | map(.rows) | max),
          ($group | map(.cols) | min),
          ($group | map(.cols) | max),
          ($group | map(.inner) | min),
          ($group | map(.inner) | max),
          $first.median_ms,
          $last.median_ms,
          maybe(if $first.median_ms == 0 then null else ($last.median_ms / $first.median_ms) end),
          $first.p95_ms,
          $last.p95_ms,
          maybe(if $first.p95_ms == 0 then null else ($last.p95_ms / $first.p95_ms) end),
          ($group | map(.cv // 0) | max),
          maybe($group | map(select(.p95_over_median != null) | .p95_over_median) | max)
        ]
    )
    | @csv
  ' "$COMPILER_JSONL" >"$OUT_DIR/operation-scaling.csv"

  jq -n -r --slurpfile compiler "$COMPILER_JSONL" --slurpfile kernel "$KERNEL_JSONL" '
    def cmedian($track; $operation; $element; $profile; $rows; $cols; $inner):
      ([$compiler[]
        | select(.track == $track and .operation == $operation and .element == $element
            and (.data_profile // "deterministic") == $profile
            and .rows == $rows and .cols == $cols and .inner == $inner)
        | .median_ms][0] // null);
    def kernelMs($operation; $size):
      ((([$kernel[]
        | select(.track == "kernel" and .operation == $operation and .size == $size)
        | .adjusted_s][0] // 0) * 1000));
    def itemMedian($track; $item; $size):
      cmedian($track; $item.operation; $item.element;
        ($item.profile // "deterministic"); $size; $size; $item.inner);
    def sumMedians($track; $items; $size):
      reduce $items[] as $item
        (0; . + (itemMedian($track; $item; $size) // 0));
    def missingCount($track; $items; $size):
      ($items | map(select(itemMedian($track; .; $size) == null)) | length);
    def row($category; $operation; $size; $setupItems; $prebuiltItems; $notes):
      (missingCount("compiler_dense"; $setupItems; $size)) as $setupMissing
      | (missingCount("compiler_dense_prebuilt"; $prebuiltItems; $size)) as $prebuiltMissing
      | [
          $category,
          $operation,
          $size,
          kernelMs($operation; $size),
          sumMedians("compiler_dense"; $setupItems; $size),
          (if ($prebuiltItems | length) == 0 then "" else sumMedians("compiler_dense_prebuilt"; $prebuiltItems; $size) end),
          $setupMissing,
          $prebuiltMissing,
          (if $setupMissing == 0 and $prebuiltMissing == 0 then "exact_compiler_match" else "missing_compiler_match" end),
          $notes
        ];
    def suiteSetupItems:
      [
        {"operation":"of","element":"Nat","inner":0},
        {"operation":"ofMatrix","element":"Nat","inner":0},
        {"operation":"toMatrix","element":"Nat","inner":0},
        {"operation":"get","element":"Nat","inner":0},
        {"operation":"get!","element":"Nat","inner":0},
        {"operation":"set","element":"Nat","inner":0},
        {"operation":"set!","element":"Nat","inner":0},
        {"operation":"add","element":"Int","inner":0},
        {"operation":"smul","element":"Int","inner":0},
        {"operation":"toString","element":"Nat","inner":0},
        {"operation":"add","element":"Rat","inner":0}
      ];
    def suitePrebuiltItems:
      [
        {"operation":"get","element":"Nat","inner":0},
        {"operation":"get!","element":"Nat","inner":0},
        {"operation":"set","element":"Nat","inner":0},
        {"operation":"set!","element":"Nat","inner":0},
        {"operation":"add","element":"Int","inner":0},
        {"operation":"smul","element":"Int","inner":0},
        {"operation":"toString","element":"Nat","inner":0},
        {"operation":"add","element":"Rat","inner":0}
      ];
    ["category","kernel_operation","kernel_size","kernel_adjusted_ms",
      "compiler_dense_setup_inclusive_sum_ms","compiler_dense_prebuilt_sum_ms",
      "compiler_setup_missing_count","compiler_prebuilt_missing_count","match_status","notes"],
    (
      [$kernel[] | select(.track == "kernel" and .operation == "suite") | .size] | sort | .[]
      | row("suite"; "suite"; .; suiteSetupItems; suitePrebuiltItems;
          "kernel #reduce suite vs compiled median sums for exact matching square size when available")
    ),
    row("construction"; "construction"; 2;
      [{"operation":"of","element":"Nat","inner":0}];
      [];
      "DenseMatrix construction has no prebuilt-input analogue"),
    row("conversion"; "conversion"; 2;
      [
        {"operation":"ofMatrix","element":"Nat","inner":0},
        {"operation":"toMatrix","element":"Nat","inner":0}
      ];
      [];
      "conversion combines ofMatrix and toMatrix"),
    row("access_update"; "access_update"; 2;
      [
        {"operation":"get","element":"Nat","inner":0},
        {"operation":"get!","element":"Nat","inner":0},
        {"operation":"set","element":"Nat","inner":0},
        {"operation":"set!","element":"Nat","inner":0}
      ];
      [
        {"operation":"get","element":"Nat","inner":0},
        {"operation":"get!","element":"Nat","inner":0},
        {"operation":"set","element":"Nat","inner":0},
        {"operation":"set!","element":"Nat","inner":0}
      ];
      "access/update combines checked and unchecked read/write paths"),
    row("arithmetic"; "arithmetic"; 2;
      [
        {"operation":"add","element":"Int","inner":0},
        {"operation":"smul","element":"Int","inner":0},
        {"operation":"add","element":"Rat","inner":0}
      ];
      [
        {"operation":"add","element":"Int","inner":0},
        {"operation":"smul","element":"Int","inner":0},
        {"operation":"add","element":"Rat","inner":0}
      ];
      "arithmetic combines Int add/smul and Rat add"),
    row("formatting"; "formatting"; 2;
      [{"operation":"toString","element":"Nat","inner":0}];
      [{"operation":"toString","element":"Nat","inner":0}];
      "formatting measures the DenseMatrix ToString instance"),
    row("data_profiles"; "data_profiles"; 2;
      [
        {"operation":"add","element":"Int","profile":"zero","inner":0},
        {"operation":"add","element":"Int","profile":"large_magnitude","inner":0},
        {"operation":"add","element":"Rat","profile":"large_magnitude","inner":0}
      ];
      [
        {"operation":"add","element":"Int","profile":"zero","inner":0},
        {"operation":"add","element":"Int","profile":"large_magnitude","inner":0},
        {"operation":"add","element":"Rat","profile":"large_magnitude","inner":0}
      ];
      "kernel data profile suite covers zero and large-magnitude add records; compiler covers profile multiplication")
    | @csv
  ' >"$OUT_DIR/kernel-compiler-comparison.csv"

  jq -s --slurpfile compilerProcess "$COMPILER_PROCESS_METRICS" \
    --slurpfile executableArtifact "$OUT_DIR/executable-artifact.json" '
    def dataProfile: (.data_profile // "deterministic");
    def recKey: "\(.track)|\(.operation)|\(.element)|\(dataProfile)|\(.rows)|\(.cols)|\(.inner)";
    def baselineTrack:
      if .track == "compiler_dense" then "compiler_mathlib"
      elif .track == "compiler_dense_prebuilt" then "compiler_mathlib_prebuilt"
      else empty end;
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
    def workModel:
      if (.operation | startswith("mul")) then "rows_cols_inner"
      else "rows_cols" end;
    def workItems:
      if (.operation | startswith("mul")) then (.rows * .cols * .inner)
      else (.rows * .cols) end;
    . as $all
    | ($all
        | map(select(.track == "compiler_mathlib" or .track == "compiler_mathlib_prebuilt")
          | {key: recKey, value: .})
        | from_entries) as $baselines
    | [
        $all[]
        | select(.track == "compiler_dense" or .track == "compiler_dense_prebuilt")
        | . as $dense
        | (baselineTrack) as $bt
        | ($dense | dataProfile) as $profile
        | ($baselines["\($bt)|\($dense.operation)|\($dense.element)|\($profile)|\($dense.rows)|\($dense.cols)|\($dense.inner)"] // null) as $baseline
        | {dense: $dense, baseline: $baseline}
      ] as $pairs
    | ($all | map(. + {shape_family: shapeFamily, setup_policy: setupPolicy})) as $annotated
    | ($all | map(.rows) | max) as $maxRows
    | ($all | map(.cols) | max) as $maxCols
    | ($all | map(.inner) | max) as $maxInner
    | ($all | map(workItems) | max) as $maxWorkItems
    | ($all | map((.samples_ns // []) | (add // 0)) | add) as $sampleTotalNs
    | ($pairs | map(select(.baseline != null and .baseline.median_ms != 0) | (.dense.median_ms / .baseline.median_ms))) as $medianRatios
    | ($pairs | map(select(.baseline != null and .baseline.p95_ms != 0) | (.dense.p95_ms / .baseline.p95_ms))) as $p95Ratios
    | {
      generated_at_utc: "'"$STAMP"'",
      git: "'"$GIT_SHORT"'",
      profile: "'"$RUN_PROFILE"'",
      core: "'"$CORE"'",
      sizes_override: "'"${SIZES:-default}"'",
      repeats_override: "'"${REPEATS:-default}"'",
      warmups_override: "'"${WARMUPS:-default}"'",
      rat_max_override: "'"${RAT_MAX:-default}"'",
      string_max_override: "'"${STRING_MAX:-default}"'",
      data_max_override: "'"${DATA_MAX:-default}"'",
      pin_command: "'"${PIN_CMD[*]}"'",
      install_tools_requested: "'"$INSTALL_TOOLS"'" == "1",
      tune_system_requested: "'"$TUNE_SYSTEM"'" == "1",
      pkexec_timeout_seconds: '"$PKEXEC_TIMEOUT_SECONDS"',
      compiler_records: length,
      compiler_sample_count: ($all | map((.samples_ns // []) | length) | add),
      compiler_sample_total_ns: $sampleTotalNs,
      compiler_sample_total_ms: ($sampleTotalNs / 1000000),
      compiler_sample_total_s: ($sampleTotalNs / 1000000000),
      compiler_measured_to_elapsed_ratio:
        (if (($compilerProcess[0].elapsed_s // 0) > 0) then
          (($sampleTotalNs / 1000000000) / $compilerProcess[0].elapsed_s)
        else null end),
      compiler_min_samples_per_record: ($all | map((.samples_ns // []) | length) | min),
      compiler_max_samples_per_record: ($all | map((.samples_ns // []) | length) | max),
      compiler_tracks: (map(.track) | unique),
      compiler_by_track: (group_by(.track) | map({track: .[0].track, count: length})),
      compiler_by_setup_policy: ($annotated | group_by(.setup_policy) | map({setup_policy: .[0].setup_policy, count: length})),
      compiler_by_shape_family: ($annotated | group_by(.shape_family) | map({shape_family: .[0].shape_family, count: length})),
      compiler_by_work_model: ($all | map(. + {work_model: workModel}) | group_by(.work_model) | map({work_model: .[0].work_model, count: length})),
      compiler_by_data_profile: ($all | map(. + {data_profile: dataProfile}) | group_by(.data_profile) | map({data_profile: .[0].data_profile, count: length})),
      compiler_by_element: (group_by(.element) | map({element: .[0].element, count: length})),
      compiler_operations: (map(.operation) | unique),
      compiler_sizes: (map(.rows) | unique),
      compiler_max_rows: $maxRows,
      compiler_max_cols: $maxCols,
      compiler_max_inner: $maxInner,
      compiler_max_work_items: $maxWorkItems,
      compiler_scaling_group_count: ($annotated | group_by([.track,.setup_policy,.shape_family,.operation,.element,(.data_profile // "deterministic")]) | length),
      executable_artifact: ($executableArtifact[0] // {}),
      compiler_process_metrics: ($compilerProcess[0] // {}),
      dense_mathlib_pair_count: ($pairs | map(select(.baseline != null)) | length),
      dense_only_case_count: ($pairs | map(select(.baseline == null)) | length),
      dense_mathlib_median_ratio_max: (if ($medianRatios | length) == 0 then null else ($medianRatios | max) end),
      dense_mathlib_p95_ratio_max: (if ($p95Ratios | length) == 0 then null else ($p95Ratios | max) end),
      dense_mathlib_checksum_mismatch_count: ($pairs | map(select(.baseline != null and .dense.checksum != .baseline.checksum)) | length)
    }
  ' "$COMPILER_JSONL" >"$OUT_DIR/summary.json"
else
  {
    echo "{"
    echo "  \"generated_at_utc\": \"$STAMP\","
    echo "  \"git\": \"$GIT_SHORT\""
    echo "}"
  } >"$OUT_DIR/summary.json"
fi

jq -s \
  --arg generated_at_utc "$STAMP" \
  --arg git "$GIT_SHORT" \
  --arg profile "$RUN_PROFILE" \
  --arg core "$CORE" \
  --slurpfile compilerProcess "$COMPILER_PROCESS_METRICS" \
  '
    def dataProfile: (.data_profile // "deterministic");
    def sampleCount: ((.samples_ns // []) | length);
    def p95OverMedian:
      if ((.median_ms // 0) == 0) then null else ((.p95_ms // 0) / .median_ms) end;
    def caseSummary:
      {
        track,
        operation,
        element,
        data_profile: dataProfile,
        rows,
        cols,
        inner,
        warmups,
        repeats,
        count,
        sample_count: sampleCount,
        mean_ms,
        median_ms,
        p95_ms,
        stddev_ms,
        mad_ms,
        cv,
        p95_over_median: p95OverMedian
      };
    . as $all
    | ($all | map(sampleCount)) as $sampleCounts
    | ($all | map(caseSummary)) as $cases
    | ($all | map(.cv // 0)) as $cvs
    | ($all | map(.mad_ms // 0)) as $mads
    | ($all | map(.stddev_ms // 0)) as $stddevs
    | ($all | map(p95OverMedian) | map(select(. != null))) as $p95Ratios
    | ($all | map((.samples_ns // []) | (add // 0)) | add) as $sampleTotalNs
    | {
        generated_at_utc: $generated_at_utc,
        git: $git,
        profile: $profile,
        core: $core,
        compiler_records: ($all | length),
        compiler_sample_count: ($sampleCounts | add),
        compiler_sample_total_ns: $sampleTotalNs,
        compiler_sample_total_ms: ($sampleTotalNs / 1000000),
        compiler_sample_total_s: ($sampleTotalNs / 1000000000),
        compiler_process_elapsed_s: ($compilerProcess[0].elapsed_s // null),
        compiler_measured_to_elapsed_ratio:
          (if (($compilerProcess[0].elapsed_s // 0) > 0) then
            (($sampleTotalNs / 1000000000) / $compilerProcess[0].elapsed_s)
          else null end),
        min_samples_per_record: ($sampleCounts | min),
        max_samples_per_record: ($sampleCounts | max),
        sample_count_declared_mismatch_count:
          ($all | map(select(sampleCount != (.count // -1))) | length),
        sample_count_repeat_mismatch_count:
          ($all | map(select(sampleCount != (.repeats // -1))) | length),
        records_with_cv_gt_0_05: ($all | map(select((.cv // 0) > 0.05)) | length),
        records_with_cv_gt_0_10: ($all | map(select((.cv // 0) > 0.10)) | length),
        records_with_cv_gt_0_25: ($all | map(select((.cv // 0) > 0.25)) | length),
        records_with_cv_gt_0_50: ($all | map(select((.cv // 0) > 0.50)) | length),
        records_with_mad_gt_0: ($all | map(select((.mad_ms // 0) > 0)) | length),
        max_cv: ($cvs | max),
        max_mad_ms: ($mads | max),
        max_stddev_ms: ($stddevs | max),
        max_p95_over_median: ($p95Ratios | max),
        by_track:
          ($cases
            | group_by(.track)
            | map({
                track: .[0].track,
                count: length,
                records_with_cv_gt_0_10: (map(select((.cv // 0) > 0.10)) | length),
                max_cv: (map(.cv // 0) | max),
                max_mad_ms: (map(.mad_ms // 0) | max),
                max_stddev_ms: (map(.stddev_ms // 0) | max)
              })),
        by_operation:
          ($cases
            | group_by(.operation)
            | map({
                operation: .[0].operation,
                count: length,
                records_with_cv_gt_0_10: (map(select((.cv // 0) > 0.10)) | length),
                max_cv: (map(.cv // 0) | max),
                max_p95_over_median:
                  (map(.p95_over_median) | map(select(. != null)) | max)
              })),
        top_cv_cases: ($cases | sort_by(.cv // 0) | reverse | .[0:20]),
        top_mad_cases: ($cases | sort_by(.mad_ms // 0) | reverse | .[0:20]),
        top_p95_over_median_cases:
          ($cases
            | map(select(.p95_over_median != null))
            | sort_by(.p95_over_median)
            | reverse
            | .[0:20]),
        notes: [
          "CV is stddev/mean from raw compiler samples; single-repeat quick runs normally produce zero CV.",
          "MAD is median absolute deviation in milliseconds, recomputed by verify_densematrix_bench.sh from compiler.jsonl.",
          "compiler_measured_to_elapsed_ratio guards against pure benchmark work being forced outside the timed sample window."
        ]
      }
  ' "$COMPILER_JSONL" >"$OUT_DIR/measurement-quality.json"

cat >"$OUT_DIR/api-coverage.csv" <<'CSV'
api,visibility,coverage_kind,compiler_operations,mathlib_operations,kernel_operations,correctness_or_static,shapes,elements,data_profiles,notes
DenseMatrix.structure_data,public_structure,benchmark_and_test,of;ofMatrix,construct,construction;suite,TEST roundtrip,square;zero_rows;zero_cols;wide;tall,Nat,deterministic,Vector-backed storage exercised through construction and conversion
DenseMatrix.rowMajorIndex,public_helper,benchmark_and_test,get;get!;set;set!;toMatrix;ofMatrix,get,access_update;conversion;suite,TEST get;set;roundtrip,square;zero_rows;zero_cols;wide;tall,Nat,deterministic,row-major offset exercised through checked and unchecked access paths
DenseMatrix.rowMajorIndex_lt,public_theorem,static_and_indirect,get;set;toMatrix;ofMatrix,get,access_update;conversion;suite,Lean build plus TEST checked access,square;zero_rows;zero_cols;wide;tall,Nat,deterministic,bounds proof compiled through checked indexing and conversions
DenseMatrix.get!,public_operation,benchmark_and_test,get!,get,access_update;suite,TEST get! example,square;zero_rows;zero_cols;wide;tall,Nat,deterministic,unchecked read fast path
DenseMatrix.set!,public_operation,benchmark_and_test,set!,not_applicable,access_update;suite,TEST set! example,square;zero_rows;zero_cols;wide;tall,Nat,deterministic,unchecked update fast path classified as dense-only
DenseMatrix.get,public_operation,benchmark_and_test,get,get,access_update;suite,TEST get example,square;zero_rows;zero_cols;wide;tall,Nat,deterministic,checked read path
DenseMatrix.set,public_operation,benchmark_and_test,set,not_applicable,access_update;suite,TEST set example,square;zero_rows;zero_cols;wide;tall,Nat,deterministic,checked update path classified as dense-only
DenseMatrix.ToString,public_instance,benchmark_and_test,toString,not_applicable,formatting;suite,TEST Rat toString,square;zero_rows;zero_cols;wide;tall,Nat;Rat,deterministic,bounded formatting benchmark avoids dominating large runs
DenseMatrix.toMatrix,public_operation,benchmark_and_test,toMatrix,construct;get,conversion;suite,TEST roundtrip,square;zero_rows;zero_cols;wide;tall,Nat,deterministic,dense to mathlib conversion
DenseMatrix.ofMatrix,public_operation,benchmark_and_test,ofMatrix,construct,conversion;suite,TEST roundtrip,square;zero_rows;zero_cols;wide;tall,Nat,deterministic,mathlib to dense conversion
DenseMatrix.toMatrix_ofMatrix,public_theorem,static_and_test,not_applicable,not_applicable,profile_densematrix_defs,TEST 2x3;2x0;0x3 roundtrip,square;zero_rows;zero_cols,Nat,not_applicable,roundtrip theorem checked by Lean and explicit examples
DenseMatrix.ofMatrix_toMatrix,public_theorem,static_and_test,not_applicable,not_applicable,profile_densematrix_defs,TEST dense roundtrip,square;wide,Nat,not_applicable,reverse roundtrip theorem checked by Lean and explicit example
DenseMatrix.of,public_operation,benchmark_and_test,of,construct,construction;suite,TEST values through roundtrip,square;zero_rows;zero_cols;wide;tall,Nat,deterministic,native row-major dense construction
DenseMatrix.add,public_operation,benchmark_and_test,add,add,arithmetic;data_profiles;suite,TEST Int add,square;zero_rows;zero_cols;wide;tall,Int;Rat,deterministic;zero;large_magnitude,addition compared against mathlib
DenseMatrix.smul,public_operation,benchmark_and_test,smul,smul,arithmetic;suite,TEST Int smul,square;zero_rows;zero_cols;wide;tall,Int,deterministic,scalar multiplication compared against mathlib expression baseline
DenseMatrix.dot,private_helper,benchmark_indirect,mul_square;mul_rect;mul_wide_inner;mul_tall_output;mul_skinny_inner,mul_square;mul_rect;mul_wide_inner;mul_tall_output;mul_skinny_inner,not_default_depth_limited,TEST Nat;Int;Rat multiplication,square;mul_wide_inner;mul_tall_output;mul_skinny_inner,Nat;Int;Rat,deterministic;zero;identity;large_magnitude,dot product hot path is covered through multiplication
DenseMatrix.mul_helper,private_helper,benchmark_indirect,mul_square;mul_rect;mul_wide_inner;mul_tall_output;mul_skinny_inner,mul_square;mul_rect;mul_wide_inner;mul_tall_output;mul_skinny_inner,not_default_depth_limited,TEST Nat;Int;Rat multiplication,square;mul_wide_inner;mul_tall_output;mul_skinny_inner,Nat;Int;Rat,deterministic;zero;identity;large_magnitude,sequential output builder covered through multiplication
DenseMatrix.mul,public_operation,benchmark_and_test,mul_square;mul_rect;mul_wide_inner;mul_tall_output;mul_skinny_inner,mul_square;mul_rect;mul_wide_inner;mul_tall_output;mul_skinny_inner,not_default_depth_limited,TEST Nat;Int;Rat multiplication,square;mul_wide_inner;mul_tall_output;mul_skinny_inner,Nat;Int;Rat,deterministic;zero;identity;large_magnitude,multiplication is compiler-benchmarked because kernel reduction is depth limited
DenseMatrix.transpose_helper,private_helper,benchmark_indirect,transpose;transpose_wide;transpose_tall,transpose;transpose_wide;transpose_tall,not_default_depth_limited,TEST Int transpose,square;wide;tall,Int,deterministic,sequential transpose builder covered through transpose
DenseMatrix.transpose,public_operation,benchmark_and_test,transpose;transpose_wide;transpose_tall,transpose;transpose_wide;transpose_tall,not_default_depth_limited,TEST Int transpose,square;wide;tall,Int,deterministic,transpose is compiler-benchmarked and mathlib-compared on nonempty shapes
DenseMatrix.rowEchelonForm,public_operation,benchmark_and_test,rowEchelonForm,rowEchelonForm,elimination;suite,TEST REF equality,square,Rat,deterministic,native dense row-echelon path with step checksum
DenseMatrix.reducedRowEchelonForm,public_operation,benchmark_and_test,reducedRowEchelonForm,reducedRowEchelonForm,elimination;suite,TEST RREF equality,square,Rat,deterministic,native dense reduced row-echelon path with step checksum
DenseMatrix.luFactorization,public_operation,benchmark_and_test,luFactorization,luFactorization,lu;suite,TEST LU equality;square reconstruction,square,Rat,deterministic,native dense LU path through dense REF steps
DenseMatrix.gaussDet,public_operation,benchmark_and_test,gaussDet,gaussDet,determinant;suite,TEST determinant correctness,square,Rat,deterministic,native dense determinant path
DenseMatrix.luDet,public_operation,benchmark_and_test,luDet,luDet,determinant;suite,TEST determinant correctness,square,Rat,deterministic,native dense LU determinant path
DenseMatrix.private_index_proofs,private_theorems,static_and_indirect,ofMatrix;toMatrix;get;set,get,conversion;access_update;profile_densematrix_defs,Lean build plus TEST roundtrip,square;zero_rows;zero_cols;wide;tall,Nat,not_applicable,division modulo and unflatten lemmas are checked by Lean and exercised by conversions
CSV

{
  echo "# DenseMatrix Benchmark Coverage"
  echo
  echo "## Compiler Tracks"
  echo
  echo "- profile=${RUN_PROFILE}"
  echo "- compiler_dense: DenseMatrix operations including deterministic data generation/setup cost."
  echo "- compiler_mathlib: mathlib Matrix baselines including matching deterministic data generation/setup cost."
  echo "- compiler_dense_prebuilt: DenseMatrix operations on prebuilt deterministic inputs, isolating operation cost."
  echo "- compiler_mathlib_prebuilt: mathlib Matrix baselines on prebuilt deterministic inputs, isolating operation cost."
  echo
  echo "## Shape Families"
  echo
  echo "- square: n x n"
  echo "- zero_rows: 0 x n for non-multiplication operations"
  echo "- zero_cols: n x 0 for non-multiplication operations"
  echo "- wide: n x 2n"
  echo "- tall: 2n x n"
  echo "- mul_wide_inner: n x 2n times 2n x n"
  echo "- mul_tall_output: 2n x n times n x n"
  echo "- mul_skinny_inner: n x 4 times 4 x n"
  echo
  echo "## Element Families"
  echo
  echo "- Nat: construction, conversion, read/update checksums, bounded toString, and multiplication."
  echo "- Int: add, scalar multiplication, transpose, and rectangular multiplication."
  echo "- Rat: add and square multiplication up to rat-max."
  echo
  echo "## Data Profiles"
  echo
  echo "- deterministic: seeded pseudo-random dense values used by the main suite."
  echo "- zero: all-zero add and multiplication cases."
  echo "- identity: square identity multiplication cases."
  echo "- large_magnitude: larger Nat/Int/Rat entries that stress arbitrary-precision arithmetic."
  echo
  echo "## Kernel Track"
  echo
  echo "- import baseline"
  echo "- #reduce construction/conversion/access-update/arithmetic/formatting/data-profile suites"
  echo "- lean --profile logs for DenseMatrix definitions and benchmark definitions"
  echo
  echo "## Machine-Readable Audit Files"
  echo
  echo "- api-coverage.csv: every public DenseMatrix API plus private hot paths mapped to compiler cases, mathlib baselines, kernel coverage, correctness checks, shapes, elements, and data profiles."
  echo "- bundle-manifest.csv and bundle-manifest.json: package file inventory with role, byte size, and sha256 for every non-self-referential bundle file."
  echo "- compiler-case-manifest.csv: every compiler benchmark case with setup policy and shape family."
  echo "- compiler-samples.csv: every raw compiler timing sample in nanoseconds for independent percentile/MAD/CV recomputation."
  echo "- compiler-throughput.csv: every compiler benchmark case normalized by rows*cols or rows*cols*inner work items, including median and p95 throughput."
  echo "- matrix-size-envelope.csv: grouped maximum rows, columns, inner dimensions, work items, and matrix cell counts by track, setup policy, shape family, operation, element, and data profile."
  echo "- dense-mathlib-pairs.csv: every directly comparable dense/mathlib pair with ratio and checksum status."
  echo "- dense-mathlib-summary.csv: per-operation DenseMatrix/mathlib ratio summaries with worst median and p95 cases."
  echo "- dense-only-cases.csv: DenseMatrix cases without a direct mathlib operation-level baseline."
  echo "- operation-scaling.csv: per-operation scaling summaries from minimum to maximum work items, including growth ratios and noise maxima."
  echo "- kernel-compiler-comparison.csv: kernel #reduce categories next to compiled runtime medians, including every requested kernel suite size and explicit exact/missing match status."
  echo "- kernel-profile-summary.csv: machine-readable Lean --profile cumulative hotspot timings for DenseMatrix definitions and benchmark definitions."
  echo "- compiler-process-metrics.json: machine-readable /usr/bin/time -v totals for elapsed time, CPU time, RSS, page faults, context switches, and file-system I/O."
  echo "- executable-artifact.json: machine-readable benchmark executable path, byte size, sha256, file output, and dynamic loader dependency output."
  echo "- measurement-quality.json: machine-readable sample-count, measured-sample-total, process-elapsed ratio, and noise audit, including CV/MAD/stddev distributions and top noisy compiler cases."
  echo "- benchmark-env.json: allowlisted benchmark-relevant environment variables, present/absent keys, and PATH hash."
  echo "- REPRODUCE.md: human-readable post-reboot rerun, verification, comparison, and reconstruction instructions."
  echo "- rerun.sh: executable rerun wrapper for the exact benchmark script invocation, with REPO_ROOT override support."
  echo "- run-config.json: machine-readable run mode, command, pinning, effective kernel sizes, and requested overrides."
  echo "- profile-plan.csv: machine-readable quick/full/stress/xl/mega run plan with default sizes, repeats, warmups, kernel sizes, maximum dimensions, and maximum work items."
  echo "- summary.json: record counts, maximum dimensions, pair counts, dense-only counts, checksum mismatch count, and compiler process metrics."
  echo "- SHA256SUMS: checksums for every file in the bundle."
  echo "- git-diff.patch plus git-untracked.patch: tracked and untracked worktree changes needed to reproduce this branch state."
  echo "- cgroup-before.txt and cgroup-after.txt: cgroup CPU, cpuset, memory, pids, IO, and pressure limits around the run."
  echo "- system-release.txt: OS release, glibc, ldd, locale, timezone, and ulimit summary."
  echo "- install-tools.txt and tune-system.txt: privileged setup transcripts with timeout status when optional install/tuning is requested."
  echo "- pinning-preflight.txt and pinning-postflight.txt: requested core, pin command, affinity, NUMA, and CPU topology evidence."
  echo "- tool-availability.json: machine-readable required and optional benchmark tool availability, paths, roles, and package hints."
} >"$OUT_DIR/coverage.md"

{
  echo "# DenseMatrix Benchmark Summary"
  echo
  echo "- Generated: $STAMP"
  echo "- Git: $GIT_SHORT"
  echo "- Core: $CORE"
  echo "- Compiler records: $(wc -l <"$COMPILER_JSONL")"
  echo "- Kernel records: $(wc -l <"$KERNEL_JSONL")"
  echo "- Profile: $RUN_PROFILE"
  echo "- Pin command: ${PIN_CMD[*]}"
  echo "- Sizes override: ${SIZES:-default}"
  echo "- Repeats override: ${REPEATS:-default}"
  echo "- Warmups override: ${WARMUPS:-default}"
  echo "- Rat max override: ${RAT_MAX:-default}"
  echo "- String max override: ${STRING_MAX:-default}"
  echo "- Data max override: ${DATA_MAX:-default}"
  echo "- Compiler JSONL: compiler.jsonl"
  echo "- Kernel JSONL: kernel.jsonl"
  echo "- Kernel profile summary: kernel-profile-summary.csv"
  echo "- Bundle manifest: bundle-manifest.csv and bundle-manifest.json"
  echo "- Executable artifact: executable-artifact.json"
  echo "- Benchmark environment: benchmark-env.json"
  echo "- System release: system-release.txt"
  echo "- Install tools transcript: install-tools.txt"
  echo "- Tune system transcript: tune-system.txt"
  echo "- Cgroup snapshots: cgroup-before.txt and cgroup-after.txt"
  echo "- API coverage manifest: api-coverage.csv"
  echo "- Matrix size envelope: matrix-size-envelope.csv"
  echo "- Reproduce instructions: REPRODUCE.md"
  echo "- Exact rerun wrapper: rerun.sh"
  echo "- Run config: run-config.json"
  echo "- Profile plan: profile-plan.csv"
  echo "- Tool availability: tool-availability.json"
  echo "- Measurement quality: measurement-quality.json"
  echo "- Compiler total time/RSS: compiler-time.txt"
  echo "- Compiler process metrics: compiler-process-metrics.json"
  if [[ -f "$PERF_LOG" ]]; then
    echo "- perf stat: perf-stat.txt"
  fi
  echo
  echo "## Fastest compiler medians"
  sort -t '"' -k 1 "$COMPILER_JSONL" >/dev/null 2>&1 || true
  if command -v jq >/dev/null 2>&1; then
    jq -s -r '
      .[0:25][]
      | "- \(.track) \(.operation) \(.element) \(.rows)x\(.cols): median=\(.median_ms)ms p95=\(.p95_ms)ms mean=\(.mean_ms)ms"
    ' "$COMPILER_JSONL"
    echo
    echo "## Machine audit"
    jq -r '
      "- compiler_records=\(.compiler_records)",
      "- compiler_sample_count=\(.compiler_sample_count)",
      "- compiler_sample_total_s=\(.compiler_sample_total_s)",
      "- compiler_measured_to_elapsed_ratio=\(.compiler_measured_to_elapsed_ratio)",
      "- data_profiles=\([.compiler_by_data_profile[].data_profile] | join(","))",
      "- pair_count=\(.dense_mathlib_pair_count)",
      "- dense_only_case_count=\(.dense_only_case_count)",
      "- checksum_mismatch_count=\(.dense_mathlib_checksum_mismatch_count)",
      "- dense_mathlib_median_ratio_max=\(.dense_mathlib_median_ratio_max)",
      "- dense_mathlib_p95_ratio_max=\(.dense_mathlib_p95_ratio_max)",
      "- compiler_scaling_group_count=\(.compiler_scaling_group_count)",
      "- max_rows=\(.compiler_max_rows) max_cols=\(.compiler_max_cols) max_inner=\(.compiler_max_inner) max_work_items=\(.compiler_max_work_items)",
      "- install_tools_requested=\(.install_tools_requested)",
      "- tune_system_requested=\(.tune_system_requested)",
      "- pkexec_timeout_seconds=\(.pkexec_timeout_seconds)",
      "- executable_sha256=\(.executable_artifact.sha256)",
      "- executable_bytes=\(.executable_artifact.bytes)"
    ' "$OUT_DIR/summary.json"
    jq -r '
      "- benchmark_env_path_sha256=\(.path_sha256)",
      "- benchmark_env_present_keys=\(.present_keys | join(","))"
    ' "$OUT_DIR/benchmark-env.json"
    jq -r '
      "- compiler_elapsed_s=\(.elapsed_s)",
      "- compiler_user_s=\(.user_s)",
      "- compiler_system_s=\(.system_s)",
      "- compiler_max_rss_kb=\(.max_rss_kb)",
      "- compiler_major_page_faults=\(.major_page_faults)",
      "- compiler_minor_page_faults=\(.minor_page_faults)",
      "- compiler_voluntary_context_switches=\(.voluntary_context_switches)",
      "- compiler_involuntary_context_switches=\(.involuntary_context_switches)"
    ' "$COMPILER_PROCESS_METRICS"
    jq -r '
      "- measurement_min_samples_per_record=\(.min_samples_per_record)",
      "- measurement_max_samples_per_record=\(.max_samples_per_record)",
      "- measurement_sample_total_s=\(.compiler_sample_total_s)",
      "- measurement_measured_to_elapsed_ratio=\(.compiler_measured_to_elapsed_ratio)",
      "- measurement_sample_count_declared_mismatch_count=\(.sample_count_declared_mismatch_count)",
      "- measurement_sample_count_repeat_mismatch_count=\(.sample_count_repeat_mismatch_count)",
      "- measurement_records_with_cv_gt_0_10=\(.records_with_cv_gt_0_10)",
      "- measurement_records_with_cv_gt_0_25=\(.records_with_cv_gt_0_25)",
      "- measurement_records_with_cv_gt_0_50=\(.records_with_cv_gt_0_50)",
      "- measurement_max_cv=\(.max_cv)",
      "- measurement_max_mad_ms=\(.max_mad_ms)",
      "- measurement_max_stddev_ms=\(.max_stddev_ms)"
    ' "$OUT_DIR/measurement-quality.json"
    jq -r '
      "- required_tools_available=\(.required_available)",
      "- optional_tools_missing=\(.optional_missing | join(","))"
    ' "$OUT_DIR/tool-availability.json"
    echo
    echo "## Dense vs mathlib median/p95 ratios"
    jq -s -r '
      def dataProfile: (.data_profile // "deterministic");
      def recKey: "\(.track)|\(.operation)|\(.element)|\(dataProfile)|\(.rows)|\(.cols)|\(.inner)";
      def baselineTrack:
        if .track == "compiler_dense" then "compiler_mathlib"
        elif .track == "compiler_dense_prebuilt" then "compiler_mathlib_prebuilt"
        else empty end;
      [
        . as $all
        | ($all
            | map(select(.track == "compiler_mathlib" or .track == "compiler_mathlib_prebuilt")
              | {key: recKey, value: .})
            | from_entries) as $baselines
        | $all[]
        | select(.track == "compiler_dense" or .track == "compiler_dense_prebuilt")
        | . as $dense
        | (baselineTrack) as $bt
        | ($dense | dataProfile) as $profile
        | ($baselines["\($bt)|\($dense.operation)|\($dense.element)|\($profile)|\($dense.rows)|\($dense.cols)|\($dense.inner)"] // empty) as $baseline
        | select($baseline != null)
        | "- \($dense.track) \($dense.operation) \($dense.element) profile=\($profile) \($dense.rows)x\($dense.cols) inner=\($dense.inner): median_dense=\($dense.median_ms)ms median_mathlib=\($baseline.median_ms)ms median_ratio=\(if $baseline.median_ms == 0 then "inf" else ($dense.median_ms / $baseline.median_ms) end) p95_dense=\($dense.p95_ms)ms p95_mathlib=\($baseline.p95_ms)ms p95_ratio=\(if $baseline.p95_ms == 0 then "inf" else ($dense.p95_ms / $baseline.p95_ms) end) checksum=\(if $dense.checksum == $baseline.checksum then "ok" else "mismatch" end)"
      ][0:60][]
    ' "$COMPILER_JSONL"
    echo
    echo "## Worst Dense vs mathlib groups"
    awk -F, '
      NR == 1 { next }
      {
        ratio = $16
        gsub(/"/, "", ratio)
        rows[NR] = $0
        ratios[NR] = ratio + 0
      }
      END {
        for (i = 0; i < 10; i++) {
          max_idx = 0
          max_val = -1
          for (row in ratios) {
            if (ratios[row] > max_val) {
              max_val = ratios[row]
              max_idx = row
            }
          }
          if (max_idx == 0) {
            break
          }
          split(rows[max_idx], f, ",")
          for (j = 1; j <= length(f); j++) {
            gsub(/^"|"$/, "", f[j])
          }
          printf("- %s %s %s %s %s profile=%s max_work=%s median_ratio_max=%s p95_ratio_max=%s worst_median=%sx%s inner=%s\n",
            f[1], f[4], f[5], f[6], f[3], f[7], f[12], f[16], f[20], f[22], f[23], f[24])
          delete ratios[max_idx]
        }
      }
    ' "$OUT_DIR/dense-mathlib-summary.csv"
    echo
    echo "## Largest operation scaling groups"
    awk -F, '
      NR == 1 { next }
      {
        work = $9
        gsub(/"/, "", work)
        rows[NR] = $0
        works[NR] = work + 0
      }
      END {
        for (i = 0; i < 10; i++) {
          max_idx = 0
          max_val = -1
          for (row in works) {
            if (works[row] > max_val) {
              max_val = works[row]
              max_idx = row
            }
          }
          if (max_idx == 0) {
            break
          }
          split(rows[max_idx], f, ",")
          for (j = 1; j <= length(f); j++) {
            gsub(/^"|"$/, "", f[j])
          }
          printf("- %s %s %s %s %s profile=%s work=%s..%s median_growth=%s p95_growth=%s max_cv=%s\n",
            f[1], f[3], f[4], f[5], f[2], f[6], f[8], f[9], f[18], f[21], f[22])
          delete works[max_idx]
        }
      }
    ' "$OUT_DIR/operation-scaling.csv"
  else
    head -n 25 "$COMPILER_JSONL"
  fi
} >"$OUT_DIR/summary.md"

ARCHIVE="$OUT_DIR.tar.gz"

cat >"$OUT_DIR/rerun.sh" <<SH
#!/usr/bin/env bash
set -euo pipefail

if [[ -n "\${REPO_ROOT:-}" ]]; then
  ROOT="\$REPO_ROOT"
else
  SELF_DIR="\$(cd "\$(dirname "\${BASH_SOURCE[0]}")" && pwd)"
  ROOT=""
  for candidate in "\$PWD" "\$SELF_DIR/../.." "\$SELF_DIR/.."; do
    if [[ -x "\$candidate/scripts/run_densematrix_bench.sh" ]]; then
      ROOT="\$(cd "\$candidate" && pwd)"
      break
    fi
  done
fi

if [[ -z "\${ROOT:-}" || ! -x "\$ROOT/scripts/run_densematrix_bench.sh" ]]; then
  echo "set REPO_ROOT to a checkout containing scripts/run_densematrix_bench.sh" >&2
  exit 2
fi

cd "\$ROOT"
$SCRIPT_INVOCATION
SH
chmod +x "$OUT_DIR/rerun.sh"

{
  echo "# Reproduce DenseMatrix Benchmark"
  echo
  echo "- Generated: $STAMP"
  echo "- Git: $GIT_SHORT"
  echo "- Profile: $RUN_PROFILE"
  echo "- Core: $CORE"
  echo "- Pin command: ${PIN_CMD[*]}"
  echo "- Bundle directory: $OUT_DIR"
  echo "- Bundle archive: $ARCHIVE"
  echo
  echo "## Exact Rerun"
  echo
  echo "From a checkout of this branch:"
  echo
  echo '```bash'
  echo "$SCRIPT_INVOCATION"
  echo '```'
  echo
  echo "From this extracted bundle, set REPO_ROOT if the checkout is not two directories above the bundle:"
  echo
  echo '```bash'
  echo "REPO_ROOT=/path/to/provable_computation ./rerun.sh"
  echo '```'
  echo
  echo "## Verify This Bundle"
  echo
  echo '```bash'
  echo "scripts/verify_densematrix_bench.sh $ARCHIVE"
  echo "scripts/verify_densematrix_bench.sh $OUT_DIR"
  echo '```'
  echo
  echo "## Compare Bundles"
  echo
  echo '```bash'
  echo "scripts/compare_densematrix_bench.sh --threshold 1.25 --out bench-results/densematrix-compare.csv bench-results/<baseline>.tar.gz bench-results/<current>.tar.gz"
  echo '```'
  echo
  echo "The comparison includes compiler median/p95, DenseMatrix/mathlib summary ratios, operation scaling summaries, kernel adjusted time, Lean --profile hotspots, executable artifact metadata, compiler process metrics, measurement-quality noise metrics, and matrix-size envelope coverage."
  echo
  echo "## Post-Reboot Long Runs"
  echo
  echo '```bash'
  echo "scripts/run_densematrix_bench.sh --install-tools --tune-system --core 2 --repeats 30 --warmups 5"
  echo "scripts/run_densematrix_bench.sh --install-tools --tune-system --core 2 --stress"
  echo "scripts/run_densematrix_bench.sh --install-tools --tune-system --core 2 --xl"
  echo "scripts/run_densematrix_bench.sh --install-tools --tune-system --core 2 --mega"
  echo '```'
  echo
  echo "Use pinning-preflight.txt and pinning-postflight.txt to confirm the process stayed on the requested core."
  echo "Use tool-availability.json to see whether numactl/perf were available or whether the run fell back to taskset."
  echo "Use install-tools.txt and tune-system.txt to audit pkexec setup attempts; override PKEXEC_TIMEOUT_SECONDS if local authorization needs more time."
  echo
  echo "## Reconstruct Branch State"
  echo
  echo "- git-diff.patch contains tracked worktree changes."
  echo "- git-untracked.patch contains untracked files captured with git diff --no-index."
  echo "- git-status.txt and git-rev-parse.txt identify the starting checkout state."
} >"$OUT_DIR/REPRODUCE.md"

write_bundle_manifest "$OUT_DIR"

(
  cd "$OUT_DIR"
  find . -type f ! -name SHA256SUMS -print0 | sort -z | xargs -0 sha256sum
) >"$OUT_DIR/SHA256SUMS"

tar -C "$OUT_PARENT" -czf "$ARCHIVE" "$(basename "$OUT_DIR")"
sha256sum "$ARCHIVE" >"$ARCHIVE.sha256"

echo "benchmark bundle: $ARCHIVE"
echo "checksum: $ARCHIVE.sha256"
