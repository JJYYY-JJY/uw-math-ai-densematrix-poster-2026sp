#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

OUT_PARENT="bench-results"
PROFILES="quick,full,stress,xl,mega"
CORE=2
INSTALL_TOOLS=0
TUNE_SYSTEM=0
PKEXEC_TIMEOUT_SECONDS="${PKEXEC_TIMEOUT_SECONDS:-60}"
ORIGINAL_ARGS=("$@")

usage() {
  cat <<'USAGE'
Usage: scripts/run_densematrix_suite.sh [options]

Runs a DenseMatrix benchmark profile suite, then packages all resulting profile
bundles into one suite archive.

Options:
  --profiles LIST      Comma-separated profiles (default: quick,full,stress,xl,mega).
                       Valid profiles: quick, full, stress, xl, mega.
  --core N             CPU core used for pinned benchmark runs (default: 2).
  --install-tools      Pass through optional pkexec tool installation to each profile.
  --tune-system        Pass through optional pkexec CPU governor tuning to each profile.
  --pkexec-timeout N   PKEXEC_TIMEOUT_SECONDS passed to child benchmark runs.
  --out-dir DIR        Parent directory for profile results and final suite package.
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

trim_spaces() {
  tr -d '[:space:]'
}

run_profile() {
  local profile="$1"
  local run_parent="$2"
  local log="$run_parent/${profile}.log"
  local args=(--core "$CORE" --out-dir "$run_parent/profile-results")

  if [[ "$INSTALL_TOOLS" -eq 1 ]]; then
    args+=(--install-tools)
  fi
  if [[ "$TUNE_SYSTEM" -eq 1 ]]; then
    args+=(--tune-system)
  fi

  case "$profile" in
    quick)
      args+=(--quick)
      ;;
    full)
      args+=(--repeats 30 --warmups 5)
      ;;
    stress)
      args+=(--stress)
      ;;
    xl)
      args+=(--xl)
      ;;
    mega)
      args+=(--mega)
      ;;
    *)
      echo "unknown suite profile: $profile" >&2
      exit 2
      ;;
  esac

  echo "running DenseMatrix suite profile: $profile" >&2
  set +e
  PKEXEC_TIMEOUT_SECONDS="$PKEXEC_TIMEOUT_SECONDS" \
    "$ROOT/scripts/run_densematrix_bench.sh" "${args[@]}" 2>&1 | tee "$log" >&2
  local status="${PIPESTATUS[0]}"
  set -e
  if [[ "$status" -ne 0 ]]; then
    echo "profile failed: $profile (exit $status), see $log" >&2
    exit "$status"
  fi

  local archive
  archive="$(awk '/^benchmark bundle:/ { print $3 }' "$log" | tail -n 1)"
  if [[ -z "$archive" || ! -f "$archive" ]]; then
    echo "could not find generated archive for profile $profile in $log" >&2
    exit 1
  fi
  echo "$archive"
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --profiles)
      PROFILES="${2:?--profiles requires a comma-separated value}"
      shift 2
      ;;
    --core)
      CORE="${2:?--core requires a value}"
      shift 2
      ;;
    --install-tools)
      INSTALL_TOOLS=1
      shift
      ;;
    --tune-system)
      TUNE_SYSTEM=1
      shift
      ;;
    --pkexec-timeout)
      PKEXEC_TIMEOUT_SECONDS="${2:?--pkexec-timeout requires a value}"
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

if [[ ! "$CORE" =~ ^[0-9]+$ ]]; then
  echo "--core must be a natural number" >&2
  exit 2
fi
if [[ ! "$PKEXEC_TIMEOUT_SECONDS" =~ ^[0-9]+$ || "$PKEXEC_TIMEOUT_SECONDS" -lt 1 ]]; then
  echo "--pkexec-timeout must be a positive integer" >&2
  exit 2
fi

need_cmd "$ROOT/scripts/run_densematrix_bench.sh"
need_cmd "$ROOT/scripts/package_densematrix_suite.sh"
need_cmd "$ROOT/scripts/verify_densematrix_suite.sh"
need_cmd tee
need_cmd awk

mkdir -p "$OUT_PARENT"
STAMP="$(date -u +%Y%m%dT%H%M%SZ)"
GIT_SHORT="$(git rev-parse --short HEAD 2>/dev/null || echo unknown)"
RUN_PARENT="$OUT_PARENT/densematrix-suite-run-${STAMP}-${GIT_SHORT}"
mkdir -p "$RUN_PARENT/profile-results"

IFS=',' read -ra raw_profiles <<< "$PROFILES"
profiles=()
for raw in "${raw_profiles[@]}"; do
  profile="$(printf '%s' "$raw" | trim_spaces)"
  [[ -n "$profile" ]] || continue
  case "$profile" in
    quick|full|stress|xl|mega)
      profiles+=("$profile")
      ;;
    *)
      echo "unknown suite profile: $profile" >&2
      exit 2
      ;;
  esac
done

if [[ "${#profiles[@]}" -lt 1 ]]; then
  echo "--profiles did not contain any valid profile names" >&2
  exit 2
fi

{
  echo "\$ scripts/run_densematrix_suite.sh ${ORIGINAL_ARGS[*]}"
  echo "generated_at_utc=$STAMP"
  echo "git=$GIT_SHORT"
  echo "profiles=${profiles[*]}"
  echo "core=$CORE"
  echo "install_tools=$INSTALL_TOOLS"
  echo "tune_system=$TUNE_SYSTEM"
  echo "pkexec_timeout_seconds=$PKEXEC_TIMEOUT_SECONDS"
} >"$RUN_PARENT/suite-run-config.txt"

archives=()
for profile in "${profiles[@]}"; do
  archive="$(run_profile "$profile" "$RUN_PARENT" | tail -n 1)"
  archives+=("$archive")
done

package_log="$RUN_PARENT/package.log"
set +e
"$ROOT/scripts/package_densematrix_suite.sh" --out-dir "$OUT_PARENT" "${archives[@]}" 2>&1 | tee "$package_log"
package_status="${PIPESTATUS[0]}"
set -e
if [[ "$package_status" -ne 0 ]]; then
  echo "suite packaging failed, see $package_log" >&2
  exit "$package_status"
fi

suite_archive="$(awk '/^suite package:/ { print $3 }' "$package_log" | tail -n 1)"
if [[ -z "$suite_archive" || ! -f "$suite_archive" ]]; then
  echo "could not find generated suite archive in $package_log" >&2
  exit 1
fi

"$ROOT/scripts/verify_densematrix_suite.sh" "$suite_archive"

echo "suite package: $suite_archive"
echo "checksum: $suite_archive.sha256"
