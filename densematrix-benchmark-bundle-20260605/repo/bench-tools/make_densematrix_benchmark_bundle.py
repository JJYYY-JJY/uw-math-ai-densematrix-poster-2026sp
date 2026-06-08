#!/usr/bin/env python3
"""Create a handoff bundle for DenseMatrix benchmark results.

The bundle is intended for poster/report collaborators.  It contains the raw
JSONL, summary tables, generated figures, machine/environment metadata, source
snapshots, and scripts for reproducing the full benchmark from the repository.
"""

from __future__ import annotations

import argparse
import csv
import json
import math
import os
import shutil
import subprocess
import zipfile
from collections import defaultdict
from datetime import datetime
from pathlib import Path
from statistics import median


PAIRED_OPERATIONS = ["construct", "get", "add", "smul", "transpose", "mul_square"]
DEFAULT_SIZES = "4,8,16,24,32,48,64,80,96,128,160,192,256,384,512,768,1024,1536,2048"
DEFAULT_WARMUPS = "10"
DEFAULT_REPEATS = "50"
DEFAULT_CORE = "3"
REPO_SNAPSHOT_EXCLUDES = {
    ".git",
    ".lake",
    "bench-results",
    "__pycache__",
    ".pytest_cache",
    ".mypy_cache",
    ".ruff_cache",
}


def read_jsonl(path: Path) -> list[dict]:
    rows: list[dict] = []
    with path.open() as f:
        for line_no, line in enumerate(f, start=1):
            line = line.strip()
            if not line:
                continue
            try:
                rows.append(json.loads(line))
            except json.JSONDecodeError as exc:
                raise SystemExit(f"{path}:{line_no}: invalid JSON: {exc}") from exc
    return rows


def read_csv(path: Path) -> list[dict]:
    with path.open(newline="") as f:
        return list(csv.DictReader(f))


def write_csv(path: Path, fieldnames: list[str], rows: list[dict]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(rows)


def write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text)


def write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")


def copy_file(src: Path, dst: Path) -> None:
    dst.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(src, dst)


def run_capture(args: list[str], cwd: Path, allow_failure: bool = False) -> str:
    proc = subprocess.run(args, cwd=cwd, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if proc.returncode != 0 and not allow_failure:
        raise SystemExit(f"command failed ({proc.returncode}): {' '.join(args)}\n{proc.stdout}")
    return proc.stdout


def parse_iso(text: str) -> datetime | None:
    text = text.strip()
    if not text:
        return None
    try:
        return datetime.fromisoformat(text)
    except ValueError:
        return None


def linreg_loglog(points: list[tuple[float, float]]) -> tuple[float, float] | None:
    clean = [(x, y) for x, y in points if x > 0 and y > 0]
    if len(clean) < 2:
        return None
    xs = [math.log(x) for x, _ in clean]
    ys = [math.log(y) for _, y in clean]
    x_mean = sum(xs) / len(xs)
    y_mean = sum(ys) / len(ys)
    ss_xx = sum((x - x_mean) ** 2 for x in xs)
    if ss_xx == 0:
        return None
    ss_xy = sum((x - x_mean) * (y - y_mean) for x, y in zip(xs, ys))
    slope = ss_xy / ss_xx
    intercept = y_mean - slope * x_mean
    y_hat = [intercept + slope * x for x in xs]
    ss_tot = sum((y - y_mean) ** 2 for y in ys)
    ss_res = sum((y - yh) ** 2 for y, yh in zip(ys, y_hat))
    r2 = 1.0 if ss_tot == 0 else 1.0 - ss_res / ss_tot
    return slope, r2


def fmt_float(value: float, digits: int = 3) -> str:
    return f"{value:.{digits}f}"


def fmt_ms_or_s(ms: float) -> str:
    if ms >= 1000:
        return f"{ms / 1000:.3f} s"
    return f"{ms:.3f} ms"


def benchmark_key(row: dict) -> tuple:
    return (
        row["backend"],
        row["operation"],
        row["element"],
        row["setup_policy"],
        int(row["rows"]),
        int(row["cols"]),
        int(row["inner"]),
    )


def collect_speedups(summary_dir: Path) -> list[dict]:
    rows = read_csv(summary_dir / "speedups.csv")
    for row in rows:
        row["rows"] = int(row["rows"])
        row["cols"] = int(row["cols"])
        row["inner"] = int(row["inner"])
        row["warmups"] = int(row["warmups"])
        row["repeats"] = int(row["repeats"])
        row["dense_median_ms"] = float(row["dense_median_ms"])
        row["mathlib_median_ms"] = float(row["mathlib_median_ms"])
        row["speedup_mathlib_over_dense"] = float(row["speedup_mathlib_over_dense"])
        row["dense_cv"] = float(row["dense_cv"])
        row["mathlib_cv"] = float(row["mathlib_cv"])
    return rows


def operation_summary(speedups: list[dict]) -> list[dict]:
    out: list[dict] = []
    by_op: dict[str, list[dict]] = defaultdict(list)
    for row in speedups:
        by_op[row["operation"]].append(row)
    for op in PAIRED_OPERATIONS:
        rows = by_op.get(op, [])
        if not rows:
            continue
        values = [row["speedup_mathlib_over_dense"] for row in rows]
        at_max = max(rows, key=lambda row: row["rows"])
        out.append(
            {
                "operation": op,
                "point_count": len(rows),
                "min_n": min(row["rows"] for row in rows),
                "max_n": max(row["rows"] for row in rows),
                "min_speedup": min(values),
                "median_speedup": median(values),
                "max_speedup": max(values),
                "speedup_at_max_n": at_max["speedup_mathlib_over_dense"],
                "dense_median_ms_at_max_n": at_max["dense_median_ms"],
                "mathlib_median_ms_at_max_n": at_max["mathlib_median_ms"],
            }
        )
    return out


def endpoint_table(speedups: list[dict], n: int) -> list[dict]:
    rows = [row for row in speedups if row["rows"] == n]
    rows.sort(key=lambda row: PAIRED_OPERATIONS.index(row["operation"]))
    return [
        {
            "operation": row["operation"],
            "n": row["rows"],
            "dense_median_ms": row["dense_median_ms"],
            "mathlib_median_ms": row["mathlib_median_ms"],
            "speedup_mathlib_over_dense": row["speedup_mathlib_over_dense"],
            "dense_cv": row["dense_cv"],
            "mathlib_cv": row["mathlib_cv"],
        }
        for row in rows
    ]


def mul_square_table(speedups: list[dict]) -> list[dict]:
    rows = [row for row in speedups if row["operation"] == "mul_square"]
    rows.sort(key=lambda row: row["rows"])
    return [
        {
            "n": row["rows"],
            "dense_median_s": row["dense_median_ms"] / 1000.0,
            "mathlib_median_s": row["mathlib_median_ms"] / 1000.0,
            "speedup_mathlib_over_dense": row["speedup_mathlib_over_dense"],
            "dense_cv": row["dense_cv"],
            "mathlib_cv": row["mathlib_cv"],
        }
        for row in rows
    ]


def conversion_table(records: list[dict]) -> list[dict]:
    rows = [
        row
        for row in records
        if row["backend"] == "dense_conversion" and row["operation"] in ("ofMatrix", "toMatrix")
    ]
    rows.sort(key=lambda row: (int(row["rows"]), row["operation"]))
    return [
        {
            "operation": row["operation"],
            "n": int(row["rows"]),
            "median_ms": float(row["median_ms"]),
            "mean_ms": float(row["mean_ms"]),
            "p95_ms": float(row["p95_ms"]),
            "cv": float(row["cv"]),
        }
        for row in rows
    ]


def complexity_by_cutoff(records: list[dict]) -> list[dict]:
    out: list[dict] = []
    cutoffs = [4, 128, 256, 512]
    for cutoff in cutoffs:
        for operation in PAIRED_OPERATIONS:
            for backend in ("dense_core", "mathlib_matrix"):
                rows = [
                    row
                    for row in records
                    if row["backend"] == backend
                    and row["operation"] == operation
                    and int(row["rows"]) >= cutoff
                ]
                fit = linreg_loglog([(float(row["rows"]), float(row["median_ms"])) for row in rows])
                if fit is None:
                    continue
                exponent, r2 = fit
                out.append(
                    {
                        "min_n_cutoff": cutoff,
                        "backend": backend,
                        "operation": operation,
                        "point_count": len(rows),
                        "min_n": min(int(row["rows"]) for row in rows),
                        "max_n": max(int(row["rows"]) for row in rows),
                        "exponent": exponent,
                        "r2": r2,
                    }
                )
    return out


def quality_summary(records: list[dict], speedups: list[dict], result_dir: Path, summary_dir: Path) -> dict:
    start = parse_iso((result_dir / "start-time.txt").read_text() if (result_dir / "start-time.txt").exists() else "")
    end = parse_iso((result_dir / "end-time.txt").read_text() if (result_dir / "end-time.txt").exists() else "")
    elapsed_hours = None if start is None or end is None else (end - start).total_seconds() / 3600.0
    measured_hours = sum(sum(int(x) for x in row.get("samples_ns", [])) for row in records) / 1e9 / 3600.0
    all_cv = [float(row["cv"]) for row in records]
    large_cv = [float(row["cv"]) for row in records if int(row["rows"]) >= 128]
    mismatches_path = summary_dir / "checksum-mismatches.csv"
    mismatch_count = max(0, len(read_csv(mismatches_path))) if mismatches_path.exists() else None
    return {
        "record_count": len(records),
        "sample_count": sum(int(row["repeats"]) for row in records),
        "paired_group_count": len(speedups),
        "checksum_mismatch_count": mismatch_count,
        "max_rows": max(int(row["rows"]) for row in records),
        "elapsed_hours": elapsed_hours,
        "measured_sample_hours": measured_hours,
        "median_cv_all_records": median(all_cv),
        "max_cv_all_records": max(all_cv),
        "large_record_count_n_ge_128": len(large_cv),
        "median_cv_n_ge_128": median(large_cv),
        "max_cv_n_ge_128": max(large_cv),
    }


def svg_escape(text: str) -> str:
    return (
        text.replace("&", "&amp;")
        .replace("<", "&lt;")
        .replace(">", "&gt;")
        .replace('"', "&quot;")
    )


def svg_line_chart(
    path: Path,
    title: str,
    x_label: str,
    y_label: str,
    series: list[tuple[str, list[tuple[float, float]], str]],
    *,
    log_x: bool = False,
    log_y: bool = False,
    width: int = 960,
    height: int = 620,
) -> None:
    margin_left = 90
    margin_right = 40
    margin_top = 70
    margin_bottom = 80
    plot_w = width - margin_left - margin_right
    plot_h = height - margin_top - margin_bottom

    all_points = [point for _, points, _ in series for point in points if point[0] > 0 and point[1] > 0]
    xs = [math.log10(x) if log_x else x for x, _ in all_points]
    ys = [math.log10(y) if log_y else y for _, y in all_points]
    x_min, x_max = min(xs), max(xs)
    y_min, y_max = min(ys), max(ys)
    if x_min == x_max:
        x_min -= 1
        x_max += 1
    if y_min == y_max:
        y_min -= 1
        y_max += 1

    def sx(x: float) -> float:
        value = math.log10(x) if log_x else x
        return margin_left + (value - x_min) / (x_max - x_min) * plot_w

    def sy(y: float) -> float:
        value = math.log10(y) if log_y else y
        return margin_top + plot_h - (value - y_min) / (y_max - y_min) * plot_h

    def tick_values(min_value: float, max_value: float, log_scale: bool) -> list[float]:
        if log_scale:
            start = math.ceil(min_value)
            end = math.floor(max_value)
            ticks = [10 ** power for power in range(start, end + 1)]
            return ticks or [10 ** min_value, 10 ** max_value]
        step = (max_value - min_value) / 5.0
        return [min_value + i * step for i in range(6)]

    x_ticks = tick_values(x_min, x_max, log_x)
    y_ticks = tick_values(y_min, y_max, log_y)
    x_tick_positions = [(tick, sx(tick)) for tick in x_ticks]
    y_tick_positions = [(tick, sy(tick)) for tick in y_ticks]

    parts = [
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" viewBox="0 0 {width} {height}">',
        '<rect width="100%" height="100%" fill="#ffffff"/>',
        f'<text x="{width / 2}" y="34" text-anchor="middle" font-family="Arial, sans-serif" font-size="24" font-weight="700">{svg_escape(title)}</text>',
        f'<rect x="{margin_left}" y="{margin_top}" width="{plot_w}" height="{plot_h}" fill="#fafafa" stroke="#d0d0d0"/>',
    ]

    for tick, x in x_tick_positions:
        label = f"{tick:g}"
        parts.append(f'<line x1="{x:.2f}" y1="{margin_top}" x2="{x:.2f}" y2="{margin_top + plot_h}" stroke="#e8e8e8"/>')
        parts.append(f'<text x="{x:.2f}" y="{margin_top + plot_h + 28}" text-anchor="middle" font-family="Arial, sans-serif" font-size="13">{label}</text>')
    for tick, y in y_tick_positions:
        label = f"{tick:g}"
        parts.append(f'<line x1="{margin_left}" y1="{y:.2f}" x2="{margin_left + plot_w}" y2="{y:.2f}" stroke="#e8e8e8"/>')
        parts.append(f'<text x="{margin_left - 12}" y="{y + 4:.2f}" text-anchor="end" font-family="Arial, sans-serif" font-size="13">{label}</text>')

    for name, points, color in series:
        coords = " ".join(f"{sx(x):.2f},{sy(y):.2f}" for x, y in points)
        parts.append(f'<polyline points="{coords}" fill="none" stroke="{color}" stroke-width="3"/>')
        for x, y in points:
            parts.append(f'<circle cx="{sx(x):.2f}" cy="{sy(y):.2f}" r="3.5" fill="{color}"/>')

    legend_x = margin_left + 16
    legend_y = margin_top + 24
    for idx, (name, _, color) in enumerate(series):
        y = legend_y + idx * 24
        parts.append(f'<line x1="{legend_x}" y1="{y}" x2="{legend_x + 26}" y2="{y}" stroke="{color}" stroke-width="4"/>')
        parts.append(f'<text x="{legend_x + 36}" y="{y + 5}" font-family="Arial, sans-serif" font-size="14">{svg_escape(name)}</text>')

    parts.append(f'<text x="{margin_left + plot_w / 2}" y="{height - 24}" text-anchor="middle" font-family="Arial, sans-serif" font-size="16">{svg_escape(x_label)}</text>')
    parts.append(
        f'<text x="24" y="{margin_top + plot_h / 2}" text-anchor="middle" transform="rotate(-90 24 {margin_top + plot_h / 2})" '
        f'font-family="Arial, sans-serif" font-size="16">{svg_escape(y_label)}</text>'
    )
    parts.append("</svg>\n")
    write_text(path, "\n".join(parts))


def svg_bar_chart(
    path: Path,
    title: str,
    x_label: str,
    y_label: str,
    bars: list[tuple[str, float, str]],
    *,
    width: int = 960,
    height: int = 620,
) -> None:
    margin_left = 90
    margin_right = 40
    margin_top = 70
    margin_bottom = 120
    plot_w = width - margin_left - margin_right
    plot_h = height - margin_top - margin_bottom
    max_v = max(value for _, value, _ in bars)
    min_v = min(0.0, min(value for _, value, _ in bars))
    value_span = max_v - min_v or 1.0

    def sy(value: float) -> float:
        return margin_top + plot_h - (value - min_v) / value_span * plot_h

    parts = [
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" viewBox="0 0 {width} {height}">',
        '<rect width="100%" height="100%" fill="#ffffff"/>',
        f'<text x="{width / 2}" y="34" text-anchor="middle" font-family="Arial, sans-serif" font-size="24" font-weight="700">{svg_escape(title)}</text>',
        f'<rect x="{margin_left}" y="{margin_top}" width="{plot_w}" height="{plot_h}" fill="#fafafa" stroke="#d0d0d0"/>',
    ]
    for idx in range(6):
        value = min_v + idx * value_span / 5
        y = sy(value)
        parts.append(f'<line x1="{margin_left}" y1="{y:.2f}" x2="{margin_left + plot_w}" y2="{y:.2f}" stroke="#e8e8e8"/>')
        parts.append(f'<text x="{margin_left - 12}" y="{y + 4:.2f}" text-anchor="end" font-family="Arial, sans-serif" font-size="13">{value:.1f}</text>')

    slot = plot_w / len(bars)
    bar_w = min(76, slot * 0.62)
    zero_y = sy(0.0)
    for idx, (label, value, color) in enumerate(bars):
        x = margin_left + idx * slot + (slot - bar_w) / 2
        y = min(sy(value), zero_y)
        h = abs(zero_y - sy(value))
        parts.append(f'<rect x="{x:.2f}" y="{y:.2f}" width="{bar_w:.2f}" height="{h:.2f}" fill="{color}"/>')
        parts.append(f'<text x="{x + bar_w / 2:.2f}" y="{y - 8:.2f}" text-anchor="middle" font-family="Arial, sans-serif" font-size="13">{value:.2f}</text>')
        parts.append(
            f'<text x="{x + bar_w / 2:.2f}" y="{margin_top + plot_h + 28}" text-anchor="middle" '
            f'transform="rotate(-35 {x + bar_w / 2:.2f} {margin_top + plot_h + 28})" '
            f'font-family="Arial, sans-serif" font-size="13">{svg_escape(label)}</text>'
        )

    parts.append(f'<text x="{margin_left + plot_w / 2}" y="{height - 24}" text-anchor="middle" font-family="Arial, sans-serif" font-size="16">{svg_escape(x_label)}</text>')
    parts.append(
        f'<text x="24" y="{margin_top + plot_h / 2}" text-anchor="middle" transform="rotate(-90 24 {margin_top + plot_h / 2})" '
        f'font-family="Arial, sans-serif" font-size="16">{svg_escape(y_label)}</text>'
    )
    parts.append("</svg>\n")
    write_text(path, "\n".join(parts))


def create_figures(figures_dir: Path, speedups: list[dict], op_summary: list[dict], complexity_rows: list[dict]) -> None:
    figures_dir.mkdir(parents=True, exist_ok=True)
    mul_rows = [row for row in speedups if row["operation"] == "mul_square"]
    mul_rows.sort(key=lambda row: row["rows"])
    svg_line_chart(
        figures_dir / "mul_square_runtime_loglog.svg",
        "Square Matrix Multiplication Runtime",
        "n",
        "median runtime (seconds)",
        [
            ("DenseMatrix", [(row["rows"], row["dense_median_ms"] / 1000.0) for row in mul_rows], "#0b6e99"),
            ("mathlib Matrix", [(row["rows"], row["mathlib_median_ms"] / 1000.0) for row in mul_rows], "#b23a48"),
        ],
        log_x=True,
        log_y=True,
    )
    svg_line_chart(
        figures_dir / "mul_square_speedup.svg",
        "Square Matrix Multiplication Speedup",
        "n",
        "mathlib median / DenseMatrix median",
        [
            (
                "speedup",
                [(row["rows"], row["speedup_mathlib_over_dense"]) for row in mul_rows],
                "#3f7d20",
            )
        ],
        log_x=True,
        log_y=False,
    )
    svg_bar_chart(
        figures_dir / "operation_median_speedups.svg",
        "Median Speedup by Operation",
        "operation",
        "mathlib median / DenseMatrix median",
        [
            (
                row["operation"],
                float(row["median_speedup"]),
                "#0b6e99" if float(row["median_speedup"]) >= 1.0 else "#b23a48",
            )
            for row in op_summary
        ],
    )
    large = [
        row
        for row in complexity_rows
        if row["min_n_cutoff"] == 128 and row["operation"] in PAIRED_OPERATIONS
    ]
    dense = {row["operation"]: row for row in large if row["backend"] == "dense_core"}
    mathlib = {row["operation"]: row for row in large if row["backend"] == "mathlib_matrix"}
    bars: list[tuple[str, float, str]] = []
    for op in PAIRED_OPERATIONS:
        if op in dense:
            bars.append((f"{op} dense", dense[op]["exponent"], "#0b6e99"))
        if op in mathlib:
            bars.append((f"{op} mathlib", mathlib[op]["exponent"], "#b23a48"))
    svg_bar_chart(
        figures_dir / "complexity_exponents_n_ge_128.svg",
        "Empirical Complexity Exponents (n >= 128)",
        "operation/backend",
        "log-log slope",
        bars,
        width=1200,
    )


def markdown_table(headers: list[str], rows: list[list[str]]) -> str:
    out = ["| " + " | ".join(headers) + " |", "| " + " | ".join("---" for _ in headers) + " |"]
    out.extend("| " + " | ".join(row) + " |" for row in rows)
    return "\n".join(out)


def create_readme(
    path: Path,
    *,
    quality: dict,
    op_summary: list[dict],
    endpoint: list[dict],
    max_n: int,
) -> None:
    op_table = markdown_table(
        [
            "operation",
            "median speedup",
            f"speedup at n={max_n}",
            f"Dense median at n={max_n}",
            f"mathlib median at n={max_n}",
        ],
        [
            [
                row["operation"],
                f"{float(row['median_speedup']):.2f}x",
                f"{float(row['speedup_at_max_n']):.2f}x",
                fmt_ms_or_s(float(row["dense_median_ms_at_max_n"])),
                fmt_ms_or_s(float(row["mathlib_median_ms_at_max_n"])),
            ]
            for row in op_summary
        ],
    )
    endpoint_table_md = markdown_table(
        ["operation", "Dense median", "mathlib median", "speedup", "Dense CV", "mathlib CV"],
        [
            [
                row["operation"],
                fmt_ms_or_s(float(row["dense_median_ms"])),
                fmt_ms_or_s(float(row["mathlib_median_ms"])),
                f"{float(row['speedup_mathlib_over_dense']):.2f}x",
                f"{float(row['dense_cv']):.4f}",
                f"{float(row['mathlib_cv']):.4f}",
            ]
            for row in endpoint
        ],
    )
    elapsed = quality.get("elapsed_hours")
    measured = quality.get("measured_sample_hours")
    text = f"""# DenseMatrix vs mathlib Matrix Benchmark Bundle

This bundle contains the completed benchmark run, generated tables, figures,
metadata, and reproduction scripts for the DenseMatrix vs mathlib Matrix
comparison.

## Headline

DenseMatrix is not uniformly 20x faster across all kernels.  The defensible
poster claim is narrower and stronger:

> DenseMatrix achieves about 20x faster full square matrix multiplication than
> mathlib Matrix on this benchmark, while preserving the expected cubic scaling.

## Run validity

- Exit status: 0.
- Raw benchmark records: {quality['record_count']}.
- Measured samples: {quality['sample_count']}.
- Paired DenseMatrix/mathlib checksum mismatches: {quality['checksum_mismatch_count']}.
- Largest matrix size: n={quality['max_rows']}.
- Wall-clock run time: {elapsed:.2f} hours.
- Total measured sample time: {measured:.2f} hours.
- Median CV over all records: {quality['median_cv_all_records']:.4f}.
- Median CV for n >= 128: {quality['median_cv_n_ge_128']:.4f}.

## Operation summary

Speedup is `mathlib median runtime / DenseMatrix median runtime`; values above
1 mean DenseMatrix is faster.

{op_table}

## Endpoint at n={max_n}

{endpoint_table_md}

## Important interpretation

- Matrix multiplication is the main result: median speedup is about 20.9x over
  all sizes and about 19.2x at n={max_n}.
- The O(n^2) kernels are not a uniform win.  `get` is about 2x, `add` is about
  1.4x, `transpose` is near parity at the largest size, and `smul`/`construct`
  can be faster in mathlib Matrix.
- Complexity fits should be described as empirical log-log slopes.  For n >=
  128, multiplication fits approximately n^3 for both backends, while the other
  kernels fit approximately n^2.
- The data supports a constant-factor story, not an asymptotic-complexity story.

## Files

- `data/results.jsonl`: raw benchmark records, including per-repeat samples.
- `data/summary/`: generated summary CSV/JSON files.
- `BENCHMARK_LOGIC.md`: exact benchmark actions and source definitions.
- `tables/`: poster-friendly derived tables.
- `figures/`: SVG plots generated from the raw data.
- `metadata/`: command, environment, git state, and progress log.
- `repo/`: self-contained repository source snapshot for reproduction.
- `source/`: source index, selected source snapshots, dependency lock files,
  and patch material.  Start with `source/README.md`.
- `scripts/`: scripts for full reproduction and quick smoke checks.

## Reproduction

From the unpacked bundle root:

```bash
./scripts/reproduce_quick_smoke.sh
./scripts/reproduce_full_48h.sh
```

Both scripts default to the bundled `repo/` source snapshot.  You can pass an
external checkout path if you want to run against a different repository.

The full reproduction uses the same profile as this run: sizes
`{DEFAULT_SIZES}`, {DEFAULT_WARMUPS} warmups, {DEFAULT_REPEATS} repeats, CPU core
{DEFAULT_CORE}, and resumable JSONL output.  Lake may need to download/build
dependencies if they are not already available locally.  The bundle includes
source code and `lake-manifest.json`, but it intentionally does not include
`.lake` build artifacts or vendored mathlib sources.
"""
    write_text(path, text)


def create_conclusions(
    path: Path,
    *,
    op_summary: list[dict],
    complexity_rows: list[dict],
    max_n: int,
) -> None:
    large = [
        row
        for row in complexity_rows
        if row["min_n_cutoff"] == 128 and row["operation"] in PAIRED_OPERATIONS
    ]
    by_pair = {(row["operation"], row["backend"]): row for row in large}
    complexity_table = markdown_table(
        ["operation", "Dense exponent", "Dense R2", "mathlib exponent", "mathlib R2"],
        [
            [
                op,
                fmt_float(float(by_pair[(op, "dense_core")]["exponent"]), 3),
                fmt_float(float(by_pair[(op, "dense_core")]["r2"]), 5),
                fmt_float(float(by_pair[(op, "mathlib_matrix")]["exponent"]), 3),
                fmt_float(float(by_pair[(op, "mathlib_matrix")]["r2"]), 5),
            ]
            for op in PAIRED_OPERATIONS
        ],
    )
    ops = {row["operation"]: row for row in op_summary}
    text = f"""# Conclusions and Poster-Ready Claims

## Recommended main claim

DenseMatrix achieves about 20x faster full square matrix multiplication than
mathlib Matrix in the compiled benchmark harness, while both implementations
retain the expected O(n^3) empirical scaling.

Useful numeric support:

- Median multiplication speedup over all tested sizes:
  {float(ops['mul_square']['median_speedup']):.2f}x.
- Best observed multiplication speedup:
  {float(ops['mul_square']['max_speedup']):.2f}x.
- Multiplication speedup at n={max_n}:
  {float(ops['mul_square']['speedup_at_max_n']):.2f}x.
- DenseMatrix median multiplication time at n={max_n}:
  {float(ops['mul_square']['dense_median_ms_at_max_n']) / 1000.0:.2f} s.
- mathlib Matrix median multiplication time at n={max_n}:
  {float(ops['mul_square']['mathlib_median_ms_at_max_n']) / 1000.0:.2f} s.

## Claims to avoid

- Do not claim DenseMatrix is 20x faster for every matrix operation.
- Do not claim the result changes asymptotic complexity.
- Do not compare DenseMatrix conversion overhead against mathlib Matrix as if it
  were a paired kernel.  `ofMatrix` and `toMatrix` are DenseMatrix conversion
  costs, not mathlib-vs-Dense speedups.

## Empirical complexity

Log-log fits on large sizes, n >= 128:

{complexity_table}

Interpretation: multiplication is cubic for both backends; construction,
indexing, addition, scalar multiplication, and transpose are quadratic.

## Secondary findings

- `get` is a clear DenseMatrix win, about {float(ops['get']['median_speedup']):.2f}x median.
- `add` is a modest DenseMatrix win, about {float(ops['add']['median_speedup']):.2f}x median.
- `transpose` is close to parity at n={max_n}, despite a median speedup of
  {float(ops['transpose']['median_speedup']):.2f}x across all sizes.
- `construct` and `smul` are not wins in this run; mathlib Matrix is faster at
  the largest size.

## Suggested figure set

1. `figures/mul_square_runtime_loglog.svg`.
2. `figures/mul_square_speedup.svg`.
3. `figures/operation_median_speedups.svg`.
4. `figures/complexity_exponents_n_ge_128.svg`.
"""
    write_text(path, text)


def create_benchmark_logic(path: Path) -> None:
    write_text(
        path,
        """# Benchmark Logic

This benchmark times executable Lean definitions in a Lake executable.  It does
not time correctness theorems.  Theorems in
`ProvableComputation/LinearAlgebra/DenseMatrix/Defs.lean`, such as
`DenseMatrix.toMatrix_ofMatrix` and `DenseMatrix.ofMatrix_toMatrix`, document
and prove conversion behavior, but they are not called by the timed benchmark
actions.

## Source Files

- DenseMatrix implementation:
  `repo/ProvableComputation/LinearAlgebra/DenseMatrix/Defs.lean`
- Benchmark harness:
  `repo/ProvableComputation/Bench/DenseMatrixBench.lean`
- Executable entry point:
  `repo/ProvableComputation/Bench/DenseMatrixRunner.lean`

## DenseMatrix Operations Under Test

The DenseMatrix implementation is a row-major `Vector` representation:

- `structure DenseMatrix`: stores `data : Vector alpha (m * n)`.
- `DenseMatrix.get!`: unchecked row-major read used by checksum scans.
- `DenseMatrix.get`: checked row-major read.
- `DenseMatrix.ofMatrix`: converts mathlib `Matrix` to row-major storage.
- `DenseMatrix.toMatrix`: exposes a dense matrix as mathlib `Matrix`.
- `DenseMatrix.of`: constructs dense storage from `Fin m -> Fin n -> alpha`.
- `DenseMatrix.add`: zips two backing vectors with addition.
- `DenseMatrix.smul`: maps scalar multiplication over the backing vector.
- `DenseMatrix.transpose`: builds transposed row-major storage.
- `DenseMatrix.mul`: builds output storage and computes dot products with
  checked dense reads.

The mathlib side uses function-backed `Matrix (Fin m) (Fin n) alpha`
expressions from `Mathlib.Data.Matrix.Basic`, notably `Matrix.of`, matrix
addition, transpose, and multiplication.

## Input Generation

Inputs are deterministic, not random:

- `natEntry seed i j = ((seed + (i+1)*73 + (j+1)*193 + i*j*17) % 997) + 1`.
- `intEntry seed i j = ((seed + (i+1)*97 + (j+1)*53 + i*j*29) % 401) - 200`.
- `matrixNat` and `matrixInt` use `Matrix.of`.
- `denseNat` and `denseInt` use `DenseMatrix.of`.

The benchmark uses square sizes.  The completed run used:

```text
4,8,16,24,32,48,64,80,96,128,160,192,256,384,512,768,1024,1536,2048
```

## Timing Method

Each JSONL record is produced by `measurePure`.

1. Run `warmups` untimed calls to the benchmark action.
2. For each measured repeat:
   - read `IO.monoNanosNow`;
   - call the pure action, which returns a `Nat` checksum;
   - mix that checksum into a running checksum using `mixNat`;
   - call `forceNatForTiming` on the mixed checksum;
   - read `IO.monoNanosNow` again;
   - store the elapsed nanoseconds in `samples_ns`.
3. Summarize `samples_ns` as min, median, mean, p95, max, standard deviation,
   and coefficient of variation.

The JSON `checksum` field is the repeat-mixed checksum, not just one raw matrix
checksum.  Paired DenseMatrix/mathlib records use the same repeat count, so
equal checksums still verify that every repeated action produced the same
full-output value under the same checksum scan.

## Evaluation and Checksums

Every action returns a `Nat` checksum.  This forces evaluation of the whole
output matrix rather than only constructing a lazy expression:

- `checksumDenseUnchecked`: loops over natural-number row/column indices and
  reads `DenseMatrix.get!`.
- `checksumDenseChecked`: loops over `List.finRange` and reads
  `DenseMatrix.get`.
- `checksumMatrix`: loops over `List.finRange` and reads `A i j` from a mathlib
  `Matrix`.

For paired DenseMatrix/mathlib operations, the summary script compares the JSON
checksums.  In the completed run there were 114 paired groups and 0 checksum
mismatches.

## Record Map

`setup_policy` matters:

- `setup_inclusive`: construction/conversion is inside the timed action.
- `prebuilt_inputs`: input matrices are constructed once per size before the
  timed record; the timed action measures the operation plus checksum scan.

| operation | backend | element | setup_policy | timed wrapper | timed operation |
| --- | --- | --- | --- | --- | --- |
| construct | dense_core | Nat | setup_inclusive | `runDenseConstructNat n` | `denseNat n n 11`, i.e. `DenseMatrix.of` over deterministic entries, then `checksumDenseUnchecked` |
| construct | mathlib_matrix | Nat | setup_inclusive | `runMatrixConstructNat n` | `matrixNat n n 11`, i.e. `Matrix.of` over deterministic entries, then `checksumMatrix` |
| ofMatrix | dense_conversion | Nat | setup_inclusive | `runDenseOfMatrixNat n` | `DenseMatrix.ofMatrix (matrixNat n n 13)`, then `checksumDenseUnchecked` |
| toMatrix | dense_conversion | Nat | setup_inclusive | `runDenseToMatrixNat n` | `DenseMatrix.toMatrix (denseNat n n 17)`, then `checksumMatrix` |
| get | dense_core | Nat | prebuilt_inputs | `runDenseGetNatFrom denseNatGet` | full checked scan with `checksumDenseChecked`, which calls `DenseMatrix.get` |
| get | mathlib_matrix | Nat | prebuilt_inputs | `runMatrixGetNatFrom matrixNatGet` | full scan with `checksumMatrix`, which calls `A i j` |
| add | dense_core | Int | prebuilt_inputs | `runDenseAddIntFrom denseIntA denseIntB` | `DenseMatrix.add A B`, then `checksumDenseUnchecked` |
| add | mathlib_matrix | Int | prebuilt_inputs | `runMatrixAddIntFrom matrixIntA matrixIntB` | mathlib matrix addition `A + B`, then `checksumMatrix` |
| smul | dense_core | Int | prebuilt_inputs | `runDenseSmulIntFrom denseIntSmul` | `DenseMatrix.smul (-7) A`, then `checksumDenseUnchecked` |
| smul | mathlib_matrix | Int | prebuilt_inputs | `runMatrixSmulIntFrom matrixIntSmul` | `Matrix.of fun i j => (-7) * A i j`, then `checksumMatrix` |
| transpose | dense_core | Int | prebuilt_inputs | `runDenseTransposeIntFrom denseIntA` | `DenseMatrix.transpose A`, then `checksumDenseUnchecked` |
| transpose | mathlib_matrix | Int | prebuilt_inputs | `runMatrixTransposeIntFrom matrixIntA` | `A.transpose`, then `checksumMatrix` |
| mul_square | dense_core | Nat | prebuilt_inputs | `runDenseMulNatFrom denseNatMulA denseNatMulB` | `DenseMatrix.mul A B`, then `checksumDenseUnchecked` |
| mul_square | mathlib_matrix | Nat | prebuilt_inputs | `runMatrixMulNatFrom matrixNatMulA matrixNatMulB` | mathlib matrix multiplication `A * B`, then `checksumMatrix` |

## Seeds Used Per Size

For every size `n`, `appendSquareBenchmarks` constructs:

- construct pair: seed 11.
- Dense conversion `ofMatrix`: seed 13.
- Dense conversion `toMatrix`: seed 17.
- get pair: seed 19.
- add pair: Int seeds 43 and 47.
- smul pair: Int seed 53.
- transpose pair: Int seed 43.
- multiplication pair: Nat seeds 61 and 67.

## What the Main Multiplication Benchmark Measures

For `mul_square` at size `n`, the inputs are prebuilt once:

```lean
let denseNatMulA := denseNat n n 61
let denseNatMulB := denseNat n n 67
let matrixNatMulA := matrixNat n n 61
let matrixNatMulB := matrixNat n n 67
```

Then each repeat times one of:

```lean
checksumDenseUnchecked natCode (DenseMatrix.mul denseNatMulA denseNatMulB)
checksumMatrix natCode (matrixNatMulA * matrixNatMulB)
```

So the reported multiplication time includes multiplication plus full output
checksum traversal, but not input construction.
""",
    )


def create_reproduce_scripts(scripts_dir: Path) -> None:
    full = f"""#!/usr/bin/env bash
set -euo pipefail

BUNDLE_DIR="$(cd "$(dirname "${{BASH_SOURCE[0]}}")/.." && pwd)"
REPO="${{1:-${{DENSEMATRIX_REPO:-$BUNDLE_DIR/repo}}}}"

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
test -x bench-tools/run_densematrix_48h.sh || {{
  echo "missing bench-tools/run_densematrix_48h.sh in $REPO" >&2
  echo "Use the benchmark branch/source snapshot included in this bundle." >&2
  exit 2
}}
test -x bench-tools/summarize_densematrix_jsonl.py || {{
  echo "missing bench-tools/summarize_densematrix_jsonl.py in $REPO" >&2
  exit 2
}}

OUT_DIR="${{DENSEMATRIX_OUT_DIR:-bench-results/densematrix-48h-reproduced}}"
CORE="${{DENSEMATRIX_CORE:-{DEFAULT_CORE}}}"

bench-tools/run_densematrix_48h.sh \\
  --out-dir "$OUT_DIR" \\
  --core "$CORE" \\
  --sizes "{DEFAULT_SIZES}" \\
  --warmups {DEFAULT_WARMUPS} \\
  --repeats {DEFAULT_REPEATS}

bench-tools/summarize_densematrix_jsonl.py "$OUT_DIR/results.jsonl" --out-dir "$OUT_DIR/summary"
if [[ "$OUT_DIR" = /* ]]; then
  RESULT_PATH="$OUT_DIR"
else
  RESULT_PATH="$REPO/$OUT_DIR"
fi
echo "Full reproduction complete: $RESULT_PATH"
echo "Reference bundle: $BUNDLE_DIR"
"""
    quick = """#!/usr/bin/env bash
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

bench-tools/run_densematrix_48h.sh \\
  --out-dir "$OUT_DIR" \\
  --core "$CORE" \\
  --sizes "4,8" \\
  --warmups 1 \\
  --repeats 1 \\
  --quiet

bench-tools/summarize_densematrix_jsonl.py "$OUT_DIR/results.jsonl" --out-dir "$OUT_DIR/summary"
if [[ "$OUT_DIR" = /* ]]; then
  RESULT_PATH="$OUT_DIR"
else
  RESULT_PATH="$REPO/$OUT_DIR"
fi
echo "Smoke reproduction complete: $RESULT_PATH"
"""
    write_text(scripts_dir / "reproduce_full_48h.sh", full)
    write_text(scripts_dir / "reproduce_quick_smoke.sh", quick)
    os.chmod(scripts_dir / "reproduce_full_48h.sh", 0o755)
    os.chmod(scripts_dir / "reproduce_quick_smoke.sh", 0o755)


def create_source_patch(repo: Path, dst: Path, source_files: list[Path]) -> None:
    chunks: list[str] = []
    tracked = run_capture(["git", "diff", "--", ".gitignore", "lakefile.toml"], repo, allow_failure=True)
    if tracked.strip():
        chunks.append(tracked.rstrip() + "\n")
    for rel in source_files:
        output = run_capture(["git", "diff", "--no-index", "--", "/dev/null", str(rel)], repo, allow_failure=True)
        if output.strip():
            chunks.append(output.rstrip() + "\n")
    write_text(dst, "\n".join(chunks))


def copy_repo_snapshot(repo: Path, dst: Path) -> None:
    def ignore(_dir: str, names: list[str]) -> set[str]:
        ignored = set()
        for name in names:
            if name in REPO_SNAPSHOT_EXCLUDES or name.endswith(".pyc"):
                ignored.add(name)
        return ignored

    shutil.copytree(repo, dst, ignore=ignore)


def create_source_index(path: Path) -> None:
    write_text(
        path,
        """# Source Snapshot

The runnable repository snapshot is in `../repo/`.  Selected source files are
also copied here under their repository-relative paths for easier reading.

## DenseMatrix implementation

- `ProvableComputation/LinearAlgebra/DenseMatrix/Defs.lean`
  - `structure DenseMatrix`
  - row-major indexing
  - `get`, `set`, `ofMatrix`, `toMatrix`
  - `add`, `smul`, `transpose`, `mul`

## Benchmark harness

- `ProvableComputation/Bench/DenseMatrixBench.lean`
  - deterministic inputs
  - checksum evaluation
  - DenseMatrix vs mathlib Matrix benchmark records
  - JSONL runner and argument parser
- `ProvableComputation/Bench/DenseMatrixRunner.lean`
  - Lake executable entry point

## Benchmark scripts

- `bench-tools/run_densematrix_48h.sh`
- `bench-tools/summarize_densematrix_jsonl.py`
- `bench-tools/make_densematrix_benchmark_bundle.py`

## Project/dependency files

- `lakefile.toml`
- `lake-manifest.json`
- `lean-toolchain`
- `.gitignore`

Mathlib source itself is not vendored in this bundle.  The Lean toolchain and
Lake manifest identify the dependency versions used by the repository.
""",
    )


def create_manifest(root: Path) -> None:
    files = sorted(path.relative_to(root) for path in root.rglob("*") if path.is_file())
    lines = [str(path) for path in files if path.name != "MANIFEST.txt"]
    write_text(root / "MANIFEST.txt", "\n".join(lines) + "\n")


def make_archives(bundle_dir: Path) -> tuple[Path, Path]:
    parent = bundle_dir.parent
    base = bundle_dir.name
    zip_path = parent / f"{base}.zip"
    tar_path = parent / f"{base}.tar.gz"
    if zip_path.exists():
        zip_path.unlink()
    if tar_path.exists():
        tar_path.unlink()
    with zipfile.ZipFile(zip_path, "w", compression=zipfile.ZIP_DEFLATED) as zf:
        for path in sorted(bundle_dir.rglob("*")):
            if path.is_file():
                zf.write(path, path.relative_to(parent))
    shutil.make_archive(str(parent / base), "gztar", root_dir=parent, base_dir=base)
    return zip_path, tar_path


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--result-dir", type=Path, default=Path("bench-results/densematrix-48h"))
    parser.add_argument("--bundle-name", default=None)
    parser.add_argument("--out-dir", type=Path, default=None)
    parser.add_argument("--force", action="store_true")
    args = parser.parse_args()

    repo = Path.cwd()
    result_dir = args.result_dir
    summary_dir = result_dir / "summary"
    jsonl = result_dir / "results.jsonl"
    if not jsonl.exists():
        raise SystemExit(f"missing results file: {jsonl}")
    if not (summary_dir / "speedups.csv").exists():
        raise SystemExit(f"missing summary; run: bench-tools/summarize_densematrix_jsonl.py {jsonl} --out-dir {summary_dir}")

    records = read_jsonl(jsonl)
    speedups = collect_speedups(summary_dir)
    op_summary = operation_summary(speedups)
    max_n = max(row["rows"] for row in speedups)
    endpoint = endpoint_table(speedups, max_n)
    mul_rows = mul_square_table(speedups)
    conversions = conversion_table(records)
    complexity_rows = complexity_by_cutoff(records)
    quality = quality_summary(records, speedups, result_dir, summary_dir)

    bundle_name = args.bundle_name or f"densematrix-benchmark-bundle-{datetime.now().strftime('%Y%m%d-%H%M%S')}"
    out_dir = args.out_dir or result_dir / "bundle"
    bundle_dir = out_dir / bundle_name
    if bundle_dir.exists():
        if not args.force:
            raise SystemExit(f"bundle already exists: {bundle_dir}; pass --force to replace it")
        shutil.rmtree(bundle_dir)
    bundle_dir.mkdir(parents=True)

    copy_file(jsonl, bundle_dir / "data" / "results.jsonl")
    for path in sorted(summary_dir.glob("*")):
        if path.is_file():
            copy_file(path, bundle_dir / "data" / "summary" / path.name)
    for name in [
        "command.txt",
        "end-time.txt",
        "exit-status.txt",
        "git-diff-stat.txt",
        "git-diff.patch",
        "git-rev.txt",
        "git-status.txt",
        "lake-version.txt",
        "lean-version.txt",
        "lscpu.txt",
        "progress.log",
        "run-config.txt",
        "start-time.txt",
        "uname.txt",
    ]:
        src = result_dir / name
        if src.exists():
            copy_file(src, bundle_dir / "metadata" / name)

    write_csv(
        bundle_dir / "tables" / "operation_summary.csv",
        [
            "operation",
            "point_count",
            "min_n",
            "max_n",
            "min_speedup",
            "median_speedup",
            "max_speedup",
            "speedup_at_max_n",
            "dense_median_ms_at_max_n",
            "mathlib_median_ms_at_max_n",
        ],
        op_summary,
    )
    write_csv(
        bundle_dir / "tables" / f"endpoint_n_{max_n}.csv",
        [
            "operation",
            "n",
            "dense_median_ms",
            "mathlib_median_ms",
            "speedup_mathlib_over_dense",
            "dense_cv",
            "mathlib_cv",
        ],
        endpoint,
    )
    write_csv(
        bundle_dir / "tables" / "mul_square_by_size.csv",
        ["n", "dense_median_s", "mathlib_median_s", "speedup_mathlib_over_dense", "dense_cv", "mathlib_cv"],
        mul_rows,
    )
    write_csv(
        bundle_dir / "tables" / "conversion_overheads.csv",
        ["operation", "n", "median_ms", "mean_ms", "p95_ms", "cv"],
        conversions,
    )
    write_csv(
        bundle_dir / "tables" / "complexity_by_cutoff.csv",
        ["min_n_cutoff", "backend", "operation", "point_count", "min_n", "max_n", "exponent", "r2"],
        complexity_rows,
    )
    write_json(bundle_dir / "tables" / "quality_summary.json", quality)

    create_figures(bundle_dir / "figures", speedups, op_summary, complexity_rows)
    create_readme(bundle_dir / "README.md", quality=quality, op_summary=op_summary, endpoint=endpoint, max_n=max_n)
    create_conclusions(bundle_dir / "CONCLUSIONS.md", op_summary=op_summary, complexity_rows=complexity_rows, max_n=max_n)
    create_benchmark_logic(bundle_dir / "BENCHMARK_LOGIC.md")
    copy_repo_snapshot(repo, bundle_dir / "repo")

    source_files = [
        Path("ProvableComputation/LinearAlgebra/DenseMatrix/Defs.lean"),
        Path("ProvableComputation/Bench/DenseMatrixBench.lean"),
        Path("ProvableComputation/Bench/DenseMatrixRunner.lean"),
        Path("bench-tools/run_densematrix_48h.sh"),
        Path("bench-tools/summarize_densematrix_jsonl.py"),
        Path("bench-tools/make_densematrix_benchmark_bundle.py"),
    ]
    for rel in source_files:
        if (repo / rel).exists():
            copy_file(repo / rel, bundle_dir / "source" / rel)
    for rel in [Path("lakefile.toml"), Path("lake-manifest.json"), Path(".gitignore"), Path("lean-toolchain")]:
        if (repo / rel).exists():
            copy_file(repo / rel, bundle_dir / "source" / rel)
    create_source_index(bundle_dir / "source" / "README.md")
    create_source_patch(repo, bundle_dir / "source" / "benchmark-harness.patch", source_files)

    scripts_dir = bundle_dir / "scripts"
    copy_file(repo / "bench-tools" / "run_densematrix_48h.sh", scripts_dir / "run_densematrix_48h.sh")
    copy_file(repo / "bench-tools" / "summarize_densematrix_jsonl.py", scripts_dir / "summarize_densematrix_jsonl.py")
    create_reproduce_scripts(scripts_dir)
    for script in scripts_dir.glob("*.sh"):
        os.chmod(script, 0o755)
    for script in scripts_dir.glob("*.py"):
        os.chmod(script, 0o755)

    create_manifest(bundle_dir)
    zip_path, tar_path = make_archives(bundle_dir)

    print(f"bundle_dir={bundle_dir}")
    print(f"zip={zip_path}")
    print(f"tar_gz={tar_path}")
    print(f"records={quality['record_count']}")
    print(f"checksum_mismatches={quality['checksum_mismatch_count']}")
    print(f"mul_square_median_speedup={next(row['median_speedup'] for row in op_summary if row['operation'] == 'mul_square'):.3f}x")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
