#!/usr/bin/env python3
"""Summarize DenseMatrix benchmark JSONL output.

The script verifies DenseMatrix/mathlib checksum agreement, writes paired
speedups, and estimates empirical complexity exponents via log-log linear
regression of median runtime against matrix size.
"""

from __future__ import annotations

import argparse
import csv
import json
import math
from collections import defaultdict
from pathlib import Path
from statistics import median


def read_rows(path: Path) -> list[dict]:
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


def pair_key(row: dict) -> tuple:
    return (
        row["operation"],
        row["element"],
        row["setup_policy"],
        row["rows"],
        row["cols"],
        row["inner"],
        row["warmups"],
        row["repeats"],
    )


def complexity_key(row: dict) -> tuple:
    return (
        row["backend"],
        row["operation"],
        row["element"],
        row["setup_policy"],
    )


def write_csv(path: Path, fieldnames: list[str], rows: list[dict]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(rows)


def linreg_loglog(points: list[tuple[float, float]]) -> dict | None:
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

    return {
        "point_count": len(clean),
        "min_n": int(min(x for x, _ in clean)),
        "max_n": int(max(x for x, _ in clean)),
        "exponent": slope,
        "constant": math.exp(intercept),
        "r2": r2,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("jsonl", type=Path)
    parser.add_argument("--out-dir", type=Path, default=None)
    args = parser.parse_args()

    rows = read_rows(args.jsonl)
    out_dir = args.out_dir or args.jsonl.with_suffix("")
    out_dir.mkdir(parents=True, exist_ok=True)

    paired: dict[tuple, dict[str, dict]] = defaultdict(dict)
    for row in rows:
        backend = row.get("backend")
        if backend in ("dense_core", "mathlib_matrix"):
            paired[pair_key(row)][backend] = row

    speedups: list[dict] = []
    mismatches: list[dict] = []
    for key, group in sorted(paired.items()):
        dense = group.get("dense_core")
        mathlib = group.get("mathlib_matrix")
        if not dense or not mathlib:
            continue
        if dense["checksum"] != mathlib["checksum"]:
            mismatches.append(
                {
                    "operation": key[0],
                    "element": key[1],
                    "setup_policy": key[2],
                    "rows": key[3],
                    "cols": key[4],
                    "inner": key[5],
                    "dense_checksum": dense["checksum"],
                    "mathlib_checksum": mathlib["checksum"],
                }
            )
        dense_ms = float(dense["median_ms"])
        mathlib_ms = float(mathlib["median_ms"])
        speedups.append(
            {
                "operation": key[0],
                "element": key[1],
                "setup_policy": key[2],
                "rows": key[3],
                "cols": key[4],
                "inner": key[5],
                "warmups": key[6],
                "repeats": key[7],
                "dense_median_ms": dense_ms,
                "mathlib_median_ms": mathlib_ms,
                "speedup_mathlib_over_dense": mathlib_ms / dense_ms if dense_ms else "",
                "dense_cv": dense.get("cv", ""),
                "mathlib_cv": mathlib.get("cv", ""),
            }
        )

    write_csv(
        out_dir / "speedups.csv",
        [
            "operation",
            "element",
            "setup_policy",
            "rows",
            "cols",
            "inner",
            "warmups",
            "repeats",
            "dense_median_ms",
            "mathlib_median_ms",
            "speedup_mathlib_over_dense",
            "dense_cv",
            "mathlib_cv",
        ],
        speedups,
    )
    write_csv(
        out_dir / "checksum-mismatches.csv",
        [
            "operation",
            "element",
            "setup_policy",
            "rows",
            "cols",
            "inner",
            "dense_checksum",
            "mathlib_checksum",
        ],
        mismatches,
    )

    points_by_group: dict[tuple, list[tuple[float, float]]] = defaultdict(list)
    for row in rows:
        n = float(row["rows"])
        time_ms = float(row["median_ms"])
        points_by_group[complexity_key(row)].append((n, time_ms))

    complexity_rows: list[dict] = []
    for key, points in sorted(points_by_group.items()):
        fit = linreg_loglog(points)
        if not fit:
            continue
        backend, operation, element, setup_policy = key
        complexity_rows.append(
            {
                "backend": backend,
                "operation": operation,
                "element": element,
                "setup_policy": setup_policy,
                **fit,
            }
        )

    write_csv(
        out_dir / "complexity.csv",
        [
            "backend",
            "operation",
            "element",
            "setup_policy",
            "point_count",
            "min_n",
            "max_n",
            "exponent",
            "constant",
            "r2",
        ],
        complexity_rows,
    )

    by_operation: dict[str, list[float]] = defaultdict(list)
    for row in speedups:
        speedup = row["speedup_mathlib_over_dense"]
        if speedup != "":
            by_operation[row["operation"]].append(float(speedup))

    summary = {
        "jsonl": str(args.jsonl),
        "record_count": len(rows),
        "paired_group_count": len(speedups),
        "checksum_mismatch_count": len(mismatches),
        "operations": sorted({row["operation"] for row in rows}),
        "max_rows": max((int(row["rows"]) for row in rows), default=0),
        "speedup_median_by_operation": {
            op: median(values) for op, values in sorted(by_operation.items())
        },
    }

    with (out_dir / "summary.json").open("w") as f:
      json.dump(summary, f, indent=2, sort_keys=True)
      f.write("\n")

    print(f"records: {summary['record_count']}")
    print(f"paired groups: {summary['paired_group_count']}")
    print(f"checksum mismatches: {summary['checksum_mismatch_count']}")
    print(f"max rows: {summary['max_rows']}")
    for op, value in summary["speedup_median_by_operation"].items():
        print(f"median speedup {op}: {value:.3f}x")
    print(f"wrote: {out_dir}")
    return 1 if mismatches else 0


if __name__ == "__main__":
    raise SystemExit(main())
