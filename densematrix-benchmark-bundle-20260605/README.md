# DenseMatrix vs mathlib Matrix Benchmark Bundle

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
- Raw benchmark records: 266.
- Measured samples: 13300.
- Paired DenseMatrix/mathlib checksum mismatches: 0.
- Largest matrix size: n=2048.
- Wall-clock run time: 30.85 hours.
- Total measured sample time: 25.72 hours.
- Median CV over all records: 0.0133.
- Median CV for n >= 128: 0.0100.

## Operation summary

Speedup is `mathlib median runtime / DenseMatrix median runtime`; values above
1 mean DenseMatrix is faster.

| operation | median speedup | speedup at n=2048 | Dense median at n=2048 | mathlib median at n=2048 |
| --- | --- | --- | --- | --- |
| construct | 0.67x | 0.62x | 300.591 ms | 185.658 ms |
| get | 2.11x | 2.07x | 89.533 ms | 184.906 ms |
| add | 1.42x | 1.27x | 254.401 ms | 324.114 ms |
| smul | 0.96x | 0.85x | 249.128 ms | 211.970 ms |
| transpose | 1.20x | 1.03x | 270.148 ms | 277.559 ms |
| mul_square | 20.93x | 19.17x | 56.533 s | 1083.504 s |

## Endpoint at n=2048

| operation | Dense median | mathlib median | speedup | Dense CV | mathlib CV |
| --- | --- | --- | --- | --- | --- |
| construct | 300.591 ms | 185.658 ms | 0.62x | 0.0145 | 0.0088 |
| get | 89.533 ms | 184.906 ms | 2.07x | 0.0122 | 0.0068 |
| add | 254.401 ms | 324.114 ms | 1.27x | 0.0119 | 0.0104 |
| smul | 249.128 ms | 211.970 ms | 0.85x | 0.0152 | 0.0060 |
| transpose | 270.148 ms | 277.559 ms | 1.03x | 0.0100 | 0.0109 |
| mul_square | 56.533 s | 1083.504 s | 19.17x | 0.0007 | 0.0016 |

## Important interpretation

- Matrix multiplication is the main result: median speedup is about 20.9x over
  all sizes and about 19.2x at n=2048.
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
`4,8,16,24,32,48,64,80,96,128,160,192,256,384,512,768,1024,1536,2048`, 10 warmups, 50 repeats, CPU core
3, and resumable JSONL output.  Lake may need to download/build
dependencies if they are not already available locally.  The bundle includes
source code and `lake-manifest.json`, but it intentionally does not include
`.lake` build artifacts or vendored mathlib sources.
