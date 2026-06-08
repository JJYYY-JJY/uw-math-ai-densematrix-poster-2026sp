# Source Snapshot

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
