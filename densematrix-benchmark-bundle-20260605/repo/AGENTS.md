# Agent Instructions

## Repo Shape

- This is a Lean 4/Lake project pinned by `lean-toolchain` to `leanprover/lean4:v4.30.0`.
- The public library surface is `ProvableComputation.lean`.
- Executable linear algebra code lives under `ProvableComputation/LinearAlgebra/`.
- Examples and benchmark harnesses live under `ProvableComputation/Examples/` and `ProvableComputation/Bench/`.

## Working Rules

- Use Lean LSP diagnostics and proof goals first for proof work.
- Keep executable algorithms, correctness proofs, demos, and benchmarks in their owning modules.
- Preserve the project style from `lakefile.toml`: explicit imports and variables, `autoImplicit = false`, and mathlib linting.
- Do not add demo or benchmark code to the public import surface unless the public API intentionally changes.

## Verification

- Narrow Lean check: `lake env lean <path>`.
- Broad project check: `lake build`.
- Executable benchmark smoke check: `lake exe densematrix_bench --quick --jsonl -`.

## Agent skills

### Issue tracker

Issues and PRDs are tracked in GitHub Issues for `uw-math-ai/provable_computation`. See `docs/agents/issue-tracker.md`.

### Triage labels

The repo uses the canonical five-label triage vocabulary. See `docs/agents/triage-labels.md`.

### Domain docs

Single-context layout; read root domain docs if they exist, and otherwise proceed silently. See `docs/agents/domain.md`.
