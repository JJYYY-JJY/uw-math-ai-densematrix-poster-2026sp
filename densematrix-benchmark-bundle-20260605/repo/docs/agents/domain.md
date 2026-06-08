# Domain Docs

How the engineering skills should consume this repo's domain documentation when exploring the codebase.

## Layout

This is a single-context repository.

## Before Exploring, Read These

- `CONTEXT.md` at the repo root, if it exists.
- `docs/adr/`, if it exists, for architectural decisions that touch the area being changed.
- The relevant Lean modules under `ProvableComputation/` for the code or proof surface being changed.

If `CONTEXT.md` or `docs/adr/` does not exist, proceed silently. Do not flag the absence or create those files unless the user asks for domain documentation work.

## Current Domain Surface

- Dense matrix backend: `ProvableComputation/LinearAlgebra/DenseMatrix/`
- Gaussian elimination and RREF: `ProvableComputation/LinearAlgebra/GaussianElimination/`
- Echelon predicates: `ProvableComputation/LinearAlgebra/Echelon.lean`
- LU factorization: `ProvableComputation/LinearAlgebra/LU/`
- Determinant routines and correctness: `ProvableComputation/LinearAlgebra/Determinant/`
- Examples and benchmark harnesses: `ProvableComputation/Examples/` and `ProvableComputation/Bench/`

## Use the Project Vocabulary

When output names a domain concept in an issue title, refactor proposal, hypothesis, or test name, use the vocabulary from the current Lean modules and `README.md`.

If the concept you need is not documented yet, note it as a domain-doc gap instead of inventing new terminology.

## Flag ADR Conflicts

If output contradicts an existing ADR, surface the conflict explicitly rather than silently overriding it.
