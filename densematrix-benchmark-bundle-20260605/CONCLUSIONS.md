# Conclusions and Poster-Ready Claims

## Recommended main claim

DenseMatrix achieves about 20x faster full square matrix multiplication than
mathlib Matrix in the compiled benchmark harness, while both implementations
retain the expected O(n^3) empirical scaling.

Useful numeric support:

- Median multiplication speedup over all tested sizes:
  20.93x.
- Best observed multiplication speedup:
  22.60x.
- Multiplication speedup at n=2048:
  19.17x.
- DenseMatrix median multiplication time at n=2048:
  56.53 s.
- mathlib Matrix median multiplication time at n=2048:
  1083.50 s.

## Claims to avoid

- Do not claim DenseMatrix is 20x faster for every matrix operation.
- Do not claim the result changes asymptotic complexity.
- Do not compare DenseMatrix conversion overhead against mathlib Matrix as if it
  were a paired kernel.  `ofMatrix` and `toMatrix` are DenseMatrix conversion
  costs, not mathlib-vs-Dense speedups.

## Empirical complexity

Log-log fits on large sizes, n >= 128:

| operation | Dense exponent | Dense R2 | mathlib exponent | mathlib R2 |
| --- | --- | --- | --- | --- |
| construct | 2.035 | 0.99997 | 2.000 | 0.99989 |
| get | 1.992 | 0.99976 | 1.988 | 0.99993 |
| add | 2.056 | 0.99996 | 1.992 | 0.99991 |
| smul | 2.045 | 0.99996 | 1.999 | 0.99991 |
| transpose | 2.066 | 0.99994 | 1.993 | 0.99996 |
| mul_square | 3.039 | 0.99986 | 3.004 | 1.00000 |

Interpretation: multiplication is cubic for both backends; construction,
indexing, addition, scalar multiplication, and transpose are quadratic.

## Secondary findings

- `get` is a clear DenseMatrix win, about 2.11x median.
- `add` is a modest DenseMatrix win, about 1.42x median.
- `transpose` is close to parity at n=2048, despite a median speedup of
  1.20x across all sizes.
- `construct` and `smul` are not wins in this run; mathlib Matrix is faster at
  the largest size.

## Suggested figure set

1. `figures/mul_square_runtime_loglog.svg`.
2. `figures/mul_square_speedup.svg`.
3. `figures/operation_median_speedups.svg`.
4. `figures/complexity_exponents_n_ge_128.svg`.
