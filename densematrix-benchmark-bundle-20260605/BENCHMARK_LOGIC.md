# Benchmark Logic

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
