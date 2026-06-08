import ProvableComputation.LinearAlgebra.LU.Defs
import ProvableComputation.LinearAlgebra.GaussianElimination.Elementary
import ProvableComputation.LinearAlgebra.GaussianElimination.Rref

/-!
# LU Basic Algorithm

This module turns the row-operation log produced by Gaussian elimination into permutation
and lower-triangular factors, and exposes the structured public LU-factorization API.
-/

variable {R : Type} [Field R] [DecidableEq R]
variable {a : Nat} {b : Nat}

namespace LUFactorizationInternal

def permutationOfSwaps (swaps : List (Fin a × Fin a)) : squareMatrix a R :=
  swaps.foldl (fun acc ij => ColumnElementary.swapCol acc ij.1 ij.2) 1

def lowerOfSwaps
    (swaps : List (Fin a × Fin a)) (MInv : squareMatrix a R) : squareMatrix a R :=
  swaps.foldl (fun acc ij => swapRow acc ij.1 ij.2) MInv

def buildPLStep
    (state : List (Fin a × Fin a) × squareMatrix a R)
    (op : RowOp a R) : List (Fin a × Fin a) × squareMatrix a R :=
  let swaps := state.1
  let MInv := state.2
  match op with
  | .swap i j => (swaps.concat (i, j), ColumnElementary.swapCol MInv i j)
  | .factor row scale => (swaps, ColumnElementary.factorCol MInv row scale⁻¹)
  | .replace use toReplace scale =>
      if use = toReplace then
        (swaps, ColumnElementary.factorCol MInv toReplace (scale + 1)⁻¹)
      else
        (swaps, ColumnElementary.replaceCol MInv use toReplace (-scale))

/-- Replay a row-operation log into the permutation and lower-triangular bookkeeping factors. -/
def buildPLFromSteps (steps : List (RowOp a R)) : squareMatrix a R × squareMatrix a R :=
  let (swaps, MInv) :=
    steps.foldl (LUFactorizationInternal.buildPLStep (R := R)) ([], 1)
  let P := LUFactorizationInternal.permutationOfSwaps (R := R) swaps
  let L := LUFactorizationInternal.lowerOfSwaps (R := R) swaps MInv
  (P, L)

/-- Internal tuple-valued LU factorization used by the proof files. -/
def rawFactorization (M : Matrix (Fin a) (Fin b) R) :
    squareMatrix a R × (squareMatrix a R × Matrix (Fin a) (Fin b) R) :=
  let (U, steps) := GaussianEliminationInternal.rawRowEchelonForm M
  let (P, L) := buildPLFromSteps steps
  (P, (L, U))

end LUFactorizationInternal

namespace Matrix

/-- Structured public LU factorization. -/
def luFactorization (M : Matrix (Fin a) (Fin b) R) : LUFactors a b R :=
  let raw := LUFactorizationInternal.rawFactorization M
  { P := raw.1, L := raw.2.1, U := raw.2.2 }

end Matrix
