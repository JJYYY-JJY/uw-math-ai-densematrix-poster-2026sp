import Mathlib.Algebra.Field.Rat

import ProvableComputation.LinearAlgebra.GaussianElimination.Rref
import ProvableComputation.LinearAlgebra.LU.Defs
import ProvableComputation.LinearAlgebra.LU.Basic

/-!
# Determinant Algorithms

This module contains the executable determinant routines built from Gaussian elimination
and LU factorization, together with namespaced public wrappers on the structured API.
-/

variable {R : Type} [Field R] [DecidableEq R]
variable {n : Nat}
variable {hn : n > 0}

open Matrix

namespace DeterminantInternal

def swapRowState (M : Matrix (Fin n) (Fin n) R) (i j : Fin n) (d : R) :
  Matrix (Fin n) (Fin n) R × R :=
  if _h : i = j then
    (M, d)
  else
    (swapRow M i j, -d)

def scaleRowState (M : Matrix (Fin n) (Fin n) R) (i : Fin n) (c : R) (d : R) :
  Matrix (Fin n) (Fin n) R × R :=
  (factor M i c⁻¹, d * c)

private def diagonalProduct (M : squareMatrix n R) : R :=
  ∏ i : (Fin n), M i i

def gaussDetLoop (M : Matrix (Fin n) (Fin n) R) (row : Nat) (d : R) : R :=
  if hrow : row < n then
    match checkPivot M row row with
      | none => 0
      | some (pivotRow, pivotCol) =>
          let rowFin : Fin n := ⟨row, hrow⟩
          let (M, d) := swapRowState M rowFin pivotRow d
          -- let pivotVal := M1 rowFin pivotCol
          -- let (M2, d2) := scaleRowState M1 rowFin pivotVal d1
          let (M, _) :=
            GaussianEliminationInternal.eliminateColCore M rowFin pivotCol List.nil false
          gaussDetLoop M (row + 1) d
  else
    d * diagonalProduct M

/-- Gaussian-elimination determinant computation with explicit swap-sign bookkeeping. -/
def rawGaussDet (M : Matrix (Fin n) (Fin n) R) : R :=
  gaussDetLoop M 0 1

/-- Internal determinant computation via the tuple-valued internal LU factorization. -/
def rawLuDet (M : Matrix (Fin n) (Fin n) R) : R :=
  let (P, L, U) := LUFactorizationInternal.rawFactorization M
  (diagonalProduct P) * (diagonalProduct L) * (diagonalProduct U)

end DeterminantInternal

namespace Matrix

/-- Structured public determinant computation via Gaussian elimination. -/
def gaussDet (M : Matrix (Fin n) (Fin n) R) : R :=
  DeterminantInternal.rawGaussDet M

/-- Structured public determinant computation via LU factorization. -/
def luDet (M : Matrix (Fin n) (Fin n) R) : R :=
  DeterminantInternal.rawLuDet M

end Matrix
