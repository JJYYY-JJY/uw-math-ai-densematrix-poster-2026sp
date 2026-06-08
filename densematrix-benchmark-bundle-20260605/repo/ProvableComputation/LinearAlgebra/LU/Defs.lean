import Mathlib.LinearAlgebra.Matrix.Block

/-!
# LU Definitions

This module contains the basic matrix types and structured public result type used by the
LU factorization development.
-/

variable {R : Type} [Field R] [DecidableEq R]
variable {a : Nat} {b : Nat}

/-- Square matrices of size `a × a`. -/
abbrev SquareMatrix (a : Nat) (R : Type) := Matrix (Fin a) (Fin a) R

/-- Legacy internal alias retained while the LU proofs are migrated to `SquareMatrix`. -/
abbrev squareMatrix (a : Nat) (R : Type) := SquareMatrix a R

/-- Unit lower-triangular matrices over `R`. -/
def IsUnitLowerTriangular (L : SquareMatrix a R) : Prop :=
  L.BlockTriangular OrderDual.toDual ∧ ∀ i : Fin a, L i i = 1

namespace Matrix

/-- Structured public output of LU factorization. -/
structure LUFactors (a b : Nat) (R : Type) where
  P : SquareMatrix a R
  L : SquareMatrix a R
  U : Matrix (Fin a) (Fin b) R

end Matrix
