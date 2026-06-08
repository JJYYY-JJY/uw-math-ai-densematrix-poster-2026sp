import Mathlib.Data.Matrix.Basic

/-!
# Gaussian Elimination Definitions

This module contains the executable row-operation primitives and pivot search used by the
Gaussian elimination routines, together with the structured public result type for row
reduction.
-/

open Matrix

variable {R : Type} [Field R] [DecidableEq R]
variable {a b : ℕ}

/-- A logged elementary row operation on `a` rows over `R`. -/
inductive RowOp (a : ℕ) (R : Type) : Type where
  | swap : Fin a → Fin a → RowOp a R
  | factor : Fin a → R → RowOp a R
  | replace : Fin a → Fin a → R → RowOp a R

/-- Swap two rows of a matrix. -/
def swapRow (given : Matrix (Fin a) (Fin b) R)
    (row1 row2 : Fin a) : Matrix (Fin a) (Fin b) R :=
  of fun i j =>
    if i = row1 then
      given row2 j
    else if i = row2 then
      given row1 j
    else
      given i j

/-- Scale one row of a matrix by a field element. -/
def factor (given : Matrix (Fin a) (Fin b) R) (i : Fin a)
    (j : R) : Matrix (Fin a) (Fin b) R :=
  of fun i' j' =>
    if i' = i then
      j * given i' j'
    else
      given i' j'

/-- Replace one row by itself plus a scalar multiple of another row. -/
def replace (given : Matrix (Fin a) (Fin b) R)
    (use toReplace : Fin a) (k : R) : Matrix (Fin a) (Fin b) R :=
  if use = toReplace then
    factor given toReplace (k + 1)
  else
    of fun i j =>
      if i = toReplace then
        given toReplace j + k * given use j
      else
        given i j

/--
Find the first nonzero pivot entry at or below `startRow` and at or to the right of
`startCol`.
-/
def checkPivot
    (M : Matrix (Fin a) (Fin b) R)
    (startRow startCol : Nat) :
    Option (Fin a × Fin b) :=
  let rec scanCol (col : Nat) : Option (Fin a × Fin b) :=
    if hcol : col < b then
      let rec scanRow (row : Nat) : Option (Fin a × Fin b) :=
        if hrow : row < a then
          if M ⟨row, hrow⟩ ⟨col, hcol⟩ ≠ 0 then
            some (⟨row, hrow⟩, ⟨col, hcol⟩)
          else
            scanRow (row + 1)
        else
          none
      match scanRow startRow with
      | some p => some p
      | none => scanCol (col + 1)
    else
      none
  scanCol startCol

namespace Matrix

/-- The public structured result of a row-reduction routine. -/
structure RowReductionResult (a b : Nat) (R : Type) where
  matrix : Matrix (Fin a) (Fin b) R
  steps : List (_root_.RowOp a R)

end Matrix
