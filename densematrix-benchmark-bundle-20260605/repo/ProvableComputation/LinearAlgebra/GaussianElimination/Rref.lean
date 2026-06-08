import ProvableComputation.LinearAlgebra.GaussianElimination.Defs

/-!
# Gaussian Elimination Algorithms

This module implements the executable elimination loops for row-echelon and reduced
row-echelon form. The tuple-valued internal routines are retained for proof convenience,
while the public `Matrix` wrappers return `RowReductionResult`.
-/

open Matrix

variable {R : Type} [Field R] [DecidableEq R]
variable {a b : ℕ}
variable {ha : a > 0} {hb : b > 0}

namespace GaussianEliminationInternal

-- `eliminateCol` iterates through the matrix row by row, and uses the `replace` operation
-- to set the value in column `pivotCol` of the row to 0.
-- `eliminateCol` calls replace between 0 and `a` times, so this algorithm's certificate
-- should include a `replace` object for each `replace` call in `eliminateCol`
def eliminateColLoopAux
    (pivotRow : Fin a) (pivotCol : Fin b) (pivotVal : R)
    (r : Nat) (cur : Matrix (Fin a) (Fin b) R) (steps : List (RowOp a R))
    : (Matrix (Fin a) (Fin b) R × List (RowOp a R)) :=
  -- Iterate over each entry in pivotCol.
  if hr : r < a then
    let i : Fin a := ⟨r, hr⟩
    -- Skip over pivotRow.
    if h : i = pivotRow then
      eliminateColLoopAux pivotRow pivotCol pivotVal (r + 1) cur steps
    else
      -- Otherwise, use pivotRow to replace the current row, setting this row's
      -- pivotCol entry to 0.
      let coeff := cur i pivotCol
      if coeff ≠ 0 then  -- eliminate unnecessary calls to `replace`
        eliminateColLoopAux pivotRow pivotCol pivotVal (r + 1)
          (replace cur pivotRow i (-coeff / pivotVal))
          (List.concat steps (.replace pivotRow i (-coeff / pivotVal)))
      else
        eliminateColLoopAux pivotRow pivotCol pivotVal (r + 1) cur steps
  else
    (cur, steps)
termination_by a - r
decreasing_by
  · omega
  · omega
  · omega

def eliminateColLoop
    (pivotRow : Fin a) (pivotCol : Fin b)
    (r : Nat) (cur : Matrix (Fin a) (Fin b) R) (steps : List (RowOp a R))
    : (Matrix (Fin a) (Fin b) R × List (RowOp a R)) :=
  eliminateColLoopAux pivotRow pivotCol (cur pivotRow pivotCol) r cur steps

def eliminateColCore
    (given : Matrix (Fin a) (Fin b) R) (pivotRow : Fin a) (pivotCol : Fin b)
    (steps : List (RowOp a R)) (reduced : Bool) : (Matrix (Fin a) (Fin b) R × List (RowOp a R)) :=
  if reduced then
    eliminateColLoop pivotRow pivotCol 0 given steps
  else
    eliminateColLoop pivotRow pivotCol pivotRow.val given steps

def rowReductionAux
  (m : Matrix (Fin a) (Fin b) R) (row col : Nat) (steps : List (RowOp a R)) (reduced : Bool)
  : (Matrix (Fin a) (Fin b) R × List (RowOp a R)) :=
  if hrow : row < a then
    if col < b then
      let pivot_location := checkPivot m row col
      match pivot_location with
      | none => (m, steps)
      | some (pivotRow, pivotCol) =>
        let m1 :=
          if pivotRow.val = row then
            m
          else
            swapRow m ⟨row, hrow⟩ pivotRow
        let steps := List.concat steps (.swap ⟨row, hrow⟩ pivotRow)
        let pivotVal : R := m1 ⟨row, hrow⟩ pivotCol
        let m2 :=
          if !reduced || pivotVal = 1 then
            m1
          else
            factor m1 ⟨row, hrow⟩ (pivotVal)⁻¹
        let steps :=
          if !reduced || pivotVal = 1 then
            steps
          else
            List.concat steps (.factor ⟨row, hrow⟩ (pivotVal)⁻¹)
        let (m3, steps) := eliminateColCore m2 ⟨row, hrow⟩ pivotCol steps reduced
        rowReductionAux m3 (row + 1) (col + 1) steps reduced
    else
      (m, steps)
  else
    (m, steps)

/-- Compute a row-echelon form together with the logged row operations that produce it. -/
def rawRowEchelonForm (given : Matrix (Fin a) (Fin b) R)
    : (Matrix (Fin a) (Fin b) R × List (RowOp a R)) :=
  rowReductionAux given 0 0 List.nil false

/-- Compute a reduced row-echelon form together with the logged row operations that produce it. -/
def rawReducedRowEchelonForm
 (given : Matrix (Fin a) (Fin b) R)
: (Matrix (Fin a) (Fin b) R × List (RowOp a R)) :=
  rowReductionAux given 0 0 List.nil true

end GaussianEliminationInternal

namespace Matrix

/-- Structured public wrapper for `GaussianEliminationInternal.rawRowEchelonForm`. -/
def rowEchelonForm
    (given : Matrix (Fin a) (Fin b) R) : RowReductionResult a b R :=
  let raw := GaussianEliminationInternal.rawRowEchelonForm given
  { matrix := raw.1, steps := raw.2 }

/-- Structured public wrapper for `GaussianEliminationInternal.rawReducedRowEchelonForm`. -/
def reducedRowEchelonForm
    (given : Matrix (Fin a) (Fin b) R) : RowReductionResult a b R :=
  let raw := GaussianEliminationInternal.rawReducedRowEchelonForm given
  { matrix := raw.1, steps := raw.2 }

end Matrix
