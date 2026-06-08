import Mathlib.Algebra.Field.Rat

import ProvableComputation.LinearAlgebra.Determinant.Basic
import ProvableComputation.LinearAlgebra.GaussianElimination.Elementary
import ProvableComputation.LinearAlgebra.LU.Basic

/-!
# Gaussian Elimination Demos

This module contains executable examples and timing checks for the Gaussian elimination,
LU factorization, and determinant code. It is intentionally kept out of the core library
import surface.
-/

/-- A small `3 × 3` matrix used in Gaussian elimination examples. -/
def sampleMatrix : Matrix (Fin 3) (Fin 3) Rat :=
  ![![1, 2, 3],
    ![2, 5, 6],
    ![4, 8, 12]]

/-- A lower-triangular matrix used to inspect LU reconstruction. -/
def luCounterexample : Matrix (Fin 3) (Fin 3) Rat :=
  ![![1, 0, 0],
    ![2, 1, 0],
    ![3, 5, 1]]

/-- A nonsquare matrix used to inspect the LU API on rectangular inputs. -/
def luNonsquare : Matrix (Fin 3) (Fin 4) Rat :=
  ![![1, 0, 0, 7],
    ![2, 1, 0, 8],
    ![3, 5, 1, 9]]

/-- A `3 × 3` matrix with dependent rows used in determinant timings. -/
def sampleMatrix2 : Matrix (Fin 3) (Fin 3) Rat :=
  ![![1, 2, 3],
    ![4, 8, 12],
    ![2, 5, 6]]

/-- A larger `10 × 10` matrix used for runtime comparisons. -/
def sampleMatrix3 : Matrix (Fin 10) (Fin 10) Rat :=
  ![![9, 8, 6, 9, 7, 4, 6, 8, 4, 7],
    ![27, 30, 22, 34, 29, 17, 23, 31, 20, 24],
    ![36, 86, 61, 106, 134, 66, 77, 100, 97, 64],
    ![9, 212, 153, 327, 658, 236, 272, 307, 384, 215],
    ![27, 24, 22, 61, 168, 52, 74, 65, 71, 79],
    ![0, 180, 124, 244, 387, 198, 214, 258, 304, 150],
    ![9, 26, 20, 71, 152, 148, 193, 181, 247, 169],
    ![27, 78, 58, 133, 262, 184, 307, 296, 753, 237],
    ![27, 30, 54, 267, 1141, 316, 511, 427, 943, 514],
    ![18, 16, 16, 52, 169, 96, 216, 207, 680, 240]]

/-- A `4 × 4` matrix used in example row-reduction and determinant runs. -/
def sampleMatrix4 : Matrix (Fin 4) (Fin 4) Rat :=
  ![![3, 5, 1, 9],
    ![94, 2, 8, 0],
    ![9, 3, 2, 9],
    ![45, 3, 9, 8]]

/-- A `5 × 5` matrix used in determinant runtime checks. -/
def matrix2 : Matrix (Fin 5) (Fin 5) Rat :=
  ![![3, -2, 5, 1, 4],
    ![1, 6, -3, 2, 0],
    ![4, 0, 2, -1, 5],
    ![-2, 3, 1, 4, -3],
    ![5, 1, -4, 0, 2]]

/-- A dense `10 × 10` matrix used in determinant runtime checks. -/
def matrix3 : Matrix (Fin 10) (Fin 10) Rat :=
  ![![1, 2, -1, 0, 3, 4, -2, 1, 5, 0],
    ![0, -3, 4, 1, 2, -1, 0, 6, -2, 3],
    ![5, 1, 0, -2, 4, 3, 1, -1, 0, 2],
    ![-2, 0, 3, 5, -1, 2, 4, 0, 1, -3],
    ![4, -1, 2, 0, 6, 1, -3, 5, 0, 2],
    ![1, 3, 0, -1, 2, 5, 4, -2, 6, 0],
    ![0, 2, -4, 3, 1, 0, 5, 2, -1, 4],
    ![3, 0, 1, 4, -2, 6, 0, 1, 2, -1],
    ![-1, 4, 2, 0, 5, -3, 1, 0, 3, 6],
    ![2, -2, 5, 1, 0, 4, -1, 3, 0, 1]]

private def reconstructLU {R : Type} [Field R] [DecidableEq R] {a b : Nat}
    (M : Matrix (Fin a) (Fin b) R) : Matrix (Fin a) (Fin b) R :=
  let lu := Matrix.luFactorization M
  lu.P * lu.L * lu.U

namespace Matrix

variable {R : Type} [Field R]

/-- A small source matrix for demonstrating `IsEchelonFormOf`. -/
def Afirst : Matrix (Fin 2) (Fin 2) R :=
  !![0, 0;
    1, 0]

/-- An echelon-form target matrix row-equivalent to `Afirst`. -/
def Bfirst : Matrix (Fin 2) (Fin 2) R :=
  !![1, 0;
    0, 0]

lemma Bfirst_eq_swap : Bfirst (R := R) = swapRow (Afirst (R := R)) 0 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Bfirst, Afirst, swapRow, Matrix.of_apply]

private lemma Bfirst_row1_zero : RowIsZero (Bfirst (R := R)) 1 := by
  intro j
  fin_cases j <;> simp [Bfirst]

lemma Bfirst_isEchelon : IsEchelonForm (M := Bfirst (R := R)) := by
  refine IsEchelonForm.mk ?row_zero_or_pivot ?zero_rows_bottom ?pivots_strict
  · intro i
    fin_cases i
    · right
      refine ⟨(0 : Fin 2), ?_⟩
      refine ⟨?_, ?_⟩
      · simp [Bfirst]
      · intro j hj
        exact (False.elim ((Fin.not_lt_zero j) hj))
    · left
      exact Bfirst_row1_zero (R := R)
  · intro i j hij hzi
    fin_cases i <;> fin_cases j
    · exact (False.elim (lt_irrefl _ hij))
    · exfalso
      have h00 : (Bfirst (R := R)) 0 0 = 0 := hzi 0
      simp [Bfirst] at h00
    · exact (False.elim ((Nat.not_lt_zero _ (show (1 : Fin 2) < (0 : Fin 2) from hij))))
    · exact (False.elim (lt_irrefl _ hij))
  · intro i j p q hij hp hq
    fin_cases i <;> fin_cases j
    · exact (False.elim (lt_irrefl _ hij))
    · exfalso
      exact hq.1 ((Bfirst_row1_zero (R := R)) q)
    · exact (False.elim ((Nat.not_lt_zero _ (show (1 : Fin 2) < (0 : Fin 2) from hij))))
    · exact (False.elim (lt_irrefl _ hij))

/--
Concrete first-point example:
`Bfirst` is an echelon form of `Afirst` (row-equivalent plus echelon predicate).
-/
theorem firstPointExample :
    IsEchelonFormOf (A := Afirst (R := R)) (Bfirst (R := R)) := by
  have hswap : RowEquivalent (Afirst (R := R)) (swapRow (Afirst (R := R)) 0 1) :=
    rowEquivalent_swapRow (A := Afirst (R := R)) (r₁ := 0) (r₂ := 1)
  have hRow : RowEquivalent (Afirst (R := R)) (Bfirst (R := R)) := by
    simpa [Bfirst_eq_swap (R := R)] using hswap
  exact isEchelonFormOf_mk (hRow := hRow) (hEch := Bfirst_isEchelon (R := R))

end Matrix

#eval (Matrix.rowEchelonForm sampleMatrix).matrix
#eval (Matrix.reducedRowEchelonForm sampleMatrix).matrix
#eval (Matrix.rowEchelonForm sampleMatrix4).matrix

-- Determinant runtime tests

-- 3x3 matrices
#time #eval Matrix.luDet sampleMatrix
#time #eval Matrix.gaussDet sampleMatrix
#time #eval sampleMatrix.det
#time #eval Matrix.luDet sampleMatrix2
#time #eval Matrix.gaussDet sampleMatrix2
#time #eval sampleMatrix2.det

-- 4x4 matrix
#time #eval Matrix.luDet sampleMatrix4
#time #eval Matrix.gaussDet sampleMatrix4
#time #eval sampleMatrix4.det

-- 5x5 matrix
#time #eval Matrix.luDet matrix2
#time #eval Matrix.gaussDet matrix2
#time #eval matrix2.det

-- 10x10 matrices
-- Stack overflow: the Leibniz determinant computation cannot handle these comfortably.
#time #eval Matrix.luDet sampleMatrix3
#time #eval Matrix.gaussDet sampleMatrix3
-- #time #eval sampleMatrix3.det
#time #eval Matrix.luDet matrix3
#time #eval Matrix.gaussDet matrix3
-- #time #eval matrix3.det

#time #eval Matrix.luFactorization sampleMatrix
#time #eval reconstructLU sampleMatrix
#eval decide (reconstructLU sampleMatrix = sampleMatrix)

#time #eval Matrix.luFactorization sampleMatrix2
#time #eval reconstructLU sampleMatrix2
#eval decide (reconstructLU sampleMatrix2 = sampleMatrix2)

#time #eval Matrix.luFactorization sampleMatrix4
#time #eval reconstructLU sampleMatrix4
#eval decide (reconstructLU sampleMatrix4 = sampleMatrix4)

#time #eval Matrix.luFactorization sampleMatrix3
#time #eval reconstructLU sampleMatrix3
#eval decide (reconstructLU sampleMatrix3 = sampleMatrix3)

#eval Matrix.luFactorization luCounterexample
#eval reconstructLU luCounterexample
#eval decide (reconstructLU luCounterexample = luCounterexample)

#eval Matrix.luFactorization luNonsquare
#eval reconstructLU luNonsquare
#eval decide (reconstructLU luNonsquare = luNonsquare)
