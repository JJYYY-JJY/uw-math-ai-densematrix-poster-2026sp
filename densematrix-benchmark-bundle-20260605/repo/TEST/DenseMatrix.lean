import ProvableComputation.LinearAlgebra.DenseMatrix.Defs

namespace DenseMatrix

private def smokeA23 : Matrix (Fin 2) (Fin 3) Nat :=
  ![![1, 2, 3],
    ![4, 5, 6]]

private def smokeB32 : Matrix (Fin 3) (Fin 2) Nat :=
  ![![7, 8],
    ![9, 10],
    ![11, 12]]

private def smokeA20 : Matrix (Fin 2) (Fin 0) Nat :=
  Matrix.of fun _ j => Fin.elim0 j

private def smokeB03 : Matrix (Fin 0) (Fin 3) Nat :=
  Matrix.of fun i _ => Fin.elim0 i

set_option linter.style.nativeDecide false in
example : toMatrix (mul (ofMatrix smokeA23) (ofMatrix smokeB32)) = smokeA23 * smokeB32 := by
  native_decide

end DenseMatrix
