import Mathlib.Data.Matrix.Basic

/-!
# Echelon Predicates

This module defines row-echelon and reduced row-echelon predicates for matrices, together
with the basic structural lemma that pivot columns are zero below pivots in echelon form.
-/

namespace Matrix

variable {R : Type*} [Field R]

/-- A row is zero if all of its entries are zero. -/
def RowIsZero {m n : Type*} (M : Matrix m n R) (i : m) : Prop :=
  ∀ j, M i j = 0

/-- A pivot at column `p` of row `i`: the entry is nonzero and all entries to the left are zero. -/
def IsPivot {m n : Type*} [LinearOrder n] (M : Matrix m n R) (i : m) (p : n) : Prop :=
  M i p ≠ 0 ∧ ∀ j < p, M i j = 0

/-- Row echelon form with respect to the given row and column orders. -/
structure IsEchelonForm {m n : Type*} [LinearOrder m] [LinearOrder n]
  (M : Matrix m n R) : Prop where
  row_zero_or_pivot :
    ∀ i, RowIsZero M i ∨ ∃ p : n, IsPivot M i p
  zero_rows_bottom :
    ∀ i j, i < j → RowIsZero M i → RowIsZero M j
  pivots_strictly_increasing :
    ∀ i j p q, i < j → IsPivot M i p → IsPivot M j q → p < q

/- In REF, a pivot column is zero below the pivot (derivable from the minimal axioms). -/
lemma IsEchelonForm.pivot_column_zero_below
    {m n : Type*} [LinearOrder m] [LinearOrder n]
    {M : Matrix m n R} (h : IsEchelonForm M) :
    ∀ i r p, i < r → IsPivot M i p → M r p = 0 := by
  intro i r p hir hp
  rcases h.row_zero_or_pivot r with hzero | ⟨q, hq⟩
  · exact hzero p
  · exact hq.2 p (h.pivots_strictly_increasing i r p q hir hp hq)

section Reduced

/-- Reduced row echelon form: echelon form plus pivot normalization and zeros above pivots. -/
structure IsReducedEchelonForm {m n : Type*} [LinearOrder m] [LinearOrder n]
  (M : Matrix m n R) : Prop where
  echelon : IsEchelonForm M
  pivot_is_one :
    ∀ i p, IsPivot M i p → M i p = 1
  pivot_column_zero_above :
    ∀ i r p, r < i → IsPivot M i p → M r p = 0
end Reduced

end Matrix
