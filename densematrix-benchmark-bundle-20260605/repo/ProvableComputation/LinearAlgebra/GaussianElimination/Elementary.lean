import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

import ProvableComputation.LinearAlgebra.Echelon
import ProvableComputation.LinearAlgebra.GaussianElimination.Defs

/-!
# Elementary Row and Column Operations

This module collects the reusable linear-algebra facts about elementary row operations,
row-equivalence, echelon-form witnesses, and the corresponding column-operation helpers
used by the LU factorization development.
-/

namespace Matrix

variable {R : Type} [Field R]

/-- Row-equivalence via left multiplication by a unit square matrix. -/
def RowEquivalent {m n : Type*} [Fintype m] [DecidableEq m]
    (A B : Matrix m n R) : Prop :=
  ∃ U : (Matrix m m R)ˣ, B = (U : Matrix m m R) * A

lemma RowEquivalent.refl {m n : Type*} [Fintype m] [DecidableEq m]
    (A : Matrix m n R) : RowEquivalent A A := by
  refine ⟨1, ?_⟩
  simp

lemma RowEquivalent.symm {m n : Type*} [Fintype m] [DecidableEq m]
    {A B : Matrix m n R} (h : RowEquivalent A B) : RowEquivalent B A := by
  rcases h with ⟨U, rfl⟩
  refine ⟨U⁻¹, ?_⟩
  simp

lemma RowEquivalent.trans {m n : Type*} [Fintype m] [DecidableEq m]
    {A B C : Matrix m n R} (hAB : RowEquivalent A B) (hBC : RowEquivalent B C) :
    RowEquivalent A C := by
  rcases hAB with ⟨U, rfl⟩
  rcases hBC with ⟨V, rfl⟩
  refine ⟨V * U, ?_⟩
  simp [Matrix.mul_assoc]

instance rowEquivalentSetoid {m n : Type*} [Fintype m] [DecidableEq m] :
    Setoid (Matrix m n R) where
  r := RowEquivalent
  iseqv := ⟨RowEquivalent.refl, RowEquivalent.symm, RowEquivalent.trans⟩

/-- `B` is an echelon-form representative of `A`. -/
def IsEchelonFormOf {m n : Type*}
    [Fintype m] [DecidableEq m] [LinearOrder m] [LinearOrder n]
    (A B : Matrix m n R) : Prop :=
  RowEquivalent A B ∧ IsEchelonForm (M := B)

lemma IsEchelonFormOf.rowEquivalent {m n : Type*}
    [Fintype m] [DecidableEq m] [LinearOrder m] [LinearOrder n]
    {A B : Matrix m n R} (h : IsEchelonFormOf (A := A) B) :
    RowEquivalent A B :=
  h.1

lemma IsEchelonFormOf.echelon {m n : Type*}
    [Fintype m] [DecidableEq m] [LinearOrder m] [LinearOrder n]
    {A B : Matrix m n R} (h : IsEchelonFormOf (A := A) B) :
    IsEchelonForm (M := B) :=
  h.2

lemma isEchelonFormOf_mk {m n : Type*}
    [Fintype m] [DecidableEq m] [LinearOrder m] [LinearOrder n]
    {A B : Matrix m n R} (hRow : RowEquivalent A B) (hEch : IsEchelonForm (M := B)) :
    IsEchelonFormOf (A := A) B :=
  ⟨hRow, hEch⟩

section FinOperations

variable {a b : Nat}

lemma swap_matrix_eq_elem_mul_matrix (M : Matrix (Fin a) (Fin b) R)
    (r₁ r₂ : Fin a) :
    swapRow M r₁ r₂ = (swapRow (1 : Matrix (Fin a) (Fin a) R) r₁ r₂) * M := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases h1 : i = r₁
  · simp [swapRow, h1, one_apply]
  · by_cases h2 : i = r₂
    · simp [swapRow, h2, one_apply]
    · simp [swapRow, one_apply]

lemma factor_matrix_eq_elem_mul_matrix (M : Matrix (Fin a) (Fin b) R)
    (r : Fin a) (s : R) :
    factor M r s = (factor (1 : Matrix (Fin a) (Fin a) R) r s) * M := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases hr : i = r
  · subst hr
    simp [factor, one_apply]
  · simp [factor, one_apply, hr]

lemma replace_matrix_eq_elem_mul_matrix (M : Matrix (Fin a) (Fin b) R)
    (use toReplace : Fin a) (k : R) :
    replace M use toReplace k =
      (replace (1 : Matrix (Fin a) (Fin a) R) use toReplace k) * M := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases h1 : use = toReplace
  · simp [replace, h1]
    by_cases hr : i = toReplace
    · subst hr
      simp [factor, one_apply]
    · simp [factor, one_apply, hr]
  · by_cases h2 : i = toReplace
    · simp [replace, one_apply, h1, h2]
      ring_nf
      simp [Finset.sum_add_distrib]
    · simp [replace, one_apply, h1, h2]

/-- Apply one logged row operation to a matrix. -/
def applyRowOp (M : Matrix (Fin a) (Fin b) R) (op : RowOp a R) : Matrix (Fin a) (Fin b) R :=
  match op with
  | .swap i j => swapRow M i j
  | .factor i c => factor M i c
  | .replace use toReplace k => replace M use toReplace k

/-- Elementary matrix corresponding to one logged row operation. -/
def elementaryMatrixOfRowOp (op : RowOp a R) : Matrix (Fin a) (Fin a) R :=
  match op with
  | .swap i j => swapRow (1 : Matrix (Fin a) (Fin a) R) i j
  | .factor i c => factor (1 : Matrix (Fin a) (Fin a) R) i c
  | .replace use toReplace k => replace (1 : Matrix (Fin a) (Fin a) R) use toReplace k

lemma elementaryMatrixOfRowOp_mul_eq_applyRowOp
    (op : RowOp a R) (M : Matrix (Fin a) (Fin b) R) :
    elementaryMatrixOfRowOp op * M = applyRowOp M op := by
  cases op with
  | swap i j =>
      simpa [elementaryMatrixOfRowOp, applyRowOp] using
        (swap_matrix_eq_elem_mul_matrix (M := M) i j).symm
  | factor i c =>
      simpa [elementaryMatrixOfRowOp, applyRowOp] using
        (factor_matrix_eq_elem_mul_matrix (M := M) (r := i) (s := c)).symm
  | replace use toReplace k =>
      simpa [elementaryMatrixOfRowOp, applyRowOp] using
        (replace_matrix_eq_elem_mul_matrix
          (M := M) (use := use) (toReplace := toReplace) (k := k)).symm

omit [Field R] in
lemma swap_inv (M : Matrix (Fin a) (Fin b) R) (r₁ r₂ : Fin a) :
    swapRow (swapRow M r₁ r₂) r₁ r₂ = M := by
  ext i j
  simp only [swapRow, of_apply]
  split_ifs with h1 h2 h3
  · rw [h2, ← h1]
  · rw [← h1]
  · rw [← h3]
  · rfl

lemma factor_inv (M : Matrix (Fin a) (Fin b) R) (i : Fin a) (j : R) (hj : j ≠ 0) :
    factor (factor M i j) i j⁻¹ = M := by
  ext i j
  simp only [factor, of_apply]
  split_ifs with h1
  · simp [hj]
  · rfl

lemma replace_inv
    (M : Matrix (Fin a) (Fin b) R) (use toReplace : Fin a) (k : R)
    (h : use ≠ toReplace) :
    replace (replace M use toReplace k) use toReplace (-k) = M := by
  ext i j
  simp only [replace]
  split_ifs with h1
  · contradiction
  simp only [of_apply]
  split_ifs with h2
  · simp [h2]
  · rfl

private lemma swap_elem_isUnit (r₁ r₂ : Fin a) :
    IsUnit (swapRow (1 : Matrix (Fin a) (Fin a) R) r₁ r₂) := by
  let E : Matrix (Fin a) (Fin a) R := swapRow (1 : Matrix (Fin a) (Fin a) R) r₁ r₂
  have hmul : E * E = (1 : Matrix (Fin a) (Fin a) R) := by
    calc
      E * E = swapRow E r₁ r₂ := by
        symm
        simpa [E] using (swap_matrix_eq_elem_mul_matrix (M := E) r₁ r₂)
      _ = (1 : Matrix (Fin a) (Fin a) R) := by
        simpa [E] using (swap_inv (M := (1 : Matrix (Fin a) (Fin a) R)) r₁ r₂)
  refine ⟨⟨E, E, hmul, hmul⟩, rfl⟩

private lemma factor_elem_isUnit (i : Fin a) (j : R) (hj : j ≠ 0) :
    IsUnit (factor (1 : Matrix (Fin a) (Fin a) R) i j) := by
  let E : Matrix (Fin a) (Fin a) R := factor (1 : Matrix (Fin a) (Fin a) R) i j
  let Einv : Matrix (Fin a) (Fin a) R := factor (1 : Matrix (Fin a) (Fin a) R) i j⁻¹
  have hleft : Einv * E = (1 : Matrix (Fin a) (Fin a) R) := by
    calc
      Einv * E = factor E i j⁻¹ := by
        symm
        simpa [E, Einv] using (factor_matrix_eq_elem_mul_matrix (M := E) (r := i) (s := j⁻¹))
      _ = (1 : Matrix (Fin a) (Fin a) R) := by
        simpa [E] using
          (factor_inv (M := (1 : Matrix (Fin a) (Fin a) R)) (i := i) (j := j) hj)
  have hrightAux : factor Einv i j = (1 : Matrix (Fin a) (Fin a) R) := by
    have hjinv : j⁻¹ ≠ 0 := inv_ne_zero hj
    simpa [Einv, hj] using
      (factor_inv (M := (1 : Matrix (Fin a) (Fin a) R)) (i := i) (j := j⁻¹) hjinv)
  have hright : E * Einv = (1 : Matrix (Fin a) (Fin a) R) := by
    calc
      E * Einv = factor Einv i j := by
        symm
        simpa [E, Einv] using (factor_matrix_eq_elem_mul_matrix (M := Einv) (r := i) (s := j))
      _ = (1 : Matrix (Fin a) (Fin a) R) := hrightAux
  refine ⟨⟨E, Einv, hright, hleft⟩, rfl⟩

private lemma replace_elem_isUnit (use toReplace : Fin a) (k : R) (huse : use ≠ toReplace) :
    IsUnit (replace (1 : Matrix (Fin a) (Fin a) R) use toReplace k) := by
  let E : Matrix (Fin a) (Fin a) R := replace (1 : Matrix (Fin a) (Fin a) R) use toReplace k
  let Einv : Matrix (Fin a) (Fin a) R := replace (1 : Matrix (Fin a) (Fin a) R) use toReplace (-k)
  have hleft : Einv * E = (1 : Matrix (Fin a) (Fin a) R) := by
    calc
      Einv * E = replace E use toReplace (-k) := by
        symm
        simpa [E, Einv] using
          (replace_matrix_eq_elem_mul_matrix (M := E) (use := use) (toReplace := toReplace)
            (k := -k))
      _ = (1 : Matrix (Fin a) (Fin a) R) := by
        simpa [E] using
          (replace_inv (M := (1 : Matrix (Fin a) (Fin a) R))
            (use := use) (toReplace := toReplace) (k := k) huse)
  have hrightAux : replace Einv use toReplace k = (1 : Matrix (Fin a) (Fin a) R) := by
    simpa [Einv] using
      (replace_inv (M := (1 : Matrix (Fin a) (Fin a) R))
        (use := use) (toReplace := toReplace) (k := -k) huse)
  have hright : E * Einv = (1 : Matrix (Fin a) (Fin a) R) := by
    calc
      E * Einv = replace Einv use toReplace k := by
        symm
        simpa [E, Einv] using
          (replace_matrix_eq_elem_mul_matrix (M := Einv) (use := use) (toReplace := toReplace)
            (k := k))
      _ = (1 : Matrix (Fin a) (Fin a) R) := hrightAux
  refine ⟨⟨E, Einv, hright, hleft⟩, rfl⟩

lemma rowEquivalent_swapRow
    (A : Matrix (Fin a) (Fin b) R) (r₁ r₂ : Fin a) :
    RowEquivalent A (swapRow A r₁ r₂) := by
  rcases swap_elem_isUnit (R := R) (a := a) r₁ r₂ with ⟨U, hU⟩
  refine ⟨U, ?_⟩
  calc
    swapRow A r₁ r₂
      = (swapRow (1 : Matrix (Fin a) (Fin a) R) r₁ r₂) * A := by
        simpa using (swap_matrix_eq_elem_mul_matrix (M := A) r₁ r₂)
    _ = (U : Matrix (Fin a) (Fin a) R) * A := by
        simp [hU]

lemma rowEquivalent_factor
    (A : Matrix (Fin a) (Fin b) R) (i : Fin a) (j : R) (hj : j ≠ 0) :
    RowEquivalent A (factor A i j) := by
  rcases factor_elem_isUnit (R := R) (a := a) i j hj with ⟨U, hU⟩
  refine ⟨U, ?_⟩
  calc
    factor A i j = (factor (1 : Matrix (Fin a) (Fin a) R) i j) * A := by
      simpa using (factor_matrix_eq_elem_mul_matrix (M := A) (r := i) (s := j))
    _ = (U : Matrix (Fin a) (Fin a) R) * A := by
      simp [hU]

lemma rowEquivalent_replace
    (A : Matrix (Fin a) (Fin b) R) (use toReplace : Fin a) (k : R)
    (huse : use ≠ toReplace) :
    RowEquivalent A (replace A use toReplace k) := by
  rcases replace_elem_isUnit (R := R) (a := a) use toReplace k huse with ⟨U, hU⟩
  refine ⟨U, ?_⟩
  calc
    replace A use toReplace k
      = (replace (1 : Matrix (Fin a) (Fin a) R) use toReplace k) * A := by
          simpa using
            (replace_matrix_eq_elem_mul_matrix (M := A) (use := use) (toReplace := toReplace)
              (k := k))
    _ = (U : Matrix (Fin a) (Fin a) R) * A := by
      simp [hU]

end FinOperations

end Matrix

namespace ColumnElementary

variable {R : Type} [Field R] [DecidableEq R]
variable {a : Nat}

def swapCol
    (given : Matrix (Fin a) (Fin a) R) (col1 col2 : Fin a) :
    Matrix (Fin a) (Fin a) R :=
  (swapRow given.transpose col1 col2).transpose

def factorCol
    (given : Matrix (Fin a) (Fin a) R) (col : Fin a) (scale : R) :
    Matrix (Fin a) (Fin a) R :=
  (factor given.transpose col scale).transpose

def replaceCol
    (given : Matrix (Fin a) (Fin a) R) (use toReplace : Fin a) (k : R) :
    Matrix (Fin a) (Fin a) R :=
  (replace given.transpose toReplace use k).transpose

omit [DecidableEq R] in
lemma elem_swap_transpose (c1 c2 : Fin a) :
    (Matrix.elementaryMatrixOfRowOp (.swap c1 c2 : RowOp a R)).transpose =
      Matrix.elementaryMatrixOfRowOp (.swap c1 c2 : RowOp a R) := by
  ext i j
  by_cases hi1 : i = c1
  all_goals
    by_cases hi2 : i = c2
    all_goals
      by_cases hj1 : j = c1
      all_goals
        by_cases hj2 : j = c2
        all_goals
          simp [Matrix.elementaryMatrixOfRowOp, swapRow, Matrix.one_apply, hi1, hi2, hj1, hj2]
          try aesop

omit [DecidableEq R] in
lemma elem_factor_transpose (c : Fin a) (s : R) :
    (Matrix.elementaryMatrixOfRowOp (.factor c s : RowOp a R)).transpose =
      Matrix.elementaryMatrixOfRowOp (.factor c s : RowOp a R) := by
  ext i j
  by_cases hi : i = c
  all_goals
    by_cases hj : j = c
    all_goals
      simp [Matrix.elementaryMatrixOfRowOp, factor, Matrix.one_apply, hi, hj]
      try aesop

omit [DecidableEq R] in
lemma elem_replace_transpose (use toReplace : Fin a) (k : R) :
    (Matrix.elementaryMatrixOfRowOp (.replace use toReplace k : RowOp a R)).transpose =
      Matrix.elementaryMatrixOfRowOp (.replace toReplace use k : RowOp a R) := by
  by_cases h : use = toReplace
  case pos =>
    subst h
    simpa [Matrix.elementaryMatrixOfRowOp, replace] using
      (elem_factor_transpose (R := R) (a := a) use (k + 1))
  case neg =>
    ext i j
    by_cases hiUse : i = use
    all_goals
      by_cases hiToReplace : i = toReplace
      all_goals
        by_cases hjUse : j = use
        all_goals
          by_cases hjToReplace : j = toReplace
          all_goals
            simp [Matrix.elementaryMatrixOfRowOp, replace, factor, Matrix.one_apply,
              h, hiUse, hiToReplace, hjUse, hjToReplace]
            try aesop

omit [DecidableEq R] in
lemma swapCol_eq_mul_elem
    (M : Matrix (Fin a) (Fin a) R) (c1 c2 : Fin a) :
    swapCol M c1 c2 =
      M * Matrix.elementaryMatrixOfRowOp (.swap c1 c2 : RowOp a R) := by
  let op : RowOp a R := .swap c1 c2
  have h := Matrix.elementaryMatrixOfRowOp_mul_eq_applyRowOp (op := op) (M := M.transpose)
  have ht := congrArg Matrix.transpose h
  simpa [
    op, swapCol, Matrix.applyRowOp, Matrix.transpose_mul, elem_swap_transpose
  ] using
    ht.symm

omit [DecidableEq R] in
lemma factorCol_eq_mul_elem
    (M : Matrix (Fin a) (Fin a) R) (c : Fin a) (s : R) :
    factorCol M c s =
      M * Matrix.elementaryMatrixOfRowOp (.factor c s : RowOp a R) := by
  let op : RowOp a R := .factor c s
  have h := Matrix.elementaryMatrixOfRowOp_mul_eq_applyRowOp (op := op) (M := M.transpose)
  have ht := congrArg Matrix.transpose h
  simpa [
    op, factorCol, Matrix.applyRowOp, Matrix.transpose_mul, elem_factor_transpose
  ] using
    ht.symm

omit [DecidableEq R] in
lemma replaceCol_eq_mul_elem
    (M : Matrix (Fin a) (Fin a) R) (use toReplace : Fin a) (k : R) :
    replaceCol M use toReplace k =
      M * Matrix.elementaryMatrixOfRowOp (.replace use toReplace k : RowOp a R) := by
  let opT : RowOp a R := .replace toReplace use k
  have h := Matrix.elementaryMatrixOfRowOp_mul_eq_applyRowOp (op := opT) (M := M.transpose)
  have ht := congrArg Matrix.transpose h
  simpa [
    opT, replaceCol, Matrix.applyRowOp, Matrix.transpose_mul, elem_replace_transpose
  ] using
    ht.symm

end ColumnElementary
