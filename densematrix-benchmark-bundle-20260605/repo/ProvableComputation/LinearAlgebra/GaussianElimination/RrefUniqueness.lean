import ProvableComputation.LinearAlgebra.GaussianElimination.Elementary
import ProvableComputation.LinearAlgebra.GaussianElimination.RrefCorrectness

/-!
# RREF uniqueness: canonical representative and semantic uniqueness

This file organizes the uniqueness story for reduced row echelon form in two
parallel viewpoints.

* `IsReducedEchelonFormOf A B` is the semantic predicate saying that `B` is a
  valid RREF representative of `A`: it is row-equivalent to `A` and reduced.
* `IsCanonicalRrefOf A B` is the canonical predicate saying that `B` is exactly
  the algorithm output `(GaussianEliminationInternal.rawReducedRowEchelonForm A).1`.
* `RrefUniquenessSemanticGoal` states the stage-2 semantic specification: any
  two semantic representatives of the same source matrix are equal.

The bridge is built in two steps.

1. Show the algorithmic pipeline preserves row-equivalence
   (`GaussianEliminationInternal.eliminateColLoop`,
   `GaussianEliminationInternal.eliminateColCore`,
   `GaussianEliminationInternal.rowReductionAux`, and finally
   `GaussianEliminationInternal.rawReducedRowEchelonForm`).
2. Prove semantic uniqueness of reduced representatives under row-equivalence
   and then derive canonical equalities as corollaries.
-/

namespace Matrix

variable {R : Type} [Field R]

set_option linter.style.longLine false

/-- `B` is an RREF representative of `A`: row-equivalent to `A` and in reduced echelon form. -/
def IsReducedEchelonFormOf {m n : Nat}
    [DecidableEq R]
    (A B : Matrix (Fin m) (Fin n) R) : Prop :=
  RowEquivalent A B ∧ IsReducedEchelonForm (M := B)

/-- Projection lemma: extract row-equivalence from `IsReducedEchelonFormOf`. -/
lemma IsReducedEchelonFormOf.rowEquivalent {m n : Nat}
    [DecidableEq R]
    {A B : Matrix (Fin m) (Fin n) R} (h : IsReducedEchelonFormOf (A := A) B) :
    RowEquivalent A B :=
  h.1

/-- Projection lemma: extract reducedness from `IsReducedEchelonFormOf`. -/
lemma IsReducedEchelonFormOf.reduced {m n : Nat}
    [DecidableEq R]
    {A B : Matrix (Fin m) (Fin n) R} (h : IsReducedEchelonFormOf (A := A) B) :
    IsReducedEchelonForm (M := B) :=
  h.2

/-- Constructor-style packaging lemma for `IsReducedEchelonFormOf`. -/
lemma isReducedEchelonFormOf_mk {m n : Nat}
    [DecidableEq R]
    {A B : Matrix (Fin m) (Fin n) R}
    (hRow : RowEquivalent A B)
    (hRed : IsReducedEchelonForm (M := B)) :
    IsReducedEchelonFormOf (A := A) B :=
  ⟨hRow, hRed⟩

section Canonical

variable [DecidableEq R]

/--
Canonical representative predicate.

This is intentionally algorithmic: `B` must be definitionally the selected
output of `GaussianEliminationInternal.rawReducedRowEchelonForm`. It is not the semantic "any reduced
representative" notion.
-/
def IsCanonicalRrefOf {m n : Nat}
    (A B : Matrix (Fin m) (Fin n) R) : Prop :=
  B = (GaussianEliminationInternal.rawReducedRowEchelonForm A).1

/-- The algorithm output is canonical for its own input matrix. -/
lemma isCanonicalRrefOf_reducedRowEchelonForm {m n : Nat}
    (A : Matrix (Fin m) (Fin n) R) :
    IsCanonicalRrefOf A (GaussianEliminationInternal.rawReducedRowEchelonForm A).1 :=
  rfl

/--
Uniqueness at the canonical level is definitional.

If both `B` and `B'` are stated to be the same algorithm output of `A`,
they are equal by rewriting.
-/
theorem IsCanonicalRrefOf.unique {m n : Nat}
    {A B B' : Matrix (Fin m) (Fin n) R}
    (hB : IsCanonicalRrefOf A B)
    (hB' : IsCanonicalRrefOf A B') :
    B = B' := by
  calc
    B = (GaussianEliminationInternal.rawReducedRowEchelonForm A).1 := hB
    _ = B' := hB'.symm

/--
Canonical representative implies reduced form.

This connects the algorithm-chosen representative to semantic properties by
reusing the canonical structured wrapper theorem.
-/
lemma IsCanonicalRrefOf.reduced {m n : Nat}
    {A B : Matrix (Fin m) (Fin n) R}
    (hB : IsCanonicalRrefOf A B) :
    IsReducedEchelonForm (M := B) := by
  rcases hB with rfl
  simpa [Matrix.reducedRowEchelonForm] using
    Matrix.reducedRowEchelonForm_isReducedEchelonForm (M := A)

end Canonical

section AlgorithmBridge

variable [DecidableEq R]

/--
Core invariance lemma for `GaussianEliminationInternal.eliminateColLoop`.

No matter which branch is taken while scanning rows (skip pivot row, replace,
or continue), the matrix stays row-equivalent to the input `cur`.
-/
private theorem eliminateColGo_rowEquivalent
    {m n : Nat}
    (pivotRow : Fin m) (pivotCol : Fin n) (row : Nat)
    (cur : Matrix (Fin m) (Fin n) R) (steps : List (RowOp m R)) :
    RowEquivalent cur (GaussianEliminationInternal.eliminateColLoop pivotRow pivotCol row cur steps).1 := by
  have goAux_matrix_eq
      (pivotVal : R) (row : Nat) (cur : Matrix (Fin m) (Fin n) R) (steps : List (RowOp m R))
      (hpivot : cur pivotRow pivotCol = pivotVal) :
      (GaussianEliminationInternal.eliminateColLoopAux pivotRow pivotCol pivotVal row cur steps).1 =
        (GaussianEliminationInternal.eliminateColLoop pivotRow pivotCol row cur steps).1 := by
    simp [GaussianEliminationInternal.eliminateColLoop, hpivot]
  rw [GaussianEliminationInternal.eliminateColLoop, GaussianEliminationInternal.eliminateColLoopAux]
  split_ifs with hr
  · let i : Fin m := ⟨row, hr⟩
    -- At a valid scan row `i`, split into "pivot row" versus "non-pivot row".
    by_cases hEq : i = pivotRow
    · simpa [i, hEq] using
        (eliminateColGo_rowEquivalent pivotRow pivotCol (row + 1) cur steps)
    -- For non-pivot rows, branch on whether elimination is needed.
    · by_cases hcoeff : cur i pivotCol ≠ 0
      -- Nonzero coefficient: perform one row replacement, then recurse.
      · let cur' := replace cur pivotRow i (-cur i pivotCol / cur pivotRow pivotCol)
        let steps' := List.concat steps (.replace pivotRow i (-cur i pivotCol / cur pivotRow pivotCol))
        have hreplace : RowEquivalent cur cur' := by
          dsimp [cur']
          exact rowEquivalent_replace
            (A := cur) (use := pivotRow) (toReplace := i) (k := -cur i pivotCol / cur pivotRow pivotCol)
            (huse := by simpa [eq_comm] using hEq)
        have hpivot' : cur' pivotRow pivotCol = cur pivotRow pivotCol := by
          have huse : pivotRow ≠ i := by
            intro hpr
            exact hEq hpr.symm
          simp [cur', replace, huse, of_apply]
        have hrec :
            RowEquivalent cur' (GaussianEliminationInternal.eliminateColLoop pivotRow pivotCol (row + 1) cur' steps').1 := by
          simpa [cur', steps'] using
            (eliminateColGo_rowEquivalent pivotRow pivotCol (row + 1) cur' steps')
        have hrec' :
            RowEquivalent cur'
              (GaussianEliminationInternal.eliminateColLoopAux pivotRow pivotCol (cur pivotRow pivotCol) (row + 1) cur' steps').1 := by
          simpa [goAux_matrix_eq (pivotVal := cur pivotRow pivotCol) (row := row + 1)
            (cur := cur') (steps := steps') hpivot'] using hrec
        simpa [i, hEq, hcoeff, cur', steps'] using RowEquivalent.trans hreplace hrec'
      -- Zero coefficient: no operation at this row; recurse directly.
      · simpa [i, hEq, hcoeff] using
          (eliminateColGo_rowEquivalent pivotRow pivotCol (row + 1) cur steps)
  -- End of scan (`row` out of range): result is definitionally unchanged.
  · simpa using (RowEquivalent.refl cur)

/--
Wrapper lemma for `GaussianEliminationInternal.eliminateColCore`.

The boolean `reduced` only changes the starting scan row; both branches are
delegated to `eliminateColGo_rowEquivalent`.
-/
private theorem eliminateCol_rowEquivalent
    {m n : Nat}
    (M : Matrix (Fin m) (Fin n) R) (pivotRow : Fin m) (pivotCol : Fin n)
    (steps : List (RowOp m R)) (reduced : Bool) :
    RowEquivalent M (GaussianEliminationInternal.eliminateColCore M pivotRow pivotCol steps reduced).1 := by
  rw [GaussianEliminationInternal.eliminateColCore]
  by_cases hred : reduced
  · simpa [hred] using
      (eliminateColGo_rowEquivalent (pivotRow := pivotRow) (pivotCol := pivotCol)
        (row := 0) (cur := M) (steps := steps))
  · simpa [hred] using
      (eliminateColGo_rowEquivalent (pivotRow := pivotRow) (pivotCol := pivotCol)
        (row := pivotRow.1) (cur := M) (steps := steps))

/--
Main bridge lemma for the RREF driver `GaussianEliminationInternal.rowReductionAux`.

Each algorithmic stage preserves row-equivalence:
`M -> m1` (optional swap), `m1 -> m2` (optional normalization),
`m2 -> m3` (column elimination), then recursive call on `(row+1, col+1)`.
-/
private theorem rrefAux_rowEquivalent
    {m n : Nat}
    (M : Matrix (Fin m) (Fin n) R) (row col : Nat)
    (steps : List (RowOp m R)) (reduced : Bool) :
    RowEquivalent M (GaussianEliminationInternal.rowReductionAux M row col steps reduced).1 := by
  rw [GaussianEliminationInternal.rowReductionAux.eq_1]
  split_ifs with hrow hcol
  -- Active region: both row and column are in range.
  · cases hcp : checkPivot M row col with
    | none =>
        -- No pivot candidate: this branch returns `M` unchanged.
        simp only
        exact RowEquivalent.refl M
    | some prpc =>
        rcases prpc with ⟨pivotRow, pivotCol⟩
        let rowFin : Fin m := ⟨row, hrow⟩
        -- `m1`: swap pivot row into current row when needed.
        let m1 : Matrix (Fin m) (Fin n) R :=
          if pivotRow.1 = row then M else swapRow M rowFin pivotRow
        let steps1 : List (RowOp m R) := List.concat steps (.swap rowFin pivotRow)
        -- `m2`: normalize pivot value to `1` when needed.
        let pivotVal : R := m1 rowFin pivotCol
        let m2 : Matrix (Fin m) (Fin n) R :=
          if !reduced || pivotVal = 1 then m1 else factor m1 rowFin pivotVal⁻¹
        let steps2 : List (RowOp m R) :=
          if !reduced || pivotVal = 1 then
            steps1
          else
            List.concat steps1 (.factor rowFin pivotVal⁻¹)
        -- Stage 1: row-equivalence from optional swap.
        have hM1 : RowEquivalent M m1 := by
          by_cases hp : pivotRow.1 = row
          · simpa [m1, hp] using (RowEquivalent.refl M)
          · simpa [m1, hp] using (rowEquivalent_swapRow (A := M) rowFin pivotRow)
        -- Pivot entry used for normalization is nonzero.
        have hpivot_ne_zero : pivotVal ≠ 0 := by
          have hnon : M pivotRow pivotCol ≠ 0 :=
            checkPivot_some_nonzero (M := M) row col (h := by simp [hcp])
          by_cases hp : pivotRow.1 = row
          · have hroweq : rowFin = pivotRow := by
              exact Fin.ext (by simpa [rowFin] using hp.symm)
            subst hroweq
            simpa [m1, hp, pivotVal] using hnon
          · have hrowne : rowFin ≠ pivotRow := by
              intro hEq
              exact hp (by simpa [rowFin] using (congrArg Fin.val hEq).symm)
            have hpres :
                (swapRow M rowFin pivotRow) rowFin pivotCol = M pivotRow pivotCol := by
              simp [swapRow, of_apply]
            simpa [m1, hp, pivotVal, hpres] using hnon
        -- Stage 2: row-equivalence from optional scaling of pivot row.
        have hM2 : RowEquivalent m1 m2 := by
          cases hred : reduced with
          | false =>
              simpa [m2, hred] using (RowEquivalent.refl m1)
          | true =>
              by_cases hv : pivotVal = 1
              · simpa [m2, hred, hv] using (RowEquivalent.refl m1)
              · have hfac : RowEquivalent m1 (factor m1 rowFin pivotVal⁻¹) :=
                  rowEquivalent_factor (A := m1) (i := rowFin) (j := pivotVal⁻¹)
                    (hj := inv_ne_zero hpivot_ne_zero)
                simpa [m2, hred, hv] using hfac
        -- Stage 3+4: elimination then recursive processing of the smaller subproblem.
        cases hp : GaussianEliminationInternal.eliminateColCore m2 rowFin pivotCol steps2 reduced with
        | mk m3 steps3 =>
            have hM3raw : RowEquivalent m2 (GaussianEliminationInternal.eliminateColCore m2 rowFin pivotCol steps2 reduced).1 := by
              simpa using
                (eliminateCol_rowEquivalent (M := m2) (pivotRow := rowFin) (pivotCol := pivotCol)
                  (steps := steps2) (reduced := reduced))
            have hRec : RowEquivalent m3 (GaussianEliminationInternal.rowReductionAux m3 (row + 1) (col + 1) steps3 reduced).1 := by
              simpa using
                (rrefAux_rowEquivalent (M := m3) (row := row + 1) (col := col + 1)
                  (steps := steps3) (reduced := reduced))
            have hRecraw :
                RowEquivalent (GaussianEliminationInternal.eliminateColCore m2 rowFin pivotCol steps2 reduced).1
                  (GaussianEliminationInternal.rowReductionAux
                    (GaussianEliminationInternal.eliminateColCore m2 rowFin pivotCol steps2 reduced).1
                    (row + 1) (col + 1)
                    (GaussianEliminationInternal.eliminateColCore m2 rowFin pivotCol steps2 reduced).2 reduced).1 := by
              simpa [hp] using hRec
            -- Compose all stages into a single row-equivalence from `M`.
            simpa [m1, m2, steps1, steps2, pivotVal, rowFin, hcp, hp, List.concat_eq_append] using
              RowEquivalent.trans (RowEquivalent.trans hM1 (RowEquivalent.trans hM2 hM3raw)) hRecraw
  -- Out-of-range guards: algorithm returns immediately with no matrix change.
  · simp only
    exact RowEquivalent.refl M
  · simp only
    exact RowEquivalent.refl M
termination_by m - row
decreasing_by
  · omega

/--
Top-level algorithmic invariant.

`GaussianEliminationInternal.rawReducedRowEchelonForm` always returns a matrix row-equivalent to its input.
-/
theorem reducedRowEchelonForm_rowEquivalent
    {m n : Nat}
    (A : Matrix (Fin m) (Fin n) R) :
    RowEquivalent A (GaussianEliminationInternal.rawReducedRowEchelonForm A).1 := by
  simpa [GaussianEliminationInternal.rawReducedRowEchelonForm] using
    (rrefAux_rowEquivalent (M := A) (row := 0) (col := 0) (steps := List.nil) (reduced := true))

/--
Bridge theorem from algorithm output to semantic predicate:
the computed output is both row-equivalent to `A` and reduced.
-/
theorem reducedRowEchelonForm_isReducedEchelonFormOf
    {m n : Nat}
    (A : Matrix (Fin m) (Fin n) R) :
    IsReducedEchelonFormOf A (GaussianEliminationInternal.rawReducedRowEchelonForm A).1 := by
  refine ⟨reducedRowEchelonForm_rowEquivalent (A := A), ?_⟩
  simpa [Matrix.reducedRowEchelonForm] using
    Matrix.reducedRowEchelonForm_isReducedEchelonForm (M := A)

/--
Auxiliary bridge theorem: algorithm output is also in echelon form.

This is weaker than reduced form but useful when a statement only requires
`IsEchelonFormOf`.
-/
theorem reducedRowEchelonForm_isEchelonFormOf
    {m n : Nat}
    (A : Matrix (Fin m) (Fin n) R) :
    IsEchelonFormOf (A := A) ((GaussianEliminationInternal.rawReducedRowEchelonForm A).1) := by
  refine ⟨reducedRowEchelonForm_rowEquivalent (A := A), ?_⟩
  simpa [Matrix.reducedRowEchelonForm] using
    Matrix.reducedRowEchelonForm_isEchelonForm (M := A)

/-- The algorithm output is canonical by definition (`rfl`). -/
lemma reducedRowEchelonForm_isCanonicalRrefOf
    {m n : Nat}
    (A : Matrix (Fin m) (Fin n) R) :
    IsCanonicalRrefOf A (GaussianEliminationInternal.rawReducedRowEchelonForm A).1 :=
  rfl

/--
If two matrices have the same computed RREF, then they are row-equivalent.
-/
theorem rowEquivalent_of_rref_eq {m n : Nat}
    {A B : Matrix (Fin m) (Fin n) R}
    (hEq : (GaussianEliminationInternal.rawReducedRowEchelonForm A).1 = (GaussianEliminationInternal.rawReducedRowEchelonForm B).1) :
    RowEquivalent A B := by
  let C : Matrix (Fin m) (Fin n) R := (GaussianEliminationInternal.rawReducedRowEchelonForm A).1
  have hAC : RowEquivalent A C := by
    simpa [C] using reducedRowEchelonForm_rowEquivalent (A := A)
  have hBC : RowEquivalent B C := by
    simpa [C, hEq] using reducedRowEchelonForm_rowEquivalent (A := B)
  exact RowEquivalent.trans hAC (RowEquivalent.symm hBC)

/--
Computational wrapper: if `decide` confirms RREF equality, conclude row-equivalence.
This is convenient with `native_decide` on concrete matrices.
example : RowEquivalent A B := by
  apply rowEquivalent_of_decide_rref_eq_true (A := A) (B := B)
  native_decide
-/
theorem rowEquivalent_of_decide_rref_eq_true {m n : Nat}
    {A B : Matrix (Fin m) (Fin n) R}
    (hEq : decide ((GaussianEliminationInternal.rawReducedRowEchelonForm A).1 = (GaussianEliminationInternal.rawReducedRowEchelonForm B).1) = true) :
    RowEquivalent A B := by
  exact rowEquivalent_of_rref_eq (A := A) (B := B) (of_decide_eq_true hEq)

end AlgorithmBridge

/-- Row-equivalent matrices have the same homogeneous solution set. -/
lemma RowEquivalent.mul_eq_zero_iff {m n : Nat}
    {A B : Matrix (Fin m) (Fin n) R}
    (hAB : RowEquivalent A B)
    (x : Matrix (Fin n) (Fin 1) R) :
    A * x = 0 ↔ B * x = 0 := by
  rcases hAB with ⟨U, rfl⟩
  constructor
  · intro h
    simp [h, Matrix.mul_assoc]
  · intro h
    have hmul := congrArg (fun Y : Matrix (Fin m) (Fin 1) R =>
      ((↑(U⁻¹) : Matrix (Fin m) (Fin m) R) * Y)) h
    simpa [Matrix.mul_assoc] using hmul

/--
If `B` and `B'` come from the same source by row-equivalence,
they define the same homogeneous equations.
-/
lemma rowEquivalent_common_source_mul_eq_zero_iff {m n : Nat}
    {A B B' : Matrix (Fin m) (Fin n) R}
    (hAB : RowEquivalent A B)
    (hAB' : RowEquivalent A B')
    (x : Matrix (Fin n) (Fin 1) R) :
    B * x = 0 ↔ B' * x = 0 := by
  have hBB' : RowEquivalent B B' :=
    RowEquivalent.trans (RowEquivalent.symm hAB) hAB'
  simpa using (RowEquivalent.mul_eq_zero_iff (hAB := hBB') x)

/--
In reduced form, every non-pivot row has `0` in a pivot column.

This combines "zero above pivot" and "zero below pivot" into one lemma by
splitting on the row order relation.
-/
private lemma reduced_pivot_col_zero_ne {m n : Nat}
    {M : Matrix (Fin m) (Fin n) R}
    (hRed : IsReducedEchelonForm (M := M))
    {i r : Fin m} {p : Fin n}
    (hp : IsPivot M i p)
    (hr : r ≠ i) :
    M r p = 0 := by
  by_cases hri : r < i
  · exact hRed.pivot_column_zero_above i r p hri hp
  · have hir_or_eq : i < r ∨ i = r := lt_or_eq_of_le (le_of_not_gt hri)
    cases hir_or_eq with
    | inl hir =>
        exact hRed.echelon.pivot_column_zero_below i r p hir hp
    | inr hir_eq =>
        exact (hr hir_eq.symm).elim

/--
Kronecker-delta view of a pivot column.

For a pivot `(i,p)` in reduced form, column `p` equals `1` at row `i` and `0`
everywhere else.
-/
private lemma reduced_pivot_col_unit {m n : Nat}
    {M : Matrix (Fin m) (Fin n) R}
    (hRed : IsReducedEchelonForm (M := M))
    {i r : Fin m} {p : Fin n}
    (hp : IsPivot M i p) :
    M r p = if r = i then 1 else 0 := by
  by_cases hri : r = i
  · subst hri
    simpa using hRed.pivot_is_one r p hp
  · simp [hri, reduced_pivot_col_zero_ne hRed hp hri]

/--
Coefficient extraction from a pivot column.

If `B = U * C` and column `q` of `C` is a pivot column with pivot row `k`,
then entry `B i q` is exactly the coefficient `U i k`.
-/
private lemma coeff_from_pivot_column {m n : Nat}
    {B C : Matrix (Fin m) (Fin n) R}
    (hC : IsReducedEchelonForm (M := C))
    (U : Matrix (Fin m) (Fin m) R)
    (hBC : B = U * C)
    {k i : Fin m} {q : Fin n}
    (hq : IsPivot C k q) :
    B i q = U i k := by
  have hEntry : B i q = (U * C) i q := by simp [hBC]
  rw [Matrix.mul_apply] at hEntry
  have hsum : (∑ t, U i t * C t q) = U i k := by
    calc
      (∑ t, U i t * C t q)
          = ∑ t, U i t * (if t = k then 1 else 0) := by
              refine Finset.sum_congr rfl ?_
              intro t _
              simp [reduced_pivot_col_unit hC hq]
      _ = U i k := by simp
  simpa [hsum] using hEntry

/--
Row-level matching relation used in the uniqueness proof.

At row `i`, either both matrices are zero rows, or they share the same pivot
column at that row.
-/
private def RowMatch {m n : Nat}
    (B C : Matrix (Fin m) (Fin n) R) (i : Fin m) : Prop :=
  (RowIsZero B i ∧ RowIsZero C i) ∨ ∃ p : Fin n, IsPivot B i p ∧ IsPivot C i p

/--
Pivot-column transfer lemma (from left matrix to right matrix).

Given row-equivalence and reducedness of `C`, every pivot column appearing in
`B` must also appear as a pivot column in `C` (possibly at another row).
-/
private lemma pivot_exists_in_right {m n : Nat}
    {B C : Matrix (Fin m) (Fin n) R}
    (hBC : RowEquivalent B C)
    (hC : IsReducedEchelonForm (M := C))
    {i : Fin m} {p : Fin n}
    (hpB : IsPivot B i p) :
    ∃ k : Fin m, IsPivot C k p := by
  rcases RowEquivalent.symm hBC with ⟨UUnit, hUraw⟩
  let U : Matrix (Fin m) (Fin m) R := (UUnit : Matrix (Fin m) (Fin m) R)
  have hU : B = U * C := by simpa [U] using hUraw
  by_contra hnone
  have hsumZero : (∑ t, U i t * C t p) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro t _
    -- Classify each row of `C` as zero-row or pivot-row.
    cases hCt : hC.echelon.row_zero_or_pivot t with
    | inl hZero =>
        simp [hZero p]
    | inr hPivot =>
        rcases hPivot with ⟨q, hq⟩
        -- Split by whether the pivot column in row `t` equals the target `p`.
        by_cases hqp : q = p
        · exact (hnone ⟨t, by simpa [hqp] using hq⟩).elim
        · rcases lt_or_gt_of_ne hqp with hqLt | hpLt
          -- Case `q < p`: pivot property of `B` forces the coefficient `U i t` to vanish.
          · have hUit : U i t = 0 := by
              have hCoeff : B i q = U i t :=
                coeff_from_pivot_column (hC := hC) (U := U) (hBC := hU)
                  (k := t) (i := i) (q := q) hq
              have hBiq : B i q = 0 := hpB.2 q hqLt
              calc
                U i t = B i q := hCoeff.symm
                _ = 0 := hBiq
            simp [hUit]
          -- Case `p < q`: pivot property of `C` gives `C t p = 0`.
          · have hCtp : C t p = 0 := hq.2 p hpLt
            simp [hCtp]
  have hBpZero : B i p = 0 := by
    calc
      B i p = (U * C) i p := by simp [hU]
      _ = ∑ t, U i t * C t p := by simp [Matrix.mul_apply]
      _ = 0 := hsumZero
  exact hpB.1 hBpZero

/--
Symmetric pivot-column transfer lemma (right matrix to left matrix).

This is `pivot_exists_in_right` applied to the symmetric row-equivalence.
-/
private lemma pivot_exists_in_left {m n : Nat}
    {B C : Matrix (Fin m) (Fin n) R}
    (hBC : RowEquivalent B C)
    (hB : IsReducedEchelonForm (M := B))
    {i : Fin m} {p : Fin n}
    (hpC : IsPivot C i p) :
    ∃ k : Fin m, IsPivot B k p := by
  simpa using
    (pivot_exists_in_right (hBC := RowEquivalent.symm hBC) (hC := hB) hpC)

/--
Key row-by-row alignment theorem under row-equivalence and reducedness.

For each row index `i`, matrices `B` and `C` either are both zero rows or
share the same pivot column at row `i`.
-/
private theorem reduced_rowMatch_of_rowEquivalent {m n : Nat}
    {B C : Matrix (Fin m) (Fin n) R}
    (hBC : RowEquivalent B C)
    (hB : IsReducedEchelonForm (M := B))
    (hC : IsReducedEchelonForm (M := C)) :
    ∀ i : Fin m, RowMatch (R := R) B C i := by
  -- Work in `Nat` indices so strong induction can recurse on smaller rows.
  have hMatchNat : ∀ iNat : Nat, ∀ hi : iNat < m, RowMatch (R := R) B C ⟨iNat, hi⟩ := by
    intro iNat
    refine Nat.strong_induction_on iNat ?_
    intro iNat ih hi
    let iFin : Fin m := ⟨iNat, hi⟩
    -- First split on whether row `i` of `B` is zero or has a pivot.
    cases hBi : hB.echelon.row_zero_or_pivot iFin with
    | inl hBZero =>
        -- `B` row `i` is zero: prove row `i` in `C` is also zero.
        have hCZero : RowIsZero C iFin := by
          cases hCi : hC.echelon.row_zero_or_pivot iFin with
          | inl hZero =>
              exact hZero
          | inr hPivot =>
              -- Contradiction: if `C` had a pivot here, it must transfer to `B`.
              rcases hPivot with ⟨q, hqC⟩
              rcases pivot_exists_in_left (hBC := hBC) (hB := hB) hqC with ⟨k, hkB⟩
              rcases lt_trichotomy k.1 iNat with hkLt | hkEq | hiLt
              -- `k < i`: use induction hypothesis at row `k`.
              · have hkMatch : RowMatch (R := R) B C k := ih k.1 hkLt k.2
                cases hkMatch with
                | inl hZeroPair =>
                    exact (RowIsZero.not_isPivot (hzero := hZeroPair.1) (hp := hkB)).elim
                | inr hPivotPair =>
                    -- Two pivots in row `k` of `B` force the same column.
                    -- Then strict increase gives the contradiction `q < q`.
                    rcases hPivotPair with ⟨qk, hkB', hkCk⟩
                    have hqk : qk = q := IsPivot.eq_of_left hkB' hkB
                    have hkCq : IsPivot C k q := by simpa [hqk] using hkCk
                    have hkLt' : k < iFin := by simpa [iFin] using hkLt
                    have hqLtq : q < q :=
                      hC.echelon.pivots_strictly_increasing k iFin q q hkLt' hkCq hqC
                    exact (lt_irrefl _ hqLtq).elim
              -- `k = i`: `B` row `i` is zero, cannot host pivot.
              · have hkEqFin : k = iFin := Fin.ext hkEq
                subst hkEqFin
                exact (RowIsZero.not_isPivot (hzero := hBZero) (hp := hkB)).elim
              -- `i < k`: zero rows stay at bottom in echelon form, so row `k` in `B` is zero.
              · have hiLt' : iFin < k := by simpa [iFin] using hiLt
                have hkZero : RowIsZero B k :=
                  hB.echelon.zero_rows_bottom iFin k hiLt' hBZero
                exact (RowIsZero.not_isPivot (hzero := hkZero) (hp := hkB)).elim
        exact Or.inl ⟨hBZero, hCZero⟩
    | inr hPivotB =>
        -- `B` row `i` has pivot `p`: force `C` row `i` to be nonzero, hence also has a pivot.
        rcases hPivotB with ⟨p, hpB⟩
        have hCNonzero : ¬ RowIsZero C iFin := by
          intro hCZero
          -- Contradiction by transferring pivot column `p` from `B` into `C`.
          rcases pivot_exists_in_right (hBC := hBC) (hC := hC) hpB with ⟨k, hkC⟩
          rcases lt_trichotomy k.1 iNat with hkLt | hkEq | hiLt
          · have hkMatch : RowMatch (R := R) B C k := ih k.1 hkLt k.2
            cases hkMatch with
            | inl hZeroPair =>
                exact (RowIsZero.not_isPivot (hzero := hZeroPair.2) (hp := hkC)).elim
            | inr hPivotPair =>
                -- Same-column forcing + strict pivot increase yields contradiction.
                rcases hPivotPair with ⟨pk, hkB, hkC'⟩
                have hpk : pk = p := IsPivot.eq_of_left hkC' hkC
                have hkBp : IsPivot B k p := by simpa [hpk] using hkB
                have hkLt' : k < iFin := by simpa [iFin] using hkLt
                have hpLtp : p < p :=
                  hB.echelon.pivots_strictly_increasing k iFin p p hkLt' hkBp hpB
                exact (lt_irrefl _ hpLtp).elim
          -- `k = i`: impossible because row `i` of `C` was assumed zero.
          · have hkEqFin : k = iFin := Fin.ext hkEq
            subst hkEqFin
            exact (RowIsZero.not_isPivot (hzero := hCZero) (hp := hkC)).elim
          -- `i < k`: zero-row-bottom in `C` forbids a pivot at row `k`.
          · have hiLt' : iFin < k := by simpa [iFin] using hiLt
            have hkZero : RowIsZero C k :=
              hC.echelon.zero_rows_bottom iFin k hiLt' hCZero
            exact (RowIsZero.not_isPivot (hzero := hkZero) (hp := hkC)).elim
        -- Extract the pivot of row `i` in `C`.
        have hCPivot : ∃ q : Fin n, IsPivot C iFin q := by
          cases hCi : hC.echelon.row_zero_or_pivot iFin with
          | inl hZero =>
              exact (hCNonzero hZero).elim
          | inr hPivot =>
              exact hPivot
        rcases hCPivot with ⟨q, hqC⟩
        -- Show `p ≤ q` by contradiction.
        have hpLeQ : p ≤ q := by
          by_contra hNotLe
          have hqLtP : q < p := lt_of_not_ge hNotLe
          rcases pivot_exists_in_left (hBC := hBC) (hB := hB) hqC with ⟨k, hkBq⟩
          rcases lt_trichotomy k.1 iNat with hkLt | hkEq | hiLt
          · have hkMatch : RowMatch (R := R) B C k := ih k.1 hkLt k.2
            cases hkMatch with
            | inl hZeroPair =>
                exact (RowIsZero.not_isPivot (hzero := hZeroPair.1) (hp := hkBq)).elim
            | inr hPivotPair =>
                -- Again: row match at `k` + strict increase in `C` leads to `q < q`.
                rcases hPivotPair with ⟨qk, hkB, hkCk⟩
                have hqk : qk = q := IsPivot.eq_of_left hkB hkBq
                have hkCq : IsPivot C k q := by simpa [hqk] using hkCk
                have hkLt' : k < iFin := by simpa [iFin] using hkLt
                have hqLtq : q < q :=
                  hC.echelon.pivots_strictly_increasing k iFin q q hkLt' hkCq hqC
                exact (lt_irrefl _ hqLtq).elim
          -- `k = i` identifies pivot columns and contradicts `q < p`.
          · have hkEqFin : k = iFin := Fin.ext hkEq
            subst hkEqFin
            have hpEqQ : p = q := IsPivot.eq_of_left hpB hkBq
            exact (ne_of_lt hqLtP) hpEqQ.symm
          -- `i < k` gives `p < q`, contradicting `q < p`.
          · have hiLt' : iFin < k := by simpa [iFin] using hiLt
            have hpLtQ : p < q :=
              hB.echelon.pivots_strictly_increasing iFin k p q hiLt' hpB hkBq
            exact (lt_irrefl _ (hqLtP.trans hpLtQ)).elim
        -- Symmetric argument yields `q ≤ p`.
        have hqLeP : q ≤ p := by
          by_contra hNotLe
          have hpLtQ : p < q := lt_of_not_ge hNotLe
          rcases pivot_exists_in_right (hBC := hBC) (hC := hC) hpB with ⟨k, hkCp⟩
          rcases lt_trichotomy k.1 iNat with hkLt | hkEq | hiLt
          · have hkMatch : RowMatch (R := R) B C k := ih k.1 hkLt k.2
            cases hkMatch with
            | inl hZeroPair =>
                exact (RowIsZero.not_isPivot (hzero := hZeroPair.2) (hp := hkCp)).elim
            | inr hPivotPair =>
                -- Mirror contradiction on the `B` side.
                rcases hPivotPair with ⟨pk, hkBk, hkCk⟩
                have hpk : pk = p := IsPivot.eq_of_left hkCk hkCp
                have hkBp : IsPivot B k p := by simpa [hpk] using hkBk
                have hkLt' : k < iFin := by simpa [iFin] using hkLt
                have hpLtp : p < p :=
                  hB.echelon.pivots_strictly_increasing k iFin p p hkLt' hkBp hpB
                exact (lt_irrefl _ hpLtp).elim
          -- `k = i` identifies columns and contradicts `p < q`.
          · have hkEqFin : k = iFin := Fin.ext hkEq
            subst hkEqFin
            have hqEqP : q = p := IsPivot.eq_of_left hqC hkCp
            exact (ne_of_lt hpLtQ) hqEqP.symm
          -- `i < k` gives `q < p`, contradicting `p < q`.
          · have hiLt' : iFin < k := by simpa [iFin] using hiLt
            have hqLtP : q < p :=
              hC.echelon.pivots_strictly_increasing iFin k q p hiLt' hqC hkCp
            exact (lt_irrefl _ (hpLtQ.trans hqLtP)).elim
        -- Conclude matching pivot column at row `i`.
        have hpq : p = q := le_antisymm hpLeQ hqLeP
        exact Or.inr ⟨p, hpB, by simpa [hpq] using hqC⟩
  intro i
  simpa using hMatchNat i.1 i.2

/--
Semantic uniqueness under row-equivalence.

If `B` and `C` are reduced and row-equivalent, then they are entrywise equal.
The proof rewrites `B = U * C`, then uses row matching plus pivot-column
Kronecker behavior to collapse coefficients to `(if i = t then 1 else 0)`.
-/
private theorem reduced_unique_of_rowEquivalent {m n : Nat}
    {B C : Matrix (Fin m) (Fin n) R}
    (hBC : RowEquivalent B C)
    (hB : IsReducedEchelonForm (M := B))
    (hC : IsReducedEchelonForm (M := C)) :
    B = C := by
  rcases RowEquivalent.symm hBC with ⟨UUnit, hUraw⟩
  let U : Matrix (Fin m) (Fin m) R := (UUnit : Matrix (Fin m) (Fin m) R)
  have hU : B = U * C := by simpa [U] using hUraw
  have hMatch : ∀ i : Fin m, RowMatch (R := R) B C i :=
    reduced_rowMatch_of_rowEquivalent (hBC := hBC) (hB := hB) (hC := hC)
  -- Prove entrywise equality.
  ext i j
  calc
    B i j = ∑ t, U i t * C t j := by
      calc
        B i j = (U * C) i j := by simp [hU]
        _ = ∑ t, U i t * C t j := by simp [Matrix.mul_apply]
    -- Replace each coefficient `U i t` by unit-style `(if i = t then 1 else 0)`.
    _ = ∑ t, (if i = t then 1 else 0) * C t j := by
      refine Finset.sum_congr rfl ?_
      intro t _
      cases hMatch t with
      | inl hZeroPair =>
          -- When row `t` in `C` is zero, this summand is zero either way.
          simp [hZeroPair.2 j]
      | inr hPivotPair =>
          -- When row `t` has matching pivots, coefficient extraction + reducedness
          -- turns `U i t` into the Kronecker unit.
          rcases hPivotPair with ⟨p, hpBt, hpCt⟩
          have hCoeff : U i t = B i p :=
            (coeff_from_pivot_column (hC := hC) (U := U) (hBC := hU)
              (k := t) (i := i) (q := p) hpCt).symm
          have hUnit : B i p = if i = t then 1 else 0 :=
            reduced_pivot_col_unit hB hpBt
          simp [hCoeff, hUnit]
    -- The resulting sum is exactly row `i` of `C`.
    _ = C i j := by simp

/--
Core semantic uniqueness theorem.

Two matrices that are both reduced representatives of the same source `A`
must be equal.
-/
theorem IsReducedEchelonFormOf.unique {m n : Nat}
    [DecidableEq R]
    {A B B' : Matrix (Fin m) (Fin n) R}
    (hB : IsReducedEchelonFormOf A B)
    (hB' : IsReducedEchelonFormOf A B') :
    B = B' := by
  have hBB' : RowEquivalent B B' :=
    RowEquivalent.trans (RowEquivalent.symm hB.rowEquivalent) hB'.rowEquivalent
  exact reduced_unique_of_rowEquivalent (hBC := hBB') (hB := hB.reduced) (hC := hB'.reduced)

/--
Semantic-to-canonical corollary.

Any semantic representative `B` of `A` equals the canonical algorithm output.
-/
lemma IsReducedEchelonFormOf.canonical {m n : Nat}
    [DecidableEq R]
    {A B : Matrix (Fin m) (Fin n) R} (h : IsReducedEchelonFormOf (A := A) B) :
    B = (GaussianEliminationInternal.rawReducedRowEchelonForm A).1 := by
  exact IsReducedEchelonFormOf.unique h (reducedRowEchelonForm_isReducedEchelonFormOf (A := A))

/--
Semantic stage-2 specification of RREF uniqueness.

This statement is intentionally algorithm-independent: it quantifies over any
`B` and `B'` satisfying the semantic predicate `IsReducedEchelonFormOf A`.
-/
def RrefUniquenessSemanticGoal {m n : Nat}
    [DecidableEq R]
    (A : Matrix (Fin m) (Fin n) R) : Prop :=
  ∀ {B B' : Matrix (Fin m) (Fin n) R},
    IsReducedEchelonFormOf A B →
    IsReducedEchelonFormOf A B' →
    B = B'

/--
The semantic stage-2 specification holds, instantiated directly from
`IsReducedEchelonFormOf.unique`.
-/
theorem rrefUniquenessSemanticGoal_holds {m n : Nat}
    [DecidableEq R]
    (A : Matrix (Fin m) (Fin n) R) :
    RrefUniquenessSemanticGoal (A := A) := by
  intro B B' hB hB'
  exact IsReducedEchelonFormOf.unique hB hB'

end Matrix
