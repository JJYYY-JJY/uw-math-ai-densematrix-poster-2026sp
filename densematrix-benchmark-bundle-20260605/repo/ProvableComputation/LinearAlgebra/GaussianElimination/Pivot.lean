import ProvableComputation.LinearAlgebra.Echelon
import ProvableComputation.LinearAlgebra.GaussianElimination.Rref

/-!
# Shared proof lemmas for echelon / RREF routines

This file collects structural lemmas used by proofs around `checkPivot`,
`replace`, and `GaussianEliminationInternal.eliminateColCore`.
The focus is to expose stable invariants of the executable procedures in
`Rref.lean` as reusable theorem statements.
-/

open Matrix

namespace Matrix

variable {R : Type} [Field R] [DecidableEq R]
variable {m n : ℕ}

set_option linter.style.longLine false

/-- Matrix output of `GaussianEliminationInternal.eliminateColCore` when the step log starts as `[]` and `reduced = true`. -/
abbrev eliminateColM
    (M : Matrix (Fin m) (Fin n) R) (pivotRow : Fin m) (pivotCol : Fin n) :
    Matrix (Fin m) (Fin n) R :=
  (GaussianEliminationInternal.eliminateColCore M pivotRow pivotCol List.nil true).1

/-- Matrix component of `GaussianEliminationInternal.eliminateColLoop` for a fixed loop index and current step log. -/
abbrev eliminateColLoopMatrix
    (pivotRow : Fin m) (pivotCol : Fin n) (r : Nat)
    (cur : Matrix (Fin m) (Fin n) R) (steps : List (RowOp m R)) :
    Matrix (Fin m) (Fin n) R :=
  (GaussianEliminationInternal.eliminateColLoop pivotRow pivotCol r cur steps).1

private lemma eliminateColLoopAux_matrix_eq
    (pivotRow : Fin m) (pivotCol : Fin n) (pivotVal : R) (r : Nat)
    (cur : Matrix (Fin m) (Fin n) R) (steps : List (RowOp m R))
    (hpivot : cur pivotRow pivotCol = pivotVal) :
    (GaussianEliminationInternal.eliminateColLoopAux pivotRow pivotCol pivotVal r cur steps).1 =
      eliminateColLoopMatrix pivotRow pivotCol r cur steps := by
  simp [Matrix.eliminateColLoopMatrix, GaussianEliminationInternal.eliminateColLoop, hpivot]

/-! ## Elementary pivot facts -/

-- A row cannot have two distinct pivot columns.
omit [DecidableEq R] in
lemma IsPivot.eq_of_left {m n : Type*} [LinearOrder n]
    {M : Matrix m n R} {i : m} {p q : n} (hp : IsPivot M i p) (hq : IsPivot M i q) :
    p = q := by
  have hnot_lt_pq : ¬ p < q := fun hlt ↦ hp.1 (hq.2 p hlt)
  have hnot_lt_qp : ¬ q < p := fun hlt ↦ hq.1 (hp.2 q hlt)
  exact le_antisymm (le_of_not_gt hnot_lt_qp) (le_of_not_gt hnot_lt_pq)

-- A zero row cannot contain a pivot.
omit [DecidableEq R] in
lemma RowIsZero.not_isPivot {m n : Type*} [LinearOrder n]
    {M : Matrix m n R} {i : m} {p : n} (hzero : RowIsZero M i) (hp : IsPivot M i p) :
    False := hp.1 (hzero p)

/-! ## `checkPivot` search invariants -/

/--
If scanning column `col` from row `row` returns `none`, then every entry in
that column at rows `≥ row` is zero.
-/
private lemma scanRow_none_col_zero
    (M : Matrix (Fin m) (Fin n) R) (col row : Nat) (hcol : col < n)
    (h : checkPivot.scanCol.scanRow (M := M) col (hcol := hcol) row = none) :
    ∀ r : Fin m, row ≤ r.1 → M r ⟨col, hcol⟩ = 0 := by
  classical
  -- Recursion invariant: for any `row`, failure of `scanRow` forces all rows
  -- at/after `row` in column `col` to be zero.
  have hrec :
      ∀ k row, m - row = k →
        checkPivot.scanCol.scanRow (M := M) col (hcol := hcol) row = none →
        ∀ r : Fin m, row ≤ r.1 → M r ⟨col, hcol⟩ = 0 := by
    intro k
    induction k with
    | zero =>
      intro row hk h r hr
      -- Base case: `row ≥ m`, so there is no `r : Fin m` with `row ≤ r.1`.
      have hrow : m ≤ row := Nat.le_of_sub_eq_zero hk
      have : r.1 < row := lt_of_lt_of_le r.2 hrow
      exact (False.elim ((Nat.not_lt_of_ge hr) this))
    | succ k ih =>
      intro row hk h r hr
      -- Step case: unfold one iteration of `scanRow` at this concrete `row`.
      have hrow : row < m := by omega
      rw [checkPivot.scanCol.scanRow, dif_pos hrow] at h
      -- If current entry is nonzero, `scanRow` would return `some`, contradiction.
      by_cases hzero : M ⟨row, hrow⟩ ⟨col, hcol⟩ ≠ 0
      · simp [hzero] at h
      -- Otherwise recurse to `row + 1`; then transfer result back to any target `r`.
      · have hnext : checkPivot.scanCol.scanRow (M := M) col (hcol := hcol) (row + 1) = none := by
          simp only [hzero] at h
          exact h
        have hk' : m - (row + 1) = k :=
          by omega
        -- Split target row `r` into exact-hit (`r = row`) or strict-after (`r > row`).
        by_cases hreq : r.1 = row
        · have hr' : r = ⟨row, hrow⟩ := by
            ext
            simp [hreq]
          subst hr'
          -- At the hit row, zero follows from the negated nonzero branch.
          have hzero' : M ⟨row, hrow⟩ ⟨col, hcol⟩ = 0 := by
            by_contra hne
            exact hzero hne
          exact hzero'
        · have hrlt : row < r.1 := lt_of_le_of_ne hr (Ne.symm hreq)
          have hr' : row + 1 ≤ r.1 := Nat.succ_le_of_lt hrlt
          exact ih (row + 1) hk' hnext r hr'
  exact hrec (m - row) row rfl h

/--
If `checkPivot M row col = none`, then all entries in the submatrix with
rows `≥ row` and columns `≥ col` are zero.
-/
lemma checkPivot_none_zero
    (M : Matrix (Fin m) (Fin n) R) (row col : Nat)
    (h : checkPivot M row col = none) :
    ∀ j : Fin n, col ≤ j.1 → ∀ r : Fin m, row ≤ r.1 → M r j = 0 := by
  classical
  -- Recursion invariant over remaining columns.
  have hrec :
      ∀ k row col, n - col = k →
        checkPivot M row col = none →
        ∀ j : Fin n, col ≤ j.1 → ∀ r : Fin m, row ≤ r.1 → M r j = 0 := by
    intro k
    induction k with
    | zero =>
      intro row col hk hnone j hj r hr
      -- Base case: `col ≥ n`; impossible to pick `j : Fin n` with `col ≤ j.1`.
      have hcol : n ≤ col := Nat.le_of_sub_eq_zero hk
      have hlt : j.1 < col := lt_of_lt_of_le j.2 hcol
      exact by omega
    | succ k ih =>
      intro row col hk hnone j hj r hr
      -- Step case: inspect the current column and then recurse if needed.
      rw [checkPivot, checkPivot.scanCol] at hnone
      by_cases hcol : col < n
      · simp only [hcol] at hnone
        -- `checkPivot = none` implies this column scan cannot return `some`.
        cases hscan : checkPivot.scanCol.scanRow (M := M) col (hcol := hcol) row with
        | some p =>
            simp [hscan] at hnone
        | none =>
            -- So the whole column segment is zero from `row` downward.
            have hcol_zero : ∀ r : Fin m, row ≤ r.1 → M r ⟨col, hcol⟩ = 0 :=
              scanRow_none_col_zero (M := M) col row hcol hscan
            have hnext : checkPivot M row (col + 1) = none := by
              simp only [hscan] at hnone
              exact hnone
            -- For target column `j`, either `j = col` (done) or `j > col` (recurse).
            have hj' := lt_or_eq_of_le hj
            cases hj' with
            | inl hjlt =>
                have hk' : n - (col + 1) = k :=
                  by omega
                have hj_ge : col + 1 ≤ j.1 := Nat.succ_le_of_lt hjlt
                exact ih row (col + 1) hk' hnext j hj_ge r hr
            | inr hjeq =>
                subst hjeq
                exact hcol_zero r hr
      · have hcol' : n ≤ col := Nat.le_of_not_gt hcol
        -- Contradict `n - col = succ k` once `col ≥ n`.
        have h' : n - col = 0 := Nat.sub_eq_zero_iff_le.mpr hcol'
        rw [hk] at h'
        exact (False.elim ((Nat.ne_of_lt (Nat.succ_pos k)) h'.symm))
  exact hrec (n - col) row col rfl h

/--
If `scanRow` finds a pivot candidate, its row index is at least the starting
row used for the scan.
-/
private lemma scanRow_some_row_ge
    (M : Matrix (Fin m) (Fin n) R) (col row : Nat) (hcol : col < n)
    {pr : Fin m} {pc : Fin n}
    (h : checkPivot.scanCol.scanRow (M := M) col (hcol := hcol) row = some (pr, pc)) :
    row ≤ pr.1 := by
  classical
  -- Recursion invariant: successful scan from `row` always returns `pr.1 ≥ row`.
  have hrec :
      ∀ k row, m - row = k →
        checkPivot.scanCol.scanRow (M := M) col (hcol := hcol) row = some (pr, pc) →
          row ≤ pr.1 := by
    intro k
    induction k with
    | zero =>
      intro row hk h
      have hrow : m ≤ row := Nat.le_of_sub_eq_zero hk
      -- Base case: if `row ≥ m`, `scanRow` must be `none`, contradiction.
      rw [checkPivot.scanCol.scanRow, dif_neg (not_lt_of_ge hrow)] at h
      cases h
    | succ k ih =>
      intro row hk h
      -- Step case: unfold `scanRow row` and inspect the current entry.
      have hrow : row < m := by omega
      rw [checkPivot.scanCol.scanRow, dif_pos hrow] at h
      by_cases hzero : M ⟨row, hrow⟩ ⟨col, hcol⟩ ≠ 0
      · simp only [ne_eq, hzero, not_false_eq_true, ↓reduceIte, Option.some.injEq,
        Prod.mk.injEq] at h
        -- Successful immediate hit: returned row is exactly `row`.
        rcases h with ⟨hpr, _⟩
        subst hpr
        exact Nat.le_refl _
      · have hnext :
            checkPivot.scanCol.scanRow (M := M) col (hcol := hcol) (row + 1) = some (pr, pc) := by
          simp only [hzero] at h
          exact h
        -- No hit at `row`; recurse from `row + 1` and weaken.
        have hk' : m - (row + 1) = k :=
          by omega
        have hge : row + 1 ≤ pr.1 := ih (row + 1) hk' hnext
        exact Nat.le_trans (Nat.le_succ _) hge
  exact hrec (m - row) row rfl h

/--
Any successful `scanRow` call in column `col` returns that same column index.
-/
private lemma scanRow_some_col_eq
    (M : Matrix (Fin m) (Fin n) R) (col row : Nat) (hcol : col < n)
    {pr : Fin m} {pc : Fin n}
    (h : checkPivot.scanCol.scanRow (M := M) col (hcol := hcol) row = some (pr, pc)) :
    pc = ⟨col, hcol⟩ := by
  classical
  -- Recursion invariant: a successful result keeps column component fixed.
  have hrec :
      ∀ k row, m - row = k →
        checkPivot.scanCol.scanRow (M := M) col (hcol := hcol) row = some (pr, pc) →
          pc = ⟨col, hcol⟩ := by
    intro k
    induction k with
    | zero =>
      intro row hk h
      have hrow : m ≤ row := Nat.le_of_sub_eq_zero hk
      -- Base case contradiction: out-of-range start cannot produce `some`.
      rw [checkPivot.scanCol.scanRow, dif_neg (not_lt_of_ge hrow)] at h
      cases h
    | succ k ih =>
      intro row hk h
      -- Step case: unfold one scan step in column `col`.
      have hrow : row < m := by omega
      rw [checkPivot.scanCol.scanRow, dif_pos hrow] at h
      by_cases hzero : M ⟨row, hrow⟩ ⟨col, hcol⟩ ≠ 0
      · simp only [ne_eq, hzero, not_false_eq_true, ↓reduceIte, Option.some.injEq,
        Prod.mk.injEq] at h
        -- Immediate success exposes the exact column equality.
        rcases h with ⟨_, hpc⟩
        exact hpc.symm
      · have hnext :
            checkPivot.scanCol.scanRow (M := M) col (hcol := hcol) (row + 1) = some (pr, pc) := by
          simp only [hzero] at h
          exact h
        -- Otherwise move to `row + 1` and reuse the induction hypothesis.
        have hk' : m - (row + 1) = k :=
          by omega
        exact ih (row + 1) hk' hnext
  exact hrec (m - row) row rfl h

/--
If `checkPivot` returns `some (pr, pc)`, the pivot row `pr` is not above
the starting search row.
-/
lemma checkPivot_some_row_ge
    (M : Matrix (Fin m) (Fin n) R) (row col : Nat)
    {pr : Fin m} {pc : Fin n}
    (h : checkPivot M row col = some (pr, pc)) :
    row ≤ pr.1 := by
  classical
  -- Recursion invariant over columns for successful `checkPivot`.
  have hrec :
      ∀ k row col, n - col = k →
        checkPivot M row col = some (pr, pc) → row ≤ pr.1 := by
    intro k
    induction k with
    | zero =>
      intro row col hk h
      have hcol : n ≤ col := Nat.le_of_sub_eq_zero hk
      -- Base case contradiction: no candidate column exists when `col ≥ n`.
      rw [checkPivot, checkPivot.scanCol, dif_neg (not_lt_of_ge hcol)] at h
      cases h
    | succ k ih =>
      intro row col hk h
      -- Step case: inspect current column then recurse to `col + 1` if needed.
      rw [checkPivot, checkPivot.scanCol] at h
      by_cases hcol : col < n
      · simp only [hcol] at h
        cases hscan : checkPivot.scanCol.scanRow (M := M) col (hcol := hcol) row with
        | some p =>
            -- Pivot found in this column; delegate row bound to `scanRow` lemma.
            have h' :
            checkPivot.scanCol.scanRow (M := M) col (hcol := hcol) row = some (pr, pc) := by
              simpa [hscan] using h
            have hrowge := scanRow_some_row_ge (M := M) col row hcol h'
            exact hrowge
        | none =>
            -- No pivot in this column; recurse to the next column.
            have hnext : checkPivot M row (col + 1) = some (pr, pc) := by
              simpa [hscan] using h
            have hk' : n - (col + 1) = k :=
              by omega
            exact ih row (col + 1) hk' hnext
      · simp [hcol] at h
  exact hrec (n - col) row col rfl h

/--
If `checkPivot M row col = some (pr, pc)`, then every earlier column `j < pc`
with `j ≥ col` is zero below `row`.
-/
lemma checkPivot_some_minimal
    (M : Matrix (Fin m) (Fin n) R) (row col : Nat)
    {pr : Fin m} {pc : Fin n}
    (h : checkPivot M row col = some (pr, pc)) :
    ∀ j : Fin n, col ≤ j.1 → j < pc → ∀ r : Fin m, row ≤ r.1 → M r j = 0 := by
  classical
  -- Recursion invariant over columns for the minimal-column property.
  have hrec :
      ∀ k row col, n - col = k →
        checkPivot M row col = some (pr, pc) →
        ∀ j : Fin n, col ≤ j.1 → j < pc → ∀ r : Fin m, row ≤ r.1 → M r j = 0 := by
    intro k
    induction k with
    | zero =>
      intro row col hk h j hj hlt r hr
      -- Base case: impossible ordering once `col ≥ n`.
      have hcol : n ≤ col := Nat.le_of_sub_eq_zero hk
      have hlt' : j.1 < col := lt_of_lt_of_le j.2 hcol
      exact by omega
    | succ k ih =>
      intro row col hk h j hj hlt r hr
      -- Step case: analyze current column `col`.
      by_cases hcol : col < n
      · dsimp [checkPivot] at h
        rw [checkPivot.scanCol] at h
        simp only [hcol] at h
        cases hscan : checkPivot.scanCol.scanRow (M := M) col (hcol := hcol) row with
        | some p =>
            -- Pivot appears in the current column, so `pc = col`.
            have h' : some p = some (pr, pc) := by simpa [hscan] using h
            cases h'
            have hpc : pc = ⟨col, hcol⟩ :=
              scanRow_some_col_eq (M := M) col row hcol hscan
            -- Then `j < pc` forces `j < col`, contradicting `col ≤ j`.
            have hlt' : j.1 < col := by simpa [hpc] using hlt
            exact by omega
        | none =>
            -- Current column is all zero from `row` down.
            have hcol_zero : ∀ r : Fin m, row ≤ r.1 → M r ⟨col, hcol⟩ = 0 :=
              scanRow_none_col_zero (M := M) col row hcol hscan
            have hnext : checkPivot M row (col + 1) = some (pr, pc) := by
              simpa [checkPivot, hscan] using h
            -- Either `j = col` (use `hcol_zero`) or `j > col` (recurse).
            have hj' := lt_or_eq_of_le hj
            cases hj' with
            | inl hjlt =>
                have hk' : n - (col + 1) = k :=
                  by omega
                have hj_ge : col + 1 ≤ j.1 := Nat.succ_le_of_lt hjlt
                exact ih row (col + 1) hk' hnext j hj_ge hlt r hr
            | inr hjeq =>
              subst hjeq
              exact hcol_zero r hr
      · have hcol' : n ≤ col := Nat.le_of_not_gt hcol
        -- Contradict `n - col = succ k` once outside valid column range.
        have h' : n - col = 0 := Nat.sub_eq_zero_iff_le.mpr hcol'
        rw [hk] at h'
        exact (False.elim ((Nat.ne_of_lt (Nat.succ_pos k)) h'.symm))
  exact hrec (n - col) row col rfl h

/--
Internal recursive witness that the pivot returned by `checkPivot` is nonzero.
-/
private def pivot_ne_zero (pivotRow : Fin m) (pivotCol : Fin n) (M : Matrix (Fin m) (Fin n) R)
    (r c : Nat) (h : checkPivot M r c = some (pivotRow, pivotCol))
    : M pivotRow pivotCol ≠ 0 := by
  -- Unfold `checkPivot` one layer and follow the branch that produced `some`.
  rw [checkPivot, checkPivot.scanCol] at h
  split_ifs at h with h1
  · split at h
    · rename_i x p heq
      -- We are in the branch where `scanRow` reported `some`.
      rw [checkPivot.scanCol.scanRow] at heq
      split_ifs at heq with h2 h3
      · rw [h] at heq
        injection heq with heq'
        cases heq'
        -- Here `h3` is exactly the nonzero proof of the returned pivot entry.
        exact h3
      · have h' : checkPivot M (r + 1) c = some (pivotRow, pivotCol) := by
          rw [checkPivot, checkPivot.scanCol]
          simp_all only [Option.some.injEq, ne_eq, Decidable.not_not, ↓reduceDIte]
        -- Current row entry is zero; continue scanning the same column downward.
        exact pivot_ne_zero pivotRow pivotCol M (r + 1) c h'
    · rename_i x heq
      -- Current column failed; recurse to the next column.
      exact pivot_ne_zero pivotRow pivotCol M r (c + 1) h

/-- Any pivot pair returned by `checkPivot` points to a nonzero matrix entry. -/
lemma checkPivot_some_nonzero
    (M : Matrix (Fin m) (Fin n) R) (row col : Nat)
    {pr : Fin m} {pc : Fin n}
    (h : checkPivot M row col = some (pr, pc)) :
    M pr pc ≠ 0 := pivot_ne_zero pr pc M row col h

/-! ## `replace` and `GaussianEliminationInternal.eliminateColCore` behavior lemmas -/

-- If `r ≠ toReplace`, then `replace` does not modify entry `(r,j)`.
omit [DecidableEq R] in
private lemma replace_apply_of_ne
    (M : Matrix (Fin m) (Fin n) R) (use toReplace : Fin m) (k : R)
    (r : Fin m) (j : Fin n) (huse : use ≠ toReplace) (hrow : r ≠ toReplace) :
    replace M use toReplace k r j = M r j := by
  simp [replace, huse, hrow, of_apply]

-- On the target row, `replace` realizes the affine row update formula.
omit [DecidableEq R] in
private lemma replace_apply_eq
    (M : Matrix (Fin m) (Fin n) R) (use toReplace : Fin m) (k : R)
    (huse : use ≠ toReplace) (j : Fin n) :
    replace M use toReplace k toReplace j = M toReplace j + k * M use j := by
  simp [replace, huse, of_apply]

-- If the pivot entry is normalized to `1`, the elimination replacement zeros it.
omit [DecidableEq R] in
private lemma replace_pivot_col_zero_of_ne
    (M : Matrix (Fin m) (Fin n) R) (pivotRow toReplace : Fin m) (pivotCol : Fin n)
    (huse : pivotRow ≠ toReplace) (hne : M pivotRow pivotCol ≠ 0) :
    replace M pivotRow toReplace (-M toReplace pivotCol / M pivotRow pivotCol) toReplace pivotCol = 0 := by
  rw [replace_apply_eq (M := M) (use := pivotRow) (toReplace := toReplace)
    (k := -M toReplace pivotCol / M pivotRow pivotCol) (huse := huse) (j := pivotCol)]
  rw [neg_div, div_eq_mul_inv]
  have hcancel : (M pivotRow pivotCol)⁻¹ * M pivotRow pivotCol = 1 := inv_mul_cancel₀ hne
  calc
    M toReplace pivotCol + -(M toReplace pivotCol * (M pivotRow pivotCol)⁻¹) * M pivotRow pivotCol
        = M toReplace pivotCol + -(M toReplace pivotCol * ((M pivotRow pivotCol)⁻¹ * M pivotRow pivotCol)) := by
            ring_nf
    _ = M toReplace pivotCol + -(M toReplace pivotCol * 1) := by rw [hcancel]
    _ = 0 := by ring

omit [DecidableEq R] in
private lemma replace_pivot_col_zero
    (M : Matrix (Fin m) (Fin n) R) (pivotRow toReplace : Fin m) (pivotCol : Fin n)
    (huse : pivotRow ≠ toReplace) (h1 : M pivotRow pivotCol = 1) :
    replace M pivotRow toReplace (-M toReplace pivotCol / M pivotRow pivotCol) toReplace pivotCol = 0 := by
  exact replace_pivot_col_zero_of_ne (M := M) (pivotRow := pivotRow)
    (toReplace := toReplace) (pivotCol := pivotCol) huse (by simp [h1])

/--
The matrix output of `GaussianEliminationInternal.eliminateColLoop` is independent of the current `steps`
list; `steps` only records operations.
-/
private theorem eliminateCol_go_matrix_irrel
    (pivotRow : Fin m) (pivotCol : Fin n) (r : Nat)
    (cur : Matrix (Fin m) (Fin n) R) (steps₁ steps₂ : List (RowOp m R)) :
    eliminateColLoopMatrix pivotRow pivotCol r cur steps₁ =
      eliminateColLoopMatrix pivotRow pivotCol r cur steps₂ := by
  -- Recursion invariant over remaining rows.
  have hrec :
      ∀ k (r : Nat) (cur : Matrix (Fin m) (Fin n) R) (steps₁ steps₂ : List (RowOp m R)),
        m - r = k →
          eliminateColLoopMatrix pivotRow pivotCol r cur steps₁ =
            eliminateColLoopMatrix pivotRow pivotCol r cur steps₂ := by
    intro k
    induction k with
    | zero =>
      intro r cur steps₁ steps₂ hk
      -- Base case: loop terminates once `r ≥ m`.
      have hr : m ≤ r := Nat.le_of_sub_eq_zero hk
      rw [Matrix.eliminateColLoopMatrix, GaussianEliminationInternal.eliminateColLoop, GaussianEliminationInternal.eliminateColLoopAux, dif_neg (not_lt_of_ge hr)]
      conv_rhs => rw [Matrix.eliminateColLoopMatrix, GaussianEliminationInternal.eliminateColLoop, GaussianEliminationInternal.eliminateColLoopAux, dif_neg (not_lt_of_ge hr)]
    | succ k ih =>
      intro r cur steps₁ steps₂ hk
      -- Step case: unfold one iteration and mirror branch choices on both sides.
      have hr : r < m := by omega
      have hk' : m - (r + 1) = k :=
        by omega
      rw [Matrix.eliminateColLoopMatrix, GaussianEliminationInternal.eliminateColLoop, GaussianEliminationInternal.eliminateColLoopAux, dif_pos hr]
      conv_rhs => rw [Matrix.eliminateColLoopMatrix, GaussianEliminationInternal.eliminateColLoop, GaussianEliminationInternal.eliminateColLoopAux, dif_pos hr]
      by_cases hEq : (⟨r, hr⟩ : Fin m) = pivotRow
      · simpa [hEq, List.concat_eq_append, dite_eq_ite] using
          ih (r + 1) cur steps₁ steps₂ hk'
      · by_cases hzero : cur ⟨r, hr⟩ pivotCol = 0
        -- When coefficient is already zero, both executions recurse on same `cur`.
        · simpa [hEq, hzero, List.concat_eq_append, dite_eq_ite] using
            ih (r + 1) cur steps₁ steps₂ hk'
        -- When replacement happens, both sides recurse on the same updated matrix.
        · let cur' := replace cur pivotRow ⟨r, hr⟩ (-cur ⟨r, hr⟩ pivotCol / cur pivotRow pivotCol)
          let steps1' := steps₁ ++ [RowOp.replace pivotRow ⟨r, hr⟩ (-cur ⟨r, hr⟩ pivotCol / cur pivotRow pivotCol)]
          let steps2' := steps₂ ++ [RowOp.replace pivotRow ⟨r, hr⟩ (-cur ⟨r, hr⟩ pivotCol / cur pivotRow pivotCol)]
          have huse : pivotRow ≠ (⟨r, hr⟩ : Fin m) := by
            intro hpr
            exact hEq hpr.symm
          have hpivot' : cur' pivotRow pivotCol = cur pivotRow pivotCol := by
            simpa [cur'] using
              replace_apply_of_ne
                (M := cur)
                (use := pivotRow)
                (toReplace := ⟨r, hr⟩)
                (k := -cur ⟨r, hr⟩ pivotCol / cur pivotRow pivotCol)
                (r := pivotRow) (j := pivotCol) (huse := huse) (hrow := huse)
          have hrec' := ih (r + 1) cur' steps1' steps2' hk'
          have hgo1 :
              (GaussianEliminationInternal.eliminateColLoopAux pivotRow pivotCol (cur pivotRow pivotCol) (r + 1) cur' steps1').1 =
                eliminateColLoopMatrix pivotRow pivotCol (r + 1) cur' steps1' := by
            simpa [steps1'] using
              eliminateColLoopAux_matrix_eq
                (pivotRow := pivotRow) (pivotCol := pivotCol)
                (pivotVal := cur pivotRow pivotCol) (r := r + 1) (cur := cur') (steps := steps1')
                hpivot'
          have hgo2 :
              (GaussianEliminationInternal.eliminateColLoopAux pivotRow pivotCol (cur pivotRow pivotCol) (r + 1) cur' steps2').1 =
                eliminateColLoopMatrix pivotRow pivotCol (r + 1) cur' steps2' := by
            simpa [steps2'] using
              eliminateColLoopAux_matrix_eq
                (pivotRow := pivotRow) (pivotCol := pivotCol)
                (pivotVal := cur pivotRow pivotCol) (r := r + 1) (cur := cur') (steps := steps2')
                hpivot'
          have hrec'' :
              (GaussianEliminationInternal.eliminateColLoopAux pivotRow pivotCol (cur pivotRow pivotCol) (r + 1) cur' steps1').1 =
                (GaussianEliminationInternal.eliminateColLoopAux pivotRow pivotCol (cur pivotRow pivotCol) (r + 1) cur' steps2').1 := by
            calc
              (GaussianEliminationInternal.eliminateColLoopAux pivotRow pivotCol (cur pivotRow pivotCol) (r + 1) cur' steps1').1
                  = eliminateColLoopMatrix pivotRow pivotCol (r + 1) cur' steps1' := hgo1
              _ = eliminateColLoopMatrix pivotRow pivotCol (r + 1) cur' steps2' := hrec'
              _ = (GaussianEliminationInternal.eliminateColLoopAux pivotRow pivotCol (cur pivotRow pivotCol) (r + 1) cur' steps2').1 := hgo2.symm
          simpa [cur', steps1', steps2', hEq, hzero, List.concat_eq_append, dite_eq_ite] using hrec''
  exact hrec (m - r) r cur steps₁ steps₂ rfl

/-- Specialization of `eliminateCol_go_matrix_irrel` to the top-level `GaussianEliminationInternal.eliminateColCore`. -/
lemma eliminateCol_matrix_irrel
    (M : Matrix (Fin m) (Fin n) R) (pivotRow : Fin m) (pivotCol : Fin n)
    (steps : List (RowOp m R)) :
    (GaussianEliminationInternal.eliminateColCore M pivotRow pivotCol steps true).1 = eliminateColM M pivotRow pivotCol := by
  simpa [eliminateColM, GaussianEliminationInternal.eliminateColCore] using
    eliminateCol_go_matrix_irrel pivotRow pivotCol 0 M steps List.nil

lemma eliminateCol_matrix_irrel_false
    (M : Matrix (Fin m) (Fin n) R) (pivotRow : Fin m) (pivotCol : Fin n)
    (steps : List (RowOp m R)) :
    (GaussianEliminationInternal.eliminateColCore M pivotRow pivotCol steps false).1 =
      (GaussianEliminationInternal.eliminateColCore M pivotRow pivotCol List.nil false).1 := by
  simpa [GaussianEliminationInternal.eliminateColCore] using
    eliminateCol_go_matrix_irrel pivotRow pivotCol pivotRow.1 M steps List.nil

/--
If column `j` of `pivotRow` is zero in `cur`, then `GaussianEliminationInternal.eliminateColLoop` preserves
column `j` for every row.
-/
lemma eliminateCol_go_preserves_col
    (cur : Matrix (Fin m) (Fin n) R) (pivotRow : Fin m) (pivotCol : Fin n)
    (r : Nat) (steps : List (RowOp m R)) (j : Fin n)
    (hzero : cur pivotRow j = 0) :
    ∀ i : Fin m, (eliminateColLoopMatrix pivotRow pivotCol r cur steps) i j = cur i j := by
  classical
  -- Recursion invariant over remaining rows for fixed comparison column `j`.
  have hrec :
      ∀ k (r : Nat) (cur : Matrix (Fin m) (Fin n) R) (steps : List (RowOp m R)), m - r = k →
        cur pivotRow j = 0 →
        ∀ i : Fin m, (eliminateColLoopMatrix pivotRow pivotCol r cur steps) i j = cur i j := by
    intro k
    induction k with
    | zero =>
      intro r cur steps hk hzero i
      -- Base case: loop ended.
      have hr : m ≤ r := Nat.le_of_sub_eq_zero hk
      rw [Matrix.eliminateColLoopMatrix, GaussianEliminationInternal.eliminateColLoop, GaussianEliminationInternal.eliminateColLoopAux, dif_neg (not_lt_of_ge hr)]
    | succ k ih =>
      intro r cur steps hk hzero i
      -- Step case: inspect row `r`.
      have hr : r < m := by omega
      rw [Matrix.eliminateColLoopMatrix, GaussianEliminationInternal.eliminateColLoop, GaussianEliminationInternal.eliminateColLoopAux, dif_pos hr]
      by_cases hEq : (⟨r, hr⟩ : Fin m) = pivotRow
      -- If current row is the pivot row, `GaussianEliminationInternal.eliminateColLoop` skips it.
      · simp only [hEq]
        have hk' : m - (r + 1) = k :=
          by omega
        exact ih (r + 1) cur steps hk' hzero i
      · by_cases hcoeff : cur ⟨r, hr⟩ pivotCol ≠ 0
        · -- Nonzero coefficient: a replacement is performed on row `r`.
          simp only [hEq, ↓reduceDIte, ne_eq, hcoeff, not_false_eq_true, ↓reduceIte]
          have hk' : m - (r + 1) = k :=
            by omega
          let i0 : Fin m := ⟨r, hr⟩
          let cur' := replace cur pivotRow i0 (-cur i0 pivotCol / cur pivotRow pivotCol)
          -- Show pivot-row value in column `j` stays zero after replacement.
          have huse : pivotRow ≠ i0 := by
            intro hpr
            exact hEq hpr.symm
          have hzero' : cur' pivotRow j = 0 := by
            have h :=
              replace_apply_of_ne
              (M := cur)
              (use := pivotRow)
              (toReplace := i0)
              (k := -cur i0 pivotCol / cur pivotRow pivotCol)
              (r := pivotRow)
              (j := j)
              (huse := huse)
              (hrow := huse)
            have h' : cur' pivotRow j = cur pivotRow j := by
              simpa [cur'] using h
            simpa [h'] using hzero
          have hpivot' : cur' pivotRow pivotCol = cur pivotRow pivotCol := by
            simpa [cur'] using
              replace_apply_of_ne
                (M := cur)
                (use := pivotRow)
                (toReplace := i0)
                (k := -cur i0 pivotCol / cur pivotRow pivotCol)
                (r := pivotRow) (j := pivotCol) (huse := huse) (hrow := huse)
          -- Apply induction to the recursive call.
          let steps' := List.concat steps (.replace pivotRow i0 (-cur i0 pivotCol / cur pivotRow pivotCol))
          have hih := ih (r + 1) cur' steps' hk' hzero' i
          have hgo :
              (GaussianEliminationInternal.eliminateColLoopAux pivotRow pivotCol (cur pivotRow pivotCol) (r + 1) cur' steps').1 =
                eliminateColLoopMatrix pivotRow pivotCol (r + 1) cur' steps' := by
            simpa [steps'] using
              eliminateColLoopAux_matrix_eq
                (pivotRow := pivotRow) (pivotCol := pivotCol)
                (pivotVal := cur pivotRow pivotCol) (r := r + 1) (cur := cur') (steps := steps')
                hpivot'
          have hih' :
              (GaussianEliminationInternal.eliminateColLoopAux pivotRow pivotCol (cur pivotRow pivotCol) (r + 1) cur' steps').1 i j =
                cur' i j := by
            calc
              (GaussianEliminationInternal.eliminateColLoopAux pivotRow pivotCol (cur pivotRow pivotCol) (r + 1) cur' steps').1 i j
                  = eliminateColLoopMatrix pivotRow pivotCol (r + 1) cur' steps' i j := by
                      simpa using congrArg (fun M => M i j) hgo
              _ = cur' i j := hih
          -- Relate `cur' i j` back to `cur i j`.
          have hcur' : cur' i j = cur i j := by
            by_cases hi : i = i0
            · subst hi
              have h := replace_apply_eq (M := cur) (use := pivotRow) (toReplace := i0)
                (k := -cur i0 pivotCol / cur pivotRow pivotCol) (huse := huse) (j := j)
              -- In the replaced row, added multiple vanishes since `cur pivotRow j = 0`.
              simpa [cur', hzero, mul_zero, add_zero] using h
            -- Any non-replaced row is untouched.
            · simpa [cur'] using
                replace_apply_of_ne
                (M := cur)
                (use := pivotRow)
                  (toReplace := i0)
                  (k := -cur i0 pivotCol / cur pivotRow pivotCol)
                  (r := i) (j := j) (huse := huse) (hrow := hi)
          calc
            (GaussianEliminationInternal.eliminateColLoopAux pivotRow pivotCol (cur pivotRow pivotCol) (r + 1) cur' steps').1 i j =
                cur' i j := hih'
            _ = cur i j := hcur'
        -- Zero coefficient: no row update; recurse directly.
        · simp (config := { failIfUnchanged := false }) only [hEq, ↓reduceDIte, hcoeff, ↓reduceIte]
          have hk' : m - (r + 1) = k :=
            by omega
          exact ih (r + 1) cur steps hk' hzero i
  exact hrec (m - r) r cur steps rfl hzero

/--
`GaussianEliminationInternal.eliminateColLoop` never changes the pivot row, regardless of the current
iterator position or step log.
-/
lemma eliminateCol_go_pivotRow
    (cur : Matrix (Fin m) (Fin n) R) (pivotRow : Fin m) (pivotCol : Fin n)
    (steps : List (RowOp m R)) :
    ∀ r j, (eliminateColLoopMatrix pivotRow pivotCol r cur steps) pivotRow j = cur pivotRow j := by
  classical
  -- Recursion invariant over remaining rows, with row value fixed to `pivotRow`.
  have hrec :
      ∀ k (r : Nat) (cur : Matrix (Fin m) (Fin n) R) (steps : List (RowOp m R)), m - r = k →
        ∀ j, (eliminateColLoopMatrix pivotRow pivotCol r cur steps) pivotRow j = cur pivotRow j := by
    intro k
    induction k with
    | zero =>
      intro r cur steps hk j
      -- Base case: recursion ended.
      have hr : m ≤ r := Nat.le_of_sub_eq_zero hk
      rw [Matrix.eliminateColLoopMatrix, GaussianEliminationInternal.eliminateColLoop, GaussianEliminationInternal.eliminateColLoopAux, dif_neg (not_lt_of_ge hr)]
    | succ k ih =>
      intro r cur steps hk j
      -- Step case: inspect behavior at row `r`.
      have hr : r < m := by omega
      let i0 : Fin m := ⟨r, hr⟩
      by_cases hEq : i0 = pivotRow
      · have hk' : m - (r + 1) = k :=
          by omega
        -- If `i0` is the pivot row, the algorithm skips replacement.
        rw [Matrix.eliminateColLoopMatrix, GaussianEliminationInternal.eliminateColLoop, GaussianEliminationInternal.eliminateColLoopAux, dif_pos hr]
        simp only [i0, hEq]
        exact ih (r + 1) cur steps hk' j
      · by_cases hcoeff : cur i0 pivotCol ≠ 0
        -- Replacement branch: prove pivot row value is unchanged by `replace`.
        · have hk' : m - (r + 1) = k :=
            by omega
          let cur' := replace cur pivotRow i0 (-cur i0 pivotCol / cur pivotRow pivotCol)
          have hpivot' : cur' pivotRow pivotCol = cur pivotRow pivotCol := by
            have huse : pivotRow ≠ i0 := by
              intro hpr
              exact hEq hpr.symm
            simpa [cur'] using
              replace_apply_of_ne
                (M := cur)
                (use := pivotRow)
                (toReplace := i0)
                (k := -cur i0 pivotCol / cur pivotRow pivotCol)
                (r := pivotRow) (j := pivotCol) (huse := huse) (hrow := huse)
          have hpr : cur' pivotRow j = cur pivotRow j := by
            have huse : pivotRow ≠ i0 := by
              intro hpr
              exact hEq hpr.symm
            have h :=
              replace_apply_of_ne
              (M := cur)
              (use := pivotRow)
              (toReplace := i0)
              (k := -cur i0 pivotCol / cur pivotRow pivotCol)
              (r := pivotRow)
              (j := j)
                  (huse := huse)
                  (hrow := huse)
            simpa [cur'] using h
          -- Recurse and stitch equalities.
          let steps' := List.concat steps (.replace pivotRow i0 (-cur i0 pivotCol / cur pivotRow pivotCol))
          have hih := ih (r + 1) cur' steps' hk' j
          have hgo :
              (GaussianEliminationInternal.eliminateColLoopAux pivotRow pivotCol (cur pivotRow pivotCol) (r + 1) cur' steps').1 =
                eliminateColLoopMatrix pivotRow pivotCol (r + 1) cur' steps' := by
            simpa [steps'] using
              eliminateColLoopAux_matrix_eq
                (pivotRow := pivotRow) (pivotCol := pivotCol)
                (pivotVal := cur pivotRow pivotCol) (r := r + 1) (cur := cur') (steps := steps')
                hpivot'
          have hstep :
              eliminateColLoopMatrix pivotRow pivotCol r cur steps pivotRow j =
                eliminateColLoopMatrix pivotRow pivotCol (r + 1) cur'
                  (List.concat steps (.replace pivotRow i0 (-cur i0 pivotCol / cur pivotRow pivotCol))) pivotRow j := by
            rw [Matrix.eliminateColLoopMatrix, GaussianEliminationInternal.eliminateColLoop, GaussianEliminationInternal.eliminateColLoopAux, dif_pos hr]
            simpa [i0, hEq, hcoeff, cur', steps'] using congrArg (fun M => M pivotRow j) hgo
          calc
            eliminateColLoopMatrix pivotRow pivotCol r cur steps pivotRow j
                = eliminateColLoopMatrix pivotRow pivotCol (r + 1) cur'
                  (List.concat steps (.replace pivotRow i0 (-cur i0 pivotCol / cur pivotRow pivotCol))) pivotRow j := hstep
            _ = cur' pivotRow j := hih
            _ = cur pivotRow j := hpr
        -- No replacement branch: recurse with unchanged state.
        · have hk' : m - (r + 1) = k :=
            by omega
          have hih := ih (r + 1) cur steps hk' j
          have hgo :
              (GaussianEliminationInternal.eliminateColLoopAux pivotRow pivotCol (cur pivotRow pivotCol) (r + 1) cur steps).1 =
                eliminateColLoopMatrix pivotRow pivotCol (r + 1) cur steps := by
            simpa using
              eliminateColLoopAux_matrix_eq
                (pivotRow := pivotRow) (pivotCol := pivotCol)
                (pivotVal := cur pivotRow pivotCol) (r := r + 1) (cur := cur) (steps := steps)
                rfl
          have hstep :
              eliminateColLoopMatrix pivotRow pivotCol r cur steps pivotRow j =
                eliminateColLoopMatrix pivotRow pivotCol (r + 1) cur steps pivotRow j := by
            rw [Matrix.eliminateColLoopMatrix, GaussianEliminationInternal.eliminateColLoop, GaussianEliminationInternal.eliminateColLoopAux, dif_pos hr]
            simpa [i0, hEq, hcoeff] using congrArg (fun M => M pivotRow j) hgo
          calc
            eliminateColLoopMatrix pivotRow pivotCol r cur steps pivotRow j
                = eliminateColLoopMatrix pivotRow pivotCol (r + 1) cur steps pivotRow j := hstep
            _ = cur pivotRow j := hih
  intro r j
  exact hrec (m - r) r cur steps rfl j

/-- Top-level `eliminateColM` preserves the pivot row entrywise. -/
lemma eliminateCol_pivotRow
    (M : Matrix (Fin m) (Fin n) R) (pivotRow : Fin m) (pivotCol : Fin n) :
    ∀ j : Fin n, (eliminateColM M pivotRow pivotCol) pivotRow j = M pivotRow j := by
  intro j
  simpa [eliminateColM, GaussianEliminationInternal.eliminateColCore] using
    (eliminateCol_go_pivotRow
      (cur := M) (pivotRow := pivotRow) (pivotCol := pivotCol) (steps := List.nil) 0 j)

lemma eliminateCol_pivotRow_false
    (M : Matrix (Fin m) (Fin n) R) (pivotRow : Fin m) (pivotCol : Fin n) :
    ∀ j : Fin n, (GaussianEliminationInternal.eliminateColCore M pivotRow pivotCol List.nil false).1 pivotRow j = M pivotRow j := by
  intro j
  simpa [GaussianEliminationInternal.eliminateColCore] using
    (eliminateCol_go_pivotRow
      (cur := M) (pivotRow := pivotRow) (pivotCol := pivotCol)
      (steps := List.nil) pivotRow.1 j)

/--
Assuming the pivot entry is normalized to `1`, `eliminateColM` zeroes the
pivot column at every non-pivot row.
-/
lemma eliminateCol_pivotCol_zero
    (M : Matrix (Fin m) (Fin n) R) (pivotRow : Fin m) (pivotCol : Fin n)
    (h1 : M pivotRow pivotCol = 1) :
    ∀ r : Fin m, r ≠ pivotRow → (eliminateColM M pivotRow pivotCol) r pivotCol = 0 := by
  classical
  intro r hr
  -- Invariant: rows already processed (< `r`) are zero in pivot column,
  -- except possibly `pivotRow`.
  have hrec :
      ∀ k (r : Nat) (cur : Matrix (Fin m) (Fin n) R) (steps : List (RowOp m R)),
        m - r = k →
        (∀ i : Fin m, i.1 < r → i ≠ pivotRow → cur i pivotCol = 0) →
        cur pivotRow pivotCol = 1 →
        ∀ i : Fin m, i ≠ pivotRow →
          (eliminateColLoopMatrix pivotRow pivotCol r cur steps) i pivotCol = 0 := by
    intro k
    induction k with
    | zero =>
      intro r cur steps hk hpre h1 i hi
      -- Base case: no rows left to process; use the precondition directly.
      have hr : m ≤ r := Nat.le_of_sub_eq_zero hk
      have hir : i.1 < r := lt_of_lt_of_le i.2 hr
      rw [Matrix.eliminateColLoopMatrix, GaussianEliminationInternal.eliminateColLoop, GaussianEliminationInternal.eliminateColLoopAux, dif_neg (not_lt_of_ge hr)]
      exact hpre i hir hi
    | succ k ih =>
      intro r cur steps hk hpre h1 i hi
      -- Step case: process current row `i0 = ⟨r,hr⟩`.
      have hr : r < m := by omega
      rw [Matrix.eliminateColLoopMatrix, GaussianEliminationInternal.eliminateColLoop, GaussianEliminationInternal.eliminateColLoopAux, dif_pos hr]
      let i0 : Fin m := ⟨r, hr⟩
      by_cases hi0 : i0 = pivotRow
      · -- Pivot row is skipped; only strengthen the processed-prefix invariant.
        simp only [i0, hi0]
        have hk' : m - (r + 1) = k :=
          by omega
        have hpre' :
            ∀ i : Fin m, i.1 < r + 1 → i ≠ pivotRow → cur i pivotCol = 0 := by
          intro i hi' hne
          have hle : i.1 ≤ r := Nat.lt_succ_iff.mp hi'
          by_cases hir : i.1 < r
          · exact hpre i hir hne
          · have hEq : i.1 = r := le_antisymm hle (le_of_not_gt hir)
            have : i = i0 := by
              ext
              simp [hEq, i0]
            exact (False.elim (hne (by simp [this, hi0])))
        exact ih (r + 1) cur steps hk' hpre' h1 i hi
      · -- Non-pivot row: either eliminate (if coefficient nonzero) or keep as-is.
        simp only [i0, hi0]
        by_cases hcoeff : cur i0 pivotCol ≠ 0
        · have hk' : m - (r + 1) = k :=
            by omega
          let cur' := replace cur pivotRow i0 (-cur i0 pivotCol / cur pivotRow pivotCol)
          -- After replacement, pivot-row pivot-column entry remains `1`.
          have huse : pivotRow ≠ i0 := by
            intro hpr
            exact hi0 hpr.symm
          have h1' : cur' pivotRow pivotCol = 1 := by
            simp [cur', replace, huse, of_apply, h1]
          have hpivot' : cur' pivotRow pivotCol = cur pivotRow pivotCol := by
            calc
              cur' pivotRow pivotCol = 1 := h1'
              _ = cur pivotRow pivotCol := by simp [h1]
          -- Rebuild processed-prefix zero invariant for `cur'`.
          have hpre' :
              ∀ i : Fin m, i.1 < r + 1 → i ≠ pivotRow → cur' i pivotCol = 0 := by
            intro i hi' hne
            have hle : i.1 ≤ r := Nat.lt_succ_iff.mp hi'
            by_cases hir : i.1 < r
            · have hne' : i ≠ i0 := by
                intro hEq
                have : i.1 = r := by simpa [i0] using congrArg Fin.val hEq
                exact (Nat.lt_irrefl _ (this ▸ hir))
              simp [cur', replace, huse, hne', of_apply, hpre i hir hne]
            · have hEq : i.1 = r := le_antisymm hle (le_of_not_gt hir)
              have hEq' : i = i0 := by
                ext
                simp [hEq, i0]
              subst hEq'
              have hzero :=
                replace_pivot_col_zero (M := cur) (pivotRow := pivotRow) (toReplace := i0)
                  (pivotCol := pivotCol) (huse := huse) h1
              exact hzero
          -- Apply induction on recursive call and rewrite back.
          let steps' := List.concat steps (.replace pivotRow i0 (-cur i0 pivotCol / cur pivotRow pivotCol))
          have hih := ih (r + 1) cur' steps' hk' hpre' h1' i hi
          have hgo :
              (GaussianEliminationInternal.eliminateColLoopAux pivotRow pivotCol (cur pivotRow pivotCol) (r + 1) cur' steps').1 =
                eliminateColLoopMatrix pivotRow pivotCol (r + 1) cur' steps' := by
            simpa [steps'] using
              eliminateColLoopAux_matrix_eq
                (pivotRow := pivotRow) (pivotCol := pivotCol)
                (pivotVal := cur pivotRow pivotCol) (r := r + 1) (cur := cur') (steps := steps')
                hpivot'
          have hih' :
              (GaussianEliminationInternal.eliminateColLoopAux pivotRow pivotCol (cur pivotRow pivotCol) (r + 1) cur' steps').1
                i pivotCol = 0 := by
            calc
              (GaussianEliminationInternal.eliminateColLoopAux pivotRow pivotCol (cur pivotRow pivotCol) (r + 1) cur' steps').1
                  i pivotCol = eliminateColLoopMatrix pivotRow pivotCol (r + 1) cur' steps' i pivotCol := by
                    simpa using congrArg (fun M => M i pivotCol) hgo
              _ = 0 := hih
          simpa [i0, hi0, hcoeff, cur', steps'] using hih'
        -- Coefficient already zero: propagate invariant without modifying `cur`.
        · have hk' : m - (r + 1) = k :=
            by omega
          have hcoeff' : cur i0 pivotCol = 0 := by
            by_contra hne; exact hcoeff hne
          have hpre' :
              ∀ i : Fin m, i.1 < r + 1 → i ≠ pivotRow → cur i pivotCol = 0 := by
            intro i hi' hne
            have hle : i.1 ≤ r := Nat.lt_succ_iff.mp hi'
            by_cases hir : i.1 < r
            · exact hpre i hir hne
            · have hEq : i.1 = r := le_antisymm hle (le_of_not_gt hir)
              have hEq' : i = i0 := by
                ext
                simp [hEq, i0]
              subst hEq'
              exact hcoeff'
          have hih := ih (r + 1) cur steps hk' hpre' h1 i hi
          simpa [i0, hi0, hcoeff'] using hih
  -- Initial processed-prefix invariant is vacuous at `r = 0`.
  have hpre0 : ∀ i : Fin m, i.1 < 0 → i ≠ pivotRow → M i pivotCol = 0 := by
    intro i hi
    exact (False.elim (Nat.not_lt_zero _ hi))
  -- Instantiate the recursive invariant from the initial state.
  have hrec' := hrec (m - 0) 0 M List.nil rfl hpre0 h1
  simpa [eliminateColM, GaussianEliminationInternal.eliminateColCore] using hrec' r hr

/--
Assuming the pivot entry is nonzero, `GaussianEliminationInternal.eliminateColCore` with `reduced = false`
zeroes the pivot column at every row strictly below the pivot.
-/
lemma eliminateCol_below_pivotCol_zero
    (M : Matrix (Fin m) (Fin n) R) (pivotRow : Fin m) (pivotCol : Fin n)
    (hne : M pivotRow pivotCol ≠ 0) :
    ∀ r : Fin m, pivotRow.1 < r.1 →
      (GaussianEliminationInternal.eliminateColCore M pivotRow pivotCol List.nil false).1 r pivotCol = 0 := by
  classical
  intro r hr
  have hrec :
      ∀ k (r0 : Nat) (cur : Matrix (Fin m) (Fin n) R) (steps : List (RowOp m R)),
        m - r0 = k →
        (∀ i : Fin m, pivotRow.1 < i.1 → i.1 < r0 → cur i pivotCol = 0) →
        cur pivotRow pivotCol ≠ 0 →
        ∀ i : Fin m, pivotRow.1 < i.1 →
          (eliminateColLoopMatrix pivotRow pivotCol r0 cur steps) i pivotCol = 0 := by
    intro k
    induction k with
    | zero =>
        intro r0 cur steps hk hpre hpivot i hi
        have hr0 : m ≤ r0 := Nat.le_of_sub_eq_zero hk
        have hii : i.1 < r0 := lt_of_lt_of_le i.2 hr0
        rw [Matrix.eliminateColLoopMatrix, GaussianEliminationInternal.eliminateColLoop, GaussianEliminationInternal.eliminateColLoopAux,
          dif_neg (not_lt_of_ge hr0)]
        exact hpre i hi hii
    | succ k ih =>
        intro r0 cur steps hk hpre hpivot i hi
        have hr0 : r0 < m := by omega
        rw [Matrix.eliminateColLoopMatrix, GaussianEliminationInternal.eliminateColLoop, GaussianEliminationInternal.eliminateColLoopAux, dif_pos hr0]
        let i0 : Fin m := ⟨r0, hr0⟩
        by_cases hi0 : i0 = pivotRow
        · have hk' : m - (r0 + 1) = k := by omega
          have hpre' :
              ∀ i : Fin m, pivotRow.1 < i.1 → i.1 < r0 + 1 → cur i pivotCol = 0 := by
            intro i hi' hir'
            have hir : i.1 < r0 := by
              by_cases hEq : i.1 = r0
              · exfalso
                have hp : pivotRow.1 = r0 := by simpa [i0] using congrArg Fin.val hi0.symm
                simp [hEq, hp] at hi'
              · omega
            exact hpre i hi' hir
          simpa [i0, hi0] using ih (r0 + 1) cur steps hk' hpre' hpivot i hi
        · by_cases hcoeff : cur i0 pivotCol ≠ 0
          · have hk' : m - (r0 + 1) = k := by omega
            let cur' := replace cur pivotRow i0 (-cur i0 pivotCol / cur pivotRow pivotCol)
            let steps' := List.concat steps (.replace pivotRow i0 (-cur i0 pivotCol / cur pivotRow pivotCol))
            have huse : pivotRow ≠ i0 := by
              intro hpr
              exact hi0 hpr.symm
            have hpivot' : cur' pivotRow pivotCol = cur pivotRow pivotCol := by
              simpa [cur'] using
                replace_apply_of_ne
                  (M := cur) (use := pivotRow) (toReplace := i0)
                  (k := -cur i0 pivotCol / cur pivotRow pivotCol)
                  (r := pivotRow) (j := pivotCol) (huse := huse) (hrow := huse)
            have hpre' :
                ∀ i : Fin m, pivotRow.1 < i.1 → i.1 < r0 + 1 → cur' i pivotCol = 0 := by
              intro i hi' hir'
              have hle : i.1 ≤ r0 := Nat.lt_succ_iff.mp hir'
              by_cases hir : i.1 < r0
              · have hne : i ≠ i0 := by
                  intro hEq
                  have : i.1 = r0 := by simpa [i0] using congrArg Fin.val hEq
                  exact (Nat.lt_irrefl _ (this ▸ hir))
                simp [cur', replace, huse, hne, of_apply, hpre i hi' hir]
              · have hEq : i.1 = r0 := le_antisymm hle (le_of_not_gt hir)
                have hEq' : i = i0 := by
                  ext
                  simp [hEq, i0]
                subst hEq'
                exact replace_pivot_col_zero_of_ne
                  (M := cur) (pivotRow := pivotRow) (toReplace := i0)
                  (pivotCol := pivotCol) huse hpivot
            have hgo :
                (GaussianEliminationInternal.eliminateColLoopAux pivotRow pivotCol (cur pivotRow pivotCol) (r0 + 1) cur' steps').1 =
                  eliminateColLoopMatrix pivotRow pivotCol (r0 + 1) cur' steps' := by
              simpa [steps'] using
                eliminateColLoopAux_matrix_eq
                  (pivotRow := pivotRow) (pivotCol := pivotCol)
                  (pivotVal := cur pivotRow pivotCol) (r := r0 + 1) (cur := cur') (steps := steps')
                  hpivot'
            have hih := ih (r0 + 1) cur' steps' hk' hpre' (by simpa [hpivot'] using hpivot) i hi
            have hih' :
                (GaussianEliminationInternal.eliminateColLoopAux pivotRow pivotCol (cur pivotRow pivotCol) (r0 + 1) cur' steps').1 i pivotCol = 0 := by
              calc
                (GaussianEliminationInternal.eliminateColLoopAux pivotRow pivotCol (cur pivotRow pivotCol) (r0 + 1) cur' steps').1 i pivotCol
                    = eliminateColLoopMatrix pivotRow pivotCol (r0 + 1) cur' steps' i pivotCol := by
                        simpa using congrArg (fun M => M i pivotCol) hgo
                _ = 0 := hih
            simpa [i0, hi0, hcoeff, cur', steps'] using hih'
          · have hk' : m - (r0 + 1) = k := by omega
            have hcoeff' : cur i0 pivotCol = 0 := by
              by_contra hne'
              exact hcoeff hne'
            have hpre' :
                ∀ i : Fin m, pivotRow.1 < i.1 → i.1 < r0 + 1 → cur i pivotCol = 0 := by
              intro i hi' hir'
              have hle : i.1 ≤ r0 := Nat.lt_succ_iff.mp hir'
              by_cases hir : i.1 < r0
              · exact hpre i hi' hir
              · have hEq : i.1 = r0 := le_antisymm hle (le_of_not_gt hir)
                have hEq' : i = i0 := by
                  ext
                  simp [hEq, i0]
                subst hEq'
                exact hcoeff'
            have hih := ih (r0 + 1) cur steps hk' hpre' hpivot i hi
            simpa [i0, hi0, hcoeff'] using hih
  have hpre0 : ∀ i : Fin m, pivotRow.1 < i.1 → i.1 < pivotRow.1 → M i pivotCol = 0 := by
    intro i hi hlt
    exact (False.elim (Nat.not_lt_of_ge (le_of_lt hi) hlt))
  have hrec' := hrec (m - pivotRow.1) pivotRow.1 M List.nil rfl hpre0 hne r hr
  simpa [Matrix.eliminateColLoopMatrix, GaussianEliminationInternal.eliminateColCore] using hrec'

end Matrix
