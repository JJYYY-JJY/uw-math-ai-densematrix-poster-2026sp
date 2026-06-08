import ProvableComputation.LinearAlgebra.GaussianElimination.Elementary
import ProvableComputation.LinearAlgebra.GaussianElimination.Pivot

/-!
# Gaussian Elimination Correctness

This module proves that the executable row-reduction procedures produce echelon and reduced
row-echelon forms, preserve the appropriate linear-algebraic invariants, and correctly log
their elementary row operations.
-/

namespace Matrix

open GaussianEliminationInternal

variable {R : Type} [Field R] [DecidableEq R]
variable {m n : ℕ}

private lemma fin_eq_of_val_eq {n : ℕ} {i : Fin n} {k : ℕ} (hk : k < n) (h : i.1 = k) :
    i = ⟨k, hk⟩ := by
  ext
  exact h

/-- Matrix output of `rrefAux` when starting from an empty step log. -/
abbrev rrefAuxM
    (M : Matrix (Fin m) (Fin n) R) (row col : Nat) (steps : List (RowOp m R)) :
    Matrix (Fin m) (Fin n) R :=
  (rowReductionAux M row col steps true).1

/-! Echelon invariants. -/

structure EchelonStateCore (M : Matrix (Fin m) (Fin n) R) (row col bound : Nat)
    (pivs : ∀ i : Fin m, i.1 < row → Fin n) : Prop where
  row_le : row ≤ m
  bound_le : bound ≤ n
  col_le : col ≤ bound
  pivot_row : ∀ i hi, IsPivot M i (pivs i hi)
  pivot_strict : ∀ i j hi hj, i.1 < j.1 → pivs i hi < pivs j hj
  pivot_lt_bound : ∀ i hi, (pivs i hi).1 < bound
  cols_lt_bound_zero :
    ∀ r : Fin m, row ≤ r.1 → ∀ j : Fin n, j.1 < bound → M r j = 0

structure ReducedStateExtras (M : Matrix (Fin m) (Fin n) R) (row : Nat)
    (pivs : ∀ i : Fin m, i.1 < row → Fin n) : Prop where
  pivot_one : ∀ i hi, M i (pivs i hi) = 1
  pivot_col_zero : ∀ i hi r, r ≠ i → M r (pivs i hi) = 0

structure EchelonState (M : Matrix (Fin m) (Fin n) R) (row col bound : Nat)
    (pivs : ∀ i : Fin m, i.1 < row → Fin n) : Prop extends
    EchelonStateCore (M := M) row col bound pivs,
    ReducedStateExtras (M := M) row pivs

private def mkEchelonState
    (M : Matrix (Fin m) (Fin n) R) (row col bound : Nat)
    (pivs : ∀ i : Fin m, i.1 < row → Fin n)
    (row_le : row ≤ m)
    (bound_le : bound ≤ n)
    (col_le : col ≤ bound)
    (pivot_row : ∀ i hi, IsPivot M i (pivs i hi))
    (pivot_strict : ∀ i j hi hj, i.1 < j.1 → pivs i hi < pivs j hj)
    (pivot_lt_bound : ∀ i hi, (pivs i hi).1 < bound)
    (cols_lt_bound_zero :
      ∀ r : Fin m, row ≤ r.1 → ∀ j : Fin n, j.1 < bound → M r j = 0)
    (pivot_one : ∀ i hi, M i (pivs i hi) = 1)
    (pivot_col_zero : ∀ i hi r, r ≠ i → M r (pivs i hi) = 0) :
    EchelonState (M := M) row col bound pivs :=
  { toEchelonStateCore := {
      row_le := row_le
      bound_le := bound_le
      col_le := col_le
      pivot_row := pivot_row
      pivot_strict := pivot_strict
      pivot_lt_bound := pivot_lt_bound
      cols_lt_bound_zero := cols_lt_bound_zero
    }
    toReducedStateExtras := {
      pivot_one := pivot_one
      pivot_col_zero := pivot_col_zero
    }
  }

omit [DecidableEq R] in
lemma echelon_of_state
    (M : Matrix (Fin m) (Fin n) R) (row col bound : Nat)
    (pivs : ∀ i : Fin m, i.1 < row → Fin n)
    (hcore : EchelonStateCore (M := M) row col bound pivs)
    (hzero : ∀ r : Fin m, row ≤ r.1 → RowIsZero M r) :
    IsEchelonForm (M := M) := by
  classical
  refine IsEchelonForm.mk ?row_zero_or_pivot ?zero_rows_bottom ?pivots_strict
  · intro i
    by_cases hi : i.1 < row
    · right
      refine ⟨pivs i hi, hcore.pivot_row i hi⟩
    · left
      have hi' : row ≤ i.1 := by omega
      exact hzero i hi'
  · intro i j hij hzi
    by_cases hi : i.1 < row
    · have : False := RowIsZero.not_isPivot (M := M) (i := i)
        (p := pivs i hi) hzi (hcore.pivot_row i hi)
      exact (False.elim this)
    · have hi' : row ≤ i.1 := by omega
      have hj' : row ≤ j.1 := le_trans hi' (le_of_lt hij)
      exact hzero j hj'
  · intro i j p q hij hp hq
    by_cases hi : i.1 < row
    · by_cases hj : j.1 < row
      · have hp' : p = pivs i hi := IsPivot.eq_of_left hp (hcore.pivot_row i hi)
        have hq' : q = pivs j hj := IsPivot.eq_of_left hq (hcore.pivot_row j hj)
        subst hp'; subst hq'
        exact hcore.pivot_strict i j hi hj (by simpa using hij)
      · have hj' : row ≤ j.1 := by omega
        have hz : RowIsZero M j := hzero j hj'
        exact (False.elim (RowIsZero.not_isPivot (M := M) (i := j) (p := q) hz hq))
    · have hi' : row ≤ i.1 := by omega
      have hz : RowIsZero M i := hzero i hi'
      exact (False.elim (RowIsZero.not_isPivot (M := M) (i := i) (p := p) hz hp))

omit [DecidableEq R] in
lemma reduced_of_state
    (M : Matrix (Fin m) (Fin n) R) (row col bound : Nat)
    (pivs : ∀ i : Fin m, i.1 < row → Fin n)
    (hcore : EchelonStateCore (M := M) row col bound pivs)
    (hextras : ReducedStateExtras (M := M) row pivs)
    (hzero : ∀ r : Fin m, row ≤ r.1 → RowIsZero M r) :
    IsReducedEchelonForm (M := M) := by
  classical
  refine IsReducedEchelonForm.mk ?echelon ?pivot_is_one ?pivot_col_zero_above
  · exact echelon_of_state (M := M) row col bound pivs hcore hzero
  · intro i p hp
    by_cases hi : i.1 < row
    · have hp' : p = pivs i hi := IsPivot.eq_of_left hp (hcore.pivot_row i hi)
      subst hp'
      exact hextras.pivot_one i hi
    · have hi' : row ≤ i.1 := by omega
      have hz : RowIsZero M i := hzero i hi'
      exact (False.elim (RowIsZero.not_isPivot (M := M) (i := i) (p := p) hz hp))
  · intro i r p hr hp
    by_cases hi : i.1 < row
    · have hp' : p = pivs i hi := IsPivot.eq_of_left hp (hcore.pivot_row i hi)
      subst hp'
      have hrne : r ≠ i := by
        intro hEq
        cases hEq
        exact lt_irrefl _ hr
      exact hextras.pivot_col_zero i hi r hrne
    · have hi' : row ≤ i.1 := by omega
      have hz : RowIsZero M i := hzero i hi'
      exact (False.elim (RowIsZero.not_isPivot (M := M) (i := i) (p := p) hz hp))

omit [DecidableEq R] in
private lemma zero_rows_of_row_ge
    (M : Matrix (Fin m) (Fin n) R) (row : Nat) (hrow : m ≤ row) :
    ∀ r : Fin m, row ≤ r.1 → RowIsZero M r := by
  intro r hr
  have hlt : r.1 < row := lt_of_lt_of_le r.2 hrow
  exact False.elim ((Nat.not_lt_of_ge hr) hlt)

private lemma zero_rows_of_checkPivot_none
    (M : Matrix (Fin m) (Fin n) R) (row col bound : Nat)
    (pivs : ∀ i : Fin m, i.1 < row → Fin n)
    (hstate : EchelonStateCore (M := M) row col bound pivs)
    (hnone : checkPivot M row col = none) :
    ∀ r : Fin m, row ≤ r.1 → RowIsZero M r := by
  intro r hr j
  by_cases hjb : j.1 < bound
  · exact hstate.cols_lt_bound_zero r hr j hjb
  · have hjc : col ≤ j.1 := by
      have : bound ≤ j.1 := by omega
      exact le_trans hstate.col_le this
    exact checkPivot_none_zero (M := M) row col hnone j hjc r hr

omit [DecidableEq R] in
private lemma zero_rows_of_col_ge
    (M : Matrix (Fin m) (Fin n) R) (row col bound : Nat)
    (pivs : ∀ i : Fin m, i.1 < row → Fin n)
    (hstate : EchelonStateCore (M := M) row col bound pivs)
    (hcol : ¬ col < n) :
    ∀ r : Fin m, row ≤ r.1 → RowIsZero M r := by
  intro r hr j
  have hbound : bound = n := by
    have hcolle : col ≤ bound := hstate.col_le
    have hboundle : bound ≤ n := hstate.bound_le
    omega
  have hj : j.1 < bound := by
    rw [hbound]
    exact j.2
  exact hstate.cols_lt_bound_zero r hr j hj

omit [DecidableEq R] in
private def emptyPivs :
    ∀ i : Fin m, i.1 < 0 → Fin n := by
  intro _ hi
  omega

omit [DecidableEq R] in
private lemma initial_state (M : Matrix (Fin m) (Fin n) R) :
    EchelonState (M := M) (row := 0) (col := 0) (bound := 0) emptyPivs := by
  refine mkEchelonState (M := M) (row := 0) (col := 0) (bound := 0) (pivs := emptyPivs)
    ?row_le ?bound_le
    ?col_le ?pivot_row
    ?pivot_strict
    ?pivot_lt_bound
    ?cols_zero
    ?pivot_one
    ?pivot_col_zero
  · omega
  · omega
  · omega
  · intro i hi; omega
  · intro i j hi hj hij; omega
  · intro i hi; omega
  · intro r hr j hj; omega
  · intro i hi; omega
  · intro i hi r hr; omega

/-! Step lemma: update state after a pivot. -/

private def extendPivs (row : Nat)
    (pivs : ∀ i : Fin m, i.1 < row → Fin n)
    (pivotCol : Fin n) :
    ∀ i : Fin m, i.1 < row + 1 → Fin n :=
  fun i _ =>
    if hlt : i.1 < row then pivs i hlt else pivotCol

private lemma pivotCol_ge_bound
    (M : Matrix (Fin m) (Fin n) R) (row col bound : Nat)
    (pivs : ∀ i : Fin m, i.1 < row → Fin n)
    (hstate : EchelonStateCore (M := M) row col bound pivs)
    {pr : Fin m} {pc : Fin n} (h : checkPivot M row col = some (pr, pc)) :
    bound ≤ pc.1 := by
  by_contra hlt
  have hlt' : pc.1 < bound := lt_of_not_ge hlt
  have hrow : row ≤ pr.1 := checkPivot_some_row_ge (M := M) row col h
  have hzero : M pr pc = 0 :=
    hstate.cols_lt_bound_zero pr hrow pc (by simpa using hlt')
  exact (checkPivot_some_nonzero (M := M) row col h) hzero

private lemma pivot_row_zero_left
    (M : Matrix (Fin m) (Fin n) R) (row col bound : Nat)
    (pivs : ∀ i : Fin m, i.1 < row → Fin n)
    (hstate : EchelonStateCore (M := M) row col bound pivs)
    {pr : Fin m} {pc : Fin n} (h : checkPivot M row col = some (pr, pc)) :
    ∀ j : Fin n, j < pc → M pr j = 0 := by
  intro j hj
  have hrow : row ≤ pr.1 := checkPivot_some_row_ge (M := M) row col h
  have hbound : bound ≤ pc.1 := pivotCol_ge_bound (M := M) row col bound pivs hstate h
  have hj' : j.1 < bound ∨ col ≤ j.1 := by
    by_cases h1 : j.1 < bound
    · left; exact h1
    · right
      have : bound ≤ j.1 := by omega
      exact le_trans (hstate.col_le) this
  cases hj' with
  | inl hlt =>
      exact hstate.cols_lt_bound_zero pr hrow j hlt
  | inr hge =>
      exact checkPivot_some_minimal (M := M) row col h j hge hj pr hrow

omit [DecidableEq R] in
private lemma isPivot_swap_of_ne
    (M : Matrix (Fin m) (Fin n) R) (i r₁ r₂ : Fin m) (p : Fin n)
    (h1 : i ≠ r₁) (h2 : i ≠ r₂) :
    IsPivot M i p → IsPivot (swapRow M r₁ r₂) i p := by
  intro hp
  refine ⟨?h0, ?hleft⟩
  · -- pivot entry unchanged
    simp [swapRow, of_apply, h1, h2, hp.1]
  · intro j hj
    simp [swapRow, of_apply, h1, h2, hp.2 j hj]

omit [DecidableEq R] in
private lemma isPivot_factor_of_ne
    (M : Matrix (Fin m) (Fin n) R) (i r : Fin m) (p : Fin n) (s : R)
    (h : i ≠ r) :
    IsPivot M i p → IsPivot (factor M r s) i p := by
  intro hp
  refine ⟨?h0, ?hleft⟩
  · simp [factor, of_apply, h, hp.1]
  · intro j hj
    simp [factor, of_apply, h, hp.2 j hj]

private lemma isPivot_eliminate_preserve
    (M : Matrix (Fin m) (Fin n) R) (pivotRow : Fin m) (pivotCol : Fin n)
    {i : Fin m} {p : Fin n} (hp : IsPivot M i p)
    (hzero : ∀ j : Fin n, j < pivotCol → M pivotRow j = 0) (hp_lt : p < pivotCol) :
    IsPivot (eliminateColM M pivotRow pivotCol) i p := by
  classical
  -- elimination only replaces rows using pivotRow; columns < pivotCol stay unchanged
  -- so the pivot remains
  have hpres : ∀ j : Fin n, j < pivotCol →
      (eliminateColM M pivotRow pivotCol) i j = M i j := by
    intro j hj
    -- use preservation of column j
    simpa [eliminateColM, eliminateColCore] using
      (eliminateCol_go_preserves_col (cur := M) (pivotRow := pivotRow)
        (pivotCol := pivotCol) (r := 0) (steps := List.nil) (j := j) (hzero := hzero j hj) i)
  refine ⟨?h0, ?hleft⟩
  · have h0 := hpres p hp_lt
    simpa [h0] using hp.1
  · intro j hj
    have h0 := hpres j (lt_of_lt_of_le hj (le_of_lt hp_lt))
    simpa [h0] using hp.2 j hj

omit [DecidableEq R] in
private lemma pivot_lt_newPivot
    (M : Matrix (Fin m) (Fin n) R) (row col bound : Nat)
    (pivs : ∀ i : Fin m, i.1 < row → Fin n)
    (hstate : EchelonStateCore (M := M) row col bound pivs)
    {pc : Fin n} (hbound : bound ≤ pc.1)
    (i : Fin m) (hlt : i.1 < row) :
    pivs i hlt < pc := by
  have hltb : (pivs i hlt).1 < bound := hstate.pivot_lt_bound i hlt
  have hltpc : (pivs i hlt).1 < pc.1 := lt_of_lt_of_le hltb hbound
  simpa using hltpc

private lemma step_pivot_row
    (M : Matrix (Fin m) (Fin n) R) (row col bound : Nat)
    (pivs : ∀ i : Fin m, i.1 < row → Fin n)
    (hstate : EchelonStateCore (M := M) row col bound pivs)
    (hrow : row < m) {pr : Fin m} {pc : Fin n}
    (hbound : bound ≤ pc.1) (hpr_ge : row ≤ pr.1) :
    let m1 := if pr.1 = row then M else swapRow M ⟨row, hrow⟩ pr
    let pivotVal : R := m1 ⟨row, hrow⟩ pc
    let m2 := if pivotVal = 1 then m1 else factor m1 ⟨row, hrow⟩ (pivotVal)⁻¹
    let m3 := eliminateColM m2 ⟨row, hrow⟩ pc
    (∀ j : Fin n, j < pc → m2 ⟨row, hrow⟩ j = 0) →
    (∀ j : Fin n, m3 ⟨row, hrow⟩ j = m2 ⟨row, hrow⟩ j) →
    m2 ⟨row, hrow⟩ pc = 1 →
    ∀ i : Fin m, ∀ hi : i.1 < row + 1, IsPivot m3 i ((extendPivs row pivs pc) i hi) := by
  intro m1 pivotVal m2 m3 hzero_left_m2 hrow_unchanged h1 i hi
  by_cases hlt : i.1 < row
  · have hp : IsPivot M i (pivs i hlt) := hstate.pivot_row i hlt
    have hne1 : i ≠ ⟨row, hrow⟩ := by
      intro hEq
      have : i.1 = row := by simpa using congrArg Fin.val hEq
      exact (lt_irrefl _ (this ▸ hlt))
    have hne2 : i ≠ pr := by
      have hltpr : i.1 < pr.1 := by omega
      intro hEq
      have : i.1 = pr.1 := by simpa using congrArg Fin.val hEq
      exact (lt_irrefl _ (this ▸ hltpr))
    have hp1 : IsPivot m1 i (pivs i hlt) := by
      by_cases hpr : pr.1 = row
      · simpa [m1, hpr] using hp
      · have hp' :=
          isPivot_swap_of_ne (M := M) (i := i) (r₁ := ⟨row, hrow⟩) (r₂ := pr)
            (p := pivs i hlt) hne1 hne2 hp
        simpa [m1, hpr] using hp'
    have hp2 : IsPivot m2 i (pivs i hlt) := by
      by_cases hpv : pivotVal = 1
      · simpa [m2, hpv] using hp1
      · have hp2' : IsPivot (factor m1 ⟨row, hrow⟩ pivotVal⁻¹) i (pivs i hlt) :=
          isPivot_factor_of_ne (M := m1) (i := i) (r := ⟨row, hrow⟩)
            (p := pivs i hlt) (s := pivotVal⁻¹) hne1 hp1
        simpa [m2, hpv] using hp2'
    have hp_lt : pivs i hlt < pc :=
      pivot_lt_newPivot (M := M) row col bound pivs hstate
        (pc := pc) hbound i hlt
    have hp3 : IsPivot m3 i (pivs i hlt) :=
      isPivot_eliminate_preserve (M := m2) (pivotRow := ⟨row, hrow⟩) (pivotCol := pc)
        (p := pivs i hlt) (hp := hp2) (hzero := hzero_left_m2) hp_lt
    simpa [extendPivs, hlt] using hp3
  · have hi_le : i.1 ≤ row := by omega
    have hi_eq : i.1 = row := by omega
    have hrowi : i = ⟨row, hrow⟩ := fin_eq_of_val_eq hrow hi_eq
    subst hrowi
    have hp : IsPivot m3 ⟨row, hrow⟩ pc := by
      refine ⟨?h0, ?hleft⟩
      · have hrowpc : m3 ⟨row, hrow⟩ pc = 1 := by
          have := hrow_unchanged pc
          simp only [h1] at this
          exact this
        simp [hrowpc]
      · intro j hj
        have := hrow_unchanged j
        have h0 := hzero_left_m2 j hj
        simp only [h0] at this
        exact this
    simpa [extendPivs, hlt, hi_eq] using hp

omit [DecidableEq R] in
private lemma step_pivot_strict
    (M : Matrix (Fin m) (Fin n) R) (row col bound : Nat)
    (pivs : ∀ i : Fin m, i.1 < row → Fin n)
    (hstate : EchelonStateCore (M := M) row col bound pivs)
    {pc : Fin n} (hbound : bound ≤ pc.1) :
    ∀ i j : Fin m, ∀ hi : i.1 < row + 1, ∀ hj : j.1 < row + 1,
      i.1 < j.1 → (extendPivs row pivs pc i hi) < (extendPivs row pivs pc j hj) := by
  intro i j hi hj hij
  by_cases hi' : i.1 < row
  · by_cases hj' : j.1 < row
    · have hp_lt := hstate.pivot_strict i j hi' hj' hij
      simpa [extendPivs, hi', hj'] using hp_lt
    · have hj_le : j.1 ≤ row := by omega
      have hj_eq : j.1 = row := by omega
      have hp_lt : pivs i hi' < pc :=
        pivot_lt_newPivot (M := M) row col bound pivs hstate (pc := pc) hbound i hi'
      simpa [extendPivs, hi', hj_eq] using hp_lt
  · have hi_le : i.1 ≤ row := by omega
    have hi_eq : i.1 = row := by omega
    have hj_le : j.1 ≤ row := by omega
    have hlt' : row < j.1 := by
      simpa [hi_eq] using hij
    exact (False.elim (not_lt_of_ge hj_le hlt'))

omit [DecidableEq R] in
private lemma step_pivot_lt_bound
    (M : Matrix (Fin m) (Fin n) R) (row col bound : Nat)
    (pivs : ∀ i : Fin m, i.1 < row → Fin n)
    (hstate : EchelonStateCore (M := M) row col bound pivs)
    {pc : Fin n} (hbound : bound ≤ pc.1) :
    ∀ i : Fin m, ∀ hi : i.1 < row + 1, ((extendPivs row pivs pc i hi).1 < pc.1 + 1) := by
  intro i hi
  by_cases hi' : i.1 < row
  · have hltpc : (pivs i hi').1 < pc.1 := by
      simpa using (pivot_lt_newPivot (M := M) row col bound pivs hstate (pc := pc) hbound i hi')
    have hlt' : (pivs i hi').1 < pc.1 + 1 := by omega
    simp [extendPivs, hi', hlt']
  · have hi_eq : i.1 = row := by
      have hi_le : i.1 ≤ row := by omega
      exact le_antisymm hi_le (by omega)
    have hlt' : pc.1 < pc.1 + 1 := by omega
    simp [extendPivs, hi', hlt']

private lemma step_cols_lt_bound_zero
    (M : Matrix (Fin m) (Fin n) R) (row col bound : Nat)
    (pivs : ∀ i : Fin m, i.1 < row → Fin n)
    (hstate : EchelonStateCore (M := M) row col bound pivs)
    (hrow : row < m) {pr : Fin m} {pc : Fin n}
    (h : checkPivot M row col = some (pr, pc))
    (hbound : bound ≤ pc.1) :
    let m1 := if pr.1 = row then M else swapRow M ⟨row, hrow⟩ pr
    let pivotVal : R := m1 ⟨row, hrow⟩ pc
    let m2 := if pivotVal = 1 then m1 else factor m1 ⟨row, hrow⟩ (pivotVal)⁻¹
    let m3 := eliminateColM m2 ⟨row, hrow⟩ pc
    (∀ j : Fin n, j < pc → m2 ⟨row, hrow⟩ j = 0) →
    m2 ⟨row, hrow⟩ pc = 1 →
    ∀ r : Fin m, row + 1 ≤ r.1 → ∀ j : Fin n, j.1 < pc.1 + 1 → m3 r j = 0 := by
  intro m1 pivotVal m2 m3 hzero_left_m2 h1 r hr j hj
  have hr_ge : row ≤ r.1 := by omega
  have hrrow : r ≠ ⟨row, hrow⟩ := by
    intro hEq
    cases hEq
    exact (Nat.not_succ_le_self _ hr)
  have hcol' : j.1 < pc.1 ∨ j.1 = pc.1 := by
    omega
  cases hcol' with
  | inl hjlt =>
      have hjlt' : j < pc := by
        exact hjlt
      have hzeroM : ∀ r : Fin m, row ≤ r.1 → M r j = 0 := by
        intro r hr'
        by_cases hjb : j.1 < bound
        · exact hstate.cols_lt_bound_zero r hr' j hjb
        · have hjc : col ≤ j.1 := by
            have hb : bound ≤ j.1 := le_of_not_gt hjb
            exact le_trans hstate.col_le hb
          exact checkPivot_some_minimal (M := M) row col h j hjc (by simpa using hjlt) r hr'
      have hm1r : m1 r j = 0 := by
        by_cases hpr : pr.1 = row
        · simp [m1, hpr, hzeroM r hr_ge]
        · by_cases hrpr : r = pr
          · have hnepr : pr ≠ ⟨row, hrow⟩ := by
              intro hEq
              exact hpr (by simpa using congrArg Fin.val hEq)
            simp [m1, hpr, swapRow, of_apply, hrpr, hnepr,
              hzeroM ⟨row, hrow⟩ (Nat.le_refl _)]
          · simp [m1, hpr, swapRow, of_apply, hrpr, hrrow, hzeroM r hr_ge]
      exact
        (calc
          m3 r j = m2 r j := by
            simpa [m3] using
              (eliminateCol_go_preserves_col (cur := m2) (pivotRow := ⟨row, hrow⟩)
                (pivotCol := pc) (r := 0) (steps := List.nil) (j := j)
                (hzero := hzero_left_m2 j hjlt') r)
          _ = 0 := by
            by_cases hpv : pivotVal = 1
            · simp [m2, hpv, hm1r]
            · simp [m2, hpv, factor, of_apply, hrrow, hm1r])
  | inr hjEq =>
      have hjeq : j = pc := Fin.ext (by simpa using hjEq)
      subst hjeq
      have hzeror : m3 r j = 0 := by
        simpa [m3] using
          eliminateCol_pivotCol_zero
          (M := m2)
          (pivotRow := ⟨row, hrow⟩)
          (pivotCol := j)
          h1 r hrrow
      simpa using hzeror

private lemma step_pivot_row_core
    (M : Matrix (Fin m) (Fin n) R) (row col bound : Nat)
    (pivs : ∀ i : Fin m, i.1 < row → Fin n)
    (hstate : EchelonStateCore (M := M) row col bound pivs)
    (hrow : row < m) {pr : Fin m} {pc : Fin n}
    (hbound : bound ≤ pc.1) (hpr_ge : row ≤ pr.1) :
    let rowFin : Fin m := ⟨row, hrow⟩
    let m1 := if pr.1 = row then M else swapRow M rowFin pr
    let m3 := (eliminateColCore m1 rowFin pc List.nil false).1
    (∀ j : Fin n, j < pc → m1 rowFin j = 0) →
    (∀ j : Fin n, m3 rowFin j = m1 rowFin j) →
    m1 rowFin pc ≠ 0 →
    ∀ i : Fin m, ∀ hi : i.1 < row + 1, IsPivot m3 i ((extendPivs row pivs pc) i hi) := by
  intro rowFin m1 m3 hzero_left_m1 hrow_unchanged hneq i hi
  by_cases hlt : i.1 < row
  · have hp : IsPivot M i (pivs i hlt) := hstate.pivot_row i hlt
    have hne1 : i ≠ rowFin := by
      intro hEq
      have : i.1 = row := by simpa using congrArg Fin.val hEq
      exact (lt_irrefl _ (this ▸ hlt))
    have hne2 : i ≠ pr := by
      have hltpr : i.1 < pr.1 := by omega
      intro hEq
      have : i.1 = pr.1 := by simpa using congrArg Fin.val hEq
      exact (lt_irrefl _ (this ▸ hltpr))
    have hp1 : IsPivot m1 i (pivs i hlt) := by
      by_cases hpr : pr.1 = row
      · simpa [m1, hpr] using hp
      · have hp' :=
          isPivot_swap_of_ne (M := M) (i := i) (r₁ := rowFin) (r₂ := pr)
            (p := pivs i hlt) hne1 hne2 hp
        simpa [m1, hpr] using hp'
    have hp_lt : pivs i hlt < pc :=
      pivot_lt_newPivot (M := M) row col bound pivs hstate (pc := pc) hbound i hlt
    have hp3 : IsPivot m3 i (pivs i hlt) := by
      refine ⟨?_, ?_⟩
      · have hpres : m3 i (pivs i hlt) = m1 i (pivs i hlt) := by
          simpa [m3, eliminateColCore] using
            (eliminateCol_go_preserves_col (cur := m1) (pivotRow := rowFin)
              (pivotCol := pc) (r := row) (steps := List.nil) (j := pivs i hlt)
              (hzero := hzero_left_m1 (pivs i hlt) hp_lt) i)
        simpa [hpres] using hp1.1
      · intro j hj
        have hjpc : j < pc := lt_of_lt_of_le hj (le_of_lt hp_lt)
        have hpres : m3 i j = m1 i j := by
          simpa [m3, eliminateColCore] using
            (eliminateCol_go_preserves_col (cur := m1) (pivotRow := rowFin)
              (pivotCol := pc) (r := row) (steps := List.nil) (j := j)
              (hzero := hzero_left_m1 j hjpc) i)
        simpa [hpres] using hp1.2 j hj
    simpa [extendPivs, hlt] using hp3
  · have hi_le : i.1 ≤ row := by omega
    have hi_eq : i.1 = row := by omega
    have hrowi : i = rowFin := fin_eq_of_val_eq hrow hi_eq
    subst hrowi
    have hp : IsPivot m3 rowFin pc := by
      refine ⟨?_, ?_⟩
      · have hrowpc : m3 rowFin pc = m1 rowFin pc := hrow_unchanged pc
        simpa [hrowpc] using hneq
      · intro j hj
        have hrowj : m3 rowFin j = m1 rowFin j := hrow_unchanged j
        simpa [hrowj] using hzero_left_m1 j hj
    simpa [extendPivs, hlt, hi_eq] using hp

private lemma step_cols_lt_bound_zero_core
    (M : Matrix (Fin m) (Fin n) R) (row col bound : Nat)
    (pivs : ∀ i : Fin m, i.1 < row → Fin n)
    (hstate : EchelonStateCore (M := M) row col bound pivs)
    (hrow : row < m) {pr : Fin m} {pc : Fin n}
    (h : checkPivot M row col = some (pr, pc))
    (_hbound : bound ≤ pc.1) :
    let rowFin : Fin m := ⟨row, hrow⟩
    let m1 := if pr.1 = row then M else swapRow M rowFin pr
    let m3 := (eliminateColCore m1 rowFin pc List.nil false).1
    (∀ j : Fin n, j < pc → m1 rowFin j = 0) →
    m1 rowFin pc ≠ 0 →
    ∀ r : Fin m, row + 1 ≤ r.1 → ∀ j : Fin n, j.1 < pc.1 + 1 → m3 r j = 0 := by
  intro rowFin m1 m3 hzero_left_m1 hneq r hr j hj
  have hr_ge : row ≤ r.1 := by omega
  have hrrow : r ≠ rowFin := by
    intro hEq
    cases hEq
    exact (Nat.not_succ_le_self _ hr)
  have hcol' : j.1 < pc.1 ∨ j.1 = pc.1 := by omega
  cases hcol' with
  | inl hjlt =>
      have hjlt' : j < pc := hjlt
      have hzeroM : ∀ r : Fin m, row ≤ r.1 → M r j = 0 := by
        intro r hr'
        by_cases hjb : j.1 < bound
        · exact hstate.cols_lt_bound_zero r hr' j hjb
        · have hjc : col ≤ j.1 := by
            have hb : bound ≤ j.1 := le_of_not_gt hjb
            exact le_trans hstate.col_le hb
          exact checkPivot_some_minimal (M := M) row col h j hjc (by simpa using hjlt) r hr'
      have hm1r : m1 r j = 0 := by
        by_cases hpr : pr.1 = row
        · simp [m1, hpr, hzeroM r hr_ge]
        · by_cases hrpr : r = pr
          · have hnepr : pr ≠ rowFin := by
              intro hEq
              exact hpr (by simpa using congrArg Fin.val hEq)
            simp [m1, hpr, swapRow, of_apply, hrpr, hnepr,
              hzeroM rowFin (Nat.le_refl _)]
          · simp [m1, hpr, swapRow, of_apply, hrpr, hrrow, hzeroM r hr_ge]
      calc
        m3 r j = m1 r j := by
          simpa [m3, eliminateColCore] using
            (eliminateCol_go_preserves_col (cur := m1) (pivotRow := rowFin)
              (pivotCol := pc) (r := row) (steps := List.nil) (j := j)
              (hzero := hzero_left_m1 j hjlt') r)
        _ = 0 := hm1r
  | inr hjEq =>
      have hjeq : j = pc := Fin.ext (by simpa using hjEq)
      simpa [m3, hjeq] using
        eliminateCol_below_pivotCol_zero (M := m1) (pivotRow := rowFin)
          (pivotCol := pc) hneq r hr

private lemma step_pivot_one
    (M : Matrix (Fin m) (Fin n) R) (row col bound : Nat)
    (pivs : ∀ i : Fin m, i.1 < row → Fin n)
    (hstate : EchelonState (M := M) row col bound pivs)
    (hrow : row < m) {pr : Fin m} {pc : Fin n}
    (hbound : bound ≤ pc.1) (hpr_ge : row ≤ pr.1) :
    let m1 := if pr.1 = row then M else swapRow M ⟨row, hrow⟩ pr
    let pivotVal : R := m1 ⟨row, hrow⟩ pc
    let m2 := if pivotVal = 1 then m1 else factor m1 ⟨row, hrow⟩ (pivotVal)⁻¹
    let m3 := eliminateColM m2 ⟨row, hrow⟩ pc
    (∀ j : Fin n, j < pc → m1 ⟨row, hrow⟩ j = 0) →
    (∀ j : Fin n, j < pc → m2 ⟨row, hrow⟩ j = 0) →
    (∀ j : Fin n, m3 ⟨row, hrow⟩ j = m2 ⟨row, hrow⟩ j) →
    m2 ⟨row, hrow⟩ pc = 1 →
    ∀ i : Fin m, ∀ hi : i.1 < row + 1, m3 i ((extendPivs row pivs pc) i hi) = 1 := by
  intro m1 pivotVal m2 m3 hzero_left_m1 hzero_left_m2 hrow_unchanged h1 i hi
  by_cases hlt : i.1 < row
  · have hp : M i (pivs i hlt) = 1 := hstate.pivot_one i hlt
    have hp_lt : pivs i hlt < pc :=
      pivot_lt_newPivot (M := M) row col bound pivs hstate.toEchelonStateCore
        (pc := pc) hbound i hlt
    simpa [extendPivs, hlt] using
      (calc
        m3 i (pivs i hlt) = m2 i (pivs i hlt) := by
          simpa [m3] using
            (eliminateCol_go_preserves_col (cur := m2) (pivotRow := ⟨row, hrow⟩)
              (pivotCol := pc) (r := 0) (steps := List.nil) (j := pivs i hlt)
              (hzero := hzero_left_m2 (pivs i hlt) hp_lt) i)
        _ = m1 i (pivs i hlt) := by
          by_cases hpv : pivotVal = 1
          · simp [m2, hpv]
          · have hne : i ≠ ⟨row, hrow⟩ := by
              intro hEq
              have : i.1 = row := by simpa using congrArg Fin.val hEq
              exact (lt_irrefl _ (this ▸ hlt))
            simp [m2, hpv, factor, of_apply, hne]
        _ = M i (pivs i hlt) := by
          by_cases hpr : pr.1 = row
          · simp [m1, hpr]
          · have hne1 : i ≠ ⟨row, hrow⟩ := by
              intro hEq
              have : i.1 = row := by simpa using congrArg Fin.val hEq
              exact (lt_irrefl _ (this ▸ hlt))
            have hne2 : i ≠ pr := by
              have hltpr : i.1 < pr.1 := by omega
              intro hEq
              have : i.1 = pr.1 := by simpa using congrArg Fin.val hEq
              exact (lt_irrefl _ (this ▸ hltpr))
            simp [m1, hpr, swapRow, of_apply, hne1, hne2]
        _ = 1 := hp)
  · have hi_eq : i.1 = row := by
      have hi_le : i.1 ≤ row := by omega
      exact le_antisymm hi_le (by omega)
    have hrowi : i = ⟨row, hrow⟩ := fin_eq_of_val_eq hrow hi_eq
    subst hrowi
    have hrowpc : m3 ⟨row, hrow⟩ pc = 1 := by
      have := hrow_unchanged pc
      simpa [h1] using this
    simp [extendPivs, hrowpc]

private lemma step_pivot_col_zero
    (M : Matrix (Fin m) (Fin n) R) (row col bound : Nat)
    (pivs : ∀ i : Fin m, i.1 < row → Fin n)
    (hstate : EchelonState (M := M) row col bound pivs)
    (hrow : row < m) {pr : Fin m} {pc : Fin n}
    (hbound : bound ≤ pc.1) (hpr_ge : row ≤ pr.1) :
    let m1 := if pr.1 = row then M else swapRow M ⟨row, hrow⟩ pr
    let pivotVal : R := m1 ⟨row, hrow⟩ pc
    let m2 := if pivotVal = 1 then m1 else factor m1 ⟨row, hrow⟩ (pivotVal)⁻¹
    let m3 := eliminateColM m2 ⟨row, hrow⟩ pc
    (∀ j : Fin n, j < pc → m1 ⟨row, hrow⟩ j = 0) →
    (∀ j : Fin n, j < pc → m2 ⟨row, hrow⟩ j = 0) →
    m2 ⟨row, hrow⟩ pc = 1 →
    ∀ i : Fin m, ∀ hi : i.1 < row + 1, ∀ r : Fin m, r ≠ i →
      m3 r ((extendPivs row pivs pc) i hi) = 0 := by
  intro m1 pivotVal m2 m3 hzero_left_m1 hzero_left_m2 h1 i hi r hrne
  by_cases hlt : i.1 < row
  · have hp_lt : pivs i hlt < pc :=
      pivot_lt_newPivot (M := M) row col bound pivs hstate.toEchelonStateCore
        (pc := pc) hbound i hlt
    have hzeroM : M r (pivs i hlt) = 0 := hstate.pivot_col_zero i hlt r hrne
    have hzero_row_M : M ⟨row, hrow⟩ (pivs i hlt) = 0 := by
      have hne : (⟨row, hrow⟩ : Fin m) ≠ i := by
        intro hEq
        have : row = i.1 := by simpa using congrArg Fin.val hEq
        exact (lt_irrefl _ (this ▸ hlt))
      exact hstate.pivot_col_zero i hlt ⟨row, hrow⟩ hne
    have hzero_pr_M : M pr (pivs i hlt) = 0 := by
      have hne : pr ≠ i := by
        have hltpr : i.1 < pr.1 := by omega
        intro hEq
        have : pr.1 = i.1 := by simpa using congrArg Fin.val hEq
        exact (lt_irrefl _ (this ▸ hltpr))
      exact hstate.pivot_col_zero i hlt pr hne
    have hm1 : m1 r (pivs i hlt) = 0 := by
      by_cases hpr : pr.1 = row
      · simp [m1, hpr, hzeroM]
      · by_cases hrpr : r = pr
        · subst hrpr
          have hnerow : (r : Fin m) ≠ ⟨row, hrow⟩ := by
            intro hEq
            exact hpr (by simpa using congrArg Fin.val hEq)
          simp [m1, hpr, swapRow, of_apply, hnerow, hzero_row_M]
        · by_cases hrrow : r = ⟨row, hrow⟩
          · subst hrrow
            have hnepr : pr ≠ ⟨row, hrow⟩ := by
              intro hEq
              exact hpr (by simpa using congrArg Fin.val hEq)
            simp [m1, hpr, swapRow, of_apply, hzero_pr_M]
          · simp [m1, hpr, swapRow, of_apply, hrpr, hrrow, hzeroM]
    simpa [extendPivs, hlt] using
      (calc
        m3 r (pivs i hlt) = m2 r (pivs i hlt) := by
          simpa [m3] using
            (eliminateCol_go_preserves_col (cur := m2) (pivotRow := ⟨row, hrow⟩)
              (pivotCol := pc) (r := 0) (steps := List.nil) (j := pivs i hlt)
              (hzero := hzero_left_m2 (pivs i hlt) hp_lt) r)
        _ = 0 := by
          by_cases hpv : pivotVal = 1
          · simp [m2, hpv, hm1]
          · by_cases hrrow : r = ⟨row, hrow⟩
            · subst hrrow
              have h0 : m1 ⟨row, hrow⟩ (pivs i hlt) = 0 := hzero_left_m1 (pivs i hlt) hp_lt
              simp [m2, hpv, factor, of_apply, h0]
            · simp [m2, hpv, factor, of_apply, hrrow, hm1])
  · have hi_eq : i.1 = row := by
      have hi_le : i.1 ≤ row := by omega
      exact le_antisymm hi_le (by omega)
    have hrowi : i = ⟨row, hrow⟩ := fin_eq_of_val_eq hrow hi_eq
    subst hrowi
    have hzeror : m3 r pc = 0 := by
      simpa [m3] using
        eliminateCol_pivotCol_zero
        (M := m2)
        (pivotRow := ⟨row, hrow⟩)
        (pivotCol := pc)
        h1 r hrne
    simp [extendPivs, hzeror]

private lemma step_state
    (M : Matrix (Fin m) (Fin n) R) (row col bound : Nat)
    (pivs : ∀ i : Fin m, i.1 < row → Fin n)
    (hstate : EchelonState (M := M) row col bound pivs)
    (hrow : row < m) (_hcol : col < n)
    {pr : Fin m} {pc : Fin n} (h : checkPivot M row col = some (pr, pc)) :
    let m1 := if pr.1 = row then M else swapRow M ⟨row, hrow⟩ pr
    let pivotVal : R := m1 ⟨row, hrow⟩ pc
    let m2 := if pivotVal = 1 then m1 else factor m1 ⟨row, hrow⟩ (pivotVal)⁻¹
    let m3 := eliminateColM m2 ⟨row, hrow⟩ pc
    EchelonState (M := m3) (row := row + 1) (col := col + 1) (bound := pc.1 + 1)
      (extendPivs row pivs pc) := by
  intro m1 pivotVal m2 m3
  -- basic bounds
  have hrowle : row ≤ m := Nat.le_of_lt hrow
  have hrow1 : row + 1 ≤ m := by omega
  have hbound : bound ≤ pc.1 := pivotCol_ge_bound (M := M) row col bound pivs
    hstate.toEchelonStateCore h
  have hcolle : col ≤ pc.1 := le_trans hstate.col_le hbound
  have hbound' : pc.1 + 1 ≤ n := by omega
  -- show pivotRow ≥ row
  have hpr_ge : row ≤ pr.1 := checkPivot_some_row_ge (M := M) row col h
  -- pivot row zeros left of pc in M
  have hzero_left : ∀ j : Fin n, j < pc → M pr j = 0 :=
    pivot_row_zero_left (M := M) row col bound pivs hstate.toEchelonStateCore h
  -- show pivot row zeros left of pc in m1
  have hzero_left_m1 : ∀ j : Fin n, j < pc → m1 ⟨row, hrow⟩ j = 0 := by
    intro j hj
    by_cases hpr : pr.1 = row
    · have : pr = ⟨row, hrow⟩ := by
        ext; exact hpr
      subst this
      simp [m1, hzero_left j hj]
    · have hne : ⟨row, hrow⟩ ≠ pr := by
        intro hEq
        exact hpr (by simpa [eq_comm] using congrArg Fin.val hEq)
      -- swapRow brings pr to row
      have : m1 ⟨row, hrow⟩ j = M pr j := by
        simp [m1, hpr, swapRow, of_apply]
      simpa [this] using hzero_left j hj
  -- show pivot entry nonzero in m1
  have hneq : m1 ⟨row, hrow⟩ pc ≠ 0 := by
    by_cases hpr : pr.1 = row
    · have : pr = ⟨row, hrow⟩ := by
        ext; exact hpr
      subst this
      simpa [m1, hpr] using checkPivot_some_nonzero (M := M) row col h
    · have hne : ⟨row, hrow⟩ ≠ pr := by
        intro hEq
        exact hpr (by simpa [eq_comm] using congrArg Fin.val hEq)
      -- swapRow moves pr to row
      have : m1 ⟨row, hrow⟩ pc = M pr pc := by
        simp [m1, hpr, swapRow, of_apply]
      simpa [this] using checkPivot_some_nonzero (M := M) row col h
  -- pivot entry is 1 in m2
  have h1 : m2 ⟨row, hrow⟩ pc = 1 := by
    by_cases hpv : pivotVal = 1
    · simp [m2, hpv, pivotVal]
    · -- factor by pivotVal⁻¹
      simp [m2, hpv, pivotVal, factor, of_apply, hneq]
  -- pivot row unchanged by eliminateColM
  have hrow_unchanged : ∀ j : Fin n, m3 ⟨row, hrow⟩ j = m2 ⟨row, hrow⟩ j := by
    intro j
    -- eliminateColM skips pivotRow
    simpa [m3] using eliminateCol_pivotRow (M := m2) (pivotRow := ⟨row, hrow⟩) (pivotCol := pc) j
  -- pivot row zeros left of pc in m2
  have hzero_left_m2 : ∀ j : Fin n, j < pc → m2 ⟨row, hrow⟩ j = 0 := by
    intro j hj
    by_cases hpv : pivotVal = 1
    · simp [m2, hpv, hzero_left_m1 j hj]
    · -- factor does not change zeros
      simp [m2, hpv, factor, of_apply, hzero_left_m1 j hj]
  -- build new state
  refine mkEchelonState (M := m3) (row := row + 1) (col := col + 1) (bound := pc.1 + 1)
    (pivs := extendPivs row pivs pc)
    ?row_le
    ?bound_le
    ?col_le
    ?pivot_row
    ?pivot_strict
    ?pivot_lt_bound
    ?cols_zero
    ?pivot_one
    ?pivot_col_zero
  · exact hrow1
  · exact hbound'
  · exact Nat.succ_le_succ hcolle
  · simpa [m1, pivotVal, m2, m3] using
      (step_pivot_row (M := M) row col bound pivs hstate.toEchelonStateCore hrow
        (pr := pr) (pc := pc) hbound hpr_ge
        hzero_left_m2 hrow_unchanged h1)
  · exact
      step_pivot_strict (M := M) row col bound pivs hstate.toEchelonStateCore
        (pc := pc) hbound
  · exact
      step_pivot_lt_bound (M := M) row col bound pivs hstate.toEchelonStateCore
        (pc := pc) hbound
  · simpa [m1, pivotVal, m2, m3] using
      (step_cols_lt_bound_zero (M := M) row col bound pivs hstate.toEchelonStateCore hrow
        (pr := pr) (pc := pc) h hbound
        hzero_left_m2 h1)
  · simpa [m1, pivotVal, m2, m3] using
      (step_pivot_one (M := M) row col bound pivs hstate hrow
        (pr := pr) (pc := pc) hbound hpr_ge
        hzero_left_m1 hzero_left_m2 hrow_unchanged h1)
  · simpa [m1, pivotVal, m2, m3] using
      (step_pivot_col_zero (M := M) row col bound pivs hstate hrow
        (pr := pr) (pc := pc) hbound hpr_ge
        hzero_left_m1 hzero_left_m2 h1)

private lemma step_state_core_false
    (M : Matrix (Fin m) (Fin n) R) (row col bound : Nat)
    (pivs : ∀ i : Fin m, i.1 < row → Fin n)
    (hstate : EchelonStateCore (M := M) row col bound pivs)
    (hrow : row < m) (_hcol : col < n)
    {pr : Fin m} {pc : Fin n} (h : checkPivot M row col = some (pr, pc)) :
    let rowFin : Fin m := ⟨row, hrow⟩
    let m1 := if pr.1 = row then M else swapRow M rowFin pr
    let m3 := (eliminateColCore m1 rowFin pc List.nil false).1
    EchelonStateCore (M := m3) (row := row + 1) (col := col + 1) (bound := pc.1 + 1)
      (extendPivs row pivs pc) := by
  intro rowFin m1 m3
  have hrow1 : row + 1 ≤ m := by omega
  have hbound : bound ≤ pc.1 := pivotCol_ge_bound (M := M) row col bound pivs hstate h
  have hcolle : col ≤ pc.1 := le_trans hstate.col_le hbound
  have hbound' : pc.1 + 1 ≤ n := by omega
  have hpr_ge : row ≤ pr.1 := checkPivot_some_row_ge (M := M) row col h
  have hzero_left_m1 : ∀ j : Fin n, j < pc → m1 rowFin j = 0 := by
    intro j hj
    by_cases hpr : pr.1 = row
    · have : pr = rowFin := by
        ext
        exact hpr
      subst this
      have hzero_left := pivot_row_zero_left (M := M) row col bound pivs hstate h
      simpa [m1, hpr] using hzero_left j hj
    · have hne : rowFin ≠ pr := by
        intro hEq
        exact hpr (by simpa using (congrArg Fin.val hEq).symm)
      have hzero_left := pivot_row_zero_left (M := M) row col bound pivs hstate h
      have : m1 rowFin j = M pr j := by
        simp [m1, hpr, swapRow, of_apply]
      simpa [this] using hzero_left j hj
  have hneq : m1 rowFin pc ≠ 0 := by
    by_cases hpr : pr.1 = row
    · have : pr = rowFin := by
        ext
        exact hpr
      subst this
      simpa [m1, hpr] using checkPivot_some_nonzero (M := M) row col h
    · have : m1 rowFin pc = M pr pc := by
        simp [m1, hpr, swapRow, of_apply]
      simpa [this] using checkPivot_some_nonzero (M := M) row col h
  have hrow_unchanged : ∀ j : Fin n, m3 rowFin j = m1 rowFin j := by
    intro j
    simpa [m3] using eliminateCol_pivotRow_false (M := m1) (pivotRow := rowFin) (pivotCol := pc) j
  refine {
    row_le := hrow1
    bound_le := hbound'
    col_le := Nat.succ_le_succ hcolle
    pivot_row := ?_
    pivot_strict := ?_
    pivot_lt_bound := ?_
    cols_lt_bound_zero := ?_
  }
  · simpa [m1, m3] using
      (step_pivot_row_core (M := M) row col bound pivs hstate hrow
        (pr := pr) (pc := pc) hbound hpr_ge
        hzero_left_m1 hrow_unchanged hneq)
  · exact step_pivot_strict (M := M) row col bound pivs hstate (pc := pc) hbound
  · exact step_pivot_lt_bound (M := M) row col bound pivs hstate (pc := pc) hbound
  · simpa [m1, m3] using
      (step_cols_lt_bound_zero_core (M := M) row col bound pivs hstate hrow
        (pr := pr) (pc := pc) h hbound hzero_left_m1 hneq)

/-! Main theorem. -/

private lemma rrefAux_isReducedEchelon
    (M : Matrix (Fin m) (Fin n) R) (row col bound : Nat)
    (steps : List (RowOp m R))
    (pivs : ∀ i : Fin m, i.1 < row → Fin n)
    (hstate : EchelonState (M := M) row col bound pivs) :
    IsReducedEchelonForm (M := rrefAuxM M row col steps) := by
  -- induction on remaining rows
  have hrec :
      ∀ k (M : Matrix (Fin m) (Fin n) R) (row col bound : Nat)
        (steps : List (RowOp m R)) (pivs : ∀ i : Fin m, i.1 < row → Fin n),
        m - row = k →
        EchelonState (M := M) row col bound pivs →
        IsReducedEchelonForm (M := rrefAuxM M row col steps) := by
    intro k
    refine Nat.strongRecOn k ?_
    intro k ih M row col bound steps pivs hk hstate
    by_cases hrow : row < m
    · by_cases hcol : col < n
      · -- unfold rrefAuxM one step and analyze checkPivot
        rw [rrefAuxM, rowReductionAux.eq_1]
        simp only [hrow, hcol]
        cases hcp : checkPivot M row col with
        | none =>
            -- no pivot: remaining submatrix is zero
            have hnone : checkPivot M row col = none := hcp
            have hzero : ∀ r : Fin m, row ≤ r.1 → RowIsZero M r :=
              zero_rows_of_checkPivot_none (M := M) row col bound pivs
                hstate.toEchelonStateCore hnone
            exact reduced_of_state (M := M) row col bound pivs
              hstate.toEchelonStateCore hstate.toReducedStateExtras hzero
        | some prpc =>
            cases prpc with
            | mk pr pc =>
                -- build step state and recurse
                have hstate' := step_state (M := M) row col bound pivs hstate hrow hcol hcp
                -- compute new matrix
                let m1 := if pr.1 = row then M else swapRow M ⟨row, hrow⟩ pr
                let pivotVal : R := m1 ⟨row, hrow⟩ pc
                let m2 := if pivotVal = 1 then m1 else factor m1 ⟨row, hrow⟩ (pivotVal)⁻¹
                let m3 := eliminateColM m2 ⟨row, hrow⟩ pc
                let steps' :=
                  if pivotVal = 1 then
                    steps ++ [RowOp.swap ⟨row, hrow⟩ pr]
                  else
                    steps ++
                      [RowOp.swap ⟨row, hrow⟩ pr,
                        RowOp.factor ⟨row, hrow⟩ (pivotVal)⁻¹]
                have hklt : m - (row + 1) < k := by
                  have hlt : m - (row + 1) < m - row := by omega
                  simpa [hk] using hlt
                have helim :
                    (eliminateColCore m2 ⟨row, hrow⟩ pc steps' true).1 = m3 := by
                  simpa [m3, steps'] using
                    (eliminateCol_matrix_irrel
                      (M := m2)
                      (pivotRow := ⟨row, hrow⟩)
                      (pivotCol := pc)
                      (steps := steps'))
                simpa [m1, pivotVal, m2, m3, steps', helim] using
                  ih (m - (row + 1)) hklt
                    m3 (row + 1) (col + 1) (pc.1 + 1)
                    ((eliminateColCore m2 ⟨row, hrow⟩ pc steps' true).2)
                    (extendPivs row pivs pc) rfl hstate'
      · -- col ≥ n, so rrefAuxM returns M
        have hcol' : ¬ col < n := hcol
        rw [rrefAuxM, rowReductionAux.eq_1]
        simp only [hrow, hcol']
        have hzero : ∀ r : Fin m, row ≤ r.1 → RowIsZero M r :=
          zero_rows_of_col_ge (M := M) row col bound pivs
            hstate.toEchelonStateCore hcol'
        exact reduced_of_state (M := M) row col bound pivs
          hstate.toEchelonStateCore hstate.toReducedStateExtras hzero
    · -- row ≥ m
      have hrow' : ¬ row < m := hrow
      rw [rrefAuxM, rowReductionAux.eq_1]
      simp only [hrow']
      have hzero : ∀ r : Fin m, row ≤ r.1 → RowIsZero M r :=
        zero_rows_of_row_ge (M := M) row (by omega)
      exact reduced_of_state (M := M) row col bound pivs
        hstate.toEchelonStateCore hstate.toReducedStateExtras hzero
  exact hrec (m - row) M row col bound steps pivs rfl hstate

private lemma rrefAux_isEchelon_false
    (M : Matrix (Fin m) (Fin n) R) (row col bound : Nat)
    (steps : List (RowOp m R))
    (pivs : ∀ i : Fin m, i.1 < row → Fin n)
    (hstate : EchelonStateCore (M := M) row col bound pivs) :
    IsEchelonForm (M := (rowReductionAux M row col steps false).1) := by
  have hrec :
      ∀ k (M : Matrix (Fin m) (Fin n) R) (row col bound : Nat)
        (steps : List (RowOp m R)) (pivs : ∀ i : Fin m, i.1 < row → Fin n),
        m - row = k →
        EchelonStateCore (M := M) row col bound pivs →
        IsEchelonForm (M := (rowReductionAux M row col steps false).1) := by
    intro k
    refine Nat.strongRecOn k ?_
    intro k ih M row col bound steps pivs hk hstate
    by_cases hrow : row < m
    · by_cases hcol : col < n
      · rw [rowReductionAux, dif_pos hrow]
        simp only [hcol]
        cases hcp : checkPivot M row col with
        | none =>
            have hnone : checkPivot M row col = none := hcp
            have hzero : ∀ r : Fin m, row ≤ r.1 → RowIsZero M r :=
              zero_rows_of_checkPivot_none (M := M) row col bound pivs hstate hnone
            exact echelon_of_state (M := M) row col bound pivs hstate hzero
        | some prpc =>
            cases prpc with
            | mk pr pc =>
                have hstate' := step_state_core_false
                  (M := M) row col bound pivs hstate hrow hcol hcp
                let rowFin : Fin m := ⟨row, hrow⟩
                let steps1 : List (RowOp m R) := steps ++ [RowOp.swap rowFin pr]
                let m1 : Matrix (Fin m) (Fin n) R :=
                  if pr.1 = row then M else swapRow M rowFin pr
                let m3 : Matrix (Fin m) (Fin n) R :=
                  (eliminateColCore m1 rowFin pc List.nil false).1
                have hklt : m - (row + 1) < k := by
                  have hlt : m - (row + 1) < m - row := by omega
                  simpa [hk] using hlt
                have helim :
                    (eliminateColCore m1 rowFin pc steps1 false).1 = m3 := by
                  simpa [m3] using
                    eliminateCol_matrix_irrel_false (M := m1) (pivotRow := rowFin)
                      (pivotCol := pc) (steps := steps1)
                have hstate'' :
                    EchelonStateCore (M := (eliminateColCore m1 rowFin pc steps1 false).1)
                      (row := row + 1) (col := col + 1) (bound := pc.1 + 1)
                      (extendPivs row pivs pc) := by
                  simpa [helim] using hstate'
                simpa [rowFin, steps1, m1, m3, hcp, helim] using
                  ih (m - (row + 1)) hklt
                    ((eliminateColCore m1 rowFin pc steps1 false).1)
                    (row + 1) (col + 1) (pc.1 + 1)
                    ((eliminateColCore m1 rowFin pc steps1 false).2)
                    (extendPivs row pivs pc) rfl hstate''
      · have hcol' : ¬ col < n := hcol
        rw [rowReductionAux, dif_pos hrow]
        simp only [hcol']
        have hzero : ∀ r : Fin m, row ≤ r.1 → RowIsZero M r :=
          zero_rows_of_col_ge (M := M) row col bound pivs hstate hcol'
        exact echelon_of_state (M := M) row col bound pivs hstate hzero
    · have hrow' : ¬ row < m := hrow
      rw [rowReductionAux, dif_neg hrow']
      have hzero : ∀ r : Fin m, row ≤ r.1 → RowIsZero M r :=
        zero_rows_of_row_ge (M := M) row (by omega)
      exact echelon_of_state (M := M) row col bound pivs hstate hzero
  exact hrec (m - row) M row col bound steps pivs rfl hstate

/-! Final theorem. -/

private theorem rawReducedRowEchelonForm_isReducedEchelonForm
    (M : Matrix (Fin m) (Fin n) R) :
    IsReducedEchelonForm (M := (rawReducedRowEchelonForm M).1) := by
  classical
  have hstate : EchelonState (M := M) (row := 0) (col := 0) (bound := 0) emptyPivs :=
    initial_state (M := M)
  simpa [rawReducedRowEchelonForm] using
    (rrefAux_isReducedEchelon (M := M) (row := 0) (col := 0) (bound := 0)
      (steps := List.nil) (pivs := emptyPivs)
      (hstate := hstate))

/-- Compatibility theorem: derive REF directly from the stronger RREF result. -/
private theorem rawReducedRowEchelonForm_isEchelonForm
    (M : Matrix (Fin m) (Fin n) R) :
    IsEchelonForm (M := (rawReducedRowEchelonForm M).1) :=
  (rawReducedRowEchelonForm_isReducedEchelonForm (M := M)).echelon

private theorem rawRowEchelonForm_isEchelonForm
    (M : Matrix (Fin m) (Fin n) R) :
    IsEchelonForm (M := (rawRowEchelonForm M).1) := by
  have hcore : EchelonStateCore (M := M) (row := 0) (col := 0) (bound := 0) emptyPivs :=
    (initial_state (M := M)).toEchelonStateCore
  simpa [rawRowEchelonForm] using
    (rrefAux_isEchelon_false (M := M) (row := 0) (col := 0) (bound := 0)
      (steps := List.nil) (pivs := emptyPivs) (hstate := hcore))

theorem reducedRowEchelonForm_isReducedEchelonForm
    (M : Matrix (Fin m) (Fin n) R) :
    IsReducedEchelonForm (M := (Matrix.reducedRowEchelonForm M).matrix) := by
  simpa [Matrix.reducedRowEchelonForm] using
    rawReducedRowEchelonForm_isReducedEchelonForm (M := M)

theorem reducedRowEchelonForm_isEchelonForm
    (M : Matrix (Fin m) (Fin n) R) :
    IsEchelonForm (M := (Matrix.reducedRowEchelonForm M).matrix) := by
  simpa [Matrix.reducedRowEchelonForm] using
    rawReducedRowEchelonForm_isEchelonForm (M := M)

theorem rowEchelonForm_isEchelonForm
    (M : Matrix (Fin m) (Fin n) R) :
    IsEchelonForm (M := (Matrix.rowEchelonForm M).matrix) := by
  simpa [Matrix.rowEchelonForm] using rawRowEchelonForm_isEchelonForm (M := M)


/-! ## Row-operation certificates and execution log theorems -/

variable {R : Type} [Field R]
variable {a b : Nat}

set_option linter.style.longLine false

omit [Field R] in
private lemma swapRow_self (M : Matrix (Fin a) (Fin b) R) (r : Fin a) :
    swapRow M r r = M := by
  ext i j
  by_cases h : i = r
  · simp [swapRow, h]
  · simp [swapRow, h]

private lemma factor_one (M : Matrix (Fin a) (Fin b) R) (r : Fin a) :
    factor M r 1 = M := by
  ext i j
  by_cases h : i = r
  · simp [factor, h]
  · simp [factor]

/- Multiplying a matrix by an invertible matrix does not change its solution set -/
lemma mul_by_inv (A : Matrix (Fin a) (Fin a) R) (A_inv : Matrix (Fin a) (Fin a) R)
    (hA : A_inv * A = (1 : Matrix (Fin a) (Fin a) R))
    (M : Matrix (Fin a) (Fin b) R) (x : Matrix (Fin b) (Fin 1) R) :
    A * (M * x) = 0 ↔ M * x = 0 := by
  constructor
  · intro h
    -- apply A on the left to both sides of the equality (⅟A * M * x = 0)
    have h1 : A_inv * (A * (M * x)) = A_inv * (0 : Matrix (Fin a) (Fin 1) R) := by rw [h]
    -- reassociate so we can see (A * ⅟A) * (M * x)
    rw [←Matrix.mul_assoc] at h1
    -- use invertibility: A * ⅟A = 1
    rw [hA] at h1
    -- finish: 1 * (M * x) = M * x and A * 0 = 0
    simpa only [Matrix.one_mul, Matrix.mul_zero] using h1
  · intro h
    -- if M * x = 0, then (⅟A) * (M * x) = (⅟A) * 0 = 0
    rw [h, Matrix.mul_zero]

variable [DecidableEq R]

/- Applying each row operation does not change the matrix's solution set -/
def swap_proof {x : Matrix (Fin b) (Fin 1) R}
    (M : Matrix (Fin a) (Fin b) R) (r₁ r₂ : Fin a)
    : (swapRow M r₁ r₂) * x = 0 ↔ M * x = 0 := by
  -- Define A_inv and hA for mul_by_inv
  let A_inv : Matrix (Fin a) (Fin a) R := swapRow 1 r₁ r₂
  have hA : A_inv * (swapRow 1 r₁ r₂) = 1 := by
    rw [← swap_matrix_eq_elem_mul_matrix, swap_inv]
  rw [swap_matrix_eq_elem_mul_matrix, Matrix.mul_assoc]
  exact mul_by_inv _ A_inv hA M x

def factor_proof {x : Matrix (Fin b) (Fin 1) R} (M : Matrix (Fin a) (Fin b) R) (i : Fin a) (j : R)
    (hj : j ≠ 0)
    : (factor M i j) * x = 0 ↔ M * x = 0 := by
  let A_inv : Matrix (Fin a) (Fin a) R := factor 1 i j⁻¹
  have hA : A_inv * (factor 1 i j) = (1 : Matrix (Fin a) (Fin a) R) := by
    rw [← factor_matrix_eq_elem_mul_matrix, factor_inv]
    exact hj
  rw [factor_matrix_eq_elem_mul_matrix, Matrix.mul_assoc]
  exact mul_by_inv _ A_inv hA M x

def replace_proof {x : Matrix (Fin b) (Fin 1) R} (M : Matrix (Fin a) (Fin b) R)
    (use toReplace : Fin a) (k : R) (h : use ≠ toReplace)
    : (replace M use toReplace k) * x = 0 ↔ M * x = 0 := by
    let A_inv : Matrix (Fin a) (Fin a) R := replace 1 use toReplace (-k)
    have hA : A_inv * (replace 1 use toReplace k) = (1 : Matrix (Fin a) (Fin a) R) := by
      rw [← replace_matrix_eq_elem_mul_matrix, replace_inv]
      exact h
    rw [replace_matrix_eq_elem_mul_matrix, Matrix.mul_assoc]
    exact mul_by_inv _ A_inv hA M x

private lemma eliminateColLoopAux_eq
    (pivotRow : Fin a) (pivotCol : Fin b) (pivotVal : R) (r : Nat)
    (M : Matrix (Fin a) (Fin b) R) (steps : List (RowOp a R))
    (hpivot : M pivotRow pivotCol = pivotVal) :
    eliminateColLoopAux pivotRow pivotCol pivotVal r M steps =
      eliminateColLoop pivotRow pivotCol r M steps := by
  simp [eliminateColLoop, hpivot]

def eliminate_proof_helper (r : Fin a) (c : Fin b) (row : Nat) (M : Matrix (Fin a) (Fin b) R)
    (x : Matrix (Fin b) (Fin 1) R) (steps : List (RowOp a R)) (reduced : Bool)
    : (eliminateColLoop r c row M steps).1 * x = 0 ↔ M * x = 0 := by
  rw [eliminateColLoop, eliminateColLoopAux]
  split_ifs with hrow
  · simp only [ne_eq, List.concat_eq_append, ite_not, dite_eq_ite]
    split_ifs with hEq hcoeff
    · simpa [eliminateColLoopAux_eq (pivotRow := r) (pivotCol := c) (pivotVal := M r c)
        (r := row + 1) (M := M) (steps := steps) rfl] using
        eliminate_proof_helper r c (row + 1) M x steps reduced
    · simpa [eliminateColLoopAux_eq (pivotRow := r) (pivotCol := c) (pivotVal := M r c)
        (r := row + 1) (M := M) (steps := steps) rfl] using
        eliminate_proof_helper r c (row + 1) M x steps reduced
    · let i : Fin a := ⟨row, hrow⟩
      let M' := replace M r i (-M i c / M r c)
      let steps' := List.concat steps (.replace r i (-M i c / M r c))
      have huse : r ≠ i := by
        push Not at hEq
        exact hEq.symm
      have hpivot' : M' r c = M r c := by
        simp [M', replace, huse, of_apply]
      have hrec :
          (eliminateColLoop r c (row + 1) M' steps').1 * x = 0 ↔ M' * x = 0 := by
        simpa [M', steps'] using eliminate_proof_helper r c (row + 1) M' x steps' reduced
      have hrec' :
          (eliminateColLoopAux r c (M r c) (row + 1) M' steps').1 * x = 0 ↔ M' * x = 0 := by
        simpa [eliminateColLoopAux_eq (pivotRow := r) (pivotCol := c) (pivotVal := M r c)
          (r := row + 1) (M := M') (steps := steps') hpivot'] using hrec
      have hrec'' :
          (eliminateColLoopAux r c (M r c) (row + 1)
              (replace M r ⟨row, hrow⟩ (-M ⟨row, hrow⟩ c / M r c))
              (steps ++ [RowOp.replace r ⟨row, hrow⟩ (-M ⟨row, hrow⟩ c / M r c)])).1 * x = 0 ↔
            M' * x = 0 := by
        simpa [i, M', steps'] using hrec'
      rw [hrec'', replace_proof]
      exact huse
  · rfl

def eliminate_proof {x : Matrix (Fin b) (Fin 1) R} (M : Matrix (Fin a) (Fin b) R)
    (r : Fin a) (c : Fin b) (steps : List (RowOp a R)) (reduced : Bool)
    : (eliminateColCore M r c steps reduced).1 * x = 0 ↔ M * x = 0 := by
  rw [eliminateColCore]
  split
  · exact eliminate_proof_helper r c 0 M x steps reduced
  · exact eliminate_proof_helper r c (↑r) M x steps reduced

/- Gaussian elimination does not change the matrix's solution set -/
def rref_proof_helper (M : Matrix (Fin a) (Fin b) R) (r c : Nat) (x : Matrix (Fin b) (Fin 1) R)
    (steps : List (RowOp a R)) (reduced : Bool)
    : (rowReductionAux M r c steps reduced).1 * x = 0 ↔ M * x = 0 := by
  rw [rowReductionAux]
  split_ifs with h1 h2
  · simp only [List.concat_eq_append, List.append_assoc, List.cons_append, List.nil_append]
    split
    · rfl
    rw [rref_proof_helper, eliminate_proof]
    split_ifs with h3 h4 h5
    · rfl
    · rw [factor_proof]
      rename_i pivotRow pivotCol heq
      have hr : pivotRow = ⟨r, h1⟩ := by
        ext
        exact h3
      rw [← hr]
      rw [ne_eq, inv_eq_iff_eq_inv, _root_.inv_zero]
      exact checkPivot_some_nonzero (M := M) r c heq
    · rw [swap_proof]
    rw [factor_proof, swap_proof]
    rename_i pivotRow pivotCol heq
    rw [swapRow, of_apply]
    split_ifs with h6 h7
    · rw [ne_eq, inv_eq_iff_eq_inv, _root_.inv_zero]
      exact checkPivot_some_nonzero (M := M) r c heq
    · rw [h7]
      rw [ne_eq, inv_eq_iff_eq_inv, _root_.inv_zero]
      exact checkPivot_some_nonzero (M := M) r c heq
    · contradiction
  · rfl
  rfl

def ref_proof (M : Matrix (Fin a) (Fin b) R) (x : Matrix (Fin b) (Fin 1) R)
    : (rawRowEchelonForm M).1 * x = 0 ↔ M * x = 0 := by
  rw [rawRowEchelonForm]
  exact rref_proof_helper M 0 0 x List.nil false

def rref_proof (M : Matrix (Fin a) (Fin b) R) (x : Matrix (Fin b) (Fin 1) R)
    : (rawReducedRowEchelonForm M).1 * x = 0 ↔ M * x = 0 := by
  rw [rawReducedRowEchelonForm]
  exact rref_proof_helper M 0 0 x List.nil true

-- Length of steps list does not decrease after an iteration of Gaussian elimination algorithm

def elim_col_go_adds_steps_helper (pivotRow : Fin a) (pivotCol : Fin b) (r : Nat)
    (M : Matrix (Fin a) (Fin b) R) (steps : List (RowOp a R))
    : (eliminateColLoop pivotRow pivotCol r M steps).2.length ≥ steps.length := by
  rw [eliminateColLoop, eliminateColLoopAux]
  split_ifs with hrow
  · simp only [ne_eq, List.concat_eq_append, ite_not, dite_eq_ite]
    split_ifs with hEq hcoeff
    · simpa [eliminateColLoopAux_eq (pivotRow := pivotRow) (pivotCol := pivotCol)
        (pivotVal := M pivotRow pivotCol) (r := r + 1) (M := M) (steps := steps) rfl] using
        elim_col_go_adds_steps_helper pivotRow pivotCol (r + 1) M steps
    · simpa [eliminateColLoopAux_eq (pivotRow := pivotRow) (pivotCol := pivotCol)
        (pivotVal := M pivotRow pivotCol) (r := r + 1) (M := M) (steps := steps) rfl] using
        elim_col_go_adds_steps_helper pivotRow pivotCol (r + 1) M steps
    · let i : Fin a := ⟨r, hrow⟩
      let M' := replace M pivotRow i (-M i pivotCol / M pivotRow pivotCol)
      let steps' := steps ++ [RowOp.replace pivotRow i (-M i pivotCol / M pivotRow pivotCol)]
      have huse : pivotRow ≠ i := by
        push Not at hEq
        exact hEq.symm
      have hpivot' : M' pivotRow pivotCol = M pivotRow pivotCol := by
        simp [M', replace, huse, of_apply]
      have hrec :
          (eliminateColLoop pivotRow pivotCol (r + 1) M' steps').2.length ≥ steps'.length := by
        simpa [M', steps'] using
          elim_col_go_adds_steps_helper pivotRow pivotCol (r + 1) M' steps'
      have hrec' :
          (eliminateColLoopAux pivotRow pivotCol (M pivotRow pivotCol) (r + 1) M' steps').2.length ≥
            steps'.length := by
        simpa [eliminateColLoopAux_eq (pivotRow := pivotRow) (pivotCol := pivotCol)
          (pivotVal := M pivotRow pivotCol) (r := r + 1) (M := M') (steps := steps') hpivot'] using hrec
      trans steps'.length
      · exact hrec'
      · aesop
  · simp

lemma elim_col_go_adds_steps (pivotRow : Fin a) (pivotCol : Fin b) (r : Nat)
    (M : Matrix (Fin a) (Fin b) R) (l1 l2 : List (RowOp a R))
    : (eliminateColLoop pivotRow pivotCol r M (l1 ++ l2)).2.length ≥ l1.length := by
  trans (l1 ++ l2).length
  · exact elim_col_go_adds_steps_helper pivotRow pivotCol r M (l1 ++ l2)
  · aesop

lemma elim_col_adds_steps (M : Matrix (Fin a) (Fin b) R) (pivotRow : Fin a) (pivotCol : Fin b)
    (l1 l2 : List (RowOp a R)) (reduced : Bool)
    : (eliminateColCore M pivotRow pivotCol (l1 ++ l2) reduced).2.length ≥ l1.length := by
  rw [eliminateColCore]
  split_ifs
  · exact elim_col_go_adds_steps pivotRow pivotCol 0 M l1 l2
  · exact elim_col_go_adds_steps pivotRow pivotCol (↑pivotRow) M l1 l2

theorem row_reduction_adds_steps (M : Matrix (Fin a) (Fin b) R) (r c : Nat)
    (steps : List (RowOp a R)) (reduced : Bool)
    : (rowReductionAux M r c steps reduced).2.length >= steps.length := by
  rw [rowReductionAux]
  split_ifs with hrow hcol
  · cases hcp : checkPivot M r c with
    | none =>
        simpa only [hcp] using (show steps.length ≥ steps.length from le_rfl)
    | some p =>
        rcases p with ⟨pivotRow, pivotCol⟩
        simp only [List.concat_eq_append, List.append_assoc]
        split_ifs with hswap hpivot
        · let rowFin : Fin a := ⟨r, hrow⟩
          let res := eliminateColCore M rowFin pivotCol
            (steps ++ [RowOp.swap rowFin pivotRow])
            reduced
          trans res.2.length
          · exact row_reduction_adds_steps res.1 (r + 1) (c + 1) res.2 reduced
          · unfold res
            exact elim_col_adds_steps M rowFin pivotCol steps [RowOp.swap rowFin pivotRow] reduced
        · let rowFin : Fin a := ⟨r, hrow⟩
          let res := eliminateColCore (factor M rowFin (M rowFin pivotCol)⁻¹) rowFin pivotCol
            (steps ++
              ([RowOp.swap rowFin pivotRow] ++ [RowOp.factor rowFin (M rowFin pivotCol)⁻¹]))
            reduced
          trans res.2.length
          · exact row_reduction_adds_steps res.1 (r + 1) (c + 1) res.2 reduced
          · unfold res
            exact elim_col_adds_steps (factor M rowFin (M rowFin pivotCol)⁻¹) rowFin pivotCol
              steps
              ([RowOp.swap rowFin pivotRow] ++ [RowOp.factor rowFin (M rowFin pivotCol)⁻¹])
              reduced
        · let rowFin : Fin a := ⟨r, hrow⟩
          let res := eliminateColCore (swapRow M rowFin pivotRow) rowFin pivotCol
            (steps ++ [RowOp.swap rowFin pivotRow])
            reduced
          trans res.2.length
          · exact row_reduction_adds_steps res.1 (r + 1) (c + 1) res.2 reduced
          · unfold res
            exact elim_col_adds_steps (swapRow M rowFin pivotRow) rowFin pivotCol steps
              [RowOp.swap rowFin pivotRow] reduced
        · let rowFin : Fin a := ⟨r, hrow⟩
          let swapped := swapRow M rowFin pivotRow
          let res := eliminateColCore (factor swapped rowFin (swapped rowFin pivotCol)⁻¹) rowFin
            pivotCol
            (steps ++
              ([RowOp.swap rowFin pivotRow] ++ [RowOp.factor rowFin (swapped rowFin pivotCol)⁻¹]))
            reduced
          trans res.2.length
          · exact row_reduction_adds_steps res.1 (r + 1) (c + 1) res.2 reduced
          · unfold res
            exact elim_col_adds_steps
              (factor swapped rowFin (swapped rowFin pivotCol)⁻¹) rowFin pivotCol steps
              ([RowOp.swap rowFin pivotRow] ++
                [RowOp.factor rowFin (swapped rowFin pivotCol)⁻¹])
              reduced
  · exact le_rfl
  · exact le_rfl

-- Proof that we can apply the steps in the steps list to the original matrix to get its row
-- echelon form

private theorem eliminateCol_go_log_correct
    (pivotRow : Fin a) (pivotCol : Fin b) (r : Nat)
    (M : Matrix (Fin a) (Fin b) R) (steps : List (RowOp a R)) :
    ∃ ops_tail : List (RowOp a R),
      eliminateColLoop pivotRow pivotCol r M steps =
        (ops_tail.foldl applyRowOp M, steps ++ ops_tail) := by
  have hrec :
      ∀ k (r : Nat) (M : Matrix (Fin a) (Fin b) R) (steps : List (RowOp a R)),
        a - r = k →
          ∃ ops_tail : List (RowOp a R),
            eliminateColLoop pivotRow pivotCol r M steps =
              (ops_tail.foldl applyRowOp M, steps ++ ops_tail) := by
    intro k
    induction k with
    | zero =>
        intro r M steps hk
        have hr : a ≤ r := Nat.le_of_sub_eq_zero hk
        refine ⟨[], ?_⟩
        rw [eliminateColLoop, eliminateColLoopAux, dif_neg (not_lt_of_ge hr)]
        simp
    | succ k ih =>
        intro r M steps hk
        have hr : r < a := by omega
        have hk' : a - (r + 1) = k := by omega
        let i : Fin a := ⟨r, hr⟩
        rw [eliminateColLoop, eliminateColLoopAux, dif_pos hr]
        by_cases hEq : i = pivotRow
        · obtain ⟨ops_tail, htail⟩ := ih (r + 1) M steps hk'
          exact ⟨ops_tail, by simpa [i, hEq, dite_eq_ite] using htail⟩
        · by_cases hcoeff : M i pivotCol ≠ 0
          · let op : RowOp a R := .replace pivotRow i (-M i pivotCol / M pivotRow pivotCol)
            let M' := replace M pivotRow i (-M i pivotCol / M pivotRow pivotCol)
            let steps' := steps ++ [op]
            have huse : pivotRow ≠ i := by
              intro hpr
              exact hEq hpr.symm
            have hpivot' : M' pivotRow pivotCol = M pivotRow pivotCol := by
              simp [M', replace, huse, of_apply]
            obtain ⟨ops_tail, htail⟩ := ih (r + 1) M' steps' hk'
            refine ⟨op :: ops_tail, ?_⟩
            simpa [i, hEq, hcoeff, op, M', steps', List.foldl_append, List.append_assoc,
              applyRowOp, dite_eq_ite, eliminateColLoopAux_eq (pivotRow := pivotRow)
              (pivotCol := pivotCol) (pivotVal := M pivotRow pivotCol) (r := r + 1)
              (M := M') (steps := steps') hpivot'] using htail
          · obtain ⟨ops_tail, htail⟩ := ih (r + 1) M steps hk'
            exact ⟨ops_tail, by
              simpa [i, hEq, hcoeff, dite_eq_ite,
                eliminateColLoopAux_eq (pivotRow := pivotRow) (pivotCol := pivotCol)
                  (pivotVal := M pivotRow pivotCol) (r := r + 1) (M := M) (steps := steps) rfl] using htail⟩
  exact hrec (a - r) r M steps rfl

private theorem eliminateCol_log_correct
    (M : Matrix (Fin a) (Fin b) R) (pivotRow : Fin a) (pivotCol : Fin b)
    (steps : List (RowOp a R)) (reduced : Bool) :
    ∃ ops_tail : List (RowOp a R),
      eliminateColCore M pivotRow pivotCol steps reduced =
        (ops_tail.foldl applyRowOp M, steps ++ ops_tail) := by
  rw [eliminateColCore]
  by_cases hred : reduced
  · simpa [hred] using eliminateCol_go_log_correct pivotRow pivotCol 0 M steps
  · simpa [hred] using eliminateCol_go_log_correct pivotRow pivotCol pivotRow.1 M steps

private theorem rrefAux_log_correct
    (M : Matrix (Fin a) (Fin b) R) (r c : Nat)
    (steps : List (RowOp a R)) (reduced : Bool) :
    ∃ ops_tail : List (RowOp a R),
      rowReductionAux M r c steps reduced =
        (ops_tail.foldl applyRowOp M, steps ++ ops_tail) := by
  have hrec :
      ∀ k (M : Matrix (Fin a) (Fin b) R) (r c : Nat)
        (steps : List (RowOp a R)) (reduced : Bool),
        a - r = k →
          ∃ ops_tail : List (RowOp a R),
            rowReductionAux M r c steps reduced =
              (ops_tail.foldl applyRowOp M, steps ++ ops_tail) := by
    intro k
    induction k with
    | zero =>
        intro M r c steps reduced hk
        have hr : a ≤ r := Nat.le_of_sub_eq_zero hk
        refine ⟨[], ?_⟩
        simp [rowReductionAux, Nat.not_lt_of_ge hr]
    | succ k ih =>
        intro M r c steps reduced hk
        have hr : r < a := by omega
        have hk' : a - (r + 1) = k := by omega
        rw [rowReductionAux, dif_pos hr]
        by_cases hc : c < b
        · rw [if_pos hc]
          cases hcp : checkPivot M r c with
          | none =>
              refine ⟨[], ?_⟩
              simp
          | some p =>
              rcases p with ⟨pivotRow, pivotCol⟩
              let rowFin : Fin a := ⟨r, hr⟩
              let swapOp : RowOp a R := .swap rowFin pivotRow
              let steps1 : List (RowOp a R) := steps ++ [swapOp]
              let m1 : Matrix (Fin a) (Fin b) R :=
                if pivotRow.1 = r then M else swapRow M rowFin pivotRow
              have hm1 : m1 = applyRowOp M swapOp := by
                by_cases hswap : pivotRow.1 = r
                · have hpiv : pivotRow = rowFin := by
                    ext
                    simpa [rowFin] using hswap
                  subst hpiv
                  simp [m1, swapOp, applyRowOp, rowFin, swapRow_self]
                · simp [m1, swapOp, applyRowOp, hswap]
              let pivotVal : R := m1 rowFin pivotCol
              let factorOp : RowOp a R := .factor rowFin pivotVal⁻¹
              cases hred : reduced with
              | false =>
                  obtain ⟨ops_elim, hElim⟩ :=
                    eliminateCol_log_correct m1 rowFin pivotCol steps1 false
                  obtain ⟨ops_rec, hRec⟩ :=
                    ih (ops_elim.foldl applyRowOp m1) (r + 1) (c + 1) (steps1 ++ ops_elim) false hk'
                  refine ⟨[swapOp] ++ ops_elim ++ ops_rec, ?_⟩
                  have hbranch :
                      (match eliminateColCore m1 rowFin pivotCol steps1 false with
                        | (m3, steps3) => rowReductionAux m3 (r + 1) (c + 1) steps3 false) =
                        (ops_rec.foldl applyRowOp (ops_elim.foldl applyRowOp m1),
                          steps1 ++ ops_elim ++ ops_rec) := by
                    simpa [hElim] using hRec
                  have hfinal :
                      (ops_rec.foldl applyRowOp (ops_elim.foldl applyRowOp m1),
                        steps1 ++ ops_elim ++ ops_rec) =
                        (List.foldl applyRowOp M ([swapOp] ++ ops_elim ++ ops_rec),
                          steps ++ ([swapOp] ++ ops_elim ++ ops_rec)) := by
                    apply Prod.ext
                    · simp only [List.cons_append, List.nil_append, List.foldl_cons,
                        List.foldl_append]
                      rw [hm1]
                    · simp [steps1, List.append_assoc]
                  simpa [hcp, rowFin, hred, steps1, m1, pivotVal, List.concat_eq_append] using
                    hbranch.trans hfinal
              | true =>
                  by_cases hpv : pivotVal = 1
                  · obtain ⟨ops_elim, hElim⟩ :=
                      eliminateCol_log_correct m1 rowFin pivotCol steps1 true
                    obtain ⟨ops_rec, hRec⟩ :=
                      ih (ops_elim.foldl applyRowOp m1) (r + 1) (c + 1) (steps1 ++ ops_elim)
                        true hk'
                    refine ⟨[swapOp] ++ ops_elim ++ ops_rec, ?_⟩
                    have hbranch :
                        (match eliminateColCore m1 rowFin pivotCol steps1 true with
                          | (m3, steps3) => rowReductionAux m3 (r + 1) (c + 1) steps3 true) =
                          (ops_rec.foldl applyRowOp (ops_elim.foldl applyRowOp m1),
                            steps1 ++ ops_elim ++ ops_rec) := by
                      simpa [hElim] using hRec
                    have hfinal :
                        (ops_rec.foldl applyRowOp (ops_elim.foldl applyRowOp m1),
                          steps1 ++ ops_elim ++ ops_rec) =
                          (List.foldl applyRowOp M ([swapOp] ++ ops_elim ++ ops_rec),
                            steps ++ ([swapOp] ++ ops_elim ++ ops_rec)) := by
                      apply Prod.ext
                      · simp only [List.cons_append, List.nil_append, List.foldl_cons,
                          List.foldl_append]
                        rw [hm1]
                      · simp [steps1, List.append_assoc]
                    simpa [hcp, rowFin, hred, hpv, steps1, m1, pivotVal, List.concat_eq_append]
                      using hbranch.trans hfinal
                  · let steps2 : List (RowOp a R) := steps1 ++ [factorOp]
                    let m2 : Matrix (Fin a) (Fin b) R := factor m1 rowFin pivotVal⁻¹
                    have hm2 : m2 = applyRowOp m1 factorOp := by
                      simp [m2, factorOp, applyRowOp]
                    obtain ⟨ops_elim, hElim⟩ :=
                      eliminateCol_log_correct m2 rowFin pivotCol steps2 true
                    obtain ⟨ops_rec, hRec⟩ :=
                      ih (ops_elim.foldl applyRowOp m2) (r + 1) (c + 1) (steps2 ++ ops_elim)
                        true hk'
                    refine ⟨[swapOp, factorOp] ++ ops_elim ++ ops_rec, ?_⟩
                    have hbranch :
                        (match eliminateColCore m2 rowFin pivotCol steps2 true with
                          | (m3, steps3) => rowReductionAux m3 (r + 1) (c + 1) steps3 true) =
                          (ops_rec.foldl applyRowOp (ops_elim.foldl applyRowOp m2),
                            steps2 ++ ops_elim ++ ops_rec) := by
                      simpa [hElim] using hRec
                    have hfinal :
                        (ops_rec.foldl applyRowOp (ops_elim.foldl applyRowOp m2),
                          steps2 ++ ops_elim ++ ops_rec) =
                          (List.foldl applyRowOp M ([swapOp, factorOp] ++ ops_elim ++ ops_rec),
                            steps ++ ([swapOp, factorOp] ++ ops_elim ++ ops_rec)) := by
                      apply Prod.ext
                      · simp only [List.cons_append, List.nil_append, List.foldl_cons,
                          List.foldl_append]
                        rw [hm2, hm1]
                      · simp [steps1, steps2, List.append_assoc]
                    simpa [hcp, rowFin, hred, hpv, steps1, m1, pivotVal, steps2, m2,
                      List.concat_eq_append] using hbranch.trans hfinal
        · refine ⟨[], ?_⟩
          simp [hc]
  exact hrec (a - r) M r c steps reduced rfl

lemma empty_list_iff_no_change (M M' : Matrix (Fin a) (Fin b) R) (r c : Nat)
    (ops : List (RowOp a R)) (reduced : Bool)
    : rowReductionAux M r c ops reduced = (M', []) → M = M' := by
  intro h
  obtain ⟨ops_tail, hlog⟩ := rrefAux_log_correct M r c ops reduced
  rw [hlog] at h
  injection h with hM hOps
  have hnil : ops_tail = [] := (List.eq_nil_of_append_eq_nil hOps).2
  simpa [hnil] using hM

theorem steps_helper (M M' : Matrix (Fin a) (Fin b) R) (r c : Nat)
    (ops_head ops_tail ops_final : List (RowOp a R)) (reduced : Bool)
    (h_ops : ops_final = ops_head ++ ops_tail)
    : rowReductionAux M r c ops_head reduced = (M', ops_head ++ ops_tail) →
        ops_tail.foldl applyRowOp M = M' := by
  intro h
  have h' : rowReductionAux M r c ops_head reduced = (M', ops_final) := by
    simpa [h_ops] using h
  obtain ⟨ops_tail', hlog⟩ := rrefAux_log_correct M r c ops_head reduced
  rw [hlog] at h'
  injection h' with hM hOps
  have hOps' : ops_head ++ ops_tail' = ops_head ++ ops_tail := by
    simpa [h_ops] using hOps
  have htail : ops_tail' = ops_tail := (List.append_right_inj ops_head).mp hOps'
  simpa [htail] using hM

private theorem rawRowEchelonForm_steps (M M' : Matrix (Fin a) (Fin b) R) (ops : List (RowOp a R))
    : rawRowEchelonForm M = (M', ops) → ops.foldl applyRowOp M = M' := by
  intro h
  have h_ops : ops = [] ++ ops := by simp
  have h' : rowReductionAux M 0 0 [] false = (M', [] ++ ops) := by
    simpa [rawRowEchelonForm]
  simpa using steps_helper M M' 0 0 [] ops ops false h_ops h'

private theorem rawReducedRowEchelonForm_steps (M M' : Matrix (Fin a) (Fin b) R)
    (ops : List (RowOp a R))
    : rawReducedRowEchelonForm M = (M', ops) → ops.foldl applyRowOp M = M' := by
  intro h
  have h_ops : ops = [] ++ ops := by simp
  have h' : rowReductionAux M 0 0 [] true = (M', [] ++ ops) := by
    simpa [rawReducedRowEchelonForm]
  simpa using steps_helper M M' 0 0 [] ops ops true h_ops h'

theorem rowEchelonForm_steps
    (M : Matrix (Fin a) (Fin b) R) :
    (Matrix.rowEchelonForm M).steps.foldl applyRowOp M = (Matrix.rowEchelonForm M).matrix := by
  simpa [Matrix.rowEchelonForm] using
    (rawRowEchelonForm_steps
      (M := M)
      (M' := (rawRowEchelonForm M).1)
      (ops := (rawRowEchelonForm M).2)
      rfl)

theorem reducedRowEchelonForm_steps
    (M : Matrix (Fin a) (Fin b) R) :
    (Matrix.reducedRowEchelonForm M).steps.foldl applyRowOp M =
      (Matrix.reducedRowEchelonForm M).matrix := by
  simpa [Matrix.reducedRowEchelonForm] using
    (rawReducedRowEchelonForm_steps
      (M := M)
      (M' := (rawReducedRowEchelonForm M).1)
      (ops := (rawReducedRowEchelonForm M).2)
      rfl)
end Matrix
