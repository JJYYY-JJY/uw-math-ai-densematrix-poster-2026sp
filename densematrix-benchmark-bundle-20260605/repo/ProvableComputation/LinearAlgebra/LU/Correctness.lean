import ProvableComputation.LinearAlgebra.GaussianElimination.Elementary
import ProvableComputation.LinearAlgebra.GaussianElimination.RrefCorrectness
import ProvableComputation.LinearAlgebra.LU.Basic

/-!
This file proves the correctness properties of the bookkeeping layer used by
`LUFactorizationInternal.rawFactorization`. The row-echelon algorithm records
a list of elementary row operations, and
`LUFactorizationInternal.buildPLFromSteps` reconstructs from that log a
permutation matrix `P` and a unit lower-triangular matrix `L`.

The proofs below show three things:
1. every recorded row operation is invertible in the cases that arise from the
   elimination algorithm;
2. the reconstructed product `P * L` exactly cancels the accumulated row
   operations, so `P * L * U = M`;
3. the reconstructed factors have the expected structural properties:
   `P` is orthogonal, `U` is in echelon form, and `L` is unit lower triangular.
-/

variable {R : Type} [Field R] [DecidableEq R]
variable {a : Nat} {b : Nat}

open ColumnElementary
open LUFactorizationInternal
open Matrix

set_option linter.style.longLine false

/-! ## Invertible row operations and explicit inverses -/

/- `InvertibleRowOp` isolates the side conditions under which a row operation
can be undone. Swaps are always invertible, scalings require a nonzero factor,
and the degenerate replacement `use = toReplace` is really a scaling by
`k + 1`, so that quantity must be nonzero. -/
private def InvertibleRowOp (op : RowOp a R) : Prop :=
  match op with
  | .swap _ _ => True
  | .factor _ c => c ≠ 0
  | .replace use toReplace k =>
      if use = toReplace then k + 1 ≠ 0 else True

/- `inverseRowOp` writes down the elementary operation that reverses `op`.
The only subtle branch is `replace use use k`, which acts as multiplication by
`k + 1` on a single row and is therefore inverted by a `factor`. -/
private def inverseRowOp (op : RowOp a R) : RowOp a R :=
  match op with
  | .swap i j => .swap i j
  | .factor i c => .factor i c⁻¹
  | .replace use toReplace k =>
      if use = toReplace then
        .factor toReplace (k + 1)⁻¹
      else
        .replace use toReplace (-k)

/-
These simp lemmas expose the concrete inverse for the easy constructor cases so
later proofs can normalize without reopening the definition manually.
-/
omit [DecidableEq R] in
/- Swapping twice is its own inverse, so the inverse operation is definitionally
the same swap. -/
@[simp] private lemma inverseRowOp_swap (i j : Fin a) :
    inverseRowOp (R := R) (.swap i j : RowOp a R) = .swap i j := rfl

omit [DecidableEq R] in
/- The inverse of a row scaling is scaling by the reciprocal. -/
@[simp] private lemma inverseRowOp_factor (i : Fin a) (c : R) :
    inverseRowOp (R := R) (.factor i c : RowOp a R) = .factor i c⁻¹ := rfl

/- Applying an operation and then its explicit inverse returns the original
matrix. This is the core local cancellation statement that all later matrix
identities reduce to. -/
omit [DecidableEq R] in
private lemma apply_inverseRowOp
    (M : Matrix (Fin a) (Fin b) R) (op : RowOp a R)
    (hop : InvertibleRowOp (R := R) op) :
    Matrix.applyRowOp (Matrix.applyRowOp M op) (inverseRowOp (R := R) op) = M := by
  cases op with
  | swap i j =>
      -- A swap is its own inverse.
      simpa [Matrix.applyRowOp, inverseRowOp] using
        swap_inv (M := M) i j
  | factor i c =>
      -- Scaling is undone by multiplying by the reciprocal.
      simpa [Matrix.applyRowOp, inverseRowOp] using
        factor_inv (M := M) (i := i) (j := c) hop
  | replace use toReplace k =>
      by_cases h : use = toReplace
      · subst h
        -- In the diagonal replacement case, the operation is just scaling by `k + 1`.
        have hk : k + 1 ≠ 0 := by
          simpa [InvertibleRowOp] using hop
        simpa [Matrix.applyRowOp, inverseRowOp, replace, factor] using
          factor_inv (M := M) (i := use) (j := k + 1) hk
      -- Off-diagonal replacement is undone by adding the opposite multiple back.
      · simpa [Matrix.applyRowOp, inverseRowOp, replace, h] using
          replace_inv (M := M) (use := use) (toReplace := toReplace) (k := k) h

/- Rephrases `apply_inverseRowOp` as left multiplication by the inverse
elementary matrix. This is the form used when manipulating matrix products. -/
omit [DecidableEq R] in
private lemma inverseRowOp_mul_applyRowOp
    (M : Matrix (Fin a) (Fin b) R) (op : RowOp a R)
    (hop : InvertibleRowOp (R := R) op) :
    Matrix.elementaryMatrixOfRowOp (inverseRowOp (R := R) op) *
      Matrix.applyRowOp M op = M := by
  rw [Matrix.elementaryMatrixOfRowOp_mul_eq_applyRowOp
    (op := inverseRowOp (R := R) op) (M := Matrix.applyRowOp M op)]
  exact apply_inverseRowOp (M := M) (op := op) hop

/- Specializes the previous lemma to the identity matrix, producing an explicit
inverse for every admissible elementary matrix. -/
omit [DecidableEq R] in
private lemma inverseRowOp_mul_elem
    (op : RowOp a R) (hop : InvertibleRowOp (R := R) op) :
    Matrix.elementaryMatrixOfRowOp (inverseRowOp (R := R) op) *
      Matrix.elementaryMatrixOfRowOp op = (1 : squareMatrix a R) := by
  simpa [Matrix.applyRowOp] using
    inverseRowOp_mul_applyRowOp
      (M := (1 : squareMatrix a R)) (op := op) hop

/-! ## The `LUFactorizationInternal.buildPLFromSteps` state product invariant -/

/- `buildPLStateProduct` is the matrix that the current bookkeeping state claims
will cancel the already-recorded row operations. The whole first half of the
file proves that this product is preserved as new operations are appended. -/
private def buildPLStateProduct
    (state : List (Fin a × Fin a) × squareMatrix a R) : squareMatrix a R :=
  permutationOfSwaps (R := R) state.1 * lowerOfSwaps (R := R) state.1 state.2

/- Expresses row-swapping as left multiplication by the corresponding
elementary matrix, so later calculations can stay purely multiplicative. -/
omit [DecidableEq R] in
private lemma swapRow_eq_elem_mul
    (M : Matrix (Fin a) (Fin b) R) (r1 r2 : Fin a) :
    swapRow M r1 r2 =
      Matrix.elementaryMatrixOfRowOp (.swap r1 r2 : RowOp a R) * M := by
  simpa [Matrix.applyRowOp] using
    (Matrix.elementaryMatrixOfRowOp_mul_eq_applyRowOp
      (op := (.swap r1 r2 : RowOp a R)) (M := M)).symm

/- Swapping rows commutes with right multiplication: swapping `X * Y` is the
same as swapping `X` first and then multiplying by `Y`. -/
omit [DecidableEq R] in
private lemma swapRow_mul
    (X : squareMatrix a R) (Y : Matrix (Fin a) (Fin b) R) (r1 r2 : Fin a) :
    swapRow (X * Y) r1 r2 = swapRow X r1 r2 * Y := by
  change Matrix.applyRowOp (X * Y) (.swap r1 r2 : RowOp a R) =
    Matrix.applyRowOp X (.swap r1 r2 : RowOp a R) * Y
  rw [← Matrix.elementaryMatrixOfRowOp_mul_eq_applyRowOp (op := (.swap r1 r2 : RowOp a R))
    (M := X * Y)]
  rw [← Matrix.elementaryMatrixOfRowOp_mul_eq_applyRowOp (op := (.swap r1 r2 : RowOp a R))
    (M := X)]
  simp [Matrix.mul_assoc]

/- Iterates the previous commutation relation through the whole list of stored
swaps. This lets us move the action of `lowerOfSwaps` across a product. -/
omit [DecidableEq R] in
private lemma foldl_swapRow_mul
    (swaps : List (Fin a × Fin a)) (X Y : squareMatrix a R) :
    swaps.foldl (fun acc ij => swapRow acc ij.1 ij.2) (X * Y) =
      (swaps.foldl (fun acc ij => swapRow acc ij.1 ij.2) X) * Y := by
  induction swaps generalizing X with
  | nil =>
      simp
  | cons ij swaps ih =>
      simp [ih, swapRow_mul]

/- `lowerOfSwaps` commutes with the column swap inserted into the inverse-state
matrix by `buildPLStep` when the current row operation is a swap. -/
omit [DecidableEq R] in
private lemma lowerOfSwaps_swapCol
    (swaps : List (Fin a × Fin a)) (M : squareMatrix a R) (i j : Fin a) :
    lowerOfSwaps (R := R) swaps (swapCol M i j) =
      swapCol (lowerOfSwaps (R := R) swaps M) i j := by
  unfold lowerOfSwaps
  rw [swapCol_eq_mul_elem, foldl_swapRow_mul, swapCol_eq_mul_elem]

/- The same commutation fact for column replacement, used in the replacement
branch of `buildPLStep`. -/
omit [DecidableEq R] in
private lemma lowerOfSwaps_replaceCol
    (swaps : List (Fin a × Fin a)) (M : squareMatrix a R)
    (use toReplace : Fin a) (k : R) :
    lowerOfSwaps (R := R) swaps (replaceCol M use toReplace k) =
      replaceCol (lowerOfSwaps (R := R) swaps M) use toReplace k := by
  unfold lowerOfSwaps
  rw [replaceCol_eq_mul_elem, foldl_swapRow_mul, replaceCol_eq_mul_elem]

/- Handles the swap case of the state invariant. The proof expands the updated
state, rewrites every swap as multiplication by the swap matrix `S`, and then
uses `S * S = 1` to cancel the new operation. -/
omit [DecidableEq R] in
private lemma buildPLStep_stateProduct_swap
    (state : List (Fin a × Fin a) × squareMatrix a R)
    (M : Matrix (Fin a) (Fin b) R) (i j : Fin a) :
    buildPLStateProduct (buildPLStep (R := R) state (.swap i j)) *
      Matrix.applyRowOp M (.swap i j : RowOp a R) =
        buildPLStateProduct state * M := by
  rcases state with ⟨swaps, MInv⟩
  let P : squareMatrix a R := permutationOfSwaps (R := R) swaps
  let L : squareMatrix a R := lowerOfSwaps (R := R) swaps MInv
  let S : squareMatrix a R := Matrix.elementaryMatrixOfRowOp (.swap i j : RowOp a R)
  have hS : S * S = (1 : squareMatrix a R) := by
    simpa using inverseRowOp_mul_elem
      (R := R) (op := (.swap i j : RowOp a R)) (by trivial)
  calc
    -- First rewrite the operational semantics into the concrete `swapRow` form.
    buildPLStateProduct (buildPLStep (R := R) (swaps, MInv) (.swap i j)) *
        Matrix.applyRowOp M (.swap i j : RowOp a R)
        = buildPLStateProduct (buildPLStep (R := R) (swaps, MInv) (.swap i j)) *
            swapRow M i j := by
              simp [Matrix.applyRowOp]
    -- Then expand the updated bookkeeping state into matrix multiplication.
    _ = (P * S) * (swapRow (L * S) i j) * swapRow M i j := by
          simp [buildPLStateProduct, buildPLStep, permutationOfSwaps, lowerOfSwaps,
            P, L, S, foldl_swapRow_mul, swapCol_eq_mul_elem, Matrix.mul_assoc]
    -- Every row swap is multiplication by the same elementary matrix `S`.
    _ = (P * S) * ((S * L) * S) * (S * M) := by
          rw [swapRow_mul, swapRow_eq_elem_mul, swapRow_eq_elem_mul]
    -- Finally cancel the inserted swap matrices.
    _ = P * L * M := by
          calc
            (P * S) * ((S * L) * S) * (S * M)
                = P * (((S * S) * L) * ((S * S) * M)) := by
                    simp [Matrix.mul_assoc]
            _ = P * ((((1 : squareMatrix a R) * L)) * ((1 : squareMatrix a R) * M)) := by
                  simp [hS]
            _ = P * L * M := by simp [Matrix.mul_assoc]

/- Handles the scaling case of the invariant. `buildPLStep` stores the inverse
scaling inside the lower factor, so the proof reduces to `Finv * F = 1`. -/
omit [DecidableEq R] in
private lemma buildPLStep_stateProduct_factor
    (state : List (Fin a × Fin a) × squareMatrix a R)
    (M : Matrix (Fin a) (Fin b) R) (row : Fin a) (scale : R)
    (hop : InvertibleRowOp (R := R) (.factor row scale)) :
    buildPLStateProduct (buildPLStep (R := R) state (.factor row scale)) *
      Matrix.applyRowOp M (.factor row scale : RowOp a R) =
        buildPLStateProduct state * M := by
  rcases state with ⟨swaps, MInv⟩
  let P : squareMatrix a R := permutationOfSwaps (R := R) swaps
  let L : squareMatrix a R := lowerOfSwaps (R := R) swaps MInv
  let F : squareMatrix a R := Matrix.elementaryMatrixOfRowOp (.factor row scale : RowOp a R)
  let Finv : squareMatrix a R :=
    Matrix.elementaryMatrixOfRowOp (.factor row scale⁻¹ : RowOp a R)
  have hF : Finv * F = (1 : squareMatrix a R) := by
    simpa using inverseRowOp_mul_elem
      (R := R) (op := (.factor row scale : RowOp a R)) hop
  calc
    -- Convert the operational action into the corresponding matrix expression.
    buildPLStateProduct (buildPLStep (R := R) (swaps, MInv) (.factor row scale)) *
        Matrix.applyRowOp M (.factor row scale : RowOp a R)
        = buildPLStateProduct (buildPLStep (R := R) (swaps, MInv) (.factor row scale)) *
            factor M row scale := by
              simp [Matrix.applyRowOp]
    -- The updated state inserts the inverse scaling into the lower factor.
    _ = P * (L * Finv) * factor M row scale := by
          simp [buildPLStateProduct, buildPLStep, permutationOfSwaps, lowerOfSwaps,
            P, L, Finv, factorCol_eq_mul_elem, foldl_swapRow_mul, Matrix.mul_assoc]
    -- Rewrite the row scaling as multiplication by its elementary matrix.
    _ = P * (L * Finv) * (F * M) := by
          rw [factor_matrix_eq_elem_mul_matrix]
          simp [F, Matrix.elementaryMatrixOfRowOp]
    -- Cancel the newly inserted inverse pair.
    _ = P * L * M := by
          calc
            P * (L * Finv) * (F * M) = P * (L * (Finv * (F * M))) := by
              simp [Matrix.mul_assoc]
            _ = P * (L * ((Finv * F) * M)) := by
              simp [Matrix.mul_assoc]
            _ = P * (L * ((1 : squareMatrix a R) * M)) := by rw [hF]
            _ = P * L * M := by simp [Matrix.mul_assoc]

/- Handles the replacement case of the invariant. There are two algebraically
different branches:
* when `use = toReplace`, the row operation is really a scaling by `scale + 1`;
* otherwise it is a genuine row replacement, inverted by replacing with `-scale`.

The proof mirrors that case split and cancels the appropriate elementary
matrices in each branch. -/
omit [DecidableEq R] in
private lemma buildPLStep_stateProduct_replace
    (state : List (Fin a × Fin a) × squareMatrix a R)
    (M : Matrix (Fin a) (Fin b) R) (use toReplace : Fin a) (scale : R)
    (hop : InvertibleRowOp (R := R) (.replace use toReplace scale)) :
    buildPLStateProduct (buildPLStep (R := R) state (.replace use toReplace scale)) *
      Matrix.applyRowOp M (.replace use toReplace scale : RowOp a R) =
        buildPLStateProduct state * M := by
  rcases state with ⟨swaps, MInv⟩
  by_cases h : use = toReplace
  -- The diagonal replacement branch is really a scaling branch in disguise.
  · subst h
    let P : squareMatrix a R := permutationOfSwaps (R := R) swaps
    let L : squareMatrix a R := lowerOfSwaps (R := R) swaps MInv
    let F : squareMatrix a R :=
      Matrix.elementaryMatrixOfRowOp (.replace use use scale : RowOp a R)
    let Finv : squareMatrix a R :=
      Matrix.elementaryMatrixOfRowOp (.factor use (scale + 1)⁻¹ : RowOp a R)
    have hR : Finv * F = (1 : squareMatrix a R) := by
      simpa [Finv, F, inverseRowOp] using inverseRowOp_mul_elem
        (R := R) (op := (.replace use use scale : RowOp a R)) hop
    calc
      buildPLStateProduct (buildPLStep (R := R) (swaps, MInv) (.replace use use scale)) *
          Matrix.applyRowOp M (.replace use use scale : RowOp a R)
          = buildPLStateProduct (buildPLStep (R := R) (swaps, MInv) (.replace use use scale)) *
              replace M use use scale := by
                simp [Matrix.applyRowOp]
      _ = P * (L * Finv) * replace M use use scale := by
            simp [buildPLStateProduct, buildPLStep, permutationOfSwaps, lowerOfSwaps,
              P, L, Finv, factorCol_eq_mul_elem, foldl_swapRow_mul, Matrix.mul_assoc]
      _ = P * (L * Finv) * (F * M) := by
            rw [replace_matrix_eq_elem_mul_matrix]
            simp [F, Matrix.elementaryMatrixOfRowOp]
      _ = P * L * M := by
            calc
              P * (L * Finv) * (F * M) = P * (L * (Finv * (F * M))) := by
                simp [Matrix.mul_assoc]
              _ = P * (L * ((Finv * F) * M)) := by
                simp [Matrix.mul_assoc]
              _ = P * (L * ((1 : squareMatrix a R) * M)) := by rw [hR]
              _ = P * L * M := by simp [Matrix.mul_assoc]
  -- The genuine replacement branch cancels with the opposite replacement matrix.
  · have hR :
        Matrix.elementaryMatrixOfRowOp (.replace use toReplace (-scale) : RowOp a R) *
          Matrix.elementaryMatrixOfRowOp (.replace use toReplace scale : RowOp a R) =
            (1 : squareMatrix a R) := by
        simpa [inverseRowOp, h] using inverseRowOp_mul_elem
          (R := R) (op := (.replace use toReplace scale : RowOp a R)) hop
    let P : squareMatrix a R := permutationOfSwaps (R := R) swaps
    let L : squareMatrix a R := lowerOfSwaps (R := R) swaps MInv
    let Rinv : squareMatrix a R :=
      Matrix.elementaryMatrixOfRowOp (.replace use toReplace (-scale) : RowOp a R)
    let Rop : squareMatrix a R :=
      Matrix.elementaryMatrixOfRowOp (.replace use toReplace scale : RowOp a R)
    calc
      buildPLStateProduct
          (buildPLStep (R := R) (swaps, MInv) (.replace use toReplace scale)) *
        Matrix.applyRowOp M (.replace use toReplace scale : RowOp a R)
          = buildPLStateProduct
              (buildPLStep (R := R) (swaps, MInv) (.replace use toReplace scale)) *
            replace M use toReplace scale := by
              simp [Matrix.applyRowOp]
      _ = P * (L * Rinv) * replace M use toReplace scale := by
            simp [buildPLStateProduct, buildPLStep, permutationOfSwaps, lowerOfSwaps,
              P, L, Rinv, replaceCol_eq_mul_elem, foldl_swapRow_mul, h, Matrix.mul_assoc]
      _ = P * (L * Rinv) * (Rop * M) := by
            rw [replace_matrix_eq_elem_mul_matrix]
            simp [Rop, Matrix.elementaryMatrixOfRowOp]
      _ = P * L * M := by
            calc
              P * (L * Rinv) * (Rop * M) = P * (L * (Rinv * (Rop * M))) := by
                simp [Matrix.mul_assoc]
              _ = P * (L * ((Rinv * Rop) * M)) := by
                simp [Matrix.mul_assoc]
              _ = P * (L * ((1 : squareMatrix a R) * M)) := by rw [hR]
              _ = P * L * M := by simp [Matrix.mul_assoc]

/- Packages the three specialized state-invariant lemmas into one statement
indexed by an arbitrary invertible row operation. -/
omit [DecidableEq R] in
private lemma buildPLStep_stateProduct
    (state : List (Fin a × Fin a) × squareMatrix a R)
    (M : Matrix (Fin a) (Fin b) R) (op : RowOp a R)
    (hop : InvertibleRowOp (R := R) op) :
    buildPLStateProduct (buildPLStep (R := R) state op) * Matrix.applyRowOp M op =
      buildPLStateProduct state * M := by
  cases op with
  | swap i j =>
      simpa using buildPLStep_stateProduct_swap
        (R := R) (state := state) (M := M) i j
  | factor row scale =>
      simpa using buildPLStep_stateProduct_factor
        (R := R) (state := state) (M := M) row scale hop
  | replace use toReplace scale =>
      simpa using buildPLStep_stateProduct_replace
        (R := R) (state := state) (M := M) use toReplace scale hop

/- Extends the one-step invariant to a whole fold over a list of recorded row
operations. The induction simply peels off the head operation and reuses the
one-step cancellation lemma. -/
omit [DecidableEq R] in
private lemma buildPLStateProduct_foldl
    (steps : List (RowOp a R))
    (state : List (Fin a × Fin a) × squareMatrix a R)
    (M : Matrix (Fin a) (Fin b) R)
    (hsteps : ∀ op ∈ steps, InvertibleRowOp (R := R) op) :
    buildPLStateProduct (steps.foldl (buildPLStep (R := R)) state) *
      steps.foldl Matrix.applyRowOp M =
        buildPLStateProduct state * M := by
  induction steps generalizing state M with
  | nil =>
      simp [buildPLStateProduct]
  | cons op steps ih =>
      have hop : InvertibleRowOp (R := R) op := hsteps op (by simp)
      have htail : ∀ op' ∈ steps, InvertibleRowOp (R := R) op' := by
        intro op' hop'
        exact hsteps op' (by simp [hop'])
      calc
        -- Apply the induction hypothesis to the tail starting from the updated state.
        buildPLStateProduct (steps.foldl (buildPLStep (R := R)) (buildPLStep (R := R) state op)) *
            steps.foldl Matrix.applyRowOp (Matrix.applyRowOp M op)
            = buildPLStateProduct (buildPLStep (R := R) state op) *
                Matrix.applyRowOp M op := by
                  simpa using ih (state := buildPLStep (R := R) state op)
                    (M := Matrix.applyRowOp M op) htail
        -- Then cancel the head operation with the one-step lemma.
        _ = buildPLStateProduct state * M := by
              exact buildPLStep_stateProduct (R := R) (state := state) (M := M) (op := op) hop

/- This is the global cancellation theorem for `LUFactorizationInternal.buildPLFromSteps`: if every logged row
operation is invertible, then the reconstructed matrices satisfy
`P * L * steps.foldl applyRowOp M = M`. -/
omit [DecidableEq R] in
private theorem buildPL_mul_foldl_applyRowOp_eq
    (steps : List (RowOp a R)) (M : Matrix (Fin a) (Fin b) R)
    (hsteps : ∀ op ∈ steps, InvertibleRowOp (R := R) op) :
    let (P, L) := LUFactorizationInternal.buildPLFromSteps (R := R) steps
    P * L * steps.foldl Matrix.applyRowOp M = M := by
  simp [LUFactorizationInternal.buildPLFromSteps]
  simpa [buildPLStateProduct, permutationOfSwaps, lowerOfSwaps, Matrix.mul_assoc] using
    buildPLStateProduct_foldl (R := R) (steps := steps) (state := ([], 1)) (M := M) hsteps

/-! ## The elimination log only records invertible operations -/

/- Proves that the recursive helper `GaussianEliminationInternal.eliminateColLoop` never appends a
non-invertible row operation. The induction follows the loop index `r` from the
current row downwards. -/
private theorem eliminateCol_go_steps_invertible
    (pivotRow : Fin a) (pivotCol : Fin b) (r : Nat)
    (M : Matrix (Fin a) (Fin b) R) (steps : List (RowOp a R))
    (hsteps : ∀ op ∈ steps, InvertibleRowOp (R := R) op) :
    ∀ op ∈ (GaussianEliminationInternal.eliminateColLoop pivotRow pivotCol r M steps).2, InvertibleRowOp (R := R) op := by
  have hrec :
      ∀ k (r : Nat) (M : Matrix (Fin a) (Fin b) R) (steps : List (RowOp a R)),
        a - r = k →
        (∀ op ∈ steps, InvertibleRowOp (R := R) op) →
        ∀ op ∈ (GaussianEliminationInternal.eliminateColLoop pivotRow pivotCol r M steps).2, InvertibleRowOp (R := R) op := by
    intro k
    induction k with
    | zero =>
        -- No rows remain to inspect, so the output step log is unchanged.
        intro r M steps hk hsteps op hop
        have hr : a ≤ r := Nat.le_of_sub_eq_zero hk
        rw [GaussianEliminationInternal.eliminateColLoop, GaussianEliminationInternal.eliminateColLoopAux,
          dif_neg (not_lt_of_ge hr)] at hop
        simpa using hsteps op hop
    | succ k ih =>
        -- We inspect the current row `i = r` and follow exactly the branch taken
        -- by the elimination code.
        intro r M steps hk hsteps op hop
        have hr : r < a := by omega
        have hk' : a - (r + 1) = k := by omega
        let i : Fin a := ⟨r, hr⟩
        rw [GaussianEliminationInternal.eliminateColLoop, GaussianEliminationInternal.eliminateColLoopAux, dif_pos hr] at hop
        by_cases hEq : i = pivotRow
        -- The pivot row is skipped and we recurse immediately.
        · exact ih (r + 1) M steps hk' hsteps op (by simpa [i, hEq, dite_eq_ite] using hop)
        · by_cases hcoeff : M i pivotCol ≠ 0
          -- A nonzero entry below the pivot produces one replacement operation,
          -- which is invertible because `pivotRow /= i`.
          · let op' : RowOp a R := .replace pivotRow i (-M i pivotCol / M pivotRow pivotCol)
            let M' := replace M pivotRow i (-M i pivotCol / M pivotRow pivotCol)
            let steps' := steps ++ [op']
            have hsteps' : ∀ op ∈ steps', InvertibleRowOp (R := R) op := by
              intro op'' hop''
              have hop'' : op'' ∈ steps ∨ op'' = op' := by
                simpa [steps', List.mem_append, List.mem_singleton] using hop''
              rcases hop'' with hop'' | rfl
              · exact hsteps op'' hop''
              · have huse : pivotRow ≠ i := by
                  intro hpr
                  exact hEq hpr.symm
                simp [op', InvertibleRowOp, huse]
            have huse : pivotRow ≠ i := by
              intro hpr
              exact hEq hpr.symm
            have hpivot' : M' pivotRow pivotCol = M pivotRow pivotCol := by
              simp [M', replace, huse]
            have hop' :
                op ∈ (GaussianEliminationInternal.eliminateColLoop pivotRow pivotCol (r + 1) M' steps').2 := by
              change op ∈ (GaussianEliminationInternal.eliminateColLoopAux pivotRow pivotCol (M' pivotRow pivotCol)
                (r + 1) M' steps').2
              simpa [hpivot', i, hEq, hcoeff, op', M', steps', List.concat_eq_append,
                dite_eq_ite] using hop
            exact ih (r + 1) M' steps' hk' hsteps' op hop'
          -- A zero entry below the pivot appends nothing and just recurses.
          · exact ih (r + 1) M steps hk' hsteps op
              (by simpa [i, hEq, hcoeff, dite_eq_ite] using hop)
  exact hrec (a - r) r M steps rfl hsteps

/- Lifts the previous helper lemma from `GaussianEliminationInternal.eliminateColLoop` to the public
`GaussianEliminationInternal.eliminateColCore` wrapper, which chooses the starting row based on `reduced`. -/
private theorem eliminateCol_steps_invertible
    (M : Matrix (Fin a) (Fin b) R) (pivotRow : Fin a) (pivotCol : Fin b)
    (steps : List (RowOp a R)) (reduced : Bool)
    (hsteps : ∀ op ∈ steps, InvertibleRowOp (R := R) op) :
    ∀ op ∈ (GaussianEliminationInternal.eliminateColCore M pivotRow pivotCol steps reduced).2, InvertibleRowOp (R := R) op := by
  rw [GaussianEliminationInternal.eliminateColCore]
  by_cases hred : reduced
  · simpa [hred] using eliminateCol_go_steps_invertible
      (R := R) pivotRow pivotCol 0 M steps hsteps
  · simpa [hred] using eliminateCol_go_steps_invertible
      (R := R) pivotRow pivotCol pivotRow.1 M steps hsteps

/- Proves that the non-reduced branch of `GaussianEliminationInternal.rowReductionAux` also records only invertible
operations. The proof follows the recursive control flow of `GaussianEliminationInternal.rowReductionAux`, first
adding a swap to move the pivot into place and then delegating to
`GaussianEliminationInternal.eliminateColCore`. -/
private theorem rrefAux_steps_invertible_false
    (M : Matrix (Fin a) (Fin b) R) (r c : Nat) (steps : List (RowOp a R))
    (hsteps : ∀ op ∈ steps, InvertibleRowOp (R := R) op) :
    ∀ op ∈ (GaussianEliminationInternal.rowReductionAux M r c steps false).2, InvertibleRowOp (R := R) op := by
  have hrec :
      ∀ k (M : Matrix (Fin a) (Fin b) R) (r c : Nat) (steps : List (RowOp a R)),
        a - r = k →
        (∀ op ∈ steps, InvertibleRowOp (R := R) op) →
        ∀ op ∈ (GaussianEliminationInternal.rowReductionAux M r c steps false).2, InvertibleRowOp (R := R) op := by
    intro k
    induction k with
    | zero =>
        -- Once there are no rows left, `GaussianEliminationInternal.rowReductionAux` returns the existing step list.
        intro M r c steps hk hsteps op hop
        have hr : a ≤ r := Nat.le_of_sub_eq_zero hk
        have hop' : op ∈ steps := by
          simpa [GaussianEliminationInternal.rowReductionAux, Nat.not_lt_of_ge hr] using hop
        exact hsteps op hop'
    | succ k ih =>
        -- Otherwise we inspect the current `(r, c)` position and mirror the
        -- algorithm's case split.
        intro M r c steps hk hsteps op hop
        have hr : r < a := by omega
        have hk' : a - (r + 1) = k := by omega
        rw [GaussianEliminationInternal.rowReductionAux, dif_pos hr] at hop
        by_cases hc : c < b
        · rw [if_pos hc] at hop
          cases hcp : checkPivot M r c with
          | none =>
              -- No pivot found in this column, so the step log is unchanged.
              have hop' : op ∈ steps := by
                simpa [hcp] using hop
              exact hsteps op hop'
          | some p =>
              -- A pivot produces one swap followed by an elimination phase.
              rcases p with ⟨pivotRow, pivotCol⟩
              let rowFin : Fin a := ⟨r, hr⟩
              let swapOp : RowOp a R := .swap rowFin pivotRow
              let steps1 : List (RowOp a R) := steps ++ [swapOp]
              let m1 : Matrix (Fin a) (Fin b) R :=
                if pivotRow.1 = r then M else swapRow M rowFin pivotRow
              have hsteps1 : ∀ op ∈ steps1, InvertibleRowOp (R := R) op := by
                intro op' hop'
                have hop' : op' ∈ steps ∨ op' = swapOp := by
                  simpa [steps1, List.mem_append, List.mem_singleton] using hop'
                rcases hop' with hop' | rfl
                · exact hsteps op' hop'
                · simp [swapOp, InvertibleRowOp]
              let res := GaussianEliminationInternal.eliminateColCore m1 rowFin pivotCol steps1 false
              have hres :
                  ∀ op ∈ res.2, InvertibleRowOp (R := R) op := by
                simpa [res] using eliminateCol_steps_invertible
                  (R := R) m1 rowFin pivotCol steps1 false hsteps1
              exact ih res.1 (r + 1) (c + 1) res.2 hk' hres op
                (by simpa [hcp, rowFin, steps1, m1, res, List.concat_eq_append] using hop)
        -- If the column index is already out of range, recursion stops.
        · have hop' : op ∈ steps := by
              simpa [hc] using hop
          exact hsteps op hop'
  exact hrec (a - r) M r c steps rfl hsteps

/- Applies the previous theorem to the actual step log produced by
`rowEchelonForm`. This is the invertibility hypothesis needed by the final
reconstruction theorem. -/
private theorem rowEchelonForm_steps_invertible
    (M : Matrix (Fin a) (Fin b) R) :
    ∀ op ∈ (GaussianEliminationInternal.rawRowEchelonForm M).2, InvertibleRowOp (R := R) op := by
  simpa [GaussianEliminationInternal.rawRowEchelonForm] using
    rrefAux_steps_invertible_false (R := R) M 0 0 [] (by simp)

/-! ## Lower-triangular structure and tail identity invariants -/

/- `tailIdentityFrom r L` says that every column with index at least `r` looks
exactly like the corresponding column of the identity matrix. This is the
structural invariant that keeps the trailing part of `L` untouched while the
algorithm modifies earlier columns. -/
private def tailIdentityFrom (r : Nat) (L : squareMatrix a R) : Prop :=
  ∀ i j : Fin a, r ≤ j.1 → L i j = if i = j then 1 else 0

/- Pointwise description of `swapRow`, used repeatedly when proving that row and
column swaps preserve lower-triangular structure. -/
omit [Field R] [DecidableEq R] in
@[simp] private lemma swapRow_apply
    (L : squareMatrix a R) (r1 r2 i j : Fin a) :
    swapRow L r1 r2 i j =
      if i = r1 then L r2 j else if i = r2 then L r1 j else L i j := by
  simp [swapRow]

/- Pointwise description of `swapCol`, dual to `swapRow_apply`. -/
omit [Field R] [DecidableEq R] in
@[simp] private lemma swapCol_apply
    (L : squareMatrix a R) (c1 c2 i j : Fin a) :
    swapCol L c1 c2 i j =
      if j = c1 then L i c2 else if j = c2 then L i c1 else L i j := by
  by_cases h1 : j = c1 <;> by_cases h2 : j = c2 <;>
    simp [swapCol, swapRow, h1, h2]

/- Pointwise formula for `replaceCol` away from the diagonal case
`use = toReplace`. This is the form needed to inspect individual entries. -/
omit [DecidableEq R] in
@[simp] private lemma replaceCol_apply_of_ne
    (L : squareMatrix a R) (use toReplace i j : Fin a) (k : R)
    (huse : use ≠ toReplace) :
    replaceCol L use toReplace k i j =
      if j = use then L i use + k * L i toReplace else L i j := by
  have hne : toReplace ≠ use := by
    intro h
    exact huse h.symm
  by_cases hj : j = use
  · subst hj
    simp [replaceCol, replace, hne]
  · simp [replaceCol, replace, hne, hj]

/- The tail-identity predicate is monotone in the starting index: once the tail
is identity from `r`, it is also identity from every later column `s >= r`. -/
omit [DecidableEq R] in
private lemma tailIdentityFrom_mono
    {r s : Nat} {L : squareMatrix a R} (hrs : r ≤ s)
    (htail : tailIdentityFrom (R := R) r L) :
    tailIdentityFrom (R := R) s L := by
  intro i j hj
  exact htail i j (le_trans hrs hj)

/- The identity matrix trivially satisfies the tail-identity predicate from the
first column onward. This seeds the later induction on `LUFactorizationInternal.buildPLFromSteps`. -/
omit [DecidableEq R] in
private lemma tailIdentityFrom_one :
    tailIdentityFrom (R := R) 0 (1 : squareMatrix a R) := by
  intro i j hj
  simp [Matrix.one_apply]

/- The identity matrix is also unit lower triangular, giving the base case for
the lower-factor invariant. -/
omit [DecidableEq R] in
private lemma one_isUnitLowerTriangular :
    IsUnitLowerTriangular (R := R) (a := a) (1 : squareMatrix a R) := by
  constructor
  · simpa using (Matrix.blockTriangular_one (R := R) (m := Fin a) (b := OrderDual.toDual))
  · intro i
    simp

/- Appending a swap to the step list updates the lower factor by swapping the
matching row and column. This unwraps how `LUFactorizationInternal.buildPLFromSteps` transports swaps from the
permutation factor into the lower factor. -/
omit [DecidableEq R] in
private lemma buildPL_lower_concat_swap
    (steps : List (RowOp a R)) (i j : Fin a) :
    (LUFactorizationInternal.buildPLFromSteps (R := R) (List.concat steps (.swap i j))).2 =
      swapRow (swapCol (LUFactorizationInternal.buildPLFromSteps (R := R) steps).2 i j) i j := by
  unfold LUFactorizationInternal.buildPLFromSteps
  rw [List.concat_eq_append, List.foldl_append]
  simp only [List.foldl]
  set state := steps.foldl (buildPLStep (R := R)) ([], (1 : squareMatrix a R))
  rcases state with ⟨swaps, MInv⟩
  change
    lowerOfSwaps (R := R) (swaps.concat (i, j)) (swapCol MInv i j) =
      swapRow (swapCol (lowerOfSwaps (R := R) swaps MInv) i j) i j
  unfold lowerOfSwaps
  rw [List.concat_eq_append, List.foldl_append]
  exact congrArg (fun X => swapRow X i j)
    (lowerOfSwaps_swapCol (R := R) (swaps := swaps) (M := MInv) i j)

/- Appending a genuine replacement updates the lower factor by the opposite
column replacement, matching the inverse stored by `buildPLStep`. -/
omit [DecidableEq R] in
private lemma buildPL_lower_concat_replace
    (steps : List (RowOp a R)) (use toReplace : Fin a) (k : R)
    (huse : use ≠ toReplace) :
    (LUFactorizationInternal.buildPLFromSteps (R := R) (List.concat steps (.replace use toReplace k))).2 =
      replaceCol (LUFactorizationInternal.buildPLFromSteps (R := R) steps).2 use toReplace (-k) := by
  unfold LUFactorizationInternal.buildPLFromSteps
  rw [List.concat_eq_append, List.foldl_append]
  simp only [List.foldl]
  set state := steps.foldl (buildPLStep (R := R)) ([], (1 : squareMatrix a R))
  rcases state with ⟨swaps, MInv⟩
  simpa only [buildPLStep, huse] using
    (lowerOfSwaps_replaceCol
      (R := R) (swaps := swaps) (M := MInv) (use := use) (toReplace := toReplace) (-k))

/- Rewrites `swapRow` using the permutation action of `Equiv.swap` on row
indices. This makes later invariance proofs look like transport by a bijection. -/
omit [Field R] [DecidableEq R] in
private lemma swapRow_apply_eq_swap
    (L : squareMatrix a R) (i j x y : Fin a) :
    swapRow L i j x y = L ((Equiv.swap i j) x) y := by
  by_cases hxi : x = i
  · rw [hxi]
    by_cases hij : i = j
    · rw [hij]
      simp [swapRow]
    · simp [swapRow]
  · by_cases hxj : x = j
    · rw [hxj]
      have hji : j ≠ i := by
        simpa [hxj] using hxi
      simp [swapRow, hji]
    · simp [swapRow, Equiv.swap_apply_def, hxi, hxj]

/- Column-wise analogue of `swapRow_apply_eq_swap`. -/
omit [Field R] [DecidableEq R] in
private lemma swapCol_apply_eq_swap
    (L : squareMatrix a R) (i j x y : Fin a) :
    swapCol L i j x y = L x ((Equiv.swap i j) y) := by
  by_cases hyi : y = i
  · rw [hyi]
    by_cases hij : i = j
    · rw [hij]
      simp [swapCol]
    · simp [swapCol]
  · by_cases hyj : y = j
    · rw [hyj]
      have hji : j ≠ i := by
        simpa [hyj] using hyi
      simp [swapCol, hji]
    · simp [swapCol, Equiv.swap_apply_def, hyi, hyj]

/- Combining the previous two lemmas gives a compact formula for the lower
factor update induced by a stored swap. -/
omit [Field R] [DecidableEq R] in
@[simp] private lemma swapRow_swapCol_apply
    (L : squareMatrix a R) (i j x y : Fin a) :
    swapRow (swapCol L i j) i j x y =
      L ((Equiv.swap i j) x) ((Equiv.swap i j) y) := by
  rw [swapRow_apply_eq_swap, swapCol_apply_eq_swap]

/- If both swapped indices lie at or beyond `r`, then `Equiv.swap i j` acts as
the identity on any index strictly before `r`. This isolates the untouched
prefix of the lower-triangular matrix. -/
private lemma swap_eq_self_of_lt
    {r : Nat} {i j x : Fin a}
    (hi : r ≤ i.1) (hj : r ≤ j.1) (hx : x.1 < r) :
    (Equiv.swap i j) x = x := by
  by_cases hxi : x = i
  · have : r ≤ x.1 := by simpa [hxi] using hi
    omega
  · by_cases hxj : x = j
    · have : r ≤ x.1 := by simpa [hxj] using hj
      omega
    · simp [Equiv.swap_apply_def, hxi, hxj]

/- Swapping two rows and the matching two columns, both at or below the active
frontier `r`, preserves unit lower-triangularity and the tail-identity
property. This is the structural invariant needed after a pivot swap. -/
omit [DecidableEq R] in
private lemma swap_preserves_unitLower_and_tail
    {r : Nat} {L : squareMatrix a R} {i j : Fin a}
    (hL : IsUnitLowerTriangular (R := R) (a := a) L)
    (htail : tailIdentityFrom (R := R) r L)
    (hi : r ≤ i.1) (hj : r ≤ j.1) :
    IsUnitLowerTriangular (R := R) (a := a) (swapRow (swapCol L i j) i j) ∧
      tailIdentityFrom (R := R) r (swapRow (swapCol L i j) i j) := by
  rcases hL with ⟨htri, hdiag⟩
  -- First show that the tail-identity part is transported through the same swap.
  have htail' : tailIdentityFrom (R := R) r (swapRow (swapCol L i j) i j) := by
    intro x y hy
    have hswap_ge : r ≤ ((Equiv.swap i j) y).1 := by
      by_cases hyi : y = i
      · simpa [hyi] using hj
      · by_cases hyj : y = j
        · simpa [hyj] using hi
        · simp [Equiv.swap_apply_def, hyi, hyj, hy]
    have h := htail ((Equiv.swap i j) x) ((Equiv.swap i j) y) hswap_ge
    have hs :
        (((Equiv.swap i j) x) = ((Equiv.swap i j) y)) ↔ x = y := by
      constructor
      · intro hxy
        exact (Equiv.swap i j).injective hxy
      · intro hxy
        simp [hxy]
    rw [swapRow_swapCol_apply]
    simpa [hs] using h
  constructor
  · constructor
    -- For entries strictly above the diagonal, either the tail-identity
    -- statement applies or the swap is invisible because both indices are in
    -- the untouched prefix.
    · intro x y hxy
      by_cases hyge : r ≤ y.1
      · have h := htail' x y hyge
        have hne : x ≠ y := by
          intro hEq
          subst hEq
          exact lt_irrefl _ hxy
        simpa [hne] using h
      · have hylt : y.1 < r := Nat.lt_of_not_ge hyge
        have hxlt : x.1 < r := by
          simpa using lt_trans (by simpa using hxy) hylt
        have hsx : (Equiv.swap i j) x = x := swap_eq_self_of_lt hi hj hxlt
        have hsy : (Equiv.swap i j) y = y := swap_eq_self_of_lt hi hj hylt
        rw [swapRow_swapCol_apply, hsx, hsy]
        exact htri hxy
    · intro x
      by_cases hxge : r ≤ x.1
      · have h := htail' x x hxge
        simpa using h
      · have hxlt : x.1 < r := Nat.lt_of_not_ge hxge
        have hsx : (Equiv.swap i j) x = x := swap_eq_self_of_lt hi hj hxlt
        rw [swapRow_swapCol_apply, hsx]
        exact hdiag x
  · exact htail'

/- Replacing column `use` by itself plus a multiple of a later column preserves
unit lower-triangularity and preserves the identity tail starting just after
`use`. This is the structural invariant needed after a genuine elimination step. -/
omit [DecidableEq R] in
private lemma replaceCol_preserves_unitLower_and_tail
    {L : squareMatrix a R} {use toReplace : Fin a} {k : R}
    (hL : IsUnitLowerTriangular (R := R) (a := a) L)
    (htail : tailIdentityFrom (R := R) (use.1 + 1) L)
    (huse : use.1 < toReplace.1) :
    IsUnitLowerTriangular (R := R) (a := a) (replaceCol L use toReplace k) ∧
      tailIdentityFrom (R := R) (use.1 + 1) (replaceCol L use toReplace k) := by
  rcases hL with ⟨htri, hdiag⟩
  have hne : use ≠ toReplace := by
    intro h
    subst h
    exact lt_irrefl _ huse
  constructor
  · constructor
    -- Above-diagonal entries in column `use` remain zero because both source
    -- entries are zero there.
    · intro i j hij
      by_cases hju : j = use
      · rw [hju]
        rw [replaceCol_apply_of_ne (L := L) (use := use) (toReplace := toReplace)
          (i := i) (j := use) (k := k) hne]
        simp
        have hij' : OrderDual.toDual use < OrderDual.toDual i := by
          simpa [hju] using hij
        have hiuse : L i use = 0 := htri hij'
        have hitoReplace : L i toReplace = 0 := by
          have h := htail i toReplace (Nat.succ_le_of_lt huse)
          have hne' : i ≠ toReplace := by
            intro hEq
            have : i.1 < toReplace.1 := by
              exact lt_trans (by simpa [hju] using hij) huse
            subst hEq
            exact lt_irrefl _ this
          simpa [hne'] using h
        simp [hiuse, hitoReplace]
      · rw [replaceCol_apply_of_ne (L := L) (use := use) (toReplace := toReplace)
          (i := i) (j := j) (k := k) hne, if_neg hju]
        exact htri hij
    · intro i
      by_cases hiu : i = use
      · rw [hiu]
        rw [replaceCol_apply_of_ne (L := L) (use := use) (toReplace := toReplace)
          (i := use) (j := use) (k := k) hne]
        simp
        have hdiagUse : L use use = 1 := hdiag use
        have hzero : L use toReplace = 0 := by
          have h := htail use toReplace (Nat.succ_le_of_lt huse)
          simpa [hne] using h
        simp [hdiagUse, hzero]
      · rw [replaceCol_apply_of_ne (L := L) (use := use) (toReplace := toReplace)
          (i := i) (j := i) (k := k) hne]
        simp [hiu, hdiag i]
  -- Columns strictly after `use` are untouched, so the tail-identity property remains.
  · intro i j hj
    have hju : j ≠ use := by
      intro h
      subst j
      have : use.1 + 1 ≤ use.1 := hj
      omega
    rw [replaceCol_apply_of_ne (L := L) (use := use) (toReplace := toReplace)
      (i := i) (j := j) (k := k) hne, if_neg hju]
    exact htail i j hj

/- The recursive elimination helper preserves the lower-factor invariants once
the pivot row has already been reached. The induction follows the same scan of
rows as `GaussianEliminationInternal.eliminateColLoop`. -/
private theorem eliminateCol_go_lower_invariant
    (pivotRow : Fin a) (pivotCol : Fin b) (r : Nat)
    (M : Matrix (Fin a) (Fin b) R) (steps : List (RowOp a R))
    (hr : pivotRow.1 ≤ r)
    (hL : IsUnitLowerTriangular (R := R) (a := a) ((LUFactorizationInternal.buildPLFromSteps (R := R) steps).2))
    (htail : tailIdentityFrom (R := R) (pivotRow.1 + 1) ((LUFactorizationInternal.buildPLFromSteps (R := R) steps).2)) :
    IsUnitLowerTriangular
        (R := R) (a := a) ((LUFactorizationInternal.buildPLFromSteps (R := R) (GaussianEliminationInternal.eliminateColLoop pivotRow pivotCol r M steps).2).2) ∧
      tailIdentityFrom (R := R) (pivotRow.1 + 1)
        ((LUFactorizationInternal.buildPLFromSteps (R := R) (GaussianEliminationInternal.eliminateColLoop pivotRow pivotCol r M steps).2).2) := by
  have hrec :
      ∀ k (r : Nat) (M : Matrix (Fin a) (Fin b) R) (steps : List (RowOp a R)),
        a - r = k →
        pivotRow.1 ≤ r →
        IsUnitLowerTriangular (R := R) (a := a) ((LUFactorizationInternal.buildPLFromSteps (R := R) steps).2) →
        tailIdentityFrom (R := R) (pivotRow.1 + 1) ((LUFactorizationInternal.buildPLFromSteps (R := R) steps).2) →
        IsUnitLowerTriangular
            (R := R)
            (a := a)
            ((LUFactorizationInternal.buildPLFromSteps (R := R) (GaussianEliminationInternal.eliminateColLoop pivotRow pivotCol r M steps).2).2) ∧
          tailIdentityFrom (R := R) (pivotRow.1 + 1)
            ((LUFactorizationInternal.buildPLFromSteps (R := R) (GaussianEliminationInternal.eliminateColLoop pivotRow pivotCol r M steps).2).2) := by
    intro k
    induction k with
    | zero =>
        -- Once the scan is exhausted, the lower factor is unchanged.
        intro r M steps hk hr hL htail
        have hr' : a ≤ r := Nat.le_of_sub_eq_zero hk
        rw [GaussianEliminationInternal.eliminateColLoop, GaussianEliminationInternal.eliminateColLoopAux,
          dif_neg (not_lt_of_ge hr')]
        exact And.intro hL htail
    | succ k ih =>
        -- Mirror the recursive elimination code and update the structural
        -- invariants only in the branch that appends a replacement.
        intro r M steps hk hr hL htail
        have hr' : r < a := by omega
        have hk' : a - (r + 1) = k := by omega
        let i : Fin a := ⟨r, hr'⟩
        rw [GaussianEliminationInternal.eliminateColLoop, GaussianEliminationInternal.eliminateColLoopAux, dif_pos hr']
        by_cases hEq : i = pivotRow
        -- The pivot row is skipped.
        · simpa [i, hEq, dite_eq_ite] using ih (r + 1) M steps hk' (by omega) hL htail
        · by_cases hcoeff : M i pivotCol ≠ 0
          -- A genuine elimination step updates the lower factor by a column replacement.
          · let op' : RowOp a R := .replace pivotRow i (-M i pivotCol / M pivotRow pivotCol)
            let M' := replace M pivotRow i (-M i pivotCol / M pivotRow pivotCol)
            let steps' := List.concat steps op'
            have hpivot_lt_i : pivotRow.1 < i.1 := by
              have hle : pivotRow.1 ≤ i.1 := by
                simpa [i] using hr
              have hne' : pivotRow.1 ≠ i.1 := by
                intro hval
                apply hEq
                exact Fin.ext hval.symm
              omega
            have hsteps' :
                IsUnitLowerTriangular (R := R) (a := a) ((LUFactorizationInternal.buildPLFromSteps (R := R) steps').2) ∧
                  tailIdentityFrom (R := R) (pivotRow.1 + 1) ((LUFactorizationInternal.buildPLFromSteps (R := R) steps').2) := by
              rw [buildPL_lower_concat_replace (R := R) (steps := steps) (use := pivotRow)
                (toReplace := i) (k := -M i pivotCol / M pivotRow pivotCol) (by
                  intro h
                  exact hEq h.symm)]
              exact replaceCol_preserves_unitLower_and_tail
                (R := R) (a := a) (L := (LUFactorizationInternal.buildPLFromSteps (R := R) steps).2) hL htail hpivot_lt_i
            have hpivot' : M' pivotRow pivotCol = M pivotRow pivotCol := by
              have hneq : pivotRow ≠ i := by
                intro h
                exact hEq h.symm
              simp [M', replace, hneq]
            have hrec' := ih (r + 1) M' steps' hk' (by omega) hsteps'.1 hsteps'.2
            dsimp [i, op', M', steps'] at hrec' ⊢
            have hEq' : (⟨r, hr'⟩ : Fin a) ≠ pivotRow := by
              simpa using hEq
            have hcoeff' : ¬M ⟨r, hr'⟩ pivotCol = 0 := by
              simpa using hcoeff
            rw [if_neg hEq', if_pos hcoeff']
            have hpivot'' :
                replace M pivotRow ⟨r, hr'⟩ (-M ⟨r, hr'⟩ pivotCol / M pivotRow pivotCol)
                  pivotRow pivotCol = M pivotRow pivotCol := by
              simpa [M'] using hpivot'
            simpa [GaussianEliminationInternal.eliminateColLoop, List.concat_eq_append, hpivot'']
              using hrec'
          -- Zero entries below the pivot do not change the lower factor.
          · simpa [i, hEq, hcoeff, dite_eq_ite] using
              ih (r + 1) M steps hk' (by omega) hL htail
  exact hrec (a - r) r M steps rfl hr hL htail

/- Specializes the previous theorem to the non-reduced `GaussianEliminationInternal.eliminateColCore` wrapper. -/
private theorem eliminateCol_lower_invariant_false
    (M : Matrix (Fin a) (Fin b) R) (pivotRow : Fin a) (pivotCol : Fin b)
    (steps : List (RowOp a R))
    (hL : IsUnitLowerTriangular (R := R) (a := a) ((LUFactorizationInternal.buildPLFromSteps (R := R) steps).2))
    (htail : tailIdentityFrom (R := R) (pivotRow.1 + 1) ((LUFactorizationInternal.buildPLFromSteps (R := R) steps).2)) :
    IsUnitLowerTriangular
        (R := R) (a := a) ((LUFactorizationInternal.buildPLFromSteps (R := R) (GaussianEliminationInternal.eliminateColCore M pivotRow pivotCol steps false).2).2) ∧
      tailIdentityFrom (R := R) (pivotRow.1 + 1)
        ((LUFactorizationInternal.buildPLFromSteps (R := R) (GaussianEliminationInternal.eliminateColCore M pivotRow pivotCol steps false).2).2) := by
  simpa [GaussianEliminationInternal.eliminateColCore] using
    eliminateCol_go_lower_invariant
      (R := R) (pivotRow := pivotRow) (pivotCol := pivotCol) (r := pivotRow.1)
      (M := M) (steps := steps) (le_rfl) hL htail

/- Propagates the lower-factor invariant through the non-reduced row-echelon
routine. Each pivot step first performs a swap-preserving update and then an
elimination-preserving update. -/
private theorem rrefAux_lower_unit_false
    (M : Matrix (Fin a) (Fin b) R) (r c : Nat) (steps : List (RowOp a R))
    (hL : IsUnitLowerTriangular (R := R) (a := a) ((LUFactorizationInternal.buildPLFromSteps (R := R) steps).2))
    (htail : tailIdentityFrom (R := R) r ((LUFactorizationInternal.buildPLFromSteps (R := R) steps).2)) :
    IsUnitLowerTriangular
        (R := R) (a := a) ((LUFactorizationInternal.buildPLFromSteps (R := R) (GaussianEliminationInternal.rowReductionAux M r c steps false).2).2) := by
  have hrec :
      ∀ k (M : Matrix (Fin a) (Fin b) R) (r c : Nat) (steps : List (RowOp a R)),
        a - r = k →
        IsUnitLowerTriangular (R := R) (a := a) ((LUFactorizationInternal.buildPLFromSteps (R := R) steps).2) →
        tailIdentityFrom (R := R) r ((LUFactorizationInternal.buildPLFromSteps (R := R) steps).2) →
        IsUnitLowerTriangular
            (R := R) (a := a) ((LUFactorizationInternal.buildPLFromSteps (R := R) (GaussianEliminationInternal.rowReductionAux M r c steps false).2).2) := by
    intro k
    induction k with
    | zero =>
        -- No rows remain, so the current lower factor is already final.
        intro M r c steps hk hL htail
        have hr : a ≤ r := Nat.le_of_sub_eq_zero hk
        simpa [GaussianEliminationInternal.rowReductionAux, Nat.not_lt_of_ge hr] using hL
    | succ k ih =>
        -- Follow the same case split as `GaussianEliminationInternal.rowReductionAux`.
        intro M r c steps hk hL htail
        have hr : r < a := by omega
        have hk' : a - (r + 1) = k := by omega
        rw [GaussianEliminationInternal.rowReductionAux, dif_pos hr]
        by_cases hc : c < b
        · rw [if_pos hc]
          cases hcp : checkPivot M r c with
          | none =>
              -- No pivot means the lower factor is unchanged in this column.
              simpa [hcp] using hL
          | some p =>
              -- A pivot step is composed of a swap update followed by an elimination update.
              rcases p with ⟨pivotRow, pivotCol⟩
              let rowFin : Fin a := ⟨r, hr⟩
              let swapOp : RowOp a R := .swap rowFin pivotRow
              let steps1 : List (RowOp a R) := List.concat steps swapOp
              let m1 : Matrix (Fin a) (Fin b) R :=
                if pivotRow.1 = r then M else swapRow M rowFin pivotRow
              have hpivot_ge : r ≤ pivotRow.1 := Matrix.checkPivot_some_row_ge (M := M) r c hcp
              have hsteps1 :
                  IsUnitLowerTriangular (R := R) (a := a) ((LUFactorizationInternal.buildPLFromSteps (R := R) steps1).2) ∧
                    tailIdentityFrom (R := R) r ((LUFactorizationInternal.buildPLFromSteps (R := R) steps1).2) := by
                rw [buildPL_lower_concat_swap
                  (R := R) (steps := steps) (i := rowFin) (j := pivotRow)]
                exact swap_preserves_unitLower_and_tail
                  (R := R) (a := a) (L := (LUFactorizationInternal.buildPLFromSteps (R := R) steps).2) hL htail
                  (by simp [rowFin]) hpivot_ge
              have hsteps1_tail :
                  tailIdentityFrom (R := R) (r + 1) ((LUFactorizationInternal.buildPLFromSteps (R := R) steps1).2) := by
                exact tailIdentityFrom_mono (R := R) (L := (LUFactorizationInternal.buildPLFromSteps (R := R) steps1).2)
                  (Nat.le_succ r) hsteps1.2
              let res := GaussianEliminationInternal.eliminateColCore m1 rowFin pivotCol steps1 false
              have hres :
                  IsUnitLowerTriangular (R := R) (a := a) ((LUFactorizationInternal.buildPLFromSteps (R := R) res.2).2) ∧
                    tailIdentityFrom (R := R) (r + 1) ((LUFactorizationInternal.buildPLFromSteps (R := R) res.2).2) := by
                simpa [res, rowFin, steps1, m1] using
                  eliminateCol_lower_invariant_false (R := R) (M := m1) (pivotRow := rowFin)
                    (pivotCol := pivotCol) (steps := steps1) hsteps1.1 hsteps1_tail
              exact ih res.1 (r + 1) (c + 1) res.2 hk' hres.1 hres.2
        · simpa [hc] using hL
  exact hrec (a - r) M r c steps rfl hL htail

/- Applies the lower-factor invariant to the actual output of
`rowEchelonForm`. This identifies the `L` factor returned by `LUFactorizationInternal.rawFactorization`
as unit lower triangular. -/
private theorem rowEchelonForm_lower_isUnitLowerTriangular
    (M : Matrix (Fin a) (Fin b) R) :
    IsUnitLowerTriangular
      (R := R) (a := a) ((LUFactorizationInternal.buildPLFromSteps (R := R) (GaussianEliminationInternal.rawRowEchelonForm M).2).2) := by
  simpa [GaussianEliminationInternal.rawRowEchelonForm] using
    rrefAux_lower_unit_false (R := R) (M := M) (r := 0) (c := 0) (steps := [])
      one_isUnitLowerTriangular tailIdentityFrom_one

/-! ## Final LU factorization theorems -/

/- Swapping two columns of a permutation matrix preserves the two orthogonality
identities `P.transpose * P = 1` and `P * P.transpose = 1`. This is the
inductive step for proving that the accumulated permutation factor is
orthogonal. -/
omit [DecidableEq R] in
private lemma swapCol_preserves_orthogonal
    (P : squareMatrix a R) (i j : Fin a)
    (hleft : P.transpose * P = 1) (hright : P * P.transpose = 1) :
    (swapCol P i j).transpose * swapCol P i j = 1 ∧
      swapCol P i j * (swapCol P i j).transpose = 1 := by
  let S : squareMatrix a R := Matrix.elementaryMatrixOfRowOp (.swap i j : RowOp a R)
  have hS : S * S = (1 : squareMatrix a R) := by
    simpa [S] using inverseRowOp_mul_elem
      (R := R) (op := (.swap i j : RowOp a R)) (by trivial)
  constructor
  -- For the left orthogonality identity, rewrite every swap as multiplication by `S`.
  · calc
      (swapCol P i j).transpose * swapCol P i j
          = (P * S).transpose * (P * S) := by simp [S, swapCol_eq_mul_elem]
      _ = S.transpose * (P.transpose * P) * S := by
            simp [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = S.transpose * (1 : squareMatrix a R) * S := by rw [hleft]
      _ = S.transpose * S := by simp
      _ = S * S := by simp [S, elem_swap_transpose]
      _ = 1 := hS
  -- The right orthogonality identity is analogous.
  · calc
      swapCol P i j * (swapCol P i j).transpose
          = (P * S) * (P * S).transpose := by simp [S, swapCol_eq_mul_elem]
      _ = P * (S * S.transpose) * P.transpose := by
            simp [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = P * P.transpose := by simp [S, elem_swap_transpose, hS]
      _ = 1 := hright

/- Folding `swapCol` over any list of swaps preserves orthogonality, starting
from an already orthogonal matrix. We later instantiate this at the identity
matrix to obtain the permutation factor returned by `LUFactorizationInternal.buildPLFromSteps`. -/
omit [DecidableEq R] in
private lemma permutationOfSwaps_orthogonal
    (swaps : List (Fin a × Fin a)) (P : squareMatrix a R)
    (hleft : P.transpose * P = 1) (hright : P * P.transpose = 1) :
    ((swaps.foldl (fun acc ij => swapCol acc ij.1 ij.2) P).transpose *
        (swaps.foldl (fun acc ij => swapCol acc ij.1 ij.2) P) = 1) ∧
      ((swaps.foldl (fun acc ij => swapCol acc ij.1 ij.2) P) *
        (swaps.foldl (fun acc ij => swapCol acc ij.1 ij.2) P).transpose = 1) := by
  induction swaps generalizing P with
  | nil =>
      simp [hleft, hright]
  | cons ij swaps ih =>
      rcases swapCol_preserves_orthogonal (R := R) P ij.1 ij.2 hleft hright with
        ⟨hleft', hright'⟩
      simpa using ih (P := swapCol P ij.1 ij.2) hleft' hright'

/- The main reconstruction theorem: the factors returned by `LUFactorizationInternal.rawFactorization`
really satisfy `P * L * U = M`. The proof combines:
* invertibility of the logged row operations,
* the execution log identity `steps.foldl applyRowOp M = U`,
* the global cancellation theorem for `LUFactorizationInternal.buildPLFromSteps`. -/
theorem LUFactorizationInternal.rawFactorization_reconstruct (M : Matrix (Fin a) (Fin b) R) :
    (LUFactorizationInternal.rawFactorization (R := R) M).1 * (LUFactorizationInternal.rawFactorization (R := R) M).2.1 *
      (LUFactorizationInternal.rawFactorization (R := R) M).2.2 = M := by
  unfold LUFactorizationInternal.rawFactorization
  split
  · rename_i U steps hrow
    split
    · rename_i P L hbuild
      -- First recover that every logged row operation is invertible.
      have hsteps : ∀ op ∈ steps, InvertibleRowOp (R := R) op := by
        simpa [hrow] using rowEchelonForm_steps_invertible (R := R) (M := M)
      -- Then turn the operational log into the matrix `U` produced by the algorithm.
      have hlog : steps.foldl Matrix.applyRowOp M = U := by
        simpa [Matrix.rowEchelonForm, hrow] using Matrix.rowEchelonForm_steps (M := M)
      -- Finally substitute both facts into the `LUFactorizationInternal.buildPLFromSteps` cancellation theorem.
      simpa [hbuild, hlog, Matrix.mul_assoc] using
        buildPL_mul_foldl_applyRowOp_eq (R := R) (steps := steps) (M := M) hsteps

namespace LUFactorizationInternal

/- The permutation factor returned by `rawFactorization` is orthogonal on both
sides, so it behaves exactly like a permutation matrix. The proof identifies it
with `permutationOfSwaps` and then folds the previous orthogonality lemma. -/
theorem rawFactorization_permutation_orthogonal
    (M : Matrix (Fin a) (Fin b) R) :
    (rawFactorization (R := R) M).1.transpose * (rawFactorization (R := R) M).1 = 1 ∧
      (rawFactorization (R := R) M).1 * (rawFactorization (R := R) M).1.transpose = 1 := by
  unfold rawFactorization
  split
  · rename_i U steps hrow
    split
    · rename_i P L hbuild
      -- Extract the concrete permutation built from the stored swap log.
      have hP :
          P = permutationOfSwaps (R := R)
            ((steps.foldl (buildPLStep (R := R)) ([], (1 : squareMatrix a R))).1) := by
        unfold LUFactorizationInternal.buildPLFromSteps at hbuild
        injection hbuild with hP hL
        exact hP.symm
      subst hP
      -- The identity matrix is orthogonal, and each stored swap preserves that property.
      simpa using
        permutationOfSwaps_orthogonal
          (R := R)
          (swaps := (steps.foldl (buildPLStep (R := R)) ([], (1 : squareMatrix a R))).1)
          (P := (1 : squareMatrix a R))
          (by simp)
          (by simp)

/- The `U` factor produced by `rawFactorization` is exactly the row-echelon form
computed by the elimination routine, so it inherits the echelon-form theorem
proved for `rowEchelonForm`. -/
theorem rawFactorization_upper_isEchelonForm (M : Matrix (Fin a) (Fin b) R) :
    Matrix.IsEchelonForm ((rawFactorization (R := R) M).2.2) := by
  unfold rawFactorization
  split
  · rename_i U steps hrow
    split
    · simpa [Matrix.rowEchelonForm, hrow] using Matrix.rowEchelonForm_isEchelonForm (M := M)

/- The lower factor returned by `rawFactorization` is unit lower triangular
because it is exactly the lower factor reconstructed from the step log of
`rowEchelonForm`. -/
theorem rawFactorization_lower_isUnitLowerTriangular
    (M : Matrix (Fin a) (Fin b) R) :
    IsUnitLowerTriangular (R := R) ((rawFactorization (R := R) M).2.1) := by
  unfold rawFactorization
  split
  · rename_i U steps hrow
    split
    · rename_i P L hbuild
      simpa [hrow, hbuild] using
        rowEchelonForm_lower_isUnitLowerTriangular (R := R) (M := M)

end LUFactorizationInternal

theorem Matrix.luFactorization_reconstruct (M : Matrix (Fin a) (Fin b) R) :
    let lu := Matrix.luFactorization M
    lu.P * lu.L * lu.U = M := by
  simpa [Matrix.luFactorization] using
    LUFactorizationInternal.rawFactorization_reconstruct (R := R) (M := M)

theorem Matrix.luFactorization_permutation_orthogonal
    (M : Matrix (Fin a) (Fin b) R) :
    let lu := Matrix.luFactorization M
    lu.P.transpose * lu.P = 1 ∧ lu.P * lu.P.transpose = 1 := by
  simpa [Matrix.luFactorization] using
    LUFactorizationInternal.rawFactorization_permutation_orthogonal (R := R) (M := M)

theorem Matrix.luFactorization_upper_isEchelonForm
    (M : Matrix (Fin a) (Fin b) R) :
    IsEchelonForm (M := (Matrix.luFactorization M).U) := by
  simpa [Matrix.luFactorization] using
    LUFactorizationInternal.rawFactorization_upper_isEchelonForm (R := R) (M := M)

theorem Matrix.luFactorization_lower_isUnitLowerTriangular
    (M : Matrix (Fin a) (Fin b) R) :
    IsUnitLowerTriangular ((Matrix.luFactorization M).L) := by
  simpa [Matrix.luFactorization] using
    LUFactorizationInternal.rawFactorization_lower_isUnitLowerTriangular (R := R) (M := M)
