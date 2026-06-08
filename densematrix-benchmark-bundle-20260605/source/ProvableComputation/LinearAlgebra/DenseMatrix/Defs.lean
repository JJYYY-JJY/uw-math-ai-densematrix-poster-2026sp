import Mathlib.Data.Matrix.Basic

/-!
# Dense matrix basics

This file contains only the minimal Vector-backed representation for dense
matrices and the bridge to mathlib's function-backed `Matrix` type.

The dimensions are tracked by the storage type itself: a value of
`DenseMatrix m n α` stores exactly `m * n` entries in one `Vector α (m * n)`.
Entries are flattened in row-major order, so row `i`, column `j` lives at offset
`i * n + j`.
-/

-- The universe parameter keeps `DenseMatrix` polymorphic over element types.
universe u

/--
Row-major matrix with dimensions tracked in the type.

The raw storage is the `data` field. Its `Vector` length is the representation
invariant, so callers index by `Fin m` and `Fin n` rather than by unchecked
natural-number offsets.
-/
structure DenseMatrix (m n : Nat) (α : Type u) where
  data : Vector α (m * n)
deriving Repr

-- All operations and helper lemmas for dense matrices live under this namespace.
namespace DenseMatrix

/--
Row-major offset for an entry of an `m` by `n` dense matrix.

For row `i` and column `j`, all entries in earlier rows contribute `i.val * n`
slots, and `j.val` selects the slot inside the current row. The companion
theorem `rowMajorIndex_lt` proves that this offset is inside the storage
interval `[0, m * n)`.
-/
def rowMajorIndex {m n : Nat} (i : Fin m) (j : Fin n) : Nat :=
  i.val * n + j.val

/--
The row-major offset is always a valid index into the flat storage vector.

The proof bounds `j` by the width `n`, rewrites the next row boundary as
`(i.val + 1) * n`, then uses `i.isLt` to stay below `m * n`.
-/
theorem rowMajorIndex_lt {m n : Nat} (i : Fin m) (j : Fin n) :
    rowMajorIndex i j < m * n := by
  unfold rowMajorIndex
  calc
    i.val * n + j.val < i.val * n + n := Nat.add_lt_add_left j.isLt (i.val * n)
    _ = (i.val + 1) * n := by rw [Nat.succ_mul]
    _ ≤ m * n := Nat.mul_le_mul_right n (Nat.succ_le_iff.mpr i.isLt)

/--
Unchecked row-major fast-path read.

The row and column are natural numbers, not typed `Fin` indices. This function
does not prove that `i < m`, `j < n`, or `i * n + j < m * n`; callers are
responsible for those bounds when they want matrix semantics. Prefer `get` when
typed indices are available.
-/
@[inline]
def get! {m n : Nat} {α : Type u} [Inhabited α] (M : DenseMatrix m n α) (i j : Nat) : α :=
  M.data[i * n + j]!

/--
Unchecked row-major fast-path update.

The row and column are natural numbers, not typed `Fin` indices. This function
computes the row-major offset `i * n + j` without carrying a bounds proof, so
callers are responsible for ensuring the offset is inside the backing vector.
Prefer `set` when typed indices are available.
-/
@[inline]
def set! {m n : Nat} {α : Type u} [Inhabited α] (M : DenseMatrix m n α) (i j : Nat) (val : α)
    : DenseMatrix m n α where
  data := M.data.set! (i * n + j) val

/--
Read an entry using checked row-major indexing.

The value-level index is computed by `rowMajorIndex`; the paired proof
`rowMajorIndex_lt` turns that offset into a `Fin (m * n)`. Thus `get` has no
unchecked fallback and no default value.
-/
@[inline]
def get {m n : Nat} {α : Type u} (A : DenseMatrix m n α) (i : Fin m) (j : Fin n) : α :=
  A.data.get ⟨rowMajorIndex i j, rowMajorIndex_lt i j⟩

/--
Return a matrix with one entry updated.

The update uses the same checked row-major offset as `get`; the `Vector` result
keeps the same length by construction.
-/
@[inline]
def set {m n : Nat} {α : Type u} (A : DenseMatrix m n α) (i : Fin m) (j : Fin n) (x : α) :
    DenseMatrix m n α where
  data := A.data.set (rowMajorIndex i j) x (rowMajorIndex_lt i j)

instance {m n : Nat} {α : Type u} [Inhabited α] [ToString α] : ToString (DenseMatrix m n α) where
  toString A := Id.run do
    let mut rows : Array String := #[]
    for i in [0:m] do
      let mut rowStr : Array String := #[]
      for j in [0:n] do
        -- Access the element using your existing `get!` function
        let val := A.get! i j
        rowStr := rowStr.push (toString val)

      -- Format the current row, e.g., "[1, 2, 3]"
      let rowFormatted := "![" ++ String.intercalate ", " rowStr.toList ++ "]"
      rows := rows.push rowFormatted

    -- Join all rows with a newline and a leading space for alignment
    return "![" ++ String.intercalate ", " rows.toList ++ "]"

/--
Convert a dense matrix to mathlib's function-backed matrix type.

`Matrix (Fin m) (Fin n) α` is represented extensionally as a function from row
and column indices to entries. The conversion exposes each dense entry through
`get`, preserving checked row-major access while hiding the underlying storage.
-/
def toMatrix {m n : Nat} {α : Type u} (A : DenseMatrix m n α) :
    Matrix (Fin m) (Fin n) α :=
  Matrix.of fun i j => A.get i j

-- Flatten/unflatten arithmetic for row-major storage. Given a flat index
-- `x < m * n`, division by `n` recovers the row and modulo `n` recovers the
-- column. The modulo proof first rules out `n = 0`: otherwise `m * n = 0`,
-- contradicting the existence of such an `x`.

-- The quotient of a flat in-bounds index by the row width is a valid row
-- index.
private theorem index_div_lt {m n : Nat} {x : Nat} (h : x < m * n) : x / n < m := by
  rw [Nat.mul_comm] at h
  exact Nat.div_lt_of_lt_mul h

-- The remainder of a flat in-bounds index by the row width is a valid column
-- index.
private theorem index_mod_lt {m n : Nat} {x : Nat} (h : x < m * n) : x % n < n := by
  have hn : n ≠ 0 := by
    intro hn
    subst n
    simp at h
  exact Nat.mod_lt x (Nat.pos_of_ne_zero hn)

-- Flattening the row and column recovered from a flat index returns that index.
private theorem rowMajorIndex_unflatten {m n : Nat} (x : Fin (m * n)) :
    rowMajorIndex
        (m := m) (n := n)
        ⟨x.val / n, index_div_lt x.isLt⟩
        ⟨x.val % n, index_mod_lt x.isLt⟩ = x.val := by
  unfold rowMajorIndex
  rw [Nat.mul_comm (x.val / n) n, Nat.div_add_mod]

-- When a proof starts from typed indices `i : Fin m` and `j : Fin n`, the
-- witness `j` proves `n > 0`: `0 <= j.val < n`. That positivity is what lets
-- the division and modulo simplification lemmas recover `i.val` and `j.val`
-- from the flattened row-major offset.

-- Dividing a flattened typed row-major index by the row width recovers the
-- row.
private theorem rowMajorIndex_div {m n : Nat} (i : Fin m) (j : Fin n) :
    rowMajorIndex i j / n = i.val := by
  unfold rowMajorIndex
  rw [Nat.mul_comm i.val n]
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le j.val) j.isLt
  rw [Nat.mul_add_div hn, Nat.div_eq_of_lt j.isLt, Nat.add_zero]

-- Taking a flattened typed row-major index modulo the row width recovers the
-- column.
private theorem rowMajorIndex_mod {m n : Nat} (i : Fin m) (j : Fin n) :
    rowMajorIndex i j % n = j.val := by
  unfold rowMajorIndex
  rw [Nat.mul_comm i.val n]
  rw [Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt j.isLt]

/--
Convert a function-backed matrix to row-major dense storage.

`Vector.ofFn` enumerates every `x : Fin (m * n)` exactly once. Each flat index
is unflattened as `(x / n, x % n)`, then the helper lemmas supply the `Fin m`
and `Fin n` bounds.
-/
def ofMatrix {m n : Nat} {α : Type u} (M : Matrix (Fin m) (Fin n) α) :
    DenseMatrix m n α where
  data := Vector.ofFn fun x : Fin (m * n) =>
    M ⟨x.val / n, index_div_lt x.isLt⟩ ⟨x.val % n, index_mod_lt x.isLt⟩

-- Reading a dense matrix built from a function-backed matrix returns the source
-- entry.
private theorem get_ofMatrix {m n : Nat} {α : Type u}
    (M : Matrix (Fin m) (Fin n) α) (i : Fin m) (j : Fin n) :
    get (ofMatrix M) i j = M i j := by
  simp [ofMatrix, get, Vector.get, rowMajorIndex_div, rowMajorIndex_mod]

-- Reading storage through the unflattened row and column returns the same flat
-- slot.
private theorem get_unflatten {m n : Nat} {α : Type u}
    (data : Vector α (m * n)) (x : Fin (m * n)) :
    get { data := data }
        ⟨x.val / n, index_div_lt x.isLt⟩
        ⟨x.val % n, index_mod_lt x.isLt⟩ = data.get x := by
  have hflat :
      (⟨rowMajorIndex
          ⟨x.val / n, index_div_lt x.isLt⟩
          ⟨x.val % n, index_mod_lt x.isLt⟩,
        rowMajorIndex_lt
          ⟨x.val / n, index_div_lt x.isLt⟩
          ⟨x.val % n, index_mod_lt x.isLt⟩⟩ : Fin (m * n)) = x := by
    apply Fin.ext
    exact rowMajorIndex_unflatten x
  simp [get, hflat]

/--
Round trip from `Matrix` to `DenseMatrix` and back.

The proof is extensional in the row and column indices. After unfolding the two
conversions, the division and modulo helper lemmas show that reading the
row-major slot created for `(i, j)` returns exactly `M i j`.
-/
@[simp]
theorem toMatrix_ofMatrix {m n : Nat} {α : Type u} (M : Matrix (Fin m) (Fin n) α) :
    toMatrix (ofMatrix M) = M := by
  ext i j
  exact get_ofMatrix M i j

/--
Round trip from `DenseMatrix` to `Matrix` and back.

After destructing the dense matrix, it is enough to prove equality of the
backing vectors pointwise. The `get_unflatten` helper identifies each recreated
slot with the original flat slot.
-/
@[simp]
theorem ofMatrix_toMatrix {m n : Nat} {α : Type u} (A : DenseMatrix m n α) :
    ofMatrix (toMatrix A) = A := by
  cases A with
  | mk data =>
    rw [DenseMatrix.mk.injEq]
    apply Vector.ext
    intro x hx
    simp [ofMatrix, toMatrix, get_unflatten, Vector.get]

/-- Define a `DenseMatrix` using a function. -/
def of {m n : Nat} {α : Type u} (f : Fin m → Fin n → α) : DenseMatrix m n α :=
  .ofMatrix (Matrix.of f)

def add {m n : Nat} {α : Type u} [Add α] (A B : DenseMatrix m n α) : DenseMatrix m n α where
  data := A.data.zipWith (· + ·) B.data

def smul {m n : Nat} {α : Type u} [Mul α] (c : α) (M : DenseMatrix m n α) : DenseMatrix m n α where
  data := M.data.map (fun x => c * x)

private def dot {m k n : Nat} {α : Type u} [Add α] [Mul α]
    (sum : α) (i : Fin m) (j : Fin n) (l : Fin k)
    (A : DenseMatrix m k α) (B : DenseMatrix k n α) : α :=
  if h: l + 1 < k then
    dot (sum + (A.get i l * B.get l j)) i j ⟨l+1, by simp [h]⟩ A B
  else
    sum + (A.get i l * B.get l j)

/-- If `i * n + j = out.size` and `j + 1 = n` then `(i + 1) * n = (out.push entry).size`. -/
private lemma row_size_invariant {α : Type u} (out : Array α) (i j n : Nat)
    (h_size : out.size = i * n + j) (hj : j + 1 = n) (entry : α)
    : (out.push entry).size = (i + 1) * n := by
  simp only [Array.size_push, h_size]
  suffices j + 1 = n from by grind
  exact hj

/-- The last `Array α` returned by `mul_helper` has size `m * n`. -/
private lemma mul_helper_size_invariant {m n : Nat} {α : Type u} (out : Array α) (i j : Nat)
    (h_size : out.size = i * n + j) (hi : i + 1 = m) (hj : j + 1 = n) (entry : α)
    : (out.push entry).size = m * n := by
  rw [Array.size_push, h_size, add_assoc, hj]
  nth_rewrite 2 [←one_mul n]
  rw [←right_distrib, hi]

/-- Computes entry ij of `A * B` and appends it to the resulting matrix. -/
private def mul_helper {m k n : Nat} {α : Type u} [Zero α] [Add α] [Mul α]
    [NeZero m] [NeZero k] [NeZero n]
    (out : Array α) (i j : Nat) (A : DenseMatrix m k α) (B : DenseMatrix k n α)
    (h_size : out.size = i * n + j) (hi : m ≥ i + 1) (hj : n ≥ j + 1)
    : Vector α (m * n) :=
  let entry := dot 0 ⟨i, by exact Nat.lt_of_succ_le hi⟩ ⟨j, by exact Nat.lt_of_succ_le hj⟩ 0 A B
  if h₁ : j + 1 < n then
    mul_helper (out.push entry) i (j+1) A B (by aesop) hi (by exact Nat.succ_le_of_lt h₁)
  else if h₂ : i + 1 < m then
    let hj' : j + 1 = n := by apply le_antisymm hj (by push Not at h₁; exact h₁)
    mul_helper (out.push entry) (i+1) 0 A B
      (row_size_invariant out i j n h_size hj' entry)
      (by exact Nat.succ_le_of_lt h₂) NeZero.one_le
  else
    let hi' : i + 1 = m := by apply le_antisymm hi (by push Not at h₂; exact h₂)
    let hj' : j + 1 = n := by apply le_antisymm hj (by push Not at h₁; exact h₁)
    ⟨out.push entry, mul_helper_size_invariant out i j h_size hi' hj' entry⟩

/--
Optimized dense matrix multiplication for nonempty dimensions.

This path builds the output storage sequentially and computes each dot product
with checked dense reads. It requires `[NeZero m] [NeZero k] [NeZero n]` so the
recursive helper can start at row, column, and dot-product index `0`.
-/
def mul {m k n : Nat} {α : Type u} [Inhabited α] [Zero α] [Add α] [Mul α]
    [NeZero m] [NeZero k] [NeZero n]
    (A : DenseMatrix m k α) (B : DenseMatrix k n α) : DenseMatrix m n α where
  data := mul_helper (Array.mkEmpty (m * n)) 0 0 A B (by simp) NeZero.one_le NeZero.one_le

/-- The last `Array α` returned by `transpose_helper` has size `n * m`. -/
private lemma transpose_helper_size_invariant {m n : Nat} {α : Type u} (out : Array α) (i j : Nat)
    (h_size : out.size = j * m + i) (hi : i + 1 = m) (hj : j + 1 = n) (entry : α)
    : (out.push entry).size = n * m := by
  rw [Array.size_push, h_size, add_assoc, hi]
  nth_rewrite 2 [←one_mul m]
  rw [←right_distrib, hj]

/-- Computes entry `ij` of M.T and appends it to the resulting matrix. -/
private def transpose_helper {m n : Nat} {α : Type u} [NeZero m] [NeZero n]
    (out : Array α) (i j : Nat) (M : DenseMatrix m n α)
    (h_size : out.size = j * m + i) (hi : m ≥ i + 1) (hj : n ≥ j + 1)
    :  Vector α (n * m) :=
  let entry := M.get ⟨i, by exact Nat.lt_of_succ_le hi⟩ ⟨j, by exact Nat.lt_of_succ_le hj⟩
  if h₁ : i + 1 < m then
    transpose_helper (out.push entry) (i+1) j M (by aesop) (by exact Nat.succ_le_of_lt h₁) hj
  else if h₂ : j + 1 < n then
    let hj' : i + 1 = m := by apply le_antisymm hi (by push Not at h₁; exact h₁)
    transpose_helper (out.push entry) 0 (j+1) M
      (row_size_invariant out j i m h_size hj' entry)
      NeZero.one_le (by exact Nat.succ_le_of_lt h₂)
  else
    let hi' : i + 1 = m := by apply le_antisymm hi (by push Not at h₁; exact h₁)
    let hj' : j + 1 = n := by apply le_antisymm hj (by push Not at h₂; exact h₂)
    ⟨out.push entry, transpose_helper_size_invariant out i j h_size hi' hj' entry⟩

def transpose {m n : Nat} {α : Type u} [NeZero m] [NeZero n]
    (M : DenseMatrix m n α) : DenseMatrix n m α :=
  { data := transpose_helper (Array.mkEmpty (n * m)) 0 0 M (by simp) NeZero.one_le NeZero.one_le }

end DenseMatrix
