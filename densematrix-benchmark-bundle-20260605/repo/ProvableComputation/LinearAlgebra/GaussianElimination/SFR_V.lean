import Mathlib.Data.Vector.Basic
import Mathlib

variable {R : Type} [Field R] [DecidableEq R]
variable {a b : ℕ}

def swapRowV (M : Vector (Vector R b) a)
    (row1 row2 : Fin a) : Vector (Vector R b) a :=
  let r1 := M.get row1
  let r2 := M.get row2
  let M' := M.set row1 r2
  M'.set row2 r1

#eval swapRowV
  ⟨#[⟨#[1,2,3], rfl⟩, ⟨#[4,5,6], rfl⟩], rfl⟩
  (0: Fin 2) (1: Fin 2)

def factorV (M : Vector (Vector R b) a)
    (i : Fin a) (c : R) : Vector (Vector R b) a :=
  let row := M.get i
  let scaledRow := row.map (fun entry => c * entry)
  M.set i scaledRow

#eval factorV
  (⟨#[⟨#[1,2,3], rfl⟩, ⟨#[4,5,6], rfl⟩], rfl⟩ : Vector (Vector ℚ 3) 2)
  (0 : Fin 2) 3

def replaceV (M : Vector (Vector R b) a)
    (use toReplace : Fin a) (k : R) : Vector (Vector R b) a :=
  if use = toReplace then
    factorV M toReplace (k + 1)
  else
    let srcRow := M.get use
    let tgtRow := M.get toReplace
    let newRow := Vector.ofFn (fun j => tgtRow.get j + k * srcRow.get j)
    M.set toReplace newRow

#eval replaceV
  (⟨#[⟨#[1,2,3], rfl⟩, ⟨#[4,5,6], rfl⟩], rfl⟩ : Vector (Vector ℚ 3) 2)
  (0 : Fin 2) (1 : Fin 2) 2
  