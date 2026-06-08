import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Determinant
import Init.Data.Random

import ProvableComputation.LinearAlgebra.Determinant.Basic

/-!
# Determinant Runtime Comparator

This module contains profiler-oriented runtime comparisons for the executable determinant
implementations. It is kept out of the core library import graph.
-/

set_option profiler true

/-- Generate a reproducible rational matrix from a pseudo-random seed. -/
def randomMatrix (n : Nat) (seed : Nat) : Matrix (Fin n) (Fin n) Rat :=
  Matrix.of fun i j =>
    let gen := mkStdGen (seed + i.val * n + j.val)
    let (numNat, gen) := randNat gen 0 100
    let (isNeg, gen) := randNat gen 0 1
    let num : Int := if isNeg == 0 then (numNat : Int) else -(numNat : Int)
    let (denom, _) := randNat gen 1 100
    mkRat num denom

/-- Compare the runtime of `gaussDet` with mathlib's Leibniz-style determinant. -/
def benchmark (n : Nat) (samples : Nat) : IO Unit := do
  let mut totalRatio : Float := 0
  let mut validSamples : Nat := 0

  for i in [0:samples] do
    let mat := randomMatrix n (i * 12345)

    let startGaussDet ← IO.monoNanosNow
    let det := Matrix.gaussDet mat
    let _ := det
    let endGaussDet ← IO.monoNanosNow
    let timeGaussDet := (endGaussDet - startGaussDet).toFloat
    IO.println s!"gaussDet time: {timeGaussDet}"

    let startLeibnizDet ← IO.monoNanosNow
    let det := mat.det
    IO.println s!"{det}"
    let endLeibnizDet ← IO.monoNanosNow
    let timeLeibnizDet := (endLeibnizDet - startLeibnizDet).toFloat
    IO.println s!"det time: {timeLeibnizDet}"

    if timeGaussDet > 0 then
      totalRatio := totalRatio + (timeLeibnizDet / timeGaussDet)
      validSamples := validSamples + 1

  if validSamples > 0 then
    let avg := totalRatio / validSamples.toFloat
    IO.println s!"Average Ratio (Matrix.det / Matrix.gaussDet) for {n}x{n}: {avg}"
  else
    IO.println "Samples ran too quickly to measure in ms."

#time #eval benchmark 5 10
