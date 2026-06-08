import ProvableComputation.LinearAlgebra.DenseMatrix.Defs
import Lean.Data.Json

/-!
# DenseMatrix benchmark harness

This module is intentionally outside the public library import surface.  It
provides deterministic inputs, checksum-based full-output evaluation, and a
small JSONL runner for comparing compiled `DenseMatrix` kernels against
function-backed mathlib `Matrix` expressions.
-/

namespace DenseMatrixBench

open Lean System

def mixNat (acc x : Nat) : Nat :=
  (acc * 16777619 + x + 1) % 2147483647

def natCode (x : Nat) : Nat :=
  x

def intCode (x : Int) : Nat :=
  x.natAbs * 2 + if x < 0 then 1 else 0

def natEntry (seed i j : Nat) : Nat :=
  ((seed + (i + 1) * 73 + (j + 1) * 193 + i * j * 17) % 997) + 1

def intEntry (seed i j : Nat) : Int :=
  Int.ofNat ((seed + (i + 1) * 97 + (j + 1) * 53 + i * j * 29) % 401) - 200

def matrixNat (m n seed : Nat) : Matrix (Fin m) (Fin n) Nat :=
  Matrix.of fun i j => natEntry seed i.val j.val

def matrixInt (m n seed : Nat) : Matrix (Fin m) (Fin n) Int :=
  Matrix.of fun i j => intEntry seed i.val j.val

def denseNat (m n seed : Nat) : DenseMatrix m n Nat :=
  DenseMatrix.of fun i j => natEntry seed i.val j.val

def denseInt (m n seed : Nat) : DenseMatrix m n Int :=
  DenseMatrix.of fun i j => intEntry seed i.val j.val

def checksumDenseUnchecked {m n : Nat} {α : Type} [Inhabited α]
    (encode : α → Nat) (A : DenseMatrix m n α) : Nat :=
  Id.run do
    let mut acc := 2166136261
    for i in [0:m] do
      for j in [0:n] do
        acc := mixNat acc (encode (A.get! i j))
    return acc

def checksumDenseChecked {m n : Nat} {α : Type}
    (encode : α → Nat) (A : DenseMatrix m n α) : Nat :=
  Id.run do
    let mut acc := 2166136261
    for i in List.finRange m do
      for j in List.finRange n do
        acc := mixNat acc (encode (A.get i j))
    return acc

def checksumMatrix {m n : Nat} {α : Type}
    (encode : α → Nat) (A : Matrix (Fin m) (Fin n) α) : Nat :=
  Id.run do
    let mut acc := 2166136261
    for i in List.finRange m do
      for j in List.finRange n do
        acc := mixNat acc (encode (A i j))
    return acc

def runDenseConstructNat (n : Nat) : Nat :=
  checksumDenseUnchecked natCode (denseNat n n 11)

def runMatrixConstructNat (n : Nat) : Nat :=
  checksumMatrix natCode (matrixNat n n 11)

def runDenseOfMatrixNat (n : Nat) : Nat :=
  checksumDenseUnchecked natCode (DenseMatrix.ofMatrix (matrixNat n n 13))

def runDenseToMatrixNat (n : Nat) : Nat :=
  checksumMatrix natCode (DenseMatrix.toMatrix (denseNat n n 17))

def runDenseGetNatFrom {m n : Nat} (A : DenseMatrix m n Nat) : Nat :=
  checksumDenseChecked natCode A

def runMatrixGetNatFrom {m n : Nat} (A : Matrix (Fin m) (Fin n) Nat) : Nat :=
  checksumMatrix natCode A

def runDenseAddIntFrom {m n : Nat} (A B : DenseMatrix m n Int) : Nat :=
  checksumDenseUnchecked intCode (DenseMatrix.add A B)

def runMatrixAddIntFrom {m n : Nat} (A B : Matrix (Fin m) (Fin n) Int) : Nat :=
  checksumMatrix intCode (A + B)

def runDenseSmulIntFrom {m n : Nat} (A : DenseMatrix m n Int) : Nat :=
  checksumDenseUnchecked intCode (DenseMatrix.smul (-7 : Int) A)

def runMatrixSmulIntFrom {m n : Nat} (A : Matrix (Fin m) (Fin n) Int) : Nat :=
  checksumMatrix intCode (Matrix.of fun i j => (-7 : Int) * A i j)

def runDenseTransposeIntFrom {m n : Nat} (A : DenseMatrix m n Int) : Nat :=
  if hm : m = 0 then
    0
  else if hn : n = 0 then
    0
  else
    haveI : NeZero m := ⟨hm⟩
    haveI : NeZero n := ⟨hn⟩
    checksumDenseUnchecked intCode (DenseMatrix.transpose A)

def runMatrixTransposeIntFrom {m n : Nat} (A : Matrix (Fin m) (Fin n) Int) : Nat :=
  checksumMatrix intCode A.transpose

def runDenseMulNatFrom {m k n : Nat} (A : DenseMatrix m k Nat) (B : DenseMatrix k n Nat) :
    Nat :=
  if hm : m = 0 then
    0
  else if hk : k = 0 then
    0
  else if hn : n = 0 then
    0
  else
    haveI : NeZero m := ⟨hm⟩
    haveI : NeZero k := ⟨hk⟩
    haveI : NeZero n := ⟨hn⟩
    checksumDenseUnchecked natCode (DenseMatrix.mul A B)

def runMatrixMulNatFrom {m k n : Nat}
    (A : Matrix (Fin m) (Fin k) Nat) (B : Matrix (Fin k) (Fin n) Nat) : Nat :=
  checksumMatrix natCode (A * B)

structure Stats where
  count : Nat
  minMs : Float
  medianMs : Float
  meanMs : Float
  p95Ms : Float
  maxMs : Float
  stddevMs : Float
  cv : Float

def summarize (samples : Array Nat) : Stats :=
  if samples.isEmpty then
    { count := 0
      minMs := 0.0
      medianMs := 0.0
      meanMs := 0.0
      p95Ms := 0.0
      maxMs := 0.0
      stddevMs := 0.0
      cv := 0.0 }
  else
    let ms := samples.map fun n => n.toFloat / 1000000.0
    let sorted := ms.qsort (fun a b => a < b)
    let count := samples.size
    let percentileIndex (pct : Nat) : Nat :=
      let idx := (count * pct) / 100
      if idx < count then idx else count - 1
    let sum := ms.foldl (fun acc x => acc + x) 0.0
    let mean := sum / count.toFloat
    let variance := ms.foldl (fun acc x =>
      let delta := x - mean
      acc + delta * delta) 0.0 / count.toFloat
    let stddev := Float.sqrt variance
    { count := count
      minMs := sorted[0]!
      medianMs := sorted[count / 2]!
      meanMs := mean
      p95Ms := sorted[percentileIndex 95]!
      maxMs := sorted[count - 1]!
      stddevMs := stddev
      cv := if mean == 0.0 then 0.0 else stddev / mean }

structure Config where
  quick : Bool := false
  repeatsOpt : Option Nat := none
  warmupsOpt : Option Nat := none
  sizesOpt : Option (List Nat) := none
  jsonl : Option String := none
  append : Bool := false
  skipExisting : Bool := false
  quiet : Bool := false
  showHelp : Bool := false

def defaultSizes (quick : Bool) : List Nat :=
  if quick then [4, 8] else [4, 8, 16, 24, 32, 48, 64, 80, 96]

def effectiveRepeats (cfg : Config) : Nat :=
  cfg.repeatsOpt.getD (if cfg.quick then 3 else 30)

def effectiveWarmups (cfg : Config) : Nat :=
  cfg.warmupsOpt.getD (if cfg.quick then 1 else 5)

def effectiveSizes (cfg : Config) : List Nat :=
  cfg.sizesOpt.getD (defaultSizes cfg.quick)

def trimString (s : String) : String :=
  s.trimAscii.toString

def parseNatArg (flag value : String) : Except String Nat :=
  match (trimString value).toNat? with
  | some n => .ok n
  | none => .error s!"{flag} expects a natural number, got '{value}'"

def parseNatList (value : String) : Except String (List Nat) :=
  let parts := value.splitOn ","
  let rec go : List String → List Nat → Except String (List Nat)
    | [], acc => .ok acc.reverse
    | part :: rest, acc =>
        let trimmed := trimString part
        if trimmed.isEmpty then
          .error s!"--sizes contains an empty entry: '{value}'"
        else
          match trimmed.toNat? with
          | some n => go rest (n :: acc)
          | none => .error s!"--sizes expects comma-separated natural numbers, got '{part}'"
  go parts []

partial def parseArgsAux : List String → Config → Except String Config
  | [], cfg => .ok cfg
  | "--help" :: _, cfg => .ok { cfg with showHelp := true }
  | "-h" :: _, cfg => .ok { cfg with showHelp := true }
  | "--quick" :: rest, cfg => parseArgsAux rest { cfg with quick := true }
  | "--repeats" :: value :: rest, cfg => do
      parseArgsAux rest { cfg with repeatsOpt := some (← parseNatArg "--repeats" value) }
  | "--repeats" :: [], _ => .error "--repeats requires a value"
  | "--warmups" :: value :: rest, cfg => do
      parseArgsAux rest { cfg with warmupsOpt := some (← parseNatArg "--warmups" value) }
  | "--warmups" :: [], _ => .error "--warmups requires a value"
  | "--sizes" :: value :: rest, cfg => do
      parseArgsAux rest { cfg with sizesOpt := some (← parseNatList value) }
  | "--sizes" :: [], _ => .error "--sizes requires a comma-separated value"
  | "--jsonl" :: value :: rest, cfg =>
      parseArgsAux rest { cfg with jsonl := some value }
  | "--jsonl" :: [], _ => .error "--jsonl requires a path or '-'"
  | "--append" :: rest, cfg => parseArgsAux rest { cfg with append := true }
  | "--skip-existing" :: rest, cfg =>
      parseArgsAux rest { cfg with skipExisting := true, append := true }
  | "--quiet" :: rest, cfg => parseArgsAux rest { cfg with quiet := true }
  | arg :: _, _ => .error s!"unknown argument '{arg}'"

def parseArgs (args : List String) : Except String Config :=
  parseArgsAux args {}

def usage : String :=
  String.intercalate "\n" [
    "Usage: lake exe densematrix_bench [options]",
    "",
    "Options:",
    "  --quick              Use sizes 4,8 and short repeats.",
    "  --repeats N          Number of measured repeats.",
    "  --warmups N          Number of warmup runs.",
    "  --sizes A,B,C        Square matrix sizes.",
    "  --jsonl PATH         Write JSONL output to PATH; '-' means stdout.",
    "  --append             Append JSONL records instead of overwriting PATH.",
    "  --skip-existing      Resume by skipping records already present in PATH.",
    "  --quiet              Suppress progress messages on stderr.",
    "  --help               Show this help."
  ]

def recordKeyParts (backend operation element setupPolicy : String)
    (rows cols inner warmups repeats : Nat) : String :=
  String.intercalate "|" [
    backend,
    operation,
    element,
    setupPolicy,
    toString rows,
    toString cols,
    toString inner,
    toString warmups,
    toString repeats
  ]

def recordKey (cfg : Config) (backend operation element setupPolicy : String)
    (rows cols inner : Nat) : String :=
  recordKeyParts backend operation element setupPolicy rows cols inner
    (effectiveWarmups cfg) (effectiveRepeats cfg)

def jsonRecordKey? (j : Json) : Except String String := do
  let backend ← j.getObjValAs? String "backend"
  let operation ← j.getObjValAs? String "operation"
  let element ← j.getObjValAs? String "element"
  let setupPolicy ← j.getObjValAs? String "setup_policy"
  let rows ← j.getObjValAs? Nat "rows"
  let cols ← j.getObjValAs? Nat "cols"
  let inner ← j.getObjValAs? Nat "inner"
  let warmups ← j.getObjValAs? Nat "warmups"
  let repeats ← j.getObjValAs? Nat "repeats"
  return recordKeyParts backend operation element setupPolicy rows cols inner warmups repeats

def loadExistingKeys (cfg : Config) : IO (List String) := do
  if !cfg.skipExisting then
    return []
  match cfg.jsonl with
  | none => return []
  | some "-" => return []
  | some path =>
      let filePath := FilePath.mk path
      if !(← filePath.pathExists) then
        return []
      let content ← IO.FS.readFile filePath
      let mut keys : List String := []
      let mut lineNo := 0
      for line in content.splitOn "\n" do
        lineNo := lineNo + 1
        let trimmed := trimString line
        if !trimmed.isEmpty then
          match Json.parse trimmed with
          | .ok json =>
              match jsonRecordKey? json with
              | .ok key => keys := key :: keys
              | .error err =>
                  unless cfg.quiet do
                    IO.eprintln s!"warning: ignoring JSONL line {lineNo}: {err}"
          | .error err =>
              unless cfg.quiet do
                IO.eprintln s!"warning: ignoring unparsable JSONL line {lineNo}: {err}"
      return keys

def ensureParentDir (path : String) : IO Unit := do
  match (FilePath.mk path).parent with
  | none => pure ()
  | some parent => IO.FS.createDirAll parent

def jsonNatArray (xs : Array Nat) : String :=
  "[" ++ String.intercalate "," (xs.toList.map fun x => toString x) ++ "]"

def jsonLine (backend operation element setupPolicy : String)
    (rows cols inner warmups repeats checksum : Nat) (samples : Array Nat) (stats : Stats) :
    String :=
  "{" ++
  s!"\"backend\":\"{backend}\"," ++
  s!"\"operation\":\"{operation}\"," ++
  s!"\"element\":\"{element}\"," ++
  s!"\"setup_policy\":\"{setupPolicy}\"," ++
  s!"\"rows\":{rows}," ++
  s!"\"cols\":{cols}," ++
  s!"\"inner\":{inner}," ++
  s!"\"warmups\":{warmups}," ++
  s!"\"repeats\":{repeats}," ++
  s!"\"checksum\":{checksum}," ++
  s!"\"samples_unit\":\"ns\"," ++
  s!"\"samples_ns\":{jsonNatArray samples}," ++
  s!"\"min_ms\":{stats.minMs}," ++
  s!"\"median_ms\":{stats.medianMs}," ++
  s!"\"mean_ms\":{stats.meanMs}," ++
  s!"\"p95_ms\":{stats.p95Ms}," ++
  s!"\"max_ms\":{stats.maxMs}," ++
  s!"\"stddev_ms\":{stats.stddevMs}," ++
  s!"\"cv\":{stats.cv}" ++
  "}"

@[noinline]
def forceNatForTiming (x : Nat) : IO Unit := do
  if x == 0 then
    IO.sleep 0
  else
    pure ()

def progress (cfg : Config) (msg : String) : IO Unit := do
  unless cfg.quiet do
    IO.eprintln msg

def measurePure (cfg : Config) (backend operation element setupPolicy : String)
    (rows cols inner : Nat) (action : Unit → Nat) : IO String := do
  let warmups := effectiveWarmups cfg
  let repeats := effectiveRepeats cfg
  let label :=
    s!"{backend}/{operation}/{element}/{setupPolicy} rows={rows} cols={cols} inner={inner}"
  for i in [0:warmups] do
    progress cfg s!"progress warmup {i + 1}/{warmups} {label}"
    forceNatForTiming (mixNat 0 (action ()))
  let mut samples : Array Nat := #[]
  let mut checksum := 0
  for i in [0:repeats] do
    progress cfg s!"progress repeat {i + 1}/{repeats} {label}"
    let start ← IO.monoNanosNow
    let nextChecksum := mixNat checksum (action ())
    forceNatForTiming nextChecksum
    let stop ← IO.monoNanosNow
    checksum := nextChecksum
    samples := samples.push (stop - start)
  return jsonLine backend operation element setupPolicy rows cols inner warmups repeats checksum
    samples (summarize samples)

def runMeasuredRecord (cfg : Config) (emit : String → IO Unit) (existingKeys : List String)
    (backend operation element setupPolicy : String) (rows cols inner : Nat)
    (action : Unit → Nat) : IO (List String) := do
  let key := recordKey cfg backend operation element setupPolicy rows cols inner
  if existingKeys.any (fun existing => existing == key) then
    progress cfg s!"skip existing {key}"
    return existingKeys
  else
    progress cfg s!"start {key}"
    let line ← measurePure cfg backend operation element setupPolicy rows cols inner action
    emit line
    progress cfg s!"finish {key}"
    return key :: existingKeys

def appendSquareBenchmarks (cfg : Config) (emit : String → IO Unit)
    (existingKeys : List String) (n : Nat) : IO (List String) := do
  let mut existingKeys := existingKeys
  existingKeys ← runMeasuredRecord cfg emit existingKeys
    "dense_core" "construct" "Nat" "setup_inclusive" n n 0
    (fun _ => runDenseConstructNat n)
  existingKeys ← runMeasuredRecord cfg emit existingKeys
    "mathlib_matrix" "construct" "Nat" "setup_inclusive" n n 0
    (fun _ => runMatrixConstructNat n)
  existingKeys ← runMeasuredRecord cfg emit existingKeys
    "dense_conversion" "ofMatrix" "Nat" "setup_inclusive" n n 0
    (fun _ => runDenseOfMatrixNat n)
  existingKeys ← runMeasuredRecord cfg emit existingKeys
    "dense_conversion" "toMatrix" "Nat" "setup_inclusive" n n 0
    (fun _ => runDenseToMatrixNat n)
  let denseNatGet := denseNat n n 19
  let matrixNatGet := matrixNat n n 19
  let denseIntA := denseInt n n 43
  let denseIntB := denseInt n n 47
  let denseIntSmul := denseInt n n 53
  let matrixIntA := matrixInt n n 43
  let matrixIntB := matrixInt n n 47
  let matrixIntSmul := matrixInt n n 53
  existingKeys ← runMeasuredRecord cfg emit existingKeys
    "dense_core" "get" "Nat" "prebuilt_inputs" n n 0
    (fun _ => runDenseGetNatFrom denseNatGet)
  existingKeys ← runMeasuredRecord cfg emit existingKeys
    "mathlib_matrix" "get" "Nat" "prebuilt_inputs" n n 0
    (fun _ => runMatrixGetNatFrom matrixNatGet)
  existingKeys ← runMeasuredRecord cfg emit existingKeys
    "dense_core" "add" "Int" "prebuilt_inputs" n n 0
    (fun _ => runDenseAddIntFrom denseIntA denseIntB)
  existingKeys ← runMeasuredRecord cfg emit existingKeys
    "mathlib_matrix" "add" "Int" "prebuilt_inputs" n n 0
    (fun _ => runMatrixAddIntFrom matrixIntA matrixIntB)
  existingKeys ← runMeasuredRecord cfg emit existingKeys
    "dense_core" "smul" "Int" "prebuilt_inputs" n n 0
    (fun _ => runDenseSmulIntFrom denseIntSmul)
  existingKeys ← runMeasuredRecord cfg emit existingKeys
    "mathlib_matrix" "smul" "Int" "prebuilt_inputs" n n 0
    (fun _ => runMatrixSmulIntFrom matrixIntSmul)
  existingKeys ← runMeasuredRecord cfg emit existingKeys
    "dense_core" "transpose" "Int" "prebuilt_inputs" n n 0
    (fun _ => runDenseTransposeIntFrom denseIntA)
  existingKeys ← runMeasuredRecord cfg emit existingKeys
    "mathlib_matrix" "transpose" "Int" "prebuilt_inputs" n n 0
    (fun _ => runMatrixTransposeIntFrom matrixIntA)
  if n = 0 then
    return existingKeys
  else
    let denseNatMulA := denseNat n n 61
    let denseNatMulB := denseNat n n 67
    let matrixNatMulA := matrixNat n n 61
    let matrixNatMulB := matrixNat n n 67
    existingKeys ← runMeasuredRecord cfg emit existingKeys
      "dense_core" "mul_square" "Nat" "prebuilt_inputs" n n n
      (fun _ => runDenseMulNatFrom denseNatMulA denseNatMulB)
    existingKeys ← runMeasuredRecord cfg emit existingKeys
      "mathlib_matrix" "mul_square" "Nat" "prebuilt_inputs" n n n
      (fun _ => runMatrixMulNatFrom matrixNatMulA matrixNatMulB)
    return existingKeys

def runBenchmarksWithEmitter (cfg : Config) (emit : String → IO Unit) : IO Unit := do
  let mut existingKeys ← loadExistingKeys cfg
  for n in effectiveSizes cfg do
    existingKeys ← appendSquareBenchmarks cfg emit existingKeys n

def runBenchmarksStreaming (cfg : Config) : IO Unit := do
  match cfg.jsonl with
  | none => runBenchmarksWithEmitter cfg (fun line => IO.println line)
  | some "-" => runBenchmarksWithEmitter cfg (fun line => IO.println line)
  | some path =>
      ensureParentDir path
      let mode := if cfg.append || cfg.skipExisting then IO.FS.Mode.append else IO.FS.Mode.write
      let handle ← IO.FS.Handle.mk path mode
      runBenchmarksWithEmitter cfg (fun line => do
        handle.putStrLn line
        handle.flush)

end DenseMatrixBench
