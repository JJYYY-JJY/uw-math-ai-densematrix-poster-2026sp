import ProvableComputation.Bench.DenseMatrixBench

/-!
# DenseMatrix benchmark executable

Lake target root for compiled DenseMatrix benchmarks.
-/

open DenseMatrixBench

def main (args : List String) : IO Unit := do
  match parseArgs args with
  | .error err =>
      IO.eprintln err
      IO.eprintln usage
      IO.Process.exit 2
  | .ok cfg =>
      if cfg.showHelp then
        IO.println usage
      else
        runBenchmarksStreaming cfg
