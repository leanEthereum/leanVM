import LeanVMTests.Cost.DecOf
import LeanVMTests.Cost.Decoder
import LeanVMTests.Cost.PMChain
import LeanVMTests.Cost.PMChainFFT
import LeanVMTests.Extraction.FFT
import LeanVMTests.Extraction.Fast
import LeanVMTests.Extraction.LanePM
import LeanVMTests.Extraction.Toy
import LeanVMTests.Extraction.ToyFast
import LeanVMTests.Extraction.ToyRadius
import LeanVMTests.Guest.CoreData
import LeanVMTests.Protocol.EndToEnd.Front.Layout
import LeanVMTests.Prover.Keccak
import LeanVMTests.Prover.Whir

/-!
# `test-runs`: the tests' runs, compiled

`lake exe test-runs` evaluates the checks too slow for the interpreter (`LeanVMTests/Runs.lean`):
whole decoder runs, toy protocol and prover runs, the guest's core data against its expansion.
Their inputs and expected values stay in their test modules; this lists them. They run on a few
threads, each printed with its time; `test-runs NAME…` runs those whose name contains a `NAME`.
Run it under `lake env` (as `lake exe` does): the core data is read from its `.olean`. The exit
code is `0` when every run passes.
-/

open Lean LeanVMTests

/-- Every module's runs, by module. -/
def modules : List (String × Runs) := [
  ("Cost.DecOf", Cost.DecOf.runs),
  ("Cost.Decoder", Cost.Decoder.runs),
  ("Cost.PMChain", Cost.PMChain.runs ++ Cost.PMChain.prices),
  ("Cost.PMChainFFT", Cost.PMChainFFT.runs),
  ("Extraction.FFT", Extraction.FFT.runs),
  ("Extraction.Fast", Extraction.Fast.runs),
  ("Extraction.LanePM", Extraction.LanePM.runs),
  ("Extraction.Toy", Extraction.Toy.runs),
  ("Extraction.ToyFast", Extraction.ToyFast.runs),
  ("Extraction.ToyRadius", Extraction.ToyRadius.runs),
  ("Protocol.EndToEnd.Front.Layout", Protocol.EndToEnd.Front.Layout.runs),
  ("Prover.Keccak", Prover.Keccak.runs),
  ("Prover.Whir", Prover.Whir.runs)]

/-- `Guest/CoreData.lean`'s check, on the environment of `LeanVM.Guest.CoreData`. -/
def coreData : IO Bool := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `LeanVM.Guest.CoreData }] {} 0 (loadExts := false)
  match Guest.CoreData.check env with
  | .ok () => return true
  | .error e => IO.eprintln e; return false

/-- Worker threads: a thread reserves address space, and check-all caps it. -/
def workers : Nat := 8

/-- The driver. -/
def main (args : List String) : IO UInt32 := do
  let runs := modules.flatMap fun (m, rs) ↦ rs.map fun (n, f) ↦ (s!"{m}: {n}", IO.lazyPure f)
  let runs := runs ++ [("Guest.CoreData: the core data is the renumbered expansion", coreData)]
  let runs := (runs.filter fun (n, _) ↦ args.isEmpty || args.any fun a ↦ (n.splitOn a).length > 1).zipIdx
  let worker (w : Nat) : IO (List (Nat × String × Bool × Nat)) :=
    (runs.filter (·.2 % workers == w)).mapM fun ((n, run), i) ↦ do
      let t0 ← IO.monoMsNow
      let ok ← run
      return (i, n, ok, (← IO.monoMsNow) - t0)
  let tasks ← (List.range workers).mapM fun w ↦ IO.asTask (prio := .dedicated) (worker w)
  let mut results : Array (Nat × String × Bool × Nat) := #[]
  for t in tasks do
    results := results ++ (← IO.ofExcept (← IO.wait t))
  let mut failed := 0
  for (_, n, ok, ms) in results.qsort (·.1 < ·.1) do
    IO.println s!"{n}: {if ok then "ok" else "FAILED"} ({ms} ms)"
    if !ok then failed := failed + 1
  IO.println s!"{runs.length - failed} of {runs.length} runs passed"
  return if failed == 0 then 0 else 1
