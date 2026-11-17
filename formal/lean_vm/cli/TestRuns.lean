import LeanVMTests.Cost.DecoderChain
import LeanVMTests.Cost.DecoderPreTest
import LeanVMTests.Cost.DecoderReaders
import LeanVMTests.Guest.CoreDataCheck
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
  ("Cost.DecoderChain", Cost.DecoderChain.runs ++ Cost.DecoderChain.frameRuns),
  ("Cost.DecoderPreTest", Cost.DecoderPreTest.runs),
  ("Cost.DecoderReaders", Cost.DecoderReaders.runs),
  ("Protocol.EndToEnd.Front.Layout", Protocol.EndToEnd.Front.Layout.runs),
  ("Prover.Keccak", Prover.Keccak.runs),
  ("Prover.Whir", Prover.Whir.runs)]

/-- `Guest/CoreDataCheck.lean`'s check, on the environment of `LeanVM.Guest.CoreData`. -/
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
  let runs := (runs.filter fun (n, _) ↦ args.isEmpty || args.any fun a ↦ (n.splitOn a).length > 1).toArray
  -- Each worker takes the next run not yet taken, so a long run does not hold back the rest.
  let next ← IO.mkRef 0
  let worker : IO (List (Nat × String × Bool × Nat)) := do
    let mut done := []
    repeat
      let i ← next.modifyGet fun i ↦ (i, i + 1)
      let some (n, run) := runs[i]? | break
      let t0 ← IO.monoMsNow
      let ok ← run
      done := (i, n, ok, (← IO.monoMsNow) - t0) :: done
    return done
  let tasks ← (List.range workers).mapM fun _ ↦ IO.asTask (prio := .dedicated) worker
  let mut results : Array (Nat × String × Bool × Nat) := #[]
  for t in tasks do
    results := results ++ (← IO.ofExcept (← IO.wait t))
  let mut failed := 0
  for (_, n, ok, ms) in results.qsort (·.1 < ·.1) do
    IO.println s!"{n}: {if ok then "ok" else "FAILED"} ({ms} ms)"
    if !ok then failed := failed + 1
  IO.println s!"{runs.size - failed} of {runs.size} runs passed"
  return if failed == 0 then 0 else 1
