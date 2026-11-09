/-
  LeanVM.Guest.B1.Tables.Vt.SpecBus

  The specification's bus after the GKR walk (`busRest`) as a run: it reads the five framework
  words and returns the bus result `vtBus`.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.SpecRun

/-!
# `busRest` as a run (V:1492-1513)

`vtBus`: the bus result `busRest` returns for the framework words `memory`, `mf`, `bf` and the
bytecode's value `bv`. `vt_busRest_run`: from any sponge `s`, `busRest` reads the five words and
returns `vtBus`, leaving `s` with the words absorbed.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The framework claims `busRest` returns. -/
def vtBusClaims (layout : Layout) (point memory : List E) (mf bf : E) : List ColumnClaim :=
  (List.zipWith (fun column value ↦ ⟨column, point.take layout.logMemory, value⟩)
    [memory0, memory1, memory2] memory) ++
  [⟨memoryFinalCounters, point.take layout.logMemory, mf⟩,
    ⟨bytecodeFinalCounters, point.take layout.logBytecode, bf⟩]

/-- The push side's fingerprints. -/
def vtFpPush (layout : Layout) (alphas point memory : List E) (bv : E) : List E :=
  fingerprints (eqKernel alphas) memory (point.take layout.logMemory)
    (point.take layout.logBytecode) bv (Verifier.gpow 0) 1 1

/-- The pull side's fingerprints. -/
def vtFpPull (layout : Layout) (alphas point memory : List E) (mf bf bv : E) : List E :=
  fingerprints (eqKernel alphas) memory (point.take layout.logMemory)
    (point.take layout.logBytecode) bv (Verifier.gpow (2 ^ layout.logBytecode - 1)) mf bf

/-- The forms and total after the push side. -/
def vtAcc0 (layout : Layout) (alphas : List E) (beta : E) (point memory : List E) (bv tv : E) :
    List (List Form) × E :=
  accumulateSide (tables.map fun _ ↦ [{}, {}, {}]) 0 layout.push
    (busLayout [0, layout.logMemory, layout.logBytecode] layout.push)
    (vtFpPush layout alphas point memory bv) (eqKernel alphas) beta point tv

/-- The forms and total after the pull side. -/
def vtAcc1 (layout : Layout) (alphas : List E) (beta : E) (point memory : List E)
    (mf bf bv tv0 tv1 : E) : List (List Form) × E :=
  accumulateSide (vtAcc0 layout alphas beta point memory bv tv0).1 1 layout.pull
    (busLayout [0, layout.logMemory, layout.logBytecode] layout.pull)
    (vtFpPull layout alphas point memory mf bf bv) (eqKernel alphas) beta point tv1

/-- The forms and total after the count side. -/
def vtAcc2 (layout : Layout) (alphas : List E) (beta : E) (point memory : List E)
    (mf bf bv tv0 tv1 tv2 : E) : List (List Form) × E :=
  accumulateSide (vtAcc1 layout alphas beta point memory mf bf bv tv0 tv1).1 2 layout.count
    (busLayout [] layout.count) [] [1] 0 point tv2

/-- **The bus result.** -/
def vtBus (layout : Layout) (alphas : List E) (beta : E) (point treeValues memory : List E)
    (mf bf bv : E) : BusResult :=
  ⟨vtBusClaims layout point memory mf bf, point,
    (vtAcc2 layout alphas beta point memory mf bf bv (treeValues.getD 0 0) (treeValues.getD 1 0)
      (treeValues.getD 2 0)).1,
    [(vtAcc0 layout alphas beta point memory bv (treeValues.getD 0 0)).2,
      (vtAcc1 layout alphas beta point memory mf bf bv (treeValues.getD 0 0)
        (treeValues.getD 1 0)).2,
      (vtAcc2 layout alphas beta point memory mf bf bv (treeValues.getD 0 0) (treeValues.getD 1 0)
        (treeValues.getD 2 0)).2]⟩

/-- **`busRest` as a run.** -/
theorem vt_busRest_run (ev : (List K → List E → VerifierProgram E)) (layout : Layout) (alphas : List E) (beta : E)
    (point treeValues : List E) (memory : List E) (hm : memory.length = 3) (mf bf bv : E)
    (hbv : BytecodeAt ev layout.bytecode (point.take layout.logBytecode ++ alphas) bv) (s : Fs) :
    RunsTo (busRest ev layout alphas beta point treeValues) s (memory ++ [mf, bf])
      (vtBus layout alphas beta point treeValues memory mf bf bv)
      (s.absorbAll (memory ++ [mf, bf]) dsObserve) := by
  have h1 := runsTo_readN s memory
  rw [hm] at h1
  have h2 := runsTo_readE (s.absorbAll memory dsObserve) mf
  have h3 := runsTo_readE ((s.absorbAll memory dsObserve).absorb mf dsObserve) bf
  have h4 := vt_runsTo_bytecode hbv
    (((s.absorbAll memory dsObserve).absorb mf dsObserve).absorb bf dsObserve)
  have h5 := runsTo_ret (vtBus layout alphas beta point treeValues memory mf bf bv)
    (((s.absorbAll memory dsObserve).absorb mf dsObserve).absorb bf dsObserve)
  have hs : s.absorbAll (memory ++ [mf, bf]) dsObserve =
      ((s.absorbAll memory dsObserve).absorb mf dsObserve).absorb bf dsObserve := by
    simp [Fs.absorbAll, List.foldl_append]
  have hx : memory ++ [mf, bf] = memory ++ ([mf] ++ ([bf] ++ ([] ++ []))) := by simp
  rw [hs, hx]
  unfold busRest
  exact h1.bind (h2.bind (h3.bind (h4.bind h5)))

end
end LeanVM.Guest.B1.Tables
