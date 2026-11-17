/-
  LeanVM.Guest.B1.Tables.Vt.SpecBus

  The specification's bus after the GKR walk (`busRest`) as a run: it reads the five framework
  words and returns the bus result `vtBus`.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.SpecRun

/-!
# `busRest` as a run

`vtBus`: the bus result `busRest` returns for the framework words `memory`, `mf`, `bf`, the
bytecode's share and the slot sumcheck's point. `vt_busRest_run`: from any sponge `s`, `busRest`
reads the four words and the bytecode share's, and returns `vtBus`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The framework claims `busRest` returns. -/
def vtBusClaims (layout : Layout) (point memory : List E) (mf bf : E) : List ColumnClaim :=
  (List.zipWith (fun column value ↦ ⟨column, point.take layout.logMemory, value⟩)
    [memory0, memory1] memory) ++
  [⟨memoryFinalCounters, point.take layout.logMemory, mf⟩,
    ⟨bytecodeFinalCounters, point.take layout.logBytecode, bf⟩]

/-- The push side's fingerprints. -/
def vtFpPush (layout : Layout) (weights point memory : List E) (share : E) : List E :=
  fingerprints weights memory (point.take layout.logMemory) (point.take layout.logBytecode) share
    (Verifier.gpow 0) 1 1

/-- The pull side's fingerprints. -/
def vtFpPull (layout : Layout) (weights point memory : List E) (mf bf share : E) : List E :=
  fingerprints weights memory (point.take layout.logMemory) (point.take layout.logBytecode) share
    (Verifier.gpow (2 ^ layout.logBytecode - 1)) mf bf

/-- The forms and total after the push side. -/
def vtAcc0 (layout : Layout) (weights : List E) (beta : E) (point memory : List E) (share tv : E) :
    List (List Form) × E :=
  accumulateSide (tables.map fun _ ↦ [{}, {}, {}]) 0 layout.push
    (busLayout [0, layout.logMemory, layout.logBytecode] layout.push)
    (vtFpPush layout weights point memory share) weights beta point tv

/-- The forms and total after the pull side. -/
def vtAcc1 (layout : Layout) (weights : List E) (beta : E) (point memory : List E)
    (mf bf share tv0 tv1 : E) : List (List Form) × E :=
  accumulateSide (vtAcc0 layout weights beta point memory share tv0).1 1 layout.pull
    (busLayout [0, layout.logMemory, layout.logBytecode] layout.pull)
    (vtFpPull layout weights point memory mf bf share) weights beta point tv1

/-- The forms and total after the count side. -/
def vtAcc2 (layout : Layout) (weights : List E) (beta : E) (point memory : List E)
    (mf bf share tv0 tv1 tv2 : E) : List (List Form) × E :=
  accumulateSide (vtAcc1 layout weights beta point memory mf bf share tv0 tv1).1 2 layout.count
    (busLayout [] layout.count) [] [1] 0 point tv2

/-- **The bus result**, the bytecode's share `share` and the slot sumcheck's point `slots`. -/
def vtBus (layout : Layout) (weights : List E) (beta : E) (point treeValues memory : List E)
    (mf bf share : E) (slots : List E) : BusResult :=
  ⟨vtBusClaims layout point memory mf bf, point.take layout.logBytecode ++ slots, point,
    (vtAcc2 layout weights beta point memory mf bf share (treeValues.getD 0 0)
      (treeValues.getD 1 0) (treeValues.getD 2 0)).1,
    [(vtAcc0 layout weights beta point memory share (treeValues.getD 0 0)).2,
      (vtAcc1 layout weights beta point memory mf bf share (treeValues.getD 0 0)
        (treeValues.getD 1 0)).2,
      (vtAcc2 layout weights beta point memory mf bf share (treeValues.getD 0 0)
        (treeValues.getD 1 0) (treeValues.getD 2 0)).2]⟩

/-- **`busRest` as a run**: the four framework words, then the bytecode share's run (`bcWords`, to
the share, the point and the value `bv`, which `ev` accepts). -/
theorem vt_busRest_run (ev : List K → List E → E → VerifierProgram Unit) (layout : Layout)
    (weights : List E) (beta : E) (point treeValues : List E) (memory : List E)
    (hm : memory.length = 2) (mf bf share bv : E) (slots bcWords : List E) (s s' : Fs)
    (hsh : RunsTo (bytecodeShare weights (point.take layout.logBytecode))
      (s.absorbAll (memory ++ [mf, bf]) dsObserve) bcWords
      (share, point.take layout.logBytecode ++ slots, bv) s')
    (hbv : BytecodeAt ev layout.bytecode (point.take layout.logBytecode ++ slots) bv) :
    RunsTo (busRest ev layout weights beta point treeValues) s (memory ++ [mf, bf] ++ bcWords)
      (vtBus layout weights beta point treeValues memory mf bf share slots) s' := by
  have h1 := runsTo_readN s memory
  rw [hm] at h1
  have h2 := runsTo_readE (s.absorbAll memory dsObserve) mf
  have h3 := runsTo_readE ((s.absorbAll memory dsObserve).absorb mf dsObserve) bf
  have hs : s.absorbAll (memory ++ [mf, bf]) dsObserve =
      ((s.absorbAll memory dsObserve).absorb mf dsObserve).absorb bf dsObserve := by
    simp [Fs.absorbAll, List.foldl_append]
  rw [hs] at hsh
  have h5 := vt_runsTo_const (p := ev layout.bytecode (point.take layout.logBytecode ++ slots) bv)
    hbv s'
  have h6 := runsTo_ret (vtBus layout weights beta point treeValues memory mf bf share slots) s'
  have hx : memory ++ [mf, bf] ++ bcWords =
      memory ++ ([mf] ++ ([bf] ++ (bcWords ++ ([] ++ [])))) := by simp
  rw [hx]
  unfold busRest
  exact h1.bind (h2.bind (h3.bind (hsh.bind (h5.bind h6))))

end
end LeanVM.Guest.B1.Tables
