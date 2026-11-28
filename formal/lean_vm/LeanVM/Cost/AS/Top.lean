module

public import LeanVM.Cost.AS.Replay
public import LeanVM.Protocol.Extraction.AS.Lite
import all LeanVM.Protocol.Extraction.AS.Lite
import all LeanVM.Protocol.EndToEnd.Sound.SkelDefs
import all LeanVM.Protocol.Relation.Stack
import all LeanVM.Protocol.Relation.Link.Rel
import all Statement.Verifier.Layout
import all Statement.Verifier.Link

/-!
# The agreement-set extractor, compiled

`extractL` (`Protocol/Extraction/AS/Lite.lean`), compiled on top of the descent's and the replay's
functions (`Cost/AS/Descent.lean`, `Cost/AS/Replay.lean`): the decoders of the announced sizes and
of the opening's trace, the body's skeleton, every root's word (its leaves inverted through the
transcript's compiled index), the candidate execution, and the top (`extractLC`).

The layout's constants that the tables' descriptors derive (which hold strings and functions) are
compiled as literals (`globalColumnBasesLit`, `stackLit`, …); the candidate's memory is built as a
vector (`candidateL_vec`).
-/

namespace LeanVM.Cost.AS

open LeanVM.Cost LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Extraction.AS LeanVM.Protocol.EndToEnd.Sound LeanVM.Extraction.Fast LeanVM.Protocol.Verifier
open Common LeanVM.Protocol.Whir.Sound

public section

/-! ## The layout's constants, as literals -/

theorem keccakInLit : keccakIn = 8 := rfl

cost_rewrite keccakInLit

theorem keccakOutLit : keccakOut = 33 := rfl

cost_rewrite keccakOutLit

theorem keccakIxLit : keccakIx = 58 := rfl

cost_rewrite keccakIxLit

theorem qkeccakSlotsLit : qkeccakSlots = 50 := rfl

cost_rewrite qkeccakSlotsLit

theorem qkeccakSpareLit : qkeccakSpare = 14 := by decide

cost_rewrite qkeccakSpareLit

theorem qkeccakSlotBitsLit : qkeccakSlotBits = 6 := by decide

cost_rewrite qkeccakSlotBitsLit

theorem globalColumnBasesLit : globalColumnBases = [3, 10, 19, 24, 34, 48] := by decide +kernel

cost_rewrite globalColumnBasesLit

/-- The stacked columns, in global order: the memory's limbs, `q_keccak`, the five arithmetic
tables' columns, and `KECCAK`'s four last pointers. -/
@[expose] def stackColumns : List ℕ :=
  [0, 1, 2] ++ (List.range 45).map (· + 3) ++ [112, 113, 114, 115]

theorem stackBlocks_columns : stackBlocks.map (·.column) = stackColumns := by decide +kernel

/-- `stack` on the stacked columns' literal. -/
@[expose] def stackOfColumns (kappas : List ℕ) : List (ℕ × ℕ) × ℕ :=
  let r := stackOffsets (stackColumns.map fun c ↦ kappas.getD c 0)
  (stackColumns.zip r.1, max Whir.minLogStack r.2)

theorem stackLit (kappas : List ℕ) : stack kappas = stackOfColumns kappas := by
  unfold stack stackOfColumns
  rw [← stackBlocks_columns, List.map_map]
  rfl

cost_rewrite stackLit

/-- A chunk's first set bit, on the word's number. -/
theorem chunkPosLit (chunks : Chunks) (w : K) (i : ℕ) : Relation.chunkPos chunks w i =
    let n := (K.lane w).toNat
    ((List.range (2 ^ chunks.widths.getD i 0)).find? fun v ↦
      (1 &&& (n >>> (chunks.wordShifts.getD i 0 + v))) != 0).getD 0 :=
  rfl

cost_rewrite chunkPosLit

/-! ## The candidate's memory, as a vector -/

/-- The memory's words read off a stack, as a vector. -/
@[expose] def memoryVecL (lay : LayoutLite) {μ : ℕ} (q : Column μ) : Vector E (2 ^ lay.logMemory) :=
  Vector.ofFn fun i ↦ E.ofLimbs (columnRowL lay q memory0 i) (columnRowL lay q memory1 i)

theorem candidateL_vec (program : LeanIsaProgram) (lay : LayoutLite) {μ : ℕ} (q : Column μ) :
    candidateL program lay q = ⟨lay.logMemory, (memoryVecL lay q).get, firstFinalL lay q⟩ := by
  unfold candidateL
  congr 1
  funext i
  simp [memoryVecL, memoryImageL, Vector.get]
  rfl

cost_rewrite candidateL_vec

/-! ## The extractor -/

cost_compile skelReplayPC := skelReplayP

cost_compile decSizesLC := decSizesL

cost_compile skBodyC := skBody

cost_compile decBodyLC := decBodyL

cost_compile laneRowC := laneRow

cost_compile laneRowsC := laneRows

cost_compile leavesAtC := leavesAt

cost_compile wordArrOfC := wordArrOf

cost_compile candidateLC := candidateL

cost_compile finishLC := finishL

cost_compile extractLC := extractL

end

end LeanVM.Cost.AS
