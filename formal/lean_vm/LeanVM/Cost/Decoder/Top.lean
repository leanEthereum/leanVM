module

public import LeanVM.Cost.Decoder.EntryTable

/-!
# The guest decoder's compiled chain: the top

The decoder's top on the program, `κ` and the memory vector (`Ends.lean`'s input side), staged
point-free, each step a function of its own, each closure a partial application, each table built
once and passed down:

* `decTop prog κ mem`: the logarithm's tables (`discreteLogTables`), the preconditions
  (`Guest.Fast.preTable`, a literal), the generator's powers (`genPows`), the readers' tables
  (`Guest.Fast.readerTabs`), the table of entries (`pcTableT`), the address tables
  (`decoderTables`);
* `decTopTables`: the reader (`memReader memT mem`) and the replay (`replayStatesOf`);
* `decTopStates`: `main`'s valuation (`mainVal rd`) and the entry table, one sorted array
  (`entryArrayT`, the precondition `preTestAt D T Pw rd`);
* `decTopFrames`: the witness (`decWitNStaged`, the frame map `frameAtA table rd`, the leanSPHINCS
  reader looking its frames up once `sphincsAtFrameT`, the cursor's length `cursorLength D`) and the decoding (`decoderOutput D`: the seed, the statement
  `decStmtD D`, `decodedOf`).

`TopEq.lean`: **`decTop_eq : decTop guest κ (memoryVector L) = End.decode L`**.
-/

namespace LeanVM.Cost.Decoder

open LeanVM.Cost LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Located
open LeanVM.Guest.B1 LeanVM.Guest.Fast LeanVM.Extraction.Fast LeanVM.Node

attribute [local instance] lexOrd

@[expose] public section

/-- The leanSPHINCS signature off `verify_sig_lean_sphincs`' frame pointer `o` (`21`): each layer's
`sp_wots` frame (`20`) looked up once (`frameFpA`), the words read off the frame pointers
(`frameValAt`). A function of the pointer, so that the search of `21` is not repeated at each word
of that frame the reader reads. -/
noncomputable def sphincsAtFp (R : ReaderTabs) (table : Array (CallKey × K)) (rd : Reader)
    (o : Option K) : Sphincs.Signature :=
  sphincsSigOfA R.sphincs (frameValAt rd o 21)
    (frameValAt rd (frameFpA table 20 (spWotsArgs (frameValAt rd o 21) 0)
      (spWotsRets (frameValAt rd o 21) 0)) 20)
    (frameValAt rd (frameFpA table 20 (spWotsArgs (frameValAt rd o 21) 1)
      (spWotsRets (frameValAt rd o 21) 1)) 20)
    (frameValAt rd (frameFpA table 20 (spWotsArgs (frameValAt rd o 21) 2)
      (spWotsRets (frameValAt rd o 21) 2)) 20)

/-- **The leanSPHINCS signature checked at slot address `p`, its frames looked up once**
(`sphincsAtFrame` at `frameAtA table rd`, `sphincsAtFrameT_eq`): `verify_sig_lean_sphincs`' frame
(`21`) one binary search (`frameFpA`), then `sphincsAtFp`. -/
noncomputable def sphincsAtFrameT (R : ReaderTabs) (table : Array (CallKey × K)) (rd : Reader)
    (σ : Val) (p : E) : Sphincs.Signature :=
  sphincsAtFp R table rd (frameFpA table 21 [p, σ (.n 68)] [])

theorem sphincsAtFrameT_eq (R : ReaderTabs) (table : Array (CallKey × K)) (rd : Reader)
    (σ : Val) : sphincsAtFrameT R table rd σ = sphincsAtFrame R σ (frameAtA table rd) := by
  funext p
  simp only [sphincsAtFrameT, sphincsAtFp, sphincsAtFrame, frameAtA_eq_frameValAt]

/-- **The leanXMSS signature `__loop2`'s iteration on `args` checks, its frame looked up once**
(`xmssAtFrame` at `frameAtA table rd`, `xmssAtFrameT_eq`): `__loop2`'s frame (`37`) one binary
search (`frameFpA`, its key the `56` arguments), then the reader off the frame pointer. -/
noncomputable def xmssAtFrameT (R : ReaderTabs) (table : Array (CallKey × K)) (rd : Reader)
    (args : List E) : LeanXmss.Signature :=
  xmssSigOfA R.xmss (frameValAt rd (frameFpA table 37 args []) 37)

theorem xmssAtFrameT_eq (R : ReaderTabs) (table : Array (CallKey × K)) (rd : Reader) :
    xmssAtFrameT R table rd = xmssAtFrame R (frameAtA table rd) := by
  funext args
  simp only [xmssAtFrameT, xmssAtFrame, frameAtA_eq_frameValAt]

/-- The decoding off `main`'s valuation and the entry table. -/
noncomputable def decTopFrames (D : DiscreteLogTables) (R : ReaderTabs) (rd : Reader) (σ : Val)
    (table : Array (CallKey × K)) : SeedStatementAndWitness :=
  decoderOutput D σ rd (decWitNStaged D R σ rd (frameAtA table rd) (xmssAtFrameT R table rd)
    (sphincsAtFrameT R table rd σ) (cursorLength D))

/-- The decoding off the reader and the replayed states. -/
noncomputable def decTopStates (D : DiscreteLogTables) (T : Array (Option FnPre)) (Pw : Array E)
    (R : ReaderTabs) (pcT : SortedMap ℕ (List ℕ)) (rd : Reader) (states : List (Registers K)) :
    SeedStatementAndWitness :=
  decTopFrames D R rd (mainVal rd) (entryArrayT pcT (preTestAt D T Pw rd) states rd)

/-- The decoding off the address tables and the memory. -/
noncomputable def decTopTables (D : DiscreteLogTables) (T : Array (Option FnPre)) (Pw : Array E)
    (R : ReaderTabs) (pcT : SortedMap ℕ (List ℕ)) (tabs : Array (ℕ × ℕ) × Array (ℕ × ℕ))
    (prog : LeanVM.Semantics.LeanIsaProgram) {κ : ℕ} (mem : Vector E (2 ^ κ)) :
        SeedStatementAndWitness :=
  decTopStates D T Pw R pcT (memReader tabs.1 mem) (replayStatesOf tabs.1 tabs.2 prog mem)

/-- **The decoder's top**: the decoding of an execution of `prog`, its memory the vector `mem` of
`2^κ` words. -/
noncomputable def decTop (prog : LeanVM.Semantics.LeanIsaProgram) (κ : ℕ) (mem : Vector E (2 ^ κ)) :
    SeedStatementAndWitness :=
  decTopTables discreteLogTables preTable genPows readerTabs pcTableT (decoderTables prog κ) prog
    mem

/-! The baby-step tables' parts, under names of their own (the bounds name them). -/
cost_compile powPairsByC measure fun _ n _ _ ↦ n := powPairsBy
cost_compile babyTableC := babyTable
set_option maxRecDepth 100000 in
cost_compile discreteLogTablesC := discreteLogTables
set_option maxRecDepth 100000 in
cost_compile sphincsAtFpC := sphincsAtFp
set_option maxRecDepth 100000 in
cost_compile sphincsAtFrameTC := sphincsAtFrameT
set_option maxRecDepth 100000 in
cost_compile xmssAtFrameTC := xmssAtFrameT
set_option maxRecDepth 100000 in
cost_compile decTopFramesC := decTopFrames
set_option maxRecDepth 100000 in
cost_compile decTopStatesC := decTopStates
set_option maxRecDepth 100000 in
cost_compile decTopTablesC := decTopTables
set_option maxRecDepth 100000 in
cost_compile decTopC := decTop

end

end LeanVM.Cost.Decoder
