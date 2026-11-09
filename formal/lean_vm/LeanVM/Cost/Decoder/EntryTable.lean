module

public import LeanVM.Cost.Decoder.PreTable
public import LeanVM.Cost.Decoder.GuestTables
public import LeanVM.Guest.Fast.FramesN

/-!
# The guest decoder's compiled chain: the replayed frame map, keyed by index

`Guest.Fast.frameVFastN pre states rd` (`Fast/FramesN.lean`): the entry table of the replayed
states (`Located.entryTable`: from a call's key to the frame of the first state that entered its
callee, the precondition `pre` holding there), and each call's frame read through the callee's
certificate. Restated with the guest's tables (`GuestTables.lean`, literals of the program) and
staged:

* `pcTableT`: the functions entered at each pc, from `guestEntries` (computed once by the caller
  and passed: a closed constant compiled in place would be recomputed at each use);
* `entryKeyT`: a state's key under a function entered at its pc, the argument and return counts
  from `guestArgCounts`, `guestRetCounts`;
* **the compiled table, one sorted array** (`entryArrayT`): every pair the states file, sorted by
  key stably, each key's first kept; `frameAtA table rd j args rets v`, the frame map, one binary
  search of the call's key, its last argument the value `v` (the frame map is the closure
  `frameAtA table rd`), the cells from `guestLocs`;
* the same table by insertions (`fileOne`, `fileStateT`, `entryTableT`, a sorted map with a
  presence lookup per filing) and its frame map (`frameAt`): definitions only, not compiled, the
  specification the sorted array is proved equal to.

`EntryTableEq.lean` proves them the definitions at the guest's tables (`frameAt_eq`), and the
sorted array's frame map the specification's (`frameAtA_entryArrayT`, `frameAtA_eq`).
-/

namespace LeanVM.Cost.Decoder

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Located
open LeanVM.Guest.Fast LeanVM.Extraction.Fast

attribute [local instance] lexOrd

@[expose] public section

/-- Function `j`'s entry filed at its entry pc's code. -/
def addEntry (m : SortedMap ℕ (List ℕ)) (j : ℕ) : SortedMap ℕ (List ℕ) :=
  addAt m (laneCode (addressOfIndex (guestEntries.getD j 0))) j

/-- **The functions entered at each pc** (`pcTable`), from the table of entries. -/
def pcTableT : SortedMap ℕ (List ℕ) := (List.range nFns).foldl addEntry .empty

/-- The key under which state `r`, at function `j`'s entry, files its frame (`entryKey`). -/
def entryKeyT (rd : Reader) (r : Registers K) (j : ℕ) : CallKey :=
  callKey j (wordsWith rd r.fp 2 (guestArgCounts.getD j 0))
    (wordsWith rd r.fp (2 + guestArgCounts.getD j 0) (guestRetCounts.getD j 0))

/-- State `r` filed under function `j`'s key, if `pre` holds (`fileState`'s step). -/
def fileOne (pre : ℕ → K → Bool) (rd : Reader) (r : Registers K) (m : SortedMap CallKey K)
    (j : ℕ) : SortedMap CallKey K :=
  if pre j r.fp then insertIfNew m (entryKeyT rd r j) r.fp else m

/-- State `r` filed under the key of each function entered at its pc (`fileState`). -/
def fileStateT (pcT : SortedMap ℕ (List ℕ)) (pre : ℕ → K → Bool) (rd : Reader)
    (m : SortedMap CallKey K) (r : Registers K) : SortedMap CallKey K :=
  (pcT.getD (laneCode r.pc) []).foldl (fileOne pre rd r) m

/-- **The entry table** of the states (`entryTable`). -/
def entryTableT (pcT : SortedMap ℕ (List ℕ)) (pre : ℕ → K → Bool) (states : List (Registers K))
    (rd : Reader) : SortedMap CallKey K :=
  states.foldl (fileStateT pcT pre rd) .empty

/-- The word of value `v` in function `j`'s frame at `fp`. -/
def frameWordAt (rd : Reader) (fp : K) (j : ℕ) (v : V) : E :=
  wordWith rd fp ((guestLocs.getD (canonIndex j) #[]).getD v.idx 0)

/-- **The frame map**, its last argument the value read: the call of function `canonIndex j`
looked up in the entry table, its frame's word of `v`; `0` if the call was not entered. -/
def frameAt (table : SortedMap CallKey K) (rd : Reader) (j : ℕ) (args rets : List E) (v : V) :
    E :=
  match table.get? (callKey (canonIndex j) args rets) with
  | some fp => frameWordAt rd fp j v
  | none => 0

/-! ### The library functions the tables use, under names of their own

The pc table's sorted map operations (`ℕ` keys), the binary search on call keys, the call key's
codes and the frame cells' words: compiled here before their callers, so that the bounds name
them, not an index (`Bounds/Decoder/EntryTable.lean`, `EntryArray.lean`). -/

cost_compile searchInPcC measure fun _ _ lo hi ↦ hi - lo := @searchIn ℕ (List ℕ) _
cost_compile mergeNewerPcC measure fun a b ↦ a.length + b.length := @mergeNewer ℕ (List ℕ) _
cost_compile levelMergePcC := @Level.merge ℕ (List ℕ) _ _ _
cost_compile carryPcC measure fun _ ls ↦ ls.length := @carry ℕ (List ℕ) _ _ _
cost_compile insertPcC := @SortedMap.insert ℕ (List ℕ) _ _ _
cost_compile getPcC := @SortedMap.get? ℕ (List ℕ) _
cost_compile addAtC := addAt

cost_compile searchInKeyC measure fun _ _ lo hi ↦ hi - lo := @searchIn CallKey K _

cost_compile wordCodeC := wordCode
cost_compile callKeyC := callKey
cost_compile wordsWithC := wordsWith
cost_compile isFunctionIndexC := isFunctionIndex

set_option maxRecDepth 100000 in
cost_compile addEntryC := addEntry
set_option maxRecDepth 100000 in
cost_compile pcTableTC := pcTableT
set_option maxRecDepth 100000 in
cost_compile entryKeyTC := entryKeyT
set_option maxRecDepth 100000 in
cost_compile frameWordAtC := frameWordAt

/-! ## The entry table as one sorted array

The same table without a presence lookup per filing: every pair a state files (`statePairs`: the
key of each function entered at its pc whose precondition holds, and the frame), in filing order
(`entryPairs`), sorted by key by a stable merge sort (`List.mergeSort`, the extractor's compiled
`mergeSortList`), each key's first pair kept (`dedupFirst`): the first pair filed for each key
(`EntryTableEq.lean`: `searchIn_entryArrayT`, its binary search is `entryTableT`'s `get?`). A
frame lookup is one binary search (`frameAtA`, `searchInKeyC`). -/

/-- Two call keys compared (`compare` at `lexOrd`), a function of its own. -/
def keyCmp (a b : CallKey) : Ordering := compare a b

/-- The pair state `s` files for function `j`: its key and the frame, if `pre` holds. -/
def pairOf (pre : ℕ → K → Bool) (rd : Reader) (s : Registers K) (j : ℕ) : Option (CallKey × K) :=
  if pre j s.fp then some (entryKeyT rd s j, s.fp) else none

/-- The pairs state `s` files: one per function entered at its pc whose precondition holds. -/
def statePairs (pcT : SortedMap ℕ (List ℕ)) (pre : ℕ → K → Bool) (rd : Reader)
    (s : Registers K) : List (CallKey × K) :=
  (pcT.getD (laneCode s.pc) []).filterMap (pairOf pre rd s)

/-- **The pairs the states file**, in filing order. -/
def entryPairs (pcT : SortedMap ℕ (List ℕ)) (pre : ℕ → K → Bool) (rd : Reader) :
    List (Registers K) → List (CallKey × K)
  | [] => []
  | s :: ss => statePairs pcT pre rd s ++ entryPairs pcT pre rd ss

/-- The pairs' order: by key. -/
def keyLe (a b : CallKey × K) : Bool :=
  match keyCmp a.1 b.1 with
  | .gt => false
  | _ => true

/-- Of each run of pairs of one key, the first. -/
def dedupFirst : List (CallKey × K) → List (CallKey × K)
  | a :: b :: l =>
    match keyCmp a.1 b.1 with
    | .eq => dedupFirst (a :: l)
    | _ => a :: dedupFirst (b :: l)
  | l => l

/-- **The entry table, a sorted array**: the pairs sorted by key, stably, each key's first kept. -/
def entryArrayT (pcT : SortedMap ℕ (List ℕ)) (pre : ℕ → K → Bool) (states : List (Registers K))
    (rd : Reader) : Array (CallKey × K) :=
  (dedupFirst ((entryPairs pcT pre rd states).mergeSort keyLe)).toArray

/-- **The frame map on the sorted array**: one binary search of the call's key. -/
def frameAtA (table : Array (CallKey × K)) (rd : Reader) (j : ℕ) (args rets : List E) (v : V) :
    E :=
  match searchIn table (callKey (canonIndex j) args rets) 0 table.size with
  | some fp => frameWordAt rd fp j v
  | none => 0

cost_compile keyCmpC := keyCmp
cost_compile pairOfC := pairOf
set_option maxRecDepth 100000 in
cost_compile statePairsC := statePairs
set_option maxRecDepth 100000 in
cost_compile entryPairsC measure fun _ _ _ l ↦ l.length := entryPairs
cost_compile keyLeC := keyLe
cost_compile dedupFirstC measure fun l ↦ l.length := dedupFirst
set_option maxRecDepth 100000 in
cost_compile entryArrayTC := entryArrayT
set_option maxRecDepth 100000 in
cost_compile frameAtAC := frameAtA

/-! ### A frame looked up once

`frameAtA` searches the call's key at every word it reads. A reader of many words of one frame
(leanSPHINCS's, `Top.lean`) looks the frame up once (`frameFpA`, the search) and reads its words off
the frame pointer found (`frameValAt`); `frameAtA_eq_frameValAt`: the same words. -/

/-- The frame pointer of function `canonIndex j`'s call on `args`, `rets`, if it was entered:
`frameAtA`'s search. -/
def frameFpA (table : Array (CallKey × K)) (j : ℕ) (args rets : List E) : Option K :=
  searchIn table (callKey (canonIndex j) args rets) 0 table.size

/-- The word of `v` in function `j`'s frame at the pointer `o` (`0` if none): `frameAtA`'s word. -/
def frameValAt (rd : Reader) (o : Option K) (j : ℕ) (v : V) : E :=
  match o with
  | some fp => frameWordAt rd fp j v
  | none => 0

theorem frameAtA_eq_frameValAt (table : Array (CallKey × K)) (rd : Reader) (j : ℕ)
    (args rets : List E) :
    frameAtA table rd j args rets = frameValAt rd (frameFpA table j args rets) j := by
  funext v
  unfold frameAtA frameValAt frameFpA
  rfl

set_option maxRecDepth 100000 in
cost_compile frameFpAC := frameFpA
cost_compile frameValAtC := frameValAt

end

end LeanVM.Cost.Decoder
