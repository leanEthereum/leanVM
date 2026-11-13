import LeanVM.Cost.Decoder.EntryTable
import LeanVMTests.Runs

/-!
# Tests: the guest decoder's compiled chain on small inputs

Each compiled reader run on a small input, its output the statement's encoding of the Lean
function's value: the cells' digests and claims, a signature claim's bit vectors, the memory's
cells through a reader (a compiled closure), `main`'s valuation, the seed. The slower ones are
runs, compiled (`lake exe test-runs`).
-/

namespace LeanVMTests.Cost.DecoderChain

open LeanVM.Cost LeanVM.Cost.Decoder LeanVM.Parameters LeanVM.Guest.Core LeanVM.Guest.B1
open LeanVM.Guest.B1.Main LeanVM.Protocol.Verifier

/-- A compiled function's value on `vs`, in the program of the bodies `deps`. -/
def runOn (deps : List (ℕ × Term)) (i : ℕ) (vs : List MachineValue) : Option MachineValue :=
  (evaluateFunctionBody (MachineProgram.ofList deps) 100000 i vs).map (·.1)

/-- The discrete logarithm's baby-step tables, built in Lean and passed in as a value. -/
def dlTables : MachineValue := encodeValue LeanVM.Extraction.Fast.discreteLogTables

def cA : E := E.ofLimbs (K.ofLane 0x0123456789abcdef) (K.ofLane 0xfedcba9876543210)
def cB : E := E.ofLimbs (K.ofLane 7) (K.ofLane 0xffffffffffffffff)

#guard runOn digestOfCellsC.costDeps digestOfCellsC.costIdx [encodeValue cA, encodeValue cB] ==
  some (encodeValue (Main.digestOfCells cA cB))

def cells : List E := (List.range 24).map fun i ↦ (gen ^ i : E)
#guard runOn deferOfCellsC.costDeps deferOfCellsC.costIdx [encodeValue cells] ==
  some (encodeValue (deferOfCells cells))
#guard runOn fixedOfCellsC.costDeps fixedOfCellsC.costIdx [encodeValue cells] ==
  some (encodeValue (fixedOfCells cells))

#guard runOn xmssClaimOfC.costDeps xmssClaimOfC.costIdx
  [encodeValue cA, encodeValue cB, encodeValue cB, encodeValue cA] ==
  some (encodeValue (Sig.xmssClaimOf cA cB cB cA))
#guard runOn sphincsClaimOfC.costDeps sphincsClaimOfC.costIdx
  [encodeValue cB, encodeValue cA, encodeValue cA, encodeValue cB] ==
  some (encodeValue (Sig.sphincsClaimOf cB cA cA cB))

/-- A small memory: the word at `g^i` is `g^(i+1)` (as `E`) for `i < 64`. -/
def smallReader (a : K) : Option E :=
  ((List.range 64).find? fun i ↦ a == LeanVM.Parameters.addressOfIndex i).map fun i ↦ (gen ^ (i +
      1) : E)
cost_compile smallReaderC := smallReader

/-- The reader as a closure value. -/
def rdVal : MachineValue := .closure smallReaderC.costIdx []

-- (`cellAt` and the readers are `noncomputable` in Lean: their values are written out.)
#guard runOn (cellAtC.costDeps ++ smallReaderC.costDeps) cellAtC.costIdx
  [rdVal, encodeValue (1 : E), encodeValue (3 : ℕ)] == some (encodeValue (gen ^ 4 : E))
#guard runOn (cellAtC.costDeps ++ smallReaderC.costDeps) cellAtC.costIdx
  [rdVal, encodeValue (1 : E), encodeValue (70 : ℕ)] == some (encodeValue (0 : E))
#guard runOn (readCellsC.costDeps ++ smallReaderC.costDeps) readCellsC.costIdx
  [rdVal, encodeValue (1 : E), encodeValue (5 : ℕ)] ==
  some (encodeValue ((List.range 5).map fun i ↦ (gen ^ (i + 1) : E)))
#guard runOn (xmssAtC.costDeps ++ smallReaderC.costDeps) xmssAtC.costIdx
  [rdVal, encodeValue (1 : E), encodeValue (2 : ℕ)] ==
  some (encodeValue (Sig.xmssClaimOf (gen ^ 9) (gen ^ 10) (gen ^ 11) (gen ^ 12)))

/-- A valuation of `main`: every value `1`. -/
def oneSigma (_ : V) : E := 1
cost_compile oneSigmaC := oneSigma

def sigmaVal : MachineValue := .closure oneSigmaC.costIdx []

#guard runOn (decSeedC.costDeps ++ oneSigmaC.costDeps) decSeedC.costIdx [sigmaVal] ==
  some (encodeValue (decSeed oneSigma))

-- The batching's hints: the nonce and the rounds at `bc_sumcheck_msgs = 1`, the cells `g^0, g^1, …`.
#guard runOn (aggHintsC.costDeps ++ oneSigmaC.costDeps ++ smallReaderC.costDeps) aggHintsC.costIdx
  [rdVal, sigmaVal] == some (encodeValue (⟨(gen : E), (List.range 23).map fun k ↦
    ((gen ^ (2 * k + 2) : E), (gen ^ (2 * k + 3) : E)), 1⟩ : LeanVM.Node.BatchingHints))

/-- A valuation of `main` whose every value is `g^7`. -/
def sevenSigma (_ : V) : E := LeanVM.Parameters.ofK (LeanVM.Parameters.addressOfIndex 7)
cost_compile sevenSigmaC := sevenSigma

/-- A memory of `2^3` words, word `i` at address `g^i` being `g^i` (as `E`). -/
def mem8 : LeanVM.Semantics.MemoryImage 3 := fun i ↦ LeanVM.Parameters.ofK (LeanVM.Parameters.addressOfIndex i.val)
cost_compile mem8C := mem8

-- The reader through the extractor's address table: the table, `κ`, the memory (a closure), the
-- address.
#guard runOn (readTableC.costDeps ++ mem8C.costDeps) readTableC.costIdx
  [encodeValue (LeanVM.Extraction.Fast.powTable 3), encodeValue (3 : ℕ), .closure mem8C.costIdx [],
    encodeValue (LeanVM.Parameters.addressOfIndex 5)] ==
  some (encodeValue (some (LeanVM.Parameters.ofK (LeanVM.Parameters.addressOfIndex 5))))
#guard runOn (readTableC.costDeps ++ mem8C.costDeps) readTableC.costIdx
  [encodeValue (LeanVM.Extraction.Fast.powTable 3), encodeValue (3 : ℕ), .closure mem8C.costIdx [],
    encodeValue (LeanVM.Parameters.addressOfIndex 9)] == some (encodeValue (none : Option E))

/-! ## The replayed frame map -/

section Frames

open LeanVM.Guest.Located LeanVM.Extraction.Fast

attribute [local instance] lexOrd

/-- A precondition that always holds. -/
def anyPre (_ : ℕ) (_ : K) : Bool := true
cost_compile anyPreC := anyPre

/-- Two states: at function `2`'s entry and at function `3`'s, frame pointer `g^4`. -/
def twoStates : List (LeanVM.Semantics.Registers K) :=
  [⟨LeanVM.Parameters.addressOfIndex (guestEntries.getD 2 0), LeanVM.Parameters.addressOfIndex 4⟩,
    ⟨LeanVM.Parameters.addressOfIndex (guestEntries.getD 3 0), LeanVM.Parameters.addressOfIndex 4⟩]

/-- The frame map's runs, compiled. -/
test_runs frameRuns := [
  -- The entry table of the two states, one sorted array (the table of entries built in the
  -- program).
  ("entryArrayTC", fun _ ↦
    runOn (entryArrayTC.costDeps ++ pcTableTC.costDeps ++ anyPreC.costDeps ++
        smallReaderC.costDeps) entryArrayTC.costIdx
      [runOn pcTableTC.costDeps pcTableTC.costIdx [] |>.getD (.nat 0), .closure anyPreC.costIdx [],
        encodeValue twoStates, rdVal] ==
      some (encodeValue (entryArrayT pcTableT anyPre twoStates smallReader))),
  -- A frame's word: function `2`'s call on its words, value `.n 0` (its first cell).
  ("frameAtAC", fun _ ↦
    runOn (frameAtAC.costDeps ++ smallReaderC.costDeps) frameAtAC.costIdx
      [encodeValue (entryArrayT pcTableT anyPre twoStates smallReader), rdVal, encodeValue (2 : ℕ),
        encodeValue (wordsWith smallReader (LeanVM.Parameters.addressOfIndex 4) 2
            (guestArgCounts.getD 2 0)),
        encodeValue (wordsWith smallReader (LeanVM.Parameters.addressOfIndex 4) (2 +
            guestArgCounts.getD 2 0)
          (guestRetCounts.getD 2 0)), encodeValue (V.n 0)] ==
      some (encodeValue (frameAtA (entryArrayT pcTableT anyPre twoStates smallReader) smallReader 2
        (wordsWith smallReader (LeanVM.Parameters.addressOfIndex 4) 2 (guestArgCounts.getD 2 0))
        (wordsWith smallReader (LeanVM.Parameters.addressOfIndex 4) (2 + guestArgCounts.getD 2 0)
          (guestRetCounts.getD 2 0)) (V.n 0))))]

end Frames

/-! ## The coverage searches, by sorting and binary search -/

open LeanVM.Guest.Fast in
/-- A region's pairs `(mark, slot)`, marks repeated and out of order. -/
def pairs7 : List (ℕ × ℕ) := [(5, 0), (3, 1), (5, 2), (1, 3), (3, 4), (9, 5), (3, 6)]

open LeanVM.Guest.Fast in
#guard coverTable pairs7 == (#[1, 3, 3, 3, 5, 5, 9], #[3, 1, 4, 6, 0, 2, 5])
open LeanVM.Guest.Fast in
#guard runOn coverTableC.costDeps coverTableC.costIdx [encodeValue pairs7] ==
  some (encodeValue (coverTable pairs7))
-- The first slot of each mark, and the count of each segment, are the scans'.
open LeanVM.Guest.Fast in
#guard (List.range 11).all fun e ↦
  slotIn (coverTable pairs7).1 (coverTable pairs7).2 e ==
    (((List.range 7).find? fun s ↦ (pairs7.getD s (0, 0)).1 == e).getD 0)
open LeanVM.Guest.Fast in
#guard (List.range 11).all fun a ↦ (List.range 11).all fun b ↦
  countIn (coverTable pairs7).1 a b ==
    ((List.range 7).filter fun s ↦ a ≤ (pairs7.getD s (0, 0)).1 && (pairs7.getD s (0, 0)).1 < b).length
open LeanVM.Guest.Fast in
#guard runOn slotInC.costDeps slotInC.costIdx [encodeValue (coverTable pairs7).1,
  encodeValue (coverTable pairs7).2, encodeValue (3 : ℕ)] == some (encodeValue (1 : ℕ))
open LeanVM.Guest.Fast in
#guard runOn countInC.costDeps countInC.costIdx [encodeValue (coverTable pairs7).1,
  encodeValue (3 : ℕ), encodeValue (6 : ℕ)] == some (encodeValue (5 : ℕ))

-- Consecutive slots' claims, the address advanced by `g^4`.
#guard runOn (xmssRunC.costDeps ++ smallReaderC.costDeps) xmssRunC.costIdx
  [rdVal, encodeValue (LeanVM.Parameters.g ^ 4), encodeValue (1 : K), encodeValue (3 : ℕ)] ==
  some (encodeValue ((List.range 3).map fun s ↦
    Sig.xmssClaimOf (gen ^ (4 * s + 1)) (gen ^ (4 * s + 2)) (gen ^ (4 * s + 3)) (gen ^ (4 * s + 4))))

/-- The slower checks above, compiled: each pays seconds in the interpreter. -/
test_runs runs := [
  ("mainValC", fun _ ↦
    runOn (mainValC.costDeps ++ smallReaderC.costDeps) mainValC.costIdx
      [rdVal, encodeValue (V.n 47)] == some (encodeValue (mainVal smallReader (V.n 47)))),
  -- read off the literal table, the certificate's cells
  ("main's values, off the certificate's cells", fun _ ↦
    (List.range 430).all fun i ↦ mainVal smallReader (V.n i) ==
      LeanVM.Guest.Located.wordWith smallReader 1
        ((LeanVM.Guest.Fn.«main».cert_w0_0 ++ LeanVM.Guest.Fn.«main».cert_w1_0).getD (V.n i).idx 0)),
  -- The statement off `main`'s frame: no declared claim (`gLog 1 = 0`), the DA digest at slot `0`
  -- of `da_digests = 1`, the deferred claim at `defer_stmt = 1`. (`decStmt` is `noncomputable` in
  -- Lean: its value is written out.)
  ("decStmtC", fun _ ↦
    runOn (decStmtC.costDeps ++ oneSigmaC.costDeps ++ smallReaderC.costDeps) decStmtC.costIdx
      [dlTables, sigmaVal, rdVal] == some (encodeValue (⟨⟨[], [], Main.digestOfCells (gen ^ 1) (gen ^ 2)⟩,
        deferOfCells ((List.range 24).map fun i ↦ (gen ^ (i + 1) : E))⟩ : LeanVM.Node.NodeStatement))),
  -- The number of children, `gLog (g^7)`, by the compiled discrete logarithm, its tables given.
  ("nKidsC", fun _ ↦
    runOn (nKidsC.costDeps ++ sevenSigmaC.costDeps) nKidsC.costIdx
      [dlTables, .closure sevenSigmaC.costIdx []] == some (encodeValue (7 : ℕ))),
  -- The cursor's length: `q = p · g^9` limb by limb.
  ("cursorLengthC", fun _ ↦
    runOn cursorLengthC.costDeps cursorLengthC.costIdx
      [dlTables, encodeValue (1 : E), encodeValue (LeanVM.Parameters.ofK
          (LeanVM.Parameters.addressOfIndex 9))] ==
      some (encodeValue (9 : ℕ))),
  -- A region's table off the memory: the mark of slot `s` at `cover = 1` is `gLog (g^(s+1))`.
  ("regionTableC", fun _ ↦
    runOn (regionTableC.costDeps ++ smallReaderC.costDeps) regionTableC.costIdx
      [dlTables, rdVal, encodeValue (1 : E), encodeValue (2 : ℕ), encodeValue (3 : ℕ)] ==
      some (encodeValue (LeanVM.Guest.Fast.coverTable [(3, 0), (4, 1), (5, 2)]))),
  -- Child `0`'s statement off the tables: its segment `[gLog g, gLog g^2) = [1, 2)` holds the slot
  -- of mark `1` in the leanXMSS region (marks `1, 2, 3`), none of the leanSPHINCS region's.
  ("kidStmtC", fun _ ↦
    runOn (kidStmtC.costDeps ++ oneSigmaC.costDeps ++ smallReaderC.costDeps) kidStmtC.costIdx
      [dlTables, rdVal, sigmaVal, encodeValue (1 : E), encodeValue (1 : E), encodeValue (1 : E),
        encodeValue (LeanVM.Guest.Fast.coverTable [(1, 0), (2, 1), (3, 2)]),
        encodeValue (LeanVM.Guest.Fast.coverTable [(4, 0), (5, 1)]), encodeValue (0 : ℕ)] ==
      some (encodeValue (⟨⟨[Sig.xmssClaimOf (gen ^ 1) (gen ^ 2) (gen ^ 3) (gen ^ 4)], [],
        Main.digestOfCells (gen ^ 1) (gen ^ 2)⟩,
        deferOfCells ((List.range 24).map fun i ↦ (gen ^ (i + 1) : E))⟩ : LeanVM.Node.NodeStatement)))]

end LeanVMTests.Cost.DecoderChain
