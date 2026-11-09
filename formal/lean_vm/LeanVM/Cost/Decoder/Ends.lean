module

public import LeanVM.Cost.Decoder.Replay
import all LeanVM.Guest.B1.Main.Interface

/-!
# The guest decoder's compiled chain: the top's two ends

The decoder's top (`Guest.Fast.decode_eq_numbered`) reads the execution's memory `L` through the
sorted table of its addresses, replays the run, and builds the decoding from `main`'s valuation.
Its two ends, compiled:

* **the input side.** The program's input `encodeGuestWitnessDecoderInput prog t` holds the memory as the
  array of its words (`encodeFiniteFunction t.memory`), which is the encoding of the vector
  `memoryVector t.memory` (`encodeValue_memoryVector`): the entry (`Cost/DecoderProgram.lean`)
  passes it as is, no copy. From `prog`, `κ` and that vector:
  - `decoderTables prog κ`: the address tables `(powTable κ, powTable prog.logSize)`, the memory's
    (`memT`) and the bytecode's (`codeT`), the extractor's compiled `powTable`;
  - `memReader memT mem`: the reader `rd` (`Located.readTable memT mem.get`), a closure by
    partial application;
  - `mainVal rd` (`Witness.lean`): `main`'s valuation `σ`, a closure by partial application;
  - the replay `replayStatesOf memT codeT prog mem` (`Replay.lean`).
* **the output side.** `decodedOf s st w`: a decoding of its three fields, as values (no field is
  matched against its encoding: `Staged.lean`'s `nodeWitnessOf`); `decoderOutput D σ rd w`: the
  seed `decSeed σ` and the statement `decStmtD D σ rd` (`Readers.lean`: `decStmt` with the
  logarithm's tables `D` given, as every logarithm-taking function of the chain) computed, then
  `decodedOf`.

`Equations.lean`: `memReader_memoryVector`, `mainVal_eq` and **`decode_eq_ends`**, the deployed
decoder through these functions.
-/

namespace LeanVM.Cost.Decoder

open LeanVM.Cost LeanVM.Parameters LeanVM.Semantics LeanVM.Extraction.Fast LeanVM.Guest.Located
open LeanVM.Guest.B1 LeanVM.Node

@[expose] public section

/-- **An execution's memory as a vector**: its encoding is the memory's own
(`encodeValue_memoryVector`), the array of its words. -/
def memoryVector {κ : ℕ} (L : MemoryImage κ) : Vector E (2 ^ κ) := Vector.ofFn L

/-- The vector of the memory is encoded as the memory (`encodeFiniteFunction`). -/
theorem encodeValue_memoryVector {κ : ℕ} (L : MemoryImage κ) :
    encodeValue (memoryVector L) = encodeValue L := by
  show MachineValue.array ((Vector.ofFn L).toArray.map encodeValue) =
    MachineValue.array (Array.ofFn fun i ↦ encodeValue (L i))
  congr 1
  apply Array.ext
  · simp
  · intro i h1 h2; simp

/-! ## The input side -/

/-- **The address tables**: the memory's `2^κ` addresses (`memT`) and the bytecode's
(`codeT`), sorted (`Extraction.Fast.powTable`). -/
def decoderTables (prog : LeanIsaProgram) (κ : ℕ) : Array (ℕ × ℕ) × Array (ℕ × ℕ) :=
  (powTable κ, powTable prog.logSize)

/-- **The reader of the memory vector** through the address table `memT`
(`Located.readTable memT mem.get`). -/
def memReader (memT : Array (ℕ × ℕ)) {κ : ℕ} (mem : Vector E (2 ^ κ)) (a : K) : Option E :=
  (gLogTable memT κ a).map mem.get

/-! ## The output side -/

/-- A decoding of its three fields. Compiled as a function of its own: the caller passes the
fields as values. -/
def decodedOf (s : LeanVM.Protocol.Digest) (st : NodeStatement) (w : NodeWitness) :
    SeedStatementAndWitness :=
  ⟨s, st, w⟩

/-- **The decoding**: the seed and the statement off `main`'s valuation `σ` and the reader `rd`
(the statement's counts by the logarithm's tables `D`), the witness `w` given. -/
noncomputable def decoderOutput (D : DiscreteLogTables) (σ : LeanVM.Guest.Core.Val)
    (rd : LeanVM.Guest.Core.Reader) (w : NodeWitness) : SeedStatementAndWitness :=
  decodedOf (Main.decSeed σ) (decStmtD D σ rd) w

cost_compile decoderTablesC := decoderTables
cost_compile memReaderC := memReader
cost_compile decodedOfC := decodedOf
cost_compile decoderOutputC := decoderOutput

end

end LeanVM.Cost.Decoder
