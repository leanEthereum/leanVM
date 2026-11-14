module

public import LeanVM.Cost.Decoder.Ends
public import LeanVM.Guest.Fast.Decode
public import LeanVM.Cost.Decoder.GuestTablesCheck
import all LeanVM.Guest.B1.Main.Interface

/-!
# The guest decoder's compiled chain: the staged functions are the decoder's

The staged forms the chain compiles are the deployed decoder's functions, proved apart from the
compiled modules (their kernel checks stay small):

* `decWitStaged_eq : decWitStaged discreteLogTables = B1.Main.decWit`;
* `decWitNStaged_eq : decWitNStaged discreteLogTables readerTabs = Guest.Fast.decWitN`, the
  deployed decoder's witness at the frame map keyed by index (`Guest.Fast.decode_eq_numbered`);
* `replayStatesOf_eq : replayStatesOf memT codeT prog mem = Located.statesTable memT codeT prog
  mem.get replayFuel ⟨gpow 0, 1⟩`, the replay `decode_eq_numbered` reads, on the memory vector
  (`statesVec_eq`: each step `stepVec`, which is `stepTable` at `mem.get`);
* the top's ends (`Ends.lean`): `memReader_memoryVector : memReader memT (memoryVector L) =
  readTable memT L`, `mainVal_eq : mainVal = End.mainValWith`, and **`decode_eq_ends`**: the
  deployed decoder `End.decode L` through `decoderTables`, `memReader`, `replayStatesOf`,
  `mainVal` and `decoderOutput`, the witness `decWitN` at the frame map keyed by index.

The other restated functions' equations at the tables built (`…D_tables`,
`dvWitND_tables`, `cursorLength_tables`, `gLogD_tables`; the readers' off arrays,
`xmssSigOfA_tabs`, `vsPiOfA_tabs`, in `Guest/Fast/`) are next to them.
-/

namespace LeanVM.Cost.Decoder

open LeanVM.Cost LeanVM.Parameters LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.B1.Main
open LeanVM.Protocol.Verifier LeanVM.Node LeanVM.Extraction.Fast

@[expose] public section

/-- **The staged witness is `decWit`**, at the tables built. -/
theorem decWitStaged_eq : decWitStaged discreteLogTables = decWit := by
  funext σ rd wX wS wD wV wA
  rw [decWitStaged_eq_lists]
  unfold nodeWitnessOf kidsAt xmssRawsAt sphincsRawsAt daWitness aggArgs decWit
  simp only [nKidsD_tables, decKidD_tables, rawXmssD_tables, rawSphincsD_tables, nRawXD_tables,
    nRawSD_tables, nDirectD_tables]

open LeanVM.Guest.Fast in
/-- **The staged witness is `decWitN`**, at the tables built and the leanSPHINCS reader off the
frame map. -/
theorem decWitNStaged_eq (σ : Val) (rd : Reader) (Vn : NFrames) (cl : E → E → ℕ) :
    decWitNStaged discreteLogTables readerTabs σ rd Vn (xmssAtFrame readerTabs Vn)
      (sphincsAtFrame readerTabs σ Vn) cl =
      decWitN σ rd Vn cl := by
  unfold decWitNStaged decWitN daAtFrame xmssAtFrame sphincsAtFrame proofAtFrame
  simp only [show readerTabs.xmss = xmssTabs from rfl, show readerTabs.sphincs = spTabs from rfl,
    show readerTabs.whir = whirTabs from rfl, xmssSigOfA_tabs, vsPiOfA_tabs]
  rw [decWitStaged_eq, dvWitND_tables]
  rfl

open LeanVM.Semantics LeanVM.Extraction.Fast LeanVM.Guest.Located in
/-- **On the memory vector, `statesVec` is `statesTable`**, the final registers given. -/
theorem statesVec_eq (memT codeT : Array (ℕ × ℕ)) (prog : LeanVM.Semantics.LeanIsaProgram) {κ : ℕ}
    (mem : Vector E (2 ^ κ)) :
    ∀ fuel r, statesVec memT codeT prog mem (Registers.final prog) fuel r =
      statesTable memT codeT prog mem.get fuel r
  | 0, r => rfl
  | fuel + 1, r => by
    rw [statesVec, statesTable, stepVec_eq]
    congr 1
    split
    · rfl
    · cases stepTable memT codeT prog mem.get r with
      | none => rfl
      | some r' => exact statesVec_eq memT codeT prog mem fuel r'

open LeanVM.Semantics LeanVM.Guest.Located in
/-- **The compiled replay is the decoder's**: the run from `(g^0, 1)` over `replayFuel`
(`Guest.Fast.decode_eq_numbered`'s `states`), the memory image `mem.get`. -/
theorem replayStatesOf_eq (memT codeT : Array (ℕ × ℕ)) (prog : LeanVM.Semantics.LeanIsaProgram)
    {κ : ℕ}
    (mem : Vector E (2 ^ κ)) :
    replayStatesOf memT codeT prog mem = statesTable memT codeT prog mem.get replayFuel ⟨addressOfIndex 0, 1⟩ :=
  statesVec_eq memT codeT prog mem replayFuel _

/-! ## The top's ends -/

/-- The vector of the memory, read, is the memory. -/
theorem memoryVector_get {κ : ℕ} (L : LeanVM.Semantics.MemoryImage κ) : (memoryVector L).get = L := by
  funext i
  exact Vector.getElem_ofFn i.isLt

open LeanVM.Semantics LeanVM.Guest.Located in
/-- **The reader of the memory vector is the memory's** (`readTable`). -/
theorem memReader_memoryVector (memT : Array (ℕ × ℕ)) {κ : ℕ} (L : MemoryImage κ) :
    memReader memT (memoryVector L) = readTable memT L := by
  funext a
  unfold memReader readTable
  rw [memoryVector_get]

/-- `main`'s certificate's cells (`certOf 1`, `Glob.lean`), its two windows. -/
theorem certOf_one_locs :
    (LeanVM.Guest.certOf 1).locs = LeanVM.Guest.Fn.«main».cert_w0_0 ++ LeanVM.Guest.Fn.«main».cert_w1_0 := by
  show List.flatten [LeanVM.Guest.Fn.«main».cert_w0_0, LeanVM.Guest.Fn.«main».cert_w1_0] = _
  simp

/-- `main`'s row of the table of cells is its certificate's cells. -/
theorem guestLocs_main (i : ℕ) :
    (guestLocs.getD 1 #[]).getD i 0 = (LeanVM.Guest.certOf 1).locs.getD i 0 := by
  rw [← guestLocs_eq (j := 1) (by decide), Array.getD_eq_getD_getElem?,
    List.getD_eq_getElem?_getD, Array.getElem?_toList]

/-- **`main`'s valuation, compiled, is the decoder's** (`End.mainValWith`). -/
theorem mainVal_eq : mainVal = LeanVM.Guest.End.mainValWith := by
  funext rd v
  unfold mainVal LeanVM.Guest.End.mainValWith
  rw [guestLocs_main]

/-- **`main`'s valuation off the table is the one off its certificate's two lists**, on every
value. -/
theorem mainVal_eq_cert (rd : Reader) (v : V) :
    mainVal rd v = LeanVM.Guest.Located.wordWith rd 1
      ((LeanVM.Guest.Fn.«main».cert_w0_0 ++ LeanVM.Guest.Fn.«main».cert_w1_0).getD v.idx 0) := by
  unfold mainVal
  rw [guestLocs_main, certOf_one_locs]

open LeanVM.Semantics LeanVM.Guest.Located LeanVM.Extraction.Fast LeanVM.Guest.Fast in
/-- **The deployed decoder through the top's ends**: the address tables (`decoderTables`), the
reader of the memory vector (`memReader`), the replay (`replayStatesOf`), `main`'s valuation
(`mainVal`) and the decoding (`decoderOutput`), the witness `decWitN` at the frame map keyed by
index (`Guest.Fast.decode_eq_numbered`), the cursor's length by any discrete logarithm `dl`. -/
theorem decode_eq_ends {dl : K → Option ℕ} (hdl : DiscreteLogSpec dl) {κ : ℕ}
    (L : MemoryImage κ) :
    LeanVM.Guest.End.decode L =
      let tabs := decoderTables LeanVM.Guest.guestProgram κ
      let mem := memoryVector L
      let rd := memReader tabs.1 mem
      let states := replayStatesOf tabs.1 tabs.2 LeanVM.Guest.guestProgram mem
      let σ := mainVal rd
      decoderOutput discreteLogTables σ rd
        (decWitN σ rd (frameVFastN (preTest rd) states rd) (cursorLenWith dl)) := by
  rw [decode_eq_numbered hdl L]
  simp only [decoderTables, memReader_memoryVector, replayStatesOf_eq, memoryVector_get, mainVal_eq,
    decoderOutput, decStmtD_tables, decodedOf]

end

end LeanVM.Cost.Decoder
