module

public import LeanVM.Cost.Decoder.Top
public import LeanVM.Cost.Decoder.Equations
public import LeanVM.Cost.Decoder.EntryTableEq
public import LeanVM.Guest.Fast.PreTest

/-!
# The decoder's top is the deployed decoder

**`decTop_eq`**: on the memory vector of an execution of the guest, the compiled top's function is
`End.decode`: `decode_eq_ends` (the top's ends), at the discrete logarithm
(`discreteLog_discreteLogSpec`), with the precondition by the table
(`preTest_eq_preTable`), the leanSPHINCS reader's frames looked up once (`sphincsAtFrameT_eq`), the frame map on the sorted
entry array (`frameAtA_eq`), the witness
staged (`decWitNStaged_eq`) and the cursor's length (`cursorLength_tables`).
-/

namespace LeanVM.Cost.Decoder

open LeanVM.Cost LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Located
open LeanVM.Guest.B1 LeanVM.Guest.Fast LeanVM.Extraction.Fast LeanVM.Node

attribute [local instance] lexOrd

@[expose] public section

/-- **The compiled top's function is the deployed decoder.** -/
theorem decTop_eq {κ : ℕ} (L : MemoryImage κ) :
    decTop LeanVM.Guest.guestProgram κ (memoryVector L) = LeanVM.Guest.End.decode L := by
  rw [decode_eq_ends discreteLog_discreteLogSpec L]
  simp only [decTop, decTopTables, decTopStates, decTopFrames, sphincsAtFrameT_eq, xmssAtFrameT_eq, frameAtA_eq,
    ← preTest_eq_preTable, decWitNStaged_eq, cursorLength_tables]

end

end LeanVM.Cost.Decoder
