import Whir.SpongefishCurrentRecordModeCapture

/-! The successful current opening parser is joined to the actual next squeeze.
Every returned byte has a bounded whole raw coordinate that retains the parsed
record. This is a deterministic hand-port statement, not Rust correspondence,
a random-oracle independence premise, or a native knowledge theorem. -/
namespace Whir.SpongefishCurrentRecordOpeningQueries
open Concrete FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame
open SpongefishSessionAdapter SpongefishPCSRoundFrames SpongefishRecordBindingParser
set_option autoImplicit false

/-- Successful parsing and squeezing determine the literal reference and reply
at every byte position. Neither a saved-record equality nor a trusted parser
is supplied. The complete construction path budget remains explicit. -/
theorem verified_squeezed_byte {Q : Nat} (c : Compression) (iv : Digest32)
    (cur next : Cursor) (r : Record)
    (accepted : verify c cur r = some next) (valid : r.shape.Valid)
    (pending : r.context.pending.length ≤ 64) (point : r.point.length = r.shape.logN)
    (represented : RepresentsCurrent c iv next.pending next.state)
    (framed : SpongefishCurrentModeQueries.FrameDomain next.pending)
    (n : Nat) (positive : n ≠ 0) (state : State) (bytes : List Byte)
    (squeezed : squeeze c next.state n = .ok (state,bytes)) (j : Nat) (within : j < n)
    (work : pathCost (SpongefishCurrentModeQueries.coordinate next.pending
      ((next.pending.consumed+j)/32)) ≤ Q) :
    let q := SpongefishCurrentModeQueries.coordinate next.pending
      ((next.pending.consumed+j)/32)
    r ∈ SpongefishCurrentRecordModeCapture.rawRecords r.shape iv (constructionKey Q iv q work) ∧
      bytes[j]'(by obtain ⟨_,len⟩ := squeeze_exact_cursor c next.state state n bytes squeezed; omega) =
        evalCoordinate c iv q ⟨(next.pending.consumed+j)%32,Nat.mod_lt _ (by decide)⟩ := by
  constructor
  · rw [SpongefishCurrentRecordModeCapture.rawRecords_construction _ _ _
      (SpongefishCurrentModeQueries.squeezed_coordinate_admissible c iv next.pending
        next.state state represented framed n positive bytes squeezed j within) work]
    exact SpongefishCurrentRecordModeCapture.verified_record_coordinate c cur next r accepted
      valid pending point _
  · exact SpongefishCurrentModeQueries.squeezed_byte c iv next.pending next.state state
      represented n positive bytes squeezed j within

#print axioms verified_squeezed_byte
end Whir.SpongefishCurrentRecordOpeningQueries
