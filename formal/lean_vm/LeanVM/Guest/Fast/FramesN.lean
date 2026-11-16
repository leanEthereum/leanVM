module

public import LeanVM.Guest.Fast.Main
public import LeanVM.Guest.Located.ReplayFast

/-!
# The replayed frame map, keyed by index

`Located.frameVFast` (`Located/ReplayFast.lean`) looks a call up in the entry table at its callee
name's index (`nameIndex`) and reads the frame by that function's places (`guestPlaces`).

* `frameVFastN pre states rd j`: the same lookup keyed by the index `j` (through `canonIndex`),
  no name read; `frameVFastN_eq`: it is `frameVFast` at `decoderFunctionName j`, for every `j`.

Apart from `Fast/Decode.lean` (the deployed decoder through it), so that the compiled chain
(`Cost/Decoder/`) imports no soundness proof.
-/

namespace LeanVM.Guest.Fast

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Node
open LeanVM.Guest.Located LeanVM.Extraction.Fast LeanVM.Cost.Decoder

attribute [local instance] lexOrd

@[expose] public section

/-- **The replayed frame map, keyed by index** (`frameVFast`): the call of function
`canonIndex j` looked up in the entry table, its frame read by its places. -/
noncomputable def frameVFastN (pre : ℕ → K → Bool) (states : List (Registers K)) (rd : Reader) :
    NFrames :=
  let table := entryTable pre states rd
  fun j args rets ↦ match table.get? (callKey (canonIndex j) args rets) with
    | some fp => fun v ↦ placeWith rd fp ((guestPlaces.getD (canonIndex j) #[]).getD v.idx 0)
    | none => fun _ ↦ 0

/-- **Keyed by index, the replayed frame map is the one keyed by name.** -/
theorem frameVFastN_eq (pre : ℕ → K → Bool) (states : List (Registers K)) (rd : Reader) (j : ℕ) :
    frameVFastN pre states rd j = frameVFast pre states rd (decoderFunctionName j) := by
  have h1 : nameIndex (decoderFunctionName j) = canonIndex j := nameIndex_decoderFunctionName j
  unfold frameVFastN frameVFast
  rw [h1]
  funext args rets
  cases (entryTable pre states rd).get? (callKey (canonIndex j) args rets) <;> rfl

end
end LeanVM.Guest.Fast
