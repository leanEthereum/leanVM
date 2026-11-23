/-
  LeanVM.Guest.B1.Gkr.RecsC

  The honest round records of a run of GKR rounds.
-/

module

public import LeanVM.Guest.B1.Gkr.Rounds
import LeanVM.Guest.B1.Tables.Basic

/-!
# Round records, completely

`RecAt rd rec cur cs es claim s r`: the record at `rec` carries the capacity, the cursor `4r` words
on and the claim after the first `r` rounds of `gkrRun cs es claim s`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- **A round record** after the first `r` rounds: the sponge's capacity, the cursor and the
claim. -/
def RecAt (rd : Reader) (rec cur : E) (cs : List (List E)) (es : List E) (claim : E) (s : Fs)
    (r : ℕ) : Prop :=
  TbCapAt rd rec 0 1 (gkrRun (cs.take r) (es.take r) claim s).2.2.cap ∧
    LoadHolds rd rec 5 (cur * gen ^ (4 * r)) ∧
    LoadHolds rd rec 6 (gkrRun (cs.take r) (es.take r) claim s).2.1

end
end LeanVM.Guest.B1.Tables
