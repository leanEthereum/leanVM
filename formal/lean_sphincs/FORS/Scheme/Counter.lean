import FORS.Scheme.Search

/-!
# The counter search

`otsSign` is the search of `Scheme/Search.lean` run over the encoding inputs: the counter rides in the
hashed bytes, so the inputs below the wrap are distinct, and the trial budget is exactly the wrap.
What remains to bound its failure is the share of answers the target-sum code rejects.
-/

open OracleComp OracleSpec ENNReal

set_option maxRecDepth 10000

namespace FORS.Completeness

variable [Params]

open Concrete Seeded

/-- The input the counter search hashes at counter `c`. -/
def encodeInput (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : HashInput) (c : Nat) : HashInput :=
  tweakableHashInput parameter (.encoding lay tree leaf)
    (message ++ bytesLE 4 (BitVec.ofNat counterBits c))

theorem encodeInput_inj (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (message : HashInput) {c c' : Nat}
    (hc : c < 2 ^ 32) (hc' : c' < 2 ^ 32)
    (h : encodeInput parameter lay tree leaf message c
      = encodeInput parameter lay tree leaf message c') : c = c' := by
  simp only [encodeInput, tweakableHashInput, List.append_assoc] at h
  have hpayload := List.append_cancel_left h
  have hpayload' := List.append_cancel_left hpayload
  exact counter_bytes_inj hc hc' (List.append_cancel_left hpayload')

end FORS.Completeness
