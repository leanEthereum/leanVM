import SphincsFors.Search

/-!
# The counter search

`otsSign` is the search of `Search.lean` run over the encoding inputs: the counter rides in the
hashed bytes, so the inputs below the wrap are distinct, and the trial budget is exactly the wrap.
What remains to bound its failure is the share of answers the target-sum code rejects.
-/

open OracleComp OracleSpec ENNReal

set_option maxRecDepth 10000

namespace SphincsFors.Completeness

open Concrete Seeded

/-- The input the counter search hashes at counter `c`. -/
def encodeInput (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : Digest) (c : Nat) : HashInput :=
  tweakableHashInput parameter (.encoding lay tree leaf)
    (bytesLE 16 message ++ bytesLE 4 (BitVec.ofNat counterBits c))

theorem encodeInput_inj (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (message : Digest) {c c' : Nat}
    (hc : c < 2 ^ 32) (hc' : c' < 2 ^ 32)
    (h : encodeInput parameter lay tree leaf message c
      = encodeInput parameter lay tree leaf message c') : c = c' := by
  simp only [encodeInput, tweakableHashInput, List.append_assoc] at h
  have hpayload := List.append_cancel_left h
  have hpayload' := List.append_cancel_left hpayload
  exact counter_bytes_inj hc hc' (List.append_cancel_left hpayload')

/-- The counter search exhausts its budget with probability at most the rejection share to the budget. -/
theorem probEvent_otsSign (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (seed : MasterSeed) (message : Digest) (cache : QueryCache HashSpec)
    (hfresh : ∀ c, c < encodingAttemptLimit →
      cache (encodeInput parameter lay tree leaf message c) = none) :
    Pr{let r ← ((simulateQ randomOracle
        (otsSign parameter lay tree leaf seed message
          : OracleComp HashSpec (Option (Counter × (ChainIndex → Digest))))).run cache)}[r.1 = none]
      ≤ failMass (fun out => TargetSum.decodeDigest (truncateHash out)) ^ encodingAttemptLimit := by
  rw [otsSign, otsSignFrom_eq_searchLoop]
  exact probEvent_searchLoop _ _ _ encodingAttemptLimit
    (fun s s' hs hs' heq => encodeInput_inj parameter lay tree leaf message hs hs' heq)
    encodingAttemptLimit 0 (by simp) cache (fun s _ hsb => hfresh s hsb)

end SphincsFors.Completeness
