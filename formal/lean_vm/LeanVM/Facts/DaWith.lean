/-
  LeanVM.Facts.DaWith

  The membership challenge the outer verifier derives from a root (`membershipChallengeOf`), and
  its form with the proofs' hash and duplex. Moved here from `Statement/LeanVmGuest.lean`, names
  kept: no end statement names them.
-/

module

public import Statement.LeanVmGuest
public import LeanDa.Scheme
public import Statement.Fast.Keccak
public import Statement.Fast.CubicExt
public import Statement.Fast.FieldWords
public import LeanDa.WithHashBridge
public import LeanVM.Guest.WithHash

namespace LeanVM.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash

@[expose] public section

/-- **The membership challenge of a root**, as the outer verifier derives it
(`membership_challenge`, `crates/verifier/src/da.rs:14-17`): the statement's
`LeanDa.membershipChallengeWith` over Keccak-f[1600], its sponge seeded with the label's hash and
the root, squeezed once. A DA claim's challenge is the root's where the outer verifier accepts
it. -/
def membershipChallengeOf (root : Digest) : E :=
  Id.run (LeanDa.membershipChallengeWith (m := Id) keccakF1600 root.toBytes)

/-- **The challenge with the proofs' hash and duplex** (`lean_da`'s
`membershipChallengeM_eq_withHash`). -/
theorem membershipChallengeOf_eq_withHash (root : Digest) :
    membershipChallengeOf root = Id.run (LeanDa.membershipChallengeMWithHash
      (LeanDa.keccakDigestBytes (m := Id) keccakF1600) keccakF1600 root.toBytes) := by
  rw [membershipChallengeOf, LeanDa.membershipChallengeM_eq_withHash]

end
end LeanVM.Da
