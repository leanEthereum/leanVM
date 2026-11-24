/-
  LeanVM.Guest.B1.Main.MainGoalsClT

  The honest shape of `claim_list_digest`'s trees (`Budget.NodeHonest`).
-/

module

public import LeanVM.Guest.B1.Main.MainGoalsF
public import LeanVM.Guest.B1.Digest.ClaimListAt
public import LeanVM.Guest.AcceptableChild

/-!
# `claim_list_digest`'s trees of honest shape

`clHonest n`: the honest shape of `claim_list_digest` on a list of `n` claims
(`Digest/ClaimListAt.lean`).
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest.B1.Digest
open LeanVM.Guest.B1 (CompleteAtDT Returns)
open LeanVM.Guest.Hints (claimCells)
open LeanVM.Guest.Budget (NodeHonest)

@[expose] public section

/-- **`claim_list_digest`'s honest shape** on `n` claims. -/
def clHonest (n : ℕ) : Tree → Prop :=
  NodeHonest coreProgram "claim_list_digest" (clQ n) (clCalls n) (clBufs n) (clTs n)

end
end LeanVM.Guest.B1.Main
