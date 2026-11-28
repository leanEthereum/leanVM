/-
  LeanVM.Guest.Hints

  The honest hint generator of the aggregation guest, as `guest-diff` and the tests name it: the
  statement's witness generation (`Statement/LeanVmGuestProver.lean`) and the initial memory of a run
  on a node's statement.
-/

module

public import Statement.LeanVmGuestProver
public import LeanVM.Facts.ClaimBytes
public import LeanVM.Guest.Batch.Def
public import LeanVM.Guest.Word
public import LeanVM.Guest.Coverage

/-!
# The honest hint generator

`honestStreams bytecode seed s w` is every stream the guest pops with `hint_witness`, each a list
of entries in the order the guest pops them, for a run on the statement `s` under the seed
`seed` held by the witness `w`: the statement's own (`LeanVM.Guest.guestStreams`, the pushes of
`aggregate`, `crates/aggregation/src/node.rs`, in `LeanVM.Guest.Prover.honestPushes`), so that
`guest-diff` compares the trusted statement's witness generation with the Rust's.
`publicInput seed s` is the initial memory, the statement's digest at cells `g^0` and `g^1`. The
encodings are the statement's, under the names the tests use.
-/

namespace LeanVM.Guest.Hints

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Node

@[expose] public section

export LeanVM.Guest.Prover (Entry Streams group claimGroup claimBig digitGroup lxDigitGroup lxWindow
  streamChunk queryWindowBits count bit cellOfBytes cellsOfBytes cell128 digestCells exponentBytes
  listSplit listPushes digitHints digitGroups ordered xmssLayer xmssHints sphincsHints daHints
  recordQueries childQueries climbSteps leafCells capDepthOf levelHints merkleHints stackHints
  childHints childSlotPushes batchPushes daPick honestPushes)

/-- A claim's four cells: the key's two halves (leanXMSS: root, parameter; leanSPHINCS: `PK.seed`,
`PK.root`), the message (`claim_cells`, `crates/aggregation/src/statement.rs`). -/
def claimCells (root parameter : BitVec 128) (message : BitVec 256) : Entry :=
  cellsOfBytes (claimBytesOf root parameter message)

/-- **The honest streams**: the statement's witness streams (`LeanVM.Guest.guestStreams`). -/
def honestStreams (bytecode : List K) (seed : Digest) (s : NodeStatement) (w : NodeWitness) :
    Streams :=
  LeanVM.Guest.guestStreams bytecode seed s w

/-- **The public input**, the initial memory at `g^0` and `g^1`: the statement's digest. -/
def publicInput (seed : Digest) (s : NodeStatement) : List E :=
  [(digestHalves (statementDigest seed s)).1, (digestHalves (statementDigest seed s)).2]

end
end LeanVM.Guest.Hints
