import LeanVM.Guest.Hints

/-!
# The honest hint generator on a raw-signature leaf

A leaf holding one leanXMSS claim by a signature: the streams it pops and the number of entries
of each, the node's own entries in full, and the signature's entries as `lean_xmss_hints` lays
them out (its leaf index's bits, then per layer 16 ordered pairs, the randomizer, 20 digit groups
and 58 chain values). The signature is not a valid one: the generator computes what an honest
run pops, whatever it is given. And the coverage planner on claims held twice: by a raw signature
and two children, and by both children. `lake exe guest-diff` checks the generator against Rust
aggregations.
-/

namespace LeanVMTests.Guest.Hints

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Node LeanVM.Guest LeanVM.Guest.Hints

def key : LeanXmss.PublicKey := ⟨BitVec.ofNat 128 0x1234, BitVec.ofNat 128 0x5678⟩

def message : LeanXmss.Message := BitVec.ofNat 256 0x9abc

def signature : LeanXmss.Signature :=
  ⟨⟨0x10002, by decide⟩, fun l ↦ ⟨BitVec.ofNat 128 (l.val + 7), fun i ↦ BitVec.ofNat 128 i.val,
    fun i ↦ BitVec.ofNat 128 (100 + i.val)⟩⟩

def seed : Digest := blake2sBytes [1, 2, 3]

def leaf : NodeStatement :=
  ⟨⟨[(key, message)], [], []⟩,
    ⟨List.replicate 22 0, 5, List.replicate 28 0, 6, 7⟩⟩

def witness : NodeWitness := ⟨[], [.direct signature], [], [], ⟨[], [], 0, 0, 0⟩⟩

def streams : Streams := honestStreams [] seed leaf witness

/- The streams, in the order of their first push, and their entry counts. -/
#guard streams.map (fun s ↦ (s.1, s.2.length)) ==
  [("meta", 1), ("fs_seed", 1), ("signers_split", 1), ("claims", 1), ("raw_index", 1),
    ("leaf_index_bits", 1), ("siblings", 32), ("randomizer", 2), ("digits", 40),
    ("chain_starts", 116), ("leaf_defer", 1), ("da_meta", 1)]

def get (n : String) : List Entry := (streams.lookup n).getD []

#guard get "meta" == [[count 1, count 0, count 1, count 0, count 0, count 0, count 0, count 0]]
#guard get "fs_seed" == [digestCells seed]
#guard get "signers_split" == [[count 0, count 0]]
#guard get "claims" == [claimCells key.root key.parameter message]
#guard get "raw_index" == [[count 0]]
#guard get "leaf_defer" == [[5, 6, 7]]
#guard get "da_meta" == [[count 0, count 0]]

/- The leaf index `2^16 + 2`, little endian. -/
#guard get "leaf_index_bits" ==
  [(List.range 32).map fun b ↦ if b = 1 ∨ b = 16 then 1 else 0]

/- The randomizers and the chain values, bottom layer first. -/
#guard get "randomizer" == [[cell128 (BitVec.ofNat 128 7)], [cell128 (BitVec.ofNat 128 8)]]
#guard get "chain_starts" == (List.range 116).map fun i ↦ [cell128 (BitVec.ofNat 128 (i % 58))]

/- Every node on the path is with its sibling: at level `l` of the bottom tree, sibling `100 + l`
on the right below level `1`, at it on the left (bit `1` of the key `2^16 + 2` is set). -/
#guard ((get "siblings").take 16).zipIdx.all fun (pair, l) ↦
  pair.length == 2 && pair.getD (if l = 1 then 0 else 1) 0 == cell128 (BitVec.ofNat 128 (100 + l))

/- A digit group's index: its digits little endian in base 4, in the exponent. -/
#guard digitGroups [1, 2, 3, 0] == [("digits", [count 57]), ("digits", [count 0])]

/-! ## Coverage -/

/- `b` is held by the raw signature, then by both children, which take duplicate slots after the
declared `a, b, c`; `d`, undeclared, takes one too. -/
#guard let r := plan ["a", "b", "c"] ["b"] [["a", "b"], ["b", "c", "d"]]
  (r.dups, r.raw, r.children) == (["b", "b", "d"], [1], [[0, 3], [4, 2, 5]])

end LeanVMTests.Guest.Hints
