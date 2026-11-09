import LeanVM.Guest.Hints
import LeanVM.Guest.AcceptableChild

/-!
# The honest hint generator on a raw-signature leaf

A leaf holding one leanXMSS claim by a signature: the streams it pops and the number of entries
of each, the node's own entries in full, and the signature's entries as `lean_xmss_hints` lays
them out (its leaf index shifted by each multiple of 8 and those windows, then per layer the 16
siblings on its path, the randomizer, its 15 digit groups in one push and 58 chain values). The signature is not a valid one: the generator computes what an honest
run pops, whatever it is given. And the coverage planner on claims held twice: by a raw signature
and two children, and by both children. `lake exe guest-diff` checks the generator against Rust
aggregations.
-/

namespace LeanVMTests.Guest.Hints

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Node LeanVM.Guest
open LeanVM.Guest.Hints LeanVM.Guest.Coverage

def key : HashSig.PublicKey := ⟨BitVec.ofNat 128 0x1234, BitVec.ofNat 128 0x5678⟩

def message : HashSig.Message := BitVec.ofNat 256 0x9abc

def signature : LeanXmss.Signature :=
  ⟨⟨0x10002, by decide⟩, fun l ↦ ⟨BitVec.ofNat 128 (l.val + 7), fun i ↦ BitVec.ofNat 128 i.val,
    fun i ↦ BitVec.ofNat 128 (100 + i.val)⟩⟩

def seed : Digest := keccak256 [1, 2, 3]

def leaf : NodeStatement := ⟨⟨[(key, message)], [], zeroDigest⟩, ⟨List.replicate 23 0, 5⟩⟩

def witness : NodeWitness := ⟨[], [((key, message), signature)], [], none, ⟨[], 0⟩⟩

def streams : Streams := honestStreams [] seed leaf witness

/- The streams, in the order of their first push, and their entry counts. -/
#guard streams.map (fun s ↦ (s.1, s.2.length)) ==
  [("meta", 1), ("fs_seed", 1), ("signers_split", 1), ("claims", 1), ("raw_index", 1),
    ("lx_index", 1), ("lx_windows", 1), ("lx_path", 32), ("randomizer", 2), ("lx_digits", 2),
    ("chain_starts", 116), ("leaf_defer", 1), ("da_pick", 1)]

def get (n : String) : List Entry := (streams.lookup n).getD []

#guard get "meta" == [[count 1, count 0, count 1, count 0, count 0, count 0, count 0, count 0]]
#guard get "fs_seed" == [digestCells seed]
#guard get "signers_split" == [[count 0, count 0, count 1]]
#guard get "claims" == [claimCells key.root key.parameter message]
#guard get "raw_index" == [[count 0]]
#guard get "leaf_defer" == [[5]]
/- No blob matrix and no child: the node publishes its own slot, zeros. -/
#guard get "da_pick" == [[count 0]]

/- The leaf index `2^16 + 2` shifted right by `0, 8, 16, 24`, and those shifts' low bytes in the
exponent. -/
#guard get "lx_index" == [[word 0x10002 0 0, word 0x100 0 0, word 1 0 0, word 0 0 0]]
#guard get "lx_windows" == [[count 2, count 0, count 1, count 0]]

/- The randomizers and the chain values, bottom layer first. -/
#guard get "randomizer" == [[cell128 (BitVec.ofNat 128 7)], [cell128 (BitVec.ofNat 128 8)]]
#guard get "chain_starts" == (List.range 116).map fun i ↦ [cell128 (BitVec.ofNat 128 (i % 58))]

/- The sibling of every node on the path, bottom first: at level `l` of the bottom tree, `100 + l`
(the guest orders each pair by the index's bit, which its window's dispatch arm fixes). -/
#guard ((get "lx_path").take 16).zipIdx.all fun (e, l) ↦
  e == [cell128 (BitVec.ofNat 128 (100 + l))]

/- Each layer's digits in one push, 15 groups of 4 (58 digits): an entry of 15 cells. -/
#guard (get "lx_digits").map List.length == [15, 15]

/- A digit group's index: its digits little endian in base 4, in the exponent; leanXMSS's groups of
4, leanSPHINCS's of 3, one push each. -/
#guard digitHints lxDigitGroup [1, 2, 3, 0, 1] == [[count 57], [count 1]]
#guard digitGroups [1, 2, 3, 0] == [("digits", [count 57]), ("digits", [count 0])]

/- A list of `n` claims splits into `n / 136` whole frames of eight groups, then the rest's whole
groups of 17 and the claims after them; `exponent_bytes` puts each byte in the exponent. -/
#guard listSplit 40 == [count 0, count 2, count 6]
#guard listSplit 300 == [count 2, count 1, count 11]
#guard exponentBytes [1, 2, 3] == [count 1, count 2, count 3]

/-! ## Coverage -/

/- `b` is held by the raw signature, then by both children, which take duplicate slots after the
declared `a, b, c`; `d`, undeclared, takes one too. -/
#guard let r := coveragePlan ["a", "b", "c"] ["b"] [["a", "b"], ["b", "c", "d"]]
  (r.duplicates, r.directSlots, r.childSlots) == (["b", "b", "d"], [1], [[0, 3], [4, 2, 5]])

end LeanVMTests.Guest.Hints
