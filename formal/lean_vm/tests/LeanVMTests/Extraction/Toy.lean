import LeanVMTests.Extraction.ToyWords

/-!
# Tests: the extractor's list decoder on toy codes

Executable checks (`#guard`) of the knowledge extractor's list decoder (`decodeStacksAt`:
Guruswami–Sudan at message length `2^κ + 6` on every lane, `toNovel (κ + 1)`, pruning, `stackOf`,
`LeanVM/Protocol/Extraction/Extractor.lean`) on toy stacks of `κ = μ − 6 = 3` message variables
(the least it decodes, at level 0's degree `2^κ + 5`; the deployed shapes, `κ ≥ 9`, are far too
large for it, as its cost table says), encoded on the `n = 2^(κ+R)` columns of their `64` lanes
with some whole columns replaced by random leaves (`ToyWords.lean`): it finds the stack when the
errors are within the radius `n − A`, including past the unique decoding radius
`⌊(n − 2^κ − 6)/2⌋` (`ToyRadius.lean`), and finds nothing when they are not; it finds it also
when the lanes carry high parts `W_κ·H_u` (`wordHighOf`). Then the parameters at the deployed
shapes: the natural Johnson threshold and the decoder's multiplicities, against the table computed
offline with exact integers; and the Merkle inversion (`committedLeaves`): under an injective toy
hash, the leaves are recovered from the answer table, an unanswered leaf is zeros, and the keys'
order and repetitions do not matter. The fast path is `ToyFast.lean`.
-/

namespace LeanVMTests.Extraction

open CompPoly LeanVM.Parameters LeanVM.Parameters.Whir LeanVM.Extraction
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile

/-! ## The list decoder -/

-- `κ = 3`, `R = 1`: `n = 16` columns, messages of `2^3 + 6 = 14` coefficients, `A = 15`; one
-- error, in column `2`, among the first `2^κ` columns, on which the fast path gives up.
#guard johnsonThreshold 9 1 = 15
#guard decodes 1 15 (randomStack 1 9) (corrupt 1 [2] (wordOf 1 (randomStack 1 9))) = (true, 1)

-- `κ = 3`, `R = 2`: `n = 32`, `A = 22`; eleven errors, past the radius `n − A = 10`: nothing
-- is decoded (ten, within it, in `ToyRadius.lean`).
#guard decodes 2 22 (randomStack 3 9)
  (corrupt 3 [0, 1, 3, 5, 7, 9, 11, 13, 15, 17, 19] (wordOf 2 (randomStack 3 9))) = (false, 0)

-- A word with high parts (`enc(block u) + W_3·H_u`, `deg H_u < 6`), the candidates of level 0's
-- list at its degree `2^3 + 5`: the decoder lists the stack, its lanes' low parts.
#guard decodes 1 15 (randomStack 5 9) (corrupt 5 [4] (wordHighOf 1 5 (randomStack 5 9))) = (true, 1)

/-! ## The parameters at the deployed shapes

The Johnson threshold `A` at level 0's degree `2^κ + 5`, the multiplicity `m` and the `Y`-degree
`ℓ = ⌊(m·A − 1)/(2^κ + 5)⌋` at `R = 1`, `μ = 16, …, 30`, and the multiplicities at `R = 2`
(computed offline with exact integers). -/

#guard johnsonThreshold 16 1 = 1472
#guard (List.range 15).map (fun i ↦ gsMultiplicity (16 + i) 1) =
  [10, 15, 21, 29, 42, 59, 83, 90, 90, 90, 90, 90, 90, 90, 90]
#guard (List.range 15).map (fun i ↦
    let p := gsParams (16 + i) 1
    p.interp.weightedDegreeBound / (2 ^ (10 + i) + 5)) =
  [14, 21, 29, 41, 59, 83, 117, 127, 127, 127, 127, 127, 127, 127, 127]
#guard (List.range 15).map (fun i ↦ gsMultiplicity (16 + i) 2) =
  [14, 19, 28, 39, 55, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64]

/-! ## Merkle inversion -/

/-- A Merkle tree over the leaves under an injective toy hash (the `i`-th hashed string gets the
digest `(i, 0, 0, 7)`): the root and the answer table. -/
def merklize (leaves : Array (List K)) (ht : ℕ) : Digest × List (Bytes × Digest) := Id.run do
  let mut table : List (Bytes × Digest) := []
  let mut level : Array Digest := #[]
  for v in [0:2 ^ ht] do
    let d : Digest := #v[(table.length).toUInt64, 0, 0, 7]
    table := ((leaves.getD v []).flatMap K.toBytes, d) :: table
    level := level.push d
  for _ in [0:ht] do
    let mut next : Array Digest := #[]
    for j in [0:level.size / 2] do
      let d : Digest := #v[(table.length).toUInt64, 0, 0, 7]
      table := (digestBytes (level.getD (2 * j) default) ++
        digestBytes (level.getD (2 * j + 1) default), d) :: table
      next := next.push d
    level := next
  return (level.getD 0 default, table)

/-- The toy word of `κ = 3`, `R = 2` with two errors, its tree of height `5`, and the table. -/
def toyWord : Array (List K) := corrupt 4 [3, 9] (wordOf 2 (randomStack 4 9))

def toyTree : Digest × List (Bytes × Digest) := merklize toyWord 5

def toyAnswers (x : Bytes) : Option Digest := (toyTree.2.find? (·.1 == x)).map (·.2)

-- The inversion recovers every leaf.
#guard committedLeaves toyAnswers (toyTree.2.map (·.1)) toyTree.1 5 64 = toyWord

-- Leaf `0` unanswered: zeros there, the other leaves unchanged.
#guard
  let keys := toyTree.2.map (·.1) |>.filter (· != (toyWord.getD 0 []).flatMap K.toBytes)
  let answers : Bytes → Option Digest := fun x ↦ if keys.contains x then toyAnswers x else none
  committedLeaves answers keys toyTree.1 5 64 = toyWord.set! 0 (List.replicate 64 0)

-- The keys reversed and repeated: the same leaves.
#guard
  let keys := toyTree.2.map (·.1)
  committedLeaves toyAnswers (keys.reverse ++ keys) toyTree.1 5 64 = toyWord

end LeanVMTests.Extraction
