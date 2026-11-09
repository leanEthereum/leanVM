import LeanVM.Protocol.Extraction.Defs

/-!
# Tests: the extractor's decoder and Merkle inversion on toy codes

Executable checks (`#guard`) of the knowledge extractor's pieces (`LeanVM/Protocol/Extraction/Extractor.lean`) on
toy shapes, `κ = μ − 6 ≤ 2` message variables (the deployed shapes, `κ ≥ 9`, are far too large for
the list decoder, as its cost table says, but not for the fast path). A toy stack of `2^μ` pseudo-random words is encoded on
the `n = 2^(κ+R)` columns of its `64` lanes, and some whole columns are replaced by random leaves:

* the list decoder (`decodeStacksAt`: Guruswami–Sudan on every lane, `toNovel`, pruning, `stackOf`)
  finds the stack when the errors are within the radius `n − A`, including past the unique
  decoding radius `⌊(n − 2^κ)/2⌋`, and finds nothing when they are not;
* the fast path (`fastStacks`) decodes a word without errors by interpolation alone, also at the
  smallest deployed shape (`μ = 15`, `R = 1`), and gives up on a word with an error among its first
  `2^κ` columns, which the list decoder still decodes;
* the parameters: the natural Johnson threshold and the decoder's multiplicities at the deployed
  shapes, against the table computed offline with exact integers;
* the Merkle inversion (`committedLeaves`): under an injective toy hash, the leaves are recovered
  from the answer table, an unanswered leaf is zeros, and the keys' order and repetitions do not
  matter.

The runs are interpreted, a few seconds each; the decoding past the unique radius takes about a
minute and a half, the fast path at the deployed shape about half a minute.
-/

namespace LeanVMTests.Extraction

open CompPoly LeanVM.Parameters LeanVM.Parameters.Whir LeanVM.Extraction
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile

/-! ## Toy words -/

/-- A linear congruential generator. -/
def lcg (s : ℕ) : ℕ := (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- `len` pseudo-random 64-bit numbers from a seed. -/
def randoms (seed len : ℕ) : Array ℕ := Id.run do
  let mut s := lcg (seed + 1)
  let mut out := #[]
  for _ in [0:len] do
    s := lcg s
    out := out.push s
  return out

/-- A pseudo-random stack of `2^μ` words. -/
def randomStack (seed μ : ℕ) : Vector K (2 ^ μ) :=
  let r := randoms seed (2 ^ μ)
  Vector.ofFn fun i ↦ K.ofBits (r.getD i.val 0)

/-- The word of a stack at rate `2^-R`: column `v` holds lane `u`'s encoding at word `63 − u`. -/
def wordOf {μ : ℕ} (R : ℕ) (q : Vector K (2 ^ μ)) : Array (List K) :=
  let κ := μ - initialFold
  let lanes := (List.range 64).map fun u ↦ novelFwd κ R (laneCoeffs q u)
  Array.ofFn fun v : Fin (2 ^ (κ + R)) ↦ (lanes.map fun e ↦ e.getD v.val 0).reverse

/-- The word with the columns `cols` replaced by random leaves. -/
def corrupt (seed : ℕ) (cols : List ℕ) (w : Array (List K)) : Array (List K) :=
  cols.foldl (fun w v ↦ w.set! v ((randoms (seed + 1000 + v) 64).toList.map K.ofBits)) w

/-- Whether the list decoder at agreement `A` lists the stack, and the list's length. -/
def decodes {μ : ℕ} (R A : ℕ) (q : Vector K (2 ^ μ)) (w : Array (List K)) : Bool × ℕ :=
  let l := decodeStacksAt μ R A fun v ↦ w.getD v []
  (l.any fun d ↦ d.toList == q.toList, l.length)

/-- Whether the fast path returns exactly the stack. -/
def fastDecodes {μ : ℕ} (R : ℕ) (q : Vector K (2 ^ μ)) (w : Array (List K)) : Bool :=
  (fastStacks μ R fun v ↦ w.getD v []).map Vector.toList == [q.toList]

/-! ## The list decoder -/

-- `κ = 1`, `R = 1`: `n = 4`, `A = 3`; one error.
#guard johnsonThreshold 7 1 = 3
#guard decodes 1 3 (randomStack 1 7) (corrupt 1 [2] (wordOf 1 (randomStack 1 7))) = (true, 1)

-- `κ = 1`, `R = 2`: `n = 8`, `A = 4`; four errors, past the unique decoding radius `3`, within
-- the radius `n − A = 4`.
#guard decodes 2 4 (randomStack 3 7) (corrupt 3 [1, 3, 5, 7] (wordOf 2 (randomStack 3 7))) = (true, 1)

-- Five errors: past the radius, nothing is decoded.
#guard decodes 2 4 (randomStack 3 7) (corrupt 3 [0, 1, 3, 5, 7] (wordOf 2 (randomStack 3 7))) =
  (false, 0)

/-! ## The fast path -/

-- `κ = 2`, `R = 2`: a word without errors.
#guard fastDecodes 2 (randomStack 2 8) (wordOf 2 (randomStack 2 8))

-- An error in column `0`, among the interpolated ones: the fast path finds nothing, the list
-- decoder (at `A = 9`, `9² > (2^2 − 1)·16`) the stack.
#guard (fastStacks 8 2 fun v ↦ (corrupt 2 [0] (wordOf 2 (randomStack 2 8))).getD v []).isEmpty
#guard decodes 2 9 (randomStack 2 8) (corrupt 2 [0] (wordOf 2 (randomStack 2 8))) = (true, 1)

-- An error past them: the fast path still finds the stack (it agrees on `15` of `16` columns).
#guard fastDecodes 2 (randomStack 2 8) (corrupt 2 [13] (wordOf 2 (randomStack 2 8)))

-- The smallest deployed shape, `μ = 15`, `R = 1`: a stack of `2^15` words on `1024` columns,
-- decoded by the fast path (about half a minute, interpreted, the word's encoding included).
#guard fastDecodes 1 (randomStack 5 15) (wordOf 1 (randomStack 5 15))

/-! ## The parameters at the deployed shapes

The Johnson threshold `A`, the multiplicity `m` and the `Y`-degree `ℓ = ⌊(m·A − 1)/(2^κ − 1)⌋` at
`R = 1`, `μ = 15, …, 28`, and the multiplicities at `R = 2` (computed offline with exact
integers). -/

#guard johnsonThreshold 15 1 = 725
#guard (List.range 14).map (fun i ↦ gsMultiplicity (15 + i) 1) =
  [65, 59, 78, 84, 87, 91, 92, 47, 47, 47, 47, 47, 32, 32]
#guard (List.range 14).map (fun i ↦
    let p := gsParams (15 + i) 1
    p.interp.weightedDegreeBound / (2 ^ (9 + i) - 1)) =
  [92, 83, 110, 119, 123, 128, 130, 66, 66, 66, 66, 66, 45, 45]
#guard (List.range 14).map (fun i ↦ gsMultiplicity (15 + i) 2) =
  [256, 37, 38, 39, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40]

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

/-- The toy word of `κ = 2`, `R = 2` with two errors, its tree of height `4`, and the table. -/
def toyWord : Array (List K) := corrupt 4 [3, 9] (wordOf 2 (randomStack 4 8))

def toyTree : Digest × List (Bytes × Digest) := merklize toyWord 4

def toyAnswers (x : Bytes) : Option Digest := (toyTree.2.find? (·.1 == x)).map (·.2)

-- The inversion recovers every leaf.
#guard committedLeaves toyAnswers (toyTree.2.map (·.1)) toyTree.1 4 64 = toyWord

-- Leaf `0` unanswered: zeros there, the other leaves unchanged.
#guard
  let keys := toyTree.2.map (·.1) |>.filter (· != (toyWord.getD 0 []).flatMap K.toBytes)
  let answers : Bytes → Option Digest := fun x ↦ if keys.contains x then toyAnswers x else none
  committedLeaves answers keys toyTree.1 4 64 = toyWord.set! 0 (List.replicate 64 0)

-- The keys reversed and repeated: the same leaves.
#guard
  let keys := toyTree.2.map (·.1)
  committedLeaves toyAnswers (keys.reverse ++ keys) toyTree.1 4 64 = toyWord

-- The decoder on the inverted word (`A = 9`, two errors).
#guard decodes 2 9 (randomStack 4 8)
  (Array.ofFn fun v : Fin 16 ↦ leafAt (committedLeaves toyAnswers (toyTree.2.map (·.1)) toyTree.1 4 64) 4 64 v) =
  (true, 1)

end LeanVMTests.Extraction
