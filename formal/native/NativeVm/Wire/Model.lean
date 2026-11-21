module

public import NativeVm.Input
public import Native.Keccak.Lanes
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# The wire decoder's model

`decodeM B` decodes the wire bytes `B` as the code does (`NativeVm.Wire.Code`): the reader a byte
position into `B` (`rdU32`, `rdWords`, `rdDigest`), the distinct positions an insertion sort
(`sortD`), and each level's carried siblings read while the level climbs (`sibsM`, `climbM`), as
the Rust reads them, rather than all levels' first. `NativeVm.Wire.ModelSpec` proves it
`Proof.fromBytes` over Keccak-f[1600].
-/

@[expose] public section

namespace NativeVm.Wire

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.KeccakHash


/-! ## Reading -/

theorem ite_no {α : Type} {c : Prop} [Decidable c] (h : ¬c) {a b : α} :
    (if c then a else b) = b := by simp [h]

theorem ite_yes {α : Type} {c : Prop} [Decidable c] (h : c) {a b : α} :
    (if c then a else b) = a := by simp [h]


/-- The little-endian number of the `n` bytes of `B` from `p`. -/
def leNat (B : List UInt8) (p n : Nat) : Nat := ∑ k ∈ Finset.range n, (B.getD (p + k) 0).toNat * 256 ^ k

/-- The little-endian word of the `n ≤ 8` bytes of `B` from `p`. -/
def leAt (B : List UInt8) (p n : Nat) : UInt64 := (leNat B p n).toUInt64

/-- A little-endian 32-bit word at `c`. -/
def rdU32 (B : List UInt8) (c : Nat) : Option (Nat × Nat) :=
  if c + 4 ≤ B.length then some (leNat B c 4, c + 4) else none

/-- `n` little-endian 32-bit words from `c`. -/
def rdU32s (B : List UInt8) : Nat → Nat → Option (List Nat × Nat)
  | 0, c => some ([], c)
  | n + 1, c => do
    let (v, c) ← rdU32 B c
    let (vs, c) ← rdU32s B n c
    some (v :: vs, c)

/-- `n` words of `K` from `c`. -/
def rdWords (B : List UInt8) (n c : Nat) : Option (List K × Nat) :=
  if c + 8 * n ≤ B.length then
    some ((List.range n).map fun i ↦ K.ofLane (leAt B (c + 8 * i) 8), c + 8 * n)
  else none

/-- A digest at `c`. -/
def rdDigest (B : List UInt8) (c : Nat) : Option (Digest × Nat) :=
  if c + 32 ≤ B.length then
    some (#v[leAt B c 8, leAt B (c + 8) 8, leAt B (c + 16) 8, leAt B (c + 24) 8], c + 32)
  else none

/-- `n` rows of `w` words from `c`. -/
def rdRows (B : List UInt8) (w : Nat) : Nat → Nat → Option (List (List K) × Nat)
  | 0, c => some ([], c)
  | n + 1, c => do
    let (r, c) ← rdWords B w c
    let (rs, c) ← rdRows B w n c
    some (r :: rs, c)

/-! ## The distinct positions -/

/-- Add `x` to the ascending list `l`, unless it is there. -/
def insD : List Nat → Nat → List Nat
  | [], x => [x]
  | a :: l, x => if x < a then x :: a :: l else if x = a then a :: l else a :: insD l x

/-- The distinct positions, ascending, by insertion. -/
def sortD (qs : List Nat) : List Nat := qs.foldl insD []

/-! ## The climb -/

/-- Each node's sibling, the nodes `nodes` of the level: the level's node beside it (`true`), or
else the next carried sibling, read at `c` (`false`). -/
def sibsM (B : List UInt8) (nodes : List (Nat × Digest)) :
    List (Nat × Digest) → Nat → Option (List (Nat × Digest × Bool) × Nat)
  | [], c => some ([], c)
  | (v, _) :: rest, c => match nodes.lookup (v ^^^ 1) with
    | some d => do
      let (r, c) ← sibsM B nodes rest c
      some ((v, d, true) :: r, c)
    | none => do
      let (d, c) ← rdDigest B c
      let (r, c) ← sibsM B nodes rest c
      some ((v, d, false) :: r, c)

/-- The parent of a node with its digest, given its sibling: hashed when it is a first child (even,
or without its sibling among the level's nodes), the left child's digest first. -/
def parentOf (nd : Nat × Digest) (sb : Nat × Digest × Bool) : List (Nat × Digest) :=
  if nd.1 % 2 = 0 ∨ sb.2.2 = false then
    [(nd.1 >>> 1, keccak256 (if nd.1 % 2 = 0 then digestBytes nd.2 ++ digestBytes sb.2.1
      else digestBytes sb.2.1 ++ digestBytes nd.2))]
  else []

/-- The parents of a level's nodes, in order. -/
def parentsOf (nodes : List (Nat × Digest)) (sibs : List (Nat × Digest × Bool)) :
    List (Nat × Digest) :=
  (nodes.zip sibs).flatMap fun p ↦ parentOf p.1 p.2

/-- The climb of `h` levels from `nodes`: each level's nodes with their siblings. -/
def climbM (B : List UInt8) : Nat → List (Nat × Digest) → Nat →
    Option (List (List (Nat × Digest)) × Nat)
  | 0, _, c => some ([], c)
  | h + 1, nodes, c => do
    let (sibs, c) ← sibsM B nodes nodes c
    let (rest, c) ← climbM B h (parentsOf nodes sibs) c
    some (sibs.map (fun s ↦ (s.1, s.2.1)) :: rest, c)

/-! ## The proof -/

/-- What a phase decodes to: its height, its leaf width and its openings. -/
structure PhaseOut where
  height : Nat
  leafWords : Nat
  openings : List Opening

/-- A phase at `c`. -/
def phaseM (B : List UInt8) (c : Nat) : Option (PhaseOut × Nat) := do
  let (count, c) ← rdU32 B c
  if wireMaxQueries < count then none
  let (queries, c) ← rdU32s B count c
  let (height, c) ← rdU32 B c
  let (leafWords, c) ← rdU32 B c
  let (rowWords, c) ← rdU32 B c
  let positions := sortD queries
  if ¬(height ≤ wireMaxHeight ∧ leafWords ≤ wireMaxLeafWords ∧ rowWords ≤ leafWords ∧
    positions ≠ [] ∧ positions.getLastD 0 < 2 ^ height) then none
  let (rows, c) ← rdRows B rowWords positions.length c
  if 0 < rowWords ∧ ∀ r ∈ rows, r.getD 0 0 = 0 then none
  let leaves := rows.map fun r ↦ paddedLeaf r leafWords
  let nodes := positions.zip (leaves.map fun leaf ↦ keccak256 (leaf.flatMap K.toBytes))
  let (sibs, c) ← climbM B height nodes c
  some (⟨height, leafWords, queries.map fun q ↦
    ⟨q, ((positions.zip leaves).lookup q).getD [],
      (List.range height).map fun level ↦ ((sibs.getD level []).lookup (q >>> level)).getD default⟩⟩,
    c)

/-- `n` phases from `c`. -/
def phasesM (B : List UInt8) : Nat → Nat → Option (List PhaseOut × Nat)
  | 0, c => some ([], c)
  | n + 1, c => do
    let (p, c) ← phaseM B c
    let (ps, c) ← phasesM B n c
    some (p :: ps, c)

/-- The stream at `c`. -/
def streamM (B : List UInt8) (c : Nat) : Option (List E × Nat) := do
  let (n, c) ← rdU32 B c
  let (ws, c) ← rdWords B (2 * n) c
  some ((List.range n).map fun i ↦ E.ofLimbs (ws.getD (2 * i) 0) (ws.getD (2 * i + 1) 0), c)

/-- **The model**: the stream, the phase count, the phases, no byte left. -/
def decodeM (B : List UInt8) : Option (List E × List PhaseOut) := do
  let (stream, c) ← streamM B 0
  let (p, c) ← rdU32 B c
  if wireMaxPhases < p then none
  let (phases, c) ← phasesM B p c
  if c ≠ B.length then none
  some (stream, phases)

/-- The proof the model decodes. -/
def toProof (d : List E × List PhaseOut) : Proof := ⟨d.1, d.2.map PhaseOut.openings⟩

end NativeVm.Wire
