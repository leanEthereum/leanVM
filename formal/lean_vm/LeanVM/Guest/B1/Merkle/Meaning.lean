/-
  LeanVM.Guest.B1.Merkle.Meaning

  The interface of B1's Merkle functions: what `verify_merkle_cap` checks of the hinted cap, and
  the statement that its core IR checks it.
-/

module

public import LeanVM.Guest.B1.Common.Sponge

/-!
# Merkle caps: meanings (TRIAGE G #33, #34)

The guest (`lean_ethereum.py`, G below) opens a WHIR commitment in two
parts: each query climbs its leaf's hash up `depth - cap_depth` levels (`walk_path`, called by `opening_query`) to a node of the cap, a hinted top of the tree whose
node `k` (`1 ≤ k < 2^(cap_depth+1)`, node `1` the root, `2k`, `2k + 1` its children) sits at the
cap's cells `2k`, `2k + 1`; the query writes the node it reached there and flags the node's
parent. `verify_merkle_cap(cap, flags, depth)` then hashes every flagged node of
the cap, and the root always; an unflagged internal node pins its children's flags to zero, so
every flagged node's ancestors are hashed. Together they are `climb` to the root, the
root being what `openOne` compares (`B1/Merkle/Climb.lean`).

* `HashesPair l0 l1 r0 r1 p0 p1`: the four child cells are canonical and the parent's cells are
  the digest of their 64 bytes (`keccak(…)` of two two-cell digests, `keccak_one`), which for
  digests' cells is `hashPair` (`LeanVM/Protocol/KeccakHash.lean`).
* `MeaningVerifyMerkleCap D`: what `verify_merkle_cap__L{D}` checks, `2 ≤ D ≤ 8`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- A node's two cells hash its children's: the node's cells are the digest of their 64 bytes. -/
def HashesPair (l0 l1 r0 r1 p0 p1 : E) : Prop :=
  (p0, p1) = digestHalves (keccak256 (Keccak.cellsBytes [l0, l1, r0, r1]))

/-- **`verify_merkle_cap(cap, flags, D)`** (TRIAGE #34): the cap's cells `cell k`,
`2 ≤ k < 2^(D+2)` (node `k / 2`'s cell `k % 2`), are in memory; the flags `fl k` of the internal
nodes `2 ≤ k < 2^D` are in memory and in `K`; the root and every flagged internal node hash their
children; an unflagged internal node whose children are internal has their flags zero; the
function returns the root's cells. -/
def MeaningVerifyMerkleCap (D : ℕ) (rd : Reader) : List E → List E → Prop
  | [cap, flags], rets =>
      ∃ cell fl : ℕ → E, (∀ k, 2 ≤ k → k < 2 ^ (D + 2) → LoadHolds rd cap k (cell k)) ∧
        (∀ k, 2 ≤ k → k < 2 ^ D → LoadHolds rd flags k (fl k) ∧ IsInK (fl k)) ∧
        (∀ k, 1 ≤ k → k < 2 ^ D → (k = 1 ∨ fl k ≠ 0) →
          HashesPair (cell (4 * k)) (cell (4 * k + 1)) (cell (4 * k + 2)) (cell (4 * k + 3))
            (cell (2 * k)) (cell (2 * k + 1))) ∧
        (∀ k, 2 ≤ k → 2 * k < 2 ^ D → fl k = 0 →
          LoadHolds rd flags (2 * k) 0 ∧ LoadHolds rd flags (2 * k + 1) 0) ∧
        rets = [cell 2, cell 3]
  | _, _ => False

/-- The deployed specializations, cap depths `2 .. 8`, by name (a name built by `++ toString`
does not reduce in a `module`'s kernel). -/
def merkleCapNames : List (String × ℕ) :=
  [("verify_merkle_cap__L2", 2),
    ("verify_merkle_cap__L3", 3),
    ("verify_merkle_cap__L4", 4),
    ("verify_merkle_cap__L5", 5),
    ("verify_merkle_cap__L6", 6),
    ("verify_merkle_cap__L7", 7),
    ("verify_merkle_cap__L8", 8)]

/-- `verify_merkle_cap__L{D}`'s function in the program `P` is its meaning, `2 ≤ D ≤ 8`. -/
def verify_merkle_cap_SpecP (P : Program) : Prop :=
  ∀ p ∈ merkleCapNames, ∀ (rd : Reader) (args rets : List E),
    P.Rel rd p.1 args rets ↔ MeaningVerifyMerkleCap p.2 rd args rets

end
end LeanVM.Guest.B1
