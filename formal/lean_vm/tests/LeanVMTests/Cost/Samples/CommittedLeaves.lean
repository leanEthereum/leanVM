module

public import LeanVM.Cost.FastLib
import all LeanVM.Protocol.Extraction.Fast.Lookup
import all LeanVM.Protocol.Extraction.Fast.SortedMap
import all LeanVM.Protocol.Extraction.Extractor

/-!
# Tests: a sample, the committed leaves, compiled

The leaves of the committed tree under a root, read through the preimage index
(`subtreeLeavesWith (preimageIn idx)`, `Fast/Lookup.lean`, the fast extractor's form of the
extractor's `committedLeaves`): the recursion over the tree's height, the lookups in the sorted
map (`SortedMap.get?`, the binary search `searchIn`), and the byte strings read as words
(`bytesWords`, `splitNode`). One `cost_compile` line, a measure for the binary search, and one
rewrite (`bytesDigest` through an array); the rest the compiler finds.
-/

namespace LeanVMTests.Cost.Samples

open LeanVM.Cost LeanVM.Parameters LeanVM.Extraction LeanVM.Extraction.Fast
open LeanVM.Protocol.Compile LeanVM.Protocol.KeccakHash LeanVM.Semantics LeanVM.Cost.FastLib

public section

attribute [local instance] lexOrd

theorem length_bytesLanes : ∀ (L : ℕ) (b : Bytes), (bytesLanes L b).length = L
  | 0, _ => rfl
  | L + 1, b => by simp [bytesLanes, length_bytesLanes L]

/-- A digest of 32 bytes, through the array of its four words. -/
theorem bytesDigest_eq (b : Bytes) :
    bytesDigest b = Vector.mk (bytesLanes 4 b).toArray (by simp [length_bytesLanes]) := by
  ext i hi
  simp [bytesDigest, List.getD_eq_getElem?_getD, length_bytesLanes]

cost_rewrite bytesDigest_eq

cost_compile searchInKeys measure fun _ _ lo hi ↦ hi - lo :=
  @searchIn (List UInt64 × ℕ) Hits lexOrd

/-- The committed leaves under `root`, read through the preimage index `idx`. -/
def committedLeavesFast (idx : SortedMap (List UInt64 × ℕ) Hits) (w h : ℕ) (root : LeanVM.Protocol.Digest) :
    Array (List K) :=
  subtreeLeavesWith (preimageIn idx) w h root

cost_compile committedLeavesC := committedLeavesFast

end

end LeanVMTests.Cost.Samples
