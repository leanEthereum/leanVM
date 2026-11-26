/-
  LeanVM.Guest.B1.Da.Tree

  The guest's trees of cell pairs as LeanDA's Merkle trees of digests, and the byte encodings
  the two share.
-/

module

public import LeanVM.Guest.B1.Da.LevelsSound
public import LeanDa.WithHash
public import LeanVM.Guest.WithHash

/-!
# The guest's trees as LeanDA's

LeanDA (Benedikt Wagner's framework, ported and instantiated in `lean_da`) roots a tree over the
leaves `f 0 … f (2^d - 1)` as `merkleRoot H d f`, its nodes `H (pairBytes l r)`; the guest keeps
a node as the two cells of its digest (`nodeCells`, `cellRoot`). With `H = Da.keccak256Bytes`:

* `mRoot d g`: the tree of `Digest`s over the leaves `g i`; `toBytes_mRoot`: as LeanDA's bytes it
  is `merkleRoot keccak d (toBytes ∘ g)`; `cellRoot_mRoot`: as cells it is the guest's `cellRoot`;
* `toList_toBytes`: LeanDA's digest bytes are this project's;
* `treeRoot_range`: a tree built level by level (`LeanDa.treeRootWithHash`) has the root
  `merkleRoot` (the statement of `lean_da`'s `treeRoot_map_range`, whose module this one cannot
  import).
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Main

@[expose] public section

/-! ## Bytes -/

theorem toList_toBytes (d : Digest) : (LeanVM.Protocol.Digest.toBytes d).toList = digestBytes d := by
  simp [LeanVM.Protocol.Digest.toBytes, Vector.toList]

/-! ## Trees of digests -/

/-- One level up a tree of digests. -/
def upD (g : ℕ → Digest) (i : ℕ) : Digest := keccak256 (digestBytes (g (2 * i)) ++ digestBytes (g (2 * i + 1)))

/-- The root of the tree of digests over the leaves `g 0 … g (2^d - 1)`. -/
def mRoot : ℕ → (ℕ → Digest) → Digest
  | 0, g => g 0
  | d + 1, g => mRoot d (upD g)

theorem toBytes_mRoot : ∀ (d : ℕ) (g : ℕ → Digest),
    LeanVM.Protocol.Digest.toBytes (mRoot d g) = LeanDa.merkleRootWithHash LeanVM.Da.keccak256Bytes d (LeanVM.Protocol.Digest.toBytes ∘ g)
  | 0, _ => rfl
  | d + 1, g => by
    rw [mRoot, toBytes_mRoot d, LeanDa.merkleRootWithHash]
    congr 1

theorem nodeCells_scalars (a b : Digest) :
    nodeCells (digestHalves a) (digestHalves b) =
      digestHalves (keccak256 (digestBytes a ++ digestBytes b)) := by
  rw [nodeCells, digestBytes_eq_cells, digestBytes_eq_cells]
  simp [cellsBytes]

theorem cellLevel_scalars (d : ℕ) (g : ℕ → Digest) :
    cellLevel ((List.range (2 ^ (d + 1))).map fun i => digestHalves (g i)) =
      (List.range (2 ^ d)).map fun i => digestHalves (upD g i) := by
  have hlen : 2 ^ (d + 1) / 2 = 2 ^ d := by rw [pow_succ, Nat.mul_div_cancel _ (by norm_num)]
  rw [cellLevel, List.length_map, List.length_range, hlen]
  refine List.map_congr_left fun i hi => ?_
  rw [List.mem_range] at hi
  have h1 : 2 * i < 2 ^ (d + 1) := by rw [pow_succ]; omega
  have h2 : 2 * i + 1 < 2 ^ (d + 1) := by rw [pow_succ]; omega
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h1,
    List.getElem?_range h2, Option.map_some, Option.getD_some, upD, nodeCells_scalars]

/-- **The guest's root of cell pairs is the root of the digests.** -/
theorem cellRoot_mRoot : ∀ (d : ℕ) (g : ℕ → Digest),
    cellRoot d ((List.range (2 ^ d)).map fun i => digestHalves (g i)) = digestHalves (mRoot d g)
  | 0, _ => rfl
  | d + 1, g => by
    rw [cellRoot, cellLevel_scalars, cellRoot_mRoot d, mRoot]

/-! ## Trees built level by level -/

theorem treeLevel_range (H : List UInt8 → Common.DigestBytes) (d : ℕ) (f : ℕ → Common.DigestBytes) :
    LeanDa.treeLevelWithHash H ((List.range (2 ^ (d + 1))).map f) = (List.range (2 ^ d)).map (LeanDa.upWithHash H f) := by
  have hlen : 2 ^ (d + 1) / 2 = 2 ^ d := by rw [pow_succ, Nat.mul_div_cancel _ (by norm_num)]
  rw [LeanDa.treeLevelWithHash, List.length_map, List.length_range, hlen]
  refine List.map_congr_left fun i hi ↦ ?_
  rw [List.mem_range] at hi
  have h1 : 2 * i < 2 ^ (d + 1) := by rw [pow_succ]; omega
  have h2 : 2 * i + 1 < 2 ^ (d + 1) := by rw [pow_succ]; omega
  simp only [LeanDa.upWithHash, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h1,
    List.getElem?_range h2, Option.map_some, Option.getD_some]

/-- **A tree built level by level has LeanDA's root.** -/
theorem treeRoot_range (H : List UInt8 → Common.DigestBytes) (d : ℕ) (f : ℕ → Common.DigestBytes) :
    LeanDa.treeRootWithHash H ((List.range (2 ^ d)).map f) = LeanDa.merkleRootWithHash H d f := by
  induction d generalizing f with
  | zero => rw [LeanDa.treeRootWithHash]; simp [LeanDa.merkleRootWithHash]
  | succ d ih =>
    have hlen : ¬((List.range (2 ^ (d + 1))).map f).length ≤ 1 := by
      rw [List.length_map, List.length_range, pow_succ]
      have := Nat.one_le_two_pow (n := d)
      omega
    rw [LeanDa.treeRootWithHash]
    simp only [hlen, ↓reduceIte]
    rw [treeLevel_range, ih]
    rfl

end
end LeanVM.Guest.B1.Da
