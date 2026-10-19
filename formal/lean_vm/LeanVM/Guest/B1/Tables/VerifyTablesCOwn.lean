/-
  LeanVM.Guest.B1.Tables.VerifyTablesCOwn

  `verify_tables`' 205 `HeapBuf`s, their sizes and their honest words.
-/

module

public import LeanVM.Guest.B1.Tables.VerifyTablesCIface

/-!
# The honest buffers

In allocation order (`vtSizes`, `vtOwnW`): `sort_order`, `block_side_tab`, `block_off_g`,
`idxc_tab`, `block_index_mle`; per selector its `offset_bits`, `eq_chain`, `goff_chain`, the two
index chains after selectors `1` and `2`; the table sumcheck's rounds, challenges' products and
equality prefix.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- A selector's three buffers' sizes. -/
def selSz : List ℕ := [34, 42, 42]

/-- The 205 buffers' sizes, the table sumcheck's `n` rounds. -/
def vtSizes (n : ℕ) : List ℕ :=
  [102, 102, 102, 34, 102] ++ selSz ++ selSz ++ [42] ++ selSz ++ [42] ++
    (List.range 62).flatMap (fun _ => selSz) ++ [4 * (n + 1), n + 1, n + 1]

/-- The push side's order and offsets, the count side's, over the blocks' log-heights `ks`. -/
def pushOrd (ks : ℕ → ℕ) : List ℕ := stackOrder ((List.range 37).map ks)
def countOrd (ks : ℕ → ℕ) : List ℕ := stackOrder ((List.range 28).map fun i => ks (74 + i))
def pushOff (ks : ℕ → ℕ) : List ℕ := (stackOffsets ((List.range 37).map ks)).1
def countOff (ks : ℕ → ℕ) : List ℕ := (stackOffsets ((List.range 28).map fun i => ks (74 + i))).1

/-- Selector `i`'s block's offset. -/
def selOff (ks : ℕ → ℕ) (i : ℕ) : ℕ :=
  if i < 37 then (pushOff ks).getD i 0 else (countOff ks).getD (i - 37) 0

/-- `sort_order`. -/
def sortW (ks : ℕ → ℕ) : List E :=
  (List.range 102).map fun r => if r < 37 then gen ^ (pushOrd ks).getD r 0
    else if 74 ≤ r then gen ^ (74 + (countOrd ks).getD (r - 74) 0) else 0

/-- `block_side_tab`. -/
def sideW : List E := (List.range 102).map fun b => word (vtBlockSide b) 0 0

/-- `block_off_g`. -/
def offW (ks : ℕ → ℕ) : List E :=
  (List.range 102).map fun b => if b < 37 then gen ^ (pushOff ks).getD b 0
    else if 74 ≤ b then gen ^ (countOff ks).getD (b - 74) 0 else 0

/-- `idxc_tab`. -/
def idxcW : List E := (List.range 34).map fun t => 1 + gen ^ 2 ^ t

/-- An index chain over the point's first `κ` coordinates, as a 42-word buffer. -/
def idxChainW (point : List E) (κ : ℕ) : List E :=
  (List.range 42).map fun t => if t ≤ κ then
    ∏ j ∈ Finset.range t, (1 + point.getD j 0 * (1 + gen ^ 2 ^ j)) else 0

/-- `block_index_mle`: the memory's and the bytecode's index values at blocks `1` and `2`. -/
def bimW (point : List E) (logMem : ℕ) : List E :=
  (List.range 102).map fun b => if b = 1 then (idxChainW point logMem).getD logMem 0
    else if b = 2 then (idxChainW point 18).getD 18 0 else 0

/-- Selector `i`'s three buffers: the offset's bits, the equality chain, the rebuilt offset. -/
def selW (ks : ℕ → ℕ) (point : List E) (i : ℕ) : List (List E) :=
  let k := ks (selBlk.getD i 0)
  let off := selOff ks i
  [(List.range 34).map fun j => bitE (off.testBit j),
    (List.range 42).map fun t => if t ≤ point.length - k then
      ∏ j ∈ Finset.range t, (1 + bitE (off.testBit (k + j)) + point.getD (k + j) 0) else 0,
    (List.range 42).map fun t => if t ≤ point.length - k then
      ∏ j ∈ Finset.range t, (1 + bitE (off.testBit (k + j)) * (gen ^ 2 ^ (k + j) + 1)) else 0]

/-- The 205 buffers' honest words. -/
def vtOwnW (ks : ℕ → ℕ) (point : List E) (logMem n : ℕ) (cvr : ℕ → Digest) (cur : E) (cl ch : ℕ → E)
    (chis : List E) : List (List E) :=
  [sortW ks, sideW, offW ks, idxcW, bimW point logMem] ++ selW ks point 0 ++ selW ks point 1 ++
    [idxChainW point logMem] ++ selW ks point 2 ++ [idxChainW point 18] ++
    (List.range 62).flatMap (fun i => selW ks point (i + 3)) ++
    [zcRoundsW cvr cur cl n, zcCprodW ch n, zcPeqW point chis n]

theorem vtOwnW_fit (ks : ℕ → ℕ) (point : List E) (logMem n : ℕ) (cvr : ℕ → Digest) (cur : E)
    (cl ch : ℕ → E) (chis : List E) :
    List.Forall₂ (fun c s => c.length ≤ s) (vtOwnW ks point logMem n cvr cur cl ch chis) (vtSizes n) := by
  have hsel : ∀ i, List.Forall₂ (fun c s => c.length ≤ s) (selW ks point i) selSz := fun i => by
    simp [selW, selSz]
  have hfm : List.Forall₂ (fun c s => c.length ≤ s) ((List.range 62).flatMap fun i => selW ks point (i + 3))
      ((List.range 62).flatMap fun _ => selSz) := by
    induction (List.range 62) with
    | nil => exact .nil
    | cons a l ih => simpa using List.rel_append (hsel (a + 3)) ih
  simp only [vtOwnW, vtSizes]
  refine List.rel_append (List.rel_append (List.rel_append (List.rel_append (List.rel_append
    (List.rel_append (List.rel_append ?_ (hsel 0)) (hsel 1)) ?_) (hsel 2)) ?_) hfm) ?_
  · simp [sortW, sideW, offW, idxcW, bimW]
  · simp [idxChainW]
  · simp [idxChainW]
  · simp only [zcRoundsW, zcCprodW, zcPeqW, List.length_map, List.length_range, List.forall₂_cons,
      le_refl, and_true, List.Forall₂.nil]
    rw [List.length_flatMap]
    simp [Nat.mul_comm]

end
end LeanVM.Guest.B1.VerifySub
