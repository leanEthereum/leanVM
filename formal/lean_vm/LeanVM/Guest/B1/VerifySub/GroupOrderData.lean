/-
  LeanVM.Guest.B1.VerifySub.GroupOrderData

  The groups `Hints` numbers the committed columns and each side's bus blocks by, against the guest's group starts (kernel evaluation).
-/

module

public import LeanVM.Guest.Hints
public import LeanVM.Guest.B1.Placement.Certify
public import LeanVM.Guest.B1.Tables.InterfaceP

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Protocol.Verifier LeanVM.Guest.B1.Tables

@[expose] public section

/-- The committed columns' groups `colGroupOrder` numbers. -/
def colGroupsH : List ℕ := Hints.runGroups 0 none ((committedCols 158).map Hints.colKey)

theorem cpC0_lt : ∀ j < 9, cpC0 j < cpC0 (j + 1) := by decide +kernel

theorem colGroupsH_eq : ∀ j < 9, ∀ x < 94, cpC0 j ≤ x → x < cpC0 (j + 1) → colGroupsH.getD x 0 = j := by
  decide +kernel

/-- A side's block keys, the framework's three first (push and pull). -/
def keysP : List ℕ :=
  [0, 1, 2] ++ List.replicate 5 3 ++ List.replicate 5 4 ++ List.replicate 3 5 ++ List.replicate 5 6 ++
    List.replicate 5 7 ++ List.replicate 28 8

/-- The count side's block keys. -/
def keysC : List ℕ :=
  List.replicate 4 3 ++ List.replicate 4 4 ++ List.replicate 2 5 ++ List.replicate 4 6 ++ List.replicate 4 7 ++
    List.replicate 27 8

/-- Block group `j`'s first block. -/
def bgs (j : ℕ) : ℕ := blockGroupStart.getD j 0

/-- The count side's group `j`'s first block, in the side. -/
def bgsC (j : ℕ) : ℕ := bgs (18 + j) - 108

theorem bgs_lt : ∀ j < 9, bgs j < bgs (j + 1) := by decide +kernel

theorem bgsC_lt : ∀ j < 6, bgsC j < bgsC (j + 1) := by decide +kernel

theorem bgs_zero : bgs 0 = 0 := rfl
theorem bgs_nine : bgs 9 = 54 := rfl
theorem bgsC_zero : bgsC 0 = 0 := rfl
theorem bgsC_six : bgsC 6 = 45 := rfl

theorem runHeads_keysP : (Hints.runHeads (Hints.runGroups 0 none keysP)).length = 9 ∧
    (Hints.runHeads (Hints.runGroups 9 none keysP)).length = 9 := by decide +kernel

/-- **The push and pull sides' groups**: numbered from `0` and from `9`. -/
theorem groupsP_eq : ∀ j < 9, ∀ x < 54, bgs j ≤ x → x < bgs (j + 1) →
    (Hints.runGroups 0 none keysP).getD x 0 = 0 + j ∧ (Hints.runGroups 9 none keysP).getD x 0 = 9 + j := by
  decide +kernel

/-- The push side's groups share their sizes' sources. -/
theorem srcP_eq : ∀ j < 9, ∀ x < 54, bgs j ≤ x → x < bgs (j + 1) →
    blockKappaSrc.getD x 0 = blockKappaSrc.getD (bgs j) 0 ∧ blockKappaAdj x = blockKappaAdj (bgs j) := by
  decide +kernel

/-- **The count side's groups**, numbered from `18`. -/
theorem groupsC_eq : ∀ j < 6, ∀ x < 45, bgsC j ≤ x → x < bgsC (j + 1) →
    (Hints.runGroups 18 none keysC).getD x 0 = 18 + j := by
  decide +kernel

/-- The count side's groups share their sizes' sources. -/
theorem srcC_eq : ∀ j < 6, ∀ x < 45, bgsC j ≤ x → x < bgsC (j + 1) →
    blockKappaSrc.getD (108 + x) 0 = blockKappaSrc.getD (bgs (18 + j)) 0 ∧
      blockKappaAdj (108 + x) = blockKappaAdj (bgs (18 + j)) := by
  decide +kernel

end
end LeanVM.Guest.B1.VerifySub
