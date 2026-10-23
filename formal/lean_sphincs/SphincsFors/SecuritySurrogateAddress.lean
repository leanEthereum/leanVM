import SphincsFors.SecurityTreeWitness

/-! The exact off-spine address of each surrogate: the spine index and the boundary index at each
level. A boundary node is never a kept node, so a surrogate target at this address cannot overlap
a prepared canonical node. -/

open OracleComp OracleSpec

namespace SphincsFors.Security
open Concrete
attribute [local irreducible] Seeded.treeNode Seeded.treeRoot Seeded.spineNode
set_option maxHeartbeats 600000

theorem xor_one_ne (index : Nat) : Nat.xor index 1 ≠ index := by
  intro heq
  change index ^^^ 1 = index at heq
  by_cases heven : index % 2 = 0
  · rw [Nat.xor_one_of_even (Nat.even_iff.mpr heven)] at heq
    omega
  · have hodd : index % 2 = 1 := by omega
    rw [Nat.xor_one_of_odd (Nat.odd_iff.mpr hodd)] at heq
    omega

variable [Params]

def spineIndex (parameter : PublicParameter) (level : Nat) : Nat :=
  subtreePosition parameter / 2 ^ (level - subtreeHeight)

def boundaryIndex (parameter : PublicParameter) (level : Nat) : Nat :=
  Nat.xor (spineIndex parameter level) 1

/-- Retained-subtree nodes below its root and the unique spine nodes above it. -/
def KeptNode (parameter : PublicParameter) (level index : Nat) : Prop :=
  if level ≤ subtreeHeight then index / 2 ^ (subtreeHeight - level) = subtreePosition parameter
  else index = spineIndex parameter level

theorem boundary_not_kept (parameter : PublicParameter) (level : Nat)
    (hlevel : subtreeHeight ≤ level) : ¬KeptNode parameter level (boundaryIndex parameter level) := by
  unfold KeptNode
  by_cases heq : level = subtreeHeight
  · subst level
    simp only [le_refl, ↓reduceIte, Nat.sub_self, pow_zero, Nat.div_one,
      boundaryIndex, spineIndex]
    exact xor_one_ne _
  · rw [ite_eq_right (by omega : ¬level ≤ subtreeHeight)]
    exact xor_one_ne _

end SphincsFors.Security
