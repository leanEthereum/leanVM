import SphincsFors.SecurityPrefixMaterialCost

/-! The exact hash cost of key generation, `226 · 2^b + 2 (26 - b)` calls (per leaf: 32 hashes of the seed,
192 chain steps and the leaf hash), including the surrogate
spine. -/

open OracleComp OracleSpec

namespace SphincsFors.Security.Prefix
open Concrete Completeness SeedModel PreparedScheme

attribute [local irreducible] Seeded.treeNode Seeded.spineNode Seeded.treeRoot
  programCache preparedOracle
set_option backward.isDefEq.respectTransparency false

variable [Params]

theorem hashCalls_spineNode (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (seed : MasterSeed) (steps : Nat)
    (hsteps : steps ≤ totalHeight - subtreeHeight) :
    hashCalls f (Seeded.spineNode parameter lay tree seed steps : OracleComp HashSpec Digest) =
      (226 * 2 ^ subtreeHeight - 1) + 2 * steps := by
  induction steps with
  | zero => simp only [Seeded.spineNode, hashCalls_treeNode, Nat.mul_zero, Nat.add_zero]
  | succ steps ih =>
      have hlevel : subtreeHeight + steps < totalHeight := by omega
      rw [Seeded.spineNode, hashCalls_bind, ih (by omega), hashCalls_bind]
      simp only [Seeded.surrogate, dite_eq_left hlevel, hashCalls_deriveKey]
      split <;> rw [hashCalls_tweakableHash] <;> omega

theorem hashCalls_keygenFromSeed (f : QueryImpl HashSpec Id) (seed : MasterSeed) :
    hashCalls f (Seeded.keygenFromSeed seed) =
      226 * 2 ^ subtreeHeight + 2 * (totalHeight - subtreeHeight) := by
  simp only [Seeded.keygenFromSeed, hashCalls_bind, hashCalls_deriveKey, Seeded.treeRoot,
    hashCalls_spineNode f _ _ _ seed _ (le_refl _), hashCalls_pure, Nat.add_zero]
  have := Nat.two_pow_pos subtreeHeight
  omega

end SphincsFors.Security.Prefix
