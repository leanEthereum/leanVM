import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Scheme.Replay
/-!
# Finite witnesses for the few-time leak

A leak chooses one successful signing entry for each of the fourteen opened trees.  Keeping the
range of that choice as a finset exposes the number of distinct signatures used by the opening.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec

abbrev SigningEntry := (request : Message) × SigningSpec.Range request
theorem indexGroup_eq_ftsIndexOf_or_last (tree : IndexGroup) :
    (∃ ftsTree : FtsTree, tree = ftsIndexOf ftsTree) ∨ tree = lastIndexGroup := by
  by_cases htree : tree.val < ftsTrees - 1
  · left
    let ftsTree : FtsTree := ⟨tree.val, htree⟩
    refine ⟨ftsTree, Fin.ext ?_⟩
    rfl
  · right
    apply Fin.ext
    change tree.val = 14
    change ¬ tree.val < 14 at htree
    have hlt := tree.isLt
    change tree.val < 15 at hlt
    omega

end SphincsSecurity.Concrete
