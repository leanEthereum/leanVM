import SphincsFors.SecurityPrefixSigning

/-! The single-layer signature reconstructed from the selected chain frontier (`publicLayer`), and
the cutoff condition under which it is the actual one: the selected leaf's first successful
encoding discloses at or above the frontier. -/

open OracleComp OracleSpec

namespace SphincsFors.Security.Prefix
open Concrete

attribute [local irreducible] encodingAttemptLimit Seeded.ftsNode Seeded.treePath chainWalk

variable [Params]

noncomputable def publicLayer (segment : Segment) (outside : QueryImpl HashSpec Id)
    (secrets : Secrets) (frontier : Digest) (surrogates : Nat → Digest)
    (index : Index) (lay : Layer) (message : FtsTops) : Option (LayerSignature lay) :=
  (firstEncoding outside segment.parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
      message encodingAttemptLimit 0).map fun pair =>
    ⟨pair.1,
      publicValues segment outside secrets frontier lay (treeIndexAt index lay) (leafIndexAt index lay) pair.2,
      publicPath segment outside secrets frontier surrogates lay (treeIndexAt index lay) (leafIndexAt index lay)⟩

/-- The single selected leaf's first successful encoding determines the permitted cutoff.
If that leaf has no successful encoding, the condition is vacuous. -/
def ReferenceCutoff (segment : Segment) (outside : QueryImpl HashSpec Id) (seed : MasterSeed) : Prop :=
  ∀ counter word,
    firstEncoding outside segment.parameter segment.lay segment.tree segment.leaf
      (evalWithAnswerFn outside (Seeded.ftsKey segment.parameter segment.leaf seed : OracleComp HashSpec FtsTops))
      encodingAttemptLimit 0 = some (counter, word) → segment.digit.val ≤ (word segment.chainIdx).val

end SphincsFors.Security.Prefix
