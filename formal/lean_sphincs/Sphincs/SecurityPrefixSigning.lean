import Sphincs.SecurityPrefixPublic

/-! The first successful encoding of a counter search (`firstEncoding`), which is what the honest
one-time signer computes, and the disclosed chain values reconstructed from a selected chain
frontier (`publicValues`). -/

open OracleComp OracleSpec

namespace Sphincs.Security.Prefix
open Concrete

attribute [local instance] Classical.propDecidable
attribute [local irreducible] encodingAttemptLimit Seeded.treePath Seeded.subNode Seeded.topNode chainWalk

/-- The actual least successful encoding search; its counter remains a 32-bit value. -/
noncomputable def firstEncoding (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (message : ForestKey) :
    Nat → Nat → Option (Counter × Encoding)
  | 0, _ => none
  | attempts + 1, counter =>
      match evalWithAnswerFn f (encode parameter lay tree leaf message (BitVec.ofNat counterBits counter) :
          OracleComp HashSpec (Option Encoding)) with
      | some word => some (BitVec.ofNat counterBits counter, word)
      | none => firstEncoding f parameter lay tree leaf message attempts (counter + 1)

theorem otsSignFrom_eq_firstEncoding (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (seed : MasterSeed) (message : ForestKey)
    (attempts start : Nat) :
    evalWithAnswerFn f (Seeded.otsSignFrom parameter lay tree leaf seed message attempts start :
      OracleComp HashSpec (Option (Counter × (ChainIndex → Digest)))) =
    (firstEncoding f parameter lay tree leaf message attempts start).map (fun pair =>
      (pair.1, fun chain => evalWithAnswerFn f (chainWalk parameter lay tree leaf chain 0
        (pair.2 chain).val (derivedSecrets f parameter seed (lay, tree, leaf, chain)) :
        OracleComp HashSpec Digest))) := by
  induction attempts generalizing start with
  | zero => rfl
  | succ attempts ih =>
      cases hencode : evalWithAnswerFn f
          (encode parameter lay tree leaf message (BitVec.ofNat counterBits start) :
            OracleComp HashSpec (Option Encoding)) with
      | none =>
          simp only [Seeded.otsSignFrom, evalWithAnswerFn_bind, firstEncoding, hencode]
          exact ih (start + 1)
      | some word =>
          simp only [Seeded.otsSignFrom, evalWithAnswerFn_bind, firstEncoding, hencode,
            Completeness.eval_sequenceFin, Completeness.eval_otsSecrets, Completeness.otsSecret,
            evalWithAnswerFn_pure, Option.map_some, derivedSecrets]

noncomputable def publicValues (segment : Segment) (outside : QueryImpl HashSpec Id)
    (secrets : Secrets) (frontier : Digest) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (word : Encoding) : ChainIndex → Digest := fun chain =>
  if (lay, tree, leaf, chain) = address segment then
    evalWithAnswerFn outside (chainWalk segment.parameter lay tree leaf chain segment.digit.val
      ((word chain).val - segment.digit.val) frontier : OracleComp HashSpec Digest)
  else
    evalWithAnswerFn outside (chainWalk segment.parameter lay tree leaf chain 0 (word chain).val
      (secrets (lay, tree, leaf, chain)) : OracleComp HashSpec Digest)

end Sphincs.Security.Prefix
