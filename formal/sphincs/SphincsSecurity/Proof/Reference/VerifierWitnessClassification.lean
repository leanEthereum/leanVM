import SphincsSecurity.Proof.Hypertree.ReferenceHypertreeWitness
import SphincsSecurity.Proof.Fts.FtsVerifierWitness
namespace SphincsSecurity.Concrete.OtsVerifierWitness

open _root_.OracleComp OracleSpec OtsContactTrace
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] chainWalk sequenceFin canonicalEncodingInputs canonicalGraphInputs instFintypePosition

theorem ReferenceLayerOpening.honest {f : QueryImpl HashSpec Id} {key : SecretKey} {words : OtsReferenceWords} {selections : ReferenceFamily}
    {index : Index} {signature : Signature} {lay : Layer} (h : ReferenceLayerOpening f key words selections index signature lay) :
    HonestLayerOpening f key.parameter key.otsSecret lay (treeIndexAt index lay) (leafIndexAt index lay)
      (evalWithAnswerFn f (layerMessage key index lay)) (signature.counter lay) (signature.chainValue lay) (signaturePath signature lay) := by
  obtain ⟨_, _, _, he, hv, hp⟩ := h
  exact ⟨words lay (treeIndexAt index lay) (leafIndexAt index lay), he, hv, hp⟩

theorem verify_classification (f : QueryImpl HashSpec Id) (key : SecretKey) (words : OtsReferenceWords)
    (messages : EncodingPosition → Digest) (selections : ReferenceFamily) (message : Message) (signature : Signature) (trace : Trace)
    (hvalid : ∀ lay tree leaf, TargetSum.Valid (words lay tree leaf))
    (hmessages : ∀ index lay, messages ⟨lay, treeIndexAt index lay, leafIndexAt index lay⟩ = evalWithAnswerFn f (layerMessage key index lay))
    (hroot : key.root = honestNode f key.parameter topLayer rootTree (key.otsSecret topLayer rootTree) (layerHeight topLayer) 0)
    (hverify : evalWithAnswerFn f (verify ⟨key.root, key.parameter⟩ message signature) = true)
    (hrun : ContainsRun f trace (verify ⟨key.root, key.parameter⟩ message signature)) :
    ∃ digest, evalWithAnswerFn f (messageDigest key.parameter key.root message signature.randomness) = digest ∧
      ContainsRun f trace (messageDigest key.parameter key.root message signature.randomness) ∧ Admissible digest ∧
      ((FullyHonestOpening f (recordedCache f trace) key (digestIndex digest) (digestLeaves digest) signature ∧
        (∀ lay, ReferenceLayerOpening f key words selections (digestIndex digest) signature lay) ∧
        ∀ tree, FtsVerifierWitness.TrueSecretQuery f key (digestIndex digest) tree (digestLeaves digest (ftsIndexOf tree)) trace) ∨
        LayerException f key words messages selections trace ∨ FtsVerifierWitness.Exception f key (digestIndex digest) trace) := by
  obtain ⟨digest, hd, hdrun, ha, hlayers, hftsrun, hlayersrun⟩ := verify_extract ⟨key.root, key.parameter⟩ message signature hverify hrun.cached
  refine ⟨digest, hd, (recordedCache_run_iff f trace _).mp hdrun, ha, ?_⟩
  rcases hypertree_classification f key words messages selections (digestIndex digest) (digestLeaves digest) signature trace
      (fun lay => hvalid lay _ _) (hmessages (digestIndex digest)) hroot hlayers ((recordedCache_run_iff f trace _).mp hlayersrun)
      with ⟨hfts, hopenings⟩ | he
  · rcases FtsVerifierWitness.recover_classification f key (digestIndex digest) (digestLeaves digest) signature.ftsSecret signature.ftsPath trace hfts
        ((recordedCache_run_iff f trace _).mp hftsrun) with ⟨hftsOpening, hqueries⟩ | he
    · refine Or.inl ⟨?_, fun lay => (hopenings lay).1, hqueries⟩
      exact ⟨fun lay => ⟨(hopenings lay).1.honest, (hopenings lay).2.1⟩, hftsOpening, hftsrun, fun lay => (hopenings lay).2.2⟩
    · exact Or.inr (Or.inr he)
  · exact Or.inr (Or.inl he)

end SphincsSecurity.Concrete.OtsVerifierWitness
