module

public import Qrom.Sphincs.Classify.Wots

@[expose] public section

/-!
# The canonical branch of the classification

A canonical opening at the honest randomizer of a message is the signature the signer gives it,
read from the data (`Qrom.Sphincs.canonical_eq_signExpl`).
-/

open OracleComp OracleSpec FORS FORS.Security FORS.Security.Graph FORS.Security.GraphCorrectness
  FORS.Security.GraphView Concrete

noncomputable section

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

namespace Qrom.Sphincs

variable [Params]

theorem digestInputs_mem' (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (call : DigestCall) :
    messageDigestInput pk.parameter pk.root message signature.randomness call ∈
      SignatureWitness.trace f pk message signature := by
  unfold SignatureWitness.trace
  rw [Concrete.verify]
  apply queriedInputs_mono_bind_left
  unfold messageDigest
  apply queriedInputs_mono_bind_left
  apply queriedInputs_sequenceFin_component f _ call
  unfold messageDigestCall
  simp only [oracleHash, HasQuery.query]
  rw [← bind_pure (liftM _), queriedInputs_query_bind]
  exact List.mem_cons_self

theorem verificationDigest_honest (d : Data) (G : Input → HashOutput) (message : Message)
    (signature : Signature) (hR : signature.randomness = rndOf (hOf d) message) :
    verificationDigest (fD d G) (pkD d) message signature = digestH (hOf d) message := by
  unfold verificationDigest
  rw [hR]
  exact digest_ovFun (hOf d) (d none) G message

/-- **A canonical opening at the honest randomizer is the signer's signature.** -/
theorem canonical_eq_signExpl (d : Data) (G : Input → HashOutput) (message : Message)
    (signature : Signature) (hR : signature.randomness = rndOf (hOf d) message)
    (counter : Layer → Counter)
    (hcount : ∀ lay, SignatureWitness.chosenCounter (fD d G) (param (hOf d)) (d none)
      (SignatureWitness.index (fD d G) (pkD d) message signature) lay = some (counter lay))
    (hcanon : SignatureWitness.CanonicalOpening (fD d G) (pkD d) (d none) message signature counter
      (SignatureWitness.chosenWord (fD d G) (param (hOf d)) (d none)
        (SignatureWitness.index (fD d G) (pkD d) message signature))) :
    signExpl (hOf d) message = some signature := by
  set f := fD d G
  have hcons := consistent_ovFun (d none) (hOf d) G
  have hdata := dataCorrect_ovFun (d none) (hOf d) G
  have htable := coordinates_correct f (param (hOf d)) (d none) (labelsOf (hOf d)) hcons
  rw [otsSecrets_ovFun, ftsSecrets_ovFun] at htable
  have hi : SignatureWitness.index f (pkD d) message signature = digestIndex (digestH (hOf d) message) := by
    unfold SignatureWitness.index
    rw [verificationDigest_honest d G message signature hR]
  have hl : digestLeaves (verificationDigest f (pkD d) message signature) =
      digestLeaves (digestH (hOf d) message) := by
    rw [verificationDigest_honest d G message signature hR]
  set i := digestIndex (digestH (hOf d) message)
  have henc : ∀ lay, encH (hOf d) lay (treeIndexAt i lay) (leafIndexAt i lay) encodingAttemptLimit 0 =
      some (counter lay, wordH (hOf d) lay (treeIndexAt i lay) (leafIndexAt i lay)) := by
    intro lay
    have hc := hcount lay
    rw [hi] at hc
    unfold SignatureWitness.chosenCounter at hc
    rw [selection_eq] at hc
    unfold wordH
    obtain ⟨cw, hcw, hfst⟩ := Option.map_eq_some_iff.mp hc
    rw [hcw]
    simp only [Option.map_some, Option.getD_some]
    rw [← hfst]
  have hall : Completeness.allSome (fun lay ↦ encH (hOf d) lay (treeIndexAt i lay) (leafIndexAt i lay)
      encodingAttemptLimit 0) = some fun lay ↦
        (counter lay, wordH (hOf d) lay (treeIndexAt i lay) (leafIndexAt i lay)) := by
    unfold Completeness.allSome
    have hv : ∀ lay, (encH (hOf d) lay (treeIndexAt i lay) (leafIndexAt i lay)
        encodingAttemptLimit 0).isSome := fun lay ↦ by simp only [henc lay, Option.isSome_some]
    rw [dite_eq_left hv]
    exact congrArg some (funext fun lay ↦ by simp only [henc lay, Option.get_some])
  unfold signExpl
  rw [hall, Option.map_some]
  refine congrArg some ?_
  obtain ⟨hland, hlayers, hfors⟩ := hcanon
  rw [hi] at hlayers hfors
  rw [hl] at hfors
  obtain ⟨σR, σF, σL⟩ := signature
  simp only at hR hlayers hfors
  simp only [Signature.mk.injEq]
  refine ⟨hR.symm, ?_, ?_⟩
  · funext κ
    obtain ⟨hs, hp⟩ := hfors κ
    change (σF κ).secret = _ at hs
    change (σF κ).path = _ at hp
    rcases hκ : σF κ with ⟨sec, pth⟩
    rw [hκ] at hs hp
    simp only at hs hp
    simp only [assembledFors, TreeOpening.mk.injEq]
    exact ⟨(htable.2 i κ _).1.trans hs.symm, (hdata.forsPath i κ _).trans hp.symm⟩
  · funext lay
    have hact : PrunedGraph.KeyActive (param (hOf d)) lay (treeIndexAt i lay) (leafIndexAt i lay) :=
      ⟨i, landed_full _ _, rfl, rfl⟩
    obtain ⟨hc, hv, hp⟩ := hlayers lay
    change (σL lay).counter = _ at hc
    change (σL lay).chainValues = _ at hv
    change (σL lay).path = _ at hp
    rcases hσ : σL lay with ⟨cl, vl, pl⟩
    rw [hσ] at hc hv hp
    simp only at hc hv hp
    simp only [layerSignatures, LayerSignature.mk.injEq]
    refine ⟨hc.symm, ?_, (hdata.treePath lay _ _ hact).trans hp.symm⟩
    rw [hv]
    funext c
    simp only [assembledValues]
    refine (htable.1 lay _ _ hact c _).trans ?_
    rw [chosenWord_eq d G i lay]
    rfl

end Qrom.Sphincs
