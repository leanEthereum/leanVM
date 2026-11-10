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

/-- The log holds what the signer gives every logged message. -/
def HonestLog (d : Data) (s : Log) : Prop := ∀ e ∈ s.1, e.2 = signH (d none) (hOf d) e.1

theorem digestInput_length (d : Data) (m : Message) (R : Randomness) (call : DigestCall) :
    (messageDigestInput (param (hOf d)) (dataOf (hOf d)).root m R call).length ≤ maxLen := by
  rw [messageDigestInput_length]
  unfold maxLen
  omega

/-- A digest call input, in the finite domain. -/
def digestInputX (d : Data) (m : Message) (R : Randomness) (call : DigestCall) : Input :=
  ⟨_, digestInput_length d m R call⟩

/-- The digest a message and a randomizer get from `G`. -/
def digestG (d : Data) (G : Input → HashOutput) (m : Message) (R : Randomness) : MessageDigest :=
  truncateMessageDigest fun call ↦ G (digestInputX d m R call)

/-- The digest of a message at a randomizer not its own comes from `G`, and its FORS leaves are all
opened by logged digests. -/
def CoverE (d : Data) (s : Log) (G : Input → HashOutput) (m : Message) (R : Randomness) : Prop :=
  R ≠ rndOf (hOf d) m ∧
    Covered (revealedLeaves d s) (digestIndex (digestG d G m R), digestLeaves (digestG d G m R))

theorem digestInput_not_honest (d : Data) (m : Message) (R : Randomness) (hR : R ≠ rndOf (hOf d) m)
    (call : DigestCall) : ∀ k, inputD d k ≠ messageDigestInput (param (hOf d)) (dataOf (hOf d)).root m R call := by
  intro k hk
  have hlen := congrArg List.length hk
  rw [messageDigestInput_length] at hlen
  cases k with
  | pkSeed => simp only [inputD, length_input_pkSeed] at hlen; omega
  | prf => simp only [inputD, length_input_prf] at hlen; omega
  | ots => simp only [inputD, length_input_ots] at hlen; omega
  | fts => simp only [inputD, length_input_fts] at hlen; omega
  | rnd => simp only [inputD, length_input_rnd] at hlen; omega
  | enc => simp only [inputD, length_input_enc] at hlen; omega
  | pos p => simp only [inputD, length_input_pos] at hlen; omega
  | dig m' call' =>
    simp only [inputD, input] at hk
    obtain ⟨-, -, hm, hr, -⟩ := messageDigestInput_injective hk
    subst hm
    exact hR hr.symm

theorem fors_hidden_prot (d : Data) (s : Log) (G : Input → HashOutput) (index : Index) (κ : FTree)
    (leaf : FLeaf) (hleaf : leaf ∉ revealedLeaves d s index κ) :
    Prot d s (pt (hOf d) (d none) (.pos (.fleaf index κ leaf))) ∧
      (pt (hOf d) (d none) (.pos (.fleaf index κ leaf))).1 = tweakableHashInput (param (hOf d))
        (.forsLeaf index κ leaf) (bytesLE 16 (Completeness.forsSecretValue (fD d G) (param (hOf d))
          index κ (d none) leaf)) := by
  refine ⟨⟨.pos (.fleaf index κ leaf), fun hsub ↦ ?_, rfl⟩, ?_⟩
  · have hq : some (Key.fts index κ leaf) ∈ deps (.pos (.fleaf index κ leaf)) := by
      simp [deps, secretDep]
    exact hleaf (inv_of_mem_rev d s _ (hsub hq))
  · exact (canonical_eq_input d G (.fleaf index κ leaf)).symm.trans
      (fleaf_input (fD d G) _ (d none) _ index κ leaf)

/-- **The canonical branch**: a protected read, or a covered digest from `G`. -/
theorem canonical_out (d : Data) (s : Log) (G : Input → HashOutput) (message : Message)
    (signature : Signature) (hlog : HonestLog d s) (hfresh : ¬ s.Contains ⟨message, signature⟩)
    (counter : Layer → Counter)
    (hcount : ∀ lay, SignatureWitness.chosenCounter (fD d G) (param (hOf d)) (d none)
      (SignatureWitness.index (fD d G) (pkD d) message signature) lay = some (counter lay))
    (hcanon : SignatureWitness.CanonicalOpening (fD d G) (pkD d) (d none) message signature counter
      (SignatureWitness.chosenWord (fD d G) (param (hOf d)) (d none)
        (SignatureWitness.index (fD d G) (pkD d) message signature))) :
    (∃ l ∈ SignatureWitness.trace (fD d G) (pkD d) message signature, ∃ x : Input, x.1 = l ∧ Prot d s x) ∨
      CoverE d s G message signature.randomness := by
  by_cases hR : signature.randomness = rndOf (hOf d) message
  · by_cases hM : ∃ e ∈ s.1, e.1 = message
    · exfalso
      obtain ⟨e, he, rfl⟩ := hM
      apply hfresh
      refine ⟨e, he, rfl, ?_⟩
      rw [hlog e he, signH_eq]
      exact canonical_eq_signExpl d G e.1 signature hR counter hcount hcanon
    · left
      refine ⟨_, digestInputs_mem' (fD d G) (pkD d) message signature ⟨0, digestCalls_pos⟩,
        pt (hOf d) (d none) (.dig message ⟨0, digestCalls_pos⟩), ?_, ?_⟩
      · change messageDigestInput (param (hOf d)) (dataOf (hOf d)).root message (rndOf (hOf d) message) _ =
          messageDigestInput (param (hOf d)) (dataOf (hOf d)).root message signature.randomness _
        rw [hR]
      · refine ⟨.dig message ⟨0, digestCalls_pos⟩, fun hsub ↦ hM ?_, rfl⟩
        have hq : some (Key.rnd message) ∈ deps (.dig message ⟨0, digestCalls_pos⟩) := by simp [deps]
        exact inv_of_mem_rev d s _ (hsub hq)
  · have hnh := digestInput_not_honest d message signature.randomness hR
    have hdig : verificationDigest (fD d G) (pkD d) message signature =
        digestG d G message signature.randomness := by
      unfold verificationDigest digestG
      simp only [messageDigest, messageDigestCall, evalWithAnswerFn_bind, Completeness.eval_sequenceFin,
        Completeness.eval_oracleHash, evalWithAnswerFn_pure, QueryImpl.ofFn_apply]
      congr 1
      funext call
      exact (ans_of_not_honest d s G (digestInputX d message signature.randomness call) (hnh call)).1
    obtain ⟨-, -, hopen⟩ := hcanon
    have hrun := (SignatureWitness.verification_fors_run (fD d G) (pkD d) message signature).bind_left
    rcases Fors.Opening.covered_or_hidden (fD d G) (param (hOf d))
        (SignatureWitness.index (fD d G) (pkD d) message signature) (d none)
        (digestLeaves (verificationDigest (fD d G) (pkD d) message signature)) signature.fors
        (revealedLeaves d s) _ hopen hrun with hcov | ⟨index', κ, leaf, hleaf, hmem⟩
    · right
      refine ⟨hR, ?_⟩
      unfold SignatureWitness.index at hcov
      rw [hdig] at hcov
      exact hcov
    · left
      obtain ⟨hp, hx⟩ := fors_hidden_prot d s G index' κ leaf hleaf
      exact ⟨_, hmem, _, hx, hp⟩

end Qrom.Sphincs
