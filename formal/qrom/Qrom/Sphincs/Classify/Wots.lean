module

public import Qrom.Sphincs.Classify.Hits

@[expose] public section

/-!
# The WOTS branches of the classification

On the hash that answers the honest inputs from the data, the reference word of a key on a path is
its word read from the data (`Qrom.Sphincs.chosenWord_eq`), and a chain coordinate a logged signature
opens sits at that word's digit (`Qrom.Sphincs.mem_chainKeys_ots`,
`Qrom.Sphincs.mem_chainKeys_chain`).
-/

open OracleComp OracleSpec FORS FORS.Security FORS.Security.Graph FORS.Security.GraphCorrectness
  FORS.Security.GraphView Concrete

noncomputable section

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

namespace Qrom.Sphincs

variable [Params]

theorem canonicalMessage_eq_data (d : Data) (G : Input → HashOutput) (i : Index) (lay : Layer) :
    SignatureWitness.canonicalMessage (QueryImpl.ofFn (ovFun (d none) (hOf d) G)) (param (hOf d))
      (d none) i lay = (dataOf (hOf d)).keyMessage lay (treeIndexAt i lay) (leafIndexAt i lay) :=
  ((dataCorrect_ovFun (d none) (hOf d) G).keyMessage lay _ _ ⟨i, landed_full _ _, rfl, rfl⟩).symm

theorem selection_eq (d : Data) (G : Input → HashOutput) (i : Index) (lay : Layer) :
    ReferenceChoice.selection (QueryImpl.ofFn (ovFun (d none) (hOf d) G)) (param (hOf d)) lay
      (treeIndexAt i lay) (leafIndexAt i lay) (SignatureWitness.canonicalMessage
        (QueryImpl.ofFn (ovFun (d none) (hOf d) G)) (param (hOf d)) (d none) i lay) =
      encH (hOf d) lay (treeIndexAt i lay) (leafIndexAt i lay) encodingAttemptLimit 0 := by
  rw [canonicalMessage_eq_data]
  exact firstEncoding_ovFun (hOf d) (d none) G lay _ _ _ _

theorem chosenWord_eq (d : Data) (G : Input → HashOutput) (i : Index) (lay : Layer) :
    SignatureWitness.chosenWord (QueryImpl.ofFn (ovFun (d none) (hOf d) G)) (param (hOf d)) (d none)
      i lay = wordH (hOf d) lay (treeIndexAt i lay) (leafIndexAt i lay) := by
  unfold SignatureWitness.chosenWord ReferenceChoice.word wordH
  rw [selection_eq]

theorem mem_chainKeys {h : Key → HashOutput} {m : Message} {q : Option Key}
    (hm : q ∈ chainKeys h m) : ∃ lay tree leaf c,
      q = chainKey lay tree leaf c (wordH h lay tree leaf c) := by
  unfold chainKeys at hm
  split at hm
  · simp at hm
  · rename_i found hfound
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hm
    obtain ⟨⟨lay, c⟩, hq⟩ := hm
    have hs := Completeness.allSome_spec hfound lay
    refine ⟨lay, treeIndexAt (digestIndex (digestH h m)) lay,
      leafIndexAt (digestIndex (digestH h m)) lay, c, ?_⟩
    rw [← hq]
    unfold wordH
    simp only [hs, Option.map_some, Option.getD_some]

theorem mem_chainKeys_ots {h : Key → HashOutput} {m : Message} {lay : Layer} {tree : TreeIndex}
    {leaf : LeafIndex} {c : ChainIndex} (hm : some (.ots lay tree leaf c) ∈ chainKeys h m) :
    (wordH h lay tree leaf c).val = 0 := by
  obtain ⟨lay', tree', leaf', c', hq⟩ := mem_chainKeys hm
  unfold chainKey at hq
  split_ifs at hq with hz
  · simp only [Option.some.injEq, Key.ots.injEq] at hq
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hq
    exact hz
  · simp at hq

theorem mem_chainKeys_chain {h : Key → HashOutput} {m : Message} {lay : Layer} {tree : TreeIndex}
    {leaf : LeafIndex} {c : ChainIndex} {j : ChainStep}
    (hm : some (.pos (.chain lay tree leaf c j)) ∈ chainKeys h m) :
    (wordH h lay tree leaf c).val = j.val + 1 := by
  obtain ⟨lay', tree', leaf', c', hq⟩ := mem_chainKeys hm
  unfold chainKey at hq
  split_ifs at hq with hz
  · simp at hq
  · simp only [Option.some.injEq, Key.pos.injEq, Position.chain.injEq] at hq
    obtain ⟨rfl, rfl, rfl, rfl, hj⟩ := hq
    rw [hj]
    simp only
    omega

/-- A chain input below the digit the key's word opens is protected. -/
theorem chain_below_prot (d : Data) (s : Log) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (c : ChainIndex) (step : ChainStep) (hlt : step.val < (wordH (hOf d) lay tree leaf c).val) :
    Prot d s (pt (hOf d) (d none) (.pos (.chain lay tree leaf c step))) := by
  refine ⟨.pos (.chain lay tree leaf c step), fun hsub ↦ ?_, rfl⟩
  by_cases hs : step.val = 0
  · have hq : some (Key.ots lay tree leaf c) ∈ deps (.pos (.chain lay tree leaf c step)) := by
      simp [deps, secretDep, hs]
    obtain ⟨e, -, he⟩ := inv_of_mem_rev d s _ (hsub hq)
    have := mem_chainKeys_ots he
    omega
  · have hc : Position.chain lay tree leaf c ⟨step.val - 1, by omega⟩ ∈
        (Position.chain lay tree leaf c step).children := by
      simp [Position.children, show 0 < step.val by omega]
    have hq : some (Key.pos (.chain lay tree leaf c ⟨step.val - 1, by omega⟩)) ∈
        deps (.pos (.chain lay tree leaf c step)) := by
      simp only [deps, Finset.mem_insert, Finset.mem_union, List.mem_toFinset, List.mem_map]
      exact Or.inr (Or.inr ⟨_, hc, rfl⟩)
    rcases inv_of_mem_rev d s _ (hsub hq) with ⟨e, -, he⟩ | ⟨e, -, j', hj', he⟩
    · have := mem_chainKeys_ots he
      omega
    · have := mem_chainKeys_chain he
      simp only at hj'
      omega

/-- An honest input at an encoding address is the key's encoding input at that counter. -/
theorem honest_encoding (d : Data) {k : Key} {param : PublicParameter} {lay : Layer} {tree : TreeIndex}
    {leaf : LeafIndex} {msg : HashInput} {c : Counter} (hmsg : msg.length = 16)
    (hk : inputD d k = Wots.encodingInput param lay tree leaf msg c) :
    k = .enc lay tree leaf c ∧ msg = (dataOf (hOf d)).keyMessage lay tree leaf := by
  have hlen := congrArg List.length hk
  have h4 : (bytesBE 4 c).length = 4 := bytesBE_length 4 c
  simp only [Wots.encodingInput, tweakableHashInput_length, List.length_append, hmsg, h4] at hlen
  cases k with
  | pkSeed => simp only [inputD, length_input_pkSeed] at hlen; omega
  | prf => simp only [inputD, length_input_prf] at hlen; omega
  | ots => simp only [inputD, length_input_ots] at hlen; omega
  | fts => simp only [inputD, length_input_fts] at hlen; omega
  | rnd => simp only [inputD, length_input_rnd] at hlen; omega
  | dig => simp only [inputD, length_input_dig] at hlen; omega
  | pos p => simp only [inputD, length_input_pos] at hlen; omega
  | enc lay' tree' leaf' c' =>
    simp only [inputD, input, Wots.encodingInput] at hk
    obtain ⟨hf, -, hpay⟩ := tweakableInput_injective hk
    have hd := hashFields_injective (left := .encoding lay' tree' leaf')
      (right := .encoding lay tree leaf) trivial trivial hf
    simp only [HashDomain.encoding.injEq] at hd
    obtain ⟨rfl, rfl, rfl⟩ := hd
    have hl : ((dataOf (hOf d)).keyMessage lay' tree' leaf').length = msg.length := by
      rw [dataOf_keyMessage, rootPayload_length, hmsg]
    obtain ⟨hm, hc⟩ := List.append_inj hpay hl
    exact ⟨by rw [bytesBE_injective hc], hm.symm⟩

/-- Two counters of a key on a path whose encodings carry the key's word: a collision of the data. -/
def BadEnc (d : Data) : Prop :=
  ∃ (i : Index) (lay : Layer) (cw : Counter × Encoding) (c : Counter),
    encH (hOf d) lay (treeIndexAt i lay) (leafIndexAt i lay) encodingAttemptLimit 0 = some cw ∧
    c ≠ cw.1 ∧ truncateHash (hOf d (.enc lay (treeIndexAt i lay) (leafIndexAt i lay) c)) =
      Completeness.pack cw.2

theorem encH_none_decode (h : Key → HashOutput) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) :
    ∀ n c₀, encH h lay tree leaf n c₀ = none → ∀ c, c₀ ≤ c → c < c₀ + n →
      TargetSum.decodeDigest (truncateHash (h (.enc lay tree leaf (BitVec.ofNat counterBits c)))) =
        none := by
  intro n
  induction n with
  | zero => intro c₀ _ c h1 h2; omega
  | succ n ih =>
    intro c₀ hn c h1 h2
    simp only [encH] at hn
    split at hn
    · simp at hn
    · rename_i hdec
      rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
      · exact hdec
      · exact ih (c₀ + 1) hn c (by omega) (by omega)

/-- The verifier's run on the hash that answers the honest inputs from the data. -/
abbrev fD (d : Data) (G : Input → HashOutput) : QueryImpl HashSpec Id :=
  QueryImpl.ofFn (ovFun (d none) (hOf d) G)

/-- The public key read from the data. -/
abbrev pkD (d : Data) : PublicKey := (keysH (d none) (hOf d)).1

/-- The outcomes of a branch: a hit, a protected read, or a collision of encodings. -/
def BranchOut (d : Data) (s : Log) (G : Input → HashOutput) (trace : List HashInput) : Prop :=
  (∃ l ∈ trace, HitAt d G l) ∨ (∃ l ∈ trace, ∃ x : Input, x.1 = l ∧ Prot d s x) ∨ BadEnc d

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
theorem wotsException_out (d : Data) (s : Log) (G : Input → HashOutput) (message : Message)
    (signature : Signature) (lay : Layer)
    (h : SignatureWitness.WotsException (fD d G) (pkD d) (d none) message signature lay) :
    BranchOut d s G (SignatureWitness.trace (fD d G) (pkD d) message signature) := by
  set f := fD d G
  set i := SignatureWitness.index f (pkD d) message signature
  have hcons := consistent_ovFun (d none) (hOf d) G
  have hact : PrunedGraph.KeyActive (param (hOf d)) lay (treeIndexAt i lay) (leafIndexAt i lay) :=
    ⟨i, landed_full _ _, rfl, rfl⟩
  unfold SignatureWitness.WotsException at h
  rcases h with ⟨msg, counter, hmsg, hexempt, hmem, hout⟩ | ⟨endpoints, hne, hmem, hout⟩ | hchain
  · -- an encoding match
    have htarget : ReferenceChoice.target f (pkD d).parameter lay (treeIndexAt i lay) (leafIndexAt i lay)
        (SignatureWitness.canonicalMessage f (pkD d).parameter (d none) i lay) =
        encTarget d lay (treeIndexAt i lay) (leafIndexAt i lay) := by
      unfold ReferenceChoice.target encTarget
      rw [← chosenWord_eq d G i lay]
      rfl
    rw [htarget] at hout
    set l := Wots.encodingInput (pkD d).parameter lay (treeIndexAt i lay) (leafIndexAt i lay) msg counter
      with hl
    have hlen : l.length ≤ maxLen := by
      have h4 : (bytesBE 4 counter).length = 4 := bytesBE_length 4 counter
      rw [hl, Wots.encodingInput, tweakableHashInput_length, List.length_append, hmsg, h4]
      unfold maxLen
      omega
    by_cases hon : ∃ k, inputD d k = l
    · obtain ⟨k, hk⟩ := hon
      obtain ⟨rfl, hmsgEq⟩ := honest_encoding d hmsg hk
      have hv : ovFun (d none) (hOf d) G l = hOf d (.enc lay (treeIndexAt i lay) (leafIndexAt i lay) counter) :=
        hk ▸ ovFun_input (d none) (hOf d) G _
      have hout' : truncateHash (hOf d (.enc lay (treeIndexAt i lay) (leafIndexAt i lay) counter)) =
          encTarget d lay (treeIndexAt i lay) (leafIndexAt i lay) := hv ▸ hout
      cases hsel : encH (hOf d) lay (treeIndexAt i lay) (leafIndexAt i lay) encodingAttemptLimit 0 with
      | none =>
        exfalso
        have hw : wordH (hOf d) lay (treeIndexAt i lay) (leafIndexAt i lay) = ReferenceChoice.dummyWord := by
          unfold wordH
          rw [hsel]
          rfl
        have hdec := encH_none_decode (hOf d) lay _ _ _ 0 hsel counter.toNat (Nat.zero_le _)
          (by have := counter.isLt; unfold encodingAttemptLimit; simpa [counterBits] using this)
        rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, hout', encTarget, hw,
          Completeness.decodeDigest_pack _ ReferenceChoice.dummyWord_valid] at hdec
        simp at hdec
      | some cw =>
        refine Or.inr (Or.inr ⟨i, lay, cw, counter, hsel, fun hc ↦ hexempt ?_, ?_⟩)
        · have hs : ReferenceChoice.selection f (pkD d).parameter lay
              (SignatureWitness.keyTree i lay) (SignatureWitness.keyLeaf i lay)
              (SignatureWitness.canonicalMessage f (pkD d).parameter (d none) i lay) = some cw :=
            (selection_eq d G i lay).trans hsel
          have hm : SignatureWitness.canonicalMessage f (pkD d).parameter (d none) i lay = msg :=
            (canonicalMessage_eq_data d G i lay).trans hmsgEq.symm
          unfold ReferenceChoice.exemptInput
          rw [hs, Option.map_some, hm, ← hc]
        · rw [hout']
          unfold encTarget wordH
          rw [hsel]
          rfl
    · push Not at hon
      refine Or.inl ⟨l, hmem, ⟨l, hlen⟩, rfl, hon, Or.inr ⟨lay, treeIndexAt i lay, leafIndexAt i lay,
        (pkD d).parameter, msg ++ bytesBE 4 counter, rfl, ?_⟩⟩
      rw [← (ans_of_not_honest d s G ⟨l, hlen⟩ hon).1]
      exact hout
  · -- a leaf output match
    have hcan : inputD d (.pos (.leaf lay (treeIndexAt i lay) (leafIndexAt i lay))) =
        tweakableHashInput (param (hOf d)) (.leaf lay (treeIndexAt i lay) (leafIndexAt i lay))
          (leafPayload (Completeness.otsEndpoint f (param (hOf d)) lay (treeIndexAt i lay)
            (leafIndexAt i lay) (d none))) := by
      rw [← canonical_eq_input d G, leaf_input f _ (d none) _ hcons lay _ _ hact]
    refine Or.inl ⟨_, hmem, hit_of_position d G (.leaf lay _ _) _ ?_ ?_ ?_ ?_⟩
    · rw [leafPayload_length]; decide
    · rw [leafPayload_length]
    · rw [hcan]
      intro heq
      exact hne (tweakableInput_injective heq).2.2
    · have hv := ovFun_input (d none) (hOf d) G (.pos (.leaf lay (treeIndexAt i lay) (leafIndexAt i lay)))
      change ovFun (d none) (hOf d) G (inputD d _) = _ at hv
      rw [hcan] at hv
      refine hout.trans ?_
      simp only [Wots.canonicalLeaf, leafHash, Completeness.eval_tweakableHash]
      exact congrArg truncateHash hv
  · -- a chain exception
    rcases Wots.ChainException.hidden_or_output _ _ _ _ _ _ _ hchain with
      ⟨c, step, hlt, hmem⟩ | ⟨c, step, payload, hmem, hpay, hout⟩
    · have hin := chain_input f _ (d none) _ hcons lay _ _ hact c step
      rw [canonical_eq_input d G] at hin
      refine Or.inr (Or.inl ⟨_, hmem, pt (hOf d) (d none) (.pos (.chain lay (treeIndexAt i lay)
        (leafIndexAt i lay) c step)), ?_, ?_⟩)
      · exact hin
      · refine chain_below_prot d s lay _ _ c step ?_
        rw [← chosenWord_eq d G i lay]
        exact hlt
    · refine Or.inl ⟨_, hmem, hit_of_position d G (.chain lay _ _ c step) _ ?_ ?_ ?_ ?_⟩
      · rw [bytesLE_length]
      · rw [bytesLE_length]; omega
      · rw [← canonical_eq_input d G, chain_input f _ (d none) _ hcons lay _ _ hact c step]
        intro heq
        exact hpay (bytesLE_injective (tweakableInput_injective heq).2.2)
      · have hv := chain_value f _ (d none) _ hcons lay _ _ hact c step
        exact hout.trans hv.symm

end Qrom.Sphincs
