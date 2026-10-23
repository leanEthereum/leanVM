import SphincsFors.SecurityChainWitness
import SphincsFors.SecurityEncoding

set_option backward.isDefEq.respectTransparency false

/-! WOTS+C extraction from the actual verifier trace, adapted from leanVM b7a107256.
The exceptional cases remain explicit: leaf or forward-chain output matches, two linked prefix
edges, two prefix contacts, or a unit-neighbor encoding together with one prefix contact. -/

open OracleComp OracleSpec

namespace SphincsFors.Security.Wots

open Concrete Chain

attribute [local irreducible] chainWalk

private theorem flatMap_ofFn_injective {α β : Type} (g : α → List β) (len : Nat)
    (hlen : ∀ a, (g a).length = len) (hinj : ∀ a b, g a = g b → a = b) :
    ∀ {n : Nat} {f f' : Fin n → α},
      (List.ofFn f).flatMap g = (List.ofFn f').flatMap g → f = f' := by
  intro n
  induction n with
  | zero => intro f f' _; funext i; exact i.elim0
  | succ n ih =>
      intro f f' h
      simp only [List.ofFn_succ, List.flatMap_cons] at h
      obtain ⟨hhead, htail⟩ := List.append_inj h (by rw [hlen, hlen])
      have hzero := hinj _ _ hhead
      have hsucc := ih htail
      funext i
      cases i using Fin.cases with
      | zero => exact hzero
      | succ j => exact congrFun hsucc j

theorem leafPayload_injective {endpoints endpoints' : ChainIndex → Digest}
    (h : leafPayload endpoints = leafPayload endpoints') : endpoints = endpoints' :=
  flatMap_ofFn_injective (bytesLE 16) 16 (bytesLE_length 16)
    (fun _ _ => bytesLE_injective) h

variable (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)

def encodingInput (message : Digest) (counter : Counter) : HashInput :=
  tweakableHashInput parameter (.encoding lay tree leaf) (bytesLE 16 message ++ bytesLE 4 counter)

theorem encodingInput_injective {message message' : Digest} {counter counter' : Counter}
    (h : encodingInput parameter lay tree leaf message counter =
      encodingInput parameter lay tree leaf message' counter') :
    message = message' ∧ counter = counter' := by
  have hpayload := List.append_cancel_left h
  obtain ⟨hm, hc⟩ := List.append_inj hpayload (by simp [bytesLE_length])
  exact ⟨bytesLE_injective hm, bytesLE_injective hc⟩

theorem encode_query_mem (message : Digest) (counter : Counter) :
    encodingInput parameter lay tree leaf message counter ∈
      queriedInputs f (encode parameter lay tree leaf message counter) := by
  simp only [encode, queriedInputs_bind, queriedInputs_tweakableHash, queriedInputs_pure,
    List.append_nil, List.mem_singleton, encodingInput]

theorem decode_of_encode (message : Digest) (counter : Counter) (candidate : Encoding)
    (hencode : evalWithAnswerFn f (encode parameter lay tree leaf message counter
      : OracleComp HashSpec (Option Encoding)) = some candidate) :
    TargetSum.decodeDigest (truncateHash (f (encodingInput parameter lay tree leaf message counter))) =
      some candidate := by
  simpa only [encode, evalWithAnswerFn_bind, Completeness.eval_tweakableHash,
    evalWithAnswerFn_pure, encodingInput] using hencode

theorem otsLeaf_chain_run (message : Digest) (counter : Counter) (values : ChainIndex → Digest)
    (candidate : Encoding) (trace : List HashInput)
    (hencode : evalWithAnswerFn f (encode parameter lay tree leaf message counter
      : OracleComp HashSpec (Option Encoding)) = some candidate)
    (hrun : ContainsRun f trace (otsLeaf parameter lay tree leaf message counter values))
    (index : ChainIndex) :
    ContainsRun f trace (recoverChain parameter lay tree leaf index (candidate index) (values index)) := by
  have htail := hrun.bind_right
  rw [hencode] at htail
  exact ContainsRun.sequenceFin_component _ htail.bind_left index

theorem otsLeaf_leaf_query_mem (message : Digest) (counter : Counter)
    (values : ChainIndex → Digest) (candidate : Encoding)
    (hencode : evalWithAnswerFn f (encode parameter lay tree leaf message counter
      : OracleComp HashSpec (Option Encoding)) = some candidate) :
    tweakableHashInput parameter (.leaf lay tree leaf)
      (leafPayload fun index => evalWithAnswerFn f
        (recoverChain parameter lay tree leaf index (candidate index) (values index))) ∈
      queriedInputs f (otsLeaf parameter lay tree leaf message counter values) := by
  rw [otsLeaf]
  apply queriedInputs_mono_bind_right
  rw [hencode]
  apply queriedInputs_mono_bind_right
  apply queriedInputs_mono_bind_left
  simp only [Completeness.eval_sequenceFin, leafHash, queriedInputs_tweakableHash,
    List.mem_singleton]

/-- A queried encoding output is a unit neighbor of the reference at this lowered chain. -/
def EncodingMarker (reference : Encoding) (lowered : ChainIndex) (trace : List HashInput) : Prop :=
  ∃ message counter candidate,
    encodingInput parameter lay tree leaf message counter ∈ trace ∧
    TargetSum.decodeDigest
      (truncateHash (f (encodingInput parameter lay tree leaf message counter))) = some candidate ∧
    EncodingCode.UnitNeighborAt reference candidate lowered

theorem otsLeaf_marker (reference : Encoding) (message : Digest) (counter : Counter)
    (values : ChainIndex → Digest) (candidate : Encoding) (trace : List HashInput)
    (hencode : evalWithAnswerFn f (encode parameter lay tree leaf message counter
      : OracleComp HashSpec (Option Encoding)) = some candidate)
    (hrun : ContainsRun f trace (otsLeaf parameter lay tree leaf message counter values))
    (index : ChainIndex) (hneighbor : EncodingCode.UnitNeighborAt reference candidate index) :
    EncodingMarker f parameter lay tree leaf reference index trace :=
  ⟨message, counter, candidate,
    hrun.bind_left _ (encode_query_mem f parameter lay tree leaf message counter),
    decode_of_encode f parameter lay tree leaf message counter candidate hencode, hneighbor⟩

variable (reference : Encoding) (secret : ChainIndex → Digest)

def frontier (index : ChainIndex) : Digest :=
  honestChain f parameter lay tree leaf index (secret index) (reference index).val

def ChainException (trace : List HashInput) : Prop :=
  (∃ index, ForwardMatch f parameter lay tree leaf index (secret index) (reference index) trace) ∨
  (∃ index, TwoEdge f parameter lay tree leaf index (reference index)
    (frontier f parameter lay tree leaf reference secret index) trace) ∨
  (∃ left right, left ≠ right ∧
    Contact f parameter lay tree leaf left (reference left)
      (frontier f parameter lay tree leaf reference secret left) trace ∧
    Contact f parameter lay tree leaf right (reference right)
      (frontier f parameter lay tree leaf reference secret right) trace) ∨
  (∃ index, EncodingMarker f parameter lay tree leaf reference index trace ∧
    Contact f parameter lay tree leaf index (reference index)
      (frontier f parameter lay tree leaf reference secret index) trace)

theorem otsLeaf_chain_classification (message : Digest) (counter : Counter)
    (values : ChainIndex → Digest) (candidate : Encoding) (trace : List HashInput)
    (hvalid : TargetSum.Valid reference)
    (hencode : evalWithAnswerFn f (encode parameter lay tree leaf message counter
      : OracleComp HashSpec (Option Encoding)) = some candidate)
    (hrun : ContainsRun f trace (otsLeaf parameter lay tree leaf message counter values))
    (hendpoints : ∀ index, evalWithAnswerFn f
      (recoverChain parameter lay tree leaf index (candidate index) (values index)) =
        honestChain f parameter lay tree leaf index (secret index) (chainLength - 1)) :
    (candidate = reference ∧ ∀ index,
      values index = frontier f parameter lay tree leaf reference secret index) ∨
      ChainException f parameter lay tree leaf reference secret trace := by
  by_cases hforward : ∃ index,
      ForwardMatch f parameter lay tree leaf index (secret index) (reference index) trace
  · exact Or.inr (Or.inl hforward)
  have hn (index : ChainIndex) :
      ¬ForwardMatch f parameter lay tree leaf index (secret index) (reference index) trace :=
    fun h => hforward ⟨index, h⟩
  have hc (index : ChainIndex) :=
    otsLeaf_chain_run f parameter lay tree leaf message counter values candidate trace hencode hrun index
  have hf (index : ChainIndex) (hb : (candidate index).val ≤ (reference index).val) :
      walkValue f parameter lay tree leaf index (candidate index).val (values index)
        ((reference index).val - (candidate index).val) =
          frontier f parameter lay tree leaf reference secret index :=
    recover_frontier f parameter lay tree leaf index (secret index) (reference index)
      (candidate index) (values index) trace hb (hendpoints index) (hc index) (hn index)
  have hcontact (index : ChainIndex) (hb : (candidate index).val < (reference index).val) :
      Contact f parameter lay tree leaf index (reference index)
        (frontier f parameter lay tree leaf reference secret index) trace :=
    recover_contact f parameter lay tree leaf index (reference index) (candidate index)
      (values index) _ trace hb (hf index (Nat.le_of_lt hb)) (hc index)
  have hcandidate := EncodingCode.decode_valid
    (decode_of_encode f parameter lay tree leaf message counter candidate hencode)
  rcases EncodingCode.valid_encoding_classification hvalid hcandidate with
    heq | ⟨index, hneighbor⟩ | ⟨index, hlarge⟩ | ⟨left, right, hne, hl, hr⟩
  · refine Or.inl ⟨heq.symm, ?_⟩
    intro index
    have hd := congrArg (fun word : Encoding => word index) heq
    simpa only [frontier, hd] using recover_value f parameter lay tree leaf index (secret index)
      (reference index) (candidate index) (values index) trace (by rw [hd])
      (hendpoints index) (hc index) (hn index)
  · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨index,
      otsLeaf_marker f parameter lay tree leaf reference message counter values candidate trace
        hencode hrun index hneighbor, ?_⟩)))
    have hd := hneighbor.2.2.1
    exact hcontact index (by omega)
  · exact Or.inr (Or.inr (Or.inl ⟨index,
      recover_twoEdge f parameter lay tree leaf index (reference index) (candidate index)
        (values index) _ trace hlarge (hf index (by omega)) (hc index)⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨left, right, hne, hcontact left hl, hcontact right hr⟩)))

def canonicalLeaf : Digest := evalWithAnswerFn f (leafHash parameter lay tree leaf
  (fun index => honestChain f parameter lay tree leaf index (secret index) (chainLength - 1)))

/-- A distinct serialized endpoint vector reaches the canonical WOTS leaf. -/
def LeafOutputMatch (trace : List HashInput) : Prop :=
  ∃ endpoints : ChainIndex → Digest,
    leafPayload endpoints ≠ leafPayload
      (fun index => honestChain f parameter lay tree leaf index (secret index) (chainLength - 1)) ∧
    tweakableHashInput parameter (.leaf lay tree leaf) (leafPayload endpoints) ∈ trace ∧
    truncateHash (f (tweakableHashInput parameter (.leaf lay tree leaf) (leafPayload endpoints))) =
      canonicalLeaf f parameter lay tree leaf secret

/-- The complete WOTS verifier either recovers the reference word and frontier, or exposes
one of the explicit leaf, chain, prefix-contact, or encoding-neighbor witnesses. -/
theorem otsLeaf_classification (message : Digest) (counter : Counter)
    (values : ChainIndex → Digest) (candidate : Encoding) (trace : List HashInput)
    (hvalid : TargetSum.Valid reference)
    (hencode : evalWithAnswerFn f (encode parameter lay tree leaf message counter
      : OracleComp HashSpec (Option Encoding)) = some candidate)
    (hrun : ContainsRun f trace (otsLeaf parameter lay tree leaf message counter values))
    (hleaf : evalWithAnswerFn f (otsLeaf parameter lay tree leaf message counter values
      : OracleComp HashSpec (Option Digest)) = some (canonicalLeaf f parameter lay tree leaf secret)) :
    (candidate = reference ∧ ∀ index,
      values index = frontier f parameter lay tree leaf reference secret index) ∨
      LeafOutputMatch f parameter lay tree leaf secret trace ∨
      ChainException f parameter lay tree leaf reference secret trace := by
  let endpoints := fun index => evalWithAnswerFn f
    (recoverChain parameter lay tree leaf index (candidate index) (values index))
  have heval : evalWithAnswerFn f (leafHash parameter lay tree leaf endpoints) =
      canonicalLeaf f parameter lay tree leaf secret := by
    simpa only [otsLeaf, evalWithAnswerFn_bind, hencode, Completeness.eval_sequenceFin,
      evalWithAnswerFn_pure, Option.some.injEq, endpoints] using hleaf
  by_cases hp : leafPayload endpoints = leafPayload
      (fun index => honestChain f parameter lay tree leaf index (secret index) (chainLength - 1))
  · have hs := otsLeaf_chain_classification f parameter lay tree leaf reference secret message counter
      values candidate trace hvalid hencode hrun (fun index => congrFun (leafPayload_injective hp) index)
    exact hs.imp_right Or.inr
  · refine Or.inr (Or.inl ⟨endpoints, hp, ?_, ?_⟩)
    · exact hrun _ (otsLeaf_leaf_query_mem f parameter lay tree leaf message counter values candidate hencode)
    · simpa only [leafHash, Completeness.eval_tweakableHash] using heval

/-- Another message/counter input has the same truncated encoding hash as the reference. -/
def EncodingOutputMatch (referenceMessage : Digest) (referenceCounter : Counter)
    (trace : List HashInput) : Prop :=
  ∃ message counter,
    encodingInput parameter lay tree leaf message counter ≠
      encodingInput parameter lay tree leaf referenceMessage referenceCounter ∧
    encodingInput parameter lay tree leaf message counter ∈ trace ∧
    truncateHash (f (encodingInput parameter lay tree leaf message counter)) =
      truncateHash (f (encodingInput parameter lay tree leaf referenceMessage referenceCounter))

end SphincsFors.Security.Wots
