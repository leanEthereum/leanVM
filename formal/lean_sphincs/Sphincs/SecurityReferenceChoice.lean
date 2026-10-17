import Sphincs.SecurityPrefixSignLayer

/-! A valid WOTS reference exists even when the canonical FORS-key encoding search fails.
The failure branch uses a fixed valid dummy word and has no exempt encoding input. -/

open OracleComp OracleSpec

namespace Sphincs.Security.ReferenceChoice
open Concrete Completeness Prefix

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local irreducible] firstEncoding encodingAttemptLimit Seeded.forestKey

def dummyWord : Encoding := fun index => if index.val < 40 then ⟨3, by decide⟩ else ⟨0, by decide⟩

theorem dummyWord_valid : TargetSum.Valid dummyWord := by decide

variable (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
  (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (referenceMessage : Digest)

theorem firstEncoding_sound (attempts start : Nat) (counter : Counter) (word : Encoding)
    (h : firstEncoding f parameter lay tree leaf referenceMessage attempts start = some (counter, word)) :
    evalWithAnswerFn f (encode parameter lay tree leaf referenceMessage counter :
      OracleComp HashSpec (Option Encoding)) = some word := by
  induction attempts generalizing start with
  | zero => simp only [firstEncoding, reduceCtorEq] at h
  | succ attempts ih =>
      cases he : evalWithAnswerFn f
        (encode parameter lay tree leaf referenceMessage (BitVec.ofNat counterBits start) :
          OracleComp HashSpec (Option Encoding)) with
      | none =>
          simp only [firstEncoding, he] at h
          exact ih _ h
      | some found =>
          simp only [firstEncoding, he, Option.some.injEq, Prod.mk.injEq] at h
          simpa only [h.1, h.2] using he

noncomputable def selection : Option (Counter × Encoding) :=
  firstEncoding f parameter lay tree leaf referenceMessage encodingAttemptLimit 0

noncomputable def word : Encoding :=
  ((selection f parameter lay tree leaf referenceMessage).map Prod.snd).getD dummyWord

theorem word_of_some (counter : Counter) (chosen : Encoding)
    (h : selection f parameter lay tree leaf referenceMessage = some (counter, chosen)) :
    word f parameter lay tree leaf referenceMessage = chosen := by
  simp only [word, h, Option.map_some, Option.getD_some]

theorem word_of_none (h : selection f parameter lay tree leaf referenceMessage = none) :
    word f parameter lay tree leaf referenceMessage = dummyWord := by
  simp only [word, h, Option.map_none, Option.getD_none]

theorem word_valid : TargetSum.Valid (word f parameter lay tree leaf referenceMessage) := by
  cases h : selection f parameter lay tree leaf referenceMessage with
  | none => rw [word_of_none _ _ _ _ _ _ h]; exact dummyWord_valid
  | some pair =>
      rw [word_of_some _ _ _ _ _ _ pair.1 pair.2 h]
      exact EncodingCode.decode_valid (Wots.decode_of_encode f parameter lay tree leaf referenceMessage
        pair.1 pair.2 (firstEncoding_sound f parameter lay tree leaf referenceMessage
          encodingAttemptLimit 0 pair.1 pair.2 h))

noncomputable def exemptInput : Option HashInput :=
  (selection f parameter lay tree leaf referenceMessage).map fun pair =>
    Wots.encodingInput parameter lay tree leaf referenceMessage pair.1

noncomputable def target : Digest := pack (word f parameter lay tree leaf referenceMessage)

theorem target_decodes : TargetSum.decodeDigest (target f parameter lay tree leaf referenceMessage) =
    some (word f parameter lay tree leaf referenceMessage) :=
  decodeDigest_pack _ (word_valid f parameter lay tree leaf referenceMessage)

theorem same_word_target (message : Digest) (counter : Counter)
    (h : evalWithAnswerFn f (encode parameter lay tree leaf message counter :
      OracleComp HashSpec (Option Encoding)) = some (word f parameter lay tree leaf referenceMessage)) :
    truncateHash (f (Wots.encodingInput parameter lay tree leaf message counter)) =
      target f parameter lay tree leaf referenceMessage :=
  EncodingCode.decode_some_injective
    (Wots.decode_of_encode f parameter lay tree leaf message counter _ h)
    (target_decodes f parameter lay tree leaf referenceMessage)

/-- One target per encoding tweak; the canonical successful input is its only exemption. -/
def EncodingMatch (trace : List HashInput) : Prop :=
  ∃ message counter,
    exemptInput f parameter lay tree leaf referenceMessage ≠
      some (Wots.encodingInput parameter lay tree leaf message counter) ∧
    Wots.encodingInput parameter lay tree leaf message counter ∈ trace ∧
    truncateHash (f (Wots.encodingInput parameter lay tree leaf message counter)) =
      target f parameter lay tree leaf referenceMessage

/-- This classification needs no successful honest signature or counter at the leaf. If
canonical encoding exhausts, recovering the dummy word instead supplies an encoding match. -/
theorem otsLeaf_classification (secret : ChainIndex → Digest) (message : Digest)
    (counter : Counter) (values : ChainIndex → Digest) (candidate : Encoding) (trace : List HashInput)
    (hencode : evalWithAnswerFn f (encode parameter lay tree leaf message counter :
      OracleComp HashSpec (Option Encoding)) = some candidate)
    (hrun : ContainsRun f trace (otsLeaf parameter lay tree leaf message counter values))
    (hleaf : evalWithAnswerFn f (otsLeaf parameter lay tree leaf message counter values :
      OracleComp HashSpec (Option Digest)) = some (Wots.canonicalLeaf f parameter lay tree leaf secret)) :
    (∃ chosenCounter,
      selection f parameter lay tree leaf referenceMessage =
        some (chosenCounter, word f parameter lay tree leaf referenceMessage) ∧
      message = referenceMessage ∧ counter = chosenCounter ∧
      ∀ index, values index = Wots.frontier f parameter lay tree leaf
        (word f parameter lay tree leaf referenceMessage) secret index) ∨
    EncodingMatch f parameter lay tree leaf referenceMessage trace ∨
    Wots.LeafOutputMatch f parameter lay tree leaf secret trace ∨
    Wots.ChainException f parameter lay tree leaf
      (word f parameter lay tree leaf referenceMessage) secret trace := by
  rcases Wots.otsLeaf_classification f parameter lay tree leaf
      (word f parameter lay tree leaf referenceMessage) secret message counter values candidate trace
      (word_valid f parameter lay tree leaf referenceMessage) hencode hrun hleaf with
    ⟨hword, hvalues⟩ | hmatch | hchain
  · have ht := same_word_target f parameter lay tree leaf referenceMessage message counter
      (hword ▸ hencode)
    by_cases he : exemptInput f parameter lay tree leaf referenceMessage =
        some (Wots.encodingInput parameter lay tree leaf message counter)
    · cases hs : selection f parameter lay tree leaf referenceMessage with
      | none => simp only [exemptInput, hs, Option.map_none, reduceCtorEq] at he
      | some pair =>
          have hi : Wots.encodingInput parameter lay tree leaf referenceMessage pair.1 =
              Wots.encodingInput parameter lay tree leaf message counter := by
            simpa only [exemptInput, hs, Option.map_some, Option.some.injEq] using he
          obtain ⟨hm, hc⟩ := Wots.encodingInput_injective parameter lay tree leaf hi
          refine Or.inl ⟨pair.1, ?_, hm.symm, hc.symm, hvalues⟩
          rw [word_of_some f parameter lay tree leaf referenceMessage pair.1 pair.2 hs]
    · exact Or.inr (Or.inl ⟨message, counter, he,
        hrun.bind_left _ (Wots.encode_query_mem f parameter lay tree leaf message counter), ht⟩)
  · exact Or.inr (Or.inr (Or.inl hmatch))
  · exact Or.inr (Or.inr (Or.inr hchain))

end Sphincs.Security.ReferenceChoice
