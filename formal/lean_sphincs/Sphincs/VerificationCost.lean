import Sphincs.Layout
import Sphincs.Code
import Sphincs.Correctness

set_option backward.isDefEq.respectTransparency false

/-!
Compression counts for the actual verifier's logged hash-input bytes. A hash of `n` bytes costs
`max 1 (ceil (n / 64))`, the BLAKE2s accounting used by `blocks` in `crates/signatures/src/tweak.rs` and
`scripts/scheme.py`. The oracle's answers remain arbitrary; only the byte lengths are counted.
-/

open OracleComp OracleSpec Finset

namespace Sphincs.Cost

open Concrete

/-- BLAKE2s compression blocks, including the block for an empty input. -/
def blocks (bytes : Nat) : Nat := max 1 ((bytes + 63) / 64)

/-- Actual hash inputs on the execution selected by an arbitrary answer function. -/
def hashTrace {α : Type} (f : QueryImpl HashSpec Id) (oa : OracleComp HashSpec α) :
    List HashInput := ((simulateQ f.withLogging oa).run).2.map Sigma.fst

/-- Compression count of the actual execution, with input lengths including parameter and address. -/
def compressions {α : Type} (f : QueryImpl HashSpec Id) (oa : OracleComp HashSpec α) : Nat :=
  ((hashTrace f oa).map (fun input => blocks input.length)).sum

@[simp] theorem hashTrace_pure {α : Type} (f : QueryImpl HashSpec Id) (x : α) :
    hashTrace f (pure x) = [] := rfl

@[simp] theorem hashTrace_query_bind {α : Type} (f : QueryImpl HashSpec Id)
    (input : HashInput) (next : HashOutput → OracleComp HashSpec α) :
    hashTrace f (liftM (HashSpec.query input) >>= next) =
      input :: hashTrace f (next (f input)) := rfl

theorem hashTrace_bind {α β : Type} (f : QueryImpl HashSpec Id)
    (oa : OracleComp HashSpec α) (next : α → OracleComp HashSpec β) :
    hashTrace f (oa >>= next) = hashTrace f oa ++
      hashTrace f (next (evalWithAnswerFn f oa)) := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind input rest ih =>
      rw [bind_assoc, hashTrace_query_bind, hashTrace_query_bind, ih,
        evalWithAnswerFn_bind,
        show evalWithAnswerFn f (liftM (HashSpec.query input)) = f input from
          simulateQ_spec_query f input, List.cons_append]

@[simp] theorem compressions_pure {α : Type} (f : QueryImpl HashSpec Id) (x : α) :
    compressions f (pure x) = 0 := rfl

theorem compressions_bind {α β : Type} (f : QueryImpl HashSpec Id)
    (oa : OracleComp HashSpec α) (next : α → OracleComp HashSpec β) :
    compressions f (oa >>= next) = compressions f oa +
      compressions f (next (evalWithAnswerFn f oa)) := by
  simp [compressions, hashTrace_bind]

@[simp] theorem compressions_oracleHash (f : QueryImpl HashSpec Id) (input : HashInput) :
    compressions f (oracleHash input : OracleComp HashSpec HashOutput) = blocks input.length := rfl

theorem tweakableHashInput_length (parameter : PublicParameter) (domain : HashDomain)
    (payload : HashInput) :
    (tweakableHashInput parameter domain payload).length = 32 + payload.length := by
  simp [tweakableHashInput, tweakBytes, fieldBytes, bytesLE_length]
  omega

@[simp] theorem compressions_tweakableHash (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput) :
    compressions f (Concrete.tweakableHash parameter domain payload) = blocks (32 + payload.length) := by
  rw [Concrete.tweakableHash, compressions_bind, compressions_oracleHash,
    compressions_pure, Nat.add_zero, tweakableHashInput_length]

theorem compressions_sequenceFin {α : Type} {n : Nat} (f : QueryImpl HashSpec Id)
    (computation : Fin n → OracleComp HashSpec α) :
    compressions f (sequenceFin computation) = ∑ i : Fin n, compressions f (computation i) := by
  induction n with
  | zero => simp [sequenceFin]
  | succ n ih =>
      rw [sequenceFin, compressions_bind]
      simp only [compressions_bind, compressions_pure, Nat.add_zero, ih, Fin.sum_univ_succ]

theorem compressions_chainWalk (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (chain : ChainIndex)
    (start steps : Nat) (value : Digest) (hsteps : start + steps ≤ chainLength - 1) :
    compressions f (chainWalk parameter lay tree leaf chain start steps value) = steps := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      rw [chainWalk, compressions_bind, dite_eq_left (by omega), compressions_tweakableHash,
        bytesLE_length, ih (by omega)]
      rfl

@[simp] theorem compressions_recoverChain (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (chain : ChainIndex) (digit : Digit) (value : Digest) :
    compressions f (recoverChain parameter lay tree leaf chain digit value) =
      chainLength - 1 - digit.val := by
  apply compressions_chainWalk
  have := digit.isLt
  omega

@[simp] theorem compressions_leafHash (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (endpoints : ChainIndex → Digest) :
    compressions f (leafHash parameter lay tree leaf endpoints) = 17 := by
  rw [leafHash, compressions_tweakableHash, leafPayload, digest_vector_length]
  rfl

@[simp] theorem compressions_encode (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : Digest) (counter : Counter) :
    compressions f (encode parameter lay tree leaf message counter) = 1 := by
  simp only [encode, compressions_bind, compressions_tweakableHash, List.length_append,
    bytesLE_length, compressions_pure]
  rfl

theorem compressions_treeFold (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (path : Nat → Digest)
    (levels : Nat) (value : Digest) :
    compressions f (treeFold parameter lay tree leaf path levels value) = levels := by
  induction levels with
  | zero => rfl
  | succ levels ih =>
      rw [treeFold, compressions_bind, ih]
      dsimp only
      split <;> simp [compressions_tweakableHash, nodePayload, bytesLE_length, blocks]

theorem lut_sum (t : LutIdx) : ∑ i, (lut t i).val = codewordSum := Completeness.lut_sum t

section Coord

variable (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (index : Index) (c : Coord)

theorem compressions_forestWalk (s : SuperIdx) (j : SubIdx) (a : ChildIdx) (i : FChain)
    (start steps : Nat) (value : Digest) (hsteps : start + steps ≤ chainTop) :
    compressions f (forestWalk parameter index c s j a i start steps value) = steps := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      rw [forestWalk, compressions_bind, dite_eq_left (by omega), compressions_tweakableHash,
        bytesLE_length, ih (by omega)]
      rfl

@[simp] theorem compressions_forestRecoverChain (s : SuperIdx) (j : SubIdx) (a : ChildIdx) (i : FChain)
    (deficit : FPos) (value : Digest) :
    compressions f (forestRecoverChain parameter index c s j a i deficit value) = deficit.val := by
  apply compressions_forestWalk
  have := deficit.isLt
  simp only [chainTop] at this ⊢
  omega

@[simp] theorem compressions_childLeafHash (s : SuperIdx) (j : SubIdx) (a : ChildIdx) (ends : FChain → Digest) :
    compressions f (childLeafHash parameter index c s j a ends) = 2 := by
  rw [childLeafHash, compressions_tweakableHash, childPayload, digest_vector_length]
  rfl

@[simp] theorem compressions_childRecover (s : SuperIdx) (j : SubIdx) (a : ChildIdx) (t : LutIdx)
    (values : FChain → Digest) :
    compressions f (childRecover parameter index c s j a (lut t) values) = 7 := by
  rw [childRecover, compressions_bind, compressions_sequenceFin, compressions_childLeafHash]
  simp only [compressions_forestRecoverChain, lut_sum]
  rfl

theorem compressions_subFold (s : SuperIdx) (j : SubIdx) (a : ChildIdx) (path : Fin subHeight → Digest)
    (levels : Nat) (hlevels : levels ≤ subHeight) (value : Digest) :
    compressions f (subFold parameter index c s j a path levels value) = levels := by
  induction levels with
  | zero => rfl
  | succ levels ih =>
      rw [subFold, compressions_bind, ih (by omega), dite_eq_left (by omega)]
      dsimp only
      split <;> simp [compressions_tweakableHash, nodePayload, bytesLE_length, blocks]

theorem compressions_topFold (s : SuperIdx) (path : Fin topHeight → Digest)
    (levels : Nat) (hlevels : levels ≤ topHeight) (value : Digest) :
    compressions f (topFold parameter index c s path levels value) = levels := by
  induction levels with
  | zero => rfl
  | succ levels ih =>
      rw [topFold, compressions_bind, ih (by omega), dite_eq_left (by omega)]
      dsimp only
      split <;> simp [compressions_tweakableHash, nodePayload, bytesLE_length, blocks]

theorem superPayload_length (tops : SubIdx → Digest × Digest) : (superPayload tops).length = 64 := by
  simp [superPayload, nodePayload, bytesLE_length]

theorem rootsPayload_length (tops : Coord → Digest × Digest) : (rootsPayload tops).length = 256 := by
  simp [rootsPayload, nodePayload, bytesLE_length, forestCoords]

/-- One coordinate costs 23 compressions: per sub-tree 5 chain steps, 2 for the WOTS-key leaf and 2
folds; 2 for the tree leaf (96 bytes); 3 folds. -/
@[simp] theorem compressions_coordRecover (mark : CoordMark) (opening : CoordOpening) :
    compressions f (coordRecover parameter index c mark opening) = 23 := by
  rw [coordRecover, compressions_bind, compressions_sequenceFin, compressions_bind, superHash,
    compressions_tweakableHash, compressions_bind,
    compressions_topFold f parameter index c _ _ _ (by decide : topHeight - 1 ≤ topHeight)]
  simp only [compressions_bind, compressions_childRecover,
    compressions_subFold f parameter index c _ _ _ _ _ (by decide : subHeight - 1 ≤ subHeight),
    compressions_pure, superPayload_length, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul]
  rfl

end Coord

/-- The forest recovery costs 189 compressions: 23 per coordinate and 5 for the key (288 bytes). -/
@[simp] theorem compressions_forestRecover (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (index : Index) (marks : Coord → CoordMark) (opening : Coord → CoordOpening) :
    compressions f (forestRecover parameter index marks opening) = 189 := by
  rw [forestRecover, compressions_bind, compressions_sequenceFin, compressions_tweakableHash]
  simp only [compressions_coordRecover, rootsPayload_length, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rfl

@[simp] theorem compressions_messageDigestCall (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (root : Digest) (message : Message)
    (randomness : Randomness) :
    compressions f (messageDigestCall parameter root message randomness) = 2 := by
  simp only [messageDigestCall, compressions_oracleHash, tweakableHashInput_length,
    messageDigestPayload, List.length_append, bytesLE_length]
  rfl

@[simp] theorem compressions_messageDigest (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (root : Digest) (message : Message) (randomness : Randomness) :
    compressions f (messageDigest parameter root message randomness) = 2 := by
  simp only [messageDigest, compressions_bind, compressions_messageDigestCall,
    compressions_pure]

theorem encode_valid (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (message : Digest)
    (counter : Counter) (word : Encoding)
    (hword : evalWithAnswerFn f (encode parameter lay tree leaf message counter
      : OracleComp HashSpec (Option Encoding)) = some word) : TargetSum.Valid word := by
  simp only [encode, evalWithAnswerFn_bind, evalWithAnswerFn_pure] at hword
  unfold TargetSum.decodeDigest at hword
  split at hword
  next hvalid =>
    cases Option.some.inj hword
    exact hvalid
  next => simp at hword

/-- Recovery spends 90 compressions after an admissible encoding, or one on rejection. -/
theorem compressions_otsLeaf (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (message : Digest)
    (counter : Counter) (values : ChainIndex → Digest) :
    compressions f (otsLeaf parameter lay tree leaf message counter values) =
      if (evalWithAnswerFn f (otsLeaf parameter lay tree leaf message counter values
        : OracleComp HashSpec (Option Digest))).isSome then 90 else 1 := by
  cases henc : evalWithAnswerFn f (encode parameter lay tree leaf message counter
      : OracleComp HashSpec (Option Encoding)) with
  | none =>
      simp only [otsLeaf, compressions_bind, compressions_encode, evalWithAnswerFn_bind,
        henc, evalWithAnswerFn_pure, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
        compressions_pure, Nat.add_zero]
  | some word =>
      have hvalid := encode_valid f parameter lay tree leaf message counter word henc
      simp only [otsLeaf, compressions_bind, compressions_encode, evalWithAnswerFn_bind,
        henc, evalWithAnswerFn_pure, Option.isSome_some, ↓reduceIte,
        compressions_sequenceFin, compressions_recoverChain, compressions_leafHash,
        compressions_pure, Nat.add_zero, Completeness.verification_chain_steps word hvalid]

attribute [local irreducible] otsLeaf encode sequenceFin chainWalk recoverChain leafHash
  forestRecover treeFold messageDigest

/-- The one actual tree layer costs 116 compressions, or one if its encoding is rejected. -/
theorem compressions_verifyLayers (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (index : Index) (signature : Signature) (message : Digest) :
    compressions f (verifyLayers parameter index signature numLayers message) =
      if (evalWithAnswerFn f (verifyLayers parameter index signature numLayers message
        : OracleComp HashSpec (Option Digest))).isSome then 116 else 1 := by
  rw [show numLayers = 0 + 1 from rfl, verifyLayers, dite_eq_left (by decide : 0 < numLayers)]
  simp only [compressions_bind, evalWithAnswerFn_bind]
  rw [compressions_otsLeaf]
  cases hleaf : evalWithAnswerFn f (otsLeaf parameter topLayer (treeIndexAt index topLayer)
      (leafIndexAt index topLayer) message (signature.layers topLayer).counter
      (signature.layers topLayer).chainValues : OracleComp HashSpec (Option Digest)) <;>
    simp only [topLayer] at hleaf
  all_goals simp only [hleaf, compressions_bind, compressions_treeFold, verifyLayers,
    evalWithAnswerFn_bind, evalWithAnswerFn_pure, compressions_pure, Nat.add_zero,
    Option.isSome_some, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
  rfl

attribute [local semireducible] Concrete.verify

/-- Every accepted signature causes exactly 307 BLAKE2s compressions in the verifier execution: 2 for
the digest, 189 for the forest and 116 for WOTS+C and the path. -/
theorem verification_compressions (f : QueryImpl HashSpec Id) (pk : PublicKey)
    (message : Message) (signature : Signature)
    (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    compressions f (Concrete.verify pk message signature : OracleComp HashSpec Bool) = 307 := by
  rw [Concrete.verify, compressions_bind, compressions_messageDigest,
    compressions_bind, compressions_forestRecover, compressions_bind, compressions_verifyLayers]
  simp only [Concrete.verify, evalWithAnswerFn_bind] at haccept
  split at haccept
  next root hroot =>
    rw [hroot]
    rfl
  next => simp at haccept

/-- Malformed signatures cannot make verification exceed its accepted-signature cost. -/
theorem verification_compressions_le (f : QueryImpl HashSpec Id) (pk : PublicKey)
    (message : Message) (signature : Signature) :
    compressions f (Concrete.verify pk message signature : OracleComp HashSpec Bool) ≤ 307 := by
  rw [Concrete.verify, compressions_bind, compressions_messageDigest,
    compressions_bind, compressions_forestRecover, compressions_bind, compressions_verifyLayers]
  split <;> split <;> simp [compressions_pure]

end Sphincs.Cost
