import Sphincs.Layout
import Sphincs.Code
import Sphincs.Correctness

/-!
Keccak-f permutation counts for the actual verifier's logged hash-input bytes. A hash of `n` bytes
costs `max 1 (ceil (n / 128))`, the leanVM hash's (Keccak-256 in the cell encoding, 128 message bytes
a permutation), as `blocks` counts it in `crates/signatures/src/tweak.rs`; the total is
`lean_sphincs::VERIFY_PERMUTATIONS`. The oracle's answers remain arbitrary; only the byte lengths are
counted.
-/

open OracleComp OracleSpec Finset

namespace Sphincs.Cost

open Concrete

/-- Permutations of the leanVM hash: one per started 128-byte block, one for the empty input. -/
def blocks (bytes : Nat) : Nat := max 1 ((bytes + 127) / 128)

/-- Actual hash inputs on the execution selected by an arbitrary answer function. -/
def hashTrace {α : Type} (f : QueryImpl HashSpec Id) (oa : OracleComp HashSpec α) :
    List HashInput := ((simulateQ f.withLogging oa).run).2.map Sigma.fst

/-- Permutation count of the actual execution, with input lengths including parameter and address. -/
def permutations {α : Type} (f : QueryImpl HashSpec Id) (oa : OracleComp HashSpec α) : Nat :=
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

@[simp] theorem permutations_pure {α : Type} (f : QueryImpl HashSpec Id) (x : α) :
    permutations f (pure x) = 0 := rfl

theorem permutations_bind {α β : Type} (f : QueryImpl HashSpec Id)
    (oa : OracleComp HashSpec α) (next : α → OracleComp HashSpec β) :
    permutations f (oa >>= next) = permutations f oa +
      permutations f (next (evalWithAnswerFn f oa)) := by
  simp [permutations, hashTrace_bind]

@[simp] theorem permutations_oracleHash (f : QueryImpl HashSpec Id) (input : HashInput) :
    permutations f (oracleHash input : OracleComp HashSpec HashOutput) = blocks input.length := rfl

theorem tweakableHashInput_length (parameter : PublicParameter) (domain : HashDomain)
    (payload : HashInput) :
    (tweakableHashInput parameter domain payload).length = 32 + payload.length := by
  simp [tweakableHashInput, tweakBytes, fieldBytes, bytesLE_length]
  omega

@[simp] theorem permutations_tweakableHash (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput) :
    permutations f (Concrete.tweakableHash parameter domain payload) = blocks (32 + payload.length) := by
  rw [Concrete.tweakableHash, permutations_bind, permutations_oracleHash,
    permutations_pure, Nat.add_zero, tweakableHashInput_length]

theorem permutations_sequenceFin {α : Type} {n : Nat} (f : QueryImpl HashSpec Id)
    (computation : Fin n → OracleComp HashSpec α) :
    permutations f (sequenceFin computation) = ∑ i : Fin n, permutations f (computation i) := by
  induction n with
  | zero => simp [sequenceFin]
  | succ n ih =>
      rw [sequenceFin, permutations_bind]
      simp only [permutations_bind, permutations_pure, Nat.add_zero, ih, Fin.sum_univ_succ]

theorem permutations_chainWalk (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (chain : ChainIndex)
    (start steps : Nat) (value : Digest) (hsteps : start + steps ≤ chainLength - 1) :
    permutations f (chainWalk parameter lay tree leaf chain start steps value) = steps := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      rw [chainWalk, permutations_bind, dif_pos (by omega), permutations_tweakableHash,
        bytesLE_length, ih (by omega)]
      rfl

@[simp] theorem permutations_recoverChain (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (chain : ChainIndex) (digit : Digit) (value : Digest) :
    permutations f (recoverChain parameter lay tree leaf chain digit value) =
      chainLength - 1 - digit.val := by
  apply permutations_chainWalk
  have := digit.isLt
  omega

@[simp] theorem permutations_leafHash (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (endpoints : ChainIndex → Digest) :
    permutations f (leafHash parameter lay tree leaf endpoints) = 9 := by
  rw [leafHash, permutations_tweakableHash, leafPayload, digest_vector_length]
  rfl

theorem rootsPayload_length (tops : Coord → Digest × Digest) : (rootsPayload tops).length = 256 := by
  simp [rootsPayload, nodePayload, bytesLE_length, forestCoords]

/-- The encoding hashes the forest key and the counter: 32 + 256 + 4 = 292 bytes, 3 permutations. -/
@[simp] theorem permutations_encode (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : ForestKey) (counter : Counter) :
    permutations f (encode parameter lay tree leaf message counter) = 3 := by
  simp only [encode, permutations_bind, permutations_tweakableHash, List.length_append,
    rootsPayload_length, bytesLE_length, permutations_pure]
  rfl

theorem permutations_treeFold (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (path : Nat → Digest)
    (levels : Nat) (value : Digest) :
    permutations f (treeFold parameter lay tree leaf path levels value) = levels := by
  induction levels with
  | zero => rfl
  | succ levels ih =>
      rw [treeFold, permutations_bind, ih]
      dsimp only
      split <;> simp [permutations_tweakableHash, nodePayload, bytesLE_length, blocks]

theorem lut_sum (t : LutIdx) : ∑ i, (lut t i).val = codewordSum := Completeness.lut_sum t

section Coord

variable (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (index : Index) (c : Coord)

theorem permutations_forestWalk (s : SuperIdx) (j : SubIdx) (a : ChildIdx) (i : FChain)
    (start steps : Nat) (value : Digest) (hsteps : start + steps ≤ chainTop) :
    permutations f (forestWalk parameter index c s j a i start steps value) = steps := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      rw [forestWalk, permutations_bind, dif_pos (by omega), permutations_tweakableHash,
        bytesLE_length, ih (by omega)]
      rfl

@[simp] theorem permutations_forestRecoverChain (s : SuperIdx) (j : SubIdx) (a : ChildIdx) (i : FChain)
    (deficit : FPos) (value : Digest) :
    permutations f (forestRecoverChain parameter index c s j a i deficit value) = deficit.val := by
  apply permutations_forestWalk
  have := deficit.isLt
  simp only [chainTop] at this ⊢
  omega

@[simp] theorem permutations_childLeafHash (s : SuperIdx) (j : SubIdx) (a : ChildIdx) (ends : FChain → Digest) :
    permutations f (childLeafHash parameter index c s j a ends) = 1 := by
  rw [childLeafHash, permutations_tweakableHash, childPayload, digest_vector_length]
  rfl

@[simp] theorem permutations_childRecover (s : SuperIdx) (j : SubIdx) (a : ChildIdx) (t : LutIdx)
    (values : FChain → Digest) :
    permutations f (childRecover parameter index c s j a (lut t) values) = 6 := by
  rw [childRecover, permutations_bind, permutations_sequenceFin, permutations_childLeafHash]
  simp only [permutations_forestRecoverChain, lut_sum]
  rfl

theorem permutations_subFold (s : SuperIdx) (j : SubIdx) (a : ChildIdx) (path : Fin subHeight → Digest)
    (levels : Nat) (hlevels : levels ≤ subHeight) (value : Digest) :
    permutations f (subFold parameter index c s j a path levels value) = levels := by
  induction levels with
  | zero => rfl
  | succ levels ih =>
      rw [subFold, permutations_bind, ih (by omega), dif_pos (by omega)]
      dsimp only
      split <;> simp [permutations_tweakableHash, nodePayload, bytesLE_length, blocks]

theorem permutations_topFold (s : SuperIdx) (path : Fin topHeight → Digest)
    (levels : Nat) (hlevels : levels ≤ topHeight) (value : Digest) :
    permutations f (topFold parameter index c s path levels value) = levels := by
  induction levels with
  | zero => rfl
  | succ levels ih =>
      rw [topFold, permutations_bind, ih (by omega), dif_pos (by omega)]
      dsimp only
      split <;> simp [permutations_tweakableHash, nodePayload, bytesLE_length, blocks]

theorem superPayload_length (tops : SubIdx → Digest × Digest) : (superPayload tops).length = 64 := by
  simp [superPayload, nodePayload, bytesLE_length]

/-- One coordinate costs 20 permutations: per sub-tree 5 chain steps, 1 for the WOTS-key leaf and 2
folds; 1 for the tree leaf (96 bytes); 3 folds. -/
@[simp] theorem permutations_coordRecover (mark : CoordMark) (opening : CoordOpening) :
    permutations f (coordRecover parameter index c mark opening) = 20 := by
  rw [coordRecover, permutations_bind, permutations_sequenceFin, permutations_bind, superHash,
    permutations_tweakableHash, permutations_bind,
    permutations_topFold f parameter index c _ _ _ (by decide : topHeight - 1 ≤ topHeight)]
  simp only [permutations_bind, permutations_childRecover,
    permutations_subFold f parameter index c _ _ _ _ _ (by decide : subHeight - 1 ≤ subHeight),
    permutations_pure, superPayload_length, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul]
  rfl

end Coord

/-- The forest recovery costs 160 permutations: 20 per coordinate. The key is not hashed: the
encoding absorbs it. -/
@[simp] theorem permutations_forestRecover (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (index : Index) (marks : Coord → CoordMark) (opening : Coord → CoordOpening) :
    permutations f (forestRecover parameter index marks opening) = 160 := by
  rw [forestRecover, permutations_sequenceFin]
  simp only [permutations_coordRecover, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rfl

@[simp] theorem permutations_messageDigestCall (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (root : Digest) (message : Message)
    (randomness : Randomness) :
    permutations f (messageDigestCall parameter root message randomness) = 1 := by
  simp only [messageDigestCall, permutations_oracleHash, tweakableHashInput_length,
    messageDigestPayload, List.length_append, bytesLE_length]
  rfl

@[simp] theorem permutations_messageDigest (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (root : Digest) (message : Message) (randomness : Randomness) :
    permutations f (messageDigest parameter root message randomness) = 1 := by
  simp only [messageDigest, permutations_bind, permutations_messageDigestCall,
    permutations_pure]

theorem encode_valid (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (message : ForestKey)
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

/-- Recovery spends 81 permutations after an admissible encoding (3 for the encoding, 69 chain steps,
9 for the leaf), or 3 on rejection. -/
theorem permutations_otsLeaf (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (message : ForestKey)
    (counter : Counter) (values : ChainIndex → Digest) :
    permutations f (otsLeaf parameter lay tree leaf message counter values) =
      if (evalWithAnswerFn f (otsLeaf parameter lay tree leaf message counter values
        : OracleComp HashSpec (Option Digest))).isSome then 81 else 3 := by
  cases henc : evalWithAnswerFn f (encode parameter lay tree leaf message counter
      : OracleComp HashSpec (Option Encoding)) with
  | none =>
      simp only [otsLeaf, permutations_bind, permutations_encode, evalWithAnswerFn_bind,
        henc, evalWithAnswerFn_pure, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
        permutations_pure, Nat.add_zero]
  | some word =>
      have hvalid := encode_valid f parameter lay tree leaf message counter word henc
      simp only [otsLeaf, permutations_bind, permutations_encode, evalWithAnswerFn_bind,
        henc, evalWithAnswerFn_pure, Option.isSome_some, ↓reduceIte,
        permutations_sequenceFin, permutations_recoverChain, permutations_leafHash,
        permutations_pure, Nat.add_zero, Completeness.verification_chain_steps word hvalid]

attribute [local irreducible] otsLeaf encode sequenceFin chainWalk recoverChain leafHash
  forestRecover treeFold messageDigest

/-- The one actual tree layer costs 107 permutations, or 3 if its encoding is rejected. -/
theorem permutations_verifyLayers (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (index : Index) (signature : Signature) (message : ForestKey) :
    permutations f (verifyLayers parameter index signature numLayers message) =
      if (evalWithAnswerFn f (verifyLayers parameter index signature numLayers message
        : OracleComp HashSpec (Option Digest))).isSome then 107 else 3 := by
  rw [show numLayers = 0 + 1 from rfl, verifyLayers, dif_pos (by decide : 0 < numLayers)]
  simp only [permutations_bind, evalWithAnswerFn_bind]
  rw [permutations_otsLeaf]
  cases hleaf : evalWithAnswerFn f (otsLeaf parameter topLayer (treeIndexAt index topLayer)
      (leafIndexAt index topLayer) message (signature.layers topLayer).counter
      (signature.layers topLayer).chainValues : OracleComp HashSpec (Option Digest)) <;>
    simp only [topLayer] at hleaf
  all_goals simp only [hleaf, permutations_bind, permutations_treeFold,
    evalWithAnswerFn_bind, evalWithAnswerFn_pure, permutations_pure, Nat.add_zero,
    Option.isSome_some, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
  rfl

attribute [local semireducible] Concrete.verify

/-- Every accepted signature causes exactly 268 Keccak-f permutations in the verifier execution: 1 for
the digest, 160 for the forest and 107 for WOTS+C (with the 3-permutation encoding of the forest key)
and the path. -/
theorem verification_permutations (f : QueryImpl HashSpec Id) (pk : PublicKey)
    (message : Message) (signature : Signature)
    (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    permutations f (Concrete.verify pk message signature : OracleComp HashSpec Bool) = 268 := by
  rw [Concrete.verify, permutations_bind, permutations_messageDigest,
    permutations_bind, permutations_forestRecover, permutations_bind, permutations_verifyLayers]
  simp only [Concrete.verify, evalWithAnswerFn_bind] at haccept
  split at haccept
  next root hroot =>
    rw [hroot]
    rfl
  next => simp at haccept

/-- Malformed signatures cannot make verification exceed its accepted-signature cost. -/
theorem verification_permutations_le (f : QueryImpl HashSpec Id) (pk : PublicKey)
    (message : Message) (signature : Signature) :
    permutations f (Concrete.verify pk message signature : OracleComp HashSpec Bool) ≤ 268 := by
  rw [Concrete.verify, permutations_bind, permutations_messageDigest,
    permutations_bind, permutations_forestRecover, permutations_bind, permutations_verifyLayers]
  split <;> split <;> simp [permutations_pure]

end Sphincs.Cost
