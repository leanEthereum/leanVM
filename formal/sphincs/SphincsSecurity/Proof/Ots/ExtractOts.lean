import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Scheme.Code
import SphincsSecurity.Proof.Ots.ExtractChain
import SphincsSecurity.Proof.Ots.OneTime
/-!
# Extracting a one-time signature

If the verifier's half of a one-time signature returns the honest leaf, then either the chain values
the adversary supplied are the honest ones at its codeword's positions, or it hit the leaf value, or
it hit a chain value. The first alternative is what the incomparability of the code turns into "the
signature is the one the signer produced".
-/

namespace SphincsSecurity.Concrete

open OracleComp

variable (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
  (secret : LeafIndex → ChainIndex → Digest) (leaf : LeafIndex)

theorem leafOfNat_val : leafOfNat leaf.val = leaf := by
  ext
  simp [leafOfNat, Nat.mod_eq_of_lt leaf.isLt]

/-- The honest one-time public values at a leaf. -/
def honestEndpoints (chainIdx : ChainIndex) : Digest :=
  honestChain f parameter lay tree leaf chainIdx (secret leaf chainIdx) (chainLength - 1)

theorem honestEndpoints_def : honestEndpoints f parameter lay tree secret leaf
    = fun chainIdx => evalWithAnswerFn f
        (chainWalk parameter lay tree leaf chainIdx 0 (chainLength - 1) (secret leaf chainIdx)) :=
  rfl

/-- A hit at a leaf: something other than the honest endpoints hashing to the honest leaf. -/
def LeafHit (payload : HashInput) : Prop :=
  payload ≠ leafPayload (honestEndpoints f parameter lay tree secret leaf)
    ∧ truncateHash (f (tweakableHashInput parameter (.leaf lay tree leaf) payload))
      = honestNode f parameter lay tree secret 0 leaf.val

theorem honestNode_zero_eq_leafHash :
    honestNode f parameter lay tree secret 0 leaf.val
      = truncateHash (f (tweakableHashInput parameter (.leaf lay tree leaf)
          (leafPayload (honestEndpoints f parameter lay tree secret leaf)))) := by
  simp only [honestNode, treeNode_zero_eq, leafOfNat_val, evalWithAnswerFn_bind, leafHash,
    eval_tweakableHash, eval_oneTimePublicKey, honestEndpoints_def]

/-- **The one-time signature.** -/
theorem otsLeaf_extract (message : Digest) (counter : Counter) (values : ChainIndex → Digest)
    (codeword : Encoding)
    (hencode : evalWithAnswerFn f (encode parameter lay tree leaf message counter) = some codeword)
    (hleaf : evalWithAnswerFn f (otsLeaf parameter lay tree leaf message counter values)
      = some (honestNode f parameter lay tree secret 0 leaf.val)) :
    (∀ chainIdx, values chainIdx
        = honestChain f parameter lay tree leaf chainIdx (secret leaf chainIdx)
            (codeword chainIdx).val)
      ∨ LeafHit f parameter lay tree secret leaf
          (leafPayload fun chainIdx => walkValue f parameter lay tree leaf chainIdx
            (codeword chainIdx).val (values chainIdx) (chainLength - 1 - (codeword chainIdx).val))
      ∨ ∃ (chainIdx : ChainIndex) (offset : Nat)
          (hoffset : (codeword chainIdx).val + offset < chainLength - 1), offset < chainLength - 1
            - (codeword chainIdx).val
            ∧ ChainHit f parameter lay tree leaf chainIdx (secret leaf chainIdx)
                ((codeword chainIdx).val + offset) hoffset
                (walkValue f parameter lay tree leaf chainIdx (codeword chainIdx).val
                  (values chainIdx) offset) := by
  classical
  have hrecovered : evalWithAnswerFn f (leafHash parameter lay tree leaf
        (fun chainIdx => walkValue f parameter lay tree leaf chainIdx (codeword chainIdx).val
          (values chainIdx) (chainLength - 1 - (codeword chainIdx).val)))
      = honestNode f parameter lay tree secret 0 leaf.val := by
    simp only [otsLeaf, evalWithAnswerFn_bind, evalWithAnswerFn_pure, hencode,
      evalWithAnswerFn_sequenceFin] at hleaf
    simpa [walkValue, recoverChain] using hleaf
  by_cases hpayload : (leafPayload fun chainIdx => walkValue f parameter lay tree leaf chainIdx
      (codeword chainIdx).val (values chainIdx) (chainLength - 1 - (codeword chainIdx).val))
      = leafPayload (honestEndpoints f parameter lay tree secret leaf)
  · have hendpoints := TargetSum.leafPayload_injective hpayload
    have hchains : ∀ chainIdx : ChainIndex,
        values chainIdx = honestChain f parameter lay tree leaf chainIdx (secret leaf chainIdx)
            (codeword chainIdx).val
          ∨ ∃ (offset : Nat) (hoffset : (codeword chainIdx).val + offset < chainLength - 1),
              offset < chainLength - 1 - (codeword chainIdx).val
                ∧ ChainHit f parameter lay tree leaf chainIdx (secret leaf chainIdx)
                    ((codeword chainIdx).val + offset) hoffset
                    (walkValue f parameter lay tree leaf chainIdx (codeword chainIdx).val
                      (values chainIdx) offset) := by
      intro chainIdx
      have hdigit : (codeword chainIdx).val ≤ chainLength - 1 := by
        have := (codeword chainIdx).isLt
        simp only [chainLength, winternitzBits] at this ⊢
        omega
      refine chainWalk_extract f parameter lay tree leaf chainIdx (secret leaf chainIdx)
        (codeword chainIdx).val (values chainIdx) (chainLength - 1 - (codeword chainIdx).val)
        (by omega) ?_
      have := congrFun hendpoints chainIdx
      rw [show (codeword chainIdx).val + (chainLength - 1 - (codeword chainIdx).val)
        = chainLength - 1 by omega]
      exact this
    by_cases hall : ∀ chainIdx, values chainIdx
        = honestChain f parameter lay tree leaf chainIdx (secret leaf chainIdx)
            (codeword chainIdx).val
    · exact Or.inl hall
    · obtain ⟨chainIdx, hne⟩ := not_forall.mp hall
      rcases hchains chainIdx with hhonest | ⟨offset, hoffset, hlt, hhit⟩
      · exact absurd hhonest hne
      · exact Or.inr (Or.inr ⟨chainIdx, offset, hoffset, hlt, hhit⟩)
  · exact Or.inr (Or.inl ⟨hpayload, by
      rw [← hrecovered, leafHash, eval_tweakableHash]⟩)

end SphincsSecurity.Concrete
