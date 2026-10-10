import LeanxmssProofs.Hash

/-!
# Every specification input is a guest input

The maps of `Statement.lean` from the guest's words to the specification's bytes are onto, so the theorems about every
guest input cover every specification input. They are also one to one (`Statement.bytes_inj`).
-/

open Aeneas Aeneas.Std Result WP
open EthCryptographySpecs.Xmss EthCryptographySpecs.Xmss.Constants

namespace leanxmss.Proofs.Words

open Bytes Statement

/-- The words whose bytes are `l`, eight bytes a word. -/
def wordsOf (l : List UInt8) (n : Nat) : List U64 := List.ofFn fun i : Fin n => word (l.drop (8 * i.val))

theorem ofWords_wordsOf (n : Nat) : ∀ l : List UInt8, l.length = 8 * n → ofWords (wordsOf l n) = l := by
  induction n with
  | zero => intro l h; simp [wordsOf] at *; exact h
  | succ n ih =>
    intro l h
    simp only [wordsOf, List.ofFn_succ, Fin.val_zero, Nat.mul_zero, List.drop_zero, Fin.val_succ]
    rw [ofWords_cons, le_word l (by omega)]
    have : (List.ofFn fun i : Fin n => word (l.drop (8 * (i.val + 1)))) = wordsOf (l.drop 8) n := by
      simp only [wordsOf, List.drop_drop]
      congr; funext i; congr 2; ring
    rw [this, ih _ (by simp; omega), List.take_append_drop]

theorem wordsOf_length (l : List UInt8) (n : Nat) : (wordsOf l n).length = n := by simp [wordsOf]

/-- Bytes as the guest's words. -/
def arrayOf {m : Nat} (v : Vector UInt8 m) (n : Std.Usize) : Std.Array U64 n :=
  Std.Array.make n (wordsOf v.toList n.val) (wordsOf_length _ _)

theorem bytes_arrayOf {m : Nat} (v : Vector UInt8 m) (n : Std.Usize) (h : m = 8 * n.val) :
    bytes (arrayOf v n) m = v := by
  apply Vector.toList_inj.mp
  rw [bytes_toList _ _ h, arrayOf, Std.Array.make_val, ofWords_wordsOf _ _ (by simp [h])]

theorem digest_arrayOf (v : Digest) : Statement.digest (arrayOf v 2#usize) = v := bytes_arrayOf v _ rfl

theorem publicParam_arrayOf (v : PublicParam) : Statement.digest (arrayOf v 2#usize) = v := bytes_arrayOf v _ rfl

theorem digest_onto (v : Digest) : ∃ d, Statement.digest d = v := ⟨_, digest_arrayOf v⟩

theorem message_onto (v : Message) : ∃ m, Statement.message m = v := ⟨arrayOf v 4#usize, bytes_arrayOf v _ rfl⟩

theorem randomness_onto (v : Randomness) : ∃ r, Statement.randomness r = v :=
  ⟨arrayOf v 3#usize, bytes_arrayOf v _ rfl⟩

theorem epoch_onto (e : Epoch) : ∃ i, Statement.epoch i = e := ⟨⟨e.toBitVec⟩, rfl⟩

theorem publicKey_onto (pk : EthCryptographySpecs.Xmss.PublicKey) : ∃ p, Statement.publicKey p = pk :=
  ⟨{ merkle_root := arrayOf pk.merkleRoot 2#usize, public_param := arrayOf pk.publicParam 2#usize },
    by cases pk; simp only [Statement.publicKey, digest_arrayOf, publicParam_arrayOf]⟩

theorem signature_onto (s : EthCryptographySpecs.Xmss.Signature) : ∃ g, Statement.signature g = s := by
  refine ⟨{ chain_tips := Std.Array.make 42#usize (List.ofFn fun i : Fin 42 => arrayOf s.chainElements[i] 2#usize)
              (by simp)
            randomness := arrayOf s.randomness 3#usize
            merkle_proof := Std.Array.make 32#usize
              (List.ofFn fun i : Fin 32 => arrayOf s.merklePath[i] 2#usize) (by simp) }, ?_⟩
  cases s with
  | mk ce r mp =>
    unfold Statement.signature
    refine (EthCryptographySpecs.Xmss.Signature.mk.injEq _ _ _ _ _ _).mpr ⟨?_, ?_, ?_⟩
    · apply Vector.ext; intro i hi
      simp only [Vector.getElem_ofFn, Std.Array.make_val]
      rw [List.getD_eq_getElem _ _ (by simpa [Constants.V] using hi), List.getElem_ofFn]
      exact digest_arrayOf _
    · exact bytes_arrayOf r _ rfl
    · apply Vector.ext; intro i hi
      simp only [Vector.getElem_ofFn, Std.Array.make_val]
      rw [List.getD_eq_getElem _ _ (by simpa [LOG_LIFETIME] using hi), List.getElem_ofFn]
      exact digest_arrayOf _

end leanxmss.Proofs.Words
