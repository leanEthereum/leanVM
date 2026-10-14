import Whir.SpongefishSessionAdapter
import Whir.PublicMerkleProgram

/-! Hand-ported positive-PoW byte adapter for the current source pin in
SpongefishSessionAdapter. The trial uses ordinary BLAKE2s-256, not the old
Scalar24 nonce role. Nonces are prover messages: their search is not verifier
challenge entropy. This module preserves state after a failed work predicate;
proof reads, poisoning, EOF and compiler correspondence remain separate. -/
namespace Whir.SpongefishPowAdapter
open Concrete FiatShamirGame DuplexRefinement DuplexModeGame PublicMerkleLog

set_option autoImplicit false

def nonceBytes (nonce : UInt64) : List Byte := List.ofFn (ByteCodec.encodeNat 8 nonce.toNat)
def trialTag : Fin 8 → Byte := fun i =>
  ⟨("FS-POW-1".toUTF8[i.val]!).toNat % 256,Nat.mod_lt _ (by decide)⟩
def trialBytes (challenge : Digest32) (nonce : UInt64) : List Byte :=
  List.ofFn challenge ++ nonceBytes nonce ++ List.replicate 16 0 ++ List.ofFn trialTag

theorem nonceBytes_length (nonce : UInt64) : (nonceBytes nonce).length = 8 := by simp [nonceBytes]
theorem trialBytes_length (challenge : Digest32) (nonce : UInt64) :
    (trialBytes challenge nonce).length = 64 := by simp [trialBytes,nonceBytes_length]

def firstWord (digest : Digest32) : UInt64 :=
  ByteCodec.decodeK (fun i => digest ⟨i.val,by omega⟩)

def clears (bits : Fin 64) (digest : Digest32) : Bool :=
  decide (bits.val ≤ (firstWord digest).toBitVec.clz.toNat)

/-- Counting leading zeroes is equivalent to the exact first-word threshold,
including zero difficulty and the all-zero digest. No whole-digest big-endian
interpretation is substituted for the native little-endian first word. -/
theorem leading_zero_threshold (word : BitVec 64) (bits : Fin 64) :
    bits.val ≤ word.clz.toNat ↔ word.toNat < 2^(64-bits.val) := by
  constructor
  · intro enough
    exact (BitVec.toNat_lt_two_pow_sub_clz (x := word)).trans_le
      (Nat.pow_le_pow_of_le (by decide) (by omega))
  · intro small
    by_contra missing
    have less : word.clz.toNat < bits.val := by omega
    have nonzero : word ≠ 0#64 := by
      intro zero
      have count := BitVec.clz_eq_iff_eq_zero.mpr zero
      have := congrArg BitVec.toNat count
      norm_num at this
      omega
    have lower := BitVec.two_pow_sub_clz_le_toNat_of_ne_zero (x := word) (by decide) nonzero
    have exponent : 64-bits.val ≤ 64-1-word.clz.toNat := by omega
    have monotone := Nat.pow_le_pow_of_le (a := 2) (by decide) exponent
    omega

theorem clears_threshold (bits : Fin 64) (digest : Digest32) :
    clears bits digest = true ↔ (firstWord digest).toNat < 2^(64-bits.val) := by
  simp only [clears,decide_eq_true_eq]
  exact leading_zero_threshold _ _

def trial (C : PrimitiveOracle) (challenge : Digest32) (nonce : UInt64) : Digest32 :=
  hash C (trialBytes challenge nonce)

/-- `bits` carries the source's MAX_BITS guard. Zero difficulty performs neither
squeeze nor nonce absorption. Positive difficulty draws raw32 and absorbs the
LE u64 before checking its predicate, so a failed predicate retains that state. -/
def check (C : PrimitiveOracle) (s : State) (bits : Fin 64) (nonce : UInt64) :
    Except Error (State × Bool) :=
  if bits.val = 0 then .ok (s,true) else
    match squeeze (compressionOf C) s 32 with
    | .error e => .error e
    | .ok (t,bytes) =>
      let challenge : Digest32 := fun i => bytes[i.val]?.getD 0
      .ok (absorb (compressionOf C) t (nonceBytes nonce),clears bits (trial C challenge nonce))

/-- The standalone verifier predicate consumes the ordinary boxed hash fold
directly. Its trial wrapper alone can be eta-expanded once per first-word byte. -/
private def checkStored (C : PrimitiveOracle) (s : State) (bits : Fin 64)
    (nonce : UInt64) : Except Error (State × Bool) :=
  if bits.val = 0 then .ok (s,true) else
    match squeeze (compressionOf C) s 32 with
    | .error e => .error e
    | .ok (t,bytes) =>
      let challenge : Digest32 := fun i => bytes[i.val]?.getD 0
      PublicMerkleProgram.withHashStored C (trialBytes challenge nonce) (fun digest =>
        .ok (absorb (compressionOf C) t (nonceBytes nonce),clears bits digest))

@[csimp] private theorem check_stored : check = checkStored := by
  funext C s bits nonce
  simp only [check,checkStored,PublicMerkleProgram.withHashStored_eq,trial]

#print axioms check_stored

theorem zero_no_event (C : PrimitiveOracle) (s : State) (nonce : UInt64) :
    check C s ⟨0,by decide⟩ nonce = .ok (s,true) := rfl

theorem positive_checked (C : PrimitiveOracle) (s t : State) (bits : Fin 64)
    (nonce : UInt64) (challenge : Digest32) (positive : bits.val ≠ 0)
    (draw : squeeze (compressionOf C) s 32 = .ok (t,List.ofFn challenge)) :
    check C s bits nonce =
      .ok (absorb (compressionOf C) t (nonceBytes nonce),clears bits (trial C challenge nonce)) := by
  simp only [check,positive,↓reduceIte,draw]
  have decoded : (fun i : Fin 32 => (List.ofFn challenge)[i.val]?.getD 0) = challenge := by
    funext i
    simp only [List.getElem?_ofFn,dite_eq_left i.isLt,Option.getD_some]
  rw [decoded]

theorem nonce_absorb_cursor (C : PrimitiveOracle) (t : State) (nonce : UInt64) :
    (absorb (compressionOf C) t (nonceBytes nonce)).consumed = 0 := by
  apply absorb_nonempty_cursor
  intro empty
  have := congrArg List.length empty
  simp [nonceBytes_length] at this

theorem raw_challenge_cursor (C : PrimitiveOracle) (s t : State) (challenge : Digest32)
    (draw : squeeze (compressionOf C) s 32 = .ok (t,List.ofFn challenge)) :
    t.consumed = s.consumed + 32 := (squeeze_exact_cursor (compressionOf C) s t 32 _ draw).1

#print axioms leading_zero_threshold
#print axioms clears_threshold
#print axioms zero_no_event
#print axioms positive_checked
#print axioms nonce_absorb_cursor
#print axioms raw_challenge_cursor
end Whir.SpongefishPowAdapter
