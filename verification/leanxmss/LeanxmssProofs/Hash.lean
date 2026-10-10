import LeanxmssProofs.Tweak

/-!
# The tweakable hash

The guest's `tweak_hash` is the specification's `tweakHash`, and a digest's first two words are its first 16 bytes.
-/

open Aeneas Aeneas.Std Result WP
open EthCryptographySpecs.Xmss EthCryptographySpecs.Xmss.Constants

namespace leanxmss.Proofs

open Bytes

@[simp] theorem hashWith_stream_ofStream (s : leanvm_guest.Stream) :
    leanvm_guest.HashWithClosure.stream (self := leanvm_guest.HashWithClosure.ofStream) s = s := rfl

@[simp] theorem hashWith_output_ofStream (s : leanvm_guest.Stream) (d : Std.Array U64 4#usize) :
    leanvm_guest.HashWithClosure.output (self := leanvm_guest.HashWithClosure.ofStream) s d = d := rfl

@[simp] theorem hashWith_stream_ofPair {C : Type} (r : C × leanvm_guest.Stream) :
    leanvm_guest.HashWithClosure.stream (self := leanvm_guest.HashWithClosure.ofPair) r = r.2 := rfl

@[simp] theorem hashWith_output_ofPair {C : Type} (r : C × leanvm_guest.Stream) (d : Std.Array U64 4#usize) :
    leanvm_guest.HashWithClosure.output (self := leanvm_guest.HashWithClosure.ofPair) r d = (d, r.1) := rfl

/-- A byte string as a `ByteArray`. -/
abbrev toBA (bs : List UInt8) : ByteArray := ⟨bs.toArray⟩

@[simp] theorem hash_length (b : ByteArray) : (Blake2s.hash b).toList.length = 32 := by simp

/-- The guest's `digest` of BLAKE2s: the first 16 bytes of the 32. -/
theorem digest_blake2s (bs : List UInt8) :
    ∃ d, leanxmss.digest (blake2s bs) = ok d ∧ ofWords d.val = (Blake2s.hash (toBA bs)).toList.take 16 := by
  refine ⟨Std.Array.make 2#usize [word ((Blake2s.hash (toBA bs)).toList.drop 0),
    word ((Blake2s.hash (toBA bs)).toList.drop 8)], ?_, ?_⟩
  · simp only [leanxmss.digest, blake2s, digestWords]
    simp [Std.Array.index_usize]
  · simp only [Std.Array.make_val, ofWords_cons, ofWords_nil, List.append_nil]
    rw [le_word _ (by simp), le_word _ (by simp)]
    simp only [List.drop_zero]
    rw [show (16 : Nat) = 8 + 8 from rfl, List.take_add]

/-- The specification's bytes of a guest digest are its words' bytes. -/
theorem digest_toList (d : Std.Array U64 2#usize) : (Statement.digest d).toList = ofWords d.val :=
  Statement.bytes_toList d DIGEST_LEN rfl

theorem packBytes_eq {n : Nat} (v : Vector UInt8 n) : packBytes v = toBA v.toList := by
  cases v; simp [packBytes, Vector.toList]

theorem packBytes_digest (d : Std.Array U64 2#usize) : packBytes (Statement.digest d) = toBA (ofWords d.val) := by
  rw [packBytes_eq, digest_toList]

/-- The same, for the digest taken as a public parameter. -/
theorem packBytes_publicParam (d : Std.Array U64 2#usize) :
    packBytes (n := PUBLIC_PARAM_LEN) (Statement.digest d) = toBA (ofWords d.val) :=
  packBytes_digest d

theorem take_digest (v : Vector UInt8 32) : (v.take DIGEST_LEN : Digest).toList = v.toList.take 16 := by
  erw [Vector.toList_take]; rfl

theorem tweakHash_toList (pp : PublicParam) (t : TweakType) (p i : UInt32) (payload : ByteArray) :
    (tweakHash pp t p i payload).toList = (Blake2s.hash (tweakInput pp t p i payload)).toList.take 16 := by
  unfold tweakHash tweakHashFull; exact take_digest _

/-- Two vectors are equal when their lists are. -/
theorem vector_eq_of_toList {n : Nat} {v w : Vector UInt8 n} (h : v.toList = w.toList) : v = w :=
  Vector.toList_inj.mp h

theorem toBA_append (a b : List UInt8) : toBA (a ++ b) = toBA a ++ toBA b := by
  apply ByteArray.ext
  simp

/-- `tweak_hash` is the specification's `tweakHash`, the payload being its words' bytes. -/
theorem tweak_hash_spec {N : Std.Usize} (pp : Std.Array U64 2#usize) (t : TweakType) (pos idx : Std.U32)
    (payload : Std.Array U64 N) :
    ∃ d, leanxmss.tweak_hash pp (tyByte t) pos idx payload = ok d ∧
      Statement.digest d = tweakHash (Statement.digest pp) t (u32 pos) (u32 idx) (toBA (ofWords payload.val)) := by
  obtain ⟨d, hd, hdb⟩ := digest_blake2s
    (ofWords [tweakWord0 (tyByte t) pos, tweakWord1 idx] ++ (ofWords pp.val ++ ofWords payload.val))
  refine ⟨d, ?_, ?_⟩
  · simp [leanxmss.tweak_hash, leanvm_guest.hash_with,
      leanxmss.tweak_hash.closure.Insts.CoreOpsFunctionFnOnceTupleMut5StreamTuple.call_once, tweak_ok,
      leanvm_guest.Stream.write, hd]
  · apply vector_eq_of_toList
    have hin : toBA (ofWords [tweakWord0 (tyByte t) pos, tweakWord1 idx] ++ (ofWords pp.val ++ ofWords payload.val))
        = tweakInput (Statement.digest pp) t (u32 pos) (u32 idx) (toBA (ofWords payload.val)) := by
      rw [tweakInput, packBytes_publicParam, packBytes_eq, ← tweak_bytes, toBA_append, toBA_append, ByteArray.append_assoc]
    rw [digest_toList, hdb, tweakHash_toList, hin]

end leanxmss.Proofs
