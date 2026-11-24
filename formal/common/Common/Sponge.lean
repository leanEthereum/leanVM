module

public import Common.Model
public import Common.Defs

@[expose] public section

/-!
# The sponge construction and Keccak-256

The sponge construction of Bertoni, Daemen, Peeters and Van Assche ("On the indifferentiability
of the sponge construction", EUROCRYPT 2008) over a permutation `π` of a state split into an
outer part, the *rate*, and an inner part, the *capacity*. A message is padded into rate-sized
blocks; each block is XORed into the rate and the state is permuted; the output is a prefix of
the rate of the final state.

The abstract sponge here (`absorbAll`, `spongeWith`) works over states `(Dg × E) × C`: the rate
is `Dg × E`, of which the output is the first component `Dg`, and the capacity is `C`. The
padding is any injective map from messages to nonempty block lists with a decoder
(`Padding`). The monad `m` is arbitrary: `π` may be a pure function (`Id`), a query to a random
permutation oracle (`OracleComp`), or any other effect.

The concrete instance is Keccak-256, as leanVM computes it (`crates/verifier/src/hash.rs`,
`keccak_hash`): the state is 200 bytes, the 25 little-endian 64-bit lanes of Keccak-f[1600]; the
rate is its first 136 bytes, the capacity its last 64 bytes (512 bits); the digest is its first 32
bytes; the padding is `0x01 ‖ 0^* ‖ 0x80` (Keccak's domain byte `0x01`, not SHA-3's `0x06`), merged
into `0x81` when one byte is left in the last block. `keccak256With π` is this sponge over any
permutation `π` of the 200-byte state.

The padding is injective with a computable decoder (`keccakPadding`): the decoder strips the
padding and accepts exactly the padded messages.
-/

set_option linter.unusedSectionVars false

namespace Common

/-! ## Exclusive-or with cancellation -/

/-- An exclusive-or such that `a ^^^ (a ^^^ b) = b`: absorbing a block into a state is
invertible, and the block is recovered from the states before and after. -/
class XorCancel (α : Type) [XorOp α] : Prop where
  /-- XOR with `a` is an involution. -/
  xor_cancel : ∀ a b : α, a ^^^ (a ^^^ b) = b

/-- Byte vectors XOR bytewise. -/
instance (n : ℕ) : XorCancel (Vector UInt8 n) where
  xor_cancel a b := by
    apply Vector.ext
    intro i hi
    change (Vector.zipWith (· ^^^ ·) a (Vector.zipWith (· ^^^ ·) a b))[i] = b[i]
    simp only [Vector.getElem_zipWith]
    rw [← UInt8.xor_assoc, UInt8.xor_self, UInt8.zero_xor]

/-! ## The abstract sponge -/

variable {Dg E C : Type}

section Xor

variable [XorOp Dg] [XorOp E] [XorCancel Dg] [XorCancel E]

/-- XOR on the rate is an involution in its second argument. -/
theorem rxor_cancel (a b : Dg × E) : rxor a (rxor a b) = b := by
  simp [rxor, XorCancel.xor_cancel]

/-- Absorbing `blockTo s x` into `s` gives `x` when `s` and `x` share their capacity. -/
theorem absorb_blockTo {s x : SpState Dg E C} (h : s.2 = x.2) : absorb s (blockTo s x) = x := by
  obtain ⟨⟨a, b⟩, c⟩ := s
  obtain ⟨⟨a', b'⟩, c'⟩ := x
  simp only at h
  subst h
  simp only [absorb, blockTo]
  rw [rxor_cancel]

/-- The block absorbed into `s` is recovered from the result. -/
theorem blockTo_absorb (s : SpState Dg E C) (B : Dg × E) : blockTo s (absorb s B) = B :=
  rxor_cancel s.1 B

/-- Absorbing keeps the capacity. -/
@[simp] theorem absorb_cap (s : SpState Dg E C) (B : Dg × E) : (absorb s B).2 = s.2 := rfl

/-- Absorbing is injective in the block. -/
theorem absorb_injective (s : SpState Dg E C) : Function.Injective (absorb s) := by
  intro B B' h
  rw [← blockTo_absorb s B, h, blockTo_absorb]

@[simp] theorem absorbAll_nil {m : Type → Type} [Monad m] (π : SpState Dg E C → m (SpState Dg E C))
    (s : SpState Dg E C) : absorbAll π s [] = pure s := rfl

theorem absorbAll_cons {m : Type → Type} [Monad m] (π : SpState Dg E C → m (SpState Dg E C))
    (s : SpState Dg E C) (B : Dg × E) (bs : List (Dg × E)) :
    absorbAll π s (B :: bs) = (π (absorb s B) >>= fun y ↦ absorbAll π y bs) := rfl

end Xor

namespace Padding

variable {Msg Blk : Type}

/-- The laws of a padding: the decoder recognises exactly the paddings, and a padded message has
at least one block. -/
class Lawful (P : Padding Msg Blk) : Prop where
  /-- The decoder recognises exactly the paddings. -/
  unpad_eq_some_iff : ∀ β m, P.unpad β = some m ↔ P.pad m = β
  /-- A padded message has at least one block. -/
  pad_ne_nil : ∀ m, P.pad m ≠ []

variable (P : Padding Msg Blk) [P.Lawful]

/-- The decoder recognises exactly the paddings. -/
theorem unpad_eq_some_iff (β : List Blk) (m : Msg) : P.unpad β = some m ↔ P.pad m = β :=
  Lawful.unpad_eq_some_iff β m

/-- A padded message has at least one block. -/
theorem pad_ne_nil (m : Msg) : P.pad m ≠ [] := Lawful.pad_ne_nil m

/-- The decoder inverts the padding. -/
@[simp] theorem unpad_pad (m : Msg) : P.unpad (P.pad m) = some m :=
  (P.unpad_eq_some_iff _ m).mpr rfl

end Padding

variable [XorOp Dg] [XorOp E] [XorCancel Dg] [XorCancel E]

/-! ## Keccak-256's padding -/

/-- The bytes of a block made of 136 bytes are those bytes. -/
theorem KBlock.toBytes_ofBytes {bs : List UInt8} (h : bs.length = 136) :
    (KBlock.ofBytes bs).toBytes = bs := by
  apply List.ext_getElem
  · simp [KBlock.toBytes, KBlock.ofBytes, h]
  intro i h1 h2
  simp only [KBlock.toBytes, KBlock.ofBytes] at h1 ⊢
  rw [List.getElem_append]
  split_ifs with hi
  · simp only [Vector.toList_ofFn, List.getElem_ofFn]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
  · simp only [Vector.toList_ofFn, List.getElem_ofFn, List.length_ofFn]
    simp only [Vector.toList_ofFn, List.length_ofFn] at hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
    congr 1
    omega

/-- Splitting a list whose length is a multiple of 136 into blocks and back gives the list. -/
theorem blocksToBytes_toBlocks (bs : List UInt8) (h : bs.length % 136 = 0) :
    blocksToBytes (toBlocks bs) = bs := by
  induction bs using toBlocks.induct with
  | case1 => simp [toBlocks, blocksToBytes]
  | case2 b bs ih =>
    rw [toBlocks]
    simp only [blocksToBytes, List.flatMap_cons] at ih ⊢
    have hlen : 136 ≤ (b :: bs).length := by
      have : 0 < (b :: bs).length := by simp
      omega
    rw [KBlock.toBytes_ofBytes (by simp only [List.length_take]; omega),
      ih (by simp only [List.length_drop]; omega), List.take_append_drop]

/-- The padded bytes have a length that is a positive multiple of 136. -/
theorem keccakPadBytes_length (msg : List UInt8) :
    (keccakPadBytes msg).length = 136 * (msg.length / 136 + 1) := by
  unfold keccakPadBytes
  split_ifs with h
  · simp; omega
  · simp; omega

/-- Stripping the padding recovers the message. -/
theorem stripPad_keccakPadBytes (msg : List UInt8) : stripPad (keccakPadBytes msg) = msg := by
  unfold keccakPadBytes
  split_ifs with h
  · simp [stripPad]
  · have hz : ∀ k, List.dropWhile (· = (0 : UInt8)) (List.replicate k 0 ++ (1 :: msg.reverse)) =
        1 :: msg.reverse := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => simp [List.replicate_succ, ih]
    simp only [stripPad, List.append_assoc, List.cons_append, List.nil_append,
      List.reverse_append, List.reverse_cons, List.reverse_nil, List.reverse_replicate]
    simp [hz]

/-- Padded block lists are never empty. -/
theorem keccakPad_ne_nil (msg : List UInt8) : keccakPad msg ≠ [] := by
  unfold keccakPad
  have hlen := keccakPadBytes_length msg
  cases h : keccakPadBytes msg with
  | nil => rw [h] at hlen; simp at hlen
  | cons b bs => rw [toBlocks]; exact List.cons_ne_nil _ _

/-- The decoder inverts the padding. -/
theorem keccakUnpad_keccakPad (msg : List UInt8) : keccakUnpad (keccakPad msg) = some msg := by
  have hb : blocksToBytes (keccakPad msg) = keccakPadBytes msg :=
    blocksToBytes_toBlocks _ (by rw [keccakPadBytes_length]; omega)
  simp [keccakUnpad, hb, stripPad_keccakPadBytes]

/-- **The Keccak-256 padding's laws.** -/
instance : keccakPadding.Lawful where
  unpad_eq_some_iff β m := by
    constructor
    · intro h
      simp only [keccakPadding, keccakUnpad] at h
      split_ifs at h with hp
      · cases h; exact hp
    · rintro rfl
      exact keccakUnpad_keccakPad m
  pad_ne_nil := keccakPad_ne_nil

/-! ## Keccak-256 -/

/-- **Keccak-256 over a permutation `π` of the state**, in any monad: the sponge with rate 136
bytes, capacity 64 bytes, the Keccak padding, the all-zero initial state, and the first 32 bytes of
the final state as the digest. -/
def keccak256With {m : Type → Type} [Monad m] (π : KState → m KState) (msg : List UInt8) :
    m DigestBytes :=
  spongeWith keccakPadding KState.zero π msg

end Common
