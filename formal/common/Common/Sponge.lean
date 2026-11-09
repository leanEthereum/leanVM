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
permutation `π` of the 200-byte state, and `keccak256` is it over Keccak-f[1600] (`keccakF`,
transcribed from `keccak_f`); the `#guard`s below check it against the test vectors of `hash.rs`.

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

/-- The rate part of a state. -/
abbrev SpState.rate (s : SpState Dg E C) : Dg × E := s.1

/-- The capacity part of a state. -/
abbrev SpState.cap (s : SpState Dg E C) : C := s.2

section Xor

variable [XorOp Dg] [XorOp E] [XorCancel Dg] [XorCancel E]

/-- XOR on the rate is an involution in its second argument. -/
theorem rxor_cancel (a b : Dg × E) : rxor a (rxor a b) = b := by
  simp [rxor, XorCancel.xor_cancel]

/-- XOR on the rate is injective in its second argument. -/
theorem rxor_injective (a : Dg × E) : Function.Injective (rxor a) := fun b b' h ↦ by
  rw [← rxor_cancel a b, h, rxor_cancel]

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

/-- Absorbing a concatenation absorbs the first part, then the second. -/
theorem absorbAll_append {m : Type → Type} [Monad m] [LawfulMonad m]
    (π : SpState Dg E C → m (SpState Dg E C)) (s : SpState Dg E C) (bs bs' : List (Dg × E)) :
    absorbAll π s (bs ++ bs') = (absorbAll π s bs >>= fun y ↦ absorbAll π y bs') := by
  induction bs generalizing s with
  | nil => simp
  | cons B bs ih => simp [absorbAll_cons, ih]

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

/-- Padding is injective. -/
theorem pad_injective : Function.Injective P.pad := fun m m' h ↦ by
  have h1 := (P.unpad_eq_some_iff (P.pad m') m).mpr h
  have h2 := (P.unpad_eq_some_iff (P.pad m') m').mpr rfl
  rw [h1] at h2
  exact Option.some.inj h2

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

/-- The rate of Keccak-256 in bytes. -/
def keccakRate : ℕ := 136

/-- **Keccak-256 over a permutation `π` of the state**, in any monad: the sponge with rate 136
bytes, capacity 64 bytes, the Keccak padding, the all-zero initial state, and the first 32 bytes of
the final state as the digest. -/
def keccak256With {m : Type → Type} [Monad m] (π : KState → m KState) (msg : List UInt8) :
    m DigestBytes :=
  spongeWith keccakPadding KState.zero π msg

/-! ## Keccak-f[1600] -/

/-- The round constants of Keccak-f[1600] (`KECCAK_RC`). -/
def keccakRC : Array UInt64 := #[
  0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000,
  0x000000000000808B, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
  0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
  0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003,
  0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
  0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008]

/-- The rotation offsets of Keccak-f[1600] (`KECCAK_RHO`), by lane. -/
def keccakRho : Array UInt64 := #[
  0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14]

/-- Where lane `i = x + 5y` lands under π (`KECCAK_PI`). -/
def keccakPi (i : ℕ) : ℕ := i / 5 + 5 * ((2 * (i % 5) + 3 * (i / 5)) % 5)

/-- Rotate a lane left. -/
def rotl64 (x n : UInt64) : UInt64 := if n = 0 then x else (x <<< n) ||| (x >>> (64 - n))

/-- One round of Keccak-f[1600] on the 25 lanes, transcribed from `keccak_f`. -/
def keccakRound (a : Array UInt64) (rc : UInt64) : Array UInt64 := Id.run do
  let c : Array UInt64 := Array.ofFn fun x : Fin 5 ↦
    a[x.1]! ^^^ a[x.1 + 5]! ^^^ a[x.1 + 10]! ^^^ a[x.1 + 15]! ^^^ a[x.1 + 20]!
  let d : Array UInt64 := Array.ofFn fun x : Fin 5 ↦
    c[(x.1 + 4) % 5]! ^^^ rotl64 c[(x.1 + 1) % 5]! 1
  let a : Array UInt64 := Array.ofFn fun i : Fin 25 ↦ a[i.1]! ^^^ d[i.1 % 5]!
  let mut b : Array UInt64 := Array.replicate 25 0
  for i in [0:25] do
    b := b.set! (keccakPi i) (rotl64 a[i]! keccakRho[i]!)
  let a : Array UInt64 := Array.ofFn fun i : Fin 25 ↦
    let r := i.1 - i.1 % 5
    b[i.1]! ^^^ ((~~~ b[r + (i.1 % 5 + 1) % 5]!) &&& b[r + (i.1 % 5 + 2) % 5]!)
  return a.set! 0 (a[0]! ^^^ rc)

/-- Keccak-f[1600] on the 25 lanes: 24 rounds. -/
def keccakFLanes (a : Array UInt64) : Array UInt64 := keccakRC.foldl keccakRound a

/-- The 25 little-endian lanes of 200 bytes. -/
def lanesOfBytes (bs : List UInt8) : Array UInt64 :=
  Array.ofFn fun i : Fin 25 ↦ (List.range 8).foldr
    (fun j acc ↦ acc ||| ((bs.getD (8 * i.1 + j) 0).toUInt64 <<< (8 * j).toUInt64)) 0

/-- The 200 bytes of 25 little-endian lanes. -/
def bytesOfLanes (a : Array UInt64) : List UInt8 :=
  (List.range 200).map fun k ↦ (a[k / 8]! >>> (8 * (k % 8)).toUInt64).toUInt8

/-- **Keccak-f[1600]** on the byte state. -/
def keccakF (s : KState) : KState :=
  KState.ofBytes (bytesOfLanes (keccakFLanes (lanesOfBytes s.toBytes)))

/-- **Keccak-256**: the sponge over Keccak-f[1600]. -/
def keccak256 (msg : List UInt8) : DigestBytes := keccak256With (m := Id) keccakF msg

/-- Hexadecimal rendering of bytes, for the test vectors. -/
def hexOfBytes (bs : List UInt8) : String :=
  String.join (bs.map fun b ↦
    let h := "0123456789abcdef".toList
    String.ofList [h.getD (b.toNat / 16) '0', h.getD (b.toNat % 16) '0'])

/-- The bytes `0, 1, …, n - 1` (mod 256) of the test vectors. -/
def countingBytes (n : ℕ) : List UInt8 := (List.range n).map fun i ↦ i.toUInt8

end Common
