/-!
# `LeanSphincs.Constants`

The leanSPHINCS parameter set, `programs/leansphincs/guest/src/lib.rs` lines 30 to 72.
-/

namespace LeanSphincs.Constants

/-! ## Object sizes -/

/-- `n`: a hash value, 128 bits (`Digest`, lib.rs line 31). -/
def DIGEST_LEN : Nat := 16

/-- `P`, the per-key public parameter (`PublicParam`, lib.rs line 33). -/
def PUBLIC_PARAM_LEN : Nat := 16

/-- The per-signature randomizer the message digest is taken under (`Randomizer`, lib.rs line 35). -/
def RANDOMIZER_LEN : Nat := 16

/-- The message to sign: a 256-bit message hash (`Message`, lib.rs line 37). -/
def MESSAGE_LEN : Nat := 32

/-- A tweak: two little-endian 64-bit words (`tweak`, lib.rs line 268). -/
def TWEAK_LEN : Nat := 16

/-- An encoding counter in the specification's serialization: 4 bytes (`Signature::to_bytes`, lib.rs line 168). -/
def COUNTER_LEN : Nat := 4

/-! ## The one-time signature (WOTS+C) -/

/-- `w`: bits per chunk of a one-time codeword (lib.rs line 40). -/
def W : Nat := 3

/-- `2^w`: values on one hash chain (lib.rs line 42). -/
def CHAIN_LEN : Nat := 2 ^ W

/-- `v`: chunks, one hash chain each (lib.rs line 44). -/
def V : Nat := 42

/-- `T`: what every codeword sums to (lib.rs line 48). -/
def TARGET_SUM : Nat := 191

/-! ## The hypertree -/

/-- `d`: hypertree layers, numbered from the top (lib.rs line 50). -/
def D : Nat := 3

instance : NeZero D := ⟨by decide⟩

/-- `h_lay`: each layer's tree height (lib.rs line 52). -/
def HEIGHTS : Vector Nat D := #v[12, 7, 7]

/-- `h`: the total height (lib.rs line 54). -/
def H : Nat := 26

/-- The height of everything below each layer's top (`SUFFIX`, lib.rs line 212). -/
def SUFFIX : Vector Nat (D + 1) := #v[H, H - HEIGHTS[0], HEIGHTS[2], 0]

/-! ## The few-time signature (FORS+C) -/

/-- `a`: log2 of the leaves of one few-time tree (lib.rs line 56). -/
def A : Nat := 10

/-- `k`: indices the message digest picks, one per few-time tree (lib.rs line 58). -/
def K : Nat := 15

/-- Trees in a few-time forest: the last index is ground to zero, so its tree is dropped (lib.rs line 60). -/
def FTS_TREES : Nat := K - 1

/-! ## Serialized sizes -/

/-- A public key, `root | public_param` (`PUB_KEY_SIZE`, lib.rs line 63). -/
def PUB_KEY_SIZE : Nat := DIGEST_LEN + PUBLIC_PARAM_LEN

/-- One few-time opening: the secret and `a` siblings. -/
def FTS_OPENING_SIZE : Nat := DIGEST_LEN * (1 + A)

/-- One layer of height `height`: the counter's 4 bytes, `v` chain values and `height` siblings. -/
def layerSize (height : Nat) : Nat := COUNTER_LEN + DIGEST_LEN * (V + height)

/-- A signature in the specification's serialization, each counter in 4 bytes (`SIG_SIZE`, lib.rs line 65). -/
def SIG_SIZE : Nat :=
  RANDOMIZER_LEN + FTS_TREES * FTS_OPENING_SIZE + layerSize HEIGHTS[0] + layerSize HEIGHTS[1] + layerSize HEIGHTS[2]

/-! The guest's compile-time checks (lib.rs lines 69 to 72). -/

example : H = HEIGHTS[0] + HEIGHTS[1] + HEIGHTS[2] := by decide
example : W * V / 2 + 1 = 64 := by decide
example : PUB_KEY_SIZE = 32 ∧ SIG_SIZE = 4924 := by decide

end LeanSphincs.Constants
