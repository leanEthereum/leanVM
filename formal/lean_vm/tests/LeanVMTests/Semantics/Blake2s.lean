module

public import LeanVM.Semantics.Lemmas

/-!
# BLAKE2s compression and cell vectors

Kernel-checked vectors. `compress` is checked against RFC 7693 Appendix B (the BLAKE2s-256
computation of `"abc"`, including the working vector before and after the first round) and
against digests of CPython's `hashlib.blake2s`, which wraps the BLAKE2 authors' reference
implementation and exposes the tree-mode `last_node` flag.
The cell encoding is checked against the executor test `blake2s_computes_the_compression` of the
pinned leanVM at `a386121f`, whose cells `hash_flock::{compression, digest, metadata}` compute (the
test is unchanged at `127510d1` but for unwrapping the now fallible `execute`). The mutations at
the end show that every cell's top limb, the last-node flag, the flag words' order and the counter
are each bound.

Vector equalities are decided on the underlying word lists (`Vector.toList_inj`), because core's
`DecidableEq` for `Vector` is not exposed to module-system importers; full compressions use
`decide +kernel`, which reduces one where the elaborator's reducer exhausts its recursion budget.
-/

namespace LeanVMTests.Semantics.Blake2s

open LeanVM.Parameters LeanVM.Semantics

/-! ## RFC 7693 Appendix B: `BLAKE2s-256("abc")` -/

/-- The all-ones flag word. -/
def flag : UInt32 := 0xFFFFFFFF

/-- The initial chaining value of an unkeyed BLAKE2s-256: `iv` with the parameter word
`0x01010020` (digest length 32, fanout 1, depth 1) XORed into word 0 (RFC 7693 §2.8). -/
def paramIv : Vector UInt32 8 := iv.set 0 (iv[0] ^^^ 0x01010020)

/-- The single, zero-padded block of `"abc"`. -/
def abcBlock : Vector UInt32 16 := #v[0x00636261, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The digest `BLAKE2s-256("abc")` as words. -/
def abcDigest : Vector UInt32 8 :=
  #v[0x8c5e8c50, 0xe2147c32, 0xa32ba7e1, 0x2f45eb4e, 0x208b4537, 0x293ad69e, 0x4c9b994d, 0x82596786]

/-- `(i=0)`: the working vector with the counter `3` and the last-block flag in place. -/
example : Blake2s.initialState paramIv 3 flag 0 =
    #v[0x6B08E647, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A, 0x510E527F, 0x9B05688C, 0x1F83D9AB,
       0x5BE0CD19, 0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A, 0x510E527C, 0x9B05688C,
       0xE07C2654, 0x5BE0CD19] :=
  Vector.toList_inj.mp (by decide)

/-- `(i=1)`: the working vector after the first round. -/
example : Blake2s.round (Blake2s.initialState paramIv 3 flag 0) abcBlock sigma[0] =
    #v[0x16A3242E, 0xD7B5E238, 0xCE8CE24B, 0x927AEDE1, 0xA7B430D9, 0x93A4A14E, 0xA44E7C31,
       0x41D4759B, 0x95BF33D3, 0x9A99C181, 0x608A3A6B, 0xB666383E, 0x7A8DD50F, 0xBE378ED7,
       0x353D1EE6, 0x3BB44C6B] :=
  Vector.toList_inj.mp (by decide)

/-- `h[8]`: the digest. -/
example : compress paramIv abcBlock 3 flag 0 = abcDigest :=
  Vector.toList_inj.mp (by decide +kernel)

/-! ## `hashlib.blake2s` digests, with and without `last_node` -/

/-- The empty message: one all-zero block with counter `0`. -/
def emptyBlock : Vector UInt32 16 := #v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

example : compress paramIv emptyBlock 0 flag 0 =
    #v[0x307a2169, 0x94809079, 0xd02111e1, 0x7c4a3542, 0x48b6551f, 0x1ea5a12c, 0xfd0d251b,
       0xf9eed01e] :=
  Vector.toList_inj.mp (by decide +kernel)

example : compress paramIv emptyBlock 0 flag flag =
    #v[0x3c11fc24, 0x848cbe3d, 0x40703c49, 0x680dafae, 0xab7b3bcc, 0x49aecd0d, 0x704abbdb,
       0x365c9d25] :=
  Vector.toList_inj.mp (by decide +kernel)

example : compress paramIv abcBlock 3 flag flag =
    #v[0xe063d90c, 0x1b6b357a, 0x42f4d4c4, 0x4862616b, 0x2945048f, 0xa0e8e232, 0xd447538b,
       0x3fee2294] :=
  Vector.toList_inj.mp (by decide +kernel)

/-- The first block of the 65-byte message `0x00, 0x01, …, 0x40`. -/
def longBlock0 : Vector UInt32 16 :=
  #v[0x03020100, 0x07060504, 0x0b0a0908, 0x0f0e0d0c, 0x13121110, 0x17161514, 0x1b1a1918,
     0x1f1e1d1c, 0x23222120, 0x27262524, 0x2b2a2928, 0x2f2e2d2c, 0x33323130, 0x37363534,
     0x3b3a3938, 0x3f3e3d3c]

/-- Its second, one-byte block, zero-padded. -/
def longBlock1 : Vector UInt32 16 := #v[0x00000040, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- Two compressions: counter `64` with no flags, then counter `65` with the last-block flag. -/
example : compress (compress paramIv longBlock0 64 0 0) longBlock1 65 flag 0 =
    #v[0x94ee531b, 0x4b4ef3aa, 0xde489d15, 0x067f2c35, 0x0ea4d061, 0x0b5af9df, 0x09b43916,
       0x7244970e] :=
  Vector.toList_inj.mp (by decide +kernel)

example : compress (compress paramIv longBlock0 64 0 0) longBlock1 65 flag flag =
    #v[0x3fd35bba, 0x4a5edc81, 0x67981930, 0x8e45dd10, 0xb3a09522, 0x9eeaa8a8, 0x1d5b657f,
       0x83ba75bb] :=
  Vector.toList_inj.mp (by decide +kernel)

/-! ## The executor vector: `blake2s_computes_the_compression` (`cpu/mod.rs:808-836`) -/

def rustM0 : E :=
  E.ofLimbs (K.ofBits 0x0123456789abcdef) (K.ofBits 0xfedcba9876543210) 0x0000000000000000
def rustM1 : E :=
  E.ofLimbs (K.ofBits 0x1111222233334444) (K.ofBits 0x5555666677778888) 0x0000000000000000
def rustM2 : E :=
  E.ofLimbs (K.ofBits 0xdeadbeefcafebabe) (K.ofBits 0x0badf00d0badf00d) 0x0000000000000000
def rustM3 : E :=
  E.ofLimbs (K.ofBits 0x9999aaaabbbbcccc) (K.ofBits 0xddddeeeeffff0000) 0x0000000000000000
def rustCv0 : E := E.ofLimbs (K.ofBits 0x0000000000000007) 0x0000000000000000 0x0000000000000000
def rustCv1 : E := E.ofLimbs (K.ofBits 0x000000000000000b) 0x0000000000000000 0x0000000000000000
def rustMd : E :=
  E.ofLimbs (K.ofBits 0x0000000000000040) (K.ofBits 0x00000000ffffffff) 0x0000000000000000
def rustOut0 : E :=
  E.ofLimbs (K.ofBits 0x583fffe1350e2137) (K.ofBits 0x0de9e32629a5c508) 0x0000000000000000
def rustOut1 : E :=
  E.ofLimbs (K.ofBits 0xf1b0679a15df60bb) (K.ofBits 0x0228c8d4ed9b3a24) 0x0000000000000000

/-- The four message cells in operand order. -/
def rustM : Fin 4 → E := ![rustM0, rustM1, rustM2, rustM3]

/-- The words the executor fed to the compression (`hash_flock.rs:155-178`). -/
example : messageWords rustM =
    #v[0x89abcdef, 0x01234567, 0x76543210, 0xfedcba98, 0x33334444, 0x11112222, 0x77778888,
       0x55556666, 0xcafebabe, 0xdeadbeef, 0x0badf00d, 0x0badf00d, 0xbbbbcccc, 0x9999aaaa,
       0xffff0000, 0xddddeeee] :=
  Vector.toList_inj.mp (by decide)

example : cellWords rustCv0 ++ cellWords rustCv1 = #v[7, 0, 0, 0, 11, 0, 0, 0] :=
  Vector.toList_inj.mp (by decide)

example : unpackMetadata rustMd = (64, flag, 0) := by decide

/-- The output cells hold the compression it computed. -/
example : cellWords rustOut0 ++ cellWords rustOut1 =
    #v[0x350e2137, 0x583fffe1, 0x29a5c508, 0x0de9e326, 0x15df60bb, 0xf1b0679a, 0xed9b3a24,
       0x0228c8d4] :=
  Vector.toList_inj.mp (by decide)

/-- The nine cells satisfy the relation. -/
example : CompressCells rustM rustCv0 rustCv1 rustOut0 rustOut1 rustMd := by decide +kernel

/-! ## Arbitrary flag words in the pinned opcode compression -/

/-- Pinned `flock::hash::blake2s_compress` accepts these distinct, non-Boolean `u32` flag words.
The corresponding Rust lane asserts the same eight output words. -/
def rawFlagsMd : E := E.ofLimbs (K.ofBits 64) (K.ofBits 0x9abcdef012345678) 0
def rawFlagsOut0 : E := E.ofLimbs (K.ofBits 0xd16af0a6e9a85163) (K.ofBits 0xba5be3252edb90ff) 0
def rawFlagsOut1 : E := E.ofLimbs (K.ofBits 0x3ce6b68fbdc018d2) (K.ofBits 0x8c0e7b0bbea90143) 0

example : unpackMetadata rawFlagsMd = (64, 0x12345678, 0x9abcdef0) := by decide
example : CompressCells rustM rustCv0 rustCv1 rawFlagsOut0 rawFlagsOut1 rawFlagsMd :=
  by decide +kernel

/-- Changing only the last-node word cannot retain the raw-flag output. -/
example : ¬ CompressCells rustM rustCv0 rustCv1 rawFlagsOut0 rawFlagsOut1
    (E.ofLimbs (K.ofBits 64) (K.ofBits 0x0000000012345678) 0) := by decide +kernel

example : wordsCell (cellWords rustOut0) = rustOut0 := wordsCell_cellWords (by decide)

/-! ## Mutations -/

/-- An output cell with a nonzero top limb is rejected although its words are right. -/
example : ¬ CompressCells rustM rustCv0 rustCv1 rustOut0
    (E.ofLimbs (K.ofBits 0xf1b0679a15df60bb) (K.ofBits 0x0228c8d4ed9b3a24) 1) rustMd := by
  decide +kernel

/-- So is a message cell with a nonzero top limb, whose words are unchanged
(`blake2s_requires_zero_third_limb`, `cpu/mod.rs:919-931` at `a386121f`; removed at `127510d1`,
where the executor returns `Fault::NotCanonical` instead, `cpu/execute.rs:883-889`). -/
example : ¬ CompressCells ![E.ofLimbs (K.ofBits 0x0123456789abcdef) (K.ofBits 0xfedcba9876543210) 1, rustM1, rustM2,
    rustM3] rustCv0 rustCv1 rustOut0 rustOut1 rustMd := by
  decide +kernel

/-- The chaining-value and metadata cells have the same canonicality requirement. -/
example : ¬ CompressCells rustM (E.ofLimbs (K.ofBits 7) 0 1) rustCv1 rustOut0 rustOut1 rustMd :=
  by decide +kernel
example : ¬ CompressCells rustM rustCv0 rustCv1 rustOut0 rustOut1
    (E.ofLimbs (K.ofBits 64) (K.ofBits 0x00000000ffffffff) 1) := by decide +kernel

/-- A single wrong output bit is rejected. -/
example : ¬ CompressCells rustM rustCv0 rustCv1 rustOut0
    (E.ofLimbs (K.ofBits 0xf1b0679a15df60ba) (K.ofBits 0x0228c8d4ed9b3a24) 0) rustMd := by
  decide +kernel

/-- The two flag words are not interchangeable: `final = 0`, `last_node = 0xFFFFFFFF`. -/
example : ¬ CompressCells rustM rustCv0 rustCv1 rustOut0 rustOut1
    (E.ofLimbs (K.ofBits 0x0000000000000040) (K.ofBits 0xffffffff00000000) 0) := by
  decide +kernel

/-- The last-node flag is not ignored: setting it as well changes the compression. -/
example : ¬ CompressCells rustM rustCv0 rustCv1 rustOut0 rustOut1
    (E.ofLimbs (K.ofBits 0x0000000000000040) (K.ofBits 0xffffffffffffffff) 0) := by
  decide +kernel

/-- The counter is limb 0; zeroing it changes the compression. -/
example : ¬ CompressCells rustM rustCv0 rustCv1 rustOut0 rustOut1
    (E.ofLimbs 0x0000000000000000 (K.ofBits 0x00000000ffffffff) 0) := by
  decide +kernel

end LeanVMTests.Semantics.Blake2s
