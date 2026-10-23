import LeanVM.Protocol.Verifier

/-!
# Verifier helper tests: differential against the Python verifier

Every expected value below was printed by `python-verifier/verifier.py` at leanVM
`127510d14c98ade4e8a97646c44fa7f1ff5e752d` (CPython, the verifier imported as a module) on
inputs drawn from the word generator `fw`, which the driver mirrors exactly. Compiled checks
(`#guard`): `E` multiplication does not reduce in the kernel from module files.

Covered: `powers`, `eq_kernel`, `multilinear_eval` (on `E` and on lifted `K` tables), `eq_eval`,
`dot`, `index_mle`, `poly_eval`, `_gpow`, `lagrange_weights`, `lagrange_interpolate`,
`_window_denominator`, `PHI`, `FIXED_CHALLENGES`, `log2_ceil`, `_selector_point`,
`_subspace_roots`, `_induced_weight`, `_ext_row`, `_enforced_sum`, `_ring_weight`, the ring map's
Frobenius coefficients and `_phi`, `derive_config` on all 56 admissible pairs, `stack_offsets`,
`Placement.stack_point` and `eq_above`, `blake2s_row_values` and `blake2s_bilinear` on full
`2^14`-entry weight vectors, `build_layout` on a sample bytecode and sizes (stack log-size,
every placement, every bus block's shape and flushed tuple at a sample row), `bus_layout` of the
three sides, the tables' widths, global bases, constraint counts, count columns and
`_jump_constraints`, the public input's halves, and the Fiat-Shamir seed
(`Transcript.__init__` with the IV preimage).
-/

namespace LeanVMTests.Protocol.Verifier.Helpers

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Protocol.Blake2sHash

/-! ## Inputs, as the driver draws them -/

/-- The driver's 64-bit word generator. -/
def fw (k lane : ℕ) : ℕ :=
  ((k + 1) * 0x9E3779B97F4A7C15 + lane * 0xD1B54A32D192ED03 + 0x632BE59BD9B4E019) % 2 ^ 64

/-- An `E` element from its three limbs. -/
def e (c0 c1 c2 : ℕ) : E := E.ofLimbs (K.ofBits c0) (K.ofBits c1) (K.ofBits c2)

/-- A `K` word. -/
def k (c : ℕ) : K := K.ofBits c

/-- The driver's `fe(k)`. -/
def fe (i : ℕ) : E := e (fw i 0) (fw i 1) (fw i 2)

/-- `fe(a), …, fe(a + n - 1)`. -/
def fes (a n : ℕ) : List E := (List.range n).map fun i ↦ fe (a + i)

/-- A lifted `K` table of sixteen entries. -/
def kTable : List E := (List.range 16).map fun i ↦ ofK (K.ofBits (fw i 5))

/-- Three lifted `K` rows of four words. -/
def kRows : List (List E) :=
  (List.range 3).map fun q ↦ (List.range 4).map fun j ↦ ofK (K.ofBits (fw (10 * q + j) 7))

/-- A placement with a low window. -/
def samplePlacement : Placement := { vars := 3, index := 0b1011001, low := 2 }

/-- The row sums of `blake2s_row_values` on `K`-valued column weights, and `blake2s_bilinear` with
`K`-valued row weights. -/
def bilinearProbe : E × E × E :=
  let cw := (List.range (2 ^ 14)).map fun i ↦ eOfNat (fw i 7)
  let rw := (List.range (2 ^ 14)).map fun i ↦ eOfNat (fw i 8)
  let rows := blake2sRowValues cw
  (sumE rows.1.toList, sumE rows.2.toList, blake2sBilinear (fe 110) rw cw)

/-- The sample bytecode: 32 words, so `log_bytecode = 1`. -/
def sampleBytecode : List K := (List.range 32).map fun i ↦ K.ofBits (fw i 9)

/-- The sample row counts: `xor, mul, set, deref, jump, blake2s`. The driver announced their
log-heights `2, 1, 1, 2, 2, 3`, which these give. -/
def sampleRows : List ℕ := [3, 2, 2, 4, 3, 5]

/-- The sample layout, at memory log-size 16. -/
def sampleLayout : Layout :=
  (buildLayout sampleBytecode 16 sampleRows).getD ⟨0, 0, [], [], [], [], [], 0, []⟩

/-- Each block's log-height, owner, arity, and its flushed tuple at the row `fe(200 + i)`,
batched by powers of `fe 300`. -/
def blockProbe (blocks : List BusBlock) : List (ℕ × ℕ × ℕ × E) :=
  blocks.map fun b ↦ (b.logRows, b.owner, b.coordinates.length,
    dot ((powers (fe 300) 16).take b.coordinates.length)
      (b.coordinates.map (·.evaluate fun i ↦ fe (200 + i))))

/-- A side's bus layout: its depth and every placement's size and offset. -/
def busProbe (frameworkLogRows : List ℕ) (blocks : List BusBlock) : ℕ × List (ℕ × ℕ) :=
  let bl := busLayout frameworkLogRows blocks
  (bl.depth, (bl.framework ++ bl.tables).map fun q ↦ (q.vars, q.index))

/-- The sample public input: the 32 bytes `fw(i, 10) mod 256`. -/
def samplePublicInput : Digest :=
  let b := fun i ↦ (fw i 10 % 256).toUInt8
  Vector.ofFn fun j : Fin 8 ↦ leWord (b (4 * j)) (b (4 * j + 1)) (b (4 * j + 2)) (b (4 * j + 3))

/-! ## Constants and conventions -/

#guard yE = y
#guard gen = ofK (K.ofBits 2)
#guard (buildLayout sampleBytecode 16 sampleRows).isSome
#guard sampleLayout.tableLogHeights = [2, 1, 1, 2, 2, 3]
#guard sampleLayout.push.all fun b ↦ b.rows == sampleRows.getD b.owner 0
#guard [16, 15, 17, 1, 0, 2 ^ 20].map log2Strict = [some 4, none, none, some 0, none, some 20]
#guard flockKSkip = 6 ∧ logPacking = 6 ∧ flockNumLincheckRounds = 8 ∧ qflockSlotBits = 8

/- Every column name the tables look up exists (the Python's `_cols` assertion). -/
#guard (blake2sCells.all fun (cell, operand, _) ↦
  [operand, "cnt_" ++ cell, cell ++ "_lo", cell ++ "_hi"].all (blake2sColumns.contains ·))
#guard blake2sSlots.all fun name? ↦ (name?.map (blake2sColumns.contains ·)).getD true

/-! ## `build_layout` rejects what the Python rejects -/

/- A bytecode length that is not a power of two; one shorter than `2^BUS_BITS`. -/
#guard (buildLayout (sampleBytecode.take 24) 16 sampleRows).isNone
#guard (buildLayout (sampleBytecode.take 8) 16 sampleRows).isNone
/- The memory window `[16, 32]`. -/
#guard (buildLayout sampleBytecode 15 sampleRows).isNone
#guard (buildLayout sampleBytecode 33 sampleRows).isNone
/- The row cap `2^32`, and no `BLAKE2S` floor. -/
#guard (buildLayout sampleBytecode 16 [2 ^ 32 + 1, 2, 2, 4, 3, 5]).isNone
#guard (buildLayout sampleBytecode 16 [2 ^ 32, 2, 2, 4, 3, 5]).isSome
#guard (buildLayout sampleBytecode 16 [3, 2, 2, 4, 3, 0]).isSome
/- Not one row count per table. -/
#guard (buildLayout sampleBytecode 16 [3, 2, 2, 4, 3, 5, 0]).isNone

/-! ## `derive_config` outside the window -/

#guard (deriveConfig 14 1).isNone ∧ (deriveConfig 29 1).isNone
#guard (deriveConfig 20 0).isNone ∧ (deriveConfig 20 5).isNone

/-! ## Python values -/

#guard (powers (fe 1) 6) =
    [(e 0x1 0x0 0x0), (e 0x9f9ad90ed849d843 0x71502341a9dcc546 0x43056d747b6fb249),
     (e 0x8d41cdea3c9b1743 0xa53215ff9e6ed6ea 0x2669efafa20976fe),
     (e 0xa4fb932c8c6005f5 0x12e1091c975015a3 0xfc6d64707160a1e0),
     (e 0xc23af15976790af3 0x29d9da9d0e15fe53 0xc526b9a545adaa4a),
     (e 0x2d1ea809ca35b247 0x46ab55d456449e8f 0x3d619d6840f9ce6d)]

#guard (eqKernel [fe 2, fe 3, fe 4]) =
    [(e 0x7487318548636ffa 0x104be15054f9c970 0x9838154b1a7217e),
     (e 0xe19ce463199bbeab 0x3d97c60a62a2663f 0xbe54a33bf161b600),
     (e 0x1e37011ff0590bf5 0x417ccde534ddbc7e 0x9f56dd4601895e41),
     (e 0xf16d92c2f7889627 0x27567ad1253a2ab4 0x352a2589b800efb7),
     (e 0x8801dc0423f74bd4 0x4a42f1c429ad748d 0x3b75987221284df6),
     (e 0xc113c563a4d14ae9 0xca21c02ab78766b2 0xf3d6dafa1bea70fb),
     (e 0xdf63be56cc597b82 0x14f2418a60ae40d8 0x4c9c234d6bbc1c97),
     (e 0xec30e10a1d56363d 0xdf67e00ad9386b62 0x9994bb65a8310712)]

#guard (multilinearEval ((List.range 8).map fe) [fe 10, fe 11, fe 12]) =
    (e 0xbca1256ff477f64b 0x625ffcf5f0075399 0x1af46b1ee1f7415d)

#guard (multilinearEval kTable (fes 13 4)) =
    (e 0x34ffd6cb8e8988f1 0xca8604399a32af81 0xfb923ada57162173)

#guard (eqEval [fe 20, fe 21, fe 22] [fe 23, fe 24, fe 25]) =
    (e 0xc0f2b18b0773cd0f 0x326bbc9c17ea3be0 0x1b82601b0a7f7e26)

#guard (dot [fe 26, fe 27, fe 28] [fe 29, fe 30, fe 31]) =
    (e 0xbdb04ddfb1e0a46e 0xeb3249201502d601 0x585ea508c62854b7)

#guard (indexMle [fe 32, fe 33, fe 34, fe 35]) =
    (e 0x132494cb3bc463b2 0x3624558675c28ed0 0x9111de27755aab6)

#guard (polyEval [fe 40, fe 41, fe 42, fe 43, fe 44] (fe 45)) =
    (e 0x135b962c7eb72a4d 0xa624b34b0383f4b8 0xdcf22a0b0f465e2e)

#guard (Verifier.gpow 5) =
    (e 0x20 0x0 0x0)

#guard (Verifier.gpow (2 ^ 32 - 1)) =
    (e 0xae3111b3bb81428f 0x0 0x0)

#guard (lagrangeWeights 64 (fe 50)) =
    [(e 0x590237b8a25a222d 0xfb881c9dda8e4704 0xc2d79a780fd7c0bb),
     (e 0x34dee223e72545ac 0x371d8d7913e5a112 0x89fffb0d44a9385),
     (e 0x80088b2a867b9b80 0xab182f1edb2a40c4 0xbc075029b164e959),
     (e 0x943d53242d20365a 0x5587274dc9d260be 0x7b7b0ae4b2644270),
     (e 0xe2eb87a1c2a562c8 0x6bdc50fb54e2ec8a 0xf76bcdfa44fa810b),
     (e 0x575c165d85f625a9 0xc80070412e33b655 0x177b67bf4b83f51e),
     (e 0xaaae8ce014fc06ec 0x7690e47e36943d16 0x2a38c7d51796b078),
     (e 0x89d73106fb7c3c2f 0xc527b315fa6b1d64 0xa2eb85c9e97e683e),
     (e 0x4db63aabff0e731d 0x3999eff9969cabef 0x2b0683fe193446cd),
     (e 0xd0e198415b7106b5 0x418f9a7257311249 0x2d18160b7433d7a4),
     (e 0x683941a57adffd41 0x3b1765317e67b13d 0x5b1535158202dc56),
     (e 0x4e2155dad67af8fd 0xff9e5dc394f60d20 0x2a3a6af9579719e),
     (e 0x500095fa27b35ca6 0xd98dca4be1bcf1f2 0x85537ff67c747f28),
     (e 0x67e28391b79ba745 0xa8b74f7788e0754b 0xf2e212d148c59a91),
     (e 0xd0d3f58525ad7fc6 0xda16c31ebafce06a 0x62637e0603b6cfe5),
     (e 0xe12f4648aacefd6f 0x5b493ff99542a9 0xcfc0aac4bb4a5c9d),
     (e 0x77c224d43e67c39c 0x6f248cd18be8a6b7 0x85c2f068ca29e05),
     (e 0xd51e06b4dd1461dd 0x84d87b09a75ac707 0x2bcd66da3e42ca27),
     (e 0xac7eda70f63fd1d5 0x8cc79eb76cf22c8c 0x7135f7f286aa753),
     (e 0xc3c2aaf6ab4f64d4 0xd259974fa901b850 0x96d860bee0ba80ab),
     (e 0xbbd65998b31b0ed 0x913807aeaf3328e 0xdf21e5694ab8154f),
     (e 0x18b05933cc9955ed 0xed5cbe7f3cb46bb8 0x799bde32ff7562c7),
     (e 0xbbf3e371b866e2c9 0x568ebb2b098f5e8b 0xe668e4ccb6b58147),
     (e 0xdbf4f0735c375898 0xed26e7ea2ab80b95 0xff0864843ac2ebf5),
     (e 0x85d2fb8e1836315e 0xacdefd985faa8bef 0xa942e067642e68cf),
     (e 0x24ff52518eb0dd8d 0x795a4c97bec169e0 0xcf1c4d1376c72e67),
     (e 0x50528f872ed2c82a 0x9322b9f0359200eb 0x6a0c4f8cb187485e),
     (e 0x6762b545b16ee442 0xfc00e7d1697de928 0x837f59223afc849d),
     (e 0x1b6a959850b5eff5 0x8bbd57f04c893aa2 0x5e6a28ed04611384),
     (e 0xacc805dc5c95a1e3 0x7a7645581c8e9ed5 0xb0824e4af650eb06),
     (e 0x866f288941c37085 0x2c55310219935b1 0x4da9925e077a998b),
     (e 0x49ac02ee325a9d32 0xe8c798ebdef3b560 0xc4e5e688b1d7ff05),
     (e 0x7aba10c87fef9e73 0x958cc6be5b4bd520 0x9dedcef462987144),
     (e 0x461126b034909146 0x64b4c2f25c855fe5 0x13bfc33b4027faac),
     (e 0xc5de62e45f8df5b7 0x8187646aedc53b54 0x42ea206f45ca91e0),
     (e 0xe5fdd14e830e7ae5 0x12afc8ebbfa0f071 0x2bdda95930cd76bb),
     (e 0xd024f5d6effc45e1 0xe809277296770a7b 0x5fac33ed9a13bac6),
     (e 0xce5618cc114736fd 0xda4c831e905867a9 0x8ef457beff79bc05),
     (e 0xe2bfabc91caa8d0d 0x3b8829ad52fda21f 0x40676409e40efc96),
     (e 0x887621d6ebad006f 0x55099969ef695d5b 0x10c5f88765e2f0e0),
     (e 0x940f1b728c52af5a 0xc3c22d74b522bf31 0x4fb215f29d8e1e3),
     (e 0x15316ee238e15943 0xf3810f4c542ad9b4 0x9f4ed1203cba875b),
     (e 0xbf27bb455c74ea73 0xe761cfdf6b49f3c7 0xa17f06d9c9853fc3),
     (e 0x406d89d06360966f 0xb3cf2e44b0160b77 0xafa78894ec325dc1),
     (e 0x361d741a8005efb1 0xe630a64b613e78f9 0xc8494b43565ccff6),
     (e 0xc53b17792e3a5fd 0x6a8ef08e729854ed 0xf006f014b08d21a2),
     (e 0x19a0633105b15ee5 0x8ed2440394331450 0xefd2cc7d4d3b605a),
     (e 0xfe72c4dcad8995f3 0x69a30f1473aad6d2 0x4d901821c50fdd4e),
     (e 0x7ae12dc134813a2d 0x7f4773bd05cffc6f 0xa301f098c5a9f382),
     (e 0xdc802abba56a1913 0xa2ba04c8a759db 0x70cb1a635c336984),
     (e 0x2f307d98d04d3158 0xd790b9ff43cc9aab 0xe8933e6c63c4332c),
     (e 0x29c2c356b9f6d3d6 0x6cb6bd3116ae9c99 0x5289f63659128063),
     (e 0xb804aa9e2d5d38b2 0x48f64aa0686d183a 0x16fe46e7d8bddd13),
     (e 0x84d7b3d2a3afb917 0xf718e4985818e8fa 0x8b4f33018fc3b6eb),
     (e 0xb9c67f41f55567d4 0x8485b7a220e66648 0x57ce9c82a389a439),
     (e 0x2e2b190fb0d91b68 0x44c78c736e9d600 0xd1a2faff036fd50f),
     (e 0xbf1b6c51eeb56a5c 0x142af1e6951e26c8 0x8a932400473e9e3b),
     (e 0x31a423c2f6ced622 0x257aac52da230ea3 0x2ed1c0666b0c13d3),
     (e 0x9dd143d00e9e4487 0xa91561dac91fa298 0x9f5403b32b45316b),
     (e 0x108246a9f53abe5 0x174dd532c2a6a7be 0x42cc213c11d599ff),
     (e 0xfecd88ad9904362d 0x8564a1fe130fa225 0x785067c8de13c667),
     (e 0x47368dba87c63fe4 0x77be8b6d16831bbb 0xca1f4d6c89a3383c),
     (e 0xf2b05e5acaaeb6c1 0xfd018db15330bfb7 0xdebdf6bbcb440cf2),
     (e 0x9b3b144cfbd23056 0x34a286dbee5c2291 0xb9e4a827235b10d)]

#guard (lagrangeInterpolate 128 ((List.range 128).map fe) (fe 51)) =
    (e 0xb22695663f81016e 0x9808d38c41fb2d74 0xbebb7b6c5f3efb26)

#guard (windowDenominator 64) =
    (e 0xa1e83c9e0d85cb4f 0x0 0x0)

#guard (windowDenominator 128) =
    (e 0x33ce8beddc8a657 0x0 0x0)

#guard ((List.range 128).map phi) =
    [(e 0x0 0x0 0x0), (e 0x1 0x0 0x0), (e 0x33ce8beddc8a656 0x0 0x0),
     (e 0x33ce8beddc8a657 0x0 0x0), (e 0x512620375ed2a108 0x0 0x0),
     (e 0x512620375ed2a109 0x0 0x0), (e 0x521ac889831a075e 0x0 0x0),
     (e 0x521ac889831a075f 0x0 0x0), (e 0xc9e636090aafc01 0x0 0x0), (e 0xc9e636090aafc00 0x0 0x0),
     (e 0xfa28bde4d625a57 0x0 0x0), (e 0xfa28bde4d625a56 0x0 0x0), (e 0x5db84357ce785d09 0x0 0x0),
     (e 0x5db84357ce785d08 0x0 0x0), (e 0x5e84abe913b0fb5f 0x0 0x0),
     (e 0x5e84abe913b0fb5e 0x0 0x0), (e 0xba4f3cd82801769c 0x0 0x0),
     (e 0xba4f3cd82801769d 0x0 0x0), (e 0xb973d466f5c9d0ca 0x0 0x0),
     (e 0xb973d466f5c9d0cb 0x0 0x0), (e 0xeb691cef76d3d794 0x0 0x0),
     (e 0xeb691cef76d3d795 0x0 0x0), (e 0xe855f451ab1b71c2 0x0 0x0),
     (e 0xe855f451ab1b71c3 0x0 0x0), (e 0xb6d15fb8b8ab8a9d 0x0 0x0),
     (e 0xb6d15fb8b8ab8a9c 0x0 0x0), (e 0xb5edb70665632ccb 0x0 0x0),
     (e 0xb5edb70665632cca 0x0 0x0), (e 0xe7f77f8fe6792b95 0x0 0x0),
     (e 0xe7f77f8fe6792b94 0x0 0x0), (e 0xe4cb97313bb18dc3 0x0 0x0),
     (e 0xe4cb97313bb18dc2 0x0 0x0), (e 0xba26e7904adb4a47 0x0 0x0),
     (e 0xba26e7904adb4a46 0x0 0x0), (e 0xb91a0f2e9713ec11 0x0 0x0),
     (e 0xb91a0f2e9713ec10 0x0 0x0), (e 0xeb00c7a71409eb4f 0x0 0x0),
     (e 0xeb00c7a71409eb4e 0x0 0x0), (e 0xe83c2f19c9c14d19 0x0 0x0),
     (e 0xe83c2f19c9c14d18 0x0 0x0), (e 0xb6b884f0da71b646 0x0 0x0),
     (e 0xb6b884f0da71b647 0x0 0x0), (e 0xb5846c4e07b91010 0x0 0x0),
     (e 0xb5846c4e07b91011 0x0 0x0), (e 0xe79ea4c784a3174e 0x0 0x0),
     (e 0xe79ea4c784a3174f 0x0 0x0), (e 0xe4a24c79596bb118 0x0 0x0),
     (e 0xe4a24c79596bb119 0x0 0x0), (e 0x69db4862da3cdb 0x0 0x0), (e 0x69db4862da3cda 0x0 0x0),
     (e 0x35533f6bf129a8d 0x0 0x0), (e 0x35533f6bf129a8c 0x0 0x0), (e 0x514ffb7f3c089dd3 0x0 0x0),
     (e 0x514ffb7f3c089dd2 0x0 0x0), (e 0x527313c1e1c03b85 0x0 0x0),
     (e 0x527313c1e1c03b84 0x0 0x0), (e 0xcf7b828f270c0da 0x0 0x0), (e 0xcf7b828f270c0db 0x0 0x0),
     (e 0xfcb50962fb8668c 0x0 0x0), (e 0xfcb50962fb8668d 0x0 0x0), (e 0x5dd1981faca261d2 0x0 0x0),
     (e 0x5dd1981faca261d3 0x0 0x0), (e 0x5eed70a1716ac784 0x0 0x0),
     (e 0x5eed70a1716ac785 0x0 0x0), (e 0x467698598926dc01 0x0 0x0),
     (e 0x467698598926dc00 0x0 0x0), (e 0x454a70e754ee7a57 0x0 0x0),
     (e 0x454a70e754ee7a56 0x0 0x0), (e 0x1750b86ed7f47d09 0x0 0x0),
     (e 0x1750b86ed7f47d08 0x0 0x0), (e 0x146c50d00a3cdb5f 0x0 0x0),
     (e 0x146c50d00a3cdb5e 0x0 0x0), (e 0x4ae8fb39198c2000 0x0 0x0),
     (e 0x4ae8fb39198c2001 0x0 0x0), (e 0x49d41387c4448656 0x0 0x0),
     (e 0x49d41387c4448657 0x0 0x0), (e 0x1bcedb0e475e8108 0x0 0x0),
     (e 0x1bcedb0e475e8109 0x0 0x0), (e 0x18f233b09a96275e 0x0 0x0),
     (e 0x18f233b09a96275f 0x0 0x0), (e 0xfc39a481a127aa9d 0x0 0x0),
     (e 0xfc39a481a127aa9c 0x0 0x0), (e 0xff054c3f7cef0ccb 0x0 0x0),
     (e 0xff054c3f7cef0cca 0x0 0x0), (e 0xad1f84b6fff50b95 0x0 0x0),
     (e 0xad1f84b6fff50b94 0x0 0x0), (e 0xae236c08223dadc3 0x0 0x0),
     (e 0xae236c08223dadc2 0x0 0x0), (e 0xf0a7c7e1318d569c 0x0 0x0),
     (e 0xf0a7c7e1318d569d 0x0 0x0), (e 0xf39b2f5fec45f0ca 0x0 0x0),
     (e 0xf39b2f5fec45f0cb 0x0 0x0), (e 0xa181e7d66f5ff794 0x0 0x0),
     (e 0xa181e7d66f5ff795 0x0 0x0), (e 0xa2bd0f68b29751c2 0x0 0x0),
     (e 0xa2bd0f68b29751c3 0x0 0x0), (e 0xfc507fc9c3fd9646 0x0 0x0),
     (e 0xfc507fc9c3fd9647 0x0 0x0), (e 0xff6c97771e353010 0x0 0x0),
     (e 0xff6c97771e353011 0x0 0x0), (e 0xad765ffe9d2f374e 0x0 0x0),
     (e 0xad765ffe9d2f374f 0x0 0x0), (e 0xae4ab74040e79118 0x0 0x0),
     (e 0xae4ab74040e79119 0x0 0x0), (e 0xf0ce1ca953576a47 0x0 0x0),
     (e 0xf0ce1ca953576a46 0x0 0x0), (e 0xf3f2f4178e9fcc11 0x0 0x0),
     (e 0xf3f2f4178e9fcc10 0x0 0x0), (e 0xa1e83c9e0d85cb4f 0x0 0x0),
     (e 0xa1e83c9e0d85cb4e 0x0 0x0), (e 0xa2d4d420d04d6d19 0x0 0x0),
     (e 0xa2d4d420d04d6d18 0x0 0x0), (e 0x461f4311ebfce0da 0x0 0x0),
     (e 0x461f4311ebfce0db 0x0 0x0), (e 0x4523abaf3634468c 0x0 0x0),
     (e 0x4523abaf3634468d 0x0 0x0), (e 0x17396326b52e41d2 0x0 0x0),
     (e 0x17396326b52e41d3 0x0 0x0), (e 0x14058b9868e6e784 0x0 0x0),
     (e 0x14058b9868e6e785 0x0 0x0), (e 0x4a8120717b561cdb 0x0 0x0),
     (e 0x4a8120717b561cda 0x0 0x0), (e 0x49bdc8cfa69eba8d 0x0 0x0),
     (e 0x49bdc8cfa69eba8c 0x0 0x0), (e 0x1ba700462584bdd3 0x0 0x0),
     (e 0x1ba700462584bdd2 0x0 0x0), (e 0x189be8f8f84c1b85 0x0 0x0),
     (e 0x189be8f8f84c1b84 0x0 0x0)]

#guard (fixedChallenges) =
    [(e 0x501d2518e3ce5a55 0x0 0x0), (e 0xff054c3f7cef0cca 0x0 0x0),
     (e 0x155755ffb7202002 0x0 0x0), (e 0x35cfd1ab784e4bf6 0x12fa45aa9a1825d1 0xb996e3c1cf34ac24),
     (e 0x63ec67547b58ffa3 0xe188dfcb58207451 0xbba7df26ed9c8ffc),
     (e 0xc9350a318893eeae 0xe5e0ec902c5238d6 0xe8bd2e5755425f21),
     (e 0x369b37ae52f8330e 0xbd7a06f7a48ae87 0x122bad6c647e24d2)]

#guard ([1, 2, 3, 5, 64, 65, 2 ^ 20].map log2Ceil) =
    [0, 1, 2, 3, 6, 7, 20]

#guard (selectorPoint 13 6) =
    [(e 0x1 0x0 0x0), (e 0x0 0x0 0x0), (e 0x1 0x0 0x0), (e 0x1 0x0 0x0), (e 0x0 0x0 0x0),
     (e 0x0 0x0 0x0)]

#guard (subspaceRoots 12) =
    [(e 0x1 0x0 0x0), (e 0x6 0x0 0x0), (e 0x168 0x0 0x0), (e 0x1166880 0x0 0x0),
     (e 0x11616686880801b 0x0 0x0), (e 0x726b6e3c6e39234e 0x0 0x0),
     (e 0x796adf34d64462c2 0x0 0x0), (e 0xf1060866be6fa9c 0x0 0x0),
     (e 0x6a06f1b0a76acb05 0x0 0x0), (e 0xd2d14e471a7186d9 0x0 0x0),
     (e 0x6d55ab94bb5f9605 0x0 0x0), (e 0xd08c5570c6423a2a 0x0 0x0), (e 0xa0ca298b954731 0x0 0x0)]

#guard (inducedWeight 5 [3, 17, 30, 0] (powers (fe 60) 4) [fe 61, fe 62, fe 63, fe 64, fe 65]) =
    (e 0x2ac3fadca39d4b81 0x1629ae443f03334e 0x4f97f27d36b81fbf)

#guard (extRow ((List.range 6).map fun i ↦ K.ofBits (fw i 6))) =
    [(e 0xeba31c864270ea40 0x89da963fc1bb6655 0x28120ff94105e26a),
     (e 0xc64989b2c0505e7f 0x6481036c3f9ada94 0x2b87d25bee556a9)]

#guard (enforcedSum kRows [fe 66, fe 67] [fe 68, fe 69, fe 70]) =
    (e 0xda0d62a8fab09447 0xf78fdc7451a4bb0a 0x2bb794332b986985)

#guard (ringWeight (fes 71 4) (fes 75 4) (fes 100 64)) =
    (e 0x6f0eb6aeec94b739 0xa58b39c32b7e22f6 0x7a7dd4c24feb966a)

#guard (ringCoefficients (fes 80 6)) =
    [(e 0x1 0x0 0x0), (e 0x89cec9ec9cba8f27 0x5b84141f6e4d7c2a 0x2d395e523fe0692d),
     (e 0xeb9750331d701312 0xbd4c9a65ef030015 0x8f01e498c095ed18),
     (e 0x1a7c40727dd8414f 0x2f9d6f2f3bb4ff59 0x1f7361f312626e20),
     (e 0x4d5fd6799e2596fd 0x1f1520ac6fb88400 0xf0ca6adf414b7103),
     (e 0xb2a07f1e3c8bbe4 0x60c454fe8a2f953a 0xd700c89eddae366a),
     (e 0xae8c650e35408c75 0xa3752cd2a81171d2 0xb8373defb3dc0c0f),
     (e 0xe54deb03304a8ec2 0x63ff83c454d2f505 0x8c748a0177b012c9),
     (e 0xaf285cc01edb1ae8 0x80dda6f2f06e07eb 0x5292f125c200f4ee),
     (e 0x45a9dd1b0887cf79 0xaa23719a2697304 0x1636533a0a0b2647),
     (e 0x2c3f81b450a4ee56 0xb4c13f22c80edd7f 0x5936ca6bc197d291),
     (e 0xf09b7a73a2037a1d 0x50ea044e8029fa1d 0x34223b534589f155),
     (e 0x73bdefcf33b76ad8 0x61dff0d68cf064eb 0xf5e4caaa31c98d2a),
     (e 0x5c3d12d4f4b870da 0xb905c99cb580d034 0x2ab61b719c9a8e02),
     (e 0xf4c379a61a521ad5 0x431b95c70a4cff67 0x45714d9dd1754a3),
     (e 0xe830de7397c0b57b 0xd7b6d466cc022395 0x71ba4c36c31c9f6),
     (e 0x10f0e3069f909ed3 0xe2a62d3971238bd6 0xb45b776c42b678d9),
     (e 0x94ecc3a46a0ae180 0xc1291ed04076ed69 0xd75bbc119be4b11c),
     (e 0x12a02e5408fa03b7 0xf574adf1305b70df 0x5a4469247528dd8b),
     (e 0x6c686912cd5496 0x5f589f78b7f3710f 0x934d979a24b70235),
     (e 0xb5756470f7895ae0 0x95e99b2f511e6c64 0x65955f68772f5828),
     (e 0x868cc50d867c8d0b 0x56a5c25c87443c52 0x6e7654977b5475d7),
     (e 0xf9ad4b17204401eb 0xa04d55a7b59654ab 0x75699c8cc9af9824),
     (e 0xf86178ca66b168d2 0x625eadd785948d5f 0xc8383a3ba7053b93),
     (e 0x19267c799cdcbcbc 0x308902d334dae1ab 0x68b9e488bab285a0),
     (e 0x733e727b41c7930e 0x9346028f3c57a53e 0xb36ac3078aa750db),
     (e 0xb2fc17c003b5c0ea 0x4b98761a1cb0bf73 0x8bc53228089fc5b1),
     (e 0xe25ac417ae6335bb 0xa593fd70a5ea6600 0xecedc965790e356),
     (e 0xe7f79ef1fb1b818f 0xf1d37fb39d85318c 0xfe615821cd511531),
     (e 0xa92f8648a40142ce 0x21c0cc6b0d52457e 0x6612b789222a7511),
     (e 0xce8a3ce2f3c3cfd7 0xab7e14a2e761f6ca 0x7744aaa7e2b25568),
     (e 0x6f239b04edc29ac1 0xd2259a0f29920eec 0x84362804534c18a8),
     (e 0x72b9694d204622be 0x446eb37ff1d90fc1 0x1623fdb2c36bfcc4),
     (e 0x39b05ea96f358f31 0x7bd4217b65c741d1 0xea5bccaedbc5839b),
     (e 0xbb80e13021735db6 0x9c2f96dbd8191b42 0x2d01b4431368a1d3),
     (e 0x95891fe3b06fb6d7 0xbb004038c8cc87c1 0x84fb5a682502a9f8),
     (e 0xb39aeb2b4eec67b5 0xed5db671df042983 0x517f86b97ce90ea7),
     (e 0x29c536f8b59db1bf 0xbb9aad369381f224 0x64ec782b6068e442),
     (e 0x26388d1ee006b87a 0x5a8b7e83eac7cbe7 0xedd36f3ae6bbeb10),
     (e 0xf5f6c39299d61870 0x23d74893e970712c 0xf1d31aac027f430e),
     (e 0xb3a3624183354c2b 0xb10e40a508738a3d 0xea362b2627b798c2),
     (e 0x4ecca651cb5ccdb8 0x784932bb7c69c4b7 0x8a6863be430d25b7),
     (e 0xeabb13a4ac61f2ff 0x3328c70e401c28fc 0xd3f15588cd4e5741),
     (e 0xdeffa1631ea291d6 0x4fe8a4e14f94ef12 0x9d20c94c7917b4f0),
     (e 0x36fb18cacf186a62 0x97a0774dda76cda9 0x27ac7b2dc0083b9f),
     (e 0x49ea5d8cd342e17f 0x9ca74798d6c20e15 0xa451a87214f60ca0),
     (e 0x11a3c2b31ec81702 0x605af12b4ea740e9 0x84ab236cc314f425),
     (e 0xf9a06f0ff05ef00c 0x992957c88bebe9ab 0xb1c06fe1a43ba046),
     (e 0xb106eb65df8351f4 0x8a1bbb40ae6c777f 0x60a7052f59c62bad),
     (e 0x6ea5f06f50685bd9 0x87d63d7bc3a29f89 0x5780a2078b34f30c),
     (e 0xdf24e6d1aad3cdbf 0xa01950302029bcc2 0xf87a419a246be97c),
     (e 0xe419df4f5cbeddc5 0x939266745075ca5 0x1caca95cc094185a),
     (e 0x9fa6188c3e2ce0c0 0x41982a77e8368460 0xfba40b2e918c89c2),
     (e 0xe2d5ab2bffc5ef12 0xf5c647d81817abbe 0x7dfbe57d9f8ff1b8),
     (e 0x154e491c19d73349 0xb027cb813c9af06a 0x4e69276ce673dad3),
     (e 0x47d820cf3671e107 0x6fbd3067e6c7f1c6 0xc315538253c09236),
     (e 0x315fb2b1ff153ab4 0xdb9f7f6f190d8f96 0x44aefb8c75abe8d9),
     (e 0xb4b03fae779f4a89 0xef6b93bc1591e6e6 0x279a13593d71775f),
     (e 0x48119b4a4de8a490 0x708759452f73e21c 0x13665fec849375dd),
     (e 0x75f5bbab22fc9912 0x35d5b141c6eab00e 0x457ffd0c062f3e3),
     (e 0xb535f1342e213efe 0x2b894b61e7bd9ed4 0x8d044cc798827ec3),
     (e 0xcc2d4824ff06cb55 0xe9425184c3aee8f0 0x16d6ac40a3e37732),
     (e 0xa451609bc2845b0f 0xe67b08b9c73baef5 0xcfde494daf247df0),
     (e 0xd2bf176e84e98d06 0x64e9a84ba5a1604d 0x7762e57a4da3a1c5)]

#guard (phiMap (fe 86) (fes 80 6)) =
    (e 0x4cb668700da3f261 0xab0d10fba861e7b4 0x23339057a2a50ce8)

/-- `derive_config(log_n, rate)` for every admissible pair: folds, rates, queries. The query
counts are those of leanVM `127510d14c98ade4e8a97646c44fa7f1ff5e752d` (`verifier.py:912`). -/
def pythonConfigs : List (ℕ × ℕ × List ℕ × List ℕ × List ℕ) :=
  [(15, 1, [6, 4], [1, 4], [222, 55]),
   (16, 1, [6, 4, 4], [1, 4, 7], [223, 56, 30]),
   (17, 1, [6, 4, 4], [1, 4, 7], [223, 56, 31]),
   (18, 1, [6, 4, 4], [1, 4, 7], [223, 56, 32]),
   (19, 1, [6, 4, 4], [1, 4, 7], [223, 56, 32]),
   (20, 1, [6, 4, 4, 4], [1, 4, 7, 10], [223, 56, 32, 22]),
   (21, 1, [6, 4, 4, 4], [1, 4, 7, 10], [223, 56, 32, 22]),
   (22, 1, [6, 4, 4, 4], [1, 4, 7, 10], [224, 56, 32, 23]),
   (23, 1, [6, 4, 4, 4], [1, 4, 7, 10], [224, 56, 32, 23]),
   (24, 1, [6, 4, 4, 4, 4], [1, 4, 7, 10, 13], [224, 56, 32, 23, 17]),
   (25, 1, [6, 4, 4, 4, 4], [1, 4, 7, 10, 13], [224, 56, 32, 23, 17]),
   (26, 1, [6, 4, 4, 4, 4], [1, 4, 7, 10, 13], [224, 56, 32, 23, 18]),
   (27, 1, [6, 4, 4, 4, 4], [1, 4, 7, 10, 13], [225, 56, 32, 23, 18]),
   (28, 1, [6, 4, 4, 4, 4, 4], [1, 4, 7, 10, 13, 16], [225, 56, 32, 23, 18, 14]),
   (15, 2, [6, 4], [2, 5], [111, 45]),
   (16, 2, [6, 4, 4], [2, 5, 8], [112, 45, 27]),
   (17, 2, [6, 4, 4], [2, 5, 8], [112, 45, 28]),
   (18, 2, [6, 4, 4], [2, 5, 8], [112, 45, 28]),
   (19, 2, [6, 4, 4], [2, 5, 8], [112, 45, 28]),
   (20, 2, [6, 4, 4, 4], [2, 5, 8, 11], [112, 45, 28, 20]),
   (21, 2, [6, 4, 4, 4], [2, 5, 8, 11], [112, 45, 28, 20]),
   (22, 2, [6, 4, 4, 4], [2, 5, 8, 11], [112, 45, 28, 21]),
   (23, 2, [6, 4, 4, 4], [2, 5, 8, 11], [112, 45, 28, 21]),
   (24, 2, [6, 4, 4, 4, 4], [2, 5, 8, 11, 14], [112, 45, 28, 21, 16]),
   (25, 2, [6, 4, 4, 4, 4], [2, 5, 8, 11, 14], [112, 45, 28, 21, 16]),
   (26, 2, [6, 4, 4, 4, 4], [2, 5, 8, 11, 14], [112, 45, 28, 21, 16]),
   (27, 2, [6, 4, 4, 4, 4], [2, 5, 8, 11, 14], [112, 45, 28, 21, 16]),
   (28, 2, [6, 4, 4, 4, 4, 4], [2, 5, 8, 11, 14, 17], [112, 45, 28, 21, 16, 13]),
   (15, 3, [6, 4], [3, 6], [75, 37]),
   (16, 3, [6, 4, 4], [3, 6, 9], [75, 37, 24]),
   (17, 3, [6, 4, 4], [3, 6, 9], [75, 37, 25]),
   (18, 3, [6, 4, 4], [3, 6, 9], [75, 38, 25]),
   (19, 3, [6, 4, 4], [3, 6, 9], [75, 38, 25]),
   (20, 3, [6, 4, 4, 4], [3, 6, 9, 12], [75, 38, 25, 18]),
   (21, 3, [6, 4, 4, 4], [3, 6, 9, 12], [75, 38, 25, 19]),
   (22, 3, [6, 4, 4, 4], [3, 6, 9, 12], [75, 38, 25, 19]),
   (23, 3, [6, 4, 4, 4], [3, 6, 9, 12], [75, 38, 25, 19]),
   (24, 3, [6, 4, 4, 4, 4], [3, 6, 9, 12, 15], [75, 38, 25, 19, 15]),
   (25, 3, [6, 4, 4, 4, 4], [3, 6, 9, 12, 15], [75, 38, 25, 19, 15]),
   (26, 3, [6, 4, 4, 4, 4], [3, 6, 9, 12, 15], [75, 38, 25, 19, 15]),
   (27, 3, [6, 4, 4, 4, 4], [3, 6, 9, 12, 15], [75, 38, 25, 19, 15]),
   (28, 3, [6, 4, 4, 4, 4, 4], [3, 6, 9, 12, 15, 18], [75, 38, 25, 19, 15, 13]),
   (15, 4, [6, 4], [4, 7], [56, 32]),
   (16, 4, [6, 4, 4], [4, 7, 10], [56, 32, 22]),
   (17, 4, [6, 4, 4], [4, 7, 10], [56, 32, 22]),
   (18, 4, [6, 4, 4], [4, 7, 10], [56, 32, 23]),
   (19, 4, [6, 4, 4], [4, 7, 10], [56, 32, 23]),
   (20, 4, [6, 4, 4, 4], [4, 7, 10, 13], [56, 32, 23, 17]),
   (21, 4, [6, 4, 4, 4], [4, 7, 10, 13], [56, 32, 23, 17]),
   (22, 4, [6, 4, 4, 4], [4, 7, 10, 13], [56, 32, 23, 18]),
   (23, 4, [6, 4, 4, 4], [4, 7, 10, 13], [56, 32, 23, 18]),
   (24, 4, [6, 4, 4, 4, 4], [4, 7, 10, 13, 16], [56, 32, 23, 18, 14]),
   (25, 4, [6, 4, 4, 4, 4], [4, 7, 10, 13, 16], [56, 32, 23, 18, 14]),
   (26, 4, [6, 4, 4, 4, 4], [4, 7, 10, 13, 16], [56, 32, 23, 18, 14]),
   (27, 4, [6, 4, 4, 4, 4], [4, 7, 10, 13, 16], [56, 32, 23, 18, 15]),
   (28, 4, [6, 4, 4, 4, 4, 4], [4, 7, 10, 13, 16, 19], [56, 32, 23, 18, 15, 12])]

#guard (stackOffsets [3, 5, 5, 0, 2, 5, 1]) =
    ([96, 0, 32, 110, 104, 64, 108], 7)

#guard (samplePlacement.stackPoint [fe 90, fe 91, fe 92] 9) =
    [(e 0x1 0x0 0x0), (e 0x0 0x0 0x0),
     (e 0xa0e42a8c192efb90 0x729974beeac1e893 0x444ebef1bc54d596),
     (e 0x3f1ba445987977a5 0x10d0ee786a0c64a8 0xe28638ab3b9f51ab),
     (e 0xdd531dff17c3f3ba 0xaf086831e956e0bd 0x80bdb264bae9cdc0), (e 0x0 0x0 0x0),
     (e 0x1 0x0 0x0), (e 0x0 0x0 0x0), (e 0x0 0x0 0x0)]

#guard (samplePlacement.eqAbove (fes 93 9)) =
    (e 0xde054c747e1b6da3 0x6695c3146656e56c 0xa8e74e9510e94f3b)

#guard (bilinearProbe) =
    ((e 0x63f5c1f382a78fc3 0x0 0x0),
     (e 0xf3359ee698bc8723 0x0 0x0),
     (e 0x30689e564a9e959c 0x801920cc33ec050b 0x20d8f6972431ac0f))

#guard (sampleLayout.stackLog) =
    19

#guard (sampleLayout.logBytecode) =
    1

#guard (sampleLayout.placements.map fun p ↦ (p.vars, p.index, p.low)) =
    [(16, 0, 0), (16, 65536, 0), (16, 131072, 0), (16, 196608, 0), (1, 264520, 0),
     (11, 262144, 0), (2, 264344, 0), (2, 264348, 0), (2, 264352, 0), (2, 264356, 0),
     (2, 264360, 0), (2, 264364, 0), (2, 264368, 0), (2, 264372, 0), (2, 264376, 0),
     (2, 264380, 0), (2, 264384, 0), (2, 264388, 0), (2, 264392, 0), (2, 264396, 0),
     (2, 264400, 0), (1, 264522, 0), (1, 264524, 0), (1, 264526, 0), (1, 264528, 0),
     (1, 264530, 0), (1, 264532, 0), (1, 264534, 0), (1, 264536, 0), (1, 264538, 0),
     (1, 264540, 0), (1, 264542, 0), (1, 264544, 0), (1, 264546, 0), (1, 264548, 0),
     (1, 264550, 0), (1, 264552, 0), (1, 264554, 0), (1, 264556, 0), (1, 264558, 0),
     (1, 264560, 0), (1, 264562, 0), (1, 264564, 0), (1, 264566, 0), (2, 264404, 0),
     (2, 264408, 0), (2, 264412, 0), (2, 264416, 0), (2, 264420, 0), (2, 264424, 0),
     (2, 264428, 0), (2, 264432, 0), (2, 264436, 0), (2, 264440, 0), (2, 264444, 0),
     (2, 264448, 0), (2, 264452, 0), (2, 264456, 0), (2, 264460, 0), (2, 264464, 0),
     (2, 264468, 0), (2, 264472, 0), (2, 264476, 0), (2, 264480, 0), (2, 264484, 0),
     (2, 264488, 0), (2, 264492, 0), (2, 264496, 0), (2, 264500, 0), (2, 264504, 0),
     (2, 264508, 0), (2, 264512, 0), (2, 264516, 0), (3, 264192, 0), (3, 264200, 0),
     (3, 264208, 0), (3, 264216, 0), (3, 264224, 0), (3, 264232, 0), (3, 264240, 0),
     (3, 264248, 0), (3, 264256, 0), (3, 262154, 8), (3, 262155, 8), (3, 262156, 8),
     (3, 262157, 8), (3, 262158, 8), (3, 262159, 8), (3, 262160, 8), (3, 262161, 8),
     (3, 262148, 8), (3, 262149, 8), (3, 262150, 8), (3, 262151, 8), (3, 262144, 8),
     (3, 262145, 8), (3, 262146, 8), (3, 262147, 8), (3, 262162, 8), (3, 262163, 8),
     (3, 264264, 0), (3, 264272, 0), (3, 264280, 0), (3, 264288, 0), (3, 264296, 0),
     (3, 264304, 0), (3, 264312, 0), (3, 264320, 0), (3, 264328, 0), (3, 264336, 0)]

#guard (blockProbe sampleLayout.push) =
    [(2, 0, 3, (e 0x295f303850cc44ae 0x2a75f12fa9759b1f 0x8d1125d19e1d7bb9)),
     (2, 0, 9, (e 0xedf31ca2a5aeb794 0xc5f4f6cee8ff67c4 0xe528ff9c358a2f2e)),
     (2, 0, 6, (e 0xc075807cea5391e6 0x45b4d3b13324285f 0x37a448cdfa07b1e8)),
     (2, 0, 6, (e 0x8e56ac23c73d6fad 0xe71e806358deb151 0xe10275b0cef82904)),
     (2, 0, 6, (e 0xae07e3f503f3500d 0x557572d8f9b4c066 0x43beb1b37255bfd1)),
     (1, 1, 3, (e 0x295f303850cc44ae 0x2a75f12fa9759b1f 0x8d1125d19e1d7bb9)),
     (1, 1, 9, (e 0xa961aa7f6e20ddeb 0x5548538ed22c297b 0xb012a9933dca2dc7)),
     (1, 1, 6, (e 0xc075807cea5391e6 0x45b4d3b13324285f 0x37a448cdfa07b1e8)),
     (1, 1, 6, (e 0x8e56ac23c73d6fad 0xe71e806358deb151 0xe10275b0cef82904)),
     (1, 1, 6, (e 0x428c6b7038d05f6b 0xa7b0a0e69f961918 0x4d7d8041bbefec3c)),
     (1, 2, 3, (e 0x295f303850cc44ae 0x2a75f12fa9759b1f 0x8d1125d19e1d7bb9)),
     (1, 2, 9, (e 0xdd943ffb420a88b3 0x9bb7754d3264ee59 0x24601c10e20f984d)),
     (1, 2, 6, (e 0x667ebdf7f01724dd 0xd09e2e1ecdea85b9 0x7e8169447f73cf3b)),
     (2, 3, 3, (e 0x295f303850cc44ae 0x2a75f12fa9759b1f 0x8d1125d19e1d7bb9)),
     (2, 3, 9, (e 0xae91a91b89c52fe2 0x49d81f26e8247a8d 0x144f4d427bdd6c7a)),
     (2, 3, 6, (e 0xf346890a1c1be1c6 0x65e453c8a3b76162 0x61cf098a3fc5a527)),
     (2, 3, 6, (e 0xe939a7d9ea89509e 0xec3c042db13b74c5 0x2296f7e76346c102)),
     (2, 3, 6, (e 0x73e5ac0b63062ab2 0x29150db386eb53d4 0xed6e27e2b115a020)),
     (2, 4, 3, (e 0x2a620b88289f92f9 0xa356282ef1076929 0x4c3a74498ad38e95)),
     (2, 4, 9, (e 0x2f105080de04647c 0x8e57d5862349c84c 0xa98f8689116eb156)),
     (2, 4, 6, (e 0xe830f8eef2f6ad55 0xc08ddeba64d34674 0xc55a4021e18ecaca)),
     (2, 4, 6, (e 0xaa491a07c444d14a 0x487ed1b20d9c060e 0x44f2c76fa9f7bf5a)),
     (2, 4, 6, (e 0x828ba7871753914 0x36c4c4d664bde020 0xceee367e0f161c65)),
     (3, 5, 3, (e 0x295f303850cc44ae 0x2a75f12fa9759b1f 0x8d1125d19e1d7bb9)),
     (3, 5, 11, (e 0x79686adb9eb7ea84 0x8aaf9e8f726e68ed 0xc90d5312c5cd0a05)),
     (3, 5, 6, (e 0xd8fcd578ce808f1b 0xb1f1fd91bee412eb 0xca44b9194b482075)),
     (3, 5, 6, (e 0xabfe6c15ff720b14 0xd0c70c96e4073f71 0x8db94e2f124e9c34)),
     (3, 5, 6, (e 0xe07091c5e7327e0c 0xd07a64e220f05b03 0x7e99c17b1afee370)),
     (3, 5, 6, (e 0x3dc740d1bd019161 0xda77035367528676 0xef82132fabee233a)),
     (3, 5, 6, (e 0x71d5681544bcabcb 0xd2d210ae178cc5d5 0xb49a251022f1bf9b)),
     (3, 5, 6, (e 0xb152108811deb2a4 0xc865452855afcc8b 0x30ae63a34e4a00f)),
     (3, 5, 6, (e 0xf1edce39fa6ae943 0x6aaef8829a2e71f5 0x5fcbf7764a67c9f7)),
     (3, 5, 6, (e 0x1ccbb9b3370c2f76 0xc906ca349cfd1bfc 0xe780a14fcc905ebb)),
     (3, 5, 6, (e 0x5d3de3da36648b98 0xb22f7756018ae5f8 0x1ad53ecfd500325))]

#guard (blockProbe sampleLayout.pull) =
    [(2, 0, 3, (e 0xa2064c999c552c7a 0xa625e23b836e1f30 0x3a85996546700198)),
     (2, 0, 9, (e 0x8a39d21e2195222f 0xa8381fa57bf3cb14 0x58b1482211f54409)),
     (2, 0, 6, (e 0x82f1497391a3d8bd 0xbb1f097c5b6ae05 0xe386a193aece1d8c)),
     (2, 0, 6, (e 0x8ac461d703ce7f2a 0x41b48880e9fe47bf 0xca86f4d1074bf0af)),
     (2, 0, 6, (e 0x50223f593589df6d 0x1001e52c4f785b4a 0xab78958c806477a4)),
     (1, 1, 3, (e 0xa2064c999c552c7a 0xa625e23b836e1f30 0x3a85996546700198)),
     (1, 1, 9, (e 0xceab64c3ea1b4850 0x3884bae5412085ab 0xd8b1e2d19b546e0)),
     (1, 1, 6, (e 0x82f1497391a3d8bd 0xbb1f097c5b6ae05 0xe386a193aece1d8c)),
     (1, 1, 6, (e 0x8ac461d703ce7f2a 0x41b48880e9fe47bf 0xca86f4d1074bf0af)),
     (1, 1, 6, (e 0xbca9b7dc0eaad00b 0xe2c43712295a8234 0xa5bba47e49de2449)),
     (1, 2, 3, (e 0xa2064c999c552c7a 0xa625e23b836e1f30 0x3a85996546700198)),
     (1, 2, 9, (e 0x9f65390701977326 0x9a150c936b0b672f 0x2ed2de50fe4a1858)),
     (1, 2, 6, (e 0xd6c08b719f317415 0x7b76af9bc85d3bf1 0xaad7604cf772c3ba)),
     (2, 3, 3, (e 0xa2064c999c552c7a 0xa625e23b836e1f30 0x3a85996546700198)),
     (2, 3, 9, (e 0xc95b67a70dfeba59 0x2414f64d7b28d65d 0xa9d6fafc5fa2075d)),
     (2, 3, 6, (e 0xb1c2400567eba89d 0x2be170ee5525e738 0xb5ede0d46b0c0943)),
     (2, 3, 6, (e 0xedab6a2d2e7a4019 0x4a960cce001b822b 0x9127686aaf518a9)),
     (2, 3, 6, (e 0x8dc070a7557ca5d2 0x6c619a473027c8f8 0x5a803dd43246855)),
     (2, 4, 3, (e 0xa2064c999c552c7a 0xa625e23b836e1f30 0x3a85996546700198)),
     (2, 4, 9, (e 0x6d94998fa5f42d27 0xc052f6a0d5db4e16 0x7dad6fd745a71d32)),
     (2, 4, 6, (e 0x262baccc1718a4 0x457b5901855f9bdb 0x332382ae6a3b42c)),
     (2, 4, 6, (e 0x4d5dc026d34ab832 0xfac2e9644cd582c7 0xde9586075ba6b06a)),
     (2, 4, 6, (e 0x1affed3568958e29 0xbcd57d73d231ea37 0x6949862fdb9c5235)),
     (3, 5, 3, (e 0xa2064c999c552c7a 0xa625e23b836e1f30 0x3a85996546700198)),
     (3, 5, 11, (e 0xc3b677a4fc6d4522 0x102ce6fab9d8611d 0xd99b3ec3bec5c5dc)),
     (3, 5, 6, (e 0xf96f9d13ff0f73f7 0x31ca629527f50cec 0xfe1a947684006b42)),
     (3, 5, 6, (e 0xa79c8970371437c5 0x7a2f781ce397d92e 0x8718e696f845d5e3)),
     (3, 5, 6, (e 0xc78615b4e9def46d 0xb96215806fd1123 0xb4e73b90e9d6298d)),
     (3, 5, 6, (e 0x6363c7d2abc95059 0xeb6dd139a6133c13 0x263f868b3611f993)),
     (3, 5, 6, (e 0xe0f4de4937167911 0xf5dc0c7ef63291c9 0x184fb5e0be8f1fd9)),
     (3, 5, 6, (e 0x34c46bb216820dfb 0x81d69c8adfa86841 0x7873f21a728bc215)),
     (3, 5, 6, (e 0xa0fed7184ac756e2 0xb750f7584375c4db 0x2b4d2dd06bcaa7ba)),
     (3, 5, 6, (e 0xc63db849ac5ad466 0xedc6abb9370472a5 0xfb046c1283a114ba)),
     (3, 5, 6, (e 0x270a4c432b8f258c 0x3b9a1e05f99e6958 0x59ef21ead76fbcd5))]

#guard (blockProbe sampleLayout.count) =
    [(2, 0, 1, (e 0x691cb3394363a17d 0x3ad1fd6c14f68e80 0xc87479ee6897b83)),
     (2, 0, 1, (e 0x7542cf2c2ae1d92 0xd909772594410a95 0xaabec15865d3f798)),
     (2, 0, 1, (e 0xa58ba6ac41f899a7 0x7740f0df138b86aa 0x48f63b11e51e73ad)),
     (2, 0, 1, (e 0x43c32065c14315bc 0x15786a9892d602bf 0xe72db4cb6468efc2)),
     (1, 1, 1, (e 0x691cb3394363a17d 0x3ad1fd6c14f68e80 0xc87479ee6897b83)),
     (1, 1, 1, (e 0x7542cf2c2ae1d92 0xd909772594410a95 0xaabec15865d3f798)),
     (1, 1, 1, (e 0xa58ba6ac41f899a7 0x7740f0df138b86aa 0x48f63b11e51e73ad)),
     (1, 1, 1, (e 0x43c32065c14315bc 0x15786a9892d602bf 0xe72db4cb6468efc2)),
     (1, 2, 1, (e 0x52075299c6ef3514 0x23bc9ccc98822217 0xf571e6ff6a150f1a)),
     (1, 2, 1, (e 0xf03ecc534639b129 0xc1f4168617cc9e2c 0x93a960b8e95f8b2f)),
     (2, 3, 1, (e 0x691cb3394363a17d 0x3ad1fd6c14f68e80 0xc87479ee6897b83)),
     (2, 3, 1, (e 0x7542cf2c2ae1d92 0xd909772594410a95 0xaabec15865d3f798)),
     (2, 3, 1, (e 0xa58ba6ac41f899a7 0x7740f0df138b86aa 0x48f63b11e51e73ad)),
     (2, 3, 1, (e 0x43c32065c14315bc 0x15786a9892d602bf 0xe72db4cb6468efc2)),
     (2, 4, 1, (e 0x8e76460cc5842d3e 0x602b903f97171a41 0x31e0da7268aa0744)),
     (2, 4, 1, (e 0x2cadbfc644cea953 0xfe6309f916619656 0xd018542be7f48359)),
     (2, 4, 1, (e 0xcae5397fc4192568 0x9c9a83b295ac126b 0x6e4fcde5673eff6e)),
     (2, 4, 1, (e 0x691cb3394363a17d 0x3ad1fd6c14f68e80 0xc87479ee6897b83)),
     (3, 5, 1, (e 0x4c944ed1380b62cd 0x1e499904099e4fd0 0xeffee336db313cd3)),
     (3, 5, 1, (e 0xeacbc88ab755dee2 0xbc8112bd88e8cbe5 0x8e365cf05a7bb8e8)),
     (3, 5, 1, (e 0x8903424436a05af7 0x5ab88c77083347fa 0x2c6dd6a9d9c634fd)),
     (3, 5, 1, (e 0x273abbfdb5ead70c 0xf8f00630877dc40f 0xcaa550635910b112)),
     (3, 5, 1, (e 0xc57235b735355321 0x97277fea06c84024 0x68dcca1cd85b2d27)),
     (3, 5, 1, (e 0x63a9af70b47fcf36 0x355ef9a38612bc39 0x71443d657a5a93c)),
     (3, 5, 1, (e 0x1e1292a33ca4b4b 0xd396735d055d384e 0xa54bbd8fd6f02551)),
     (3, 5, 1, (e 0xa018a2e3b314c760 0x71cded1684a7b463 0x43833749563aa166)),
     (3, 5, 1, (e 0x3e501c9d325f4375 0x100566d003f23078 0xe1bab102d5851d7b)),
     (3, 5, 1, (e 0xdc879656b1a9bf8a 0xae3ce089833cac8d 0x7ff22abc54cf9990))]

#guard (tableWidths) =
    [15, 15, 8, 15, 14, 37]

#guard (globalColumnBases) =
    [6, 21, 36, 44, 59, 73]

#guard (tables.map Table.nConstraints) =
    [0, 0, 0, 0, 2, 0]

#guard (tables.map Table.countColumns) =
    [[11, 12, 13, 14], [11, 12, 13, 14], [6, 7], [11, 12, 13, 14], [8, 9, 10, 11],
     [27, 28, 29, 30, 31, 32, 33, 34, 35, 36]]

#guard (jumpConstraints (fes 400 14)) =
    [(e 0x74c3d55b8563cc8d 0xe14fe16b59b07f5b 0xc8d072e655497420),
     (e 0xa796fc834b5ba71f 0x101f01afc165bbbb 0xa16e9550118705e7)]

#guard (busProbe [0, 16, 1] sampleLayout.push) =
    (17,
     [(0, 65702), (16, 0), (1, 65684), (2, 65624), (2, 65628), (2, 65632), (2, 65636), (2, 65640),
      (1, 65686), (1, 65688), (1, 65690), (1, 65692), (1, 65694), (1, 65696), (1, 65698),
      (1, 65700), (2, 65644), (2, 65648), (2, 65652), (2, 65656), (2, 65660), (2, 65664),
      (2, 65668), (2, 65672), (2, 65676), (2, 65680), (3, 65536), (3, 65544), (3, 65552),
      (3, 65560), (3, 65568), (3, 65576), (3, 65584), (3, 65592), (3, 65600), (3, 65608),
      (3, 65616)])

#guard (busProbe [0, 16, 1] sampleLayout.pull) =
    (17,
     [(0, 65702), (16, 0), (1, 65684), (2, 65624), (2, 65628), (2, 65632), (2, 65636), (2, 65640),
      (1, 65686), (1, 65688), (1, 65690), (1, 65692), (1, 65694), (1, 65696), (1, 65698),
      (1, 65700), (2, 65644), (2, 65648), (2, 65652), (2, 65656), (2, 65660), (2, 65664),
      (2, 65668), (2, 65672), (2, 65676), (2, 65680), (3, 65536), (3, 65544), (3, 65552),
      (3, 65560), (3, 65568), (3, 65576), (3, 65584), (3, 65592), (3, 65600), (3, 65608),
      (3, 65616)])

#guard (busProbe [] sampleLayout.count) =
    (8,
     [(2, 80), (2, 84), (2, 88), (2, 92), (1, 128), (1, 130), (1, 132), (1, 134), (1, 136),
      (1, 138), (2, 96), (2, 100), (2, 104), (2, 108), (2, 112), (2, 116), (2, 120), (2, 124),
      (3, 0), (3, 8), (3, 16), (3, 24), (3, 32), (3, 40), (3, 48), (3, 56), (3, 64), (3, 72)])

#guard ((seed sampleBytecode samplePublicInput).toList) =
    [0xe7ce50a2, 0xc5f85fbb, 0xefba29b0, 0x74df1ac1, 0x11d22d76, 0x7e5ed099, 0xd0843e59,
     0xa1650dde]

#guard ([(digestScalars samplePublicInput).1, (digestScalars samplePublicInput).2]) =
    [(e 0xdfcab5a08b76614c 0x87725d48331e09f4 0x0), (e 0x2f1a05f0dbc6b19c 0xd7c2ad98836e5944 0x0)]

#guard pythonConfigs.length = 56
#guard pythonConfigs.all fun (n, r, folds, rates, queries) ↦
  decide ((deriveConfig n r).map (fun ls ↦
    (ls.map (·.fold), ls.map (·.logInvRate), ls.map (·.queries))) = some (folds, rates, queries))

end LeanVMTests.Protocol.Verifier.Helpers
