import LeanVM.Protocol.Verifier

/-!
# Verifier helper tests: differential against the verifier at its pin

Every expected value below is the Rust verifier's (`crates/verifier`), on inputs drawn from the word generator `fw`, which the driver mirrors exactly; the
driver is the verifier crate's sources with their items made crate-visible and a module printing
each probe, kept in the port's scratch, not in the repository. Values that no change of the
protocol touched (the RMFE, the carry-less arithmetic, Keccak-f, Keccak-256, the IV and the seed)
are those of the earlier pins (`4af2cdddd`, `990b93526`), the others the driver's at `afe891a73`
but `fold_row` (at `71205cca4`) and `derive_config`'s query counts: nothing else they
read changed since. The line citations are to
`crates/verifier/src/`. Compiled checks (`#guard`): `E` multiplication does not reduce
in the kernel from module files.

Covered: `powers`, `eq_kernel`, `multilinear_eval` (on `E` and on lifted `K` tables), `eq_eval`,
`dot`, `index_mle`, `poly_eval`, `gpow`, `padding_weight`, `log2_ceil`, `log2_strict`,
`selector_point`, `grinding_bits`; `subspace_roots`, `Subspace::at`, `novel_eval`, `fold_row`,
`induced_weight`, `ext_row`; the ring map's `ring_coefficients`, `ring_psi`, `ring_target` and
`frobenius_8`; the tables' log-height floors, `keccak_cell_lanes`, `layout_limb`;
`derive_config` on all 56 admissible pairs; `along`,
`linear_transpose`, `instance_weights`, the slot weights of `open`,
`RMFE_EMBED`, `RMFE_PROJECT`, the carry-less product and the Keccak reduction's
constants; `KECCAK_RC`, `KECCAK_RHO`, `KECCAK_PI`, `keccak_f`, `keccak_hash` across the block
boundary, the sponge's `duplex`, `sample` and `absorb_nonce`; `TAG` (`versionTag`), the IV
(`fiatShamirIv`), the public input's halves, and the Fiat-Shamir seed (`Sponge::new`: Keccak-f of
`iv ‖ pi ‖ 0`). `build_layout`'s rejections are checked against what the verifier rejects on the
same inputs. Hotwire's layout, placements, stack and ring switch are pinned in `Spec/Layout.lean`
and `Protocol/RingSwitchVector.lean`, its link in `Protocol/Link.lean`; this file's bus-era pins of
them are archived at tag `formal-bus-archive`.
-/

namespace LeanVMTests.Protocol.Verifier.Helpers

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile

/-! ## Inputs, as the driver draws them -/

/-- The driver's 64-bit word generator. -/
def fw (k lane : ℕ) : ℕ :=
  ((k + 1) * 0x9E3779B97F4A7C15 + lane * 0xD1B54A32D192ED03 + 0x632BE59BD9B4E019) % 2 ^ 64

/-- An `E` element from its two limbs. -/
def e (c0 c1 : ℕ) : E := E.ofLimbs (K.ofBits c0) (K.ofBits c1)

/-- The driver's `fe(k)`. -/
def fe (i : ℕ) : E := e (fw i 0) (fw i 1)

/-- `fe(a), …, fe(a + n - 1)`. -/
def fes (a n : ℕ) : List E := (List.range n).map fun i ↦ fe (a + i)

/-- A lifted `K` table of sixteen entries. -/
def kTable : List E := (List.range 16).map fun i ↦ ofK (K.ofBits (fw i 5))

/-- Three fold rounds, `α, β` the elements `fe(910 + 2r), fe(911 + 2r)`. -/
def sampleRounds : List FoldRound :=
  (List.range 3).map fun r ↦ ⟨fe (910 + 2 * r), fe (911 + 2 * r)⟩

/-- A domain point outside the small subspaces: the word `fw(3, 7)`. -/
def samplePoint : K := K.ofBits (fw 3 7)

/-- The sample bytecode: 32 words, so `log_bytecode = 1`. -/
def sampleBytecode : List K := (List.range 32).map fun i ↦ K.ofBits (fw i 9)

/-- The sample row counts: `xor, mul, set, deref, jump, keccak`. Their log-heights are
`2, 1, 1, 2, 2, 9`, `KECCAK`'s raised to its floor `KECCAK_MIN_STEPS_LOG`. -/
def sampleRows : List ℕ := [3, 2, 2, 4, 3, 5]

/-- The sample public input: the 32 bytes `fw(i, 10) mod 256`. -/
def samplePublicInput : Digest :=
  digestOfBytes ((List.range 32).map fun i ↦ (fw i 10 % 256).toUInt8)

/-- The `n` bytes `fw(i, 15) mod 256`, hashed across Keccak-256's block boundary. -/
def sampleBytes (n : ℕ) : List UInt8 := (List.range n).map fun i ↦ (fw i 15 % 256).toUInt8

/-- A sponge state: the lanes `fw(i, 12)`. -/
def sampleState : KeccakState := Vector.ofFn fun i : Fin 25 ↦ (fw i 12).toUInt64

/-- `Sponge::duplex` from `sampleState` with these scalars waiting, and the challenge
`sample` reads off the result. -/
def duplexProbe (pending : List (E × ℕ)) : List UInt64 × E :=
  let s := keccakF1600 (duplexInput ⟨sampleState, pending, none⟩)
  (s.toList, challengeOf s)

/-- `Sponge::absorb_nonce` from `sampleState` with these scalars waiting: the proof of work, the
state, and the challenge it leaves for the next `sample`. -/
def nonceProbe (pending : List (E × ℕ)) (nonce : E) : UInt64 × List UInt64 × Option E :=
  let (pow, sponge) := Id.run (absorbNonce keccakF1600 ⟨sampleState, pending, none⟩ nonce)
  (pow, sponge.state.toList, sponge.ground)

/-- The `(j, k)` pairs `along` is probed at. -/
def alongPairs : List (ℕ × ℕ) :=
  [(0, 1), (63, 4), (64, 2), (255, 3), (1000, 1), (1599, 4), (1280, 0)]

/-- `linear_transpose` on the weights `fes 1000 1600`: its length, its first two entries,
and all of it batched by powers of `fe 501`. -/
def transposeProbe : ℕ × List E × E :=
  let t := keccakLinearTranspose (fes 1000 1600)
  (t.length, t.take 2, dot (powers (fe 501) 1600) t)

/-- A Keccak claim at `log_steps = 9`: a five-coordinate pack index and a segment index. -/
def sampleClaim : KeccakClaim := ⟨fe 609, fes 640 16, fes 610 6, fes 1000 1600⟩

/-- The slot weights at `log_steps = 9` of `sampleClaim` on `count` segments from `first`: the
number of rows, whether each is 64 wide, and all of them batched by powers of `fe 620`. In the Rust
they are no function of their own: `open` (`keccak.rs`) sums them against the slot
challenges' eq weights; the driver computes them by its loop with the slot weight left out. -/
def slotProbe (first count : ℕ) : ℕ × Bool × E :=
  let w := keccakSlotWeights 9 sampleClaim first count
  (w.length, w.all (·.length == 64), dot (powers (fe 620) 4096) w.flatten)

/-- The pairs the carry-less product is probed at: a 20-bit and a 12-bit polynomial. -/
def carrylessInputs : List (ℕ × ℕ) :=
  (List.range 4).map fun i ↦ (fw i 13 % 2 ^ 20, fw i 14 % 2 ^ 12)

/-- The Keccak reduction's and the layout's constants, in the driver's order. -/
def keccakConstants : List ℕ :=
  [keccakDepth, keccakSegments, keccakSegmentBits, qkeccakSlotBits, keccakMinStepsLog, keccakBits,
    keccakLocalBits, keccakLaneBits, kBits, pack, embedBits, productBits, numGlobalColumns,
    bytecodeSlotBits, Whir.minLogStack, Whir.maxLogStack]

/-! ## Constants and conventions -/

/- `y`, the generator of `E` over `K`, is a root of its modulus `y^2 + x·y + 1`. -/
#guard yE * yE = gen * yE + 1
#guard gen = ofK (K.ofBits 2)
#guard (buildLayout sampleBytecode 16 sampleRows).isSome

/-! ## `build_layout` rejects what the verifier rejects

On each input the driver ran `build_layout` and recorded whether it rejected. -/

/- A bytecode length that is not a power of two; one shorter than `2^BYTECODE_SLOT_BITS`; exactly
`2^BYTECODE_SLOT_BITS`. -/
#guard (buildLayout (sampleBytecode.take 24) 16 sampleRows).isNone
#guard (buildLayout (sampleBytecode.take 8) 16 sampleRows).isNone
#guard (buildLayout (sampleBytecode.take 16) 16 sampleRows).isSome
/- The memory window `[1, 30]`. -/
#guard (buildLayout sampleBytecode 0 sampleRows).isNone
#guard (buildLayout sampleBytecode 1 sampleRows).isSome
#guard (buildLayout sampleBytecode 31 sampleRows).isNone
#guard (buildLayout sampleBytecode 30 sampleRows).isSome
/- The row cap `2^30`, on any table. -/
#guard (buildLayout sampleBytecode 16 [2 ^ 30 + 1, 2, 2, 4, 3, 5]).isNone
#guard (buildLayout sampleBytecode 16 [2 ^ 30, 2, 2, 4, 3, 5]).isSome
#guard (buildLayout sampleBytecode 16 [3, 2, 2, 4, 3, 2 ^ 30]).isSome
/- No `KECCAK` row is no rejection: the table's height is its floor. Past the floor it grows. -/
#guard ((buildLayout sampleBytecode 16 [3, 2, 2, 4, 3, 0]).map (·.tableLogHeights)) =
  some [2, 1, 1, 2, 2, 9]
#guard ((buildLayout sampleBytecode 16 [3, 2, 2, 4, 3, 600]).map (·.tableLogHeights)) =
  some [2, 1, 1, 2, 2, 10]
/- Not one row count per table (the Rust verifier reads exactly `N_TABLES`, `lib.rs`). -/
#guard (buildLayout sampleBytecode 16 [3, 2, 2, 4, 3, 5, 0]).isNone
#guard (buildLayout sampleBytecode 16 [3, 2, 2, 4, 3]).isNone

/-! ## `derive_config` outside the window -/

#guard (Whir.ladder 15 1).isNone ∧ (Whir.ladder 33 1).isNone
#guard (Whir.ladder 20 0).isNone ∧ (Whir.ladder 20 5).isNone

/-! ## Field and multilinear arithmetic (`field.rs`, `multilinear.rs`, `layout.rs`;
`transcript.rs`) -/

#guard (powers (fe 1) 6) =
    [(e 0x1 0x0), (e 0x9f9ad90ed849d843 0x71502341a9dcc546),
     (e 0xe1a37ba00fcb757 0x6b7f4a078cf4033), (e 0xa8122ee46f0a5aa9 0x207e9faa54d4477e),
     (e 0x1386ae69256209bc 0x2935cd2a2d6d520a), (e 0x75aabec44b6c29e4 0x149ffcea20068577)]

#guard (eqKernel [fe 2, fe 3, fe 4]) =
    [(e 0xbead2bd434e75d5f 0xda6b629b43525dbe), (e 0x3d20be3cf61a211 0x4fcc71c241dada95),
     (e 0x59418220818cc34 0x21a6e468f3306334), (e 0xc2aa7e2ea5b77ff9 0xfff7675fd604dd9a),
     (e 0x425c891d2a16dba4 0xa5ca2492f4f2a42b), (e 0x232a65ab074ef486 0x9dd2217f5e0b9e70),
     (e 0xc4b7e823417d1e96 0x51803e9a6db7dbfa), (e 0xdf8042ae3a0c7d36 0x226eab19e0f2d824)]

#guard (multilinearEval ((List.range 8).map fe) [fe 10, fe 11, fe 12]) =
    (e 0x3e614120d15a4536 0xcd07a5dac74e097a)

#guard (multilinearEval kTable (fes 13 4)) =
    (e 0x1dc3a1c24ded43f0 0xf8b7ffe93761c398)

#guard (eqEval [fe 20, fe 21, fe 22] [fe 23, fe 24, fe 25]) =
    (e 0x82bd01e07f82614f 0x7851b73699908985)

#guard (dot [fe 26, fe 27, fe 28] [fe 29, fe 30, fe 31]) =
    (e 0x51628321ce552fa1 0x8fa5c83b4a6033d3)

#guard (indexMle [fe 32, fe 33, fe 34, fe 35]) =
    (e 0x76b748ec823a93fb 0xf9c17010b7cf0a2c)

#guard (polyEval [fe 40, fe 41, fe 42, fe 43, fe 44] (fe 45)) =
    (e 0x9ad61792f8d1c662 0xe7ba24ba7baefa70)

#guard (Verifier.gpow 5) =
    (e 0x20 0x0)

#guard (Verifier.gpow (2 ^ 32 - 1)) =
    (e 0xae3111b3bb81428f 0x0)

#guard ([0, 5, 11, 16].map (paddingWeight (fes 120 4))) =
    [(e 0x1 0x0), (e 0xfe088f14baad8355 0x396e02003469a810),
     (e 0x36fb865ece8ef208 0x83f8ca436afff1ea), (e 0x0 0x0)]

#guard ([0, 1, 2, 3, 5, 64, 65, 2 ^ 20].map log2Ceil) =
    [0, 0, 1, 2, 3, 6, 7, 20]

#guard ([16, 15, 17, 1, 0, 2 ^ 20].map log2Strict) =
    [some 4, none, none, some 0, none, some 20]

#guard (selectorPoint 13 6) =
    [(e 0x1 0x0), (e 0x0 0x0), (e 0x1 0x0), (e 0x1 0x0), (e 0x0 0x0), (e 0x0 0x0)]

/- `grinding_bits`, at the inputs of `fiat_shamir_prover`'s own test -/
#guard ([0, 1, 2, 8, 9, 31, 46, 64, 65, 2 ^ 20].map grindingBits) =
    [0, 0, 0, 0, 1, 2, 3, 3, 4, 17]

/-! ## WHIR helpers (`whir.rs`) -/

#guard ((subspaceRoots 12).map kToNat) =
    [0x1, 0x6, 0x168, 0x1166880, 0x11616686880801b, 0x726b6e3c6e39234e, 0x796adf34d64462c2,
     0xf1060866be6fa9c, 0x6a06f1b0a76acb05, 0xd2d14e471a7186d9, 0x6d55ab94bb5f9605,
     0xd08c5570c6423a2a, 0xa0ca298b954731]

#guard ((subspaceAt 5 samplePoint).map kToNat) =
    [0x97fed3e591e34b82, 0x820abeab5326f91b, 0xa114ae0175dc5efb, 0xbe64d74b712dcf9b,
     0x78e3eabfdbd2fc1f, 0xbbb44a699f093317]

#guard (novelEval (fes 50 7) (subspaceAt 5 samplePoint)) =
    (e 0xb6f010b2bcb2ddf3 0x4ea90edd296a3d9)

/- `2^5 + 1` coefficients: the last weighs `What_5`. -/
#guard (novelEval (fes 50 33) (subspaceAt 5 samplePoint)) =
    (e 0x87e252e36d1b76a7 0xe08d5e4b4a5b7a2e)

#guard (foldRow (fes 900 8) (K.ofBits 23) sampleRounds) =
    (e 0xb8d373c1d29ea65a 0xba103fe1bfbd4c47)

#guard (inducedWeight 5 [3, 17, 30, 0] (powers (fe 60) 4) [fe 61, fe 62, fe 63, fe 64, fe 65]) =
    (e 0x1f414c84d37628a1 0xfc45dc207f904f40)

#guard (extRow ((List.range 6).map fun i ↦ K.ofBits (fw i 6))) =
    [(e 0xeba31c864270ea40 0x89da963fc1bb6655), (e 0x28120ff94105e26a 0xc64989b2c0505e7f),
     (e 0x6481036c3f9ada94 0x2b87d25bee556a9)]

/- An odd word is dropped. -/
#guard (extRow ((List.range 7).map fun i ↦ K.ofBits (fw i 6))) =
    [(e 0xeba31c864270ea40 0x89da963fc1bb6655), (e 0x28120ff94105e26a 0xc64989b2c0505e7f),
     (e 0x6481036c3f9ada94 0x2b87d25bee556a9)]

/-! ## Ring switching (`ring_switch.rs`) -/

#guard (ringCoefficients (fes 80 8) (fes 88 8)) =
    [(e 0x50a3732d98b25847 0x485783167b605da4), (e 0x6abb07138c18f0f9 0xeac0f214fe325859),
     (e 0xd611ecc1cc4d7387 0x4c9e9d11365c1009), (e 0x12259a8cb8ab8986 0xcc029a2a82c1df76),
     (e 0xe567e0c2e347c200 0xd1433bb6c65b3eef), (e 0x69ffd590d5ce4d57 0x7c4f1ab7870c6460),
     (e 0x8c4f9c70125ac3f5 0xb8f6fe4a0ec0f6b8), (e 0x37cbf2331969ec0d 0xb3130f3790a148b4),
     (e 0x6b37f06cee3af49e 0xa2731ed82dc1ca60), (e 0xf7efb79f9c3f4b85 0x8f015b52604972b1),
     (e 0xde572696c46b9d4f 0xa4545fa66490a55d), (e 0x1452537f52385cca 0x342dea07aacf85b5),
     (e 0xe134b152c370c9ca 0x27cf634c9ea7e054), (e 0xe99dfd5eefc375ad 0xb97246efb1831500),
     (e 0xc9e0fa00f3e10266 0x7e8374871f70dcc7), (e 0x4830007e983476f1 0x83a07c3a3ce4c8fc),
     (e 0x31998518d78293e 0xc70177ed1621782), (e 0x665719ec07847cf5 0x161e89c73e72a776),
     (e 0xf677b54994c01f5f 0x3ef09127b630250f), (e 0x6b18eedae39b86b8 0xa781a1b9af8e17ce),
     (e 0x140e5c59be8ffc1c 0xc212ca142beea2b1), (e 0xccc99e8f38368d8d 0xa22ff0ef6cf6971e),
     (e 0xf981c0f6300698ec 0xc38bd33b406d1e8b), (e 0x601f24f47b8b4b98 0x2d1e568a5efc6a89),
     (e 0xe4cd38e05ed82c32 0x8743589f25c0c4d2), (e 0xa21982c467a0e41 0x6de2080435fad976),
     (e 0x27245558a61e31a3 0x37aed79f9f48980b), (e 0xa6737ae9057e6d48 0x21e6aee3abdfcb4f),
     (e 0xad83ad6089574a19 0x907b2785d8cb8ba), (e 0x2a96e6a8a92f269c 0x2a3d3963c4c6338e),
     (e 0x5618cf20676d722f 0x9c9ff4efdfb18922), (e 0x5260511768780187 0xb65099e25fa961a4),
     (e 0x57717a286aae26df 0x54f6dd51432bfc56), (e 0x9bbd0bb06816822c 0xf87b83080eaf117d),
     (e 0xd1cba5a6ca17829a 0xd1029176ba5f290), (e 0x94478543effd4a5f 0x982e46b42467c97e),
     (e 0x2c9a2089ca3ef389 0x27025004df19c53a), (e 0xeb3b1bc451ebdb52 0x678ffd8eeaa46d9b),
     (e 0x2633586dd089f9f0 0xea6c9a4ffeed6340), (e 0x3ce88fd4eafdadb5 0x2a2461e73fe5f42c),
     (e 0xe610862aa209e590 0x6ee7470aa8a54db4), (e 0xfb05cf13c32e8dd6 0xc382dceeb934ef62),
     (e 0xe274fac9a3d02b03 0x8ea64c0fe553be15), (e 0x704d785f0f74af52 0x3543596cc84b8279),
     (e 0x18954d11d787dbe1 0x690318d6b15d7c1f), (e 0x66ac6c02d71561cf 0x6fc5b31d9837a89d),
     (e 0xc56eb4882a99e0f3 0x28cea2759a37504d), (e 0x22cbbfd05d23ef9f 0xa3dc0e8c508898b4),
     (e 0xf4abe83726c2a35e 0x20609568eba0870d), (e 0x5f8b3250b8cb068e 0x9074e1ad5bf4d69b),
     (e 0xc3c0e4e98922d4dc 0xb8c6e9ad428ada02), (e 0x1c3c14cb7e00faf8 0x1feaddd455ec9a8d),
     (e 0x2cfc85a970655be1 0xf3ecab42599a8a7f), (e 0x3a4ea0cd9267e037 0xd282f0ec3fab5310),
     (e 0xd1fe62fbcd70f92b 0x86848a0a6de29968), (e 0xc66219c21c0d31ab 0x1fddc983bd14871a),
     (e 0xee238a1ddcb4cc62 0x1076e966ccf1012c), (e 0xaa3447cda6a54d 0x7c102d47a198ac87),
     (e 0x697b03fdc18b2c1f 0xb63a1b13bb08eb27), (e 0x60be2559a1170a21 0x6df0832ec7cee6dd),
     (e 0x802a0b932c334ecc 0x29b24e4ec9fc781c), (e 0xee98666e19e50c19 0x85fc104d06ba77ff),
     (e 0x3638fa1b4cf435c2 0x883f3ea488e72c88), (e 0xfb74e1c597a32a29 0x649b0ee661d7fa42)]

#guard (ringPsi (fe 86) (fes 88 8)) =
    (e 0xb254215a0dad7123 0xa6def745624dd0b9)

#guard (ringTarget (fes 130 64) (fes 80 8) (fes 88 8)) =
    (e 0x9a2f7a8e451a7d5e 0x92fdd92ed9c8d7c3)

#guard (frobenius8 (fe 87) 3) =
    (e 0x6d621675ade71890 0xc961818aa4701716)

/-! ## The tables (`layout.rs`; their columns, widths and links are pinned at Hotwire in
`Spec/Layout.lean`) -/

#guard (tableLogFloors) =
    [0, 0, 0, 0, 0, 9]

#guard ([false, true].map fun odd ↦ (List.range 13).map (LeanVM.Semantics.cellLanes odd)) =
    [[(some 0, some 1), (some 2, some 3), (some 4, some 5), (some 6, some 7), (some 8, some 9),
      (some 10, some 11), (some 12, some 13), (some 14, some 15), (some 16, none),
      (some 17, some 18), (some 19, some 20), (some 21, some 22), (some 23, some 24)],
     [(none, some 0), (some 1, some 2), (some 3, some 4), (some 5, some 6), (some 7, some 8),
      (some 9, some 10), (some 11, some 12), (some 13, some 14), (some 15, some 16),
      (some 17, some 18), (some 19, some 20), (some 21, some 22), (some 23, some 24)]]

#guard ((layoutLimb (some 3) (some 5) 7 (some 9)).evaluate fun i ↦ fe (150 + i)) =
    (e 0xd51b5df9c3a2114e 0xaed8f199a2d42f42)

#guard ((layoutLimb none (some 5) 7 (some 9)).evaluate fun i ↦ fe (150 + i)) =
    (e 0x82a6265599796dc4 0xb572cac242f27e3b)

#guard ((layoutLimb (some 3) none 7 none).evaluate fun i ↦ fe (150 + i)) =
    (e 0xd0b726c353e61095 0xbe9f7b339d0c5441)

#guard ((layoutLimb none none 7 none).evaluate fun i ↦ fe (150 + i)) =
    (e 0x0 0x0)

#guard ((layoutLimb none none 7 (some 9)).evaluate fun i ↦ fe (150 + i)) =
    (e 0x45d7f98b68426d39 0x178d43be39d55a3c)

#guard ((layoutLimb (some 4) (some 4) 7 none).evaluate fun i ↦ fe (150 + i)) =
    (e 0x2ec298ebebce00d0 0x77e31ebd60edd3)

#guard ((layoutLimb none (some 9) 7 (some 9)).evaluate fun i ↦ fe (150 + i)) =
    (e 0x45d7f98b68426d39 0x178d43be39d55a3c)

/-! ## `derive_config` (`whir.rs`) -/

/-- `derive_config(log_n, rate)` for every admissible pair: folds, rates, queries. -/
def refConfigs : List (ℕ × ℕ × List ℕ × List ℕ × List ℕ) :=
  [(16, 1, [6, 4, 4], [1, 4, 7], [230, 60, 42]),
   (17, 1, [6, 4, 4], [1, 4, 7], [225, 58, 38]),
   (18, 1, [6, 4, 4], [1, 4, 7], [222, 57, 35]),
   (19, 1, [6, 4, 4], [1, 4, 7], [220, 56, 34]),
   (20, 1, [6, 4, 4, 4], [1, 4, 7, 10], [219, 55, 33, 27]),
   (21, 1, [6, 4, 4, 4], [1, 4, 7, 10], [218, 55, 32, 25]),
   (22, 1, [6, 4, 4, 4], [1, 4, 7, 10], [218, 55, 32, 24]),
   (23, 1, [6, 4, 4, 4], [1, 4, 7, 10], [218, 55, 32, 23]),
   (24, 1, [6, 4, 4, 4, 4], [1, 4, 7, 10, 13], [218, 55, 32, 23, 20]),
   (25, 1, [6, 4, 4, 4, 4], [1, 4, 7, 10, 13], [218, 55, 32, 23, 19]),
   (26, 1, [6, 4, 4, 4, 4], [1, 4, 7, 10, 13], [218, 55, 32, 23, 18]),
   (27, 1, [6, 4, 4, 4, 4], [1, 4, 7, 10, 13], [218, 55, 32, 23, 18]),
   (28, 1, [6, 4, 4, 4, 4, 4], [1, 4, 7, 10, 13, 16], [218, 55, 32, 23, 18, 16]),
   (29, 1, [6, 4, 4, 4, 4, 4], [1, 4, 7, 10, 13, 16], [218, 55, 32, 23, 18, 15]),
   (30, 1, [6, 4, 4, 4, 4, 4], [1, 4, 7, 10, 13, 16], [218, 55, 32, 23, 18, 15]),
   (16, 2, [6, 4, 4], [2, 5, 8], [112, 47, 35]),
   (17, 2, [6, 4, 4], [2, 5, 8], [111, 46, 32]),
   (18, 2, [6, 4, 4], [2, 5, 8], [110, 45, 31]),
   (19, 2, [6, 4, 4], [2, 5, 8], [110, 45, 29]),
   (20, 2, [6, 4, 4, 4], [2, 5, 8, 11], [109, 44, 29, 24]),
   (21, 2, [6, 4, 4, 4], [2, 5, 8, 11], [109, 44, 28, 23]),
   (22, 2, [6, 4, 4, 4], [2, 5, 8, 11], [109, 44, 28, 22]),
   (23, 2, [6, 4, 4, 4], [2, 5, 8, 11], [109, 44, 28, 21]),
   (24, 2, [6, 4, 4, 4, 4], [2, 5, 8, 11, 14], [109, 44, 28, 21, 18]),
   (25, 2, [6, 4, 4, 4, 4], [2, 5, 8, 11, 14], [109, 44, 28, 21, 17]),
   (26, 2, [6, 4, 4, 4, 4], [2, 5, 8, 11, 14], [109, 44, 28, 21, 17]),
   (27, 2, [6, 4, 4, 4, 4], [2, 5, 8, 11, 14], [109, 44, 28, 21, 17]),
   (28, 2, [6, 4, 4, 4, 4, 4], [2, 5, 8, 11, 14, 17], [109, 44, 28, 21, 17, 15]),
   (29, 2, [6, 4, 4, 4, 4, 4], [2, 5, 8, 11, 14, 17], [109, 44, 28, 21, 17, 15]),
   (30, 2, [6, 4, 4, 4, 4, 4], [2, 5, 8, 11, 14, 17], [109, 44, 28, 21, 17, 15]),
   (16, 3, [6, 4, 4], [3, 6, 9], [74, 39, 30]),
   (17, 3, [6, 4, 4], [3, 6, 9], [74, 38, 28]),
   (18, 3, [6, 4, 4], [3, 6, 9], [73, 37, 27]),
   (19, 3, [6, 4, 4], [3, 6, 9], [73, 37, 26]),
   (20, 3, [6, 4, 4, 4], [3, 6, 9, 12], [73, 37, 25, 22]),
   (21, 3, [6, 4, 4, 4], [3, 6, 9, 12], [73, 37, 25, 20]),
   (22, 3, [6, 4, 4, 4], [3, 6, 9, 12], [73, 37, 25, 20]),
   (23, 3, [6, 4, 4, 4], [3, 6, 9, 12], [73, 37, 25, 19]),
   (24, 3, [6, 4, 4, 4, 4], [3, 6, 9, 12, 15], [73, 37, 25, 19, 17]),
   (25, 3, [6, 4, 4, 4, 4], [3, 6, 9, 12, 15], [73, 37, 25, 19, 16]),
   (26, 3, [6, 4, 4, 4, 4], [3, 6, 9, 12, 15], [73, 37, 25, 19, 16]),
   (27, 3, [6, 4, 4, 4, 4], [3, 6, 9, 12, 15], [73, 37, 25, 19, 16]),
   (28, 3, [6, 4, 4, 4, 4, 4], [3, 6, 9, 12, 15, 18], [73, 37, 25, 19, 16, 15]),
   (29, 3, [6, 4, 4, 4, 4, 4], [3, 6, 9, 12, 15, 18], [73, 37, 25, 19, 16, 14]),
   (30, 3, [6, 4, 4, 4, 4, 4], [3, 6, 9, 12, 15, 18], [73, 37, 25, 19, 16, 15]),
   (16, 4, [6, 4, 4], [4, 7, 10], [56, 33, 27]),
   (17, 4, [6, 4, 4], [4, 7, 10], [55, 32, 25]),
   (18, 4, [6, 4, 4], [4, 7, 10], [55, 32, 24]),
   (19, 4, [6, 4, 4], [4, 7, 10], [55, 32, 23]),
   (20, 4, [6, 4, 4, 4], [4, 7, 10, 13], [55, 32, 23, 20]),
   (21, 4, [6, 4, 4, 4], [4, 7, 10, 13], [55, 32, 23, 19]),
   (22, 4, [6, 4, 4, 4], [4, 7, 10, 13], [55, 32, 23, 18]),
   (23, 4, [6, 4, 4, 4], [4, 7, 10, 13], [55, 32, 23, 18]),
   (24, 4, [6, 4, 4, 4, 4], [4, 7, 10, 13, 16], [55, 32, 23, 18, 16]),
   (25, 4, [6, 4, 4, 4, 4], [4, 7, 10, 13, 16], [55, 32, 23, 18, 15]),
   (26, 4, [6, 4, 4, 4, 4], [4, 7, 10, 13, 16], [55, 32, 23, 18, 15]),
   (27, 4, [6, 4, 4, 4, 4], [4, 7, 10, 13, 16], [55, 32, 23, 18, 15]),
   (28, 4, [6, 4, 4, 4, 4, 4], [4, 7, 10, 13, 16, 19], [55, 32, 23, 18, 15, 14]),
   (29, 4, [6, 4, 4, 4, 4, 4], [4, 7, 10, 13, 16, 19], [55, 32, 23, 18, 16, 14]),
   (30, 4, [6, 4, 4, 4, 4, 4], [4, 7, 10, 13, 16, 19], [55, 32, 23, 18, 16, 14])]

#guard refConfigs.length = 60
#guard refConfigs.all fun (n, r, folds, rates, queries) ↦
  decide ((Whir.ladder n r).map (fun ls ↦
    (ls.map (·.fold), ls.map (·.logInvRate), ls.map (·.queries))) = some (folds, rates, queries))

/-! ## Keccak GKR and the RMFE (`keccak.rs`) -/

#guard (alongPairs.map fun (j, k) ↦ keccakAlong j k) =
    [64, 319, 192, 127, 1064, 1535, 1280]

#guard (transposeProbe) =
    (1600, [(e 0xca8abc6d967083b1 0x23e90670f9332354), (e 0xe18c283116a57e56 0x3d63a0587881af69)],
     (e 0x18512301d3bb1def 0x58f71514239c1028))

#guard (keccakInstanceWeights (fe 600)) =
    [(e 0xa52fefc1ac0d7a0 0xaafd3b9a726acd34), (e 0xacfe43ba7bb6e9bd 0x5a7f7f3b1a274ba),
     (e 0x2332778e532fc3ec 0xf6d55c6b09decc68), (e 0x171aadeba89d3bfe 0xc46ffcbc452f4842),
     (e 0x1884961b9484a0b3 0xe15bd89b05d5a7aa), (e 0x7a84ab7916508023 0x940a4d7330a93a0b),
     (e 0x3a8e63c129aa464a 0x3bc6c1f50e7c6af2), (e 0x159f64052fdb06ca 0x6f9caf57bf95618c),
     (e 0xc289527a4cd91db7 0xe3ffa88c291323a4), (e 0x2452c1cde88ed6f0 0x632e5b58ef41269a),
     (e 0xa45b3f2a2c038545 0xed0ae5a668a1567c), (e 0x1795531c103995e4 0x1ff11c0eb8ee98ca),
     (e 0xfc501772b3dd0922 0x4086d18d1e79f0f7), (e 0xa3ccb4106931fc89 0x7249f88792352b6a),
     (e 0x3356022b7c67f956 0xaf170f5564911e72), (e 0xb6c9bb9d329b71bd 0x65a3d0bc80700cb7)]

#guard (slotProbe 0 2) =
    (64, true, (e 0xee64d4d570e2c99e 0x44df39a864249bb5))

#guard (slotProbe 1 1) =
    (64, true, (e 0xcc1c5bf753aae3d9 0x9b117bda43b57d11))

#guard (rmfeEmbed) =
    [0x40c50b, 0x7f79f2, 0x4b4e0a, 0x72740c, 0x5357da, 0x1d1c9e, 0x4be6e, 0x785246, 0x97cdc,
     0x109e7e, 0x1f1454, 0x213cfc, 0x4cfcc8, 0x775770, 0x187386, 0x818a16]

#guard (rmfeProject) =
    [0x1, 0x7fffffffffff, 0x274e9d3a74e9, 0x1d3a74e9d3a7, 0x65cb972e5cb9, 0x5cb972e5cb97,
     0x6690aec7cd21, 0x5d8f9a42bb1f, 0x73485763e690, 0x3750967c6ea1, 0x12cf8dd4259f, 0x1ba84b3e3750,
     0xad0c9f715a1, 0x64fb8ad0c9f, 0x456864fb8ad0, 0x400000000000]

#guard (carrylessInputs.map fun (a, b) ↦ carryless a b) =
    [0xbee80b8, 0x5d073452, 0x436b037e, 0x18ea27ac]

#guard (keccakConstants) =
    [12, 2, 1, 6, 9, 1600, 11, 5, 64, 16, 24, 47, 3, 4, 16, 30]

#guard (ringMapWidth) = 8

/-! ## Keccak-f, Keccak-256 and the sponge (`hash.rs`, `transcript.rs`) -/

#guard (keccakRC) =
    [0x1, 0x8082, 0x800000000000808a, 0x8000000080008000, 0x808b, 0x80000001, 0x8000000080008081,
     0x8000000000008009, 0x8a, 0x88, 0x80008009, 0x8000000a, 0x8000808b, 0x800000000000008b,
     0x8000000000008089, 0x8000000000008003, 0x8000000000008002, 0x8000000000000080, 0x800a,
     0x800000008000000a, 0x8000000080008081, 0x8000000000008080, 0x80000001, 0x8000000080008008]

#guard (keccakRho) =
    [0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14]

#guard ((List.range 25).map keccakPi) =
    [0, 10, 20, 5, 15, 16, 1, 11, 21, 6, 7, 17, 2, 12, 22, 23, 8, 18, 3, 13, 14, 24, 9, 19, 4]

#guard ((keccakF1600 (Vector.replicate 25 0)).toList) =
    [0xf1258f7940e1dde7, 0x84d5ccf933c0478a, 0xd598261ea65aa9ee, 0xbd1547306f80494d,
     0x8b284e056253d057, 0xff97a42d7f8e6fd4, 0x90fee5a0a44647c4, 0x8c5bda0cd6192e76,
     0xad30a6f71b19059c, 0x30935ab7d08ffc64, 0xeb5aa93f2317d635, 0xa9a6e6260d712103,
     0x81a57c16dbcf555f, 0x43b831cd0347c826, 0x1f22f1a11a5569f, 0x5e5635a21d9ae61,
     0x64befef28cc970f2, 0x613670957bc46611, 0xb87c5a554fd00ecb, 0x8c3ee88a1ccf32c8,
     0x940c7922ae3a2614, 0x1841f924a2c509e4, 0x16f53526e70465c2, 0x75f644e97f30a13b,
     0xeaf1ff7b5ceca249]

#guard ((keccakF1600 sampleState).toList) =
    [0xbbe1405ddfd4d06, 0x7f37a0e9b1a487eb, 0x195143c6ce53241d, 0xb8a443fd55d7d522,
     0x89514f07bdba7312, 0xca68843d05b5aac6, 0x802928c9e382be60, 0xe4bb1d37351316a2,
     0xed82178ba36c6c44, 0x668e7096d504c916, 0xb1ac7a0875df7f9b, 0x3e479b5291050c73,
     0xb1573b6dd3be8144, 0x74420236af80cfa3, 0x2769a953a41029d6, 0x1f86b6fbc1404d8e,
     0xccbe7b0f314596d9, 0xfe2296c7376aa897, 0xb16409a354083080, 0xcd78dd9c6eeca6bd,
     0xf02b5b250b1d4ac0, 0x6b047a98a5cb1964, 0x2bcbc7b0dfad862a, 0x9e0ba50e8f8fae6f,
     0xe7d070bfdd49fed4]

#guard ((keccak256 (sampleBytes 0)).toList) =
    [0x3c23f7860146d2c5, 0xc003c7dcb27d7e92, 0x3b2782ca53b600e5, 0x70a4855d04d8fa7b]

#guard ((keccak256 (sampleBytes 1)).toList) =
    [0x6b6b97284816509f, 0x748c719ca39e47aa, 0xfd7db621250dbc5b, 0x571071c9bd4c47e8]

#guard ((keccak256 (sampleBytes 135)).toList) =
    [0x4c3a6cdb4861e7b4, 0x8e3fb7d478522d60, 0xd0abd178b425d805, 0xf6683088fdcbb3bf]

#guard ((keccak256 (sampleBytes 136)).toList) =
    [0x2459abe9e2ad4dc9, 0xcc4da5f34f87f824, 0xf5a2b9fc81c9e5ec, 0x722aa2b67cb704de]

#guard ((keccak256 (sampleBytes 137)).toList) =
    [0xb8195730b3e8b689, 0x1913cb375b2aeda0, 0x7ee5d01df31a5914, 0xe16d946a453d8461]

#guard ((keccak256 (sampleBytes 300)).toList) =
    [0xf25b66e14591a877, 0x90835b86e8868d1, 0xbc3230d92c88bc08, 0x7aeb3db2a1ec8e09]

/- `Sponge::duplex` from `sampleState`, and `sample`'s challenge -/
#guard (duplexProbe []) =
    ([0xd85b3e2fd2e1eb4f, 0xd3d1d5831bc8efcd, 0xa4056d0625b721fd, 0xddd7a11d7b68e7fe,
      0x9c33be148cdcabe2, 0x6c3a5f7fef476758, 0x1ab2897d42fb581f, 0xeb832fbbd7f4b214,
      0x141607deb5d4b3fa, 0x8844798c929486fe, 0x39555ca203fd1aa6, 0x5de5afd0072b7e9c,
      0x35e50f807d9e647b, 0x1f806ab5f98c1db7, 0x9d3e256d10db6635, 0x3f030c8a70795ae6,
      0xb236683aae5f33ca, 0xe3b607cb1d995ac1, 0xfd8ef7d66bf2cef9, 0x337a8960ca3f21fa,
      0xeef74e55ee09f48d, 0x87c2c8cfa1a748a9, 0x8184d72c67c99ec0, 0x39e027c8d413076,
      0x163dcd923875c144], (e 0xd85b3e2fd2e1eb4f 0xd3d1d5831bc8efcd))

#guard (duplexProbe [(fe 800, 1), (fe 801, 4), (fe 802, 1)]) =
    ([0xf0717f39d6afa2cc, 0x9cecec659afe4d18, 0xbfd3c7ad7e7bfe0f, 0x9a10c4a913fff9fa,
      0x61da3ae809ee3543, 0x802f2580b48b90a5, 0xf5df65913686d948, 0x8f33a0dc707c8189,
      0x904235e575cf25d3, 0x55a7cacf41897802, 0x7e027766f7a7c70b, 0xc955060de4248bd4,
      0x3a354b2564540357, 0x6e86585b19ea95c7, 0x827d6359de30c158, 0x235777594084262c,
      0x11b945aab9196735, 0xef21aeb8dfa01499, 0xfb54ef2b21e2d600, 0xa356dd21cd02c0fe,
      0x74059c856f05cecd, 0xc9357a096f17c098, 0x49765849639dd2c2, 0xabba0d79f75283f2,
      0xc05eee3800036462], (e 0xf0717f39d6afa2cc 0x9cecec659afe4d18))

#guard (duplexProbe [(fe 803, 1), (fe 804, 1), (fe 805, 4), (fe 806, 1)]) =
    ([0xebeedba924c61115, 0x8cef96123e1e8fc3, 0xebdb8ec315092f44, 0x647a3a0fd5194aed,
      0xc07a703d5877f22e, 0x69c9e1e1c31e1603, 0xc47d361e8e9439a4, 0x6b49f9ff062fb999,
      0x3cfca783247dde82, 0x66e191543392af8e, 0xae8eb3980bd2a81a, 0x3d4539159a206168,
      0xa63b1163d3fb8b76, 0x81deb06e326f0747, 0xbb6dd3aca9d675e6, 0xc8e113c0ee5ae16,
      0x8c810e5cb255fb21, 0xf961b8d5430035e4, 0xb0f63460d37e3300, 0x7420bc4681ec058b,
      0x22641ca1b086370e, 0xcc1ea014cc013c50, 0x9f9607c115a452af, 0x3524e4d53dd759d3,
      0x4c018208d2a28b5c], (e 0xebeedba924c61115 0x8cef96123e1e8fc3))

/- `Sponge::absorb_nonce` after one waiting scalar, and after four (the nonce's absorb permutes
them first) -/
#guard (nonceProbe [(fe 808, 1)] (fe 809)) =
    (0x9c5d2e33fcd86254,
     [0xec443f4173e43f31, 0xaf4f713894ff670a, 0x9c5d2e33fcd86254, 0x795249884078a412,
      0x9edc32a503c1e727, 0xe49dfa22c35f016a, 0x993f66ce8008b63e, 0x10900e1cf0a00d3f,
      0x6a0bdf664bc2ffb3, 0xeca1d084da04273b, 0x4e8354571163e60c, 0x3f0be7f5005cf7c5,
      0x11c65905c6043e49, 0x3f577fcf0e4ba908, 0xbde80a5fcf417d36, 0x6c4833d43ed1b03e,
      0x4bf94068f683554, 0x1ef3ded7f55f5788, 0x4022bc21004c55a4, 0x7162a415c46111a1,
      0xc2abd0b1b85088ce, 0xb8c4faaf94944e89, 0x21fdc980fdc3c695, 0xb313e520d5f653fd,
      0x348e1631cac8b971], some (e 0xec443f4173e43f31 0xaf4f713894ff670a))

#guard (nonceProbe [(fe 810, 1), (fe 811, 1), (fe 812, 1), (fe 813, 1)] (fe 814)) =
    (0xbfab84464e4d4ec9,
     [0x12c2014d119c4383, 0xd30e6b61a8acbea6, 0xbfab84464e4d4ec9, 0xde53fd3050428bea,
      0x24cd3c07ea6c879, 0x22df8b7a3d14a47f, 0x11e565a0d9904513, 0xd5bd00d7165a4b3b,
      0xac25ea648b2bb85d, 0x7bd4bb1675d189d6, 0x189f284ecc1cb5a9, 0x960571e8adf5b966,
      0x2813dc00fafdee8, 0xd7c7913f4fe07f99, 0xcb67407e583cc273, 0x7ee0262f734d2241,
      0x57ff37dda9bc7a33, 0xccb8fb6dc40e9827, 0x48d91e433375b538, 0x3894a1e093b47fa9,
      0x3c6a117f5daa1975, 0x31c4a9d7468387bd, 0x1b1c4426ba8af87d, 0x2fbc9cb1d64538c,
      0xbfc7c9b13da31fc0], some (e 0x12c2014d119c4383 0xd30e6b61a8acbea6))

/-! ## The tag, the IV and the seed (`layout.rs`, `bytecode.rs`, `transcript.rs`) -/

#guard (versionTag) =
    [108, 101, 97, 110, 118, 109, 45, 118, 49]

#guard ((keccak256 (sampleBytecode.flatMap K.toBytes)).toList) =
    [0x5ee1b7ed85bd7f40, 0xe30f235e90f241ba, 0x2c5175ed6d0af92b, 0x99aaaff5bf8937b8]

#guard ((fiatShamirIv sampleBytecode).toList) =
    [0x388a48ed64bdc88, 0xc56fdc9a5bbfc60b, 0x9177eb91e2b31ac9, 0x60b15bff515ffc9a]

#guard (samplePublicInput.toList) =
    [0xdfcab5a08b76614c, 0x87725d48331e09f4, 0x2f1a05f0dbc6b19c, 0xd7c2ad98836e5944]

#guard ([(digestHalves samplePublicInput).1, (digestHalves samplePublicInput).2]) =
    [(e 0xdfcab5a08b76614c 0x87725d48331e09f4), (e 0x2f1a05f0dbc6b19c 0xd7c2ad98836e5944)]

#guard ((seed sampleBytecode samplePublicInput).toList) =
    [0x9d7d4eb7cc97e374, 0xb724b7ba8b1c3421, 0x14d14d64d9182a28, 0x1c1a4bc2a316a26c,
     0xe410600d8d0706c8, 0x4dd78f280a2db761, 0x50dc9d77b0f34b74, 0x2d2743bc3e4da033,
     0xf266f7f60648d489, 0xa55b889e0f5c5da7, 0x2f671d6a94b8c6aa, 0xcda35ca721ea79e1,
     0xbbcb869a8f7e0386, 0xa00ae0785cf727df, 0xd9b984d1efc0d523, 0x354259a0706ebaeb,
     0x7fa694082e9b86c0, 0xe22eb021ce923a65, 0x43dc097da59a77b9, 0xa5084af5f4153506,
     0xb1ced25d740086b4, 0x26aaa2d4102a5604, 0x60ee864b6821e0aa, 0x8f239df976d3a9ef,
     0x6d5f9ca9bf33253e]

end LeanVMTests.Protocol.Verifier.Helpers
