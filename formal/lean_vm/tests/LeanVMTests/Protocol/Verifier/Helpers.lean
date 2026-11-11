import LeanVM.Protocol.Verifier

/-!
# Verifier helper tests: differential against the verifier at its pins

Every expected value below is the verifier's at leanVM `4af2cdddd7cd41b9df2cc7e123e314a91b0b4462`
on inputs drawn from the word generator `fw`, which the driver mirrors exactly, but the tag, the
IV and the seed, taken at `990b935263dc7f793f280914f262ca7955ddc3e0` (the only functions checked
here that changed between the two), and the tables, the `q_keccak` slots, the output columns and
`build_layout`'s sample layout and bus blocks, taken at leanVM main
`40f877dc2c858f013c5974ab71ca594b31a7aec9` (the `KECCAK` table's output flags; the driver checked
first to print the previous values at `5e3ade21`); the drivers live in the port's scratch, not in
the repository. The line citations are to `crates/verifier/src/` at `40f877dc`. Compiled checks
(`#guard`): `E` multiplication does not reduce in the kernel from module files.

Covered: `powers`, `eq_kernel`, `multilinear_eval` (on `E` and on lifted `K` tables), `eq_eval`,
`dot`, `index_mle`, `poly_eval`, `gpow`, `padding_weight`, `log2_ceil`, `log2_strict`,
`selector_point`; `subspace_roots`, `induced_weight`, `ext_row`, the enforced sum of a WHIR
level; the ring map `ring_map`, `ring_weight`, and `ring_switch`'s Frobenius coefficients, weight
and target; `stack_offsets`, `Placement::stack_point` and `eq_above`; the tables' columns, widths,
global bases, log-height floors, constraint counts, count columns and padding rows,
`jump_constraints`, `keccak_cell_lanes`, `layout_limb`, the `q_keccak` slots (`qkeccak_slot`) and
output columns; `build_layout` on a sample bytecode and sizes (log-heights, stack log-size, every
placement, every bus block's shape and flushed tuple at a sample row), `bus_layout` of the three
sides; `derive_config` on all 68 admissible pairs (at `aca3ea6a`); `along`, `linear_transpose`,
`instance_weights`, the slot weights of `open`, the RMFE's factors, `RMFE_EMBED`, `RMFE_PROJECT`,
the carry-less product and division and the Keccak reduction's constants; `KECCAK_RC`,
`KECCAK_RHO`, `KECCAK_PI`, `keccak_f`, `keccak_hash` across the block boundary, the sponge's
`duplex` and `sample`; `TAG` (`versionTag`), the IV (`fiatShamirIv`), the public input's halves,
and the Fiat-Shamir seed (`Sponge::new`: Keccak-f of `iv ‖ pi ‖ 0`). `build_layout`'s
rejections are checked against what the verifier rejects on the same inputs.
-/

namespace LeanVMTests.Protocol.Verifier.Helpers

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile

/-! ## Inputs, as the driver draws them -/

/-- The driver's 64-bit word generator. -/
def fw (k lane : ℕ) : ℕ :=
  ((k + 1) * 0x9E3779B97F4A7C15 + lane * 0xD1B54A32D192ED03 + 0x632BE59BD9B4E019) % 2 ^ 64

/-- An `E` element from its three limbs. -/
def e (c0 c1 c2 : ℕ) : E := E.ofLimbs (K.ofBits c0) (K.ofBits c1) (K.ofBits c2)

/-- The driver's `fe(k)`. -/
def fe (i : ℕ) : E := e (fw i 0) (fw i 1) (fw i 2)

/-- `fe(a), …, fe(a + n - 1)`. -/
def fes (a n : ℕ) : List E := (List.range n).map fun i ↦ fe (a + i)

/-- A lifted `K` table of sixteen entries. -/
def kTable : List E := (List.range 16).map fun i ↦ ofK (K.ofBits (fw i 5))

/-- Three lifted `K` rows of four words. -/
def kRows : List (List E) :=
  (List.range 3).map fun q ↦ (List.range 4).map fun j ↦ ofK (K.ofBits (fw (10 * q + j) 7))

/-- A sample placement (its two checks printed at the pin, `../leanvm-rev`). -/
def samplePlacement : Placement := { variableCount := 3, index := 0b1011001 }

/-- The sample bytecode: 32 words, so `log_bytecode = 1`. -/
def sampleBytecode : List K := (List.range 32).map fun i ↦ K.ofBits (fw i 9)

/-- The sample row counts: `xor, mul, set, deref, jump, keccak`. Their log-heights are
`2, 1, 1, 2, 2, 9`, `KECCAK`'s raised to its floor `KECCAK_MIN_STEPS_LOG`. -/
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
  (bl.depth, (bl.framework ++ bl.tables).map fun q ↦ (q.variableCount, q.index))

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
  let s := keccakF1600 (duplexInput ⟨sampleState, pending⟩)
  (s.toList, challengeOf s)

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
number of rows, whether each is 64 wide, and all of them batched by powers of `fe 620`. At the pin
they are no function of their own: `open` (`keccak.rs:208-221`) sums them against the slot
challenges' eq weights. The expected values are those of the separate function of the previous pin
`3375f7a13`. -/
def slotProbe (first count : ℕ) : ℕ × Bool × E :=
  let w := keccakSlotWeights 9 sampleClaim first count
  (w.length, w.all (·.length == 64), dot (powers (fe 620) 4096) w.flatten)

/-- The pairs the carry-less product is probed at: a 20-bit and a 12-bit polynomial. -/
def carrylessInputs : List (ℕ × ℕ) :=
  (List.range 4).map fun i ↦ (fw i 13 % 2 ^ 20, fw i 14 % 2 ^ 12)

/-- The pairs the carry-less division is probed at: a 40-bit dividend by a degree-11 divisor, then
two small ones. -/
def divmodInputs : List (ℕ × ℕ) :=
  (List.range 4).map (fun i ↦ (fw i 13 % 2 ^ 40, fw i 14 % 2 ^ 12 ||| 2 ^ 11)) ++
    [(0b1011, 0b10), (5, 0b100101)]

/-- The Keccak reduction's and the layout's constants, in the driver's order. -/
def keccakConstants : List ℕ :=
  [keccakDepth, keccakSegments, keccakSegmentBits, qkeccakSlotBits, keccakMinStepsLog, keccakBits,
    keccakLocalBits, keccakLaneBits, kBits, pack, embedBits, productBits, globalColumnCount,
    busBits, Whir.minLogStack, Whir.maxLogStack]

/-! ## Constants and conventions -/

#guard yE = y
#guard gen = ofK (K.ofBits 2)
#guard (buildLayout sampleBytecode 16 sampleRows).isSome
#guard sampleLayout.push.all fun b ↦ b.rows == sampleRows.getD b.owner 0
#guard sampleLayout.placements.length = globalColumnCount + tableWidths.sum

/- Every column a table's flushes name exists (`cols`'s `expect`, `layout.rs:105-112`): a missing
name would be `columnIndexByName`'s out-of-range index, the table's width. -/
#guard tables.all fun t ↦ (t.flushes.push ++ t.flushes.pull).all fun tuple ↦
  tuple.all fun f ↦ f.terms.all fun (m, _) ↦ m.all (· < t.width)

/-! ## `build_layout` rejects what the verifier rejects

On each input the driver ran `build_layout` and recorded whether it rejected. -/

/- A bytecode length that is not a power of two; one shorter than `2^BUS_BITS`; exactly
`2^BUS_BITS`. -/
#guard (buildLayout (sampleBytecode.take 24) 16 sampleRows).isNone
#guard (buildLayout (sampleBytecode.take 8) 16 sampleRows).isNone
#guard (buildLayout (sampleBytecode.take 16) 16 sampleRows).isSome
/- The memory window `[1, 32]` (at `aca3ea6a`). -/
#guard (buildLayout sampleBytecode 0 sampleRows).isNone
#guard (buildLayout sampleBytecode 1 sampleRows).isSome
#guard (buildLayout sampleBytecode 33 sampleRows).isNone
#guard (buildLayout sampleBytecode 32 sampleRows).isSome
/- The row cap `2^32`, on any table. -/
#guard (buildLayout sampleBytecode 16 [2 ^ 32 + 1, 2, 2, 4, 3, 5]).isNone
#guard (buildLayout sampleBytecode 16 [2 ^ 32, 2, 2, 4, 3, 5]).isSome
#guard (buildLayout sampleBytecode 16 [3, 2, 2, 4, 3, 2 ^ 32]).isSome
/- No `KECCAK` row is no rejection: the table's height is its floor. Past the floor it grows. -/
#guard ((buildLayout sampleBytecode 16 [3, 2, 2, 4, 3, 0]).map (·.tableLogHeights)) =
  some [2, 1, 1, 2, 2, 9]
#guard ((buildLayout sampleBytecode 16 [3, 2, 2, 4, 3, 600]).map (·.tableLogHeights)) =
  some [2, 1, 1, 2, 2, 10]
/- Not one row count per table (the Rust verifier reads exactly `N_TABLES`, `lib.rs:220`). -/
#guard (buildLayout sampleBytecode 16 [3, 2, 2, 4, 3, 5, 0]).isNone
#guard (buildLayout sampleBytecode 16 [3, 2, 2, 4, 3]).isNone

/-! ## `derive_config` outside the window -/

#guard (Whir.ladder 15 1).isNone ∧ (Whir.ladder 33 1).isNone
#guard (Whir.ladder 20 0).isNone ∧ (Whir.ladder 20 5).isNone

/-! ## Field and multilinear arithmetic (`field.rs:258-267`, `multilinear.rs`, `layout.rs:114`) -/

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

#guard ([0, 5, 11, 16].map (paddingWeight (fes 120 4))) =
    [(e 0x1 0x0 0x0), (e 0x640f7f969c5b2061 0x90deeb5bf84036c7 0xd25ce47a63bd7fdc),
     (e 0xa2ae4697e637e700 0x2ae7b1c3c637f562 0xb87a7de37e6c85f9), (e 0x0 0x0 0x0)]

#guard ([0, 1, 2, 3, 5, 64, 65, 2 ^ 20].map log2Ceil) =
    [0, 0, 1, 2, 3, 6, 7, 20]

#guard ([16, 15, 17, 1, 0, 2 ^ 20].map log2Strict) =
    [some 4, none, none, some 0, none, some 20]

#guard (selectorPoint 13 6) =
    [(e 0x1 0x0 0x0), (e 0x0 0x0 0x0), (e 0x1 0x0 0x0), (e 0x1 0x0 0x0), (e 0x0 0x0 0x0),
     (e 0x0 0x0 0x0)]

/-! ## WHIR helpers (`whir.rs:65-126`, `:197-211`) -/

#guard (subspaceRoots 12) =
    [(e 0x1 0x0 0x0), (e 0x6 0x0 0x0), (e 0x168 0x0 0x0), (e 0x1166880 0x0 0x0),
     (e 0x11616686880801b 0x0 0x0), (e 0x726b6e3c6e39234e 0x0 0x0), (e 0x796adf34d64462c2 0x0 0x0),
     (e 0xf1060866be6fa9c 0x0 0x0), (e 0x6a06f1b0a76acb05 0x0 0x0), (e 0xd2d14e471a7186d9 0x0 0x0),
     (e 0x6d55ab94bb5f9605 0x0 0x0), (e 0xd08c5570c6423a2a 0x0 0x0), (e 0xa0ca298b954731 0x0 0x0)]

#guard (inducedWeight 5 [3, 17, 30, 0] (powers (fe 60) 4) [fe 61, fe 62, fe 63, fe 64, fe 65]) =
    (e 0x2ac3fadca39d4b81 0x1629ae443f03334e 0x4f97f27d36b81fbf)

#guard (extRow ((List.range 6).map fun i ↦ K.ofBits (fw i 6))) =
    [(e 0xeba31c864270ea40 0x89da963fc1bb6655 0x28120ff94105e26a),
     (e 0xc64989b2c0505e7f 0x6481036c3f9ada94 0x2b87d25bee556a9)]

#guard (extRow ((List.range 7).map fun i ↦ K.ofBits (fw i 6))) =
    [(e 0xeba31c864270ea40 0x89da963fc1bb6655 0x28120ff94105e26a),
     (e 0xc64989b2c0505e7f 0x6481036c3f9ada94 0x2b87d25bee556a9), (e 0xa0eff6df3e2fd2be 0x0 0x0)]

#guard (enforcedSum kRows [fe 66, fe 67] [fe 68, fe 69, fe 70]) =
    (e 0xda0d62a8fab09447 0xf78fdc7451a4bb0a 0x2bb794332b986985)

/-! ## Ring switching (`ring_switch.rs:8-54`) -/

/- `ring_switch`'s Frobenius coefficients, read off its weight closure -/
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

#guard (ringWeight (fes 71 4) (fes 75 4) (fes 100 64)) =
    (e 0x6f0eb6aeec94b739 0xa58b39c32b7e22f6 0x7a7dd4c24feb966a)

/- `ring_switch`'s weight `W` at `r' = fes 75 4`, and its target on the slices `fes 130 64` -/
#guard (ringWeight (fes 71 4) (fes 75 4) (ringCoefficients (fes 80 6))) =
    (e 0x328877f69da26c34 0x790f74e5b6d4aeff 0x9e6f2eef8593477c)

#guard (polyEval ((fes 130 64).map (phiMap · (fes 80 6))) gen) =
    (e 0xb69e86537be854df 0xc66fc5b97b11e1ed 0x80a34c7b2b8c9e71)

/-! ## Placements (`multilinear.rs:114-148`) -/

#guard (stackOffsets [3, 5, 5, 0, 2, 5, 1]) =
    ([96, 0, 32, 110, 104, 64, 108], 7)

#guard (samplePlacement.stackPoint [fe 90, fe 91, fe 92] 9) =
    [(e 0xa0e42a8c192efb90 0x729974beeac1e893 0x444ebef1bc54d596),
     (e 0x3f1ba445987977a5 0x10d0ee786a0c64a8 0xe28638ab3b9f51ab),
     (e 0xdd531dff17c3f3ba 0xaf086831e956e0bd 0x80bdb264bae9cdc0), (e 0x1 0x0 0x0), (e 0x1 0x0 0x0),
     (e 0x0 0x0 0x0), (e 0x1 0x0 0x0), (e 0x0 0x0 0x0), (e 0x0 0x0 0x0)]

#guard (samplePlacement.eqAbove (fes 93 9)) =
    (e 0xb55551000c96060f 0x491ccd354400b340 0x66d12dcfc1d3da0a)

/-! ## The tables (`layout.rs:130-490`) -/

#guard (tables.map Table.columns) =
    [["pc", "fp", "o_a", "o_b", "o_c", "va_0", "va_1", "va_2", "vb_0", "vb_1", "vb_2", "cnt_a",
      "cnt_b", "cnt_c", "cnt_bc"],
     ["pc", "fp", "o_a", "o_b", "o_c", "va_0", "va_1", "va_2", "vb_0", "vb_1", "vb_2", "cnt_a",
      "cnt_b", "cnt_c", "cnt_bc"],
     ["pc", "fp", "o", "k_0", "k_1", "k_2", "cnt", "cnt_bc"],
     ["pc", "fp", "o1", "o2", "o3", "f_pc", "f_fp", "ptr", "v3_0", "v3_1", "v3_2", "cnt_ptr",
      "cnt_target", "cnt_local", "cnt_bc"],
     ["pc", "fp", "o_c", "o_d", "o_f", "v_cond", "v_pc", "v_fp", "cnt_c", "cnt_d", "cnt_f",
      "cnt_bc", "w", "b"],
     ["pc", "fp", "o_m0", "o_m1", "o_m2", "o_m3", "o_tail", "o_b8", "o_cap", "o_out", "odd_in",
      "odd_out", "out_two", "out_all", "free", "in_0", "in_1", "in_2", "in_3", "in_4", "in_5",
      "in_6", "in_7", "in_8", "in_9", "in_10", "in_11", "in_12", "in_13", "in_14", "in_15",
      "in_16", "in_17", "in_18", "in_19", "in_20", "in_21", "in_22", "in_23", "in_24", "out_0",
      "out_1", "out_2", "out_3", "out_4", "out_5", "out_6", "out_7", "out_8", "out_9", "out_10",
      "out_11", "out_12", "out_13", "out_14", "out_15", "out_16", "out_17", "out_18", "out_19",
      "out_20", "out_21", "out_22", "out_23", "out_24", "cnt_0", "cnt_1", "cnt_2", "cnt_3",
      "cnt_4", "cnt_5", "cnt_6", "cnt_7", "cnt_8", "cnt_9", "cnt_10", "cnt_11", "cnt_12", "cnt_13",
      "cnt_14", "cnt_15", "cnt_16", "cnt_17", "cnt_18", "cnt_19", "cnt_20", "cnt_21", "cnt_22",
      "cnt_23", "cnt_24", "cnt_25", "cnt_bc"]]

#guard (tableWidths) =
    [15, 15, 8, 15, 14, 92]

#guard (globalColumnBases) =
    [6, 21, 36, 44, 59, 73]

#guard (tableLogFloors) =
    [0, 0, 0, 0, 0, 9]

#guard (tables.map Table.nConstraints) =
    [0, 0, 0, 0, 2, 0]

#guard (tables.map Table.countColumns) =
    [[11, 12, 13, 14],
     [11, 12, 13, 14],
     [6, 7],
     [11, 12, 13, 14],
     [8, 9, 10, 11],
     [65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87,
      88, 89, 90, 91]]

#guard (tables.map fun t ↦ t.padding.map eToNat) =
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     [0, 0, 0, 0, 0, 0, 0, 0],
     [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0xf1258f7940e1dde7, 0x84d5ccf933c0478a, 0xd598261ea65aa9ee,
      0xbd1547306f80494d, 0x8b284e056253d057, 0xff97a42d7f8e6fd4, 0x90fee5a0a44647c4,
      0x8c5bda0cd6192e76, 0xad30a6f71b19059c, 0x30935ab7d08ffc64, 0xeb5aa93f2317d635,
      0xa9a6e6260d712103, 0x81a57c16dbcf555f, 0x43b831cd0347c826, 0x1f22f1a11a5569f,
      0x5e5635a21d9ae61, 0x64befef28cc970f2, 0x613670957bc46611, 0xb87c5a554fd00ecb,
      0x8c3ee88a1ccf32c8, 0x940c7922ae3a2614, 0x1841f924a2c509e4, 0x16f53526e70465c2,
      0x75f644e97f30a13b, 0xeaf1ff7b5ceca249, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]

#guard (jumpConstraints (fes 400 14)) =
    [(e 0x74c3d55b8563cc8d 0xe14fe16b59b07f5b 0xc8d072e655497420),
     (e 0xa796fc834b5ba71f 0x101f01afc165bbbb 0xa16e9550118705e7)]

#guard ([false, true].map fun odd ↦ (List.range 13).map (LeanVM.Semantics.cellLanes odd)) =
    [[(some 0, some 1), (some 2, some 3), (some 4, some 5), (some 6, some 7), (some 8, some 9),
      (some 10, some 11), (some 12, some 13), (some 14, some 15), (some 16, none),
      (some 17, some 18), (some 19, some 20), (some 21, some 22), (some 23, some 24)],
     [(none, some 0), (some 1, some 2), (some 3, some 4), (some 5, some 6), (some 7, some 8),
      (some 9, some 10), (some 11, some 12), (some 13, some 14), (some 15, some 16),
      (some 17, some 18), (some 19, some 20), (some 21, some 22), (some 23, some 24)]]

#guard ((layoutLimb (some 3) (some 5) 7 (some 9)).evaluate fun i ↦ fe (150 + i)) =
    (e 0x85ec37342d31c0a9 0x6c27ed054ad7bd99 0x88bbd549302a0e)

#guard ((layoutLimb none (some 5) 7 (some 9)).evaluate fun i ↦ fe (150 + i)) =
    (e 0xfc746ee9dfa27169 0x100d5386fe7e4d15 0xdc3df7492cc30e19)

#guard ((layoutLimb (some 3) none 7 none).evaluate fun i ↦ fe (150 + i)) =
    (e 0x26e523742a1b7be2 0xded54b00374ddb4d 0x340c90abd786cf33)

#guard ((layoutLimb none none 7 none).evaluate fun i ↦ fe (150 + i)) =
    (e 0x0 0x0 0x0)

#guard ((layoutLimb none none 7 (some 9)).evaluate fun i ↦ fe (150 + i)) =
    (e 0x45d7f98b68426d39 0x178d43be39d55a3c 0xe9428df10b68473f)

#guard ((layoutLimb (some 4) (some 4) 7 none).evaluate fun i ↦ fe (150 + i)) =
    (e 0x2ec298ebebce00d0 0x77e31ebd60edd3 0xd22d2d518ef3dad6)

#guard ((layoutLimb none (some 9) 7 (some 9)).evaluate fun i ↦ fe (150 + i)) =
    (e 0x45d7f98b68426d39 0x178d43be39d55a3c 0xe9428df10b68473f)

/- `build_layout`'s `q_keccak` slots (`qkeccak_slot`) and `outputs`, and the output lanes' columns -/
#guard ((List.range 168).filterMap fun c ↦ (keccakSlot c).map (c, ·)) =
    [(73, 50), (74, 51), (75, 52), (76, 53), (77, 54), (78, 55), (79, 56), (80, 57), (81, 58),
     (82, 59), (83, 60), (84, 61), (85, 62), (86, 63), (88, 0), (89, 1), (90, 2), (91, 3), (92, 4),
     (93, 5), (94, 6), (95, 7), (96, 8), (97, 9), (98, 10), (99, 11), (100, 12), (101, 13),
     (102, 14), (103, 15), (104, 16), (105, 17), (106, 18), (107, 19), (108, 20), (109, 21),
     (110, 22), (111, 23), (112, 24)]

#guard (keccakOutputColumns) =
    [113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131,
     132, 133, 134, 135, 136, 137]

/-! ## `build_layout` on the sample (`bus.rs:53-79`, `layout.rs:492-583`) -/

#guard (sampleLayout.tableLogHeights) =
    [2, 1, 1, 2, 2, 9]

#guard (sampleLayout.stackLog) =
    19

#guard (sampleLayout.logBytecode) =
    1

#guard (sampleLayout.placements.map (·.map fun p ↦ (p.variableCount, p.index))) =
    [some (16, 0), some (16, 65536), some (16, 131072), some (16, 196608), some (1, 309424),
     some (15, 262144), some (2, 309248), some (2, 309252), some (2, 309256), some (2, 309260),
     some (2, 309264), some (2, 309268), some (2, 309272), some (2, 309276), some (2, 309280),
     some (2, 309284), some (2, 309288), some (2, 309292), some (2, 309296), some (2, 309300),
     some (2, 309304), some (1, 309426), some (1, 309428), some (1, 309430), some (1, 309432),
     some (1, 309434), some (1, 309436), some (1, 309438), some (1, 309440), some (1, 309442),
     some (1, 309444), some (1, 309446), some (1, 309448), some (1, 309450), some (1, 309452),
     some (1, 309454), some (1, 309456), some (1, 309458), some (1, 309460), some (1, 309462),
     some (1, 309464), some (1, 309466), some (1, 309468), some (1, 309470), some (2, 309308),
     some (2, 309312), some (2, 309316), some (2, 309320), some (2, 309324), some (2, 309328),
     some (2, 309332), some (2, 309336), some (2, 309340), some (2, 309344), some (2, 309348),
     some (2, 309352), some (2, 309356), some (2, 309360), some (2, 309364), some (2, 309368),
     some (2, 309372), some (2, 309376), some (2, 309380), some (2, 309384), some (2, 309388),
     some (2, 309392), some (2, 309396), some (2, 309400), some (2, 309404), some (2, 309408),
     some (2, 309412), some (2, 309416), some (2, 309420), some (9, 287744), some (9, 288256),
     some (9, 288768), some (9, 289280), some (9, 289792), some (9, 290304), some (9, 290816),
     some (9, 291328), some (9, 291840), some (9, 292352), some (9, 292864), some (9, 293376),
     some (9, 293888), some (9, 294400), some (9, 294912), some (9, 262144), some (9, 262656),
     some (9, 263168), some (9, 263680), some (9, 264192), some (9, 264704), some (9, 265216),
     some (9, 265728), some (9, 266240), some (9, 266752), some (9, 267264), some (9, 267776),
     some (9, 268288), some (9, 268800), some (9, 269312), some (9, 269824), some (9, 270336),
     some (9, 270848), some (9, 271360), some (9, 271872), some (9, 272384), some (9, 272896),
     some (9, 273408), some (9, 273920), some (9, 274432), none, none, none, none, none, none,
     none, none, none, none, none, none, none, none, none, none, none, none, none, none, none,
     none, none, none, none, some (9, 295424), some (9, 295936), some (9, 296448),
     some (9, 296960), some (9, 297472), some (9, 297984), some (9, 298496), some (9, 299008),
     some (9, 299520), some (9, 300032), some (9, 300544), some (9, 301056), some (9, 301568),
     some (9, 302080), some (9, 302592), some (9, 303104), some (9, 303616), some (9, 304128),
     some (9, 304640), some (9, 305152), some (9, 305664), some (9, 306176), some (9, 306688),
     some (9, 307200), some (9, 307712), some (9, 308224), some (9, 308736)]

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
     (9, 5, 3, (e 0x295f303850cc44ae 0x2a75f12fa9759b1f 0x8d1125d19e1d7bb9)),
     (9, 5, 16, (e 0xe5f394bca1806783 0x60cc95d400bd2b7e 0xc09c9961d6f769c4)),
     (9, 5, 6, (e 0xcf9fccff0a082b33 0xf56977ad0a4cf607 0x7513a2c91dfd0649)),
     (9, 5, 6, (e 0x922c7bc0d7c591ac 0xa9877aa7f706c77e 0x31f108ade44012fb)),
     (9, 5, 6, (e 0x2f177f5c4d457990 0x4f4d90b19ab8a3d6 0x79df62b17a37bbe9)),
     (9, 5, 6, (e 0x2c618b6014272d08 0x76680dd7427bfbbd 0xd4698557ac4446d1)),
     (9, 5, 6, (e 0x850e972fd3f29dbc 0x6c9d678493790829 0xe7e4c266e8b8487f)),
     (9, 5, 6, (e 0xe92f9548b3346004 0xcb1faab0c0bb76ae 0x3410fdae1cb02386)),
     (9, 5, 6, (e 0x80cd0ff16b0d80d7 0x3b635b2b6195bc89 0x2b0b467cc56a36f8)),
     (9, 5, 6, (e 0x23dd18f3298bbdd5 0x54ce58d45c517aa4 0x859624456eb6a32a)),
     (9, 5, 6, (e 0x778df542131fe406 0xd6d9ef4b22805c00 0x355aca466469e69c)),
     (9, 5, 6, (e 0x6b07af9ca1271754 0xceacb7fd504f8239 0x2f90517d2dd4cb19)),
     (9, 5, 6, (e 0xd8269dac5bd129f6 0x445c01af5167cb3d 0x2ac36bfc1a185954)),
     (9, 5, 6, (e 0x5cad4a33b43cce63 0x4e43d993c8a1e892 0xe4c95e704ec9b18c)),
     (9, 5, 6, (e 0x718f149b9d832049 0x9372253d1071fa45 0xbaa4db2370bcdbce)),
     (9, 5, 6, (e 0x6faaf3fbf9205892 0xfc0a4896cf2cc959 0xc348e52c6ab1852c)),
     (9, 5, 6, (e 0xf4f624ac201816e 0x475924781e968a0b 0x8770f6079080b423)),
     (9, 5, 6, (e 0x645c37bf01c865b8 0x77cb04c6b07dc4e4 0xa337956bcfc13ace)),
     (9, 5, 6, (e 0x490197447a37f81e 0x9e37d1bd40b9348c 0x48347ca738f4d1d1)),
     (9, 5, 6, (e 0x7d2aa87c73c92986 0xe8ab150a2fc3800e 0x775484cec92ff6c2)),
     (9, 5, 6, (e 0x3312bcf950b13d00 0x57698308116cffcd 0x8785a099fcc494a4)),
     (9, 5, 6, (e 0x3900920c1bee4014 0xedce6fda19554f16 0xf14a54e45d220725)),
     (9, 5, 6, (e 0x781179c586d7e139 0x3d8eaa6494fb4f13 0x2f6b69808858ea11)),
     (9, 5, 6, (e 0x3a7ea10b0c2cd88 0x44c49fdc00794f23 0xe5154aaaa473a326)),
     (9, 5, 6, (e 0xcf01cba40de7c930 0xd82d494db95c65d1 0xb1ffbd4296019ba1)),
     (9, 5, 6, (e 0x4e72a1d7a2d08974 0x645f93574128bec3 0x29bb739244b014d5)),
     (9, 5, 6, (e 0x5be151ae8026c49e 0x69fd4619a72a5e32 0xb95be21d16822f88)),
     (9, 5, 6, (e 0x824b277e3751f27 0xea42e3682f184d5b 0x596c5a494fd94887))]

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
     (9, 5, 3, (e 0xa2064c999c552c7a 0xa625e23b836e1f30 0x3a85996546700198)),
     (9, 5, 16, (e 0xc05ec97e5d23e579 0xbfb70d730f941c8e 0x5d649115571354d2)),
     (9, 5, 6, (e 0x5ca3f8f4a03f808e 0xd1d5df849e99d56b 0x758118cf4ae2ab6a)),
     (9, 5, 6, (e 0x3e012595df415fc5 0x77f5681db35f6a7c 0x3be713804aaea112)),
     (9, 5, 6, (e 0xc83a12dda32af5b0 0xb7736db527d7cca5 0x3828892c974021a5)),
     (9, 5, 6, (e 0x16fe276aac63a824 0xe4303ca4a60be419 0xa820acc471fbbb06)),
     (9, 5, 6, (e 0x4a611a09ba036a68 0x24d4fe2b8e5180f1 0xc0695dd993ebd878)),
     (9, 5, 6, (e 0x393fe087e7d16c8b 0x3976053a15674185 0x7ea577a1b1a409b7)),
     (9, 5, 6, (e 0xd304bf5c2d16b51f 0x4f1bcedb7c6f9bca 0xd79ad8c72f3d3b5f)),
     (9, 5, 6, (e 0x603e02630ec376ff 0x6037631da2596ff7 0x688299a31067a7d5)),
     (9, 5, 6, (e 0xe66ca12bae44d884 0x6f343c0a91caf137 0xb2d2d6ce164b2fa7)),
     (9, 5, 6, (e 0xbac04432136cf90 0x5fc9dc11e1f2a7b 0x89bd968561776d8)),
     (9, 5, 6, (e 0xcf1741245acb15b6 0xa8c248d7962ee3e0 0x8ccfe3d320d4854f)),
     (9, 5, 6, (e 0x84df46e3e460066b 0xf45ccca9ff3ea4c9 0x1bf78afd01d8f59a)),
     (9, 5, 6, (e 0x10fa1840f18ab0fd 0xfc7705b50be1a738 0x97fe4e2b34c4f7ca)),
     (9, 5, 6, (e 0xe33b1def59476c95 0x39c4ac1797ebdd2b 0x4cdd548f8253d8bd)),
     (9, 5, 6, (e 0xfa54ff9bdc17327d 0xa62b19416b4f6cac 0xca7bf83e5407d031)),
     (9, 5, 6, (e 0xd659f595ea6699a3 0xd259a64f376b5392 0x4875a4beab2c7e4b)),
     (9, 5, 6, (e 0xae5a201e3cc39a3c 0x4473fd13dacebf0 0xf9865f560e642205)),
     (9, 5, 6, (e 0x1015b91c3c009e9b 0x9aefc5a31a7310d4 0xb1736dc6606bec4e)),
     (9, 5, 6, (e 0x4f498f500cb168e 0x2e668ac0ed3fac1b 0xecd618713ff3284e)),
     (9, 5, 6, (e 0x1a8e5b948382b276 0x57bea397317ec799 0xed2ea25978c9c6e3)),
     (9, 5, 6, (e 0xc7f3db8d61ff11a4 0x2a2f2452a98f1d3e 0x45279a24dd7367fc)),
     (9, 5, 6, (e 0x8bb1b9176834b6de 0x4fc57bd34b788a2f 0x617921ec8a390482)),
     (9, 5, 6, (e 0x98395262ee3e52a6 0xbe7833f8616c99b8 0xf1d4b79a58392300)),
     (9, 5, 6, (e 0x8eca886b4cf60b5c 0x9ad0850d213f0af1 0x243c9f9ae450f0f6)),
     (9, 5, 6, (e 0xe4b6c9b66bba241a 0x160aea72efbecea4 0xd74b4e0889de46ec)),
     (9, 5, 6, (e 0x3fbc789e9a8a81a8 0x386310b1efc64478 0xbeeb1748405c64a1))]

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
     (9, 5, 1, (e 0xc8d0605a1d19cdeb 0x9a85aa8ceeacbaee 0x6c3af4bfc03fa7f1)),
     (9, 5, 1, (e 0x6707da139c644a00 0x38bd24466df73703 0xa726e793f8a2406)),
     (9, 5, 1, (e 0x53f53cd1baec615 0xd6f49dffed41b318 0xa8a9e832bed4a01b)),
     (9, 5, 1, (e 0xa376cd869af9422a 0x752c17b96c8c2f2d 0x46e161ec3e1f1c30)),
     (9, 5, 1, (e 0x41ae47401a43be3f 0x13639172ebd6ab42 0xe518dba5bd699845)),
     (9, 5, 1, (e 0xdfe5c0f9998e3a54 0xb19b0b2c6b212757 0x8350555f3cb4145a)),
     (9, 5, 1, (e 0x7e1d3ab318d8b669 0x4fd284e5ea6ba36c 0x2187cf18bbfe906f)),
     (9, 5, 1, (e 0x1c54b46c9823327e 0xee09fe9f69b61f81 0xbfbf48d23b490c84)),
     (9, 5, 1, (e 0xba8c2e26176dae93 0x8c417858e9009b96 0x5df6c28bba938899)),
     (9, 5, 1, (e 0x58c3a7df96b82aa8 0x2a78f212684b17ab 0xfc2e3c4539de04ae)),
     (9, 5, 1, (e 0xf6fb21991602a6bd 0xc8b06bcbe79593c0 0x9a65b5feb92880c3)),
     (9, 5, 1, (e 0x95329b52954d22d2 0x66e7e58566e00fd5 0x389d2fb83872fcd8)),
     (9, 5, 1, (e 0x336a150c14979ee7 0x51f5f3ee62a8bea 0xd6d4a971b7bd78ed)),
     (9, 5, 1, (e 0xd1a18ec593e21afc 0xa356d8f8657507ff 0x750c232b3707f502)),
     (9, 5, 1, (e 0x6fd9087f132c9711 0x418e52b1e4bf8414 0x13439ce4b6527117)),
     (9, 5, 1, (e 0xe10823892771326 0xdfc5cc6b640a0029 0xb17b169e359ced2c)),
     (9, 5, 1, (e 0xac47fbf211c18f3b 0x7dfd4624e3547c3e 0x4fb29057b4e76941)),
     (9, 5, 1, (e 0x4a7f75ab910c0b50 0x1c34bfde629ef853 0xedea0a113431e556)),
     (9, 5, 1, (e 0xe8b6ef6510568765 0xba6c3997e1e97468 0x8c2183cab37c616b)),
     (9, 5, 1, (e 0x86ee691e8fa1037a 0x58a3b3516133f07d 0x2a58fd8432c6dd80)),
     (9, 5, 1, (e 0x2525e2d80eeb7f8f 0xf6db2d0ae07e6c92 0xc890773db2115995)),
     (9, 5, 1, (e 0xc35d5c918e35fba4 0x9512a6c45fc8e8a7 0x66c7f0f7315bd5aa)),
     (9, 5, 1, (e 0x6194d64b0d8077b9 0x334a207ddf1364bc 0x4ff6ab0b0a651bf)),
     (9, 5, 1, (e 0xffcc50048ccaf3ce 0xd1819a375e5de0d1 0xa336e46a2ff0cdd4)),
     (9, 5, 1, (e 0x9e03c9be0c156fe3 0x6fb913f0dda85ce6 0x416e5e23af3b49e9)),
     (9, 5, 1, (e 0x3c3b43778b5febf8 0xdf08daa5cf2d8fb 0xdfa5d7dd2e85c5fe)),
     (9, 5, 1, (e 0xda72bd310aaa680d 0xac280763dc3d5510 0x7ddd5196add04213))]


#guard (busProbe [0, 16, 1] sampleLayout.push) =
    (17,
     [(0, 79950), (16, 0), (1, 79932), (2, 79872), (2, 79876), (2, 79880), (2, 79884), (2, 79888),
      (1, 79934), (1, 79936), (1, 79938), (1, 79940), (1, 79942), (1, 79944), (1, 79946),
      (1, 79948), (2, 79892), (2, 79896), (2, 79900), (2, 79904), (2, 79908), (2, 79912),
      (2, 79916), (2, 79920), (2, 79924), (2, 79928), (9, 65536), (9, 66048), (9, 66560),
      (9, 67072), (9, 67584), (9, 68096), (9, 68608), (9, 69120), (9, 69632), (9, 70144),
      (9, 70656), (9, 71168), (9, 71680), (9, 72192), (9, 72704), (9, 73216), (9, 73728),
      (9, 74240), (9, 74752), (9, 75264), (9, 75776), (9, 76288), (9, 76800), (9, 77312),
      (9, 77824), (9, 78336), (9, 78848), (9, 79360)])

#guard (busProbe [0, 16, 1] sampleLayout.pull) =
    (17,
     [(0, 79950), (16, 0), (1, 79932), (2, 79872), (2, 79876), (2, 79880), (2, 79884), (2, 79888),
      (1, 79934), (1, 79936), (1, 79938), (1, 79940), (1, 79942), (1, 79944), (1, 79946),
      (1, 79948), (2, 79892), (2, 79896), (2, 79900), (2, 79904), (2, 79908), (2, 79912),
      (2, 79916), (2, 79920), (2, 79924), (2, 79928), (9, 65536), (9, 66048), (9, 66560),
      (9, 67072), (9, 67584), (9, 68096), (9, 68608), (9, 69120), (9, 69632), (9, 70144),
      (9, 70656), (9, 71168), (9, 71680), (9, 72192), (9, 72704), (9, 73216), (9, 73728),
      (9, 74240), (9, 74752), (9, 75264), (9, 75776), (9, 76288), (9, 76800), (9, 77312),
      (9, 77824), (9, 78336), (9, 78848), (9, 79360)])

#guard (busProbe [] sampleLayout.count) =
    (14,
     [(2, 13824), (2, 13828), (2, 13832), (2, 13836), (1, 13872), (1, 13874), (1, 13876),
      (1, 13878), (1, 13880), (1, 13882), (2, 13840), (2, 13844), (2, 13848), (2, 13852),
      (2, 13856), (2, 13860), (2, 13864), (2, 13868), (9, 0), (9, 512), (9, 1024), (9, 1536),
      (9, 2048), (9, 2560), (9, 3072), (9, 3584), (9, 4096), (9, 4608), (9, 5120), (9, 5632),
      (9, 6144), (9, 6656), (9, 7168), (9, 7680), (9, 8192), (9, 8704), (9, 9216), (9, 9728),
      (9, 10240), (9, 10752), (9, 11264), (9, 11776), (9, 12288), (9, 12800), (9, 13312)])

/-! ## `derive_config` (`whir.rs:17-63`) -/

/-- `derive_config(log_n, rate)` for every admissible pair: folds, rates, queries. -/
def refConfigs : List (ℕ × ℕ × List ℕ × List ℕ × List ℕ) :=
  [(16, 1, [6, 4, 4], [1, 4, 7], [223, 56, 30]), (17, 1, [6, 4, 4], [1, 4, 7], [223, 56, 31]),
   (18, 1, [6, 4, 4], [1, 4, 7], [223, 56, 32]), (19, 1, [6, 4, 4], [1, 4, 7], [223, 56, 32]),
   (20, 1, [6, 4, 4, 4], [1, 4, 7, 10], [223, 56, 32, 22]),
   (21, 1, [6, 4, 4, 4], [1, 4, 7, 10], [223, 56, 32, 22]),
   (22, 1, [6, 4, 4, 4], [1, 4, 7, 10], [224, 56, 32, 23]),
   (23, 1, [6, 4, 4, 4], [1, 4, 7, 10], [224, 56, 32, 23]),
   (24, 1, [6, 4, 4, 4, 4], [1, 4, 7, 10, 13], [224, 56, 32, 23, 17]),
   (25, 1, [6, 4, 4, 4, 4], [1, 4, 7, 10, 13], [224, 56, 32, 23, 17]),
   (26, 1, [6, 4, 4, 4, 4], [1, 4, 7, 10, 13], [224, 56, 32, 23, 18]),
   (27, 1, [6, 4, 4, 4, 4], [1, 4, 7, 10, 13], [225, 56, 32, 23, 18]),
   (28, 1, [6, 4, 4, 4, 4, 4], [1, 4, 7, 10, 13, 16], [225, 56, 32, 23, 18, 14]),
   (29, 1, [6, 4, 4, 4, 4, 4], [1, 4, 7, 10, 13, 16], [225, 56, 32, 23, 18, 14]),
   (30, 1, [6, 4, 4, 4, 4, 4], [1, 4, 7, 10, 13, 16], [226, 56, 32, 23, 18, 14]),
   (31, 1, [6, 4, 4, 4, 4, 4], [1, 4, 7, 10, 13, 16], [226, 56, 32, 23, 18, 15]),
   (32, 1, [6, 4, 4, 4, 4, 4, 4], [1, 4, 7, 10, 13, 16, 19], [227, 56, 32, 23, 18, 15, 12]),
   (16, 2, [6, 4, 4], [2, 5, 8], [112, 45, 27]), (17, 2, [6, 4, 4], [2, 5, 8], [112, 45, 28]),
   (18, 2, [6, 4, 4], [2, 5, 8], [112, 45, 28]), (19, 2, [6, 4, 4], [2, 5, 8], [112, 45, 28]),
   (20, 2, [6, 4, 4, 4], [2, 5, 8, 11], [112, 45, 28, 20]),
   (21, 2, [6, 4, 4, 4], [2, 5, 8, 11], [112, 45, 28, 20]),
   (22, 2, [6, 4, 4, 4], [2, 5, 8, 11], [112, 45, 28, 21]),
   (23, 2, [6, 4, 4, 4], [2, 5, 8, 11], [112, 45, 28, 21]),
   (24, 2, [6, 4, 4, 4, 4], [2, 5, 8, 11, 14], [112, 45, 28, 21, 16]),
   (25, 2, [6, 4, 4, 4, 4], [2, 5, 8, 11, 14], [112, 45, 28, 21, 16]),
   (26, 2, [6, 4, 4, 4, 4], [2, 5, 8, 11, 14], [112, 45, 28, 21, 16]),
   (27, 2, [6, 4, 4, 4, 4], [2, 5, 8, 11, 14], [112, 45, 28, 21, 16]),
   (28, 2, [6, 4, 4, 4, 4, 4], [2, 5, 8, 11, 14, 17], [112, 45, 28, 21, 16, 13]),
   (29, 2, [6, 4, 4, 4, 4, 4], [2, 5, 8, 11, 14, 17], [113, 45, 28, 21, 16, 14]),
   (30, 2, [6, 4, 4, 4, 4, 4], [2, 5, 8, 11, 14, 17], [113, 45, 28, 21, 17, 14]),
   (31, 2, [6, 4, 4, 4, 4, 4], [2, 5, 8, 11, 14, 17], [113, 45, 28, 21, 17, 14]),
   (32, 2, [6, 4, 4, 4, 4, 4, 4], [2, 5, 8, 11, 14, 17, 20], [113, 45, 29, 21, 17, 14, 12]),
   (16, 3, [6, 4, 4], [3, 6, 9], [75, 37, 24]), (17, 3, [6, 4, 4], [3, 6, 9], [75, 37, 25]),
   (18, 3, [6, 4, 4], [3, 6, 9], [75, 38, 25]), (19, 3, [6, 4, 4], [3, 6, 9], [75, 38, 25]),
   (20, 3, [6, 4, 4, 4], [3, 6, 9, 12], [75, 38, 25, 18]),
   (21, 3, [6, 4, 4, 4], [3, 6, 9, 12], [75, 38, 25, 19]),
   (22, 3, [6, 4, 4, 4], [3, 6, 9, 12], [75, 38, 25, 19]),
   (23, 3, [6, 4, 4, 4], [3, 6, 9, 12], [75, 38, 25, 19]),
   (24, 3, [6, 4, 4, 4, 4], [3, 6, 9, 12, 15], [75, 38, 25, 19, 15]),
   (25, 3, [6, 4, 4, 4, 4], [3, 6, 9, 12, 15], [75, 38, 25, 19, 15]),
   (26, 3, [6, 4, 4, 4, 4], [3, 6, 9, 12, 15], [75, 38, 25, 19, 15]),
   (27, 3, [6, 4, 4, 4, 4], [3, 6, 9, 12, 15], [75, 38, 25, 19, 15]),
   (28, 3, [6, 4, 4, 4, 4, 4], [3, 6, 9, 12, 15, 18], [75, 38, 25, 19, 15, 13]),
   (29, 3, [6, 4, 4, 4, 4, 4], [3, 6, 9, 12, 15, 18], [75, 38, 25, 19, 15, 13]),
   (30, 3, [6, 4, 4, 4, 4, 4], [3, 6, 9, 12, 15, 18], [75, 38, 25, 19, 16, 13]),
   (31, 3, [6, 4, 4, 4, 4, 4], [3, 6, 9, 12, 15, 18], [75, 38, 25, 19, 16, 13]),
   (32, 3, [6, 4, 4, 4, 4, 4, 4], [3, 6, 9, 12, 15, 18, 21], [75, 38, 25, 19, 16, 13, 11]),
   (16, 4, [6, 4, 4], [4, 7, 10], [56, 32, 22]), (17, 4, [6, 4, 4], [4, 7, 10], [56, 32, 22]),
   (18, 4, [6, 4, 4], [4, 7, 10], [56, 32, 23]), (19, 4, [6, 4, 4], [4, 7, 10], [56, 32, 23]),
   (20, 4, [6, 4, 4, 4], [4, 7, 10, 13], [56, 32, 23, 17]),
   (21, 4, [6, 4, 4, 4], [4, 7, 10, 13], [56, 32, 23, 17]),
   (22, 4, [6, 4, 4, 4], [4, 7, 10, 13], [56, 32, 23, 18]),
   (23, 4, [6, 4, 4, 4], [4, 7, 10, 13], [56, 32, 23, 18]),
   (24, 4, [6, 4, 4, 4, 4], [4, 7, 10, 13, 16], [56, 32, 23, 18, 14]),
   (25, 4, [6, 4, 4, 4, 4], [4, 7, 10, 13, 16], [56, 32, 23, 18, 14]),
   (26, 4, [6, 4, 4, 4, 4], [4, 7, 10, 13, 16], [56, 32, 23, 18, 14]),
   (27, 4, [6, 4, 4, 4, 4], [4, 7, 10, 13, 16], [56, 32, 23, 18, 15]),
   (28, 4, [6, 4, 4, 4, 4, 4], [4, 7, 10, 13, 16, 19], [56, 32, 23, 18, 15, 12]),
   (29, 4, [6, 4, 4, 4, 4, 4], [4, 7, 10, 13, 16, 19], [57, 32, 23, 18, 15, 12]),
   (30, 4, [6, 4, 4, 4, 4, 4], [4, 7, 10, 13, 16, 19], [57, 33, 23, 18, 15, 12]),
   (31, 4, [6, 4, 4, 4, 4, 4], [4, 7, 10, 13, 16, 19], [57, 33, 23, 18, 15, 13]),
   (32, 4, [6, 4, 4, 4, 4, 4, 4], [4, 7, 10, 13, 16, 19, 22], [57, 33, 23, 18, 15, 13, 11])]

#guard refConfigs.length = 68
#guard refConfigs.all fun (n, r, folds, rates, queries) ↦
  decide ((Whir.ladder n r).map (fun ls ↦
    (ls.map (·.fold), ls.map (·.logInvRate), ls.map (·.queries))) = some (folds, rates, queries))

/-! ## Keccak GKR and the RMFE (`keccak.rs:14-113`, `:208-221`) -/

#guard (alongPairs.map fun (j, k) ↦ keccakAlong j k) =
    [64, 319, 192, 127, 1064, 1535, 1280]

#guard (transposeProbe) =
    (1600,
     [(e 0xca8abc6d967083b1 0x23e90670f9332354 0xf6e220ad94161c47),
      (e 0xe18c283116a57e56 0x3d63a0587881af69 0xc54b99b0a60ab8c)],
     (e 0x9957ef50a4776ca3 0x29facd4353569cf0 0xa17e5a9bd314d8c4))

#guard (keccakInstanceWeights (fe 600)) =
    [(e 0xabf76e47f0538fe3 0x25c59b093b738419 0xa078d3a21966422f),
     (e 0xaa15ec70e967a4f9 0x90baaedf5703239d 0x52289def6d60ee2e),
     (e 0x12fe76f613f4585f 0xf937853a55de468b 0x25c93ea9b9df7e59),
     (e 0x1dc48c30a766e0fe 0xb53d94e9881cdaad 0x4c1957abaf45ba7f),
     (e 0xb7efb58bfffb136b 0xb1905f6529f0cc14 0x11d24bf6d67b619d),
     (e 0xd7a307cede31f29a 0x50df91ec5e0d0252 0xf4d77942c78a6beb),
     (e 0x97cb741f6b59cadd 0x87779aa014ec0dd1 0x851772f64f90c6da),
     (e 0x77fbb2d0cedf2b37 0x70e2253e144298ed 0xffbabe05fc4c8caf),
     (e 0x8d43b725fccc5d3d 0xf897c5d8a269a8a2 0x53cc92cf4f9e50a0),
     (e 0x1a7d105c173d0fdd 0x4f761d7fb86338d7 0x12bba7e7208a6c62),
     (e 0xb804dcd11bb21a98 0xd2bfc0917515037 0xbac7572c28cdd784),
     (e 0xefd10d90052a38a1 0xbfe33fb9531accc0 0xb7c17643504a6bdc),
     (e 0x5038636ecfaa2cb0 0x7e32c36af721e9 0x751c4d914b60f03f),
     (e 0x7ce5a398eacfaa54 0xad8c86a7032429d1 0xd9486452839663fd),
     (e 0xd972d9438d33a47b 0x7f303cbb60543024 0xbb95675af8f83f41),
     (e 0xe715d527918f04f1 0x706dda4850a86d5b 0x21e60ce9386aa849)]

#guard (slotProbe 0 2) =
    (64, true, (e 0x10f3280723043bde 0x6cbb309461f07cdc 0x458ec0d7e494875))

#guard (slotProbe 1 1) =
    (64, true, (e 0xcb8ea1ef741e8eca 0xe04b54c5f0899db4 0x866d484ffa7bb30a))

#guard (rmfeFactors) =
    [(0b10, 1), (0b11, 1), (0b1011, 2), (0b1101, 2), (0b100101, 3), (0b101001, 3), (0b101111, 3)]

#guard (rmfeEmbed) =
    [0x40c50b, 0x7f79f2, 0x4b4e0a, 0x72740c, 0x5357da, 0x1d1c9e, 0x4be6e, 0x785246, 0x97cdc,
     0x109e7e, 0x1f1454, 0x213cfc, 0x4cfcc8, 0x775770, 0x187386, 0x818a16]

#guard (rmfeProject) =
    [0x1, 0x7fffffffffff, 0x274e9d3a74e9, 0x1d3a74e9d3a7, 0x65cb972e5cb9, 0x5cb972e5cb97,
     0x6690aec7cd21, 0x5d8f9a42bb1f, 0x73485763e690, 0x3750967c6ea1, 0x12cf8dd4259f, 0x1ba84b3e3750,
     0xad0c9f715a1, 0x64fb8ad0c9f, 0x456864fb8ad0, 0x400000000000]

#guard (carrylessInputs.map fun (a, b) ↦ carryless a b) =
    [0xbee80b8, 0x5d073452, 0x436b037e, 0x18ea27ac]

#guard (divmodInputs.map fun (a, f) ↦ carrylessDivmod a f) =
    [(0x1b08c182, 0x5e5), (0x1d3534da, 0x1c8), (0x95fdc62, 0xbb), (0x3f3d41f, 0x1b9), (0x5, 0x1),
     (0x0, 0x5)]

#guard (keccakConstants) =
    [12, 2, 1, 6, 9, 1600, 11, 5, 64, 16, 24, 47, 6, 4, 16, 32]

#guard (ringMapShifts) =
    [32, 16, 8, 4, 2, 1]

/-! ## Keccak-f, Keccak-256 and the sponge (`hash.rs:6-99`, `transcript.rs:17-75`) -/

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
      0x163dcd923875c144], (e 0xd85b3e2fd2e1eb4f 0xd3d1d5831bc8efcd 0xa4056d0625b721fd))

#guard (duplexProbe [(fe 800, 1), (fe 801, 4), (fe 802, 1)]) =
    ([0x5c65f06a8c48e5d3, 0xff98d475e0ca11de, 0x888cb567449790e7, 0xc26fc20e304badc6,
      0xfbcca4fdafb56689, 0xad71ffb0d635248f, 0x1c03491988471785, 0x8045e33617757193,
      0xc34c4ef70674131d, 0xd7d7f87d41b52f94, 0xc6a681c2b319e6f9, 0x6e88eff078527160,
      0x4424be1e66f80f08, 0xb129d190df13c0c9, 0xe0eb32fac77fc508, 0x27f09328b09c2a10,
      0xec26a77f057643d6, 0x9aa83a127f5c1c1c, 0x5299d3d57892f07f, 0xa4efda258e20c562,
      0xe13a109ff887969, 0xe3199f10eedfe092, 0xdd3fa52d85b383f3, 0xee14430390d231b4,
      0xa4f3f800c9b0f4f3], (e 0x5c65f06a8c48e5d3 0xff98d475e0ca11de 0x888cb567449790e7))

#guard (duplexProbe [(fe 803, 1), (fe 804, 1), (fe 805, 4), (fe 806, 1)]) =
    ([0x64dc67f1e0409331, 0x2bbdabde4d11810f, 0x5f84b465ed2dc183, 0x47597d7327c5f9df,
      0xb023c216dd9aed4e, 0x3b0209d2863f6875, 0xac5249717127864e, 0xea4b63efef6a7362,
      0x56e1e947403c0534, 0x876fac31329f0048, 0x89e1c37ead2e965a, 0x906e6d8b2cfe8182,
      0xe55326f9923f04ab, 0x949494d9c721c805, 0xfd1ebfedd92744a8, 0xe367df91e05da0f1,
      0x7b1f895158f02429, 0x18a4a56f3336a459, 0xc200fd5d1f7ff09, 0xb4821d1e596ee97d,
      0xc423cd04d2d6b248, 0x2e89040fcc61f189, 0x75c84d5504e01c28, 0xbf54aece417c3beb,
      0x4d44fe1a93147d07], (e 0x64dc67f1e0409331 0x2bbdabde4d11810f 0x5f84b465ed2dc183))

/-! ## The tag, the IV and the seed (`layout.rs:68`, `bytecode.rs:46-53`, `transcript.rs:33-46`) -/

#guard (versionTag) = [108, 101, 97, 110, 118, 109, 45, 118, 49]

#guard ((keccak256 (sampleBytecode.flatMap K.toBytes)).toList) =
    [0x5ee1b7ed85bd7f40, 0xe30f235e90f241ba, 0x2c5175ed6d0af92b, 0x99aaaff5bf8937b8]

#guard ((fiatShamirIv sampleBytecode).toList) =
    [0x388a48ed64bdc88, 0xc56fdc9a5bbfc60b, 0x9177eb91e2b31ac9, 0x60b15bff515ffc9a]

#guard (samplePublicInput.toList) =
    [0xdfcab5a08b76614c, 0x87725d48331e09f4, 0x2f1a05f0dbc6b19c, 0xd7c2ad98836e5944]

#guard ([(digestHalves samplePublicInput).1, (digestHalves samplePublicInput).2]) =
    [(e 0xdfcab5a08b76614c 0x87725d48331e09f4 0x0), (e 0x2f1a05f0dbc6b19c 0xd7c2ad98836e5944 0x0)]

#guard ((seed sampleBytecode samplePublicInput).toList) =
    [0x9d7d4eb7cc97e374, 0xb724b7ba8b1c3421, 0x14d14d64d9182a28, 0x1c1a4bc2a316a26c,
     0xe410600d8d0706c8, 0x4dd78f280a2db761, 0x50dc9d77b0f34b74, 0x2d2743bc3e4da033,
     0xf266f7f60648d489, 0xa55b889e0f5c5da7, 0x2f671d6a94b8c6aa, 0xcda35ca721ea79e1,
     0xbbcb869a8f7e0386, 0xa00ae0785cf727df, 0xd9b984d1efc0d523, 0x354259a0706ebaeb,
     0x7fa694082e9b86c0, 0xe22eb021ce923a65, 0x43dc097da59a77b9, 0xa5084af5f4153506,
     0xb1ced25d740086b4, 0x26aaa2d4102a5604, 0x60ee864b6821e0aa, 0x8f239df976d3a9ef,
     0x6d5f9ca9bf33253e]

end LeanVMTests.Protocol.Verifier.Helpers
