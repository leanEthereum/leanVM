# AVX2 single-thread performance ideas from `riscv-exploration`

Ideas for the experimental prover on x86 machines with AVX2 and no AVX-512, proving on one thread (`LEANVM_NUM_THREADS=1`), taken from the `riscv-exploration` branch (`06e5c9cd6`). Each idea keeps the proof bytes, so `bins/leanvm/tests/identical_proofs.rs` checks it. Paths prefixed `riscv:` are in that branch; unprefixed ones are under `crates/experimental_prover/`.

The ranking comes from the span trees of `cargo leanvm --prover experimental aggregate` at 100 and 400 leanXMSS and 40 leanSPHINCS signatures, built for one AVX-512 and three AVX2 targets on one Zen 4 core. The measurements are in the commit message. AVX2 targets come in three tiers, and some ideas need the third:

|tier|flags|machines|
|---|---|---|
|AVX2 + PCLMULQDQ|`-C target-cpu=haswell`|Haswell to Skylake, Zen 1 and 2, CI's `haswell` testbed|
|+ VPCLMULQDQ|`-C target-cpu=x86-64-v3 -C target-feature=+pclmulqdq,+vpclmulqdq`|Zen 3|
|+ GFNI|the above with `+gfni`|Alder Lake and later Intel client cores, whose AVX-512 is off|

## Where the time goes on AVX2

In order of share of the proof:

1. The Keccak reduction (`keccak_gkr`), the largest stage and the furthest behind AVX-512. Within its layers, Skip falls furthest behind, then Tables and Product. Tail stays closest to AVX-512.
2. The PCS opening: level 0's lane projection (`Project`) and the extension commits of levels 1 to 3.
3. The commit: the base encode and the Keccak Merkle leaves it hashes as rows finish. The additive NTT alone already runs as fast on AVX2 as `riscv-exploration`'s, so most of the AVX2 cost here is Keccak (below).
4. The bus: GKR, then the grind and the leaves.

Execution and witness building run at the same speed on every target.

## Ideas, by expected gain

### 1. An AVX2+GFNI arm for the Keccak skip pass

- Today: `keccak_gkr/src/kernels.rs:255` selects `skip_gfni::SkipBlock` only with AVX-512F, AVX-512BW and GFNI. Every AVX2 target falls back to embedding each position and multiplying by CLMUL, which is the AVX2 kernel furthest behind AVX-512.
- In riscv: every byte-field kernel has an AVX2 arm alongside its AVX-512 one, the same algorithm two registers wide (`riscv:crates/flock/src/zerocheck/round1.rs:711`, `product_bytes_avx2`, beside `product_bytes_gfni` at `:665`).
- The port: `skip_gfni.rs` uses only `gf2p8affineqb`, `gf2p8mulb`, XOR, loads, stores and broadcasts, all of which exist at 256 bits under GFNI with AVX. Each `__m512i` becomes a pair of `__m256i`. The 24 residues are three ZMM registers, so six YMM; keep the per-slot loop's live set within 16 registers, as riscv's eight-byte output tiles do (`riscv:round1.rs:930`).
- Gain: the largest of this list on the GFNI tier. None on the other two tiers.

### 2. An AVX2+GFNI arm for the Keccak tables

- Today: `keccak_gkr/src/prover.rs:415` builds `table_gfni::RowMaps` only on AVX-512 with GFNI. Elsewhere each position is embedded, multiplied by the fold weights, written to a `6 * BITS`-word scratch and reduced from there (`prover.rs:460`).
- In riscv: the lift and weighting of packed bytes are GF(2)-linear maps applied 32 lanes at a time with `_mm256_gf2p8affine_epi64_epi8`, eight output bytes at a time so the accumulators stay in registers (`riscv:round1.rs:930` `convert`, `riscv:crates/primitives/src/bit_fold/avx2.rs:55`).
- The port: `table_gfni.rs`'s AVX-512 operations are the affine map, unpacks, `shuffle_i64x2` (`vperm2i128` or `vpermq` at 256 bits) and one `ternarylogic` (two XORs). The scratch pass goes away with it.
- Gain: medium, GFNI tier only.

### 3. The bus GKR's vertical kernel on AVX2+VPCLMULQDQ

- Today: `lean_vm_core/src/gkr.rs:44` (`products_into`) and `:518` (`fold_and_message`) use the transposed eight-lane kernel only on AVX-512, through `field::x8::F128x8`. AVX2 runs the scalar-shaped row loops, calling `mul2` per pair.
- In riscv: the GKR is written once over `field::lanes::Lane`, which on x86 is the AVX2+VPCLMULQDQ type even where AVX-512 exists (`riscv:crates/primitives/src/field/lanes.rs:19`). Products are gathered into lanes, kept there across the layer, and accumulated unreduced (`riscv:crates/leanvm_core/src/gkr/mod.rs:48`, `gkr/layer.rs:231`).
- The port: `field::f128x8::F128x8` already has an AVX2+VPCLMULQDQ arm (`primitives/src/field/f128x8.rs:20`), two `x4` halves. Write `gkr.rs`'s `vertical` module over it instead of `x8`, gate it on AVX2 with VPCLMULQDQ, and check for spills, since one AVX-512 plane register becomes two YMM registers. `products_into` alone, which also builds the leaves, is the smaller first step.
- Gain: medium on the VPCLMULQDQ and GFNI tiers.

### 4. An AVX2 bit transpose, with a GFNI form

- Today: `primitives/src/bits.rs:16` has an AVX-512 VBMI+GFNI arm, a NEON arm, and a portable gather for everything else, AVX2 with GFNI included. It runs per eight words in the level-0 lane projection (`pcs/src/stack_open/basis.rs:422`) and in the Keccak openings (`keccak_gkr/src/open.rs:129`, `:278`).
- In riscv: `riscv:crates/primitives/src/bits.rs:182` gathers the byte columns with two loads, two unpack rounds, a `vpermq` and a `vpshufb`. Then it applies either one `gf2p8affineqb` per register (`:203`) or the three masked-swap rounds on four words at once (`:217`).
- The port: the same 64-byte contract and bit order, so copy the functions and add the two `cfg` arms. Both forms beat the portable gather in a microbenchmark on one core, the GFNI form by far.
- Gain: low to medium, on every tier. The projection also spends time in `fold_columns` and the pattern dots, which this leaves unchanged.

### 5. Row-major `BitFold::fold_block` on AVX2

- Today: with or without GFNI, AVX2 folds row-major blocks through scalar subset-sum lookups, one 256-entry `F128` table per input byte (`primitives/src/bit_fold.rs:178`, and `:753` under GFNI). Only column-major input reaches the AVX2 nibble and GFNI-256 kernels.
- In riscv: rows are transposed into 32-byte columns, then go through the same byte maps (`riscv:crates/primitives/src/bit_fold/avx2.rs:198` `transpose_rows`, `:308` `fold_block`). Without GFNI, each nibble table is stored once as 16 bytes and broadcast to both lanes (`:98`), not stored twice.
- The port: put an AVX2 row transpose in front of the existing `fold_columns`. The consumer is the ring switch's dense lift (`pcs/src/ring_switch.rs:313`).
- Gain: low on these workloads, where the ring switch's spans are small. It grows with ring-heavy openings.

### 6. Two sumcheck rounds per pass over a table

- Today: the Keccak tail (`keccak_gkr/src/prover.rs:547`) and the bus GKR (`lean_vm_core/src/gkr.rs:446`) already fuse each fold with the next round's message. Each round still writes a half-size table that the next round reads.
- In riscv: a quadratic round computes the shared terms for two rounds and folds two pending challenges in one read of the table (`riscv:crates/flock/src/zerocheck/multilinear.rs:232`, `:562`). The quartic GKR does the same with a degree-(4, 4) grid (`riscv:crates/leanvm_core/src/gkr/layer.rs:82` `fold`, `:199` `second_round`).
- Gain: low to medium, and the effort is high. On AVX2 the quartic version's extra accumulators may spill, so try the quadratic Keccak tail first.

### 7. Byte-field products without GFNI

- Today: on the two tiers without GFNI, Product and Skip multiply by CLMUL.
- In riscv: the same byte-field kernels run without GFNI by shift-and-add byte products (`riscv:round1.rs:749`, `gf8_mul_vec32`).
- Whether residues with shift-and-add products beat the CLMUL path is open: try it on the PCLMULQDQ tier, where the CLMUL path is slowest.

## Looked at and not proposed

- Explicit AVX2 absorb and digest transposes for four-way Keccak (`riscv:crates/primitives/src/hash/x86.rs:85`): `keccak256`'s AVX2 batch takes the same time per permutation for 64-byte and 512-byte inputs, so absorbing is not what limits it. Keccak on AVX2 is bound by the permutation: no 64-bit rotate and no ternary logic. That is the main AVX2 cost in the commit, the extension commits and the bus grind, and none of it is in `riscv-exploration`, which hashes with BLAKE2s.
- Fewer live registers in the radix-8 NTT tile (`riscv:crates/pcs/src/ntt/kernels.rs:103`): on one core, the commit's encode alone already runs as fast here as `riscv-exploration`'s.
- Incremental twiddles (`riscv:crates/pcs/src/ntt/mod.rs:44`), SIMD for WHIR's deeper-level affine rounds (`pcs/src/whir.rs:572`), and composed ring-weight maps (`riscv:crates/pcs/src/ring_switch.rs:134`): the spans they would speed up are small on these workloads.
- Karatsuba with delayed reduction, VPCLMULQDQ-256 batching, split equality tables in the bus GKR, Gruen's equality factoring, and packed Keccak witnesses: this tree already has them.
- Flock's fixed small challenges and univariate skip: these change the protocol, so they are out of scope here.
