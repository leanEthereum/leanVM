# Verus proofs of leanVM arithmetic, kernel models and BLAKE2s

This standalone crate verifies annotated executable copies and mathematical models of leanVM arithmetic using [Verus](https://verus-lang.github.io/verus/guide/overview.html). Coverage includes portable field arithmetic, selected SIMD field and reduction kernels, bit transposes, the embedding `φ₈`, bit-fold linear maps, equality tables and multilinear evaluation, additive NTT kernels and evaluation theorems, the `GF(2^8)` NTT used by flock, skip-domain interpolation, Fiat-Shamir block encoding, and portable scalar/batched BLAKE2s. Each theorem applies to its stated preconditions and the checked copy, not directly to production source.

It is a workspace of its own, outside the leanVM one: `cargo build`, `cargo testall` and the other CI jobs never
see it, and the production crates do not depend on Verus.

## How it is tied to the production code

Verus checks functions inside `verus! { }`. Production does not depend on `vstd`: modules here copy production operations and attach specifications. Source adaptations are documented at each function: iterator chains, array maps and patterns become loops or explicit arrays; argument assertions become preconditions; debug assertions become proved assertions. SIMD copies call real intrinsics with trusted lane specifications and trusted memory wrappers where pointer operations cannot be expressed directly.

`tests/equivalence/` compares executable copies with production on exhaustive small domains and deterministic edge and random inputs. Private functions use reachable public callers or source modules compiled into the test binary, with exceptions recorded below. These tests can detect drift, but do not prove source equivalence or guarantee that future divergence will be caught. A verified model or copy is not verified production source.

The proof matrix covers portable x86, Haswell, AVX2 with VPCLMULQDQ (with and without GFNI), AVX-512, and AArch64 with and without SHA3. Native tests exercise available hardware; AArch64 tests under QEMU exercise an emulator rather than physical ARM hardware. CI additionally runs the equivalence suite on an ARM64 runner. Runtime feature checks skip unavailable x86 instructions; a passing skipped test is not hardware evidence for that instruction.

## What is proven

Polynomials over GF(2) are machine words, bit `i` the coefficient of `x^i`. The specifications are:

- `clmul(a, b)`: the carry-less product, defined as the XOR over the set bits `i` of `a` of `b << i`
  (`src/clmul.rs`).
- `is_remainder(p, r)`: `p = q * M + r` for some polynomial `q`, with `deg r < 64` (`M = x^64 + x^4 + x^3 + x + 1`);
  `k_mod(p)` is that remainder and `k_mul(a, b) = k_mod(clmul(a, b))`, the product in `K`. The same for
  `GF(2^8)` with `M = x^8 + x^4 + x^3 + x + 1` (`f8_mul`).
- `e_mul(a, b)`: the product of `a0 + a1 y + a2 y^2` and `b0 + b1 y + b2 y^2` as polynomials in `y` over `K`,
  folded by `y^3 = y + 1` and `y^4 = y^2 + y`.
- `k_pow`, `e_pow`, `f8_pow`: repeated products.

### `K = GF(2^64)` (`src/gf2_64.rs`)

- `software::clmul` computes `clmul`; so do `mul_wide` and `square_wide` (portable arms).
- `reduce(p)` returns the remainder of `p` modulo `M`, for every 128-bit `p`, and the remainder is unique.
- `F64 * F64` is `k_mul`, `F64::square` is `k_mul(a, a)`; `+` is XOR.
- `K` is a commutative ring: `k_mul` is commutative, associative, distributes over XOR, and has one and zero.
- `F64::inv(a)` is `a^(2^64 - 2)` (the Itoh-Tsujii addition chain is checked step by step), and
  `a * inv(a) = 1` for every nonzero `a`, `inv(0) = 0`.
- Fermat: `a^(2^64) = a` for every `a`.
- So `K` is a field, with no assumption on `M`: the proof shows the only idempotents (`e^2 = e`) are 0 and 1,
  one bit-vector query on the squaring map, then `a^(2^64 - 1)` is an idempotent that is not 0 when `a` is not.
- SIMD copies of `x86_64::mul` and `aarch64::mul_shift_tail` compute `k_mul`; x86 `clmul` and NEON `pmull`/`pmull_hi` compute the specified carry-less product. `aarch64::reduce_pair_pmull4` returns the two `k_mod` remainders lane by lane, for arbitrary 128-bit inputs. BMI2 `spread` equals the carry-less square by depositing each input bit into an even output position. The dispatched `F64` operations retain their field contracts in each configuration.
- These proofs use `lemma_clmul_fold_reduction` for the two high-word folds by `0x1B` and the explicit intrinsic assumptions below. The empty NEON assembly barrier is represented by the trusted identity wrapper `hide_lanes`, not verified assembly.

### `E = GF(2^192)` (`src/gf2_64x3.rs`)

- `software::mul_unreduced`, `F192::mul_unreduced`, `mul_base_unreduced` and `From<F192>` build an
  `F192Unreduced` whose three 128-bit coefficients, each reduced modulo `M`, are the product (`e_value`).
- `F192Unreduced::reduce` returns that element; `F192 * F192 = e_mul`; `mul_base(k) = e_mul(a, k)`;
  `square(a) = e_mul(a, a)` (the cross terms cancel).
- Lazy reduction: `e_value(u ^ v) = e_value(u) + e_value(v)`, and for any sequence of unreduced values,
  reducing their XOR once equals summing their reductions (`lemma_lazy_reduction`). This is what the
  accumulating kernels rely on.
- `mul2`, `mul4`, `mul_unreduced4`, `mul_base8` (portable arms) are lane-wise products; `Weights8::new` then
  `get(i)` returns weight `i`; `dot_base` returns `sum_i w_i * k_i`.
- `E` is a commutative ring (associativity by expansion into the 27 triple products).
- `frobenius(a)` is `a^(2^64)` (it is the 64th squaring, by Fermat in `K`).
- `F192::inv(a)` is `a^(2^192 - 2)`, and `a * inv(a) = 1` for every nonzero `a`; the norm `a * φ(a) * φ²(a)`
  lies in `K` (production's `debug_assert!`). So `E` is a field too, again with no assumption.
- The x86 Karatsuba product (six PCLMULQDQs and `fold`) gives the same three unreduced coefficients as the
  schoolbook product, given that PCLMULQDQ computes `clmul` (`lemma_karatsuba_fold`).

#### x86 GF(2^192) SIMD copies

`src/gf2_64x3_x86.rs`, `src/gf2_64x3_x86_avx2.rs`, and `src/gf2_64x3_x86_wrappers.rs` cover the PCLMULQDQ scalar-register kernels, AVX2/VPCLMULQDQ two-product and lane-major kernels, and AVX-512 four-product, lane-major, mixed-product and planar kernels. These are proofs of annotated copies, not proofs obtained by verifying production source directly.

- `pair`, `karatsuba`, `fold`, `mul_unreduced`, `mul_base_unreduced`, `F192x1` and `F192x1Unreduced` specify the exact coefficient words or held field element. `reduce_lanes128/256/512` reduce arbitrary low/high word pairs, not only multiplication outputs.
- `karatsuba_vec2/4`, `mul_vec2/4`, `mul_unreduced_vec2/4`, `mul_by_pairs` and `mul_by_pairs256` specify every product lane. The configured `F192` and batched dispatch copies call these kernels. Squaring uses the existing base-field square/reduce copies, as production's x86 arm does.
- `Lanes4` holds `[c0,c1]` and `[c2,c2]` in each 128-bit lane. AVX-512 has four such lanes per register; AVX2 has two registers per plane, with elements `2h` and `2h+1` in half `h`. Loads, stores, XOR, multiplication, reduction, and transpose preserve this representation. Transpose moves both words of each plane: output lane `j` of row `i` is input lane `i` of row `j`. Multiplication and AVX2 stores require the duplicated `c2` invariant; the safe wrapper's type invariant enforces it.
- `F192x4` and its unreduced wrapper prove lane-wise arithmetic, memory round trips and transpose; sums use the lazy-reduction identity. `MixedSums8` has eight independently specified sums. `mul_base8_add` updates each by `t * k[i]`, and `mul_base8_reduce` reduces each once.
- AVX-512 `F192x8` stores coefficient `c` of element `i` in qword `i` of plane `c`. Its products are lane-wise `e_mul`; `F192x8Sum::mul_add` adds all eight products to the held sum. `dot_base` is the mixed inner product for `k.len() == 8 * w.len()`. The proof has this precondition; production rejects mismatched lengths. No correctness claim is made for violating a precondition or running code without its required ISA.

Trust inventory added by these copies:

- Existing `intrinsics::x86` register views, layout axioms and intrinsic specifications remain assumptions, including carry-less multiplication, XOR, unpacking, shifts, permutation, broadcast and ternary logic. `intrinsics::x86_bits` retains its own registrations; no intrinsic is specified a second time by the GF192 extension.
- `intrinsics::x86_gfx86` adds specifications for `_mm_setzero_si128`, `_mm_set1_epi64x`, `_mm_slli_epi64`, `_mm_srli_epi64`, `_mm_shuffle_epi32`, `_mm256_shuffle_epi32`, `_mm512_shuffle_epi32`, `_mm256_blend_epi32`, `_mm256_permute2x128_si256`, `_mm256_permutevar_pd`, `_mm256_castpd_si256`, `_mm256_castsi256_si128`, `_mm256_extracti128_si256`, `_mm512_setzero_si512`, `_mm512_broadcast_i32x4`, `_mm512_castsi512_si256`, `_mm512_castsi256_si512`, and `_mm512_extracti64x4_epi64`. The widening cast constrains only its low half; unspecified upper words are never used as initialized data. The `__m256d` bit view and the all-zero register-array layout axioms for `core::mem::zeroed` are also trusted.
- Raw pointer helpers are `external_body`: `load_c01`, `load_c2`, `store_c01_c2`, `load_k8`, `load_k_at`, `load_weights`, `load_head8`, `load_tail4`, `store_head_tail`, and AVX2 `load_half`, `store_half`, `load_k4`. Their contracts assume the documented `repr(C)` field layout, transparent `F64` layout, 64-byte `Weights8` alignment and in-bounds reads/writes. Arithmetic, permutations and accumulation outside these helpers are proved, not assumed.

`tests/equivalence/intrinsics_x86_gfx86.rs` checks each added intrinsic assumption against hardware, including shift boundaries, lane selectors, casts and zeroed arrays. The executable shuffle model takes even word slices of at most eight words, matching the register widths and bounding its index arithmetic. `tests/equivalence/gf2_64x3.rs` checks the copies against production through scalar and batched dispatch, register operators, loads/stores, arbitrary wide reductions, transposes, mixed accumulation, dot products and planar products/sums. Private helpers are exercised through those callers. These deterministic edge/random comparisons are evidence for the tested inputs only; they neither prove the assumptions nor prevent future source drift.

### `GF(2^8)` (`src/gf2_8.rs`)

- `clmul8_software` (and the portable arm of `clmul8`) computes the carry-less product of two bytes.
- `gf8_reduce(p)` is the remainder modulo `x^8 + x^4 + x^3 + x + 1` for every 16-bit `p`, not only the
  documented 15-bit ones, and the remainder is unique.
- `F8 * F8` is that product, a commutative ring as for `K`; `F8::inv(a)` is `a^254` and `a * inv(a) = 1` for
  every nonzero `a`.

### SIMD kernels of `E` on aarch64 and of `GF(2^8)` (`src/gf2_64x3/aarch64.rs`, `src/gf2_8.rs`)

Copies of `crates/primitives/src/field/gf2_64x3/aarch64.rs` (all of it), of the aarch64 dispatch arms of `gf2_64x3.rs`, and of the SIMD arms of `gf2_8.rs`, proven against the portable specifications given the intrinsic specifications of `src/intrinsics/aarch64_gfneon.rs` and `src/intrinsics/x86_gfneon.rs` (and the shared `aarch64.rs`, `x86.rs`). They verify in the configurations that compile them: the `E` kernels and the NEON helpers in `neon` and `neon-no-sha3` (EOR3 and its two-XOR fallback), `gf8_mul_vec32` in `haswell`, `avx2-vpclmulqdq`, `avx2-gfni` and `avx512`. A register holding a 128-bit coefficient is read as one polynomial (`v128`, its two lanes).

- `E` products: `aarch64::mul(a, b) = e_mul(a, b)`; `mul_unreduced` and `mul_base_unreduced` return an `F192Unreduced` whose value (`e_value`) is `e_mul(a, b)`, `e_mul(a, k)`; `mul_base(a, k) = e_mul(a, k)`; `square(a) = e_mul(a, a)`; `reduce(u) = e_value(u)`. The nine PMULL products of `products`, y-folded, are the three coefficients the portable `software::mul_unreduced` builds (`lemma_products_fold`, `folded`), whatever the operand words. `reduce_lane` (two PMULL2 by `0x1B` and a three-way XOR) is `k_mod` of the coefficient (`lemma_clmul_fold_reduction`).
- With those arms, `F192 * F192`, `F192::mul_unreduced`, `mul_base`, `mul_base_unreduced`, `square` and `F192Unreduced::reduce` keep their specifications on aarch64 with `aes`, so everything proven above on top of them (`inv`, the batched portable arms, `dot_base`, ...) holds there too.
- Register-resident values: `F192x1` holds an element (`value()`), with the type invariant that both lanes of its `c22` register hold `c2` (the high-lane products read it); `new`, `load`, `store` (which initializes the `MaybeUninit`), `+` and `*` are `e_add` and `e_mul` of the values, `mul_unreduced` and `mul_base_unreduced` give an `F192x1Unreduced` whose value reduces to the product; `F192x1Unreduced` XOR and `^=` are `u_xor`, `zero()` is `F192Unreduced::ZERO`, `reduce` is `e_value`, and the conversions to `F192` and `F192Unreduced` return the values. So an XOR-accumulated sum of register products reduces to the sum of the products (`lemma_lazy_reduction`).
- `GF(2^8)`: `clmul8_neon` (PMULL on bytes) and the `clmul8` dispatch compute `clmul`. `neon::gf8_reduce_vec16(c0, c1)` returns, in lane `i`, the remainder modulo `M` of polynomial lane `i` (low byte `2 (i % 8)`, high byte `2 (i % 8) + 1` of `c0` for `i < 8`, of `c1` after), for every 16-bit lane, not only products of two bytes: its Barrett quotient (the high byte of `hi * 0x8d * x`) is exact for every high byte (`lemma_reduce_vec16_lane`, one bit-vector query). `neon::gf8_mul_vec16(a, b)` is `f8_mul` lane by lane. `avx2::gf8_mul_vec32(a, b)` is `f8_mul` on each of the 32 bytes: after step `s` of the Horner loop each byte is `a * (b >> (8 - s))` (`lemma_horner_step`, from `a * (x c) = x (a * c)` and linearity).

### Bit transposes (`src/bits.rs`)

- `transpose_8x8_bits`: bit `8r + c` of the result is bit `8c + r` of the input; it is an involution.
- `transpose_64x64`: afterwards bit `r` of word `c` is bit `c` of word `r` before, for all `r, c < 64`;
  transposing twice restores the matrix. Each masked-swap round exchanges `(r, c)` and `(r ^ J, c ^ J)`
  exactly when bit `J` of `r` and `c` differ.
- `bit_transpose_64bytes_portable`: bit `x` of `output[8b + t]` is bit `t` of `input[8x + b]`.

### Bit transposes, SIMD arms (`src/bits.rs`)

`bit_transpose_64bytes` and every SIMD arm it dispatches to are copied under production's `cfg(target_feature)` gates, and each proves the portable arm's theorem, `is_bit_transpose_64bytes(input, output)`: bit `x` of `output[8b + t]` is bit `t` of `input[8x + b]`, for all `b, t, x < 8`. `verify.sh` checks each arm in the configurations that compile it: `avx512` (all three x86 arms), `avx2-gfni` (the two AVX2 ones), `haswell` and `avx2-vpclmulqdq` (the AVX2 one), `neon` and `neon-no-sha3`, and `portable` (the dispatch to the portable arm).

- `bit_transpose_64bytes_gfni` (AVX-512 VBMI with GFNI): after `vpermb` with the written-out `IDX`, word `b` of the register is byte column `b` with the rows reversed, its byte `y` being `input[8 (7 - y) + b]` (`is_reversed_column`, from `lemma_idx`); GF2P8AFFINEQB with the constant `0x8040_2010_0804_0201` then makes bit `x` of result byte `t` bit `t` of the matrix word's byte `7 - x` (`lemma_affine_unit`, one bit-vector query on the instruction's closed form), which undoes the reversal (`lemma_affine_column`).
- `gather_columns_avx2`: byte `k` of result register `w` is input byte `gather_src(w, 16 (k / 16) + order[k % 16])` for every `order` entry below 16: the two unpack rounds put input byte `unpacked_src` at each byte (`lemma_unpack_rounds`), the `0b11_01_10_00` permute moves it to `gather_src` (`lemma_permuted`), and the shuffle by the broadcast `order` picks within each lane.
- `bit_transpose_64bytes_gfni_avx2`: with `REVERSED` each word of the gathered pair is a reversed column (`lemma_reversed`), and the affine map of the AVX-512 arm turns it into its output row (`lemma_gfni_avx2_rows`).
- `bit_transpose_64bytes_avx2` and its `swap`: with `NATURAL` each word is a column in row order (`lemma_natural`); `swap::<D>(x, mask)` is the masked swap `swap_word` on each word, and the three of them are `transpose_8x8_formula` (`lemma_three_swaps`), so each stored word is the output row (`lemma_avx2_rows`, through `lemma_transposed_column`).
- `bit_transpose_64bytes_neon`: `vqtbl4q_u8` with `IDX0..IDX3` makes the two words of register `j` columns `2j` and `2j + 1` (`lemma_neon_idx`, `lemma_neon_columns`); the three rounds are the same three masked swaps; the stores make them rows `2j`, `2j + 1` (`lemma_neon_rows`).

The copies differ from production where Verus requires it, each noted at the function: the function-local `const` tables are module-level (`IDX` written out instead of built by a `while` loop), `swap` is moved out of `bit_transpose_64bytes_avx2`, `array::map` and `into_iter().enumerate()` become two calls and an index loop, and the loads and stores through `as_ptr()` are the memory helpers below. The copied arms are `pub` (production's are private), so `tests/equivalence/bits.rs` (`every_arm_matches_reference`) runs each one this build compiles against the definition and production's dispatched function.

### Additive NTT (`src/ntt.rs`)

Following annex `d` of the leanVM document:

- Butterflies: the forward butterfly evaluates the line `u + v X` at `X = t` and `X = t + 1`; the inverse
  butterfly of `inverse_transform` and the forward one undo each other for every twiddle; the transposed
  butterfly undoes the forward one with the rows swapped.
- Twiddles: `span_get(b, idx)` is the subset sum of `b` selected by the bits of `idx`, GF(2)-linear in `idx`;
  `twiddle(layer, block)` is `Ŵ_i(sum_j bit_j(block) b_(i+1+j))` with `i = L - layer - 1`; `twiddles_radix8`
  returns exactly the seven twiddles of the three layers it fuses.
- Twiddle table: entry `k` of row `i` of `generate_evals_from_subspace(b)` is `s_i(b_(i+k)) * s_i(b_i)^(-1)`,
  with `s_0(x) = x`, `s_i(x) = s_(i-1)(x) (s_(i-1)(x) + s_(i-1)(b_(i-1)))` the subspace polynomials; each `s_i`
  is GF(2)-linear and vanishes on the span of `b_0 .. b_(i-1)`.
- Layers: `radix8_butterflies` and the radix-4 group of `butterfly_interleaved_fused_2layer` equal three and
  two successive single layers. The layer-by-layer forward transform (`forward_scalar_from_layer`, the
  production tests' reference, which they compare with the parallel `transform`) followed by the inverse layers
  is the identity, for every number of interleaved lanes and every size up to the table's; with one lane the
  inverse layers are `inverse_transform`.
- Evaluation: for the table `AdditiveNttF64::standard(dim)` builds (`1 <= dim <= 63`), output word `v` of the
  forward transform on `2^dim` words is `P(v)`, where `P(x) = sum_j a_j X_j(x)` with novel basis
  `X_j = prod_i Ŵ_i(x)^(bit_i(j))` and the input `a` read as its coefficients; the domain point of index `v` is
  the field element `v` itself (no bit reversal). Encoding at rate `2^-r` (layers `r..dim` on `2^r` copies of the
  message) gives the evaluations of the polynomial whose coefficients are the message, zero-padded: the
  Reed-Solomon codeword (`lemma_standard_forward_evaluates`, `lemma_standard_encode_evaluates`; the sum is
  `novel_sum`, equal to the annex's even-odd recurrence `novel_eval` by `lemma_novel_eval_flat`). The proof
  needs every row of the table to start with one, `Ŵ_i(b_i) = 1`; it is proven for the standard basis, from
  `K` being a field and `s_i` vanishing only on the span of `b_0 .. b_(i-1)`. For an arbitrary basis the same
  theorems (`lemma_forward_evaluates`, `lemma_encode_evaluates`) take that as a hypothesis.

### Parallel NTT driver refinement (`src/ntt_driver.rs`, `src/parallel.rs`)

- `run_layers` proves the fused radix-8/radix-4/single-layer sweeps equal `sub_layers` for every well-formed table, positive lane count and valid sub-block. `lemma_gather_layer` and `lemma_gather_sub_layers` prove that gathering rows paired by a band of layers commutes with it.
- `group` proves gather/transform/scatter with permissions for every accessed word. Its input can come from the codeword, its first replica, or a separate read-only message, under the explicit permission and source-content preconditions. This is a single-group theorem, not a proof that production's fused-message scheduler establishes those preconditions.
- `gathered_pass` partitions words by `(block, residue)`, dispatches groups through the real pool, and proves equality to the corresponding global layers. `deep_pass` proves the same for the remaining layers on disjoint contiguous sub-blocks. `transform` composes them into `forward_layers`, the verified layer reference, for any positive gathered width and `start <= deep_start <= log_d <= table.len()`, with `2^log_d` rows and any positive lane count whose buffer length fits `usize`. The zero-layer domain is included with a well-formed table.
- These are executable refinements, not production-source proofs. The top-level refinement takes the cache plan as arguments and expects replicas already populated. It does not implement production's cache planner, fused message replication, row callbacks, or streaming-store fences. Gathered work is dispatched per group rather than borrowing scratch once per claimed range; the deep pass dispatches individual sub-blocks instead of explicitly batching adjacent ones. Streaming stores become ordinary copies. Function comments document the other Rust rewrites.
- `PointsTo` maps are split by task owner and returned with their postconditions. Different owners have disjoint keys and only receive their own permissions. Bounds and pointer addresses are checked before constructing row slices. `for_each` and `chunks_mut` are proved adapters over the trusted `for_each_chunk` contract: disjoint claims cover every item exactly once and join before return. The actual pool's atomic claim counter and synchronization are not verified; the conditional permission proof is not a formal safety proof of production's pool.
- `tests/equivalence/ntt_driver.rs` executes the refinement, layer reference and production public encoder word for word on seeded random inputs, rates, lane counts, domain/table sizes, gathered widths and deep splits. Separate processes configure the real pool for 1, 2 and 4 workers. These finite differential checks neither prove production equivalence nor prevent future drift.

### BLAKE2s (`src/blake2s.rs`, `src/blake2s_batch.rs`)

- The model transcribes [RFC 7693](https://www.rfc-editor.org/rfc/rfc7693), sections 2 and 3: 32-bit modular addition, G with rotations 16, 12, 8, 7, IV, SIGMA, ten rounds, counter injection, final-block flag and feed-forward. The message model is unkeyed BLAKE2s-256, including parameter initialization, little-endian encoding, zero padding, and the empty message's single final block.
- The scalar executable copies prove `compress = f_spec`, `hash = blake2s_spec`, and streaming `Hasher::finalize = blake2s_spec` of all bytes absorbed. The streaming invariant retains a full last block until more input arrives. Message lengths and continued counters must remain below `2^64`. `hash_from_state` proves whole-block continuation from arbitrary states; `lemma_zero_prefix_continuation` connects the zero-prefix state to the full message hash.
- `compress_groups` proves RFC compression separately for every group and every lane of a transposed state, for all group counts. Both the single-group inline rounds and interleaved multi-group rounds are covered. The theorem is generic over the `Lanes32` arithmetic contracts; `Scalar8` proves those contracts. G and group loops are factored into inline helpers to isolate their proof contexts.
- Safe array models `transpose_words` and `store_digests` prove the state/message transpose and little-endian digest scatter. `compress_rows` composes these with compression and proves each lane's output is the RFC compression digest of that input lane. These layout models replace raw-pointer operations; they do not prove production's pointer manipulation or batched driver.
- Equivalence tests compare scalar compression, one-shot and streaming hashes, prefix states and continuation with production. The RFC Appendix B `"abc"` known answer checks both copies and production. Batch tests compare groups 1, 2 and 4 through production's public batched hash and compare arbitrary transposed compression states lane by lane, including both counter halves and final flags.
- These are functional-correctness results relative to the RFC model, not proofs of collision resistance, preimage resistance, constant-time execution, or cryptographic security. Keyed and variable-output BLAKE2 modes are not modeled.

### SIMD butterflies of the additive NTT (`src/ntt_simd.rs`)

The kernels of `crates/pcs/src/ntt/additive_ntt_f64.rs` that `lane_butterflies` dispatches to, `butterfly_lanes_avx512` (VPCLMULQDQ with AVX-512F), `butterfly_lanes_avx2` (VPCLMULQDQ with AVX2, no AVX-512F), `butterfly_lanes_neon_8` and `butterfly_lane_pair_neon` (AES, so PMULL; EOR3 or its two-EOR fallback in `reduce_pair_pmull4`), each for `TRANSPOSED` false and true, and `lane_butterflies` with production's `cfg` arms. Each `cfg` arm is checked in the `verify.sh` configuration that compiles it: `avx512`, `avx2-vpclmulqdq` and `avx2-gfni`, `neon` and `neon-no-sha3`; the others (`portable`, `haswell`) check the scalar arm.

- Each kernel at offset `at` of width `w` (8, 4, 8, 2) leaves word `j` of the rows, for `at <= j < at + w`, as `butterfly_spec(TRANSPOSED, u_j, v_j, t)` (forward `u' = u + t v, v' = v + u'`, transposed `u' = u + v, v' = v + t u'`, products by `k_mul`, the specification of the portable `butterfly_one`), and every other word unchanged (`butterflied`).
- The products: PCLMULQDQ `0x00` and `0x11` unpacked low with high give word `i`'s 128-bit product in lane order (`lemma_products_in_lane_order`); PMULL and PMULL2 read back as `uint64x2_t` give it as the register's two lanes (`lemma_pmull_products`, `lemma_reduced_products`), reduced by the already verified `reduce_pair_pmull4`.
- The x86 reduction `lo ^ g(hi ^ spill)`, `g(x) = x ^ x<<1 ^ x<<3 ^ x<<4`, `spill = hi>>63 ^ hi>>61 ^ hi>>60`, is `k_mod` of the product (`lemma_shift_reduction`, from `lemma_k_mod`). On AVX-512 the XORs are `vpternlogq 0x96`, the three-way XOR (`lemma_ternlog_xor3`); on AVX2 the shifts are doublings by addition (`lemma_avx2_lane`) and the spill is one byte shuffle of a 16-entry table by the top nibbles, proven word by word from the shuffle's byte semantics and the register layout (`lemma_spill_shuffle`, `lemma_spill_table`, `lemma_word_of_low_byte`).
- `lane_butterflies` (and so `butterfly_lanes`, `transposed_butterfly_lanes`) keeps its specification in every configuration: the kernel blocks compose (`lemma_butterflied_extend`), then the NEON pair tail and the scalar tail finish the row.
- Rewrites, noted at each function: the kernels take the rows and the offset their pointers point to instead of `*mut F64`, and load and store through the helpers below (Verus cannot obtain pointer permissions from the `&mut [F64]` borrows `lane_butterflies` holds); production's function-local constants `XOR3` and `SPILL` are module constants, `SPILL` listed rather than computed by a `while` loop in a `const` block; the AVX2 kernel names the nibble shift and the table load (`nibbles`, `t128`) so the proof can refer to them; the NEON pair loop tests `top.len() - lane >= 2` instead of `lane + 2 <= top.len()`.
- Tests (`tests/equivalence/ntt_simd.rs`): each kernel, both directions, every offset of short rows, edge rows and twiddles (0, 1, all ones, the top bit, every top nibble) and random ones, against production's butterfly in the production field; `butterfly_lanes` and `transposed_butterfly_lanes` on every row length up to 40; and production's own kernels, which are private, through `encode_interleaved_in_place` on 8 to 31 lanes, reproduced by a layer-by-layer driver built from the verified `butterfly_lanes`. Run natively (AVX-512), with the AVX2 flags, and under qemu with and without SHA3.

### The embedding `φ₈` (`src/phi8_tower.rs`)

`φ₈` (`phi8`) is the GF(2)-linear map sending the byte `x^i` to `PHI_8_BASIS[i]` in `K` (`phi8_basis`); `phi8_e(a)` is `φ₈(a)` in `E`. Annex `c` calls it the subfield embedding of `GF(2^8)` in `E`, and flock's univariate skip domain is `φ₈(0..64)`.

- `build_phi8_table_192` fills entry `v` with `φ₈(v)` embedded in `E`; so does the static `PHI_8_TABLE_192`, and `phi8_192(a)` returns `phi8_e(a)`.
- `φ₈` is GF(2)-linear (`lemma_phi8_xor`), so `φ₈(0..64)` is the span of `φ₈(1), φ₈(2), .., φ₈(32)`, and zero only at zero (`lemma_phi8_nonzero`, from injectivity).
- `φ₈` is multiplicative into `K`: `φ₈(a * b) = φ₈(a) φ₈(b)` for all bytes, `a * b` the product of `GF(2^8)` (`f8_mul`) and the right side `k_mul` (`lemma_phi8_mul`). The proof: `φ₈(x a) = φ₈(x) φ₈(a)` (`lemma_phi8_mulx`), which by linearity needs only the eight monomials, eight products of concrete constants in `K` checked by bit-vector evaluation of the closed-form carry-less product (`clmul64_closed`, `lemma_k_mul_closed`); then `φ₈(x^i b) = φ₈(x^i) φ₈(b)` by induction on `i` and associativity in `K`, and the general product by linearity in the left factor.
- So `φ₈` is a ring homomorphism into `E`, `φ₈(1) = 1`, `φ₈(0) = 0`, and it is injective (the eight basis images are GF(2)-independent), with image in `K` (`c1 = c2 = 0`) (`lemma_phi8_e_homomorphism`). Its image is therefore a subfield of `E` with 256 elements. That it is the only one (production's doc comment) is not proven: it would need that a polynomial of degree 256 has at most 256 roots.

### Bit folds and linear maps of `E` (`src/bit_fold.rs`)

The portable arm of `crates/primitives/src/bit_fold.rs` (`bit_fold/portable.rs`) and the wrappers `BitFold`, `F192Map`, `Sliced`. Bit `s` of a row of bytes is bit `s % 8` of byte `s / 8`; coordinate bit `b` of an `E` value is bit `b % 64` of coefficient `b / 64`.

- Tables: `lookup_tables(w)` returns one table per whole chunk of 8 weights, entry `[j][v]` the sum of `w[8j + i]` over the set bits `i` of `v` (`byte_sum`); the lowest-set-bit recurrence is proven to build exactly that (`lemma_byte_sum_clear`). The weight of bit `s` is recovered as table `s / 8` at the single bit `s % 8` (`lemma_byte_sum_monomial`), so `Imp::new(w)` holds the weights `w`, truncated to whole chunks.
- Fold: `BitFold::new(w)` (for 8, 16, 32, 64 or 128 bytes per row, production's `assert!` being the `requires`) then `fold_block(rows, out)` sets `out[p] = sum_{s : bit s of rows[p]} w_s` (`fold_spec`) for every `p < rows.len()`, the definition the module doc states, and leaves `out[rows.len()..]` unchanged. The table lookups add up to that sum byte by byte (`lemma_tables_fold`).
- Linear maps: `F192Map::new(w)` then `apply_add(xs, out)` (and `apply_sliced_add` on `Sliced::new(xs)`) adds `map(w, xs[p]) = sum_{b : coordinate bit b of xs[p]} w_b` (`map_spec`) to `out[p]` for every `p < out.len()`: the 24 little-endian bytes of a value fold to its map (`lemma_row_sum_le_row`). The map is GF(2)-linear (`lemma_coord_sum_add`, `lemma_coord_sum_zero`) and every element is the sum of the coordinate vectors of its set bits (`lemma_units_sum`), so a GF(2)-linear `Φ: E -> E` is the `F192Map` of the weights `Φ(unit(b))`, which is how ring switching uses it.
- `after_mul(c)` returns the map with weights `map(w, unit(b) * c)` and, for every `x`, `after_mul(c)(x) = map(w, x * c)` (`lemma_after_mul`, from the linearity of the map and the distributivity `(a + b) c = a c + b c` in `E`, `lemma_e_mul_add_left`). This is the identity production's `composed_map_is_the_map_after_the_product` tests.
### Lane-interleaved NTT (`src/ntt_lanes.rs`)

A buffer of `m` interleaved lanes holds word `v` of lane `l` at word `m v + l` (`lane(data, m, l)`).

- One layer commutes with taking a lane: lane `l` of a forward or inverse layer's output is the same layer applied to lane `l` alone (`lemma_lane_layer`), so the forward layers `start..end` and the inverse layers transform every lane independently (`lemma_lane_forward_layers`, `lemma_lane_inverse_layers`). This holds for any table and any lane count, and `forward_scalar_from_layer` computes `forward_layers` for any lane count.
- Evaluation: for `AdditiveNttF64::standard(dim)` on `m` lanes of `2^dim` rows, output word `m v + l` is `P_l(v) = sum_j a_(m j + l) X_j(v)`, lane `l`'s novel-basis polynomial at the domain point `v` (`lemma_standard_lanes_forward_evaluates`).
- Encoding: the encoder at rate `2^-r` on `m` lanes (layers `r..dim` on `2^r` copies of an `m`-lane message of `2^(dim - r)` rows, as `encode_interleaved_in_place` lays it out) gives at word `m v + l` the evaluation at `v` of the polynomial whose coefficients are lane `l` of the message, zero-padded: every lane is Reed-Solomon encoded (`lemma_standard_lanes_encode_evaluates`).
- No new executable copy: the lanes theorems are about `forward_scalar_from_layer`, already checked against `encode_interleaved_in_place` for 1, 2, 3, 5 and 8 lanes, at rate 1 and at several rates, in `tests/equivalence/ntt.rs`.

### `GF(2^8)` additive NTT of flock's zerocheck (`src/flock_ntt.rs`)

Over the field of `src/gf2_8.rs`, with the standard basis `b_i = x^i` (the byte with bit `i` alone), the subspace polynomials `s_0(x) = x`, `s_i(x) = s_(i-1)(x) (s_(i-1)(x) + s_(i-1)(b_(i-1)))` and `Ŵ_i(x) = s_i(b_i)^(-1) s_i(x)`. `novel8(m, a, x)` is the novel-basis polynomial `sum_(j < 2^m) a_j X_j(x)`, `X_j = prod_(i < m) Ŵ_i(x)^(bit_i(j))`, written by its split on the top bit of `j`; `lemma_novel8_flat` proves it equal to the flat sum `novel8_sum`. `fft_spec` and `ifft_spec` are the recursions of `fft_rec` and `ifft_rec`.

- Subspace polynomials: each `s_i` and `Ŵ_i` is GF(2)-linear, `s_i` vanishes exactly on `{0, .., 2^i - 1}` (`lemma_subspace_poly8_vanishes`, `lemma_subspace_poly8_roots`, from `GF(2^8)` having no zero divisors), so `Ŵ_i(b_i) = 1` for every `i < 8` (`lemma_normalized_poly8_at_basis`).
- Twiddles: `compute_twiddles(k, β)` (any `k <= 8`, any offset `β`) returns `2^k - 1` entries, entry `2^d - 1 + j` (depth `d < k`, block `j < 2^d`) being `Ŵ_(k-1-d)(β + j 2^(k-d))`, `Ŵ` of the first point of the block, as its documentation's layout says (`twiddles_of`, the postcondition).
- Butterflies and recursions: `fft_butterfly`, `ifft_butterfly`, `fft_rec` and `ifft_rec` compute `fft_spec` and `ifft_spec` on every power-of-two length; `AdditiveNttGf8::forward` and `inverse` are `fft_rec` and `ifft_rec` from the root.
- Evaluation: with the table of `new(k, β)`, output word `u` of `forward` on `2^k` coefficients is `P(β + u)` (the point `β ⊕ u`, no bit reversal), the novel-basis polynomial of the input at the `u`-th point of the domain `β + span{1, 2, .., 2^(k-1)}`, as the struct's documentation claims (`lemma_fft_evaluates`).
- Inverse: `inverse` undoes `forward` and `forward` undoes `inverse`, for any table and any buffer (`lemma_ifft_after_fft`, `lemma_fft_after_ifft`), so `inverse` interpolates: on the evaluations of `P` it returns `P`'s coefficients (`lemma_ifft_interpolates`).
- The extension matrix: let `M = forward_Λ ∘ inverse_S` for any two `2^k`-point NTTs (offsets `β_s`, `β_l`), column `t` being the image of `e_t` (`lde_column`). Then `M[i][j] = M[i ⊕ j][0]` (`lemma_lde_shift`): the interpolant of `e_j` on `S` is the interpolant of `e_0` translated by `j`, because a translate of a novel-basis polynomial is again one (`translate`, `lemma_translate`) and the transform is injective. This is the "XOR-shift relation" `inv_table.rs` relies on.
- The table: `InvNttTableByteSingleGf8::new(ntt_s, ntt_l)` (`3 <= k <= 7`) holds, at row `w`, the XOR of the columns `t < 8` of `M` over the set bits `t` of `w`, as its field's documentation claims (`table_row`, the postcondition), for any two NTTs of the same `k`.
- `apply_scalar` applies `M`: its output word `i` on a row of `ell / 8` bytes is `sum_b T[bytes[b]][i ⊕ 8b]` (the postcondition), which equals `sum_j x_j M[i][j]`, `x_(8b+t)` being bit `t` of byte `b`, for the table of two NTTs built by `new` (`lemma_table_applies_lde`).
- Copies: `compute_twiddles` and `new` take `k <= 8` as a precondition (the domain lies in `GF(2^8)`; production does not check it), `fft_rec` and `ifft_rec` take a power-of-two length and in-table twiddle reads (production's only caller guarantees both), the `assert!`s become `requires`, iterator loops and `copy_from_slice` become index loops, the `continue` of `new`'s last loop becomes an `if` (Verus's `for` has no `continue`), and `w.trailing_zeros()` is taken on `w as u64` (vstd specifies it for `u64`, not `usize`).

### Fiat-Shamir step block (`src/fiat_shamir.rs`)

- `step_block(scalars, tag)` and `builder_step_message`, a value-level model of the message the circuit's `Builder::step` hashes, put the last scalar in words 4 to 6, the preceding scalar (if present) in words 0 to 2, the count in word 3 and the tag in word 7, with zero elsewhere (`block_word`). For equal scalar/tag inputs these models produce the same block. This does not prove the circuit constraints bind its wires to those inputs.
- On the domain production takes (at most `MAX_PENDING = 2` scalars, longer slices panic) the block names its scalars and its tag (`lemma_step_block_decodes`), so two steps with the same block absorb the same scalars, so the same count, under the same tag (`lemma_step_block_injective`). This holds for every tag word; the four `DS_*` tags are pairwise distinct (`lemma_tags_distinct`).
- This is injectivity of the current two-scalar step encoding, not a security theorem for the Fiat-Shamir transform or a proof about any replacement transcript or duplex design.

### The equality polynomial and multilinear evaluation (`src/multilinear.rs`)

Over `E`, `eq(r, x) = prod_i (r_i x_i + (1 + r_i)(1 + x_i))` (`eq_poly`, `eq_factor`; `1 - a = 1 + a` in characteristic 2), and a table over `n` variables holds at index `x` the value at the cube point whose coordinate `i` is bit `i` of `x` (`cube_point`, `eq_at`). `is_eq_table(t, r, seed)` says `t[x] = seed * eq(r, x)` for all `2^n` indices.

- `eq_eval(r, x)`, the product of `1 + r_i + x_i`, is `eq(r, x)` for every `x` in `E^n`, not only on the cube (`lemma_eq_factor_sum`).
- `eq_table`, `eq_table_seeded` and `fill_eq_table_uninit` build `seed * eq(r, .)` entry by entry, LSB first, for `n < 64`: the doubling build below `2^16` entries (each level writes `v r_i` to the high child and `v (1 + r_i)` to the low one, `lemma_eq_at_high`) and the tensor build above (`eq(r, (h << L) | l) = eq(r[..L], l) eq(r[L..], h)`, `lemma_eq_at_tensor`).
- `shrink_eq_low` and `shrink_eq_high` sum the low pairs, or the two halves, of any table; on `seed * eq(r, .)` the result is `seed * eq(r[1..], .)`, or `seed * eq(r[..n-1], .)` (`lemma_shrink_low_eq`, `lemma_shrink_high_eq`).
- `SplitEq::with_low_vars`, `with_high_vars`: the two tables are `eq` over `r[..L]` and `r[L..]`; `at(x)` is `eq(r, x)`.
- `interp(lo, hi, t) = (1 + t) lo + t hi`, and `interp_k` the same on `K` endpoints.
- `mle_eval(table, point)` is the multilinear extension `sum_x eq(point, x) table[x]` (`mle`) of the `K`-valued table, on both paths: folding the lowest variable (`fold_low_k`, then `fold_ladder`, by `lemma_mle_fold_low`), and from three variables the packed low `eq` table, one `dot_base` per row, then the ladder over the rows (`lemma_mle_blocks`).
- `window_denominator(2^log)` (and the table `DENOMINATORS` it reads, computed at compile time) is `(prod_{k=1}^{2^log - 1} φ₈(k))^(2^64 - 2)`, the inverse in `K` of the product of the window's nonzero nodes (`lemma_denominator_inverts`; the product is nonzero since the nodes are and `K` has no zero divisors).

### The univariate-skip domain (`src/skip_domain.rs`)

`SkipDomain` of `crates/flock/src/zerocheck/skip_domain.rs` is generic over `fiat_shamir::arith::Arith`; the copy is instantiated at `Native` (its trait methods and the defaults it inherits copied as inherent methods). The domain of `l = 2^k` nodes (`k < 8`) is `S = {s_i = φ₈(i)}`; `V_l(z) = prod_i (z + s_i)` (`vanishing_spec`) and `L_i(z) = prod_{k != i} (z + s_k) / prod_{k != i} (s_i + s_k)` (`lagrange_basis`), the textbook Lagrange basis, with `L_i(s_j) = [i = j]` (`lemma_lagrange_basis_at_nodes`).

- `vanishing_coefficients` returns the coefficients of `V_l` as a linearized polynomial, `V_l(x) = sum_j c_j x^(2^j)` for every `x`, and it is monic (production's `debug_assert!`); adding a basis element `a` takes `V` to `V(x)^2 + V(a) V(x)` (`lemma_lin_step`, `lemma_vanishing_double`). `vanishing(z)` is `V_l(z)`.
- Every node of a window sees the same `prod_{k != i} (s_i + s_k)`: `k -> i ^ k` permutes the window (`lemma_prod_xor`), so it is the product of the nonzero nodes, which `window_denominator` inverts (`lemma_weight_inverts`).
- `lagrange_at(z, V_l(z), values)` (through `lagrange_scale`, `inverses`, `lagrange_with`) is `sum_i values_i L_i(z)` (`lagrange_sum`), and `first_round_at(z, V_l(z), values)` is `sum_i values_i L_(l+i)(z)` over the window of `2l` nodes (`window_sum`): the interpolant of `values` on the coset `{s_l, .., s_(2l-1)}` and of zero on `S`, for every `z` off the respective theorem's excluded nodes. At a node production returns zero because its vanishing factor is zero and `1 / 0 = 0`. This need not equal the supplied value on `S` for `lagrange_at` or on `Lambda` for `first_round_at`; zero is the correct first-round value on `S`. Under a uniform challenge in `E`, the exceptional set for each operation has at most `128 / 2^192` probability and can cause rejection of an honest proof. The proofs do not establish transcript challenge uniformity.

## Trust base and assumptions

- Kernel theorems do not use `assume` or `admit` to discharge their obligations. The trust boundary explicitly includes `assume_specification`, external vector type declarations, `axiom fn` layout facts, and `#[verifier::external_body]` memory helpers in the intrinsic modules. These are assumptions, not proved ISA or pointer-safety results.
- The driver has explicit trusted adapters in `src/parallel.rs`: slice/permission borrowing, raw slice construction, core pointer/integer specifications, worker count, and exactly-once joined dispatch. `with_scratch` trusts the thread-local scratch borrow and callback contract. Their `external_body`/`assume_specification` annotations are trust boundaries, not solved proof obligations.
- `src/blake2s.rs` retains an explicit `assume_specification` for `u32::rotate_right`, absent from the pinned `vstd`: for `0 < n < 32` it equals `(x >> n) ^ (x << (32 - n))`. A deterministic test checks samples and edge cases against Rust's implementation, but does not prove this trusted library contract.
- Verus and Z3 are trusted: Verus's encoding of Rust (machine integers, the truncating casts and shifts the code
  uses, arrays, `Vec`) and Z3's answers, in both its integer and its bit-vector modes.
- `vstd`'s specifications of what the copies call are trusted: integer `From`, the operator traits, `Vec` and
  slice indexing (by index and by range), `slice_to_vec`, `vec![x; n]`, `Vec::clone`, `Vec::truncate`,
  `Vec::as_mut_slice`, `split_at_mut`, `u64::trailing_zeros`, and its proven `pow2` and division lemmas.
- `src/ntt.rs` declares `global size_of usize == 8`: the NTT proofs are for 64-bit targets, which Verus checks
  when it compiles the crate.
- Copy-to-production correspondence is tested, not proved. `builder_step_message` has no public production counterpart (`Builder` is in `leanvm_core`'s private `rec` module); production's `rec::transcript::tests::the_circuit_replays_the_native_transcript` checks the circuit/native transcript relationship separately. `SkipDomain::first_round_at` and `SkipDomain::new` are compared with the references used by production's own tests.
- `PHI_8_TABLE_192`, `DENOMINATORS` and `SkipDomain::FLOCK` are written in Verus's `exec static` / `exec const` form, which states what the initializer returns; Verus checks the initializer like a function body. The parallel pass of `fill_eq_table_uninit` is copied as a loop over the same rows in order.
- `src/intrinsics/mod.rs` trusts `core::mem::transmute` through the uninterpreted `transmuted` view. Per-architecture layout axioms relate byte, word and polynomial views in little-endian lane order. Intrinsic specifications and memory contracts are compared with their executable models, not proved from ISA semantics, compiler lowering or hardware.
- Shared x86 contracts in `src/intrinsics/x86.rs`, exercised by `tests/equivalence/intrinsics_x86.rs`, specify scalar/register conversion, word constructors, XOR/AND, wrapping 64-bit addition, PCLMULQDQ and VPCLMULQDQ per 128-bit lane (immediate bits 0 and 4 choose operands), BMI2 bit deposit, low/high word unpacking, lane shifts, lane-local byte shuffles, broadcast, 64-bit permutations, two-source permutations, 128-bit-block shuffles, and ternary Boolean logic. Layout axioms are `axiom_m128_bytes`, `axiom_m256_bytes`, `axiom_m512_bytes`, `axiom_m128_as_u128`, `axiom_m256_as_pairs`, `axiom_m512_as_pairs`, and `axiom_m512_from_words`. Their source declarations enumerate each intrinsic and immediate domain.
- Shared AArch64 contracts in `src/intrinsics/aarch64.rs`, exercised by `tests/equivalence/intrinsics_aarch64.rs`, specify `vmull_p64`, `vmull_high_p64`, `vdupq_n_u64`, `veorq_u64`, `veor3q_u64`, `vzip1q_u64`, and `vgetq_lane_u64`. Layout axioms are `axiom_u128_as_u64x2`, `axiom_u64x2_as_u128`, and `axiom_u64x2_as_p64x2`. `gf2_64::aarch64::hide_lanes` trusts the empty inline-assembly barrier to preserve its registers; reduction tests exercise that wrapper through `reduce_pair_pmull4`.
- `src/bit_fold.rs` relies on `vstd`'s specification of `u8::trailing_zeros` (with its proven `axiom_u8_trailing_zeros`) and of `Vec::push`, `Vec::as_slice` and `Vec::as_mut_slice`.
- `src/intrinsics/aarch64_gfneon.rs` and `src/intrinsics/x86_gfneon.rs` (the `E` aarch64 kernels and the `GF(2^8)` SIMD arms): `assume_specification`s of `vreinterpretq_p64_u64`, `vcreate_u64`, `vcombine_u64`, `vextq_u64`, `vdupq_laneq_u64`, `vdup_n_p8`, `vmull_p8`, `vreinterpretq_u16_p16`, `vreinterpretq_u8_u16`, `vgetq_lane_u16`, `vshlq_n_u16`, `vget_low_u8`, `vget_high_u8`, `vuzp1q_u8`, `vuzp2q_u8`, `veorq_u8`, `_mm256_setzero_si256`, `_mm256_set1_epi8`, `_mm256_add_epi8`, `_mm256_cmpgt_epi8`; the layout axioms `axiom_u8x8_as_p8x8`, `axiom_u64_as_p8x8`, `axiom_words_as_u64x2`; and the `external_body` memory helpers `gf2_64x3::aarch64::load_f192` and `store_f192`, whose bodies are production's loads and stores. Each is compared with the hardware in `tests/equivalence/intrinsics_aarch64_gfneon.rs` and `intrinsics_x86_gfneon.rs` (under `qemu-aarch64-static` for NEON), through the executable twins `model_vmull_p8_lane`, `model_uzp_u8_lane`, `model_ext_u64_lane`, `model_u16_byte`, `model_cmpgt_epi8_lane` where the lane semantics is more than a move. `vstd`'s `MaybeUninit` specification (`as_option`) states what `store` writes.
- The SIMD arms of the bit transposes assume the specifications of the intrinsics they call, each tied to the hardware by a differential test that runs the real intrinsic on edge and random operands and compares every lane with the specification's executable twin:
  - `src/intrinsics/x86_bits.rs`, tested by `tests/equivalence/intrinsics_x86_bits.rs`: `_mm256_unpacklo_epi8`, `_mm256_unpackhi_epi8` (`unpacklo_epi8_lane`, `unpackhi_epi8_lane`), `_mm512_permutexvar_epi8` (`permutexvar_epi8_lane`: byte `idx[k] & 63`, tested with the top index bits set), and `_mm256_gf2p8affine_epi64_epi8`, `_mm512_gf2p8affine_epi64_epi8` (`gf2p8affine_lane`: per byte, bit `i` is the parity of `A.byte[7 - i] & x` XOR bit `i` of the immediate, `A` the 64-bit word holding the byte; tested on random and edge matrices with the immediates `0, 1, 0x63, 0x80, 0xAA, 0xFF`, and the twin `model_affine_byte` against Intel's pseudocode written with `count_ones`). The memory helpers `load128_bytes`, `load256_bytes_at`, `store256_bytes_at`, `load512_bytes`, `store512_bytes` (`external_body`, each body the production load or store) are tested at several offsets, the stores also for leaving the other bytes alone.
  - `src/intrinsics/aarch64_bits.rs`, tested by `tests/equivalence/intrinsics_aarch64_bits.rs` (under `qemu-aarch64-static` from x86): `vqtbl4q_u8` (`tbl4_byte`: the 64-byte table, zero from index 64 on), `vreinterpretq_u64_u8`, `vreinterpretq_u8_u64` (the little-endian layout, `u64x2_byte`), `vandq_u64`, `vshrq_n_u64` (zero at 64), `vshlq_n_u64`, and the helpers `vld1q_u8_16`, `vld1q_u8_at`, `vst1q_u8_at`. The view `u8x16` of `uint8x16_t` is the `transmute` to `[u8; 16]`; `uint8x16x4_t` is a transparent external type (its four public fields).
  - The shared ones of `src/intrinsics/x86.rs` (`_mm256_shuffle_epi8`, `_mm256_permute4x64_epi64`, `_mm256_broadcastsi128_si256`, `_mm256_set1_epi64x`, `_mm256_and_si256`, `_mm256_xor_si256`, the 64-bit lane shifts, `_mm512_set1_epi64`, and the byte layout axioms `axiom_m128_bytes`, `axiom_m256_bytes`, `axiom_m512_bytes`) and `src/intrinsics/aarch64.rs` (`vdupq_n_u64`, `veorq_u64`).
- `src/ntt_simd.rs` relies on the intrinsic specifications of `src/intrinsics/x86.rs` (`_mm512_set1_epi64`, `_mm512_xor_si512`, `_mm512_clmulepi64_epi128`, `_mm512_unpacklo_epi64`, `_mm512_unpackhi_epi64`, `_mm512_srli_epi64`, `_mm512_slli_epi64`, `_mm512_ternarylogic_epi64`; `_mm256_set1_epi64x`, `_mm256_xor_si256`, `_mm256_clmulepi64_epi128`, `_mm256_unpacklo_epi64`, `_mm256_unpackhi_epi64`, `_mm256_broadcastsi128_si256`, `_mm256_srli_epi64`, `_mm256_shuffle_epi8`, `_mm256_add_epi64`, with the byte layout axioms `axiom_m128_bytes`, `axiom_m256_bytes`) and `src/intrinsics/aarch64.rs` (`vdupq_n_u64`, `veorq_u64`, `vgetq_lane_u64`, `vmull_p64`, `vmull_high_p64`, with `axiom_u128_as_u64x2`, `axiom_u64x2_as_p64x2`, and those `reduce_pair_pmull4` uses), and on the trusted memory helpers of `src/intrinsics/x86_nttsimd.rs` (`loadu512_at`, `storeu512_at`, `loadu256_at`, `storeu256_at`, `loadu128_bytes`) and `src/intrinsics/aarch64_nttsimd.rs` (`vld1q_u64_at`, `vst1q_u64_at`): `external_body` functions whose bodies are production's load or store at the offset and whose specification is the words they read or write. `tests/equivalence/intrinsics_x86_nttsimd.rs` and `intrinsics_aarch64_nttsimd.rs` check each helper at every offset of random rows.

## Not covered

- Production-source equivalence, compiler correctness, CPU correctness and absence of undefined behavior in trusted memory helpers are not established by these proofs. Production differential coverage includes:
  - `K`: `field::gf2_64::tests::mul_and_square_match_the_reference` (PCLMULQDQ and PMULL products, `pdep` square),
    `neon_variants_match_software`.
  - `E`: the AArch64 and x86 SIMD copies are verified as described above. Production also checks them with `field::gf2_64x3::tests::products_match_software`, `batched_products_match_software`, `lane_products_match_software`, `register_products_match_software`, `batched_mixed_products_match_scalar`, `mixed_sums_match_software`, and `planar_products_match_software`.
  - `GF(2^8)`: the SIMD arms are verified (above); production also tests them with `software_matches_neon`, `neon_gf8_mul_vec16_matches_scalar`, `avx2_gf8_mul_vec32_matches_scalar`, `neon_gf8_reduce_vec16_matches_scalar`.
  - Bit transposes: `bits::tests::every_arm_matches_reference`; the SIMD arms of `bit_transpose_64bytes` are also verified (see above).
  - Bit folds and `F192Map`: `bit_fold::tests::fold_block_matches_definition`, `f192_map_matches_definition`, `composed_map_is_the_map_after_the_product`, `avx2_products_match_definition` (every AVX2 product, also on GFNI machines). The equivalence tests of this crate compare the verified portable copies with whatever arm the machine dispatches.
  - NTT butterflies: verified (`src/ntt_simd.rs`, above); production's driver tests `ntt::additive_ntt_f64::tests::interleaved_parallel_matches_scalar` (forward) and `whir::induce::tests::blocked_and_gathered_transposes_match_layer_by_layer` (transposed) run them too.
  - flock's LDE table (`apply_v128` on NEON and SSE2, `apply_avx2`, `apply_avx512`/`apply_zmm`): `zerocheck::ntt::inv_table::tests::apply_simd_matches_apply_scalar`, and `tests/equivalence/flock_ntt.rs`, which compares the dispatched `apply` with the verified `apply_scalar` on every single-byte row and on random rows. The round-1 kernels that read the table through `data_ptr` and `apply_zmm` (`zerocheck/round1.rs`) are not covered.
- Production's NTT cache planner, fused-message scheduling/replication, row callbacks, streaming store ordering, and `transpose_lane_major` are not proved. The parallel refinement above proves populated-replica computation with explicit plan inputs. The inverse reference in `ntt.rs` remains covered; the separate transposed driver is outside this refinement.
- BLAKE2s's raw-pointer batch driver, pointer load/store safety, dispatch and SIMD implementations are not verified. Batch comparisons exercise the backend selected by the test build.
- Bit folds (`crates/primitives/src/bit_fold.rs`): `BitFold::at_level`, which builds its weights with `multilinear::eq_table` (copied in `src/multilinear.rs`) and then calls `BitFold::new`, and `BitFold::fold_quads` (AVX-512 with GFNI only) are not copied. Only `out[..rows.len()]` of `fold_block` is documented and compared: past it the portable arm leaves `out` as it was (proven) and the SIMD arms store the fold of a zero row.
- Of `multilinear.rs`, the parallel `mle_eval_par`, `SplitEq::weighted_sum` and its SIMD variants, the high folds (`fold_high_k`, `fold_high_inplace`, `interp_into`), `barycentric_sum`, `skip_lagrange_weights`, `poly_eval` and the inner products are not copied.
- The circuit's constraints (that the hash row's wires carry the message `builder_step_message` computes) are not modeled; only the message is.
- `AdditiveNttF64::standard(0)` panics while building an empty first table row. The supported constructor domain is `1 <= dim <= 63`, now stated in its production documentation; zero-dimensional construction is not proved or fixed here.

## Reproduce

Verus release `0.2026.10.04.426d8b0` (commit `426d8b01e7ffb910a36c15e1f870ff985bb61eef`, with its bundled Z3
4.16.0, built against Rust 1.98.1), and `vstd = "=0.0.0-2026-10-04-0306"` from crates.io, the `vstd` of that
release. From the repository root:

```bash
verification/verus/verify.sh                          # every proof; installs the pinned Verus under ~/.verus if missing
verification/verus/verify.sh gf2_64                   # one module
(cd verification/verus && cargo test --release)       # the verified copies against production
```

`verify.sh` downloads the pinned Linux x86-64 release if needed, installs its Rust toolchain with `rustup`, and checks every configuration listed above. Set `VERUS_HOME` to install elsewhere, `VERUS_THREADS` to control solver parallelism (default 4), and `VERUS_CONFIGS` to select configurations. Solver and equivalence counts belong in the PR verification report, not a performance claim.

The script isolates whole-crate and per-module proof caches, because changing the forwarded module argument must not reuse a different module's cached result. `CARGO_TARGET_DIR` selects the cache root; configuration and proof-selection directories are appended.
