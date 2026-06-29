# PQ-DAS V1 on LeanVM: Implementation Plan

## 1. Executive recommendation

For the first end-to-end demo, use the following profile:

| Item | V1 demo choice |
|---|---|
| LeanVM version | Pin commit `2d4148a6082c85769dbf5ef7f3dd61cade17eeb4` (v0.8 / `spec-latest`) |
| Data and RS base field | KoalaBear, `p = 2^31 - 2^24 + 1 = 0x7f000001` |
| RS domain | Multiplicative two-adic domain of size `m = 2^s`, `s <= 24` |
| RS rate | `rho = 1/2` initially |
| RS layout | Systematic: interpolate the first `k=m/2` evaluations, then evaluate on all `m` points |
| Cell size | `c = 8` KoalaBear elements |
| Application hash | LeanVM-native Poseidon1, width 16, rate 8 |
| Digest | 8 KoalaBear elements |
| Merkle tree | Binary; Poseidon sponge for leaves and Poseidon feed-forward compression for internal nodes |
| RS membership | Special `rho=1/2` barycentric check, with challenge and arithmetic in the quintic extension |
| Public input | One 8-element Poseidon digest committing to the full typed statement and parameter profile |
| LeanVM proof rate | Benchmark WHIR rates `1/2`, `1/4`, `1/8`, and `1/16`; start with `1/2` |
| Security mode | Default proven/Johnson-bound mode, not `prox-gaps-conjecture` |

Do not make the first demo generic over the base field or hash inside the LeanVM
guest. Those are currently native, effectively fixed parts of LeanVM. Make the
application layer generic over parameter profiles so that alternate constructions
can be benchmarked as separate compiled programs or, for a different field/hash,
against a separate LeanVM build.

## 2. Corrections required in the construction document

### 2.1 Symbols and cells are currently conflated

The document first defines `w[i,j]` as a symbol and later reuses it as a cell.
Use distinct notation:

- `x[i,s]` for field symbol `s`, where `0 <= s < m`.
- `cell[i,j] = x[i,j*c .. (j+1)*c]`, where `0 <= j < ell=m/c`.
- A queried column `j` contains `n*c` field elements, not `n` field elements.

If queries return cells, the reconstruction threshold is:

`t_cells = ceil(k/c)`,

provided cells align with consecutive evaluation positions. The current `t=k`
is correct only when one query returns one field symbol.

### 2.2 Hash inputs need exact serialization and domain separation

Replace every ambiguous concatenation with a typed field-element transcript.
At minimum, bind:

- protocol/version identifier;
- parameter-profile identifier;
- `n`, `m`, `k`, `c`, `ell`, RS check type;
- row index for row hashes;
- column index for column hashes;
- exact logical input length;
- all row hashes and the column Merkle root.

Use separate domain tags for:

- row/systematic-data hash;
- column/cell hash;
- Merkle leaf;
- public statement;
- RS membership challenge.

For Merkle internal nodes, V1 should use the dedicated feed-forward compression
primitive. Its operation and fixed `digest || digest` input shape provide
structural separation from the tagged variable-length leaf hash. Adding an
explicit internal-node tag would require an additional permutation or a
different tree construction.

### 2.3 One base-field linear check is not sufficiently sound

A single random linear identity over KoalaBear has failure probability roughly
`1/p`, only about 31 bits. Use a challenge in LeanVM's degree-5 extension field
and evaluate the membership identity there. This gives an algebraic error scale
near `1/p^5` before accounting for the rest of the proof system.

LeanVM exposes `dot_product_be`, which computes a dot product between extension
and base-field vectors. It is the natural precompile for this check.

### 2.4 Fiat-Shamir challenge derivation must be verifier-reproducible

The RS challenge cannot be sampled privately by the prover. It must be derived
from a domain-separated transcript that already binds:

- the complete parameter profile;
- all `h_i`;
- the Merkle root;
- optionally a batch/slot/block identifier.

The host verifier must derive the same challenge. Any precomputed check vector
`L` must either be recomputed by the verifier and bound into the statement, or
be derived and checked inside the guest.

### 2.5 Systematic RS encoding must be stated precisely

For `U = {omega^0, ..., omega^(m-1)}`, define `P_i` as the unique degree-`<k`
polynomial satisfying:

`P_i(omega^j) = b[i,j]` for `0 <= j < k`.

Then set `x[i,j] = P_i(omega^j)` for all `0 <= j < m`. This makes the first
`k` evaluations systematic without confusing coefficients and evaluations.

## 3. LeanVM compatibility findings

### 3.1 Fields

LeanVM VM arithmetic uses:

- Base field `F = KoalaBear`.
- Prime `p = 2^31 - 2^24 + 1`.
- Two-adicity `24`, so power-of-two RS domains up to `2^24` exist.
- Proof extension field `EF = QuinticExtensionFieldKB`.

The guest language's ordinary values and memory cells are base-field elements.
Extension-field operations are available through the extension precompile.

Recommendation: use KoalaBear for the application RS code in V1. Using another
RS field would require non-native arithmetic inside the VM and would erase the
main performance advantage.

### 3.2 Hash

The native permutation is Poseidon1 over KoalaBear:

- width `16`;
- rate `8`;
- capacity `8`;
- digest length `8` field elements.

There are three relevant operations/conventions that must not be mixed:

- Application slice hash: `poseidon_hash_slice`, a left-to-right overwrite
  sponge using the raw Poseidon permutation and a length IV. The zkDSL
  `slice_hash` implementation matches it.
- WHIR-internal leaf hash: `hash_slice_rtl`, which absorbs in the opposite
  direction. It is an internal proving-system convention and should not be used
  as the PQ-DAS application hash.
- Merkle node hash: Poseidon feed-forward compression of two 8-element digests.

The repository has both host implementations and guest precompiles. Reuse their
exact semantics rather than implementing a new Poseidon wrapper. Add cross-tests
that compare every host hash against its zkDSL result.

An 8-element digest carries about 248 raw field bits, but generic collision
security is about 124 bits. This matches LeanVM's current stated proof target,
not a full 128-bit target.

### 3.3 Public input and witness model

LeanVM has exactly 8 public base-field elements. The recommended pattern is:

1. Host serializes the complete public PQ-DAS statement into field elements.
2. Host computes its 8-element Poseidon digest and uses that as public input.
3. The serialized statement and codeword matrix are supplied as named witness
   blobs via `ExecutionWitness`.
4. The guest recomputes the statement digest and asserts equality with public
   memory.

This lets `com = ({h_i}, root, pi)` remain externally readable while fitting
LeanVM's fixed public-input surface.

### 3.4 Proving-system parameters

Current defaults:

- degree-5 extension;
- claimed proven security about 124 bits;
- 16 grinding bits;
- WHIR starting inverse rates `2^1` through `2^4`;
- Johnson-bound mode by default;
- optional conjectural proximity-gap feature;
- maximum memory `2^26` field elements;
- maximum execution rows `2^24`;
- maximum Poseidon and extension-precompile rows `2^21`.

These table limits, especially `2^21` Poseidon rows, must be enforced by the
parameter validator before proving.

## 4. Encoding and hashing profile

### 4.1 External bytes to KoalaBear

Define this boundary explicitly. Recommended canonical V1 encoding:

- Pack 3 little-endian bytes into one KoalaBear element.
- Record the original byte length in the statement.
- Reject non-canonical field encodings on decode.

Three-byte limbs are always below the KoalaBear modulus and avoid rejection
sampling. Also benchmark one-byte-per-field-element encoding as a simple
reference. Do not directly reduce 32-bit words modulo `p`, because that is not
injective.

If the upstream data already consists of canonical KoalaBear elements, bypass
byte packing and mark the input encoding in the parameter profile.

### 4.2 Cell size

Start with `c=8` because it aligns with the Poseidon rate:

- row systematic data is naturally hashed in 8-element chunks;
- one row's contribution to a cell is one Poseidon rate block;
- padding is minimized;
- query and reconstruction accounting is simple.

Benchmark `c in {4, 8, 16, 32}` later. Larger cells reduce Merkle height and the
number of distinct queried cells needed for reconstruction, but increase query
bandwidth and column-hash work.

### 4.3 Column leaves and Merkle tree

For column/cell index `j`, serialize:

`tag_column || profile_id || j || n || c || cell[0,j] || ... || cell[n-1,j]`

Pad to a multiple of 8 with an unambiguous length-bearing scheme, then hash with
the LeanVM Poseidon slice hash.

Build a binary tree over exactly `ell` leaves. For V1 require `ell` to be a power
of two. Later, specify a fixed padding-leaf rule if non-power-of-two sizes are
needed.

Do not add an extra Merkle leaf hash over an already hashed `d_j` unless both
guest and external verifier intentionally use that two-level convention.

## 5. RS membership implementation

### 5.1 V1 path: special barycentric check

Use `rho=1/2`, `m=2k`, and the even/odd split from the design.

Recommended flow:

1. Derive an extension-field challenge `p_ext` from the typed public statement.
2. Set `q_ext = p_ext / omega`.
3. Compute or witness barycentric coefficients in the extension field.
4. If coefficients are witnessed, check each claimed inverse with a
   multiplication identity before use.
5. For each row, use `dot_product_be` for the even and odd halves.
6. Assert `A_i(p_ext) - B_i(q_ext) = 0` in all five extension coordinates.
7. Process rows with `parallel_range`.

This path has linear guest work per row and avoids an in-guest FFT.

### 5.2 Alternative paths for benchmarking

Implement behind a compile-time `MembershipCheck` profile:

- `SpecialBarycentricHalfRate`: first demo and expected best V1 option.
- `ParityExtension`: host computes the randomized parity vector over the
  extension field; verifier recomputes it; guest checks its binding and performs
  extension/base dot products.
- `GeneralBarycentricExtension`: supports arbitrary systematic subsets/rates,
  with higher coefficient-generation cost.

Do not benchmark a single base-field check as a production candidate. It can be
kept only as an explicitly insecure performance lower bound.

### 5.3 Batch soundness across rows

Checking each row with the same random dual-code vector is acceptable only after
a written soundness argument for the batched statement. For a conservative
first implementation, derive independent row challenges from:

`tag_rs || statement_digest || row_index`.

Then add a benchmark mode using a shared challenge to quantify the performance
benefit before deciding whether to adopt it.

## 6. Software architecture

Add a new workspace crate, tentatively `crates/pq_das`, with:

```text
crates/pq_das/
  src/
    config.rs          Typed parameter profiles and validation
    encoding.rs        Bytes <-> KoalaBear and systematic RS encoding
    hashing.rs         Typed Poseidon transcript and domain tags
    merkle.rs          Column commitment/open/verify
    membership.rs      Host-side challenge/coefficient generation
    statement.rs       Canonical public statement serialization
    prover.rs          LeanVM witness construction and prove_execution wrapper
    verifier.rs        Native transcript and LeanVM proof verification
    reconstruction.rs  Cell collection and RS erasure reconstruction
    benchmark.rs       Structured JSON benchmark reports
  zkdsl/
    main.py
    hashing.py
    membership.py
    utils.py
  tests/
```

Keep host and guest constants generated from one Rust `ParameterProfile`.
Compile separate bytecode per profile using `CompilationFlags::replacements`.
The bytecode hash is already included in LeanVM's Fiat-Shamir domain separation,
so proof verification remains bound to the selected compiled program.

## 7. Implementation workflow

### Phase 0: freeze the executable specification

- Resolve the symbol/cell notation and reconstruction threshold.
- Freeze canonical serialization and all domain tags.
- Decide whether RS row challenges are independent or shared.
- Specify malformed-input behavior and exact bounds.
- Add test vectors for byte encoding, Poseidon hashes, RS encoding, Merkle roots,
  and membership coefficients.

Exit criterion: Rust and a small independent reference script produce identical
vectors.

### Phase 1: native host implementation

- Implement parameter validation.
- Implement bytes-to-KoalaBear encoding.
- Implement systematic RS encode/reconstruct.
- Implement typed row/column hashing and Merkle open/verify.
- Implement all three membership checks natively.
- Add corruption tests for every row, symbol, digest, root, and path.

Exit criterion: `Com`, query verification, and `Ext` work without LeanVM.

### Phase 2: minimal LeanVM relation

- Create a zkDSL guest that reads a small fixed-size matrix.
- Recompute the statement digest.
- Recompute row hashes and column hashes.
- Recompute the Merkle root.
- Implement only `SpecialBarycentricHalfRate`.
- Wire `compile_program_with_flags`, `ExecutionWitness`,
  `prove_execution`, and `verify_execution`.

Start with a tiny profile such as:

`n=2, m=16, k=8, c=8`.

Exit criterion: one valid proof verifies and one mutation in every witness
component fails.

### Phase 3: scalable guest

- Replace fixed loops with bounded runtime loops where useful.
- Use `parallel_range` across independent rows and columns.
- Keep lengths and maxima compile-time bounded.
- Add preflight estimates for memory, execution rows, Poseidon rows, and
  extension rows.
- Increase through profiles until table limits or RAM become the bottleneck.

Exit criterion: repeatable proofs for representative DAS sizes with no hidden
out-of-range or unchecked dynamic indices.

### Phase 4: complete protocol API

- Expose `setup`, `commit`, `query`, `verify_query`, and `reconstruct`.
- Define serializable `Commitment`, `AuxData`, `Transcript`, and `ProofBundle`.
- Add deterministic query sampling from an explicitly specified randomness
  source.
- Support multiproofs or deduplicated Merkle paths as a later optimization.

Exit criterion: an end-to-end integration test covers commit, proof, sampling,
query verification, and reconstruction.

### Phase 5: benchmark and optimize

- Add JSON output with profile ID, git commit, machine data, and security mode.
- Profile guest instruction counts and all LeanVM table heights.
- Optimize only after separating RS, hashing, Merkle, witness generation,
  proving, verification, proof size, and query bandwidth.

## 8. Benchmark matrix

Sweep one axis at a time:

| Axis | Initial values |
|---|---|
| Rows `n` | `1, 2, 4, 8, 16, 32` |
| RS size `m` | `2^8, 2^10, 2^12, 2^14` |
| RS rate `rho` | `1/2`, then `1/4` |
| Cell size `c` | `4, 8, 16, 32` |
| Membership | special barycentric, parity, general barycentric |
| Row challenge | independent, shared |
| WHIR rate | `1/2, 1/4, 1/8, 1/16` |
| Security assumption | proven default; conjectural reported separately |
| Byte encoding | 3-byte limbs; 1-byte reference |

Record:

- encoding and reconstruction time;
- native hash/Merkle time;
- witness generation time;
- execution cycles;
- execution, Poseidon, and extension table rows;
- proving time and peak RSS;
- verification time;
- proof size;
- commitment size;
- query response bytes;
- minimum distinct cells required for reconstruction.

Never compare benchmark rows without including the LeanVM commit, compiled
bytecode hash, CPU features, thread count, and security mode.

## 9. Recommended first three deliverables

1. **Specification patch and native vectors**: fix the V1 document and publish
   canonical vectors for one tiny and one medium profile.
2. **Tiny LeanVM proof demo**: `n=2, m=16, k=8, c=8`, full relation, negative
   tests, and JSON timing.
3. **Parameter sweep demo**: compile-time profiles for several `n/m/c` values,
   all four WHIR rates, and at least two membership checks.

## 10. Decisions to defer

Do not block the first demo on:

- replacing KoalaBear or Poseidon;
- 128-bit rather than current approximately 124-bit LeanVM security;
- non-power-of-two RS or Merkle domains;
- a production network sampling policy;
- Merkle multiproofs;
- recursive aggregation of many PQ-DAS proofs.

These should remain explicit roadmap items. A different base field or hash is a
LeanVM backend experiment, not merely a PQ-DAS runtime parameter.
