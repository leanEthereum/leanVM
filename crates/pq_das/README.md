# PQ-DAS V1 LeanVM Demo

## Construction Algorithms and Code Mapping

- **Setup**
  - There is no standalone `setup()` function because this demo uses transparent LeanVM/WHIR parameters and compile-time profile constants.
  - `ParameterProfile::{TINY, MEDIUM, LARGE, STRESS, BLOB_128K_1, BLOB_128K_4, BLOB_128K_16}` defines $n$, $m$, $k$, $c$, and the WHIR inverse-rate exponent.
  - `ParameterProfile::validate()` checks the current implementation constraints: $m=2k$, power-of-two FFT and Merkle domains, $c\mid m$, KoalaBear two-adicity, and Poseidon rate alignment.
  - `ParameterProfile::profile_block()` and `fs_block()` provide the public domain-separated field encodings used by Fiat-Shamir.
  - `compilation_flags()` specializes the compact zkDSL program to the selected profile, while `default_whir_config()` selects the LeanVM proving parameters.

- **Encoding / Commitment algorithm $\mathsf{Com}({\sf pp},{\sf data})$**
  - `commit()` is the complete convenience entry point.
  - `commit()` calls `encode_and_commit()` to construct the codewords and public commitment.
    - `encode_and_commit()` calls `encode()`.
    - `encode()` calls `encode_blob()` once for every input blob.
    - `encode_blob()` calls `ifft()` on the size-$k$ systematic subgroup, zero-pads the coefficients to length $m$, and calls `fft()` on the size-$m$ domain.
    - `encode_and_commit()` calls `row_hash()` for every row, `column_hash()` for every cell column, and `merkle_layers()` to construct the binary Poseidon tree and ${\sf root}$.
  - `commit()` then calls `prepare_statement()`.
    - `prepare_statement()` calls `check_vector()`.
    - `check_vector()` calls `challenge()`, which calls `fiat_shamir_digest()`.
    - `prepare_statement()` compiles the profile-specific guest once and attaches the public row hashes, ${\sf root}$, and $L$ vector as read-only LeanVM data.
  - `commit()` finally calls `prove_codewords()`, which packages only the codeword matrix as the private witness and invokes LeanVM `prove_execution()`.

- **First verifier / query algorithm $\mathsf{V}_1({\sf com})$**
  - `ParameterProfile::sampling_count()` computes the minimum distinct-cell sample count matching LeanVM's current $124$-bit WHIR security target.
  - `sample_query_indices()` expands external randomness and the commitment ${\sf root}$ through Poseidon, uses rejection sampling to avoid modulo bias, and derives that many distinct cell-column indices.
  - `query()` receives one or more selected indices, extracts $W_{1,j},\ldots,W_{n,j}$ from the codeword matrix, and obtains the sibling digest at every Merkle level from the stored `merkle_layers`.
  - `query()` returns a `Transcript` containing each queried column of cells and its authentication path.

- **Second verifier algorithm $\mathsf{V}_2({\sf com},{\sf tran})$**
  - `verify()` is the combined entry point.
  - `verify()` first calls `verify_execution_proof()` with only the public `Commitment` and proof.
    - `verify_execution_proof()` calls `prepare_statement()` independently on the verifier side.
    - `prepare_statement()` recomputes Fiat–Shamir, $p$, $q$, every $L_j$, and the read-only public-data segment from the public profile, row hashes, and ${\sf root}$.
    - It then invokes LeanVM `verify_execution()` with the independently reconstructed bytecode.
  - `verify()` then calls `verify_openings()`.
    - `verify_openings()` recomputes each queried `column_hash`.
    - It folds the authentication path with `poseidon16_compress_pair()`.
    - It accepts only if every reconstructed root equals the public commitment ${\sf root}$.

- **Reconstruction algorithm $\mathsf{Ext}({\sf com},{\sf tran}_1,\ldots,{\sf tran}_L)$**
  - `reconstruct()` calls `verify_openings()` on every supplied transcript.
  - It unions openings by cell index and requires at least $\lceil k/c\rceil$ distinct cells.
  - It expands the accepted cells into arbitrary indexed RS evaluations and constructs one shared `ErasureDecoder` for their erasure pattern.
  - `ErasureDecoder::new()` constructs the erasure locator polynomial $Z(X)$ with an FFT subproduct tree, evaluates $Z$ over the size-$m$ domain, and prepares the reversed-polynomial inverse used for exact division.
  - For each row, `ErasureDecoder::reconstruct_blob()` forms the complete evaluation vector of $N(X)=f(X)Z(X)$, applies a size-$m$ IFFT, divides $N(X)$ by $Z(X)$ using the prepared Newton inverse, and applies a size-$k$ FFT to recover the systematic even-position values.
  - The locator preparation is shared by every row. It costs $O(M(m)\log m)$ for arbitrary erasures, where $M(m)$ is polynomial-multiplication cost; with the current radix-2 FFT multiplier this is $O(m\log^2m)$. Each row then costs $O(m\log m)$.

## Current Demo Instantiation

- **Blob definition:** `Blob = Vec<F>`, where `F` is the KoalaBear base-field type. One blob is exactly $k$ canonical KoalaBear elements, and `Data = Vec<Blob>` contains $n$ blobs. The 128 KiB profiles use $k=32768$, which occupies 128 KiB when each canonical field element is serialized in four bytes. This is a field-native format, not yet an injective packing of an arbitrary 128 KiB byte string.

- **Fields used by the demo:**
  - **KoalaBear base field $\mathbb{F}$:** represented by `lean_vm::F`. Blob symbols, RS coefficients and evaluations, FFT arithmetic, Poseidon inputs and digests, Merkle nodes, VM memory, and the five coordinates used to serialize extension elements all live in $\mathbb{F}$.
  - **Quintic extension field $\mathbb{E}=\mathbb{F}[X]/(f(X))$:** represented by `lean_vm::EF`. It is used for the Fiat–Shamir challenge $p$, the derived point $q=p/\omega$, the coefficients $L_j$, and the RS membership inner product. Since $[\mathbb{E}:\mathbb{F}]=5$, one extension element is represented by five KoalaBear coordinates.
  - **WHIR/STARK arithmetic:** LeanVM's execution proof is ultimately arithmetized over the same KoalaBear base field, while extension-field values used by the proof system and `dot_product_be()` are represented through their five base-field coordinates. The demo does not introduce a third application-level RS field.

- **RS encoding and systematic data:** the evaluation domain is
  $\mathsf{U}=\{1,\omega,\ldots,\omega^{m-1}\}$ over KoalaBear. The current special-barycentric implementation requires $m=2k$. `encode_blob()` interprets the input blob as evaluations on the size-$k$ subgroup generated by $\omega^2$, applies a size-$k$ IFFT, zero-pads the coefficient vector, and applies a size-$m$ FFT. Therefore the original blob values appear at the even codeword positions:
  $$
  w_{i\cdot(m/k)}=w_{2i}={\sf blob}_i.
  $$

- **Cell definition:** one row is divided into $\ell=m/c$ cells. Cell $W_{i,j}$ contains the $c$ consecutive values
  $$
  W_{i,j}=(w_{i,jc},\ldots,w_{i,(j+1)c-1}).
  $$
  A queried cell column contains the cells with the same index from all $n$ rows. The reconstruction threshold is $t=\lceil k/c\rceil$ distinct cell columns because they contain at least $k$ codeword evaluations per row.

- **Arbitrary-cell reconstruction:** reconstruction accepts any verified set of at least $t$ distinct cells; the selected cells do not need to contain the systematic even positions or form an FFT subgroup. Let $S\subseteq[0,m-1]$ be the available symbol indices and let
  $$
  Z(X)=\prod_{j\notin S}(X-\omega^j)
  $$
  be the erasure locator. For each row polynomial $f(X)$, the decoder constructs the complete size-$m$ evaluation vector of
  $$
  N(X)=f(X)Z(X).
  $$
  At every available position $j\in S$, it sets $N(\omega^j)=w_jZ(\omega^j)$; at every erased position, $Z(\omega^j)=0$, so $N(\omega^j)=0$ is known without knowing $w_j$. A size-$m$ IFFT recovers the coefficients of $N$, fast exact division by $Z$ recovers the coefficients of $f$, and a size-$k$ FFT over the subgroup generated by $\omega^2$ returns
  $$
  \bigl(f(1),f(\omega^2),\ldots,f(\omega^{2(k-1)})\bigr),
  $$
  which is exactly the original systematic blob. `ErasureDecoder::new()` prepares $Z$, its domain evaluations, and the Newton division inverse once for the shared cell pattern; `ErasureDecoder::reconstruct_blob()` reuses them for every row.

- **Row hash:** `row_hash()` gathers the $k$ systematic positions $w_{i,2r}$ and computes
  $$
  h_i=\mathsf{PoseidonHash}(w_{i,0},w_{i,2},\ldots,w_{i,2k-2}).
  $$
  The output $h_i$ is an eight-KoalaBear-element digest.

- **Column hash and Merkle tree:** `column_hash()` computes
  $$
  d_j=\mathsf{PoseidonHash}(W_{1,j}\parallel\cdots\parallel W_{n,j})
  $$
  over $n\cdot c$ KoalaBear elements using the Poseidon width-16, rate-8 sponge. These $\ell$ digests are the leaves of a complete binary tree; every internal node is `poseidon16_compress_pair(left, right)`, and the final digest is the public ${\sf root}$.

- **LeanVM public statement and witness:** on the prover side, `PreparedStatement` contains the public `Commitment`, the derived RS check vector $L$, and the compiled bytecode. The prover sends the public `Commitment` and proof, but does not send $L$ as a trusted verifier input. The verifier independently reconstructs an equivalent `PreparedStatement`. In both instances, the row hashes, ${\sf root}$, and derived $L$ are stored in a read-only public-data segment bound by both the bytecode hash and the public-memory polynomial. The private `ExecutionWitness` contains only the flattened $n\times m$ codeword matrix.

- **LeanVM proof relation:** the zkDSL `main()` proves exactly three classes of constraints:
  1. for every row, recompute the systematic Poseidon hash and equate it to the public $h_i$;
  2. recompute every column hash and the complete binary Poseidon tree, then equate the result to the public ${\sf root}$;
  3. for every row, execute `dot_product_be(w_i, L)` and constrain all five quintic-extension coordinates of the result to zero:
     $$
     \langle w_i,L\rangle=\sum_{j=0}^{m-1}w_{i,j}L_j=0\in\mathbb{E}.
     $$

- **Fiat–Shamir and $L$ computation outside the proof:** `fiat_shamir_digest()` hashes the RS domain separator, encoded profile, all row hashes, and the Merkle ${\sf root}$. The first five digest coordinates define $p\in\mathbb{E}$, and $q=p/\omega$. For $x_r=(\omega^2)^r$, the implementation computes
  $$
  L_{2r}=\frac{p^k-1}{k}\cdot\frac{x_r}{p-x_r},
  \qquad
  L_{2r+1}=-\frac{q^k-1}{k}\cdot\frac{x_r}{q-x_r}.
  $$
  Montgomery batch inversion replaces the $2k$ individual extension-field inversions with one inversion and $O(k)$ multiplications. For nonzero denominators $a_1,\ldots,a_N$, it computes prefix products $P_i=\prod_{j=1}^{i}a_j$, inverts only $P_N$, and walks backward using
  $$
  a_i^{-1}=P_{i-1}\cdot P_N^{-1}\cdot\prod_{j=i+1}^{N}a_j,
  $$
  updating the suffix inverse at each step. Thus every $a_i^{-1}$ is recovered with multiplications after one inversion. The resulting $L$ is generated once during each party's statement preparation and reused throughout that party's proof or verification workflow.
  The verifier is required to call `prepare_statement(commitment)` independently. Consequently, it recomputes the Fiat–Shamir digest, $p$, $q$, all denominator inverses, and every $L_j$ from the public profile, row hashes, and ${\sf root}$ before LeanVM proof verification. A prover-supplied incorrect challenge or $L$ therefore produces bytecode that differs from the verifier's bytecode and cannot verify.

- **RS membership computation inside the proof:** for each row, LeanVM's extension-field precompile computes
  $$
  \sum_{j=0}^{m-1}w_{i,j}L_j.
  $$
  Since $L_j$ has five KoalaBear coordinates, `dot_product_be()` returns one quintic-extension element. `assert_ext_zero()` constrains all five coordinates to zero. No Fiat–Shamir hashing, challenge derivation, denominator inversion, or $L$ construction occurs inside the proof.

## Benchmark Parameter Sets

| Dataset | Base field $\mathbb{F}$ | Challenge field $\mathbb{E}$ | Hash | $\rho$ | Membership | WHIR $\log(1/{\rm rate})$ | $n$ | $m$ | $k$ | $c$ | $\ell=m/c$ | $t=k/c$ | Input size | Encoded size |
| --- | --- | --- | --- | ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `tiny` | KoalaBear | Quintic extension | Poseidon-16/8 | $1/2$ | Special barycentric | 1 | 2 | 16 | 8 | 8 | 2 | 1 | 64 B | 128 B |
| `medium` | KoalaBear | Quintic extension | Poseidon-16/8 | $1/2$ | Special barycentric | 1 | 8 | 256 | 128 | 8 | 32 | 16 | 4 KiB | 8 KiB |
| `large` | KoalaBear | Quintic extension | Poseidon-16/8 | $1/2$ | Special barycentric | 1 | 16 | 1,024 | 512 | 8 | 128 | 64 | 32 KiB | 64 KiB |
| `stress` | KoalaBear | Quintic extension | Poseidon-16/8 | $1/2$ | Special barycentric | 1 | 32 | 4,096 | 2,048 | 8 | 512 | 256 | 256 KiB | 512 KiB |
| `blob-128k-1` | KoalaBear | Quintic extension | Poseidon-16/8 | $1/2$ | Special barycentric | 1 | 1 | 65,536 | 32,768 | 64 | 1,024 | 512 | 128 KiB | 256 KiB |
| `blob-128k-4` | KoalaBear | Quintic extension | Poseidon-16/8 | $1/2$ | Special barycentric | 1 | 4 | 65,536 | 32,768 | 64 | 1,024 | 512 | 512 KiB | 1 MiB |

Sizes use the four-byte canonical serialization of one KoalaBear element.

## Benchmark Results

All six proofs were accepted and all six profiles completed reconstruction from an independently sampled arbitrary set of exactly $t$ cells. LeanVM currently configures WHIR for $124$-bit security, so sampling uses the minimum number of distinct cells satisfying the matching worst-case availability bound:
$$
\Pr[\mathsf{miss}]
=\frac{\binom{t-1}{q}}{\binom{\ell}{q}}
\le 2^{-124},
$$
where an unreconstructable encoding has at most $t-1$ available cell columns. For the two smallest domains, $124$-bit soundness requires $q=t$, making the bound zero. The larger profiles achieve the target with $q<t$. Raising only the sampling target above $124$ bits would not raise the end-to-end demo security while WHIR remains configured for $124$ bits.

| Dataset | Bytecode instructions | Read-only elements | Opened cells $q$ | Commitment size (KB) | Proof size (KB) | Sample size (KB) | Encode + commit | Prover preprocess | LeanVM prove | Verifier rebuild + LeanVM verify | Verify openings | Reconstruct | Result |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | --- |
| `tiny` | 512 | 104 | 1 | 0.094 | 187.723 | 0.098 | 0.000s | 0.005s | 0.100s | 0.028s | 0.000s | 0.000s | Correct |
| `medium` | 512 | 1,352 | 16 | 0.281 | 260.516 | 6.562 | 0.001s | 0.006s | 0.200s | 0.035s | 0.000s | 0.000s | Correct |
| `large` | 1,024 | 5,256 | 63 | 0.531 | 308.270 | 45.527 | 0.006s | 0.015s | 0.915s | 0.045s | 0.002s | 0.003s | Correct |
| `stress` | 1,024 | 20,744 | 105 | 1.031 | 376.602 | 134.941 | 0.043s | 0.016s | 6.812s | 0.055s | 0.006s | 0.025s | Correct |
| `blob-128k-1` | 1,024 | 327,696 | 114 | 0.062 | 357.512 | 64.570 | 0.023s | 0.077s | 3.600s | 0.130s | 0.003s | 0.067s | Correct |
| `blob-128k-4` | 1,024 | 327,720 | 114 | 0.156 | 398.496 | 150.070 | 0.097s | 0.079s | 17.400s | 0.209s | 0.008s | 0.143s | Correct |

Size columns use $1\,\mathrm{KB}=1024$ bytes. The benchmark columns measure the following:

- **Bytecode instructions:** the number of LeanVM instructions in the compiled, profile-specific zkDSL program after padding to the bytecode domain. Public row hashes, ${\sf root}$, and $L$ are not expanded into assignment instructions, so increasing $m$ mainly enlarges the read-only segment rather than the instruction count.

- **Read-only elements:** the number of KoalaBear elements stored in LeanVM's statement-bound read-only segment. It contains all $n$ row-hash digests, the Merkle ${\sf root}$, and the $m$ extension-field coefficients of $L$, each represented by five base-field coordinates:
  $$
  8n+8+5m.
  $$

- **Opened cells $q$:** the minimum number of distinct random cell columns needed to make the worst-case availability false-accept probability at most $2^{-124}$, matching LeanVM's current WHIR setting. This is a DAS sampling count, not the reconstruction threshold $t$. Each opening contains the corresponding cell from every row and a Merkle authentication path.

- **Commitment size:** the size in KB of the canonical four-byte field serialization of the construction commitment $\{h_i\}_{i=1}^{n}$ and ${\sf root}$:
  $$
  (n+1)\cdot 8\cdot 4\ \text{bytes}.
  $$
  The profile ${\sf pp}$ is assumed to be agreed public metadata and is not counted again.

- **Proof size:** `proof_size_fe()` reported by the LeanVM/WHIR proof, multiplied by four bytes per canonically serialized KoalaBear element and converted to KB. This measures the cryptographic execution proof only; it excludes the commitment and sampled cell openings.

- **Sample size:** the canonical wire size in KB of the benchmark `Transcript`. For each of the $q$ openings it counts one four-byte cell index, $n\cdot c$ four-byte field elements, and $\log_2\ell$ sibling digests of eight field elements:
  $$
  q\left(4+4nc+32\log_2\ell\right)\ \text{bytes}.
  $$

- **Encode + commit:** host time for `encode_and_commit()`. It includes RS encoding of all $n$ blobs, computation of every row hash, computation of all column hashes, and construction of the complete Poseidon Merkle tree. It does not include Fiat–Shamir, $L$ generation, bytecode compilation, or LeanVM proving.

- **Prover preprocess:** host time for the prover's `prepare_statement()`. Starting from the public `Commitment`, it computes the Fiat–Shamir digest, derives $p$ and $q$, constructs $L$ using batch inversion, compiles the compact profile-specific zkDSL program, and attaches the row hashes, ${\sf root}$, and $L$ as read-only public data. It does not execute or prove the LeanVM program.

- **LeanVM prove:** time spent in `prove_codewords()` after encoding, commitment construction, Fiat–Shamir, $L$ generation, and bytecode compilation have finished. It includes witness packaging, execution of the zkDSL program, execution-trace construction, and generation of the LeanVM/WHIR proof for the row-hash, Merkle-root, and RS inner-product relations.

- **Verifier rebuild + LeanVM verify:** total verifier time for `verify_execution_proof()`. The verifier first runs its own `prepare_statement(commitment)`, independently recomputing Fiat–Shamir, $p$, $q$, all $L_j$, the read-only segment, and the expected bytecode. It then invokes LeanVM `verify_execution()` on the proof. This column therefore includes both public $L$ validation by reconstruction and cryptographic proof verification, but excludes Merkle opening verification.

- **Verify openings:** host time for `verify_openings()`. It recomputes the Poseidon column digest for every opened cell column and verifies every Merkle authentication path against the public ${\sf root}$. It does not include LeanVM proof verification or RS reconstruction.

- **Reconstruct:** total time for `reconstruct()`, including re-verification of the $t$ reconstruction openings, one shared arbitrary-erasure locator preparation, and recovery of all $n$ rows through numerator IFFT, fast exact division, and systematic-domain FFT.

- **Result:** whether the reconstructed blobs exactly equal the original input blobs.

## Implemented Engineering Optimizations

- The prover's `PreparedStatement` caches the commitment, its single generated $L$ vector, and compiled bytecode for proving.
- The verifier accepts only the public `Commitment` and proof, then independently recomputes Fiat–Shamir, $p$, $q$, $L$, and the bound bytecode before proof verification.
- LeanVM has a read-only public-data segment for row hashes, ${\sf root}$, and $L$. It is immutable, included in the bytecode hash, and constrained by the public-memory polynomial.
- Public constants are no longer expanded into hundreds of thousands of VM assignment instructions.
- Within each party, $L$ is computed once and reused instead of being regenerated per row. The verifier's copy is independently derived rather than received from the prover.
- Availability sampling derives distinct Poseidon-based indices and computes the minimum count for a $124$-bit worst-case hypergeometric bound matching LeanVM instead of opening the reconstruction threshold by default.
- Montgomery batch inversion reduces $L$ generation from $2k$ extension-field inversions to one inversion plus linear-many multiplications.
- Poseidon sponge absorption uses runtime loops, keeping bytecode size nearly constant as $k$ and $m$ grow.
- RS encoding uses radix-2 IFFT/FFT rather than quadratic Lagrange evaluation.
- Arbitrary-cell reconstruction replaces quadratic barycentric interpolation with a shared FFT subproduct-tree erasure locator, Newton exact division, and FFT recovery. Locator preparation is reused across every row.
- RS membership inside LeanVM uses the optimized `dot_product_be` extension-field precompile.
- Benchmark timing is separated into encoding/commitment, prover preprocessing, proving, verifier statement reconstruction plus proof verification, and opening verification. Commitment, proof, and sample sizes are reported separately.

## Running Commands

Run correctness tests:

```bash
cargo test --release -p pq_das -- --nocapture
```

Run the six benchmark datasets:

```bash
cargo run --release -p pq_das -- --profile tiny
cargo run --release -p pq_das -- --profile medium
cargo run --release -p pq_das -- --profile large
cargo run --release -p pq_das -- --profile stress
cargo run --release -p pq_das -- --profile blob-128k-1
cargo run --release -p pq_das -- --profile blob-128k-4
```

Build once and run all six benchmarks:

```bash
cargo build --release -p pq_das && \
  for p in tiny medium large stress blob-128k-1 blob-128k-4; do
    target/release/pq_das --profile "$p"
  done
```

Run a custom half-rate profile:

```bash
cargo run --release -p pq_das -- \
  --profile custom --n 4 --m 128 --k 64 --c 8
```

Override the WHIR inverse-rate exponent:

```bash
cargo run --release -p pq_das -- \
  --profile medium --whir-log-inv-rate 2
```
