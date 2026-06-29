# PQ-DAS Optimization Checklist

## A. Profiling and Cost Breakdown

- [ ] **A1. Add detailed LeanVM prover profiling:** report actual and padded rows for every LeanVM table.
- [ ] **A2. Add stage-level prover timing:** separately measure bytecode execution, trace generation, memory access counting, logup, AIR sumcheck, WHIR, and grinding.
- [ ] **A3. Enable LeanVM VM profiling and tracing:** expose instruction, memory, Poseidon, and extension-operation statistics.
- [ ] **A4. Add relation-isolation benchmarks:** benchmark row hashing, column hashing plus Merkle construction, and RS membership independently.

## B. LeanVM Proof Optimization

- [ ] **B1. Implement a PQ-DAS-specific LeanVM precompile/AIR:** directly constrain row hashes, the column Merkle root, and RS membership.
- [ ] **B2. Add a batched Poseidon sponge precompile:** process all row hashes or all column hashes in batches.
- [ ] **B3. Add a strided Poseidon input mode:** hash systematic row symbols directly without copying them into a temporary array.
- [ ] **B4. Add a gathered Poseidon input mode:** hash column cells directly across rows without constructing `column_data`.
- [ ] **B5. Fuse column hashing with Merkle construction:** stream leaf digests into a Merkle accumulator without storing the full tree in VM memory.
- [ ] **B6. Add a batched matrix-vector membership precompile:** compute all $\langle w_i,L\rangle$ checks while reusing the same public $L$.
- [ ] **B7. Add a structured fixed-column segment for $L$:** remove the $5m$ coordinates of $L$ from generic VM memory while keeping verifier-side derivation mandatory.
- [ ] **B8. Store codewords in dedicated AIR trace columns:** avoid placing the complete $n\times m$ codeword matrix in generic VM memory.
- [ ] **B9. Reduce generic VM memory traffic:** eliminate unnecessary intermediate arrays, reads, writes, and memory-bus lookups in the guest.

## C. Parallelism and Low-Level Prover Optimization

- [ ] **C1. Parallelize row-hash guest loops.**
- [ ] **C2. Parallelize column-hash guest loops.**
- [ ] **C3. Parallelize each independent Merkle-tree level.**
- [ ] **C4. Parallelize RS membership checks across rows.**
- [ ] **C5. Parallelize prover memory access-count construction:** use thread-local accumulators followed by reduction.
- [ ] **C6. Parallelize bytecode access-count construction.**
- [ ] **C7. Parallelize independent trace-table processing.**
- [ ] **C8. Enable native CPU optimization:** benchmark builds using `RUSTFLAGS="-C target-cpu=native"`.
- [ ] **C9. Verify SIMD utilization:** confirm AVX2 or AVX-512 Poseidon and packed KoalaBear arithmetic are active.
- [ ] **C10. Tune LeanVM worker-thread count for the benchmark machine.**
- [ ] **C11. Add NUMA-aware trace allocation and worker placement.**
- [ ] **C12. Reuse prover scratch buffers and avoid repeated zero-initialization.**
- [ ] **C13. Evaluate GPU acceleration for WHIR FFTs, Poseidon, Merkle commitments, and sumcheck.**

## D. WHIR Configuration Optimization

- [ ] **D1. Benchmark `whir_log_inv_rate` values 1 through 4:** compare prover time, verifier time, proof size, and memory.
- [ ] **D2. Tune the initial WHIR folding factor while preserving at least 124-bit security.**
- [ ] **D3. Tune the subsequent WHIR folding factor while preserving at least 124-bit security.**
- [ ] **D4. Tune the RS-domain initial reduction factor.**
- [ ] **D5. Tune the grinding-bit and query-count allocation while preserving total soundness.**
- [ ] **D6. Tune `MAX_NUM_VARIABLES_TO_SEND_COEFFS`.**

## E. Host and Engineering Optimization

- [ ] **E1. Cache profile-specific compiled bytecode templates.**
- [ ] **E2. Bind commitment-specific row hashes, root, and $L$ without recompiling the guest.**
- [ ] **E3. Cache FFT roots, twiddle factors, domains, and reusable FFT plans.**
- [ ] **E4. Cache reconstruction locator data when multiple rows use the same erasure pattern.**
- [ ] **E5. Implement a zero-copy contiguous codeword representation.**
- [ ] **E6. Remove the witness flattening copy before LeanVM execution.**
- [ ] **E7. Parallelize native RS encoding across blobs.**
- [ ] **E8. Parallelize native row and column commitment hashing.**
- [ ] **E9. Parallelize reconstruction across rows.**
- [ ] **E10. Add reusable benchmark automation and machine-configuration reporting.**

## F. Protocol-Level Optimization Candidates

- [ ] **F1. Evaluate row-sharded parallel proofs:** measure latency, total proof size, and verifier cost.
- [ ] **F2. Evaluate recursive aggregation of row-sharded proofs.**
- [ ] **F3. Benchmark alternative cell sizes $c$:** measure Merkle cost, sample size, sampling count, and network granularity.
- [ ] **F4. Benchmark alternative RS code rates $\rho=k/m$:** recompute reconstruction and availability soundness for every rate.
- [ ] **F5. Design a V2 commitment that avoids hashing systematic symbols independently in both row and column commitments.**

## Security Constraints

- [ ] **S1. Keep LeanVM and DAS sampling soundness at or above the configured security target.**
- [ ] **S2. Keep verifier-side Fiat-Shamir challenge and $L$ reconstruction mandatory.**
- [ ] **S3. Keep row hashes, column commitment root, and RS membership inside the proved relation.**
- [ ] **S4. Do not reduce the extension degree, digest length, or proof-system security solely for performance.**
