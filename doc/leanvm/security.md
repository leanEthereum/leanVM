# Security ledger

`leanvm::security::Ledger::for_program` derives accounting from a validated program, the announced table heights and a rate, including an upper bound on the number of point and ring-switched opening claims. It allocates no witness and changes no prover messages or verifier parameters. A report is conditional accounting, not a security certification.

The intended relation is existence of a valid RV64IM execution on private advice, returning the four public output words. The current verifier binds a terminal halt address, `a7 = 93` and the output; binding termination to an actual ECALL is tracked separately in [PR #327](https://github.com/leanEthereum/leanVM/pull/327). Numerical bounds cannot repair that semantic gap. Proofs are not zero knowledge; no knowledge-extraction or post-quantum theorem is claimed.

## Binding order

The program digest and output seed the BLAKE2s transcript. Table heights, rate and final clock enter the scalar stream, then the witness commitment enters before challenges. Received scalars bind automatically; authenticated Merkle hints have no second absorption.

| Reduction | Bound before challenge | Degree accounting | Terminal obligation |
| --- | --- | --- | --- |
| Bus | Witness commitment before fingerprints; roots and GKR messages before their respective challenges | At side dimension `b`, `5*2^b + 8*(b+1)^2` conservatively covers fingerprints and GKR | Framework column claims and table bus forms |
| Tables | Bus framework evaluations before batching; each round polynomial before its challenge | `C+2` batching degree, `tau` residual detection, `3*tau` cubic rounds | Every table column evaluation enters the shared opening |
| Each class | Skip message before skip challenge; round messages before fold challenges; final A/B claims before lincheck batching | Annex C's conservative `5*k + 4*n + 93` degree sum, including constant pin | The packed Boolean witness slices enter ring switching |
| Ring switch | All slice vectors before the six map challenges | Composed Frobenius degree `2^31+2^15+2^7+2^3+2+1` | A weight and target for the same committed stack |
| Shared opening | All claims before the power-batch challenge | `J-1` for the actual total claim count `J` | WHIR authenticates the combined weight and target |
| WHIR | Each commitment and round polynomial before its challenge | Johnson list size multiplies algebraic degrees; folding includes proximity-gap and `2*L/2^192` terms | Merkle paths and the terminal residual |

Here `C` is the total number of table identities, `tau` the largest table log height, `k` a class circuit log size, and `n` its table log height. Every class is charged, even a class padded to its minimum batch. The seven fixed friendly equality coordinates are not random challenges: their rank argument applies to Boolean residuals, not arbitrary extension-field residuals.

## Numeric terms and assumptions

The base field has `2^64` elements; challenges have `2^192`. Existing computational tests check both defining polynomials' irreducibility, the complete prime factorization of `2^64-1` and the timestamp generator's full order. Wire coordinates follow the implemented polynomial basis, not an interchangeable binary-tower basis. A real memory access's timestamp gap is strictly positive and below `2^32`; layout caps bound read-flush counts below the generator order.

WHIR accepts committed dimensions 15 through 28 and inverse-rate logs 1 through 4. The executable PCS sweep covers all 56 pairs. `security_terms` reports the Johnson list bound, actual batching degree, algebraic, binding and proximity-gap terms, raw query rejection and its grinding budget. The ledger multiplies the outer algebraic degree sum by the L0 list size, because a commitment is initially list binding. It does not treat every commitment as a unique witness.

For example, degree 3 over a list of size `L` contributes at most `3*L/2^192`, conditional on the applicable list-binding and reduction lemmas. Two bad events at one folding challenge add their probabilities. Checking each against `2^-128` does not establish that their sum is at most `2^-128`; the report exposes the combined fold term rather than calling the whole system “128-bit secure.”

Query grinding uses 17 bits after the level's commitment and before query sampling. The nonce is three little-endian 64-bit limbs on the scalar channel. The honest prover searches the first limb; the verifier accepts the full 192-bit encoding. Domain tags distinguish observations, squeezes, the grinding base and nonce absorption. A valid nonce is absorbed before later challenges. These bits apply to query search, not unrelated algebraic challenges.

## Obligations before a composed security claim

- Prove a joint auxiliary argument for the bus, reused GKR point and heterogeneous table sumcheck, including each authenticated terminal claim and non-wrapping counters.

- Prove that the L0 candidate list has base-field coefficients, so unpacking gives Boolean residuals for the friendly-coordinate argument; justify the rectangular ring switch and shared map over every class jointly. Existing rank and map-support tests are regression checks, not replacements for these proofs.

- Establish a round-by-round soundness definition and composition theorem for the complete protocol. Separate that bound from an interactive union bound. The numeric reports inherit the PCS annex's list and proximity-gap lemmas; those assumptions require independent review before any parameter relaxation.

- State the classical random-oracle adversarial query budget `Q` and hash-binding term. A reduction of the form `Q*epsilon_RBR + epsilon_hash` loses `log2(Q)` bits relative to a per-query error; this formula is conditional on the selected theorem, not established here for the transcript chain. BLAKE2s has a 256-bit output, so its generic collision scale is 128 bits. Field width alone is not a hash or composed security level.

The distinction between numerical bounds and soundness notions follows [On Round-By-Round Soundness and State Restoration Attacks](https://eprint.iacr.org/2019/1261) and [On Soundness Notions for Interactive Oracle Proofs](https://eprint.iacr.org/2023/1256). [Polylogarithmic Proofs for Multilinears over Binary Towers](https://eprint.iacr.org/2024/504) motivates ring switching; the implemented rectangular composition still needs its own justification.
