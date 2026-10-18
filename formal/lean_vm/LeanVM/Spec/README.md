# The specification

What the project proves, in the files a reviewer reads. They import nothing else from the project (CI checks it); the rest is proof.

Read in this order:

1. [`Field.lean`](Field.lean): the fields `K = GF(2^64)` and `E = GF(2^192)`, and the generator `g`.
2. [`Blake2s.lean`](Blake2s.lean): the BLAKE2s compression function and BLAKE2s-256 of bytes.
3. [`Isa.lean`](Isa.lean): leanISA (programs, memory, one step, valid executions, the instructions of each opcode an execution executes) and the encoding of an instruction.
4. [`Verifier.lean`](Verifier.lean): the verifier, transcribed from leanVM's Python verifier, with the WHIR and Flock constants it reads and the Fiat-Shamir transcript it runs on; and the deferring verifier an aggregate runs on its children, which takes the values of the fixed polynomials from claims instead of computing them. The prover announces each table's row count, the table's height being the least power of two holding them; the bus discounts the rows past the count (padding rows) through a public term (`paddingWeight`, `Table.padding`).
5. [`Statement.lean`](Statement.lean): the random-oracle experiment and the two statements, `KnowledgeSoundness` and `Completeness`.

The aggregation guest (stated, not yet proved):

6. The two signature schemes, leanXMSS and leanSPHINCS, imported from the projects that prove their security: [`formal/lean_xmss/LeanXmss/Scheme.lean`](../../../lean_xmss/LeanXmss/Scheme.lean) and [`formal/lean_sphincs/Sphincs/Scheme.lean`](../../../lean_sphincs/Sphincs/Scheme.lean).
7. [`Da.lean`](Da.lean): the claim on a DA root, in terms of LeanDA as [`formal/lean_da/LeanDa/Scheme.lean`](../../../lean_da/LeanDa/Scheme.lean) defines it (the deployed commitment, the membership vector and its digest), on this project's BLAKE2s.
8. [`Node.lean`](Node.lean): a node's statement and its digest, the batching of deferred claims, `NodeSpec` (what a node establishes) and the outer verifier.

[`Fast/`](Fast/) needs no review: it holds `@[csimp]` theorems, each proved, that make the compiled field arithmetic, BLAKE2s, LeanDA's membership vector and the signature schemes' verifiers fast. They change no definition.

The proofs are `LeanVM.knowledgeSoundness_holds` and `LeanVM.completeness_holds` in [`LeanVM/Protocol/LeanVM.lean`](../Protocol/LeanVM.lean).
