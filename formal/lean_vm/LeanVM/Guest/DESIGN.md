# Proving the aggregation guest

The goal: for the deployed guest bytecode `guest : Program`, soundness (a valid execution on the public input `statementDigest seed s` gives `seed'`, `s'` with the same digest, `s'.defer` shaped and `NodeRel seed' s'`) and completeness (`NodeRel` within the deployed limits gives a valid execution), without trusting the zkDSL compiler. [TRIAGE.md](TRIAGE.md) is the function-by-function map of the guest.

## The chain

```text
bytecode  ⇐ B2 ⇒  core IR of the guest  =  expand (source AST)  ⇐ B1 ⇒  NodeRel
```

* **Source AST.** `crates/rec_aggregation/guests/lean_ethereum.py` after placeholder substitution, as data (`Guest/Data/Source.lean`, exported by the Rust parser). It is not trusted: a parser bug makes B1 or B2 fail, never a false theorem.
* **Expansion** (`Guest/Expand.lean`): the zkDSL front end, written in Lean: `Const` specialization, `unroll`, `@inline`, compile-time folding in its two regimes, virtual bindings, `StackBuf` and slices, `mul_range` lifted to loop functions. It turns a source function and its `Const` arguments into a core IR function. The source semantics is defined as the core semantics of the expansion, and the structural lemmas B1 needs (an `unroll` is a conjunction over its index, a call is its callee's relation) are theorems about `expand`.
* **Core IR** (`Guest/Core.lean`): straight-line SSA statements over field values (sums, products, constants, heap reads and stores as equations on one global memory, hints as free values, `assert ==`, `!=`, range checks, `assert_in_k`, BLAKE2s compressions), calls, forward branches, `match`, loop functions. Its semantics is relational: a function's meaning is a predicate on the memory and its argument and return values. `HeapBuf` is an existential g-power and fresh cells carry no distinctness, so soundness never relies on the allocator.
* **The mirror** of the goal is `expand` applied to the source AST: executable (an interpreter runs it on recorded hints for the differential check), structured as the guest, never out of sync with it.

## B2: bytecode and core IR

The bytecode is data too (`Guest/Data/Bytecode*.lean`, one definition per compiled function, operands as `Nat` offsets so that no `g^n` is ever evaluated), exported by Rust with an untrusted certificate per compiled function: its source function and `Const` arguments (or loop), entry pc, frame size, and the frame cell of each core IR value. A Rust test regenerates all of it and fails when it is stale, as for `NodeVectors.lean`.

* **Program logic** (`Guest/Logic.lean`): `FunSpec f P Q`, in continuation form on `run`: from `f`'s entry with frame `fp` and a run that halts, the run returns to the caller's `(pc, fp)` stored at `fp[0]`, `fp[1]`, with `Q` holding of the memory. All functions are proved together by strong induction on the remaining steps; a loop's tail call is its own spec at the next frame.
* **Symbolic executor** (`Guest/Exec.lean`): walks one compiled function's code once and cuts it into segments at the joins of its forward control flow; each segment's items are atoms (one per executed instruction, plus the meanings of the gadgets: range check, `!=`, copy as `MUL·1`, booleanity, `assert ==`) and forward branches, and its exits are classified (local jump, return, call or fused dispatch into a callee frame holding its return registers, and any other jump by the registers it names: tail call, table dispatch, halt). Frame knowledge (constants that are powers of `g`, the self frame pointer, a loop's next frame) is an environment, intersected at joins and checked by `Result.linked`, never trusted. Inputs (`Facts`): the entry environment, the powers of `g` the constants name (checked by the kernel), dispatch arms; a selector's bound is not an input, the dispatch exit naming the cell its target is read into. Sound (`exec_sound`, step accounting for `funSpec_induction`) and complete (`exec_complete`) against the program logic; the two largest functions are run in windows (`execWin`, `Result.linkedExt`).
* **Checker** (`Guest/Check.lean`): with the certificate's cell map, every core IR constraint is implied by an atom (soundness), and every atom holds of the honest memory built from the core IR values (completeness). Evaluated by the kernel per compiled function (`decide +kernel`), over structural recursion, `Nat` keys, no field arithmetic.
* **Control-flow integrity.** A `match` dispatch reads its target from the jump table at the selector, so the selector must be in range before it on the path; the jump table's slots are the `SET`s of `__jump_tables`, executed first by every run. 111 of the 207 dispatch sites range-check their selector in the same function. The others are bounded elsewhere, and their bound enters the function's spec: as a precondition its callers establish (`da_list_digest`), as the postcondition of a callee run before the dispatch (`da_verify`, `da_verify_column`, through `da_row_shape`), or, for the 92 column selectors of `check_opening_terminal`, as a precondition carrying the semantic fact that every column's `κ` is below 29, which B1's lemmas about `certify_placement`, `log2_ceil_in_the_exponent` and the candidate selection establish. So B2's soundness for those sites rests on B1 facts proved about code run earlier.
* **Completeness** additionally builds the memory: frames and heap regions by a bump allocator, as the Rust runner does, within `2^32` words.

## B1: core IR and the specification

Per source function, a lemma relating its relation to the Spec definition it computes ([TRIAGE.md](TRIAGE.md): 37 by a representation lemma, 39 guest-specific). The honest hint generator is a Lean function of a `NodeRel` witness, mirroring the Rust producers; completeness assumes the deployed limits of TRIAGE.md's findings.

## Workstreams

1. Dispatch range checks in the guest, with the compiled-bytecode test (on `main`).
2. Exporters (Rust): bytecode, source AST, certificates; Lean data representation and the bridge to `Program`.
3. Core IR, semantics, source AST, `expand`.
4. Program logic, symbolic executor, checker, their proofs.
5. B1, by function, from the leaves (`pack64x2`, Fiat-Shamir, sumcheck) up to `main`.
6. Honest hint generator, completeness, differential check.
