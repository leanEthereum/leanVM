# Decompiling the RISC-V verifier into Lean: how cheap is it to re-prove after a change?

Experimental draft, 2026-11-20, `formal/rv64mc`, compared with draft PR #738. Costs are in CPU-seconds (CPU-s); wall times come from a shared 32-core host under load 15 to 100 and are indicative only. "The kernel" is Lean's small trusted proof checker; "standard axioms" are Lean's three (`propext`, `Classical.choice`, `Quot.sound`); estimates are marked as such.

## 1. Summary

- **Iteration.** Across 13 measured changes to the Rust verifier, our pipeline re-checked everything in 300 to 3,230 CPU-s (4 to 13 minutes wall); our cold build is 4,333 CPU-s (1.2 CPU-hours). A change to a proved function's code never reached its callers, which import its contract, not its code: only its own proof broke, and the compiler set the repair cost, minutes when it reallocated registers, an estimated 1 to 2 hours when it turned unrolled code into a loop (left unrepaired, as was one 20-minute attempt, C5).
- **Against #738.** After the same one-token change, #738's rebuild alone cost 3.71 CPU-hours (57 minutes wall), before any repair, and left it broken: 28 modules failed and 707 more (701 proof files, 194,552 lines) went unchecked because they import a failed one, the final `soundness` theorem among them. The three failures sampled need only address renaming, but 228 of its 823 proof files (76,569 lines, a third) name a shifted address, no renaming script exists, and the slowest failing files take about 30 minutes per attempt before the kernel rejects them. On C1 itself: 2,751 CPU-s and a 3-minute repair for us, against 13,356 CPU-s and a tree that no longer builds. In a complete tree we estimate an edit to a widely imported mirror or contract at 1.5 to 3+ CPU-hours for us, comparable to #738's rebuild before repair; code-only changes would not grow.
- **Proved, standard axioms only:** `rv64_sound`: every code word decodes, and a run of the binary that halts with "accept" read a proof that the trusted Lean verifier accepts, given `main`'s contract, its one hypothesis. 94 of 230 functions (15% of instructions) are proved and linked at the image. Real proofs run in the statement's own machine are accepted, mutated ones rejected.
- **Not proved:** `main`'s contract and the 136 functions without proofs; absence of traps (the theorem is partial correctness). The decoder and ELF reader are trusted, and the binary is a `no_std` copy of the verifier with inserted inline attributes.
- **Frameworks.** machine-checked's proved lift covered all 230 functions and its soundness theorem was reused unforked; we built relocatable templates, a link step, a symbolic executor (100 times cheaper on the one function measured) and a heap vocabulary around it. braid is very experimental: a nicer logic, but native axioms, absolute addresses and quadratic composition.
- **Recommendation.** The per-function, relocatable design is the right shape. Completion needs framework features first (heap and `sret` frames, nested representations, closures), then agent effort on loop invariants; CPU is not the constraint.

## 2. The question, and the two approaches

After a small or medium change to the Rust verifier, how much proving and building does it take to re-establish `Rust verifier accepts ⇒ Lean verifier accepts` for its RISC-V build? (The brief named PR #768 in places; it meant #738. We built on current `main`, which has moved on since #738 forked.)

```
#738   Rust → ELF → Image.lean (absolute addresses) → 2,352 block specs at pcs → 823 proof files naming pcs → Sound
                      ▲ every proof imports it: any change rebuilds everything

ours   Rust (no_std copy, frozen inlining) → hermetic ELF (sha256 pinned)
         → machine-checked proved lift → 230 relocatable templates tmpl(L)
         → per-function proofs over any program p with p[i] = tmpl L, callee contracts as hypotheses
         → contracts stated with Lean mirrors of the Rust; mirrors proved ⇒ verifyWith
         → link step (kernel checks, no proof search) instantiates all at the real image → rv64_sound
```

**#738** (RV64IM: 64-bit RISC-V with multiply) is about 680k lines, 89 commits in one day by agents; every proof imports the image, so moving one function by 4 bytes renames everything after it. **Ours** treats the binary like position-independent code with a linker: each function is proved once against its template, with its callees' **contracts** (pre- and postconditions, stated with a **Lean mirror** of the Rust) as hypotheses. About 30 agent runs over roughly one day (about 20 hours wall) built both the framework and the proofs.

## 3. What was built

**Hermetic build and provability rewrites.** The binary is a pure function of the sources (a stray `-C target-cpu=native` in a parent Cargo config had silently changed 128 of 230 functions), with function boundaries frozen, jump tables off and its sha256 pinned. Six behaviour-preserving rewrites of `crates/verifier` (enums for boxed closures, sorted `Vec`s for `BTreeMap`s, no divisions or `expect`s) removed every instruction the lift rejects; a review found no soundness bug, and 2,124 mutated proofs got identical verdicts before and after. Final image: 230 functions, 20,888 instructions.

**Lift, templates and link.** machine-checked's `decompile --to lean --proved` lifts all 230 functions into Lprog, its intermediate language, in about 5 s. Its transfer theorem says: if every function of the lifted program keeps its contract, every machine run from the entry that reaches the accepting system call satisfies the property the entry's contract promises. `scripts/gen.py` turns each lifted function into `tmpl (L : Link)`, `L` holding its base address and one entry per callee and per constant table, keyed by symbol name. A proof imports only its template and its callees' contracts, so Lake (Lean's build tool) rebuilds it only when that function's code changes, or the mirror, type layouts or contract framework it imports. The link step proves, per function, `(liftProg fns)[i]? = some (tmpl L)` and the link's well-formedness (each callee entry is the call target's address, each data reference points where the code computes it) by kernel evaluation, with no proof search.

**Contracts.** `Holds env p i need Pre Post Out` is machine-checked's contract plus the calling convention: on entry, enough stack, `sp` 16-aligned, static data intact; on return, `sp` and the callee-saved registers restored, memory unchanged outside the function's stack, its allocations and its declared out-buffer, and `Post`. It is partial correctness: a run that traps or diverges satisfies any contract. `env` abstracts the static data, the stack limit and the pointer of the bump allocator (which only increments, never frees), so no proof names an address.

**`rv_auto`.** An automated symbolic executor: it follows every path of a function's machine code, tracking registers and memory as formulas, applies callees' contracts at calls, and leaves only what needs insight, the functional identity and loop invariants. machine-checked's executor (`lsym`) cost 1.5 CPU-s per instruction on `E::mul`, `rv_auto` 0.015; it steps every path of all 230 functions in 354 CPU-s. The complete proof of `E::mul` (61 instructions, Karatsuba):

```lean
theorem ok … (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    (hcl : Clmul.spec env p L.clmul.idx needC) (hrd : Reduce.spec env p L.reduce.idx needR) :
    EMul.spec env p i need := by
  rv_auto hp with [hL] using [hcl, hrd]
  all_goals simp only [Model.eMul, ← hi128_xor, ← lo128_xor, ← hi128_shl1, ← lo128_shl1]
  all_goals simp only [BitVec.xor_assoc, BitVec.xor_comm, xor_left_comm, append_hi_lo]
```

**Mirrors, statement and non-vacuity.** `Rv64mc/Model` (12,011 lines, binary-free) mirrors each Rust function's loops, wrapping arithmetic and early returns. Its top theorem, `mainVerdictRust_sound`, proves that if the mirror of `main`'s verdict accepts, then `verifyWith` (the trusted Lean verifier of `formal/Statement`) accepts. Three reviews found no fidelity defect; where no machine proof exists yet, a mirror is tied to the Rust only by those reviews, a runner and a drift script. The trusted `EndStatement.lean` defines the machine, the loader, the input format, and:

```lean
def Sound (img : Image) : Prop :=
  ∀ words s n, Loaded img words s → Halts s n 0 →
    ∃ bytecode publicInput proof, decodeInput words = some (bytecode, publicInput, proof) ∧
      verify bytecode publicInput proof = true
theorem rv64_sound_of_main (hmain : MainSpec Rv64mc.env (liftProg fns) Idx.Main Needs.Main) :
    AllDecode image ∧ Sound image
```

`Halts` reaches the contracts through a bridge: each step of our machine is a step of SP1's (SP1 is a RISC-V zkVM whose machine machine-checked builds in), and our halt is its accepting state. `AllDecode`, proved by the kernel, stops `Sound` holding vacuously because the machine halts on an unknown instruction. On the current image, 24 runs of the statement's own machine and of the mirror on real proofs of four programs all came out as expected: honest proofs accepted after 127 to 205 million steps, bit-flipped ones rejected, truncated ones malformed.

## 4. Results

### Changes to proved functions (round 2, tree of 104 proof files)

| change | callers proved | rebuilt | broke | repair | CPU-s (wall) |
| --- | --- | --- | --- | --- | --- |
| C6 `E::mul` Karatsuba to schoolbook | 11 of 32 | 1; 62 after mirror edit | own proof | mirror 10 lines, 9 min | 3,230 (797 s) |
| C7 `dot` as an index loop | 1 of 8 | none (same binary) | nothing | none | 300 (235 s) |
| C7b `dot` from the last index down | 1 of 8 | 1; 45 after mirror edit | own proof | loop proof rewritten, 6 min | 2,627 (655 s) |
| C8 `duplex` lanes via `chunks_exact_mut` | 3 of 3 | 1 | own proof | **not repaired**: unrolled writes became a loop (estimated 1 to 2 h) | 1,073 (312 s) |
| C8b `duplex` counter reset moved | 3 of 3 | 1 | own proof | registers swapped, 9 min | 1,485 (468 s) |
| C9 `poly_eval` Horner from the top (contract change) | 0 of 4 | 58 | own proof | loop proof reversed, 6 min | 3,054 (621 s) |

Code changes never reached callers, not even to rebuild them; mirror edits rebuilt 45 to 62 importers, all green. Round 1's C1 is the contract change with proved callers (two, rebuilt green).

### Earlier changes (round 1, tree of 66 proof files)

| change | changed function proved? | broke | repair | CPU-s (wall) |
| --- | --- | --- | --- | --- |
| C1 `eq_eval`: `1 + x + y` to `1 + x * y`, with spec and mirror | yes; 2 callers proved | own proof | 3 min | 2,751 (584 s) |
| C2 `MerklePath::root` rewritten | no | nothing | none; a complete tree would re-prove `root` | 1,245 (380 s) |
| C3 unused function added (relocation) | none changed | 8 tables (literal indices, since fixed) | script, 3 min | 1,354 (413 s) |
| C4 two `Sponge` fields swapped | yes | 3 proofs (literal offsets, a layout assumption) | 21 lines, 9 min | 2,792 (658 s) |
| C5 a real 5-function commit reverted | 2 of 5 | 16 modules | unfinished after 20 min: a drop loop, and mirror drift caught only by the drift script | 1,461 (420 s) so far |
| I1 allocator alignment | yes (`alloc`) | `alloc`; 75 templates changed (LLVM dropped an argument program-wide) | untested on callers: one proved, written after | 2,948 (756 of it an unrelated module) |
| I2 16-byte stack alignment in every contract | framework | 20 proof, 3 framework files | 20 min | 2,212 |

### Against #738

| | ours | #738 |
| --- | --- | --- |
| cold build | 4,333 CPU-s (1.2 CPU-h), 516 s wall on 8 jobs | about 23.4 CPU-h, about 8 h wall (12 jobs, memory-capped to about 4.3 at once), peak 24.9 GB (13.3 GB for one module) |
| after C1 | 2,751 CPU-s, a 3-minute repair | 13,356 CPU-s (3.71 CPU-h), 57 min wall, peak 22.6 GB, before any repair: 182 modules rebuilt, 28 failed (27 proof files, 13,486 lines), 707 unchecked as importers of a failed one (701 proof files, 194,552 lines, `soundness` among them); first errors: 10 hardcoded pc or word index in a kernel check, 10 renamed block lemma, 8 address literal in a statement; the 3 sampled are renaming only; 228 proof files (76,569 lines) name a shifted address; no renaming script (estimated half a day to a day to write) |
| proof lines with a binary-specific token | 8.8% of 14,432 (mid-campaign) | 29% of 215,295 |
| absolute code addresses in proof text | 1 line | 6,962 |

Cold builds exclude Mathlib (and machine-checked, for ours) and include the Lean statement. #738's repair effort was never measured, only its textual breakage and rebuild; `eq_eval` sits late in its image (38 functions after it moved), and the same change early would touch most proofs. Our link step is a fixed floor of 670 to 1,000 CPU-s per change. The section 1 projection scales C1's non-link rebuild (about 1,650 CPU-s for 158 modules at 66 proof files) to all 230 functions, the unproved ones being the largest.

**Per function**, straight-line code costs seconds and a few lines (`E::mul`: 3 lines, 1.0 s); each loop needs a hand invariant of 50 to 250 lines (`eq_eval`: 63 lines, 2.9 s; `linear_transpose`, 5 loops: 1,027 lines, 70 s; `is_valid_encoding`: 347 lines, 135 s).

## 5. How far the full theorem got

- **Status.** 94 of 230 functions (3,161 of 20,888 instructions, 15%) are proved and linked at the image, 47 of them with no open hypothesis; 66 (47% of instructions) have a contract only, including partial proofs of `main` and `counting_sort`; 70 (38%) have nothing. 31,994 hand-written lines, standard axioms, no `sorry`, build green. The Model layer is complete.
- **Blockers** are mostly framework features: frames for heap blocks and for caller-owned `sret` slots (the hidden pointer through which a function returns a large value), callees whose output is not such a slot (`memcpy`), predicates for nested types, closure layouts (rustc does not report them), and arithmetic goals that exhaust memory.
- **Two lessons.** Contracts belong to machine instances, not Rust functions: LLVM specialised `try_allocate_in` for `main` without its `init` argument, so a contract written from the Rust signature was wrong. And a contract can be unprovable as written: `Sponge::new`'s first one let its inputs lie where it writes, and was fixed by a stronger precondition.
- **Extrapolation (estimate).** The WHIR family estimated 1.5 to 2 agent-hours per function that allocates, grows a `Vec`, loops and returns through `sret`; the largest functions (`verify_bus_balance` 899 instructions, `verify_whir` 855 with 18 loops, `walk` 762 with 16) did not fit a 3-hour time box, and `keccak_f` was estimated at 4 to 6 hours. At that rate the 136 functions left are 200 to 270 agent-hours if each cost as much (many are smaller, a few larger), after the framework features.

## 6. The frameworks

### machine-checked

**Worked.** The proved lift covered all 230 functions once the source was adapted; its contracts are generic in the program, so per-function proofs over templates needed no fork; its soundness theorems were reused unchanged.

**Missing**, each built or worked around by us:
- **Identity:** contracts mention the whole lifted program, and statements carry ELF-order indices and absolute addresses; a one-line change altered the Lean text of 45 of 89 lifted functions (1 modulo addresses). Our link step still evaluates the whole program per function, hence the floor.
- **Machine:** hard-wired to SP1 (about 47 references), with accept as `a0 = 0` and no contract possible for the function that halts; partial correctness only, so fault freedom cannot be stated.
- **Coverage:** functions with `unimp` or most 32-bit `W` instructions are dropped (109 of our first build's 198); jump tables are never lifted.
- **Executor:** `lsym` is quadratic, runs `simp` (Lean's rewriter) over the whole context, and its `bv_omega` arithmetic side conditions hang or exhaust kernel memory.
- **Memory and composition:** no regions, ownership, freshness or byte-in-word reasoning; no proved table composing contracts.

### braid (very experimental)

A successor design by machine-checked's author, started two days earlier, tried on the side. It has a generic RISC-V machine, Iris separation logic (framing built in) and loops by plain induction; it lowered an earlier build at about 0.03 CPU-s per instruction, and proved `E::mul` in about 8 CPU-s assuming its callee's contract, never carried to the machine. Its blockers: proofs rest on native axioms (`bv_decide` results trusted from compiled code, 132 in `eq_eval`), which this repository forbids; statements use absolute addresses (shifting code by 0x100 failed every proof until 22 literals were edited); triples are total and fault-free, which does not fit reachable panics; composition is quadratic in blocks.

| | machine-checked | braid |
| --- | --- | --- |
| machine | SP1, hard-wired | generic RV64 |
| lift or lowering | proved generically, 230 of 230 after rewrites | certified per function, 99% of an earlier build |
| identity | indices and absolute addresses | absolute addresses |
| logic | partial, traps safe | total, fault-free |
| memory | none | separation logic |
| axioms | standard | native `bv_decide` |
| composition | manual, whole program | callee blocks inside callers, quadratic check |

## 7. What to add to machine-checked (and braid)

Effort: S days, M one to two weeks, L a month or more (our judgment).

1. **A relocatable lift theorem with symbol-keyed, address-free output** (M): `liftFn` parametric in the function's base and a callee entry table, functions named by symbol, an emitter with a substitution map. Removes the link floor; our tables already moved to names (the C3 breakage is fixed), but link modules still reach the whole program through the index.
2. **Full instruction coverage** (S to M): `unimp`, every `W` operation, jump tables. An undecoded instruction traps, so without a decode check a soundness theorem can hold vacuously; we close this with a kernel-checked `AllDecode` conjunct, which the framework could provide.
3. **An executor that states the next state, with a memory vocabulary** (M to L): one rule per instruction form, no `simp` over hypotheses, loop heads from the control flow; regions, ownership, freshness, bytes; frames for heap blocks and caller-owned outputs; stack room and alignment in the contract from the start (adding alignment late cost the I2 migration).
4. **Machine contexts as parameters, with a fault-freedom judgement** (M): a context declares its step, memory check and halt convention, and a judgement where a trap is an error makes "every run stops only at the halting call" provable.
5. **For braid: kernel-only proofs and entry-relative statements** (M).

Further items in the roadmap: a contract table with a soundness theorem, per-function word modules, content-hash caching, loop schemas and path merging, generated layouts including closures, inline and ABI control.

## 8. Trust and caveats

- **Not stated:** completeness, termination, absence of traps. A machine that continues where ours stops (misaligned or out-of-window access, system calls) is not covered; `TrapFree`, the theorem that every run stops only at the halting call, is unproved. `main`'s contract is the open hypothesis.
- **Which binary:** the build of a `no_std` copy of `crates/verifier` written by `scripts/nostd-verifier.sh`, with inline attributes inserted from `boundaries.txt`, not the crate as shipped.
- **Trusted:** `EndStatement.lean`; riscv-zkvm's decoder (no theorem ties it to Sail, the reference ISA model) and its instruction semantics (tied to Sail except for a few instructions, among them `SRLW` and `SRLIW`, which the image uses); SP1's memory check; the ELF reader.
- **Bytecode encoding gap (open obligation M5):** composing with the leanVM statement assumes the program's encoded bytecode equals the words read.

## 9. Reproduce

```bash
cd formal/rv64mc && scripts/regen.sh && scripts/type-layouts.sh && lake build Rv64mc   # image, templates, proofs
scripts/iterate.sh --init && scripts/iterate.sh bench/patches/C1.patch --label C1         # one benchmark change
lake build rv64mc-run && .lake/build/bin/rv64mc-run out/canon.elf WORDS --verify          # run the statement's machine
```
