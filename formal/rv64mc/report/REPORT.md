# Decompiling the RISC-V verifier into Lean: how cheap is it to re-prove after a change?

Experimental draft, 2026-11-20. Project `formal/rv64mc`, compared with draft PR #738. CPU-seconds (CPU-s) are the primary metric throughout: the host was shared (load 15 to 100 on 32 cores), so wall times are inflated and only indicative.

## 1. Summary

- **Iteration, the main question.** After a small or medium change to the verifier, our pipeline regenerates and re-checks everything in 1,250 to 2,800 CPU-s (6 to 11 minutes wall on 6 jobs), and repair took 0 to 20 minutes of agent work, local to the changed function's own proof, proofs that hard-coded a layout offset, and contract tables. #738 rebuilds nearly everything on the same change, because every proof imports the absolute-address image; its cold build is 20.4 CPU-hours (4 h 45 min wall, 26.5 GB peak). Measured #738 rebuild after the same change: {{PR738_C1}}. Order of magnitude: **minutes and a fraction of a CPU-hour, against hours and tens of CPU-hours**.
- **Proved end to end, standard axioms only:** `rv64_sound`: every code word decodes, and a run of the binary that halts with "accept" read a proof that the Lean verifier `verifyWith` accepts, *given `main`'s contract*. The Lean mirror of the Rust is complete and proved to imply the Lean verifier. Real proofs run in the statement's own machine halt with accept (honest), reject (mutated) or malformed (truncated), so the statement is not vacuous.
- **Not proved yet:** `main`'s contract, i.e. the machine-code proofs of the top of the call graph ({{STATUS}}). The theorem is partial correctness (a trap is not excluded), is about a `no_std` copy of the verifier with inserted inline attributes, and trusts riscv-zkvm's decoder and an ELF reader.
- **Framework gaps.** machine-checked's proved lift worked (230 of 230 functions) and its soundness theorem was reused unforked. Almost everything around it had to be built: relocatable per-function templates and a link step (its contracts are whole-program and its output names absolute addresses and indices), a symbolic executor 100 times cheaper than its `lsym`, a heap and frame vocabulary, a bridge from SP1's machine to the statement's. braid, which is **very experimental**, has a nicer logic but rests on native `bv_decide` axioms, absolute addresses and a quadratic composition certificate.
- **Recommendation.** The per-function, relocatable design is the right shape: iteration is cheap and breakage is local. What blocks completion is missing framework features (heap and `sret` frames, nested representations, closures), not CPU. machine-checked should add, first: a relocatable lift with symbol-keyed output; full instruction coverage; an `lsym` that states the next state, with a memory vocabulary; machine contexts as parameters, with a fault-freedom judgement.

## 2. The question, and the two approaches

The question: if the Rust verifier changes a little, how much proving and building does it take to re-establish `Rust verifier accepts ⇒ Lean verifier accepts` for its RISC-V build?

**#738** compiles the verifier for RV64IM (64-bit RISC-V, integer and multiply), exports the binary as one Lean file (`Image.lean`: 101 functions, 18,870 instructions), cuts it into 2,352 basic blocks keyed by absolute address, checks each by symbolic execution (412,827 generated lines), and proves 823 files (229,028 lines) of per-function proofs that name program counters, registers and stack offsets: about 680k lines, written by agents in one day. For iteration, its weakness is that every proof imports the image, and 29% of proof lines contain binary-specific tokens (6,962 distinct code addresses). Moving one function by 4 bytes changes the addresses of everything after it.

**Ours** treats the binary like position-independent code with a linker. machine-checked decompiles each function with a *proved* lift into Lprog, its intermediate language. A generator turns each lifted function into a **template** parametric in where it lives and where its callees and constants live. Each function is proved once against its template, with its callees' **contracts** as hypotheses; a contract states the function's effect in terms of a **Lean mirror** of the Rust function. A proof-free **link step** checks by kernel evaluation that the real binary is an instance of the templates. The mirrors are proved, once, to imply the trusted Lean verifier.

```
#738   Rust → ELF → Image.lean (absolute addresses) → 2,352 block specs at pcs → 823 proof files naming pcs → Sound
                      ▲ every proof imports it: any change rebuilds everything

ours   Rust (no_std copy, frozen inlining) → hermetic ELF (sha256 pinned)
         → machine-checked proved lift → 230 relocatable templates tmpl(L)
         → per-function proofs over any program p with p[i] = tmpl L, callee contracts as hypotheses
         → contracts stated with Lean mirrors of the Rust; mirrors proved ⇒ verifyWith
         → link step (kernel checks, no proof search) instantiates all at the real image → rv64_sound
```

## 3. What was built, layer by layer

**Hermetic guest build and provability rewrites.** The ELF is a pure function of the sources: built in a fresh directory with the guest's own flags (a stray `-C target-cpu=native` from a parent Cargo config silently changed 128 of 230 functions), its sha256 pinned and rechecked by `regen.sh --check`. Function boundaries are frozen (`#[inline(never)]` on every verifier function except 28 listed straight-line helpers; jump tables and function merging off; relocations emitted). Six behaviour-preserving rewrites of `crates/verifier` (enums instead of boxed closures, sorted `Vec`s instead of `BTreeMap`s, no divisions or `expect`s on the verification path) removed every instruction the lift cannot handle; an adversarial review found no soundness bug, and 2,124 mutated proofs gave identical verdicts before and after. Result: 230 functions, 20,723 instructions.

**machine-checked's lift.** `decompile --to lean --proved` lifts all 230 functions in about 5 s, and its transfer theorem turns a contract on the lifted program into a statement about the machine. Both are used unchanged.

**Templates and the link step.** `scripts/gen.py` rewrites each lifted function into `tmpl (L : Link)`, where `L` holds the function's base address, one entry per callee and one per constant table, keyed by demangled symbol, never by address or index. A proof imports only its own template, so Lake rebuilds it only if that function's code changes. Each function's link module checks `(liftProg fns)[i]? = some (tmpl L)` and the link's well-formedness by kernel evaluation: about 1,000 CPU-s for the whole image, no proof search.

**The contract framework.** `Holds env p i need Pre Post Out` (`Core/Holds.lean`) is machine-checked's contract plus the calling convention: on entry, `need` bytes of stack, `sp` 16-aligned, static data intact; on return, `sp` and `s0` to `s11` restored, memory unchanged outside the function's stack, its allocations and its declared out-buffer (`Out`), and `Post`. It is partial correctness: a run that traps or diverges satisfies any contract. The environment `Env` abstracts the static data, the bump allocator's `NEXT` pointer and the stack limit, so no proof mentions the image's addresses.

**`rv_auto`, a symbolic executor.** machine-checked's `lsym` cost 1.5 CPU-s per instruction on `E::mul` (61 instructions), mostly `simp` over the whole context and `bv_omega` side conditions. `rv_auto` applies one named rule per instruction form and states the next state itself, keeps addresses as base plus literal offset with kernel-decided side conditions, and carries the body's suffix instead of looking instructions up by index. Result: 0.015 CPU-s per instruction on `E::mul` (91 to 0.9 CPU-s, a 100 times cut), and every path of all 230 functions stepped in 354 CPU-s. A whole straight-line proof:

```lean
theorem ok … (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    (hcl : Clmul.spec env p L.clmul.idx needC) (hrd : Reduce.spec env p L.reduce.idx needR) :
    EMul.spec env p i need := by
  rv_auto hp with [hL] using [hcl, hrd]
  all_goals simp only [Model.eMul, ← hi128_xor, ← lo128_xor, ← hi128_shl1, ← lo128_shl1]
  all_goals simp only [BitVec.xor_assoc, BitVec.xor_comm, xor_left_comm, append_hi_lo]
```

What remains manual: the functional algebra, loop invariants (a lemma by induction at each loop head), and heap reasoning beyond what the opt-in heap mode (`rv_sym.heap`) closes.

**Model mirrors and their capstone.** `Rv64mc/Model` (11,932 lines, no binary coupling) mirrors each Rust function in Lean, following its loop order, wrapping arithmetic and early returns. The capstone `mainVerdictRust_sound` proves that if the mirror of `main`'s verdict accepts, then `verifyWith keccakF1600` accepts, with one hypothesis (Merkle leaf indices below 2^64, which `u64` guarantees). Three adversarial reviews found no fidelity or soundness defect. A compiled runner (`rv64mc-model`) checks the mirror on real inputs: 4 of 4 honest proofs accepted, 4 of 4 mutated rejected, 4 of 4 truncated undecodable, each agreeing with the Lean verifier.

**The end statement and its non-vacuity.** `EndStatement.lean` (trusted, about 200 lines) defines the machine, the loader, the input format and:

```lean
def Sound (img : Image) : Prop :=
  ∀ words s n, Loaded img words s → Halts s n 0 →
    ∃ bytecode publicInput proof, decodeInput words = some (bytecode, publicInput, proof) ∧
      verify bytecode publicInput proof = true
theorem rv64_sound (hmain : MainSpec env (liftProg Gen.fns) Gen.Start.link.main.idx need) :
    AllDecode image ∧ Sound image
```

`AllDecode` (every code word decodes) is proved by the kernel, so `Sound` cannot hold vacuously by the machine stopping on an unknown instruction, and `loaded_nonempty` proves the loader satisfiable. A runner (`rv64mc-run`) executes the statement's own `step` on real proofs of four programs: honest inputs halt with accept after 127 to 205 million steps, bit-flipped ones with reject after 2.6 to 4.3 million, truncated ones with malformed after 1.7 to 3.4 million.

## 4. Results

### Iteration benchmark

Each change is applied to a copy of a green tree (66 proof files, 74 contracts linked): regenerate, rebuild, sweep, repair. The total includes the repair rebuilds.

| change | templates changed | proof modules rebuilt | broke | repair (agent) | total CPU-s (wall) |
| --- | --- | --- | --- | --- | --- |
| C0 nothing | 0 | 0 | nothing | none | 194 (172 s) |
| C1 `eq_eval`: `1 + x + y` to `1 + x * y`, with Lean spec and mirror | 1 | 47 | its own proof | 1 file, 3 min | 2,751 (584 s) |
| C2 `MerklePath::root` rewritten, Rust only | 1 | 0 | nothing | none | 1,245 (380 s) |
| C3 an unused function added (pure relocation) | 1 added | 0 | 8 tables (literal indices) | script, 3 min | 1,354 (413 s) |
| C4 two `Sponge` fields swapped (representation) | 5 | 56 | 3 proofs (literal offsets, a layout assumption) | 21 lines, 9 min | 2,792 (658 s) |
| C5 a real 5-function commit reverted | 4 changed, 1 added, 4 removed | 1 | 16 (removed functions, tables, one drop proof) | 20 min, 1 proof left | 1,461 (420 s) |
| I1 allocator alignment (unplanned) | 75 | full build | `alloc`'s own proof | spec 13 lines, proof 42 added, 37 removed | 2,948 (756 of it an unrelated unfinished module) |
| I2 framework: stack alignment added to every contract | 0 | all | 23 files | hypotheses threaded, 20 min | 2,212 |

For comparison, #738: cold build 73,440 CPU-s (20.4 CPU-hours, 1,053 modules). C1 on its own tree changes one function modulo addresses but 59 byte for byte (everything after it moves by 4 bytes), and the rebuild was expected to take 4 to 5 hours wall. Measured: {{PR738_C1}}. For the real gap between #738's fork point and today's `main` (`E` from three limbs to two, a new WHIR fold, a new ring switch), the three-limb accessor alone has 3,133 uses in 361 of its proof files: essentially every per-function proof would be redone.

Lessons. The floor of any change is the link step, 880 to 1,000 CPU-s, plus about 160 CPU-s to regenerate. A Rust-only change to an unproved function, or a relocation, rebuilds no proof. An edit to the Lean spec or mirror rebuilds every importer of the Model (C1); a layout change, every importer of the layouts (C4). I1 showed the design's predicted risk: a one-line allocator change made LLVM drop an argument program-wide and changed 75 templates, yet no caller proof needed an edit, because callers see only `alloc`'s contract and `rv_auto` re-steps the new call sequences. These numbers come from a partial proof tree: rebuild costs that scale with importers will grow with it; the link floor will not.

### Coupling to the binary

| | ours | #738 |
| --- | --- | --- |
| hand- or agent-written proof, spec and table lines | 14,432 | 215,295 |
| lines with any binary-specific token (address, register, pc, stack offset) | 1,277 (8.8%) | 61,970 (29%) |
| absolute code addresses | 1 line | 6,962 distinct |

Our binary-specific lines are mostly argument registers in specs (the calling convention) and 32 numeric loop-head positions.

### Per-function cost

From the proof logs; CPU-s are tactic plus kernel. Straight-line arithmetic costs about a second and a few lines: `E::mul` (61 instructions) 3 proof lines, 1.0 s; `Layout::constant` one `rv_auto` line, 5.5 s. A simple loop adds a hand invariant: `eq_eval` 63 lines, 2.9 s; `dot` 102 lines, 7.0 s. Heavy cases: `K::inv` (291 instructions, 63 unrolled squarings) 41.6 s; `linear_transpose` (196 instructions, 5 loops) 1,027 lines, 70 s; `finish_grow` 219 lines, about 100 s; `is_valid_encoding` 347 lines, 135 s. In proof lines per instruction, ours runs from about 0.05 (`E::mul`) to 5 to 7 for loop and heap code (`linear_transpose`, `selector_point`); #738 averages about 12.

## 5. How far the full theorem got

- **End theorem:** `rv64_sound` is proved with `main`'s contract (`MainSpec`) as its one hypothesis; `_start`, the bridge to the statement's machine, the Model-to-verdict step and `verify_execution` (a tail call of `walk`) are proved.
- **Model layer:** complete, capstone proved.
- **Per-function machine proofs:** {{STATUS}}.
- **What blocks the rest** is mostly framework, not proof writing: frames for heap blocks and caller-owned `sret` slots (blocked `main`, `Bytecode::new`, `Input::digest`), callees whose out-buffer is not an `sret` (`memcpy`), representation predicates for nested types (`Vec<Vec<Form>>`, the layout tables), closure environments (rustc does not report their layout, so offsets were read off the code), `Result` layouts not yet generated, and 64-bit `omega` goals that exhaust memory.
- **Extrapolation, with its basis.** CPU is not the constraint: stepping every instruction costs 354 CPU-s, and a proved function seconds to minutes. Agent effort is: loop invariants run 50 to 250 lines each, and the WHIR family estimated 1.5 to 2 agent-hours per function that allocates, grows a `Vec`, loops and returns through `sret`. The largest functions (`verify_bus_balance` 899 instructions, `verify_whir` 855 with 18 loops, `walk` 762 with 16 loops) did not fit a 3-hour time box. The heap mode already cut `finish_grow`'s leftover goals from 83 to 15; the framework items of section 7 should come before more proof writing.

## 6. The frameworks

### machine-checked

**What worked.** The proved lift covered 230 of 230 functions once the source was adapted. Its contracts are generic in the program `p`, so per-function proofs over symbolic templates worked without a fork (confirmed in the first probe). Its lift soundness and transfer theorems were reused unchanged. Decompiling takes seconds.

**What did not, or had to be built.**
- **SP1-only machine:** step, memory check and `ecall` are hard-wired to SP1 (about 47 references), and accept means `a0 = 0`. We changed the guest's verdict code and proved a bridge to our statement's machine.
- **The accepting function has no contract:** the accepting `ecall` cannot occur inside one; only `_start` is proved directly.
- **Whole-program contracts:** contracts mention `liftProg fns`, so any word change rebuilds everything; we wrote our own template generator. Even so, each link module evaluates `liftProg` over all functions, so every change pays the full 1,000 CPU-s link floor.
- **Index and address identity:** functions are numbered in ELF order and statements carry literal addresses; a one-line source change altered the Lean text of 45 of 89 lifted functions (1 modulo addresses).
- **Emitter literals:** mangled names, 128-instruction chunks, callee indices only inside candidate lists; we recovered the structure by parsing the output.
- **`lsym` cost and hazards:** quadratic in function length, `simp` over the context, `bv_omega` that hangs, kernel unfolding hazards (deep recursion on `0 + 0xfff…f`, 16 GB unfolding a `mulhu` value).
- **No memory vocabulary:** no regions, ownership, freshness or byte-in-doubleword reasoning; we built `Env.Frame`, the heap mode and byte lemmas.
- **Coverage:** `--proved` drops any function containing `unimp` or most 32-bit `W` operations: 109 of our first build's 198 functions. Jump tables are never lifted, so we build with them off. An indirect call with an unknown target gets every function as candidate.
- **No proved composition table** at the Lprog level; composition is by hand.
- **Partial correctness only:** traps count as safe, so fault freedom cannot be stated.
- **Trust:** the decoder is not tied to Sail, the ELF is read at elaboration time, and no theorem produces the loaded state.

### braid (very experimental)

braid, a successor redesign by machine-checked's author begun two days before this run, was tried on the side. **Good:** a generic RISC-V step (not SP1), an exit convention matching our guest, an Iris separation logic with framing built in, loops by plain induction, and cheap stepping (about 0.03 CPU-s per instruction to lower and certify the whole image, 99% of it lowered). `E::mul` took about 8 CPU-s. **Blockers:** the stepper discharges alignment with `bv_decide`, so `eq_eval`'s proof rests on 132 native axioms, which this repository forbids; statements use absolute addresses (shifting code by 0x100 changed 677 of 753 lines and failed every proof); callers embed callee blocks, with a composition certificate quadratic in blocks (17 to 24 s for about 300); triples are total and fault-free, which does not fit reachable panics or a halting `ecall`; omitting one read-only data cell made a hypothesis unsatisfiable and its theorems vacuous, caught only one level up.

| | machine-checked | braid |
| --- | --- | --- |
| machine | SP1 step, hard-wired | generic RV64 step |
| lift or lowering | proved, 230 of 230 after rewrites | proved, 99% of the image |
| identity | indices and absolute addresses | absolute addresses |
| logic | partial, traps safe | total, fault-free |
| memory | none | separation logic |
| axioms | standard | native `bv_decide` |
| composition | manual, whole program | callee blocks inside callers, quadratic check |
| maturity | usable with additions | very experimental |

## 7. What to add to machine-checked (and braid)

Effort: S days, M one to two weeks, L a month or more (our judgment). The five that matter most:

1. **A relocatable lift theorem with symbol-keyed, address-free output** (M): `liftFn` parametric in the function's base and a callee entry table, functions named by symbol, an emitter with a substitution map. Removes the 1,000 CPU-s link floor and the C3 kind of breakage.
2. **Full instruction coverage** (S to M): `unimp` and every `W` operation lifted (an undecoded op traps, so `Sound` would hold vacuously), and jump tables, so the proved binary is the default build.
3. **An `lsym` that states the next state, with a memory vocabulary** (M to L): one rule per instruction form, no `simp` on hypotheses, no `bv_omega` side conditions, loop heads from the control flow; regions, ownership, freshness, bytes; frames for heap blocks and caller-owned out-buffers; stack room and alignment in the contract from the start (adding alignment late cost a 23-file migration).
4. **Machine contexts as parameters, with a fault-freedom judgement** (M): a context declares its step, memory check and halt convention; a judgement where a trap is an error makes `TrapFree` provable.
5. **For braid: kernel-only proofs and entry-relative statements** (M).

Also: a contract table with a soundness theorem, keyed by name (M); per-function word modules (S); content-hash caching per template (M); loop schemas and path merging (L; without merging, `walk`'s 763 instructions took 25,282 steps); generated type layouts including closures and `Result` niches (M); exact stack needs (S); inline and ABI control, so that whole-program argument elimination cannot change callers (M); hermetic builds (S). For braid: composition by callee contract, partial-correctness and exit triples, frame ergonomics, `braid-lower` split per ISA (its build cost 3,466 CPU-s).

## 8. Trust and caveats

- **What is proved:** if the loaded binary halts at an `ecall` with `t0 = 0` and `a0 = 0`, its input decodes to a bytecode, public input and proof that the Lean verifier accepts. Not proved: completeness, termination, or that the binary never traps; a machine that continues where ours stops (misaligned or out-of-window access, system calls) is not covered (`TrapFree` is named, not proved).
- **Which binary:** the build of a `no_std` copy of `crates/verifier` written by `scripts/nostd-verifier.sh`, with inline attributes inserted from `boundaries.txt`, not the crate as shipped.
- **Trusted:** `EndStatement.lean`; riscv-zkvm's decoder (no theorem ties it to Sail); its instruction semantics (tied to Sail except for a few instructions, among them `SRLW` and `SRLIW`, which the image uses); SP1's memory check; the ELF reader.
- **Bytecode encoding gap (M5):** the composition with the leanVM statement assumes the program's encoded bytecode equals the words read; not closed.
- **Open hypothesis:** `main`'s contract (section 5).
- **Non-vacuity runs** were made on the image before I1 (sha256 `8cb4e7b8…`); the pinned image is now `d58fd6eb…`, and the runs should be repeated.
- **Timings:** CPU-s are primary; wall times were taken under load 15 to 100 from other sessions.

## 9. Reproduce

```bash
cd formal/rv64mc
scripts/regen.sh                # hermetic guest build, lift, templates (--check: sha256 and files unchanged)
scripts/type-layouts.sh         # Rust type layouts into Rv64mc/Gen/Layouts.lean
lake build Rv64mc               # link step, proofs, rv64_sound
scripts/iterate.sh --init       # benchmark base copy, then one change:
scripts/iterate.sh bench/patches/C1.patch --label C1
lake build rv64mc-run rv64mc-model
python3 -I scripts/input-words.py FIX/fibonacci-rate4 fib.words   # FIX from formal/lean_vm/scripts/export-verifier-fixtures-rust.sh
.lake/build/bin/rv64mc-run out/canon.elf fib.words --verify       # halted, a0 = 0; verify: true
.lake/build/bin/rv64mc-model fib.words                            # mainVerdictRust: true, verify: true
```

## 10. A note on the brief

The request named PR #768 in places; it meant #738 (#768 is the sidecar PR). The work is based on current `main`, not on #738's fork, so it does not inherit #738's Rust rewrites, and the gap between the two is the "real change" against which #738's reuse is judged.
