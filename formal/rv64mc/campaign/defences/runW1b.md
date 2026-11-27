# Defence: wave 1b, total contracts of `memcpy` (with the bytes copied), `xor_block`, `E::sum::<Chain>`, `keccak_cell_lanes`; `memmove` stated only; `keccak_f` not done

Base: e8794dc66a. Head: 2490caba17 (branch formal/rv64mc-total-w1b, worktree /home/devops/leanEthereum/leanVM-t-symt, 9 commits, not pushed).

Check: `cd formal/rv64mc && timeout 3600 systemd-run --user --scope -q -p MemoryMax=16G lake build Rv64mc.Spec.Runtime.MemT Rv64mc.Proof.Runtime.CopyT Rv64mc.Proof.Runtime.MemcpyT Rv64mc.Proof.Runtime.MemmoveT Rv64mc.Proof.Hash.XorBlockT Rv64mc.Proof.Field.SumChainT Rv64mc.Proof.Layout.KeccakCellLanesT Rv64mc.Table.MemT Rv64mc.Table.HashT Rv64mc.Table.FieldSumT Rv64mc.Table.LayoutT` -> `Build completed successfully (4906 jobs)`, no warning lines. Each module was first built from scratch by the same command form (e.g. CopyT+MemcpyT: 1m16s wall; XorBlockT/SumChainT/MemcpyT/MemT rebuild 1m11s). `lake env lean` of the heaviest file: `MemcpyT.lean` 58.0 s, `CopyT.lean` 10.3 s (machine shared with a sibling build; an earlier run of MemcpyT took 22 s).

Every new theorem that is a deliverable carries a `#guard_msgs in #print axioms` block pinning `[propext, Classical.choice, Quot.sound]`: `MemcpyT.total`, `XorBlockT.total`, `SumChainT.total`, `KeccakCellLanesT.total`, `Table.MemT.memcpyT`, `memsetT`, `Table.HashT.xorBlockT`, `Table.FieldSumT.sumChainT`, `Table.LayoutT.keccakCellLanesT`.

## Decisions

### D1. `CopyPostT` (Spec/Runtime/MemT.lean) restricts `CopyPost`'s byte frame to bytes apart from the stack below the entry's stack pointer
- **Why**: the existing `CopyPost` says `ByteFrame m m' dst n`: every byte outside `[dst, dst + n)` is kept, the callee's own stack included. `compiler_builtins`' `memcpy` keeps scratch in its stack slot `sp + 8 = top - 8` on the misaligned path (template labels 27, 58: `sd [sp+8] 0`; labels 100-122: narrow stores of source bytes into it; 38/69: loads of it) and does not restore it. So for an input with the source misaligned against the destination after alignment (n at least 16) and the slot's byte 7 non-zero at entry, the slot's byte 7 is 0 at return: `CopyPost` fails, and `MemcpySpec` (a `Holds`, universally quantified over memories) is false of this template whenever such a run returns. The same holds of `memmove` (its frame at `sp`, labels 31, 42 store and load a partial word there; it saves `x8` at `sp + 8`). This argument is by reading the template; it is **not machine-checked**. If it is right, `MemcpySpec`/`MemmoveSpec`, open hypotheses of 47 partial `Table` theorems (`notes/status.md`: "memcpy (223)"), are unsatisfiable at the image.
- **Rejected**: keeping `CopyPost` verbatim (unprovable, by the above); an `OffStack`-free frame "outside `[top - 16, top)`" (names memcpy's frame size in the spec and does not fit memmove's).
- **Claims**: `CopyPostT env regs m r' m'` = `r' .x10 = regs .x10` ∧ the same copied-bytes conjunct as `CopyPost` ∧ `∀ b, ¬ InRange (regs .x10) n b → OffStack env (regs .x2) b 1 → m'.getByte b = m.getByte b`. Together with `HoldsT`'s `Env.Frame top (CopyOut regs m)` (doublewords of the destination, plus the stack below `top`, allocations, `NEXT`) this is the precise frame a caller can use: its objects lie at or above its stack pointer (= the callee's `regs .x2`), in the heap, or in the static data, all `OffStack`.
- **Evidence**: `MemT.lean` lines defining `CopyPostT`; `MemcpyT.ret_ok` proves exactly these three conjuncts from `Inv … n`.

### D2. `CopyPreT` (Spec/Runtime/MemT.lean): `CopyPre`, and unless `n = 0`, the destination in the heap window up to `heapEnd` or the stack window from `stackLimit`, the source `inWindow`, both `OffStack env (regs .x2)`
- **Why**: the destination needs a window apart from the static data and `NEXT` (else `env.Static`/`NEXT` could break), as `MemsetT.InWin` (written inline here so that a Spec module does not import a Proof module; it is definitionally `MemsetT.InWin`, used as such in `MemcpyT.Fx`). The source only needs to be readable: `inWindow`, because `keccak_f` copies its 192-byte round-constant table out of the static data (`.rodata` at 0xa0000000.., `guest/link.x`), which `InWin` excludes (static data lies in `[staticLo, staticHi)` with `heapEnd ≤ staticLo` and `staticHi < stackLimit`). `OffStack` (below `stackLimit` or at or above the stack pointer) is needed for both: the slot stores at `[top - 16, top)` must not hit the source before it is read nor the destination after it is written. The disjunct `n = 0` because `Vec::clone` of an empty vector calls `memcpy(8, dangling, 0)` (`Alloc/Vec/VecE/AsClone/Clone`, `x10 = 8`, `x12 = len * size`).
- **Rejected**: `InWin` for the source (vacuous at keccak_f's call); no `OffStack` (the functional postcondition is then false when the source or destination overlaps the callee's slot).
- **Claims (call sites, by reading the templates; not machine-checked)**: the 47 `call`/`tail` sites of `memcpy` (the C wrapper 227, which tail-calls 223 keeping `sp`; list in runW1b/memcpy_sites.txt, made by mainT/sites2.py) pass (a) a destination in the caller's frame (`x2 + c`), an `sret`/out pointer of a caller (`x8`, `x9` + c), or a fresh `alloc` block, and (b) a source in the caller's frame, a caller's object, a heap buffer, the input, or (keccak_f only) the static data. Each is either in the heap window below `heapEnd` (below `stackLimit`) or in the stack window at or above the calling function's `sp`, which is `memcpy`'s `regs .x2`; `NoWrap` and non-overlap are `CopyPre`'s, unchanged. Which caller fact discharges the window conjuncts is the caller's own representation facts (its `VecAt`/`InWin` facts, its frame bounds), which the caller's total proof must carry; for keccak_f, the table's words are `env.data` entries, and such a word lies in `[staticLo, staticHi)` (from `Env.static_frame` + `static_data` given one `Static m`; not proved yet, see Not done) and in a window (`Windows.data_ok`).
- **Evidence**: `python3 mainT/sites2.py memcpy` (run from formal/rv64mc) output (runW1b/memcpy_sites.txt), keccak_f template labels 15-20.

### D3. `MemcpyT.total : MemcpySpecT env p i 16` over the template, by parts (Proof/Runtime/MemcpyT.lean, Proof/Runtime/CopyT.lean)
- **Why**: one `rv_autoT` run over the 254-instruction body leaves 22 goals with large terms; cut at the loops' heads and at the partial loads' joins, each part is a theorem from its program counter (`ret_ok` 196, `loopD_ok` 184, `tail_ok` 176, `loopC_ok` 166, `lastWord_ok` 138, `lastByte_ok` 128, `bit0_ok` 124, `partial_ok` 110, `loopB_ok` 90, `prev_ok` 76, `endWord_ok` 68, `endBit2_ok` 64, `endPartial_ok` 44, `words_ok` 32, `loopA_ok` 20, `total` 0), stepped by `rv_symT … stop [...]`, the next part applied at each stop. The copy so far is `CopyT.Inv` (Kept frame; `∀ k < j`, byte `dst + k` = entry byte `src + k`; every byte outside `[dst, dst + j)` and off the stack below `top` kept), maintained by `Inv.byte`, `Inv.word`, `Inv.slot`, `slot_copy(_from)`.
- **Rejected**: `TStep` by hand as `MemsetT` (the template is 127 instructions with 7 narrow-store paths; `TotalRv.label`'s `rfl` on `fd.body[pc]?` hit the kernel's deep-recursion limit at pc 196 in a first attempt; `rv_symT` fetches by `drop_at`).
- **Claims**: every loop is `Total.loop` with a measure that strictly decreases on the back edge: `DInv` bytes left `c` (back edge `ih (c - 1)`, `0 < c`), `CInv` bytes left `k` (`ih (k - 8)`, `0 < k`), `BInv` bytes left `k ≥ 16` (`ih (k - 8)`), `AInv` bytes left `c` (`ih (c - 1)`). The functional content is the whole `CopyPostT`: `Inv … n` at the return gives the copied bytes and the byte frame. The source disjointness used is `Fx.disj`, from `CopyPre false`'s non-overlap. `Fx` (entry facts) has no field that is not derived from `HoldsT.pre` in `total`.
- **Evidence**: build above; `#print axioms MemcpyT.total` pinned.

### D4. Safety-only total contracts for `xor_block`, `E::sum::<Chain<…>>`, `keccak_cell_lanes` (Post `True`, a precise `Out`)
- **Why**: the task asks functional postconditions "where a spec exists and callers need it, safety ones otherwise". No caller's safety reads a Keccak lane's value, the sum's value, or the cell lanes as addresses: `keccak_hash` only passes its state on to `keccak_f`; `verify_bus_balance` compares sums; `flushes_keccak` reads the cell array's entries as data. Each keeps `Out` exact: `XorBlock.Out` (the spec's: the state's 200 bytes), nothing for `E::sum` (`Out` default `False`), `CellOut = DwordsOf sret 416` for `keccak_cell_lanes`.
- **Rejected**: proving `Spec.Hash.XorBlock`'s functional post (`Model.xorBlockRust`): a byte-assembly proof over 136 byte loads, not needed for `MainSpecT`; it can be added later with `HoldsT.of_holds_post` once a partial proof exists.
- **Claims**: `XorPreT`: state 8-aligned, `InWin`-shaped (inline) for 200 bytes, `OffStack env (regs .x2)` (xor_block saves a register at `sp + 8` of a 16-byte frame), block 136 bytes `inWindow` (inline disjunction). At both call sites in `keccak_hash` (`KeccakHash` instructions 32, 60) the state is `x2 + 0` (keccak_hash's frame: stack window, at or above its `sp`, 16-aligned) and the block is `x9` (the data slice, a caller's object) or `x2 + 0xc8` (keccak_hash's frame). `SumPreT`: the chain struct 8-aligned, 64 bytes in a window (`Win`, inline), and each `IterOk tag ptr end` (None, or `ptr ≤ end`, `16 ∣ end - ptr`, ptr 8-aligned, elements in a window unless empty); at `verify_bus_balance` the chain is built in its frame from two `Vec<E>::into_iter`, whose dangling empty pointer satisfies the `end = ptr` disjunct. `CellPreT`: sret 8-aligned, 416 bytes in a window; its one call site (`FlushesKeccak`, instruction 189 area) passes `x2 + 0x60`. Loops: `SumChainT.loopA_ok`/`loopB_ok` bytes left `k` (`ih (k - 16)`, `0 < k`, `16 ∣ k`), `KeccakCellLanesT.loop_ok` entries left `k ≤ 11` (`ih (k - 1)`, exit exactly at `k = 0`).
- **Evidence**: build above; `XorBlockT.total` is `rv_autoT hp` alone (every side goal closed by the executor).

### D5. `Table` instances in new files `Table/MemT.lean` (223, 224), `HashT.lean` (123), `FieldSumT.lean` (34), `LayoutT.lean` (208)
- **Why**: the task's deliverable 3 for functions whose callees are all total (these are leaves). Each is `HoldsT.mono_need (… .total <Gen>.tmpl_eq) (by decide)` at `liftProg Gen.fns`, `Gen.Idx`, `Gen.Needs`; no hypothesis but `env`.
- **Rejected**: wrappers 227-229 (the sibling wave's), `memmove` (unproved), `keccak_f` (unproved).
- **Claims**: `memsetT` instantiates the existing `MemsetT.total` (no new proof); the sibling task also says to instantiate "the functions already total", so a second `memset` instance may appear in its files: harmless, different names.
- **Evidence**: build above; axioms pinned.

### D6. `MemmoveSpecT` stated with `CopyPreT true` and `CopyPostT` (Proof/Runtime/MemmoveT.lean), no proof
- **Why**: published in the first commit (5cd0a65a88) so the sibling can state the wrapper 228 over it.
- **Claims**: same shape as `MemcpySpecT` but `overlap = true`; the call sites (`Form::add_scaled`, `whir::subspace_roots`) move within one heap vector (window, `OffStack` by the heap's position).

### D7. Order of work: deliverable 2 and 3 items before `memmove`
- **Why**: `memmove` is a forward copy (memcpy's algorithm, recompiled with other registers and pcs) plus a backward copy (a mirror needing a suffix invariant and reverse partial loads): about the effort of `memcpy` again, with 2 callers. `xor_block`, `E::sum::<Chain>` and `keccak_cell_lanes` were cheap and are leaves for `keccak_hash`, `verify_bus_balance`, `flushes_keccak`.
- **Rejected**: the task's literal order (memmove next); spending the remaining budget on one function with two callers.

## Invariants of the whole change
- No existing file changed but `notes/total-correctness.md` (two bullets added, nothing removed): `git diff e8794dc66a --name-status` lists 11 added `.lean` files and `M formal/rv64mc/notes/total-correctness.md`; `git diff e8794dc66a -- formal/rv64mc/notes | grep -c '^-[^-]'` -> 0.
- No `sorry`, `admit`, `axiom`, `native_decide`, `bv_decide`, `implemented_by`, `maxHeartbeats` added: `git diff e8794dc66a | grep -cE '^\+.*(sorry|axiom |native_decide|bv_decide|admit|maxHeartbeats|implemented_by)'` -> 0.
- No em or en dash in any new file or the notes: `grep -cP "\x{2014}|\x{2013}"` -> 0 for each.
- Lines at most 120 characters in the new `.lean` files (`awk 'length > 120'` empty after the last fix).
- The only build artifact outside the repo's own modules: `lake build RiscvZkvm.Rv64.Logic.MemRegionWriteWide` (the riscv-zkvm package module CopyT imports for `extractByte_replaceHalfword`/`Word32`, not built before in this worktree; `.lake/packages` only gained its olean).

## Rows for `notes/total-status.md`
| idx | function | instr | total contract | module | Table | open hypotheses |
|---|---|---|---|---|---|---|
| 223 | `compiler_builtins::mem::memcpy` | 127 | `MemcpySpecT` (bytes copied, frame) | Proof/Runtime/MemcpyT `total` | Table/MemT `memcpyT` | env |
| 224 | `compiler_builtins::mem::memset` | 38 | `MemsetSafeT` (existing) | Proof/Runtime/MemsetT `total` | Table/MemT `memsetT` | env |
| 225 | `compiler_builtins::mem::memmove` | 268 | `MemmoveSpecT` stated | Proof/Runtime/MemmoveT | - | no proof |
| 123 | `verifier::hash::xor_block` | 430 | `XorBlockSafeT` (safety, writes the state) | Proof/Hash/XorBlockT `total` | Table/HashT `xorBlockT` | env |
| 34 | `E::sum::<Chain<IntoIter<E>, IntoIter<E>>>` | 32 | `SumChainSafeT` (safety, no writes) | Proof/Field/SumChainT `total` | Table/FieldSumT `sumChainT` | env |
| 208 | `verifier::layout::keccak_cell_lanes` | 59 | `CellLanesSafeT` (safety, writes sret) | Proof/Layout/KeccakCellLanesT `total` | Table/LayoutT `keccakCellLanesT` | env |
| 114 | `verifier::hash::keccak_f` | 391 | - | draft only (runW1b/KeccakFT.draft.lean) | - | not proved |

## Not done
- **`memmove` (225)**: statement only. Obstacle: size (forward copy re-proved over its own template, backward copy with a suffix invariant `Inv` mirror and reverse partial loads). `CopyT`'s byte lemmas and `slot_copy_from` apply; `Fx.src` would need its disjointness replaced by "a byte read at or after position `j` is not among `[dst, dst + j)`" (true for a forward copy with `dst ≤ src`).
- **`keccak_f` (114)**: a draft (`KeccakFSafeT`, not committed) steps the prologue and the call to `memcpy` (side goals left: the table's no-wrap, disjointness, window), then `rv_autoT` hits the default heartbeat limit (`whnf`) somewhere in the 116-instruction straight line to the round loop's head. Needs: stops to cut the body, the lemma that an `env.data` word lies in `[staticLo, staticHi)` (from `Env.static_frame`, `static_data`), hypotheses `∀ k, (d + 8k, ws[k]) ∈ env.data` for the three tables, loop invariants carrying the round counter at `sp + 0x78` and the saved registers at `sp + 0x228..0x288`, and `PI[i] < 25` from the table by `decide`. Its `Table` instance also needs the wrappers 227 and 229's instances.
- No functional postcondition for `xor_block`, `E::sum`, `keccak_cell_lanes` (D4).
- The call-site claims (D2, D4) are by reading templates, not proved: they become proof obligations of the callers' total proofs.
- `MemcpySpec`'s falsity (D1) is argued, not machine-checked; no change made to it (statement changes are out of scope).

## Known risks
- **D1/D2's frame**: check that `OffStack env (regs .x2) b 1` in `CopyPostT` loses nothing a caller needs: a caller's objects at or above its `sp` are kept; bytes below its `sp` are not promised (they were not promised by `Holds`' doubleword frame either).
- **Vacuity at call sites**: `CopyPreT`'s source `OffStack` at keccak_f's static table relies on the static data lying below `stackLimit` (true by `Env.layout` once the data words are shown in `[staticLo, staticHi)`); a caller passing a pointer into its own callee frame would violate `OffStack`, which I believe never happens (Rust references point at or above the caller's `sp`).
- **`MemcpyT.Fx.src`** proves source bytes unchanged only for `k < n` with `j ≤ n` and the `disj` field; every call passes indices inside the source (look at `partial_ok`'s `src` helper and `loopB_ok`'s `hcur`, where the read index is `j + 8 - o + u`).
- **`tlit`** closes literal goals with a `decide` on `(UnOp.sext .b4).eval k#64 = k#64` for k in {2, 3, 6}: closed terms only.
- **`KeccakCellLanesT.KInv`** fixes `x14 = 27`, `x15 = 17`, `x12 = 1` (constants set before the loop and never written in it): if a reviewer finds a write to them in the loop body (labels 36-57), the invariant is wrong; the build says it is not.

## Golf

Commit 0f668b9ec7 on top of 2490caba17 (4 files, +148 -258). Skills: `lean4:golf` and `lean4:refactor` loaded. Only proof bodies, helper lemmas and tactic macros introduced by e8794dc66a..2490caba17 changed; no `def` and no statement of a deliverable (`MemcpySpecT`, `MemmoveSpecT`, `CopyPreT`, `CopyPostT`, `XorPreT`, `SumPreT`, `CellPreT`, `CellOut`, the invariants `Inv`/`DInv`/`CInv`/`BInv`/`AInv`/`KInv`, `Fx`'s fields, every `total`, every `Table` theorem) changed: `git diff 2490caba17 0f668b9ec7 | grep -E '^[-+](def|abbrev|structure) '` is empty. Spec/ and Table/ files untouched.

Check (after the last change): `cd formal/rv64mc && timeout 3600 systemd-run --user --scope -q -p MemoryMax=16G lake build Rv64mc.Spec.Runtime.MemT Rv64mc.Proof.Runtime.CopyT Rv64mc.Proof.Runtime.MemcpyT Rv64mc.Proof.Runtime.MemmoveT Rv64mc.Proof.Hash.XorBlockT Rv64mc.Proof.Field.SumChainT Rv64mc.Proof.Layout.KeccakCellLanesT Rv64mc.Table.MemT Rv64mc.Table.HashT Rv64mc.Table.FieldSumT Rv64mc.Table.LayoutT` -> `Build completed successfully (4906 jobs)`, no warning; every `#guard_msgs in #print axioms` still pins `[propext, Classical.choice, Quot.sound]`. Each file was also checked by `lake env lean` after each edit. No `sorry`/`axiom`/`native_decide`/`maxHeartbeats` added (grep count 0), no dash added, no line over 120 characters.

### G1. CopyT: `iteT`/`iteF` deleted, upstream `ite_eq_left`/`ite_eq_right` used
- **Why equivalent**: `iteT h : (if c then a else b) = a` and `iteF h : ... = b` are exactly `ite_eq_left h`/`ite_eq_right h` (core). `if_pos`/`if_neg` were tried first and are deprecated in this toolchain in favour of these names. Only `rw` arguments changed; six lines rewrapped to stay at 120 characters.

### G2. CopyT: `extractByte_window` deleted
- **Why equivalent**: unused (its name occurs once, at its declaration, across `Rv64mc/`), not in the header's main results.

### G3. CopyT: `slot_copy` proved from `slot_copy_from` (`lo := 0`), and moved after it
- **Why equivalent**: `slot_copy`'s statement is unchanged character for character (only its docstring now points to `slot_copy_from`, whose docstring took the description); `slot_copy_from` with `lo = 0` has hypothesis `∀ t, 0 ≤ t → t < i → ...`, given by `fun t _ => hS t`, and conclusion `∀ t, 0 ≤ t → ...`, specialised by `Nat.zero_le`. The duplicate 8-line proof is gone.

### G4. CopyT: `and2_zero`, `and4_zero` through `and_low`
- **Why equivalent**: statements unchanged. Both re-derived the low-three-bits rewrite that `and_low` (introduced by the change, unused until now) states: `and_low rfl (by decide)` rewrites `x &&& c` to `ofNat (x.toNat % 8) &&& c` for `c` in {2, 4}; `and2_zero` then rewrites `x.toNat % 4` as `x.toNat % 8 % 4` (omega) and closes the eight cases by `decide`, as `and4_zero` did.

### G5. CopyT: `extractByte_getMem` (new helper), used at the four doubleword loads in MemcpyT
- **Why equivalent**: it is `extractByte_loadVal (w := .b8)`, `loadVal .b8 M x` being `M.getMem x` by `rfl` (the step the four sites did each time with `rw [show loadVal .b8 M x = M.getMem x from rfl] at this`). Sites: `loopC_ok`'s `hv`, `lastWord_ok`'s `hv`, `loopB_ok`'s `hcur`, `prev_ok`'s `h5`.

### G6. MemcpyT: `Fx.src` takes the address `a` with `src ≤ a < src + n` instead of an offset `k < n`
- **Why equivalent**: a helper inside the proof (not a deliverable); the conclusion `bat M a = bat m a` at `a = src + k` is the old one. Five of its eight uses had to turn an address into an offset and back (`rw [show src + (a - src) = a by omega] at this`, `← Nat.add_assoc`); each is now `F.src hI (by omega) (by omega) (by omega)`. The proof is the old one at `k := a - src` followed by `Nat.add_sub_cancel'`. The defence's risk note about `Fx.src` ("only for `k < n`") now reads: only for `src ≤ a < src + n`, which every use proves by `omega` from its context.

### G7. MemcpyT: `slot_addr` moved before `lastWord_ok`, which now uses it
- **Why equivalent**: `lastWord_ok`'s `hs8` had `slot_addr`'s proof inlined verbatim with the same hypotheses (`hx2`, `F.room`).

### G8. MemcpyT: `fx_facts F hI` macro for the five entry lines repeated in 11 parts
- **Why equivalent**: `set_option hygiene false` so that it introduces the same names (`hsw`, `hdw` unfolded, `hW`, `hcode`) the parts had, from the same terms; `words_ok` (which had only three of the lines) is untouched. A `local macro`.

### G9. MemcpyT: `ret_ok`'s 13 `by simpa [updReg_apply] using h…` replaced by `simpa [AbiRegs, updReg_apply, hx2] using ha.2`
- **Why equivalent**: the same goal (`AbiRegs top regs` at the return's register file), closed by the same simp set over all conjuncts at once instead of conjunct by conjunct.

### G10. MemcpyT: `· tnorm; exact hX` runs replaced by `any_goals (tnorm; assumption)` in `lastByte_ok` and `bit0_ok` (twice)
- **Why equivalent**: proof-irrelevant `Prop` goals; each closed goal is closed by a hypothesis, as before; the remaining goals keep their explicit proofs. Tried in `loopA_ok` too: `assumption` hit the recursion limit there, so `loopA_ok` keeps its explicit bullets (only its `have e …; rw [e] at hI'; exact hI'` became `rwa [show … by omega] at hI'`).

### G11. MemcpyT: the bit tests' negations
- **Why equivalent**: `fun h => hc ((andN_zero _).2 h)` is `mt (andN_zero _).2 hc` (8 sites); `have hc_1 : ¬ (8 - o) % 2 = 0 := fun h => hc_1 ((and1_zero _).2 (by rw [h5]; exact h))` is `rw [and1_zero, h5] at hc_1`, the form the same proof already used for the positive cases (14 sites). The hypothesis obtained has the same type and name.

### G12. `tlit`, `regs_ok`, `abi_ok` (twice: SumChainT, KeccakCellLanesT) made `local macro`
- **Why equivalent**: same expansion inside their files. Before, the two identical global `abi_ok` declarations would clash in a module importing both proofs.

### G13. KeccakCellLanesT: deduplicated branches
- **Why equivalent**: `loop_ok` ended with three bullets that ran the same `exact back (hne hc_1) ⟨…⟩ (hK4 _ _ _ _)`, the first after `rv_symT hp stop [78]`; now `on_goal 1 => rv_symT hp stop [78]` then `all_goals exact …` with the same term. Likewise `total`'s two `refine loop_ok …` bullets. `⟨rfl × 13⟩` for `AbiRegs` at entry is `AbiRegs.refl rfl` (the existing `Core/Repr.lean` lemma, whose proof is that tuple). In SumChainT `AbiRegs.refl rfl` failed to elaborate (the register file is a metavariable at that point), so SumChainT keeps the tuple; only a stray blank line removed there.

### Not done
- `partial_ok`'s six `have ho4 : … := by have := BitVec.le_def.1 hc_1; rw [h16] at this; exact this` and `endPartial_ok`'s case bullets: left, a shared helper would need the branch's facts as arguments and would not be shorter.
- SumChainT `total`'s two pairs of identical branches: `any_goals exact` over goals at other program counters would be less direct; left.

## Amendments, round 1

Head after this round: 41e90ff126 (11 commits over e8794dc66a, not pushed). Check, after the commit's changes: `cd formal/rv64mc && timeout 3600 systemd-run --user --scope -q -p MemoryMax=16G lake build Rv64mc.Spec.Runtime.MemT Rv64mc.Proof.Runtime.CopyT Rv64mc.Proof.Runtime.MemcpyT Rv64mc.Proof.Runtime.MemmoveT Rv64mc.Proof.Hash.XorBlockT Rv64mc.Proof.Field.SumChainT Rv64mc.Proof.Layout.KeccakCellLanesT Rv64mc.Table.MemT Rv64mc.Table.HashT Rv64mc.Table.FieldSumT Rv64mc.Table.CellLanesT` -> `Build completed successfully (4906 jobs).`, no warning or error lines (the two changed modules alone: `Built Rv64mc.Proof.Layout.KeccakCellLanesT (26s)`, `Built Rv64mc.Table.CellLanesT (3.5s)`, 4792 jobs). No statement, `def` body or proof changed: one docstring, one file rename with its namespace, one notes sentence.

### R1-1 (add/add conflicts with formal/rv64mc-total-w2a): fixed for `Table/LayoutT.lean`; deferred to integration for `MemcpyT.lean`
- **Changed**: `Table/LayoutT.lean` renamed to `Table/CellLanesT.lean`, namespace `Rv64mc.Table.LayoutT` -> `Rv64mc.Table.CellLanesT` (theorem now `Rv64mc.Table.CellLanesT.keccakCellLanesT`, its `#guard_msgs` updated); the notes' file list updated. No module imported the old name (`grep -rn LayoutT` over `formal/rv64mc` outside `.lake`: only the file itself and the notes). This contradicts D5's file list (`LayoutT.lean (208)`): the instance for 208 is now in `CellLanesT.lean`.
- **Evidence**: `git merge-tree --write-tree --name-only 41e90ff126 formal/rv64mc-total-w2a` now reports one conflict, `MemcpyT.lean`; the merged tree holds both the sibling's `Table/LayoutT.lean` (no `keccakCellLanes` in it) and this branch's `Table/CellLanesT.lean`.
- **Deferred (`MemcpyT.lean`)**: the sibling's file is its cherry-pick `9f641f34ad` of this branch's statement commit, and is byte-identical to this branch's `5cd0a65a88` version (`git diff --stat 5cd0a65a88 formal/rv64mc-total-w2a -- …/MemcpyT.lean` is empty). This branch's file descends from it, so the resolution at integration is "take this branch's" with nothing lost. Renaming here would not help: the sibling's `MemmoveT`/`MemWrappersT` and this branch's `Table/MemT` import `Rv64mc.Proof.Runtime.MemcpyT` for `MemcpySpecT`, so the module name must stay. Avoiding the conflict would need a change on the sibling branch (dropping its cherry-pick or rebasing it onto this branch), which is outside this worktree.

### R1-2 (D4 says one call site of `keccak_cell_lanes`): fixed (defence text only)
- **Correction of D4**: there are two call sites in `FlushesKeccak` (template labels 186-189: `x10 = x2 + 0x60`, `x11 = 0`, call at 189; labels 190-194: `x10 = x2 + 0x200`, `x11 = 1`, call at 194; `Gen/Tmpl/Verifier/Layout/FlushesKeccak.lean` lines 445-463).
- **`CellPreT` at both**: `flushes_keccak`'s frame is `0x4e0` bytes (line 69, `x2 += 0xfffffffffffffb20`; restored by `+0x4e0` at line 807), and its `sp` is 16-aligned and in the stack window, so `x2 + 0x60` and `x2 + 0x200` are 8-aligned and `0x200 + 416 = 0x3a0 ≤ 0x4e0` keeps both 416-byte arrays inside the frame, in the stack window. `x11` is not read by `CellPreT`. By reading the template, as D4's other call-site claims; not machine-checked.

### R1-3 (`KInv` docstring): fixed
- **Changed**: `Proof/Layout/KeccakCellLanesT.lean` line 55, "`t` entries after the first done" -> "`k` entries left after this one", matching `loop_ok`'s docstring and `KInv`'s `x10 = dst + 0x38 + 32 * (11 - k)`.

### R1-4 (defence header names head 2490caba17, 9 commits): fixed (here)
- **Correction of the header**: the reviewed head was 0f668b9ec7 (the golf commit, 10 commits over e8794dc66a), as the Golf section said; the header was written before the golf commit. The head after this round is 41e90ff126, 11 commits. Earlier entries are not edited.

### R1-5 (notes do not state the consequence of D1, nor that it is unchecked): fixed
- **Changed**: `notes/total-correctness.md`, the `Spec/Runtime/MemT.lean` bullet, adds: "So `MemcpySpec` and `MemmoveSpec` are false at the image, and the partial `Table` theorems that take `memcpy (223)` as a hypothesis (`status.md`) are vacuous; this argument is by reading the templates (the slot stores `sd [sp+8]` and the narrow stores into it, never restored) and is not machine-checked."
- **Evidence**: the commit's diff of the notes (1 line). D1's argument itself is unchanged and still unchecked.
