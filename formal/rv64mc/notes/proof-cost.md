# What a per-function proof costs, and why

Measured on the shared 32-core host (load 25 to 35 from other sessions), CPU seconds: for one declaration, Lean's profiler (tactic execution plus kernel type checking); for a file, `/usr/bin/time` on `lake env lean` less the imports (about 5.4 s). Wall time is not comparable under the host's load. The benchmark is `<E as Mul>::mul` (61 instructions, 18 memory operations, 5 calls) over its relocatable template, with phase 0's contract unchanged (`Rv64mc/Tactic/Bench/EMulAuto.lean`; the `lsym` proof it replaces is phase 0's `Probe/EMul.lean`).

## The cost curve on `E::mul`

| step | CPU-s | per instruction |
| --- | --- | --- |
| phase 0: `lsym`, then the callees' frames by `simp` with discharger `bv_omega` | 91 | 1.5 |
| the same, `bv_omega` replaced by literal-offset lemmas (`Tactic/Addr.lean`) | 34 | 0.56 |
| `rv_auto` (`Tactic/Sym.lean`): the tactic states each next state, register reads by reduction | 0.8 (0.15 tactic, 0.65 kernel) | 0.013 |
| `rv_auto`, every equation by name or by `decide`, the register file as `rf`, the instruction from the body's suffix | 0.9 (0.5 tactic, 0.4 kernel) | 0.015 |

The proof text of `E::mul` is five lines: `rv_auto hp with [hL] using [hcl, hrd]`, then `simp only [spec]` and `ac_rfl` under `rd` for the two functional equations. Nothing about frames, the stack pointer, saved registers or memory is left. The last row costs as much as the third on `E::mul` but is the one that scales (below).

`eq_eval` (40 instructions, a loop, `Bench/EqEvalAuto.lean`): the contract and its loop lemma in 2.6 CPU-s, the file's arithmetic and fold lemmas included.

## Where the cost went

- `lsym` (25 s, 0.4 s per instruction): every step is a macro `first` over the rules (label, operation, goto, branch, return, then four forms per contract), each looking the instruction up by `rfl`, and an operation's result is computed by `simp [lsym_simp, <the with-list>, <every hret>] at he` with the whole default simp set, the lemma list elaborated again at each step. Most of it is that `simp` (15 s of 28 in a profile of `lsym` alone).
- The callees' frames (about 60 s, 28 s of it kernel): `simp (disch := bv_omega)` over the loads after the calls. `bv_omega` starts with `simp only [bv_toNat] at *`, so each address comparison translated the whole context (five postconditions and the memory terms, 15,000 characters of hypotheses) and `omega` abstracted it into an auxiliary theorem: 60 auxiliary theorems of 0.45 s kernel each. This is machine-checked's hardening finding that `bv_omega` after `lsym` hangs, in milder form.

## What fixed it

- **The tactic states the next state.** `rv_sym` reads the body once and applies one rule per instruction form by name (`Tactic/Steps.lean`, e.g. `step_set v R' … (hv : e.eval regs = v) (hR : updReg regs rd v = R') (h : SafeN … R' m)`), with the value, register file and memory it computed itself. No `simp` runs on the goal or a hypothesis.
- **Every equation is an instance of a named lemma or a closed fact the kernel decides by evaluation.** A register read is `rf_get_<r>` and a write `rf_set_<r>` (the register file is an `rf` of its 32 values, `Tactic/RegFile.lean`, so a read costs the same after any number of writes), an expression's value `eval_*` and `bin_*`, an address `t + c1 + c2 = t + (c1 + c2)` by `add_assoc` with `c1 + c2 = c` by `decide`. The first version proved reads by reduction (`Eq.refl` through an `updReg` chain): on the image the kernel then hit deep recursion checking `0 + 0xffffffffffffffff`, and grew to 16 GB unfolding a `mulhu` value (into `Nat.div`'s well-founded recursion) when its lazy unfolding chose the value's side.
- **The instruction comes from the body's suffix**, `fd.body.drop pc = i :: rest`, carried from step to step (`drop_get`, `drop_next`), instead of `body[pc]?` by `rfl`, which the kernel evaluates from the start of the body: 0.1 s per lookup at instruction 850 of `verify_bus_balance`, quadratic over a function.
- **Addresses are a base plus a literal offset**, and the facts about them are lemmas whose side condition is a Boolean on the literals and the base's bounds that the kernel evaluates (`Addr.offLe`, `offLtLt`, `litLe`): two offsets of one base are different addresses, an offset is below another, an address at or above a bound is not a store below it. The bounds are the precondition's (`0x10000#64 ≤ top`, `top ≤ 0x7fff…`), found in the context, or a hypothesis `t ≤ a` for a pointer. No `omega` runs on a goal that holds the program's state.
- **A callee's memory is a frame hypothesis**, `∀ a, lo ≤ a → m'.getMem a = m.getMem a` (the ABI's last conjunct, split out of the postcondition), which a load passes through when its address is at or above `lo`, and which the closer chains to prove the function's own frame.
- **Facts become state.** The precondition's and each postcondition's equations about registers are written into the register file (`absorbFacts`), so that a later read is a lemma instance, not a rewrite with a hypothesis.
- **Loop heads are stops**: the target of a backward jump ends a path, where a loop lemma applies, instead of the path going round once.

## On the image

`rv_sweep` over each of the 230 templates the generator writes (`Rv64mc/Gen`): from the entry, and from every loop head with nothing known of the state; every path stepped to a return, a loop head or an instruction no rule covers. Every callee goes through a contract that promises nothing (`Post := True`), or, in the last row, the ones whose name says they do not return (panics, `handle_error`, failed checks) through one whose postcondition is `False`, as their real contracts will be.

| run | functions | instructions | steps | tactic CPU-s | kernel CPU-s | per step |
| --- | --- | --- | --- | --- | --- | --- |
| first `rv_auto`, from the entry only | 219 of 230 | 14,739 | 83,114 | 152 | 427 | 7.0 ms |
| final, on the same 219 functions | 219 | 14,739 | 51,244 | 70 | 83 | 3.0 ms |
| final, entry and loop heads, every function | 230 | 20,500 | 142,214 | 211 | 142 | 2.5 ms |

The 11 the first run lost ran out of heartbeats or of `simp`'s recursion depth; in the final run every one passes (the largest, `verify_bus_balance`, with a larger heartbeat budget in this single-declaration probe). The whole image's stepping costs 354 CPU-s, 17 ms per instruction of code. Per function the median is 0.34 s, 187 functions cost under 1 s and 223 under 10 s; the costliest are those with many paths (`verify_bus_balance` 69 s, `walk` 40 s with 25,282 steps for 763 instructions, `table_sumcheck` 30 s). Every path ended at a return or a loop head (2,111 loop-head ends), except at the image's 2 `Lext`: no instruction form, call or link fact went unhandled.

## What remains manual, and the limits

- **Functional postconditions.** `rv_auto` leaves `R .x10 = Model.f args` with the register's value computed; closing it is the Model's algebra (`ac_rfl` for `E::mul`).
- **Loops.** A loop is a lemma at its head, proved by induction with `rv_intro` (the invariant's facts into the register file), `rv_sym` over the body and `rv_close`; what is left is the invariant's arithmetic at the back edge. For `eq_eval` that is eight goals (two pointer increments, the fold's step twice, four "the element is above the frame"), one lemma application each, and the exit test, one lemma (`end_iff`, by `omega` on a clean goal). The invariant here is the word-level fold (`stepW` over the slices' limbs); tying it to `Model.eqEvalRust` over `E` is a Model lemma. A library of loop schemas (fold over a slice, counted loop) would state the invariant from the Model's fold and close these goals.
- **Path explosion.** Branches are not merged: every path is stepped to its end, so code after `k` independent branches is stepped up to `2^k` times (`table_sumcheck`: 461 instructions, 15,302 steps). The kernel shares identical proofs of identical suffixes, the tactic does not. Cut points (a stop and a lemma at a join), or two states merged into `if c then … else …` values, would bound it.
- **Memory.** Doubleword accesses (7,673 of the image's 8,063 loads and stores) at base-plus-literal addresses are automatic. A byte, halfword or word store is kept as `setByte`/`setHalfword`/`setWord32`, which a later load does not see through (byte-in-doubleword reasoning; 231 `lbu`, 122 `sb`, 37 others). Two addresses of different bases are different only by a hypothesis (`a ≠ b`, or `t ≤ a` against a store below `t`): a heap and slice vocabulary (regions, a bump allocator's watermark) is the next step.
- **Tactic time** is now about as large as the kernel's: `mkAppM` and type inference per proof node, and instance synthesis (about 10%). Prebuilt operator heads and instances would roughly halve it.
- **Not handled:** self-calls (14, a contract's own induction), `Lext` (2 system calls), indirect calls with more than one candidate (none in the canonical image).

## For machine-checked

- `lsym` should state the next state (a rule per operation form with the result as a parameter, as `Steps.lean` does) instead of `simp … at he` with the default simp set, and should not pass the context's hypotheses to `simp`.
- Keep `bv_omega` out of dischargers: its `simp at *` makes every auxiliary proof carry the whole context. Address facts on base-plus-literal forms with kernel-evaluated side conditions are two orders of magnitude cheaper.
- Reduction-free proofs: equation lemmas for `Expr.eval`, `BinOp.eval` and `updReg` by name, `decide` for literals. On this machine model the kernel's lazy unfolding of a value is a hazard (deep recursion on large literals, `Nat.div` under `mulhu`).
- A body lookup that is not linear in the program counter: the suffix carried from step to step, as here, or a lookup proved equal to `getElem?`.
- A memory vocabulary at the Lprog level: the ABI's frame as `∀ a, top ≤ a → m'.getMem a = m.getMem a` (as `Abi` here), its use through a load and its closure under composition, and stack room in contracts (a caller shows its callee's room: `0x10030 ≤ top` for `eq_eval`, whose callee needs `0x10000 ≤ top - 48`).
- Loop heads from the control flow (backward jump targets) rather than from a path coming back, which needs the function index to be a literal and steps the body once more.
- `SafeN.block` was not needed: with one rule per instruction and no `simp`, a step costs a few milliseconds, kernel included.
