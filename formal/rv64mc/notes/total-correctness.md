# Total correctness: `HaltsSafely`

`HaltsSafely image` (`Rv64mc/EndStatement.lean`): on every input of fewer than `2^16` words, the loaded image runs, every step taken by the statement's `step`, to the halting `ECALL` with `a0` in `{0, 1, 2}`. Its end theorem is `rv64_halts_of_main` (`Final/EndT.lean`), whose one hypothesis is `main`'s total contract `MainSpecT` (`Final/MainSpecT.lean`).

## The pieces

* `Rv64mc/Total/` (namespace `Lprog`, on `lprog` alone): `Ascent.Total R accept G Q s`, the inductive "every run reaches an accepting state satisfying `Q`, and every state before it satisfies `G`, steps, and neither traps nor goes `wrong`"; `Isa.Total` at Lprog; one rule per instruction (`Total.label`, `opn`, `set`, `goto`, `cond`, `call`, `tail`, `ret`, `ext`, `ext_done`, `returned`); `Total.loop` (strong induction on a measure at a loop head); `Isa.TContract`, a total contract with a stopping set `Stop` (where the callee may end the run inside the call) and the obligation `G` fixed, and `Total.call_contract`, `tail_contract`, `TContract.measure`.
* `Core/HoldsT.lean`: `stmtCtx` (every `ECALL` stops; every halt, `t0 = 0`, accepts), the obligation `WinOk` (a load or store lies in a window), `HoldsT` (`Holds`'s pre- and postcondition plus `Stop`), `HoldsT.call`.
* `Final/Transfer.lean`: `halts_of_total`, from `Isa.Total` under machine-checked's `Sim` to `Halts` over `step`, reusing `Sim.split`, `back_instr` and `trap_instr`.
* `Proof/Runtime/HaltT.lean`, `PanicsT.lean`: `Aborts` (never returns, ends the run with `a0 = 2`) for `halt` and the panic chain, the pattern for a function that does not return.

## Proving a function total

What differs from a `Holds` proof, and so what `rv_sym` needs to step `rvIsa.Total p stmtCtx (WinOk p) Q s` goals:

* A rule set of its own: the `Total.*` rules in place of `SafeN.*`, with the same continuation shape. Each takes the obligation `WinOk p s` at the state it steps from: `WinOk.of_ne hp rfl nofun` at every instruction but a load or store, `WinOk.of_set` at a register write, `WinOk.of_opn hp rfl hw` at a load or store, where `hw : opWin op regs` is `inWindow addr width = true`, a new side goal about the address.
* A load or store must give a result: `Total.opn` takes `rvIsa.opn op regs m = some (r', m')`, so SP1's check (address range, alignment, a store not over code) is a goal, where `lsym` leaves it as a hypothesis `hm` because a fault is safe for `SafeN`.
* A loop needs a measure that decreases on every iteration, not only an invariant: `Total.loop` at its head, the induction hypothesis applied where `rv_sym` stops at the head again. A recursive function: `TContract.measure` (or `Ascent.budget_induction` over a table).
* A call through `HoldsT.call` (or `Total.call_contract` with `h.contract`) has one more goal than `Holds.call`: `Q` at every halt in the callee's `Stop`. For a caller whose own `Stop` contains the callee's, it is the caller's `hstop`.
* A function that ends the run: `Total.ext_done` at the halting `Lext`, with `stmtCtx.accept` (`t0 = 0`) and `Q` there.
