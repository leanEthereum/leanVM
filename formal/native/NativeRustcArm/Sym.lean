module

public import NativeRustcArm.Sym.Sound
public import NativeRustcArm.Sym.Simp
public import NativeRustcArm.Sym.Tactic
public import NativeRustcArm.Sym.Run

/-!
# The verified symbolic executor for Kraken's AArch64

`Sym.exec ds S` runs a basic block on a symbolic state (`NativeRustcArm.Sym.Exec`);
`Sym.exec_sound` makes its result a fact about the machine (`NativeRustcArm.Sym.Sound`);
`sym_block` computes the result as a literal, checked by the kernel (`NativeRustcArm.Sym.Tactic`);
`Match.read` and `sym_simp` read it (`NativeRustcArm.Sym.Simp`).

A block proof: an environment `env` (often `Sym.Env.ofMachine m regions`, with its regions'
bases), a start state (`Sym.init`, its `Match` by `Sym.match_init`), `sym_block h := exec ds S`,
then `Sym.exec_sound hk h hwf hm` and the facts of the final `Match` and `PcOk`. A loop's state at
its head takes the loop's variables as atoms (`Sym.var`, bounded by `SState.bounds` where it
indexes memory) or rebases the regions per iteration.

Memory accesses: at a constant offset in a region (a region pointer, a label at a region's base, a
value with an alias), at a bounded index in an area no write touches (loads), or over the slots
`o + s * k` of an index `s * x` with `x < B` (`SState.slots`, loads and stores; a store writes each
slot, `ite (x = k) v old`). Facts a proof adds to a state, at its start or between two parts of a
block: `Match.withBound`, `Match.withAlias` (a computed pointer), `Match.withReg` (a register's
value re-expressed, e.g. a byte offset as a bounded variable times the access size). Examples:
`Sym/Test/Slots.lean`.
-/
