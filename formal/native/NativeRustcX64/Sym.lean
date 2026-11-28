module

public import NativeRustcX64.Sym.Sound
public import NativeRustcX64.Sym.Simp
public import NativeRustcX64.Sym.Run
public import NativeRustcX64.Sym.Tactic

/-!
# The verified symbolic executor for Kraken's x86-64

`Sym.exec ds S` runs a basic block on a symbolic state (`NativeRustcX64.Sym.Exec`);
`Sym.exec_sound` makes its result a fact about the machine (`NativeRustcX64.Sym.Sound`);
`sym_block` computes the result as a literal, checked by the kernel (`NativeRustcX64.Sym.Tactic`);
`Match.read` and `sym_simp` read it (`NativeRustcX64.Sym.Simp`).

Memory accesses: at a constant offset in a region (a region pointer, a label at a region's base, a
value with an alias), at a bounded index in an area no write touches (loads), or over the slots
`o + s * k` of an index `s * x` with `x < B` (`SState.slots`, loads and stores; a store writes each
slot, `ite (x = k) v old`). Facts a proof adds to a state, at its start or between two parts of a
block: `Match.withBound`, `Match.withAlias` (a computed pointer), `Match.withReg` (a register's
value re-expressed, e.g. a byte offset as a bounded variable times the access size). Examples:
`Sym/Test/Slots.lean`.
-/
