module

public import NativeRustcX64.Mem.Memcpy
public import NativeRustcX64.Mem.Memset

/-!
# rustc's x86-64 `memcpy` and `memset` meet their contracts

`NativeRustcX64.Mem.Memcpy.memcpy_spec`, `NativeRustcX64.Mem.Memset.memset_spec`, with Lean's three
axioms only.
-/

/--
info: 'NativeRustcX64.Mem.Memcpy.memcpy_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NativeRustcX64.Mem.Memcpy.memcpy_spec

/--
info: 'NativeRustcX64.Mem.Memset.memset_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NativeRustcX64.Mem.Memset.memset_spec
