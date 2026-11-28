module

public import NativeRustcArm.Mem.Memcpy
public import NativeRustcArm.Mem.Memset

/-!
# The axioms of `memcpy`'s and `memset`'s contracts
-/

/--
info: 'NativeRustcArm.Mem.Memcpy.memcpy_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NativeRustcArm.Mem.Memcpy.memcpy_spec

/--
info: 'NativeRustcArm.Mem.Memset.memset_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NativeRustcArm.Mem.Memset.memset_spec
