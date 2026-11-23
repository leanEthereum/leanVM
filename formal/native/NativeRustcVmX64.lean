module

public import NativeRustcVmX64.Basic
public import NativeRustcVmX64.Placed
public import NativeRustcVmX64.Mem
public import NativeRustcVmX64.Rodata.Keccak
public import NativeRustcVmX64.Rodata.Items
public import NativeRustcVmX64.Top.Assembly

/-!
# The rustc-compiled leanVM verifier on x86-64

`VmVerifier.verify_correct` proves the pinned rustc's raw `leanvm_verify` assembly (`rustc/vm`), ingested as `NativeRustcVmX64.Vm.code`, against Kraken's x86-64 semantics and the verifier model, as `NativeRustcVmArm` does on AArch64. Every function contract is discharged by its blocks and proved callees. The theorem retains program placement, input representation, alignment, stack, memory-separation, and `GotAt` assumptions: the reached `memcpy` and `memset` slots contain their labels' addresses and are disjoint from the stack and protected areas. It has no unproved callee contracts. The build fails if an axiom footprint grows beyond Lean's three standard axioms.
-/

/-- info: 'NativeRustcVmX64.VmVerifier.verify_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.VmVerifier.verify_correct

/-- info: 'NativeRustcVmX64.Placement.labels_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Placement.labels_nodup

/-- info: 'NativeRustcVmX64.Placement.placed_LeanvmVerify' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Placement.placed_LeanvmVerify

/-- info: 'NativeRustcVmX64.Placement.placed_Memcpy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Placement.placed_Memcpy

/-- info: 'NativeRustcVmX64.Placement.placed_Memset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Placement.placed_Memset

/-- info: 'NativeRustcVmX64.Mem.memcpy_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Mem.memcpy_spec

/-- info: 'NativeRustcVmX64.Mem.memset_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Mem.memset_spec

/-- info: 'NativeRustcVmX64.Rodata.labels_rodata' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Rodata.labels_rodata

/-- info: 'NativeRustcVmX64.Rodata.data_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Rodata.data_eq

/-- info: 'NativeRustcVmX64.RodataAt.rcAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.RodataAt.rcAt

/-- info: 'NativeRustcVmX64.RodataAt.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.RodataAt.mono

/-- info: 'NativeRustcVmX64.RodataAt.mono_of_dmem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.RodataAt.mono_of_dmem

/-- info: 'NativeRustcVmX64.bytesOf_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.bytesOf_eq

/-- info: 'NativeRustcVmX64.noWrap_stackBelow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.noWrap_stackBelow

/-- info: 'NativeRustcVmX64.Mapped.of_saved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Mapped.of_saved
