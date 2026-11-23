module

public import NativeRustcVmArm.Whir.VerifyStackedOpening.Exec
public meta import NativeRustcVmArm.Code.Vm.VerifyStackedOpening
public meta import NativeRustcVmArm.Whir.Common

/-!
# `b34` in two parts

`b34` loads the `WhirW`'s address from the stack argument, then writes the `WhirW`'s head: the
argument's word and the `WhirW` need not be apart, so the load (`b34a`, from `argS`: the frame,
the argument above it) and the rest (`b34b`, from `whir2S`: the frame, the `WhirW`'s head at X6)
run in environments of their own.
-/

namespace NativeRustcVmArm.Whir.VerifyStackedOpening

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.VerifyStackedOpening

@[expose] public section

/-- `b34`'s load of the stack argument. -/
def b34a : List Directive := b34.take 1
/-- The rest of `b34`. -/
def b34b : List Directive := b34.drop 1
/-- `b34a`: the frame, the stack argument above it. -/
def argS : SState := init [(512, true), (8, false)] (.ptr 0 0) [] [] [] [(.ptr 0 512, 1, 0)]
/-- `b34b`: the frame, the `WhirW`'s head at X6. -/
def whir2S : SState := init [(512, true), (512, false)] (.ptr 0 0) [(.X6, .ptr 1 0)]

end

set_option Elab.async false

sym_block run_b34a := exec b34a argS
sym_block run_b34b := exec b34b whir2S

public section

theorem b34_split : b34 = b34a ++ b34b := (List.take_append_drop 1 b34).symm

end

end NativeRustcVmArm.Whir.VerifyStackedOpening
