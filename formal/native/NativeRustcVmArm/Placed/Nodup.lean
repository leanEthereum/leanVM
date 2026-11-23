module

public import NativeRustcVmArm.Placed.Basic
public import NativeRustcVmArm.Code.Vm

/-!
# The labels of `leanvm_verify`'s program are distinct

One kernel check over the program: the labels' numbers (`key`) pairwise distinct (about a minute).
-/

namespace NativeRustcVmArm.Placement

set_option Elab.async false

/-- **The program's labels are pairwise distinct.** -/
public theorem labels_nodup : (labels Vm.code).Nodup :=
  nodup_of_keys (by decide +kernel)

end NativeRustcVmArm.Placement
