module

public import NativeRustcVmX64.Placed.Basic
public import NativeRustcVmX64.Code.Vm

/-!
# The labels of `leanvm_verify`'s program are distinct

One kernel check over the program: the labels' numbers (`key`) pairwise distinct (about a minute).
-/

namespace NativeRustcVmX64.Placement

set_option Elab.async false

/-- **The program's labels are pairwise distinct.** -/
public theorem labels_nodup : (labels Vm.code).Nodup :=
  nodup_of_keys (by decide +kernel)

end NativeRustcVmX64.Placement
