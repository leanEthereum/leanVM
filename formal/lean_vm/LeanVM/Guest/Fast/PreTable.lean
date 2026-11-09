module

public import LeanVM.Guest.Fast.PreSig
public import LeanVM.Guest.Glob
public meta import LeanVM.Guest.KernelLit

/-!
# The functions' preconditions, a literal table

`preTable`: entry `j` is function `j`'s precondition as its test reads it (`fnPreOf (glob.sig j)`,
`Fast/PreSig.lean`), for the guest's `885` functions, written out by the kernel (`kernel_lit`:
`preTable_eq`, the kernel's check that it is the table computed from the certificates). The
decoder's compiled precondition test reads this literal (`Cost/Decoder/PreTable.lean`), not the
certificates.

A slow module (the kernel reads every certificate's tables), importing only the definitions it
evaluates (`Fast/Firewall.lean` checks it).
-/

namespace LeanVM.Guest.Fast

open LeanVM.Guest.Check

@[expose] public section

/-- **The functions' preconditions**, entry `j` function `j`'s. -/
kernel_lit preTable : Array (Option FnPre) :=
  ((List.range nFns).map fun j ↦ fnPreOf (glob.sig j)).toArray

/-- Entry `j < 885` of the table is function `j`'s precondition. -/
theorem preTable_getD {j : ℕ} (hj : j < nFns) : preTable.getD j none = fnPreOf (glob.sig j) := by
  rw [← preTable_eq]
  simp [Array.getD, hj]

end

end LeanVM.Guest.Fast
