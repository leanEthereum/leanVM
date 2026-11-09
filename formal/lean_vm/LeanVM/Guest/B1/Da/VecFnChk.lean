/-
  LeanVM.Guest.B1.Da.VecFnChk

  `da_vector`'s body, checked by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Da.VecFn

namespace LeanVM.Guest.B1.Da

@[expose] public section

set_option maxRecDepth 100000 in
theorem vec_ok : vecOk = true := by decide +kernel

end
end LeanVM.Guest.B1.Da
