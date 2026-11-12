/-
  LeanVM.Guest.B1.VerifySub.Body

  `verify_sub`'s body is the template `vsT`, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.VerifySub.Template
public import LeanVM.Guest.B1.Common.Find

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Guest.Core LeanVM.Guest.B1

@[expose] public section

theorem vs_body : Data.core18.body = vsT := stmtsEqb_sound (by decide +kernel)

theorem vs_params : Data.core18.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5] := rfl

theorem find_vs : coreProgram.find? "verify_sub" = some Data.core18 :=
  coreProgram_find?_at (j := 18) rfl

end
end LeanVM.Guest.B1.VerifySub
