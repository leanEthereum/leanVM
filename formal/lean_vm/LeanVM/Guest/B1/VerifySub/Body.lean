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

theorem vs_body : (fn% «verify_sub»).body = vsT := stmtsEqb_sound (by decide +kernel)

theorem vs_params : (fn% «verify_sub»).params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5] := rfl

theorem find_vs : coreProgram.find? "verify_sub" = some fn% «verify_sub» :=
  coreProgram_find?_at (j := idx% «verify_sub») rfl

end
end LeanVM.Guest.B1.VerifySub
