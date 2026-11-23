/-
  LeanVM.Guest.B1.VerifySub.Body

  `verify_sub`'s body is the template `vsT`, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.VerifySub.Template
public import LeanVM.Guest.B1.Common.Find
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_sub»

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Guest.Core LeanVM.Guest.B1

@[expose] public section

theorem vs_body : (fn% «verify_sub»).body = vsT := stmtsEqb_sound (by decide +kernel)

theorem vs_params : (fn% «verify_sub»).params = [.n (val% «verify_sub» "pi_0"), .n (val% «verify_sub» "pi_1"), .n (val% «verify_sub» "seed_0"), .n (val% «verify_sub» "seed_1"), .n (val% «verify_sub» "g_squares"), .n (val% «verify_sub» "defer_out")] := rfl

theorem find_vs : coreProgram.find? name% «verify_sub» = some fn% «verify_sub» :=
  coreProgram_find?_at (j := idx% «verify_sub») rfl

end
end LeanVM.Guest.B1.VerifySub
