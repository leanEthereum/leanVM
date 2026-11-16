/-
  LeanVM.Guest.EndExecRGkrC

  The layer loop `verify_bus_gkr_loop0`'s certificate's residuals at its honest frames.
-/

module

public import LeanVM.Guest.EndExecRGkr
public import LeanVM.Guest.Pack.«P11».ModeCert

/-!
# The layer loop's certificate

`resLy_alignA`: `ly_resCert` on the certificate, its residuals in `Res.lyResB` at their offsets, its
entries, and the positions at the calls of `gkr_rounds__L2` and `__L1` reaching them, by kernel
evaluation.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Guest LeanVM.Guest.Core

public section

/-- **The layer loop's residuals at its honest frames.** -/
theorem resLy_alignA : ResCert Bridge.alignA Fn.«verify_bus_gkr_loop0».modeCert :=
  ly_resCert (by decide +kernel) ⟨by decide +kernel, by decide +kernel⟩ (by decide +kernel) (by decide +kernel)

end

end LeanVM.Guest.EndExec
