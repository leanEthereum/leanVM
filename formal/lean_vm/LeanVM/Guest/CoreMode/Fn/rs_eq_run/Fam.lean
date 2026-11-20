/-
  LeanVM.Guest.CoreMode.Fn.rs_eq_run.Fam

  `rs_eq_run`'s own residual families (`CoreMode/FnReg.lean`): its `count = q^8·r` split from hinted bits.
-/

module

public import LeanVM.Guest.CoreMode.CoreRes
public meta import LeanVM.Guest.CoreRef

namespace LeanVM.Guest.CoreMode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- `rs_eq_run`'s `count = q^8·r` (`EndExecCoreSplit`). -/
def spRs : SplitC := ⟨[(27, 1), (31, 1), (36, 1)], [(13, 1), (17, 1), (22, 1)], 23, 3, 8, 8⟩

end

end LeanVM.Guest.CoreMode

namespace LeanVM.Guest.CoreMode.Own.rs_eq_run

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **Its family**: the residuals its split gives (`splitRes`). -/
noncomputable def fams : List (String × (Fn → CRes → Bool)) := [(name% «rs_eq_run», fun _ r ↦ splitRes spRs [] r)]

end

end LeanVM.Guest.CoreMode.Own.rs_eq_run
