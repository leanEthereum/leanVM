/-
  LeanVM.Guest.CoreMode.Fn.shared_selector_tables.Fam

  `shared_selector_tables`'s own residual families (`CoreMode/FnReg.lean`): its `len = q^4·r` split from hinted bits.
-/

module

public import LeanVM.Guest.CoreMode.CoreRes
public meta import LeanVM.Guest.CoreRef

namespace LeanVM.Guest.CoreMode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- `shared_selector_tables`' `len = q^4·r` (`EndExecCoreSplit`). -/
def spSst : SplitC := ⟨[(24, 1), (28, 1), (33, 1), (38, 1)], [(15, 1), (19, 1)], 20, 5, 4, 16⟩

end

end LeanVM.Guest.CoreMode

namespace LeanVM.Guest.CoreMode.Own.shared_selector_tables

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **Its family**: the residuals its split gives (`splitRes`). -/
noncomputable def fams : List (String × (Fn → CRes → Bool)) := [(name% «shared_selector_tables», fun _ r ↦ splitRes spSst [] r)]

end

end LeanVM.Guest.CoreMode.Own.shared_selector_tables
