/-
  LeanVM.Guest.CoreMode.Fn.shared_selector_tables.Fam

  `shared_selector_tables`'s own residual families (`CoreMode/FnReg.lean`): its `len = q^4·r` split from hinted bits.
-/

module

public import LeanVM.Guest.CoreMode.CoreRes
public meta import LeanVM.Guest.CoreRef
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«shared_selector_tables»

namespace LeanVM.Guest.CoreMode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- `shared_selector_tables`' `len = q^4·r`, `q = q_g@1·q_g@2~3·q_g@3~3·q_g@4~3` and `r = r_g = r_g~3·r_g~7`
(`EndExecCoreSplit`). -/
def spSst : SplitC :=
  ⟨[(val% «shared_selector_tables» "q_g@1", 1), (val% «shared_selector_tables» "q_g@2~3", 1), (val% «shared_selector_tables» "q_g@3~3", 1),
    (val% «shared_selector_tables» "q_g@4~3", 1)], [(val% «shared_selector_tables» "r_g~3", 1), (val% «shared_selector_tables» "r_g~7", 1)], val% «shared_selector_tables» "r_g", 5, 4, 16⟩

end

end LeanVM.Guest.CoreMode

namespace LeanVM.Guest.CoreMode.Own.shared_selector_tables

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **Its family**: the residuals its split gives (`splitRes`). -/
noncomputable def fams : List (String × (Fn → CRes → Bool)) := [(name% «shared_selector_tables», fun _ r ↦ splitRes spSst [] r)]

end

end LeanVM.Guest.CoreMode.Own.shared_selector_tables
