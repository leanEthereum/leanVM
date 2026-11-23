/-
  LeanVM.Guest.CoreMode.Fn.rs_eq_run.Fam

  `rs_eq_run`'s own residual families (`CoreMode/FnReg.lean`): its `count = q^8·r` split from hinted bits.
-/

module

public import LeanVM.Guest.CoreMode.CoreRes
public meta import LeanVM.Guest.CoreRef
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«rs_eq_run»

namespace LeanVM.Guest.CoreMode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- `rs_eq_run`'s `count = q^8·r`, `q = q_g@1·q_g@2~3·q_g@3~3` and `r = r_g@3 = r_g@1·r_g@2~3·r_g@3~3`
(`EndExecCoreSplit`). -/
def spRs : SplitC :=
  ⟨[(val% «rs_eq_run» "q_g@1", 1), (val% «rs_eq_run» "q_g@2~3", 1), (val% «rs_eq_run» "q_g@3~3", 1)],
    [(val% «rs_eq_run» "r_g@1", 1), (val% «rs_eq_run» "r_g@2~3", 1), (val% «rs_eq_run» "r_g@3~3", 1)], val% «rs_eq_run» "r_g@3", 3, 8, 8⟩

end

end LeanVM.Guest.CoreMode

namespace LeanVM.Guest.CoreMode.Own.rs_eq_run

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **Its family**: the residuals its split gives (`splitRes`). -/
noncomputable def fams : List (String × (Fn → CRes → Bool)) := [(name% «rs_eq_run», fun _ r ↦ splitRes spRs [] r)]

end

end LeanVM.Guest.CoreMode.Own.rs_eq_run
