/-
  LeanVM.Guest.CoreMode.Fn.ring_rows.Fam

  `ring_rows`'s own residual families (`CoreMode/FnReg.lean`): its `count = q^8·r` split from hinted bits.
-/

module

public import LeanVM.Guest.CoreMode.CoreRes
public meta import LeanVM.Guest.CoreRef
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«ring_rows»

namespace LeanVM.Guest.CoreMode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- `ring_rows`' `count = q^8·r`, `q = q_g@1·q_g@2~3·q_g@3~3` and `r = r_g@3 = r_g@1·r_g@2~3·r_g@3~3`
(`EndExecCoreSplit`). -/
def spRg : SplitC :=
  ⟨[(val% «ring_rows» "q_g@1", 1), (val% «ring_rows» "q_g@2~3", 1), (val% «ring_rows» "q_g@3~3", 1)],
    [(val% «ring_rows» "r_g@1", 1), (val% «ring_rows» "r_g@2~3", 1), (val% «ring_rows» "r_g@3~3", 1)], val% «ring_rows» "r_g@3", val% «ring_rows» "count_g", 8, 8⟩

end

end LeanVM.Guest.CoreMode

namespace LeanVM.Guest.CoreMode.Own.ring_rows

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **Its family**: the residuals its split gives (`splitRes`). -/
noncomputable def fams : List (String × (Fn → CRes → Bool)) := [(name% «ring_rows», fun _ r ↦ splitRes spRg [] r)]

end

end LeanVM.Guest.CoreMode.Own.ring_rows
