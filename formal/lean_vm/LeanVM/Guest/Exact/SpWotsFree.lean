module

public import LeanVM.Guest.Exact.Free
import LeanVM.Guest.CoreRef

/-!
# `sp_wots`'s computed hints, pinned

`sp_wots` calls nothing and pins each computed hint locally (kernel evaluation), so every valid
tree of it is exact (`sp_wots_exactFree`).
-/

namespace LeanVM.Guest.Memory

@[expose] public section

set_option maxRecDepth 100000 in
theorem sp_wots_exactFree : ExactFreeG "sp_wots" :=
  exactFreeG_of (by decide +kernel : exactFree "sp_wots" idx% «sp_wots» = true)

end
end LeanVM.Guest.Memory
