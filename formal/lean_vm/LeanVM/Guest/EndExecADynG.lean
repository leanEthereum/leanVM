/-
  LeanVM.Guest.EndExecADynG

  `DynPowA` on the deployed guest: its loops pass their check (`progOk_guest`), so every dynamic
  `HeapBuf`'s size is a power of `g` at every honest instance, whatever the flags.
-/

module

public import LeanVM.Guest.EndExecADyn
public import LeanVM.Guest.CoreMode.Fam.ProgOkG

namespace LeanVM.Guest.EndExec

public section

/-- **Every dynamic `HeapBuf`'s size a power of `g`**, on the deployed guest. -/
theorem dynPowA_guest {al : String → Bool} {D : Ref → RefD} : DynPowA (layB al) D := dynPowA_of progOk_guest

end

end LeanVM.Guest.EndExec
