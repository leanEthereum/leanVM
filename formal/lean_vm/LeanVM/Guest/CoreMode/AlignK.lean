module

public import LeanVM.Guest.Bridge.AlignDefs

/-!
# The alignment pass's states from the pairing's

A long function's alignment pass (`Bridge.alignOk`) is checked in windows (`Bridge.winOk`, `Bridge.alignOk_of_chain`)
from the core route's pairing states at the same offsets (`CoreMode.winOkH`, `scripts/core-mode/pair.py`): the pairing
holds its cursors normalized to the next heap event (`PairCtx.nL`), the alignment to the next flow hint or jump
(`Bridge.normZ`), so the alignment's state is the pairing's with its cursors normalized further (`alignKOf`). Nothing
is proved of it: each window is decided at the states it names.
-/

namespace LeanVM.Guest.CoreMode

open LeanVM.Guest.Bridge

@[expose] public section

/-- A cursor of `body` as the alignment pass holds it: normalized (`normZ`), or itself where that fails. -/
noncomputable def alignCur (X : AlignCtx) (body : List Core.Stmt) (c : Cur) : Cur :=
  ((normZ X.fuel (zipOf body c.1 c.2)).map Zip.key).getD c

/-- A pairing state as the alignment pass's: its cursors normalized (`alignCur`). -/
noncomputable def alignKOf (X : AlignCtx) (body : List Core.Stmt) (K : KSt) : KSt :=
  ⟨K.i, K.nd, K.cur.map (alignCur X body), K.pend.map fun p ↦ (p.1, alignCur X body p.2),
    K.tabs.map fun t ↦ (t.1, alignCur X body t.2.1, t.2.2)⟩

end

end LeanVM.Guest.CoreMode
