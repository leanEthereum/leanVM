/-
  LeanVM.Guest.CoreMode.Fn.squeeze_packed.Fam

  `squeeze_packed`'s own residual family (`CoreMode/FnReg.lean`): its count's exponent bound, which bounds its promised
  runs (`fn/squeeze_packed.py`'s `sel_bound`, `fam`).
-/

module

public import LeanVM.Guest.CoreMode.CoreRes
public meta import LeanVM.Guest.CoreRef
public import LeanVM.Guest.Data.NameStrings

namespace LeanVM.Guest.CoreMode.Own.squeeze_packed

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **Its count's bound**: `e(count_g) < m`, `64 ≤ m < capE` (value `6`, `g^p`, `p < 64`: `B1.Link.MeaningSP`). -/
def countFam : CRes → Bool
  | .lt (.val x) (.num m) => Nat.beq x 6 && Nat.ble 64 m && Nat.blt m capE
  | _ => false

/-- **Its family**: its count's bound (`countFam`). -/
noncomputable def fams : List (String × (Fn → CRes → Bool)) := [(name% «squeeze_packed», fun _ r ↦ countFam r)]

end

end LeanVM.Guest.CoreMode.Own.squeeze_packed
