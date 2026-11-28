/-
  LeanVM.Guest.CoreMode.Fn.verify_sub.GwInv

  `verify_sub`'s own residual over the windows-table index `g_w·g^-1` (`fn/verify_sub.py`'s `gw_inv_fam`): the read
  `g_squares[g_w·g^-1]` on its `flag == 1` arm lies in the exponent tables `g_squares[0, 2226)`.
-/

module

public import LeanVM.Guest.CoreMode.CoreRes
public meta import LeanVM.Guest.CoreRef
public import LeanVM.Guest.Data.NameStrings

namespace LeanVM.Guest.CoreMode.Own.verify_sub

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **The index `g_w·g^-1`** as the solver names it: `[108]·[460]·[472]·g`, `g_log_mem = [108]·g` (value `101`),
`g_w = [460]·g_log_mem` (value `409`), `[472] = g^-1` (`INV_GEN`, on the arm). -/
def gwInvC : CCell := ⟨[(108, 1), (460, 1), (472, 1)], 1⟩

/-- **`e(g_w·g^-1) < m`** on the `flag == 1` arm (`zero 471`, `471 = flag + 1`), `24 ≤ m < capE`
(`g_w = g^w`, `w ≤ 24`). -/
def gwInvFam : CRes → Bool
  | .under g (.lt (.mono c) (.num m)) =>
      g.contains (.zero 471) && decide (c = gwInvC) && Nat.ble 24 m && Nat.blt m capE
  | _ => false

end

end LeanVM.Guest.CoreMode.Own.verify_sub
