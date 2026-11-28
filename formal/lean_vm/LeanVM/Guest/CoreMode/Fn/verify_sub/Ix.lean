/-
  LeanVM.Guest.CoreMode.Fn.verify_sub.Ix

  `verify_sub`'s own residuals over the blocks its dispatches write (`fn/verify_sub.py`'s `ix_fam`): `index_side`'s
  `below[0, w + 1)` and `one_plus_suffixes`' `corners[0, n + 1)` (`armblock`), and the index point read below the
  link width.
-/

module

public import LeanVM.Guest.CoreMode.CoreRes
public meta import LeanVM.Guest.CoreRef
public import LeanVM.Guest.Data.NameStrings

namespace LeanVM.Guest.CoreMode.Own.verify_sub

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- `g_w·g` as `index_side`'s dispatch names it: `g_log_mem = [108]·g`, `g_w = [460]·g_log_mem`. -/
def ixGw : CCell := ⟨[(108, 1), (460, 1)], 2⟩

/-- `g_w·g` through the dispatch's selector `g_w·g^-19` (`795` the word `g^-19`): `[108]·[460]·[795]·g^21`. -/
def ixGwSel : CCell := ⟨[(108, 1), (460, 1), (795, 1)], 21⟩

/-- `g_n·g`, `g_n = kb[2]·[412]`. -/
def ixGn : CCell := ⟨[(115, 1), (412, 1)], 1⟩

/-- `gmv·g` through `open_stacked`'s size selector `gmv·g^-16` (`488` the word `g^-16`): `[485]·[488]·g^17`. -/
def ixGmv : CCell := ⟨[(485, 1), (488, 1)], 17⟩

/-- **Its residuals over the dispatches' blocks**: `k < e(g_w)`, `k ≤ 18` (the index point `r[g^k]`); `k < e(g_w·g)`,
`k ≤ 19`, and `e(g_log_mem) < e(g_w·g)` (`below`'s reads, `below = ⟨[13], 1, 0, g_w·g⟩`); under arm `j ≤ 5` of
`index_side`'s and `link_terminal`'s dispatches (selectors `796`, `2893`, each `g_w·g^-19`), `k < e(g_w·g)`,
`k ≤ 19 + j`; `e(kb[2 + t]) < e(g_n·g)`, `t < 6` (`corners[kb[2 + t]]`, `corners = ⟨[18], 1, 0, g_n·g⟩`), also as
`k < e(g_n·g)`, `k ≤ j`, under arm `j` of a dispatch on `kb[2 + t]` (`table_point`'s, which names it `g^j`);
`e(gmv) < e(gmv·g)` (`open_stacked`'s size selector); a trivial equation (`kb[7]` named by its own base, `RES_EQ`). -/
def ixFam : CRes → Bool
  | .lt (.num k) (.val v) => Nat.beq v 409 && Nat.ble k 18
  | .lt (.num k) (.mono c) => (decide (c = ixGw) || decide (c = ixGwSel)) && Nat.ble k 19
  | .lt (.val v) (.mono c) =>
      ((decide (c = ixGwSel) || decide (c = ixGw)) && Nat.beq v 101) ||
        (decide (c = ixGn) && Nat.ble 115 v && Nat.ble v 120) || (decide (c = ixGmv) && Nat.beq v 485)
  | .under g r => match g, r with
    | [.arm x j], .lt (.num k) (.mono c) =>
        ((Nat.beq x 796 || Nat.beq x 2893) && decide (c = ixGw) && Nat.ble j 5 && Nat.ble k (19 + j)) ||
          (Nat.ble 115 x && Nat.ble x 120 && decide (c = ixGn) && Nat.ble j 24 && Nat.ble k j)
    | _, _ => false
  | .eq a b => decide (a = b)
  | _ => false

end

end LeanVM.Guest.CoreMode.Own.verify_sub
