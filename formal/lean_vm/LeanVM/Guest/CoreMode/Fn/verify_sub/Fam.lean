/-
  LeanVM.Guest.CoreMode.Fn.verify_sub.Fam

  `verify_sub`'s own residual families (`CoreMode/FnReg.lean`): its values' exponent bounds where they bound its
  callees' runs.
-/

module

public import LeanVM.Guest.CoreMode.CoreRes
public import LeanVM.Guest.CoreMode.Fn.verify_sub.Chal
public import LeanVM.Guest.CoreMode.Fn.verify_sub.Ix
public import LeanVM.Guest.CoreMode.Fn.verify_sub.GwInv
public import LeanVM.Guest.CoreMode.Fn.verify_sub.Stream
public meta import LeanVM.Guest.CoreRef
public import LeanVM.Guest.Data.NameStrings

namespace LeanVM.Guest.CoreMode.Own.verify_sub

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **Its values' exponent bounds** `(v, n)`, `e(v) < n`, where they bound its callees' runs: its link width `g_w`
(value `409`, `shape[g]`, `g^w`, `19 ≤ w ≤ 24`, by `assert log(g_w·g^-BYTECODE_LOG) < LINK_W_ARMS`); the Keccak
table's height word `kb[2 + TABLE_KECCAK]` (value `120`, `g^h`, `h ≤ 24`, `SizesOk.heights24`); its tallest height `g_n`
(value `408`, `shape[1]`, `g_n / kb[2]` range checked below `2^24`); `g_log_mem` (value `101`, `logMemory ≤ 30`) and
`gmv` (value `485`, `stackLog ≤ 30`) (`SizesOk`). -/
def vsBounds : List (ℕ × ℕ) := [(409, 25), (120, 25), (408, 49), (101, 31), (485, 31)]

/-- **`e(v) < m`**, `(v, n)` one of `vsBounds`, `n ≤ m < capE`. -/
def gwFam : CRes → Bool
  | .lt (.val x) (.num m) => vsBounds.any (fun b ↦ Nat.beq b.1 x && Nat.ble b.2 m) && Nat.blt m capE
  | _ => false

/-- **Its families.** -/
def fams : List (String × (Fn → CRes → Bool)) :=
  [(name% «verify_sub», fun _ r ↦ gwFam r || chalFam r || ixFam r || gwInvFam r || streamFam r)]

end

end LeanVM.Guest.CoreMode.Own.verify_sub
