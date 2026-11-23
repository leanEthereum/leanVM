module

public import NativeRustcArm.Code.Common.Memset.Names
public import NativeRustcArm.Code.Xmss.XmssVerify.Names

public import NativeRustcArm.XmssVerify.Node
public import NativeRustcArm.XmssVerify.Turn
public import NativeRustcArm.XmssVerify.Fold
meta import NativeRustcArm.Code.Xmss.XmssVerify
public meta import NativeRustcArm.XmssVerify.Turn

/-!
# `xmss_verify`: the bottom path loop's blocks

Block 8, a turn's head (`x24` the level `z`, `x27` the path node `z` at `2492 + 16 z`, the
index `var 0 = 16 z`): the current node at `4954` and the sibling stored as the children at
`5016` in the order bit `z` of the key index `x23` says (`c8`), the address at `5392` (`lo` the
key index shifted by `z + 1`, the level `z + 1`, the type `3`), `memset` of the hasher at `5408`.
Block 14, a turn's tail: the hash's first 16 bytes to the current node, `x27` to the next path
node, back to block 8 until `z + 1 = 16`. Their values (`c8_eval`, `lvl8_toNat`,
`lo8_toNat`).
-/

namespace NativeRustcArm.Xmss.XmssVerify

open NativeRustcArm.Sym NativeRustcArm LeanVM.Protocol.KeccakHash NativeRustc

set_option Elab.async false

@[expose] public section

/-- The registers block 8 knows. -/
def knownB : List (XReg × Sym) :=
  [(.X21, .ptr 0 5392), (.X25, .ptr 0 4896), (.X26, .ptr 0 5016), (.X19, .ptr 0 4976),
    (.X27, .bin .add .W64 (.ptr 0 2492) (.var 0)), (.X28, .lit 1), (.X20, .lit 3)]

sym_block b8_exec := exec b8 (initL knownB)

/-- The symbolic state after block 8. -/
def st8 : SState := ((exec b8 (initL knownB)).getD (initL knownB, .fall)).1

theorem b8_exec' : exec b8 (initL knownB) = some (st8, .call NativeRustcArm.Common.Memset.entryLabel) := by
  rw [b8_exec]
  rfl

/-- Bit `z` of the key index is zero: `tst x9, x23` with `x9 = 1 << x24`. -/
def c8 : SBool :=
  .cmp .eq .W64 (.bin .and .W64 (.bin .lslv .W64 (.lit 1) (.reg .X24)) (.reg .X23)) (.lit 0)

/-- The level `x24 + 1`. -/
def lvl8 : Sym := .bin .add .W64 (.reg .X24) (.lit 1)

theorem st8_facts : st8.reg .X0 = some (.ptr 0 5408) ∧ st8.reg .X1 = some (.lit 0) ∧
    st8.reg .X2 = some (.lit 344) ∧ st8.sp = .ptr 0 0 ∧ (initL knownB).reg .X29 = some (.reg .X29) ∧
    st8.reg .X29 = some (.reg .X29) ∧ writesIn st8 [0] = true ∧
    (∀ x, 5776 ≤ x → x < 5872 → findWrite 0 x st8.mem = none) ∧ st8.reg .X24 = some lvl8 ∧
    (∀ p ∈ knownB, st8.reg p.1 = some p.2) ∧
    (∀ r ∈ [XReg.X22, .X23], st8.reg r = some (.reg r)) ∧
    firstOverlap 0 0 8 st8.mem = none ∧ firstOverlap 0 2448 32 st8.mem = none ∧
    firstOverlap 0 2492 2400 st8.mem = none := by
  decide +kernel

theorem st8_children :
    (∀ t < 8, findWrite 0 (5016 + t) st8.mem =
      some (.ite c8 (.load 0 4954 8) (.loadx 0 2492 (.var 0) 8), t)) ∧
    (∀ t < 8, findWrite 0 (5024 + t) st8.mem =
      some (.ite c8 (.load 0 4962 8) (.loadx 0 2500 (.var 0) 8), t)) ∧
    (∀ t < 8, findWrite 0 (5032 + t) st8.mem =
      some (.ite c8 (.loadx 0 2492 (.var 0) 8) (.load 0 4954 8), t)) ∧
    (∀ t < 8, findWrite 0 (5040 + t) st8.mem =
      some (.ite c8 (.loadx 0 2500 (.var 0) 8) (.load 0 4962 8), t)) := by
  decide +kernel

theorem st8_addr :
    (∀ t < 4, findWrite 0 (5392 + t) st8.mem = some (.bin .lsrv .W64 (.reg .X23) lvl8, t)) ∧
    (∀ t < 2, findWrite 0 (5396 + t) st8.mem = some (lvl8, t)) ∧
    (∀ t < 1, findWrite 0 (5398 + t) st8.mem = some (.un (.ubfm 16 31) .W32 lvl8, t)) ∧
    (∀ t < 1, findWrite 0 (5399 + t) st8.mem = some (.lit 3, t)) ∧
    (∀ t < 8, findWrite 0 (5400 + t) st8.mem = some (.lit 0, t)) := by
  decide +kernel

sym_block b14_exec := exec b14 (stF0 [(.X25, .ptr 0 4896)])

/-- The symbolic state after block 14. -/
def st14 : SState := ((exec b14 (stF0 [(.X25, .ptr 0 4896)])).getD (stF0 [], .fall)).1

/-- Another turn: `x24 ≠ 16`. -/
def c14 : SBool := .not (.cmp .eq .W64 (.reg .X24) (.lit 16))

theorem b14_exec' :
    exec b14 (stF0 [(.X25, .ptr 0 4896)]) = some (st14, .cond c14 NativeRustcArm.Xmss.XmssVerify.label_4) := by
  rw [b14_exec]
  rfl

theorem st14_facts : st14.sp = .ptr 0 0 ∧ st14.reg .X29 = some (.reg .X29) ∧
    writesIn st14 [0] = true ∧ (∀ x, 5776 ≤ x → x < 5872 → findWrite 0 x st14.mem = none) ∧
    (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X26, .X28],
      st14.reg r = some (.reg r)) ∧
    st14.reg .X25 = some (.ptr 0 4896) ∧
    st14.reg .X27 = some (.bin .add .W64 (.reg .X27) (.lit 16)) ∧
    (∀ t < 8, findWrite 0 (4954 + t) st14.mem = some (.load 0 5408 8, t)) ∧
    (∀ t < 8, findWrite 0 (4962 + t) st14.mem = some (.load 0 5416 8, t)) ∧
    firstOverlap 0 0 8 st14.mem = none ∧ firstOverlap 0 2448 32 st14.mem = none ∧
    firstOverlap 0 2492 2400 st14.mem = none := by
  decide +kernel

end

/-! ## Values -/

public section

variable [Labels] {env : Env}

theorem c8_eval {z e : Nat} (hz : z < 16) (he : e < 2 ^ 64)
    (h24 : env.regs .X24 = BitVec.ofNat 64 z) (h23 : env.regs .X23 = BitVec.ofNat 64 e) :
    c8.eval env = decide (e >>> z &&& 1 = 0) := by
  have := bit_eq (BitVec.ofNat 64 e) z (by omega)
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt he] at this
  rw [← this]
  simp only [c8, SBool.eval, CmpOp.apply, Sym.eval, BinOp.apply, low_W64, ext_W64, h24, h23,
    RegWidth.bits, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show z < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show z < 64 by omega)]

theorem lvl8_toNat {z : Nat} (hz : z < 16) (h24 : env.regs .X24 = BitVec.ofNat 64 z) :
    (lvl8.eval env).toNat = z + 1 := by
  simp only [lvl8, Sym.eval, BinOp.apply, low_W64, ext_W64, h24, BitVec.toNat_add,
    BitVec.toNat_ofNat]
  omega

theorem lo8_toNat {z e : Nat} (hz : z < 16) (he : e < 2 ^ 64)
    (h24 : env.regs .X24 = BitVec.ofNat 64 z) (h23 : env.regs .X23 = BitVec.ofNat 64 e) :
    ((Sym.bin .lsrv .W64 (.reg .X23) lvl8).eval env).toNat = e >>> (z + 1) := by
  have h1 := lvl8_toNat hz h24
  simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, h23, RegWidth.bits]
  rw [h1, Nat.mod_eq_of_lt (show z + 1 < 64 by omega)]
  exact (BitVec.toNat_ushiftRight (x := BitVec.ofNat 64 e) (i := z + 1)).trans
    (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt he])

end

end NativeRustcArm.Xmss.XmssVerify
