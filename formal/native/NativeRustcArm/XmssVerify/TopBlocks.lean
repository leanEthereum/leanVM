module

public import NativeRustcArm.Code.Common.Memset.Names
public import NativeRustcArm.Code.Xmss.XmssVerify.Names

public import NativeRustcArm.XmssVerify.Node
public import NativeRustcArm.XmssVerify.Turn
public import NativeRustcArm.XmssVerify.Fold
meta import NativeRustcArm.Code.Xmss.XmssVerify
public meta import NativeRustcArm.XmssVerify.Turn

/-!
# `xmss_verify`: the top path loop's blocks

Block 18, a turn's head (`x20` the level `z + 1`, `x22` the path node `z` at `3692 + 16 z`, the
index `var 0 = 16 z`, the current node in `x9`, `x8`): the current node and the sibling stored as
the children at `5016` in the order bit `z` of the key index `x19` says (`c18`), the address at
`5392` (`hi` the level with the top flag), `memset` of the hasher at `5408`. Block 24, a turn's
tail: the hash's first 16 bytes to `x9`, `x8`, `x22` to the next path node, back to block 18 until
`z + 1 = 16`. Block 25: the root compared with the key's (`x0`).
-/

namespace NativeRustcArm.Xmss.XmssVerify

open NativeRustcArm.Sym NativeRustcArm LeanVM.Protocol.KeccakHash NativeRustc

set_option Elab.async false

@[expose] public section

/-- The registers block 18 knows. -/
def knownT : List (XReg × Sym) :=
  [(.X21, .ptr 0 5392), (.X25, .ptr 0 4976), (.X23, .ptr 0 5016), (.X27, .ptr 0 2448),
    (.X22, .bin .add .W64 (.ptr 0 3692) (.var 0)), (.X24, .lit 1), (.X26, .lit 3)]

sym_block b18_exec := exec b18 (initL knownT)

/-- The symbolic state after block 18. -/
def st18 : SState := ((exec b18 (initL knownT)).getD (initL knownT, .fall)).1

theorem b18_exec' : exec b18 (initL knownT) = some (st18, .call NativeRustcArm.Common.Memset.entryLabel) := by
  rw [b18_exec]
  rfl

/-- Bit `z` of the key index is zero: `tst x10, x19` with `x10 = 1 << (x20 - 1)`. -/
def c18 : SBool :=
  .cmp .eq .W64 (.bin .and .W64 (.bin .lslv .W64 (.lit 1) (.bin .sub .W64 (.reg .X20) (.lit 1)))
    (.reg .X19)) (.lit 0)

theorem st18_facts : st18.reg .X0 = some (.ptr 0 5408) ∧ st18.reg .X1 = some (.lit 0) ∧
    st18.reg .X2 = some (.lit 344) ∧ st18.sp = .ptr 0 0 ∧
    (initL knownT).reg .X29 = some (.reg .X29) ∧ st18.reg .X29 = some (.reg .X29) ∧
    writesIn st18 [0] = true ∧ (∀ x, 5776 ≤ x → x < 5872 → findWrite 0 x st18.mem = none) ∧
    (∀ p ∈ knownT, st18.reg p.1 = some p.2) ∧
    (∀ r ∈ [XReg.X19, .X20], st18.reg r = some (.reg r)) ∧
    firstOverlap 0 2448 32 st18.mem = none ∧ firstOverlap 0 3692 1200 st18.mem = none := by
  decide +kernel

theorem st18_children :
    (∀ t < 8, findWrite 0 (5016 + t) st18.mem =
      some (.ite c18 (.reg .X9) (.loadx 0 3692 (.var 0) 8), t)) ∧
    (∀ t < 8, findWrite 0 (5024 + t) st18.mem =
      some (.ite c18 (.reg .X8) (.loadx 0 3700 (.var 0) 8), t)) ∧
    (∀ t < 8, findWrite 0 (5032 + t) st18.mem =
      some (.ite c18 (.loadx 0 3692 (.var 0) 8) (.reg .X9), t)) ∧
    (∀ t < 8, findWrite 0 (5040 + t) st18.mem =
      some (.ite c18 (.loadx 0 3700 (.var 0) 8) (.reg .X8), t)) := by
  decide +kernel

theorem st18_addr :
    (∀ t < 4, findWrite 0 (5392 + t) st18.mem =
      some (.bin .lsrv .W64 (.reg .X19) (.reg .X20), t)) ∧
    (∀ t < 2, findWrite 0 (5396 + t) st18.mem = some (.reg .X20, t)) ∧
    (∀ t < 1, findWrite 0 (5398 + t) st18.mem =
      some (.un (.ubfm 16 31) .W32 (.bin .orr .W32 (.reg .X20) (.lit 8388608)), t)) ∧
    (∀ t < 1, findWrite 0 (5399 + t) st18.mem = some (.lit 3, t)) ∧
    (∀ t < 8, findWrite 0 (5400 + t) st18.mem = some (.lit 0, t)) := by
  decide +kernel

sym_block b24_exec := exec b24 (stF0 [])

/-- The symbolic state after block 24. -/
def st24 : SState := ((exec b24 (stF0 [])).getD (stF0 [], .fall)).1

/-- Another turn: `x20 + 1 ≠ 17`. -/
def c24 : SBool := .not (.cmp .eq .W64 (.bin .add .W64 (.reg .X20) (.lit 1)) (.lit 17))

theorem b24_exec' : exec b24 (stF0 []) = some (st24, .cond c24 NativeRustcArm.Xmss.XmssVerify.label_7) := by
  rw [b24_exec]
  rfl

theorem st24_facts : st24.sp = .ptr 0 0 ∧ st24.reg .X29 = some (.reg .X29) ∧ st24.mem = [] ∧
    (∀ r ∈ [XReg.X19, .X21, .X23, .X24, .X25, .X26, .X27], st24.reg r = some (.reg r)) ∧
    st24.reg .X20 = some (.bin .add .W64 (.reg .X20) (.lit 1)) ∧
    st24.reg .X22 = some (.bin .add .W64 (.reg .X22) (.lit 16)) ∧
    st24.reg .X9 = some (.load 0 5408 8) ∧ st24.reg .X8 = some (.load 0 5416 8) := by
  decide +kernel

sym_block b25_exec := exec b25 (stF0 [])

/-- The symbolic state after block 25. -/
def st25 : SState := ((exec b25 (stF0 [])).getD (stF0 [], .fall)).1

theorem b25_exec' : exec b25 (stF0 []) = some (st25, .jump NativeRustcArm.Xmss.XmssVerify.label_10) := by
  rw [b25_exec]
  rfl

theorem st25_facts : st25.sp = .ptr 0 0 ∧ st25.reg .X29 = some (.reg .X29) ∧ st25.mem = [] ∧
    keeps (stF0 []) st25 = true ∧
    st25.reg .X0 = some (.ite (.not (.ite (.cmp .eq .W64 (.reg .X9) (.load 0 2448 8))
      (.cmp .eq .W64 (.reg .X8) (.load 0 2456 8)) (.lit false))) (.lit 0) (.lit 1)) := by
  decide +kernel

end

/-! ## Values -/

public section

variable [Labels] {env : Env}

theorem c18_eval {z e : Nat} (hz : z < 16) (he : e < 2 ^ 64)
    (h20 : env.regs .X20 = BitVec.ofNat 64 (z + 1)) (h19 : env.regs .X19 = BitVec.ofNat 64 e) :
    c18.eval env = decide (e >>> z &&& 1 = 0) := by
  have := bit_eq (BitVec.ofNat 64 e) z (by omega)
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt he] at this
  rw [← this]
  have hs : (BitVec.ofNat 64 (z + 1) - BitVec.ofNat 64 1).toNat = z := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  simp only [c18, SBool.eval, CmpOp.apply, Sym.eval, BinOp.apply, low_W64, ext_W64, h20, h19,
    RegWidth.bits, hs, Nat.mod_eq_of_lt (show z < 64 by omega)]

theorem lo18_toNat {z e : Nat} (hz : z < 16) (he : e < 2 ^ 64)
    (h20 : env.regs .X20 = BitVec.ofNat 64 (z + 1)) (h19 : env.regs .X19 = BitVec.ofNat 64 e) :
    ((Sym.bin .lsrv .W64 (.reg .X19) (.reg .X20)).eval env).toNat = e >>> (z + 1) := by
  simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, h19, h20, RegWidth.bits]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show z + 1 < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show z + 1 < 64 by omega)]
  exact (BitVec.toNat_ushiftRight (x := BitVec.ofNat 64 e) (i := z + 1)).trans
    (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt he])

omit [Labels] in
/-- The address's `hi` bytes of a top node at level `z + 1`, as block 18 stores them. -/
theorem hiTop : ∀ z < 16, [UInt8.ofNat (BitVec.ofNat 64 (z + 1)).toNat,
    UInt8.ofNat ((BitVec.ofNat 64 (z + 1)).toNat / 256),
    UInt8.ofNat (UnOp.apply (.ubfm 16 31) .W32
      (BinOp.apply .orr .W32 (BitVec.ofNat 64 (z + 1)) (BitVec.ofNat 64 8388608))).toNat] =
    (u32Bytes (Xmss.layerHi 1 (z + 1).toUInt32)).take 3 := by
  decide +kernel

omit [Labels] in
/-- A 64-bit sum. -/
theorem binAdd64 (a b : BitVec 64) : BinOp.apply .add .W64 a b = a + b := by
  simp [BinOp.apply]

end

end NativeRustcArm.Xmss.XmssVerify
