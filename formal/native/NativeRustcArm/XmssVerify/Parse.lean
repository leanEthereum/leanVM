module

public import NativeRustcArm.XmssVerify.Copy
public import NativeRustcArm.XmssVerify.Model
meta import NativeRustcArm.Code.Xmss.XmssVerify

/-!
# `xmss_verify`: parsing the signature

Block 3 writes the key at `2448` and a slice descriptor `(frame + 48, 2400)`
at `5408`, then reads the bottom layer into `2492`. Block 4 reads the top
layer into `3692` using the advanced descriptor. `Parsed` records the
unchanged message and key alongside both decoded layers.
-/

namespace NativeRustcArm.Xmss.XmssVerify

open NativeRustcArm.Sym NativeRustcArm LeanVM.Protocol.KeccakHash

set_option Elab.async false

@[expose] public section

/-- At block 5: the message, the key and the layers in the frame. -/
structure Parsed (w : Nat → UInt64) (m₀ m : MachineData) : Prop where
  common : Common m₀ m
  x19 : (m.regs.getXReg .X19).toBitVec = ad m₀ (fb + 2492)
  x20 : (m.regs.getXReg .X20).toBitVec = ad m₀ (fb + 2448)
  x24 : m.regs.getXReg .X24 = w 8
  x23 : (m.regs.getXReg .X23).toNat = (w 8).toNat % 2 ^ 32
  msg : BytesAt m.dmem (ad m₀ (fb + 8)) (msgB w)
  pk : BytesAt m.dmem (ad m₀ (fb + 2448)) (pkB w)
  bottom : BytesAt m.dmem (ad m₀ (fb + 2492)) (bottomL w).memBytes
  top : BytesAt m.dmem (ad m₀ (fb + 3692)) (topL w).memBytes
  x21 : (m.regs.getXReg .X21).toBitVec = ad m₀ (fb + 5392)
  x22 : (m.regs.getXReg .X22).toBitVec = ad m₀ (fb + 3692)

/-- The frame as region 0, SP its base. -/
def stF0 (known : List (XReg × Sym)) : SState := init [(5872, true)] (.ptr 0 0) known

sym_block b3_exec := exec b3 (stF0 [])

/-- The symbolic state after block 3. -/
def st3 : SState := ((exec b3 (stF0 [])).getD (stF0 [], .fall)).1

theorem st3_facts : st3.reg .X0 = some (.ptr 0 2492) ∧ st3.reg .X1 = some (.ptr 0 5408) ∧
    st3.reg .X19 = some (.ptr 0 2492) ∧
    st3.reg .X20 = some (.ptr 0 2448) ∧ st3.reg .X24 = some (.reg .X24) ∧
    st3.reg .X23 = some (.reg .X23) ∧ st3.reg .X29 = some (.reg .X29) ∧ st3.sp = .ptr 0 0 ∧
    writesIn st3 [0] = true ∧ (∀ x, 5776 ≤ x → x < 5872 → findWrite 0 x st3.mem = none) ∧
    firstOverlap 0 8 32 st3.mem = none ∧ firstOverlap 0 44 2404 st3.mem = none := by decide +kernel

theorem st3_x21 : st3.reg .X21 = some (.reg .X21) := by decide +kernel

theorem st3_pk : ∀ j < 4, ∀ t < 8, findWrite 0 (2448 + 8 * j + t) st3.mem =
    some (.reg ([XReg.X8, .X9, .X10, .X11].getD j .X0), t) := by decide +kernel

theorem st3_cursorData : ∀ t < 8, findWrite 0 (5408 + t) st3.mem = some (.reg .X19, t) := by
  decide +kernel

theorem st3_cursorLength : ∀ t < 8, findWrite 0 (5416 + t) st3.mem = some (.lit 2400, t) := by
  decide +kernel

sym_block b4_exec := exec b4 (stF0 [(.X19, .ptr 0 2492)])

/-- The symbolic state after block 4. -/
def st4 : SState := ((exec b4 (stF0 [(.X19, .ptr 0 2492)])).getD (stF0 [], .fall)).1

theorem st4_facts : st4.reg .X0 = some (.ptr 0 3692) ∧ st4.reg .X1 = some (.ptr 0 5408) ∧
    st4.mem = [] ∧ st4.sp = .ptr 0 0 ∧
    st4.reg .X19 = some (.ptr 0 2492) ∧
    (∀ r ∈ [XReg.X20, .X21, .X23, .X24, .X29], st4.reg r = some (.reg r)) ∧
    writesIn st4 [0] = true ∧
    (∀ x, 5776 ≤ x → x < 5872 → findWrite 0 x st4.mem = none) := by decide +kernel

theorem st4_x22 : st4.reg .X22 = some (.ptr 0 3692) := by decide +kernel

end

end NativeRustcArm.Xmss.XmssVerify
