module

public import NativeRustcVmArm.KeccakGkr.SlotWeights.SegA

/-!
# `slot_weights`: the pieces of a segment's step

The store's address (`store_addr`), the rows kept by a call of `EW::mul` (`rows_keep_call`), the
product stored at a flat index (`store_rows`).
-/

namespace NativeRustcVmArm.KeccakGkr.SlotWeights

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model
open NativeRustcVm (Region)
open NativeRustcVm.KeccakGkr (rowsBytes weightsBytes)

public section

/-- `x << 10` as a number. -/
theorem shl10_toNat (x : BitVec 64) :
    (UnOp.apply (.shift .LSL 10) .W64 x).toNat = x.toNat * 1024 % 2 ^ 64 := by
  simp only [UnOp.apply, low_W64, ext_W64, shiftW, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

/-- `(x & 63) << 4` as a number. -/
theorem idx63_toNat (x : BitVec 64) :
    (UnOp.apply (.shift .LSL 4) .W64 (BinOp.apply .and .W64 x (BitVec.ofNat 64 63))).toNat =
      16 * (x.toNat % 64) := by
  simp only [UnOp.apply, BinOp.apply, low_W64, ext_W64, shiftW, BitVec.toNat_shiftLeft,
    BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [show (63 : Nat) % 2 ^ 64 = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    Nat.shiftLeft_eq]
  have := Nat.mod_lt x.toNat (show 2 ^ 6 > 0 by decide)
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

/-- **The store's address**: row `r` (X`row`), position `j & 63` (X`jr`) of the rows (X19). -/
theorem store_addr [Labels] (env : Env) (row jr : XReg) {a : BitVec 64} {r j n : Nat}
    (h19 : env.regs .X19 = a) (hrow : (env.regs row).toNat = r) (hj : (env.regs jr).toNat = j)
    (hn : 64 * r + j % 64 = n) :
    (storeAddr row jr).eval env = a + BitVec.ofNat 64 (16 * n) := by
  show BinOp.apply .add .W64 (BinOp.apply .add .W64 (env.regs .X19)
      (UnOp.apply (.shift .LSL 10) .W64 (env.regs row)))
    (UnOp.apply (.shift .LSL 4) .W64 (BinOp.apply .and .W64 (env.regs jr) (BitVec.ofNat 64 63))) = _
  have h1 := shl10_toNat (env.regs row)
  have h2 := idx63_toNat (env.regs jr)
  simp only [BinOp.apply, low_W64, ext_W64] at h1 h2 ⊢
  rw [h19, BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, h1, h2, hrow, hj, BitVec.toNat_ofNat]
  omega

variable {c : KeccakClaimW} {m0 st st' : MachineData}

/-- The rows kept by a callee using `n` bytes below a body's SP. -/
theorem rows_keep_call (hpre : SlotWeightsPre c m0) (hb : Body m0 st) {n : Nat}
    (hn : 176 + n ≤ slotWeightsStack) {f : Nat → EW} (h : ElemsAt st.dmem (rowsA m0) f 4096)
    (hs : SameOutside st.dmem st'.dmem (InRange (stackBelow st n) n)) :
    ElemsAt st'.dmem (rowsA m0) f 4096 := by
  have hS := hpre.1
  have hrok := rows_ok hpre
  have hap := Areas.apart_stack (pre_areas hpre) (w := ⟨rowsA m0, rowsBytes⟩) (by simp)
  exact h.keep hs (fun p hp hc ↦ NativeRustcVm.Apart.not_inRange hap hrok.2 (noWrap_stackBelow hS)
    (show InRange (rowsA m0) rowsBytes p by unfold InRange at hp ⊢; exact hp)
    (hb.stack_in hS hn hc)) (show (rowsA m0).toNat + 16 * 4096 ≤ 2 ^ 64 from hrok.2)

/-- **A product stored** at flat index `n` of the rows, the others kept. -/
theorem store_rows (hpre : SlotWeightsPre c m0) {f : Nat → EW} {n : Nat} (hn : n < 4096) {v : EW}
    (h : ElemsAt st.dmem (rowsA m0) f 4096)
    (hs : SameOutside st.dmem st'.dmem (InRange (rowsA m0 + BitVec.ofNat 64 (16 * n)) 16))
    (hv : NativeRustcVm.EWAt st'.dmem (rowsA m0 + BitVec.ofNat 64 (16 * n)) v) :
    ElemsAt st'.dmem (rowsA m0) (fun i ↦ if i = n then v else f i) 4096 :=
  ElemsAt.update h (show (rowsA m0).toNat + 16 * 4096 ≤ 2 ^ 64 from (rows_ok hpre).2) hn hs hv

end

end NativeRustcVmArm.KeccakGkr.SlotWeights
