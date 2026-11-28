module

public import NativeRustcVmArm.Bus.AccumulateSide.Vals

/-!
# `accumulate_side`: a callee's stack, the point

A callee's stack below the frame (`stackBelow_toNat`), the point in a state of the body
(`pt_eq`), a call writing only its stack as `St.call` takes it (`changes_call`).
-/

namespace NativeRustcVmArm.Bus.AccumulateSide

open NativeRustcArm NativeRustcArm.Sym
open NativeVm.Model NativeRustcVmArm.Ring NativeRustcVm.Bus NativeRustcVm.Layout
open LeanVM.Protocol.Verifier (Placement)

public section

variable [Host] {m0 : MachineData} {L : LayoutW} {rows : Array Nat}
  {bl : List NativeRustcVm.Data.Block} {Fm : Array (Array FormW)} {SL : BusLayoutW}

theorem sp_ge (h : Pre L rows bl Fm SL m0) : 12800 ≤ m0.regs.SP.toNat := by
  have := h.stack.2.1; rw [N_eq] at this; exact this

/-- A callee's stack below the frame. -/
theorem stackBelow_toNat (h : Pre L rows bl Fm SL m0) {st : MachineData}
    (hfr : Fr m0 F N slots keep (outs m0) st) {N' : Nat} (hle : F + N' ≤ N) :
    (stackBelow st N').toNat = m0.regs.SP.toNat - (F + N') := by
  rw [stackBelow_eq hfr.sp (by have := h.stack.2.1; omega)]
  exact base_toNat (by have := h.stack.2.1; omega)

/-- The point in a state of the body is the entry's. -/
theorem pt_eq (h : Pre L rows bl Fm SL m0) {st : MachineData}
    (hfr : Fr m0 F N slots keep (outs m0) st) :
    slice st (stackArg m0 40) (stackArg m0 48) = ptA m0 :=
  Bus.Fr.slice_eq hfr h.stack h.pt fun _ hj ↦
    NativeRustcVm.Apart.not_inRange_add (NativeRustcVm.Apart.symm h.fPt) h.pt.1.2 h.formsOk.1.2 hj

omit [Host] in
/-- A call's frame of no outputs as `St.call` takes it. -/
theorem changes_call {st m' : MachineData} {N' : Nat} (hc : Changes st m' N' 0 0) :
    SameOutside st.dmem m'.dmem (fun q ↦ InRange (stackBelow st N') N' q ∨
      InRange (base m0 F + BitVec.ofNat 64 0) 0 q ∨ outs m0 q) :=
  NativeRustcVm.SameOutside.mono hc fun q hq ↦ hq.elim
    (fun h ↦ by unfold InRange at h; omega) .inl

end

end NativeRustcVmArm.Bus.AccumulateSide
