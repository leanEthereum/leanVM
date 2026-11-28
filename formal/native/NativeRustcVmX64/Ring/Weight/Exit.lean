module

public import NativeRustcVmX64.Ring.Weight.Basic
public import NativeRustcVmX64.Ring.Weight.Facts

/-!
# `ring_weight`'s epilogue (x86-64)

`b25` from `tE` with the output (`rsO`, writable): the tag `1` and the total stored, the pushed
registers restored, back at the entry's return address (`exitW`). `Goal` is what `ring_weight`'s
contract asks of the state it returns in.
-/

namespace NativeRustcVmX64.Ring.Weight

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Ring NativeVm.Model NativeRustcVm.Ring
open NativeRustcVmX64.Vm.RingWeight
open NativeRustcVmX64.Transcript (after wordAt_write)

@[expose] public section

/-- What the contract asks of the state `ring_weight` returns in. -/
abbrev Goal [Host] (m0 : MachineData) : MachineState → Prop :=
  fun st ↦ st.pc = retOf m0 ∧ rspOf st.data = rspOf m0 + 8#64 ∧ RingWeightPost m0 st.data

/-- The output's window. -/
abbrev rsO (m0 : MachineData) : List (BitVec 64 × Nat) := [(reg m0 .rdi + BitVec.ofNat 64 0, 24)]

end

public section

variable {m0 : MachineData}

theorem layO (h : RingWeightPre m0) : Lay m0 672 NW (rsO m0) :=
  lay1 h.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2.1 (by omega)

variable [Host] {k : Nat}

/-- **The epilogue**: the total `T` stored as `some T`, back at the return address. -/
theorem exitW (hp : Placed code k) (h : RingWeightPre m0) {vals : Nat → BitVec 64} {T : EW}
    (hv : ∀ i < 6, vals i = vv m0 0 0 0 0 i)
    (h20 : vals 20 = c0 T) (h21 : vals 21 = c1 T)
    (hT : T = ringWeight (rL m0) (qL m0) (cL m0)) {I : MachineData → Prop} {st : MachineState}
    (hA : At m0 k NativeRustcVmX64.Vm.RingWeight.b25Offset (rsO m0) oWr (tE (sz1 24) oAl) vals I st) :
    Eventually (step1 Host.exe) (Goal m0) st := by
  obtain ⟨d, pc⟩ := st
  obtain ⟨hpc, hB, -⟩ := hA
  simp only at hpc hB
  subst hpc
  obtain ⟨hrun, hwr, hsp, hbx, hbp, h12, h13, h14, h15, hw⟩ := f_b25
  refine exitStep (layO h) hB (b25_in_code.trans hp.1 (by simp [b25])) hrun hwr hsp ?_
    fun st hm hret hrsp hso hsv ↦ .done _ ⟨hret, hrsp, ?_, ?_, hsv⟩
  · intro r hr
    cases r <;> simp only [calleeSaved, Bool.false_eq_true] at hr
    · exact ⟨_, hbx, hv 5 (by decide)⟩
    · exact ⟨_, hbp, hv 0 (by decide)⟩
    · exact ⟨_, h12, hv 4 (by decide)⟩
    · exact ⟨_, h13, hv 3 (by decide)⟩
    · exact ⟨_, h14, hv 2 (by decide)⟩
    · exact ⟨_, h15, hv 1 (by decide)⟩
  · rw [← hT]
    have w0 := wordAt_write hm (r := 1) (o := 0) rfl (by decide) fun u hu ↦ by rw [Nat.zero_add]; exact (hw u hu).1
    have w8 := wordAt_write hm (r := 1) (o := 8) rfl (by decide) fun u hu ↦ (hw u hu).2.1
    have w16 := wordAt_write hm (r := 1) (o := 16) rfl (by decide) fun u hu ↦ (hw u hu).2.2
    have e0 : NativeRustcVm.WordAt st.data.dmem (reg m0 .rdi + BitVec.ofNat 64 0 + BitVec.ofNat 64 0)
        1 := w0
    have e8 : NativeRustcVm.WordAt st.data.dmem (reg m0 .rdi + BitVec.ofNat 64 0 + BitVec.ofNat 64 8)
        (UInt64.ofBitVec (vals 20)) := w8
    have e16 : NativeRustcVm.WordAt st.data.dmem
        (reg m0 .rdi + BitVec.ofNat 64 0 + BitVec.ofNat 64 16) (UInt64.ofBitVec (vals 21)) := w16
    rw [NativeRustcVm.addr_add_zero, NativeRustcVm.addr_add_zero] at e0
    rw [NativeRustcVm.addr_add_zero, h20] at e8
    rw [NativeRustcVm.addr_add_zero, h21] at e16
    refine ⟨e0, NativeRustcVm.ewAt_iff.mpr ⟨e8, ?_⟩⟩
    rw [show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, NativeRustcVm.addr_add_add]
    exact e16
  · intro q hq
    refine hso q fun h' ↦ hq (h'.elim .inr fun ⟨i, e, _, he, hin⟩ ↦ .inl ?_)
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at he
      subst he
      have hin' : InRange (reg m0 .rdi + BitVec.ofNat 64 0) 24 q := hin
      rwa [NativeRustcVm.addr_add_zero] at hin'
    | succ i => simp at he

end

end NativeRustcVmX64.Ring.Weight
