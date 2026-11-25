module

public import NativeRustcVmArm.Spec.Top
public import NativeVm.Entry.Restrict

namespace NativeRustcVmArm.VmVerifier

open NativeRustcArm NativeVm NativeRustcVm.Top

@[expose] public section

/-- The Rust regions, ABI stack and loader's read-only data. -/
def readRegions [Labels] (m : MachineData) (a : NativeVm.Entry.Areas) (L n : Nat) :
    List (BitVec 64 × Nat) :=
  (entryRegions m.regs.X0 a L n).map (fun r ↦ (r.addr, r.size)) ++
    (stackBelow m leanvmVerifyStack, leanvmVerifyStack) ::
      NativeRustcVm.Data.Item.all.map (fun t ↦ (rodataAddr t, t.bytes.length))

noncomputable def restrictedState [Labels] (m : MachineData) (a : NativeVm.Entry.Areas) (L n : Nat) :
    MachineData :=
  { m with dmem := NativeRustc.restrictMemory m.dmem (readRegions m a L n) }

theorem restricted_pre [Labels]
    {bytes : List UInt8} {bytecode : List UInt64} {pub : Vector UInt64 4} {a : NativeVm.Entry.Areas}
    {m : MachineData}
    (hin : NativeVm.Entry.EntryPre m.dmem m.regs.X0 a bytes bytecode pub)
    (hstack : StackOk m leanvmVerifyStack) (hrod : RodataAt m leanvmVerifyStack) :
    let confined := restrictedState m a bytes.length bytecode.length
    NativeVm.Entry.EntryPre confined.dmem confined.regs.X0 a bytes bytecode pub ∧
      StackOk confined leanvmVerifyStack ∧ RodataAt confined leanvmVerifyStack := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · apply hin.restrict <;> simp [readRegions, entryRegions]
  · exact ⟨hstack.1, hstack.2.1,
      NativeRustcVm.Mapped.restrict hstack.2.2 (by simp [readRegions, stackBelow, restrictedState])⟩
  · intro t
    refine ⟨(hrod.bytesAt t).restrict ?_, hrod.noWrap t, hrod.apart t⟩
    apply List.mem_append_right
    apply List.mem_cons_of_mem
    exact List.mem_map.mpr ⟨t, by cases t <;> decide, rfl⟩

end

end NativeRustcVmArm.VmVerifier
