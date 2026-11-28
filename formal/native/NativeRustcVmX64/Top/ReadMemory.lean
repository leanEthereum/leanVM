module

public import NativeRustcVmX64.Spec.Top
public import NativeVm.Entry.Restrict

namespace NativeRustcVmX64.VmVerifier

open NativeRustcX64 NativeVm NativeRustcVm.Top

@[expose] public section

/-- The Rust regions, ABI stack and return address, rodata, and reached GOT slots. -/
def readRegions [Labels] (m : MachineData) (a : NativeVm.Entry.Areas) (L n : Nat) :
    List (BitVec 64 × Nat) :=
  (entryRegions (ctxOf m) a L n).map (fun r ↦ (r.addr, r.size)) ++
    (stackBelow m leanvmVerifyStack, leanvmVerifyStack + 8) ::
      (rodataAreas ++ (["memcpy", "memset"] : List Label).map (fun l ↦ (gotAddr l, 8)))

noncomputable def restrictedState [Labels] (m : MachineData) (a : NativeVm.Entry.Areas) (L n : Nat) :
    MachineData :=
  { m with dmem := NativeRustc.restrictMemory m.dmem (readRegions m a L n) }

theorem restricted_pre [Labels]
    {bytes : List UInt8} {bytecode : List UInt64} {pub : Vector UInt64 4} {a : NativeVm.Entry.Areas}
    {m : MachineData}
    (hin : NativeVm.Entry.EntryPre m.dmem (ctxOf m) a bytes bytecode pub)
    (hstack : StackOk m leanvmVerifyStack) (hrod : RodataAt m leanvmVerifyStack)
    (hgot : GotAt m leanvmVerifyStack
      ((entryRegions (ctxOf m) a bytes.length bytecode.length).map (fun r ↦ (r.addr, r.size)) ++
        rodataAreas) ["memcpy", "memset"]) :
    let confined := restrictedState m a bytes.length bytecode.length
    NativeVm.Entry.EntryPre confined.dmem (ctxOf confined) a bytes bytecode pub ∧
      StackOk confined leanvmVerifyStack ∧ RodataAt confined leanvmVerifyStack ∧
      GotAt confined leanvmVerifyStack
        ((entryRegions (ctxOf confined) a bytes.length bytecode.length).map (fun r ↦ (r.addr, r.size)) ++
          rodataAreas) ["memcpy", "memset"] := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply hin.restrict <;> simp [readRegions, entryRegions]
  · exact ⟨hstack.1, hstack.2.1,
      NativeRustcVm.Mapped.restrict hstack.2.2 (by simp [readRegions, stackBelow, restrictedState, rspOf])⟩
  · intro t
    refine ⟨NativeRustcVm.BytesAt.restrict (hrod.bytesAt t) ?_, hrod.noWrap t, hrod.apart t⟩
    apply List.mem_append_right
    apply List.mem_cons_of_mem
    apply List.mem_append_left
    exact List.mem_map.mpr ⟨t, by cases t <;> decide, rfl⟩
  · refine ⟨?_, hgot.2⟩
    intro l hl
    obtain ⟨hb, hn, hs, ha⟩ := hgot.1 l hl
    refine ⟨NativeRustcVm.BytesAt.restrict hb ?_, hn, hs, ha⟩
    have h : (gotAddr l, 8) ∈ readRegions m a bytes.length bytecode.length := by
      apply List.mem_append_right
      apply List.mem_cons_of_mem
      apply List.mem_append_right
      exact List.mem_map.mpr ⟨l, hl, rfl⟩
    simpa only [Int.toBytes_length] using h

end

end NativeRustcVmX64.VmVerifier
