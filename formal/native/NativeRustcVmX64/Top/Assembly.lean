module

public import NativeRustcVmX64.Top.Correct
public import NativeRustcVmX64.Top.Assembly.VerifyExecution
public import NativeRustcVmX64.Top.Assembly.Wire
public import NativeRustcVmX64.Code.Vm.LeanvmVerify.Names
public import NativeRustcVmX64.Top.Leanvm.Reject

/-!
# The end-to-end x86-64 verifier theorem

`verify_correct` proves rustc's raw `leanvm_verify` assembly against the verifier model under its Rust safety contract, ABI stack and return address, and loader facts including the reached GOT slots. The entry's checks guard the result, and every callee contract is discharged by its assembly proof.
-/

namespace NativeRustcVmX64.VmVerifier

open NativeRustcX64 NativeVm NativeRustcVm.Top NativeRustcVm.Transcript NativeVm.Model
open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

public section

variable [Host]

/-- The complete verifier returns the model's verdict in RAX, pops its return address, and preserves the caller's saved state. -/
theorem verify_correct (hP : Host.prog = Vm.code)
    {bytes : List UInt8} {bytecode : List UInt64} {pub : Vector UInt64 4} {a : NativeVm.Entry.Areas}
    {m : MachineData}
    (hin : NativeVm.Entry.EntryPre m.dmem (ctxOf m) a bytes bytecode pub)
    (hstack : StackOk m leanvmVerifyStack) (hrod : RodataAt m leanvmVerifyStack)
    (hapS : ApartFrom (entryRegions (ctxOf m) a bytes.length bytecode.length)
      (stackBelow m leanvmVerifyStack) (leanvmVerifyStack + 8))
    (hapR : ∀ r ∈ entryRegions (ctxOf m) a bytes.length bytecode.length, 0 < r.size →
      RodataApart r.addr r.size)
    (hgot : GotAt m leanvmVerifyStack
      ((entryRegions (ctxOf m) a bytes.length bytecode.length).map (fun r => (r.addr, r.size)) ++
        rodataAreas) ["memcpy", "memset"]) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = retOf m ∧ rspOf st.data = rspOf m + 8#64 ∧
      reg st.data .rax = (if Checks a bytes.length bytecode.length
        then verdictWord bytes bytecode pub else 0).toBitVec ∧
      NativeRustcVm.SameOutside m.dmem st.data.dmem (NativeRustcVm.InAny
        [⟨a.decoded.toBitVec, 8 * NativeVm.decodedWords bytes.length⟩,
          ⟨a.work.toBitVec, NativeRustcVm.Top.workAreaBytes⟩, NativeRustcVmX64.frameR m leanvmVerifyStack]) ∧
      Saved m st.data) ⟨m, label NativeRustcVmX64.Vm.LeanvmVerify.entryLabel⟩ := by
  classical
  by_cases hc : Checks a bytes.length bytecode.length
  · have hR : ∀ r ∈ usedRegions (ctxOf m) a bytes.length bytecode.length, 0 < r.size →
        RodataApart r.addr r.size := by
      intro r hr hp t
      obtain ⟨s, hs, ha, hn⟩ := usedRegions_cover hc.1 hr
      have h := hapR s hs (by omega) t
      unfold NativeRustcVm.Apart at h ⊢
      rw [ha] at h
      omega
    have hG : GotAt m leanvmVerifyStack
        ((usedRegions (ctxOf m) a bytes.length bytecode.length).map (fun r => (r.addr, r.size)) ++
          rodataAreas) ["memcpy", "memset"] := by
      refine ⟨?_, hgot.2⟩
      intro l hl
      obtain ⟨hb, hn, hs, ha⟩ := hgot.1 l hl
      refine ⟨hb, hn, hs, ?_⟩
      intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hp
        obtain ⟨s, hs, he, hsz⟩ := usedRegions_cover hc.1 hr
        have h := ha (s.addr, s.size)
          (List.mem_append_left _ (List.mem_map.mpr ⟨s, hs, rfl⟩))
        unfold Apart at h ⊢
        simp only at h ⊢
        rw [he] at h
        omega
      · exact ha p (List.mem_append_right _ hp)
    simpa only [ite_eq_left hc, verdictWord] using verify_correct_of_specs hP (Assembly.decode hP)
      (Assembly.verifyExecution hP) (hin.checked hc.1) hc.2 hstack hrod (hapS.used hc.1) hR hG
  · have hctx := hapS ⟨(ctxOf m).toBitVec, 96⟩
      (by simp [entryRegions, NativeVm.Entry.ctxWords]) (by change 0 < 96; decide)
    rw [Top.Leanvm.lbl_entry (Placement.placed_LeanvmVerify hP)]
    refine Eventually.mono
      (Top.Leanvm.reject (Placement.placed_LeanvmVerify hP) hin.toContextAt hstack hctx hc)
      fun st ⟨hpc, hrsp, hx, hm, hs⟩ ↦ ⟨hpc, hrsp, ?_, ?_, hs⟩
    · simpa only [ite_eq_right hc, UInt64.toBitVec_zero] using hx
    · intro p hp
      exact hm p fun h ↦ hp ⟨frameR m leanvmVerifyStack,
        List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), h⟩

end

end NativeRustcVmX64.VmVerifier
