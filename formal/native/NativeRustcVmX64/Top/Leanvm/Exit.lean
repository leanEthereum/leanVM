module

public import NativeRustcVmX64.Top.Leanvm.Decode

/-!
# `leanvm_verify`'s returns (x86-64)

`exit13`: the epilogue (`b13`) returns with RAX kept; `exit12`: `b12` sets RAX to `0`, then the
epilogue. Both from the frame with RSP at offset `8`, the memory unchanged.
-/

namespace NativeRustcVmX64.Top.Leanvm

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.LeanvmVerify NativeRustcVmX64.Transcript
open NativeRustcVmX64.Top NativeVm NativeRustcVm.Transcript

public section

variable [Host] {k : Nat}

/-- **The epilogue**, RAX kept. -/
theorem exit13 (hp : Placed code k) {m0 : MachineData} (hst : StackOk m0 leanvmVerifyStack)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.LeanvmVerify.b13Offset)) (hf : Frame m0 112 slots 8 st.data) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = retOf m0 ∧
      rspOf st'.data = rspOf m0 + 8#64 ∧ reg st'.data .rax = reg st.data .rax ∧
      st'.data.dmem = st.data.dmem ∧ Saved m0 st'.data) st := by
  have hfnw := frame_noWrap (F := 112) hst (by decide)
  have hwf := frame_wf (m0 := m0) (d := st.data) (F := 112) (rest := []) (vars := fun _ ↦ 0)
    (ret := 0) ⟨Mapped.keeps (frame_mapped hst (by decide)) hf.kept, hfnw⟩ (by simp)
    (List.pairwise_singleton _ _)
  refine exec_at (infix_of b13_in_code (by simp [b13]) hp) run_b13 hwf nofun hpc
    (match_ofMachine ⟨rfl, trivial⟩ ⟨hf.rsp_eval, trivial⟩ trivial trivial trivial)
    fun st' hm hpc' ↦ ?_
  obtain ⟨hepi, hmem, hrax⟩ := after_eq run_b13 ▸ ok_b13
  obtain ⟨hsv, hrsp⟩ := Frame.epilogue hf hwf hm hepi
  simp only [PcOk] at hpc'
  exact .done _ ⟨by rw [hpc']; exact hf.load_ret hst (by decide), hrsp, hm.regs .rax _ hrax,
    hm.dmem_eq hwf hmem, hsv⟩

/-- **`0`**, then the epilogue. -/
theorem exit12 (hp : Placed code k) {m0 : MachineData} (hst : StackOk m0 leanvmVerifyStack)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.LeanvmVerify.b12Offset)) (hf : Frame m0 112 slots 8 st.data) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = retOf m0 ∧
      rspOf st'.data = rspOf m0 + 8#64 ∧ reg st'.data .rax = 0#64 ∧
      st'.data.dmem = st.data.dmem ∧ Saved m0 st'.data) st := by
  have hfnw := frame_noWrap (F := 112) hst (by decide)
  have hwf := frame_wf (m0 := m0) (d := st.data) (F := 112) (rest := []) (vars := fun _ ↦ 0)
    (ret := 0) ⟨Mapped.keeps (frame_mapped hst (by decide)) hf.kept, hfnw⟩ (by simp)
    (List.pairwise_singleton _ _)
  refine exec_at (infix_of b12_in_code (by simp [b12]) hp) run_b12 hwf nofun hpc
    (match_ofMachine ⟨rfl, trivial⟩ ⟨hf.rsp_eval, trivial⟩ trivial trivial trivial)
    fun st' hm hpc' ↦ ?_
  obtain ⟨hmid, hmem, hrax⟩ := after_eq run_b12 ▸ ok_b12
  have hf' : Frame m0 112 slots 8 st'.data := Frame.of_block hf hwf hm hmid slots_le
  simp only [PcOk] at hpc'
  refine Eventually.mono (exit13 hp hst (hpc'.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.LeanvmVerify.b12_next)) hf')
    fun s ⟨h1, h2, h3, h4, h5⟩ ↦ ⟨h1, h2, h3.trans (hm.regs .rax _ hrax), h4.trans
      (hm.dmem_eq hwf hmem), h5⟩

end

end NativeRustcVmX64.Top.Leanvm
