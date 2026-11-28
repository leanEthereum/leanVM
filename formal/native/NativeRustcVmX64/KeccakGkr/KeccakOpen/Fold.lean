module

public import NativeRustcVmX64.KeccakGkr.KeccakOpen.FoldR01
public import NativeRustcVmX64.KeccakGkr.KeccakOpen.FoldRounds
public import NativeRustcVmX64.KeccakGkr.KeccakOpen.FoldR5
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Code.Vm.Memcpy.Names

namespace NativeRustcVmX64.KeccakGkr.KeccakOpen

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVmX64.Vm.KeccakOpen
open NativeRustcVm.Transcript (DecArea)

public section

/-- The six in-place rounds, preserving the frame and all non-output memory. -/
theorem fold_run [Host] {k : Nat} (hp : Placed code k)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (hcpy : Spec (Labels.label NativeRustcVmX64.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData} (h : PreOk a s c m0)
    {cx : Cx} (hA : cx.a = a) {rows : Array (Array EW)}
    (hrsz : rows.size = 64) (hrow : ∀ r < 64, (rows.getD r #[]).size = 64)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.KeccakOpen.b5Offset))
    (hm : Mid cx m0 8 st.data) (hk : KAt m0 (varsOf cx.sl 0 0) kR0 st.data)
    (hr : ElemsAt st.data.dmem (rwA m0) (Fr cx.sl rows 0) 4096) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.KeccakOpen.b93Offset) ∧
      Mid cx m0 8 st'.data ∧ ElemsAt st'.data.dmem (rwA m0) (Fr cx.sl rows 6) 4096) st := by
  refine (round0 hp h hcpy hmul hA hrsz hrow hpc hm hk hr).bind fun st ⟨hpc, hm, hr⟩ ↦ ?_
  refine (round1 hp h hcpy hmul hA hrsz hrow hpc hm hr).bind fun st ⟨hpc, hm, hr⟩ ↦ ?_
  refine (round2 hp h hcpy hmul hA hrsz hrow hpc hm hr).bind fun st ⟨hpc, hm, hk, hw, hr⟩ ↦ ?_
  refine (round3 hp h hcpy hmul hA hrsz hrow hpc hm hk hw hr).bind fun st ⟨hpc, hm, hk, hw, hr⟩ ↦ ?_
  refine (round4 hp h hcpy hmul hA hrsz hrow hpc hm hk hw hr).bind fun st ⟨hpc, hm, hk, hw, hr⟩ ↦ ?_
  exact round5 hp h hcpy hmul hA hrsz hrow hpc hm hk hw hr

end

end NativeRustcVmX64.KeccakGkr.KeccakOpen
