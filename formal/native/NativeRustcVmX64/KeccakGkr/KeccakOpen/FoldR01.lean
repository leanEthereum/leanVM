module

public import NativeRustcVmX64.KeccakGkr.KeccakOpen.FoldR01Rows
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Code.Vm.Memcpy.Names

namespace NativeRustcVmX64.KeccakGkr.KeccakOpen

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVmX64.Vm.KeccakOpen
open NativeRustcVm.Transcript (DecArea)

public section

variable [Host] {k : Nat} {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData}
  {cx : Cx} {rows : Array (Array EW)}

theorem round0 (hp : Placed code k) (h : PreOk a s c m0)
    (hcpy : Spec (Labels.label NativeRustcVmX64.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost) (hA : cx.a = a)
    (hrsz : rows.size = 64) (hrow : ∀ r < 64, (rows.getD r #[]).size = 64)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.KeccakOpen.b5Offset))
    (hm : Mid cx m0 8 st.data) (hk : KAt m0 (varsOf cx.sl 0 0) kR0 st.data)
    (hr : ElemsAt st.data.dmem (rwA m0) (Fr cx.sl rows 0) 4096) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.KeccakOpen.b11Offset) ∧
      Mid cx m0 8 st'.data ∧ ElemsAt st'.data.dmem (rwA m0) (Fr cx.sl rows 1) 4096) st := by
  have hh : Row cx m0 rows 0 0 (varsOf cx.sl 0 0) kR0 [] st.data :=
    ⟨hm, hk, trivial, by simpa only [F_zero] using hr⟩
  refine (inner_loop (I := fun i d ↦ Row cx m0 rows 0 i (varsOf cx.sl 0 i) kR0 [] d)
    (fun i hi st' hp' hh' ↦ row0 hp h hcpy hmul hA hrsz hrow hi hp' hh') (by decide) hpc hh).mono
    fun st' ⟨hp', hh'⟩ ↦ ?_
  refine ⟨hp', hh'.mid, ?_⟩
  have hr' := hh'.rows
  change ElemsAt st'.data.dmem (rwA m0) (F cx.sl rows 0 (half 0) 0) 4096 at hr'
  rwa [F_half] at hr'

theorem round1 (hp : Placed code k) (h : PreOk a s c m0)
    (hcpy : Spec (Labels.label NativeRustcVmX64.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost) (hA : cx.a = a)
    (hrsz : rows.size = 64) (hrow : ∀ r < 64, (rows.getD r #[]).size = 64)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.KeccakOpen.b11Offset))
    (hm : Mid cx m0 8 st.data) (hr : ElemsAt st.data.dmem (rwA m0) (Fr cx.sl rows 1) 4096) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.KeccakOpen.b18Offset) ∧
      Mid cx m0 8 st'.data ∧ ElemsAt st'.data.dmem (rwA m0) (Fr cx.sl rows 2) 4096) st := by
  refine blk_run (vars := varsOf cx.sl 1 0) hp h hA (varsOf_ok cx (by decide))
    (by decide) (by decide) b11_in_code (by simp [b11]) x11 f11.2 (ret := 0) nofun hpc hm
    trivial trivial fun st1 hpc1 _ hm1 hk1 _ hso1 ↦ ?_
  have hk1' : KAt m0 (varsOf cx.sl 1 0) kR1 st1.data := by
    refine ⟨hk1.1, hk1.2.1, hk1.2.2.1, ?_, trivial⟩
    change reg st1.data .rbx = (rwA m0 + 0#64) + 0#64
    rw [BitVec.add_zero]
    exact hk1.2.2.2.1
  have hpc1' : st1.pc = Host.addrOf (k + NativeRustcVmX64.Vm.KeccakOpen.b12Offset) := hpc1.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.KeccakOpen.b11_next)
  have hh : Row cx m0 rows 1 0 (varsOf cx.sl 1 0) kR1 [] st1.data :=
    ⟨hm1, hk1', trivial, by simpa only [F_zero] using low64_rows h hr hso1⟩
  refine (inner_loop (I := fun i d ↦ Row cx m0 rows 1 i (varsOf cx.sl 1 i) kR1 [] d)
    (fun i hi st' hp' hh' ↦ row1 hp h hcpy hmul hA hrsz hrow hi hp' hh') (by decide) hpc1' hh).mono
    fun st' ⟨hp', hh'⟩ ↦ ?_
  refine ⟨hp', hh'.mid, ?_⟩
  have hr' := hh'.rows
  change ElemsAt st'.data.dmem (rwA m0) (F cx.sl rows 1 (half 1) 0) 4096 at hr'
  rwa [F_half] at hr'

end

end NativeRustcVmX64.KeccakGkr.KeccakOpen
