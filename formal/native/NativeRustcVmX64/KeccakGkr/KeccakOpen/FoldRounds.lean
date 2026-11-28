module

public import NativeRustcVmX64.KeccakGkr.KeccakOpen.FoldR2Tail
public import NativeRustcVmX64.KeccakGkr.KeccakOpen.FoldR34Rows
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Code.Vm.Memcpy.Names

namespace NativeRustcVmX64.KeccakGkr.KeccakOpen

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVmX64.Vm.KeccakOpen
open NativeRustcVm.Transcript (off DecArea)

public section

variable [Host] {k : Nat} {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData}
  {cx : Cx} {rows : Array (Array EW)}

theorem round2 (hp : Placed code k) (h : PreOk a s c m0)
    (hcpy : Spec (Labels.label NativeRustcVmX64.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost) (hA : cx.a = a)
    (hrsz : rows.size = 64) (hrow : ∀ r < 64, (rows.getD r #[]).size = 64)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.KeccakOpen.b18Offset))
    (hm : Mid cx m0 8 st.data)
    (hr : ElemsAt st.data.dmem (rwA m0) (Fr cx.sl rows 2) 4096) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.KeccakOpen.b58Offset) ∧
      Mid cx m0 8 st'.data ∧ KAt m0 (varsOf cx.sl 3 0) [(.r13, P)] st'.data ∧
      Words m0 (varsOf cx.sl 3 0) W6 st'.data ∧
      ElemsAt st'.data.dmem (rwA m0) (Fr cx.sl rows 3) 4096) st := by
  have hh : Row cx m0 rows 2 0 (varsOf cx.sl 2 0) [] [] st.data :=
    ⟨hm, trivial, trivial, by simpa only [F_zero] using hr⟩
  refine (row2_0 hp h hcpy hmul hA hrsz hrow hpc hh).bind fun st' ⟨hpc, hh⟩ ↦ ?_
  refine (row2_1 hp h hcpy hmul hA hrsz hrow hpc hh).bind fun st' ⟨hpc, hh⟩ ↦ ?_
  refine (row2_2 hp h hcpy hmul hA hrsz hrow hpc hh).bind fun st' ⟨hpc, hh⟩ ↦ ?_
  refine (row2_3 hp h hcpy hmul hA hrsz hrow hpc hh).bind fun st' ⟨hpc, hh⟩ ↦ ?_
  refine (row2_4 hp h hcpy hmul hA hrsz hrow hpc hh).bind fun st' ⟨hpc, hh⟩ ↦ ?_
  refine (row2_5 hp h hcpy hmul hA hrsz hrow hpc hh).bind fun st' ⟨hpc, hh⟩ ↦ ?_
  refine (row2_6 hp h hcpy hmul hA hrsz hrow hpc hh).bind fun st' ⟨hpc, hh⟩ ↦ ?_
  refine (row2_7 hp h hcpy hmul hA hrsz hrow hpc hh).mono fun st' ⟨hp', hh'⟩ ↦ ?_
  refine ⟨hp', hh'.mid, ⟨hh'.known.get (r := .r13) (v := P) (.tail _ (.tail _ (.head _))), trivial⟩,
    hh'.words, ?_⟩
  have hr' := hh'.rows
  change ElemsAt st'.data.dmem (rwA m0) (F cx.sl rows 2 (half 2) 0) 4096 at hr'
  rwa [F_half] at hr'

theorem round3 (hp : Placed code k) (h : PreOk a s c m0)
    (hcpy : Spec (Labels.label NativeRustcVmX64.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost) (hA : cx.a = a)
    (hrsz : rows.size = 64) (hrow : ∀ r < 64, (rows.getD r #[]).size = 64)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.KeccakOpen.b58Offset))
    (hm : Mid cx m0 8 st.data)
    (hk : KAt m0 (varsOf cx.sl 3 0) [(.r13, P)] st.data)
    (hw : Words m0 (varsOf cx.sl 3 0) W6 st.data)
    (hr : ElemsAt st.data.dmem (rwA m0) (Fr cx.sl rows 3) 4096) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.KeccakOpen.b78Offset) ∧
      Mid cx m0 8 st'.data ∧ KAt m0 (varsOf cx.sl 4 0) [(.r13, P)] st'.data ∧
      Words m0 (varsOf cx.sl 4 0) W6 st'.data ∧
      ElemsAt st'.data.dmem (rwA m0) (Fr cx.sl rows 4) 4096) st := by
  have hh : Row cx m0 rows 3 0 (varsOf cx.sl 3 0) [(.r13, P)] W6 st.data :=
    ⟨hm, hk, hw, by simpa only [F_zero] using hr⟩
  refine (row3_0 hp h hcpy hmul hA hrsz hrow hpc hh).bind fun st' ⟨hpc, hh⟩ ↦ ?_
  refine (row3_1 hp h hcpy hmul hA hrsz hrow hpc hh).bind fun st' ⟨hpc, hh⟩ ↦ ?_
  refine (row3_2 hp h hcpy hmul hA hrsz hrow hpc hh).bind fun st' ⟨hpc, hh⟩ ↦ ?_
  refine (row3_3 hp h hcpy hmul hA hrsz hrow hpc hh).mono fun st' ⟨hp', hh'⟩ ↦ ?_
  refine ⟨hp', hh'.mid, ⟨hh'.known.get (r := .r13) (v := P) (.tail _ (.tail _ (.head _))), trivial⟩,
    hh'.words, ?_⟩
  have hr' := hh'.rows
  change ElemsAt st'.data.dmem (rwA m0) (F cx.sl rows 3 (half 3) 0) 4096 at hr'
  rwa [F_half] at hr'

theorem round4 (hp : Placed code k) (h : PreOk a s c m0)
    (hcpy : Spec (Labels.label NativeRustcVmX64.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost) (hA : cx.a = a)
    (hrsz : rows.size = 64) (hrow : ∀ r < 64, (rows.getD r #[]).size = 64)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.KeccakOpen.b78Offset))
    (hm : Mid cx m0 8 st.data)
    (hk : KAt m0 (varsOf cx.sl 4 0) [(.r13, P)] st.data)
    (hw : Words m0 (varsOf cx.sl 4 0) W6 st.data)
    (hr : ElemsAt st.data.dmem (rwA m0) (Fr cx.sl rows 4) 4096) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.KeccakOpen.b88Offset) ∧
      Mid cx m0 8 st'.data ∧ KAt m0 (varsOf cx.sl 5 0) [(.rbp, P)] st'.data ∧
      Words m0 (varsOf cx.sl 5 0) W6 st'.data ∧
      ElemsAt st'.data.dmem (rwA m0) (Fr cx.sl rows 5) 4096) st := by
  have hh : Row cx m0 rows 4 0 (varsOf cx.sl 4 0) [(.r13, P)] W6 st.data :=
    ⟨hm, hk, hw, by simpa only [F_zero] using hr⟩
  refine (row4_0 hp h hcpy hmul hA hrsz hrow hpc hh).bind fun st' ⟨hpc, hh⟩ ↦ ?_
  refine (row4_1 hp h hcpy hmul hA hrsz hrow hpc hh).mono fun st' ⟨hp', hh'⟩ ↦ ?_
  refine ⟨hp', hh'.mid, ⟨hh'.known.get (r := .rbp) (v := P) (.tail _ (.tail _ (.head _))), trivial⟩,
    hh'.words, ?_⟩
  have hr' := hh'.rows
  change ElemsAt st'.data.dmem (rwA m0) (F cx.sl rows 4 (half 4) 0) 4096 at hr'
  rwa [F_half] at hr'

end

end NativeRustcVmX64.KeccakGkr.KeccakOpen
