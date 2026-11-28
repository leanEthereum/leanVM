module

public import NativeRustcVmX64.Bus.AccumulateSide.TurnG
public import NativeRustcVmX64.Bus.AccumulateSide.TurnA
public import NativeRustcVmX64.Code.Vm.BlockForm.Names
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Code.Vm.EqEvalFnOfEqAbove.Names
public import NativeRustcVmX64.Code.Vm.Evaluate.Names
public import NativeRustcVmX64.Code.Vm.FormBufAddScaled.Names
public import NativeRustcVmX64.Code.Vm.PaddingWeight.Names

/-! # `accumulate_side`: the complete table loop (x86-64) -/

namespace NativeRustcVmX64.Bus.AccumulateSide

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVm.Transcript
open NativeRustcVmX64.Vm.AccumulateSide
open NativeVm.Model NativeRustcVm.Bus NativeRustcVm.Layout

public section

variable [Host] {L : LayoutW} {rows : Array Nat} {bl : List NativeRustcVm.Data.Block}
  {Fm : Array (Array FormW)} {SL : BusLayoutW} {m0 : MachineData} {k : Nat}

 theorem tableTurn (hp : Placed code k) (h : Pre L rows bl Fm SL m0)
    (hee : Spec (Labels.label NativeRustcVmX64.Vm.EqEvalFnOfEqAbove.entryLabel) EqEvalFnOfEqAbovePre EqEvalFnOfEqAbovePost)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (hbf : Spec (Labels.label NativeRustcVmX64.Vm.BlockForm.entryLabel) BlockFormPre BlockFormPost)
    (has : ∀ f g, Spec (Labels.label NativeRustcVmX64.Vm.FormBufAddScaled.entryLabel) (FormBufAddScaledPre f g) (FormBufAddScaledPost f g))
    (hpw : Spec (Labels.label NativeRustcVmX64.Vm.PaddingWeight.entryLabel) PaddingWeightPre PaddingWeightPost)
    (hev : ∀ f, Spec (Labels.label NativeRustcVmX64.Vm.Evaluate.entryLabel) (EvaluatePre f) (EvaluatePost f))
    {j : Nat} (hj : j < bl.length) {m : MachineData} (hst : TH L rows bl Fm SL m0 j m) :
    Eventually (step1 Host.exe) (fun st ↦ TH L rows bl Fm SL m0 (j + 1) st.data ∧
      ((st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b17Offset) ∧ j + 1 < bl.length) ∨
        (st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b28Offset) ∧ j + 1 = bl.length)))
      ⟨m, Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b17Offset)⟩ := by
  refine turnA hp h hee hj hst fun m1 hs1 hr1 hg1 ↦ ?_
  refine turnB hp h hbf hj hs1 hr1 hg1 fun m2 hs2 hf2 hg2 ↦ ?_
  refine turnC hp h has hj hs2 hf2 hg2 fun m3 hs3 hf3 hg3 ↦ ?_
  refine turnD hp h hj hs3 hf3 hg3 fun m4 hs4 hf4 hg4 hsi hdx ↦ ?_
  refine turnE hp h hpw hj hs4 hf4 hg4 hsi hdx fun m5 hs5 hf5 hg5 hr5 ↦ ?_
  refine turnF hp h hmul hev hj hs5 hf5 hg5 hr5 fun m6 hs6 hg6 hr6 ↦ ?_
  exact turnG hp h hj hs6 hg6 hr6

 theorem tableLoop (hp : Placed code k) (h : Pre L rows bl Fm SL m0)
    (hee : Spec (Labels.label NativeRustcVmX64.Vm.EqEvalFnOfEqAbove.entryLabel) EqEvalFnOfEqAbovePre EqEvalFnOfEqAbovePost)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (hbf : Spec (Labels.label NativeRustcVmX64.Vm.BlockForm.entryLabel) BlockFormPre BlockFormPost)
    (has : ∀ f g, Spec (Labels.label NativeRustcVmX64.Vm.FormBufAddScaled.entryLabel) (FormBufAddScaledPre f g) (FormBufAddScaledPost f g))
    (hpw : Spec (Labels.label NativeRustcVmX64.Vm.PaddingWeight.entryLabel) PaddingWeightPre PaddingWeightPost)
    (hev : ∀ f, Spec (Labels.label NativeRustcVmX64.Vm.Evaluate.entryLabel) (EvaluatePre f) (EvaluatePost f))
    {j : Nat} (hj : j < bl.length) {m : MachineData} (hst : TH L rows bl Fm SL m0 j m) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b28Offset) ∧
      TH L rows bl Fm SL m0 bl.length st.data) ⟨m, Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b17Offset)⟩ := by
  refine Sym.loop (fun n (st : MachineState) ↦ ∃ j, n = bl.length - j ∧ j < bl.length ∧
      st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b17Offset) ∧ TH L rows bl Fm SL m0 j st.data)
    (fun n st ⟨j, hn, hj, hpc, hst⟩ ↦ ?_) ⟨j, rfl, hj, rfl, hst⟩
  obtain ⟨d, pc⟩ := st
  simp only at hpc hst
  subst hpc
  refine (tableTurn hp h hee hmul hbf has hpw hev hj hst).mono fun st' ⟨hs, hx⟩ ↦ ?_
  rcases hx with ⟨hpc, hlt⟩ | ⟨hpc, heq⟩
  · exact .inr ⟨bl.length - (j + 1), by omega, j + 1, rfl, hlt, hpc, hs⟩
  · exact .inl ⟨hpc, heq ▸ hs⟩

end

end NativeRustcVmX64.Bus.AccumulateSide
