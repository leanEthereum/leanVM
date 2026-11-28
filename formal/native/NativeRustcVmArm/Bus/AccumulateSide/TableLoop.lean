module

public import NativeRustcVmArm.Code.Vm.BlockForm.Names
public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Code.Vm.EqEvalFnOfEqAbove.Names
public import NativeRustcVmArm.Code.Vm.Evaluate.Names
public import NativeRustcVmArm.Code.Vm.FormBufAddScaled.Names
public import NativeRustcVmArm.Code.Vm.PaddingWeight.Names
public import NativeRustcVmArm.Bus.AccumulateSide.Loop3
public import NativeRustcVmArm.Bus.AccumulateSide.Loop4
public import NativeRustcVmArm.Bus.AccumulateSide.Loop5
public import NativeRustcVmArm.Bus.AccumulateSide.Loop6
public import NativeRustcVmArm.Bus.AccumulateSide.Loop7
public import NativeRustcVmArm.Bus.AccumulateSide.Loop8

/-!
# `accumulate_side`: all table blocks
-/

namespace NativeRustcVmArm.Bus.AccumulateSide

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.AccumulateSide
open NativeVm.Model NativeRustcVmArm.Ring NativeRustcVm.Bus NativeRustcVm.Layout

public section

variable [Host] {m0 : MachineData} {L : LayoutW} {rows : Array Nat}
  {bl : List NativeRustcVm.Data.Block} {Fm : Array (Array FormW)} {SL : BusLayoutW} {k : Nat}

/-- The table loop reaches its exit with every block accumulated. -/
theorem tableLoop (hp : Placed code k) (h : Pre L rows bl Fm SL m0)
    (hee : Spec (Labels.label NativeRustcVmArm.Vm.EqEvalFnOfEqAbove.entryLabel) EqEvalFnOfEqAbovePre EqEvalFnOfEqAbovePost)
    (hbf : Spec (Labels.label NativeRustcVmArm.Vm.BlockForm.entryLabel) BlockFormPre BlockFormPost)
    (has : ∀ f g, Spec (Labels.label NativeRustcVmArm.Vm.FormBufAddScaled.entryLabel) (FormBufAddScaledPre f g) (FormBufAddScaledPost f g))
    (hpw : Spec (Labels.label NativeRustcVmArm.Vm.PaddingWeight.entryLabel) PaddingWeightPre PaddingWeightPost)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (hev : ∀ f, Spec (Labels.label NativeRustcVmArm.Vm.Evaluate.entryLabel) (EvaluatePre f) (EvaluatePost f))
    {j : Nat} (hj : j ≤ bl.length) {m : MachineData}
    (hst : St m0 (TT SL m0 L rows bl Fm j) DL m)
    (hG : FormsAt m.dmem m0.regs.X1.toBitVec (sta SL m0 (BA L rows bl) Fm j).1)
    {R : MachineState → Prop}
    (cont : ∀ m2, St m0 (TT SL m0 L rows bl Fm bl.length) DL m2 →
      FormsAt m2.dmem m0.regs.X1.toBitVec (sta SL m0 (BA L rows bl) Fm bl.length).1 →
      Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b38Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m, if j < bl.length then Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b27Offset)
      else Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b38Offset)⟩ := by
  by_cases hjlt : j < bl.length
  · simp only [hjlt, ↓reduceIte]
    refine turn27 hp h hee hjlt hst fun m1 hs1 hf1 ↦ ?_
    refine turn28 hp h hbf hjlt hs1 fun m2 hs2 hx2 hg2 hf2 ↦ ?_
    refine turn29 hp h hs2 hx2 hg2 fun m3 hs3 hg3 hf3 ↦ ?_
    refine turn30 hp h hjlt hs3 hg3 fun m4 hs4 hg4 hf4 ↦ ?_
    refine turn31 hp h has hjlt hs4 hg4 (hf4 _ (hf3 _ (hf2 _ (hf1 _ hG))))
      fun m5 hs5 hx5 hg5 hG5 ↦ ?_
    refine turn32 hp h hs5 hx5 hg5 fun m6 hs6 hg6 hf6 ↦ ?_
    refine turn33 hp h hpw hjlt hs6 hg6 fun m7 hs7 hg7 hf7 ↦ ?_
    refine turn34 hp h hmul hs7 hg7 fun m8 hs8 hg8 hf8 ↦ ?_
    refine turn35 hp h hev hjlt hs8 hg8 fun m9 hs9 hg9 hf9 ↦ ?_
    refine turn36 hp h hmul hs9 hg9 fun m10 hs10 _ hf10 ↦ ?_
    refine turn37 hp h hjlt hs10 fun m11 hs11 hf11 ↦ ?_
    exact tableLoop hp h hee hbf has hpw hmul hev (by omega) hs11
      (hf11 _ (hf10 _ (hf9 _ (hf8 _ (hf7 _ (hf6 _ hG5)))))) cont
  · have he : j = bl.length := by omega
    subst j
    simp only [Nat.lt_irrefl, ↓reduceIte]
    exact cont m hst hG
termination_by bl.length - j
decreasing_by omega

end

end NativeRustcVmArm.Bus.AccumulateSide
