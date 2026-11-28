module

public import NativeRustcVmX64.KeccakGkr.VerifyLayer.CheckA
public import NativeRustcVmX64.KeccakGkr.VerifyLayer.Back.State
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Code.Vm.EqKernel.Names
public import NativeRustcVmX64.Code.Vm.SumE.Names
public import NativeRustcVmX64.Code.Vm.TStateReadScalars.Names

/-!
# `verify_layer` on x86-64: from the entry to the first check passed

The front (`front`: the product's read), its projection (`proj`), the segment kernel (`segs`),
ι's two loops (`b26Run`, `iotaLoop1`, `b32Run`, `iotaLoop2`), its terms (`mulPair`, `iotaMu`) and
the first check (`checkARun`): at `b44` (code index `370`) with `AfterA` and the rest of the
layer's run, or back at the caller on a rejected product or check (`toAfterA`).
-/

namespace NativeRustcVmX64.KeccakGkr.VerifyLayer

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVmX64.Vm.VerifyLayer
open NativeRustcVm.Transcript (tstateBytes DecArea TStateAt off)
open LeanVM.Parameters LeanVM.Protocol.Verifier

public section

variable [Host] {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData} {k : Nat}

/-- ι's spills hold the words the rest reads. -/
theorem backWords_of {p : Array EW} {s1 : TState} {d : MachineData}
    (h : K0 m0 a c p s1 (spillsJ m0 c) d) : FWs m0 d.dmem (backWords m0) := fun q hq ↦
  h.sp q (by
    simp only [backWords, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [spillsJ, spillsI, spills3])

/-- **From the entry to the first check passed**, given `read_scalars`'s, `EW::mul`'s,
`eq_kernel`'s and `sum_e`'s contracts. -/
theorem toAfterA (hp : Placed code k)
    (hrs : Spec (Labels.label NativeRustcVmX64.Vm.TStateReadScalars.entryLabel) (ReadScalarsPre a s) (ReadScalarsPost a s))
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (hek : Spec (Labels.label NativeRustcVmX64.Vm.EqKernel.entryLabel) EqKernelPre EqKernelPost)
    (hsum : Spec (Labels.label NativeRustcVmX64.Vm.SumE.entryLabel) SumEPre SumEPost)
    (hpre : VerifyLayerPre a s c m0)
    (cont : ∀ p s1 d, AfterA m0 a c p s1 d →
      runL s c m0 = ((grind (grindingBits (productBits - 1))).run s1).bind
        (fun q ↦ rest2 c p q.2) →
      Eventually (step1 Host.exe) (Goal a s c m0) ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b44Offset)⟩) :
    Eventually (step1 Host.exe) (Goal a s c m0) ⟨m0, Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b0Offset)⟩ := by
  refine front hp hrs hpre fun p s1 d hr hh ↦ ?_
  have hrun1 : runL s c m0 = rest1 (reg m0 .rsi).toNat (stepN m0) c p s1 := by
    unfold runL
    rw [run_rest, hr]
    rfl
  refine Eventually.bind (proj hp hmul hpre hh) fun st ⟨hpc, he⟩ ↦ ?_
  obtain ⟨d1, pc1⟩ := st
  simp only at hpc he
  subst hpc
  refine segs hp hek hpre he fun d2 hsg ↦ b26Run hp hpre hsg fun d3 hia ↦ ?_
  refine Eventually.bind (iotaLoop1 hp hpre hia) fun st ⟨hpc, hx⟩ ↦ ?_
  obtain ⟨d4, pc4⟩ := st
  simp only at hpc hx
  subst hpc
  refine b32Run hp hpre hx fun d5 hja ↦ ?_
  refine Eventually.bind (iotaLoop2 hp hpre hja) fun st ⟨hpc, hjx⟩ ↦ ?_
  obtain ⟨d6, pc6⟩ := st
  simp only at hpc hjx
  subst hpc
  refine mulPair hp hmul hpre hjx fun d7 hcb ↦ iotaMu hp hmul hsum hpre hcb fun d8 hcc ↦ ?_
  refine checkARun hp hpre hcc hrun1 fun d9 hk hc ↦ ?_
  exact cont p s1 d9 ⟨hk.body, hk.ts, hk.prod, hk.psize, backWords_of hk⟩
    (hrun1.trans (rest1_true hc))

end

end NativeRustcVmX64.KeccakGkr.VerifyLayer
