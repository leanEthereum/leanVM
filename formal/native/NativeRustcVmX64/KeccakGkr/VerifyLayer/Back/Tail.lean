module

public import NativeRustcVmX64.KeccakGkr.VerifyLayer.Back.ClaimExtend
public import NativeRustcVmX64.Code.Vm.BufEW30Extend.Names
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Code.Vm.LinearTranspose.Names
public import NativeRustcVmX64.Code.Vm.Memcpy.Names

/-! # From completed layer weights to the successful return -/

namespace NativeRustcVmX64.KeccakGkr.VerifyLayer

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model
open NativeRustcVm.Transcript (DecArea)
open NativeRustcVmX64.Vm.VerifyLayer

public section

variable [Host] {m0 : MachineData} {a : DecArea} {s s6 : TState} {c : KeccakClaimW}
  {ch b : EW} {pt lp t : Array EW} {k : Nat}

theorem tail (hp : Placed code k) (hpre : VerifyLayerPre a s c m0)
    (hext : Spec (Labels.label NativeRustcVmX64.Vm.BufEW30Extend.entryLabel) (BufEWExtendPre 30) (BufEWExtendPost 30))
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (hlt : ∀ ws, Spec (Labels.label NativeRustcVmX64.Vm.LinearTranspose.entryLabel) (LinearTransposePre ws)
      (LinearTransposePost ws))
    (hmemcpy : Spec (Labels.label NativeRustcVmX64.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    (hpt : pt.size ≤ 30) (hpsz : pt.size = c.point.size) (hlp : lp.size = 11)
    {d : MachineData} (hb : Body m0 (wFront m0) 24 d)
    (h : WMem m0 a c ch b pt lp t s6 1600 d.dmem) (h15 : reg d .r15 = sA m0)
    (hrun : runL s c m0 = some (newClaim ch pt lp t b, s6)) :
    Eventually (step1 Host.exe) (Goal a s c m0) ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b79Offset)⟩ := by
  refine transpose hp hpre hlt hpt hlp hb h h15 fun d1 hb1 h1 ↦ ?_
  refine claim_value hp hpre hmul hpt hb1 h1 fun d2 hb2 h2 hv2 ↦ ?_
  refine claim_copy hp hpre hmemcpy hpt hb2 h2 hv2 fun d3 hb3 h3 hbx3 hv3 hmu3 ↦ ?_
  refine claim_extend hp hpre hext hpt hpsz hb3 h3 hbx3 hv3 hmu3 fun d4 hb4 h4 hal4 hc4 ↦ ?_
  refine return_success hp hpre hb4 hal4 (by rw [hrun]; rfl) ?_
  intro c' s' he
  rw [hrun] at he
  cases he
  exact ⟨h4.ts, hc4, ⟨NativeRustcVm.KeccakGkr.linearTranspose_size' _, h4.weights⟩⟩

end

end NativeRustcVmX64.KeccakGkr.VerifyLayer
