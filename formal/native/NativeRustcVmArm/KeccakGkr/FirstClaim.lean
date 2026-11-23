module

public import NativeRustcVmArm.Code.Vm.BufEW30Extend.Names
public import NativeRustcVmArm.Code.Vm.Dot.Names
public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Code.Vm.EqKernel.Names
public import NativeRustcVmArm.Code.Vm.FirstClaim.Names
public import NativeRustcVmArm.Code.Vm.Memcpy.Names
public import NativeRustcVmArm.KeccakGkr.FirstClaim.Result

/-!
# `first_claim` meets its contract

The prologue (`prologue`: `eq_kernel` on the lane point into the frame's lanes), the bit weights'
loop (`w_loop`: lane `j / 64` times `1 << (j % 64)` by `EW::mul`), the segment's kernel, `last`
and the instance weights' kernel (`mid`: `eq_kernel`, `dot`, `EW::mul`, `eq_kernel`), the claim's
point (`tail`: two `Buf::extend`s), the result copied out and the return (`finish`: two
`memcpy`s) (`firstClaim_spec`).
-/

namespace NativeRustcVmArm.KeccakGkr.FirstClaim

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model
open NativeRustcVmArm.Vm.FirstClaim NativeRustcVmArm.Arrays NativeRustcVmArm.Sumcheck

public section

variable [NativeRustcArm.Host] {k : Nat}

/-- **`first_claim` meets its contract**, given `eq_kernel`'s, `EW::mul`'s, `dot`'s,
`Buf<EW, 30>::extend`'s and `memcpy`'s. -/
theorem firstClaim_spec (hp : Placed code k)
    (heq : Spec (Labels.label NativeRustcVmArm.Vm.EqKernel.entryLabel) EqKernelPre EqKernelPost)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (hdot : Spec (Labels.label NativeRustcVmArm.Vm.Dot.entryLabel) DotPre DotPost)
    (hext : Spec (Labels.label NativeRustcVmArm.Vm.BufEW30Extend.entryLabel) (BufEWExtendPre 30) (BufEWExtendPost 30))
    (hmemcpy : Spec (Labels.label NativeRustcVmArm.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    (inst segment lanePoint output : Array EW) :
    Spec (Labels.label NativeRustcVmArm.Vm.FirstClaim.entryLabel) (FirstClaimPre inst segment lanePoint output)
      (FirstClaimPost inst segment lanePoint output) := by
  intro m0 hpre
  have hl : Labels.label NativeRustcVmArm.Vm.FirstClaim.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.FirstClaim.b0Offset) := hp.label (j := NativeRustcVmArm.Vm.FirstClaim.entryOffset) NativeRustcVmArm.Vm.FirstClaim.entry_at
  rw [hl]
  exact (prologue hp hpre heq).bind fun _ ⟨hpc, hI⟩ ↦
    (w_loop hp hpre hmul hpc hI).bind fun _ ⟨hpc, hI⟩ ↦
    (mid hp hpre heq hmul hdot hpc hI).bind fun _ ⟨hpc, hI⟩ ↦
    (tail hp hpre hext hpc hI).bind fun _ ⟨hpc, hI⟩ ↦ finish hp hpre hmemcpy hpc hI

end

end NativeRustcVmArm.KeccakGkr.FirstClaim
