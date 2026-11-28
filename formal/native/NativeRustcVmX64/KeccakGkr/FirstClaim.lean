module

public import NativeRustcVmX64.KeccakGkr.FirstClaim.Result
public import NativeRustcVmX64.Code.Vm.BufEW30Extend.Names
public import NativeRustcVmX64.Code.Vm.Dot.Names
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Code.Vm.EqKernel.Names
public import NativeRustcVmX64.Code.Vm.FirstClaim.Names
public import NativeRustcVmX64.Code.Vm.Memcpy.Names

/-!
# `first_claim` meets its contract (x86-64)

The prologue (`prologue`: `eq_kernel` on the lane point into the frame's lanes), the bit weights'
loop (`w_loop`: lane `j / 64` times `1 << (j % 64)` by `EW::mul`), the segment's kernel and `last`
(`last`: `eq_kernel`, `dot`, `EW::mul`), the instance weights' kernel (`mu`: `eq_kernel`), the
claim's point (`tail`: two `Buf::extend`s), the result copied out and the return (`finish`: two
`memcpy`s) (`firstClaim_spec`).
-/

namespace NativeRustcVmX64.KeccakGkr.FirstClaim

open NativeRustcX64 NativeVm.Model NativeRustcVmX64.Vm.FirstClaim

public section

variable [Host] {k : Nat}

/-- **`first_claim` meets its contract**, given `eq_kernel`'s, `EW::mul`'s, `dot`'s,
`Buf<EW, 30>::extend`'s and `memcpy`'s. -/
theorem firstClaim_spec (hp : Placed code k)
    (heq : Spec (Labels.label NativeRustcVmX64.Vm.EqKernel.entryLabel) EqKernelPre EqKernelPost)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (hdot : Spec (Labels.label NativeRustcVmX64.Vm.Dot.entryLabel) DotPre DotPost)
    (hext : Spec (Labels.label NativeRustcVmX64.Vm.BufEW30Extend.entryLabel) (BufEWExtendPre 30) (BufEWExtendPost 30))
    (hmemcpy : Spec (Labels.label NativeRustcVmX64.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    (inst segment lanePoint output : Array EW) :
    Spec (Labels.label NativeRustcVmX64.Vm.FirstClaim.entryLabel) (FirstClaimPre inst segment lanePoint output)
      (FirstClaimPost inst segment lanePoint output) := by
  intro m0 hpre
  have hl : Labels.label NativeRustcVmX64.Vm.FirstClaim.entryLabel = Host.addrOf (k + NativeRustcVmX64.Vm.FirstClaim.b0Offset) := label_of_infix hp b0_in_code rfl
  rw [hl]
  exact (prologue hp hpre heq).bind fun _ ⟨hpc, hI⟩ ↦
    (w_loop hp hpre hmul hpc hI).bind fun _ ⟨hpc, hI⟩ ↦
    (last hp hpre heq hmul hdot hpc hI).bind fun _ ⟨hpc, hI⟩ ↦
    (mu hp hpre heq hpc hI).bind fun _ ⟨hpc, hI⟩ ↦
    (tail hp hpre hext hpc hI).bind fun _ ⟨hpc, hI⟩ ↦ finish hp hpre hmemcpy hpc hI

end

end NativeRustcVmX64.KeccakGkr.FirstClaim
