module

public import NativeRustcVmX64.Whir.GlueLevel.Exit
public import NativeRustcVmX64.Code.Vm.BufEW230Extend.Names
public import NativeRustcVmX64.Code.Vm.BufEW30Extend.Names
public import NativeRustcVmX64.Code.Vm.BufU64x230Extend.Names
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Code.Vm.GlueLevel.Names

/-!
# `glue_level` meets its contract (x86-64)

`glueLevel_spec`: `glue_level`, placed anywhere in the program, given `EW::mul`'s and the three
`Buf::extend`s' contracts, from its entry in a state satisfying `GlueLevelPre s` returns with AL =
`1`, the state at RDI `glueLevel s λ μ oodPoint oodValue queries weights batched`, memory changed
in the state and its stack only, the callee-saved registers and RSP restored (`GlueLevelPost s`).
The run: the products (`head_step`), the claim and the first glued claim (`first_step`), the
second's header and queries (`second_step`), its weights and the count (`third_step`), the return
(`exit_step`).
-/

namespace NativeRustcVmX64.Whir.GlueLevel

open NativeRustcX64 NativeVm.Model NativeRustcVmX64.Vm.GlueLevel

public section

variable [Host] {k : Nat}

/-- **`glue_level`'s contract.** -/
theorem glueLevel_spec (hp : Placed code k)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (hext30 : Spec (Labels.label NativeRustcVmX64.Vm.BufEW30Extend.entryLabel) (BufEWExtendPre 30) (BufEWExtendPost 30))
    (hextU : Spec (Labels.label NativeRustcVmX64.Vm.BufU64x230Extend.entryLabel) (BufU64ExtendPre 230)
      (BufU64ExtendPost 230))
    (hext230 : Spec (Labels.label NativeRustcVmX64.Vm.BufEW230Extend.entryLabel) (BufEWExtendPre 230)
      (BufEWExtendPost 230))
    (s : WhirStateW) : Spec (Labels.label NativeRustcVmX64.Vm.GlueLevel.entryLabel) (GlueLevelPre s) (GlueLevelPost s) := by
  intro m0 hpre
  rw [show Labels.label NativeRustcVmX64.Vm.GlueLevel.entryLabel = Host.addrOf (k + NativeRustcVmX64.Vm.GlueLevel.b0Offset) from hp.label NativeRustcVmX64.Vm.GlueLevel.entry_at]
  exact Eventually.bind (head_step hp hmul hpre) fun _ h3 ↦
    Eventually.bind (first_step hp hext30 hpre h3) fun _ h6 ↦
      Eventually.bind (second_step hp hextU hpre h6) fun _ h9 ↦
        Eventually.bind (third_step hp hext230 hpre h9) fun _ h13 ↦ exit_step hp hpre h13

end

end NativeRustcVmX64.Whir.GlueLevel
