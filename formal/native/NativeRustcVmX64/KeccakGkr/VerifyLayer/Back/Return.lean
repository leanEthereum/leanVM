module

public import NativeRustcVmX64.KeccakGkr.VerifyLayer.Back.Grind

/-! # The successful `verify_layer` return after extending the claim's point -/

namespace NativeRustcVmX64.KeccakGkr.VerifyLayer

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVmX64.Vm.VerifyLayer
open NativeRustcVm.Transcript (DecArea)

public section

variable [Host] {k : Nat} {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData}

theorem return_success (hp : Placed code k) (hpre : VerifyLayerPre a s c m0)
    {d : MachineData} (hb : Body m0 (outs m0) 24 d)
    (hal : OkAl d true) (hrun : (runL s c m0).isSome = true)
    (hdone : Done a m0 (runL s c m0) d.dmem) :
    Eventually (step1 Host.exe) (Goal a s c m0) ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b84Offset)⟩ := by
  have g := geo_of hpre
  have hwf := wf0 (pre_stack hpre) hb (vars := fun _ ↦ 0) (ret := 0)
  have hm : Match (envB m0 d [] (fun _ ↦ 0) 0) (fr 24) d :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨hb.rsp, trivial⟩ trivial trivial trivial
  refine Body.blk (o' := 24) g hb hwf (blk hp b84_in_code (by simp [b84])) e84 nofun hm
    (by decide +kernel) (hex0 (by decide +kernel)) fun st hm1 hpc1 hb1 _ ↦ ?_
  have hd1 : st.data.dmem = d.dmem := hm1.dmem_eq hwf rfl
  simp only [PcOk] at hpc1
  rw [show (SBool.cmp .eq .W8 (.bin .and .W8 (.reg .rax) (.reg .rax)) (.lit 0)).eval
      (envB m0 d [] (fun _ ↦ 0) 0) = false from okAl_test hal] at hpc1
  simp only [Bool.false_eq_true, ↓reduceIte] at hpc1
  obtain ⟨d1, pc1⟩ := st
  simp only at hpc1 hb1 hd1
  subst hpc1
  rw [show k + NativeRustcVmX64.Vm.VerifyLayer.b84Offset + b84.length = k + NativeRustcVmX64.Vm.VerifyLayer.b85Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyLayer.b84_next]]
  have hwf2 := wf0 (pre_stack hpre) hb1 (vars := fun _ ↦ 0) (ret := 0)
  have hm2 : Match (envB m0 d1 [] (fun _ ↦ 0) 0) (fr 24) d1 :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨hb1.rsp, trivial⟩ trivial trivial trivial
  refine Body.blk (o' := 24) g hb1 hwf2 (blk hp b85_in_code (by simp [b85])) e85 nofun hm2
    (by decide +kernel) (hex0 (by decide +kernel)) fun st2 hm3 hpc3 hb3 _ ↦ ?_
  have hd3 : st2.data.dmem = d.dmem := (hm3.dmem_eq hwf2 rfl).trans hd1
  have hbx : (reg st2.data .rbx).toNat % 256 = 1 := by
    rw [show reg st2.data .rbx = _ from hm3.regs .rbx _ rfl]
    simp only [Sym.eval]
    change (BinOp.apply .merge .W8 (reg d1 .rbx) 1#64).toNat % 256 = 1
    exact NativeRustcVmX64.Arrays.merge_one_mod _
  simp only [PcOk] at hpc3
  rw [lbl hp b87_in_code rfl] at hpc3
  exact at_pc hpc3 (exit50 hp hpre (fun _ h ↦ h) hb3 (by rw [hrun]; exact hbx)
    (by rw [hd3]; exact hdone))

end

end NativeRustcVmX64.KeccakGkr.VerifyLayer
