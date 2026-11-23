module

public import NativeRustcVmX64.KeccakGkr.KeccakOpen.Entry0
public import NativeRustcVmX64.KeccakGkr.KeccakOpen.Exit

/-! # `keccak_open`: a failed sumcheck returns `None` -/

namespace NativeRustcVmX64.KeccakGkr.KeccakOpen

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVmX64.Vm.KeccakOpen
open NativeRustcVm.Transcript (DecArea off)

public section

variable [Host] {k : Nat} {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData}

theorem none_exit (hp : Placed code k) (h : PreOk a s c m0) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.KeccakOpen.b1Offset)) (hsc : Sc a s m0 st.data) (hn : scRun s m0 = none) :
    Eventually (step1 Host.exe) (Goal a s c m0) st := by
  have hwf := wf_fold h hsc.body.fr.kept (vars := fun _ ↦ 0) (ret := 0)
  refine exec_at (infix_of b1_in_code (by simp [b1]) hp) x1 hwf nofun hpc
    (body_match h hsc.body) fun st1 hm1 hpc1 ↦ ?_
  have htag : NativeRustcVm.WordAt st.data.dmem (off (fbA m0) 88) 0 := by
    have ht := hsc.out.1
    rw [hn] at ht
    exact ht
  have hl : (E m0 st.data (fun _ ↦ 0) 0).load 0 88 4 = 0#64 :=
    load4_of_tag (.inl rfl) htag
  have ht : (SBool.not (.cmp .eq .W32 (.load 0 88 4) (.lit 1))).eval
      (E m0 st.data (fun _ ↦ 0) 0) = true := by
    simp only [SBool.eval, Sym.eval, hl]
    decide +kernel
  have hp1 : st1.pc = Host.addrOf (k + NativeRustcVmX64.Vm.KeccakOpen.b94Offset) := by
    simp only [PcOk, ht, ↓reduceIte] at hpc1
    exact hpc1.trans (label_of_infix hp b94_in_code rfl)
  have hb1 := body_unchanged h hsc.body hm1 f1.2.1 f1.2.2.1
  have hbx1 : reg st1.data .rbx = oA m0 :=
    (hm1.regs .rbx (.reg .rbx) (by rw [after_eq e1]; rfl)).trans hsc.bx
  have hwf1 := wf_fold h hb1.fr.kept (vars := fun _ ↦ 0) (ret := 0)
  refine exec_at (infix_of b94_in_code (by simp [b94]) hp) x94 hwf1 nofun hp1
    (body_match h hb1) fun st2 hm2 hpc2 ↦ ?_
  have hb2 := body_unchanged h hb1 hm2 f94.2.1 f94.2.2.1
  have hbx2 : reg st2.data .rbx = oA m0 :=
    (hm2.regs .rbx (.reg .rbx) (by rw [after_eq e94]; rfl)).trans hbx1
  have hax : reg st2.data .rax = 0#64 := hm2.regs .rax _ f94.2.2.2.1
  have hp2 : st2.pc = Host.addrOf (k + NativeRustcVmX64.Vm.KeccakOpen.b95Offset) := by
    simp only [PcOk] at hpc2
    exact hpc2.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.KeccakOpen.b94_next)
  refine (tail_run hp h hp2 hb2.fr hb2.same hbx2).mono fun st' ⟨hp', hsp, hsv, hwr, htag', _, _⟩ ↦ ?_
  have hr := open_none (L := (reg m0 .rdx).toNat) (c := c) (f := (openFirst m0).toNat)
    (n := (openCount m0).toNat) hn
  refine ⟨hp', hsp, ?_, ?_, hwr, hsv⟩
  · rw [hr]
    rw [hax] at htag'
    exact htag'
  · intro sl ws v s' he
    rw [hr] at he
    cases he

end

end NativeRustcVmX64.KeccakGkr.KeccakOpen
