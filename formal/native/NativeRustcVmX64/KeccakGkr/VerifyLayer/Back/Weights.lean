module

public import NativeRustcVmX64.KeccakGkr.VerifyLayer.Back.WeightsEntry
public import NativeRustcVmX64.KeccakGkr.VerifyLayer.Back.WeightsStore
public import NativeRustcVmX64.Code.Vm.EWMul.Names

/-! # The complete 1600-iteration layer weights loop -/

namespace NativeRustcVmX64.KeccakGkr.VerifyLayer

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model
open NativeRustcVmX64.Vm.VerifyLayer
open NativeRustcVm.Transcript (DecArea)

public section

variable [Host] {m0 : MachineData} {a : DecArea} {s s6 : TState} {c : KeccakClaimW}
  {ch b : EW} {pt lp t : Array EW} {k : Nat}

theorem weights_loop (hp : Placed code k) (hpre : VerifyLayerPre a s c m0)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (hpt : pt.size ≤ 30) (hlp : lp.size = 11) {R : MachineState → Prop}
    (done : ∀ d', Body m0 (wFront m0) 24 d' → WMem m0 a c ch b pt lp t s6 1600 d'.dmem →
      reg d' .r15 = sA m0 → Eventually (step1 Host.exe) R ⟨d', Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b79Offset)⟩) :
    ∀ n j d, 1600 - j = n → WHead m0 a c ch b pt lp t s6 j d →
      Eventually (step1 Host.exe) R ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b74Offset)⟩ := by
  intro n
  induction n with
  | zero =>
    intro j d hn h
    have := h.lt
    omega
  | succ n ih =>
    intro j d hn h
    refine weights_head hp hpre h fun d1 h1 hc1 ha1 hdi1 hsi1 ↦ ?_
    refine weights_four hp hpre hlp h1 hdi1 hsi1 fun d2 h2 hk2 h14_2 h12_2 ↦ ?_
    refine weights_three_index hp hpre h2 ((hk2 .rcx (by simp)).trans hc1)
      ((hk2 .rax (by simp)).trans ha1) fun d3 h3 hk3 ha3 ↦ ?_
    refine weights_three hp hpre hlp h3 ha3
      ((hk3 .rsi (by simp)).trans ((hk2 .rsi (by simp)).trans hsi1))
      fun d4 h4 h14_4 h12_4 he3 ↦ ?_
    refine weights_mul hp hpre hmul hpt hlp h4
      (h14_4.trans ((hk3 .r14 (by simp)).trans h14_2))
      (h12_4.trans ((hk3 .r12 (by simp)).trans h12_2)) he3 fun d5 h5 ↦ ?_
    exact weights_store hp hpre hpt hlp h.lt h5
      (fun d6 h6 ↦ ih (j + 1) d6 (by omega) h6) done

theorem weights_run (hp : Placed code k) (hpre : VerifyLayerPre a s c m0)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {d : MachineData} (h : C6 m0 a c ch b pt lp t s6 d) {R : MachineState → Prop}
    (done : ∀ d', Body m0 (wFront m0) 24 d' → WMem m0 a c ch b pt lp t s6 1600 d'.dmem →
      reg d' .r15 = sA m0 → Eventually (step1 Host.exe) R ⟨d', Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b79Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b69Offset)⟩ :=
  weights_entry hp hpre h fun d' h' ↦ weights_loop hp hpre hmul
    (by rw [h.psz]; exact (claimPt hpre (fun _ h ↦ h) h.body).1) h.lsz done 1600 0 d' rfl h'

end

end NativeRustcVmX64.KeccakGkr.VerifyLayer
