module

public import NativeRustcVmX64.Layout.StackOffsets.Step
public import NativeRustcVmX64.Code.Vm.BitLength.Names

/-!
# `stack_offsets` on x86-64: the main loop to its end, the return (`b23` to `b25`)

The main loop runs to a failure or its end (`loop`). At the end `b23` takes the total's
`bit_length(total - 1)` (`log2Ceil`), `b24` returns it in RDX with RAX = `1`, the epilogue `b25`
returns (`finish`).
-/

namespace NativeRustcVmX64.Layout.StackOffsets

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVm.Transcript
open NativeRustcVmX64.Vm.StackOffsets NativeRustcVmX64.Layout.BuildFrame
open NativeRustcVm.Layout (OffsetsFit)

public section

/-- `total - 1`, saturating (`subq $1`, `cmovae`). -/
theorem satsub_eval [Labels] (env : Env) {t : Nat} (h : ((Sym.reg .rdx).eval env).toNat = t) :
    ((Sym.ite (SBool.cmp .ult .W64 (.reg .rdx) (.lit 1)).not
      (.bin .sub .W64 (.reg .rdx) (.lit 1)) (.lit 0)).eval env).toNat = t - 1 := by
  show (if (SBool.not (SBool.cmp .ult .W64 (.reg .rdx) (.lit 1))).eval env = true then
    BinOp.apply .sub .W64 ((Sym.reg .rdx).eval env) (BitVec.ofNat 64 1)
    else BitVec.ofNat 64 0).toNat = _
  have h1 : ((Sym.lit 1).eval env).toNat = 1 := rfl
  rw [SBool.eval, ult_eval, h, h1]
  by_cases ht : t < 1
  · have : t = 0 := by omega
    subst this
    rfl
  · rw [decide_eq_false ht]
    simp only [Bool.not_false, ↓reduceIte, BinOp.apply, low_W64, ext_W64]
    rw [BitVec.toNat_sub, h, show (1#64).toNat = 1 from rfl]
    have := ((Sym.reg .rdx).eval env).isLt
    omega

variable [Host] {k : Nat} {m0 : MachineData}

/-- **The main loop**, to a failure or its end. -/
theorem loop (hp : Placed code k) (hpre : StackOffsetsPre m0) (hcap : n m0 ≤ cap m0) {j : Nat}
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.StackOffsets.b18Offset)) (hL : Loop m0 j st.data) :
    Eventually (step1 Host.exe) (fun s ↦ Fail k m0 s ∨ End k m0 s) st :=
  Sym.loop (fun r s ↦ s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.StackOffsets.b18Offset) ∧ ∃ j, n m0 - j = r ∧ Loop m0 j s.data)
    (fun r s ⟨hpc, j, hr, hL⟩ ↦ Eventually.mono (step hp hpre hcap hpc hL) fun s' h ↦ by
      rcases h with h | h | ⟨hpc', hL'⟩
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr ⟨n m0 - (j + 1), by have := hL'.le; omega, hpc', j + 1, rfl, hL'⟩)
    ⟨hpc, j, rfl, hL⟩

/-- **The end** `b23` to `b25`: `bit_length(total - 1)` and the offsets returned. -/
theorem finish (hp : Placed code k)
    (hbl : Spec (label NativeRustcVmX64.Vm.BitLength.entryLabel) BitLengthPre BitLengthPost) (hpre : StackOffsetsPre m0)
    (hcap : n m0 ≤ cap m0) {st : MachineState} (h : End k m0 st) :
    Eventually (step1 Host.exe) (Post m0) st := by
  obtain ⟨hpc, hL⟩ := h
  have hst : StackOk m0 1344 := hpre.1
  have hoff : OffStack m0 (out m0) (8 * cap m0) 1344 := hpre.2.2.2.2.2.1
  have hno : NativeRustcVm.NoWrap (out m0) (8 * cap m0) := hpre.2.2.2.2.1.2
  obtain ⟨hok, hw23, hdi, hK⟩ := ok_b23
  refine run0 (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.StackOffsets.b23Offset + b23.length)).toBitVec) hst
    (b23_in_code.trans hp.1 (List.cons_ne_nil _ _)) exit_b23 (fun _ _ ↦ rfl) hpc hL.b
    (match0 hL.b) hok fun st1 hm1 hpc1 hb1 ↦ ?_
  have hwf1 := fr_wf0 (vars := fun _ ↦ 0) (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.StackOffsets.b23Offset + b23.length)).toBitVec)
    hL.b hst (by decide)
  have hs1 : NativeRustcVm.SameOutside st.data.dmem st1.data.dmem
      (NativeRustcVm.InRange (stackBelow m0 1328) 8) :=
    sameOutside_low hwf1 hm1 (r := 0) rfl (by decide) hw23
  have hout1 := hL.out.keep hcap hno hs1 fun q h hr ↦
    R_not_frame hst hoff hno hr (inRange_mono h (by decide))
  have hrdi : (reg st1.data .rdi).toNat = (P m0 (n m0)).2 - 1 := by
    show (st1.data.regs.get64 .rdi).toNat = _
    rw [hm1.regs .rdi _ hdi]
    exact satsub_eval _ hL.rdx
  refine call_then hpc1 hbl (hb1.stackOk hst (by decide)) fun st2 hpc2 hrsp2 hpost ↦ ?_
  obtain ⟨hax2, hso2, hsv2⟩ := hpost
  rw [show bitLengthStack = 0 from rfl] at hso2
  have hb2 : B m0 8 st2.data := hb1.call hsv2 hrsp2 hso2 (fun _ h ↦ absurd h not_inRange_zero')
    (fun _ _ _ _ h ↦ not_inRange_zero' h) (fun _ _ h ↦ not_inRange_zero' h)
  have hout2 := hout1.keep hcap hno hso2 fun _ h ↦ absurd h not_inRange_zero'
  obtain ⟨hok24, hmem24, hax24, hdx24, hK24⟩ := ok_b24
  refine step0 hst (b24_in_code.trans hp.1 (List.cons_ne_nil _ _)) exit_b24 nofun
    (hpc2.trans rfl) hb2 hok24 hmem24 fun st3 hm3 hpc3 hb3 hd3 ↦ ?_
  obtain ⟨hok25, hmem25, hK25⟩ := ok_b25
  refine hb3.done hst (by decide) (b25_in_code.trans hp.1 (List.cons_ne_nil _ _)) exit_b25
    hpc3 (match0 hb3) hok25 hmem25 fun st4 hm4 hpc4 hrsp4 hsv4 hd4 ↦
      ⟨hpc4, hrsp4, ?_, fun q hq ↦ by rw [hd4]; exact hb3.same q hq, hsv4⟩
  have hfit : n m0 ≤ cap m0 ∧ OffsetsFit (sizes m0) :=
    ⟨hcap, fit_end (by rw [← hL.rdx]; exact (reg st.data .rdx).isLt)⟩
  split
  · rw [stackOffsets_eq]
    refine ⟨?_, ?_, ?_⟩
    · rw [kreg hm4 hK25 (by simp)]
      exact hm3.regs .rax _ hax24
    · rw [kreg hm4 hK25 (by simp)]
      show (st3.data.regs.get64 .rdx).toNat = _
      rw [hm3.regs .rdx _ hdx24]
      show (reg st2.data .rax).toNat = _
      rw [hax2, hrdi]
      rfl
    · rw [hd4, hd3]
      exact OutAt.words hout2
  · rename_i h; exact absurd hfit h

end

end NativeRustcVmX64.Layout.StackOffsets
