module

public import NativeRustcVmX64.Sumcheck.Climb.Loop
public import NativeRustcVmX64.Code.Vm.Climb.Names
public import NativeRustcVmX64.Code.Vm.HashPair.Names

/-!
# `climb` on x86-64

**`climb_spec`**: the entry (`b0`: the prologue, the node copied to the accumulator, the output's
address saved; with no level straight to the exit, else `b1` sets the loop's registers), the loop
over the path's levels (`loop_spec`), the exit (`b12`: the accumulator copied to the output, the
registers restored); the output holds `climb node q path` (`ClimbPost`).
-/

namespace NativeRustcVmX64.Sumcheck.Climb

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.Climb NativeRustcVmX64.Transcript
open NativeVm.Model LeanVM.Protocol NativeRustcVm.Sumcheck NativeRustcVm.Transcript

public section

variable [Host] {N : Digest} {P : Array Digest} {m0 : MachineData} {k : Nat}

/-- The entry's environment: the frame, the node. -/
abbrev entryEnv (m0 : MachineData) : Env := frameEnv m0 m0 160 [(reg m0 .rsi, 32)] (fun _ ↦ 0) 0

/-- What the entry's blocks leave (`EntryOk`): the frame with the node as the accumulator. -/
theorem fr_entry (hpre : ClimbPre N P m0) (hwf : (entryEnv m0).WF) {S : SState}
    (hS : EntryOk S) {d : MachineData} (hm : Match (entryEnv m0) S d) : Fr m0 N d := by
  have g := Geo.of_pre hpre
  obtain ⟨hpro, hW, hout, hws⟩ := hS
  refine ⟨Frame.of_prologue Frame.entry hwf hm hpro slots_le slots_cs, ?_, ?_, ?_⟩
  · exact wordsAt_written hm (r := 0) rfl (by omega) hW fun i hi ↦
      load_ofMachine (o := 8 * i) (b := reg m0 .rsi) rfl
        (wordsAt_iff.mp hpre.2.2.2.2.1 i (by simpa using hi))
  · exact wordAt_write hm (r := 0) (o := 72) (v := .reg .rdi) rfl (by omega) hout
  · exact SameOutside.mono (sameOutside_low hwf hm (r := 0) rfl (hi := 160) (by omega) hws)
      fun q hq ↦ g.inRange_stack hq

/-- **The entry**: at the exit with the node as the accumulator when the path is empty, else at
the head of level `0`. -/
theorem entry_spec (hp : Placed code k) (hpre : ClimbPre N P m0) :
    Eventually (step1 Host.exe)
      (fun st ↦ (st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.Climb.b12Offset) ∧ P.size = 0 ∧ Fr m0 N st.data) ∨
        (st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.Climb.b6Offset) ∧ Inv m0 N P 0 st.data))
      ⟨m0, Host.addrOf (k + NativeRustcVmX64.Vm.Climb.b0Offset)⟩ := by
  have g := Geo.of_pre hpre
  have hst := hpre.1
  have hsz : P.size = (reg m0 .r8).toNat := hpre.2.2.2.1
  have hfnw := frame_noWrap (F := 160) hst (by rw [climbStack_eq]; omega)
  have hap := g.apart_of_stack hpre.2.2.2.2.2.2.2.2.2.2.1 (o := 0) (k := 168) (by omega)
    (by omega)
  rw [off_zero] at hap
  have hwf : (entryEnv m0).WF :=
    frame_wf ⟨frame_mapped hst (by rw [climbStack_eq]; omega), hfnw⟩
      (fun x hx ↦ by
        rw [List.mem_singleton] at hx; subst hx
        exact ⟨by simpa using hpre.2.2.2.2.1.mapped, hpre.2.2.2.2.2.2.1⟩)
      (List.pairwise_pair.mpr (Apart.symm' hap))
  have hm : Match (entryEnv m0) entryS m0 :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨match_rsp, known_ptr rfl rfl, trivial⟩ trivial trivial
      trivial
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) exit_b0 hwf nofun hm
    fun st0 hm0 hpc0 ↦ ?_
  have hc0 : c0.eval (entryEnv m0) = decide (P.size = 0) := by
    simp only [c0, SBool.eval, Sym.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64,
      BitVec.and_self, Env.ofMachine_regs]
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, hsz, ← BitVec.toNat_inj]
    rfl
  simp only [PcOk, hc0] at hpc0
  by_cases h0 : P.size = 0
  · simp only [h0, decide_true, ite_true] at hpc0
    exact .done _ (Or.inl ⟨hpc0.trans (hp.label NativeRustcVmX64.Vm.Climb.label_9_at), h0, fr_entry hpre hwf ok_b0 hm0⟩)
  · simp only [h0, decide_false, Bool.false_eq_true, ite_false] at hpc0
    refine exec_at (infix_of b1_in_code (by simp [b1]) hp) exit_b1 hwf nofun
      (hpc0.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.Climb.b0_next)) hm0 fun st1 hm1 hpc1 ↦ ?_
    obtain ⟨hok, hr12, hr13, hr14, hr15, hrbp, hrbx⟩ := ok_b1
    simp only [PcOk] at hpc1
    refine .done _ (Or.inr ⟨hpc1.trans (hp.label NativeRustcVmX64.Vm.Climb.label_2_at), fr_entry hpre hwf hok hm1,
      by omega, hm1.regs .r12 _ hr12, ?_, ?_, hm1.regs .r15 _ hr15,
      (hm1.regs .rbp _ hrbp).trans (eval_ptr0 8), (hm1.regs .rbx _ hrbx).trans (eval_ptr0 40)⟩)
    · rw [show reg st1.data .r13 = _ from hm1.regs .r13 _ hr13]; rfl
    · rw [show reg st1.data .r14 = _ from hm1.regs .r14 _ hr14, hsz]; rfl

/-- **The exit**: the accumulator `D` copied to the output, the registers restored, `ret`. -/
theorem exit_spec (hp : Placed code k) (hpre : ClimbPre N P m0) {D : Digest} {m : MachineData}
    (hfr : Fr m0 D m) :
    Eventually (step1 Host.exe)
      (fun st ↦ st.pc = retOf m0 ∧ rspOf st.data = rspOf m0 + 8#64 ∧
        NativeRustcVm.WordsAt st.data.dmem (reg m0 .rdi) D.toList ∧
        NativeRustcVm.SameOutside m0.dmem st.data.dmem (fun p ↦
          NativeRustcVm.InRange (reg m0 .rdi) 32 p ∨
            NativeRustcVm.InRange (stackBelow m0 climbStack) climbStack p) ∧ Saved m0 st.data)
      ⟨m, Host.addrOf (k + NativeRustcVmX64.Vm.Climb.b12Offset)⟩ := by
  have g := Geo.of_pre hpre
  have hst := hpre.1
  have hfnw := frame_noWrap (F := 160) hst (by rw [climbStack_eq]; omega)
  have hap := g.apart_of_stack hpre.2.2.2.2.2.2.2.2.2.2.2.2.1 (o := 0) (k := 168) (by omega)
    (by omega)
  rw [off_zero] at hap
  let env := frameEnv m0 m 160 [(reg m0 .rdi, 32)] (fun _ ↦ 0) 0
  have hwf : env.WF :=
    frame_wf ⟨Mapped.keeps (frame_mapped hst (by rw [climbStack_eq]; omega)) hfr.frame.kept,
      hfnw⟩
      (fun x hx ↦ by
        rw [List.mem_singleton] at hx; subst hx
        exact ⟨Mapped.keeps hpre.2.2.2.2.2.2.2.2.1 hfr.frame.kept, hpre.2.2.2.2.2.2.2.2.2.1⟩)
      (List.pairwise_pair.mpr (Apart.symm' hap))
  have hal : (Sym.load 0 72 8).eval env = env.base 1 + BitVec.ofInt 64 0 := by
    rw [ofInt_zero64, BitVec.add_zero]
    exact load_ofMachine (o := 72) rfl hfr.out
  have hm : Match env exitS m :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hfr.frame.rsp_eval, trivial⟩ trivial trivial
      ⟨hal, trivial⟩
  refine exec_then (infix_of b12_in_code (by simp [b12]) hp) exit_b12 hwf nofun hm
    fun st hm' hpc ↦ ?_
  obtain ⟨hepi, hW, hws⟩ := ok_b12
  obtain ⟨hsv, hrsp⟩ := Frame.epilogue hfr.frame hwf hm' hepi
  simp only [PcOk, Sym.eval] at hpc
  refine .done _ ⟨hpc.trans (hfr.frame.load_ret hst (by rw [climbStack_eq]; omega)), hrsp, ?_,
    ?_, hsv⟩
  · have := wordsAt_written hm' (r := 1) (o := 0) rfl (by omega) hW (D := D) fun i hi ↦
      load_ofMachine (o := 8 + 8 * i) rfl (by
        rw [← off_off]; exact wordsAt_iff.mp hfr.acc i (by simpa using hi))
    rwa [off_zero] at this
  · refine SameOutside.mono (hfr.same.trans (sameOutside_region hwf hm' (r := 1) rfl hws))
      fun q hq ↦ ?_
    rcases hq with hq | hq
    · exact Or.inr hq
    · exact Or.inl hq

/-- **`climb`'s contract.** -/
theorem climb_spec (hp : Placed code k)
    (hhp : Spec (Labels.label NativeRustcVmX64.Vm.HashPair.entryLabel) HashPairPre HashPairPost) (N : Digest)
    (P : Array Digest) : Spec (Labels.label NativeRustcVmX64.Vm.Climb.entryLabel) (ClimbPre N P) (ClimbPost N P) := by
  intro m0 hpre
  rw [show Labels.label NativeRustcVmX64.Vm.Climb.entryLabel = Host.addrOf (k + NativeRustcVmX64.Vm.Climb.b0Offset) from hp.label NativeRustcVmX64.Vm.Climb.entry_at]
  have fin : ∀ (D : Digest), D = climb N (q0 m0) P → ∀ st : MachineState,
      st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.Climb.b12Offset) → Fr m0 D st.data →
      Eventually (step1 Host.exe) (fun st' ↦ st'.pc = retOf m0 ∧
        rspOf st'.data = rspOf m0 + 8#64 ∧ ClimbPost N P m0 st'.data) st := by
    intro D hD st hpc hfr
    obtain ⟨d, pc⟩ := st
    simp only at hpc
    subst hpc hD
    exact Eventually.mono (exit_spec hp hpre hfr) fun st' ⟨h1, h2, h3, h4, h5⟩ ↦
      ⟨h1, h2, h3, h4, h5⟩
  refine Eventually.bind (entry_spec hp hpre) fun st h ↦ ?_
  rcases h with ⟨hpc, h0, hfr⟩ | ⟨hpc, hinv⟩
  · refine fin N ?_ st hpc hfr
    rw [← climbTo_size, h0]
    rfl
  · obtain ⟨d, pc⟩ := st
    simp only at hpc
    subst hpc
    exact Eventually.bind (loop_spec hp hhp hpre hinv) fun st ⟨hpc, hfr⟩ ↦ fin _ rfl st hpc hfr

end

end NativeRustcVmX64.Sumcheck.Climb
