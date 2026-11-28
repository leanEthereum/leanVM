module

public import NativeRustcVmArm.Sumcheck.QueryOpenings.Exec
public import NativeRustcVmArm.Spec.Sumcheck

/-!
# `TState::query_openings`'s `None` exit

`b7` (`.LTStateQueryOpenings_5`, `k + NativeRustcVmArm.Vm.TStateQueryOpenings.b7Offset`) stores `0` at the output (X19) and runs the epilogue:
where the model rejects, the postcondition holds (`finish_fail`). `Out` is what the function may
change: the output, the `TState`, its stack; `Stk` what it changes before `b6`: its stack, which
keeps the `TState` (`tstate_stk`) and words apart from the stack (`wordsAt_stk`).
-/

namespace NativeRustcVmArm.Sumcheck.QueryOpenings

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.TStateQueryOpenings
open NativeRustcVm.Transcript NativeVm.Model NativeRustcArm NativeRustcVmArm.Transcript

public section

/-- What `query_openings` may change: the output, the `TState`, its stack. -/
abbrev Out (m0 : MachineData) (q : BitVec 64) : Prop :=
  NativeRustcVm.InRange m0.regs.X0.toBitVec 32 q ∨
    NativeRustcVm.InRange m0.regs.X1.toBitVec tstateBytes q ∨
    NativeRustcVm.InRange (stackBelow m0 queryOpeningsStack) queryOpeningsStack q

theorem stack_eq : queryOpeningsStack = 1184 := rfl

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 96 := by decide

/-- What `query_openings` changes before `b6`: its stack. -/
abbrev Stk (m0 : MachineData) (q : BitVec 64) : Prop :=
  NativeRustcVm.InRange (stackBelow m0 queryOpeningsStack) queryOpeningsStack q

theorem stk_noWrap {m0 : MachineData} (hst : StackOk m0 queryOpeningsStack) :
    NativeRustcVm.NoWrap (stackBelow m0 queryOpeningsStack) queryOpeningsStack := by
  show _ + queryOpeningsStack ≤ _
  rw [NativeRustcVmArm.Transcript.toNat_stackBelow hst.2.1]
  have := m0.regs.SP.toNat_lt
  have := hst.2.1
  omega

/-- The frame is in the function's stack. -/
theorem frame_stk {m0 : MachineData} (hst : StackOk m0 queryOpeningsStack) {q : BitVec 64}
    (h : NativeRustcVm.InRange (frameBase m0 96) 96 q) : Stk m0 q :=
  inRange_frame_stack hst.2.1 (by decide) h

variable [Host] {k : Nat}

/-- The `TState` kept where only the stack changed. -/
theorem tstate_stk {a : DecArea} {s : TState} {Q : Array UInt64} {m0 : MachineData}
    (hpre : QueryOpeningsPre a s Q m0) {d : Mem 64} (hk : Keeps m0.dmem d)
    (hs : SameOutside m0.dmem d (Stk m0)) : TStateAt d m0.regs.X1.toBitVec a s :=
  hpre.2.2.1.frame hk (fun _ hq ↦
    ⟨not_inRange_of_apart (Apart.symm' hpre.2.2.2.1.1) (stk_noWrap hpre.1)
        hpre.2.2.1.footprint.1.2 hq,
      not_inRange_of_apart (Apart.symm' hpre.2.2.2.1.2.1) (stk_noWrap hpre.1)
        hpre.2.2.1.footprint.2.1.2 hq⟩) hs

omit [Host] in
/-- Words apart from the stack kept where only the stack changed. -/
theorem wordsAt_stk {m0 : MachineData} (hst : StackOk m0 queryOpeningsStack) {d : Mem 64}
    (hs : SameOutside m0.dmem d (Stk m0)) {p : BitVec 64} {ws : List UInt64}
    (hnw : NativeRustcVm.NoWrap p (8 * ws.length))
    (hA : NativeRustcVm.Apart p (8 * ws.length) (stackBelow m0 queryOpeningsStack)
      queryOpeningsStack)
    (h : NativeRustcVm.WordsAt m0.dmem p ws) : NativeRustcVm.WordsAt d p ws :=
  bytesAt_congr h fun i hi ↦ hs _ fun hq ↦ not_inRange_of_apart hA hnw (stk_noWrap hst)
    (inRange_off_self (by rw [length_flatMap_wordBytes] at hi; exact hi)
      (by unfold NativeRustcVm.NoWrap at hnw; omega)) hq

/-- **`b7`**: `0` at the output, the epilogue; the model's `None`. -/
theorem finish_fail (hp : Placed code k) {a : DecArea} {s : TState} {Q : Array UInt64}
    {m0 : MachineData} (hpre : QueryOpeningsPre a s Q m0)
    (hnone : (queryOpenings m0.regs.X2.toNat Q).run s = none) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.TStateQueryOpenings.b7Offset)) (hf : Frame m0 96 slots st.data)
    (hx19 : st.data.regs.X19 = m0.regs.X0) (hso : SameOutside m0.dmem st.data.dmem (Out m0)) :
    Eventually (step1 Host.exe)
      (fun st' ↦ st'.pc = retOf m0 ∧ QueryOpeningsPost a s Q m0 st'.data) st := by
  obtain ⟨hst, -, -, -, -, -, -, -, -, hout, -⟩ := hpre
  set out := m0.regs.X0.toBitVec
  have hn : queryOpeningsStack ≤ m0.regs.SP.toNat := hst.2.1
  have hfnw : (frameBase m0 96).toNat + 96 ≤ 2 ^ 64 := frame_noWrap (by rw [stack_eq] at hn; omega)
  have hOF : NativeRustcVm.Apart out 32 (frameBase m0 96) 96 := apart_frame hout.2.2.2.2.1 hn (by decide)
  have hOF' : out.toNat + 32 ≤ (frameBase m0 96).toNat ∨ (frameBase m0 96).toNat + 96 ≤ out.toNat :=
    hOF
  have hon : out.toNat + 32 ≤ 2 ^ 64 := hout.2.1
  have hwf : (frameEnv m0 st.data 96 [(out, 8)]).WF :=
    Env.wf_of ⟨⟨Mapped.keeps (frame_mapped (F := 96) hst (by decide)) hf.kept, hfnw⟩,
      ⟨Mapped.keeps (fun i hi ↦ hout.1 i (by omega)) hf.kept, by show out.toNat + 8 ≤ 2 ^ 64; omega⟩,
      trivial⟩ (List.pairwise_pair.mpr (by
        show (frameBase m0 96).toNat + 96 ≤ out.toNat ∨ out.toNat + 8 ≤ (frameBase m0 96).toNat
        omega))
  have hm : Match (frameEnv m0 st.data 96 [(out, 8)]) failS st.data :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hst (by decide) (by decide), rfl, nofun, trivial⟩
      (by rw [hf.sp]; exact (eval_ptr rfl).symm)
      ⟨known_ptr rfl (by show st.data.regs.X19.toBitVec = _; rw [hx19]), trivial⟩ trivial trivial
      trivial
  refine exec_at (infix_of b7_in_code (by simp [b7]) hp) run_b7 hwf hpc hm fun st1 hm1 hpc1 => ?_
  obtain ⟨hepi, hw0, hws⟩ := after_eq run_b7 ▸ ok_b7
  obtain ⟨hsv, hsl⟩ := Frame.epilogue hf hwf hm1 hepi
  have hx30 : st1.data.regs.X30 = m0.regs.X30 := hsl (32, .X30) (List.mem_cons_self ..)
  have h0 := wordAt_write hm1 (r := 1) (o := 0) (b := out) (sz := 8) rfl (by decide) hw0
  rw [off_zero] at h0
  have hs1 : SameOutside st.data.dmem st1.data.dmem (NativeRustcVm.InRange out 8) :=
    sameOutside_region hwf hm1 rfl hws
  refine .done _ ⟨by simp only [PcOk] at hpc1; rw [hpc1]; simp only [retOf, hx30], ?_, ?_, ?_, hsv⟩
  · rw [hnone]
    exact h0
  · intro x s' h
    rw [hnone] at h
    cases h
  · intro q hq
    rw [hs1 q fun h ↦ hq (Or.inl (inRange_mono h (by omega)))]
    exact hso q hq

end

end NativeRustcVmArm.Sumcheck.QueryOpenings
