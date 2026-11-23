module

public import NativeRustcVmX64.Sumcheck.QueryOpenings.Exec
public import NativeRustcVmX64.Spec.Sumcheck

/-!
# `TState::query_openings`'s `None` exit (x86-64)

`b6` (`NativeRustcVmX64.Vm.TStateQueryOpenings.label_4`, `k + NativeRustcVmX64.Vm.TStateQueryOpenings.b6Offset`) stores `0` at the output (R14) and `b7` runs the
epilogue: where the model rejects, the postcondition holds (`finish_fail`). `Out` is what the
function may change: the output, the `TState`, its stack; `Stk` what it changes before `b5`: its
stack, which keeps the `TState` (`tstate_stk`) and words apart from the stack (`wordsAt_stk`).
-/

namespace NativeRustcVmX64.Sumcheck.QueryOpenings

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.TStateQueryOpenings
open NativeRustcVm.Transcript NativeVm.Model NativeRustcVmX64.Transcript NativeRustcVmX64.Sumcheck

public section

/-- What `query_openings` may change: the output, the `TState`, its stack. -/
abbrev Out (m0 : MachineData) (q : BitVec 64) : Prop :=
  NativeRustcVm.InRange (reg m0 .rdi) 32 q ∨ NativeRustcVm.InRange (reg m0 .rsi) tstateBytes q ∨
    NativeRustcVm.InRange (stackBelow m0 queryOpeningsStack) queryOpeningsStack q

/-- What `query_openings` changes before `b5`: its stack. -/
abbrev Stk (m0 : MachineData) (q : BitVec 64) : Prop :=
  NativeRustcVm.InRange (stackBelow m0 queryOpeningsStack) queryOpeningsStack q

theorem stack_eq : queryOpeningsStack = 1280 := rfl

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 96 := by decide

theorem slots_cs : ∀ p ∈ slots, calleeSaved p.2 = true := by decide

theorem slots_ge : ∀ p ∈ slots, 48 ≤ p.1 := by decide

section
variable [Labels]

/-- The function's context. -/
theorem ctx {a : DecArea} {s : TState} {Q : Array UInt64} {m0 : MachineData}
    (hpre : QueryOpeningsPre a s Q m0) : Ctx m0 (reg m0 .rsi) a queryOpeningsStack 96 :=
  ⟨hpre.1, hpre.2.1, hpre.2.2.2.1, hpre.2.2.1.footprint, by decide⟩

omit [Labels] in
/-- The frame is in the function's stack. -/
theorem frame_stk {m0 : MachineData} (hst : StackOk m0 queryOpeningsStack) {q : BitVec 64}
    (h : NativeRustcVm.InRange (stackBelow m0 96) 96 q) : Stk m0 q :=
  inRange_frame_stack hst.2.1 hst.1 (by decide) h

/-- The `TState` kept where only the stack changed. -/
theorem tstate_stk {a : DecArea} {s : TState} {Q : Array UInt64} {m0 : MachineData}
    (hpre : QueryOpeningsPre a s Q m0) {d : Mem 64} (hk : Kept m0.dmem d)
    (hs : NativeRustcVm.SameOutside m0.dmem d (Stk m0)) : TStateAt d (reg m0 .rsi) a s :=
  hpre.2.2.1.frame hk (fun _ hq ↦ (ctx hpre).stack_not_t hq) hs

omit [Labels] in
/-- Words apart from the stack kept where only the stack changed. -/
theorem wordsAt_stk {m0 : MachineData} (hst : StackOk m0 queryOpeningsStack) {d : Mem 64}
    (hs : NativeRustcVm.SameOutside m0.dmem d (Stk m0)) {p : BitVec 64} {ws : List UInt64}
    (hnw : NativeRustcVm.NoWrap p (8 * ws.length))
    (hA : NativeRustcVm.Apart p (8 * ws.length) (stackBelow m0 queryOpeningsStack)
      (queryOpeningsStack + 8))
    (h : NativeRustcVm.WordsAt m0.dmem p ws) : NativeRustcVm.WordsAt d p ws :=
  bytesAt_congr h fun i hi ↦ hs _ fun hq ↦ not_inRange_of_apart hA hnw (noWrap_stackBelow hst)
    (inRange_off_self (by rw [length_flatMap_wordBytes] at hi; exact hi)
      (by unfold NativeRustcVm.NoWrap at hnw; omega)) (inRange_mono hq (by omega))

end

variable [Host] {k : Nat}

/-- **`b6`, `b7`**: `0` at the output, the epilogue; the model's `None`. -/
theorem finish_fail (hp : Placed code k) {a : DecArea} {s : TState} {Q : Array UInt64}
    {m0 : MachineData} (hpre : QueryOpeningsPre a s Q m0)
    (hnone : (queryOpenings (reg m0 .rdx).toNat Q).run s = none) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.TStateQueryOpenings.b6Offset)) (hf : Frame m0 96 slots 8 st.data)
    (h14 : reg st.data .r14 = reg m0 .rdi)
    (hso : NativeRustcVm.SameOutside m0.dmem st.data.dmem (Out m0)) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = retOf m0 ∧
      rspOf st'.data = rspOf m0 + 8#64 ∧ QueryOpeningsPost a s Q m0 st'.data) st := by
  have hst := hpre.1
  have hout := hpre.2.2.2.2.2.2.2.2.2.1
  set out := reg m0 .rdi
  have hn : queryOpeningsStack ≤ (rspOf m0).toNat := hst.1
  have hfnw : NativeRustcVm.NoWrap (stackBelow m0 96) (96 + 8) := frame_noWrap hst (by decide)
  have hoF : NativeRustcVm.Apart out 32 (stackBelow m0 96) (96 + 8) :=
    apart_frame hout.2.2.2.2.1 hn (by decide)
  have hwf := frame_wf (m0 := m0) (d := st.data) (F := 96) (rest := [(out, 32)])
    (vars := fun _ ↦ 0) (ret := 0)
    ⟨Mapped.keeps (frame_mapped hst (by decide)) hf.kept, hfnw⟩
    (by
      intro x hx
      rw [List.mem_singleton] at hx
      subst hx
      exact ⟨Mapped.keeps hout.1 hf.kept, hout.2.1⟩)
    (List.pairwise_pair.mpr (Apart.symm' hoF))
  refine exec_at (infix_of b6_in_code (by simp [b6]) hp) exit_b6 hwf nofun hpc
    (match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hf.rsp_eval, known_ptr rfl h14, trivial⟩ trivial
      trivial trivial) fun st1 hm1 hpc1 => ?_
  refine exec_at (infix_of b7_in_code (by simp [b7]) hp) exit_b7f hwf nofun
    (hpc1.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.TStateQueryOpenings.b6_next)) hm1 fun st2 hm2 hpc2 => ?_
  obtain ⟨hepi, hw0, hws⟩ := ok_fail
  obtain ⟨hsv, hrsp⟩ := Frame.epilogue hf hwf hm2 hepi
  have ht := wordAt_write hm2 (r := 1) (o := 0) (b := out) (sz := 32) rfl (by decide) hw0
  rw [off_zero] at ht
  have hs2 := sameOutside_region hwf hm2 (r := 1) rfl hws
  simp only [PcOk] at hpc2
  refine .done _ ⟨by rw [hpc2]; exact hf.load_ret hst (by decide), hrsp, ?_, ?_, ?_, hsv⟩
  · rw [hnone]; exact ht
  · rw [hnone]; intro x s' h; cases h
  · intro q hq
    rw [hs2 q fun h ↦ hq (Or.inl h)]
    exact hso q hq

end

end NativeRustcVmX64.Sumcheck.QueryOpenings
