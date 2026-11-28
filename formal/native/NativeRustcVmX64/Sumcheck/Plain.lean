module

public import NativeRustcVmX64.Sumcheck.Plain.Tail
public import NativeRustcVmX64.Code.Vm.PolyEval.Names
public import NativeRustcVmX64.Code.Vm.SpongeWSqueeze.Names
public import NativeRustcVmX64.Code.Vm.SumcheckOfSumcheckPlain.Names
public import NativeRustcVmX64.Code.Vm.TStateSumcheckRoundPoly.Names

/-!
# `TState::sumcheck` with `sumcheck_plain`'s closure on x86-64

**`sumcheckPlain_spec`**: the entry, the loop over the slots (a round each: `head_spec`,
`tail_spec`), the exit; the output holds `sumcheckPlain claim count n`'s claim, the slots its
challenges, the `TState` its state (`SumcheckPlainPost`).
-/

namespace NativeRustcVmX64.Sumcheck.Plain

open NativeRustcX64 NativeRustcVmX64.Vm.SumcheckOfSumcheckPlain
open NativeVm.Model NativeRustcVm.Transcript

public section

variable [Host] {k : Nat}

/-- **The loop**: from the head, the exit on a rejection or `.L5` after the last round. -/
theorem loop_spec (hp : Placed code k)
    (hrp : ∀ a s e, Spec (Labels.label NativeRustcVmX64.Vm.TStateSumcheckRoundPoly.entryLabel) (RoundPolyPre a s e) (RoundPolyPost a s e))
    (hsq : ∀ sp, Spec (Labels.label NativeRustcVmX64.Vm.SpongeWSqueeze.entryLabel) (SqueezePre sp) (SqueezePost sp))
    (hpe : Spec (Labels.label NativeRustcVmX64.Vm.PolyEval.entryLabel) PolyEvalPre PolyEvalPost)
    {a : DecArea} {s : TState} {m0 : MachineData} (hpre : SumcheckPlainPre a s m0) {i : Nat}
    {m : MachineData} (hi : Inv a s m0 i m) :
    Eventually (step1 Host.exe) (Goal a s m0 k) ⟨m, Host.addrOf (k + NativeRustcVmX64.Vm.SumcheckOfSumcheckPlain.b2Offset)⟩ := by
  refine Sym.loop (fun n st ↦ st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SumcheckOfSumcheckPlain.b2Offset) ∧
      ∃ i, nP m0 - i = n ∧ Inv a s m0 i st.data) (fun n st ⟨hpc, i, hn, hi⟩ ↦ ?_)
    ⟨rfl, i, rfl, hi⟩
  obtain ⟨d, pc⟩ := st
  simp only at hpc
  subst hpc hn
  have hl := hi.lt
  refine Eventually.bind (head_spec hp hrp hpre hi) fun st h ↦ ?_
  rcases h with h | ⟨hpc, xs, msg, s1, hmid⟩
  · exact Eventually.done _ (.inl h)
  obtain ⟨d', pc'⟩ := st
  simp only at hpc
  subst hpc
  refine Eventually.mono (tail_spec hp hsq hpe hpre hmid) fun st h ↦ ?_
  rcases h with h | ⟨hpc, hinv⟩
  · exact .inl h
  · exact .inr ⟨nP m0 - (i + 1), by omega, hpc, i + 1, rfl, hinv⟩

/-- **`sumcheck` with `sumcheck_plain`'s closure: its contract.** -/
theorem sumcheckPlain_spec (hp : Placed code k)
    (hrp : ∀ a s e, Spec (Labels.label NativeRustcVmX64.Vm.TStateSumcheckRoundPoly.entryLabel) (RoundPolyPre a s e) (RoundPolyPost a s e))
    (hsq : ∀ sp, Spec (Labels.label NativeRustcVmX64.Vm.SpongeWSqueeze.entryLabel) (SqueezePre sp) (SqueezePost sp))
    (hpe : Spec (Labels.label NativeRustcVmX64.Vm.PolyEval.entryLabel) PolyEvalPre PolyEvalPost)
    (a : DecArea) (s : TState) :
    Spec (Labels.label NativeRustcVmX64.Vm.SumcheckOfSumcheckPlain.entryLabel) (SumcheckPlainPre a s) (SumcheckPlainPost a s) := by
  intro m0 hpre
  rw [show Labels.label NativeRustcVmX64.Vm.SumcheckOfSumcheckPlain.entryLabel = Host.addrOf (k + NativeRustcVmX64.Vm.SumcheckOfSumcheckPlain.b0Offset) from hp.label NativeRustcVmX64.Vm.SumcheckOfSumcheckPlain.entry_at]
  have fin : ∀ st : MachineState, Goal a s m0 k st →
      Eventually (step1 Host.exe)
        (fun st' ↦ st'.pc = retOf m0 ∧ rspOf st'.data = rspOf m0 + 8#64 ∧
          SumcheckPlainPost a s m0 st'.data) st := by
    intro st h
    rcases h with h | ⟨hpc, hd⟩
    · exact Eventually.done _ h
    · obtain ⟨d, pc⟩ := st
      simp only at hpc
      subst hpc
      exact exit_done hp hpre hd
  refine Eventually.bind (entry_spec hp hpre) fun st h ↦ ?_
  rcases h with ⟨hpc, hd⟩ | ⟨hpc, hinv⟩
  · exact fin st (.inr ⟨hpc, hd⟩)
  · obtain ⟨d, pc⟩ := st
    simp only at hpc
    subst hpc
    exact Eventually.bind (loop_spec hp hrp hsq hpe hpre hinv) fin

end

end NativeRustcVmX64.Sumcheck.Plain
