module

public import NativeRustcVmX64.Whir.WhirLevels.Final
public import NativeRustcVmX64.Whir.WhirLevels.Next
public import NativeRustcVmX64.Code.Vm.FinalLevel.Names
public import NativeRustcVmX64.Code.Vm.FoldRounds.Names
public import NativeRustcVmX64.Code.Vm.NextLevel.Names
public import NativeRustcVmX64.Code.Vm.WhirLevels.Names

/-!
# `whir_levels` on x86-64

**`whirLevels_spec`**: AL becomes `whirLevels logN laneFolds b 0 levels`'s `Some`/`None`, the
`TState` its next state, given `fold_rounds`', `next_level`'s and `final_level`'s contracts. The
prologue (`entry`) keeps the arguments in the frame's words and RBX, R12, R13, R15, RBP; the loop
at `NativeRustcVmX64.Vm.WhirLevels.label_1` runs a level's fold rounds (`fold_step`), computes `μ` and tests for the last
level (`mu_step`), then either calls `next_level` and goes on with the next level (`next_step`) or
restores the registers and jumps to `final_level` (`final_tail`), whose stack argument is the
function's own; a `None` returns `0` (`none_exit`). Model: `whirLevels_single`,
`whirLevels_cons_cons`.
-/

namespace NativeRustcVmX64.Whir.Levels.WL

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmX64.Transcript NativeRustcVm.Whir LeanVM.Parameters NativeRustcVmX64.Whir.Levels
open NativeRustcVmX64.Vm.WhirLevels

public section

variable [Host] {k0 : Nat}

/-- **`whir_levels`' contract.** -/
theorem whirLevels_spec (hp : Placed code k0)
    (hfr : ∀ a s w, Spec (Labels.label NativeRustcVmX64.Vm.FoldRounds.entryLabel) (FoldRoundsPre a s w)
      (FoldRoundsPost a s w))
    (hnl : ∀ a s level w rounds, Spec (Labels.label NativeRustcVmX64.Vm.NextLevel.entryLabel)
      (NextLevelPre a s level w rounds) (NextLevelPost a s level w rounds))
    (hfl : ∀ a s level ba b w rounds, Spec (Labels.label NativeRustcVmX64.Vm.FinalLevel.entryLabel)
      (FinalLevelPre a s level ba b w rounds) (FinalLevelPost a s level b w rounds))
    (a : DecArea) (s : TState) (levels : List Whir.Level) (ba : BasisAddrs) (b : BasisW)
    (claim : EW) :
    Spec (Labels.label NativeRustcVmX64.Vm.WhirLevels.entryLabel) (WhirLevelsPre a s levels ba b claim)
      (WhirLevelsPost a s levels b claim) := by
  intro m0 h
  obtain ⟨rate, c⟩ := Ctx.of_pre h
  rw [show Labels.label NativeRustcVmX64.Vm.WhirLevels.entryLabel = Host.addrOf (k0 + NativeRustcVmX64.Vm.WhirLevels.b0Offset) from hp.label NativeRustcVmX64.Vm.WhirLevels.entry_at]
  let I : Nat → MachineState → Prop := fun n st ↦ ∃ kk s' w, n = levels.length - kk ∧
    st.pc = Host.addrOf (k0 + NativeRustcVmX64.Vm.WhirLevels.b1Offset) ∧ Head a s levels b claim m0 kk s' w st.data
  have hloop : ∀ {n : Nat} {st : MachineState}, I n st →
      Eventually (step1 Host.exe) (Goal a s levels b claim m0) st := by
    refine Sym.loop I fun n st ⟨kk, s', w, hn, hpc, hh⟩ ↦ ?_
    refine Eventually.bind (fold_step hp hfr c hpc hh) fun st1 h1 ↦ ?_
    rcases h1 with h1 | ⟨hpc1, s1, w1, rs1, hm1⟩
    · exact .done _ (Or.inl h1)
    refine Eventually.bind (mu_step hp c hpc1 hm1) fun st2 ⟨hmm, h2⟩ ↦ ?_
    rcases h2 with ⟨hlast, hpc2⟩ | ⟨hnext, hpc2⟩
    · exact Eventually.mono (final_tail hp hfl c hpc2 hmm hlast) fun _ h ↦ Or.inl h
    · refine Eventually.mono (next_step hp hnl c hpc2 hmm hnext) fun st3 h3 ↦ ?_
      rcases h3 with h3 | ⟨hpc3, s3, w3, hh3⟩
      · exact Or.inl h3
      · exact Or.inr ⟨levels.length - (kk + 1), by have := hh.lt; omega, kk + 1, s3, w3, rfl,
          hpc3, hh3⟩
  exact Eventually.bind (entry hp c) fun st ⟨hpc, hh⟩ ↦ hloop ⟨0, s, _, rfl, hpc, hh⟩

end

end NativeRustcVmX64.Whir.Levels.WL
