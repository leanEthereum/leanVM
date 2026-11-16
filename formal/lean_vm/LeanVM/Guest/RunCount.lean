/-
  LeanVM.Guest.RunCount

  Counted runs: a run with the number of instructions of each opcode it executes, and the step
  lemmas that build one.
-/

module

public import LeanVM.Guest.Logic

/-!
# Counted runs

`RunC prog L s t c`: some run goes from `s` to `t` executing `c op` instructions of each opcode
`op` (`opcodeCountInRun`). Counted runs compose (`RunC.trans`, the counts adding), are built one
instruction at a time as `Reach` is (`runC_step`, `runC_fallThrough`, `runC_jump`), and a counted
run from the initial to the final registers counts the trace that halts there
(`count_eq_of_runC`), since a run reaches the final registers after one number of steps only
(`run_final_unique`).
-/

namespace LeanVM.Guest

open LeanVM.Parameters LeanVM.Semantics

@[expose] public section

/-- **A counted run**: some run goes from `s` to `t`, executing `c op` instructions of each
opcode `op`. -/
def RunC {κ : ℕ} (prog : LeanIsaProgram) (L : MemoryImage κ) (s t : Registers K) (c : Opcode → ℕ) :
    Prop :=
  ∃ n, run prog L n s = some t ∧ ∀ op, opcodeCountInRun prog L op n s = c op

section

variable {κ : ℕ} {prog : LeanIsaProgram} {L : MemoryImage κ}

/-- Along a run that reaches `t`, the counts of a longer run add. -/
theorem runCount_add_of_run {op : Opcode} : ∀ {n : ℕ} {s t : Registers K}, run prog L n s = some t →
    ∀ m, opcodeCountInRun prog L op (n + m) s = opcodeCountInRun prog L op n s + opcodeCountInRun prog L op m t
  | 0, s, t, h, m => by
    simp only [run_zero, Option.some.injEq] at h
    subst h
    simp [opcodeCountInRun]
  | n + 1, s, t, h, m => by
    have hne := ne_final_of_run_succ h
    rw [run_succ_of_ne_final hne] at h
    obtain ⟨s', hs', h'⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨ins, hins⟩ : ∃ ins, prog.fetch s.pc = some ins := by
      cases hf : prog.fetch s.pc with
      | none => rw [step_eq_none_of_fetch_eq_none hf] at hs'; cases hs'
      | some ins => exact ⟨ins, rfl⟩
    rw [show n + 1 + m = (n + m) + 1 by omega]
    simp only [opcodeCountInRun, hins, hs', runCount_add_of_run h' m]
    omega

theorem RunC.refl (s : Registers K) : RunC prog L s s 0 := ⟨0, rfl, fun _ ↦ rfl⟩

theorem RunC.trans {s t u : Registers K} {c₁ c₂ : Opcode → ℕ} (h₁ : RunC prog L s t c₁)
    (h₂ : RunC prog L t u c₂) : RunC prog L s u (c₁ + c₂) := by
  obtain ⟨m, hm, hcm⟩ := h₁
  obtain ⟨n, hn, hcn⟩ := h₂
  refine ⟨m + n, by rw [run_add, hm]; exact hn, fun op ↦ ?_⟩
  rw [runCount_add_of_run hm, hcm, hcn, Pi.add_apply]

theorem RunC.reach {s t : Registers K} {c : Opcode → ℕ} (h : RunC prog L s t c) : Reach prog L s t :=
  let ⟨n, hn, _⟩ := h
  ⟨n, hn⟩

/-! ## Counted steps -/

/-- One step from a fetched instruction away from the last slot, counting its opcode. -/
theorem runC_step {pc : ℕ} {fp : K} {ins : OffsetInstruction} {r : Registers K}
    (hf : prog.fetch (addressOfIndex pc) = some ins.toLeanIsaInstruction) (hpc : pc < 2 ^
        prog.logSize - 1)
    (h : execute L ⟨addressOfIndex pc, fp⟩ ins.toLeanIsaInstruction = some r) :
    RunC prog L ⟨addressOfIndex pc, fp⟩ r (fun op ↦ if op = ins.toLeanIsaInstruction.opcode
        then 1 else 0) := by
  have hf' : prog.fetch (⟨addressOfIndex pc, fp⟩ : Registers K).pc = some
      ins.toLeanIsaInstruction := hf
  have hs : step prog L ⟨addressOfIndex pc, fp⟩ = some r := by rw [step_of_fetch_eq_some hf', h]
  refine ⟨1, ?_, fun op ↦ ?_⟩
  · rw [run_succ_of_ne (gpow_ne_pcFinal hpc), hs]
    rfl
  · simp only [opcodeCountInRun, hf', hs, add_zero]
    by_cases ho : op = ins.toLeanIsaInstruction.opcode
    · simp [ho]
    · simp [ho, Ne.symm ho]

/-- A non-`JUMP` that `Holds` falls through, counting its opcode. -/
theorem runC_fallThrough {pc : ℕ} {fp : K} {ins : OffsetInstruction}
    (hf : prog.fetch (addressOfIndex pc) = some ins.toLeanIsaInstruction) (hpc : pc < 2 ^
        prog.logSize - 1)
    (hj : ins.isJump = false) (h : Holds L pc fp ins) :
    RunC prog L ⟨addressOfIndex pc, fp⟩ ⟨addressOfIndex (pc + 1), fp⟩ (fun op ↦ if op = ins.toLeanIsaInstruction.opcode then 1 else 0) :=
  runC_step hf hpc ((execute_iff_holds hj).mpr ⟨h, rfl⟩)

/-- A `JUMP` goes where it `JumpsTo`, counting one `JUMP`. -/
theorem runC_jump {pc : ℕ} {fp : K} {oc od of : ℕ} {r : Registers K}
    (hf : prog.fetch (addressOfIndex pc) = some (OffsetInstruction.jump oc od
        of).toLeanIsaInstruction)
    (hpc : pc < 2 ^ prog.logSize - 1) (h : JumpsTo L pc fp oc od of r) :
    RunC prog L ⟨addressOfIndex pc, fp⟩ r (fun op ↦ if op = .jump then 1 else 0) :=
  runC_step hf hpc (execute_jump_iff.mpr h)

/-! ## The final registers -/

/-- A run reaches the final registers after one number of steps only: it halts there. -/
theorem run_final_unique {n m : ℕ} {s : Registers K} (hn : run prog L n s = some (Registers.final prog))
    (hm : run prog L m s = some (Registers.final prog)) : n = m := by
  have key : ∀ {a b : ℕ}, a < b → run prog L a s = some (Registers.final prog) →
      run prog L b s ≠ some (Registers.final prog) := by
    intro a b hab ha hb
    obtain ⟨k, rfl⟩ : ∃ k, b = a + (k + 1) := ⟨b - a - 1, by omega⟩
    rw [run_add, ha] at hb
    change run prog L (k + 1) (Registers.final prog) = _ at hb
    rw [run_succ_of_eq rfl] at hb
    cases hb
  rcases Nat.lt_trichotomy n m with h | h | h
  · exact absurd hm (key h hn)
  · exact h
  · exact absurd hn (key h hm)

/-- **A counted run to the final registers counts the trace that halts there.** -/
theorem count_eq_of_runC {n : ℕ} {c : Opcode → ℕ}
    (hc : RunC prog L Registers.initial (Registers.final prog) c)
    (hn : run prog L n Registers.initial = some (Registers.final prog)) (op : Opcode) :
    (⟨κ, L, n⟩ : Execution prog).opcodeCount op = c op := by
  obtain ⟨m, hm, hcm⟩ := hc
  obtain rfl := run_final_unique hn hm
  exact hcm op

end

end
end LeanVM.Guest
