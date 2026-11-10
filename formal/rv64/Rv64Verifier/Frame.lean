import Rv64Verifier.Machine

/-!
# Runs, function contracts, calls and loops

The rules a proof of compiled code composes: runs concatenate (`Steps.trans`) and are determined
by their start (`Steps.det`); a function contract (`FunSpec`) says that from its entry the code
returns to the caller's `ra` within the standard calling convention's frame; a call applies the
callee's contract (`FunSpec.call`); a loop is an invariant with a decreasing measure
(`Steps.loop`).
-/

namespace Rv64Verifier
open RiscvZkvm.Rv64

variable {code : Code}

theorem Steps.zero {s : MachineState} : Steps code 0 s s := rfl

theorem Steps.one {s t : MachineState} (h : step code s = some t) : Steps code 1 s t :=
  ⟨t, h, rfl⟩

theorem Steps.trans {n m : Nat} {s t u : MachineState} (h₁ : Steps code n s t)
    (h₂ : Steps code m t u) : Steps code (n + m) s u := by
  induction n generalizing s with
  | zero => cases h₁; simpa using h₂
  | succ n ih =>
    obtain ⟨s', hs', h₁'⟩ := h₁
    rw [show n + 1 + m = (n + m) + 1 by omega]
    exact ⟨s', hs', ih h₁'⟩

theorem Steps.det {n : Nat} {s t t' : MachineState} (h : Steps code n s t)
    (h' : Steps code n s t') : t = t' := by
  induction n generalizing s with
  | zero => exact h.symm.trans h'
  | succ n ih =>
    obtain ⟨s₁, hs₁, h₁⟩ := h
    obtain ⟨s₂, hs₂, h₂⟩ := h'
    rw [hs₁] at hs₂
    cases hs₂
    exact ih h₁ h₂

/-- `s` reaches `t`. -/
def Reaches (code : Code) (s t : MachineState) : Prop := ∃ n, Steps code n s t

theorem Reaches.refl (s : MachineState) : Reaches code s s := ⟨0, rfl⟩

theorem Reaches.trans {s t u : MachineState} (h₁ : Reaches code s t) (h₂ : Reaches code t u) :
    Reaches code s u :=
  let ⟨_, h₁⟩ := h₁
  let ⟨_, h₂⟩ := h₂
  ⟨_, h₁.trans h₂⟩

/-! ## Function contracts -/

/-- Where a `ret` from `s` lands: `ra` with its low bit cleared, as `JALR` computes it. -/
def returnAddress (s : MachineState) : Word := s.getReg .x1 &&& ~~~1#64

/-- The callee-saved registers of the RISC-V calling convention, `sp` and `s0`..`s11`. -/
def calleeSaved : List Reg :=
  [.x2, .x8, .x9, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27]

/-- The convention's frame: the callee-saved registers keep their values. -/
def Preserves (s t : MachineState) : Prop := ∀ r ∈ calleeSaved, t.getReg r = s.getReg r

/-- A dead end that cannot accept: the machine stops here (a trap, or the `HALT` call), and if it is
the `HALT` call its verdict is not `1`. A panic ends in one (the guest halts with `2`), and so does
a word that does not decode. -/
def Dead (code : Code) (t : MachineState) : Prop :=
  step code t = none ∧ (Halting code t → t.getReg .x10 ≠ 1)

/-- A function's contract: from every state at `entry` satisfying `pre`, the code either returns
to the caller with the callee-saved registers restored and `post` relating entry and exit
states, or reaches a dead end. The memory the function may change is `post`'s to say. -/
def FunSpec (code : Code) (entry : Word) (pre : MachineState → Prop)
    (post : MachineState → MachineState → Prop) : Prop :=
  ∀ s, s.pc = entry → pre s → ∃ t, Reaches code s t ∧
    ((t.pc = returnAddress s ∧ Preserves s t ∧ post s t) ∨ Dead code t)

/-- A call: once the caller's state `c` has jumped to the callee's entry (`c'`), the callee's
contract brings it back to the return address, or to a dead end. -/
theorem FunSpec.call {entry : Word} {pre : MachineState → Prop}
    {post : MachineState → MachineState → Prop} (h : FunSpec code entry pre post)
    {c c' : MachineState} (hjump : Reaches code c c') (hpc : c'.pc = entry) (hpre : pre c') :
    ∃ t, Reaches code c t ∧
      ((t.pc = returnAddress c' ∧ Preserves c' t ∧ post c' t) ∨ Dead code t) := by
  obtain ⟨t, ht, hout⟩ := h c' hpc hpre
  exact ⟨t, hjump.trans ht, hout⟩

/-- A run that reaches a dead end does not halt with `1` from there on. -/
theorem Dead.not_accept {t : MachineState} (h : Dead code t) {n : Nat} :
    ¬ HaltsWith code t n 1 := by
  rintro ⟨u, hu, hhalt, ha0⟩
  cases n with
  | zero => cases hu; exact h.2 hhalt ha0
  | succ n => obtain ⟨_, hs, _⟩ := hu; rw [h.1] at hs; cases hs

/-! ## Loops -/

/-- A loop: an invariant `inv` whose every state either exits to a state satisfying `done`, or
runs to another state of the invariant with a smaller `measure`. -/
theorem Reaches.loop (inv : MachineState → Prop) (measure : MachineState → Nat)
    (done : MachineState → Prop)
    (body : ∀ s, inv s → (∃ t, Reaches code s t ∧ done t) ∨
      (∃ t, Reaches code s t ∧ inv t ∧ measure t < measure s)) :
    ∀ s, inv s → ∃ t, Reaches code s t ∧ done t := by
  intro s hs
  induction h : measure s using Nat.strongRecOn generalizing s with
  | ind m ih =>
    rcases body s hs with ⟨t, hst, ht⟩ | ⟨t, hst, ht, hlt⟩
    · exact ⟨t, hst, ht⟩
    · obtain ⟨u, htu, hu⟩ := ih (measure t) (h ▸ hlt) t ht rfl
      exact ⟨u, hst.trans htu, hu⟩

end Rv64Verifier
