/-
  Rv64mc.Core.LocalRun

  A function's body run as a function, for any instruction set, so that the kernel can evaluate a concrete run
  (`decide`): `Isa.lstep` is one step of an activation at an operation, a label, a jump, a branch or a return, and
  `Isa.lrun k` is `k` of them, stopping once the activation has returned. Each such step is a step of `Isa.step`
  (`lstep_sound`), so a partial judgement at the entry holds at the state a returning run reaches
  (`safeN_of_lrun`): a contract that a concrete run returning in a state outside its postcondition refutes.

  ## Main definitions

  * `Isa.Local`, `Isa.lstep`, `Isa.lrun`, `Isa.lrunReturns`

  ## Main results

  * `Isa.lstep_sound`, `Isa.safeN_of_lrun`
  * `Isa.Contract.not_of_lrun`: a contract refuted by a run that returns outside its postcondition
-/

import Lprog.Contract

namespace Lprog.Isa

variable {I : Isa}

/-- An activation as a run of its body leaves it: its counter (`none` once it has returned), the registers and the
    memory. -/
abbrev Local (I : Isa) : Type := Option Nat × (I.Reg → BitVec 64) × I.M

/-- One step of an activation with return address `ret` and stack top `top`, at an operation, a label, a jump, a
    branch or a return of `body`; `none` at any other instruction, a fault, or an unknown label. -/
def lstep (body : Lcmd I.Op I.Reg) (ret top : BitVec 64) (pc : Nat) (regs : I.Reg → BitVec 64) (m : I.M) :
    Option (Local I) :=
  match body[pc]? with
  | some (.Lopn op) => (I.opn op regs m).map fun x => (some (pc + 1), x.1, x.2)
  | some (.Llabel ..) => some (some (pc + 1), regs, m)
  | some (.Lgoto l) => (labelIdx body l).map fun j => (some j, regs, m)
  | some (.Lcond cnd l) => match I.cond cnd regs m with
    | some true => (labelIdx body l).map fun j => (some j, regs, m)
    | some false => some (some (pc + 1), regs, m)
    | none => none
  | some .Lret => if regs I.link = ret ∧ regs I.sp = top then some (none, regs, m) else none
  | _ => none

/-- `k` steps of `lstep`, stopping once the activation has returned. -/
def lrun (body : Lcmd I.Op I.Reg) (ret top : BitVec 64) : Nat → Local I → Option (Local I)
  | 0, s => some s
  | _ + 1, (none, r, m) => some (none, r, m)
  | k + 1, (some pc, regs, m) => (lstep body ret top pc regs m).bind (lrun body ret top k)

/-- Whether `k` steps of `lrun` from `s` return, in registers and memory satisfying `P`: a check the kernel
    evaluates. -/
def lrunReturns (body : Lcmd I.Op I.Reg) (ret top : BitVec 64) (k : Nat) (s : Local I)
    (P : (I.Reg → BitVec 64) → I.M → Bool) : Bool :=
  match lrun body ret top k s with
  | some (none, r', m') => P r' m'
  | _ => false

theorem lrunReturns_spec {body : Lcmd I.Op I.Reg} {ret top : BitVec 64} {k : Nat} {s : Local I}
    {P : (I.Reg → BitVec 64) → I.M → Bool} (h : lrunReturns body ret top k s P = true) :
    ∃ r' m', lrun body ret top k s = some (none, r', m') ∧ P r' m' = true := by
  unfold lrunReturns at h
  split at h
  · exact ⟨_, _, by assumption, h⟩
  · cases h

/-- The state of a run that `Local` describes, in function `fn` over the stack `rest`. -/
def Local.toState (fn : Nat) (ret top : BitVec 64) (rest : List Frame) : Local I → State I
  | (some pc, r, m) => ⟨⟨fn, pc, ret, top⟩ :: rest, r, m⟩
  | (none, r, m) => ⟨rest, r, m⟩

/-- **A step of `lstep` is a step of the program**, of function `fn` holding the body, with no events. -/
theorem lstep_sound {p : Lprog I.Op I.Reg} {E : Type} {c : Context I E} {fn : Nat} {fd : Lfundef I.Op I.Reg}
    (hp : p[fn]? = some fd) {ret top : BitVec 64} {rest : List Frame} {pc : Nat} {regs : I.Reg → BitVec 64}
    {m : I.M} {x : Local I} (h : lstep fd.body ret top pc regs m = some x) :
    I.step p c ⟨⟨fn, pc, ret, top⟩ :: rest, regs, m⟩ (.ok (x.toState fn ret top rest, [])) := by
  unfold lstep at h
  cases hi : fd.body[pc]? with
  | none => simp [hi] at h
  | some i =>
    rw [hi] at h
    rw [SafeN.step_eq (fr := ⟨fn, pc, ret, top⟩) hp hi]
    cases i <;> simp only [Isa.stepI] at h ⊢
    all_goals (repeat' split at h) <;> (try simp only [Option.map_eq_some_iff] at h) <;>
      (try obtain ⟨_, _, rfl⟩ := h) <;> simp_all [Local.toState, Frame.at]

theorem lrun_none (body : Lcmd I.Op I.Reg) (ret top : BitVec 64) (k : Nat) (r : I.Reg → BitVec 64) (m : I.M) :
    lrun body ret top k (none, r, m) = some (none, r, m) := by
  cases k <;> rfl

/-- **A returning run carries a partial judgement from the entry to the return**, one budget unit a step. -/
theorem safeN_of_lrun {p : Lprog I.Op I.Reg} {E : Type} {c : Context I E} {fn : Nat} {fd : Lfundef I.Op I.Reg}
    (hp : p[fn]? = some fd) {Q : State I → Prop} {ret top : BitVec 64} {rest : List Frame} :
    ∀ (k n pc : Nat) (regs r' : I.Reg → BitVec 64) (m m' : I.M),
      lrun fd.body ret top k (some pc, regs, m) = some (none, r', m') →
      I.SafeN p c (fun _ => True) (n + k) Q ⟨⟨fn, pc, ret, top⟩ :: rest, regs, m⟩ →
      I.SafeN p c (fun _ => True) n Q ⟨rest, r', m'⟩
  | 0, _, _, _, _, _, _, h, _ => by cases h
  | k + 1, n, pc, regs, r', m, m', h, hs => by
    simp only [lrun] at h
    cases hx : lstep fd.body ret top pc regs m with
    | none => rw [hx] at h; cases h
    | some x =>
      rw [hx, Option.bind_some] at h
      have h1 := Ascent.SafeN.next (n := n + k) trivial ⟨[], lstep_sound (c := c) (rest := rest) hp hx⟩ hs
      obtain ⟨_ | pc', r, m1⟩ := x
      · rw [lrun_none] at h
        cases h
        exact Ascent.SafeN.mono (Nat.le_add_right n k) h1
      · exact safeN_of_lrun hp k n pc' r r' m1 m' h h1

/-- **A contract is refuted by a run** from its entry, in a state satisfying its precondition, that returns in
    registers and memory outside its postcondition. -/
theorem Contract.not_of_lrun {p : Lprog I.Op I.Reg} {E : Type} {c : Context I E} {f : Nat}
    {fd : Lfundef I.Op I.Reg} (hp : p[f]? = some fd)
    {Pre : BitVec 64 → BitVec 64 → (I.Reg → BitVec 64) → I.M → Prop}
    {Post : BitVec 64 → BitVec 64 → (I.Reg → BitVec 64) → I.M → (I.Reg → BitVec 64) → I.M → Prop}
    {ret top : BitVec 64} {regs r' : I.Reg → BitVec 64} {m m' : I.M} (hpre : Pre ret top regs m) {k : Nat}
    (hrun : lrun fd.body ret top k (some 0, regs, m) = some (none, r', m'))
    (hpost : ¬ Post ret top regs m r' m') : ¬ I.Contract p c f Pre Post := fun hc => by
  have hs := hc.run (G := fun _ => True) (n := 1 + k)
    (Q := fun s => s.stack = [] → Post ret top regs m s.regs s.m) (rest := []) hpre
    fun _ _ hq => SafeN.returned fun _ => hq
  exact hpost (Ascent.SafeN.of_accept trivial (.inl rfl) (safeN_of_lrun hp k 1 0 regs r' m m' hrun hs) rfl)

end Lprog.Isa
