module

public import X86.QM
public import Std.Data.HashMap

/-!
# Running statements in Lean

An evaluator of `Stmt` that steps with `QInstr.step` and `Cond.eval`, keeping the memory in a hash
map, for tests of the code against the models.
-/

@[expose] public section

namespace X86.Test

/-- A state whose registers and memory are tables, for evaluation. -/
structure RState where
  regs : Array UInt64
  mem : Std.HashMap UInt64 UInt64

/-- Register indices. -/
def regIdx : Reg64 → Nat
  | .rax => 0 | .rbx => 1 | .rcx => 2 | .rdx => 3 | .rsi => 4 | .rdi => 5 | .rsp => 6
  | .rbp => 7 | .r8 => 8 | .r9 => 9 | .r10 => 10 | .r11 => 11 | .r12 => 12 | .r13 => 13
  | .r14 => 14 | .r15 => 15

/-- The `QState` a table state describes. -/
def RState.toQ (s : RState) : QState := ⟨fun r ↦ s.regs.getD (regIdx r) 0, fun a ↦ s.mem[a]?⟩

/-- All registers. -/
def allRegs : List Reg64 :=
  [.rax, .rbx, .rcx, .rdx, .rsi, .rdi, .rsp, .rbp, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

/-- One instruction on a table state, by `QInstr.step`: the registers read back from the result,
the word a store writes inserted. -/
def stepI (i : QInstr) (s : RState) : Option RState := do
  let q := s.toQ
  let q' ← i.step q
  let regs := (allRegs.map q'.reg).toArray
  let mem ← match i with
    | .store a _ | .storei a _ => do
      let addr := a.eval q
      let v ← q'.mem addr
      some (s.mem.insert addr v)
    | _ => some s.mem
  some ⟨regs, mem⟩

/-- The outcome of a statement, evaluated with at most `fuel` loop iterations in all. -/
inductive ROutcome
  | ok (s : RState)
  | err (s : RState)

/-- Evaluate a statement; `none` when stuck or out of fuel. -/
partial def run : Nat → Stmt → RState → Option (ROutcome × Nat)
  | fuel, .skip, s => some (.ok s, fuel)
  | fuel, .ins i, s => (stepI i s).map fun s ↦ (.ok s, fuel)
  | fuel, .fail, s => some (.err s, fuel)
  | fuel, .seq a b, s => do
    match ← run fuel a s with
    | (.ok s, fuel) => run fuel b s
    | r => some r
  | fuel, .ite c t e, s => if c.eval s.toQ then run fuel t s else run fuel e s
  | 0, .loop _ _, _ => none
  | fuel + 1, .loop c b, s =>
    if c.eval s.toQ then do
      match ← run fuel b s with
      | (.ok s, fuel) => run fuel (.loop c b) s
      | r => some r
    else some (.ok s, fuel)

/-- A state with `rdi = base` and the given words. -/
def RState.ofWords (base : UInt64) (words : List (UInt64 × UInt64)) : RState :=
  ⟨(allRegs.map fun r ↦ if r = .rdi then base else 0).toArray, Std.HashMap.ofList words⟩

/-- The word at `a`, zero if there is none. -/
def RState.word (s : RState) (a : UInt64) : UInt64 := s.mem[a]?.getD 0

end X86.Test
