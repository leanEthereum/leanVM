import Rv64Verifier.Sym.Micro

/-!
# The symbolic executor

Ported from sig.golf's `SigGolfCandidate.Rv`.

`symRun cfg words pc fuel : Option Result` symbolically executes the straight-line code `words`
(raw instruction encodings, the first at address `pc`) for at most `fuel` instructions. It stops

* before an `ECALL` (`Stop.ecall`), so the caller can apply the halt law (`Halting`);
* after a branch (`Stop.branch`, the final pc is an `E.ite`) or `JAL`/`JALR` (`Stop.jump`);
* when `fuel` or `words` is exhausted (`Stop.fuel`, `Stop.endOfCode`).

It returns `none` on an undecodable or unsupported instruction, on a constant address that fails
`validAccess`, or on a memory read it cannot resolve (possible aliasing with `cfg.noAlias = false`).
All values are symbolic expressions over the initial state (`E`).
-/

namespace Rv64Verifier.Sym
open RiscvZkvm.Rv64

/-- Symbolic register file (`x0` is hard-wired to `0`). -/
structure RegFile where
  r1 : E
  r2 : E
  r3 : E
  r4 : E
  r5 : E
  r6 : E
  r7 : E
  r8 : E
  r9 : E
  r10 : E
  r11 : E
  r12 : E
  r13 : E
  r14 : E
  r15 : E
  r16 : E
  r17 : E
  r18 : E
  r19 : E
  r20 : E
  r21 : E
  r22 : E
  r23 : E
  r24 : E
  r25 : E
  r26 : E
  r27 : E
  r28 : E
  r29 : E
  r30 : E
  r31 : E
  deriving Repr

/-- The 31 fields `x1 … x31`, in order. -/
def RegFile.fields (rf : RegFile) : List E := [rf.r1, rf.r2, rf.r3, rf.r4, rf.r5, rf.r6, rf.r7, rf.r8, rf.r9, rf.r10, rf.r11, rf.r12, rf.r13, rf.r14, rf.r15, rf.r16, rf.r17, rf.r18, rf.r19, rf.r20, rf.r21, rf.r22, rf.r23, rf.r24, rf.r25, rf.r26, rf.r27, rf.r28, rf.r29, rf.r30, rf.r31]

def RegFile.init : RegFile := ⟨.reg .x1, .reg .x2, .reg .x3, .reg .x4, .reg .x5, .reg .x6, .reg .x7, .reg .x8, .reg .x9, .reg .x10, .reg .x11, .reg .x12, .reg .x13, .reg .x14, .reg .x15, .reg .x16, .reg .x17, .reg .x18, .reg .x19, .reg .x20, .reg .x21, .reg .x22, .reg .x23, .reg .x24, .reg .x25, .reg .x26, .reg .x27, .reg .x28, .reg .x29, .reg .x30, .reg .x31⟩

def RegFile.get (rf : RegFile) : Reg → E
  | .x0 => .c 0
  | .x1 => rf.r1
  | .x2 => rf.r2
  | .x3 => rf.r3
  | .x4 => rf.r4
  | .x5 => rf.r5
  | .x6 => rf.r6
  | .x7 => rf.r7
  | .x8 => rf.r8
  | .x9 => rf.r9
  | .x10 => rf.r10
  | .x11 => rf.r11
  | .x12 => rf.r12
  | .x13 => rf.r13
  | .x14 => rf.r14
  | .x15 => rf.r15
  | .x16 => rf.r16
  | .x17 => rf.r17
  | .x18 => rf.r18
  | .x19 => rf.r19
  | .x20 => rf.r20
  | .x21 => rf.r21
  | .x22 => rf.r22
  | .x23 => rf.r23
  | .x24 => rf.r24
  | .x25 => rf.r25
  | .x26 => rf.r26
  | .x27 => rf.r27
  | .x28 => rf.r28
  | .x29 => rf.r29
  | .x30 => rf.r30
  | .x31 => rf.r31

def RegFile.set (rf : RegFile) (r : Reg) (e : E) : RegFile :=
  match r with
  | .x0 => rf
  | .x1 => { rf with r1 := e }
  | .x2 => { rf with r2 := e }
  | .x3 => { rf with r3 := e }
  | .x4 => { rf with r4 := e }
  | .x5 => { rf with r5 := e }
  | .x6 => { rf with r6 := e }
  | .x7 => { rf with r7 := e }
  | .x8 => { rf with r8 := e }
  | .x9 => { rf with r9 := e }
  | .x10 => { rf with r10 := e }
  | .x11 => { rf with r11 := e }
  | .x12 => { rf with r12 := e }
  | .x13 => { rf with r13 := e }
  | .x14 => { rf with r14 := e }
  | .x15 => { rf with r15 := e }
  | .x16 => { rf with r16 := e }
  | .x17 => { rf with r17 := e }
  | .x18 => { rf with r18 := e }
  | .x19 => { rf with r19 := e }
  | .x20 => { rf with r20 := e }
  | .x21 => { rf with r21 := e }
  | .x22 => { rf with r22 := e }
  | .x23 => { rf with r23 := e }
  | .x24 => { rf with r24 := e }
  | .x25 => { rf with r25 := e }
  | .x26 => { rf with r26 := e }
  | .x27 => { rf with r27 := e }
  | .x28 => { rf with r28 := e }
  | .x29 => { rf with r29 := e }
  | .x30 => { rf with r30 := e }
  | .x31 => { rf with r31 := e }

/-- Symbolic memory: doubleword writes, newest first. -/
abbrev SymMem := List (Addr × E)

/-- Meaning of a symbolic memory relative to the initial state `s`. -/
def memEval (s : MachineState) : SymMem → Word → Word
  | [], a => s.getMem a
  | (k, v) :: ws, a => if a = k.eval s then v.eval s else memEval s ws a

structure Config where
  /-- If `true`, reads that cannot be resolved syntactically emit `Oblig.ne` side conditions
  (the addresses differ) instead of failing. -/
  noAlias : Bool := false
  deriving Repr

/-- Resolve a doubleword read at key `k`: the value and extra side conditions. -/
def readMem (cfg : Config) (k : Addr) : SymMem → Option (E × List Oblig)
  | [] => some (.ld k.toE, [])
  | (k', v) :: ws =>
    match k.alias k' with
    | .same => some (v, [])
    | .diff => readMem cfg k ws
    | .unknown =>
      if cfg.noAlias then
        match readMem cfg k ws with
        | none => none
        | some (e, os) => some (e, .ne k k' :: os)
      else none

def isSame (k k' : Addr) : Bool :=
  match k.alias k' with
  | .same => true
  | _ => false

def writeMem (k : Addr) (v : E) (ws : SymMem) : SymMem :=
  (k, v) :: ws.filter (fun p => !isSame k p.1)

structure SymState where
  regs : RegFile
  mem : SymMem
  /-- side conditions, newest first -/
  obl : List Oblig
  deriving Repr

def SymState.init : SymState := ⟨RegFile.init, [], []⟩

/-- Is it worth looking for a duplicate of `o`? `ne` conditions are numerous and not
deduplicated during execution (`Oblig.dedup` does it afterwards). -/
def Oblig.dedupable : Oblig → Bool
  | .ne .. => false
  | _ => true

def SymState.addObl (σ : SymState) (o : Oblig) : SymState :=
  if o.dedupable && σ.obl.any (Oblig.beq o) then σ else { σ with obl := o :: σ.obl }

def SymState.addObls (σ : SymState) (os : List Oblig) : SymState :=
  os.foldl SymState.addObl σ

def Src.sym (rf : RegFile) (pc : Word) : Src → E
  | .reg r => rf.get r
  | .imm v => .c v
  | .pc => .c pc

/-- Validity of an access at `a` of width `w`: checked for constants, emitted otherwise. -/
def checkValid (σ : SymState) (a : Addr) (w : Nat) : Option SymState :=
  match a.base with
  | none => if validAccess w a.off then some σ else none
  | some _ => some (σ.addObl (.valid a w))

/-- Doubleword key and byte offset of a sub-doubleword access. -/
def subKey (σ : SymState) (a : Addr) : SymState × Addr × Nat :=
  match a.base with
  | none => (σ, ⟨none, alignToDword a.off⟩, byteOffset a.off)
  | some b => (σ.addObl (.align8 b), ⟨some b, alignToDword a.off⟩, byteOffset a.off)

def LoadKind.isD : LoadKind → Bool
  | .d => true
  | _ => false

def StoreKind.isD : StoreKind → Bool
  | .d => true
  | _ => false

/-- Symbolic execution of one micro-op at constant pc `pc`: the new state and `none` (continue
at `pc + 4`) or `some target` (stop). -/
def symMicro (cfg : Config) (pc : Word) (σ : SymState) : Micro → Option (SymState × Option E)
  | .alu rd op a b =>
    some ({ σ with regs := σ.regs.set rd (mkBin op (a.sym σ.regs pc) (b.sym σ.regs pc)) }, none)
  | .load k rd rs off =>
    let a := norm (mkAdd (σ.regs.get rs) (.c off))
    match checkValid σ a k.width with
    | none => none
    | some σ₁ =>
      if k.isD then
        match readMem cfg a σ₁.mem with
        | none => none
        | some (v, os) =>
          let σ₂ := σ₁.addObls os
          some ({ σ₂ with regs := σ₂.regs.set rd v }, none)
      else
        match subKey σ₁ a with
        | (σ₂, key, bo) =>
          match readMem cfg key σ₂.mem with
          | none => none
          | some (w, os) =>
            let σ₃ := σ₂.addObls os
            some ({ σ₃ with regs := σ₃.regs.set rd (mkUn (.ld k bo) w) }, none)
  | .store k rs1 rs2 off =>
    let a := norm (mkAdd (σ.regs.get rs1) (.c off))
    let v := σ.regs.get rs2
    match checkValid σ a k.width with
    | none => none
    | some σ₁ =>
      if k.isD then
        some ({ σ₁ with mem := writeMem a v σ₁.mem }, none)
      else
        match subKey σ₁ a with
        | (σ₂, key, bo) =>
          match readMem cfg key σ₂.mem with
          | none => none
          | some (old, os) =>
            let σ₃ := σ₂.addObls os
            some ({ σ₃ with mem := writeMem key (mkBin (.st k bo) old v) σ₃.mem }, none)
  | .branch op r1 r2 off =>
    some (σ, some (mkIte op (σ.regs.get r1) (σ.regs.get r2) (.c (pc + off)) (.c (pc + 4))))
  | .jal rd off =>
    some ({ σ with regs := σ.regs.set rd (.c (pc + 4)) }, some (.c (pc + off)))
  | .jalr rd rs off =>
    some ({ σ with regs := σ.regs.set rd (.c (pc + 4)) },
      some (mkBin .and (mkAdd (σ.regs.get rs) (.c off)) (.c (~~~1#64))))

inductive Stop where
  | fuel | endOfCode | branch | jump | ecall
  deriving DecidableEq, Repr

/-- Result of symbolic execution of a block. -/
structure Result where
  st : SymState
  /-- final pc -/
  pc : E
  stop : Stop
  /-- number of steps executed -/
  steps : Nat
  deriving Repr

def Micro.stopKind : Micro → Stop
  | .branch .. => .branch
  | _ => .jump

def isEcall : Instruction → Bool
  | .base .ECALL => true
  | _ => false

def symRunAux (cfg : Config) : List (BitVec 32) → Word → Nat → SymState → Option Result
  | _, pc, 0, σ => some ⟨σ, .c pc, .fuel, 0⟩
  | [], pc, _ + 1, σ => some ⟨σ, .c pc, .endOfCode, 0⟩
  | w :: ws, pc, f + 1, σ =>
    match decodeInstruction w with
    | none => none
    | some i =>
      if isEcall i then some ⟨σ, .c pc, .ecall, 0⟩ else
      match classify i with
      | none => none
      | some m =>
        match symMicro cfg pc σ m with
        | none => none
        | some (σ', none) =>
          match symRunAux cfg ws (pc + 4) f σ' with
          | none => none
          | some r => some { r with steps := r.steps + 1 }
        | some (σ', some t) => some ⟨σ', t, m.stopKind, 1⟩

/-- Symbolically execute `words` (located at `pc`) for at most `fuel` instructions, from the
identity symbolic state. -/
def symRun (cfg : Config) (words : List (BitVec 32)) (pc : Word) (fuel : Nat) : Option Result :=
  symRunAux cfg words pc fuel SymState.init

/-! ## Reading results back -/

/-- The concrete state a symbolic state describes, relative to the initial state `s`, with code
map `c` and pc `pc`. -/
def SymState.toState (σ : SymState) (s : MachineState) (c : Word → Option Instr) (pc : Word) :
    MachineState :=
  { s with
    regs := fun r => if r = .x0 then s.regs .x0 else (σ.regs.get r).eval s
    mem := memEval s σ.mem
    code := c
    pc := pc }

/-- The concrete final state of a block result, with code map `c`. -/
def Result.toState (r : Result) (s : MachineState) (c : Word → Option Instr) : MachineState :=
  r.st.toState s c (r.pc.eval s)

/-- The side conditions of a block result, as a proposition about the initial state. -/
def Result.obligs (r : Result) (s : MachineState) : Prop := Oblig.all s r.st.obl

/-- Code placement: `words` sit in `code` at address `pc`. -/
def CodeAt (code : Code) (pc : Word) (words : List (BitVec 32)) : Prop :=
  code.base.toNat ≤ pc.toNat ∧ pc.toNat % 4 = 0 ∧ pc.toNat + 4 * words.length < 2 ^ 64 ∧
    words <+: code.words.drop ((pc.toNat - code.base.toNat) / 4)

end Rv64Verifier.Sym
