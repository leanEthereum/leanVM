/-
  LeanVM.Spec.Isa

  leanISA, the leanVM instruction set: memory, instructions, programs, one step, valid
  executions; and the encoding of an instruction as sixteen `K` slots.
-/

module

public import LeanVM.Spec.Field
public import LeanVM.Spec.Blake2s

/-!
# leanISA

The leanVM instruction set, from §2 of the leanVM specification at
`127510d14c98ade4e8a97646c44fa7f1ff5e752d`.

Words are elements of `E = K[y]/(y³ + y + 1)`, `K = GF(2^64)`. Addresses are powers of the
generator `g` of `K*`: memory word `i` and bytecode slot `i` both sit at `g^i`. The machine has two
registers, `pc` and `fp`. The memory is fixed before the run and only read: every instruction
checks a relation on the words it reads, so all nondeterminism is the choice of the memory.

The encoding of an instruction as sixteen `K` slots (specification §8.1) is how the verifier
receives a program.
-/

namespace LeanVM.Parameters

@[expose] public section

/-! ## Opcodes -/

/-- The six instructions, in bus-code order (`tables.rs:99-104`). -/
inductive Opcode
  | xor
  | mulNative
  | setConstant
  | deref
  | jump
  | blake2s
  deriving DecidableEq, Repr

/-- The bus code of an opcode: `g^0, …, g^5` in constructor order (specification §6.4). -/
def Opcode.code : Opcode → K
  | .xor => gpow 0
  | .mulNative => gpow 1
  | .setConstant => gpow 2
  | .deref => gpow 3
  | .jump => gpow 4
  | .blake2s => gpow 5

/-! ## Size bounds (specification §2, §6.2) -/

/-- The least memory log-size, `2^16` cells (`cpu/mod.rs:51`, `MIN_LOG_MEM`). -/
def minLogMem : ℕ := 16

/-- The greatest memory log-size, `2^32` cells (`cpu/mod.rs:52`, `MAX_LOG_MEM`). -/
def maxLogMem : ℕ := 32

/-- The greatest bytecode log-size (`crates/verifier/src/layout.rs:393`; `MAX_LOG_BYTECODE`,
`cpu/mod.rs:64` at `a386121f`, is removed at `127510d1`). -/
def maxLogBytecode : ℕ := 32

end
end LeanVM.Parameters

namespace LeanVM.Semantics

open LeanVM.Parameters

@[expose] public section

/-! ## Memory -/

open Classical in
/-- The index of an address: `some i` when `a = g^i` with `i < 2^κ`, otherwise `none`. -/
noncomputable def gLog? (κ : ℕ) (a : K) : Option (Fin (2 ^ κ)) :=
  if h : ∃ i : Fin (2 ^ κ), a = gpow i then some (Classical.choose h) else none

/-- A memory of `2^κ` words, by index. -/
abbrev MemImage (κ : ℕ) : Type := Fin (2 ^ κ) → E

/-- The word at address `a`, if `a` is an address. -/
noncomputable def MemImage.read {κ : ℕ} (L : MemImage κ) (a : K) : Option E :=
  (gLog? κ a).map L

/-- The public input: 256 bits, as four `K` lanes. -/
structure PublicInput where
  /-- The four lanes. -/
  lanes : Fin 4 → K
  deriving DecidableEq

/-- Memory word `0` holds `lane₀ + lane₁·y`. -/
def PublicInput.word0 (p : PublicInput) : E := E.ofLimbs (p.lanes 0) (p.lanes 1) 0

/-- Memory word `1` holds `lane₂ + lane₃·y`. -/
def PublicInput.word1 (p : PublicInput) : E := E.ofLimbs (p.lanes 2) (p.lanes 3) 0

/-! ## Instructions and programs

An operand `o` names the word at `fp · o`, written `[o]`. -/

/-- What a `DEREF` stores: a local word, the return address, or the frame pointer. -/
inductive DerefMode
  | cell
  | pc
  | fp
  deriving DecidableEq, Repr

/-- The six instructions. -/
inductive Instr
  /-- `[o_C] = [o_A] + [o_B]`. -/
  | xor (oA oB oC : K)
  /-- `[o_C] = [o_A] · [o_B]`. -/
  | mulNative (oA oB oC : K)
  /-- `[o] = k`. -/
  | setConstant (o : K) (k : E)
  /-- `[o₁]` is in `K`, and the word at address `[o₁] · o₂` is the source `mode` selects
  (`derefSource`); `[o₃]` is read in every mode. -/
  | deref (o1 o2 o3 : K) (mode : DerefMode)
  /-- `[o_c]`, `[o_d]`, `[o_f]` are in `K`; jump to `([o_d], [o_f])` if `[o_c] ≠ 0`. -/
  | jump (oc od of : K)
  /-- `([o_out], [g·o_out])` is the BLAKE2s compression of the message `[o_m₀], …, [o_m₃]` under
  the chaining value `([o_cv], [g·o_cv])`, with counter and flags `[o_md]`. -/
  | blake2s (om : Fin 4 → K) (ocv oout omd : K)
  deriving DecidableEq

/-- The opcode of an instruction. -/
def Instr.opcode : Instr → Opcode
  | .xor .. => .xor
  | .mulNative .. => .mulNative
  | .setConstant .. => .setConstant
  | .deref .. => .deref
  | .jump .. => .jump
  | .blake2s .. => .blake2s

/-- A program: `2^logSize` instructions, instruction `i` at address `g^i`. -/
structure Program where
  /-- The log of the number of instructions. -/
  logSize : ℕ
  /-- At most `2^32` instructions. -/
  logSize_le : logSize ≤ maxLogBytecode
  /-- The instructions. -/
  code : Fin (2 ^ logSize) → Instr

/-- The instruction at address `pc`. -/
noncomputable def Program.fetch (prog : Program) (pc : K) : Option Instr :=
  (gLog? prog.logSize pc).map prog.code

/-! ## `BLAKE2S`

How the 32-bit words of the compression function are stored in memory words. -/

/-- The metadata word: the counter is limb 0, the two flag words are the halves of limb 1. -/
def unpackMetadata (md : E) : UInt64 × UInt32 × UInt32 :=
  (⟨(md.limb 0).toBitVec⟩, lowWord (md.limb 1), highWord (md.limb 1))

/-- The sixteen message words of four memory words. -/
def messageWords (m : Fin 4 → E) : Vector UInt32 16 :=
  cellWords (m 0) ++ cellWords (m 1) ++ cellWords (m 2) ++ cellWords (m 3)

/-- What `BLAKE2S` checks: the nine words have no `y²` term, and the output is the compression
of the message under the chaining value and the metadata. -/
def CompressCells (m : Fin 4 → E) (cv0 cv1 out0 out1 md : E) : Prop :=
  (∀ i, IsCanonical128 (m i)) ∧ IsCanonical128 cv0 ∧ IsCanonical128 cv1 ∧
    IsCanonical128 out0 ∧ IsCanonical128 out1 ∧ IsCanonical128 md ∧
    cellWords out0 ++ cellWords out1 =
      compress (cellWords cv0 ++ cellWords cv1) (messageWords m) (unpackMetadata md).1
        (unpackMetadata md).2.1 (unpackMetadata md).2.2

/-- `CompressCells` is decidable (compared as lists of words, which the kernel reduces). -/
instance {m : Fin 4 → E} {cv0 cv1 out0 out1 md : E} :
    Decidable (CompressCells m cv0 cv1 out0 out1 md) :=
  decidable_of_iff
    ((∀ i, IsCanonical128 (m i)) ∧ IsCanonical128 cv0 ∧ IsCanonical128 cv1 ∧
      IsCanonical128 out0 ∧ IsCanonical128 out1 ∧ IsCanonical128 md ∧
      (cellWords out0 ++ cellWords out1).toList =
        (compress (cellWords cv0 ++ cellWords cv1) (messageWords m) (unpackMetadata md).1
          (unpackMetadata md).2.1 (unpackMetadata md).2.2).toList)
    (by simp only [CompressCells, Vector.toList_inj])

/-! ## One step -/

/-- The registers: the program counter and the frame pointer. -/
structure Regs (F : Type) where
  /-- The program counter. -/
  pc : F
  /-- The frame pointer. -/
  fp : F
  deriving Repr

/-- The next instruction, same frame: `(g · pc, fp)`. -/
def Regs.next (r : Regs K) : Regs K := ⟨g * r.pc, r.fp⟩

/-- What a `DEREF` stores: the local word `[o₃]`, the return address `g² · pc`, or `fp`. -/
def derefSource : DerefMode → Regs K → E → E
  | .cell, _, v3 => v3
  | .pc, r, _ => ofK (g ^ 2 * r.pc)
  | .fp, r, _ => ofK r.fp

/-- Execute an instruction with the memory reader `read`: read its words, check its relation, and
return the next registers; `none` if a read or a check fails. -/
def executeWith (read : K → Option E) (r : Regs K) : Instr → Option (Regs K)
  | .xor oA oB oC => do
    let vA ← read (r.fp * oA)
    let vB ← read (r.fp * oB)
    let vC ← read (r.fp * oC)
    guard (vC = vA + vB)
    pure r.next
  | .mulNative oA oB oC => do
    let vA ← read (r.fp * oA)
    let vB ← read (r.fp * oB)
    let vC ← read (r.fp * oC)
    guard (vC = vA * vB)
    pure r.next
  | .setConstant o k => do
    let v ← read (r.fp * o)
    guard (v = k)
    pure r.next
  | .deref o1 o2 o3 mode => do
    let p ← read (r.fp * o1)
    guard (IsInK p)
    let v3 ← read (r.fp * o3)
    let v2 ← read (p.limb 0 * o2)
    guard (v2 = derefSource mode r v3)
    pure r.next
  | .jump oc od of => do
    let c ← read (r.fp * oc)
    let d ← read (r.fp * od)
    let f ← read (r.fp * of)
    guard (IsInK c ∧ IsInK d ∧ IsInK f)
    pure (if c = 0 then r.next else ⟨d.limb 0, f.limb 0⟩)
  | .blake2s om ocv oout omd => do
    let m0 ← read (r.fp * om 0)
    let m1 ← read (r.fp * om 1)
    let m2 ← read (r.fp * om 2)
    let m3 ← read (r.fp * om 3)
    let cv0 ← read (r.fp * ocv)
    let cv1 ← read (r.fp * (g * ocv))
    let out0 ← read (r.fp * oout)
    let out1 ← read (r.fp * (g * oout))
    let md ← read (r.fp * omd)
    guard (CompressCells ![m0, m1, m2, m3] cv0 cv1 out0 out1 md)
    pure r.next

/-- Execute an instruction on the memory `L`. -/
noncomputable def execute {κ : ℕ} (L : MemImage κ) (r : Regs K) : Instr → Option (Regs K) :=
  executeWith L.read r

/-- One step: fetch the instruction at `pc` and execute it. -/
noncomputable def step {κ : ℕ} (prog : Program) (L : MemImage κ) (r : Regs K) :
    Option (Regs K) :=
  prog.fetch r.pc >>= execute L r

/-! ## Valid executions -/

/-- The machine starts at `(pc, fp) = (1, 1)`. -/
def Regs.initial : Regs K := ⟨1, 1⟩

/-- The last bytecode slot, `g^(2^logSize − 1)`: reaching it halts the machine. -/
def Program.finalPc (prog : Program) : K := gpow (2 ^ prog.logSize - 1)

/-- The machine halts at `(finalPc, 1)`. -/
def Regs.final (prog : Program) : Regs K := ⟨prog.finalPc, 1⟩

/-- `n` steps from `r`, halting at `finalPc`: `none` if a step fails or the machine halts first. -/
noncomputable def run {κ : ℕ} (prog : Program) (L : MemImage κ) : ℕ → Regs K → Option (Regs K)
  | 0, r => some r
  | n + 1, r => if r.pc = prog.finalPc then none else step prog L r >>= run prog L n

/-- An execution: a memory of `2^κ` words and a number of steps. -/
structure Trace (prog : Program) where
  /-- The log of the memory size. -/
  κ : ℕ
  /-- The memory. -/
  image : MemImage κ
  /-- The number of steps. -/
  steps : ℕ

/-- The memory has between `2^16` and `2^32` words and holds the public input in words `0`, `1`. -/
def HasPublicBoundary {prog : Program} (input : PublicInput) (t : Trace prog) : Prop :=
  minLogMem ≤ t.κ ∧ t.κ ≤ maxLogMem ∧
    t.image.read (gpow 0) = some input.word0 ∧ t.image.read (gpow 1) = some input.word1

/-- **A valid execution** of `prog` on `input`: the memory holds the public input, and `t.steps`
steps from `(1, 1)` halt at `(finalPc, 1)`. -/
def ValidExecution (prog : Program) (input : PublicInput) (t : Trace prog) : Prop :=
  HasPublicBoundary input t ∧ run prog t.image t.steps Regs.initial = some (Regs.final prog)

/-- The last instruction is not a `JUMP`: the one condition knowledge soundness puts on a
program. leanVM's compiler always pads the last slot with a `SET`; the verifier does not check
it, and for bytecode whose last instruction is a `JUMP` its constraints accept runs that are not
valid executions. -/
def SentinelSafe (prog : Program) : Prop :=
  (prog.code ⟨2 ^ prog.logSize - 1, Nat.sub_lt (Nat.two_pow_pos _) (by decide)⟩).opcode ≠ .jump

/-! ## Instruction counts -/

/-- The number of instructions of opcode `op` executed in `n` steps from `r`, stepping as `run`
does; the count stops at a step that fails. -/
noncomputable def runCount {κ : ℕ} (prog : Program) (L : MemImage κ) (op : Opcode) :
    ℕ → Regs K → ℕ
  | 0, _ => 0
  | n + 1, r =>
    match prog.fetch r.pc, step prog L r with
    | some ins, some r' => (if ins.opcode = op then 1 else 0) + runCount prog L op n r'
    | _, _ => 0

/-- The number of instructions of opcode `op` an execution executes. -/
noncomputable def Trace.count {prog : Program} (t : Trace prog) (op : Opcode) : ℕ :=
  runCount prog t.image op t.steps Regs.initial

end
end LeanVM.Semantics

namespace LeanVM.Arithmetization

open LeanVM.Parameters LeanVM.Semantics

@[expose] public section

/-! ## The bytecode encoding (specification §8.1) -/

/-- The `DEREF` store-mode flags `(f_pc, f_fp)`: `cell ↦ (0, 0)`, `pc ↦ (1, 0)`, `fp ↦ (0, 1)`
(`isa.rs:68-75`; specification §7.4). -/
def derefFlags : DerefMode → K × K
  | .cell => (0, 0)
  | .pc => (1, 0)
  | .fp => (0, 1)

/-- The bus entry of an instruction, `(opcode, op₁, …, op₇)`: slots 3 to 10 of specification §8.1,
the eight public columns of `layout.rs:228-289`. -/
def entry : Instr → Vector K 8
  | .xor oA oB oC => #v[Opcode.xor.code, oA, oB, oC, 0, 0, 0, 0]
  | .mulNative oA oB oC => #v[Opcode.mulNative.code, oA, oB, oC, 0, 0, 0, 0]
  | .setConstant o k => #v[Opcode.setConstant.code, o, k.limb 0, k.limb 1, k.limb 2, 0, 0, 0]
  | .deref o1 o2 o3 mode =>
      #v[Opcode.deref.code, o1, o2, o3, (derefFlags mode).1, (derefFlags mode).2, 0, 0]
  | .jump oc od of => #v[Opcode.jump.code, oc, od, of, 0, 0, 0, 0]
  | .blake2s om ocv oout omd => #v[Opcode.blake2s.code, om 0, om 1, om 2, om 3, ocv, oout, omd]

/-- The sixteen slots of an instruction (specification §8.1): the entry at slots 3 to 10, zero
elsewhere. -/
def encodeSlots (i : Instr) : Vector K 16 :=
  let e := entry i
  #v[0, 0, 0, e[0], e[1], e[2], e[3], e[4], e[5], e[6], e[7], 0, 0, 0, 0, 0]

end
end LeanVM.Arithmetization
