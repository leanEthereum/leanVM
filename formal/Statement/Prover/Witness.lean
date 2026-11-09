module

public import Statement.LeanVmVerifier

/-!
# The witness of an execution, executable

The run of a trace through the address indices (`powIndex`, `gLogIn`: a word's index looked up in a
hash map), recording each state stepped from, its bytecode slot and the instruction fetched there
(`runSteps`); then the six opcode tables' rows in one pass over the steps, each read carrying its
cell's count so far, the counters stepping by `g` in place (`rowsOf`). The address indices and the
public boundary are the knowledge extractor's too (`lean_vm`,
`LeanVM/Protocol/Extraction/Extractor.lean`).
-/

@[expose] public section

namespace LeanVM.Extraction

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Verifier

/-! ## The address indices and the public boundary -/

/-- Insert `g^i ↦ i` into `m`, keyed by the lane of `g^i`, for the `n` indices `i` from `i₀`,
where `x = g^i₀`: one multiplication and one insertion per index. -/
def powIndexFrom : ℕ → ℕ → K → Std.HashMap UInt64 ℕ → Std.HashMap UInt64 ℕ
  | 0, _, _, m => m
  | n + 1, i, x, m => powIndexFrom n (i + 1) (x * g) (m.insert x.lane i)

/-- **The index of the address space of `2^κ` words**: the lane of `g^i` ↦ `i`, for `i < 2^κ`. -/
def powIndex (κ : ℕ) : Std.HashMap UInt64 ℕ := powIndexFrom (2 ^ κ) 0 1 ∅

/-- The index of address `a` among `2^κ` words, looked up in `idx`: `some i` when `idx` maps the
lane of `a` to `i < 2^κ` (`addressIndex?`, computed). -/
def gLogIn (idx : Std.HashMap UInt64 ℕ) (κ : ℕ) (a : K) : Option (Fin (2 ^ κ)) :=
  match idx[a.lane]? with
  | some i => if h : i < 2 ^ κ then some ⟨i, h⟩ else none
  | none => none

/-- **The public boundary** (`HoldsPublicInput`), decided: the memory has between `2^16` and
`2^32` words, and words `0` and `1` (at the addresses `g^0`, `g^1`) hold the public input. -/
def boundaryOK {prog : LeanIsaProgram} (input : PublicInput) (t : Execution prog) : Bool :=
  if h : minLogMem ≤ t.logMemorySize ∧ t.logMemorySize ≤ maxLogMem then
    decide (t.memory ⟨0, Nat.two_pow_pos t.logMemorySize⟩ = input.word0) &&
      decide (t.memory ⟨1, Nat.one_lt_two_pow (by unfold minLogMem at h; omega)⟩ = input.word1)
  else false

end LeanVM.Extraction

namespace LeanVM.Prover

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Extraction
open LeanVM.Protocol.Verifier

/-! ## The run -/

/-- One step of a run: the state stepped from, the bytecode slot of its counter, and the
instruction fetched there. -/
structure Step where
  /-- The program counter stepped from. -/
  pc : K
  /-- The frame pointer stepped from. -/
  fp : K
  /-- The bytecode slot of `pc`: `pc = g^slot`. -/
  slot : ℕ
  /-- The instruction fetched at `pc`. -/
  ins : LeanIsaInstruction

/-- The memory reader through the index `memIdx` (`MemoryImage.read`, computed). -/
def readIn (memIdx : Std.HashMap UInt64 ℕ) {κ : ℕ} (img : MemoryImage κ) (a : K) : Option E :=
  (gLogIn memIdx κ a).map img

/-- `n` steps from `r` (`run`, computed through the indices, the instruction of slot `i` read
from `code`, `prog.code` tabulated), the steps taken pushed on `acc`: the steps and the state
reached; `none` if a step fails or the machine halts first. -/
def stepsFrom (memIdx codeIdx : Std.HashMap UInt64 ℕ) (prog : LeanIsaProgram)
    (code : Vector LeanIsaInstruction (2 ^ prog.logSize)) {κ : ℕ} (img : MemoryImage κ) :
    ℕ → Registers K → Array Step → Option (Array Step × Registers K)
  | 0, r, acc => some (acc, r)
  | n + 1, r, acc =>
    if r = Registers.final prog then none
    else
      match gLogIn codeIdx prog.logSize r.pc with
      | none => none
      | some i =>
        match executeWith (readIn memIdx img) r code[i] with
        | none => none
        | some r' =>
          stepsFrom memIdx codeIdx prog code img n r' (acc.push ⟨r.pc, r.fp, i.val, code[i]⟩)

/-- **The run of a trace**: its `t.steps` steps from the initial state, when they end in the
final state; `none` otherwise. The program's instructions are tabulated once. -/
def runSteps (memIdx codeIdx : Std.HashMap UInt64 ℕ) (prog : LeanIsaProgram) (t : Execution prog) :
    Option (Array Step) :=
  match stepsFrom memIdx codeIdx prog (Vector.ofFn prog.instructions) t.memory t.stepCount
      Registers.initial
    #[] with
  | some (acc, r) => if r = Registers.final prog then some acc else none
  | none => none

/-- The number of steps of opcode `op` (`Execution.opcodeCount`, computed). -/
def opCount (steps : Array Step) (op : Opcode) : ℕ :=
  steps.countP fun st ↦ decide (st.ins.opcode = op)

/-- The committed size of an execution from its memory log-size and its counts
(`Execution.committedSize`, with `log2Ceil` for `Nat.clog 2`). -/
def committedSizeOf (logSize κ : ℕ) (count : Opcode → ℕ) : ℕ :=
  let height (op : Opcode) : ℕ := 2 ^ log2Ceil (count op)
  let keccakHeight : ℕ := 2 ^ max (log2Ceil (count .keccak)) 9
  3 * 2 ^ κ + 2 ^ logSize +
    13 * height .xor + 13 * height .mulNative + 7 * height .setConstant + 14 * height .deref +
    14 * height .jump + 28 * keccakHeight + 2 ^ 6 * keccakHeight

/-- The greatest committed size the verifier admits, `2^28` (`MAX_MU`, `pcs.rs:52`). -/
def maxCommitted : ℕ := 2 ^ 28

/-! ## The rows -/

/-- The limbs of the word at `a`, zero when there is none (`MemoryImage.limbsAt`, computed). -/
def limbsIn (memIdx : Std.HashMap UInt64 ℕ) {κ : ℕ} (img : MemoryImage κ) (a : K) : Vector K 2 :=
  match readIn memIdx img a with
  | some v => #v[v.limb 0, v.limb 1]
  | none => #v[0, 0]

/-- The cells an instruction reads, in the order its row's reads carry them (`readAddrs`,
computed): a `KECCAK`'s thirteen cells read, then the output cells it writes, the first
`outCells.cellCount` (a cell it does not write keeps its count, `execute.rs:976-986`). -/
def addrsIn (memIdx : Std.HashMap UInt64 ℕ) {κ : ℕ} (img : MemoryImage κ) (fp : K) :
    LeanIsaInstruction → List K
  | .xor oA oB oC | .mulNative oA oB oC | .jump oA oB oC => [fp * oA, fp * oB, fp * oC]
  | .setConstant o _ => [fp * o]
  | .deref o1 o2 o3 _ => [fp * o1, (limbsIn memIdx img (fp * o1))[0] * o2, fp * o3]
  | .keccak om otail ob8 ocap oout _ _ outCells =>
      (List.finRange 13).map (fun c ↦ fp * keccakInputCellOffset om otail ob8 ocap c) ++
        (List.range outCells.cellCount).map fun k ↦ fp * (g ^ k * oout)

/-- The counts of a sequence of reads: each read gets its cell's counter, which then steps by
`g`, in place; the counts are pushed on `cs`. -/
def countReads (memIdx : Std.HashMap UInt64 ℕ) (κ : ℕ) :
    List K → Array K → Array K → Array K × Array K
  | [], cs, ctr => (cs, ctr)
  | a :: rest, cs, ctr =>
    match gLogIn memIdx κ a with
    | some i => countReads memIdx κ rest (cs.push (ctr.getD i.val 1)) (ctr.modify i.val (g * ·))
    | none => countReads memIdx κ rest (cs.push 1) ctr

/-- The cells a `KECCAK` with these operands reads at `fp`, the zero word where a read fails
(`keccakInputCells`, computed). -/
def keccakInputIn (memIdx : Std.HashMap UInt64 ℕ) {κ : ℕ} (img : MemoryImage κ) (fp : K)
    (om : Fin 4 → K) (otail ob8 ocap : K) (c : Fin 13) : E :=
  (readIn memIdx img (fp * keccakInputCellOffset om otail ob8 ocap c)).getD 0

/-- The lane `l` of a state, as a `K` word. -/
def laneK (S : KeccakState) (l : ℕ) : K := K.ofLane (Keccak.lane S l)

/-- The raw row of an instruction executed from `(pc, fp)` (`rowOf`, computed): the typed row of
its table as an array, with the read counts `c 0, c 1, …` and the bytecode count `rbc`. -/
def rowIn (memIdx : Std.HashMap UInt64 ℕ) {κ : ℕ} (img : MemoryImage κ) (pc fp : K) (c : ℕ → K)
    (rbc : K) : LeanIsaInstruction → Array K
  | .xor oA oB oC | .mulNative oA oB oC =>
    let vA := limbsIn memIdx img (fp * oA)
    let vB := limbsIn memIdx img (fp * oB)
    #[pc, fp, oA, oB, oC, vA[0], vA[1], vB[0], vB[1], c 0, c 1, c 2, rbc]
  | .setConstant o k => #[pc, fp, o, k.limb 0, k.limb 1, c 0, rbc]
  | .deref o1 o2 o3 mode =>
    let v3 := limbsIn memIdx img (fp * o3)
    #[pc, fp, o1, o2, o3, (derefFlags mode).1, (derefFlags mode).2,
      (limbsIn memIdx img (fp * o1))[0], v3[0], v3[1], c 0, c 1, c 2, rbc]
  | .jump oc od of =>
    let vc := (limbsIn memIdx img (fp * oc))[0]
    #[pc, fp, oc, od, of, vc, (limbsIn memIdx img (fp * od))[0],
      (limbsIn memIdx img (fp * of))[0], c 0, c 1, c 2, rbc,
      if vc = 0 then 0 else vc⁻¹, if vc = 0 then 0 else 1]
  | .keccak om otail ob8 ocap oout inOdd outOdd outCells =>
    let input := keccakInputIn memIdx img fp om otail ob8 ocap
    let S := stateOfCells input inOdd
    let out := keccakF1600 S
    #[pc, fp, om 0, om 1, om 2, om 3, otail, ob8, ocap, oout, layoutFlagWord inOdd,
        layoutFlagWord outOdd, (keccakOutputFlags outCells).1, (keccakOutputFlags outCells).2,
        if inOdd then (input 0).limb 0 else (input 8).limb 1] ++
      Array.ofFn (fun l : Fin 25 ↦ laneK S l) ++ Array.ofFn (fun l : Fin 25 ↦ laneK out l) ++
      Array.ofFn (fun j : Fin 26 ↦ c j) ++ #[rbc]

/-- The table of an opcode, in the ensemble's order. -/
def opTableIdx : Opcode → ℕ
  | .xor => 0
  | .mulNative => 1
  | .setConstant => 2
  | .deref => 3
  | .jump => 4
  | .keccak => 5

/-- The rows built so far: the six tables' rows, the memory cells' and the bytecode slots'
counters (`g^n` after `n` reads). -/
structure Rows where
  /-- The six opcode tables' rows, in the ensemble's order. -/
  tabs : Array (Array (Array K))
  /-- The memory cells' counters, by index. -/
  mem : Array K
  /-- The bytecode slots' counters, by index. -/
  bc : Array K

/-- The rows of one more step: its reads take their cells' counts, its bytecode read its slot's,
and its row is pushed on its table. -/
def stepRows (memIdx : Std.HashMap UInt64 ℕ) {κ : ℕ} (img : MemoryImage κ) (acc : Rows)
    (st : Step) : Rows :=
  -- the fields taken out first, so that each counter array is updated in place
  let ⟨tabs, mem, bc⟩ := acc
  let (cs, mem) := countReads memIdx κ (addrsIn memIdx img st.fp st.ins) #[] mem
  let row := rowIn memIdx img st.pc st.fp (fun j ↦ cs.getD j 1) (bc.getD st.slot 1) st.ins
  ⟨tabs.modify (opTableIdx st.ins.opcode) (·.push row), mem, bc.modify st.slot (g * ·)⟩

/-- **The rows of a run**: one pass over its steps, from empty tables and every counter `1`. -/
def rowsOf (memIdx : Std.HashMap UInt64 ℕ) {κ : ℕ} (img : MemoryImage κ) (logSize : ℕ)
    (steps : Array Step) : Rows :=
  steps.foldl (stepRows memIdx img)
    ⟨Array.replicate 6 #[], Array.replicate (2 ^ κ) 1, Array.replicate (2 ^ logSize) 1⟩

end LeanVM.Prover

end
