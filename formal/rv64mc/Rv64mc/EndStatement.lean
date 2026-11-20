import RiscvZkvm.Rv64.StepOn
import RiscvZkvm.Interpreter.Decode
import Statement.LeanVmVerifier

/-!
# What is proved about the RV64IM image of the verifier

The trusted statement. An image (`Image`: an entry, the code words from a base, and the data words) is loaded
with the input words at `inputBase` and their number in `a0` (`Loaded`); the code is exactly the image's words as
riscv-zkvm's decoder reads them, and nothing else is code. The machine (`step`) is riscv-zkvm's execution of one
decoded instruction, which stops at every `ECALL`, `EBREAK` and `CSRS`, at an address with no code, and at a memory
access that SP1 would refuse (`memOkSp1`: beyond `2^37`, misaligned, or a store over code) or that leaves the
guest's windows (`inWindow`). `Sound`: a run that stops at the halting `ECALL` (`t0 = 0`) with `a0 = 0` read an
input that decodes (`decodeInput`, the format `guest/src/main.rs` documents) to a bytecode, a public input and a
proof that the statement's verifier `verifyWith` over Keccak-f[1600] accepts. `AllDecode`: every code word is an
instruction the machine models, so that no word the decoder cannot read makes `Sound` hold by trapping.

The end result is `AllDecode image ∧ Sound image` for the image built by `scripts/nostd-verifier.sh` and `guest/`.
Every memory word but the image's data and the input is arbitrary at the start, and so are all registers but `a0`
(`_start` sets `sp` and `gp` itself). A deployment whose machine continues where this one stops is not covered.
-/

namespace Rv64mc

open RiscvZkvm.Rv64 RiscvZkvm.Interpreter LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol
  LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

/-! ## The image -/

/-- An image as the ELF gives it: its entry, its code words from `codeBase` on, and its data as (address, word)
    pairs of 8-byte words. -/
structure Image where
  /-- The address of the first instruction run. -/
  entry : Word
  /-- The address of the first code word. -/
  codeBase : Word
  /-- The code words, one every 4 bytes from `codeBase`. -/
  code : List (BitVec 32)
  /-- The memory's initial 8-byte words at their addresses. -/
  data : List (Word × Word)

/-- The image's code as a map: the word at `pc`, decoded, and none where there is no code or it does not decode. -/
def Image.codeAt (img : Image) (pc : Word) : Option Instr :=
  if img.codeBase.toNat ≤ pc.toNat ∧ (pc.toNat - img.codeBase.toNat) % 4 = 0 then
    (img.code[(pc.toNat - img.codeBase.toNat) / 4]?).bind decode
  else none

/-- Every code word is an instruction riscv-zkvm's `Instr` models. -/
def AllDecode (img : Image) : Prop := ∀ w ∈ img.code, (decode w).isSome

/-! ## The machine -/

/-- The guest's data windows (`guest/link.x`, `guest/src/main.rs`): the input and the heap,
    `0x10000000..0x78000000`; `.rodata`, `.data`, `.bss` and the stack, `0xa0000000..0xc0000000`. -/
def inWindow (a : Word) (w : Nat) : Bool :=
  (decide (0x10000000 ≤ a.toNat) && decide (a.toNat + w ≤ 0x78000000)) ||
    (decide (0xa0000000 ≤ a.toNat) && decide (a.toNat + w ≤ 0xc0000000))

/-- A memory access passes SP1's check and lies wholly in one window. -/
def memOk (s : MachineState) (i : Instr) : Bool :=
  memOkSp1 s i && match memAccess s i with
    | none => true
    | some (a, w, _) => inWindow a w

/-- **One step**: none at `ECALL`, `EBREAK`, ZisK's `CSRS` or where there is no code; a memory access only where
    `memOk` holds; otherwise riscv-zkvm's execution of the instruction. -/
def step (s : MachineState) : Option MachineState :=
  match s.code s.pc with
  | none | some .ECALL | some .EBREAK | some (.CSRS ..) => none
  | some i => if memOk s i then some (execInstrBr s i) else none

/-- `n` steps of `step`. -/
def steps : Nat → MachineState → Option MachineState
  | 0, s => some s
  | n + 1, s => (step s).bind (steps n)

/-- From `s`, `n` steps reach the halting `ECALL` (`t0 = 0`) with `a0 = v`. -/
def Halts (s : MachineState) (n : Nat) (v : Word) : Prop :=
  ∃ t, steps n s = some t ∧ t.code t.pc = some .ECALL ∧ t.getReg .x5 = 0 ∧ t.getReg .x10 = v

/-! ## Loading -/

/-- Where the loader puts the input (`INPUT`, `guest/src/main.rs`). -/
def inputBase : Word := 0x10000000

/-- How many input words fit between `inputBase` and the heap at `0x20000000`. -/
def inputCapacity : Nat := 2 ^ 25

/-- `s` is the image loaded with the input `words`, about to run: at the entry, the code exactly the image's, the
    data words and the input words in memory, their number in `a0`, and not more than fit below the heap. -/
def Loaded (img : Image) (words : List Word) (s : MachineState) : Prop :=
  s.pc = img.entry ∧ s.code = img.codeAt ∧
  (∀ p ∈ img.data, s.getMem p.1 = p.2) ∧
  (∀ i (h : i < words.length), s.getMem (inputBase + BitVec.ofNat 64 (8 * i)) = words[i]) ∧
  s.getReg .x10 = BitVec.ofNat 64 words.length ∧ words.length ≤ inputCapacity

/-! ## The input -/

/-- A reader of input words. -/
abbrev Reader := StateT (List Word) Option

/-- The next word. -/
def readWord : Reader Word := do
  match ← get with
  | w :: ws => set ws; return w
  | [] => failure

/-- `n` items, in order. -/
def readMany {α : Type} (item : Reader α) : Nat → Reader (List α)
  | 0 => pure []
  | n + 1 => do
    let x ← item
    let xs ← readMany item n
    return x :: xs

/-- A count: one word. -/
def readCount : Reader Nat := do return (← readWord).toNat

/-- A count, then that many items. -/
def readList {α : Type} (item : Reader α) : Reader (List α) := do readMany item (← readCount)

/-- A `K` word: one word, bit `i` the coefficient of `x^i`. -/
def readK : Reader K := do return BF64.ofBitVec (← readWord)

/-- A scalar `c0 + c1·y`: two words, `c0` first (`E::new`). -/
def readScalar : Reader E := do
  let c0 ← readK
  let c1 ← readK
  return E.ofLimbs c0 c1

/-- A digest: four words, its 32 bytes little-endian. -/
def readDigest : Reader Digest := do
  let w0 ← readWord
  let w1 ← readWord
  let w2 ← readWord
  let w3 ← readWord
  return #v[⟨w0⟩, ⟨w1⟩, ⟨w2⟩, ⟨w3⟩]

/-- A Merkle path: the leaf index, the leaf's words, the siblings from the leaf up. -/
def readOpening : Reader Opening := do
  let leafIndex ← readCount
  let leaf ← readList readK
  let path ← readList readDigest
  return { leafIndex, leaf, path }

/-- The input format of `guest/src/main.rs`: the bytecode, the public input, the stream, the openings by phase. -/
def readInput : Reader (List K × Digest × Proof) := do
  let bytecode ← readList readK
  let publicInput ← readDigest
  let stream ← readList readScalar
  let openings ← readList (readList readOpening)
  return (bytecode, publicInput, { stream, openings })

/-- The whole input, nothing left over. -/
def decodeInput (words : List Word) : Option (List K × Digest × Proof) :=
  match readInput.run words with
  | some (value, []) => some value
  | _ => none

/-! ## The end statement -/

/-- The deployed verifier: `verifyWith` over Keccak-f[1600]. -/
def verify (bytecode : List K) (publicInput : Digest) (proof : Proof) : Bool :=
  Id.run (verifyWith (m := Id) keccakF1600 bytecode publicInput proof)

/-- **Accepting is sound**: a run of the loaded image that halts with `a0 = 0` read an input that decodes to a
    proof the verifier accepts. -/
def Sound (img : Image) : Prop :=
  ∀ words s n, Loaded img words s → Halts s n 0 →
    ∃ bytecode publicInput proof, decodeInput words = some (bytecode, publicInput, proof) ∧
      verify bytecode publicInput proof = true

end Rv64mc
