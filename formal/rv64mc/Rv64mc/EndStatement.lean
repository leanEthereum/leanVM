import RiscvZkvm.Rv64.StepOn
import RiscvZkvm.Interpreter.Decode
import Statement.LeanVmVerifier

/-!
# What is proved about the RV64IM image of the verifier

The trusted statement. `Sound image`: a run of the loaded image that halts with `a0 = 0` read an input that decodes
(`decodeInput`, the format `guest/src/main.rs` documents) to a bytecode, a public input and a proof that the
statement's verifier `verifyWith` over Keccak-f[1600] accepts. `AllDecode image`: every code word decodes to an
instruction the machine runs, so that no word the decoder cannot read, and no `EBREAK` or `CSRS`, makes `Sound`
hold by stopping the machine. The end theorem is `rv64_sound` (`Final/End.lean`), `AllDecode image ∧ Sound image`
for the concrete image; until `main`'s proof lands, `main`'s contract (`MainSpec`) is its one hypothesis.
`HaltsSafely image`: on every input of fewer than `maxInputWords` words, the loaded image runs, every step taken by
`step`, to the halting `ECALL` with `a0` one of the guest's verdicts. Its end theorem is `rv64_halts_of_main`
(`Final/EndT.lean`), with `main`'s total contract (`MainSpecT`) its one hypothesis until that is proved.

## The loader (`Loaded`)

The image (`Image`: the entry, the code words from `codeBase`, the data as 8-byte words at their addresses) is
loaded with: the program counter at the entry; the code map exactly the image's words as riscv-zkvm's `decode`
reads them, and nothing else code; every data word in memory; the input words at `inputBase = 0x10000000`, one every
8 bytes; their number in `a0`, at most `inputCapacity = 2^25`, so that they end below the heap at `0x20000000`. Every
other memory word and register is arbitrary (`_start` sets `sp` and `gp` itself).

## Where the machine stops

`step` is riscv-zkvm's `execInstrBr` of the decoded instruction at `pc`, and stops (`none`):
* at every `ECALL` (so at the halting one, which `Halts` asks for, and at any other system call), `EBREAK` and `CSRS`;
* where the code map has nothing: no code, or a word that does not decode (riscv-zkvm's `Instr` lacks `ADDW`, `SLLW`,
  `SRAW`, `SRAIW`, `MULW`, `DIVW`, `DIVUW`, `REMW`, `REMUW`, which RV64IM has; `AllDecode` excludes them);
* at a load or store that SP1 refuses (`memOkSp1`: beyond `2^37`, misaligned for its width, a store over code), or
  that is not wholly inside one of the guest's two windows (`inWindow`): `0x10000000..0x78000000` (input and heap)
  and `0xa0000000..0xc0000000` (static data and stack). Code, at `0x80000000`, is in neither, so loads from code
  stop it too.
A machine that continues where this one stops (one that runs system calls, allows misaligned or out-of-window
accesses, or loads from code) can accept runs this statement says nothing about. `TrapFree` names the theorem that
would close this: every loaded run stops only at the halting `ECALL`. It is not proved; `HaltsSafely` implies it for
the inputs it covers (`stops_at_halt`, `Final/HaltsSafely.lean`).

## Weaker than #738, or than intent

* System calls: every `ECALL` stops the machine, where #738's generic `step` hands host calls to the host.
* Windows: the two windows are narrower than riscv-zkvm's zones (`0x20..0x78000000`, `0x40000000..0x40002000`,
  `0xa0000000..0xc0000000`) that #738's machine allows, and SP1's checks are added.
* Word operations: #738's machine executes all RV64IM 32-bit operations; here those outside `Instr` stop it, and
  `AllDecode` must hold of the image instead.
* The verdict is `a0 = 0` (#738: `1`).
* No completeness (#738 names `Complete` but never defines it). `Sound` is partial: a run that stops elsewhere or
  never halts is not constrained by it. `HaltsSafely` adds termination at a verdict, but only for inputs of fewer
  than `maxInputWords` words, and with any of the three verdicts: an accepted proof may be answered `1` or `2` (the
  guest aborts with `2` when memory runs out), so it is not completeness either. It bounds no number of steps. Its
  end theorem is conditional on `MainSpecT`, which is not proved.
* The image is the build of `scripts/nostd-verifier.sh`'s `no_std` copy of `crates/verifier`, with the inline
  attributes it inserts (`boundaries.txt`), and `guest/`; the end theorem is about the ELF whose sha256 is
  `image.sha256`, read by `Rv64mc/ImageOfElf.lean`.
* Trusted besides this file: riscv-zkvm's `decode` (tied to Sail by no theorem, `docs/validation.md`), `execInstrBr`
  (tied to Sail for one step, under side conditions, by `step_execute_sail_sim`, for every instruction but `SUBW`,
  `SRLW`, `SLLIW`, `SRLIW`, `MV`, `LI`, `NOP` and `CSRS`; the image uses `SRLW` and `SRLIW`), `memOkSp1`, and the
  ELF reader.
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

/-- A decoded word the machine runs: an instruction of `Instr`, and neither `EBREAK` nor `CSRS`, at which `step`
    stops (`ECALL` stops it too, but it is how the image halts). -/
def Runnable : Option Instr → Bool
  | none | some .EBREAK | some (.CSRS ..) => false
  | some _ => true

/-- Every code word decodes to an instruction the machine runs. -/
def AllDecode (img : Image) : Prop := ∀ w ∈ img.code, Runnable (decode w) = true

/-! ## The machine -/

/-- The guest's data windows (`guest/link.x`, `guest/src/main.rs`): the input and the heap,
    `0x10000000..0x78000000`; the static data (`.rodata`, `.data`) and the stack, `0xa0000000..0xc0000000`. -/
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

/-- **The open obligation that would make `Sound` hold of machines that continue where `step` stops**: every run of
    the loaded image stops only at the halting `ECALL` (`t0 = 0`). Not proved. -/
def TrapFree (img : Image) : Prop :=
  ∀ words s n t, Loaded img words s → steps n s = some t → step t = none →
    t.code t.pc = some .ECALL ∧ t.getReg .x5 = 0

/-- The inputs `HaltsSafely` covers: fewer than `2^16` words (512 KiB). -/
def maxInputWords : Nat := 2 ^ 16

/-- **Every run ends at a verdict**: on every input of fewer than `maxInputWords` words, the loaded image takes `n`
    steps of `step` (so none of them traps, accesses memory outside SP1's checks or the windows, meets a missing or
    undecodable word, or is an `ECALL` other than the last) and is then at the halting `ECALL` (`t0 = 0`), with `a0`
    the guest's acceptance `0`, rejection `1` or abort `2`. Since `step` is a function and stops at every `ECALL`,
    that run is the only one (`Final/HaltsSafely.lean`). Says nothing of which verdict, nor of larger inputs. -/
def HaltsSafely (img : Image) : Prop :=
  ∀ words s, words.length < maxInputWords → Loaded img words s →
    ∃ n v, Halts s n v ∧ (v = 0 ∨ v = 1 ∨ v = 2)

end Rv64mc
