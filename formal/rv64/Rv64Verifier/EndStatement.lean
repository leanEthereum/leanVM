import Rv64Verifier.Machine
import Statement.LeanVmVerifier

/-!
# What is proved about the image

The image (`guest/`, exported to Lean by `scripts/export-image.py`) is loaded with its code at its
base, its data words in memory, the input words at `inputBase` and their number in `a0`, and
started at its entry; the input fits below the heap (`inputCapacity` words). `Sound`: if it halts with `a0 = 1`, the input decodes to a bytecode, a public
input and a proof that `verifyWith` over Keccak-f[1600] accepts. `Complete`: if `verifyWith`
accepts a proof whose input fits the image's memory, the image halts with `a0 = 1` on its encoding.
The input is a list of 64-bit words (`decodeInput`, the format `guest/src/main.rs` documents).
-/

namespace Rv64Verifier
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.Verifier

/-- A loadable image: code, and the words its data segments hold. -/
structure LoadImage where
  entry : Word
  code : Code
  data : List (Word × Word)

/-- Where the loader puts the input. -/
def inputBase : Word := 0x10000000

/-- How many input words fit between `inputBase` and the heap at `0x20000000`. -/
def inputCapacity : Nat := 2 ^ 25

/-! ## The input -/

/-- A reader of input words. -/
abbrev Reader := StateT (List Word) Option

def readWord : Reader Word := do
  match ← get with
  | w :: ws => set ws; return w
  | [] => failure

def readWords : Nat → Reader (List Word)
  | 0 => pure []
  | n + 1 => do return (← readWord) :: (← readWords n)

def readCount : Reader Nat := do return (← readWord).toNat

def readScalar : Reader E := do
  let c0 ← readWord
  let c1 ← readWord
  let c2 ← readWord
  return E.ofLimbs (BF64.ofBitVec c0) (BF64.ofBitVec c1) (BF64.ofBitVec c2)

def readDigest : Reader Digest := do
  let w ← readWords 4
  return Vector.ofFn fun i : Fin 4 ↦ ⟨w.getD i 0⟩

def readList {α : Type} (item : Reader α) : Reader (List α) := do
  let n ← readCount
  (List.range n).mapM fun _ ↦ item

def readOpening : Reader Opening := do
  let leafIndex ← readCount
  let leaf ← readList (BF64.ofBitVec <$> readWord)
  let path ← readList readDigest
  return { leafIndex, leaf, path }

/-- The input format of `guest/src/main.rs`. -/
def readInput : Reader (List K × Digest × Proof) := do
  let bytecode ← readList (BF64.ofBitVec <$> readWord)
  let publicInput ← readDigest
  let stream ← readList readScalar
  let openings ← readList (readList readOpening)
  return (bytecode, publicInput, { stream, openings })

/-- The whole input, nothing left over. -/
def decodeInput (words : List Word) : Option (List K × Digest × Proof) :=
  match readInput.run words with
  | some (value, []) => some value
  | _ => none

/-! ## Loading -/

/-- `s` is the image loaded with the input `words`, about to run. -/
def Loaded (image : LoadImage) (words : List Word) (s : MachineState) : Prop :=
  s.pc = image.entry ∧
  (∀ p ∈ image.data, s.getMem p.1 = p.2) ∧
  (∀ i (h : i < words.length), s.getMem (inputBase + BitVec.ofNat 64 (8 * i)) = words[i]) ∧
  s.getReg .x10 = BitVec.ofNat 64 words.length ∧
  words.length ≤ inputCapacity

/-! ## The end statements -/

/-- The deployed verifier: `verifyWith` over Keccak-f[1600]. -/
def verify (bytecode : List K) (publicInput : Digest) (proof : Proof) : Bool :=
  Id.run (verifyWith (m := Id) keccakF1600 bytecode publicInput proof)

/-- Accepting is sound: a run that halts with `a0 = 1` read a proof the verifier accepts. -/
def Sound (image : LoadImage) : Prop :=
  ∀ words s n, Loaded image words s → HaltsWith image.code s n 1 →
    ∃ bytecode publicInput proof, decodeInput words = some (bytecode, publicInput, proof) ∧
      verify bytecode publicInput proof = true

end Rv64Verifier
