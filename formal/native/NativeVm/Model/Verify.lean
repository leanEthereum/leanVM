module

public import NativeVm.Model.Whir

/-!
# The verifier, after decoding

Models `verifyWith (m := Id) keccakF1600 bytecode publicInput proof`
(`Statement/Verifier/Lib.lean`): the seed (`spongeSeedWith`), the walk (`verifyExecution
computedBytecodeValue`), and the end check (`runProof`: the stream and the openings consumed).

**The seed.** The IV is Keccak-256 of the tag `leanvm-v1` then the bytecode's words, as one run of
words in memory (`ivWords`: the tag's first eight bytes, then each word shifted up a byte past the
tag's ninth), `9 + 8n` bytes of it; the sponge starts at Keccak-f of the IV's four words, the public
input's four, then zeros.

**The walk**, phase by phase, each a module:

| phase | model | statement |
|---|---|---|
| 1 | `readAnnouncedSizes` (`Layout`) | `readAnnouncedSizes`, `buildLayout` |
| 2 | `commitStack`, `readOod` (`Stack`) | `commitStack`, `readOod` |
| 3 | `verifyBusBalance` (`Gkr`, `Bus`) | `verifyBusBalance computedBytecodeValue` |
| 4 | `tablePhase`, `tableColumnClaims` (`Tables`) | `tablePhase`, `tableColumnClaims` |
| 5 | `publicInputPhase` (`PublicInput`) | `publicInputPhase` |
| 6 | `keccakPhase` (`KeccakGkr`) | `keccakPhase`, `verifyKeccak` |
| 7 | `ringSwitch`, `verifyStackedOpening` (`RingSwitch`, `Whir`) | `ringSwitch`, `verifyStackedOpening` |
-/

@[expose] public section

namespace NativeVm.Model

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakHash

/-- The first eight bytes of `leanvm-v1`, little-endian. -/
def tagLow : UInt64 := 0x762d6d766e61656c

/-- The tag's ninth byte, `1`. -/
def tagLast : UInt64 := 0x31

/-- The words holding `leanvm-v1` then the bytecode's words: `tagLow`, then word `k + 1` the top
byte of the previous word (the tag's ninth for `k = 0`) and the low seven of word `k`. -/
def ivWords (bytecode : Array UInt64) : Array UInt64 :=
  let ext := #[tagLast <<< 56] ++ bytecode ++ #[0]
  #[tagLow] ++ (Array.range (bytecode.size + 1)).map fun k ↦
    (ext.getD k 0 >>> 56) ||| (ext.getD (k + 1) 0 <<< 8)

/-- `fiatShamirIv`: Keccak-256 of the tag and the bytecode. -/
def fiatShamirIv (bytecode : Array UInt64) : Digest :=
  keccak256 ((Native.Keccak.wordsBytes (ivWords bytecode).toList).take (9 + 8 * bytecode.size))

/-- `spongeSeedWith`: Keccak-f of the IV, the public input, zeros. -/
def seed (bytecode : Array UInt64) (publicInput : Vector UInt64 4) : KeccakState :=
  let iv := fiatShamirIv bytecode
  keccakF1600 (Vector.ofFn fun i ↦
    if h : i.val < 4 then iv[i.val] else if h' : i.val < 8 then publicInput[i.val - 4] else 0)

/-- **The walk** (`verifyExecution computedBytecodeValue`). -/
def verifyExecution (bytecode : Array UInt64) (publicInput : Vector UInt64 4) : VM Unit := do
  -- 1] memory log-size, table row counts, and the WHIR rate
  let (layout, logInverseRate) ← readAnnouncedSizes bytecode
  -- 2] the stack's commitment, and its out-of-domain sample
  commitStack layout.stackLog logInverseRate
  let ood ← readOod layout.stackLog
  -- 3] the bus
  let bus ← verifyBusBalance layout
  -- 4] the table sumcheck, and the tables' column claims
  let evaluations ← tablePhase layout bus
  let claims := bus.claims ++ tableColumnClaims evaluations
  -- 5] the public input
  let publicClaims ← publicInputPhase layout publicInput
  let claims := claims ++ publicClaims
  -- 6] KECCAK validity, by GKR over the rounds
  let (outputs, keccakPoint, keccakSlices) ← keccakPhase layout evaluations
  let claims := claims ++ outputs
  -- 7] ring switching, then one opening of the stack for every claim with a placement
  let (target, ringPoint, coefficients) ← ringSwitch keccakPoint keccakSlices
  verifyStackedOpening layout.stackLog logInverseRate
    (#[ringSwitchClaim layout target ringPoint coefficients] ++
      claims.filterMap (·.onStack layout) ++ #[ood])

/-- **The verifier after decoding**: the walk from the seed, accepting when it ends with the
stream and the openings consumed. -/
def verify (bytecode : Array UInt64) (publicInput : Vector UInt64 4) (stream : Array EW)
    (openings : Array (Array OpeningW)) : Bool :=
  let start : TState := ⟨⟨seed bytecode publicInput, #[], none⟩, stream, 0, openings, 0, #[]⟩
  match verifyExecution bytecode publicInput start with
  | some ((), s) => s.cursor == s.stream.size && s.phase == s.openings.size
  | none => false

end NativeVm.Model
