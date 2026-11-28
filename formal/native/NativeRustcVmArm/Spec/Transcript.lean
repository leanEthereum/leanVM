module

public import NativeRustcVmArm.Code.Vm.DecodedPhase.Names
public import NativeRustcVmArm.Code.Vm.DecodedPhaseCount.Names
public import NativeRustcVmArm.Code.Vm.DecodedStreamElement.Names
public import NativeRustcVmArm.Code.Vm.SpongeWAbsorb.Names
public import NativeRustcVmArm.Code.Vm.SpongeWAbsorbNonce.Names
public import NativeRustcVmArm.Code.Vm.SpongeWDuplex.Names
public import NativeRustcVmArm.Code.Vm.SpongeWDuplexInput.Names
public import NativeRustcVmArm.Code.Vm.SpongeWSqueeze.Names
public import NativeRustcVmArm.Code.Vm.TStateGrind.Names
public import NativeRustcVmArm.Code.Vm.TStateNextScalar.Names
public import NativeRustcVmArm.Code.Vm.TStateReadCommitment.Names
public import NativeRustcVmArm.Code.Vm.TStateReadScalar.Names
public import NativeRustcVmArm.Code.Vm.TStateReadScalars.Names
public import NativeRustcVmArm.Code.Vm.TStateSampleChallenges.Names
public import NativeRustcVmArm.Spec.Keccak
public import NativeRustcVm.Transcript.Rep

/-!
# The contracts of `transcript.rs`'s and `input.rs`'s functions on AArch64

Each function uses the stack below SP (`<fn>Stack` bytes, its callees' included; `StackOk` in its
precondition) and returns with the callee-saved registers and SP kept (`Saved`), no byte changed
outside its outputs and that stack. Those that permute (`duplex` and its callers) read the round
constants (`RcAt`); the state they permute is apart from them.

The sponge's functions take it at `p` (X0) representing the model's `sp`
(`NativeRustcVm.Transcript.SpongeAt`); the transcript's take the `TState` at `t` representing the
model's `s` with the decoded area `a` (`NativeRustcVm.Transcript.TStateAt`), and leave it
representing the model's next state. A `VM` step's `none` is the Rust's `None`: a tag word `0`
(`Option<EW>`) or X0 = `0` (`Option<()>`), and on it the contract says nothing more of the
`TState` than the frame.

- `SpongeW::duplex_input(p)`: the lanes become `sp.duplexInput`.
- `SpongeW::duplex(p)`: `sp.duplex`.
- `SpongeW::absorb(p, x, tag)` (`x` in X1, X2, `tag` in X3): `sp.absorb x tag`.
- `SpongeW::squeeze(p)`: `sp.squeeze`, the challenge in X0, X1.
- `SpongeW::absorb_nonce(p, nonce)` (X1, X2): `sp.absorbNonce nonce`, the lane in X0.
- `Decoded::stream_element(out, words, len, i)` (X0 to X3; rustc passes `self.words` by value):
  the `Option<EW>` at `out` is `stream[i]?`.
- `Decoded::phase_count(dec)` (X0): the phase count in X0.
- `Decoded::phase(dec, k)` (X0, X1): phase `k`'s address in X0 if `k` is below the phase count,
  else `0` (`None`; the slice's length is always `phaseWords`).
- `TState::next_scalar(out, t)` (X0, X1): `nextScalar`, the `Option<EW>` at `out`.
- `TState::read_scalar(out, t)` (X0, X1): `readScalar`, the `Option<EW>` at `out`.
- `TState::read_scalars(t, out, n)` (X0, X1, X2): `readScalars n`, the elements at `out`.
- `TState::sample_challenges(t, out, n)` (X0, X1, X2): `sampleChallenges n` (never `none`).
- `TState::grind(t, bits)` (X0, W1; `bits < 64`, rustc compiled `pow_ok_w`'s mask for its callers'
  `grinding_bits`, at most `61`): `grind bits`.
- `TState::read_commitment(t, height, width)` (X0, X1, X2; fewer than `8` roots read, the Rust
  rejecting at `MAX_ROOTS`): `readCommitment height width`.
-/

namespace NativeRustcVmArm

open NativeRustcArm NativeVm.Model NativeRustcVm.Transcript

@[expose] public section

/-! ## Symbols -/


/-! ## Stacks -/

/-- `duplex_input` uses no stack. -/
def duplexInputStack : Nat := 0
/-- The stack `duplex` uses: its 16-byte frame and `keccak_f`'s. -/
def duplexStack : Nat := 16 + keccakFStack
/-- The stack `absorb` uses: its 48-byte frame and `duplex`'s. -/
def absorbStack : Nat := 48 + duplexStack
/-- The stack `squeeze` uses: its 16-byte frame and `duplex`'s. -/
def squeezeStack : Nat := 16 + duplexStack
/-- The stack `absorb_nonce` uses: its 16-byte frame and `absorb`'s (above `duplex`'s). -/
def absorbNonceStack : Nat := 16 + absorbStack
/-- `stream_element` uses no stack. -/
def streamElementStack : Nat := 0
/-- `phase_count` uses no stack. -/
def phaseCountStack : Nat := 0
/-- The stack `phase` uses: its 32-byte frame (`phase_count` uses none). -/
def phaseStack : Nat := 32
/-- The stack `next_scalar` uses: its 64-byte frame (`stream_element` uses none). -/
def nextScalarStack : Nat := 64
/-- The stack `read_scalar` uses: its 80-byte frame and `absorb`'s (above `next_scalar`'s). -/
def readScalarStack : Nat := 80 + absorbStack
/-- The stack `read_scalars` uses: its 64-byte frame and `read_scalar`'s. -/
def readScalarsStack : Nat := 64 + readScalarStack
/-- The stack `sample_challenges` uses: its 32-byte frame and `squeeze`'s. -/
def sampleChallengesStack : Nat := 32 + squeezeStack
/-- The stack `grind` uses: its 64-byte frame and `absorb_nonce`'s (above `next_scalar`'s). -/
def grindStack : Nat := 64 + absorbNonceStack
/-- The stack `read_commitment` uses: its 80-byte frame and `read_scalar`'s. -/
def readCommitmentStack : Nat := 80 + readScalarStack

section
variable [Labels]

/-! ## Footprints -/

/-- The sponge at `p` for a function using `n` bytes of stack: data memory, not wrapping, apart
from the stack and the round constants. -/
def SpongeOk (m : MachineData) (p : BitVec 64) (n : Nat) : Prop :=
  Mapped m.dmem p spongeBytes ∧ NoWrap p spongeBytes ∧
    Apart p spongeBytes (stackBelow m n) n ∧ Apart p spongeBytes rcAddr 192

/-- The `TState` at `t` and its decoded area for a function using `n` bytes of stack: apart from
the stack, the `TState` apart from the round constants. -/
def TStateOk (m : MachineData) (t : BitVec 64) (a : DecArea) (n : Nat) : Prop :=
  Apart t tstateBytes (stackBelow m n) n ∧ Apart a.words (8 * a.len) (stackBelow m n) n ∧
    Apart t tstateBytes rcAddr 192

/-- An output of `n` bytes at `o` beside the `TState` at `t`: data memory, not wrapping, apart
from the `TState`, its decoded area, the stack and the round constants. -/
def OutOk (m : MachineData) (t : BitVec 64) (a : DecArea) (o : BitVec 64) (n N : Nat) : Prop :=
  Mapped m.dmem o n ∧ NoWrap o n ∧ Apart o n t tstateBytes ∧ Apart o n a.words (8 * a.len) ∧
    Apart o n (stackBelow m N) N ∧ Apart o n rcAddr 192

/-- `Some`/`None` of `Option<()>` in X0. -/
def okWord (b : Bool) : UInt64 := if b then 1 else 0

/-! ## The sponge -/

/-- `duplex_input`'s precondition. -/
def DuplexInputPre (sp : SpongeW) (m : MachineData) : Prop :=
  StackOk m duplexInputStack ∧ SpongeOk m m.regs.X0.toBitVec duplexInputStack ∧
    SpongeAt m.dmem m.regs.X0.toBitVec sp

/-- `duplex_input`'s postcondition. -/
def DuplexInputPost (sp : SpongeW) (m m' : MachineData) : Prop :=
  let p := m.regs.X0.toBitVec
  SpongeAt m'.dmem p { sp with state := sp.duplexInput } ∧
    SameOutside m.dmem m'.dmem (InRange p spongeBytes) ∧ Saved m m'

/-- `duplex`'s precondition. -/
def DuplexPre (sp : SpongeW) (m : MachineData) : Prop :=
  StackOk m duplexStack ∧ RcAt m duplexStack ∧ SpongeOk m m.regs.X0.toBitVec duplexStack ∧
    SpongeAt m.dmem m.regs.X0.toBitVec sp

/-- `duplex`'s postcondition. -/
def DuplexPost (sp : SpongeW) (m m' : MachineData) : Prop :=
  let p := m.regs.X0.toBitVec
  SpongeAt m'.dmem p sp.duplex ∧
    SameOutside m.dmem m'.dmem (fun q ↦ InRange p spongeBytes q ∨
      InRange (stackBelow m duplexStack) duplexStack q) ∧ Saved m m'

/-- `absorb`'s precondition. -/
def AbsorbPre (sp : SpongeW) (m : MachineData) : Prop :=
  StackOk m absorbStack ∧ RcAt m absorbStack ∧ SpongeOk m m.regs.X0.toBitVec absorbStack ∧
    SpongeAt m.dmem m.regs.X0.toBitVec sp

/-- `absorb`'s postcondition. -/
def AbsorbPost (sp : SpongeW) (m m' : MachineData) : Prop :=
  let p := m.regs.X0.toBitVec
  SpongeAt m'.dmem p (sp.absorb ⟨m.regs.X1, m.regs.X2⟩ m.regs.X3) ∧
    SameOutside m.dmem m'.dmem (fun q ↦ InRange p spongeBytes q ∨
      InRange (stackBelow m absorbStack) absorbStack q) ∧ Saved m m'

/-- `squeeze`'s precondition. -/
def SqueezePre (sp : SpongeW) (m : MachineData) : Prop :=
  StackOk m squeezeStack ∧ RcAt m squeezeStack ∧ SpongeOk m m.regs.X0.toBitVec squeezeStack ∧
    SpongeAt m.dmem m.regs.X0.toBitVec sp

/-- `squeeze`'s postcondition. -/
def SqueezePost (sp : SpongeW) (m m' : MachineData) : Prop :=
  let p := m.regs.X0.toBitVec
  m'.regs.X0 = sp.squeeze.1.c0 ∧ m'.regs.X1 = sp.squeeze.1.c1 ∧
    SpongeAt m'.dmem p sp.squeeze.2 ∧
    SameOutside m.dmem m'.dmem (fun q ↦ InRange p spongeBytes q ∨
      InRange (stackBelow m squeezeStack) squeezeStack q) ∧ Saved m m'

/-- `absorb_nonce`'s precondition. -/
def AbsorbNoncePre (sp : SpongeW) (m : MachineData) : Prop :=
  StackOk m absorbNonceStack ∧ RcAt m absorbNonceStack ∧
    SpongeOk m m.regs.X0.toBitVec absorbNonceStack ∧ SpongeAt m.dmem m.regs.X0.toBitVec sp

/-- `absorb_nonce`'s postcondition. -/
def AbsorbNoncePost (sp : SpongeW) (m m' : MachineData) : Prop :=
  let p := m.regs.X0.toBitVec
  let r := sp.absorbNonce ⟨m.regs.X1, m.regs.X2⟩
  m'.regs.X0 = r.1 ∧ SpongeAt m'.dmem p r.2 ∧
    SameOutside m.dmem m'.dmem (fun q ↦ InRange p spongeBytes q ∨
      InRange (stackBelow m absorbNonceStack) absorbNonceStack q) ∧ Saved m m'

/-! ## The decoded proof -/

/-- `stream_element`'s precondition: the area `a` (X1, X2) holds the stream, the output (X0, 24
bytes) apart from it. -/
def StreamElementPre (a : DecArea) (stream : Array EW) (openings : Array (Array OpeningW))
    (m : MachineData) : Prop :=
  let o := m.regs.X0.toBitVec
  StackOk m streamElementStack ∧ m.regs.X1.toBitVec = a.words ∧ m.regs.X2.toNat = a.len ∧
    NativeRustcVm.Region.Ok m.dmem a.region ∧ DecodedAt m.dmem a stream openings ∧
    Mapped m.dmem o 24 ∧ NoWrap o 24 ∧ Apart o 24 a.words (8 * a.len)

/-- `stream_element`'s postcondition. -/
def StreamElementPost (stream : Array EW) (m m' : MachineData) : Prop :=
  let o := m.regs.X0.toBitVec
  OptEWAt m'.dmem o stream[m.regs.X3.toNat]? ∧ SameOutside m.dmem m'.dmem (InRange o 24) ∧
    Saved m m'

/-- `phase_count`'s precondition: the `Decoded` at X0 (24 bytes, apart from the area) names the
area `a`, which holds the openings. -/
def PhaseCountPre (a : DecArea) (stream : Array EW) (openings : Array (Array OpeningW))
    (m : MachineData) : Prop :=
  let dp := m.regs.X0.toBitVec
  StackOk m phaseCountStack ∧ DecFieldsAt m.dmem dp a ∧ Mapped m.dmem dp 24 ∧ NoWrap dp 24 ∧
    Apart dp 24 a.words (8 * a.len) ∧ NativeRustcVm.Region.Ok m.dmem a.region ∧
    DecodedAt m.dmem a stream openings

/-- `phase_count`'s postcondition. -/
def PhaseCountPost (openings : Array (Array OpeningW)) (m m' : MachineData) : Prop :=
  m'.regs.X0 = openings.size.toUInt64 ∧ SameOutside m.dmem m'.dmem (fun _ ↦ False) ∧ Saved m m'

/-- `phase`'s precondition: as `phase_count`'s, the `Decoded` and the area apart from the stack. -/
def PhasePre (a : DecArea) (stream : Array EW) (openings : Array (Array OpeningW))
    (m : MachineData) : Prop :=
  let dp := m.regs.X0.toBitVec
  StackOk m phaseStack ∧ DecFieldsAt m.dmem dp a ∧ Mapped m.dmem dp 24 ∧ NoWrap dp 24 ∧
    Apart dp 24 a.words (8 * a.len) ∧ Apart dp 24 (stackBelow m phaseStack) phaseStack ∧
    NativeRustcVm.Region.Ok m.dmem a.region ∧
    Apart a.words (8 * a.len) (stackBelow m phaseStack) phaseStack ∧
    DecodedAt m.dmem a stream openings

/-- `phase`'s postcondition: phase `k`'s address, or `0`. -/
def PhasePost (a : DecArea) (openings : Array (Array OpeningW)) (m m' : MachineData) : Prop :=
  m'.regs.X0 = (if m.regs.X1.toNat < openings.size then
      UInt64.ofBitVec (a.word (NativeVm.phaseBase a.l m.regs.X1.toNat)) else 0) ∧
    SameOutside m.dmem m'.dmem (InRange (stackBelow m phaseStack) phaseStack) ∧ Saved m m'

/-! ## The transcript -/

/-- What a `VM` step leaves at `t`: on `some`, the `TState` represents the next state. -/
def NextAt {α : Type} (d : Mem 64) (t : BitVec 64) (a : DecArea) (r : Option (α × TState)) :
    Prop :=
  ∀ x s', r = some (x, s') → TStateAt d t a s'

/-- `next_scalar`'s precondition. -/
def NextScalarPre (a : DecArea) (s : TState) (m : MachineData) : Prop :=
  let t := m.regs.X1.toBitVec
  StackOk m nextScalarStack ∧ TStateAt m.dmem t a s ∧ TStateOk m t a nextScalarStack ∧
    OutOk m t a m.regs.X0.toBitVec 24 nextScalarStack

/-- `next_scalar`'s postcondition. -/
def NextScalarPost (a : DecArea) (s : TState) (m m' : MachineData) : Prop :=
  let t := m.regs.X1.toBitVec; let o := m.regs.X0.toBitVec
  OptEWAt m'.dmem o ((nextScalar.run s).map (·.1)) ∧ NextAt m'.dmem t a (nextScalar.run s) ∧
    SameOutside m.dmem m'.dmem (fun q ↦ InRange o 24 q ∨ InRange t tstateBytes q ∨
      InRange (stackBelow m nextScalarStack) nextScalarStack q) ∧ Saved m m'

/-- `read_scalar`'s precondition. -/
def ReadScalarPre (a : DecArea) (s : TState) (m : MachineData) : Prop :=
  let t := m.regs.X1.toBitVec
  StackOk m readScalarStack ∧ RcAt m readScalarStack ∧ TStateAt m.dmem t a s ∧
    TStateOk m t a readScalarStack ∧ OutOk m t a m.regs.X0.toBitVec 24 readScalarStack

/-- `read_scalar`'s postcondition. -/
def ReadScalarPost (a : DecArea) (s : TState) (m m' : MachineData) : Prop :=
  let t := m.regs.X1.toBitVec; let o := m.regs.X0.toBitVec
  OptEWAt m'.dmem o ((readScalar.run s).map (·.1)) ∧ NextAt m'.dmem t a (readScalar.run s) ∧
    SameOutside m.dmem m'.dmem (fun q ↦ InRange o 24 q ∨ InRange t tstateBytes q ∨
      InRange (stackBelow m readScalarStack) readScalarStack q) ∧ Saved m m'

/-- `read_scalars`'s precondition: the output, `n` elements at X1, X2 = `n`. -/
def ReadScalarsPre (a : DecArea) (s : TState) (m : MachineData) : Prop :=
  let t := m.regs.X0.toBitVec
  StackOk m readScalarsStack ∧ RcAt m readScalarsStack ∧ TStateAt m.dmem t a s ∧
    TStateOk m t a readScalarsStack ∧
    OutOk m t a m.regs.X1.toBitVec (16 * m.regs.X2.toNat) readScalarsStack

/-- `read_scalars`'s postcondition. -/
def ReadScalarsPost (a : DecArea) (s : TState) (m m' : MachineData) : Prop :=
  let t := m.regs.X0.toBitVec; let o := m.regs.X1.toBitVec; let n := m.regs.X2.toNat
  let r := (readScalars n).run s
  m'.regs.X0 = okWord r.isSome ∧
    (∀ xs s', r = some (xs, s') → NativeRustcVm.EWsAt m'.dmem o xs.toList) ∧
    NextAt m'.dmem t a r ∧
    SameOutside m.dmem m'.dmem (fun q ↦ InRange o (16 * n) q ∨ InRange t tstateBytes q ∨
      InRange (stackBelow m readScalarsStack) readScalarsStack q) ∧ Saved m m'

/-- `sample_challenges`'s precondition: the output, `n` elements at X1, X2 = `n`. -/
def SampleChallengesPre (a : DecArea) (s : TState) (m : MachineData) : Prop :=
  let t := m.regs.X0.toBitVec
  StackOk m sampleChallengesStack ∧ RcAt m sampleChallengesStack ∧ TStateAt m.dmem t a s ∧
    TStateOk m t a sampleChallengesStack ∧
    OutOk m t a m.regs.X1.toBitVec (16 * m.regs.X2.toNat) sampleChallengesStack

/-- `sample_challenges`'s postcondition. -/
def SampleChallengesPost (a : DecArea) (s : TState) (m m' : MachineData) : Prop :=
  let t := m.regs.X0.toBitVec; let o := m.regs.X1.toBitVec; let n := m.regs.X2.toNat
  (∃ xs s', (sampleChallenges n).run s = some (xs, s') ∧ NativeRustcVm.EWsAt m'.dmem o xs.toList ∧
    TStateAt m'.dmem t a s') ∧
    SameOutside m.dmem m'.dmem (fun q ↦ InRange o (16 * n) q ∨ InRange t tstateBytes q ∨
      InRange (stackBelow m sampleChallengesStack) sampleChallengesStack q) ∧ Saved m m'

/-- `grind`'s bit count: W1. -/
def grindBits (m : MachineData) : Nat := m.regs.X1.toNat % 2 ^ 32

/-- `grind`'s precondition: fewer than `64` bits. -/
def GrindPre (a : DecArea) (s : TState) (m : MachineData) : Prop :=
  let t := m.regs.X0.toBitVec
  StackOk m grindStack ∧ RcAt m grindStack ∧ TStateAt m.dmem t a s ∧ TStateOk m t a grindStack ∧
    grindBits m < 64

/-- `grind`'s postcondition. -/
def GrindPost (a : DecArea) (s : TState) (m m' : MachineData) : Prop :=
  let t := m.regs.X0.toBitVec
  let r := (grind (grindBits m)).run s
  m'.regs.X0 = okWord r.isSome ∧ NextAt m'.dmem t a r ∧
    SameOutside m.dmem m'.dmem (fun q ↦ InRange t tstateBytes q ∨
      InRange (stackBelow m grindStack) grindStack q) ∧ Saved m m'

/-- `read_commitment`'s precondition: fewer than `maxRoots` roots read. -/
def ReadCommitmentPre (a : DecArea) (s : TState) (m : MachineData) : Prop :=
  let t := m.regs.X0.toBitVec
  StackOk m readCommitmentStack ∧ RcAt m readCommitmentStack ∧ TStateAt m.dmem t a s ∧
    TStateOk m t a readCommitmentStack ∧ s.roots.size < maxRoots

/-- `read_commitment`'s postcondition. -/
def ReadCommitmentPost (a : DecArea) (s : TState) (m m' : MachineData) : Prop :=
  let t := m.regs.X0.toBitVec
  let r := (readCommitment m.regs.X1.toNat m.regs.X2.toNat).run s
  m'.regs.X0 = okWord r.isSome ∧ NextAt m'.dmem t a r ∧
    SameOutside m.dmem m'.dmem (fun q ↦ InRange t tstateBytes q ∨
      InRange (stackBelow m readCommitmentStack) readCommitmentStack q) ∧ Saved m m'

end

end

end NativeRustcVmArm
