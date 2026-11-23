module

public import NativeRustcVmX64.Spec.Keccak
public import NativeRustcVmX64.Basic
public import NativeRustcX64.Spec.Got
public import NativeRustcVm.Transcript.Rep
public import NativeRustcVmX64.Code.Vm.DecodedPhase.Names
public import NativeRustcVmX64.Code.Vm.DecodedPhaseCount.Names
public import NativeRustcVmX64.Code.Vm.DecodedStreamElement.Names
public import NativeRustcVmX64.Code.Vm.SpongeWAbsorb.Names
public import NativeRustcVmX64.Code.Vm.SpongeWAbsorbNonce.Names
public import NativeRustcVmX64.Code.Vm.SpongeWDuplex.Names
public import NativeRustcVmX64.Code.Vm.SpongeWDuplexInput.Names
public import NativeRustcVmX64.Code.Vm.SpongeWSqueeze.Names
public import NativeRustcVmX64.Code.Vm.TStateGrind.Names
public import NativeRustcVmX64.Code.Vm.TStateNextScalar.Names
public import NativeRustcVmX64.Code.Vm.TStateReadCommitment.Names
public import NativeRustcVmX64.Code.Vm.TStateReadScalar.Names
public import NativeRustcVmX64.Code.Vm.TStateReadScalars.Names
public import NativeRustcVmX64.Code.Vm.TStateSampleChallenges.Names

/-!
# The contracts of `transcript.rs`'s and `input.rs`'s functions on x86-64

The AArch64 contracts (`NativeRustcVmArm.Spec.Transcript`) with the System V registers: arguments
in RDI, RSI, RDX, RCX, the result in RAX (and RDX). Each function uses the stack below RSP
(`<fn>Stack` bytes: its pushes, its frame, its callees' return addresses and stacks; `StackOk` in
its precondition also maps the return address at RSP) and returns with the callee-saved registers
kept (and RSP 8 above, `Spec`), no byte changed outside its outputs and that stack. Those that
permute (`duplex` and its callers) read the round constants (`RcAt`) and the `memcpy` GOT slot
(`GotAt`), protected from their existing data areas and stack. Other functions need no GOT premise.

The sponge's functions take it at `p` (RDI) representing the model's `sp`
(`NativeRustcVm.Transcript.SpongeAt`); the transcript's take the `TState` at `t` representing the
model's `s` with the decoded area `a` (`NativeRustcVm.Transcript.TStateAt`), and leave it
representing the model's next state. A `VM` step's `none` is the Rust's `None`: a tag word `0`
(`Option<EW>`) or AL = `0` (`Option<()>`, a `bool`: rustc sets AL alone, `OkAl`), and on it the
contract says nothing more of the `TState` than the frame.

- `SpongeW::duplex_input(p)`: the lanes become `sp.duplexInput`.
- `SpongeW::duplex(p)`: `sp.duplex`.
- `SpongeW::absorb(p, x, tag)` (`x` in RSI, RDX, `tag` in RCX): `sp.absorb x tag`.
- `SpongeW::squeeze(p)`: `sp.squeeze`, the challenge in RAX, RDX.
- `SpongeW::absorb_nonce(p, nonce)` (RSI, RDX): `sp.absorbNonce nonce`, the lane in RAX.
- `Decoded::stream_element(out, words, len, i)` (RDI to RCX; rustc passes `self.words` by value):
  the `Option<EW>` at `out` is `stream[i]?`.
- `Decoded::phase_count(dec)` (RDI): the phase count in RAX.
- `Decoded::phase(dec, k)` (RDI, RSI): phase `k`'s address in RAX if `k` is below the phase
  count, else `0` (`None`; the slice's length is always `phaseWords`).
- `TState::next_scalar(out, t)` (RDI, RSI): `nextScalar`, the `Option<EW>` at `out`.
- `TState::read_scalar(out, t)` (RDI, RSI): `readScalar`, the `Option<EW>` at `out`.
- `TState::read_scalars(t, out, n)` (RDI, RSI, RDX): `readScalars n`, the elements at `out`.
- `TState::sample_challenges(t, out, n)` (RDI, RSI, RDX): `sampleChallenges n` (never `none`).
- `TState::grind(t, bits)` (RDI, ESI; `bits < 64`, rustc compiled `pow_ok_w`'s mask for its callers'
  `grinding_bits`, at most `61`): `grind bits`.
- `TState::read_commitment(t, height, width)` (RDI, RSI, RDX; fewer than `8` roots read, the Rust
  rejecting at `MAX_ROOTS`): `readCommitment height width`.
-/

namespace NativeRustcVmX64

open NativeRustcX64 NativeVm.Model NativeRustcVm.Transcript

@[expose] public section

/-! ## Stacks -/

/-- `duplex_input` uses no stack. -/
def duplexInputStack : Nat := 0
/-- The stack `duplex` uses: its push, then `keccak_f`'s return address and stack
(`duplex_input` uses only its return address). -/
def duplexStack : Nat := 8 + 8 + keccakFStack
/-- The stack `absorb` uses: its 5 pushes, then `duplex`'s return address and stack. -/
def absorbStack : Nat := 40 + 8 + duplexStack
/-- The stack `squeeze` uses: its push, then `duplex`'s return address and stack. -/
def squeezeStack : Nat := 8 + 8 + duplexStack
/-- The stack `absorb_nonce` uses: its push, then `absorb`'s return address and stack (above
`duplex`'s). -/
def absorbNonceStack : Nat := 8 + 8 + absorbStack
/-- `stream_element` uses no stack. -/
def streamElementStack : Nat := 0
/-- `phase_count` uses no stack. -/
def phaseCountStack : Nat := 0
/-- The stack `phase` uses: its 3 pushes, then `phase_count`'s return address. -/
def phaseStack : Nat := 24 + 8
/-- The stack `next_scalar` uses: its 3 pushes, its 32-byte frame, then `stream_element`'s return
address. -/
def nextScalarStack : Nat := 24 + 32 + 8
/-- The stack `read_scalar` uses: its 5 pushes, its 32-byte frame, then `absorb`'s return address
and stack (above `next_scalar`'s). -/
def readScalarStack : Nat := 40 + 32 + 8 + absorbStack
/-- The stack `read_scalars` uses: its 5 pushes, its 32-byte frame, then `read_scalar`'s return
address and stack. -/
def readScalarsStack : Nat := 40 + 32 + 8 + readScalarStack
/-- The stack `sample_challenges` uses: its 3 pushes, then `squeeze`'s return address and
stack. -/
def sampleChallengesStack : Nat := 24 + 8 + squeezeStack
/-- The stack `grind` uses: its 2 pushes, its 24-byte frame, then `absorb_nonce`'s return address
and stack (above `next_scalar`'s). -/
def grindStack : Nat := 16 + 24 + 8 + absorbNonceStack
/-- The stack `read_commitment` uses: its 5 pushes, its 32-byte frame, then `read_scalar`'s
return address and stack. -/
def readCommitmentStack : Nat := 40 + 32 + 8 + readScalarStack

section
variable [Labels]

/-! ## Footprints -/

/-- The sponge at `p` for a function using `n` bytes of stack: data memory, not wrapping, apart
from the stack (and the return address) and the round constants. -/
def SpongeOk (m : MachineData) (p : BitVec 64) (n : Nat) : Prop :=
  Mapped m.dmem p spongeBytes ∧ NoWrap p spongeBytes ∧
    Apart p spongeBytes (stackBelow m n) (n + 8) ∧ Apart p spongeBytes rcAddr 192

/-- The `TState` at `t` and its decoded area for a function using `n` bytes of stack: apart from
the stack (and the return address), the `TState` apart from the round constants. -/
def TStateOk (m : MachineData) (t : BitVec 64) (a : DecArea) (n : Nat) : Prop :=
  Apart t tstateBytes (stackBelow m n) (n + 8) ∧ Apart a.words (8 * a.len) (stackBelow m n) (n + 8) ∧
    Apart t tstateBytes rcAddr 192

/-- An output of `n` bytes at `o` beside the `TState` at `t`: data memory, not wrapping, apart
from the `TState`, its decoded area, the stack (and the return address) and the round
constants. -/
def OutOk (m : MachineData) (t : BitVec 64) (a : DecArea) (o : BitVec 64) (n N : Nat) : Prop :=
  Mapped m.dmem o n ∧ NoWrap o n ∧ Apart o n t tstateBytes ∧ Apart o n a.words (8 * a.len) ∧
    Apart o n (stackBelow m N) (N + 8) ∧ Apart o n rcAddr 192

/-- `Some`/`None` of `Option<()>` as a word. -/
def okWord (b : Bool) : UInt64 := if b then 1 else 0

/-- `Some`/`None` of `Option<()>` in AL (rustc returns the `bool` in AL alone, `boolRet`). -/
def OkAl (m : MachineData) (b : Bool) : Prop := boolRet m = (okWord b).toNat

/-! ## The sponge -/

/-- `duplex_input`'s precondition. -/
def DuplexInputPre (sp : SpongeW) (m : MachineData) : Prop :=
  StackOk m duplexInputStack ∧ SpongeOk m (reg m .rdi) duplexInputStack ∧
    SpongeAt m.dmem (reg m .rdi) sp

/-- `duplex_input`'s postcondition. -/
def DuplexInputPost (sp : SpongeW) (m m' : MachineData) : Prop :=
  let p := reg m .rdi
  SpongeAt m'.dmem p { sp with state := sp.duplexInput } ∧
    SameOutside m.dmem m'.dmem (InRange p spongeBytes) ∧ Saved m m'

/-- `duplex`'s precondition. -/
def DuplexPre (sp : SpongeW) (m : MachineData) : Prop :=
  StackOk m duplexStack ∧ RcAt m duplexStack ∧ SpongeOk m (reg m .rdi) duplexStack ∧
    SpongeAt m.dmem (reg m .rdi) sp ∧
    GotAt m duplexStack [(reg m .rdi, spongeBytes), (rcAddr, 192)] ["memcpy"]

/-- `duplex`'s postcondition. -/
def DuplexPost (sp : SpongeW) (m m' : MachineData) : Prop :=
  let p := reg m .rdi
  SpongeAt m'.dmem p sp.duplex ∧
    SameOutside m.dmem m'.dmem (fun q ↦ InRange p spongeBytes q ∨
      InRange (stackBelow m duplexStack) duplexStack q) ∧ Saved m m'

/-- `absorb`'s precondition. -/
def AbsorbPre (sp : SpongeW) (m : MachineData) : Prop :=
  StackOk m absorbStack ∧ RcAt m absorbStack ∧ SpongeOk m (reg m .rdi) absorbStack ∧
    SpongeAt m.dmem (reg m .rdi) sp ∧
    GotAt m absorbStack [(reg m .rdi, spongeBytes), (rcAddr, 192)] ["memcpy"]

/-- `absorb`'s postcondition. -/
def AbsorbPost (sp : SpongeW) (m m' : MachineData) : Prop :=
  let p := reg m .rdi
  SpongeAt m'.dmem p (sp.absorb ⟨.ofBitVec (reg m .rsi), .ofBitVec (reg m .rdx)⟩
      (.ofBitVec (reg m .rcx))) ∧
    SameOutside m.dmem m'.dmem (fun q ↦ InRange p spongeBytes q ∨
      InRange (stackBelow m absorbStack) absorbStack q) ∧ Saved m m'

/-- `squeeze`'s precondition. -/
def SqueezePre (sp : SpongeW) (m : MachineData) : Prop :=
  StackOk m squeezeStack ∧ RcAt m squeezeStack ∧ SpongeOk m (reg m .rdi) squeezeStack ∧
    SpongeAt m.dmem (reg m .rdi) sp ∧
    GotAt m squeezeStack [(reg m .rdi, spongeBytes), (rcAddr, 192)] ["memcpy"]

/-- `squeeze`'s postcondition. -/
def SqueezePost (sp : SpongeW) (m m' : MachineData) : Prop :=
  let p := reg m .rdi
  reg m' .rax = sp.squeeze.1.c0.toBitVec ∧ reg m' .rdx = sp.squeeze.1.c1.toBitVec ∧
    SpongeAt m'.dmem p sp.squeeze.2 ∧
    SameOutside m.dmem m'.dmem (fun q ↦ InRange p spongeBytes q ∨
      InRange (stackBelow m squeezeStack) squeezeStack q) ∧ Saved m m'

/-- `absorb_nonce`'s precondition. -/
def AbsorbNoncePre (sp : SpongeW) (m : MachineData) : Prop :=
  StackOk m absorbNonceStack ∧ RcAt m absorbNonceStack ∧
    SpongeOk m (reg m .rdi) absorbNonceStack ∧ SpongeAt m.dmem (reg m .rdi) sp ∧
    GotAt m absorbNonceStack [(reg m .rdi, spongeBytes), (rcAddr, 192)] ["memcpy"]

/-- `absorb_nonce`'s postcondition. -/
def AbsorbNoncePost (sp : SpongeW) (m m' : MachineData) : Prop :=
  let p := reg m .rdi
  let r := sp.absorbNonce ⟨.ofBitVec (reg m .rsi), .ofBitVec (reg m .rdx)⟩
  reg m' .rax = r.1.toBitVec ∧ SpongeAt m'.dmem p r.2 ∧
    SameOutside m.dmem m'.dmem (fun q ↦ InRange p spongeBytes q ∨
      InRange (stackBelow m absorbNonceStack) absorbNonceStack q) ∧ Saved m m'

/-! ## The decoded proof -/

/-- `stream_element`'s precondition: the area `a` (RSI, RDX) holds the stream, the output (RDI,
24 bytes) apart from it and from the return address at RSP (unlike AArch64's, x86-64's return
address is in memory, and a leaf writing over it would not return). -/
def StreamElementPre (a : DecArea) (stream : Array EW) (openings : Array (Array OpeningW))
    (m : MachineData) : Prop :=
  let o := reg m .rdi
  StackOk m streamElementStack ∧ reg m .rsi = a.words ∧ (reg m .rdx).toNat = a.len ∧
    NativeRustcVm.Region.Ok m.dmem a.region ∧ DecodedAt m.dmem a stream openings ∧
    Mapped m.dmem o 24 ∧ NoWrap o 24 ∧ Apart o 24 a.words (8 * a.len) ∧
    Apart o 24 (stackBelow m streamElementStack) (streamElementStack + 8)

/-- `stream_element`'s postcondition. -/
def StreamElementPost (stream : Array EW) (m m' : MachineData) : Prop :=
  let o := reg m .rdi
  OptEWAt m'.dmem o stream[(reg m .rcx).toNat]? ∧ SameOutside m.dmem m'.dmem (InRange o 24) ∧
    Saved m m'

/-- `phase_count`'s precondition: the `Decoded` at RDI (24 bytes, apart from the area) names the
area `a`, which holds the openings. -/
def PhaseCountPre (a : DecArea) (stream : Array EW) (openings : Array (Array OpeningW))
    (m : MachineData) : Prop :=
  let dp := reg m .rdi
  StackOk m phaseCountStack ∧ DecFieldsAt m.dmem dp a ∧ Mapped m.dmem dp 24 ∧ NoWrap dp 24 ∧
    Apart dp 24 a.words (8 * a.len) ∧ NativeRustcVm.Region.Ok m.dmem a.region ∧
    DecodedAt m.dmem a stream openings

/-- `phase_count`'s postcondition. -/
def PhaseCountPost (openings : Array (Array OpeningW)) (m m' : MachineData) : Prop :=
  reg m' .rax = openings.size.toUInt64.toBitVec ∧ SameOutside m.dmem m'.dmem (fun _ ↦ False) ∧
    Saved m m'

/-- `phase`'s precondition: as `phase_count`'s, the `Decoded` and the area apart from the stack
(and the return address). -/
def PhasePre (a : DecArea) (stream : Array EW) (openings : Array (Array OpeningW))
    (m : MachineData) : Prop :=
  let dp := reg m .rdi
  StackOk m phaseStack ∧ DecFieldsAt m.dmem dp a ∧ Mapped m.dmem dp 24 ∧ NoWrap dp 24 ∧
    Apart dp 24 a.words (8 * a.len) ∧ Apart dp 24 (stackBelow m phaseStack) (phaseStack + 8) ∧
    NativeRustcVm.Region.Ok m.dmem a.region ∧
    Apart a.words (8 * a.len) (stackBelow m phaseStack) (phaseStack + 8) ∧
    DecodedAt m.dmem a stream openings

/-- `phase`'s postcondition: phase `k`'s address, or `0`. -/
def PhasePost (a : DecArea) (openings : Array (Array OpeningW)) (m m' : MachineData) : Prop :=
  reg m' .rax = (if (reg m .rsi).toNat < openings.size then
      a.word (NativeVm.phaseBase a.l (reg m .rsi).toNat) else 0) ∧
    SameOutside m.dmem m'.dmem (InRange (stackBelow m phaseStack) phaseStack) ∧ Saved m m'

/-! ## The transcript -/

/-- What a `VM` step leaves at `t`: on `some`, the `TState` represents the next state. -/
def NextAt {α : Type} (d : Mem 64) (t : BitVec 64) (a : DecArea) (r : Option (α × TState)) :
    Prop :=
  ∀ x s', r = some (x, s') → TStateAt d t a s'

/-- `next_scalar`'s precondition. -/
def NextScalarPre (a : DecArea) (s : TState) (m : MachineData) : Prop :=
  let t := reg m .rsi
  StackOk m nextScalarStack ∧ TStateAt m.dmem t a s ∧ TStateOk m t a nextScalarStack ∧
    OutOk m t a (reg m .rdi) 24 nextScalarStack

/-- `next_scalar`'s postcondition. -/
def NextScalarPost (a : DecArea) (s : TState) (m m' : MachineData) : Prop :=
  let t := reg m .rsi; let o := reg m .rdi
  OptEWAt m'.dmem o ((nextScalar.run s).map (·.1)) ∧ NextAt m'.dmem t a (nextScalar.run s) ∧
    SameOutside m.dmem m'.dmem (fun q ↦ InRange o 24 q ∨ InRange t tstateBytes q ∨
      InRange (stackBelow m nextScalarStack) nextScalarStack q) ∧ Saved m m'

/-- `read_scalar`'s precondition. -/
def ReadScalarPre (a : DecArea) (s : TState) (m : MachineData) : Prop :=
  let t := reg m .rsi
  StackOk m readScalarStack ∧ RcAt m readScalarStack ∧ TStateAt m.dmem t a s ∧
    TStateOk m t a readScalarStack ∧ OutOk m t a (reg m .rdi) 24 readScalarStack ∧
    GotAt m readScalarStack [(t, tstateBytes), (a.words, 8 * a.len), (reg m .rdi, 24),
      (rcAddr, 192)] ["memcpy"]

/-- `read_scalar`'s postcondition. -/
def ReadScalarPost (a : DecArea) (s : TState) (m m' : MachineData) : Prop :=
  let t := reg m .rsi; let o := reg m .rdi
  OptEWAt m'.dmem o ((readScalar.run s).map (·.1)) ∧ NextAt m'.dmem t a (readScalar.run s) ∧
    SameOutside m.dmem m'.dmem (fun q ↦ InRange o 24 q ∨ InRange t tstateBytes q ∨
      InRange (stackBelow m readScalarStack) readScalarStack q) ∧ Saved m m'

/-- `read_scalars`'s precondition: the output, `n` elements at RSI, RDX = `n`. -/
def ReadScalarsPre (a : DecArea) (s : TState) (m : MachineData) : Prop :=
  let t := reg m .rdi
  StackOk m readScalarsStack ∧ RcAt m readScalarsStack ∧ TStateAt m.dmem t a s ∧
    TStateOk m t a readScalarsStack ∧
    OutOk m t a (reg m .rsi) (16 * (reg m .rdx).toNat) readScalarsStack ∧
    GotAt m readScalarsStack [(t, tstateBytes), (a.words, 8 * a.len),
      (reg m .rsi, 16 * (reg m .rdx).toNat), (rcAddr, 192)] ["memcpy"]

/-- `read_scalars`'s postcondition. -/
def ReadScalarsPost (a : DecArea) (s : TState) (m m' : MachineData) : Prop :=
  let t := reg m .rdi; let o := reg m .rsi; let n := (reg m .rdx).toNat
  let r := (readScalars n).run s
  OkAl m' r.isSome ∧
    (∀ xs s', r = some (xs, s') → NativeRustcVm.EWsAt m'.dmem o xs.toList) ∧
    NextAt m'.dmem t a r ∧
    SameOutside m.dmem m'.dmem (fun q ↦ InRange o (16 * n) q ∨ InRange t tstateBytes q ∨
      InRange (stackBelow m readScalarsStack) readScalarsStack q) ∧ Saved m m'

/-- `sample_challenges`'s precondition: the output, `n` elements at RSI, RDX = `n`. -/
def SampleChallengesPre (a : DecArea) (s : TState) (m : MachineData) : Prop :=
  let t := reg m .rdi
  StackOk m sampleChallengesStack ∧ RcAt m sampleChallengesStack ∧ TStateAt m.dmem t a s ∧
    TStateOk m t a sampleChallengesStack ∧
    OutOk m t a (reg m .rsi) (16 * (reg m .rdx).toNat) sampleChallengesStack ∧
    GotAt m sampleChallengesStack [(t, tstateBytes), (a.words, 8 * a.len),
      (reg m .rsi, 16 * (reg m .rdx).toNat), (rcAddr, 192)] ["memcpy"]

/-- `sample_challenges`'s postcondition. -/
def SampleChallengesPost (a : DecArea) (s : TState) (m m' : MachineData) : Prop :=
  let t := reg m .rdi; let o := reg m .rsi; let n := (reg m .rdx).toNat
  (∃ xs s', (sampleChallenges n).run s = some (xs, s') ∧ NativeRustcVm.EWsAt m'.dmem o xs.toList ∧
    TStateAt m'.dmem t a s') ∧
    SameOutside m.dmem m'.dmem (fun q ↦ InRange o (16 * n) q ∨ InRange t tstateBytes q ∨
      InRange (stackBelow m sampleChallengesStack) sampleChallengesStack q) ∧ Saved m m'

/-- `grind`'s bit count: ESI. -/
def grindBits (m : MachineData) : Nat := (reg m .rsi).toNat % 2 ^ 32

/-- `grind`'s precondition: fewer than `64` bits. -/
def GrindPre (a : DecArea) (s : TState) (m : MachineData) : Prop :=
  let t := reg m .rdi
  StackOk m grindStack ∧ RcAt m grindStack ∧ TStateAt m.dmem t a s ∧ TStateOk m t a grindStack ∧
    grindBits m < 64 ∧
    GotAt m grindStack [(t, tstateBytes), (a.words, 8 * a.len), (rcAddr, 192)] ["memcpy"]

/-- `grind`'s postcondition. -/
def GrindPost (a : DecArea) (s : TState) (m m' : MachineData) : Prop :=
  let t := reg m .rdi
  let r := (grind (grindBits m)).run s
  OkAl m' r.isSome ∧ NextAt m'.dmem t a r ∧
    SameOutside m.dmem m'.dmem (fun q ↦ InRange t tstateBytes q ∨
      InRange (stackBelow m grindStack) grindStack q) ∧ Saved m m'

/-- `read_commitment`'s precondition: fewer than `maxRoots` roots read. -/
def ReadCommitmentPre (a : DecArea) (s : TState) (m : MachineData) : Prop :=
  let t := reg m .rdi
  StackOk m readCommitmentStack ∧ RcAt m readCommitmentStack ∧ TStateAt m.dmem t a s ∧
    TStateOk m t a readCommitmentStack ∧ s.roots.size < maxRoots ∧
    GotAt m readCommitmentStack [(t, tstateBytes), (a.words, 8 * a.len),
      (rcAddr, 192)] ["memcpy"]

/-- `read_commitment`'s postcondition. -/
def ReadCommitmentPost (a : DecArea) (s : TState) (m m' : MachineData) : Prop :=
  let t := reg m .rdi
  let r := (readCommitment (reg m .rsi).toNat (reg m .rdx).toNat).run s
  OkAl m' r.isSome ∧ NextAt m'.dmem t a r ∧
    SameOutside m.dmem m'.dmem (fun q ↦ InRange t tstateBytes q ∨
      InRange (stackBelow m readCommitmentStack) readCommitmentStack q) ∧ Saved m m'

end

end

end NativeRustcVmX64
