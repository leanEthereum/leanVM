module

public import NativeVm.Input
public import Native.Keccak
public import Native.Frame

/-!
# The transcript's memory

The transcript (`LeanVM.Protocol.Compile.run`'s state, `VerifierProgramState`) lives in three
places: the sponge in the context, after `Keccak.hash`'s scratch area; the cursors and the roots in
the first `workWords` words of the working area; the stream and the openings in the decoded proof
(`Decoded`), which nothing writes.

| word of the context | holds |
|---|---|
| `scratchW ..` | `Keccak.hash`'s scratch area (`Keccak.scratchWords` words), its lanes first |
| `laneW .. + 25` | the sponge's state, lane `i` at `laneW + i` |
| `rateW .. + 16` | the waiting scalars as the rate lanes they enter (`pendingLanes`), zeros after them |
| `countW` | the number of waiting scalars |
| `groundW`, `+ 1`, `+ 2` | `1` and the ground challenge's two limbs, or `0` |
| `climbW .. + 8` | a Merkle climb's hash input |
| `qRootW .. + 6` | the root a query opens: its digest, height and width |

| word of the working area | holds |
|---|---|
| `workCursor` | the next stream element's index `c` |
| `workPhase`, `workPhasePtr` | the next phase's index `p`, and the address of its words |
| `workPhaseCount` | the number of phases |
| `workRootCount` | the number of roots read |
| `workRoots + rootStride · j ..` | root `j`: its digest's four words, its height, its width |

`SimState env st s` says the machine state `s` holds `st`: `rdi` at the context, the decoded proof
`env.proof` in place, and the words above holding the sponge, the cursors and the roots.
-/

@[expose] public section

namespace NativeVm.Transcript

open Native LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.KeccakHash
open LeanVM.Semantics

/-! ## Words -/

/-- The address of word `k` of the area at `b`. -/
def wd (b : UInt64) (k : Nat) : UInt64 := b + (8 * k).toUInt64

/-- The area of `n` words at `b` does not wrap around the address space. -/
def Fits (b : UInt64) (n : Nat) : Prop := b.toNat + 8 * n ≤ 2 ^ 64

/-- The areas of `n` words at `a` and `m` words at `b` do not overlap. -/
def Disj (a : UInt64) (n : Nat) (b : UInt64) (m : Nat) : Prop :=
  a.toNat + 8 * n ≤ b.toNat ∨ b.toNat + 8 * m ≤ a.toNat

/-! ## The context's words -/

/-- The wire bytes' count `L`. -/
def ctxWireLen : Nat := 1
/-- The bytecode's address. -/
def ctxBytecode : Nat := 2
/-- The bytecode's word count. -/
def ctxBytecodeLen : Nat := 3
/-- The public input's digest, four words. -/
def ctxPublic : Nat := 4
/-- The decoded proof's address. -/
def ctxDecoded : Nat := 8
/-- The working area's address. -/
def ctxWork : Nat := 10
/-- `Keccak.hash`'s scratch area. -/
def scratchW : Nat := 32
/-- The sponge's 25 lanes. -/
def laneW : Nat := scratchW + Keccak.scratchWords
/-- The rate lanes of the waiting scalars. -/
def rateW : Nat := laneW + 25
/-- The number of waiting scalars. -/
def countW : Nat := rateW + 16
/-- The ground challenge: a flag, then its two limbs. -/
def groundW : Nat := countW + 1
/-- A Merkle climb's input, two digests. -/
def climbW : Nat := groundW + 3
/-- The root a query opens: digest, height, width. -/
def qRootW : Nat := climbW + 8
/-- The context's words the transcript needs. -/
def ctxEnd : Nat := qRootW + 6

/-! ## The working area's words -/

/-- The next stream element's index. -/
def workCursor : Nat := 0
/-- The next phase's index. -/
def workPhase : Nat := 1
/-- The next phase's address. -/
def workPhasePtr : Nat := 2
/-- The number of phases. -/
def workPhaseCount : Nat := 3
/-- The number of roots read. -/
def workRootCount : Nat := 4
/-- The roots. -/
def workRoots : Nat := 5
/-- The words of a root's entry: digest, height, width, two unused. -/
def rootStride : Nat := 8
/-- The most roots the table holds: one per phase the decoder accepts. -/
def maxRoots : Nat := wireMaxPhases
/-- The working area's words the transcript needs. -/
def workWords : Nat := workRoots + rootStride * maxRoots

/-! ## The state -/

/-- Where the transcript is: the context, the decoded proof (of a wire of `L` bytes), the working
area, and the proof the decoded area holds. -/
structure Env where
  ctx : UInt64
  dec : UInt64
  work : UInt64
  L : Nat
  proof : Proof

/-- The areas: each fits, they are pairwise disjoint, the context's and the working area's words
exist, and the context points to the others. -/
structure Layout (env : Env) (mem : UInt64 → Option UInt64) : Prop where
  fitCtx : Fits env.ctx ctxEnd
  fitDec : Fits env.dec (decodedWords env.L)
  fitWork : Fits env.work workWords
  disjCD : Disj env.ctx ctxEnd env.dec (decodedWords env.L)
  disjCW : Disj env.ctx ctxEnd env.work workWords
  disjDW : Disj env.dec (decodedWords env.L) env.work workWords
  ctxSome : ∀ k < ctxEnd, (mem (wd env.ctx k)).isSome
  workSome : ∀ k < workWords, (mem (wd env.work k)).isSome
  decPtr : mem (wd env.ctx ctxDecoded) = some env.dec
  workPtr : mem (wd env.ctx ctxWork) = some env.work

/-- The ground challenge in the context's words: the flag `0`, or `1` and its limbs. -/
def GroundAt (mem : UInt64 → Option UInt64) (ctx : UInt64) : Option E → Prop
  | none => mem (wd ctx groundW) = some 0
  | some c => mem (wd ctx groundW) = some 1 ∧ mem (wd ctx (groundW + 1)) = some (c.limb 0).lane ∧
      mem (wd ctx (groundW + 2)) = some (c.limb 1).lane

/-- The sponge `sp` in the context's words. -/
structure SpongeAt (mem : UInt64 → Option UInt64) (ctx : UInt64) (sp : Sponge) : Prop where
  lanes : ∀ i < 25, mem (wd ctx (laneW + i)) = some (Keccak.lane sp.state i)
  pendingLen : sp.pending.length ≤ rateScalars
  count : mem (wd ctx countW) = some sp.pending.length.toUInt64
  rate : ∀ i < 16, mem (wd ctx (rateW + i)) = some ((pendingLanes sp.pending).getD i 0)
  ground : GroundAt mem ctx sp.ground

/-- Root `j`'s entry holds the digest `d` of a tree of `2^h` leaves of `w` words. -/
def RootAt (mem : UInt64 → Option UInt64) (work : UInt64) (j : Nat) (r : Digest × Nat × Nat) :
    Prop :=
  (∀ k (hk : k < 4), mem (wd work (workRoots + rootStride * j + k)) = some r.1[k]) ∧
  r.2.1 < 2 ^ 64 ∧ r.2.2 < 2 ^ 64 ∧
  mem (wd work (workRoots + rootStride * j + 4)) = some r.2.1.toUInt64 ∧
  mem (wd work (workRoots + rootStride * j + 5)) = some r.2.2.toUInt64

/-- **The machine state `s` holds the transcript's state `st`.** -/
structure SimState (env : Env) (st : VerifierProgramState) (s : QState) : Prop where
  rdi : s.reg .rdi = env.ctx
  layout : Layout env s.mem
  decoded : Decoded s.mem env.dec env.L env.proof
  sponge : SpongeAt s.mem env.ctx st.sponge
  cursor : ∃ c ≤ env.proof.stream.length, s.mem (wd env.work workCursor) = some c.toUInt64 ∧
    st.stream = env.proof.stream.drop c
  phase : ∃ p ≤ env.proof.openings.length, s.mem (wd env.work workPhase) = some p.toUInt64 ∧
    s.mem (wd env.work workPhasePtr) = some (wd env.dec (phaseBase env.L p)) ∧
    st.openings = env.proof.openings.drop p
  phaseCount : s.mem (wd env.work workPhaseCount) = some env.proof.openings.length.toUInt64
  rootsLen : st.roots.length ≤ maxRoots
  rootCount : s.mem (wd env.work workRootCount) = some st.roots.length.toUInt64
  roots : ∀ j (hj : j < st.roots.length), RootAt s.mem env.work j st.roots[j]

/-! ## What a gadget writes -/

/-- The words the transcript's gadgets write: the context's from the scratch area to `ctxEnd`, and
the working area's first `workWords`. -/
def Foot (env : Env) (a : UInt64) : Prop :=
  (∃ k, scratchW ≤ k ∧ k < ctxEnd ∧ a = wd env.ctx k) ∨ ∃ k < workWords, a = wd env.work k

/-- The registers the transcript's gadgets other than `query` may write. -/
def clobbers : List Reg64 := [.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r9, .r10, .r11]

/-- What a gadget keeps from `s` to `s'`: `rdi`, the registers outside `rs`, and every word outside
`foot`. -/
structure Keeps (rs : List Reg64) (foot : UInt64 → Prop) (s s' : QState) : Prop where
  rdi : s'.reg .rdi = s.reg .rdi
  regs : RegsFrame rs s s'
  mem : ∀ a, ¬ foot a → s'.mem a = s.mem a

end NativeVm.Transcript
