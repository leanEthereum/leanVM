module

public import NativeVm.Input
public import Native.Keccak.Words

/-!
# The caller's transcript memory layout
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

end NativeVm.Transcript
