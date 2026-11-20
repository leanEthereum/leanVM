/-
  Rv64mc.Spec.Hash.Keccak

  The contracts of `xor_block` and `keccak_hash` (`hash.rs`), on bytes as `Model.Hash` holds them.

  * `xor_block(state, block)`: the state's `25` lanes at `a0` (`WordsAt`, in memory its caller may write), the
    block's `136` bytes at `a1` (`BytesAt`), no byte of the block in a doubleword of the state (the code stores a
    lane between the block's byte loads). It leaves `Model.xorBlockRust`'s lanes, writing only the state.
  * `keccak_hash(data) -> Digest`: the digest returned through `sret` (`a0`), the data as a pointer and a length
    (`a1`, `a2`) in memory its caller owns. It leaves `Model.keccakHashRust`'s 32 bytes there, writing only the
    doublewords that hold them and keeping every other byte.
-/

import Rv64mc.Spec.Runtime.Mem
import Rv64mc.Model.Hash

namespace Rv64mc.Spec.Hash

open RiscvZkvm.Rv64 Lprog Lprog.RiscV

/-- The state's size in bytes: `25` lanes. -/
abbrev stateBytes : Nat := 8 * 25

/-- The sponge's rate in bytes. -/
abbrev rate : Nat := 136

namespace XorBlock

def Pre (env : Env) (ws : List Word) (bs : List (BitVec 8)) (regs : Reg → Word) (m : MachineState) : Prop :=
  ws.length = 25 ∧ WordsAt m (regs .x10) ws ∧ env.Owned m (regs .x2) (regs .x10) stateBytes ∧
    bs.length = rate ∧ BytesAt m (regs .x11) bs ∧
    ∀ b, InRange (regs .x11) rate b → ∀ k < 25, alignToDword b ≠ regs .x10 + BitVec.ofNat 64 (8 * k)

def Post (ws : List Word) (bs : List (BitVec 8)) (regs : Reg → Word) (_m : MachineState) (_r' : Reg → Word)
    (m' : MachineState) : Prop :=
  WordsAt m' (regs .x10) (Model.xorBlockRust ws bs)

/-- What it writes besides its stack: the state. -/
def Out (regs : Reg → Word) (_m : MachineState) (b : Word) : Prop := InRange (regs .x10) stateBytes b

/-- **The contract of `xor_block`**, function `i` of `p` with `need` bytes of stack, for every state and block. -/
def spec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ ws bs, Holds env p i need (Pre env ws bs) (Post ws bs) Out

end XorBlock

/-- The digest's slot at `a`: the doublewords that hold its 32 bytes are the caller's. -/
def DigestSlot (env : Env) (m : MachineState) (top a : Word) : Prop :=
  env.Owned m top (alignToDword a) (Layouts.Digest.byteSize + a.toNat % 8)

/-- What a function returning a digest at `a` writes besides its stack and allocations: the slot's doublewords. -/
def DigestOut (a : Word) : Word → Prop := Spec.Runtime.DwordsOf a Layouts.Digest.byteSize

/-- The digest `d` at `a`, every other byte as in `m`. -/
def DigestPost (m : MachineState) (a : Word) (m' : MachineState) (d : List (BitVec 8)) : Prop :=
  BytesAt m' a d ∧ ByteFrame m m' a Layouts.Digest.byteSize

namespace KeccakHash

def Pre (env : Env) (bs : List (BitVec 8)) (regs : Reg → Word) (m : MachineState) : Prop :=
  DigestSlot env m (regs .x2) (regs .x10) ∧ SliceArgs BytesAt m (regs .x11) (regs .x12) bs ∧
    env.Owned m (regs .x2) (regs .x11) bs.length

def Post (bs : List (BitVec 8)) (regs : Reg → Word) (m : MachineState) (_r' : Reg → Word) (m' : MachineState) :
    Prop :=
  DigestPost m (regs .x10) m' (Model.keccakHashRust bs)

/-- **The contract of `keccak_hash`**, function `i` of `p` with `need` bytes of stack, for every byte string. -/
def spec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ bs, Holds env p i need (Pre env bs) (Post bs) fun regs _ => DigestOut (regs .x10)

end KeccakHash

end Rv64mc.Spec.Hash
