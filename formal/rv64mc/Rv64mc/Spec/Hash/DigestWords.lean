/-
  Rv64mc.Spec.Hash.DigestWords

  The contract of `Digest::words(&self) -> [u64; 4]`: the result's slot (`sret`) in `a0`, at a doubleword
  boundary and the caller's to write (`Owned`), the digest's 32 bytes at `a1` (`DigestAt`), apart from the slot. The
  slot holds `Model.digestWordsRust`'s four little-endian words. It writes the slot (`Out`).
-/

import Rv64mc.Core.Repr
import Rv64mc.Model.Hash

namespace Rv64mc.Spec.Hash.DigestWords

open RiscvZkvm.Rv64 Lprog Lprog.RiscV

def Pre (env : Env) (d : List (BitVec 8)) (regs : Reg → Word) (m : MachineState) : Prop :=
  DigestAt m (regs .x11) d ∧ env.Owned m (regs .x2) (regs .x10) Layouts.Digest.byteSize ∧
    (regs .x10).toNat % 8 = 0 ∧
    ((regs .x10).toNat + Layouts.Digest.byteSize ≤ (regs .x11).toNat ∨
      (regs .x11).toNat + Layouts.Digest.byteSize ≤ (regs .x10).toNat)

def Post (d : List (BitVec 8)) (regs : Reg → Word) (_m : MachineState) (_r' : Reg → Word) (m' : MachineState) :
    Prop :=
  WordsAt m' (regs .x10) (Model.digestWordsRust d)

/-- What it writes besides its stack: the slot. -/
def Out (regs : Reg → Word) (_m : MachineState) (b : Word) : Prop := InRange (regs .x10) Layouts.Digest.byteSize b

/-- **The contract of `Digest::words`**, function `i` of `p` with `need` bytes of stack (no frame; it tail-calls
    `memcpy`), for every digest. -/
def spec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ d, Holds env p i need (Pre env d) (Post d) Out

end Rv64mc.Spec.Hash.DigestWords
