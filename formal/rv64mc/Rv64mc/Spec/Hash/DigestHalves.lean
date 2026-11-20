/-
  Rv64mc.Spec.Hash.DigestHalves

  The contract of `Digest::halves(&self) -> (E, E)`: the result's slot (`sret`) in `a0`, the caller's to write
  (`Owned`), the digest's 32 bytes at `a1` (`DigestAt`), a caller's object. The slot holds `Model.digestHalvesRust`'s two `E`s, the
  second one `E`'s size further (the layout generator has no `(E, E)`; the code stores the four limbs in order). It
  writes the slot (`Out`).
-/

import Rv64mc.Core.Repr
import Rv64mc.Model.Hash

namespace Rv64mc.Spec.Hash.DigestHalves

open RiscvZkvm.Rv64 Lprog Lprog.RiscV

def Pre (env : Env) (d : List (BitVec 8)) (regs : Reg → Word) (m : MachineState) : Prop :=
  DigestAt m (regs .x11) d ∧ env.Owned m (regs .x2) (regs .x11) Layouts.Digest.byteSize ∧
    env.Owned m (regs .x2) (regs .x10) (2 * Layouts.E.byteSize)

def Post (d : List (BitVec 8)) (regs : Reg → Word) (_m : MachineState) (_r' : Reg → Word) (m' : MachineState) :
    Prop :=
  EAt m' (regs .x10) (Model.digestHalvesRust d).1 ∧
    EAt m' (regs .x10 + BitVec.ofNat 64 Layouts.E.byteSize) (Model.digestHalvesRust d).2

/-- What it writes besides its stack: the slot. -/
def Out (regs : Reg → Word) (_m : MachineState) (b : Word) : Prop := InRange (regs .x10) (2 * Layouts.E.byteSize) b

/-- **The contract of `Digest::halves`**, function `i` of `p` with `need` bytes of stack, for every digest. -/
def spec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ d, Holds env p i need (Pre env d) (Post d) Out

end Rv64mc.Spec.Hash.DigestHalves
