/-
  Rv64mc.Spec.Hash.Digest

  The contract of `Digest::from_halves(low, high)`: the two `E`s' limbs in `a1`..`a4`, the digest returned through
  `sret` (`a0`), in memory its caller may write (`Owned`). It leaves there `Model.digestFromHalvesRust`'s 32 bytes,
  writing only the doublewords that hold them (`DwordsOf`) and keeping every other byte (`ByteFrame`). A leaf
  without a frame.
-/

import Rv64mc.Spec.Runtime.Mem
import Rv64mc.Model.Hash

namespace Rv64mc.Spec.Hash.DigestFromHalves

open RiscvZkvm.Rv64 Lprog Lprog.RiscV

def Pre (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  env.Owned m (regs .x2) (alignToDword (regs .x10)) (Layouts.Digest.byteSize + (regs .x10).toNat % 8)

def Post (regs : Reg → Word) (m : MachineState) (_r' : Reg → Word) (m' : MachineState) : Prop :=
  BytesAt m' (regs .x10) (Model.digestFromHalvesRust (regs .x11, regs .x12) (regs .x13, regs .x14)) ∧
    ByteFrame m m' (regs .x10) Layouts.Digest.byteSize

/-- What it writes besides its stack: the doublewords of the digest. -/
def Out (regs : Reg → Word) (_m : MachineState) : Word → Prop :=
  Spec.Runtime.DwordsOf (regs .x10) Layouts.Digest.byteSize

/-- **The contract of `Digest::from_halves`**, function `i` of `p` with `need` bytes of stack. -/
def spec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop := Holds env p i need (Pre env) Post Out

end Rv64mc.Spec.Hash.DigestFromHalves
