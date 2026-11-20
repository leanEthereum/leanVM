/-
  Rv64mc.Spec.Transcript.SpongeNew

  The contract of `Sponge::new(fiat_shamir_iv: Digest, public_input: Digest) -> Sponge`: the result's slot
  (`sret`) in `a0`, in a caller's frame; the two digests, passed by reference, in `a1`, `a2`, apart from the slot
  and safe from the call (`Safe`). The slot becomes the mirror's `Model.SpongeRust.new`: the IV's and the public
  input's words in lanes `0..8`, permuted. It writes the slot (`SretOut`).
-/

import Rv64mc.Spec.Transcript.Repr
import Rv64mc.Spec.Whir.Basic

namespace Rv64mc.Spec.Transcript.SpongeNew

open RiscvZkvm.Rv64 Lprog Lprog.RiscV

def Pre (env : Env) (iv pi : List (BitVec 8)) (regs : Reg → Word) (m : MachineState) : Prop :=
  DigestAt m (regs .x11) iv ∧ DigestAt m (regs .x12) pi ∧
    InFrame (regs .x2) (regs .x10) Layouts.Sponge.byteSize ∧
    Apart (regs .x10) Layouts.Sponge.byteSize (regs .x11) Layouts.Digest.byteSize ∧
    Apart (regs .x10) Layouts.Sponge.byteSize (regs .x12) Layouts.Digest.byteSize ∧
    Safe env m (regs .x2) (regs .x11) Layouts.Digest.byteSize ∧
    Safe env m (regs .x2) (regs .x12) Layouts.Digest.byteSize

def Post (iv pi : List (BitVec 8)) (regs : Reg → Word) (_m : MachineState) (_r' : Reg → Word)
    (m' : MachineState) : Prop :=
  SpongeAt m' (regs .x10) (Model.SpongeRust.new iv pi)

/-- **The contract of `Sponge::new`**, function `i` of `p` with `need` bytes of stack (its frame is 224 bytes; it
    calls `Digest::words`, `memset`, `keccak_f` and `memcpy`), for every pair of digests. -/
def spec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ iv pi, Holds env p i need (Pre env iv pi) (Post iv pi) (Whir.SretOut Layouts.Sponge.byteSize)

end Rv64mc.Spec.Transcript.SpongeNew
