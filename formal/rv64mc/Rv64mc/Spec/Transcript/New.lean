/-
  Rv64mc.Spec.Transcript.New

  The contract of `Transcript::new(proof: &Proof, fiat_shamir_iv: Digest, public_input: Digest) -> Transcript`, in
  the image with `checked` always `true` (its one caller's): the result's slot (`sret`) in `a0`, in a caller's
  frame; the proof's reference in `a1`; the two digests, passed by reference, in `a2`, `a3`. The slot becomes the
  mirror's `Model.TState.new`: the sponge after the IV and the public input, nothing read. It writes the slot
  (`SretOut`).
-/

import Rv64mc.Spec.Transcript.Repr
import Rv64mc.Spec.Whir.Basic

namespace Rv64mc.Spec.Transcript.New

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Protocol LeanVM.Protocol.Compile

def Pre (env : Env) (pf : Proof) (iv pi : Digest) (regs : Reg → Word) (m : MachineState) : Prop :=
  ProofAt env m (regs .x11) pf ∧ DigestAt m (regs .x12) (Model.digestBits iv) ∧
    DigestAt m (regs .x13) (Model.digestBits pi) ∧ InFrame (regs .x2) (regs .x10) Layouts.Transcript.byteSize ∧
    Apart (regs .x10) Layouts.Transcript.byteSize (regs .x11) Layouts.Proof.byteSize ∧
    Apart (regs .x10) Layouts.Transcript.byteSize (regs .x12) Layouts.Digest.byteSize ∧
    Apart (regs .x10) Layouts.Transcript.byteSize (regs .x13) Layouts.Digest.byteSize

def Post (env : Env) (pf : Proof) (iv pi : Digest) (regs : Reg → Word) (_m : MachineState) (_r' : Reg → Word)
    (m' : MachineState) : Prop :=
  TranscriptAt env m' (regs .x10) (Model.TState.new pf iv pi true)

/-- **The contract of `Transcript::new`**, function `i` of `p` with `need` bytes of stack (its frame is 32 bytes;
    it calls `Sponge::new`), for every proof and digests. -/
def spec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ pf iv pi, Holds env p i need (Pre env pf iv pi) (Post env pf iv pi) (Whir.SretOut Layouts.Transcript.byteSize)

end Rv64mc.Spec.Transcript.New
