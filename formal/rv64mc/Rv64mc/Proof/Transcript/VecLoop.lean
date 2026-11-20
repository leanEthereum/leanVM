/-
  Rv64mc.Proof.Transcript.VecLoop

  What `next_scalars` and its iterator share: a transcript read through a memory that agrees with the old one on
  the transcript, its `Proof` and everything below the stack (`TranscriptAt.agree`), the result of `next_scalar` in
  a slot, and the stores into objects of a caller's frame.
-/

import Rv64mc.Proof.Transcript.Common

namespace Rv64mc.Proof.Transcript

open RiscvZkvm.Rv64 LeanVM.Parameters Rv64mc.Spec.Transcript

variable {env : Env}

/-- **A transcript through a memory that keeps its words, its `Proof` and everything below the stack.** -/
theorem _root_.Rv64mc.Spec.Transcript.TranscriptAt.agree {m M : MachineState} {a : Word} {t : Model.TState}
    (ht : TranscriptAt env m a t) (ha : a.toNat + Layouts.Transcript.byteSize < 2 ^ 64)
    (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hk : ∀ b : Word, InRange a Layouts.Transcript.byteSize b ∨ InRange (proofAddr m a) Layouts.Proof.byteSize b ∨
      b.toNat < env.stackLimit.toNat → M.getMem b = m.getMem b) :
    TranscriptAt env M a t := by
  have := env.layout
  have hn : env.next M = env.next m := hk _ (Or.inr (Or.inr (by omega)))
  exact ht.keep ha (fun b hb => hk b (Or.inl hb)) (fun b hb => hk b (Or.inr (Or.inl hb)))
    ⟨by rw [hn], fun b hb => hk b (Or.inr (Or.inr (by omega)))⟩

end Rv64mc.Proof.Transcript
