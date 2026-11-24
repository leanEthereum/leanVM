/-
  LeanVM.Guest.B1.Whir.CompleteIface

  The completeness interface of `open_stacked` (B1-b): the run it completes on, the hypothesis on
  that run (openings that agree in the caps).
-/

module

public import LeanVM.Protocol.Verifier.WhirTarget
public import LeanVM.Guest.B1.Whir.Interface
public import LeanVM.Protocol.WithHash
public import LeanVM.Guest.AcceptableChild

/-!
# `open_stacked`'s completeness: the interface

**The run.** An honest child's stacked WHIR opening is an accepting run of `whirOpen μ r target`
(`RunsWith`) from the sponge `⟨capOf S, []⟩` (the state `S` of the caller's sponge, nothing
waiting), the words `xs` and the openings `os`, the stack's root committed with its shape.

**The hypothesis on the run**, without which the statement is false, as `AcceptableChild` states
it for the whole proof: `CapsAgree μ r target S xs os root`, at every query step of the run
(`Limits.queryStepsOf`), two openings giving one node of the tree a digest give it the same
(`Limits.OpeningsAgree`). The guest writes each level's Merkle cap once (write-once memory), so
openings meeting in the cap must agree there; the Spec checks each opening alone against the
root.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The run's hypothesis -/

/-- **The openings agree in the caps**: at every query step of the run of `whirOpen μ r target`
from the sponge state `S` (nothing waiting) on `xs` and `os`, the root committed, the step's
openings agree wherever they meet. -/
def CapsAgree (μ r : ℕ) (target : E) (S : KeccakState) (xs : List E)
    (os : List (List Opening)) (root : Digest) : Prop :=
  ∀ b ∈ Limits.queryStepsOf (whirOpen μ r target) ⟨⟨S, [], none⟩, xs, os, [(root, stackShape μ r)]⟩,
    Limits.OpeningsAgree b.1 b.2

/-! ## Memory layouts -/

end
end LeanVM.Guest.B1.Whir
