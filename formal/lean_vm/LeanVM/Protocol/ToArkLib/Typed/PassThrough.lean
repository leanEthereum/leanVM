/-
  LeanVM.Protocol.ToArkLib.Typed.PassThrough

  The typed component with no round: the verdict is a function of the statement, the oracles and
  the witness are handed on. Both halves. Candidate for ArkLib.
-/

module

public import LeanVM.Protocol.ToArkLib.Typed.Component

/-!
# The pass-through component

`Typed.passThrough O f` runs on the empty slot `doneSlot`: the verdict is `f` of the statement,
always accepted. It relabels a statement: the empty tail of a sequence of rounds carries its
statement across an equality of stages.

Completeness (`passThroughComplete`): `f` carries the input relation into the output relation.
Knowledge soundness (`passThroughSecurity`, at no error, the extractor empty): the output relation
at `f` of a statement is the input relation at it. A tree with no move has its input state as its
terminal state, so the typed framework asks the two relations to agree there.
-/

namespace LeanVM.Protocol.Typed

open Interaction Interaction.Oracle Interaction.Oracle.Security

@[expose] public section

/-- The empty slot. -/
abbrev doneSlot : Slot := ⟨.done, ⟨⟩, ⟨⟩, PUnit.unit⟩

/-- No error: the empty slot has no challenge. -/
abbrev doneErrors : Errors doneSlot.tree doneSlot.roles := PUnit.unit

variable {ι : Type} (O : ι → Type) {S T W : Type} (f : S → T)

/-- The pass-through component. -/
def passThrough : Def O S W T W doneSlot where
  verdict s _ := some (f s)
  prover so w := ((f so.1, so.2), w)

variable {O f} {relIn : Set ((S × ∀ i, O i) × W)} {relOut : Set ((T × ∀ i, O i) × W)}

/-- **Completeness**, whenever `f` carries the input relation into the output relation. -/
theorem passThroughComplete (h : ∀ s o w, ((s, o), w) ∈ relIn → ((f s, o), w) ∈ relOut) :
    Complete (passThrough O f) relIn relOut := by
  rintro s o w hin ⟨⟩ a rfl
  exact ⟨rfl, rfl, h s o w hin⟩

/-- **Knowledge soundness at no error**, whenever the output relation at `f` of a statement is
the input relation at it. -/
def passThroughSecurity (h : ∀ s o w, ((f s, o), w) ∈ relOut ↔ ((s, o), w) ∈ relIn) :
    Security (passThrough O f) relIn relOut doneErrors where
  extractor _ _ := PUnit.unit
  prover_preserving _ _ := trivial
  local_bound _ _ := trivial
  terminal s o :=
    { witnessEquiv := fun _ ↦ Equiv.refl W
      knowledge_iff := fun _ w ↦
        ⟨fun hw ↦ ⟨f s, rfl, (h s o w).mpr hw⟩, fun ⟨_, ht, hw⟩ ↦ by
          cases ht
          exact (h s o w).mp hw⟩ }

/-- Knowledge soundness at no error for the trivial witness, from the equivalence of the two
relations at `f`. -/
def passThroughSecurityOfIff {rIn : Set ((S × ∀ i, O i) × Unit)}
    {rOut : Set ((T × ∀ i, O i) × Unit)}
    (hf : ∀ s o, ((f s, o), ()) ∈ rOut ↔ ((s, o), ()) ∈ rIn) :
    Security (passThrough O f) rIn rOut doneErrors :=
  passThroughSecurity fun s o w ↦ by cases w; exact hf s o

end
end LeanVM.Protocol.Typed
