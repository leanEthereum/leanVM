/-
  LeanVM.Guest.B1.Stack.Section

  The stack section's statement, proved; the verifier's memory term and public claims as their pure forms.
-/

module

public import LeanVM.Guest.B1.Stack.TermSound
public import LeanVM.Guest.B1.Stack.Certify

/-!
# The stack and its terminal, proved

`stack_section_sound`: `StackSectionSound`, from `certify_stack_sound`, `stack_selectors_holds` and
`check_stack_terminal_sound`. `memoryTermClaim_eq` and `bindPublicInput_eq`: the verifier's
`memoryTermClaim` returns `memoryTermPure`'s claim, and `bindPublicInput` samples the public challenge
`rm` and returns `publicClaimsPure` at `rm` and the public input's two limbs on their line
(`publicLimb`), the forms `stackedClaims` takes.
-/

namespace LeanVM.Guest.B1.Stack

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash

@[expose] public section

/-- **The stack and its terminal in the circuit.** -/
theorem stack_section_sound : StackSectionSound := fun hκ11 hκ L ↦
  ⟨certify_stack_sound hκ11 hκ L, stack_selectors_holds hκ (by omega) L,
    check_stack_terminal_sound (by omega) hκ L⟩

/-- **`memoryTermClaim` returns `memoryTermPure`'s claim.** -/
theorem memoryTermClaim_eq {layout : Layout} {link : LinkEnd} {c : StackClaim}
    (h : memoryTermPure layout link = some c) : memoryTermClaim layout link = .ret c := by
  unfold memoryTermPure at h
  unfold memoryTermClaim
  split at h
  · rename_i p0 p1 h0 h1
    simp only [Option.some.injEq] at h
    subst h
    simp only [h0, h1]
    rfl
  · cases h

/-- The public input's limb `limb` on the line through its two halves, at `rm`. -/
def publicLimb (publicInput : Digest) (limb : Fin 2) (rm : E) : E :=
  multilinearEval [ofK ((digestHalves publicInput).1.limb limb), ofK ((digestHalves publicInput).2.limb limb)] [rm]

/-- **`bindPublicInput` samples `rm` and returns `publicClaimsPure` at it.** -/
theorem bindPublicInput_eq {layout : Layout} (publicInput : Digest) {p : Placement}
    (hp : layout.placements.getD memory0 none = some p) :
    bindPublicInput layout publicInput = .sample fun rm ↦
      .ret (publicClaimsPure layout rm (publicLimb publicInput 0 rm) (publicLimb publicInput 1 rm)) := by
  unfold bindPublicInput publicClaimsPure
  simp only [hp]
  rfl

end
end LeanVM.Guest.B1.Stack
