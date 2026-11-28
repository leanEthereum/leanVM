/-
  LeanVM.Guest.B1.Ring.Interface

  B1 of the ring switch's target: the meaning of `ring_switch_target`, and the statement that its
  core IR computes it.
-/

module

public import LeanVM.Guest.B1.Common.Basic
public import LeanVM.Guest.CoreData

/-!
# The ring switch: the interface

The ring switch (`ringSwitch`, `ring_switch.rs`) turns the 64 claims on the merged bit slices
into one claim on the stack, whose target is `ringTarget s f g` (`ringMerge`), over the map's
sixteen challenges, `f` then `g`.

| function | meaning |
| --- | --- |
| `ring_psi` (inline) | `ringPsi v g`: the inner stage `Σ_b g_b v^(2^b)` |
| `ring_switch_target` | `ringTarget s f g`, eight rows a loop iteration, Horner in `w_p = 1/z_p` |

The function writes scratch buffers (`HeapBuf`) whose words its relation reads back, so its
converse holds only over a memory holding the honest scratch; it is stated with `verify_sub`'s
completeness.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## `ring_switch_target` -/

/-- **`ring_switch_target(slices, map_challenges)`**: the 64 slices `s` at
`slices` and the sixteen map challenges `f ++ g` at `map_challenges`; it returns
`ringTarget s f g`. -/
def MeaningRingTarget (rd : Reader) : List E → List E → Prop
  | [sl, mc], rets =>
      ∃ s ch : List E, s.length = kBits ∧ ch.length = 2 * ringMapWidth ∧ ReadsAt rd sl s ∧
        ReadsAt rd mc ch ∧ rets = [ringTarget s (ch.take ringMapWidth) (ch.drop ringMapWidth)]
  | _, _ => False

/-- `ring_switch_target`'s core IR computes its meaning. -/
def ring_switch_target_Spec : Prop :=
  ∀ (rd : Reader) (args rets : List E),
    coreProgram.Rel rd "ring_switch_target" args rets → MeaningRingTarget rd args rets

end
end LeanVM.Guest.B1.VerifySub
