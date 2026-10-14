import Whir.WHIRPhysicalDriver
import Whir.WHIRObservableSource

namespace Whir.WHIRNativeEvent
open DuplexModeGame WHIRPhysicalDriver WHIRPhysicalDriver.Unanchored

abbrev Output (registry : ProductionRegistry) (Q cap : Nat) :=
  WHIRPublicBackfill.Completed (WHIRCallerRegistry.context registry.publicRegistry) Q
    (WHIRSourceChronology.Result cap (Option (Accepted registry.context Q cap)))

/-- The native event sees only the completed public result and reconstructs its first-frozen candidate list from public records. It never receives a source program, private coins, a simulator seed, or a total compression oracle. -/
def Failure (registry : ProductionRegistry) (Q : Nat) {cap : Nat} (output : Output registry Q cap) : Prop :=
  ∃ observed, WHIRObservableSource.observe registry.publicRegistry Q select output = some observed ∧
    nativeWrong observed.state output.result.value

noncomputable def distinguisher (registry : ProductionRegistry) (Q cap : Nat) :
    View (Output registry Q cap) → Bool := by
  classical
  exact fun view => decide (Failure registry Q view.result)

/-- Rejection is not a false acceptance, even if reconstruction encounters malformed public records. -/
theorem rejected (registry : ProductionRegistry) (Q cap : Nat) (output : Output registry Q cap)
    (none : output.result.value = Option.none) : ¬ Failure registry Q output := by
  rintro ⟨observed,_,wrong⟩
  rw [none] at wrong
  exact wrong

end Whir.WHIRNativeEvent
