import Whir.PublicCompressionCouplingMixed

/-! Construction observations in the actual ideal runner name and return their
literal bounded raw key. The simulator may change primitive replies, but cannot
replace or resample these construction answers. -/
set_option autoImplicit false
namespace Whir.PCSBCSIdealConstructionAnswers
open FiatShamirGame DuplexFraming DuplexModeGame

/-- Every observed construction answer comes from the same independent RO,
including arbitrary primitive calls, cached simulator replies and early abort. -/
theorem construction_observations {Q : Nat} {Seed State R : Type}
    (sim : Simulator Q Seed State) (ro : RawKey Q → Digest32) (iv : Digest32)
    (state : State) (program : Program R) (remaining : Nat) (limit : remaining ≤ Q)
    (counted : Counts remaining program) :
    ∀ coordinate valid answer,
      (⟨.construction coordinate valid,answer⟩ : Observation) ∈
        (runIdeal sim ro iv state program remaining limit counted).view.observations →
      ∃ bound : pathCost coordinate ≤ Q,
        answer = ro (constructionKey Q iv coordinate bound) := by
  induction program generalizing state remaining with
  | done value => simp [runIdeal]
  | ask query next ih =>
    cases query with
    | primitive purpose input =>
      intro coordinate valid answer member
      simp only [runIdeal,prepend,List.mem_cons] at member
      rcases member with impossible | later
      · cases impossible
      · exact ih (runRO ro (sim.answer state input)).1.2
          (runRO ro (sim.answer state input)).1.1 (remaining-1) (by omega)
          (counted.2 _) coordinate valid answer later
    | construction coordinate valid =>
      intro other otherValid answer member
      simp only [runIdeal,prepend,List.mem_cons] at member
      rcases member with first | later
      · cases first
        exact ⟨counted.1.trans limit,rfl⟩
      · exact ih (ro (constructionKey Q iv coordinate (counted.1.trans limit)))
          state (remaining-pathCost coordinate) (by omega) (counted.2 _)
          other otherValid answer later

#print axioms construction_observations
end Whir.PCSBCSIdealConstructionAnswers
