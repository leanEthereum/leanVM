import Whir.WHIRSourceRootPolicy
import Whir.WHIRSourceBackfill

namespace Whir.WHIRSourceMerkleSecurity
open FiatShamirGame DuplexModeGame WHIRCallerRegistry WHIRSourceChronology

variable {cap : Nat} {R Coins : Type}

/-- Root announcements are charged separately from public compression calls. The fixed production maximum is derived from all schedules. -/
def rootBudget (Q free : Nat) : Nat :=
  (Q+1) * (free+(Q+1)*(WHIRSourceRootPolicy.productionDepth+1))

def loss (Q free : Nat) : ℚ := PublicMerkleProbability.bound Q (rootBudget Q free)

/-- This is the actual shared-compression event over the source plus its physically executed completion suffix, not a whole-hash random-oracle event. -/
noncomputable def probability [Fintype Coins] (registry : Public) (Q : Nat)
    (sources : Coins → Source cap R) (select : R → Option (RawWHIRKeys.Packet (context registry) Q))
    (counts : ∀ coins, DuplexModeGame.Counts Q
      (WHIRSourceBackfill.instrument (context registry) Q (sources coins) select)) : ℚ :=
  average (fun coins => PublicMerkleProbability.openingProbability
    (WHIRSourceRootPolicy.policy registry Q select (sources coins))
    (PublicCompressionProgram.compile registry.iv
      (WHIRSourceBackfill.instrument (context registry) Q (sources coins) select) Q (counts coins)))

/-- Causal root selection, all old ordinary primitive calls, and fresh-target/collision losses are handled by the actual finite compression experiment. -/
theorem probability_bound [Fintype Coins] [Nonempty Coins]
    (registry : Public) (Q free : Nat) (sources : Coins → Source cap R)
    (select : R → Option (RawWHIRKeys.Packet (context registry) Q))
    (sourceCounts : ∀ coins, Counts Q (sources coins))
    (announcements : ∀ coins, WHIRSourceRootPolicy.FreeAnnouncements free (sources coins))
    (counts : ∀ coins, DuplexModeGame.Counts Q
      (WHIRSourceBackfill.instrument (context registry) Q (sources coins) select)) :
    probability registry Q sources select counts ≤ loss Q free := by
  apply le_trans (average_mono (fun coins =>
    PublicMerkleProbability.real_mode_opening_bound
      (WHIRSourceRootPolicy.policy registry Q select (sources coins)) Q (rootBudget Q free)
      (WHIRSourceRootPolicy.production_cardinality registry Q free select (sources coins)
        (sourceCounts coins) (announcements coins))
      (WHIRSourceRootPolicy.rootsGrow registry Q select (sources coins)) registry.iv
      (WHIRSourceBackfill.instrument (context registry) Q (sources coins) select) (counts coins)))
  exact le_of_eq (average_const _)

end Whir.WHIRSourceMerkleSecurity
