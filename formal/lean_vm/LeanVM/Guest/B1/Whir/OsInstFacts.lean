/-
  LeanVM.Guest.B1.Whir.OsInstFacts

  The 28 configurations' body facts, closed.
-/

module

public import LeanVM.Guest.B1.Whir.OsInstAll
public import LeanVM.Guest.B1.Whir.OsCfgFactsInst0
public import LeanVM.Guest.B1.Whir.OsCfgFactsInst1
public import LeanVM.Guest.B1.Whir.OsCfgFactsInst2
public import LeanVM.Guest.B1.Whir.OsCfgFactsInst3

namespace LeanVM.Guest.B1

open LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

/-- **The 28 configurations' body facts** (`os_facts_M`). -/
theorem osAllBodyFacts : OsAllBodyFacts :=
  ⟨os_facts_0,
    os_facts_1, os_facts_2, os_facts_3, os_facts_4, os_facts_5, os_facts_6, os_facts_7, os_facts_8,
    os_facts_9, os_facts_10, os_facts_11, os_facts_12, os_facts_13, os_facts_14, os_facts_15, os_facts_16,
    os_facts_17, os_facts_18, os_facts_19, os_facts_20, os_facts_21, os_facts_22, os_facts_23, os_facts_24,
    os_facts_25, os_facts_26, os_facts_27⟩

/-- **`open_stacked` is complete, placed, at every candidate**, from group 1's callees and the queries
loops' certificate facts. -/
theorem open_stacked_completeAt' (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) (h1 : OsCalleesAtD fs cert k)
    (hq : OsOqFits fs cert) : VerifySub.CompleteOpenAt fs cert k CapAgrees :=
  open_stacked_completeAt fs cert k osAllBodyFacts h1 hq

end
end LeanVM.Guest.B1
