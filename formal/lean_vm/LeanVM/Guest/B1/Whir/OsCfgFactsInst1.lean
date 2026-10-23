/-
  LeanVM.Guest.B1.Whir.OsCfgFactsInst1

  `OsBodyFacts` of `open_stacked__L7` to `open_stacked__L13`, by evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.OsCfgFactsB

namespace LeanVM.Guest.B1

@[expose] public section

set_option maxRecDepth 100000 in
theorem os_facts_7 : OsBodyFacts osCfg7 := os_facts_of (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_facts_8 : OsBodyFacts osCfg8 := os_facts_of (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_facts_9 : OsBodyFacts osCfg9 := os_facts_of (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_facts_10 : OsBodyFacts osCfg10 := os_facts_of (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_facts_11 : OsBodyFacts osCfg11 := os_facts_of (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_facts_12 : OsBodyFacts osCfg12 := os_facts_of (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_facts_13 : OsBodyFacts osCfg13 := os_facts_of (by decide +kernel)

end
end LeanVM.Guest.B1
