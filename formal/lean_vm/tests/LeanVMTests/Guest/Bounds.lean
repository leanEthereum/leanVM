import LeanVM.Guest.Complete.MainCalleesHonest
import LeanVM.Guest.Complete.Left

/-!
# `main`'s callees' bounded fields, pinned

The frames below `2^16` (`fs_lt16`), `da_verify`'s end within `2^38` of its cursor (`dv_callAtA`),
`aggregate_claims`' window from what is left (`aggWinHyp_of_left`), and `main`'s callees at the honest
coverage table from the children's claim lists (`mainCalleesOpenA_of_kids`), closed by claims'
`kidsListsOpen` (`mainCalleesOpenA`), on Lean's three axioms.
-/

/-- info: 'LeanVM.Guest.Complete.fs_lt16' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.fs_lt16

/-- info: 'LeanVM.Guest.Complete.dv_callAtA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.dv_callAtA

/-- info: 'LeanVM.Guest.Complete.Agg.aggWinHyp_of_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.aggWinHyp_of_left

/-- info: 'LeanVM.Guest.Complete.mainCalleesOpenA_of_kids' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.mainCalleesOpenA_of_kids

/-- info: 'LeanVM.Guest.Complete.mainCalleesOpenA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.mainCalleesOpenA
