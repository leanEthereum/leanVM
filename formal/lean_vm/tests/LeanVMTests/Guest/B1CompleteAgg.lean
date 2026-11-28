import LeanVM.Guest.Complete.AggFree
import LeanVM.Guest.Complete.Agg.Loop1
import LeanVM.Guest.Complete.Agg.Loop2
import LeanVM.Guest.Complete.Agg.Loop3
import LeanVM.Guest.Complete.Agg.Loops
import LeanVM.Guest.Complete.MainFree

/-!
# `aggregate_claims`' completeness pieces, pinned

Callees free of witness hints and exact for free complete from their relation; `aggregate_claims`'
callees are such; its loops' blocks hold on their evaluated valuations. Lean's three axioms.
-/

/-- info: 'LeanVM.Guest.Complete.callCompletes_free' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.callCompletes_free

/-- info: 'LeanVM.Guest.Complete.agg_bs_free' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.agg_bs_free

/-- info: 'LeanVM.Guest.Complete.agg_loop0_free' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.agg_loop0_free

/-- info: 'LeanVM.Guest.Complete.Agg.a1_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.a1_block

/-- info: 'LeanVM.Guest.Complete.Agg.a2_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.a2_block

/-- info: 'LeanVM.Guest.Complete.Agg.a3_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.a3_block

/-- info: 'LeanVM.Guest.Complete.Agg.a0_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.a0_block

/-- info: 'LeanVM.Guest.Complete.Agg.agg_loop0_completes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.agg_loop0_completes

/-- info: 'LeanVM.Guest.Complete.Agg.agg_loop1_completes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.agg_loop1_completes

/-- info: 'LeanVM.Guest.Complete.Agg.agg_loop2_completes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.agg_loop2_completes

/-- info: 'LeanVM.Guest.Complete.Agg.agg_loop3_completes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.agg_loop3_completes

/-- info: 'LeanVM.Guest.Complete.Agg.agg_bs_completes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.agg_bs_completes

/-- info: 'LeanVM.Guest.Complete.exponent_tables_completes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.exponent_tables_completes

/-- info: 'LeanVM.Guest.Complete.da_padding_completes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.da_padding_completes

/-- info: 'LeanVM.Guest.Complete.da_levels_completes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.da_levels_completes
