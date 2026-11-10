module

public import Qrom.QromSearch
public import Qrom.OvSearch
public import Qrom.HidingMain
public import Qrom.Deferral
public import Qrom.Presample
public import Qrom.Verify
public import Qrom.Assembly
public import Qrom.Sphincs.Numeric

/-! # Generic results in the quantum random-oracle model

`Qrom.qrom_search_le`: a program making at most `t` calls to the quantum random oracle and
outputting at most `k` inputs outputs one whose value is good with probability at most
`λ (√6 t + 2 k)²`, where every input has a fraction at most `λ` of good values.
`Qrom.OvGame.ov_search_le` is the same bound for games whose hash answers some inputs from fixed
data, depending on a classical side state, beside classical side ports such as a signing oracle,
with `t` the number of calls in all. `Qrom.Sphincs.winProb_le` bounds a leanSPHINCS forgery by an
adversary making at most `n` calls in all, from those and from the classical classification of a
winning forgery; `Qrom.Sphincs.winProb_le_h26` makes it numeric for the parameters of
`FORS.h26_layered`, with the cover probability at most `2^-98` (`Qrom.Sphincs.lamB_h26`). The build fails if their axiom footprints grow beyond Lean's
three standard axioms. -/

/-- info: 'Qrom.qrom_search_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Qrom.qrom_search_le

/-- info: 'Qrom.OvGame.ov_search_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Qrom.OvGame.ov_search_le

/-- info: 'Qrom.OvGame.hiding_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Qrom.OvGame.hiding_le

/-- info: 'Qrom.OvGame.hiding_side_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Qrom.OvGame.hiding_side_le

/-- info: 'Qrom.OvGame.sum_sideW_protHit_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Qrom.OvGame.sum_sideW_protHit_le

/-- info: 'Qrom.OvGame.deferral_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Qrom.OvGame.deferral_le

/-- info: 'Qrom.sum_eq_sum_override' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Qrom.sum_eq_sum_override

/-- info: 'Qrom.OvGame.sideW_withVerifier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Qrom.OvGame.sideW_withVerifier

/-- info: 'Qrom.OvGame.search_withVerifier_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Qrom.OvGame.search_withVerifier_le

/-- info: 'Qrom.Sphincs.winProb_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Qrom.Sphincs.winProb_le

/-- info: 'Qrom.Sphincs.winProb_le_h26' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Qrom.Sphincs.winProb_le_h26
