import LeanVM.Guest.B1.VsC.VsOrcPin
import LeanVM.Guest.B1.VsC.VsOrcAlW
import LeanVM.Guest.B1.VsC.VsHonEnds
import LeanVM.Guest.B1.VsC.VsOrcPhOpenE
import LeanVM.Guest.B1.VsC.CalleesU

/-!
# `verify_sub`'s phases at the pinned callee ends

`VsOrcSpec.lean`: the non-leaf callees' calls (`CsCall`, `SpCall`, `LrCall`, `LrsCall`) at the pinned ends
`x.ec 4`, `6`, `7`, `9`, the cursors `Carry6` and `Carry11` carry. `VsOrcPh46.lean`, `VsOrcPh711.lean`: `Ph4to6S`,
`Ph7to11S` on them. `VsOrcPin.lean`: the composition from `Ph12toEndP`; `Carry6`, `Carry11` carry `StkAt`, so `verify_sub`'s
windows follow from `VsHonEx` alone (`VsOrcAlW.lean` at `alW`). On Lean's three axioms.
-/

/-- info: 'LeanVM.Guest.B1.VsC.vsA_ptr26' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsA_ptr26

/-- info: 'LeanVM.Guest.B1.VsC.ph4to6S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.ph4to6S





/-- info: 'LeanVM.Guest.B1.VsC.ph7Ok_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.ph7Ok_at

/-- info: 'LeanVM.Guest.B1.VsC.ph7Ok_in' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.ph7Ok_in

/-- info: 'LeanVM.Guest.B1.VsC.ph9Ok_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.ph9Ok_at

/-- info: 'LeanVM.Guest.B1.VsC.ph9Ok_in' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.ph9Ok_in

/-- info: 'LeanVM.Guest.B1.VsC.ph7to11S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.ph7to11S


/-- info: 'LeanVM.Guest.B1.VsC.vsOrcWFromCallees_of_P' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsOrcWFromCallees_of_P

/-- info: 'LeanVM.Guest.B1.VsC.vsOrcWFromCallees_of_endP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsOrcWFromCallees_of_endP

/-- info: 'LeanVM.Guest.B1.VsC.VsCtx.StkAt.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.VsCtx.StkAt.mono

/-- info: 'LeanVM.Guest.B1.VsC.vsOrcW_of_honexA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsOrcW_of_honexA

/-- info: 'LeanVM.Guest.B1.VsC.vsWindows_of_honexA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsWindows_of_honexA

/-- info: 'LeanVM.Guest.B1.VsC.vsOrcW_of_honex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsOrcW_of_honex

/-- info: 'LeanVM.Guest.B1.VsC.vsWindows_of_honex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsWindows_of_honex

/-- info: 'LeanVM.Guest.B1.VsC.cstE_b2c' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.cstE_b2c

/-- info: 'LeanVM.Guest.B1.VsC.VsCtx.hend_of_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.VsCtx.hend_of_steps

/-- info: 'LeanVM.Guest.B1.VsC.phOpenOk_inE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.phOpenOk_inE

/-- info: 'LeanVM.Guest.B1.VsC.vsCalleesEndU_b2c' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsCalleesEndU_b2c
