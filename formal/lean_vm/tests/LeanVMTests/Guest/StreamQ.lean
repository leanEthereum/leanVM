import LeanVM.Guest.CoreMode.Fn.verify_sub.StreamQ

/-!
# `verify_sub`'s proof stream, pinned

At an honest instance, `verify_sub`'s body is a `VsRun` (`vsRun_honest`), its cursors' positions past the stream are
known through `link_rounds`, `link_row_side` and the Keccak reduction (`vs_c772`, `vs_c1076`, `vs_c2920`; exactly,
`vs_c2920x` from `verify_keccak`'s returned cursor `vk_retCur`, `klRel_cur`), and given
`open_stacked`'s returned cursor (`OsCurSpec`) through the opening (`vs_cEnd`), so every stream read lies before the end
(`vsStreamQ_of`), on Lean's three axioms.
-/

/-- info: 'LeanVM.Guest.EndExec.vsRun_honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.vsRun_honest

/-- info: 'LeanVM.Guest.EndExec.vs_c772' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.vs_c772

/-- info: 'LeanVM.Guest.EndExec.vs_c1076' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.vs_c1076

/-- info: 'LeanVM.Guest.EndExec.vs_c2920' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.vs_c2920

/-- info: 'LeanVM.Guest.EndExec.vs_cEnd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.vs_cEnd

/-- info: 'LeanVM.Guest.EndExec.vsPos_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.vsPos_of

/-- info: 'LeanVM.Guest.EndExec.streamQ_of_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.streamQ_of_pos

/-- info: 'LeanVM.Guest.EndExec.vsStreamQ_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.vsStreamQ_of

/-- info: 'LeanVM.Guest.EndExec.streamFam_okA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.streamFam_okA

/-- info: 'LeanVM.Guest.EndExec.klRel_cur' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.klRel_cur

/-- info: 'LeanVM.Guest.EndExec.vk_retCur' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.vk_retCur

/-- info: 'LeanVM.Guest.EndExec.vs_c2920x' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.vs_c2920x
