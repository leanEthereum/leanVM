import LeanVM.Guest.CoreMode.Fn.verify_sub.OsCur

/-!
# `open_stacked`'s returned cursor, pinned

`open_stacked` returns its cursor argument times `g^(osWordsLen c)` (`open_stacked_sound_cur`), past the words its
contract reads (`osWords_room`), so `OsCurSpec` holds (`osCurSpec`) and `verify_sub`'s stream reads lie before its end
(`vsStreamQ`), on Lean's three axioms.
-/

/-- info: 'LeanVM.Guest.B1.Whir.open_stacked_sound_cur' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Whir.open_stacked_sound_cur

/-- info: 'LeanVM.Guest.EndExec.osCurSpec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.osCurSpec

/-- info: 'LeanVM.Guest.EndExec.vsStreamQ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.vsStreamQ
