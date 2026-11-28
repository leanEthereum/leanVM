import LeanVM.Guest.CoreMode.Fn.verify_keccak.SoundA
import LeanVM.Guest.CoreMode.Fn.keccak_layer.SoundA

/-!
# `verify_keccak` on the core route, pinned

Its exponent facts (`e(pack_g) < 21`, `e(step_g) < 2`, `e(rem_g) < 16`) at its honest instances, given the table
height carried from `verify_sub` (`expFam_okA_of`, `fams_okA` with route21's `vkQ_allA`), step `0`'s claim point the point (`ptEq_holds`), its runs over the head's exponents (`runFam_holds`, `vk_headWords`); `keccak_layer`'s point length
`y_g = step_g^16·rem_g`, `e(y_g) < 32`, carried from `verify_keccak` (`klQ_allA`) into its family (`ygFam_holds`,
`Own.keccak_layer.fams_okA`); its stream reads inside its residue runs at every height (`stFam_holds`, `stLt_holds`, `vk_stEx`); on
Lean's three axioms.
-/

/-- info: 'LeanVM.Guest.CoreMode.Own.verify_keccak.expFam_okA_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.CoreMode.Own.verify_keccak.expFam_okA_of

/-- info: 'LeanVM.Guest.CoreMode.Own.verify_keccak.fams_okA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.CoreMode.Own.verify_keccak.fams_okA

/-- info: 'LeanVM.Guest.EndExec.klQ_allA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.klQ_allA

/-- info: 'LeanVM.Guest.CoreMode.Own.keccak_layer.ygFam_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.CoreMode.Own.keccak_layer.ygFam_holds

/-- info: 'LeanVM.Guest.CoreMode.Own.keccak_layer.fams_okA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.CoreMode.Own.keccak_layer.fams_okA

/-- info: 'LeanVM.Guest.CoreMode.Own.verify_keccak.ptEq_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.CoreMode.Own.verify_keccak.ptEq_holds

/-- info: 'LeanVM.Guest.CoreMode.Own.verify_keccak.runFam_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.CoreMode.Own.verify_keccak.runFam_holds

/-- info: 'LeanVM.Guest.CoreMode.Own.verify_keccak.vk_headWords' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.CoreMode.Own.verify_keccak.vk_headWords

/-- info: 'LeanVM.Guest.CoreMode.Own.verify_keccak.stFam_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.CoreMode.Own.verify_keccak.stFam_holds

/-- info: 'LeanVM.Guest.CoreMode.Own.verify_keccak.vk_stEx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.CoreMode.Own.verify_keccak.vk_stEx

/-- info: 'LeanVM.Guest.CoreMode.Own.verify_keccak.stLt_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.CoreMode.Own.verify_keccak.stLt_holds
