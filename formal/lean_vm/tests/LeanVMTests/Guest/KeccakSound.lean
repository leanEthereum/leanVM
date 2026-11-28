import LeanVM.Guest.B1.KeccakGkr.IndexMleLink
import LeanVM.Guest.B1.KeccakGkr.LayerRounds
import LeanVM.Guest.B1.KeccakGkr.LayerHolds
import LeanVM.Guest.B1.KeccakGkr.VkHolds
import LeanVM.Guest.B1.KeccakGkr.Algebra
import LeanVM.Guest.B1.KeccakGkr.LayerRmfe
import LeanVM.Guest.B1.KeccakGkr.KFormMath
import LeanVM.Guest.B1.KeccakGkr.FoldMath

/-!
# The Keccak reduction in the circuit, pinned

B1 of `verify_sub`'s section `KECCAK validity, by GKR over the rounds` and of `index_mle`, on Lean's
three axioms.
-/

/-- info: 'LeanVM.Guest.B1.KeccakGkr.index_side_sound_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.KeccakGkr.index_side_sound_core

/-- info: 'LeanVM.Guest.B1.VerifySub.layer_rounds_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VerifySub.layer_rounds_sound

/-- info: 'LeanVM.Guest.B1.VerifySub.keccak_plain_rounds_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VerifySub.keccak_plain_rounds_holds

/-- info: 'LeanVM.Guest.B1.VerifySub.keccak_layer_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VerifySub.keccak_layer_holds

/-- info: 'LeanVM.Guest.B1.VerifySub.keccak_section_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VerifySub.keccak_section_sound
