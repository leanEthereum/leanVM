import Quantum.Model
import Quantum.Decomposition
import Quantum.Sponge.PermTail
import Quantum.Sponge.Outputs
import Quantum.Sponge.Hash
import Quantum.Sponge.Simulate
import Quantum.Sponge.Reads.Log
import Quantum.Sponge.Assembly.Prep
import Quantum.Sponge.Reads.Single
import Quantum.Sponge.Keccak
import Quantum.Sponge.Assembly.Collision
import Quantum.Sponge.Target
import Quantum.Xmss.Game
import Quantum.Xmss.Keccak
import Quantum.Xmss.HonestTable
import Quantum.Classical
import Quantum.Xmss.Classical
import Quantum.Sponge.Oracle.Hardwired
import Quantum.Xmss.Classify
import Quantum.Xmss.TableLaw
import Quantum.Xmss.Events
import Quantum.Xmss.Hybrid.Kraus
import Quantum.Xmss.Hybrid.View
import Quantum.Xmss.Hybrid.Disclose
import Quantum.Sphincs.Keccak
import Quantum.Sphincs.Coverage

/-! Security against quantum adversaries in the quantum random-permutation model (`Quantum.Model`),
on VCVio's quantum oracle programs (`VCVio.Quantum`): the sponge's collision and preimage
resistance against an adversary making `q` superposition calls to `π` and `π⁻¹`
(`Quantum.Sponge.qrpm_sponge_collision_le`, `Quantum.Sponge.qrpm_sponge_preimage_le`), and their
values at Keccak-256's sizes (`Quantum.Sponge.keccak256_qrpm_collision_le`,
`Quantum.Sponge.keccak256_qrpm_preimage_le`). The build fails if the axiom footprint of the main
theorems ever grows beyond Lean's three standard axioms. -/

/-- info: 'Quantum.qrpmEvalDistMap_eq_spongePerm' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quantum.qrpmEvalDistMap_eq_spongePerm

/-- info: 'Quantum.Sponge.qrpm_sponge_collision_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quantum.Sponge.qrpm_sponge_collision_le

/-- info: 'Quantum.Sponge.qrpm_sponge_preimage_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quantum.Sponge.qrpm_sponge_preimage_le

/-- info: 'Quantum.Sponge.keccak256_qrpm_collision_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quantum.Sponge.keccak256_qrpm_collision_le

/-- info: 'Quantum.Sponge.keccak256_qrpm_preimage_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quantum.Sponge.keccak256_qrpm_preimage_le

/-- info: 'Quantum.qrpmEvalDistMap_toQuantumAt_qrpmImpl' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quantum.qrpmEvalDistMap_toQuantumAt_qrpmImpl

/-- info: 'Quantum.Xmss.winProb_classicalAdversary' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quantum.Xmss.winProb_classicalAdversary
