import LeanVM.Guest.B1.VsC.VsNatChain
import LeanVM.Guest.B1.VsC.VsNatFront
import LeanVM.Guest.B1.VsC.VsNatRun
import LeanVM.Guest.B1.VsC.VsNatLink
import LeanVM.Guest.B1.VsC.VsNatLk

/-!
# `verify_sub`'s native values on an accepted child, pinned

The completeness direction of `verify_sub`'s Fiat-Shamir correspondence: the native verifier's
values, phase by phase, and the facts the guest's windows need of them. On Lean's three axioms.
-/

/-- info: 'LeanVM.Guest.B1.VsC.natChain_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.natChain_inv

/-- info: 'LeanVM.Guest.B1.VsC.natRun_phases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.natRun_phases

/-- info: 'LeanVM.Guest.B1.VsC.natFront' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.natFront

/-- info: 'LeanVM.Guest.B1.VsC.runTc_readOod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.runTc_readOod

/-- info: 'LeanVM.Guest.B1.VsC.natChain_fst_cap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.natChain_fst_cap

/-- info: 'LeanVM.Guest.B1.VsC.natReadPacked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.natReadPacked

/-- info: 'LeanVM.Guest.B1.VsC.natGrindSample' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.natGrindSample

/-- info: 'LeanVM.Guest.B1.VsC.natLink_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.natLink_inv

/-- info: 'LeanVM.Guest.B1.VsC.natChildLink' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.natChildLink

/-- info: 'LeanVM.Guest.B1.VsC.natLink_counts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.natLink_counts

/-- info: 'LeanVM.Guest.B1.VsC.natRun_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.natRun_all

/-- info: 'LeanVM.Guest.B1.VsC.lk2Ok_nat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.lk2Ok_nat

/-- info: 'LeanVM.Guest.B1.VsC.VsCtx.g1_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.VsCtx.g1_of

/-- info: 'LeanVM.Guest.B1.VsC.VsCtx.g2_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.VsCtx.g2_of

/-- info: 'LeanVM.Guest.B1.VsC.VsCtx.g3_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.VsCtx.g3_of

/-- info: 'LeanVM.Guest.B1.VsC.vsC_keccak_fs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsC_keccak_fs

/-- info: 'LeanVM.Guest.B1.VsC.vsA_keccak_fs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsA_keccak_fs

/-- info: 'LeanVM.Guest.B1.VsC.natLink_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.natLink_of

/-- info: 'LeanVM.Guest.B1.VsC.VsCtx.bw2_of_nat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.VsCtx.bw2_of_nat

/-- info: 'LeanVM.Guest.B1.VsC.BwNat.lengths' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.BwNat.lengths

/-- info: 'LeanVM.Guest.B1.VsC.VsCtx.bw2_of_bwNat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.VsCtx.bw2_of_bwNat

/-- info: 'LeanVM.Guest.B1.VsC.VsCtx.bw2Ret2_of_nat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.VsCtx.bw2Ret2_of_nat

/-- info: 'LeanVM.Guest.B1.VsC.VsCtx.bw2Ret2_honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.VsCtx.bw2Ret2_honest
