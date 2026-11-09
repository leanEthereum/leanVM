import FORS

/-!
Axiom guards. The `#print axioms` below pin the main theorem, the size and cost theorems of
`Configurations` and the theorems the documentation cites. The last command checks
every declaration of every `FORS` module (`FORS.lean` imports all of them) and fails if
one depends on an axiom other than `propext`, `Classical.choice` and `Quot.sound`, such as the
one an unfinished proof or a compiled decision procedure adds.
-/

/-- info: 'FORS.h26_layered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FORS.h26_layered

/-- info: 'FORS.Lifetimes.h26_layered_adversary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FORS.Lifetimes.h26_layered_adversary

/-- info: 'FORS.Configurations.keccak256_h26_layered_k24' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FORS.Configurations.keccak256_h26_layered_k24

/-- info: 'FORS.Configurations.size_h26_layered_k24' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FORS.Configurations.size_h26_layered_k24

/-- info: 'FORS.Security.ForsPotential.det_bitsF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FORS.Security.ForsPotential.det_bitsF

/-- info: 'FORS.Security.AdvCount.forgeAdvantage_le_seedFree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FORS.Security.AdvCount.forgeAdvantage_le_seedFree

/-- info: 'FORS.Security.AdvCount.budgetedWinAdv_le_seedFreeH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FORS.Security.AdvCount.budgetedWinAdv_le_seedFreeH

/-- info: 'FORS.Security.Det.evalDist_rtable_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FORS.Security.Det.evalDist_rtable_split

/-- info: 'FORS.Security.AdvCount.win_avg_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FORS.Security.AdvCount.win_avg_le

/-- info: 'FORS.Security.SeedCoupling.evalDist_prepared_continuation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FORS.Security.SeedCoupling.evalDist_prepared_continuation

/-- info: 'FORS.Security.SignatureWitness.accepted_full_classification' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FORS.Security.SignatureWitness.accepted_full_classification

/-- info: 'FORS.Security.Fors.recover_classification' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FORS.Security.Fors.recover_classification

/-- info: 'FORS.Security.HiddenBridge.win_implies_badA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FORS.Security.HiddenBridge.win_implies_badA

/-- info: 'FORS.Security.Prefix.hashCalls_keygenFromSeed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FORS.Security.Prefix.hashCalls_keygenFromSeed

/-- info: 'FORS.Concrete.verify_calls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FORS.Concrete.verify_calls

/-- info: 'FORS.Security.GraphView.scan_boundW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FORS.Security.GraphView.scan_boundW

/-- info: 'FORS.LoopWalk.creation_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FORS.LoopWalk.creation_le

/-- info: 'FORS.Security.H0.lam_start' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FORS.Security.H0.lam_start

/-- info: 'FORS.Security.ForsPotential.sign_term' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FORS.Security.ForsPotential.sign_term

/-- info: 'FORS.Security.PrunedGraph.keyActive_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FORS.Security.PrunedGraph.keyActive_iff

/-- info: 'FORS.Security.ForsPotential.expectedFail_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FORS.Security.ForsPotential.expectedFail_le

/-- info: 'FORS.Security.verified_layers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FORS.Security.verified_layers

/-- info: 'FORS.Security.PotentialA.smallRoute_potentialHFrom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FORS.Security.PotentialA.smallRoute_potentialHFrom

/-- info: 'FORS.Security.ForsPotential.reveal_le_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FORS.Security.ForsPotential.reveal_le_all

/-- info: 'FORS.Security.ForsPotential.arm_paysF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FORS.Security.ForsPotential.arm_paysF

/-- info: 'FORS.Security.ForsPotential.sample_boundF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FORS.Security.ForsPotential.sample_boundF

/-- info: 'FORS.Security.ForsPotential.det_smallF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FORS.Security.ForsPotential.det_smallF

/-- info: 'FORS.Security.ForsPotential.forgeAdvantage_le_largeWH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FORS.Security.ForsPotential.forgeAdvantage_le_largeWH

/-- info: 'FORS.Concrete.fullDigestView_bijective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FORS.Concrete.fullDigestView_bijective

/-- info: 'FORS.Security.fieldInput_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FORS.Security.fieldInput_injective

/-- info: 'FORS.Security.hashFields_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FORS.Security.hashFields_injective

/-- info: 'FORS.walk_iterate_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FORS.walk_iterate_ne

/-- info: 'FORS.Completeness.correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FORS.Completeness.correct

/-- info: 'FORS.Completeness.eval_treeFold_pruned_path' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FORS.Completeness.eval_treeFold_pruned_path

/-- info: 'FORS.signature_size' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FORS.signature_size

/-- info: 'FORS.Cost.verification_compressions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FORS.Cost.verification_compressions

/-- info: 'FORS.Crate.eval_keygen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FORS.Crate.eval_keygen

/-- info: 'FORS.Crate.eval_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FORS.Crate.eval_sign

open Lean in
run_cmd do
  let env ← getEnv
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let mut bad : Array (Name × Name) := #[]
  for h : i in [0:env.header.moduleNames.size] do
    unless (`FORS).isPrefixOf env.header.moduleNames[i] do continue
    for name in env.header.moduleData[i]!.constNames do
      for axiomName in ← collectAxioms name do
        unless allowed.contains axiomName do bad := bad.push (name, axiomName)
  unless bad.isEmpty do
    throwError m!"declarations with axioms outside propext, Classical.choice, Quot.sound: {bad.toList}"
