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
import Quantum.SufCma.Game
import Quantum.SufCma.Trace
import Quantum.Xmss.Keccak
import Quantum.Xmss.HonestTable
import Quantum.Classical
import Quantum.SufCma.Classical
import Quantum.Sponge.Oracle.Hardwired
import Quantum.Xmss.Classify
import Quantum.Xmss.TableLaw
import Quantum.Xmss.Events
import Quantum.Xmss.Hybrid.Kraus
import Quantum.Xmss.Hybrid.View
import Quantum.Xmss.Hybrid.Disclose
import Quantum.Xmss.GameReads
import Quantum.Xmss.FlipCost
import Quantum.Xmss.Hybrid.Seed
import Quantum.Xmss.Hybrid.ViewBy
import Quantum.Xmss.Assembly.TableComp
import Quantum.Xmss.Hybrid.SchemeSeed
import Quantum.Xmss.Assembly.Costs
import Quantum.Xmss.EncCost
import Quantum.Xmss.Hybrid.Coins
import Quantum.Xmss.Assembly.Template
import Quantum.Xmss.Assembly.Runtime1
import Quantum.Xmss.Hybrid.CoinsHiding
import Quantum.Xmss.Hybrid.CoinPath
import Quantum.Xmss.Assembly.RecordPorts
import Quantum.Xmss.Hybrid.Graded
import Quantum.Xmss.Hybrid.Mismatch
import Quantum.Xmss.Assembly.Masses
import Quantum.Xmss.Assembly.CostLift
import Quantum.Xmss.Assembly.PathBad
import Quantum.Xmss.Assembly.EndReads
import Quantum.Xmss.Assembly.GameTCalls
import Quantum.Xmss.Assembly.MassSources
import Quantum.Xmss.Assembly.SrcBad
import Quantum.Xmss.Assembly.FullTable
import Quantum.Xmss.Assembly.GameR
import Quantum.Xmss.Assembly.CostRun
import Quantum.Xmss.Assembly.CostJoint
import Quantum.Xmss.Assembly.MassesR0
import Quantum.Xmss.Assembly.ProgView
import Quantum.Xmss.Assembly.WinDecomp
import Quantum.Sponge.Oracle.Hardwired.ReadCost
import Quantum.Xmss.Assembly.GameCongr
import Quantum.Xmss.Hybrid.SeedStage
import Quantum.Xmss.Assembly.ProgSafe
import Quantum.Xmss.Assembly.ReparamR0
import Quantum.Xmss.Hybrid.GradedMasked
import Quantum.Xmss.Assembly.CoversFull
import Quantum.Xmss.Assembly.EventSqrt
import Quantum.Xmss.Assembly.PrefixFacts
import Quantum.Xmss.Assembly.TrialsOff
import Quantum.Xmss.Assembly.KeyLazy
import Quantum.Xmss.Assembly.KeysReparam
import Quantum.Xmss.Assembly.EncPotential
import Quantum.Xmss.Assembly.PathsDisjoint
import Quantum.Xmss.Assembly.TrialHit
import Quantum.Sponge.Oracle.Hardwired.DecUniform
import Quantum.Xmss.Assembly.TrialSource
import Quantum.Xmss.Assembly.TrialHitUniform
import Quantum.Xmss.Assembly.RestMass
import Quantum.Xmss.Assembly.EncPorts
import Quantum.Xmss.Assembly.HTrial
import Quantum.Xmss.Assembly.GoodTables
import Quantum.Xmss.Assembly.RecJ
import Quantum.Xmss.Assembly.CostRefined
import Quantum.Xmss.Assembly.CwRec
import Quantum.Sponge.Oracle.Hardwired.Persistence
import Quantum.Xmss.Assembly.EncRefined
import Quantum.Xmss.Assembly.RecBadMass
import Quantum.Xmss.Assembly.HwHeads
import Quantum.Xmss.Assembly.CwRev
import Quantum.Xmss.Assembly.RecOffDecHit
import Quantum.Xmss.Assembly.CwReFail
import Quantum.Xmss.NoReuse
import Quantum.Xmss.Assembly.NoReuse
import Quantum.Xmss.Hybrid.SchemeSplit
import Quantum.Xmss.Hybrid.CoinStage
import Quantum.Xmss.Hybrid.R0Stage
import Quantum.Xmss.Assembly.Security
import Quantum.Xmss.Assembly.BoundValue
import Quantum.Xmss.Assembly.CoinsEvent
import Quantum.Xmss.Assembly.Reparam
import Quantum.Xmss.Assembly.GameT
import Quantum.Xmss.Assembly.RecordDrop
import Quantum.Sphincs.Keccak
import Quantum.Sphincs.Coverage
import Quantum.Sphincs.Codeword
import Quantum.Sphincs.CoverStream
import Quantum.Sphincs.CovBad
import Quantum.Sig.Sampled
import Quantum.Sphincs.HonestTable
import Quantum.Sphincs.Assembly.PathsDisjoint
import Quantum.Sphincs.Hybrid.SchemeSplit
import Quantum.Sphincs.Events
import Quantum.Sphincs.EncCost
import Quantum.Sphincs.Hybrid.SeedStage
import Quantum.Sphincs.Hybrid.Seed
import Quantum.Sphincs.Hybrid.Disclose
import Quantum.Sphincs.Classify
import Quantum.Sphincs.Assembly.Template.Exempt
import Quantum.Sphincs.Hybrid.RStage
import Quantum.Sphincs.Assembly.Reparam
import Quantum.Sphincs.Assembly.FullTable
import Quantum.Sphincs.Hybrid.DigestStage
import Quantum.Sphincs.Assembly.GameTCalls
import Quantum.Sphincs.Assembly.GameT
import Quantum.Sphincs.Assembly.RecordDrop
import Quantum.Sphincs.Assembly.Costs
import Quantum.Sphincs.Assembly.GameR
import Quantum.Sphincs.Game
import Quantum.Sphincs.Assembly.PrefixFacts
import Quantum.Sphincs.Assembly.CostRun
import Quantum.Sphincs.Assembly.EncPorts
import Quantum.Sphincs.Assembly.ProgSafe
import Quantum.Sphincs.Assembly.TrialHitUniform
import Quantum.Sphincs.Assembly.HwHeads
import Quantum.Sphincs.Assembly.RecBadMass
import Quantum.Sphincs.Assembly.RecJ
import Quantum.Sphincs.Assembly.WinDecomp
import Quantum.Sphincs.Assembly.EventSqrt
import Quantum.Sphincs.Assembly.EncRefined
import Quantum.Sphincs.Assembly.KeysReparam
import Quantum.Sphincs.Assembly.RecOffDecHit
import Quantum.Sphincs.Assembly.HConflict

/-! Security against quantum adversaries in the quantum random-permutation model (`Quantum.Model`),
on VCVio's quantum oracle programs (`VCVio.Quantum`): the sponge's collision and preimage
resistance against an adversary making `q` superposition calls to `π` and `π⁻¹`
(`Quantum.Sponge.qrpm_sponge_collision_le`, `Quantum.Sponge.qrpm_sponge_preimage_le`), their
values at Keccak-256's sizes (`Quantum.Sponge.keccak256_qrpm_collision_le`,
`Quantum.Sponge.keccak256_qrpm_preimage_le`), and leanXMSS's strong unforgeability against quantum
adversaries (`Quantum.Xmss.Assembly.leanXmss_qrpm_security`). The build fails if the axiom
footprint of the main theorems ever grows beyond Lean's three standard axioms. -/

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

/-- info: 'Quantum.SufCma.winProb_classicalAdversary' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quantum.SufCma.winProb_classicalAdversary

/-- info: 'Quantum.Xmss.Assembly.leanXmss_qrpm_security' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quantum.Xmss.Assembly.leanXmss_qrpm_security

/-- info: 'Quantum.Xmss.Assembly.qrpmBound_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quantum.Xmss.Assembly.qrpmBound_le

/-- info: 'Quantum.Xmss.Assembly.qrpmBound_two_pow_30_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quantum.Xmss.Assembly.qrpmBound_two_pow_30_le

/-- info: 'Quantum.Xmss.Assembly.qrpmBound_two_pow_50_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quantum.Xmss.Assembly.qrpmBound_two_pow_50_le
