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
import Quantum.Sphincs.Assembly.CwRev
import Quantum.Sphincs.Assembly.HTrial
import Quantum.Sphincs.Assembly.KeyLazy
import Quantum.Sphincs.Assembly.MassSources
import Quantum.Sphincs.Assembly.EventRef
import Quantum.Sphincs.Assembly.Stream
import Quantum.Sphincs.Assembly.EventSide
import Quantum.Sphincs.Assembly.CwReFail
import Quantum.Sphincs.Assembly.GoodES
import Quantum.Sphincs.Assembly.CandCharge
import Quantum.Sphincs.Assembly.ChgRevBound
import Quantum.Sphincs.Hybrid.Masked
import Quantum.Sphincs.Assembly.Masses
import Quantum.Sphincs.Assembly.HmsgCoversMass
import Quantum.Sphincs.Assembly.BoundValue
import Quantum.Sphincs.Assembly.HStaticFrac
import Quantum.Sphincs.Assembly.ChgRevAvg
import Quantum.Qrom.Model
import Quantum.Qrom.SufCma.Game
import Quantum.Qrom.Classical
import Quantum.Qrom.SufCma.Classical
import Quantum.Qrom.Embed
import Quantum.Qrom.CellEvent
import Quantum.Qrom.TableLaw
import Quantum.Qrom.Regroup
import Quantum.Qrom.Xmss.Scheme
import Quantum.Qrom.Xmss.Slots
import Quantum.Qrom.Xmss.Events
import Quantum.Qrom.Xmss.HonestTable
import Quantum.Qrom.Xmss.NoReuse
import Quantum.Qrom.Xmss.GameReads
import Quantum.Qrom.Xmss.Runtime1
import Quantum.Qrom.Xmss.Classify
import Quantum.Qrom.Xmss.Template
import Quantum.Qrom.Xmss.GameT
import Quantum.Qrom.Xmss.GameTFacts
import Quantum.Qrom.Xmss.GameTCalls
import Quantum.Qrom.Xmss.Hybrid
import Quantum.Qrom.Xmss.Costs.Total
import Quantum.Qrom.Xmss.End
import Quantum.Qrom.Xmss.Security
import Quantum.Qrom.Xmss.BoundValue
import Quantum.Qrom.Sphincs.Scheme
import Quantum.Qrom.Sphincs.Slots
import Quantum.Qrom.Sphincs.Cov
import Quantum.Qrom.Sphincs.Stream
import Quantum.Qrom.Sphincs.HonestTable
import Quantum.Qrom.Sphincs.GameReads
import Quantum.Qrom.Sphincs.Runtime1
import Quantum.Qrom.Sphincs.Events
import Quantum.Qrom.Sphincs.Classify
import Quantum.Qrom.Sphincs.Template
import Quantum.Qrom.Sphincs.GameT
import Quantum.Qrom.Sphincs.StreamGame
import Quantum.Qrom.Sphincs.GameTCalls
import Quantum.Qrom.Sphincs.GameTFacts
import Quantum.Qrom.Sphincs.GameTFactsPre
import Quantum.Qrom.Sphincs.Costs.Total
import Quantum.Qrom.Sphincs.Hybrid
import Quantum.Qrom.Sphincs.End
import Quantum.Qrom.Sphincs.Security
import Quantum.Qrom.Sphincs.BoundValue
import Quantum.Sponge.Indifferentiability.Selection
import Quantum.Sponge.Indifferentiability.FixCircuit
import Quantum.Sponge.Indifferentiability.PadCircuit
import Quantum.Cost.Qrom
import Quantum.Cost.Qrpm
import Quantum.Qrom.TableLawOn
import Quantum.Qrom.MultiUser.Owner
import Quantum.StdModel.World
import Quantum.StdModel.StraightLine
import Quantum.StdModel.Formats
import Quantum.StdModel.Props
import Quantum.StdModel.Xmss.Reduction
import Quantum.StdModel.Sphincs.Reduction
import Quantum.Par.Subst
import Quantum.Par.Lockstep
import Quantum.Par.LockstepRounds
import Quantum.Xmss.Assembly.Depth.Ports
import Quantum.Qrom.Sphincs.Multi.Classify
import Quantum.Qrom.Sphincs.Multi.GameT
import Quantum.Qrom.Sphincs.Multi.StreamGame
import Quantum.Qrom.Sphincs.Multi.GameTSel
import Quantum.Qrom.Sphincs.Multi.GameTCalls
import Quantum.Qrom.Sphincs.Multi.Costs.Numeric
import Quantum.Qrom.Sphincs.Multi.BoundValue
import Quantum.Qrom.Sphincs.DepthSecurity
import Quantum.Qrom.Sphincs.DepthBoundValue
import Quantum.Qrom.SufCma.GamePar
import Quantum.Sponge.Oracle.Parallel
import Quantum.Cost.Nist
import Quantum.Qrom.Xmss.DepthBoundValue
import Quantum.Xmss.Hybrid.GradedPar
import Quantum.Qrom.Xmss.DepthBridge
import Quantum.Qrom.Xmss.Multi.Hybrid
import Quantum.Qrom.Xmss.Multi.End
import Quantum.Qrom.Xmss.Multi.Security
import Quantum.Qrom.Xmss.Multi.BoundValue
import Quantum.Qrom.Xmss.Multi.GameT
import Quantum.Qrom.Xmss.Multi.GameTSel
import Quantum.Qrom.Xmss.Multi.GameTCalls
import Quantum.Qrom.Xmss.Multi.GameTFacts
import Quantum.Qrom.SufCma.MultiOne
import Quantum.Qrom.Xmss.Multi.NoReuse
import Quantum.Qrom.Xmss.Multi.Memo
import Quantum.Qrom.Xmss.Multi.Table
import Quantum.Qrom.Xmss.Multi.Classify

/-! Security against quantum adversaries in the quantum random-permutation model (`Quantum.Model`),
on VCVio's quantum oracle programs (`VCVio.Quantum`): the sponge's collision and preimage
resistance against an adversary making `q` superposition calls to `π` and `π⁻¹`
(`Quantum.Sponge.qrpm_sponge_collision_le`, `Quantum.Sponge.qrpm_sponge_preimage_le`), their
values at Keccak-256's sizes (`Quantum.Sponge.keccak256_qrpm_collision_le`,
`Quantum.Sponge.keccak256_qrpm_preimage_le`), and leanXMSS's and leanSPHINCS's strong
unforgeability against quantum adversaries (`Quantum.Xmss.Assembly.leanXmss_qrpm_security`,
`Quantum.Sphincs.Assembly.leanSphincs_qrpm_security`). For comparison, both schemes in the
quantum random-oracle model with Keccak-256 as one random function (`Quantum.Qrom`:
`Quantum.Qrom.Xmss.leanXmss_qrom_security`, `Quantum.Qrom.Sphincs.leanSphincs_qrom_security`),
and leanXMSS with `n` users in the quantum random-oracle model
(`Quantum.Qrom.Xmss.Multi.leanXmss_qrom_mu_security`). The build fails if the axiom footprint of
the main theorems ever grows beyond Lean's three standard axioms. -/

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

/-- info: 'Quantum.Sphincs.Assembly.leanSphincs_qrpm_security' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quantum.Sphincs.Assembly.leanSphincs_qrpm_security

/-- info: 'Quantum.Sphincs.Assembly.sphincsQrpmBound_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quantum.Sphincs.Assembly.sphincsQrpmBound_le

/-- info: 'Quantum.Sphincs.Assembly.sphincsQrpmBound_two_pow_30_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quantum.Sphincs.Assembly.sphincsQrpmBound_two_pow_30_le

/-- info: 'Quantum.Sphincs.Assembly.sphincsQrpmBound_two_pow_40_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quantum.Sphincs.Assembly.sphincsQrpmBound_two_pow_40_le

/-- info: 'Quantum.Qrom.SufCma.winProb_classicalAdversary' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quantum.Qrom.SufCma.winProb_classicalAdversary

/-- info: 'Quantum.Qrom.Xmss.leanXmss_qrom_security' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quantum.Qrom.Xmss.leanXmss_qrom_security

/-- info: 'Quantum.Qrom.Xmss.xmssQromBound_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quantum.Qrom.Xmss.xmssQromBound_le

/-- info: 'Quantum.Qrom.Xmss.xmssQromBound_two_pow_30_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quantum.Qrom.Xmss.xmssQromBound_two_pow_30_le

/-- info: 'Quantum.Qrom.Xmss.xmssQromBound_two_pow_50_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quantum.Qrom.Xmss.xmssQromBound_two_pow_50_le

/-- info: 'Quantum.Qrom.Sphincs.leanSphincs_qrom_security' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quantum.Qrom.Sphincs.leanSphincs_qrom_security

/-- info: 'Quantum.Qrom.Sphincs.sphincsQromBound_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quantum.Qrom.Sphincs.sphincsQromBound_le

/-- info: 'Quantum.Qrom.Sphincs.sphincsQromBound_two_pow_30_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quantum.Qrom.Sphincs.sphincsQromBound_two_pow_30_le

/-- info: 'Quantum.Qrom.Sphincs.sphincsQromBound_two_pow_40_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quantum.Qrom.Sphincs.sphincsQromBound_two_pow_40_le

/-- info: 'Quantum.Qrom.Xmss.Multi.leanXmss_qrom_mu_security' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quantum.Qrom.Xmss.Multi.leanXmss_qrom_mu_security

/-- info: 'Quantum.Qrom.Xmss.Multi.xmssQromMuBound_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quantum.Qrom.Xmss.Multi.xmssQromMuBound_le

/-- info: 'Quantum.StdModel.Xmss.xmss_suf_le_props_keccak' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quantum.StdModel.Xmss.xmss_suf_le_props_keccak

/-- info: 'Quantum.Qrom.Xmss.leanXmss_qrom_depth_security' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quantum.Qrom.Xmss.leanXmss_qrom_depth_security

/-- info: 'Quantum.Qrom.Xmss.xmssQromDepthBound_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quantum.Qrom.Xmss.xmssQromDepthBound_le

/-- info: 'Quantum.StdModel.Sphincs.sphincs_suf_le_props_keccak' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quantum.StdModel.Sphincs.sphincs_suf_le_props_keccak

/-- info: 'Quantum.Cost.Qrom.leanXmss_qrom_gateDepth_closed' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quantum.Cost.Qrom.leanXmss_qrom_gateDepth_closed

/-- info: 'Quantum.Cost.Nist.leanXmss_qrom_cat1_lowDepth' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quantum.Cost.Nist.leanXmss_qrom_cat1_lowDepth

/-- info: 'Quantum.Cost.Nist.leanXmss_qrom_cat1_inPlace' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quantum.Cost.Nist.leanXmss_qrom_cat1_inPlace

/-- info: 'Quantum.Qrom.Sphincs.Multi.leanSphincs_qrom_mu_security' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quantum.Qrom.Sphincs.Multi.leanSphincs_qrom_mu_security

/-- info: 'Quantum.Qrom.Sphincs.Multi.sphincsQromMuBound_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quantum.Qrom.Sphincs.Multi.sphincsQromMuBound_le

/-- info: 'Quantum.Qrom.Sphincs.Multi.rhoMaxQ_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quantum.Qrom.Sphincs.Multi.rhoMaxQ_le

/-- info: 'Quantum.Qrom.Sphincs.leanSphincs_qrom_depth_security' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quantum.Qrom.Sphincs.leanSphincs_qrom_depth_security

/-- info: 'Quantum.Qrom.Sphincs.sphincsQromDepthBound_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quantum.Qrom.Sphincs.sphincsQromDepthBound_le
