import Whir.PCSBCSNativeRootRoles
import Whir.PCSBCSNativePacketVisit

/-! Actual successful historical mixed source to every literal first-address
capture. Visitation and address membership are derived, not endpoint premises.
The retained bad alternative concerns opening against the earlier prefix; this
is not a uniform-primitive bound or a Fiat-Shamir extraction theorem.
-/
set_option autoImplicit false
namespace Whir.PCSBCSNativeCapturedRows
open Concrete Protocol FiatShamirGame DuplexModeGame TypedOracleCompiler
open RawOracleCoupling PCSBCSChallengeOracle WHIRSourceChronology AnchoredPhysicalDriver
open PCSBCSSourceRootReferences PCSBCSMerkleRootCache PCSBCSCapturedNativeReplyBridge
open PCSBCSCapturedSourceAcceptance PublicMerkleLog MerkleTransport
open MerkleTransport.Commitments

section Driver
variable (cap : Nat) (model : WHIRCallerSupport.ProductionLayout)
    (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack) (Q : Nat)
    (packet : RawWHIRKeys.Packet ctx Q) (saved : AnchoredHeaderCodec.Record)
    (proofs : Array PrunedMerklePaths) (B : Nat)
    (limit : WHIRPhysicalVerifier.sourceBudget ctx Q packet ≤ B)
    (seed : DuplexPublicSimulator.Seed) (ro : RawKey B → Digest32)

private noncomputable abbrev addresses :=
  PCSBCSCapturedSourceTransport.address (p := packet.val.profile) (Q := B) (iv := ctx.iv)
    (boundary := (RawWHIRKeys.entry ctx packet.val).frames.length)

private noncomputable abbrev program :=
  PCSBCSCapturedIdealNativeAcceptance.allocationProgram cap model ctx stack Q packet saved proofs B limit

private noncomputable abbrev table := PCSBCSCapturedIdealNativeAcceptance.table ctx Q packet B seed ro

noncomputable def referenceLog (ref : Reference) : PublicLog :=
  sourceLog (addresses ctx Q packet B) ref
    (program cap model ctx stack Q packet saved proofs B limit) (table ctx Q packet B seed ro)

noncomputable def openingLog (opening : WHIRPhysicalVerifier.QueryOpening packet.val.profile) : PublicLog :=
  referenceLog cap model ctx stack Q packet saved proofs B limit seed ro
    (PCSBCSCapturedIdealNativeAcceptance.openingReference ctx Q packet opening saved.shape.lanes)

theorem mixed_success_captured_rows
    (a : Accepted ctx Q cap packet saved) (familyCap : cap ≤ 2^64)
    (success : (AnchoredMixedIdealSourceAcceptance.mixedView cap .fresh model ctx stack Q packet
      saved proofs ctx.iv B limit seed ro).result.value = some a) :
    ∀ opening ∈ a.wire.openings,
      let log := openingLog cap model ctx stack Q packet saved proofs B limit seed ro opening
      AuthenticLog seed log ∧
      (opening.result.rows = WHIRPhysicalVerifier.atQueries
        (WHIRPhysicalVerifier.frozenQueryOracle (hash seed) ⟨recordDomain (records log),[]⟩
          opening.root packet.val.profile opening.level.val saved.shape.lanes)
        (WHIRPhysicalVerifier.queryIndices packet.val.profile opening.level opening.sample) ∨
        PublicMerkleBinding.OpenPrimitiveBad seed log opening.root opening.result.paths) := by
  have self : packet ∈ RawOracleCoupling.Concrete.completion ctx Q packet := by
    simp [RawOracleCoupling.Concrete.completion]
  obtain ⟨bounded,recorded⟩ := PCSBCSNativePacketVisit.mixed_success_recorded cap model ctx stack Q
    packet saved proofs B limit seed ro a success packet self
  let packetB := PCSBCSNativePacketVisit.packetAtBound ctx Q B packet bounded
  let entered := PCSBCSNativePacketBridge.enteredPacketAt ctx stack B packetB
    (WHIRPhysicalVerifier.completion_profiles ctx Q packet packet self)
    (PCSBCSNativePacketBridge.completion_entries ctx Q packet packet self)
  have visited : (.inl entered) ∈ ((Sampling.execute (table ctx Q packet B seed ro)
      (program cap model ctx stack Q packet saved proofs B limit)).2.map Sigma.fst) := by
    exact List.mem_map.mpr ⟨_,recorded,rfl⟩
  have mentioned := PCSBCSNativeRootRoles.mixed_success_reindexed_address cap model ctx stack Q
    packet saved proofs B limit seed ro a success packetB rfl
  intro opening member
  have mentioned' : PCSBCSCapturedIdealNativeAcceptance.openingReference ctx Q packet opening saved.shape.lanes ∈
      addresses ctx Q packet B (.inl entered) := by
    simpa only [addresses,PCSBCSCapturedIdealNativeAcceptance.table,entered,packetB]
      using mentioned opening member
  obtain ⟨_,_,_,_,f,captured,auth,_,rows⟩ :=
    PCSBCSCapturedIdealNativeAcceptance.mixed_success_captured_rows cap model ctx stack Q packet
      saved proofs B limit seed ro a familyCap success opening member entered visited mentioned'
  obtain ⟨events,found,frozen,_⟩ := PCSBCSSourceRootCapture.capture_provenance
    (addresses ctx Q packet B)
    (PCSBCSCapturedIdealNativeAcceptance.openingReference ctx Q packet opening saved.shape.lanes)
    (program cap model ctx stack Q packet saved proofs B limit) (table ctx Q packet B seed ro) f captured
  have log : openingLog cap model ctx stack Q packet saved proofs B limit seed ro opening = f.queryPrefix := by
    rw [frozen]
    simp only [openingLog,referenceLog,sourceLog,found,Option.getD_some,freeze_prefix]
  dsimp only
  rw [log]
  exact ⟨auth,rows⟩
end Driver
#print axioms mixed_success_captured_rows
end Whir.PCSBCSNativeCapturedRows
