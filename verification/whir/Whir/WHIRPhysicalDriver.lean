import Whir.WHIRPhysicalSoundness
import Whir.WHIRSourceComposition
import Whir.WHIRSourceBackfill

namespace Whir.WHIRPhysicalDriver
open Concrete Protocol FiatShamirGame DuplexModeGame
open MerkleTransport WHIRSourceChronology WHIRPhysicalVerifier
open PublicMerkleProgram (Runs)
open WHIRSourceBackfill (AllResults)

/-- The physical parser and logical caller registry share this one public
production model. Neither the attacker nor a successful result chooses lanes. -/
structure ProductionRegistry where
  iv : Digest32
  domain : Digest32
  models : Digest32 → Option WHIRCallerSupport.ProductionLayout
  callerOutputCap : Nat

def ProductionRegistry.publicRegistry (registry : ProductionRegistry) : WHIRCallerRegistry.Public where
  iv := registry.iv
  domain := registry.domain
  layouts := fun statement => (registry.models statement).map WHIRCallerSupport.ProductionLayout.layout
  callerOutputCap := registry.callerOutputCap

def ProductionRegistry.context (registry : ProductionRegistry) : RawWHIRKeys.Context :=
  WHIRCallerRegistry.context registry.publicRegistry

def ProductionRegistry.packetModel (registry : ProductionRegistry) (Q : Nat)
    (packet : RawWHIRKeys.Packet registry.context Q) : WHIRCallerSupport.ProductionLayout :=
  match found : registry.models packet.val.statement with
  | some model => model
  | none => False.elim (by
      have registered := (WHIRCallerRegistry.selection_spec registry.publicRegistry _ _ _
        (WHIRCallerRegistry.packet_selection registry.publicRegistry Q packet)).1
      simp only [publicRegistry,found,Option.map_none] at registered
      cases registered)

theorem ProductionRegistry.packetModel_layout (registry : ProductionRegistry) (Q : Nat)
    (packet : RawWHIRKeys.Packet registry.context Q) :
    (registry.packetModel Q packet).layout = WHIRCallerRegistry.packetLayout registry.publicRegistry Q packet := by
  have registered := (WHIRCallerRegistry.selection_spec registry.publicRegistry _ _ _
    (WHIRCallerRegistry.packet_selection registry.publicRegistry Q packet)).1
  unfold packetModel
  split
  · rename_i model found
    change (registry.models packet.val.statement).map WHIRCallerSupport.ProductionLayout.layout = _ at registered
    rw [found] at registered
    exact Option.some.inj registered
  · rename_i found
    simp only [publicRegistry,found,Option.map_none] at registered
    cases registered

theorem ProductionRegistry.packetModel_registered (registry : ProductionRegistry) (Q : Nat)
    (packet : RawWHIRKeys.Packet registry.context Q) :
    registry.publicRegistry.layouts packet.val.statement = some (registry.packetModel Q packet).layout := by
  rw [registry.packetModel_layout Q packet]
  exact (WHIRCallerRegistry.selection_spec registry.publicRegistry _ _ _
    (WHIRCallerRegistry.packet_selection registry.publicRegistry Q packet)).1

def ProductionRegistry.packetLanes (registry : ProductionRegistry) (Q : Nat)
    (packet : RawWHIRKeys.Packet registry.context Q) : Nat :=
  WHIRCallerClaims.callerLanes (registry.packetModel Q packet).layout

/- Historical unanchored endpoint retained only for its underlying physical list-binding theorem chain. The 32c public endpoint is AnchoredSourcePacket.receiveAndVerify. -/
namespace Unanchored

/-- An attacker chooses transport bytes and opening proofs, not a verifier
result or its acceptance evidence. -/
structure Input (ctx : RawWHIRKeys.Context) (Q : Nat) where
  packet : RawWHIRKeys.Packet ctx Q
  proofs : Array PrunedMerklePaths

structure Accepted (ctx : RawWHIRKeys.Context) (Q cap : Nat) where
  packet : RawWHIRKeys.Packet ctx Q
  verified : Verified ctx Q cap packet

def select {ctx : RawWHIRKeys.Context} {Q cap : Nat} :
    Option (Accepted ctx Q cap) → Option (RawWHIRKeys.Packet ctx Q) :=
  Option.map Accepted.packet

def verifier (cap : Nat) (registry : ProductionRegistry) (Q : Nat) (input : Input registry.context Q) :
    Source cap (Option (Accepted registry.context Q cap)) :=
  (verifySource cap (registry.packetModel Q input.packet) registry.context rfl Q
    (registry.packetLanes Q input.packet) input.packet input.proofs).map
    (Option.map (fun verified => ⟨input.packet,verified⟩))

/-- Exactly one final native verifier follows the arbitrary attacker-input
source. Rejection is literal none; successful payloads only come from verifier. -/
def verifyAfter (cap : Nat) (registry : ProductionRegistry) (Q : Nat)
    (attacker : Source cap (Input registry.context Q)) : Source cap (Option (Accepted registry.context Q cap)) :=
  attacker.bind (verifier cap registry Q)

/-- A public completed-result/observer event. The fixed list is reconstructed
only from the first frozen public records, and the claims are those the native
caller actually decoded. No source program, coins, or primitive oracle occurs. -/
def nativeWrong {ctx : RawWHIRKeys.Context} {Q cap : Nat} (state : CausalBindingState.State cap) :
    Option (Accepted ctx Q cap) → Prop
  | none => False
  | some accepted =>
      let original := WHIRPhysicalSoundness.committedStatement accepted.verified state
      ¬ ∃ witness ∈ InitialCandidates.witnesses (ParameterBounds.config accepted.packet.val.profile)
        original.lanes original.root,
        RingPCSGame.Honest (ParameterBounds.config accepted.packet.val.profile)
          original.lanes original.family original.points witness

theorem native_list_bound {ctx : RawWHIRKeys.Context} {Q cap : Nat}
    (state : CausalBindingState.State cap) (accepted : Accepted ctx Q cap) :
    (InitialCandidates.witnesses (ParameterBounds.config accepted.packet.val.profile)
      (WHIRPhysicalSoundness.committedStatement accepted.verified state).lanes
      (WHIRPhysicalSoundness.committedStatement accepted.verified state).root).card ≤ 2^32 :=
  InitialCandidates.production_witnesses_card _ _ _

theorem verifier_counted (cap : Nat) (registry : ProductionRegistry) (Q : Nat)
    (input : Input registry.context Q) :
    Counts (sourceBudget registry.context Q input.packet) (verifier cap registry Q input) := by
  apply (Source.map_counted _ _ _).mpr
  exact verifySource_counted cap (registry.packetModel Q input.packet) registry.context rfl Q
    (registry.packetLanes Q input.packet) input.packet input.proofs

/-- Only packets the attacker can actually return require a native-verifier
budget. This includes every answer branch, not only a chosen oracle execution. -/
theorem verifyAfter_counted (cap : Nat) (registry : ProductionRegistry) (Q : Nat)
    (attacker : Source cap (Input registry.context Q)) (a b : Nat) (before : Counts a attacker)
    (budget : AllResults (fun input => sourceBudget registry.context Q input.packet ≤ b) (erase attacker)) :
    Counts (a+b) (verifyAfter cap registry Q attacker) := by
  apply (erase_counted _ _).mp
  rw [verifyAfter,Source.erase_bind]
  apply WHIRSourceBackfill.bind_counted_reachable _ _ _ a b
    ((erase_counted _ _).mpr before) budget
  intro input bounded
  exact (erase_counted _ _).mpr (Source.counts_mono (verifier_counted cap registry Q input) bounded)

private theorem allResults_bind (program : Program R) (next : R → Program S) (post : S → Prop) :
    AllResults post (WHIRModeFinal.bind program next) =
      AllResults (fun result => AllResults post (next result)) program := by
  induction program with
  | done => rfl
  | ask query cont ih => simp only [WHIRModeFinal.bind,AllResults,ih]

theorem verifier_selected (cap : Nat) (registry : ProductionRegistry) (Q : Nat)
    (input : Input registry.context Q) (post : RawWHIRKeys.Packet registry.context Q → Prop)
    (valid : post input.packet) :
    AllResults (fun result => ∀ packet, select result = some packet → post packet)
      (erase (verifier cap registry Q input)) := by
  rw [verifier,Source.map,Source.erase_bind,allResults_bind]
  apply WHIRSourceBackfill.allResults_of_forall
  intro result packet selected
  cases result with
  | none => cases selected
  | some verified =>
    cases Option.some.inj selected
    exact valid

/-- Successful native verification preserves the attacker's chosen packet.
In particular a reachable path budget needs no guard or result clipping. -/
theorem verifyAfter_selected (cap : Nat) (registry : ProductionRegistry) (Q : Nat)
    (attacker : Source cap (Input registry.context Q)) (post : RawWHIRKeys.Packet registry.context Q → Prop)
    (reachable : AllResults (fun input => post input.packet) (erase attacker)) :
    AllResults (fun result => ∀ packet, select result = some packet → post packet)
      (erase (verifyAfter cap registry Q attacker)) := by
  rw [verifyAfter,Source.erase_bind,allResults_bind]
  exact WHIRSourceBackfill.allResults_mono _ _ _ reachable
    (fun input valid => verifier_selected cap registry Q input post valid)

theorem verifyAfter_path_bound (cap : Nat) (registry : ProductionRegistry) (Q : Nat)
    (attacker : Source cap (Input registry.context Q)) (Mf : Nat)
    (reachable : AllResults
      (fun input => DuplexFraming.pathCost (RawWHIRKeys.coordinate registry.context input.packet.val 0) ≤ Mf) (erase attacker)) :
    AllResults (fun result => ∀ packet, select result = some packet →
      DuplexFraming.pathCost (RawWHIRKeys.coordinate registry.context packet.val 0) ≤ Mf)
      (erase (verifyAfter cap registry Q attacker)) :=
  verifyAfter_selected cap registry Q attacker _ reachable

/-- Every accepted wrapper result has an actual native verifier suffix. An
arbitrary attacker prefix cannot supply a fabricated Verified payload. -/
theorem native_segment (cap : Nat) (registry : ProductionRegistry) (Q : Nat)
    (attacker : Source cap (Input registry.context Q)) (observations : List Observation)
    (accepted : Accepted registry.context Q cap)
    (run : Runs (erase (verifyAfter cap registry Q attacker)) observations (some accepted)) :
    ∃ (input : Input registry.context Q) (before after : List Observation)
      (verified : Verified registry.context Q cap input.packet),
      observations = before ++ after ∧ Runs (erase attacker) before input ∧
      Runs (erase (verifySource cap (registry.packetModel Q input.packet) registry.context rfl Q
        (registry.packetLanes Q input.packet) input.packet input.proofs)) after (some verified) ∧
      accepted = ⟨input.packet,verified⟩ := by
  obtain ⟨before,input,after,trace,first,last⟩ :=
    (Source.erased_bind_runs attacker _ observations (some accepted)).mp run
  obtain ⟨result,native,mapped⟩ := (Source.erased_map_runs _ _ after (some accepted)).mp last
  obtain ⟨verified,returned,equal⟩ := Option.map_eq_some_iff.mp mapped
  rw [returned] at native
  exact ⟨input,before,after,verified,trace,first,native,equal.symm⟩

/-- The event-segment equation is about the real compiler result itself,
including both the attacker's events and the trusted native continuation. -/
theorem real_result (C : PrimitiveOracle) (iv : Digest32) (cap : Nat)
    (registry : ProductionRegistry) (Q : Nat) (attacker : Source cap (Input registry.context Q)) :
    (runReal C iv (compile (verifyAfter cap registry Q attacker))).view.result =
      let chosen := (runReal C iv (compile attacker)).view.result
      let native := (runReal C iv (compile (verifySource cap (registry.packetModel Q chosen.value.packet)
        registry.context rfl Q (registry.packetLanes Q chosen.value.packet)
        chosen.value.packet chosen.value.proofs))).view.result
      ⟨native.value.map (fun verified => ⟨chosen.value.packet,verified⟩),chosen.events ++ native.events⟩ := by
  rw [verifyAfter,Source.real_bind]
  simp only [verifier,Source.real_map]

theorem real_native_segment (C : PrimitiveOracle) (iv : Digest32) (cap : Nat)
    (registry : ProductionRegistry) (Q : Nat) (attacker : Source cap (Input registry.context Q))
    (accepted : Accepted registry.context Q cap)
    (returned : (runReal C iv (compile (verifyAfter cap registry Q attacker))).view.result.value = some accepted) :
    ∃ (input : Input registry.context Q) (verified : Verified registry.context Q cap input.packet),
      input = (runReal C iv (compile attacker)).view.result.value ∧
      (runReal C iv (compile (verifySource cap (registry.packetModel Q input.packet) registry.context rfl Q
        (registry.packetLanes Q input.packet) input.packet input.proofs))).view.result.value = some verified ∧
      accepted = ⟨input.packet,verified⟩ ∧
      (runReal C iv (compile (verifyAfter cap registry Q attacker))).view.result.events =
        (runReal C iv (compile attacker)).view.result.events ++
          (runReal C iv (compile (verifySource cap (registry.packetModel Q input.packet) registry.context rfl Q
            (registry.packetLanes Q input.packet) input.packet input.proofs))).view.result.events := by
  have whole := real_result C iv cap registry Q attacker
  have value := congrArg Result.value whole
  rw [value] at returned
  obtain ⟨verified,native,equal⟩ := Option.map_eq_some_iff.mp returned
  exact ⟨_,verified,rfl,native,equal.symm,congrArg Result.events whole⟩

end Unanchored

end Whir.WHIRPhysicalDriver
