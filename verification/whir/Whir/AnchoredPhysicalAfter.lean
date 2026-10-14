import Whir.AnchoredPhysicalExecution
import Whir.WHIRPhysicalDriver

/-! The arbitrary attacker may make ordinary/constructed prequeries and then
choose transport, a retained anchor record and Merkle paths. Only the trusted
anchored verifier can produce acceptance. The whole source keeps those earlier
queries; verifier-only captures do not substitute for its first-address logs. -/
set_option autoImplicit false
namespace Whir.AnchoredPhysicalAfter
open Concrete FiatShamirGame DuplexModeGame WHIRSourceChronology WHIRPhysicalVerifier
open MerkleTransport MerkleTransport.Commitments PublicMerkleProgram
open WHIRPhysicalDriver
open WHIRSourceBackfill (AllResults)

structure Input (ctx : RawWHIRKeys.Context) (Q : Nat) where
  packet : RawWHIRKeys.Packet ctx Q
  record : AnchoredHeaderCodec.Record
  proofs : Array PrunedMerklePaths

structure Accepted (ctx : RawWHIRKeys.Context) (Q cap : Nat) where
  input : Input ctx Q
  native : AnchoredPhysicalDriver.Accepted ctx Q cap input.packet input.record

def verifier (cap : Nat) (registry : ProductionRegistry) (Q : Nat) (input : Input registry.context Q) :
    Source cap (Option (Accepted registry.context Q cap)) :=
  (AnchoredPhysicalDriver.verifySource cap .fresh (registry.packetModel Q input.packet)
    registry.context rfl Q input.packet input.record input.proofs).map
      (Option.map (fun native => ⟨input,native⟩))

def verifyAfter (cap : Nat) (registry : ProductionRegistry) (Q : Nat)
    (attacker : Source cap (Input registry.context Q)) : Source cap (Option (Accepted registry.context Q cap)) :=
  attacker.bind (verifier cap registry Q)

theorem verifier_counted (cap : Nat) (registry : ProductionRegistry) (Q : Nat)
    (input : Input registry.context Q) :
    Counts (sourceBudget registry.context Q input.packet) (verifier cap registry Q input) := by
  apply (Source.map_counted _ _ _).mpr
  exact AnchoredPhysicalDriver.verifySource_counted cap .fresh (registry.packetModel Q input.packet)
    registry.context rfl Q input.packet input.record input.proofs

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

theorem native_segment (cap : Nat) (registry : ProductionRegistry) (Q : Nat)
    (attacker : Source cap (Input registry.context Q)) (observations : List Observation)
    (accepted : Accepted registry.context Q cap)
    (run : Runs (erase (verifyAfter cap registry Q attacker)) observations (some accepted)) :
    ∃ (input : Input registry.context Q) (before after : List Observation)
      (native : AnchoredPhysicalDriver.Accepted registry.context Q cap input.packet input.record),
      observations = before ++ after ∧ Runs (erase attacker) before input ∧
      Runs (erase (AnchoredPhysicalDriver.verifySource cap .fresh (registry.packetModel Q input.packet)
        registry.context rfl Q input.packet input.record input.proofs)) after (some native) ∧
      accepted = ⟨input,native⟩ := by
  obtain ⟨before,input,after,trace,first,last⟩ :=
    (Source.erased_bind_runs attacker _ observations (some accepted)).mp run
  obtain ⟨result,nativeRun,mapped⟩ := (Source.erased_map_runs _ _ after (some accepted)).mp last
  obtain ⟨native,returned,equal⟩ := Option.map_eq_some_iff.mp mapped
  rw [returned] at nativeRun
  exact ⟨input,before,after,native,trace,first,nativeRun,equal.symm⟩

theorem real_result (C : PrimitiveOracle) (iv : Digest32) (cap : Nat)
    (registry : ProductionRegistry) (Q : Nat) (attacker : Source cap (Input registry.context Q)) :
    (runReal C iv (compile (verifyAfter cap registry Q attacker))).view.result =
      let chosen := (runReal C iv (compile attacker)).view.result
      let native := (runReal C iv (compile (AnchoredPhysicalDriver.verifySource cap .fresh
        (registry.packetModel Q chosen.value.packet) registry.context rfl Q
        chosen.value.packet chosen.value.record chosen.value.proofs))).view.result
      ⟨native.value.map (fun accepted => ⟨chosen.value,accepted⟩),chosen.events ++ native.events⟩ := by
  rw [verifyAfter,Source.real_bind]
  simp only [verifier,Source.real_map]

end Whir.AnchoredPhysicalAfter
#print axioms Whir.AnchoredPhysicalAfter.verifier_counted
#print axioms Whir.AnchoredPhysicalAfter.verifyAfter_counted
#print axioms Whir.AnchoredPhysicalAfter.native_segment
#print axioms Whir.AnchoredPhysicalAfter.real_result
