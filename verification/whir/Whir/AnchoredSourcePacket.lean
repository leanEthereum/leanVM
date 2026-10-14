import Whir.AnchoredPhysicalDriver

/-! Pinned 32c anchored source packets retain RawWHIRKeys' exact bounded path reconstruction and shared cache. Original and fresh caller boundaries have distinct exact frame counts. The entire original-CV/metadata/pending/point/value frame remains part of entryFrames and hence every physical path cost and backfill input. -/
namespace Whir.AnchoredSourcePacket
open Concrete FiatShamirGame WHIRSourceChronology AnchoredHeaderCodec
open WHIRPhysicalDriver
open MerkleTransport MerkleTransport.Commitments

/-- Fresh CPU source prelude is announcements plus clock; recursion captures immediately after its native transcript seed. Full pending blocks are retained until the next byte. -/
def originalPending : WHIRCallerClaims.CallerLayout → Nat
  | .recursion _ => 0
  | .cpu layout => ((24*(layout.tables.length+2)-1)%64)+1

def context (registry : ProductionRegistry) : RawWHIRKeys.Context :=
  { registry.context with
    entryLength := fun statement => ((WHIRCallerRegistry.selection registry.publicRegistry statement).map
      (fun selected => AnchoredSourceCaller.entryLength selected.1 (originalPending selected.1))).getD 0
    callerOutputCap := registry.callerOutputCap + (24*28+31)/32 }

/-- A later session transports the new payload and immutable frame only. Original point output blocks are not replayed or resampled here. -/
def freshContext (registry : ProductionRegistry) (record : Record) : RawWHIRKeys.Context :=
  {registry.context with entryLength := fun statement =>
    ((WHIRCallerRegistry.selection registry.publicRegistry statement).map
      (fun selected => AnchoredSourceFreshCaller.entryLength selected.1 record)).getD 0}

def headerPublic (registry : ProductionRegistry) : AnchoredHeaderRoots.Public where
  iv := registry.iv
  domain := registry.domain
  shapes := fun statement => ((WHIRCallerRegistry.selection registry.publicRegistry statement).map
    (fun selected => AnchoredSourceCaller.shape selected.1))

/-- The same immutable production registry selects the model. No packet carries a supplied layout, shape proof, root decoder or native acceptance evidence. -/
def packetModel (registry : ProductionRegistry) (ctx : RawWHIRKeys.Context)
    (catalogue : ctx.catalog = registry.context.catalog) (Q : Nat) (packet : RawWHIRKeys.Packet ctx Q) :
    WHIRCallerSupport.ProductionLayout :=
  match found : registry.models packet.val.statement with
  | some model => model
  | none => False.elim (by
      have catalog := packet.property.1
      rw [catalogue] at catalog
      change (WHIRCallerRegistry.selection registry.publicRegistry packet.val.statement).map Prod.snd =
        some packet.val.profile at catalog
      cases selected : WHIRCallerRegistry.selection registry.publicRegistry packet.val.statement with
      | none => simp [selected] at catalog
      | some pair =>
        have registered := (WHIRCallerRegistry.selection_spec registry.publicRegistry packet.val.statement
          pair.1 pair.2 selected).1
        simp [ProductionRegistry.publicRegistry,found] at registered)

structure Input (registry : ProductionRegistry) (Q : Nat) where
  packet : RawWHIRKeys.Packet (context registry) Q
  proofs : Array PrunedMerklePaths

structure Accepted (registry : ProductionRegistry) (Q cap : Nat) (record : Record) where
  packet : RawWHIRKeys.Packet (context registry) Q
  native : AnchoredPhysicalDriver.Accepted (context registry) Q cap packet record

def verifier (cap : Nat) (registry : ProductionRegistry) (Q : Nat) (record : Record)
    (input : Input registry Q) : Source cap (Option (Accepted registry Q cap record)) :=
  (AnchoredPhysicalDriver.verifySource cap .original (packetModel registry (context registry) rfl Q input.packet) (context registry) rfl Q
    input.packet record input.proofs).map (Option.map (fun native => ⟨input.packet,native⟩))

/-- Actual public opening endpoint: the attacker supplies only bytes and Merkle proofs. The native continuation enforces the complete caller/record parse before opening challenges, and computes acceptance itself. -/
def verifyAfter (cap : Nat) (registry : ProductionRegistry) (Q : Nat) (record : Record)
    (attacker : Source cap (Input registry Q)) : Source cap (Option (Accepted registry Q cap record)) :=
  attacker.bind (verifier cap registry Q record)

structure Completed (registry : ProductionRegistry) (Q cap : Nat) where
  record : Record
  accepted : Accepted registry Q cap record

/-- Original commitment is executed once. Its immutable result, rather than a caller-injected commitment record, is reused by the later attacker and verifier. The advertised value may depend on the original point. -/
def receiveAndVerify (cap : Nat) (registry : ProductionRegistry) (Q : Nat) (shape : Shape)
    (original : DuplexRefinement.State) (header : List E) (advertised : List E → E)
    (attacker : Record → Source cap (Input registry Q)) : Source cap (Option (Completed registry Q cap)) :=
  (AnchoredPhysicalTranscript.receiveSource shape original header advertised).bind fun result =>
    match result with
    | .error _ => .done none
    | .ok (_,record) => (verifyAfter cap registry Q record (attacker record)).map
        (Option.map (fun accepted => ⟨record,accepted⟩))

theorem verifier_counted (cap : Nat) (registry : ProductionRegistry) (Q : Nat) (record : Record)
    (input : Input registry Q) :
    Counts (WHIRPhysicalVerifier.sourceBudget (context registry) Q input.packet)
      (verifier cap registry Q record input) := by
  apply (Source.map_counted _ _ _).mpr
  exact AnchoredPhysicalDriver.verifySource_counted cap .original (packetModel registry (context registry) rfl Q input.packet)
    (context registry) rfl Q input.packet record input.proofs

/-- Every returned packet must satisfy the verifier resource bound on every reachable attacker branch. Neither rejected paths nor original-context backfill calls are discarded from the budget. -/
theorem verifyAfter_counted (cap : Nat) (registry : ProductionRegistry) (Q : Nat) (record : Record)
    (attacker : Source cap (Input registry Q)) (a b : Nat) (before : Counts a attacker)
    (budget : WHIRSourceBackfill.AllResults
      (fun input => WHIRPhysicalVerifier.sourceBudget (context registry) Q input.packet ≤ b) (erase attacker)) :
    Counts (a+b) (verifyAfter cap registry Q record attacker) := by
  apply (erase_counted _ _).mp
  rw [verifyAfter,Source.erase_bind]
  apply WHIRSourceBackfill.bind_counted_reachable _ _ _ a b ((erase_counted _ _).mpr before) budget
  intro input bounded
  exact (erase_counted _ _).mpr (Source.counts_mono (verifier_counted cap registry Q record input) bounded)

theorem receiveAndVerify_counted (cap : Nat) (registry : ProductionRegistry) (Q : Nat) (shape : Shape)
    (original : DuplexRefinement.State) (header : List E) (advertised : List E → E)
    (attacker : Record → Source cap (Input registry Q)) (a b : Nat)
    (before : ∀ record, Counts a (attacker record))
    (budget : ∀ record, WHIRSourceBackfill.AllResults
      (fun input => WHIRPhysicalVerifier.sourceBudget (context registry) Q input.packet ≤ b) (erase (attacker record))) :
    Counts (AnchoredPhysicalTranscript.receiveBudget shape+(a+b))
      (receiveAndVerify cap registry Q shape original header advertised attacker) := by
  apply Source.bind_counted _ _ (AnchoredPhysicalTranscript.receiveBudget shape) (a+b)
    (AnchoredPhysicalTranscript.receiveSource_counted shape original header advertised)
  intro result
  cases result with
  | error error => trivial
  | ok result =>
    apply (Source.map_counted _ _ _).mpr
    exact verifyAfter_counted cap registry Q result.2 (attacker result.2) a b (before result.2) (budget result.2)

structure FreshInput (registry : ProductionRegistry) (Q : Nat) (record : Record) where
  packet : RawWHIRKeys.Packet (freshContext registry record) Q
  proofs : Array PrunedMerklePaths

structure FreshAccepted (registry : ProductionRegistry) (Q cap : Nat) (record : Record) where
  packet : RawWHIRKeys.Packet (freshContext registry record) Q
  native : AnchoredPhysicalDriver.Accepted (freshContext registry record) Q cap packet record

/-- The saved record comes from the original receiver. A fresh attacker supplies only its new packet and paths, never a replacement record or acceptance payload. -/
def verifierFresh (cap : Nat) (registry : ProductionRegistry) (Q : Nat) (record : Record)
    (input : FreshInput registry Q record) : Source cap (Option (FreshAccepted registry Q cap record)) :=
  (AnchoredPhysicalDriver.verifySource cap .fresh
    (packetModel registry (freshContext registry record) rfl Q input.packet)
    (freshContext registry record) rfl Q input.packet record input.proofs).map
      (Option.map (fun native => ⟨input.packet,native⟩))

def verifyFreshAfter (cap : Nat) (registry : ProductionRegistry) (Q : Nat) (record : Record)
    (attacker : Source cap (FreshInput registry Q record)) : Source cap (Option (FreshAccepted registry Q cap record)) :=
  attacker.bind (verifierFresh cap registry Q record)

theorem verifierFresh_counted (cap : Nat) (registry : ProductionRegistry) (Q : Nat) (record : Record)
    (input : FreshInput registry Q record) :
    Counts (WHIRPhysicalVerifier.sourceBudget (freshContext registry record) Q input.packet)
      (verifierFresh cap registry Q record input) := by
  apply (Source.map_counted _ _ _).mpr
  exact AnchoredPhysicalDriver.verifySource_counted cap .fresh
    (packetModel registry (freshContext registry record) rfl Q input.packet)
    (freshContext registry record) rfl Q input.packet record input.proofs

theorem verifyFreshAfter_counted (cap : Nat) (registry : ProductionRegistry) (Q : Nat) (record : Record)
    (attacker : Source cap (FreshInput registry Q record)) (a b : Nat) (before : Counts a attacker)
    (budget : WHIRSourceBackfill.AllResults
      (fun input => WHIRPhysicalVerifier.sourceBudget (freshContext registry record) Q input.packet ≤ b) (erase attacker)) :
    Counts (a+b) (verifyFreshAfter cap registry Q record attacker) := by
  apply (erase_counted _ _).mp
  rw [verifyFreshAfter,Source.erase_bind]
  apply WHIRSourceBackfill.bind_counted_reachable _ _ _ a b ((erase_counted _ _).mpr before) budget
  intro input bounded
  exact (erase_counted _ _).mpr (Source.counts_mono (verifierFresh_counted cap registry Q record input) bounded)

structure FreshCompleted (registry : ProductionRegistry) (Q cap : Nat) where
  record : Record
  accepted : FreshAccepted registry Q cap record

/-- Source-owned original receiver followed by a genuinely fresh caller/session continuation. The retained record is the only link between their transcripts. -/
def receiveAndFreshVerify (cap : Nat) (registry : ProductionRegistry) (Q : Nat) (shape : Shape)
    (original : DuplexRefinement.State) (header : List E) (advertised : List E → E)
    (attacker : (record : Record) → Source cap (FreshInput registry Q record)) :
    Source cap (Option (FreshCompleted registry Q cap)) :=
  (AnchoredPhysicalTranscript.receiveSource shape original header advertised).bind fun result =>
    match result with
    | .error _ => .done none
    | .ok (_,record) => (verifyFreshAfter cap registry Q record (attacker record)).map
        (Option.map (fun accepted => ⟨record,accepted⟩))

theorem receiveAndFreshVerify_counted (cap : Nat) (registry : ProductionRegistry) (Q : Nat) (shape : Shape)
    (original : DuplexRefinement.State) (header : List E) (advertised : List E → E)
    (attacker : (record : Record) → Source cap (FreshInput registry Q record)) (a b : Nat)
    (before : ∀ record, Counts a (attacker record))
    (budget : ∀ record, WHIRSourceBackfill.AllResults
      (fun input => WHIRPhysicalVerifier.sourceBudget (freshContext registry record) Q input.packet ≤ b)
        (erase (attacker record))) :
    Counts (AnchoredPhysicalTranscript.receiveBudget shape+(a+b))
      (receiveAndFreshVerify cap registry Q shape original header advertised attacker) := by
  apply Source.bind_counted _ _ (AnchoredPhysicalTranscript.receiveBudget shape) (a+b)
    (AnchoredPhysicalTranscript.receiveSource_counted shape original header advertised)
  intro result
  cases result with
  | error error => trivial
  | ok result =>
    apply (Source.map_counted _ _ _).mpr
    exact verifyFreshAfter_counted cap registry Q result.2 (attacker result.2) a b (before result.2) (budget result.2)

end Whir.AnchoredSourcePacket

