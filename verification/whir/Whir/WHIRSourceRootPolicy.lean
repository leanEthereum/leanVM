import Whir.WHIRHeaderRoots
import Whir.WHIRSourceChronology
import Whir.PublicMerkleProbability
import Whir.DuplexPublicSimulator

/-! Causal root announcements for a fixed source and public final-value selector.
Only finite past compression cells are inspected; a pending query contributes its
input, never its answer. Exact registry/header/packet parsers handle raw prequeries
and mode calls. Source commitments, packet footprints and the final selected packet
are captured before any final backfill. No changes to the public `View` are needed.

Prefix-union persistence covers inconsistent logs as well as genuine oracle traces.
The independent all-branches `FreeAnnouncements R` resource accounts for zero-cost
source commits. With compression budget Q, the cap is
`(Q+1)*(R+(Q+1)*(productionDepth+1))`, where `productionDepth` is the computed maximum
of the actual 56 production schedules. Theorems connect the finite replay to both
source-owned `recover` and the actual `PublicCompressionProgram` full-C trace.
This module supplies policy/capture/resource facts, not the frozen-opening transport
or an unconditional duplex security claim. -/
namespace Whir.WHIRSourceRootPolicy
open FiatShamirGame DuplexFraming DuplexModeGame
open WHIRSourceChronology WHIRCallerRegistry PublicCompressionProgram
open PublicMerkleLog

variable {cap : Nat} {T : Type}

/-- Zero-cost commitments require an independent all-branches resource. -/
def FreeAnnouncements : Nat → Source cap T → Prop
  | _, .done _ => True
  | R, .ask _ next => ∀ d, FreeAnnouncements R (next d)
  | R, .commit _ next => 0 < R ∧ FreeAnnouncements (R-1) next
  | R, .claims _ _ _ next => FreeAnnouncements R next

/-- A public geometry bound, not a root-cover assumption. -/
def ProfileBound (registry : Public) (H : Nat) : Prop :=
  ∀ statement layout profile, selection registry statement = some (layout,profile) →
    WHIRHistory.depth (ParameterBounds.config profile) ≤ H

/-- Computable maximum of the actual 56 production schedules. -/
def productionDepth : Nat :=
  Finset.univ.sup (fun p : ParameterBounds.Profile => WHIRHistory.depth (ParameterBounds.config p))

theorem production_profileBound (registry : Public) : ProfileBound registry productionDepth := by
  intro statement layout profile _
  exact Finset.le_sup (f := fun p : ParameterBounds.Profile =>
    WHIRHistory.depth (ParameterBounds.config p)) (Finset.mem_univ profile)

/-- First chronological replies are retained, including on inconsistent logs. -/
def firstReply (log : PublicLog) (n : Node) : Option Digest32 :=
  PublicMerkleLog.lookup log.reverse n

def partialEval (log : PublicLog) {N : Nat} : Computation T N → Option T
  | .ret value => some value
  | .draw n next => (firstReply log n).bind (fun d => partialEval log (next d))

def queryReply (iv : Digest32) (log : PublicLog) (q : Query) : Option Digest32 :=
  partialEval log (queryCalls iv q)

/-- Header parsing includes exact raw garbage prequeries; footprint parsing uses
only the actual exact packet recognizer, never an assumed list of roots. -/
def rawRoots (registry : Public) (Q : Nat) (raw : RawKey Q) : List Digest32 :=
  (WHIRHeaderRoots.rawRoot registry raw).toList ++
    match RawWHIRKeys.recognize (context registry) Q raw with
    | none => []
    | some pos => (WHIRSnapshotReplay.historyFootprint pos.1.val.profile
        pos.1.val.statement pos.1.val.messages).map Prod.fst

def queryRoots (registry : Public) (Q : Nat) (visible : PublicLog) : Query → List Digest32
  | .primitive _ n => match DuplexPublicSimulator.privateKey Q visible n with
    | none => []
    | some raw => rawRoots registry Q raw
  | .construction q _ =>
    if bound : pathCost q ≤ Q then rawRoots registry Q (constructionKey Q registry.iv q bound)
    else []

def packetRoots (registry : Public) (Q : Nat)
    (packet : RawWHIRKeys.Packet (context registry) Q) : List Digest32 :=
  (WHIRHeaderRoots.packetHeader registry Q packet).toList.map WHIRHeaderRoots.Header.root ++
    (WHIRSnapshotReplay.historyFootprint packet.val.profile packet.val.statement
      packet.val.messages).map Prod.fst

def finalRoots (registry : Public) (Q : Nat)
    (select : T → Option (RawWHIRKeys.Packet (context registry) Q)) (value : T) : List Digest32 :=
  match select value with
  | none => []
  | some packet => packetRoots registry Q packet

def advance (visible : PublicLog) (q : Query) (d : Digest32) : PublicLog :=
  match q with
  | .primitive _ n => (n,d) :: visible
  | .construction _ _ => visible

/-- Query inputs are inspected before attempting their answer. In particular the
first missing compression reply does not hide the pending query's announcements. -/
def scan (registry : Public) (Q : Nat)
    (select : T → Option (RawWHIRKeys.Packet (context registry) Q)) (log : PublicLog) :
    Source cap T → PublicLog → List Digest32
  | .done value, _ => finalRoots registry Q select value
  | .commit root next, visible => root :: scan registry Q select log next visible
  | .claims _ _ _ next, visible => scan registry Q select log next visible
  | .ask q next, visible => queryRoots registry Q visible q ++
      match queryReply registry.iv log q with
      | none => []
      | some d => scan registry Q select log (next d) (advance visible q d)

/-- Union over chronological prefixes: adding any cell cannot revoke an earlier
announcement, even if the new cell contradicts an old reply. -/
def rootList (registry : Public) (Q : Nat)
    (select : T → Option (RawWHIRKeys.Packet (context registry) Q))
    (source : Source cap T) : PublicLog → List Digest32
  | [] => scan registry Q select [] source []
  | entry :: past => scan registry Q select (entry :: past) source [] ++ rootList registry Q select source past

noncomputable def policy (registry : Public) (Q : Nat)
    (select : T → Option (RawWHIRKeys.Packet (context registry) Q)) (source : Source cap T) :
    PublicMerkleProbability.RootPolicy := fun log => (rootList registry Q select source log).toFinset

theorem rootsGrow (registry : Public) (Q : Nat)
    (select : T → Option (RawWHIRKeys.Packet (context registry) Q)) (source : Source cap T) :
    PublicMerkleProbability.RootsGrow (policy registry Q select source) := by
  intro history entry root member
  simp only [policy, List.mem_toFinset] at *
  exact List.mem_append_right _ member

theorem scan_captured (registry : Public) (Q : Nat)
    (select : T → Option (RawWHIRKeys.Packet (context registry) Q)) (source : Source cap T)
    (log : PublicLog) (root : Digest32) (member : root ∈ scan registry Q select log source []) :
    root ∈ policy registry Q select source log := by
  simp only [policy, List.mem_toFinset]
  cases log with
  | nil => exact member
  | cons entry past => exact List.mem_append_left _ member

private theorem option_length (o : Option α) : o.toList.length ≤ 1 := by cases o <;> simp

theorem replyFootprint_length {c : Protocol.Config} (q : CausalProbability.Coordinate c)
    (xs : List Concrete.E) : (WHIRSnapshotReplay.replyFootprint q xs).length ≤ 1 := by
  cases q <;> simp only [WHIRSnapshotReplay.replyFootprint]
  all_goals try simp
  split <;> try simp
  split <;> try simp
  split <;> try simp
  split <;> simp [List.length_map]

theorem historyFootprint_length (p : ParameterBounds.Profile) (s : Digest32)
    (messages : List WHIRHistory.Pending) :
    (WHIRSnapshotReplay.historyFootprint p s messages).length ≤ messages.length := by
  induction messages with
  | nil => simp [WHIRSnapshotReplay.historyFootprint]
  | cons m rest ih =>
    cases rest with
    | nil => simp [WHIRSnapshotReplay.historyFootprint]
    | cons previous older =>
      simp only [WHIRSnapshotReplay.historyFootprint, List.length_append, List.length_cons] at *
      have := replyFootprint_length (WHIRReplay.query p (s,previous :: older)) m.scalars
      omega

theorem rawRoots_length (registry : Public) (Q H : Nat) (bounded : ProfileBound registry H)
    (raw : RawKey Q) : (rawRoots registry Q raw).length ≤ H+1 := by
  unfold rawRoots
  rw [List.length_append]
  have hh := option_length (WHIRHeaderRoots.rawRoot registry raw)
  cases found : RawWHIRKeys.recognize (context registry) Q raw with
  | none => simpa only [List.length_nil, Nat.add_zero] using hh.trans (by omega)
  | some pos =>
    simp only [List.length_map]
    have hf := historyFootprint_length pos.1.val.profile pos.1.val.statement pos.1.val.messages
    have hd := RawWHIRKeys.packet_depth (context registry) Q pos.1
    have hb := bounded _ _ _ (packet_selection registry Q pos.1)
    omega

theorem queryRoots_length (registry : Public) (Q H : Nat) (bounded : ProfileBound registry H)
    (visible : PublicLog) (q : Query) : (queryRoots registry Q visible q).length ≤ H+1 := by
  cases q with
  | primitive purpose n =>
    simp only [queryRoots]
    cases DuplexPublicSimulator.privateKey Q visible n with
    | none => simp
    | some raw => exact rawRoots_length registry Q H bounded raw
  | construction q valid =>
    simp only [queryRoots]
    split
    · exact rawRoots_length registry Q H bounded _
    · simp

private theorem query_cost_pos (q : Query) : 1 ≤ q.cost := by
  cases q with
  | primitive => exact Nat.le_refl _
  | construction q valid => exact DuplexRawProgram.pathCost_pos q

theorem packetRoots_length (registry : Public) (Q H : Nat) (bounded : ProfileBound registry H)
    (packet : RawWHIRKeys.Packet (context registry) Q) :
    (packetRoots registry Q packet).length ≤ H+1 := by
  have hh := option_length (WHIRHeaderRoots.packetHeader registry Q packet)
  have hf := historyFootprint_length packet.val.profile packet.val.statement packet.val.messages
  have hd := RawWHIRKeys.packet_depth (context registry) Q packet
  have hb := bounded _ _ _ (packet_selection registry Q packet)
  simp only [packetRoots, List.length_append, List.length_map]
  omega

theorem finalRoots_length (registry : Public) (Q H : Nat) (bounded : ProfileBound registry H)
    (select : T → Option (RawWHIRKeys.Packet (context registry) Q)) (value : T) :
    (finalRoots registry Q select value).length ≤ H+1 := by
  unfold finalRoots
  cases select value with
  | none => simp
  | some packet => exact packetRoots_length registry Q H bounded packet

theorem scan_length (registry : Public) (Q H R N : Nat) (bounded : ProfileBound registry H)
    (select : T → Option (RawWHIRKeys.Packet (context registry) Q))
    (source : Source cap T) (counted : WHIRSourceChronology.Counts N source)
    (free : FreeAnnouncements R source) (log visible : PublicLog) :
    (scan registry Q select log source visible).length ≤ R + (N+1)*(H+1) := by
  induction source generalizing R N visible with
  | done value =>
    have hf := finalRoots_length registry Q H bounded select value
    have hm := Nat.mul_le_mul_right (H+1) (show 1 ≤ N+1 by omega)
    simp only [Nat.one_mul] at hm
    exact hf.trans (by omega)
  | commit root next ih =>
    have h := ih (R-1) N counted free.2 visible
    simp only [scan, List.length_cons]
    have := free.1
    omega
  | claims p entry request next ih => exact ih R N counted free visible
  | ask q next ih =>
    simp only [scan, List.length_append]
    have hq := queryRoots_length registry Q H bounded visible q
    cases reply : queryReply registry.iv log q with
    | none =>
      simp only [List.length_nil]
      have hm := Nat.mul_le_mul_right (H+1) (show 1 ≤ N+1 by omega)
      simp only [Nat.one_mul] at hm
      omega
    | some d =>
      simp only
      have h := ih d R (N-q.cost) (counted.2 d) (free d) (advance visible q d)
      have hp := query_cost_pos q
      have hc := counted.1
      have hm := Nat.mul_le_mul_right (H+1) (show N-q.cost+1+1 ≤ N+1 by omega)
      rw [Nat.add_mul, Nat.one_mul] at hm
      omega

theorem rootList_length (registry : Public) (Q H R : Nat) (bounded : ProfileBound registry H)
    (select : T → Option (RawWHIRKeys.Packet (context registry) Q))
    (source : Source cap T) (counted : WHIRSourceChronology.Counts Q source)
    (free : FreeAnnouncements R source) (log : PublicLog) :
    (rootList registry Q select source log).length ≤ (log.length+1)*(R+(Q+1)*(H+1)) := by
  induction log with
  | nil => simpa [rootList] using scan_length registry Q H R Q bounded select source counted free [] []
  | cons entry past ih =>
    have hs := scan_length registry Q H R Q bounded select source counted free (entry :: past) []
    simp only [rootList, List.length_append, List.length_cons]
    nlinarith

theorem cardinality (registry : Public) (Q H R : Nat) (bounded : ProfileBound registry H)
    (select : T → Option (RawWHIRKeys.Packet (context registry) Q))
    (source : Source cap T) (counted : WHIRSourceChronology.Counts Q source)
    (free : FreeAnnouncements R source) (log : PublicLog) (budget : log.length ≤ Q) :
    (policy registry Q select source log).card ≤ (Q+1)*(R+(Q+1)*(H+1)) := by
  exact (List.toFinset_card_le _).trans ((rootList_length registry Q H R bounded select source counted free log).trans
    (Nat.mul_le_mul_right _ (Nat.succ_le_succ budget)))

/-- The actual partial source interpreter stops at a missing finite compression
cell; its events have the same source-owned type as `recover`. -/
def partialPrefix (iv : Digest32) (log : PublicLog) : Source cap T → Prefix cap T
  | .done value => ⟨[],none,some value⟩
  | .commit root next => prependPrefix (.commit root) (partialPrefix iv log next)
  | .claims p entry request next =>
      prependPrefix (.claims p entry request) (partialPrefix iv log next)
  | .ask q next => match queryReply iv log q with
    | none => ⟨[],some q,none⟩
    | some d => prependPrefix (.answer q d) (partialPrefix iv log (next d))

def visibleAfter : List (Event cap) → PublicLog → PublicLog
  | [], visible => visible
  | .answer q d :: rest, visible => visibleAfter rest (advance visible q d)
  | .commit _ :: rest, visible => visibleAfter rest visible
  | .claims _ _ _ :: rest, visible => visibleAfter rest visible

def eventRoots (registry : Public) (Q : Nat) : List (Event cap) → PublicLog → List Digest32
  | [], _ => []
  | .answer q d :: rest, visible =>
      queryRoots registry Q visible q ++ eventRoots registry Q rest (advance visible q d)
  | .commit root :: rest, visible => root :: eventRoots registry Q rest visible
  | .claims _ _ _ :: rest, visible => eventRoots registry Q rest visible

def capture (registry : Public) (Q : Nat)
    (select : T → Option (RawWHIRKeys.Packet (context registry) Q))
    (seen : Prefix cap T) (visible : PublicLog) : List Digest32 :=
  eventRoots registry Q seen.events visible ++
    (seen.pending.toList.flatMap (queryRoots registry Q (visibleAfter seen.events visible)) ++
      seen.value.toList.flatMap (finalRoots registry Q select))

theorem scan_eq_capture (registry : Public) (Q : Nat)
    (select : T → Option (RawWHIRKeys.Packet (context registry) Q))
    (log : PublicLog) (source : Source cap T) (visible : PublicLog) :
    scan registry Q select log source visible =
      capture registry Q select (partialPrefix registry.iv log source) visible := by
  induction source generalizing visible with
  | done => simp [scan,partialPrefix,capture,eventRoots]
  | commit root next ih =>
    simpa [scan,partialPrefix,capture,prependPrefix,eventRoots,visibleAfter] using
      congrArg (List.cons root) (ih visible)
  | claims p entry request next ih =>
    simpa [scan,partialPrefix,capture,prependPrefix,eventRoots,visibleAfter] using ih visible
  | ask q next ih =>
    cases answer : queryReply registry.iv log q with
    | none => simp [scan,partialPrefix,answer,capture,eventRoots,visibleAfter]
    | some d =>
      simp only [scan,partialPrefix,answer,prependPrefix]
      rw [ih d]
      simp [capture,eventRoots,visibleAfter,List.append_assoc]

theorem partialPrefix_recover (iv : Digest32) (log : PublicLog) (source : Source cap T) :
    recover source (observations (partialPrefix iv log source).events) =
      partialPrefix iv log source := by
  induction source with
  | done => rfl
  | commit root next ih =>
    simpa [partialPrefix,prependPrefix,observations,WHIRSourceChronology.recover] using congrArg (prependPrefix (.commit root)) ih
  | claims p entry request next ih =>
    simpa [partialPrefix,prependPrefix,observations,WHIRSourceChronology.recover] using
      congrArg (prependPrefix (.claims p entry request)) ih
  | ask q next ih =>
    cases answer : queryReply iv log q with
    | none => simp [partialPrefix,answer,observations,WHIRSourceChronology.recover]
    | some d =>
      simpa [partialPrefix,answer,prependPrefix,observations,WHIRSourceChronology.recover] using
        congrArg (prependPrefix (.answer q d)) (ih d)

theorem prefix_capture (registry : Public) (Q : Nat)
    (select : T → Option (RawWHIRKeys.Packet (context registry) Q))
    (source : Source cap T) (log : PublicLog) (root : Digest32)
    (member : root ∈ capture registry Q select (partialPrefix registry.iv log source) []) :
    root ∈ policy registry Q select source log :=
  scan_captured registry Q select source log root ((scan_eq_capture ..).symm ▸ member)

theorem event_commit (registry : Public) (Q : Nat) (events : List (Event cap))
    (visible : PublicLog) (root : Digest32) (member : Event.commit root ∈ events) :
    root ∈ eventRoots registry Q events visible := by
  induction events generalizing visible with
  | nil => simp at member
  | cons event rest ih =>
    cases event with
    | answer q d => exact List.mem_append_right _ (ih _ (by simpa using member))
    | commit other =>
      rcases List.mem_cons.mp member with same | member
      · cases same; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih _ member)
    | claims p entry request => exact ih _ (by simpa using member)

/-- Every actual source commitment in the recovered prefix is covered, without a
separate correctness/cover hypothesis. -/
theorem commit_captured (registry : Public) (Q : Nat)
    (select : T → Option (RawWHIRKeys.Packet (context registry) Q))
    (source : Source cap T) (log : PublicLog) (root : Digest32)
    (member : Event.commit root ∈ (partialPrefix registry.iv log source).events) :
    root ∈ policy registry Q select source log :=
  prefix_capture registry Q select source log root
    (List.mem_append_left _ (event_commit registry Q _ [] root member))

theorem pending_captured (registry : Public) (Q : Nat)
    (select : T → Option (RawWHIRKeys.Packet (context registry) Q))
    (source : Source cap T) (log : PublicLog) (q : Query) (root : Digest32)
    (pending : (partialPrefix registry.iv log source).pending = some q)
    (member : root ∈ queryRoots registry Q
      (visibleAfter (partialPrefix registry.iv log source).events []) q) :
    root ∈ policy registry Q select source log := by
  apply prefix_capture registry Q select source log root
  unfold capture
  apply List.mem_append_right
  apply List.mem_append_left
  simpa only [pending,Option.toList_some,List.flatMap_cons,List.flatMap_nil,List.append_nil] using member

theorem eventRoots_append (registry : Public) (Q : Nat) (before after : List (Event cap))
    (visible : PublicLog) :
    eventRoots registry Q (before ++ after) visible =
      eventRoots registry Q before visible ++ eventRoots registry Q after (visibleAfter before visible) := by
  induction before generalizing visible with
  | nil => rfl
  | cons event rest ih =>
    cases event <;> simp [eventRoots,visibleAfter,ih,List.append_assoc]

theorem answered_captured (registry : Public) (Q : Nat)
    (select : T → Option (RawWHIRKeys.Packet (context registry) Q))
    (source : Source cap T) (log : PublicLog) (before after : List (Event cap))
    (q : Query) (d root : Digest32)
    (split : (partialPrefix registry.iv log source).events = before ++ .answer q d :: after)
    (member : root ∈ queryRoots registry Q (visibleAfter before []) q) :
    root ∈ policy registry Q select source log := by
  apply prefix_capture registry Q select source log root
  apply List.mem_append_left
  rw [split,eventRoots_append]
  exact List.mem_append_right _ (List.mem_append_left _ member)

theorem final_captured (registry : Public) (Q : Nat)
    (select : T → Option (RawWHIRKeys.Packet (context registry) Q))
    (source : Source cap T) (log : PublicLog) (value : T)
    (packet : RawWHIRKeys.Packet (context registry) Q) (root : Digest32)
    (done : (partialPrefix registry.iv log source).value = some value)
    (selected : select value = some packet) (member : root ∈ packetRoots registry Q packet) :
    root ∈ policy registry Q select source log := by
  apply prefix_capture registry Q select source log root
  unfold capture
  apply List.mem_append_right
  apply List.mem_append_right
  simpa [done,finalRoots,selected] using member

theorem raw_header_member (registry : Public) (Q : Nat) (raw : RawKey Q) (root : Digest32)
    (parsed : WHIRHeaderRoots.rawRoot registry raw = some root) :
    root ∈ rawRoots registry Q raw := by
  apply List.mem_append_left
  simp [parsed]

theorem raw_footprint_member (registry : Public) (Q : Nat) (raw : RawKey Q)
    (pos : RawWHIRKeys.Position (context registry) Q)
    (recognized : RawWHIRKeys.recognize (context registry) Q raw = some pos)
    (ref : WHIRSnapshotReplay.RootRef)
    (member : ref ∈ WHIRSnapshotReplay.historyFootprint pos.1.val.profile
      pos.1.val.statement pos.1.val.messages) :
    ref.1 ∈ rawRoots registry Q raw := by
  apply List.mem_append_right
  simp only [recognized]
  exact List.mem_map.mpr ⟨ref,member,rfl⟩

theorem primitive_roots (registry : Public) (Q : Nat) (visible : PublicLog)
    (purpose : Purpose) (n : Node) (raw : RawKey Q)
    (recognized : DuplexPublicSimulator.privateKey Q visible n = some raw) :
    queryRoots registry Q visible (.primitive purpose n) = rawRoots registry Q raw := by
  simp [queryRoots,recognized]

theorem construction_roots (registry : Public) (Q : Nat) (visible : PublicLog)
    (q : Coordinate) (valid : DuplexEncoding.Admissible q) (bound : pathCost q ≤ Q) :
    queryRoots registry Q visible (.construction q valid) =
      rawRoots registry Q (constructionKey Q registry.iv q bound) := by
  simp [queryRoots,bound]

theorem packet_header_member (registry : Public) (Q : Nat)
    (packet : RawWHIRKeys.Packet (context registry) Q) (header : WHIRHeaderRoots.Header)
    (parsed : WHIRHeaderRoots.packetHeader registry Q packet = some header) :
    header.root ∈ packetRoots registry Q packet := by
  apply List.mem_append_left
  simp [parsed]

theorem packet_footprint_member (registry : Public) (Q : Nat)
    (packet : RawWHIRKeys.Packet (context registry) Q) (ref : WHIRSnapshotReplay.RootRef)
    (member : ref ∈ WHIRSnapshotReplay.historyFootprint packet.val.profile
      packet.val.statement packet.val.messages) : ref.1 ∈ packetRoots registry Q packet :=
  List.mem_append_right _ (List.mem_map.mpr ⟨ref,member,rfl⟩)

theorem packet_ancestor_footprint_member (registry : Public) (Q : Nat)
    (packet : RawWHIRKeys.Packet (context registry) Q) (i : Nat)
    (ref : WHIRSnapshotReplay.RootRef)
    (member : ref ∈ WHIRSnapshotReplay.historyFootprint packet.val.profile
      packet.val.statement (packet.val.messages.drop i)) : ref.1 ∈ packetRoots registry Q packet :=
  packet_footprint_member registry Q packet ref
    (WHIRSnapshotReplay.historyFootprint_drop _ _ _ i ref member)

theorem production_cardinality (registry : Public) (Q R : Nat)
    (select : T → Option (RawWHIRKeys.Packet (context registry) Q))
    (source : Source cap T) (counted : WHIRSourceChronology.Counts Q source)
    (free : FreeAnnouncements R source) (log : PublicLog) (budget : log.length ≤ Q) :
    (policy registry Q select source log).card ≤ (Q+1)*(R+(Q+1)*(productionDepth+1)) :=
  cardinality registry Q productionDepth R (production_profileBound registry) select source counted free log budget

theorem firstReply_sound (C : PrimitiveOracle) (log : PublicLog)
    (authentic : AuthenticLog C log) (n : Node) (d : Digest32)
    (found : firstReply log n = some d) : C n = d :=
  authentic n d (List.mem_reverse.mp (PublicMerkleLog.lookup_mem found))

theorem firstReply_cons_preserves (log : PublicLog) (entry : Node × Digest32)
    (n : Node) (d : Digest32) (found : firstReply log n = some d) :
    firstReply (entry :: log) n = some d := by
  unfold firstReply at *
  rw [List.reverse_cons]
  generalize log.reverse = past at *
  induction past with
  | nil => simp [PublicMerkleLog.lookup] at found
  | cons e rest ih =>
    simp only [List.cons_append,PublicMerkleLog.lookup] at *
    split at found
    · rename_i same
      simp [same,found]
    · rename_i different
      simp only [different,↓reduceIte]
      exact ih found

theorem partialEval_sound (C : PrimitiveOracle) (log : PublicLog)
    (authentic : AuthenticLog C log) {N : Nat} (program : Computation T N) (value : T)
    (found : partialEval log program = some value) :
    TypedOracleCompiler.Sampling.eval C program = value := by
  induction program with
  | ret r => exact Option.some.inj found
  | draw n next ih =>
    cases hit : firstReply log n with
    | none => simp [partialEval,hit] at found
    | some d =>
      have same := firstReply_sound C log authentic n d hit
      simpa only [TypedOracleCompiler.Sampling.eval,same] using
        ih d (by simpa only [partialEval,hit,Option.bind_some] using found)

theorem queryReply_sound (C : PrimitiveOracle) (iv : Digest32) (log : PublicLog)
    (authentic : AuthenticLog C log) (q : Query) (d : Digest32)
    (found : queryReply iv log q = some d) : realAnswer C iv q = d := by
  rw [← queryCalls_eval]
  exact partialEval_sound C log authentic _ d found

theorem partialEval_complete (C : PrimitiveOracle) (log : PublicLog)
    (authentic : AuthenticLog C log) {N : Nat} (program : Computation T N)
    (available : ∀ entry ∈ toLog (TypedOracleCompiler.Sampling.execute C program).2, entry ∈ log) :
    partialEval log program = some (TypedOracleCompiler.Sampling.eval C program) := by
  induction program with
  | ret => rfl
  | draw n next ih =>
    have hit : firstReply log n = some (C n) :=
      PublicMerkleLog.lookup_authentic_member C log.reverse
        (fun m d hm => authentic m d (List.mem_reverse.mp hm))
        (List.mem_reverse.mpr (available (n,C n) (by
          simp [toLog,TypedOracleCompiler.Sampling.execute])))
    simp only [partialEval,hit,Option.bind_some,TypedOracleCompiler.Sampling.eval]
    apply ih
    intro entry member
    exact available entry (List.mem_cons_of_mem _ member)

/-- All cells used here come from the actual all-C compiler. This completeness
lemma is useful when transporting an actual completed prefix into the policy. -/
theorem partialPrefix_full (C : PrimitiveOracle) (iv : Digest32) (log : PublicLog)
    (authentic : AuthenticLog C log) (source : Source cap T) (Q : Nat)
    (counted : WHIRSourceChronology.Counts Q source)
    (available : ∀ entry ∈ primitiveLog C iv (erase source) Q ((erase_counted source Q).mpr counted),
      entry ∈ log) :
    partialPrefix iv log source =
      completedPrefix (runReal C iv (WHIRSourceChronology.compile source)).view.result := by
  induction source generalizing Q with
  | done => rfl
  | commit root next ih =>
    have inner := ih Q counted available
    simpa [partialPrefix,WHIRSourceChronology.compile,map_real,mapExecution,
      WHIRSourceChronology.prepend,completedPrefix,prependPrefix] using
      congrArg (prependPrefix (.commit root)) inner
  | claims p entry request next ih =>
    have inner := ih Q counted available
    simpa [partialPrefix,WHIRSourceChronology.compile,map_real,mapExecution,
      WHIRSourceChronology.prepend,completedPrefix,prependPrefix] using
      congrArg (prependPrefix (.claims p entry request)) inner
  | ask q next ih =>
    simp only [erase,primitiveLog,PublicCompressionProgram.compile,
      TypedOracleCompiler.Sampling.execute_pad,TypedOracleCompiler.Sampling.execute_bind,
      execute_mapResult,toLog,List.map_append,queryCalls_eval] at available
    have answer : queryReply iv log q = some (realAnswer C iv q) := by
      rw [queryReply,← queryCalls_eval C iv q]
      apply partialEval_complete C log authentic
      intro entry member
      exact available entry (List.mem_append_left _ member)
    have inner := ih (realAnswer C iv q) (Q-q.cost) (counted.2 _) (by
      intro entry member
      exact available entry (List.mem_append_right _ member))
    simpa [partialPrefix,answer,WHIRSourceChronology.compile,runReal,map_real,mapExecution,
      WHIRSourceChronology.prepend,DuplexModeGame.prepend,completedPrefix,prependPrefix] using
      congrArg (prependPrefix (.answer q (realAnswer C iv q))) inner

theorem primitiveLog_map (C : PrimitiveOracle) (iv : Digest32) (f : T → U)
    (program : Program T) (Q : Nat) (counted : DuplexModeGame.Counts Q program) :
    primitiveLog C iv (WHIRSourceChronology.map f program) Q ((map_counted f program Q).mpr counted) =
      primitiveLog C iv program Q counted := by
  induction program generalizing Q with
  | done => rfl
  | ask q next ih =>
    simp only [WHIRSourceChronology.map,primitiveLog,PublicCompressionProgram.compile,
      TypedOracleCompiler.Sampling.execute_pad,TypedOracleCompiler.Sampling.execute_bind,
      execute_mapResult,toLog,List.map_append,queryCalls_eval]
    exact congrArg (_ ++ ·) (ih (realAnswer C iv q) (Q-q.cost) (counted.2 _))

/-- Source event instrumentation does not change a single full-C trace cell. -/
theorem primitiveLog_source (C : PrimitiveOracle) (iv : Digest32)
    (source : Source cap T) (Q : Nat) (counted : WHIRSourceChronology.Counts Q source) :
    primitiveLog C iv (WHIRSourceChronology.compile source) Q ((compile_counted source Q).mpr counted) =
      primitiveLog C iv (erase source) Q ((erase_counted source Q).mpr counted) := by
  induction source generalizing Q with
  | done => rfl
  | commit root next ih =>
    change primitiveLog C iv (WHIRSourceChronology.map _ _) _ _ = _
    rw [primitiveLog_map]
    exact ih Q counted
  | claims p entry request next ih =>
    change primitiveLog C iv (WHIRSourceChronology.map _ _) _ _ = _
    rw [primitiveLog_map]
    exact ih Q counted
  | ask q next ih =>
    simp only [WHIRSourceChronology.compile,erase,primitiveLog,PublicCompressionProgram.compile,
      TypedOracleCompiler.Sampling.execute_pad,TypedOracleCompiler.Sampling.execute_bind,
      execute_mapResult,toLog,List.map_append,queryCalls_eval]
    apply congrArg (_ ++ ·)
    change primitiveLog C iv (WHIRSourceChronology.map _ _) _ _ = _
    rw [primitiveLog_map]
    exact ih (realAnswer C iv q) (Q-q.cost) (counted.2 _)

theorem partialPrefix_full_compiled (C : PrimitiveOracle) (iv : Digest32) (log : PublicLog)
    (authentic : AuthenticLog C log) (source : Source cap T) (Q : Nat)
    (counted : WHIRSourceChronology.Counts Q source)
    (available : ∀ entry ∈ primitiveLog C iv (WHIRSourceChronology.compile source) Q
      ((compile_counted source Q).mpr counted), entry ∈ log) :
    partialPrefix iv log source =
      completedPrefix (runReal C iv (WHIRSourceChronology.compile source)).view.result := by
  rw [primitiveLog_source C iv source Q counted] at available
  exact partialPrefix_full C iv log authentic source Q counted available

/-- On any authentic finite C log, the recovered events are a genuine prefix of
the actual source execution, including zero-cost commitments and claim metadata. -/
theorem partialPrefix_real_prefix (C : PrimitiveOracle) (iv : Digest32) (log : PublicLog)
    (authentic : AuthenticLog C log) (source : Source cap T) :
    ∃ suffix, (partialPrefix iv log source).events ++ suffix =
      (runReal C iv (WHIRSourceChronology.compile source)).view.result.events := by
  induction source with
  | done => exact ⟨[],rfl⟩
  | commit root next ih =>
    obtain ⟨suffix,equal⟩ := ih
    exact ⟨suffix,by simpa [partialPrefix,prependPrefix,WHIRSourceChronology.compile,
      map_real,mapExecution,WHIRSourceChronology.prepend] using congrArg (List.cons (.commit root)) equal⟩
  | claims p entry request next ih =>
    obtain ⟨suffix,equal⟩ := ih
    exact ⟨suffix,by simpa [partialPrefix,prependPrefix,WHIRSourceChronology.compile,
      map_real,mapExecution,WHIRSourceChronology.prepend] using congrArg (List.cons (.claims p entry request)) equal⟩
  | ask q next ih =>
    cases answer : queryReply iv log q with
    | none => simp [partialPrefix,answer]
    | some d =>
      have same := queryReply_sound C iv log authentic q d answer
      obtain ⟨suffix,equal⟩ := ih d
      refine ⟨suffix,?_⟩
      simpa [partialPrefix,answer,prependPrefix,WHIRSourceChronology.compile,
        runReal,same,map_real,mapExecution,WHIRSourceChronology.prepend,DuplexModeGame.prepend]
        using congrArg (List.cons (.answer q d)) equal

/-- Exercises actual executable lists: announcement before answer, first reply
on inconsistent repeats, and absence of a root that depends on a later answer. -/
def smoke : IO Unit := do
  let iv := DuplexCompression.parameterIV
  let early : Digest32 := fun _ => 17
  let late : Digest32 := fun _ => 23
  let conflicting : Digest32 := fun _ => 42
  let registry : Public := ⟨iv,iv,fun _ => none,0⟩
  let n := PublicMerkleLog.node iv 0 [] true
  let select : Unit → Option (RawWHIRKeys.Packet (context registry) 2) := fun _ => none
  let source : Source 0 Unit := .commit early (.ask (.primitive .direct n) fun d =>
    .ask (.primitive .direct n) fun repeated => if d = repeated then .commit d (.done ()) else .done ())
  let before := rootList registry 2 select source []
  let after := rootList registry 2 select source [(n,late)]
  let repeated := rootList registry 2 select source [(n,conflicting),(n,late)]
  unless before.contains early && !(before.contains late) do
    throw (IO.userError "root-before-answer / late-root failure")
  unless after.contains early && after.contains late do
    throw (IO.userError "answered commitment missing")
  unless repeated.contains early && repeated.contains late && !(repeated.contains conflicting) do
    throw (IO.userError "inconsistent repetition replaced first reply")
  let layout : WHIRCallerClaims.CallerLayout := .recursion
    ⟨⟨[],[],[],0⟩,[],#[],⟨0,6,9⟩,1⟩
  let headers : Public := ⟨iv,iv,fun _ => some layout,WHIRCallerClaims.callerOutputCap layout⟩
  let coordinate : Coordinate := ⟨⟨iv,iv,[.absorb 0 (WHIRHistory.rootBytes early)]⟩,.output 0⟩
  if valid : DuplexEncoding.Admissible coordinate then
    let budget := pathCost coordinate
    let noFinal : Unit → Option (RawWHIRKeys.Packet (context headers) budget) := fun _ => none
    let request : Source 0 Unit := .ask (.construction coordinate valid) (fun _ => .done ())
    unless (rootList headers budget noFinal request []).contains early do
      throw (IO.userError "canonical header not captured before construction answer")
    let calls := toLog (TypedOracleCompiler.Sampling.execute blake2sOracle (queryCalls iv (.construction coordinate valid))).2
    let prior := (calls.take (calls.length-1)).reverse
    let some terminal := calls.getLast? | throw (IO.userError "empty construction trace")
    unless (queryRoots headers budget prior (.primitive .direct terminal.1)).contains early do
      throw (IO.userError "canonical raw prequery header not captured before terminal answer")
  else throw (IO.userError "header smoke coordinate malformed")
  IO.println s!"source-root-policy smoke: before={before.length}, answered={after.length}, repeated={repeated.length}; productionDepth={productionDepth}"

end Whir.WHIRSourceRootPolicy
