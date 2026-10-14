import Whir.PCSBCSSourceRootReferencesBudget
import Whir.PCSBCSSourceCoordinateDecoderSource
import Whir.PCSBCSSourceSavedRecordProvenance
import Whir.AnchoredHeaderRoots

/-! Public-byte-only reference recovery. A terminal query pays one physical
query, not its ancestry, so the conservative target cap is Q*(Q+1). -/
set_option autoImplicit false
namespace Whir.PCSBCSSourcePrimitiveRootBudget
open Concrete Protocol FiatShamirGame DuplexPublicSimulator DuplexFraming
open PCSBCSMerkleRootCache PCSBCSSourceRootReferences

variable (p : ParameterBounds.Profile) (Q boundary : Nat)
    (registry : AnchoredHeaderRoots.Public)

/-- The boundary counts chronological frames, not newest-first log records. -/
def entry (key : Coordinate) (boundary : Nat) : FramedHistory :=
  {key.history with frames := key.history.frames.take boundary}

/-- Anchors use the fixed public registry even when opening decoding fails. -/
def anchorReferences (key : Coordinate) : List Reference :=
  match key.terminal with
  | .output _ =>
    match AnchoredHeaderRoots.fromHistory registry key.history with
    | none => []
    | some header => [⟨header.root,initialShape header.shape⟩]
  | _ => []

theorem anchorReferences_length (key : Coordinate) :
    (anchorReferences registry key).length ≤ 1 := by
  unfold anchorReferences
  cases key.terminal <;> try simp
  split <;> simp

/-- Conservative opening admission needs no caller layout or answer getter.
Every root and shape is decoded or selected by the actual source role parser. -/
def openingReferencesFromEntry (callerEntry : FramedHistory) (key : Coordinate) : Option (List Reference) := do
  let saved ← PCSBCSSourceSavedRecordDecoder.decode p callerEntry
  let messages ← parsePendingKey p callerEntry key
  if phaseRolesAdmitted (ParameterBounds.config p) messages then
    pure (⟨saved.root,initialShape saved.shape⟩ ::
      phaseReferences (ParameterBounds.config p) messages)
  else none

def openingReferences (key : Coordinate) : Option (List Reference) :=
  openingReferencesFromEntry p (entry key boundary) key

theorem openingReferences_bound (key : Coordinate) (refs : List Reference)
    (accepted : openingReferences p boundary key = some refs) :
    refs.length ≤ pathCost key := by
  unfold openingReferences openingReferencesFromEntry at accepted
  cases saved : PCSBCSSourceSavedRecordDecoder.decode p (entry key boundary) with
  | none => simp [saved] at accepted
  | some record =>
    simp only [saved] at accepted
    dsimp only [Bind.bind,Option.bind] at accepted
    cases pending : parsePendingKey p (entry key boundary) key with
    | none => simp [pending] at accepted
    | some messages =>
      simp only [pending] at accepted
      dsimp only [Bind.bind,Option.bind,Pure.pure] at accepted
      split at accepted
      · cases accepted
        obtain ⟨nonempty,admitted,block,same⟩ :=
          parsePendingKey_admitted p (entry key boundary) key messages pending
        rw [same]
        simpa only [List.length_cons,Nat.add_comm] using
          complete_path_reference_bound p (entry key boundary) messages nonempty admitted block
      · contradiction

/-- Native acceptance itself supplies saved-record provenance; no record-equality
or metadata reconstruction premise is needed. -/
theorem openingReferencesFromEntry_native (layout : WHIRCallerClaims.CallerLayout)
    (saved : AnchoredHeaderCodec.Record) (answers : Coordinate → Digest32)
    (callerEntry : FramedHistory) (key : Coordinate) (refs : List Reference)
    (accepted : parseReferences p layout saved callerEntry answers key = some refs) :
    openingReferencesFromEntry p callerEntry key = some refs := by
  obtain ⟨valid,profile,claims,messages,caller,pending,roles,same⟩ :=
    parseReferences_admitted p layout saved callerEntry answers key refs accepted
  have decoded := PCSBCSSourceSavedRecordProvenance.decode_saved_profileShape p layout saved
    callerEntry answers claims caller valid profile
  simp only [openingReferencesFromEntry,decoded]
  dsimp only [Bind.bind,Option.bind]
  simp only [pending]
  dsimp only [Bind.bind,Option.bind,Pure.pure]
  rw [ite_eq_left roles]
  exact congrArg some same.symm

theorem openingReferences_native (layout : WHIRCallerClaims.CallerLayout)
    (saved : AnchoredHeaderCodec.Record) (answers : Coordinate → Digest32)
    (key : Coordinate) (refs : List Reference)
    (accepted : parseReferences p layout saved (entry key boundary) answers key = some refs) :
    openingReferences p boundary key = some refs :=
  openingReferencesFromEntry_native p layout saved answers (entry key boundary) key refs accepted

/-- Only the strictly earlier newest-first public log and the actual input are
read. Recovered histories retain their chronological frame ordering. -/
def references (queryPrefix : PublicLog) (input : Node) : List Reference :=
  ((PCSBCSSourceCoordinateDecoder.recover Q PCSBCSSourceCoordinateDecoder.seedIV queryPrefix input).map
    (fun key => anchorReferences registry key ++
      (openingReferences p boundary key).getD [])).getD []

theorem references_native (queryPrefix : PublicLog) (input : Node) (key : Coordinate)
    (recovered : PCSBCSSourceCoordinateDecoder.recover Q
      PCSBCSSourceCoordinateDecoder.seedIV queryPrefix input = some key)
    (layout : WHIRCallerClaims.CallerLayout) (saved : AnchoredHeaderCodec.Record)
    (answers : Coordinate → Digest32) (refs : List Reference)
    (accepted : parseReferences p layout saved (entry key boundary) answers key = some refs) :
    ∀ ref ∈ refs, ref ∈ references p Q boundary registry queryPrefix input := by
  have parsed := openingReferences_native p boundary layout saved answers key refs accepted
  simp only [references,recovered,Option.map_some,Option.getD_some,parsed]
  intro ref member
  exact List.mem_append_right _ member

theorem references_le (queryPrefix : PublicLog) (input : Node) :
    (references p Q boundary registry queryPrefix input).length ≤ Q+1 := by
  unfold references
  cases recovered : PCSBCSSourceCoordinateDecoder.recover Q
      PCSBCSSourceCoordinateDecoder.seedIV queryPrefix input with
  | none => simp
  | some key =>
    simp only [Option.map_some,Option.getD_some,List.length_append]
    have anchor := anchorReferences_length registry key
    have opening : ((openingReferences p boundary key).getD []).length ≤ Q := by
      cases parsed : openingReferences p boundary key with
      | none => simp
      | some refs =>
        simp only [Option.getD_some]
        obtain ⟨_,_,_,_,_,_,_,cost⟩ := PCSBCSSourceCoordinateDecoder.recover_sound recovered
        exact (openingReferences_bound p boundary key refs parsed).trans cost
    omega

/-- Newest records are stored first; announcements are accumulated oldest first
and each captures the exact prefix before its primitive reply. -/
def scanAux : PublicLog → List Announcement → List Announcement
  | [], acc => acc
  | (input,_) :: queryPrefix, acc =>
      scanAux queryPrefix (announcements queryPrefix
        (references p Q boundary registry queryPrefix input) ++ acc)

def scan (log : PublicLog) : List Announcement :=
  scanAux p Q boundary registry log []

theorem scanAux_append (log : PublicLog) (left right : List Announcement) :
    scanAux p Q boundary registry log (left ++ right) =
      scanAux p Q boundary registry log left ++ right := by
  induction log generalizing left with
  | nil => rfl
  | cons record queryPrefix ih =>
    rcases record with ⟨input,digest⟩
    simp only [scanAux,← List.append_assoc,ih]

theorem scan_cons (input : Node) (digest : Digest32) (queryPrefix : PublicLog) :
    scan p Q boundary registry ((input,digest)::queryPrefix) =
      scan p Q boundary registry queryPrefix ++
        announcements queryPrefix (references p Q boundary registry queryPrefix input) := by
  simpa only [scan,scanAux,List.nil_append,List.append_nil] using
    scanAux_append p Q boundary registry queryPrefix []
      (announcements queryPrefix (references p Q boundary registry queryPrefix input))

theorem scan_length (log : PublicLog) :
    (scan p Q boundary registry log).length ≤ log.length*(Q+1) := by
  induction log with
  | nil => simp [scan,scanAux]
  | cons record queryPrefix ih =>
    rcases record with ⟨input,digest⟩
    have bound := references_le p Q boundary registry queryPrefix input
    simp only [scan_cons,List.length_append,announcements,List.length_map,List.length_cons]
    rw [Nat.succ_mul]
    omega

theorem register_scan (cache : Registry) (log : PublicLog) (budget : log.length ≤ Q) :
    (registerAll cache (scan p Q boundary registry log)).size ≤
      cache.size + Q*(Q+1) := by
  have entries := registerAll_size_le cache (scan p Q boundary registry log)
  have count := scan_length p Q boundary registry log
  have cost := Nat.mul_le_mul_right (Q+1) budget
  omega

/-- Shape addresses remain distinct in the announcement/cache table. Only the
probability event projects those addresses to digest targets. -/
def targets (log : PublicLog) : Finset Digest32 :=
  ((scan p Q boundary registry log).map (fun a => a.root)).toFinset

theorem targets_grow : PublicMerkleProbability.RootsGrow
    (targets p Q boundary registry) := by
  intro history record root member
  simp only [targets,List.mem_toFinset,List.mem_map] at member ⊢
  obtain ⟨announcement,inOld,same⟩ := member
  rcases record with ⟨input,digest⟩
  rw [scan_cons]
  exact ⟨announcement,List.mem_append_left _ inOld,same⟩

theorem targets_cap (log : PublicLog) (budget : log.length ≤ Q) :
    (targets p Q boundary registry log).card ≤ Q*(Q+1) := by
  have finite := List.toFinset_card_le
    ((scan p Q boundary registry log).map (fun a => a.root))
  have count := scan_length p Q boundary registry log
  have cost := Nat.mul_le_mul_right (Q+1) budget
  simp only [List.length_map] at finite
  exact finite.trans (count.trans cost)

#print axioms openingReferences_native
#print axioms openingReferencesFromEntry_native
#print axioms references_native
#print axioms references_le
#print axioms scan_length
#print axioms register_scan
#print axioms targets_grow
#print axioms targets_cap
end Whir.PCSBCSSourcePrimitiveRootBudget
