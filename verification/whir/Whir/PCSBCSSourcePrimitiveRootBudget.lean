import Whir.PCSBCSSourceRootReferencesBudget
import Whir.PCSBCSSourceCoordinateDecoderSource
import Whir.AnchoredHeaderRoots

/-! A public terminal costs one compression query, not its complete ancestry.
This actual-log scanner includes anchored commitment headers and opening roles,
using the conservative Q*(Q+1) target cap. Shared ancestry is not re-charged. -/
set_option autoImplicit false
namespace Whir.PCSBCSSourcePrimitiveRootBudget
open Concrete Protocol FiatShamirGame DuplexPublicSimulator DuplexFraming
open PCSBCSMerkleRootCache PCSBCSSourceRootReferences

variable (p : ParameterBounds.Profile) (Q : Nat)
    (layout : PublicLog → Node → WHIRCallerClaims.CallerLayout)
    (saved : PublicLog → Node → AnchoredHeaderCodec.Record)
    (entry : PublicLog → Node → FramedHistory)
    (answers : PublicLog → Node → FiatShamirGame.Coordinate → Digest32)
    (headers : PublicLog → Node → AnchoredHeaderRoots.Public)

/-- Commitment-point output blocks register the verifier-selected full image
shape before their reply. The context CV is never treated as a tree root. -/
def anchorReferences (queryPrefix : PublicLog) (input : Node)
    (key : FiatShamirGame.Coordinate) : List Reference :=
  match key.terminal with
  | .output _ =>
    match AnchoredHeaderRoots.fromHistory (headers queryPrefix input) key.history with
    | none => []
    | some header => [⟨header.root,initialShape header.shape⟩]
  | _ => []

theorem anchorReferences_length (queryPrefix : PublicLog) (input : Node)
    (key : FiatShamirGame.Coordinate) :
    (anchorReferences headers queryPrefix input key).length ≤ 1 := by
  unfold anchorReferences
  cases key.terminal <;> try simp
  split <;> simp

/-- Ordinary public inputs and their strictly earlier log, with one source-key
inversion, no history oracle and no future records. Every shape is retained. -/
def references (queryPrefix : PublicLog) (input : Node) : List Reference :=
  ((PCSBCSSourceCoordinateDecoder.recover Q PCSBCSSourceCoordinateDecoder.seedIV queryPrefix input).map
    (fun key => anchorReferences headers queryPrefix input key ++
      (parseReferences p (layout queryPrefix input) (saved queryPrefix input)
        (entry queryPrefix input) (answers queryPrefix input) key).getD [])).getD []

theorem references_le (queryPrefix : PublicLog) (input : Node) :
    (references p Q layout saved entry answers headers queryPrefix input).length ≤ Q+1 := by
  unfold references
  cases recovered : PCSBCSSourceCoordinateDecoder.recover Q
      PCSBCSSourceCoordinateDecoder.seedIV queryPrefix input with
  | none => simp
  | some key =>
    simp only [Option.map_some,Option.getD_some,List.length_append]
    have anchor := anchorReferences_length headers queryPrefix input key
    have opening : ((parseReferences p (layout queryPrefix input) (saved queryPrefix input)
        (entry queryPrefix input) (answers queryPrefix input) key).getD []).length ≤ Q := by
      cases parsed : parseReferences p (layout queryPrefix input) (saved queryPrefix input)
          (entry queryPrefix input) (answers queryPrefix input) key with
      | none => simp
      | some refs =>
        simp only [Option.getD_some]
        obtain ⟨_,_,_,_,_,_,_,cost⟩ := PCSBCSSourceCoordinateDecoder.recover_sound recovered
        exact (parsed_reference_bound p (layout queryPrefix input) (saved queryPrefix input)
          (entry queryPrefix input) (answers queryPrefix input) key refs parsed).trans cost
    omega

/-- Newest records are stored first. The accumulator avoids repeatedly copying
older announcements and captures each exact prefix at its primitive request. -/
def scanAux : PublicLog → List Announcement → List Announcement
  | [], acc => acc
  | (input,_) :: queryPrefix, acc =>
      scanAux queryPrefix (announcements queryPrefix
        (references p Q layout saved entry answers headers queryPrefix input) ++ acc)

def scan (log : PublicLog) : List Announcement :=
  scanAux p Q layout saved entry answers headers log []

theorem scanAux_append (log : PublicLog) (left right : List Announcement) :
    scanAux p Q layout saved entry answers headers log (left ++ right) =
      scanAux p Q layout saved entry answers headers log left ++ right := by
  induction log generalizing left with
  | nil => rfl
  | cons record queryPrefix ih =>
    rcases record with ⟨input,digest⟩
    simp only [scanAux,← List.append_assoc,ih]

theorem scan_cons (input : Node) (digest : Digest32) (queryPrefix : PublicLog) :
    scan p Q layout saved entry answers headers ((input,digest)::queryPrefix) =
      scan p Q layout saved entry answers headers queryPrefix ++
        announcements queryPrefix (references p Q layout saved entry answers headers queryPrefix input) := by
  simpa only [scan,scanAux,List.nil_append,List.append_nil] using
    scanAux_append p Q layout saved entry answers headers queryPrefix []
      (announcements queryPrefix (references p Q layout saved entry answers headers queryPrefix input))

theorem scan_length (log : PublicLog) :
    (scan p Q layout saved entry answers headers log).length ≤ log.length*(Q+1) := by
  induction log with
  | nil => simp [scan,scanAux]
  | cons record queryPrefix ih =>
    rcases record with ⟨input,digest⟩
    have bound := references_le p Q layout saved entry answers headers queryPrefix input
    simp only [scan_cons,List.length_append,announcements,List.length_map,List.length_cons]
    rw [Nat.succ_mul]
    omega

/-- Shared physical queries bound the actual public log. No Q+1 target cap or
one-opening-root-per-terminal premise is used. Adaptive anchors are included. -/
theorem register_scan (registry : Registry) (log : PublicLog) (budget : log.length ≤ Q) :
    (registerAll registry (scan p Q layout saved entry answers headers log)).size ≤
      registry.size + Q*(Q+1) := by
  have entries := registerAll_size_le registry (scan p Q layout saved entry answers headers log)
  have count := scan_length p Q layout saved entry answers headers log
  have cost : log.length*(Q+1) ≤ Q*(Q+1) := Nat.mul_le_mul_right (Q+1) budget
  omega

/-- Digest targets come from classified shape references, not a registry that
conflates equal digests at different verifier-fixed shapes. -/
def targets (log : PublicLog) : Finset Digest32 :=
  ((scan p Q layout saved entry answers headers log).map (fun a => a.root)).toFinset

theorem targets_grow : PublicMerkleProbability.RootsGrow
    (targets p Q layout saved entry answers headers) := by
  intro history record root member
  simp only [targets,List.mem_toFinset,List.mem_map] at member ⊢
  obtain ⟨announcement,inOld,same⟩ := member
  rcases record with ⟨input,digest⟩
  rw [scan_cons]
  exact ⟨announcement,List.mem_append_left _ inOld,same⟩

theorem targets_cap (log : PublicLog) (budget : log.length ≤ Q) :
    (targets p Q layout saved entry answers headers log).card ≤ Q*(Q+1) := by
  have finite := List.toFinset_card_le
    ((scan p Q layout saved entry answers headers log).map (fun a => a.root))
  have count := scan_length p Q layout saved entry answers headers log
  have cost : log.length*(Q+1) ≤ Q*(Q+1) := Nat.mul_le_mul_right (Q+1) budget
  simp only [List.length_map] at finite
  exact finite.trans (count.trans cost)

#print axioms anchorReferences_length
#print axioms references_le
#print axioms scan_length
#print axioms register_scan
#print axioms targets_grow
#print axioms targets_cap
end Whir.PCSBCSSourcePrimitiveRootBudget
