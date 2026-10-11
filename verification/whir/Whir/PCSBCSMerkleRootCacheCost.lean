import Whir.PCSBCSMerkleRootCache
import Whir.PCSBCSMerkleLeafImageCost

/-! Resources are charged to actual announcements, not unique CVs. A fresh
(CV,height,leafWords,occupied) address creates one captured image/suffix table;
identical addresses only perform the registry lookup. Metrics are proof-side,
not extra scans executed by register. Storage counts both full images and raw
suffix arrays, status cells and captured-prefix records. Container-internal
instructions, shared capacities and Rust allocators are not refined here. -/
namespace Whir.PCSBCSMerkleRootCache
open Concrete FiatShamirGame PublicMerkleLog MerkleQueryLogExtraction PCSBCSMerkleQueryLog
open PCSBCSMerkleLeafImages

structure Announcement where
  queryPrefix : PublicLog
  root : Digest32
  shape : Shape

def registerAll (registry : Registry) : List Announcement → Registry
  | [] => registry
  | a::rest => registerAll (register registry a.queryPrefix a.root a.shape) rest

theorem register_size_le (registry : Registry) (log : PublicLog) (root : Digest32)
    (shape : Shape) : (register registry log root shape).size ≤ registry.size+1 := by
  unfold register
  dsimp only
  split
  next => omega
  next => exact Std.ExtHashMap.size_insert_le

theorem registerAll_size_le (registry : Registry) (announcements : List Announcement) :
    (registerAll registry announcements).size ≤ registry.size+announcements.length := by
  induction announcements generalizing registry with
  | nil => simp [registerAll]
  | cons a rest ih =>
    have later := ih (register registry a.queryPrefix a.root a.shape)
    have first := register_size_le registry a.queryPrefix a.root a.shape
    simp only [registerAll,List.length_cons]
    omega

theorem registerAll_wellFormed (registry : Registry) (announcements : List Announcement)
    (valid : WellFormed registry) : WellFormed (registerAll registry announcements) := by
  induction announcements generalizing registry with
  | nil => exact valid
  | cons a rest ih =>
    exact ih _ (register_wellFormed registry a.queryPrefix a.root a.shape valid)

def sumCharges (charge : Registry → Announcement → Nat) (registry : Registry) :
    List Announcement → Nat
  | [] => 0
  | a::rest => charge registry a +
      sumCharges charge (register registry a.queryPrefix a.root a.shape) rest

theorem sumCharges_bound (charge : Registry → Announcement → Nat)
    (registry : Registry) (announcements : List Announcement) (budget : Nat)
    (cap : ∀ r a, a ∈ announcements → charge r a ≤ budget) :
    sumCharges charge registry announcements ≤ announcements.length*budget := by
  induction announcements generalizing registry with
  | nil => simp [sumCharges]
  | cons a rest ih =>
    have first := cap registry a (List.mem_cons_self)
    have later := ih (register registry a.queryPrefix a.root a.shape)
      (fun r b member => cap r b (List.mem_cons_of_mem a member))
    simp only [sumCharges,List.length_cons]
    nlinarith

def extractionCharge (registry : Registry) (a : Announcement) : Nat :=
  match registry[cacheKey a.root a.shape]? with
  | some _ => 0
  | none => 1

def imageSlots (a : Announcement) : Nat :=
  ((imageTable (sourceCells a.queryPrefix a.root a.shape.height a.shape.leafWords a.shape.occupied)).toList.map Array.size).sum

def compactSlots (a : Announcement) : Nat :=
  ((compactTable (sourceCells a.queryPrefix a.root a.shape.height a.shape.leafWords a.shape.occupied)).toList.map Array.size).sum

/-- Actual replay operations, map invocations, fused node visits and codec-input
byte volume; cell/raw-array pushes, materialized slots and a full-image-word
upper charge for zero-prefix traversal. These are data-operation metrics. -/
def operationCharge (registry : Registry) (a : Announcement) : Nat :=
  match registry[cacheKey a.root a.shape]? with
  | some _ => 1
  | none => 2 + (PublicCost.recordsFrom a.queryPrefix a.queryPrefix).2 +
      (countedBuild (records a.queryPrefix)).2 +
      (countedCells canonicalCodec (build (records a.queryPrefix)) a.shape.leafWords a.shape.occupied
        (defaultCell a.shape.leafWords a.shape.occupied) a.shape.height a.root #[]).2 +
      inputByteVolume canonicalCodec (build (records a.queryPrefix)) a.shape.height a.root +
      2*(sourceCells a.queryPrefix a.root a.shape.height a.shape.leafWords a.shape.occupied).size +
      2*imageSlots a + compactSlots a

def wordCharge (registry : Registry) (a : Announcement) : Nat :=
  match registry[cacheKey a.root a.shape]? with
  | some _ => 0
  | none => imageSlots a + compactSlots a

def cellCharge (registry : Registry) (a : Announcement) : Nat :=
  match registry[cacheKey a.root a.shape]? with
  | some _ => 0
  | none => (sourceCells a.queryPrefix a.root a.shape.height a.shape.leafWords a.shape.occupied).size

def prefixCharge (registry : Registry) (a : Announcement) : Nat :=
  match registry[cacheKey a.root a.shape]? with
  | some _ => 0
  | none => a.queryPrefix.length

def operationBudget (Q N leafWords occupied : Nat) : Nat :=
  2+Q*(20000*(Q+2)*(Q+2)+1)+Q+4*N+2*N*(64*(Q+2))+2*N*leafWords+N*occupied

theorem cached_charges (registry : Registry) (a : Announcement) (frozen : Frozen)
    (known : registry[cacheKey a.root a.shape]? = some frozen) :
    operationCharge registry a = 1 ∧ extractionCharge registry a = 0 ∧
      wordCharge registry a = 0 ∧ cellCharge registry a = 0 ∧ prefixCharge registry a = 0 := by
  simp [operationCharge,extractionCharge,wordCharge,cellCharge,prefixCharge,known]

theorem announcement_charges (registry : Registry) (a : Announcement) (Q N leafWords occupied : Nat)
    (queryCap : a.queryPrefix.length ≤ Q) (rowCap : 2^a.shape.height ≤ N)
    (leafCap : a.shape.leafWords ≤ leafWords) (widthCap : a.shape.occupied ≤ occupied)
    (fits : a.shape.occupied ≤ a.shape.leafWords) :
    operationCharge registry a ≤ operationBudget Q N leafWords occupied ∧
      extractionCharge registry a ≤ 1 ∧ wordCharge registry a ≤ N*(leafWords+occupied) ∧
      cellCharge registry a ≤ N ∧ prefixCharge registry a ≤ Q := by
  have resources := actual_resource_contract a.queryPrefix a.root a.shape.height
    a.shape.leafWords Q (2^a.shape.height) queryCap rfl
  obtain ⟨saturation,inserts,_index,_payload,_visits,_rows,_words⟩ := resources
  have visits := source_visit_budget a.queryPrefix a.root a.shape.height a.shape.leafWords a.shape.occupied
  have bytes := public_input_byte_volume a.queryPrefix a.root a.shape.height Q N queryCap rowCap
  have cells := sourceCells_size a.queryPrefix a.root a.shape.height a.shape.leafWords a.shape.occupied
  have images := image_word_slots a.queryPrefix a.root a.shape.height a.shape.leafWords a.shape.occupied
  have suffix := compact_word_slots a.queryPrefix a.root a.shape.height a.shape.leafWords a.shape.occupied fits
  have imageCap : imageSlots a ≤ N*leafWords := images.trans (Nat.mul_le_mul rowCap leafCap)
  have suffixCap : compactSlots a ≤ N*occupied := suffix.trans (Nat.mul_le_mul rowCap widthCap)
  unfold operationCharge extractionCharge wordCharge cellCharge prefixCharge
  cases registry[cacheKey a.root a.shape]? with
  | some frozen => simp only []; unfold operationBudget; omega
  | none =>
    simp only []
    refine ⟨?_,by omega,?_,by omega,queryCap⟩
    · unfold operationBudget
      rw [cells]
      nlinarith
    · nlinarith [imageCap,suffixCap]

/-- Every configuration announcement is counted, even if all CVs coincide. -/
theorem registration_resources (registry : Registry) (announcements : List Announcement)
    (Q N leafWords occupied : Nat)
    (caps : ∀ a ∈ announcements, a.queryPrefix.length ≤ Q ∧
      2^a.shape.height ≤ N ∧ a.shape.leafWords ≤ leafWords ∧
      a.shape.occupied ≤ occupied ∧ a.shape.occupied ≤ a.shape.leafWords) :
    (registerAll registry announcements).size ≤ registry.size+announcements.length ∧
    sumCharges operationCharge registry announcements ≤
      announcements.length*operationBudget Q N leafWords occupied ∧
    sumCharges extractionCharge registry announcements ≤ announcements.length ∧
    sumCharges wordCharge registry announcements ≤ announcements.length*(N*(leafWords+occupied)) ∧
    sumCharges cellCharge registry announcements ≤ announcements.length*N ∧
    sumCharges prefixCharge registry announcements ≤ announcements.length*Q := by
  have charged : ∀ r a, a ∈ announcements →
      operationCharge r a ≤ operationBudget Q N leafWords occupied ∧
      extractionCharge r a ≤ 1 ∧ wordCharge r a ≤ N*(leafWords+occupied) ∧
      cellCharge r a ≤ N ∧ prefixCharge r a ≤ Q := by
    intro r a member
    obtain ⟨queryCap,rowCap,leafCap,widthCap,fits⟩ := caps a member
    exact announcement_charges r a Q N leafWords occupied queryCap rowCap leafCap widthCap fits
  refine ⟨registerAll_size_le registry announcements,
    sumCharges_bound operationCharge registry announcements _
      (fun r a member => (charged r a member).1),?_,
    sumCharges_bound wordCharge registry announcements _
      (fun r a member => (charged r a member).2.2.1),
    sumCharges_bound cellCharge registry announcements _
      (fun r a member => (charged r a member).2.2.2.1),
    sumCharges_bound prefixCharge registry announcements _
      (fun r a member => (charged r a member).2.2.2.2)⟩
  simpa only [Nat.mul_one] using sumCharges_bound extractionCharge registry announcements 1
    (fun r a member => (charged r a member).2.1)

end Whir.PCSBCSMerkleRootCache
