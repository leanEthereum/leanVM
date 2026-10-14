import Whir.SpongefishCurrentPhysicalRootCapture
import Whir.SpongefishCurrentRoundPackets

/-! Partition-level first-mention root capture for the current #607 source,
generic in the raw address function and in the packet partition of raw mixed
keys. A packet key mentions every reference of every one of its block raw keys;
a garbage key mentions the references of its raw key. The captured image is the
existing `freeze` of the ordinary primitive records preceding the first mention,
newest first, exactly as `SpongefishCurrentPhysicalRootCapture.ordinaryLog`.

On atomic packet programs this capture agrees with the raw capture on the joined
raw trace, provided the raw address is uniform across the blocks of a packet
(true for addresses derived from the shared key history) and no ordinary
primitive input is a packet block. The capture never reads the answer of a packet
that mentions the reference, so it is a function of the erased table, and on
compiled counted programs it is the public capture read from the view. -/
namespace Whir.SpongefishCurrentPartitionCapture
open Concrete FiatShamirGame DuplexModeGame TypedOracleCompiler RawOracleCoupling
open PCSBCSChallengeOracle PCSBCSSourceRootReferences PCSBCSMerkleRootCache PublicMerkleLog
open PCSBCSAtomicAllocationTrace
set_option autoImplicit false

abbrev Event (B : Nat) := SpongefishCurrentPhysicalRootCapture.Event B

variable {B : Nat} {Packet : Type} {Block : Packet → Type}

section Address
variable (part : Partition (PublicCompressionCouplingMixed.Key B) Packet Block)
  (addr : PublicCompressionCouplingMixed.Key B → List Reference)

/-- The raw address does not depend on which block of a packet is requested. -/
def Uniform : Prop :=
  ∀ (packet : Packet) (b c : Block packet) (ref : Reference),
    ref ∈ addr (part.encode ⟨packet,b⟩) → ref ∈ addr (part.encode ⟨packet,c⟩)

/-- No ordinary primitive input is recognized as a packet block. -/
def Plain : Prop := ∀ node, part.recognize (.inl node) = none

/-- Ordinary records are garbage keys whose raw key is a primitive input. -/
def ordinaryStep (log : PublicLog) (event : Sigma (part.Answer (D := Digest32))) : PublicLog :=
  match event with
  | ⟨.inl _,_⟩ => log
  | ⟨.inr garbage,answer⟩ =>
    match garbage.val with
    | .inl input => (input,answer) :: log
    | .inr _ => log

/-- Newest first, the same convention as the raw `ordinaryLog`. -/
def ordinaryLog (events : List (Sigma (part.Answer (D := Digest32)))) : PublicLog :=
  events.foldl (ordinaryStep part) []

variable [∀ packet, Fintype (Block packet)]

/-- A packet mentions the references of all its block raw keys; a garbage key
mentions the references of its raw key. -/
noncomputable def paddr : part.Key → List Reference
  | .inl packet => (Finset.univ : Finset (Block packet)).toList.flatMap
      fun b => addr (part.encode ⟨packet,b⟩)
  | .inr garbage => addr garbage.val

theorem mem_paddr_packet (packet : Packet) (ref : Reference) :
    ref ∈ paddr part addr (.inl packet) ↔ ∃ b, ref ∈ addr (part.encode ⟨packet,b⟩) := by
  simp [paddr]

theorem mem_paddr_garbage (garbage : part.Garbage) (ref : Reference) :
    ref ∈ paddr part addr (.inr garbage) ↔ ref ∈ addr garbage.val := Iff.rfl

/-- Partition-level capture: freeze the ordinary prefix before the first mention. -/
noncomputable def pcapture (ref : Reference) {R : Type} {n : Nat}
    (source : Sampling part.Key (part.Answer (D := Digest32)) R n)
    (table : (key : part.Key) → part.Answer (D := Digest32) key) : Option Frozen :=
  (PCSBCSFirstRootDisclosure.firstMention (paddr part addr) ref source table).map
    fun before => freeze (ordinaryLog part before) ref.root ref.shape

end Address

/-- Raw capture on a raw mixed trace with an arbitrary raw address. -/
def rawCapture (addr : PublicCompressionCouplingMixed.Key B → List Reference)
    (ref : Reference) (events : List (Event B)) : Option Frozen :=
  (PCSBCSNativePublicCapture.firstPrefix addr ref events).map
    fun before => freeze (SpongefishCurrentPhysicalRootCapture.ordinaryLog before) ref.root ref.shape

/-- Public capture read from a view: the raw capture of the decoded mixed trace. -/
def viewCapture {R : Type} (addr : PublicCompressionCouplingMixed.Key B → List Reference)
    (iv : Digest32) (ref : Reference) (view : View R) : Option Frozen :=
  rawCapture addr ref (PCSBCSNativePublicCapture.mixedTrace B iv [] view.observations)

section Raw
variable (part : Partition (PublicCompressionCouplingMixed.Key B) Packet Block)
  (addr : PublicCompressionCouplingMixed.Key B → List Reference)
variable [∀ packet, Fintype (Block packet)]

theorem mem_paddr_allocation (uniform : Uniform part addr)
    (table : (key : part.Key) → part.Answer (D := Digest32) key)
    (raw : PublicCompressionCouplingMixed.Key B) (ref : Reference) :
    ref ∈ paddr part addr (allocation part table raw).1 ↔ ref ∈ addr raw := by
  unfold allocation
  split
  · rename_i block found
    have encoded := part.encode_recognize raw block found
    rw [mem_paddr_packet]
    constructor
    · rintro ⟨b,member⟩
      rw [← encoded]
      exact uniform block.1 b block.2 ref member
    · intro member
      refine ⟨block.2,?_⟩
      rw [← encoded] at member
      exact member
  · exact Iff.rfl

theorem firstPrefix_allocation (uniform : Uniform part addr)
    (table : (key : part.Key) → part.Answer (D := Digest32) key)
    (ref : Reference) (events : List (Event B)) :
    PCSBCSNativePublicCapture.firstPrefix (paddr part addr) ref
        (events.map fun event => allocation part table event.1) =
      (PCSBCSNativePublicCapture.firstPrefix addr ref events).map
        (List.map fun event => allocation part table event.1) := by
  induction events with
  | nil => rfl
  | cons event rest ih =>
    by_cases hit : ref ∈ addr event.1
    · have mapped : ref ∈ paddr part addr (allocation part table event.1).1 :=
        (mem_paddr_allocation part addr uniform table event.1 ref).mpr hit
      simp only [List.map_cons,PCSBCSNativePublicCapture.firstPrefix,hit,mapped,
        ↓reduceIte,Option.map_some,List.map_nil]
    · have mapped : ref ∉ paddr part addr (allocation part table event.1).1 :=
        fun member => hit ((mem_paddr_allocation part addr uniform table event.1 ref).mp member)
      simp only [List.map_cons,PCSBCSNativePublicCapture.firstPrefix,hit,mapped,
        ↓reduceIte,ih,Option.map_map]
      rfl

omit [∀ packet, Fintype (Block packet)] in
theorem join_garbage (table : (key : part.Key) → part.Answer (D := Digest32) key)
    (raw : PublicCompressionCouplingMixed.Key B) (missing : part.recognize raw = none) :
    part.join table raw = table (.inr ⟨raw,missing⟩) := by
  unfold Partition.join
  split
  · rename_i block found
    rw [missing] at found
    cases found
  · rfl

omit [∀ packet, Fintype (Block packet)] in
theorem ordinaryStep_allocation (plain : Plain part)
    (table : (key : part.Key) → part.Answer (D := Digest32) key)
    (log : PublicLog) (event : Event B) (correct : event.2 = part.join table event.1) :
    ordinaryStep part log (allocation part table event.1) =
      SpongefishCurrentPhysicalRootCapture.ordinaryStep log event := by
  rcases event with ⟨raw,answer⟩
  dsimp only at correct
  cases raw with
  | inl node =>
    rw [correct,join_garbage part table (.inl node) (plain node)]
    unfold allocation
    split
    · rename_i block found
      rw [plain node] at found
      cases found
    · rfl
  | inr key =>
    unfold allocation
    split <;> rfl

omit [∀ packet, Fintype (Block packet)] in
theorem ordinaryLog_allocation (plain : Plain part)
    (table : (key : part.Key) → part.Answer (D := Digest32) key)
    (events : List (Event B)) (correct : ∀ event ∈ events, event.2 = part.join table event.1) :
    ordinaryLog part (events.map fun event => allocation part table event.1) =
      SpongefishCurrentPhysicalRootCapture.ordinaryLog events := by
  unfold ordinaryLog SpongefishCurrentPhysicalRootCapture.ordinaryLog
  generalize ([] : PublicLog) = log
  induction events generalizing log with
  | nil => rfl
  | cons event rest ih =>
    simp only [List.map_cons,List.foldl_cons]
    rw [ordinaryStep_allocation part plain table log event (correct event List.mem_cons_self)]
    exact ih (fun other member => correct other (List.mem_cons_of_mem _ member)) _

/-- Atomic packet programs: the partition capture is the raw capture on the
joined raw trace. -/
theorem pcapture_raw (uniform : Uniform part addr) (plain : Plain part) (ref : Reference)
    {R : Type} {n : Nat} (prog : Sampling (PublicCompressionCouplingMixed.Key B) (fun _ => Digest32) R n)
    (table : (key : part.Key) → part.Answer (D := Digest32) key) :
    pcapture part addr ref (Atomic.program part prog) table =
      rawCapture addr ref (Sampling.execute (part.join table) prog).2 := by
  unfold pcapture rawCapture
  rw [PCSBCSNativePublicCapture.firstPrefix_execute,execute_program,
    firstPrefix_allocation part addr uniform table]
  cases found : PCSBCSNativePublicCapture.firstPrefix addr ref
      (Sampling.execute (part.join table) prog).2 with
  | none => rfl
  | some before =>
    simp only [Option.map_some]
    rw [ordinaryLog_allocation part plain table before fun event member =>
      PCSBCSNativePublicCapture.execute_answers (part.join table) prog event
        (PCSBCSNativePublicCapture.firstPrefix_subset addr ref _ before found event member)]

end Raw

section Erased
variable (part : Partition (PublicCompressionCouplingMixed.Key B) Packet Block)
  (addr : PublicCompressionCouplingMixed.Key B → List Reference)

open Classical in
/-- Ghost completion of the erased packet entry by zero blocks. -/
noncomputable def otherTable (packet : Packet)
    (other : PCSStateRestoration.Latent.Erased (part.Answer (D := Digest32)) (.inl packet)) :
    (key : part.Key) → part.Answer (D := Digest32) key :=
  PCSStateRestoration.Latent.fill (.inl packet) other (fun _ => 0)

variable [∀ packet, Fintype (Block packet)]

/-- A packet that mentions the reference is never read before the capture. -/
theorem pcapture_erased (packet : Packet) (ref : Reference)
    (mentioned : ref ∈ paddr part addr (.inl packet)) {R : Type} {n : Nat}
    (source : Sampling part.Key (part.Answer (D := Digest32)) R n)
    (table : (key : part.Key) → part.Answer (D := Digest32) key) :
    pcapture part addr ref source
        (otherTable part packet (PCSStateRestoration.Latent.erase (.inl packet) table)) =
      pcapture part addr ref source table := by
  classical
  unfold otherTable pcapture
  rw [PCSStateRestoration.Latent.fill_erase,
    PCSBCSFirstRootDisclosure.first_mention_answer_independent (paddr part addr)
      (.inl packet) ref mentioned source table]

end Erased

section View
variable (part : Partition (PublicCompressionCouplingMixed.Key B) Packet Block)
  (addr : PublicCompressionCouplingMixed.Key B → List Reference)
variable [∀ packet, Fintype (Block packet)]

/-- Compiled counted programs: the partition capture is the public capture read
from the view of the atomic program, for every partition-level table. -/
theorem pcapture_view (uniform : Uniform part addr) (plain : Plain part)
    (iv : Digest32) (ref : Reference) {R : Type} (program : Program R) (remaining : Nat)
    (limit : remaining ≤ B) (counted : Counts remaining program)
    (table : (key : part.Key) → part.Answer (D := Digest32) key) :
    let source := Atomic.program part
      (PublicCompressionCouplingMixed.compile B iv [] program remaining limit counted)
    pcapture part addr ref source table = viewCapture addr iv ref (Sampling.eval table source) := by
  dsimp only
  have joined : PublicCompressionCouplingMixed.oracle
      ((PublicCompressionCouplingMixed.tableEquiv B) (part.join table)).1
      ((PublicCompressionCouplingMixed.tableEquiv B) (part.join table)).2 = part.join table :=
    (PublicCompressionCouplingMixed.tableEquiv B).left_inv (part.join table)
  rw [pcapture_raw part addr uniform plain ref _ table,viewCapture,Atomic.eval_program,← joined,
    PCSBCSNativePublicCapture.mixedTrace_actual]

/-- The builder's capture from the erased table is the public capture of the
full-table view, whenever the erased packet mentions the reference. -/
theorem pcapture_erased_view (uniform : Uniform part addr) (plain : Plain part)
    (iv : Digest32) (packet : Packet) (ref : Reference)
    (mentioned : ref ∈ paddr part addr (.inl packet)) {R : Type} (program : Program R)
    (remaining : Nat) (limit : remaining ≤ B) (counted : Counts remaining program)
    (table : (key : part.Key) → part.Answer (D := Digest32) key) :
    let source := Atomic.program part
      (PublicCompressionCouplingMixed.compile B iv [] program remaining limit counted)
    pcapture part addr ref source
        (otherTable part packet (PCSStateRestoration.Latent.erase (.inl packet) table)) =
      viewCapture addr iv ref (Sampling.eval table source) := by
  dsimp only
  rw [pcapture_erased part addr packet ref mentioned,
    pcapture_view part addr uniform plain iv ref program remaining limit counted table]

end View

/-- The current round partition recognizes no ordinary primitive input. -/
theorem round_plain (p : ParameterBounds.Profile) (Q : Nat) (iv : Digest32)
    (grinding : Fin (ParameterBounds.config p).folds.size → Fin 64) (boundary : Nat) :
    Plain (SpongefishCurrentRoundPackets.partition p Q iv grinding boundary) := by
  intro node
  simp [SpongefishCurrentRoundPackets.partition,partitionOfInjection,
    SpongefishCurrentRoundPackets.blockKey]

#print axioms mem_paddr_allocation
#print axioms firstPrefix_allocation
#print axioms ordinaryLog_allocation
#print axioms pcapture_raw
#print axioms pcapture_erased
#print axioms pcapture_view
#print axioms pcapture_erased_view
#print axioms round_plain
end Whir.SpongefishCurrentPartitionCapture
