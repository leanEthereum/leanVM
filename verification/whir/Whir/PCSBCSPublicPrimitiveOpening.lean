import Whir.PCSBCSWholeNativeCaptureTransport
import Whir.PCSBCSNativePublicCapture
import Whir.PCSBCSObservedPrimitiveExtension

/-! Finite public refinement of every retained historical native opening.
The zero extension is used only on observed inputs; unobserved oracle values
may differ arbitrarily. No global seed equality or cryptographic exclusion is
an assumption of the refinement. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Whir.PCSBCSPublicPrimitiveOpening
open Concrete Protocol FiatShamirGame DuplexFraming DuplexModeGame TypedOracleCompiler
open RawOracleCoupling PCSBCSChallengeOracle PublicMerkleLog
open MerkleTransport WHIRPhysicalVerifier PCSBCSSourceRootReferences
open PCSBCSCapturedNativeReplyBridge
open PCSStateRestoration.Latent

/-- A genuinely public finite oracle, with a fixed zero fallback. -/
def publicSeed {R : Type} (view : View R) : PrimitiveOracle :=
  PCSBCSObservedPrimitiveExtension.extension (fun _ => DuplexRefinement.zeroDigest)
    (DuplexPublicSimulator.finalLog [] view.observations)

noncomputable def publicOrdinaryLog {R : Type} (B : Nat) (iv : Digest32)
    (view : View R) : PublicLog :=
  (PCSBCSNativePublicCapture.mixedTrace B iv [] view.observations).foldl
    (fun log event => PCSBCSNativePublicCapture.rawOrdinary event ++ log) []

/-- The decoder is the literal-byte constant-address decoder, not caller
answers or a private registry. Profile and entry boundary are current metadata. -/
noncomputable def publicBadOpening {R : Type} (B : Nat) (iv : Digest32)
    {p : ParameterBounds.Profile} {boundary : Nat} (ref : Reference)
    (view : View R) (opening : QueryOpening p) : Prop :=
  PublicMerkleBinding.OpenPrimitiveBad (publicSeed view)
    (PCSBCSNativePublicCapture.publicLog
      (PCSBCSCapturedSourceTransport.address (p := p) (Q := B) (iv := iv)
        (boundary := boundary)) ref view) opening.root opening.result.paths
theorem planFrom_authentic (C : PrimitiveOracle) (cv : Digest32) (count : Nat)
    (bs : List (List Byte)) : AuthenticLog C (planFrom C cv count bs) := by
  induction bs generalizing cv count with
  | nil => intro n d member; simp [planFrom] at member
  | cons b rest ih =>
    cases rest with
    | nil =>
      intro n d member
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (List.mem_singleton.mp member)
      rfl
    | cons next rest =>
      intro n d member
      rcases List.mem_cons.mp member with equal | later
      · obtain ⟨rfl,rfl⟩ := Prod.mk.inj equal
        rfl
      · exact ih _ _ n d later


/-- Agreement on just one finite adaptive compression plan suffices. -/
theorem planFrom_locality (C D : PrimitiveOracle) (cv : Digest32) (count : Nat)
    (bs : List (List Byte))
    (agree : ∀ e ∈ planFrom C cv count bs, D e.1 = C e.1) :
    planFrom D cv count bs = planFrom C cv count bs ∧
      run (fun n => some (D n)) cv count bs = run (fun n => some (C n)) cv count bs := by
  induction bs generalizing cv count with
  | nil => exact ⟨rfl,rfl⟩
  | cons b rest ih =>
    cases rest with
    | nil =>
      have equal := agree _ (List.mem_cons_self :
        (node cv count b true,C (node cv count b true)) ∈ planFrom C cv count [b])
      constructor <;> simp only [planFrom,run,equal]
    | cons next rest =>
      have equal := agree _ (List.mem_cons_self :
        (node cv count b false,C (node cv count b false)) ∈ planFrom C cv count (b :: next :: rest))
      obtain ⟨plans,runs⟩ := ih (C (node cv count b false)) (count+b.length)
        (fun e member => agree e (List.mem_cons_of_mem _ member))
      constructor
      · simp only [planFrom,equal,plans]
      · simpa only [run,equal,Option.bind_eq_bind,Option.bind_some] using runs

theorem hash_plan_locality (C D : PrimitiveOracle) (bytes : List Byte)
    (agree : ∀ e ∈ plan C bytes, D e.1 = C e.1) :
    hash D bytes = hash C bytes ∧ plan D bytes = plan C bytes := by
  obtain ⟨plans,runs⟩ := planFrom_locality C D DuplexCompression.parameterIV 0 (chunks bytes) agree
  exact ⟨congrArg (fun result => result.getD DuplexCompression.parameterIV) runs,plans⟩

/-- Hash equality is required only for the inputs of this particular path. -/
theorem opening_locality (C D : PrimitiveOracle) {q : List Bool}
    (opening : MerkleBinding.Opening (List K) Digest32 q)
    (agree : ∀ bytes ∈ opening.inputs (hashing (hash C)), hash D bytes = hash C bytes) :
    opening.digest (hashing (hash D)) = opening.digest (hashing (hash C)) ∧
      opening.inputs (hashing (hash D)) = opening.inputs (hashing (hash C)) := by
  induction opening with
  | leaf row =>
    exact ⟨agree _ (by simp [MerkleBinding.Opening.inputs,hashing]),rfl⟩
  | node side sibling child ih =>
    obtain ⟨digest,inputs⟩ := ih (fun bytes member => agree bytes (Finset.mem_insert_of_mem member))
    constructor
    · simp only [MerkleBinding.Opening.digest]
      rw [digest]
      exact agree _ (Finset.mem_insert_self _ _)
    · simp only [MerkleBinding.Opening.inputs]
      rw [digest,inputs]
      rfl

/-- Targets depend on the pair codec and public recorded domain, not the hash. -/
theorem target_locality (C D : PrimitiveOracle) (table : Finset (List Byte))
    (root digest : Digest32) :
    MerkleBinding.Target (hashing (hash D)) table root digest ↔
      MerkleBinding.Target (hashing (hash C)) table root digest := Iff.rfl

theorem freshTarget_locality (C D : PrimitiveOracle) (oldLog : PublicLog)
    (target : Digest32) (bytes : List Byte)
    (agree : ∀ e ∈ plan C bytes, D e.1 = C e.1) :
    FreshTarget D oldLog target (plan D bytes) ↔ FreshTarget C oldLog target (plan C bytes) := by
  have plans := (hash_plan_locality C D bytes agree).2
  rw [plans]
  constructor
  · rintro ⟨n,present,absent,hit⟩
    have equal := agree (n,D n) present
    exact ⟨n,by simpa only [equal] using present,absent,by simpa only [equal] using hit⟩
  · rintro ⟨n,present,absent,hit⟩
    have equal := agree (n,C n) present
    exact ⟨n,by simpa only [equal] using present,absent,by simpa only [equal] using hit⟩

theorem openPrimitiveBad_locality (C D : PrimitiveOracle) (oldLog : PublicLog)
    (root : Digest32) (paths : List RawPath)
    (agree : ∀ path ∈ paths, ∀ bytes ∈ path.opening.inputs (hashing (hash C)),
      ∀ e ∈ plan C bytes, D e.1 = C e.1) :
    PublicMerkleBinding.OpenPrimitiveBad D oldLog root paths ↔
      PublicMerkleBinding.OpenPrimitiveBad C oldLog root paths := by
  have inputs : ∀ path ∈ paths,
      path.opening.inputs (hashing (hash D)) = path.opening.inputs (hashing (hash C)) := by
    intro path member
    exact (opening_locality C D path.opening
      (fun bytes present => (hash_plan_locality C D bytes (agree path member bytes present)).1)).2
  unfold PublicMerkleBinding.OpenPrimitiveBad PublicMerkleBinding.PrimitiveFreshHit
  apply or_congr Iff.rfl
  apply exists_congr
  intro path
  apply and_congr_right
  intro member
  rw [inputs path member]
  apply exists_congr
  intro bytes
  apply and_congr_right
  intro present
  have agreement := agree path member bytes present
  rw [(hash_plan_locality C D bytes agreement).1]
  exact and_congr (target_locality C D _ _ _) (freshTarget_locality C D oldLog _ bytes agreement)

section Generic
variable {R : Type} {p : ParameterBounds.Profile} {B : Nat} {iv : Digest32} {boundary : Nat}
    (seed : PrimitiveOracle) (ro : RawKey B → Digest32) (program : Program R)
    (remaining : Nat) (limit : remaining ≤ B) (counted : Counts remaining program)
local notation "part" => EnteredPacket.partition (p := p) (Q := B) (iv := iv) (boundary := boundary)
local notation "source" => (Atomic.program part
  (PublicCompressionCouplingMixed.compile B iv [] program remaining limit counted))
local notation "table" => Partition.split part (PublicCompressionCouplingMixed.oracle seed ro)

theorem publicSeed_observed :
    ∀ purpose input answer,
      (⟨.primitive purpose input,answer⟩ : Observation) ∈
        (Sampling.eval (PublicCompressionCouplingMixed.oracle seed ro)
          (PublicCompressionCouplingMixed.compile B iv [] program remaining limit counted)).observations →
      publicSeed (Sampling.eval (PublicCompressionCouplingMixed.oracle seed ro)
        (PublicCompressionCouplingMixed.compile B iv [] program remaining limit counted)) input = answer := by
  intro purpose input answer member
  apply PCSBCSObservedPrimitiveExtension.extension_of_mem
  · rw [PublicCompressionCouplingMixed.compile_actual]
    exact DuplexPublicSimulator.finalLog_functional ro iv ⟨seed,[]⟩ program remaining limit counted
      (by simp [DuplexPublicSimulator.Functional])
  · exact PCSBCSObservedPrimitiveExtension.primitive_in_finalLog [] _ purpose input answer member

theorem publicOrdinaryLog_actual :
    publicOrdinaryLog B iv (Sampling.eval table source) =
      PCSBCSSourceRootCapture.ordinaryPrefix (Sampling.execute table source).2 := by
  rw [Atomic.eval_program,Partition.join_split]
  unfold publicOrdinaryLog PCSBCSSourceRootCapture.ordinaryPrefix
  rw [← PCSBCSNativePublicCapture.mixedTrace_actual B seed ro iv [] program remaining limit counted,
    PCSBCSAtomicAllocationTrace.execute_program,Partition.join_split]
  symm
  exact PCSBCSNativePublicCapture.ordinary_map seed ro _
    (PCSBCSNativePublicCapture.execute_answers _ _) []

/-- Every captured old record is also an authentic record for the public
extension. Even nonzero-tag fallback draws have actual observation provenance. -/
theorem publicSeed_sourceLog_authentic
    (address : PCSBCSSourceRootCapture.Key (p := p) (Q := B) (iv := iv) (boundary := boundary) → List Reference)
    (ref : Reference) :
    AuthenticLog (publicSeed (Sampling.eval table source)) (sourceLog address ref source table) := by
  intro input answer member
  have whole := PCSBCSNativeCapturedLogs.sourceLog_subset address ref source table _ member
  have raw := PCSBCSNativePhysicalMerkleBad.atomic_ordinary_origin seed ro _ (input,answer) whole
  obtain ⟨purpose,observed⟩ := PCSBCSNativePhysicalMerkleBad.mixed_seed_origin
    B seed ro iv [] program remaining limit counted input answer raw
  rw [Atomic.eval_program,Partition.join_split]
  exact publicSeed_observed seed ro program remaining limit counted purpose input answer observed

/-- The public whole-log reconstruction covers every typed table, not just
tables from a constrained seed family. -/
theorem publicOrdinaryLog_every_table
    (typed : Table (PCSBCSSourceRootCapture.Key (p := p) (Q := B) (iv := iv) (boundary := boundary))
      PCSBCSSourceRootCapture.Answer) :
    publicOrdinaryLog B iv (Sampling.eval typed source) =
      PCSBCSSourceRootCapture.ordinaryPrefix (Sampling.execute typed source).2 := by
  obtain ⟨arbitrarySeed,arbitraryRO,equal⟩ := PCSBCSNativeSourceTables.every_table typed
  rw [← equal]
  exact publicOrdinaryLog_actual arbitrarySeed arbitraryRO program remaining limit counted

theorem publicSeed_sourceLog_authentic_every_table
    (typed : Table (PCSBCSSourceRootCapture.Key (p := p) (Q := B) (iv := iv) (boundary := boundary))
      PCSBCSSourceRootCapture.Answer)
    (address : PCSBCSSourceRootCapture.Key (p := p) (Q := B) (iv := iv) (boundary := boundary) → List Reference)
    (ref : Reference) :
    AuthenticLog (publicSeed (Sampling.eval typed source)) (sourceLog address ref source typed) := by
  obtain ⟨arbitrarySeed,arbitraryRO,equal⟩ := PCSBCSNativeSourceTables.every_table typed
  rw [← equal]
  exact publicSeed_sourceLog_authentic arbitrarySeed arbitraryRO program remaining limit counted address ref

/-- Public first-reference logs are subsets of the public whole ordinary log,
including prequeries, repeated queries, and independently answered packets. -/
theorem publicLog_subset_every_table
    (typed : Table (PCSBCSSourceRootCapture.Key (p := p) (Q := B) (iv := iv) (boundary := boundary))
      PCSBCSSourceRootCapture.Answer)
    (address : PCSBCSSourceRootCapture.Key (p := p) (Q := B) (iv := iv) (boundary := boundary) → List Reference)
    (ref : Reference) :
    ∀ record ∈ PCSBCSNativePublicCapture.publicLog address ref (Sampling.eval typed source),
      record ∈ publicOrdinaryLog B iv (Sampling.eval typed source) := by
  rw [← PCSBCSNativePublicCapture.publicLog_every_table program remaining limit counted typed address ref,
    publicOrdinaryLog_every_table program remaining limit counted typed]
  exact PCSBCSNativeCapturedLogs.sourceLog_subset address ref source typed

end Generic

section Whole
variable (cap : Nat) (registry : WHIRPhysicalDriver.ProductionRegistry) (Q : Nat)
    (attacker : WHIRSourceChronology.Source cap (AnchoredPhysicalAfter.Input registry.context Q))
    (A B : Nat) (limit : A ≤ B)
    (counted : Counts A (PCSBCSNativePhysicalFreeze.wholeProgram cap registry Q attacker))
    (seed : PrimitiveOracle) (ro : RawKey B → Digest32)

/-- Accepted native syntax supplies every ordinary path plan in the complete
mixed-source view, including any arbitrary attacker prefix. -/
theorem mixed_success_evaluated (a : AnchoredPhysicalAfter.Accepted registry.context Q cap)
    (success : (PCSBCSWholeNativePacketCoverage.mixedView cap registry Q attacker A B limit counted seed ro).result.value = some a)
    (opening : QueryOpening a.input.packet.val.profile) (member : opening ∈ a.native.wire.openings) :
    ∀ path ∈ opening.result.paths, ∀ bytes ∈ path.opening.inputs (hashing (hash seed)),
      bytes.length < 2^56 ∧ ∀ event ∈ plan seed bytes,
        (⟨.primitive .verification event.1,event.2⟩ : Observation) ∈
          (PCSBCSWholeNativePacketCoverage.mixedView cap registry Q attacker A B limit counted seed ro).observations := by
  obtain ⟨before,after,split,_,run,consistent⟩ := PCSBCSWholeNativePacketCoverage.mixed_success_native_segment
    cap registry Q attacker A B limit counted seed ro a success
  obtain ⟨_,_,_,_,observed⟩ := AnchoredPhysicalExecution.verifySource_execution
    cap .fresh (registry.packetModel Q a.input.packet) registry.context rfl Q
    a.input.packet a.input.record a.input.proofs after a.native run
  obtain ⟨proof,_,accepted,covered⟩ := AnchoredIdealPhysicalAcceptance.observed_real
    (observed opening member) seed registry.context.iv consistent
  intro path present bytes input
  obtain ⟨bound,evaluated⟩ := WHIRPhysicalSoundness.openQuery_evaluated seed registry.context.iv
    a.input.packet.val.profile opening.level a.input.record.shape.lanes proof opening.root opening.sample
    opening.result accepted path present bytes input
  refine ⟨bound,?_⟩
  intro event queried
  rw [split]
  exact List.mem_append_right _ (covered _ (evaluated event queried))

theorem mixed_success_publicBadOpening_iff
    (a : AnchoredPhysicalAfter.Accepted registry.context Q cap)
    (success : (PCSBCSWholeNativePacketCoverage.mixedView cap registry Q attacker A B limit counted seed ro).result.value = some a)
    (opening : QueryOpening a.input.packet.val.profile) (member : opening ∈ a.native.wire.openings) :
    publicBadOpening B registry.context.iv
      (boundary := (RawWHIRKeys.entry registry.context a.input.packet.val).frames.length)
      (PCSBCSNativeRootRoles.openingRole a.input.record opening)
      (PCSBCSWholeNativePacketCoverage.mixedView cap registry Q attacker A B limit counted seed ro) opening ↔
    PublicMerkleBinding.OpenPrimitiveBad seed
      (PCSBCSWholeNativeCaptureTransport.wholeOpeningLog cap registry Q attacker A B limit counted seed ro a opening)
      opening.root opening.result.paths := by
  let program := PCSBCSNativePhysicalFreeze.wholeProgram cap registry Q attacker
  have logs := PCSBCSNativePublicCapture.publicLog_actual (p := a.input.packet.val.profile)
    (iv := registry.context.iv) (boundary := (RawWHIRKeys.entry registry.context a.input.packet.val).frames.length)
    seed ro program A limit counted PCSBCSCapturedSourceTransport.address
    (PCSBCSNativeRootRoles.openingRole a.input.record opening)
  dsimp only at logs
  rw [Atomic.eval_program,Partition.join_split] at logs
  change PublicMerkleBinding.OpenPrimitiveBad _ _ _ _ ↔ _
  rw [← logs]
  apply openPrimitiveBad_locality
  intro path present bytes input event queried
  have observed := (mixed_success_evaluated cap registry Q attacker A B limit counted seed ro
    a success opening member path present bytes input).2 event queried
  have answer := publicSeed_observed seed ro program A limit counted .verification event.1 event.2 observed
  have authentic : event.2 = seed event.1 := by
    exact (planFrom_authentic seed _ _ _ event.1 event.2 queried).symm
  exact answer.trans authentic

theorem wholeOrdinaryLog_actual (a : AnchoredPhysicalAfter.Accepted registry.context Q cap) :
    publicOrdinaryLog B registry.context.iv
      (PCSBCSWholeNativePacketCoverage.mixedView cap registry Q attacker A B limit counted seed ro) =
    PCSBCSSourceRootCapture.ordinaryPrefix
      (Sampling.execute
        (PCSBCSWholeNativePacketCoverage.mixedTable (p := a.input.packet.val.profile)
          (iv := registry.context.iv)
          (boundary := (RawWHIRKeys.entry registry.context a.input.packet.val).frames.length) seed ro)
        (PCSBCSWholeNativeCaptureTransport.wholeAllocation cap registry Q attacker A B limit counted a)).2 := by
  have logs := publicOrdinaryLog_actual (p := a.input.packet.val.profile) (iv := registry.context.iv)
    (boundary := (RawWHIRKeys.entry registry.context a.input.packet.val).frames.length)
    seed ro (PCSBCSNativePhysicalFreeze.wholeProgram cap registry Q attacker) A limit counted
  rw [Atomic.eval_program,Partition.join_split] at logs
  exact logs

/-- Cleanliness of the one public whole log implies cleanliness at all first
reference captures, without a separate per-reference hypothesis. -/
theorem wholeReferenceLog_clean (a : AnchoredPhysicalAfter.Accepted registry.context Q cap)
    (clean : ¬ OutputCollision (publicOrdinaryLog B registry.context.iv
      (PCSBCSWholeNativePacketCoverage.mixedView cap registry Q attacker A B limit counted seed ro))) :
    ∀ ref, ¬ OutputCollision
      (PCSBCSWholeNativeCaptureTransport.wholeReferenceLog cap registry Q attacker A B limit counted seed ro a ref) := by
  have logs := publicOrdinaryLog_actual (p := a.input.packet.val.profile) (iv := registry.context.iv)
    (boundary := (RawWHIRKeys.entry registry.context a.input.packet.val).frames.length)
    seed ro (PCSBCSNativePhysicalFreeze.wholeProgram cap registry Q attacker) A limit counted
  rw [Atomic.eval_program,Partition.join_split] at logs
  rw [logs] at clean
  intro ref collision
  exact clean (PCSBCSNativeCapturedLogs.sourceLog_collision _ ref _ _ collision)

end Whole
#print axioms planFrom_locality
#print axioms hash_plan_locality
#print axioms opening_locality
#print axioms target_locality
#print axioms freshTarget_locality
#print axioms openPrimitiveBad_locality
#print axioms publicSeed_observed
#print axioms publicOrdinaryLog_actual
#print axioms publicSeed_sourceLog_authentic
#print axioms mixed_success_evaluated
#print axioms mixed_success_publicBadOpening_iff
#print axioms wholeReferenceLog_clean
#print axioms planFrom_authentic
#print axioms publicOrdinaryLog_every_table
#print axioms publicSeed_sourceLog_authentic_every_table
#print axioms publicLog_subset_every_table
#print axioms wholeOrdinaryLog_actual
end Whir.PCSBCSPublicPrimitiveOpening
