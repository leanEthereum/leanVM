import Whir.PCSBCSNativeSourceFailure
import Whir.PCSBCSNativeSourceTables
import Whir.PCSBCSAtomicAllocationTrace
import Whir.PCSBCSMerkleTableAuthenticity

/-! Public reconstruction for the historical native source. Root admission reads
only public packet-entry bytes, including earlier fake-entry prequeries. Public
observations retain repeated queries; `mixedTrace` reconstructs the compiler's
actual raw draws with its first-answer seed-cache discipline. Original-caller
decoding still requires genuine caller-output observations. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Whir.PCSBCSNativePublicCapture
open Concrete Protocol FiatShamirGame DuplexFraming DuplexModeGame TypedOracleCompiler
open RawOracleCoupling PCSBCSChallengeOracle PCSStateRestoration.Latent
open PublicMerkleLog PCSBCSSourceRootReferences PCSBCSCapturedNativeReplyBridge

/-- Decode the actual mixed draw belonging to an observation. Cache hits make
no draw. The bound test is just the actual source construction-path budget. -/
def observationDraw (B : Nat) (iv : Digest32)
    (log : DuplexPublicSimulator.PublicLog) (o : Observation) :
    List (Sigma (fun _ : PublicCompressionCouplingMixed.Key B => Digest32)) :=
  match o.query with
  | .primitive _ input =>
    match DuplexPublicSimulator.lookup log input with
    | some _ => []
    | none =>
      match DuplexPublicSimulator.privateKey B log input with
      | some key => [⟨.inr key,o.answer⟩]
      | none => [⟨.inl input,o.answer⟩]
  | .construction coordinate _ =>
    if bound : pathCost coordinate ≤ B then
      [⟨.inr (constructionKey B iv coordinate bound),o.answer⟩]
    else []

def nextLog (log : DuplexPublicSimulator.PublicLog) (o : Observation) :
    DuplexPublicSimulator.PublicLog :=
  match o.query with
  | .primitive _ input => DuplexPublicSimulator.observe log input o.answer
  | .construction _ _ => log

/-- Chronological raw draws, not the duplicate-retaining observation list. -/
def mixedTrace (B : Nat) (iv : Digest32)
    (log : DuplexPublicSimulator.PublicLog) : List Observation →
    List (Sigma (fun _ : PublicCompressionCouplingMixed.Key B => Digest32))
  | [] => []
  | o :: rest => observationDraw B iv log o ++ mixedTrace B iv (nextLog log o) rest

private theorem execute_map {B n : Nat} {R S : Type}
    (table : PublicCompressionCouplingMixed.Key B → Digest32) (f : R → S)
    (program : PublicCompressionCouplingMixed.Computation B R n) :
    Sampling.execute table (PublicCompressionCouplingMixed.Computation.map f program) =
      (f (Sampling.execute table program).1,(Sampling.execute table program).2) := by
  induction program with
  | ret => rfl
  | draw key next ih => simp only [PublicCompressionCouplingMixed.Computation.map,Sampling.execute,ih]

private theorem primitive_trace (B : Nat) (seed : DuplexPublicSimulator.Seed)
    (ro : RawKey B → Digest32) (iv : Digest32)
    (log : DuplexPublicSimulator.PublicLog) (purpose : Purpose) (input : Node) :
    let program := PublicCompressionCouplingMixed.primitiveCalls B log input
    let table := PublicCompressionCouplingMixed.oracle seed ro
    (Sampling.execute table program).2 = observationDraw B iv log
      ⟨.primitive purpose input,Sampling.eval table program |>.2⟩ ∧
    (Sampling.eval table program).1 = nextLog log
      ⟨.primitive purpose input,Sampling.eval table program |>.2⟩ := by
  cases hit : DuplexPublicSimulator.lookup log input with
  | some answer => simp [PublicCompressionCouplingMixed.primitiveCalls,hit,Sampling.execute,
      Sampling.eval,observationDraw,nextLog]
  | none =>
    cases key : DuplexPublicSimulator.privateKey B log input <;>
      simp [PublicCompressionCouplingMixed.primitiveCalls,hit,key,Sampling.execute,
        Sampling.eval,observationDraw,nextLog]

/-- The whole public view determines every raw draw, without a seed or RO
argument to the decoder. This is valid for arbitrary prequeries and repeats. -/
theorem mixedTrace_actual {R : Type} (B : Nat) (seed : DuplexPublicSimulator.Seed)
    (ro : RawKey B → Digest32) (iv : Digest32)
    (log : DuplexPublicSimulator.PublicLog) (program : Program R) (remaining : Nat)
    (limit : remaining ≤ B) (counted : Counts remaining program) :
    (Sampling.execute (PublicCompressionCouplingMixed.oracle seed ro)
      (PublicCompressionCouplingMixed.compile B iv log program remaining limit counted)).2 =
      mixedTrace B iv log (Sampling.eval (PublicCompressionCouplingMixed.oracle seed ro)
        (PublicCompressionCouplingMixed.compile B iv log program remaining limit counted)).observations := by
  induction program generalizing log remaining with
  | done result => rfl
  | ask query next ih =>
    cases query with
    | primitive purpose input =>
      simp only [PublicCompressionCouplingMixed.compile,Sampling.execute_pad,Sampling.execute_bind,
        execute_map,Sampling.eval_pad,Sampling.eval_bind,
        PublicCompressionCouplingMixed.Computation.eval_map,DuplexRawProgram.observe,mixedTrace]
      obtain ⟨trace,updated⟩ := primitive_trace B seed ro iv log purpose input
      rw [trace,updated]
      congr 1
      exact ih _ _ _ _ _
    | construction coordinate valid =>
      have bound : pathCost coordinate ≤ B := counted.1.trans limit
      simp only [PublicCompressionCouplingMixed.compile,Sampling.execute_pad,Sampling.execute,
        execute_map,Sampling.eval_pad,PublicCompressionCouplingMixed.Computation.eval_map,
        Sampling.eval,DuplexRawProgram.observe,mixedTrace,observationDraw,nextLog,
        dite_eq_left bound,List.singleton_append]
      congr 1
      exact ih _ _ _ _ _

section First
universe u v w z
variable {Key : Type u} {Answer : Key → Type v} {Root : Type w} {R : Type z}
    [DecidableEq Root]

/-- First address mention in the chronological trace, excluding its answer. -/
def firstPrefix (address : Key → List Root) (root : Root) :
    List (Sigma Answer) → Option (List (Sigma Answer))
  | [] => none
  | event :: rest => if root ∈ address event.1 then some []
      else (firstPrefix address root rest).map (event :: ·)

theorem firstPrefix_execute (address : Key → List Root) (root : Root)
    {n : Nat} (program : Sampling Key Answer R n) (table : Table Key Answer) :
    PCSBCSFirstRootDisclosure.firstMention address root program table =
      firstPrefix address root (Sampling.execute table program).2 := by
  induction program with
  | ret => rfl
  | draw key next ih => simp only [PCSBCSFirstRootDisclosure.firstMention,
      Sampling.execute,firstPrefix,ih]

theorem firstPrefix_subset (address : Key → List Root) (root : Root)
    (events before : List (Sigma Answer)) (found : firstPrefix address root events = some before) :
    ∀ event ∈ before, event ∈ events := by
  induction events generalizing before with
  | nil => simp [firstPrefix] at found
  | cons event rest ih =>
    simp only [firstPrefix] at found
    split at found
    · cases Option.some.inj found
      simp
    · obtain ⟨earlier,hprefix,equal⟩ := Option.map_eq_some_iff.mp found
      subst before
      intro item member
      rcases List.mem_cons.mp member with equal | present
      · exact List.mem_cons.mpr (Or.inl equal)
      · exact List.mem_cons_of_mem _ (ih earlier hprefix item present)
end First

section Allocation
variable {p : ParameterBounds.Profile} {B : Nat} {iv : Digest32} {boundary : Nat}
local notation "part" => EnteredPacket.partition (p := p) (Q := B) (iv := iv) (boundary := boundary)
local notation "Keys" => PCSBCSSourceRootCapture.Key (p := p) (Q := B) (iv := iv) (boundary := boundary)
local notation "Answers" => PCSBCSSourceRootCapture.Answer (p := p) (Q := B) (iv := iv) (boundary := boundary)

/-- Only the key of a raw allocation is needed to locate its address mention.
A recognized packet's independently sampled full answer is never inspected. -/
noncomputable def allocatedKey (raw : PublicCompressionCouplingMixed.Key B) : Keys :=
  match found : (part).recognize raw with
  | some block => .inl block.1
  | none => .inr ⟨raw,found⟩

/-- Public chronological capture, with a public key-address decoder. This keeps
exact first mention, including a raw prequery before a later announcement. -/
noncomputable def publicPrefix {R : Type} (address : Keys → List Reference)
    (ref : Reference) (view : View R) : Option
      (List (Sigma (fun _ : PublicCompressionCouplingMixed.Key B => Digest32))) :=
  firstPrefix (fun raw => address (allocatedKey raw)) ref (mixedTrace B iv [] view.observations)

private theorem allocation_key (table : Table Keys Answers)
    (raw : PublicCompressionCouplingMixed.Key B) :
    (PCSBCSAtomicAllocationTrace.allocation (part) table raw).1 = allocatedKey raw := by
  unfold PCSBCSAtomicAllocationTrace.allocation allocatedKey
  split <;> split <;> simp_all

private theorem firstPrefix_map (address : Keys → List Reference) (ref : Reference)
    (table : Table Keys Answers)
    (events : List (Sigma (fun _ : PublicCompressionCouplingMixed.Key B => Digest32))) :
    firstPrefix address ref (events.map (fun e =>
      PCSBCSAtomicAllocationTrace.allocation (part) table e.1)) =
      (firstPrefix (fun raw => address (allocatedKey raw)) ref events).map
        (List.map (fun e => PCSBCSAtomicAllocationTrace.allocation (part) table e.1)) := by
  induction events with
  | nil => rfl
  | cons event rest ih =>
    simp only [List.map_cons,firstPrefix,allocation_key]
    split
    · rfl
    · rw [ih]
      simp only [Option.map_map,Function.comp_def,List.map_cons]

/-- Exact prefix provenance for the actual atomic source. The full packet
trace need not equal the public trace: it has independent full-vector answers.
The capture *prefix* is exactly the public raw prefix's allocation map. -/
theorem publicPrefix_actual {R : Type} (seed : DuplexPublicSimulator.Seed)
    (ro : RawKey B → Digest32) (program : Program R) (remaining : Nat)
    (limit : remaining ≤ B) (counted : Counts remaining program)
    (address : Keys → List Reference) (ref : Reference) :
    let table := (part).split (PublicCompressionCouplingMixed.oracle seed ro)
    let source := Atomic.program (part)
      (PublicCompressionCouplingMixed.compile B iv [] program remaining limit counted)
    PCSBCSFirstRootDisclosure.firstMention address ref source table =
      (publicPrefix address ref (Sampling.eval table source)).map
        (List.map (fun e => PCSBCSAtomicAllocationTrace.allocation (part) table e.1)) := by
  dsimp only
  rw [firstPrefix_execute,PCSBCSAtomicAllocationTrace.execute_program,Partition.join_split,
    firstPrefix_map,mixedTrace_actual]
  unfold publicPrefix
  rw [Atomic.eval_program,Partition.join_split]


private theorem seed_unrecognized (input : Node) :
    (part).recognize (.inl input) = none := by
  cases found : (part).recognize (.inl input) with
  | none => rfl
  | some block =>
    have equal := (part).encode_recognize _ block found
    change Sum.inr _ = Sum.inl input at equal
    cases equal

def rawOrdinary (event : Sigma (fun _ : PublicCompressionCouplingMixed.Key B => Digest32)) :
    PublicLog :=
  match event.1 with
  | .inl input => [(input,event.2)]
  | .inr _ => []

noncomputable def publicLog {R : Type} (address : Keys → List Reference)
    (ref : Reference) (view : View R) : PublicLog :=
  ((publicPrefix address ref view).getD []).foldl (fun log event => rawOrdinary event ++ log) []

private theorem allocation_ordinary (seed : DuplexPublicSimulator.Seed)
    (ro : RawKey B → Digest32) (raw : PublicCompressionCouplingMixed.Key B) :
    PCSBCSSourceRootCapture.ordinaryRecord
      (PCSBCSAtomicAllocationTrace.allocation (part)
        ((part).split (PublicCompressionCouplingMixed.oracle seed ro)) raw) =
      rawOrdinary ⟨raw,PublicCompressionCouplingMixed.oracle seed ro raw⟩ := by
  cases raw with
  | inl input =>
    unfold PCSBCSAtomicAllocationTrace.allocation
    split
    · rename_i block found
      have impossible := found.symm.trans (seed_unrecognized (p := p) (iv := iv)
        (boundary := boundary) input)
      cases impossible
    · rfl
  | inr key =>
    unfold PCSBCSAtomicAllocationTrace.allocation
    split <;> rfl

theorem execute_answers {Key : Type} {R : Type} {n : Nat}
    (table : Key → Digest32) (program : Sampling Key (fun _ => Digest32) R n) :
    ∀ event ∈ (Sampling.execute table program).2, event.2 = table event.1 := by
  induction program with
  | ret => simp [Sampling.execute]
  | draw key next ih =>
    intro event member
    rcases List.mem_cons.mp member with equal | present
    · cases equal
      rfl
    · exact ih _ event present

theorem ordinary_map (seed : DuplexPublicSimulator.Seed) (ro : RawKey B → Digest32)
    (events : List (Sigma (fun _ : PublicCompressionCouplingMixed.Key B => Digest32)))
    (correct : ∀ event ∈ events, event.2 = PublicCompressionCouplingMixed.oracle seed ro event.1)
    (prior : PublicLog) :
    (events.map (fun e => PCSBCSAtomicAllocationTrace.allocation (part)
        ((part).split (PublicCompressionCouplingMixed.oracle seed ro)) e.1)).foldl
      (fun log event => PCSBCSSourceRootCapture.ordinaryRecord event ++ log) prior =
      events.foldl (fun log event => rawOrdinary event ++ log) prior := by
  induction events generalizing prior with
  | nil => rfl
  | cons event rest ih =>
    simp only [List.map_cons,List.foldl_cons,allocation_ordinary]
    have equal : (⟨event.1,PublicCompressionCouplingMixed.oracle seed ro event.1⟩ :
        Sigma (fun _ : PublicCompressionCouplingMixed.Key B => Digest32)) = event :=
      Sigma.ext rfl (by simpa using (correct event List.mem_cons_self).symm)
    rw [equal]
    exact ih (fun e member => correct e (List.mem_cons_of_mem _ member)) _

/-- Exact ordinary-log equality, not a conflation of deduplicated seed draws
with duplicate-retaining public observations. The public decoder has no table,
seed, full-packet completion, or private hash-oracle input. -/
theorem publicLog_actual {R : Type} (seed : DuplexPublicSimulator.Seed)
    (ro : RawKey B → Digest32) (program : Program R) (remaining : Nat)
    (limit : remaining ≤ B) (counted : Counts remaining program)
    (address : Keys → List Reference) (ref : Reference) :
    let table := (part).split (PublicCompressionCouplingMixed.oracle seed ro)
    let source := Atomic.program (part)
      (PublicCompressionCouplingMixed.compile B iv [] program remaining limit counted)
    sourceLog address ref source table = publicLog address ref (Sampling.eval table source) := by
  dsimp only
  unfold sourceLog publicLog
  rw [publicPrefix_actual]
  cases found : publicPrefix address ref
      (Sampling.eval ((part).split (PublicCompressionCouplingMixed.oracle seed ro))
        (Atomic.program (part)
          (PublicCompressionCouplingMixed.compile B iv [] program remaining limit counted))) with
  | none => rfl
  | some events =>
    simp only [Option.map_some,Option.getD_some,PCSBCSSourceRootCapture.ordinaryPrefix]
    apply ordinary_map seed ro events _ []
    intro event member
    have present := firstPrefix_subset _ ref _ events found event member
    have trace := mixedTrace_actual B seed ro iv [] program remaining limit counted
    rw [Atomic.eval_program,Partition.join_split] at present
    rw [← trace] at present
    exact execute_answers _ _ event present

/-- All typed tables are covered, not just tables in a deterministic compression
family. The address decoder reads only public packet bytes. -/
theorem publicLog_every_table {R : Type} (program : Program R) (remaining : Nat)
    (limit : remaining ≤ B) (counted : Counts remaining program)
    (table : Table Keys Answers) (address : Keys → List Reference) (ref : Reference) :
    let source := Atomic.program (part)
      (PublicCompressionCouplingMixed.compile B iv [] program remaining limit counted)
    sourceLog address ref source table = publicLog address ref (Sampling.eval table source) := by
  obtain ⟨seed,ro,equal⟩ := PCSBCSNativeSourceTables.every_table table
  rw [← equal]
  exact publicLog_actual seed ro program remaining limit counted address ref

/-- Public reconstruction uses full-width zero-prefix leaves and only then
strips the occupied suffix, via the existing `freeze` constructor. -/
noncomputable def publicRoot {R : Type} (address : Keys → List Reference)
    (ref : Reference) (view : View R) : CausalGame.BaseOracle :=
  (PCSBCSMerkleRootCache.freeze (publicLog address ref view) ref.root ref.shape).raw

theorem publicRoot_actual {R : Type} (seed : DuplexPublicSimulator.Seed)
    (ro : RawKey B → Digest32) (program : Program R) (remaining : Nat)
    (limit : remaining ≤ B) (counted : Counts remaining program)
    (address : Keys → List Reference) (ref : Reference)
    (clean : ¬ OutputCollision (publicLog address ref
      (Sampling.eval ((part).split (PublicCompressionCouplingMixed.oracle seed ro))
        (Atomic.program (part)
          (PublicCompressionCouplingMixed.compile B iv [] program remaining limit counted))))) :
    let table := (part).split (PublicCompressionCouplingMixed.oracle seed ro)
    let source := Atomic.program (part)
      (PublicCompressionCouplingMixed.compile B iv [] program remaining limit counted)
    publicRoot address ref (Sampling.eval table source) =
      PCSBCSCapturedSourceAcceptance.sourceRoot seed address ref source table := by
  dsimp only
  have equal := publicLog_actual seed ro program remaining limit counted address ref
  have auth := PCSBCSMerkleSeedProjection.sourceLog_authentic seed ro address ref
    (Atomic.program (part)
      (PublicCompressionCouplingMixed.compile B iv [] program remaining limit counted))
  unfold publicRoot PCSBCSCapturedSourceAcceptance.sourceRoot
  rw [← equal]
  exact (PCSBCSCapturedNativeReplyBridge.next_image_provenance seed _ ref auth
    (equal ▸ clean)).2

/-- Two arbitrary typed tables with the same actual whole View have identical
ordinary capture logs for any fixed public address decoder. -/
theorem publicLog_same_view {R : Type} (program : Program R) (remaining : Nat)
    (limit : remaining ≤ B) (counted : Counts remaining program)
    (left right : Table Keys Answers) (address : Keys → List Reference)
    (ref : Reference)
    (same : Sampling.eval left (Atomic.program (part)
        (PublicCompressionCouplingMixed.compile B iv [] program remaining limit counted)) =
      Sampling.eval right (Atomic.program (part)
        (PublicCompressionCouplingMixed.compile B iv [] program remaining limit counted))) :
    let source := Atomic.program (part)
      (PublicCompressionCouplingMixed.compile B iv [] program remaining limit counted)
    sourceLog address ref source left =
      sourceLog address ref source right := by
  dsimp only
  rw [publicLog_every_table,publicLog_every_table,same]

theorem publicRoot_every_table {R : Type} (program : Program R) (remaining : Nat)
    (limit : remaining ≤ B) (counted : Counts remaining program)
    (table : Table Keys Answers) (address : Keys → List Reference) (ref : Reference)
    (clean : ¬ OutputCollision (publicLog address ref (Sampling.eval table
      (Atomic.program (part)
        (PublicCompressionCouplingMixed.compile B iv [] program remaining limit counted))))) :
    let source := Atomic.program (part)
      (PublicCompressionCouplingMixed.compile B iv [] program remaining limit counted)
    publicRoot address ref (Sampling.eval table source) =
      PCSBCSCapturedSourceAcceptance.sourceRoot (PCSBCSMerkleTableAuthenticity.seed table)
        address ref source table := by
  dsimp only
  have equal := publicLog_every_table program remaining limit counted table address ref
  have auth := PCSBCSMerkleTableAuthenticity.sourceLog_authentic address ref
    (Atomic.program (part)
      (PublicCompressionCouplingMixed.compile B iv [] program remaining limit counted)) table
  unfold publicRoot PCSBCSCapturedSourceAcceptance.sourceRoot
  rw [← equal]
  exact (PCSBCSCapturedNativeReplyBridge.next_image_provenance _ _ ref auth
    (equal ▸ clean)).2

/-- Literal sourceRoot independence across ANY two typed tables. Each seed is
its own table projection; no equality of seeds or roots is assumed. -/
theorem sourceRoot_same_view {R : Type} (program : Program R) (remaining : Nat)
    (limit : remaining ≤ B) (counted : Counts remaining program)
    (left right : Table Keys Answers)
    (ref : Reference)
    (same : Sampling.eval left (Atomic.program (part)
        (PublicCompressionCouplingMixed.compile B iv [] program remaining limit counted)) =
      Sampling.eval right (Atomic.program (part)
        (PublicCompressionCouplingMixed.compile B iv [] program remaining limit counted)))
    (clean : ¬ OutputCollision (publicLog (PCSBCSCapturedSourceTransport.address
      (p := p) (Q := B) (iv := iv) (boundary := boundary))
      ref (Sampling.eval left (Atomic.program (part)
        (PublicCompressionCouplingMixed.compile B iv [] program remaining limit counted))))) :
    let source := Atomic.program (part)
      (PublicCompressionCouplingMixed.compile B iv [] program remaining limit counted)
    PCSBCSCapturedSourceAcceptance.sourceRoot (PCSBCSMerkleTableAuthenticity.seed left)
      PCSBCSCapturedSourceTransport.address ref source left =
      PCSBCSCapturedSourceAcceptance.sourceRoot (PCSBCSMerkleTableAuthenticity.seed right)
        PCSBCSCapturedSourceTransport.address ref source right := by
  dsimp only
  rw [← publicRoot_every_table program remaining limit counted left _ ref clean]
  have rightClean := clean
  rw [same] at rightClean
  rw [← publicRoot_every_table program remaining limit counted right _ ref rightClean,same]
end Allocation

/-- Read the construction observations themselves, not a proposed public/eval
codec equality. Missing unqueried coordinates receive only an inert default. -/
def publicAnswers {R : Type} (view : View R) (q : Coordinate) : Digest32 :=
  (WHIRPhysicalCaller.latestAnswers view.observations q).getD (fun _ => 0)

def publicOriginal {R : Type} (p : ParameterBounds.Profile)
    (layout : WHIRCallerClaims.CallerLayout) (saved : AnchoredHeaderCodec.Record)
    (entry : FramedHistory) (view : View R) : Option (PCSBCSCallerBinding.CallerInput p) :=
  PCSBCSSourceCallerOriginal.original p layout saved entry (publicAnswers view)

section WholeCaller
variable {p : ParameterBounds.Profile} {B : Nat} {iv : Digest32} {boundary : Nat}
local notation "part" => EnteredPacket.partition (p := p) (Q := B) (iv := iv) (boundary := boundary)
local notation "Keys" => PCSBCSSourceRootCapture.Key (p := p) (Q := B) (iv := iv) (boundary := boundary)

/-- Public recovery of a coordinate actually queried anywhere in the WHOLE
source program. Repeated observations are consistent by actual raw RO execution,
not by an assumed public/evaluation codec equality. -/
theorem publicAnswers_recorded {R : Type} (seed : DuplexPublicSimulator.Seed)
    (ro : RawKey B → Digest32) (program : Program R) (remaining : Nat)
    (limit : remaining ≤ B) (counted : Counts remaining program)
    (wanted : Coordinate) (valid : DuplexEncoding.Admissible wanted) (answer : Digest32)
    (present : (⟨.construction wanted valid,answer⟩ : Observation) ∈
      (Sampling.eval (PublicCompressionCouplingMixed.oracle seed ro)
        (PublicCompressionCouplingMixed.compile B iv [] program remaining limit counted)).observations) :
    publicAnswers (Sampling.eval (PublicCompressionCouplingMixed.oracle seed ro)
      (PublicCompressionCouplingMixed.compile B iv [] program remaining limit counted)) wanted =
      PCSBCSSourceCallerAnswers.answers ((part).split
        (PublicCompressionCouplingMixed.oracle seed ro)) wanted := by
  let view := Sampling.eval (PublicCompressionCouplingMixed.oracle seed ro)
    (PublicCompressionCouplingMixed.compile B iv [] program remaining limit counted)
  have first := present
  rw [PublicCompressionCouplingMixed.compile_actual] at first
  obtain ⟨bounded,_⟩ := PCSBCSIdealConstructionAnswers.construction_observations
    _ ro iv _ _ _ _ _ wanted valid answer first
  have consistent : ∀ observation ∈ view.observations, ∀ proof,
      observation.query = .construction wanted proof →
      observation.answer = ro (constructionKey B iv wanted bounded) := by
    intro observation member proof same
    have construction : (⟨.construction wanted proof,observation.answer⟩ : Observation) ∈
        view.observations := by
      cases observation
      cases same
      exact member
    dsimp only [view] at construction
    rw [PublicCompressionCouplingMixed.compile_actual] at construction
    obtain ⟨bound,actual⟩ := PCSBCSIdealConstructionAnswers.construction_observations
      _ ro iv _ _ _ _ _ wanted proof _ construction
    exact actual
  have found := WHIRPhysicalCaller.latestAnswers_consistent view.observations wanted valid
    (ro (constructionKey B iv wanted bounded)) ⟨_,present,rfl⟩ consistent
  rw [PCSBCSNativeIdealCallerOriginal.split_answers seed ro wanted bounded]
  change (WHIRPhysicalCaller.latestAnswers view.observations wanted).getD (fun _ => 0) = _
  rw [found]
  rfl

/-- The only coverage premise is actual public construction-query membership,
which a native caller segment supplies. No decoded-original equality is assumed. -/
theorem publicOriginal_recorded {R : Type} (seed : DuplexPublicSimulator.Seed)
    (ro : RawKey B → Digest32) (program : Program R) (remaining : Nat)
    (limit : remaining ≤ B) (counted : Counts remaining program)
    (layout : WHIRCallerClaims.CallerLayout) (saved : AnchoredHeaderCodec.Record)
    (entry : FramedHistory)
    (queried : ∀ wanted ∈ WHIRCallerOutputs.callerOutputs entry,
      ∃ valid answer, (⟨.construction wanted valid,answer⟩ : Observation) ∈
        (Sampling.eval (PublicCompressionCouplingMixed.oracle seed ro)
          (PublicCompressionCouplingMixed.compile B iv [] program remaining limit counted)).observations) :
    publicOriginal p layout saved entry (Sampling.eval (PublicCompressionCouplingMixed.oracle seed ro)
      (PublicCompressionCouplingMixed.compile B iv [] program remaining limit counted)) =
      PCSBCSSourceCallerOriginal.original p layout saved entry
        (PCSBCSSourceCallerAnswers.answers ((part).split
          (PublicCompressionCouplingMixed.oracle seed ro))) := by
  unfold publicOriginal
  apply PCSBCSSourceCallerOriginal.original_prior_only
  intro wanted member
  obtain ⟨valid,answer,present⟩ := queried wanted member
  exact publicAnswers_recorded seed ro program remaining limit counted wanted valid answer present

/-- Failure observer input is only the whole View and public source geometry.
It does not accept a seed, table, root accessor, or failure certificate. -/
noncomputable def publicExtractionFailed {R : Type}
    (layout : WHIRCallerClaims.CallerLayout) (saved : AnchoredHeaderCodec.Record)
    (entry : FramedHistory)
    (ref : Reference) (view : View R) : Prop :=
  ∃ original : PCSBCSCallerBinding.CallerInput p,
    publicOriginal p layout saved entry view = some original ∧
    ¬ ∃ witness,
      PCSRoundByRoundKnowledge.extract p original.lanes original.family original.points
        original.anchorPoint original.anchorValue
        (publicRoot (PCSBCSCapturedSourceTransport.address (p := p) (Q := B)
          (iv := iv) (boundary := boundary)) ref view) = some witness ∧
      PCSRewindSource.ExplainsOriginal (ParameterBounds.config p) original.lanes
        (publicRoot (PCSBCSCapturedSourceTransport.address (p := p) (Q := B)
          (iv := iv) (boundary := boundary)) ref view) original.family original.points
        original.anchorPoint original.anchorValue witness

theorem publicExtractionFailed_actual {R : Type} (seed : DuplexPublicSimulator.Seed)
    (ro : RawKey B → Digest32) (program : Program R) (remaining : Nat)
    (limit : remaining ≤ B) (counted : Counts remaining program)
    (layout : WHIRCallerClaims.CallerLayout) (saved : AnchoredHeaderCodec.Record)
    (entry : FramedHistory) (ref : Reference)
    (queried : ∀ wanted ∈ WHIRCallerOutputs.callerOutputs entry,
      ∃ valid answer, (⟨.construction wanted valid,answer⟩ : Observation) ∈
        (Sampling.eval (PublicCompressionCouplingMixed.oracle seed ro)
          (PublicCompressionCouplingMixed.compile B iv [] program remaining limit counted)).observations)
    (clean : ¬ OutputCollision (publicLog (PCSBCSCapturedSourceTransport.address
      (p := p) (Q := B) (iv := iv) (boundary := boundary)) ref
      (Sampling.eval (PublicCompressionCouplingMixed.oracle seed ro)
        (PublicCompressionCouplingMixed.compile B iv [] program remaining limit counted)))) :
    let table := (part).split (PublicCompressionCouplingMixed.oracle seed ro)
    let source := Atomic.program (part)
      (PublicCompressionCouplingMixed.compile B iv [] program remaining limit counted)
    let view := Sampling.eval table source
    publicExtractionFailed (p := p) (B := B) (iv := iv) (boundary := boundary)
      layout saved entry ref view ↔
      ∃ original : PCSBCSCallerBinding.CallerInput p,
        PCSBCSSourceCallerOriginal.original p layout saved entry
          (PCSBCSSourceCallerAnswers.answers table) = some original ∧
        ¬ ∃ witness,
          PCSRoundByRoundKnowledge.extract p original.lanes original.family original.points
            original.anchorPoint original.anchorValue
            (PCSBCSCapturedSourceAcceptance.sourceRoot seed PCSBCSCapturedSourceTransport.address ref source table) = some witness ∧
          PCSRewindSource.ExplainsOriginal (ParameterBounds.config p) original.lanes
            (PCSBCSCapturedSourceAcceptance.sourceRoot seed PCSBCSCapturedSourceTransport.address ref source table)
            original.family original.points original.anchorPoint original.anchorValue witness := by
  dsimp only
  have root := publicRoot_actual seed ro program remaining limit counted
    PCSBCSCapturedSourceTransport.address ref
    (by simpa only [Atomic.eval_program,Partition.join_split] using clean)
  unfold publicExtractionFailed
  rw [root]
  simp only [Atomic.eval_program,Partition.join_split]
  rw [publicOriginal_recorded seed ro program remaining limit counted layout saved entry queried]
end WholeCaller

section NativeCaller
variable (cap : Nat) (model : WHIRCallerSupport.ProductionLayout)
    (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack) (Q : Nat)
    (packet : RawWHIRKeys.Packet ctx Q) (saved : AnchoredHeaderCodec.Record)
    (proofs : Array MerkleTransport.PrunedMerklePaths) (B : Nat)
    (limit : WHIRPhysicalVerifier.sourceBudget ctx Q packet ≤ B)
    (seed : DuplexPublicSimulator.Seed) (ro : RawKey B → Digest32)

/-- Verifier-only specialization: successful actual fresh execution derives
public reconstruction of the independently decoded original. -/
theorem native_publicOriginal
    (a : AnchoredPhysicalDriver.Accepted ctx Q cap packet saved)
    (success : (AnchoredMixedIdealSourceAcceptance.mixedView cap .fresh model ctx stack Q packet saved proofs
      ctx.iv B limit seed ro).result.value = some a) :
    publicOriginal packet.val.profile model.layout saved (RawWHIRKeys.entry ctx packet.val)
      (AnchoredMixedIdealSourceAcceptance.mixedView cap .fresh model ctx stack Q packet saved proofs
        ctx.iv B limit seed ro) =
      PCSBCSSourceCallerOriginal.original packet.val.profile model.layout saved
        (RawWHIRKeys.entry ctx packet.val)
        (PCSBCSSourceCallerAnswers.answers
          (PCSBCSCapturedIdealNativeAcceptance.table ctx Q packet B seed ro)) := by
  let view := AnchoredMixedIdealSourceAcceptance.mixedView cap .fresh model ctx stack Q packet saved proofs
    ctx.iv B limit seed ro
  let table := PCSBCSCapturedIdealNativeAcceptance.table ctx Q packet B seed ro
  obtain ⟨run,_,_⟩ := AnchoredMixedIdealSourceAcceptance.mixedView_runs
    cap .fresh model ctx stack Q packet saved proofs ctx.iv B limit seed ro
  rw [success] at run
  obtain ⟨caller,_,_,_,_⟩ := AnchoredPhysicalExecution.verifySource_execution
    cap .fresh model ctx stack Q packet saved proofs _ a run
  obtain ⟨before,after,splitTrace,_,queries,_⟩ := caller
  unfold publicOriginal
  apply PCSBCSSourceCallerOriginal.original_prior_only
  intro wanted prior
  have queried : Query.construction wanted (RawWHIRKeys.callerOutput_admissible ctx Q packet wanted prior) ∈
      before.map Observation.query := by
    rw [queries]
    exact List.mem_map.mpr ⟨⟨wanted,prior⟩,List.mem_attach _ _,rfl⟩
  obtain ⟨observation,present,same⟩ := List.mem_map.mp queried
  have presentWhole : observation ∈ view.observations := by
    rw [show view.observations = before ++ after from splitTrace]
    exact List.mem_append_left _ present
  have consistent : ∀ observation ∈ view.observations, ∀ valid,
      observation.query = .construction wanted valid →
      observation.answer = PCSBCSSourceCallerAnswers.answers table wanted := by
    intro observed member valid same
    have construction : (⟨.construction wanted valid,observed.answer⟩ : Observation) ∈
        view.observations := by
      cases observed
      cases same
      exact member
    simp only [view,AnchoredMixedIdealSourceAcceptance.mixedView,
      PublicCompressionCouplingMixed.compile_actual] at construction
    obtain ⟨bounded,actual⟩ := PCSBCSIdealConstructionAnswers.construction_observations
      _ ro ctx.iv _ _ _ _ _ wanted valid _ construction
    dsimp only [table,PCSBCSCapturedIdealNativeAcceptance.table]
    rw [PCSBCSNativeIdealCallerOriginal.split_answers seed ro wanted bounded]
    exact actual
  have answer := WHIRPhysicalCaller.latestAnswers_consistent view.observations wanted
    (RawWHIRKeys.callerOutput_admissible ctx Q packet wanted prior)
    (PCSBCSSourceCallerAnswers.answers table wanted) ⟨observation,presentWhole,same⟩ consistent
  change (WHIRPhysicalCaller.latestAnswers view.observations wanted).getD (fun _ => 0) = _
  rw [answer]
  rfl
end NativeCaller
#print axioms mixedTrace_actual
#print axioms firstPrefix_execute
#print axioms publicPrefix_actual
#print axioms publicLog_actual
#print axioms publicLog_every_table
#print axioms publicLog_same_view
#print axioms publicRoot_actual
#print axioms publicRoot_every_table
#print axioms sourceRoot_same_view
#print axioms native_publicOriginal
#print axioms publicAnswers_recorded
#print axioms publicOriginal_recorded
#print axioms publicExtractionFailed_actual
end Whir.PCSBCSNativePublicCapture
