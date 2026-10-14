import Whir.PCSBCSCapturedNativeReplyBridge
import Whir.PCSBCSActualMerkleBound

/-! Ordinary Merkle nodes use the seed summand of the actual mixed compiler.
Cached public replies remain observations but allocate no physical draw. The
invariant below concerns only tag-zero records, not equality of public logs.
The grouped first-mention prefix is authenticated directly by physical seed
coordinates; no hidden full-table extraction is assumed. -/
set_option autoImplicit false
namespace Whir.PCSBCSMerkleSeedProjection
open FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame TypedOracleCompiler

/-- The exact count-plus-chunk induction and UInt64 no-wrap bound are already
proved by PublicMerkleLog; retain that bound at the seed-projection boundary. -/
theorem plan_tag_zero (C : PrimitiveOracle) (bytes : List Byte)
    (bound : bytes.length < 2^56) (n : Node) (d : Digest32)
    (member : (n,d) ∈ PublicMerkleLog.plan C bytes) : tag n = 0 :=
  PublicMerkleLog.plan_tag_zero C bytes bound n d member

theorem not_terminal {input : Node} (ordinary : tag input = 0) : ¬ isTerminal input := by
  simp [isTerminal,ordinary]

theorem recognized_none (log : DuplexPublicSimulator.PublicLog) {input : Node}
    (ordinary : tag input = 0) : DuplexPublicSimulator.recognized log input = none := by
  simp [DuplexPublicSimulator.recognized,not_terminal ordinary]

theorem privateKey_none (Q : Nat) (log : DuplexPublicSimulator.PublicLog) {input : Node}
    (ordinary : tag input = 0) : DuplexPublicSimulator.privateKey Q log input = none := by
  unfold DuplexPublicSimulator.privateKey
  rw [recognized_none log ordinary]
  split <;> rfl

theorem plan_privateKey_none (Q : Nat) (log : DuplexPublicSimulator.PublicLog)
    (C : PrimitiveOracle) (bytes : List Byte) (bound : bytes.length < 2^56)
    (n : Node) (d : Digest32) (member : (n,d) ∈ PublicMerkleLog.plan C bytes) :
    DuplexPublicSimulator.privateKey Q log n = none :=
  privateKey_none Q log (plan_tag_zero C bytes bound n d member)

theorem primitiveCalls_miss (Q : Nat) (log : DuplexPublicSimulator.PublicLog)
    (input : Node) (ordinary : tag input = 0)
    (miss : DuplexPublicSimulator.lookup log input = none) :
    PublicCompressionCouplingMixed.primitiveCalls Q log input =
      .draw (.inl input) (fun answer =>
        .ret (DuplexPublicSimulator.observe log input answer,answer)) := by
  simp [PublicCompressionCouplingMixed.primitiveCalls,miss,privateKey_none Q log ordinary]

theorem primitiveCalls_hit (Q : Nat) (log : DuplexPublicSimulator.PublicLog)
    (input : Node) (answer : Digest32)
    (hit : DuplexPublicSimulator.lookup log input = some answer) :
    PublicCompressionCouplingMixed.primitiveCalls Q log input =
      .ret (DuplexPublicSimulator.observe log input answer,answer) := by
  simp [PublicCompressionCouplingMixed.primitiveCalls,hit]

/-- A miss has precisely one physical seed draw, even though the simulator's
runRO meter does not count fallback seed evaluations as private RO draws. -/
theorem execute_miss (Q : Nat) (seed : PrimitiveOracle) (ro : RawKey Q → Digest32)
    (log : DuplexPublicSimulator.PublicLog) (input : Node) (ordinary : tag input = 0)
    (miss : DuplexPublicSimulator.lookup log input = none) :
    Sampling.execute (PublicCompressionCouplingMixed.oracle seed ro)
      (PublicCompressionCouplingMixed.primitiveCalls Q log input) =
      ((DuplexPublicSimulator.observe log input (seed input),seed input),
        [⟨.inl input,seed input⟩]) := by
  rw [primitiveCalls_miss Q log input ordinary miss]
  rfl

theorem execute_hit (Q : Nat) (seed : PrimitiveOracle) (ro : RawKey Q → Digest32)
    (log : DuplexPublicSimulator.PublicLog) (input : Node) (answer : Digest32)
    (hit : DuplexPublicSimulator.lookup log input = some answer) :
    Sampling.execute (PublicCompressionCouplingMixed.oracle seed ro)
      (PublicCompressionCouplingMixed.primitiveCalls Q log input) =
      ((DuplexPublicSimulator.observe log input answer,answer),[]) := by
  rw [primitiveCalls_hit Q log input answer hit]
  rfl

/-- Nonordinary public answers may come from the private-key summand. Only the
ordinary part must agree with the seed, and this is maintained operationally. -/
def OrdinaryAuthentic (seed : PrimitiveOracle) (log : DuplexPublicSimulator.PublicLog) : Prop :=
  ∀ n d, (n,d) ∈ log → tag n = 0 → seed n = d

theorem lookup_mem {log : DuplexPublicSimulator.PublicLog} {input : Node} {answer : Digest32}
    (hit : DuplexPublicSimulator.lookup log input = some answer) : (input,answer) ∈ log := by
  unfold DuplexPublicSimulator.lookup at hit
  cases found : log.find? (fun e => decide (e.1 = input)) with
  | none => simp [found] at hit
  | some entry =>
    have hm := List.mem_of_find?_eq_some found
    have he := List.find?_some found
    have hn : entry.1 = input := of_decide_eq_true he
    have hd : entry.2 = answer := by simpa [found] using hit
    have same : entry = (input,answer) := Prod.ext hn hd
    simpa only [same] using hm

theorem observe_preserves (seed : PrimitiveOracle) (log : DuplexPublicSimulator.PublicLog)
    (auth : OrdinaryAuthentic seed log) (input : Node) (answer : Digest32)
    (correct : tag input = 0 → seed input = answer) :
    OrdinaryAuthentic seed (DuplexPublicSimulator.observe log input answer) := by
  intro n d member ordinary
  rcases List.mem_cons.mp member with same | prior
  · cases same
    exact correct ordinary
  · exact auth n d prior ordinary

theorem primitiveCalls_preserves (Q : Nat) (seed : PrimitiveOracle) (ro : RawKey Q → Digest32)
    (log : DuplexPublicSimulator.PublicLog) (auth : OrdinaryAuthentic seed log) (input : Node) :
    let result := Sampling.eval (PublicCompressionCouplingMixed.oracle seed ro)
      (PublicCompressionCouplingMixed.primitiveCalls Q log input)
    OrdinaryAuthentic seed result.1 ∧ (tag input = 0 → seed input = result.2) := by
  cases hit : DuplexPublicSimulator.lookup log input with
  | some answer =>
    rw [primitiveCalls_hit Q log input answer hit]
    simp only [Sampling.eval]
    have correct : tag input = 0 → seed input = answer := auth input answer (lookup_mem hit)
    exact ⟨observe_preserves seed log auth input answer correct,correct⟩
  | none =>
    by_cases ordinary : tag input = 0
    · rw [primitiveCalls_miss Q log input ordinary hit]
      change OrdinaryAuthentic seed
        (DuplexPublicSimulator.observe log input (seed input)) ∧
        (tag input = 0 → seed input = seed input)
      exact ⟨observe_preserves seed log auth input (seed input) (fun _ => rfl),fun _ => rfl⟩
    · unfold PublicCompressionCouplingMixed.primitiveCalls
      rw [hit]
      cases key : DuplexPublicSimulator.privateKey Q log input <;>
        simp only [Sampling.eval,PublicCompressionCouplingMixed.oracle]
      · exact ⟨observe_preserves seed log auth input (seed input) (fun h => (ordinary h).elim),
          fun h => (ordinary h).elim⟩
      · exact ⟨observe_preserves seed log auth input (ro _) (fun h => (ordinary h).elim),
          fun h => (ordinary h).elim⟩

def AuthenticObservations (seed : PrimitiveOracle) (seen : List Observation) : Prop :=
  ∀ purpose input answer, (⟨.primitive purpose input,answer⟩ : Observation) ∈ seen →
    tag input = 0 → seed input = answer

/-- Adaptive continuations and arbitrary nonordinary/construction queries are
allowed. Each cached ordinary hit is justified by the preceding invariant. -/
theorem compile_authentic {R : Type} (Q : Nat) (seed : PrimitiveOracle)
    (ro : RawKey Q → Digest32) (iv : Digest32) (log : DuplexPublicSimulator.PublicLog)
    (auth : OrdinaryAuthentic seed log) (program : Program R) (remaining : Nat)
    (cap : remaining ≤ Q) (counted : Counts remaining program) :
    AuthenticObservations seed
      (Sampling.eval (PublicCompressionCouplingMixed.oracle seed ro)
        (PublicCompressionCouplingMixed.compile Q iv log program remaining cap counted)).observations := by
  induction program generalizing log remaining with
  | done => simp [PublicCompressionCouplingMixed.compile,Sampling.eval,AuthenticObservations]
  | ask query next ih =>
    cases query with
    | primitive purpose input =>
      simp only [PublicCompressionCouplingMixed.compile,Sampling.eval_pad,Sampling.eval_bind,
        PublicCompressionCouplingMixed.Computation.eval_map,DuplexRawProgram.observe]
      have step := primitiveCalls_preserves Q seed ro log auth input
      let result := Sampling.eval (PublicCompressionCouplingMixed.oracle seed ro)
        (PublicCompressionCouplingMixed.primitiveCalls Q log input)
      have tail := ih result.2 result.1 step.1 (remaining-1) (by omega) (counted.2 result.2)
      intro purpose' input' answer member ordinary
      rcases List.mem_cons.mp member with same | prior
      · cases same
        exact step.2 ordinary
      · exact tail purpose' input' answer prior ordinary
    | construction coordinate valid =>
      simp only [PublicCompressionCouplingMixed.compile,Sampling.eval_pad,Sampling.eval,
        PublicCompressionCouplingMixed.oracle,PublicCompressionCouplingMixed.Computation.eval_map,
        DuplexRawProgram.observe]
      have tail := ih
        (ro (constructionKey Q iv coordinate (counted.1.trans cap))) log auth
        (remaining-pathCost coordinate) (by omega)
        (counted.2 (ro (constructionKey Q iv coordinate (counted.1.trans cap))))
      intro purpose input answer member ordinary
      rcases List.mem_cons.mp member with same | prior
      · cases same
      · exact tail purpose input answer prior ordinary

theorem compile_empty_authentic {R : Type} (Q : Nat) (seed : PrimitiveOracle)
    (ro : RawKey Q → Digest32) (iv : Digest32) (program : Program R) (remaining : Nat)
    (cap : remaining ≤ Q) (counted : Counts remaining program) :
    AuthenticObservations seed
      (Sampling.eval (PublicCompressionCouplingMixed.oracle seed ro)
        (PublicCompressionCouplingMixed.compile Q iv [] program remaining cap counted)).observations :=
  compile_authentic Q seed ro iv [] (by simp [OrdinaryAuthentic]) program remaining cap counted

/-- Any relevant observation prefix, including a capture boundary, inherits
ordinary authenticity; cached hits need not appear in the physical draw trace. -/
theorem observations_prefix {seed : PrimitiveOracle} {seen earlier : List Observation}
    (auth : AuthenticObservations seed seen) (included : ∀ o ∈ earlier, o ∈ seen) :
    AuthenticObservations seed earlier := by
  intro purpose input answer member
  exact auth purpose input answer (included _ member)

/-- A public Merkle interpreter receives relevant ordinary observations, not
construction answers or a hidden oracle table. Repetitions are retained. -/
def ordinaryObservations (seen : List Observation) : PublicMerkleLog.PublicLog :=
  seen.filterMap fun observation => match observation.query with
    | .primitive _ input =>
      if tag input = 0 then some (input,observation.answer) else none
    | .construction _ _ => none

theorem ordinaryObservations_authentic (seed : PrimitiveOracle) (seen : List Observation)
    (auth : AuthenticObservations seed seen) :
    PublicMerkleLog.AuthenticLog seed (ordinaryObservations seen) := by
  intro n d member
  obtain ⟨observation,present,record⟩ := List.mem_filterMap.mp member
  rcases observation with ⟨query,answer⟩
  cases query with
  | construction coordinate valid => simp at record
  | primitive purpose input =>
    by_cases ordinary : tag input = 0
    · simp only [ordinary,↓reduceIte,Option.some.injEq,Prod.mk.injEq] at record
      rcases record with ⟨rfl,rfl⟩
      exact auth purpose input answer present ordinary
    · simp [ordinary] at record

theorem observation_parse_seed (seed : PrimitiveOracle) (seen : List Observation)
    (auth : AuthenticObservations seed seen) (n : Node) (d : Digest32) (bytes : List Byte)
    (parsed : PublicMerkleLog.parse (ordinaryObservations seen) n d = some bytes) :
    PublicMerkleLog.hash seed bytes = d :=
  PublicMerkleLog.parse_authentic seed (ordinaryObservations seen)
    (ordinaryObservations_authentic seed seen auth) n d bytes parsed

section GroupedPrefix
open PCSBCSSourceRootCapture
variable {p : ParameterBounds.Profile} {Q : Nat} {iv : Digest32} {boundary : Nat}
local notation "Keys" => PCSBCSSourceRootCapture.Key (p := p) (Q := Q) (iv := iv) (boundary := boundary)
local notation "Answers" => PCSBCSSourceRootCapture.Answer (p := p) (Q := Q) (iv := iv) (boundary := boundary)

/-- Each actual physical seed event is authentic, independently of its tag.
This is a coordinatewise property of the literal partition split, not a
whole-game AuthenticLog premise. -/
theorem ordinaryRecord_split (seed : PrimitiveOracle) (ro : RawKey Q → Digest32) (key : Keys) :
    PublicMerkleLog.AuthenticLog seed
      (ordinaryRecord ⟨key,
        (PCSBCSChallengeOracle.EnteredPacket.partition (p := p) (Q := Q) (iv := iv)
          (boundary := boundary)).split (PublicCompressionCouplingMixed.oracle seed ro) key⟩) := by
  cases key with
  | inl packet => simp [ordinaryRecord,PublicMerkleLog.AuthenticLog]
  | inr other =>
    cases raw : other.val with
    | inl input =>
      simp [ordinaryRecord,RawOracleCoupling.Partition.split,raw,
        PublicCompressionCouplingMixed.oracle,PublicMerkleLog.AuthenticLog]
    | inr rawKey => simp [ordinaryRecord,raw,PublicMerkleLog.AuthenticLog]

theorem authentic_fold (seed : PrimitiveOracle) (events : List (Sigma Answers))
    (each : ∀ event ∈ events, PublicMerkleLog.AuthenticLog seed (ordinaryRecord event))
    (log : DuplexPublicSimulator.PublicLog) (auth : PublicMerkleLog.AuthenticLog seed log) :
    PublicMerkleLog.AuthenticLog seed
      (events.foldl (fun prior event => ordinaryRecord event ++ prior) log) := by
  induction events generalizing log with
  | nil => exact auth
  | cons event rest ih =>
    apply ih
    · intro e member
      exact each e (List.mem_cons_of_mem _ member)
    · intro n d member
      rcases List.mem_append.mp member with current | prior
      · exact each event (List.mem_cons_self) n d current
      · exact auth n d prior

theorem ordinaryPrefix_authentic (seed : PrimitiveOracle) (events : List (Sigma Answers))
    (each : ∀ event ∈ events, PublicMerkleLog.AuthenticLog seed (ordinaryRecord event)) :
    PublicMerkleLog.AuthenticLog seed (ordinaryPrefix events) :=
  authentic_fold seed events each [] (by simp [PublicMerkleLog.AuthenticLog])

/-- Literal pre-first-mention physical events suffice to authenticate the
captured public prefix. No assertion about captured leaf availability follows. -/
theorem firstMention_authentic {R : Type} {count : Nat}
    (seed : PrimitiveOracle) (ro : RawKey Q → Digest32)
    (addresses : Keys → List PCSBCSSourceRootReferences.Reference)
    (ref : PCSBCSSourceRootReferences.Reference) (program : Sampling Keys Answers R count)
    (events : List (Sigma Answers))
    (found : PCSBCSFirstRootDisclosure.firstMention addresses ref program
      ((PCSBCSChallengeOracle.EnteredPacket.partition (p := p) (Q := Q) (iv := iv)
        (boundary := boundary)).split (PublicCompressionCouplingMixed.oracle seed ro)) = some events) :
    PublicMerkleLog.AuthenticLog seed (ordinaryPrefix events) := by
  apply ordinaryPrefix_authentic
  induction program generalizing events with
  | ret result => simp [PCSBCSFirstRootDisclosure.firstMention] at found
  | draw key next ih =>
    unfold PCSBCSFirstRootDisclosure.firstMention at found
    split at found
    · have empty : events = [] := (Option.some.inj found).symm
      subst events
      simp
    · cases tailFound : PCSBCSFirstRootDisclosure.firstMention addresses ref
        (next ((PCSBCSChallengeOracle.EnteredPacket.partition (p := p) (Q := Q) (iv := iv)
          (boundary := boundary)).split (PublicCompressionCouplingMixed.oracle seed ro) key))
        ((PCSBCSChallengeOracle.EnteredPacket.partition (p := p) (Q := Q) (iv := iv)
          (boundary := boundary)).split (PublicCompressionCouplingMixed.oracle seed ro)) with
      | none => simp [tailFound] at found
      | some tail =>
        simp only [tailFound,Option.map_some,Option.some.injEq] at found
        subst events
        intro event member
        rcases List.mem_cons.mp member with same | prior
        · subst event
          exact ordinaryRecord_split seed ro key
        · exact ih _ tail tailFound event prior

theorem firstMention_parse_seed {R : Type} {count : Nat}
    (seed : PrimitiveOracle) (ro : RawKey Q → Digest32)
    (addresses : Keys → List PCSBCSSourceRootReferences.Reference)
    (ref : PCSBCSSourceRootReferences.Reference) (program : Sampling Keys Answers R count)
    (events : List (Sigma Answers))
    (found : PCSBCSFirstRootDisclosure.firstMention addresses ref program
      ((PCSBCSChallengeOracle.EnteredPacket.partition (p := p) (Q := Q) (iv := iv)
        (boundary := boundary)).split (PublicCompressionCouplingMixed.oracle seed ro)) = some events)
    (n : Node) (d : Digest32) (bytes : List Byte)
    (parsed : PublicMerkleLog.parse (ordinaryPrefix events) n d = some bytes) :
    PublicMerkleLog.hash seed bytes = d :=
  PublicMerkleLog.parse_authentic seed (ordinaryPrefix events)
    (firstMention_authentic seed ro addresses ref program events found) n d bytes parsed

/-- The native-reply bridge's literal sourceLog is authentic under the exact
mixed table split. An absent capture gives an empty authentic log, not a full
Merkle image or an accepted opening. -/
theorem sourceLog_authentic {R : Type} {count : Nat}
    (seed : PrimitiveOracle) (ro : RawKey Q → Digest32)
    (addresses : Keys → List PCSBCSSourceRootReferences.Reference)
    (ref : PCSBCSSourceRootReferences.Reference) (program : Sampling Keys Answers R count) :
    PublicMerkleLog.AuthenticLog seed
      (PCSBCSCapturedNativeReplyBridge.sourceLog addresses ref program
        ((PCSBCSChallengeOracle.EnteredPacket.partition (p := p) (Q := Q) (iv := iv)
          (boundary := boundary)).split (PublicCompressionCouplingMixed.oracle seed ro))) := by
  unfold PCSBCSCapturedNativeReplyBridge.sourceLog
  cases found : PCSBCSFirstRootDisclosure.firstMention addresses ref program
      ((PCSBCSChallengeOracle.EnteredPacket.partition (p := p) (Q := Q) (iv := iv)
        (boundary := boundary)).split (PublicCompressionCouplingMixed.oracle seed ro)) with
  | none => simp [ordinaryPrefix,PublicMerkleLog.AuthenticLog]
  | some events =>
    exact firstMention_authentic seed ro addresses ref program events found
end GroupedPrefix

#print axioms plan_privateKey_none
#print axioms execute_miss
#print axioms execute_hit
#print axioms primitiveCalls_preserves
#print axioms compile_empty_authentic
#print axioms firstMention_authentic
#print axioms observation_parse_seed
#print axioms firstMention_parse_seed
#print axioms sourceLog_authentic
end Whir.PCSBCSMerkleSeedProjection
