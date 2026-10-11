import Whir.PublicCompressionCouplingCoordinates

/-! Public record provenance in the pinned simulator's actual mixed sampling
trace. Cached primitive calls retain their original witness; recognized terminal
coordinates have actual seed trees, not an asserted public/primitive coupling. -/
namespace Whir.PublicCompressionCouplingRecognition
open FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame DuplexPublicSimulator
open PublicCompressionCouplingMixed
open TypedOracleCompiler (Sampling)

abbrev MixedTrace (Q : Nat) := List (Sigma (fun _ : Key Q => Digest32))

def TraceWitnessed (Q : Nat) (seed : Seed) (trace : MixedTrace Q) (log : PublicLog) : Prop :=
  ∀ input answer, (input,answer) ∈ log →
    ∃ key, CoordinateWitness Q seed input key ∧ (⟨key,answer⟩ : Sigma (fun _ : Key Q => Digest32)) ∈ trace

 theorem TraceWitnessed.mono {Q : Nat} {seed : Seed} {a b : MixedTrace Q} {log : PublicLog}
    (witnessed : TraceWitnessed Q seed a log) (subset : ∀ entry ∈ a, entry ∈ b) :
    TraceWitnessed Q seed b log := by
  intro input answer member
  obtain ⟨key,coordinate,hit⟩ := witnessed input answer member
  exact ⟨key,coordinate,subset _ hit⟩

 theorem TraceWitnessed.observe {Q : Nat} {seed : Seed} {trace : MixedTrace Q} {log : PublicLog}
    (witnessed : TraceWitnessed Q seed trace log) (input : Node) (answer : Digest32) (key : Key Q)
    (coordinate : CoordinateWitness Q seed input key)
    (hit : (⟨key,answer⟩ : Sigma (fun _ : Key Q => Digest32)) ∈ trace) :
    TraceWitnessed Q seed trace (observe log input answer) := by
  intro node digest member
  rcases List.mem_cons.mp member with equal | old
  · cases equal
    exact ⟨key,coordinate,hit⟩
  · exact witnessed node digest old

 theorem execute_map_trace {Q n : Nat} {R S : Type} (table : Key Q → Digest32)
    (f : R → S) (p : Computation Q R n) :
    (Sampling.execute table (PublicCompressionCouplingMixed.Computation.map f p)).2 = (Sampling.execute table p).2 := by
  induction p with
  | ret r => rfl
  | draw key next ih => simpa only [PublicCompressionCouplingMixed.Computation.map,Sampling.execute] using congrArg (⟨key,table key⟩ :: ·) (ih (table key))

 theorem primitiveCalls_traceWitnessed (Q : Nat) (seedTable : Seed) (ro : RawKey Q → Digest32)
    (log : PublicLog) (trace : MixedTrace Q) (auth : NonterminalAuthentic seedTable log)
    (witnessed : TraceWitnessed Q seedTable trace log) (input : Node) :
    TraceWitnessed Q seedTable
      (trace ++ (Sampling.execute (oracle seedTable ro) (primitiveCalls Q log input)).2)
      (Sampling.eval (oracle seedTable ro) (primitiveCalls Q log input)).1 := by
  cases hit : lookup log input with
  | some answer =>
    simp only [primitiveCalls,hit,Sampling.execute,Sampling.eval,List.append_nil]
    obtain ⟨key,coordinate,member⟩ := witnessed input answer (lookup_mem hit)
    exact TraceWitnessed.observe witnessed input answer key coordinate member
  | none =>
    cases found : privateKey Q log input with
    | some key =>
      simp only [primitiveCalls,hit,found,Sampling.execute,Sampling.eval,oracle]
      apply TraceWitnessed.observe
        (TraceWitnessed.mono witnessed (fun entry member => List.mem_append_left _ member))
        input (ro key) (.inr key) (privateKey_coordinateWitness seedTable auth found)
      exact List.mem_append_right _ (by simp)
    | none =>
      simp only [primitiveCalls,hit,found,Sampling.execute,Sampling.eval,oracle]
      apply TraceWitnessed.observe
        (TraceWitnessed.mono witnessed (fun entry member => List.mem_append_left _ member))
        input (seedTable input) (.inl input) CoordinateWitness.fallback
      exact List.mem_append_right _ (by simp)

 theorem primitiveCalls_authentic (Q : Nat) (seedTable : Seed) (ro : RawKey Q → Digest32)
    (log : PublicLog) (auth : NonterminalAuthentic seedTable log) (input : Node) :
    NonterminalAuthentic seedTable
      (Sampling.eval (oracle seedTable ro) (primitiveCalls Q log input)).1 := by
  have result := answer_nonterminal_authentic Q ro ⟨seedTable,log⟩ auth input
  simpa only [primitiveCalls_actual] using result

 theorem primitiveCalls_log (Q : Nat) (table : Key Q → Digest32)
    (log : PublicLog) (input : Node) :
    (Sampling.eval table (primitiveCalls Q log input)).1 =
      DuplexPublicSimulator.observe log input (Sampling.eval table (primitiveCalls Q log input)).2 := by
  cases hit : lookup log input with
  | some answer => simp only [primitiveCalls,hit,Sampling.eval]
  | none => cases found : privateKey Q log input <;>
      simp only [primitiveCalls,hit,found,Sampling.eval]

set_option backward.isDefEq.respectTransparency false in
 theorem compile_traceWitnessed (Q : Nat) (seedTable : Seed) (ro : RawKey Q → Digest32)
    (iv : Digest32) (log : PublicLog) (trace : MixedTrace Q) (p : Program R)
    (remaining : Nat) (cap : remaining ≤ Q) (counted : Counts remaining p)
    (auth : NonterminalAuthentic seedTable log) (witnessed : TraceWitnessed Q seedTable trace log) :
    TraceWitnessed Q seedTable
      (trace ++ (Sampling.execute (oracle seedTable ro) (compile Q iv log p remaining cap counted)).2)
      (finalLog log (Sampling.eval (oracle seedTable ro) (compile Q iv log p remaining cap counted)).observations) := by
  induction p generalizing log trace remaining with
  | done result => simpa only [compile,Sampling.execute,Sampling.eval,finalLog,List.append_nil] using witnessed
  | ask query next ih =>
    cases query with
    | primitive purpose input =>
      have nextWitness := primitiveCalls_traceWitnessed Q seedTable ro log trace auth witnessed input
      have nextAuth := primitiveCalls_authentic Q seedTable ro log auth input
      have result := ih (Sampling.eval (oracle seedTable ro) (primitiveCalls Q log input)).2
        (Sampling.eval (oracle seedTable ro) (primitiveCalls Q log input)).1
        (trace ++ (Sampling.execute (oracle seedTable ro) (primitiveCalls Q log input)).2)
        (remaining-1) (by omega) (counted.2 _) nextAuth nextWitness
      simpa only [compile,Sampling.execute_pad,Sampling.execute_bind,execute_map_trace,
        Sampling.eval_pad,Sampling.eval_bind,PublicCompressionCouplingMixed.Computation.eval_map,DuplexRawProgram.observe,
        finalLog,List.append_assoc,primitiveCalls_log] using result
    | construction coordinate valid =>
      have nextWitness := TraceWitnessed.mono witnessed (fun entry member =>
        List.mem_append_left [⟨.inr (constructionKey Q iv coordinate (counted.1.trans cap)),
          ro (constructionKey Q iv coordinate (counted.1.trans cap))⟩] member)
      have result := ih (ro (constructionKey Q iv coordinate (counted.1.trans cap))) log
        (trace ++ [⟨.inr (constructionKey Q iv coordinate (counted.1.trans cap)),
          ro (constructionKey Q iv coordinate (counted.1.trans cap))⟩])
        (remaining-pathCost coordinate) (by omega) (counted.2 _) auth nextWitness
      simpa only [compile,Sampling.execute_pad,Sampling.execute,execute_map_trace,
        Sampling.eval_pad,Sampling.eval,PublicCompressionCouplingMixed.Computation.eval_map,oracle,DuplexRawProgram.observe,
        finalLog,List.append_assoc,List.cons_append,List.nil_append] using result

 theorem primitiveCalls_seed_record (Q : Nat) (seedTable : Seed) (ro : RawKey Q → Digest32)
    (log : PublicLog) (input node : Node) (answer : Digest32)
    (member : (⟨.inl node,answer⟩ : Sigma (fun _ : Key Q => Digest32)) ∈
      (Sampling.execute (oracle seedTable ro) (primitiveCalls Q log input)).2) :
    (node,answer) ∈ (Sampling.eval (oracle seedTable ro) (primitiveCalls Q log input)).1 := by
  cases hit : lookup log input with
  | some digest => simp only [primitiveCalls,hit,Sampling.execute,List.not_mem_nil] at member
  | none =>
    cases found : privateKey Q log input with
    | some key =>
      simp [primitiveCalls,hit,found,Sampling.execute] at member
    | none =>
      simp only [primitiveCalls,hit,found,Sampling.execute,oracle,List.mem_cons,
        List.not_mem_nil,or_false] at member
      have nodes : node = input := by
        simpa using congrArg Sigma.fst member
      subst node
      have answers : answer = seedTable input := by simpa using member
      subst answer
      simp [primitiveCalls,hit,found,Sampling.eval,oracle,DuplexPublicSimulator.observe]

set_option backward.isDefEq.respectTransparency false in
/-- Conversely, every seed coordinate sampled in the actual public phase is
a public primitive record. Construction requests do not sample hidden seeds. -/
 theorem compile_seed_record (Q : Nat) (seedTable : Seed) (ro : RawKey Q → Digest32)
    (iv : Digest32) (log : PublicLog) (p : Program R) (remaining : Nat)
    (cap : remaining ≤ Q) (counted : Counts remaining p) (node : Node) (answer : Digest32)
    (member : (⟨.inl node,answer⟩ : Sigma (fun _ : Key Q => Digest32)) ∈
      (Sampling.execute (oracle seedTable ro) (compile Q iv log p remaining cap counted)).2) :
    (node,answer) ∈
      finalLog log (Sampling.eval (oracle seedTable ro) (compile Q iv log p remaining cap counted)).observations := by
  induction p generalizing log remaining with
  | done result => simp [compile,Sampling.execute] at member
  | ask query next ih =>
    cases query with
    | primitive purpose input =>
      simp only [compile,Sampling.execute_pad,Sampling.execute_bind,execute_map_trace,
        List.mem_append] at member
      simp only [compile,Sampling.eval_pad,Sampling.eval_bind,PublicCompressionCouplingMixed.Computation.eval_map,
        DuplexRawProgram.observe,finalLog]
      rw [← primitiveCalls_log Q (oracle seedTable ro) log input]
      rcases member with first | later
      · apply finalLog_contains
        exact primitiveCalls_seed_record Q seedTable ro log input node answer first
      · exact ih _ _ _ _ _ later
    | construction coordinate valid =>
      simp only [compile,Sampling.execute_pad,Sampling.execute,execute_map_trace,List.mem_cons] at member
      rcases member with impossible | later
      · have keys := congrArg Sigma.fst impossible
        cases keys
      · simpa only [compile,Sampling.eval_pad,Sampling.eval,PublicCompressionCouplingMixed.Computation.eval_map,oracle,
          DuplexRawProgram.observe,finalLog] using ih _ log _ _ _ later

#print axioms compile_seed_record

#print axioms compile_traceWitnessed
end Whir.PublicCompressionCouplingRecognition
