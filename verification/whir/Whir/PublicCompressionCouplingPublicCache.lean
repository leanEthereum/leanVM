import Whir.PublicCompressionCouplingPublicTrace
import Whir.PublicCompressionCouplingCausal
import Whir.PublicCompressionCouplingTargetCache
import Whir.PublicCompressionCouplingBirthdayCache
import Whir.PublicCompressionCouplingPrefixTrace

/-! Public record witnesses in the literal causal ideal memo cache, and the
actual derived no-output-collision consequence of the causal birthday alarm. -/
namespace Whir.PublicCompressionCouplingRecognition
open FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame DuplexPublicSimulator
open PublicCompressionCouplingMixed RawOracleCoupling
open TypedOracleCompiler (Sampling)

 theorem causalConstruction_trace (Q : Nat) (table : Key Q → Digest32) (iv : Digest32)
    (coordinate : Coordinate) (valid : DuplexEncoding.Admissible coordinate)
    (budget : pathCost coordinate ≤ Q) :
    (Sampling.execute table (causalConstruction Q iv coordinate valid budget)).2 =
      (Sampling.execute table (bodyCalls Q iv (DuplexEncoding.plan coordinate).dropLast)).2 ++
      [⟨.inr (constructionKey Q iv coordinate budget),table (.inr (constructionKey Q iv coordinate budget))⟩] := by
  simp only [causalConstruction,Sampling.execute_pad,Sampling.execute_bind,Sampling.execute]

set_option backward.isDefEq.respectTransparency false in
 theorem causalCompile_trace_covers (Q : Nat) (table : Key Q → Digest32) (iv : Digest32)
    (log : PublicLog) (p : Program R) (remaining : Nat) (cap : remaining ≤ Q)
    (counted : Counts remaining p) {entry : Sigma (fun _ : Key Q => Digest32)}
    (member : entry ∈ (Sampling.execute table (compile Q iv log p remaining cap counted)).2) :
    entry ∈ (Sampling.execute table (causalCompile Q iv log p remaining cap counted)).2 := by
  induction p generalizing log remaining with
  | done result => simp [compile,Sampling.execute] at member
  | ask query next ih =>
    cases query with
    | primitive purpose input =>
      simp only [compile,Sampling.execute_pad,Sampling.execute_bind,execute_map_trace,List.mem_append] at member
      simp only [causalCompile,Sampling.execute_pad,Sampling.execute_bind,execute_map_trace,List.mem_append]
      rcases member with first | later
      · exact Or.inl first
      · exact Or.inr (ih _ _ _ _ _ later)
    | construction coordinate valid =>
      simp only [compile,Sampling.execute_pad,Sampling.execute,execute_map_trace,List.mem_cons] at member
      simp only [causalCompile,Sampling.execute_pad,Sampling.execute_bind,execute_map_trace,
        causalConstruction_trace,causalConstruction_eval,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
      rcases member with first | later
      · exact Or.inl (Or.inr first)
      · exact Or.inr (ih _ log _ _ _ later)

open Classical in
 theorem actual_causal_cache_witnessed {R : Type} (Q : Nat) (iv : Digest32)
    (p : Program R) (counted : Counts Q p) (seedTable : Seed) (ro : RawKey Q → Digest32) :
    Witnessed Q seedTable
      (Sampling.eval (oracle seedTable ro)
        (memo (causalCompile Q iv [] p Q (by rfl) counted) (fun _ => none))).2
      (finalLog [] (Sampling.eval (oracle seedTable ro)
        (compile Q iv [] p Q (by rfl) counted)).observations) := by
  have witnessed := compile_traceWitnessed Q seedTable ro iv [] [] p Q (by rfl) counted
    (by intro n d member; cases member) (by intro n d member; cases member)
  intro input answer member
  obtain ⟨key,coordinate,record⟩ := witnessed input answer member
  refine ⟨key,coordinate,?_⟩
  apply PublicCompressionCouplingTargetCache.trace_recorded _ _ (fun _ => none)
    (by intro k d impossible; cases impossible)
  apply causalCompile_trace_covers
  simpa only [List.nil_append] using record

open Classical in
 theorem actual_causal_public_noOutputCollision {R : Type} (Q : Nat) (iv : Digest32)
    (p : Program R) (counted : Counts Q p) (seedTable : Seed) (ro : RawKey Q → Digest32)
    (quiet : PublicCompressionCouplingBirthday.alarm (oracle seedTable ro)
      (causalCompile Q iv [] p Q (by rfl) counted) (fun _ => none) ∅ = false) :
    ¬OutputCollision (finalLog [] (Sampling.eval (oracle seedTable ro)
      (compile Q iv [] p Q (by rfl) counted)).observations) := by
  apply Witnessed.no_outputCollision (actual_causal_cache_witnessed Q iv p counted seedTable ro)
  exact PublicCompressionCouplingBirthdayCache.birthday_cache_injective _ _ quiet

 theorem causalConstruction_prefix_record (Q : Nat) (table : Key Q → Digest32)
    (iv : Digest32) (coordinate : Coordinate) (valid : DuplexEncoding.Admissible coordinate)
    (budget : pathCost coordinate ≤ Q) {node : Node} {answer : Digest32}
    (record : (node,answer) ∈ (Sampling.eval table
      (causalConstruction Q iv coordinate valid budget)).prefixLog) :
    (⟨.inl node,answer⟩ : Sigma (fun _ : Key Q => Digest32)) ∈
      (Sampling.execute table (causalConstruction Q iv coordinate valid budget)).2 := by
  simp only [causalConstruction_eval] at record
  rw [causalConstruction_trace]
  apply List.mem_append_left
  rw [bodyCalls_trace]
  exact List.mem_map.mpr ⟨(node,answer),record,rfl⟩

set_option backward.isDefEq.respectTransparency false in
 theorem causalCompile_prefix_record (Q : Nat) (table : Key Q → Digest32)
    (iv : Digest32) (log : PublicLog) (p : Program R) (remaining : Nat)
    (cap : remaining ≤ Q) (counted : Counts remaining p) {construction : InspectedConstruction}
    (member : construction ∈ (Sampling.eval table (causalCompile Q iv log p remaining cap counted)).2)
    {node : Node} {answer : Digest32} (record : (node,answer) ∈ construction.prefixLog) :
    (⟨.inl node,answer⟩ : Sigma (fun _ : Key Q => Digest32)) ∈
      (Sampling.execute table (causalCompile Q iv log p remaining cap counted)).2 := by
  induction p generalizing log remaining with
  | done result => simp [causalCompile,Sampling.eval] at member
  | ask query next ih =>
    cases query with
    | primitive purpose input =>
      simp only [causalCompile,Sampling.eval_pad,Sampling.eval_bind,
        PublicCompressionCouplingMixed.Computation.eval_map] at member
      simp only [causalCompile,Sampling.execute_pad,Sampling.execute_bind,execute_map_trace,List.mem_append]
      exact Or.inr (ih _ _ _ _ _ member)
    | construction coordinate valid =>
      simp only [causalCompile,Sampling.eval_pad,Sampling.eval_bind,
        PublicCompressionCouplingMixed.Computation.eval_map,List.mem_cons] at member
      simp only [causalCompile,Sampling.execute_pad,Sampling.execute_bind,execute_map_trace,List.mem_append]
      rcases member with equal | later
      · subst construction
        exact Or.inl (causalConstruction_prefix_record Q table iv coordinate valid _ record)
      · exact Or.inr (ih _ log _ _ _ later)

open Classical in
 theorem actual_causal_prefix_stored {R : Type} (Q : Nat) (iv : Digest32)
    (p : Program R) (counted : Counts Q p) (table : Key Q → Digest32)
    {construction : InspectedConstruction}
    (member : construction ∈ (Sampling.eval table (causalCompile Q iv [] p Q (by rfl) counted)).2)
    {node : Node} {answer : Digest32} (record : (node,answer) ∈ construction.prefixLog) :
    (Sampling.eval table (memo (causalCompile Q iv [] p Q (by rfl) counted)
      (fun _ => none))).2 (.inl node) = some answer := by
  apply PublicCompressionCouplingTargetCache.trace_recorded _ _ (fun _ => none)
    (by intro key digest impossible; cases impossible)
  exact causalCompile_prefix_record Q table iv [] p Q (by rfl) counted member record

 theorem CoordinateWitness.nonterminal_coordinate {Q : Nat} {seedTable : Seed}
    {input : Node} {key : Key Q} (coordinate : CoordinateWitness Q seedTable input key)
    (nonterminal : ¬isTerminal input) : key = .inl input := by
  cases coordinate with
  | fallback => rfl
  | terminal raw rest complete tree extracted =>
    have parsed := (complete?_correct _).mpr complete
    simp only [complete?,Bool.and_eq_true,decide_eq_true_eq] at parsed
    exact False.elim (nonterminal parsed.1)

 theorem Witnessed.nonterminal_stored {Q : Nat} {seedTable : Seed}
    {cache : Key Q → Option Digest32} {log : PublicLog}
    (witnessed : Witnessed Q seedTable cache log) {input : Node} {answer : Digest32}
    (member : (input,answer) ∈ log) (nonterminal : ¬isTerminal input) :
    cache (.inl input) = some answer := by
  obtain ⟨key,coordinate,stored⟩ := witnessed input answer member
  rwa [CoordinateWitness.nonterminal_coordinate coordinate nonterminal] at stored

#print axioms Witnessed.nonterminal_stored

#print axioms actual_causal_prefix_stored

#print axioms actual_causal_cache_witnessed
#print axioms actual_causal_public_noOutputCollision
end Whir.PublicCompressionCouplingRecognition
