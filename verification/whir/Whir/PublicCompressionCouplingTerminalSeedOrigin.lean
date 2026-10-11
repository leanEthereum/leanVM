import Whir.PublicCompressionCouplingPublicCache

/-! A terminal Seed coordinate in the causal cache can only come from an
actual public fallback call. Hidden construction prefix nodes are nonterminal;
thus causal/private sampling cannot manufacture cached-miss provenance. -/
namespace Whir.PublicCompressionCouplingRecognition
open FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame DuplexPublicSimulator
open PublicCompressionCouplingMixed RawOracleCoupling
open TypedOracleCompiler (Sampling)
set_option backward.isDefEq.respectTransparency false

 theorem bodyCalls_no_terminal (Q : Nat) (seedTable : Seed) (ro : RawKey Q → Digest32)
    (iv : Digest32) (coordinate : Coordinate) (valid : DuplexEncoding.Admissible coordinate)
    (input : Node) (terminal : isTerminal input) (answer : Digest32) :
    (⟨.inl input,answer⟩ : Sigma (fun _ : Key Q => Digest32)) ∉
      (Sampling.execute (oracle seedTable ro)
        (bodyCalls Q iv (DuplexEncoding.plan coordinate).dropLast)).2 := by
  rw [bodyCalls_trace]
  intro member
  obtain ⟨entry,record,equal⟩ := List.mem_map.mp member
  have nodes : entry.1=input := Sum.inl.inj (congrArg Sigma.fst equal)
  rcases entry with ⟨node,digest⟩
  dsimp only at nodes
  subst node
  rw [inspection_body_nodes Q seedTable ro iv coordinate valid] at record
  obtain ⟨node,nodeMember,equal⟩ := List.mem_map.mp record
  have nodes := congrArg Prod.fst equal
  dsimp only at nodes
  subst node
  have body := (traceHistory_valid (compressionOf seedTable) iv coordinate.history valid.1).1.body
  exact body_no_terminal body input (List.mem_reverse.mp nodeMember) terminal

 theorem causalConstruction_no_terminal_seed (Q : Nat) (seedTable : Seed) (ro : RawKey Q → Digest32)
    (iv : Digest32) (coordinate : Coordinate) (valid : DuplexEncoding.Admissible coordinate)
    (budget : pathCost coordinate ≤ Q) (input : Node) (terminal : isTerminal input) (answer : Digest32) :
    (⟨.inl input,answer⟩ : Sigma (fun _ : Key Q => Digest32)) ∉
      (Sampling.execute (oracle seedTable ro) (causalConstruction Q iv coordinate valid budget)).2 := by
  rw [causalConstruction_trace,List.mem_append]
  rintro (prefixMember | rawMember)
  · exact bodyCalls_no_terminal Q seedTable ro iv coordinate valid input terminal answer prefixMember
  · have equal := List.mem_singleton.mp rawMember
    have keys := congrArg Sigma.fst equal
    cases keys

 theorem causal_terminal_seed_public_draw (Q : Nat) (seedTable : Seed) (ro : RawKey Q → Digest32)
    (iv : Digest32) (log : PublicLog) (p : Program R) (remaining : Nat)
    (cap : remaining ≤ Q) (counted : Counts remaining p) (input : Node)
    (terminal : isTerminal input) (answer : Digest32)
    (member : (⟨.inl input,answer⟩ : Sigma (fun _ : Key Q => Digest32)) ∈
      (Sampling.execute (oracle seedTable ro) (causalCompile Q iv log p remaining cap counted)).2) :
    (⟨.inl input,answer⟩ : Sigma (fun _ : Key Q => Digest32)) ∈
      (Sampling.execute (oracle seedTable ro) (compile Q iv log p remaining cap counted)).2 := by
  induction p generalizing log remaining with
  | done result => simp [causalCompile,Sampling.execute] at member
  | ask query next ih =>
    cases query with
    | primitive purpose node =>
      simp only [causalCompile,Sampling.execute_pad,Sampling.execute_bind,execute_map_trace,List.mem_append] at member
      simp only [compile,Sampling.execute_pad,Sampling.execute_bind,execute_map_trace,List.mem_append]
      rcases member with first | later
      · exact Or.inl first
      · exact Or.inr (ih _ _ _ _ _ later)
    | construction coordinate valid =>
      simp only [causalCompile,Sampling.execute_pad,Sampling.execute_bind,execute_map_trace,List.mem_append] at member
      rcases member with first | later
      · exact False.elim (causalConstruction_no_terminal_seed Q seedTable ro iv coordinate valid
          (counted.1.trans cap) input terminal answer first)
      · have publicDraw := ih _ log _ _ _ later
        simp only [causalConstruction_eval,oracle] at publicDraw
        simp only [compile,Sampling.execute_pad,Sampling.execute,execute_map_trace]
        exact List.mem_cons_of_mem _ publicDraw

 theorem actual_terminal_seed_public_cache {R : Type} (Q : Nat) [DecidableEq (Key Q)]
    (iv : Digest32) (p : Program R)
    (counted : Counts Q p) (seedTable : Seed) (ro : RawKey Q → Digest32)
    {input : Node} (terminal : isTerminal input) {answer : Digest32}
    (stored : (Sampling.eval (oracle seedTable ro)
      (memo (causalCompile Q iv [] p Q (by rfl) counted) (fun _ => none))).2 (.inl input)=some answer) :
    (Sampling.eval (oracle seedTable ro)
      (memo (compile Q iv [] p Q (by rfl) counted) (fun _ => none))).2 (.inl input)=some answer := by
  have causal := PublicCompressionCouplingTargetCache.memo_empty_trace _ _ stored
  have publicDraw := causal_terminal_seed_public_draw Q seedTable ro iv [] p Q (by rfl) counted input terminal answer causal
  exact PublicCompressionCouplingTargetCache.trace_recorded _ _ (fun _ => none)
    (by intro key digest impossible; cases impossible) publicDraw

#print axioms actual_terminal_seed_public_cache
end Whir.PublicCompressionCouplingRecognition
