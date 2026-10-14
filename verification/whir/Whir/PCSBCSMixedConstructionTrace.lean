import Whir.PCSBCSAtomicAllocationTrace
import Whir.PublicCompressionCouplingMixed

/-! Literal construction observations in the mixed source compiler retain
actual raw draw provenance, including primitive simulator work between them. -/
set_option autoImplicit false
namespace Whir.PCSBCSMixedConstructionTrace
open FiatShamirGame DuplexFraming DuplexModeGame
open TypedOracleCompiler (Sampling)
open PublicCompressionCouplingMixed

theorem execute_map {Q n : Nat} {R S : Type} (table : Key Q → Digest32)
    (f : R → S) (program : Computation Q R n) :
    (Sampling.execute table (PublicCompressionCouplingMixed.Computation.map f program)).2 =
      (Sampling.execute table program).2 := by
  induction program with
  | ret result => rfl
  | draw key next ih =>
    simp only [PublicCompressionCouplingMixed.Computation.map,Sampling.execute,ih]

theorem compiled_recorded {Q : Nat} {R : Type} (seed : DuplexPublicSimulator.Seed)
    (ro : RawKey Q → Digest32) (iv : Digest32) (log : DuplexPublicSimulator.PublicLog)
    (program : Program R) (remaining : Nat) (limit : remaining ≤ Q)
    (counted : Counts remaining program) :
    ∀ (coordinate : Coordinate) (valid : DuplexEncoding.Admissible coordinate) (answer : Digest32),
      (⟨.construction coordinate valid,answer⟩ : Observation) ∈
        (Sampling.eval (oracle seed ro) (compile Q iv log program remaining limit counted)).observations →
      ∃ bound : pathCost coordinate ≤ Q,
        (⟨.inr (constructionKey Q iv coordinate bound),answer⟩ :
          Sigma (fun _ : Key Q => Digest32)) ∈
          (Sampling.execute (oracle seed ro) (compile Q iv log program remaining limit counted)).2 := by
  induction program generalizing log remaining with
  | done result => simp [compile,Sampling.eval]
  | ask query next ih =>
    cases query with
    | primitive purpose input =>
      intro coordinate valid answer member
      simp only [compile,Sampling.eval_pad,Sampling.eval_bind,PublicCompressionCouplingMixed.Computation.eval_map,
        DuplexRawProgram.observe,List.mem_cons] at member
      rcases member with impossible | later
      · cases impossible
      · obtain ⟨bound,recorded⟩ := ih
          (Sampling.eval (oracle seed ro) (primitiveCalls Q log input)).2
          (Sampling.eval (oracle seed ro) (primitiveCalls Q log input)).1
          (remaining-1) (by omega) (counted.2 _) coordinate valid answer later
        refine ⟨bound,?_⟩
        rw [compile,Sampling.execute_pad,Sampling.execute_bind,execute_map]
        exact List.mem_append_right _ recorded
    | construction requested admitted =>
      intro coordinate valid answer member
      simp only [compile,Sampling.eval_pad,Sampling.eval,PublicCompressionCouplingMixed.Computation.eval_map,
        DuplexRawProgram.observe,List.mem_cons] at member
      rcases member with same | later
      · cases same
        refine ⟨counted.1.trans limit,?_⟩
        simp only [compile,Sampling.execute_pad,Sampling.execute,execute_map]
        exact List.mem_cons_self
      · obtain ⟨bound,recorded⟩ := ih (oracle seed ro
          (.inr (constructionKey Q iv requested (counted.1.trans limit)))) log
          (remaining-pathCost requested) (by omega) (counted.2 _) coordinate valid answer later
        refine ⟨bound,?_⟩
        simp only [compile,Sampling.execute_pad,Sampling.execute,execute_map]
        exact List.mem_cons_of_mem _ recorded

theorem ideal_recorded {Q : Nat} {R : Type} (seed : DuplexPublicSimulator.Seed)
    (ro : RawKey Q → Digest32) (iv : Digest32) (log : DuplexPublicSimulator.PublicLog)
    (program : Program R) (remaining : Nat) (limit : remaining ≤ Q)
    (counted : Counts remaining program)
    (coordinate : Coordinate) (valid : DuplexEncoding.Admissible coordinate) (answer : Digest32)
    (member : (⟨.construction coordinate valid,answer⟩ : Observation) ∈
      (runIdeal (DuplexPublicSimulator.simulator Q) ro iv ⟨seed,log⟩
        program remaining limit counted).view.observations) :
    ∃ bound : pathCost coordinate ≤ Q,
      (⟨.inr (constructionKey Q iv coordinate bound),answer⟩ :
        Sigma (fun _ : Key Q => Digest32)) ∈
        (Sampling.execute (oracle seed ro) (compile Q iv log program remaining limit counted)).2 := by
  apply compiled_recorded seed ro iv log program remaining limit counted coordinate valid answer
  rw [compile_actual]
  exact member

theorem ideal_packet_recorded {Q : Nat} {R Packet : Type} {Block : Packet → Type}
    (part : RawOracleCoupling.Partition (Key Q) Packet Block)
    (seed : DuplexPublicSimulator.Seed) (ro : RawKey Q → Digest32) (iv : Digest32)
    (log : DuplexPublicSimulator.PublicLog) (program : Program R) (remaining : Nat)
    (limit : remaining ≤ Q) (counted : Counts remaining program)
    (coordinate : Coordinate) (valid : DuplexEncoding.Admissible coordinate)
    (bound : pathCost coordinate ≤ Q) (answer : Digest32) (block : Sigma Block)
    (member : (⟨.construction coordinate valid,answer⟩ : Observation) ∈
      (runIdeal (DuplexPublicSimulator.simulator Q) ro iv ⟨seed,log⟩
        program remaining limit counted).view.observations)
    (recognized : part.recognize (.inr (constructionKey Q iv coordinate bound)) = some block) :
    (⟨.inl block.1,(part.split (oracle seed ro)) (.inl block.1)⟩ :
      Sigma (part.Answer (D := Digest32))) ∈
      (Sampling.execute (part.split (oracle seed ro))
        (PCSBCSChallengeOracle.Atomic.program part
          (compile Q iv log program remaining limit counted))).2 := by
  obtain ⟨actualBound,recorded⟩ := ideal_recorded seed ro iv log program remaining limit counted
    coordinate valid answer member
  apply PCSBCSAtomicAllocationTrace.recognized_recorded part (part.split (oracle seed ro))
    (compile Q iv log program remaining limit counted)
    (.inr (constructionKey Q iv coordinate actualBound)) answer block
  · simpa only [RawOracleCoupling.Partition.join_split] using recorded
  · exact recognized

#print axioms execute_map
#print axioms compiled_recorded
#print axioms ideal_recorded
#print axioms ideal_packet_recorded
end Whir.PCSBCSMixedConstructionTrace
