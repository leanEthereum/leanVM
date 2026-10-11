import Whir.PublicCompressionCouplingPublicCache

/-! Origin of every raw RO coordinate actually consumed by the causal ideal
compiler: a publicly recognized terminal body or an actual construction whose
private prefix is in the same causal memo cache. -/
namespace Whir.PublicCompressionCouplingRecognition
open FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame DuplexPublicSimulator
open PublicCompressionCouplingMixed
open TypedOracleCompiler (Sampling)
set_option backward.isDefEq.respectTransparency false

 theorem publicBody_mono {old new : PublicLog} {cv : Digest32} {ns : List Node}
    (tree : PublicBody old cv ns) (subset : ∀ n d, (n,d) ∈ old → (n,d) ∈ new) :
    PublicBody new cv ns := by
  induction tree with
  | seed member valid => exact PublicBody.seed (subset _ _ member) valid
  | step member valid child ih => exact PublicBody.step (subset _ _ member) valid ih

 theorem bodyCalls_not_raw (Q : Nat) (table : Key Q → Digest32) (cv : Digest32)
    (instructions : List DuplexEncoding.Instruction) (key : RawKey Q) (answer : Digest32) :
    (⟨.inr key,answer⟩ : Sigma (fun _ : Key Q => Digest32)) ∉
      (Sampling.execute table (bodyCalls Q cv instructions)).2 := by
  rw [bodyCalls_trace]
  rintro member
  obtain ⟨entry,prior,equal⟩ := List.mem_map.mp member
  have keys := congrArg Sigma.fst equal
  cases keys

 theorem causalConstruction_raw_key (Q : Nat) (table : Key Q → Digest32) (iv : Digest32)
    (coordinate : Coordinate) (valid : DuplexEncoding.Admissible coordinate)
    (budget : pathCost coordinate ≤ Q) {key : RawKey Q} {answer : Digest32}
    (member : (⟨.inr key,answer⟩ : Sigma (fun _ : Key Q => Digest32)) ∈
      (Sampling.execute table (causalConstruction Q iv coordinate valid budget)).2) :
    key = constructionKey Q iv coordinate budget := by
  rw [causalConstruction_trace,List.mem_append] at member
  rcases member with prefixMember | rawMember
  · exact False.elim (bodyCalls_not_raw Q table iv _ key answer prefixMember)
  · have equal := List.mem_singleton.mp rawMember
    exact Sum.inr.inj (congrArg Sigma.fst equal)

 theorem primitiveCalls_raw_key (Q : Nat) (seedTable : Seed) (ro : RawKey Q → Digest32)
    (log : PublicLog) (input : Node) {key : RawKey Q} {answer : Digest32}
    (member : (⟨.inr key,answer⟩ : Sigma (fun _ : Key Q => Digest32)) ∈
      (Sampling.execute (oracle seedTable ro) (primitiveCalls Q log input)).2) :
    privateKey Q log input = some key := by
  cases hit : lookup log input with
  | some digest => simp [primitiveCalls,hit,Sampling.execute] at member
  | none =>
    cases found : privateKey Q log input with
    | none => simp [primitiveCalls,hit,found,Sampling.execute] at member
    | some raw =>
      simp only [primitiveCalls,hit,found,Sampling.execute,List.mem_cons,List.not_mem_nil,or_false] at member
      have keys : key=raw := Sum.inr.inj (congrArg Sigma.fst member)
      exact congrArg some keys.symm

 def PublicTerminalWitness (Q : Nat) (seedTable : Seed) (log : PublicLog) (key : RawKey Q) : Prop :=
  ∃ input rest, Complete (input::rest) ∧ Tree (compressionOf seedTable) input.cv rest ∧
    extract (input::rest) = some (expandKey key) ∧ PublicBody log input.cv rest

 theorem publicTerminalWitness_mono {Q : Nat} {seedTable : Seed} {old new : PublicLog} {key : RawKey Q}
    (witness : PublicTerminalWitness Q seedTable old key)
    (subset : ∀ n d, (n,d) ∈ old → (n,d) ∈ new) :
    PublicTerminalWitness Q seedTable new key := by
  obtain ⟨input,rest,complete,tree,extract,body⟩ := witness
  exact ⟨input,rest,complete,tree,extract,publicBody_mono body subset⟩

 theorem primitiveCalls_raw_witness (Q : Nat) (seedTable : Seed) (ro : RawKey Q → Digest32)
    (log : PublicLog) (auth : NonterminalAuthentic seedTable log) (input : Node)
    {key : RawKey Q} {answer : Digest32}
    (member : (⟨.inr key,answer⟩ : Sigma (fun _ : Key Q => Digest32)) ∈
      (Sampling.execute (oracle seedTable ro) (primitiveCalls Q log input)).2) :
    PublicTerminalWitness Q seedTable log key := by
  have found := primitiveCalls_raw_key Q seedTable ro log input member
  obtain ⟨rest,complete,tree,extracted⟩ := privateKey_seed_tree seedTable auth found
  obtain ⟨nodes,recognized,hc,he⟩ := privateKey_sound found
  obtain ⟨rest',equal,body⟩ := recognized_publicBody recognized
  subst nodes
  have actual := PublicBody.seed_tree body seedTable auth
  have same := (complete_key_unique complete hc tree actual (extracted.trans he.symm)).2
  subst rest'
  exact ⟨input,rest,complete,tree,extracted,body⟩

 theorem causalCompile_raw_origin (Q : Nat) (seedTable : Seed) (ro : RawKey Q → Digest32)
    (iv : Digest32) (log : PublicLog) (p : Program R) (remaining : Nat)
    (cap : remaining ≤ Q) (counted : Counts remaining p)
    (auth : NonterminalAuthentic seedTable log) {key : RawKey Q} {answer : Digest32}
    (member : (⟨.inr key,answer⟩ : Sigma (fun _ : Key Q => Digest32)) ∈
      (Sampling.execute (oracle seedTable ro) (causalCompile Q iv log p remaining cap counted)).2) :
    PublicTerminalWitness Q seedTable
      (finalLog log (Sampling.eval (oracle seedTable ro) (compile Q iv log p remaining cap counted)).observations) key ∨
      ∃ construction ∈ (Sampling.eval (oracle seedTable ro)
          (causalCompile Q iv log p remaining cap counted)).2,
        ∃ budget : pathCost construction.coordinate ≤ Q,
          key = constructionKey Q iv construction.coordinate budget := by
  induction p generalizing log remaining with
  | done result => simp [causalCompile,Sampling.execute] at member
  | ask query next ih =>
    cases query with
    | primitive purpose input =>
      simp only [causalCompile,Sampling.execute_pad,Sampling.execute_bind,execute_map_trace,List.mem_append] at member
      rcases member with first | later
      · apply Or.inl
        apply publicTerminalWitness_mono (primitiveCalls_raw_witness Q seedTable ro log auth input first)
        exact fun n d stored => finalLog_contains _ _ _ stored
      · have result := ih _ _ _ _ _ (primitiveCalls_authentic Q seedTable ro log auth input) later
        simpa only [compile,Sampling.eval_pad,Sampling.eval_bind,
          PublicCompressionCouplingMixed.Computation.eval_map,DuplexRawProgram.observe,finalLog,
          primitiveCalls_log,causalCompile] using result
    | construction coordinate valid =>
      simp only [causalCompile,Sampling.execute_pad,Sampling.execute_bind,execute_map_trace,List.mem_append] at member
      rcases member with first | later
      · apply Or.inr
        let construction := Sampling.eval (oracle seedTable ro)
          (causalConstruction Q iv coordinate valid (counted.1.trans cap))
        have coordinateEq : construction.coordinate=coordinate := by
          simp only [construction,causalConstruction_eval]
        have budget : pathCost construction.coordinate ≤ Q := by
          rw [coordinateEq]
          exact counted.1.trans cap
        refine ⟨construction,?_,budget,?_⟩
        · simp only [causalCompile,Sampling.eval_pad,Sampling.eval_bind,
            PublicCompressionCouplingMixed.Computation.eval_map]
          exact List.mem_cons_self
        · simpa only [coordinateEq] using causalConstruction_raw_key Q _ iv coordinate valid _ first
      · have result := ih _ log _ _ _ auth later
        rcases result with publicOrigin | privateOrigin
        · apply Or.inl
          simpa only [compile,Sampling.eval_pad,Sampling.eval,
            PublicCompressionCouplingMixed.Computation.eval_map,oracle,DuplexRawProgram.observe,finalLog,
            causalConstruction_eval] using publicOrigin
        · apply Or.inr
          obtain ⟨construction,constructionMember,budget,equal⟩ := privateOrigin
          refine ⟨construction,?_,budget,equal⟩
          simpa only [causalCompile,Sampling.eval_pad,Sampling.eval_bind,
            PublicCompressionCouplingMixed.Computation.eval_map,causalConstruction_eval] using
            List.mem_cons_of_mem (Sampling.eval (oracle seedTable ro)
              (causalConstruction Q iv coordinate valid (counted.1.trans cap))) constructionMember

#print axioms causalCompile_raw_origin
end Whir.PublicCompressionCouplingRecognition
