import Whir.PublicCompressionCouplingCausal
import Whir.PublicCompressionCouplingPublicTrace

/-! Every private prefix query in causal and posthoc inspection is a literal
node of the same actual seed-table construction body, including the root CV. -/
namespace Whir.PublicCompressionCouplingRecognition
open FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame DuplexPublicSimulator
open PublicCompressionCouplingMixed
open TypedOracleCompiler (Sampling)
set_option backward.isDefEq.respectTransparency false

 theorem bodyCalls_append (Q : Nat) (table : Key Q → Digest32) (cv : Digest32)
    (xs ys : List DuplexEncoding.Instruction) :
    Sampling.eval table (bodyCalls Q cv (xs++ys)) =
      let left := Sampling.eval table (bodyCalls Q cv xs)
      let right := Sampling.eval table (bodyCalls Q left.1 ys)
      (right.1,left.2++right.2) := by
  induction xs generalizing cv with
  | nil => rfl
  | cons instruction rest ih =>
    simp only [List.cons_append,bodyCalls,Sampling.eval,PublicCompressionCouplingMixed.Computation.eval_map]
    rw [ih]

 theorem bodyCalls_trace (Q : Nat) (table : Key Q → Digest32) (cv : Digest32)
    (xs : List DuplexEncoding.Instruction) :
    (Sampling.execute table (bodyCalls Q cv xs)).2 =
      (Sampling.eval table (bodyCalls Q cv xs)).2.map
        (fun entry => (⟨.inl entry.1,entry.2⟩ : Sigma (fun _ : Key Q => Digest32))) := by
  induction xs generalizing cv with
  | nil => rfl
  | cons instruction rest ih =>
    simp only [bodyCalls,Sampling.execute,execute_map_trace,Sampling.eval,PublicCompressionCouplingMixed.Computation.eval_map,
      List.map_cons]
    rw [ih]

 theorem bodyCalls_tree {seedTable : Seed} {cv : Digest32} {ns : List Node}
    (tree : Tree (compressionOf seedTable) cv ns) (Q : Nat) (iv : Digest32)
    (anchored : Anchored iv ns) (ro : RawKey Q → Digest32) :
    Sampling.eval (oracle seedTable ro) (bodyCalls Q iv (rawPlan ns)) =
      (cv,ns.reverse.map (fun n => (n,seedTable n))) := by
  induction tree with
  | seed node valid =>
    have root := anchored node (by simp) valid
    have fields : (⟨iv,node.block,node.tweak,true⟩ : Node) = node :=
      node_fields_equal root.symm rfl rfl valid.2.symm
    have planEq : rawPlan [node] = [(node.block,node.tweak)] := by simp [rawPlan]
    rw [planEq]
    simp only [bodyCalls,Sampling.eval,PublicCompressionCouplingMixed.Computation.eval_map,
      oracle,fields,nodeValue,compressionOf,List.reverse_singleton,List.map_cons,List.map_nil]
  | step node rest valid child ih =>
    have inherited : Anchored iv rest := fun n member seed =>
      anchored n (List.mem_cons_of_mem _ member) seed
    have bodyEvaluation := ih inherited
    have fields : (⟨node.cv,node.block,node.tweak,true⟩ : Node) = node :=
      node_fields_equal rfl rfl rfl valid.2.symm
    have planEq : rawPlan (node::rest) = rawPlan rest ++ [(node.block,node.tweak)] := by
      simp [rawPlan]
    rw [planEq,bodyCalls_append,bodyEvaluation]
    simp only [bodyCalls,Sampling.eval,PublicCompressionCouplingMixed.Computation.eval_map,oracle,
      fields,nodeValue,compressionOf,List.reverse_cons,List.map_append,List.map_cons,List.map_nil]

 theorem coordinate_body_plan (c : Compression) (iv : Digest32) (coordinate : Coordinate) :
    rawPlan (traceHistory c iv coordinate.history).nodes =
      (DuplexEncoding.plan coordinate).dropLast := by
  have plan := congrArg List.dropLast (coordinateTree_plan c iv coordinate)
  simpa only [coordinateTree,rawPlan,List.reverse_cons,List.map_append,List.map_cons,
    List.map_nil,List.dropLast_concat] using plan

 theorem inspection_body_nodes (Q : Nat) (seedTable : Seed) (ro : RawKey Q → Digest32)
    (iv : Digest32) (coordinate : Coordinate) (valid : DuplexEncoding.Admissible coordinate) :
    (Sampling.eval (oracle seedTable ro)
      (bodyCalls Q iv (DuplexEncoding.plan coordinate).dropLast)).2 =
      (traceHistory (compressionOf seedTable) iv coordinate.history).nodes.reverse.map
        (fun n => (n,seedTable n)) := by
  rw [← coordinate_body_plan (compressionOf seedTable) iv coordinate]
  have anchored : Anchored iv (traceHistory (compressionOf seedTable) iv coordinate.history).nodes :=
    traceHistory_anchored (compressionOf seedTable) iv coordinate.history valid.1
  exact congrArg Prod.snd
    (bodyCalls_tree (traceHistory_valid (compressionOf seedTable) iv coordinate.history valid.1).1
      Q iv anchored ro)

 theorem inspect_prefix_record (Q : Nat) (iv : Digest32) (table : Key Q → Digest32)
    (observations : List Observation) {construction : InspectedConstruction}
    (member : construction ∈ Sampling.eval table (inspect Q iv observations))
    {node : Node} {answer : Digest32} (record : (node,answer) ∈ construction.prefixLog) :
    (⟨.inl node,answer⟩ : Sigma (fun _ : Key Q => Digest32)) ∈
      (Sampling.execute table (inspect Q iv observations)).2 := by
  induction observations with
  | nil => simp [inspect,Sampling.eval] at member
  | cons observation rest ih =>
    rcases observation with ⟨query,digest⟩
    cases query with
    | primitive purpose input => exact ih member
    | construction coordinate valid =>
      simp only [inspect,Sampling.eval_bind,PublicCompressionCouplingMixed.Computation.eval_map,List.mem_cons] at member
      simp only [inspect,Sampling.execute_bind,execute_map_trace,List.mem_append]
      rcases member with equal | later
      · subst construction
        apply Or.inl
        rw [bodyCalls_trace]
        exact List.mem_map.mpr ⟨(node,answer),record,rfl⟩
      · exact Or.inr (ih later)

 theorem inspect_construction_nodes (Q : Nat) (seedTable : Seed) (ro : RawKey Q → Digest32)
    (iv : Digest32) (observations : List Observation) {construction : InspectedConstruction}
    (member : construction ∈ Sampling.eval (oracle seedTable ro) (inspect Q iv observations)) :
    construction.prefixLog =
      (traceHistory (compressionOf seedTable) iv construction.coordinate.history).nodes.reverse.map
        (fun n => (n,seedTable n)) := by
  induction observations with
  | nil => simp [inspect,Sampling.eval] at member
  | cons observation rest ih =>
    rcases observation with ⟨query,digest⟩
    cases query with
    | primitive purpose input => exact ih member
    | construction coordinate valid =>
      simp only [inspect,Sampling.eval_bind,PublicCompressionCouplingMixed.Computation.eval_map,List.mem_cons] at member
      rcases member with equal | later
      · subst construction
        exact inspection_body_nodes Q seedTable ro iv coordinate valid
      · exact ih later

#print axioms bodyCalls_tree
#print axioms inspection_body_nodes
end Whir.PublicCompressionCouplingRecognition
