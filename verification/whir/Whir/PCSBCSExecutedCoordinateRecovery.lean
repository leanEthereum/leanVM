import Whir.PCSBCSSourceCoordinateDecoderSource
import Whir.PublicCompressionCouplingPrefixTrace
import Whir.PublicCompressionCouplingClosure
import Whir.PublicCompressionProgram
import Whir.PCSBCSSourcePrimitiveRootBudget

/-! Recovery from the actual executed primitive ancestry, rather than an
assumed recognized compression tree. The terminal remains outside its prefix;
freshness, collision freedom and the full public-log budget are explicit. -/
namespace Whir.PCSBCSExecutedCoordinateRecovery
open FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame DuplexPublicSimulator
open PublicCompressionProgram PublicCompressionCouplingMixed
open PublicCompressionCouplingRecognition TypedOracleCompiler
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

 theorem planCalls_body (C : PrimitiveOracle) (Q : Nat) (ro : RawKey Q → Digest32)
    (cv : Digest32) (xs : List DuplexEncoding.Instruction) :
    (Sampling.execute C (planCalls cv xs)).1 =
      (Sampling.eval (oracle C ro) (bodyCalls Q cv xs)).1 ∧
    toLog (Sampling.execute C (planCalls cv xs)).2 =
      (Sampling.eval (oracle C ro) (bodyCalls Q cv xs)).2 := by
  induction xs generalizing cv with
  | nil => exact ⟨rfl,rfl⟩
  | cons i rest ih =>
    simp only [planCalls,Sampling.execute,bodyCalls,Sampling.eval,
      PublicCompressionCouplingMixed.Computation.eval_map,oracle]
    constructor
    · exact (ih (C ⟨cv,i.1,i.2,true⟩)).1
    · simpa only [toLog,List.map_cons] using
        congrArg (fun log => (⟨cv,i.1,i.2,true⟩,C ⟨cv,i.1,i.2,true⟩)::log)
          (ih (C ⟨cv,i.1,i.2,true⟩)).2

 theorem body_value (C : PrimitiveOracle) (iv : Digest32) (q : Coordinate)
    (valid : DuplexEncoding.Admissible q) :
    (Sampling.execute C (planCalls iv (DuplexEncoding.plan q).dropLast)).1 =
      (traceHistory (compressionOf C) iv q.history).state.cv := by
  rw [(planCalls_body C 0 (fun _ => iv) iv _).1,← coordinate_body_plan]
  exact congrArg Prod.fst
    (bodyCalls_tree (traceHistory_valid (compressionOf C) iv q.history valid.1).1
      0 iv (traceHistory_anchored (compressionOf C) iv q.history valid.1) (fun _ => iv))

 theorem body_records (C : PrimitiveOracle) (iv : Digest32) (q : Coordinate)
    (valid : DuplexEncoding.Admissible q) :
    toLog (Sampling.execute C (planCalls iv (DuplexEncoding.plan q).dropLast)).2 =
      (traceHistory (compressionOf C) iv q.history).nodes.reverse.map (fun n => (n,C n)) := by
  rw [(planCalls_body C 0 (fun _ => iv) iv _).2]
  exact inspection_body_nodes 0 C (fun _ => iv) iv q valid

 theorem executed_publicBody (C : PrimitiveOracle) (iv : Digest32) (q : Coordinate)
    (valid : DuplexEncoding.Admissible q) (prior : PublicLog) :
    PublicBody
      ((toLog (Sampling.execute C (planCalls iv (DuplexEncoding.plan q).dropLast)).2).reverse ++ prior)
      (traceHistory (compressionOf C) iv q.history).state.cv
      (traceHistory (compressionOf C) iv q.history).nodes := by
  classical
  apply Tree.publicBody_of_exposure
    (traceHistory_valid (compressionOf C) iv q.history valid.1).1 _ Finset.univ
  · intro n d member
    exact Finset.mem_univ _
  · intro n member hit
    apply List.mem_append_left
    rw [body_records C iv q valid,← List.map_reverse,List.reverse_reverse]
    exact List.mem_map.mpr ⟨n,member,rfl⟩
  · exact Finset.mem_univ _

 theorem recover_executed_prefix (C : PrimitiveOracle) (iv : Digest32)
    (q : Coordinate) (valid : DuplexEncoding.Admissible q) (prior : PublicLog) (Q : Nat)
    (priorAuth : PublicMerkleLog.AuthenticLog C prior)
    (clean : ¬ OutputCollision
      ((toLog (Sampling.execute C (planCalls iv (DuplexEncoding.plan q).dropLast)).2).reverse ++ prior))
    (fresh : lookup
      ((toLog (Sampling.execute C (planCalls iv (DuplexEncoding.plan q).dropLast)).2).reverse ++ prior)
      (terminalNode (Sampling.execute C
        (planCalls iv (DuplexEncoding.plan q).dropLast)).1 q.terminal) = none)
    (budget : (toLog (Sampling.execute C
      (planCalls iv (DuplexEncoding.plan q).dropLast)).2).length + prior.length + 1 ≤ Q) :
    PCSBCSSourceCoordinateDecoder.recover Q iv
      ((toLog (Sampling.execute C (planCalls iv (DuplexEncoding.plan q).dropLast)).2).reverse ++ prior)
      (terminalNode (Sampling.execute C
        (planCalls iv (DuplexEncoding.plan q).dropLast)).1 q.terminal) = some q := by
  rw [body_value C iv q valid] at fresh ⊢
  have auth : PublicMerkleLog.AuthenticLog C
      ((toLog (Sampling.execute C
        (planCalls iv (DuplexEncoding.plan q).dropLast)).2).reverse ++ prior) := by
    intro n d member
    rcases List.mem_append.mp member with member | member
    · exact execute_authentic C _ n d (List.mem_reverse.mp member)
    · exact priorAuth n d member
  have functional : Functional
      ((toLog (Sampling.execute C
        (planCalls iv (DuplexEncoding.plan q).dropLast)).2).reverse ++ prior) := by
    intro n a b ha hb
    exact (auth n a ha).symm.trans (auth n b hb)
  apply PCSBCSSourceCoordinateDecoder.recover_from_publicBody functional clean fresh
  · exact terminal_node _ _
  · cases q.terminal <;> simpa only [terminalNode] using executed_publicBody C iv q valid prior
  · exact PCSBCSSourceCoordinateDecoder.coordinateTree_sourceShape (compressionOf C) iv q valid
  · simpa only [List.length_append,List.length_reverse] using budget

 theorem references_executed_prefix (C : PrimitiveOracle)
    (p : ParameterBounds.Profile) (Q boundary : Nat) (registry : AnchoredHeaderRoots.Public)
    (q : Coordinate) (valid : DuplexEncoding.Admissible q) (prior : PublicLog)
    (priorAuth : PublicMerkleLog.AuthenticLog C prior)
    (clean : ¬ OutputCollision
      ((toLog (Sampling.execute C
        (planCalls PCSBCSSourceCoordinateDecoder.seedIV (DuplexEncoding.plan q).dropLast)).2).reverse ++ prior))
    (fresh : lookup
      ((toLog (Sampling.execute C
        (planCalls PCSBCSSourceCoordinateDecoder.seedIV (DuplexEncoding.plan q).dropLast)).2).reverse ++ prior)
      (terminalNode (Sampling.execute C
        (planCalls PCSBCSSourceCoordinateDecoder.seedIV (DuplexEncoding.plan q).dropLast)).1 q.terminal) = none)
    (budget : (toLog (Sampling.execute C
      (planCalls PCSBCSSourceCoordinateDecoder.seedIV (DuplexEncoding.plan q).dropLast)).2).length +
      prior.length + 1 ≤ Q)
    (layout : WHIRCallerClaims.CallerLayout) (saved : AnchoredHeaderCodec.Record)
    (answers : Coordinate → Digest32) (refs : List PCSBCSSourceRootReferences.Reference)
    (native : PCSBCSSourceRootReferences.parseReferences p layout saved
      (PCSBCSSourcePrimitiveRootBudget.entry q boundary) answers q = some refs) :
    ∀ ref ∈ refs, ref ∈ PCSBCSSourcePrimitiveRootBudget.references p Q boundary registry
      ((toLog (Sampling.execute C
        (planCalls PCSBCSSourceCoordinateDecoder.seedIV (DuplexEncoding.plan q).dropLast)).2).reverse ++ prior)
      (terminalNode (Sampling.execute C
        (planCalls PCSBCSSourceCoordinateDecoder.seedIV (DuplexEncoding.plan q).dropLast)).1 q.terminal) := by
  exact PCSBCSSourcePrimitiveRootBudget.references_native p Q boundary registry _ _ q
    (recover_executed_prefix C _ q valid prior Q priorAuth clean fresh budget)
    layout saved answers refs native

#print axioms planCalls_body
#print axioms body_value
#print axioms body_records
#print axioms executed_publicBody
#print axioms recover_executed_prefix
#print axioms references_executed_prefix
end Whir.PCSBCSExecutedCoordinateRecovery
