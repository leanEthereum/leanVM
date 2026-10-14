import Whir.PublicCompressionCouplingPrimitiveStream
import Whir.PublicCompressionCouplingPublicTrace

/-! Operational alignment of hidden Seed prefix calls and the actual RO terminal.
Both interpreters consume the identical fresh stream, including cache hits. -/
namespace Whir.PublicCompressionCouplingConstructionStream
open FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame DuplexPublicSimulator
open TypedFiatShamirGame
open TypedOracleCompiler (Sampling)
open PublicCompressionCouplingMixed PublicCompressionCouplingJoint
open PublicCompressionCouplingStreams PublicCompressionCouplingRelabelCache
open PublicCompressionCouplingRecognition PublicCompressionCouplingPrimitiveStream
set_option backward.isDefEq.respectTransparency false

 theorem run_draw_split {K R : Type} [DecidableEq K] {n : Nat} (key : K)
    (next : Digest32 → PublicCompressionCouplingJoint.Computation K R n)
    (cache : PublicCompressionCouplingJoint.Cache K) (stream : List Digest32)
    {result : R} {final : PublicCompressionCouplingJoint.Cache K} {remaining : List Digest32}
    (execution : run (.draw key next) cache stream=some (result,final,remaining)) :
    ∃ answer updated rest,
      run (.draw key (fun d => .ret (n:=0) d)) cache stream=some (answer,updated,rest) ∧
      run (next answer) updated rest=some (result,final,remaining) := by
  cases hit : cache key with
  | some answer =>
    exact ⟨answer,cache,stream,by rw [run_hit hit]; rfl,by rwa [run_hit hit] at execution⟩
  | none =>
    cases stream with
    | nil => rw [run_miss_nil hit] at execution; cases execution
    | cons answer rest =>
      exact ⟨answer,put cache key answer,rest,by rw [run_miss_cons hit]; rfl,
        by rwa [run_miss_cons hit] at execution⟩

 theorem mixed_map_recover {Q n : Nat} {R S : Type} (f : R → S)
    (p : PublicCompressionCouplingMixed.Computation Q R n)
    (cache : PublicCompressionCouplingJoint.Cache (Key Q)) (stream : List Digest32)
    {result : S} {final : PublicCompressionCouplingJoint.Cache (Key Q)} {remaining : List Digest32}
    (execution : run (PublicCompressionCouplingMixed.Computation.map f p) cache stream=
      some (result,final,remaining)) :
    ∃ value, run p cache stream=some (value,final,remaining) ∧ f value=result := by
  rw [run_mixed_map] at execution
  cases found : run p cache stream with
  | none => simp only [found,Option.map_none] at execution; cases execution
  | some triple =>
    rcases triple with ⟨value,updated,rest⟩
    simp only [found,Option.map_some,Option.some.injEq,Prod.mk.injEq] at execution
    obtain ⟨valueEq,cacheEq,restEq⟩ := execution
    exact ⟨value,by simp only [cacheEq,restEq],valueEq⟩

 theorem body_stream_alignment (Q : Nat) (seedTable : Seed) (cv : Digest32)
    (xs : List DuplexEncoding.Instruction)
    (pc : PublicCompressionCouplingJoint.Cache Node)
    (qc final : PublicCompressionCouplingJoint.Cache (Key Q)) (stream : List Digest32)
    (body : Digest32 × BodyLog) (updated : PublicCompressionCouplingJoint.Cache (Key Q))
    (remaining : List Digest32)
    (execution : run (bodyCalls Q cv xs) qc stream=some (body,updated,remaining))
    (related : Related (coordinateLabel seedTable) pc qc)
    (extension : Extends updated final) (injective : InjectiveOn (coordinateLabel seedTable) final) :
    ∃ pc', run (PublicCompressionProgram.planCalls cv xs) pc stream=some (body.1,pc',remaining) ∧
      Related (coordinateLabel seedTable) pc' updated ∧ Extends updated final := by
  induction xs generalizing cv pc qc stream body updated remaining with
  | nil =>
    simp only [bodyCalls,run,Option.some.injEq,Prod.mk.injEq] at execution
    obtain ⟨bodyEq,cacheEq,restEq⟩ := execution
    subst body; subst updated; subst remaining
    exact ⟨pc,rfl,related,extension⟩
  | cons instruction xs ih =>
    simp only [bodyCalls] at execution
    obtain ⟨answer,first,rest,draw,tail⟩ := run_draw_split _ _ qc stream execution
    obtain ⟨tailBody,tailRun,bodyEq⟩ := mixed_map_recover _ _ first rest tail
    have firstExtension : Extends first final := by
      intro key digest stored
      exact extension key digest (run_extends _ first rest tailRun stored)
    obtain ⟨firstReal,realDraw,firstRelated,_,_⟩ := matched_draw (coordinateLabel seedTable)
      (.inl ⟨cv,instruction.1,instruction.2,true⟩) pc qc final stream answer first rest draw related
      firstExtension injective
    simp only [coordinateLabel] at realDraw
    obtain ⟨lastReal,realTail,lastRelated,lastExtension⟩ :=
      ih answer firstReal first rest tailBody updated remaining tailRun firstRelated extension
    refine ⟨lastReal,?_,lastRelated,lastExtension⟩
    have viewEq := congrArg (fun p : Digest32 × BodyLog => p.1) bodyEq
    dsimp only at viewEq
    simp only [PublicCompressionProgram.planCalls]
    cases hit : pc ⟨cv,instruction.1,instruction.2,true⟩ with
    | some value =>
      rw [run_hit hit] at realDraw ⊢
      simp only [run,Option.some.injEq,Prod.mk.injEq] at realDraw
      obtain ⟨rfl,rfl,rfl⟩ := realDraw
      simpa only [viewEq] using realTail
    | none =>
      cases stream with
      | nil => rw [run_miss_nil hit] at realDraw; cases realDraw
      | cons value restStream =>
        rw [run_miss_cons hit] at realDraw ⊢
        simp only [run,Option.some.injEq,Prod.mk.injEq] at realDraw
        obtain ⟨rfl,rfl,rfl⟩ := realDraw
        simpa only [viewEq] using realTail

 theorem plan_append_run (cv : Digest32) (xs ys : List DuplexEncoding.Instruction)
    (cache : PublicCompressionCouplingJoint.Cache Node) (stream : List Digest32) :
    run (PublicCompressionProgram.planCalls cv (xs++ys)) cache stream =
      match run (PublicCompressionProgram.planCalls cv xs) cache stream with
      | none => none
      | some (value,updated,rest) => run (PublicCompressionProgram.planCalls value ys) updated rest := by
  induction xs generalizing cv cache stream with
  | nil => rfl
  | cons instruction xs ih =>
    cases hit : cache ⟨cv,instruction.1,instruction.2,true⟩ with
    | some answer =>
      simp only [List.cons_append,PublicCompressionProgram.planCalls]
      rw [run_hit hit,run_hit hit]
      exact ih answer cache stream
    | none =>
      cases stream with
      | nil => simp only [List.cons_append,PublicCompressionProgram.planCalls,run_miss_nil,hit]
      | cons answer rest =>
        simpa only [List.cons_append,PublicCompressionProgram.planCalls,run_miss_cons,hit] using
          ih answer (put cache ⟨cv,instruction.1,instruction.2,true⟩ answer) rest

open Classical in
 theorem actual_construction_stream_alignment (Q : Nat) (seedTable : Seed) (ro : RawKey Q → Digest32)
    (iv : Digest32) (coordinate : Coordinate) (valid : DuplexEncoding.Admissible coordinate)
    (budget : pathCost coordinate ≤ Q)
    (pc : PublicCompressionCouplingJoint.Cache Node)
    (qc final : PublicCompressionCouplingJoint.Cache (Key Q)) (stream : List Digest32)
    (construction : InspectedConstruction) (updated : PublicCompressionCouplingJoint.Cache (Key Q))
    (remaining : List Digest32)
    (execution : run (causalConstruction Q iv coordinate valid budget) qc stream=
      some (construction,updated,remaining))
    (related : Related (coordinateLabel seedTable) pc qc)
    (extension : Extends updated final) (injective : InjectiveOn (coordinateLabel seedTable) final)
    (consistent : ∀ key answer, final key=some answer → oracle seedTable ro key=answer) :
    ∃ pc', run (PublicCompressionProgram.queryCalls iv (.construction coordinate valid)) pc stream=
      some (construction.advertised,pc',remaining) ∧
      Related (coordinateLabel seedTable) pc' updated ∧ Extends updated final := by
  simp only [causalConstruction,run_pad,run_bind] at execution
  cases prefixRun : run (bodyCalls Q iv (DuplexEncoding.plan coordinate).dropLast) qc stream with
  | none => simp only [prefixRun] at execution; cases execution
  | some triple =>
    rcases triple with ⟨body,prefixCache,prefixRest⟩
    rw [prefixRun] at execution
    obtain ⟨answer,lastCache,lastRest,terminalRun,finish⟩ := run_draw_split
      (.inr (constructionKey Q iv coordinate budget)) _ prefixCache prefixRest execution
    simp only [run,Option.some.injEq,Prod.mk.injEq] at finish
    obtain ⟨constructionEq,cacheEq,restEq⟩ := finish
    subst construction; subst updated; subst remaining
    have prefixExtension : Extends prefixCache final := by
      intro key digest stored
      exact extension key digest (run_extends _ prefixCache prefixRest execution stored)
    obtain ⟨prefixReal,realPrefix,prefixRelated,_⟩ := body_stream_alignment Q seedTable iv _ pc qc
      final stream body prefixCache prefixRest prefixRun related prefixExtension injective
    have prefixValue := congrArg Prod.fst (run_eval _ qc stream prefixRun (oracle seedTable ro)
      (fun key digest stored => consistent key digest (prefixExtension key digest stored)))
    rw [bodyCalls_eval,plan_prefix_evaluate] at prefixValue
    have label : coordinateLabel seedTable (.inr (constructionKey Q iv coordinate budget))=
        ⟨body.1,(DuplexEncoding.terminalPlan coordinate.terminal).1,
          (DuplexEncoding.terminalPlan coordinate.terminal).2,true⟩ := by
      have witness := terminalLabel_witness (construction_coordinateWitness Q seedTable iv coordinate valid budget)
      rw [coordinateLabel,witness,← prefixValue]
      cases coordinate.terminal <;> rfl
    obtain ⟨lastReal,realTerminal,lastRelated,_,_⟩ := matched_draw (coordinateLabel seedTable)
      (.inr (constructionKey Q iv coordinate budget)) prefixReal prefixCache final prefixRest answer
      lastCache lastRest terminalRun prefixRelated extension injective
    refine ⟨lastReal,?_,lastRelated,extension⟩
    have planEq : DuplexEncoding.plan coordinate=(DuplexEncoding.plan coordinate).dropLast ++
        [DuplexEncoding.terminalPlan coordinate.terminal] := by
      unfold DuplexEncoding.plan
      rw [List.dropLast_concat]
    exact (congrArg (fun xs => run (PublicCompressionProgram.planCalls iv xs) pc stream) planEq).trans (by
      rw [plan_append_run,realPrefix]
      simpa only [PublicCompressionProgram.planCalls,label,run] using realTerminal)

#print axioms actual_construction_stream_alignment
end Whir.PublicCompressionCouplingConstructionStream
