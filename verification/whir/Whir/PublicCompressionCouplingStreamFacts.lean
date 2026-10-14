import Whir.PublicCompressionCouplingStreams
import Whir.PublicCompressionCouplingCausal

/-! Exact lazy fresh-stream interpreter facts for source-aware alignment.
Completed caches recover actual memo execution under every consistent table;
no independent replay seed or oracle is introduced. -/
namespace Whir.PublicCompressionCouplingStreams
open FiatShamirGame TypedFiatShamirGame RawOracleCoupling
open TypedOracleCompiler (Sampling)
open PublicCompressionCouplingJoint

variable {K R : Type} [DecidableEq K]

 theorem run_extends {n : Nat} (p : Computation K R n) (cache : Cache K) (stream : List Digest32)
    {result : R} {final : Cache K} {remaining : List Digest32}
    (execution : run p cache stream=some (result,final,remaining)) {key : K} {answer : Digest32}
    (stored : cache key=some answer) : final key=some answer := by
  induction p generalizing cache stream with
  | ret value =>
    simp only [run,Option.some.injEq,Prod.mk.injEq] at execution
    obtain ⟨_,equal,_⟩ := execution
    simpa only [← equal] using stored
  | draw input next ih =>
    cases hit : cache input with
    | some value =>
      rw [run_hit hit] at execution
      exact ih value cache stream execution stored
    | none =>
      cases stream with
      | nil => rw [run_miss_nil hit] at execution; cases execution
      | cons value rest =>
        rw [run_miss_cons hit] at execution
        apply ih value (put cache input value) rest execution
        by_cases same : key=input
        · subst key
          rw [hit] at stored
          cases stored
        · simpa only [put_other _ _ _ _ same] using stored

 theorem run_table {n : Nat} (p : Computation K R n) (cache : Cache K) (stream : List Digest32)
    {result : R} {final : Cache K} {remaining : List Digest32}
    (execution : run p cache stream=some (result,final,remaining)) (table : K → Digest32)
    (consistent : ∀ key answer, final key=some answer → table key=answer) :
    Sampling.eval table (memo p cache)=(result,final) := by
  induction p generalizing cache stream with
  | ret value =>
    simp only [run,Option.some.injEq,Prod.mk.injEq] at execution
    obtain ⟨equal,cacheEq,_⟩ := execution
    simp only [memo,Sampling.eval,equal,cacheEq]
  | draw input next ih =>
    cases hit : cache input with
    | some value =>
      rw [run_hit hit] at execution
      simp only [memo,hit,Sampling.eval_pad]
      exact ih value cache stream execution
    | none =>
      cases stream with
      | nil => rw [run_miss_nil hit] at execution; cases execution
      | cons value rest =>
        rw [run_miss_cons hit] at execution
        have stored := run_extends (next value) (put cache input value) rest execution (put_self _ _ _)
        have actual := consistent input value stored
        simp only [memo,hit,Sampling.eval,actual]
        exact ih value (put cache input value) rest execution

 theorem run_eval {n : Nat} (p : Computation K R n) (cache : Cache K) (stream : List Digest32)
    {result : R} {final : Cache K} {remaining : List Digest32}
    (execution : run p cache stream=some (result,final,remaining)) (table : K → Digest32)
    (consistent : ∀ key answer, final key=some answer → table key=answer) :
    Sampling.eval table p=result := by
  have initial : ∀ key answer, cache key=some answer → table key=answer := by
    intro key answer stored
    exact consistent key answer (run_extends p cache stream execution stored)
  have overlayEq : overlay cache table=table := by
    funext key
    cases hit : cache key with
    | none => simp only [overlay,hit,Option.getD_none]
    | some answer =>
      simp only [overlay,hit,Option.getD_some]
      exact (initial key answer hit).symm
  have pure := memo_eval_first p cache table
  rw [overlayEq] at pure
  exact pure.symm.trans (congrArg Prod.fst (run_table p cache stream execution table consistent))

 theorem run_pad {n m : Nat} (bound : n ≤ m) (p : Computation K R n)
    (cache : Cache K) (stream : List Digest32) :
    run (Sampling.pad bound p) cache stream=run p cache stream := by
  induction p generalizing m cache stream with
  | ret result => simp only [Sampling.pad,run]
  | draw key next ih =>
    cases m with
    | zero => omega
    | succ m =>
      cases hit : cache key with
      | some answer =>
        simp only [Sampling.pad]
        rw [run_hit hit,run_hit hit]
        exact ih answer _ cache stream
      | none =>
        cases stream with
        | nil => simp only [Sampling.pad,run_miss_nil,hit]
        | cons answer rest =>
          simpa only [Sampling.pad,run_miss_cons,hit] using ih answer _ (put cache key answer) rest

 theorem run_bind {S : Type} {n m : Nat} (p : Computation K R n)
    (next : R → Computation K S m) (cache : Cache K) (stream : List Digest32) :
    run (Sampling.bind p next) cache stream =
      match run p cache stream with
      | none => none
      | some (value,updated,rest) => run (next value) updated rest := by
  induction p generalizing cache stream with
  | ret result => simp only [Sampling.bind,run_pad,run]
  | draw key continuation ih =>
    cases hit : cache key with
    | some answer =>
      simp only [Sampling.bind,run_pad]
      rw [run_hit hit,run_hit hit]
      exact ih answer cache stream
    | none =>
      cases stream with
      | nil => simp only [Sampling.bind,run_pad,run_miss_nil,hit]
      | cons answer rest =>
        simpa only [Sampling.bind,run_pad,run_miss_cons,hit] using ih answer (put cache key answer) rest

 theorem run_mixed_map {Q n : Nat} [DecidableEq (PublicCompressionCouplingMixed.Key Q)]
    {R S : Type} (f : R → S)
    (p : PublicCompressionCouplingMixed.Computation Q R n)
    (cache : Cache (PublicCompressionCouplingMixed.Key Q)) (stream : List Digest32) :
    run (PublicCompressionCouplingMixed.Computation.map f p) cache stream =
      (run p cache stream).map (fun result => (f result.1,result.2.1,result.2.2)) := by
  induction p generalizing cache stream with
  | ret result => rfl
  | draw key next ih =>
    cases hit : cache key with
    | some answer =>
      simp only [PublicCompressionCouplingMixed.Computation.map]
      rw [run_hit hit,run_hit hit]
      exact ih answer cache stream
    | none =>
      cases stream with
      | nil => simp only [PublicCompressionCouplingMixed.Computation.map,run_miss_nil,hit,Option.map_none]
      | cons answer rest =>
        simpa only [PublicCompressionCouplingMixed.Computation.map,run_miss_cons,hit] using ih answer (put cache key answer) rest

 theorem run_real_map {n : Nat} [DecidableEq DuplexFraming.Node] {R S : Type} (f : R → S)
    (p : PublicCompressionProgram.Computation R n) (cache : Cache DuplexFraming.Node) (stream : List Digest32) :
    run (PublicCompressionProgram.mapResult f p) cache stream =
      (run p cache stream).map (fun result => (f result.1,result.2.1,result.2.2)) := by
  induction p generalizing cache stream with
  | ret result => rfl
  | draw key next ih =>
    cases hit : cache key with
    | some answer =>
      simp only [PublicCompressionProgram.mapResult]
      rw [run_hit hit,run_hit hit]
      exact ih answer cache stream
    | none =>
      cases stream with
      | nil => simp only [PublicCompressionProgram.mapResult,run_miss_nil,hit,Option.map_none]
      | cons answer rest =>
        simpa only [PublicCompressionProgram.mapResult,run_miss_cons,hit] using ih answer (put cache key answer) rest

#print axioms run_table
#print axioms run_bind
end Whir.PublicCompressionCouplingStreams
