import Whir.PublicCompressionCouplingJoint

/-! Deterministic path semantics for the existing shared-answer joint sampler.
A Unit draw is fresh randomness on each occurrence: it is NOT evaluated using
one memoized Unit table. Both marginals consume the same fresh digest stream. -/
namespace Whir.PublicCompressionCouplingStreams
open FiatShamirGame TypedFiatShamirGame
open TypedOracleCompiler (Sampling)
open PublicCompressionCouplingJoint

variable {K R : Type} [DecidableEq K]

/-- The ordinary lazy-table interpreter, exposing its unconsumed stream solely
for deterministic cache/trace induction. -/
def run {n : Nat} : Computation K R n → Cache K → List Digest32 →
    Option (R × Cache K × List Digest32)
  | .ret result, cache, stream => some (result,cache,stream)
  | .draw key next, cache, stream =>
      match cache key with
      | some answer => run (next answer) cache stream
      | none => match stream with
        | [] => none
        | answer::rest => run (next answer) (put cache key answer) rest

 theorem run_hit {n : Nat} {key : K} {next : Digest32 → Computation K R n}
    {cache : Cache K} {stream : List Digest32} {answer : Digest32}
    (hit : cache key=some answer) :
    run (.draw key next) cache stream=run (next answer) cache stream := by
  rw [run.eq_def]
  dsimp only
  rw [hit]

 theorem run_miss_nil {n : Nat} {key : K} {next : Digest32 → Computation K R n}
    {cache : Cache K} (hit : cache key=none) :
    run (.draw key next) cache []=none := by
  rw [run,hit]

 theorem run_miss_cons {n : Nat} {key : K} {next : Digest32 → Computation K R n}
    {cache : Cache K} {answer : Digest32} {rest : List Digest32} (hit : cache key=none) :
    run (.draw key next) cache (answer::rest)=run (next answer) (put cache key answer) rest := by
  rw [run,hit]

/-- Fresh independent draws, including repeated Unit coordinates in joint. -/
def draws {K R : Type} {n : Nat} : Sampling K (fun _ => Digest32) R n → List Digest32 → Option R
  | .ret result, _ => some result
  | .draw _ next, [] => none
  | .draw _ next, answer::rest => draws (next answer) rest

 theorem draws_pad {K R : Type} {n m : Nat} (bound : n ≤ m)
    (p : Sampling K (fun _ => Digest32) R n) (stream : List Digest32) :
    draws (Sampling.pad bound p) stream = draws p stream := by
  induction p generalizing m stream with
  | ret result => simp only [Sampling.pad,draws]
  | draw key next ih =>
    cases m with
    | zero => omega
    | succ m =>
      cases stream with
      | nil => simp only [Sampling.pad,draws]
      | cons answer rest => simpa only [Sampling.pad,draws] using ih answer _ rest

variable {A B S : Type} [DecidableEq A] [DecidableEq B]

 theorem joint_stream {n m : Nat} (p : Computation A R n) (pc : Cache A)
    (q : Computation B S m) (qc : Cache B) (stream : List Digest32) :
    draws (joint p pc q qc) stream =
      match run p pc stream,run q qc stream with
      | some (r,pc',_),some (s,qc',_) => some ((r,pc'),(s,qc'))
      | _,_ => none := by
  suffices aux : ∀ size n m, n+m=size →
      ∀ (p : Computation A R n) (pc : Cache A) (q : Computation B S m) (qc : Cache B) stream,
      draws (joint p pc q qc) stream =
        match run p pc stream,run q qc stream with
        | some (r,pc',_),some (s,qc',_) => some ((r,pc'),(s,qc'))
        | _,_ => none by
    exact aux (n+m) n m rfl p pc q qc stream
  intro size
  induction size using Nat.strong_induction_on with
  | h size ih =>
    intro n m total p pc q qc stream
    cases p with
    | ret r =>
      cases q with
      | ret s => simp only [joint,draws,run]
      | @draw j key next =>
        cases hit : qc key with
        | some answer =>
          simp only [joint,hit,draws_pad,run]
          rw [run_hit (next := next) hit]
          simpa only [run] using ih (n+j) (by omega) n j rfl (.ret r) pc (next answer) qc stream
        | none =>
          cases stream with
          | nil => simp only [joint,hit,draws_pad,draws,run]
          | cons answer rest =>
            simp only [joint,hit,draws_pad,draws,run]
            have equal := ih (n+j) (by omega) n j rfl (.ret r) pc (next answer) (put qc key answer) rest
            cases finished : run (next answer) (put qc key answer) rest with
            | none => simpa only [run,finished] using equal
            | some result =>
              rcases result with ⟨value,cache,unused⟩
              simpa only [run,finished] using equal
    | @draw i key next =>
      cases q with
      | ret s =>
        cases hit : pc key with
        | some answer =>
          simp only [joint,hit,draws_pad,run]
          rw [run_hit (next := next) hit]
          simpa only [run] using ih (i+m) (by omega) i m rfl (next answer) pc (.ret s) qc stream
        | none =>
          cases stream with
          | nil => simp only [joint,hit,draws_pad,draws,run]
          | cons answer rest =>
            simp only [joint,hit,draws_pad,draws,run]
            have equal := ih (i+m) (by omega) i m rfl (next answer) (put pc key answer) (.ret s) qc rest
            cases finished : run (next answer) (put pc key answer) rest with
            | none => simpa only [run,finished] using equal
            | some result =>
              rcases result with ⟨value,cache,unused⟩
              simpa only [run,finished] using equal
      | @draw j key' next' =>
        cases hit : pc key with
        | some answer =>
          simp only [joint,hit,draws_pad]
          rw [run_hit (next := next) hit]
          simpa only [run] using ih (i+(j+1)) (by omega) i (j+1) rfl (next answer) pc (.draw key' next') qc stream
        | none =>
          cases hit' : qc key' with
          | some answer =>
            simp only [joint,hit,hit',draws_pad]
            rw [run_hit (next := next') hit']
            simpa only [run] using ih ((i+1)+j) (by omega) (i+1) j rfl (.draw key next) pc (next' answer) qc stream
          | none =>
            cases stream with
            | nil => simp only [joint,hit,hit',draws_pad,draws,run]
            | cons answer rest =>
              simp only [joint,hit,hit',draws_pad,draws,run]
              simpa only [run] using ih (i+j) (by omega) i j rfl (next answer) (put pc key answer) (next' answer) (put qc key' answer) rest

 theorem runs_draws {K R : Type} {n : Nat} {p : Sampling K (fun _ => Digest32) R n}
    {trace : List (Sigma (fun _ : K => Digest32))} {result : R}
    (execution : Sampling.Runs p trace result) :
    draws p (trace.map (fun entry => entry.2)) = some result := by
  induction execution with
  | ret result => rfl
  | draw answer execution ih => simpa only [List.map_cons,draws] using ih

#print axioms joint_stream
end Whir.PublicCompressionCouplingStreams
