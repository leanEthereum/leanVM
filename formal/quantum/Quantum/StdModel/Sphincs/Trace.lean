module

public import Quantum.StdModel.Sphincs.Extract
public import Quantum.StdModel.World

@[expose] public section

/-!
# The verification trace as a classical computation

A reduction decides the trace-local events of a forgery (`EvEncT`, `EvTcrT`, `EvCpreT` at
`Extract.traceH`) from the forgery's verification trace, which it computes by running the verifier
with the world's hash and recording every hashed input (`recVerify`). At a fixed table this is the
verifier's query list `Extract.verifyQueries` (`simulateQ_recVerify`), so the recorded inputs and
the hash at them give `Extract.traceH` (`traceOf`, `traceOf_eq`).
-/

open OracleComp OracleSpec
open HashSig hiding PublicKey
open Sphincs hiding HashDomain
open Common.SufCma (SchemeHashSpec)

namespace Quantum.StdModel.Sphincs

variable {ι : Type} {O : OracleSpec.{0, 0} ι}

/-- The hash recorded: each query answered by `hash`, its input appended to the state. -/
noncomputable def recImpl (hash : HashInput → OracleComp O HashOutput) :
    QueryImpl SchemeHashSpec (StateT (List HashInput) (OracleComp O)) :=
  fun x ↦ do
    let o ← (liftM (hash x) : StateT (List HashInput) (OracleComp O) HashOutput)
    modify (· ++ [x])
    pure o

/-- **The recorded verification**: the verifier of the hash-query form answered by `hash`, with
the list of hashed inputs. -/
noncomputable def recVerify (hash : HashInput → OracleComp O HashOutput) (pk : PublicKey)
    (M : Message) (σ : Signature) : OracleComp O (Bool × List HashInput) :=
  (simulateQ (recImpl hash)
    (Quantum.Sphincs.WithHash.verify Quantum.Sphincs.WithHash.hashQuery pk M σ)).run []

/-- At hashes answering purely, a recorded computation returns its evaluation and its queries. -/
theorem simulateQ_run_recImpl {r : Type → Type} [Monad r] [LawfulMonad r]
    (impl : QueryImpl O r) (hash : HashInput → OracleComp O HashOutput)
    (h : HashInput → HashOutput) (hh : ∀ x, simulateQ impl (hash x) = pure (h x)) {α : Type}
    (x : OracleComp SchemeHashSpec α) (l : List HashInput) :
    simulateQ impl ((simulateQ (recImpl hash) x).run l) =
      pure (evalWithAnswerFn (Extract.idH h) x, l ++ Quantum.SufCma.queries (Extract.idH h) x) := by
  induction x using OracleComp.inductionOn generalizing l with
  | pure a =>
    simp [Quantum.SufCma.queries, Quantum.SufCma.trace_pure]
  | query_bind t k ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    have hq : (recImpl hash t).run l = (fun o ↦ (o, l ++ [t])) <$> hash t := by
      simp [recImpl, StateT.run_bind, StateT.run_monadLift, StateT.run_modify]
    rw [hq, bind_map_left, simulateQ_bind, hh, pure_bind]
    have hk := ih (h t) (l ++ [t])
    have hqt : Quantum.SufCma.queries (Extract.idH h)
        ((liftM (SchemeHashSpec.query t) : OracleComp SchemeHashSpec _) >>= k) =
        [t] ++ Quantum.SufCma.queries (Extract.idH h) (k (h t)) :=
      Quantum.SufCma.trace_query_bind (Extract.idH h) (fun t ↦ [t]) t k
    simp only [hqt, evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query]
    convert hk using 3
    · rfl
    · simp [List.append_assoc]

/-- **The recorded verification at pure answers** is the verification with its query list. -/
theorem simulateQ_recVerify {r : Type → Type} [Monad r] [LawfulMonad r]
    (impl : QueryImpl O r) (hash : HashInput → OracleComp O HashOutput)
    (h : HashInput → HashOutput) (hh : ∀ x, simulateQ impl (hash x) = pure (h x))
    (pk : PublicKey) (M : Message) (σ : Signature) :
    simulateQ impl (recVerify hash pk M σ) =
      pure (evalWithAnswerFn (Extract.idH h)
          (Quantum.Sphincs.WithHash.verify Quantum.Sphincs.WithHash.hashQuery pk M σ),
        Extract.verifyQueries h pk M σ) := by
  rw [recVerify, simulateQ_run_recImpl impl hash h hh, List.nil_append]
  rfl

/-- **The trace from recorded inputs and their hashes**: `some (out x)` at a recorded input. -/
def traceOf (xs : List HashInput) (out : HashInput → HashOutput) :
    HashInput → Option HashOutput :=
  fun x ↦ if x ∈ xs then some (out x) else none

theorem traceOf_eq (h : HashInput → HashOutput) (pk : PublicKey) (M : Message)
    (σ : Signature) : traceOf (Extract.verifyQueries h pk M σ) h = Extract.traceH h pk M σ :=
  rfl

end Quantum.StdModel.Sphincs

end
