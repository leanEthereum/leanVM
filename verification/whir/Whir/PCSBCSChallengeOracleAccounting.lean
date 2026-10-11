import Whir.PCSBCSChallengeOracleSource

/-! Exact request ledger. Direct calls of every purpose (including Merkle
verification) cost one; every continuation block charges its entire construction
path. Repetitions are charged, irrespective of global memoization. -/
set_option autoImplicit false
namespace Whir.PCSBCSChallengeOracle
open Concrete Protocol CausalGame CausalProbability WHIRHistory PCSBCSRounds
open FiatShamirGame DuplexModeGame DuplexFraming
open scoped BigOperators

def requestCost (queries : List Query) : Nat := (queries.map Query.cost).sum

def requests {R : Type} : List Query → (List Digest32 → Program R) → Program R
  | [], next => next []
  | q :: qs, next => .ask q (fun d => requests qs (fun ds => next (d :: ds)))

/-- Exact prefix budget composes with any adaptive suffix, not merely an honest
verifier or a challenge-only observer. No Merkle-domain call is forgotten. -/
theorem requests_counted {R : Type} (queries : List Query) (remaining : Nat)
    (next : List Digest32 → Program R) (suffix : ∀ ds, Counts remaining (next ds)) :
    Counts (requestCost queries + remaining) (requests queries next) := by
  induction queries generalizing next with
  | nil => simpa [requestCost, requests] using suffix []
  | cons q qs ih =>
    simp only [requests, Counts, requestCost, List.map_cons, List.sum_cons]
    constructor
    · omega
    · intro d
      have h := ih (fun ds => next (d :: ds)) (fun ds => suffix (d :: ds))
      simp only [requestCost] at h
      convert h using 1
      omega

theorem requests_real_cost {R : Type} (queries : List Query)
    (oracle : PrimitiveOracle) (iv : Digest32) (next : List Digest32 → Program R) :
    (runReal oracle iv (requests queries next)).primitiveCost =
      requestCost queries + (runReal oracle iv
        (next (queries.map (realAnswer oracle iv)))).primitiveCost := by
  induction queries generalizing next with
  | nil => simp [requests, requestCost]
  | cons q qs ih => simp [requests, runReal, prepend, ih, requestCost, Nat.add_assoc]

namespace SourcePacket
variable {p : ParameterBounds.Profile} {Q : Nat} {iv : Digest32}
  {entry : FramedHistory} {q : CausalProbability.Coordinate (ParameterBounds.config p)}

def queries (s : SourcePacket p Q iv entry q) : List Query :=
  List.ofFn (fun b : Fin (blocks (rawWidth q)) => .construction (s.coordinate b) (s.valid b))

theorem request_number (s : SourcePacket p Q iv entry q) :
    s.queries.length = (24*rawWidth q+31)/32 := by
  simp [queries, blocks]

theorem exact_path_cost (s : SourcePacket p Q iv entry q) :
    requestCost s.queries = ∑ b : Fin (blocks (rawWidth q)), pathCost (s.coordinate b) := by
  simp [requestCost, queries, Query.cost, List.sum_ofFn]

/-- Caller/anchor and serialized prover/nonce work are included in EVERY
uncached root-to-output path. No block or repeated request is free. -/
theorem exact_framed_cost (s : SourcePacket p Q iv entry q) :
    requestCost s.queries = blocks (rawWidth q) *
      (2 + (entry.frames.flatMap DuplexEncoding.framePlan).length +
        ((WHIRHistoryKey.canonicalFrames (WHIRHistoryKey.stackWidth (ParameterBounds.config p))
          s.messages).flatMap DuplexEncoding.framePlan).length) := by
  rw [s.exact_path_cost]
  simp_rw [coordinate, WHIRCallerPrefix.pathCostFrom _
    (WHIRHistoryKey.stackWidth_positive p) entry
    (WHIRHistoryKey.scheduled_normal _ _ s.nonempty s.admitted)]
  simp

/-- Eight E needs six 32-byte output blocks, not eight truncated RO calls. -/
theorem initial_output_blocks : blocks 8 = 6 := by decide

end SourcePacket

/-- Aggregate mode cap for a completed list of packet requests and arbitrary
public calls. This identity includes every repeated request at its full cost. -/
theorem aggregate_query_cost (packets : List (List Query)) (publicQueries : List Query) :
    requestCost (packets.flatten ++ publicQueries) =
      (packets.map requestCost).sum + requestCost publicQueries := by
  have append (xs ys : List Query) :
      requestCost (xs ++ ys) = requestCost xs + requestCost ys := by
    simp [requestCost]
  have flattened : requestCost packets.flatten = (packets.map requestCost).sum := by
    induction packets with
    | nil => simp [requestCost]
    | cons packet packets ih =>
      simp only [List.flatten_cons,append,List.map_cons,List.sum_cons,ih]
  rw [append,flattened]

#print axioms requests_counted
#print axioms requests_real_cost
#print axioms SourcePacket.exact_path_cost
#print axioms SourcePacket.exact_framed_cost
#print axioms aggregate_query_cost
end Whir.PCSBCSChallengeOracle
