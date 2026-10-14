import Whir.PCSBCSChallengeOracleSource

/-! Executable inverse of the actual WHIR scalar projection. Authentication is
not inferred from scalars: the parent supplies frozen, coordinate-indexed rows
and root-table access. This adapter neither assumes honest commitments nor
creates rows. A nonce is retained as rejection metadata, never a challenge. -/
set_option autoImplicit false
namespace Whir.PCSBCSSourceReplyInversion
open Concrete Protocol CausalGame CausalProbability WHIRHistory FiatShamirGame
open PCSBCSChallengeOracle

/-- Literal source stage and phase; foreign phases reject before parsing. -/
inductive Stage where
  | initial
  | fold (phase round : Nat)
  | ood (phase index : Nat)
  | query (phase : Nat)
  | tail (round : Nat)
  deriving DecidableEq, Repr

def stage {c : Config} : CausalProbability.Coordinate c → Stage
  | .initial => .initial
  | .fold i j => .fold i.val j.val
  | .ood i j => .ood i.val j.val
  | .query i => .query i.val
  | .tail j => .tail j.val

/-- Explicit external frozen data, not a recovery oracle. At a query, `rows q`
is the COMPACT array in query-list order: frozenOracle[derivedQueries[j]],
using the Raw of that strictly earlier query packet from the reconstructed
prefix tape. It is NOT the full root oracle. By contrast `next q digest` is
the FULL next Oracle from the authenticated frozen root registry.
The parent must bind both accesses to that prior public boundary; neither may
depend on the current packet's Raw or its subsequent reply. No relation between
a digest and an honest oracle is assumed. -/
structure FrozenOracles (c : Config) where
  rows : CausalProbability.Coordinate c → Oracle
  next : CausalProbability.Coordinate c → Digest32 → Oracle

structure Inverted where
  reply : Reply
  nonce : Option (Nat × E)

def inverse {c : Config} (frozen : FrozenOracles c)
    (q : CausalProbability.Coordinate c) (source : Stage) (m : Pending) : Option Inverted :=
  if source = stage q then
    (decodeReplyScalars q (frozen.next q) (frozen.rows q) m.scalars).map
      (fun r => ⟨r,m.nonce⟩)
  else none

/-- Reuse the exact canonical scalar-to-digest codec used by WHIR's reply
parser. Only a final nonterminal fold announces a root, at scalar offset two. -/
def announcedRoot {c : Config} (q : CausalProbability.Coordinate c) (m : Pending) :
    Option Digest32 :=
  match q with
  | .fold i j =>
    if j.val+1 = c.folds[i.val]! ∧ i.val+1 < c.folds.size then
      match m.scalars with
      | [_,_,a,b] => ByteCodec.scalarsToHash (a,b)
      | _ => none
    else none
  | _ => none

theorem announcedRoot_roundtrip (c : Config) (i : Fin c.folds.size)
    (j : Fin c.folds[i.val]!) (last : j.val+1 = c.folds[i.val]!)
    (later : i.val+1 < c.folds.size) (a b : E) (root : Digest32)
    (nonce : Option (Nat × E)) :
    announcedRoot (.fold i j) ⟨[a,b] ++ rootScalars root,nonce⟩ = some root := by
  simp [announcedRoot,last,later,rootScalars,ByteCodec.scalarsToHash_hashToScalars]

/-- Exact quotient: coefficients/claims are retained; query rows are erased;
fold next-oracles are erased; middle-fold residuals and nonterminal-boundary
residuals are erased; terminal-boundary residuals are retained. The digest is
explicit side input, fixed on both sides. Malformed tags remain rejected. -/
def ScalarEquivalent {c : Config} (q : CausalProbability.Coordinate c)
    (digest : Digest32) (a b : Reply) : Prop :=
  replyScalars q digest a = replyScalars q digest b

theorem quotient_congr {c : Config} (q : CausalProbability.Coordinate c)
    (digest : Digest32) (frozen : FrozenOracles c) (a b : Reply)
    (same : ScalarEquivalent q digest a b) :
    canonicalReply q digest (frozen.next q) (frozen.rows q) a =
      canonicalReply q digest (frozen.next q) (frozen.rows q) b := by
  rw [← replyScalars_roundtrip, ← replyScalars_roundtrip]
  exact congrArg (fun xs => xs.bind (decodeReplyScalars q (frozen.next q) (frozen.rows q))) same

/-- On the explicitly frozen-compatible domain, the scalar quotient is exactly
semantic equality. Normalization, not an assumption of honest commitments,
removes the unbound fields before this equivalence is asserted. -/
theorem normalized_quotient_eq {c : Config} (q : CausalProbability.Coordinate c)
    (digest : Digest32) (frozen : FrozenOracles c) (a b : Reply)
    (left : canonicalReply q digest (frozen.next q) (frozen.rows q) a = some a)
    (right : canonicalReply q digest (frozen.next q) (frozen.rows q) b = some b) :
    ScalarEquivalent q digest a b ↔ a = b := by
  constructor
  · intro same
    have h := quotient_congr q digest frozen a b same
    rw [left, right] at h
    exact Option.some.inj h
  · intro same
    subst b
    rfl

/-- Roundtrip is canonical equality, not equality of erased semantic fields.
Wrong terminal residual lengths reject rather than being padded or truncated. -/
theorem scalar_roundtrip {c : Config} (frozen : FrozenOracles c)
    (q : CausalProbability.Coordinate c) (digest : Digest32) (r : Reply)
    (nonce : Option (Nat × E)) :
    (replyScalars q digest r).bind (fun xs => inverse frozen q (stage q) ⟨xs,nonce⟩) =
      (canonicalReply q digest (frozen.next q) (frozen.rows q) r).map
        (fun reply => (⟨reply,nonce⟩ : Inverted)) := by
  simpa [inverse] using congrArg
    (Option.map (fun reply => (⟨reply,nonce⟩ : Inverted)))
    (replyScalars_roundtrip q digest (frozen.next q) (frozen.rows q) r)

theorem inverse_wrong_stage {c : Config} (frozen : FrozenOracles c)
    (q : CausalProbability.Coordinate c) (source : Stage) (m : Pending)
    (wrong : source ≠ stage q) : inverse frozen q source m = none := by
  simp [inverse, wrong]

theorem inverse_nonce {c : Config} (frozen : FrozenOracles c)
    (q : CausalProbability.Coordinate c) (source : Stage) (m : Pending) (r : Inverted)
    (parsed : inverse frozen q source m = some r) : r.nonce = m.nonce := by
  unfold inverse at parsed
  split at parsed
  · cases h : decodeReplyScalars q (frozen.next q) (frozen.rows q) m.scalars with
    | none => simp [h] at parsed
    | some reply => simp only [h, Option.map_some, Option.some.injEq] at parsed; cases parsed; rfl
  · contradiction

/-- Source admission alone is syntax admission, not a claim of authenticated
rows or honest evaluation. Given the exact scalar projection, inversion equals
precisely its canonical semantic reply. -/
theorem source_admitted_inverse {p : ParameterBounds.Profile} {Q : Nat} {iv : Digest32}
    {entry : FramedHistory} {current : CausalProbability.Coordinate (ParameterBounds.config p)}
    (packet : SourcePacket p Q iv entry current)
    (frozen : FrozenOracles (ParameterBounds.config p))
    (q : CausalProbability.Coordinate (ParameterBounds.config p))
    (n : Nat) (m : Pending) (digest : Digest32) (r : Reply)
    (_earlier : n < position current)
    (_coordinate : (schedule (ParameterBounds.config p))[n]? = some q)
    (_message : packet.messages.reverse[n+1]? = some m)
    (scalars : replyScalars q digest r = some m.scalars) :
    inverse frozen q (stage q) m =
      (canonicalReply q digest (frozen.next q) (frozen.rows q) r).map
        (fun reply => (⟨reply,m.nonce⟩ : Inverted)) := by
  have h := scalar_roundtrip frozen q digest r m.nonce
  rw [scalars, Option.bind_some] at h
  exact h

/-- Chronological message n+1 is the response to coordinate n. Index zero is
the empty initial Pending. Out-of-range reads reject; there is no fallback to
initial, and no lookup of a reply at the current or a future coordinate. -/
def inverseAt {c : Config} (frozen : FrozenOracles c) (messages : List Pending)
    (n : Nat) : Option Inverted := do
  let q ← (schedule c)[n]?
  let m ← messages.reverse[n+1]?
  inverse frozen q (stage q) m

/-- Correctness at the actual chronological source index. Stage and phase are
selected by the admitted public schedule, not by untrusted scalar contents. -/
theorem inverseAt_source {p : ParameterBounds.Profile} {Q : Nat} {iv : Digest32}
    {entry : FramedHistory} {current : CausalProbability.Coordinate (ParameterBounds.config p)}
    (packet : SourcePacket p Q iv entry current)
    (frozen : FrozenOracles (ParameterBounds.config p))
    (q : CausalProbability.Coordinate (ParameterBounds.config p))
    (n : Nat) (m : Pending) (digest : Digest32) (r : Reply)
    (earlier : n < position current)
    (coordinate : (schedule (ParameterBounds.config p))[n]? = some q)
    (message : packet.messages.reverse[n+1]? = some m)
    (scalars : replyScalars q digest r = some m.scalars) :
    inverseAt frozen packet.messages n =
      (canonicalReply q digest (frozen.next q) (frozen.rows q) r).map
        (fun reply => (⟨reply,m.nonce⟩ : Inverted)) := by
  simp only [inverseAt, coordinate, message]
  exact source_admitted_inverse packet frozen q n m digest r earlier coordinate message scalars

/-- Full semantic equality requires the frozen-field compatibility hypothesis
explicitly. Without it only canonical equality in the scalar quotient holds. -/
theorem inverseAt_source_exact {p : ParameterBounds.Profile} {Q : Nat} {iv : Digest32}
    {entry : FramedHistory} {current : CausalProbability.Coordinate (ParameterBounds.config p)}
    (packet : SourcePacket p Q iv entry current)
    (frozen : FrozenOracles (ParameterBounds.config p))
    (q : CausalProbability.Coordinate (ParameterBounds.config p))
    (n : Nat) (m : Pending) (digest : Digest32) (r : Reply)
    (earlier : n < position current)
    (coordinate : (schedule (ParameterBounds.config p))[n]? = some q)
    (message : packet.messages.reverse[n+1]? = some m)
    (scalars : replyScalars q digest r = some m.scalars)
    (frozenCompatible : canonicalReply q digest (frozen.next q) (frozen.rows q) r = some r) :
    inverseAt frozen packet.messages n = some ⟨r,m.nonce⟩ := by
  rw [inverseAt_source packet frozen q n m digest r earlier coordinate message scalars,
    frozenCompatible]
  rfl

/-- Build only the requested strict prefix. Reverse chronological storage and
the public schedule are computed once, outside the recursive array builder. -/
def prefixReplies {c : Config} (frozen : FrozenOracles c) (messages : List Pending)
    (count : Nat) : Option (Array Reply) :=
  let chronological := messages.reverse
  let qs := schedule c
  let rec loop : Nat → Option (Array Reply)
    | 0 => some #[]
    | n+1 => do
      let prior ← loop n
      let r ← (do
        let q ← qs[n]?
        let m ← chronological[n+1]?
        inverse frozen q (stage q) m)
      pure (prior.push r.reply)
  loop count

theorem prefixReplies_succ {c : Config} (frozen : FrozenOracles c)
    (messages : List Pending) (n : Nat) :
    prefixReplies frozen messages (n+1) = (do
      let prior ← prefixReplies frozen messages n
      let r ← inverseAt frozen messages n
      pure (prior.push r.reply)) := rfl

def replies {c : Config} (frozen : FrozenOracles c) (messages : List Pending) :
    Option (Array Reply) :=
  if messages ≠ [] ∧ scheduledAdmissible c messages = true then
    prefixReplies frozen messages (messages.length-1)
  else none

theorem prefixReplies_size {c : Config} (frozen : FrozenOracles c)
    (messages : List Pending) (n : Nat) (answers : Array Reply)
    (parsed : prefixReplies frozen messages n = some answers) : answers.size = n := by
  induction n generalizing answers with
  | zero => simp only [prefixReplies] at parsed; cases parsed; rfl
  | succ n ih =>
    rw [prefixReplies_succ] at parsed
    cases hp : prefixReplies frozen messages n with
    | none => simp [hp] at parsed
    | some prior =>
      cases hr : inverseAt frozen messages n with
      | none => simp [hp,hr] at parsed
      | some r =>
        simp only [hp,hr] at parsed
        cases parsed
        simp [ih prior hp]

/-- The array index used by `incomingData` is exactly the source response
position, never the position of the Pending that carries that response. -/
theorem prefixReplies_index {c : Config} (frozen : FrozenOracles c)
    (messages : List Pending) (count : Nat) (answers : Array Reply)
    (parsed : prefixReplies frozen messages count = some answers)
    (n : Nat) (earlier : n < count) :
    (inverseAt frozen messages n).map Inverted.reply = answers[n]? := by
  induction count generalizing answers with
  | zero => omega
  | succ count ih =>
    rw [prefixReplies_succ] at parsed
    cases hp : prefixReplies frozen messages count with
    | none => simp [hp] at parsed
    | some prior =>
      cases hr : inverseAt frozen messages count with
      | none => simp [hp,hr] at parsed
      | some r =>
        simp only [hp,hr] at parsed
        cases parsed
        have size := prefixReplies_size frozen messages count prior hp
        by_cases last : n = count
        · subst n
          rw [hr]
          change some r.reply = (prior.push r.reply)[count]?
          rw [← size]
          simp
        · have before : n < count := by omega
          rw [ih prior hp before]
          simp [Array.getElem?_push, size, Nat.ne_of_lt before]

/-- A strong no-late-read property: successful prefix reconstruction is
unchanged by ANY changes outside the inverse results at strict earlier indexes. -/
theorem prefixReplies_congr {c : Config} (f g : FrozenOracles c)
    (left right : List Pending) (count : Nat)
    (same : ∀ n, n < count → inverseAt f left n = inverseAt g right n) :
    prefixReplies f left count = prefixReplies g right count := by
  induction count with
  | zero => rfl
  | succ count ih =>
    simp only [prefixReplies_succ, ih (fun n hn => same n (by omega)), same count (by omega)]

theorem packet_replies {p : ParameterBounds.Profile} {Q : Nat} {iv : Digest32}
    {entry : FramedHistory} {q : CausalProbability.Coordinate (ParameterBounds.config p)}
    (packet : SourcePacket p Q iv entry q) (frozen : FrozenOracles (ParameterBounds.config p)) :
    replies frozen packet.messages = prefixReplies frozen packet.messages (position q) := by
  unfold replies
  rw [ite_eq_left ⟨packet.nonempty,packet.admitted⟩, packet.position_eq]

theorem packet_reply_index {p : ParameterBounds.Profile} {Q : Nat} {iv : Digest32}
    {entry : FramedHistory} {q : CausalProbability.Coordinate (ParameterBounds.config p)}
    (packet : SourcePacket p Q iv entry q) (frozen : FrozenOracles (ParameterBounds.config p))
    (answers : Array Reply) (parsed : replies frozen packet.messages = some answers)
    (n : Nat) (earlier : n < position q) :
    (inverseAt frozen packet.messages n).map Inverted.reply = answers[n]? := by
  rw [packet_replies] at parsed
  exact prefixReplies_index frozen packet.messages (position q) answers parsed n earlier

/-- Even the underlying coordinate-indexed parser cannot find a current or
future response inside a SourcePacket. This is independent of scalar values
and of the supplied oracle accessor. -/
theorem packet_inverse_not_future {p : ParameterBounds.Profile} {Q : Nat} {iv : Digest32}
    {entry : FramedHistory} {q : CausalProbability.Coordinate (ParameterBounds.config p)}
    (packet : SourcePacket p Q iv entry q) (frozen : FrozenOracles (ParameterBounds.config p))
    (n : Nat) (future : position q ≤ n) :
    inverseAt frozen packet.messages n = none := by
  have missing : packet.messages.reverse[n+1]? = none := by
    apply List.getElem?_eq_none
    rw [List.length_reverse]
    have pos := packet.position_eq
    omega
  simp only [inverseAt, missing]
  cases (schedule (ParameterBounds.config p))[n]? <;> rfl

#print axioms announcedRoot_roundtrip
#print axioms normalized_quotient_eq
#print axioms inverse_nonce
#print axioms inverseAt_source
#print axioms inverseAt_source_exact
#print axioms prefixReplies_size
#print axioms packet_inverse_not_future
#print axioms prefixReplies_index
#print axioms prefixReplies_congr
#print axioms packet_reply_index
#print axioms quotient_congr
#print axioms scalar_roundtrip
#print axioms source_admitted_inverse
end Whir.PCSBCSSourceReplyInversion
