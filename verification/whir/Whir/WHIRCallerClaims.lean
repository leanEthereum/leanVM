import Whir.WHIRCallerOutputs
import Whir.RingPCSGame

/-! Claim extraction at the actual Flock-to-stack boundary. `decodeFlock` alone
is not a production `ClaimRequest` resolver: CPU additionally has
multiplicity/register rings and both callers have point claims.
`WHIRCallerSource` supplies their concrete bus/GKR, constraints/bit-column,
settled-table, placement and exit-claim interpreter and the complete request
decoder. Flock's algebraic acceptance checks are not claimed here: this extracts
the claims an accepted Flock trace returns. No serialized claim frame,
re-observation, or transcript restart is introduced here.

The extraction was exercised against two genuine Rust `reduction::prove` /
`reduction::verify` fixtures, including matrix checks. Those fixtures use the
baseline Rust transcript; their read/sample traces were framed and their sampled
scalars supplied as prior-output blocks. This tests source claim assembly, not a
Rust implementation of conditional #552's compression mode. -/
namespace Whir.WHIRCallerClaims
open Concrete FiatShamirGame DuplexRefinement DuplexEncoding WHIRCallerOutputs

local instance : DecidableEq Terminal := by
  intro a b
  cases a <;> cases b <;> simp <;> infer_instance

local instance : DecidableEq Coordinate := by
  intro a b
  cases a
  cases b
  simp only [Coordinate.mk.injEq]
  infer_instance

/-- Public placement and dimensions, from `reduction::verify` and `Window::ring`.
Neither points nor slice values are public configuration. -/
structure FlockLayout where
  offset : Nat
  kLog : Nat
  instanceLog : Nat
  deriving DecidableEq, Repr

def FlockLayout.logN (l : FlockLayout) : Nat := l.kLog + l.instanceLog

/-- Only physical outputs at strict entry prefixes are accessible. -/
def priorAnswers (entry : FramedHistory) (answers : Coordinate → Digest32)
    (q : Coordinate) : Digest32 :=
  if q ∈ callerOutputs entry then answers q else zeroDigest

theorem priorAnswers_congr (entry : FramedHistory) (a b : Coordinate → Digest32)
    (agree : ∀ q ∈ callerOutputs entry, a q = b q) :
    priorAnswers entry a = priorAnswers entry b := by
  funext q
  simp only [priorAnswers]
  split
  next h => exact agree q h
  next => rfl

theorem priorAnswers_future (entry : FramedHistory) (answers : Coordinate → Digest32)
    (q : Coordinate) (future : entry.frames.length ≤ q.history.frames.length) :
    priorAnswers entry answers q = zeroDigest := by
  unfold priorAnswers
  split
  next h => have := (callerOutputs_strict_prefix entry q h).2.2.1; omega
  next => rfl

/-- An actual absorb frame and the caller scalars consumed immediately before it.
The lengths are checked; truncated scalar encodings are not padded. -/
structure ScalarFrame where
  before : List E
  sent : List E
  deriving DecidableEq

def scalarFrame (entry : FramedHistory) (answers : Coordinate → Digest32)
    (index : Nat) : Option ScalarFrame := do
  let .absorb consumed bytes ← entry.frames[index]? | none
  if consumed % 24 ≠ 0 then none else do
    let before ← WHIRHistory.parseExact (consumed / 24)
      (recoveredBytes (priorAnswers entry answers)
        {entry with frames := entry.frames.take index} 0 consumed)
    let sent ← WHIRHistory.parseExact (bytes.length / 24) bytes
    pure ⟨before,sent⟩

/-- Flock's real public read/sample schedule. The first vector sample and lambda
share an output run; each round transmits two of three coefficients. The last
read is 64 slices followed by one matrix value per circuit. -/
def flockShape (layouts : List FlockLayout) : List (Nat × Nat) :=
  let m := (layouts.map FlockLayout.logN).foldl max 0
  let rounds := (layouts.map (fun l => l.kLog - 6)).foldl max 0
  [(m - 13 + 1,64)] ++ List.replicate (m - 6) (1,2) ++
    [(1,3 * layouts.length)] ++ List.replicate rounds (1,2) ++
    [(1,65 * layouts.length)]

/-- Reject malformed/non-Flock suffixes, including nonce frames and mismatched
consumption cursors. Earlier caller frames are retained in every output key. -/
def flockFrames (layouts : List FlockLayout) (entry : FramedHistory)
    (answers : Coordinate → Digest32) : Option (List ScalarFrame) := do
  if layouts.isEmpty || layouts.any (fun l => l.kLog < 6 || l.logN < 13) then none else do
    let shape := flockShape layouts
    if entry.frames.length < shape.length then none else do
      let start := entry.frames.length - shape.length
      let frames ← (List.range shape.length).mapM (fun i => scalarFrame entry answers (start+i))
      if frames.map (fun f => (f.before.length,f.sent.length)) = shape then some frames else none

def scalarBefore (frames : List ScalarFrame) (i : Nat) : Option E := do
  let f ← frames[i]?
  match f.before with
  | [x] => some x
  | _ => none

/-- The exact returned slice-claim construction in `lincheck.rs:518` and
`reduction.rs:258-263`: reverse the circuit's own lincheck rounds, then append
its zerocheck outer suffix. This does not assert either sumcheck identity. -/
def assembleFlock (layout : FlockLayout) (zc lc slices : List E) : Option RingPCSGame.FamilyClaim := do
  let rest := layout.kLog - 6
  if layout.kLog < 6 || layout.logN < 13 || lc.length < rest ||
      zc.length < layout.logN - 6 then none else do
    if h : slices.length = 64 then
      pure ⟨layout.offset, ((lc.take rest).reverse ++
        (zc.drop rest).take layout.instanceLog).toArray,
        fun i => slices[i.val]'(by omega)⟩
    else none

/-- The source's `[rest .. m-K_SKIP]` slice has exactly the public instance
dimension. This equality also fixes the direction of the lincheck reversal. -/
theorem assembleFlock_source (layout : FlockLayout) (zc lc slices : List E)
    (hk : 6 ≤ layout.kLog) (hm : 13 ≤ layout.logN)
    (hlc : layout.kLog - 6 ≤ lc.length) (hzc : layout.logN - 6 ≤ zc.length)
    (hs : slices.length = 64) :
    assembleFlock layout zc lc slices =
      some ⟨layout.offset,
        ((lc.take (layout.kLog - 6)).reverse ++
          (zc.drop (layout.kLog - 6)).take
            (layout.logN - 6 - (layout.kLog - 6))).toArray,
        fun i => slices[i.val]'(by omega)⟩ := by
  have hn : layout.logN - 6 - (layout.kLog - 6) = layout.instanceLog := by
    simp only [FlockLayout.logN]
    omega
  simp [assembleFlock, hn, hs, Nat.not_lt.mpr hk, Nat.not_lt.mpr hm,
    Nat.not_lt.mpr hlc, Nat.not_lt.mpr hzc]

/-- Decode the Flock ring claims directly from a hypothetical complete caller
entry, before any WHIR sample. It works equally for actual and early-query
entries, and never accepts claims supplied as metadata. -/
def decodeFlock (layouts : List FlockLayout) (entry : FramedHistory)
    (answers : Coordinate → Digest32) : Option (List RingPCSGame.FamilyClaim) := do
  let frames ← flockFrames layouts entry answers
  let m := (layouts.map FlockLayout.logN).foldl max 0
  let rounds := (layouts.map (fun l => l.kLog - 6)).foldl max 0
  let zc ← (List.range (m-6)).mapM (fun j => scalarBefore frames (j+2))
  let lc ← (List.range rounds).mapM (fun j => scalarBefore frames (m-6+3+j))
  let terminal ← frames[m-6+rounds+2]?
  layouts.zipIdx |>.mapM (fun (layout,i) =>
    assembleFlock layout zc lc ((terminal.sent.drop (65*i)).take 64))

theorem decodeFlock_prior_only (layouts : List FlockLayout) (entry : FramedHistory)
    (a b : Coordinate → Digest32)
    (agree : ∀ q ∈ callerOutputs entry, a q = b q) :
    decodeFlock layouts entry a = decodeFlock layouts entry b := by
  have h : scalarFrame entry a = scalarFrame entry b := by
    funext i
    simp only [scalarFrame, priorAnswers_congr entry a b agree]
  simp only [decodeFlock, flockFrames, h]

/-- Under physical output recovery, early decoding agrees with evaluation of
this same concrete Flock frame parser using the actual compression function. -/
theorem decodeFlock_actual_outputs (layouts : List FlockLayout) (entry : FramedHistory)
    (answers : Coordinate → Digest32) (c : Compression) (iv : Digest32)
    (observed : ∀ q ∈ callerOutputs entry, answers q = evalCoordinate c iv q) :
    decodeFlock layouts entry answers = decodeFlock layouts entry (evalCoordinate c iv) :=
  decodeFlock_prior_only layouts entry answers (evalCoordinate c iv) observed

/-- Full entry identity is retained, not replaced by seed identity. -/
def identifiedFlock (layouts : List FlockLayout) (entry : FramedHistory)
    (answers : Coordinate → Digest32) :
    Option (FramedHistory × List RingPCSGame.FamilyClaim) :=
  (decodeFlock layouts entry answers).map (entry,·)

theorem identifiedFlock_entry (layouts : List FlockLayout) (entry : FramedHistory)
    (answers : Coordinate → Digest32) (other : FramedHistory)
    (claims : List RingPCSGame.FamilyClaim)
    (ok : identifiedFlock layouts entry answers = some (other,claims)) : entry = other := by
  unfold identifiedFlock at ok
  cases h : decodeFlock layouts entry answers <;> simp [h] at ok
  exact ok.1

end Whir.WHIRCallerClaims
