import Whir.WHIRCallerClaims
import Whir.CausalBindingState

/-! Executable claim-producing projection of the two production fresh-stack
callers: `cpu/reduce.rs::verify_core` and `rec/proof.rs::verify_core`. Recursive
verifier rows call those same routines. Direct PCS users and Flock benchmarks
retain their separate caller-bound public-claims contract.

The public configuration contains layout/shape data and public outputs, not
returned claims, a user instruction tape, or a decoder. The concrete program
covers GKR's radix-four/binary point order, shared framework-column deduplication,
table sumcheck point reversal, ordered bit-field reconstruction, settled-table
merging, Flock/producer/register rings, and point/port/sliced/exit placement.
`callerShape`, `callerProfile`, `callerLanes`, `callerEntryLength`, and
`callerOutputCap` compute public metadata. The decoder checks supplied opening
geometry against it. `decodeAvailableRequest` additionally rejects missing
preceding output samples instead of substituting arbitrary values.

This is a claim projection, not a proof of the enclosing caller's arithmetic
soundness. Arithmetic acceptance checks which do not alter transcript control
or returned claims remain obligations of successful source verification.
`decodeRequest_physical_source` connects the concrete interpreter's returned
claims to actual framed bytes and preceding physical streams, without a generic
decoder correctness hypothesis or any announcement of claims.

`initialRoot` reads only the initial absorb-zero frame, before any caller draw
or proof-of-work step. `sourceClaims_initialPrefix` and
`interpretCaller_initialRoot` prove that the original token-only source parser
returns that same root: scalar-prefix replay followed by normalized framing
establishes agreement, without adding an acceptance guard. The CPU announcement
factoring is equated to its original loop by `readAnnouncements_loop`.

Source assembly was exercised against fully verified baseline Rust CPU and
recursion proofs, including all returned point and ring claims. Their read/sample
traces are transported through the conditional framing model using the recorded
caller outputs. This does not claim baseline Rust implements conditional #552's
compression mode; that mode's physical recovery is the separate checked theorem.
No claims are observed again and no sampler is restarted. -/
namespace Whir.WHIRCallerClaims
open Concrete FiatShamirGame DuplexRefinement DuplexEncoding WHIRCallerOutputs ParameterBounds
inductive CallerToken where
  | sent (value : E)
  | draw (value : E)
  | nonce (bits : Nat) (value : Scalar24)
  deriving DecidableEq

def tokenOperation : CallerToken → WHIRCallerShape.Operation
  | .sent x => .absorb (WHIRHistory.scalarBytes [x])
  | .draw _ => .squeeze 24
  | .nonce bits value => .nonce bits value

/-- Pure framing check. This neither evaluates a fresh transcript nor draws any
randomness: output values come only from physical prior-output coordinates. -/
def tokenHistory (domain statement : Digest32) (tokens : List CallerToken) : FramedHistory :=
  (closeRun (WHIRCallerShape.runOperations
    (WHIRCallerShape.seedModel domain statement) (tokens.map tokenOperation))).history

def tokensFromFrame (f : Frame) (output : List Byte) : Option (List CallerToken) := do
  let n := previousConsumed f
  if n % 24 ≠ 0 then none else do
    let draws ← WHIRHistory.parseExact (n / 24) output
    let suffix ← match f with
      | .absorb _ bytes => do
        let sent ← WHIRHistory.parseExact (bytes.length / 24) bytes
        pure (sent.map CallerToken.sent)
      | .nonce _ bits value => pure [.nonce bits value]
    pure (draws.map CallerToken.draw ++ suffix)

def frameTokens (entry : FramedHistory) (answers : Coordinate → Digest32)
    (i : Nat) (f : Frame) : Option (List CallerToken) :=
  tokensFromFrame f (recoveredBytes (priorAnswers entry answers)
    {entry with frames := entry.frames.take i} 0 (previousConsumed f))

/-- The actual caller interpreter obtains preceding challenge bytes by replaying
the physical stream, independently of the decoder's output-answer cache. -/
def sourceFrameTokens (c : Compression) (iv : Digest32) (entry : FramedHistory)
    (i : Nat) (f : Frame) : Option (List CallerToken) :=
  tokensFromFrame f (stream c (evalHistory c iv {entry with frames := entry.frames.take i})
    0 (previousConsumed f))

theorem frameTokens_source (c : Compression) (iv : Digest32) (entry : FramedHistory)
    (answers : Coordinate → Digest32)
    (observed : ∀ q ∈ callerOutputs entry, answers q = evalCoordinate c iv q)
    (i : Nat) (f : Frame) (atFrame : entry.frames[i]? = some f) :
    frameTokens entry answers i f = sourceFrameTokens c iv entry i f := by
  obtain ⟨hi,hf⟩ := List.getElem?_eq_some_iff.mp atFrame
  have split : entry.frames = entry.frames.take i ++ f :: entry.frames.drop (i+1) := by
    rw [← hf, ← List.drop_eq_getElem_cons hi, List.take_append_drop]
  have observed' : ∀ q ∈ callerOutputs entry,
      priorAnswers entry answers q = evalCoordinate c iv q := by
    intro q hq
    simpa [priorAnswers, hq] using observed q hq
  unfold frameTokens sourceFrameTokens
  rw [callerBytes_recovery c iv entry (priorAnswers entry answers) observed'
    (entry.frames.take i) f (entry.frames.drop (i+1)) split 0 (previousConsumed f) (by omega)]

private theorem option_mapM_congr {α β : Type} (xs : List α) (f g : α → Option β)
    (agree : ∀ x ∈ xs, f x = g x) : xs.mapM f = xs.mapM g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx := agree x (by simp)
    have ht := ih (fun y hy => agree y (by simp [hy]))
    simp [List.mapM_cons, hx, ht]

def entryTokens (entry : FramedHistory) (answers : Coordinate → Digest32) : Option (List CallerToken) := do
  let frames ← entry.frames.zipIdx.mapM (fun (f,i) => frameTokens entry answers i f)
  let tokens := frames.flatten
  if tokenHistory entry.domain entry.statement tokens = entry then some tokens else none

theorem entryTokens_prior_only (entry : FramedHistory) (a b : Coordinate → Digest32)
    (agree : ∀ q ∈ callerOutputs entry, a q = b q) :
    entryTokens entry a = entryTokens entry b := by
  simp only [entryTokens, frameTokens, priorAnswers_congr entry a b agree]

theorem entryTokens_history (entry : FramedHistory) (answers : Coordinate → Digest32)
    (tokens : List CallerToken) (ok : entryTokens entry answers = some tokens) :
    tokenHistory entry.domain entry.statement tokens = entry := by
  unfold entryTokens at ok
  cases h : entry.frames.zipIdx.mapM (fun (f,i) => frameTokens entry answers i f) with
  | none => simp [h] at ok
  | some frames =>
    simp only [h] at ok
    by_cases hh : tokenHistory entry.domain entry.statement frames.flatten = entry
    · have ht : frames.flatten = tokens := by simpa [hh] using ok
      simpa [← ht] using hh
    · simp [hh] at ok

def sourceTokens (c : Compression) (iv : Digest32) (entry : FramedHistory) :
    Option (List CallerToken) := do
  let frames ← entry.frames.zipIdx.mapM (fun (f,i) => sourceFrameTokens c iv entry i f)
  let tokens := frames.flatten
  if tokenHistory entry.domain entry.statement tokens = entry then some tokens else none

theorem entryTokens_source (c : Compression) (iv : Digest32) (entry : FramedHistory)
    (answers : Coordinate → Digest32)
    (observed : ∀ q ∈ callerOutputs entry, answers q = evalCoordinate c iv q) :
    entryTokens entry answers = sourceTokens c iv entry := by
  have h := option_mapM_congr entry.frames.zipIdx
    (fun (f,i) => frameTokens entry answers i f)
    (fun (f,i) => sourceFrameTokens c iv entry i f) (by
      intro x hx
      exact frameTokens_source c iv entry answers observed x.2 x.1
        (List.mem_zipIdx_iff_getElem?.mp hx))
  simp only [entryTokens, sourceTokens, h]

abbrev CallerParser := StateT (List CallerToken) Option

def readScalar : CallerParser E
  | .sent x :: rest => some (x,rest)
  | _ => none

def drawScalar : CallerParser E
  | .draw x :: rest => some (x,rest)
  | _ => none

def readScalars : Nat → CallerParser (List E)
  | 0 => pure []
  | n+1 => do
    let x ← readScalar
    let xs ← readScalars n
    pure (x :: xs)

def drawScalars : Nat → CallerParser (List E)
  | 0 => pure []
  | n+1 => do
    let x ← drawScalar
    let xs ← drawScalars n
    pure (x :: xs)

theorem readScalars_sent (xs : List E) (rest : List CallerToken) :
    readScalars xs.length (xs.map CallerToken.sent ++ rest) = some (xs,rest) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change (readScalars xs.length (xs.map CallerToken.sent ++ rest)).bind
      (fun (ys,tail) => some (x :: ys,tail)) = _
    rw [ih]
    rfl

theorem drawScalars_draw (xs : List E) (rest : List CallerToken) :
    drawScalars xs.length (xs.map CallerToken.draw ++ rest) = some (xs,rest) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change (drawScalars xs.length (xs.map CallerToken.draw ++ rest)).bind
      (fun (ys,tail) => some (x :: ys,tail)) = _
    rw [ih]
    rfl

def check (ok : Bool) : CallerParser Unit :=
  if ok then pure () else fun _ => none

def nonce (bits : Nat) : CallerParser Unit
  | .nonce actual _ :: rest => if actual = bits then some ((),rest) else none
  | _ => none

/-- Only layout attributes affecting `Side::decompose`'s claim-producing branch.
Owned table coordinates are never read here. Complex framework coordinates are
invalid in Rust and rejected rather than silently converted to column reads. -/
inductive BusCoord where
  | column (index : Nat)
  | publicValue
  | tableExpression
  deriving DecidableEq, Repr

structure BusBlock where
  kappa : Nat
  tableOwned : Bool
  coords : List BusCoord
  deriving DecidableEq, Repr

structure BusProducer where
  kappa : Nat
  bits : Nat
  window : Nat
  deriving DecidableEq, Repr

structure BusLayout where
  push : List BusBlock
  pull : List BusBlock
  producers : List BusProducer
  grinding : Nat
  deriving DecidableEq, Repr

/-- `BusSetup::new`: each side is stacked independently; producers are push-only. -/
def BusLayout.mu (l : BusLayout) : Nat :=
  let push := (l.push.map (fun b => 2^b.kappa)).sum +
    (l.producers.map (fun p => p.bits * 2^p.kappa)).sum
  let pull := (l.pull.map (fun b => 2^b.kappa)).sum
  Nat.log2 (max (max push pull) 1 - 1) + if max push pull ≤ 1 then 0 else 1

structure ColumnClaim where
  column : Nat
  point : List E
  value : E
  deriving DecidableEq

/-- Exact radix-four GKR challenge ordering from `gkr::verify_products`.
Coefficients and child values do not enter the returned point. -/
def gkrPoint (mu : Nat) : CallerParser (List E) := do
  let _ ← readScalar
  let _ ← drawScalar
  let mut point := []
  if mu % 2 = 1 then
    let _ ← readScalars 4
    let x ← drawScalar
    let _ ← drawScalar
    point := [x]
  for _ in List.range (mu / 2) do
    let rounds ← (List.range point.length).mapM (fun _ => do
      let _ ← readScalars 4
      drawScalar)
    let _ ← readScalars 8
    let low ← drawScalar
    let high ← drawScalar
    let _ ← drawScalar
    point := low :: high :: rounds
  pure point

/-- The shared `(column,kappa)` cache preserves first occurrence in push/pull,
block, coordinate order. Producer bits and owned tables cause no column reads. -/
def busClaims (layout : BusLayout) : CallerParser (List E × List ColumnClaim) := do
  if layout.grinding > 0 then nonce layout.grinding
  let _ ← drawScalars 4
  let _ ← drawScalar
  let point ← gkrPoint layout.mu
  let mut known : List (Nat × Nat) := []
  let mut claims := []
  for block in layout.push ++ layout.pull do
    check (block.kappa ≤ point.length)
    if !block.tableOwned then
      for coord in block.coords do
        match coord with
        | .column col =>
          if (col,block.kappa) ∉ known then
            let value ← readScalar
            known := known ++ [(col,block.kappa)]
            claims := claims ++ [⟨col,point.take block.kappa,value⟩]
        | .publicValue => pure ()
        | .tableExpression => check false
  pure (point,claims)

structure BitField where
  column : Nat
  width : Nat
  deriving DecidableEq, Repr

structure AirLayout where
  tau : Nat
  columns : Nat
  publicColumns : Nat
  fields : List BitField
  deriving DecidableEq, Repr

structure TableClaims where
  point : List E
  evals : List E
  slices : List E
  deriving DecidableEq

/-- `BitColumns::field_of`: field order determines slice offsets. -/
def fieldOf (column : Nat) : List BitField → Nat → Option (BitField × Nat)
  | [], _ => none
  | f :: fs, offset => if f.column = column then some (f,offset)
      else fieldOf column fs (offset+f.width)

/-- `BitColumns::combine` uses polynomial-basis words, not E powers of two. -/
def combineBits (bits : List E) : E :=
  (bits.zipIdx.map (fun (x,b) => x * E.ofK (UInt64.ofNat (2^b)))).foldl (· + ·) 0

def receiveTable (layout : AirLayout) (point : List E) : CallerParser TableClaims := do
  check (layout.publicColumns ≤ layout.columns && layout.tau ≤ point.length)
  let n := layout.columns - layout.publicColumns
  check (layout.fields.all (fun f => f.column < n && f.width ≤ 64))
  check ((layout.fields.map BitField.column).eraseDups.length == layout.fields.length)
  let sent ← readScalars (n-layout.fields.length)
  let slices ← readScalars ((layout.fields.map BitField.width).sum)
  let mut cursor := sent
  let mut evals := []
  for c in List.range n do
    match fieldOf c layout.fields 0 with
    | some (f,start) =>
      evals := evals ++ [combineBits ((slices.drop start).take f.width)]
    | none =>
      match cursor with
      | [] => check false
      | x :: xs => evals := evals ++ [x]; cursor := xs
  check cursor.isEmpty
  pure ⟨point.take layout.tau,evals,slices⟩

/-- `constraints::verify` binds high coordinates first and stores them in reverse
round order, then receives each table's ordinary values and bit slices. -/
def constraintClaims (layouts : List AirLayout) (busPoint : List E) :
    CallerParser (List TableClaims) := do
  let n := (layouts.map AirLayout.tau).foldl max 0
  check (n ≤ busPoint.length)
  let rounds ← (List.range n).mapM (fun _ => do
    let _ ← readScalars 3
    drawScalar)
  layouts.mapM (fun l => receiveTable l rounds.reverse)

/-- Direct statement-producing projection of `reduction::verify`.
Its wire reads and sampled coordinates are not supplied by configuration. -/
def flockClaims (layouts : List FlockLayout) : CallerParser (List RingPCSGame.FamilyClaim) := do
  check (!layouts.isEmpty && layouts.all (fun l => 6 ≤ l.kLog && 13 ≤ l.logN))
  let m := (layouts.map FlockLayout.logN).foldl max 0
  let rounds := (layouts.map (fun l => l.kLog-6)).foldl max 0
  let _ ← drawScalars (m-13)
  let _ ← drawScalar
  let _ ← readScalars 64
  let _ ← drawScalar
  let zc ← (List.range (m-6)).mapM (fun _ => do
    let _ ← readScalars 2
    drawScalar)
  let _ ← readScalars (3*layouts.length)
  let _ ← drawScalar
  let lc ← (List.range rounds).mapM (fun _ => do
    let _ ← readScalars 2
    drawScalar)
  layouts.mapM (fun layout => do
    let slices ← readScalars 64
    let _ ← readScalar
    match assembleFlock layout zc lc slices with
    | some claim => pure claim
    | none => fun _ => none)

inductive Placement where
  | committed (offset dimension : Nat)
  | port (offset slot strideLog : Nat)
  | sliced
  deriving DecidableEq, Repr

def placeClaim (p : Placement) (c : ColumnClaim) : Option RingPCSGame.PointClaim :=
  match p with
  | .committed offset _ => some (.point offset c.point.toArray c.value)
  | .port offset slot stride => some (.strided offset slot stride c.point.toArray c.value)
  | .sliced => none

def placeClaims (placements : Array Placement) (claims : List ColumnClaim) :
    Option (Array RingPCSGame.PointClaim) := do
  let located ← claims.mapM (fun c => do
    let p ← placements[c.column]?
    pure (placeClaim p c))
  pure ((located.filterMap id).toArray)

def tableColumns (base : Nat) (claims : TableClaims) : List ColumnClaim :=
  claims.evals.zipIdx.map (fun (x,i) => ⟨base+i,claims.point,x⟩)

/-- `SliceClaim::zero_padded`, without accepting more than 64 slices. -/
def paddedRing (offset : Nat) (point slices : List E) : Option RingPCSGame.FamilyClaim :=
  if slices.length ≤ 64 then some ⟨offset,point.toArray,fun i => slices[i.val]?.getD 0⟩ else none

structure RecLayout where
  bus : BusLayout
  tables : List (Nat × AirLayout)
  placements : Array Placement
  hash : FlockLayout
  logInvRate : Nat

structure CpuTableLayout where
  base : Nat
  tau : Nat
  committedColumns : Nat
  settled : Bool
  summedColumns : List Nat
  summedBits : List BitField
  deriving DecidableEq, Repr

def CpuTableLayout.air (t : CpuTableLayout) : AirLayout :=
  ⟨t.tau,t.summedColumns.length,0,t.summedBits⟩

structure RegisterWord where
  offset : Nat
  tables : List Nat
  deriving DecidableEq, Repr

structure CpuLayout where
  bus : BusLayout
  tables : List CpuTableLayout
  placements : Array Placement
  flock : List FlockLayout
  registers : List RegisterWord
  finalRegisterColumn : Nat
  output : Fin 4 → UInt64
  logInvRate : Nat

structure CallerClaims where
  root : Digest32
  families : List RingPCSGame.FamilyClaim
  points : Array RingPCSGame.PointClaim

def readRoot : CallerParser Digest32 := do
  let a ← readScalar
  let b ← readScalar
  match ByteCodec.scalarsToHash (a,b) with
  | some root => pure root
  | none => fun _ => none

@[inline] def recPayload (layout : RecLayout) :
    CallerParser (List RingPCSGame.FamilyClaim × Array RingPCSGame.PointClaim) := do
  let (point,bus) ← busClaims layout.bus
  let _ ← drawScalar
  let tables ← constraintClaims (layout.tables.map Prod.snd) point
  let rings ← flockClaims [layout.hash]
  let columns := bus ++ ((layout.tables.map Prod.fst).zip tables).flatMap
    (fun (base,claims) => tableColumns base claims)
  match placeClaims layout.placements columns with
  | some points => pure (rings,points)
  | none => fun _ => none

def recClaims (layout : RecLayout) : CallerParser CallerClaims := do
  let root ← readRoot
  let (rings,points) ← recPayload layout
  pure ⟨root,rings,points⟩

def settledClaims (tables : List CpuTableLayout) (point : List E) : CallerParser (List TableClaims) := do
  let mut claims := []
  for table in tables do
    if table.settled then
      check (table.summedColumns.all (· < table.committedColumns))
      check (table.summedColumns.eraseDups.length == table.summedColumns.length)
      let sent ← readScalars (table.committedColumns-table.summedColumns.length)
      let mut remaining := sent
      let mut evals := []
      for c in List.range table.committedColumns do
        if c ∈ table.summedColumns then evals := evals ++ [0]
        else
          match remaining with
          | [] => check false
          | x :: xs => evals := evals ++ [x]; remaining := xs
      check (table.tau ≤ point.length && remaining.isEmpty)
      claims := claims ++ [⟨point.take table.tau,evals,[]⟩]
  pure claims

def exitClaims (column : Nat) (output : Fin 4 → UInt64) : List ColumnClaim :=
  let claim := fun reg value => (⟨column,
    (List.range 6).map (fun b => if reg.testBit b then 1 else 0),value⟩ : ColumnClaim)
  claim 17 (E.ofK 93) :: List.ofFn (fun i : Fin 4 => claim (10+i.val) (E.ofK (output i)))

def readAnnouncements : List Nat → CallerParser Unit
  | [] => pure ()
  | height :: rest => do
    let sent ← readScalar
    check (sent == E.ofK (UInt64.ofNat height))
    readAnnouncements rest

/-- The CPU announcement, clock and commitment are read before bus grinding or
any caller challenge. Shared by the early physical-root and full-token parsers. -/
def cpuRoot (layout : CpuLayout) : CallerParser Digest32 := do
  check (layout.tables.length == 11)
  -- `Announcement::read`: dimensions and rate are fixed public family data.
  readAnnouncements (layout.tables.map CpuTableLayout.tau ++ [layout.logInvRate])
  let clock ← readScalar
  check (clock.c1 == 0 && clock.c2 == 0 && clock.c0.toNat / 2^40 == 1 && clock.c0.toNat % 32 == 0)
  readRoot

@[inline] def cpuPayload (layout : CpuLayout) :
    CallerParser (List RingPCSGame.FamilyClaim × Array RingPCSGame.PointClaim) := do
  let (point,bus) ← busClaims layout.bus
  let settled ← settledClaims layout.tables point
  let _ ← drawScalar
  let producerAirs := layout.bus.producers.map (fun p => (⟨p.kappa,2*p.bits,p.bits,[]⟩ : AirLayout))
  let summed ← constraintClaims (layout.tables.map CpuTableLayout.air ++ producerAirs) point
  -- `TableClaims::new`: settled tables form the initial table segment.
  check (layout.tables.take settled.length |>.all (·.settled))
  check (layout.tables.drop settled.length |>.all (! ·.settled))
  let columns := settled ++ (summed.take layout.tables.length).drop settled.length
  let packed ← flockClaims layout.flock
  let producers := summed.drop layout.tables.length
  let mut rings := packed
  for (p,c) in layout.bus.producers.zip producers do
    match paddedRing p.window c.point c.evals with
    | some ring => rings := rings ++ [ring]
    | none => check false
  for word in layout.registers do
    let some first := word.tables.head? | return ← (fun _ => none)
    let some firstClaims := summed[first]? | return ← (fun _ => none)
    let mut slices := []
    for t in word.tables do
      let some claims := summed[t]? | return ← (fun _ => none)
      slices := slices ++ claims.slices
    match paddedRing word.offset firstClaims.point slices with
    | some ring => rings := rings ++ [ring]
    | none => check false
  let columnClaims := bus ++ ((layout.tables.map CpuTableLayout.base).zip columns).flatMap
    (fun (base,claims) => tableColumns base claims) ++ exitClaims layout.finalRegisterColumn layout.output
  match placeClaims layout.placements columnClaims with
  | some points => pure (rings,points)
  | none => fun _ => none

def cpuClaims (layout : CpuLayout) : CallerParser CallerClaims := do
  let root ← cpuRoot layout
  let (rings,points) ← cpuPayload layout
  pure ⟨root,rings,points⟩

inductive CallerLayout where
  | cpu (layout : CpuLayout)
  | recursion (layout : RecLayout)

def callerRoot : CallerLayout → CallerParser Digest32
  | .cpu layout => cpuRoot layout
  | .recursion _ => readRoot

def rootScalarCount : CallerLayout → Nat
  | .cpu _ => 15
  | .recursion _ => 2

/-- The actual pre-challenge commitment, solely from the initial absorb-zero
frame. CPU contributes twelve public heights/rate scalars, clock and two root
scalars; recursion contributes only the two root scalars. No sampled output,
PoW result, future claim registration or fresh transcript is consulted. -/
def initialRoot (layout : CallerLayout) (entry : FramedHistory) : Option Digest32 := do
  match entry.frames with
  | .absorb 0 bytes :: _ =>
    let values ← WHIRHistory.parseExact (rootScalarCount layout) bytes
    let (root,rest) ← callerRoot layout (values.map CallerToken.sent)
    if rest.isEmpty then some root else none
  | _ => none

def callerPlacements : CallerLayout → Array Placement
  | .cpu l => l.placements
  | .recursion l => l.placements

def callerWords (layout : CallerLayout) : Nat :=
  (callerPlacements layout).foldl (fun n p => match p with
    | .committed _ dimension => n + 2^dimension
    | _ => n) 0

/-- Exact `witness::placements_of` rounding, including the production floor. -/
def callerMu (layout : CallerLayout) : Nat :=
  let words := callerWords layout
  max 15 (Nat.log2 (max words 1 - 1) + if words ≤ 1 then 0 else 1)

def callerLanes (layout : CallerLayout) : Nat :=
  let laneWords := 2^(callerMu layout - 6)
  max 1 ((callerWords layout + laneWords - 1) / laneWords)

def callerRate : CallerLayout → Nat
  | .cpu l => l.logInvRate
  | .recursion l => l.logInvRate

def callerProfile (layout : CallerLayout) : Option Profile :=
  if hm : 15 ≤ callerMu layout ∧ callerMu layout ≤ 28 then
    if hr : 1 ≤ callerRate layout ∧ callerRate layout ≤ 4 then
      some (⟨callerMu layout-15,by omega⟩,⟨callerRate layout-1,by omega⟩)
    else none
  else none

def openingMatches (profile : Profile) (lanes : Nat) (layout : CallerLayout) : Bool :=
  lanes == callerLanes layout && profile.1.val+15 == callerMu layout &&
    profile.2.val+1 == callerRate layout

theorem callerProfile_matches (layout : CallerLayout) (profile : Profile)
    (ok : callerProfile layout = some profile) :
    openingMatches profile (callerLanes layout) layout = true := by
  unfold callerProfile at ok
  split at ok
  next hm =>
    split at ok
    next hr =>
      have hp := Option.some.inj ok
      subst profile
      simp [openingMatches, Nat.sub_add_cancel hm.1, Nat.sub_add_cancel hr.1]
    next => simp at ok
  next => simp at ok

def sourceClaims : CallerLayout → CallerParser CallerClaims
  | .cpu layout => cpuClaims layout
  | .recursion layout => recClaims layout

private def reads (n : Nat) : List WHIRCallerShape.EventShape :=
  List.replicate n (.absorb 24)

private def draws (n : Nat) : List WHIRCallerShape.EventShape :=
  List.replicate n (.squeeze 24)

def gkrShape (mu : Nat) : List WHIRCallerShape.EventShape :=
  reads 1 ++ draws 1 ++ (if mu % 2 = 1 then reads 4 ++ draws 2 else []) ++
    (List.range (mu/2)).flatMap (fun i =>
      (List.replicate (mu%2+2*i) (reads 4 ++ draws 1)).flatten ++ reads 8 ++ draws 3)

def frameworkKeys (layout : BusLayout) : List (Nat × Nat) :=
  ((layout.push ++ layout.pull).flatMap (fun block =>
    if block.tableOwned then [] else block.coords.filterMap (fun coord =>
      match coord with
      | .column col => some (col,block.kappa)
      | _ => none))).eraseDups

def busShape (layout : BusLayout) : List WHIRCallerShape.EventShape :=
  (if layout.grinding > 0 then [.nonce layout.grinding] else []) ++ draws 5 ++
    gkrShape layout.mu ++ reads (frameworkKeys layout).length

def constraintsShape (layouts : List AirLayout) : List WHIRCallerShape.EventShape :=
  (List.replicate ((layouts.map AirLayout.tau).foldl max 0) (reads 3 ++ draws 1)).flatten ++
    layouts.flatMap (fun l => reads (l.columns-l.publicColumns-l.fields.length) ++
      reads ((l.fields.map BitField.width).sum))

def flockProgramShape (layouts : List FlockLayout) : List WHIRCallerShape.EventShape :=
  let m := (layouts.map FlockLayout.logN).foldl max 0
  let rounds := (layouts.map (fun l => l.kLog-6)).foldl max 0
  draws (m-13+1) ++ reads 64 ++ draws 1 ++
    (List.replicate (m-6) (reads 2 ++ draws 1)).flatten ++
    reads (3*layouts.length) ++ draws 1 ++
    (List.replicate rounds (reads 2 ++ draws 1)).flatten ++
    layouts.flatMap (fun _ => reads 64 ++ reads 1)

/-- The actual public CPU/recursion source program's scalar-level operation
shape, not a configurable instruction tape. Adjacent reads remain coalescible
by the checked `WHIRCallerShape` framing model. -/
def callerShape : CallerLayout → List WHIRCallerShape.EventShape
  | .recursion l => reads 2 ++ busShape l.bus ++ draws 1 ++
      constraintsShape (l.tables.map Prod.snd) ++ flockProgramShape [l.hash]
  | .cpu l =>
      let airs := l.tables.map CpuTableLayout.air ++
        l.bus.producers.map (fun p => ⟨p.kappa,2*p.bits,p.bits,[]⟩)
      reads (l.tables.length+2) ++ reads 2 ++ busShape l.bus ++
        l.tables.flatMap (fun t => if t.settled then reads (t.committedColumns-t.summedColumns.length) else []) ++
        draws 1 ++ constraintsShape airs ++ flockProgramShape l.flock

def tokensShape (tokens : List CallerToken) : List WHIRCallerShape.EventShape :=
  tokens.map (WHIRCallerShape.operationShape ∘ tokenOperation)

def callerEntryLength (layout : CallerLayout) : Nat :=
  WHIRCallerShape.entryCount (callerShape layout)

def callerOutputCap (layout : CallerLayout) : Nat :=
  WHIRCallerShape.callerOutputCap (callerShape layout)

/-- Exact source parser, finishing at the stack entry rather than accepting a
prefix and discarding extra caller events. -/
def interpretCaller (layout : CallerLayout) (tokens : List CallerToken) : Option CallerClaims := do
  if tokensShape tokens ≠ callerShape layout then none else do
    let (claims,rest) ← sourceClaims layout tokens
    if rest.isEmpty then some claims else none

theorem interpretCaller_shape (layout : CallerLayout) (tokens : List CallerToken)
    (claims : CallerClaims) (ok : interpretCaller layout tokens = some claims) :
    tokensShape tokens = callerShape layout := by
  unfold interpretCaller at ok
  by_contra h
  simp [h] at ok

def decodeCaller (layout : CallerLayout) (entry : FramedHistory)
    (answers : Coordinate → Digest32) : Option CallerClaims := do
  let tokens ← entryTokens entry answers
  interpretCaller layout tokens

/-- Concrete source caller interpreter, including its actual preceding physical
streams. No cache resolver or decoder is a parameter of this definition. -/
def interpretPhysicalCaller (c : Compression) (iv : Digest32) (layout : CallerLayout)
    (entry : FramedHistory) : Option CallerClaims := do
  let tokens ← sourceTokens c iv entry
  interpretCaller layout tokens

theorem decodeCaller_physical_source (c : Compression) (iv : Digest32)
    (layout : CallerLayout) (entry : FramedHistory) (answers : Coordinate → Digest32)
    (observed : ∀ q ∈ callerOutputs entry, answers q = evalCoordinate c iv q) :
    decodeCaller layout entry answers = interpretPhysicalCaller c iv layout entry := by
  simp only [decodeCaller, interpretPhysicalCaller, entryTokens_source c iv entry answers observed]

theorem decodeCaller_prior_only (layout : CallerLayout) (entry : FramedHistory)
    (a b : Coordinate → Digest32)
    (agree : ∀ q ∈ callerOutputs entry, a q = b q) :
    decodeCaller layout entry a = decodeCaller layout entry b := by
  simp only [decodeCaller, entryTokens_prior_only entry a b agree]

/-- The decoder returns exactly the concrete source interpreter's claims when
its accepted parse reaches this stack entry. No claim-decoder argument occurs. -/
theorem decodeCaller_source (layout : CallerLayout) (entry : FramedHistory)
    (answers : Coordinate → Digest32) (tokens : List CallerToken) (claims : CallerClaims)
    (trace : entryTokens entry answers = some tokens)
    (accepted : interpretCaller layout tokens = some claims) :
    decodeCaller layout entry answers = some claims := by
  simp [decodeCaller, trace, accepted]

theorem decodeCaller_public_shape (layout : CallerLayout) (entry : FramedHistory)
    (answers : Coordinate → Digest32) (claims : CallerClaims)
    (ok : decodeCaller layout entry answers = some claims) :
    entry.frames.length = WHIRCallerShape.entryCount (callerShape layout) ∧
      callerOutputCount entry.frames = WHIRCallerShape.callerOutputCap (callerShape layout) := by
  cases ht : entryTokens entry answers with
  | none => simp [decodeCaller, ht] at ok
  | some tokens =>
    have accepted : interpretCaller layout tokens = some claims := by
      simpa [decodeCaller, ht] using ok
    have hh := entryTokens_history entry answers tokens ht
    have hs := interpretCaller_shape layout tokens claims accepted
    have hc := WHIRCallerShape.normalized_entry_count entry.domain entry.statement
      (tokens.map tokenOperation)
    have ho := WHIRCallerShape.normalized_callerOutputCount entry.domain entry.statement
      (tokens.map tokenOperation)
    change (tokenHistory entry.domain entry.statement tokens).frames.length = _ at hc
    change callerOutputCount (tokenHistory entry.domain entry.statement tokens).frames = _ at ho
    unfold tokensShape at hs
    simp only [List.map_map, hh, hs] at hc ho
    exact ⟨hc,ho⟩

/-- Commitment metadata is public; original claims are produced by the caller
interpreter above. Oversized claim families reject instead of being truncated. -/
def decodeRequest (cap : Nat) (profile : Profile) (lanes : Nat)
    (layout : CallerLayout) (entry : FramedHistory) (answers : Coordinate → Digest32) :
    Option (CausalBindingState.ClaimRequest cap profile) := do
  if !openingMatches profile lanes layout then none else do
    let claims ← decodeCaller layout entry answers
    if hl : lanes ≤ 2 ^ (config profile).folds[0]! then
      if hf : claims.families.length ≤ cap then
        if hp : claims.points.size + 1 ≤ 2^64 then
          some ⟨claims.root,lanes,hl,
            ⟨claims.families.length,fun i => claims.families[i],hf,claims.points,hp⟩⟩
        else none
      else none
    else none

theorem decodeRequest_prior_only (cap : Nat) (profile : Profile) (lanes : Nat)
    (layout : CallerLayout) (entry : FramedHistory) (a b : Coordinate → Digest32)
    (agree : ∀ q ∈ callerOutputs entry, a q = b q) :
    decodeRequest cap profile lanes layout entry a = decodeRequest cap profile lanes layout entry b := by
  simp only [decodeRequest, decodeCaller_prior_only layout entry a b agree]

theorem decodeRequest_actual_outputs (cap : Nat) (profile : Profile) (lanes : Nat)
    (layout : CallerLayout) (entry : FramedHistory) (answers : Coordinate → Digest32)
    (c : Compression) (iv : Digest32)
    (observed : ∀ q ∈ callerOutputs entry, answers q = evalCoordinate c iv q) :
    decodeRequest cap profile lanes layout entry answers =
      decodeRequest cap profile lanes layout entry (evalCoordinate c iv) :=
  decodeRequest_prior_only cap profile lanes layout entry answers (evalCoordinate c iv) observed

theorem decodeRequest_future_irrelevant (cap : Nat) (profile : Profile) (lanes : Nat)
    (layout : CallerLayout) (entry : FramedHistory) (a b : Coordinate → Digest32)
    (agree : ∀ q, q.history.domain = entry.domain → q.history.statement = entry.statement →
      q.history.frames.length < entry.frames.length →
      q.history.frames = entry.frames.take q.history.frames.length → a q = b q) :
    decodeRequest cap profile lanes layout entry a = decodeRequest cap profile lanes layout entry b := by
  apply decodeRequest_prior_only
  intro q h
  obtain ⟨hd,hs,hlen,hpre⟩ := callerOutputs_strict_prefix entry q h
  exact agree q hd hs hlen hpre

theorem decodeRequest_source (cap : Nat) (profile : Profile) (lanes : Nat)
    (layout : CallerLayout) (entry : FramedHistory) (answers : Coordinate → Digest32)
    (tokens : List CallerToken) (claims : CallerClaims)
    (trace : entryTokens entry answers = some tokens)
    (accepted : interpretCaller layout tokens = some claims)
    (metadata : openingMatches profile lanes layout = true)
    (hl : lanes ≤ 2 ^ (config profile).folds[0]!)
    (hf : claims.families.length ≤ cap) (hp : claims.points.size + 1 ≤ 2^64) :
    decodeRequest cap profile lanes layout entry answers =
      some ⟨claims.root,lanes,hl,
        ⟨claims.families.length,fun i => claims.families[i],hf,claims.points,hp⟩⟩ := by
  simp [decodeRequest, metadata,
    decodeCaller_source layout entry answers tokens claims trace accepted, hl, hf]
  omega

/-- Physical source agreement, without assuming a decoder equation for its
trace or announcing any claims to the decoder. -/
theorem decodeRequest_physical_source (cap : Nat) (profile : Profile) (lanes : Nat)
    (c : Compression) (iv : Digest32) (layout : CallerLayout) (entry : FramedHistory)
    (answers : Coordinate → Digest32)
    (observed : ∀ q ∈ callerOutputs entry, answers q = evalCoordinate c iv q)
    (claims : CallerClaims) (accepted : interpretPhysicalCaller c iv layout entry = some claims)
    (metadata : openingMatches profile lanes layout = true)
    (hl : lanes ≤ 2 ^ (config profile).folds[0]!)
    (hf : claims.families.length ≤ cap) (hp : claims.points.size + 1 ≤ 2^64) :
    decodeRequest cap profile lanes layout entry answers =
      some ⟨claims.root,lanes,hl,
        ⟨claims.families.length,fun i => claims.families[i],hf,claims.points,hp⟩⟩ := by
  simp [decodeRequest, decodeCaller_physical_source c iv layout entry answers observed,
    accepted, metadata, hl, hf]
  omega

def identifiedRequest (cap : Nat) (profile : Profile) (lanes : Nat)
    (layout : CallerLayout) (entry : FramedHistory) (answers : Coordinate → Digest32) :
    Option (FramedHistory × CausalBindingState.ClaimRequest cap profile) :=
  (decodeRequest cap profile lanes layout entry answers).map (entry,·)

theorem identifiedRequest_entry (cap : Nat) (profile : Profile) (lanes : Nat)
    (layout : CallerLayout) (entry other : FramedHistory) (answers : Coordinate → Digest32)
    (request : CausalBindingState.ClaimRequest cap profile)
    (ok : identifiedRequest cap profile lanes layout entry answers = some (other,request)) :
    entry = other := by
  unfold identifiedRequest at ok
  cases h : decodeRequest cap profile lanes layout entry answers <;> simp [h] at ok
  exact ok.1

theorem decodeRequest_public_shape (cap : Nat) (profile : Profile) (lanes : Nat)
    (layout : CallerLayout) (entry : FramedHistory) (answers : Coordinate → Digest32)
    (request : CausalBindingState.ClaimRequest cap profile)
    (ok : decodeRequest cap profile lanes layout entry answers = some request) :
    entry.frames.length = callerEntryLength layout ∧
      callerOutputCount entry.frames = callerOutputCap layout := by
  cases hc : decodeCaller layout entry answers with
  | none => simp [decodeRequest, hc] at ok
  | some claims => exact decodeCaller_public_shape layout entry answers claims hc

theorem decodeRequest_wrong_metadata (cap : Nat) (profile : Profile) (lanes : Nat)
    (layout : CallerLayout) (entry : FramedHistory) (answers : Coordinate → Digest32)
    (wrong : openingMatches profile lanes layout = false) :
    decodeRequest cap profile lanes layout entry answers = none := by
  simp [decodeRequest, wrong]

/-- Raw dependency histories can be incomplete. Such an entry rejects before
any fallback bytes are used. The total-answer endpoint above is for a cache
whose preceding caller outputs have already been proved complete. -/
def decodeAvailableRequest (cap : Nat) (profile : Profile) (lanes : Nat)
    (layout : CallerLayout) (entry : FramedHistory) (answers : Coordinate → Option Digest32) :
    Option (CausalBindingState.ClaimRequest cap profile) :=
  if (callerOutputs entry).all (fun q => (answers q).isSome) then
    decodeRequest cap profile lanes layout entry (fun q => (answers q).getD zeroDigest)
  else none

theorem decodeAvailableRequest_missing (cap : Nat) (profile : Profile) (lanes : Nat)
    (layout : CallerLayout) (entry : FramedHistory) (answers : Coordinate → Option Digest32)
    (q : Coordinate) (prior : q ∈ callerOutputs entry) (missing : answers q = none) :
    decodeAvailableRequest cap profile lanes layout entry answers = none := by
  cases h : (callerOutputs entry).all (fun q => (answers q).isSome) with
  | false => simp [decodeAvailableRequest, h]
  | true =>
    have hq := List.all_eq_true.mp h q prior
    simp [missing] at hq

theorem decodeAvailableRequest_malformed (cap : Nat) (profile : Profile) (lanes : Nat)
    (layout : CallerLayout) (entry : FramedHistory) (answers : Coordinate → Option Digest32)
    (malformed : entryTokens entry (fun q => (answers q).getD zeroDigest) = none) :
    decodeAvailableRequest cap profile lanes layout entry answers = none := by
  simp [decodeAvailableRequest, decodeRequest, decodeCaller, malformed]

theorem decodeAvailableRequest_prior_only (cap : Nat) (profile : Profile) (lanes : Nat)
    (layout : CallerLayout) (entry : FramedHistory) (a b : Coordinate → Option Digest32)
    (agree : ∀ q ∈ callerOutputs entry, a q = b q) :
    decodeAvailableRequest cap profile lanes layout entry a =
      decodeAvailableRequest cap profile lanes layout entry b := by
  have complete : (callerOutputs entry).all (fun q => (a q).isSome) =
      (callerOutputs entry).all (fun q => (b q).isSome) := by
    apply Bool.eq_iff_iff.mpr
    simp only [List.all_eq_true]
    constructor
    · intro h q hq
      rw [← agree q hq]
      exact h q hq
    · intro h q hq
      rw [agree q hq]
      exact h q hq
  have values := decodeRequest_prior_only cap profile lanes layout entry
    (fun q => (a q).getD zeroDigest) (fun q => (b q).getD zeroDigest)
    (fun q hq => congrArg (fun o => o.getD zeroDigest) (agree q hq))
  simp only [decodeAvailableRequest, complete, values]

theorem decodeAvailableRequest_physical_source (cap : Nat) (profile : Profile) (lanes : Nat)
    (c : Compression) (iv : Digest32) (layout : CallerLayout) (entry : FramedHistory)
    (answers : Coordinate → Option Digest32)
    (observed : ∀ q ∈ callerOutputs entry, answers q = some (evalCoordinate c iv q))
    (claims : CallerClaims) (accepted : interpretPhysicalCaller c iv layout entry = some claims)
    (metadata : openingMatches profile lanes layout = true)
    (hl : lanes ≤ 2 ^ (config profile).folds[0]!)
    (hf : claims.families.length ≤ cap) (hp : claims.points.size + 1 ≤ 2^64) :
    decodeAvailableRequest cap profile lanes layout entry answers =
      some ⟨claims.root,lanes,hl,
        ⟨claims.families.length,fun i => claims.families[i],hf,claims.points,hp⟩⟩ := by
  have available : (callerOutputs entry).all (fun q => (answers q).isSome) = true :=
    List.all_eq_true.mpr (fun q hq => by rw [observed q hq]; rfl)
  simp only [decodeAvailableRequest, available, ↓reduceIte]
  exact decodeRequest_physical_source cap profile lanes c iv layout entry
    (fun q => (answers q).getD zeroDigest)
    (fun q hq => by rw [observed q hq]; rfl) claims accepted metadata hl hf hp

theorem decodeAvailableRequest_public_shape (cap : Nat) (profile : Profile) (lanes : Nat)
    (layout : CallerLayout) (entry : FramedHistory) (answers : Coordinate → Option Digest32)
    (request : CausalBindingState.ClaimRequest cap profile)
    (ok : decodeAvailableRequest cap profile lanes layout entry answers = some request) :
    entry.frames.length = callerEntryLength layout ∧
      callerOutputCount entry.frames = callerOutputCap layout := by
  unfold decodeAvailableRequest at ok
  split at ok
  next =>
    exact decodeRequest_public_shape cap profile lanes layout entry
      (fun q => (answers q).getD zeroDigest) request ok
  next => simp at ok


set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

theorem parser_bind_apply {α β : Type} (p : CallerParser α) (f : α → CallerParser β)
    (tokens : List CallerToken) :
    (p >>= f) tokens = (p tokens).bind (fun x => f x.1 x.2) := rfl

theorem parser_bind_inv {α β : Type} (p : CallerParser α) (f : α → CallerParser β)
    (tokens rest : List CallerToken) (value : β)
    (accepted : (do let x ← p; f x) tokens = some (value,rest)) :
    ∃ x middle, p tokens = some (x,middle) ∧ f x middle = some (value,rest) := by
  change (p tokens).bind (fun x => f x.1 x.2) = some (value,rest) at accepted
  obtain ⟨pair,first,last⟩ := Option.bind_eq_some_iff.mp accepted
  exact ⟨pair.1,pair.2,first,last⟩

/-- A successful scalar-only parser consumes a fixed number of sent scalars
and can replay that exact prefix before any arbitrary continuation. -/
def SentPrefix {α : Type} (n : Nat) (parser : CallerParser α) : Prop :=
  ∀ tokens value rest, parser tokens = some (value,rest) →
    ∃ values : List E, values.length = n ∧ tokens = values.map CallerToken.sent ++ rest ∧
      ∀ tail, parser (values.map CallerToken.sent ++ tail) = some (value,tail)

theorem sentPrefix_pure {α : Type} (value : α) : SentPrefix 0 (pure value) := by
  intro tokens result rest accepted
  change some (value,tokens) = some (result,rest) at accepted
  cases Option.some.inj accepted
  exact ⟨[],rfl,rfl,fun _ => rfl⟩

theorem sentPrefix_fail {α : Type} (n : Nat) : SentPrefix n (fun _ => (none : Option (α × List CallerToken))) := by
  intro tokens value rest accepted
  cases accepted

theorem sentPrefix_bind {α β : Type} (n m : Nat) (p : CallerParser α) (f : α → CallerParser β)
    (first : SentPrefix n p) (last : ∀ x, SentPrefix m (f x)) :
    SentPrefix (n+m) (do let x ← p; f x) := by
  intro tokens result rest accepted
  obtain ⟨value,middle,hp,hf⟩ := parser_bind_inv p f tokens rest result accepted
  obtain ⟨left,hlen,heq,hreplay⟩ := first tokens value middle hp
  obtain ⟨right,rlen,req,rreplay⟩ := last value middle result rest hf
  refine ⟨left ++ right,by simp [hlen,rlen],?_,?_⟩
  · simp only [List.map_append,List.append_assoc,← req,← heq]
  · intro tail
    change (p ((left ++ right).map CallerToken.sent ++ tail)).bind (fun x => f x.1 x.2) = _
    rw [List.map_append,List.append_assoc,hreplay]
    exact rreplay tail

theorem sentPrefix_readScalar : SentPrefix 1 readScalar := by
  intro tokens value rest accepted
  cases tokens with
  | nil => simp [readScalar] at accepted
  | cons token tail =>
    cases token with
    | sent x =>
      simp only [readScalar,Option.some.injEq,Prod.mk.injEq] at accepted
      obtain ⟨equal,remaining⟩ := accepted
      exact ⟨[value],rfl,by simp [equal,remaining],fun _ => rfl⟩
    | draw => simp [readScalar] at accepted
    | nonce => simp [readScalar] at accepted

theorem sentPrefix_check (ok : Bool) : SentPrefix 0 (check ok) := by
  cases ok
  · exact sentPrefix_fail 0
  · exact sentPrefix_pure ()

theorem sentPrefix_readRoot : SentPrefix 2 readRoot := by
  unfold readRoot
  apply sentPrefix_bind 1 1 _ _ sentPrefix_readScalar
  intro a
  apply sentPrefix_bind 1 0 _ _ sentPrefix_readScalar
  intro b
  cases ByteCodec.scalarsToHash (a,b) with
  | none => exact sentPrefix_fail 0
  | some root => exact sentPrefix_pure root

theorem sentPrefix_announcements (heights : List Nat) : SentPrefix heights.length (readAnnouncements heights) := by
  induction heights with
  | nil => exact sentPrefix_pure ()
  | cons height rest ih =>
    have after (value : E) : SentPrefix rest.length (do
        check (value == E.ofK (UInt64.ofNat height))
        readAnnouncements rest) := by
      simpa only [Nat.zero_add] using
        sentPrefix_bind 0 rest.length (check (value == E.ofK (UInt64.ofNat height))) _
          (sentPrefix_check _) (fun _ => ih)
    simpa only [readAnnouncements,List.length_cons,Nat.add_comm] using
      sentPrefix_bind 1 rest.length readScalar _ sentPrefix_readScalar after

theorem readAnnouncements_loop (heights : List Nat) : readAnnouncements heights =
    (do for height in heights do
      let sent ← readScalar
      check (sent == E.ofK (UInt64.ofNat height)) : CallerParser Unit) := by
  induction heights with
  | nil => simp [readAnnouncements]
  | cons height rest ih =>
    simp only [readAnnouncements,List.forIn_cons,bind_assoc,pure_bind,ih]

theorem sentPrefix_cpuRoot (layout : CpuLayout) :
    SentPrefix (layout.tables.length+4) (cpuRoot layout) := by
  have afterClock (clock : E) : SentPrefix 2
      (do
        check (clock.c1 == 0 && clock.c2 == 0 && clock.c0.toNat / 2^40 == 1 && clock.c0.toNat % 32 == 0)
        readRoot) := by
    exact sentPrefix_bind 0 2 _ _ (sentPrefix_check _) (fun _ => sentPrefix_readRoot)
  have clockRoot : SentPrefix 3 (do
      let clock ← readScalar
      check (clock.c1 == 0 && clock.c2 == 0 && clock.c0.toNat / 2^40 == 1 && clock.c0.toNat % 32 == 0)
      readRoot) :=
    sentPrefix_bind 1 2 _ _ sentPrefix_readScalar afterClock
  have announced := sentPrefix_bind
    (layout.tables.map CpuTableLayout.tau ++ [layout.logInvRate]).length 3
    (readAnnouncements (layout.tables.map CpuTableLayout.tau ++ [layout.logInvRate]))
    (fun _ => do
      let clock ← readScalar
      check (clock.c1 == 0 && clock.c2 == 0 && clock.c0.toNat / 2^40 == 1 && clock.c0.toNat % 32 == 0)
      readRoot) (sentPrefix_announcements _) (fun _ => clockRoot)
  have result := sentPrefix_bind 0 _ (check (layout.tables.length == 11)) _
    (sentPrefix_check _) (fun _ => announced)
  simpa only [cpuRoot,List.length_append,List.length_map,List.length_cons,List.length_nil,
    Nat.zero_add,Nat.add_assoc] using result

theorem cpuRoot_tables (layout : CpuLayout) (tokens rest : List CallerToken) (root : Digest32)
    (accepted : cpuRoot layout tokens = some (root,rest)) : layout.tables.length = 11 := by
  by_contra different
  simp [cpuRoot,parser_bind_apply,check,different] at accepted

theorem busClaims_sent (layout : BusLayout) (value : E) (rest : List CallerToken) :
    busClaims layout (.sent value :: rest) = none := by
  by_cases grinding : 0 < layout.grinding <;>
    simp [busClaims,grinding,parser_bind_apply,nonce,drawScalars,drawScalar]

theorem recPayload_sent (layout : RecLayout) (value : E) (rest : List CallerToken) :
    recPayload layout (.sent value :: rest) = none := by
  change (busClaims layout.bus (.sent value :: rest)).bind _ = none
  rw [busClaims_sent]
  rfl

theorem cpuPayload_sent (layout : CpuLayout) (value : E) (rest : List CallerToken) :
    cpuPayload layout (.sent value :: rest) = none := by
  change (busClaims layout.bus (.sent value :: rest)).bind _ = none
  rw [busClaims_sent]
  rfl

theorem rootedParser_prefix (n : Nat) (header : CallerParser Digest32)
    (payload : CallerParser (List RingPCSGame.FamilyClaim × Array RingPCSGame.PointClaim))
    (scalarOnly : SentPrefix n header)
    (delimiter : ∀ value rest, payload (.sent value :: rest) = none)
    (tokens rest : List CallerToken) (claims : CallerClaims)
    (accepted : (do
      let root ← header
      let (rings,points) ← payload
      pure (⟨root,rings,points⟩ : CallerClaims)) tokens = some (claims,rest)) :
    ∃ (values : List E) (tail : List CallerToken),
      values.length = n ∧ tokens = values.map CallerToken.sent ++ tail ∧
      header (values.map CallerToken.sent) = some (claims.root,[]) ∧
      ∀ value rest, tail ≠ .sent value :: rest := by
  obtain ⟨root,middle,head,body⟩ := parser_bind_inv _ _ _ _ _ accepted
  obtain ⟨pair,remaining,parsed,finished⟩ := parser_bind_inv _ _ _ _ _ body
  change some (⟨root,pair.1,pair.2⟩,remaining) = some (claims,rest) at finished
  cases Option.some.inj finished
  obtain ⟨values,count,hpref,replay⟩ := scalarOnly _ _ _ head
  refine ⟨values,middle,count,hpref,?_,?_⟩
  · simpa only [List.append_nil] using replay []
  · intro value rest same
    rw [same,delimiter] at parsed
    cases parsed

theorem sourceClaims_initialPrefix (layout : CallerLayout) (tokens rest : List CallerToken)
    (claims : CallerClaims) (accepted : sourceClaims layout tokens = some (claims,rest)) :
    ∃ (values : List E) (tail : List CallerToken), values.length = rootScalarCount layout ∧
      tokens = values.map CallerToken.sent ++ tail ∧
      callerRoot layout (values.map CallerToken.sent) = some (claims.root,[]) ∧
      ∀ value rest, tail ≠ .sent value :: rest := by
  cases layout with
  | cpu layout =>
    obtain ⟨values,tail,count,hpref,header,delimiter⟩ :=
      rootedParser_prefix _ (cpuRoot layout) (cpuPayload layout)
        (sentPrefix_cpuRoot layout) (cpuPayload_sent layout) tokens rest claims accepted
    have eleven := cpuRoot_tables layout _ _ _ header
    exact ⟨values,tail,by simpa only [rootScalarCount,eleven] using count,hpref,header,delimiter⟩
  | recursion layout =>
    exact rootedParser_prefix 2 readRoot (recPayload layout) sentPrefix_readRoot
      (recPayload_sent layout) tokens rest claims accepted

theorem modelAbsorb_concat (model : Model) (left right : List Byte) :
    modelAbsorb (modelAbsorb model left) right = modelAbsorb model (left ++ right) := by
  by_cases hl : left = []
  · simp [hl,modelAbsorb]
  · by_cases hr : right = []
    · simp [hr,modelAbsorb]
    · simp [modelAbsorb,hl,hr,List.append_assoc]

theorem run_sent_tokens (model : Model) (values : List E) :
    WHIRCallerShape.runOperations model ((values.map CallerToken.sent).map tokenOperation) =
      modelAbsorb model (WHIRHistory.scalarBytes values) := by
  induction values generalizing model with
  | nil => simp [WHIRCallerShape.runOperations,WHIRHistory.scalarBytes,modelAbsorb]
  | cons value rest ih =>
    simp only [List.map_cons,WHIRCallerShape.runOperations,List.foldl_cons,
      tokenOperation,WHIRCallerShape.applyOperation]
    change WHIRCallerShape.runOperations (modelAbsorb model (WHIRHistory.scalarBytes [value]))
      ((rest.map CallerToken.sent).map tokenOperation) = _
    rw [ih,modelAbsorb_concat]
    rfl

theorem runOperations_prepend (frames : List Frame) (model : Model)
    (operations : List WHIRCallerShape.Operation) :
    WHIRCallerShape.runOperations (WHIRCallerPrefix.prepend frames model) operations =
      WHIRCallerPrefix.prepend frames (WHIRCallerShape.runOperations model operations) := by
  induction operations generalizing model with
  | nil => rfl
  | cons operation rest ih =>
    cases operation <;>
      simp only [WHIRCallerShape.runOperations,List.foldl_cons,WHIRCallerShape.applyOperation,
        WHIRCallerPrefix.prepend_modelAbsorb,WHIRCallerPrefix.prepend_modelSqueeze,
        WHIRCallerPrefix.prepend_modelNonce] <;> exact ih _

theorem runOperations_append (model : Model) (left right : List WHIRCallerShape.Operation) :
    WHIRCallerShape.runOperations model (left ++ right) =
      WHIRCallerShape.runOperations (WHIRCallerShape.runOperations model left) right := by
  simp only [WHIRCallerShape.runOperations,List.foldl_append]

theorem tokenHistory_initialFrame (domain statement : Digest32) (values : List E)
    (tail : List CallerToken) (nonempty : values ≠ [])
    (delimiter : ∀ value rest, tail ≠ .sent value :: rest) :
    (tokenHistory domain statement (values.map CallerToken.sent ++ tail)).frames.head? =
      some (.absorb 0 (WHIRHistory.scalarBytes values)) := by
  have bytes : WHIRHistory.scalarBytes values ≠ [] := fun empty =>
    nonempty ((WHIRHistory.scalarBytes_empty _).mp empty)
  unfold tokenHistory
  rw [List.map_append,runOperations_append,run_sent_tokens]
  cases tail with
  | nil => simp [WHIRCallerShape.runOperations,WHIRCallerShape.seedModel,modelAbsorb,closeRun,bytes]
  | cons token rest =>
    cases token with
    | sent value => exact False.elim (delimiter value rest rfl)
    | draw value =>
      have first :
          modelSqueeze (modelAbsorb (WHIRCallerShape.seedModel domain statement)
            (WHIRHistory.scalarBytes values)) 24 =
          WHIRCallerPrefix.prepend [.absorb 0 (WHIRHistory.scalarBytes values)]
            (⟨⟨domain,statement,[]⟩,[],0,24⟩ : Model) := by
        simp [WHIRCallerShape.seedModel,modelAbsorb,modelSqueeze,closeRun,bytes,WHIRCallerPrefix.prepend]
      change (closeRun (WHIRCallerShape.runOperations
        (modelSqueeze (modelAbsorb (WHIRCallerShape.seedModel domain statement)
          (WHIRHistory.scalarBytes values)) 24) (rest.map tokenOperation))).history.frames.head? = _
      rw [first,runOperations_prepend,WHIRCallerPrefix.prepend_closeRun]
      rfl
    | nonce bits value =>
      have first :
          modelNonce (modelAbsorb (WHIRCallerShape.seedModel domain statement)
            (WHIRHistory.scalarBytes values)) value bits =
          WHIRCallerPrefix.prepend [.absorb 0 (WHIRHistory.scalarBytes values)]
            (⟨⟨domain,statement,[.nonce 0 bits value]⟩,[],0,0⟩ : Model) := by
        simp [WHIRCallerShape.seedModel,modelAbsorb,modelNonce,closeRun,bytes,WHIRCallerPrefix.prepend]
      change (closeRun (WHIRCallerShape.runOperations
        (modelNonce (modelAbsorb (WHIRCallerShape.seedModel domain statement)
          (WHIRHistory.scalarBytes values)) value bits) (rest.map tokenOperation))).history.frames.head? = _
      rw [first,runOperations_prepend,WHIRCallerPrefix.prepend_closeRun]
      rfl

theorem initialRoot_frame (layout : CallerLayout) (entry : FramedHistory) (values : List E)
    (root : Digest32) (count : values.length = rootScalarCount layout)
    (first : entry.frames.head? = some (.absorb 0 (WHIRHistory.scalarBytes values)))
    (header : callerRoot layout (values.map CallerToken.sent) = some (root,[])) :
    initialRoot layout entry = some root := by
  cases frames : entry.frames with
  | nil => simp [frames] at first
  | cons frame rest =>
    simp only [frames,List.head?_cons,Option.some.injEq] at first
    subst frame
    simp only [initialRoot,frames,← count,WHIRHistory.parseExact_roundtrip]
    dsimp only [Bind.bind,Option.bind]
    rw [header]
    rfl

theorem interpretCaller_sourceRun (layout : CallerLayout) (tokens : List CallerToken)
    (claims : CallerClaims) (accepted : interpretCaller layout tokens = some claims) :
    ∃ rest, sourceClaims layout tokens = some (claims,rest) := by
  unfold interpretCaller at accepted
  split at accepted
  next => simp at accepted
  next =>
    cases run : sourceClaims layout tokens with
    | none => simp [run] at accepted
    | some pair =>
      simp only [run] at accepted
      dsimp only [Bind.bind,Option.bind] at accepted
      split at accepted
      next =>
        have same := Option.some.inj accepted
        exact ⟨pair.2,by rw [← same]⟩
      next => simp at accepted

/-- The original unguarded token source already fixes the root in the initial
physical frame. This is a refinement theorem, not a new acceptance condition. -/
theorem interpretCaller_initialRoot (layout : CallerLayout) (domain statement : Digest32)
    (tokens : List CallerToken) (claims : CallerClaims)
    (accepted : interpretCaller layout tokens = some claims) :
    initialRoot layout (tokenHistory domain statement tokens) = some claims.root := by
  obtain ⟨rest,run⟩ := interpretCaller_sourceRun layout tokens claims accepted
  obtain ⟨values,tail,count,hpref,header,delimiter⟩ :=
    sourceClaims_initialPrefix layout tokens rest claims run
  apply initialRoot_frame layout _ values claims.root count
  · rw [hpref]
    apply tokenHistory_initialFrame domain statement values tail _ delimiter
    intro empty
    rw [empty] at count
    cases layout <;> simp [rootScalarCount] at count
  · exact header

theorem decodeCaller_initialRoot (layout : CallerLayout) (entry : FramedHistory)
    (answers : Coordinate → Digest32) (claims : CallerClaims)
    (accepted : decodeCaller layout entry answers = some claims) :
    initialRoot layout entry = some claims.root := by
  cases ht : entryTokens entry answers with
  | none => simp [decodeCaller,ht] at accepted
  | some tokens =>
    have source : interpretCaller layout tokens = some claims := by
      simpa [decodeCaller,ht] using accepted
    have root := interpretCaller_initialRoot layout entry.domain entry.statement tokens claims source
    rw [entryTokens_history entry answers tokens ht] at root
    exact root

theorem decodeRequest_initialRoot (cap : Nat) (profile : Profile) (lanes : Nat)
    (layout : CallerLayout) (entry : FramedHistory) (answers : Coordinate → Digest32)
    (request : CausalBindingState.ClaimRequest cap profile)
    (accepted : decodeRequest cap profile lanes layout entry answers = some request) :
    initialRoot layout entry = some request.root := by
  cases hc : decodeCaller layout entry answers with
  | none => simp [decodeRequest,hc] at accepted
  | some claims =>
    have root := decodeCaller_initialRoot layout entry answers claims hc
    unfold decodeRequest at accepted
    split at accepted
    next => simp at accepted
    next =>
      simp only [hc] at accepted
      split at accepted
      next =>
        dsimp only [Bind.bind,Option.bind] at accepted
        split at accepted
        next =>
          split at accepted
          next =>
            cases Option.some.inj accepted
            exact root
          next => simp at accepted
        next => simp at accepted
      next => simp at accepted

/-- Any recovered request has precisely the root read before all draws. The
proof uses original source parsing and normalized frame grammar, not a guard. -/
theorem decodeAvailableRequest_initialRoot (cap : Nat) (profile : Profile) (lanes : Nat)
    (layout : CallerLayout) (entry : FramedHistory) (answers : Coordinate → Option Digest32)
    (request : CausalBindingState.ClaimRequest cap profile)
    (accepted : decodeAvailableRequest cap profile lanes layout entry answers = some request) :
    initialRoot layout entry = some request.root := by
  unfold decodeAvailableRequest at accepted
  split at accepted
  next =>
    exact decodeRequest_initialRoot cap profile lanes layout entry
      (fun q => (answers q).getD zeroDigest) request accepted
  next => simp at accepted

end Whir.WHIRCallerClaims
