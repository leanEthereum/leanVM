import Whir.PCSBCSCallerParserCost
import Whir.AnchoredSourceFreshCaller

/-! Reached source-operation accounting for the historical payload and anchored
record transport. The units are source operations, not CPU time: a pattern,
branch, scalar/Nat operation, projection, or constructor costs one. List
traversals are charged per visited cons and their terminal nil; append charges
its copied left spine. Indexed list lookup charges the visited prefix, including
failure. Array lookup and fixed-width field operations are primitive operations.
Opaque CPU output evaluation is charged separately, once at each of its four
reached calls. No transcript, sampler, or output cache is re-executed. -/
set_option autoImplicit false
namespace Whir.PCSBCSCallerPayloadCost
open Concrete FiatShamirGame WHIRCallerClaims AnchoredHeaderCodec
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

structure OutputCosts where
  call : Fin 4 → Nat
  pending : Fin 8 → Nat
  rootByte : Fin 32 → Nat
  contextByte : Fin 32 → Nat

def OutputCosts.total (cost : OutputCosts) : Nat :=
  (List.ofFn cost.call).sum

def OutputCosts.zero : OutputCosts := ⟨fun _ => 0,fun _ => 0,fun _ => 0,fun _ => 0⟩

@[simp] theorem erase_someFirst {A B : Type} (x : Option A)
    (yes : A → PCSBCSCallerParserCost.Parser B) (no : PCSBCSCallerParserCost.Parser B) :
    PCSBCSCallerParserCost.erase (match x with | some a => yes a | _ => no) =
      match x with | some a => PCSBCSCallerParserCost.erase (yes a)
                   | none => PCSBCSCallerParserCost.erase no := by
  cases x <;> rfl

/-- Charge an evaluated pure source expression without changing the cursor. -/
def charged {A : Type} (work : Nat) (value : A) : PCSBCSCallerParserCost.Parser A := do
  PCSBCSCallerParserCost.tick work
  pure value

@[simp] theorem erase_charged {A : Type} (work : Nat) (value : A) :
    PCSBCSCallerParserCost.erase (charged work value) = pure value := by
  simp [charged]

/-- Short-circuit predicate traversal, including predicate and branch costs. -/
def allWork {A : Type} (p : A → Bool) (predicateWork : A → Nat) : List A → Nat
  | [] => 1
  | x :: xs => 2 + predicateWork x + if p x then allWork p predicateWork xs else 0

def containsWork (x : Nat) : List Nat → Nat
  | [] => 1
  | y :: ys => 3 + if x == y then 0 else containsWork x ys

def indexWork {A : Type} : List A → Nat → Nat
  | [], _ => 1
  | _ :: _, 0 => 2
  | _ :: xs, n+1 => 2 + indexWork xs n

def dupsWork : List Nat → List Nat → Nat
  | [], seen => 2 * seen.length + 2
  | x :: xs, seen => 2 + containsWork x seen +
      if seen.contains x then dupsWork xs seen else 1 + dupsWork xs (x :: seen)

/-- Literal six-bit register coordinates; each range/map cell, testBit, branch,
field literal, and claim constructor is charged. The opaque getter is separate. -/
def exitClaims (column : Nat) (output : Fin 4 → UInt64) (cost : OutputCosts) :
    PCSBCSCallerParserCost.Costed (List ColumnClaim) :=
  ⟨WHIRCallerClaims.exitClaims column output,
    5 * (1 + (6 * 3 + 1) + (6 * 5 + 1)) + 4 * (1 + 1 + 1) + 14 + cost.total⟩

@[simp] theorem exitClaims_erasure (column : Nat) (output : Fin 4 → UInt64)
    (cost : OutputCosts) : (exitClaims column output cost).value = WHIRCallerClaims.exitClaims column output := rfl

theorem exitClaims_work (column : Nat) (output : Fin 4 → UInt64) (cost : OutputCosts) :
    (exitClaims column output cost).work = 281 + cost.total := rfl

theorem exitClaims_length (column : Nat) (output : Fin 4 → UInt64) (cost : OutputCosts) :
    (exitClaims column output cost).value.length = 5 := by
  simp [exitClaims,WHIRCallerClaims.exitClaims]

theorem exitClaims_values (column : Nat) (output : Fin 4 → UInt64) (cost : OutputCosts) :
    ((exitClaims column output cost).value.map ColumnClaim.value) =
      E.ofK 93 :: List.ofFn (fun i => E.ofK (output i)) := by
  simp [exitClaims,WHIRCallerClaims.exitClaims]

def columnsWork (bus : List ColumnClaim) (paired : List (Nat × TableClaims)) : Nat :=
  2 * bus.length + 1 + paired.length + 1 +
    (paired.map (fun (base,claims) =>
      (PCSBCSCallerParserCost.tableColumns base claims).work + 2 * claims.evals.length + 1)).sum

def recPayload (layout : RecLayout) :
    PCSBCSCallerParserCost.Parser (List RingPCSGame.FamilyClaim × Array RingPCSGame.PointClaim) := do
  let (point,bus) ← PCSBCSCallerParserCost.busClaims layout.bus
  let _ ← PCSBCSCallerParserCost.drawScalar
  let airs ← charged (3 * layout.tables.length + 1) (layout.tables.map Prod.snd)
  let tables ← PCSBCSCallerParserCost.constraintClaims airs point
  let rings ← PCSBCSCallerParserCost.flockClaims [layout.hash]
  let paired := (layout.tables.map Prod.fst).zip tables
  let columns ← charged (3 * layout.tables.length + 1 + 4 * min layout.tables.length tables.length + 1 +
    columnsWork bus paired)
    (bus ++ paired.flatMap (fun (base,claims) => WHIRCallerClaims.tableColumns base claims))
  let placed := PCSBCSCallerParserCost.placeClaims layout.placements columns
  let points ← PCSBCSCallerParserCost.liftOption placed.work placed.value
  pure (rings,points)

def settledClaims (tables : List CpuTableLayout) (point : List E) : PCSBCSCallerParserCost.Parser (List TableClaims) := do
  let mut claims := []
  for table in tables do
    PCSBCSCallerParserCost.tick 2
    if table.settled then
      PCSBCSCallerParserCost.tick (allWork (· < table.committedColumns) (fun _ => 2) table.summedColumns)
      PCSBCSCallerParserCost.check (table.summedColumns.all (· < table.committedColumns))
      PCSBCSCallerParserCost.tick (dupsWork table.summedColumns [] + table.summedColumns.eraseDups.length + 1 +
        table.summedColumns.length + 1 + 1)
      PCSBCSCallerParserCost.check (table.summedColumns.eraseDups.length == table.summedColumns.length)
      PCSBCSCallerParserCost.tick (table.summedColumns.length + 2)
      let sent ← PCSBCSCallerParserCost.readScalars (table.committedColumns-table.summedColumns.length)
      let mut remaining := sent
      let mut evals := []
      PCSBCSCallerParserCost.tick (3 * table.committedColumns + 1)
      for c in List.range table.committedColumns do
        PCSBCSCallerParserCost.tick (1 + containsWork c table.summedColumns + 2 * evals.length + 2)
        if c ∈ table.summedColumns then evals := evals ++ [0]
        else
          match remaining with
          | [] => PCSBCSCallerParserCost.check false
          | x :: xs => evals := evals ++ [x]; remaining := xs
      PCSBCSCallerParserCost.tick (point.length + 4)
      PCSBCSCallerParserCost.check (table.tau ≤ point.length && remaining.isEmpty)
      PCSBCSCallerParserCost.tick (2 * min table.tau point.length + 1 + 2 * claims.length + 3)
      claims := claims ++ [⟨point.take table.tau,evals,[]⟩]
  pure claims

def cpuPayloadBeforeExit (layout : CpuLayout) :
    PCSBCSCallerParserCost.Parser (List RingPCSGame.FamilyClaim × List ColumnClaim) := do
  let (point,bus) ← PCSBCSCallerParserCost.busClaims layout.bus
  let settled ← settledClaims layout.tables point
  let _ ← PCSBCSCallerParserCost.drawScalar
  let producerAirs ← charged (7 * layout.bus.producers.length + 1)
    (layout.bus.producers.map (fun p => (⟨p.kappa,2*p.bits,p.bits,[]⟩ : AirLayout)))
  let airs ← charged (8 * layout.tables.length +
    (layout.tables.map (fun t => t.summedColumns.length + 1)).sum + 2)
    (layout.tables.map CpuTableLayout.air ++ producerAirs)
  let summed ← PCSBCSCallerParserCost.constraintClaims airs point
  PCSBCSCallerParserCost.tick (settled.length + 1 + 2 * min settled.length layout.tables.length + 1 +
    allWork (·.settled) (fun _ => 1) (layout.tables.take settled.length))
  PCSBCSCallerParserCost.check (layout.tables.take settled.length |>.all (·.settled))
  PCSBCSCallerParserCost.tick (settled.length + 1 + min settled.length layout.tables.length + 1 +
    allWork (! ·.settled) (fun _ => 2) (layout.tables.drop settled.length))
  PCSBCSCallerParserCost.check (layout.tables.drop settled.length |>.all (! ·.settled))
  let columns ← charged (layout.tables.length + 1 + 2 * min layout.tables.length summed.length + 1 +
    settled.length + 1 + min settled.length (min layout.tables.length summed.length) + 1 +
    2 * settled.length + 1) (settled ++ (summed.take layout.tables.length).drop settled.length)
  let packed ← PCSBCSCallerParserCost.flockClaims layout.flock
  let producers ← charged (layout.tables.length + 1 + min layout.tables.length summed.length + 1)
    (summed.drop layout.tables.length)
  PCSBCSCallerParserCost.tick (4 * min layout.bus.producers.length producers.length + 1)
  let mut rings := packed
  for (p,c) in layout.bus.producers.zip producers do
    let ring := PCSBCSCallerParserCost.paddedRing p.window c.point c.evals
    PCSBCSCallerParserCost.tick (1 + ring.work)
    match ring.value with
    | some ring => PCSBCSCallerParserCost.tick (2 * rings.length + 2); rings := rings ++ [ring]
    | none => PCSBCSCallerParserCost.check false
  for word in layout.registers do
    PCSBCSCallerParserCost.tick 2
    let some first := word.tables.head? | return ← PCSBCSCallerParserCost.liftOption 1 none
    PCSBCSCallerParserCost.tick (indexWork summed first)
    let some firstClaims := summed[first]? | return ← PCSBCSCallerParserCost.liftOption 1 none
    let mut slices := []
    for t in word.tables do
      PCSBCSCallerParserCost.tick (1 + indexWork summed t)
      let some claims := summed[t]? | return ← PCSBCSCallerParserCost.liftOption 1 none
      PCSBCSCallerParserCost.tick (2 * slices.length + 2)
      slices := slices ++ claims.slices
    let ring := PCSBCSCallerParserCost.paddedRing word.offset firstClaims.point slices
    PCSBCSCallerParserCost.tick ring.work
    match ring.value with
    | some ring => PCSBCSCallerParserCost.tick (2 * rings.length + 2); rings := rings ++ [ring]
    | none => PCSBCSCallerParserCost.check false
  let paired := (layout.tables.map CpuTableLayout.base).zip columns
  let columnClaims ← charged (3 * layout.tables.length + 1 +
    4 * min layout.tables.length columns.length + 1 + columnsWork bus paired)
    (bus ++ paired.flatMap (fun (base,claims) => WHIRCallerClaims.tableColumns base claims))
  pure (rings,columnClaims)

def cpuPayload (layout : CpuLayout) (cost : OutputCosts) :
    PCSBCSCallerParserCost.Parser (List RingPCSGame.FamilyClaim × Array RingPCSGame.PointClaim) := do
  let (rings,columns) ← cpuPayloadBeforeExit layout
  let exits := exitClaims layout.finalRegisterColumn layout.output cost
  let columnClaims ← charged (exits.work + 2 * columns.length + 1) (columns ++ exits.value)
  let placed := PCSBCSCallerParserCost.placeClaims layout.placements columnClaims
  let points ← PCSBCSCallerParserCost.liftOption placed.work placed.value
  pure (rings,points)

/-- This is the reached callback trace: the four indices are present exactly
when the ordinary caller reached exit construction, even if placement rejects. -/
def outputGetterTrace (layout : CpuLayout) (tokens : List CallerToken) : List (Fin 4) :=
  if (cpuPayloadBeforeExit layout tokens).result.isSome then List.finRange 4 else []

theorem outputGetterTrace_length (layout : CpuLayout) (tokens : List CallerToken) :
    (outputGetterTrace layout tokens).length =
      if (cpuPayloadBeforeExit layout tokens).result.isSome then 4 else 0 := by
  unfold outputGetterTrace
  split <;> simp

theorem outputGetterTrace_cost (layout : CpuLayout) (tokens : List CallerToken) (cost : OutputCosts) :
    ((outputGetterTrace layout tokens).map cost.call).sum =
      if (cpuPayloadBeforeExit layout tokens).result.isSome then cost.total else 0 := by
  unfold outputGetterTrace
  split <;> simp [List.finRange,OutputCosts.total]


def readAnnouncements : List Nat → PCSBCSCallerParserCost.Parser Unit
  | [] => do PCSBCSCallerParserCost.tick 1; pure ()
  | height :: rest => do
    PCSBCSCallerParserCost.tick 1
    let sent ← PCSBCSCallerParserCost.readScalar
    PCSBCSCallerParserCost.tick 5
    PCSBCSCallerParserCost.check (sent == E.ofK (UInt64.ofNat height))
    readAnnouncements rest

def prelude : CallerLayout → PCSBCSCallerParserCost.Parser Unit
  | .recursion _ => do PCSBCSCallerParserCost.tick 1; pure ()
  | .cpu layout => do
    PCSBCSCallerParserCost.tick (layout.tables.length + 3)
    PCSBCSCallerParserCost.check (layout.tables.length == 11)
    let heights ← charged (3 * layout.tables.length + 2)
      (layout.tables.map CpuTableLayout.tau ++ [layout.logInvRate])
    readAnnouncements heights
    let clock ← PCSBCSCallerParserCost.readScalar
    PCSBCSCallerParserCost.tick (3 + (if clock.c1 == 0 then
      3 + (if clock.c2 == 0 then 125 + (if clock.c0.toNat / 2^40 == 1 then 4 else 0) else 0) else 0))
    PCSBCSCallerParserCost.check
      (clock.c1 == 0 && clock.c2 == 0 && clock.c0.toNat / 2^40 == 1 && clock.c0.toNat % 32 == 0)

def wordsWork (layout : CallerLayout) : Nat :=
  3 + ((callerPlacements layout).toList.map (fun p => match p with
    | .committed _ d => 3 * d + 5
    | _ => 2)).sum

/-- Layout arithmetic includes every placement visit, repeated power, log2
argument, and lane division; no supplied geometry certificate is evaluated. -/
def shapeWork (layout : CallerLayout) : Nat :=
  let w := callerWords layout
  let m := callerMu layout
  3 * wordsWork layout + 2 * (max w 1 - 1) + 3 * (m - 6) + 26

def scalarEqWork (x y : E) : Nat :=
  4 + if x.c0 == y.c0 then 4 + if x.c1 == y.c1 then 4 else 0 else 0

def headerWork (shape : Shape) : List E → Nat
  | [marker,sh,lanes,a,b] =>
    6 + scalarEqWork marker anchorMarker +
      if marker = anchorMarker then 4 + scalarEqWork sh (shapeScalar shape) +
        if sh = shapeScalar shape then 2 + scalarEqWork lanes (lanesScalar shape) +
          if lanes = lanesScalar shape then 2 +
            if a.c2 = 0 then 2 + if b.c2 = 0 then 2 else 0 else 0
          else 0
        else 0
      else 0
  | _ => 1

def shapeValidWork (shape : Shape) : Nat :=
  4 + if shape.logBatch < shape.logN then
    3 + if shape.logN < 64 then
      3 + if 1 ≤ shape.logRate then
        7 + if shape.logN - shape.logBatch + shape.logRate < 64 then
          3 + if 1 ≤ shape.lanes then 3 * shape.logBatch + 4 else 0
        else 0
      else 0
    else 0
  else 0

def receive (layout : CallerLayout) (original : Context) :
    PCSBCSCallerParserCost.Parser Record := do
  PCSBCSCallerParserCost.tick (shapeWork layout + shapeValidWork (AnchoredSourceCaller.shape layout))
  PCSBCSCallerParserCost.check (decide (AnchoredSourceCaller.shape layout).Valid)
  let header ← PCSBCSCallerParserCost.readScalars 5
  PCSBCSCallerParserCost.tick (shapeWork layout + headerWork (AnchoredSourceCaller.shape layout) header)
  let some root := parseHeader (AnchoredSourceCaller.shape layout) header |
    return ← PCSBCSCallerParserCost.liftOption 1 none
  PCSBCSCallerParserCost.tick (shapeWork layout + 1)
  let point ← PCSBCSCallerParserCost.drawScalars (AnchoredSourceCaller.shape layout).logN
  let value ← PCSBCSCallerParserCost.readScalar
  PCSBCSCallerParserCost.tick (shapeWork layout + 1)
  pure ⟨AnchoredSourceCaller.shape layout,root,original,point,value⟩

def payload (layout : CallerLayout) (cost : OutputCosts) :
    PCSBCSCallerParserCost.Parser (List RingPCSGame.FamilyClaim × Array RingPCSGame.PointClaim) :=
  match layout with
  | .recursion l => recPayload l
  | .cpu l => cpuPayload l cost

theorem sumMap_le {A : Type} (xs : List A) (f : A → Nat) (k : Nat)
    (bound : ∀ x ∈ xs, f x ≤ k) : (xs.map f).sum ≤ k * xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := bound x (by simp)
    have ht := ih (fun y hy => bound y (by simp [hy]))
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    nlinarith
/-- Each live pending pack pays its range cell and three word accesses, Nat
index arithmetic and branches. Fixed digest decoding pays four eight-byte
folds per digest (read, projection, shift, addition at each byte). -/
def pendingPackWork (context : Context) (i : Nat) : Nat :=
  23 + (if 3 * i + 1 < (context.pendingBytes + 7) / 8 then 6 else 1) +
    (if 3 * i + 2 < (context.pendingBytes + 7) / 8 then 6 else 1)

theorem pendingPackWork_le (context : Context) (i : Nat) : pendingPackWork context i ≤ 35 := by
  simp only [pendingPackWork]
  split <;> split <;> omega

def openingWork (record : Record) : Nat :=
  let packs := (record.context.pendingBytes + 23) / 24
  4 * (4 * (8 * 4 + 2) + 3) + 17 +
    (3 * packs + 1) + ((List.range packs).map (pendingPackWork record.context)).sum + 1 +
      19 + (2 * packs + 1) + (2 * record.point.length + 1)


def scalarListEqWork : List E → List E → Nat
  | [], _ => 1
  | _ :: _, [] => 1
  | x :: xs, y :: ys => 2 + scalarEqWork x y + if x == y then scalarListEqWork xs ys else 0

/-- Actual opaque pending-word accesses in one `pendingPacks` construction.
The source modulo-eight indices are retained even for non-normalized inputs. -/
def pendingPackGetterTrace (context : Context) (i : Nat) : List (Fin 8) :=
  [⟨3*i % 8,Nat.mod_lt _ (by decide)⟩] ++
    (if 3*i+1 < (context.pendingBytes+7)/8 then
      [⟨(3*i+1)%8,Nat.mod_lt _ (by decide)⟩] else []) ++
    (if 3*i+2 < (context.pendingBytes+7)/8 then
      [⟨(3*i+2)%8,Nat.mod_lt _ (by decide)⟩] else [])

def pendingGetterTrace (context : Context) : List (Fin 8) :=
  (List.range ((context.pendingBytes+23)/24)).flatMap (pendingPackGetterTrace context)

def pendingGetterWork (context : Context) (cost : OutputCosts) : Nat :=
  ((pendingGetterTrace context).map cost.pending).sum

/-- The two tuple projections each execute the complete 32-byte decoder. -/
def digestGetterTrace : List (Fin 32) := List.finRange 32 ++ List.finRange 32

def openingGetterWork (record : Record) (cost : OutputCosts) : Nat :=
  pendingGetterWork record.context cost + (digestGetterTrace.map cost.rootByte).sum +
    (digestGetterTrace.map cost.contextByte).sum

def binding (record : Record) (cost : OutputCosts) : PCSBCSCallerParserCost.Parser Unit := do
  PCSBCSCallerParserCost.tick (openingWork record + openingGetterWork record cost + (openingScalars record).length + 1)
  let frame ← PCSBCSCallerParserCost.readScalars (openingScalars record).length
  PCSBCSCallerParserCost.tick (openingWork record + openingGetterWork record cost + scalarListEqWork frame (openingScalars record))
  PCSBCSCallerParserCost.check (frame == openingScalars record)

@[simp] theorem binding_ignore_output_prices (record : Record) (cost : OutputCosts)
    (calls : Fin 4 → Nat) :
    binding record {cost with call := calls} = binding record cost := rfl
def sourceClaims (layout : CallerLayout) (original : Context) (cost : OutputCosts) :
    PCSBCSCallerParserCost.Parser AnchoredSourceCaller.Claims := do
  prelude layout
  let record ← receive layout original
  let (families,points) ← payload layout cost
  binding record cost
  PCSBCSCallerParserCost.tick 3
  pure ⟨record,⟨record.root,families,points⟩⟩

def freshSourceClaims (layout : CallerLayout) (saved : Record) (cost : OutputCosts) :
    PCSBCSCallerParserCost.Parser AnchoredSourceCaller.Claims := do
  let (families,points) ← payload layout cost
  binding saved cost
  PCSBCSCallerParserCost.tick 3
  pure ⟨saved,⟨saved.root,families,points⟩⟩

@[simp] theorem readAnnouncements_erasure (heights : List Nat) :
    PCSBCSCallerParserCost.erase (readAnnouncements heights) = WHIRCallerClaims.readAnnouncements heights := by
  induction heights with
  | nil => simp [readAnnouncements,WHIRCallerClaims.readAnnouncements]
  | cons x xs ih => simp [readAnnouncements,WHIRCallerClaims.readAnnouncements,ih]

@[simp] theorem prelude_erasure (layout : CallerLayout) :
    PCSBCSCallerParserCost.erase (prelude layout) = AnchoredSourceCaller.prelude layout := by
  cases layout <;> simp [prelude,AnchoredSourceCaller.prelude]

@[simp] private theorem sourceFailure_bind {A B : Type} (f : A → CallerParser B) :
    ((fun _ => none : CallerParser A) >>= f) = (fun _ => none : CallerParser B) := rfl

@[simp] private theorem sourceFailure_map {A B : Type} (f : A → B) :
    (@Functor.map CallerParser _ A B f (fun _ => none)) =
      (fun _ => none : CallerParser B) := rfl
@[simp] theorem receive_erasure (layout : CallerLayout) (original : Context) :
    PCSBCSCallerParserCost.erase (receive layout original) = AnchoredSourceCaller.receive layout original := by
  simp [receive,AnchoredSourceCaller.receive]
  congr! 8
  all_goals split <;> simp_all

@[simp] theorem binding_erasure (record : Record) (cost : OutputCosts) :
    PCSBCSCallerParserCost.erase (binding record cost) = AnchoredSourceCaller.binding record := by
  simp [binding,AnchoredSourceCaller.binding]

@[simp] theorem recPayload_erasure (layout : RecLayout) :
    PCSBCSCallerParserCost.erase (recPayload layout) = WHIRCallerClaims.recPayload layout := by
  simp [recPayload,WHIRCallerClaims.recPayload]
  congr! 12
  all_goals try (split <;> simp_all)

@[simp] theorem settledClaims_erasure (tables : List CpuTableLayout) (point : List E) :
    PCSBCSCallerParserCost.erase (settledClaims tables point) =
      WHIRCallerClaims.settledClaims tables point := by
  simp [settledClaims,WHIRCallerClaims.settledClaims]
  congr! 20
  all_goals split <;> simp_all

/- The source's early-return desugaring carries an `Option finalResult` through
the register loops. Every attempted early return first executes the failing
parser. These helpers remove that unreachable carrier without assuming
acceptance or changing failures/cursors. -/

@[simp] private theorem erase_catchAll {A B : Type} (x : Option A)
    (yes : A → PCSBCSCallerParserCost.Parser B)
    (no : Option A → PCSBCSCallerParserCost.Parser B) :
    PCSBCSCallerParserCost.erase (match x with | some a => yes a | missing => no missing) =
      match x with | some a => PCSBCSCallerParserCost.erase (yes a)
                   | missing => PCSBCSCallerParserCost.erase (no missing) := by
  cases x <;> rfl


private theorem sourceForIn_none {A B R : Type} (xs : List A) (initial : B)
    (step : A → B → CallerParser B) :
    forIn xs ((none : Option R),initial) (fun a state => do
      let next ← step a state.2
      pure (.yield (none,next))) =
      (do let last ← forIn xs initial (fun a value => do
            let next ← step a value
            pure (.yield next))
          pure (none,last)) := by
  induction xs generalizing initial with
  | nil => simp
  | cons x xs ih =>
    simp only [List.forIn_cons,bind_assoc,pure_bind]
    simp only [ih]

private def sourceSliceStep (summed : List TableClaims) (t : Nat) (slices : List E) :
    CallerParser (List E) :=
  match summed[t]? with
  | some claims => pure (slices ++ claims.slices)
  | none => fun _ => none

private def sourceSlices (summed : List TableClaims) (tables : List Nat) (slices : List E) :
    CallerParser (List E) :=
  forIn tables slices (fun t slices => do
    let next ← sourceSliceStep summed t slices
    pure (.yield next))

private def sourceSliceLoop {R : Type} (summed : List TableClaims) (tables : List Nat)
    (slices : List E) : CallerParser (Option R × List E) :=
  forIn tables (none,slices) (fun t state =>
    match summed[t]? with
    | some claims => pure (.yield (none,state.2 ++ claims.slices))
    | none => do
      let out ← (fun _ => none : CallerParser R)
      pure (.done (some out,state.2)))

private theorem sourceSliceLoop_eq {R : Type} (summed : List TableClaims) (tables : List Nat)
    (slices : List E) : sourceSliceLoop (R := R) summed tables slices =
  forIn tables (none,slices) (fun t state =>
    match summed[t]? with
    | some claims => pure (.yield (none,state.2 ++ claims.slices))
    | _missing => fun _ => none) := by
  unfold sourceSliceLoop
  congr 1
  funext t state
  cases summed[t]? <;> simp

private theorem sourceSliceLoop_normalize {R : Type} (summed : List TableClaims)
    (tables : List Nat) (slices : List E) :
    sourceSliceLoop (R := R) summed tables slices =
      (do let out ← sourceSlices summed tables slices; pure (none,out)) := by
  have body : (fun (t : Nat) (state : Option R × List E) =>
      show CallerParser (ForInStep (Option R × List E)) from match summed[t]? with
      | some claims => pure (.yield (none,state.2 ++ claims.slices))
      | none => do
        let out ← (fun _ => none : CallerParser R)
        pure (.done (some out,state.2))) =
      (fun t state => show CallerParser (ForInStep (Option R × List E)) from do
        let next ← sourceSliceStep summed t state.2
        pure (.yield (none,next))) := by
    funext t state
    cases h : summed[t]? <;> simp [sourceSliceStep,h]
  unfold sourceSliceLoop
  rw [body,sourceForIn_none]
  rfl

private def sourceRegisterStep (summed : List TableClaims) (word : RegisterWord)
    (rings : List RingPCSGame.FamilyClaim) : CallerParser (List RingPCSGame.FamilyClaim) :=
  match word.tables.head? with
  | none => fun _ => none
  | some first => match summed[first]? with
    | none => fun _ => none
    | some firstClaims => do
      let slices ← sourceSlices summed word.tables []
      match WHIRCallerClaims.paddedRing word.offset firstClaims.point slices with
      | some ring => pure (rings ++ [ring])
      | none => do WHIRCallerClaims.check false; pure rings

private def sourceRegisterLoop {R : Type} (summed : List TableClaims)
    (words : List RegisterWord) (rings : List RingPCSGame.FamilyClaim) :
    CallerParser (Option R × List RingPCSGame.FamilyClaim) :=
  forIn words (none,rings) (fun word state =>
    match word.tables.head? with
    | some first => match summed[first]? with
      | some firstClaims => do
        let pair ← sourceSliceLoop summed word.tables []
        match pair.1 with
        | some out => pure (.done (some out,state.2))
        | none => match WHIRCallerClaims.paddedRing word.offset firstClaims.point pair.2 with
          | some ring => pure (.yield (none,state.2 ++ [ring]))
          | none => do WHIRCallerClaims.check false; pure (.yield (none,state.2))
      | none => do
        let out ← (fun _ => none : CallerParser R)
        pure (.done (some out,state.2))
    | none => do
      let out ← (fun _ => none : CallerParser R)
      pure (.done (some out,state.2)))

private theorem sourceRegisterLoop_eq {R : Type} (summed : List TableClaims)
    (words : List RegisterWord) (rings : List RingPCSGame.FamilyClaim) :
    sourceRegisterLoop (R := R) summed words rings =
  forIn words (none,rings) (fun word state =>
    match word.tables.head? with
    | some first => match summed[first]? with
      | some firstClaims => do
        let pair ← sourceSliceLoop summed word.tables []
        match pair.1 with
        | some out => pure (.done (some out,state.2))
        | none => match WHIRCallerClaims.paddedRing word.offset firstClaims.point pair.2 with
          | some ring => pure (.yield (none,state.2 ++ [ring]))
          | none => do WHIRCallerClaims.check false; pure (.yield (none,state.2))
      | _missing => fun _ => none
    | _missing => fun _ => none) := by
  unfold sourceRegisterLoop
  congr 1
  funext word state
  cases h : word.tables.head? with
  | none => simp
  | some first =>
    cases hc : summed[first]? <;> simp [hc]

private theorem sourceRegisterLoop_normalize {R : Type} (summed : List TableClaims)
    (words : List RegisterWord) (rings : List RingPCSGame.FamilyClaim) :
    sourceRegisterLoop (R := R) summed words rings =
      (do let out ← forIn words rings (fun word rings => do
            let next ← sourceRegisterStep summed word rings
            pure (.yield next))
          pure (none,out)) := by
  unfold sourceRegisterLoop
  simp only [sourceSliceLoop_normalize,bind_assoc,pure_bind]
  have body : (fun (word : RegisterWord) (state : Option R × List RingPCSGame.FamilyClaim) =>
      show CallerParser (ForInStep (Option R × List RingPCSGame.FamilyClaim)) from match word.tables.head? with
      | some first => match summed[first]? with
        | some firstClaims => do
          let slices ← sourceSlices summed word.tables []
          match WHIRCallerClaims.paddedRing word.offset firstClaims.point slices with
          | some ring => pure (.yield (none,state.2 ++ [ring]))
          | none => do WHIRCallerClaims.check false; pure (.yield (none,state.2))
        | none => fun _ => none
      | none => fun _ => none) =
      (fun word state => show CallerParser (ForInStep (Option R × List RingPCSGame.FamilyClaim)) from do
        let next ← sourceRegisterStep summed word state.2
        pure (.yield (none,next))) := by
    funext word state
    cases h : word.tables.head? with
    | none => simp [h,sourceRegisterStep]
    | some first =>
      cases hc : summed[first]? with
      | none => simp [h,hc,sourceRegisterStep]
      | some claims =>
        simp only [h,hc,sourceRegisterStep]
        simp only [bind_assoc]
        congr 1
        funext slices
        cases hr : WHIRCallerClaims.paddedRing word.offset claims.point slices <;>
          simp [WHIRCallerClaims.check]
  simp only [sourceFailure_bind]
  rw [body,sourceForIn_none]

private def sourceRegisterRaw {R : Type} (summed : List TableClaims)
    (words : List RegisterWord) (rings : List RingPCSGame.FamilyClaim) :
    CallerParser (Option R × List RingPCSGame.FamilyClaim) :=
  forIn words (none,rings) (fun word state =>
    match word.tables.head? with
    | some first => match summed[first]? with
      | some firstClaims => do
        let pair ← forIn word.tables (none,[]) (fun t state =>
          match summed[t]? with
          | some claims => pure (.yield (none,state.2 ++ claims.slices))
          | _missing => fun _ => none)
        match pair.1 with
        | some out => pure (.done (some out,state.2))
        | none => match WHIRCallerClaims.paddedRing word.offset firstClaims.point pair.2 with
          | some ring => pure (.yield (none,state.2 ++ [ring]))
          | none => do WHIRCallerClaims.check false; pure (.yield (none,state.2))
      | _missing => fun _ => none
    | _missing => fun _ => none)

private theorem sourceRegisterRaw_eq {R : Type} (summed : List TableClaims)
    (words : List RegisterWord) (rings : List RingPCSGame.FamilyClaim) :
    sourceRegisterRaw (R := R) summed words rings = sourceRegisterLoop summed words rings := by
  unfold sourceRegisterRaw
  rw [sourceRegisterLoop_eq]
  congr 1
  funext word state
  cases head : word.tables.head? with
  | none => simp
  | some first =>
    cases claimed : summed[first]? with
    | none => simp [claimed]
    | some claims =>
      simp only [claimed]
      rw [sourceSliceLoop_eq]

private def countedSliceRaw {R : Type} (summed : List TableClaims) (tables : List Nat)
    (slices : List E) : PCSBCSCallerParserCost.Parser (Option R × List E) :=
  forIn tables (none,slices) (fun t state => do
    PCSBCSCallerParserCost.tick (1 + indexWork summed t)
    match summed[t]? with
    | some claims => do
      PCSBCSCallerParserCost.tick (2 * state.2.length + 2)
      pure (.yield (none,state.2 ++ claims.slices))
    | _missing => do
      let out ← PCSBCSCallerParserCost.liftOption 1 none
      pure (.done (some out,state.2)))

private theorem countedSliceRaw_erasure {R : Type} (summed : List TableClaims)
    (tables : List Nat) (slices : List E) :
    PCSBCSCallerParserCost.erase (countedSliceRaw (R := R) summed tables slices) =
      sourceSliceLoop summed tables slices := by
  simp only [countedSliceRaw,PCSBCSCallerParserCost.erase_forIn]
  unfold sourceSliceLoop
  congr 1
  funext t state
  cases summed[t]? <;> simp

private def countedRegisterRaw {R : Type} (summed : List TableClaims)
    (words : List RegisterWord) (rings : List RingPCSGame.FamilyClaim) :
    PCSBCSCallerParserCost.Parser (Option R × List RingPCSGame.FamilyClaim) :=
  forIn words (none,rings) (fun word state =>
    match word.tables.head? with
    | some first => do
      PCSBCSCallerParserCost.tick (indexWork summed first)
      match summed[first]? with
      | some firstClaims => do
        let pair ← countedSliceRaw summed word.tables []
        match pair.1 with
        | some out => pure (.done (some out,state.2))
        | none => do
          PCSBCSCallerParserCost.tick
            (PCSBCSCallerParserCost.paddedRing word.offset firstClaims.point pair.2).work
          match WHIRCallerClaims.paddedRing word.offset firstClaims.point pair.2 with
          | some ring => do
            PCSBCSCallerParserCost.tick (2 * state.2.length + 2)
            pure (.yield (none,state.2 ++ [ring]))
          | none => do PCSBCSCallerParserCost.check false; pure (.yield (none,state.2))
      | _missing => do
        let out ← PCSBCSCallerParserCost.liftOption 1 none
        pure (.done (some out,state.2))
    | _missing => do
      let out ← PCSBCSCallerParserCost.liftOption 1 none
      pure (.done (some out,state.2)))

private theorem countedRegisterRaw_erasure {R : Type} (summed : List TableClaims)
    (words : List RegisterWord) (rings : List RingPCSGame.FamilyClaim) :
    PCSBCSCallerParserCost.erase (countedRegisterRaw (R := R) summed words rings) =
      sourceRegisterLoop summed words rings := by
  simp only [countedRegisterRaw,PCSBCSCallerParserCost.erase_forIn]
  unfold sourceRegisterLoop
  congr 1
  funext word state
  cases head : word.tables.head? with
  | none => simp
  | some first =>
    cases claimed : summed[first]? with
    | none => simp [claimed]
    | some claims =>
      simp only [claimed]
      simp only [PCSBCSCallerParserCost.erase_bind,PCSBCSCallerParserCost.tick_erasure,
        pure_bind,countedSliceRaw_erasure]
      congr 1
      funext pair
      cases branch : pair.1 with
      | some out => simp
      | none =>
        cases WHIRCallerClaims.paddedRing word.offset claims.point pair.2 <;> simp

@[simp] theorem cpuPayload_erasure (layout : CpuLayout) (cost : OutputCosts) :
    PCSBCSCallerParserCost.erase (cpuPayload layout cost) = WHIRCallerClaims.cpuPayload layout := by
  simp [cpuPayload,cpuPayloadBeforeExit,WHIRCallerClaims.cpuPayload,bind_assoc]
  congr 1
  funext bus
  congr 1
  funext settled
  congr 1
  funext coin
  congr 1
  funext summed
  simp_rw [← bind_pure_comp]
  congr! 10
  · rename_i _ _ producer rings
    cases WHIRCallerClaims.paddedRing producer.1.window producer.2.point producer.2.evals <;>
      simp
  · rename_i _ _ rings
    conv_rhs =>
      lhs
      change sourceRegisterRaw (R := List RingPCSGame.FamilyClaim × Array RingPCSGame.PointClaim)
        summed layout.registers rings
      rw [sourceRegisterRaw_eq,sourceRegisterLoop_normalize]
    conv_lhs =>
      lhs
      rw [←PCSBCSCallerParserCost.erase_forIn]
      change PCSBCSCallerParserCost.erase
        (countedRegisterRaw (R := List RingPCSGame.FamilyClaim × List ColumnClaim)
          summed layout.registers rings)
      rw [countedRegisterRaw_erasure,sourceRegisterLoop_normalize]
    simp only [bind_assoc,pure_bind]
    congr 1
    funext out
    simp
    split <;> simp_all

@[simp] theorem payload_erasure (layout : CallerLayout) (cost : OutputCosts) :
    PCSBCSCallerParserCost.erase (payload layout cost) = AnchoredSourceCaller.payload layout := by
  cases layout <;> simp [payload,AnchoredSourceCaller.payload]

@[simp] theorem sourceClaims_erasure (layout : CallerLayout) (original : Context) (cost : OutputCosts) :
    PCSBCSCallerParserCost.erase (sourceClaims layout original cost) =
      AnchoredSourceCaller.sourceClaims layout original := by
  simp [sourceClaims,AnchoredSourceCaller.sourceClaims]

@[simp] theorem freshSourceClaims_erasure (layout : CallerLayout) (saved : Record) (cost : OutputCosts) :
    PCSBCSCallerParserCost.erase (freshSourceClaims layout saved cost) =
      AnchoredSourceFreshCaller.sourceClaims layout saved := by
  simp [freshSourceClaims,AnchoredSourceFreshCaller.sourceClaims]

theorem allWork_le {A : Type} (p : A → Bool) (w : A → Nat) (xs : List A) (k : Nat)
    (bound : ∀ x ∈ xs, w x ≤ k) : allWork p w xs ≤ (k + 2) * xs.length + 1 := by
  induction xs with
  | nil => simp [allWork]
  | cons x xs ih =>
    have hx := bound x (by simp)
    have ht := ih (fun y hy => bound y (by simp [hy]))
    simp only [allWork,List.length_cons]
    split <;> nlinarith

theorem containsWork_le (x : Nat) (xs : List Nat) :
    containsWork x xs ≤ 3 * xs.length + 1 := by
  induction xs with
  | nil => simp [containsWork]
  | cons y ys ih =>
    simp only [containsWork,List.length_cons]
    split <;> omega

theorem indexWork_le {A : Type} (xs : List A) (index : Nat) :
    indexWork xs index ≤ 2 * xs.length + 1 := by
  induction xs generalizing index with
  | nil => simp [indexWork]
  | cons x xs ih =>
    cases index with
    | zero => simp [indexWork]; omega
    | succ n =>
      have ht := ih n
      simp only [indexWork,List.length_cons]
      omega

theorem dupsWork_le (xs seen : List Nat) :
    dupsWork xs seen ≤ 3 * (xs.length + seen.length + 1) * (xs.length + 1) := by
  induction xs generalizing seen with
  | nil => simp [dupsWork]; omega
  | cons x xs ih =>
    have hc := containsWork_le x seen
    have hs := ih seen
    have hn := ih (x :: seen)
    simp only [List.length_cons] at hn ⊢
    simp only [dupsWork]
    split <;> nlinarith

theorem openingWork_polynomial (record : Record) :
    openingWork record ≤ 42 * (record.context.pendingBytes + record.point.length + 1) + 600 := by
  have hd : (record.context.pendingBytes + 23) / 24 ≤ record.context.pendingBytes + 1 := by omega
  have hs := sumMap_le (List.range ((record.context.pendingBytes + 23) / 24))
    (pendingPackWork record.context) 35 (fun i _ => pendingPackWork_le record.context i)
  simp only [List.length_range] at hs
  simp only [openingWork]
  omega

theorem cpuPayload_output_work (layout : CpuLayout) (cost : OutputCosts) (tokens : List CallerToken) :
    (cpuPayload layout cost tokens).work =
      (cpuPayload layout {cost with call := fun _ => 0} tokens).work +
        if (cpuPayloadBeforeExit layout tokens).result.isSome then cost.total else 0 := by
  cases h : (cpuPayloadBeforeExit layout tokens).result with
  | none =>
    simp [cpuPayload,Bind.bind,PCSBCSCallerParserCost.bind,h]
  | some pair =>
    rcases pair with ⟨⟨rings,columns⟩,rest⟩
    simp [cpuPayload,charged,Bind.bind,Pure.pure,PCSBCSCallerParserCost.bind,
      PCSBCSCallerParserCost.tick,PCSBCSCallerParserCost.pure,
      PCSBCSCallerParserCost.liftOption,exitClaims,OutputCosts.total,h]
    split <;> simp_all <;> omega

abbrev Schedule := List WHIRCallerShape.EventShape

def scheduleReads (n : Nat) : PCSBCSCallerParserCost.Costed Schedule :=
  ⟨List.replicate n (.absorb 24),3 * n + 2⟩

def scheduleDraws (n : Nat) : PCSBCSCallerParserCost.Costed Schedule :=
  ⟨List.replicate n (.squeeze 24),3 * n + 2⟩

def scheduleAppend (a b : PCSBCSCallerParserCost.Costed Schedule) :
    PCSBCSCallerParserCost.Costed Schedule :=
  ⟨a.value ++ b.value,a.work + b.work + 2 * a.value.length + 1⟩

def scheduleFlatMap {A : Type} (xs : List A)
    (f : A → PCSBCSCallerParserCost.Costed Schedule) : PCSBCSCallerParserCost.Costed Schedule :=
  ⟨xs.flatMap (fun a => (f a).value),xs.length + 1 +
    (xs.map (fun a => (f a).work + 2 * (f a).value.length + 1)).sum⟩

def scheduleRepeat (n : Nat) (a : PCSBCSCallerParserCost.Costed Schedule) :
    PCSBCSCallerParserCost.Costed Schedule :=
  ⟨(List.replicate n a.value).flatten,
    a.work + 3 * n + 1 + n * (2 * a.value.length + 2) + 1⟩

def gkrShape (mu : Nat) : PCSBCSCallerParserCost.Costed Schedule :=
  let odd := if mu % 2 = 1 then scheduleAppend (scheduleReads 4) (scheduleDraws 2) else ⟨[],1⟩
  let rows := scheduleFlatMap (List.range (mu / 2)) (fun i =>
    scheduleAppend
      (scheduleRepeat (mu % 2 + 2 * i) (scheduleAppend (scheduleReads 4) (scheduleDraws 1)))
      (scheduleAppend (scheduleReads 8) (scheduleDraws 3)))
  let assembled := scheduleAppend (scheduleReads 1)
    (scheduleAppend (scheduleDraws 1) (scheduleAppend odd rows))
  ⟨WHIRCallerClaims.gkrShape mu,assembled.work + 6 * (mu / 2) + 5⟩

def frameworkKeys (layout : BusLayout) : PCSBCSCallerParserCost.Costed (List (Nat × Nat)) :=
  let blocks := layout.push ++ layout.pull
  let keys := blocks.flatMap (fun block => if block.tableOwned then []
    else block.coords.filterMap (fun coord => match coord with
      | .column col => some (col,block.kappa)
      | _ => none))
  let blockWork := blocks.map (fun block => 2 + if block.tableOwned then 1 else
    1 + (block.coords.map (fun coord => match coord with | .column _ => 5 | _ => 2)).sum)
  ⟨WHIRCallerClaims.frameworkKeys layout,
    2 * layout.push.length + 1 + blocks.length + 1 + blockWork.sum + 2 * keys.length +
      blocks.length + PCSBCSCallerParserCost.eraseDupsCost 2 keys []⟩

def busShape (layout : BusLayout) : PCSBCSCallerParserCost.Costed Schedule :=
  let grinding : PCSBCSCallerParserCost.Costed Schedule :=
    if layout.grinding > 0 then ⟨[.nonce layout.grinding],4⟩ else ⟨[],2⟩
  let keys := frameworkKeys layout
  let m := PCSBCSCallerParserCost.mu layout
  let assembled := scheduleAppend grinding (scheduleAppend (scheduleDraws 5)
    (scheduleAppend (gkrShape m.value) (scheduleReads keys.value.length)))
  ⟨WHIRCallerClaims.busShape layout,assembled.work + m.work + keys.work + keys.value.length + 1⟩

def constraintsShape (layouts : List AirLayout) : PCSBCSCallerParserCost.Costed Schedule :=
  let n := (layouts.map AirLayout.tau).foldl max 0
  let front := scheduleRepeat n (scheduleAppend (scheduleReads 3) (scheduleDraws 1))
  let tables := scheduleFlatMap layouts (fun l =>
    let fields := (l.fields.map BitField.width).sum
    let a := scheduleAppend (scheduleReads (l.columns-l.publicColumns-l.fields.length))
      (scheduleReads fields)
    ⟨a.value,a.work + 5 + l.fields.length + 1 + 5 * l.fields.length + 2⟩)
  let assembled := scheduleAppend front tables
  ⟨WHIRCallerClaims.constraintsShape layouts,assembled.work + 5 * layouts.length + 2⟩

def flockProgramShape (layouts : List FlockLayout) : PCSBCSCallerParserCost.Costed Schedule :=
  let m := (layouts.map FlockLayout.logN).foldl max 0
  let rounds := (layouts.map (fun l => l.kLog-6)).foldl max 0
  let round := scheduleAppend (scheduleReads 2) (scheduleDraws 1)
  let assembled := scheduleAppend (scheduleDraws (m-13+1))
    (scheduleAppend (scheduleReads 64) (scheduleAppend (scheduleDraws 1)
      (scheduleAppend (scheduleRepeat (m-6) round)
        (scheduleAppend (scheduleReads (3*layouts.length)) (scheduleAppend (scheduleDraws 1)
          (scheduleAppend (scheduleRepeat rounds round)
            (scheduleFlatMap layouts (fun _ => scheduleAppend (scheduleReads 64) (scheduleReads 1)))))))))
  ⟨WHIRCallerClaims.flockProgramShape layouts,assembled.work + 14 * layouts.length + 10⟩

def callerShape (layout : CallerLayout) : PCSBCSCallerParserCost.Costed Schedule :=
  match layout with
  | .recursion l =>
    let assembled := scheduleAppend (scheduleReads 2) (scheduleAppend (busShape l.bus)
      (scheduleAppend (scheduleDraws 1)
        (scheduleAppend (constraintsShape (l.tables.map Prod.snd)) (flockProgramShape [l.hash]))))
    ⟨WHIRCallerClaims.callerShape layout,assembled.work + 3 * l.tables.length + 4⟩
  | .cpu l =>
    let airs := l.tables.map CpuTableLayout.air ++
      l.bus.producers.map (fun p => (⟨p.kappa,2*p.bits,p.bits,[]⟩ : AirLayout))
    let settled := scheduleFlatMap l.tables (fun t =>
      if t.settled then
        let a := scheduleReads (t.committedColumns-t.summedColumns.length)
        ⟨a.value,a.work + t.summedColumns.length + 3⟩
      else ⟨[],2⟩)
    let assembled := scheduleAppend (scheduleReads (l.tables.length+2))
      (scheduleAppend (scheduleReads 2) (scheduleAppend (busShape l.bus)
        (scheduleAppend settled (scheduleAppend (scheduleDraws 1)
          (scheduleAppend (constraintsShape airs) (flockProgramShape l.flock))))))
    ⟨WHIRCallerClaims.callerShape layout,assembled.work + 9 * l.tables.length +
      (l.tables.map (fun t => t.summedColumns.length + 1)).sum +
      7 * l.bus.producers.length + 5⟩

/-- Recursive byte encoding visits exactly the requested little-endian prefix. -/
def encodeByteWork : Nat → Nat
  | 0 => 4
  | n+1 => 6 + encodeByteWork n

def encodeScalarByteWork (i : Nat) : Nat :=
  if i < 8 then 3 + encodeByteWork i
  else if i < 16 then 6 + encodeByteWork (i-8) else 6 + encodeByteWork (i-16)

def scheduleEqWork : Schedule → Schedule → Nat
  | [], _ => 1
  | _ :: _, [] => 1
  | x :: xs, y :: ys => 5 + if x = y then scheduleEqWork xs ys else 0

def tokensShape (tokens : List CallerToken) : PCSBCSCallerParserCost.Costed Schedule :=
  ⟨WHIRCallerClaims.tokensShape tokens,1 + (tokens.map (fun token => match token with
    | .sent _ => 8 + 24 * 3 + 1 + ((List.range 24).map encodeScalarByteWork).sum +
        2 * 24 + 1 + 24 + 1
    | .draw _ => 4
    | .nonce _ _ => 4)).sum⟩

def freshCallerShape (layout : CallerLayout) (saved : Record) (cost : OutputCosts) :
    PCSBCSCallerParserCost.Costed Schedule :=
  let base := callerShape layout
  let n := rootScalarCount layout
  let frame := openingScalars saved
  ⟨AnchoredSourceFreshCaller.callerShape layout saved,
    base.work + 2 + min n base.value.length + 1 + openingWork saved + openingGetterWork saved cost + frame.length + 1 +
      3 * frame.length + 2 + 2 * (base.value.drop n).length + 1⟩

@[simp] theorem freshCallerShape_ignore_output_prices (layout : CallerLayout) (saved : Record)
    (cost : OutputCosts) (calls : Fin 4 → Nat) :
    freshCallerShape layout saved {cost with call := calls} = freshCallerShape layout saved cost := rfl
def freshInterpret (layout : CallerLayout) (saved : Record) (cost : OutputCosts)
    (tokens : List CallerToken) : PCSBCSCallerParserCost.Costed (Option AnchoredSourceCaller.Claims) :=
  let actual := tokensShape tokens
  let expected := freshCallerShape layout saved cost
  let compared := scheduleEqWork actual.value expected.value
  let front := actual.work + expected.work + compared + 1
  if actual.value ≠ expected.value then ⟨none,front⟩ else
    let parsed := freshSourceClaims layout saved cost tokens
    match parsed.result with
    | none => ⟨none,front + parsed.work + 1⟩
    | some (claims,rest) =>
      if rest.isEmpty then ⟨some claims,front + parsed.work + 3⟩
      else ⟨none,front + parsed.work + 3⟩

@[simp] theorem gkrShape_erasure (mu : Nat) :
    (gkrShape mu).value = WHIRCallerClaims.gkrShape mu := rfl
@[simp] theorem frameworkKeys_erasure (layout : BusLayout) :
    (frameworkKeys layout).value = WHIRCallerClaims.frameworkKeys layout := rfl
@[simp] theorem busShape_erasure (layout : BusLayout) :
    (busShape layout).value = WHIRCallerClaims.busShape layout := rfl
@[simp] theorem constraintsShape_erasure (layouts : List AirLayout) :
    (constraintsShape layouts).value = WHIRCallerClaims.constraintsShape layouts := rfl
@[simp] theorem flockProgramShape_erasure (layouts : List FlockLayout) :
    (flockProgramShape layouts).value = WHIRCallerClaims.flockProgramShape layouts := rfl
@[simp] theorem callerShape_erasure (layout : CallerLayout) :
    (callerShape layout).value = WHIRCallerClaims.callerShape layout := by cases layout <;> rfl
@[simp] theorem tokensShape_erasure (tokens : List CallerToken) :
    (tokensShape tokens).value = WHIRCallerClaims.tokensShape tokens := rfl
@[simp] theorem freshCallerShape_erasure (layout : CallerLayout) (saved : Record) (cost : OutputCosts) :
    (freshCallerShape layout saved cost).value = AnchoredSourceFreshCaller.callerShape layout saved := rfl

theorem freshInterpret_erasure (layout : CallerLayout) (saved : Record) (cost : OutputCosts)
    (tokens : List CallerToken) : (freshInterpret layout saved cost tokens).value =
      AnchoredSourceFreshCaller.interpret layout saved tokens := by
  have erased := congrFun (freshSourceClaims_erasure layout saved cost) tokens
  change (freshSourceClaims layout saved cost tokens).result = _ at erased
  by_cases h : WHIRCallerClaims.tokensShape tokens ≠ AnchoredSourceFreshCaller.callerShape layout saved
  · simp [freshInterpret,AnchoredSourceFreshCaller.interpret,h]
  · cases hr : (freshSourceClaims layout saved cost tokens).result with
    | none => simp [freshInterpret,AnchoredSourceFreshCaller.interpret,h,← erased,hr]
    | some pair =>
      rcases pair with ⟨claims,rest⟩
      cases rest <;> simp [freshInterpret,AnchoredSourceFreshCaller.interpret,h,← erased,hr]

theorem scalarEqWork_le (x y : E) : scalarEqWork x y ≤ 12 := by
  simp only [scalarEqWork]; split <;> (try split) <;> omega

theorem scalarListEqWork_le (xs ys : List E) :
    scalarListEqWork xs ys ≤ 14 * ys.length + 1 := by
  induction ys generalizing xs with
  | nil => cases xs <;> simp [scalarListEqWork]
  | cons y ys ih =>
    cases xs with
    | nil => simp [scalarListEqWork]
    | cons x xs =>
      have h := scalarEqWork_le x y
      have ht := ih xs
      simp only [scalarListEqWork,List.length_cons]
      split <;> omega

theorem scheduleEqWork_le (xs ys : Schedule) :
    scheduleEqWork xs ys ≤ 5 * ys.length + 1 := by
  induction ys generalizing xs with
  | nil => cases xs <;> simp [scheduleEqWork]
  | cons y ys ih =>
    cases xs with
    | nil => simp [scheduleEqWork]
    | cons x xs =>
      have ht := ih xs
      simp only [scheduleEqWork,List.length_cons]
      split <;> omega

theorem scalarByteWork_sum :
    ((List.range 24).map encodeScalarByteWork).sum = 720 := by decide

theorem tokensShape_work_le (tokens : List CallerToken) :
    (tokensShape tokens).work ≤ 875 * tokens.length + 1 := by
  induction tokens with
  | nil => simp [tokensShape]
  | cons token rest ih =>
    cases token <;> simp only [tokensShape,List.map_cons,List.sum_cons,List.length_cons,
      scalarByteWork_sum] at * <;> omega

theorem binding_work_le (record : Record) (cost : OutputCosts) (tokens : List CallerToken) :
    (binding record cost tokens).work ≤
      2 * openingWork record + 2 * openingGetterWork record cost + 24 * (openingScalars record).length + 7 := by
  have hr := PCSBCSCallerParserCost.readScalars_work_le (openingScalars record).length tokens
  simp only [binding,Bind.bind,PCSBCSCallerParserCost.bind,PCSBCSCallerParserCost.tick]
  cases h : (PCSBCSCallerParserCost.readScalars (openingScalars record).length tokens).result with
  | none => dsimp only; omega
  | some pair =>
    rcases pair with ⟨frame,rest⟩
    have he := scalarListEqWork_le frame (openingScalars record)
    change _ ≤ _
    simp only [PCSBCSCallerParserCost.check]
    split <;> dsimp only <;> omega

theorem binding_polynomial (record : Record) (cost : OutputCosts) (tokens : List CallerToken) :
    (binding record cost tokens).work ≤
      108 * (record.context.pendingBytes + record.point.length + 1) + 1447 + 2 * openingGetterWork record cost := by
  have hb := binding_work_le record cost tokens
  have ho := openingWork_polynomial record
  have hn := openingScalars_length record
  have hd : (record.context.pendingBytes + 23) / 24 ≤ record.context.pendingBytes + 1 := by omega
  omega

theorem freshInterpret_work_le (layout : CallerLayout) (saved : Record) (cost : OutputCosts)
    (tokens : List CallerToken) :
    (freshInterpret layout saved cost tokens).work ≤
      (tokensShape tokens).work + (freshCallerShape layout saved cost).work +
        scheduleEqWork (tokensShape tokens).value (freshCallerShape layout saved cost).value +
        (freshSourceClaims layout saved cost tokens).work + 4 := by
  by_cases shapeMismatch : WHIRCallerClaims.tokensShape tokens ≠
      AnchoredSourceFreshCaller.callerShape layout saved
  · simp [freshInterpret,shapeMismatch]
    omega
  · cases parsed : (freshSourceClaims layout saved cost tokens).result with
    | none =>
      simp [freshInterpret,shapeMismatch,parsed]
      omega
    | some pair =>
      rcases pair with ⟨claims,rest⟩
      cases remaining : rest.isEmpty <;>
        simp [freshInterpret,shapeMismatch,parsed,remaining]
      all_goals omega


theorem columnsWork_le (bus : List ColumnClaim) (paired : List (Nat × TableClaims)) (evalCap : Nat)
    (cap : ∀ p ∈ paired, p.2.evals.length ≤ evalCap) :
    columnsWork bus paired ≤ 2 * bus.length + paired.length * (8 * evalCap + 4) + 2 := by
  have hs := sumMap_le paired (fun (base,claims) =>
    (PCSBCSCallerParserCost.tableColumns base claims).work + 2 * claims.evals.length + 1)
    (8 * evalCap + 3) (by
      intro p hp
      have hc := cap p hp
      rcases p with ⟨base,claims⟩
      dsimp only at hc ⊢
      simp only [PCSBCSCallerParserCost.tableColumns_work]
      omega)
  simp only [columnsWork]
  nlinarith

theorem freshCallerShape_work_le (layout : CallerLayout) (saved : Record) (cost : OutputCosts) :
    (freshCallerShape layout saved cost).work ≤
      (callerShape layout).work + openingWork saved + openingGetterWork saved cost +
        3 * (callerShape layout).value.length + 4 * (openingScalars saved).length + 7 := by
  have hm : min (rootScalarCount layout) (callerShape layout).value.length ≤
      (callerShape layout).value.length := Nat.min_le_right _ _
  have hd : ((callerShape layout).value.drop (rootScalarCount layout)).length ≤
      (callerShape layout).value.length := by simp
  simp only [freshCallerShape]
  omega

theorem freshCallerShape_length_le (layout : CallerLayout) (saved : Record) (cost : OutputCosts) :
    (freshCallerShape layout saved cost).value.length ≤
      (callerShape layout).value.length + (openingScalars saved).length := by
  simp only [freshCallerShape_erasure,callerShape_erasure,AnchoredSourceFreshCaller.callerShape,
    AnchoredSourceCaller.reads,List.length_append,List.length_replicate,List.length_drop]
  omega

theorem freshInterpret_compositional_bound (layout : CallerLayout) (saved : Record)
    (cost : OutputCosts) (tokens : List CallerToken) :
    (freshInterpret layout saved cost tokens).work ≤
      875 * tokens.length + (callerShape layout).work + openingWork saved + openingGetterWork saved cost +
        8 * (callerShape layout).value.length + 9 * (openingScalars saved).length +
        (freshSourceClaims layout saved cost tokens).work + 13 := by
  have hi := freshInterpret_work_le layout saved cost tokens
  have ht := tokensShape_work_le tokens
  have hc := freshCallerShape_work_le layout saved cost
  have hl := freshCallerShape_length_le layout saved cost
  have he := scheduleEqWork_le (tokensShape tokens).value (freshCallerShape layout saved cost).value
  omega

theorem freshInterpret_exact (layout : CallerLayout) (saved : Record) (cost : OutputCosts)
    (tokens : List CallerToken) (claims : AnchoredSourceCaller.Claims) :
    (freshInterpret layout saved cost tokens).value = some claims ↔
      WHIRCallerClaims.tokensShape tokens = AnchoredSourceFreshCaller.callerShape layout saved ∧
        (freshSourceClaims layout saved cost tokens).result = some (claims,[]) := by
  rw [freshInterpret_erasure,AnchoredSourceFreshCaller.interpret_exact]
  change (_ ∧ _) ↔ (_ ∧ PCSBCSCallerParserCost.erase (freshSourceClaims layout saved cost) tokens = _)
  rw [freshSourceClaims_erasure]

theorem binding_exact (record : Record) (cost : OutputCosts) (suffix : List CallerToken) :
    (binding record cost ((openingScalars record).map CallerToken.sent ++ suffix)).result = some ((),suffix) := by
  change PCSBCSCallerParserCost.erase (binding record cost) _ = _
  rw [binding_erasure]
  exact AnchoredSourceCaller.binding_exact record suffix

theorem binding_frame_rejected (record : Record) (cost : OutputCosts) (frame : List E) (suffix : List CallerToken)
    (length : frame.length = (openingScalars record).length) (changed : frame ≠ openingScalars record) :
    (binding record cost (frame.map CallerToken.sent ++ suffix)).result = none := by
  change PCSBCSCallerParserCost.erase (binding record cost) _ = _
  rw [binding_erasure]
  exact AnchoredSourceFreshCaller.binding_frame_rejected record frame suffix length changed

/-- Closed geometry avoids evaluating `openingScalars` solely to obtain its
length while computing a trace. -/
def freshShapeForTrace (layout : CallerLayout) (saved : Record) : Schedule :=
  (WHIRCallerClaims.callerShape layout).drop (rootScalarCount layout) ++
    AnchoredSourceCaller.reads (10 + saved.point.length + (saved.context.pendingBytes+23)/24)

theorem freshShapeForTrace_erasure (layout : CallerLayout) (saved : Record) :
    freshShapeForTrace layout saved = AnchoredSourceFreshCaller.callerShape layout saved := by
  simp [freshShapeForTrace,AnchoredSourceFreshCaller.callerShape,openingScalars_length]
def freshOutputGetterTrace (layout : CallerLayout) (tokens : List CallerToken) : List (Fin 4) :=
  match layout with
  | .cpu l => outputGetterTrace l tokens
  | .recursion _ => []

def freshInterpretOutputGetterTrace (layout : CallerLayout) (saved : Record)
    (tokens : List CallerToken) : List (Fin 4) :=
  if WHIRCallerClaims.tokensShape tokens = freshShapeForTrace layout saved
    then freshOutputGetterTrace layout tokens else []

theorem freshOutputGetterTrace_length_le (layout : CallerLayout) (tokens : List CallerToken) :
    (freshOutputGetterTrace layout tokens).length ≤ 4 := by
  cases layout with
  | recursion _ => simp [freshOutputGetterTrace]
  | cpu l =>
    simp only [freshOutputGetterTrace,outputGetterTrace_length]
    split <;> omega

theorem freshInterpretOutputGetterTrace_length_le (layout : CallerLayout) (saved : Record)
    (tokens : List CallerToken) : (freshInterpretOutputGetterTrace layout saved tokens).length ≤ 4 := by
  unfold freshInterpretOutputGetterTrace
  split
  · exact freshOutputGetterTrace_length_le layout tokens
  · simp

theorem freshSourceClaims_output_work (layout : CpuLayout) (saved : Record) (cost : OutputCosts)
    (tokens : List CallerToken) :
    (freshSourceClaims (.cpu layout) saved cost tokens).work =
      (freshSourceClaims (.cpu layout) saved {cost with call := fun _ => 0} tokens).work +
        if (cpuPayloadBeforeExit layout tokens).result.isSome then cost.total else 0 := by
  have hw := cpuPayload_output_work layout cost tokens
  have hr : (cpuPayload layout cost tokens).result = (cpuPayload layout {cost with call := fun _ => 0} tokens).result := by
    change PCSBCSCallerParserCost.erase (cpuPayload layout cost) tokens =
      PCSBCSCallerParserCost.erase (cpuPayload layout {cost with call := fun _ => 0}) tokens
    rw [cpuPayload_erasure,cpuPayload_erasure]
  simp only [freshSourceClaims,payload,Bind.bind,Pure.pure,PCSBCSCallerParserCost.bind]
  rw [hr]
  cases h : (cpuPayload layout {cost with call := fun _ => 0} tokens).result with
  | none => omega
  | some pair =>
    rcases pair with ⟨⟨families,points⟩,rest⟩
    simp only [binding_ignore_output_prices]
    omega

theorem freshSourceClaims_output_bound (layout : CallerLayout) (saved : Record) (cost : OutputCosts)
    (tokens : List CallerToken) :
    (freshSourceClaims layout saved cost tokens).work ≤
      (freshSourceClaims layout saved {cost with call := fun _ => 0} tokens).work + cost.total := by
  cases layout with
  | recursion l => simp [freshSourceClaims,payload]
  | cpu l =>
    rw [freshSourceClaims_output_work]
    split <;> omega

theorem shapeValidWork_le (shape : Shape) :
    shapeValidWork shape ≤ 3 * shape.logBatch + 24 := by
  unfold shapeValidWork
  repeat' first | omega | split

theorem headerWork_le (shape : Shape) (header : List E) : headerWork shape header ≤ 54 := by
  unfold headerWork scalarEqWork
  repeat' first | omega | split

theorem wordsWork_le (layout : CallerLayout) (dimensionCap : Nat)
    (cap : ∀ p ∈ (callerPlacements layout).toList, ∀ o d, p = .committed o d → d ≤ dimensionCap) :
    wordsWork layout ≤ (3 * dimensionCap + 5) * (callerPlacements layout).size + 3 := by
  have hs := sumMap_le (callerPlacements layout).toList
    (fun p => match p with | .committed _ d => 3 * d + 5 | _ => 2)
    (3 * dimensionCap + 5) (by
      intro p hp
      cases p with
      | committed o d =>
        have hd := cap _ hp o d rfl
        dsimp only
        omega
      | port o slot stride => dsimp only; omega
      | sliced => dsimp only; omega)
  simp only [Array.length_toList] at hs
  simp only [wordsWork]
  omega

theorem settledClaims_success_geometry (tables : List CpuTableLayout) (point : List E)
    (tokens rest : List CallerToken) (claims : List TableClaims)
    (success : (settledClaims tables point tokens).result = some (claims,rest)) :
    List.Forall₂ WHIRCallerGeometry.SettledGeometry (tables.filter CpuTableLayout.settled) claims := by
  have erased := congrFun (settledClaims_erasure tables point) tokens
  change (settledClaims tables point tokens).result = _ at erased
  exact WHIRCallerGeometry.settledClaims_geometry tables point tokens claims rest (erased.symm.trans success)

theorem settledClaims_success_length (tables : List CpuTableLayout) (point : List E)
    (tokens rest : List CallerToken) (claims : List TableClaims)
    (success : (settledClaims tables point tokens).result = some (claims,rest)) :
    claims.length = (tables.filter CpuTableLayout.settled).length :=
  (settledClaims_success_geometry tables point tokens rest claims success).length_eq.symm

/-- Proof-side access trace. Its construction does not call an opaque accessor. -/
structure GetterTrace where
  outputs : List (Fin 4)
  pendingWords : List (Fin 8)
  rootBytes : List (Fin 32)
  contextBytes : List (Fin 32)

def GetterTrace.empty : GetterTrace := ⟨[],[],[],[]⟩

def GetterTrace.append (a b : GetterTrace) : GetterTrace :=
  ⟨a.outputs ++ b.outputs,a.pendingWords ++ b.pendingWords,
    a.rootBytes ++ b.rootBytes,a.contextBytes ++ b.contextBytes⟩

def GetterTrace.price (trace : GetterTrace) (cost : OutputCosts) : Nat :=
  (trace.outputs.map cost.call).sum + (trace.pendingWords.map cost.pending).sum +
    (trace.rootBytes.map cost.rootByte).sum + (trace.contextBytes.map cost.contextByte).sum

@[simp] theorem GetterTrace.price_append (a b : GetterTrace) (cost : OutputCosts) :
    (a.append b).price cost = a.price cost + b.price cost := by
  simp only [GetterTrace.price,GetterTrace.append,List.map_append,List.sum_append]
  omega

@[simp] theorem GetterTrace.price_zero (trace : GetterTrace) :
    trace.price OutputCosts.zero = 0 := by
  simp [GetterTrace.price,OutputCosts.zero,List.sum_replicate]

def openingGetterTrace (record : Record) : GetterTrace :=
  ⟨[],pendingGetterTrace record.context,digestGetterTrace,digestGetterTrace⟩

def bindingGetterTrace (record : Record) (tokens : List CallerToken) : GetterTrace :=
  let frameLength := 10 + record.point.length + (record.context.pendingBytes+23)/24
  let first := openingGetterTrace record
  if (PCSBCSCallerParserCost.readScalars frameLength tokens).result.isSome
    then first.append first else first

private theorem mapM_isSome_all {A B : Type} (xs : List A) (f : A → Option B) :
    (xs.mapM f).isSome = xs.all (fun x => (f x).isSome) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases hx : f x <;> cases ht : xs.mapM f <;> simp_all [List.mapM_cons,List.all]

theorem placeClaims_isSome (placements : Array Placement) (claims : List ColumnClaim) :
    (PCSBCSCallerParserCost.placeClaims placements claims).value.isSome =
      claims.all (fun c => decide (c.column < placements.size)) := by
  rw [PCSBCSCallerParserCost.placeClaims_erasure]
  unfold WHIRCallerClaims.placeClaims
  let locate := fun c : ColumnClaim => do
    let p ← placements[c.column]?
    pure (WHIRCallerClaims.placeClaim p c)
  have hm := mapM_isSome_all claims locate
  have hl : ∀ c, (locate c).isSome = decide (c.column < placements.size) := by
    intro c
    have hb := isSome_getElem? placements c.column
    cases h : placements[c.column]? <;> simp [locate,h] at * <;> assumption
  simp only [hl] at hm
  cases h : claims.mapM locate with
  | none =>
    simp only [h,Option.isSome_none] at hm
    rw [← hm]
    rfl
  | some located =>
    simp only [h,Option.isSome_some] at hm
    rw [← hm]
    rfl

/-- CPU completion is decided from actual parsed column indices. The five exit
claims all use the public final-register column; their opaque values cannot
change whether placement rejects. No output getter is executed by this scanner. -/
def payloadPendingCursor (layout : CallerLayout) (tokens : List CallerToken) : Option (List CallerToken) :=
  match layout with
  | .recursion l => (recPayload l tokens).result.map Prod.snd
  | .cpu l => (cpuPayloadBeforeExit l tokens).result.bind (fun ((_,columns),rest) =>
      if columns.all (fun c => decide (c.column < l.placements.size)) &&
          decide (l.finalRegisterColumn < l.placements.size)
      then some rest else none)

theorem payloadPendingCursor_erasure (layout : CallerLayout) (cost : OutputCosts)
    (tokens : List CallerToken) :
    payloadPendingCursor layout tokens = (payload layout cost tokens).result.map Prod.snd := by
  cases layout with
  | recursion l => rfl
  | cpu l =>
    cases h : (cpuPayloadBeforeExit l tokens).result with
    | none => simp [payloadPendingCursor,payload,cpuPayload,Bind.bind,PCSBCSCallerParserCost.bind,h]
    | some pair =>
      rcases pair with ⟨⟨rings,columns⟩,rest⟩
      have hp := placeClaims_isSome l.placements
        (columns ++ WHIRCallerClaims.exitClaims l.finalRegisterColumn l.output)
      have hexit : (WHIRCallerClaims.exitClaims l.finalRegisterColumn l.output).all
          (fun c => decide (c.column < l.placements.size)) =
          decide (l.finalRegisterColumn < l.placements.size) := by
        simp [WHIRCallerClaims.exitClaims,List.ofFn_succ]
      simp only [List.all_append,hexit] at hp
      simp only [payloadPendingCursor,payload,cpuPayload,charged,Bind.bind,Pure.pure,
        PCSBCSCallerParserCost.bind,PCSBCSCallerParserCost.tick,PCSBCSCallerParserCost.pure,
        PCSBCSCallerParserCost.liftOption,exitClaims,h]
      cases placed : (PCSBCSCallerParserCost.placeClaims l.placements
          (columns ++ WHIRCallerClaims.exitClaims l.finalRegisterColumn l.output)).value <;>
        simp_all

def freshSourceClaimsGetterTrace (layout : CallerLayout) (saved : Record)
    (tokens : List CallerToken) : GetterTrace :=
  let outputs : GetterTrace := ⟨freshOutputGetterTrace layout tokens,[],[],[]⟩
  match payloadPendingCursor layout tokens with
  | none => outputs
  | some rest => outputs.append (bindingGetterTrace saved rest)


def freshInterpretGetterTrace (layout : CallerLayout) (saved : Record)
    (tokens : List CallerToken) : GetterTrace :=
  let shape := openingGetterTrace saved
  if WHIRCallerClaims.tokensShape tokens = freshShapeForTrace layout saved
    then shape.append (freshSourceClaimsGetterTrace layout saved tokens)
    else shape

theorem digestGetterTrace_length : digestGetterTrace.length = 64 := by
  simp [digestGetterTrace]

theorem openingGetterTrace_price (record : Record) (cost : OutputCosts) :
    (openingGetterTrace record).price cost = openingGetterWork record cost := by
  simp [openingGetterTrace,GetterTrace.price,openingGetterWork,pendingGetterWork]

theorem binding_getter_work (record : Record) (cost : OutputCosts)
    (tokens : List CallerToken) :
    (binding record cost tokens).work = (binding record OutputCosts.zero tokens).work +
      (bindingGetterTrace record tokens).price cost := by
  have hz : openingGetterWork record OutputCosts.zero = 0 := by
    rw [← openingGetterTrace_price]
    simp
  have hn := openingScalars_length record
  cases h : (PCSBCSCallerParserCost.readScalars (openingScalars record).length tokens).result with
  | none =>
    simp [binding,Bind.bind,PCSBCSCallerParserCost.bind,PCSBCSCallerParserCost.tick,
      h,hz,bindingGetterTrace,← hn,openingGetterTrace_price]
    omega
  | some pair =>
    rcases pair with ⟨frame,rest⟩
    simp [binding,Bind.bind,PCSBCSCallerParserCost.bind,PCSBCSCallerParserCost.tick,
      PCSBCSCallerParserCost.check,h,hz,bindingGetterTrace,
      ← hn,openingGetterTrace_price,GetterTrace.price_append]
    split <;> simp <;> omega

theorem pendingPackGetterTrace_length_le (context : Context) (i : Nat) :
    (pendingPackGetterTrace context i).length ≤ 3 := by
  simp only [pendingPackGetterTrace,List.length_append]
  split <;> split <;> simp

theorem pendingGetterTrace_length_le (context : Context) :
    (pendingGetterTrace context).length ≤ 3 * ((context.pendingBytes+23)/24) := by
  have hs := sumMap_le (List.range ((context.pendingBytes+23)/24))
    (fun i => (pendingPackGetterTrace context i).length) 3
    (fun i _ => pendingPackGetterTrace_length_le context i)
  simpa [pendingGetterTrace,List.length_flatMap] using hs

theorem bindingGetterTrace_bound (record : Record) (tokens : List CallerToken) :
    (bindingGetterTrace record tokens).outputs = [] ∧
      (bindingGetterTrace record tokens).pendingWords.length ≤ 2 * (pendingGetterTrace record.context).length ∧
      (bindingGetterTrace record tokens).rootBytes.length ≤ 128 ∧
      (bindingGetterTrace record tokens).contextBytes.length ≤ 128 := by
  unfold bindingGetterTrace
  dsimp only
  split <;> simp [openingGetterTrace,GetterTrace.append,digestGetterTrace] <;> omega

theorem freshSourceClaimsGetterTrace_bound (layout : CallerLayout) (saved : Record)
    (tokens : List CallerToken) :
    (freshSourceClaimsGetterTrace layout saved tokens).outputs.length ≤ 4 ∧
      (freshSourceClaimsGetterTrace layout saved tokens).pendingWords.length ≤
        2 * (pendingGetterTrace saved.context).length ∧
      (freshSourceClaimsGetterTrace layout saved tokens).rootBytes.length ≤ 128 ∧
      (freshSourceClaimsGetterTrace layout saved tokens).contextBytes.length ≤ 128 := by
  have ho := freshOutputGetterTrace_length_le layout tokens
  unfold freshSourceClaimsGetterTrace
  cases h : payloadPendingCursor layout tokens with
  | none =>
    dsimp only
    simp only [List.length_nil]
    exact ⟨ho,by omega,by omega,by omega⟩
  | some rest =>
    have hb := bindingGetterTrace_bound saved rest
    simp only [GetterTrace.append,List.length_append]
    simpa [hb.1] using And.intro ho hb.2

theorem freshInterpretGetterTrace_bound (layout : CallerLayout) (saved : Record)
    (tokens : List CallerToken) :
    (freshInterpretGetterTrace layout saved tokens).outputs.length ≤ 4 ∧
      (freshInterpretGetterTrace layout saved tokens).pendingWords.length ≤
        3 * (pendingGetterTrace saved.context).length ∧
      (freshInterpretGetterTrace layout saved tokens).rootBytes.length ≤ 192 ∧
      (freshInterpretGetterTrace layout saved tokens).contextBytes.length ≤ 192 := by
  have hb := freshSourceClaimsGetterTrace_bound layout saved tokens
  unfold freshInterpretGetterTrace
  split
  · simp only [GetterTrace.append,openingGetterTrace,List.length_append,
      List.length_nil,Nat.zero_add,digestGetterTrace_length]
    omega
  · simp [openingGetterTrace,digestGetterTrace]
    omega

/-- A polynomial callback component using the caller's explicit per-access caps.
The exact reached indices remain available in `freshInterpretGetterTrace`. -/
theorem freshInterpretGetterTrace_price_le (layout : CallerLayout) (saved : Record)
    (tokens : List CallerToken) (cost : OutputCosts)
    (outputCap pendingCap rootCap contextCap : Nat)
    (outputs : ∀ i, cost.call i ≤ outputCap)
    (pending : ∀ i, cost.pending i ≤ pendingCap)
    (root : ∀ i, cost.rootByte i ≤ rootCap)
    (context : ∀ i, cost.contextByte i ≤ contextCap) :
    (freshInterpretGetterTrace layout saved tokens).price cost ≤
      4 * outputCap + 9 * ((saved.context.pendingBytes+23)/24) * pendingCap +
        192 * rootCap + 192 * contextCap := by
  let t := freshInterpretGetterTrace layout saved tokens
  have ht := freshInterpretGetterTrace_bound layout saved tokens
  have hp := pendingGetterTrace_length_le saved.context
  have ho := sumMap_le t.outputs cost.call outputCap (fun i _ => outputs i)
  have hw := sumMap_le t.pendingWords cost.pending pendingCap (fun i _ => pending i)
  have hr := sumMap_le t.rootBytes cost.rootByte rootCap (fun i _ => root i)
  have hc := sumMap_le t.contextBytes cost.contextByte contextCap (fun i _ => context i)
  change _ + _ + _ + _ ≤ _
  dsimp only [t] at ho hw hr hc
  have hn : (freshInterpretGetterTrace layout saved tokens).pendingWords.length ≤
      9 * ((saved.context.pendingBytes+23)/24) := by omega
  have a := Nat.mul_le_mul_left outputCap ht.1
  have b := Nat.mul_le_mul_left pendingCap hn
  have c := Nat.mul_le_mul_left rootCap ht.2.2.1
  have d := Nat.mul_le_mul_left contextCap ht.2.2.2
  nlinarith



#print axioms freshSourceClaims_output_work

#print axioms binding_polynomial
#print axioms cpuPayload_output_work
#print axioms freshInterpret_erasure

#print axioms recPayload_erasure
#print axioms cpuPayload_erasure
#print axioms sourceClaims_erasure
#print axioms freshSourceClaims_erasure
#print axioms dupsWork_le

end Whir.PCSBCSCallerPayloadCost
