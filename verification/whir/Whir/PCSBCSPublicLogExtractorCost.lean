import Whir.PCSBCSPublicLogExtractor
import Whir.PCSRoundByRoundSourceDecoderCost
import Whir.PCSBCSCoordinateCodecCost
import Whir.PCSBCSPublicLogParserCost
import Whir.PCSBCSSourceReferencePolynomialBound
import Whir.PCSBCSSourceSavedRecordDecoderCost
import Whir.PCSBCSRecoveredSourceVolume

/-! PCS-only resource accounting. The predecessor relation is a LINEAR chain;
its fuel is the physical prefix length, not a recursively expanded construction
ledger. Counts below distinguish fixed-size comparisons, parser reservations,
public shape-lookup invocations and immutable retained words. Charges are
not wall-clock time or compiler instructions. The literal saved-record decoder
pays its checked physical-volume polynomial; no caller metadata is supplied. No Fiat-Shamir endpoint or concrete-hash security bound is asserted. -/
set_option autoImplicit false
set_option maxRecDepth 10000
namespace Whir.PCSBCSPublicLogExtractorCost
open Concrete Protocol FiatShamirGame DuplexFraming DuplexRefinement DuplexModeGame
open DuplexPublicSimulator PCSBCSMerkleRootCache PCSBCSSourceRootReferences
open SupportedCandidateExtraction
attribute [local irreducible] ParameterBounds.config

local instance : DecidableEq Terminal := by
  intro a b
  cases a <;> cases b <;> simp <;> infer_instance

local instance : DecidableEq Coordinate := by
  intro a b
  cases a
  cases b
  simp only [Coordinate.mk.injEq]
  infer_instance

/-- One predicate evaluation per visited record, with early stopping. -/
def findCount {α : Type} (test : α → Bool) : List α → Option α × Nat
  | [] => (none,0)
  | x::xs => if test x then (some x,1) else
      let later := findCount test xs
      (later.1,later.2+1)

theorem findCount_value {α : Type} (test : α → Bool) (xs : List α) :
    (findCount test xs).1 = xs.find? test := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [findCount,List.find?_cons]; split <;> simp_all

theorem findCount_bound {α : Type} (test : α → Bool) (xs : List α) :
    (findCount test xs).2 ≤ xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [findCount,List.length_cons]; split <;> simp only [] <;> omega

def lookupCount (log : PublicLog) (input : Node) : Option Digest32 × Nat :=
  let found := findCount (fun e => decide (e.1 = input)) log
  (found.1.map Prod.snd,found.2)

def predecessorCount (log : PublicLog) (cv : Digest32) : Option Node × Nat :=
  let found := findCount (fun e => decide (e.2 = cv)) log
  (found.1.map Prod.fst,found.2)

theorem lookupCount_value (log : PublicLog) (input : Node) :
    (lookupCount log input).1 = lookup log input := by
  simp [lookupCount,lookup,findCount_value]

theorem predecessorCount_value (log : PublicLog) (cv : Digest32) :
    (predecessorCount log cv).1 = predecessor log cv := by
  simp [predecessorCount,predecessor,findCount_value]

/-- Each predecessor comparison is expanded into 512 fixed-width byte/index
operations. Seed/internal role checks reserve 1024 such operations. There is
exactly one recursive child, never a binary reconstruction ledger. -/
def extendCount (log : PublicLog) : Nat → Digest32 → Option (List Node) × Nat
  | 0,_ => (none,1)
  | fuel+1,cv =>
    let previous := predecessorCount log cv
    match previous.1 with
    | none => (none,512*previous.2+1024)
    | some n =>
      if isSeed n then (some [n],512*previous.2+1024)
      else if isInternal n then
        let rest := extendCount log fuel n.cv
        (rest.1.map (n::·),512*previous.2+1024+rest.2)
      else (none,512*previous.2+1024)

theorem extendCount_value (log : PublicLog) (fuel : Nat) (cv : Digest32) :
    (extendCount log fuel cv).1 = extend log fuel cv := by
  induction fuel generalizing cv with
  | zero => rfl
  | succ fuel ih =>
    simp only [extendCount,extend]
    rw [predecessorCount_value]
    cases h : predecessor log cv with
    | none => rfl
    | some n =>
      dsimp only
      split
      · rfl
      · split <;> simp [ih]

theorem extendCount_bound (log : PublicLog) (fuel : Nat) (cv : Digest32) :
    (extendCount log fuel cv).2 ≤ fuel*(512*log.length+1024)+1 := by
  induction fuel generalizing cv with
  | zero => simp [extendCount]
  | succ fuel ih =>
    have scan := findCount_bound (fun e : Node × Digest32 => decide (e.2 = cv)) log
    change (predecessorCount log cv).2 ≤ log.length at scan
    simp only [extendCount]
    cases (predecessorCount log cv).1 with
    | none => simp only []; nlinarith
    | some n =>
      dsimp only
      split
      · simp only []; nlinarith
      · split
        · have later := ih n.cv; simp only []; nlinarith
        · nlinarith

def recognizedCount (log : PublicLog) (input : Node) : Option (List Node) × Nat :=
  if isTerminal input then
    let body := extendCount log log.length input.cv
    (body.1.map (input::·),body.2+log.length+1024)
  else (none,1)

theorem recognizedCount_value (log : PublicLog) (input : Node) :
    (recognizedCount log input).1 = recognized log input := by
  simp only [recognizedCount,recognized]; split <;> simp [extendCount_value]

/-- Mapping both payload/template lists, their length guards, and short-list
construction are reserved linearly in the actual recognized length. -/
def privateKeyCount (Q : Nat) (log : PublicLog) (input : Node) : Option (RawKey Q) × Nat :=
  let repeated := lookupCount log input
  if repeated.1.isSome then (none,1024*repeated.2+1) else
  let tree := recognizedCount log input
  match tree.1 with
  | none => (none,1024*repeated.2+tree.2+1)
  | some ns =>
    (if h : ns.length ≤ Q then
      some (restrictKey Q ⟨ns.map payload,ns.map (fun n => (n.tweak,n.last))⟩
        (by simpa using h) (by simpa using h)) else none,
      1024*repeated.2+tree.2+8*ns.length+4)

theorem privateKeyCount_value (Q : Nat) (log : PublicLog) (input : Node) :
    (privateKeyCount Q log input).1 = privateKey Q log input := by
  simp only [privateKeyCount,privateKey,lookupCount_value,recognizedCount_value]
  split
  · rfl
  · cases recognized log input <;> rfl

def recognitionPolynomial (Q : Nat) : Nat := Q*(512*Q+1024)+1040*Q+2048

theorem privateKeyCount_bound (Q : Nat) (log : PublicLog) (input : Node) :
    (privateKeyCount Q log input).2 ≤ recognitionPolynomial log.length := by
  have scan := findCount_bound (fun e : Node × Digest32 => decide (e.1 = input)) log
  change (lookupCount log input).2 ≤ log.length at scan
  have chain := extendCount_bound log log.length input.cv
  have roles : (recognizedCount log input).2 ≤ log.length*(512*log.length+1024)+log.length+1025 := by
    unfold recognizedCount
    split
    · simp only []; omega
    · simp only []; omega
  unfold privateKeyCount
  dsimp only
  split
  · simp only []; unfold recognitionPolynomial; omega
  · cases h : (recognizedCount log input).1 with
    | none => simp only []; unfold recognitionPolynomial; omega
    | some ns =>
      have size := (recognized_sound (recognizedCount_value log input ▸ h)).2
      simp only []
      unfold recognitionPolynomial
      omega

/-- Proven bound for concrete byte parsing, plan reconstruction and whole-key
equality, plus materialization of both bounded raw-key lists. -/
def codecReservation (Q : Nat) : Nat :=
  PCSBCSCoordinateCodecCost.extractedPolynomial (Q+1)+16*(Q+1)+2

def recoverCount (Q : Nat) (iv : Digest32) (log : PublicLog) (input : Node) :
    Option Coordinate × Nat :=
  let raw := privateKeyCount Q log input
  match raw.1 with
  | none => (none,raw.2)
  | some key =>
    let decoded := PCSBCSCoordinateCodecCost.decodeExtractedCount iv (expandKey key)
    (decoded.1,raw.2+decoded.2+8*(key.1.1.val+key.2.1.val)+2)

theorem recoverCount_value (Q : Nat) (iv : Digest32) (log : PublicLog) (input : Node) :
    (recoverCount Q iv log input).1 = PCSBCSSourceCoordinateDecoder.recover Q iv log input := by
  simp only [recoverCount,privateKeyCount_value,PCSBCSSourceCoordinateDecoder.recover]
  cases privateKey Q log input <;>
    simp only [PCSBCSCoordinateCodecCost.decodeExtractedCount_value,
      Option.bind_none,Option.bind_some,PCSBCSSourceCoordinateDecoder.decode]

theorem recoverCount_bound (Q : Nat) (iv : Digest32) (log : PublicLog) (input : Node) :
    (recoverCount Q iv log input).2 ≤
      recognitionPolynomial log.length + codecReservation log.length := by
  have rawBound := privateKeyCount_bound Q log input
  unfold recoverCount
  dsimp only
  cases h : (privateKeyCount Q log input).1 with
  | none => unfold codecReservation; dsimp only; omega
  | some key =>
    have sizes := privateKey_lengths_log (privateKeyCount_value Q log input ▸ h)
    have decodeBound := PCSBCSCoordinateCodecCost.decodeExtractedCount_bound iv (expandKey key)
      (log.length+1) (by simpa [expandKey,expandShort] using sizes.1)
      (by simpa [expandKey,expandShort] using sizes.2)
    unfold codecReservation
    dsimp only
    omega

theorem recognitionPolynomial_mono {a b : Nat} (cap : a ≤ b) :
    recognitionPolynomial a ≤ recognitionPolynomial b := by
  unfold recognitionPolynomial
  nlinarith [Nat.mul_le_mul cap cap]

theorem codecReservation_mono {a b : Nat} (cap : a ≤ b) :
    codecReservation a ≤ codecReservation b := by
  have shifted : a+3 ≤ b+3 := Nat.add_le_add_right cap 3
  unfold codecReservation PCSBCSCoordinateCodecCost.extractedPolynomial
  nlinarith [Nat.mul_le_mul shifted shifted]

/-- Physical Q, not the recursive source-construction path ledger: at most Q
predecessor stages, each scanning at most Q fixed-size public nodes. -/
theorem recoverCount_physical_bound (Q : Nat) (iv : Digest32)
    (log : PublicLog) (input : Node) (queryCap : log.length ≤ Q) :
    (recoverCount Q iv log input).2 ≤ recognitionPolynomial Q+codecReservation Q :=
  (recoverCount_bound Q iv log input).trans
    (Nat.add_le_add (recognitionPolynomial_mono queryCap) (codecReservation_mono queryCap))

/-- The only scanner callback is the fixed public registry's shape lookup.
Original-input allowances price the separate full-root backend, not scanning. -/
structure MetadataCosts where
  shape : Nat
  originalFamily : Nat
  originalSlice : Nat

structure Calls where
  shape : Nat := 0
  deriving Repr

def Calls.add (a b : Calls) : Calls := ⟨a.shape+b.shape⟩
def Calls.cost (a : Calls) (c : MetadataCosts) : Nat := a.shape*c.shape

theorem Calls.add_cost (a b : Calls) (cost : MetadataCosts) :
    (a.add b).cost cost = a.cost cost+b.cost cost := by
  simp only [Calls.add,Calls.cost]
  ring

variable (p : ParameterBounds.Profile) (Q boundary : Nat)
    (registry : AnchoredHeaderRoots.Public) (target : AnchoredHeaderCodec.Record)

/-- Exact outer header decoding: concrete suffix/scalar parsing and fixed-word
header checks. The nested shapes getter is called only after its domain guard. -/
def headerCount (registry : AnchoredHeaderRoots.Public) (history : FramedHistory) :
    Option AnchoredHeaderRoots.Header × Nat × Nat :=
  if history.domain = registry.domain then
    match registry.shapes history.statement with
    | none => (none,1026,1)
    | some shape =>
      let shapeCost := PCSBCSCallerPayloadCost.shapeValidWork shape
      if shape.Valid then
        match history.frames.getLast? with
        | some (.absorb _ bytes) =>
          if 120 ≤ bytes.length then
            let scalars := PCSBCSPublicLogParserCost.parseExactCount 5 (bytes.drop (bytes.length-120))
            match scalars.1 with
            | none => (none,scalars.2+3*bytes.length+history.frames.length+shapeCost+1032,1)
            | some values =>
              ((AnchoredHeaderCodec.parseHeader shape values).map
                (fun root => ⟨history.statement,shape,root⟩),
                scalars.2+PCSBCSCallerPayloadCost.headerWork shape values+
                  3*bytes.length+history.frames.length+shapeCost+1544,1)
          else (none,2*bytes.length+history.frames.length+shapeCost+1032,1)
        | _ => (none,history.frames.length+shapeCost+1030,1)
      else (none,shapeCost+1028,1)
  else (none,1024,0)

theorem headerCount_value (registry : AnchoredHeaderRoots.Public) (history : FramedHistory) :
    (headerCount registry history).1 = AnchoredHeaderRoots.fromHistory registry history := by
  unfold headerCount AnchoredHeaderRoots.fromHistory
  split
  · cases registry.shapes history.statement with
    | none => rfl
    | some shape =>
      dsimp only
      split
      · cases history.frames.getLast? with
        | none => rfl
        | some frame =>
          cases frame with
          | nonce previous bits nonce => rfl
          | absorb previous bytes =>
            dsimp only
            split
            · rw [PCSBCSPublicLogParserCost.parseExactCount_value]
              cases WHIRHistory.parseExact 5 (bytes.drop (bytes.length-120)) <;> rfl
            · rfl
      · rfl
  · rfl

theorem shapeValidWork_fixed (shape : AnchoredHeaderCodec.Shape) :
    PCSBCSCallerPayloadCost.shapeValidWork shape ≤ 256 := by
  unfold PCSBCSCallerPayloadCost.shapeValidWork
  repeat' first | omega | split

def headerPolynomial (P : Nat) : Nat := 10000+4*P

theorem headerCount_bound (registry : AnchoredHeaderRoots.Public) (history : FramedHistory) :
    (headerCount registry history).2.1 ≤
      headerPolynomial (PCSBCSPublicLogParserCost.framesSize history.frames) ∧
    (headerCount registry history).2.2 ≤ 1 := by
  have count := PCSBCSPublicLogParserCost.framesSize_length history.frames
  unfold headerCount
  split
  · cases shapeAt : registry.shapes history.statement with
    | none => simp only [headerPolynomial]; omega
    | some shape =>
      have shapeBound := shapeValidWork_fixed shape
      dsimp only
      split
      · cases last : history.frames.getLast? with
        | none => dsimp only; unfold headerPolynomial; constructor <;> omega
        | some frame =>
          cases frame with
          | nonce previous bits nonce =>
            dsimp only
            unfold headerPolynomial
            constructor <;> omega
          | absorb previous bytes =>
            have member := List.mem_of_getLast? last
            have size : PCSBCSPublicLogParserCost.frameSize (.absorb previous bytes) ≤
                PCSBCSPublicLogParserCost.framesSize history.frames := by
              unfold PCSBCSPublicLogParserCost.framesSize
              exact List.le_sum_of_mem (List.mem_map.mpr ⟨.absorb previous bytes,member,rfl⟩)
            simp only [PCSBCSPublicLogParserCost.frameSize] at size
            dsimp only
            split
            · have suffixSize : (bytes.drop (bytes.length-120)).length ≤ 120 := by
                simp only [List.length_drop]
                omega
              have scalarBound := PCSBCSPublicLogParserCost.parseExactCount_bound 5
                (bytes.drop (bytes.length-120))
              have scalarCap : (PCSBCSPublicLogParserCost.parseExactCount 5
                  (bytes.drop (bytes.length-120))).2 ≤ 6866 := by omega
              cases parsed : (PCSBCSPublicLogParserCost.parseExactCount 5
                (bytes.drop (bytes.length-120))).1 with
              | none =>
                try dsimp only
                unfold headerPolynomial
                constructor <;> omega
              | some values =>
                have headerBound := PCSBCSCallerPayloadCost.headerWork_le shape values
                try dsimp only
                unfold headerPolynomial
                constructor <;> omega
            · try dsimp only
              unfold headerPolynomial
              constructor <;> omega
      · dsimp only; unfold headerPolynomial; constructor <;> omega
  · simp only [headerPolynomial]; omega


/-- Count the actual saved decoder and scheduled-key parser. The saved
record is neither supplied nor reconstructed by an opaque callback. The shape
exponent charge is explicit; supported valid records have logBatch < 64. -/
def openingReferencesCount (key : Coordinate) : Option (List Reference) × Nat :=
  let callerEntry := PCSBCSSourcePrimitiveRootBudget.entry key boundary
  let entryWork := callerEntry.frames.length+1
  let saved := PCSBCSSourceSavedRecordDecoderCost.decodeCount p callerEntry
  match saved.1 with
  | none => (none,entryWork+saved.2+1)
  | some record =>
    let pending := PCSBCSSourceReferenceParserCost.parsePendingKeyCount p callerEntry key
    match pending.1 with
    | none => (none,entryWork+saved.2+pending.2+1)
    | some messages =>
      (if phaseRolesAdmitted (ParameterBounds.config p) messages then
        some (⟨record.root,initialShape record.shape⟩ ::
          phaseReferences (ParameterBounds.config p) messages)
       else none,
       entryWork+saved.2+pending.2+PCSBCSSourceReferenceParserCost.phaseWork
         (ParameterBounds.config p) messages+3*record.shape.logBatch+4)

theorem openingReferencesCount_value (key : Coordinate) :
    (openingReferencesCount p boundary key).1 =
      PCSBCSSourcePrimitiveRootBudget.openingReferences p boundary key := by
  unfold openingReferencesCount PCSBCSSourcePrimitiveRootBudget.openingReferences
    PCSBCSSourcePrimitiveRootBudget.openingReferencesFromEntry
  dsimp only
  rw [PCSBCSSourceSavedRecordDecoderCost.decodeCount_value]
  cases PCSBCSSourceSavedRecordDecoder.decode p
    (PCSBCSSourcePrimitiveRootBudget.entry key boundary) with
  | none => rfl
  | some saved =>
    dsimp only [Bind.bind,Option.bind]
    simp only [PCSBCSSourceReferenceParserCost.parsePendingKeyCount_value]
    cases parsePendingKey p (PCSBCSSourcePrimitiveRootBudget.entry key boundary) key <;> rfl

/-- P+1 pays the shared entry take. 204 is the phase counter's eight-unit tail
plus 3*64+4 for initial-shape construction, not a caller-work reserve. -/
def openingReferencePolynomial (profile : ParameterBounds.Profile) (W P S : Nat) : Nat :=
  PCSBCSSourceSavedRecordDecoderCost.physicalPolynomial S+
    PCSBCSSourceReferencePolynomialBound.pendingKeyPolynomial (ParameterBounds.config profile) W P+
    (P+1)*(98*PCSBCSSourceReferencePolynomialBound.configSize (ParameterBounds.config profile)+4106)+P+205

theorem openingReferencesCount_bound (key : Coordinate) (W P S : Nat)
    (width : ∀ n, WHIRHistoryKey.stackWidth (ParameterBounds.config p) n ≤ W)
    (keyCap : PCSBCSPublicLogParserCost.framesSize key.history.frames ≤ P)
    (physicalCap : PCSBCSSourceSavedRecordDecoderCost.physicalSize
      (PCSBCSSourcePrimitiveRootBudget.entry key boundary) ≤ S) :
    (openingReferencesCount p boundary key).2 ≤ openingReferencePolynomial p W P S := by
  have entryCap : PCSBCSPublicLogParserCost.framesSize
      (PCSBCSSourcePrimitiveRootBudget.entry key boundary).frames ≤ P :=
    (PCSBCSPublicLogParserCost.framesSize_take _ _).trans keyCap
  have entryLength : (PCSBCSSourcePrimitiveRootBudget.entry key boundary).frames.length ≤ P :=
    (PCSBCSPublicLogParserCost.framesSize_length _).trans entryCap
  have savedBound := PCSBCSSourceSavedRecordDecoderCost.decodeCount_bound p
    (PCSBCSSourcePrimitiveRootBudget.entry key boundary)
  have savedCap : (PCSBCSSourceSavedRecordDecoderCost.decodeCount p
      (PCSBCSSourcePrimitiveRootBudget.entry key boundary)).2 ≤
      PCSBCSSourceSavedRecordDecoderCost.physicalPolynomial S := by
    apply savedBound.trans
    unfold PCSBCSSourceSavedRecordDecoderCost.physicalPolynomial
    gcongr
  have pendingCap := PCSBCSSourceReferencePolynomialBound.parsePendingKeyCount_work p
    (PCSBCSSourcePrimitiveRootBudget.entry key boundary) key W P width entryCap keyCap
  unfold openingReferencesCount
  dsimp only
  cases decoded : (PCSBCSSourceSavedRecordDecoderCost.decodeCount p
      (PCSBCSSourcePrimitiveRootBudget.entry key boundary)).1 with
  | none => simp only []; unfold openingReferencePolynomial; omega
  | some saved =>
    have accepted : PCSBCSSourceSavedRecordDecoder.decode p
        (PCSBCSSourcePrimitiveRootBudget.entry key boundary) = some saved := by
      rw [← PCSBCSSourceSavedRecordDecoderCost.decodeCount_value,decoded]
    have valid := (PCSBCSSourceSavedRecordDecoder.decode_sound p _ saved accepted).1
    have batch : saved.shape.logBatch < 64 := lt_trans valid.1.1 valid.1.2.1
    dsimp only
    cases pending : (PCSBCSSourceReferenceParserCost.parsePendingKeyCount p
        (PCSBCSSourcePrimitiveRootBudget.entry key boundary) key).1 with
    | none => simp only []; unfold openingReferencePolynomial; omega
    | some messages =>
      have mass := PCSBCSSourceReferencePolynomialBound.parsePendingKeyCount_mass p
        (PCSBCSSourcePrimitiveRootBudget.entry key boundary) key messages pending
      have phase := PCSBCSSourceReferencePolynomialBound.phaseWork_bound
        (ParameterBounds.config p) messages
      have phaseCap : PCSBCSSourceReferenceParserCost.phaseWork (ParameterBounds.config p) messages ≤
          (P+1)*(98*PCSBCSSourceReferencePolynomialBound.configSize (ParameterBounds.config p)+4106)+8 := by
        apply phase.trans
        apply Nat.add_le_add_right
        exact Nat.mul_le_mul_right _ (by omega)
      simp only []
      unfold openingReferencePolynomial
      omega

/-- Header parsing and materializing its cache shape are separate computations:
the latter performs the initial full-image width exponent once. -/
def headerShapeWork : Option AnchoredHeaderRoots.Header → Nat
  | none => 1
  | some header => 3*header.shape.logBatch+4

theorem headerShapeWork_bound (headers : AnchoredHeaderRoots.Public) (history : FramedHistory) :
    headerShapeWork (headerCount headers history).1 ≤ 196 := by
  cases parsed : (headerCount headers history).1 with
  | none => simp [headerShapeWork]
  | some header =>
    have accepted : AnchoredHeaderRoots.fromHistory headers history = some header := by
      rw [← headerCount_value,parsed]
    have valid := (AnchoredHeaderRoots.fromHistory_valid headers history header accepted).2.2.2
    have batch : header.shape.logBatch < 64 := lt_trans valid.1 valid.2.1
    simp only [headerShapeWork]
    omega

/-- One recovery, independent anchor decoding, then optional saved-opening
recovery. Shared entry take and both opening/anchor cache shapes are charged. -/
def referencesCount (_cost : MetadataCosts) (log : PublicLog) (input : Node) :
    List Reference × Nat × Calls :=
  let recovered := recoverCount Q PCSBCSSourceCoordinateDecoder.seedIV log input
  match recovered.1 with
  | none => ([],recovered.2,{})
  | some key =>
    let anchored :=
      match key.terminal with
      | .output _ =>
        let decoded := headerCount registry key.history
        ((decoded.1.map
          (fun h : AnchoredHeaderRoots.Header => [(⟨h.root,initialShape h.shape⟩ : Reference)])).getD [],
          decoded.2.1+headerShapeWork decoded.1,decoded.2.2)
      | _ => ([],1,0)
    let parsed := openingReferencesCount p boundary key
    (anchored.1 ++ parsed.1.getD [],
      recovered.2+anchored.2.1+parsed.2+anchored.1.length+1,
      ⟨anchored.2.2⟩)

theorem referencesCount_value (cost : MetadataCosts) (log : PublicLog) (input : Node) :
    (referencesCount p Q boundary registry cost log input).1 =
      PCSBCSSourcePrimitiveRootBudget.references p Q boundary registry log input := by
  unfold referencesCount PCSBCSSourcePrimitiveRootBudget.references
  dsimp only
  rw [recoverCount_value]
  cases PCSBCSSourceCoordinateDecoder.recover Q PCSBCSSourceCoordinateDecoder.seedIV log input with
  | none => rfl
  | some key =>
    dsimp only
    simp only [openingReferencesCount_value,Option.map_some,Option.getD_some]
    unfold PCSBCSSourcePrimitiveRootBudget.anchorReferences
    cases key.terminal <;> try rfl
    simp only [headerCount_value]
    cases AnchoredHeaderRoots.fromHistory registry key.history <;> rfl

theorem referencesCount_callback_cost (cost : MetadataCosts) (log : PublicLog) (input : Node) :
    (referencesCount p Q boundary registry cost log input).2.2.cost cost ≤ cost.shape := by
  unfold referencesCount
  dsimp only
  cases (recoverCount Q PCSBCSSourceCoordinateDecoder.seedIV log input).1 with
  | none => simp [Calls.cost]
  | some key =>
    have shapeCap := (headerCount_bound registry key.history).2
    dsimp only [Calls.cost]
    cases key.terminal <;> dsimp only
    all_goals nlinarith [Nat.mul_le_mul_right cost.shape shapeCap]

def sourceReferencePolynomial (profile : ParameterBounds.Profile) (queries W P S : Nat) : Nat :=
  recognitionPolynomial queries+codecReservation queries+headerPolynomial P+
    openingReferencePolynomial profile W P S+198

theorem referencesCount_polynomial (cost : MetadataCosts) (log : PublicLog) (input : Node)
    (W P S : Nat) (queryCap : log.length ≤ Q)
    (width : ∀ n, WHIRHistoryKey.stackWidth (ParameterBounds.config p) n ≤ W)
    (keyCaps : ∀ key, (recoverCount Q PCSBCSSourceCoordinateDecoder.seedIV log input).1 = some key →
      PCSBCSPublicLogParserCost.framesSize key.history.frames ≤ P)
    (physicalCaps : ∀ key, (recoverCount Q PCSBCSSourceCoordinateDecoder.seedIV log input).1 = some key →
      PCSBCSSourceSavedRecordDecoderCost.physicalSize
        (PCSBCSSourcePrimitiveRootBudget.entry key boundary) ≤ S) :
    (referencesCount p Q boundary registry cost log input).2.1 ≤
      sourceReferencePolynomial p Q W P S := by
  have recoveredCap := recoverCount_physical_bound Q PCSBCSSourceCoordinateDecoder.seedIV log input queryCap
  unfold referencesCount
  dsimp only
  cases recovered : (recoverCount Q PCSBCSSourceCoordinateDecoder.seedIV log input).1 with
  | none => simp only []; unfold sourceReferencePolynomial; omega
  | some key =>
    have keyCap := keyCaps key recovered
    have openingCap := openingReferencesCount_bound p boundary key W P S width keyCap
      (physicalCaps key recovered)
    have headerCap := (headerCount_bound registry key.history).1
    have headerShapeCap := headerShapeWork_bound registry key.history
    have headerWorkCap : (headerCount registry key.history).2.1 ≤ headerPolynomial P := by
      unfold headerPolynomial at headerCap ⊢
      omega
    have anchorLength : (((headerCount registry key.history).1.map
        (fun h : AnchoredHeaderRoots.Header => [(⟨h.root,initialShape h.shape⟩ : Reference)])).getD []).length ≤ 1 := by
      cases (headerCount registry key.history).1 <;> simp
    dsimp only
    cases key.terminal <;> dsimp only [List.length] <;>
      unfold sourceReferencePolynomial headerPolynomial at * <;> omega

#print axioms openingReferencesCount_value
#print axioms openingReferencesCount_bound
#print axioms referencesCount_polynomial

structure Selection where
  value : Option PublicLog
  operations : Nat
  callbacks : Calls
  referencesEvaluated : Nat
  targetComparisons : Nat

/-- The target CV/height/full-width/occupied key is materialized once. Every
visited reference comparison reserves 2048 byte/index/equality operations.
After the first capture, later records perform only one recursion visit. -/
def selectPrefixLoop (cost : MetadataCosts) (wanted : CacheKey) : PublicLog → Selection
  | [] => ⟨none,1,{},0,0⟩
  | (input,_)::log =>
    let prior := selectPrefixLoop cost wanted log
    match prior.value with
    | some captured => {prior with value := some captured,operations := prior.operations+1}
    | none =>
      let refs := referencesCount p Q boundary registry cost log input
      let found := findCount (fun ref => decide (cacheKey ref.root ref.shape = wanted)) refs.1
      ⟨if found.1.isSome then some log else none,
        prior.operations+refs.2.1+2048*found.2+1,
        Calls.add prior.callbacks refs.2.2,prior.referencesEvaluated+1,
        prior.targetComparisons+found.2⟩

def selectPrefixCount (cost : MetadataCosts) (log : PublicLog) : Selection :=
  let selected := selectPrefixLoop p Q boundary registry cost
    (cacheKey target.root (initialShape target.shape)) log
  {selected with operations := selected.operations+256+3*target.shape.logBatch}

theorem findCount_isSome {α : Type} (test : α → Bool) (xs : List α) :
    (findCount test xs).1.isSome = xs.any test := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [findCount,List.any_cons]
    split <;> simp_all

theorem selectPrefixLoop_value (cost : MetadataCosts) (wanted : CacheKey) (log : PublicLog) :
    (selectPrefixLoop p Q boundary registry cost wanted log).value =
      PCSBCSPublicLogExtractor.selectPrefixLoop p Q boundary registry wanted log := by
  induction log with
  | nil => rfl
  | cons record log ih =>
    rcases record with ⟨input,digest⟩
    simp only [selectPrefixLoop,PCSBCSPublicLogExtractor.selectPrefixLoop,ih]
    cases PCSBCSPublicLogExtractor.selectPrefixLoop p Q boundary registry wanted log with
    | some captured => rfl
    | none => simp only [findCount_isSome,referencesCount_value]

theorem selectPrefixCount_value (cost : MetadataCosts) (log : PublicLog) :
    (selectPrefixCount p Q boundary registry target cost log).value =
      PCSBCSPublicLogExtractor.selectPrefix p Q boundary registry target log := by
  exact selectPrefixLoop_value p Q boundary registry cost
    (cacheKey target.root (initialShape target.shape)) log

theorem selectPrefixLoop_calls (cost : MetadataCosts) (wanted : CacheKey) (log : PublicLog) :
    (selectPrefixLoop p Q boundary registry cost wanted log).referencesEvaluated ≤ log.length := by
  induction log with
  | nil => simp [selectPrefixLoop]
  | cons record log ih =>
    rcases record with ⟨input,digest⟩
    simp only [selectPrefixLoop,List.length_cons]
    split <;> dsimp only <;> omega

theorem selectPrefixCount_calls (cost : MetadataCosts) (log : PublicLog) :
    (selectPrefixCount p Q boundary registry target cost log).referencesEvaluated ≤ log.length := by
  exact selectPrefixLoop_calls p Q boundary registry cost _ log

/-- Exact source predicate visits, independently of key caching. A costly
target digest closure in the original uncached source selector is evaluated
at every visited target predicate, not merely once per root or log record. -/
theorem selectPrefixLoop_comparisons (cost : MetadataCosts) (wanted : CacheKey)
    (log : PublicLog) (queryCap : log.length ≤ Q) :
    (selectPrefixLoop p Q boundary registry cost wanted log).targetComparisons ≤
      log.length*(Q+1) := by
  induction log with
  | nil => simp [selectPrefixLoop]
  | cons record log ih =>
    rcases record with ⟨input,digest⟩
    have prefixCap : log.length ≤ Q := by simp only [List.length_cons] at queryCap; omega
    have prior := ih prefixCap
    have refsCap := PCSBCSSourcePrimitiveRootBudget.references_le p Q boundary registry log input
    have visits := findCount_bound (fun ref : Reference => decide (cacheKey ref.root ref.shape = wanted))
      (referencesCount p Q boundary registry cost log input).1
    rw [referencesCount_value] at visits
    have visitedCap :
        (findCount (fun ref : Reference => decide (cacheKey ref.root ref.shape = wanted))
          (referencesCount p Q boundary registry cost log input).1).2 ≤ Q+1 := by
      rw [referencesCount_value]
      omega
    simp only [selectPrefixLoop,List.length_cons]
    split <;> dsimp only <;> nlinarith

/-- Explicit extra price for an arbitrary target Digest32 closure. Both actual
and counted selectors cache the key once. After capture the counted freeze
also reads the root for its input-volume pass, in addition to the freeze key. -/
def targetDigestReadReservation (selected : Selection) : Nat :=
  1+(if selected.value.isSome then 2 else 0)

def targetDigestSurcharge (selected : Selection) (price : Fin 32 → Nat) : Nat :=
  targetDigestReadReservation selected*(List.ofFn price).sum

theorem targetDigestSurcharge_bound (cost : MetadataCosts) (log : PublicLog)
    (price : Fin 32 → Nat) :
    targetDigestSurcharge
      (selectPrefixCount p Q boundary registry target cost log) price ≤
      3*(List.ofFn price).sum := by
  unfold targetDigestSurcharge
  apply Nat.mul_le_mul_right
  unfold targetDigestReadReservation
  split <;> omega


theorem selectPrefixLoop_callback_cost (cost : MetadataCosts) (wanted : CacheKey)
    (log : PublicLog) :
    (selectPrefixLoop p Q boundary registry cost wanted log).callbacks.cost cost ≤
      log.length*cost.shape := by
  induction log with
  | nil => simp [selectPrefixLoop,Calls.cost]
  | cons record log ih =>
    rcases record with ⟨input,digest⟩
    have prior := ih
    have current := referencesCount_callback_cost p Q boundary registry cost log input
    simp only [selectPrefixLoop,List.length_cons]
    split
    · dsimp only; nlinarith
    · dsimp only; rw [Calls.add_cost]; nlinarith

theorem selectPrefixCount_callback_cost (cost : MetadataCosts) (log : PublicLog)
    :
    (selectPrefixCount p Q boundary registry target cost log).callbacks.cost cost ≤
      log.length*cost.shape := by
  exact selectPrefixLoop_callback_cost p Q boundary registry cost _ log


/-- Composition only: the concrete parser polynomial below discharges the
per-reference cap. This lemma never accepts a replacement parser or oracle. -/
theorem selectPrefixLoop_operations (cost : MetadataCosts) (wanted : CacheKey)
    (log : PublicLog) (B : Nat) (queryCap : log.length ≤ Q)
    (referenceCap : ∀ queryPrefix input, queryPrefix.length ≤ Q →
      (referencesCount p Q boundary registry cost queryPrefix input).2.1 ≤ B) :
    (selectPrefixLoop p Q boundary registry cost wanted log).operations ≤
      log.length*(B+2048*(Q+1)+1)+1 := by
  induction log with
  | nil => simp [selectPrefixLoop]
  | cons record log ih =>
    rcases record with ⟨input,digest⟩
    have prefixCap : log.length ≤ Q := by simp only [List.length_cons] at queryCap; omega
    have prior := ih prefixCap
    have parser := referenceCap log input prefixCap
    have refsCap := PCSBCSSourcePrimitiveRootBudget.references_le p Q boundary registry log input
    have findCap := findCount_bound (fun ref : Reference => decide (cacheKey ref.root ref.shape = wanted))
      (referencesCount p Q boundary registry cost log input).1
    rw [referencesCount_value] at findCap
    have actualFindCap :
        (findCount (fun ref : Reference => decide (cacheKey ref.root ref.shape = wanted))
          (referencesCount p Q boundary registry cost log input).1).2 ≤ Q+1 := by
      rw [referencesCount_value]
      omega
    simp only [selectPrefixLoop,List.length_cons]
    split <;> dsimp only <;> nlinarith

theorem selectPrefixCount_operations (cost : MetadataCosts) (log : PublicLog) (B : Nat)
    (queryCap : log.length ≤ Q)
    (referenceCap : ∀ queryPrefix input, queryPrefix.length ≤ Q →
      (referencesCount p Q boundary registry cost queryPrefix input).2.1 ≤ B) :
    (selectPrefixCount p Q boundary registry target cost log).operations ≤
      log.length*(B+2048*(Q+1)+1)+1+256+3*target.shape.logBatch := by
  have bound := selectPrefixLoop_operations p Q boundary registry cost
    (cacheKey target.root (initialShape target.shape)) log B queryCap referenceCap
  change (selectPrefixLoop p Q boundary registry cost
    (cacheKey target.root (initialShape target.shape)) log).operations+256+3*target.shape.logBatch ≤ _
  omega


open MerkleQueryLogExtraction PCSBCSMerkleQueryLog PCSBCSMerkleLeafImages

/-- One replay/preimage index and one fused full-image/suffix table. The
counter projections reuse their values; no second sourceCells is executed. -/
def freezeCount (log : PublicLog) (root : Digest32) (shape : Shape) : Frozen × Nat :=
  let replayed := MerkleQueryLogExtraction.PublicCost.recordsFrom log log
  let indexed := countedBuild replayed.1
  let cells := countedCells canonicalCodec indexed.1 shape.leafWords shape.occupied
    (defaultCell shape.leafWords shape.occupied) shape.height root #[]
  let compact := compactTable cells.1
  let images := ((cells.1.toList.map (fun cell => cell.image.size)).sum)
  let words := ((compact.toList.map Array.size).sum)
  (⟨shape,log,cells.1,compact⟩,
    2+replayed.2+indexed.2+cells.2+inputByteVolume canonicalCodec indexed.1 shape.height root+
      2*cells.1.size+2*images+words)

theorem replayedRecords_value (log : PublicLog) :
    (MerkleQueryLogExtraction.PublicCost.recordsFrom log log).1 =
      PublicMerkleLog.records log := by
  rw [MerkleQueryLogExtraction.PublicCost.recordsFrom_value]
  rfl

theorem freezeCount_value (log : PublicLog) (root : Digest32) (shape : Shape) :
    (freezeCount log root shape).1 = freeze log root shape := by
  simp only [freezeCount,replayedRecords_value,countedBuild_value,countedCells_value,
    freeze,sourceCells]

theorem freezeCount_charge (log : PublicLog) (root : Digest32) (shape : Shape) :
    (freezeCount log root shape).2 =
      operationCharge (∅ : Registry) ⟨log,root,shape⟩ := by
  simp only [freezeCount,replayedRecords_value,countedBuild_value,countedCells_value,
    operationCharge,Std.ExtHashMap.getElem?_empty,sourceCells,imageSlots,compactSlots,
    imageTable,Array.toList_map,List.map_map,Function.comp_def]

theorem freezeCount_bound (log : PublicLog) (root : Digest32) (shape : Shape)
    (Q N L O : Nat) (queryCap : log.length ≤ Q) (rowCap : 2^shape.height ≤ N)
    (leafCap : shape.leafWords ≤ L) (occupiedCap : shape.occupied ≤ O)
    (fits : shape.occupied ≤ shape.leafWords) :
    (freezeCount log root shape).2 ≤ operationBudget Q N L O := by
  rw [freezeCount_charge]
  exact (announcement_charges (∅ : Registry) ⟨log,root,shape⟩ Q N L O
    queryCap rowCap leafCap occupiedCap fits).1

/-- Actual retained image and compact field-word slots; unavailable cells and
bad padding remain status-bearing cells, not authenticated zero leaves. -/
theorem freezeCount_retained (log : PublicLog) (root : Digest32) (shape : Shape)
    (Q N L O : Nat) (queryCap : log.length ≤ Q) (rowCap : 2^shape.height ≤ N)
    (leafCap : shape.leafWords ≤ L) (occupiedCap : shape.occupied ≤ O)
    (fits : shape.occupied ≤ shape.leafWords) :
    ((imageTable (freezeCount log root shape).1.cells).toList.map Array.size).sum+
      (((freezeCount log root shape).1.raw).toList.map Array.size).sum ≤ N*(L+O) ∧
      (freezeCount log root shape).1.cells.size ≤ N ∧
      (freezeCount log root shape).1.queryPrefix.length ≤ Q := by
  rw [freezeCount_value]
  have charges := announcement_charges (∅ : Registry) ⟨log,root,shape⟩ Q N L O
    queryCap rowCap leafCap occupiedCap fits
  simpa only [wordCharge,cellCharge,prefixCharge,Std.ExtHashMap.getElem?_empty,
    imageSlots,compactSlots,freeze] using
    And.intro charges.2.2.1 (And.intro charges.2.2.2.1 charges.2.2.2.2)

#print axioms freezeCount_bound
#print axioms freezeCount_retained

/-- The actual full-root helper, with one counted freeze and one counted Gao/
original-statement run. The raw field-operation counter is kept separate from
opaque original-accessor prices. -/
def rootCount {m : Nat} (profile : ParameterBounds.Profile) (lanes : Nat)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (anchorPoint : Array E) (anchorValue : E) (log : PublicLog)
    (saved : AnchoredHeaderCodec.Record) :
    Option (CausalGame.Witness (ParameterBounds.config profile) lanes) × Nat × Nat :=
  let frozen := freezeCount log saved.root (initialShape saved.shape)
  let decoded := PCSRoundByRoundSource.countedRun profile lanes family points
    anchorPoint anchorValue frozen.1.raw
  (decoded.1,frozen.2,decoded.2)

theorem rootCount_value {m : Nat} (profile : ParameterBounds.Profile) (lanes : Nat)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (anchorPoint : Array E) (anchorValue : E) (log : PublicLog)
    (saved : AnchoredHeaderCodec.Record) :
    (rootCount profile lanes family points anchorPoint anchorValue log saved).1 =
      PCSBCSPublicRootExtractor.extract profile lanes family points anchorPoint anchorValue log saved := by
  simp only [rootCount,PCSRoundByRoundSource.countedRun_value,freezeCount_value,
    PCSBCSPublicRootExtractor.extract]

theorem rootCount_bound {m : Nat} (profile : ParameterBounds.Profile) (lanes : Nat)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (anchorPoint : Array E) (anchorValue : E) (log : PublicLog)
    (saved : AnchoredHeaderCodec.Record) (queries N L O : Nat)
    (queryCap : log.length ≤ queries)
    (rowsCap : 2^(initialShape saved.shape).height ≤ N)
    (leafCap : (initialShape saved.shape).leafWords ≤ L)
    (occupiedCap : (initialShape saved.shape).occupied ≤ O)
    (fits : (initialShape saved.shape).occupied ≤ (initialShape saved.shape).leafWords) :
    (rootCount profile lanes family points anchorPoint anchorValue log saved).2.1+
      (rootCount profile lanes family points anchorPoint anchorValue log saved).2.2 ≤
      operationBudget queries N L O +
        PCSRoundByRoundSource.resourcePolynomial (blockLength (ParameterBounds.config profile))
          (laneCount (ParameterBounds.config profile)) lanes m points.size := by
  exact Nat.add_le_add (freezeCount_bound log saved.root (initialShape saved.shape)
    queries N L O queryCap rowsCap leafCap occupiedCap fits)
    (PCSRoundByRoundSource.countedRun_polynomial_cost profile lanes family points
      anchorPoint anchorValue (freezeCount log saved.root (initialShape saved.shape)).1.raw)

/-- Preserve the existing kernel's raw field-operation/resource counter, before
the separate Merkle source-operation charge and opaque getter allowances. -/
theorem rootCount_kernel_bound {m : Nat} (profile : ParameterBounds.Profile) (lanes : Nat)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (anchorPoint : Array E) (anchorValue : E) (log : PublicLog)
    (saved : AnchoredHeaderCodec.Record) :
    (rootCount profile lanes family points anchorPoint anchorValue log saved).2.2 ≤
      PCSRoundByRoundSource.resourcePolynomial (blockLength (ParameterBounds.config profile))
        (laneCount (ParameterBounds.config profile)) lanes m points.size := by
  exact PCSRoundByRoundSource.countedRun_polynomial_cost profile lanes family points
    anchorPoint anchorValue (freezeCount log saved.root (initialShape saved.shape)).1.raw

#print axioms rootCount_value
#print axioms rootCount_bound
#print axioms rootCount_kernel_bound

/-- One selected full table and one full-root Gao/original-claim helper. Merkle
freeze is executed once; kernel backends are executed once each. -/
def extractCount {m : Nat} (cost : MetadataCosts) (lanes : Nat)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (anchorPoint : Array E) (anchorValue : E) (log : PublicLog) :
    Option (CausalGame.Witness (ParameterBounds.config p) lanes) × Selection × Nat :=
  let selected := selectPrefixCount p Q boundary registry target cost log
  match selected.value with
  | none => (none,selected,0)
  | some captured =>
    let decoded := rootCount p lanes family points anchorPoint anchorValue captured target
    (decoded.1,selected,decoded.2.1+decoded.2.2)

theorem extractCount_value {m : Nat} (cost : MetadataCosts) (lanes : Nat)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (anchorPoint : Array E) (anchorValue : E) (log : PublicLog) :
    (extractCount p Q boundary registry target cost lanes family points anchorPoint anchorValue log).1 =
      PCSBCSPublicLogExtractor.extract p Q boundary registry target lanes family points anchorPoint anchorValue log := by
  unfold extractCount PCSBCSPublicLogExtractor.extract
  dsimp only
  rw [selectPrefixCount_value]
  cases PCSBCSPublicLogExtractor.selectPrefix p Q boundary registry target log with
  | none => rfl
  | some captured =>
    exact rootCount_value p lanes family points anchorPoint anchorValue captured target

theorem selectPrefixLoop_prefix (cost : MetadataCosts) (wanted : CacheKey)
    (log captured : PublicLog)
    (known : (selectPrefixLoop p Q boundary registry cost wanted log).value = some captured) :
    captured.length ≤ log.length := by
  induction log generalizing captured with
  | nil => simp [selectPrefixLoop] at known
  | cons record log ih =>
    rcases record with ⟨input,digest⟩
    simp only [selectPrefixLoop] at known
    cases prior : (selectPrefixLoop p Q boundary registry cost wanted log).value with
    | some previous =>
      simp only [prior,Option.some.injEq] at known
      subst captured
      exact (ih previous prior).trans (by simp)
    | none =>
      simp only [prior] at known
      split at known
      · have equal := Option.some.inj known
        subst captured
        simp
      · cases known

theorem selectPrefixCount_prefix (cost : MetadataCosts) (log captured : PublicLog)
    (known : (selectPrefixCount p Q boundary registry target cost log).value = some captured) :
    captured.length ≤ log.length := by
  exact selectPrefixLoop_prefix p Q boundary registry cost _ log captured known

def backendPolynomial (p : ParameterBounds.Profile) (Q N L O lanes families points : Nat) : Nat :=
  PCSBCSMerkleRootCache.operationBudget Q N L O+
    PCSRoundByRoundSource.resourcePolynomial (blockLength (ParameterBounds.config p))
      (laneCount (ParameterBounds.config p)) lanes families points

/-- One physical-prefix preindex, one full padded image/suffix table and one
full-root Gao/original-statement helper. Decoder nodes and full lanes are the
literal production geometry; N/L/O cap the declared target tree geometry. -/
theorem extractCount_backend_bound {m : Nat} (cost : MetadataCosts) (lanes : Nat)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (anchorPoint : Array E) (anchorValue : E) (log : PublicLog) (N L O : Nat)
    (queryCap : log.length ≤ Q)
    (rowsCap : 2^(initialShape target.shape).height ≤ N)
    (leafCap : (initialShape target.shape).leafWords ≤ L)
    (occupiedCap : (initialShape target.shape).occupied ≤ O)
    (fits : (initialShape target.shape).occupied ≤ (initialShape target.shape).leafWords) :
    (extractCount p Q boundary registry target cost lanes family points anchorPoint anchorValue log).2.2 ≤
      backendPolynomial p Q N L O lanes m points.size := by
  unfold extractCount
  dsimp only
  cases selected : (selectPrefixCount p Q boundary registry target cost log).value with
  | none => exact Nat.zero_le _
  | some captured =>
    have prefixCap := (selectPrefixCount_prefix p Q boundary registry target cost
      log captured selected).trans queryCap
    exact rootCount_bound p lanes family points anchorPoint anchorValue captured target
      Q N L O prefixCap rowsCap leafCap occupiedCap fits

/-- The sole selected root table retains at most N*(L+O) field words, N
status-bearing cells and Q public-record references. This is NOT a dense-Gao
workspace, native-closure or total peak-memory certificate. Neither image
availability nor valid padding is assumed. -/
theorem selectedTable_retained (cost : MetadataCosts) (log captured : PublicLog)
    (N L O : Nat) (queryCap : log.length ≤ Q)
    (selected : (selectPrefixCount p Q boundary registry target cost log).value =
      some captured)
    (rowsCap : 2^(initialShape target.shape).height ≤ N)
    (leafCap : (initialShape target.shape).leafWords ≤ L)
    (occupiedCap : (initialShape target.shape).occupied ≤ O)
    (fits : (initialShape target.shape).occupied ≤ (initialShape target.shape).leafWords) :
    ((imageTable (freezeCount captured target.root (initialShape target.shape)).1.cells).toList.map Array.size).sum+
      ((freezeCount captured target.root (initialShape target.shape)).1.raw.toList.map Array.size).sum ≤ N*(L+O) ∧
      (freezeCount captured target.root (initialShape target.shape)).1.cells.size ≤ N ∧
      (freezeCount captured target.root (initialShape target.shape)).1.queryPrefix.length ≤ Q :=
  freezeCount_retained captured target.root (initialShape target.shape) Q N L O
    ((selectPrefixCount_prefix p Q boundary registry target cost
      log captured selected).trans queryCap) rowsCap leafCap occupiedCap fits

/-- The kernel's raw counter is preserved. Every backend logical unit is
additionally charged at BOTH supplied original-accessor prices, including
malformed original shape rejection. This deliberately conservative allowance
is not an exact getter-call count, CPU timing, or dense-Gao peak-memory bound.
Public-log/target/frame/header bytes are declared immutable input tables in
the base model; arbitrary costly digest closures need a separate surcharge. -/
def originalAccessorAllowance (rawBackend : Nat) (cost : MetadataCosts) : Nat :=
  rawBackend*(cost.originalFamily+cost.originalSlice)

def totalCharge {m : Nat} (cost : MetadataCosts) (lanes : Nat)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (anchorPoint : Array E) (anchorValue : E) (log : PublicLog) : Nat :=
  let result := extractCount p Q boundary registry target cost
    lanes family points anchorPoint anchorValue log
  result.2.1.operations+result.2.1.callbacks.cost cost+
    result.2.2+originalAccessorAllowance result.2.2 cost

theorem originalAccessorAllowance_bound (raw bound : Nat) (cost : MetadataCosts)
    (cap : raw ≤ bound) :
    raw+originalAccessorAllowance raw cost ≤
      bound*(1+cost.originalFamily+cost.originalSlice) := by
  unfold originalAccessorAllowance
  nlinarith [Nat.mul_le_mul_right (cost.originalFamily+cost.originalSlice) cap]

theorem extractCount_selection {m : Nat} (cost : MetadataCosts) (lanes : Nat)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (anchorPoint : Array E) (anchorValue : E) (log : PublicLog) :
    (extractCount p Q boundary registry target cost lanes family points
      anchorPoint anchorValue log).2.1 =
      selectPrefixCount p Q boundary registry target cost log := by
  unfold extractCount
  dsimp only
  split <;> rfl

/-- Missing capture never constructs a leaf table or invokes the decoder. A
captured table can separately contain unavailable cells or invalid padding. -/
theorem extractCount_missing {m : Nat} (cost : MetadataCosts) (lanes : Nat)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (anchorPoint : Array E) (anchorValue : E) (log : PublicLog)
    (missing : (selectPrefixCount p Q boundary registry target cost log).value = none) :
    (extractCount p Q boundary registry target cost lanes family points
      anchorPoint anchorValue log).1 = none ∧
    (extractCount p Q boundary registry target cost lanes family points
      anchorPoint anchorValue log).2.2 = 0 := by
  simp [extractCount,missing]

/-- Algebraic composition of reached internal source work, exact outer callback
prices and the separately preserved weighted kernel model. `B` bounds the REAL
counted references function, not a replacement parser, recovery oracle or
security hypothesis. This lemma by itself is not a public-input-size endpoint. -/
def compositionPolynomial (profile : ParameterBounds.Profile)
    (queries N L O lanes families points B batch : Nat) (cost : MetadataCosts) : Nat :=
  queries*(B+2048*(queries+1)+1)+257+3*batch+
    queries*cost.shape+
    backendPolynomial profile queries N L O lanes families points*
      (1+cost.originalFamily+cost.originalSlice)

theorem totalCharge_composition {m : Nat} (cost : MetadataCosts) (lanes : Nat)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (anchorPoint : Array E) (anchorValue : E) (log : PublicLog) (N L O B : Nat)
    (queryCap : log.length ≤ Q)
    (referenceCap : ∀ queryPrefix input, queryPrefix.length ≤ Q →
      (referencesCount p Q boundary registry cost queryPrefix input).2.1 ≤ B)
    (rowsCap : 2^(initialShape target.shape).height ≤ N)
    (leafCap : (initialShape target.shape).leafWords ≤ L)
    (occupiedCap : (initialShape target.shape).occupied ≤ O)
    (fits : (initialShape target.shape).occupied ≤ (initialShape target.shape).leafWords) :
    totalCharge p Q boundary registry target cost lanes family points
      anchorPoint anchorValue log ≤
      compositionPolynomial p Q N L O lanes m points.size B target.shape.logBatch cost := by
  have internal := selectPrefixCount_operations p Q boundary registry
    target cost log B queryCap referenceCap
  have metadata := selectPrefixCount_callback_cost p Q boundary registry
    target cost log
  have backend := extractCount_backend_bound p Q boundary registry
    target cost lanes family points anchorPoint anchorValue log N L O queryCap
    rowsCap leafCap occupiedCap fits
  have weighted := originalAccessorAllowance_bound _ _ cost backend
  have sourceCap := Nat.mul_le_mul_right (B+2048*(Q+1)+1) queryCap
  have metadataCap := Nat.mul_le_mul_right cost.shape queryCap
  unfold totalCharge compositionPolynomial
  simp only [extractCount_selection]
  omega

#print axioms totalCharge_composition

/-- Public-volume endpoint: P measures decoded chronological frame/cursor
volume and S the physical entry bytes/slots. No layout, saved record, caller
answer closure or caller-work reserve is a scanner input or cost premise. -/
theorem totalCharge_public_polynomial {m : Nat} (cost : MetadataCosts) (lanes : Nat)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (anchorPoint : Array E) (anchorValue : E) (log : PublicLog)
    (N L O W P S : Nat) (queryCap : log.length ≤ Q)
    (width : ∀ n, WHIRHistoryKey.stackWidth (ParameterBounds.config p) n ≤ W)
    (keyCaps : ∀ queryPrefix input key, queryPrefix.length ≤ Q →
      (recoverCount Q PCSBCSSourceCoordinateDecoder.seedIV queryPrefix input).1 = some key →
      PCSBCSPublicLogParserCost.framesSize key.history.frames ≤ P)
    (physicalCaps : ∀ queryPrefix input key, queryPrefix.length ≤ Q →
      (recoverCount Q PCSBCSSourceCoordinateDecoder.seedIV queryPrefix input).1 = some key →
      PCSBCSSourceSavedRecordDecoderCost.physicalSize
        (PCSBCSSourcePrimitiveRootBudget.entry key boundary) ≤ S)
    (rowsCap : 2^(initialShape target.shape).height ≤ N)
    (leafCap : (initialShape target.shape).leafWords ≤ L)
    (occupiedCap : (initialShape target.shape).occupied ≤ O)
    (fits : (initialShape target.shape).occupied ≤ (initialShape target.shape).leafWords) :
    totalCharge p Q boundary registry target cost lanes family points anchorPoint anchorValue log ≤
      compositionPolynomial p Q N L O lanes m points.size
        (sourceReferencePolynomial p Q W P S) target.shape.logBatch cost := by
  apply totalCharge_composition p Q boundary registry target cost lanes family points
    anchorPoint anchorValue log N L O (sourceReferencePolynomial p Q W P S) queryCap
  · intro queryPrefix input prefixCap
    exact referencesCount_polynomial p Q boundary registry cost queryPrefix input W P S
      prefixCap width (fun key recovered => keyCaps queryPrefix input key prefixCap recovered)
      (fun key recovered => physicalCaps queryPrefix input key prefixCap recovered)
  · exact rowsCap
  · exact leafCap
  · exact occupiedCap
  · exact fits

theorem bodyUnits_take (frames : List Frame) (n : Nat) :
    PCSBCSCoordinateCodecCost.bodyUnits (frames.take n) ≤
      PCSBCSCoordinateCodecCost.bodyUnits frames := by
  induction frames generalizing n with
  | nil => simp [PCSBCSCoordinateCodecCost.bodyUnits]
  | cons frame frames ih =>
    cases n with
    | zero => simp [PCSBCSCoordinateCodecCost.bodyUnits]
    | succ n =>
      simpa only [List.take_succ_cons,PCSBCSCoordinateCodecCost.bodyUnits,List.map_cons,
        List.sum_cons] using Nat.add_le_add_left (ih n) (PCSBCSCoordinateCodecCost.frameUnits frame)

theorem recoveredEntry_physical {log : PublicLog} {input : Node} {key : Coordinate}
    (recovered : (recoverCount Q PCSBCSSourceCoordinateDecoder.seedIV log input).1 = some key) :
    PCSBCSSourceSavedRecordDecoderCost.physicalSize
      (PCSBCSSourcePrimitiveRootBudget.entry key boundary) ≤ 65*Q := by
  rw [recoverCount_value] at recovered
  obtain ⟨_,_,_,_,_,_,valid,budget⟩ := PCSBCSSourceCoordinateDecoder.recover_sound recovered
  exact (bodyUnits_take key.history.frames boundary).trans
    (PCSBCSSourceSavedRecordDecoderCost.coordinate_physical key valid Q budget)

/-- Closed physical-Q endpoint, including the literal 2*S^2+2550*S+30100
saved decoder at S=65*Q. Numeric cursor volume is derived separately from the
source's admitted 49-bit cursor range; it is not substituted for physical bytes. -/
def physicalCompositionPolynomial (profile : ParameterBounds.Profile)
    (queries N L O lanes families points W batch : Nat) (cost : MetadataCosts) : Nat :=
  compositionPolynomial profile queries N L O lanes families points
    (sourceReferencePolynomial profile queries W
      (PCSBCSRecoveredSourceVolume.recoveredFramePolynomial queries) (65*queries)) batch cost

theorem totalCharge_physical_polynomial {m : Nat} (cost : MetadataCosts) (lanes : Nat)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (anchorPoint : Array E) (anchorValue : E) (log : PublicLog)
    (N L O W : Nat) (queryCap : log.length ≤ Q)
    (width : ∀ n, WHIRHistoryKey.stackWidth (ParameterBounds.config p) n ≤ W)
    (rowsCap : 2^(initialShape target.shape).height ≤ N)
    (leafCap : (initialShape target.shape).leafWords ≤ L)
    (occupiedCap : (initialShape target.shape).occupied ≤ O)
    (fits : (initialShape target.shape).occupied ≤ (initialShape target.shape).leafWords) :
    totalCharge p Q boundary registry target cost lanes family points anchorPoint anchorValue log ≤
      physicalCompositionPolynomial p Q N L O lanes m points.size W target.shape.logBatch cost := by
  apply totalCharge_public_polynomial p Q boundary registry target cost lanes family points
    anchorPoint anchorValue log N L O W
    (PCSBCSRecoveredSourceVolume.recoveredFramePolynomial Q) (65*Q) queryCap width
  · intro queryPrefix input key _ recovered
    rw [recoverCount_value] at recovered
    exact PCSBCSRecoveredSourceVolume.recover_wire recovered
  · intro queryPrefix input key _ recovered
    exact recoveredEntry_physical Q boundary recovered
  · exact rowsCap
  · exact leafCap
  · exact occupiedCap
  · exact fits

#print axioms totalCharge_public_polynomial
#print axioms recoveredEntry_physical
#print axioms totalCharge_physical_polynomial
#print axioms extractCount_backend_bound
#print axioms extendCount_bound
#print axioms privateKeyCount_bound
#print axioms recoverCount_value
#print axioms selectPrefixCount_value
#print axioms selectPrefixCount_operations
#print axioms extractCount_value
end Whir.PCSBCSPublicLogExtractorCost
