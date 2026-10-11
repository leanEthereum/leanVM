import Whir.PCSBCSChallengeOracleSource
import Whir.AnchoredSourceFreshCaller
import Whir.PCSBCSMerkleRootCacheCost

/-! Literal PR600 roles at 12eea88c41dd964d82d4eb15ce91bba17ef91339:
commit.rs:124-175,229-253 and verify.rs:395-437. This is a source schedule
hand-port, not universal Rust refinement and not a digest search. Admission is
syntax and immutable-record binding, not Merkle acceptance, honest padding,
or truth of any evaluation. No current packet is read by the registry. -/
namespace Whir.PCSBCSSourceRootReferences
open Concrete Protocol CausalGame CausalProbability FiatShamirGame WHIRHistory WHIRHistoryKey
open AnchoredHeaderCodec PCSBCSMerkleRootCache

local instance : DecidableEq Terminal := by
  intro a b
  cases a <;> cases b <;> simp <;> infer_instance

local instance : DecidableEq FiatShamirGame.Coordinate := by
  intro a b
  cases a
  cases b
  simp only [FiatShamirGame.Coordinate.mk.injEq]
  infer_instance

local instance : DecidableEq PCSBCSMerkleRootCache.Shape := by
  intro a b
  cases a
  cases b
  simp only [PCSBCSMerkleRootCache.Shape.mk.injEq]
  infer_instance

structure Reference where
  root : Digest32
  shape : PCSBCSMerkleRootCache.Shape
  deriving DecidableEq

/-- The production initial leaf is the full lane cube, not just its live suffix. -/
def initialShape (s : AnchoredHeaderCodec.Shape) : PCSBCSMerkleRootCache.Shape :=
  ⟨s.logN-s.logBatch+s.logRate, 2^s.logBatch, s.lanes⟩

/-- Phase i+1 is announced after folding phase i, but uses the NEXT fold and
rate for its own row geometry. Extension elements occupy three base words. -/
def phaseShape (c : Config) (phase : Nat) : PCSBCSMerkleRootCache.Shape :=
  ⟨remaining c phase + c.rates[phase]!, 3*2^c.folds[phase]!, 3*2^c.folds[phase]!⟩

def profileShape (p : ParameterBounds.Profile) (s : AnchoredHeaderCodec.Shape) : Prop :=
  s.logN = (ParameterBounds.config p).logN ∧
  s.logBatch = (ParameterBounds.config p).folds[0]! ∧
  s.logRate = (ParameterBounds.config p).rates[0]!
instance (p : ParameterBounds.Profile) (s : AnchoredHeaderCodec.Shape) :
    Decidable (profileShape p s) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Offset 3 is the root role; offset 5 is context CV and NEVER a tree root.
The entire original record frame must match, not merely its marker or digest. -/
def parseInitial (saved : Record) (frame : List E) (offset : Nat) : Option Reference :=
  if saved.Valid ∧ frame = openingScalars saved ∧ offset = 3 then
    some ⟨saved.root, initialShape saved.shape⟩ else none

theorem parseInitial_roundtrip (saved : Record) (valid : saved.Valid) :
    parseInitial saved (openingScalars saved) 3 =
      some ⟨saved.root,initialShape saved.shape⟩ := by simp [parseInitial,valid]

theorem parseInitial_admitted (saved : Record) (frame : List E) (offset : Nat)
    (ref : Reference) (parsed : parseInitial saved frame offset = some ref) :
    saved.Valid ∧ frame = openingScalars saved ∧ offset = 3 ∧
      ref = ⟨saved.root,initialShape saved.shape⟩ := by
  unfold parseInitial at parsed
  split at parsed
  next guard => exact ⟨guard.1,guard.2.1,guard.2.2,(Option.some.inj parsed).symm⟩
  next => contradiction

/-- Reuse the deployed scalar-pair codec directly, as decodeReplyScalars does.
No temporary 48-byte re-encoding and scalar re-decoding is executed. -/
def parseRootScalars : List E → Option Digest32
  | [a,b] => ByteCodec.scalarsToHash (a,b)
  | _ => none

theorem parseRootScalars_byte_codec (a b : E) :
    parseRootScalars [a,b] = WHIRHistory.parseRoot (scalarBytes [a,b]) := by
  have decoded := parseExact_roundtrip [a,b]
  simp only [List.length_cons,List.length_nil] at decoded
  simp [parseRootScalars,WHIRHistory.parseRoot,decoded]

theorem parseRootScalars_roundtrip (root : Digest32) :
    parseRootScalars (rootScalars root) = some root := by
  simp [parseRootScalars,rootScalars,ByteCodec.scalarsToHash_hashToScalars]

/-- The root immediately follows the two quadratic coefficients of a final
nonterminal fold. Foreign phases, middle folds and arbitrary scalar offsets
reject even if their values happen to encode a digest. -/
def parsePhase (c : Config) (q : CausalProbability.Coordinate c)
    (m : Pending) (phase offset : Nat) : Option Reference :=
  match q with
  | .fold i j =>
    if j.val+1 = c.folds[i.val]! ∧ i.val+1 < c.folds.size ∧
        phase = i.val+1 ∧ offset = 2 ∧ m.scalars.length = 4 then do
      let root ← parseRootScalars (m.scalars.drop 2)
      pure ⟨root,phaseShape c phase⟩
    else none
  | _ => none

theorem parsePhase_roundtrip (c : Config) (i : Fin c.folds.size)
    (j : Fin c.folds[i.val]!) (last : j.val+1 = c.folds[i.val]!)
    (later : i.val+1 < c.folds.size) (a b : E) (root : Digest32)
    (nonce : Option (Nat × E)) :
    parsePhase c (.fold i j) ⟨[a,b] ++ rootScalars root,nonce⟩ (i.val+1) 2 =
      some ⟨root,phaseShape c (i.val+1)⟩ := by
  have size : (rootScalars root).length = 2 := rfl
  have decoded : parseRootScalars (rootScalars root) = some root :=
    parseRootScalars_roundtrip root
  simp [parsePhase,last,later,size,decoded]

theorem parsePhase_admitted (c : Config) (q : CausalProbability.Coordinate c)
    (m : Pending) (phase offset : Nat) (ref : Reference)
    (parsed : parsePhase c q m phase offset = some ref) :
    offset = 2 ∧ phase < c.folds.size ∧ m.scalars.length = 4 ∧
      ref.shape = phaseShape c phase := by
  cases q <;> try (change none = some ref at parsed; contradiction)
  case fold i j =>
    dsimp only [parsePhase] at parsed
    by_cases guard : j.val+1 = c.folds[i.val]! ∧ i.val+1 < c.folds.size ∧
        phase = i.val+1 ∧ offset = 2 ∧ m.scalars.length = 4
    · rw [ite_eq_left guard] at parsed
      obtain ⟨last,later,index,role,size⟩ := guard
      cases root : parseRootScalars (m.scalars.drop 2) with
      | none =>
        simp only [root] at parsed
        dsimp only [Bind.bind,Option.bind] at parsed
        contradiction
      | some digest =>
        simp only [root] at parsed
        dsimp only [Bind.bind,Option.bind,Pure.pure] at parsed
        have equal := Option.some.inj parsed
        subst ref
        exact ⟨role,index.symm ▸ later,size,rfl⟩
    · rw [ite_eq_right guard] at parsed
      contradiction

/-- Chronological Pending position n contains the reply to schedule[n-1]. -/
def phaseAt (c : Config) (n : Nat) (m : Pending) : Option Reference :=
  if n = 0 then none else
  let q := ((schedule c)[n-1]?).getD .initial
  match q with
  | .fold i _ => parsePhase c q m (i.val+1) 2
  | _ => none

def phaseReferences (c : Config) (messages : List Pending) : List Reference :=
  messages.reverse.zipIdx.filterMap (fun (m,n) => phaseAt c n m)

/-- Source next_root rejects noncanonical halves. An invalid root at a checked
role is a failed parse, not permission to silently omit that reference. -/
def phaseRolesAdmitted (c : Config) (messages : List Pending) : Bool :=
  messages.reverse.zipIdx.all fun (m,n) =>
    if n = 0 then true else
    let q := ((schedule c)[n-1]?).getD .initial
    match q with
    | .fold i j =>
      if j.val+1 = c.folds[i.val]! ∧ i.val+1 < c.folds.size then
        (parsePhase c q m (i.val+1) 2).isSome
      else true
    | _ => true

/-- Parse ALL prior steps, restore the unabsorbed initial Pending, then require
literal whole-key equality. Wrong seed, prefix, previous-width, nonce frame,
scalar role or continuation block cannot be admitted by a suffix search. -/
def parsePendingKey (p : ParameterBounds.Profile) (entry : FramedHistory)
    (key : FiatShamirGame.Coordinate) : Option (List Pending) := do
  let chronological ← parseSteps (key.history.frames.drop entry.frames.length)
  let messages := chronological.reverse ++ [initialPending]
  let block ← match key.terminal with | .output b => some b | _ => none
  if scheduledAdmissible (ParameterBounds.config p) messages = true ∧
      key = WHIRCallerPrefix.outputKeyFrom (stackWidth (ParameterBounds.config p))
        entry messages block then some messages else none

theorem parsePendingKey_roundtrip (p : ParameterBounds.Profile) (entry : FramedHistory)
    (messages : List Pending) (nonempty : messages ≠ [])
    (admitted : scheduledAdmissible (ParameterBounds.config p) messages = true)
    (block : Nat) :
    parsePendingKey p entry (WHIRCallerPrefix.outputKeyFrom
      (stackWidth (ParameterBounds.config p)) entry messages block) = some messages := by
  have normal := scheduled_normal _ _ nonempty admitted
  have parsed := WHIRCallerPrefix.parse_outputKeyFrom _ (stackWidth_positive p)
    entry normal block
  simp only [parsePendingKey,parsed]
  dsimp only [Bind.bind,Option.bind,WHIRCallerPrefix.outputKeyFrom]
  rw [List.reverse_reverse]
  rw [normal.restore]
  simp [admitted]

theorem parsePendingKey_admitted (p : ParameterBounds.Profile) (entry : FramedHistory)
    (key : FiatShamirGame.Coordinate) (messages : List Pending)
    (parsed : parsePendingKey p entry key = some messages) :
    messages ≠ [] ∧ scheduledAdmissible (ParameterBounds.config p) messages = true ∧
      ∃ block, key = WHIRCallerPrefix.outputKeyFrom (stackWidth (ParameterBounds.config p))
        entry messages block := by
  unfold parsePendingKey at parsed
  cases steps : parseSteps (key.history.frames.drop entry.frames.length) with
  | none => simp [steps] at parsed
  | some chronological =>
    simp only [steps] at parsed
    dsimp only [Bind.bind,Option.bind] at parsed
    cases terminal : key.terminal with
    | commitment _ => simp [terminal] at parsed
    | powBase _ _ => simp [terminal] at parsed
    | output block =>
      simp only [terminal] at parsed
      split at parsed
      next guard =>
        have same := Option.some.inj parsed
        subst messages
        exact ⟨by simp,guard.1,block,guard.2⟩
      next => contradiction

/-- Initial identity admission is the existing public caller parser. This
checks the saved binding frame at its control-shape position; its context CV,
point and value are not additional root references. -/
def parseReferences (p : ParameterBounds.Profile) (layout : WHIRCallerClaims.CallerLayout)
    (saved : Record) (entry : FramedHistory) (answers : FiatShamirGame.Coordinate → Digest32)
    (key : FiatShamirGame.Coordinate) : Option (List Reference) := do
  if saved.Valid ∧ profileShape p saved.shape then pure () else none
  let _ ← AnchoredSourceFreshCaller.decode layout saved entry answers
  let messages ← parsePendingKey p entry key
  if phaseRolesAdmitted (ParameterBounds.config p) messages then
    pure (⟨saved.root,initialShape saved.shape⟩ ::
      phaseReferences (ParameterBounds.config p) messages)
  else none

theorem parseReferences_admitted (p : ParameterBounds.Profile)
    (layout : WHIRCallerClaims.CallerLayout) (saved : Record) (entry : FramedHistory)
    (answers : FiatShamirGame.Coordinate → Digest32) (key : FiatShamirGame.Coordinate)
    (refs : List Reference) (parsed : parseReferences p layout saved entry answers key = some refs) :
    saved.Valid ∧ profileShape p saved.shape ∧
      ∃ claims messages,
        AnchoredSourceFreshCaller.decode layout saved entry answers = some claims ∧
        parsePendingKey p entry key = some messages ∧
        phaseRolesAdmitted (ParameterBounds.config p) messages = true ∧
        refs = ⟨saved.root,initialShape saved.shape⟩ ::
          phaseReferences (ParameterBounds.config p) messages := by
  unfold parseReferences at parsed
  split at parsed
  next guard =>
    dsimp only [Bind.bind,Option.bind,Pure.pure] at parsed
    cases caller : AnchoredSourceFreshCaller.decode layout saved entry answers with
    | none => simp [caller] at parsed
    | some claims =>
      simp only [caller] at parsed
      cases pending : parsePendingKey p entry key with
      | none => simp [pending] at parsed
      | some messages =>
        simp only [pending] at parsed
        split at parsed
        next roles =>
          exact ⟨guard.1,guard.2,claims,messages,rfl,rfl,roles,
            (Option.some.inj parsed).symm⟩
        next => contradiction
  next => simp at parsed

theorem initialShape_admitted (saved : Record) (valid : saved.Valid) :
    (initialShape saved.shape).occupied ≤ (initialShape saved.shape).leafWords :=
  valid.1.2.2.2.2.2

theorem phaseShape_admitted (c : Config) (phase : Nat) :
    (phaseShape c phase).occupied = (phaseShape c phase).leafWords := rfl

/-- Every listed phase reference comes from its scheduled Pending position,
and carries the full three-limb extension leaf rather than an occupied-only
or CV-only address. No assumption about committed padding is used. -/
theorem phaseReference_admitted (c : Config) (messages : List Pending)
    (ref : Reference) (member : ref ∈ phaseReferences c messages) :
    ref.shape.occupied = ref.shape.leafWords := by
  obtain ⟨⟨m,n⟩,_,decoded⟩ := List.mem_filterMap.mp member
  change phaseAt c n m = some ref at decoded
  by_cases initial : n = 0
  · simp [phaseAt,initial] at decoded
  · simp only [phaseAt,initial,↓reduceIte] at decoded
    cases coordinate : ((schedule c)[n-1]?).getD .initial with
    | fold i j =>
      simp only [coordinate] at decoded
      have shape := (parsePhase_admitted c (.fold i j) m (i.val+1) 2 ref decoded).2.2.2
      rw [shape]
      rfl
    | initial => simp [coordinate] at decoded
    | ood i j => simp [coordinate] at decoded
    | query i => simp [coordinate] at decoded
    | tail i => simp [coordinate] at decoded

#print axioms parseInitial_roundtrip
#print axioms parseInitial_admitted
#print axioms parseRootScalars_byte_codec
#print axioms parseRootScalars_roundtrip
#print axioms parsePhase_roundtrip
#print axioms parsePhase_admitted
#print axioms parsePendingKey_roundtrip
#print axioms parsePendingKey_admitted
#print axioms parseReferences_admitted
#print axioms initialShape_admitted
#print axioms phaseShape_admitted
#print axioms phaseReference_admitted
end Whir.PCSBCSSourceRootReferences
