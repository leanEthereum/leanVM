import Whir.WHIRPhysicalHistory

/-! Erasure changes only ghost commitment oracles, never physical query rows or scalar parsing. The physical decoder retains all root, nonce, position and ancestor guards. -/
namespace Whir.WHIRPhysicalErasure
open Concrete Protocol CausalGame CausalProbability ParameterBounds
open FiatShamirGame (Digest32)
open WHIRHistory (Pending)

def eraseReply : Reply → Reply
  | .fold m next residual => .fold m (next.map fun _ => #[]) residual
  | r => r

def eraseLevel (level : LevelProof) : LevelProof :=
  {level with nextOracle := level.nextOracle.map fun _ => #[]}

def eraseOracles (proof : Opening) : Opening :=
  {proof with levels := proof.levels.map eraseLevel}

def zeroRoots : WHIRReplay.Roots := fun _ _ => #[]

def eraseReplay {p : Profile} (r : WHIRReplay.Replay p) : WHIRReplay.Replay p :=
  {r with replies := r.replies.map eraseReply}

def eraseStackReplay {p : Profile} {cap : Nat} (r : StackWHIRReplay.Replay p cap) :
    StackWHIRReplay.Replay p cap :=
  {r with whir := eraseReplay r.whir}

@[simp] theorem eraseReply_default : eraseReply default = default := rfl

@[simp] theorem initialField_erase (r : Reply) : initialField (eraseReply r) = initialField r := by
  cases r <;> rfl
@[simp] theorem foldField_erase (r : Reply) : foldField (eraseReply r) = foldField r := by
  cases r <;> rfl
@[simp] theorem rootField_erase (r : Reply) :
    rootField (eraseReply r) = (rootField r).map (fun _ => #[]) := by
  cases r <;> rfl
@[simp] theorem residualField_erase (r : Reply) : residualField (eraseReply r) = residualField r := by
  cases r <;> rfl
@[simp] theorem oodField_erase (r : Reply) : oodField (eraseReply r) = oodField r := by
  cases r <;> rfl
@[simp] theorem rowsField_erase (r : Reply) : rowsField (eraseReply r) = rowsField r := by
  cases r <;> rfl
@[simp] theorem introField_erase (r : Reply) : introField (eraseReply r) = introField r := by
  cases r <;> rfl
@[simp] theorem tailField_erase (r : Reply) : tailField (eraseReply r) = tailField r := by
  cases r <;> rfl

@[simp] theorem getElem!_erase (answers : Array Reply) (i : Nat) :
    (answers.map eraseReply)[i]! = eraseReply answers[i]! := by
  by_cases h : i < answers.size
  · simp only [getElem!_pos, Array.size_map, h, Array.getElem_map]
  · rw [getElem!_neg (answers.map eraseReply) i (by simpa using h),
      getElem!_neg answers i h]
    rfl

/-- All serialized scalars, including the explicit root digest, are unchanged. -/
theorem replyScalars_erase {c : Config} (q : Coordinate c) (digest : Digest32) (r : Reply) :
    WHIRHistory.replyScalars q digest (eraseReply r) = WHIRHistory.replyScalars q digest r := by
  cases q <;> cases r <;> rfl

theorem decodeReplyScalars_zero {c : Config} (q : Coordinate c)
    (lookup : Digest32 → Oracle) (rows : Oracle) (xs : List E) :
    WHIRHistory.decodeReplyScalars q (fun _ => #[]) rows xs =
      (WHIRHistory.decodeReplyScalars q lookup rows xs).map eraseReply := by
  cases q with
  | initial => simp [WHIRHistory.decodeReplyScalars, Option.map_map, Function.comp_def, eraseReply]
  | tail j => simp [WHIRHistory.decodeReplyScalars, Option.map_map, Function.comp_def, eraseReply]
  | query i => simp [WHIRHistory.decodeReplyScalars, Option.map_map, Function.comp_def, eraseReply]
  | ood i j =>
    cases xs with
    | nil => rfl
    | cons a xs => cases xs with
      | nil => rfl
      | cons b xs => cases xs with
        | nil => rfl
        | cons d xs => cases xs <;> rfl
  | fold i j =>
    cases xs with
    | nil => rfl
    | cons a xs => cases xs with
      | nil => rfl
      | cons b rest =>
        simp only [WHIRHistory.decodeReplyScalars]
        split
        · split
          · cases rest with
            | nil => rfl
            | cons r rest => cases rest with
              | nil => rfl
              | cons s rest => cases rest <;>
                  simp [Option.map_map, Function.comp_def, eraseReply]
          · split <;> rfl
        · split <;> rfl

theorem parseReply_zero {c : Config} (q : Coordinate c)
    (lookup : Digest32 → Oracle) (rows : Oracle) (bytes : List FiatShamirGame.Byte) :
    WHIRHistory.parseReply q (fun _ => #[]) rows bytes =
      (WHIRHistory.parseReply q lookup rows bytes).map eraseReply := by
  unfold WHIRHistory.parseReply
  cases WHIRHistory.parseExact (WHIRHistory.replyScalarCount q) bytes with
  | none => rfl
  | some xs => exact decodeReplyScalars_zero q lookup rows xs

theorem checkReplies_erase (batches : List Batch) (answers : List Reply) :
    checkReplies batches (answers.map eraseReply) = checkReplies batches answers := by
  induction batches generalizing answers with
  | nil => cases answers <;> rfl
  | cons b bs ih =>
    cases answers with
    | nil => cases b <;> rfl
    | cons r rs => cases b <;> cases r <;> simp [checkReplies, eraseReply, ih]

theorem decodedLevel_erase (c : Config) (ch : Challenges) (answers : Array Reply) (i : Nat) :
    decodedLevel c ch (answers.map eraseReply) i = eraseLevel (decodedLevel c ch answers i) := by
  simp only [decodedLevel, getElem!_erase, foldField_erase, rootField_erase,
    oodField_erase, rowsField_erase, introField_erase, eraseLevel]
  split <;> rfl

theorem decodedOpening_erase (c : Config) (ch : Challenges) (answers : Array Reply) :
    decodedOpening c ch (answers.map eraseReply) = eraseOracles (decodedOpening c ch answers) := by
  simp [decodedOpening, eraseOracles, Array.map_ofFn, Function.comp_def, decodedLevel_erase]

theorem opening_erase (c : Config) (ch : Challenges) (answers : Array Reply) :
    opening c ch (answers.map eraseReply) = (opening c ch answers).map eraseOracles := by
  simp only [opening, Array.toList_map, checkReplies_erase]
  cases checkReplies (visibleBatches c E.zero ch) answers.toList <;>
    simp [decodedOpening_erase, Except.map]

theorem reply_zero {p : Profile} (roots : WHIRReplay.Roots) (rows : WHIRPhysicalHistory.Rows)
    (q : Coordinate (config p)) (pending : Pending) :
    WHIRPhysicalHistory.reply zeroRoots rows q pending =
      (WHIRPhysicalHistory.reply roots rows q pending).map eraseReply :=
  decodeReplyScalars_zero q _ _ _

theorem step_zero {p : Profile} (roots : WHIRReplay.Roots) (rows : WHIRPhysicalHistory.Rows)
    (r : WHIRReplay.Replay p) (q : Coordinate (config p)) (x : Sample q) (pending : Pending) :
    WHIRPhysicalHistory.step zeroRoots rows (eraseReplay r) q x pending =
      (WHIRPhysicalHistory.step roots rows r q x pending).map eraseReplay := by
  unfold WHIRPhysicalHistory.step
  rw [reply_zero roots]
  simp [Option.map_map, Function.comp_def, eraseReplay, Array.map_push]

theorem decodeHistory_zero (p : Profile) (catalog : WHIRReplay.Catalog p)
    (roots : WHIRReplay.Roots) (rows : WHIRPhysicalHistory.Rows) (s : Digest32)
    (messages : List Pending) (ancestors : List (Pending × Sigma (@Sample (config p)))) :
    WHIRPhysicalHistory.decodeHistory p catalog zeroRoots rows s messages ancestors =
      (WHIRPhysicalHistory.decodeHistory p catalog roots rows s messages ancestors).map eraseReplay := by
  induction messages generalizing ancestors with
  | nil => rfl
  | cons m messages ih =>
    cases messages with
    | nil =>
      cases ancestors with
      | nil =>
        simp only [WHIRPhysicalHistory.decodeHistory]
        split
        · cases catalog s <;> simp [eraseReplay]
        · rfl
      | cons a ancestors => rfl
    | cons previous older =>
      cases ancestors with
      | nil => rfl
      | cons entry past =>
        rcases entry with ⟨previous',q,x⟩
        simp only [WHIRPhysicalHistory.decodeHistory]
        split
        · split
          · split
            · split
              · split
                · rw [ih]
                  cases WHIRPhysicalHistory.decodeHistory p catalog roots rows s (previous::older) past with
                  | none => rfl
                  | some before => exact step_zero roots rows before q x m
                · rfl
              · rfl
            · rfl
          · rfl
        · rfl

theorem decode_zero (p : Profile) (catalog : WHIRReplay.Catalog p)
    (roots : WHIRReplay.Roots) (rows : WHIRPhysicalHistory.Rows) (key : WHIRReplay.Key p) :
    WHIRPhysicalHistory.decode p catalog zeroRoots rows key =
      (WHIRPhysicalHistory.decode p catalog roots rows key).map eraseReplay :=
  decodeHistory_zero p catalog roots rows _ _ _

theorem decodeStack_zero (p : Profile) (cap : Nat) (catalog : StackWHIRReplay.Catalog p cap)
    (roots : WHIRReplay.Roots) (rows : WHIRPhysicalHistory.Rows) (key : StackWHIRReplay.Key p) :
    WHIRPhysicalHistory.decodeStack p cap catalog zeroRoots rows key =
      (WHIRPhysicalHistory.decodeStack p cap catalog roots rows key).map eraseStackReplay := by
  unfold WHIRPhysicalHistory.decodeStack
  cases catalog key.statement with
  | none => rfl
  | some original =>
    cases StackWHIRReplay.initialSeed key.ancestors with
    | none => rfl
    | some initial =>
      change (WHIRPhysicalHistory.decode p (StackWHIRReplay.localCatalog original initial) zeroRoots rows
        (StackWHIRReplay.projectKey key)).bind (fun whir => some ⟨original,initial,whir⟩) =
        ((WHIRPhysicalHistory.decode p (StackWHIRReplay.localCatalog original initial) roots rows
          (StackWHIRReplay.projectKey key)).bind (fun whir => some ⟨original,initial,whir⟩)).map eraseStackReplay
      rw [decode_zero p _ roots]
      cases WHIRPhysicalHistory.decode p (StackWHIRReplay.localCatalog original initial) roots rows
        (StackWHIRReplay.projectKey key) <;> rfl

end Whir.WHIRPhysicalErasure
