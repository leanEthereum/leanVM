import Whir.SpongefishCurrentRecordModeCapture

/-! Current #607 round boundaries. Consecutive E values within one verifier
message may share a 32-byte output block. This module checks that distinct
scheduled verifier messages have a nonempty absorbed prover payload between
them, and proves that this creates a distinct construction history. These are
causal framing results, not a random-oracle or whole-system entropy theorem. -/
namespace Whir.SpongefishCurrentRoundSeparation
open Concrete FiatShamirGame DuplexRefinement
open SpongefishPCSRoundFrames
set_option autoImplicit false

/-- `waiting` means a verifier message has been emitted since the last
nonempty prover payload. No guard is added to the source verifier. -/
def scan : Bool → List Call → Option Bool
  | waiting, [] => some waiting
  | waiting, .read kind :: rest =>
      scan (if kind.codec.size = 0 then waiting else false) rest
  | waiting, .hint :: rest => scan waiting rest
  | waiting, .draw _ :: rest =>
      if waiting then none else scan true rest

theorem scan_append (waiting : Bool) (xs ys : List Call) :
    scan waiting (xs ++ ys) = (scan waiting xs).bind (fun next => scan next ys) := by
  induction xs generalizing waiting with
  | nil => rfl
  | cons call xs ih =>
    cases call with
    | read kind => simpa only [List.cons_append,scan] using ih _
    | hint => simpa only [List.cons_append,scan] using ih waiting
    | draw group => cases waiting <;> simp [scan,ih]

private theorem scan_waiting_without_payload (middle suffix : List Call) (g : Group)
    (empty : ∀ kind, Call.read kind ∈ middle → kind.codec.size = 0) :
    scan true (middle ++ Call.draw g :: suffix) = none := by
  induction middle with
  | nil => rfl
  | cons call middle ih =>
    cases call with
    | draw first => rfl
    | hint =>
      exact ih (fun kind member => empty kind (by simp [member]))
    | read kind =>
      have zero := empty kind (by simp)
      simpa only [List.cons_append,scan,zero,↓reduceIte] using
        ih (fun next member => empty next (by simp [member]))

/-- The source schedule check implies a real nonempty payload between any
two verifier messages, not just an unrelated absence of adjacent draws. -/
theorem scan_between (waiting finished : Bool) (pre middle suffix : List Call)
    (first second : Group)
    (ok : scan waiting (pre ++ (Call.draw first :: (middle ++ Call.draw second :: suffix))) =
      some finished) :
    ∃ kind, Call.read kind ∈ middle ∧ kind.codec.size ≠ 0 := by
  classical
  rw [scan_append] at ok
  obtain ⟨ready,_,tail⟩ := Option.bind_eq_some_iff.mp ok
  cases ready
  · simp only [scan,Bool.false_eq_true,↓reduceIte] at tail
    by_contra absent
    have empty : ∀ kind, Call.read kind ∈ middle → kind.codec.size = 0 := by
      intro kind member
      by_contra positive
      exact absent ⟨kind,member,positive⟩
    rw [scan_waiting_without_payload middle suffix second empty] at tail
    cases tail
  · simp [scan] at tail

theorem payload_nonempty (kind : WireKind) (positive : kind.codec.size ≠ 0)
    (value : kind.Value) : kind.codec.bytes value ≠ [] := by
  intro empty
  have length := congrArg List.length empty
  simp only [Codec.bytes,List.length_ofFn,List.length_nil] at length
  exact positive length

@[simp] theorem scan_fold : scan false foldSchedule = some false := by
  simp [scan,foldSchedule,WireKind.codec,vectorCodec]

@[simp] theorem scan_pow (waiting : Bool) (bits : Fin 64) :
    scan waiting (powSchedule bits) =
      if bits.val = 0 then some waiting else if waiting then none else some false := by
  by_cases zero : bits.val = 0
  · simp [powSchedule,zero,scan]
  · cases waiting <;> simp [powSchedule,zero,scan,WireKind.codec,nonceCodec]

@[simp] theorem scan_query (depth count : Nat) (bits : Fin 64) :
    scan false (querySchedule depth count bits) = some false := by
  simp only [querySchedule,scan_append,scan_pow]
  by_cases zero : bits.val = 0 <;>
    simp [zero,scan,WireKind.codec,vectorCodec]

@[simp] theorem scan_ood (dimension : Nat) :
    scan false (oodSchedule dimension) = some false := by
  by_cases zero : dimension = 0 <;>
    simp [oodSchedule,zero,scan,WireKind.codec,vectorCodec]

private theorem scan_flatMap_reset {A : Type} (xs : List A) (f : A → List Call)
    (reset : ∀ x ∈ xs, scan false (f x) = some false) :
    scan false (xs.flatMap f) = some false := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons,scan_append]
    rw [reset x (by simp)]
    simp only [Option.bind_some]
    exact ih (fun y hy => reset y (by simp [hy]))

@[simp] theorem scan_folds (rounds : Nat) :
    scan false ((List.replicate rounds foldSchedule).flatten) = some false := by
  simpa only [List.flatMap_id] using
    scan_flatMap_reset (List.replicate rounds foldSchedule) id
      (fun x member => by simpa only [(List.mem_replicate.mp member).2,id_eq] using scan_fold)

@[simp] theorem scan_root (waiting : Bool) (dimension oodCount depth count : Nat)
    (bits : Fin 64) :
    scan waiting (rootBoundarySchedule dimension oodCount depth count bits) = some false := by
  have ood : scan false ((List.replicate oodCount (oodSchedule dimension)).flatten) = some false := by
    simpa only [List.flatMap_id] using
      scan_flatMap_reset (List.replicate oodCount (oodSchedule dimension)) id
        (fun x member => by simpa only [(List.mem_replicate.mp member).2,id_eq] using scan_ood dimension)
  simp only [rootBoundarySchedule,List.cons_append,List.nil_append,scan,
    WireKind.codec,rootCodec,show ¬(32 : Nat) = 0 by decide,↓reduceIte,
    scan_append,ood,Option.bind_some,scan_query]

/-- Every repeated fold absorbs two real E values before another verifier
message; every root boundary also begins with a raw32 prover message. -/
theorem scan_intermediate (stages : List (Nat × Boundary)) :
    scan false (stages.flatMap (fun stage =>
      (List.replicate stage.1 foldSchedule).flatten ++ stage.2.schedule)) = some false := by
  apply scan_flatMap_reset
  intro stage _
  simp [scan_append,Boundary.schedule]

private theorem scan_residual_from (start rounds : Nat) :
    scan false ((List.range' start rounds).flatMap (fun j =>
      [.draw .residualFold] ++
        if j+1 < start+rounds then [.read (.vector 2)] else [])) =
      some (decide (rounds ≠ 0)) := by
  induction rounds generalizing start with
  | zero => simp [scan]
  | succ rounds ih =>
    cases rounds with
    | zero => simp [List.range'_succ,scan]
    | succ rounds =>
      have first : start+1 < start+(rounds+1+1) := by omega
      simpa [List.range'_succ,List.flatMap_cons,first,scan,WireKind.codec,vectorCodec,
        Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using ih (start+1)

theorem scan_residual (rounds : Nat) :
    scan false (residualSchedule rounds) = some (decide (rounds ≠ 0)) := by
  simpa [residualSchedule,List.range_eq_range'] using scan_residual_from 0 rounds

theorem scan_final (waiting : Bool) (dimension depth count : Nat) (bits : Fin 64) :
    scan waiting (finalBoundarySchedule dimension depth count bits) =
      some (decide (dimension ≠ 0)) := by
  simp [finalBoundarySchedule,scan_append,scan,WireKind.codec,vectorCodec,
    scan_query,scan_residual]

/-- Every scheduled current PCS verifier message is separated from the next
by a nonempty actual prover payload. A final residual draw needs no following
payload, and absent PoW introduces no extra verifier round. -/
theorem scan_opening (layout : OpeningLayout) :
    scan false layout.schedule = some (decide (layout.residualDimension ≠ 0)) := by
  have boundary : scan false layout.firstBoundary.schedule = some false := by
    simp [Boundary.schedule]
  simp [OpeningLayout.schedule,scan_append,scan,WireKind.codec,vectorCodec,
    boundary,scan_intermediate,scan_final]

theorem opening_between (layout : OpeningLayout) (pre middle suffix : List Call)
    (first second : Group)
    (scheduled : layout.schedule =
      pre ++ (Call.draw first :: (middle ++ Call.draw second :: suffix))) :
    ∃ kind, Call.read kind ∈ middle ∧ ∀ value : kind.Value, kind.codec.bytes value ≠ [] := by
  have safe := scan_opening layout
  rw [scheduled] at safe
  obtain ⟨kind,member,positive⟩ := scan_between false _ pre middle suffix first second safe
  exact ⟨kind,member,payload_nonempty kind positive⟩

/-- A nonempty prover message following a positive draw cannot reuse any
output coordinate from that draw's history, even when the prior draw stopped
partway through a 32-byte output block. -/
theorem prover_message_adds_history (m : Pending) (n : Nat) (positive : n ≠ 0)
    (bytes : List Byte) (nonempty : bytes ≠ []) :
    ((close (SpongefishPCSRoundFrames.bind (draw m n) bytes)).core.history.frames).length =
      ((close m).core.history.frames).length + 1 := by
  simp only [draw,positive,↓reduceIte,SpongefishPCSRoundFrames.bind,nonempty,
    close,Pending.core]
  simp [nonempty,List.map_append]

theorem distinct_history_after_prover (m : Pending) (n : Nat) (positive : n ≠ 0)
    (bytes : List Byte) (nonempty : bytes ≠ []) (beforeBlock afterBlock : Nat) :
    SpongefishCurrentModeQueries.coordinate m beforeBlock ≠
      SpongefishCurrentModeQueries.coordinate
        (SpongefishPCSRoundFrames.bind (draw m n) bytes) afterBlock := by
  intro equal
  have len := congrArg (fun q : Coordinate => q.history.frames.length) equal
  have grew := prover_message_adds_history m n positive bytes nonempty
  simp only [SpongefishCurrentModeQueries.coordinate] at len
  omega

/-- Both raw keys are literal full-IV/template encodings of admissible source
coordinates. Their inequality is derived from the prover-message boundary,
not from a hash-collision assumption or a different output index. -/
theorem distinct_raw_key_after_prover {Q : Nat} (parameter : Digest32)
    (m : Pending) (n : Nat) (positive : n ≠ 0) (bytes : List Byte) (nonempty : bytes ≠ [])
    (beforeBlock afterBlock : Nat)
    (beforeValid : DuplexEncoding.Admissible (SpongefishCurrentModeQueries.coordinate m beforeBlock))
    (afterValid : DuplexEncoding.Admissible (SpongefishCurrentModeQueries.coordinate
      (SpongefishPCSRoundFrames.bind (draw m n) bytes) afterBlock))
    (beforeBound : DuplexFraming.pathCost (SpongefishCurrentModeQueries.coordinate m beforeBlock) ≤ Q)
    (afterBound : DuplexFraming.pathCost (SpongefishCurrentModeQueries.coordinate
      (SpongefishPCSRoundFrames.bind (draw m n) bytes) afterBlock) ≤ Q) :
    DuplexModeGame.constructionKey Q parameter (SpongefishCurrentModeQueries.coordinate m beforeBlock) beforeBound ≠
      DuplexModeGame.constructionKey Q parameter (SpongefishCurrentModeQueries.coordinate
        (SpongefishPCSRoundFrames.bind (draw m n) bytes) afterBlock) afterBound := by
  intro equal
  have decoded := congrArg (WHIRHeaderRoots.decodeRaw parameter) equal
  rw [WHIRHeaderRoots.decodeRaw_construction parameter _ beforeValid beforeBound,
    WHIRHeaderRoots.decodeRaw_construction parameter _ afterValid afterBound] at decoded
  exact distinct_history_after_prover m n positive bytes nonempty beforeBlock afterBlock
    (Option.some.inj decoded)

#print axioms scan_append
#print axioms scan_intermediate
#print axioms scan_opening
#print axioms opening_between
#print axioms prover_message_adds_history
#print axioms distinct_history_after_prover
#print axioms distinct_raw_key_after_prover
end Whir.SpongefishCurrentRoundSeparation
