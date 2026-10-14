import Whir.SpongefishOrdinarySession
import Whir.PublicCompressionProgram

/-! Executable primitive-event hand-port for the current #607 byte cursor at
75d4562bde1efe296b4e32d2a195fdfc232b3ead. Every compression is an observed
literal primitive query. Arbitrary pre-existing pending/output buffers are
retained. The checked codec rejects insufficient transport before absorption;
its canonical dictionaries are bijective, not a model of additional Rust
malformed-field checks. Hints are the already-decoded separate source channel.
No mode-coupling, whole native acceptance, Rows, or Aeneas join is asserted. -/
namespace Whir.SpongefishCurrentPrimitiveEventCompiler
open FiatShamirGame DuplexRefinement DuplexModeGame SpongefishPCSRoundFrames
set_option autoImplicit false

abbrev seq {A B : Type} := @WHIRModeFinal.bind A B

/-- The only primitive entry point: the literal complete compression node. -/
def primitive (cv : Digest32) (block : Block64) (tweak : UInt64)
    (last : Bool) : Program Digest32 :=
  .ask (.primitive .auxiliary ⟨cv,block,tweak,last⟩) Program.done

@[simp] theorem primitive_real (C : PrimitiveOracle) (iv cv : Digest32)
    (block : Block64) (tweak : UInt64) (last : Bool) :
    (runReal C iv (primitive cv block tweak last)).view.result =
      compressionOf C cv block tweak last := rfl

/-- Consumed output is moved into the previous-frame cursor before the full
pending block is tested, exactly as in absorbByte. -/
def absorbByteProgram (s : State) (b : Byte) : Program State :=
  let s := if s.consumed = 0 then s else {s with previous := s.consumed, consumed := 0}
  if s.pending.size = 64 then
    seq (primitive s.cv (padded s.pending) (absorbTweak s.first false 64 s.previous) true)
      (fun d => .done {s with cv := d, pending := #[b], first := false, previous := 0})
  else .done {s with pending := s.pending.push b}

def absorbProgram : State → List Byte → Program State
  | s, [] => .done s
  | s, b :: bs => seq (absorbByteProgram s b) (fun t => absorbProgram t bs)

def finishProgram (s : State) : Program State :=
  if s.pending.isEmpty then .done s else
    seq (primitive s.cv (padded s.pending)
      (absorbTweak s.first true s.pending.size s.previous) true)
      (fun d => .done {s with cv := d, pending := #[], first := true, previous := 0})

def squeezeByteProgram (s : State) : Program (State × Byte) :=
  let next := fun d => Program.done
    ({s with output := d, consumed := s.consumed + 1},
      d ⟨s.consumed % 32, Nat.mod_lt _ (by decide)⟩)
  if s.consumed % 32 = 0 then
    seq (primitive s.cv (wordsBlock [s.consumed / 32]) (UInt64.ofNat (6*2^56)) true) next
  else next s.output

def squeezeLoopProgram : Nat → State → Program (State × List Byte)
  | 0, s => .done (s, [])
  | n+1, s => seq (squeezeByteProgram s) (fun (t,b) =>
      seq (squeezeLoopProgram n t) (fun (u,bs) => .done (u,b::bs)))

/-- Both guards precede finalization, including on arbitrary malformed states. -/
def squeezeProgram (s : State) (n : Nat) : Program (Except Error (State × List Byte)) :=
  if n = 0 then .done (.ok (s, []))
  else if s.consumed + n ≤ maxCursor then
    seq (finishProgram s) (fun t =>
      seq (squeezeLoopProgram n t) (fun result => .done (.ok result)))
  else .done (.error .cursorExhausted)

@[simp] theorem absorbByteProgram_real (C : PrimitiveOracle) (iv : Digest32)
    (s : State) (b : Byte) :
    (runReal C iv (absorbByteProgram s b)).view.result = absorbByte (compressionOf C) s b := by
  simp only [absorbByteProgram,absorbByte]
  split <;> split <;>
    simp [seq,WHIRModeFinal.bind_real_result,primitive_real,runReal]

@[simp] theorem absorbProgram_real (C : PrimitiveOracle) (iv : Digest32)
    (s : State) (bs : List Byte) :
    (runReal C iv (absorbProgram s bs)).view.result = absorb (compressionOf C) s bs := by
  induction bs generalizing s with
  | nil => rfl
  | cons b bs ih =>
    simp only [absorbProgram,seq,WHIRModeFinal.bind_real_result,absorbByteProgram_real,ih,
      absorb,List.foldl_cons]

@[simp] theorem finishProgram_real (C : PrimitiveOracle) (iv : Digest32) (s : State) :
    (runReal C iv (finishProgram s)).view.result = finish (compressionOf C) s := by
  simp only [finishProgram,finish,finalized]
  split <;> simp_all [seq,WHIRModeFinal.bind_real_result,primitive_real,runReal]

@[simp] theorem squeezeByteProgram_real (C : PrimitiveOracle) (iv : Digest32) (s : State) :
    (runReal C iv (squeezeByteProgram s)).view.result = squeezeByte (compressionOf C) s := by
  simp only [squeezeByteProgram,squeezeByte,outputBlock]
  split <;> simp_all [seq,WHIRModeFinal.bind_real_result,primitive_real,runReal]

@[simp] theorem squeezeLoopProgram_real (C : PrimitiveOracle) (iv : Digest32)
    (n : Nat) (s : State) :
    (runReal C iv (squeezeLoopProgram n s)).view.result = squeezeLoop (compressionOf C) n s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp [squeezeLoopProgram,seq,WHIRModeFinal.bind_real_result,squeezeLoop,ih,runReal]

@[simp] theorem squeezeProgram_real (C : PrimitiveOracle) (iv : Digest32)
    (s : State) (n : Nat) :
    (runReal C iv (squeezeProgram s n)).view.result = squeeze (compressionOf C) s n := by
  unfold squeezeProgram squeeze
  split
  · rfl
  · split
    · simp [seq,WHIRModeFinal.bind_real_result,runReal]
    · rfl

/-- Parse is performed before constructing any absorb program. -/
def readProgram (cur : Cursor) (kind : WireKind) : Program (Option (Cursor × kind.Value)) :=
  match kind.codec.parse cur.narg with
  | none => .done none
  | some (value,rest) =>
    let bytes := kind.codec.bytes value
    seq (absorbProgram cur.state bytes) (fun s => .done (some
      ({cur with
        state := s
        pending := bind cur.pending bytes
        narg := rest
        bytesRead := cur.bytesRead + kind.codec.size
        messagesRead := cur.messagesRead + kind.messages
        events := cur.events ++ [.prover kind bytes]},value)))

def squeezeGroupProgram (cur : Cursor) (g : Group) : Program (Except Error (Cursor × List Byte)) :=
  seq (squeezeProgram cur.state g.bytes) (fun result => .done (match result with
    | .error e => .error e
    | .ok (s,bytes) => .ok ({cur with
        state := s
        pending := draw cur.pending g.bytes
        events := cur.events ++ [.verifier bytes]},bytes)))

def hintProgram (cur : Cursor) : Program (Option Cursor) := .done (takeHint cur)

def publicAbsorbProgram (cur : Cursor) (bytes : List Byte) : Program Cursor :=
  seq (absorbProgram cur.state bytes) (fun s => .done
    {cur with
      state := s
      pending := bind cur.pending bytes
      events := cur.events ++ [.publicBytes bytes]})

@[simp] theorem readProgram_real (C : PrimitiveOracle) (iv : Digest32)
    (cur : Cursor) (kind : WireKind) :
    (runReal C iv (readProgram cur kind)).view.result = read (compressionOf C) cur kind := by
  unfold readProgram SpongefishPCSRoundFrames.read
  cases kind.codec.parse cur.narg with
  | none => rfl
  | some pair => rcases pair with ⟨value,rest⟩; simp [seq,WHIRModeFinal.bind_real_result,runReal]

@[simp] theorem squeezeGroupProgram_real (C : PrimitiveOracle) (iv : Digest32)
    (cur : Cursor) (g : Group) :
    (runReal C iv (squeezeGroupProgram cur g)).view.result = squeezeGroup (compressionOf C) cur g := by
  simp only [squeezeGroupProgram,seq,WHIRModeFinal.bind_real_result,squeezeProgram_real]
  unfold squeezeGroup
  cases squeeze (compressionOf C) cur.state g.bytes <;> rfl

@[simp] theorem hintProgram_real (C : PrimitiveOracle) (iv : Digest32) (cur : Cursor) :
    (runReal C iv (hintProgram cur)).view.result = takeHint cur := rfl

@[simp] theorem publicAbsorbProgram_real (C : PrimitiveOracle) (iv : Digest32)
    (cur : Cursor) (bytes : List Byte) :
    (runReal C iv (publicAbsorbProgram cur bytes)).view.result = publicAbsorb (compressionOf C) cur bytes := by
  simp [publicAbsorbProgram,seq,WHIRModeFinal.bind_real_result,runReal,publicAbsorb]

/-- Errors add diagnostics but do not reinterpret source rejection. The reached
cursor is the input to the failing call: reads and guarded draws are atomic. -/
inductive ReplayError where
  | readRejected (kind : WireKind)
  | drawRejected (error : Error)
  | missingHint

abbrev ReplayResult := Except (Cursor × ReplayError) Cursor

def callProgram (cur : Cursor) : Call → Program ReplayResult
  | .read kind => seq (readProgram cur kind) (fun result => .done (match result with
      | none => .error (cur,.readRejected kind) | some (next,_) => .ok next))
  | .draw g => seq (squeezeGroupProgram cur g) (fun result => .done (match result with
      | .error e => .error (cur,.drawRejected e) | .ok (next,_) => .ok next))
  | .hint => .done (match takeHint cur with
      | none => .error (cur,.missingHint) | some next => .ok next)

def replayProgram : Cursor → List Call → Program ReplayResult
  | cur, [] => .done (.ok cur)
  | cur, call :: calls => seq (callProgram cur call) (fun result => match result with
      | .error e => .done (.error e) | .ok next => replayProgram next calls)

/-- Instrumented actual operations, not independently supplied opening tapes. -/
def actualCall (c : Compression) (cur : Cursor) : Call → ReplayResult
  | .read kind => match read c cur kind with
      | none => .error (cur,.readRejected kind) | some (next,_) => .ok next
  | .draw g => match squeezeGroup c cur g with
      | .error e => .error (cur,.drawRejected e) | .ok (next,_) => .ok next
  | .hint => match takeHint cur with
      | none => .error (cur,.missingHint) | some next => .ok next

def actualReplay (c : Compression) : Cursor → List Call → ReplayResult
  | cur, [] => .ok cur
  | cur, call :: calls => match actualCall c cur call with
      | .error e => .error e | .ok next => actualReplay c next calls

def erase (result : ReplayResult) : Option Cursor := result.toOption

@[simp] theorem callProgram_real (C : PrimitiveOracle) (iv : Digest32)
    (cur : Cursor) (call : Call) :
    (runReal C iv (callProgram cur call)).view.result = actualCall (compressionOf C) cur call := by
  cases call <;> simp [callProgram,actualCall,seq,WHIRModeFinal.bind_real_result,runReal]

@[simp] theorem replayProgram_real (C : PrimitiveOracle) (iv : Digest32)
    (cur : Cursor) (calls : List Call) :
    (runReal C iv (replayProgram cur calls)).view.result = actualReplay (compressionOf C) cur calls := by
  induction calls generalizing cur with
  | nil => rfl
  | cons call calls ih =>
    simp only [replayProgram,seq,WHIRModeFinal.bind_real_result,callProgram_real,actualReplay]
    cases actualCall (compressionOf C) cur call <;> simp [runReal,ih]

theorem actualCall_erases (c : Compression) (cur : Cursor) (call : Call) :
    erase (actualCall c cur call) = replayCall c cur call := by
  cases call with
  | read kind =>
    simp only [actualCall,replayCall]
    cases SpongefishPCSRoundFrames.read c cur kind <;> rfl
  | draw g =>
    simp only [actualCall,replayCall]
    cases squeezeGroup c cur g <;> rfl
  | hint =>
    unfold actualCall replayCall
    cases takeHint cur <;> rfl

theorem actualReplay_erases (c : Compression) (cur : Cursor) (calls : List Call) :
    erase (actualReplay c cur calls) = replayCalls c cur calls := by
  induction calls generalizing cur with
  | nil => rfl
  | cons call calls ih =>
    simp only [actualReplay,replayCalls,← actualCall_erases]
    cases actualCall c cur call with
    | error => rfl
    | ok next => exact ih next

/-- Unconditional success AND failure correspondence, retaining the entire
reached cursor in the diagnostic result and exact source Option on erasure. -/
theorem replayProgram_source (C : PrimitiveOracle) (iv : Digest32)
    (cur : Cursor) (calls : List Call) :
    erase (runReal C iv (replayProgram cur calls)).view.result =
      replayCalls (compressionOf C) cur calls := by
  rw [replayProgram_real,actualReplay_erases]

/-- Syntactic provenance excludes any hidden construction queries. -/
def OnlyPrimitive {R : Type} : Program R → Prop
  | .done _ => True
  | .ask q next => (∃ n, q = .primitive .auxiliary n) ∧ ∀ d, OnlyPrimitive (next d)

theorem onlyPrimitive_seq {A B : Type} (p : Program A) (next : A → Program B)
    (hp : OnlyPrimitive p) (hn : ∀ a, OnlyPrimitive (next a)) : OnlyPrimitive (seq p next) := by
  induction p with
  | done a => exact hn a
  | ask q cont ih => exact ⟨hp.1,fun d => ih d (hp.2 d)⟩
theorem seq_done_counted {A B : Type} (p : Program A) (f : A → B) {Q : Nat}
    (h : Counts Q p) : Counts Q (seq p (fun a => .done (f a))) := by
  simpa using WHIRModeFinal.bind_counted p (fun a => .done (f a)) Q 0 h (fun _ => trivial)


theorem primitive_certified (cv : Digest32) (block : Block64) (tweak : UInt64) (last : Bool) :
    Counts 1 (primitive cv block tweak last) ∧ OnlyPrimitive (primitive cv block tweak last) :=
  ⟨⟨Nat.le_refl 1,fun _ => trivial⟩,⟨⟨_,rfl⟩,fun _ => trivial⟩⟩

/-- Every visited byte costs at most one primitive, even for arbitrary initial
pending buffers. This is source work, not the number of ideal raw lookups. -/
theorem absorbByteProgram_certified (s : State) (b : Byte) :
    Counts 1 (absorbByteProgram s b) ∧ OnlyPrimitive (absorbByteProgram s b) := by
  unfold absorbByteProgram
  split <;> dsimp only <;> split
  all_goals
    first
    | exact ⟨⟨Nat.le_refl 1,fun _ => trivial⟩,⟨⟨_,rfl⟩,fun _ => trivial⟩⟩
    | exact ⟨trivial,trivial⟩

theorem absorbProgram_certified (s : State) (bs : List Byte) :
    Counts bs.length (absorbProgram s bs) ∧ OnlyPrimitive (absorbProgram s bs) := by
  induction bs generalizing s with
  | nil => exact ⟨trivial,trivial⟩
  | cons b bs ih =>
    refine ⟨?_,onlyPrimitive_seq _ _ (absorbByteProgram_certified s b).2 (fun t => (ih t).2)⟩
    simpa [absorbProgram,seq,List.length_cons,Nat.add_comm] using WHIRModeFinal.bind_counted _ _ 1 bs.length
      (absorbByteProgram_certified s b).1 (fun t => (ih t).1)

theorem finishProgram_certified (s : State) :
    Counts 1 (finishProgram s) ∧ OnlyPrimitive (finishProgram s) := by
  unfold finishProgram
  split
  · exact ⟨trivial,trivial⟩
  · exact ⟨⟨Nat.le_refl 1,fun _ => trivial⟩,⟨⟨_,rfl⟩,fun _ => trivial⟩⟩

theorem squeezeByteProgram_certified (s : State) :
    Counts 1 (squeezeByteProgram s) ∧ OnlyPrimitive (squeezeByteProgram s) := by
  unfold squeezeByteProgram
  split
  · exact ⟨⟨Nat.le_refl 1,fun _ => trivial⟩,⟨⟨_,rfl⟩,fun _ => trivial⟩⟩
  · exact ⟨trivial,trivial⟩

theorem squeezeLoopProgram_certified (n : Nat) (s : State) :
    Counts n (squeezeLoopProgram n s) ∧ OnlyPrimitive (squeezeLoopProgram n s) := by
  induction n generalizing s with
  | zero => exact ⟨trivial,trivial⟩
  | succ n ih =>
    have tail : ∀ p : State × Byte, Counts n
        (seq (squeezeLoopProgram n p.1) (fun (u,bs) => .done (u,p.2::bs))) := by
      intro p
      exact seq_done_counted _ _ (ih p.1).1
    refine ⟨?_,onlyPrimitive_seq _ _ (squeezeByteProgram_certified s).2 (fun p =>
      onlyPrimitive_seq _ _ (ih p.1).2 (fun _ => trivial))⟩
    simpa [squeezeLoopProgram,seq,Nat.add_comm] using WHIRModeFinal.bind_counted _ _ 1 n
      (squeezeByteProgram_certified s).1 tail

theorem squeezeProgram_certified (s : State) (n : Nat) :
    Counts (n+1) (squeezeProgram s n) ∧ OnlyPrimitive (squeezeProgram s n) := by
  unfold squeezeProgram
  split
  · exact ⟨trivial,trivial⟩
  · split
    · refine ⟨?_,onlyPrimitive_seq _ _ (finishProgram_certified s).2 (fun t =>
        onlyPrimitive_seq _ _ (squeezeLoopProgram_certified n t).2 (fun _ => trivial))⟩
      simpa [Nat.add_comm] using WHIRModeFinal.bind_counted _ _ 1 n
        (finishProgram_certified s).1 (fun t => by
          exact seq_done_counted _ _ (squeezeLoopProgram_certified n t).1)
    · exact ⟨trivial,trivial⟩

theorem readProgram_certified (cur : Cursor) (kind : WireKind) :
    Counts kind.codec.size (readProgram cur kind) ∧ OnlyPrimitive (readProgram cur kind) := by
  unfold readProgram
  cases kind.codec.parse cur.narg with
  | none => exact ⟨trivial,trivial⟩
  | some pair =>
    rcases pair with ⟨value,rest⟩
    refine ⟨?_,onlyPrimitive_seq _ _ (absorbProgram_certified _ _).2 (fun _ => trivial)⟩
    have len : (kind.codec.bytes value).length = kind.codec.size := by simp [Codec.bytes]
    rw [← len]
    exact seq_done_counted _ _ (absorbProgram_certified _ _).1

theorem squeezeGroupProgram_certified (cur : Cursor) (g : Group) :
    Counts (g.bytes+1) (squeezeGroupProgram cur g) ∧ OnlyPrimitive (squeezeGroupProgram cur g) := by
  refine ⟨?_,onlyPrimitive_seq _ _ (squeezeProgram_certified _ _).2 (fun _ => trivial)⟩
  exact seq_done_counted _ _ (squeezeProgram_certified _ _).1

def callWork : Call → Nat
  | .read kind => kind.codec.size
  | .draw g => g.bytes+1
  | .hint => 0

def sourceBudget (calls : List Call) : Nat := (calls.map callWork).sum

theorem callProgram_certified (cur : Cursor) (call : Call) :
    Counts (callWork call) (callProgram cur call) ∧ OnlyPrimitive (callProgram cur call) := by
  cases call with
  | read kind =>
    refine ⟨?_,onlyPrimitive_seq _ _ (readProgram_certified _ _).2 (fun _ => trivial)⟩
    exact seq_done_counted _ _ (readProgram_certified _ _).1
  | draw g =>
    refine ⟨?_,onlyPrimitive_seq _ _ (squeezeGroupProgram_certified _ _).2 (fun _ => trivial)⟩
    exact seq_done_counted _ _ (squeezeGroupProgram_certified _ _).1
  | hint => exact ⟨trivial,trivial⟩

theorem replayProgram_certified (cur : Cursor) (calls : List Call) :
    Counts (sourceBudget calls) (replayProgram cur calls) ∧ OnlyPrimitive (replayProgram cur calls) := by
  induction calls generalizing cur with
  | nil => exact ⟨trivial,trivial⟩
  | cons call calls ih =>
    have tails : ∀ result : ReplayResult, Counts (sourceBudget calls)
        (match result with | .error e => Program.done (.error e) | .ok next => replayProgram next calls) := by
      intro result
      cases result with
      | error => trivial
      | ok next => exact (ih next).1
    refine ⟨?_,onlyPrimitive_seq _ _ (callProgram_certified _ _).2 (fun result => ?_)⟩
    · simpa [replayProgram,seq,sourceBudget] using WHIRModeFinal.bind_counted _ _ (callWork call) (sourceBudget calls)
        (callProgram_certified _ _).1 tails
    · cases result with
      | error => trivial
      | ok next => exact (ih next).2

/-- Observed literal nodes are answered by the same real C, and the number of
observations is exactly the primitive cost: no hidden calls, no dedup discount. -/
theorem observed_provenance {R : Type} (C : PrimitiveOracle) (iv : Digest32)
    (p : Program R) (hp : OnlyPrimitive p) :
    (∀ o ∈ (runReal C iv p).view.observations,
      ∃ n, o.query = .primitive .auxiliary n ∧ o.answer = C n) ∧
    (runReal C iv p).view.observations.length = (runReal C iv p).primitiveCost := by
  induction p with
  | done => exact ⟨by simp [runReal],rfl⟩
  | ask q next ih =>
    obtain ⟨n,rfl⟩ := hp.1
    have h := ih (C n) (hp.2 (C n))
    refine ⟨?_,?_⟩
    · intro o ho
      simp only [runReal,realAnswer,prepend,List.mem_cons] at ho
      rcases ho with rfl | ho
      · exact ⟨n,rfl,rfl⟩
      · exact h.1 o ho
    · simp only [runReal,realAnswer,prepend,Query.cost,List.length_cons]
      omega

theorem replay_observed_budget (C : PrimitiveOracle) (iv : Digest32)
    (cur : Cursor) (calls : List Call) :
    (∀ o ∈ (runReal C iv (replayProgram cur calls)).view.observations,
      ∃ n, o.query = .primitive .auxiliary n ∧ o.answer = C n) ∧
    (runReal C iv (replayProgram cur calls)).view.observations.length =
      (runReal C iv (replayProgram cur calls)).primitiveCost ∧
    (runReal C iv (replayProgram cur calls)).primitiveCost ≤ sourceBudget calls :=
  ⟨(observed_provenance C iv _ (replayProgram_certified cur calls).2).1,
    (observed_provenance C iv _ (replayProgram_certified cur calls).2).2,
    runReal_counts C iv _ _ (replayProgram_certified cur calls).1⟩

/-- Explicit linear source budget in literal read/draw bytes plus one per draw.
It does not identify these bytes with ideal construction-coordinate queries. -/
def byteWork : Call → Nat
  | .read kind => kind.codec.size
  | .draw g => g.bytes
  | .hint => 0

theorem sourceBudget_linear (calls : List Call) :
    sourceBudget calls ≤ (calls.map byteWork).sum + calls.length := by
  induction calls with
  | nil => simp [sourceBudget]
  | cons call calls ih =>
    have step : callWork call ≤ byteWork call + 1 := by cases call <;> simp [callWork,byteWork]
    simp only [sourceBudget,List.map_cons,List.sum_cons,List.length_cons] at *
    omega

theorem sourceBudget_uniform (calls : List Call) (W : Nat)
    (bounded : ∀ call ∈ calls, byteWork call ≤ W) : sourceBudget calls ≤ calls.length * (W+1) := by
  induction calls with
  | nil => simp [sourceBudget]
  | cons call calls ih =>
    have head := bounded call List.mem_cons_self
    have tail := ih (fun c hc => bounded c (List.mem_cons_of_mem _ hc))
    have step : callWork call ≤ byteWork call + 1 := by cases call <;> simp [callWork,byteWork]
    simp only [sourceBudget,List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul] at *
    omega

/-- Rejecting parse and exhausted/zero draws issue no primitive at all. -/
theorem read_rejected_before_absorb (cur : Cursor) (kind : WireKind)
    (rejected : kind.codec.parse cur.narg = none) : readProgram cur kind = .done none := by
  simp [readProgram,rejected]

theorem squeeze_zero_before_finish (s : State) : squeezeProgram s 0 = .done (.ok (s,[])) := by
  simp [squeezeProgram]

theorem squeeze_rejected_before_finish (s : State) (n : Nat)
    (positive : n ≠ 0) (exhausted : maxCursor < s.consumed+n) :
    squeezeProgram s n = .done (.error .cursorExhausted) := by
  simp [squeezeProgram,positive,Nat.not_le.mpr exhausted]

/-- Trace concatenation retains repeated nodes and rejecting-prefix work. -/
theorem seq_observations {A B : Type} (C : PrimitiveOracle) (iv : Digest32)
    (p : Program A) (next : A → Program B) :
    (runReal C iv (seq p next)).view.observations =
      (runReal C iv p).view.observations ++
        (runReal C iv (next (runReal C iv p).view.result)).view.observations := by
  induction p with
  | done => rfl
  | ask q cont ih =>
    simpa only [seq,WHIRModeFinal.bind,runReal,prepend,List.cons_append] using
      congrArg (Observation.mk q (realAnswer C iv q) :: ·) (ih (realAnswer C iv q))

def record (C : PrimitiveOracle) (n : DuplexFraming.Node) : List Observation :=
  [⟨.primitive .auxiliary n,C n⟩]

private def recordStored (C : PrimitiveOracle) (n : DuplexFraming.Node) : List Observation :=
  withDigest (C n) (fun d => [⟨.primitive .auxiliary n,d⟩])

@[csimp] private theorem record_stored : record = recordStored := by
  funext C n
  simp only [record,recordStored,withDigest_eq]

/-- These source traces compute literal nodes from the actual reached states,
not from ideal raw keys or an independently supplied opening tape. -/
def absorbByteTrace (C : PrimitiveOracle) (s : State) : List Observation :=
  let t := if s.consumed = 0 then s else {s with previous := s.consumed, consumed := 0}
  if t.pending.size = 64 then
    record C ⟨t.cv,padded t.pending,absorbTweak t.first false 64 t.previous,true⟩
  else []

def absorbTrace (C : PrimitiveOracle) : State → List Byte → List Observation
  | _, [] => []
  | s, b :: bs => absorbByteTrace C s ++ absorbTrace C (absorbByte (compressionOf C) s b) bs

def finishTrace (C : PrimitiveOracle) (s : State) : List Observation :=
  if s.pending.isEmpty then [] else
    record C ⟨s.cv,padded s.pending,absorbTweak s.first true s.pending.size s.previous,true⟩

def squeezeByteTrace (C : PrimitiveOracle) (s : State) : List Observation :=
  if s.consumed % 32 = 0 then
    record C ⟨s.cv,wordsBlock [s.consumed / 32],UInt64.ofNat (6*2^56),true⟩
  else []

def squeezeLoopTrace (C : PrimitiveOracle) : Nat → State → List Observation
  | 0, _ => []
  | n+1, s => squeezeByteTrace C s ++
      squeezeLoopTrace C n (squeezeByte (compressionOf C) s).1

def squeezeTrace (C : PrimitiveOracle) (s : State) (n : Nat) : List Observation :=
  if n = 0 then [] else if s.consumed+n ≤ maxCursor then
    finishTrace C s ++ squeezeLoopTrace C n (finish (compressionOf C) s)
  else []

@[simp] theorem absorbByteProgram_trace (C : PrimitiveOracle) (iv : Digest32) (s : State) (b : Byte) :
    (runReal C iv (absorbByteProgram s b)).view.observations = absorbByteTrace C s := by
  simp only [absorbByteProgram,absorbByteTrace]
  split <;> split <;> rfl

@[simp] theorem absorbProgram_trace (C : PrimitiveOracle) (iv : Digest32) (s : State) (bs : List Byte) :
    (runReal C iv (absorbProgram s bs)).view.observations = absorbTrace C s bs := by
  induction bs generalizing s with
  | nil => rfl
  | cons b bs ih => simp only [absorbProgram,seq_observations,absorbByteProgram_trace,
      absorbByteProgram_real,ih,absorbTrace]

@[simp] theorem finishProgram_trace (C : PrimitiveOracle) (iv : Digest32) (s : State) :
    (runReal C iv (finishProgram s)).view.observations = finishTrace C s := by
  unfold finishProgram finishTrace
  split <;> rfl

@[simp] theorem squeezeByteProgram_trace (C : PrimitiveOracle) (iv : Digest32) (s : State) :
    (runReal C iv (squeezeByteProgram s)).view.observations = squeezeByteTrace C s := by
  unfold squeezeByteProgram squeezeByteTrace
  split <;> rfl

@[simp] theorem squeezeLoopProgram_trace (C : PrimitiveOracle) (iv : Digest32) (n : Nat) (s : State) :
    (runReal C iv (squeezeLoopProgram n s)).view.observations = squeezeLoopTrace C n s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [squeezeLoopProgram,seq_observations,squeezeByteProgram_trace,
      squeezeByteProgram_real,ih,runReal,List.append_nil,squeezeLoopTrace]

@[simp] theorem squeezeProgram_trace (C : PrimitiveOracle) (iv : Digest32) (s : State) (n : Nat) :
    (runReal C iv (squeezeProgram s n)).view.observations = squeezeTrace C s n := by
  unfold squeezeProgram squeezeTrace
  split
  · rfl
  · split
    · simp only [seq_observations,finishProgram_trace,finishProgram_real,
        squeezeLoopProgram_trace,runReal,List.append_nil]
    · rfl

def callTrace (C : PrimitiveOracle) (cur : Cursor) : Call → List Observation
  | .read kind => match kind.codec.parse cur.narg with
      | none => [] | some (value,_) => absorbTrace C cur.state (kind.codec.bytes value)
  | .draw g => squeezeTrace C cur.state g.bytes
  | .hint => []

def replayTrace (C : PrimitiveOracle) : Cursor → List Call → List Observation
  | _, [] => []
  | cur, call :: calls => callTrace C cur call ++
      match actualCall (compressionOf C) cur call with
      | .error _ => [] | .ok next => replayTrace C next calls

@[simp] theorem readProgram_trace (C : PrimitiveOracle) (iv : Digest32) (cur : Cursor) (kind : WireKind) :
    (runReal C iv (readProgram cur kind)).view.observations = callTrace C cur (.read kind) := by
  simp only [readProgram,callTrace]
  cases kind.codec.parse cur.narg with
  | none => rfl
  | some pair =>
    rcases pair with ⟨value,rest⟩
    simp only [seq_observations,absorbProgram_trace,runReal,List.append_nil]

@[simp] theorem squeezeGroupProgram_trace (C : PrimitiveOracle) (iv : Digest32) (cur : Cursor) (g : Group) :
    (runReal C iv (squeezeGroupProgram cur g)).view.observations = callTrace C cur (.draw g) := by
  simp only [squeezeGroupProgram,seq_observations,squeezeProgram_trace,runReal,List.append_nil,callTrace]

@[simp] theorem callProgram_trace (C : PrimitiveOracle) (iv : Digest32) (cur : Cursor) (call : Call) :
    (runReal C iv (callProgram cur call)).view.observations = callTrace C cur call := by
  cases call <;> simp only [callProgram,seq_observations,readProgram_trace,
    squeezeGroupProgram_trace,runReal,List.append_nil,callTrace]

/-- Exact trace and exact primitive count, including the work of a rejecting
prefix. The reference trace follows only the actual source-reached cursor. -/
theorem replayProgram_trace (C : PrimitiveOracle) (iv : Digest32) (cur : Cursor) (calls : List Call) :
    (runReal C iv (replayProgram cur calls)).view.observations = replayTrace C cur calls := by
  induction calls generalizing cur with
  | nil => rfl
  | cons call calls ih =>
    simp only [replayProgram,seq_observations,callProgram_trace,callProgram_real,replayTrace]
    cases actualCall (compressionOf C) cur call <;> simp only [runReal,ih]

/-- Reference trace adapters use the same single observed execution as their
programs. Computing a separate state transition beside each record would
retain a second compression history in the returned observations. -/
private def absorbTraceStored (C : PrimitiveOracle) (s : State) (bs : List Byte) :
    List Observation := (runReal C zeroDigest (absorbProgram s bs)).view.observations

@[csimp] private theorem absorbTrace_stored : absorbTrace = absorbTraceStored := by
  funext C s bs
  exact (absorbProgram_trace C zeroDigest s bs).symm

private def squeezeLoopTraceStored (C : PrimitiveOracle) (n : Nat) (s : State) :
    List Observation := (runReal C zeroDigest (squeezeLoopProgram n s)).view.observations

@[csimp] private theorem squeezeLoopTrace_stored : squeezeLoopTrace = squeezeLoopTraceStored := by
  funext C n s
  exact (squeezeLoopProgram_trace C zeroDigest n s).symm

private def squeezeTraceStored (C : PrimitiveOracle) (s : State) (n : Nat) :
    List Observation := (runReal C zeroDigest (squeezeProgram s n)).view.observations

@[csimp] private theorem squeezeTrace_stored : squeezeTrace = squeezeTraceStored := by
  funext C s n
  exact (squeezeProgram_trace C zeroDigest s n).symm

private def callTraceStored (C : PrimitiveOracle) (cur : Cursor) (call : Call) :
    List Observation := (runReal C zeroDigest (callProgram cur call)).view.observations

@[csimp] private theorem callTrace_stored : callTrace = callTraceStored := by
  funext C cur call
  exact (callProgram_trace C zeroDigest cur call).symm

private def replayTraceStored (C : PrimitiveOracle) (cur : Cursor) (calls : List Call) :
    List Observation := (runReal C zeroDigest (replayProgram cur calls)).view.observations

@[csimp] private theorem replayTrace_stored : replayTrace = replayTraceStored := by
  funext C cur calls
  exact (replayProgram_trace C zeroDigest cur calls).symm

theorem replayProgram_exact_count (C : PrimitiveOracle) (iv : Digest32) (cur : Cursor) (calls : List Call) :
    (runReal C iv (replayProgram cur calls)).primitiveCost = (replayTrace C cur calls).length := by
  rw [← replayProgram_trace]
  exact (replay_observed_budget C iv cur calls).2.1.symm

/-- PublicCompressionProgram's executable sampling backend, with the source
budget certificate supplied internally rather than as an acceptance premise. -/
def compiledReplay (iv : Digest32) (cur : Cursor) (calls : List Call) :
    PublicCompressionProgram.Computation (Execution ReplayResult) (sourceBudget calls) :=
  PublicCompressionProgram.compile iv (replayProgram cur calls) (sourceBudget calls)
    (replayProgram_certified cur calls).1

theorem compiledReplay_real (C : PrimitiveOracle) (iv : Digest32) (cur : Cursor) (calls : List Call) :
    TypedOracleCompiler.Sampling.eval C (compiledReplay iv cur calls) = runReal C iv (replayProgram cur calls) :=
  PublicCompressionProgram.compile_eval C iv _ _ _

theorem compiledReplay_source (C : PrimitiveOracle) (iv : Digest32) (cur : Cursor) (calls : List Call) :
    (TypedOracleCompiler.Sampling.eval C (compiledReplay iv cur calls)).view.result = actualReplay (compressionOf C) cur calls := by
  rw [compiledReplay_real,replayProgram_real]

#print axioms record_stored
#print axioms absorbTrace_stored
#print axioms squeezeLoopTrace_stored
#print axioms squeezeTrace_stored
#print axioms callTrace_stored
#print axioms replayTrace_stored

#print axioms compiledReplay_real
#print axioms compiledReplay_source

#print axioms replayProgram_trace
#print axioms replayProgram_exact_count

#print axioms absorbByteProgram_real
#print axioms absorbProgram_real
#print axioms finishProgram_real
#print axioms squeezeByteProgram_real
#print axioms squeezeLoopProgram_real
#print axioms squeezeProgram_real
#print axioms readProgram_real
#print axioms squeezeGroupProgram_real
#print axioms replayProgram_real
#print axioms replayProgram_source
#print axioms replayProgram_certified
#print axioms replay_observed_budget
#print axioms sourceBudget_linear
#print axioms sourceBudget_uniform
end Whir.SpongefishCurrentPrimitiveEventCompiler
