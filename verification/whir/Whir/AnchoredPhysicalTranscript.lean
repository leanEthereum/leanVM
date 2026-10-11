import Whir.AnchoredHeaderCodec
import Whir.WHIRSourceComposition

/-! Counted physical compression source for the new immutable commit/open boundary. This hand-port uses the same public primitive interface and source-owned chronological records as the physical WHIR verifier. It does not identify an arbitrary chosen-CV primitive oracle with independent random anchor coordinates. -/
namespace Whir.AnchoredPhysicalTranscript
open Concrete FiatShamirGame DuplexRefinement DuplexFraming
open DuplexModeGame (PrimitiveOracle Query runReal compressionOf)
open WHIRSourceChronology AnchoredHeaderCodec

/-- Pure capture cannot install a cached output. The native source retains its existing private cache and only uses it under the usual CacheValid precondition. -/
def absorbByteSource (s : State) (b : Byte) : Source cap State :=
  let s := if s.consumed = 0 then s else {s with previous := s.consumed,consumed := 0}
  if s.pending.size = 64 then
    .ask (.primitive .auxiliary ⟨s.cv,padded s.pending,absorbTweak s.first false 64 s.previous,true⟩)
      (fun cv => .done {s with cv,pending := #[b],first := false,previous := 0})
  else .done {s with pending := s.pending.push b}

def absorbSource (s : State) : List Byte → Source cap State
  | [] => .done s
  | b :: rest => (absorbByteSource s b).bind (fun s => absorbSource s rest)

def finishSource (s : State) : Source cap State :=
  if s.pending.isEmpty then .done s else
    .ask (.primitive .auxiliary ⟨s.cv,padded s.pending,
      absorbTweak s.first true s.pending.size s.previous,true⟩)
      (fun cv => .done {s with cv,pending := #[],first := true,previous := 0})

def squeezeByteSource (s : State) : Source cap (State × Byte) :=
  if s.consumed % 32 = 0 then
    .ask (.primitive .auxiliary ⟨s.cv,wordsBlock [s.consumed/32],UInt64.ofNat (6*2^56),true⟩)
      (fun digest => .done ({s with consumed := s.consumed+1,output := digest},
        digest ⟨s.consumed%32,Nat.mod_lt _ (by decide)⟩))
  else .done ({s with consumed := s.consumed+1},
    s.output ⟨s.consumed%32,Nat.mod_lt _ (by decide)⟩)

def squeezeLoopSource : Nat → State → Source cap (State × List Byte)
  | 0,s => .done (s,[])
  | n+1,s => (squeezeByteSource s).bind fun (t,b) =>
      (squeezeLoopSource n t).map fun (u,bs) => (u,b::bs)

def squeezeSource (s : State) (n : Nat) : Source cap (Except DuplexRefinement.Error (State × List Byte)) :=
  if n = 0 then .done (.ok (s,[]))
  else if s.consumed+n ≤ maxCursor then
    (finishSource s).bind fun t => (squeezeLoopSource n t).map Except.ok
  else .done (.error .cursorExhausted)

def sampleVecSource (s : State) (n : Nat) : Source cap (Except DuplexRefinement.Error (State × List E)) :=
  (squeezeSource s (24*n)).map (Except.map fun (t,bytes) =>
    (t,List.ofFn (fun j : Fin n => ByteCodec.decodeE (fun i =>
      (bytes[24*j.val+i.val]?).getD 0))))

def scalarsBytes (xs : List E) : List Byte := xs.flatMap (fun x => List.ofFn (ByteCodec.encodeE x))

/-- Header parsing and shape validation happen before point sampling. Root announcement precedes the finalization and first fresh output block; its snapshot therefore cannot contain any anchor answer. Only the advertised value is read after that one point. -/
def receiveSource (expected : Shape) (s : State) (header : List E) (advertised : List E → E) :
    Source cap (Except AnchoredHeaderCodec.Error (State × Record)) :=
  if !decide expected.Valid then .done (.error .commitmentMismatch)
  else match parseHeader expected header with
  | none => .done (.error .commitmentMismatch)
  | some root =>
    (absorbSource s (scalarsBytes header)).bind fun headerState =>
      .commit root ((sampleVecSource headerState expected.logN).bind fun sampled =>
        match sampled with
        | .error _ => .done (.error .cursorExhausted)
        | .ok (pointState,point) =>
          let advertised := advertised point
          (absorbSource pointState (scalarsBytes [advertised])).map fun final =>
            .ok (final,⟨expected,root,capture s,point,advertised⟩))

/-- A fresh-session frame is absorbed only after all record fields match. An invalid or truncated record returns a literal error with no compression call and no opening batching challenge. -/
def bindingSource (expected : Shape) (record : Record) (session : State) (transport : List E) :
    Source cap (Except AnchoredHeaderCodec.Error (State × List E)) :=
  match verifyBinding expected record transport with
  | .error e => .done (.error e)
  | .ok rest => (absorbSource session (scalarsBytes (openingScalars record))).map
      (fun state => .ok (state,rest))

theorem bindingSource_rejected (expected : Shape) (record : Record) (session : State)
    (transport : List E) (e : AnchoredHeaderCodec.Error)
    (rejected : verifyBinding expected record transport = .error e) :
    bindingSource (cap := cap) expected record session transport = .done (.error e) := by
  simp [bindingSource,rejected]

theorem absorbByteSource_real (C : PrimitiveOracle) (iv : Digest32) (s : State) (b : Byte) :
    (runReal C iv (compile (absorbByteSource (cap := cap) s b))).view.result.value =
      absorbByte (compressionOf C) s b := by
  unfold absorbByteSource absorbByte
  dsimp only
  split <;> split <;> rfl

theorem finishSource_real (C : PrimitiveOracle) (iv : Digest32) (s : State) :
    (runReal C iv (compile (finishSource (cap := cap) s))).view.result.value = finish (compressionOf C) s := by
  unfold finishSource finish finalized
  split <;> rfl

theorem squeezeByteSource_real (C : PrimitiveOracle) (iv : Digest32) (s : State) :
    (runReal C iv (compile (squeezeByteSource (cap := cap) s))).view.result.value =
      squeezeByte (compressionOf C) s := by
  unfold squeezeByteSource squeezeByte outputBlock
  split <;> rfl

theorem absorbSource_real (C : PrimitiveOracle) (iv : Digest32) (s : State) (bytes : List Byte) :
    (runReal C iv (compile (absorbSource (cap := cap) s bytes))).view.result.value =
      absorb (compressionOf C) s bytes := by
  induction bytes generalizing s with
  | nil => rfl
  | cons b rest ih =>
    rw [absorbSource,Source.real_bind]
    dsimp only
    rw [absorbByteSource_real,ih]
    rfl

theorem squeezeLoopSource_real (C : PrimitiveOracle) (iv : Digest32) (n : Nat) (s : State) :
    (runReal C iv (compile (squeezeLoopSource (cap := cap) n s))).view.result.value =
      squeezeLoop (compressionOf C) n s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    rw [squeezeLoopSource,Source.real_bind]
    dsimp only
    have sampled := squeezeByteSource_real (cap := cap) C iv s
    rw [Source.real_map]
    dsimp only
    rw [ih]
    exact congrArg (fun pair : State × Byte =>
      let rest := squeezeLoop (compressionOf C) n pair.1
      (rest.1,pair.2::rest.2)) sampled

theorem squeezeSource_real (C : PrimitiveOracle) (iv : Digest32) (s : State) (n : Nat) :
    (runReal C iv (compile (squeezeSource (cap := cap) s n))).view.result.value =
      squeeze (compressionOf C) s n := by
  unfold squeezeSource squeeze
  split
  · rfl
  · split
    · rw [Source.real_bind]
      dsimp only
      have finished := finishSource_real (cap := cap) C iv s
      rw [finished,Source.real_map]
      dsimp only
      exact congrArg Except.ok (squeezeLoopSource_real (cap := cap) C iv n (finish (compressionOf C) s))
    · rfl

theorem sampleVecSource_real (C : PrimitiveOracle) (iv : Digest32) (s : State) (n : Nat) :
    (runReal C iv (compile (sampleVecSource (cap := cap) s n))).view.result.value =
      sampleVec (compressionOf C) s n := by
  rw [sampleVecSource,Source.real_map]
  dsimp only
  have squeezed := squeezeSource_real (cap := cap) C iv s (24*n)
  rw [squeezed]
  unfold sampleVec
  split
  next e sampled => simp [sampled,Except.map]
  next t bytes sampled =>
    simp only [sampled,Except.map]
    have size := (squeeze_exact_cursor (compressionOf C) s t (24*n) bytes sampled).2
    apply congrArg (fun point : List E => (Except.ok (t,point) : Except DuplexRefinement.Error (State × List E)))
    apply congrArg (@List.ofFn E n)
    funext j
    apply congrArg ByteCodec.decodeE
    funext i
    have bound : 24*j.val+i.val < bytes.length := by
      have := j.isLt
      have := i.isLt
      omega
    simp [bound]

theorem absorbByteSource_counted (s : State) (b : Byte) : Counts 1 (absorbByteSource (cap := cap) s b) := by
  unfold absorbByteSource
  dsimp only
  split <;> split <;> simp [Counts,Query.cost]

theorem absorbSource_counted (s : State) (bytes : List Byte) :
    Counts bytes.length (absorbSource (cap := cap) s bytes) := by
  induction bytes generalizing s with
  | nil => trivial
  | cons b rest ih =>
    simpa only [absorbSource,List.length_cons,Nat.add_comm] using
      Source.bind_counted (absorbByteSource s b) (fun t => absorbSource t rest) 1 rest.length
        (absorbByteSource_counted s b) ih

theorem finishSource_counted (s : State) : Counts 1 (finishSource (cap := cap) s) := by
  unfold finishSource
  split <;> simp [Counts,Query.cost]

theorem squeezeByteSource_counted (s : State) : Counts 1 (squeezeByteSource (cap := cap) s) := by
  unfold squeezeByteSource
  split <;> simp [Counts,Query.cost]

theorem squeezeLoopSource_counted (n : Nat) (s : State) :
    Counts n (squeezeLoopSource (cap := cap) n s) := by
  induction n generalizing s with
  | zero => trivial
  | succ n ih =>
    simpa only [squeezeLoopSource,Nat.add_comm] using
      Source.bind_counted (squeezeByteSource s) (fun (t,b) =>
        (squeezeLoopSource n t).map (fun (u,bs) => (u,b::bs))) 1 n
        (squeezeByteSource_counted s) (fun (t,b) => (Source.map_counted _ _ _).mpr (ih t))

theorem squeezeSource_counted (s : State) (n : Nat) :
    Counts (1+n) (squeezeSource (cap := cap) s n) := by
  unfold squeezeSource
  split
  · trivial
  · split
    · exact Source.bind_counted (finishSource s) _ 1 n (finishSource_counted s)
        (fun t => (Source.map_counted _ _ _).mpr (squeezeLoopSource_counted n t))
    · trivial

theorem sampleVecSource_counted (s : State) (n : Nat) :
    Counts (1+24*n) (sampleVecSource (cap := cap) s n) := by
  exact (Source.map_counted _ _ _).mpr (squeezeSource_counted s (24*n))

/-- This bound deliberately counts all source context and frame bytes, including the original CV and pending packs. It is conservative per byte, not the obsolete unanchored packet path cost. -/
def receiveBudget (shape : Shape) : Nat := 120 + (1+24*shape.logN) + 24

theorem receiveSource_counted (shape : Shape) (s : State) (header : List E) (advertised : List E → E) :
    Counts (receiveBudget shape) (receiveSource (cap := cap) shape s header advertised) := by
  unfold receiveSource
  split
  · trivial
  · split
    · trivial
    · rename_i root parsed
      have exactHeader := parseHeader_sound shape header root parsed
      subst header
      apply Source.bind_counted _ _ 120 (1+24*shape.logN+24)
      · have counted := absorbSource_counted (cap := cap) s (scalarsBytes (headerScalars shape root))
        simpa [scalarsBytes,headerScalars] using counted
      · intro state
        change Counts _ ((sampleVecSource state shape.logN).bind _)
        apply Source.bind_counted _ _ (1+24*shape.logN) 24 (sampleVecSource_counted state _)
        intro sampled
        cases sampled with
        | error e => trivial
        | ok result =>
          apply (Source.map_counted _ _ _).mpr
          have counted := absorbSource_counted (cap := cap) result.1 (scalarsBytes [advertised result.2])
          simpa [scalarsBytes] using counted

theorem bindingSource_counted (expected : Shape) (record : Record) (session : State) (transport : List E) :
    Counts (24*(openingScalars record).length) (bindingSource (cap := cap) expected record session transport) := by
  unfold bindingSource
  cases checked : verifyBinding expected record transport with
  | error error => trivial
  | ok rest =>
    apply (Source.map_counted _ _ _).mpr
    have bytes : (scalarsBytes (openingScalars record)).length = 24*(openingScalars record).length :=
      WHIRHistory.scalarBytes_length _
    simpa only [bytes] using absorbSource_counted (cap := cap) session (scalarsBytes (openingScalars record))

/-- Nonempty mandatory header absorption discards the old output cursor before the one original vector request. There is no externally installed output cache in the captured record. -/
theorem original_header_resets_cursor (C : DuplexRefinement.Compression) (s : State) (shape : Shape) (root : Digest32) :
    (absorb C s (scalarsBytes (headerScalars shape root))).consumed = 0 := by
  apply absorb_nonempty_cursor
  have length : (scalarsBytes (headerScalars shape root)).length = 120 := by
    change (WHIRHistory.scalarBytes (headerScalars shape root)).length = 120
    rw [WHIRHistory.scalarBytes_length,headerScalars_length]
  intro empty
  rw [empty] at length
  contradiction

end Whir.AnchoredPhysicalTranscript
