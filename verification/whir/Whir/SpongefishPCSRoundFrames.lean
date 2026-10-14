import Whir.SpongefishPowAdapter
import Whir.PublicMerkleProgram
import Whir.RawOracleCoupling

/-! Current #607 PCS round/cursor bridge, source-inspected at
`75d4562bde1efe296b4e32d2a195fdfc232b3ead`. This is NOT a universal Rust
refinement, a construction-uniformity claim, or a current SourceDriver theorem.
The finite laws below are exact byte-coordinate pushforwards: they do not
assume that the deployed BLAKE sponge produces independent uniform bytes.

Callsite pins (paths relative to crates/):
* pcs/src/stack.rs:291-296,415-418: record binding, gamma, six map E, lambda;
  pcs/src/ring_switch.rs:49,541-545,562-564 fixes the six-map order.
* pcs/src/whir/prove.rs:125-131,150-163,201-216,235-244,263-271,293:
  start quadratic; fold E/next quadratic; raw root; OOD; PoW; queries/lambda;
  residual before final queries; no polynomial after the last residual draw.
* pcs/src/whir/verify.rs:250-251,277-280,475-477,487-492,518,561-575:
  same generic OpeningVerifier calls for native and Rows.
* pcs/src/whir/mod.rs:91-100,111-131: all three E limbs, disjoint chunks,
  fixed-count strata, neither sorting nor deduplication.
* pcs/src/verifier.rs:100-105 and leanvm_core/src/rec/verifier/mod.rs:
  153-164,226-251: native/Rows root32, E192, same query grouping.
* fiat_shamir/src/arith.rs:327-335,351-362: only c0,c2 are sent for
  the unweighted quadratic. Reconstructed c1 is not an absorbed message.
* fiat_shamir/src/verifier.rs:88-107,155-163,177-185: successful canonical
  read absorbs the exact consumed bytes; positive PoW raw32 then LE u64.
* leanvm_core/src/rec/transcript.rs:185-204,224-239: identical whole-word
  messages/draws; positive trial constrains the first digest word.

Bridge hypotheses are explicit: canonical successful reads, successful guarded
squeezes, and initial Represents. Source poisoning, malformed reads, hints/EOF,
Rows free-wire constraints, and a whole-current-event compiler are not proved
here. Session derivation is separately charged by derivationPrimitiveCost;
the session ID may be a fixed model domain only after that ordinary query path
has been accounted for. A whole-current wrapper must retain a dynamic domain
registry when the observed derive answer selects the session ID; this module
does not condition that answer to a fixed registry domain. The current typed
grammar cannot express the old Scalar24 nonce or role7/8/9 terminals. -/
namespace Whir.SpongefishPCSRoundFrames
open FiatShamirGame Concrete DuplexRefinement SpongefishSessionAdapter
open scoped BigOperators
set_option autoImplicit false

def sourceRevision : String := SpongefishSessionAdapter.sourceRevision

/-- A distinct type-level profile: no implicit historical codec conversion. -/
inductive CodecVersion where | current607 | historical552
  deriving DecidableEq

def currentVersion : CodecVersion := .current607

/-- SHA256 pins of the inspected actual source, not generated-code evidence. -/
def sourcePins : List (String × String) :=
  [("pcs/src/whir/prove.rs","4335eb6728ebd7916bb14d086cc4b104e5a547162173316b81cbca97fec7d5d1"),
   ("pcs/src/whir/verify.rs","7cb2b200249e3cd842d61aa1b7cf1feb702e1c2ebc03812649a6eb5a5a712add"),
   ("pcs/src/whir/mod.rs","990f4a99bca7b4079043ab224972313075ba15fa2172a646fd8de5e91063c327"),
   ("pcs/src/whir/commit.rs","e59c1d4052925af940c50166e47baf04024fec41eed745b22f8c86443c5d90bc"),
   ("pcs/src/verifier.rs","9e4fb7af8e0180fb575e2f77017632e3808cfdab4f94e4d3a488231dc2b5cdbb"),
   ("pcs/src/stack.rs","5d63bc7203f01a97b0823c3c33b874f35ff2e355bcd6334afb4a08ea83e4db27"),
   ("pcs/src/ring_switch.rs","422657fcb5045503f4cf203348224693b6f2e9dfe27cc02c3d0de0eaa29b8a02"),
   ("leanvm_core/src/rec/verifier/mod.rs","9c81bd01362cfce4cefce0b771f8b169d222d346a5979dbccc7bc62b90cecf44"),
   ("leanvm_core/src/rec/transcript.rs","bf770f07c3b85640e01b6d855a4aab069fb848206a3826ed69e29b09c646c894"),
   ("fiat_shamir/src/arith.rs","9a98c7470d8ba45c6cc8a0c236b3a2250ab8211a73253883242db75901d8e6f2"),
   ("fiat_shamir/src/verifier.rs","afeeef22f1bb90b5142edc076ecc23a525d7efa5310bd6d2511d242e09f97fd9"),
   ("fiat_shamir/src/prover.rs","d6d54b2ffa18dbebfaf085be6fb3e4b9364bb6fd28f395aa14c76860f421d3a8")]


/-- The only completed frame of the deployed ordinary byte grammar. -/
inductive ByteFrame where
  | absorb (previousConsumed : Nat) (bytes : List Byte)
  deriving DecidableEq

def ByteFrame.historicalCore : ByteFrame → Frame
  | .absorb previous bytes => .absorb previous bytes

structure Pending where
  domain : Digest32
  frames : List ByteFrame := []
  run : List Byte := []
  previous : Nat := 0
  consumed : Nat := 0

def Pending.core (m : Pending) : Model :=
  ⟨⟨m.domain,zeroDigest,m.frames.map ByteFrame.historicalCore⟩,
    m.run,m.previous,m.consumed⟩

def close (m : Pending) : Pending :=
  if m.run = [] then m else
    {m with frames := m.frames ++ [.absorb m.previous m.run], run := [], previous := 0}

def bind (m : Pending) (bs : List Byte) : Pending :=
  if bs = [] then m else
    {m with
      run := m.run ++ bs
      previous := if m.consumed = 0 then m.previous else m.consumed
      consumed := 0}

def draw (m : Pending) (n : Nat) : Pending :=
  if n = 0 then m else {close m with consumed := m.consumed + n}

theorem close_core (m : Pending) : (close m).core = closeRun m.core := by
  by_cases h : m.run = [] <;> simp [close,closeRun,Pending.core,h,List.map_append,
    ByteFrame.historicalCore]

theorem bind_core (m : Pending) (bs : List Byte) :
    (bind m bs).core = modelAbsorb m.core bs := by
  by_cases h : bs = []
  · simp [bind,modelAbsorb,Pending.core,h]
  · simp [bind,modelAbsorb,Pending.core,h]
    rfl

theorem draw_core (m : Pending) (n : Nat) :
    (draw m n).core = modelSqueeze m.core n := by
  by_cases h : n = 0
  · simp [draw,modelSqueeze,h]
  · simp only [draw,modelSqueeze,h,↓reduceIte]
    rw [← close_core]
    rfl

/-- No byte of an earlier prover message is lost at a subsequent draw. -/
def retainedBytes (m : Pending) : List Byte :=
  (m.frames.flatMap fun f => match f with | .absorb _ bs => bs) ++ m.run

theorem close_retains (m : Pending) : retainedBytes (close m) = retainedBytes m := by
  by_cases h : m.run = [] <;> simp [close,retainedBytes,h,List.flatMap_append]

theorem draw_retains (m : Pending) (n : Nat) : retainedBytes (draw m n) = retainedBytes m := by
  by_cases h : n = 0
  · simp [draw,h]
  · simpa [draw,h,retainedBytes] using close_retains m

theorem bind_retains (m : Pending) (bs : List Byte) :
    retainedBytes (bind m bs) = retainedBytes m ++ bs := by
  by_cases h : bs = [] <;> simp [bind,retainedBytes,h,List.append_assoc]

def RepresentsCurrent (c : Compression) (parameter : Digest32) (m : Pending) (s : State) : Prop :=
  Represents c parameter m.core s

theorem session_bridge (c : Compression) (parameter session : Digest32) (instanceBytes : List Byte) :
    RepresentsCurrent c parameter (bind {domain := session} instanceBytes)
      (absorb c (init c parameter session) instanceBytes) := by
  unfold RepresentsCurrent
  rw [bind_core]
  exact session_represents c parameter session instanceBytes

theorem bind_bridge (c : Compression) (parameter : Digest32) (m : Pending) (s : State)
    (h : RepresentsCurrent c parameter m s) (bs : List Byte) :
    RepresentsCurrent c parameter (bind m bs) (absorb c s bs) := by
  unfold RepresentsCurrent at *
  rw [bind_core]
  exact absorb_represents c parameter m.core s h bs

theorem draw_bridge (c : Compression) (parameter : Digest32) (m : Pending) (s t : State)
    (h : RepresentsCurrent c parameter m s) (n : Nat) (bytes : List Byte)
    (ok : squeeze c s n = .ok (t,bytes)) :
    RepresentsCurrent c parameter (draw m n) t := by
  unfold RepresentsCurrent at *
  rw [draw_core]
  exact squeeze_represents c parameter m.core s t h n bytes ok

/-- Fixed-length canonical codecs; nonce is UInt64, not E/Scalar24. -/
structure Codec (A : Type) where
  size : Nat
  encode : A → Fin size → Byte
  decode : (Fin size → Byte) → A
  decode_encode : ∀ a, decode (encode a) = a
  encode_decode : ∀ bs, encode (decode bs) = bs

def scalarCodec : Codec E :=
  ⟨24,ByteCodec.encodeE,ByteCodec.decodeE,ByteCodec.decodeE_encodeE,ByteCodec.encodeE_decodeE⟩
def rootCodec : Codec Digest32 := ⟨32,id,id,fun _ => rfl,fun _ => rfl⟩
def nonceCodec : Codec UInt64 :=
  ⟨8,ByteCodec.encodeK,ByteCodec.decodeK,ByteCodec.decodeK_encodeK,ByteCodec.encodeK_decodeK⟩

def Codec.bytes {A : Type} (codec : Codec A) (a : A) : List Byte := List.ofFn (codec.encode a)
def Codec.parse {A : Type} (codec : Codec A) (bs : List Byte) : Option (A × List Byte) :=
  if h : codec.size ≤ bs.length then
    some (codec.decode (fun i => bs[i.val]'(by omega)),bs.drop codec.size)
  else none

theorem Codec.parse_append {A : Type} (codec : Codec A) (a : A) (suffix : List Byte) :
    codec.parse (codec.bytes a ++ suffix) = some (a,suffix) := by
  have len : codec.size ≤ (codec.bytes a ++ suffix).length := by simp [Codec.bytes]
  simp only [Codec.parse,len,↓reduceDIte]
  have first : (fun i : Fin codec.size =>
      (codec.bytes a ++ suffix)[i.val]'(by omega)) = codec.encode a := by
    funext i
    rw [List.getElem_append_left (by simp [Codec.bytes])]
    exact List.getElem_ofFn _
  rw [first,codec.decode_encode]
  simp [Codec.bytes]

theorem Codec.canonical_read {A : Type} (codec : Codec A) (bs rest : List Byte) (a : A)
    (ok : codec.parse bs = some (a,rest)) : bs = codec.bytes a ++ rest := by
  unfold Codec.parse at ok
  split at ok
  · rename_i h
    cases ok
    have encoded : codec.bytes (codec.decode (fun i : Fin codec.size => bs[i.val]'(by omega))) =
        bs.take codec.size := by
      simp only [Codec.bytes,codec.encode_decode]
      apply List.ext_getElem
      · simp; omega
      · intro i hi hj
        simp only [List.getElem_ofFn,List.getElem_take]
    rw [encoded]
    exact (List.take_append_drop codec.size bs).symm
  · cases ok

/-- Byte vectors and E vectors are bijective using every c0,c1,c2 byte. -/
def vectorEncode (n : Nat) (xs : Fin n → E) : Fin (n*24) → Byte := fun i =>
  ByteCodec.encodeE (xs ⟨i.val/24,by have := i.isLt; omega⟩) ⟨i.val%24,by omega⟩
def vectorDecode (n : Nat) (bs : Fin (n*24) → Byte) : Fin n → E := fun j =>
  ByteCodec.decodeE (fun i => bs ⟨j.val*24+i.val,by have := j.isLt; have := i.isLt; omega⟩)

theorem vector_decode_encode (n : Nat) (xs : Fin n → E) :
    vectorDecode n (vectorEncode n xs) = xs := by
  funext j
  unfold vectorDecode
  have first : (fun i : Fin 24 => vectorEncode n xs
      ⟨j.val*24+i.val,by have := j.isLt; have := i.isLt; omega⟩) = ByteCodec.encodeE (xs j) := by
    funext i
    simp only [vectorEncode]
    have div : (j.val*24+i.val)/24 = j.val := by omega
    have mod : (j.val*24+i.val)%24 = i.val := by omega
    simp only [div,mod]
  rw [first,ByteCodec.decodeE_encodeE]

theorem vector_encode_decode (n : Nat) (bs : Fin (n*24) → Byte) :
    vectorEncode n (vectorDecode n bs) = bs := by
  funext i
  simp only [vectorEncode,vectorDecode,ByteCodec.encodeE_decodeE]
  congr 1
  apply Fin.ext
  simpa only [Nat.mul_comm] using Nat.div_add_mod i.val 24

def vectorCodec (n : Nat) : Codec (Fin n → E) :=
  ⟨n*24,vectorEncode n,vectorDecode n,vector_decode_encode n,vector_encode_decode n⟩

def vectorEquiv (n : Nat) : (Fin (n*24) → Byte) ≃ (Fin n → E) where
  toFun := vectorDecode n
  invFun := vectorEncode n
  left_inv := vector_encode_decode n
  right_inv := vector_decode_encode n

theorem sampleVec_codec (c : Compression) (s t : State) (n : Nat)
    (bytes : Fin (n*24) → Byte)
    (ok : squeeze c s (24*n) = .ok (t,List.ofFn bytes)) :
    sampleVec c s n = .ok (t,List.ofFn (vectorDecode n bytes)) := by
  unfold sampleVec
  split
  · rename_i e hs
    rw [ok] at hs
    cases hs
  · rename_i u bs hs
    have values : (u,bs) = (t,List.ofFn bytes) := Except.ok.inj (hs.symm.trans ok)
    cases values
    apply congrArg Except.ok
    apply Prod.ext
    · rfl
    · apply congrArg List.ofFn
      funext j
      unfold vectorDecode
      apply congrArg ByteCodec.decodeE
      funext i
      simp only [List.getElem_ofFn]
      apply congrArg bytes
      apply Fin.ext
      simp only [Nat.mul_comm]


inductive WireKind where | scalar | root | nonce | vector (count : Nat)
abbrev WireKind.Value : WireKind → Type
  | .scalar => E | .root => Digest32 | .nonce => UInt64 | .vector n => Fin n → E
def WireKind.codec : (k : WireKind) → Codec k.Value
  | .scalar => scalarCodec | .root => rootCodec | .nonce => nonceCodec | .vector n => vectorCodec n
def WireKind.messages : WireKind → Nat
  | .vector n => n | _ => 1

/-- Source read counts, remaining transport, earlier outputs and exact messages
are all retained. A hint has no absorb event but remains in the public log. -/
inductive SourceEvent where
  | publicBytes (bytes : List Byte)
  | prover (kind : WireKind) (bytes : List Byte)
  | verifier (bytes : List Byte)
  | hint (bytes : List Byte)

structure Cursor where
  state : State
  pending : Pending
  narg : List Byte
  bytesRead : Nat := 0
  messagesRead : Nat := 0
  hintsRead : Nat := 0
  hints : List (List Byte) := []
  events : List SourceEvent := []

def read (c : Compression) (cur : Cursor) (kind : WireKind) : Option (Cursor × kind.Value) := do
  let (value,rest) ← kind.codec.parse cur.narg
  let bytes := kind.codec.bytes value
  pure ({cur with
    state := absorb c cur.state bytes
    pending := bind cur.pending bytes
    narg := rest
    bytesRead := cur.bytesRead + kind.codec.size
    messagesRead := cur.messagesRead + kind.messages
    events := cur.events ++ [.prover kind bytes]},value)

theorem read_append (c : Compression) (cur : Cursor) (kind : WireKind)
    (value : kind.Value) (rest : List Byte)
    (source : cur.narg = kind.codec.bytes value ++ rest) :
    read c cur kind = some ({cur with
      state := absorb c cur.state (kind.codec.bytes value),
      pending := bind cur.pending (kind.codec.bytes value), narg := rest,
      bytesRead := cur.bytesRead + kind.codec.size,
      messagesRead := cur.messagesRead + kind.messages,
      events := cur.events ++ [.prover kind (kind.codec.bytes value)]},value) := by
  simp [read,source,Codec.parse_append]

theorem read_bridge (c : Compression) (parameter : Digest32) (cur next : Cursor)
    (kind : WireKind) (value : kind.Value)
    (h : RepresentsCurrent c parameter cur.pending cur.state)
    (ok : read c cur kind = some (next,value)) :
    RepresentsCurrent c parameter next.pending next.state ∧
      cur.narg = kind.codec.bytes value ++ next.narg ∧
      next.bytesRead = cur.bytesRead + kind.codec.size ∧
      next.messagesRead = cur.messagesRead + kind.messages ∧
      next.events = cur.events ++ [.prover kind (kind.codec.bytes value)] := by
  unfold read at ok
  cases hp : kind.codec.parse cur.narg with
  | none => simp [hp] at ok
  | some pair =>
    rcases pair with ⟨v,rest⟩
    simp only [hp] at ok
    rcases ok with ⟨rfl,rfl⟩
    exact ⟨bind_bridge c parameter cur.pending cur.state h _,
      Codec.canonical_read kind.codec cur.narg rest v hp,rfl,rfl,rfl⟩

/-- Maximal ordinary uninterrupted PCS draw groups. OOD zero-dimensional
vectors issue no verifier call; a nonempty OOD group carries dimension-1. -/
inductive Group where
  | anchor (dimensionMinusOne : Nat)
  | stackFamilyAndLambda
  | fold
  | ood (dimensionMinusOne : Nat)
  | queryAndLambda (depth count : Nat)
  | residualFold
  | positivePow
  | finalDigest
  deriving DecidableEq

def queryDraws (depth count : Nat) : Nat := (count + (192/depth) - 1)/(192/depth)
def Group.elements : Group → Nat
  | .anchor d | .ood d => d+1
  | .stackFamilyAndLambda => 8
  | .fold | .residualFold => 1
  | .queryAndLambda depth count => queryDraws depth count + 1
  | .positivePow | .finalDigest => 0

def Group.bytes (g : Group) : Nat :=
  match g with | .positivePow | .finalDigest => 32 | _ => 24*g.elements

def Group.entropyBits (g : Group) : Nat := 8*g.bytes

theorem all_group_entropy_min192 (g : Group) : 192 ≤ g.entropyBits := by
  cases g <;> simp [Group.entropyBits,Group.bytes,Group.elements] <;> omega

theorem positive_pow_entropy : Group.positivePow.entropyBits = 256 := rfl

theorem group_carrier_card (g : Group) :
    Fintype.card (Fin g.bytes → Byte) = 2^g.entropyBits := by
  simp only [Fintype.card_fun,Fintype.card_fin,Byte,Group.entropyBits]
  rw [show (256 : Nat) = 2^8 by decide,← pow_mul]

def squeezeGroup (c : Compression) (cur : Cursor) (g : Group) :
    Except Error (Cursor × List Byte) := do
  let (s,bytes) ← squeeze c cur.state g.bytes
  pure ({cur with
    state := s
    pending := draw cur.pending g.bytes
    events := cur.events ++ [.verifier bytes]},bytes)

theorem group_bridge (c : Compression) (parameter : Digest32) (cur : Cursor)
    (g : Group) (s : State) (bytes : List Byte)
    (h : RepresentsCurrent c parameter cur.pending cur.state)
    (ok : squeeze c cur.state g.bytes = .ok (s,bytes)) :
    RepresentsCurrent c parameter (draw cur.pending g.bytes) s ∧
      s.consumed = cur.state.consumed + g.bytes ∧ bytes.length = g.bytes :=
  ⟨draw_bridge c parameter cur.pending cur.state s h g.bytes bytes ok,
    squeeze_exact_cursor c cur.state s g.bytes bytes ok⟩

theorem query_lambda_grouping (c : Compression) (s : State) (depth count : Nat)
    (limit : s.consumed + (Group.queryAndLambda depth count).bytes ≤ maxCursor) :
    squeeze c s (Group.queryAndLambda depth count).bytes =
      match squeeze c s (24*queryDraws depth count) with
      | .error e => .error e
      | .ok (t,xs) => match squeeze c t 24 with
        | .error e => .error e
        | .ok (u,ys) => .ok (u,xs++ys) :=
  query_lambda_concatenates c s (queryDraws depth count) limit

theorem query_chunks_length (depth : Nat) (x : E) :
    (queryChunks depth x).length = 192/depth := by simp [queryChunks]

theorem query_chunk_vector_length (depth : Nat) (xs : List E) :
    (xs.flatMap (queryChunks depth)).length = xs.length * (192/depth) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons,List.length_append,query_chunks_length,ih,List.length_cons]
    simp only [Nat.add_mul,Nat.one_mul]
    omega

/-- Native and Rows loop termination requires 1 <= depth < 64. Invalid
depth/count totalizations here are not Rust panic/overflow semantics. -/
theorem query_draws_adequate (depth count : Nat) (positive : 0 < depth) (small : depth < 64) :
    count ≤ queryDraws depth count * (192/depth) := by
  have per : 0 < 192/depth := Nat.div_pos (by omega) positive
  have rem := Nat.mod_lt (count + (192/depth) - 1) per
  have split := Nat.mod_add_div (count + (192/depth) - 1) (192/depth)
  unfold queryDraws
  rw [Nat.mul_comm]
  omega


/-- Current PoW source schedule: zero has neither a read nor a byte event.
Positive has one raw32 group followed by one canonical LE UInt64 read. -/
inductive Call where
  | read (kind : WireKind)
  | draw (group : Group)
  | hint

def powSchedule (bits : Fin 64) : List Call :=
  if bits.val = 0 then [] else [.draw .positivePow,.read .nonce]

def querySchedule (depth count : Nat) (bits : Fin 64) : List Call :=
  powSchedule bits ++ [.draw (.queryAndLambda depth count),.hint,.read (.vector 2)]

def oodSchedule (dimension : Nat) : List Call :=
  (if dimension = 0 then [] else [.draw (.ood (dimension-1))]) ++
    [.read .scalar,.read (.vector 2)]

def foldSchedule : List Call := [.draw .fold,.read (.vector 2)]
def residualSchedule (rounds : Nat) : List Call :=
  (List.range rounds).flatMap fun j =>
    [.draw .residualFold] ++ (if j+1 < rounds then [.read (.vector 2)] else [])

def rootBoundarySchedule (dimension oodCount depth count : Nat) (bits : Fin 64) : List Call :=
  [.read .root] ++ (List.replicate oodCount (oodSchedule dimension)).flatten ++
    querySchedule depth count bits

def finalBoundarySchedule (dimension depth count : Nat) (bits : Fin 64) : List Call :=
  [.read (.vector (2^dimension))] ++ querySchedule depth count bits ++ residualSchedule dimension

/-- Normalized successful-read replay, not a verifier acceptance machine.
PoW's work predicate is checked separately by checkPow below. Hints have
already been decoded successfully from the separate hint channel. -/
def takeHint (cur : Cursor) : Option Cursor :=
  match cur.hints with
  | [] => none
  | bs :: rest => some {cur with
      hints := rest
      hintsRead := cur.hintsRead + 1
      events := cur.events ++ [.hint bs]}

def publicAbsorb (c : Compression) (cur : Cursor) (bytes : List Byte) : Cursor :=
  {cur with
    state := absorb c cur.state bytes
    pending := bind cur.pending bytes
    events := cur.events ++ [.publicBytes bytes]}

def replayCall (c : Compression) (cur : Cursor) : Call → Option Cursor
  | .read kind => (read c cur kind).map Prod.fst
  | .draw g => match squeezeGroup c cur g with | .error _ => none | .ok result => some result.1
  | .hint => takeHint cur

def replayCalls (c : Compression) : Cursor → List Call → Option Cursor
  | cur, [] => some cur
  | cur, call :: calls => do
    let next ← replayCall c cur call
    replayCalls c next calls

theorem replayCall_bridge (c : Compression) (parameter : Digest32) (cur next : Cursor)
    (call : Call) (h : RepresentsCurrent c parameter cur.pending cur.state)
    (ok : replayCall c cur call = some next) :
    RepresentsCurrent c parameter next.pending next.state := by
  cases call with
  | read kind =>
    simp only [replayCall] at ok
    cases hr : read c cur kind with
    | none => simp [hr] at ok
    | some pair =>
      rcases pair with ⟨t,value⟩
      simp only [hr,Option.map_some,Option.some.injEq] at ok
      subst next
      exact (read_bridge c parameter cur t kind value h hr).1
  | draw g =>
    simp only [replayCall,squeezeGroup] at ok
    cases hs : squeeze c cur.state g.bytes with
    | error e => simp [hs] at ok
    | ok pair =>
      rcases pair with ⟨s,bytes⟩
      simp only [hs] at ok
      cases ok
      exact draw_bridge c parameter cur.pending cur.state s h g.bytes bytes hs
  | hint =>
    simp only [replayCall,takeHint] at ok
    cases hh : cur.hints with
    | nil => simp [hh] at ok
    | cons bs rest =>
      simp only [hh,Option.some.injEq] at ok
      subst next
      exact h

theorem all_round_replay_bridge (c : Compression) (parameter : Digest32)
    (cur next : Cursor) (calls : List Call)
    (h : RepresentsCurrent c parameter cur.pending cur.state)
    (ok : replayCalls c cur calls = some next) :
    RepresentsCurrent c parameter next.pending next.state := by
  induction calls generalizing cur with
  | nil =>
    simp only [replayCalls,Option.some.injEq] at ok
    subst next
    exact h
  | cons call calls ih =>
    simp only [replayCalls] at ok
    cases hc : replayCall c cur call with
    | none => simp [hc] at ok
    | some middle =>
      simp only [hc] at ok
      exact ih middle (replayCall_bridge c parameter cur middle call h hc) ok

def SourceEvent.proverBytes : SourceEvent → List Byte
  | .prover _ bytes => bytes | _ => []
def SourceEvent.proverCount : SourceEvent → Nat
  | .prover kind _ => kind.messages | _ => 0
def SourceEvent.hintCount : SourceEvent → Nat
  | .hint _ => 1 | _ => 0
def SourceEvent.model (m : Pending) : SourceEvent → Pending
  | .publicBytes bytes | .prover _ bytes => bind m bytes
  | .verifier bytes => draw m bytes.length
  | .hint _ => m

/-- An exact extension, retaining all earlier messages, outputs and counts.
This is about successful normalized source replay, not Rust acceptance. -/
def Extends (cur next : Cursor) : Prop :=
  ∃ suffix : List SourceEvent,
    next.events = cur.events ++ suffix ∧
    cur.narg = suffix.flatMap SourceEvent.proverBytes ++ next.narg ∧
    next.bytesRead = cur.bytesRead + (suffix.flatMap SourceEvent.proverBytes).length ∧
    next.messagesRead = cur.messagesRead + (suffix.map SourceEvent.proverCount).sum ∧
    next.hintsRead = cur.hintsRead + (suffix.map SourceEvent.hintCount).sum ∧
    next.pending = suffix.foldl SourceEvent.model cur.pending

theorem extends_refl (cur : Cursor) : Extends cur cur := by
  exact ⟨[],by simp⟩

theorem extends_trans (a b c : Cursor) (ab : Extends a b) (bc : Extends b c) : Extends a c := by
  rcases ab with ⟨xs,eventsAB,nargAB,bytesAB,messagesAB,hintsAB,modelAB⟩
  rcases bc with ⟨ys,eventsBC,nargBC,bytesBC,messagesBC,hintsBC,modelBC⟩
  refine ⟨xs++ys,?_,?_,?_,?_,?_,?_⟩
  · simp only [eventsBC,eventsAB,List.append_assoc]
  · rw [List.flatMap_append,List.append_assoc,nargAB,nargBC]
  · simp only [List.flatMap_append,List.length_append,bytesBC,bytesAB,Nat.add_assoc]
  · simp only [List.map_append,List.sum_append,messagesBC,messagesAB,Nat.add_assoc]
  · simp only [List.map_append,List.sum_append,hintsBC,hintsAB,Nat.add_assoc]
  · simp only [List.foldl_append,modelBC,modelAB]

theorem replayCall_transport (c : Compression) (cur next : Cursor) (call : Call)
    (ok : replayCall c cur call = some next) : Extends cur next := by
  cases call with
  | read kind =>
    cases hp : kind.codec.parse cur.narg with
    | none => simp [replayCall,read,hp] at ok
    | some pair =>
      rcases pair with ⟨value,rest⟩
      simp [replayCall,read,hp] at ok
      subst next
      refine ⟨[.prover kind (kind.codec.bytes value)],?_,?_,?_,?_,?_,?_⟩
      · rfl
      · simpa [SourceEvent.proverBytes] using Codec.canonical_read kind.codec cur.narg rest value hp
      · simp [SourceEvent.proverBytes,Codec.bytes]
      · simp [SourceEvent.proverCount]
      · simp [SourceEvent.hintCount]
      · rfl
  | draw g =>
    cases hs : squeeze c cur.state g.bytes with
    | error e => simp [replayCall,squeezeGroup,hs] at ok
    | ok pair =>
      rcases pair with ⟨s,bytes⟩
      simp [replayCall,squeezeGroup,hs] at ok
      subst next
      refine ⟨[.verifier bytes],rfl,?_,?_,?_,?_,?_⟩
      · simp [SourceEvent.proverBytes]
      · simp [SourceEvent.proverBytes]
      · simp [SourceEvent.proverCount]
      · simp [SourceEvent.hintCount]
      · simp [SourceEvent.model,(squeeze_exact_cursor c cur.state s g.bytes bytes hs).2]
  | hint =>
    cases hh : cur.hints with
    | nil => simp [replayCall,takeHint,hh] at ok
    | cons bytes rest =>
      simp [replayCall,takeHint,hh] at ok
      subst next
      refine ⟨[.hint bytes],rfl,?_,?_,?_,?_,?_⟩
      · simp [SourceEvent.proverBytes]
      · simp [SourceEvent.proverBytes]
      · simp [SourceEvent.proverCount]
      · simp [SourceEvent.hintCount]
      · rfl

theorem all_round_transport (c : Compression) (cur next : Cursor) (calls : List Call)
    (ok : replayCalls c cur calls = some next) : Extends cur next := by
  induction calls generalizing cur with
  | nil =>
    simp only [replayCalls,Option.some.injEq] at ok
    subst next
    exact extends_refl cur
  | cons call calls ih =>
    simp only [replayCalls] at ok
    cases hc : replayCall c cur call with
    | none => simp [hc] at ok
    | some middle =>
      simp only [hc] at ok
      exact extends_trans cur middle next (replayCall_transport c cur middle call hc) (ih middle ok)


/-- Every call in these schedules is one of the actual PCS/native/Rows wire
operations. Grouped vector reads preserve the individual message count. -/
def recordBindingSchedule (r : Record) : List Call :=
  [.read (.vector 3),.read .root,.read .root,.read (.vector 2),
    .read (.vector ((r.context.pending.length+23)/24)),.read (.vector r.point.length),.read .scalar]

def readBytes : Call → Nat
  | .read kind => kind.codec.size | _ => 0
def readMessages : Call → Nat
  | .read kind => kind.messages | _ => 0

theorem record_binding_bytes (r : Record) :
    ((recordBindingSchedule r).map readBytes).sum = (openingBytes r).length := by
  rw [openingBytes_length]
  simp [recordBindingSchedule,readBytes,WireKind.codec,vectorCodec,scalarCodec,rootCodec]
  omega

theorem record_binding_messages (r : Record) :
    ((recordBindingSchedule r).map readMessages).sum =
      8 + (r.context.pending.length+23)/24 + r.point.length := by
  simp [recordBindingSchedule,readMessages,WireKind.messages]
  omega

/-- Exact metadata framing shared by the native and Rows call sequence in
commit.rs:124-164,219-241. Raw root/CV and normalized pending bytes remain
in the ordinary absorb run, before any stack-family challenge. -/
theorem sourceMetadataFraming (c : Compression) (parameter : Digest32)
    (m : Pending) (s : State) (r : Record)
    (h : RepresentsCurrent c parameter m s) :
    RepresentsCurrent c parameter (bind m (openingBytes r))
      (absorbMessages c s (openingMessages r)) := by
  rw [opening_grouping]
  exact bind_bridge c parameter m s h _

theorem source_record_binding_counts (r : Record) (pointShape : r.point.length = r.shape.logN) :
    ((recordBindingSchedule r).map readBytes).sum =
        208 + 24*((r.context.pending.length+23)/24 + r.shape.logN) ∧
    ((recordBindingSchedule r).map readMessages).sum =
        8 + (r.context.pending.length+23)/24 + r.shape.logN := by
  rw [record_binding_bytes,record_binding_messages,openingBytes_length,pointShape]
  exact ⟨rfl,rfl⟩


structure Boundary where
  dimension : Nat
  oodCount : Nat
  depth : Nat
  count : Nat
  grinding : Fin 64

def Boundary.schedule (b : Boundary) : List Call :=
  rootBoundarySchedule b.dimension b.oodCount b.depth b.count b.grinding

/-- Literal current source loop layout after the record binding. Shape/config
checks and PCS equations remain upstream, not new soundness premises here. -/
structure OpeningLayout where
  initialRounds : Nat
  firstBoundary : Boundary
  intermediate : List (Nat × Boundary)
  finalFoldRounds : Nat
  residualDimension : Nat
  finalDepth : Nat
  finalCount : Nat
  finalGrinding : Fin 64

def OpeningLayout.schedule (layout : OpeningLayout) : List Call :=
  [.draw .stackFamilyAndLambda,.read (.vector 2)] ++
    (List.replicate layout.initialRounds foldSchedule).flatten ++
    layout.firstBoundary.schedule ++
    layout.intermediate.flatMap (fun stage =>
      (List.replicate stage.1 foldSchedule).flatten ++ stage.2.schedule) ++
    (List.replicate layout.finalFoldRounds foldSchedule).flatten ++
    finalBoundarySchedule layout.residualDimension layout.finalDepth layout.finalCount layout.finalGrinding

theorem all_actual_schedule_entropy (layout : OpeningLayout) (g : Group)
    (_callsite : Call.draw g ∈ layout.schedule) : 192 ≤ g.entropyBits :=
  all_group_entropy_min192 g


theorem zero_pow_schedule : powSchedule ⟨0,by decide⟩ = [] := rfl

theorem positive_pow_schedule (bits : Fin 64) (positive : bits.val ≠ 0) :
    powSchedule bits = [.draw .positivePow,.read .nonce] := by simp [powSchedule,positive]

theorem zero_query_schedule (depth count : Nat) :
    querySchedule depth count ⟨0,by decide⟩ =
      [.draw (.queryAndLambda depth count),.hint,.read (.vector 2)] := rfl

theorem positive_query_schedule (depth count : Nat) (bits : Fin 64) (positive : bits.val ≠ 0) :
    querySchedule depth count bits = [.draw .positivePow,.read .nonce,
      .draw (.queryAndLambda depth count),.hint,.read (.vector 2)] := by
  simp [querySchedule,positive_pow_schedule bits positive]

/-- Reuses the exact deployed checked trial/buffers; difficulty is not used as
verifier entropy. This helper includes predicate failures, not poisoned reads. -/
def checkPow := SpongefishPowAdapter.check

theorem positive_pow_bridge (C : DuplexModeGame.PrimitiveOracle) (parameter : Digest32)
    (m : Pending) (s t : State) (bits : Fin 64) (nonce : UInt64) (challenge : Digest32)
    (h : RepresentsCurrent (DuplexModeGame.compressionOf C) parameter m s)
    (positive : bits.val ≠ 0)
    (ok : squeeze (DuplexModeGame.compressionOf C) s 32 = .ok (t,List.ofFn challenge)) :
    checkPow C s bits nonce = .ok
      (absorb (DuplexModeGame.compressionOf C) t (SpongefishPowAdapter.nonceBytes nonce),
        SpongefishPowAdapter.clears bits (SpongefishPowAdapter.trial C challenge nonce)) ∧
    RepresentsCurrent (DuplexModeGame.compressionOf C) parameter
      (bind (draw m 32) (SpongefishPowAdapter.nonceBytes nonce))
      (absorb (DuplexModeGame.compressionOf C) t (SpongefishPowAdapter.nonceBytes nonce)) :=
  ⟨SpongefishPowAdapter.positive_checked C s t bits nonce challenge positive ok,
    bind_bridge _ parameter _ t (draw_bridge _ parameter m s t h 32 _ ok) _⟩

theorem zero_pow_bridge (C : DuplexModeGame.PrimitiveOracle) (s : State) (nonce : UInt64) :
    checkPow C s ⟨0,by decide⟩ nonce = .ok (s,true) := rfl

theorem nonce_codec_matches (nonce : UInt64) :
    nonceCodec.bytes nonce = SpongefishPowAdapter.nonceBytes nonce := rfl

theorem root_codec_matches (root : Digest32) : rootCodec.bytes root = rawRoot root := rfl

theorem scalar_codec_matches (x : E) : scalarCodec.bytes x = scalarBytes x := rfl

/-- Successful normalized source PoW cursor. Unlike the byte-event replay,
this computes the actual checked predicate and keeps the nonce-bound state
even when that predicate is false. Missing nonce transport fails the read. -/
def powCursor (C : DuplexModeGame.PrimitiveOracle) (cur : Cursor) (bits : Fin 64) :
    Option (Cursor × Bool) :=
  if bits.val = 0 then some (cur,true) else
    match squeezeGroup (DuplexModeGame.compressionOf C) cur .positivePow with
    | .error _ => none
    | .ok (challenged,bytes) => do
      let (next,nonce) ← read (DuplexModeGame.compressionOf C) challenged .nonce
      let challenge : Digest32 := fun i => bytes[i.val]?.getD 0
      pure (next,SpongefishPowAdapter.clears bits (SpongefishPowAdapter.trial C challenge nonce))

/-- The PoW predicate consumes the boxed ordinary hash at its Option boundary,
instead of repeatedly entering a function-valued trial hash for word bytes. -/
def powCursorStored (C : DuplexModeGame.PrimitiveOracle) (cur : Cursor) (bits : Fin 64) :
    Option (Cursor × Bool) :=
  if bits.val = 0 then some (cur,true) else
    match squeezeGroup (DuplexModeGame.compressionOf C) cur .positivePow with
    | .error _ => none
    | .ok (challenged,bytes) => do
      let (next,nonce) ← read (DuplexModeGame.compressionOf C) challenged .nonce
      let challenge : Digest32 := fun i => bytes[i.val]?.getD 0
      PublicMerkleProgram.withHashStored C (SpongefishPowAdapter.trialBytes challenge nonce)
        (fun digest => pure (next,SpongefishPowAdapter.clears bits digest))

@[csimp] theorem powCursor_stored : powCursor = powCursorStored := by
  funext C cur bits
  simp only [powCursor,powCursorStored,PublicMerkleProgram.withHashStored_eq,
    SpongefishPowAdapter.trial]

theorem zero_pow_cursor (C : DuplexModeGame.PrimitiveOracle) (cur : Cursor) :
    powCursor C cur ⟨0,by decide⟩ = some (cur,true) := rfl

theorem positive_pow_cursor (C : DuplexModeGame.PrimitiveOracle) (cur : Cursor)
    (bits : Fin 64) (nonce : UInt64) (challenge : Digest32) (t : State) (rest : List Byte)
    (positive : bits.val ≠ 0)
    (drawOK : squeeze (DuplexModeGame.compressionOf C) cur.state 32 = .ok (t,List.ofFn challenge))
    (readOK : cur.narg = nonceCodec.bytes nonce ++ rest) :
    powCursor C cur bits = some
      ({cur with
        state := absorb (DuplexModeGame.compressionOf C) t (nonceCodec.bytes nonce)
        pending := bind (draw cur.pending 32) (nonceCodec.bytes nonce)
        narg := rest
        bytesRead := cur.bytesRead + 8
        messagesRead := cur.messagesRead + 1
        events := cur.events ++ [.verifier (List.ofFn challenge),.prover .nonce (nonceCodec.bytes nonce)]},
        SpongefishPowAdapter.clears bits (SpongefishPowAdapter.trial C challenge nonce)) := by
  have decoded : (fun i : Fin 32 => (List.ofFn challenge)[i.val]?.getD 0) = challenge := by
    funext i
    simp only [List.getElem?_ofFn,dite_eq_left i.isLt,Option.getD_some]
  simp only [powCursor,positive,↓reduceIte,squeezeGroup,Group.bytes,drawOK]
  dsimp only [Bind.bind,Pure.pure,Except.instMonad,Except.bind,Except.pure]
  simp only [read,WireKind.codec]
  dsimp only [Bind.bind,Pure.pure]
  rw [readOK,Codec.parse_append]
  simp only [Option.bind_some]
  rw [decoded]
  simp only [WireKind.messages,List.append_assoc]
  rfl


/-- Exact finite fresh-vector law, not a premise asserting uniformity. The
coordinate space is literal bytes and the inverse codec is proved above. -/
private noncomputable instance : Fintype E :=
  Fintype.ofEquiv Scalar24
    {toFun := ByteCodec.decodeE, invFun := ByteCodec.encodeE,
      left_inv := ByteCodec.encodeE_decodeE, right_inv := ByteCodec.decodeE_encodeE}

theorem full_vector_distribution (n : Nat) (payoff : (Fin n → E) → ℚ) :
    average (fun bs : Fin (n*24) → Byte => payoff (vectorDecode n bs)) = average payoff :=
  RawOracleCoupling.average_equiv (vectorEquiv n) payoff

def Codec.equiv {A : Type} (codec : Codec A) : (Fin codec.size → Byte) ≃ A where
  toFun := codec.decode
  invFun := codec.encode
  left_inv := codec.encode_decode
  right_inv := codec.decode_encode

def Group.Response (g : Group) : Type :=
  match g with | .positivePow | .finalDigest => Digest32 | _ => Fin g.elements → E

def Group.codec (g : Group) : Codec g.Response :=
  match g with
  | .positivePow | .finalDigest => rootCodec
  | .anchor d | .ood d => vectorCodec (d+1)
  | .stackFamilyAndLambda => vectorCodec 8
  | .fold | .residualFold => vectorCodec 1
  | .queryAndLambda depth count => vectorCodec (queryDraws depth count+1)

private noncomputable instance (g : Group) : Fintype g.Response := by
  cases g <;> dsimp [Group.Response,Group.elements] <;> infer_instance

theorem group_codec_size (g : Group) : g.codec.size = g.bytes := by
  cases g <;> simp [Group.codec,Group.bytes,Group.elements,vectorCodec,rootCodec,Nat.mul_comm]

/-- All current groups, including raw32 PoW/digest and stack's eight E, have
their checked finite byte-codec law. No uniformity hypothesis is introduced. -/
theorem all_group_distribution (g : Group) (payoff : g.Response → ℚ) :
    average (fun bs : Fin g.codec.size → Byte => payoff (g.codec.decode bs)) = average payoff :=
  RawOracleCoupling.average_equiv g.codec.equiv payoff

theorem all_group_response_card (g : Group) :
    Fintype.card g.Response = 2^g.entropyBits := by
  rw [← Fintype.card_congr g.codec.equiv,group_codec_size,group_carrier_card]

/-- The exact atom law in the finite byte experiment, hence minimum entropy
192 for every nonempty actual group. Not a law of fixed BLAKE outputs. -/
noncomputable def groupAtom (g : Group) (x : g.Response) : ℚ := by
  classical
  exact average (fun bs : Fin g.codec.size → Byte => if g.codec.decode bs = x then 1 else 0)

theorem all_group_atom_law (g : Group) (x : g.Response) :
    groupAtom g x = 1/(2^g.entropyBits : Nat) := by
  classical
  unfold groupAtom
  rw [all_group_distribution g (fun y => if y = x then 1 else 0)]
  simp [average,all_group_response_card]



/-- Query positions have the exact source pushforward law. This intentionally
makes no iid/unstratified-query claim: count controls both chunks and strata. -/
def queryProjection (depth count : Nat) (xs : Fin (queryDraws depth count + 1) → E) :
    List Nat × E :=
  (projectQueries count depth (List.ofFn fun i : Fin (queryDraws depth count) =>
    xs ⟨i.val,by omega⟩),xs ⟨queryDraws depth count,by omega⟩)

theorem query_projection_distribution (depth count : Nat) (payoff : (List Nat × E) → ℚ) :
    average (fun bs : Fin ((queryDraws depth count+1)*24) → Byte =>
      payoff (queryProjection depth count (vectorDecode _ bs))) =
      average (fun xs : Fin (queryDraws depth count+1) → E =>
        payoff (queryProjection depth count xs)) :=
  full_vector_distribution (queryDraws depth count+1)
    (fun xs => payoff (queryProjection depth count xs))

theorem query_distribution_retains_history (cur : Cursor) (depth count : Nat)
    (payoff : Cursor → (List Nat × E) → ℚ) :
    average (fun bs : Fin ((queryDraws depth count+1)*24) → Byte =>
      payoff cur (queryProjection depth count (vectorDecode _ bs))) =
    average (fun xs : Fin (queryDraws depth count+1) → E =>
      payoff cur (queryProjection depth count xs)) :=
  query_projection_distribution depth count (payoff cur)


/-- Prefix causality includes ALL earlier prover bytes/output events and read
counts; later events cannot change the captured prefix. -/
def publicPrefix (cur : Cursor) (later : List SourceEvent) : List SourceEvent :=
  (cur.events ++ later).take cur.events.length

theorem source_prefix_causality (cur : Cursor) (later : List SourceEvent) :
    publicPrefix cur later = cur.events := by simp [publicPrefix]

theorem query_prefix_causality (count depth : Nat) (xs ys : List E)
    (enough : count ≤ (xs.flatMap (queryChunks depth)).length) :
    projectQueries count depth (xs++ys) = projectQueries count depth xs :=
  projected_query_causality count depth xs ys enough

theorem current_query_causality (depth count : Nat) (positive : 0 < depth) (small : depth < 64)
    (xs : Fin (queryDraws depth count) → E) (later : List E) :
    projectQueries count depth (List.ofFn xs ++ later) =
      projectQueries count depth (List.ofFn xs) := by
  apply projected_query_causality
  rw [query_chunk_vector_length,List.length_ofFn]
  exact query_draws_adequate depth count positive small


/-- Session derivation is NOT folded into a zero-cost domain selection. -/
theorem separate_session_charge (tag : List Byte) :
    derivationPrimitiveCost tag + 1 = 3 + (tag.length+63)/64 := by
  rw [derivation_cost_closed]
  omega

#print axioms session_bridge
#print axioms read_bridge
#print axioms group_bridge
#print axioms all_group_entropy_min192
#print axioms group_carrier_card
#print axioms query_lambda_grouping
#print axioms positive_pow_bridge
#print axioms full_vector_distribution
#print axioms query_projection_distribution
#print axioms source_prefix_causality
#print axioms query_prefix_causality
#print axioms separate_session_charge
#print axioms query_draws_adequate
#print axioms all_round_replay_bridge
#print axioms record_binding_bytes
#print axioms record_binding_messages
#print axioms all_actual_schedule_entropy
#print axioms all_group_distribution
#print axioms all_round_transport
#print axioms sampleVec_codec
#print axioms zero_pow_cursor
#print axioms positive_pow_cursor
#print axioms all_group_response_card
#print axioms all_group_atom_law
#print axioms query_distribution_retains_history
#print axioms current_query_causality
#print axioms sourceMetadataFraming
#print axioms source_record_binding_counts
end Whir.SpongefishPCSRoundFrames
