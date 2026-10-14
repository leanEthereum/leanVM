import Whir.DuplexCompression
import Whir.DuplexEncoding
import Whir.AnchoredHeaderCodec

/-! Byte adapter for native #607 at 75d4562b. This reuses only the ordinary
absorb/squeeze core of the explicitly historical #552 DuplexRefinement.
AnchoredHeaderCodec/Roots and DuplexFraming retain their historical meanings.
The adapter is a source-inspected hand port, NOT compiler equivalence, source
acceptance, extraction, an FS theorem, or an indifferentiability theorem.

Source: fiat_shamir/{session,duplex,codec,prover,verifier}.rs and
pcs/whir/commit.rs. Session derivation is a separate ordinary primitive path;
it must be charged even when the session identifier is subsequently fixed.
Historical domain/statement fields are mapped to (sessionId, zero32), NOT to
(tag, instance). The canonical nonempty instance is an ordinary absorb run.
PoW's positive difficulty draws raw32 then absorbs LE u64; zero difficulty is
no event. Historical roles 7/8/9, Scalar24 nonce, and nonmutating commitment
are NOT deployed #607 operations. A final raw32 draw is an ordinary squeeze,
not historical role7. `SpongefishPowAdapter` proves the deployed trial predicate
and checked-state transition. Nonce search, poisoned reads/hints/EOF, and the
actual source observer/reduction remain outside this session adapter. -/
namespace Whir.SpongefishSessionAdapter
open FiatShamirGame Concrete DuplexRefinement

 def sourceRevision : String := "75d4562bde1efe296b4e32d2a195fdfc232b3ead"

 def derivationIV : Digest32 := fun i =>
  ⟨("irtf-cfrg-fiat-shamir/session-id".toUTF8[i.val]!).toNat % 256,
    Nat.mod_lt _ (by decide)⟩

 def init (c : Compression) (parameter iv : Digest32) : State :=
  seed c parameter iv zeroDigest

 theorem init_node (c : Compression) (parameter iv : Digest32) :
    (init c parameter iv).cv =
      c parameter (ByteCodec.pairBytes (iv, zeroDigest)) (UInt64.ofNat (2^56)) true := rfl

 theorem init_prefix (iv : Digest32) (i : Fin 32) :
    ByteCodec.pairBytes (iv, zeroDigest) ⟨i.val, by omega⟩ = iv i := by
  simp [ByteCodec.pairBytes, i.isLt]

 theorem init_zero_suffix (iv : Digest32) (i : Fin 32) :
    ByteCodec.pairBytes (iv, zeroDigest) ⟨32+i.val, by omega⟩ = 0 := by
  simp [ByteCodec.pairBytes, zeroDigest, show ¬32+i.val < 32 by omega]

 theorem absorb_zero_cursor (c : Compression) (s : State) (bs : List Byte)
    (h : s.consumed = 0) : (absorb c s bs).consumed = 0 := by
  by_cases empty : bs = []
  · simp [empty, h]
  · exact absorb_nonempty_cursor c s bs empty

 /-- Derivation is always a valid 32-byte draw, including an empty tag. -/
 def derive (c : Compression) (parameter : Digest32) (tag : List Byte) : Digest32 :=
  let bs := (squeezeLoop c 32 (finish c (absorb c (init c parameter derivationIV) tag))).2
  fun i => bs[i.val]'(by simp only [bs, squeezeLoop_length]; exact i.isLt)

 /-- Evaluate the complete ordinary draw before handing its list-backed digest
to a data-valued consumer. A Digest32-returning derivation wrapper alone can
be eta-expanded and repeat initialization and absorption for every byte. -/
 def withDerived {Result : Type} (c : Compression) (parameter : Digest32)
    (tag : List Byte) (next : Digest32 → Result) : Result :=
  let bs := (squeezeLoop c 32 (finish c (absorb c (init c parameter derivationIV) tag))).2
  next (fun i => bs[i.val]'(by simp only [bs,squeezeLoop_length]; exact i.isLt))

 theorem withDerived_eq {Result : Type} (c : Compression) (parameter : Digest32)
    (tag : List Byte) (next : Digest32 → Result) :
    withDerived c parameter tag next = next (derive c parameter tag) := rfl

 theorem derive_checked (c : Compression) (parameter : Digest32) (tag : List Byte) :
    squeeze c (absorb c (init c parameter derivationIV) tag) 32 =
      .ok ((squeezeLoop c 32 (finish c (absorb c (init c parameter derivationIV) tag))).1,
        List.ofFn (derive c parameter tag)) := by
  have cursor := absorb_zero_cursor c (init c parameter derivationIV) tag rfl
  simp only [squeeze, show (32 : Nat) ≠ 0 by decide, cursor, maxCursor]
  simp only [show (0+32 ≤ 2^49-1) by decide, ↓reduceIte]
  congr 2

 /-- Exactly the source constructor's instance bytes; empty input panics in Rust. -/
 def newSession (c : Compression) (parameter session : Digest32) (instanceBytes : List Byte) :
    Option State :=
  if instanceBytes = [] then none else some (absorb c (init c parameter session) instanceBytes)

 theorem newSession_nonempty (c : Compression) (parameter session : Digest32)
    (instanceBytes : List Byte) (nonempty : instanceBytes ≠ []) :
    newSession c parameter session instanceBytes = some (absorb c (init c parameter session) instanceBytes) := by
  simp [newSession, nonempty]

 /-- Derived, not assumed: historical seed fields now mean sessionId and zero32.
The instance is in `modelAbsorb`, never in the old seed's second 32 bytes. -/
 theorem session_represents (c : Compression) (parameter session : Digest32)
    (instanceBytes : List Byte) :
    Represents c parameter (modelAbsorb ⟨⟨session,zeroDigest,[]⟩,[],0,0⟩ instanceBytes)
      (absorb c (init c parameter session) instanceBytes) :=
  absorb_represents c parameter _ _ (seed_represents c parameter session zeroDigest) instanceBytes

 /-- Explicit ordinary primitive plan: seed, every tag block, and output block0.
The extra one-node session initialization is NOT included here. No role7/8/9. -/
 def derivationPlan (tag : List Byte) : List DuplexEncoding.Instruction :=
  (ByteCodec.pairBytes (derivationIV,zeroDigest), UInt64.ofNat (2^56)) ::
    DuplexEncoding.chunks true 0 [] tag ++
      [(wordsBlock [0], UInt64.ofNat (6*2^56))]

 def derivationPrimitiveCost (tag : List Byte) : Nat := (derivationPlan tag).length

 theorem derivation_cost (tag : List Byte) :
    derivationPrimitiveCost tag = 2 + (DuplexEncoding.chunks true 0 [] tag).length := by
  simp [derivationPrimitiveCost, derivationPlan]; omega

 theorem derivation_empty_cost : derivationPrimitiveCost [] = 2 := by
  simp [derivationPrimitiveCost, derivationPlan, DuplexEncoding.chunks]

 theorem derivation_and_session_init_cost (tag : List Byte) :
    derivationPrimitiveCost tag + 1 =
      3 + (DuplexEncoding.chunks true 0 [] tag).length := by rw [derivation_cost]; omega

 def scalarBytes (x : E) : List Byte := List.ofFn (ByteCodec.encodeE x)
 def scalarsBytes (xs : List E) : List Byte := xs.flatMap scalarBytes
 def rawRoot (root : Digest32) : List Byte := List.ofFn root
 /-- Number of ordinary absorb nodes, including the delayed final block. -/
 theorem chunks_length (first : Bool) (previous : Nat) (pending bs : List Byte)
    (bounded : pending.length ≤ 64) :
    (DuplexEncoding.chunks first previous pending bs).length =
      (pending.length + bs.length + 63)/64 := by
  induction bs generalizing first previous pending with
  | nil =>
    by_cases empty : pending = []
    · simp [DuplexEncoding.chunks, empty]
    · have positive : 0 < pending.length := List.length_pos_iff.mpr empty
      simp only [DuplexEncoding.chunks, empty, ↓reduceIte, List.length_cons, List.length_nil]
      omega
  | cons b bs ih =>
    by_cases full : pending.length = 64
    · simp only [DuplexEncoding.chunks, full, ↓reduceIte, List.length_cons]
      rw [ih false 0 [b] (by simp)]
      simp only [List.length_cons, List.length_nil]
      omega
    · simp only [DuplexEncoding.chunks, full, ↓reduceIte]
      rw [ih first previous (pending++[b]) (by simp; omega)]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega

 theorem derivation_cost_closed (tag : List Byte) :
    derivationPrimitiveCost tag = 2 + (tag.length+63)/64 := by
  rw [derivation_cost, chunks_length true 0 [] tag (by simp)]
  simp


 @[simp] theorem scalarBytes_length (x : E) : (scalarBytes x).length = 24 := by simp [scalarBytes]
 @[simp] theorem scalarsBytes_length (xs : List E) : (scalarsBytes xs).length = 24*xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [scalarsBytes]; omega
 @[simp] theorem rawRoot_length (root : Digest32) : (rawRoot root).length = 32 := by simp [rawRoot]

 theorem rawRoot_injective : Function.Injective rawRoot := by
  intro a b h
  funext i
  have := congrArg (fun bs => bs[i.val]?) h
  simpa only [rawRoot, List.getElem?_ofFn, dite_eq_left i.isLt, Option.some.injEq] using this

 theorem raw_not_historical (root : Digest32) :
    rawRoot root ≠ scalarsBytes [(ByteCodec.hashToScalars root).1, (ByteCodec.hashToScalars root).2] := by
  intro h
  have := congrArg List.length h
  simp at this

 abbrev Shape := AnchoredHeaderCodec.Shape
 def constants (marker : E) (shape : Shape) : List E :=
  [marker, AnchoredHeaderCodec.shapeScalar shape, AnchoredHeaderCodec.lanesScalar shape]

 def commitPrefix (shape : Shape) (root : Digest32) : List Byte :=
  scalarsBytes (constants AnchoredHeaderCodec.anchorMarker shape) ++ rawRoot root

 theorem commitPrefix_length (shape : Shape) (root : Digest32) :
    (commitPrefix shape root).length = 104 := by simp [commitPrefix, constants]

 /-- There are 3E+raw32 BEFORE drawing logN complete E coordinates;
only the advertised value after the draw brings transport to 4E+raw32. -/
 def commitTransport (shape : Shape) (root : Digest32) (value : E) : List Byte :=
  commitPrefix shape root ++ scalarBytes value

 theorem commitTransport_length (shape : Shape) (root : Digest32) (value : E) :
    (commitTransport shape root value).length = 128 := by
  simp [commitTransport, commitPrefix_length]

 def absorbMessages (c : Compression) (s : State) (messages : List (List Byte)) : State :=
  messages.foldl (absorb c) s

 theorem absorbMessages_flatten (c : Compression) (s : State) (messages : List (List Byte)) :
    absorbMessages c s messages = absorb c s messages.flatten := by
  induction messages generalizing s with
  | nil => rfl
  | cons m ms ih => simp only [absorbMessages, List.foldl_cons, List.flatten_cons, absorb_append] at *; exact ih _

 theorem commitPrefix_grouping (c : Compression) (s : State) (shape : Shape) (root : Digest32) :
    absorbMessages c s ((constants AnchoredHeaderCodec.anchorMarker shape).map scalarBytes ++ [rawRoot root]) =
      absorb c s (commitPrefix shape root) := by
  rw [absorbMessages_flatten]
  simp [commitPrefix, scalarsBytes, List.flatten_append, List.flatMap_def]

 def commit (c : Compression) (s : State) (shape : Shape) (root : Digest32) (value : E) :
    Except Error (State × List E) := do
  let (t, point) ← sampleVec c (absorb c s (commitPrefix shape root)) shape.logN
  pure (observe c t value, point)

 /-- Complete 24-byte draws survive grouping, even if only c0 is projected.
No absorb/value event is moved across this draw. -/
 theorem draw_grouping (c : Compression) (s : State) (a b : Nat)
    (limit : s.consumed + (24*a+24*b) ≤ maxCursor) :
    squeeze c s (24*(a+b)) =
      match squeeze c s (24*a) with
      | .error e => .error e
      | .ok (t,xs) => match squeeze c t (24*b) with
        | .error e => .error e
        | .ok (u,ys) => .ok (u,xs++ys) := by
  rw [Nat.mul_add]
  exact squeeze_concatenates c s (24*a) (24*b) limit

 /-- Source uses ALL 192 bits, not c0-only: disjoint depth-bit chunks,
low bits first, then fixed-count strata. Native 64-bit shifts/masks are kept
literally. Source callers require 1 ≤ depth < 64 and count < 2^64.
Totalization outside those source preconditions is not a Rust panic model. -/
 def limb (x : E) (i : Nat) : UInt64 :=
  match i with | 0 => x.c0 | 1 => x.c1 | 2 => x.c2 | _ => 0

 def queryChunks (depth : Nat) (x : E) : List Nat :=
  (List.range (192/depth)).map fun j =>
    let off := j*depth
    let sh := off%64
    let chunk := limb x (off/64) >>> UInt64.ofNat sh
    let chunk := if sh+depth > 64 then
      chunk ||| (limb x (off/64+1) <<< UInt64.ofNat (64-sh)) else chunk
    (chunk &&& UInt64.ofNat (2^depth-1)).toNat

 def strata (count depth : Nat) : List (Nat × Nat) :=
  ((List.range 64).reverse.filter fun g =>
    ((UInt64.ofNat count >>> UInt64.ofNat g) &&& 1) == 1).flatMap fun g =>
    (List.range (2^g)).map fun j => (min g depth,
      (UInt64.ofNat j &&& UInt64.ofNat (2^(min g depth)-1)).toNat)

 def projectQueries (count depth : Nat) (xs : List E) : List Nat :=
  ((xs.flatMap (queryChunks depth)).take count).zip (strata count depth) |>.map fun p =>
    let low := depth-p.2.1
    ((UInt64.ofNat p.1 &&& UInt64.ofNat (2^low-1)) |||
      (UInt64.ofNat p.2.2 <<< UInt64.ofNat low)).toNat

 /-- For fixed source count/strata, later E draws cannot affect the projected
positions already supplied by an adequate prefix. Changing count also changes
strata and is deliberately NOT claimed to preserve positions. -/
 theorem projected_query_causality (count depth : Nat) (xs ys : List E)
    (enough : count ≤ (xs.flatMap (queryChunks depth)).length) :
    projectQueries count depth (xs++ys) = projectQueries count depth xs := by
  simp only [projectQueries, List.flatMap_append, List.take_append,
    Nat.sub_eq_zero_of_le enough, List.take_zero, List.append_nil]

 theorem sample_full_cursor (c : Compression) (s t : State) (x : E)
    (ok : sample c s = .ok (t,x)) : t.consumed = s.consumed + 24 := by
  unfold sample at ok
  split at ok
  · cases ok
  · rename_i u bs hs
    cases ok
    exact (squeeze_exact_cursor c s t 24 bs hs).1

 structure Context where
  cv : Digest32
  pending : List Byte
  first : Bool
  previous : UInt64
  squeezed : UInt64

 def capture (s : State) : Context :=
  ⟨s.cv, s.pending.toList, s.first, UInt64.ofNat s.previous, UInt64.ofNat s.consumed⟩

 theorem capture_cache_irrelevant (s : State) (out : Digest32) :
    capture {s with output := out} = capture s := rfl

 /-- Three normalized LE words per E, literal zero in every absent byte.
This includes zeroing the unused high bytes of the final partial word. -/
 def pendingPacks (ctx : Context) : List E :=
  List.ofFn fun i : Fin ((ctx.pending.length+23)/24) =>
    ByteCodec.decodeE (fun j => ctx.pending[24*i.val+j.val]?.getD 0)

 theorem pendingPack_bytes (ctx : Context) (i : Fin ((ctx.pending.length+23)/24)) :
    ByteCodec.encodeE ((pendingPacks ctx)[i.val]'(by simp [pendingPacks])) =
      (fun j => ctx.pending[24*i.val+j.val]?.getD 0) := by
  simp [pendingPacks, ByteCodec.encodeE_decodeE]

 def contextScalars (ctx : Context) : List E :=
  [⟨UInt64.ofNat ctx.pending.length, if ctx.first then 1 else 0, ctx.previous⟩,
    ⟨ctx.squeezed,0,0⟩]

 structure Record where
  shape : Shape
  root : Digest32
  context : Context
  point : List E
  value : E

 /-- Native opening order: 3 constants, raw root, raw original CV, two
metadata E, ceil(pendingBytes/24) normalized E, original point, original value. -/
 def openingBytes (r : Record) : List Byte :=
  scalarsBytes (constants AnchoredHeaderCodec.openingMarker r.shape) ++
  rawRoot r.root ++ rawRoot r.context.cv ++ scalarsBytes (contextScalars r.context) ++
  scalarsBytes (pendingPacks r.context) ++ scalarsBytes r.point ++ scalarBytes r.value

 theorem openingBytes_length (r : Record) :
    (openingBytes r).length = 208 + 24*((r.context.pending.length+23)/24 + r.point.length) := by
  simp [openingBytes, constants, contextScalars, pendingPacks]; omega

 theorem openingBytes_point_length (r : Record) (point : r.point.length = r.shape.logN) :
    (openingBytes r).length = 208 + 24*((r.context.pending.length+23)/24 + r.shape.logN) := by
  rw [openingBytes_length, point]

 def openingMessages (r : Record) : List (List Byte) :=
  (constants AnchoredHeaderCodec.openingMarker r.shape).map scalarBytes ++
  [rawRoot r.root, rawRoot r.context.cv] ++ (contextScalars r.context).map scalarBytes ++
  (pendingPacks r.context).map scalarBytes ++ r.point.map scalarBytes ++ [scalarBytes r.value]

 theorem opening_grouping (c : Compression) (s : State) (r : Record) :
    absorbMessages c s (openingMessages r) = absorb c s (openingBytes r) := by
  rw [absorbMessages_flatten]
  simp [openingMessages, openingBytes, scalarsBytes, List.flatten_append, List.flatMap_def,
    List.append_assoc]

 /-- A byte-level expected-record parser, not the source verifier or its acceptance theorem. -/
 def readOpening (r : Record) (transport : List Byte) : Option (List Byte) :=
  if transport.take (openingBytes r).length = openingBytes r then
    some (transport.drop (openingBytes r).length) else none

 theorem readOpening_honest (r : Record) (suffix : List Byte) :
    readOpening r (openingBytes r ++ suffix) = some suffix := by simp [readOpening]

 theorem readOpening_sound (r : Record) (transport suffix : List Byte)
    (h : readOpening r transport = some suffix) : transport = openingBytes r ++ suffix := by
  unfold readOpening at h
  split at h
  · rename_i same
    cases h
    calc
      transport = transport.take (openingBytes r).length ++ transport.drop (openingBytes r).length :=
        (List.take_append_drop _ _).symm
      _ = openingBytes r ++ transport.drop (openingBytes r).length := by rw [same]
  · cases h

 /-- Reproducible differential fixture, not a universal Rust equivalence proof.
The external probe includes the pinned actual Rust source modules and native
BLAKE2s implementation. Each output line is compared byte-for-byte. -/
 def runtimeFixture : List String := Id.run do
  let c := DuplexCompression.compress
  let parameter := DuplexCompression.parameterIV
  let root : Digest32 := fun i => ⟨i.val, by omega⟩
  let mut lines := ["init|" ++ DuplexCompression.hex (rawRoot (init c parameter root).cv)]
  for n in [0,1,31,32,63,64,65,129] do
    let tag : List Byte := (List.range n).map fun i => ⟨i%256, Nat.mod_lt _ (by decide)⟩
    lines := lines ++ [withDerived c parameter tag fun session =>
      "derive" ++ toString n ++ "|" ++ DuplexCompression.hex (rawRoot session)]
  let tag : List Byte := "607-runtime-fixture".toUTF8.toList.map fun b =>
    ⟨b.toNat%256, Nat.mod_lt _ (by decide)⟩
  let s := withDerived c parameter tag fun session =>
    absorb c (init c parameter session) (littleWord 0x0102030405060708)
  lines := lines ++ ["session|" ++ DuplexCompression.hex (rawRoot s.cv)]
  let shape : Shape := ⟨3,1,1,2⟩
  let value : E := ⟨1,2,3⟩
  let headerBytes := commitPrefix shape root
  lines := lines ++ ["prefix|" ++ DuplexCompression.hex headerBytes]
  match sampleVec c (absorb c s headerBytes) shape.logN with
  | .error e => return lines ++ ["error|" ++ reprStr e]
  | .ok (t,point) =>
    lines := lines ++ ["point|" ++ DuplexCompression.hex (scalarsBytes point),
      "commit|" ++ DuplexCompression.hex (commitTransport shape root value)]
    let r : Record := ⟨shape,root,capture s,point,value⟩
    let opening := openingBytes r
    lines := lines ++ ["opening|" ++ DuplexCompression.hex opening]
    match squeeze c (absorb c (observe c t value) opening) 32 with
    | .error e => return lines ++ ["error|" ++ reprStr e]
    | .ok (_,bytes) => return lines ++ ["final32|" ++ DuplexCompression.hex bytes]

#print axioms withDerived_eq

end Whir.SpongefishSessionAdapter
