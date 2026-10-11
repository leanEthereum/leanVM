import Whir.FiatShamirGame
import Whir.ByteCodec

/-! The byte state machine of conditional #552, not the baseline step chain.
The compression function is public and includes the complete CV, block, counter
and final flag. This is a hand-port semantics, not a Rust compiler theorem. -/
namespace Whir.DuplexRefinement
open FiatShamirGame

def sourceRevision : String := "ff6a275304a3b577118b066ddcff83bfafa5998d"
def modeVersion : String := "#552/LVFS-1/framed-byte-duplex"
def libSourceSHA256 : String := "cadcb014afca2f228f597131b5ac0ee63693358e65c793fc2b357bf445bbba79"
def transportSourceSHA256 : String := "5b8f4190afea759cc37c289f7f3af9597f6d416b944a66fa229078dea1d793c5"
abbrev Block64 := Fin 64 → Byte
abbrev Compression := Digest32 → Block64 → UInt64 → Bool → Digest32

def maxCursor : Nat := 2^49 - 1

def role (first last : Bool) : Nat :=
  if first then (if last then 4 else 2) else (if last then 5 else 3)

/-- The three fields occupy disjoint bit intervals: 8, 7, and 49 bits. -/
def packTweak (r len previous : Nat) : Nat := r * 2^56 + len * 2^49 + previous

def absorbTweak (first last : Bool) (len previous : Nat) : UInt64 :=
  UInt64.ofNat (packTweak (role first last) len previous)

def zeroDigest : Digest32 := fun _ => 0

def padded (bytes : Array Byte) : Block64 := fun i => bytes[i.val]?.getD 0

def littleWord (n : Nat) : List Byte :=
  List.ofFn (ByteCodec.encodeNat 8 n)

def wordsBlock (ns : List Nat) : Block64 := padded (ns.flatMap littleWord).toArray

/-- Only bounded buffering lives in the executable state; no transcript log. -/
structure State where
  cv : Digest32
  pending : Array Byte := #[]
  first : Bool := true
  previous : Nat := 0
  consumed : Nat := 0
  output : Digest32 := zeroDigest

/-- Eagerly close a finite digest over 32 stored bytes, rather than retaining a
closure that recursively recomputes the previous compression history. -/
def memoCV (s : State) (d : Digest32) : State :=
  let bytes := Array.ofFn d
  {s with cv := fun i => bytes[i.val]'(by simp only [bytes, Array.size_ofFn]; exact i.isLt)}

def memoOutput (s : State) (d : Digest32) : State :=
  let bytes := Array.ofFn d
  {s with output := fun i => bytes[i.val]'(by simp only [bytes, Array.size_ofFn]; exact i.isLt)}

@[simp] theorem memoCV_eq (s : State) (d : Digest32) : memoCV s d = {s with cv := d} := by
  simp [memoCV]

@[simp] theorem memoOutput_eq (s : State) (d : Digest32) : memoOutput s d = {s with output := d} := by
  simp [memoOutput]

/-- Seed uses exactly domain || statement with the parameter IV supplied by the
primitive instantiation. There is no API for injecting a live chaining value. -/
def seed (compress : Compression) (iv domain statement : Digest32) : State :=
  { cv := compress iv (ByteCodec.pairBytes (domain, statement)) (UInt64.ofNat (2^56)) true }

def seedMemo (c : Compression) (iv domain statement : Digest32) : State :=
  memoCV {cv := zeroDigest} (c iv (ByteCodec.pairBytes (domain,statement)) (UInt64.ofNat (2^56)) true)

@[csimp] theorem seed_memo : seed = seedMemo := by
  funext c iv domain statement
  simp [seed, seedMemo]

/-- One byte, retaining a full block until a subsequent byte proves nonfinality. -/
def absorbByte (compress : Compression) (s : State) (b : Byte) : State :=
  let s := if s.consumed = 0 then s
    else { s with previous := s.consumed, consumed := 0 }
  let s := if s.pending.size = 64 then
    { s with
      cv := compress s.cv (padded s.pending) (absorbTweak s.first false 64 s.previous) true
      pending := #[]
      first := false
      previous := 0 }
    else s
  { s with pending := s.pending.push b }

def absorbByteMemo (c : Compression) (s : State) (b : Byte) : State :=
  let s := if s.consumed = 0 then s else {s with previous := s.consumed, consumed := 0}
  let s := if s.pending.size = 64 then
    let s := memoCV s (c s.cv (padded s.pending) (absorbTweak s.first false 64 s.previous) true)
    {s with pending := #[], first := false, previous := 0}
    else s
  {s with pending := s.pending.push b}

@[csimp] theorem absorbByte_memo : absorbByte = absorbByteMemo := by
  funext c s b
  simp only [absorbByte, absorbByteMemo, memoCV_eq]

def absorb (compress : Compression) (s : State) (bytes : List Byte) : State :=
  bytes.foldl (absorbByte compress) s

/-- Nonmutating finalization used by both export families. -/
def finalized (compress : Compression) (s : State) : Digest32 :=
  if s.pending.isEmpty then s.cv else
    compress s.cv (padded s.pending)
      (absorbTweak s.first true s.pending.size s.previous) true

def finish (compress : Compression) (s : State) : State :=
  if s.pending.isEmpty then s else
    { s with cv := finalized compress s, pending := #[], first := true, previous := 0 }

def finishMemo (c : Compression) (s : State) : State :=
  if s.pending.isEmpty then s else
    let s := memoCV s (finalized c s)
    {s with pending := #[], first := true, previous := 0}

@[csimp] theorem finish_memo : finish = finishMemo := by
  funext c s
  simp only [finish, finishMemo, memoCV_eq]

def outputBlock (compress : Compression) (cv : Digest32) (index : Nat) : Digest32 :=
  compress cv (wordsBlock [index]) (UInt64.ofNat (6 * 2^56)) true

/-- Retains unused output bytes rather than recomputing their block. -/
def squeezeByte (compress : Compression) (s : State) : State × Byte :=
  let digest := if s.consumed % 32 = 0 then outputBlock compress s.cv (s.consumed / 32)
    else s.output
  ({ s with consumed := s.consumed + 1, output := digest },
    digest ⟨s.consumed % 32, Nat.mod_lt _ (by decide)⟩)

def squeezeByteMemo (c : Compression) (s : State) : State × Byte :=
  let s := if s.consumed % 32 = 0 then memoOutput s (outputBlock c s.cv (s.consumed / 32)) else s
  ({s with consumed := s.consumed + 1}, s.output ⟨s.consumed % 32, Nat.mod_lt _ (by decide)⟩)

@[csimp] theorem squeezeByte_memo : squeezeByte = squeezeByteMemo := by
  funext c s
  simp only [squeezeByte, squeezeByteMemo, memoOutput_eq]
  split <;> rfl

def squeezeLoop (compress : Compression) : Nat → State → State × List Byte
  | 0, s => (s, [])
  | n + 1, s =>
    let (s', b) := squeezeByte compress s
    let (s'', bs) := squeezeLoop compress n s'
    (s'', b :: bs)

inductive Error where
  | cursorExhausted
  | grindingBits
  | nonceExhausted
  | absorbLength
  | absorbCursor
  deriving DecidableEq, Repr

/-- Limits are checked before finishing pending input or consuming output. -/
def squeeze (compress : Compression) (s : State) (n : Nat) : Except Error (State × List Byte) :=
  if n = 0 then .ok (s, [])
  else if s.consumed + n ≤ maxCursor then .ok (squeezeLoop compress n (finish compress s))
  else .error .cursorExhausted

def commitment (compress : Compression) (s : State) : Digest32 :=
  compress (finalized compress s) (wordsBlock [s.consumed]) (UInt64.ofNat (7 * 2^56)) true

def powBase (compress : Compression) (s : State) (bits : Nat) : Digest32 :=
  compress (finalized compress s) (wordsBlock [s.consumed, bits])
    (UInt64.ofNat (8 * 2^56)) true

def nonceBlock (nonce : Scalar24) (consumed bits : Nat) : Block64 :=
  padded ((List.ofFn nonce ++ littleWord consumed ++ littleWord bits).toArray)

/-- Internal nonce event. In verification even a failed PoW predicate binds its
nonce; the caller must reject. No ordinary scalar absorption is performed. -/
def bindNonce (compress : Compression) (s : State) (nonce : Scalar24) (bits : Nat) : State :=
  let s := finish compress s
  { s with cv := (compress s.cv (nonceBlock nonce s.consumed bits)
      (UInt64.ofNat (9 * 2^56)) true), consumed := 0 }

def bindNonceMemo (c : Compression) (s : State) (nonce : Scalar24) (bits : Nat) : State :=
  let s := finish c s
  let s := memoCV s (c s.cv (nonceBlock nonce s.consumed bits) (UInt64.ofNat (9 * 2^56)) true)
  {s with consumed := 0}

@[csimp] theorem bindNonce_memo : bindNonce = bindNonceMemo := by
  funext c s nonce bits
  simp only [bindNonce, bindNonceMemo, memoCV_eq]

def verifyNonce (compress : Compression) (powOK : Digest32 → Scalar24 → Nat → Bool)
    (s : State) (nonce : Scalar24) (bits : Nat) : Except Error (State × Bool) :=
  if bits ≤ 63 then
    let s := finish compress s
    let ok := if bits = 0 then decide (nonce = fun _ => 0) else powOK (powBase compress s bits) nonce bits
    .ok (bindNonce compress s nonce bits, ok)
  else .error .grindingBits

@[simp] theorem absorb_empty (c : Compression) (s : State) : absorb c s [] = s := rfl

/-- All positive/empty call chunkings denote the same absorb run. -/
theorem absorb_append (c : Compression) (s : State) (a b : List Byte) :
    absorb c s (a ++ b) = absorb c (absorb c s a) b := by
  simp [absorb, List.foldl_append]

@[simp] theorem squeeze_empty (c : Compression) (s : State) :
    squeeze c s 0 = .ok (s, []) := by simp [squeeze]

@[simp] theorem finish_pending (c : Compression) (s : State) :
    (finish c s).pending = #[] := by
  simp only [finish]
  split
  next h => simpa using Array.isEmpty_iff.mp h
  next => rfl

@[simp] theorem finish_cv (c : Compression) (s : State) :
    (finish c s).cv = finalized c s := by
  simp only [finish, finalized]
  split <;> rfl

@[simp] theorem finish_consumed (c : Compression) (s : State) :
    (finish c s).consumed = s.consumed := by
  simp only [finish]; split <;> rfl

@[simp] theorem finish_idempotent (c : Compression) (s : State) :
    finish c (finish c s) = finish c s := by
  unfold finish
  split <;> simp_all

@[simp] theorem squeezeLoop_consumed (c : Compression) (n : Nat) (s : State) :
    (squeezeLoop c n s).1.consumed = s.consumed + n := by
  induction n generalizing s with
  | zero => simp [squeezeLoop]
  | succ n ih =>
    simp only [squeezeLoop, ih, squeezeByte]
    omega

@[simp] theorem squeezeLoop_length (c : Compression) (n : Nat) (s : State) :
    (squeezeLoop c n s).2.length = n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simp [squeezeLoop, ih]

/-- The exact cursor, not the padded output length, is committed. -/
theorem squeeze_exact_cursor (c : Compression) (s t : State) (n : Nat) (bs : List Byte)
    (h : squeeze c s n = .ok (t, bs)) : t.consumed = s.consumed + n ∧ bs.length = n := by
  unfold squeeze at h
  split at h
  next hn => cases h; simp_all
  next =>
    split at h
    next =>
      have he := Except.ok.inj h
      have hc := congrArg (fun p : State × List Byte => p.1.consumed) he
      have hl := congrArg (fun p : State × List Byte => p.2.length) he
      exact ⟨by simpa using hc.symm, by simpa using hl.symm⟩
    next => cases h

theorem squeeze_exhausted (c : Compression) (s : State) (n : Nat)
    (positive : n ≠ 0) (large : maxCursor < s.consumed + n) :
    squeeze c s n = .error .cursorExhausted := by simp [squeeze, positive, Nat.not_le.mpr large]

/-- Nonmutating exports and Lean value cloning preserve the complete pending
buffer and unused output; the two independent continuations start identically. -/
theorem clone_continuation (s : State) (f : State → State) : f (id s) = f s := rfl

/-- No carry can turn length/cursor data into a different role. -/
theorem packTweak_injective {r r' len len' previous previous' : Nat}
    (hl : len < 128) (hl' : len' < 128)
    (hp : previous < 2^49) (hp' : previous' < 2^49)
    (h : packTweak r len previous = packTweak r' len' previous') :
    r = r' ∧ len = len' ∧ previous = previous' := by
  unfold packTweak at h
  omega

theorem role_injective {f l f' l' : Bool} (h : role f l = role f' l') :
    f = f' ∧ l = l' := by
  cases f <;> cases l <;> cases f' <;> cases l' <;> simp_all [role]

def observe (c : Compression) (s : State) (x : Concrete.E) : State :=
  absorb c s (List.ofFn (ByteCodec.encodeE x))

def observeMany (c : Compression) (s : State) (xs : List Concrete.E) : State :=
  xs.foldl (observe c) s

/-- The root is transported as two canonical E scalars, hence 48 bytes,
including the two zero spare limbs. It is never absorbed a second time. -/
def observeRoot (c : Compression) (s : State) (root : Digest32) : State :=
  let p := ByteCodec.hashToScalars root
  observe c (observe c s p.1) p.2

theorem observeRoot_bytes (c : Compression) (s : State) (root : Digest32) :
    observeRoot c s root = absorb c s
      (List.ofFn (ByteCodec.encodeE (ByteCodec.hashToScalars root).1) ++
       List.ofFn (ByteCodec.encodeE (ByteCodec.hashToScalars root).2)) := by
  simp only [observeRoot, observe, absorb_append]

theorem scalar_codec_bijection :
    Function.Bijective ByteCodec.encodeE := by
  exact ⟨ByteCodec.encodeE_injective, fun b => ⟨ByteCodec.decodeE b, ByteCodec.encodeE_decodeE b⟩⟩

/-- Exactly the transmitted coefficients, not the reconstructed coefficient. -/
def transmittedCoefficients (coefficients : List Concrete.E) (eqFactored : Bool) : List Concrete.E :=
  (coefficients.zipIdx.filter (fun p => p.2 != (if eqFactored then 0 else 1))).map Prod.fst

def observeRound (c : Compression) (s : State) (coefficients : List Concrete.E)
    (eqFactored : Bool) : State :=
  observeMany c s (transmittedCoefficients coefficients eqFactored)

/-- Side authentication is deliberately outside the byte transcript. -/
def authenticate (_level : Nat) (s : State) : State := s

theorem authenticate_preserves (level : Nat) (s : State) : authenticate level s = s := rfl

theorem absorbByte_bounded (c : Compression) (s : State) (b : Byte)
    (h : s.pending.size ≤ 64) : (absorbByte c s b).pending.size ≤ 64 := by
  simp only [absorbByte]
  split <;> split <;> simp_all only [Array.size_push, Array.size_empty] <;> omega

theorem absorb_bounded (c : Compression) (s : State) (bs : List Byte)
    (h : s.pending.size ≤ 64) : (absorb c s bs).pending.size ≤ 64 := by
  induction bs generalizing s with
  | nil => exact h
  | cons b bs ih => exact ih _ (absorbByte_bounded c s b h)

theorem absorbByte_cursor (c : Compression) (s : State) (b : Byte) :
    (absorbByte c s b).consumed = 0 := by
  simp only [absorbByte]
  split <;> split <;> simp_all

theorem squeezeLoop_append (c : Compression) (a b : Nat) (s : State) :
    squeezeLoop c (a + b) s =
      let p := squeezeLoop c a s
      let q := squeezeLoop c b p.1
      (q.1, p.2 ++ q.2) := by
  induction a generalizing s with
  | zero => simp [squeezeLoop]
  | succ a ih =>
    simp only [Nat.succ_add, squeezeLoop, ih, List.cons_append]

theorem squeezeLoop_pending (c : Compression) (n : Nat) (s : State) :
    (squeezeLoop c n s).1.pending = s.pending := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simp only [squeezeLoop, ih, squeezeByte]

theorem squeezeLoop_cv (c : Compression) (n : Nat) (s : State) :
    (squeezeLoop c n s).1.cv = s.cv := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simp only [squeezeLoop, ih, squeezeByte]

theorem squeezeLoop_finish (c : Compression) (n : Nat) (s : State) :
    finish c (squeezeLoop c n (finish c s)).1 = (squeezeLoop c n (finish c s)).1 := by
  have hp : (squeezeLoop c n (finish c s)).1.pending = #[] := by
    rw [squeezeLoop_pending, finish_pending]
  generalize he : (squeezeLoop c n (finish c s)).1 = t at hp ⊢
  simp only [finish, hp, Array.isEmpty_empty, ↓reduceIte]

/-- Consecutive output calls concatenate, including calls crossing block
boundaries; no intervening frame or challenge opportunity is introduced. -/
theorem squeeze_concat (c : Compression) (s : State) (a b : Nat)
    (ha : a ≠ 0) (hb : b ≠ 0) (limit : s.consumed + (a+b) ≤ maxCursor) :
    squeeze c s (a+b) =
      match squeeze c s a with
      | .error e => .error e
      | .ok (t,xs) => match squeeze c t b with
        | .error e => .error e
        | .ok (u,ys) => .ok (u,xs++ys) := by
  have ha' : s.consumed + a ≤ maxCursor := by omega
  have hab : a+b ≠ 0 := by omega
  simp only [squeeze, ha, hb, hab, ↓reduceIte, ha', limit,
    squeezeLoop_consumed, finish_consumed, squeezeLoop_finish]
  rw [ite_eq_left (by omega), squeezeLoop_append]

/-- The cache is relevant only inside a partially consumed block. -/
def CacheValid (c : Compression) (s : State) : Prop :=
  s.consumed % 32 ≠ 0 → s.output = outputBlock c s.cv (s.consumed / 32)

theorem squeezeByte_value (c : Compression) (s : State) (h : CacheValid c s) :
    (squeezeByte c s).2 =
      outputBlock c s.cv (s.consumed / 32) ⟨s.consumed % 32, Nat.mod_lt _ (by decide)⟩ := by
  unfold squeezeByte
  split
  · rfl
  · rename_i hn; rw [h hn]

theorem squeezeByte_cache (c : Compression) (s : State) (h : CacheValid c s) :
    CacheValid c (squeezeByte c s).1 := by
  intro hn
  have hd : (s.consumed + 1) / 32 = s.consumed / 32 := by
    change (s.consumed + 1) % 32 ≠ 0 at hn
    omega
  simp only [squeezeByte, hd]
  split
  · rfl
  · rename_i hz; exact h hz

def stream (c : Compression) (cv : Digest32) : Nat → Nat → List Byte
  | _, 0 => []
  | offset, n+1 =>
    outputBlock c cv (offset / 32) ⟨offset % 32, Nat.mod_lt _ (by decide)⟩ ::
      stream c cv (offset+1) n

theorem squeezeLoop_stream (c : Compression) (s : State) (n : Nat) (h : CacheValid c s) :
    (squeezeLoop c n s).2 = stream c s.cv s.consumed n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [squeezeLoop, stream]
    rw [squeezeByte_value c s h, ih _ (squeezeByte_cache c s h)]
    rfl

theorem squeezeLoop_cache (c : Compression) (s : State) (n : Nat) (h : CacheValid c s) :
    CacheValid c (squeezeLoop c n s).1 := by
  induction n generalizing s with
  | zero => exact h
  | succ n ih => exact ih _ (squeezeByte_cache c s h)

theorem held_full_block (c : Compression) (s : State) (b : Byte)
    (cursor : s.consumed = 0) (full : s.pending.size = 64) :
    (absorbByte c s b).cv =
      c s.cv (padded s.pending) (absorbTweak s.first false 64 s.previous) true ∧
    (absorbByte c s b).pending = #[b] ∧
    (absorbByte c s b).first = false ∧ (absorbByte c s b).previous = 0 := by
  simp [absorbByte, cursor, full]

theorem held_final_block (c : Compression) (s : State)
    (full : s.pending.size = 64) :
    finalized c s = c s.cv (padded s.pending) (absorbTweak s.first true 64 s.previous) true := by
  have hn : s.pending.isEmpty = false := by
    simp only [Array.isEmpty_eq_false_iff]
    intro he
    simp [he] at full
  simp [finalized, hn, full]

theorem absorbByte_output (c : Compression) (s : State) (b : Byte) :
    (absorbByte c s b).output = s.output := by
  simp only [absorbByte]; split <;> split <;> rfl

theorem absorb_output (c : Compression) (s : State) (bs : List Byte) :
    (absorb c s bs).output = s.output := by
  induction bs generalizing s with
  | nil => rfl
  | cons b bs ih => exact (ih _).trans (absorbByte_output c s b)

theorem absorb_nonempty_cursor (c : Compression) (s : State) (bs : List Byte)
    (h : bs ≠ []) : (absorb c s bs).consumed = 0 := by
  induction bs generalizing s with
  | nil => exact False.elim (h rfl)
  | cons b bs ih =>
    cases bs with
    | nil => exact absorbByte_cursor c s b
    | cons b' bs => exact ih _ (by simp)

theorem absorb_nonempty_pending (c : Compression) (s : State) (bs : List Byte)
    (h : bs ≠ []) : (absorb c s bs).pending.isEmpty = false := by
  induction bs generalizing s with
  | nil => exact False.elim (h rfl)
  | cons b bs ih =>
    cases bs with
    | nil =>
      simp only [absorb, List.foldl_cons, List.foldl_nil, absorbByte]
      split <;> split <;> simp
    | cons b' bs => exact ih _ (by simp)

/-- Completed canonical history interpretation. Squeeze counts are metadata:
replaying a frame does not expand an earlier stream. -/
def evalFrame (c : Compression) (cv : Digest32) : Frame → Digest32
  | .absorb previous bytes => finalized c (absorb c {cv, previous} bytes)
  | .nonce previous bits nonce =>
    c cv (nonceBlock nonce previous bits) (UInt64.ofNat (9 * 2^56)) true

def evalHistory (c : Compression) (iv : Digest32) (h : FramedHistory) : Digest32 :=
  h.frames.foldl (evalFrame c) (seed c iv h.domain h.statement).cv

def evalTerminal (c : Compression) (cv : Digest32) : Terminal → Digest32
  | .output block => outputBlock c cv block
  | .commitment consumed => c cv (wordsBlock [consumed]) (UInt64.ofNat (7 * 2^56)) true
  | .powBase consumed bits => c cv (wordsBlock [consumed,bits]) (UInt64.ofNat (8 * 2^56)) true

def evalCoordinate (c : Compression) (iv : Digest32) (q : Coordinate) : Digest32 :=
  evalTerminal c (evalHistory c iv q.history) q.terminal

theorem evalHistory_append (c : Compression) (iv : Digest32) (h : FramedHistory) (fs : List Frame) :
    evalHistory c iv {h with frames := h.frames ++ fs} = fs.foldl (evalFrame c) (evalHistory c iv h) := by
  simp [evalHistory, List.foldl_append]

/-- Ghost-only history with an unfinished absorb run. No executable operation
stores this record or copies its history. -/
structure Model where
  history : FramedHistory
  run : List Byte := []
  previous : Nat := 0
  consumed : Nat := 0

def materialize (c : Compression) (iv : Digest32) (m : Model) (out : Digest32) : State :=
  absorb c {cv := evalHistory c iv m.history, previous := m.previous, consumed := m.consumed, output := out} m.run

def Model.Valid (m : Model) : Prop :=
  (m.run ≠ [] → m.consumed = 0) ∧ (m.run = [] → m.previous = 0) ∧ m.consumed ≤ maxCursor ∧ m.previous ≤ maxCursor

def Represents (c : Compression) (iv : Digest32) (m : Model) (s : State) : Prop :=
  m.Valid ∧ s = materialize c iv m s.output ∧ CacheValid c s

def closeRun (m : Model) : Model :=
  if m.run = [] then m else
    {m with
      history := {m.history with frames := m.history.frames ++ [.absorb m.previous m.run]}
      run := []
      previous := 0}

theorem absorbByte_setOutput (c : Compression) (s : State) (out : Digest32) (b : Byte) :
    absorbByte c {s with output := out} b = {absorbByte c s b with output := out} := by
  simp only [absorbByte]
  split <;> split <;> rfl

theorem absorb_setOutput (c : Compression) (s : State) (out : Digest32) (bs : List Byte) :
    absorb c {s with output := out} bs = {absorb c s bs with output := out} := by
  induction bs generalizing s with
  | nil => rfl
  | cons b bs ih =>
    simp only [absorb, List.foldl_cons]
    rw [absorbByte_setOutput]
    exact ih _

@[simp] theorem finalized_setOutput (c : Compression) (s : State) (out : Digest32) :
    finalized c {s with output := out} = finalized c s := rfl

theorem absorb_switch (c : Compression) (s : State) (bs : List Byte) (hb : bs ≠ []) :
    absorb c s bs = absorb c
      {s with consumed := 0, previous := if s.consumed = 0 then s.previous else s.consumed} bs := by
  cases bs with
  | nil => exact False.elim (hb rfl)
  | cons b bs =>
    simp only [absorb, List.foldl_cons]
    congr 1
    by_cases hc : s.consumed = 0
    · have he : {s with consumed := 0, previous := s.previous} = s := by
        cases s; simp_all
      simp only [hc, ↓reduceIte, he]
    · simp only [absorbByte, hc, ↓reduceIte]

theorem materialize_output (c : Compression) (iv : Digest32) (m : Model) (out : Digest32) :
    (materialize c iv m out).output = out := absorb_output c _ _

theorem materialize_consumed (c : Compression) (iv : Digest32) (m : Model) (out : Digest32)
    (valid : m.Valid) : (materialize c iv m out).consumed = m.consumed := by
  by_cases hr : m.run = []
  · simp [materialize, hr]
  · rw [valid.1 hr]
    exact absorb_nonempty_cursor c _ _ hr

theorem closeRun_valid (m : Model) (h : m.Valid) : (closeRun m).Valid := by
  unfold closeRun
  split
  · exact h
  · simp only [Model.Valid]
    exact ⟨by simp, by simp, h.2.2.1, by simp [maxCursor]⟩

theorem closeRun_empty (m : Model) : (closeRun m).run = [] := by
  unfold closeRun; split <;> simp_all

theorem finish_materialize (c : Compression) (iv : Digest32) (m : Model) (out : Digest32)
    (h : m.Valid) :
    finish c (materialize c iv m out) = materialize c iv (closeRun m) out := by
  by_cases hr : m.run = []
  · simp [closeRun, hr, materialize, finish]
  · have hc := h.1 hr
    have hp := absorb_nonempty_pending c
      ({cv := evalHistory c iv m.history, previous := m.previous, consumed := m.consumed, output := out} : State) m.run hr
    have ho := absorb_output c
      ({cv := evalHistory c iv m.history, previous := m.previous, consumed := m.consumed, output := out} : State) m.run
    have hz := absorb_nonempty_cursor c
      ({cv := evalHistory c iv m.history, previous := m.previous, consumed := m.consumed, output := out} : State) m.run hr
    simp only [closeRun, hr, ↓reduceIte, materialize, finish, hp, Bool.false_eq_true,
      ↓reduceIte, absorb_empty, evalHistory_append, List.foldl_cons, List.foldl_nil]
    simp only [hc] at ho hz ⊢
    simp only [ho, hz, evalFrame]
    have he := absorb_setOutput c
      ({cv := evalHistory c iv m.history, previous := m.previous} : State) out m.run
    change absorb c {cv := evalHistory c iv m.history, previous := m.previous, output := out} m.run =
      {absorb c {cv := evalHistory c iv m.history, previous := m.previous} m.run with output := out} at he
    rw [he, finalized_setOutput]

def modelAbsorb (m : Model) (bs : List Byte) : Model :=
  if bs = [] then m else
    {m with run := m.run ++ bs, previous := if m.consumed = 0 then m.previous else m.consumed, consumed := 0}

theorem absorb_materialize (c : Compression) (iv : Digest32) (m : Model) (out : Digest32)
    (h : m.Valid) (bs : List Byte) :
    absorb c (materialize c iv m out) bs = materialize c iv (modelAbsorb m bs) out := by
  by_cases hb : bs = []
  · simp [modelAbsorb, hb]
  · by_cases hr : m.run = []
    · simp only [materialize, hr, absorb_empty, modelAbsorb, hb, ↓reduceIte, List.nil_append]
      exact absorb_switch c _ _ hb
    · have hc := h.1 hr
      simp only [modelAbsorb, hb, ↓reduceIte, hc, materialize, absorb_append]

theorem modelAbsorb_valid (m : Model) (h : m.Valid) (bs : List Byte) :
    (modelAbsorb m bs).Valid := by
  by_cases hb : bs = []
  · simpa [modelAbsorb, hb] using h
  · simp only [modelAbsorb, hb, ↓reduceIte, Model.Valid]
    refine ⟨by simp, ?_, by simp [maxCursor], ?_⟩
    · intro he
      exact False.elim (hb (List.append_eq_nil_iff.mp he).2)
    · split
      · exact h.2.2.2
      · exact h.2.2.1

theorem absorb_represents (c : Compression) (iv : Digest32) (m : Model) (s : State)
    (h : Represents c iv m s) (bs : List Byte) :
    Represents c iv (modelAbsorb m bs) (absorb c s bs) := by
  refine ⟨modelAbsorb_valid m h.1 bs, ?_, ?_⟩
  · rw [absorb_output]
    calc
      absorb c s bs = absorb c (materialize c iv m s.output) bs := congrArg (fun t => absorb c t bs) h.2.1
      _ = materialize c iv (modelAbsorb m bs) s.output := absorb_materialize c iv m s.output h.1 bs
  · by_cases hb : bs = []
    · simpa [hb] using h.2.2
    · intro hn
      have hz := absorb_nonempty_cursor c s bs hb
      exact False.elim (hn (by rw [hz]))

theorem seed_represents (c : Compression) (iv domain statement : Digest32) :
    Represents c iv ⟨⟨domain,statement,[]⟩,[],0,0⟩ (seed c iv domain statement) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [Model.Valid, maxCursor]
  · rfl
  · simp [CacheValid, seed]

theorem closeRun_consumed (m : Model) : (closeRun m).consumed = m.consumed := by
  unfold closeRun; split <;> rfl

theorem materialize_closed (c : Compression) (iv : Digest32) (m : Model) (out : Digest32)
    (valid : m.Valid) (empty : m.run = []) :
    materialize c iv m out = {cv := evalHistory c iv m.history, consumed := m.consumed, output := out} := by
  simp only [materialize, empty, absorb_empty, valid.2.1 empty]

theorem finish_cache (c : Compression) (iv : Digest32) (m : Model) (s : State)
    (h : Represents c iv m s) : CacheValid c (finish c s) := by
  by_cases hr : m.run = []
  · have he : finish c s = s := by
      rw [h.2.1, finish_materialize c iv m s.output h.1]
      simp [closeRun, hr]
    rw [he]
    exact h.2.2
  · have hz : s.consumed = 0 := by
      rw [h.2.1, materialize_consumed c iv m s.output h.1, h.1.1 hr]
    intro hn
    exact False.elim (hn (by rw [finish_consumed, hz]))

theorem finish_represents (c : Compression) (iv : Digest32) (m : Model) (s : State)
    (h : Represents c iv m s) : Represents c iv (closeRun m) (finish c s) := by
  refine ⟨closeRun_valid m h.1, ?_, finish_cache c iv m s h⟩
  have ho : (finish c s).output = s.output := by unfold finish; split <;> rfl
  rw [ho]
  exact (congrArg (finish c) h.2.1).trans (finish_materialize c iv m s.output h.1)

theorem state_ext {s t : State} (cv : s.cv = t.cv) (pending : s.pending = t.pending)
    (first : s.first = t.first) (previous : s.previous = t.previous)
    (consumed : s.consumed = t.consumed) (output : s.output = t.output) : s = t := by
  cases s; cases t; simp_all

theorem squeezeLoop_first (c : Compression) (n : Nat) (s : State) :
    (squeezeLoop c n s).1.first = s.first := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simp only [squeezeLoop, ih, squeezeByte]

theorem squeezeLoop_previous (c : Compression) (n : Nat) (s : State) :
    (squeezeLoop c n s).1.previous = s.previous := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simp only [squeezeLoop, ih, squeezeByte]

def modelSqueeze (m : Model) (n : Nat) : Model :=
  if n = 0 then m else {closeRun m with consumed := m.consumed + n}

theorem squeeze_represents (c : Compression) (iv : Digest32) (m : Model) (s t : State)
    (h : Represents c iv m s) (n : Nat) (bs : List Byte)
    (ok : squeeze c s n = .ok (t,bs)) :
    Represents c iv (modelSqueeze m n) t := by
  by_cases hn : n = 0
  · subst n
    simp only [squeeze_empty, Except.ok.injEq, Prod.mk.injEq] at ok
    rcases ok with ⟨rfl, rfl⟩
    simpa [modelSqueeze] using h
  · have hc : s.consumed = m.consumed := by
      rw [h.2.1, materialize_consumed c iv m s.output h.1]
    unfold squeeze at ok
    simp only [hn, ↓reduceIte] at ok
    split at ok
    next limit =>
      have he := Except.ok.inj ok
      have ht : t = (squeezeLoop c n (finish c s)).1 := (congrArg Prod.fst he).symm
      subst t
      have hf := finish_represents c iv m s h
      have hem := closeRun_empty m
      have hm := materialize_closed c iv (closeRun m) (finish c s).output hf.1 hem
      have hs : finish c s = {cv := evalHistory c iv (closeRun m).history, consumed := m.consumed, output := (finish c s).output} := by
        simpa only [closeRun_consumed] using hf.2.1.trans hm
      refine ⟨?_, ?_, squeezeLoop_cache c (finish c s) n hf.2.2⟩
      · simp only [modelSqueeze, hn, ↓reduceIte, Model.Valid, hem]
        refine ⟨by simp, fun _ => hf.1.2.1 hem, ?_, hf.1.2.2.2⟩
        simpa only [hc] using limit
      · simp only [modelSqueeze, hn, ↓reduceIte, materialize, hem, absorb_empty]
        apply state_ext
        · rw [squeezeLoop_cv, hs]
        · rw [squeezeLoop_pending, finish_pending]
        · rw [squeezeLoop_first, hs]
        · rw [squeezeLoop_previous, hs, hf.1.2.1 hem]
        · rw [squeezeLoop_consumed, finish_consumed, hc]
        · rfl
    next => cases ok

/-- The actual bytes, including a partial final block, are exactly the
canonical terminal stream at the completed history; unused bytes are not new
independent challenges and never enter the live chaining value. -/
theorem squeeze_frame_bytes (c : Compression) (iv : Digest32) (m : Model) (s t : State)
    (h : Represents c iv m s) (n : Nat) (bs : List Byte)
    (ok : squeeze c s n = .ok (t,bs)) :
    bs = stream c (evalHistory c iv (closeRun m).history) m.consumed n := by
  by_cases hn : n = 0
  · subst n; simp only [squeeze_empty, Except.ok.injEq, Prod.mk.injEq] at ok
    simpa [stream] using ok.2.symm
  · have hf := finish_represents c iv m s h
    have hm := materialize_closed c iv (closeRun m) (finish c s).output hf.1 (closeRun_empty m)
    have hcv := congrArg State.cv (hf.2.1.trans hm)
    have hc := materialize_consumed c iv m s.output h.1
    have hsc : s.consumed = m.consumed := (congrArg State.consumed h.2.1).trans hc
    unfold squeeze at ok
    simp only [hn, ↓reduceIte] at ok
    split at ok
    next =>
      have hb := congrArg Prod.snd (Except.ok.inj ok)
      rw [squeezeLoop_stream c _ n hf.2.2, hcv, finish_consumed, hsc] at hb
      exact hb.symm
    next => cases ok

def modelNonce (m : Model) (nonce : Scalar24) (bits : Nat) : Model :=
  let m := closeRun m
  {history := {m.history with frames := m.history.frames ++ [.nonce m.consumed bits nonce]}}

theorem nonce_represents (c : Compression) (iv : Digest32) (m : Model) (s : State)
    (h : Represents c iv m s) (nonce : Scalar24) (bits : Nat) :
    Represents c iv (modelNonce m nonce bits) (bindNonce c s nonce bits) := by
  have hf := finish_represents c iv m s h
  have hm := materialize_closed c iv (closeRun m) (finish c s).output hf.1 (closeRun_empty m)
  have hs := hf.2.1.trans hm
  refine ⟨?_, ?_, ?_⟩
  · simp [modelNonce, Model.Valid, maxCursor]
  · simp only [bindNonce, modelNonce, materialize, absorb_empty,
      evalHistory_append, List.foldl_cons, List.foldl_nil, evalFrame]
    rw [hs]
  · simp [CacheValid, bindNonce]

theorem bindNonce_finish (c : Compression) (s : State) (nonce : Scalar24) (bits : Nat) :
    bindNonce c (finish c s) nonce bits = bindNonce c s nonce bits := by
  simp only [bindNonce, finish_idempotent]

/-- The verification result does not suppress the nonce event on failure. -/
theorem verifyNonce_represents (c : Compression) (powOK : Digest32 → Scalar24 → Nat → Bool)
    (iv : Digest32) (m : Model) (s t : State) (h : Represents c iv m s)
    (nonce : Scalar24) (bits : Nat) (accepted : Bool)
    (ok : verifyNonce c powOK s nonce bits = .ok (t,accepted)) :
    Represents c iv (modelNonce m nonce bits) t := by
  unfold verifyNonce at ok
  split at ok
  next =>
    have he := congrArg Prod.fst (Except.ok.inj ok)
    simp only [bindNonce_finish] at he
    rw [← he]
    exact nonce_represents c iv m s h nonce bits
  next => cases ok

theorem finalized_history (c : Compression) (iv : Digest32) (m : Model) (s : State)
    (h : Represents c iv m s) :
    finalized c s = evalHistory c iv (closeRun m).history := by
  have hf := finish_represents c iv m s h
  have hm := materialize_closed c iv (closeRun m) (finish c s).output hf.1 (closeRun_empty m)
  exact (finish_cv c s).symm.trans (congrArg State.cv (hf.2.1.trans hm))

theorem commitment_frame (c : Compression) (iv : Digest32) (m : Model) (s : State)
    (h : Represents c iv m s) :
    commitment c s = evalCoordinate c iv ⟨(closeRun m).history, .commitment m.consumed⟩ := by
  have hc : s.consumed = m.consumed :=
    (congrArg State.consumed h.2.1).trans (materialize_consumed c iv m s.output h.1)
  simp only [commitment, evalCoordinate, evalTerminal, finalized_history c iv m s h, hc]

theorem powBase_frame (c : Compression) (iv : Digest32) (m : Model) (s : State)
    (h : Represents c iv m s) (bits : Nat) :
    powBase c s bits = evalCoordinate c iv ⟨(closeRun m).history, .powBase m.consumed bits⟩ := by
  have hc : s.consumed = m.consumed :=
    (congrArg State.consumed h.2.1).trans (materialize_consumed c iv m s.output h.1)
  simp only [powBase, evalCoordinate, evalTerminal, finalized_history c iv m s h, hc]

/-- Source-level operations only: finish is internal, not a history-splitting
API. Export and cloning are nonmutating; their correspondence is above. -/
inductive Reachable (c : Compression) (iv domain statement : Digest32) : Model → State → Prop where
  | seed : Reachable c iv domain statement ⟨⟨domain,statement,[]⟩,[],0,0⟩ (seed c iv domain statement)
  | absorb {m s} (h : Reachable c iv domain statement m s) (bs : List Byte) :
      Reachable c iv domain statement (modelAbsorb m bs) (absorb c s bs)
  | squeeze {m s t bs} (h : Reachable c iv domain statement m s) (n : Nat)
      (ok : squeeze c s n = .ok (t,bs)) :
      Reachable c iv domain statement (modelSqueeze m n) t
  | nonce {m s} (h : Reachable c iv domain statement m s) (nonce : Scalar24) (bits : Nat)
      (limit : bits ≤ 63) :
      Reachable c iv domain statement (modelNonce m nonce bits) (bindNonce c s nonce bits)

theorem reachable_represents (c : Compression) (iv domain statement : Digest32)
    {m : Model} {s : State} (h : Reachable c iv domain statement m s) : Represents c iv m s := by
  induction h with
  | seed => exact seed_represents c iv domain statement
  | absorb _ bs ih => exact absorb_represents c iv _ _ ih bs
  | squeeze _ n ok ih => exact squeeze_represents c iv _ _ _ ih n _ ok
  | nonce _ nonce bits limit ih => exact nonce_represents c iv _ _ ih nonce bits

/-- Public helper's panic conditions, represented as explicit model errors. -/
def checkedAbsorbTweak (first last : Bool) (len previous : Nat) : Except Error UInt64 :=
  if 0 < len ∧ len ≤ 64 ∧ (last = true ∨ len = 64) then
    if previous ≤ maxCursor ∧ (first = true ∨ previous = 0) then
      .ok (absorbTweak first last len previous)
    else .error .absorbCursor
  else .error .absorbLength

theorem checkedAbsorbTweak_ok (first last : Bool) (len previous : Nat) (v : UInt64)
    (h : checkedAbsorbTweak first last len previous = .ok v) :
    0 < len ∧ len ≤ 64 ∧ (last = true ∨ len = 64) ∧
    previous ≤ maxCursor ∧ (first = true ∨ previous = 0) ∧
    v = absorbTweak first last len previous := by
  unfold checkedAbsorbTweak at h
  split at h
  next hl =>
    split at h
    next hp => cases h; exact ⟨hl.1,hl.2.1,hl.2.2,hp.1,hp.2,rfl⟩
    next => cases h
  next => cases h

def sample (c : Compression) (s : State) : Except Error (State × Concrete.E) :=
  match h : squeeze c s 24 with
  | .error e => .error e
  | .ok (t,bs) =>
    .ok (t, ByteCodec.decodeE (fun i => bs[i.val]'(by
      have hl := (squeeze_exact_cursor c s t 24 bs h).2
      omega)))

/-- One globally checked request before allocating the vector. Squeezing the
concatenation agrees with repeated samples by `squeeze_concat`. -/
def sampleVec (c : Compression) (s : State) (n : Nat) : Except Error (State × List Concrete.E) :=
  match h : squeeze c s (24*n) with
  | .error e => .error e
  | .ok (t,bs) =>
    .ok (t, List.ofFn (fun j : Fin n => ByteCodec.decodeE (fun i =>
      bs[24*j.val+i.val]'(by
        have hl := (squeeze_exact_cursor c s t (24*n) bs h).2
        have := j.isLt
        have := i.isLt
        omega))))

theorem sample_frame (c : Compression) (iv : Digest32) (m : Model) (s : State)
    (h : Represents c iv m s) (t : State) (x : Concrete.E) (ok : sample c s = .ok (t,x)) :
    Represents c iv (modelSqueeze m 24) t := by
  unfold sample at ok
  split at ok
  next e he => cases ok
  next t' bs hs =>
    have ht := congrArg Prod.fst (Except.ok.inj ok)
    cases ht
    exact squeeze_represents c iv m s t h 24 bs hs

def searchNonce (test : UInt64 → Bool) : Nat → Nat → Option UInt64
  | 0, _ => none
  | remaining+1, start =>
    let n := UInt64.ofNat start
    if test n then some n else searchNonce test remaining (start+1)

/-- Reference smallest-nonce search. Parallel Rust's contiguous-window search
has the same selection rule; this model does not reproduce its scheduling. -/
def grind (c : Compression) (powOK : Digest32 → Scalar24 → Nat → Bool)
    (s : State) (bits : Nat) : Except Error (State × UInt64) :=
  if bits ≤ 63 then
    let s := finish c s
    let candidate := if bits = 0 then some (0 : UInt64) else
      let base := Array.ofFn (powBase c s bits)
      searchNonce (fun n => powOK (fun i => base[i.val]'(by simp only [base, Array.size_ofFn]; exact i.isLt))
        (ByteCodec.encodeE ⟨n,0,0⟩) bits) (2^64) 0
    match candidate with
    | none => .error .nonceExhausted
    | some n => .ok (bindNonce c s (ByteCodec.encodeE ⟨n,0,0⟩) bits,n)
  else .error .grindingBits

theorem grind_zero (c : Compression) (powOK : Digest32 → Scalar24 → Nat → Bool) (s : State) :
    grind c powOK s 0 = .ok (bindNonce c s (ByteCodec.encodeE ⟨0,0,0⟩) 0,0) := by
  simp [grind, bindNonce_finish]

theorem searchNonce_smallest (test : UInt64 → Bool) (remaining start : Nat) (n : UInt64)
    (bound : start + remaining ≤ 2^64) (ok : searchNonce test remaining start = some n) :
    start ≤ n.toNat ∧ n.toNat < start + remaining ∧ test n = true ∧
      ∀ k, start ≤ k → k < n.toNat → test (UInt64.ofNat k) = false := by
  induction remaining generalizing start with
  | zero => simp [searchNonce] at ok
  | succ remaining ih =>
    have hs : start < 2^64 := by omega
    simp only [searchNonce] at ok
    split at ok
    next ht =>
      cases ok
      have hn : (UInt64.ofNat start).toNat = start := by
        simp only [UInt64.toNat_ofNat', Nat.mod_eq_of_lt hs]
      rw [hn]
      exact ⟨by omega, by omega, ht, by intros; omega⟩
    next ht =>
      obtain ⟨hl,hu,hpass,hprior⟩ := ih (start+1) (by omega) ok
      refine ⟨by omega, by omega, hpass, ?_⟩
      intro k hk hkn
      by_cases he : k = start
      · subst k; simpa using ht
      · exact hprior k (by omega) hkn

theorem sampleVec_frame (c : Compression) (iv : Digest32) (m : Model) (s : State)
    (h : Represents c iv m s) (n : Nat) (t : State) (xs : List Concrete.E)
    (ok : sampleVec c s n = .ok (t,xs)) :
    Represents c iv (modelSqueeze m (24*n)) t ∧ xs.length = n := by
  unfold sampleVec at ok
  split at ok
  next e he => cases ok
  next t' bs hs =>
    have ht := congrArg Prod.fst (Except.ok.inj ok)
    have hx := congrArg Prod.snd (Except.ok.inj ok)
    cases ht
    refine ⟨squeeze_represents c iv m s t h (24*n) bs hs, ?_⟩
    simpa using congrArg List.length hx.symm

theorem squeeze_concatenates (c : Compression) (s : State) (a b : Nat)
    (limit : s.consumed + (a+b) ≤ maxCursor) :
    squeeze c s (a+b) =
      match squeeze c s a with
      | .error e => .error e
      | .ok (t,xs) => match squeeze c t b with
        | .error e => .error e
        | .ok (u,ys) => .ok (u,xs++ys) := by
  by_cases ha : a = 0
  · subst a
    simp only [Nat.zero_add, squeeze_empty, List.nil_append]
    cases squeeze c s b <;> rfl
  · by_cases hb : b = 0
    · subst b
      simp only [Nat.add_zero]
      cases squeeze c s a <;> simp [squeeze_empty]
    · exact squeeze_concat c s a b ha hb limit

/-- The query vector and its adjacent lambda occupy one uninterrupted squeeze
run, with exactly 24*(chunks+1) consumed bytes and no intervening message. -/
theorem query_lambda_concatenates (c : Compression) (s : State) (chunks : Nat)
    (limit : s.consumed + 24*(chunks+1) ≤ maxCursor) :
    squeeze c s (24*(chunks+1)) =
      match squeeze c s (24*chunks) with
      | .error e => .error e
      | .ok (t,xs) => match squeeze c t 24 with
        | .error e => .error e
        | .ok (u,ys) => .ok (u,xs++ys) := by
  simpa only [Nat.mul_add, Nat.mul_one] using squeeze_concatenates c s (24*chunks) 24
    (by simpa only [Nat.mul_add, Nat.mul_one] using limit)

theorem grind_frame (c : Compression) (powOK : Digest32 → Scalar24 → Nat → Bool)
    (iv : Digest32) (m : Model) (s t : State) (h : Represents c iv m s)
    (bits : Nat) (n : UInt64) (ok : grind c powOK s bits = .ok (t,n)) :
    Represents c iv (modelNonce m (ByteCodec.encodeE ⟨n,0,0⟩) bits) t := by
  unfold grind at ok
  split at ok
  next hb =>
    dsimp only at ok
    split at ok
    next => cases ok
    next nonce hc =>
      have he := Except.ok.inj ok
      have hs := congrArg Prod.fst he
      have hn := congrArg Prod.snd he
      cases hn
      simp only [bindNonce_finish] at hs
      rw [← hs]
      exact nonce_represents c iv m s h _ bits
  next => cases ok

theorem absorbTweak_injective {first last first' last' : Bool} {len previous len' previous' : Nat}
    (hl : len ≤ 64) (hl' : len' ≤ 64) (hp : previous ≤ maxCursor) (hp' : previous' ≤ maxCursor)
    (same : absorbTweak first last len previous = absorbTweak first' last' len' previous') :
    first = first' ∧ last = last' ∧ len = len' ∧ previous = previous' := by
  have hr : role first last ≤ 5 := by cases first <;> cases last <;> decide
  have hr' : role first' last' ≤ 5 := by cases first' <;> cases last' <;> decide
  have hp0 : previous < 2^49 := by unfold maxCursor at hp; omega
  have hp0' : previous' < 2^49 := by unfold maxCursor at hp'; omega
  have hb : packTweak (role first last) len previous < 2^64 := by unfold packTweak; omega
  have hb' : packTweak (role first' last') len' previous' < 2^64 := by unfold packTweak; omega
  have he := congrArg UInt64.toNat same
  simp only [absorbTweak, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hb'] at he
  obtain ⟨hrole, hlen, hprev⟩ := packTweak_injective (by omega) (by omega) hp0 hp0' he
  obtain ⟨hf,hlast⟩ := role_injective hrole
  exact ⟨hf,hlast,hlen,hprev⟩

/-- Arithmetic framing is exactly the source's disjoint-field bitwise OR,
not merely an injective alternative encoding. -/
theorem packTweak_or (r len previous : Nat) (hl : len < 128) (hp : previous < 2^49) :
    packTweak r len previous = ((r <<< 56) ||| (len <<< 49)) ||| previous := by
  have lower : len * 2^49 + previous < 2^56 := by omega
  have h0 := Nat.shiftLeft_add_eq_or_of_lt hp len
  have h1 := Nat.shiftLeft_add_eq_or_of_lt lower r
  simp only [Nat.shiftLeft_eq] at h0 h1 ⊢
  unfold packTweak
  rw [Nat.add_assoc, h1, h0, Nat.or_assoc]

theorem absorbTweak_source_bits (first last : Bool) (len previous : Nat)
    (hl : len ≤ 64) (hp : previous ≤ maxCursor) :
    absorbTweak first last len previous =
      ((UInt64.ofNat (role first last) <<< 56) ||| (UInt64.ofNat len <<< 49)) |||
        UInt64.ofNat previous := by
  have hp' : previous < 2^49 := by unfold maxCursor at hp; omega
  rw [absorbTweak, packTweak_or _ _ _ (by omega) hp']
  simp only [UInt64.ofNat_or, UInt64.ofNat_shiftLeft _ 56 (by decide), UInt64.ofNat_shiftLeft _ 49 (by decide)]
  rfl

end Whir.DuplexRefinement
