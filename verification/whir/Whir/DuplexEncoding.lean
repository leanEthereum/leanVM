import Whir.DuplexRefinement

/-! Exact syntactic encoding of the normalized #552 framed-byte history.
Observe call boundaries and empty calls are absent from `Frame`; nonempty runs
are separated only by an actual squeeze or nonce event. No compression function
or collision assumption occurs in this codec. -/
namespace Whir.DuplexEncoding
open FiatShamirGame DuplexRefinement

abbrev Instruction := Block64 × UInt64

def chunk (first last : Bool) (previous : Nat) (bytes : List Byte) : Instruction :=
  (padded bytes.toArray, absorbTweak first last bytes.length previous)

/-- Retain a full block until another byte proves it nonfinal. -/
def chunks (first : Bool) (previous : Nat) (pending : List Byte) : List Byte → List Instruction
  | [] => if pending = [] then [] else [chunk first true previous pending]
  | b :: bs =>
    if pending.length = 64 then
      chunk first false previous pending :: chunks false 0 [b] bs
    else chunks first previous (pending ++ [b]) bs

def framePlan : Frame → List Instruction
  | .absorb previous bytes => chunks true previous [] bytes
  | .nonce previous bits nonce => [(nonceBlock nonce previous bits, UInt64.ofNat (9 * 2^56))]

def terminalPlan : Terminal → Instruction
  | .output block => (wordsBlock [block], UInt64.ofNat (6 * 2^56))
  | .commitment consumed => (wordsBlock [consumed], UInt64.ofNat (7 * 2^56))
  | .powBase consumed bits => (wordsBlock [consumed,bits], UInt64.ofNat (8 * 2^56))

/-- Chronological public-compression inputs. The parameter IV is fixed externally,
not a selectable field in the semantic history. Every compression final flag is true. -/
def plan (q : Coordinate) : List Instruction :=
  (ByteCodec.pairBytes (q.history.domain,q.history.statement), UInt64.ofNat (2^56)) ::
    q.history.frames.flatMap framePlan ++ [terminalPlan q.terminal]

def FrameValid : Frame → Prop
  | .absorb previous bytes => previous < 2^49 ∧ bytes ≠ []
  | .nonce previous bits _ => previous < 2^49 ∧ bits ≤ 63

def TerminalValid : Terminal → Prop
  | .output block => block < 2^44
  | .commitment consumed => consumed < 2^49
  | .powBase consumed bits => consumed < 2^49 ∧ bits ≤ 63

/-- A syntactic superdomain of reachable normalized histories: no empty ordinary
frame, bounded cursors/difficulties, and a bounded output block. Actual source
reachability may restrict it further without weakening the injection theorem. -/
def Admissible (q : Coordinate) : Prop :=
  (∀ f ∈ q.history.frames, FrameValid f) ∧ TerminalValid q.terminal

def blockBytes (b : Block64) : List Byte := List.ofFn b

def takeBytes (b : Block64) (n : Nat) : List Byte := (blockBytes b).take n

def wordAt (b : Block64) (offset : Nat) : Nat :=
  ByteCodec.decodeNat 8 (fun i => ((blockBytes b)[offset + i.val]?).getD 0)

def readRole (t : UInt64) : Nat := t.toNat / 2^56
def readLength (t : UInt64) : Nat := t.toNat / 2^49 % 128
def readPrevious (t : UInt64) : Nat := t.toNat % 2^49

/-- Read one ordinary run. Its continuation cursor is always zero. -/
def readRun (first : Bool) : List Instruction → Option (Nat × List Byte × List Instruction)
  | [] => none
  | (b,t) :: rest =>
    if readRole t = role first true then
      some (readPrevious t, takeBytes b (readLength t), rest)
    else if readRole t = role first false then
      match readRun false rest with
      | some (_, bytes, tail) => some (readPrevious t, takeBytes b (readLength t) ++ bytes, tail)
      | none => none
    else none

theorem readRun_shorter (first : Bool) (xs : List Instruction) (p : Nat) (bs : List Byte)
    (tail : List Instruction) (h : readRun first xs = some (p,bs,tail)) :
    tail.length < xs.length := by
  induction xs generalizing first p bs tail with
  | nil => simp [readRun] at h
  | cons x xs ih =>
    rcases x with ⟨b,t⟩
    simp only [readRun] at h
    split at h
    · cases h; simp
    · split at h
      · split at h
        · cases h
          have := ih _ _ _ _ (by assumption)
          simp only [List.length_cons]; omega
        · cases h
      · cases h

/-- The raw parser is deliberately permissive about padding. `decode` below
rejects every noncanonical encoding by checking the reconstructed exact plan. -/
def readBody : List Instruction → Option (List Frame × Terminal)
  | [] => none
  | [(b,t)] =>
    if readRole t = 6 then some ([], .output (wordAt b 0))
    else if readRole t = 7 then some ([], .commitment (wordAt b 0))
    else if readRole t = 8 then some ([], .powBase (wordAt b 0) (wordAt b 8))
    else none
  | (b,t) :: next :: rest =>
    if readRole t = 9 then
      match readBody (next :: rest) with
      | some (fs, terminal) => some (.nonce (wordAt b 24) (wordAt b 32)
          (fun i => b ⟨i.val, by omega⟩) :: fs, terminal)
      | none => none
    else
      match h : readRun true ((b,t) :: next :: rest) with
      | some (previous, bytes, tail) =>
        match readBody tail with
        | some (fs, terminal) => some (.absorb previous bytes :: fs, terminal)
        | none => none
      | none => none
termination_by xs => xs.length

decreasing_by
  · simp_wf
  · have hs := readRun_shorter true _ _ _ _ h
    simp_all only [List.length_cons]
def parse : List Instruction → Option Coordinate
  | [] => none
  | (b,t) :: rest =>
    if readRole t = 1 then
      match readBody rest with
      | some (fs, terminal) => some ⟨⟨(fun i => b ⟨i.val, by omega⟩),
          (fun i => b ⟨i.val + 32, by omega⟩), fs⟩, terminal⟩
      | none => none
    else none

instance (f : Frame) : Decidable (FrameValid f) := by cases f <;> unfold FrameValid <;> infer_instance
instance (t : Terminal) : Decidable (TerminalValid t) := by cases t <;> unfold TerminalValid <;> infer_instance
instance (q : Coordinate) : Decidable (Admissible q) := inferInstanceAs (Decidable (_ ∧ _))

def decode (xs : List Instruction) : Option Coordinate :=
  match parse xs with
  | none => none
  | some q => if Admissible q ∧ plan q = xs then some q else none

 theorem decode_sound {xs : List Instruction} {q : Coordinate} (h : decode xs = some q) :
    Admissible q ∧ plan q = xs := by
  unfold decode at h
  split at h
  · cases h
  · split at h
    · cases h; assumption
    · cases h

theorem packed_fields (first last : Bool) (len previous : Nat)
    (hl : len ≤ 64) (hp : previous < 2^49) :
    readRole (absorbTweak first last len previous) = role first last ∧
    readLength (absorbTweak first last len previous) = len ∧
    readPrevious (absorbTweak first last len previous) = previous := by
  have hr : role first last < 256 := by cases first <;> cases last <;> decide
  simp only [readRole, readLength, readPrevious, absorbTweak, UInt64.toNat_ofNat', packTweak]
  omega

theorem takeBytes_padded (bs : List Byte) (h : bs.length ≤ 64) :
    takeBytes (padded bs.toArray) bs.length = bs := by
  apply List.ext_getElem
  · simp [takeBytes, blockBytes, Nat.min_eq_left h]
  · intro i hi hi'
    simp only [takeBytes, blockBytes, List.getElem_take, List.getElem_ofFn, padded]
    simp [hi']

theorem wordAt_padded (bs : List Byte) (offset : Nat) (h : offset + 8 ≤ 64) :
    wordAt (padded bs.toArray) offset =
      ByteCodec.decodeNat 8 (fun i => (bs[offset + i.val]?).getD 0) := by
  unfold wordAt
  congr 1
  funext i
  have hi : offset + i.val < 64 := by omega
  simp only [blockBytes, List.getElem?_ofFn, dite_eq_left hi, padded, Option.getD_some]
  simp

theorem readRun_chunks (first : Bool) (previous : Nat) (pending bs : List Byte)
    (tail : List Instruction) (hp : previous < 2^49)
    (hlen : pending.length ≤ 64) (hne : pending ++ bs ≠ []) :
    readRun first (chunks first previous pending bs ++ tail) =
      some (previous, pending ++ bs, tail) := by
  induction bs generalizing first previous pending with
  | nil =>
    have hn : pending ≠ [] := by simpa using hne
    simp only [chunks, hn, ↓reduceIte, List.singleton_append, readRun, chunk]
    rw [(packed_fields first true pending.length previous hlen hp).1]
    simp only [↓reduceIte]
    rw [(packed_fields first true pending.length previous hlen hp).2.1,
      (packed_fields first true pending.length previous hlen hp).2.2, takeBytes_padded pending hlen]
    simp
  | cons b bs ih =>
    by_cases full : pending.length = 64
    · simp only [chunks, full, ↓reduceIte, List.cons_append, readRun, chunk]
      rw [← full, (packed_fields first false pending.length previous hlen hp).1]
      have roles : role first false ≠ role first true := by cases first <;> decide
      simp only [roles, ↓reduceIte]
      rw [ih false 0 [b] (by decide) (by simp) (by simp)]
      rw [(packed_fields first false pending.length previous hlen hp).2.1,
        (packed_fields first false pending.length previous hlen hp).2.2,
        takeBytes_padded pending hlen]
      rfl
    · simp only [chunks, full, ↓reduceIte]
      have hs : (pending ++ [b]).length ≤ 64 := by simp; omega
      simpa only [List.append_assoc, List.singleton_append] using
        ih first previous (pending ++ [b]) hp hs (by simp)

theorem wordAt_segment (pre post : List Byte) (n : Nat)
    (hoff : pre.length + 8 ≤ 64) (hn : n < 256^8) :
    wordAt (padded (pre ++ littleWord n ++ post).toArray) pre.length = n := by
  rw [wordAt_padded _ _ hoff]
  have he : (fun i : Fin 8 =>
      ((pre ++ littleWord n ++ post)[pre.length + i.val]?).getD 0) = ByteCodec.encodeNat 8 n := by
    funext i
    have hi : i.val < (littleWord n).length := by simpa only [littleWord, List.length_ofFn] using i.isLt
    rw [List.append_assoc, List.getElem?_append_right (by omega : pre.length ≤ pre.length + i.val),
      Nat.add_sub_cancel_left, List.getElem?_append_left hi]
    simp only [littleWord, List.getElem?_ofFn, dite_eq_left i.isLt, Option.getD_some]
  rw [he, ByteCodec.decodeNat_encodeNat _ _ hn]

theorem wordAt_words_one (n : Nat) (hn : n < 256^8) :
    wordAt (wordsBlock [n]) 0 = n := by
  exact wordAt_segment [] [] n (by decide) hn

theorem wordAt_words_two_first (n m : Nat) (hn : n < 256^8) :
    wordAt (wordsBlock [n,m]) 0 = n := by
  exact wordAt_segment [] (littleWord m) n (by decide) hn

theorem wordAt_words_two_second (n m : Nat) (hm : m < 256^8) :
    wordAt (wordsBlock [n,m]) 8 = m := by
  exact wordAt_segment (littleWord n) [] m (by simp [littleWord]) hm

theorem wordAt_nonce_previous (nonce : Scalar24) (previous bits : Nat) (hp : previous < 256^8) :
    wordAt (nonceBlock nonce previous bits) 24 = previous := by
  exact wordAt_segment (List.ofFn nonce) (littleWord bits) previous (by simp) hp

theorem wordAt_nonce_bits (nonce : Scalar24) (previous bits : Nat) (hb : bits < 256^8) :
    wordAt (nonceBlock nonce previous bits) 32 = bits := by
  exact wordAt_segment (List.ofFn nonce ++ littleWord previous) [] bits
    (by simp [littleWord]) hb

theorem nonce_prefix (nonce : Scalar24) (previous bits : Nat) :
    (fun i : Fin 24 => nonceBlock nonce previous bits ⟨i.val, by omega⟩) = nonce := by
  funext i
  simp only [nonceBlock, padded, List.getElem?_toArray]
  have hi : i.val < (List.ofFn nonce).length := by simp
  simp only [List.append_assoc, List.getElem?_append_left hi, List.getElem?_ofFn,
    dite_eq_left i.isLt, Option.getD_some]

theorem terminal_recovery (t : Terminal) (ht : TerminalValid t) :
    readBody [terminalPlan t] = some ([],t) := by
  cases t with
  | output n =>
    have hn : n < 256^8 := by dsimp [TerminalValid] at ht; omega
    simp [readBody, terminalPlan, readRole, wordAt_words_one n hn]
  | commitment n =>
    have hn : n < 256^8 := by dsimp [TerminalValid] at ht; omega
    simp [readBody, terminalPlan, readRole, wordAt_words_one n hn]
  | powBase n m =>
    have hn : n < 256^8 := by dsimp [TerminalValid] at ht; omega
    have hm : m < 256^8 := by dsimp [TerminalValid] at ht; omega
    simp [readBody, terminalPlan, readRole, wordAt_words_two_first n m hn,
      wordAt_words_two_second n m hm]

theorem readRun_not_nonce (b : Block64) (t : UInt64) (xs : List Instruction)
    (p : Nat) (bs : List Byte) (tail : List Instruction)
    (h : readRun true ((b,t) :: xs) = some (p,bs,tail)) : readRole t ≠ 9 := by
  simp only [readRun] at h
  split at h
  · simp_all [role]
  · split at h
    · simp_all [role]
    · cases h

theorem readBody_run (xs : List Instruction) (p : Nat) (bs : List Byte)
    (tail : List Instruction) (fs : List Frame) (t : Terminal)
    (hr : readRun true xs = some (p,bs,tail)) (hn : tail ≠ [])
    (hb : readBody tail = some (fs,t)) :
    readBody xs = some (.absorb p bs :: fs,t) := by
  have hl := readRun_shorter true xs p bs tail hr
  cases xs with
  | nil => simp [readRun] at hr
  | cons x xs =>
    rcases x with ⟨b,tweak⟩
    cases xs with
    | nil =>
      have ht : tail.length = 0 := by simpa using Nat.lt_one_iff.mp hl
      exact False.elim (hn (List.length_eq_zero_iff.mp ht))
    | cons x xs =>
      have hrole := readRun_not_nonce b tweak (x :: xs) p bs tail hr
      simp only [readBody, hrole, ↓reduceIte]
      split
      · rename_i p' bs' tail' he
        have hparts := Option.some.inj (he.symm.trans hr)
        obtain ⟨rfl, rfl, rfl⟩ := Prod.mk.inj hparts |>.imp_right Prod.mk.inj
        simp only [hb]
      · rename_i he
        rw [hr] at he
        cases he

theorem frames_recovery (fs : List Frame) (t : Terminal)
    (hf : ∀ f ∈ fs, FrameValid f) (ht : TerminalValid t) :
    readBody (fs.flatMap framePlan ++ [terminalPlan t]) = some (fs,t) := by
  induction fs with
  | nil => exact terminal_recovery t ht
  | cons f fs ih =>
    have hv := hf f (by simp)
    have hb := ih (by intro f h; exact hf f (by simp [h]))
    cases f with
    | absorb p bs =>
      simp only [FrameValid] at hv
      have hr := readRun_chunks true p [] bs
        (fs.flatMap framePlan ++ [terminalPlan t]) hv.1 (by simp) (by simpa using hv.2)
      simp only [List.nil_append] at hr
      simpa only [List.flatMap_cons, framePlan, List.append_assoc] using
        readBody_run _ p bs _ fs t hr (by simp) hb
    | nonce p bits nonce =>
      simp only [FrameValid] at hv
      have hp : p < 256^8 := by omega
      have hbits : bits < 256^8 := by omega
      have hn : fs.flatMap framePlan ++ [terminalPlan t] ≠ [] := by simp
      generalize he : fs.flatMap framePlan ++ [terminalPlan t] = tail at *
      cases tail with
      | nil => contradiction
      | cons x xs =>
        simp only [List.flatMap_cons, framePlan, List.cons_append, List.nil_append, he]
        simp only [readBody, readRole, UInt64.toNat_ofNat', Nat.reducePow, Nat.reduceMul,
          Nat.reduceMod, Nat.reduceDiv, ↓reduceIte, hb]
        rw [wordAt_nonce_previous nonce p bits hp, wordAt_nonce_bits nonce p bits hbits,
          nonce_prefix]

theorem parse_plan (q : Coordinate) (h : Admissible q) : parse (plan q) = some q := by
  rcases q with ⟨⟨domain,statement,fs⟩,t⟩
  have hb := frames_recovery fs t h.1 h.2
  simp only [plan, List.cons_append, parse, readRole, UInt64.toNat_ofNat', Nat.reducePow, Nat.reduceMod,
    Nat.reduceDiv, ↓reduceIte, hb]
  congr 3
  funext i
  simp [ByteCodec.pairBytes, i.isLt]

theorem decode_plan (q : Coordinate) (h : Admissible q) : decode (plan q) = some q := by
  simp only [decode, parse_plan q h, h, and_self, ↓reduceIte]

theorem plan_injective {a b : Coordinate} (ha : Admissible a) (hb : Admissible b)
    (h : plan a = plan b) : a = b := by
  have := congrArg decode h
  simpa only [decode_plan a ha, decode_plan b hb, Option.some.injEq] using this

/-- The accepted raw language is exactly the image of the explicit syntactic
domain, not a decoder-correctness hypothesis. In particular this rejects
nonzero padding, empty ordinary chunks, bad role/length combinations, nonzero
continuation cursors, and out-of-range semantic metadata. -/
theorem decode_iff (xs : List Instruction) (q : Coordinate) :
    decode xs = some q ↔ Admissible q ∧ plan q = xs := by
  constructor
  · exact decode_sound
  · rintro ⟨h, rfl⟩
    exact decode_plan q h

end Whir.DuplexEncoding
