module

public import LeanVMCircuits.Rec.Statement

@[expose] public section

/-!
The Fiat-Shamir duplex, natively and in rows.

`Duplex` is `fiat_shamir::Duplex` on 64-bit words: every call the recursion verifier makes absorbs or squeezes whole
little-endian words (a scalar's three limbs), so its byte buffers hold whole words and its byte counts are multiples
of eight. Every compression is RFC 7693's `F` at the call's tweak as counter, final, of a chaining value and a
zero-padded block. `RowState` and the `...Rows` relations are `rec::transcript::Transcript`: the same bookkeeping,
each compression a hash row whose output is the next chaining value, each squeezed word read from the output block
of the row that computed it. `run_rows` proves the rows sample the native duplex's challenges.
-/

namespace LeanVMCircuits.Rec

open LeanVMCircuits.Blake2s Rfc7693

attribute [local irreducible] program

/-- `fiat_shamir`'s compression roles, in the counter word's top byte. -/
def seedTag : BitVec 64 := BitVec.ofNat 64 (1 * 2 ^ 56)
def outputTag : BitVec 64 := BitVec.ofNat 64 (6 * 2 ^ 56)
def commitTag : BitVec 64 := BitVec.ofNat 64 (7 * 2 ^ 56)
def powBaseTag : BitVec 64 := BitVec.ofNat 64 (8 * 2 ^ 56)
def nonceTag : BitVec 64 := BitVec.ofNat 64 (9 * 2 ^ 56)

/-- `fiat_shamir::absorb_tweak`: the role, the block's length in bytes, and the previous squeeze run's length. -/
def tweak (first last : Bool) (len previous : ℕ) : BitVec 64 :=
  let role := match first, last with
    | true, false => 2
    | false, false => 3
    | true, true => 4
    | false, true => 5
  BitVec.ofNat 64 (role * 2 ^ 56 + len * 2 ^ 49 + previous)

/-- A chaining value's eight 32-bit words from its four 64-bit words. -/
def cvWords (cv : Fin 4 → BitVec 64) : Vector (BitVec 32) 8 :=
  Vector.ofFn fun r => half (cv ⟨r.val / 2, by omega⟩) (r.val % 2)

theorem digest_cvWords (cv : Fin 4 → BitVec 64) (k : Fin 4) : digest (cvWords cv) k = cv k := by
  apply eq_of_halves
  · rw [half_digest _ k 0 (by omega)]
    simp only [cvWords, Vector.getElem_ofFn]
    congr 2 <;> simp
  · rw [half_digest _ k 1 (by omega)]
    simp only [cvWords, Vector.getElem_ofFn]
    congr 2
    · ext; simp only; omega
    · omega

/-- `fiat_shamir`'s `compress_block`: RFC 7693's `F` of the chaining value and the zero-padded block of `ws`, at
counter `t`, final. -/
def comp (cv : Fin 4 → BitVec 64) (ws : List (BitVec 64)) (t : BitVec 64) : Fin 4 → BitVec 64 :=
  digest (F (cvWords cv) (block ws 0) t true)

/-! The native duplex. -/

/-- `fiat_shamir::Duplex`: chaining value, pending words, whether the pending block is a run's first, the previous
squeeze run's length and this one's, in bytes. -/
structure Duplex where
  cv : Fin 4 → BitVec 64
  pending : List (BitVec 64)
  first : Bool
  previous : ℕ
  squeezed : ℕ

/-- `Duplex::new`: the seed node of the domain and statement digests. -/
def Duplex.new (domain statement : Fin 4 → BitVec 64) : Duplex :=
  ⟨comp (digest paramIV) (List.ofFn domain ++ List.ofFn statement) seedTag, [], true, 0, 0⟩

/-- `Duplex::absorb` of one word. -/
def Duplex.absorbWord (d : Duplex) (w : BitVec 64) : Duplex :=
  let d := if d.squeezed ≠ 0 then { d with previous := d.squeezed, squeezed := 0 } else d
  let d := if d.pending.length = 8 then
      { d with cv := comp d.cv d.pending (tweak d.first false 64 d.previous), first := false, previous := 0,
               pending := [] }
    else d
  { d with pending := d.pending ++ [w] }

/-- `Duplex::finish_absorb`. -/
def Duplex.finishAbsorb (d : Duplex) : Duplex :=
  if d.pending = [] then d else
    { d with cv := comp d.cv d.pending (tweak d.first true (8 * d.pending.length) d.previous), pending := [],
             first := true, previous := 0 }

/-- `Duplex::squeeze` of one word: word `squeezed % 32 / 8` of output block `squeezed / 32`. -/
def Duplex.squeezeWord (d : Duplex) : Duplex × BitVec 64 :=
  let d := d.finishAbsorb
  ({ d with squeezed := d.squeezed + 8 },
    comp d.cv [BitVec.ofNat 64 (d.squeezed / 32)] outputTag ⟨d.squeezed % 32 / 8, by omega⟩)

/-- `Duplex::commitment`. -/
def Duplex.commitment (d : Duplex) : Fin 4 → BitVec 64 :=
  comp d.finishAbsorb.cv [BitVec.ofNat 64 d.squeezed] commitTag

/-- `Duplex::absorb_nonce`. -/
def Duplex.absorbNonce (d : Duplex) (n : Fin 3 → BitVec 64) (bits : ℕ) : Duplex :=
  let d := d.finishAbsorb
  { d with cv := comp d.cv [n 0, n 1, n 2, BitVec.ofNat 64 d.squeezed, BitVec.ofNat 64 bits] nonceTag,
           squeezed := 0 }

/-- What the recursion verifier does with a transcript: observe a scalar's limbs, sample one, bind a nonce. -/
inductive Op where
  | observe (x : Fin 3 → BitVec 64)
  | sample
  | nonce (n : Fin 3 → BitVec 64) (bits : ℕ)

/-- One operation, natively, with the words it samples. -/
def Duplex.step (d : Duplex) : Op → Duplex × List (BitVec 64)
  | .observe x => (((d.absorbWord (x 0)).absorbWord (x 1)).absorbWord (x 2), [])
  | .sample =>
    let (d, a) := d.squeezeWord
    let (d, b) := d.squeezeWord
    let (d, c) := d.squeezeWord
    (d, [a, b, c])
  | .nonce n bits => (d.absorbNonce n bits, [])

/-- Operations in order, natively, with the words they sample. -/
def Duplex.run (d : Duplex) : List Op → Duplex × List (BitVec 64)
  | [] => (d, [])
  | op :: ops => let (d, w) := d.step op; let (d, ws) := d.run ops; (d, w ++ ws)

/-! The duplex in rows. -/

/-- A hash row computing `comp cv ws t`: its chaining value, message, counter and finalization columns. -/
structure CompRow (row : ℕ → K) (cv : Fin 4 → BitVec 64) (ws : List (BitVec 64)) (t : BitVec 64) : Prop where
  hashRow : HashRow row
  h : ∀ k : Fin 4, columnWord row (hashH + k) = cv k
  m : ∀ i : Fin 8, columnWord row (hashM + i) = wordAt ws i
  counter : columnWord row hashT = t
  final : (columnWord row hashF).setWidth 32 = finalWord true

theorem comp_row (row : ℕ → K) (cv : Fin 4 → BitVec 64) (ws : List (BitVec 64)) (t : BitVec 64)
    (h : CompRow row cv ws t) : outWords row = comp cv ws t := by
  rw [hash_row_digest row h.hashRow (cvWords cv) (fun k => (h.h k).trans (digest_cvWords cv k).symm) true
    h.final, h.counter, msg_block row ws 0 (fun i => by simpa using h.m i)]
  rfl

/-- `Transcript`: the native bookkeeping, a chaining value that is a row's output, and the words of the last output
block's row. -/
structure RowState where
  d : Duplex
  output : Fin 4 → BitVec 64

/-- `Transcript::flush`: nothing when nothing is pending, else one row compressing the pending block. -/
def FlushRows (s : Duplex) (last : Bool) (rows : List (ℕ → K)) (s' : Duplex) : Prop :=
  (s.pending = [] ∧ rows = [] ∧ s' = s) ∨
    (s.pending ≠ [] ∧ ∃ row, rows = [row] ∧
      CompRow row s.cv s.pending (tweak s.first last (8 * s.pending.length) s.previous) ∧
      s' = { s with cv := outWords row, pending := [], first := last, previous := 0 })

/-- `Transcript::observe` of one word: a full pending block is flushed, not final, before the word joins it. -/
def AbsorbWordRows (s : Duplex) (w : BitVec 64) (rows : List (ℕ → K)) (s' : Duplex) : Prop :=
  let s1 := if s.squeezed ≠ 0 then { s with previous := s.squeezed, squeezed := 0 } else s
  ∃ s2, (if s1.pending.length = 8 then FlushRows s1 false rows s2 else rows = [] ∧ s2 = s1) ∧
    s' = { s2 with pending := s2.pending ++ [w] }

/-- `Transcript::sample` of one word: at an output block's start a row computes the block, and the word is read
from the last block's row. -/
def SqueezeWordRows (r : RowState) (rows : List (ℕ → K)) (r' : RowState) (w : BitVec 64) : Prop :=
  ∃ out : Fin 4 → BitVec 64,
    (if r.d.squeezed % 32 / 8 = 0 then
      ∃ row, rows = [row] ∧ CompRow row r.d.cv [BitVec.ofNat 64 (r.d.squeezed / 32)] outputTag ∧
        out = outWords row
    else rows = [] ∧ out = r.output) ∧
    w = out ⟨r.d.squeezed % 32 / 8, by omega⟩ ∧ r' = ⟨{ r.d with squeezed := r.d.squeezed + 8 }, out⟩

/-- One operation in rows. A nonce's proof of work is checked by rows `pow_rows` is about; here it is bound. -/
def StepRows (r : RowState) : Op → List (ℕ → K) → RowState → List (BitVec 64) → Prop
  | .observe x, rows, r', out => out = [] ∧ r'.output = r.output ∧
    ∃ s1 s2 rows0 rows1 rows2, rows = rows0 ++ rows1 ++ rows2 ∧ AbsorbWordRows r.d (x 0) rows0 s1 ∧
      AbsorbWordRows s1 (x 1) rows1 s2 ∧ AbsorbWordRows s2 (x 2) rows2 r'.d
  | .sample, rows, r', out => ∃ s0 r1 r2 rows0 rows1 rows2 rows3 a b c,
    rows = rows0 ++ rows1 ++ rows2 ++ rows3 ∧ FlushRows r.d true rows0 s0 ∧
      SqueezeWordRows ⟨s0, r.output⟩ rows1 r1 a ∧ SqueezeWordRows r1 rows2 r2 b ∧ SqueezeWordRows r2 rows3 r' c ∧
      out = [a, b, c]
  | .nonce n bits, rows, r', out => out = [] ∧ ∃ s1 rows0 row, rows = rows0 ++ [row] ∧
    FlushRows r.d true rows0 s1 ∧
      CompRow row s1.cv [n 0, n 1, n 2, BitVec.ofNat 64 s1.squeezed, BitVec.ofNat 64 bits] nonceTag ∧
      r' = ⟨{ s1 with cv := outWords row, squeezed := 0 }, r.output⟩

/-- Operations in order, in rows. -/
def RunRows : RowState → List Op → List (ℕ → K) → RowState → List (BitVec 64) → Prop
  | r, [], rows, r', out => rows = [] ∧ r' = r ∧ out = []
  | r, op :: ops, rows, r', out => ∃ r1 rows1 rows2 out1 out2, rows = rows1 ++ rows2 ∧ StepRows r op rows1 r1 out1 ∧
    RunRows r1 ops rows2 r' out2 ∧ out = out1 ++ out2

/-- What the rows keep true: whole words squeezed, the kept output block the current one mid-block, and nothing
pending mid-squeeze. -/
def RowState.Inv (r : RowState) : Prop :=
  r.d.squeezed % 8 = 0 ∧
    (r.d.squeezed % 32 ≠ 0 → r.output = comp r.d.cv [BitVec.ofNat 64 (r.d.squeezed / 32)] outputTag) ∧
    (r.d.pending ≠ [] → r.d.squeezed = 0)

theorem flush_rows (s : Duplex) (last : Bool) (rows : List (ℕ → K)) (s' : Duplex) (h : FlushRows s last rows s') :
    s' = if s.pending = [] then s else
      { s with cv := comp s.cv s.pending (tweak s.first last (8 * s.pending.length) s.previous), pending := [],
               first := last, previous := 0 } := by
  rcases h with ⟨hp, _, rfl⟩ | ⟨hp, row, _, hrow, rfl⟩
  · simp [hp]
  · rw [if_neg hp, comp_row row _ _ _ hrow]

theorem absorbWord_rows (s : Duplex) (w : BitVec 64) (rows : List (ℕ → K)) (s' : Duplex)
    (h : AbsorbWordRows s w rows s') : s' = s.absorbWord w := by
  obtain ⟨s2, hflush, rfl⟩ := h
  simp only [Duplex.absorbWord]
  generalize (if s.squeezed ≠ 0 then { s with previous := s.squeezed, squeezed := 0 } else s) = s1 at hflush ⊢
  by_cases h8 : s1.pending.length = 8
  · rw [if_pos h8] at hflush
    rw [flush_rows _ _ _ _ hflush, if_neg (by intro h; rw [h] at h8; simp at h8), if_pos h8, h8]
  · rw [if_neg h8] at hflush
    rw [hflush.2, if_neg h8]

theorem squeezeWord_rows (r : RowState) (rows : List (ℕ → K)) (r' : RowState) (w : BitVec 64) (hinv : r.Inv)
    (hp : r.d.pending = []) (h : SqueezeWordRows r rows r' w) :
    r.d.squeezeWord = (r'.d, w) ∧ r'.Inv ∧ r'.d.pending = [] := by
  obtain ⟨out, hout, rfl, rfl⟩ := h
  have hfa : r.d.finishAbsorb = r.d := by simp [Duplex.finishAbsorb, hp]
  have hout' : out = comp r.d.cv [BitVec.ofNat 64 (r.d.squeezed / 32)] outputTag := by
    by_cases h0 : r.d.squeezed % 32 / 8 = 0
    · rw [if_pos h0] at hout
      obtain ⟨row, _, hrow, rfl⟩ := hout
      exact comp_row _ _ _ _ hrow
    · rw [if_neg h0] at hout
      rw [hout.2]
      exact hinv.2.1 (by omega)
  refine ⟨by simp only [Duplex.squeezeWord, hfa, hout'], ⟨?_, fun h => ?_, fun h => absurd hp h⟩, hp⟩
  · have := hinv.1
    simp only
    omega
  · simp only at h ⊢
    rw [hout', show (r.d.squeezed + 8) / 32 = r.d.squeezed / 32 by have := hinv.1; omega]

theorem absorbWord_squeezed (d : Duplex) (w : BitVec 64) : (d.absorbWord w).squeezed = 0 := by
  simp only [Duplex.absorbWord]
  split_ifs <;> simp_all

theorem finishAbsorb_pending (d : Duplex) : d.finishAbsorb.pending = [] := by
  simp only [Duplex.finishAbsorb]
  split_ifs <;> simp_all

theorem finishAbsorb_squeezed (d : Duplex) : d.finishAbsorb.squeezed = d.squeezed := by
  simp only [Duplex.finishAbsorb]
  split_ifs <;> rfl

theorem finishAbsorb_finishAbsorb (d : Duplex) : d.finishAbsorb.finishAbsorb = d.finishAbsorb := by
  conv_lhs => rw [Duplex.finishAbsorb, if_pos (finishAbsorb_pending d)]

theorem squeezeWord_finishAbsorb (d : Duplex) : d.finishAbsorb.squeezeWord = d.squeezeWord := by
  simp only [Duplex.squeezeWord, finishAbsorb_finishAbsorb]

/-- After a final flush the rows' state still keeps its invariant, with nothing pending. -/
theorem flush_inv (r : RowState) (rows : List (ℕ → K)) (s0 : Duplex) (hinv : r.Inv)
    (h : FlushRows r.d true rows s0) : s0 = r.d.finishAbsorb ∧ RowState.Inv ⟨s0, r.output⟩ := by
  have hs0 : s0 = r.d.finishAbsorb := flush_rows _ _ _ _ h
  refine ⟨hs0, ?_⟩
  by_cases hp : r.d.pending = []
  · have : r.d.finishAbsorb = r.d := by simp [Duplex.finishAbsorb, hp]
    rw [hs0, this]
    exact hinv
  · have hsq := hinv.2.2 hp
    have : r.d.finishAbsorb.squeezed = 0 := by simp [Duplex.finishAbsorb, hp, hsq]
    refine ⟨?_, fun h => absurd (by rw [hs0, this]) h, fun h => ?_⟩
    · rw [hs0, this]
    · exact absurd (by rw [hs0]; exact finishAbsorb_pending _) h

/-- One operation in rows is the native one, sampling the same words. -/
theorem step_rows (r : RowState) (op : Op) (rows : List (ℕ → K)) (r' : RowState) (out : List (BitVec 64))
    (hinv : r.Inv) (h : StepRows r op rows r' out) : r.d.step op = (r'.d, out) ∧ r'.Inv := by
  cases op with
  | observe x =>
    obtain ⟨rfl, _, s1, s2, _, _, _, _, h0, h1, h2⟩ := h
    rw [absorbWord_rows _ _ _ _ h0] at h1
    rw [absorbWord_rows _ _ _ _ h1] at h2
    have hd := absorbWord_rows _ _ _ _ h2
    have hz : r'.d.squeezed = 0 := by rw [hd]; exact absorbWord_squeezed _ _
    refine ⟨by rw [hd]; rfl, by rw [hz], fun h => absurd (by rw [hz]) h, fun _ => hz⟩
  | sample =>
    obtain ⟨s0, r1, r2, _, _, _, _, a, b, c, _, hf, h1, h2, h3, rfl⟩ := h
    obtain ⟨rfl, hinv0⟩ := flush_inv r _ s0 hinv hf
    obtain ⟨e1, hinv1, hp1⟩ := squeezeWord_rows _ _ _ _ hinv0 (finishAbsorb_pending _) h1
    obtain ⟨e2, hinv2, hp2⟩ := squeezeWord_rows _ _ _ _ hinv1 hp1 h2
    obtain ⟨e3, hinv3, _⟩ := squeezeWord_rows _ _ _ _ hinv2 hp2 h3
    simp only [squeezeWord_finishAbsorb] at e1
    refine ⟨?_, hinv3⟩
    simp only [Duplex.step, e1, e2, e3]
  | nonce n bits =>
    obtain ⟨rfl, s1, _, row, _, hf, hrow, rfl⟩ := h
    obtain ⟨rfl, _⟩ := flush_inv r _ s1 hinv hf
    refine ⟨?_, ?_, fun h => absurd rfl h, fun h => rfl⟩
    · simp only [Duplex.step, Duplex.absorbNonce, comp_row _ _ _ _ hrow]
    · simp only

/-- The rows replay the native duplex: the same state, every sampled word the native challenge's. -/
theorem run_rows (r : RowState) (ops : List Op) (rows : List (ℕ → K)) (r' : RowState) (out : List (BitVec 64))
    (hinv : r.Inv) (h : RunRows r ops rows r' out) : r.d.run ops = (r'.d, out) ∧ r'.Inv := by
  induction ops generalizing r rows out with
  | nil =>
    obtain ⟨_, rfl, rfl⟩ := h
    exact ⟨rfl, hinv⟩
  | cons op ops ih =>
    obtain ⟨r1, _, rows2, out1, out2, _, hs, hrun, rfl⟩ := h
    obtain ⟨e1, hinv1⟩ := step_rows r op _ r1 out1 hinv hs
    obtain ⟨e2, hinv2⟩ := ih r1 rows2 out2 hinv1 hrun
    refine ⟨?_, hinv2⟩
    simp only [Duplex.run, e1, e2]

/-- `Transcript::new`: the seed row outputs the native duplex's first chaining value. -/
theorem seed_row (row : ℕ → K) (domain statement : Fin 4 → BitVec 64)
    (h : CompRow row (digest paramIV) (List.ofFn domain ++ List.ofFn statement) seedTag) :
    outWords row = (Duplex.new domain statement).cv :=
  comp_row _ _ _ _ h

/-- A transcript starts with its invariant. -/
theorem new_inv (domain statement : Fin 4 → BitVec 64) (output : Fin 4 → BitVec 64) :
    RowState.Inv ⟨Duplex.new domain statement, output⟩ := by
  refine ⟨rfl, fun h => absurd rfl h, fun h => absurd rfl h⟩

/-- `Transcript::commitment`: the pending block's final compression if any, then the commitment row. -/
def CommitRows (r : RowState) (rows : List (ℕ → K)) (c : Fin 4 → BitVec 64) : Prop :=
  ∃ s1 rows0 row, rows = rows0 ++ [row] ∧ FlushRows r.d true rows0 s1 ∧
    CompRow row s1.cv [BitVec.ofNat 64 r.d.squeezed] commitTag ∧ c = outWords row

theorem commit_rows (r : RowState) (rows : List (ℕ → K)) (c : Fin 4 → BitVec 64) (h : CommitRows r rows c) :
    c = r.d.commitment := by
  obtain ⟨s1, _, row, _, hf, hrow, rfl⟩ := h
  rw [comp_row _ _ _ _ hrow, flush_rows _ _ _ _ hf]
  rfl

/-! Proof of work. -/

/-- `fiat_shamir::POW_TAG`. -/
def powTag : BitVec 64 := 0x31574f502d534646

/-- `Duplex::pow_base`. -/
def Duplex.powBase (d : Duplex) (bits : ℕ) : Fin 4 → BitVec 64 :=
  comp d.finishAbsorb.cv [BitVec.ofNat 64 d.squeezed, BitVec.ofNat 64 bits] powBaseTag

/-- `Duplex::verify_pow_field`'s check: the zero nonce at no difficulty, else the low `bits` bits of BLAKE2s-256's
first word of the base and nonce zero. -/
def powOk (base : Fin 4 → BitVec 64) (n : Fin 3 → BitVec 64) (bits : ℕ) : Prop :=
  if bits = 0 then n = 0 else
    (digest (hash64 (block [base 0, base 1, base 2, base 3, n 0, n 1, n 2, powTag] 0)) 0).toNat % 2 ^ bits = 0

theorem cvWords_digest (h : Vector (BitVec 32) 8) : cvWords (digest h) = h := by
  apply Vector.ext
  intro r hr
  simp only [cvWords, Vector.getElem_ofFn]
  rw [half_digest h ⟨r / 2, by omega⟩ (r % 2) (Nat.mod_lt _ (by norm_num))]
  congr 1
  simp only
  omega

/-- A `SPLIT` row whose bits below `bits` are held to zero makes its word a multiple of `2 ^ bits`. -/
theorem low_bits_row (row : ℕ → K) (hid : ∀ id ∈ splitIdentities, id.eval row = 0) (bits : ℕ) (hb : bits ≤ 64)
    (hzero : ∀ i < bits, row (1 + i) = 0) : toWord (row 0) % 2 ^ bits = 0 := by
  obtain ⟨_, hword⟩ := split_spec row hid
  rw [hword]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow, Nat.zero_testBit]
  by_cases hi : i < bits
  · rw [testBit_num _ _ _ (by omega), bitsOf, hzero i hi]
    simp
  · simp [hi]

/-- `Transcript::grind_check`'s check in rows: the nonce held to zero at no difficulty; else, after the final flush,
the base row, the one-block hash row of the base, nonce and tag, and a `SPLIT` row of its first output word whose
low `bits` bits are held to zero. -/
def PowRows (r : RowState) (n : Fin 3 → BitVec 64) (bits : ℕ) : Prop :=
  if bits = 0 then n = 0 else
    ∃ s1 rows0 baseRow powRow splitRow, FlushRows r.d true rows0 s1 ∧
      CompRow baseRow s1.cv [BitVec.ofNat 64 s1.squeezed, BitVec.ofNat 64 bits] powBaseTag ∧
      CompRow powRow (digest paramIV)
        [outWords baseRow 0, outWords baseRow 1, outWords baseRow 2, outWords baseRow 3, n 0, n 1, n 2, powTag]
        64 ∧
      (∀ id ∈ splitIdentities, id.eval splitRow = 0) ∧ splitRow 0 = powRow (hashO + 0) ∧
      ∀ i < bits, splitRow (1 + i) = 0

/-- The rows' proof-of-work check is the native one. -/
theorem pow_rows (r : RowState) (n : Fin 3 → BitVec 64) (bits : ℕ) (hb : bits ≤ 64) (h : PowRows r n bits) :
    powOk (r.d.powBase bits) n bits := by
  unfold PowRows at h
  unfold powOk
  split_ifs at h ⊢ with h0
  · exact h
  · obtain ⟨s1, _, baseRow, powRow, splitRow, hf, hbase, hpow, hid, hsplit, hzero⟩ := h
    have hs1 : s1 = r.d.finishAbsorb := flush_rows _ _ _ _ hf
    have hb' : outWords baseRow = r.d.powBase bits := by
      rw [comp_row _ _ _ _ hbase, hs1, finishAbsorb_squeezed, Duplex.powBase]
    have hp := comp_row _ _ _ _ hpow
    rw [comp, cvWords_digest, hb'] at hp
    have hw := congrFun hp 0
    simp only [outWords, words4] at hw
    have e : powRow (hashO + ((0 : Fin 4) : ℕ)) = splitRow 0 := hsplit.symm
    have hlt : toWord (splitRow 0) < 2 ^ 64 := num_lt _ 64
    rw [hash64, ← hw, e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    exact low_bits_row splitRow hid bits hb hzero

/-! The squeeze cursor's bound and the tweak's fields. -/

/-- `fiat_shamir::MAX_SQUEEZE_BYTES`: a squeeze run's length fits the tweak's 49-bit cursor field. -/
def maxSqueeze : ℕ := 2 ^ 49 - 1

/-- Operations each within the cursor bound `Duplex::squeeze` and `Transcript::sample` assert: a sample only when
its 24 bytes keep the run within `maxSqueeze`. -/
def Duplex.Bounded (d : Duplex) : List Op → Prop
  | [] => True
  | op :: ops => (op = .sample → d.squeezed + 24 ≤ maxSqueeze) ∧ (d.step op).1.Bounded ops

/-- A state whose cursors fit their field. -/
def Duplex.Fits (d : Duplex) : Prop := d.squeezed ≤ maxSqueeze ∧ d.previous ≤ maxSqueeze

theorem finishAbsorb_fits (d : Duplex) (h : d.Fits) : d.finishAbsorb.Fits := by
  unfold Duplex.finishAbsorb; split
  · exact h
  · exact ⟨h.1, by simp [maxSqueeze]⟩

theorem absorbWord_previous (d : Duplex) (w : BitVec 64) :
    (d.absorbWord w).previous = 0 ∨ (d.absorbWord w).previous = d.squeezed ∨
      (d.absorbWord w).previous = d.previous := by
  simp only [Duplex.absorbWord]
  split_ifs <;> simp

theorem absorbWord_fits (d : Duplex) (w : BitVec 64) (h : d.Fits) : (d.absorbWord w).Fits := by
  refine ⟨by rw [absorbWord_squeezed]; exact Nat.zero_le _, ?_⟩
  rcases absorbWord_previous d w with h' | h' | h' <;> rw [h']
  · exact Nat.zero_le _
  · exact h.1
  · exact h.2

theorem squeezeWord_fits (e : Duplex) (h : e.Fits) (hb : e.squeezed + 8 ≤ maxSqueeze) :
    (e.squeezeWord).1.Fits ∧ (e.squeezeWord).1.squeezed = e.squeezed + 8 := by
  have hs : (e.squeezeWord).1 = { e.finishAbsorb with squeezed := e.finishAbsorb.squeezed + 8 } := rfl
  rw [hs, finishAbsorb_squeezed]
  exact ⟨⟨hb, (finishAbsorb_fits e h).2⟩, rfl⟩

theorem step_fits (d : Duplex) (op : Op) (h : d.Fits) (hb : op = .sample → d.squeezed + 24 ≤ maxSqueeze) :
    (d.step op).1.Fits := by
  cases op with
  | observe x => exact absorbWord_fits _ _ (absorbWord_fits _ _ (absorbWord_fits _ _ h))
  | sample =>
    have hb := hb rfl
    obtain ⟨h1, e1⟩ := squeezeWord_fits d h (by omega)
    obtain ⟨h2, e2⟩ := squeezeWord_fits _ h1 (by omega)
    obtain ⟨h3, -⟩ := squeezeWord_fits _ h2 (by omega)
    exact h3
  | nonce n bits => exact ⟨by simp [Duplex.step, Duplex.absorbNonce], (finishAbsorb_fits d h).2⟩

theorem run_fits (d : Duplex) (ops : List Op) (h : d.Fits) (hb : d.Bounded ops) : (d.run ops).1.Fits := by
  induction ops generalizing d with
  | nil => exact h
  | cons op ops ih =>
    obtain ⟨h1, h2⟩ := hb
    exact ih _ (step_fits d op h h1) h2

/-- Within the bounds, a tweak names its role, its block's length and its cursor: absorption nodes of different
positions or lengths, and the seed, output, commitment, base and nonce nodes, never share a counter word. -/
theorem tweak_injective (f l f' l' : Bool) (len len' p p' : ℕ) (hl : len ≤ 64) (hl' : len' ≤ 64)
    (hp : p ≤ maxSqueeze) (hp' : p' ≤ maxSqueeze) (h : tweak f l len p = tweak f' l' len' p') :
    f = f' ∧ l = l' ∧ len = len' ∧ p = p' := by
  unfold maxSqueeze at hp hp'
  unfold tweak at h
  have h2 := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat] at h2
  cases f <;> cases l <;> cases f' <;> cases l' <;> simp only at h2 <;>
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h2 <;>
    first | omega | exact ⟨rfl, rfl, by omega, by omega⟩

/-- Every role tag differs from every absorption tweak within the bounds. -/
theorem tag_ne_tweak (f l : Bool) (len p : ℕ) (hl : len ≤ 64) (hp : p ≤ maxSqueeze) :
    tweak f l len p ∉ [seedTag, outputTag, commitTag, powBaseTag, nonceTag] := by
  unfold maxSqueeze at hp
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
  unfold tweak seedTag outputTag commitTag powBaseTag nonceTag
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;> have h2 := congrArg BitVec.toNat h <;>
    simp only [BitVec.toNat_ofNat] at h2 <;> cases f <;> cases l <;> simp only at h2 <;>
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h2 <;> omega

end LeanVMCircuits.Rec
