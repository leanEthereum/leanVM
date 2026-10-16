module

public import LeanVMCircuits.Rec.Statement
public import LeanVMCircuits.Rec.Rows

@[expose] public section

/-!
The Fiat-Shamir duplex, natively and in rows.

`Duplex` is `fiat_shamir::Blake2sDuplex` on 64-bit words: every call the recursion verifier makes absorbs or squeezes
whole little-endian words (the instance's words, a scalar's three limbs, a root's four words, a nonce), so its byte
buffers hold whole words and its byte counts are multiples of eight. Every compression is RFC 7693's `F` at the
node's counter (`Role::counter`) as counter, final, of a chaining value and a zero-padded block. `RowState` and the
`...Rows` relations are `rec::transcript::Transcript`: the same bookkeeping, each compression a hash row whose output
is the next chaining value, each squeezed word read from the output block of the row that computed it. `run_rows`
proves the rows sample the native duplex's challenges, `pow_rows` that their proof-of-work check is
`ProofOfWork::verify` on the native challenge.
-/

namespace LeanVMCircuits.Rec

open LeanVMCircuits.Blake2s Rfc7693

attribute [local irreducible] program

/-- `Role::Seed.counter(0, 0)` and `Role::Output.counter(0, 0)`: the role in the counter word's top byte. -/
def seedTag : BitVec 64 := BitVec.ofNat 64 (1 * 2 ^ 56)
def outputTag : BitVec 64 := BitVec.ofNat 64 (6 * 2 ^ 56)

/-- `Role::absorb(first, last).counter(len, previous)`: the role, the block's length in bytes, and the previous
squeeze run's length. -/
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

theorem cvWords_digest (h : Vector (BitVec 32) 8) : cvWords (digest h) = h := by
  apply Vector.ext
  intro r hr
  simp only [cvWords, Vector.getElem_ofFn]
  rw [half_digest h ⟨r / 2, by omega⟩ (r % 2) (Nat.mod_lt _ (by norm_num))]
  congr 1
  simp only
  omega

/-- `fiat_shamir`'s `node`: RFC 7693's `F` of the chaining value and the zero-padded block of `ws`, at counter `t`,
final. -/
def comp (cv : Fin 4 → BitVec 64) (ws : List (BitVec 64)) (t : BitVec 64) : Fin 4 → BitVec 64 :=
  digest (F (cvWords cv) (block ws 0) t true)

/-! The native duplex. -/

/-- `Blake2sDuplex`: chaining value, pending words, whether the pending block is a run's first, the previous squeeze
run's length and this one's, in bytes. -/
structure Duplex where
  cv : Fin 4 → BitVec 64
  pending : List (BitVec 64)
  first : Bool
  previous : ℕ
  squeezed : ℕ

/-- `Blake2sDuplex::init` of a session id's four words: the seed node of the id, zero-padded to a block. -/
def Duplex.init (sid : Fin 4 → BitVec 64) : Duplex :=
  ⟨comp (digest paramIV) (List.ofFn sid) seedTag, [], true, 0, 0⟩

/-- `Blake2sDuplex::absorb` of one word. -/
def Duplex.absorbWord (d : Duplex) (w : BitVec 64) : Duplex :=
  let d := if d.squeezed ≠ 0 then { d with previous := d.squeezed, squeezed := 0 } else d
  let d := if d.pending.length = 8 then
      { d with cv := comp d.cv d.pending (tweak d.first false 64 d.previous), first := false, previous := 0,
               pending := [] }
    else d
  { d with pending := d.pending ++ [w] }

/-- `Blake2sDuplex::absorb` of whole words. -/
def Duplex.absorb (d : Duplex) (ws : List (BitVec 64)) : Duplex := ws.foldl Duplex.absorbWord d

/-- `compress_pending(true)` when a block is pending: the absorb run's last block. -/
def Duplex.finishAbsorb (d : Duplex) : Duplex :=
  if d.pending = [] then d else
    { d with cv := comp d.cv d.pending (tweak d.first true (8 * d.pending.length) d.previous), pending := [],
             first := true, previous := 0 }

/-- `Blake2sDuplex::squeeze` of one word: word `squeezed % 32 / 8` of output block `squeezed / 32`. -/
def Duplex.squeezeWord (d : Duplex) : Duplex × BitVec 64 :=
  let d := d.finishAbsorb
  ({ d with squeezed := d.squeezed + 8 },
    comp d.cv [BitVec.ofNat 64 (d.squeezed / 32)] outputTag ⟨d.squeezed % 32 / 8, by omega⟩)

/-- `Blake2sDuplex::squeeze` of `n` words: nothing at all for none. -/
def Duplex.squeeze (d : Duplex) : ℕ → Duplex × List (BitVec 64)
  | 0 => (d, [])
  | n + 1 => let (d, w) := d.squeezeWord; let (d, ws) := d.squeeze n; (d, w :: ws)

/-- What the recursion verifier does with a transcript: absorb words (the instance's, a public or prover message's
three, a root's four), squeeze words (a verifier message's three, a digest's four), check proof of work. -/
inductive Op where
  | absorb (ws : List (BitVec 64))
  | squeeze (n : ℕ)
  | pow (nonce : BitVec 64) (bits : ℕ)

/-- One operation, natively, with the words it squeezes. `check_pow` at no difficulty is no step at all; else it
squeezes the four-word challenge, then absorbs the nonce. -/
def Duplex.step (d : Duplex) : Op → Duplex × List (BitVec 64)
  | .absorb ws => (d.absorb ws, [])
  | .squeeze n => d.squeeze n
  | .pow nonce bits => if bits = 0 then (d, []) else
    let (d, c) := d.squeeze 4
    (d.absorbWord nonce, c)

/-- Operations in order, natively, with the words they squeeze. -/
def Duplex.run (d : Duplex) : List Op → Duplex × List (BitVec 64)
  | [] => (d, [])
  | op :: ops => let (d, w) := d.step op; let (d, ws) := d.run ops; (d, w ++ ws)

/-! Proof of work, natively. -/

/-- `ProofOfWork::TRIAL_TAG`, the bytes `FS-POW-1`. -/
def trialTag : BitVec 64 := 0x312d574f502d5346

/-- `ProofOfWork::verify`: BLAKE2s-256 of the one block of the challenge's words, the nonce, two zero words and the
trial tag has a first little-endian word whose top `bits` bits are zero. -/
def powOk (challenge : List (BitVec 64)) (nonce : BitVec 64) (bits : ℕ) : Prop :=
  (digest (hash64 (block (challenge ++ [nonce, 0, 0, trialTag]) 0)) 0).toNat < 2 ^ (64 - bits)

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

/-- `Transcript::compress_pending` when a block is pending, else nothing: one row compressing the pending block. -/
def FlushRows (s : Duplex) (last : Bool) (rows : List (ℕ → K)) (s' : Duplex) : Prop :=
  (s.pending = [] ∧ rows = [] ∧ s' = s) ∨
    (s.pending ≠ [] ∧ ∃ row, rows = [row] ∧
      CompRow row s.cv s.pending (tweak s.first last (8 * s.pending.length) s.previous) ∧
      s' = { s with cv := outWords row, pending := [], first := last, previous := 0 })

/-- `Transcript::absorb_word`: a full pending block is compressed, not last, before the word joins it. -/
def AbsorbWordRows (s : Duplex) (w : BitVec 64) (rows : List (ℕ → K)) (s' : Duplex) : Prop :=
  let s1 := if s.squeezed ≠ 0 then { s with previous := s.squeezed, squeezed := 0 } else s
  ∃ s2, (if s1.pending.length = 8 then FlushRows s1 false rows s2 else rows = [] ∧ s2 = s1) ∧
    s' = { s2 with pending := s2.pending ++ [w] }

/-- Words absorbed in order, in rows. -/
def AbsorbRows : Duplex → List (BitVec 64) → List (ℕ → K) → Duplex → Prop
  | s, [], rows, s' => rows = [] ∧ s' = s
  | s, w :: ws, rows, s' => ∃ s1 rows0 rows1, rows = rows0 ++ rows1 ∧ AbsorbWordRows s w rows0 s1 ∧
    AbsorbRows s1 ws rows1 s'

/-- `Transcript::squeeze_word`: the pending block compressed as its run's last, then at an output block's start a
row computes the block, and the word is read from the last block's row. -/
def SqueezeWordRows (r : RowState) (rows : List (ℕ → K)) (r' : RowState) (w : BitVec 64) : Prop :=
  ∃ s0 rows0 rows1, ∃ out : Fin 4 → BitVec 64, rows = rows0 ++ rows1 ∧ FlushRows r.d true rows0 s0 ∧
    (if s0.squeezed % 32 / 8 = 0 then
      ∃ row, rows1 = [row] ∧ CompRow row s0.cv [BitVec.ofNat 64 (s0.squeezed / 32)] outputTag ∧
        out = outWords row
    else rows1 = [] ∧ out = r.output) ∧
    w = out ⟨s0.squeezed % 32 / 8, by omega⟩ ∧ r' = ⟨{ s0 with squeezed := s0.squeezed + 8 }, out⟩

/-- Words squeezed in order, in rows. -/
def SqueezeRows : RowState → ℕ → List (ℕ → K) → RowState → List (BitVec 64) → Prop
  | r, 0, rows, r', out => rows = [] ∧ r' = r ∧ out = []
  | r, n + 1, rows, r', out => ∃ r1 rows0 rows1 w ws, rows = rows0 ++ rows1 ∧ SqueezeWordRows r rows0 r1 w ∧
    SqueezeRows r1 n rows1 r' ws ∧ out = w :: ws

/-- `check_pow`'s trial in rows: the one-block hash row of the challenge, the nonce, two zero words and the trial
tag, and a `SPLIT` row of its first output word whose top `bits` bits are held to zero. -/
def TrialRows (challenge : List (BitVec 64)) (nonce : BitVec 64) (bits : ℕ) (powRow splitRow : ℕ → K) : Prop :=
  CompRow powRow (digest paramIV) (challenge ++ [nonce, 0, 0, trialTag]) 64 ∧
    (∀ id ∈ splitIdentities, id.eval splitRow = 0) ∧ splitRow 0 = powRow (hashO + 0) ∧
    ∀ i, 64 - bits ≤ i → i < 64 → splitRow (1 + i) = 0

/-- One operation in rows. `check_pow` at no difficulty takes no row; else the challenge's squeezes, the nonce's
absorption, then the trial's rows. -/
def StepRows (r : RowState) : Op → List (ℕ → K) → RowState → List (BitVec 64) → Prop
  | .absorb ws, rows, r', out => out = [] ∧ r'.output = r.output ∧ AbsorbRows r.d ws rows r'.d
  | .squeeze n, rows, r', out => SqueezeRows r n rows r' out
  | .pow nonce bits, rows, r', out => if bits = 0 then rows = [] ∧ r' = r ∧ out = [] else
    ∃ r1 rows0 rows1 powRow splitRow, rows = rows0 ++ rows1 ++ [powRow, splitRow] ∧ SqueezeRows r 4 rows0 r1 out ∧
      AbsorbWordRows r1.d nonce rows1 r'.d ∧ r'.output = r1.output ∧ TrialRows out nonce bits powRow splitRow

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

theorem absorb_rows (s : Duplex) (ws : List (BitVec 64)) (rows : List (ℕ → K)) (s' : Duplex)
    (h : AbsorbRows s ws rows s') : s' = s.absorb ws := by
  induction ws generalizing s rows with
  | nil => exact h.2
  | cons w ws ih =>
    obtain ⟨s1, _, rows1, _, h0, h1⟩ := h
    rw [ih s1 rows1 h1, absorbWord_rows _ _ _ _ h0]
    rfl

theorem absorbWord_squeezed (d : Duplex) (w : BitVec 64) : (d.absorbWord w).squeezed = 0 := by
  simp only [Duplex.absorbWord]
  split_ifs <;> simp_all

theorem finishAbsorb_pending (d : Duplex) : d.finishAbsorb.pending = [] := by
  simp only [Duplex.finishAbsorb]
  split_ifs <;> simp_all

theorem finishAbsorb_squeezed (d : Duplex) : d.finishAbsorb.squeezed = d.squeezed := by
  simp only [Duplex.finishAbsorb]
  split_ifs <;> rfl

/-- A final flush keeps the rows' invariant, with nothing pending. -/
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

theorem squeezeWord_rows (r : RowState) (rows : List (ℕ → K)) (r' : RowState) (w : BitVec 64) (hinv : r.Inv)
    (h : SqueezeWordRows r rows r' w) : r.d.squeezeWord = (r'.d, w) ∧ r'.Inv := by
  obtain ⟨s0, _, _, out, _, hf, hout, rfl, rfl⟩ := h
  obtain ⟨rfl, hinv0⟩ := flush_inv r _ s0 hinv hf
  have hout' : out = comp r.d.finishAbsorb.cv [BitVec.ofNat 64 (r.d.finishAbsorb.squeezed / 32)] outputTag := by
    by_cases h0 : r.d.finishAbsorb.squeezed % 32 / 8 = 0
    · rw [if_pos h0] at hout
      obtain ⟨row, _, hrow, rfl⟩ := hout
      exact comp_row _ _ _ _ hrow
    · rw [if_neg h0] at hout
      rw [hout.2]
      exact hinv0.2.1 (by have := hinv0.1; simp only at this ⊢; omega)
  refine ⟨by simp only [Duplex.squeezeWord, hout'], ⟨?_, fun h => ?_, fun h => absurd (finishAbsorb_pending _) h⟩⟩
  · have := hinv0.1
    simp only at this ⊢
    omega
  · simp only at h ⊢
    rw [hout', show (r.d.finishAbsorb.squeezed + 8) / 32 = r.d.finishAbsorb.squeezed / 32 by
      have := hinv0.1; simp only at this; omega]

theorem squeeze_rows (r : RowState) (n : ℕ) (rows : List (ℕ → K)) (r' : RowState) (out : List (BitVec 64))
    (hinv : r.Inv) (h : SqueezeRows r n rows r' out) : r.d.squeeze n = (r'.d, out) ∧ r'.Inv := by
  induction n generalizing r rows out with
  | zero =>
    obtain ⟨_, rfl, rfl⟩ := h
    exact ⟨rfl, hinv⟩
  | succ n ih =>
    obtain ⟨r1, _, rows1, w, ws, _, h1, h2, rfl⟩ := h
    obtain ⟨e1, hinv1⟩ := squeezeWord_rows _ _ _ _ hinv h1
    obtain ⟨e2, hinv2⟩ := ih r1 rows1 ws hinv1 h2
    exact ⟨by simp only [Duplex.squeeze, e1, e2], hinv2⟩

/-- An absorbed word leaves no squeeze run open, so the invariant holds whatever output block is kept. -/
theorem absorbWord_inv (d : Duplex) (w : BitVec 64) (output : Fin 4 → BitVec 64) :
    RowState.Inv ⟨d.absorbWord w, output⟩ := by
  have hz := absorbWord_squeezed d w
  exact ⟨by simp only [hz], fun h => absurd (by simp only [hz]) h, fun _ => hz⟩

theorem absorb_inv (r : RowState) (ws : List (BitVec 64)) (hinv : r.Inv) : RowState.Inv ⟨r.d.absorb ws, r.output⟩ := by
  induction ws generalizing r with
  | nil => exact hinv
  | cons w ws ih => exact ih ⟨r.d.absorbWord w, r.output⟩ (absorbWord_inv _ _ _)

/-- One operation in rows is the native one, squeezing the same words. -/
theorem step_rows (r : RowState) (op : Op) (rows : List (ℕ → K)) (r' : RowState) (out : List (BitVec 64))
    (hinv : r.Inv) (h : StepRows r op rows r' out) : r.d.step op = (r'.d, out) ∧ r'.Inv := by
  cases op with
  | absorb ws =>
    obtain ⟨rfl, ho, ha⟩ := h
    have hd := absorb_rows _ _ _ _ ha
    refine ⟨by rw [hd]; rfl, ?_⟩
    have := absorb_inv r ws hinv
    rw [← hd, ← ho] at this
    exact this
  | squeeze n => exact squeeze_rows r n rows r' out hinv h
  | pow nonce bits =>
    by_cases h0 : bits = 0
    · simp only [StepRows, h0, ↓reduceIte] at h
      obtain ⟨_, rfl, rfl⟩ := h
      exact ⟨by simp [Duplex.step, h0], hinv⟩
    · simp only [StepRows, h0, ↓reduceIte] at h
      obtain ⟨r1, _, _, _, _, _, hs, ha, ho, _⟩ := h
      obtain ⟨e1, -⟩ := squeeze_rows r 4 _ r1 out hinv hs
      have hd := absorbWord_rows _ _ _ _ ha
      refine ⟨by simp only [Duplex.step, if_neg h0, e1, hd], ?_⟩
      have := absorbWord_inv r1.d nonce r1.output
      rw [← hd, ← ho] at this
      exact this

/-- The rows replay the native duplex: the same state, every squeezed word the native challenge's. -/
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

theorem wordAt_append_zeros (ws : List (BitVec 64)) (k n : ℕ) :
    wordAt (ws ++ List.replicate k 0) n = wordAt ws n := by
  unfold wordAt
  by_cases h : n < ws.length
  · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
      List.getElem?_eq_none (l := ws) (by omega), List.getElem?_replicate]
    split_ifs <;> rfl

/-- `Transcript::new`: the constant seed chaining value, the seed node of the session id's words then four zero
words, is the native duplex's first. -/
theorem seed_row (sid : Fin 4 → BitVec 64) :
    comp (digest paramIV) [sid 0, sid 1, sid 2, sid 3, 0, 0, 0, 0] seedTag = (Duplex.init sid).cv := by
  have e : [sid 0, sid 1, sid 2, sid 3, 0, 0, 0, 0] = List.ofFn sid ++ List.replicate 4 0 := by
    simp [List.ofFn_succ]
  simp only [Duplex.init, comp, block, e, wordAt_append_zeros]

/-- A transcript starts with its invariant. -/
theorem new_inv (sid : Fin 4 → BitVec 64) (output : Fin 4 → BitVec 64) :
    RowState.Inv ⟨Duplex.init sid, output⟩ := by
  refine ⟨rfl, fun h => absurd rfl h, fun h => absurd rfl h⟩

/-! Proof of work in rows. -/

/-- The trial's rows are `ProofOfWork::verify` of their challenge and nonce. -/
theorem trial_rows (challenge : List (BitVec 64)) (nonce : BitVec 64) (bits : ℕ) (powRow splitRow : ℕ → K)
    (h : TrialRows challenge nonce bits powRow splitRow) : powOk challenge nonce bits := by
  obtain ⟨hpow, hid, hsplit, hzero⟩ := h
  have hp := comp_row _ _ _ _ hpow
  rw [comp, cvWords_digest] at hp
  have hw := congrFun hp 0
  simp only [outWords, words4] at hw
  have e : powRow (hashO + ((0 : Fin 4) : ℕ)) = splitRow 0 := hsplit.symm
  have hlt : toWord (splitRow 0) < 2 ^ 64 := num_lt _ 64
  unfold powOk
  rw [hash64, ← hw, e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  exact (pack_row splitRow hid (64 - bits) hzero).2.2

/-- `Transcript::check_pow` is `VerifierState::check_pow`'s test: in rows, the nonce is `ProofOfWork::verify`'s work
on the native duplex's challenge. -/
theorem pow_rows (r : RowState) (nonce : BitVec 64) (bits : ℕ) (rows : List (ℕ → K)) (r' : RowState)
    (out : List (BitVec 64)) (hinv : r.Inv) (h : StepRows r (.pow nonce bits) rows r' out) :
    powOk (r.d.step (.pow nonce bits)).2 nonce bits := by
  rw [(step_rows r _ rows r' out hinv h).1]
  by_cases h0 : bits = 0
  · subst h0
    exact (digest (hash64 (block (out ++ [nonce, 0, 0, trialTag]) 0)) 0).isLt
  · simp only [StepRows, h0, ↓reduceIte] at h
    obtain ⟨_, _, _, powRow, splitRow, _, _, _, _, ht⟩ := h
    exact trial_rows out nonce bits powRow splitRow ht

/-! The squeeze cursor's bound and the tweak's fields. -/

/-- `fiat_shamir::MAX_SQUEEZE`: a squeeze run's length fits the counter's 49-bit cursor field. -/
def maxSqueeze : ℕ := 2 ^ 49 - 1

/-- The words an operation squeezes. -/
def Op.squeezes : Op → ℕ
  | .absorb _ => 0
  | .squeeze n => n
  | .pow _ bits => if bits = 0 then 0 else 4

/-- Operations each within the cursor bound `Blake2sDuplex::squeeze` and `Transcript::squeeze_word` assert: a squeeze
only when its words keep the run within `maxSqueeze`. -/
def Duplex.Bounded (d : Duplex) : List Op → Prop
  | [] => True
  | op :: ops => d.squeezed + 8 * op.squeezes ≤ maxSqueeze ∧ (d.step op).1.Bounded ops

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

theorem absorb_fits (d : Duplex) (ws : List (BitVec 64)) (h : d.Fits) : (d.absorb ws).Fits := by
  induction ws generalizing d with
  | nil => exact h
  | cons w ws ih => exact ih _ (absorbWord_fits d w h)

theorem squeezeWord_fits (e : Duplex) (h : e.Fits) (hb : e.squeezed + 8 ≤ maxSqueeze) :
    (e.squeezeWord).1.Fits ∧ (e.squeezeWord).1.squeezed = e.squeezed + 8 := by
  have hs : (e.squeezeWord).1 = { e.finishAbsorb with squeezed := e.finishAbsorb.squeezed + 8 } := rfl
  rw [hs, finishAbsorb_squeezed]
  exact ⟨⟨hb, (finishAbsorb_fits e h).2⟩, rfl⟩

theorem squeeze_fits (e : Duplex) (n : ℕ) (h : e.Fits) (hb : e.squeezed + 8 * n ≤ maxSqueeze) :
    (e.squeeze n).1.Fits := by
  induction n generalizing e with
  | zero => exact h
  | succ n ih =>
    obtain ⟨h1, e1⟩ := squeezeWord_fits e h (by omega)
    have hb1 : e.squeezeWord.1.squeezed + 8 * n ≤ maxSqueeze := by rw [e1]; omega
    exact ih e.squeezeWord.1 h1 hb1

theorem step_fits (d : Duplex) (op : Op) (h : d.Fits) (hb : d.squeezed + 8 * op.squeezes ≤ maxSqueeze) :
    (d.step op).1.Fits := by
  cases op with
  | absorb ws => exact absorb_fits d ws h
  | squeeze n => exact squeeze_fits d n h hb
  | pow nonce bits =>
    by_cases h0 : bits = 0
    · simp only [Duplex.step, if_pos h0]
      exact h
    · simp only [Op.squeezes, if_neg h0] at hb
      simp only [Duplex.step, if_neg h0]
      exact absorbWord_fits _ _ (squeeze_fits d 4 h hb)

theorem run_fits (d : Duplex) (ops : List Op) (h : d.Fits) (hb : d.Bounded ops) : (d.run ops).1.Fits := by
  induction ops generalizing d with
  | nil => exact h
  | cons op ops ih =>
    obtain ⟨h1, h2⟩ := hb
    exact ih _ (step_fits d op h h1) h2

/-- Within the bounds, an absorb counter names its role, its block's length and its cursor: absorption nodes of
different positions or lengths never share a counter word. -/
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

/-- The seed and output counters differ from every absorb counter within the bounds. -/
theorem tag_ne_tweak (f l : Bool) (len p : ℕ) (hl : len ≤ 64) (hp : p ≤ maxSqueeze) :
    tweak f l len p ∉ [seedTag, outputTag] := by
  unfold maxSqueeze at hp
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
  unfold tweak seedTag outputTag
  refine ⟨?_, ?_⟩ <;> intro h <;> have h2 := congrArg BitVec.toNat h <;>
    simp only [BitVec.toNat_ofNat] at h2 <;> cases f <;> cases l <;> simp only at h2 <;>
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h2 <;> omega

end LeanVMCircuits.Rec
