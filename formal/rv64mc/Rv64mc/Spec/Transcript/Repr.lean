/-
  Rv64mc.Spec.Transcript.Repr

  How `transcript.rs`'s `Sponge` and `Transcript` sit in memory, as the Model's `SpongeRust` and `TState` hold them,
  so that a caller can state "the transcript at `a` is the mirror's state `t`" before a call and read the mirror's
  next state after it.

  * `SpongeAt m a r`: the sponge at `a` is `r` (`Layouts.Sponge`): its `25` lanes, the `n_pending` waiting scalars
    (each an `(E, u64)` slot: the `E`'s limbs, then the tag), the count, and the ground challenge (`Option<E>`).
    Slots past `n_pending` are not read, so they are left free.
  * `ProofAt env m q pf`: the `Proof` at `q` is `pf`, its stream a `Vec<E>` of `pf.stream`'s limbs and its openings
    a `Vec<Vec<MerklePath>>` of `MerklePathRust.ofOpening`'s, every object of it allocated before (`Live`), so that
    every call keeps it (`ProofAt.keep`).
  * `TranscriptAt env m a t`: the transcript at `a` is `t` (`Layouts.Transcript`): its sponge, the proof it points
    to, the two offsets and the `checked` byte. The ghost roots of `TState` are in no memory.

  Each has its `keep` lemma, and `TranscriptAt.frameF` keeps a transcript in a caller's frame across a call that
  writes nothing beyond its stack and its allocations.
-/

import Rv64mc.Core.Repr
import Rv64mc.Model.Transcript
import Rv64mc.Tactic.Frame

namespace Rv64mc.Spec.Transcript

open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.KeccakHash

/-! ## Layout the generated layouts do not name -/

/-- The size of a waiting scalar's slot, `(E, u64)`: the four slots fill `pending` up to `n_pending`. -/
abbrev pendingSlot : Nat := (Layouts.Sponge.n_pending - Layouts.Sponge.pending) / 4

/-- The tag's offset in a slot: rustc lays the `E` first, the tag after it. -/
abbrev pendingTag : Nat := Layouts.E.byteSize

/-! ## Values -/

/-- **The `Option<E>` at `a` is `o`**: its tag, and for `Some` the `E`'s limbs. -/
def OptionEAt (m : MachineState) (a : Word) : Option E → Prop
  | none => m.getMem (a + BitVec.ofNat 64 Layouts.OptionE.tagOffset) = BitVec.ofNat 64 Layouts.OptionE.None.tag
  | some e => m.getMem (a + BitVec.ofNat 64 Layouts.OptionE.tagOffset) = BitVec.ofNat 64 Layouts.OptionE.Some.tag ∧
      EAt m (a + BitVec.ofNat 64 Layouts.OptionE.Some.f0) (Model.limbs e)

/-- **The waiting scalars `ps` from `a`**, slot `k` at `a + 24 k`. -/
def PendingAt (m : MachineState) (a : Word) (ps : List (E × BitVec 64)) : Prop :=
  ∀ k (h : k < ps.length), EAt m (a + BitVec.ofNat 64 (pendingSlot * k)) (Model.limbs ps[k].1) ∧
    m.getMem (a + BitVec.ofNat 64 (pendingSlot * k + pendingTag)) = ps[k].2

/-- **The sponge at `a` is `r`**, at a doubleword boundary (`Layouts.Sponge.byteAlign`). A structure, so that
    `rv_auto` keeps it whole. -/
structure SpongeAt (m : MachineState) (a : Word) (r : Model.SpongeRust) : Prop where
  aligned : a.toNat % Layouts.Sponge.byteAlign = 0
  inv : r.Inv
  state : WordsAt m (a + BitVec.ofNat 64 Layouts.Sponge.state) r.state
  pending : PendingAt m (a + BitVec.ofNat 64 Layouts.Sponge.pending) (r.pending.take r.nPending)
  nPending : m.getMem (a + BitVec.ofNat 64 Layouts.Sponge.n_pending) = BitVec.ofNat 64 r.nPending
  ground : OptionEAt m (a + BitVec.ofNat 64 Layouts.Sponge.ground) r.ground

/-- `size`-byte objects laid end to end from `a`, object `k` at `a + size k` satisfying `El`. -/
def ArrayAt {α : Type} (size : Nat) (El : MachineState → Word → α → Prop) (m : MachineState) (a : Word)
    (xs : List α) : Prop :=
  ∀ k (h : k < xs.length), El m (a + BitVec.ofNat 64 (size * k)) xs[k]

/-- **A `Vec<T>` of `size`-byte elements at `a` holds `xs`**, its elements allocated before (`Live`). -/
def LiveVecAt {α : Type} (env : Env) (size : Nat) (Elems : MachineState → Word → List α → Prop)
    (m : MachineState) (a : Word) (xs : List α) : Prop :=
  ∃ ptr cap, VecAt Elems m a ptr cap xs ∧ env.Live m ptr (size * xs.length)

/-- **The `MerklePath` at `a` is the opening `o`'s** (`MerklePathRust.ofOpening`): its leaf's words, its siblings'
    bytes and its position. -/
def PathAt (env : Env) (m : MachineState) (a : Word) (o : Opening) : Prop :=
  LiveVecAt env Layouts.K.byteSize WordsAt m (a + BitVec.ofNat 64 Layouts.MerklePath.leaf)
      (Model.MerklePathRust.ofOpening o).leaf ∧
    LiveVecAt env Layouts.Digest.byteSize (ArrayAt Layouts.Digest.byteSize DigestAt) m
      (a + BitVec.ofNat 64 Layouts.MerklePath.siblings) (Model.MerklePathRust.ofOpening o).siblings ∧
    m.getMem (a + BitVec.ofNat 64 Layouts.MerklePath.leaf_index) = (Model.MerklePathRust.ofOpening o).leafIndex

/-- A phase of openings: a `Vec<MerklePath>`. -/
def PhaseAt (env : Env) (m : MachineState) (a : Word) (phase : List Opening) : Prop :=
  LiveVecAt env Layouts.MerklePath.byteSize (ArrayAt Layouts.MerklePath.byteSize (PathAt env)) m a phase

/-- **The `Proof` at `q` is `pf`**: the struct and everything it points to allocated before. -/
structure ProofAt (env : Env) (m : MachineState) (q : Word) (pf : Proof) : Prop where
  live : env.Live m q Layouts.Proof.byteSize
  stream : LiveVecAt env Layouts.E.byteSize EListAt m (q + BitVec.ofNat 64 Layouts.Proof.stream)
    (pf.stream.map Model.limbs)
  openings : LiveVecAt env Layouts.Vec.byteSize (ArrayAt Layouts.Vec.byteSize (PhaseAt env)) m
    (q + BitVec.ofNat 64 Layouts.Proof.merkle_openings) pf.openings

/-- The `checked` byte of a transcript. -/
def boolByte (b : Bool) : BitVec 8 := if b then 1#8 else 0#8

/-- **The transcript at `a` is `t`**: its sponge, its proof (through the reference at `proof`), the stream and
    opening offsets, within the proof (as `TState.Inv` keeps them), and `checked`. -/
structure TranscriptAt (env : Env) (m : MachineState) (a : Word) (t : Model.TState) : Prop where
  stream_le : t.streamOffset ≤ t.proof.stream.length
  opening_le : t.openingOffset ≤ t.proof.openings.length
  sponge : SpongeAt m (a + BitVec.ofNat 64 Layouts.Transcript.sponge) t.sponge
  proof : ProofAt env m (m.getMem (a + BitVec.ofNat 64 Layouts.Transcript.proof)) t.proof
  streamOffset : m.getMem (a + BitVec.ofNat 64 Layouts.Transcript.stream_offset) = BitVec.ofNat 64 t.streamOffset
  openingOffset :
    m.getMem (a + BitVec.ofNat 64 Layouts.Transcript.opening_offset) = BitVec.ofNat 64 t.openingOffset
  checked : m.getByte (a + BitVec.ofNat 64 Layouts.Transcript.checked) = boolByte t.checked

/-- **An object of `n` bytes at `a` in a caller's frame**: at or above the callee's stack top `top`, without
    wrapping. -/
def InFrame (top a : Word) (n : Nat) : Prop := top.toNat ≤ a.toNat ∧ a.toNat + n < 2 ^ 64

/-- Two footprints `[a, a + n)` and `[b, b + k)` apart. -/
def Apart (a : Word) (n : Nat) (b : Word) (k : Nat) : Prop := a.toNat + n ≤ b.toNat ∨ b.toNat + k ≤ a.toNat

/-- **The `Result<E, VerifierError>` at `a` is the mirror's outcome**: `Ok` with the value's limbs, or an `Err`
    (`none`, whatever error it carries). -/
def ResultEAt (m : MachineState) (a : Word) : Option E → Prop
  | some v => m.getMem (a + BitVec.ofNat 64 Layouts.ResultE.tagOffset) = BitVec.ofNat 64 Layouts.ResultE.Ok.tag ∧
      EAt m (a + BitVec.ofNat 64 Layouts.ResultE.Ok.f0) (Model.limbs v)
  | none => m.getMem (a + BitVec.ofNat 64 Layouts.ResultE.tagOffset) = BitVec.ofNat 64 Layouts.ResultE.Err.tag

/-! ## What a call keeps -/

section Keep

variable {env : Env} {m m' : MachineState}

/-- `m'` has `m`'s words below `NEXT` in `m`, and `NEXT` did not go down: what every call keeps of the heap. -/
def HeapKept (env : Env) (m m' : MachineState) : Prop :=
  (env.next m).toNat ≤ (env.next m').toNat ∧ ∀ b : Word, b.toNat < (env.next m).toNat → m'.getMem b = m.getMem b

theorem HeapKept.of_frame {top : Word} {out : Word → Prop} (hf : env.Frame top out m m')
    (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) (hout : ∀ b, out b → (env.next m).toNat ≤ b.toNat) :
    HeapKept env m m' :=
  ⟨hf.1, fun b hb => hf.getMem_below_next hnx hb fun ho => absurd (hout b ho) (by omega)⟩

theorem HeapKept.keeps (h : HeapKept env m m') {a : Word} {n : Nat} (hl : env.Live m a n) : Keeps m m' a n :=
  fun b hb => h.2 b (by have := hb.2; unfold Env.Live at hl; omega)

theorem HeapKept.live (h : HeapKept env m m') {a : Word} {n : Nat} (hl : env.Live m a n) : env.Live m' a n := by
  have := h.1; unfold Env.Live at *; omega

theorem keepWords (h : HeapKept env m m') {a : Word} {ws : List Word} (hw : WordsAt m a ws)
    (hl : env.Live m a (8 * ws.length)) : WordsAt m' a ws :=
  hw.keep (h.keeps hl)

theorem keepEList (h : HeapKept env m m') {a : Word} {es : List (Word × Word)} (he : EListAt m a es)
    (hl : env.Live m a (Layouts.E.byteSize * es.length)) : EListAt m' a es :=
  he.keep (h.keeps hl)

theorem keepBytes (h : HeapKept env m m') {a : Word} {bs : List (BitVec 8)} (hb : BytesAt m a bs)
    (hl : env.Live m a bs.length) : BytesAt m' a bs := by
  refine hb.keep fun k hk => ?_
  have hk' : (a + BitVec.ofNat 64 k).toNat = a.toNat + k := toNat_add_ofNat (by have := hb.1; omega)
  apply getByte_congr
  apply h.2
  rw [toNat_alignToDword, hk']
  unfold Env.Live at hl
  omega

/-- An array's footprint: object `k` lies within the whole. -/
theorem ArrayAt.live_elem {size k n : Nat} {a : Word} (hl : env.Live m a (size * n)) (hk : k < n) :
    env.Live m (a + BitVec.ofNat 64 (size * k)) size := by
  unfold Env.Live at *
  have : size * k + size ≤ size * n := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hk
  rw [toNat_add_ofNat (by have := (env.next m).isLt; omega)]
  omega

theorem live_sub {a : Word} {n k j : Nat} (hl : env.Live m a n) (hkj : k + j ≤ n) :
    env.Live m (a + BitVec.ofNat 64 k) j := by
  unfold Env.Live at *
  rw [toNat_add_ofNat (by have := (env.next m).isLt; omega)]
  omega

theorem LiveVecAt.keep {α : Type} {size : Nat} {Elems : MachineState → Word → List α → Prop} {a : Word}
    {xs : List α} (h : HeapKept env m m') (hv : LiveVecAt env size Elems m a xs)
    (ha : env.Live m a Layouts.Vec.byteSize)
    (he : ∀ ptr, env.Live m ptr (size * xs.length) → Elems m ptr xs → Elems m' ptr xs) :
    LiveVecAt env size Elems m' a xs := by
  obtain ⟨ptr, cap, hv, hl⟩ := hv
  refine ⟨ptr, cap, hv.keep ?_ (h.keeps ha) (he ptr hl), h.live hl⟩
  have := (env.next m).isLt; unfold Env.Live at ha; omega

theorem keepDigest (h : HeapKept env m m') {a : Word} {d : List (BitVec 8)} (hd : DigestAt m a d)
    (hl : env.Live m a Layouts.Digest.byteSize) : DigestAt m' a d :=
  ⟨hd.1, keepBytes h hd.2 (by rw [hd.1]; exact hl)⟩

theorem PathAt.keep (h : HeapKept env m m') {a : Word} {o : Opening} (hp : PathAt env m a o)
    (hl : env.Live m a Layouts.MerklePath.byteSize) : PathAt env m' a o := by
  obtain ⟨h1, h2, h3⟩ := hp
  refine ⟨h1.keep h (live_sub hl (by decide)) fun ptr hl' hw => keepWords h hw hl', h2.keep h
    (live_sub hl (by decide)) fun ptr hl' hw k hk => keepDigest h (hw k hk) (ArrayAt.live_elem hl' hk), ?_⟩
  rw [h.2 _ (by have := live_sub (k := Layouts.MerklePath.leaf_index) (j := 8) hl (by decide); unfold Env.Live at this; omega)]
  exact h3

theorem PhaseAt.keep (h : HeapKept env m m') {a : Word} {phase : List Opening} (hp : PhaseAt env m a phase)
    (hl : env.Live m a Layouts.Vec.byteSize) : PhaseAt env m' a phase :=
  LiveVecAt.keep h hp hl fun _ hl' hw k hk => (hw k hk).keep h (ArrayAt.live_elem hl' hk)

/-- **Every call keeps a proof**: it lies below `NEXT`. -/
theorem ProofAt.keep (h : HeapKept env m m') {q : Word} {pf : Proof} (hp : ProofAt env m q pf) :
    ProofAt env m' q pf := by
  obtain ⟨hl, h1, h2⟩ := hp
  exact ⟨h.live hl, h1.keep h (live_sub hl (by decide)) fun _ hl' he => keepEList h he hl',
    h2.keep h (live_sub hl (by decide)) fun _ hl' hw k hk => (hw k hk).keep h (ArrayAt.live_elem hl' hk)⟩

/-- The words of a transcript's footprint, as offsets read. -/
theorem keeps_get {a : Word} {n k : Nat} (hk : Keeps m m' a n) (ha : a.toNat + n < 2 ^ 64) (hkn : k + 8 ≤ n) :
    m'.getMem (a + BitVec.ofNat 64 k) = m.getMem (a + BitVec.ofNat 64 k) :=
  hk _ ⟨by rw [toNat_add_ofNat (by omega)]; omega, by rw [toNat_add_ofNat (by omega)]; omega⟩

theorem SpongeAt.keep {a : Word} {r : Model.SpongeRust} (hs : SpongeAt m a r)
    (ha : a.toNat + Layouts.Sponge.byteSize < 2 ^ 64) (hk : Keeps m m' a Layouts.Sponge.byteSize) :
    SpongeAt m' a r := by
  simp only [Layouts.Sponge.byteSize] at ha hk
  have get : ∀ k, k + 8 ≤ 328 → m'.getMem (a + BitVec.ofNat 64 k) = m.getMem (a + BitVec.ofNat 64 k) :=
    fun k hkn => keeps_get hk ha hkn
  have add : ∀ j k, a + BitVec.ofNat 64 j + BitVec.ofNat 64 k = a + BitVec.ofNat 64 (j + k) := fun j k => by
    rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp
  obtain ⟨hal, hi, hst, hp, hn, hg⟩ := hs
  simp only [PendingAt, EAt, pendingSlot, pendingTag, Layouts.Sponge.state, Layouts.Sponge.pending,
    Layouts.Sponge.n_pending, Layouts.Sponge.ground, Layouts.E.c0, Layouts.E.c1, Layouts.E.byteSize] at hst hp hn hg
  refine ⟨hal, hi, ⟨hst.1, fun k hk' => ?_⟩, fun k hk' => ?_, ?_, ?_⟩
  · have := hi.1; simp only [Layouts.Sponge.state]; rw [add, get _ (by omega), ← add]; exact hst.2 k hk'
  · have hk4 : k < 4 := by have := hi.2.2; simp at hk'; omega
    obtain ⟨⟨h0, h1⟩, h2⟩ := hp k hk'
    simp only [EAt, pendingSlot, pendingTag, Layouts.Sponge.pending, Layouts.Sponge.n_pending, Layouts.E.c0,
      Layouts.E.c1, Layouts.E.byteSize]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [add, add, get _ (by omega), ← add, ← add]; exact h0
    · rw [add, add, get _ (by omega), ← add, ← add]; exact h1
    · rw [add, get _ (by omega), ← add]; exact h2
  · simp only [Layouts.Sponge.n_pending]; rw [get _ (by decide)]; exact hn
  · cases hr : r.ground with
    | none =>
      rw [hr] at hg
      simp only [Layouts.Sponge.ground]
      simp only [OptionEAt, Layouts.OptionE.tagOffset, Layouts.OptionE.None.tag, BitVec.add_zero] at hg ⊢
      rw [show a = a + BitVec.ofNat 64 0 by simp, get _ (by decide)]; simpa using hg
    | some e =>
      rw [hr] at hg
      simp only [Layouts.Sponge.ground]
      simp only [OptionEAt, EAt, Layouts.OptionE.tagOffset, Layouts.OptionE.Some.f0, Layouts.OptionE.Some.tag,
        Layouts.E.c0, Layouts.E.c1, BitVec.add_zero] at hg ⊢
      refine ⟨by rw [show a = a + BitVec.ofNat 64 0 by simp, get _ (by decide)]; simpa using hg.1,
        by rw [get _ (by decide)]; exact hg.2.1, by rw [add, get _ (by decide), ← add]; exact hg.2.2⟩

/-- **A transcript is kept** by a call that keeps its footprint and the heap below `NEXT`. -/
theorem TranscriptAt.keep {a : Word} {t : Model.TState} (ht : TranscriptAt env m a t)
    (ha : a.toNat + Layouts.Transcript.byteSize < 2 ^ 64) (hk : Keeps m m' a Layouts.Transcript.byteSize)
    (hh : HeapKept env m m') : TranscriptAt env m' a t := by
  obtain ⟨hb1, hb2, hs, hp, h1, h2, h3⟩ := ht
  simp only [Layouts.Transcript.byteSize, Layouts.Transcript.sponge, Layouts.Transcript.proof,
    Layouts.Transcript.stream_offset, Layouts.Transcript.opening_offset, Layouts.Transcript.checked] at *
  have get : ∀ k, k + 8 ≤ 360 → m'.getMem (a + BitVec.ofNat 64 k) = m.getMem (a + BitVec.ofNat 64 k) :=
    fun k hkn => keeps_get hk ha hkn
  refine ⟨hb1, hb2, hs.keep (by simpa using (by omega : a.toNat + 328 < 2 ^ 64)) ?_, ?_, by rw [get _ (by decide)]; exact h1,
    by rw [get _ (by decide)]; exact h2, ?_⟩
  · simpa using hk.mono (a' := a) (n' := 328) (by simp) (by omega)
  · rw [get _ (by decide)]; exact hp.keep hh
  · rw [getByte_congr]; exact h3
    have h352 : (a + 352#64).toNat = a.toNat + 352 := toNat_add_ofNat (by omega)
    apply hk
    constructor <;> rw [toNat_alignToDword, h352] <;> omega

/-- **A transcript in a caller's frame is kept by a call without `out`.** -/
theorem TranscriptAt.frameF {top a : Word} {t : Model.TState} (ht : TranscriptAt env m a t)
    (hf : env.Frame top Tactic.F m m') (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hlim : env.stackLimit.toNat ≤ top.toNat) (ha : InFrame top a Layouts.Transcript.byteSize) :
    TranscriptAt env m' a t :=
  ht.keep ha.2 (Env.Frame.keeps_above hf hlim ha.1 fun _ _ h => h)
    (HeapKept.of_frame hf hnx fun _ h => h.elim)

end Keep

end Rv64mc.Spec.Transcript
