import Rv64Verifier.Proofs.Runtime.Step
import Rv64Verifier.Proofs.Rodata
import Rv64Verifier.Model.Transcript

/-!
# The transcript in memory

How the image holds `transcript.rs`'s values, read off the code:

* `Sponge` (336 bytes): `pending: [(E, u64); 4]` at `0..128`, waiting scalar `i` at `32 i` (its
  limbs, then its tag at `+24`); `state: [u64; 25]` at `128..328`; `n_pending` at `328`.
  `spongeAt` reads the statement's `Sponge` back: the state's lanes, and the first `n_pending`
  waiting scalars with their tags.
* `Transcript` (368 bytes): `proof: &Proof` at `0`, the sponge at `8..344`, `stream_offset` at
  `344`, `opening_offset` at `352`, `checked` (a byte) at `360`.
* `Proof`: `stream: Vec<E>` at `0`, `merkle_openings: Vec<Vec<MerklePath>>` at `24`.

`TranscriptAt s p T` says the transcript at `p` stands for `T`: its proof's stream, its sponge and
its offsets (the openings and the ghost roots are not read here). `TranscriptOk` is where it and the
proof's bytes it reads lie.

Frames are stated on doublewords (`DFrame s t w`: a doubleword whose eight bytes miss `w` keeps
its value), which every callee's frame implies: the runtime's `ByteFrame`, and the two-range
frames of the field and hash contracts.
-/

namespace Rv64Verifier.Transcript
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model

/-! ## Frames of doublewords -/

/-- `t`'s doublewords are `s`'s wherever their eight bytes miss `w`. -/
def DFrame (s t : MachineState) (w : Word → Prop) : Prop :=
  ∀ a, (∀ i < 8, ¬ w (a + BitVec.ofNat 64 i)) → t.getMem a = s.getMem a

theorem DFrame.refl (s : MachineState) (w : Word → Prop) : DFrame s s w := fun _ _ ↦ rfl

theorem DFrame.mono {s t : MachineState} {w w' : Word → Prop} (h : DFrame s t w)
    (hw : ∀ a, w a → w' a) : DFrame s t w' :=
  fun a ha ↦ h a fun i hi h' ↦ ha i hi (hw _ h')

theorem DFrame.trans {s t u : MachineState} {w w' : Word → Prop} (h₁ : DFrame s t w)
    (h₂ : DFrame t u w') (hw : ∀ a, w' a → w a) : DFrame s u w :=
  fun a ha ↦ (h₂ a fun i hi h' ↦ ha i hi (hw _ h')).trans (h₁ a ha)

theorem add_ofNat_zero (a : Word) : a + BitVec.ofNat 64 0 = a := by
  simp

theorem DFrame.of_memFrame {s t : MachineState} {lo : Word} {n : Nat} (h : MemFrame s t lo n) :
    DFrame s t (Within · lo n) :=
  fun a ha ↦ h a (by simpa only [add_ofNat_zero] using ha 0 (by decide))

theorem DFrame.of_byteFrame {s t : MachineState} {w : Word → Prop} (h : ByteFrame s t w) :
    DFrame s t w :=
  fun _ ha ↦ h.getMem ha

theorem DFrame.of_same {s t : MachineState} (h : ∀ a, t.getMem a = s.getMem a) (w : Word → Prop) :
    DFrame s t w :=
  fun a _ ↦ h a

/-- The field and hash contracts' frame: two ranges. -/
theorem DFrame.of_two {s t : MachineState} {lo₁ lo₂ : Word} {n₁ n₂ : Nat}
    (h : ∀ a, ¬ Within a lo₁ n₁ → ¬ Within a lo₂ n₂ → t.getMem a = s.getMem a) :
    DFrame s t fun a ↦ Within a lo₁ n₁ ∨ Within a lo₂ n₂ :=
  fun a ha ↦ h a (fun h' ↦ ha 0 (by decide) (Or.inl (by rwa [add_ofNat_zero])))
    (fun h' ↦ ha 0 (by decide) (Or.inr (by rwa [add_ofNat_zero])))

theorem add_ofNat_add (p : Word) (k i : Nat) :
    p + BitVec.ofNat 64 k + BitVec.ofNat 64 i = p + BitVec.ofNat 64 (k + i) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

/-- An `E` whose bytes miss the frame keeps its value. -/
theorem DFrame.eAt {s t : MachineState} {w : Word → Prop} (h : DFrame s t w) {p : Word}
    (hp : ∀ i < 24, ¬ w (p + BitVec.ofNat 64 i)) : eAt t p = eAt s p := by
  have e (k : Nat) (hk : k < 3) : t.getMem (p + BitVec.ofNat 64 (8 * k)) =
      s.getMem (p + BitVec.ofNat 64 (8 * k)) :=
    h _ fun i hi ↦ by rw [add_ofNat_add]; exact hp _ (by omega)
  have e0 := e 0 (by decide)
  have e1 := e 1 (by decide)
  have e2 := e 2 (by decide)
  simp only [Nat.mul_zero, add_ofNat_zero, Nat.mul_one, Nat.reduceMul] at e0 e1 e2
  unfold Rv64Verifier.eAt
  rw [e0, show (8 : Word) = BitVec.ofNat 64 8 from rfl, e1,
    show (16 : Word) = BitVec.ofNat 64 16 from rfl, e2]

/-- A slice of `E` whose bytes miss the frame keeps its value. -/
theorem DFrame.eListAt {s t : MachineState} {w : Word → Prop} (h : DFrame s t w) {p : Word}
    {n : Nat} (hp : ∀ i < 24 * n, ¬ w (p + BitVec.ofNat 64 i)) : eListAt t p n = eListAt s p n := by
  unfold Rv64Verifier.eListAt
  apply List.map_congr_left
  intro i hi
  simp only [List.mem_range] at hi
  exact h.eAt fun j hj ↦ by rw [add_ofNat_add]; exact hp _ (by omega)

theorem rodataWords_aligned : (rodataWords.all fun q ↦ q.1.toNat % 8 == 0) = true := by
  decide +kernel

/-- `.rodata` is kept by a frame that misses it. -/
theorem _root_.Rv64Verifier.RodataOk.dframe {s t : MachineState} {w : Word → Prop} (h : RodataOk s) (hf : DFrame s t w)
    (hw : ∀ a, Within a rodataBase rodataSize → ¬ w a) : RodataOk t := by
  intro p hp
  have hw' := within_of_mem_rodataWords hp
  have h8 : p.1.toNat % 8 = 0 := by
    simpa using List.all_eq_true.mp rodataWords_aligned p hp
  rw [hf p.1 fun i hi ↦ hw _ (by addr_omega [hw', h8, hi])]
  exact h p hp

/-! ## Regions -/

/-- `n` bytes from `a`, 8-aligned, in one of the machine's data windows. -/
@[rv_addr] def Region (a : Word) (n : Nat) : Prop := Mapped a n ∧ a.toNat % 8 = 0

theorem Region.valid {a x : Word} {n : Nat} (h : Region a n) (h1 : a.toNat ≤ x.toNat)
    (h2 : x.toNat + 8 ≤ a.toNat + n) (h3 : x.toNat % 8 = 0) : Sym.validAccess 8 x = true :=
  Mapped.valid8 h.1 h1 h2 h3

/-- The stack's bytes lie in the upper window. -/
theorem _root_.Rv64Verifier.Runtime.RtStack.mapped {s : MachineState} {n : Nat} (h : RtStack s n) (hn : 16 ≤ n)
    (h8 : n % 8 = 0) :
    0xa0000000 ≤ (stackLo s n).toNat ∧ (stackLo s n).toNat + n ≤ 0xc0000008 ∧
      (s.getReg .x2).toNat = (stackLo s n).toNat + n := by
  have hb := h.bounds (by omega) h8
  have ha := h.above
  have h0 := (Sym.validAccess_eight _).mp (validAccess_of_dword (h.valid 0 (by omega)))
  have h1 := (Sym.validAccess_eight _).mp (validAccess_of_dword (h.valid 1 (by omega)))
  simp only [Nat.mul_zero, BitVec.add_zero, Nat.mul_one] at h0 h1
  have hlo := hb.2.2.2
  simp only [heapEnd] at ha
  rw [BitVec.toNat_add] at h1
  simp only [BitVec.toNat_ofNat] at h1
  omega

/-- A callee's stack: `k` bytes below `sp`, `m` bytes deep, within the caller's. -/
theorem _root_.Rv64Verifier.Runtime.RtStack.sub {s u : MachineState} {n m : Nat} (k : Nat)
    (h : RtStack s n) (hsp : u.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 k) (hk : k + m ≤ n)
    (h16 : k % 16 = 0) (hm8 : m % 8 = 0) (hn : 16 ≤ n) (hn8 : n % 8 = 0) : RtStack u m := by
  have hb := h.mapped hn hn8
  have hlo : (stackLo u m).toNat = (s.getReg .x2).toNat - k - m := by
    simp only [stackLo, hsp]; addr_omega [hb, hk]
  have ha := h.above
  have hx := h.next
  have hr := h.rodata
  refine ⟨⟨ValidMemRange.sub h.valid (by omega) (by omega) (by omega), ?_⟩, ?_, ?_, ?_⟩
  · have hal := h.aligned
    rw [hsp]; addr_omega [hb, h16, hk, hal]
  · addr_omega [ha, hlo, hb, hk]
  · addr_omega [hx, hlo, hb, hk]
  · addr_omega [hr, hlo, hb, hk]

/-! ## The sponge -/

/-- The 25 lanes from `a`. -/
def stateAt (s : MachineState) (a : Word) : KeccakState :=
  Vector.ofFn fun i : Fin 25 ↦ UInt64.ofBitVec (s.getMem (a + BitVec.ofNat 64 (8 * i.val)))

/-- The first `n` waiting scalars of the sponge at `a`, with their tags. -/
def pendingAt (s : MachineState) (a : Word) (n : Nat) : List (E × ℕ) :=
  (List.range n).map fun i ↦
    (eAt s (a + BitVec.ofNat 64 (32 * i)), (s.getMem (a + BitVec.ofNat 64 (32 * i + 24))).toNat)

/-- `n_pending` of the sponge at `a`, at most four: every function that reads a larger one traps,
so the sponge is read within its bytes. -/
def nPending (s : MachineState) (a : Word) : Nat := min (s.getMem (a + 328)).toNat 4

/-- The sponge at `a`. -/
def spongeAt (s : MachineState) (a : Word) : Sponge :=
  ⟨stateAt s (a + 128), pendingAt s a (nPending s a)⟩

/-- `Sponge::duplex`, `Sponge::absorb` and `Sponge::sample` over Keccak-f[1600]. -/
def spDuplex (sp : Sponge) : Sponge := Id.run (duplex (m := Id) keccakF1600 sp)

def spAbsorb (sp : Sponge) (x : E) (tag : ℕ) : Sponge :=
  Id.run (absorb (m := Id) keccakF1600 sp x tag)

def spSqueeze (sp : Sponge) : E × Sponge := Id.run (squeeze (m := Id) keccakF1600 sp)

/-! ## The transcript -/

@[rv_addr] def transcriptSize : Nat := 368

/-- `Transcript::proof`. -/
@[rv_addr] def proofAt (s : MachineState) (p : Word) : Word := s.getMem p

/-- The buffer and the length of the proof's stream. -/
@[rv_addr] def streamPtr (s : MachineState) (p : Word) : Word := vecPtr s (proofAt s p)
@[rv_addr] def streamLen (s : MachineState) (p : Word) : Nat := (vecLen s (proofAt s p)).toNat

/-- The transcript at `p` stands for `T`: the proof's stream, the sponge, the offsets. -/
structure TranscriptAt (s : MachineState) (p : Word) (T : TState) : Prop where
  stream : eListAt s (streamPtr s p) (streamLen s p) = T.proof.stream
  sponge : spongeAt s (p + 8) = T.sponge
  streamOffset : (s.getMem (p + 344)).toNat = T.streamOffset
  openingOffset : (s.getMem (p + 352)).toNat = T.openingOffset

/-- The proof's bytes the transcript at `p` reads, the `Proof` and its stream's buffer, miss the
`n` bytes from `lo`. -/
@[rv_addr] def ProofApart (s : MachineState) (p : Word) (lo : Word) (n : Nat) : Prop :=
  Apart (proofAt s p) 48 lo n ∧ Apart (streamPtr s p) (24 * streamLen s p) lo n

/-- The transcript at `p` and the proof it reads lie in memory, the proof apart from the parts of
the transcript that change. -/
structure TranscriptOk (s : MachineState) (p : Word) : Prop where
  self : Region p transcriptSize
  proof : Region (proofAt s p) 48
  stream : streamLen s p = 0 ∨ Region (streamPtr s p) (24 * streamLen s p)
  apart : ProofApart s p (p + 8) 344

/-- The stream's buffer and length are kept by a frame that misses the `Proof` and `proof`. -/
theorem DFrame.stream {s t : MachineState} {w : Word → Prop} (h : DFrame s t w) {p : Word}
    (hp : ∀ i < 8, ¬ w (p + BitVec.ofNat 64 i))
    (hq : ∀ i < 48, ¬ w (proofAt s p + BitVec.ofNat 64 i)) :
    proofAt t p = proofAt s p ∧ streamPtr t p = streamPtr s p ∧ streamLen t p = streamLen s p := by
  have h0 : proofAt t p = proofAt s p := h p hp
  refine ⟨h0, ?_, ?_⟩
  · simp only [streamPtr, vecPtr, h0]
    exact h _ fun i hi ↦ by rw [show (8 : Word) = BitVec.ofNat 64 8 from rfl, add_ofNat_add]; exact hq _ (by omega)
  · simp only [streamLen, vecLen, h0]
    rw [h _ fun i hi ↦ by rw [show (16 : Word) = BitVec.ofNat 64 16 from rfl, add_ofNat_add]; exact hq _ (by omega)]

/-- The stream a transcript reads is kept by a frame that misses the proof's bytes. -/
theorem DFrame.eListAt_stream {s t : MachineState} {w : Word → Prop} (h : DFrame s t w) {p : Word}
    (hp : ∀ i < 8, ¬ w (p + BitVec.ofNat 64 i))
    (hq : ∀ i < 48, ¬ w (proofAt s p + BitVec.ofNat 64 i))
    (hb : ∀ i < 24 * streamLen s p, ¬ w (streamPtr s p + BitVec.ofNat 64 i)) :
    Rv64Verifier.eListAt t (streamPtr t p) (streamLen t p) =
      Rv64Verifier.eListAt s (streamPtr s p) (streamLen s p) := by
  obtain ⟨-, h1, h2⟩ := h.stream hp hq
  rw [h1, h2]
  exact h.eListAt hb

/-! ## Results -/

/-- An `Option<E>` at `a`: its tag, then the value. -/
def optEAt (s : MachineState) (a : Word) : Option E :=
  if s.getMem a = 0 then none else some (eAt s (a + 8))

/-- `n` of them from `a`, 32 bytes apart. -/
def optEListAt (s : MachineState) (a : Word) (n : Nat) : List (Option E) :=
  (List.range n).map fun i ↦ optEAt s (a + BitVec.ofNat 64 (32 * i))

/-- `Result<Vec<_>, VerifierError>`'s `Err`, which the `Vec`'s capacity takes as a niche. -/
@[rv_addr] def errNiche : Word := 0xffffffffffffffff

/-- A `Vec<E>` at `a` holding `xs` in a buffer allocated from `s` on to `t`. -/
structure NewVecE (s t : MachineState) (a : Word) (xs : List E) : Prop where
  vec : VecOk t a 24 8
  buf : NewBuf s t (vecPtr t a) ((vecCap t a).toNat * 24) 8
  elems : vecEs t a = xs

end Rv64Verifier.Transcript
