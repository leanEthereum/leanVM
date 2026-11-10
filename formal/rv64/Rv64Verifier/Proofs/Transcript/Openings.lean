import Rv64Verifier.Proofs.Transcript.Frames
import Rv64Verifier.Proofs.Hash.Contracts

/-!
# The proof's Merkle openings in memory

`Proof.merkle_openings: Vec<Vec<MerklePath>>` at the proof's `24`; a phase is a `Vec<MerklePath>`,
a `MerklePath` (56 bytes) its leaf `Vec<K>` at `0`, its siblings `Vec<[u8; 32]>` at `24` (alignment
one: read as bytes, a digest's lanes little-endian) and `leaf_index` at `48`.

`OpeningsAt s p T` says the openings of the transcript at `p`'s proof are `T.proof.openings`, in
the shape `PcsContracts.VsoSpec` takes. `OpenFoot s p` is the bytes it reads: the `Vec` buffers
(the siblings' widened to the doublewords holding them, as `getByte` reads them), the headers
inside them; the outer header lies in the `Proof`'s 48 bytes. `OpenFits s p` says those buffers do
not wrap. `OpenMem s p w` places them for a function writing at most `w`: mapped, aligned as their
types ask (`OpenMapped`, which gives `OpenFits`), `OpenFoot` missing `w`.

A frame that misses the pointer at `p`, the `Proof` and `OpenFoot` keeps `OpeningsAt`, `OpenFoot`,
`OpenFits` and `OpenMapped` (`DFrame.openings`, `DFrame.openingsAt`, `DFrame.openMapped`);
`OpeningsAt` reads only `T.proof` (`OpeningsAt.of_proof`).
-/

namespace Rv64Verifier.Transcript
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model

/-- A lane from its eight bytes, little-endian. -/
def laneOfBytes (bs : List (BitVec 8)) : UInt64 :=
  UInt64.ofBitVec (bs.foldr (fun b acc ↦ (acc <<< 8) ||| b.setWidth 64) 0)

/-- The digest whose 32 bytes start at `a`. -/
def digestBytesAt (s : MachineState) (a : Word) : Digest :=
  Vector.ofFn fun i : Fin 4 ↦ laneOfBytes (Contracts.bytesAt s (a + BitVec.ofNat 64 (8 * i.val)) 8)

/-- `n` words of `K` from `a`. -/
def kListAt (s : MachineState) (a : Word) (n : Nat) : List K :=
  (List.range n).map fun i ↦ BF64.ofBitVec (s.getMem (a + BitVec.ofNat 64 (8 * i)))

/-- The `MerklePath` at `a` is `o`. -/
structure PathAt (s : MachineState) (a : Word) (o : Opening) : Prop where
  leaf : kListAt s (vecPtr s a) (vecLen s a).toNat = o.leaf
  path : (List.range (vecLen s (a + 24)).toNat).map
    (fun i ↦ digestBytesAt s (vecPtr s (a + 24) + BitVec.ofNat 64 (32 * i))) = o.path
  leafIndex : (s.getMem (a + 48)).toNat = o.leafIndex

/-- The `Vec<MerklePath>` at `a` is the phase `ph`. -/
structure PhaseAt (s : MachineState) (a : Word) (ph : List Opening) : Prop where
  len : (vecLen s a).toNat = ph.length
  paths : ∀ j (h : j < ph.length), PathAt s (vecPtr s a + BitVec.ofNat 64 (56 * j)) ph[j]

/-- Where the openings' outer `Vec` is: the proof's `24`. -/
@[rv_addr] def openingsVec (s : MachineState) (p : Word) : Word := proofAt s p + 24

/-- The transcript at `p`'s proof holds `T`'s openings. -/
structure OpeningsAt (s : MachineState) (p : Word) (T : TState) : Prop where
  len : (vecLen s (openingsVec s p)).toNat = T.proof.openings.length
  phases : ∀ k (h : k < T.proof.openings.length),
    PhaseAt s (vecPtr s (openingsVec s p) + BitVec.ofNat 64 (24 * k)) T.proof.openings[k]

/-- How many bytes the doublewords holding the `n` digests from `b` span, from the first's start:
none for none. -/
@[rv_addr] def sibSpan (b : Word) (n : Nat) : Nat := 32 * n + 8 * min n ((b.toNat % 8 + 7) / 8)

/-- The bytes a `MerklePath` at `a` reads beyond its header: the leaf's buffer, the doublewords
holding the siblings' bytes. -/
def PathFoot (s : MachineState) (a y : Word) : Prop :=
  Within y (vecPtr s a) (8 * (vecLen s a).toNat) ∨
    Within y (vecPtr s (a + 24) &&& ~~~7#64) (sibSpan (vecPtr s (a + 24)) (vecLen s (a + 24)).toNat)

/-- The bytes a phase at `a` reads beyond its header: its buffer, its paths'. -/
def PhaseFoot (s : MachineState) (a y : Word) : Prop :=
  Within y (vecPtr s a) (56 * (vecLen s a).toNat) ∨
    ∃ j < (vecLen s a).toNat, PathFoot s (vecPtr s a + BitVec.ofNat 64 (56 * j)) y

/-- The bytes the openings of the transcript at `p` read beyond the `Proof`. -/
def OpenFoot (s : MachineState) (p y : Word) : Prop :=
  Within y (vecPtr s (openingsVec s p)) (24 * (vecLen s (openingsVec s p)).toNat) ∨
    ∃ k < (vecLen s (openingsVec s p)).toNat,
      PhaseFoot s (vecPtr s (openingsVec s p) + BitVec.ofNat 64 (24 * k)) y

attribute [local rv_addr] vecPtr vecLen

/-! ## What the openings read does not wrap -/

/-- The leaf's and the siblings' buffers of the `MerklePath` at `a` end below `2 ^ 64`. -/
structure PathFits (s : MachineState) (a : Word) : Prop where
  leaf : (vecPtr s a).toNat + 8 * (vecLen s a).toNat ≤ 2 ^ 64
  path : (vecPtr s (a + 24)).toNat + 32 * (vecLen s (a + 24)).toNat ≤ 2 ^ 64

/-- The phase at `a`'s buffer and its paths' end below `2 ^ 64`. -/
structure PhaseFits (s : MachineState) (a : Word) : Prop where
  buf : (vecPtr s a).toNat + 56 * (vecLen s a).toNat ≤ 2 ^ 64
  paths : ∀ j < (vecLen s a).toNat, PathFits s (vecPtr s a + BitVec.ofNat 64 (56 * j))

/-- The buffers the openings of the transcript at `p` read end below `2 ^ 64`. -/
structure OpenFits (s : MachineState) (p : Word) : Prop where
  buf : (vecPtr s (openingsVec s p)).toNat + 24 * (vecLen s (openingsVec s p)).toNat ≤ 2 ^ 64
  phases : ∀ k < (vecLen s (openingsVec s p)).toNat,
    PhaseFits s (vecPtr s (openingsVec s p) + BitVec.ofNat 64 (24 * k))

/-! ## Where the openings lie -/

/-- The `MerklePath` at `a`'s buffers: the leaf's mapped and 8-aligned, the siblings' mapped. -/
structure PathMapped (s : MachineState) (a : Word) : Prop where
  leaf : (vecLen s a).toNat = 0 ∨ Region (vecPtr s a) (8 * (vecLen s a).toNat)
  siblings : (vecLen s (a + 24)).toNat = 0 ∨
    Mapped (vecPtr s (a + 24)) (32 * (vecLen s (a + 24)).toNat)

/-- The phase at `a`'s buffer, mapped and 8-aligned, and its paths'. -/
structure PhaseMapped (s : MachineState) (a : Word) : Prop where
  buf : (vecLen s a).toNat = 0 ∨ Region (vecPtr s a) (56 * (vecLen s a).toNat)
  paths : ∀ j < (vecLen s a).toNat, PathMapped s (vecPtr s a + BitVec.ofNat 64 (56 * j))

/-- The buffers the openings of the transcript at `p` read: mapped, aligned as their types ask. -/
structure OpenMapped (s : MachineState) (p : Word) : Prop where
  buf : (vecLen s (openingsVec s p)).toNat = 0 ∨
    Region (vecPtr s (openingsVec s p)) (24 * (vecLen s (openingsVec s p)).toNat)
  phases : ∀ k < (vecLen s (openingsVec s p)).toNat,
    PhaseMapped s (vecPtr s (openingsVec s p) + BitVec.ofNat 64 (24 * k))

/-- The openings of the transcript at `p` in place for a function writing at most `w`. -/
structure OpenMem (s : MachineState) (p : Word) (w : Word → Prop) : Prop where
  mapped : OpenMapped s p
  apart : ∀ y, OpenFoot s p y → ¬ w y

theorem PathMapped.fits {s : MachineState} {a : Word} (h : PathMapped s a) : PathFits s a := by
  constructor
  · rcases h.leaf with h0 | ⟨hm, -⟩
    · have := (vecPtr s a).isLt
      omega
    · simp only [Mapped] at hm
      omega
  · rcases h.siblings with h0 | hm
    · have := (vecPtr s (a + 24)).isLt
      omega
    · simp only [Mapped] at hm
      omega

theorem PhaseMapped.fits {s : MachineState} {a : Word} (h : PhaseMapped s a) : PhaseFits s a := by
  refine ⟨?_, fun j hj ↦ (h.paths j hj).fits⟩
  rcases h.buf with h0 | ⟨hm, -⟩
  · have := (vecPtr s a).isLt
    omega
  · simp only [Mapped] at hm
    omega

theorem OpenMapped.fits {s : MachineState} {p : Word} (h : OpenMapped s p) : OpenFits s p := by
  refine ⟨?_, fun k hk ↦ (h.phases k hk).fits⟩
  rcases h.buf with h0 | ⟨hm, -⟩
  · have := (vecPtr s (openingsVec s p)).isLt
    omega
  · simp only [Mapped] at hm
    omega

/-! ## Frames -/

theorem getByte_congr {s t : MachineState} {a : Word}
    (h : t.getMem (alignToDword a) = s.getMem (alignToDword a)) : t.getByte a = s.getByte a := by
  simp only [MachineState.getByte, h]

/-- The four header words of the `MerklePath` at `a` (in its 56 bytes) are kept. -/
theorem DFrame.pathHead {s t : MachineState} {w : Word → Prop} (h : DFrame s t w) {a : Word}
    (hm : Misses w a 56) (han : a.toNat + 56 ≤ 2 ^ 64) :
    vecPtr t a = vecPtr s a ∧ vecLen t a = vecLen s a ∧ vecPtr t (a + 24) = vecPtr s (a + 24) ∧
      vecLen t (a + 24) = vecLen s (a + 24) ∧ t.getMem (a + 48) = s.getMem (a + 48) := by
  refine ⟨h _ (hm.bytes ?_ ?_ han), h _ (hm.bytes ?_ ?_ han), h _ (hm.bytes ?_ ?_ han),
    h _ (hm.bytes ?_ ?_ han), h _ (hm.bytes ?_ ?_ han)⟩ <;> addr_omega [han]

/-- A `MerklePath` whose header and footprint miss the frame keeps its value. -/
theorem DFrame.pathAt {s t : MachineState} {w : Word → Prop} (h : DFrame s t w) {a : Word}
    {o : Opening} (hm : Misses w a 56) (han : a.toNat + 56 ≤ 2 ^ 64)
    (hf : ∀ y, PathFoot s a y → ¬ w y) (fit : PathFits s a) (hp : PathAt s a o) : PathAt t a o := by
  obtain ⟨e0, e1, e2, e3, e4⟩ := h.pathHead hm han
  have fl := fit.leaf
  have fp := fit.path
  refine ⟨?_, ?_, by rw [e4]; exact hp.leafIndex⟩
  · rw [e0, e1, ← hp.leaf]
    unfold kListAt
    refine List.map_congr_left fun i hi ↦ ?_
    simp only [List.mem_range] at hi
    rw [h _ fun j hj hw ↦ hf _ (Or.inl (by addr_omega [fl, hi, hj])) hw]
  · rw [e2, e3, ← hp.path]
    refine List.map_congr_left fun i hi ↦ ?_
    simp only [List.mem_range] at hi
    unfold digestBytesAt
    congr 1
    funext l
    congr 1
    unfold Contracts.bytesAt
    refine List.map_congr_left fun m hm' ↦ ?_
    simp only [List.mem_range] at hm'
    refine getByte_congr (h _ fun j hj hw ↦ hf _ (Or.inr ?_) hw)
    have hal := Sym.alignToDword_toNat
      (vecPtr s (a + 24) + BitVec.ofNat 64 (32 * i) + BitVec.ofNat 64 (8 * l.val) + BitVec.ofNat 64 m)
    have hal0 := Sym.alignToDword_toNat (vecPtr s (a + 24))
    have hl := l.isLt
    simp only [alignToDword] at hal0
    addr_omega [fp, hi, hj, hl, hm', hal, hal0]

/-- What the frame keeps of a `MerklePath` whose header and footprint miss it: its footprint, and
that it fits. -/
theorem DFrame.pathFoot {s t : MachineState} {w : Word → Prop} (h : DFrame s t w) {a : Word}
    (hm : Misses w a 56) (han : a.toNat + 56 ≤ 2 ^ 64) (fit : PathFits s a) :
    (∀ y, PathFoot t a y ↔ PathFoot s a y) ∧ PathFits t a := by
  obtain ⟨e0, e1, e2, e3, -⟩ := h.pathHead hm han
  refine ⟨fun y ↦ by simp only [PathFoot, e0, e1, e2, e3], ?_⟩
  exact ⟨by rw [e0, e1]; exact fit.leaf, by rw [e2, e3]; exact fit.path⟩

/-- The phase at `a`'s header (24 bytes) kept. -/
theorem DFrame.phaseHead {s t : MachineState} {w : Word → Prop} (h : DFrame s t w) {a : Word}
    (hm : Misses w a 24) (han : a.toNat + 24 ≤ 2 ^ 64) :
    vecPtr t a = vecPtr s a ∧ vecLen t a = vecLen s a :=
  ⟨h _ (hm.bytes (by addr_omega [han]) (by addr_omega [han]) han),
    h _ (hm.bytes (by addr_omega [han]) (by addr_omega [han]) han)⟩

/-- A phase whose header and footprint miss the frame: its value, its footprint and that it fits
are kept. -/
theorem DFrame.phase {s t : MachineState} {w : Word → Prop} (h : DFrame s t w) {a : Word}
    (hm : Misses w a 24) (han : a.toNat + 24 ≤ 2 ^ 64) (hf : ∀ y, PhaseFoot s a y → ¬ w y)
    (fit : PhaseFits s a) :
    (∀ ph, PhaseAt s a ph → PhaseAt t a ph) ∧ (∀ y, PhaseFoot t a y ↔ PhaseFoot s a y) ∧
      PhaseFits t a := by
  obtain ⟨e0, e1⟩ := h.phaseHead hm han
  have fb := fit.buf
  have path (j : Nat) (hj : j < (vecLen s a).toNat) :
      Misses w (vecPtr s a + BitVec.ofNat 64 (56 * j)) 56 ∧
        (vecPtr s a + BitVec.ofNat 64 (56 * j)).toNat + 56 ≤ 2 ^ 64 ∧
        ∀ y, PathFoot s (vecPtr s a + BitVec.ofNat 64 (56 * j)) y → ¬ w y :=
    ⟨fun y hy ↦ hf y (Or.inl (by addr_omega [hy, fb, hj])), by addr_omega [fb, hj],
      fun y hy ↦ hf y (Or.inr ⟨j, hj, hy⟩)⟩
  refine ⟨fun ph hp ↦ ⟨by rw [e1]; exact hp.len, fun j hj ↦ ?_⟩, fun y ↦ ?_, ?_⟩
  · have hj' : j < (vecLen s a).toNat := by rw [hp.len]; exact hj
    obtain ⟨m, n, f⟩ := path j hj'
    rw [e0]
    exact h.pathAt m n f (fit.paths j hj') (hp.paths j hj)
  · simp only [PhaseFoot, e0, e1]
    refine or_congr Iff.rfl (exists_congr fun j ↦ ?_)
    refine ⟨fun ⟨hj, hy⟩ ↦ ⟨hj, ?_⟩, fun ⟨hj, hy⟩ ↦ ⟨hj, ?_⟩⟩
    · obtain ⟨m, n, -⟩ := path j hj
      exact ((h.pathFoot m n (fit.paths j hj)).1 y).mp hy
    · obtain ⟨m, n, -⟩ := path j hj
      exact ((h.pathFoot m n (fit.paths j hj)).1 y).mpr hy
  · refine ⟨by rw [e0, e1]; exact fb, fun j hj ↦ ?_⟩
    rw [e1] at hj
    obtain ⟨m, n, -⟩ := path j hj
    rw [e0]
    exact (h.pathFoot m n (fit.paths j hj)).2

/-- **A frame keeps the openings** of the transcript at `p` when it misses the pointer at `p`, the
`Proof`'s 48 bytes and what the openings read beyond them (`OpenFoot`), which then do not wrap
(`OpenFits`): their value, their footprint and that it fits. -/
theorem DFrame.openings {s t : MachineState} {w : Word → Prop} (h : DFrame s t w) {p : Word}
    (hp : Misses w p 8) (hpn : p.toNat + 8 ≤ 2 ^ 64) (hq : Misses w (proofAt s p) 48)
    (hqn : (proofAt s p).toNat + 48 ≤ 2 ^ 64) (hf : ∀ y, OpenFoot s p y → ¬ w y)
    (fit : OpenFits s p) :
    (∀ T, OpeningsAt s p T → OpeningsAt t p T) ∧ (∀ y, OpenFoot t p y ↔ OpenFoot s p y) ∧
      OpenFits t p := by
  have e : proofAt t p = proofAt s p := h.proofAt_eq hp hpn
  have ev : openingsVec t p = openingsVec s p := by simp only [openingsVec, e]
  have e0 : vecPtr t (openingsVec s p) = vecPtr s (openingsVec s p) :=
    h _ (hq.bytes (by simp only [openingsVec]; addr_omega [hqn])
      (by simp only [openingsVec]; addr_omega [hqn]) hqn)
  have e1 : vecLen t (openingsVec s p) = vecLen s (openingsVec s p) :=
    h _ (hq.bytes (by simp only [openingsVec]; addr_omega [hqn])
      (by simp only [openingsVec]; addr_omega [hqn]) hqn)
  have fb := fit.buf
  have phase (k : Nat) (hk : k < (vecLen s (openingsVec s p)).toNat) :=
    h.phase (a := vecPtr s (openingsVec s p) + BitVec.ofNat 64 (24 * k))
      (fun y hy ↦ hf y (Or.inl (by addr_omega [hy, fb, hk]))) (by addr_omega [fb, hk])
      (fun y hy ↦ hf y (Or.inr ⟨k, hk, hy⟩)) (fit.phases k hk)
  refine ⟨fun T hT ↦ ⟨by rw [ev, e1]; exact hT.len, fun k hk ↦ ?_⟩, fun y ↦ ?_, ?_⟩
  · have hk' : k < (vecLen s (openingsVec s p)).toNat := by rw [hT.len]; exact hk
    rw [ev, e0]
    exact (phase k hk').1 _ (hT.phases k hk)
  · simp only [OpenFoot, ev, e0, e1]
    refine or_congr Iff.rfl (exists_congr fun k ↦ ?_)
    exact ⟨fun ⟨hk, hy⟩ ↦ ⟨hk, ((phase k hk).2.1 y).mp hy⟩,
      fun ⟨hk, hy⟩ ↦ ⟨hk, ((phase k hk).2.1 y).mpr hy⟩⟩
  · refine ⟨by rw [ev, e0, e1]; exact fb, fun k hk ↦ ?_⟩
    rw [ev, e1] at hk
    rw [ev, e0]
    exact (phase k hk).2.2

theorem DFrame.pathMapped {s t : MachineState} {w : Word → Prop} (h : DFrame s t w) {a : Word}
    (hm : Misses w a 56) (han : a.toNat + 56 ≤ 2 ^ 64) (hp : PathMapped s a) : PathMapped t a := by
  obtain ⟨e0, e1, e2, e3, -⟩ := h.pathHead hm han
  exact ⟨by rw [e0, e1]; exact hp.leaf, by rw [e2, e3]; exact hp.siblings⟩

theorem DFrame.phaseMapped {s t : MachineState} {w : Word → Prop} (h : DFrame s t w) {a : Word}
    (hm : Misses w a 24) (han : a.toNat + 24 ≤ 2 ^ 64) (hf : ∀ y, PhaseFoot s a y → ¬ w y)
    (fit : PhaseFits s a) (hp : PhaseMapped s a) : PhaseMapped t a := by
  obtain ⟨e0, e1⟩ := h.phaseHead hm han
  have fb := fit.buf
  refine ⟨by rw [e0, e1]; exact hp.buf, fun j hj ↦ ?_⟩
  rw [e1] at hj
  rw [e0]
  exact h.pathMapped (fun y hy ↦ hf y (Or.inl (by addr_omega [hy, fb, hj])))
    (by addr_omega [fb, hj]) (hp.paths j hj)

/-- A frame as `DFrame.openings` asks keeps `OpenMapped`. -/
theorem DFrame.openMapped {s t : MachineState} {w : Word → Prop} (h : DFrame s t w) {p : Word}
    (hp : Misses w p 8) (hpn : p.toNat + 8 ≤ 2 ^ 64) (hq : Misses w (proofAt s p) 48)
    (hqn : (proofAt s p).toNat + 48 ≤ 2 ^ 64) (hf : ∀ y, OpenFoot s p y → ¬ w y)
    (hm : OpenMapped s p) : OpenMapped t p := by
  have fit := hm.fits
  have e : proofAt t p = proofAt s p := h.proofAt_eq hp hpn
  have ev : openingsVec t p = openingsVec s p := by simp only [openingsVec, e]
  have e0 : vecPtr t (openingsVec s p) = vecPtr s (openingsVec s p) :=
    h _ (hq.bytes (by simp only [openingsVec]; addr_omega [hqn])
      (by simp only [openingsVec]; addr_omega [hqn]) hqn)
  have e1 : vecLen t (openingsVec s p) = vecLen s (openingsVec s p) :=
    h _ (hq.bytes (by simp only [openingsVec]; addr_omega [hqn])
      (by simp only [openingsVec]; addr_omega [hqn]) hqn)
  have fb := fit.buf
  refine ⟨by rw [ev, e0, e1]; exact hm.buf, fun k hk ↦ ?_⟩
  rw [ev, e1] at hk
  rw [ev, e0]
  exact h.phaseMapped (fun y hy ↦ hf y (Or.inl (by addr_omega [hy, fb, hk])))
    (by addr_omega [fb, hk]) (fun y hy ↦ hf y (Or.inr ⟨k, hk, hy⟩)) (fit.phases k hk)
    (hm.phases k hk)

/-- `OpeningsAt` reads only `T.proof`. -/
theorem OpeningsAt.of_proof {s : MachineState} {p : Word} {T T' : TState} (h : OpeningsAt s p T)
    (e : T'.proof = T.proof) : OpeningsAt s p T' := by
  exact ⟨by rw [e]; exact h.len, by rw [e]; exact h.phases⟩

/-- The openings of the transcript at `p` are kept by a frame that misses the pointer at `p`, the
`Proof`'s 48 bytes and what the openings read beyond them. -/
theorem DFrame.openingsAt {s t : MachineState} {w : Word → Prop} (h : DFrame s t w) {p : Word}
    {T : TState} (hok : TranscriptOk s p) (hp : Misses w p 8) (hq : Misses w (proofAt s p) 48)
    (hf : ∀ y, OpenFoot s p y → ¬ w y) (fit : OpenFits s p) (hT : OpeningsAt s p T) :
    OpeningsAt t p T :=
  (h.openings hp (by addr_omega [hok.self]) hq (by addr_omega [hok.proof]) hf fit).1 T hT

end Rv64Verifier.Transcript
