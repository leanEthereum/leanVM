import Rv64Verifier.Proofs.Bus.VbbTail5

/-!
# `verify_bus_balance` past the GKR loop: the claims in memory

`ClaimAt` is a `ColumnClaim` (56 bytes: the point's `Vec<E>`, the column, the value) whose point is
a `Vec` allocated since the entry; `ClaimsAt` a `Vec<ColumnClaim>` in registers' words. Both keep
across a step writing the frame (`keepR`), and the claims across `grow_one`, which copies their
bytes to a new buffer (`ClaimsAt.grow`, `growOneCall`).
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript

/-- The `k` elements of a buffer allocated since the entry keep across a step writing the
frame. -/
theorem StepR.eListAt {s v w : MachineState} {A : Word → Prop} (hpre : BusBalancePre s)
    (st : StepR s v w A) (hA : FrameW s A) {p : Word} {m k : Nat} (hb : NewBuf s v p m 8)
    (hk : 24 * k ≤ m) : eListAt w p k = eListAt v p k := by
  refine eListAt_congr fun i hi ↦ ?_
  have hbd : p.toNat + m ≤ 2 ^ 64 := by
    simp only [NewBuf] at hb
    rcases hb.2 with h0 | ⟨b1, b2⟩
    · omega
    · have := st.heap.hi
      have := st.mono
      simp only [heapNext, heapEnd] at *; omega
  have bw (j : Nat) (hj : j + 8 ≤ 24) : w.getMem (p + BitVec.ofNat 64 (24 * i) +
      BitVec.ofNat 64 j) = v.getMem (p + BitVec.ofNat 64 (24 * i) + BitVec.ofNat 64 j) :=
    st.bufWord hpre hA hb (by addr_omega [hbd, hi, hk, hj]) (by addr_omega [hbd, hi, hk, hj])
  exact eAt_congr (by simpa using bw 0 (by omega)) (bw 8 (by omega)) (bw 16 (by omega))

/-- A `Vec<E>` whose header moved (or stayed) and whose elements are kept. -/
theorem _root_.Rv64Verifier.Transcript.NewVecE.transfer {s v w : MachineState} {a b : Word}
    {xs : List E} (h : NewVecE s v a xs) (e0 : w.getMem b = v.getMem a)
    (e8 : w.getMem (b + 8) = v.getMem (a + 8)) (e16 : w.getMem (b + 16) = v.getMem (a + 16))
    (hm : heapNext v ≤ heapNext w)
    (hel : eListAt w (vecPtr v a) (vecLen v a).toNat = eListAt v (vecPtr v a) (vecLen v a).toNat) :
    NewVecE s w b xs := by
  obtain ⟨⟨raw, len⟩, buf, el⟩ := h
  simp only [RawVecOk, Buf, NewBuf, vecCap, vecPtr, vecLen, vecEs] at raw len buf el hel
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;>
    simp only [RawVecOk, Buf, NewBuf, vecCap, vecPtr, vecLen, vecEs, e0, e8, e16]
  · exact ⟨raw.1, raw.2.imp_right fun h' ↦ ⟨h'.1, by omega⟩⟩
  · exact len
  · exact ⟨buf.1, buf.2.imp_right fun h' ↦ ⟨h'.1, by omega⟩⟩
  · rw [hel, el]

theorem _root_.Rv64Verifier.Transcript.NewVecE.bound {s v : MachineState} {a : Word} {xs : List E}
    (h : NewVecE s v a xs) :
    24 * (vecLen v a).toNat ≤ (vecCap v a).toNat * 24 ∧
      NewBuf s v (vecPtr v a) ((vecCap v a).toNat * 24) 8 :=
  ⟨by have := h.vec.len; omega, h.buf⟩

/-- A `Vec<E>` whose header lies in a buffer allocated since the entry keeps what it holds. -/
theorem _root_.Rv64Verifier.Transcript.NewVecE.keepBuf {s v w : MachineState} {A : Word → Prop}
    (hpre : BusBalancePre s) (st : StepR s v w A) (hA : FrameW s A) {a P : Word} {m : Nat}
    {xs : List E} (h : NewVecE s v a xs) (hb : NewBuf s v P m 8) (h1 : P.toNat ≤ a.toNat)
    (h2 : a.toNat + 24 ≤ P.toNat + m) : NewVecE s w a xs := by
  have hbd : P.toNat + m ≤ 2 ^ 64 := by
    simp only [NewBuf] at hb
    rcases hb.2 with h0 | ⟨b1, b2⟩
    · omega
    · have := st.heap.hi
      have := st.mono
      simp only [heapNext, heapEnd] at *; omega
  have hw (j : Nat) (hj : j + 8 ≤ 24) : w.getMem (a + BitVec.ofNat 64 j) =
      v.getMem (a + BitVec.ofNat 64 j) :=
    st.bufWord hpre hA hb (by addr_omega [h1, h2, hj, hbd]) (by addr_omega [h1, h2, hj, hbd])
  obtain ⟨hl, hbuf⟩ := h.bound
  exact h.transfer (by simpa using hw 0 (by omega)) (hw 8 (by omega)) (hw 16 (by omega)) st.mono
    (st.eListAt hpre hA hbuf hl)

/-- The `ColumnClaim` at `a` is `c`, its point a `Vec` allocated since the entry. -/
structure ClaimAt (s t : MachineState) (a : Word) (c : ColumnClaim) : Prop where
  vec : NewVecE s t a c.point
  column : (t.getMem (a + 24)).toNat = c.column
  value : eAt t (a + 32) = c.value

theorem ClaimAt.eq {s t : MachineState} {a : Word} {c : ColumnClaim} (h : ClaimAt s t a c) :
    claimAt t a = c := by
  obtain ⟨col, pt, val⟩ := c
  simp only [claimAt, ColumnClaim.mk.injEq]
  exact ⟨h.column, h.vec.elems, h.value⟩

theorem ClaimAt.keepBuf {s v w : MachineState} {A : Word → Prop} (hpre : BusBalancePre s)
    (st : StepR s v w A) (hA : FrameW s A) {a P : Word} {m : Nat} {c : ColumnClaim}
    (h : ClaimAt s v a c) (hb : NewBuf s v P m 8) (h1 : P.toNat ≤ a.toNat)
    (h2 : a.toNat + 56 ≤ P.toNat + m) : ClaimAt s w a c := by
  have hbd : P.toNat + m ≤ 2 ^ 64 := by
    simp only [NewBuf] at hb
    rcases hb.2 with h0 | ⟨b1, b2⟩
    · omega
    · have := st.heap.hi
      have := st.mono
      simp only [heapNext, heapEnd] at *; omega
  have hw (j : Nat) (hj : j + 8 ≤ 56) : w.getMem (a + BitVec.ofNat 64 j) =
      v.getMem (a + BitVec.ofNat 64 j) :=
    st.bufWord hpre hA hb (by addr_omega [h1, h2, hj, hbd]) (by addr_omega [h1, h2, hj, hbd])
  refine ⟨h.vec.keepBuf hpre st hA hb h1 (by omega), ?_, ?_⟩
  · rw [show a + 24 = a + BitVec.ofNat 64 24 from rfl, hw 24 (by omega)]; exact h.column
  · rw [← h.value]
    have e40 : a + 32 + 8 = a + BitVec.ofNat 64 40 := by rw [BitVec.add_assoc]; rfl
    have e48 : a + 32 + 16 = a + BitVec.ofNat 64 48 := by rw [BitVec.add_assoc]; rfl
    exact eAt_congr (hw 32 (by omega)) (by rw [e40]; exact hw 40 (by omega))
      (by rw [e48]; exact hw 48 (by omega))

/-- A `Vec<ColumnClaim>` in registers' words (capacity, buffer, length) holding `cs`. -/
structure ClaimsAt (s t : MachineState) (cap ptr len : Word) (cs : List ColumnClaim) : Prop where
  le : len.toNat ≤ cap.toNat
  buf : NewBuf s t ptr (56 * cap.toNat) 8
  len : len.toNat = cs.length
  claims : ∀ i (h : i < cs.length), ClaimAt s t (ptr + BitVec.ofNat 64 (56 * i)) cs[i]

theorem ClaimsAt.keepR {s v w : MachineState} {A : Word → Prop} (hpre : BusBalancePre s)
    (st : StepR s v w A) (hA : FrameW s A) {cap ptr len : Word} {cs : List ColumnClaim}
    (h : ClaimsAt s v cap ptr len cs) : ClaimsAt s w cap ptr len cs := by
  have hb := h.buf
  have hm := st.mono
  have hle := h.le
  have hl := h.len
  refine ⟨hle, ?_, hl, fun i hi ↦ ?_⟩
  · simp only [NewBuf] at hb ⊢
    exact ⟨hb.1, hb.2.imp_right fun h' ↦ ⟨h'.1, by omega⟩⟩
  · have hbd : ptr.toNat + 56 * cap.toNat ≤ 2 ^ 64 := by
      simp only [NewBuf] at hb
      rcases hb.2 with h0 | ⟨b1, b2⟩
      · omega
      · have := st.heap.hi
        simp only [heapNext, heapEnd] at *; omega
    exact (h.claims i hi).keepBuf hpre st hA hb (by addr_omega [hbd, hi, hle, hl])
      (by addr_omega [hbd, hi, hle, hl])

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
