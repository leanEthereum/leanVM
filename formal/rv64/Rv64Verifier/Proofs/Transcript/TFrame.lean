import Rv64Verifier.Proofs.Transcript.Frames
import Rv64Verifier.Proofs.Transcript.Contracts

/-!
# What an allocating function writes, and what it keeps

For a function whose precondition is `TPre n k` (the result's `n` bytes at `a0`, the transcript at
`a1`, a stack of `k` bytes): `TW n k s u` is what it may have written by `u` (`TFrame`'s set), and
`TLow k s hi` what a step writing only the stack, `NEXT` and the heap allocated below `hi` writes.
Such frames keep the transcript's reads (`TW.misses`, `TW.ok`) and, for `TLow`, what the
transcript stands for (`TLow.transcriptAt`). `TW.post` is the contract's frame and heap from the
state before the result is written.
-/

namespace Rv64Verifier.Transcript
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.Model

theorem TPre.bounds {n k : Nat} {s : MachineState} (h : TPre n k s) (hk : 16 ≤ k) (hk8 : k % 8 = 0) :
    0xa0000000 + k ≤ (s.getReg .x2).toNat ∧ (s.getReg .x2).toNat ≤ 0xc0000000 ∧
      (s.getReg .x2).toNat % 16 = 0 ∧ (stackLo s k).toNat = (s.getReg .x2).toNat - k := by
  have hm := h.stack.mapped hk hk8
  have hb := h.stack.bounds (by omega) hk8
  omega

/-- What the function may have written by `u`: `TFrame n k`'s set. -/
def TW (n k : Nat) (s u : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x10) n ∨ Within a (s.getReg .x11 + 8) 344 ∨ Within a (stackLo s k) k ∨
    Within a nextAddr 8 ∨ Fresh s u a

theorem TW.mono {n k : Nat} {s u v : MachineState} {a : Word} (h : heapNext u ≤ heapNext v)
    (hw : TW n k s u a) : TW n k s v a := by
  rcases hw with hw | hw | hw | hw | hw
  · exact Or.inl hw
  · exact Or.inr (Or.inl hw)
  · exact Or.inr (Or.inr (Or.inl hw))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hw)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hw.1, Nat.lt_of_lt_of_le hw.2 h⟩)))

theorem TW.miss {n k : Nat} {s u : MachineState} (hhi : heapNext u ≤ heapEnd) {lo : Word} {m : Nat}
    (h0 : Apart lo m (s.getReg .x10) n) (h1 : Apart lo m (s.getReg .x11 + 8) 344)
    (h2 : Apart lo m (stackLo s k) k) (h3 : Outside s lo m) (hn : lo.toNat + m ≤ 2 ^ 64) :
    Misses (TW n k s u) lo m := fun y hy hw ↦ by
  simp only [TW] at hw
  rcases hw with hw | hw | hw | hw | hw <;> addr_omega [hy, hw, h0, h1, h2, h3, hn, hhi]

/-- The transcript's pointer, the `Proof` and the stream miss what the function writes. -/
theorem TW.misses {n k : Nat} {s u : MachineState} (hpre : TPre n k s) (hhi : heapNext u ≤ heapEnd) :
    Misses (TW n k s u) (s.getReg .x11) 8 ∧ Misses (TW n k s u) (proofAt s (s.getReg .x11)) 48 ∧
      Misses (TW n k s u) (streamPtr s (s.getReg .x11)) (24 * streamLen s (s.getReg .x11)) := by
  have hS := hpre.self.self
  have hP := hpre.self.proof
  have hpa := hpre.self.apart
  refine ⟨TW.miss hhi (by addr_omega [hpre.outSelf]) (by addr_omega [hS])
    (by addr_omega [hpre.selfStack]) (by addr_omega [hpre.selfFree]) (by addr_omega [hS]),
    TW.miss hhi (by addr_omega [hpre.proofOut]) (by addr_omega [hpa])
      (by addr_omega [hpre.proofStack]) (by addr_omega [hpre.proofFree]) (by addr_omega [hP]), ?_⟩
  rcases hpre.self.stream with h0 | hB
  · intro y hy; rw [h0] at hy; simp only [Within] at hy; omega
  · exact TW.miss hhi (by addr_omega [hpre.proofOut]) (by addr_omega [hpa])
      (by addr_omega [hpre.proofStack]) hpre.streamFree (by addr_omega [hB])

theorem TW.ok {n k : Nat} {s u : MachineState} (hpre : TPre n k s) (hhi : heapNext u ≤ heapEnd)
    (F : DFrame s u (TW n k s u)) : TranscriptOk u (s.getReg .x11) :=
  F.transcriptOk hpre.self (TW.misses hpre hhi).1 (TW.misses hpre hhi).2.1

theorem TW.proofApart {n k : Nat} {s u : MachineState} (hpre : TPre n k s)
    (hhi : heapNext u ≤ heapEnd) (F : DFrame s u (TW n k s u)) {lo : Word} {m : Nat}
    (ha : ProofApart s (s.getReg .x11) lo m) : ProofApart u (s.getReg .x11) lo m :=
  F.proofApart (TW.misses hpre hhi).1 (by addr_omega [hpre.self.self]) (TW.misses hpre hhi).2.1
    (by addr_omega [hpre.self.proof]) ha

/-- What a step that writes only the stack, `NEXT` and the heap allocated below `hi` writes. -/
def TLow (k : Nat) (s : MachineState) (hi : Nat) (a : Word) : Prop :=
  Within a (stackLo s k) k ∨ Within a nextAddr 8 ∨ (heapNext s ≤ a.toNat ∧ a.toNat < hi)

theorem TLow.toW {n k : Nat} {s v : MachineState} {hi : Nat} {a : Word} (h : hi ≤ heapNext v)
    (hw : TLow k s hi a) : TW n k s v a := by
  rcases hw with hw | hw | hw
  · exact Or.inr (Or.inr (Or.inl hw))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hw)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hw.1, Nat.lt_of_lt_of_le hw.2 h⟩)))

/-- A step that writes only the result, the stack, `NEXT` and the heap allocated keeps the
transcript. -/
theorem TLow.transcriptAt' {n k : Nat} {s u v : MachineState} (hpre : TPre n k s) {hi : Nat}
    (hhi : hi ≤ heapEnd) (hu : heapNext u ≤ heapEnd) (F : DFrame s u (TW n k s u))
    (G : DFrame u v fun a ↦ Within a (s.getReg .x10) n ∨ TLow k s hi a) {T : TState}
    (hT : TranscriptAt u (s.getReg .x11) T) : TranscriptAt v (s.getReg .x11) T := by
  have hS := hpre.self.self
  have hP := hpre.self.proof
  have hok := TW.ok hpre hu F
  obtain ⟨e0, e1, e2⟩ := F.stream' (TW.misses hpre hu).1 (by addr_omega [hS])
    (TW.misses hpre hu).2.1 (by addr_omega [hP])
  have ml (lo : Word) (m : Nat) (h0 : Apart lo m (s.getReg .x10) n)
      (h2 : Apart lo m (stackLo s k) k) (h3 : Outside s lo m)
      (hn : lo.toNat + m ≤ 2 ^ 64) : Misses (fun a ↦ Within a (s.getReg .x10) n ∨ TLow k s hi a) lo m :=
    fun y hy hw ↦ by rcases hw with hw | hw | hw | hw <;> addr_omega [hy, hw, h0, h2, h3, hn, hhi]
  have mq : Misses (fun a ↦ Within a (s.getReg .x10) n ∨ TLow k s hi a)
      (proofAt s (s.getReg .x11)) 48 :=
    ml _ _ (by addr_omega [hpre.proofOut]) (by addr_omega [hpre.proofStack])
      (by addr_omega [hpre.proofFree]) (by addr_omega [hP])
  refine G.transcriptAt hT hok (ml _ _ (by addr_omega [hpre.outSelf]) (by addr_omega [hpre.selfStack])
    (by addr_omega [hpre.selfFree]) (by addr_omega [hS])) (by rw [e0]; exact mq) ?_
    (ml _ _ (by addr_omega [hpre.outSelf, hS]) (by addr_omega [hpre.selfStack, hS])
      (by addr_omega [hpre.selfFree, hS]) (by addr_omega [hS]))
  rw [e1, e2]
  rcases hpre.self.stream with h0 | hB
  · intro y hy; rw [h0] at hy; simp only [Within] at hy; omega
  · exact ml _ _ (by addr_omega [hpre.proofOut]) (by addr_omega [hpre.proofStack]) hpre.streamFree
      (by addr_omega [hB])

/-- A step that writes only the stack, `NEXT` and the heap allocated keeps the transcript. -/
theorem TLow.transcriptAt {n k : Nat} {s u v : MachineState} (hpre : TPre n k s) {hi : Nat}
    (hhi : hi ≤ heapEnd) (hu : heapNext u ≤ heapEnd) (F : DFrame s u (TW n k s u))
    (G : DFrame u v (TLow k s hi)) {T : TState} (hT : TranscriptAt u (s.getReg .x11) T) :
    TranscriptAt v (s.getReg .x11) T :=
  TLow.transcriptAt' hpre hhi hu F (G.mono fun _ h ↦ Or.inr h) hT

theorem ProofApart.mono' {s : MachineState} {p lo lo' : Word} {n n' : Nat}
    (h : ProofApart s p lo n) (h1 : lo.toNat ≤ lo'.toNat) (h2 : lo'.toNat + n' ≤ lo.toNat + n) :
    ProofApart s p lo' n' := by
  obtain ⟨ha, hb⟩ := h
  exact ⟨by addr_omega [ha, h1, h2], by addr_omega [hb, h1, h2]⟩

/-- A callee's `TPre`: its stack `j` bytes below the caller's `sp`, its result in the caller's
frame, the caller's transcript. -/
theorem TPre.callee {n k n' k' : Nat} (j : Nat) {s u : MachineState} (hpre : TPre n k s)
    (hu : HeapOk u) (mono : heapNext s ≤ heapNext u) (F : DFrame s u (TW n k s u))
    (x2 : u.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 j) (x11 : u.getReg .x11 = s.getReg .x11)
    (hj : j + k' ≤ k) (hj16 : j % 16 = 0) (hk' : k' % 8 = 0) (hk : 16 ≤ k) (hk8 : k % 8 = 0)
    (ho : (s.getReg .x2).toNat - j ≤ (u.getReg .x10).toNat ∧
      (u.getReg .x10).toNat + n' ≤ (s.getReg .x2).toNat ∧ (u.getReg .x10).toNat % 8 = 0) :
    TPre n' k' u := by
  have hb := hpre.bounds hk hk8
  have hst := hpre.stack
  have hS := hpre.self.self
  have hP := hpre.self.proof
  have hro := hst.rodata
  have hsl : stackLo u k' = s.getReg .x2 - BitVec.ofNat 64 j - BitVec.ofNat 64 k' := by
    simp only [stackLo, x2]
  obtain ⟨e0, e1, e2⟩ := F.stream' (TW.misses hpre hu.hi).1 (by addr_omega [hS])
    (TW.misses hpre hu.hi).2.1 (by addr_omega [hP])
  have pa (lo : Word) (m : Nat) (h1 : (stackLo s k).toNat ≤ lo.toNat)
      (h2 : lo.toNat + m ≤ (stackLo s k).toNat + k) : ProofApart u (s.getReg .x11) lo m :=
    TW.proofApart hpre hu.hi F (ProofApart.mono' hpre.proofStack h1 h2)
  have hm := hst.mapped hk hk8
  exact {
    heap := hu
    out := by addr_omega [ho, hb, hm, hj]
    self := by rw [x11]; exact TW.ok hpre hu.hi F
    stack := hst.sub j x2 hj hj16 hk' hk hk8
    outStack := by rw [hsl]; addr_omega [ho, hb, hj]
    selfStack := by rw [hsl, x11]; addr_omega [hpre.selfStack, hb, hj]
    outSelf := by rw [x11]; addr_omega [ho, hpre.selfStack, hb, hj]
    proofStack := by rw [hsl, x11]; exact pa _ _ (by addr_omega [hb, hj]) (by addr_omega [hb, hj])
    proofOut := by rw [x11]; exact pa _ _ (by addr_omega [ho, hb, hj]) (by addr_omega [ho, hb, hj])
    outFree := by addr_omega [ho, hb, hst.above, hst.next, hj]
    selfFree := by rw [x11]; addr_omega [hpre.selfFree, mono]
    proofFree := by rw [x11, e0]; addr_omega [hpre.proofFree, mono]
    streamFree := by rw [x11, e1, e2]; addr_omega [hpre.streamFree, mono]
    rodata := hpre.rodata.dframe F fun a ha hw ↦ by
      simp only [TW] at hw
      rcases hw with hw | hw | hw | hw | hw <;>
        addr_omega [ha, hw, hro, hb, hpre.outRodata, hpre.selfRodata, hS, hu.hi]
    outRodata := by addr_omega [ho, hro, hb, hj]
    selfRodata := by rw [x11]; exact hpre.selfRodata }

/-- The contract's frame and heap, and the transcript, from the state before the result is
written. -/
theorem TW.post {n k : Nat} {s v t : MachineState} (hpre : TPre n k s)
    (F : DFrame s v (TW n k s v)) (heap : HeapOk v) (mono : heapNext s ≤ heapNext v)
    (f : MemFrame v t (s.getReg .x10) n) :
    HeapOk t ∧ heapNext s ≤ heapNext t ∧ DFrame s t (TW n k s t) ∧ heapNext t = heapNext v ∧
      ∀ T, TranscriptAt v (s.getReg .x11) T → TranscriptAt t (s.getReg .x11) T := by
  have ho := hpre.out
  have hof := hpre.outFree
  have hS := hpre.self.self
  have hP := hpre.self.proof
  have hn : heapNext t = heapNext v := by
    simp only [heapNext]; rw [f _ (by addr_omega [ho, hof])]
  have hok := TW.ok hpre heap.hi F
  obtain ⟨e0, e1, e2⟩ := F.stream' (TW.misses hpre heap.hi).1 (by addr_omega [hS])
    (TW.misses hpre heap.hi).2.1 (by addr_omega [hP])
  have mo (lo : Word) (m : Nat) (h0 : Apart lo m (s.getReg .x10) n) (hm : lo.toNat + m ≤ 2 ^ 64) :
      Misses (Within · (s.getReg .x10) n) lo m :=
    fun y hy h ↦ by addr_omega [hy, h, h0, hm]
  refine ⟨⟨hn ▸ heap.lo, hn ▸ heap.hi⟩, hn ▸ mono, ?_, hn, fun T hT ↦ ?_⟩
  · exact (F.mono fun a h ↦ TW.mono (Nat.le_of_eq hn.symm) h).trans (DFrame.of_memFrame f)
      fun a h ↦ Or.inl h
  · have mq : Misses (Within · (s.getReg .x10) n) (proofAt s (s.getReg .x11)) 48 :=
      mo _ _ (by addr_omega [hpre.proofOut]) (by addr_omega [hP])
    refine (DFrame.of_memFrame f).transcriptAt hT hok (mo _ _ (by addr_omega [hpre.outSelf])
      (by addr_omega [hS])) (by rw [e0]; exact mq)
      ?_ (mo _ _ (by addr_omega [hpre.outSelf, hS]) (by addr_omega [hS]))
    rw [e1, e2]
    rcases hpre.self.stream with h0 | hB
    · intro y hy; rw [h0] at hy; simp only [Within] at hy; omega
    · exact mo _ _ (by addr_omega [hpre.proofOut]) (by addr_omega [hB])

/-- The `Vec` a function returns, from its fields. -/
theorem newVec {s v t : MachineState} (hs : HeapOk s) {out cap ptr len : Word}
    (ec : vecCap t out = cap) (ep : vecPtr t out = ptr) (el : vecLen t out = len)
    (hn : heapNext t = heapNext v) (hbuf : NewBuf s v ptr (cap.toNat * 24) 8)
    (hl : len.toNat ≤ cap.toNat) :
    VecOk t out 24 8 ∧ NewBuf s t (vecPtr t out) ((vecCap t out).toNat * 24) 8 := by
  have := hs.lo
  simp only [NewBuf] at hbuf
  refine ⟨⟨?_, by rw [el, ec]; exact hl⟩, ?_⟩
  · simp only [RawVecOk, Buf, ec, ep, hn]; omega
  · simp only [NewBuf, ec, ep, hn]; omega

/-- A buffer of a `Vec` allocated in the heap does not have `-1` as its capacity. -/
theorem cap_ne_errNiche {s v : MachineState} {cap ptr : Word} (hbuf : NewBuf s v ptr (cap.toNat * 24) 8)
    (hhi : heapNext v ≤ heapEnd) : cap ≠ errNiche := fun he ↦ by
  rw [he] at hbuf
  simp only [NewBuf, heapEnd] at hbuf hhi
  have : (errNiche).toNat = 18446744073709551615 := rfl
  rw [this] at hbuf
  omega

end Rv64Verifier.Transcript
