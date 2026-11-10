import Rv64Verifier.Proofs.Transcript.NextScalarsModel
import Rv64Verifier.Proofs.Transcript.Samples
import Rv64Verifier.Proofs.Transcript.ShuntNext
import Rv64Verifier.Blocks.F6

/-!
# `Transcript::next_scalars`

```rust
pub fn next_scalars(&mut self, count: usize) -> Result<Vec<E>, VerifierError> {
    (0..count).map(|_| self.next_scalar()).collect()
}
```

compiled at `0x80004818` (`Blocks/F6.lean`), with `S` the entry's `sp`: a 224-byte frame saving
`ra`, `s0`..`s5`; the residual (`-1`: none) at `S - 224`, the shunt `(transcript, 0, count,
residual)` at `S - 208`, and its first `next` into `S - 152` (`first`). `None` goes to
`0x80004940`: an empty `Vec`, or the residual's error (`leave0`). `Some` allocates 96 bytes, makes
the `Vec` (capacity 4, length 1) at `S - 176` and copies the shunt to `S - 120` (`start`). The loop
head `0x80004908` calls `next` into `S - 88` (`call`); `None` leaves through `0x80004968`
(`leave`); `Some` reserves one more when full (`grow`) and pushes (`push`). `0x80004978` writes
the `Vec`, `0x80004950` the error, and `0x80004984` returns.

`Body s u cap ptr d` is the loop head after `d` scalars: the buffer holds what the mirror's first
`d` reads return and the transcript stands for its state after them, for every transcript the
entry stood for; every write since entry lies in the result, the sponge, the stack, `NEXT` or the
heap allocated (`W`).
-/

namespace Rv64Verifier.Transcript.NextScalars
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F6
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

attribute [local rv_addr] vecPtr vecLen vecCap shuntP shuntR shuntStart shuntEnd

theorem bounds {s : MachineState} (h : NextScalarsPre s) :
    0xa0000000 + nextScalarsStack ≤ (s.getReg .x2).toNat ∧ (s.getReg .x2).toNat ≤ 0xc0000000 ∧
      (s.getReg .x2).toNat % 16 = 0 ∧
      (stackLo s nextScalarsStack).toNat = (s.getReg .x2).toNat - nextScalarsStack := by
  have hm := h.stack.mapped (by decide) (by decide)
  have hb := h.stack.bounds (by decide) (by decide)
  omega

/-- What the function may have written by `u`: `TFrame`'s set. -/
def W (s u : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x10) 24 ∨ Within a (s.getReg .x11 + 8) 344 ∨
    Within a (stackLo s nextScalarsStack) nextScalarsStack ∨ Within a nextAddr 8 ∨ Fresh s u a

theorem W.mono {s u v : MachineState} {a : Word} (h : heapNext u ≤ heapNext v) (hw : W s u a) :
    W s v a := by
  rcases hw with hw | hw | hw | hw | hw
  · exact Or.inl hw
  · exact Or.inr (Or.inl hw)
  · exact Or.inr (Or.inr (Or.inl hw))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hw)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hw.1, Nat.lt_of_lt_of_le hw.2 h⟩)))

theorem miss {s u : MachineState} (hhi : heapNext u ≤ heapEnd) {lo : Word} {n : Nat}
    (h0 : Apart lo n (s.getReg .x10) 24) (h1 : Apart lo n (s.getReg .x11 + 8) 344)
    (h2 : Apart lo n (stackLo s nextScalarsStack) nextScalarsStack) (h3 : Outside s lo n)
    (hn : lo.toNat + n ≤ 2 ^ 64) : Misses (W s u) lo n := fun y hy hw ↦ by
  simp only [W] at hw
  rcases hw with hw | hw | hw | hw | hw <;> addr_omega [hy, hw, h0, h1, h2, h3, hn, hhi]

/-- The transcript's pointer, the `Proof` and the stream miss what the function writes. -/
theorem misses {s u : MachineState} (hpre : NextScalarsPre s) (hhi : heapNext u ≤ heapEnd) :
    Misses (W s u) (s.getReg .x11) 8 ∧ Misses (W s u) (proofAt s (s.getReg .x11)) 48 ∧
      Misses (W s u) (streamPtr s (s.getReg .x11)) (24 * streamLen s (s.getReg .x11)) := by
  have hS := hpre.self.self
  have hP := hpre.self.proof
  have hpa := hpre.self.apart
  refine ⟨miss hhi (by addr_omega [hpre.outSelf]) (by addr_omega [hS])
    (by addr_omega [hpre.selfStack]) (by addr_omega [hpre.selfFree]) (by addr_omega [hS]),
    miss hhi (by addr_omega [hpre.proofOut]) (by addr_omega [hpa]) (by addr_omega [hpre.proofStack])
      (by addr_omega [hpre.proofFree]) (by addr_omega [hP]), ?_⟩
  rcases hpre.self.stream with h0 | hB
  · intro y hy; rw [h0] at hy; simp only [Within] at hy; omega
  · exact miss hhi (by addr_omega [hpre.proofOut]) (by addr_omega [hpa])
      (by addr_omega [hpre.proofStack]) hpre.streamFree (by addr_omega [hB])

theorem ok_of {s u : MachineState} (hpre : NextScalarsPre s) (hhi : heapNext u ≤ heapEnd)
    (F : DFrame s u (W s u)) : TranscriptOk u (s.getReg .x11) :=
  F.transcriptOk hpre.self (misses hpre hhi).1 (misses hpre hhi).2.1

theorem proofApart_of {s u : MachineState} (hpre : NextScalarsPre s) (hhi : heapNext u ≤ heapEnd)
    (F : DFrame s u (W s u)) {lo : Word} {n : Nat} (ha : ProofApart s (s.getReg .x11) lo n) :
    ProofApart u (s.getReg .x11) lo n :=
  F.proofApart (misses hpre hhi).1 (by addr_omega [hpre.self.self]) (misses hpre hhi).2.1
    (by addr_omega [hpre.self.proof]) ha

/-- What a step that writes only the stack, `NEXT` and the heap allocated below `hi` writes. -/
def Low (s : MachineState) (hi : Nat) (a : Word) : Prop :=
  Within a (stackLo s nextScalarsStack) nextScalarsStack ∨ Within a nextAddr 8 ∨
    (heapNext s ≤ a.toNat ∧ a.toNat < hi)

theorem Low.toW {s v : MachineState} {hi : Nat} {a : Word} (h : hi ≤ heapNext v) (hw : Low s hi a) :
    W s v a := by
  rcases hw with hw | hw | hw
  · exact Or.inr (Or.inr (Or.inl hw))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hw)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hw.1, Nat.lt_of_lt_of_le hw.2 h⟩)))

/-- A step that writes only the stack, `NEXT` and the heap allocated keeps the transcript. -/
theorem Low.transcriptAt {s u v : MachineState} (hpre : NextScalarsPre s) {hi : Nat}
    (hhi : hi ≤ heapEnd) (hu : heapNext u ≤ heapEnd) (F : DFrame s u (W s u))
    (G : DFrame u v (Low s hi)) {T : TState} (hT : TranscriptAt u (s.getReg .x11) T) :
    TranscriptAt v (s.getReg .x11) T := by
  have hS := hpre.self.self
  have hP := hpre.self.proof
  have hpa := hpre.self.apart
  have hok := ok_of hpre hu F
  obtain ⟨e0, e1, e2⟩ := F.stream' (misses hpre hu).1 (by addr_omega [hS]) (misses hpre hu).2.1
    (by addr_omega [hP])
  have ml (lo : Word) (n : Nat) (h2 : Apart lo n (stackLo s nextScalarsStack) nextScalarsStack)
      (h3 : Outside s lo n) (hn : lo.toNat + n ≤ 2 ^ 64) : Misses (Low s hi) lo n :=
    fun y hy hw ↦ by rcases hw with hw | hw | hw <;> addr_omega [hy, hw, h2, h3, hn, hhi]
  have mq : Misses (Low s hi) (proofAt s (s.getReg .x11)) 48 :=
    ml _ _ (by addr_omega [hpre.proofStack]) (by addr_omega [hpre.proofFree]) (by addr_omega [hP])
  refine G.transcriptAt hT hok (ml _ _ (by addr_omega [hpre.selfStack]) (by addr_omega [hpre.selfFree])
    (by addr_omega [hS])) (by rw [e0]; exact mq) ?_
    (ml _ _ (by addr_omega [hpre.selfStack, hS]) (by addr_omega [hpre.selfFree, hS])
      (by addr_omega [hS]))
  rw [e1, e2]
  rcases hpre.self.stream with h0 | hB
  · intro y hy; rw [h0] at hy; simp only [Within] at hy; omega
  · exact ml _ _ (by addr_omega [hpre.proofStack]) hpre.streamFree (by addr_omega [hB])

/-! ## The frame's saved registers, and the return -/

/-- The callee-saved registers the function never touches. -/
def keptRegs : List Reg := [.x22, .x23, .x24, .x25, .x26, .x27]

/-- Inside the frame: `sp`, and the saved registers in place. -/
structure Saved (s u : MachineState) : Prop where
  x2 : u.getReg .x2 = s.getReg .x2 - 224
  kept : ∀ r ∈ keptRegs, u.getReg r = s.getReg r
  ra : u.getMem (s.getReg .x2 - 8) = s.getReg .x1
  s0 : u.getMem (s.getReg .x2 - 16) = s.getReg .x8
  s1 : u.getMem (s.getReg .x2 - 24) = s.getReg .x9
  s2 : u.getMem (s.getReg .x2 - 32) = s.getReg .x18
  s3 : u.getMem (s.getReg .x2 - 40) = s.getReg .x19
  s4 : u.getMem (s.getReg .x2 - 48) = s.getReg .x20
  s5 : u.getMem (s.getReg .x2 - 56) = s.getReg .x21

theorem Saved.step {s u v : MachineState} (h : Saved s u) (hS : 56 ≤ (s.getReg .x2).toNat)
    (x2 : v.getReg .x2 = u.getReg .x2) (kept : ∀ r ∈ keptRegs, v.getReg r = u.getReg r)
    (mem : ∀ y : Word, (s.getReg .x2).toNat - 56 ≤ y.toNat → y.toNat + 8 ≤ (s.getReg .x2).toNat →
      v.getMem y = u.getMem y) : Saved s v where
  x2 := x2.trans h.x2
  kept := fun r hr ↦ (kept r hr).trans (h.kept r hr)
  ra := by rw [mem _ (by addr_omega [hS]) (by addr_omega [hS]), h.ra]
  s0 := by rw [mem _ (by addr_omega [hS]) (by addr_omega [hS]), h.s0]
  s1 := by rw [mem _ (by addr_omega [hS]) (by addr_omega [hS]), h.s1]
  s2 := by rw [mem _ (by addr_omega [hS]) (by addr_omega [hS]), h.s2]
  s3 := by rw [mem _ (by addr_omega [hS]) (by addr_omega [hS]), h.s3]
  s4 := by rw [mem _ (by addr_omega [hS]) (by addr_omega [hS]), h.s4]
  s5 := by rw [mem _ (by addr_omega [hS]) (by addr_omega [hS]), h.s5]

theorem Saved.same {s u v : MachineState} (h : Saved s u) (hS : 56 ≤ (s.getReg .x2).toNat)
    (x2 : v.getReg .x2 = u.getReg .x2) (kept : ∀ r ∈ keptRegs, v.getReg r = u.getReg r)
    (mem : ∀ y : Word, v.getMem y = u.getMem y) : Saved s v :=
  h.step hS x2 kept fun y _ _ ↦ mem y

/-- `0x80004984`: the saved registers back, return. -/
theorem epilogue {s u : MachineState} (hpre : NextScalarsPre s) (hpc : u.pc = 0x80004984)
    (h : Saved s u) :
    ∃ t, Reaches Image.code u t ∧ t.pc = returnAddress s ∧ Preserves s t ∧
      ∀ a, t.getMem a = u.getMem a := by
  have hb := bounds hpre
  obtain ⟨t, hr, h₁⟩ := Sym.BlockSpec.reaches b80004984_spec hpc (by
    rv_eval [h.x2]
    and_intros <;> valid_access hpre.stack.valid [hb])
  have k := b80004984_keeps h₁
  have pc := b80004984_pc h₁
  have y2 := b80004984_x2 h₁
  have y8 := b80004984_x8 h₁
  have y9 := b80004984_x9 h₁
  have y18 := b80004984_x18 h₁
  have y19 := b80004984_x19 h₁
  have y20 := b80004984_x20 h₁
  have y21 := b80004984_x21 h₁
  rv_eval [h.x2] at pc y2 y8 y9 y18 y19 y20 y21
  refine ⟨t, hr, by rw [pc, h.ra, returnAddress_eq], ?_, b80004984_mem_same h₁⟩
  intro r hr
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact y2
  · rw [y8, h.s0]
  · rw [y9, h.s1]
  · rw [y18, h.s2]
  · rw [y19, h.s3]
  · rw [y20, h.s4]
  · rw [y21, h.s5]
  all_goals rw [k _ (by decide), h.kept _ (by decide)]

/-- `0x80004978`: the `Vec` (`a0`, `a1`, `s3`) out, return. -/
theorem finish_ok {s u : MachineState} (hpre : NextScalarsPre s) (hpc : u.pc = 0x80004978)
    (h : Saved s u) (x8 : u.getReg .x8 = s.getReg .x10) :
    ∃ t, Reaches Image.code u t ∧ t.pc = returnAddress s ∧ Preserves s t ∧
      vecCap t (s.getReg .x10) = u.getReg .x10 ∧ vecPtr t (s.getReg .x10) = u.getReg .x11 ∧
      vecLen t (s.getReg .x10) = u.getReg .x19 ∧ MemFrame u t (s.getReg .x10) 24 := by
  have hb := bounds hpre
  have ho := hpre.out
  have hos := hpre.outStack
  obtain ⟨v, hr, h₁⟩ := Sym.BlockSpec.reaches b80004978_spec hpc (by
    rv_eval [x8]
    and_intros <;> (refine Region.valid ho ?_ ?_ ?_ <;> addr_omega [ho]))
  have k := b80004978_keeps h₁
  have m0 := b80004978_m_x8_0 h₁
  have m8 := b80004978_m_x8_8 h₁
  have m16 := b80004978_m_x8_16 h₁
  have f := b80004978_frame h₁ (by rw [x8]; addr_omega [ho])
  rw [x8] at m0 m8 m16 f
  obtain ⟨t, hr', pc, pres, hm⟩ := epilogue hpre (b80004978_pc h₁)
    (h.step (by addr_omega [hb]) (k .x2 (by decide)) (fun r hr ↦ k r (mem_of_mem hr _))
      fun y h1 h2 ↦ f y (by addr_omega [h1, h2, hb, ho, hos]))
  exact ⟨t, hr.trans hr', pc, pres, by rw [vecCap, hm, m0], by rw [vecPtr, hm, m8],
    by rw [vecLen, hm, m16], fun a ha ↦ (hm a).trans (f a ha)⟩

/-- `0x80004950`: the error out (`-1` in the capacity), return. -/
theorem finish_err {s u : MachineState} (hpre : NextScalarsPre s) (hpc : u.pc = 0x80004950)
    (h : Saved s u) (x8 : u.getReg .x8 = s.getReg .x10) :
    ∃ t, Reaches Image.code u t ∧ t.pc = returnAddress s ∧ Preserves s t ∧
      vecCap t (s.getReg .x10) = errNiche ∧ MemFrame u t (s.getReg .x10) 24 := by
  have hb := bounds hpre
  have ho := hpre.out
  have hos := hpre.outStack
  obtain ⟨v, hr, h₁⟩ := Sym.BlockSpec.reaches b80004950_spec hpc (by
    rv_eval [x8, h.x2]
    and_intros <;> first
      | valid_access hpre.stack.valid [hb]
      | (refine Region.valid ho ?_ ?_ ?_ <;> addr_omega [ho]))
  have k := b80004950_keeps h₁
  have m0 := b80004950_m_x8_0 h₁
  have f := b80004950_frame h₁ (by rw [x8]; addr_omega [ho])
  rw [x8] at m0 f
  obtain ⟨t, hr', pc, pres, hm⟩ := epilogue hpre (b80004950_pc h₁)
    (h.step (by addr_omega [hb]) (k .x2 (by decide)) (fun r hr ↦ k r (mem_of_mem hr _))
      fun y h1 h2 ↦ f y (by addr_omega [h1, h2, hb, ho, hos]))
  exact ⟨t, hr.trans hr', pc, pres, by rw [vecCap, hm, m0]; rfl, fun a ha ↦ (hm a).trans (f a ha)⟩

/-- The contract's frame and heap, and the transcript, from the state before the result is
written. -/
theorem post_of {s v t : MachineState} (hpre : NextScalarsPre s) (F : DFrame s v (W s v))
    (heap : HeapOk v) (mono : heapNext s ≤ heapNext v) (f : MemFrame v t (s.getReg .x10) 24) :
    HeapOk t ∧ heapNext s ≤ heapNext t ∧ TFrame 24 nextScalarsStack s t ∧
      heapNext t = heapNext v ∧
      ∀ T, TranscriptAt v (s.getReg .x11) T → TranscriptAt t (s.getReg .x11) T := by
  have ho := hpre.out
  have hof := hpre.outFree
  have hS := hpre.self.self
  have hP := hpre.self.proof
  have hn : heapNext t = heapNext v := by
    simp only [heapNext]; rw [f _ (by addr_omega [ho, hof])]
  have hok := ok_of hpre heap.hi F
  obtain ⟨e0, e1, e2⟩ := F.stream' (misses hpre heap.hi).1 (by addr_omega [hS])
    (misses hpre heap.hi).2.1 (by addr_omega [hP])
  have mo (lo : Word) (n : Nat) (h0 : Apart lo n (s.getReg .x10) 24) (hn : lo.toNat + n ≤ 2 ^ 64) :
      Misses (Within · (s.getReg .x10) 24) lo n :=
    fun y hy h ↦ by addr_omega [hy, h, h0, hn]
  refine ⟨⟨hn ▸ heap.lo, hn ▸ heap.hi⟩, hn ▸ mono, ?_, hn, fun T hT ↦ ?_⟩
  · exact (F.mono fun a h ↦ W.mono (Nat.le_of_eq hn.symm) h).trans (DFrame.of_memFrame f)
      fun a h ↦ Or.inl h
  · have mq : Misses (Within · (s.getReg .x10) 24) (proofAt s (s.getReg .x11)) 48 :=
      mo _ _ (by addr_omega [hpre.proofOut]) (by addr_omega [hP])
    refine (DFrame.of_memFrame f).transcriptAt hT hok (mo _ _ (by addr_omega [hpre.outSelf])
      (by addr_omega [hS])) (by rw [e0]; exact mq)
      ?_ (mo _ _ (by addr_omega [hpre.outSelf, hS]) (by addr_omega [hS]))
    rw [e1, e2]
    rcases hpre.self.stream with h0 | hB
    · intro y hy; rw [h0] at hy; simp only [Within] at hy; omega
    · exact mo _ _ (by addr_omega [hpre.proofOut]) (by addr_omega [hB])

/-! ## `GenericShunt::next` -/

/-- The shunt's precondition, for the result at `o` and the shunt at `h`, both in the frame
above the residual, apart. -/
theorem shunt_pre {s u : MachineState} (hpre : NextScalarsPre s) {o h : Word}
    (x2 : u.getReg .x2 = s.getReg .x2 - 224) (x10 : u.getReg .x10 = o) (x11 : u.getReg .x11 = h)
    (ho : (s.getReg .x2).toNat - 208 ≤ o.toNat ∧ o.toNat + 32 ≤ (s.getReg .x2).toNat - 56 ∧
      o.toNat % 8 = 0)
    (hh : (s.getReg .x2).toNat - 208 ≤ h.toNat ∧ h.toNat + 32 ≤ (s.getReg .x2).toNat - 56 ∧
      h.toNat % 8 = 0)
    (hoh : o.toNat + 32 ≤ h.toNat ∨ h.toNat + 32 ≤ o.toNat)
    (hP : u.getMem h = s.getReg .x11) (hR : u.getMem (h + 24) = s.getReg .x2 - 224)
    (heap : heapNext u ≤ heapEnd) (F : DFrame s u (W s u)) : ShuntNextPre u := by
  have hb := bounds hpre
  have hS := hpre.self.self
  have hro := hpre.stack.rodata
  have hss := hpre.selfStack
  have hsm := hpre.stack.mapped (by decide) (by decide)
  have eP : shuntP u = s.getReg .x11 := by simp only [shuntP, x11, hP]
  have eR : shuntR u = s.getReg .x2 - 224 := by simp only [shuntR, x11, hR]
  have hps := hpre.proofStack
  have pa (lo : Word) (n : Nat) (h1 : (stackLo s nextScalarsStack).toNat ≤ lo.toNat)
      (h2 : lo.toNat + n ≤ (stackLo s nextScalarsStack).toNat + nextScalarsStack) :
      ProofApart u (s.getReg .x11) lo n :=
    proofApart_of hpre heap F (ShuntNext.ProofApart.mono hps h1 h2)
  have hst : stackLo u shuntNextStack = s.getReg .x2 - 224 - BitVec.ofNat 64 shuntNextStack := by
    simp only [stackLo, x2]
  have pS : ProofApart u (s.getReg .x11) (stackLo u shuntNextStack) shuntNextStack := by
    rw [hst]; exact pa _ _ (by addr_omega [hb]) (by addr_omega [hb])
  have pO : ProofApart u (s.getReg .x11) o 32 := pa _ _ (by addr_omega [ho, hb]) (by addr_omega [ho, hb])
  have pH : ProofApart u (s.getReg .x11) h 32 := pa _ _ (by addr_omega [hh, hb]) (by addr_omega [hh, hb])
  have pR : ProofApart u (s.getReg .x11) (s.getReg .x2 - 224) 16 :=
    pa _ _ (by addr_omega [hb]) (by addr_omega [hb])
  have rd : RodataOk u := hpre.rodata.dframe F fun a ha hw ↦ by
    simp only [W] at hw
    rcases hw with hw | hw | hw | hw | hw <;>
      addr_omega [ha, hw, hro, hb, hpre.outRodata, hpre.selfRodata, hS, heap]
  exact {
    out := by rw [x10]; addr_omega [ho, hb, hsm]
    shunt := by rw [x11]; addr_omega [hh, hb, hsm]
    residual := by rw [eR]; addr_omega [hb, hsm]
    self := by rw [eP]; exact ok_of hpre heap F
    stack := hpre.stack.sub 224 x2 (by simp only [nextScalarsStack]; omega) (by decide) (by decide)
      (by decide) (by decide)
    outStack := by rw [hst, x10]; addr_omega [ho, hb]
    shuntStack := by rw [hst, x11]; addr_omega [hh, hb]
    residualStack := by rw [hst, eR]; addr_omega [hb]
    selfStack := by rw [hst, eP]; addr_omega [hss, hb]
    outShunt := by rw [x10, x11]; addr_omega [hoh]
    outResidual := by rw [x10, eR]; addr_omega [ho, hb]
    outSelf := by rw [x10, eP]; addr_omega [ho, hss, hb]
    shuntResidual := by rw [x11, eR]; addr_omega [hh, hb]
    shuntSelf := by rw [x11, eP]; addr_omega [hh, hss, hb]
    residualSelf := by rw [eR, eP]; addr_omega [hss, hb]
    proofStack := by rw [eP]; exact pS
    proofOut := by rw [eP, x10]; exact pO
    proofShunt := by rw [eP, x11]; exact pH
    proofResidual := by rw [eP, eR]; exact pR
    rodata := rd
    outRodata := by rw [x10]; addr_omega [ho, hro, hb]
    shuntRodata := by rw [x11]; addr_omega [hh, hro, hb]
    residualRodata := by rw [eR]; addr_omega [hro, hb]
    selfRodata := by rw [eP]; exact hpre.selfRodata }

/-! ## The first `next` -/

/-- After the first `next`, at `0x80004868`: its tag at `S - 152`, its value at `S - 144`. -/
structure First (s u : MachineState) : Prop where
  saved : Saved s u
  x8 : u.getReg .x8 = s.getReg .x10
  x18 : u.getReg .x18 = 0xffffffffffffffff
  shP : u.getMem (s.getReg .x2 - 208) = s.getReg .x11
  shStart : u.getMem (s.getReg .x2 - 200) = if 0 < (s.getReg .x12).toNat then 0 + 1 else 0
  shEnd : u.getMem (s.getReg .x2 - 192) = s.getReg .x12
  shR : u.getMem (s.getReg .x2 - 184) = s.getReg .x2 - 224
  past : ¬ 0 < (s.getReg .x12).toNat → u.getMem (s.getReg .x2 - 152) = 0
  kept : u.getMem (s.getReg .x2 - 152) ≠ 0 ∨ ¬ 0 < (s.getReg .x12).toNat →
    u.getMem (s.getReg .x2 - 224) = 0xffffffffffffffff
  heap : HeapOk u
  next : heapNext u = heapNext s
  frame : DFrame s u (W s u)
  value : ∀ T, TranscriptAt s (s.getReg .x11) T →
    if 0 < (s.getReg .x12).toNat then
      match TM.nextScalar.run T with
      | some (x, T') => u.getMem (s.getReg .x2 - 152) = 1 ∧ eAt u (s.getReg .x2 - 144) = x ∧
          TranscriptAt u (s.getReg .x11) T'
      | none => u.getMem (s.getReg .x2 - 152) = 0 ∧ u.getMem (s.getReg .x2 - 224) = 3
    else TranscriptAt u (s.getReg .x11) T

set_option maxHeartbeats 1000000 in
/-- The frame, the residual, the shunt, and its first `next`. -/
theorem first (hN : ShuntNextSpec) {s : MachineState} (hpc : s.pc = 0x80004818)
    (hpre : NextScalarsPre s) :
    ∃ u, Reaches Image.code s u ∧ ((u.pc = 0x80004868 ∧ First s u) ∨ Dead Image.code u) := by
  have hb := bounds hpre
  have hS := hpre.self.self
  have hss := hpre.selfStack
  have hsf := hpre.selfFree
  have hst := hpre.stack
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80004818_spec hpc (by
    rv_eval []
    and_intros <;> valid_access hst.valid [hb])
  have k₁ := b80004818_keeps h₁
  have x2₁ := b80004818_x2 h₁
  have x10₁ := b80004818_x10 h₁
  have x11₁ := b80004818_x11 h₁
  have f₁ := b80004818_frame h₁ (by addr_omega [hb])
  have nx₁ : heapNext t₁ = heapNext s := by
    simp only [heapNext]; rw [f₁ _ (by addr_omega [hst.next, hb])]
  have L₁ : DFrame s t₁ (Low s (heapNext s)) :=
    (DFrame.of_memFrame f₁).mono fun a ha ↦ Or.inl (by addr_omega [ha, hb])
  have F₁ : DFrame s t₁ (W s t₁) := L₁.mono fun a ha ↦ Low.toW (Nat.le_of_eq nx₁.symm) ha
  have m208 := b80004818_m_x2_n208 h₁
  have m200 := b80004818_m_x2_n200 h₁
  have m192 := b80004818_m_x2_n192 h₁
  have m184 := b80004818_m_x2_n184 h₁
  have m224 := b80004818_m_x2_n224 h₁
  have e24 : s.getReg .x2 - 208 + 24 = s.getReg .x2 - 184 := by bv_omega
  have e16 : s.getReg .x2 - 208 + 16 = s.getReg .x2 - 192 := by bv_omega
  have e8 : s.getReg .x2 - 208 + 8 = s.getReg .x2 - 200 := by bv_omega
  have hsp : ShuntNextPre t₁ := shunt_pre hpre x2₁ x10₁ x11₁ (by addr_omega [hb]) (by addr_omega [hb])
    (by addr_omega [hb]) m208 (by rw [e24]; exact m184) (by rw [nx₁]; exact hpre.heap.hi) F₁
  obtain ⟨w, hr₂, ⟨hpc₂, hpres₂, hpost₂⟩ | hd⟩ := hN.call hr₁ (b80004818_pc h₁) hsp
  swap
  · exact ⟨_, hr₂, Or.inr hd⟩
  have eP : shuntP t₁ = s.getReg .x11 := by simp only [shuntP, x11₁, m208]
  have eR : shuntR t₁ = s.getReg .x2 - 224 := by simp only [shuntR, x11₁, e24, m184]
  have eSt : (shuntStart t₁).toNat = 0 := by simp only [shuntStart, x11₁, e8, m200]; rfl
  have eEn : shuntEnd t₁ = s.getReg .x12 := by simp only [shuntEnd, x11₁, e16, m192]
  have G := hpost₂.frame
  rw [x10₁, x11₁, eR, eP] at G
  simp only [stackLo, x2₁] at G
  have hG (y : Word) (hy : ∀ i < 8, ¬ (Within (y + BitVec.ofNat 64 i) (s.getReg .x2 - 152) 32 ∨
      Within (y + BitVec.ofNat 64 i) (s.getReg .x2 - 208 + 8) 8 ∨
      Within (y + BitVec.ofNat 64 i) (s.getReg .x2 - 224) 16 ∨
      Within (y + BitVec.ofNat 64 i) (s.getReg .x11 + 8) 344 ∨
      Within (y + BitVec.ofNat 64 i) (s.getReg .x2 - 224 - BitVec.ofNat 64 shuntNextStack)
        shuntNextStack)) : w.getMem y = t₁.getMem y := G y hy
  have slot (y : Word) (h1 : (s.getReg .x2).toNat - 56 ≤ y.toNat)
      (h2 : y.toNat + 8 ≤ (s.getReg .x2).toNat) : w.getMem y = t₁.getMem y :=
    hG y fun i hi h ↦ by rcases h with h | h | h | h | h <;> addr_omega [h, hi, h1, h2, hb, hss, hS]
  have frm (y : Word) (h1 : (s.getReg .x2).toNat - 208 ≤ y.toNat)
      (h2 : y.toNat + 8 ≤ (s.getReg .x2).toNat - 152)
      (h3 : y.toNat + 8 ≤ (s.getReg .x2).toNat - 200 ∨ (s.getReg .x2).toNat - 192 ≤ y.toNat) :
      w.getMem y = t₁.getMem y :=
    hG y fun i hi h ↦ by
      rcases h with h | h | h | h | h <;> addr_omega [h, hi, h1, h2, h3, hb, hss, hS]
  have nxw : heapNext w = heapNext t₁ := by
    have e := hG nextAddr fun i hi h ↦ by
      rcases h with h | h | h | h | h <;> addr_omega [h, hi, hst.next, hb, hsf, hS]
    simp only [heapNext, e]
  have Fw : DFrame s w (W s w) :=
    (F₁.mono fun a h ↦ W.mono (Nat.le_of_eq nxw.symm) h).trans G fun a h ↦ by
      rcases h with h | h | h | h | h
      · exact Or.inr (Or.inr (Or.inl (by addr_omega [h, hb])))
      · exact Or.inr (Or.inr (Or.inl (by addr_omega [h, hb])))
      · exact Or.inr (Or.inr (Or.inl (by addr_omega [h, hb])))
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl (by addr_omega [h, hb])))
  have Sv : Saved s t₁ := {
    x2 := x2₁
    kept := fun r hr ↦ k₁ r (mem_of_mem hr _)
    ra := b80004818_m_x2_n8 h₁
    s0 := b80004818_m_x2_n16 h₁
    s1 := b80004818_m_x2_n24 h₁
    s2 := b80004818_m_x2_n32 h₁
    s3 := b80004818_m_x2_n40 h₁
    s4 := b80004818_m_x2_n48 h₁
    s5 := b80004818_m_x2_n56 h₁ }
  have hstart := hpost₂.start
  have hpast := hpost₂.past
  have hkept := hpost₂.kept
  rw [x11₁, e8, eEn] at hstart
  rw [eEn, eSt, x10₁] at hpast
  rw [eEn, eSt, x10₁, eR, m224] at hkept
  rw [eSt] at hstart
  refine ⟨w, hr₂, Or.inl ⟨by rw [hpc₂, returnAddress_eq, b80004818_x1 h₁]; decide, {
    saved := Sv.step (by addr_omega [hb]) (hpres₂.reg .x2 (by decide))
      (fun r hr ↦ hpres₂.reg r (mem_of_mem hr _))
      slot
    x8 := by rw [hpres₂.reg .x8 (by decide), b80004818_x8 h₁]
    x18 := by rw [hpres₂.reg .x18 (by decide), b80004818_x18 h₁]
    shP := by rw [frm _ (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb]), m208]
    shStart := by
      rw [hstart]
      have : (shuntStart t₁) = 0 := BitVec.eq_of_toNat_eq eSt
      rw [this]
    shEnd := by rw [frm _ (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb]), m192]
    shR := by rw [frm _ (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb]), m184]
    past := hpast
    kept := hkept
    heap := ⟨by rw [nxw, nx₁]; exact hpre.heap.lo, by rw [nxw, nx₁]; exact hpre.heap.hi⟩
    next := nxw.trans nx₁
    frame := Fw
    value := fun T hT ↦ by
      have hT₁ := Low.transcriptAt hpre hpre.heap.hi hpre.heap.hi (DFrame.refl _ _) L₁ hT
      have hv := hpost₂.value T (by rw [eP]; exact hT₁)
      rw [eSt, eEn, eP, x10₁, eR] at hv
      rw [show s.getReg .x2 - 152 + 8 = s.getReg .x2 - 144 by bv_omega] at hv
      exact hv }⟩⟩

theorem nextScalars_zero (T : TState) : (TM.nextScalars 0).run T = some ([], T) := rfl

/-- The `Vec` the function returns, from its fields. -/
theorem newVec {s v t : MachineState} (hs : HeapOk s) {cap ptr len : Word}
    (ec : vecCap t (s.getReg .x10) = cap) (ep : vecPtr t (s.getReg .x10) = ptr)
    (el : vecLen t (s.getReg .x10) = len) (hn : heapNext t = heapNext v)
    (hbuf : NewBuf s v ptr (cap.toNat * 24) 8) (hl : len.toNat ≤ cap.toNat) :
    VecOk t (s.getReg .x10) 24 8 ∧ NewBuf s t (vecPtr t (s.getReg .x10))
      ((vecCap t (s.getReg .x10)).toNat * 24) 8 := by
  have := hs.lo
  simp only [NewBuf] at hbuf
  refine ⟨⟨?_, by rw [el, ec]; exact hl⟩, ?_⟩
  · simp only [RawVecOk, Buf, ec, ep, hn]; omega
  · simp only [NewBuf, ec, ep, hn]; omega

set_option maxHeartbeats 1000000 in
/-- `None` from the first `next`: an empty `Vec`, or the residual's error. -/
theorem leave0 {s u : MachineState} (hpre : NextScalarsPre s) (hpc : u.pc = 0x80004868)
    (h : First s u) (htag : u.getMem (s.getReg .x2 - 152) = 0) :
    ∃ t, Reaches Image.code u t ∧ t.pc = returnAddress s ∧ Preserves s t ∧
      NextScalarsPost s t := by
  have hb := bounds hpre
  have hS : 56 ≤ (s.getReg .x2).toNat := by addr_omega [hb]
  have e72 : u.getReg .x2 + 72 = s.getReg .x2 - 152 := by rw [h.saved.x2]; bv_omega
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80004868_spec hpc (by
    rv_eval [h.saved.x2]
    valid_access hpre.stack.valid [hb])
  have k₁ := b80004868_keeps h₁
  have hm₁ := b80004868_mem_same h₁
  have x2₁ : u₁.getReg .x2 = s.getReg .x2 - 224 := (k₁ .x2 (by decide)).trans h.saved.x2
  obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80004940_spec
    (b80004868_pc_taken h₁ (by rw [e72]; exact htag)) (by
      rv_eval [x2₁]
      valid_access hpre.stack.valid [hb])
  have k₂ := b80004940_keeps h₂
  have hm₂ := b80004940_mem_same h₂
  have S₂ : Saved s u₂ := (h.saved.same hS (k₁ .x2 (by decide)) (fun r hr ↦ k₁ r (mem_of_mem hr _))
    hm₁).same hS (k₂ .x2 (by decide)) (fun r hr ↦ k₂ r (mem_of_mem hr _)) hm₂
  have x8₂ : u₂.getReg .x8 = s.getReg .x10 := by rw [k₂ .x8 (by decide), k₁ .x8 (by decide), h.x8]
  have hm (a : Word) : u₂.getMem a = u.getMem a := by rw [hm₂, hm₁]
  have nx₂ : heapNext u₂ = heapNext u := by simp only [heapNext, hm]
  have F₂ : DFrame s u₂ (W s u₂) :=
    (h.frame.mono fun a h ↦ W.mono (Nat.le_of_eq nx₂.symm) h).trans (DFrame.of_same hm _)
      fun _ h ↦ h
  have heap₂ : HeapOk u₂ := ⟨nx₂ ▸ h.heap.lo, nx₂ ▸ h.heap.hi⟩
  have mono₂ : heapNext s ≤ heapNext u₂ := by rw [nx₂, h.next]
  have tr₂ (T : TState) (hT : TranscriptAt u (s.getReg .x11) T) : TranscriptAt u₂ (s.getReg .x11) T :=
    Low.transcriptAt hpre h.heap.hi h.heap.hi h.frame
      (DFrame.of_same hm (Low s (heapNext u))) hT
  have hres : u₁.getMem (u₁.getReg .x2) = u.getMem (s.getReg .x2 - 224) := by rw [x2₁, hm₁]
  have x18₁ : u₁.getReg .x18 = 0xffffffffffffffff := by rw [k₁ .x18 (by decide), h.x18]
  by_cases hr : u.getMem (s.getReg .x2 - 224) = 0xffffffffffffffff
  · obtain ⟨t, hr₃, pc, pres, ec, ep, el, f⟩ := finish_ok hpre
      (b80004940_pc_taken h₂ (by rw [hres, x18₁]; exact hr)) S₂ x8₂
    obtain ⟨heapt, monot, frt, nxt, trt⟩ := post_of hpre F₂ heap₂ mono₂ f
    have x10₂ : u₂.getReg .x10 = 0 := by rw [k₂ .x10 (by decide), b80004868_x10 h₁, e72, htag]
    rw [x10₂] at ec
    rw [b80004940_x11 h₂] at ep
    rw [b80004940_x19 h₂] at el
    obtain ⟨hvec, hnb⟩ := newVec (v := u₂) hpre.heap ec ep el nxt (by simp [NewBuf]) (by simp)
    refine ⟨t, (hr₁.trans hr₂).trans hr₃, pc, pres, heapt, monot, fun T hT ↦ ?_, frt,
      fun _ ↦ ⟨hvec, hnb⟩⟩
    have hv := h.value T hT
    by_cases hc : 0 < (s.getReg .x12).toNat
    · rw [ite_eq_left hc] at hv
      generalize TM.nextScalar.run T = o at hv
      rcases o with _ | ⟨x, T'⟩
      · exact absurd (hv.2.symm.trans hr) (by decide)
      · exact absurd (hv.1.symm.trans htag) (by decide)
    · rw [ite_eq_right hc] at hv
      rw [show (s.getReg .x12).toNat = 0 by omega, nextScalars_zero]
      refine ⟨by rw [ec]; decide, ⟨hvec, hnb, ?_⟩, trt T (tr₂ T hv)⟩
      simp only [vecEs, el]
      rfl
  · obtain ⟨t, hr₃, pc, pres, ec, f⟩ := finish_err hpre
      (b80004940_pc_not_taken h₂ (by rw [hres, x18₁]; exact hr)) S₂ x8₂
    obtain ⟨heapt, monot, frt, -, -⟩ := post_of hpre F₂ heap₂ mono₂ f
    refine ⟨t, (hr₁.trans hr₂).trans hr₃, pc, pres, heapt, monot, fun T hT ↦ ?_, frt,
      fun hne ↦ absurd ec hne⟩
    have hc : 0 < (s.getReg .x12).toNat := by
      by_contra hc; exact hr (h.kept (Or.inr hc))
    have hv := h.value T hT
    rw [ite_eq_left hc] at hv
    cases hn : TM.nextScalar.run T with
    | some p => rw [hn] at hv; exact absurd (hv.1.symm.trans htag) (by decide)
    | none => rw [nextScalars_fail (nextScalars_zero T) hn hc]; exact ec

/-! ## The loop -/

/-- The loop head `0x80004908` after `d` scalars, the `Vec` at `S - 176` with capacity `cap` and
buffer `ptr`, the shunt at `S - 120`. -/
structure Body (s u : MachineState) (cap ptr : Word) (d : Nat) : Prop where
  saved : Saved s u
  x8 : u.getReg .x8 = s.getReg .x10
  x9 : u.getReg .x9 = ptr
  x18 : u.getReg .x18 = 0xffffffffffffffff
  x19 : u.getReg .x19 = BitVec.ofNat 64 d
  x20 : u.getReg .x20 = BitVec.ofNat 64 (24 * d)
  x21 : u.getReg .x21 = s.getReg .x2 - 80
  capM : u.getMem (s.getReg .x2 - 176) = cap
  ptrM : u.getMem (s.getReg .x2 - 168) = ptr
  lenM : u.getMem (s.getReg .x2 - 160) = BitVec.ofNat 64 d
  shP : u.getMem (s.getReg .x2 - 120) = s.getReg .x11
  shStart : u.getMem (s.getReg .x2 - 112) = BitVec.ofNat 64 d
  shEnd : u.getMem (s.getReg .x2 - 104) = s.getReg .x12
  shR : u.getMem (s.getReg .x2 - 96) = s.getReg .x2 - 224
  res : u.getMem (s.getReg .x2 - 224) = 0xffffffffffffffff
  le : d ≤ (s.getReg .x12).toNat
  room : d ≤ cap.toNat
  buf : NewBuf s u ptr (cap.toNat * 24) 8
  heap : HeapOk u
  mono : heapNext s ≤ heapNext u
  frame : DFrame s u (W s u)
  value : ∀ T, TranscriptAt s (s.getReg .x11) T → ∃ T',
    (TM.nextScalars d).run T = some (eListAt u ptr d, T') ∧ TranscriptAt u (s.getReg .x11) T'

set_option maxHeartbeats 1000000 in
/-- `Some` from the first `next`: 96 bytes, the `Vec` holding the scalar, the shunt copied. -/
theorem start (hA : AllocSpec) {s u : MachineState} (hpre : NextScalarsPre s)
    (hpc : u.pc = 0x80004868) (h : First s u) (htag : u.getMem (s.getReg .x2 - 152) ≠ 0) :
    ∃ v, Reaches Image.code u v ∧ ((v.pc = 0x80004908 ∧ ∃ cap ptr, Body s v cap ptr 1) ∨
      Dead Image.code v) := by
  have hb := bounds hpre
  have hS : 56 ≤ (s.getReg .x2).toNat := by addr_omega [hb]
  have hst := hpre.stack
  have hc : 0 < (s.getReg .x12).toNat := by by_contra hc; exact htag (h.past hc)
  have hres := h.kept (Or.inl htag)
  have e72 : u.getReg .x2 + 72 = s.getReg .x2 - 152 := by rw [h.saved.x2]; bv_omega
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80004868_spec hpc (by
    rv_eval [h.saved.x2]
    valid_access hpre.stack.valid [hb])
  have k₁ := b80004868_keeps h₁
  have hm₁ := b80004868_mem_same h₁
  obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80004870_spec
    (b80004868_pc_not_taken h₁ (by rw [e72]; exact htag)) trivial
  have k₂ := b80004870_keeps h₂
  have hm₂ := b80004870_mem_same h₂
  have hm12 (a : Word) : u₂.getMem a = u.getMem a := by rw [hm₂, hm₁]
  have nx₂ : heapNext u₂ = heapNext u := by simp only [heapNext, hm12]
  have hap : AllocPre u₂ := ⟨⟨nx₂ ▸ h.heap.lo, nx₂ ▸ h.heap.hi⟩, by rw [b80004870_x10 h₂]; decide⟩
  obtain ⟨u₃, hr₃, ⟨hpc₃, hpres₃, hpost₃⟩ | hd⟩ := hA.call (hr₁.trans hr₂) (b80004870_pc h₂) hap
  swap
  · exact ⟨_, hr₃, Or.inr hd⟩
  have hB0 : heapNext u₂ ≤ (u₃.getReg .x10).toNat := hpost₃.above
  have hBn : heapNext u₃ = (u₃.getReg .x10).toNat + 96 := by
    rw [hpost₃.next, b80004870_x11 h₂]; rfl
  have hBa : (u₃.getReg .x10).toNat % 8 = 0 := by
    have := hpost₃.aligned; rw [b80004870_x10 h₂] at this; exact this
  have hBh : (u₃.getReg .x10).toNat + 96 ≤ heapEnd := hBn ▸ hpost₃.heap.hi
  have hlo : heapStart ≤ heapNext u := h.heap.lo
  have hsn : heapNext u = heapNext s := h.next
  have hB0' : heapNext s ≤ (u₃.getReg .x10).toNat := by rw [← hsn, ← nx₂]; exact hB0
  have hm₃ (a : Word) (ha : a ≠ nextAddr) : u₃.getMem a = u₂.getMem a := hpost₃.mem a ha
  have hne : u₃.getReg .x10 ≠ 0 := fun h0 ↦ by
    rw [h0] at hB0; simp only [heapStart] at hlo; rw [nx₂] at hB0; simp at hB0; omega
  obtain ⟨u₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b80004880_spec
    (by rw [hpc₃, returnAddress_eq, b80004870_x1 h₂]; decide) trivial
  have k₄ := b80004880_keeps h₄
  have hm₄ := b80004880_mem_same h₄
  have x2₃ : u₃.getReg .x2 = s.getReg .x2 - 224 := by
    rw [hpres₃.reg .x2 (by decide), k₂ .x2 (by decide), k₁ .x2 (by decide), h.saved.x2]
  have x2₄ : u₄.getReg .x2 = s.getReg .x2 - 224 := (k₄ .x2 (by decide)).trans x2₃
  have x10₄ : u₄.getReg .x10 = u₃.getReg .x10 := k₄ .x10 (by decide)
  obtain ⟨u₅, hr₅, h₅⟩ := Sym.BlockSpec.reaches b80004884_spec
    (b80004880_pc_not_taken h₄ hne) (by
      rv_eval [x2₄, x10₄]
      and_intros <;> first
        | addr_omega [hb, hB0', hBh, hBa]
        | valid_access hpre.stack.valid [hb]
        | (refine Samples.heap_valid ?_ ?_ ?_ <;> addr_omega [hb, hB0', hBh, hBa, hlo, hsn]))
  have k₅ := b80004884_keeps h₅
  have fr₅ : ∀ a, ¬ Within a (s.getReg .x2 - 176) 88 → ¬ Within a (u₃.getReg .x10) 24 →
      u₅.getMem a = u₄.getMem a := fun a h1 h2 ↦ h₅.frame a (by
    rv_eval [x2₄, x10₄]
    and_intros <;> addr_omega [h1, h2, hb, hB0', hBh])
  have G₅ := DFrame.of_two fr₅
  have mem4 (a : Word) (ha : a ≠ nextAddr) : u₄.getMem a = u.getMem a := by
    rw [hm₄, hm₃ a ha, hm12]
  have nx₅ : heapNext u₅ = heapNext u₃ := by
    simp only [heapNext]
    rw [fr₅ _ (by addr_omega [hb, hst.next]) (by addr_omega [hBh]), hm₄]
  have S₂ : Saved s u₂ := (h.saved.same hS (k₁ .x2 (by decide)) (fun r hr ↦ k₁ r (mem_of_mem hr _))
    hm₁).same hS (k₂ .x2 (by decide)) (fun r hr ↦ k₂ r (mem_of_mem hr _)) hm₂
  have S₃ : Saved s u₃ := S₂.step hS (hpres₃.reg .x2)
    (fun r hr ↦ hpres₃.reg r (mem_of_mem hr _))
    fun y h1 h2 ↦ hm₃ y (by addr_omega [h1, h2, hb, hst.next])
  have S₄ : Saved s u₄ := S₃.same hS (k₄ .x2 (by decide)) (fun r hr ↦ k₄ r (mem_of_mem hr _)) hm₄
  have S₅ : Saved s u₅ := S₄.step hS (k₅ .x2 (by decide)) (fun r hr ↦ k₅ r (mem_of_mem hr _))
    fun y h1 h2 ↦ fr₅ y (by addr_omega [h1, h2, hb]) (by addr_omega [h1, h2, hb, hBh])
  have m48 := b80004884_m_x2_48 h₅
  have m56 := b80004884_m_x2_56 h₅
  have m64 := b80004884_m_x2_64 h₅
  have m104 := b80004884_m_x2_104 h₅
  have m112 := b80004884_m_x2_112 h₅
  have m120 := b80004884_m_x2_120 h₅
  have m128 := b80004884_m_x2_128 h₅
  have b0 := b80004884_m_x10_0 h₅
  have b8 := b80004884_m_x10_8 h₅
  have b16 := b80004884_m_x10_16 h₅
  rv_eval [x2₄, x10₄] at m48 m56 m64 m104 m112 m120 m128 b0 b8 b16
  have nn (y : Word) (h1 : (s.getReg .x2).toNat - 224 ≤ y.toNat) (h2 : y.toNat + 8 ≤ (s.getReg .x2).toNat) :
      y ≠ nextAddr := by addr_omega [h1, h2, hb, hst.next]
  have D₄ : DFrame u u₄ (Within · nextAddr 8) :=
    fun a ha ↦ mem4 a fun he ↦ ha 0 (by decide) (by rw [add_ofNat_zero, he]; addr_omega [])
  have Lu : DFrame u u₅ (Low s (heapNext u₅)) :=
    (D₄.mono fun a ha ↦ Or.inr (Or.inl ha)).trans G₅ fun a ha ↦ by
      rcases ha with ha | ha
      · exact Or.inl (by addr_omega [ha, hb])
      · exact Or.inr (Or.inr ⟨by addr_omega [ha, hB0'], by rw [nx₅, hBn]; addr_omega [ha]⟩)
  have hhi₅ : heapNext u₅ ≤ heapEnd := by rw [nx₅, hBn]; exact hBh
  refine ⟨u₅, hr₃.trans (hr₄.trans hr₅), Or.inl ⟨b80004884_pc h₅, 4,
    u₃.getReg .x10, ?_⟩⟩
  exact {
    saved := S₅
    x8 := by rw [k₅ .x8 (by decide), k₄ .x8 (by decide), hpres₃.reg .x8, k₂ .x8 (by decide),
      k₁ .x8 (by decide), h.x8]
    x9 := by rw [b80004884_x9 h₅, x10₄]
    x18 := by rw [k₅ .x18 (by decide), k₄ .x18 (by decide), hpres₃.reg .x18, k₂ .x18 (by decide),
      k₁ .x18 (by decide), h.x18]
    x19 := by rw [b80004884_x19 h₅]; rfl
    x20 := by rw [b80004884_x20 h₅]; rfl
    x21 := by rw [b80004884_x21 h₅, x2₄]; bv_omega
    capM := m48
    ptrM := m56
    lenM := by rw [m64]; rfl
    shP := by rw [m104, mem4 _ (nn _ (by addr_omega [hb]) (by addr_omega [hb])), h.shP]
    shStart := by
      rw [m112, mem4 _ (nn _ (by addr_omega [hb]) (by addr_omega [hb])), h.shStart, ite_eq_left hc]
      rfl
    shEnd := by rw [m120, mem4 _ (nn _ (by addr_omega [hb]) (by addr_omega [hb])), h.shEnd]
    shR := by rw [m128, mem4 _ (nn _ (by addr_omega [hb]) (by addr_omega [hb])), h.shR]
    res := by
      rw [fr₅ _ (by addr_omega [hb]) (by addr_omega [hb, hBh]),
        mem4 _ (nn _ (by addr_omega [hb]) (by addr_omega [hb])), hres]
    le := hc
    room := by decide
    buf := by
      simp only [NewBuf]
      refine ⟨hBa, Or.inr ⟨hB0', ?_⟩⟩
      rw [nx₅, hBn]; simp
    heap := ⟨by rw [nx₅, hBn]; have := hlo; simp only [heapStart] at this ⊢; omega, hhi₅⟩
    mono := by rw [nx₅, hBn]; omega
    frame := (h.frame.mono fun a h ↦ W.mono (by rw [nx₅, hBn, hsn]; omega) h).trans Lu
      fun a ha ↦ Low.toW (Nat.le_refl _) ha
    value := fun T hT ↦ by
      have hv := h.value T hT
      rw [ite_eq_left hc] at hv
      cases hn : TM.nextScalar.run T with
      | none => rw [hn] at hv; exact absurd hv.1 htag
      | some p =>
        obtain ⟨x, T'⟩ := p
        rw [hn] at hv
        obtain ⟨-, hx, hT'⟩ := hv
        refine ⟨T', ?_, Low.transcriptAt hpre hhi₅ h.heap.hi h.frame Lu hT'⟩
        have hel : eListAt u₅ (u₃.getReg .x10) 1 = [x] := by
          simp only [eListAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero,
            add_ofNat_zero]
          rw [← hx]
          refine congrArg (fun z ↦ [z]) (eAt_congr ?_ ?_ ?_)
          · rw [b0, mem4 _ (nn _ (by addr_omega [hb]) (by addr_omega [hb]))]
          · rw [b8, mem4 _ (nn _ (by addr_omega [hb]) (by addr_omega [hb])),
              show s.getReg .x2 - 144 + 8 = s.getReg .x2 - 136 by bv_omega]
          · rw [b16, mem4 _ (nn _ (by addr_omega [hb]) (by addr_omega [hb])),
              show s.getReg .x2 - 144 + 16 = s.getReg .x2 - 128 by bv_omega]
        rw [hel]
        exact nextScalars_snoc (nextScalars_zero T) hn }

/-- What the mirror says of the loop's `next` after `d` scalars, read at `u`. -/
def CallValue (s u : MachineState) (ptr : Word) (d : Nat) : Prop :=
  ∀ T, TranscriptAt s (s.getReg .x11) T → ∃ T',
    (TM.nextScalars d).run T = some (eListAt u ptr d, T') ∧
    if d < (s.getReg .x12).toNat then
      match TM.nextScalar.run T' with
      | some (x, T'') => u.getMem (s.getReg .x2 - 88) = 1 ∧ eAt u (s.getReg .x2 - 80) = x ∧
          TranscriptAt u (s.getReg .x11) T''
      | none => u.getMem (s.getReg .x2 - 88) = 0 ∧ u.getMem (s.getReg .x2 - 224) = 3
    else TranscriptAt u (s.getReg .x11) T'

theorem CallValue.transport {s u v : MachineState} {ptr ptr' : Word} {d : Nat}
    (h : CallValue s u ptr d) (hel : eListAt v ptr' d = eListAt u ptr d)
    (h88 : v.getMem (s.getReg .x2 - 88) = u.getMem (s.getReg .x2 - 88))
    (h80 : eAt v (s.getReg .x2 - 80) = eAt u (s.getReg .x2 - 80))
    (h224 : v.getMem (s.getReg .x2 - 224) = u.getMem (s.getReg .x2 - 224))
    (htr : ∀ T, TranscriptAt u (s.getReg .x11) T → TranscriptAt v (s.getReg .x11) T) :
    CallValue s v ptr' d := by
  intro T hT
  obtain ⟨T', h1, h2⟩ := h T hT
  refine ⟨T', by rw [hel]; exact h1, ?_⟩
  by_cases hc : d < (s.getReg .x12).toNat
  · rw [ite_eq_left hc] at h2 ⊢
    generalize TM.nextScalar.run T' = o at h2 ⊢
    rcases o with _ | ⟨x, T''⟩
    · exact ⟨h88.trans h2.1, h224.trans h2.2⟩
    · exact ⟨h88.trans h2.1, h80.trans h2.2.1, htr _ h2.2.2⟩
  · rw [ite_eq_right hc] at h2 ⊢
    exact htr _ h2

/-- Back from the loop's `next`, at `0x80004918`: its tag at `S - 88`, its value at `S - 80`. -/
structure AfterCall (s u : MachineState) (cap ptr : Word) (d : Nat) : Prop where
  saved : Saved s u
  x8 : u.getReg .x8 = s.getReg .x10
  x9 : u.getReg .x9 = ptr
  x18 : u.getReg .x18 = 0xffffffffffffffff
  x19 : u.getReg .x19 = BitVec.ofNat 64 d
  x20 : u.getReg .x20 = BitVec.ofNat 64 (24 * d)
  x21 : u.getReg .x21 = s.getReg .x2 - 80
  capM : u.getMem (s.getReg .x2 - 176) = cap
  ptrM : u.getMem (s.getReg .x2 - 168) = ptr
  lenM : u.getMem (s.getReg .x2 - 160) = BitVec.ofNat 64 d
  shP : u.getMem (s.getReg .x2 - 120) = s.getReg .x11
  shStart : u.getMem (s.getReg .x2 - 112) =
    if d < (s.getReg .x12).toNat then BitVec.ofNat 64 d + 1 else BitVec.ofNat 64 d
  shEnd : u.getMem (s.getReg .x2 - 104) = s.getReg .x12
  shR : u.getMem (s.getReg .x2 - 96) = s.getReg .x2 - 224
  past : ¬ d < (s.getReg .x12).toNat → u.getMem (s.getReg .x2 - 88) = 0
  kept : u.getMem (s.getReg .x2 - 88) ≠ 0 ∨ ¬ d < (s.getReg .x12).toNat →
    u.getMem (s.getReg .x2 - 224) = 0xffffffffffffffff
  le : d ≤ (s.getReg .x12).toNat
  room : d ≤ cap.toNat
  buf : NewBuf s u ptr (cap.toNat * 24) 8
  heap : HeapOk u
  mono : heapNext s ≤ heapNext u
  frame : DFrame s u (W s u)
  value : CallValue s u ptr d

/-- The registers `AfterCall` reads. -/
def callRegs : List Reg := [.x2, .x8, .x9, .x18, .x19, .x20, .x21] ++ keptRegs

theorem AfterCall.same {s u v : MachineState} {cap ptr : Word} {d : Nat} (hpre : NextScalarsPre s)
    (h : AfterCall s u cap ptr d) (hr : ∀ r ∈ callRegs, v.getReg r = u.getReg r)
    (hm : ∀ a, v.getMem a = u.getMem a) : AfterCall s v cap ptr d := by
  have hb := bounds hpre
  have nx : heapNext v = heapNext u := by simp only [heapNext, hm]
  exact {
    saved := h.saved.same (by addr_omega [hb]) (hr .x2 (by decide))
      (fun r h' ↦ hr r (by simp only [callRegs, List.mem_append]; exact Or.inr h')) hm
    x8 := (hr .x8 (by decide)).trans h.x8
    x9 := (hr .x9 (by decide)).trans h.x9
    x18 := (hr .x18 (by decide)).trans h.x18
    x19 := (hr .x19 (by decide)).trans h.x19
    x20 := (hr .x20 (by decide)).trans h.x20
    x21 := (hr .x21 (by decide)).trans h.x21
    capM := (hm _).trans h.capM
    ptrM := (hm _).trans h.ptrM
    lenM := (hm _).trans h.lenM
    shP := (hm _).trans h.shP
    shStart := (hm _).trans h.shStart
    shEnd := (hm _).trans h.shEnd
    shR := (hm _).trans h.shR
    past := fun hc ↦ (hm _).trans (h.past hc)
    kept := fun hc ↦ (hm _).trans (h.kept (by rw [hm] at hc; exact hc))
    le := h.le
    room := h.room
    buf := by have := h.buf; simp only [NewBuf, nx] at this ⊢; exact this
    heap := ⟨nx ▸ h.heap.lo, nx ▸ h.heap.hi⟩
    mono := nx ▸ h.mono
    frame := (h.frame.mono fun a h ↦ W.mono (Nat.le_of_eq nx.symm) h).trans (DFrame.of_same hm _)
      fun _ h ↦ h
    value := h.value.transport (by
        unfold eListAt; apply List.map_congr_left; intro i _; exact eAt_congr (hm _) (hm _) (hm _))
      (hm _) (eAt_congr (hm _) (hm _) (hm _)) (hm _)
      fun T hT ↦ Low.transcriptAt hpre h.heap.hi h.heap.hi h.frame (DFrame.of_same hm _) hT }

set_option maxHeartbeats 1000000 in
/-- The loop's `next`, into `S - 88`. -/
theorem call (hN : ShuntNextSpec) {s u : MachineState} {cap ptr : Word} {d : Nat}
    (hpre : NextScalarsPre s) (hpc : u.pc = 0x80004908) (h : Body s u cap ptr d) :
    ∃ w, Reaches Image.code u w ∧ ((w.pc = 0x80004918 ∧ AfterCall s w cap ptr d) ∨
      Dead Image.code w) := by
  have hb := bounds hpre
  have hS : 56 ≤ (s.getReg .x2).toNat := by addr_omega [hb]
  have hSf := hpre.self.self
  have hss := hpre.selfStack
  have hsf := hpre.selfFree
  have hst := hpre.stack
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80004908_spec hpc trivial
  have k₁ := b80004908_keeps h₁
  have hm₁ := b80004908_mem_same h₁
  have x2₁ : u₁.getReg .x2 = s.getReg .x2 - 224 := (k₁ .x2 (by decide)).trans h.saved.x2
  have x10₁ : u₁.getReg .x10 = s.getReg .x2 - 88 := by rw [b80004908_x10 h₁, h.saved.x2]; bv_omega
  have x11₁ : u₁.getReg .x11 = s.getReg .x2 - 120 := by rw [b80004908_x11 h₁, h.saved.x2]; bv_omega
  have nx₁ : heapNext u₁ = heapNext u := by simp only [heapNext, hm₁]
  have F₁ : DFrame s u₁ (W s u₁) :=
    (h.frame.mono fun a h ↦ W.mono (Nat.le_of_eq nx₁.symm) h).trans (DFrame.of_same hm₁ _)
      fun _ h ↦ h
  have e24 : s.getReg .x2 - 120 + 24 = s.getReg .x2 - 96 := by bv_omega
  have e16 : s.getReg .x2 - 120 + 16 = s.getReg .x2 - 104 := by bv_omega
  have e8 : s.getReg .x2 - 120 + 8 = s.getReg .x2 - 112 := by bv_omega
  have hsp : ShuntNextPre u₁ := shunt_pre hpre x2₁ x10₁ x11₁ (by addr_omega [hb]) (by addr_omega [hb])
    (by addr_omega [hb]) (by rw [hm₁, h.shP]) (by rw [e24, hm₁, h.shR]) (by rw [nx₁]; exact h.heap.hi)
    F₁
  obtain ⟨w, hr₂, ⟨hpc₂, hpres₂, hpost₂⟩ | hd⟩ := hN.call (hr₁) (b80004908_pc h₁) hsp
  swap
  · exact ⟨_, hr₂, Or.inr hd⟩
  have hd64 : d < 2 ^ 64 := Nat.lt_of_le_of_lt h.le (s.getReg .x12).isLt
  have eP : shuntP u₁ = s.getReg .x11 := by simp only [shuntP, x11₁, hm₁, h.shP]
  have eR : shuntR u₁ = s.getReg .x2 - 224 := by simp only [shuntR, x11₁, e24, hm₁, h.shR]
  have eSt' : shuntStart u₁ = BitVec.ofNat 64 d := by simp only [shuntStart, x11₁, e8, hm₁, h.shStart]
  have eSt : (shuntStart u₁).toNat = d := by rw [eSt', BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd64]
  have eEn : shuntEnd u₁ = s.getReg .x12 := by simp only [shuntEnd, x11₁, e16, hm₁, h.shEnd]
  have G := hpost₂.frame
  rw [x10₁, x11₁, eR, eP] at G
  simp only [stackLo, x2₁] at G
  have keep (y : Word) (h1 : (s.getReg .x2).toNat - 208 ≤ y.toNat)
      (h2 : y.toNat + 8 ≤ (s.getReg .x2).toNat)
      (h3 : y.toNat + 8 ≤ (s.getReg .x2).toNat - 112 ∨ (s.getReg .x2).toNat - 104 ≤ y.toNat)
      (h4 : y.toNat + 8 ≤ (s.getReg .x2).toNat - 88 ∨ (s.getReg .x2).toNat - 56 ≤ y.toNat) :
      w.getMem y = u₁.getMem y :=
    G y fun i hi h ↦ by
      rcases h with h | h | h | h | h <;> addr_omega [h, hi, h1, h2, h3, h4, hb, hss, hSf]
  have nxw : heapNext w = heapNext u₁ := by
    have e := G nextAddr fun i hi h ↦ by
      rcases h with h | h | h | h | h <;> addr_omega [h, hi, hst.next, hb, hsf, hSf]
    simp only [heapNext, e]
  have Fw : DFrame s w (W s w) :=
    (F₁.mono fun a h ↦ W.mono (Nat.le_of_eq nxw.symm) h).trans G fun a h ↦ by
      rcases h with h | h | h | h | h
      · exact Or.inr (Or.inr (Or.inl (by addr_omega [h, hb])))
      · exact Or.inr (Or.inr (Or.inl (by addr_omega [h, hb])))
      · exact Or.inr (Or.inr (Or.inl (by addr_omega [h, hb])))
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl (by addr_omega [h, hb])))
  have hbuf := h.buf
  have hhi := h.heap.hi
  have hroom := h.room
  have hel : eListAt w ptr d = eListAt u ptr d := by
    rw [G.eListAt fun i hi hw ↦ by
      rcases hw with hw | hw | hw | hw | hw <;>
        addr_omega [hw, hi, hbuf, hroom, hhi, hb, hsf, hSf, hst.above]]
    unfold eListAt; apply List.map_congr_left; intro i _; exact eAt_congr (hm₁ _) (hm₁ _) (hm₁ _)
  have hstart := hpost₂.start
  have hpast := hpost₂.past
  have hkept := hpost₂.kept
  rw [x11₁, e8, eEn, eSt, eSt'] at hstart
  rw [eEn, eSt, x10₁] at hpast
  rw [eEn, eSt, x10₁, eR, hm₁, h.res] at hkept
  have hregs (r : Reg) (hr : r ∈ callRegs) : w.getReg r = u.getReg r := by
    rw [hpres₂.reg r (mem_of_mem hr _), k₁ r (mem_of_mem hr _)]
  refine ⟨w, hr₂, Or.inl ⟨by rw [hpc₂, returnAddress_eq, b80004908_x1 h₁]; decide, {
    saved := h.saved.step hS (hregs .x2 (by decide))
      (fun r hr ↦ hregs r (by simp only [callRegs, List.mem_append]; exact Or.inr hr))
      fun y h1 h2 ↦ (keep y (by omega) h2 (by omega) (by omega)).trans (hm₁ y)
    x8 := (hregs .x8 (by decide)).trans h.x8
    x9 := (hregs .x9 (by decide)).trans h.x9
    x18 := (hregs .x18 (by decide)).trans h.x18
    x19 := (hregs .x19 (by decide)).trans h.x19
    x20 := (hregs .x20 (by decide)).trans h.x20
    x21 := (hregs .x21 (by decide)).trans h.x21
    capM := by rw [keep _ (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb])
      (by addr_omega [hb]), hm₁, h.capM]
    ptrM := by rw [keep _ (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb])
      (by addr_omega [hb]), hm₁, h.ptrM]
    lenM := by rw [keep _ (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb])
      (by addr_omega [hb]), hm₁, h.lenM]
    shP := by rw [keep _ (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb])
      (by addr_omega [hb]), hm₁, h.shP]
    shStart := hstart
    shEnd := by rw [keep _ (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb])
      (by addr_omega [hb]), hm₁, h.shEnd]
    shR := by rw [keep _ (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb])
      (by addr_omega [hb]), hm₁, h.shR]
    past := hpast
    kept := hkept
    le := h.le
    room := h.room
    buf := by have := h.buf; simp only [NewBuf, nxw, nx₁] at this ⊢; exact this
    heap := ⟨by rw [nxw, nx₁]; exact h.heap.lo, by rw [nxw, nx₁]; exact h.heap.hi⟩
    mono := by rw [nxw, nx₁]; exact h.mono
    frame := Fw
    value := fun T hT ↦ by
      obtain ⟨T', h1, h2⟩ := h.value T hT
      have h2' := Low.transcriptAt hpre h.heap.hi h.heap.hi h.frame (DFrame.of_same hm₁ _) h2
      have hv := hpost₂.value T' (by rw [eP]; exact h2')
      rw [eSt, eEn, eP, x10₁, eR] at hv
      rw [show s.getReg .x2 - 88 + 8 = s.getReg .x2 - 80 by bv_omega] at hv
      exact ⟨T', by rw [hel]; exact h1, hv⟩ }⟩⟩

theorem toNat_ofNat_of_le {d n : Nat} (h : d ≤ n) (hn : n < 2 ^ 64) : (BitVec.ofNat 64 d).toNat = d := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

set_option maxHeartbeats 1000000 in
/-- A full `Vec` (`0x80004928`): `reserve(1)`, then the buffer reloaded. -/
theorem reserve_step (hR : ReserveFreshSpec 0x80008a10 24 8) {s u : MachineState} {cap ptr : Word}
    {d : Nat} (hpre : NextScalarsPre s) (hpc : u.pc = 0x80004928) (h : AfterCall s u cap ptr d)
    (hfull : cap.toNat = d) :
    ∃ v, Reaches Image.code u v ∧ ((v.pc = 0x800048e0 ∧ v.getMem (s.getReg .x2 - 88) =
      u.getMem (s.getReg .x2 - 88) ∧ ∃ cap' ptr', AfterCall s v cap' ptr' d ∧
        d + 1 ≤ cap'.toNat) ∨ Dead Image.code v) := by
  have hb := bounds hpre
  have hS : 56 ≤ (s.getReg .x2).toNat := by addr_omega [hb]
  have hst := hpre.stack
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80004928_spec hpc trivial
  have k₁ := b80004928_keeps h₁
  have hm₁ := b80004928_mem_same h₁
  have x2₁ : u₁.getReg .x2 = s.getReg .x2 - 224 := (k₁ .x2 (by decide)).trans h.saved.x2
  have x10₁ : u₁.getReg .x10 = s.getReg .x2 - 176 := by
    rw [b80004928_x10 h₁, h.saved.x2]; bv_omega
  have nx₁ : heapNext u₁ = heapNext u := by simp only [heapNext, hm₁]
  have heap₁ : HeapOk u₁ := ⟨nx₁ ▸ h.heap.lo, nx₁ ▸ h.heap.hi⟩
  have e8 : s.getReg .x2 - 176 + 8 = s.getReg .x2 - 168 := by bv_omega
  have e16 : s.getReg .x2 - 176 + 16 = s.getReg .x2 - 160 := by bv_omega
  have ec : vecCap u₁ (s.getReg .x2 - 176) = cap := by simp only [vecCap, hm₁, h.capM]
  have ep : vecPtr u₁ (s.getReg .x2 - 176) = ptr := by simp only [vecPtr, e8, hm₁, h.ptrM]
  have el : vecLen u₁ (s.getReg .x2 - 176) = BitVec.ofNat 64 d := by
    simp only [vecLen, e16, hm₁, h.lenM]
  have eld : (BitVec.ofNat 64 d).toNat = d := toNat_ofNat_of_le h.le (s.getReg .x12).isLt
  have hbufS := h.buf.buf hpre.heap
  have hrp : ReservePre 24 8 u₁ := {
    heap := heap₁
    self := by rw [x10₁]; valid_sub hst.valid [hb]
    vec := by
      rw [x10₁]
      refine ⟨?_, by rw [el, ec, eld]; exact h.room⟩
      simp only [RawVecOk, ec, ep]
      simp only [Buf, nx₁] at hbufS ⊢
      exact hbufS
    stack := hst.sub 224 x2₁ (by decide) (by decide) (by decide) (by decide) (by decide)
    selfFree := by
      rw [x10₁]; simp only [Outside]
      exact ⟨Or.inr (by addr_omega [hst.above, hb]), by addr_omega [hst.next, hb]⟩
    selfStack := by rw [x10₁]; simp only [stackLo, x2₁]; addr_omega [hb] }
  obtain ⟨v, hr₂, ⟨hpc₂, hpres₂, hpost₂, hfr₂⟩ | hd⟩ := hR.call hr₁ (b80004928_pc h₁) hrp
  swap
  · exact ⟨_, hr₂, Or.inr hd⟩
  rw [x10₁] at hfr₂
  have hcap := hpost₂.cap
  rw [x10₁, el, eld, b80004928_x11 h₁] at hcap
  have hlen := hpost₂.len
  rw [x10₁, el] at hlen
  have hvec := hpost₂.vec
  rw [x10₁] at hvec
  have hbytes := hpost₂.bytes
  rw [x10₁, ec, ep] at hbytes
  have Fr := DFrame.of_byteFrame hpost₂.frame
  rw [x10₁] at Fr
  simp only [stackLo, x2₁] at Fr
  have mono₂ := hpost₂.mono
  have hhi₂ := hpost₂.heap.hi
  have keep (y : Word) (h1 : (s.getReg .x2).toNat - 224 ≤ y.toNat)
      (h2 : y.toNat + 8 ≤ (s.getReg .x2).toNat)
      (h3 : y.toNat + 8 ≤ (s.getReg .x2).toNat - 176 ∨ (s.getReg .x2).toNat - 160 ≤ y.toNat) :
      v.getMem y = u.getMem y := by
    rw [Fr y fun i hi h ↦ by
      rcases h with h | h | h | h <;> addr_omega [h, hi, h1, h2, h3, hb, hst.next, hhi₂], hm₁]
  have x2v : v.getReg .x2 = s.getReg .x2 - 224 := (hpres₂.reg .x2).trans x2₁
  obtain ⟨q, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80004938_spec
    (by rw [hpc₂, returnAddress_eq, b80004928_x1 h₁]; decide) (by
      rv_eval [x2v]
      valid_access hst.valid [hb])
  have k₃ := b80004938_keeps h₃
  have hm₃ := b80004938_mem_same h₃
  have x9₃ : q.getReg .x9 = v.getMem (s.getReg .x2 - 168) := by
    rw [b80004938_x9 h₃, x2v, show s.getReg .x2 - 224 + 56 = s.getReg .x2 - 168 by bv_omega]
  have nxq : heapNext q = heapNext v := by simp only [heapNext, hm₃]
  have kq (y : Word) (h1 : (s.getReg .x2).toNat - 224 ≤ y.toNat)
      (h2 : y.toNat + 8 ≤ (s.getReg .x2).toNat)
      (h3 : y.toNat + 8 ≤ (s.getReg .x2).toNat - 176 ∨ (s.getReg .x2).toNat - 160 ≤ y.toNat) :
      q.getMem y = u.getMem y := by rw [hm₃, keep y h1 h2 h3]
  have hroom : d + 1 ≤ (v.getMem (s.getReg .x2 - 176)).toNat := by
    have := hcap; simp only [vecCap] at this; exact this
  have hpa : (vecPtr v (s.getReg .x2 - 176)).toNat % 8 = 0 := hvec.raw.1
  rw [vecPtr, e8] at hpa
  have hregs (r : Reg) (hr : r ∈ [Reg.x8, .x18, .x19, .x20, .x21] ++ keptRegs) :
      q.getReg r = u.getReg r := by
    rw [k₃ r (mem_of_mem hr _), hpres₂.reg r (mem_of_mem hr _), k₁ r (mem_of_mem hr _)]
  have Lq : DFrame u q (Low s (heapNext q)) :=
    ((DFrame.of_same hm₁ _).trans Fr fun a hw ↦ by
      rcases hw with hw | hw | hw | hw
      · exact Or.inl (by addr_omega [hw, hb])
      · exact Or.inl (by addr_omega [hw, hb])
      · exact Or.inr (Or.inl hw)
      · have := h.mono
        exact Or.inr (Or.inr ⟨by simp only [Fresh] at hw; rw [nx₁] at hw; omega,
          by rw [nxq]; exact hw.2⟩)).trans (DFrame.of_same hm₃ _) fun _ hw ↦ hw
  have hhiq : heapNext q ≤ heapEnd := nxq ▸ hhi₂
  refine ⟨q, hr₂.trans hr₃, Or.inl ⟨b80004938_pc h₃, kq _ (by addr_omega [hb])
    (by addr_omega [hb]) (by addr_omega [hb]), v.getMem (s.getReg .x2 - 176),
    v.getMem (s.getReg .x2 - 168), ?_, hroom⟩⟩
  exact {
    saved := h.saved.step hS (by rw [k₃ .x2 (by decide), x2v, h.saved.x2])
      (fun r hr ↦ hregs r (by simp only [List.mem_append]; exact Or.inr hr))
      fun y h1 h2 ↦ kq y (by omega) h2 (by omega)
    x8 := (hregs .x8 (by decide)).trans h.x8
    x9 := x9₃
    x18 := (hregs .x18 (by decide)).trans h.x18
    x19 := (hregs .x19 (by decide)).trans h.x19
    x20 := (hregs .x20 (by decide)).trans h.x20
    x21 := (hregs .x21 (by decide)).trans h.x21
    capM := hm₃ _
    ptrM := hm₃ _
    lenM := by rw [hm₃]; simp only [vecLen, e16] at hlen; exact hlen
    shP := by rw [kq _ (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb]), h.shP]
    shStart := by rw [kq _ (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb]), h.shStart]
    shEnd := by rw [kq _ (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb]), h.shEnd]
    shR := by rw [kq _ (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb]), h.shR]
    past := fun hc ↦ by
      rw [kq _ (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb])]; exact h.past hc
    kept := fun hc ↦ by
      rw [kq _ (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb])] at hc ⊢
      exact h.kept hc
    le := h.le
    room := by omega
    buf := by
      rcases hfr₂ with ⟨-, ec'⟩ | hn
      · rw [vecCap, vecCap, hm₁, h.capM] at ec'
        rw [ec'] at hroom; omega
      · have hm1 := h.mono
        simp only [NewBuf, vecPtr, vecCap, e8] at hn ⊢
        rw [nxq]; rw [nx₁] at hn; omega
    heap := ⟨by rw [nxq]; exact hpost₂.heap.lo, hhiq⟩
    mono := by rw [nxq]; have := h.mono; rw [nx₁] at mono₂; omega
    frame := (h.frame.mono fun a h ↦ W.mono (by rw [nxq, ← nx₁]; exact mono₂) h).trans Lq
      fun a ha ↦ Low.toW (Nat.le_refl _) ha
    value := h.value.transport
      (by
        rw [(DFrame.of_same hm₃ fun _ ↦ False).eListAt fun _ _ h ↦ h,
          ← (DFrame.of_same hm₁ fun _ ↦ False).eListAt fun _ _ h ↦ h]
        refine eListAt_eq_of_bytesAt ?_ hpa h.buf.1
        rw [show 24 * d = cap.toNat * 24 by omega]
        simp only [vecPtr, e8] at hbytes
        exact hbytes)
      (kq _ (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb]))
      (eAt_congr (kq _ (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb]))
        (kq _ (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb]))
        (kq _ (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb])))
      (kq _ (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb]))
      fun T hT ↦ Low.transcriptAt hpre hhiq h.heap.hi h.frame Lq hT }

set_option maxHeartbeats 1000000 in
/-- `Some` (`0x80004918`): room for one more, reserved when the `Vec` is full. -/
theorem grow (hR : ReserveFreshSpec 0x80008a10 24 8) {s u : MachineState} {cap ptr : Word}
    {d : Nat} (hpre : NextScalarsPre s) (hpc : u.pc = 0x80004918) (h : AfterCall s u cap ptr d)
    (htag : u.getMem (s.getReg .x2 - 88) ≠ 0) :
    ∃ v, Reaches Image.code u v ∧ ((v.pc = 0x800048e0 ∧ v.getMem (s.getReg .x2 - 88) ≠ 0 ∧
      ∃ cap' ptr', AfterCall s v cap' ptr' d ∧ d + 1 ≤ cap'.toNat) ∨ Dead Image.code v) := by
  have hb := bounds hpre
  have e136 : u.getReg .x2 + 136 = s.getReg .x2 - 88 := by rw [h.saved.x2]; bv_omega
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80004918_spec hpc (by
    rv_eval [h.saved.x2]
    valid_access hpre.stack.valid [hb])
  have k₁ := b80004918_keeps h₁
  have hm₁ := b80004918_mem_same h₁
  have A₁ : AfterCall s u₁ cap ptr d := h.same hpre (fun r hr ↦ k₁ r (mem_of_mem hr _)) hm₁
  obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80004920_spec
    (b80004918_pc_not_taken h₁ (by rw [e136]; exact htag)) (by
      rv_eval [A₁.saved.x2]
      valid_access hpre.stack.valid [hb])
  have k₂ := b80004920_keeps h₂
  have hm₂ := b80004920_mem_same h₂
  have A₂ : AfterCall s u₂ cap ptr d := A₁.same hpre (fun r hr ↦ k₂ r (mem_of_mem hr _)) hm₂
  have tag₂ : u₂.getMem (s.getReg .x2 - 88) ≠ 0 := by rw [hm₂, hm₁]; exact htag
  have e48 : u₁.getReg .x2 + 48 = s.getReg .x2 - 176 := by rw [A₁.saved.x2]; bv_omega
  have eld : (BitVec.ofNat 64 d).toNat = d := toNat_ofNat_of_le h.le (s.getReg .x12).isLt
  by_cases hfull : u₁.getReg .x19 = u₁.getMem (u₁.getReg .x2 + 48)
  · have hcd : cap.toNat = d := by
      rw [A₁.x19, e48, A₁.capM] at hfull; rw [← hfull, eld]
    obtain ⟨v, hr₃, ⟨hpc₃, htv, cap', ptr', hv, hroom⟩ | hd⟩ :=
      reserve_step hR hpre (b80004920_pc_not_taken h₂ hfull) A₂ hcd
    · exact ⟨v, hr₁.trans (hr₂.trans hr₃), Or.inl ⟨hpc₃, by rw [htv]; exact tag₂, cap', ptr', hv,
        hroom⟩⟩
    · exact ⟨_, hr₁.trans (hr₂.trans hr₃), Or.inr hd⟩
  · have hne : cap.toNat ≠ d := fun hc ↦ hfull (by
      rw [A₁.x19, e48, A₁.capM]; exact BitVec.eq_of_toNat_eq (by rw [eld, hc]))
    have := A₁.room
    exact ⟨u₂, hr₁.trans hr₂, Or.inl ⟨b80004920_pc_taken h₂ hfull, tag₂, cap, ptr, A₂,
      by omega⟩⟩

set_option maxHeartbeats 1000000 in
/-- `0x800048e0`: the scalar pushed. -/
theorem push {s u : MachineState} {cap ptr : Word} {d : Nat} (hpre : NextScalarsPre s)
    (hpc : u.pc = 0x800048e0) (h : AfterCall s u cap ptr d) (hroom : d + 1 ≤ cap.toNat)
    (htag : u.getMem (s.getReg .x2 - 88) ≠ 0) :
    ∃ v, Reaches Image.code u v ∧ v.pc = 0x80004908 ∧ Body s v cap ptr (d + 1) := by
  have hb := bounds hpre
  have hS : 56 ≤ (s.getReg .x2).toNat := by addr_omega [hb]
  have hst := hpre.stack
  have hc : d < (s.getReg .x12).toNat := by by_contra hc; exact htag (h.past hc)
  have hres := h.kept (Or.inl htag)
  have hbuf := h.buf
  have hhi := h.heap.hi
  have hd24 : 24 * d < 2 ^ 64 := by simp only [NewBuf, heapEnd] at hbuf hhi; omega
  obtain ⟨v, hr₁, h₁⟩ := Sym.BlockSpec.reaches b800048e0_spec hpc (by
    rv_eval [h.x9, h.x20, h.x21, h.saved.x2]
    and_intros <;> first
      | addr_omega [hb, hbuf, hroom, hhi, hd24]
      | valid_access hst.valid [hb]
      | (refine Samples.heap_valid ?_ ?_ ?_ <;> addr_omega [hb, hbuf, hroom, hhi, hd24, hpre.heap.lo]))
  have k₁ := b800048e0_keeps h₁
  have m0 := b800048e0_m0 h₁
  have m2 := b800048e0_m2 h₁
  have m3 := b800048e0_m3 h₁
  have m64 := b800048e0_m_x2_64 h₁
  rw [h.x9, h.x20, h.x21] at m0 m2 m3
  rw [h.saved.x2, h.x19, show s.getReg .x2 - 224 + 64 = s.getReg .x2 - 160 by bv_omega] at m64
  have fr : ∀ a, ¬ Within a (ptr + BitVec.ofNat 64 (24 * d)) 24 →
      ¬ Within a (s.getReg .x2 - 160) 8 → v.getMem a = u.getMem a := fun a h1 h2 ↦ h₁.frame a (by
    rv_eval [h.x9, h.x20, h.saved.x2]
    and_intros <;> addr_omega [h1, h2, hb, hbuf, hroom, hhi, hd24])
  have G := DFrame.of_two fr
  have kp (y : Word) (h1 : (s.getReg .x2).toNat - 224 ≤ y.toNat) (h2 : y.toNat + 8 ≤ (s.getReg .x2).toNat)
      (h3 : y.toNat + 8 ≤ (s.getReg .x2).toNat - 160 ∨ (s.getReg .x2).toNat - 152 ≤ y.toNat) :
      v.getMem y = u.getMem y := fr y (by addr_omega [h1, h2, hb, hbuf, hroom, hhi, hd24])
    (by addr_omega [h1, h2, h3, hb])
  have nx : heapNext v = heapNext u := by
    simp only [heapNext]
    rw [fr _ (by addr_omega [hbuf, hroom, hhi, hd24]) (by addr_omega [hb, hst.next])]
  have L : DFrame u v (Low s (heapNext v)) := G.mono fun a h ↦ by
    rcases h with h | h
    · simp only [NewBuf] at hbuf
      exact Or.inr (Or.inr ⟨by addr_omega [h, hbuf, hroom, hd24], by
        rw [nx]; addr_omega [h, hbuf, hroom, hd24]⟩)
    · exact Or.inl (by addr_omega [h, hb])
  have hhiv : heapNext v ≤ heapEnd := nx ▸ hhi
  refine ⟨v, hr₁, b800048e0_pc h₁, ?_⟩
  exact {
    saved := h.saved.step hS (k₁ .x2 (by decide)) (fun r hr ↦ k₁ r (mem_of_mem hr _))
      fun y h1 h2 ↦ kp y (by omega) h2 (by omega)
    x8 := (k₁ .x8 (by decide)).trans h.x8
    x9 := (k₁ .x9 (by decide)).trans h.x9
    x18 := (k₁ .x18 (by decide)).trans h.x18
    x19 := by rw [b800048e0_x19 h₁, h.x19]; bv_omega
    x20 := by rw [b800048e0_x20 h₁, h.x20]; bv_omega
    x21 := (k₁ .x21 (by decide)).trans h.x21
    capM := by rw [kp _ (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb]), h.capM]
    ptrM := by rw [kp _ (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb]), h.ptrM]
    lenM := by rw [m64]; bv_omega
    shP := by rw [kp _ (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb]), h.shP]
    shStart := by
      rw [kp _ (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb]), h.shStart,
        ite_eq_left hc]
      bv_omega
    shEnd := by rw [kp _ (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb]), h.shEnd]
    shR := by rw [kp _ (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb]), h.shR]
    res := by rw [kp _ (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb]), hres]
    le := hc
    room := hroom
    buf := by simp only [NewBuf, nx] at hbuf ⊢; exact hbuf
    heap := ⟨by rw [nx]; exact h.heap.lo, hhiv⟩
    mono := by rw [nx]; exact h.mono
    frame := (h.frame.mono fun a h ↦ W.mono (Nat.le_of_eq nx.symm) h).trans L
      fun a ha ↦ Low.toW (Nat.le_refl _) ha
    value := fun T hT ↦ by
      obtain ⟨T', h1, h2⟩ := h.value T hT
      rw [ite_eq_left hc] at h2
      cases hn : TM.nextScalar.run T' with
      | none => rw [hn] at h2; exact absurd h2.1 htag
      | some p =>
        obtain ⟨x, T''⟩ := p
        rw [hn] at h2
        obtain ⟨-, hx, hT''⟩ := h2
        refine ⟨T'', ?_, Low.transcriptAt hpre hhiv h.heap.hi h.frame L hT''⟩
        have hel : eListAt v ptr d = eListAt u ptr d := G.eListAt fun i hi hw ↦ by
          rcases hw with hw | hw <;> addr_omega [hw, hi, hb, hbuf, hroom, hhi, hd24]
        rw [Samples.eListAt_succ, hel, eAt_congr m0 m2 m3, hx]
        exact nextScalars_snoc h1 hn }

set_option maxHeartbeats 1000000 in
/-- `None` from the loop's `next` (`0x80004918`): the `Vec`, or the residual's error. -/
theorem leave {s u : MachineState} {cap ptr : Word} {d : Nat} (hpre : NextScalarsPre s)
    (hpc : u.pc = 0x80004918) (h : AfterCall s u cap ptr d)
    (htag : u.getMem (s.getReg .x2 - 88) = 0) :
    ∃ t, Reaches Image.code u t ∧ t.pc = returnAddress s ∧ Preserves s t ∧
      NextScalarsPost s t := by
  have hb := bounds hpre
  have hS : 56 ≤ (s.getReg .x2).toNat := by addr_omega [hb]
  have e136 : u.getReg .x2 + 136 = s.getReg .x2 - 88 := by rw [h.saved.x2]; bv_omega
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80004918_spec hpc (by
    rv_eval [h.saved.x2]
    valid_access hpre.stack.valid [hb])
  have k₁ := b80004918_keeps h₁
  have hm₁ := b80004918_mem_same h₁
  have A₁ : AfterCall s u₁ cap ptr d := h.same hpre (fun r hr ↦ k₁ r (mem_of_mem hr _)) hm₁
  obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80004968_spec
    (b80004918_pc_taken h₁ (by rw [e136]; exact htag)) (by
      rv_eval [A₁.saved.x2]
      and_intros <;> valid_access hpre.stack.valid [hb])
  have k₂ := b80004968_keeps h₂
  have hm₂ := b80004968_mem_same h₂
  have A₂ : AfterCall s u₂ cap ptr d := A₁.same hpre (fun r hr ↦ k₂ r (mem_of_mem hr _)) hm₂
  have x2₁ := A₁.saved.x2
  have x10₂ : u₂.getReg .x10 = cap := by
    rw [b80004968_x10 h₂, x2₁, show s.getReg .x2 - 224 + 48 = s.getReg .x2 - 176 by bv_omega,
      A₁.capM]
  have x11₂ : u₂.getReg .x11 = ptr := by
    rw [b80004968_x11 h₂, x2₁, show s.getReg .x2 - 224 + 56 = s.getReg .x2 - 168 by bv_omega,
      A₁.ptrM]
  have hres : u₁.getMem (u₁.getReg .x2) = u.getMem (s.getReg .x2 - 224) := by rw [x2₁, hm₁]
  have tag₂ : u₂.getMem (s.getReg .x2 - 88) = 0 := by rw [hm₂, hm₁]; exact htag
  have eld : (BitVec.ofNat 64 d).toNat = d := toNat_ofNat_of_le h.le (s.getReg .x12).isLt
  by_cases hr : u.getMem (s.getReg .x2 - 224) = 0xffffffffffffffff
  · obtain ⟨t, hr₃, pc, pres, ec, ep, el, f⟩ := finish_ok hpre
      (b80004968_pc_not_taken h₂ (by rw [hres, A₁.x18]; exact hr)) A₂.saved A₂.x8
    obtain ⟨heapt, monot, frt, nxt, trt⟩ := post_of hpre A₂.frame A₂.heap A₂.mono f
    rw [x10₂] at ec
    rw [x11₂] at ep
    rw [A₂.x19] at el
    have hbuf := A₂.buf
    have hhi := A₂.heap.hi
    obtain ⟨hvec, hnb⟩ := newVec hpre.heap ec ep el nxt hbuf (by rw [eld]; exact A₂.room)
    refine ⟨t, hr₁.trans (hr₂.trans hr₃), pc, pres, heapt, monot, fun T hT ↦ ?_, frt,
      fun _ ↦ ⟨hvec, hnb⟩⟩
    have res₂ : u₂.getMem (s.getReg .x2 - 224) = 0xffffffffffffffff := by rw [hm₂, hm₁]; exact hr
    obtain ⟨T', h1, h2⟩ := A₂.value T hT
    by_cases hc : d < (s.getReg .x12).toNat
    · rw [ite_eq_left hc] at h2
      generalize TM.nextScalar.run T' = o at h2
      rcases o with _ | ⟨x, T''⟩
      · exact absurd (h2.2.symm.trans res₂) (by decide)
      · exact absurd (h2.1.symm.trans tag₂) (by decide)
    · rw [ite_eq_right hc] at h2
      have hdc : (s.getReg .x12).toNat = d := by have := h.le; omega
      rw [hdc, h1]
      refine ⟨fun he ↦ ?_, ⟨hvec, hnb, ?_⟩, trt T' h2⟩
      · rw [ec] at he
        rw [he] at hbuf
        simp only [NewBuf, heapEnd] at hbuf hhi
        have : (errNiche).toNat = 18446744073709551615 := rfl
        rw [this] at hbuf
        omega
      · have ho := hpre.out
        have hof := hpre.outFree
        simp only [vecEs, ep, el, eld]
        exact (DFrame.of_memFrame f).eListAt fun i hi hw ↦ by
          simp only [NewBuf] at hbuf
          addr_omega [hw, hi, ho, hof, hbuf, A₂.room, A₂.mono, hhi]
  · obtain ⟨t, hr₃, pc, pres, ec, f⟩ := finish_err hpre
      (b80004968_pc_taken h₂ (by rw [hres, A₁.x18]; exact hr)) A₂.saved A₂.x8
    obtain ⟨heapt, monot, frt, -, -⟩ := post_of hpre A₂.frame A₂.heap A₂.mono f
    refine ⟨t, hr₁.trans (hr₂.trans hr₃), pc, pres, heapt, monot, fun T hT ↦ ?_, frt,
      fun hne ↦ absurd ec hne⟩
    have hc : d < (s.getReg .x12).toNat := by
      by_contra hc; exact hr (by rw [← hm₁, ← hm₂]; exact A₂.kept (Or.inr hc))
    obtain ⟨T', h1, h2⟩ := A₂.value T hT
    rw [ite_eq_left hc] at h2
    cases hn : TM.nextScalar.run T' with
    | some p => rw [hn] at h2; exact absurd (h2.1.symm.trans tag₂) (by decide)
    | none => rw [nextScalars_fail h1 hn hc]; exact ec

set_option maxHeartbeats 1000000 in
/-- **`Transcript::next_scalars` meets its contract**, given `GenericShunt::next`'s, the
allocator's and `reserve`'s (with its buffer new or kept). -/
theorem next_scalars_spec (hN : ShuntNextSpec) (hA : AllocSpec)
    (hR : ReserveFreshSpec 0x80008a10 24 8) : NextScalarsSpec := by
  intro s hpc hpre
  obtain ⟨u, hsu, ⟨hpcu, hu⟩ | hd⟩ := first hN hpc hpre
  swap
  · exact ⟨u, hsu, Or.inr hd⟩
  by_cases htag : u.getMem (s.getReg .x2 - 152) = 0
  · obtain ⟨t, hut, pc, pres, post⟩ := leave0 hpre hpcu hu htag
    exact ⟨t, hsu.trans hut, Or.inl ⟨pc, pres, post⟩⟩
  obtain ⟨v, huv, ⟨hpcv, cap, ptr, hv⟩ | hd⟩ := start hA hpre hpcu hu htag
  swap
  · exact ⟨v, hsu.trans huv, Or.inr hd⟩
  have hn64 := (s.getReg .x12).isLt
  obtain ⟨t, hvt, ht⟩ := Reaches.loop
    (fun t ↦ ∃ d cap ptr, t.pc = 0x80004908 ∧ Body s t cap ptr d)
    (fun t ↦ (s.getReg .x12).toNat + 1 - (t.getReg .x19).toNat)
    (fun t ↦ (t.pc = returnAddress s ∧ Preserves s t ∧ NextScalarsPost s t) ∨ Dead Image.code t)
    (fun t ⟨d, cap, ptr, hpct, ht⟩ ↦ by
      obtain ⟨w, htw, ⟨hpcw, hw⟩ | hdw⟩ := call hN hpre hpct ht
      swap
      · exact Or.inl ⟨w, htw, Or.inr hdw⟩
      by_cases htg : w.getMem (s.getReg .x2 - 88) = 0
      · obtain ⟨t', hwt, pc, pres, post⟩ := leave hpre hpcw hw htg
        exact Or.inl ⟨t', htw.trans hwt, Or.inl ⟨pc, pres, post⟩⟩
      obtain ⟨q, hwq, ⟨hpcq, htq, cap', ptr', hq, hroom⟩ | hdq⟩ := grow hR hpre hpcw hw htg
      swap
      · exact Or.inl ⟨q, htw.trans hwq, Or.inr hdq⟩
      obtain ⟨v', hqv, hpcv', hv'⟩ := push hpre hpcq hq hroom htq
      refine Or.inr ⟨v', htw.trans (hwq.trans hqv), ⟨d + 1, cap', ptr', hpcv', hv'⟩, ?_⟩
      have h1 := hv'.le
      rw [hv'.x19, ht.x19, toNat_ofNat_of_le h1 hn64, toNat_ofNat_of_le ht.le hn64]
      omega)
    v ⟨1, cap, ptr, hpcv, hv⟩
  exact ⟨t, hsu.trans (huv.trans hvt), ht⟩

end Rv64Verifier.Transcript.NextScalars
