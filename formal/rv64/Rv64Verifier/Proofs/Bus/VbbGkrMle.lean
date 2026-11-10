import Rv64Verifier.Proofs.Bus.VbbGkrCheck
import Rv64Verifier.Proofs.Multilinear.Bridges

/-!
# `verify_bus_balance`: an iteration's `multilinear_eval` calls

A call of `multilinear_eval` on two `Vec<E>`s in the heap, non-empty, its result at `S - 608`
(`mleCall`); a step that also writes `values`' first 72 bytes at `P`, below what the iteration
allocates, keeps the transcript (`Inv.transcriptS`) and the iteration's buffers (`keepP`).
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F26

/-- A step writing the stack, `NEXT` and the heap allocated since the entry keeps the
transcript. -/
theorem Inv.transcriptS {s u v : MachineState} (hpre : BusBalancePre s) (h : Inv s u)
    (hv : HeapOk v) (hf : DFrame u v (Loc s s v)) {T : TState}
    (hT : TranscriptAt u (s.getReg .x12) T) : TranscriptAt v (s.getReg .x12) T := by
  obtain ⟨e0, e1, e2⟩ := h.stream hpre
  have hS := hpre.self.self
  have ss := hpre.selfStack
  have sf := hpre.selfFree
  have ps := hpre.proofStack
  have pf := hpre.proofFree
  have bf := hpre.streamFree
  have hn := hv.hi
  rw [stackLo_eq, stack_eq] at ss ps
  simp only [ProofApart] at ps
  simp only [Outside, heapNext, heapEnd] at pf bf sf hn
  have loc (lo : Word) (n : Nat) (h1 : Apart lo n (s.getReg .x2 - 4544) 4544)
      (h2 : Apart lo n nextAddr 8) (h3 : lo.toNat + n ≤ (s.getMem nextAddr).toNat ∨
        0x78000000 ≤ lo.toNat) : Misses (Loc s s v) lo n := fun y hy hl ↦ by
    simp only [Loc, Fresh, heapNext] at hl
    rcases hl with hl | hl | hl
    · addr_omega [hy, hl, h1]
    · addr_omega [hy, hl, h2]
    · addr_omega [hy, hl, h3, hn]
  refine hf.transcriptAt hT (h.tok hpre) (loc _ _ (by addr_omega [ss, hS])
    (by addr_omega [sf.2, hS]) (by addr_omega [sf.1, hS])) ?_ ?_
    (loc _ _ (by addr_omega [ss, hS]) (by addr_omega [sf.2, hS]) (by addr_omega [sf.1, hS]))
  · rw [e0]; exact loc _ _ ps.1 pf.2 pf.1
  · rw [e1, e2]; exact loc _ _ ps.2 bf.2 bf.1

section KeepP
variable {s u v w : MachineState} {A : Word → Prop} {P : Word}

/-- A `Vec<E>` held in registers, its buffer allocated since `u`, above `values`' first 72 bytes,
keeps what it holds through a step writing the frame and those bytes. -/
theorem NewVecR.keepP (hpre : BusBalancePre s) (hu : heapNext s ≤ heapNext u)
    (hP : P.toNat + 72 ≤ heapNext u) (st : StepR s v w A)
    (hA : ∀ a, A a → Within a (s.getReg .x2 - 1344) 1240 ∨ Within a P 72) {c p l : Word}
    {xs : List E} (h : NewVecR u v c p l xs) : NewVecR u w c p l xs := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hb := h.buf
  have hl := h.le
  have hm := st.mono
  refine ⟨hl, ⟨hb.1, hb.2.imp_right fun h' ↦ ⟨h'.1, by omega⟩⟩, ?_⟩
  rw [← h.elems]
  refine eListAt_congr fun i hi ↦ ?_
  simp only [NewBuf] at hb
  rcases hb.2 with h0 | ⟨b1, b2⟩
  · omega
  have hh := st.heap.hi
  simp only [heapNext, heapEnd] at b1 b2 hh hm hP hu
  have hc : 24 * i + 24 ≤ c.toNat * 24 := by omega
  have bw (j : Nat) (hj : j + 8 ≤ 24) : w.getMem (p + BitVec.ofNat 64 (24 * i) +
      BitVec.ofNat 64 j) = v.getMem (p + BitVec.ofNat 64 (24 * i) + BitVec.ofNat 64 j) := by
    refine st.word hpre (fun y hy hy' ↦ ?_) (Or.inr ⟨?_, ?_⟩)
    · rcases hA y hy' with ha | ha
      · addr_omega [ha, hy, hb1, b1, b2, hc, hj, hh, hm]
      · addr_omega [ha, hy, hP, b1, b2, hc, hj]
    · simp only [heapNext]; addr_omega [b1, b2, hc, hj, hu]
    · simp only [heapNext]; addr_omega [b1, b2, hc, hj]
  exact eAt_congr (by simpa using bw 0 (by omega)) (bw 8 (by omega)) (bw 16 (by omega))

theorem HeapVec.keepP (hpre : BusBalancePre s) (hu : heapNext s ≤ heapNext u)
    (hP : P.toNat + 72 ≤ heapNext u) (st : StepR s v w A)
    (hA : ∀ a, A a → Within a (s.getReg .x2 - 1344) 1240 ∨ Within a P 72) {p l : Word}
    {xs : List E} (h : HeapVec u v p l xs) : HeapVec u w p l xs := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, hc.keepP hpre hu hP st hA⟩

/-- A `Vec<E>` in the frame apart from what a step writes, its buffer as `NewVecR.keepP`'s. -/
theorem _root_.Rv64Verifier.Transcript.NewVecE.keepP (hpre : BusBalancePre s)
    (hu : heapNext s ≤ heapNext u) (hP : P.toNat + 72 ≤ heapNext u) (st : StepR s v w A)
    (hA : ∀ a, A a → Within a (s.getReg .x2 - 1344) 1240 ∨ Within a P 72) {j : Nat}
    (hj1 : 128 ≤ j) (hj2 : j ≤ 1344)
    (hap : ∀ y, Within y (s.getReg .x2 - BitVec.ofNat 64 j) 24 → ¬ A y) {xs : List E}
    (h : NewVecE u v (s.getReg .x2 - BitVec.ofNat 64 j) xs) :
    NewVecE u w (s.getReg .x2 - BitVec.ofNat 64 j) xs := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hw (i : Nat) (hi : i + 8 ≤ 24) : w.getMem (s.getReg .x2 - BitVec.ofNat 64 j +
      BitVec.ofNat 64 i) = v.getMem (s.getReg .x2 - BitVec.ofNat 64 j + BitVec.ofNat 64 i) :=
    st.word hpre (fun y hy ↦ hap y (by addr_omega [hy, hb1, hj1, hj2, hi]))
      (Or.inl (by addr_omega [hb1, hj1, hj2, hi]))
  have e0 : w.getMem (s.getReg .x2 - BitVec.ofNat 64 j) =
      v.getMem (s.getReg .x2 - BitVec.ofNat 64 j) := by simpa using hw 0 (by omega)
  have e8 : w.getMem (s.getReg .x2 - BitVec.ofNat 64 j + 8) =
      v.getMem (s.getReg .x2 - BitVec.ofNat 64 j + 8) := hw 8 (by omega)
  have e16 : w.getMem (s.getReg .x2 - BitVec.ofNat 64 j + 16) =
      v.getMem (s.getReg .x2 - BitVec.ofNat 64 j + 16) := hw 16 (by omega)
  have hvec := h.vec
  have hr : NewVecR u v (vecCap v (s.getReg .x2 - BitVec.ofNat 64 j))
      (vecPtr v (s.getReg .x2 - BitVec.ofNat 64 j)) (vecLen v (s.getReg .x2 - BitVec.ofNat 64 j))
      xs := ⟨hvec.len, h.buf, h.elems⟩
  have hr' := hr.keepP hpre hu hP st hA
  refine ⟨hvec.keep e0 e8 e16 st.mono, ?_, ?_⟩
  · simp only [vecPtr, vecCap, e0, e8]
    exact hr'.buf
  · simp only [vecEs, vecPtr, vecLen, e8, e16]
    exact hr'.elems

end KeepP

/-- A `Vec<E>` in the heap, non-empty, read only by `multilinear_eval`. -/
theorem heldHeap {s u : MachineState} (hpre : BusBalancePre s) (h : Inv s u) {c p l : Word}
    {xs : List E} (hm : NewVecR s u c p l xs) (hl : 0 < l.toNat) :
    Held u Vbb.mleEvalStack p (24 * l.toNat) ∧
      Apart p (24 * l.toNat) (s.getReg .x2 - BitVec.ofNat 64 608) 32 ∧
      p.toNat + 24 * l.toNat ≤ 0xc0000000 := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hb := hm.buf
  have hlc := hm.le
  have hh := h.heap.hi
  have hlo := h.heap.lo
  have hsl : stackLo u Vbb.mleEvalStack = s.getReg .x2 - BitVec.ofNat 64 2576 := by
    have : Vbb.mleEvalStack = 1232 := rfl
    simp only [stackLo, this, h.sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  simp only [NewBuf] at hb
  rcases hb.2 with h0 | ⟨b1, b2⟩
  · omega
  simp only [heapNext, heapEnd, heapStart] at hh hlo b1 b2
  have hs := hpre.heap.lo
  simp only [heapNext, heapStart] at hs
  refine ⟨⟨?_, ⟨Or.inl ?_, ?_⟩, ?_⟩, ?_, ?_⟩
  · rw [show 24 * l.toNat / 8 = 3 * l.toNat by omega]
    exact heapRange hb.1 (by simp only [heapStart]; omega) (by simp only [heapEnd]; omega)
  · simp only [heapNext]; omega
  · addr_omega [b1, b2, hh, hlc]
  · rw [hsl]; addr_omega [b1, b2, hh, hb1, hlc]
  · addr_omega [b1, b2, hh, hb1, hlc]
  · omega

/-- A call of `multilinear_eval` on two non-empty `Vec<E>`s in the heap, into `S - 608`. -/
theorem mleCall (hME : FunSpec Image.code 0x8000d28c
      (fun s ↦ Vbb.MleEvalPre s ∧ Rv64Verifier.Proofs.Multilinear.Bridges.MleEnds s)
      Vbb.MleEvalPost)
    {s u₀ u : MachineState} (hpre : BusBalancePre s) (h : Inv s u) (hr : Reaches Image.code u₀ u)
    (hpc : u.pc = 0x8000d28c) (h10 : u.getReg .x10 = s.getReg .x2 - BitVec.ofNat 64 608)
    {c p l c' p' l' : Word} {xs ys : List E} (hm : NewVecR s u c p l xs) (hl : 0 < l.toNat)
    (h11 : u.getReg .x11 = p) (h12 : u.getReg .x12 = l) (hy : NewVecR s u c' p' l' ys)
    (hl' : 0 < l'.toNat) (h13 : u.getReg .x13 = p') (h14 : u.getReg .x14 = l') :
    ∃ v, Reaches Image.code u₀ v ∧ ((v.pc = returnAddress u ∧ Preserves u v ∧
      StepR s u v (Within · (s.getReg .x2 - BitVec.ofNat 64 608) 32) ∧
      (match multilinearEvalRust xs ys with
        | some e => v.getMem (s.getReg .x2 - BitVec.ofNat 64 608) = 0 ∧
            eAt v (s.getReg .x2 - BitVec.ofNat 64 608 + 8) = e
        | none => v.getMem (s.getReg .x2 - BitVec.ofNat 64 608) ≠ 0) ∧
      ∀ T, TranscriptAt u (s.getReg .x12) T → TranscriptAt v (s.getReg .x12) T) ∨
      Dead Image.code v) := by
  obtain ⟨hb1, -, hb3, -⟩ := bounds hpre
  obtain ⟨o1, o2, o3⟩ := frameSlot (m := Vbb.mleEvalStack) hpre h (k := 608) (n := 32)
    (by omega) (by omega) (by omega) (by decide)
  have hsl : stackLo u Vbb.mleEvalStack = s.getReg .x2 - BitVec.ofNat 64 2576 := by
    have : Vbb.mleEvalStack = 1232 := rfl
    simp only [stackLo, this, h.sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have hst := hpre.stack.rodata
  have hrb : rodataBase.toNat = 2684354560 := rfl
  rw [stackLo_eq] at hst
  have rs : RtStack u Vbb.mleEvalStack :=
    hpre.stack.sub 1344 h.sp (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨H1, A1, E1⟩ := heldHeap hpre h hm hl
  obtain ⟨H2, A2, E2⟩ := heldHeap hpre h hy hl'
  have pre : Vbb.MleEvalPre u := {
    heap := h.heap
    stack := rs
    rodata := h.rodata hpre
    out := by rw [h10]; exact o1
    outFree := by rw [h10]; exact o2
    outStack := by rw [h10]; exact o3
    outRodata := by rw [h10]; simp only [rodataSize] at hst ⊢; addr_omega [hst, hrb, hb1]
    mle := by rw [h11, h12]; exact H1
    mleOut := by rw [h11, h12, h10]; exact A1
    point := by rw [h13, h14]; exact H2
    pointOut := by rw [h13, h14, h10]; exact A2 }
  have ends : Rv64Verifier.Proofs.Multilinear.Bridges.MleEnds u := by
    simp only [Rv64Verifier.Proofs.Multilinear.Bridges.MleEnds, h11, h12, h13, h14]
    exact ⟨Or.inr E1, Or.inr E2⟩
  obtain ⟨v, hrv, ⟨hpcv, hp, post⟩ | hd⟩ := hME.call hr hpc ⟨pre, ends⟩
  swap
  · exact ⟨v, hrv, Or.inr hd⟩
  have fr : DFrame u v fun x ↦ Within x (s.getReg .x2 - BitVec.ofNat 64 608) 32 ∨
      Within x (s.getReg .x2 - BitVec.ofNat 64 2576) 1232 ∨ Within x nextAddr 8 ∨ Fresh u v x :=
    post.frame.mono fun x hx ↦ by
      rw [h10, hsl, show Vbb.mleEvalStack = 1232 from rfl] at hx; exact hx
  have hx := hpre.stack.next
  rw [stackLo_eq] at hx
  have hv : HeapOk v := post.heap
  refine ⟨v, hrv, Or.inl ⟨hpcv, hp, ⟨fr.mono fun x hx ↦ ?_, hv, post.mono, hp.reg .x2⟩, ?_,
    fun T hT ↦ h.transcript hpre hv (fr.mono fun x hx ↦ ?_) hT⟩⟩
  · rcases hx with hx | hx | hx | hx
    · exact Or.inl hx
    · exact Or.inr (Or.inr (Or.inl (by addr_omega [hx, hb1])))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hx)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr hx)))
  · have := post.value
    rw [h10, h11, h12, h13, h14, hm.elems, hy.elems] at this
    exact this
  · rcases hx with hx | hx | hx | hx
    · exact Or.inl (by addr_omega [hx, hb1])
    · exact Or.inl (by addr_omega [hx, hb1])
    · exact Or.inr (Or.inl hx)
    · exact Or.inr (Or.inr hx)

/-- An `Err` of a `multilinear_eval`, through `0x80006c0c`. -/
theorem errMle {bev : MachineState → Word → List E → Option E} {s t : MachineState} {k : Start}
    {cnt : E} {P : Word} (hpre : BusBalancePre s) (C : Ctx s t k cnt P) (hpc : t.pc = 0x80006c0c)
    (hnone : ∀ T, TranscriptAt s (s.getReg .x12) T → (prog bev s).run T = none) :
    ∃ t', Reaches Image.code t t' ∧ Done bev s t' := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  have sp := C.inv.sp
  obtain ⟨t₁, hr, h₁⟩ := Sym.BlockSpec.reaches b80006c0c_spec hpc (by
    rv_eval [sp]
    and_intros <;> valid_access hval [hb1])
  have m₁ := b80006c0c_mem_same h₁
  have k₁ := b80006c0c_keeps h₁ .x2 (by decide)
  obtain ⟨t', hr', hd⟩ := err7100 hpre (C.inv.same m₁ k₁)
    (C.kept.step hpre (StepR.same m₁ C.inv.heap k₁)) (b80006c0c_pc h₁) hnone
  exact ⟨t', hr.trans hr', hd⟩

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
