import Rv64Verifier.Proofs.Bus.VbbEnd

/-!
# `verify_bus_balance`: steps that use the transcript

A `StepT` may also write the transcript's sponge and offsets: what `samples`, `next_scalar(s)`,
`duplex` and `sumcheck` do. It keeps `Inv`, the frame's other words and the buffers allocated
since the entry. `tpre` builds the transcript callees' common precondition (`TPre`) for a result in
the frame.
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript

/-- A step writing `Below` or the transcript's sponge and offsets, keeping `sp`. -/
structure StepT (s v w : MachineState) (lo : Word) (n : Nat) : Prop where
  frame : DFrame v w fun a ↦ Below s v w lo n a ∨ Within a (s.getReg .x12 + 8) 344
  heap : HeapOk w
  mono : heapNext v ≤ heapNext w
  sp : w.getReg .x2 = v.getReg .x2

theorem Step.toT {s v w : MachineState} {lo : Word} {n : Nat} (st : Step s v w lo n) :
    StepT s v w lo n :=
  ⟨st.frame.mono fun _ ha ↦ Or.inl ha, st.heap, st.mono, st.sp⟩

theorem Inv.afterT {s v w : MachineState} (hpre : BusBalancePre s) (h : Inv s v) {lo : Word}
    {n : Nat} (hl : InFrame s lo n) (st : StepT s v w lo n) : Inv s w := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hS := hpre.self.self
  have ss := hpre.selfStack
  rw [stackLo_eq] at ss
  refine h.step hpre st.frame (fun a ha ↦ ?_) st.heap st.mono st.sp
  rcases ha with ha | ha
  · exact Loc.w hpre h st.heap (Below.loc hpre hl ha)
  · exact ⟨Or.inr (Or.inl ha), by addr_omega [ha, hS, ss, hb1]⟩

/-- A word in the frame or in a buffer allocated since the entry, apart from what a step writes,
keeps its value. -/
theorem StepT.word {s v w : MachineState} (hpre : BusBalancePre s) {lo : Word} {n : Nat}
    (st : StepT s v w lo n) {x : Word} (hx : Apart x 8 lo n)
    (hy : (s.getReg .x2 - 1344).toNat ≤ x.toNat ∧ x.toNat + 8 ≤ (s.getReg .x2).toNat ∨
      heapNext s ≤ x.toNat ∧ x.toNat + 8 ≤ heapNext v) : w.getMem x = v.getMem x := by
  obtain ⟨hb1, hb2, -, -⟩ := bounds hpre
  have hh := st.heap.hi
  have hm := st.mono
  have hS := hpre.self.self
  have ss := hpre.selfStack
  have sf := hpre.selfFree
  rw [stackLo_eq] at ss
  refine st.frame x fun i hi hw ↦ ?_
  simp only [Below, Fresh, Outside, heapNext, heapEnd] at hw hy hh hm sf
  rcases hy with hy | hy <;> rcases hw with (hw | hw | hw | hw) | hw <;>
    addr_omega [hx, hy, hw, hi, hb1, hb2, hh, hm, hS, ss, sf]

theorem StepT.bufWord {s v w : MachineState} (hpre : BusBalancePre s) {lo : Word} {n : Nat}
    (st : StepT s v w lo n) (hl : InFrame s lo n) {p x : Word} {m : Nat}
    (hb : NewBuf s v p m 8) (h1 : p.toNat ≤ x.toNat) (h2 : x.toNat + 8 ≤ p.toNat + m) :
    w.getMem x = v.getMem x := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hhi := st.heap.hi
  simp only [NewBuf, InFrame] at hb hl
  rcases hb.2 with h0 | ⟨b1, b2⟩
  · omega
  refine st.word hpre ?_ (Or.inr ⟨by omega, by omega⟩)
  simp only [heapNext, heapEnd] at b1 b2 hhi
  have hm := st.mono
  simp only [heapNext] at hm
  addr_omega [b1, b2, h1, h2, hl, hb1, hhi, hm]

theorem LayoutAt.keepT {s v w : MachineState} (hpre : BusBalancePre s) {lo : Word} {n : Nat}
    (st : StepT s v w lo n) (hl : InFrame s lo n) {a : Word} {l : BusLayoutRust}
    (h : LayoutAt s v a l) (hin : InFrame s a 56) (hap : Apart a 56 lo n) : LayoutAt s w a l := by
  obtain ⟨hb1, hb2, -, -⟩ := bounds hpre
  simp only [InFrame] at hin
  have hw (j : Nat) (hj : j + 8 ≤ 56) : w.getMem (a + BitVec.ofNat 64 j) =
      v.getMem (a + BitVec.ofNat 64 j) :=
    st.word hpre (by addr_omega [hap, hin, hj, hb1]) (Or.inl (by addr_omega [hin, hj, hb1]))
  have e0 : w.getMem a = v.getMem a := by simpa using hw 0 (by omega)
  have e8 : w.getMem (a + 8) = v.getMem (a + 8) := hw 8 (by omega)
  have e16 : w.getMem (a + 16) = v.getMem (a + 16) := hw 16 (by omega)
  have e24 : w.getMem (a + 24) = v.getMem (a + 24) := hw 24 (by omega)
  have e32 : w.getMem (a + 24 + 8) = v.getMem (a + 24 + 8) := by
    rw [BitVec.add_assoc]; exact hw 32 (by omega)
  have e40 : w.getMem (a + 24 + 16) = v.getMem (a + 24 + 16) := by
    rw [BitVec.add_assoc]; exact hw 40 (by omega)
  have e48 : w.getMem (a + 48) = v.getMem (a + 48) := hw 48 (by omega)
  have hm := st.mono
  have pk {b : Word} (hv : VecOk v b 16 8)
      (hb : NewBuf s v (vecPtr v b) (16 * (vecCap v b).toNat) 8)
      (h8 : w.getMem (b + 8) = v.getMem (b + 8)) (h16 : w.getMem (b + 16) = v.getMem (b + 16)) :
      placementsAt w b = placementsAt v b := by
    have hlen := hv.len
    simp only [placementsAt, vecPtr, vecLen] at hb hlen ⊢
    rw [h8, h16]
    refine List.map_congr_left fun i hi ↦ ?_
    simp only [List.mem_range] at hi
    have hc : 16 * i + 16 ≤ 16 * (vecCap v b).toNat := by omega
    have hbd : (v.getMem (b + 8)).toNat + 16 * (vecCap v b).toNat ≤ 2 ^ 64 := by
      rcases hb.2 with h0 | ⟨b1, b2⟩
      · omega
      · have := st.heap.hi
        simp only [heapNext, heapEnd] at *; omega
    rw [st.bufWord hpre hl hb (by addr_omega [hbd, hc]) (by addr_omega [hbd, hc]),
      st.bufWord hpre hl hb (by addr_omega [hbd, hc]) (by addr_omega [hbd, hc])]
  refine ⟨?_, h.framework.keep e0 e8 e16 hm, ?_, h.tables.keep e24 e32 e40 hm, ?_⟩
  · rw [← h.value]
    simp only [busLayoutOf, e48]
    rw [pk h.framework h.frameworkNew e8 e16, pk h.tables h.tablesNew e32 e40]
  · have := h.frameworkNew
    simp only [NewBuf, vecPtr, vecCap] at this ⊢
    rw [e8, e0]
    exact ⟨this.1, this.2.imp_right fun h' ↦ ⟨h'.1, by omega⟩⟩
  · have := h.tablesNew
    simp only [NewBuf, vecPtr, vecCap] at this ⊢
    rw [e32, e24]
    exact ⟨this.1, this.2.imp_right fun h' ↦ ⟨h'.1, by omega⟩⟩

/-- The precondition of a transcript callee with an `m`-byte stack, its `n`-byte result at
`S - k` in the frame. -/
theorem tpre {s u : MachineState} (hpre : BusBalancePre s) (h : Inv s u) {k n m : Nat}
    (hk1 : 104 + n ≤ k) (hk2 : k ≤ 1344) (hk8 : k % 8 = 0) (hm : 1344 + m ≤ 4544)
    (hm8 : m % 8 = 0)
    (h10 : u.getReg .x10 = s.getReg .x2 - BitVec.ofNat 64 k)
    (h11 : u.getReg .x11 = s.getReg .x12) : TPre n m u := by
  obtain ⟨hb1, hb2, -, -⟩ := bounds hpre
  obtain ⟨o1, o2, o3⟩ := frameSlot (m := m) hpre h hk1 hk2 hk8 hm
  obtain ⟨e0, e1, e2⟩ := h.stream hpre
  have hsl : stackLo u m = s.getReg .x2 - BitVec.ofNat 64 (1344 + m) := by
    simp only [stackLo, h.sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1, hm]
  have ss := hpre.selfStack
  have ps := hpre.proofStack
  have hS := hpre.self.self
  have hr := hpre.stack.rodata
  have hrb : rodataBase.toNat = 2684354560 := rfl
  rw [stackLo_eq] at ss ps hr
  simp only [ProofApart] at ps
  have mono := h.mono
  refine ⟨h.heap, h10 ▸ o1, h11 ▸ h.tok hpre,
    hpre.stack.sub 1344 h.sp (by rw [stack_eq]; omega) (by decide) hm8 (by decide) (by decide),
    h10 ▸ o3, ?_,
    ?_, ?_, ?_, h10 ▸ o2, ?_, ?_, ?_, h.rodata hpre, ?_, ?_⟩
  · rw [h11, hsl]; addr_omega [ss, hS, hb1, hm]
  · rw [h10, h11]; addr_omega [ss, hS, hb1, hk1, hk2]
  · rw [h11]; simp only [ProofApart, e0, e1, e2, hsl]
    exact ⟨by addr_omega [ps.1, hb1, hm], by addr_omega [ps.2, hb1, hm]⟩
  · rw [h11]; simp only [ProofApart, e0, e1, e2, h10]
    exact ⟨by addr_omega [ps.1, hb1, hk1, hk2], by addr_omega [ps.2, hb1, hk1, hk2]⟩
  · rw [h11]; exact outside_mono hpre.selfFree mono
  · rw [h11, e0]; exact outside_mono hpre.proofFree mono
  · rw [h11, e1, e2]; exact outside_mono hpre.streamFree mono
  · rw [h10]; simp only [rodataSize] at hr ⊢; addr_omega [hr, hrb, hb1, hk1, hk2]
  · rw [h11]; exact hpre.selfRodata

/-- A transcript callee's frame (`TFrame`) as a `StepT`, its result at `S - k`. -/
theorem TFrame.stepT {s u v : MachineState} (hpre : BusBalancePre s) (h : Inv s u) {k n m : Nat}
    (hm : 1344 + m ≤ 4544) (h10 : u.getReg .x10 = s.getReg .x2 - BitVec.ofNat 64 k)
    (h11 : u.getReg .x11 = s.getReg .x12) (hf : TFrame n m u v) (hheap : HeapOk v)
    (hmono : heapNext u ≤ heapNext v) (hsp : v.getReg .x2 = u.getReg .x2) :
    StepT s u v (s.getReg .x2 - BitVec.ofNat 64 k) n := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  refine ⟨hf.mono fun a ha ↦ ?_, hheap, hmono, hsp⟩
  simp only [stackLo, h.sp, h10, h11] at ha
  rcases ha with ha | ha | ha | ha | ha
  · exact Or.inl (Or.inl ha)
  · exact Or.inr ha
  · exact Or.inl (Or.inr (Or.inl (by addr_omega [ha, hb1, hm])))
  · exact Or.inl (Or.inr (Or.inr (Or.inl ha)))
  · exact Or.inl (Or.inr (Or.inr (Or.inr ha)))

/-- A call of `Transcript::samples`, its `Vec` at `S - k`. -/
theorem samplesCall (hS : SamplesSpec) {s u₀ u : MachineState} (hpre : BusBalancePre s)
    (h : Inv s u) (hr : Reaches Image.code u₀ u) (hpc : u.pc = 0x8000c618) {k : Nat}
    (h10 : u.getReg .x10 = s.getReg .x2 - BitVec.ofNat 64 k) (h11 : u.getReg .x11 = s.getReg .x12)
    (hk1 : 128 ≤ k) (hk2 : k ≤ 1344) (hk8 : k % 8 = 0) :
    ∃ v, Reaches Image.code u₀ v ∧ ((v.pc = returnAddress u ∧ Preserves u v ∧
      StepT s u v (s.getReg .x2 - BitVec.ofNat 64 k) 24 ∧ Inv s v ∧
      ∀ T, TranscriptAt u (s.getReg .x12) T → ∃ xs T',
        (TM.samples (u.getReg .x12).toNat).run T = some (xs, T') ∧
        NewVecE u v (s.getReg .x2 - BitVec.ofNat 64 k) xs ∧ TranscriptAt v (s.getReg .x12) T') ∨
      Dead Image.code v) := by
  have pre : SamplesPre u := tpre hpre h (n := 24) (m := samplesStack) (by omega) hk2 hk8
    (by decide) (by decide) h10 h11
  obtain ⟨v, hrv, ⟨hpcv, hp, post⟩ | hd⟩ := hS.call hr hpc pre
  · have st := TFrame.stepT hpre h (by decide) h10 h11 post.frame post.heap post.mono (hp.reg .x2)
    refine ⟨v, hrv, Or.inl ⟨hpcv, hp, st,
      h.afterT hpre (inFrame hpre (by omega) hk2) st, fun T hT ↦ ?_⟩⟩
    obtain ⟨xs, T', h1, h2, h3⟩ := post.value T (h11 ▸ hT)
    exact ⟨xs, T', h1, h10 ▸ h2, h11 ▸ h3⟩
  · exact ⟨v, hrv, Or.inr hd⟩

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
