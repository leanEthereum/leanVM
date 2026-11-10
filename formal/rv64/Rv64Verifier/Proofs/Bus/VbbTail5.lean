import Rv64Verifier.Proofs.Bus.VbbTail4

/-!
# `verify_bus_balance` past the GKR loop: `to_vec`'s calls

The rest inlines `point[..n].to_vec()` as `try_allocate_in(S - 608, n, 0, 8, 24)` and a `memcpy`
into the new buffer. `tryAllocCall` is the first, `memcpyCall` the second; `StepS.copy` makes the
two one step from before the allocation, the copy's bytes then allocated since. Past the
scalars nothing writes the transcript: a `StepS` keeps it.
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript

/-- A call of `try_allocate_in(S - 608, n, _, 8, 24)`: on `Ok` (tag `0`) a new buffer of `n`
elements, its capacity `n`. -/
theorem tryAllocCall (hT : TryAllocZeroedSpec) {s u₀ u : MachineState} (hpre : BusBalancePre s)
    (h : Inv s u) (hr : Reaches Image.code u₀ u) (hpc : u.pc = 0x800049ac)
    (h10 : u.getReg .x10 = s.getReg .x2 - BitVec.ofNat 64 608) (h13 : u.getReg .x13 = 8)
    (h14 : u.getReg .x14 = 24) :
    ∃ v, Reaches Image.code u₀ v ∧ ((v.pc = returnAddress u ∧ Preserves u v ∧
      Step s u v (s.getReg .x2 - BitVec.ofNat 64 608) 24 ∧ Inv s v ∧
      (v.getMem (s.getReg .x2 - BitVec.ofNat 64 608) = 0 →
        v.getMem (s.getReg .x2 - BitVec.ofNat 64 608 + 8) = u.getReg .x11 ∧
        NewBuf u v (v.getMem (s.getReg .x2 - BitVec.ofNat 64 608 + 16))
          ((u.getReg .x11).toNat * 24) 8)) ∨ Dead Image.code v) := by
  obtain ⟨hb1, -, hb3, -⟩ := bounds hpre
  obtain ⟨o1, o2, o3⟩ := frameSlot (m := tryAllocStack) hpre h (n := 24) (k := 608) (by omega)
    (by omega) (by omega) (by decide)
  have pre : TryAllocPre .x13 .x14 u := {
    heap := h.heap
    out := by
      rw [h10]; exact regionRange o1 (Nat.le_refl _) (by omega) (by addr_omega [hb1, hb3])
    align := by rw [h13]; decide
    size := by rw [h14]; decide
    stack := hpre.stack.sub 1344 h.sp (by decide) (by decide) (by decide) (by decide) (by decide)
    outFree := h10 ▸ o2
    outStack := h10 ▸ o3 }
  obtain ⟨v, hrv, ⟨hpcv, hp, post, -⟩ | hd⟩ := hT.call hr hpc pre
  swap
  · exact ⟨v, hrv, Or.inr hd⟩
  have hsl : stackLo u tryAllocStack = s.getReg .x2 - BitVec.ofNat 64 (1344 + 48) := by
    simp only [stackLo, h.sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have st : Step s u v (s.getReg .x2 - BitVec.ofNat 64 608) 24 := by
    refine ⟨fun x hx ↦ post.frame.getMem fun i hi hw ↦ hx i hi ?_, post.heap, post.mono, hp.reg .x2⟩
    rw [hsl, h10] at hw
    rcases hw with hw | hw | hw | hw
    · exact Or.inl hw
    · exact Or.inr (Or.inl (by addr_omega [hw, hb1]))
    · exact Or.inr (Or.inr (Or.inl hw))
    · exact Or.inr (Or.inr (Or.inr hw))
  refine ⟨v, hrv, Or.inl ⟨hpcv, hp, st, h.after hpre (inFrame hpre (by omega) (by omega)) st,
    fun h0 ↦ ?_⟩⟩
  have hok := post.ok (by rw [h10]; exact h0)
  rw [h10, h13, h14] at hok
  exact hok

/-- A call of `memcpy` from a buffer allocated before `y` to one allocated since, both in the
heap: the bytes copied, as `n` elements. -/
theorem memcpyCall (hM : MemcpySpec 0x800126e4) {s y u₀ u : MachineState} (hpre : BusBalancePre s)
    (h : Inv s u) (hr : Reaches Image.code u₀ u) (hpc : u.pc = 0x800126e4) {n : Nat}
    (hn : (u.getReg .x12).toNat = 24 * n) (hd : heapNext y ≤ (u.getReg .x10).toNat)
    (hd' : (u.getReg .x10).toNat + 24 * n ≤ heapNext u)
    (hs : heapStart ≤ (u.getReg .x11).toNat) (hs' : (u.getReg .x11).toNat + 24 * n ≤ heapNext y)
    (hda : (u.getReg .x10).toNat % 8 = 0) (hsa : (u.getReg .x11).toNat % 8 = 0) :
    ∃ v, Reaches Image.code u₀ v ∧ ((v.pc = returnAddress u ∧ Preserves u v ∧
      DFrame u v (fun a ↦ Within a (u.getReg .x10) (24 * n) ∨
        Within a (s.getReg .x2 - BitVec.ofNat 64 1360) 16) ∧
      heapNext v = heapNext u ∧ v.getReg .x2 = u.getReg .x2 ∧
      eListAt v (u.getReg .x10) n = eListAt u (u.getReg .x11) n) ∨ Dead Image.code v) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hh := h.heap.hi
  have hlo := hpre.heap.lo
  have hm := h.mono
  have hy : heapStart ≤ heapNext y := Nat.le_trans hs (by omega)
  simp only [heapNext, heapEnd, heapStart] at hh hlo hm hd hd' hs hs' hy
  have hsl : stackLo u memcpyStack = s.getReg .x2 - BitVec.ofNat 64 1360 := by
    simp only [stackLo, h.sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have hst := hpre.stack.above
  rw [stackLo_eq] at hst
  simp only [heapEnd] at hst
  have pre : MemcpyPre u := {
    dst := by rw [hn]; simp only [Mapped]; omega
    src := by rw [hn]; simp only [Mapped]; omega
    apart := by rw [hn]; addr_omega [hd, hs']
    stack := ⟨by
        rw [hsl]
        refine ValidMemRange.sub hpre.stack.valid ?_ ?_ ?_ <;> rw [stackLo_eq] <;>
          addr_omega [hb1],
      by rw [h.sp]; have := hpre.stack.aligned; addr_omega [hb1, this]⟩
    dstStack := by rw [hn, hsl]; addr_omega [hd', hh, hst, hb1]
    srcStack := by rw [hn, hsl]; addr_omega [hs', hd, hd', hy, hh, hm, hst, hb1] }
  obtain ⟨v, hrv, ⟨hpcv, hp, post⟩ | hdd⟩ := hM.call hr hpc pre
  swap
  · exact ⟨v, hrv, Or.inr hdd⟩
  have fr := post.frame
  rw [hn, hsl] at fr
  have hx := hpre.stack.next
  rw [stackLo_eq] at hx
  have hnx : heapNext v = heapNext u := by
    simp only [heapNext]
    exact congrArg BitVec.toNat (fr.getMem fun i hi hw ↦ by
      rcases hw with hw | hw <;> addr_omega [hw, hi, hd', hh, hx, hb1])
  have hby := post.bytes
  rw [hn] at hby
  refine ⟨v, hrv, Or.inl ⟨hpcv, hp, fun a ha ↦ fr.getMem ha, hnx, hp.reg .x2, ?_⟩⟩
  exact eListAt_eq_of_bytesAt hby hda hsa

/-! ## Steps that leave the transcript alone

Past the scalars nothing writes the transcript: a `StepS` writes the frame's `A`, the stack below
the frame, `NEXT` and the heap it allocates, and keeps what the transcript stands for. -/

structure StepS (s v w : MachineState) (A : Word → Prop) : Prop where
  frame : DFrame v w fun a ↦ A a ∨ Within a (s.getReg .x2 - 4544) 3200 ∨ Within a nextAddr 8 ∨
    Fresh v w a
  heap : HeapOk w
  mono : heapNext v ≤ heapNext w
  sp : w.getReg .x2 = v.getReg .x2

section StepS
variable {s u v w : MachineState} {A B : Word → Prop}

theorem StepS.toR (st : StepS s v w A) : StepR s v w A :=
  ⟨st.frame.mono fun a ha ↦ by
    rcases ha with ha | ha | ha | ha
    · exact Or.inl ha
    · exact Or.inr (Or.inr (Or.inl ha))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ha))), st.heap, st.mono, st.sp⟩

theorem Step.toS {lo : Word} {n : Nat} (st : Step s v w lo n) : StepS s v w (Within · lo n) :=
  ⟨st.frame, st.heap, st.mono, st.sp⟩

theorem StepS.weaken (h : StepS s v w A) (hAB : ∀ a, A a → B a) : StepS s v w B :=
  ⟨h.frame.mono fun a ha ↦ ha.imp_left (hAB a), h.heap, h.mono, h.sp⟩

theorem StepS.trans (h₁ : StepS s u v A) (h₂ : StepS s v w B) :
    StepS s u w fun a ↦ A a ∨ B a where
  frame := (h₁.frame.mono fun a ha ↦ by
      rcases ha with ha | ha | ha | ⟨f1, f2⟩
      · exact Or.inl (Or.inl ha)
      · exact Or.inr (Or.inl ha)
      · exact Or.inr (Or.inr (Or.inl ha))
      · exact Or.inr (Or.inr (Or.inr ⟨f1, by have := h₂.mono; omega⟩))).trans
    h₂.frame fun a ha ↦ by
      rcases ha with ha | ha | ha | ⟨f1, f2⟩
      · exact Or.inl (Or.inr ha)
      · exact Or.inr (Or.inl ha)
      · exact Or.inr (Or.inr (Or.inl ha))
      · exact Or.inr (Or.inr (Or.inr ⟨by have := h₁.mono; omega, f2⟩))
  heap := h₂.heap
  mono := h₁.mono.trans h₂.mono
  sp := h₂.sp.trans h₁.sp

/-- A block that writes nothing. -/
theorem StepS.same (hm : ∀ a, w.getMem a = v.getMem a) (hh : HeapOk v)
    (sp : w.getReg .x2 = v.getReg .x2) : StepS s v w A := by
  have hn : heapNext w = heapNext v := by simp only [heapNext, hm]
  exact ⟨DFrame.of_same hm _, ⟨hn ▸ hh.lo, hn ▸ hh.hi⟩, hn.ge, sp⟩

/-- A block that writes only `B`, in `A`, apart from `NEXT`. -/
theorem StepS.ofDFrame (hh : HeapOk v) (hf : DFrame v w B) (hA : ∀ a, B a → A a)
    (hn : ∀ i < 8, ¬ B (nextAddr + BitVec.ofNat 64 i)) (sp : w.getReg .x2 = v.getReg .x2) :
    StepS s v w A := by
  have he : heapNext w = heapNext v := by simp only [heapNext]; rw [hf nextAddr hn]
  exact ⟨hf.mono fun a ha ↦ Or.inl (hA a ha), ⟨he ▸ hh.lo, he ▸ hh.hi⟩, he.ge, sp⟩

theorem StepS.transcript (hpre : BusBalancePre s) (h : Inv s v) (hA : FrameW s A)
    (st : StepS s v w A) {T : TState} (hT : TranscriptAt v (s.getReg .x12) T) :
    TranscriptAt w (s.getReg .x12) T := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  refine h.transcript hpre st.heap (st.frame.mono fun a ha ↦ ?_) hT
  rcases ha with ha | ha | ha | ha
  · have := hA a ha
    exact Or.inl (by addr_omega [this, hb1])
  · exact Or.inl (by addr_omega [ha, hb1])
  · exact Or.inr (Or.inl ha)
  · exact Or.inr (Or.inr ha)

/-- An allocation and a step that writes only the new bytes: one step from before the
allocation. -/
theorem StepS.copy {y : MachineState} {d : Word} {m : Nat}
    (st : StepS s y u A) (hd : heapNext y ≤ d.toNat) (hd' : d.toNat + m ≤ heapNext u)
    (fr : DFrame u v fun a ↦ Within a d m ∨ Within a (s.getReg .x2 - BitVec.ofNat 64 1360) 16)
    (hb : (s.getReg .x2).toNat ≥ 4544) (hnx : heapNext v = heapNext u)
    (sp : v.getReg .x2 = u.getReg .x2) : StepS s y v A where
  frame := (st.frame.mono fun a ha ↦ by
      rcases ha with ha | ha | ha | ⟨f1, f2⟩
      · exact Or.inl ha
      · exact Or.inr (Or.inl ha)
      · exact Or.inr (Or.inr (Or.inl ha))
      · exact Or.inr (Or.inr (Or.inr ⟨f1, by rw [hnx]; exact f2⟩))).trans fr
    fun a ha ↦ by
      rcases ha with ha | ha
      · refine Or.inr (Or.inr (Or.inr ?_))
        show heapNext y ≤ a.toNat ∧ a.toNat < heapNext v
        simp only [Within] at ha
        omega
      · exact Or.inr (Or.inl (by addr_omega [ha, hb]))
  heap := ⟨hnx ▸ st.heap.lo, hnx ▸ st.heap.hi⟩
  mono := by rw [hnx]; exact st.mono
  sp := sp.trans st.sp

end StepS

/-- A prefix of a slice of `E`. -/
theorem eListAt_take (s : MachineState) (p : Word) {m n : Nat} (h : m ≤ n) :
    eListAt s p m = (eListAt s p n).take m := by
  simp only [eListAt, ← List.map_take, List.take_range, Nat.min_eq_left h]

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
