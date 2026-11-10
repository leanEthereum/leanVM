import Rv64Verifier.Proofs.Walk.AtR17
import Rv64Verifier.Proofs.Walk.Exit

/-!
# `walk` from `0x800035f0` on: what stays

`Rest s u₀ u`: past `u₀` (the state `AtR17` describes), memory has changed only outside `KeepR`:
the frame slots read to the end (the rate, the public input, the result's and the proof's
addresses, `checked`, the `Layout`, the root) and the heap `walk` allocated before `u₀`, but the
claims' buffer, which the table claims fill. A step writing frame slots apart from these keeps it
(`Rest.step`, `Rest.stepT`).
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.Model
  Rv64Verifier.Transcript

/-- What the rest of `walk` keeps of `u₀`. -/
@[rv_addr] def KeepR (s u₀ : MachineState) (a : Word) : Prop :=
  (Within a (s.getReg .x2 - 2584) 40 ∨ Within a (s.getReg .x2 - 2488) 8 ∨
    Within a (s.getReg .x2 - 2448) 8 ∨ Within a (s.getReg .x2 - 2088) 8 ∨
    Within a (s.getReg .x2 - 2080) 208 ∨ Within a (s.getReg .x2 - 1800) 32) ∨
  (heapNext s ≤ a.toNat ∧ a.toNat < heapNext u₀ ∧
    ¬ Within a (vecPtr u₀ (s.getReg .x2 - 928)) (56 * (vecCap u₀ (s.getReg .x2 - 928)).toNat))

/-- Past `u₀`: `Inv`, and memory changed only outside `KeepR`. -/
structure Rest (s u₀ u : MachineState) : Prop where
  inv : Inv s u
  mono : heapNext u₀ ≤ heapNext u
  keep : DFrame u₀ u fun a ↦ ¬ KeepR s u₀ a

theorem Rest.of {s u : MachineState} (h : Inv s u) : Rest s u u :=
  ⟨h, le_refl _, DFrame.of_same (fun _ ↦ rfl) _⟩

theorem Rest.same {s u₀ v w : MachineState} (h : Rest s u₀ v) (hm : ∀ a, w.getMem a = v.getMem a)
    (sp : w.getReg .x2 = v.getReg .x2) : Rest s u₀ w := by
  have hn : heapNext w = heapNext v := by simp only [heapNext, hm]
  exact ⟨h.inv.same hm sp, hn ▸ h.mono, h.keep.trans (DFrame.of_same hm _) fun _ h ↦ h⟩

/-- What a step past `u₀` may write misses `KeepR`, but for its frame slot. -/
theorem Below.keep {s u₀ v w : MachineState} (hpre : WalkPre s) (h : Rest s u₀ v)
    (hw : HeapOk w) {lo : Word} {n : Nat} (hk : ∀ a, Within a lo n → ¬ KeepR s u₀ a) {a : Word}
    (ha : Below s v w lo n a) : ¬ KeepR s u₀ a := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hx := hpre.stack.next
  have hab := hpre.stack.above
  rw [stackLo_eq, stack_eq] at hx
  rw [stackLo_eq] at hab
  have m₀ := h.mono
  have hv := h.inv.heap.hi
  have hh := hw.hi
  rcases ha with ha | ha | ha | ⟨f1, f2⟩
  · exact hk a ha
  · simp only [KeepR, heapNext, heapEnd] at hab hv m₀ ⊢
    intro hK
    rcases hK with (hK | hK | hK | hK | hK | hK) | ⟨-, hK, -⟩ <;> addr_omega [ha, hK, hb1, hab, hv, m₀]
  · simp only [KeepR, heapNext, heapEnd] at hv m₀ ⊢
    intro hK
    rcases hK with (hK | hK | hK | hK | hK | hK) | ⟨-, hK, -⟩ <;> addr_omega [ha, hK, hb1, hx, hv, m₀]
  · simp only [KeepR, heapNext, heapEnd] at hab hv m₀ hh f1 f2 ⊢
    intro hK
    rcases hK with (hK | hK | hK | hK | hK | hK) | ⟨-, hK, -⟩ <;>
      addr_omega [hK, hb1, hab, hh, m₀, f1, f2]

/-- The sponge and offsets miss `KeepR`. -/
theorem sponge_keep {s u₀ v : MachineState} (hpre : WalkPre s) (h : Rest s u₀ v) {a : Word}
    (ha : Within a (tp s + 8) 352) : ¬ KeepR s u₀ a := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hab := hpre.stack.above
  rw [stackLo_eq] at hab
  have m₀ := h.mono
  have hv := h.inv.heap.hi
  simp only [KeepR, tp, heapNext, heapEnd] at hab hv m₀ ha ⊢
  intro hK
  rcases hK with (hK | hK | hK | hK | hK | hK) | ⟨-, hK, -⟩ <;> addr_omega [ha, hK, hb1, hab, hv, m₀]

theorem Rest.step {s u₀ v w : MachineState} (hpre : WalkPre s) (h : Rest s u₀ v) {lo : Word}
    {n : Nat} (hl : InFrame s lo n) (hk : ∀ a, Within a lo n → ¬ KeepR s u₀ a)
    (st : Step s v w lo n) : Rest s u₀ w :=
  ⟨h.inv.after hpre hl st, h.mono.trans st.mono,
    h.keep.trans st.frame fun _ ha ↦ Below.keep hpre h st.heap hk ha⟩

theorem Rest.stepT {s u₀ v w : MachineState} (hpre : WalkPre s) (h : Rest s u₀ v) {lo : Word}
    {n : Nat} (hl : InFrame s lo n) (hk : ∀ a, Within a lo n → ¬ KeepR s u₀ a)
    (st : StepT s v w lo n) : Rest s u₀ w :=
  ⟨h.inv.afterT hpre hl st, h.mono.trans st.mono,
    h.keep.trans st.frame fun _ ha ↦ ha.elim (Below.keep hpre h st.heap hk) (sponge_keep hpre h)⟩

/-- A doubleword all of whose bytes `KeepR` holds keeps its value at `u₀`. -/
theorem Rest.get {s u₀ u : MachineState} (h : Rest s u₀ u) {x : Word}
    (hx : ∀ i < 8, KeepR s u₀ (x + BitVec.ofNat 64 i)) : u.getMem x = u₀.getMem x :=
  h.keep x fun i hi h' ↦ h' (hx i hi)

/-- A frame slot `KeepR` holds. -/
theorem keep_slot {s u₀ : MachineState} (hpre : WalkPre s) {k : Nat}
    (hk : (2088 ≤ k ∧ k ≤ 2088) ∨ (1872 + 8 ≤ k ∧ k ≤ 2080) ∨ (1768 + 8 ≤ k ∧ k ≤ 1800) ∨
      (2544 + 8 ≤ k ∧ k ≤ 2584) ∨ k = 2488 ∨ k = 2448) :
    ∀ i < 8, KeepR s u₀ (s.getReg .x2 - BitVec.ofNat 64 k + BitVec.ofNat 64 i) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  intro i hi
  left
  simp only [Within]
  rcases hk with hk | hk | hk | hk | hk | hk
  · exact Or.inr (Or.inr (Or.inr (Or.inl (by constructor <;> addr_omega [hb1, hk, hi]))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by constructor <;> addr_omega [hb1, hk, hi])))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by constructor <;> addr_omega [hb1, hk, hi])))))
  · exact Or.inl (by constructor <;> addr_omega [hb1, hk, hi])
  · exact Or.inr (Or.inl (by subst hk; constructor <;> addr_omega [hb1, hi]))
  · exact Or.inr (Or.inr (Or.inl (by subst hk; constructor <;> addr_omega [hb1, hi])))

/-- Heap `walk` allocated before `u₀`, apart from the claims' buffer, is in `KeepR`. -/
theorem keep_old {s u₀ : MachineState} {p : Word} {n : Nat} (ho : Old s u₀ p n)
    (hc : Apart p n (vecPtr u₀ (s.getReg .x2 - 928)) (56 * (vecCap u₀ (s.getReg .x2 - 928)).toNat))
    {x : Word} (h1 : p.toNat ≤ x.toNat) (h2 : x.toNat + 8 ≤ p.toNat + n) :
    ∀ i < 8, KeepR s u₀ (x + BitVec.ofNat 64 i) := by
  intro i hi
  right
  replace ho := ho.newBuf
  simp only [NewBuf] at ho
  have hp := p.isLt
  rcases ho.2 with h0 | ho2
  · omega
  have : (x + BitVec.ofNat 64 i).toNat = x.toNat + i := by addr_omega [h1, h2, ho2, hi]
  refine ⟨by omega, by omega, fun hw ↦ ?_⟩
  simp only [Within, Apart] at hw hc
  omega

/-! ## Steps writing frame slots -/

/-- A block's frame: what it writes, by address. -/
theorem _root_.Rv64Verifier.Sym.Expect.Holds.dframe {x : Sym.Expect} {s t : MachineState}
    (h : x.Holds s t) {w : Word → Prop} (hw : ∀ k ∈ x.writes, w (k.eval s)) : DFrame s t w :=
  fun a ha ↦ h.frame a fun k hk he ↦ ha 0 (by decide) (by rw [add_ofNat_zero, he]; exact hw k hk)

/-- In the frame, below the saved registers. -/
@[rv_addr] def InF (s : MachineState) (a : Word) : Prop :=
  (s.getReg .x2 - 2656).toNat ≤ a.toNat ∧ a.toNat < (s.getReg .x2 - 104).toNat

/-- A step past `u₀` writing the frame bytes `W`, the stack below the frame, `NEXT`, the heap it
allocates, and the sponge and offsets when `T` holds; keeping `sp`. -/
structure StepW (s v w : MachineState) (W : Word → Prop) (T : Prop) : Prop where
  frame : DFrame v w fun a ↦ W a ∨ Within a (s.getReg .x2 - 11392) 8736 ∨ Within a nextAddr 8 ∨
    Fresh v w a ∨ (T ∧ Within a (tp s + 8) 352)
  heap : HeapOk w
  mono : heapNext v ≤ heapNext w
  sp : w.getReg .x2 = v.getReg .x2

theorem StepW.same {s v w : MachineState} (hh : HeapOk v) (hm : ∀ a, w.getMem a = v.getMem a)
    (sp : w.getReg .x2 = v.getReg .x2) (W : Word → Prop) (T : Prop) : StepW s v w W T := by
  have hn : heapNext w = heapNext v := by simp only [heapNext, hm]
  exact ⟨DFrame.of_same hm _, ⟨hn ▸ hh.lo, hn ▸ hh.hi⟩, hn.ge, sp⟩

theorem StepW.trans {s u v w : MachineState} {W W' : Word → Prop} {T T' : Prop}
    (h₁ : StepW s u v W T) (h₂ : StepW s v w W' T') :
    StepW s u w (fun a ↦ W a ∨ W' a) (T ∨ T') := by
  have m₁ := h₁.mono
  have m₂ := h₂.mono
  refine ⟨(h₁.frame.mono fun a ha ↦ ?_).trans h₂.frame fun a ha ↦ ?_, h₂.heap, m₁.trans m₂,
    h₂.sp.trans h₁.sp⟩
  · simp only [Fresh] at ha ⊢
    rcases ha with ha | ha | ha | ha | ⟨ht, ha⟩
    · exact Or.inl (Or.inl ha)
    · exact Or.inr (Or.inl ha)
    · exact Or.inr (Or.inr (Or.inl ha))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨ha.1, by omega⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨Or.inl ht, ha⟩)))
  · simp only [Fresh] at ha ⊢
    rcases ha with ha | ha | ha | ha | ⟨ht, ha⟩
    · exact Or.inl (Or.inr ha)
    · exact Or.inr (Or.inl ha)
    · exact Or.inr (Or.inr (Or.inl ha))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, ha.2⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨Or.inr ht, ha⟩)))

theorem StepW.weaken {s v w : MachineState} {W W' : Word → Prop} {T T' : Prop}
    (h : StepW s v w W T) (hW : ∀ a, W a → W' a) (hT : T → T') : StepW s v w W' T' :=
  ⟨h.frame.mono fun a ha ↦ by
    rcases ha with ha | ha | ha | ha | ⟨ht, ha⟩
    · exact Or.inl (hW a ha)
    · exact Or.inr (Or.inl ha)
    · exact Or.inr (Or.inr (Or.inl ha))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hT ht, ha⟩))), h.heap, h.mono, h.sp⟩

theorem Rest.stepW {s u₀ v w : MachineState} (hpre : WalkPre s) (h : Rest s u₀ v)
    {W : Word → Prop} {T : Prop} (hW : ∀ a, W a → InF s a ∧ ¬ KeepR s u₀ a)
    (st : StepW s v w W T) : Rest s u₀ w := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hx := hpre.stack.next
  have hab := hpre.stack.above
  rw [stackLo_eq, stack_eq] at hx
  rw [stackLo_eq] at hab
  have hh := st.heap.hi
  have m₀ := h.inv.mono
  have kept : ∀ a, (W a ∨ Within a (s.getReg .x2 - 11392) 8736 ∨ Within a nextAddr 8 ∨
      Fresh v w a ∨ (T ∧ Within a (tp s + 8) 352)) →
      (WalkW s w a ∧ ¬ Within a (s.getReg .x2 - 104) 104) := by
    intro a ha
    simp only [WalkW, Fresh, stackLo_eq, heapNext, heapEnd, InF] at ha hab hh m₀ hW ⊢
    rcases ha with ha | ha | ha | ⟨f1, f2⟩ | ⟨-, ha⟩
    · obtain ⟨⟨i1, i2⟩, -⟩ := hW a ha
      exact ⟨Or.inr (Or.inl (by addr_omega [i1, i2, hb1])), by addr_omega [i1, i2, hb1]⟩
    · exact ⟨Or.inr (Or.inl (by addr_omega [ha, hb1])), by addr_omega [ha, hb1]⟩
    · exact ⟨Or.inr (Or.inr (Or.inl ha)), by addr_omega [ha, hx, hb1]⟩
    · exact ⟨Or.inr (Or.inr (Or.inr ⟨by omega, f2⟩)), by addr_omega [f1, f2, hh, hab, hb1]⟩
    · rw [tp] at ha
      exact ⟨Or.inr (Or.inl (by addr_omega [ha, hb1])), by addr_omega [ha, hb1]⟩
  refine ⟨h.inv.step hpre st.frame kept st.heap st.mono st.sp, h.mono.trans st.mono,
    h.keep.trans st.frame fun a ha ↦ ?_⟩
  rcases ha with ha | ha | ha | ha | ⟨-, ha⟩
  · exact (hW a ha).2
  · exact Below.keep hpre h st.heap (lo := 0) (n := 0) (fun _ h ↦ absurd h.2 (by simp))
      (Or.inr (Or.inl ha))
  · exact Below.keep hpre h st.heap (lo := 0) (n := 0) (fun _ h ↦ absurd h.2 (by simp))
      (Or.inr (Or.inr (Or.inl ha)))
  · exact Below.keep hpre h st.heap (lo := 0) (n := 0) (fun _ h ↦ absurd h.2 (by simp))
      (Or.inr (Or.inr (Or.inr ha)))
  · exact sponge_keep hpre h ha

/-- A step that does not write the sponge, writing frame bytes apart from the transcript, keeps
what the transcript stands for. -/
theorem StepW.transcript {s v w : MachineState} (hpre : WalkPre s) (h : Inv s v)
    (hptr : v.getMem (tp s) = s.getReg .x13) {W : Word → Prop}
    (hW : ∀ a, W a → InF s a ∧ ¬ Within a (tp s) 368) (st : StepW s v w W False) {T : TState}
    (hT : TranscriptAt v (tp s) T) : TranscriptAt w (tp s) T := by
  obtain ⟨hb1, hb2, -, -⟩ := bounds hpre
  have hx := hpre.stack.next
  have hab := hpre.stack.above
  rw [stackLo_eq, stack_eq] at hx
  rw [stackLo_eq] at hab
  have hh := st.heap.hi
  obtain ⟨e0, e1, e2⟩ := proofVals hpre h hptr
  have hP := hpre.proof
  have m₀ := h.mono
  have ro : ∀ {a : Word} {n : Nat}, ReadOnly s a n → a.toNat + n ≤ 2 ^ 64 →
      Misses (fun y ↦ W y ∨ Within y (s.getReg .x2 - 11392) 8736 ∨ Within y nextAddr 8 ∨
        Fresh v w y ∨ (False ∧ Within y (tp s + 8) 352)) a n := by
    intro a n hr hn y hy hw
    obtain ⟨⟨hf, hfx⟩, hs, -, -⟩ := hr
    rw [stackLo_eq, stack_eq] at hs
    simp only [Fresh, heapNext, heapEnd] at hw hh hab hf m₀
    rcases hw with hw | hw | hw | ⟨f1, f2⟩ | ⟨hf', -⟩
    · obtain ⟨⟨i1, i2⟩, -⟩ := hW y hw
      addr_omega [hy, i1, i2, hs, hb1]
    · addr_omega [hy, hw, hs]
    · addr_omega [hy, hw, hfx]
    · rcases hf with hf | hf <;> addr_omega [hy, f1, f2, hf, m₀, hn, hh]
    · exact hf'
  have tpw : ∀ y, Within y (tp s) 368 → ¬ (W y ∨ Within y (s.getReg .x2 - 11392) 8736 ∨
      Within y nextAddr 8 ∨ Fresh v w y ∨ (False ∧ Within y (tp s + 8) 352)) := by
    intro y hy hw
    simp only [Fresh, heapNext, heapEnd] at hw hh hab
    rcases hw with hw | hw | hw | ⟨-, hw⟩ | ⟨hf, -⟩
    · exact (hW y hw).2 hy
    · rw [tp] at hy; addr_omega [hy, hw, hb1]
    · rw [tp] at hy; addr_omega [hy, hw, hx, hb1]
    · rw [tp] at hy; addr_omega [hy, hw, hh, hab, hb1]
    · exact hf
  refine st.frame.transcriptAt hT (tok hpre h hptr) (fun y hy ↦ tpw y (by
      rw [tp] at hy ⊢; addr_omega [hy, hb1])) ?_ ?_ (fun y hy ↦ tpw y (by
      rw [tp] at hy ⊢; addr_omega [hy, hb1]))
  · rw [e0]; exact ro hpre.proofRO (by addr_omega [hP])
  · rw [e1, e2]
    refine ro hpre.streamRO ?_
    rcases hpre.stream with h0 | h0
    · rw [h0]; have := (vecPtr s (s.getReg .x13)).isLt; omega
    · addr_omega [h0]

/-- A frame doubleword a step does not write keeps its value. -/
theorem StepW.getF {s v w : MachineState} (hpre : WalkPre s) {W : Word → Prop} {T : Prop}
    (st : StepW s v w W T) {x : Word}
    (hx : (s.getReg .x2 - 2656).toNat ≤ x.toNat ∧ x.toNat + 8 ≤ (s.getReg .x2).toNat)
    (hW : ∀ i < 8, ¬ W (x + BitVec.ofNat 64 i))
    (hT : T → Apart x 8 (tp s + 8) 352) : w.getMem x = v.getMem x := by
  obtain ⟨hb1, hb2, -, -⟩ := bounds hpre
  have hh := st.heap.hi
  have hn := hpre.stack.next
  have ha := hpre.stack.above
  rw [stackLo_eq, stack_eq] at hn
  rw [stackLo_eq] at ha
  refine st.frame x fun i hi hw ↦ ?_
  simp only [Fresh, heapNext, heapEnd] at hw hh ha
  rcases hw with hw | hw | hw | ⟨-, hw⟩ | ⟨ht, hw⟩
  · exact hW i hi hw
  · addr_omega [hx, hw, hi, hb1, hb2]
  · addr_omega [hx, hw, hi, hb1, hb2, hn]
  · addr_omega [hx, hw, hi, hb1, hb2, hh, ha]
  · have := hT ht; rw [tp] at hw this; addr_omega [hx, hw, hi, hb1, this]

/-- A heap doubleword allocated before a step that writes only frame bytes keeps its value. -/
theorem StepW.getH {s v w : MachineState} (hpre : WalkPre s) {W : Word → Prop} {T : Prop}
    (st : StepW s v w W T) (hW : ∀ a, W a → InF s a) {x : Word}
    (hx : x.toNat + 8 ≤ heapNext v) : w.getMem x = v.getMem x := by
  obtain ⟨hb1, hb2, -, -⟩ := bounds hpre
  have hh := st.heap.hi
  have hm := st.mono
  have ha := hpre.stack.above
  rw [stackLo_eq] at ha
  refine st.frame x fun i hi hw ↦ ?_
  simp only [Fresh, heapNext, heapEnd, nextAddr] at hw hh ha hx hm
  rcases hw with hw | hw | hw | ⟨hw, -⟩ | ⟨-, hw⟩
  · have := hW _ hw; simp only [InF] at this; addr_omega [hx, this, hi, hb1, hh, hm, ha]
  · addr_omega [hx, hw, hi, hb1, hh, hm, ha]
  · addr_omega [hx, hw, hi, hh, hm]
  · addr_omega [hx, hw, hi]
  · rw [tp] at hw; addr_omega [hx, hw, hi, hb1, hh, hm, ha]

/-- An allocated buffer is a region. -/
theorem NewBuf.region {s u : MachineState} {p : Word} {n : Nat} (h : NewBuf s u p n 8)
    (hs : HeapOk s) (hu : HeapOk u) (hn : n ≠ 0) : Region p n := by
  have h1 := hs.lo
  have h2 := hu.hi
  simp only [NewBuf, Region, Mapped, heapNext, heapStart, heapEnd] at h h1 h2 ⊢
  omega

/-- A frame slot `S - k` apart from `KeepR`'s slots. -/
theorem slot_ok {s u₀ v : MachineState} (hpre : WalkPre s) (h : Rest s u₀ v) {k : Nat}
    (hk : 112 ≤ k ∧ k ≤ 2656)
    (hn : (k ≤ 1768 ∨ 1800 < k) ∧ (k ≤ 1872 ∨ 2088 < k) ∧ (k ≤ 2440 ∨ 2448 < k) ∧
      (k ≤ 2480 ∨ 2488 < k) ∧ (k ≤ 2544 ∨ 2584 < k)) :
    InF s (s.getReg .x2 - BitVec.ofNat 64 k) ∧ ¬ KeepR s u₀ (s.getReg .x2 - BitVec.ofNat 64 k) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hab := hpre.stack.above
  rw [stackLo_eq] at hab
  have m₀ := h.mono
  have hv := h.inv.heap.hi
  simp only [InF, KeepR, heapNext, heapEnd] at hab hv m₀ ⊢
  refine ⟨⟨by addr_omega [hb1, hk], by addr_omega [hb1, hk]⟩, fun hK ↦ ?_⟩
  rcases hK with (hK | hK | hK | hK | hK | hK) | ⟨-, hK, -⟩ <;> addr_omega [hK, hb1, hk, hn, hab, hv, m₀]

/-- A block writing only frame doublewords. -/
theorem StepW.ofFrame {s v w : MachineState} (hpre : WalkPre s) (hh : HeapOk v) {W : Word → Prop}
    (fr : DFrame v w W) (hW : ∀ a, W a → InF s a) (sp : w.getReg .x2 = v.getReg .x2) :
    StepW s v w W False := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have he : heapNext w = heapNext v := by
    simp only [heapNext]
    exact congrArg BitVec.toNat (fr nextAddr fun i hi hw ↦ by
      have := hW _ hw; simp only [InF] at this; addr_omega [this, hi, hb1])
  exact ⟨fr.mono fun a ha ↦ Or.inl ha, ⟨he ▸ hh.lo, he ▸ hh.hi⟩, he.ge, sp⟩

/-- A frame range `[S - c, S - c + n)` apart from `KeepR`'s slots. -/
theorem range_ok {s u₀ v : MachineState} (hpre : WalkPre s) (h : Rest s u₀ v) {c : Word} {k n : Nat}
    (hc : c.toNat = k) (hk : 112 + n ≤ k + 8 ∧ k ≤ 2656)
    (hn : (k ≤ 1768 ∨ 1800 + n ≤ k) ∧ (k ≤ 1872 ∨ 2088 + n ≤ k) ∧ (k ≤ 2440 ∨ 2448 + n ≤ k) ∧
      (k ≤ 2480 ∨ 2488 + n ≤ k) ∧ (k ≤ 2544 ∨ 2584 + n ≤ k)) {a : Word}
    (ha : Within a (s.getReg .x2 - c) n) : InF s a ∧ ¬ KeepR s u₀ a := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hab := hpre.stack.above
  rw [stackLo_eq] at hab
  have m₀ := h.mono
  have hv := h.inv.heap.hi
  simp only [InF, KeepR, heapNext, heapEnd] at hab hv m₀ ⊢
  refine ⟨⟨by addr_omega [hb1, hk, hc, ha], by addr_omega [hb1, hk, hc, ha]⟩, fun hK ↦ ?_⟩
  rcases hK with (hK | hK | hK | hK | hK | hK) | ⟨-, hK, -⟩ <;>
    addr_omega [hK, hb1, hk, hn, hab, hv, m₀, hc, ha]

/-- A frame range, for a callee with an `m`-byte stack below the frame: outside the free heap,
apart from the callee's stack and `.rodata`. -/
theorem fr_ok {s u : MachineState} (hpre : WalkPre s) (h : Inv s u) {c : Word} {k n m : Nat}
    (hc : c.toNat = k) (hk1 : 104 + n ≤ k) (hk2 : k ≤ 2656) (hm : m ≤ 8736) :
    Outside u (s.getReg .x2 - c) n ∧ Apart (s.getReg .x2 - c) n (stackLo u m) m ∧
      Apart (s.getReg .x2 - c) n rodataBase rodataSize := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hab := hpre.stack.above
  have hx := hpre.stack.next
  have hro := hpre.stack.rodata
  rw [stackLo_eq] at hab
  rw [stackLo_eq, stack_eq] at hx hro
  have hrb : rodataBase.toNat = 2684354560 := rfl
  have hrs : rodataStart.toNat = 2684354560 := rfl
  simp only [heapEnd] at hab
  refine ⟨⟨Or.inr (by addr_omega [hab, hb1, hk1, hk2, hc]), by addr_omega [hx, hb1, hk1, hk2, hc]⟩,
    by rw [stackLo_callee h]; addr_omega [hb1, hk1, hk2, hm, hc],
    by addr_omega [hro, hrb, hrs, hb1, hk1, hk2, hc]⟩

/-- An allocated heap buffer: outside the free heap, apart from the stack and `.rodata`. -/
theorem heap_ok {u : MachineState} (hu : HeapOk u) {p : Word} {n : Nat}
    (hb : p.toNat + n ≤ heapNext u) :
    Outside u p n ∧ (∀ lo m, heapEnd ≤ lo.toNat → Apart p n lo m) ∧
      Apart p n rodataBase rodataSize := by
  have hh := hu.hi
  have hrb : rodataBase.toNat = 2684354560 := rfl
  simp only [Outside, heapNext, heapEnd, nextAddr] at hb hh ⊢
  exact ⟨⟨Or.inl hb, by addr_omega [hb, hh]⟩, fun lo m hl ↦ by addr_omega [hb, hh, hl],
    by addr_omega [hb, hh, hrb]⟩

/-- A callee's frame: its result, its `m`-byte stack below the frame, `NEXT`, what it allocates. -/
theorem StepW.ofCall {s u v : MachineState} (hpre : WalkPre s) (h : Inv s u) {m : Nat}
    (hm : m ≤ 8736) {W : Word → Prop}
    (fr : DFrame u v fun a ↦ W a ∨ Within a (stackLo u m) m ∨ Within a nextAddr 8 ∨ Fresh u v a)
    (heap : HeapOk v) (mono : heapNext u ≤ heapNext v) (sp : v.getReg .x2 = u.getReg .x2) :
    StepW s u v W False := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  refine ⟨fr.mono fun a ha ↦ ?_, heap, mono, sp⟩
  rcases ha with ha | ha | ha | ha
  · exact Or.inl ha
  · rw [stackLo_callee h] at ha
    exact Or.inr (Or.inl (by addr_omega [ha, hb1, hm]))
  · exact Or.inr (Or.inr (Or.inl ha))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))

/-- A frame `E` a step does not write keeps its value. -/
theorem StepW.eAtF {s v w : MachineState} (hpre : WalkPre s) {W : Word → Prop} {T : Prop}
    (st : StepW s v w W T) {x : Word}
    (hx : (s.getReg .x2 - 2656).toNat ≤ x.toNat ∧ x.toNat + 24 ≤ (s.getReg .x2).toNat)
    (hW : ∀ i < 24, ¬ W (x + BitVec.ofNat 64 i))
    (hT : T → Apart x 24 (tp s + 8) 352) : eAt w x = eAt v x := by
  obtain ⟨hb1, hb2, -, -⟩ := bounds hpre
  have hh := st.heap.hi
  have hn := hpre.stack.next
  have ha := hpre.stack.above
  rw [stackLo_eq, stack_eq] at hn
  rw [stackLo_eq] at ha
  refine st.frame.eAt fun i hi hw ↦ ?_
  simp only [Fresh, heapNext, heapEnd] at hw hh ha
  rcases hw with hw | hw | hw | ⟨-, hw⟩ | ⟨ht, hw⟩
  · exact hW i hi hw
  · addr_omega [hx, hw, hi, hb1, hb2]
  · addr_omega [hx, hw, hi, hb1, hb2, hn]
  · addr_omega [hx, hw, hi, hb1, hb2, hh, ha]
  · have := hT ht; rw [tp] at hw this; addr_omega [hx, hw, hi, hb1, this]

/-- Heap `E`s allocated before a step that writes only frame bytes keep their values. -/
theorem StepW.eListH {s v w : MachineState} (hpre : WalkPre s) {W : Word → Prop} {T : Prop}
    (st : StepW s v w W T) (hW : ∀ a, W a → InF s a) {p : Word} {n : Nat}
    (hx : p.toNat + 24 * n ≤ heapNext v) : eListAt w p n = eListAt v p n := by
  obtain ⟨hb1, hb2, -, -⟩ := bounds hpre
  have hh := st.heap.hi
  have hm := st.mono
  have ha := hpre.stack.above
  rw [stackLo_eq] at ha
  refine st.frame.eListAt fun i hi hw ↦ ?_
  simp only [Fresh, heapNext, heapEnd, nextAddr] at hw hh ha hx hm
  rcases hw with hw | hw | hw | ⟨hw, -⟩ | ⟨-, hw⟩
  · have := hW _ hw; simp only [InF] at this; addr_omega [hx, this, hi, hb1, hh, hm, ha]
  · addr_omega [hx, hw, hi, hb1, hh, hm, ha]
  · addr_omega [hx, hw, hi, hh, hm]
  · addr_omega [hx, hw, hi]
  · rw [tp] at hw; addr_omega [hx, hw, hi, hb1, hh, hm, ha]

/-- A block writing the result's first `n ≤ 80` bytes keeps `Rest`. -/
theorem Rest.result {s u₀ v w : MachineState} (hpre : WalkPre s) (h : Rest s u₀ v) {n : Nat}
    (hn : n ≤ 80) (fr : DFrame v w fun a ↦ Within a (s.getReg .x10) n)
    (sp : w.getReg .x2 = v.getReg .x2) : Rest s u₀ w := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hO := hpre.outStack
  have hF := hpre.outFree
  have hR := hpre.out
  rw [stackLo_eq, stack_eq] at hO
  have he : heapNext w = heapNext v := by
    simp only [heapNext]
    exact congrArg BitVec.toNat (fr nextAddr fun i hi hw ↦ by
      have := hF.2; addr_omega [this, hw, hi, hn])
  have m₀ := h.mono
  have hv := h.inv.heap.hi
  refine ⟨h.inv.step hpre fr (fun a ha ↦ ⟨Or.inl (by addr_omega [ha, hn]), by
      addr_omega [ha, hn, hO, hb1]⟩) ⟨he ▸ h.inv.heap.lo, he ▸ h.inv.heap.hi⟩ he.ge sp,
    he ▸ h.mono, h.keep.trans fr fun a ha hK ↦ ?_⟩
  have m₁ := h.inv.mono
  simp only [KeepR, Outside, heapNext, heapEnd] at hK hF m₀ hv m₁
  rcases hK with (hK | hK | hK | hK | hK | hK) | ⟨k1, k2, -⟩
  all_goals first
    | addr_omega [ha, hK, hO, hb1, hn]
    | rcases hF.1 with f | f <;> addr_omega [ha, k1, k2, f, hn, m₀, hv, m₁]

end Rv64Verifier.Proofs.Walk
