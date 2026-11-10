import Rv64Verifier.Proofs.Bus.TableSumcheck
import Rv64Verifier.Proofs.Transcript.Frames

/-!
# `table_sumcheck`: the frame

With `S` the entry's `sp`, the function keeps a 496-byte frame, the registers it saves in its top
104 bytes. Past the prologue, `Inv s u` holds: `sp` is `S - 496`, the saved registers are in
place, and memory has changed only where `TableSumcheckPost.frame` allows (`W`). A step that
writes only the stack below the saved registers, `NEXT` and the heap it allocates (`Loc`) keeps
`Inv`, the transcript and everything read only.
-/

namespace Rv64Verifier.Proofs.Bus.TableSumcheck
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.Model
  Rv64Verifier.Bus Rv64Verifier.Transcript

theorem stack_eq : tableSumcheckStack = 2128 := rfl

theorem stackLo_eq (s : MachineState) : stackLo s tableSumcheckStack = s.getReg .x2 - 2128 := rfl

theorem bounds {s : MachineState} (h : TableSumcheckPre s) :
    0xa0000f38 + 2128 ≤ (s.getReg .x2).toNat ∧ (s.getReg .x2).toNat ≤ 0xc0000008 ∧
      (s.getReg .x2).toNat % 16 = 0 ∧
      (stackLo s tableSumcheckStack).toNat = (s.getReg .x2).toNat - 2128 := by
  have hm := h.stack.mapped (by decide) (by decide)
  have hb := h.stack.bounds (by decide) (by decide)
  have hn := h.stack.next
  have hr := h.stack.rodata
  rw [stack_eq] at hm hb hn hr ⊢
  refine ⟨?_, hb.2.1, hb.2.2.1, hb.2.2.2⟩
  addr_omega [hm, hb, hn, hr]

/-- The registers the prologue saves, from `S - 8` down. -/
def savedRegs : List Reg :=
  [.x1, .x8, .x9, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27]

/-- What the function may write (`TableSumcheckPost.frame`). -/
def W (s u : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x10) 24 ∨ Within a (tsTarget s) 24 ∨ Within a (tsSelf s + 8) 344 ∨
    Within a (stackLo s tableSumcheckStack) tableSumcheckStack ∨ Within a nextAddr 8 ∨ Fresh s u a

theorem W.mono {s u v : MachineState} (h : heapNext u ≤ heapNext v) {a : Word} (ha : W s u a) :
    W s v a := by
  rcases ha with ha | ha | ha | ha | ha | ⟨h1, h2⟩
  · exact Or.inl ha
  · exact Or.inr (Or.inl ha)
  · exact Or.inr (Or.inr (Or.inl ha))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, by omega⟩))))

/-- Past the prologue. -/
structure Inv (s u : MachineState) : Prop where
  sp : u.getReg .x2 = s.getReg .x2 - 496
  heap : HeapOk u
  mono : heapNext s ≤ heapNext u
  frame : DFrame s u (W s u)
  saved : ∀ i < 13, u.getMem (s.getReg .x2 - BitVec.ofNat 64 (8 * i + 8)) =
    s.getReg (savedRegs.getD i .x0)

/-- A step that writes what the function may, but not the saved registers, keeps `Inv`. -/
theorem Inv.step {s u v : MachineState} {w : Word → Prop} (hpre : TableSumcheckPre s)
    (h : Inv s u) (hf : DFrame u v w)
    (hw : ∀ a, w a → W s v a ∧ ¬ Within a (s.getReg .x2 - 104) 104) (heap : HeapOk v)
    (mono : heapNext u ≤ heapNext v) (sp : v.getReg .x2 = u.getReg .x2) : Inv s v := by
  obtain ⟨hb1, hb2, -, -⟩ := bounds hpre
  refine ⟨sp.trans h.sp, heap, h.mono.trans mono,
    (h.frame.mono fun a ha ↦ W.mono mono ha).trans hf fun a ha ↦ (hw a ha).1, fun i hi ↦ ?_⟩
  rw [hf _ fun j hj hw' ↦ (hw _ hw').2 (by addr_omega [hb1, hb2, hi, hj])]
  exact h.saved i hi

/-- The local writes: the stack below the saved registers, `NEXT`, the heap allocated. -/
def Loc (s u v : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x2 - 2128) 2024 ∨ Within a nextAddr 8 ∨ Fresh u v a

theorem Loc.w {s u v : MachineState} (hpre : TableSumcheckPre s) (h : Inv s u) (hv : HeapOk v)
    {a : Word} (ha : Loc s u v a) : W s v a ∧ ¬ Within a (s.getReg .x2 - 104) 104 := by
  obtain ⟨hb1, hb2, -, -⟩ := bounds hpre
  have hm := h.mono
  have hh := hv.hi
  simp only [Loc, Fresh] at ha
  rcases ha with ha | ha | ⟨h1, h2⟩
  · exact ⟨Or.inr (Or.inr (Or.inr (Or.inl (by rw [stackLo_eq]; addr_omega [ha])))),
      by addr_omega [ha, hb1]⟩
  · exact ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha)))), by addr_omega [ha, hb1]⟩
  · exact ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, h2⟩)))),
      by simp only [heapEnd, heapNext] at hh hm h1 h2 ⊢; addr_omega [hh, h1, h2, hb1]⟩

theorem Inv.loc {s u v : MachineState} (hpre : TableSumcheckPre s) (h : Inv s u)
    (hf : DFrame u v (Loc s u v)) (heap : HeapOk v) (mono : heapNext u ≤ heapNext v)
    (sp : v.getReg .x2 = u.getReg .x2) : Inv s v :=
  h.step hpre hf (fun _ ha ↦ Loc.w hpre h heap ha) heap mono sp

theorem _root_.Rv64Verifier.Bus.RO.bound {s : MachineState} {n : Nat} {ws : List (Word × Nat)}
    {p a : Word} {m : Nat}
    (h : RO s n ws p a m) : a.toNat + m ≤ 2 ^ 64 := by
  rcases h.region with h0 | h0
  · have := a.isLt; omega
  · addr_omega [h0]

/-- What is read only misses what the function writes. -/
theorem Inv.miss {s u : MachineState} (h : Inv s u) {a : Word} {m : Nat}
    (hr : RO s tableSumcheckStack (tsWrites s) (tsSelf s) a m) : Misses (W s u) a m := by
  have ho : Apart a m (s.getReg .x10) 24 := hr.out (s.getReg .x10, 24) (by simp [tsWrites])
  have ht : Apart a m (tsTarget s) 24 := hr.out (tsTarget s, 24) (by simp [tsWrites])
  have hf := hr.free
  have hs := hr.stack
  have hself := hr.self
  have hn := h.heap.hi
  intro y hy hw
  simp only [W, stackLo_eq] at hw
  rw [stackLo_eq] at hs
  rcases hw with hw | hw | hw | hw | hw | hw
  · addr_omega [ho, hy, hw]
  · addr_omega [ht, hy, hw]
  · addr_omega [hself, hy, hw]
  · addr_omega [hs, hy, hw]
  · addr_omega [hf, hy, hw]
  · simp only [Outside, Fresh, heapNext, heapEnd] at hf hw hn
    addr_omega [hf, hy, hw, hn]

/-- What is read only misses the local writes. -/
theorem Inv.missLoc {s u v : MachineState} (h : Inv s u) (hv : HeapOk v) {a : Word} {m : Nat}
    (hr : RO s tableSumcheckStack (tsWrites s) (tsSelf s) a m) : Misses (Loc s u v) a m := by
  have hf := hr.free
  have hs := hr.stack
  have hm := h.mono
  have hh := hv.hi
  rw [stackLo_eq, stack_eq] at hs
  intro y hy hl
  simp only [Loc, Fresh] at hl
  simp only [Outside, heapNext, heapEnd] at hf hl hm hh
  rcases hl with hl | hl | hl
  · addr_omega [hs, hy, hl]
  · addr_omega [hf, hy, hl]
  · addr_omega [hf, hy, hl, hm, hh]

theorem Inv.word {s u : MachineState} (h : Inv s u) {a : Word}
    {m : Nat} (hr : RO s tableSumcheckStack (tsWrites s) (tsSelf s) a m) {x : Word}
    (h1 : a.toNat ≤ x.toNat) (h2 : x.toNat + 8 ≤ a.toNat + m) : u.getMem x = s.getMem x :=
  h.frame x ((h.miss hr).bytes h1 h2 hr.bound)

theorem Inv.elem {s u : MachineState} (h : Inv s u) {a : Word}
    {m : Nat} (hr : RO s tableSumcheckStack (tsWrites s) (tsSelf s) a m) {x : Word}
    (h1 : a.toNat ≤ x.toNat) (h2 : x.toNat + 24 ≤ a.toNat + m) : eAt u x = eAt s x :=
  h.frame.eAt ((h.miss hr).bytes h1 h2 hr.bound)

theorem Inv.elems {s u : MachineState} (h : Inv s u) {a : Word}
    {n : Nat} (hr : RO s tableSumcheckStack (tsWrites s) (tsSelf s) a (24 * n)) :
    eListAt u a n = eListAt s a n :=
  h.frame.eListAt ((h.miss hr).bytes (Nat.le_refl _) (Nat.le_refl _) hr.bound)

/-- The transcript at `tsSelf s` and its proof miss what the function writes but the sponge and
the offsets. -/
theorem missSelf {s u : MachineState} (hpre : TableSumcheckPre s) (h : Inv s u) :
    Misses (W s u) (tsSelf s) 8 := by
  have hS := hpre.self.self
  have so := hpre.selfOut
  have st := hpre.targetSelf
  have ss := hpre.selfStack
  have sf := hpre.selfFree
  have hn := h.heap.hi
  rw [stackLo_eq, stack_eq] at ss
  simp only [Outside, heapNext, heapEnd] at sf hn
  intro y hy hw
  simp only [W, Fresh, heapNext, stackLo_eq] at hw
  rcases hw with hw | hw | hw | hw | hw | hw
  · addr_omega [hy, hw, so]
  · addr_omega [hy, hw, st]
  · addr_omega [hy, hw, hS]
  · addr_omega [hy, hw, ss]
  · addr_omega [hy, hw, sf]
  · addr_omega [hy, hw, sf, hn]

theorem missProof {s u : MachineState} (hpre : TableSumcheckPre s) (h : Inv s u) :
    Misses (W s u) (proofAt s (tsSelf s)) 48 := by
  have hA := hpre.self.apart.1
  have po := hpre.proofOut.1
  have pt := hpre.proofTarget.1
  have ps := hpre.proofStack.1
  have pf := hpre.proofFree
  have hn := h.heap.hi
  rw [stackLo_eq, stack_eq] at ps
  simp only [Outside, heapNext, heapEnd] at pf hn
  intro y hy hw
  simp only [W, Fresh, heapNext, stackLo_eq] at hw
  rcases hw with hw | hw | hw | hw | hw | hw
  · addr_omega [hy, hw, po]
  · addr_omega [hy, hw, pt]
  · addr_omega [hy, hw, hA]
  · addr_omega [hy, hw, ps]
  · addr_omega [hy, hw, pf]
  · addr_omega [hy, hw, pf, hn]

theorem missStream {s u : MachineState} (hpre : TableSumcheckPre s) (h : Inv s u) :
    Misses (W s u) (streamPtr s (tsSelf s)) (24 * streamLen s (tsSelf s)) := by
  have hA := hpre.self.apart.2
  have po := hpre.proofOut.2
  have pt := hpre.proofTarget.2
  have ps := hpre.proofStack.2
  have pf := hpre.streamFree
  have hn := h.heap.hi
  rw [stackLo_eq, stack_eq] at ps
  simp only [Outside, heapNext, heapEnd] at pf hn
  intro y hy hw
  simp only [W, Fresh, heapNext, stackLo_eq] at hw
  rcases hw with hw | hw | hw | hw | hw | hw
  · addr_omega [hy, hw, po]
  · addr_omega [hy, hw, pt]
  · addr_omega [hy, hw, hA]
  · addr_omega [hy, hw, ps]
  · addr_omega [hy, hw, pf]
  · addr_omega [hy, hw, pf, hn]

theorem Inv.tok {s u : MachineState} (hpre : TableSumcheckPre s) (h : Inv s u) :
    TranscriptOk u (tsSelf s) :=
  h.frame.transcriptOk hpre.self (missSelf hpre h) (missProof hpre h)

theorem Inv.stream {s u : MachineState} (hpre : TableSumcheckPre s) (h : Inv s u) :
    proofAt u (tsSelf s) = proofAt s (tsSelf s) ∧ streamPtr u (tsSelf s) = streamPtr s (tsSelf s) ∧
      streamLen u (tsSelf s) = streamLen s (tsSelf s) :=
  h.frame.stream' (missSelf hpre h) (by have := hpre.self.self; addr_omega [this])
    (missProof hpre h) (by have := hpre.self.proof; addr_omega [this])

theorem Inv.rodata {s u : MachineState} (hpre : TableSumcheckPre s) (h : Inv s u) :
    RodataOk u := by
  have r1 := hpre.outRodata
  have r2 := hpre.targetRodata
  have r3 := hpre.selfRodata
  have r4 := hpre.stack.rodata
  have hn := h.heap.hi
  have hrb : rodataBase.toNat = 2684354560 := rfl
  rw [stackLo_eq, stack_eq] at r4
  refine hpre.rodata.dframe h.frame fun a ha hw ↦ ?_
  simp only [W, Fresh, heapNext, heapEnd, stackLo_eq] at hw hn
  rcases hw with hw | hw | hw | hw | hw | hw
  · addr_omega [ha, hw, r1, hrb]
  · addr_omega [ha, hw, r2, hrb]
  · have hS := hpre.self.self
    addr_omega [ha, hw, r3, hrb, hS]
  · addr_omega [ha, hw, r4, hrb]
  · addr_omega [ha, hw, hrb]
  · addr_omega [ha, hw, hn, hrb]

/-- A local step keeps the transcript. -/
theorem Inv.transcript {s u v : MachineState} (hpre : TableSumcheckPre s) (h : Inv s u)
    (hv : HeapOk v) (hf : DFrame u v (Loc s u v)) {T : TState}
    (hT : TranscriptAt u (tsSelf s) T) : TranscriptAt v (tsSelf s) T := by
  obtain ⟨e0, e1, e2⟩ := h.stream hpre
  have hS := hpre.self.self
  have ss := hpre.selfStack
  have sf := hpre.selfFree
  have ps := hpre.proofStack
  have pf := hpre.proofFree
  have bf := hpre.streamFree
  have hn := hv.hi
  have hm := h.mono
  rw [stackLo_eq, stack_eq] at ss ps
  simp only [ProofApart] at ps
  simp only [Outside, heapNext, heapEnd] at pf bf sf hn hm
  have loc (lo : Word) (n : Nat) (h1 : Apart lo n (s.getReg .x2 - 2128) 2128)
      (h2 : Apart lo n nextAddr 8) (h3 : lo.toNat + n ≤ (s.getMem nextAddr).toNat ∨
        0x78000000 ≤ lo.toNat) : Misses (Loc s u v) lo n := fun y hy hl ↦ by
    simp only [Loc, Fresh, heapNext] at hl
    rcases hl with hl | hl | hl
    · addr_omega [hy, hl, h1]
    · addr_omega [hy, hl, h2]
    · addr_omega [hy, hl, h3, hm, hn]
  refine hf.transcriptAt hT (h.tok hpre) (loc _ _ (by addr_omega [ss, hS])
    (by addr_omega [sf.2, hS]) (by addr_omega [sf.1, hS])) ?_ ?_
    (loc _ _ (by addr_omega [ss, hS]) (by addr_omega [sf.2, hS]) (by addr_omega [sf.1, hS]))
  · rw [e0]; exact loc _ _ ps.1 pf.2 pf.1
  · rw [e1, e2]; exact loc _ _ ps.2 bf.2 bf.1

end Rv64Verifier.Proofs.Bus.TableSumcheck
