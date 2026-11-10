import Rv64Verifier.Proofs.Walk.Contracts
import Rv64Verifier.Proofs.Walk.WalkModel
import Rv64Verifier.Proofs.Transcript.Frames

/-!
# `walk`: the frame

With `S` the entry's `sp`, the function keeps a 2656-byte frame, the registers it saves in its top
104 bytes, the transcript at `S - 2448` (`tp`). Past the prologue, `Inv s u` holds: `sp` is
`S - 2656`, the saved registers are in place, and memory has changed only where `WalkPost.frame`
allows (`WalkW`). A step that writes only the stack below the saved registers, `NEXT` and the heap
it allocates (`Loc`) keeps `Inv` and everything read only.

From the transcript's construction on, `Tracks OI s u C` says the code runs `C`, what is left of
`walkRust` from `TState.init`: every proof the memory holds (`ProofIn`) runs the mirror as `C`
runs from a transcript the memory at `tp` stands for, holding the same proof.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.Verifier Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript

theorem stack_eq : walkStack = 11392 := rfl

theorem stackLo_eq (s : MachineState) : stackLo s walkStack = s.getReg .x2 - 11392 := rfl

theorem bounds {s : MachineState} (h : WalkPre s) :
    0xa0000f38 + 11392 ≤ (s.getReg .x2).toNat ∧ (s.getReg .x2).toNat ≤ 0xc0000008 ∧
      (s.getReg .x2).toNat % 16 = 0 ∧
      (stackLo s walkStack).toNat = (s.getReg .x2).toNat - 11392 := by
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

theorem WalkW.mono {s u v : MachineState} (h : heapNext u ≤ heapNext v) {a : Word}
    (ha : WalkW s u a) : WalkW s v a := by
  rcases ha with ha | ha | ha | ⟨h1, h2⟩
  · exact Or.inl ha
  · exact Or.inr (Or.inl ha)
  · exact Or.inr (Or.inr (Or.inl ha))
  · exact Or.inr (Or.inr (Or.inr ⟨h1, by omega⟩))

/-- Past the prologue. -/
structure Inv (s u : MachineState) : Prop where
  sp : u.getReg .x2 = s.getReg .x2 - 2656
  heap : HeapOk u
  mono : heapNext s ≤ heapNext u
  frame : DFrame s u (WalkW s u)
  saved : ∀ i < 13, u.getMem (s.getReg .x2 - BitVec.ofNat 64 (8 * i + 8)) =
    s.getReg (savedRegs.getD i .x0)

/-- A step that writes what the function may, but not the saved registers, keeps `Inv`. -/
theorem Inv.step {s u v : MachineState} {w : Word → Prop} (hpre : WalkPre s)
    (h : Inv s u) (hf : DFrame u v w)
    (hw : ∀ a, w a → WalkW s v a ∧ ¬ Within a (s.getReg .x2 - 104) 104) (heap : HeapOk v)
    (mono : heapNext u ≤ heapNext v) (sp : v.getReg .x2 = u.getReg .x2) : Inv s v := by
  obtain ⟨hb1, hb2, -, -⟩ := bounds hpre
  refine ⟨sp.trans h.sp, heap, h.mono.trans mono,
    (h.frame.mono fun a ha ↦ WalkW.mono mono ha).trans hf fun a ha ↦ (hw a ha).1, fun i hi ↦ ?_⟩
  rw [hf _ fun j hj hw' ↦ (hw _ hw').2 (by addr_omega [hb1, hb2, hi, hj])]
  exact h.saved i hi

/-- The local writes: the stack below the saved registers, `NEXT`, the heap allocated. -/
def Loc (s u v : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x2 - 11392) 11288 ∨ Within a nextAddr 8 ∨ Fresh u v a

theorem Loc.w {s u v : MachineState} (hpre : WalkPre s) (h : Inv s u) (hv : HeapOk v)
    {a : Word} (ha : Loc s u v a) : WalkW s v a ∧ ¬ Within a (s.getReg .x2 - 104) 104 := by
  obtain ⟨hb1, hb2, -, -⟩ := bounds hpre
  have hm := h.mono
  have hh := hv.hi
  simp only [Loc, Fresh] at ha
  rcases ha with ha | ha | ⟨h1, h2⟩
  · exact ⟨Or.inr (Or.inl (by rw [stackLo_eq]; addr_omega [ha])), by addr_omega [ha, hb1]⟩
  · exact ⟨Or.inr (Or.inr (Or.inl ha)), by addr_omega [ha, hb1]⟩
  · exact ⟨Or.inr (Or.inr (Or.inr ⟨by omega, h2⟩)),
      by simp only [heapEnd, heapNext] at hh hm h1 h2 ⊢; addr_omega [hh, h1, h2, hb1]⟩

theorem Inv.loc {s u v : MachineState} (hpre : WalkPre s) (h : Inv s u)
    (hf : DFrame u v (Loc s u v)) (heap : HeapOk v) (mono : heapNext u ≤ heapNext v)
    (sp : v.getReg .x2 = u.getReg .x2) : Inv s v :=
  h.step hpre hf (fun _ ha ↦ Loc.w hpre h heap ha) heap mono sp

/-- A step that writes no memory keeps `Inv`. -/
theorem Inv.same {s u v : MachineState} (h : Inv s u) (hm : ∀ a, v.getMem a = u.getMem a)
    (sp : v.getReg .x2 = u.getReg .x2) : Inv s v := by
  have hn : heapNext v = heapNext u := by simp only [heapNext, hm]
  exact ⟨sp.trans h.sp, ⟨hn ▸ h.heap.lo, hn ▸ h.heap.hi⟩, hn ▸ h.mono,
    (h.frame.trans (DFrame.of_same hm _) fun _ h ↦ h).mono fun _ ha ↦ WalkW.mono hn.ge ha,
    fun i hi ↦ (hm _).trans (h.saved i hi)⟩

/-! ## Steps in the frame -/

/-- What a step past the prologue may write: `n` bytes from `lo`, the stack below the frame,
`NEXT`, the heap it allocates. -/
def Below (s v w : MachineState) (lo : Word) (n : Nat) (a : Word) : Prop :=
  Within a lo n ∨ Within a (s.getReg .x2 - 11392) 8736 ∨ Within a nextAddr 8 ∨ Fresh v w a

/-- A step from `v` to `w` writing `Below`, keeping `sp`. -/
structure Step (s v w : MachineState) (lo : Word) (n : Nat) : Prop where
  frame : DFrame v w (Below s v w lo n)
  heap : HeapOk w
  mono : heapNext v ≤ heapNext w
  sp : w.getReg .x2 = v.getReg .x2

/-- The `n` bytes from `lo` lie in the frame, below the saved registers. -/
def InFrame (s : MachineState) (lo : Word) (n : Nat) : Prop :=
  (s.getReg .x2 - 2656).toNat ≤ lo.toNat ∧ lo.toNat + n ≤ (s.getReg .x2 - 104).toNat

theorem inFrame {s : MachineState} (hpre : WalkPre s) {k n : Nat} (hk1 : 104 + n ≤ k)
    (hk2 : k ≤ 2656) : InFrame s (s.getReg .x2 - BitVec.ofNat 64 k) n := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  simp only [InFrame]
  constructor <;> addr_omega [hb1, hk1, hk2]

theorem Below.loc {s v w : MachineState} (hpre : WalkPre s) {lo : Word} {n : Nat}
    (hl : InFrame s lo n) {a : Word} (ha : Below s v w lo n a) : Loc s v w a := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  simp only [InFrame] at hl
  rcases ha with ha | ha | ha | ha
  · exact Or.inl (by addr_omega [ha, hl, hb1])
  · exact Or.inl (by addr_omega [ha, hb1])
  · exact Or.inr (Or.inl ha)
  · exact Or.inr (Or.inr ha)

theorem Inv.after {s v w : MachineState} (hpre : WalkPre s) (h : Inv s v) {lo : Word}
    {n : Nat} (hl : InFrame s lo n) (st : Step s v w lo n) : Inv s w :=
  h.loc hpre (st.frame.mono fun _ ha ↦ Below.loc hpre hl ha) st.heap st.mono st.sp

/-- A block that writes the `n` bytes from `lo`. -/
theorem Step.ofMemFrame {s v w : MachineState} (hpre : WalkPre s) (hh : HeapOk v) {lo : Word}
    {n : Nat} (hl : InFrame s lo n) (hf : MemFrame v w lo n) (sp : w.getReg .x2 = v.getReg .x2) :
    Step s v w lo n := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  simp only [InFrame] at hl
  have fr := DFrame.of_memFrame hf
  have he : heapNext w = heapNext v := by
    simp only [heapNext]
    exact congrArg BitVec.toNat (fr nextAddr fun i hi hw ↦ by addr_omega [hl, hw, hi, hb1])
  exact ⟨fr.mono fun a ha ↦ Or.inl ha, ⟨he ▸ hh.lo, he ▸ hh.hi⟩, he.ge, sp⟩

/-- A block that writes nothing. -/
theorem Step.same {s v w : MachineState} (hh : HeapOk v) (hm : ∀ a, w.getMem a = v.getMem a)
    (sp : w.getReg .x2 = v.getReg .x2) (lo : Word) (n : Nat) : Step s v w lo n := by
  have hn : heapNext w = heapNext v := by simp only [heapNext, hm]
  exact ⟨DFrame.of_same hm _, ⟨hn ▸ hh.lo, hn ▸ hh.hi⟩, hn.ge, sp⟩

/-- A doubleword in the frame apart from what a step writes keeps its value. -/
theorem Step.word {s v w : MachineState} (hpre : WalkPre s) {lo : Word} {n : Nat}
    (st : Step s v w lo n) {x : Word} (hx : Apart x 8 lo n)
    (hy : (s.getReg .x2 - 2656).toNat ≤ x.toNat ∧ x.toNat + 8 ≤ (s.getReg .x2).toNat) :
    w.getMem x = v.getMem x := by
  obtain ⟨hb1, hb2, -, -⟩ := bounds hpre
  have hh := st.heap.hi
  have hn := hpre.stack.next
  have ha := hpre.stack.above
  rw [stackLo_eq, stack_eq] at hn
  rw [stackLo_eq] at ha
  refine st.frame x fun i hi hw ↦ ?_
  simp only [Below, Fresh, heapNext, heapEnd] at hw hh ha
  rcases hw with hw | hw | hw | ⟨-, hw⟩ <;> addr_omega [hx, hy, hw, hi, hb1, hb2, hh, hn, ha]

/-- `.rodata` is kept. -/
theorem Inv.rodata {s u : MachineState} (hpre : WalkPre s) (h : Inv s u) : RodataOk u := by
  have r1 := hpre.outRodata
  have r4 := hpre.stack.rodata
  have hn := h.heap.hi
  have hrb : rodataBase.toNat = 2684354560 := rfl
  have hrs : rodataStart.toNat = 2684354560 := rfl
  rw [stackLo_eq, stack_eq] at r4
  refine hpre.rodata.dframe h.frame fun a ha hw ↦ ?_
  simp only [WalkW, Fresh, heapNext, heapEnd, stackLo_eq] at hw hn
  rcases hw with hw | hw | hw | hw
  · addr_omega [ha, hw, r1, hrb]
  · addr_omega [ha, hw, r4, hrb, hrs]
  · addr_omega [ha, hw, hrb]
  · addr_omega [ha, hw, hn, hrb]

/-! ## What is only read -/

/-- What is only read misses what the function writes. -/
theorem Inv.miss {s u : MachineState} (h : Inv s u) {a : Word} {n : Nat}
    (hr : ReadOnly s a n) (hn : a.toNat + n ≤ 2 ^ 64) : Misses (WalkW s u) a n := by
  obtain ⟨⟨hf, hx⟩, hs, ho, -⟩ := hr
  have hh := h.heap.hi
  intro y hy hw
  rcases hw with hw | hw | hw | ⟨w1, w2⟩
  · addr_omega [ho, hy, hw]
  · addr_omega [hs, hy, hw]
  · addr_omega [hx, hy, hw]
  · simp only [heapNext, heapEnd] at hf hh w1 w2
    addr_omega [hf, hy, w1, w2, hh, hn]

/-- What is only read misses the local writes. -/
theorem Inv.missLoc {s u v : MachineState} (h : Inv s u) (hv : HeapOk v) {a : Word} {n : Nat}
    (hr : ReadOnly s a n) (hn : a.toNat + n ≤ 2 ^ 64) : Misses (Loc s u v) a n := by
  obtain ⟨⟨hf, hx⟩, hs, -, -⟩ := hr
  have hm := h.mono
  have hh := hv.hi
  rw [stackLo_eq, stack_eq] at hs
  intro y hy hl
  simp only [Loc, Fresh] at hl
  simp only [heapNext, heapEnd] at hf hl hm hh
  rcases hl with hl | hl | hl
  · addr_omega [hs, hy, hl]
  · addr_omega [hx, hy, hl]
  · addr_omega [hf, hy, hl, hm, hh, hn]

/-- A doubleword of what is only read keeps its value. -/
theorem Inv.word {s u : MachineState} (h : Inv s u) {a : Word} {n : Nat} (hr : ReadOnly s a n)
    (hn : a.toNat + n ≤ 2 ^ 64) {x : Word} (h1 : a.toNat ≤ x.toNat)
    (h2 : x.toNat + 8 ≤ a.toNat + n) : u.getMem x = s.getMem x :=
  h.frame x ((h.miss hr hn).bytes h1 h2 hn)

/-! ## The transcript -/

/-- The transcript's address, `S - 2448`. -/
@[rv_addr] def tp (s : MachineState) : Word := s.getReg .x2 - 2448

/-- The program `walk` runs from its entry: `walkRust` of the `Bytecode` and the public input. -/
def prog (s : MachineState) : TM SummaryRust :=
  walkRust (Proofs.Bytecode.readBytecode s (s.getReg .x11)) (bytesAt s (s.getReg .x12) 32)

/-- The transcript `Transcript::new` starts, on `proof`. -/
def initT (s : MachineState) (proof : Proof) : TState :=
  TState.init proof (spongeNewRust (Proofs.Bytecode.readBytecode s (s.getReg .x11)).fiatShamirIv
    (bytesAt s (s.getReg .x12) 32))

/-- From `u` on, the code runs `C`, what is left of `prog s` from `initT s proof`, for every proof
the memory holds. -/
def Tracks (OI : MachineState → Word → List (List Opening) → Prop) (s u : MachineState)
    (C : TM SummaryRust) : Prop :=
  ∀ proof, ProofIn OI s (s.getReg .x13) proof → ∃ T, T.proof = proof ∧
    TranscriptAt u (tp s) T ∧ (prog s).run (initT s proof) = C.run T

section Tracks
variable {OI : MachineState → Word → List (List Opening) → Prop} {β : Type}
  {C : TM SummaryRust} {s u v : MachineState}

theorem Tracks.keep (h : Tracks OI s u C)
    (hk : ∀ T, TranscriptAt u (tp s) T → TranscriptAt v (tp s) T) : Tracks OI s v C :=
  fun proof hp ↦ by
    obtain ⟨T, e, hT, hr⟩ := h proof hp
    exact ⟨T, e, hk T hT, hr⟩

theorem Tracks.bind {A : TM β} {K : β → TM SummaryRust} {x : β}
    (h : Tracks OI s u (A >>= K)) (hk : KeepsProof A)
    (hA : ∀ T, TranscriptAt u (tp s) T → ∃ T', A.run T = some (x, T') ∧ TranscriptAt v (tp s) T') :
    Tracks OI s v (K x) := fun proof hp ↦ by
  obtain ⟨T₁, e₁, h₁, r₁⟩ := h proof hp
  obtain ⟨T₂, e₂, h₂⟩ := hA T₁ h₁
  refine ⟨T₂, (hk e₂).trans e₁, h₂, ?_⟩
  rw [r₁, StateT.run_bind, e₂]
  rfl

theorem Tracks.fail {A : TM β} {K : β → TM SummaryRust} (h : Tracks OI s u (A >>= K))
    (hA : ∀ T, TranscriptAt u (tp s) T → A.run T = none) :
    ∀ proof, ProofIn OI s (s.getReg .x13) proof → (prog s).run (initT s proof) = none :=
  fun proof hp ↦ by
    obtain ⟨T, -, hT, hr⟩ := h proof hp
    rw [hr, StateT.run_bind, hA T hT]
    rfl

theorem Tracks.require {c : Prop} [Decidable c] {K : Unit → TM SummaryRust}
    (h : Tracks OI s u (TM.require c >>= K)) (hc : c) : Tracks OI s u (K ()) :=
  Tracks.bind (v := u) h (KeepsProof.require c) fun T hT ↦
    ⟨T, by simp [TM.require, StateT.run, hc], hT⟩

theorem Tracks.require_fail {c : Prop} [Decidable c] {K : Unit → TM SummaryRust}
    (h : Tracks OI s u (TM.require c >>= K)) (hc : ¬ c) :
    ∀ proof, ProofIn OI s (s.getReg .x13) proof → (prog s).run (initT s proof) = none :=
  h.fail fun _ _ ↦ by simp [TM.require, StateT.run, hc]

theorem Tracks.done {r : SummaryRust} (h : Tracks OI s u (pure r)) :
    ∀ proof, ProofIn OI s (s.getReg .x13) proof →
      ∃ summary, verifyExecutionRust (Proofs.Bytecode.readBytecode s (s.getReg .x11))
        (bytesAt s (s.getReg .x12) 32) proof = some summary := fun proof hp ↦ by
  obtain ⟨T, -, -, hr⟩ := h proof hp
  refine ⟨r, ?_⟩
  show ((prog s).run (initT s proof)).map (·.1) = some r
  rw [hr]
  rfl

end Tracks

/-! ## Leaving -/

/-- The function has returned with its contract's post. -/
def Done (OI : MachineState → Word → List (List Opening) → Prop) (s t : MachineState) : Prop :=
  t.pc = returnAddress s ∧ Preserves s t ∧ WalkPost OI s t

end Rv64Verifier.Proofs.Walk
