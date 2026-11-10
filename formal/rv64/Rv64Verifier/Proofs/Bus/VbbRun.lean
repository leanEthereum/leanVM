import Rv64Verifier.Proofs.Bus.VbbSteps

/-!
# `verify_bus_balance`: the mirror's run, steps writing several regions, what stays

`Tracks M p s u C`: from `u` on, the code runs `C`, what is left of `M`: every transcript the
entry's stands for runs `M` as one the transcript at `u` stands for runs `C`. A callee that uses
the transcript moves it over one bind (`Tracks.bind`) or ends the whole run in `none`
(`Tracks.fail`).

A `StepR` writes a set `A` of the frame's bytes besides what every step may. `Free` is the part of
the frame the stages past the start write; `Kept` what lies elsewhere and is read later.
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript

/-! ## The mirror's run -/

def Tracks {α : Type} (M : TM α) (p : Word) (s u : MachineState) (C : TM α) : Prop :=
  ∀ T, TranscriptAt s p T → ∃ T', TranscriptAt u p T' ∧ M.run T = C.run T'

section Tracks
variable {α β : Type} {M C : TM α} {p : Word} {s u v : MachineState}

theorem Tracks.start (M : TM α) (p : Word) (s : MachineState) : Tracks M p s s M :=
  fun T hT ↦ ⟨T, hT, rfl⟩

theorem Tracks.keep (h : Tracks M p s u C) (hk : ∀ T, TranscriptAt u p T → TranscriptAt v p T) :
    Tracks M p s v C := fun T hT ↦ by
  obtain ⟨T₁, h₁, e₁⟩ := h T hT
  exact ⟨T₁, hk T₁ h₁, e₁⟩

theorem Tracks.bind {A : TM β} {K : β → TM α} {x : β} (h : Tracks M p s u (A >>= K))
    (hA : ∀ T, TranscriptAt u p T → ∃ T', A.run T = some (x, T') ∧ TranscriptAt v p T') :
    Tracks M p s v (K x) := fun T hT ↦ by
  obtain ⟨T₁, h₁, e₁⟩ := h T hT
  obtain ⟨T₂, e₂, h₂⟩ := hA T₁ h₁
  refine ⟨T₂, h₂, ?_⟩
  rw [e₁, StateT.run_bind, e₂]
  rfl

theorem Tracks.fail {A : TM β} {K : β → TM α} (h : Tracks M p s u (A >>= K))
    (hA : ∀ T, TranscriptAt u p T → A.run T = none) :
    ∀ T, TranscriptAt s p T → M.run T = none := fun T hT ↦ by
  obtain ⟨T₁, h₁, e₁⟩ := h T hT
  rw [e₁, StateT.run_bind, hA T₁ h₁]
  rfl

theorem Tracks.done {r : α} (h : Tracks M p s u (pure r)) :
    ∀ T, TranscriptAt s p T → ∃ T', TranscriptAt u p T' ∧ M.run T = some (r, T') :=
  fun T hT ↦ h T hT

theorem Tracks.require {c : Prop} [Decidable c] {K : Unit → TM α}
    (h : Tracks M p s u (TM.require c >>= K)) (hc : c) : Tracks M p s u (K ()) :=
  Tracks.bind (v := u) h fun T hT ↦ ⟨T, by simp [TM.require, StateT.run, hc], hT⟩

theorem Tracks.require_fail {c : Prop} [Decidable c] {K : Unit → TM α}
    (h : Tracks M p s u (TM.require c >>= K)) (hc : ¬ c) :
    ∀ T, TranscriptAt s p T → M.run T = none :=
  h.fail fun _ _ ↦ by simp [TM.require, StateT.run, hc]

end Tracks

/-- A transcript the memory at `p` stands for, with no openings and no roots. -/
def canonT (u : MachineState) (p : Word) : TState :=
  ⟨⟨eListAt u (streamPtr u p) (streamLen u p), []⟩, spongeAt u (p + 8),
    (u.getMem (p + 344)).toNat, (u.getMem (p + 352)).toNat, []⟩

theorem canonT_at (u : MachineState) (p : Word) : TranscriptAt u p (canonT u p) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The program `verify_bus_balance` runs from `s`. -/
def prog (bev : MachineState → Word → List E → Option E) (s : MachineState) : TM BusResultRust :=
  verifyBusBalanceM (bev s (bytecodeOf s (s.getReg .x11))) (busLayoutAt s (s.getReg .x11))

/-- The function has returned with its contract's post. -/
def Done (bev : MachineState → Word → List E → Option E) (s t : MachineState) : Prop :=
  t.pc = returnAddress s ∧ Preserves s t ∧ BusBalancePost bev s t

/-- The `Err` exit of a run the mirror fails. -/
theorem errDone {bev : MachineState → Word → List E → Option E} {s u : MachineState}
    (hpre : BusBalancePre s) (h : Inv s u) (hx18 : u.getReg .x18 = s.getReg .x10)
    (hpc : u.pc = 0x80007104)
    (hnone : ∀ T, TranscriptAt s (s.getReg .x12) T → (prog bev s).run T = none) :
    ∃ t, Reaches Image.code u t ∧ Done bev s t := by
  obtain ⟨t, hr, ex, hcap⟩ := errExit hpre h hx18 hpc
  refine ⟨t, hr, ex.pc, ex.preserves, ex.heap, ex.mono, fun T hT ↦ ?_, ex.frame⟩
  rw [show (verifyBusBalanceM (bev s (bytecodeOf s (s.getReg .x11)))
      (busLayoutAt s (s.getReg .x11))).run T = none from hnone T hT]
  exact hcap

/-! ## Steps writing a set of the frame's bytes -/

/-- A step writing `A`, the transcript's sponge and offsets, the stack below the frame, `NEXT`
and the heap it allocates, keeping `sp`. -/
structure StepR (s v w : MachineState) (A : Word → Prop) : Prop where
  frame : DFrame v w fun a ↦ A a ∨ Within a (s.getReg .x12 + 8) 344 ∨
    Within a (s.getReg .x2 - 4544) 3200 ∨ Within a nextAddr 8 ∨ Fresh v w a
  heap : HeapOk w
  mono : heapNext v ≤ heapNext w
  sp : w.getReg .x2 = v.getReg .x2

/-- `A` lies in the frame below the saved registers. -/
def FrameW (s : MachineState) (A : Word → Prop) : Prop :=
  ∀ a, A a → Within a (s.getReg .x2 - 1344) 1240

section StepR
variable {s u v w : MachineState} {A B : Word → Prop}

theorem StepT.toR {lo : Word} {n : Nat} (st : StepT s v w lo n) : StepR s v w (Within · lo n) :=
  ⟨st.frame.mono fun a ha ↦ by
    rcases ha with (ha | ha | ha | ha) | ha
    · exact Or.inl ha
    · exact Or.inr (Or.inr (Or.inl ha))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ha)))
    · exact Or.inr (Or.inl ha), st.heap, st.mono, st.sp⟩

theorem Step.toR {lo : Word} {n : Nat} (st : Step s v w lo n) : StepR s v w (Within · lo n) :=
  st.toT.toR

theorem StepR.weaken (h : StepR s v w A) (hAB : ∀ a, A a → B a) : StepR s v w B :=
  ⟨h.frame.mono fun a ha ↦ ha.imp_left (hAB a), h.heap, h.mono, h.sp⟩

theorem StepR.trans (h₁ : StepR s u v A) (h₂ : StepR s v w B) :
    StepR s u w fun a ↦ A a ∨ B a where
  frame := (h₁.frame.mono fun a ha ↦ by
      rcases ha with ha | ha | ha | ha | ⟨f1, f2⟩
      · exact Or.inl (Or.inl ha)
      · exact Or.inr (Or.inl ha)
      · exact Or.inr (Or.inr (Or.inl ha))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨f1, by have := h₂.mono; omega⟩)))).trans
    h₂.frame fun a ha ↦ by
      rcases ha with ha | ha | ha | ha | ⟨f1, f2⟩
      · exact Or.inl (Or.inr ha)
      · exact Or.inr (Or.inl ha)
      · exact Or.inr (Or.inr (Or.inl ha))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by have := h₁.mono; omega, f2⟩)))
  heap := h₂.heap
  mono := h₁.mono.trans h₂.mono
  sp := h₂.sp.trans h₁.sp

/-- A block that writes nothing. -/
theorem StepR.same (hm : ∀ a, w.getMem a = v.getMem a) (hh : HeapOk v)
    (sp : w.getReg .x2 = v.getReg .x2) : StepR s v w A := by
  have hn : heapNext w = heapNext v := by simp only [heapNext, hm]
  exact ⟨DFrame.of_same hm _, ⟨hn ▸ hh.lo, hn ▸ hh.hi⟩, hn.ge, sp⟩

/-- A block that writes the `n` bytes from `lo`, in `A`. -/
theorem StepR.ofMemFrame {lo : Word} {n : Nat} (hh : HeapOk v)
    (hf : MemFrame v w lo n) (hA : ∀ a, Within a lo n → A a) (hn : Apart lo n nextAddr 8)
    (sp : w.getReg .x2 = v.getReg .x2) : StepR s v w A := by
  have fr := DFrame.of_memFrame hf
  have he : heapNext w = heapNext v := by
    simp only [heapNext]
    exact congrArg BitVec.toNat (fr nextAddr fun i hi hw ↦ by addr_omega [hn, hw, hi])
  exact ⟨fr.mono fun a ha ↦ Or.inl (hA a ha), ⟨he ▸ hh.lo, he ▸ hh.hi⟩, he.ge, sp⟩

theorem Inv.afterR (hpre : BusBalancePre s) (h : Inv s v) (hA : FrameW s A)
    (st : StepR s v w A) : Inv s w := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hS := hpre.self.self
  have ss := hpre.selfStack
  rw [stackLo_eq] at ss
  refine h.step hpre st.frame (fun a ha ↦ ?_) st.heap st.mono st.sp
  rcases ha with ha | ha | ha
  · have := hA a ha
    exact ⟨Or.inr (Or.inr (Or.inl (by rw [stackLo_eq]; addr_omega [this, hb1]))),
      by addr_omega [this, hb1]⟩
  · exact ⟨Or.inr (Or.inl ha), by addr_omega [ha, hS, ss, hb1]⟩
  · exact Loc.w hpre h st.heap (by
      rcases ha with ha | ha | ha
      · exact Or.inl (by addr_omega [ha, hb1])
      · exact Or.inr (Or.inl ha)
      · exact Or.inr (Or.inr ha))

/-- A word in the frame or in a buffer allocated since the entry, apart from `A`, keeps its
value. -/
theorem StepR.word (hpre : BusBalancePre s) (st : StepR s v w A) {x : Word}
    (hx : ∀ y, Within y x 8 → ¬ A y)
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
  rcases hw with hw | hw
  · exact hx _ (by rcases hy with hy | hy <;> simp only [heapNext] at hy hh <;>
      addr_omega [hy, hi, hb2, hh]) hw
  simp only [Fresh, Outside, heapNext, heapEnd] at hw hy hh hm sf
  rcases hy with hy | hy <;> rcases hw with hw | hw | hw | hw <;>
    addr_omega [hy, hw, hi, hb1, hb2, hh, hm, hS, ss, sf]

theorem StepR.bufWord (hpre : BusBalancePre s) (st : StepR s v w A) (hA : FrameW s A)
    {p x : Word} {m : Nat} (hb : NewBuf s v p m 8) (h1 : p.toNat ≤ x.toNat)
    (h2 : x.toNat + 8 ≤ p.toNat + m) : w.getMem x = v.getMem x := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hhi := st.heap.hi
  have hlo := hpre.heap.lo
  simp only [NewBuf] at hb
  rcases hb.2 with h0 | ⟨b1, b2⟩
  · omega
  have hx8 : x.toNat + 8 ≤ heapNext v := by omega
  refine st.word hpre (fun y hy hy' ↦ ?_) (Or.inr ⟨by omega, hx8⟩)
  have := hA y hy'
  simp only [heapNext, heapEnd, heapStart] at hhi hlo b1 hx8
  have hm := st.mono
  simp only [heapNext] at hm
  addr_omega [this, hy, b1, hx8, hb1, hm, hhi, hlo]

/-- A `Vec<E>` whose header lies in the frame apart from `A` keeps what it holds. -/
theorem _root_.Rv64Verifier.Transcript.NewVecE.keepR (hpre : BusBalancePre s) (st : StepR s v w A) (hA : FrameW s A)
    {a : Word} {xs : List E} (h : NewVecE s v a xs)
    (hin : (s.getReg .x2 - 1344).toNat ≤ a.toNat ∧ a.toNat + 24 ≤ (s.getReg .x2).toNat)
    (hx : ∀ y, Within y a 24 → ¬ A y) : NewVecE s w a xs := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hw (j : Nat) (hj : j + 8 ≤ 24) : w.getMem (a + BitVec.ofNat 64 j) =
      v.getMem (a + BitVec.ofNat 64 j) :=
    st.word hpre (fun y hy ↦ hx y (by addr_omega [hy, hin, hj, hb1]))
      (Or.inl (by addr_omega [hin, hj, hb1]))
  have e0 : w.getMem a = v.getMem a := by simpa using hw 0 (by omega)
  have e8 : w.getMem (a + 8) = v.getMem (a + 8) := hw 8 (by omega)
  have e16 : w.getMem (a + 16) = v.getMem (a + 16) := hw 16 (by omega)
  have hm := st.mono
  have hvec := h.vec
  have hbuf := h.buf
  have hlen := hvec.len
  refine ⟨hvec.keep e0 e8 e16 hm, ?_, ?_⟩
  · simp only [NewBuf, vecPtr, vecCap] at hbuf ⊢
    rw [e8, e0]
    exact ⟨hbuf.1, hbuf.2.imp_right fun h' ↦ ⟨h'.1, by omega⟩⟩
  · rw [← h.elems]
    simp only [vecEs, vecPtr, vecLen] at hlen hbuf ⊢
    rw [e8, e16]
    refine eListAt_congr fun i hi ↦ ?_
    have hc : 24 * i + 24 ≤ (vecCap v a).toNat * 24 := by omega
    have hbd : (v.getMem (a + 8)).toNat + (vecCap v a).toNat * 24 ≤ 2 ^ 64 := by
      rcases hbuf.2 with h0 | ⟨b1, b2⟩
      · omega
      · have := st.heap.hi
        simp only [heapNext, heapEnd] at *; omega
    have bw (j : Nat) (hj : j + 8 ≤ 24) : w.getMem (v.getMem (a + 8) + BitVec.ofNat 64 (24 * i) +
        BitVec.ofNat 64 j) = v.getMem (v.getMem (a + 8) + BitVec.ofNat 64 (24 * i) +
        BitVec.ofNat 64 j) :=
      st.bufWord hpre hA hbuf (by addr_omega [hbd, hc, hj]) (by addr_omega [hbd, hc, hj])
    exact eAt_congr (by simpa using bw 0 (by omega)) (bw 8 (by omega)) (bw 16 (by omega))

theorem _root_.Rv64Verifier.Transcript.NewVecE.widen {a : Word} {xs : List E} (h : NewVecE u v a xs)
    (hm : heapNext s ≤ heapNext u) : NewVecE s v a xs := by
  have hb := h.buf
  simp only [NewBuf] at hb
  exact ⟨h.vec, ⟨hb.1, hb.2.imp_right fun h' ↦ ⟨by omega, h'.2⟩⟩, h.elems⟩

theorem LayoutAt.keepR (hpre : BusBalancePre s) (st : StepR s v w A) (hA : FrameW s A) {a : Word}
    {l : BusLayoutRust} (h : LayoutAt s v a l) (hin : InFrame s a 56)
    (hap : ∀ y, Within y a 56 → ¬ A y) : LayoutAt s w a l := by
  obtain ⟨hb1, hb2, -, -⟩ := bounds hpre
  simp only [InFrame] at hin
  have hw (j : Nat) (hj : j + 8 ≤ 56) : w.getMem (a + BitVec.ofNat 64 j) =
      v.getMem (a + BitVec.ofNat 64 j) :=
    st.word hpre (fun y hy ↦ hap y (by addr_omega [hy, hin, hj, hb1]))
      (Or.inl (by addr_omega [hin, hj, hb1]))
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
    rw [st.bufWord hpre hA hb (by addr_omega [hbd, hc]) (by addr_omega [hbd, hc]),
      st.bufWord hpre hA hb (by addr_omega [hbd, hc]) (by addr_omega [hbd, hc])]
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

end StepR

/-! ## What the start leaves for the rest -/

/-- The frame's bytes the stages past the start may write (from `sp`: `[0, 32)`, `[40, 80)`,
`[88, 96)`, `[128, 144)`, `[200, 208)`, `[216, 264)`, `[480, 1240)`). -/
def Free (s : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x2 - 1344) 32 ∨ Within a (s.getReg .x2 - 1304) 40 ∨
    Within a (s.getReg .x2 - 1256) 8 ∨ Within a (s.getReg .x2 - 1216) 16 ∨
    Within a (s.getReg .x2 - 1144) 8 ∨ Within a (s.getReg .x2 - 1128) 48 ∨
    Within a (s.getReg .x2 - 864) 760

theorem Free.frameW {s : MachineState} (hpre : BusBalancePre s) : FrameW s (Free s) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  intro a ha
  rcases ha with ha | ha | ha | ha | ha | ha | ha <;> addr_omega [ha, hb1]

/-- `E` of its three limbs. -/
def eOf3 (a b c : Word) : E := E.ofLimbs (BF64.ofBitVec a) (BF64.ofBitVec b) (BF64.ofBitVec c)

/-- The values the start computes that the stages after it read from the frame. -/
structure Start where
  alphas : List E
  beta0 : Word
  beta1 : Word
  beta2 : Word
  count0 : Word
  count1 : Word

def Start.beta (k : Start) : E := eOf3 k.beta0 k.beta1 k.beta2

/-- The frame's words outside `Free` that the stages past the start read. -/
structure Kept (s u : MachineState) (k : Start) : Prop where
  out : u.getMem (s.getReg .x2 - 1312) = s.getReg .x10
  pushLen : u.getMem (s.getReg .x2 - 1264) = vecLen s (s.getReg .x11 + 24)
  countLen : u.getMem (s.getReg .x2 - 1248) = vecLen s (s.getReg .x11 + 72)
  layout : u.getMem (s.getReg .x2 - 1240) = s.getReg .x11
  count1 : u.getMem (s.getReg .x2 - 1232) = k.count1
  count0 : u.getMem (s.getReg .x2 - 1224) = k.count0
  beta1 : u.getMem (s.getReg .x2 - 1200) = k.beta1
  beta0 : u.getMem (s.getReg .x2 - 1192) = k.beta0
  beta2 : u.getMem (s.getReg .x2 - 1184) = k.beta2
  lm : u.getMem (s.getReg .x2 - 1136) = logMem s
  lb : u.getMem (s.getReg .x2 - 1152) = logBc s
  pullPtr : u.getMem (s.getReg .x2 - 1168) = vecPtr s (s.getReg .x11 + 48)
  pullLen : u.getMem (s.getReg .x2 - 1176) = vecLen s (s.getReg .x11 + 48)
  countPtr : u.getMem (s.getReg .x2 - 1160) = vecPtr s (s.getReg .x11 + 72)
  push : LayoutAt s u (s.getReg .x2 - 1080)
    (busLayoutRust [0, (logMem s).toNat, (logBc s).toNat] (busLayoutAt s (s.getReg .x11)).push)
  pull : LayoutAt s u (s.getReg .x2 - 1024)
    (busLayoutRust [0, (logMem s).toNat, (logBc s).toNat] (busLayoutAt s (s.getReg .x11)).pull)
  count : LayoutAt s u (s.getReg .x2 - 968) (busLayoutRust [] (busLayoutAt s (s.getReg .x11)).count)
  alphas : NewVecE s u (s.getReg .x2 - 912) k.alphas
  weights : NewVecE s u (s.getReg .x2 - 888) (eqKernelRust k.alphas)

/-- The words at `S - j`, `j` from `n` down, miss `Free`. -/
theorem Free.miss {s : MachineState} (hpre : BusBalancePre s) {j n : Nat} (hj : n ≤ j)
    (hj2 : j ≤ 1344)
    (h : ∀ i, j - n < i → i ≤ j → (1312 < i ∧ i ≤ 1344 → False) ∧ (1264 < i ∧ i ≤ 1304 → False) ∧
      (1248 < i ∧ i ≤ 1256 → False) ∧ (1200 < i ∧ i ≤ 1216 → False) ∧
      (1136 < i ∧ i ≤ 1144 → False) ∧ (1080 < i ∧ i ≤ 1128 → False) ∧ (104 < i ∧ i ≤ 864 → False)) :
    ∀ y, Within y (s.getReg .x2 - BitVec.ofNat 64 j) n → ¬ Free s y := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  intro y hy hf
  have hyn : (s.getReg .x2).toNat - j ≤ y.toNat ∧ y.toNat < (s.getReg .x2).toNat - j + n := by
    addr_omega [hy, hb1, hj, hj2]
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := h ((s.getReg .x2).toNat - y.toNat) (by omega)
    (by omega)
  rcases hf with hf | hf | hf | hf | hf | hf | hf
  · exact c1 (by addr_omega [hf, hb1, hyn])
  · exact c2 (by addr_omega [hf, hb1, hyn])
  · exact c3 (by addr_omega [hf, hb1, hyn])
  · exact c4 (by addr_omega [hf, hb1, hyn])
  · exact c5 (by addr_omega [hf, hb1, hyn])
  · exact c6 (by addr_omega [hf, hb1, hyn])
  · exact c7 (by addr_omega [hf, hb1, hyn])

/-- A step writing only `Free` keeps what the start left. -/
theorem Kept.step {s v w : MachineState} {k : Start} (hpre : BusBalancePre s) (h : Kept s v k)
    (st : StepR s v w (Free s)) : Kept s w k := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hA := Free.frameW hpre
  have wd (j : Nat) (hj : 8 ≤ j) (hj2 : j ≤ 1344)
      (hm : ∀ i, j - 8 < i → i ≤ j → (1312 < i ∧ i ≤ 1344 → False) ∧
        (1264 < i ∧ i ≤ 1304 → False) ∧ (1248 < i ∧ i ≤ 1256 → False) ∧
        (1200 < i ∧ i ≤ 1216 → False) ∧ (1136 < i ∧ i ≤ 1144 → False) ∧
        (1080 < i ∧ i ≤ 1128 → False) ∧ (104 < i ∧ i ≤ 864 → False)) :
      w.getMem (s.getReg .x2 - BitVec.ofNat 64 j) = v.getMem (s.getReg .x2 - BitVec.ofNat 64 j) :=
    st.word hpre (Free.miss hpre hj hj2 hm) (Or.inl (by addr_omega [hb1, hj, hj2]))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← h.out]; exact wd 1312 (by omega) (by omega) (by intro i h1 h2; omega)
  · rw [← h.pushLen]; exact wd 1264 (by omega) (by omega) (by intro i h1 h2; omega)
  · rw [← h.countLen]; exact wd 1248 (by omega) (by omega) (by intro i h1 h2; omega)
  · rw [← h.layout]; exact wd 1240 (by omega) (by omega) (by intro i h1 h2; omega)
  · rw [← h.count1]; exact wd 1232 (by omega) (by omega) (by intro i h1 h2; omega)
  · rw [← h.count0]; exact wd 1224 (by omega) (by omega) (by intro i h1 h2; omega)
  · rw [← h.beta1]; exact wd 1200 (by omega) (by omega) (by intro i h1 h2; omega)
  · rw [← h.beta0]; exact wd 1192 (by omega) (by omega) (by intro i h1 h2; omega)
  · rw [← h.beta2]; exact wd 1184 (by omega) (by omega) (by intro i h1 h2; omega)
  · rw [← h.lm]; exact wd 1136 (by omega) (by omega) (by intro i h1 h2; omega)
  · rw [← h.lb]; exact wd 1152 (by omega) (by omega) (by intro i h1 h2; omega)
  · rw [← h.pullPtr]; exact wd 1168 (by omega) (by omega) (by intro i h1 h2; omega)
  · rw [← h.pullLen]; exact wd 1176 (by omega) (by omega) (by intro i h1 h2; omega)
  · rw [← h.countPtr]; exact wd 1160 (by omega) (by omega) (by intro i h1 h2; omega)
  · exact h.push.keepR hpre st hA (inFrame hpre (k := 1080) (n := 56) (by omega) (by omega))
      (Free.miss hpre (j := 1080) (by omega) (by omega) (by intro i h1 h2; omega))
  · exact h.pull.keepR hpre st hA (inFrame hpre (k := 1024) (n := 56) (by omega) (by omega))
      (Free.miss hpre (j := 1024) (by omega) (by omega) (by intro i h1 h2; omega))
  · exact h.count.keepR hpre st hA (inFrame hpre (k := 968) (n := 56) (by omega) (by omega))
      (Free.miss hpre (j := 968) (by omega) (by omega) (by intro i h1 h2; omega))
  · exact h.alphas.keepR hpre st hA (by addr_omega [hb1])
      (Free.miss hpre (j := 912) (by omega) (by omega) (by intro i h1 h2; omega))
  · exact h.weights.keepR hpre st hA (by addr_omega [hb1])
      (Free.miss hpre (j := 888) (by omega) (by omega) (by intro i h1 h2; omega))

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
