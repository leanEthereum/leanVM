import Rv64Verifier.Proofs.Walk.R5
import Rv64Verifier.Proofs.Layout.ContractsBuild
import Rv64Verifier.Proofs.Layout.Keep
import Rv64Verifier.Proofs.Layout.CloneLemmas

/-!
# `walk`: `tables()`, `flushes_keccak`'s head (R6, first part)

From `state_step`'s call (`AtR5`, `0x80004a90`): `state_step` on the empty `Flushes` at
`sp + 1168`, `alloc(8, 288)` for the operands' `Vec<Form>` at `sp + 2504` (`reserve(12)`: room
enough), the twelve `col(2 + i, 0)` into `sp + 1728`, each copied to `P + 24 i`, then
`bytecode(KECCAK_CNT_BC, OP_KECCAK, operands)`, to the call of `keccak_cell_lanes(false)`
(`AtR6a`, `0x80004d10`).

The code reuses `s0..s11` from here on, so `walk`'s state is kept in memory only (`M6`): every step
writes the frame past the transcript, the heights' lengths, the stack below the frame, `NEXT` or
the heap allocated since `table_log_heights` (`W6`, `M6.step`). A layout function's frame is a
`Layout.DFrame` (doublewords that do not wrap); `Inv` keeps the same kind.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F4
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-! ## `walk`'s state in memory -/

/-- `walk`'s state from `tables()` on, in memory only (the code reuses `s0..s11`): `Inv`, the
transcript, `build_layout`'s head (`HeadOk`, `log_bytecode` at `sp + 160`), `table_rows` at `R`
(`sp + 176`), the heights at `Q` (`sp + 192`, capacity at `sp + 120`), the spills; what `walk`
owned at `table_log_heights`' end lies below `B`. -/
structure M6 (OI : MachineState → Word → List (List Opening) → Prop) (s u : MachineState)
    (A : List E) (k : Nat) (R Q : Word) (B : Nat) : Prop where
  inv : Inv s u
  proofPtr : u.getMem (tp s) = s.getReg .x13
  checked : byteAt u (tp s + 360) = 1
  ok : HeadOk s A k
  rate : 1#64 ≤ rateOf A ∧ rateOf A ≤ 4#64
  tracks : Tracks OI s u (afterRate s A)
  lb : u.getMem (s.getReg .x2 - 2496) = BitVec.ofNat 64 (k - 4)
  bufR : R.toNat % 8 = 0 ∧ 0x20000000 ≤ R.toNat ∧ R.toNat + 48 ≤ Q.toNat
  bufQ : Q.toNat % 8 = 0 ∧ heapNext s ≤ Q.toNat ∧ Q.toNat + 48 ≤ B ∧ B ≤ heapNext u
  rows : ∀ i < 6, u.getMem (R + BitVec.ofNat 64 (8 * i)) = (rowsOf A).getD i 0
  heights : ∀ i < 6, u.getMem (Q + BitVec.ofNat 64 (8 * i)) =
    BitVec.ofNat 64 ((LayoutMirror.tableLogHeightsRust (rowsOf A)).getD i 0)
  cap : u.getMem (s.getReg .x2 - 2536) = 6
  ptr : u.getMem (s.getReg .x2 - 2464) = Q
  spills : u.getMem (s.getReg .x2 - 2584) = rateOf A ∧
    u.getMem (s.getReg .x2 - 2576) = s.getMem (s.getReg .x12 + 16) ∧
    u.getMem (s.getReg .x2 - 2568) = s.getMem (s.getReg .x12) ∧
    u.getMem (s.getReg .x2 - 2560) = s.getMem (s.getReg .x12 + 24) ∧
    u.getMem (s.getReg .x2 - 2552) = s.getMem (s.getReg .x12 + 8) ∧
    u.getMem (s.getReg .x2 - 2528) = s.getReg .x11 ∧ u.getMem (s.getReg .x2 - 2512) = lmOf A ∧
    u.getMem (s.getReg .x2 - 2488) = s.getReg .x10 ∧ u.getMem (s.getReg .x2 - 2480) = R

/-- What a step past `table_log_heights` may write: the frame from `sp + 576` (past the transcript)
and the slots at `sp + 136`, `sp + 152`, `sp + 184`, `sp + 200`, the stack below the frame, `NEXT`,
the heap from `B` on. -/
def W6 (s : MachineState) (B : Nat) (v : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x2 - 2080) 1976 ∨ Within a (s.getReg .x2 - 2520) 8 ∨
    (Within a (s.getReg .x2 - 2504) 8 ∨ Within a (s.getReg .x2 - 2472) 8 ∨
      Within a (s.getReg .x2 - 2456) 8) ∨ Within a (s.getReg .x2 - 11392) 8736 ∨
    Within a nextAddr 8 ∨ (B ≤ a.toNat ∧ a.toNat < heapNext v)

theorem M6.step {OI : MachineState → Word → List (List Opening) → Prop} {s u v : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} (hpre : WalkPre s) (h : M6 OI s u A k R Q B)
    (fr : Rv64Verifier.Layout.DFrame u v (W6 s B v)) (hv : HeapOk v)
    (mono : heapNext u ≤ heapNext v) (sp : v.getReg .x2 = u.getReg .x2) : M6 OI s v A k R Q B := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have hh := hv.hi
  have hm := h.inv.mono
  obtain ⟨q1, q2, q3, q4⟩ := h.bufQ
  obtain ⟨r1, r2, r3⟩ := h.bufR
  have hhu := h.inv.heap.hi
  simp only [heapEnd] at hh hhu
  have I : Inv s v := h.inv.stepL hpre fr (fun a ha ↦ by
    simp only [W6, Within] at ha
    rcases ha with ha | ha | (ha | ha | ha) | ha | ha | ⟨ha1, ha2⟩
    all_goals first
      | exact ⟨Or.inr (Or.inl (by rw [stackLo_eq, stack_eq]; simp only [Within]; addr_omega [ha, hb1])),
          by simp only [Within]; addr_omega [ha, hb1]⟩
      | exact ⟨Or.inr (Or.inr (Or.inl (by simp only [Within]; exact ha))),
          by simp only [Within]; addr_omega [ha, hb1]⟩
      | exact ⟨Or.inr (Or.inr (Or.inr ⟨by omega, ha2⟩)),
          by simp only [Within, heapNext] at ha2 hh ⊢; addr_omega [ha2, hh, hb1]⟩) hv mono sp
  have keep (x : Word) (hx : ((s.getReg .x2 - 2656).toNat ≤ x.toNat ∧ x.toNat + 8 ≤ (s.getReg .x2 - 2520).toNat) ∨
      ((s.getReg .x2 - 2512).toNat ≤ x.toNat ∧ x.toNat + 8 ≤ (s.getReg .x2 - 2504).toNat) ∨
      ((s.getReg .x2 - 2496).toNat ≤ x.toNat ∧ x.toNat + 8 ≤ (s.getReg .x2 - 2472).toNat) ∨
      ((s.getReg .x2 - 2464).toNat ≤ x.toNat ∧ x.toNat + 8 ≤ (s.getReg .x2 - 2456).toNat) ∨
      ((s.getReg .x2 - 2448).toNat ≤ x.toNat ∧ x.toNat + 8 ≤ (s.getReg .x2 - 2080).toNat) ∨
      (0x20 ≤ x.toNat ∧ x.toNat + 8 ≤ B)) : v.getMem x = u.getMem x :=
    fr x (fun y hy hw ↦ by
      simp only [W6, Within, heapNext] at hy hw hh hhu q4 ⊢
      rcases hw with hw | hw | (hw | hw | hw) | hw | hw | hw <;> addr_omega [hx, hy, hw, hb1, q4, hhu, hh])
      (by simp only [heapNext] at hhu q4; addr_omega [hx, hb1, q4, hhu])
  have hT (T : TState) (hT : TranscriptAt u (tp s) T) : TranscriptAt v (tp s) T := by
    obtain ⟨e0, e1, e2⟩ := proofVals hpre h.inv h.proofPtr
    have pRO := hpre.proofRO
    have sRO := hpre.streamRO
    have hP := hpre.proof
    have hS := hpre.stream
    simp only [ReadOnly, Outside, stack_eq, heapEnd] at pRO sRO
    obtain ⟨⟨p1, p1'⟩, p2, -⟩ := pRO
    obtain ⟨⟨s1, s1'⟩, s2, -⟩ := sRO
    simp only [Region] at hP
    refine (lframe_d fr).transcriptAt hT (tok hpre h.inv h.proofPtr) ?_ ?_ ?_ ?_
    · intro y hy hw
      simp only [W6, Within, tp, heapNext] at hy hw hh
      rcases hw with (hw | hw | (hw | hw | hw) | hw | hw | hw) | hw <;> addr_omega [hy, hw, hh, hb1]
    · rw [e0]; intro y hy hw
      simp only [W6, Within, heapNext] at hy hw hh hm p1
      rcases hw with (hw | hw | (hw | hw | hw) | hw | hw | hw) | hw <;>
        addr_omega [hy, hw, hh, hb1, p1, p1', p2, hP, q2, q3, q4, hm]
    · rw [e1, e2]; intro y hy hw
      simp only [W6, Within, heapNext] at hy hw hh hm s1
      rcases hS with h0 | h0
      · rw [h0] at hy; omega
      simp only [Region] at h0
      rcases hw with (hw | hw | (hw | hw | hw) | hw | hw | hw) | hw <;>
        addr_omega [hy, hw, hh, hb1, s1, s1', s2, h0, q2, q3, q4, hm]
    · intro y hy hw
      simp only [W6, Within, tp, heapNext] at hy hw hh
      rcases hw with (hw | hw | (hw | hw | hw) | hw | hw | hw) | hw <;> addr_omega [hy, hw, hh, hb1]
  have hn : B ≤ heapNext v := by omega
  exact {
    inv := I
    proofPtr := by rw [keep _ (by rw [tp]; addr_omega [hb1])]; exact h.proofPtr
    checked := by
      have ha : (tp s + 360).toNat % 8 = 0 := by rw [tp]; addr_omega [hb1, hb3]
      rw [byteAt_congr ha (keep _ (by rw [tp]; addr_omega [hb1]))]; exact h.checked
    ok := h.ok
    rate := h.rate
    tracks := h.tracks.keep hT
    lb := by rw [keep _ (by addr_omega [hb1])]; exact h.lb
    bufR := ⟨r1, r2, r3⟩
    bufQ := ⟨q1, q2, q3, hn⟩
    rows := fun i hi ↦ by rw [keep _ (by addr_omega [hi, r1, r2, r3, q3, q4, hhu])]; exact h.rows i hi
    heights := fun i hi ↦ by rw [keep _ (by addr_omega [hi, q3, r2, r3, q4, hhu])]; exact h.heights i hi
    cap := by rw [keep _ (by addr_omega [hb1])]; exact h.cap
    ptr := by rw [keep _ (by addr_omega [hb1])]; exact h.ptr
    spills := by
      obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h.spills
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        rw [keep _ (by addr_omega [hb1])] <;> assumption }

theorem AtR5.toM6 {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {Q : Word} (h : AtR5 OI s u A k Q) :
    M6 OI s u A k (u.getReg .x18) Q (heapNext u) := by
  obtain ⟨q1, q2, q3, q4⟩ := h.q
  have hb := h.buf
  exact {
    inv := h.inv
    proofPtr := h.proofPtr
    checked := h.checked
    ok := h.ok
    rate := h.rate
    tracks := h.tracks
    lb := h.lb
    bufR := ⟨hb.1, hb.2.1, q3⟩
    bufQ := ⟨q2, q1, q4, le_refl _⟩
    rows := fun i hi ↦ h.toHead.row hi
    heights := h.heights
    cap := h.cap
    ptr := h.ptr
    spills := h.spills }

/-! ## An empty `Flushes` -/

theorem flushesOk_empty {u : MachineState} {a : Word}
    (h0 : u.getMem a = 0) (h8 : u.getMem (a + 8) = 8) (h16 : u.getMem (a + 16) = 0)
    (h24 : u.getMem (a + 24) = 0) (h32 : u.getMem (a + 24 + 8) = 8)
    (h40 : u.getMem (a + 24 + 16) = 0) :
    Rv64Verifier.Layout.FlushesOk u a ∧ Rv64Verifier.Layout.flushesOf u a = {} ∧
      ∀ x, ¬ Rv64Verifier.Layout.flushesDeep u a x := by
  have e0 : (0 : Word).toNat = 0 := rfl
  have e8 : (8 : Word).toNat = 8 := rfl
  have v1 : Rv64Verifier.Layout.FormVecsOk u a := {
    vec := ⟨by simp only [RawVecOk, Buf, vecCap, vecPtr]; rw [h0, h8, e0, e8]; exact ⟨rfl, Or.inl rfl⟩,
      by simp only [vecLen, vecCap, h0, h16]; exact le_refl _⟩
    elems := fun i hi ↦ by simp only [vecLen, h16, e0] at hi; omega
    sep := fun i hi ↦ by simp only [vecLen, h16, e0] at hi; omega }
  have v2 : Rv64Verifier.Layout.FormVecsOk u (a + 24) := {
    vec := ⟨by simp only [RawVecOk, Buf, vecCap, vecPtr]; rw [h24, h32, e0, e8]; exact ⟨rfl, Or.inl rfl⟩,
      by simp only [vecLen, vecCap, h24, h40]; exact le_refl _⟩
    elems := fun i hi ↦ by simp only [vecLen, h40, e0] at hi; omega
    sep := fun i hi ↦ by simp only [vecLen, h40, e0] at hi; omega }
  have nd : ∀ x, ¬ Rv64Verifier.Layout.flushesDeep u a x := fun x hx ↦ by
    simp only [Rv64Verifier.Layout.flushesDeep, Rv64Verifier.Layout.formVecsDeep,
      Rv64Verifier.Layout.formVecsBuf, vecCap, vecLen, vecPtr, h0, h16, h24, h40, Within] at hx
    rcases hx with (hx | ⟨i, hi, -⟩) | (hx | ⟨i, hi, -⟩)
    · have : (0 : Word).toNat = 0 := rfl; omega
    · have : (0 : Word).toNat = 0 := rfl; omega
    · have : (0 : Word).toNat = 0 := rfl; omega
    · have : (0 : Word).toNat = 0 := rfl; omega
  refine ⟨⟨v1, v2, fun x hx hd ↦ nd x (Or.inr hd), fun x hx hd ↦ nd x (Or.inl hd),
    fun x _ hd ↦ nd x hd⟩, ?_, nd⟩
  simp only [Rv64Verifier.Layout.flushesOf, Rv64Verifier.Layout.formVecsOf, vecLen, h16, h40]
  rfl

/-- The `Flushes` at `sp + 1168` holds `F`, all it reaches allocated from `B` on. -/
structure FlAt (s u : MachineState) (F : LayoutMirror.FlushesRust) (B : Nat) : Prop where
  ok : Rv64Verifier.Layout.FlushesOk u (s.getReg .x2 - 1488)
  val : Rv64Verifier.Layout.flushesOf u (s.getReg .x2 - 1488) = F
  deep : ∀ x, Rv64Verifier.Layout.flushesDeep u (s.getReg .x2 - 1488) x → B ≤ x.toNat

/-! ## `Flushes::state_step` -/

theorem stk_sub {s u : MachineState} (hpre : WalkPre s) (h : Inv s u) {m : Nat} (hm : m ≤ 8736)
    (hm8 : m % 8 = 0) : RtStack u m :=
  hpre.stack.sub 2656 h.sp (by rw [stack_eq]; omega) (by decide) hm8 (by decide) (by decide)

/-- A callee's stack below `sp`, as `W6` sees it. -/
theorem stackLo_w6 {s u : MachineState} (hpre : WalkPre s) (h : Inv s u) {m : Nat}
    (hm : m ≤ 8736) {x : Word} (hx : Within x (stackLo u m) m) :
    Within x (s.getReg .x2 - 11392) 8736 := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  rw [stackLo_callee h m] at hx
  simp only [Within] at hx ⊢
  addr_omega [hx, hb1, hm]

/-- What a layout function's `GrowFlushes` frame writes, for the `Flushes` at `sp + 1168` holding
only buffers from `B` on. -/
theorem grow_w6 {s u t : MachineState} (hpre : WalkPre s) (h : Inv s u) {B m : Nat}
    (hm : m ≤ 8736) (hB : B ≤ heapNext u)
    (hd : ∀ x, Rv64Verifier.Layout.flushesBuf u (s.getReg .x2 - 1488) x → B ≤ x.toNat)
    (hok : Rv64Verifier.Layout.FlushesOk u (s.getReg .x2 - 1488)) (hmono : heapNext u ≤ heapNext t)
    {x : Word} (hx : Within x (s.getReg .x2 - 1488) 48 ∨
      Rv64Verifier.Layout.flushesBuf u (s.getReg .x2 - 1488) x ∨ Within x (stackLo u m) m ∨
      Within x nextAddr 8 ∨ Fresh u t x) : W6 s B t x := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  rcases hx with hx | hx | hx | hx | hx
  · exact Or.inl (by simp only [Within] at hx ⊢; addr_omega [hx, hb1])
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hd x hx, by
      have := (hok.buf_below hx).2; omega⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (stackLo_w6 hpre h hm hx))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hx))))
  · simp only [Fresh] at hx
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, hx.2⟩))))

/-- The registers past `state_step`. -/
structure Regs6 (s u : MachineState) : Prop where
  x9 : u.getReg .x9 = 0
  x26 : u.getReg .x26 = s.getReg .x2 - 512

set_option maxRecDepth 8192 in
/-- `state_step` on the empty `Flushes` at `sp + 1168`. -/
theorem r6stateStep (hSS : Rv64Verifier.Layout.StateStepSpec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState} {A : List E}
    {k : Nat} {Q : Word} (hpre : WalkPre s) (hpc : u.pc = 0x80004a90) (h : AtR5 OI s u A k Q) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = 0x8000186c ∧
      M6 OI s t A k (u.getReg .x18) Q (heapNext u) ∧ Regs6 s t ∧
      FlAt s t (({} : LayoutMirror.FlushesRust).stateStep 0 1) (heapNext u)) ∨ Dead Image.code t) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  have M := h.toM6
  have hab := hpre.stack.above
  have hx := hpre.stack.next
  rw [stackLo_eq] at hab
  rw [stackLo_eq, stack_eq] at hx
  simp only [heapEnd] at hab
  have x10 : u.getReg .x10 = s.getReg .x2 - 1488 := h.x10
  have a24 : s.getReg .x2 - 1488 + 24 = s.getReg .x2 - 1464 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  obtain ⟨f0, f8, f16, f24, f32, f40⟩ := h.flushes
  have e8 : s.getReg .x2 - 1488 + 8 = s.getReg .x2 - 1480 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have e16 : s.getReg .x2 - 1488 + 16 = s.getReg .x2 - 1472 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have e32 : s.getReg .x2 - 1488 + 24 + 8 = s.getReg .x2 - 1456 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have e40 : s.getReg .x2 - 1488 + 24 + 16 = s.getReg .x2 - 1448 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  obtain ⟨fok, fval, fnd⟩ := flushesOk_empty (u := u) (a := s.getReg .x2 - 1488) f0
    (by rw [e8]; exact f8) (by rw [e16]; exact f16) (by rw [a24]; exact f24) (by rw [e32]; exact f32)
    (by rw [e40]; exact f40)
  have hn : Rv64Verifier.Layout.stateStepStack ≤ 8736 := by decide
  have pre : Rv64Verifier.Layout.FlushesPre Rv64Verifier.Layout.stateStepStack u := {
    heap := h.inv.heap
    stack := stk_sub hpre h.inv hn (by decide)
    self := by rw [x10]; valid_sub hval [hb1]
    ok := by rw [x10]; exact fok
    selfFree := by rw [x10]; exact ⟨Or.inr (by addr_omega [hab, hb1]), by addr_omega [hx, hb1]⟩
    selfStack := by rw [x10, stackLo_callee h.inv]; addr_omega [hb1, hn]
    rodata := h.inv.rodata hpre }
  obtain ⟨t, hr, ⟨hpct, hp, ⟨g, gv⟩⟩ | hd⟩ := hSS u hpc pre
  swap
  · exact ⟨t, hr, Or.inr hd⟩
  rw [x10] at g gv
  have M' := M.step hpre (g.frame.mono fun x hx ↦ grow_w6 hpre h.inv hn (le_refl _)
    (fun y hy ↦ absurd (hy.imp Or.inl Or.inl) (fnd y)) fok g.mono hx) g.heap g.mono (hp.reg .x2)
  refine ⟨t, hr, Or.inl ⟨by rw [hpct, returnAddress_eq, h.x1]; decide, M',
    ⟨by rw [hp.reg .x9]; exact h.x9, by rw [hp.reg .x26]; exact h.x26⟩,
    ⟨g.ok, by rw [gv, fval], fun x hx ↦ ?_⟩⟩⟩
  rcases g.deep x hx with hd | hd | hd
  · exact absurd hd (fnd x)
  · exact hd.elim
  · exact hd.1

/-! ## The operands of `flushes_keccak`'s bytecode flush -/

/-- Building the operands: the `Flushes` at `sp + 1168` after `state_step` (all it reaches below
`P`), the `Vec<Form>` of capacity 12 and buffer `P` at `sp + 2504` (`s10 + 360`), its first `j` forms
`col(2 + i, 0)` at `P + 24 i` (their buffers past `P`'s 288 bytes), the heights' lengths at
`sp + 136` (6) and `sp + 152` (0); `s0 = 0`, `s1 = P`, `s10 = sp + 2144`. -/
structure Ops (OI : MachineState → Word → List (List Opening) → Prop) (s u : MachineState)
    (A : List E) (k : Nat) (R Q : Word) (B : Nat) (P : Word) (j : Nat) : Prop where
  m : M6 OI s u A k R Q B
  fl : FlAt s u (({} : LayoutMirror.FlushesRust).stateStep 0 1) B
  flP : ∀ x, Rv64Verifier.Layout.flushesDeep u (s.getReg .x2 - 1488) x → x.toNat < P.toNat
  buf : P.toNat % 8 = 0 ∧ B ≤ P.toNat ∧ P.toNat + 288 ≤ heapNext u
  vec : u.getMem (s.getReg .x2 - 152) = 12 ∧ u.getMem (s.getReg .x2 - 144) = P
  lens : u.getMem (s.getReg .x2 - 2520) = 6 ∧ u.getMem (s.getReg .x2 - 2504) = 0
  forms : ∀ i < j, Rv64Verifier.Layout.FormOk u (P + BitVec.ofNat 64 (24 * i)) ∧
    Rv64Verifier.Layout.formOf u (P + BitVec.ofNat 64 (24 * i)) = LayoutMirror.colRust (i + 2) 0 ∧
    ∀ x, Rv64Verifier.Layout.formBuf u (P + BitVec.ofNat 64 (24 * i)) x → P.toNat + 288 ≤ x.toNat
  x8 : j ≤ 11 → u.getReg .x8 = 0
  x9 : u.getReg .x9 = P
  x26 : u.getReg .x26 = s.getReg .x2 - 512
  x18 : 11 ≤ j → u.getReg .x18 = 13
  x19 : 8 ≤ j → u.getReg .x19 = 10
  x21 : 9 ≤ j → u.getReg .x21 = 11

theorem Ops.hb {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {P : Word} {j : Nat} (h : Ops OI s u A k R Q B P j) :
    P.toNat + 288 ≤ 0x78000000 := by
  have := h.m.inv.heap.hi; have := h.buf; simp only [heapEnd] at *; omega

/-- A form copied from `sp + 1728` to `P + 24 j`. -/
theorem Ops.copy {OI : MachineState → Word → List (List Opening) → Prop} {s u v : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {P : Word} {j : Nat} (hpre : WalkPre s)
    (h : Ops OI s u A k R Q B P j) (hj : j < 12)
    (hf : Rv64Verifier.Layout.FormOk u (s.getReg .x2 - 928))
    (hv : Rv64Verifier.Layout.formOf u (s.getReg .x2 - 928) = LayoutMirror.colRust (j + 2) 0)
    (hb : ∀ x, Rv64Verifier.Layout.formBuf u (s.getReg .x2 - 928) x → P.toNat + 288 ≤ x.toNat)
    (fr : Rv64Verifier.Layout.DFrame u v fun x ↦ Within x (P + BitVec.ofNat 64 (24 * j)) 24 ∨
      Within x (s.getReg .x2 - 136) 8)
    (m0 : v.getMem (P + BitVec.ofNat 64 (24 * j)) = u.getMem (s.getReg .x2 - 928))
    (m8 : v.getMem (P + BitVec.ofNat 64 (24 * j) + 8) = u.getMem (s.getReg .x2 - 928 + 8))
    (m16 : v.getMem (P + BitVec.ofNat 64 (24 * j) + 16) = u.getMem (s.getReg .x2 - 928 + 16))
    (sp : v.getReg .x2 = u.getReg .x2) (x8 : j + 1 ≤ 11 → v.getReg .x8 = u.getReg .x8)
    (x9 : v.getReg .x9 = u.getReg .x9) (x26 : v.getReg .x26 = u.getReg .x26)
    (x18 : 11 ≤ j + 1 → v.getReg .x18 = 13) (x19 : 8 ≤ j + 1 → v.getReg .x19 = 10)
    (x21 : 9 ≤ j + 1 → v.getReg .x21 = 11) :
    Ops OI s v A k R Q B P (j + 1) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  obtain ⟨p1, p2, p3⟩ := h.buf
  have hP := h.hb
  have fd := fr
  have keep (x : Word) (hx : x.toNat + 8 ≤ P.toNat + 24 * j ∨ P.toNat + 24 * j + 24 ≤ x.toNat)
      (hs : x.toNat + 8 ≤ (s.getReg .x2 - 136).toNat ∨ (s.getReg .x2 - 128).toNat ≤ x.toNat)
      (hx' : x.toNat + 8 ≤ 2 ^ 64) : v.getMem x = u.getMem x :=
    fd x (fun y hy hw ↦ by
      simp only [Within] at hy hw; rcases hw with hw | hw <;> addr_omega [hy, hw, hx, hs, hj, hP, hb1]) hx'
  have hn : heapNext v = heapNext u := by
    simp only [heapNext]; rw [keep _ (by addr_omega [hj, hP]) (by addr_omega [hb1]) (by decide)]
  have hheap : HeapOk u := h.m.inv.heap
  have M := h.m.step hpre (fd.mono fun x hx ↦ by
      rcases hx with hx | hx
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by
          simp only [Within] at hx; addr_omega [hx, hj, p2, hP], by
          simp only [Within] at hx; rw [hn]; addr_omega [hx, hj, p3]⟩))))
      · exact Or.inl (by simp only [Within] at hx ⊢; addr_omega [hx, hb1]))
    ⟨hn ▸ hheap.lo, hn ▸ hheap.hi⟩ hn.ge sp
  have F := Rv64Verifier.Layout.flushesOf_frame fd h.fl.ok
    (fun x hx hw ↦ by
      simp only [Within] at hx hw; rcases hw with hw | hw <;> addr_omega [hx, hw, hb1, hj, hP])
    (fun x hx hw ↦ by
      have t1 := h.flP x hx; have t2 := (h.fl.ok.deep_below hx).2; have hh := h.m.inv.heap.hi
      simp only [Within, heapEnd] at hw hh; rcases hw with hw | hw <;> addr_omega [hw, t1, t2, hj, hP, hb1, hh])
    (by addr_omega [hb1]) hheap hn.ge
  refine {
    m := M
    fl := ⟨F.2.1, by rw [F.1]; exact h.fl.val, fun x hx ↦ h.fl.deep x (by rw [← F.2.2.1]; exact hx)⟩
    flP := fun x hx ↦ h.flP x (by rw [← F.2.2.1]; exact hx)
    buf := ⟨p1, p2, by rw [hn]; exact p3⟩
    vec := by
      rw [keep _ (by addr_omega [hb1, hP, hj]) (by addr_omega [hb1]) (by addr_omega [hb1]),
        keep _ (by addr_omega [hb1, hP, hj]) (by addr_omega [hb1]) (by addr_omega [hb1])]
      exact h.vec
    lens := by
      rw [keep _ (by addr_omega [hb1, hP, hj]) (by addr_omega [hb1]) (by addr_omega [hb1]),
        keep _ (by addr_omega [hb1, hP, hj]) (by addr_omega [hb1]) (by addr_omega [hb1])]
      exact h.lens
    forms := fun i hi ↦ ?_
    x8 := fun hj' ↦ by rw [x8 hj']; exact h.x8 (by omega)
    x9 := by rw [x9]; exact h.x9
    x26 := by rw [x26]; exact h.x26
    x18 := x18
    x19 := x19
    x21 := x21 }
  by_cases hij : i < j
  · obtain ⟨o1, o2, o3⟩ := h.forms i hij
    have ha : ∀ x, Within x (P + BitVec.ofNat 64 (24 * i)) 24 →
        ¬ (Within x (P + BitVec.ofNat 64 (24 * j)) 24 ∨ Within x (s.getReg .x2 - 136) 8) :=
      fun x hx hw ↦ by
        simp only [Within] at hx hw; rcases hw with hw | hw <;> addr_omega [hx, hw, hij, hj, hP, hb1]
    have hbw : ∀ x, Rv64Verifier.Layout.formBuf u (P + BitVec.ofNat 64 (24 * i)) x →
        ¬ (Within x (P + BitVec.ofNat 64 (24 * j)) 24 ∨ Within x (s.getReg .x2 - 136) 8) :=
      fun x hx hw ↦ by
        have t1 := o3 x hx; have t2 := (o1.buf_below hx).2; have hh := h.m.inv.heap.hi
        simp only [Within, heapEnd] at hw hh; rcases hw with hw | hw <;> addr_omega [hw, t1, t2, hj, hP, hb1, hh]
    have G := Rv64Verifier.Layout.formOf_frame fd o1 ha hbw (by addr_omega [hi, hj, hP]) hheap hn.ge
    have Hb := Rv64Verifier.Layout.formBuf_frame fd ha (by addr_omega [hi, hj, hP])
    exact ⟨G.2, by rw [G.1]; exact o2, fun x hx ↦ o3 x (by rw [← Hb]; exact hx)⟩
  · have e : i = j := by omega
    subst e
    have G := Rv64Verifier.Layout.formOf_move fd hf m0 m8 m16
      (fun x hx hw ↦ by
        have t1 := hb x hx; have t2 := (hf.buf_below hx).2; have hh := h.m.inv.heap.hi
        simp only [Within, heapEnd] at hw hh; rcases hw with hw | hw <;> addr_omega [hw, t1, t2, hj, hP, hb1, hh])
      hheap hn.ge
    exact ⟨G.2.1, by rw [G.1]; exact hv, fun x hx ↦ hb x (by rw [← G.2.2]; exact hx)⟩

theorem new_w6 {s u t : MachineState} (hpre : WalkPre s) (h : Inv s u) {B m : Nat} {o : Word}
    (hm : m ≤ 8736) (hB : B ≤ heapNext u)
    (ho : (s.getReg .x2 - 2080).toNat ≤ o.toNat ∧ o.toNat + 24 ≤ (s.getReg .x2 - 104).toNat)
    {x : Word} (hx : Within x o 24 ∨ Within x (stackLo u m) m ∨ Within x nextAddr 8 ∨ Fresh u t x) :
    W6 s B t x := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  rcases hx with hx | hx | hx | hx
  · exact Or.inl (by simp only [Within] at hx ⊢; addr_omega [hx, ho, hb1])
  · exact Or.inr (Or.inr (Or.inr (Or.inl (stackLo_w6 hpre h hm hx))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hx))))
  · simp only [Fresh] at hx
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, hx.2⟩))))

set_option maxRecDepth 8192 in
/-- `col(j + 2, 0)` into `sp + 1728`. -/
theorem Ops.col (hC : Rv64Verifier.Layout.ColSpec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {P : Word} {j : Nat} (hpre : WalkPre s)
    (h : Ops OI s u A k R Q B P j) (hpc : u.pc = 0x80004b34)
    (x10 : u.getReg .x10 = s.getReg .x2 - 928) (x11 : u.getReg .x11 = BitVec.ofNat 64 (j + 2))
    (x12 : u.getReg .x12 = 0) (hj : j < 12) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = returnAddress u ∧ Ops OI s t A k R Q B P j ∧
      Rv64Verifier.Layout.FormOk t (s.getReg .x2 - 928) ∧
      Rv64Verifier.Layout.formOf t (s.getReg .x2 - 928) = LayoutMirror.colRust (j + 2) 0 ∧
      (∀ x, Rv64Verifier.Layout.formBuf t (s.getReg .x2 - 928) x → P.toNat + 288 ≤ x.toNat)) ∨
      Dead Image.code t) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  have hab := hpre.stack.above
  have hx := hpre.stack.next
  rw [stackLo_eq] at hab
  rw [stackLo_eq, stack_eq] at hx
  simp only [heapEnd] at hab
  obtain ⟨p1, p2, p3⟩ := h.buf
  have hP := h.hb
  have hheap : HeapOk u := h.m.inv.heap
  have hhu := hheap.hi
  simp only [heapEnd] at hhu
  have hn : Rv64Verifier.Layout.colStack ≤ 8736 := by decide
  have pre : Rv64Verifier.Layout.ColPre u := {
    heap := hheap
    stack := stk_sub hpre h.m.inv hn (by decide)
    out := by rw [x10]; valid_sub hval [hb1]
    outFree := by rw [x10]; exact ⟨Or.inr (by addr_omega [hab, hb1]), by addr_omega [hx, hb1]⟩
    outStack := by rw [x10, stackLo_callee h.m.inv]; addr_omega [hb1, hn]
    rodata := h.m.inv.rodata hpre }
  obtain ⟨t, hr, ⟨hpct, hp, ⟨nf, fv⟩⟩ | hd⟩ := hC u hpc pre
  swap
  · exact ⟨t, hr, Or.inr hd⟩
  rw [x10] at nf fv
  rw [x11, x12] at fv
  have fr := nf.frame
  have hw : ∀ x, (Within x (s.getReg .x2 - 928) 24 ∨
      Within x (stackLo u Rv64Verifier.Layout.colStack) Rv64Verifier.Layout.colStack ∨
      Within x nextAddr 8 ∨ Fresh u t x) → x.toNat < heapNext u → ¬ (x.toNat < 0x20 ∨ 0x20 ≤ x.toNat) ∨
        heapNext u ≤ x.toNat ∨ 0x78000000 ≤ x.toNat := fun x hx hl ↦ by
    rcases hx with hx | hx | hx | hx
    · right; right; simp only [Within] at hx; addr_omega [hx, hb1]
    · right; right; rw [stackLo_callee h.m.inv] at hx; simp only [Within] at hx; addr_omega [hx, hb1, hn]
    · right; right; simp only [Within] at hx; addr_omega [hx]
    · right; left; simp only [Fresh] at hx; exact hx.1
  have miss (x : Word) (hl : x.toNat < heapNext u) : ¬ (Within x (s.getReg .x2 - 928) 24 ∨
      Within x (stackLo u Rv64Verifier.Layout.colStack) Rv64Verifier.Layout.colStack ∨
      Within x nextAddr 8 ∨ Fresh u t x) := fun hx ↦ by
    rcases hw x hx hl with h0 | h0 | h0
    · exact h0 (by omega)
    · omega
    · omega
  have F := Rv64Verifier.Layout.flushesOf_frame fr h.fl.ok
    (fun x hx hw ↦ by
      rcases hw with hw | hw | hw | hw
      · simp only [Within] at hx hw; addr_omega [hx, hw, hb1]
      · rw [stackLo_callee h.m.inv] at hw; simp only [Within] at hx hw; addr_omega [hx, hw, hb1, hn]
      · simp only [Within] at hx hw; addr_omega [hx, hw, hb1]
      · simp only [Fresh] at hw; simp only [Within] at hx; have := nf.heap.hi
        simp only [heapEnd] at this; addr_omega [hx, hw, hb1, this])
    (fun x hx ↦ miss x (by have := h.flP x hx; omega)) (by addr_omega [hb1]) hheap nf.mono
  have keep (y : Word) (hy : (s.getReg .x2 - 904).toNat ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2 - 104).toNat ∨
      (s.getReg .x2 - 2656).toNat ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2 - 928).toNat) :
      t.getMem y = u.getMem y :=
    fr y (fun x hx hw ↦ by
      rcases hw with hw | hw | hw | hw
      · simp only [Within] at hx hw; addr_omega [hx, hw, hy, hb1]
      · rw [stackLo_callee h.m.inv] at hw; simp only [Within] at hx hw; addr_omega [hx, hw, hy, hb1, hn]
      · simp only [Within] at hx hw; addr_omega [hx, hw, hy, hb1]
      · simp only [Fresh] at hw; simp only [Within] at hx; have := nf.heap.hi; simp only [heapEnd] at this
        addr_omega [hx, hw, hy, hb1, this]) (by addr_omega [hy, hb1])
  refine ⟨t, hr, Or.inl ⟨hpct, {
    m := h.m.step hpre (fr.mono fun x hx ↦ new_w6 hpre h.m.inv hn h.m.bufQ.2.2.2
      (by addr_omega [hb1]) hx) nf.heap nf.mono (hp.reg .x2)
    fl := ⟨F.2.1, by rw [F.1]; exact h.fl.val, fun x hx ↦ h.fl.deep x (by rw [← F.2.2.1]; exact hx)⟩
    flP := fun x hx ↦ h.flP x (by rw [← F.2.2.1]; exact hx)
    buf := ⟨p1, p2, by have := nf.mono; omega⟩
    vec := by
      rw [keep _ (Or.inl (by addr_omega [hb1])), keep _ (Or.inl (by addr_omega [hb1]))]
      exact h.vec
    lens := by
      rw [keep _ (Or.inr (by addr_omega [hb1])), keep _ (Or.inr (by addr_omega [hb1]))]
      exact h.lens
    forms := fun i hi ↦ by
      obtain ⟨o1, o2, o3⟩ := h.forms i hi
      have G := Rv64Verifier.Layout.formOf_frame (a := P + BitVec.ofNat 64 (24 * i)) fr o1
        (fun x hx ↦ miss x (by simp only [Within] at hx; addr_omega [hx, hi, hj, hP, p3]))
        (fun x hx ↦ miss x (o1.buf_below hx).2) (by addr_omega [hi, hj, hP]) hheap nf.mono
      have Hb := Rv64Verifier.Layout.formBuf_frame (e := P + BitVec.ofNat 64 (24 * i)) fr
        (fun x hx ↦ miss x (by simp only [Within] at hx; addr_omega [hx, hi, hj, hP, p3]))
        (by addr_omega [hi, hj, hP])
      exact ⟨G.2, by rw [G.1]; exact o2, fun x hx ↦ o3 x (by rw [← Hb]; exact hx)⟩
    x8 := fun hj' ↦ by rw [hp.reg .x8]; exact h.x8 hj'
    x9 := by rw [hp.reg .x9]; exact h.x9
    x26 := by rw [hp.reg .x26]; exact h.x26
    x18 := fun hj ↦ by rw [hp.reg .x18]; exact h.x18 hj
    x19 := fun hj ↦ by rw [hp.reg .x19]; exact h.x19 hj
    x21 := fun hj ↦ by rw [hp.reg .x21]; exact h.x21 hj }, nf.ok, ?_, fun x hx ↦ ?_⟩⟩
  · rw [fv]; congr 1
    · simp only [BitVec.toNat_ofNat]; omega
  · have nb := nf.fresh
    simp only [NewBuf, Rv64Verifier.Layout.formBuf, Within] at nb hx
    rcases nb.2 with h0 | h0 <;> omega

theorem Expect.ldframe {x : Sym.Expect} {s t : MachineState} (h : x.Holds s t) {w : Word → Prop}
    (hw : ∀ k ∈ x.writes, w (k.eval s)) : Rv64Verifier.Layout.DFrame s t w :=
  dframe_l (Expect.dframe h hw)

/-- `FlAt` across a step that writes nothing it reaches nor its header. -/
theorem FlAt.frame {s u v : MachineState} {F : LayoutMirror.FlushesRust} {B : Nat} {w : Word → Prop}
    (hpre : WalkPre s) (h : FlAt s u F B) (fr : Rv64Verifier.Layout.DFrame u v w)
    (hh : ∀ x, Within x (s.getReg .x2 - 1488) 48 → ¬ w x)
    (hd : ∀ x, Rv64Verifier.Layout.flushesDeep u (s.getReg .x2 - 1488) x → ¬ w x)
    (hheap : HeapOk u) (hmono : heapNext u ≤ heapNext v) :
    FlAt s v F B ∧ Rv64Verifier.Layout.flushesDeep v (s.getReg .x2 - 1488) =
      Rv64Verifier.Layout.flushesDeep u (s.getReg .x2 - 1488) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have G := Rv64Verifier.Layout.flushesOf_frame fr h.ok hh hd (by addr_omega [hb1]) hheap hmono
  exact ⟨⟨G.2.1, by rw [G.1]; exact h.val, fun x hx ↦ h.deep x (by rw [← G.2.2.1]; exact hx)⟩, G.2.2.1⟩

set_option maxRecDepth 8192 in
/-- `alloc(8, 288)` for the operands, the `Vec` {12, `P`, 0} at `sp + 2504`, the heights' lengths
at `sp + 136`, `sp + 152`, `reserve(12)` (room enough), then the call `col(2, 0)`. -/
theorem r6alloc (hAS : AllocSpec) (hRF : ReserveFastSpec 0x80004aec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState} {A : List E}
    {k : Nat} {R Q : Word} {B : Nat} (hpre : WalkPre s) (hpc : u.pc = 0x8000186c)
    (h : M6 OI s u A k R Q B) (hr : Regs6 s u)
    (hf : FlAt s u (({} : LayoutMirror.FlushesRust).stateStep 0 1) B) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = 0x80004b34 ∧ ∃ P, Ops OI s t A k R Q B P 0 ∧
      t.getReg .x10 = s.getReg .x2 - 928 ∧ t.getReg .x11 = BitVec.ofNat 64 (0 + 2) ∧
      t.getReg .x12 = 0 ∧ t.getReg .x1 = 0x800018d0) ∨ Dead Image.code t) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  have hheap := h.inv.heap
  have hhu := hheap.hi
  have hlo := hheap.lo
  simp only [heapEnd, heapStart] at hhu hlo
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000186c_spec hpc (by rv_eval [])
  have m₁ := b8000186c_mem_same h₁
  have hn₁ : heapNext u₁ = heapNext u := by simp only [heapNext, m₁]
  have M₁ := h.step hpre (Rv64Verifier.Layout.DFrame.of_same m₁ _) ⟨hn₁ ▸ hheap.lo, hn₁ ▸ hheap.hi⟩
    hn₁.ge (b8000186c_keeps h₁ .x2 (by decide))
  have F₁ := hf.frame hpre (Rv64Verifier.Layout.DFrame.of_same m₁ (fun _ ↦ False)) (fun _ _ h ↦ h)
    (fun _ _ h ↦ h) hheap hn₁.ge
  have pre₁ : AllocPre u₁ := ⟨M₁.inv.heap, by rw [b8000186c_x10 h₁]; decide⟩
  obtain ⟨u₂, hr₂, ⟨hpc₂, hp₂, post₂⟩ | hd⟩ := hAS.call (Reaches.refl u₁) (b8000186c_pc h₁) pre₁
  swap
  · exact ⟨u₂, hr₁.trans hr₂, Or.inr hd⟩
  have hal := post₂.aligned
  have hab := post₂.above
  have hnx := post₂.next
  rw [b8000186c_x10 h₁] at hal
  rw [b8000186c_x11 h₁] at hnx
  have e8 : (8 : Word).toNat = 8 := rfl
  have e288 : (288 : Word).toNat = 288 := rfl
  rw [e8] at hal
  rw [e288] at hnx
  rw [hn₁] at hab
  set P := u₂.getReg .x10 with hP
  have fr₂' : Rv64Verifier.Layout.DFrame u₁ u₂ (Within · nextAddr 8) := fun a ha _ ↦
    post₂.mem a fun he ↦ ha a (by simp only [Within]; omega) (by rw [he]; simp only [Within]; omega)
  have fr₂ : Rv64Verifier.Layout.DFrame u₁ u₂ (W6 s B u₂) :=
    fr₂'.mono fun x hx ↦ Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hx))))
  have hBP : B ≤ P.toNat := by have := h.bufQ.2.2.2; omega
  have M₂ := M₁.step hpre fr₂ post₂.heap (by rw [hnx, hn₁]; omega) (hp₂.reg .x2)
  have flP : ∀ x, Rv64Verifier.Layout.flushesDeep u₁ (s.getReg .x2 - 1488) x → x.toNat < P.toNat :=
    fun x hx ↦ by have := (F₁.1.ok.deep_below hx).2; rw [hn₁] at this; omega
  have F₂ := F₁.1.frame hpre fr₂'
    (fun x hx hw ↦ by simp only [Within] at hx hw; addr_omega [hx, hw, hb1])
    (fun x hx hw ↦ by
      have := (F₁.1.ok.deep_below hx).2
      simp only [Within] at hw; rw [hn₁] at this; addr_omega [hw, this, hhu])
    M₁.inv.heap (by rw [hnx, hn₁]; omega)
  obtain ⟨u₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000187c_spec
    (by rw [hpc₂, returnAddress_eq, b8000186c_x1 h₁]; decide) (by rv_eval [])
  have hP0 : u₂.getReg .x10 ≠ 0 := fun he ↦ by
    have := congrArg BitVec.toNat he; rw [← hP] at this
    have h0 : (0 : Word).toNat = 0 := rfl
    omega
  have m₃ := b8000187c_mem_same h₃
  have k₃ := b8000187c_keeps h₃
  have hn₃ : heapNext u₃ = heapNext u₂ := by simp only [heapNext, m₃]
  have M₃ := M₂.step hpre (Rv64Verifier.Layout.DFrame.of_same m₃ _) ⟨hn₃ ▸ post₂.heap.lo,
    hn₃ ▸ post₂.heap.hi⟩ hn₃.ge (k₃ .x2 (by decide))
  have F₃ := F₂.1.frame hpre (Rv64Verifier.Layout.DFrame.of_same m₃ (fun _ ↦ False)) (fun _ _ h ↦ h)
    (fun _ _ h ↦ h) post₂.heap hn₃.ge
  have sp₃ : u₃.getReg .x2 = s.getReg .x2 - 2656 := M₃.inv.sp
  have x26₃ : u₃.getReg .x26 = s.getReg .x2 - 512 := by
    rw [k₃ .x26 (by decide), hp₂.reg .x26, b8000186c_keeps h₁ .x26 (by decide)]; exact hr.x26
  have x9₃ : u₃.getReg .x9 = 0 := by
    rw [k₃ .x9 (by decide), hp₂.reg .x9, b8000186c_keeps h₁ .x9 (by decide)]; exact hr.x9
  have x10₃ : u₃.getReg .x10 = P := k₃ .x10 (by decide)
  obtain ⟨u₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b80001884_spec (b8000187c_pc_taken h₃ hP0) (by
    rv_eval [sp₃, x26₃]
    and_intros
    all_goals first
      | valid_access hval [hb1]
      | addr_omega [hb1])
  have e (N M : Word) (hNM : N.toNat + M.toNat = 2656) : u₃.getReg .x2 + N = s.getReg .x2 - M :=
    spAdd hpre sp₃ hNM
  have e' (N M : Word) (hNM : N.toNat + M.toNat = 512) : u₃.getReg .x26 + N = s.getReg .x2 - M := by
    rw [x26₃]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1, hNM]
  have fr₄' : Rv64Verifier.Layout.DFrame u₃ u₄ fun x ↦ Within x (s.getReg .x2 - 152) 24 ∨
      Within x (s.getReg .x2 - 2520) 8 ∨ Within x (s.getReg .x2 - 2504) 8 :=
    Expect.ldframe h₄ (by
      rv_eval [sp₃, x26₃]
      simp only [Within]
      and_intros <;> addr_omega [hb1])
  have k₄ := b80001884_keeps h₄
  have fr₄ : Rv64Verifier.Layout.DFrame u₃ u₄ (W6 s B u₄) := fr₄'.mono fun x hx ↦ by
    rcases hx with hx | hx | hx
    · exact Or.inl (by simp only [Within] at hx ⊢; addr_omega [hx, hb1])
    · exact Or.inr (Or.inl hx)
    · exact Or.inr (Or.inr (Or.inl (Or.inl hx)))
  have keep₄ (y : Word) (hy : y.toNat + 8 ≤ (s.getReg .x2 - 2520).toNat ∨
      (s.getReg .x2 - 2512).toNat ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2 - 2504).toNat ∨
      (s.getReg .x2 - 2496).toNat ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2 - 152).toNat) :
      u₄.getMem y = u₃.getMem y :=
    fr₄' y (fun x hx hw ↦ by
      simp only [Within] at hx hw; rcases hw with hw | hw | hw <;> addr_omega [hx, hw, hy, hb1])
      (by addr_omega [hy, hb1])
  have hn₄ : heapNext u₄ = heapNext u₃ := by
    simp only [heapNext]; rw [keep₄ _ (by addr_omega [hb1])]
  have M₄ := M₃.step hpre fr₄ ⟨hn₄ ▸ M₃.inv.heap.lo, hn₄ ▸ M₃.inv.heap.hi⟩ hn₄.ge (k₄ .x2 (by decide))
  have hhu₂ := post₂.heap.hi
  simp only [heapEnd] at hhu₂
  have F₄ := F₃.1.frame hpre fr₄'
    (fun x hx hw ↦ by simp only [Within] at hx hw; rcases hw with hw | hw | hw <;> addr_omega [hx, hw, hb1])
    (fun x hx hw ↦ by
      have := (F₃.1.ok.deep_below hx).2
      simp only [Within] at hw; rw [hn₃] at this
      rcases hw with hw | hw | hw <;> addr_omega [hw, this, hb1, hhu₂])
    M₃.inv.heap hn₄.ge
  have v0 : u₄.getMem (s.getReg .x2 - 152) = 12 := by rw [← e' 360 152 (by decide)]; exact b80001884_m_x26_360 h₄
  have v1 : u₄.getMem (s.getReg .x2 - 144) = P := by
    rw [← e' 368 144 (by decide), b80001884_m_x26_368 h₄, x10₃]
  have v2 : u₄.getMem (s.getReg .x2 - 136) = 0 := by rw [← e' 376 136 (by decide)]; exact b80001884_m_x26_376 h₄
  have l0 : u₄.getMem (s.getReg .x2 - 2520) = 6 := by
    rw [← e 136 2520 (by decide), b80001884_m_x2_136 h₄, x9₃]; rfl
  have l1 : u₄.getMem (s.getReg .x2 - 2504) = 0 := by
    rw [← e 152 2504 (by decide), b80001884_m_x2_152 h₄, x9₃]
  have x10₄ : u₄.getReg .x10 = s.getReg .x2 - 152 := by rw [b80001884_x10 h₄, e 2504 152 (by decide)]
  have pre₄ : ValidMemRange (u₄.getReg .x10) 3 ∧ (vecLen u₄ (u₄.getReg .x10)).toNat +
      (u₄.getReg .x11).toNat ≤ (vecCap u₄ (u₄.getReg .x10)).toNat := by
    have e16 : s.getReg .x2 - 152 + 16 = s.getReg .x2 - 136 := by
      apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
    refine ⟨by rw [x10₄]; valid_sub hval [hb1], ?_⟩
    simp only [vecLen, vecCap, x10₄, e16, v0, v2, b80001884_x11 h₄]
    decide
  obtain ⟨u₅, hr₅, ⟨hpc₅, hp₅, post₅⟩ | hd⟩ := hRF.call (Reaches.refl u₄) (b80001884_pc h₄) pre₄
  swap
  · exact ⟨u₅, hr₁.trans (hr₂.trans (hr₃.trans (hr₄.trans hr₅))), Or.inr hd⟩
  have m₅ := post₅.2
  have hn₅ : heapNext u₅ = heapNext u₄ := by simp only [heapNext, m₅]
  obtain ⟨u₆, hr₆, h₆⟩ := Sym.BlockSpec.reaches b800018b4_spec
    (by rw [hpc₅, returnAddress_eq, b80001884_x1 h₄]; decide) (by
      rv_eval [hp₅.reg .x26, k₄ .x26 (by decide), x26₃]
      and_intros <;> valid_access hval [hb1])
  have m₆ := b800018b4_mem_same h₆
  have hn₆ : heapNext u₆ = heapNext u₅ := by simp only [heapNext, m₆]
  have mm (y : Word) : u₆.getMem y = u₄.getMem y := (m₆ y).trans (m₅ y)
  have hn₆₄ : heapNext u₆ = heapNext u₄ := hn₆.trans hn₅
  have x26₅ : u₅.getReg .x26 = s.getReg .x2 - 512 := by
    rw [hp₅.reg .x26, k₄ .x26 (by decide), x26₃]
  have sp₆ : u₆.getReg .x2 = u₄.getReg .x2 := by
    rw [b800018b4_keeps h₆ .x2 (by decide), hp₅.reg .x2]
  have F₆ := F₄.1.frame hpre (Rv64Verifier.Layout.DFrame.of_same mm (fun _ ↦ False)) (fun _ _ h ↦ h)
    (fun _ _ h ↦ h) M₄.inv.heap hn₆₄.ge
  have hd₆ : Rv64Verifier.Layout.flushesDeep u₆ (s.getReg .x2 - 1488) =
      Rv64Verifier.Layout.flushesDeep u₁ (s.getReg .x2 - 1488) := by
    rw [F₆.2, F₄.2, F₃.2, F₂.2]
  refine ⟨u₆, hr₁.trans (hr₂.trans (hr₃.trans (hr₄.trans (hr₅.trans hr₆)))), Or.inl ⟨b800018b4_pc h₆, P, {
    m := M₄.step hpre (Rv64Verifier.Layout.DFrame.of_same mm _) ⟨hn₆₄ ▸ M₄.inv.heap.lo,
      hn₆₄ ▸ M₄.inv.heap.hi⟩ hn₆₄.ge sp₆
    fl := F₆.1
    flP := fun x hx ↦ flP x (by rw [← hd₆]; exact hx)
    buf := ⟨hal, hBP, by rw [hn₆₄, hn₄, hn₃, hnx]⟩
    vec := ⟨by rw [mm]; exact v0, by rw [mm]; exact v1⟩
    lens := ⟨by rw [mm]; exact l0, by rw [mm]; exact l1⟩
    forms := fun i hi ↦ absurd hi (Nat.not_lt_zero _)
    x8 := fun _ ↦ by
      rw [b800018b4_x8 h₆, x26₅, show s.getReg .x2 - 512 + 376 = s.getReg .x2 - 136 by
        apply BitVec.eq_of_toNat_eq; addr_omega [hb1], m₅]; exact v2
    x9 := by
      rw [b800018b4_x9 h₆, x26₅, show s.getReg .x2 - 512 + 368 = s.getReg .x2 - 144 by
        apply BitVec.eq_of_toNat_eq; addr_omega [hb1], m₅]; exact v1
    x26 := by rw [b800018b4_keeps h₆ .x26 (by decide)]; exact x26₅
    x18 := fun h ↦ absurd h (by decide)
    x19 := fun h ↦ absurd h (by decide)
    x21 := fun h ↦ absurd h (by decide) },
    by rw [b800018b4_x10 h₆, hp₅.reg .x2, k₄ .x2 (by decide)]; exact e 1728 928 (by decide),
    b800018b4_x11 h₆, b800018b4_x12 h₆, b800018b4_x1 h₆⟩⟩

set_option maxRecDepth 8192 in
/-- `col(2, 0)`, copied to `P + 0`. -/
theorem op0 (hC : Rv64Verifier.Layout.ColSpec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {P : Word} (hpre : WalkPre s)
    (h : Ops OI s u A k R Q B P 0) (hpc : u.pc = 0x80004b34)
    (x10 : u.getReg .x10 = s.getReg .x2 - 928) (x11 : u.getReg .x11 = BitVec.ofNat 64 (0 + 2))
    (x12 : u.getReg .x12 = 0) (x1 : u.getReg .x1 = 0x800018d0) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = 0x80004b34 ∧ Ops OI s t A k R Q B P 1 ∧
      t.getReg .x10 = s.getReg .x2 - 928 ∧ t.getReg .x11 = BitVec.ofNat 64 (1 + 2) ∧
      t.getReg .x12 = 0 ∧ t.getReg .x1 = 0x8000190c) ∨ Dead Image.code t) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  obtain ⟨t, hr, ⟨hpct, H, fo, fv, fb⟩ | hd⟩ := h.col hC hpre hpc x10 x11 x12 (by decide)
  swap
  · exact ⟨t, hr, Or.inr hd⟩
  have sp : t.getReg .x2 = s.getReg .x2 - 2656 := H.m.inv.sp
  have x9 := H.x9
  have x8 := H.x8 (by decide)
  have hP := H.hb
  obtain ⟨p1, p2, p3⟩ := H.buf
  have hmP : Mapped P 288 := Or.inl ⟨by
    have := hpre.heap.lo; have := H.m.bufQ; simp only [heapStart] at *; omega, hP⟩
  obtain ⟨v, hr', hv⟩ := Sym.BlockSpec.reaches b800018d0_spec
    (by rw [hpct, returnAddress_eq, x1]; decide) (by
      rv_eval [sp, x9, x8]
      and_intros
      all_goals first
        | valid_access hval [hb1]
        | exact Mapped.valid8 hmP (by addr_omega [hP]) (by addr_omega [hP]) (by addr_omega [hP, p1])
        | addr_omega [hb1, hP])
  have ea : t.getReg .x9 + (t.getReg .x8 * 16 + t.getReg .x8 * 8) = P + BitVec.ofNat 64 (24 * 0) := by rw [x9, x8]; simp
  have k := b800018d0_keeps hv
  have e (N M : Word) (hNM : N.toNat + M.toNat = 2656) : t.getReg .x2 + N = s.getReg .x2 - M :=
    spAdd hpre sp hNM
  have H' := H.copy hpre (by decide) fo fv fb ((MemFrame.dframe (Sym.Expect.Holds.memFrame hv (lo := P + BitVec.ofNat 64 (24 * 0)) (by rv_eval [x9, x8]; simp only [Within]; and_intros <;> addr_omega [hP]))).mono fun _ h ↦ Or.inl h)
    (by rw [← ea, b800018d0_m0 hv, e 1728 928 (by decide)])
    (by rw [show P + BitVec.ofNat 64 (24 * 0) + 8 = (t.getReg .x9 + (t.getReg .x8 * 16 + t.getReg .x8 * 8)) + 8 from (by rw [← ea]), b800018d0_m1 hv,
      show s.getReg .x2 - 928 + 8 = t.getReg .x2 + 1736 by
        rw [sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]])
    (by rw [show P + BitVec.ofNat 64 (24 * 0) + 16 = (t.getReg .x9 + (t.getReg .x8 * 16 + t.getReg .x8 * 8)) + 16 from (by rw [← ea]), b800018d0_m2 hv,
      show s.getReg .x2 - 928 + 16 = t.getReg .x2 + 1744 by
        rw [sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]])
    (k .x2 (by decide)) (fun _ ↦ k .x8 (by decide)) (by rw [b800018d0_x9 hv, x8]; simp)
    (k .x26 (by decide)) (fun h ↦ absurd h (by decide)) (fun h ↦ absurd h (by decide)) (fun h ↦ absurd h (by decide))
  exact ⟨v, hr.trans hr', Or.inl ⟨b800018d0_pc hv, H', by rw [b800018d0_x10 hv, e 1728 928 (by decide)],
    by rw [b800018d0_x11 hv]; rfl, b800018d0_x12 hv, b800018d0_x1 hv⟩⟩

set_option maxRecDepth 8192 in
/-- `col(3, 0)`, copied to `P + 24`. -/
theorem op1 (hC : Rv64Verifier.Layout.ColSpec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {P : Word} (hpre : WalkPre s)
    (h : Ops OI s u A k R Q B P 1) (hpc : u.pc = 0x80004b34)
    (x10 : u.getReg .x10 = s.getReg .x2 - 928) (x11 : u.getReg .x11 = BitVec.ofNat 64 (1 + 2))
    (x12 : u.getReg .x12 = 0) (x1 : u.getReg .x1 = 0x8000190c) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = 0x80004b34 ∧ Ops OI s t A k R Q B P 2 ∧
      t.getReg .x10 = s.getReg .x2 - 928 ∧ t.getReg .x11 = BitVec.ofNat 64 (2 + 2) ∧
      t.getReg .x12 = 0 ∧ t.getReg .x1 = 0x80001938) ∨ Dead Image.code t) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  obtain ⟨t, hr, ⟨hpct, H, fo, fv, fb⟩ | hd⟩ := h.col hC hpre hpc x10 x11 x12 (by decide)
  swap
  · exact ⟨t, hr, Or.inr hd⟩
  have sp : t.getReg .x2 = s.getReg .x2 - 2656 := H.m.inv.sp
  have x9 := H.x9
  have x8 := H.x8 (by decide)
  have hP := H.hb
  obtain ⟨p1, p2, p3⟩ := H.buf
  have hmP : Mapped P 288 := Or.inl ⟨by
    have := hpre.heap.lo; have := H.m.bufQ; simp only [heapStart] at *; omega, hP⟩
  obtain ⟨v, hr', hv⟩ := Sym.BlockSpec.reaches b8000190c_spec
    (by rw [hpct, returnAddress_eq, x1]; decide) (by
      rv_eval [sp, x9, x8]
      and_intros
      all_goals first
        | valid_access hval [hb1]
        | exact Mapped.valid8 hmP (by addr_omega [hP]) (by addr_omega [hP]) (by addr_omega [hP, p1])
        | addr_omega [hb1, hP])
  have ea : t.getReg .x9 + 24 = P + BitVec.ofNat 64 (24 * 1) := by rw [x9]; rfl
  have k := b8000190c_keeps hv
  have e (N M : Word) (hNM : N.toNat + M.toNat = 2656) : t.getReg .x2 + N = s.getReg .x2 - M :=
    spAdd hpre sp hNM
  have H' := H.copy hpre (by decide) fo fv fb ((MemFrame.dframe (by rw [← ea]; exact b8000190c_frame hv (by rw [x9]; omega))).mono fun _ h ↦ Or.inl h)
    (by rw [← ea, b8000190c_m_x9_24 hv, e 1728 928 (by decide)])
    (by rw [show P + BitVec.ofNat 64 (24 * 1) + 8 = t.getReg .x9 + 32 from (by rw [← ea, BitVec.add_assoc]; rfl), b8000190c_m_x9_32 hv,
      show s.getReg .x2 - 928 + 8 = t.getReg .x2 + 1736 by
        rw [sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]])
    (by rw [show P + BitVec.ofNat 64 (24 * 1) + 16 = t.getReg .x9 + 40 from (by rw [← ea, BitVec.add_assoc]; rfl), b8000190c_m_x9_40 hv,
      show s.getReg .x2 - 928 + 16 = t.getReg .x2 + 1744 by
        rw [sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]])
    (k .x2 (by decide)) (fun _ ↦ k .x8 (by decide)) (k .x9 (by decide))
    (k .x26 (by decide)) (fun h ↦ absurd h (by decide)) (fun h ↦ absurd h (by decide)) (fun h ↦ absurd h (by decide))
  exact ⟨v, hr.trans hr', Or.inl ⟨b8000190c_pc hv, H', by rw [b8000190c_x10 hv, e 1728 928 (by decide)],
    by rw [b8000190c_x11 hv]; rfl, b8000190c_x12 hv, b8000190c_x1 hv⟩⟩

set_option maxRecDepth 8192 in
/-- `col(4, 0)`, copied to `P + 48`. -/
theorem op2 (hC : Rv64Verifier.Layout.ColSpec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {P : Word} (hpre : WalkPre s)
    (h : Ops OI s u A k R Q B P 2) (hpc : u.pc = 0x80004b34)
    (x10 : u.getReg .x10 = s.getReg .x2 - 928) (x11 : u.getReg .x11 = BitVec.ofNat 64 (2 + 2))
    (x12 : u.getReg .x12 = 0) (x1 : u.getReg .x1 = 0x80001938) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = 0x80004b34 ∧ Ops OI s t A k R Q B P 3 ∧
      t.getReg .x10 = s.getReg .x2 - 928 ∧ t.getReg .x11 = BitVec.ofNat 64 (3 + 2) ∧
      t.getReg .x12 = 0 ∧ t.getReg .x1 = 0x80001964) ∨ Dead Image.code t) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  obtain ⟨t, hr, ⟨hpct, H, fo, fv, fb⟩ | hd⟩ := h.col hC hpre hpc x10 x11 x12 (by decide)
  swap
  · exact ⟨t, hr, Or.inr hd⟩
  have sp : t.getReg .x2 = s.getReg .x2 - 2656 := H.m.inv.sp
  have x9 := H.x9
  have x8 := H.x8 (by decide)
  have hP := H.hb
  obtain ⟨p1, p2, p3⟩ := H.buf
  have hmP : Mapped P 288 := Or.inl ⟨by
    have := hpre.heap.lo; have := H.m.bufQ; simp only [heapStart] at *; omega, hP⟩
  obtain ⟨v, hr', hv⟩ := Sym.BlockSpec.reaches b80001938_spec
    (by rw [hpct, returnAddress_eq, x1]; decide) (by
      rv_eval [sp, x9, x8]
      and_intros
      all_goals first
        | valid_access hval [hb1]
        | exact Mapped.valid8 hmP (by addr_omega [hP]) (by addr_omega [hP]) (by addr_omega [hP, p1])
        | addr_omega [hb1, hP])
  have ea : t.getReg .x9 + 48 = P + BitVec.ofNat 64 (24 * 2) := by rw [x9]; rfl
  have k := b80001938_keeps hv
  have e (N M : Word) (hNM : N.toNat + M.toNat = 2656) : t.getReg .x2 + N = s.getReg .x2 - M :=
    spAdd hpre sp hNM
  have H' := H.copy hpre (by decide) fo fv fb ((MemFrame.dframe (by rw [← ea]; exact b80001938_frame hv (by rw [x9]; omega))).mono fun _ h ↦ Or.inl h)
    (by rw [← ea, b80001938_m_x9_48 hv, e 1728 928 (by decide)])
    (by rw [show P + BitVec.ofNat 64 (24 * 2) + 8 = t.getReg .x9 + 56 from (by rw [← ea, BitVec.add_assoc]; rfl), b80001938_m_x9_56 hv,
      show s.getReg .x2 - 928 + 8 = t.getReg .x2 + 1736 by
        rw [sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]])
    (by rw [show P + BitVec.ofNat 64 (24 * 2) + 16 = t.getReg .x9 + 64 from (by rw [← ea, BitVec.add_assoc]; rfl), b80001938_m_x9_64 hv,
      show s.getReg .x2 - 928 + 16 = t.getReg .x2 + 1744 by
        rw [sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]])
    (k .x2 (by decide)) (fun _ ↦ k .x8 (by decide)) (k .x9 (by decide))
    (k .x26 (by decide)) (fun h ↦ absurd h (by decide)) (fun h ↦ absurd h (by decide)) (fun h ↦ absurd h (by decide))
  exact ⟨v, hr.trans hr', Or.inl ⟨b80001938_pc hv, H', by rw [b80001938_x10 hv, e 1728 928 (by decide)],
    by rw [b80001938_x11 hv]; rfl, b80001938_x12 hv, b80001938_x1 hv⟩⟩

set_option maxRecDepth 8192 in
/-- `col(5, 0)`, copied to `P + 72`. -/
theorem op3 (hC : Rv64Verifier.Layout.ColSpec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {P : Word} (hpre : WalkPre s)
    (h : Ops OI s u A k R Q B P 3) (hpc : u.pc = 0x80004b34)
    (x10 : u.getReg .x10 = s.getReg .x2 - 928) (x11 : u.getReg .x11 = BitVec.ofNat 64 (3 + 2))
    (x12 : u.getReg .x12 = 0) (x1 : u.getReg .x1 = 0x80001964) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = 0x80004b34 ∧ Ops OI s t A k R Q B P 4 ∧
      t.getReg .x10 = s.getReg .x2 - 928 ∧ t.getReg .x11 = BitVec.ofNat 64 (4 + 2) ∧
      t.getReg .x12 = 0 ∧ t.getReg .x1 = 0x80001990) ∨ Dead Image.code t) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  obtain ⟨t, hr, ⟨hpct, H, fo, fv, fb⟩ | hd⟩ := h.col hC hpre hpc x10 x11 x12 (by decide)
  swap
  · exact ⟨t, hr, Or.inr hd⟩
  have sp : t.getReg .x2 = s.getReg .x2 - 2656 := H.m.inv.sp
  have x9 := H.x9
  have x8 := H.x8 (by decide)
  have hP := H.hb
  obtain ⟨p1, p2, p3⟩ := H.buf
  have hmP : Mapped P 288 := Or.inl ⟨by
    have := hpre.heap.lo; have := H.m.bufQ; simp only [heapStart] at *; omega, hP⟩
  obtain ⟨v, hr', hv⟩ := Sym.BlockSpec.reaches b80001964_spec
    (by rw [hpct, returnAddress_eq, x1]; decide) (by
      rv_eval [sp, x9, x8]
      and_intros
      all_goals first
        | valid_access hval [hb1]
        | exact Mapped.valid8 hmP (by addr_omega [hP]) (by addr_omega [hP]) (by addr_omega [hP, p1])
        | addr_omega [hb1, hP])
  have ea : t.getReg .x9 + 72 = P + BitVec.ofNat 64 (24 * 3) := by rw [x9]; rfl
  have k := b80001964_keeps hv
  have e (N M : Word) (hNM : N.toNat + M.toNat = 2656) : t.getReg .x2 + N = s.getReg .x2 - M :=
    spAdd hpre sp hNM
  have H' := H.copy hpre (by decide) fo fv fb ((MemFrame.dframe (by rw [← ea]; exact b80001964_frame hv (by rw [x9]; omega))).mono fun _ h ↦ Or.inl h)
    (by rw [← ea, b80001964_m_x9_72 hv, e 1728 928 (by decide)])
    (by rw [show P + BitVec.ofNat 64 (24 * 3) + 8 = t.getReg .x9 + 80 from (by rw [← ea, BitVec.add_assoc]; rfl), b80001964_m_x9_80 hv,
      show s.getReg .x2 - 928 + 8 = t.getReg .x2 + 1736 by
        rw [sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]])
    (by rw [show P + BitVec.ofNat 64 (24 * 3) + 16 = t.getReg .x9 + 88 from (by rw [← ea, BitVec.add_assoc]; rfl), b80001964_m_x9_88 hv,
      show s.getReg .x2 - 928 + 16 = t.getReg .x2 + 1744 by
        rw [sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]])
    (k .x2 (by decide)) (fun _ ↦ k .x8 (by decide)) (k .x9 (by decide))
    (k .x26 (by decide)) (fun h ↦ absurd h (by decide)) (fun h ↦ absurd h (by decide)) (fun h ↦ absurd h (by decide))
  exact ⟨v, hr.trans hr', Or.inl ⟨b80001964_pc hv, H', by rw [b80001964_x10 hv, e 1728 928 (by decide)],
    by rw [b80001964_x11 hv]; rfl, b80001964_x12 hv, b80001964_x1 hv⟩⟩

set_option maxRecDepth 8192 in
/-- `col(6, 0)`, copied to `P + 96`. -/
theorem op4 (hC : Rv64Verifier.Layout.ColSpec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {P : Word} (hpre : WalkPre s)
    (h : Ops OI s u A k R Q B P 4) (hpc : u.pc = 0x80004b34)
    (x10 : u.getReg .x10 = s.getReg .x2 - 928) (x11 : u.getReg .x11 = BitVec.ofNat 64 (4 + 2))
    (x12 : u.getReg .x12 = 0) (x1 : u.getReg .x1 = 0x80001990) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = 0x80004b34 ∧ Ops OI s t A k R Q B P 5 ∧
      t.getReg .x10 = s.getReg .x2 - 928 ∧ t.getReg .x11 = BitVec.ofNat 64 (5 + 2) ∧
      t.getReg .x12 = 0 ∧ t.getReg .x1 = 0x800019bc) ∨ Dead Image.code t) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  obtain ⟨t, hr, ⟨hpct, H, fo, fv, fb⟩ | hd⟩ := h.col hC hpre hpc x10 x11 x12 (by decide)
  swap
  · exact ⟨t, hr, Or.inr hd⟩
  have sp : t.getReg .x2 = s.getReg .x2 - 2656 := H.m.inv.sp
  have x9 := H.x9
  have x8 := H.x8 (by decide)
  have hP := H.hb
  obtain ⟨p1, p2, p3⟩ := H.buf
  have hmP : Mapped P 288 := Or.inl ⟨by
    have := hpre.heap.lo; have := H.m.bufQ; simp only [heapStart] at *; omega, hP⟩
  obtain ⟨v, hr', hv⟩ := Sym.BlockSpec.reaches b80001990_spec
    (by rw [hpct, returnAddress_eq, x1]; decide) (by
      rv_eval [sp, x9, x8]
      and_intros
      all_goals first
        | valid_access hval [hb1]
        | exact Mapped.valid8 hmP (by addr_omega [hP]) (by addr_omega [hP]) (by addr_omega [hP, p1])
        | addr_omega [hb1, hP])
  have ea : t.getReg .x9 + 96 = P + BitVec.ofNat 64 (24 * 4) := by rw [x9]; rfl
  have k := b80001990_keeps hv
  have e (N M : Word) (hNM : N.toNat + M.toNat = 2656) : t.getReg .x2 + N = s.getReg .x2 - M :=
    spAdd hpre sp hNM
  have H' := H.copy hpre (by decide) fo fv fb ((MemFrame.dframe (by rw [← ea]; exact b80001990_frame hv (by rw [x9]; omega))).mono fun _ h ↦ Or.inl h)
    (by rw [← ea, b80001990_m_x9_96 hv, e 1728 928 (by decide)])
    (by rw [show P + BitVec.ofNat 64 (24 * 4) + 8 = t.getReg .x9 + 104 from (by rw [← ea, BitVec.add_assoc]; rfl), b80001990_m_x9_104 hv,
      show s.getReg .x2 - 928 + 8 = t.getReg .x2 + 1736 by
        rw [sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]])
    (by rw [show P + BitVec.ofNat 64 (24 * 4) + 16 = t.getReg .x9 + 112 from (by rw [← ea, BitVec.add_assoc]; rfl), b80001990_m_x9_112 hv,
      show s.getReg .x2 - 928 + 16 = t.getReg .x2 + 1744 by
        rw [sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]])
    (k .x2 (by decide)) (fun _ ↦ k .x8 (by decide)) (k .x9 (by decide))
    (k .x26 (by decide)) (fun h ↦ absurd h (by decide)) (fun h ↦ absurd h (by decide)) (fun h ↦ absurd h (by decide))
  exact ⟨v, hr.trans hr', Or.inl ⟨b80001990_pc hv, H', by rw [b80001990_x10 hv, e 1728 928 (by decide)],
    by rw [b80001990_x11 hv]; rfl, b80001990_x12 hv, b80001990_x1 hv⟩⟩

set_option maxRecDepth 8192 in
/-- `col(7, 0)`, copied to `P + 120`. -/
theorem op5 (hC : Rv64Verifier.Layout.ColSpec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {P : Word} (hpre : WalkPre s)
    (h : Ops OI s u A k R Q B P 5) (hpc : u.pc = 0x80004b34)
    (x10 : u.getReg .x10 = s.getReg .x2 - 928) (x11 : u.getReg .x11 = BitVec.ofNat 64 (5 + 2))
    (x12 : u.getReg .x12 = 0) (x1 : u.getReg .x1 = 0x800019bc) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = 0x80004b34 ∧ Ops OI s t A k R Q B P 6 ∧
      t.getReg .x10 = s.getReg .x2 - 928 ∧ t.getReg .x11 = BitVec.ofNat 64 (6 + 2) ∧
      t.getReg .x12 = 0 ∧ t.getReg .x1 = 0x800019e8) ∨ Dead Image.code t) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  obtain ⟨t, hr, ⟨hpct, H, fo, fv, fb⟩ | hd⟩ := h.col hC hpre hpc x10 x11 x12 (by decide)
  swap
  · exact ⟨t, hr, Or.inr hd⟩
  have sp : t.getReg .x2 = s.getReg .x2 - 2656 := H.m.inv.sp
  have x9 := H.x9
  have x8 := H.x8 (by decide)
  have hP := H.hb
  obtain ⟨p1, p2, p3⟩ := H.buf
  have hmP : Mapped P 288 := Or.inl ⟨by
    have := hpre.heap.lo; have := H.m.bufQ; simp only [heapStart] at *; omega, hP⟩
  obtain ⟨v, hr', hv⟩ := Sym.BlockSpec.reaches b800019bc_spec
    (by rw [hpct, returnAddress_eq, x1]; decide) (by
      rv_eval [sp, x9, x8]
      and_intros
      all_goals first
        | valid_access hval [hb1]
        | exact Mapped.valid8 hmP (by addr_omega [hP]) (by addr_omega [hP]) (by addr_omega [hP, p1])
        | addr_omega [hb1, hP])
  have ea : t.getReg .x9 + 120 = P + BitVec.ofNat 64 (24 * 5) := by rw [x9]; rfl
  have k := b800019bc_keeps hv
  have e (N M : Word) (hNM : N.toNat + M.toNat = 2656) : t.getReg .x2 + N = s.getReg .x2 - M :=
    spAdd hpre sp hNM
  have H' := H.copy hpre (by decide) fo fv fb ((MemFrame.dframe (by rw [← ea]; exact b800019bc_frame hv (by rw [x9]; omega))).mono fun _ h ↦ Or.inl h)
    (by rw [← ea, b800019bc_m_x9_120 hv, e 1728 928 (by decide)])
    (by rw [show P + BitVec.ofNat 64 (24 * 5) + 8 = t.getReg .x9 + 128 from (by rw [← ea, BitVec.add_assoc]; rfl), b800019bc_m_x9_128 hv,
      show s.getReg .x2 - 928 + 8 = t.getReg .x2 + 1736 by
        rw [sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]])
    (by rw [show P + BitVec.ofNat 64 (24 * 5) + 16 = t.getReg .x9 + 136 from (by rw [← ea, BitVec.add_assoc]; rfl), b800019bc_m_x9_136 hv,
      show s.getReg .x2 - 928 + 16 = t.getReg .x2 + 1744 by
        rw [sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]])
    (k .x2 (by decide)) (fun _ ↦ k .x8 (by decide)) (k .x9 (by decide))
    (k .x26 (by decide)) (fun h ↦ absurd h (by decide)) (fun h ↦ absurd h (by decide)) (fun h ↦ absurd h (by decide))
  exact ⟨v, hr.trans hr', Or.inl ⟨b800019bc_pc hv, H', by rw [b800019bc_x10 hv, e 1728 928 (by decide)],
    by rw [b800019bc_x11 hv]; rfl, b800019bc_x12 hv, b800019bc_x1 hv⟩⟩

set_option maxRecDepth 8192 in
/-- `col(8, 0)`, copied to `P + 144`. -/
theorem op6 (hC : Rv64Verifier.Layout.ColSpec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {P : Word} (hpre : WalkPre s)
    (h : Ops OI s u A k R Q B P 6) (hpc : u.pc = 0x80004b34)
    (x10 : u.getReg .x10 = s.getReg .x2 - 928) (x11 : u.getReg .x11 = BitVec.ofNat 64 (6 + 2))
    (x12 : u.getReg .x12 = 0) (x1 : u.getReg .x1 = 0x800019e8) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = 0x80004b34 ∧ Ops OI s t A k R Q B P 7 ∧
      t.getReg .x10 = s.getReg .x2 - 928 ∧ t.getReg .x11 = BitVec.ofNat 64 (7 + 2) ∧
      t.getReg .x12 = 0 ∧ t.getReg .x1 = 0x80001a14) ∨ Dead Image.code t) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  obtain ⟨t, hr, ⟨hpct, H, fo, fv, fb⟩ | hd⟩ := h.col hC hpre hpc x10 x11 x12 (by decide)
  swap
  · exact ⟨t, hr, Or.inr hd⟩
  have sp : t.getReg .x2 = s.getReg .x2 - 2656 := H.m.inv.sp
  have x9 := H.x9
  have x8 := H.x8 (by decide)
  have hP := H.hb
  obtain ⟨p1, p2, p3⟩ := H.buf
  have hmP : Mapped P 288 := Or.inl ⟨by
    have := hpre.heap.lo; have := H.m.bufQ; simp only [heapStart] at *; omega, hP⟩
  obtain ⟨v, hr', hv⟩ := Sym.BlockSpec.reaches b800019e8_spec
    (by rw [hpct, returnAddress_eq, x1]; decide) (by
      rv_eval [sp, x9, x8]
      and_intros
      all_goals first
        | valid_access hval [hb1]
        | exact Mapped.valid8 hmP (by addr_omega [hP]) (by addr_omega [hP]) (by addr_omega [hP, p1])
        | addr_omega [hb1, hP])
  have ea : t.getReg .x9 + 144 = P + BitVec.ofNat 64 (24 * 6) := by rw [x9]; rfl
  have k := b800019e8_keeps hv
  have e (N M : Word) (hNM : N.toNat + M.toNat = 2656) : t.getReg .x2 + N = s.getReg .x2 - M :=
    spAdd hpre sp hNM
  have H' := H.copy hpre (by decide) fo fv fb ((MemFrame.dframe (by rw [← ea]; exact b800019e8_frame hv (by rw [x9]; omega))).mono fun _ h ↦ Or.inl h)
    (by rw [← ea, b800019e8_m_x9_144 hv, e 1728 928 (by decide)])
    (by rw [show P + BitVec.ofNat 64 (24 * 6) + 8 = t.getReg .x9 + 152 from (by rw [← ea, BitVec.add_assoc]; rfl), b800019e8_m_x9_152 hv,
      show s.getReg .x2 - 928 + 8 = t.getReg .x2 + 1736 by
        rw [sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]])
    (by rw [show P + BitVec.ofNat 64 (24 * 6) + 16 = t.getReg .x9 + 160 from (by rw [← ea, BitVec.add_assoc]; rfl), b800019e8_m_x9_160 hv,
      show s.getReg .x2 - 928 + 16 = t.getReg .x2 + 1744 by
        rw [sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]])
    (k .x2 (by decide)) (fun _ ↦ k .x8 (by decide)) (k .x9 (by decide))
    (k .x26 (by decide)) (fun h ↦ absurd h (by decide)) (fun h ↦ absurd h (by decide)) (fun h ↦ absurd h (by decide))
  exact ⟨v, hr.trans hr', Or.inl ⟨b800019e8_pc hv, H', by rw [b800019e8_x10 hv, e 1728 928 (by decide)],
    by rw [b800019e8_x11 hv]; rfl, b800019e8_x12 hv, b800019e8_x1 hv⟩⟩

set_option maxRecDepth 8192 in
/-- `col(9, 0)`, copied to `P + 168`. -/
theorem op7 (hC : Rv64Verifier.Layout.ColSpec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {P : Word} (hpre : WalkPre s)
    (h : Ops OI s u A k R Q B P 7) (hpc : u.pc = 0x80004b34)
    (x10 : u.getReg .x10 = s.getReg .x2 - 928) (x11 : u.getReg .x11 = BitVec.ofNat 64 (7 + 2))
    (x12 : u.getReg .x12 = 0) (x1 : u.getReg .x1 = 0x80001a14) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = 0x80004b34 ∧ Ops OI s t A k R Q B P 8 ∧
      t.getReg .x10 = s.getReg .x2 - 928 ∧ t.getReg .x11 = BitVec.ofNat 64 (8 + 2) ∧
      t.getReg .x12 = 0 ∧ t.getReg .x1 = 0x80001a44) ∨ Dead Image.code t) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  obtain ⟨t, hr, ⟨hpct, H, fo, fv, fb⟩ | hd⟩ := h.col hC hpre hpc x10 x11 x12 (by decide)
  swap
  · exact ⟨t, hr, Or.inr hd⟩
  have sp : t.getReg .x2 = s.getReg .x2 - 2656 := H.m.inv.sp
  have x9 := H.x9
  have x8 := H.x8 (by decide)
  have hP := H.hb
  obtain ⟨p1, p2, p3⟩ := H.buf
  have hmP : Mapped P 288 := Or.inl ⟨by
    have := hpre.heap.lo; have := H.m.bufQ; simp only [heapStart] at *; omega, hP⟩
  obtain ⟨v, hr', hv⟩ := Sym.BlockSpec.reaches b80001a14_spec
    (by rw [hpct, returnAddress_eq, x1]; decide) (by
      rv_eval [sp, x9, x8]
      and_intros
      all_goals first
        | valid_access hval [hb1]
        | exact Mapped.valid8 hmP (by addr_omega [hP]) (by addr_omega [hP]) (by addr_omega [hP, p1])
        | addr_omega [hb1, hP])
  have ea : t.getReg .x9 + 168 = P + BitVec.ofNat 64 (24 * 7) := by rw [x9]; rfl
  have k := b80001a14_keeps hv
  have e (N M : Word) (hNM : N.toNat + M.toNat = 2656) : t.getReg .x2 + N = s.getReg .x2 - M :=
    spAdd hpre sp hNM
  have H' := H.copy hpre (by decide) fo fv fb ((MemFrame.dframe (by rw [← ea]; exact b80001a14_frame hv (by rw [x9]; omega))).mono fun _ h ↦ Or.inl h)
    (by rw [← ea, b80001a14_m_x9_168 hv, e 1728 928 (by decide)])
    (by rw [show P + BitVec.ofNat 64 (24 * 7) + 8 = t.getReg .x9 + 176 from (by rw [← ea, BitVec.add_assoc]; rfl), b80001a14_m_x9_176 hv,
      show s.getReg .x2 - 928 + 8 = t.getReg .x2 + 1736 by
        rw [sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]])
    (by rw [show P + BitVec.ofNat 64 (24 * 7) + 16 = t.getReg .x9 + 184 from (by rw [← ea, BitVec.add_assoc]; rfl), b80001a14_m_x9_184 hv,
      show s.getReg .x2 - 928 + 16 = t.getReg .x2 + 1744 by
        rw [sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]])
    (k .x2 (by decide)) (fun _ ↦ k .x8 (by decide)) (k .x9 (by decide))
    (k .x26 (by decide)) (fun h ↦ absurd h (by decide)) (fun _ ↦ b80001a14_x19 hv) (fun h ↦ absurd h (by decide))
  exact ⟨v, hr.trans hr', Or.inl ⟨b80001a14_pc hv, H', by rw [b80001a14_x10 hv, e 1728 928 (by decide)],
    by rw [b80001a14_x11 hv]; rfl, b80001a14_x12 hv, b80001a14_x1 hv⟩⟩

set_option maxRecDepth 8192 in
/-- `col(10, 0)`, copied to `P + 192`. -/
theorem op8 (hC : Rv64Verifier.Layout.ColSpec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {P : Word} (hpre : WalkPre s)
    (h : Ops OI s u A k R Q B P 8) (hpc : u.pc = 0x80004b34)
    (x10 : u.getReg .x10 = s.getReg .x2 - 928) (x11 : u.getReg .x11 = BitVec.ofNat 64 (8 + 2))
    (x12 : u.getReg .x12 = 0) (x1 : u.getReg .x1 = 0x80001a44) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = 0x80004b34 ∧ Ops OI s t A k R Q B P 9 ∧
      t.getReg .x10 = s.getReg .x2 - 928 ∧ t.getReg .x11 = BitVec.ofNat 64 (9 + 2) ∧
      t.getReg .x12 = 0 ∧ t.getReg .x1 = 0x80001a74) ∨ Dead Image.code t) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  obtain ⟨t, hr, ⟨hpct, H, fo, fv, fb⟩ | hd⟩ := h.col hC hpre hpc x10 x11 x12 (by decide)
  swap
  · exact ⟨t, hr, Or.inr hd⟩
  have sp : t.getReg .x2 = s.getReg .x2 - 2656 := H.m.inv.sp
  have x9 := H.x9
  have x8 := H.x8 (by decide)
  have hP := H.hb
  obtain ⟨p1, p2, p3⟩ := H.buf
  have hmP : Mapped P 288 := Or.inl ⟨by
    have := hpre.heap.lo; have := H.m.bufQ; simp only [heapStart] at *; omega, hP⟩
  obtain ⟨v, hr', hv⟩ := Sym.BlockSpec.reaches b80001a44_spec
    (by rw [hpct, returnAddress_eq, x1]; decide) (by
      rv_eval [sp, x9, x8]
      and_intros
      all_goals first
        | valid_access hval [hb1]
        | exact Mapped.valid8 hmP (by addr_omega [hP]) (by addr_omega [hP]) (by addr_omega [hP, p1])
        | addr_omega [hb1, hP])
  have ea : t.getReg .x9 + 192 = P + BitVec.ofNat 64 (24 * 8) := by rw [x9]; rfl
  have k := b80001a44_keeps hv
  have e (N M : Word) (hNM : N.toNat + M.toNat = 2656) : t.getReg .x2 + N = s.getReg .x2 - M :=
    spAdd hpre sp hNM
  have H' := H.copy hpre (by decide) fo fv fb ((MemFrame.dframe (by rw [← ea]; exact b80001a44_frame hv (by rw [x9]; omega))).mono fun _ h ↦ Or.inl h)
    (by rw [← ea, b80001a44_m_x9_192 hv, e 1728 928 (by decide)])
    (by rw [show P + BitVec.ofNat 64 (24 * 8) + 8 = t.getReg .x9 + 200 from (by rw [← ea, BitVec.add_assoc]; rfl), b80001a44_m_x9_200 hv,
      show s.getReg .x2 - 928 + 8 = t.getReg .x2 + 1736 by
        rw [sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]])
    (by rw [show P + BitVec.ofNat 64 (24 * 8) + 16 = t.getReg .x9 + 208 from (by rw [← ea, BitVec.add_assoc]; rfl), b80001a44_m_x9_208 hv,
      show s.getReg .x2 - 928 + 16 = t.getReg .x2 + 1744 by
        rw [sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]])
    (k .x2 (by decide)) (fun _ ↦ k .x8 (by decide)) (k .x9 (by decide))
    (k .x26 (by decide)) (fun h ↦ absurd h (by decide)) (fun h ↦ by rw [k .x19 (by decide)]; exact H.x19 (by omega)) (fun _ ↦ b80001a44_x21 hv)
  exact ⟨v, hr.trans hr', Or.inl ⟨b80001a44_pc hv, H', by rw [b80001a44_x10 hv, e 1728 928 (by decide)],
    by rw [b80001a44_x11 hv]; rfl, b80001a44_x12 hv, b80001a44_x1 hv⟩⟩

set_option maxRecDepth 8192 in
/-- `col(11, 0)`, copied to `P + 216`. -/
theorem op9 (hC : Rv64Verifier.Layout.ColSpec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {P : Word} (hpre : WalkPre s)
    (h : Ops OI s u A k R Q B P 9) (hpc : u.pc = 0x80004b34)
    (x10 : u.getReg .x10 = s.getReg .x2 - 928) (x11 : u.getReg .x11 = BitVec.ofNat 64 (9 + 2))
    (x12 : u.getReg .x12 = 0) (x1 : u.getReg .x1 = 0x80001a74) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = 0x80004b34 ∧ Ops OI s t A k R Q B P 10 ∧
      t.getReg .x10 = s.getReg .x2 - 928 ∧ t.getReg .x11 = BitVec.ofNat 64 (10 + 2) ∧
      t.getReg .x12 = 0 ∧ t.getReg .x1 = 0x80001aa0) ∨ Dead Image.code t) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  obtain ⟨t, hr, ⟨hpct, H, fo, fv, fb⟩ | hd⟩ := h.col hC hpre hpc x10 x11 x12 (by decide)
  swap
  · exact ⟨t, hr, Or.inr hd⟩
  have sp : t.getReg .x2 = s.getReg .x2 - 2656 := H.m.inv.sp
  have x9 := H.x9
  have x8 := H.x8 (by decide)
  have hP := H.hb
  obtain ⟨p1, p2, p3⟩ := H.buf
  have hmP : Mapped P 288 := Or.inl ⟨by
    have := hpre.heap.lo; have := H.m.bufQ; simp only [heapStart] at *; omega, hP⟩
  obtain ⟨v, hr', hv⟩ := Sym.BlockSpec.reaches b80001a74_spec
    (by rw [hpct, returnAddress_eq, x1]; decide) (by
      rv_eval [sp, x9, x8]
      and_intros
      all_goals first
        | valid_access hval [hb1]
        | exact Mapped.valid8 hmP (by addr_omega [hP]) (by addr_omega [hP]) (by addr_omega [hP, p1])
        | addr_omega [hb1, hP])
  have ea : t.getReg .x9 + 216 = P + BitVec.ofNat 64 (24 * 9) := by rw [x9]; rfl
  have k := b80001a74_keeps hv
  have e (N M : Word) (hNM : N.toNat + M.toNat = 2656) : t.getReg .x2 + N = s.getReg .x2 - M :=
    spAdd hpre sp hNM
  have H' := H.copy hpre (by decide) fo fv fb ((MemFrame.dframe (by rw [← ea]; exact b80001a74_frame hv (by rw [x9]; omega))).mono fun _ h ↦ Or.inl h)
    (by rw [← ea, b80001a74_m_x9_216 hv, e 1728 928 (by decide)])
    (by rw [show P + BitVec.ofNat 64 (24 * 9) + 8 = t.getReg .x9 + 224 from (by rw [← ea, BitVec.add_assoc]; rfl), b80001a74_m_x9_224 hv,
      show s.getReg .x2 - 928 + 8 = t.getReg .x2 + 1736 by
        rw [sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]])
    (by rw [show P + BitVec.ofNat 64 (24 * 9) + 16 = t.getReg .x9 + 232 from (by rw [← ea, BitVec.add_assoc]; rfl), b80001a74_m_x9_232 hv,
      show s.getReg .x2 - 928 + 16 = t.getReg .x2 + 1744 by
        rw [sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]])
    (k .x2 (by decide)) (fun _ ↦ k .x8 (by decide)) (k .x9 (by decide))
    (k .x26 (by decide)) (fun h ↦ absurd h (by decide)) (fun h ↦ by rw [k .x19 (by decide)]; exact H.x19 (by omega)) (fun h ↦ by rw [k .x21 (by decide)]; exact H.x21 (by omega))
  exact ⟨v, hr.trans hr', Or.inl ⟨b80001a74_pc hv, H', by rw [b80001a74_x10 hv, e 1728 928 (by decide)],
    by rw [b80001a74_x11 hv]; rfl, b80001a74_x12 hv, b80001a74_x1 hv⟩⟩

set_option maxRecDepth 8192 in
/-- `col(12, 0)`, copied to `P + 240`. -/
theorem op10 (hC : Rv64Verifier.Layout.ColSpec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {P : Word} (hpre : WalkPre s)
    (h : Ops OI s u A k R Q B P 10) (hpc : u.pc = 0x80004b34)
    (x10 : u.getReg .x10 = s.getReg .x2 - 928) (x11 : u.getReg .x11 = BitVec.ofNat 64 (10 + 2))
    (x12 : u.getReg .x12 = 0) (x1 : u.getReg .x1 = 0x80001aa0) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = 0x80004b34 ∧ Ops OI s t A k R Q B P 11 ∧
      t.getReg .x10 = s.getReg .x2 - 928 ∧ t.getReg .x11 = BitVec.ofNat 64 (11 + 2) ∧
      t.getReg .x12 = 0 ∧ t.getReg .x1 = 0x80001ad0) ∨ Dead Image.code t) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  obtain ⟨t, hr, ⟨hpct, H, fo, fv, fb⟩ | hd⟩ := h.col hC hpre hpc x10 x11 x12 (by decide)
  swap
  · exact ⟨t, hr, Or.inr hd⟩
  have sp : t.getReg .x2 = s.getReg .x2 - 2656 := H.m.inv.sp
  have x9 := H.x9
  have x8 := H.x8 (by decide)
  have hP := H.hb
  obtain ⟨p1, p2, p3⟩ := H.buf
  have hmP : Mapped P 288 := Or.inl ⟨by
    have := hpre.heap.lo; have := H.m.bufQ; simp only [heapStart] at *; omega, hP⟩
  obtain ⟨v, hr', hv⟩ := Sym.BlockSpec.reaches b80001aa0_spec
    (by rw [hpct, returnAddress_eq, x1]; decide) (by
      rv_eval [sp, x9, x8]
      and_intros
      all_goals first
        | valid_access hval [hb1]
        | exact Mapped.valid8 hmP (by addr_omega [hP]) (by addr_omega [hP]) (by addr_omega [hP, p1])
        | addr_omega [hb1, hP])
  have ea : t.getReg .x9 + 240 = P + BitVec.ofNat 64 (24 * 10) := by rw [x9]; rfl
  have k := b80001aa0_keeps hv
  have e (N M : Word) (hNM : N.toNat + M.toNat = 2656) : t.getReg .x2 + N = s.getReg .x2 - M :=
    spAdd hpre sp hNM
  have H' := H.copy hpre (by decide) fo fv fb ((MemFrame.dframe (by rw [← ea]; exact b80001aa0_frame hv (by rw [x9]; omega))).mono fun _ h ↦ Or.inl h)
    (by rw [← ea, b80001aa0_m_x9_240 hv, e 1728 928 (by decide)])
    (by rw [show P + BitVec.ofNat 64 (24 * 10) + 8 = t.getReg .x9 + 248 from (by rw [← ea, BitVec.add_assoc]; rfl), b80001aa0_m_x9_248 hv,
      show s.getReg .x2 - 928 + 8 = t.getReg .x2 + 1736 by
        rw [sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]])
    (by rw [show P + BitVec.ofNat 64 (24 * 10) + 16 = t.getReg .x9 + 256 from (by rw [← ea, BitVec.add_assoc]; rfl), b80001aa0_m_x9_256 hv,
      show s.getReg .x2 - 928 + 16 = t.getReg .x2 + 1744 by
        rw [sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]])
    (k .x2 (by decide)) (fun _ ↦ k .x8 (by decide)) (k .x9 (by decide))
    (k .x26 (by decide)) (fun _ ↦ b80001aa0_x18 hv) (fun h ↦ by rw [k .x19 (by decide)]; exact H.x19 (by omega)) (fun h ↦ by rw [k .x21 (by decide)]; exact H.x21 (by omega))
  exact ⟨v, hr.trans hr', Or.inl ⟨b80001aa0_pc hv, H', by rw [b80001aa0_x10 hv, e 1728 928 (by decide)],
    by rw [b80001aa0_x11 hv]; rfl, b80001aa0_x12 hv, b80001aa0_x1 hv⟩⟩

set_option maxRecDepth 8192 in
/-- `col(13, 0)`, copied to `P + 264`; the length 12; the call of `bytecode`. -/
theorem op11 (hC : Rv64Verifier.Layout.ColSpec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {P : Word} (hpre : WalkPre s)
    (h : Ops OI s u A k R Q B P 11) (hpc : u.pc = 0x80004b34)
    (x10 : u.getReg .x10 = s.getReg .x2 - 928) (x11 : u.getReg .x11 = BitVec.ofNat 64 (11 + 2))
    (x12 : u.getReg .x12 = 0) (x1 : u.getReg .x1 = 0x80001ad0) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = 0x80004b94 ∧ Ops OI s t A k R Q B P 12 ∧
      t.getMem (s.getReg .x2 - 136) = 12 ∧ t.getReg .x10 = s.getReg .x2 - 1488 ∧
      t.getReg .x11 = 91 ∧ t.getReg .x12 = 5 ∧ t.getReg .x13 = s.getReg .x2 - 152 ∧
      t.getReg .x1 = 0x80001b0c) ∨ Dead Image.code t) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  obtain ⟨t, hr, ⟨hpct, H, fo, fv, fb⟩ | hd⟩ := h.col hC hpre hpc x10 x11 x12 (by decide)
  swap
  · exact ⟨t, hr, Or.inr hd⟩
  have sp : t.getReg .x2 = s.getReg .x2 - 2656 := H.m.inv.sp
  have x9 := H.x9
  have x8 := H.x8 (by decide)
  have x26 := H.x26
  have hP := H.hb
  obtain ⟨p1, p2, p3⟩ := H.buf
  have hmP : Mapped P 288 := Or.inl ⟨by
    have := hpre.heap.lo; have := H.m.bufQ; simp only [heapStart] at *; omega, hP⟩
  obtain ⟨v, hr', hv⟩ := Sym.BlockSpec.reaches b80001ad0_spec
    (by rw [hpct, returnAddress_eq, x1]; decide) (by
      rv_eval [sp, x9, x8, x26]
      and_intros
      all_goals first
        | valid_access hval [hb1]
        | exact Mapped.valid8 hmP (by addr_omega [hP]) (by addr_omega [hP]) (by addr_omega [hP, p1])
        | addr_omega [hb1, hP])
  have ea : t.getReg .x9 + 264 = P + BitVec.ofNat 64 (24 * 11) := by rw [x9]; rfl
  have k := b80001ad0_keeps hv
  have e (N M : Word) (hNM : N.toNat + M.toNat = 2656) : t.getReg .x2 + N = s.getReg .x2 - M :=
    spAdd hpre sp hNM
  have e376 : t.getReg .x26 + 376 = s.getReg .x2 - 136 := by
    rw [x26]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have fr : Rv64Verifier.Layout.DFrame t v fun x ↦ Within x (P + BitVec.ofNat 64 (24 * 11)) 24 ∨
      Within x (s.getReg .x2 - 136) 8 := Expect.ldframe hv (by
    rv_eval [sp, x9, x8, x26]
    simp only [Within]
    and_intros <;> addr_omega [hb1, hP])
  have H' := H.copy hpre (by decide) fo fv fb fr
    (by rw [← ea, b80001ad0_m_x9_264 hv, e 1728 928 (by decide)])
    (by rw [show P + BitVec.ofNat 64 (24 * 11) + 8 = t.getReg .x9 + 272 by rw [← ea, BitVec.add_assoc]; rfl,
      b80001ad0_m_x9_272 hv, show s.getReg .x2 - 928 + 8 = t.getReg .x2 + 1736 by
        rw [sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]])
    (by rw [show P + BitVec.ofNat 64 (24 * 11) + 16 = t.getReg .x9 + 280 by rw [← ea, BitVec.add_assoc]; rfl,
      b80001ad0_m_x9_280 hv, show s.getReg .x2 - 928 + 16 = t.getReg .x2 + 1744 by
        rw [sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]])
    (k .x2 (by decide)) (fun h ↦ absurd h (by decide)) (k .x9 (by decide)) (k .x26 (by decide))
    (fun h ↦ by rw [k .x18 (by decide)]; exact H.x18 (by omega))
    (fun h ↦ by rw [k .x19 (by decide)]; exact H.x19 (by omega))
    (fun h ↦ by rw [k .x21 (by decide)]; exact H.x21 (by omega))
  exact ⟨v, hr.trans hr', Or.inl ⟨b80001ad0_pc hv, H', by
    rw [← e376, b80001ad0_m_x26_376 hv, x8]; rfl, by rw [b80001ad0_x10 hv, e 1168 1488 (by decide)],
    b80001ad0_x11 hv, b80001ad0_x12 hv, by rw [b80001ad0_x13 hv, e 2504 152 (by decide)],
    b80001ad0_x1 hv⟩⟩

/-- `flushes_keccak`'s `Flushes` past `state_step` and `bytecode`. -/
def keccakHead : LayoutMirror.FlushesRust :=
  (({} : LayoutMirror.FlushesRust).stateStep 0 1).bytecode 0 91 5
    ((List.range 12).map fun i ↦ LayoutMirror.colRust (i + 2) 0)

theorem keccakHead_eq : keccakHead =
    (({} : LayoutMirror.FlushesRust).stateStep LayoutMirror.KeccakCol.pc
      LayoutMirror.KeccakCol.fp).bytecode LayoutMirror.KeccakCol.pc LayoutMirror.keccakCntBcRust
      LayoutMirror.opKeccakRust ((LayoutMirror.KeccakCol.oM ++ [LayoutMirror.KeccakCol.oTail,
        LayoutMirror.KeccakCol.oB8, LayoutMirror.KeccakCol.oCap, LayoutMirror.KeccakCol.oOut,
        LayoutMirror.KeccakCol.oddIn, LayoutMirror.KeccakCol.oddOut, LayoutMirror.KeccakCol.outTwo,
        LayoutMirror.KeccakCol.outAll]).map (LayoutMirror.colRust · 0)) := rfl

/-- At `0x80004d10`, the first `keccak_cell_lanes(false)` (into `sp + 1312`, return to
`0x80001b1c`): `walk`'s state (`M6`), the `Flushes` at `sp + 1168` past `state_step` and
`bytecode` (`keccakHead`), the heights' lengths 6 and 0 at `sp + 136`, `sp + 152`. -/
structure AtR6a (OI : MachineState → Word → List (List Opening) → Prop) (s u : MachineState)
    (A : List E) (k : Nat) (R Q : Word) (B : Nat) : Prop where
  m : M6 OI s u A k R Q B
  fl : FlAt s u keccakHead B
  lens : u.getMem (s.getReg .x2 - 2520) = 6 ∧ u.getMem (s.getReg .x2 - 2504) = 0
  x1 : u.getReg .x1 = 0x80001b1c
  x10 : u.getReg .x10 = s.getReg .x2 - 1344
  x11 : u.getReg .x11 = 0
  x26 : u.getReg .x26 = s.getReg .x2 - 512
  x18 : u.getReg .x18 = 13
  x19 : u.getReg .x19 = 10
  x21 : u.getReg .x21 = 11

set_option maxRecDepth 8192 in
/-- `bytecode(KECCAK_CNT_BC, OP_KECCAK, operands)`, then the call of `keccak_cell_lanes(false)`. -/
theorem r6bytecode (hBC : Rv64Verifier.Layout.BytecodeSpec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {P : Word} (hpre : WalkPre s)
    (h : Ops OI s u A k R Q B P 12) (hpc : u.pc = 0x80004b94)
    (hlen : u.getMem (s.getReg .x2 - 136) = 12) (x10 : u.getReg .x10 = s.getReg .x2 - 1488)
    (x11 : u.getReg .x11 = 91) (x12 : u.getReg .x12 = 5) (x13 : u.getReg .x13 = s.getReg .x2 - 152)
    (x1 : u.getReg .x1 = 0x80001b0c) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = 0x80004d10 ∧ AtR6a OI s t A k R Q B) ∨
      Dead Image.code t) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  have hab := hpre.stack.above
  have hx := hpre.stack.next
  rw [stackLo_eq] at hab
  rw [stackLo_eq, stack_eq] at hx
  simp only [heapEnd] at hab
  obtain ⟨p1, p2, p3⟩ := h.buf
  have hP := h.hb
  have hheap : HeapOk u := h.m.inv.heap
  have hlo := hpre.heap.lo
  have hQ := h.m.bufQ
  simp only [heapStart] at hlo
  have hn : Rv64Verifier.Layout.bytecodeStack ≤ 8736 := by decide
  have e8 : s.getReg .x2 - 152 + 8 = s.getReg .x2 - 144 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have e16 : s.getReg .x2 - 152 + 16 = s.getReg .x2 - 136 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have cap : vecCap u (s.getReg .x2 - 152) = 12 := h.vec.1
  have ptr : vecPtr u (s.getReg .x2 - 152) = P := by simp only [vecPtr, e8]; exact h.vec.2
  have len : vecLen u (s.getReg .x2 - 152) = 12 := by simp only [vecLen, e16]; exact hlen
  have e12 : (12 : Word).toNat = 12 := rfl
  have pre : Rv64Verifier.Layout.BytecodePre u := {
    heap := hheap
    stack := stk_sub hpre h.m.inv hn (by decide)
    self := by rw [x10]; valid_sub hval [hb1]
    ok := by rw [x10]; exact h.fl.ok
    selfFree := by rw [x10]; exact ⟨Or.inr (by addr_omega [hab, hb1]), by addr_omega [hx, hb1]⟩
    selfStack := by rw [x10, stackLo_callee h.m.inv]; addr_omega [hb1, hn]
    rodata := h.m.inv.rodata hpre
    ops := by rw [x13]; valid_sub hval [hb1]
    opsOk := by
      rw [x13]
      refine ⟨⟨?_, by rw [len, cap]⟩, ?_, ?_⟩
      · simp only [RawVecOk, Buf, cap, ptr, e12]
        exact ⟨p1, Or.inr ⟨by simp only [heapStart]; omega, by omega⟩⟩
      · rw [ptr, len, e12]; exact fun i hi ↦ (h.forms i hi).1
      · rw [ptr, len, e12]
        rintro x ⟨i, hi, hx⟩ hw
        have := (h.forms i hi).2.2 x hx
        simp only [Rv64Verifier.Layout.formVecBuf, ptr, cap, e12, Within] at hw
        omega
    opsFree := by rw [x13]; exact ⟨Or.inr (by addr_omega [hab, hb1]), by addr_omega [hx, hb1]⟩
    opsStack := by rw [x13, stackLo_callee h.m.inv]; addr_omega [hb1, hn]
    opsBuf := by
      rw [x13, ptr, len, e12]
      exact ⟨Or.inl (by omega), by addr_omega [hP]⟩
    opsBufStack := by
      rw [x13, ptr, len, e12, stackLo_callee h.m.inv]; addr_omega [hb1, hn, hP] }
  obtain ⟨t, hr, ⟨hpct, hp, ⟨g, gv⟩⟩ | hd⟩ := hBC u hpc pre
  swap
  · exact ⟨t, hr, Or.inr hd⟩
  rw [x10] at g gv
  rw [x11, x12, x13] at gv
  have vops : Rv64Verifier.Layout.formVecOf u (s.getReg .x2 - 152) =
      (List.range 12).map fun i ↦ LayoutMirror.colRust (i + 2) 0 := by
    simp only [Rv64Verifier.Layout.formVecOf, Rv64Verifier.Layout.formsAt, ptr, len, e12]
    exact List.map_congr_left fun i hi ↦ (h.forms i (List.mem_range.mp hi)).2.1
  have M' := h.m.step hpre (g.frame.mono fun x hx ↦ grow_w6 hpre h.m.inv hn h.m.bufQ.2.2.2
    (fun y hy ↦ h.fl.deep y (hy.imp Or.inl Or.inl)) h.fl.ok g.mono hx) g.heap g.mono (hp.reg .x2)
  have keep (y : Word) (hy : (s.getReg .x2 - 2656).toNat ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2 - 1488).toNat) :
      t.getMem y = u.getMem y :=
    g.frame y (fun z hz hw ↦ by
      rcases hw with hw | hw | hw | hw | hw
      · simp only [Within] at hz hw; addr_omega [hz, hw, hy, hb1]
      · have := (h.fl.ok.buf_below hw).2; have hh := hheap.hi; simp only [Within, heapEnd] at hz this hh
        addr_omega [hz, this, hy, hb1, hh]
      · rw [stackLo_callee h.m.inv] at hw; simp only [Within] at hz hw; addr_omega [hz, hw, hy, hb1, hn]
      · simp only [Within] at hz hw; addr_omega [hz, hw, hy, hb1]
      · simp only [Fresh] at hw; have hh := g.heap.hi; simp only [Within, heapEnd] at hz hh
        addr_omega [hz, hw, hy, hb1, hh]) (by addr_omega [hy, hb1])
  obtain ⟨v, hr', hv⟩ := Sym.BlockSpec.reaches b80001b0c_spec
    (by rw [hpct, returnAddress_eq, x1]; decide) (by rv_eval [])
  have m := b80001b0c_mem_same hv
  have kv := b80001b0c_keeps hv
  have hnv : heapNext v = heapNext t := by simp only [heapNext, m]
  refine ⟨v, hr.trans hr', Or.inl ⟨b80001b0c_pc hv, {
    m := M'.step hpre (Rv64Verifier.Layout.DFrame.of_same m _) ⟨hnv ▸ g.heap.lo, hnv ▸ g.heap.hi⟩
      hnv.ge (kv .x2 (by decide))
    fl := ⟨?_, ?_, fun x hx ↦ ?_⟩
    lens := ⟨by rw [m, keep _ (by addr_omega [hb1])]; exact h.lens.1,
      by rw [m, keep _ (by addr_omega [hb1])]; exact h.lens.2⟩
    x1 := b80001b0c_x1 hv
    x10 := by rw [b80001b0c_x10 hv, hp.reg .x2]; exact spAdd hpre h.m.inv.sp (by decide)
    x11 := b80001b0c_x11 hv
    x26 := by rw [kv .x26 (by decide), hp.reg .x26]; exact h.x26
    x18 := by rw [kv .x18 (by decide), hp.reg .x18]; exact h.x18 (by decide)
    x19 := by rw [kv .x19 (by decide), hp.reg .x19]; exact h.x19 (by decide)
    x21 := by rw [kv .x21 (by decide), hp.reg .x21]; exact h.x21 (by decide) }⟩⟩
  · exact (Rv64Verifier.Layout.flushesOf_frame (Rv64Verifier.Layout.DFrame.of_same m (fun _ ↦ False))
      g.ok (fun _ _ h ↦ h) (fun _ _ h ↦ h) (by addr_omega [hb1]) g.heap hnv.ge).2.1
  · rw [(Rv64Verifier.Layout.flushesOf_frame (Rv64Verifier.Layout.DFrame.of_same m (fun _ ↦ False))
      g.ok (fun _ _ h ↦ h) (fun _ _ h ↦ h) (by addr_omega [hb1]) g.heap hnv.ge).1, gv, h.fl.val, vops]
    rfl
  · rw [(Rv64Verifier.Layout.flushesOf_frame (Rv64Verifier.Layout.DFrame.of_same m (fun _ ↦ False))
      g.ok (fun _ _ h ↦ h) (fun _ _ h ↦ h) (by addr_omega [hb1]) g.heap hnv.ge).2.2.1] at hx
    rcases g.deep x hx with hd | hd | hd
    · exact h.fl.deep x hd
    · exact hd.elim
    · exact le_trans h.m.bufQ.2.2.2 hd.1

/-- **`tables()`, its first part**: from `state_step`'s call (`AtR5`) through `state_step`, the
twelve operand forms and `bytecode`, to the first `keccak_cell_lanes` call (`AtR6a`), or a trap. -/
theorem r6a (hAS : AllocSpec) (hRF : ReserveFastSpec 0x80004aec)
    (hSS : Rv64Verifier.Layout.StateStepSpec) (hC : Rv64Verifier.Layout.ColSpec)
    (hBC : Rv64Verifier.Layout.BytecodeSpec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState} {A : List E}
    {k : Nat} {Q : Word} (hpre : WalkPre s) (hpc : u.pc = 0x80004a90) (h : AtR5 OI s u A k Q) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = 0x80004d10 ∧
      AtR6a OI s t A k (u.getReg .x18) Q (heapNext u)) ∨ Dead Image.code t) := by
  obtain ⟨t₀, r₀, ⟨p₀, M₀, G₀, F₀⟩ | d⟩ := r6stateStep hSS hpre hpc h
  swap; · exact ⟨t₀, r₀, Or.inr d⟩
  obtain ⟨t, r, ⟨p, P, H, a, b, c, e⟩ | d⟩ := r6alloc hAS hRF hpre p₀ M₀ G₀ F₀
  swap; · exact ⟨t, r₀.trans r, Or.inr d⟩
  have R := r₀.trans r
  obtain ⟨t, r, ⟨p, H, a, b, c, e⟩ | d⟩ := op0 hC hpre H p a b c e
  swap; · exact ⟨t, R.trans r, Or.inr d⟩
  have R := R.trans r
  obtain ⟨t, r, ⟨p, H, a, b, c, e⟩ | d⟩ := op1 hC hpre H p a b c e
  swap; · exact ⟨t, R.trans r, Or.inr d⟩
  have R := R.trans r
  obtain ⟨t, r, ⟨p, H, a, b, c, e⟩ | d⟩ := op2 hC hpre H p a b c e
  swap; · exact ⟨t, R.trans r, Or.inr d⟩
  have R := R.trans r
  obtain ⟨t, r, ⟨p, H, a, b, c, e⟩ | d⟩ := op3 hC hpre H p a b c e
  swap; · exact ⟨t, R.trans r, Or.inr d⟩
  have R := R.trans r
  obtain ⟨t, r, ⟨p, H, a, b, c, e⟩ | d⟩ := op4 hC hpre H p a b c e
  swap; · exact ⟨t, R.trans r, Or.inr d⟩
  have R := R.trans r
  obtain ⟨t, r, ⟨p, H, a, b, c, e⟩ | d⟩ := op5 hC hpre H p a b c e
  swap; · exact ⟨t, R.trans r, Or.inr d⟩
  have R := R.trans r
  obtain ⟨t, r, ⟨p, H, a, b, c, e⟩ | d⟩ := op6 hC hpre H p a b c e
  swap; · exact ⟨t, R.trans r, Or.inr d⟩
  have R := R.trans r
  obtain ⟨t, r, ⟨p, H, a, b, c, e⟩ | d⟩ := op7 hC hpre H p a b c e
  swap; · exact ⟨t, R.trans r, Or.inr d⟩
  have R := R.trans r
  obtain ⟨t, r, ⟨p, H, a, b, c, e⟩ | d⟩ := op8 hC hpre H p a b c e
  swap; · exact ⟨t, R.trans r, Or.inr d⟩
  have R := R.trans r
  obtain ⟨t, r, ⟨p, H, a, b, c, e⟩ | d⟩ := op9 hC hpre H p a b c e
  swap; · exact ⟨t, R.trans r, Or.inr d⟩
  have R := R.trans r
  obtain ⟨t, r, ⟨p, H, a, b, c, e⟩ | d⟩ := op10 hC hpre H p a b c e
  swap; · exact ⟨t, R.trans r, Or.inr d⟩
  have R := R.trans r
  obtain ⟨t, r, ⟨p, H, l, a, b, c, f, e⟩ | d⟩ := op11 hC hpre H p a b c e
  swap; · exact ⟨t, R.trans r, Or.inr d⟩
  have R := R.trans r
  obtain ⟨t, r, ht⟩ := r6bytecode hBC hpre H p l a b c f e
  exact ⟨t, R.trans r, ht⟩

end Rv64Verifier.Proofs.Walk
