import Rv64Verifier.Proofs.Walk.R17C
import Rv64Verifier.Proofs.Walk.Announced

/-!
# `walk` R17, `table_sumcheck`'s arguments

`0x8000375c` sets `table_sumcheck`'s arguments (three on the stack); `tsEntry` reaches its entry
with `TableSumcheckPre`.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Compile Rv64Verifier.Runtime Rv64Verifier.Model
  Rv64Verifier.Transcript Rv64Verifier.Blocks.F4 Rv64Verifier.Bus
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- At `table_sumcheck`'s entry. -/
structure AtTS (s u₀ w : MachineState) (bus : BusResultRust) (PP : Word) : Prop where
  rest : Rest s u₀ w
  old : ∀ x : Word, x.toNat + 8 ≤ heapNext u₀ → w.getMem x = u₀.getMem x
  x1 : w.getReg .x1 = 0x800037ac
  x10 : w.getReg .x10 = s.getReg .x2 - 928
  x11 : w.getReg .x11 = u₀.getMem (s.getReg .x2 - 2456)
  x12 : w.getReg .x12 = 6
  x13 : w.getReg .x13 = u₀.getMem (s.getReg .x2 - 2464)
  x14 : w.getReg .x14 = 6
  x15 : w.getReg .x15 = u₀.getMem (s.getReg .x2 - 848)
  x16 : w.getReg .x16 = u₀.getMem (s.getReg .x2 - 840)
  x17 : w.getReg .x17 = PP
  x28 : w.getReg .x28 = 2
  x29 : w.getReg .x29 = PP + 48
  x30 : w.getReg .x30 = 3
  x31 : w.getReg .x31 = u₀.getMem (s.getReg .x2 - 872)
  eqLen : tsEqLen w = u₀.getMem (s.getReg .x2 - 864)
  target : tsTarget w = s.getReg .x2 - 1704
  self : tsSelf w = tp s
  regs : ∀ r ∈ ([.x19, .x21, .x25] : List Reg), w.getReg r = u₀.getReg r
  m184 : w.getMem (s.getReg .x2 - 2472) = u₀.getMem (s.getReg .x2 - 920)
  pp : NewBuf u₀ w PP 120 8
  powers : eListAt w PP 5 = LeanVM.Protocol.Verifier.powers (eAt w (s.getReg .x2 - 152)) 5
  tgt : eAt w (s.getReg .x2 - 1704) = dotRust (eListAt w (PP + 48) 3) bus.totals
  sample : ∀ T, TranscriptAt u₀ (tp s) T → ∃ T', TM.sample.run T =
    some (eAt w (s.getReg .x2 - 152), T') ∧ TranscriptAt w (tp s) T'

set_option maxRecDepth 8192 in
theorem tsArgs {OI : MachineState → Word → List (List Opening) → Prop}
    {s u₀ v : MachineState} {layout : LayoutMirror.LayoutRust} {rows : List (BitVec 64)}
    {lir : BitVec 64} {bus : BusResultRust} {PP : Word} (hpre : WalkPre s)
    (h : AtR17 OI s u₀ layout rows lir bus) (hpc : v.pc = 0x8000375c) (P : PreArgs s u₀ v bus PP) :
    ∃ w, Reaches Image.code v w ∧ w.pc = 0x80008010 ∧ AtTS s u₀ w bus PP := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  have R := P.rest
  have sp := R.inv.sp
  obtain ⟨w, hr, h₁⟩ := Sym.BlockSpec.reaches b8000375c_spec hpc (by
    rv_eval [sp]; and_intros <;> valid_access hval [hb1])
  have k₁ := b8000375c_keeps h₁
  have WA : ∀ a, (a = s.getReg .x2 - 2656 ∨ a = s.getReg .x2 - 2648 ∨ a = s.getReg .x2 - 2640) →
      InF s a ∧ ¬ KeepR s u₀ a := fun a ha ↦ by
    rcases ha with rfl | rfl | rfl
    · exact slot_ok (k := 2656) hpre R (by omega) (by omega)
    · exact slot_ok (k := 2648) hpre R (by omega) (by omega)
    · exact slot_ok (k := 2640) hpre R (by omega) (by omega)
  have st : StepW s v w (fun a ↦ a = s.getReg .x2 - 2656 ∨ a = s.getReg .x2 - 2648 ∨
      a = s.getReg .x2 - 2640) False := StepW.ofFrame hpre R.inv.heap (h₁.dframe (by
      rv_eval [sp]; simp only [true_or, or_true, and_self])) (fun a ha ↦ (WA a ha).1)
    (k₁ .x2 (by decide))
  have R₁ := R.stepW hpre WA st
  have fW : ∀ a, W17b s a → InF s a := fun a ha ↦ (W17b_ok hpre (Rest.of h.inv) ha).1
  have oldW : ∀ x : Word, x.toNat + 8 ≤ heapNext u₀ → w.getMem x = u₀.getMem x := fun x hx ↦ by
    rw [st.getH hpre (fun a ha ↦ (WA a ha).1) (by have := R.mono; omega),
      P.st.getH hpre fW hx]
  -- frame slots read from `v`: apart from what R17 wrote
  have gF (k : Nat) (hk : 2456 ≤ k ∧ k ≤ 2464) : v.getMem (s.getReg .x2 - BitVec.ofNat 64 k) =
      u₀.getMem (s.getReg .x2 - BitVec.ofNat 64 k) :=
    P.st.getF hpre (by addr_omega [hb1, hk]) (fun i hi hw ↦ by
        rcases hw with hw | hw | hw
        · exact notW17a hpre (by omega) (by
            intro m hm; simp only [List.mem_cons, List.not_mem_nil, or_false] at hm; omega) i hi hw
        · addr_omega [hw, hi, hb1, hk]
        · addr_omega [hw, hi, hb1, hk])
      fun _ ↦ by rw [tp]; addr_omega [hb1, hk]
  have ea (c d : Word) (hc : c.toNat + d.toNat = 2656) : v.getReg .x2 + c = s.getReg .x2 - d := by
    rw [sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1, hc]
  have sv : w.getReg .x2 = v.getReg .x2 := k₁ .x2 (by decide)
  have hppb := P.pp
  simp only [NewBuf] at hppb
  have hPPn : PP.toNat + 120 ≤ heapNext v := by
    rcases hppb.2 with h0 | h0
    · exact absurd h0 (by decide)
    · exact h0.2
  have stW : ∀ a, (a = s.getReg .x2 - 2656 ∨ a = s.getReg .x2 - 2648 ∨ a = s.getReg .x2 - 2640) →
      InF s a := fun a ha ↦ (WA a ha).1
  have nW (k : Nat) (hk : 112 ≤ k ∧ k ≤ 2632) : ∀ i < 24,
      ¬ (s.getReg .x2 - BitVec.ofNat 64 k + BitVec.ofNat 64 i = s.getReg .x2 - 2656 ∨
        s.getReg .x2 - BitVec.ofNat 64 k + BitVec.ofNat 64 i = s.getReg .x2 - 2648 ∨
        s.getReg .x2 - BitVec.ofNat 64 k + BitVec.ofNat 64 i = s.getReg .x2 - 2640) := by
    intro i hi hw
    rcases hw with hw | hw | hw <;> · have := congrArg BitVec.toNat hw; addr_omega [this, hb1, hk, hi]
  have e152 : eAt w (s.getReg .x2 - 152) = eAt v (s.getReg .x2 - 152) :=
    st.eAtF hpre (by addr_omega [hb1]) (nW 152 (by omega)) fun hf ↦ hf.elim
  have e1704 : eAt w (s.getReg .x2 - 1704) = eAt v (s.getReg .x2 - 1704) :=
    st.eAtF hpre (by addr_omega [hb1]) (nW 1704 (by omega)) fun hf ↦ hf.elim
  refine ⟨w, hr, b8000375c_pc h₁, {
    rest := R₁
    old := oldW
    x1 := b8000375c_x1 h₁
    x10 := by rw [b8000375c_x10 h₁, ea 1728 928 rfl]
    x11 := by rw [b8000375c_x11 h₁, ea 200 2456 rfl]; exact gF 2456 (by omega)
    x12 := b8000375c_x12 h₁
    x13 := by rw [b8000375c_x13 h₁, ea 192 2464 rfl]; exact gF 2464 (by omega)
    x14 := by rw [b8000375c_x14 h₁, P.regs .x27 (by decide), h.x27]
    x15 := by rw [b8000375c_x15 h₁, ea 64 2592 rfl, P.m64]
    x16 := by rw [b8000375c_x16 h₁, ea 56 2600 rfl, P.m56]
    x17 := by rw [b8000375c_x17 h₁, P.x18]
    x28 := by rw [b8000375c_x28 h₁, P.x24]
    x29 := by rw [b8000375c_x29 h₁, P.x26]
    x30 := by rw [b8000375c_x30 h₁, P.x20]
    x31 := by rw [b8000375c_x31 h₁, ea 160 2496 rfl, P.m160]
    eqLen := by
      show w.getMem (w.getReg .x2) = _
      rw [sv, b8000375c_m_x2_0 h₁, P.x22]
    target := by
      show w.getMem (w.getReg .x2 + 8) = _
      rw [sv, b8000375c_m_x2_8 h₁, P.x9]
    self := by
      show w.getMem (w.getReg .x2 + 16) = _
      rw [sv, b8000375c_m_x2_16 h₁, ea 208 2448 rfl]; rfl
    regs := fun r hr ↦ by
      have hr' := P.regs r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with rfl | rfl | rfl <;> simp)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> rw [k₁ _ (by decide), hr']
    m184 := by
      rw [show (2472 : Word) = BitVec.ofNat 64 2472 from rfl, st.getF hpre (by addr_omega [hb1]) (fun i hi ↦ nW 2472 (by omega) i (by omega))
        fun hf ↦ hf.elim]
      exact P.m184
    pp := by
      have := st.mono
      simp only [NewBuf] at hppb ⊢
      exact ⟨hppb.1, Or.inr ⟨by rcases hppb.2 with h0 | h0 <;> omega, by omega⟩⟩
    powers := by
      rw [st.eListH hpre stW (by omega), P.powers, e152]
    tgt := by
      rw [e1704, st.eListH hpre stW (by addr_omega [hPPn]), P.target]
    sample := fun T hT ↦ by
      obtain ⟨T', e, hT'⟩ := P.sample T hT
      have ptr : v.getMem (tp s) = s.getReg .x13 := by
        have etp : tp s = s.getReg .x2 - BitVec.ofNat 64 2448 := rfl
        rw [etp, R.get (keep_slot hpre (by omega)), ← etp]; exact h.proofPtr
      refine ⟨T', by rw [e, e152], st.transcript hpre R.inv ptr (fun a ha ↦ ⟨(WA a ha).1, by
        rw [tp]; rcases ha with rfl | rfl | rfl <;> addr_omega [hb1]⟩) hT'⟩ }⟩

/-- A buffer `walk` allocated before `u₀`, read only for `table_sumcheck`. -/
theorem oldRO {s u₀ w : MachineState} (hpre : WalkPre s) (h : Inv s w)
    (hm : heapNext u₀ ≤ heapNext w) {ws : List (Word × Nat)}
    (hws : ∀ x ∈ ws, (s.getReg .x2 - 2656).toNat ≤ x.1.toNat) {p : Word} {n : Nat}
    (ho : Old s u₀ p n) : RO w tableSumcheckStack ws (tp s) p n := by
  have hl := hpre.heap.lo
  obtain ⟨h1, h2, h3⟩ := ho
  exact ro_heap hpre h (by decide) hws h1 (by omega)
    (h3.imp id fun h' ↦ by simp only [heapStart, heapNext] at hl h' ⊢; omega)

set_option maxRecDepth 8192 in
theorem tsPre {OI : MachineState → Word → List (List Opening) → Prop}
    {s u₀ w : MachineState} {layout : LayoutMirror.LayoutRust} {rows : List (BitVec 64)}
    {lir : BitVec 64} {bus : BusResultRust} {PP : Word} (hpre : WalkPre s)
    (h : AtR17 OI s u₀ layout rows lir bus) (A : AtTS s u₀ w bus PP) : TableSumcheckPre w := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have I := A.rest.inv
  have sp := I.sp
  have etp : tp s = s.getReg .x2 - BitVec.ofNat 64 2448 := rfl
  have ptr : w.getMem (tp s) = s.getReg .x13 := by
    rw [etp, A.rest.get (keep_slot hpre (by omega)), ← etp]; exact h.proofPtr
  have m₀ := A.rest.mono
  have hws : ∀ x ∈ tsWrites w, (s.getReg .x2 - 2656).toNat ≤ x.1.toNat := by
    intro x hx
    simp only [tsWrites, A.x10, A.target, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> addr_omega [hb1]
  have T928 := tfacts hpre I ptr (m := tableSumcheckStack) (by decide) (c := 928) (k := 928)
    (n := 24) rfl (by omega) (by omega) (by omega)
  have T1704 := tfacts hpre I ptr (m := tableSumcheckStack) (by decide) (c := 1704) (k := 1704)
    (n := 24) rfl (by omega) (by omega) (by omega)
  have F928 := fr_ok hpre I (m := tableSumcheckStack) (c := 928) (k := 928) (n := 24) rfl
    (by omega) (by omega) (by decide)
  have F1704 := fr_ok hpre I (m := tableSumcheckStack) (c := 1704) (k := 1704) (n := 24) rfl
    (by omega) (by omega) (by decide)
  have F2656 := fr_ok hpre I (m := tableSumcheckStack) (c := 2656) (k := 2656) (n := 24) rfl
    (by omega) (by omega) (by decide)
  have LI := h.layoutIn
  have FO := h.forms
  have fb := h.formsBuf
  obtain ⟨fb1, fb2, -⟩ := fb
  have e848 : vecPtr u₀ (s.getReg .x2 - 856) = u₀.getMem (s.getReg .x2 - 848) := by
    rw [vecPtr]; congr 1; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have e840 : vecLen u₀ (s.getReg .x2 - 856) = u₀.getMem (s.getReg .x2 - 840) := by
    rw [vecLen]; congr 1; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have e872 : vecPtr u₀ (s.getReg .x2 - 880) = u₀.getMem (s.getReg .x2 - 872) := by
    rw [vecPtr]; congr 1; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have e864 : vecLen u₀ (s.getReg .x2 - 880) = u₀.getMem (s.getReg .x2 - 864) := by
    rw [vecLen]; congr 1; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  rw [e848, e840] at FO fb2
  have PO := h.pointOld
  rw [e872, e864] at PO
  have hppb := A.pp
  simp only [NewBuf] at hppb
  have hl0 := h.inv.heap.lo
  refine {
    heap := I.heap
    stack := hpre.stack.sub 2656 sp (by rw [stack_eq]; decide) (by decide) (by decide)
      (by decide) (by decide)
    rodata := I.rodata hpre
    out := by rw [A.x10]; addr_omega [hb1, hb2, hb3]
    outFree := by rw [A.x10]; exact F928.1
    outStack := by rw [A.x10]; exact F928.2.1
    outRodata := by rw [A.x10]; exact F928.2.2
    args := by
      rw [A.self, sp]
      refine ⟨Or.inr (by addr_omega [hb1, hb2, hb3]), F2656.1, F2656.2.1, fun x hx ↦ ?_,
        by rw [tp]; addr_omega [hb1]⟩
      simp only [tsWrites, A.x10, A.target, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> addr_omega [hb1]
    self := by rw [A.self]; exact tok hpre I ptr
    checked := by
      rw [A.self]
      have ha : (tp s + 360).toNat % 8 = 0 := by rw [tp]; addr_omega [hb1, hb3]
      have e360 : tp s + 360 = s.getReg .x2 - BitVec.ofNat 64 2088 := by
        rw [tp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
      have g : w.getMem (tp s + 360) = u₀.getMem (tp s + 360) := by
        rw [e360]; exact A.rest.get (keep_slot hpre (by omega))
      rw [byteAt_congr ha g, h.checked]
      decide
    selfStack := by rw [A.self]; exact T928.1
    selfOut := by rw [A.self, A.x10]; exact T928.2.1
    selfFree := by rw [A.self]; exact T928.2.2.1
    selfRodata := by rw [A.self]; exact T928.2.2.2.1
    proofStack := by rw [A.self]; exact T928.2.2.2.2.1
    proofOut := by rw [A.self, A.x10]; exact T928.2.2.2.2.2.1
    proofFree := by rw [A.self]; exact T928.2.2.2.2.2.2.1
    streamFree := by rw [A.self]; exact T928.2.2.2.2.2.2.2
    target := by rw [A.target]; addr_omega [hb1, hb2, hb3]
    targetFree := by rw [A.target]; exact F1704.1
    targetStack := by rw [A.target]; exact F1704.2.1
    targetOut := by rw [A.target, A.x10]; addr_omega [hb1]
    targetSelf := by rw [A.target, A.self, tp]; addr_omega [hb1]
    proofTarget := by rw [A.target, A.self]; exact T1704.2.2.2.2.2.1
    targetRodata := by rw [A.target]; exact F1704.2.2
    tables := by
      rw [A.x11, A.x12, A.self]
      exact oldRO hpre I m₀ hws LI.tables
    heights := by
      rw [A.x13, A.x14, A.self]
      exact oldRO hpre I m₀ hws LI.heights
    forms := by
      rw [A.x15, A.x16, A.self]
      have fbO := h.formsBuf
      rw [e848, e840] at fbO
      have hh := I.heap.hi
      have vp (a : Word) (ha : a.toNat + 24 ≤ heapNext u₀) :
          vecPtr w a = vecPtr u₀ a ∧ vecLen w a = vecLen u₀ a := by
        simp only [heapNext, heapEnd] at ha hh m₀
        exact ⟨A.old _ (by simp only [heapNext]; addr_omega [ha, hh, m₀]),
          A.old _ (by simp only [heapNext]; addr_omega [ha, hh, m₀])⟩
      have rowB (i : Nat) (hi : i < (u₀.getMem (s.getReg .x2 - 840)).toNat) :
          (u₀.getMem (s.getReg .x2 - 848) + BitVec.ofNat 64 (24 * i)).toNat + 24 ≤ heapNext u₀ := by
        have := fbO.2.1
        simp only [heapNext, heapEnd] at this hh m₀
        addr_omega [this, hi, hh, m₀]
      refine ⟨oldRO hpre I m₀ hws fbO, fun i hi ↦ ?_, fun i hi j hj ↦ ?_⟩
      · obtain ⟨e1, e2⟩ := vp _ (rowB i hi)
        rw [e1, e2]
        exact oldRO hpre I m₀ hws (FO.forms i hi)
      · obtain ⟨e1, e2⟩ := vp _ (rowB i hi)
        rw [e2] at hj
        rw [e1]
        have fo := FO.forms i hi
        have hb : (vecPtr u₀ (u₀.getMem (s.getReg .x2 - 848) + BitVec.ofNat 64 (24 * i)) +
            BitVec.ofNat 64 (24 * j)).toNat + 24 ≤ heapNext u₀ := by
          have := fo.2.1
          simp only [heapNext, heapEnd] at this hh m₀ ⊢
          addr_omega [this, hj, hh, m₀]
        obtain ⟨e3, e4⟩ := vp _ hb
        rw [e3, e4]
        exact oldRO hpre I m₀ hws (FO.terms i hi j hj)
    constraintPowers := by
      rw [A.x17, A.x28, A.self, show ((2 : Word)).toNat = 2 from rfl]
      exact ro_heap hpre I (by decide) hws hppb.1 (by rcases hppb.2 with h0 | h0 <;> omega)
        (Or.inr (by rcases hppb.2 with h0 | h0 <;> simp only [heapStart, heapNext] at hl0 h0 ⊢ <;> omega))
    formPowers := by
      rw [A.x29, A.x30, A.self, show ((3 : Word)).toNat = 3 from rfl]
      have hb := hppb.2
      have hh := I.heap.hi
      simp only [heapNext, heapEnd] at hb hh m₀
      exact ro_heap hpre I (by decide) hws
        (by rcases hb with h0 | h0 <;> addr_omega [hppb.1, h0, hh, m₀])
        (by rcases hppb.2 with h0 | h0 <;> addr_omega [h0])
        (Or.inr (by rcases hppb.2 with h0 | h0 <;> simp only [heapStart, heapNext] at hl0 h0 ⊢ <;>
          addr_omega [h0, hl0]))
    equalityPoint := by
      rw [A.x31, A.eqLen, A.self]
      exact oldRO hpre I m₀ hws PO }

end Rv64Verifier.Proofs.Walk
