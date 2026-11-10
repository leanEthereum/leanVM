import Rv64Verifier.Proofs.Walk.R18H

/-!
# `walk` R18, the table claims: `0x80003878`, `0x8000387c`, `0x8000383c`
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.Verifier Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript
  Rv64Verifier.Blocks.F4 Rv64Verifier.Bus
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

section Outer
variable {OI : MachineState → Word → List (List Opening) → Prop} {s u₀ w t u : MachineState}
  {layout : LayoutMirror.LayoutRust} {rows : List (BitVec 64)} {lir : BitVec 64}
  {bus : BusResultRust} {evs : List (List E × List E)} {k : Nat} {P C L : Word}

/-- Room for table `k`'s values: an empty table is done, else on to `0x8000387c`. -/
theorem tab3878 (hpre : WalkPre s) (T : TabR18 OI s u₀ w t u layout rows lir bus evs k P C L)
    (hpc : u.pc = 0x80003878) (hroom : (evs.getD k ([], [])).2.length ≤ C.toNat - L.toNat) :
    ∃ v, Reaches Image.code u v ∧
      ((TabR18 OI s u₀ w t v layout rows lir bus evs k P C L ∧ v.pc = 0x8000387c ∧
        L.toNat + (evs.getD k ([], [])).2.length ≤ C.toNat ∧ 0 < (evs.getD k ([], [])).2.length) ∨
      EndR18 OI s u₀ w t v layout rows lir bus evs k P C L) := by
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80003878_spec hpc (by rv_eval [])
  have m₁ := b80003878_mem_same h₁
  have k₁ := b80003878_keeps h₁
  have T₁ := T.same hpre m₁ fun r hr ↦ k₁ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  have hLC := T.len
  have hC := T.n_lt
  by_cases hn : (evs.getD k ([], [])).2.length = 0
  · have pc₁ := b80003878_pc_taken h₁ (by rw [T.x20, hn]; rfl)
    have e : bus.claims ++ tableClaimsRust (evs.take (k + 1)) =
        bus.claims ++ tableClaimsRust (evs.take k) := by
      have e0 : tableClaimsOf evs k = [] :=
        List.eq_nil_of_length_eq_zero (by rw [tableClaimsOf_length]; exact hn)
      rw [tableClaims_succ evs k T.hk.1 T.hk.2, e0, List.append_nil]
    have C₁ : CoreR18 OI s u₀ w t u₁ layout rows lir bus evs P C L.toNat
        (bus.claims ++ tableClaimsRust (evs.take (k + 1))) := by rw [e]; exact T₁.toCoreR18
    exact ⟨u₁, hr₁, Or.inr ⟨C₁, pc₁, T.hk, T₁.x8, T₁.x9, T₁.x18, T₁.x19, T₁.x21, T₁.x22, T₁.x23,
      T₁.x25⟩⟩
  · have pc₁ := b80003878_pc_not_taken h₁ (by
      rw [T.x20]; intro h0; have := congrArg BitVec.toNat h0
      addr_omega [this, hn, hroom, hC])
    exact ⟨u₁, hr₁, Or.inl ⟨T₁, pc₁, by omega, by omega⟩⟩

/-- To the inner loop's head, no value done. -/
theorem tab387c (hpre : WalkPre s) (T : TabR18 OI s u₀ w t u layout rows lir bus evs k P C L)
    (hpc : u.pc = 0x8000387c) (hroom : L.toNat + (evs.getD k ([], [])).2.length ≤ C.toNat)
    (hn : 0 < (evs.getD k ([], [])).2.length) :
    ∃ v, Reaches Image.code u v ∧ InnerR18 OI s u₀ w t v layout rows lir bus evs k 0 P C L := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  have sp := T.rest.inv.sp
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000387c_spec hpc (by
    rv_eval [sp]; valid_access hval [hb1, hb3])
  have m₁ := b8000387c_mem_same h₁
  have k₁ := b8000387c_keeps h₁
  have C₁ := T.toCoreR18.stepW hpre (StepW.same T.rest.inv.heap m₁ (k₁ .x2 (by decide))
    (fun _ ↦ False) False) (fun _ h ↦ h.elim) (fun _ h ↦ h.elim)
  have C₂ : CoreR18 OI s u₀ w t u₁ layout rows lir bus evs P C (L.toNat + 0)
      (bus.claims ++ tableClaimsRust (evs.take k) ++ (tableClaimsOf evs k).take 0) := by
    rw [List.take_zero, List.append_nil]; exact C₁
  have hC := T.n_lt
  exact ⟨u₁, hr₁, {
    toCoreR18 := C₂
    pc := b8000387c_pc h₁
    hk := T.hk
    hj := hn
    room := hroom
    x8 := by rw [k₁ .x8 (by decide), T.x8]
    x9 := by rw [k₁ .x9 (by decide), T.x9]
    x18 := by rw [k₁ .x18 (by decide), T.x18]
    x19 := by rw [k₁ .x19 (by decide), T.x19]
    x21 := by rw [k₁ .x21 (by decide), T.x21]
    x22 := by rw [k₁ .x22 (by decide), T.x22]
    x23 := by rw [k₁ .x23 (by decide), T.x23]
    x20 := by rw [k₁ .x20 (by decide), T.x20]; rfl
    x24 := by rw [k₁ .x24 (by decide), T.x24]; simp
    x25 := by rw [b8000387c_x25 h₁, T.x25, T.x20]
    x26 := by rw [k₁ .x26 (by decide), T.x26]; rfl
    x27 := by
      rw [b8000387c_x27 h₁, sp, show s.getReg .x2 - 2656 + 184 = s.getReg .x2 - 2472 by bv_omega,
        T.ptr184, T.x25]
      bv_omega
    lenSlot := by rw [m₁]; exact T.lenSlot }⟩

/-- Table `k` done: the length stored, then the next table's head or the exit. -/
theorem endStep (hpre : WalkPre s) (E : EndR18 OI s u₀ w t u layout rows lir bus evs k P C L) :
    ∃ v, Reaches Image.code u v ∧ (ExitR18 OI s u₀ w t v layout rows lir bus evs P C L ∨
      (k + 1 < 6 ∧ LoopR18 OI s u₀ w t v layout rows lir bus evs (k + 1) P C L)) := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  have sp := E.rest.inv.sp
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000383c_spec E.pc (by
    rv_eval [sp]; valid_access hval [hb1, hb3])
  have k₁ := b8000383c_keeps h₁
  have e1040 : u.getReg .x2 + 1040 = s.getReg .x2 - 1616 := by rw [sp]; bv_omega
  have fr : DFrame u u₁ (Within · (s.getReg .x2 - 1616) 8) := by
    have := DFrame.of_memFrame (b8000383c_frame h₁ (by rw [sp]; addr_omega [hb1, hb2]))
    rwa [e1040] at this
  have W₁ok : ∀ a, Within a (s.getReg .x2 - 1616) 8 → InF s a ∧ ¬ KeepR s u₀ a := fun a ha ↦
    range_ok hpre E.rest (c := 1616) (k := 1616) (n := 8) rfl (by omega) (by omega) ha
  have st : StepW s u u₁ (Within · (s.getReg .x2 - 1616) 8) False :=
    StepW.ofFrame hpre E.rest.inv.heap fr (fun a ha ↦ (W₁ok a ha).1) (k₁ .x2 (by decide))
  have C₁ := E.toCoreR18.stepW hpre st (fun a ha ↦ ⟨(W₁ok a ha).1, (W₁ok a ha).2, by
      rw [tp]; simp only [Within] at ha ⊢; addr_omega [ha, hb1]⟩)
    (fun a ha ↦ by simp only [Within] at ha ⊢; refine ⟨?_, ?_, ?_, ?_⟩ <;> addr_omega [ha, hb1])
  have ls : u₁.getMem (s.getReg .x2 - 1616) = L := by
    rw [← e1040, b8000383c_m_x2_1040 h₁, E.x25]
  have hk := E.hk
  by_cases hk1 : k + 1 = 6
  · have pc₁ := b8000383c_pc_taken h₁ (by rw [E.x18, E.x8, show k = 5 by omega]; rfl)
    rw [hk1, tableClaims_take_six] at C₁
    exact ⟨u₁, hr₁, Or.inl ⟨C₁, pc₁, by rw [b8000383c_x24 h₁, sp]; bv_omega,
      by rw [k₁ .x25 (by decide), E.x25], ls⟩⟩
  · have pc₁ := b8000383c_pc_not_taken h₁ (by
      rw [E.x18, E.x8]; intro h0; have := congrArg BitVec.toNat h0; addr_omega [this, hk, hk1])
    exact ⟨u₁, hr₁, Or.inr ⟨by omega, {
      toCoreR18 := C₁
      pc := pc₁
      hk := ⟨by omega, by omega⟩
      x8 := by rw [k₁ .x8 (by decide), E.x8]
      x9 := by rw [k₁ .x9 (by decide), E.x9]
      x18 := by rw [b8000383c_x18 h₁, E.x18]; bv_omega
      x19 := by rw [k₁ .x19 (by decide), E.x19]
      x21 := by rw [k₁ .x21 (by decide), E.x21]
      x22 := by rw [k₁ .x22 (by decide), E.x22]
      x23 := by rw [b8000383c_x23 h₁, E.x23]; bv_omega
      x24 := by rw [b8000383c_x24 h₁, sp]; bv_omega
      x25 := by rw [k₁ .x25 (by decide), E.x25]
      lenSlot := ls }⟩⟩

end Outer

end Rv64Verifier.Proofs.Walk
