import Rv64Verifier.Proofs.Pcs.RingEval

/-!
# `<RingWeight>::evaluate`: the loops and the contract

The inner loop (`innerLoop`, by `Reaches.loop` over `Inner`, its body `innerMul` then
`innerSquare`), the outer loop's tail (`outerTail`: the product added to the total), the outer
loop (`outerLoop`, over `Outer`), the epilogue (`exit`), and the contract (`ring_eval_spec`).
-/

namespace Rv64Verifier.Proofs.Pcs.RingEval
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.FieldContracts
  Rv64Verifier.Model.Pcs Rv64Verifier.Blocks.F66
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-! ## The inner loop -/

def imeasure (u : MachineState) : Nat := (u.getReg .x26).toNat - (u.getReg .x19).toNat

theorem innerLoop (hMul : MulSpec) (hSq : ESquareSpec) {s u : MachineState} {nx P : Word}
    {i : Nat} (hpre : RingEvalPre s) (hlen : s.getMem (s.getReg .x11 + 16) = s.getReg .x13)
    (hBuf : BufOk s P nx) (h0 : Inner s u nx P i 0) :
    ∃ v, Reaches Image.code u v ∧ (Done s v nx P i ∨ Dead Image.code v) := by
  refine Reaches.loop (fun v ↦ ∃ j, Inner s v nx P i j) imeasure
    (fun v ↦ Done s v nx P i ∨ Dead Image.code v) ?_ u ⟨0, h0⟩
  rintro v ⟨j, hv⟩
  obtain ⟨w, hvw, hw⟩ := innerMul hMul hpre hlen hBuf hv
  rcases hw with hd | hw
  · exact Or.inl ⟨w, hvw, Or.inr hd⟩
  obtain ⟨x, hwx, hx⟩ := innerSquare hSq hpre hlen hBuf hw
  rcases hx with hd | ⟨hj, hx⟩ | ⟨-, hx⟩
  · exact Or.inl ⟨x, hvw.trans hwx, Or.inr hd⟩
  · refine Or.inr ⟨x, hvw.trans hwx, ⟨j + 1, hx⟩, ?_⟩
    have hPr := hBuf.range.resolve_left (by omega)
    have hfit := hv.inv.fits
    simp only [imeasure]
    rw [hx.x26, hx.x19, hv.x26, hv.x19]
    simp only [nn] at hj hPr
    addr_omega [hj, hPr, hfit]
  · exact Or.inl ⟨x, hvw.trans hwx, Or.inl hx⟩

/-! ## The outer loop's tail -/

theorem outerTail {s u : MachineState} {nx P : Word} {i : Nat} (hpre : RingEvalPre s)
    (hlen : s.getMem (s.getReg .x11 + 16) = s.getReg .x13) (hd : Done s u nx P i) :
    ∃ v, Reaches Image.code u v ∧
      ((i + 1 < nc s ∧ Outer s v nx P (i + 1)) ∨ (i + 1 = nc s ∧ Exit s v nx)) := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hi := hd.lt
  have hsp := hd.inv.sp
  obtain ⟨t, hr, h⟩ := Sym.BlockSpec.reaches b8000dffc_spec hd.pc (by
    rv_eval [hsp]
    and_intros <;> valid_access hst.valid [hb])
  have k := b8000dffc_keeps h
  have hm := b8000dffc_mem_same h
  have inv := hd.inv.same hm (k .x2 (by decide)) (fun _ h ↦ by cases h)
  -- the total
  have hL := st_length (pt_length hlen) i
  have hacc : Model.limbs (st s (i + 1)).1 =
      (t.getReg .x20, t.getReg .x23, t.getReg .x22) := by
    rw [st_succ hi]
    simp only [stepW]
    rw [pass_fst _ _ _ (by rw [hL, rp_length]), rp_length,
      ← List.getD_eq_getElem _ 0 (by rw [cs_length]; exact hi), ← hd.prod, limbs_add, hd.acc,
      limbs_eAt, b8000dffc_x20 h, b8000dffc_x22 h, b8000dffc_x23 h, hsp]
    rv_eval [Prod.mk.injEq]
    exact ⟨BitVec.xor_comm _ _, BitVec.xor_comm _ _, BitVec.xor_comm _ _⟩
  have hC := Region.bounds (cs_region hpre (by omega))
  have hx21 : t.getReg .x21 = cp s + BitVec.ofNat 64 (24 * (i + 1)) := by
    rw [b8000dffc_x21 h, hd.x21]; simp only [cp, nc] at hC hi ⊢; addr_omega [hC, hi]
  by_cases hlast : i + 1 = nc s
  · obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000e0d8_spec
      (b8000dffc_pc_taken h (by
        rw [hd.x21, hd.x25]; simp only [cp, nc] at hC hlast ⊢; addr_omega [hC, hlast])) (by
        have hO := Region.bounds hpre.out.region
        rv_eval [k .x8 (by decide), hd.x8]
        and_intros <;> exact Region.valid hpre.out.region (by addr_omega [hO]) (by addr_omega [hO])
          (by addr_omega [hO]))
    have hO := Region.bounds hpre.out.region
    have k₂ := b8000e0d8_keeps h₂
    have hx8 : t.getReg .x8 = s.getReg .x10 := (k .x8 (by decide)).trans hd.x8
    have hm₂ := b8000e0d8_frame h₂ (by rw [hx8]; addr_omega [hO])
    rw [hx8] at hm₂
    have hOf := hpre.out.free
    simp only [Outside] at hOf
    have inv₂ := Inv.step' hpre inv (DFrame.of_memFrame hm₂)
      (fun a ha ↦ Or.inl (by simp only [W]; addr_omega [ha, hO]))
      (fun a ha ↦ by have := hpre.out.stack; addr_omega [ha, hO, this, hb])
      ((hm₂ _ (by addr_omega [hOf.2, hO])).trans inv.next) (Nat.le_refl _) inv.fits
      (k₂ .x2 (by decide))
    have hv := hacc
    rw [hlast] at hv
    refine ⟨t₂, hr.trans hr₂, Or.inr ⟨hlast, {
      inv := inv₂
      pc := b8000e0d8_pc h₂
      x8 := (k₂ .x8 (by decide)).trans hx8
      x20 := by rw [k₂ .x20 (by decide), hv]
      o8 := by have := b8000e0d8_m_x8_8 h₂; rw [hx8] at this; rw [this, hv]
      o16 := by have := b8000e0d8_m_x8_16 h₂; rw [hx8] at this; rw [this, hv] }⟩⟩
  · have hi1 : i + 1 < nc s := by omega
    refine ⟨t, hr, Or.inl ⟨hi1, {
      x8 := (k .x8 (by decide)).trans hd.x8
      x9 := (k .x9 (by decide)).trans hd.x9
      x18 := (k .x18 (by decide)).trans hd.x18
      x24 := (k .x24 (by decide)).trans hd.x24
      x25 := (k .x25 (by decide)).trans hd.x25
      x26 := (k .x26 (by decide)).trans hd.x26
      inv := inv
      pc := b8000dffc_pc_not_taken h (by
        rw [hd.x21, hd.x25]; simp only [cp, nc] at hC hi1 ⊢; addr_omega [hC, hi1])
      lt := hi1
      x21 := hx21
      acc := hacc
      buf := fun l hl ↦ by simp only [eAt, hm]; exact hd.buf l hl
      o8 := by rw [hm]; exact hd.o8
      o16 := by rw [hm]; exact hd.o16 }⟩⟩

/-! ## The outer loop -/

def omeasure (u : MachineState) : Nat := (u.getReg .x25).toNat - (u.getReg .x21).toNat

theorem outerLoop (hMul : MulSpec) (hSq : ESquareSpec) {s u : MachineState} {nx P : Word}
    (hpre : RingEvalPre s) (hlen : s.getMem (s.getReg .x11 + 16) = s.getReg .x13)
    (hBuf : BufOk s P nx) (h0 : Outer s u nx P 0) :
    ∃ v, Reaches Image.code u v ∧ (Exit s v nx ∨ Dead Image.code v) := by
  refine Reaches.loop (fun v ↦ ∃ i, Outer s v nx P i) omeasure
    (fun v ↦ Exit s v nx ∨ Dead Image.code v) ?_ u ⟨0, h0⟩
  rintro v ⟨i, hv⟩
  obtain ⟨w, hvw, hw⟩ := outerHead hpre hBuf hv
  obtain ⟨x, hvx, hx⟩ : ∃ x, Reaches Image.code v x ∧ (Done s x nx P i ∨ Dead Image.code x) := by
    rcases hw with hw | ⟨-, hw⟩
    · obtain ⟨x, hwx, hx⟩ := innerLoop hMul hSq hpre hlen hBuf hw
      exact ⟨x, hvw.trans hwx, hx⟩
    · exact ⟨w, hvw, Or.inl hw⟩
  rcases hx with hx | hx
  swap
  · exact Or.inl ⟨x, hvx, Or.inr hx⟩
  obtain ⟨y, hxy, hy⟩ := outerTail hpre hlen hx
  rcases hy with ⟨hi, hy⟩ | ⟨-, hy⟩
  · refine Or.inr ⟨y, hvx.trans hxy, ⟨i + 1, hy⟩, ?_⟩
    have hC := Region.bounds (cs_region hpre (by omega))
    simp only [omeasure]
    rw [hy.x25, hy.x21, hv.x25, hv.x21]
    simp only [cp, nc] at hC hi ⊢
    addr_omega [hC, hi]
  · exact Or.inl ⟨y, hvx.trans hxy, Or.inl hy⟩

/-! ## The epilogue -/

theorem exit {s u : MachineState} {nx : Word} (hpre : RingEvalPre s)
    (hlen : s.getMem (s.getReg .x11 + 16) = s.getReg .x13) (he : Exit s u nx) :
    ∃ t, Reaches Image.code u t ∧ t.pc = returnAddress s ∧ Preserves s t ∧ RingEvalPost s t := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hO := Region.bounds hpre.out.region
  have hOs := hpre.out.stack
  have hOf := hpre.out.free
  simp only [Outside] at hOf
  have hsp := he.inv.sp
  have sl := he.inv.slots
  simp only [slots, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
    and_true] at sl
  rv_eval [] at sl
  obtain ⟨s1, s8, s9, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27⟩ := sl
  obtain ⟨t, hr, h⟩ := Sym.BlockSpec.reaches b8000e0e8_spec he.pc (by
    rv_eval [hsp, he.x8]
    and_intros <;> first
      | valid_access hst.valid [hb]
      | exact Region.valid hpre.out.region (by addr_omega [hO]) (by addr_omega [hO])
          (by addr_omega [hO])
      | addr_omega [hO, hOs, hb])
  have hm := b8000e0e8_frame h (by rw [he.x8]; addr_omega [hO])
  rw [he.x8] at hm
  have pc := b8000e0e8_pc h
  have x2 := b8000e0e8_x2 h
  have x8 := b8000e0e8_x8 h
  have x9 := b8000e0e8_x9 h
  have x18 := b8000e0e8_x18 h
  have x19 := b8000e0e8_x19 h
  have x20 := b8000e0e8_x20 h
  have x21 := b8000e0e8_x21 h
  have x22 := b8000e0e8_x22 h
  have x23 := b8000e0e8_x23 h
  have x24 := b8000e0e8_x24 h
  have x25 := b8000e0e8_x25 h
  have x26 := b8000e0e8_x26 h
  have x27 := b8000e0e8_x27 h
  rv_eval [hsp, s1, s8, s9, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27] at pc x2 x8 x9 x18
  rv_eval [hsp, s19, s20, s21, s22, s23, s24, s25, s26, s27] at x19 x20 x21 x22 x23 x24 x25 x26 x27
  have m0 := b8000e0e8_m_x8_0 h
  rw [he.x8, he.x20] at m0
  have hnt : t.getMem nextAddr = nx := (hm _ (by addr_omega [hOf.2, hO])).trans he.inv.next
  have hn : heapNext t = nx.toNat := by simp only [heapNext, hnt]
  have hn' : heapNext u = nx.toNat := by simp only [heapNext, he.inv.next]
  refine ⟨t, hr, pc.trans (returnAddress_eq s).symm,
    preserves_of x2 x8 x9 x18 x19 fun r hr' ↦ ?_, {
      heap := ⟨by rw [hn]; exact Nat.le_trans hpre.heap.lo he.inv.mono, by rw [hn]; exact he.inv.fits⟩
      mono := by rw [hn]; exact he.inv.mono
      value := ?_
      frame := ?_ }⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact x20
    · exact x21
    · exact x22
    · exact x23
    · exact x24
    · exact x25
    · exact x26
    · exact x27
  · show (ringWeightAt s (s.getReg .x11)).evaluate (rp s) = _
    rw [value_eq (pt_length hlen)]
    congr 1
    symm
    apply eAt_eq_of_limbs
    rw [m0, hm _ (by addr_omega [hO]), hm _ (by addr_omega [hO]), he.o8, he.o16]
  · refine (he.inv.frame.trans (DFrame.of_memFrame hm) fun a ha ↦ Or.inl ?_).mono fun a ha ↦ ?_
    · simp only [W]; addr_omega [ha, hO]
    · rcases ha with ha | ha | ha | ha
      · exact Or.inl ha
      · exact Or.inr (Or.inl ha)
      · exact Or.inr (Or.inr (Or.inl ha))
      · exact Or.inr (Or.inr (Or.inr (by simp only [Fresh, hn, hn'] at ha ⊢; exact ha)))

/-! ## `RingWeight::evaluate` -/

/-- **`RingWeight::evaluate` meets its contract**, given `try_allocate_in`'s, `memcpy`'s, `mul`'s
and `E::square`'s. -/
theorem ring_eval_spec (hT : TryAllocZeroedSpec) (hC : Runtime.MemcpySpec 0x800126e4) (hMul : MulSpec)
    (hSq : ESquareSpec) : RingEvalSpec := by
  intro s hpc hpre
  obtain ⟨u, hsu, hu⟩ := setup hT hC hpc hpre
  rcases hu with hd | ⟨nx, P, hm⟩
  · exact ⟨u, hsu, Or.inr hd⟩
  have fin (w : MachineState) (hw : Reaches Image.code s w) (he : Exit s w nx) :
      ∃ t, Reaches Image.code s t ∧
        ((t.pc = returnAddress s ∧ Preserves s t ∧ RingEvalPost s t) ∨ Dead Image.code t) := by
    obtain ⟨t, hwt, h1, h2, h3⟩ := exit hpre hm.len he
    exact ⟨t, hw.trans hwt, Or.inl ⟨h1, h2, h3⟩⟩
  obtain ⟨v, huv, hv⟩ := start hpre hm
  rcases hv with he | ho
  · exact fin v (hsu.trans huv) he
  · obtain ⟨w, hvw, hw⟩ := outerLoop hMul hSq hpre hm.len hm.bufOk ho
    rcases hw with he | hd
    · exact fin w (hsu.trans (huv.trans hvw)) he
    · exact ⟨w, hsu.trans (huv.trans hvw), Or.inr hd⟩

end Rv64Verifier.Proofs.Pcs.RingEval

/-- info: 'Rv64Verifier.Proofs.Pcs.RingEval.ring_eval_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.RingEval.ring_eval_spec
