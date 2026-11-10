import Rv64Verifier.Proofs.Gkr.LayerStart

/-!
# `keccak::verify_layer`: the prologue and the product's coefficients

The registers saved, `next_scalars(47)` into `f + 960` (`to_scalars`); its `Err` returned
(`scalars_err`), its `Ok` the product at `0x8000f0c0` (`scalars_ok`).
-/

namespace Rv64Verifier.Gkr.Layer
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Model.Gkr Rv64Verifier.Transcript Rv64Verifier.Contracts
  Rv64Verifier.Gkr Rv64Verifier.Blocks.F74
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

attribute [local rv_addr] vecPtr vecLen vecCap

theorem nextScalars_length {n : Nat} {T T' : TState} {xs : List E}
    (h : (TM.nextScalars n).run T = some (xs, T')) : xs.length = n := by
  induction n generalizing T T' xs with
  | zero => cases (Option.some.inj h : ([], T) = (xs, T')); rfl
  | succ n ih =>
    simp only [TM.nextScalars, StateT.run_bind] at h
    generalize hx : TM.nextScalar.run T = o at h
    rcases o with _ | ⟨x, T₁⟩
    · simp at h
    · simp only [Option.bind_eq_bind, Option.bind_some] at h
      generalize hy : (TM.nextScalars n).run T₁ = o' at h
      rcases o' with _ | ⟨ys, T₂⟩
      · simp at h
      · simp only [Option.bind_some, StateT.run_pure] at h
        cases (Option.some.inj h : (x :: ys, T₂) = (xs, T'))
        rw [List.length_cons, ih hy]

/-- Back from the first `next_scalars`. -/
structure N1 (s u : MachineState) : Prop where
  pc : u.pc = 0x8000f0ac
  base : Base s u
  x8 : u.getReg .x8 = s.getReg .x10
  x9 : u.getReg .x9 = s.getReg .x13
  x19 : u.getReg .x19 = s.getReg .x15
  x20 : u.getReg .x20 = s.getReg .x11
  x22 : u.getReg .x22 = s.getReg .x14
  x24 : u.getReg .x24 = s.getReg .x12
  result : ∀ T, TranscriptAt s (s.getReg .x11) T →
    match (TM.nextScalars productBits).run T with
    | some (xs, T') => ¬ vecCap u (s.getReg .x2 - 752) = errNiche ∧
        (NewVecE s u (s.getReg .x2 - 752) xs ∧ TranscriptAt u (s.getReg .x11) T')
    | none => vecCap u (s.getReg .x2 - 752) = errNiche

theorem to_scalars (hNS : NextScalarsSpec) {s : MachineState} (hpre : VerifyLayerPre s)
    (hpc : s.pc = 0x8000f04c) : ∃ u, Reaches Image.code s u ∧ (N1 s u ∨ Dead Image.code u) := by
  have hb := bounds hpre
  have hnx := hpre.stack.next
  have hS := hpre.self.self
  have hss := hpre.selfStack
  obtain ⟨t₀, hr₀, h₀⟩ := Sym.BlockSpec.reaches b8000f04c_spec hpc (by
    rv_eval []
    and_intros <;> valid_access hpre.stack.valid [hb])
  have k₀ := b8000f04c_keeps h₀
  have f₀ := b8000f04c_frame h₀ (by omega)
  have x2₀ := b8000f04c_x2 h₀
  have hN₀ : t₀.getMem nextAddr = s.getMem nextAddr := f₀ _ (by
    unfold verifyLayerStack at hb hnx; addr_omega [hb, hnx])
  have hH₀ : HeapOk t₀ := ⟨by simp only [heapNext, hN₀]; exact hpre.heap.lo,
    by simp only [heapNext, hN₀]; exact hpre.heap.hi⟩
  have F₀ : DFrame s t₀ (LW s t₀) := (DFrame.of_memFrame f₀).mono fun a h ↦
    Or.inr (Or.inr (Or.inl (by unfold verifyLayerStack at hb; addr_omega [h, hb])))
  have B₀ : Base s t₀ := {
    x2 := x2₀
    saved := {
      ra := b8000f04c_m_x2_n8 h₀
      s0 := b8000f04c_m_x2_n16 h₀
      s1 := b8000f04c_m_x2_n24 h₀
      s2 := b8000f04c_m_x2_n32 h₀
      s3 := b8000f04c_m_x2_n40 h₀
      s4 := b8000f04c_m_x2_n48 h₀
      s5 := b8000f04c_m_x2_n56 h₀
      s6 := b8000f04c_m_x2_n64 h₀
      s7 := b8000f04c_m_x2_n72 h₀
      s8 := b8000f04c_m_x2_n80 h₀
      s9 := b8000f04c_m_x2_n88 h₀
      s10 := b8000f04c_m_x2_n96 h₀
      s11 := b8000f04c_m_x2_n104 h₀ }
    heap := hH₀
    mono := by simp only [heapNext, hN₀]; exact le_refl _
    frame := F₀ }
  have x10₀ : t₀.getReg .x10 = s.getReg .x2 - BitVec.ofNat 64 752 := b8000f04c_x10 h₀
  have x11₀ : t₀.getReg .x11 = s.getReg .x11 := k₀ .x11 (by decide)
  have hns : NextScalarsPre t₀ :=
    B₀.tpre hpre 752 x10₀ x11₀ (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨u, hr₁, ⟨hpc₁, hpres₁, hpost₁⟩ | hd⟩ := hNS.call hr₀ (b8000f04c_pc h₀) hns
  swap
  · exact ⟨u, hr₁, Or.inr hd⟩
  have x2u : u.getReg .x2 = s.getReg .x2 - 1712 := (hpres₁.reg .x2).trans x2₀
  have B₁ : Base s u := B₀.next hpre x2u hpost₁.heap hpost₁.mono hpost₁.frame fun a ha ↦
    tframe_lw hpre B₀ 752 x10₀ x11₀ (by decide) (by decide) (by decide) hpost₁.heap a ha
  refine ⟨u, hr₁, Or.inl {
    pc := by rw [hpc₁, returnAddress_eq, b8000f04c_x1 h₀]; decide
    base := B₁
    x8 := by rw [hpres₁.reg .x8, b8000f04c_x8 h₀]
    x9 := by rw [hpres₁.reg .x9, b8000f04c_x9 h₀]
    x19 := by rw [hpres₁.reg .x19, b8000f04c_x19 h₀]
    x20 := by rw [hpres₁.reg .x20, b8000f04c_x20 h₀]
    x22 := by rw [hpres₁.reg .x22, b8000f04c_x22 h₀]
    x24 := by rw [hpres₁.reg .x24, b8000f04c_x24 h₀]
    result := fun T hT ↦ ?_ }⟩
  have hT₀ : TranscriptAt t₀ (s.getReg .x11) T := by
    obtain ⟨r1, r2, r3⟩ := readsLW hpre hH₀
    refine (DFrame.of_memFrame f₀).transcriptAt hT hpre.self (fun y hy h ↦ r1 y hy (by
      unfold verifyLayerStack at hb; exact Or.inr (Or.inr (Or.inl (by addr_omega [h, hb])))))
      (fun y hy h ↦ r2 y hy (by
        unfold verifyLayerStack at hb; exact Or.inr (Or.inr (Or.inl (by addr_omega [h, hb])))))
      (fun y hy h ↦ r3 y hy (by
        unfold verifyLayerStack at hb; exact Or.inr (Or.inr (Or.inl (by addr_omega [h, hb])))))
      fun y hy h ↦ by unfold verifyLayerStack at hb hss; addr_omega [hy, h, hb, hss, hS]
  have hv := hpost₁.value T (by rw [x11₀]; exact hT₀)
  rw [x10₀, x11₀, b8000f04c_x12 h₀] at hv
  have e47 : ((47 : Word).toNat) = productBits := rfl
  rw [e47] at hv
  have hm : heapNext s = heapNext t₀ := by simp only [heapNext, hN₀]
  generalize (TM.nextScalars productBits).run T = o at hv ⊢
  rcases o with _ | ⟨xs, T'⟩
  · exact hv
  · exact ⟨hv.1, Open.newVecE_mono hv.2.1 (le_of_eq hm), hv.2.2⟩

/-- `next_scalars` failed: the `Err` copied out, return. -/
theorem scalars_err {s u : MachineState} (hpre : VerifyLayerPre s) (N : N1 s u)
    (herr : vecCap u (s.getReg .x2 - 752) = errNiche) :
    ∃ t, Reaches Image.code u t ∧ t.pc = returnAddress s ∧ Preserves s t ∧
      VerifyLayerPost s t := by
  have hb := bounds hpre
  have ho := hpre.out
  have hos := hpre.outStack
  have B := N.base
  obtain ⟨v, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000f0ac_spec N.pc (by
    rv_eval [B.x2]
    and_intros <;> valid_access hpre.stack.valid [hb])
  have k₁ := b8000f0ac_keeps h₁
  have hm₁ := b8000f0ac_mem_same h₁
  have x8₁ : v.getReg .x8 = s.getReg .x10 := (k₁ .x8 (by decide)).trans N.x8
  obtain ⟨w, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000f708_spec
    (b8000f0ac_pc_taken h₁ (by rw [B.x2]; rv_eval []; exact herr)) (by
      rv_eval [x8₁]
      and_intros <;> (refine Region.valid ho ?_ ?_ ?_ <;> addr_omega [ho]))
  have m0 := b8000f708_m_x8_0 h₂
  have f₂ := b8000f708_frame h₂ (by rw [x8₁]; addr_omega [ho])
  rw [x8₁, b8000f0ac_x10 h₁] at m0
  rw [x8₁] at f₂
  have Bv : Base s v := B.same ((k₁ .x2 (by decide)).trans B.x2) hm₁
  have Bw : Base s w := Bv.next hpre ((b8000f708_keeps h₂ .x2 (by decide)).trans Bv.x2)
    (by
      have hN : w.getMem nextAddr = v.getMem nextAddr := f₂ _ (by addr_omega [ho, hpre.outFree])
      exact ⟨by simp only [heapNext, hN]; exact Bv.heap.lo, by simp only [heapNext, hN]; exact Bv.heap.hi⟩)
    (by simp only [heapNext]; rw [f₂ _ (by addr_omega [ho, hpre.outFree])])
    (DFrame.of_memFrame f₂) fun a ha ↦
      ⟨Or.inl (by addr_omega [ha]), by unfold verifyLayerStack at hb hos; addr_omega [ha, hos, hb]⟩
  obtain ⟨t, hr₃, pc, pres, same⟩ := exit hpre (b8000f708_pc h₂) Bw.x2 Bw.saved
  refine ⟨t, hr₁.trans (hr₂.trans hr₃), pc, pres, post_err Bw m0 ?_ same⟩
  intro T hT
  have e := N.result T hT
  simp only [mir]
  rw [verifyLayerRust_eq]
  generalize hx : (TM.nextScalars productBits).run T = o at e
  rcases o with _ | ⟨xs, T'⟩
  · exact run_bind_none hx
  · exact absurd herr e.1

end Rv64Verifier.Gkr.Layer
