import Rv64Verifier.Proofs.Gkr.KeccakStart

/-!
# `keccak::verify_keccak`: the prologue, the sizes' check, the segment's point

The registers saved, the sizes checked (`Err` returned when they do not fit, `sizes_err`), the
segment count `24 / 12 = 2` and its `log2_ceil`, `samples(1)` into `f + 80` (`to_seg`).
-/

namespace Rv64Verifier.Gkr.Keccak
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Model.Gkr Rv64Verifier.Transcript Rv64Verifier.Contracts
  Rv64Verifier.Gkr Rv64Verifier.Blocks.F35
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

attribute [local rv_addr] vecPtr vecLen vecCap

/-- The function's outcome: returned with its contract, or a dead end. -/
def Done (s t : MachineState) : Prop :=
  (t.pc = returnAddress s ∧ Preserves s t ∧ VerifyKeccakPostW s t) ∨ Dead Image.code t

/-- After the prologue. -/
structure P0 (s u : MachineState) : Prop where
  base : Base s u
  x8 : u.getReg .x8 = s.getReg .x11
  keeps : ∀ r ∈ ([.x9, .x10, .x13, .x14, .x15, .x16] : List Reg), u.getReg r = s.getReg r
  tat : ∀ T, TranscriptAt s (s.getReg .x11) T → TranscriptAt u (s.getReg .x11) T

/-- The sizes fit. -/
def OK (s : MachineState) : Prop := s.getReg .x15 = s.getReg .x12 ∧ 4 ≤ (s.getReg .x12).toNat

theorem prologue {s : MachineState} (hpre : VerifyKeccakPreW s) (hpc : s.pc = 0x80008e34) :
    ∃ u, Reaches Image.code s u ∧ P0 s u ∧ (OK s → u.pc = 0x80008e8c) ∧
      (¬ OK s → u.pc = 0x80009154) := by
  have hb := bounds hpre
  have hnx := hpre.stack.next
  obtain ⟨t₀, hr₀, h₀⟩ := Sym.BlockSpec.reaches b80008e34_spec hpc (by
    rv_eval []
    and_intros <;> valid_access hpre.stack.valid [hb])
  have k₀ := b80008e34_keeps h₀
  have f₀ := b80008e34_frame h₀ (by omega)
  have x2₀ := b80008e34_x2 h₀
  have hN₀ : t₀.getMem nextAddr = s.getMem nextAddr := f₀ _ (by
    unfold verifyKeccakStack at hb hnx; addr_omega [hb, hnx])
  have hH₀ : HeapOk t₀ := ⟨by simp only [heapNext, hN₀]; exact hpre.heap.lo,
    by simp only [heapNext, hN₀]; exact hpre.heap.hi⟩
  have F₀ : DFrame s t₀ (KW s t₀) := (DFrame.of_memFrame f₀).mono fun a h ↦
    Or.inr (Or.inr (Or.inl (by unfold verifyKeccakStack at hb; addr_omega [h, hb])))
  have pc₀ := h₀.pc
  rv_eval [] at pc₀
  refine ⟨t₀, hr₀, {
    base := {
      x2 := x2₀
      saved := {
        ra := b80008e34_m_x2_n8 h₀
        s0 := b80008e34_m_x2_n16 h₀
        s1 := b80008e34_m_x2_n24 h₀
        s2 := b80008e34_m_x2_n32 h₀
        s3 := b80008e34_m_x2_n40 h₀
        s4 := b80008e34_m_x2_n48 h₀
        s5 := b80008e34_m_x2_n56 h₀
        s6 := b80008e34_m_x2_n64 h₀
        s7 := b80008e34_m_x2_n72 h₀
        s8 := b80008e34_m_x2_n80 h₀
        s9 := b80008e34_m_x2_n88 h₀
        s10 := b80008e34_m_x2_n96 h₀
        s11 := b80008e34_m_x2_n104 h₀ }
      heap := hH₀
      mono := by simp only [heapNext, hN₀]; exact le_refl _
      frame := F₀ }
    x8 := b80008e34_x8 h₀
    keeps := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> exact k₀ _ (by decide)
    tat := fun T hT ↦ ?_ }, ?_⟩
  · have hS := hpre.self.self
    have hss := hpre.selfStack
    obtain ⟨r1, r2, r3⟩ := readsKW hpre hH₀
    unfold verifyKeccakStack at hb hss
    refine (DFrame.of_memFrame f₀).transcriptAt hT hpre.self
      (fun y hy h ↦ r1 y hy (Or.inr (Or.inr (Or.inl (by addr_omega [h, hb])))))
      (fun y hy h ↦ r2 y hy (Or.inr (Or.inr (Or.inl (by addr_omega [h, hb])))))
      (fun y hy h ↦ r3 y hy (Or.inr (Or.inr (Or.inl (by addr_omega [h, hb])))))
      fun y hy h ↦ by addr_omega [hy, h, hb, hss, hS]
  refine ⟨fun hok ↦ ?_, fun hok ↦ ?_⟩
  · have h2 : (s.getReg .x12).ult 4 = false := by
      rw [BitVec.ult, decide_eq_false_iff_not]; show ¬ (s.getReg .x12).toNat < 4; exact hok.2.not_gt
    rw [pc₀]
    simp only [hok.1, BitVec.xor_self, h2]
    decide
  · rw [pc₀]
    by_cases h1 : s.getReg .x15 = s.getReg .x12
    · have h2 : (s.getReg .x12).ult 4 = true := by
        rw [BitVec.ult, decide_eq_true_eq]; show (s.getReg .x12).toNat < 4
        exact Nat.lt_of_not_le fun h ↦ hok ⟨h1, h⟩
      simp only [h1, BitVec.xor_self, h2]
      decide
    · have hne : s.getReg .x15 ^^^ s.getReg .x12 ≠ 0 := fun h ↦ h1 (by
        have := congrArg (· ^^^ s.getReg .x12) h
        simpa [BitVec.xor_assoc] using this)
      have h0 : BitVec.ult 0 (s.getReg .x15 ^^^ s.getReg .x12) = true := by
        rw [BitVec.ult, decide_eq_true_eq]
        show 0 < (s.getReg .x15 ^^^ s.getReg .x12).toNat
        exact Nat.pos_of_ne_zero fun h ↦ hne (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
      simp only [h0]
      by_cases h3 : (s.getReg .x12).ult 4 = true <;> simp only [h3] <;> decide

/-- The sizes do not fit: `Err` returned. -/
theorem sizes_err {s u : MachineState} (hpre : VerifyKeccakPreW s) (P : P0 s u)
    (hpc : u.pc = 0x80009154) (hbad : ¬ OK s) :
    ∃ t, Reaches Image.code u t ∧ Done s t := by
  have hb := bounds hpre
  have ho := hpre.out
  have hos := hpre.outStack
  have B := P.base
  have x10 : u.getReg .x10 = s.getReg .x10 := P.keeps .x10 (by decide)
  obtain ⟨w, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80009154_spec hpc (by
    rv_eval [x10]
    and_intros <;> (refine Region.valid ho ?_ ?_ ?_ <;> addr_omega [ho]))
  have m0 := b80009154_m_x10_0 h₁
  have f₁ := b80009154_frame h₁ (by rw [x10]; addr_omega [ho])
  rw [x10] at m0 f₁
  have hN : w.getMem nextAddr = u.getMem nextAddr := f₁ _ (by addr_omega [ho, hpre.outFree])
  have Bw : Base s w := B.next hpre ((b80009154_keeps h₁ .x2 (by decide)).trans B.x2)
    ⟨by simp only [heapNext, hN]; exact B.heap.lo, by simp only [heapNext, hN]; exact B.heap.hi⟩
    (by simp only [heapNext, hN]; exact le_refl _) (DFrame.of_memFrame f₁) fun a ha ↦
      ⟨Or.inl (by addr_omega [ha]), by unfold verifyKeccakStack at hb hos; addr_omega [ha, hos, hb]⟩
  obtain ⟨t, hr₂, pc, pres, same⟩ := exit hpre (b80009154_pc h₁) Bw.x2 Bw.saved
  refine ⟨t, hr₁.trans hr₂, Or.inl ⟨pc, pres, post_err Bw m0 ?_ same⟩⟩
  refine (rest_start hpre).require_fail fun h ↦ hbad ⟨?_, ?_⟩
  · have := h.1
    simp only [instOf, eListAt_length, kInstLen] at this
    exact BitVec.eq_of_toNat_eq this
  · exact h.2.2

/-- Back from `samples(1)`: the segment's point at `f + 80`. -/
structure A1 (s u : MachineState) : Prop where
  pc : u.pc = 0x80008f7c
  base : Base s u
  ok : OK s
  x8 : u.getReg .x8 = s.getReg .x11
  x9 : u.getReg .x9 = s.getReg .x14
  x18 : u.getReg .x18 = s.getReg .x12
  x19 : u.getReg .x19 = 12
  m40 : u.getMem (s.getReg .x2 - 5208) = s.getReg .x16
  m48 : u.getMem (s.getReg .x2 - 5200) = s.getReg .x10
  m64 : u.getMem (s.getReg .x2 - 5184) = 2
  seg : NewVecE s u (s.getReg .x2 - 5168) (vecEs u (s.getReg .x2 - 5168))
  segLen : (vecEs u (s.getReg .x2 - 5168)).length = 1
  rest : Rest s u (kSeg (s.getReg .x12).toNat (instOf s) (outOf s) (vecEs u (s.getReg .x2 - 5168)))

theorem to_seg (hS : SamplesSpec) {s u : MachineState} (hpre : VerifyKeccakPreW s) (P : P0 s u)
    (hok : OK s) (hpc : u.pc = 0x80008e8c) :
    ∃ v, Reaches Image.code u v ∧ (A1 s v ∨ Dead Image.code v) := by
  have hb := bounds hpre
  have B := P.base
  have x13 : u.getReg .x13 = 12 := (P.keeps .x13 (by decide)).trans hpre.depth
  -- `depth != 0`
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80008e8c_spec hpc trivial
  have pc₁ := b80008e8c_pc_not_taken h₁ (by rw [x13]; decide)
  have k₁ := b80008e8c_keeps h₁
  have B₁ := B.same ((k₁ .x2 (by decide)).trans B.x2) (b80008e8c_mem_same h₁)
  have x19₁ : u₁.getReg .x19 = 12 := (b80008e8c_x19 h₁).trans x13
  -- `24 / depth` and the segment bits
  obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80008e94_spec pc₁ (by
    rv_eval [B₁.x2]
    and_intros <;> valid_access hpre.stack.valid [hb])
  have pc₂ : u₂.pc = 0x80008ec0 := h₂.pc_eq (by rv_eval [x19₁]; decide)
  have x11₂ : u₂.getReg .x11 = 1 := h₂.reg_eq .x11 rfl (by rv_eval [x19₁]; decide)
  have m64₂ : u₂.getMem (u₁.getReg .x2 + 64) = 2 :=
    h₂.mem_eq 0 (by decide) (by rv_eval []) (by rv_eval [x19₁]; decide)
  have m48₂ := b80008e94_m_x2_48 h₂
  have k₂ := b80008e94_keeps h₂
  have f₂ := b80008e94_frame h₂ (by rw [B₁.x2]; addr_omega [hb])
  rw [B₁.x2] at f₂ m48₂ m64₂
  rv_eval [] at f₂ m48₂ m64₂
  have B₂ := B₁.slots hpre ((k₂ .x2 (by decide)).trans B₁.x2) f₂ (by addr_omega [hb])
    (by addr_omega [hb])
  -- `log2_ceil`
  obtain ⟨u₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80008ec0_spec pc₂ trivial
  have x12₃ : u₃.getReg .x12 = 63 := h₃.reg_eq .x12 rfl (by rv_eval [x11₂]; decide)
  have k₃ := b80008ec0_keeps h₃
  have m₃ := b80008ec0_mem_same h₃
  have B₃ := B₂.same ((k₃ .x2 (by decide)).trans B₂.x2) m₃
  -- `samples(1)`
  obtain ⟨u₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b80008f64_spec (b80008ec0_pc h₃) (by
    rv_eval [B₃.x2]
    valid_access hpre.stack.valid [hb])
  have k₄ := b80008f64_keeps h₄
  have f₄ := b80008f64_frame h₄ (by rw [B₃.x2]; addr_omega [hb])
  have m40₄ := b80008f64_m_x2_40 h₄
  rw [B₃.x2] at f₄ m40₄
  rv_eval [] at f₄ m40₄
  have B₄ := B₃.slots hpre ((k₄ .x2 (by decide)).trans B₃.x2) f₄ (by addr_omega [hb])
    (by addr_omega [hb])
  have x10₄ : u₄.getReg .x10 = s.getReg .x2 - 5168 := by
    rw [b80008f64_x10 h₄, B₃.x2]; rv_eval []
  have x11₄ : u₄.getReg .x11 = s.getReg .x11 := by
    rw [b80008f64_x11 h₄, k₃ .x8 (by decide), k₂ .x8 (by decide), k₁ .x8 (by decide), P.x8]
  have x12₄ : u₄.getReg .x12 = 1 := by
    rw [b80008f64_x12 h₄, x12₃, k₃ .x10 (by decide), b80008e94_x10 h₂]; decide
  have hsp : SamplesPre u₄ := B₄.tpre hpre 5168 x10₄ x11₄ (by decide) (by decide) (by decide)
    (by decide) (by decide)
  obtain ⟨v, hr₅, ⟨hpc₅, hpres₅, hpost₅⟩ | hd⟩ :=
    hS.call (hr₁.trans (hr₂.trans (hr₃.trans hr₄))) (b80008f64_pc h₄) hsp
  swap
  · exact ⟨v, hr₅, Or.inr hd⟩
  have x2₅ : v.getReg .x2 = s.getReg .x2 - 5248 := (hpres₅.reg .x2).trans B₄.x2
  have F₅ : DFrame u₄ v (SW s u₄ v [(5168, 24)] true) := DFrame.mono hpost₅.frame
    fun a ha ↦ tframe_sw hpre 5168 B₄.x2 x10₄ x11₄ (by decide) a ha
  have B₅ := B₄.step hpre x2₅ hpost₅.heap hpost₅.mono (by decide) F₅
  have keep (J : Nat) (hJ : J ≤ 5248) (h8 : 8 ≤ J) (hsep : SlotsSep [(5168, 24)] J 8 = true) :=
    SW.mem hpre hpost₅.heap (by decide) hJ h8 hsep F₅
  have T₄ : ∀ T, TranscriptAt s (s.getReg .x11) T → TranscriptAt u₄ (s.getReg .x11) T :=
    fun T hT ↦ B₃.slots_tat hpre B₄ f₄ (by addr_omega [hb]) (by addr_omega [hb])
      (Layer.transcriptAt_congr m₃ (B₁.slots_tat hpre B₂ f₂ (by addr_omega [hb])
        (by addr_omega [hb]) (Layer.transcriptAt_congr (b80008e8c_mem_same h₁) (P.tat T hT))))
  have R₄ : Rest s u₄ (kMain (s.getReg .x12).toNat (instOf s) (outOf s)) :=
    ((rest_start hpre).require_pass ⟨by
      simp only [instOf, eListAt_length, kInstLen]; rw [hok.1], by
      simp only [outOf, eListAt_length], hok.2⟩).keep T₄
  obtain ⟨T₀, hT₀⟩ := Open.exists_T u₄ (s.getReg .x11)
  have hv₀ := hpost₅.value T₀ (by rw [x11₄]; exact hT₀)
  obtain ⟨xs₀, T₀', hrun₀, hvec₀, -⟩ := hv₀
  rw [x10₄] at hvec₀
  have hseg := hvec₀.elems
  refine ⟨v, hr₅, Or.inl {
    pc := by rw [hpc₅, returnAddress_eq, b80008f64_x1 h₄]; decide
    base := B₅
    ok := hok
    x8 := by rw [hpres₅.reg .x8, k₄ .x8 (by decide), k₃ .x8 (by decide), k₂ .x8 (by decide),
      k₁ .x8 (by decide), P.x8]
    x9 := by rw [hpres₅.reg .x9, k₄ .x9 (by decide), k₃ .x9 (by decide), b80008e94_x9 h₂,
      k₁ .x14 (by decide), P.keeps .x14 (by decide)]
    x18 := by rw [hpres₅.reg .x18, k₄ .x18 (by decide), k₃ .x18 (by decide), b80008e94_x18 h₂,
      k₁ .x15 (by decide), P.keeps .x15 (by decide), hok.1]
    x19 := by rw [hpres₅.reg .x19, k₄ .x19 (by decide), k₃ .x19 (by decide), k₂ .x19 (by decide),
      x19₁]
    m40 := (keep 5208 (by decide) (by decide) (by decide)).trans (m40₄.trans (by
      rw [k₃ .x16 (by decide), k₂ .x16 (by decide), k₁ .x16 (by decide), P.keeps .x16 (by decide)]))
    m48 := (keep 5200 (by decide) (by decide) (by decide)).trans ((f₄ _ (by addr_omega [hb])).trans
      ((m₃ _).trans (m48₂.trans (by rw [k₁ .x10 (by decide), P.keeps .x10 (by decide)]))))
    m64 := (keep 5184 (by decide) (by decide) (by decide)).trans ((f₄ _ (by addr_omega [hb])).trans
      ((m₃ _).trans m64₂))
    seg := by rw [hseg]; exact Open.newVecE_mono hvec₀ B₄.mono
    segLen := by rw [hseg]; exact Returns.samples _ _ _ _ (by rw [x12₄] at hrun₀; exact hrun₀)
    rest := R₄.step fun T hT ↦ ?_ }⟩
  obtain ⟨xs, T', hrun, hvec, hT'⟩ := hpost₅.value T (by rw [x11₄]; exact hT)
  rw [x10₄] at hvec
  rw [x12₄] at hrun
  rw [x11₄] at hT'
  exact ⟨T', by rw [hvec.elems]; exact hrun, hT'⟩

end Rv64Verifier.Gkr.Keccak
