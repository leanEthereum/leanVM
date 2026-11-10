import Rv64Verifier.Proofs.Gkr.LayerR8

/-!
# `keccak::verify_layer`: a pack round's middle

`0x8000f644..0x8000f6d0`: the challenge `c` sampled (`duplex`, the state's first three lanes),
the message at `c` (`poly_eval`), `value = (1 + r + c) * message(c)` and `scale * (1 + r + c)`.
-/

namespace Rv64Verifier.Gkr.Layer
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Model.Gkr Rv64Verifier.Transcript
  Rv64Verifier.Contracts Rv64Verifier.Gkr Rv64Verifier.Blocks.F74
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

attribute [local rv_addr] vecPtr vecLen vecCap

theorem mem_sub {r : Reg} {l l' : List Reg} (hl : ∀ x ∈ l, x ∈ l') (hr : r ∈ l) : r ∈ l' :=
  hl r hr

/-- What the round's middle writes after the challenge: its slots and the callees' stacks. -/
@[rv_addr] def W8c (s : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x2 - 1592) 24 ∨ Within a (s.getReg .x2 - 1448) 24 ∨
    Within a (s.getReg .x2 - 752) 32 ∨ Within a (s.getReg .x2 - 128) 24 ∨
    Within a (s.getReg .x2 - 1712 - BitVec.ofNat 64 sumcheckStack) sumcheckStack

/-- The message at the challenge, at `0x8000f69c`. -/
structure Qm (s w t : MachineState) (c : E) (k : Nat) (acc : E × E × List E) (msg : List E)
    (ch : E) : Prop where
  pc : t.pc = 0x8000f69c
  base : Base s t
  mono : heapNext w ≤ heapNext t
  frame : DFrame w t (W8 s w t)
  x19 : t.getReg .x19 = s.getMem (s.getReg .x15 + 32) + BitVec.ofNat 64 (24 * k)
  regs : ∀ r ∈ [Reg.x9, .x23, .x26], t.getReg r = w.getReg r
  chL : limbs ch = (t.getReg .x18, t.getReg .x25, t.getReg .x20)
  oneL : limbs (1 + rOf s k + ch) = (t.getReg .x27, t.getReg .x8, t.getReg .x24)
  one : eAt t (s.getReg .x2 - 128) = 1 + rOf s k + ch
  pe : eAt t (s.getReg .x2 - 1448) = polyEvalRust msg ch
  scale : eAt t (s.getReg .x2 - 1472) = acc.2.1
  rest : Rest s t (packR s c (k + 1) ((1 + rOf s k + ch) * polyEvalRust msg ch,
    acc.2.1 * (1 + rOf s k + ch), acc.2.2 ++ [ch]))

set_option maxHeartbeats 16000000 in
/-- `0x8000f644..0x8000f69c`: the challenge and the message at it. -/
theorem pk_mid1 (hD : DuplexSpec) (hPE : MultilinearContracts.PolyEvalSpec)
    {s w t : MachineState} {ip : Word} {c : E} {k : Nat} {acc : E × E × List E} {msg : List E}
    (hpre : VerifyLayerPre s) (P : PK s w ip c k acc) (Q : Q1 s w t ip c k acc msg) :
    ∃ v, Reaches Image.code t v ∧ ((∃ ch, Qm s w v c k acc msg ch) ∨ Dead Image.code v) := by
  have hb := bounds hpre
  have B := Q.base
  have hnx := hpre.stack.next
  have hab := hpre.stack.above
  have hS := hpre.self.self
  have hss := hpre.selfStack
  have hsf := hpre.selfFree
  have hrs := hpre.stack.rodata
  simp only [stackLo] at hnx hab hss hrs
  unfold verifyLayerStack at hb hnx hab hss hrs
  have hHt := B.heap.hi
  have kq (y : Word) (h1 : (s.getReg .x2).toNat - 1712 ≤ y.toNat)
      (h2 : y.toNat + 8 ≤ (s.getReg .x2).toNat - 1592 ∨
        (s.getReg .x2).toNat - 1568 ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2).toNat - 1448 ∨
        (s.getReg .x2).toNat - 1424 ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2).toNat - 752 ∨
        (s.getReg .x2).toNat - 720 ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2).toNat - 128) :
      t.getMem y = w.getMem y :=
    Q.frame y fun i hi hw ↦ by
      simp only [W8, Fresh] at hw
      rcases hw with hw | hw | hw | hw | hw | hw | hw | hw <;>
        addr_omega [hw, hi, h1, h2, hb, hss, hS, hnx, hab, hHt]
  -- `0x8000f644`: `duplex`
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000f644_spec Q.pc (by
    rv_eval [B.x2]; valid_access hpre.stack.valid [hb])
  have k₁ := b8000f644_keeps h₁
  have hm₁ := b8000f644_mem_same h₁
  have x2₁ : t₁.getReg .x2 = s.getReg .x2 - 1712 := (k₁ .x2 (by decide)).trans B.x2
  have B₁ : Base s t₁ := B.same x2₁ hm₁
  have x10₁ : t₁.getReg .x10 = s.getReg .x11 + 8 := by
    rw [b8000f644_x10 h₁, B.x2]; rv_eval []
    rw [kq _ (by addr_omega [hb]) (Or.inl (by addr_omega [hb])), P.sponge]
  obtain ⟨t₂, hr₂, ⟨hpc₂, hp₂, B₂, F₂, tr₂⟩ | hd⟩ := duplexCall hD hpre B₁ hr₁ (b8000f644_pc h₁) x10₁
  swap
  · exact ⟨_, hr₂, Or.inr hd⟩
  have R₂ := (Q.rest.keep fun T hT ↦ transcriptAt_congr hm₁ hT).sample tr₂
  have x2₂ : t₂.getReg .x2 = s.getReg .x2 - 1712 := (hp₂.reg .x2).trans x2₁
  have r₂ (r : Reg) (hr : r ∈ [Reg.x8, .x9, .x19, .x20, .x21, .x22, .x23, .x24, .x26, .x27]) :
      t₂.getReg r = t.getReg r := by
    rw [hp₂.reg r (mem_of_mem hr _), k₁ r (mem_of_mem hr _)]
  have x20₂ : t₂.getReg .x20 = s.getReg .x11 := by
    rw [r₂ .x20 (by decide), Q.regs .x20 (by decide), P.x20]
  -- `0x8000f650`: `c`, `1 + r + c`, `poly_eval(message, c)`
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000f650_spec
    (by rw [hpc₂, returnAddress_eq, b8000f644_x1 h₁]; decide) (by
      rv_eval [x2₂, x20₂]
      and_intros <;> first
        | valid_access hpre.stack.valid [hb]
        | (refine Region.valid hS ?_ ?_ ?_ <;> addr_omega [hS]))
  have k₃ := b8000f650_keeps h₃
  have F₃ : DFrame t₂ t₃ fun a ↦ Within a (s.getReg .x2 - 752) 24 ∨ Within a (s.getReg .x2 - 128) 24 :=
    dframe_of_writes h₃ (by rv_eval [x2₂]; and_intros <;> addr_omega [hb])
  have x2₃ : t₃.getReg .x2 = s.getReg .x2 - 1712 := (k₃ .x2 (by decide)).trans x2₂
  have hN₃ : t₃.getMem nextAddr = t₂.getMem nextAddr := F₃ _ fun i hi hw ↦ by
    rcases hw with hw | hw <;> addr_omega [hw, hi, hb, hnx]
  have B₃ : Base s t₃ := B₂.next hpre x2₃
    ⟨by simp only [heapNext, hN₃]; exact B₂.heap.lo, by simp only [heapNext, hN₃]; exact B₂.heap.hi⟩
    (by simp only [heapNext, hN₃]; exact le_refl _) F₃ fun a h ↦ by
      rcases h with h | h
      · exact slots_lw hpre (by addr_omega [hb]) (by addr_omega [hb]) h
      · exact slots_lw hpre (by addr_omega [hb]) (by addr_omega [hb]) h
  have m960 := b8000f650_m_x2_960 h₃
  have m968 := b8000f650_m_x2_968 h₃
  have m976 := b8000f650_m_x2_976 h₃
  have m1584 := b8000f650_m_x2_1584 h₃
  have m1592 := b8000f650_m_x2_1592 h₃
  have m1600 := b8000f650_m_x2_1600 h₃
  have e8 := r₂ .x8 (by decide)
  have e27 := r₂ .x27 (by decide)
  have e24 := r₂ .x24 (by decide)
  rw [x2₂, x20₂] at m960 m968 m976 m1584 m1592 m1600
  rv_eval [e8, e27, e24, Q.x8, Q.x27, Q.x24] at m960 m968 m976 m1584 m1592 m1600
  have hch : limbs (eAt t₂ (s.getReg .x11 + 136)) = (t₂.getMem (s.getReg .x11 + 136),
      t₂.getMem (s.getReg .x11 + 144), t₂.getMem (s.getReg .x11 + 152)) := by
    rw [limbs_eAt]; rv_eval []
  have e1rc : eAt t₃ (s.getReg .x2 - 128) = 1 + rOf s k + eAt t₂ (s.getReg .x11 + 136) := by
    apply eAt_eq_of_limbs
    rw [limbs_one_add, limbs_eAt, hch]
    rv_eval [m1584, m1592, m1600]
  have ech : eAt t₃ (s.getReg .x2 - 752) = eAt t₂ (s.getReg .x11 + 136) :=
    eAt_congr (by rv_eval [m960]) (by rv_eval [m968]) (by rv_eval [m976])
  -- `poly_eval(message, c)` into `f + 264`
  have x10₃ : t₃.getReg .x10 = s.getReg .x2 - 1448 := by rw [b8000f650_x10 h₃, x2₂]; rv_eval []
  have x11₃ : t₃.getReg .x11 = t.getMem (s.getReg .x2 - 1440) := by
    rw [b8000f650_x11 h₃, r₂ .x22 (by decide), Q.x22]
  have x12₃ : t₃.getReg .x12 = t.getMem (s.getReg .x2 - 1432) := by
    rw [b8000f650_x12 h₃, r₂ .x21 (by decide), Q.x21]
  have x13₃ : t₃.getReg .x13 = s.getReg .x2 - 752 := by rw [b8000f650_x13 h₃, x2₂]; rv_eval []
  obtain ⟨⟨mraw, mlen⟩, mbuf, melems⟩ := Q.msgV
  simp only [RawVecOk, Buf, NewBuf, vecEs, vecPtr, vecLen, vecCap] at mraw mlen mbuf melems
  rv_eval [] at mraw mlen mbuf melems
  have hHw := P.base.heap.lo
  have hsw := P.base.mono
  have hHs := hpre.heap.lo
  have hlo : stackLo t₃ MultilinearContracts.polyEvalStack =
      s.getReg .x2 - 1712 - BitVec.ofNat 64 MultilinearContracts.polyEvalStack := by
    simp only [stackLo, x2₃]
  have hps : (MultilinearContracts.polyEvalStack : Nat) ≤ sumcheckStack := by decide
  have hpe : MultilinearContracts.PolyEvalPre t₃ := {
    ret := by rw [x10₃]; exact slot_vmr hpre (by decide) (by decide) (by decide)
    coeffs := by
      rw [x11₃, x12₃]
      by_cases hl0 : (t.getMem (s.getReg .x2 - 1432)).toNat = 0
      · rw [hl0]; intro i hi; omega
      · exact heap_vmr (by omega) (by omega) mbuf.1
    point := by rw [x13₃]; exact slot_vmr hpre (by decide) (by decide) (by decide)
    stack := (hpre.stack.sub 1712 x2₃ (by unfold verifyLayerStack; omega) (by decide)
      (by decide) (by decide) (by decide)).toStackOk
    retCoeffs := by rw [x10₃, x11₃, x12₃]; addr_omega [hb, mbuf, mlen, hHt, hab]
    retPoint := by rw [x10₃, x13₃]; addr_omega [hb]
    retStack := by rw [x10₃, hlo]; addr_omega [hb, hps]
    coeffsStack := by rw [x11₃, x12₃, hlo]; addr_omega [hb, mbuf, mlen, hHt, hab, hps]
    pointStack := by rw [x13₃, hlo]; addr_omega [hb, hps]
    rodata := B₃.rodata hpre
    retRodata := by rw [x10₃]; addr_omega [hb, hrs]
    stackRodata := by rw [hlo]; addr_omega [hb, hrs, hps] }
  obtain ⟨t₄, hr₄, ⟨hpc₄, hp₄, PE⟩ | hd⟩ := hPE.call (hr₂.trans hr₃) (b8000f650_pc h₃) hpe
  swap
  · exact ⟨_, hr₄, Or.inr hd⟩
  have V₄ := PE.value
  rw [x10₃, x11₃, x12₃, x13₃, ech] at V₄
  have F₄ := DFrame.of_two PE.frame
  rw [x10₃, hlo] at F₄
  have x2₄ : t₄.getReg .x2 = s.getReg .x2 - 1712 := (hp₄.reg .x2).trans x2₃
  have hN₄ : t₄.getMem nextAddr = t₃.getMem nextAddr := F₄ _ fun i hi hw ↦ by
    rcases hw with hw | hw <;> addr_omega [hi, hw, hb, hnx, hps]
  have B₄ : Base s t₄ := B₃.next hpre x2₄
    ⟨by simp only [heapNext, hN₄]; exact B₃.heap.lo, by simp only [heapNext, hN₄]; exact B₃.heap.hi⟩
    (by simp only [heapNext, hN₄]; exact le_refl _) F₄ fun a h ↦ by
      refine ⟨Or.inr (Or.inr (Or.inl ?_)), ?_⟩ <;> rcases h with h | h <;> addr_omega [h, hb, hps]
  -- the frames from `t` and from the challenge
  have G₂ : DFrame t t₂ (W8b s) := (DFrame.of_same hm₁ _).trans F₂ fun a h ↦ by
    simp only [W8b]; rcases h with h | h <;> addr_omega [h, hb]
  have H₃ : DFrame t₂ t₃ (W8c s) := F₃.mono fun a h ↦ by
    simp only [W8c]; rcases h with h | h <;> addr_omega [h, hb]
  have H₄ : DFrame t₂ t₄ (W8c s) := H₃.trans F₄ fun a h ↦ by
    simp only [W8c]; rcases h with h | h <;> addr_omega [h, hb, hps]
  have hmsg : eListAt t₃ (t.getMem (s.getReg .x2 - 1440)) (t.getMem (s.getReg .x2 - 1432)).toNat =
      msg := by
    rw [← melems]
    exact (G₂.trans H₃ fun a h ↦ by
      simp only [W8c] at h; simp only [W8b]; rcases h with h | h | h | h | h <;> addr_omega [h]).eListAt
      fun j hj hw ↦ by
        simp only [W8b] at hw
        rcases hsf.1 with hs1 | hs1 <;>
        rcases hw with hw | hw | hw | hw | hw | hw <;>
          addr_omega [hw, hj, hb, mbuf, mlen, hHt, hab, hs1, hsw, hS]
  rw [hmsg] at V₄
  have G₄ : DFrame t t₄ (W8b s) := G₂.trans H₄ fun a h ↦ by
    simp only [W8c] at h; simp only [W8b]; rcases h with h | h | h | h | h <;> addr_omega [h]
  have hN₄t : t₄.getMem nextAddr = t.getMem nextAddr := G₄ _ fun i hi hw ↦ by
    simp only [W8b] at hw
    rcases hw with hw | hw | hw | hw | hw | hw <;> addr_omega [hw, hi, hb, hnx, hsf.2, hS]
  have hNt : heapNext t₄ = heapNext t := by simp only [heapNext, hN₄t]
  have y4 (r : Reg) (hr : r ∈ [Reg.x8, .x9, .x18, .x19, .x20, .x23, .x24, .x25, .x26, .x27]) :
      t₄.getReg r = t₃.getReg r := hp₄.reg r (mem_of_mem hr _)
  have y3 (r : Reg) (hr : r ∈ [Reg.x9, .x19, .x23, .x26]) : t₄.getReg r = t₂.getReg r := by
    rw [y4 r (mem_sub (by decide) hr),
      k₃ r (mem_of_mem hr _)]
  refine ⟨t₄, hr₄, Or.inl ⟨eAt t₂ (s.getReg .x11 + 136), {
    pc := by rw [hpc₄, returnAddress_eq, b8000f650_x1 h₃]; decide
    base := B₄
    mono := by rw [hNt]; exact Q.mono
    frame := (Q.frame.mono fun a h ↦ w8_mono (le_of_eq hNt.symm) h).trans G₄ fun a h ↦ by
      simp only [W8b] at h; simp only [W8]; rcases h with h | h | h | h | h | h <;> addr_omega [h]
    x19 := by rw [y3 .x19 (by decide), r₂ .x19 (by decide), Q.x19]
    regs := fun r hr ↦ by
      rw [y3 r (mem_sub (by decide) hr),
        r₂ r (mem_sub (by decide) hr),
        Q.regs r (mem_sub (by decide) hr)]
    chL := by
      rw [hch, y4 .x18 (by decide), y4 .x25 (by decide), y4 .x20 (by decide),
        b8000f650_x18 h₃, b8000f650_x25 h₃, b8000f650_x20 h₃, x20₂]
    oneL := by
      rw [← e1rc, limbs_eAt, y4 .x27 (by decide), y4 .x8 (by decide), y4 .x24 (by decide),
        b8000f650_x27 h₃, b8000f650_x8 h₃, b8000f650_x24 h₃]
      rv_eval [m1584, m1592, m1600, x20₂, e8, e27, e24, Q.x8, Q.x27, Q.x24]
    one := by
      rw [← e1rc]
      exact F₄.eAt fun j hj hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hj, hb, hps]
    pe := V₄
    scale := by
      rw [G₄.eAt fun j hj hw ↦ by
          simp only [W8b] at hw
          rcases hw with hw | hw | hw | hw | hw | hw <;> addr_omega [hw, hj, hb, hss, hS],
        Q.frame.eAt fun j hj hw ↦ by
          simp only [W8, Fresh] at hw
          rcases hw with hw | hw | hw | hw | hw | hw | hw | hw <;>
            addr_omega [hw, hj, hb, hss, hS, hnx, hab, hHt]]
      exact P.scale
    rest := R₂.keep fun T hT ↦ B₂.tat hpre B₄.heap H₄ (fun a ha ↦ bodyW_tat hpre B₂ B₄.heap
      (Or.inl (by
        unfold verifyLayerStack
        simp only [W8c] at ha
        rcases ha with ha | ha | ha | ha | ha <;> addr_omega [ha, hb]))) hT }⟩⟩

set_option maxHeartbeats 16000000 in
/-- `0x8000f69c..0x8000f6d0`: `value` and `scale`'s products. -/
theorem pk_mid2 (hM : MulSpec) {s w t : MachineState} {c : E} {k : Nat}
    {acc : E × E × List E} {msg : List E} {ch : E} (hpre : VerifyLayerPre s)
    (Q : Qm s w t c k acc msg ch) :
    ∃ v, Reaches Image.code t v ∧ ((∃ nv, Q2 s w v c k acc ch nv) ∨ Dead Image.code v) := by
  have hb := bounds hpre
  have B := Q.base
  unfold verifyLayerStack at hb
  -- `0x8000f69c`: `value = (1 + r + c) * message(c)`
  obtain ⟨t₅, hr₅, h₅⟩ := Sym.BlockSpec.reaches b8000f69c_spec Q.pc trivial
  have k₅ := b8000f69c_keeps h₅
  have hm₅ := b8000f69c_mem_same h₅
  have x2₅ : t₅.getReg .x2 = s.getReg .x2 - 1712 := (k₅ .x2 (by decide)).trans B.x2
  have B₅ : Base s t₅ := B.same x2₅ hm₅
  obtain ⟨t₆, hr₆, ⟨hpc₆, hp₆, B₆, F₆, V₆⟩ | hd⟩ := mulCall hM hpre B₅ hr₅ (b8000f69c_pc h₅)
    1592 128 1448 (by rw [b8000f69c_x10 h₅, B.x2]; rv_eval []) (by rw [b8000f69c_x11 h₅, B.x2]; rv_eval [])
    (by rw [b8000f69c_x12 h₅, B.x2]; rv_eval []) (by decide) (by decide) (by decide)
    (by decide) (by decide)
  swap
  · exact ⟨_, hr₆, Or.inr hd⟩
  rv_eval [] at F₆ V₆
  have e5 (a : Word) : eAt t₅ a = eAt t a := by unfold Rv64Verifier.eAt; rw [hm₅, hm₅, hm₅]
  rw [e5, e5, Q.pe, Q.one] at V₆
  have x2₆ : t₆.getReg .x2 = s.getReg .x2 - 1712 := B₆.x2
  -- `0x8000f6b0`: `1 + r + c` into `f + 264`, `scale * (1 + r + c)` into `f + 960`
  obtain ⟨t₇, hr₇, h₇⟩ := Sym.BlockSpec.reaches b8000f6b0_spec
    (by rw [hpc₆, returnAddress_eq, b8000f69c_x1 h₅]; decide) (by
      rv_eval [x2₆]; and_intros <;> valid_access hpre.stack.valid [hb])
  have k₇ := b8000f6b0_keeps h₇
  have f₇ := b8000f6b0_frame h₇ (by rw [x2₆]; addr_omega [hb])
  rw [x2₆] at f₇
  rv_eval [] at f₇
  have x2₇ : t₇.getReg .x2 = s.getReg .x2 - 1712 := (k₇ .x2 (by decide)).trans x2₆
  have B₇ : Base s t₇ := B₆.slots hpre x2₇ f₇ (by addr_omega [hb]) (by addr_omega [hb])
  have y6 (r : Reg) (hr : r ∈ [Reg.x8, .x9, .x18, .x19, .x20, .x23, .x24, .x25, .x26, .x27]) :
      t₆.getReg r = t.getReg r := by
    rw [hp₆.reg r (mem_of_mem hr _), k₅ r (mem_of_mem hr _)]
  have m264 := b8000f6b0_m_x2_264 h₇
  have m272 := b8000f6b0_m_x2_272 h₇
  have m280 := b8000f6b0_m_x2_280 h₇
  rw [x2₆, y6 .x27 (by decide)] at m264
  rw [x2₆, y6 .x8 (by decide)] at m272
  rw [x2₆, y6 .x24 (by decide)] at m280
  rv_eval [] at m264 m272 m280
  have e7 : eAt t₇ (s.getReg .x2 - 1448) = 1 + rOf s k + ch := by
    apply eAt_eq_of_limbs
    rw [Q.oneL]
    rv_eval [m264, m272, m280]
  have F67 : DFrame t₆ t₇ (Within · (s.getReg .x2 - 1448) 24) := DFrame.of_memFrame f₇
  have esc : eAt t₇ (s.getReg .x2 - 1472) = acc.2.1 := by
    rw [F67.eAt fun j hj hw ↦ by addr_omega [hw, hj, hb],
      F₆.eAt fun j hj hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hj, hb], e5]
    exact Q.scale
  obtain ⟨t₈, hr₈, ⟨hpc₈, hp₈, B₈, F₈, V₈⟩ | hd⟩ := mulCall hM hpre B₇ hr₇ (b8000f6b0_pc h₇)
    752 1472 1448 (by rw [b8000f6b0_x10 h₇, x2₆]; rv_eval []) (by rw [b8000f6b0_x11 h₇, x2₆]; rv_eval [])
    (by rw [b8000f6b0_x12 h₇, x2₆]; rv_eval []) (by decide) (by decide) (by decide)
    (by decide) (by decide)
  swap
  · exact ⟨_, hr₆.trans hr₈, Or.inr hd⟩
  rv_eval [] at F₈ V₈
  rw [esc, e7] at V₈
  have hnx := hpre.stack.next
  simp only [stackLo] at hnx
  unfold verifyLayerStack at hnx
  have H : DFrame t t₈ (W8c s) :=
    (((DFrame.of_same hm₅ _).trans F₆ fun a h ↦ by
      simp only [W8c]; rcases h with h | h <;> addr_omega [h, hb]).trans F67 fun a h ↦ by
        simp only [W8c]; addr_omega [h, hb]).trans F₈ fun a h ↦ by
          simp only [W8c]; rcases h with h | h <;> addr_omega [h, hb]
  have hN : t₈.getMem nextAddr = t.getMem nextAddr := H _ fun i hi hw ↦ by
    simp only [W8c] at hw
    rcases hw with hw | hw | hw | hw | hw <;> addr_omega [hw, hi, hb, hnx]
  have hNt : heapNext t₈ = heapNext t := by simp only [heapNext, hN]
  have y8 (r : Reg) (hr : r ∈ [Reg.x9, .x18, .x19, .x20, .x23, .x25, .x26]) :
      t₈.getReg r = t.getReg r := by
    rw [hp₈.reg r (mem_of_mem hr _), k₇ r (mem_of_mem hr _),
      y6 r (mem_sub (by decide) hr)]
  refine ⟨t₈, hr₆.trans hr₈, Or.inl ⟨(1 + rOf s k + ch) * polyEvalRust msg ch, {
    pc := by rw [hpc₈, returnAddress_eq, b8000f6b0_x1 h₇]; decide
    base := B₈
    mono := by rw [hNt]; exact Q.mono
    frame := (Q.frame.mono fun a h ↦ w8_mono (le_of_eq hNt.symm) h).trans H fun a h ↦ by
      simp only [W8c] at h; simp only [W8]; rcases h with h | h | h | h | h <;> addr_omega [h]
    x19 := by rw [y8 .x19 (by decide), Q.x19]
    regs := fun r hr ↦ by
      rw [y8 r (mem_sub (by decide) hr),
        Q.regs r hr]
    chL := by rw [y8 .x18 (by decide), y8 .x25 (by decide), y8 .x20 (by decide)]; exact Q.chL
    value := by
      rw [← V₆, F₈.eAt fun j hj hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hj, hb]]
      exact F67.eAt fun j hj hw ↦ by addr_omega [hw, hj, hb]
    sc := V₈
    rest := Q.rest.body hpre B B₈ (H.mono fun a h ↦ Or.inl (by
      unfold verifyLayerStack
      simp only [W8c] at h
      rcases h with h | h | h | h | h <;> addr_omega [h, hb])) }⟩⟩

theorem pk_mid (hD : DuplexSpec) (hPE : MultilinearContracts.PolyEvalSpec) (hM : MulSpec)
    {s w t : MachineState} {ip : Word} {c : E} {k : Nat} {acc : E × E × List E} {msg : List E}
    (hpre : VerifyLayerPre s) (P : PK s w ip c k acc) (Q : Q1 s w t ip c k acc msg) :
    ∃ v, Reaches Image.code t v ∧ ((∃ ch nv, Q2 s w v c k acc ch nv) ∨ Dead Image.code v) := by
  obtain ⟨t₁, hr₁, ⟨ch, M⟩ | hd⟩ := pk_mid1 hD hPE hpre P Q
  · obtain ⟨v, hr₂, ⟨nv, Q₂⟩ | hd⟩ := pk_mid2 hM hpre M
    · exact ⟨v, hr₁.trans hr₂, Or.inl ⟨ch, nv, Q₂⟩⟩
    · exact ⟨v, hr₁.trans hr₂, Or.inr hd⟩
  · exact ⟨t₁, hr₁, Or.inr hd⟩

end Rv64Verifier.Gkr.Layer
