import Rv64Verifier.Proofs.Layout.ExtendStart

/-!
# `extend_trusted`: the loop

At `0x80006034` for block `j` (`Loop`): the blocks before it written, each a clone whose buffers lie
between `N2` (the heap's end after `reserve`, above `P`'s buffer) and `NEXT`.
-/

namespace Rv64Verifier.Layout.Extend
open RiscvZkvm.Rv64 Rv64Verifier.Runtime Rv64Verifier.Sym Rv64Verifier.Blocks.F22
  Rv64Verifier.Model.LayoutMirror
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- Block `i`'s address. -/
@[rv_addr] def blk (s : MachineState) (P : Word) (i : Nat) : Word := P + BitVec.ofNat 64 (48 * (len s + i))

structure Loop (s u : MachineState) (nx P C : Word) (N2 : Nat) (j : Nat) : Prop where
  res : Res s P C N2
  inv : Inv s u nx
  n2 : N2 ≤ nx.toNat
  x8 : u.getReg .x8 = s.getReg .x10
  x9 : u.getReg .x9 = itTable s
  x18 : u.getReg .x18 = blk s P j
  x19 : u.getReg .x19 = vecLen s (s.getReg .x10) + BitVec.ofNat 64 (itLen s)
  x20 : u.getReg .x20 = itHeight s
  x21 : u.getReg .x21 = itRows s
  x22 : u.getReg .x22 = itStart s + BitVec.ofNat 64 (24 * j + 16)
  x23 : u.getReg .x23 = itEnd s + 16
  hdr : u.getMem (s.getReg .x10) = C ∧ u.getMem (s.getReg .x10 + 8) = P ∧
    u.getMem (s.getReg .x10 + 16) = vecLen s (s.getReg .x10)
  old : bytesAt u P (48 * len s) = bytesAt s (vecPtr s (s.getReg .x10)) (48 * len s)
  blocks : ∀ i < j, NewBlock s u (blk s P i) (itElem s i) ∧
    ∀ x, formVecDeep u (blk s P i) x → N2 ≤ x.toNat ∧ x.toNat < nx.toNat
  le : j ≤ itLen s

/-- A doubleword in the heap is a valid access. -/
theorem valid_heap {x : Word} (h1 : heapStart ≤ x.toNat) (h2 : x.toNat + 8 ≤ heapEnd)
    (h3 : x.toNat % 8 = 0) : Sym.validAccess 8 x = true := by
  rw [Sym.validAccess_eight]; simp only [heapStart, heapEnd] at h1 h2; omega

/-- The facts about the arguments every step uses. -/
theorem facts {s : MachineState} (hpre : ExtendPre s) :
    (s.getReg .x10).toNat % 8 = 0 ∧ (s.getReg .x10).toNat + 24 ≤ 0xc0000008 ∧
      (itLen s = 0 ∨ (itStart s).toNat % 8 = 0 ∧ (itStart s).toNat + 24 * itLen s ≤ 0xc0000008) ∧
      (itHeight s).toNat + 8 ≤ 0xc0000008 ∧ (itRows s).toNat + 8 ≤ 0xc0000008 ∧
      (itTable s + 72).toNat + 8 ≤ 0xc0000008 := by
  have h1 := ValidMemRange.bounds hpre.self (by decide)
  have h3 := ValidMemRange.bounds hpre.height (by decide)
  have h4 := ValidMemRange.bounds hpre.rows (by decide)
  have h5 := ValidMemRange.bounds hpre.owner (by decide)
  refine ⟨h1.2.1, by omega, ?_, by omega, by omega, by omega⟩
  by_cases hk : itLen s = 0
  · exact Or.inl hk
  · have h2 := ValidMemRange.bounds hpre.src (by omega)
    exact Or.inr ⟨h2.2.1, by omega⟩

theorem body (hC : CloneSpec) {s u : MachineState} (hpre : ExtendPre s) {nx P C : Word} {N2 j : Nat}
    (h : Loop s u nx P C N2 j) (hlt : j < itLen s) (hpc : u.pc = 0x80006034) :
    ∃ v, Reaches Image.code u v ∧ ((∃ nx', Loop s v nx' P C N2 (j + 1) ∧
      v.pc = (if j + 1 = itLen s then 0x80006084 else 0x80006034)) ∨ Dead Image.code v) := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hab := hst.above
  have hnx8 := hst.next
  have hss := hpre.selfStack
  have hsf := hpre.selfFree
  simp only [Outside] at hsf
  obtain ⟨hs8, hsb, hsrc, hhb, hrb, hob⟩ := facts hpre
  obtain ⟨hst8, hsrc⟩ := hsrc.resolve_left (by omega)
  have hR := h.res
  have hroom := hR.room
  have hfitC := hR.fit.resolve_left (by omega)
  have hP8 := hR.align
  have hn2 := h.n2
  have hfit := h.inv.fits
  have hmono := h.inv.mono
  have hlo0 := hpre.heap.lo
  have hsp : u.getReg .x2 = s.getReg .x2 - 144 := h.inv.sp
  have hnu : heapNext u = nx.toNat := by simp only [heapNext, h.inv.next]
  obtain ⟨v₀, hr₀, h₀⟩ := BlockSpec.reaches b80006034_spec hpc (by
    rv_eval [h.x20, h.x21, h.x22]
    and_intros <;> first
      | valid_access hpre.height [hhb]
      | valid_access hpre.rows [hrb]
      | valid_access hpre.src [hsrc, hst8, hlt])
  have k₀ := b80006034_keeps h₀
  have hm₀ := b80006034_mem_same h₀
  have inv₀ := h.inv.same hpre hm₀ k₀
  have hdv := inv₀.dframe hpre
  have he8 : itStart s + BitVec.ofNat 64 (24 * j + 16) - 8 = itElem s j + 8 := by
    simp only [itElem]; addr_omega [hsrc, hlt]
  have he16 : itStart s + BitVec.ofNat 64 (24 * j + 16) = itElem s j + 16 := by
    simp only [itElem]; addr_omega [hsrc, hlt]
  have x10₀ : v₀.getReg .x10 = s.getReg .x2 - 136 := by rw [b80006034_x10 h₀, hsp]; rv_eval []
  have x11₀ : v₀.getReg .x11 = vecPtr v₀ (itElem s j) := by
    rw [b80006034_x11 h₀, h.x22, he8]; exact (hm₀ _).symm
  have x12₀ : v₀.getReg .x12 = vecLen v₀ (itElem s j) := by
    rw [b80006034_x12 h₀, h.x22, he16]; exact (hm₀ _).symm
  have x24₀ : v₀.getReg .x24 = s.getMem (itHeight s) := by
    rw [b80006034_x24 h₀, h.x20, ← hm₀]
    exact inv₀.read hpre (fun x hx ↦ Or.inr (Or.inr (Or.inr (Or.inl hx)))) (by omega)
  have x25₀ : v₀.getReg .x25 = s.getMem (itRows s) := by
    rw [b80006034_x25 h₀, h.x21, ← hm₀]
    exact inv₀.read hpre (fun x hx ↦ Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hx))))) (by omega)
  have hnv₀ : heapNext v₀ = nx.toNat := by simp only [heapNext, inv₀.next]
  obtain ⟨hFv, hF⟩ := formVecOf_frame hdv (hpre.elems j hlt)
    (fun x hx hn ↦ hn (Or.inr (Or.inl (by simp only [itElem] at hx; addr_omega [hx, hsrc, hlt]))))
    (fun x hx hn ↦ hn (Or.inr (Or.inr (Or.inl ⟨j, hlt, hx⟩))))
    (by simp only [itElem]; addr_omega [hsrc, hlt]) hpre.heap (by rw [hnv₀]; exact hmono)
  have hbe := vecBuf_bounds hF.vec (by decide)
  have hle := hF.vec.len
  have hsrcb : (vecLen v₀ (itElem s j)).toNat = 0 ∨ heapStart ≤ (vecPtr v₀ (itElem s j)).toNat ∧
      (vecPtr v₀ (itElem s j)).toNat + 24 * (vecLen v₀ (itElem s j)).toNat ≤ nx.toNat := by
    rcases hbe.2 with h0 | h0
    · exact Or.inl (by omega)
    · exact Or.inr ⟨h0.1, by rw [hnv₀] at h0; omega⟩
  have x2₀ : v₀.getReg .x2 = s.getReg .x2 - 144 := (k₀ .x2 (by decide)).trans hsp
  have hsl : stackLo v₀ cloneStack = s.getReg .x2 - 320 := by
    simp only [stackLo, cloneStack, tryAllocStack, x2₀, Nat.reduceAdd]; rv_eval []
  have hcp : ClonePre v₀ := {
    heap := ⟨by rw [hnv₀]; exact Nat.le_trans hlo0 hmono, by rw [hnv₀]; exact hfit⟩
    stack := hst.inner (k := 144) x2₀ (by decide) (by decide) (by decide) (by decide) (by decide)
    out := by rw [x10₀]; valid_sub hst.valid [hb]
    src := by
      rw [x11₀, x12₀]
      rcases hsrcb with h0 | h0
      · intro i hi; omega
      · exact validMemRange_of hbe.1 (Or.inl ⟨by simp only [heapStart] at h0; omega, by
          simp only [heapEnd] at hfit; omega⟩)
    srcOk := by rw [x11₀, x12₀]; exact hF.forms
    outFree := by
      rw [x10₀]; simp only [Outside]
      exact ⟨Or.inr (by addr_omega [hab, hb]), by addr_omega [hnx8, hb]⟩
    srcFree := by
      rw [x11₀, x12₀]; simp only [Outside, hnv₀]
      rcases hsrcb with h0 | h0
      · have hp := hpre.elemsPtr j hlt
        rw [show vecPtr v₀ (itElem s j) = vecPtr s (itElem s j) from
          inv₀.read hpre (fun x hx ↦ Or.inr (Or.inl (by simp only [itElem] at hx; addr_omega [hx, hsrc, hlt])))
            (by simp only [itElem]; addr_omega [hsrc, hlt])]
        refine ⟨?_, by simp only [Apart]; omega⟩
        rcases hp with hp | hp
        · exact Or.inl (by rw [hnv₀] at *; omega)
        · exact Or.inr hp
      · exact ⟨Or.inl (by omega), by addr_omega [h0, hfit]⟩
    outStack := by rw [x10₀, hsl]; addr_omega [hb]
    srcStack := by
      rw [x11₀, x12₀, hsl]
      rcases hsrcb with h0 | h0
      · simp only [Apart]; omega
      · addr_omega [h0, hfit, hab, hb] }
  obtain ⟨v₁, hr₁, ⟨hpc₁, hpres₁, hnf, hval⟩ | hdead⟩ := hC.call hr₀ (b80006034_pc h₀) hcp
  swap
  · exact ⟨v₁, hr₁, Or.inr hdead⟩
  rw [x10₀] at hnf hval
  rw [x11₀, x12₀] at hval
  have hval' : formVecOf v₁ (s.getReg .x2 - 136) = formVecOf s (itElem s j) := hval.trans hFv
  have hfr₁ := hnf.frame
  rw [hsl] at hfr₁
  have hmn₁ := hnf.mono
  rw [hnv₀] at hmn₁
  have hhi₁ := hnf.heap.hi
  have inv₁ : Inv s v₁ (v₁.getMem nextAddr) := inv₀.step hpre hfr₁ (fun a ha ↦ by
      rcases ha with ha | ha | ha | ha
      · exact Or.inl (Or.inr (by addr_omega [ha, hb]))
      · exact Or.inl (Or.inr (by addr_omega [ha, hb]))
      · exact Or.inr (Or.inl ha)
      · simp only [Fresh, hnv₀] at ha
        exact Or.inr (Or.inr ⟨Nat.le_trans hmono ha.1, ha.2⟩))
    rfl hmn₁ hhi₁ fun r hr ↦ hpres₁ r (by unfold calleeSaved; revert hr; revert r; decide)
  have hnv₁ : heapNext v₁ = (v₁.getMem nextAddr).toNat := rfl
  have x2₁ : v₁.getReg .x2 = s.getReg .x2 - 144 := (hpres₁.reg .x2).trans x2₀
  have hreg₁ (r : Reg) (hr : r ∈ [Reg.x8, .x9, .x18, .x19, .x20, .x21, .x22, .x23]) :
      v₁.getReg r = u.getReg r := by
    rw [hpres₁ r (by unfold calleeSaved; revert hr; revert r; decide), k₀ r (by revert hr; revert r; decide)]
  have x9₁ : v₁.getReg .x9 = itTable s := (hreg₁ .x9 (by decide)).trans h.x9
  have x18₁ : v₁.getReg .x18 = blk s P j := (hreg₁ .x18 (by decide)).trans h.x18
  have hRhi := hR.hi
  have hfc := hfitC
  obtain ⟨hfc1, hfc2⟩ := hfc
  obtain ⟨v₂, hr₂, h₂⟩ := BlockSpec.reaches b80006050_spec
    (by rw [hpc₁, returnAddress_eq, b80006034_x1 h₀]; decide) (by
      rv_eval [x9₁, x18₁, x2₁]
      and_intros <;> first
        | valid_access hpre.owner [hob]
        | valid_access hst.valid [hb]
        | (refine valid_heap ?_ ?_ ?_ <;> addr_omega [hfc1, hfc2, hRhi, hroom, hlt, hP8]))
  have k₂ := b80006050_keeps h₂
  have hmf := b80006050_frame h₂ (by rw [x18₁]; addr_omega [hfc1, hfc2, hRhi, hroom, hlt])
  rw [x18₁] at hmf
  have m0 := b80006050_m_x18_0 h₂
  have m8 := b80006050_m_x18_8 h₂
  have m16 := b80006050_m_x18_16 h₂
  have m24 := b80006050_m_x18_24 h₂
  have m32 := b80006050_m_x18_32 h₂
  have m40 := b80006050_m_x18_40 h₂
  rw [x18₁, x2₁] at m0 m8 m16
  rw [x18₁] at m24 m32
  rw [x18₁, x9₁] at m40
  rw [hpres₁.reg .x24, x24₀] at m24
  rw [hpres₁.reg .x25, x25₀] at m32
  rw [inv₁.read hpre (fun x hx ↦ Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hx))))) (by omega)] at m40
  have hdm := hmf.dframe
  have hnext₂ : v₂.getMem nextAddr = v₁.getMem nextAddr :=
    hmf _ fun hw ↦ by addr_omega [hw, hfc1, hfc2, hRhi, hroom, hlt]
  have inv₂ : Inv s v₂ (v₁.getMem nextAddr) := inv₁.step hpre hdm (fun a ha ↦ by
      rcases hR.wr (a := a) (by addr_omega [ha, hfc1, hfc2, hRhi, hroom, hlt]) with h0 | h0
      · exact Or.inl h0
      · exact Or.inr (Or.inr ⟨h0.1, by simp only [heapNext] at hmn₁; omega⟩))
    hnext₂ (Nat.le_refl _) hhi₁ fun r hr ↦ k₂ r (by revert hr; revert r; decide)
  have hnv₂ : heapNext v₂ = heapNext v₁ := by simp only [heapNext, hnext₂]
  have hselfP : Apart (s.getReg .x10) 24 P (48 * C.toNat) := by
    rcases hR.same with ⟨rfl, rfl⟩ | h0 | h0
    · exact hpre.selfBuf
    · simp only [Apart]; omega
    · addr_omega [h0, hsf, hsb, hRhi]
  -- what lies in `P`'s buffer below block `j`, or between `N2` and `NEXT`, is kept from `u` on
  have D := ((DFrame.of_same hm₀ fun _ ↦ False).union hfr₁).union hdm
  have keepU (a : Word) (ha : (P.toNat ≤ a.toNat ∧ a.toNat + 8 ≤ (blk s P j).toNat) ∨
      (N2 ≤ a.toNat ∧ a.toNat + 8 ≤ nx.toNat)) : v₂.getMem a = u.getMem a :=
    D.getMem_of (fun x hx hw ↦ by
      rcases hw with (hw | hw | hw | hw | hw) | hw
      · exact hw
      all_goals (try simp only [Fresh, hnv₀] at hw); addr_omega [hx, hw, ha, hb, hab, hfc1, hfc2,
        hRhi, hroom, hlt, hfit, hn2, hnx8])
      (by addr_omega [ha, hfc1, hfc2, hRhi, hroom, hlt, hfit])
  have hu₂ := hpre.heap
  refine ⟨v₂, hr₁.trans hr₂, Or.inl ⟨v₁.getMem nextAddr, {
    res := hR
    inv := inv₂
    n2 := by simp only [heapNext] at hmn₁; omega
    x8 := by rw [k₂ .x8 (by decide), hreg₁ .x8 (by decide), h.x8]
    x9 := (k₂ .x9 (by decide)).trans x9₁
    x18 := by rw [b80006050_x18 h₂, x18₁]; addr_omega [hfc1, hfc2, hRhi, hroom, hlt]
    x19 := by rw [k₂ .x19 (by decide), hreg₁ .x19 (by decide), h.x19]
    x20 := by rw [k₂ .x20 (by decide), hreg₁ .x20 (by decide), h.x20]
    x21 := by rw [k₂ .x21 (by decide), hreg₁ .x21 (by decide), h.x21]
    x22 := by rw [b80006050_x22 h₂, hreg₁ .x22 (by decide), h.x22]; addr_omega [hsrc, hlt]
    x23 := by rw [k₂ .x23 (by decide), hreg₁ .x23 (by decide), h.x23]
    hdr := by
      have kS (a : Word) (ha : (s.getReg .x10).toNat ≤ a.toNat ∧ a.toNat + 8 ≤ (s.getReg .x10).toNat + 24) :
          v₂.getMem a = u.getMem a :=
        D.getMem_of (fun x hx hw ↦ by
          rcases hw with (hw | hw | hw | hw | hw) | hw
          · exact hw
          all_goals (try simp only [Fresh, hnv₀] at hw); addr_omega [hx, hw, ha, hb, hss, hselfP, hsb,
            hnx8, hsf, hmono, hab, hhi₁, hfc1, hfc2, hRhi, hroom, hlt])
          (by addr_omega [ha, hsb])
      obtain ⟨h0, h1, h2⟩ := h.hdr
      exact ⟨(kS _ (by addr_omega [hsb])).trans h0, (kS _ (by addr_omega [hsb])).trans h1,
        (kS _ (by addr_omega [hsb])).trans h2⟩
    old := by
      rw [← h.old]
      have hl : len s ≤ C.toNat := by omega
      exact bytesAt_eq_iff.mpr fun i hi ↦ by
        have hi' : i < 48 * len s := hi
        have hal := toNat_alignDown (P + BitVec.ofNat 64 i)
        have hpi : (P + BitVec.ofNat 64 i).toNat = P.toNat + i := by
          rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
        rw [byteAt_eq, byteAt_eq, keepU _ (Or.inl (by
          constructor <;> addr_omega [hal, hpi, hi', hP8, hfc1, hfc2, hRhi, hroom, hlt]))]
    blocks := fun i hi ↦ ?_
    le := by omega }, ?_⟩⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
    · obtain ⟨nb, hdp⟩ := h.blocks i hi'
      have hwd (x : Word) (hx : N2 ≤ x.toNat ∧ x.toNat < nx.toNat) : ¬ ((False ∨
          (Within x (s.getReg .x2 - 136) 24 ∨ Within x (s.getReg .x2 - 320) cloneStack ∨
            Within x nextAddr 8 ∨ Fresh v₀ v₁ x)) ∨ Within x (blk s P j) 48) := by
        intro hw
        rcases hw with (hw | hw | hw | hw | hw) | hw
        · exact hw
        all_goals (try simp only [Fresh, hnv₀] at hw); addr_omega [hx, hw, hb, hab, hfc1, hfc2, hRhi,
          hroom, hlt, hfit, hn2, hnx8]
      have hbi : (blk s P i).toNat + 48 ≤ (blk s P j).toNat := by
        addr_omega [hfc1, hfc2, hRhi, hroom, hlt, hi']
      obtain ⟨hv, hok, hdeq⟩ := formVecOf_moved D (e := blk s P i) (e' := blk s P i)
        (keepU _ (Or.inl (by constructor <;> addr_omega [hbi, hfc1, hfc2, hRhi, hroom, hlt, hi'])))
        (keepU _ (Or.inl (by constructor <;> addr_omega [hbi, hfc1, hfc2, hRhi, hroom, hlt, hi'])))
        (keepU _ (Or.inl (by constructor <;> addr_omega [hbi, hfc1, hfc2, hRhi, hroom, hlt, hi'])))
        nb.ok (fun x hx ↦ hwd x (hdp x hx)) ⟨by rw [hnu]; exact Nat.le_trans hlo0 hmono, by rw [hnu]; exact hfit⟩
        (by rw [hnv₂, hnu]; simp only [heapNext] at hmn₁; omega)
      refine ⟨{
        logRows := (keepU _ (Or.inl (by constructor <;> addr_omega [hbi, hfc1, hfc2, hRhi, hroom, hlt, hi']))).trans nb.logRows
        rows := (keepU _ (Or.inl (by constructor <;> addr_omega [hbi, hfc1, hfc2, hRhi, hroom, hlt, hi']))).trans nb.rows
        owner := (keepU _ (Or.inl (by constructor <;> addr_omega [hbi, hfc1, hfc2, hRhi, hroom, hlt, hi']))).trans nb.owner
        ok := hok
        value := hv.trans nb.value
        fresh := fun x hx ↦ by
          rw [hdeq] at hx
          have := nb.fresh x hx
          simp only [Fresh, hnv₂, hnu] at this ⊢
          simp only [heapNext] at hmn₁
          omega }, fun x hx ↦ by
          rw [hdeq] at hx
          have := hdp x hx
          simp only [heapNext] at hmn₁
          omega⟩
    · have h8 : v₂.getMem (blk s P i + 8) = v₁.getMem (s.getReg .x2 - 136 + 8) := by rw [m8]; rv_eval []
      have h16 : v₂.getMem (blk s P i + 16) = v₁.getMem (s.getReg .x2 - 136 + 16) := by
        rw [m16]; rv_eval []
      have h0 : v₂.getMem (blk s P i) = v₁.getMem (s.getReg .x2 - 136) := by rw [m0]; rv_eval []
      obtain ⟨hv, hok, hdeq⟩ := formVecOf_moved hdm h0 h8 h16 hnf.ok
        (fun x hx hw ↦ by
          have := hnf.fresh x hx
          simp only [Fresh, hnv₀] at this
          addr_omega [this, hw, hfc1, hfc2, hRhi, hroom, hlt, hn2])
        hnf.heap (by rw [hnv₂])
      refine ⟨{
        logRows := m24
        rows := m32
        owner := m40
        ok := hok
        value := hv.trans hval'
        fresh := fun x hx ↦ by
          rw [hdeq] at hx
          have := hnf.fresh x hx
          simp only [Fresh, hnv₂, hnv₀] at this ⊢
          omega }, fun x hx ↦ by
          rw [hdeq] at hx
          have := hnf.fresh x hx
          simp only [Fresh, hnv₀] at this
          simp only [heapNext] at this
          omega⟩
  · have hK : (itEnd s).toNat = (itStart s).toNat + 24 * itLen s := by
      have := hpre.whole; have := hpre.bounds; simp only [itLen]; omega
    have x22₁ := hreg₁ .x22 (by decide)
    have x23₁ := hreg₁ .x23 (by decide)
    by_cases hj : j + 1 = itLen s
    · simp only [hj, ↓reduceIte]
      exact b80006050_pc_not_taken h₂ (by rw [x22₁, x23₁, h.x22, h.x23]; addr_omega [hsrc, hK, hj])
    · simp only [hj, ↓reduceIte]
      exact b80006050_pc_taken h₂ (by rw [x22₁, x23₁, h.x22, h.x23]; addr_omega [hsrc, hK, hj, hlt])

end Rv64Verifier.Layout.Extend
