import Rv64Verifier.Proofs.Layout.ExtendLoop

/-!
# `extend_trusted` meets its contract

`0x80006008` enters the loop; `0x80006084` stores the length and returns.
-/

namespace Rv64Verifier.Layout.Extend
open RiscvZkvm.Rv64 Rv64Verifier.Runtime Rv64Verifier.Sym Rv64Verifier.Blocks.F22
  Rv64Verifier.Model.LayoutMirror
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- At `0x80006084`: every block written. -/
structure Done (s u : MachineState) (nx P C : Word) (N2 : Nat) : Prop where
  res : Res s P C N2
  inv : Inv s u nx
  n2 : N2 ≤ nx.toNat
  x8 : u.getReg .x8 = s.getReg .x10
  x19 : u.getReg .x19 = vecLen s (s.getReg .x10) + BitVec.ofNat 64 (itLen s)
  hdr : u.getMem (s.getReg .x10) = C ∧ u.getMem (s.getReg .x10 + 8) = P
  old : bytesAt u P (48 * len s) = bytesAt s (vecPtr s (s.getReg .x10)) (48 * len s)
  blocks : ∀ i < itLen s, NewBlock s u (blk s P i) (itElem s i) ∧
    ∀ x, formVecDeep u (blk s P i) x → N2 ≤ x.toNat ∧ x.toNat < nx.toNat

theorem finish {s u : MachineState} (hpre : ExtendPre s) {nx P C : Word} {N2 : Nat}
    (h : Done s u nx P C N2) (hpc : u.pc = 0x80006084) :
    ∃ t, Reaches Image.code u t ∧
      ((t.pc = returnAddress s ∧ Preserves s t ∧ ExtendPost s t) ∨ Dead Image.code t) := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hab := hst.above
  have hnx8 := hst.next
  have hss := hpre.selfStack
  have hsf := hpre.selfFree
  simp only [Outside] at hsf
  obtain ⟨hs8, hsb, -, -, -, -⟩ := facts hpre
  have hR := h.res
  have hroom := hR.room
  have hRhi := hR.hi
  have hRlo := hR.lo
  have hn2 := h.n2
  have hfit := h.inv.fits
  have hmono := h.inv.mono
  have hlo0 := hpre.heap.lo
  obtain ⟨hsp, sl1, sl2, sl3, sl4, sl5, sl6, sl7, sl8, sl9, sl10, sl11⟩ := h.inv.slotVals
  have x8 := h.x8
  have hselfP : Apart (s.getReg .x10) 24 P (48 * C.toNat) := by
    rcases hR.same with ⟨rfl, rfl⟩ | h0 | h0
    · exact hpre.selfBuf
    · simp only [Apart]; omega
    · addr_omega [h0, hsf, hsb, hRhi]
  obtain ⟨t, hr, ht⟩ := BlockSpec.reaches b80006084_spec hpc (by
    rv_eval [hsp, x8]
    and_intros <;> first
      | valid_access hst.valid [hb]
      | valid_access hpre.self [hsb, hs8]
      | addr_omega [hb, hss, hsb])
  have k := b80006084_keeps ht
  have hm := b80006084_frame ht (by rw [x8]; omega)
  rw [x8] at hm
  have m16 := b80006084_m_x8_16 ht
  rw [x8, h.x19] at m16
  have pc := b80006084_pc ht
  rw [hsp] at pc
  rv_eval [sl1] at pc
  have hreg (r : Reg) (e : Word) (he : t.getReg r = u.getMem (u.getReg .x2 + e))
      (hv : u.getMem (s.getReg .x2 - 144 + e) = s.getReg r) : t.getReg r = s.getReg r := by
    rw [he, hsp, hv]
  have hdm := hm.dframe
  have hnt : t.getMem nextAddr = nx := (hm _ fun hw ↦ by addr_omega [hw, hsb, hnx8, hsf]).trans h.inv.next
  have hnext : heapNext t = nx.toNat := by simp only [heapNext, hnt]
  have hnu : heapNext u = nx.toNat := by simp only [heapNext, h.inv.next]
  have keep (a : Word) (ha : a.toNat + 8 ≤ (s.getReg .x10).toNat + 16 ∨
      (s.getReg .x10).toNat + 24 ≤ a.toNat) : t.getMem a = u.getMem a := hm a fun hw ↦ by addr_omega [hw, ha, hsb]
  have hlen : len s = (vecLen s (s.getReg .x10)).toNat := rfl
  have hP0 : (vecPtr t (s.getReg .x10)) = P := (keep _ (by addr_omega [hsb])).trans h.hdr.2
  have hC1 : (vecCap t (s.getReg .x10)) = C := (keep _ (by addr_omega [hsb])).trans h.hdr.1
  have hroom' : (vecLen s (s.getReg .x10)).toNat + itLen s ≤ C.toNat := hroom
  have hLK : (vecLen s (s.getReg .x10) + BitVec.ofNat 64 (itLen s)).toNat =
      (vecLen s (s.getReg .x10)).toNat + itLen s := by
    rcases hR.fit with h0 | h0
    · have : (vecLen s (s.getReg .x10)).toNat + itLen s = 0 := by omega
      addr_omega [this]
    · addr_omega [h0, hroom', hRhi]
  have hL1 : (vecLen t (s.getReg .x10)).toNat = len s + itLen s := by
    show (t.getMem (s.getReg .x10 + 16)).toNat = _
    rw [m16, hLK]
  refine ⟨t, hr, Or.inl ⟨by rw [pc, returnAddress_eq], ?_, ?_⟩⟩
  · refine preserves_of (by rw [b80006084_x2 ht, hsp]; addr_omega [hb])
      (hreg .x8 128 (b80006084_x8 ht) (by rv_eval [sl2])) (hreg .x9 120 (b80006084_x9 ht) (by rv_eval [sl3]))
      (hreg .x18 112 (b80006084_x18 ht) (by rv_eval [sl4]))
      (hreg .x19 104 (b80006084_x19 ht) (by rv_eval [sl5])) ?_
    intro r hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hreg .x20 96 (b80006084_x20 ht) (by rv_eval [sl6])
    · exact hreg .x21 88 (b80006084_x21 ht) (by rv_eval [sl7])
    · exact hreg .x22 80 (b80006084_x22 ht) (by rv_eval [sl8])
    · exact hreg .x23 72 (b80006084_x23 ht) (by rv_eval [sl9])
    · exact hreg .x24 64 (b80006084_x24 ht) (by rv_eval [sl10])
    · exact hreg .x25 56 (b80006084_x25 ht) (by rv_eval [sl11])
    all_goals exact (k _ (by decide)).trans (h.inv.regs _ (by decide))
  have hP8 := hR.align
  refine {
    heap := ⟨by rw [hnext]; exact Nat.le_trans hlo0 hmono, by rw [hnext]; exact hfit⟩
    mono := by rw [hnext]; exact hmono
    vec := ⟨?_, by rw [hL1, hC1]; exact hroom⟩
    len := hL1
    old := ?_
    buf := ?_
    new := fun i hi ↦ ?_
    frame := ?_ }
  · simp only [RawVecOk, Buf, hP0, hC1, hnext]
    refine ⟨hP8, ?_⟩
    rcases hR.fit with h0 | h0
    · exact Or.inl (by omega)
    · exact Or.inr ⟨h0.1, by omega⟩
  · rw [hP0, ← h.old]
    refine DFrame.bytesAt_al hdm hP8 (by omega) ?_ fun x hx hw ↦ ?_
    · have := P.isLt
      rcases hR.fit with h0 | h0
      · omega
      · simp only [heapEnd] at hRhi; omega
    · rcases hR.fit with h0 | h0
      · simp only [Within] at hx; omega
      · addr_omega [hx, hw, hselfP, h0, hroom', hsb]
  · rw [hP0, hC1]
    rcases hR.same with h0 | h0
    · exact Or.inl h0
    · right
      refine ⟨hP8, ?_⟩
      rcases h0 with h0 | h0
      · exact Or.inl (by omega)
      · exact Or.inr ⟨h0.1, by rw [hnext]; omega⟩
  · obtain ⟨nb, hdp⟩ := h.blocks i hi
    have hfc := hR.fit.resolve_left (by omega)
    obtain ⟨hfc1, hfc2⟩ := hfc
    have kb (a : Word) (ha : P.toNat ≤ a.toNat ∧ a.toNat + 8 ≤ P.toNat + 48 * C.toNat ∨
        N2 ≤ a.toNat ∧ a.toNat + 8 ≤ nx.toNat) : t.getMem a = u.getMem a :=
      keep a (by
        rcases ha with ha | ha
        · addr_omega [ha, hselfP]
        · addr_omega [ha, hsf, hsb, hRlo, hn2, hfit])
    have hbi : P.toNat ≤ (blk s P i).toNat ∧ (blk s P i).toNat + 48 ≤ P.toNat + 48 * C.toNat := by
      constructor <;> addr_omega [hfc1, hfc2, hRhi, hroom, hi]
    obtain ⟨hv, hok, hdeq⟩ := formVecOf_moved hdm (e := blk s P i) (e' := blk s P i)
      (kb _ (Or.inl (by constructor <;> addr_omega [hbi, hfc2, hRhi, hlen])))
      (kb _ (Or.inl (by constructor <;> addr_omega [hbi, hfc2, hRhi, hlen])))
      (kb _ (Or.inl (by constructor <;> addr_omega [hbi, hfc2, hRhi, hlen]))) nb.ok
      (fun x hx hw ↦ by have := hdp x hx; addr_omega [this, hw, hsf, hsb, hRlo, hn2, hfit])
      ⟨by rw [hnu]; exact Nat.le_trans hlo0 hmono, by rw [hnu]; exact hfit⟩ (by rw [hnext, hnu])
    rw [hP0]
    show NewBlock s t (blk s P i) (itElem s i)
    exact {
      logRows := (kb _ (Or.inl (by constructor <;> addr_omega [hbi, hfc2, hRhi, hlen]))).trans nb.logRows
      rows := (kb _ (Or.inl (by constructor <;> addr_omega [hbi, hfc2, hRhi, hlen]))).trans nb.rows
      owner := (kb _ (Or.inl (by constructor <;> addr_omega [hbi, hfc2, hRhi, hlen]))).trans nb.owner
      ok := hok
      value := hv.trans nb.value
      fresh := fun x hx ↦ by
        rw [hdeq] at hx
        have := nb.fresh x hx
        simp only [Fresh, hnext, hnu] at this ⊢
        exact this }
  · refine (h.inv.mem.union hdm).mono fun a ha ↦ ?_
    rcases ha with (ha | ha | ha | ha) | ha
    · simp only [W] at ha
      rcases ha with ha | ha
      · exact Or.inl ha
      · exact Or.inr (Or.inl (by addr_omega [ha, hb]))
    · exact Or.inr (Or.inl (by addr_omega [ha, hb]))
    · exact Or.inr (Or.inr (Or.inl ha))
    · exact Or.inr (Or.inr (Or.inr (by simp only [Fresh, hnext]; exact ha)))
    · exact Or.inl (Or.inl (by addr_omega [ha, hsb]))

theorem Done.of_loop {s u : MachineState} {nx P C : Word} {N2 : Nat}
    (h : Loop s u nx P C N2 (itLen s)) : Done s u nx P C N2 :=
  ⟨h.res, h.inv, h.n2, h.x8, h.x19, ⟨h.hdr.1, h.hdr.2.1⟩, h.old, h.blocks⟩

theorem itEnd_eq {s : MachineState} (hpre : ExtendPre s) :
    (itEnd s).toNat = (itStart s).toNat + 24 * itLen s := by
  have := hpre.whole; have := hpre.bounds; simp only [itLen]; omega

/-- `0x80006008`: the captures loaded, the loop entered. -/
theorem setup {s u : MachineState} (hpre : ExtendPre s) {nx P C : Word} (hR : Res s P C nx.toNat)
    (inv : Inv s u nx) (mid : Mid s u P C) (hpc : u.pc = 0x80006008) (hne : itEnd s ≠ itStart s) :
    ∃ v, Reaches Image.code u v ∧ Loop s v nx P C nx.toNat 0 ∧ v.pc = 0x80006034 := by
  obtain ⟨hs8, hsb, hsrc, -, -, -⟩ := facts hpre
  obtain ⟨-, hit2, hit8⟩ := iter_facts hpre
  have hKe := itEnd_eq hpre
  have hK : 0 < itLen s := by
    refine Nat.pos_of_ne_zero fun h0 ↦ hne (BitVec.eq_of_toNat_eq ?_)
    rw [h0] at hKe; omega
  obtain ⟨hst8, hsrc⟩ := hsrc.resolve_left (by omega)
  have hroom' : (vecLen s (s.getReg .x10)).toNat + itLen s ≤ C.toNat := hR.room
  have hfc := hR.fit.resolve_left (by omega)
  have hRhi := hR.hi
  obtain ⟨v, hr, hv⟩ := BlockSpec.reaches b80006008_spec hpc (by
    rv_eval [mid.x8, mid.x9]
    and_intros <;> first | valid_access hpre.self [hsb, hs8] | valid_access hpre.iter [hit2, hit8])
  have k := b80006008_keeps hv
  have hm := b80006008_mem_same hv
  have rd (a : Word) (h1 : (s.getReg .x11).toNat ≤ a.toNat)
      (h2 : a.toNat + 8 ≤ (s.getReg .x11).toNat + 40) : u.getMem a = s.getMem a :=
    inv.read hpre (fun x hx ↦ Or.inl (by addr_omega [hx, h1, h2])) (by omega)
  refine ⟨v, hr, {
    res := hR
    inv := inv.same hpre hm k
    n2 := Nat.le_refl _
    x8 := (k .x8 (by decide)).trans mid.x8
    x9 := by rw [b80006008_x9 hv, mid.x9, rd _ (by addr_omega [hit2]) (by addr_omega [hit2])]; rfl
    x18 := by
      show v.getReg .x18 = P + BitVec.ofNat 64 (48 * ((vecLen s (s.getReg .x10)).toNat + 0))
      rw [b80006008_x18 hv, mid.x8, mid.x19, mid.hdr.2.1]
      addr_omega [hfc, hroom', hRhi]
    x19 := by rw [b80006008_x19 hv, mid.x19, mid.x18]
    x20 := by rw [b80006008_x20 hv, mid.x9, rd _ (by addr_omega [hit2]) (by addr_omega [hit2])]; rfl
    x21 := by rw [b80006008_x21 hv, mid.x9, rd _ (by addr_omega [hit2]) (by addr_omega [hit2])]; rfl
    x22 := by rw [b80006008_x22 hv, mid.x22]; rfl
    x23 := by rw [b80006008_x23 hv, mid.x22, mid.x23]; addr_omega [hsrc, hKe]
    hdr := ⟨(hm _).trans mid.hdr.1, (hm _).trans mid.hdr.2.1, (hm _).trans mid.hdr.2.2⟩
    old := (bytesAt_eq_iff.mpr fun i _ ↦ by simp only [byteAt_eq, hm]).trans mid.old
    blocks := fun i hi ↦ absurd hi (Nat.not_lt_zero _)
    le := Nat.zero_le _ }, b80006008_pc hv⟩

/-- **`Vec<BusBlock>::extend_trusted` meets its contract**, given `reserve`'s and `clone`'s. -/
theorem extend_spec (hR : ReserveFreshSpec 0x800060bc 48 8) (hC : CloneSpec) : ExtendSpec := by
  intro s hpc hpre
  obtain ⟨u, hr, ⟨nx, P, C, hres, inv, mid, hpcu⟩ | hd⟩ := start hR hpc hpre
  swap
  · exact ⟨u, hr, Or.inr hd⟩
  have hKe := itEnd_eq hpre
  by_cases he : itEnd s = itStart s
  · simp only [he, ↓reduceIte] at hpcu
    have hK : itLen s = 0 := by rw [he] at hKe; omega
    obtain ⟨t, ht, hres'⟩ := finish hpre {
      res := hres
      inv := inv
      n2 := Nat.le_refl _
      x8 := mid.x8
      x19 := by rw [mid.x19, hK]; simp
      hdr := ⟨mid.hdr.1, mid.hdr.2.1⟩
      old := mid.old
      blocks := fun i hi ↦ absurd hi (by omega) } hpcu
    exact ⟨t, hr.trans ht, hres'⟩
  · simp only [he, ↓reduceIte] at hpcu
    obtain ⟨hst8, hsrc⟩ := (facts hpre).2.2.1.resolve_left fun h0 ↦ he
      (BitVec.eq_of_toNat_eq (by rw [h0] at hKe; omega))
    obtain ⟨v, hv, L0, hpcv⟩ := setup hpre hres inv mid hpcu he
    have hK : 0 < itLen s := Nat.pos_of_ne_zero fun h0 ↦ he (BitVec.eq_of_toNat_eq (by
      rw [h0] at hKe; omega))
    obtain ⟨w, hw, hdone⟩ := Reaches.loop (code := Image.code)
      (fun u ↦ ∃ nx' j, Loop s u nx' P C nx.toNat j ∧ j < itLen s ∧ u.pc = 0x80006034)
      (fun u ↦ (u.getReg .x23).toNat - (u.getReg .x22).toNat)
      (fun u ↦ (∃ nx', Done s u nx' P C nx.toNat ∧ u.pc = 0x80006084) ∨ Dead Image.code u)
      (fun u ⟨nx', j, hl, hj, hpc⟩ ↦ by
        obtain ⟨y, hy, ⟨nx'', hl', hpcy⟩ | hd⟩ := body hC hpre hl hj hpc
        · by_cases hj1 : j + 1 = itLen s
          · simp only [hj1, ↓reduceIte] at hpcy
            rw [hj1] at hl'
            exact Or.inl ⟨y, hy, Or.inl ⟨nx'', Done.of_loop hl', hpcy⟩⟩
          · simp only [hj1, ↓reduceIte] at hpcy
            refine Or.inr ⟨y, hy, ⟨nx'', j + 1, hl', by omega, hpcy⟩, ?_⟩
            rw [hl'.x22, hl'.x23, hl.x22, hl.x23]
            addr_omega [hsrc, hKe, hj]
        · exact Or.inl ⟨y, hy, Or.inr hd⟩) v ⟨nx, 0, L0, hK, hpcv⟩
    rcases hdone with ⟨nx', hD, hpcw⟩ | hd
    · obtain ⟨t, ht, hres'⟩ := finish hpre hD hpcw
      exact ⟨t, hr.trans (hv.trans (hw.trans ht)), hres'⟩
    · exact ⟨w, hr.trans (hv.trans hw), Or.inr hd⟩

end Rv64Verifier.Layout.Extend
