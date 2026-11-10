import Rv64Verifier.Proofs.Layout.BusLayoutTail

/-!
# `bus_layout` meets its contract

`0x80010c88` writes the result and returns; `busLayoutRust`'s placements are the pairs by index
(`take_pairs`, `drop_pairs`).
-/

namespace Rv64Verifier.Layout.BusLayout
open RiscvZkvm.Rv64 Rv64Verifier.Runtime Rv64Verifier.Sym Rv64Verifier.Bus Rv64Verifier.Blocks.F82
  Rv64Verifier.MultilinearContracts Rv64Verifier.Model
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

theorem natsAt_length (s : MachineState) (a : Word) (n : Nat) : (natsAt s a n).length = n := by
  simp [natsAt, readWords_eq_map]

theorem take_pairs (a : List ℕ) (b : List (BitVec 64)) {n m : Nat} (ha : a.length = n + m)
    (hb : b.length = n + m) :
    ((a.zip b).map fun p ↦ (⟨p.1, p.2⟩ : PlacementRust)).take n =
      (List.range n).map fun i ↦ ⟨a.getD i 0, b.getD i 0⟩ := by
  apply List.ext_getElem
  · simp [ha, hb]
  · intro i h1 h2
    simp only [List.length_map, List.length_range] at h2
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : i < a.length),
      List.getElem?_eq_getElem (by omega : i < b.length)]

theorem drop_pairs (a : List ℕ) (b : List (BitVec 64)) {n m : Nat} (ha : a.length = n + m)
    (hb : b.length = n + m) :
    ((a.zip b).map fun p ↦ (⟨p.1, p.2⟩ : PlacementRust)).drop n =
      (List.range m).map fun i ↦ ⟨a.getD (n + i) 0, b.getD (n + i) 0⟩ := by
  apply List.ext_getElem
  · simp [ha, hb]
  · intro i h1 h2
    simp only [List.length_map, List.length_range] at h2
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : n + i < a.length),
      List.getElem?_eq_getElem (by omega : n + i < b.length)]

/-- `0x80010c88`: the result written, the registers restored. -/
theorem finish {s u : MachineState} (hpre : BusLayoutPre s) {nx R T : Word} (h : Final s u nx R T) :
    ∃ t, Reaches Image.code u t ∧
      ((t.pc = returnAddress s ∧ Preserves s t ∧ BusLayoutPost s t) ∨ Dead Image.code t) := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hab := hst.above
  have hnx8 := hst.next
  obtain ⟨ho8, ho56, hn8, hm48, -, -⟩ := facts hpre
  have hos := hpre.outStack
  have hof := hpre.outFree
  have hout := hpre.out
  simp only [Outside] at hof
  have hfit := h.inv.fits
  have hmono := h.inv.mono
  have hlo0 := hpre.heap.lo
  obtain ⟨hsp, sl1, sl2, sl3, sl4, sl5, sl6, sl7, sl8, sl9⟩ := h.inv.saved
  have x9 := h.x9
  obtain ⟨t, hr, ht⟩ := BlockSpec.reaches b80010c88_spec h.pc (by
    rv_eval [hsp, x9]
    and_intros <;> first
      | addr_omega [hb, hos, ho56, ho8]
      | valid_access hst.valid [hb]
      | (refine Transcript.Region.valid hout ?_ ?_ ?_ <;> addr_omega [ho8, ho56]))
  have k := b80010c88_keeps ht
  have hm := b80010c88_frame ht (by rw [x9]; addr_omega [ho56])
  rw [x9] at hm
  have m0 := b80010c88_m_x9_0 ht
  have m8 := b80010c88_m_x9_8 ht
  have m16 := b80010c88_m_x9_16 ht
  have m24 := b80010c88_m_x9_24 ht
  have m32 := b80010c88_m_x9_32 ht
  have m40 := b80010c88_m_x9_40 ht
  have m48 := b80010c88_m_x9_48 ht
  rw [x9, h.x22] at m0
  rw [x9, h.x21] at m8
  rw [x9, h.x8] at m16
  rw [x9, h.x23] at m24
  rw [x9, h.x19] at m32
  rw [x9, h.x18] at m40
  rw [x9] at m48
  have pc := b80010c88_pc ht
  rw [hsp] at pc
  rv_eval [sl1] at pc
  have hreg (r : Reg) (e : Word) (he : t.getReg r = u.getMem (u.getReg .x2 + e))
      (hv : u.getMem (s.getReg .x2 - 112 + e) = s.getReg r) : t.getReg r = s.getReg r := by
    rw [he, hsp, hv]
  have bf := ByteFrame.of_memFrame hm ho8 (by decide)
    (ht.unaligned (by rv_eval [x9]; and_intros <;> addr_omega [ho8, ho56]))
  have hnt : t.getMem nextAddr = nx := (hm _ (by addr_omega [hof.2])).trans h.inv.next
  have hnext : heapNext t = nx.toNat := by simp only [heapNext, hnt]
  have hbf := FnInv.frame h.inv bf (fun a ha ↦ Or.inl ha) hnt
  have keep (a : Word) (ha : a.toNat + 8 ≤ (s.getReg .x10).toNat ∨ (s.getReg .x10).toNat + 56 ≤ a.toNat) :
      t.getMem a = u.getMem a := hm a fun hw ↦ by addr_omega [hw, ha]
  have hRb := h.rbuf
  have hTb := h.tbuf
  have hnn : nn s = (s.getReg .x12).toNat + (s.getReg .x14).toNat := rfl
  have hsz : sizesList s = (List.range (nn s)).map fun i ↦ (srcWord s i).toNat := (sizes_eq s).symm
  have hlenS : (sizesList s).length = nn s := by rw [hsz]; simp
  have hgetS (i : Nat) (hi : i < nn s) : (sizesList s).getD i 0 = (srcWord s i).toNat := by
    rw [hsz]; simp [hi]
  have hN : (BitVec.ofNat 64 (nn s)).toNat = nn s := by addr_omega [hn8, hm48]
  refine ⟨t, hr, Or.inl ⟨by rw [pc, returnAddress_eq], ?_, ?_⟩⟩
  · refine preserves_of (by rw [b80010c88_x2 ht, hsp]; addr_omega [hb])
      (hreg .x8 96 (b80010c88_x8 ht) (by rv_eval [sl2])) (hreg .x9 88 (b80010c88_x9 ht) (by rv_eval [sl3]))
      (hreg .x18 80 (b80010c88_x18 ht) (by rv_eval [sl4]))
      (hreg .x19 72 (b80010c88_x19 ht) (by rv_eval [sl5])) ?_
    intro r hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hreg .x20 64 (b80010c88_x20 ht) (by rv_eval [sl6])
    · exact hreg .x21 56 (b80010c88_x21 ht) (by rv_eval [sl7])
    · exact hreg .x22 48 (b80010c88_x22 ht) (by rv_eval [sl8])
    · exact hreg .x23 40 (b80010c88_x23 ht) (by rv_eval [sl9])
    all_goals exact (k _ (by decide)).trans (h.inv.kept _ (by decide))
  refine {
    heap := ⟨by rw [hnext]; exact Nat.le_trans hlo0 hmono, by rw [hnext]; exact hfit⟩
    mono := by rw [hnext]; exact hmono
    value := ?_
    framework := ?_
    tables := ?_
    frame := ?_ }
  · rw [show busLayoutRust (natsAt s (s.getReg .x11) (s.getReg .x12).toNat)
        (blocksFrom s (s.getReg .x13) (s.getReg .x14).toNat) =
        ⟨(stackOffsetsRust (sizesList s)).2,
          (((sizesList s).zip (stackOffsetsRust (sizesList s)).1).map
            fun p ↦ (⟨p.1, p.2⟩ : PlacementRust)).take (s.getReg .x12).toNat,
          (((sizesList s).zip (stackOffsetsRust (sizesList s)).1).map
            fun p ↦ (⟨p.1, p.2⟩ : PlacementRust)).drop (s.getReg .x12).toNat⟩ by
      simp only [busLayoutRust, natsAt_length]; rfl]
    simp only [busLayoutOf, placementsAt, vecLen, vecPtr]
    rw [take_pairs (n := (s.getReg .x12).toNat) (m := (s.getReg .x14).toNat) (sizesList s)
        (stackOffsetsRust (sizesList s)).1 hlenS h.offsLen,
      drop_pairs (n := (s.getReg .x12).toNat) (m := (s.getReg .x14).toNat) (sizesList s)
        (stackOffsetsRust (sizesList s)).1 hlenS h.offsLen]
    rv_eval [m16, m8, m40, m32, m48]
    rw [h.x20]
    congr 1
    · exact List.map_congr_left fun i hi ↦ by
        have hi' := List.mem_range.mp hi
        obtain ⟨h0, h1⟩ := h.head i hi'
        rw [keep _ (by addr_omega [hRb, hfit, hi', hof]), keep _ (by addr_omega [hRb, hfit, hi', hof]),
          h0, h1, hgetS i (by omega)]
        rfl
    · exact List.map_congr_left fun i hi ↦ by
        have hi' := List.mem_range.mp hi
        obtain ⟨h0, h1⟩ := h.tail i hi'
        rw [keep _ (by addr_omega [hTb, hfit, hi', hof]), keep _ (by addr_omega [hTb, hfit, hi', hof]),
          h0, h1, hgetS _ (by omega)]
        rfl
  · have hc : vecCap t (s.getReg .x10) = BitVec.ofNat 64 (nn s) := m0
    have hp : vecPtr t (s.getReg .x10) = R := m8
    have hl : vecLen t (s.getReg .x10) = s.getReg .x12 := m16
    have hR8 := h.ralign
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simp only [RawVecOk, Buf, hc, hp, hN, hnext]
      refine ⟨hR8, ?_⟩
      rcases hRb with h0 | h0
      · exact Or.inl (by omega)
      · exact Or.inr ⟨Nat.le_trans hlo0 h0.1, by omega⟩
    · rw [hc, hl, hN]; omega
    · simp only [NewBuf, hc, hp, hN, hnext]
      refine ⟨hR8, ?_⟩
      rcases hRb with h0 | h0
      · exact Or.inl (by omega)
      · exact Or.inr ⟨h0.1, by omega⟩
  · have hc : vecCap t (s.getReg .x10 + 24) = s.getReg .x14 := m24
    have hp : vecPtr t (s.getReg .x10 + 24) = T := by simp only [vecPtr]; rv_eval [m32]
    have hl : vecLen t (s.getReg .x10 + 24) = s.getReg .x14 := by simp only [vecLen]; rv_eval [m40]
    have hT8 := h.talign
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simp only [RawVecOk, Buf, hc, hp, hnext]
      refine ⟨hT8, ?_⟩
      rcases hTb with h0 | h0
      · exact Or.inl (by omega)
      · exact Or.inr ⟨Nat.le_trans hlo0 h0.1, by omega⟩
    · rw [hc, hl]
    · simp only [NewBuf, hc, hp, hnext]
      refine ⟨hT8, ?_⟩
      rcases hTb with h0 | h0
      · exact Or.inl (by omega)
      · exact Or.inr ⟨h0.1, by omega⟩
  · refine (Transcript.DFrame.of_byteFrame hbf).mono fun a ha ↦ ?_
    simp only [W] at ha
    rcases ha with (ha | ha) | ha | ha | ha
    · exact Or.inl ha
    · exact Or.inr (Or.inl (by addr_omega [ha, hb]))
    · exact Or.inr (Or.inl (by addr_omega [ha, hb]))
    · exact Or.inr (Or.inr (Or.inl ha))
    · exact Or.inr (Or.inr (Or.inr ha))

/-- **`bus_layout` meets its contract**, given its callees'. -/
theorem bus_layout_spec (hT : TryAllocZeroedSpec) (hR : ReserveFastSpec 0x8000d628)
    (hM : MemcpySpec 0x800126e4) (hS : StackOffsetsSpec) : BusLayoutSpec := by
  intro s hpc hpre
  obtain ⟨u, hr, ⟨nx, P, hu⟩ | hd⟩ := filled hT hR hM hpc hpre
  swap
  · exact ⟨u, hr, Or.inr hd⟩
  obtain ⟨v, hrv, ⟨nx', Q, R, hz, hpcv, x18, x22⟩ | hd⟩ := offsets hT hS hpre hu
  swap
  · exact ⟨v, hr.trans hrv, Or.inr hd⟩
  obtain ⟨w, hrw, hzw, hpcw⟩ := zipped hpre hz hpcv x18 x22
  obtain ⟨y, hry, ⟨nx'', T, hy⟩ | hd⟩ := split hT hM hpre hzw hpcw
  swap
  · exact ⟨y, hr.trans (hrv.trans (hrw.trans hry)), Or.inr hd⟩
  obtain ⟨t, hrt, ht⟩ := finish hpre hy
  exact ⟨t, hr.trans (hrv.trans (hrw.trans (hry.trans hrt))), ht⟩

end Rv64Verifier.Layout.BusLayout
